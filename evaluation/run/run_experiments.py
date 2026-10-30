#!/usr/bin/env python3
"""run_experiments.py MODE -- the measurement script (run/run.sh MODE calls it after the setup).

It plans the runs of MODE from modes.conf (benchmarks, columns, families, sizes, instances, repeats, order),
generates every instance right before its first run and deletes it after its last, and for every run starts the
single-run program of one solver on one instance, as a user would from the command line, under the paper's
timeout policy: 1200 s per run (wall time under `timeout'; CPU time under `prlimit' for push-relabel), and the
ladder rule, by which a timeout or an out-of-memory on one problem stops the other repeats of that problem and
every larger size of that solver and family (recorded as inferred, never run).  The row the program prints is
kept in results/<date>_<mode>/<benchmark>/<family>/raw.csv; make_tables.py then writes the paper's tables
beside it, projected to the columns of the mode.

Orders.  by_benchmark: one benchmark after the other, family by family, size by size.  round_robin: size by
size across the benchmarks (the first size of every benchmark, then the second, ...); with a budget, no run is
started after budget_hours since the setup began (work/started_<mode>), and the runs that were not started are
recorded NOT_RUN.
"""
import csv, datetime, hashlib, json, os, re, shutil, subprocess, sys, time

EVAL = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RUN = os.path.join(EVAL, 'run'); BENCH = os.path.join(EVAL, 'benchmarks'); WORK = os.path.join(EVAL, 'work')
WARM = os.path.join(RUN, 'warm_then_exec.py')
CAP = 1200                       # the paper's timeout per run, seconds
MEM_GB = 45                      # the paper's address-space cap for the Python programs; AS_BYTES for prlimit
AS_BYTES = 48318382080
OK_STATUS = {'OK', 'OPTIMAL', 'SOLVED', 'REACHED', 'RAN', 'ok', 'OPT', 'DONE', 'FOUND', 'UNREACHED', 'NOT_REACHED'}
PY = {'scipy_csr', 'scipy_prebuilt', 'networkx', 'scipy', 'scipy_lsa', 'scipy_mwfbm_csr', 'ortools', 'sage_oracle', 'sage_plain'}
GR = ('dfs', 'bfs', 'dijkstra', 'kruskal'); ASN = ('hungarian', 'matroid_intersections', 'hybrid_bipartite_matching')
ROADS = ['NY', 'BAY', 'COL', 'FLA', 'NW', 'NE', 'CAL', 'LKS', 'E', 'W', 'CTR', 'USA']
ROAD_NODES = dict(zip(ROADS, [264346, 321270, 435666, 1070376, 1207945, 1524453, 1890815, 2758119, 3598623, 6262104, 14081816, 23947347]))
# the sizes of the paper's tables (size keys: the exponent of the .gr families, the rung of push-relabel, n otherwise)
SIZES = {'Square-n': [str(p) for p in range(10, 22)], 'Long-n': [str(p) for p in range(10, 22)], 'Dense-n': [str(p) for p in range(10, 16)], 'USA-road-t': ROADS,
         'rmf-long': ['rmf-long-8-64', 'rmf-long-10-90', 'rmf-long-11-128', 'rmf-long-13-181', 'rmf-long-16-256', 'rmf-long-19-361', 'rmf-long-23-511', 'rmf-long-27-723',
                      'rmf-long-32-1022', 'rmf-long-38-1448', 'rmf-long-45-2048', 'rmf-long-54-2896', 'rmf-long-64-4096', 'rmf-long-76-5793', 'rmf-long-91-8104'],
         'wash-rlg-long': ['wash-rlg-long-128-%d' % (32 << i) for i in range(15)],
         'ak': ['ak-4102', 'ak-8198', 'ak-16390', 'ak-32774', 'ak-65542', 'ak-131078', 'ak-262150', 'ak-524294', 'ak-1048582']}
SIZES_N = {'hungarian': {'low-cost': [2048, 4096, 8192, 16384, 32768], 'two-cost': [2048, 4096, 8192, 16384, 32768], 'geometric': [256, 512, 1024, 2048, 4096]},
           'matroid_intersections': {'low-cost': [32 << i for i in range(11)], 'two-cost': [32 << i for i in range(11)], 'geometric': [32 << i for i in range(8)]},
           'hybrid_bipartite_matching': {'low-cost': [2048 << i for i in range(10)], 'two-cost': [2048 << i for i in range(10)], 'geometric': [256 << i for i in range(7)]}}
SEEDS_PER_SIZE = {'hungarian': 10, 'matroid_intersections': 5, 'hybrid_bipartite_matching': 10}
NOT_APPLICABLE = {('sml_afp', 'rmf-long'): 'the AFP network model forbids antiparallel arcs; genrmf has them'}   # n/a in the paper: recorded, not run
WARM_CORE = {'kruskal': 3}       # seconds of busy spin on the core before the program, as the campaign did (PROTOCOL.txt)
AK_WARM = {'lemon_csr', 'scipy_csr'}   # push-relabel ak: 5 s warm-up for these columns, as the campaign did

def conf(mode):
    """modes.conf -> {key without the mode prefix: [values]}"""
    out = {}
    for line in open(os.path.join(EVAL, 'modes.conf')):
        line = line.split('#', 1)[0].strip()
        if '=' not in line: continue
        k, v = line.split('=', 1)
        k = k.strip()
        if k.startswith(mode + '.'): out[k[len(mode) + 1:]] = v.split()
    if 'benchmarks' not in out: sys.exit('modes.conf has no mode ' + mode)
    return out

def read_columns(pkg):
    """benchmarks/<pkg>/columns.txt -> {column: [program, fixed args...]} (program relative to the benchmark)"""
    out = {}
    for line in open(os.path.join(BENCH, pkg, 'columns.txt')):
        parts = line.split('#', 1)[0].split()
        if parts: out[parts[0]] = parts[1:]
    return out

LOGF = None
def log(*a):
    line = time.strftime('%H:%M:%S') + ' ' + ' '.join(str(x) for x in a)
    print(line, flush=True)
    if LOGF: LOGF.write(line + '\n'); LOGF.flush()

def md5(path):
    h = hashlib.md5()
    with open(path, 'rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''): h.update(chunk)
    return h.hexdigest()

def not_available():
    p = os.path.join(EVAL, 'NOT_AVAILABLE.txt')
    return open(p).read() if os.path.exists(p) else ''

# ----------------------------------------------------------------------------------------------
# Instances: generated from the seeds files as each benchmark's instances/README.txt describes
# ----------------------------------------------------------------------------------------------
def read_seeds_gr(pkg, fam):
    """lines 'NAME n=.. ... cmd: spgrid.exe ARGS' -> [(name, n, [cmd...])]"""
    out = []
    for line in open(os.path.join(BENCH, pkg, 'instances', 'seeds', fam + '.txt')):
        m = re.match(r'^(\S+\.gr)\s+n=(\d+).*cmd:\s+(.*)$', line.strip())
        if m: out.append((m.group(1), int(m.group(2)), m.group(3).split()))
    return out

def read_seeds_pr(fam):
    """push-relabel: 'RUNG n=.. m=.. [seed=k] GEN ARGS > FILE' -> [(rung, n, seed, [gen...], file)]"""
    out = []
    for line in open(os.path.join(BENCH, 'push_relabel', 'instances', 'seeds', fam + '.txt')):
        m = re.match(r'^(\S+)\s+n=(\d+)\s+m=(\d+)\s+(?:seed=(\d+)\s+)?(\S.*?)\s*>\s*(\S+)$', line.strip())
        if m: out.append((m.group(1), int(m.group(2)), int(m.group(4)) if m.group(4) else 0, m.group(5).split(), m.group(6)))
    return out

def read_queries(pkg):
    out = {}
    p = os.path.join(BENCH, pkg, 'instances', 'queries.csv')
    if os.path.exists(p):
        for r in csv.DictReader(open(p)): out.setdefault(r['instance'], []).append((r['query'], r['source'], r['target']))
    return out

def md5_list(pkg):
    p = os.path.join(BENCH, pkg, 'instances', 'MD5SUM_instances.txt')
    out = {}
    if os.path.exists(p):
        for line in open(p):
            parts = line.split()
            if len(parts) >= 2 and re.match(r'^[0-9a-f]{32}$', parts[0]): out[os.path.basename(parts[-1])] = parts[0]
    return out

class Instances:
    """Describes the instance files of a size (paths and how to make them), makes them on demand and deletes
    them when the plan has no run left that needs them."""
    def __init__(self):
        self.made = 0; self.checked = 0; self.mismatch = []; self.makers = {}; self.generated = set()
    # ---- describing ----
    def gr(self, pkg, fam, size, first_only):
        """[(name, nodes, path)] of one size (exponent) of a synthetic family"""
        gens = os.path.join(BENCH, pkg, 'instances', 'generators')
        out = []
        for name, n, cmd in read_seeds_gr(pkg, fam):
            if name.split('.')[1] != size: continue
            path = os.path.join(BENCH, pkg, 'instances', fam, name)
            self.makers[path] = ('gen', [os.path.join(gens, cmd[0])] + cmd[1:], gens, pkg)
            out.append((name, n, path))
            if first_only: break
        return out
    def road(self, pkg, name):
        """the unpacked road network, from the archive the setup downloaded"""
        gz = os.path.join(WORK, 'downloads', 'USA-road-t.%s.gr.gz' % name)
        path = os.path.join(BENCH, pkg, 'instances', 'USA-road-t', 'USA-road-t.%s.gr' % name)
        if not os.path.exists(gz) and not os.path.exists(path): return None
        self.makers[path] = ('gunzip', gz, None, pkg)
        return path
    def pr(self, fam, rung, first_only):
        """push-relabel: [(file name, nodes, seed, path)] of one rung"""
        gens = os.path.join(BENCH, 'push_relabel', 'instances', 'generators', 'bin')
        out = []
        for r, n, seed, cmd, fname in read_seeds_pr(fam):
            if r != rung: continue
            fname = fname if seed == 0 else fname.replace('.max', '_s%d.max' % seed)
            path = os.path.join(BENCH, 'push_relabel', 'instances', fam, fname)
            self.makers[path] = ('gen', [os.path.join(gens, cmd[0])] + cmd[1:], gens, 'push_relabel')
            out.append((fname, n, seed, path))
            if first_only: break
        return out
    def asn(self, pkg, fam, n, seeds):
        """assignment instances of one size: [(file name, path)]; the benchmark's generator scripts make them"""
        gens = os.path.join(BENCH, pkg, 'instances', 'generators')
        outdir = os.path.join(BENCH, pkg, 'instances', 'files' if pkg == 'hybrid_bipartite_matching' else os.path.join('generators', 'out'))
        out = []
        for s in seeds:
            name = '%s_n%d_s%d.asn' % (fam, n, s); path = os.path.join(outdir, fam, name)
            self.makers[path] = ('asn', (fam, n, s), gens, pkg); out.append((name, path))
            if pkg == 'matroid_intersections':
                self.makers[path[:-4] + '.bmatch'] = ('bmatch', (fam, path), gens, pkg)
        return out
    # ---- making ----
    def check(self, pkg, path):
        ref = md5_list(pkg).get(os.path.basename(path))
        if ref:
            self.checked += 1
            if md5(path) != ref: self.mismatch.append(os.path.relpath(path, EVAL))
    def ensure(self, path):
        if os.path.exists(path): return True
        kind, what, cwd, pkg = self.makers[path]
        os.makedirs(os.path.dirname(path), exist_ok=True)
        # the assignment generators write the other families of the same size and seed too: those files are tracked as well
        siblings = [p for p, m in self.makers.items() if m[3] == pkg and m[0] in ('asn', 'bmatch') and p != path and not os.path.exists(p)] if kind in ('asn', 'bmatch') else []
        if kind == 'gen':
            if not os.path.exists(what[0]): log('   generator missing:', os.path.relpath(what[0], EVAL)); return False
            with open(path + '.part', 'w') as f: r = subprocess.run(what, stdout=f, stderr=subprocess.DEVNULL, cwd=cwd)
            if r.returncode != 0 or os.path.getsize(path + '.part') == 0: os.remove(path + '.part'); log('   generator failed:', ' '.join(what)); return False
            os.replace(path + '.part', path)
        elif kind == 'gunzip':
            if not os.path.exists(what): log('   road network archive missing:', os.path.relpath(what, EVAL)); return False
            with open(path + '.part', 'wb') as f: r = subprocess.run(['gzip', '-dc', what], stdout=f, stderr=subprocess.DEVNULL)
            if r.returncode != 0: os.remove(path + '.part'); log('   could not unpack', what); return False
            os.replace(path + '.part', path)
        elif kind == 'asn':
            fam, n, s = what
            script = 'gen_geometric.sh' if fam == 'geometric' else 'gen_instances.sh'
            r = subprocess.run(['bash', script, '--nodes', str(n), '--seeds', str(s)], cwd=cwd, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
            if not os.path.exists(path): log('   %s did not produce %s: %s' % (script, os.path.basename(path), r.stderr[-300:])); return False
        elif kind == 'bmatch':
            fam, asn = what
            if not self.ensure(asn): return False
            subprocess.run(['bash', 'stamp_instances.sh', '--families', fam], cwd=cwd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            if not os.path.exists(path): log('   stamp_instances.sh did not produce', os.path.basename(path)); return False
        for p in [path] + [p for p in siblings if os.path.exists(p)]:
            self.made += 1; self.generated.add(p); self.check(pkg, p)
        return True
    def delete(self, path):
        if path in self.generated and os.path.exists(path): os.remove(path); self.generated.discard(path)
    def cleanup(self):
        for p in list(self.generated): self.delete(p)

# ----------------------------------------------------------------------------------------------
# The plan: one job per (column, problem, repeat), in run order; a job is a dict
# ----------------------------------------------------------------------------------------------
def make_plan(mode, cf, inst):
    """-> (jobs in run order, {pkg: [columns planned]})"""
    first_size = cf['sizes'][0] == 'first'; first_inst = cf['instances'][0] == 'first'
    reps = int(cf['repeats'][0]); na = not_available()
    planned = {}
    per_rank = {}            # (pkg, fam) -> [jobs of size rank 0, of rank 1, ...]
    for pkg in cf['benchmarks']:
        progs = read_columns(pkg)
        cols = []
        for c in cf.get('columns.' + pkg, []):
            if c not in progs: log('   %s: column %s is not in columns.txt, left out' % (pkg, c)); continue
            if os.path.exists(os.path.join(BENCH, pkg, progs[c][0])): cols.append(c)
            else: log('   %s: column %s left out (program not built)' % (pkg, c))
        planned[pkg] = cols
        def program(c): return [os.path.join(BENCH, pkg, progs[c][0])] + progs[c][1:]
        for fam in cf.get('families.' + pkg, []):
            sizes = SIZES.get(fam) or [str(x) for x in SIZES_N[pkg][fam]]
            if fam == 'USA-road-t': sizes = [r for r in sizes if r in (cf['roads'] if cf['roads'][0] != 'all' else ROADS)]
            if first_size: sizes = sizes[:1]
            ranks = []
            for size in sizes:
                jobs = []
                if pkg in GR:
                    queries = read_queries(pkg)
                    if fam == 'USA-road-t':
                        path = inst.road(pkg, size)
                        files = [('USA-road-t.%s.gr' % size, ROAD_NODES[size], path)] if path else []
                        if not files: log('   %s: road network %s not downloaded, row left out' % (pkg, size))
                    else:
                        files = inst.gr(pkg, fam, size, first_inst)
                    for name, n, path in files:
                        if pkg == 'kruskal': probs = [('', [])]
                        else:
                            probs = [(q, ['--source', s, '--target', ('0' if pkg == 'dfs' else t), '--query', q]) for q, s, t in queries.get(name, [])]
                            if not probs: raise RuntimeError('no query for %s in %s/instances/queries.csv' % (name, pkg))
                            if first_inst: probs = probs[:1]
                        for q, qargs in probs:
                            for c in cols:
                                for k in range(1, reps + 1):
                                    cmd = program(c) + qargs + ['--tag', '%s;rep=%d%s' % (fam, k, ';warmcore=%ds' % WARM_CORE[pkg] if pkg in WARM_CORE else '')]
                                    if c in PY: cmd += ['--mem-gb', str(MEM_GB)]
                                    cmd.append(path)
                                    jobs.append(dict(pkg=pkg, col=c, fam=fam, size=size, nodes=n, inst=name, q=q, rep=k, cmd=cmd, cwd=os.path.join(BENCH, pkg),
                                                     cap=CAP, warm=WARM_CORE.get(pkg, 0), mode='timeout', files=[path]))
                elif pkg == 'push_relabel':
                    files = inst.pr(fam, size, first_inst)
                    if not files and fam == 'ak' and 'ak' in na: log('   push_relabel: the AK generator is not available, family left out'); break
                    repeated = fam == 'ak' or first_inst                      # one file, repeated; else one run per seed file
                    for fname, n, seed, path in (files[:1] if repeated else files):   # seed files outer: one on disk at a time
                        for c in cols:
                            for k in (range(1, reps + 1) if repeated else [seed]):
                                warm = 5 if (fam == 'ak' and c in AK_WARM) else 0
                                cmd = program(c) + ['--tag', 'island=X;repeat=%d;seed=%d%s' % (k, seed or 1, ';warmcore=5s' if warm else '')]
                                if c in PY: cmd += ['--memory-gb', str(MEM_GB)]
                                cmd.append(path)
                                jobs.append(dict(pkg=pkg, col=c, fam=fam, size=size, nodes=n, inst=fname, q='', rep=k, cmd=cmd, cwd=os.path.join(BENCH, pkg), cap=CAP,
                                                 warm=warm, mode='prlimit', as_limit=(c not in PY and c != 'jgrapht'), env={'PR_XMX': '42g'},
                                                 na=NOT_APPLICABLE.get((c, fam), ''), files=[path]))
                elif pkg in ASN:
                    n = int(size)
                    nseeds = 1 if first_inst else SEEDS_PER_SIZE[pkg]
                    problems = cf.get('problems.' + fam, ['']) if pkg == 'matroid_intersections' else ['']
                    for name, path in inst.asn(pkg, fam, n, range(1, nseeds + 1)):
                        for c in cols:
                            for pr in problems:
                                for k in range(1, reps + 1):
                                    if pkg == 'hungarian':
                                        tag = ['--tag', '%s;rep=%d' % (fam, k)]
                                        cmd = program(c) + ((['--theta-frac', '1.0', '--cap', '2'] + tag) if c == 'sml' else (['--csv'] + tag)) + [path]
                                        job = dict(cap=1320 if c == 'csa_q_csr' else CAP, warm=0, mode='timeout', files=[path])
                                    elif pkg == 'hybrid_bipartite_matching':
                                        cmd = program(c) + ['--timeout', str(CAP), '--tag', '%s;rep=%d;warmcore=3s' % (fam, k), path]
                                        job = dict(cap=1324, warm=3, mode='timeout', files=[path])
                                    else:
                                        f = path if pr in ('matching', 'weighted_matching') else path[:-4] + '.bmatch'
                                        cmd = program(c) + [pr, f]
                                        job = dict(cap=CAP, warm=0, mode='timeout', files=[path, f] if f != path else [path])
                                    job.update(pkg=pkg, col=(c + '/' + pr if pr else c), fam=fam, size=size, nodes=n, inst=name, q='', rep=k, cmd=cmd, cwd=os.path.join(BENCH, pkg))
                                    jobs.append(job)
                ranks.append(jobs)
            per_rank[(pkg, fam)] = ranks
    order = []
    if cf['order'][0] == 'round_robin':
        depth = max([len(r) for r in per_rank.values()] or [0])
        for k in range(depth):
            for pkg in cf['benchmarks']:
                for fam in cf.get('families.' + pkg, []):
                    ranks = per_rank.get((pkg, fam), [])
                    if k < len(ranks): order += ranks[k]
    else:
        for pkg in cf['benchmarks']:
            for fam in cf.get('families.' + pkg, []):
                for jobs in per_rank.get((pkg, fam), []): order += jobs
    return order, planned

# ----------------------------------------------------------------------------------------------
# Running
# ----------------------------------------------------------------------------------------------
RAW_FIELDS = ['package', 'column', 'family', 'size', 'nodes', 'instance', 'query', 'repeat', 'status', 'cpu_ms', 'wall_s', 'rc', 'program_row', 'stderr']
KNOWN_HEADERS = {    # the column names of rows printed by programs that do not print a header
    15: 'instance,nodes,arcs,left,right,theta,theta_frac,status,matched,cost,cpu_ms,cpu_usr_ms,cpu_sys_ms,wall_ms,tag',
    16: 'instance,nodes,arcs,left,right,theta,theta_frac,cap,status,matched,cost,cpu_ms,cpu_usr_ms,cpu_sys_ms,wall_ms,tag',
    17: 'instance,nodes,arcs,left,right,theta,theta_frac,cap,status,matched,cost,cpu_ms,cpu_usr_ms,cpu_sys_ms,proc_ms,wall_ms,tag',
    25: 'instance,nodes,arcs,left,right,status,matched,cost,oracle,cpu_ms,t_parsed,t_oracle_in,t_csa_start,t_csa_done,t_leave_c,t_oracle_done,t_done,screen_ms,glue_in_ms,csa_ms,cert_ms,glue_out_ms,check_cleanup_ms,wall_ms,tag'}
_header_cache = {}
def program_header(prog):
    """the header line a program prints on --header, or None"""
    if prog not in _header_cache:
        h = None
        try:
            r = subprocess.run([prog, '--header'], capture_output=True, text=True, timeout=60)
            first = (r.stdout.strip().splitlines() or [''])[0]
            if 'cpu_ms' in first and first.startswith('instance'): h = first
        except Exception: pass
        _header_cache[prog] = h
    return _header_cache[prog]

def parse_row(out, prog=None):
    """the program's output -> (dict of its fields or {}, the raw line)"""
    lines = [l for l in out.strip().splitlines() if l.strip() and not l.startswith('c ')]
    if not lines: return {}, ''
    last = lines[-1]
    if '=' in last and ',' not in last.split()[0]:            # key=value pairs (the matroid programs)
        d = {}
        for kv in last.split():
            if '=' in kv: k, v = kv.split('=', 1); d[k] = v
        return d, last
    vals = next(csv.reader([last]))
    header = next((l for l in lines if l.startswith('instance,')), None) or (program_header(prog) if prog else None) or KNOWN_HEADERS.get(len(vals))
    if header:
        keys = header.split(',')
        if len(keys) == len(vals): return dict(zip(keys, vals)), last
        if len(keys) > len(vals) and keys[-1] == 'tag':      # a header that names clock columns the row leaves out
            d = dict(zip(keys[:len(vals) - 1], vals[:-1])); d['tag'] = vals[-1]; return d, last
    return {}, last

def classify(rc, row, err, cap_hit):
    st = row.get('status', '')
    if rc == 0 and (st in OK_STATUS or (not st and row.get('cpu_ms', '') != '')): return 'OK'
    if cap_hit or rc in (124, 137, -9, 152, -24) and 'TIMEOUT' in (st, err.upper()) or st.startswith('TIMEOUT') or rc == 124 or rc == 152 or rc == -24: return 'TIMEOUT'
    mem = re.search(r'out of memory|OutOfMemoryError|StackOverflowError|MemoryError|Cannot allocate|cannot allocate|Killed|stack overflow|exceeds limit|fatal error: runtime: out of memory', err)
    if st.startswith('MEMORY') or mem or rc in (137, -9): return 'MEMORY'
    if rc == 0 and st: return st
    return 'ERROR'

class Runner:
    def __init__(self, outdir, deadline):
        self.outdir = outdir; self.deadline = deadline
        self.files = {}; self.done = 0; self.total = 0; self.t0 = time.time()
    def writer(self, pkg, fam):
        if (pkg, fam) not in self.files:
            d = os.path.join(self.outdir, pkg, fam); os.makedirs(d, exist_ok=True)
            f = open(os.path.join(d, 'raw.csv'), 'a', newline='')
            w = csv.writer(f)
            if f.tell() == 0: w.writerow(RAW_FIELDS)
            self.files[(pkg, fam)] = (f, w)
        return self.files[(pkg, fam)]
    def record(self, j, status, cpu_ms, wall, rc, row, err):
        f, w = self.writer(j['pkg'], j['fam'])
        w.writerow([j['pkg'], j['col'], j['fam'], j['size'], j['nodes'], j['inst'], j['q'], j['rep'], status, cpu_ms, '%.1f' % wall, rc, row, err[-300:].replace('\n', ' | ')])
        f.flush(); self.done += 1
        log('%5d/%d %-26s %-30s %-14s %-18s %-26s rep%d %-18s %10s ms %7.1fs' % (self.done, self.total, j['pkg'], j['col'], j['fam'], j['size'], j['inst'][:26], j['rep'], status, cpu_ms, wall))
    def run_job(self, j):
        """one process: the single-run program under the paper's wrapper -> status"""
        pre = []
        if j['mode'] == 'prlimit' and shutil.which('prlimit'):
            pre += ['prlimit', '--cpu=%d' % j['cap']] + (['--as=%d' % AS_BYTES] if j.get('as_limit') else [])
            wall_cap = 3600
        else:
            pre += ['timeout', '-k', '10', str(j['cap'])]; wall_cap = j['cap'] + 60
        budget_cut = False
        if self.deadline:
            remaining = self.deadline - time.time()
            if remaining < wall_cap: wall_cap = max(1, int(remaining)); budget_cut = True
        warm = [sys.executable, WARM, str(j['warm']), '--'] if j.get('warm') else []
        env = dict(os.environ); env.update(j.get('env', {}))
        t0 = time.time()
        try:
            r = subprocess.run(pre + warm + j['cmd'], cwd=j['cwd'], capture_output=True, text=True, env=env, timeout=wall_cap)
            rc, out, err, cap_hit = r.returncode, r.stdout, r.stderr, False
        except subprocess.TimeoutExpired as e:
            rc, out, err, cap_hit = 124, (e.stdout or b'').decode(errors='replace') if isinstance(e.stdout, bytes) else (e.stdout or ''), 'WALL TIMEOUT', True
            if budget_cut: self.record(j, 'NOT_RUN', '', time.time() - t0, rc, '', 'stopped by the time budget'); return 'NOT_RUN'
        wall = time.time() - t0
        row, raw = parse_row(out, j['cmd'][0])
        status = classify(rc, row, err, cap_hit)
        cpu = row.get('cpu_ms', '') if status not in ('TIMEOUT', 'MEMORY', 'ERROR') else ''
        self.record(j, status, cpu, wall, rc, raw, err)
        return status
    def run_all(self, jobs, inst):
        self.total = len(jobs)
        last_use = {}
        for i, j in enumerate(jobs):
            for p in j['files']: last_use[p] = i
        ladder = {}      # (pkg, col, fam) -> (stopped at size, how); dead problems per ladder
        dead = {}
        out_of_time = False
        for i, j in enumerate(jobs):
            key = (j['pkg'], j['col'], j['fam']); prob = (j['inst'], j['q'])
            try:
                if j.get('na'): self.record(j, 'NOT_APPLICABLE', '', 0, '', '', j['na'])
                elif out_of_time or (self.deadline and time.time() >= self.deadline):
                    if not out_of_time: log('   the time budget is used up; the remaining runs are recorded NOT_RUN')
                    out_of_time = True; self.record(j, 'NOT_RUN', '', 0, '', '', 'not started: the time budget was used up')
                elif key in ladder and ladder[key][0] != j['size']:
                    self.record(j, ladder[key][1] + '_INFERRED', '', 0, '', '', 'not run: %s at size %s' % (ladder[key][1], ladder[key][0]))
                elif prob in dead.get(key, ()):
                    self.record(j, ladder[key][1] + '_INFERRED', '', 0, '', '', 'not run: %s on this problem' % ladder[key][1])
                elif not all(inst.ensure(p) for p in j['files']):
                    self.record(j, 'NOT_RUN', '', 0, '', '', 'instance could not be generated')
                else:
                    st = self.run_job(j)
                    if st in ('TIMEOUT', 'MEMORY'): ladder[key] = (j['size'], st); dead.setdefault(key, set()).add(prob)
                    if st == 'NOT_RUN': out_of_time = True
            except Exception as e:
                log('   run failed:', e); self.record(j, 'ERROR', '', 0, '', '', str(e))
            for p in j['files']:
                if last_use[p] == i: inst.delete(p)      # no run left that needs this instance
        for f, _ in self.files.values(): f.close()

# ----------------------------------------------------------------------------------------------
def main():
    global LOGF
    if len(sys.argv) != 2 or sys.argv[1] not in ('smoke', '8h', 'full'): sys.exit('usage: run_experiments.py smoke|8h|full')
    mode = sys.argv[1]; cf = conf(mode)
    if not os.path.exists(os.path.join(WORK, 'env.sh')): sys.exit('run setup/setup.sh %s first' % mode)
    outdir = os.path.join(EVAL, 'results', datetime.datetime.now().strftime('%Y%m%d_%H%M%S') + '_' + mode)
    os.makedirs(outdir); LOGF = open(os.path.join(outdir, 'run.log'), 'w')
    started = time.time(); deadline = None
    sp = os.path.join(WORK, 'started_' + mode)
    if os.path.exists(sp): started = float(open(sp).read().strip())
    if 'budget_hours' in cf:
        deadline = started + 3600 * float(cf['budget_hours'][0])
        log('mode %s: time budget %s h from %s, %.1f h left for the measurements' % (mode, cf['budget_hours'][0], datetime.datetime.fromtimestamp(started).isoformat(timespec='seconds'), (deadline - time.time()) / 3600))
    else: log('mode %s' % mode)
    source = os.path.join(WORK, 'exports', 'current', 'SOURCE.txt')
    inst = Instances()
    jobs, planned = make_plan(mode, cf, inst)
    log('plan: %d runs, %s' % (len(jobs), ', '.join('%s: %s' % (p, ' '.join(c)) for p, c in planned.items())))
    if not jobs: sys.exit('nothing to run')
    with open(os.path.join(outdir, 'columns.json'), 'w') as f: json.dump(planned, f, indent=1)
    with open(os.path.join(outdir, 'conditions.txt'), 'w') as f:
        f.write('mode: %s\nstarted: %s\nsetup_started: %s\ntimeout_s: %d\norder: %s\nbudget_hours: %s\nmachine: %s\n' % (
            mode, datetime.datetime.now().isoformat(timespec='seconds'), datetime.datetime.fromtimestamp(started).isoformat(timespec='seconds'), CAP, cf['order'][0], cf.get('budget_hours', ['-'])[0], os.uname().machine))
        try: f.write(open('/proc/cpuinfo').read().split('model name')[1].split('\n')[0].replace(': ', 'cpu: ').strip() + '\n')
        except Exception: pass
        try: f.write('mem_kB: ' + open('/proc/meminfo').readline().split()[1] + '\n')
        except Exception: pass
        f.write('code_exports: ' + (open(source).readline().strip('# \n') if os.path.exists(source) else 'unknown') + '\n')
        f.write('not_available: %s\n' % not_available().replace('\n', '; '))
    runner = Runner(outdir, deadline)
    try: runner.run_all(jobs, inst)
    finally: inst.cleanup()
    if inst.mismatch: log('   WARNING: regenerated instances differ from the recorded checksums: ' + ', '.join(inst.mismatch))
    log('   %d instance files generated and deleted again, %d checked against MD5SUM_instances.txt' % (inst.made, inst.checked))
    import resource
    with open(os.path.join(outdir, 'conditions.txt'), 'a') as f:
        f.write('finished: %s\nwall_s: %.0f\nmax_rss_of_any_run_kB: %d\n' % (datetime.datetime.now().isoformat(timespec='seconds'), time.time() - runner.t0, resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss))
    log('runs done in %.0f s; writing the tables' % (time.time() - runner.t0))
    subprocess.run([sys.executable, os.path.join(RUN, 'make_tables.py'), outdir])
    log('results in ' + os.path.relpath(outdir, EVAL))

if __name__ == '__main__':
    main()
