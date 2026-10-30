#!/usr/bin/env python3
"""Turns the raw rows of a run into the paper's tables, projected to the columns the run measured, next to the
values of the paper appendix.

    make_tables.py <results dir>        (run_experiments.py calls it; it can be re-run by hand)

Reads <results dir>/<benchmark>/<family>/raw.csv and <results dir>/columns.json (the columns the run planned) and writes
    <results dir>/<benchmark>/<family>/table.csv         the paper's table, measured by this run (cell = seconds (ratio))
    <results dir>/<benchmark>/<family>/table_paper.csv   the same table as in the paper appendix, the same columns
    <results dir>/<benchmark>/<family>/raw.csv           every run's row (written by run_experiments.py)
    <results dir>/SUMMARY.txt                            per table: cells measured, deviation from the paper
A cell is formed as the benchmark's PROTOCOL.txt describes: per problem the median of the repeats,
per size the mean over the problems that finished (k/m marks a partial mean); push-relabel
rmf-long and wash-rlg-long: the mean over the three seeds; ak: the median of three runs;
matroid intersection: the mean over the instances; the hybrid solver: per instance the
repeat with the median total, then the mean of each component.  Ratios are to the SML column
of the same size.  TO = timed out, OOM = out of memory, ERR = other error, - = not run.
The values of the paper appendix come from each package's paper_results zip, formed the same way.
"""
import csv, io, json, os, re, statistics, sys, zipfile, collections

EVAL = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BENCH = os.path.join(EVAL, 'benchmarks')
TABLES = [  # number, package, family, title, problems (matroid only)
    (5, 'dfs', 'Square-n', 'Depth-first search, Square-n'), (6, 'dfs', 'Long-n', 'Depth-first search, Long-n'),
    (7, 'dfs', 'Dense-n', 'Depth-first search, dense connected random'), (8, 'dfs', 'USA-road-t', 'Depth-first search, USA-road-t'),
    (9, 'bfs', 'Square-n', 'Breadth-first search, Square-n'), (10, 'bfs', 'Long-n', 'Breadth-first search, Long-n'),
    (11, 'bfs', 'Dense-n', 'Breadth-first search, dense connected random'), (12, 'bfs', 'USA-road-t', 'Breadth-first search, USA-road-t'),
    (13, 'dijkstra', 'Square-n', "Dijkstra's algorithm, Square-n"), (14, 'dijkstra', 'Long-n', "Dijkstra's algorithm, Long-n"), (15, 'dijkstra', 'USA-road-t', "Dijkstra's algorithm, USA-road-t"),
    (16, 'kruskal', 'Square-n', "Kruskal's algorithm, Square-n"), (17, 'kruskal', 'Long-n', "Kruskal's algorithm, Long-n"), (18, 'kruskal', 'Dense-n', "Kruskal's algorithm, dense connected random"),
    (19, 'push_relabel', 'rmf-long', 'Push-relabel, RMF-long'), (20, 'push_relabel', 'wash-rlg-long', 'Push-relabel, WASH-RLG-long'), (21, 'push_relabel', 'ak', 'Push-relabel, AK'),
    (22, 'hungarian', 'low-cost', 'Hungarian method, low-cost'), (23, 'hungarian', 'two-cost', 'Hungarian method, two-cost'), (24, 'hungarian', 'geometric', 'Hungarian method, geometric'),
    (25, 'matroid_intersections', 'low-cost+two-cost', 'Matroid intersection, unweighted problems on low-cost and two-cost'),
    (26, 'matroid_intersections', 'low-cost', 'Matroid intersection, weighted problems on low-cost'),
    (27, 'matroid_intersections', 'two-cost', 'Matroid intersection, weighted problems on two-cost'),
    (28, 'matroid_intersections', 'geometric', 'Matroid intersection, geometric'),
    (35, 'hybrid_bipartite_matching', 'low-cost', 'Hybrid bipartite matching solver with CSA, low-cost'),
    (36, 'hybrid_bipartite_matching', 'two-cost', 'Hybrid bipartite matching solver with CSA, two-cost'),
    (37, 'hybrid_bipartite_matching', 'geometric', 'Hybrid bipartite matching solver with CSA, geometric')]
COLS = {'dfs': ['sml_csr', 'sml_lists', 'sml_rbt', 'scala_csr', 'scala_lists', 'scala_rbt', 'go_csr', 'go_lists', 'go_rbt', 'lemon_csr', 'lemon_linked', 'jgrapht_csr', 'jgrapht_hashgraph', 'scipy_csr', 'scipy_prebuilt', 'networkx'],
        'bfs': ['sml_csr', 'sml_rbt', 'scala_csr', 'scala_rbt', 'go_csr', 'go_rbt', 'lemon_csr', 'lemon_linked', 'jgrapht_csr', 'jgrapht_hashgraph', 'scipy_csr', 'scipy_prebuilt', 'networkx'],
        'dijkstra': ['sml', 'scala', 'go', 'lemon_csr', 'lemon_linked', 'jgrapht_csr', 'jgrapht_hashgraph', 'scipy_csr', 'scipy_prebuilt', 'networkx'],
        'kruskal': ['sml', 'scala', 'go', 'lemon', 'jgrapht', 'scipy', 'networkx'],
        'push_relabel': ['sml_hl', 'sml_fifo', 'sml_afp', 'lemon_csr', 'lemon_linked', 'jgrapht', 'scipy_csr', 'scipy_prebuilt', 'networkx', 'hipr'],
        'hungarian': ['sml', 'scala', 'go', 'csa_q_csr', 'ortools', 'scipy_lsa', 'scipy_mwfbm_csr', 'jgrapht_kuhnmunkres_threadgc', 'jgrapht_mwbm_csr', 'jgrapht_mwbm_hashgraph'],
        'matroid_intersections': ['sml', 'scala', 'go', 'sage_oracle', 'sage_plain'],
        'hybrid_bipartite_matching': ['oracle_ms', 'cert_ms', 'check_ms', 'glue_ms', 'total_ms', 'total_over_oracle']}
PAPER_NAMES = {'sml_csr': 'SML CSR', 'sml_lists': 'SML lists', 'sml_rbt': 'SML RBT', 'scala_csr': 'Scala CSR', 'scala_lists': 'Scala lists', 'scala_rbt': 'Scala RBT',
               'go_csr': 'Go CSR', 'go_lists': 'Go lists', 'go_rbt': 'Go RBT', 'lemon_csr': 'LEMON CSR', 'lemon_linked': 'LEMON linked', 'jgrapht_csr': 'JGraphT CSR',
               'jgrapht_hashgraph': 'JGraphT hash', 'scipy_csr': 'SciPy CSR', 'scipy_prebuilt': 'SciPy prebuilt', 'networkx': 'NetworkX', 'sml': 'SML', 'scala': 'Scala', 'go': 'Go',
               'lemon': 'LEMON', 'jgrapht': 'JGraphT', 'scipy': 'SciPy', 'sml_hl': 'SML HL', 'sml_fifo': 'SML FIFO', 'sml_afp': 'SML AFP', 'hipr': 'GC (hi_pr)',
               'csa_q_csr': 'CSA CSR', 'ortools': 'OR-Tools', 'scipy_lsa': 'SciPy LSA', 'scipy_mwfbm_csr': 'SciPy MWFBM CSR', 'jgrapht_kuhnmunkres_threadgc': 'JGraphT KM with GC',
               'jgrapht_mwbm_csr': 'JGraphT MWBM CSR', 'jgrapht_mwbm_hashgraph': 'JGraphT MWBM hash', 'sage_oracle': 'Sage (our oracle)', 'sage_plain': 'Sage (plain)',
               'oracle_ms': 'Oracle', 'cert_ms': 'Cert.', 'check_ms': 'Check', 'glue_ms': 'Glue', 'total_ms': 'Total', 'total_over_oracle': 'Total/Oracle'}
BFS_NAMES = {'sml_csr': 'SML imp.', 'sml_rbt': 'SML func.', 'scala_csr': 'Scala imp.', 'scala_rbt': 'Scala func.', 'go_csr': 'Go imp.', 'go_rbt': 'Go func.'}
def paper_name(pkg, c):
    if '/' in c:
        s, p = c.split('/'); return '%s %s' % (p.replace('_', ' '), PAPER_NAMES.get(s, s))
    if pkg == 'bfs' and c in BFS_NAMES: return BFS_NAMES[c]
    return PAPER_NAMES.get(c, c)
BASE = {'dfs': 'sml_csr', 'bfs': 'sml_csr', 'dijkstra': 'sml', 'kruskal': 'sml', 'push_relabel': 'sml_hl', 'hungarian': 'sml', 'matroid_intersections': 'sml'}
PROBLEMS = {25: ['matching', 'b_matching'], 26: ['weighted_matching', 'weighted_b_matching'], 27: ['weighted_matching', 'weighted_b_matching'], 28: ['matching', 'b_matching', 'weighted_matching', 'weighted_b_matching']}
ZIPS = {'dfs': 'dfs_results.zip', 'bfs': 'bfs_results.zip', 'dijkstra': 'dijkstra_results.zip', 'kruskal': 'kruskal_results.zip', 'push_relabel': 'push_relabel_results.zip',
        'hungarian': 'hungarian_results.zip', 'matroid_intersections': 'solver_csvs.zip', 'hybrid_bipartite_matching': 'hybrid_timings.zip'}

def status_of(statuses):
    s = ' '.join(statuses)
    if 'TIMEOUT' in s: return 'TO'
    if 'MEMORY' in s or 'OOM' in s: return 'OOM'
    if 'NOT_RUN' in s: return 'NOT_RUN'
    if 'NOT_ATTEMPTED' in s or not s.strip(): return '-'
    if 'NOT_APPLICABLE' in s: return 'n/a'
    return 'ERR'

def fmt(x):
    """seconds as the paper prints them: three significant digits down to 0.001, four decimals below"""
    if x is None: return ''
    if isinstance(x, str): return x
    if x >= 100: return '%.0f' % x
    if x >= 10: return '%.1f' % x
    if x >= 1: return '%.2f' % x
    if x >= 0.01: return '%.3f' % x
    if x < 0.00005: return '<0.0001'
    return '%.4f' % x
def fmt_ratio(x):
    if x is None: return ''
    if x >= 100: return '%.0f' % x
    if x >= 10: return '%.1f' % x
    return '%.2f' % x

# ------------------------------------------------------------------ measured cells
def load_raw(resdir):
    rows = []
    for pkg in sorted(os.listdir(resdir)):
        p = os.path.join(resdir, pkg)
        if not os.path.isdir(p): continue
        for fam in sorted(os.listdir(p)):
            f = os.path.join(p, fam, 'raw.csv')
            if os.path.exists(f): rows += list(csv.DictReader(open(f)))
    return rows

def program_field(r, key):
    row = r.get('program_row', '')
    if '=' in row and ',' not in row.split()[0]:
        for kv in row.split():
            if kv.startswith(key + '='): return kv.split('=', 1)[1]
        return None
    return None

def measured_cells(rows):
    """{(pkg, col, fam, size): cell}; cell = dict(value, status, k, m, nodes, parts) ; value in ms"""
    by = collections.defaultdict(list)
    for r in rows: by[(r['package'], r['column'], r['family'], r['size'])].append(r)
    cells = {}
    for key, rs in by.items():
        pkg, col, fam, size = key
        probs = collections.defaultdict(list)
        for r in rs: probs[(r['instance'], r['query'])].append(r)
        per_problem = []; statuses = []
        nodes = rs[0]['nodes'] or ''
        for p, prs in probs.items():
            ok = [float(r['cpu_ms']) for r in prs if r['status'] == 'OK' and r['cpu_ms'] not in ('', None)]
            statuses += [r['status'] for r in prs if r['status'] != 'OK']
            if pkg == 'push_relabel' and fam != 'ak':
                if ok: per_problem.append(ok[0])           # one run per seed
            elif pkg == 'hybrid_bipartite_matching':
                good = [r for r in prs if r['status'] == 'OK' and r['cpu_ms']]
                if len(good) == len(prs) and good:
                    good.sort(key=lambda r: float(r['cpu_ms']))
                    per_problem.append(good[len(good) // 2])  # the median repeat's row
            else:
                if ok and len(ok) == len(prs): per_problem.append(statistics.median(ok))
        m = len(probs)
        if pkg == 'push_relabel' and fam != 'ak': m = len(probs)
        k = len(per_problem)
        cell = dict(k=k, m=m, nodes=nodes, status='')
        if pkg == 'hybrid_bipartite_matching':
            if k:
                def comp(name):
                    vals = []
                    for r in per_problem:
                        d = dict(zip(['instance', 'nodes', 'arcs', 'left', 'right', 'status', 'matched', 'cost', 'oracle', 'cpu_ms', 't_parsed', 't_oracle_in', 't_csa_start', 't_csa_done', 't_leave_c', 't_oracle_done', 't_done', 'screen_ms', 'glue_in_ms', 'csa_ms', 'cert_ms', 'glue_out_ms', 'check_cleanup_ms', 'wall_ms', 'tag'], next(csv.reader([r['program_row']]))))
                        if name == 'glue_ms': vals.append(float(d['screen_ms']) + float(d['glue_in_ms']) + float(d['glue_out_ms']))
                        elif name == 'oracle_ms': vals.append(float(d['csa_ms']))
                        elif name == 'cert_ms': vals.append(float(d['cert_ms']))
                        elif name == 'check_ms': vals.append(float(d['check_cleanup_ms']))
                        else: vals.append(float(d['cpu_ms']))
                    return statistics.mean(vals)
                cell['parts'] = {n: comp(n) for n in ('oracle_ms', 'cert_ms', 'check_ms', 'glue_ms', 'total_ms')}
                cell['parts']['total_over_oracle'] = cell['parts']['total_ms'] / cell['parts']['oracle_ms'] if cell['parts']['oracle_ms'] else None
                cell['value'] = cell['parts']['total_ms']
            else: cell['value'] = None; cell['status'] = status_of(statuses)
        else:
            cell['value'] = statistics.mean(per_problem) if k else None
            if not k: cell['status'] = status_of(statuses)
        cells[key] = cell
        if pkg == 'hybrid_bipartite_matching':        # the table's columns are the phases of the one hybrid run
            for c in COLS[pkg]: cells[(pkg, c, fam, size)] = cell
    return cells

# ------------------------------------------------------------- cells of the paper appendix
def paper_cells(pkg):
    """{(col, fam, rowkey): (value_ms or None, status, nodes)} from the package's paper_results zip"""
    z = os.path.join(BENCH, pkg, 'paper_results', ZIPS[pkg])
    out = {}
    if not os.path.exists(z): return out
    zf = zipfile.ZipFile(z)
    for n in zf.namelist():
        parts = n.split('/')
        if not n.endswith('.csv'): continue
        text = zf.read(n).decode()
        if pkg == 'hybrid_bipartite_matching':
            m = re.match(r'(.*)_n(\d+)\.csv', parts[-1])
            if not m or len(parts) != 3: continue
            fam, N = m.group(1), m.group(2)
            rs = list(csv.DictReader(io.StringIO(text)))
            def mean(f): return statistics.mean(f(r) for r in rs)
            p = {'oracle_ms': mean(lambda r: float(r['csa_ms'])), 'cert_ms': mean(lambda r: float(r['cert_ms'])), 'check_ms': mean(lambda r: float(r['check_cleanup_ms'])),
                 'glue_ms': mean(lambda r: float(r['screen_ms']) + float(r['glue_in_ms']) + float(r['glue_out_ms'])), 'total_ms': mean(lambda r: float(r['cpu_ms']))}
            p['total_over_oracle'] = p['total_ms'] / p['oracle_ms']
            for c, v in p.items(): out[(c, fam, N)] = (v, '', N)
        elif pkg == 'matroid_intersections':
            if len(parts) != 4: continue
            solver, problem, fam = parts[1], parts[2], parts[3][:-4]
            byn = collections.defaultdict(list); st = collections.defaultdict(list)
            for r in csv.DictReader(io.StringIO(text)):
                if r['status'] == 'ok' and r['cpu_ms'] != '': byn[r['n']].append(float(r['cpu_ms']))
                else: st[r['n']].append(r['status'])
            for N in set(byn) | set(st):
                out[(solver + '/' + problem, fam, N)] = (statistics.mean(byn[N]) if byn[N] else None, '' if byn[N] else status_of(st[N]).replace('ERR', 'TO' if 'timeout' in ' '.join(st[N]) else 'ERR'), N)
        else:
            if 'raw' in parts or len(parts) != 3: continue
            col, fam = parts[1], parts[2][:-4]
            rs = list(csv.DictReader(io.StringIO(text)))
            for r in rs:
                key = r.get('rung') or r['nodes']
                val = r.get('average_ms') or r.get('median_ms') or r.get('mean_ms') or ''
                cells = [v for k2, v in r.items() if re.match(r'^[sr]\d+$', k2 or '')]
                out[(col, fam, key)] = (float(val) if val else None, '' if val else status_of(cells), r['nodes'])
    return out

# ------------------------------------------------------------------ tables
def main():
    resdir = sys.argv[1]
    rows = load_raw(resdir)
    pj = os.path.join(resdir, 'columns.json')
    planned = json.load(open(pj)) if os.path.exists(pj) else {}     # the columns the run measured: the tables are projected to them
    cells = measured_cells(rows)
    tdir = resdir
    summary = []; allcells = []
    pubcache = {}
    for num, pkg, fam, title in TABLES:
        pub = pubcache.setdefault(pkg, paper_cells(pkg))
        fams = fam.split('+') if '+' in fam else [fam]
        solvers = [c for c in COLS[pkg] if pkg not in planned or c in planned[pkg] or pkg == 'hybrid_bipartite_matching']
        if pkg == 'matroid_intersections':
            cols = ['%s/%s' % (s, p) for p in PROBLEMS[num] for s in solvers]
        else: cols = solvers
        sizes = []
        for (p, c, f, s) in cells:
            if p == pkg and f in fams and s not in sizes: sizes.append(s)
        if not sizes: continue
        sizes.sort(key=lambda s: (len(s), s))
        base = BASE.get(pkg)
        header = ['nodes']
        for c in cols:
            header += [c + '_s' if pkg != 'hybrid_bipartite_matching' else c, c + '_x', c + '_paper_s' if pkg != 'hybrid_bipartite_matching' else c + '_paper', c + '_paper_x'] if pkg != 'hybrid_bipartite_matching' else [c, c + '_paper']
        out = [header]; devs = []; measured = 0; any_cell = False
        # the paper prints TO for the sizes above a column's first timeout, which the campaign did not attempt
        to_from = {}
        for (c, f, k), (v, st, nd) in pub.items():
            if f in fams and st == 'TO' and str(nd).isdigit(): to_from[c] = min(to_from.get(c, int(nd)), int(nd))
        for s in sizes:
            def mcell(c):
                if len(fams) == 1: return cells.get((pkg, c, fams[0], s))
                # Table 25: pool the two families' runs (mean over both families' per-problem values)
                vals = [cells.get((pkg, c, f, s)) for f in fams]; vals = [v for v in vals if v]
                if not vals: return None
                ks = sum(v['k'] for v in vals); ms = sum(v['m'] for v in vals)
                good = [v for v in vals if v['value'] is not None]
                return dict(k=ks, m=ms, nodes=vals[0]['nodes'], value=(sum(v['value'] * v['k'] for v in good) / ks) if ks else None, status=vals[0]['status'] if not ks else '')
            nodes_key = next((cells[(pkg, c2, f2, s)]['nodes'] for c2 in cols for f2 in fams if (pkg, c2, f2, s) in cells and cells[(pkg, c2, f2, s)]['nodes']), s)
            def pcell(c):
                keys = [(c, f, (str(nodes_key) if pkg in ('dfs', 'bfs', 'dijkstra', 'kruskal') else s)) for f in fams]
                vals = [pub.get(k) for k in keys]; vals = [v for v in vals if v]
                if not vals: return None
                good = [v[0] for v in vals if v[0] is not None]
                return (statistics.mean(good) if good else None, vals[0][1], vals[0][2])
            nodes = next((mcell(c)['nodes'] for c in cols if mcell(c) and mcell(c)['nodes']), '')
            if not nodes:
                pn = next((pcell(c)[2] for c in cols if pcell(c)), ''); nodes = pn or s
            line = [nodes]
            for c in cols:
                mc = mcell(c); pc = pcell(c)
                bc = ('%s/%s' % (base, c.split('/')[1]) if '/' in c else base) if base else None   # the ratio's base: the SML column of the same problem
                mb = mcell(bc) if bc else None; pb = pcell(bc) if bc else None
                if mc is not None: any_cell = True
                if pkg == 'hybrid_bipartite_matching':
                    mv = mc['parts'].get(c) if mc and mc.get('parts') else None
                    pv = pc[0] if pc else None
                    line += [fmt(mv) if mv is not None else (mc['status'] if mc else 'not available'), fmt(pv) if pv is not None else (pc[1] if pc else '')]
                    if mv is not None and pv:
                        measured += 1
                        if mv > 0: devs.append((mv / pv, c, s))
                    elif mv is not None: measured += 1
                    continue
                if mc is None:
                    line += ['not available' if any(cells.get((pkg, c2, f2, s)) for c2 in cols for f2 in fams) else '', '']
                else:
                    if mc['value'] is not None:
                        v = mc['value'] / 1000.0; measured += 1
                        km = '' if mc['k'] == mc['m'] else ' %d/%d' % (mc['k'], mc['m'])
                        x = (mc['value'] / mb['value']) if (mb and mb.get('value')) else None
                        line += [fmt(v) + km, fmt_ratio(x) if x is not None else ('-' if mb else '')]
                    else: line += [mc['status'] or '-', '']
                if pc is None: line += ['', '']
                else:
                    pv, pst, _ = pc
                    if pv is not None:
                        px = (pv / pb[0]) if (pb and pb[0]) else None
                        line += [fmt(pv / 1000.0), fmt_ratio(px) if px is not None else ('-' if pb else '')]
                        if mc and mc['value'] is not None and pv > 0 and mc['value'] > 0: devs.append((mc['value'] / pv, c, s))
                    else:
                        if pst == '-' and c in to_from and str(pc[2]).isdigit() and int(pc[2]) > to_from[c]: pst = 'TO'
                        line += [pst or '-', '']
                allcells.append([num, pkg, fam, s, nodes, c, mc['value'] / 1000.0 if mc and mc['value'] is not None else (mc['status'] if mc else ''), pc[0] / 1000.0 if pc and pc[0] is not None else (pc[1] if pc else '')])
            out.append(line)
        if not any_cell: continue          # none of this table's problems was run
        fdir = os.path.join(resdir, pkg, fam.replace('+', '_and_')); os.makedirs(fdir, exist_ok=True)
        # the table as the paper prints it: one cell "seconds (ratio)" per solver, and the one of the paper appendix beside it
        hyb = pkg == 'hybrid_bipartite_matching'
        hdr = ['n'] + [paper_name(pkg, c) for c in cols]
        def paper_cell(line, k, hyb):
            if hyb: return line[1 + 2 * k]
            v, x = line[1 + 4 * k], line[2 + 4 * k]
            return (v + (' (%s)' % x if x else '')) if v else ''
        def pub_cell(line, k, hyb):
            if hyb: return line[2 + 2 * k]
            v, x = line[3 + 4 * k], line[4 + 4 * k]
            return (v + (' (%s)' % x if x else '')) if v else ''
        unit = 'milliseconds' if hyb else 'seconds (ratio to %s)' % base
        for fname, cellf, head in (('table.csv', paper_cell, '# Table %d of the paper, measured by this run: %s. Cell = %s; TO, OOM, ERR, n/a and k/m as in the paper.'),
                                   ('table_paper.csv', pub_cell, '# Table %d as in the paper appendix: %s. Cell = %s.')):
            with open(os.path.join(fdir, fname), 'w', newline='') as f:
                w = csv.writer(f)
                w.writerow([head % (num, title, unit)])
                if pkg == 'matroid_intersections':
                    w.writerow(['problem', 'n'] + [paper_name(pkg, s) for s in solvers])
                    for pr in PROBLEMS[num]:
                        for line in out[1:]:
                            w.writerow([pr.replace('_', ' '), line[0]] + [cellf(line, cols.index('%s/%s' % (s, pr)), hyb) for s in solvers])
                elif hyb:
                    w.writerow(['n', 'm'] + hdr[1:])
                    for line in out[1:]:
                        arcs = next((r['program_row'].split(',')[2] for r in rows if r['package'] == pkg and r['family'] == fam and r['nodes'] == str(line[0]) and r['program_row']), '')
                        w.writerow([line[0], arcs] + [cellf(line, k, hyb) for k in range(len(cols))])
                else:
                    w.writerow(hdr)
                    for line in out[1:]: w.writerow([line[0]] + [cellf(line, k, hyb) for k in range(len(cols))])
        if devs:
            import math
            logs = sorted(abs(math.log(d)) for d, _, _ in devs)
            worst = max(devs, key=lambda t: abs(math.log(t[0])))
            summary.append('Table %2d %-62s %3d cells; median |measured/paper| %.2fx, worst %.2fx (%s at %s)' % (num, title, len(devs), math.exp(logs[len(logs) // 2]), worst[0], worst[1], worst[2]))
        else:
            summary.append('Table %2d %-62s %3d cells measured, no paper-appendix value to compare' % (num, title, measured))
    with open(os.path.join(resdir, 'SUMMARY.txt'), 'w') as f:
        f.write('Measured cells against the tables of the paper appendix (ratio of the measured mean to the mean of the paper appendix; 1.00x is a perfect reproduction).\n')
        f.write('On another machine the absolute times differ by a constant; the *_x columns (ratios to SML) are the ones to compare.\n\n')
        f.write('\n'.join(summary) + '\n')
        na = os.path.join(EVAL, 'NOT_AVAILABLE.txt')
        if os.path.exists(na):
            f.write('\nNot run (NOT_AVAILABLE.txt):\n' + open(na).read())
        cond = os.path.join(resdir, 'conditions.txt')
        if os.path.exists(cond): f.write('\nConditions of this run:\n' + open(cond).read())
    print('\n'.join(summary))

if __name__ == '__main__':
    main()
