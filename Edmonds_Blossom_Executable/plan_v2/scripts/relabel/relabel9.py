"""Desired labels = labels in prov.tsv, with the targets set to human. Strip the markers of the
copied theories, place minimal markers, verify with the tool (prov.sh) and fix mismatches."""
import csv, json, re, subprocess, importlib.util
V = '/home/llm/.claude/jobs/d07b4540/tmp/v7/'
TH = ['Blossom_Misc', 'Graph_Quotient', 'Graph_Quotient_Lifting', 'Blossom_Prefixes', 'Compute_Alt_Path_Invars']
spec = importlib.util.spec_from_file_location('cl', '/home/llm/.claude/jobs/d07b4540/tmp/v2/relabel/locate.py'); cl = importlib.util.module_from_spec(spec); spec.loader.exec_module(cl)
MARK = re.compile(r' ?\\<\^marker>\\<open>provenance \w+\\<close>')
def mk(l): return r' \<^marker>\<open>provenance ' + l + r'\<close>'
GOAL = {'lemma', 'theorem', 'corollary', 'have', 'show', 'hence', 'thus', 'obtain', 'interpret', 'consider'}
TERM = {'by', '.', '..', 'sorry', 'done', 'oops'}
def rows_of(tsv): return list(csv.DictReader(open(tsv), delimiter='\t'))
def run_tool():
    subprocess.run(V + 'prov.sh ' + V + 'prov_iter.tsv > /dev/null', shell=True, check=True)
    return rows_of(V + 'prov_iter.tsv')
rows = rows_of(V + 'prov_cur.tsv')
import sys
sys.path.insert(0, V)
exec(open(V + 'desired.py').read().split("if __name__")[0])
desired = {t: [d for c, d in desired_for(t)] for t in TH}
# provenance commands: keep the first one (theory label), drop the others
for t in TH:
    out = []; first = None
    for l in open(V + t + '.thy').read().split('\n'):
        if re.match(r'^provenance \w+\s*$', l):
            if first is None: first = l; out.append(l)
            elif out and out[-1].strip() == '': out.pop()
            continue
        out.append(MARK.sub('', l))
    assert first == 'provenance human', (t, first)
    open(V + t + '.thy', 'w').write('\n'.join(out))
rows = run_tool()
for t in TH:
    cmds = [c for c in cl.commands(V + t + '.thy', rows, t) if c['kw'] != 'provenance']
    want = desired[t]; assert len(cmds) == len(want), (t, len(cmds), len(want))
    stack = []; ins = []
    for c, d in zip(cmds, want):
        inh = stack[-1][1] if stack else 'human'
        if d != inh: ins.append((c['line'], c['col'] + len(c['kw']), d))
        kw = c['kw']
        if kw in GOAL: stack.append(('goal', d))
        elif kw == 'proof': stack.append(('proof', d))
        elif kw in TERM:
            while stack and stack[-1][0] != 'goal': stack.pop()
            if stack: stack.pop()
        elif kw == 'qed':
            while stack and stack[-1][0] != 'proof': stack.pop()
            if stack: stack.pop()
            if stack and stack[-1][0] == 'goal': stack.pop()
    L = open(V + t + '.thy').read().split('\n')
    for ln, col, w in sorted(ins, key=lambda x: (x[0], -x[1])):
        L[ln - 1] = L[ln - 1][:col] + mk(w) + L[ln - 1][col:]
    open(V + t + '.thy', 'w').write('\n'.join(L))
    print(t, 'markers placed:', len(ins), flush=True)
for it in range(8):
    rows = run_tool(); total = 0
    for t in TH:
        cmds = [c for c in cl.commands(V + t + '.thy', rows, t) if c['kw'] != 'provenance']
        fix = [(c['line'], c['col'] + len(c['kw']), w) for c, w in zip(cmds, desired[t]) if c['label'] != w]
        total += len(fix)
        if fix:
            L = open(V + t + '.thy').read().split('\n')
            for ln, col, w in sorted(fix, key=lambda x: (x[0], -x[1])):
                L[ln - 1] = L[ln - 1][:col] + mk(w) + L[ln - 1][col:]
            open(V + t + '.thy', 'w').write('\n'.join(L))
    print('verification pass', it, 'mismatches:', total, flush=True)
    if total == 0: break
