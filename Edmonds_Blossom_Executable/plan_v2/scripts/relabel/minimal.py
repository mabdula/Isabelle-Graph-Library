import json, re, subprocess, csv, importlib.util
V2 = '/home/llm/.claude/jobs/d07b4540/tmp/v2/'
E = '/media/llms/Isabelle-Graph-Library-Blossom-Executable/Edmonds_Blossom_Executable/'
TH = ['Blossom_Misc', 'Graph_Quotient', 'Graph_Quotient_Lifting', 'Blossom_Prefixes', 'Compute_Alt_Path_Invars']
MARK = re.compile(r' ?\\<\^marker>\\<open>provenance \w+\\<close>')
def mk(l): return r' \<^marker>\<open>provenance ' + l + r'\<close>'
spec = importlib.util.spec_from_file_location('cl', V2 + 'relabel/locate.py'); cl = importlib.util.module_from_spec(spec); spec.loader.exec_module(cl)
GOAL = {'lemma', 'theorem', 'corollary', 'have', 'show', 'hence', 'thus', 'obtain', 'interpret', 'consider'}
TERM = {'by', '.', '..', 'sorry', 'done', 'oops'}
desired = {t: ['human' if c['label'] in ('human', 'ai_human') else 'ai' for c in json.load(open(V2 + 'relabel/' + t + '.json'))] for t in TH}
def run_tool():
    subprocess.run('cd /media/llms/Isabelle-Graph-Library-Blossom-Executable && USER_HOME=/media/llms/isabelle-home-blossom '
                   'isabelle ai_provenance -o ' + V2 + 'relabel/cur.tsv Blossom_Executable > /dev/null 2>&1', shell=True, check=True)
    return list(csv.DictReader(open(V2 + 'relabel/cur.tsv'), delimiter='\t'))
for t in TH:   # strip every marker and every provenance command; one 'provenance human' after begin
    src = open(E + t + '.thy').read()
    out = []; seen_first = False
    for l in src.split('\n'):
        if re.match(r'^provenance \w+\s*$', l):
            if not seen_first:
                out.append('provenance human'); seen_first = True
            elif out and out[-1].strip() == '':
                out.pop()
            continue
        out.append(MARK.sub('', l))
    assert seen_first and len(out) > 50, t
    text = '\n'.join(out)
    with open(E + t + '.thy', 'w') as f:
        f.write(text)
rows = run_tool()
for t in TH:
    cmds = [c for c in cl.commands(E + t + '.thy', rows, t) if c['kw'] != 'provenance']
    want = desired[t]; assert len(cmds) == len(want), t
    stack = []; ins = []
    for c, d in zip(cmds, want):
        inh = stack[-1][1] if stack else 'human'
        own = d
        if d != inh:
            ins.append((c['line'], c['col'] + len(c['kw']), d))
        kw = c['kw']
        if kw in GOAL:
            stack.append(('goal', own))
        elif kw == 'proof':
            stack.append(('proof', own))
        elif kw in TERM:
            while stack and stack[-1][0] != 'goal': stack.pop()
            if stack: stack.pop()
        elif kw == 'qed':
            while stack and stack[-1][0] != 'proof': stack.pop()
            if stack: stack.pop()
            if stack and stack[-1][0] == 'goal': stack.pop()
    L = open(E + t + '.thy').read().split('\n'); assert len(L) > 50
    for ln, col, w in sorted(ins, key=lambda x: (x[0], -x[1])):
        L[ln - 1] = L[ln - 1][:col] + mk(w) + L[ln - 1][col:]
    open(E + t + '.thy', 'w').write('\n'.join(L))
    print(t, 'markers placed:', len(ins), flush=True)
for it in range(6):    # verify with the tool; fix remaining mismatches if the model was wrong anywhere
    rows = run_tool(); total = 0
    for t in TH:
        cmds = [c for c in cl.commands(E + t + '.thy', rows, t) if c['kw'] != 'provenance']
        fix = [(c['line'], c['col'] + len(c['kw']), w) for c, w in zip(cmds, desired[t]) if c['label'] != w]
        total += len(fix)
        if fix:
            L = open(E + t + '.thy').read().split('\n')
            for ln, col, w in sorted(fix, key=lambda x: (x[0], -x[1])):
                L[ln - 1] = L[ln - 1][:col] + mk(w) + L[ln - 1][col:]
            open(E + t + '.thy', 'w').write('\n'.join(L))
    print('verification pass', it, 'mismatches:', total, flush=True)
    if total == 0: break
