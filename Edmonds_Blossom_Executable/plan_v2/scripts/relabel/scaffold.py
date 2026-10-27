"""Find ai commands in apply-script conversions that are mechanical: Isar scaffolding (case, next,
qed, show ?case/?thesis, the then before it), proof/by with a method of the original script, and
using with facts of the original script."""
import csv, re, difflib, importlib.util, sys, json
spec = importlib.util.spec_from_file_location('inv', '/home/llm/.claude/jobs/d07b4540/tmp/v4/inv_lib.py'); inv = importlib.util.module_from_spec(spec); spec.loader.exec_module(inv)
O = '/media/llms/Isabelle-Graph-Library-Blossom-Executable/Edmonds_Blossom_Algorithm/'
orows = list(csv.DictReader(open('/home/llm/.claude/jobs/d07b4540/tmp/v2/prov_orig.tsv'), delimiter='\t'))
crows = list(csv.DictReader(open(sys.argv[1]), delimiter='\t')); SRC = sys.argv[2]
SOURCES = {'Blossom_Misc': ['Blossom_Misc'], 'Graph_Quotient': ['Graph_Quotient'], 'Graph_Quotient_Lifting': ['Graph_Quotient'],
           'Blossom_Prefixes': ['Blossom_Algo_Contraction'], 'Compute_Alt_Path_Invars': ['Blossom_Algo_Search']}
def nz(t): return re.sub(r'\s+', '', t)
def strip_par(m):
    m = nz(m)
    while m.startswith('(') and m.endswith(')'): m = m[1:-1]
    return m
def facts(t):
    t = re.sub(r'^\s*using\s+', '', t)
    return set(x for x in re.findall(r"\\<open>.*?\\<close>|[\w'.]+(?:\[[^\]]*\])?(?:\([\d,\- ]+\))?", t))
targets = []
for th, srcs in SOURCES.items():
    cur = inv.texts(SRC + th + '.thy', th, crows)
    org = []
    for s in srcs: org += inv.texts(O + s + '.thy', s, orows)
    # innermost enclosing proof opener of every command (qed: the opener it closes)
    stack = []
    for c in cur:
        c['opener'] = stack[-1] if stack else None
        if c['kw'] == 'proof': stack.append(c)
        elif c['kw'] == 'qed':
            c['opener'] = stack.pop() if stack else None
    A = [nz(c['text']) for c in org]; B = [nz(c['text']) for c in cur]
    sm = difflib.SequenceMatcher(None, A, B, autojunk=False)
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag != 'replace': continue
        oc = org[i1:i2]; cc = cur[j1:j2]
        if not any(c['kw'] == 'apply' for c in oc): continue
        if any(c['kw'] in ('lemma', 'theorem', 'corollary', 'definition', 'fun') for c in oc): continue
        meths = [strip_par(c['text'][len(c['kw']):]) for c in oc if c['kw'] in ('apply', 'by')]
        meths = [m for m in meths if not re.search(r'\b(metis|smt|meson)\b', m)]
        meths = meths + [strip_par(p.rstrip('+')) for m in meths for p in m.split(';')]
        ofacts = set().union(*[facts(c['text']) for c in oc if c['kw'] == 'using']) if any(c['kw'] == 'using' for c in oc) else set()
        for k, c in enumerate(cc):
            if c['label'] != 'ai': continue
            t = c['text']; kw = c['kw']; why = None
            nxt = cc[k + 1]['text'] if k + 1 < len(cc) else ''
            if kw in ('case', 'next'): why = 'scaffold'
            elif kw == 'qed' and t.strip() == 'qed': why = 'scaffold'
            elif kw == 'show' and t.strip() in ('show ?case', 'show ?thesis'): why = 'scaffold'
            elif kw == 'then' and nxt.strip() in ('show ?case', 'show ?thesis'): why = 'scaffold'
            elif kw == 'proof':
                m = re.sub(r',\s*goal_cases\s*\)$', ')', t[len('proof'):].strip())
                m = strip_par(m)
                if m and any(o == m or o.startswith(m + ';') for o in meths): why = 'method of the script'
            elif kw in ('by', 'qed'):
                m = strip_par(t[len(kw):])
                if m and m in meths: why = 'method of the script'
            elif kw == 'using':
                f = facts(t)
                if f and f <= ofacts: why = 'facts of the script'
            if why == 'scaffold':
                op = c['opener']
                if op is None or not (op['label'] == 'human' or op.get('target')): why = None
            if why:
                c['target'] = True
                targets.append({'theory': th, 'line': c['line'], 'col': c['col'], 'kw': kw, 'text': t[:100], 'why': why})
json.dump(targets, open(sys.argv[3], 'w'), indent=0)
from collections import Counter
print(len(targets), Counter((t['theory'], t['why']) for t in targets))
