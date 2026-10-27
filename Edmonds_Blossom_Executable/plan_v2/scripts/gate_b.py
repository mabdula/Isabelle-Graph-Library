"""Stage B gate for one copied theory: compares the gated ASCII copy (BXG/<T>.thy, with its
provenance table BXG/prov.tsv) with the Stage A version and its provenance table.
usage: python3 gate_b.py THEORY"""
import csv, difflib, re, sys, subprocess
T = sys.argv[1]
V2 = '/home/llm/.claude/jobs/d07b4540/tmp/v2/'
A_FILE = '/media/llms/Isabelle-Graph-Library-Blossom-Executable/Edmonds_Blossom_Executable/backups/v2_stageA_green_2026-10-24/' + T + '.thy'
cur = open(V2 + 'BXG/' + T + '.thy').read().split('\n')
old = open(A_FILE).read().split('\n')
def labels(tsv, theory, n):
    lab = [None] * (n + 2)
    rows = [r for r in csv.DictReader(open(tsv), delimiter='\t') if r['theory'].split('.')[-1] == theory]
    for r in rows:
        s = int(r['line']); k = max(1, int(r['lines']))
        for i in range(s, min(n + 1, s + k)):
            lab[i] = r['label']
    return rows, lab
rows_c, lab_c = labels(V2 + 'BXG/prov.tsv', T, len(cur))
rows_a, lab_a = labels(V2 + 'gate/stageA_prov.tsv', T, len(old))
# 1. statements
print(subprocess.run(['python3', '/media/llms/Isabelle-Graph-Library-Blossom-Executable/Edmonds_Blossom_Executable/plan_v2/scripts/gate_stmts.py',
                      V2 + 'BXG/' + T + '.thy', A_FILE], capture_output=True, text=True).stdout.strip())
# 2. counts
txt = '\n'.join(cur)
cnt = {
  'metis': len(re.findall(r'\bmetis\b', txt)), 'smt': len(re.findall(r'\bsmt\b', txt)), 'meson': len(re.findall(r'\bmeson\b', txt)),
  'apply': len(re.findall(r'^\s*apply\b', txt, re.M)), 'blocks': len(re.findall(r'^\s*\{\s*$', txt, re.M)) + len(re.findall(r'^\s*\{\s+(fix|assume|have)\b', txt, re.M)),
  'proof -': len(re.findall(r'\bproof -', txt)),
  'same-line using/by': sum(1 for l in cur if re.match(r'^\s*(lemma|theorem|corollary|have|show|hence|thus|obtain|moreover have|ultimately have|ultimately show|then have|then show|then obtain|also have|finally have|finally show)\b.*\S.*\s(using|by)\b', l) and not re.match(r'^\s*(using|by)\b', l)),
  'sorry/oops': len(re.findall(r'\b(sorry|oops)\b', txt)),
}
print('counts:', cnt)
# 3. no unchanged human line in an ai scope
sm = difflib.SequenceMatcher(None, old, cur, autojunk=False)
bad = []
for tag, i1, i2, j1, j2 in sm.get_opcodes():
    if tag != 'equal': continue
    for k in range(j2 - j1):
        a, c = i1 + k + 1, j1 + k + 1
        if cur[c - 1].strip() and lab_a[a] == 'human' and lab_c[c] == 'ai':
            bad.append((c, cur[c - 1].strip()[:90]))
print('unchanged human lines now in ai scope:', len(bad))
for b in bad[:15]: print('  ', b)
# 4. labels summary
from collections import Counter
print('commands by label (Stage A -> now):', dict(Counter(r['label'] for r in rows_a)), '->', dict(Counter(r['label'] for r in rows_c)))
