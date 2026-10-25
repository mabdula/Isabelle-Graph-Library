"""Classify every command of a copied theory against its original source:
human (identical), ai_human (edited), ai (added). Writes desired.json."""
import csv, re, difflib, json, sys
V2 = '/home/llm/.claude/jobs/d07b4540/tmp/v2/'
THEORY, CUR_FILE, CUR_TSV, OUT = sys.argv[1:5]
SOURCES = json.loads(sys.argv[5])  # [[file, theory, lo, hi], ...]
MARK = re.compile(r'\\<\^marker>\\<open>provenance \w+\\<close>\s*')
TRIVIAL = {'qed', 'next', 'done', '.', '..', 'end', 'then', 'moreover', 'ultimately', 'also', 'finally', 'note'}
def commands(path, tsv, theory, lo=1, hi=10**9):
    L = open(path).read().split('\n')
    rows = [r for r in csv.DictReader(open(tsv), delimiter='\t') if r['theory'].split('.')[-1] == theory and r['command'] != 'theory']
    pos = []; last = (0, 0)
    for r in rows:
        ln = int(r['line']); kw = r['command']
        start_col = last[1] if last[0] == ln else 0
        pat = re.escape(kw) if not kw[0].isalpha() else r'(?<![\w.])' + re.escape(kw) + r'(?![\w])'
        m = re.compile(pat).search(L[ln - 1], start_col)
        col = m.start() if m else start_col
        pos.append((ln, col, kw)); last = (ln, col + len(kw))
    out = []
    for i, (ln, col, kw) in enumerate(pos):
        if i + 1 < len(pos):
            nl, nc, _ = pos[i + 1]
            txt = L[ln - 1][col:] if nl != ln else L[ln - 1][col:nc]
            if nl != ln:
                txt = '\n'.join([txt] + L[ln:nl - 1] + [L[nl - 1][:nc]])
        else:
            txt = '\n'.join([L[ln - 1][col:]] + L[ln:])
        norm = ' '.join(MARK.sub('', txt).split())
        if lo <= ln <= hi:
            out.append({'line': ln, 'col': col, 'kw': kw, 'text': norm})
    return out
cur = [c for c in commands(CUR_FILE, CUR_TSV, THEORY) if c['kw'] != 'provenance']
orig = []
for f, th, lo, hi in SOURCES:
    orig += [c for c in commands(f, V2 + 'prov_orig.tsv', th, lo, hi) if c['kw'] != 'provenance']
A = [c['text'] for c in orig]; B = [c['text'] for c in cur]
sm = difflib.SequenceMatcher(None, A, B, autojunk=False)
lab = [None] * len(cur)
def toks(s): return re.findall(r'\\<[^>]+>|\w+|[^\w\s]', s)
def sim(a, b):
    s = difflib.SequenceMatcher(None, toks(a), toks(b), autojunk=False)
    return s.ratio()
by_kw = {}
for c in orig: by_kw.setdefault(c['kw'], []).append(c['text'])
for tag, i1, i2, j1, j2 in sm.get_opcodes():
    for j in range(j1, j2):
        if tag == 'equal':
            lab[j] = 'human'; continue
        t = B[j]
        if t in by_kw.get(cur[j]['kw'], []) and cur[j]['kw'] not in TRIVIAL and len(t) > 15:
            lab[j] = 'human'; continue   # moved verbatim (e.g. pref_suf)
        cands = []
        if tag == 'replace':
            ip = i1 + round((j - j1) * (i2 - i1) / max(1, j2 - j1))
            cands = A[max(i1, ip - 3):min(i2, ip + 4)]
        best = max([sim(t, a) for a in cands], default=0)
        if best < 0.5 and cur[j]['kw'] not in TRIVIAL and len(t) >= 25:
            pool = [a for a in by_kw.get(cur[j]['kw'], []) if abs(len(a) - len(t)) < 0.5 * max(len(a), len(t))]
            for a in pool:
                s = difflib.SequenceMatcher(None, toks(t), toks(a), autojunk=False)
                if s.real_quick_ratio() > best and s.quick_ratio() > best:
                    best = max(best, s.ratio())
        lab[j] = 'ai_human' if best >= 0.5 else 'ai'
OVR = json.loads(sys.argv[6]) if len(sys.argv) > 6 else []
for j, c in enumerate(cur):
    for pre in OVR:
        if c['text'].startswith(pre):
            lab[j] = 'ai_human'
# isolated equal trivial commands inside changed regions take the region's label
for j in range(len(cur)):
    if lab[j] == 'human' and cur[j]['kw'] in TRIVIAL:
        prev = next((lab[k] for k in range(j - 1, -1, -1) if cur[k]['kw'] not in TRIVIAL), 'human')
        nxt = next((lab[k] for k in range(j + 1, len(cur)) if cur[k]['kw'] not in TRIVIAL), 'human')
        if prev != 'human' and nxt != 'human' and prev == nxt:
            lab[j] = prev
TOP = {'lemma','theorem','corollary','definition','fun','function','abbreviation','text','section','subsection',
       'subsubsection','context','locale','lemmas','datatype','record','interpretation','named_theorems','declare',
       'end','partial_function','global_interpretation'}
in_created = False
for j, c in enumerate(cur):
    if c['kw'] in TOP:
        in_created = c['kw'] in ('lemma', 'theorem', 'corollary') and lab[j] == 'ai'
    elif in_created:
        lab[j] = 'ai'
json.dump([dict(c, label=l) for c, l in zip(cur, lab)], open(OUT, 'w'), indent=0)
from collections import Counter
print(THEORY, Counter(lab))
