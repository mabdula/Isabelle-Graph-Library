"""Desired labels for the five copied theories: human, except replacements of metis/smt/meson calls (ai);
ai_human labels set by the user are kept."""
import csv, pickle, re, json, collections, importlib.util
spec = importlib.util.spec_from_file_location('cl', '/home/llm/.claude/jobs/d07b4540/tmp/v2/relabel/locate.py'); cl = importlib.util.module_from_spec(spec); spec.loader.exec_module(cl)
V = '/home/llm/.claude/jobs/d07b4540/tmp/v7/'
TH = ['Blossom_Misc', 'Graph_Quotient', 'Graph_Quotient_Lifting', 'Blossom_Prefixes', 'Compute_Alt_Path_Invars']
P = pickle.load(open(V + 'proposals.pkl', 'rb'))
R = set()
for p in P:
    if p['cg'] is None: continue
    for (l, c) in p['ai']:
        if p['th'] == 'Blossom_Misc' and p['cg'] == 98 and l != 102: continue
        if p['th'] == 'Graph_Quotient_Lifting' and p['cg'] == 1876 and l not in (1881, 1882, 1886, 1887): continue
        R.add((p['th'], l, c))
ranges = []
for ln in open(V + 'manual.txt'):
    ln = ln.split('#')[0].split()
    if not ln: continue
    th, a, b, ov = ln[0], int(ln[1]), int(ln[2]), ln[3:]
    ranges.append((th, a, b, [o.split('=') for o in ov]))
rows = list(csv.DictReader(open(V + 'prov_cur.tsv'), delimiter='\t'))
def desired_for(t):
    cmds = [c for c in cl.commands(V + t + '.thy', rows, t) if c['kw'] != 'provenance']
    out = []
    for c in cmds:
        ai = (t, c['line'], c['col']) in R
        for th, a, b, ov in ranges:
            if th == t and a <= c['line'] <= b:
                hum = False
                for k, v in ov:
                    if '@' in k:
                        kk, ll = k.split('@')
                        if c['kw'] == kk and c['line'] == int(ll): hum = True
                    elif c['kw'] == k: hum = True
                ai = not hum if not ai else (not hum)
        if c['label'] == 'ai_human': d = 'ai_human'
        elif c['kw'] in ('theory', 'end') and c['label'] == 'unmarked': d = c['label']
        else: d = 'ai' if ai else 'human'
        out.append((c, d))
    return out
if __name__ == '__main__':
    tot = collections.Counter()
    for t in TH:
        D = desired_for(t)
        for c, d in D: tot[(c['label'], d)] += 1
        print(t, collections.Counter(d for _, d in D))
    print(tot)
