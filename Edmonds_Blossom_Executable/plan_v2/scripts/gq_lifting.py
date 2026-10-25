import sys, re
sys.path.insert(0, '/home/llm/.claude/jobs/d07b4540/tmp/v2/scripts')
from gq_common import *
L = lines()
B = L[1069:3307]          # original lines 1070..3307
TOP = re.compile(r'^(lemma|theorem|corollary|definition|fun|function|abbreviation|context|end|text|subsection|subsubsection|section|locale|lemmas|interpretation|declare|named_theorems|\(\*)\b')

def blocks(Ls):
    """split into top-level command blocks: list of (head_line, [lines])"""
    out = []; cur = []
    for l in Ls:
        if TOP.match(l) and cur:
            out.append(cur); cur = []
        cur.append(l)
    if cur: out.append(cur)
    return out

bl = blocks(B)
drop_heads = [r'^definition choose_con_vert\b', r'^definition stem2vert_path\b', r'^definition replace_cycle\b',
              r'^definition refine\b']
pref_heads = [r'^fun pref_suf\b', r'^lemma pref_suf_append_1\b', r'^lemma pref_suf_append_2\b', r'^lemma pref_suf_works\b']
moved = [r'^lemma ' + re.escape(n) + r'\b' for n in GENERAL_FROM_B]
kept, pref = [], []
dropped = []
for b in bl:
    h = b[0]
    if any(re.match(p, h) for p in drop_heads) or any(re.match(p, h) for p in moved):
        dropped.append(h); continue
    if any(re.match(p, h) for p in pref_heads):
        pref.append('\n'.join(b)); continue
    # a text block just before refine def ("text\<open>The function the refines...") is kept (harmless)
    kept.append('\n'.join(b))
t = '\n'.join(kept)
t = re.sub(r'^context quot\s*$', 'context quot_lift', t, flags=re.M)
t = re.sub(r'choose_con_vert \(set C\)\s*', 'choose_con_vert adj C ', t)
t = re.sub(r'stem2vert_path C\s+M\b', 'stem2vert_path adj mate C', t)
t = re.sub(r'replace_cycle C\s+M\b', 'replace_cycle adj mate C', t)
t = re.sub(r'(?<![\w.])refine C\s+M\b', 'refine adj mate u C', t)
t = re.sub(r'\bstem2vert_path_def\b', "stem2vert_path_def'", t)
t = re.sub(r'\breplace_cycle_def\b', "replace_cycle_def'", t)
for v in ['hd p2', 'last p1']:
    old = ("""  ultimately have "sel (set C \\<inter> neighbourhood E (%s)) \\<in> set C \\<inter> neighbourhood E (%s)"
    apply -
    apply(rule sel)
    using edges_are_Vs quot insert_absorb
    by auto
  hence "choose_con_vert adj C (%s) \\<in> (set C \\<inter> neighbourhood E (%s))"
    apply (subst choose_con_vert_def)
    by auto
  thus ?thesis
    by(fastforce simp: neighbourhood_def)""" % (v, v, v, v))
    new = ("""  ultimately have "\\<exists>x \\<in> set C. {%s, x} \\<in> E"
    by \\<^marker>\\<open>provenance ai\\<close> (auto simp: neighbourhood_def insert_commute)
  thus ?thesis
    using choose_con_vert_props
    by \\<^marker>\\<open>provenance ai\\<close> blast""" % v)
    assert old in t, v
    t = t.replace(old, new)
pre = open('/home/llm/.claude/jobs/d07b4540/tmp/v2/scripts/lifting_preamble.thy').read()
pre = pre.replace('@@PREF_SUF@@', '\n\n'.join(p.rstrip() for p in pref))
out = ('theory Graph_Quotient_Lifting\n  imports Graph_Quotient Blossom_Misc\nbegin\n\n' + pre + '\n' + t.rstrip() + '\n\nend\n')
open('/home/llm/.claude/jobs/d07b4540/tmp/v2/BXS/Graph_Quotient_Lifting.thy', 'w').write(out)
print('dropped:', dropped)
print('pref:', [p.split('\n')[0] for p in pref])
print('lines:', len(out.split('\n')))
