import re
ORIG = '/media/llms/Isabelle-Graph-Library-Blossom-Executable/Edmonds_Blossom_Algorithm/'
S = open(ORIG + 'Blossom_Algo_Search.thy').read().split('\n')
CTR = open(ORIG + 'Blossom_Algo_Contraction.thy').read().split('\n')
CAP = open(ORIG + 'Blossom_Algo_Compute_Aug_Path.thy').read().split('\n')
V1 = open('/media/llms/Isabelle-Graph-Library-Blossom-Executable/Edmonds_Blossom_Executable/backups/v1_reuse_design_2026-10-24/Alternating_Forest_Search.thy').read()
TOP = re.compile(r'^(lemma|theorem|corollary|definition|fun|function|abbreviation|context|end|text|subsection|subsubsection|section|locale|lemmas|interpretation|declare|named_theorems|datatype|find_theorems|\(\*)\b')

def blocks(Ls):
    out = []; cur = []
    for l in Ls:
        if TOP.match(l) and cur:
            out.append(cur); cur = []
        cur.append(l)
    if cur: out.append(cur)
    return out

# body of the search theory: after "provenance human" up to the last "end" (theory end)
i0 = S.index('provenance human') + 1
body = S[i0:]
# cut the theory 'end' at the very end
while body and body[-1].strip() in ('', 'end'):
    body.pop()
# 2314.. : find compute_alt_path_from_tree_2' block boundaries (1-based lines in S)
def idx(prefix, start=0):
    for k in range(start, len(S)):
        if S[k].startswith(prefix):
            return k
    raise ValueError(prefix)
k_t2p = idx("lemma compute_alt_path_from_tree_2':")
k_t2 = idx("lemma compute_alt_path_from_tree_2:")
k_case = idx("      case noL1: False", k_t2p)
k_ult = None
for k in range(k_t2 - 1, k_t2p, -1):
    if S[k].strip() == 'by metis' and S[k-1].strip() == 'ultimately show ?thesis':
        k_ult = k; break
assert k_ult
base = S[k_case + 4:k_ult + 2]   # skip "case noL1", "then have if2_nholds ...", "using 2", "by(auto ...)"
assert S[k_case + 1].strip().startswith('then have if2_nholds')
assert S[k_case + 3].strip().startswith('by(auto simp add: compute_alt_path.psimps')
base_t = '\n'.join(base)
base_t = re.sub(r'"2\.prems"\(([1-7])\)', r'invars(\1)', base_t)
base_t = base_t.replace('"2.prems"(9)', 'init(1)').replace('"2.prems"(10)', 'init(2)')
assert '"2.prems"' not in base_t and not re.search(r'(?<![\w.])2\(\d', base_t), 'unmapped references'
# tail after the induction: from the line after the 3 qed's that close the induction
k_tail = None
for k in range(k_ult + 1, k_t2):
    if S[k].startswith('  then have "card M\' \\<le> card M"'):
        k_tail = k; break
assert k_tail
tail = S[k_tail:k_t2]
while tail and tail[-1].strip() == '':
    tail.pop()
assert tail[-1].strip() == 'qed'
new_t2p = '''lemma compute_alt_path_from_tree_2':
  assumes invars: 
    "flabel_invar flabel"
    "examined_have_odd_verts_invar ex flabel"
    "unexamined_matched_unlabelled_invar ex flabel"
    "finite_odds_invar flabel"
    "odd_labelled_verts_num_invar ex flabel"
    "ulabelled_verts_matched_invar ex flabel"
    "odd_then_matched_examined_invar ex flabel" and
    noL1: "\\<not> if1_cond flabel ex" and
    if2_nholds: "\\<not> if2_cond flabel" and
    init:       
    "finite ex" "ex \\<subseteq> G"
  shows "\\<nexists>p. matching_augmenting_path M p \\<and> path G p \\<and> distinct p"
proof-
  have "\\<exists>OSC. odd_set_cover OSC G \\<and> capacity2 OSC = card M"
  proof-
''' + base_t + '''
  qed
''' + '\n'.join(tail) + '\n'
# assemble kept blocks
bl = blocks(body)
drop = [r"^find_theorems", r"^function \(domintros\) compute_alt_path",
        r"^lemma if1_cond_props'''", r"^lemma if2_cond_props'''",
        r"^lemma compute_alt_path_if1\b", r"^lemma compute_alt_path_pinduct_2", r'^definition "compute_alt_path_meas',
        r"^lemma compute_alt_path_dom\b", r"^lemma compute_alt_path_dom_if1\b",
        r"^lemma compute_alt_path_from_tree_1\b", r"^lemma compute_alt_path_from_tree_2:",
        r"^lemma compute_alt_path_from_tree_sound", r"^lemma compute_alt_path_from_tree_complete",
        r"^locale compute_alt_path_use", r"^abbreviation \"flabel\b", r"^abbreviation \"ex\b", r"^abbreviation \"par\b",
        r"^interpretation compute_match_blossom'_use", r"^lemmas find_max_matching_works"]
out = []; dropped = []
skip_use_locale = False
for b in bl:
    h = b[0]; txt = '\n'.join(b)
    if h.startswith('locale compute_alt_path_use'):
        skip_use_locale = True
    if skip_use_locale:
        dropped.append(h); continue
    if h.startswith("lemma compute_alt_path_from_tree_2':"):
        out.append(new_t2p); continue
    if any(re.match(p, h) for p in drop):
        dropped.append(h); continue
    if h.startswith('definition') and (re.match(r'^definition\s*$', h) and len(b) > 1 and re.match(r'\s*"sel_if[12]', b[1])):
        dropped.append(h + ' ' + b[1].strip()[:20]); continue
    if h.startswith('lemma assumes') and 'compute_alt_path_dom' in txt:
        dropped.append(h + ' (anonymous, about the function)'); continue
    if h.startswith("lemma compute_alt_path_from_tree_2':"):
        out.append(new_t2p); continue
    out.append(txt)
t = '\n'.join(out)
t = t.replace('locale compute_alt_path = match G M + choose sel \n\nfor G M::"\'a set set" and sel::"\'a set \\<Rightarrow> \'a"',
              'locale compute_alt_path = match G M\n\nfor G M::"\'a set set"')
assert 'choose sel' not in t, 'locale header not replaced'
# copied pieces from other human theories
m0 = next(k for k, l in enumerate(CTR) if l.startswith('locale match = graph_abs G for G+'))
match_loc = '\n'.join(CTR[m0:m0 + 4]) + '\n'
c0 = next(k for k, l in enumerate(CAP) if l.startswith('definition compute_alt_path_spec where'))
c1 = next(k for k, l in enumerate(CAP) if l.startswith('locale compute_match_blossom\''))
spec = '\n'.join(CAP[c0:c1]).rstrip() + '\n'
# ai section from v1 (green), adapted: search_invars_complete without the abstract function
a0 = V1.index('subsection \\<open>The abstract search, one state at a time\\<close>')
a1 = V1.index('subsection \\<open>Edges of a forest given by parent pointers\\<close>')
ai = V1[a0:a1]
old_c = ai[ai.index('lemma search_invars_complete:'):]
old_c = old_c[:old_c.index('\nqed') + 4]
new_c = '''lemma search_invars_complete:
  assumes invars: "search_invars ex par flabel"
      and no_if1: "\\<not> if1_cond flabel ex" and no_if2: "\\<not> if2_cond flabel"
  shows "\\<nexists>p. matching_augmenting_path M p \\<and> path G p \\<and> distinct p"
proof-
  note I = search_invarsD[OF invars]
  show ?thesis
    by (rule compute_alt_path_from_tree_2'[OF I(4,12,13,14,15,16,17) no_if1 no_if2 I(18,19)])
qed'''
ai = ai.replace(old_c, new_c)
ai = ai.replace("text \\<open>If no growth step applies and no edge joins two even vertices, there is no augmenting\n  path. This is the theorem @{thm [source] compute_alt_path_from_tree_2'}, applied at a state at\n  which the abstract search returns immediately.\\<close>",
                "text \\<open>If no growth step applies and no edge joins two even vertices, there is no augmenting\n  path (@{thm [source] compute_alt_path_from_tree_2'}).\\<close>")

ai = ai.replace("text \\<open>A growth step preserves the invariants. The individual steps are those of the proofs\n  of @{thm [source] compute_alt_path_from_tree_1} and @{thm [source] compute_alt_path_from_tree_2'}.\\<close>",
                "text \\<open>A growth step preserves the invariants. The individual steps are those of the induction\n  steps of the soundness and the completeness proofs of the abstract search.\\<close>")
ai = ai.replace("text \\<open>An edge between two even vertices yields two paths with the properties required by\n  @{const compute_alt_path_spec}. The argument is the returning case of the proof of\n  @{thm [source] compute_alt_path_from_tree_1}.\\<close>",
                "text \\<open>An edge between two even vertices yields two paths with the properties required by\n  @{const compute_alt_path_spec}. The argument is the returning case of the soundness proof of\n  the abstract search.\\<close>")
assert 'compute_alt_path_from_tree_1' not in ai
hdr = '''theory Compute_Alt_Path_Invars
  imports Graph_Algorithms_Dev.Parent_Map Blossom_Prefixes
begin

provenance human

'''
res = (hdr + t.rstrip() + '\n\nprovenance ai\n\n' + ai.rstrip() + '\n\nend\n')
open('/home/llm/.claude/jobs/d07b4540/tmp/v2/BXS/Compute_Alt_Path_Invars.thy', 'w').write(res)
print('dropped:'); [print('  ', d) for d in dropped]
print('lines:', len(res.split('\n')))
