import re
ORIG = '/media/llms/Isabelle-Graph-Library-Blossom-Executable/Edmonds_Blossom_Algorithm/Graph_Quotient.thy'

def lines():
    return open(ORIG).read().split('\n')

def find_line(L, text, start=0):
    for i in range(start, len(L)):
        if L[i].startswith(text):
            return i
    raise ValueError(text)

def part_A(L):
    """lines 1..1069 (index 0..1068) with the header and the quot locale adapted."""
    A = L[:1069]
    t = '\n'.join(A)
    t = t.replace('imports choose "Basic_Matching.Berge"',
                  'imports Undirected_Set_Graphs.Pair_Graph_Berge_Adaptor Undirected_Set_Graphs.Undirected_Set_Graphs\n        "Basic_Matching.Berge"')
    # quot locale without the choice function
    i0 = t.index('locale pre_quot = choose sel +')
    i1 = t.index('lemma edge_in_quot_in_graph_1:')
    new_loc = '''locale quot = graph_abs E for E :: "'a set set" +
  fixes s::"'a set" and u::'a
  assumes good_quot_map: "u \\<notin> s" "s \\<subset> Vs E"
begin

abbreviation "P v \\<equiv> (if v \\<in> s then v else u)"

'''
    t = t[:i0] + new_loc + t[i1:]
    # path lemmas: drop rev_P
    j0 = t.index('lemma path_is_quot_path:\n  assumes path: "path (quotG E) p" "set p \\<subseteq> s"\n  shows "path E (map rev_P p)"')
    j1 = t.index('lemma vert_in_graph_iff_in_quot:')
    # keep edge_of_path_in_graph_iff_in_quot (between) but drop rev_map_map, quot_alt_path_iff_alt_path, path_is_quot_path'
    seg = t[j0:j1]
    k0 = seg.index('lemma edge_of_path_in_graph_iff_in_quot:')
    k1 = seg.index('lemma rev_map_map:')
    keep = seg[k0:k1]
    new_paths = '''lemma path_is_quot_path:
  assumes path: "path (quotG E) p" "set p \\<subseteq> s"
  shows "path E p"
  using assms
proof \\<^marker>\\<open>provenance ai\\<close> (induction)
  case path0
  then show ?case
    by simp
next
  case (path1 v)
  then show ?case
    using good_quot_map
    by auto
next
  case (path2 v v' vs)
  then show ?case
    using edge_in_quot_in_graph_1'
    by auto
qed

lemma path_is_quot_path':
  assumes path: "path (quotG E) p" "set p \\<subseteq> s"
  shows "path E p"
  using assms
  by \\<^marker>\\<open>provenance ai\\<close> (rule path_is_quot_path)

'''
    t = t[:j0] + new_paths + keep + t[j1:]
    return t

def part_C(L):
    return '\n'.join(L[3307:])

def extract_lemma(L, name):
    """Return the text of the top-level lemma `name` (from its 'lemma name' line up to the next
    top-level command or context end), and its line range (0-based, inclusive start, exclusive end)."""
    start = None
    for i, l in enumerate(L):
        if re.match(r'^(lemma|theorem|corollary)\s+' + re.escape(name) + r'\b', l):
            start = i
            break
    if start is None:
        raise ValueError(name)
    j = start + 1
    top = re.compile(r'^(lemma|theorem|corollary|definition|fun|function|abbreviation|context|end|text|subsection|subsubsection|section|locale|lemmas|interpretation|declare|named_theorems|\(\*)\b')
    while j < len(L) and not top.match(L[j]):
        j += 1
    return '\n'.join(L[start:j]).rstrip() + '\n', (start, j)

GENERAL_FROM_B = ['in_quot_graph_neq_u', 'Vs_quotG_subset_Vs_quot_graph', 'in_quotG_neq_u',
                  'neq_u_notin_quot_graph', 'neq_u_notin_quotG']

def general_from_B(L):
    out = ['context quot', 'begin', '']
    for n in GENERAL_FROM_B:
        txt, _ = extract_lemma(L, n)
        out.append(txt)
    out.append('end')
    out.append('')
    return '\n'.join(out)
