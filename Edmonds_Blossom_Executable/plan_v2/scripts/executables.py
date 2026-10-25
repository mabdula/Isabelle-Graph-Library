import re
V1 = '/media/llms/Isabelle-Graph-Library-Blossom-Executable/Edmonds_Blossom_Executable/backups/v1_reuse_design_2026-10-24/'
OUT = '/home/llm/.claude/jobs/d07b4540/tmp/v2/EX/'
def rd(n): return open(V1 + n + '.thy').read()
def drop_plan_change_comments(t):
    # (* PLAN CHANGE ... *) comments of v1 coders: the v2 plan incorporates them as design
    t = re.sub(r'\(\* PLAN CHANGE.*?\*\)\n', '', t, flags=re.S)
    t = re.sub(r'[ ]*\\<comment> \\<open>PLAN CHANGE[^\n]*?\\<close>\n', '', t)
    return t
def cut(t, start, end):
    i = t.index(start); j = t.index(end, i)
    return t[:i] + t[j:]
def must(t, old, new, count=1):
    assert t.count(old) >= 1, old[:80]
    return t.replace(old, new) if count is None else t.replace(old, new, count)

# ---------------------------------------------------------------- Graph_Matching_Specs
gms = drop_plan_change_comments(rd('Graph_Matching_Specs'))
open(OUT + 'Graph_Matching_Specs.thy', 'w').write(gms)

# ---------------------------------------------------------------- Find_Max_Matching
t = drop_plan_change_comments(rd('Edmonds_Blossom_Top_Loop'))
t = must(t, 'theory Edmonds_Blossom_Top_Loop', 'theory Find_Max_Matching')
t = t.replace('Edmonds_Blossom_Loop', 'Find_Max_Matching')
t = t.replace('augmenting_path_search', 'aug_path_search')
open(OUT + 'Find_Max_Matching.thy', 'w').write(t)

# ---------------------------------------------------------------- Compute_Alt_Path
t = drop_plan_change_comments(rd('Alternating_Forest_Search'))
t = must(t, 'theory Alternating_Forest_Search\n  imports Graph_Matching_Specs Blossom.Blossom_Algo_Search',
         'theory Compute_Alt_Path\n  imports Graph_Matching_Specs Compute_Alt_Path_Invars')
t = cut(t, 'subsection \\<open>The abstract search, one state at a time\\<close>',
        'subsection \\<open>Edges of a forest given by parent pointers\\<close>')
t = t.replace('Alternating_Forest_Search', 'Compute_Alt_Path')
t = must(t, 'interpretation abs_search: compute_alt_path "ugraph_abs G" "matching_abs M" "\\<lambda>S. SOME x. x \\<in> S"',
         'interpretation abs_search: compute_alt_path "ugraph_abs G" "matching_abs M"')
open(OUT + 'Compute_Alt_Path.thy', 'w').write(t)

# ---------------------------------------------------------------- Find_Aug_Path
t = drop_plan_change_comments(rd('Blossom_Shrinking_Search'))
t = must(t, 'theory Blossom_Shrinking_Search\n  imports Graph_Matching_Specs Blossom.Blossom_Algo_Contraction',
         'theory Find_Aug_Path\n  imports Graph_Matching_Specs Graph_Quotient_Lifting Blossom_Prefixes')
t = cut(t, 'subsection \\<open>A choice function for the lifting\\<close>', 'subsection \\<open>Contracting an edge list\\<close>')
# lifting definitions: the functions of Graph_Quotient_Lifting
a = t.index('definition "cycle_neighbour E C v =')
b = t.index('fun lift_path where')
t = t[:a] + t[b:]
t = must(t, '| "lift_path ((E, N, C, u) # cs) p = lift_path cs (lift_one E N C u p)"',
         '| "lift_path ((E, N, C, u) # cs) p =\n     lift_path cs (refine (\\<lambda>v. isin (Graph.neighbourhood E v)) (mate_lookup N) u C p)"')
t = re.sub(r'lemmas \[code\] = contract_vertices_def contract_graph_def contract_matching_def cycle_neighbour_def\n.*?lift_path\.simps',
           'lemmas [code] = contract_vertices_def contract_graph_def contract_matching_def lift_path.simps', t, flags=re.S)
t = must(t, '''lemma quot_here: "quot (cycle_sel C) (ugraph_abs E) (Vs (ugraph_abs E) - set C) u"
  apply unfold_locales
  using choose.sel[OF cycle_sel_choose] contraction_facts(1,2,3,6)
  by (auto simp: neq_Nil_conv)

interpretation Q: quot "cycle_sel C" "ugraph_abs E" "Vs (ugraph_abs E) - set C" u''',
'''lemma quot_here: "quot (ugraph_abs E) (Vs (ugraph_abs E) - set C) u"
  apply unfold_locales
  using contraction_facts(1,2,3,6)
  by (auto simp: neq_Nil_conv)

interpretation Q: quot "ugraph_abs E" "Vs (ugraph_abs E) - set C" u''')
a = t.index('lemma cycle_neighbour_eq:')
b = t.index('lemma lift_one_correct:')
new_bridge = '''lemma quot_lift_here:
  "quot_lift (ugraph_abs E) (Vs (ugraph_abs E) - set C) u (\\<lambda>v. isin (Graph.neighbourhood E v))
     (mate_lookup N) (matching_abs N) C"
proof(intro quot_lift.intro quot_here quot_lift_axioms.intro)
  show "isin (Graph.neighbourhood E v) w \\<longleftrightarrow> {v, w} \\<in> ugraph_abs E" for v w
    by (simp add: isin_neighbourhood_iff in_ugraph_abs_iff[OF contraction(1)])
  show "mate_lookup N v = Some w \\<longleftrightarrow> {v, w} \\<in> matching_abs N" for v w
    by (simp add: matching_abs_iff[OF contraction_facts(7)])
  show "matching_abs N \\<subseteq> ugraph_abs E"
    by (rule contraction_facts(9))
  show "u \\<notin> Vs (ugraph_abs E)"
    by (rule contraction_facts(6))
  show "hd C = last C"
    by (rule contraction_facts(4))
qed simp

'''
t = t[:a] + new_bridge + t[b:]
t = must(t, '''lemma lift_one_correct:
  assumes "graph_augmenting_path (ugraph_abs (contract_graph E vs' C u))
             (matching_abs (contract_matching N vs' C u)) p"
  shows "graph_augmenting_path (ugraph_abs E) (matching_abs N) (lift_one E N C u p)"
proof-
  have "graph_augmenting_path (Q.quotG (ugraph_abs E)) (Q.quotG (matching_abs N)) p"
    using assms
    by (simp add: contract_graph_abs contract_matching_abs)
  hence "graph_augmenting_path (ugraph_abs E) (matching_abs N) (Q.refine C (matching_abs N) p)"
    by (rule Q.refine_works[OF contraction(3) _ contraction_facts(8,9) refl])
  thus ?thesis
    by (simp add: lift_one_eq)
qed''', '''lemma refine_correct:
  assumes "graph_augmenting_path (ugraph_abs (contract_graph E vs' C u))
             (matching_abs (contract_matching N vs' C u)) p"
  shows "graph_augmenting_path (ugraph_abs E) (matching_abs N)
           (refine (\\<lambda>v. isin (Graph.neighbourhood E v)) (mate_lookup N) u C p)"
proof-
  interpret L: quot_lift "ugraph_abs E" "Vs (ugraph_abs E) - set C" u
                 "\\<lambda>v. isin (Graph.neighbourhood E v)" "mate_lookup N" "matching_abs N" C
    by (rule quot_lift_here)
  have "graph_augmenting_path (Q.quotG (ugraph_abs E)) (Q.quotG (matching_abs N)) p"
    using assms
    by (simp add: contract_graph_abs contract_matching_abs)
  thus ?thesis
    by (rule L.refine_works[OF contraction(3) _ contraction_facts(8,9) refl])
qed''')
t = t.replace('lift_one_correct', 'refine_correct')
assert 'lift_one' not in t and 'cycle_sel' not in t, [l for l in t.split('\n') if 'lift_one' in l or 'cycle_sel' in l]
t = t.replace('Blossom_Shrinking_Search', 'Find_Aug_Path')
t = re.sub(r'\bblossom_search\b', 'blos_search', t)
t = re.sub(r'\bfresh_vertex\b', 'create_vert', t)
open(OUT + 'Find_Aug_Path.thy', 'w').write(t)

# ---------------------------------------------------------------- Find_Aug_Path_Subprocedures
t = drop_plan_change_comments(rd('Edmonds_Blossom_Subprocedures'))
t = must(t, 'theory Edmonds_Blossom_Subprocedures\n  imports Blossom_Shrinking_Search Blossom.Blossom_Algo_Compute_Aug_Path',
         'theory Find_Aug_Path_Subprocedures\n  imports Find_Aug_Path')
t = t.replace('Edmonds_Blossom_Subprocedures', 'Find_Aug_Path_subprocedures')
t = re.sub(r'\balternating_forest_search\b', 'compute_alt_path', t)
t = t.replace('blossom_search_path', 'compute_match_blossom_sound_path')
t = t.replace('blossom_search_blossom', 'compute_match_blossom_sound_blossom')
t = t.replace('blossom_search_complete', 'compute_match_blossom_complete')
t = t.replace('blossom_search_def', 'compute_match_blossom_def')
t = must(t, 'lemmas blossom_search = ', 'lemmas compute_match_blossom = ')
t = re.sub(r'\bblossom_search\b', 'compute_match_blossom', t)
open(OUT + 'Find_Aug_Path_Subprocedures.thy', 'w').write(t)
print('ok')

# ---------------------------------------------------------------- text fixes
def fix(name, old, new):
    p = OUT + name + '.thy'
    t = open(p).read()
    assert old in t, (name, old[:60])
    open(p, 'w').write(t.replace(old, new))
fix('Find_Aug_Path', '''  The correctness of lifting and contracting is that of the abstract algorithm
  @{const find_aug_path.find_aug_path}: the lifting function below is equal to
  @{const quot.refine} for a suitable choice function.\\<close>''',
'''  A path is lifted through one contraction by the function @{const refine} of the theory of
  graph quotients, whose correctness is @{thm [source] quot_lift.refine_works}.\\<close>''')
fix('Find_Aug_Path_Subprocedures', '''  longest disjoint prefixes form a blossom with the remainder of either path as its stem. This is
  the procedure @{const compute_match_blossom'.compute_match_blossom}, without its special case
  for an edge between two free vertices: the forest search returns such an edge itself.\\<close>''',
'''  longest disjoint prefixes form a blossom with the remainder of either path as its stem. In the
  original formalisation, the procedure has a special case for an edge between two free
  vertices; it is not needed here, as the forest search returns such an edge itself.\\<close>''')
fix('Compute_Alt_Path', '''  The correctness proof reuses the invariants of the abstract search
  @{const compute_alt_path.compute_alt_path}: every growth step of the executable search is a
  step of the abstract search.\\<close>''',
'''  The correctness proof uses the invariants of the abstract search, which are proved in the
  theory \\<open>Compute_Alt_Path_Invars\\<close>: every growth step of the search is one of the steps
  @{const compute_alt_path.if1} and @{const compute_alt_path.if2} that preserve them.\\<close>''')

# ---------------------------------------------------------------- Edmonds_Blossom_Example
t = drop_plan_change_comments(rd('Edmonds_Blossom_Example'))
t = must(t, '''theory Edmonds_Blossom_Example
  imports Edmonds_Blossom_Top_Loop Edmonds_Blossom_Subprocedures Alternating_Forest_Search
          Directed_Set_Graphs.Pair_Graph_RBT''', '''theory Edmonds_Blossom_Example
  imports Find_Max_Matching Find_Aug_Path_Subprocedures Compute_Alt_Path
          Directed_Set_Graphs.Pair_Graph_RBT''')
# the alternating forest search
t = must(t, '''global_interpretation alt_forest: Alternating_Forest_Search''', '''global_interpretation compute_alt_path: Compute_Alt_Path''')
t = must(t, '''  defines alt_forest_impl = alt_forest.Alternating_Forest_Search_impl
    and alt_forest_free_vertices = alt_forest.free_vertices
    and alt_forest_initial_labels = alt_forest.initial_labels
    and alt_forest_initial_state = alt_forest.initial_state
    and alt_forest_paths = alt_forest.alternating_paths
    and alt_forest_run_impl = alt_forest.Alternating_Forest_Search_run_impl
  by (intro Alternating_Forest_Search.intro gm.Graph_Matching_Specs_axioms Map_axioms_as_needed)''',
'''  defines compute_alt_path_impl = compute_alt_path.Compute_Alt_Path_impl
    and compute_alt_path_free_vertices = compute_alt_path.free_vertices
    and compute_alt_path_initial_labels = compute_alt_path.initial_labels
    and compute_alt_path_initial_state = compute_alt_path.initial_state
    and compute_alt_path_paths = compute_alt_path.alternating_paths
    and compute_alt_path_run_impl = compute_alt_path.Compute_Alt_Path_run_impl
  by (intro Compute_Alt_Path.intro gm.Graph_Matching_Specs_axioms Map_axioms_as_needed)''')
t = t.replace('alt_forest_run_impl', 'compute_alt_path_run_impl')
t = t.replace('alt_forest.Alternating_Forest_Search_run_impl_correct[unfolded alt_forest.Alternating_Forest_Search_axiom_def]',
              'compute_alt_path.Compute_Alt_Path_run_impl_correct[unfolded compute_alt_path.Compute_Alt_Path_axiom_def]')
# compute_match_blossom
t = must(t, '''global_interpretation subprocedures: Edmonds_Blossom_Subprocedures''',
         '''global_interpretation find_aug_path_subprocedures: Find_Aug_Path_subprocedures''')
t = must(t, '''    and alternating_forest_search = compute_alt_path_run_impl
  defines blossom_search_rbt = subprocedures.blossom_search
  by (intro Edmonds_Blossom_Subprocedures.intro gm.Graph_Matching_Specs_axioms
            Edmonds_Blossom_Subprocedures_axioms.intro,''',
'''    and compute_alt_path = compute_alt_path_run_impl
  defines compute_match_blossom_impl = find_aug_path_subprocedures.compute_match_blossom
  by (intro Find_Aug_Path_subprocedures.intro gm.Graph_Matching_Specs_axioms
            Find_Aug_Path_subprocedures_axioms.intro,''')
# Find_Aug_Path
t = must(t, '''subsection \\<open>Searching for an augmenting path by shrinking blossoms\\<close>

global_interpretation shrinking: Blossom_Shrinking_Search''', '''subsection \\<open>Searching for an augmenting path by shrinking blossoms\\<close>

global_interpretation find_aug_path: Find_Aug_Path''')
t = must(t, '''    and blossom_search = blossom_search_rbt and fresh_vertex = fresh_nat
  for G vs N
  defines shrinking_impl = shrinking.Blossom_Shrinking_Search_impl
    and shrinking_initial_state = shrinking.initial_state
    and shrinking_augmenting_path = shrinking.augmenting_path
    and shrinking_run_impl = shrinking.Blossom_Shrinking_Search_run_impl
    and contract_vertices_rbt = shrinking.contract_vertices
    and contract_graph_rbt = shrinking.contract_graph
    and contract_matching_rbt = shrinking.contract_matching
    and cycle_neighbour_rbt = shrinking.cycle_neighbour
    and last_edge_matched_rbt = shrinking.last_edge_matched
    and cycle_path_rbt = shrinking.cycle_path
    and matched_to_cycle_rbt = shrinking.matched_to_cycle
    and replace_cycle_rbt = shrinking.replace_cycle_impl
    and lift_one_rbt = shrinking.lift_one
    and lift_path_rbt = shrinking.lift_path
  by (intro Blossom_Shrinking_Search.intro gm.Graph_Matching_Specs_axioms
            Blossom_Shrinking_Search_axioms.intro,
      fold graph_input_rbt_def matching_invar_rbt_def ugraph_abs_rbt_def matching_abs_rbt_def,
      use subprocedures.blossom_search fresh_nat in \\<open>blast+\\<close>)''',
'''    and blos_search = compute_match_blossom_impl and create_vert = fresh_nat
  for G vs N
  defines find_aug_path_impl = find_aug_path.Find_Aug_Path_impl
    and find_aug_path_initial_state = find_aug_path.initial_state
    and find_aug_path_augmenting_path = find_aug_path.augmenting_path
    and find_aug_path_run_impl = find_aug_path.Find_Aug_Path_run_impl
    and contract_vertices_rbt = find_aug_path.contract_vertices
    and contract_graph_rbt = find_aug_path.contract_graph
    and contract_matching_rbt = find_aug_path.contract_matching
    and lift_path_rbt = find_aug_path.lift_path
  by (intro Find_Aug_Path.intro gm.Graph_Matching_Specs_axioms Find_Aug_Path_axioms.intro,
      fold graph_input_rbt_def matching_invar_rbt_def ugraph_abs_rbt_def matching_abs_rbt_def,
      use find_aug_path_subprocedures.compute_match_blossom fresh_nat in \\<open>blast+\\<close>)''')
t = t.replace('lemma shrinking_run_impl_correct:', 'lemma find_aug_path_run_impl_correct:')
t = t.replace('shrinking.Blossom_Shrinking_Search_run_impl_correct[unfolded shrinking.Blossom_Shrinking_Search_axiom_def,',
              'find_aug_path.Find_Aug_Path_run_impl_correct[unfolded find_aug_path.Find_Aug_Path_axiom_def,')
t = t.replace('shrinking_run_impl', 'find_aug_path_run_impl')
# Find_Max_Matching
t = must(t, 'global_interpretation edmonds_blossom: Edmonds_Blossom_Loop', 'global_interpretation find_max_matching: Find_Max_Matching')
t = t.replace('augmenting_path_search = ', 'aug_path_search = ')
t = must(t, '''  defines edmonds_blossom_impl = edmonds_blossom.Edmonds_Blossom_Loop_impl
    and edmonds_blossom_initial_state = edmonds_blossom.initial_state
    and edmonds_blossom_run_impl = edmonds_blossom.Edmonds_Blossom_Loop_run_impl
  by (intro Edmonds_Blossom_Loop.intro gm.Graph_Matching_Specs_axioms
            Edmonds_Blossom_Loop_axioms.intro,''', '''  defines find_max_matching_impl = find_max_matching.Find_Max_Matching_impl
    and find_max_matching_initial_state = find_max_matching.initial_state
    and find_max_matching_run_impl = find_max_matching.Find_Max_Matching_run_impl
  by (intro Find_Max_Matching.intro gm.Graph_Matching_Specs_axioms
            Find_Max_Matching_axioms.intro,''')
t = t.replace('interpretation edmonds_blossom_proofs: Edmonds_Blossom_Loop_thms', 'interpretation find_max_matching_proofs: Find_Max_Matching_thms')
t = t.replace('Edmonds_Blossom_Loop_thms', 'Find_Max_Matching_thms')
t = t.replace('edmonds_blossom.Edmonds_Blossom_Loop', 'find_max_matching.Find_Max_Matching')
t = t.replace('edmonds_blossom_proofs.Edmonds_Blossom_Loop', 'find_max_matching_proofs.Find_Max_Matching')
t = t.replace('Edmonds_Blossom_Loop', 'Find_Max_Matching')
t = t.replace('edmonds_blossom_impl', 'find_max_matching_impl').replace('edmonds_blossom_initial_state', 'find_max_matching_initial_state')
t = t.replace('edmonds_blossom_run_impl', 'find_max_matching_run_impl')
# code generation: no overrides any more
a = t.index('subsection \\<open>Code generation\\<close>')
b = t.index('subsection \\<open>Demonstration\\<close>')
t = t[:a] + '''subsection \\<open>Code generation\\<close>

text \\<open>The code equations of the later interpretations mention the constants of the data-structure
  layer in their unfolded form; the equations below rewrite them to the constants defined by the
  interpretation of the data-structure layer.\\<close>

lemmas [code_unfold] =
  augment_rbt_def[symmetric] adjacency_edges_rbt_def[symmetric] mate_from_list_rbt_def[symmetric]
  matching_edges_rbt_def[symmetric] neighbourhood_rbt_def[symmetric] from_list_rbt_def[symmetric]

''' + t[b:]
for bad in ['alt_forest', 'shrinking.', 'shrinking_', 'subprocedures.blossom', 'blossom_search', 'Edmonds_Blossom_Loop', 'edmonds_blossom.', 'lift_one', 'pref_suf_list', 'quot_nat']:
    assert bad not in t, (bad, [l for l in t.split('\n') if bad in l][:3])
open(OUT + 'Edmonds_Blossom_Example.thy', 'w').write(t)
print('example ok')
