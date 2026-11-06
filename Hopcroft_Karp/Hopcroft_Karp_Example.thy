theory Hopcroft_Karp_Example
  imports Hopcroft_Karp_Subprocedures
begin

section \<open>The Executable Hopcroft-Karp Algorithm\<close>

subsection \<open>Code equations for the graph operations\<close>

text \<open>The interpretations G and idfs.Graph are plain interpretations, so their constants are
  partially applied instances of locale constants, which cannot be code equations. Each is
  replaced, at code-generation time, by a global constant with its own code equations.\<close>

definition "nb_rbt G v = (case lookup G v of None \<Rightarrow> Leaf | Some N \<Rightarrow> N)"

lemma G_nb_code_unfold[code_unfold]: "G.neighbourhood = nb_rbt"
  by (intro ext) (simp add: G.neighbourhood_def nb_rbt_def)

definition "add_edge_rbt G u v =
  (case lookup G u of None \<Rightarrow> update u (insert_rbt v Leaf) G | Some N \<Rightarrow> update u (insert_rbt v N) G)"

definition "from_list_rbt xs = foldl (\<lambda>G (u, v). add_edge_rbt G u v) Leaf xs"

lemma G_add_edge_code_unfold[code_unfold]: "G.add_edge = add_edge_rbt"
  by (intro ext) (simp add: G.add_edge_def add_edge_rbt_def split: option.splits)

lemma G_from_list_code_unfold[code_unfold]: "G.from_list = from_list_rbt"
  unfolding G.from_list_def[abs_def] from_list_rbt_def[abs_def] G_add_edge_code_unfold
  by (simp add: RBT_Set.empty_def)

definition "add_edge_idfs G u v =
  (case lookup G u of None \<Rightarrow> update u (vset_insert v vset_empty) G
   | Some N \<Rightarrow> update u (vset_insert v N) G)"

definition "from_list_idfs xs = foldl (\<lambda>G (u, v). add_edge_idfs G u v) map_empty xs"

lemma idfs_add_edge_code_unfold[code_unfold]: "idfs.Graph.add_edge = add_edge_idfs"
  by (intro ext) (simp add: idfs.Graph.add_edge_def add_edge_idfs_def split: option.splits)

lemma idfs_from_list_code_unfold[code_unfold]: "idfs.Graph.from_list = from_list_idfs"
  unfolding idfs.Graph.from_list_def[abs_def] from_list_idfs_def[abs_def] idfs_add_edge_code_unfold
  by (rule refl)

subsection \<open>The algorithm\<close>

global_interpretation hopcroft_karp: Hopcroft_Karp_Loop
  where insert = insert_rbt and isin = isin and t_set = Tree2.set_tree and sel = sel
    and vset_empty = Leaf and vset_delete = RBT.delete and vset_inv = vset_inv
    and lookup = lookup and adjmap_inv = M.invar
    and G = G and vertex_list = vertex_list
    and empty_matching = Leaf and augment = mate_augment
    and matching_invar = "mate_invar nil (ugraph_abs_rbt G)" and matching_abstract = "mate_matching nil"
    and phase = "hopcroft_karp_phase nil (adjacency_edges G vertex_list) vertex_list"
  for nil G vertex_list
  defines hopcroft_karp_impl = hopcroft_karp.Hopcroft_Karp_Loop_impl
    and hopcroft_karp_initial_state = hopcroft_karp.initial_state
    and hopcroft_karp_run_impl = hopcroft_karp.Hopcroft_Karp_Loop_run_impl
  by unfold_locales

subsection \<open>Correctness of the executable algorithm\<close>

context
  fixes nil :: "'v::linorder" and G :: "(('v \<times> ('v \<times> color) tree) \<times> color) tree" and vertex_list
  assumes "hopcroft_karp_axiom_rbt G vertex_list" and nil_fresh: "nil \<notin> Vs (ugraph_abs_rbt G)"
begin

interpretation hopcroft_karp_proofs: Hopcroft_Karp_Loop_thms
  where insert = insert_rbt and isin = isin and t_set = Tree2.set_tree and sel = sel
    and vset_empty = Leaf and vset_delete = RBT.delete and vset_inv = vset_inv
    and lookup = lookup and adjmap_inv = M.invar
    and G = G and vertex_list = vertex_list
    and empty_matching = Leaf and augment = mate_augment
    and matching_invar = "mate_invar nil (ugraph_abs_rbt G)" and matching_abstract = "mate_matching nil"
    and phase = "hopcroft_karp_phase nil (adjacency_edges G vertex_list) vertex_list"
  apply unfold_locales
  unfolding ugraph_abs_rbt_def[symmetric] hopcroft_karp_axiom_rbt_def[symmetric]
  by (assumption | rule Hopcroft_Karp_Subprocedures.matching Hopcroft_Karp_Subprocedures.augment
                        phase nil_fresh \<open>hopcroft_karp_axiom_rbt G vertex_list\<close>)+

lemmas hopcroft_karp_correct_1 =
  hopcroft_karp_proofs.Hopcroft_Karp_Loop_correct_1[
    folded hopcroft_karp_proofs.Hopcroft_Karp_Loop_impl_to_Hopcroft_Karp_Loop,
    folded hopcroft_karp_impl_def hopcroft_karp_initial_state_def,
    folded hopcroft_karp.Hopcroft_Karp_Loop_run_impl_def, folded ugraph_abs_rbt_def]

lemmas hopcroft_karp_correct_2 =
  hopcroft_karp_proofs.Hopcroft_Karp_Loop_correct_2[
    folded hopcroft_karp_proofs.Hopcroft_Karp_Loop_impl_to_Hopcroft_Karp_Loop,
    folded hopcroft_karp_impl_def hopcroft_karp_initial_state_def,
    folded hopcroft_karp.Hopcroft_Karp_Loop_run_impl_def, folded ugraph_abs_rbt_def]

end

subsection \<open>Demonstration\<close>

definition "demo_edges =
  [(0::nat, 3::nat), (3, 0), (0, 4), (4, 0), (1, 3), (3, 1), (1, 5), (5, 1), (2, 4), (4, 2)]"
definition "demo_G = G.from_list demo_edges"
definition "demo_vs = [0, 1, 2, 3, 4, 5::nat]"

value "adjacency_edges demo_G demo_vs"
value "hopcroft_karp_phase 6 (adjacency_edges demo_G demo_vs) demo_vs Leaf"
value "Tree2.inorder (current_matching (hopcroft_karp_run_impl 6 demo_G demo_vs))"

lemma demo_abs: "G.digraph_abs demo_G = set demo_edges"
  by (simp add: demo_G_def)

lemma demo_bipartite: "bipartite (ugraph_abs_rbt demo_G) {0, 1, 2} {3, 4, 5}"
  by (auto simp: bipartite_def hopcroft_karp_input_rbt.ugraph_abs_def demo_abs demo_edges_def
                 insert_commute)

lemma demo_axiom: "hopcroft_karp_axiom_rbt demo_G demo_vs"
proof-
  have "G.graph_inv demo_G" "G.finite_graph demo_G" "G.finite_vsets demo_G"
    by (simp_all add: demo_G_def G.from_list_correct(2,3,5))
  thus ?thesis
    using demo_bipartite
    unfolding hopcroft_karp_input_rbt.Hopcroft_Karp_axiom_def
    by (auto simp: demo_abs demo_vs_def demo_edges_def dVs_eq)
qed

lemma demo_max:
  "max_card_matching (ugraph_abs_rbt demo_G)
     (mate_matching 6 (current_matching (hopcroft_karp_run_impl 6 demo_G demo_vs)))"
  by (rule hopcroft_karp_correct_1[OF demo_axiom])
     (auto simp: hopcroft_karp_input_rbt.ugraph_abs_def demo_abs demo_edges_def Vs_def)

export_code hopcroft_karp_run_impl in SML module_name Hopcroft_Karp

end
