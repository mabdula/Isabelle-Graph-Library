theory Edmonds_Blossom_Example
  imports Find_Max_Matching Find_Aug_Path_Subprocedures Compute_Alt_Path
          Directed_Set_Graphs.Pair_Graph_RBT
begin

provenance ai

section \<open>The executable blossom algorithm on red-black trees\<close>

text \<open>Graphs, mate functions, parent maps and label maps are red-black trees. Vertices are
  natural numbers; a fresh vertex is one more than the largest vertex of a list.\<close>

subsection \<open>Fresh vertices and vertex lists\<close>

definition \<^marker>\<open>provenance ai_human\<close> "fresh_nat (vs :: nat list) = Suc (foldr max vs 0)"

lemma foldr_max_ge: "x \<in> set vs \<Longrightarrow> x \<le> foldr max vs (a :: nat)"
  by (induction vs) auto

lemma fresh_nat: "fresh_nat vs \<notin> set vs"
  using foldr_max_ge[of _ vs 0]
  by (fastforce simp: fresh_nat_def)

lemma vset_to_list_rbt: "vset_inv N \<Longrightarrow> set (Tree2.inorder N) = Tree2.set_tree N"
  by simp

subsection \<open>The data structures\<close>

global_interpretation gm: Graph_Matching_Specs
  where empty = map_empty and delete = RBT_Map.delete and lookup = lookup and insert = vset_insert
    and isin = isin and t_set = t_set and sel = sel and update = update and adjmap_inv = adj_inv
    and vset_empty = vset_empty and vset_delete = vset_delete and vset_inv = vset_inv
    and mate_empty = Leaf and mate_update = update and mate_delete = RBT_Map.delete
    and mate_lookup = lookup and mate_invar = M.invar
    and vset_to_list = Tree2.inorder
  defines ugraph_abs_rbt = gm.ugraph_abs
    and graph_input_rbt = gm.graph_input
    and matching_invar_rbt = gm.matching_invar
    and matching_abs_rbt = gm.Mate.\<M>
    and augment_rbt = gm.Mate.augment_impl
    and neighbourhood_rbt = gm.Graph.neighbourhood
    and add_edge_rbt = gm.Graph.add_edge
    and from_list_rbt = gm.Graph.from_list
    and neighbour_list_rbt = gm.neighbour_list
    and adjacency_edges_rbt = gm.adjacency_edges
    and matching_edges_rbt = gm.matching_edges
    and mate_from_list_rbt = gm.mate_from_list
proof(rule Graph_Matching_Specs.intro)
  show "Pair_Graph_Specs map_empty RBT_Map.delete lookup vset_insert isin t_set sel update adj_inv
          vset_empty vset_delete vset_inv"
    using G.Pair_Graph_Specs_axioms
    by (simp add: RBT_Set.empty_def adj_inv_def map_empty_def)
  show "Map Leaf update RBT_Map.delete lookup M.invar"
    using Map_axioms_as_needed
    by (simp add: RBT_Set.empty_def)
  thus "matching_augmentation Leaf update RBT_Map.delete lookup M.invar"
    by (simp add: matching_augmentation_def Matching_Augmentation_Specs_def)
  show "Graph_Matching_Specs_axioms t_set vset_inv Tree2.inorder"
    by (rule Graph_Matching_Specs_axioms.intro) simp
qed

subsection \<open>The alternating forest search\<close>

global_interpretation compute_alt_path: Compute_Alt_Path
  where empty = map_empty and delete = RBT_Map.delete and lookup = lookup and insert = vset_insert
    and isin = isin and t_set = t_set and sel = sel and update = update and adjmap_inv = adj_inv
    and vset_empty = vset_empty and vset_delete = vset_delete and vset_inv = vset_inv
    and mate_empty = Leaf and mate_update = update and mate_delete = RBT_Map.delete
    and mate_lookup = lookup and mate_invar = M.invar and vset_to_list = Tree2.inorder
    and parent_empty = Leaf and parent_update = update and parent_delete = RBT_Map.delete
    and parent_lookup = lookup and parent_invar = M.invar
    and label_empty = Leaf and label_update = update and label_delete = RBT_Map.delete
    and label_lookup = lookup and label_invar = M.invar
    and G = G and vs = vs and M = N
  for G vs N
  defines compute_alt_path_impl = compute_alt_path.Compute_Alt_Path_impl
    and compute_alt_path_free_vertices = compute_alt_path.free_vertices
    and compute_alt_path_initial_labels = compute_alt_path.initial_labels
    and compute_alt_path_initial_state = compute_alt_path.initial_state
    and compute_alt_path_paths = compute_alt_path.alternating_paths
    and compute_alt_path_run_impl = compute_alt_path.Compute_Alt_Path_run_impl
  by (intro Compute_Alt_Path.intro gm.Graph_Matching_Specs_axioms Map_axioms_as_needed)

lemma compute_alt_path_run_impl_correct:
  "\<lbrakk>graph_input_rbt G vs; matching_invar_rbt G N\<rbrakk>
   \<Longrightarrow> compute_alt_path_spec (ugraph_abs_rbt G) (matching_abs_rbt N) (compute_alt_path_run_impl G vs N)"
  "\<lbrakk>graph_input_rbt G vs; matching_invar_rbt G N;
    \<exists>p. graph_augmenting_path (ugraph_abs_rbt G) (matching_abs_rbt N) p\<rbrakk>
   \<Longrightarrow> compute_alt_path_run_impl G vs N \<noteq> None"
  using compute_alt_path.Compute_Alt_Path_run_impl_correct[unfolded compute_alt_path.Compute_Alt_Path_axiom_def]
  by blast+

subsection \<open>Finding an augmenting path or a blossom\<close>

global_interpretation find_aug_path_subprocedures: Find_Aug_Path_subprocedures
  where empty = map_empty and delete = RBT_Map.delete and lookup = lookup and insert = vset_insert
    and isin = isin and t_set = t_set and sel = sel and update = update and adjmap_inv = adj_inv
    and vset_empty = vset_empty and vset_delete = vset_delete and vset_inv = vset_inv
    and mate_empty = Leaf and mate_update = update and mate_delete = RBT_Map.delete
    and mate_lookup = lookup and mate_invar = M.invar and vset_to_list = Tree2.inorder
    and compute_alt_path = compute_alt_path_run_impl
  defines compute_match_blossom_impl = find_aug_path_subprocedures.compute_match_blossom
  by (intro Find_Aug_Path_subprocedures.intro gm.Graph_Matching_Specs_axioms
            Find_Aug_Path_subprocedures_axioms.intro,
      fold graph_input_rbt_def matching_invar_rbt_def ugraph_abs_rbt_def matching_abs_rbt_def,
      use compute_alt_path_run_impl_correct in \<open>blast+\<close>)

subsection \<open>Searching for an augmenting path by shrinking blossoms\<close>

global_interpretation find_aug_path: Find_Aug_Path
  where empty = map_empty and delete = RBT_Map.delete and lookup = lookup and insert = vset_insert
    and isin = isin and t_set = t_set and sel = sel and update = update and adjmap_inv = adj_inv
    and vset_empty = vset_empty and vset_delete = vset_delete and vset_inv = vset_inv
    and mate_empty = Leaf and mate_update = update and mate_delete = RBT_Map.delete
    and mate_lookup = lookup and mate_invar = M.invar and vset_to_list = Tree2.inorder
    and G = G and vs = vs and M = N
    and blos_search = compute_match_blossom_impl and create_vert = fresh_nat
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
      use find_aug_path_subprocedures.compute_match_blossom fresh_nat in \<open>blast+\<close>)

lemma find_aug_path_run_impl_correct:
  "\<lbrakk>graph_input_rbt G vs; matching_invar_rbt G N; find_aug_path_run_impl G vs N = Some p\<rbrakk>
   \<Longrightarrow> graph_augmenting_path (ugraph_abs_rbt G) (matching_abs_rbt N) p"
  "\<lbrakk>graph_input_rbt G vs; matching_invar_rbt G N;
    \<exists>p. graph_augmenting_path (ugraph_abs_rbt G) (matching_abs_rbt N) p\<rbrakk>
   \<Longrightarrow> find_aug_path_run_impl G vs N \<noteq> None"
  using find_aug_path.Find_Aug_Path_run_impl_correct[unfolded find_aug_path.Find_Aug_Path_axiom_def,
          folded graph_input_rbt_def matching_invar_rbt_def ugraph_abs_rbt_def matching_abs_rbt_def]
  by blast+

subsection \<open>The algorithm\<close>

global_interpretation find_max_matching: Find_Max_Matching
  where empty = map_empty and delete = RBT_Map.delete and lookup = lookup and insert = vset_insert
    and isin = isin and t_set = t_set and sel = sel and update = update and adjmap_inv = adj_inv
    and vset_empty = vset_empty and vset_delete = vset_delete and vset_inv = vset_inv
    and mate_empty = Leaf and mate_update = update and mate_delete = RBT_Map.delete
    and mate_lookup = lookup and mate_invar = M.invar and vset_to_list = Tree2.inorder
    and G = G and vs = vs and aug_path_search = "find_aug_path_run_impl G vs"
  for G vs
  defines find_max_matching_impl = find_max_matching.Find_Max_Matching_impl
    and find_max_matching_initial_state = find_max_matching.initial_state
    and find_max_matching_run_impl = find_max_matching.Find_Max_Matching_run_impl
  by (intro Find_Max_Matching.intro gm.Graph_Matching_Specs_axioms
            Find_Max_Matching_axioms.intro,
      fold graph_input_rbt_def matching_invar_rbt_def ugraph_abs_rbt_def matching_abs_rbt_def,
      use find_aug_path_run_impl_correct in \<open>blast+\<close>)

subsection \<open>Correctness of the executable algorithm\<close>

context
  fixes G :: "((nat \<times> (nat \<times> color) tree) \<times> color) tree" and vs :: "nat list"
  assumes graph_input: "graph_input_rbt G vs"
begin

interpretation find_max_matching_proofs: Find_Max_Matching_thms
  where empty = map_empty and delete = RBT_Map.delete and lookup = lookup and insert = vset_insert
    and isin = isin and t_set = t_set and sel = sel and update = update and adjmap_inv = adj_inv
    and vset_empty = vset_empty and vset_delete = vset_delete and vset_inv = vset_inv
    and mate_empty = Leaf and mate_update = update and mate_delete = RBT_Map.delete
    and mate_lookup = lookup and mate_invar = M.invar and vset_to_list = Tree2.inorder
    and G = G and vs = vs and aug_path_search = "find_aug_path_run_impl G vs"
  by (intro Find_Max_Matching_thms.intro find_max_matching.Find_Max_Matching_axioms
            Find_Max_Matching_thms_axioms.intro)
     (simp add: find_max_matching.Find_Max_Matching_axiom_def graph_input[unfolded graph_input_rbt_def])

lemmas edmonds_blossom_correct_1 =
  find_max_matching_proofs.Find_Max_Matching_correct_1[
    folded find_max_matching_proofs.Find_Max_Matching_impl_to_Find_Max_Matching,
    folded find_max_matching_impl_def find_max_matching_initial_state_def,
    folded find_max_matching.Find_Max_Matching_run_impl_def,
    folded graph_input_rbt_def matching_invar_rbt_def ugraph_abs_rbt_def matching_abs_rbt_def]

lemmas edmonds_blossom_correct_2 =
  find_max_matching_proofs.Find_Max_Matching_correct_2[
    folded find_max_matching_proofs.Find_Max_Matching_impl_to_Find_Max_Matching,
    folded find_max_matching_impl_def find_max_matching_initial_state_def,
    folded find_max_matching.Find_Max_Matching_run_impl_def,
    folded graph_input_rbt_def matching_invar_rbt_def ugraph_abs_rbt_def matching_abs_rbt_def]

end

subsection \<open>Code generation\<close>

text \<open>The code equations of the later interpretations mention the constants of the data-structure
  layer in their unfolded form; the equations below rewrite them to the constants defined by the
  interpretation of the data-structure layer.\<close>

lemmas [code_unfold] =
  augment_rbt_def[symmetric] adjacency_edges_rbt_def[symmetric] mate_from_list_rbt_def[symmetric]
  matching_edges_rbt_def[symmetric] neighbourhood_rbt_def[symmetric] from_list_rbt_def[symmetric]

subsection \<open>Demonstration\<close>

text \<open>Two triangles joined by an edge. A maximum matching has three edges; finding it requires
  shrinking a triangle.\<close>

definition "demo_edges =
  [(0::nat, 1::nat), (1, 0), (1, 2), (2, 1), (2, 0), (0, 2), (2, 3), (3, 2),
   (3, 4), (4, 3), (4, 5), (5, 4), (5, 3), (3, 5)]"

definition "demo_G = from_list_rbt demo_edges"

definition "demo_vs = [0, 1, 2, 3, 4, 5::nat]"

value "Tree2.inorder (current_matching (find_max_matching_run_impl demo_G demo_vs))"

lemma demo_input: "graph_input_rbt demo_G demo_vs"
  unfolding demo_G_def
  by (rule gm.from_list_graph_input) (auto simp: demo_edges_def demo_vs_def dVs_eq)

lemma demo_max:
  "max_card_matching (ugraph_abs_rbt demo_G)
     (matching_abs_rbt (current_matching (find_max_matching_run_impl demo_G demo_vs)))"
  by (rule edmonds_blossom_correct_1[OF demo_input])

export_code find_max_matching_run_impl in SML module_name Edmonds_Blossom

end
