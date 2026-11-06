theory Edmonds_Blossom_Example
  imports Find_Max_Matching Find_Aug_Path Find_Aug_Path_Subprocedures Compute_Alt_Path
          Directed_Set_Graphs.Pair_Graph_RBT Basic_Matching.Alternating_Forest_Executable
begin

provenance ai_human

section \<open>The executable blossom algorithm on red-black trees\<close>

text \<open>Graphs, matchings and the encapsulated alternating forest use red-black trees.
  Vertices are natural numbers. A sentinel outside the input is kept fixed throughout a run;
  contraction chooses fresh vertices distinct from that sentinel.\<close>

subsection \<open>Fresh vertices and vertex lists\<close>

definition \<^marker>\<open>provenance ai_human\<close> "fresh_nat (vs :: nat list) = Suc (foldr max vs 0)"

lemma foldr_max_ge: "x \<in> set vs \<Longrightarrow> x \<le> foldr max vs (a :: nat)"
  by (induction vs) auto

lemma fresh_nat: "fresh_nat vs \<notin> set vs"
  using foldr_max_ge[of _ vs 0]
  by (fastforce simp: fresh_nat_def)

lemma fresh_nat_avoids_sentinel:
  "fresh_nat (nil # vs) \<notin> set vs" "fresh_nat (nil # vs) \<noteq> nil"
  using fresh_nat[of "nil # vs"] by auto

lemma vset_to_list_rbt: "vset_inv N \<Longrightarrow> set (Tree2.inorder N) = Tree2.set_tree N"
  by simp

subsection \<open>The data structures\<close>

definition "blossom_map_update t (k :: nat) (v :: nat) = update k v t"

definition "blossom_map_get (nil :: nat) t k =
  (case lookup t k of None \<Rightarrow> nil | Some v \<Rightarrow> v)"

definition "blossom_set_invar (nil :: nat) S = (vset_inv S \<and> nil \<notin> t_set S)"

definition "blossom_set_iterate f init S = foldl f init (Tree2.inorder S)"

lemma blossom_rbt_map:
  "fixed_univ_map K M.invar blossom_map_update (blossom_map_get nil)"
  by unfold_locales
     (auto simp: M.map_update M.invar_update blossom_map_update_def blossom_map_get_def)

lemma blossom_rbt_set:
  "fixed_univ_set (- {nil}) (blossom_set_invar nil) t_set
    vset_empty vset_insert vset_delete isin"
  by unfold_locales
     (auto simp: blossom_set_invar_def set.invar_empty[folded RBT_Set.empty_def]
       set.invar_insert set.invar_delete set.set_empty[folded RBT_Set.empty_def]
       set.set_insert set.set_delete set.set_isin)

lemma blossom_rbt_empty:
  "M.invar Leaf" "blossom_map_get nil Leaf = (\<lambda>_. nil)"
  using M.invar_empty by (auto simp: RBT_Set.empty_def blossom_map_get_def)

lemma blossom_rbt_iterate:
  assumes "blossom_set_invar nil S"
  shows "\<exists>xs. t_set S = set xs \<and> distinct xs \<and>
    blossom_set_iterate f init S = foldl f init xs"
proof-
  have "distinct (Tree2.inorder S)"
    using assms unfolding blossom_set_invar_def vset_inv_def
    by (induction S rule: tree2_induct) (auto; meson less_asym)+
  then show ?thesis
    by (intro exI[of _ "Tree2.inorder S"]) (simp add: blossom_set_iterate_def)
qed

global_interpretation matching_rbt: matching_augmentation
  where K = "- {nil}" and buddy_invar = M.invar and buddy_upd = blossom_map_update
    and buddy_get = "blossom_map_get nil" and buddy_empty = Leaf and nil = nil
  for nil
  defines matching_abs_rbt = matching_rbt.\<M>
    and matching_invar_abs_rbt = matching_rbt.invar_matching
    and matching_lookup_rbt = matching_rbt.buddy_lookup
    and matching_partner_rbt = matching_rbt.get_partner
    and augment_rbt = matching_rbt.augment_impl
    and contract_path_rbt = matching_rbt.contract_path
    and contract_at_matched_rbt = matching_rbt.contract_path_at_matched
    and expand_path_rbt = matching_rbt.expand_path_at_matched
    and add_alternatingly_rbt = matching_rbt.add_alternatingly
  by (auto intro!: matching_augmentation.intro Matching_Augmentation_Specs.intro
      matching_augmentation_axioms.intro blossom_rbt_map simp: blossom_rbt_empty)

lemmas blossom_matching_rbt = matching_rbt.blossom_matching_spec_satisfied[
  folded matching_abs_rbt_def matching_invar_abs_rbt_def matching_lookup_rbt_def
    matching_partner_rbt_def augment_rbt_def contract_path_rbt_def expand_path_rbt_def
    add_alternatingly_rbt_def]

global_interpretation gm: Graph_Matching_Specs
  where empty = map_empty and delete = RBT_Map.delete and lookup = lookup and insert = vset_insert
    and isin = isin and t_set = t_set and sel = sel and update = update and adjmap_inv = adj_inv
    and vset_empty = vset_empty and vset_delete = vset_delete and vset_inv = vset_inv
    and K = "- {nil}" and mate_empty = Leaf
    and matching_invar_abs = "matching_invar_abs_rbt nil" and matching_abs = "matching_abs_rbt nil"
    and mate_lookup = "matching_lookup_rbt nil" and mate_partner = "matching_partner_rbt nil"
    and mate_augment = augment_rbt and mate_contract = "contract_path_rbt nil"
    and mate_expand = "expand_path_rbt nil" and mate_add_alternatingly = add_alternatingly_rbt
    and vset_to_list = Tree2.inorder
  for nil
  defines ugraph_abs_rbt = gm.ugraph_abs
    and graph_input_rbt = gm.graph_input
    and matching_invar_rbt = gm.matching_invar
    and neighbourhood_rbt = gm.Graph.neighbourhood
    and add_edge_rbt = gm.Graph.add_edge
    and from_list_rbt = gm.Graph.from_list
    and neighbour_list_rbt = gm.neighbour_list
    and adjacency_edges_rbt = gm.adjacency_edges
proof(rule Graph_Matching_Specs.intro)
  show "Pair_Graph_Specs map_empty RBT_Map.delete lookup vset_insert isin t_set sel update adj_inv
          vset_empty vset_delete vset_inv"
    using G.Pair_Graph_Specs_axioms
    by (simp add: RBT_Set.empty_def adj_inv_def map_empty_def)
  show "blossom_matching (- {nil}) Leaf (matching_invar_abs_rbt nil) (matching_lookup_rbt nil)
    (matching_partner_rbt nil) augment_rbt (matching_abs_rbt nil) (contract_path_rbt nil)
    (expand_path_rbt nil) add_alternatingly_rbt"
    by (rule blossom_matching_rbt)
  show "Graph_Matching_Specs_axioms t_set vset_inv Tree2.inorder"
    by (rule Graph_Matching_Specs_axioms.intro) simp
qed

global_interpretation forest_rbt: forest_manipulation
  where K = "- {nil}"
    and parent_invar = M.invar and parent_upd = blossom_map_update
    and parent_get = "blossom_map_get nil"
    and origin_invar = M.invar and origin_upd = blossom_map_update
    and origin_get = "blossom_map_get nil"
    and vset_invar = "blossom_set_invar nil" and vset_to_set = t_set
    and vset_empty = vset_empty and vset_insert = vset_insert
    and vset_delete = vset_delete and vset_isin = isin
    and vset_iterate = blossom_set_iterate
    and parent_empty = Leaf and origin_empty = Leaf and nil = nil
  for nil
  defines forest_get_path_rbt = forest_rbt.get_path
    and forest_get_path_loop_rbt = forest_rbt.get_path_loop
    and forest_empty_rbt = forest_rbt.empty_forest
    and forest_extend_rbt = forest_rbt.extend_forest_even_unclassified
    and forest_abs_rbt = forest_rbt.abstract_forest
    and forest_invar_rbt = forest_rbt.forest_invar
  by (auto intro!: forest_manipulation.intro forest_manipulation_spec.intro
      forest_manipulation_axioms.intro blossom_rbt_map blossom_rbt_set blossom_rbt_iterate
      simp: blossom_rbt_empty)

lemmas [code] =
  forest_rbt.get_path_loop.simps[folded forest_get_path_loop_rbt_def]
  forest_rbt.get_path_def[folded forest_get_path_rbt_def forest_get_path_loop_rbt_def]

subsection \<open>The alternating forest search\<close>

global_interpretation compute_alt_path: Compute_Alt_Path
  where empty = map_empty and delete = RBT_Map.delete and lookup = lookup and insert = vset_insert
    and isin = isin and t_set = t_set and sel = sel and update = update and adjmap_inv = adj_inv
    and vset_empty = vset_empty and vset_delete = vset_delete and vset_inv = vset_inv
    and K = "- {nil}" and mate_empty = Leaf
    and matching_invar_abs = "matching_invar_abs_rbt nil" and matching_abs = "matching_abs_rbt nil"
    and mate_lookup = "matching_lookup_rbt nil" and mate_partner = "matching_partner_rbt nil"
    and mate_augment = augment_rbt and mate_contract = "contract_path_rbt nil"
    and mate_expand = "expand_path_rbt nil" and mate_add_alternatingly = add_alternatingly_rbt
    and vset_to_list = Tree2.inorder
    and fset_invar = "blossom_set_invar nil" and fset_to_set = t_set
    and fset_empty = vset_empty and fset_insert = vset_insert
    and fset_delete = vset_delete and fset_isin = isin
    and evens = evens and odds = odds and roots = roots
    and get_path = "forest_get_path_rbt nil" and abstract_forest = "forest_abs_rbt nil"
    and forest_invar = "forest_invar_rbt nil"
    and extend_forest_even_unclassified = "forest_extend_rbt nil"
    and empty_forest = forest_empty_rbt
    and G = G and vs = vs and M = N
  for nil G vs N
  defines compute_alt_path_impl = compute_alt_path.Compute_Alt_Path_impl
    and compute_alt_path_free_vertices = compute_alt_path.free_vertices
    and compute_alt_path_initial_roots = compute_alt_path.initial_roots
    and compute_alt_path_initial_state = compute_alt_path.initial_state
    and compute_alt_path_paths = compute_alt_path.alternating_paths
    and compute_alt_path_run_impl = compute_alt_path.Compute_Alt_Path_run_impl
  by (intro Compute_Alt_Path.intro gm.Graph_Matching_Specs_axioms blossom_rbt_set
      forest_rbt.satisified[folded forest_get_path_rbt_def forest_abs_rbt_def forest_invar_rbt_def
        forest_extend_rbt_def forest_empty_rbt_def])

lemma compute_alt_path_run_impl_correct:
  "\<lbrakk>graph_input_rbt nil G vs; matching_invar_rbt nil G N\<rbrakk>
   \<Longrightarrow> compute_alt_path_spec (ugraph_abs_rbt G) (matching_abs_rbt nil N) (compute_alt_path_run_impl nil G vs N)"
  "\<lbrakk>graph_input_rbt nil G vs; matching_invar_rbt nil G N;
    \<exists>p. graph_augmenting_path (ugraph_abs_rbt G) (matching_abs_rbt nil N) p\<rbrakk>
   \<Longrightarrow> compute_alt_path_run_impl nil G vs N \<noteq> None"
  using compute_alt_path.Compute_Alt_Path_run_impl_correct[unfolded compute_alt_path.Compute_Alt_Path_axiom_def,
    folded matching_invar_rbt_def matching_abs_rbt_def]
  by blast+

subsection \<open>Finding an augmenting path or a blossom\<close>

global_interpretation find_aug_path_subprocedures: Find_Aug_Path_subprocedures
  where empty = map_empty and delete = RBT_Map.delete and lookup = lookup and insert = vset_insert
    and isin = isin and t_set = t_set and sel = sel and update = update and adjmap_inv = adj_inv
    and vset_empty = vset_empty and vset_delete = vset_delete and vset_inv = vset_inv
    and K = "- {nil}" and mate_empty = Leaf
    and matching_invar_abs = "matching_invar_abs_rbt nil" and matching_abs = "matching_abs_rbt nil"
    and mate_lookup = "matching_lookup_rbt nil" and mate_partner = "matching_partner_rbt nil"
    and mate_augment = augment_rbt and mate_contract = "contract_path_rbt nil"
    and mate_expand = "expand_path_rbt nil" and mate_add_alternatingly = add_alternatingly_rbt
    and vset_to_list = Tree2.inorder
    and compute_alt_path = "compute_alt_path_run_impl nil"
  for nil
  defines compute_match_blossom_impl = find_aug_path_subprocedures.compute_match_blossom
  by (intro Find_Aug_Path_subprocedures.intro gm.Graph_Matching_Specs_axioms
            Find_Aug_Path_subprocedures_axioms.intro,
      fold graph_input_rbt_def matching_invar_rbt_def ugraph_abs_rbt_def matching_abs_rbt_def,
      insert compute_alt_path_run_impl_correct, blast)

subsection \<open>Searching for an augmenting path by shrinking blossoms\<close>

global_interpretation find_aug_path: Find_Aug_Path
  where empty = map_empty and delete = RBT_Map.delete and lookup = lookup and insert = vset_insert
    and isin = isin and t_set = t_set and sel = sel and update = update and adjmap_inv = adj_inv
    and vset_empty = vset_empty and vset_delete = vset_delete and vset_inv = vset_inv
    and K = "- {nil}" and mate_empty = Leaf
    and matching_invar_abs = "matching_invar_abs_rbt nil" and matching_abs = "matching_abs_rbt nil"
    and mate_lookup = "matching_lookup_rbt nil" and mate_partner = "matching_partner_rbt nil"
    and mate_augment = augment_rbt and mate_contract = "contract_path_rbt nil"
    and mate_expand = "expand_path_rbt nil" and mate_add_alternatingly = add_alternatingly_rbt
    and vset_to_list = Tree2.inorder
    and G = G and vs = vs and M = N
    and blos_search = "compute_match_blossom_impl nil"
    and create_vert = "\<lambda>vs. fresh_nat (nil # vs)"
  for nil G vs N
  defines find_aug_path_impl = find_aug_path.Find_Aug_Path_impl
    and find_aug_path_initial_state = find_aug_path.initial_state
    and find_aug_path_augmenting_path = find_aug_path.augmenting_path
    and find_aug_path_run_impl = find_aug_path.Find_Aug_Path_run_impl
    and contract_vertices_rbt = find_aug_path.contract_vertices
    and contract_graph_rbt = find_aug_path.contract_graph
    and contract_matching_rbt = find_aug_path.contract_matching
    and lift_path_rbt = find_aug_path.lift_path
  apply (intro Find_Aug_Path.intro gm.Graph_Matching_Specs_axioms Find_Aug_Path_axioms.intro)
  apply (fold graph_input_rbt_def matching_invar_rbt_def ugraph_abs_rbt_def matching_abs_rbt_def)
  by ((rule find_aug_path_subprocedures.compute_match_blossom[
        folded graph_input_rbt_def matching_invar_rbt_def ugraph_abs_rbt_def matching_abs_rbt_def];
        assumption) | simp add: fresh_nat_avoids_sentinel)+

lemma find_aug_path_run_impl_correct:
  "\<lbrakk>graph_input_rbt nil G vs; matching_invar_rbt nil G N; find_aug_path_run_impl nil G vs N = Some p\<rbrakk>
   \<Longrightarrow> graph_augmenting_path (ugraph_abs_rbt G) (matching_abs_rbt nil N) p"
  "\<lbrakk>graph_input_rbt nil G vs; matching_invar_rbt nil G N;
    \<exists>p. graph_augmenting_path (ugraph_abs_rbt G) (matching_abs_rbt nil N) p\<rbrakk>
   \<Longrightarrow> find_aug_path_run_impl nil G vs N \<noteq> None"
  using find_aug_path.Find_Aug_Path_run_impl_correct[unfolded find_aug_path.Find_Aug_Path_axiom_def,
          folded graph_input_rbt_def matching_invar_rbt_def ugraph_abs_rbt_def matching_abs_rbt_def]
  by blast+

subsection \<open>The algorithm\<close>

global_interpretation find_max_matching: Find_Max_Matching
  where empty = map_empty and delete = RBT_Map.delete and lookup = lookup and insert = vset_insert
    and isin = isin and t_set = t_set and sel = sel and update = update and adjmap_inv = adj_inv
    and vset_empty = vset_empty and vset_delete = vset_delete and vset_inv = vset_inv
    and K = "- {nil}" and mate_empty = Leaf
    and matching_invar_abs = "matching_invar_abs_rbt nil" and matching_abs = "matching_abs_rbt nil"
    and mate_lookup = "matching_lookup_rbt nil" and mate_partner = "matching_partner_rbt nil"
    and mate_augment = augment_rbt and mate_contract = "contract_path_rbt nil"
    and mate_expand = "expand_path_rbt nil" and mate_add_alternatingly = add_alternatingly_rbt
    and vset_to_list = Tree2.inorder
    and G = G and vs = vs and aug_path_search = "find_aug_path_run_impl nil G vs"
  for nil G vs
  defines find_max_matching_impl = find_max_matching.Find_Max_Matching_impl
    and find_max_matching_initial_state = find_max_matching.initial_state
    and find_max_matching_run_core = find_max_matching.Find_Max_Matching_run_impl
  by (intro Find_Max_Matching.intro gm.Graph_Matching_Specs_axioms
            Find_Max_Matching_axioms.intro,
      fold graph_input_rbt_def matching_invar_rbt_def ugraph_abs_rbt_def matching_abs_rbt_def,
      insert find_aug_path_run_impl_correct, blast+)

definition "find_max_matching_run_impl G vs =
  find_max_matching_run_core (fresh_nat vs) G vs"

subsection \<open>Correctness of the executable algorithm\<close>

context
  fixes nil :: nat and G :: "((nat \<times> (nat \<times> color) tree) \<times> color) tree" and vs :: "nat list"
  assumes graph_input: "graph_input_rbt nil G vs"
begin

interpretation find_max_matching_proofs: Find_Max_Matching_thms
  where empty = map_empty and delete = RBT_Map.delete and lookup = lookup and insert = vset_insert
    and isin = isin and t_set = t_set and sel = sel and update = update and adjmap_inv = adj_inv
    and vset_empty = vset_empty and vset_delete = vset_delete and vset_inv = vset_inv
    and K = "- {nil}" and mate_empty = Leaf
    and matching_invar_abs = "matching_invar_abs_rbt nil" and matching_abs = "matching_abs_rbt nil"
    and mate_lookup = "matching_lookup_rbt nil" and mate_partner = "matching_partner_rbt nil"
    and mate_augment = augment_rbt and mate_contract = "contract_path_rbt nil"
    and mate_expand = "expand_path_rbt nil" and mate_add_alternatingly = add_alternatingly_rbt
    and vset_to_list = Tree2.inorder
    and G = G and vs = vs and aug_path_search = "find_aug_path_run_impl nil G vs"
  by (intro Find_Max_Matching_thms.intro find_max_matching.Find_Max_Matching_axioms
            Find_Max_Matching_thms_axioms.intro)
     (simp add: find_max_matching.Find_Max_Matching_axiom_def graph_input)

lemmas edmonds_blossom_core_correct_1 =
  find_max_matching_proofs.Find_Max_Matching_correct_1[
    folded find_max_matching_proofs.Find_Max_Matching_impl_to_Find_Max_Matching,
    folded find_max_matching_impl_def find_max_matching_initial_state_def,
    folded find_max_matching.Find_Max_Matching_run_impl_def,
    folded graph_input_rbt_def matching_invar_rbt_def ugraph_abs_rbt_def matching_abs_rbt_def]

lemmas edmonds_blossom_core_correct_2 =
  find_max_matching_proofs.Find_Max_Matching_correct_2[
    folded find_max_matching_proofs.Find_Max_Matching_impl_to_Find_Max_Matching,
    folded find_max_matching_impl_def find_max_matching_initial_state_def,
    folded find_max_matching.Find_Max_Matching_run_impl_def,
    folded graph_input_rbt_def matching_invar_rbt_def ugraph_abs_rbt_def matching_abs_rbt_def]

end

lemma edmonds_blossom_correct_1:
  "graph_input_rbt (fresh_nat vs) G vs \<Longrightarrow>
    max_card_matching (ugraph_abs_rbt G)
      (matching_abs_rbt (fresh_nat vs) (current_matching (find_max_matching_run_impl G vs)))"
  using edmonds_blossom_core_correct_1[where nil="fresh_nat vs" and G=G and vs=vs]
  by (simp add: find_max_matching_run_impl_def)

lemma edmonds_blossom_correct_2:
  "graph_input_rbt (fresh_nat vs) G vs \<Longrightarrow>
    matching_invar_rbt (fresh_nat vs) G (current_matching (find_max_matching_run_impl G vs))"
  using edmonds_blossom_core_correct_2[where nil="fresh_nat vs" and G=G and vs=vs]
  by (simp add: find_max_matching_run_impl_def)

subsection \<open>Code generation\<close>

text \<open>The code equations of the later interpretations mention the constants of the data-structure
  layer in their unfolded form; the equations below rewrite them to the constants defined by the
  interpretation of the data-structure layer.\<close>

lemmas [code_unfold] =
  augment_rbt_def[symmetric] adjacency_edges_rbt_def[symmetric]
  neighbourhood_rbt_def[symmetric] from_list_rbt_def[symmetric]
  matching_lookup_rbt_def[symmetric] contract_path_rbt_def[symmetric]
  contract_at_matched_rbt_def[symmetric]

lemmas [code] =
  matching_rbt.contract_path_def[folded contract_path_rbt_def contract_at_matched_rbt_def]
  matching_rbt.contract_path_at_matched_def[folded contract_at_matched_rbt_def]
  matching_rbt.buddy_lookup_def[folded matching_lookup_rbt_def]

subsection \<open>Demonstration\<close>

text \<open>Two triangles joined by an edge. A maximum matching has three edges; finding it requires
  shrinking a triangle.\<close>

definition "demo_edges =
  [(0::nat, 1::nat), (1, 0), (1, 2), (2, 1), (2, 0), (0, 2), (2, 3), (3, 2),
   (3, 4), (4, 3), (4, 5), (5, 4), (5, 3), (3, 5)]"

definition "demo_G = from_list_rbt demo_edges"

definition "demo_vs = [0, 1, 2, 3, 4, 5::nat]"

value "Tree2.inorder (current_matching (find_max_matching_run_impl demo_G demo_vs))"

lemma demo_input: "graph_input_rbt (fresh_nat demo_vs) demo_G demo_vs"
  unfolding demo_G_def
  by (rule gm.from_list_graph_input) (auto simp: demo_edges_def demo_vs_def dVs_eq fresh_nat_def)

lemma demo_max:
  "max_card_matching (ugraph_abs_rbt demo_G)
     (matching_abs_rbt (fresh_nat demo_vs) (current_matching (find_max_matching_run_impl demo_G demo_vs)))"
  by (rule edmonds_blossom_correct_1[OF demo_input])

export_code find_max_matching_run_impl in SML module_name Edmonds_Blossom

end
