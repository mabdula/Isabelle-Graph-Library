theory Hopcroft_Karp_Subprocedures
  imports Hopcroft_Karp_Phase Micali_Vazirani.Alt_BFS_Example Micali_Vazirani.IDFS_Example
          Basic_Matching.Matching_Augmentation_Executable
begin

section \<open>Sub-procedures of the Hopcroft-Karp Algorithm at Red-Black Trees\<close>

text \<open>The phase of @{theory Hopcroft_Karp.Hopcroft_Karp_Phase} at red-black trees: the input
  graph, the graph of copies and their vertex sets, the map of distances and the mate function
  are red-black trees, and the BFS sub-operations are those of
  @{theory Micali_Vazirani.Alt_BFS_Example}. The lemmas meeting the contract of the top loop are
  stated for these operations.\<close>

subsection \<open>The matching, represented by its mate function\<close>

definition "mate_get nil M u = (case lookup M u of None \<Rightarrow> nil | Some v \<Rightarrow> v)"

lemma mate_fixed_univ_map:
  "fixed_univ_map K M.invar (\<lambda>M u v. update u v M) (mate_get nil)"
  by unfold_locales (auto simp: mate_get_def M.map_update M.invar_update)

global_interpretation mate: Matching_Augmentation_Specs "- {nil}" M.invar
  "\<lambda>M u v. update u v M" "mate_get nil" Leaf nil
  for nil
  defines mate_augment = mate.augment_impl
    and mate_matching = mate.\<M>
    and mate_invar = mate.invar_matching
    and mate_lookup = mate.buddy_lookup
  by (auto intro!: Matching_Augmentation_Specs.intro mate_fixed_univ_map)

interpretation mate_thms: matching_augmentation "- {nil}" M.invar
  "\<lambda>M u v. update u v M" "mate_get nil" Leaf nil
  for nil
  by (auto intro!: matching_augmentation.intro matching_augmentation_axioms.intro
                   mate.Matching_Augmentation_Specs_axioms
           simp: mate_get_def M.invar_def rbt_def fun_eq_iff)

lemmas mate_augmentation_correct =
  mate_thms.augmentation_correct[folded mate_invar_def mate_matching_def mate_augment_def]
lemmas mate_empty_props =
  mate_thms.empty_matching_props[folded mate_invar_def mate_matching_def]
lemmas mate_invarD =
  mate.invar_matchingD[folded mate_invar_def mate_matching_def]
lemmas mate_matching_eq = mate.\<M>_def'[folded mate_matching_def mate_lookup_def]

lemma mate_lookup_symmetric:
  "mate_invar nil G m \<Longrightarrow> mate_lookup nil m u = Some v \<longleftrightarrow> mate_lookup nil m v = Some u"
  unfolding mate_lookup_def
  by (rule mate.symmetric_buddiesD[OF mate_invarD(2)])

lemma mate_matching_iff:
  assumes "mate_invar nil G m"
  shows "{u, v} \<in> mate_matching nil m \<longleftrightarrow> mate_get nil m u = v \<and> v \<noteq> nil"
proof-
  have "{u, v} \<in> mate_matching nil m \<longleftrightarrow> mate_lookup nil m u = Some v"
    using assms by (auto simp: mate_matching_eq doubleton_eq_iff dest: mate_lookup_symmetric)
  thus ?thesis by (auto simp: mate_lookup_def mate.buddy_lookup_def)
qed

lemma mate_Vs_iff:
  assumes "mate_invar nil G m"
  shows "v \<in> Vs (mate_matching nil m) \<longleftrightarrow> mate_get nil m v \<noteq> nil"
proof-
  have "v \<in> Vs (mate_matching nil m) \<longleftrightarrow> mate_lookup nil m v \<noteq> None"
    using assms by (auto simp: Vs_def mate_matching_eq dest: mate_lookup_symmetric)
  thus ?thesis by (auto simp: mate_lookup_def mate.buddy_lookup_def)
qed

subsection \<open>The input\<close>

global_interpretation hopcroft_karp_input_rbt: Hopcroft_Karp_Input
  where insert = insert_rbt and isin = isin and t_set = Tree2.set_tree and sel = sel
    and vset_empty = Leaf and vset_delete = RBT.delete and vset_inv = vset_inv
    and lookup = lookup and adjmap_inv = M.invar
  for G vertex_list
  defines ugraph_abs_rbt = hopcroft_karp_input_rbt.ugraph_abs
    and hopcroft_karp_axiom_rbt = hopcroft_karp_input_rbt.Hopcroft_Karp_axiom
  using S_C.Set_Choose_axioms
  by (simp add: Hopcroft_Karp_Input_def Pair_Graph_Specs_Read_Only_def)

subsection \<open>The input graph as a list of edges\<close>

definition "adjacency_edges Gin vs =
  concat (map (\<lambda>u. map (Pair u) (Tree2.inorder (G.neighbourhood Gin u))) vs)"

lemma adjacency_edges_set:
  "hopcroft_karp_axiom_rbt Gin vs \<Longrightarrow> set (adjacency_edges Gin vs) = G.digraph_abs Gin"
  using G.are_connected_abs[of Gin]
  by (auto simp: adjacency_edges_def hopcroft_karp_input_rbt.Hopcroft_Karp_axiom_def)

subsection \<open>The phase\<close>

global_interpretation phase: Hopcroft_Karp_Phase
  where empty = RBT_Set.empty and delete = RBT_Map.delete and lookup = lookup
    and insert = insert_rbt and isin = isin and t_set = Tree2.set_tree and sel = sel
    and update = update and adjmap_inv = M.invar and vset_empty = Leaf
    and vset_delete = delete_rbt and vset_inv = vset_inv
    and union = union_rbt and inter = inter_rbt and diff = diff_rbt
    and c_empty = map_empty and c_delete = RBT_Map.delete and c_lookup = lookup
    and c_insert = vset_insert and c_isin = isin and c_t_set = t_set and c_sel = sel
    and c_update = update and c_adjmap_inv = adj_inv and c_vset_empty = vset_empty
    and c_vset_delete = vset_delete and c_vset_inv = vset_inv
    and c_union = vset_union and c_inter = vset_inter and c_diff = vset_diff
    and K = "- {nil}" and nil = nil and mate_get = "mate_get nil"
    and mate_invar = "mate_invar nil" and mate_matching = "mate_matching nil"
    and lookup_dist = lookup and empty_dist = Leaf and update_dist = update
    and delete_dist = RBT_Map.delete and invar_dist = M.invar
    and expand_tree = expand_tree and next_frontier_impl = next_frontier
    and upd_dists = upd_dists_exec and init_dists_of = init_dists_exec
  for nil
  defines hopcroft_karp_phase = phase.hopcroft_karp_phase
    and matched_edges = phase.matched_edges
    and unmatched_edges = phase.unmatched_edges
    and free_vertices = phase.free_vertices
    and free_vertex_set = phase.free_vertex_set
    and copies_edges = phase.copies_edges
    and copy_level = phase.copy_level
    and phase_roots = phase.phase_roots
    and blocked_copies = phase.blocked_copies
    and c_vset_of_list_rbt = phase.c_vset_of_list
    and IDFS_stack0_rbt = phase.IDFS_stack0_c
    and IDFS_impl_rbt = phase.IDFS_impl_c
proof(intro Hopcroft_Karp_Phase.intro Hopcroft_Karp_Phase_axioms.intro, goal_cases)
  case 1
  show ?case
    using alt_bfs.BFS_axioms unfolding Alt_BFS.BFS_def RBT_Set.empty_def by blast
next
  case 2
  show ?case
    using alt_bfs.BFS_axioms unfolding Alt_BFS.BFS_def RBT_Set.empty_def by blast
next
  case 3
  show ?case
    using G.Pair_Graph_Specs_axioms
    by (simp add: adj_inv_def map_empty_def RBT_Set.empty_def)
next
  case 4
  show ?case
    using RBT.Set2_axioms
    by (simp add: vset_inv_def RBT_Set.empty_def)
next
  case 5
  show ?case
    by (rule mate_thms.matching.Matching_Specs_axioms[folded mate_invar_def mate_matching_def])
next
  case (6 srcs)
  show ?case
    using alt_bfs.BFS_axioms[of srcs] by (simp add: RBT_Set.empty_def)
qed

subsection \<open>Code equations\<close>

text \<open>The sub-procedures of the phase are partially applied instances of locale constants. As
  for the graph operations in the executable algorithm, each is replaced at code-generation time by
  a global constant with its own code equations: the alternating BFS by that of
  @{theory Micali_Vazirani.Alt_BFS_Example}, the incremental DFS by that of
  @{theory Micali_Vazirani.IDFS_Example}, and the disjoint-paths search by the constants below.\<close>

lemma phase_bfs_code_unfold[code_unfold]:
  "phase.phase_bfs.BFS_impl mG uG state = alt_bfs_impl mG uG state"
  "phase.phase_bfs.initial_state srcs = alt_bfs_initial_state srcs"
  by (simp_all add: alt_bfs_impl_def alt_bfs_initial_state_def)

lemmas IDFS_impl_rbt_code[code] = phase.IDFS_impl_c_def[folded avoid_impl_rbt_def]

definition "disjoint_paths_search_impl_rbt blk CG P =
  phase.phase_search.Disjoint_Paths_Search_impl blk CG P"

definition "disjoint_paths_search_rbt blk rs CG P =
  phase.phase_search.Disjoint_Paths_Search_run_impl blk rs CG P"

lemmas disjoint_paths_search_impl_rbt_code[code] =
  phase.phase_search.Disjoint_Paths_Search_impl.simps[folded disjoint_paths_search_impl_rbt_def]

lemma disjoint_paths_search_rbt_code[code]:
  "disjoint_paths_search_rbt blk rs CG P =
     disjoint_paths_search_impl_rbt blk CG P
       \<lparr>roots = rs, avoided = vset_empty, explored = vset_empty, paths = []\<rparr>"
  by (simp add: disjoint_paths_search_rbt_def disjoint_paths_search_impl_rbt_def
                phase.phase_search.Disjoint_Paths_Search_run_impl_def
                phase.phase_search.initial_state_def)

lemma disjoint_paths_search_code_unfold[code_unfold]:
  "phase.phase_search.Disjoint_Paths_Search_run_impl blk rs CG P = disjoint_paths_search_rbt blk rs CG P"
  by (simp add: disjoint_paths_search_rbt_def)

subsection \<open>The sub-procedures meet the contracts of the top loop\<close>

lemma matching:
  "mate_invar nil (ugraph_abs_rbt G) M \<Longrightarrow> graph_matching (ugraph_abs_rbt G) (mate_matching nil M)"
  "nil \<notin> Vs (ugraph_abs_rbt G) \<Longrightarrow> mate_invar nil (ugraph_abs_rbt G) Leaf"
  "mate_matching nil Leaf = {}"
  by (auto dest: mate_invarD(4) intro: mate_empty_props(1) simp: mate_empty_props(2))

lemma augment:
  "\<lbrakk>mate_invar nil (ugraph_abs_rbt G) M; graph_augmenting_path (ugraph_abs_rbt G) (mate_matching nil M) p\<rbrakk>
   \<Longrightarrow> mate_invar nil (ugraph_abs_rbt G) (mate_augment M p)"
  "\<lbrakk>mate_invar nil (ugraph_abs_rbt G) M; graph_augmenting_path (ugraph_abs_rbt G) (mate_matching nil M) p\<rbrakk>
   \<Longrightarrow> mate_matching nil (mate_augment M p) = mate_matching nil M \<oplus> set (edges_of_path p)"
  by (simp_all add: mate_augmentation_correct)

lemma bipartite_of_axiom:
  "hopcroft_karp_axiom_rbt G vs \<Longrightarrow> \<exists>X Y. bipartite (ugraph_abs_rbt G) X Y"
  unfolding hopcroft_karp_input_rbt.Hopcroft_Karp_axiom_def
  by blast

lemma phase_sound:
  assumes "hopcroft_karp_axiom_rbt G vs" "mate_invar nil (ugraph_abs_rbt G) M"
    "p \<in> set (hopcroft_karp_phase nil (adjacency_edges G vs) vs M)"
  shows "graph_augmenting_path (ugraph_abs_rbt G) (mate_matching nil M) p"
proof -
  obtain X Y where "bipartite (ugraph_abs_rbt G) X Y"
    using bipartite_of_axiom[OF assms(1)] by blast
  then show ?thesis
    using phase.phase_sound[OF _ _ adjacency_edges_set[OF assms(1)]] assms
    unfolding ugraph_abs_rbt_def hopcroft_karp_axiom_rbt_def by blast
qed

lemma phase_disjoint:
  assumes "hopcroft_karp_axiom_rbt G vs" "mate_invar nil (ugraph_abs_rbt G) M"
  shows "sorted_wrt (\<lambda>p q. set p \<inter> set q = {}) (hopcroft_karp_phase nil (adjacency_edges G vs) vs M)"
proof -
  obtain X Y where "bipartite (ugraph_abs_rbt G) X Y"
    using bipartite_of_axiom[OF assms(1)] by blast
  then show ?thesis
    using phase.phase_disjoint[OF _ _ adjacency_edges_set[OF assms(1)]] assms
    unfolding ugraph_abs_rbt_def hopcroft_karp_axiom_rbt_def by blast
qed

lemma phase_complete:
  assumes "hopcroft_karp_axiom_rbt G vs" "mate_invar nil (ugraph_abs_rbt G) M"
    "\<exists>p. graph_augmenting_path (ugraph_abs_rbt G) (mate_matching nil M) p"
  shows "hopcroft_karp_phase nil (adjacency_edges G vs) vs M \<noteq> []"
proof -
  obtain X Y where "bipartite (ugraph_abs_rbt G) X Y"
    using bipartite_of_axiom[OF assms(1)] by blast
  then show ?thesis
    using phase.phase_complete[OF _ _ adjacency_edges_set[OF assms(1)]] assms
    unfolding ugraph_abs_rbt_def hopcroft_karp_axiom_rbt_def by blast
qed

lemmas phase = phase_sound phase_disjoint phase_complete

end
