theory Hopcroft_Karp_Subprocedures
  imports Hopcroft_Karp_Phase Micali_Vazirani.Alt_BFS_Example Micali_Vazirani.IDFS_Example
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

<<<<<<< HEAD
definition "matched_edges nil edges m = filter (\<lambda>(u, v). mate_get nil m u = v) edges"

definition "unmatched_edges nil edges m = filter (\<lambda>(u, v). mate_get nil m u \<noteq> v) edges"

definition "free_vertices nil vs m = filter (\<lambda>v. mate_get nil m v = nil) vs"

definition "free_vertex_set nil vs m = foldr insert_rbt (free_vertices nil vs m) Leaf"

definition "copies_edges nil edges m dag =
  concat (map (\<lambda>(u, v).
     if isin (G.neighbourhood dag u) v
     then (if mate_get nil m u = v then [(Vtx Even v, Vtx Odd u)] else [(Vtx Odd v, Vtx Even u)])
     else []) edges)"

definition "copy_level dists w = the_enat (the (lookup dists w))"

definition "phase_roots nil vs m odd_visited dists =
  (let free_odd = filter (\<lambda>t. isin odd_visited t) (free_vertices nil vs m) in
   if free_odd = [] then [] else
   let k = fold min (map (\<lambda>t. copy_level dists (Vtx Odd t)) (tl free_odd))
                    (copy_level dists (Vtx Odd (hd free_odd)))
   in map (Vtx Odd) (filter (\<lambda>t. copy_level dists (Vtx Odd t) = k) free_odd))"

definition "blocked_copies copies p =
  vset_of_list_rbt
    (filter (\<lambda>w. w \<in> set copies) (concat (map (\<lambda>w. [Vtx Even (vtx w), Vtx Odd (vtx w)]) p)))"

definition "IDFS_stack0_rbt avoid vis p =
  (if p \<noteq> [] \<and> (isin avoid (hd p) \<or> isin vis (hd p)) then tl p else p)"

definition "IDFS_impl_rbt CG P avoid p vis =
  (let state = avoid_impl_rbt CG (IDFS_stack0_rbt avoid vis p) vis avoid P
   in (DFS_avoid_state.ret state, DFS_avoid_state.visited state))"

subsection \<open>Auxiliary lemmas\<close>

lemma fold_min_mem: "fold min xs (x::nat) \<in> Set.insert x (set xs)"
  by (induction xs arbitrary: x) (auto simp: min_def)

lemma layered_dgraph_cong:
  assumes "\<And>w. w \<in> dVs dG \<Longrightarrow> f w = g w" "layered_dgraph dG f"
  shows "layered_dgraph dG g"
proof(rule layered_dgraphI)
  show "finite (dVs dG)"
    using assms(2)
    by (rule layered_dgraph_finite)
  show "g v' < g v" if "(v, v') \<in> dG" for v v'
  proof-
    have "v \<in> dVs dG" "v' \<in> dVs dG"
      using that
      by auto
    thus ?thesis
      using layered_dgraph_level[OF assms(2) that] assms(1)[of v] assms(1)[of v']
      by simp
  qed
  show "\<exists>p v'. dpath_bet dG p v v' \<and> g v' = 0" if "v \<in> dVs dG" for v
  proof-
    obtain p v' where "p \<noteq> []" "dpath_bet dG p v v'" "f v' = 0"
      using layered_dgraph_base[OF assms(2) \<open>v \<in> dVs dG\<close>]
      by blast
    moreover hence "v' \<in> dVs dG"
      by (auto intro: vwalk_bet_in_dVs simp: last_of_vwalk_bet)
    ultimately show ?thesis
      using assms(1)
      by auto
  qed
qed

lemma vset_of_list_rbt_props[simp]:
  "vset_inv (vset_of_list_rbt xs)" "Tree2.set_tree (vset_of_list_rbt xs) = set xs"
  by (induction xs)
     (simp_all add: idfs.vset_of_list_def idfs.Graph.vset.set.invar_empty idfs.Graph.vset.set.set_empty)

lemma set_tree_foldr_insert_rbt[simp]:
  "vset_inv (foldr insert_rbt xs Leaf)" "Tree2.set_tree (foldr insert_rbt xs Leaf) = set xs"
  by (induction xs)
     (simp_all add: idfs.Graph.vset.set.invar_empty idfs.Graph.vset.set.set_empty)

lemma finite_neighbourhood_of_finite:
  "finite E \<Longrightarrow> finite (Pair_Graph.neighbourhood E u)"
  unfolding Pair_Graph.neighbourhood_def
  by (rule finite_subset[where B = "snd ` E"]) (auto intro: rev_image_eqI)

subsection \<open>The incremental DFS meets the contract of the search step\<close>

context
  fixes CG lev
  assumes layered: "idfs.Graph.layered_graph_input CG lev"
begin

interpretation idfs_witness: IDFS_witness
  where insert = vset_insert and sel = sel and vset_empty = vset_empty
    and diff = vset_diff and lookup = lookup and empty = map_empty
    and delete = RBT_Map.delete and isin = isin and t_set = t_set
    and update = update and adjmap_inv = adj_inv
    and vset_delete = vset_delete and vset_inv = vset_inv
    and union = vset_union and inter = vset_inter
    and G = CG and lev = lev
proof(intro IDFS.IDFS_witness.intro IDFS.IDFS_witness_axioms.intro, goal_cases)
  case 1
  show ?case
    using G.Pair_Graph_Specs_axioms
    by (simp add: adj_inv_def map_empty_def RBT_Set.empty_def)
next
  case 2
  show ?case
    using RBT.Set2_axioms
    by (simp add: vset_inv_def RBT_Set.empty_def)
next
  case 3
  show ?case
    by (rule layered)
qed

lemma IDFS_impl_rbt_eq: "IDFS_impl_rbt CG = idfs_witness.IDFS_impl"
  by (intro ext)
     (simp add: IDFS_impl_rbt_def IDFS_stack0_rbt_def idfs_witness.IDFS_impl_def
                idfs_witness.IDFS_stack0_def avoid_impl_rbt_def)

lemma search_step:
  assumes "vset_inv avoid" "vset_inv vis" "t_set avoid \<subseteq> dVs (idfs.Graph.digraph_abs CG)"
          "t_set vis \<subseteq> dVs (idfs.Graph.digraph_abs CG)" "r \<in> dVs (idfs.Graph.digraph_abs CG)"
  shows "IDFS_impl_rbt CG P avoid [r] vis = (res, vis') \<Longrightarrow> vset_inv vis'"
        "IDFS_impl_rbt CG P avoid [r] vis = (res, vis') \<Longrightarrow>
           t_set vis' \<subseteq> dVs (idfs.Graph.digraph_abs CG)"
        "IDFS_impl_rbt CG P avoid [r] vis = (res, vis') \<Longrightarrow> t_set vis \<subseteq> t_set vis'"
        "\<lbrakk>IDFS_impl_rbt CG P avoid [r] vis = (None, vis'); r \<notin> t_set avoid\<rbrakk>
         \<Longrightarrow> r \<in> t_set vis'"
        "\<lbrakk>IDFS_impl_rbt CG P avoid [r] vis = (None, vis'); v \<in> t_set vis' - t_set vis;
          (v, w) \<in> idfs.Graph.digraph_abs CG\<rbrakk>
         \<Longrightarrow> w \<in> t_set avoid \<union> t_set vis'"
        "\<lbrakk>IDFS_impl_rbt CG P avoid [r] vis = (res, vis'); v \<in> t_set vis' - t_set vis\<rbrakk>
         \<Longrightarrow> \<not> P v"
        "IDFS_impl_rbt CG P avoid [r] vis = (Some p, vis') \<Longrightarrow>
           Vwalk.vwalk (idfs.Graph.digraph_abs CG) (rev p) \<and> p \<noteq> [] \<and> distinct p \<and> P (hd p) \<and>
           last p = r \<and> set p \<inter> (t_set avoid \<union> t_set vis') = {}"
proof-
  have "dpath (idfs.Graph.digraph_abs CG) (rev [r])" "distinct [r]"
    using assms(5)
    by (auto intro: vwalk1)
  note pre = this assms(1-4)
  show "vset_inv vis'" if "IDFS_impl_rbt CG P avoid [r] vis = (res, vis')"
    by (rule idfs_witness.IDFS_vis_works_4[OF pre that[unfolded IDFS_impl_rbt_eq]])
  show "t_set vis' \<subseteq> dVs (idfs.Graph.digraph_abs CG)"
    if "IDFS_impl_rbt CG P avoid [r] vis = (res, vis')"
    by (rule idfs_witness.IDFS_dVs_bound[OF pre that[unfolded IDFS_impl_rbt_eq]])
  show "t_set vis \<subseteq> t_set vis'" if "IDFS_impl_rbt CG P avoid [r] vis = (res, vis')"
    by (rule idfs_witness.IDFS_vis_works_3[OF pre that[unfolded IDFS_impl_rbt_eq]])
  show "r \<in> t_set vis'" if "IDFS_impl_rbt CG P avoid [r] vis = (None, vis')" "r \<notin> t_set avoid"
    using idfs_witness.IDFS_complete_w[OF pre, where P = P and vis' = vis']
          that[unfolded IDFS_impl_rbt_eq]
    by auto
  show "w \<in> t_set avoid \<union> t_set vis'"
    if "IDFS_impl_rbt CG P avoid [r] vis = (None, vis')" "v \<in> t_set vis' - t_set vis"
       "(v, w) \<in> idfs.Graph.digraph_abs CG"
    using idfs_witness.IDFS_closed_None[OF pre, where P = P and vis' = vis' and v = v and w = w]
          that[unfolded IDFS_impl_rbt_eq]
    by auto
  show "\<not> P v" if "IDFS_impl_rbt CG P avoid [r] vis = (res, vis')" "v \<in> t_set vis' - t_set vis"
    using that(2)
    by (rule idfs_witness.IDFS_vis_works_1[OF pre that(1)[unfolded IDFS_impl_rbt_eq]])
  show "Vwalk.vwalk (idfs.Graph.digraph_abs CG) (rev p) \<and> p \<noteq> [] \<and> distinct p \<and> P (hd p) \<and>
          last p = r \<and> set p \<inter> (t_set avoid \<union> t_set vis') = {}"
    if "IDFS_impl_rbt CG P avoid [r] vis = (Some p, vis')"
    using idfs_witness.IDFS_sound_1[OF pre, where P = P and vis' = vis' and p' = p]
          idfs_witness.IDFS_sound_2[OF pre, where P = P and vis' = vis' and p' = p]
          idfs_witness.IDFS_sound_3[OF pre, where P = P and vis' = vis' and p' = p]
          idfs_witness.IDFS_sound_6[OF pre, where P = P and vis' = vis' and p' = p]
          idfs_witness.IDFS_sound_7[OF pre, where P = P and vis' = vis' and p' = p]
          idfs_witness.IDFS_sound_8[OF pre, where P = P and vis' = vis' and p' = p]
          that[unfolded IDFS_impl_rbt_eq]
    by auto
qed

end

subsection \<open>The executable disjoint-paths search\<close>

global_interpretation phase_search: Disjoint_Paths_Search
  where insert = vset_insert and sel = sel and vset_empty = vset_empty
    and diff = vset_diff and lookup = lookup and empty = map_empty
    and delete = RBT_Map.delete and isin = isin and t_set = t_set
    and update = update and adjmap_inv = adj_inv
    and vset_delete = vset_delete and vset_inv = vset_inv
    and union = vset_union and inter = vset_inter
    and G = CG and target = P and blocked = blk and initial_roots = rs
    and search_step = "\<lambda>avoid r vis. IDFS_impl_rbt CG P avoid [r] vis"
  for CG P blk rs
  defines disjoint_paths_search_impl_rbt = phase_search.Disjoint_Paths_Search_impl
    and disjoint_paths_search_initial_state = phase_search.initial_state
    and disjoint_paths_search_rbt = phase_search.Disjoint_Paths_Search_run_impl
proof(intro Disjoint_Paths_Search.intro Disjoint_Paths_Search_axioms.intro, goal_cases)
  case 1
  show ?case
    using G.Pair_Graph_Specs_axioms
    by (simp add: adj_inv_def map_empty_def RBT_Set.empty_def)
next
  case 2
  show ?case
    using RBT.Set2_axioms
    by (simp add: vset_inv_def RBT_Set.empty_def)
qed (fact search_step)+

subsection \<open>The phase\<close>

definition "hopcroft_karp_phase nil edges vs m =
  (if free_vertices nil vs m = [] then [] else
   let matching_graph = G.from_list (matched_edges nil edges m);
       non_matching_graph = G.from_list (unmatched_edges nil edges m);
       bfs_state = alt_bfs_impl matching_graph non_matching_graph
                     (alt_bfs_initial_state (free_vertex_set nil vs m));
       copies_edge_list = copies_edges nil edges m (Alt_BFS.BFS_state.parents bfs_state);
       copies_graph = idfs.Graph.from_list copies_edge_list;
       level = copy_level (distances bfs_state)
   in map (map vtx)
        (paths (disjoint_paths_search_rbt copies_graph (\<lambda>w. level w = 0)
                  (blocked_copies (map fst copies_edge_list @ map snd copies_edge_list))
                  (phase_roots nil vs m (visited_odd bfs_state) (distances bfs_state)))))"

lemma hopcroft_karp_phase_no_free:
  "free_vertices nil vs m = [] \<Longrightarrow> hopcroft_karp_phase nil edges vs m = []"
  by (simp add: hopcroft_karp_phase_def)

subsection \<open>The input graph\<close>

context
  fixes Gin and vs :: "('a::linorder) list" and X Y and nil :: 'a
  assumes input: "hopcroft_karp_axiom_rbt Gin vs" "bipartite (ugraph_abs_rbt Gin) X Y"
begin

lemma input_props[simp]:
  "G.graph_inv Gin" "G.finite_graph Gin" "G.finite_vsets Gin"
  "(u, u) \<notin> G.digraph_abs Gin" "set vs = dVs (G.digraph_abs Gin)"
  using input(1)
  by (auto simp: hopcroft_karp_input_rbt.Hopcroft_Karp_axiom_def)

lemma input_sym: "(u, v) \<in> G.digraph_abs Gin \<Longrightarrow> (v, u) \<in> G.digraph_abs Gin"
  using input(1)
  by (auto simp: hopcroft_karp_input_rbt.Hopcroft_Karp_axiom_def)

lemma adjacency_edges_set[simp]: "set (adjacency_edges Gin vs) = G.digraph_abs Gin"
  using G.are_connected_abs[OF input_props(1)]
  by (auto simp: adjacency_edges_def)

lemma ugraph_abs_rbt_edge_iff[simp]:
  "{u, v} \<in> ugraph_abs_rbt Gin \<longleftrightarrow> (u, v) \<in> G.digraph_abs Gin"
  by (auto simp: hopcroft_karp_input_rbt.ugraph_abs_def doubleton_eq_iff dest: input_sym)

lemma Vs_ugraph_abs_rbt[simp]: "Vs (ugraph_abs_rbt Gin) = set vs"
  by (auto simp: hopcroft_karp_input_rbt.ugraph_abs_def Vs_def dVs_def)

lemma ugraph_abs_rbt_graph_invar: "graph_invar (ugraph_abs_rbt Gin)"
proof-
  have "u \<noteq> v" if "(u, v) \<in> G.digraph_abs Gin" for u v
    using that input_props(4)
    by auto
  hence "dblton_graph (ugraph_abs_rbt Gin)"
    unfolding dblton_graph_def hopcroft_karp_input_rbt.ugraph_abs_def
    by blast
  thus ?thesis
    using finite_set[of vs]
    by simp
=======
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
    and mate_empty = Leaf and mate_update = update and mate_delete = RBT_Map.delete
    and mate_lookup = lookup and mate_map_invar = M.invar
    and lookup_dist = lookup and empty_dist = Leaf and update_dist = update
    and delete_dist = RBT_Map.delete and invar_dist = M.invar
    and expand_tree = expand_tree and next_frontier_impl = next_frontier
    and upd_dists = upd_dists_exec and init_dists_of = init_dists_exec
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
    by (rule mate.Matching_Augmentation_Specs_axioms)
next
  case (6 srcs)
  show ?case
    using alt_bfs.BFS_axioms[of srcs] by (simp add: RBT_Set.empty_def)
>>>>>>> main
qed

subsection \<open>Code equations\<close>

<<<<<<< HEAD
context
  fixes m
  assumes m_invar: "mate_invar nil (ugraph_abs_rbt Gin) m" and m_free: "free_vertices nil vs m \<noteq> []"
begin

abbreviation "edge_list \<equiv> adjacency_edges Gin vs"
abbreviation "matching_graph \<equiv> G.from_list (matched_edges nil edge_list m)"
abbreviation "non_matching_graph \<equiv> G.from_list (unmatched_edges nil edge_list m)"
abbreviation "bfs_sources \<equiv> free_vertex_set nil vs m"
abbreviation "bfs_state \<equiv> alt_bfs_impl matching_graph non_matching_graph (alt_bfs_initial_state bfs_sources)"
abbreviation "bfs_dag \<equiv> Alt_BFS.BFS_state.parents bfs_state"
abbreviation "copies_edge_list \<equiv> copies_edges nil edge_list m bfs_dag"
abbreviation "copies_graph \<equiv> idfs.Graph.from_list copies_edge_list"
abbreviation "level \<equiv> copy_level (distances bfs_state)"
abbreviation "copy_roots \<equiv> phase_roots nil vs m (visited_odd bfs_state) (distances bfs_state)"
abbreviation "blocked \<equiv> blocked_copies (map fst copies_edge_list @ map snd copies_edge_list)"
abbreviation "search_state \<equiv>
  phase_search.Disjoint_Paths_Search blocked copies_graph (\<lambda>w. level w = 0)
    (phase_search.initial_state copy_roots)"

lemma mate_matching_subset: "mate_matching nil m \<subseteq> ugraph_abs_rbt Gin"
  using mate_invarD(4)[OF m_invar]
  by auto

lemma matching_graph_vertices:
  "nil \<notin> Vs (ugraph_abs_rbt Gin)"
  using mate_invarD(6)[OF m_invar] by auto

lemma input_edge_not_nil[simp]:
  "(u, v) \<in> G.digraph_abs Gin \<Longrightarrow> u \<noteq> nil"
  "(u, v) \<in> G.digraph_abs Gin \<Longrightarrow> v \<noteq> nil"
  using matching_graph_vertices
  by (auto simp: hopcroft_karp_input_rbt.ugraph_abs_def Vs_def)

lemma matching_graph_abs: "G.digraph_abs matching_graph = {(u, v). {u, v} \<in> mate_matching nil m}"
proof-
  have "(u, v) \<in> G.digraph_abs Gin" if "mate_get nil m u = v" "v \<noteq> nil" for u v
    using mate_matching_subset that mate_matching_iff[OF m_invar, of u v]
    by auto
  thus ?thesis
    by (auto simp: matched_edges_def mate_matching_iff[OF m_invar] dest: input_edge_not_nil)
qed

lemma non_matching_graph_abs:
  "G.digraph_abs non_matching_graph = {(u, v). {u, v} \<in> ugraph_abs_rbt Gin - mate_matching nil m}"
  by (auto simp: unmatched_edges_def mate_matching_iff[OF m_invar] dest: input_edge_not_nil)

lemma bfs_sources_props:
  "vset_inv bfs_sources" "Tree2.set_tree bfs_sources = set (free_vertices nil vs m)"
  "Tree2.set_tree bfs_sources = Vs (ugraph_abs_rbt Gin) - Vs (mate_matching nil m)"
  by (auto simp: free_vertex_set_def free_vertices_def mate_Vs_iff[OF m_invar])

lemma bfs_sources_in_graph: "Tree2.set_tree bfs_sources \<subseteq> dVs (G.digraph_abs non_matching_graph)"
proof
  fix v
  assume "v \<in> Tree2.set_tree bfs_sources"
  then obtain w where "(v, w) \<in> G.digraph_abs Gin" "mate_get nil m v = nil"
    by (auto simp: bfs_sources_props(2) free_vertices_def dVs_eq dest: input_sym)
  thus "v \<in> dVs (G.digraph_abs non_matching_graph)"
    unfolding non_matching_graph_abs
    by (auto simp: mate_matching_iff[OF m_invar])
qed

lemma phase_bfs_axiom:
  "Alt_BFS.BFS.BFS_axiom isin Tree2.set_tree M.invar Leaf vset_inv lookup
     bfs_sources matching_graph non_matching_graph"
proof-
  have "finite (G.digraph_abs matching_graph)" "finite (G.digraph_abs non_matching_graph)"
    by simp_all
  hence "\<forall>u. finite (Pair_Graph.neighbourhood (G.digraph_abs matching_graph) u)"
        "\<forall>u. finite (Pair_Graph.neighbourhood (G.digraph_abs non_matching_graph) u)"
    by (auto intro: finite_neighbourhood_of_finite)
  moreover have "Tree2.set_tree bfs_sources \<noteq> {}"
    using bfs_sources_props(2) m_free
    by simp
  moreover have "G.digraph_abs matching_graph \<inter> G.digraph_abs non_matching_graph = {}"
    unfolding matching_graph_abs non_matching_graph_abs
    by auto
  ultimately show ?thesis
    unfolding phase_bfs.BFS_axiom_def
    using G.from_list_correct(1-3) bfs_sources_props(1) bfs_sources_in_graph
    by (auto simp: G.from_list_correct(1-3))
qed

lemma bipartite_matching_input_phase:
  "phase_bfs.bipartite_matching_input bfs_sources matching_graph non_matching_graph
     (ugraph_abs_rbt Gin) (mate_matching nil m) X Y"
  using ugraph_abs_rbt_graph_invar mate_matching_subset matching_graph_abs non_matching_graph_abs
        bfs_sources_props(3) input(2)
  by (simp add: phase_bfs.bipartite_matching_input_def)

lemma bfs_state_eq: "bfs_state = alt_bfs.BFS matching_graph non_matching_graph (alt_bfs_initial_state bfs_sources)"
  by (rule alt_bfs.BFS_impl_same[OF alt_bfs.initial_state_props(13)[OF phase_bfs_axiom]])

lemma bfs_state_valid_impl:
  "phase_bfs.valid_alt_BFS_DAG_impl bfs_sources matching_graph non_matching_graph bfs_dag
     (distances bfs_state) (visited_even bfs_state) (visited_odd bfs_state)"
  unfolding bfs_state_eq
  by (rule alt_bfs.BFS_valid_DAG_impl[OF phase_bfs_axiom])

lemma bfs_state_valid:
  "phase_bfs.valid_alt_BFS_DAG bfs_sources matching_graph non_matching_graph bfs_dag
     (distances bfs_state) (visited_even bfs_state) (visited_odd bfs_state)"
  by (rule phase_bfs.valid_alt_BFS_DAG_impl_props(7)[OF phase_bfs_axiom bfs_state_valid_impl])

lemma bfs_dag_subset: "G.digraph_abs bfs_dag \<subseteq> G.digraph_abs Gin"
proof
  fix e
  assume "e \<in> G.digraph_abs bfs_dag"
  then obtain u v where e: "e = (u, v)" and edge: "(u, v) \<in> G.digraph_abs bfs_dag"
    by (cases e) auto
  from phase_bfs.valid_alt_BFS_DAG_props(3)[OF phase_bfs_axiom bfs_state_valid edge]
  show "e \<in> G.digraph_abs Gin"
    unfolding e
    by (auto simp only: G.from_list_correct(4) matched_edges_def unmatched_edges_def
                        set_filter adjacency_edges_set case_prod_conv)
qed

lemma bfs_dag_graph_inv: "G.graph_inv bfs_dag"
  by (rule phase_bfs.valid_alt_BFS_DAG_impl_props(1)[OF phase_bfs_axiom bfs_state_valid_impl])

lemma isin_bfs_dag: "isin (G.neighbourhood bfs_dag u) v \<longleftrightarrow> (u, v) \<in> G.digraph_abs bfs_dag"
  using G.are_connected_abs[OF bfs_dag_graph_inv, of v u]
        set.set_isin[OF G.neighbourhood_invars'[OF bfs_dag_graph_inv, of u], of v]
  by simp

lemma copies_graph_abs:
  "idfs.Graph.digraph_abs copies_graph =
     phase_bfs.copies_dag matching_graph non_matching_graph (G.digraph_abs bfs_dag)"
  using bfs_dag_subset
  by (auto simp: copies_edges_def isin_bfs_dag phase_bfs.copies_dag_def
                 matching_graph_abs[unfolded G.from_list_correct(4)]
                 non_matching_graph_abs[unfolded G.from_list_correct(4)] mate_matching_iff[OF m_invar]
           dest: input_edge_not_nil split: if_splits)

lemma copies_graph_level:
  "w \<in> dVs (idfs.Graph.digraph_abs copies_graph) \<Longrightarrow>
   level w = phase_bfs.copies_lev bfs_sources matching_graph non_matching_graph w"
proof-
  assume "w \<in> dVs (idfs.Graph.digraph_abs copies_graph)"
  hence "w \<in> dVs (phase_bfs.copies_dag matching_graph non_matching_graph (G.digraph_abs bfs_dag))"
    by (simp only: copies_graph_abs)
  thus ?thesis
    using phase_bfs.copies_lev_by_lookup[OF phase_bfs_axiom bfs_state_valid]
    by (simp add: copy_level_def)
qed

lemma copies_graph_layered: "idfs.Graph.layered_graph_input copies_graph level"
proof-
  have "layered_dgraph (idfs.Graph.digraph_abs copies_graph)
          (phase_bfs.copies_lev bfs_sources matching_graph non_matching_graph)"
    using phase_bfs.valid_DAG_layered[OF phase_bfs_axiom bfs_state_valid_impl]
    by (simp only: copies_graph_abs)
  hence "layered_dgraph (idfs.Graph.digraph_abs copies_graph) level"
    by (intro layered_dgraph_cong[OF copies_graph_level[symmetric]])
  thus ?thesis
    by (auto intro!: idfs.Graph.layered_graph_inputI simp: idfs.Graph.from_list_correct(2,3,5))
qed

lemma visited_odd_inv: "vset_inv (visited_odd bfs_state)"
  by (rule phase_bfs.valid_alt_BFS_DAG_impl_props(3)[OF phase_bfs_axiom bfs_state_valid_impl])

lemma copy_roots_free_odd:
  "set copy_roots \<subseteq> Vtx Odd ` (Tree2.set_tree bfs_sources \<inter> Tree2.set_tree (visited_odd bfs_state))"
  using set.set_isin[OF visited_odd_inv]
  by (auto simp: phase_roots_def bfs_sources_props(2) split: if_splits)

lemma copy_roots_in_graph: "set copy_roots \<subseteq> dVs (idfs.Graph.digraph_abs copies_graph)"
proof
  fix w
  assume "w \<in> set copy_roots"
  then obtain t where "w = Vtx Odd t" "t \<in> Tree2.set_tree (visited_odd bfs_state)"
    using copy_roots_free_odd
    by auto
  thus "w \<in> dVs (idfs.Graph.digraph_abs copies_graph)"
    using phase_bfs.VisO_copies_dVs[OF phase_bfs_axiom bfs_state_valid]
    by (simp only: copies_graph_abs)
qed

lemma copy_roots_nonempty:
  "filter (\<lambda>t. isin (visited_odd bfs_state) t) (free_vertices nil vs m) \<noteq> [] \<Longrightarrow> copy_roots \<noteq> []"
proof(cases "filter (\<lambda>t. isin (visited_odd bfs_state) t) (free_vertices nil vs m)")
  case (Cons t0 ts)
  let ?L = "\<lambda>t. copy_level (distances bfs_state) (Vtx Odd t)"
  have "fold min (map ?L ts) (?L t0) \<in> ?L ` set (t0 # ts)"
    using fold_min_mem[of "map ?L ts" "?L t0"]
    by auto
  thus ?thesis
    using Cons
    by (auto simp: phase_roots_def filter_empty_conv)
qed simp

lemma dVs_copies_graph:
  "dVs (idfs.Graph.digraph_abs copies_graph) = set (map fst copies_edge_list @ map snd copies_edge_list)"
  by (simp add: dVs_eq image_Un)

lemma blocked_copies_props:
  "vset_inv (blocked p)"
  "Tree2.set_tree (blocked p) \<subseteq> dVs (idfs.Graph.digraph_abs copies_graph)"
  "\<lbrakk>w \<in> dVs (idfs.Graph.digraph_abs copies_graph); vtx w \<in> vtx ` set p\<rbrakk> \<Longrightarrow> w \<in> Tree2.set_tree (blocked p)"
proof-
  show "vset_inv (blocked p)" "Tree2.set_tree (blocked p) \<subseteq> dVs (idfs.Graph.digraph_abs copies_graph)"
    by (auto simp: blocked_copies_def dVs_copies_graph)
  show "w \<in> Tree2.set_tree (blocked p)"
    if "w \<in> dVs (idfs.Graph.digraph_abs copies_graph)" "vtx w \<in> vtx ` set p"
    using that
    by (cases w; cases "label w") (auto simp: blocked_copies_def dVs_copies_graph dVs_eq)
qed

text \<open>The search at this phase, with its proofs locale.\<close>

interpretation phase_search_proofs: Disjoint_Paths_Search_thms
  where insert = vset_insert and sel = sel and vset_empty = vset_empty
    and diff = vset_diff and lookup = lookup and empty = map_empty
    and delete = RBT_Map.delete and isin = isin and t_set = t_set
    and update = update and adjmap_inv = adj_inv
    and vset_delete = vset_delete and vset_inv = vset_inv
    and union = vset_union and inter = vset_inter
    and G = copies_graph and target = "\<lambda>w. level w = 0" and blocked = blocked
    and initial_roots = copy_roots
    and search_step = "\<lambda>avoid r vis. IDFS_impl_rbt copies_graph (\<lambda>w. level w = 0) avoid [r] vis"
  using phase_search.Disjoint_Paths_Search_axioms copies_graph_layered copy_roots_in_graph
        blocked_copies_props(1,2)
  by (auto intro!: Disjoint_Paths_Search_thms.intro Disjoint_Paths_Search_thms_axioms.intro
           simp: phase_search.Disjoint_Paths_Search_axiom_def)

lemmas phase_search_correct_1 =
  phase_search_proofs.Disjoint_Paths_Search_correct_1[folded disjoint_paths_search_initial_state_def]

lemmas phase_search_correct_2 =
  phase_search_proofs.Disjoint_Paths_Search_correct_2[folded disjoint_paths_search_initial_state_def]

lemmas phase_search_correct_3 =
  phase_search_proofs.Disjoint_Paths_Search_correct_3[folded disjoint_paths_search_initial_state_def]

lemma hopcroft_karp_phase_unfold:
  "hopcroft_karp_phase nil edge_list vs m = map (map vtx) (paths search_state)"
  using m_free
  by (simp add: hopcroft_karp_phase_def phase_search.Disjoint_Paths_Search_run_impl_def
                phase_search_proofs.Disjoint_Paths_Search_impl_to_Disjoint_Paths_Search[
                  folded disjoint_paths_search_impl_rbt_def disjoint_paths_search_initial_state_def])

text \<open>A path of the phase is the projection of a walk of the copies graph from a free odd copy
  down to level 0, hence an augmenting path (Alt_BFS_Bipartite).\<close>

lemma phase_paths_augmenting:
  "P \<in> set (hopcroft_karp_phase nil edge_list vs m) \<Longrightarrow>
   graph_augmenting_path (ugraph_abs_rbt Gin) (mate_matching nil m) P"
proof-
  assume "P \<in> set (hopcroft_karp_phase nil edge_list vs m)"
  then obtain q where "q \<in> set (paths search_state)" "P = map vtx q"
    by (auto simp: hopcroft_karp_phase_unfold)
  note q = phase_search_correct_1[OF this(1)]
  then obtain t where "last q = Vtx Odd t" "t \<in> Tree2.set_tree bfs_sources"
    using copy_roots_free_odd
    by blast
  moreover have "Vwalk.vwalk_bet (idfs.Graph.digraph_abs copies_graph) (last q) (rev q) (hd q)"
    using q
    by (auto intro: found_vwalk_bet)
  moreover hence "phase_bfs.copies_lev bfs_sources matching_graph non_matching_graph (hd q) = 0"
    using q copies_graph_level[OF vwalk_bet_endpoints(2)]
    by simp
  ultimately have "graph_augmenting_path (ugraph_abs_rbt Gin) (mate_matching nil m) (rev (map vtx (rev q)))"
    by (intro phase_bfs.copies_walk_augmenting(1)[OF phase_bfs_axiom bipartite_matching_input_phase
                                                      bfs_state_valid])
       (simp_all only: copies_graph_abs)
  thus "graph_augmenting_path (ugraph_abs_rbt Gin) (mate_matching nil m) P"
    using \<open>P = map vtx q\<close>
    by (simp add: rev_map)
qed

lemma phase_paths_disjoint: "sorted_wrt (\<lambda>P Q. set P \<inter> set Q = {}) (hopcroft_karp_phase nil edge_list vs m)"
proof-
  have "set q \<subseteq> dVs (idfs.Graph.digraph_abs copies_graph)" if "q \<in> set (paths search_state)" for q
  proof-
    have "Vwalk.vwalk_bet (idfs.Graph.digraph_abs copies_graph) (last q) (rev q) (hd q)"
      using phase_search_correct_1[OF that]
      by (auto intro: found_vwalk_bet)
    hence "set (rev q) \<subseteq> dVs (idfs.Graph.digraph_abs copies_graph)"
      by (rule vwalk_bet_in_dVs)
    thus ?thesis
      by simp
  qed
  hence "sorted_wrt (\<lambda>q p. set (map vtx q) \<inter> set (map vtx p) = {}) (paths search_state)"
    using blocked_copies_props(3)
    by (intro sorted_wrt_mono_rel[OF _ phase_search_correct_2]) force
  thus ?thesis
    by (simp add: hopcroft_karp_phase_unfold sorted_wrt_map)
qed

text \<open>If an augmenting path exists, some free vertex has an odd copy in the copies graph; then
  the roots are not empty, every root reaches level 0, and the search finds a path.\<close>

lemma phase_paths_nonempty:
  "\<exists>P. graph_augmenting_path (ugraph_abs_rbt Gin) (mate_matching nil m) P \<Longrightarrow>
   hopcroft_karp_phase nil edge_list vs m \<noteq> []"
proof-
  assume "\<exists>P. graph_augmenting_path (ugraph_abs_rbt Gin) (mate_matching nil m) P"
  then obtain t where "t \<in> Tree2.set_tree bfs_sources"
      "Vtx Odd t \<in> dVs (phase_bfs.copies_dag matching_graph non_matching_graph (G.digraph_abs bfs_dag))"
    using phase_bfs.augmenting_path_iff_free_odd_copy[OF phase_bfs_axiom bipartite_matching_input_phase
                                                         bfs_state_valid]
    by blast
  moreover hence "t \<in> Tree2.set_tree (visited_odd bfs_state)"
    using phase_bfs.copies_dag_dVs[OF phase_bfs_axiom bfs_state_valid]
    by blast
  ultimately have "copy_roots \<noteq> []"
    using set.set_isin[OF visited_odd_inv]
    by (auto intro!: copy_roots_nonempty simp: bfs_sources_props(2) filter_empty_conv)
  then obtain r where "r \<in> set copy_roots"
    by (cases copy_roots) auto
  moreover hence "r \<in> dVs (phase_bfs.copies_dag matching_graph non_matching_graph (G.digraph_abs bfs_dag))"
    by (rule subsetD[OF copy_roots_in_graph[unfolded copies_graph_abs]])
  then obtain q z where "Vwalk.vwalk_bet (phase_bfs.copies_dag matching_graph non_matching_graph (G.digraph_abs bfs_dag)) r q z"
                        "phase_bfs.copies_lev bfs_sources matching_graph non_matching_graph z = 0"
    by (elim phase_bfs.copies_reach_zero[OF phase_bfs_axiom bfs_state_valid])
  hence "Vwalk.vwalk_bet (idfs.Graph.digraph_abs copies_graph) r q z"
    by (simp only: copies_graph_abs)
  moreover hence "level z = 0"
    using copies_graph_level[OF vwalk_bet_endpoints(2)] \<open>phase_bfs.copies_lev bfs_sources matching_graph non_matching_graph z = 0\<close>
    by simp
  ultimately show ?thesis
    using phase_search_correct_3[OF \<open>r \<in> set copy_roots\<close>]
    by (simp add: hopcroft_karp_phase_unfold)
qed

end

lemma free_vertices_nonempty:
  "\<lbrakk>mate_invar nil (ugraph_abs_rbt Gin) m;
    \<exists>P. graph_augmenting_path (ugraph_abs_rbt Gin) (mate_matching nil m) P\<rbrakk>
   \<Longrightarrow> free_vertices nil vs m \<noteq> []"
proof-
  assume inv: "mate_invar nil (ugraph_abs_rbt Gin) m"
    and "\<exists>P. graph_augmenting_path (ugraph_abs_rbt Gin) (mate_matching nil m) P"
  then obtain P where aug: "graph_augmenting_path (ugraph_abs_rbt Gin) (mate_matching nil m) P"
    by blast
  have path: "path (ugraph_abs_rbt Gin) P" and nonempty: "P \<noteq> []"
    and free: "hd P \<notin> Vs (mate_matching nil m)"
    using aug by (auto simp: matching_augmenting_path_def)
  have "hd P \<in> set vs"
    using mem_path_Vs[OF path hd_in_set[OF nonempty]] by simp
  moreover have "mate_get nil m (hd P) = nil"
    using free by (simp add: mate_Vs_iff[OF inv])
  ultimately have "hd P \<in> set (free_vertices nil vs m)"
    by (simp add: free_vertices_def)
  thus ?thesis by auto
qed

end
=======
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
>>>>>>> main

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
<<<<<<< HEAD
  "\<lbrakk>hopcroft_karp_axiom_rbt G vs; mate_invar nil (ugraph_abs_rbt G) M;
    p \<in> set (hopcroft_karp_phase nil (adjacency_edges G vs) vs M)\<rbrakk>
   \<Longrightarrow> graph_augmenting_path (ugraph_abs_rbt G) (mate_matching nil M) p"
proof-
  assume "hopcroft_karp_axiom_rbt G vs" "mate_invar nil (ugraph_abs_rbt G) M"
         "p \<in> set (hopcroft_karp_phase nil (adjacency_edges G vs) vs M)"
  moreover hence "free_vertices nil vs M \<noteq> []"
    by (auto simp: hopcroft_karp_phase_no_free)
  moreover obtain X Y where "bipartite (ugraph_abs_rbt G) X Y"
    using bipartite_of_axiom \<open>hopcroft_karp_axiom_rbt G vs\<close>
    by blast
  ultimately show ?thesis
    using phase_paths_augmenting
    by blast
qed

lemma phase_disjoint:
  "\<lbrakk>hopcroft_karp_axiom_rbt G vs; mate_invar nil (ugraph_abs_rbt G) M\<rbrakk>
   \<Longrightarrow> sorted_wrt (\<lambda>p q. set p \<inter> set q = {}) (hopcroft_karp_phase nil (adjacency_edges G vs) vs M)"
proof-
  assume "hopcroft_karp_axiom_rbt G vs" "mate_invar nil (ugraph_abs_rbt G) M"
  moreover obtain X Y where "bipartite (ugraph_abs_rbt G) X Y"
    using bipartite_of_axiom \<open>hopcroft_karp_axiom_rbt G vs\<close>
    by blast
  ultimately show ?thesis
    using phase_paths_disjoint
    by (cases "free_vertices nil vs M = []") (simp_all add: hopcroft_karp_phase_no_free)
qed

lemma phase_complete:
  "\<lbrakk>hopcroft_karp_axiom_rbt G vs; mate_invar nil (ugraph_abs_rbt G) M;
    \<exists>p. graph_augmenting_path (ugraph_abs_rbt G) (mate_matching nil M) p\<rbrakk>
   \<Longrightarrow> hopcroft_karp_phase nil (adjacency_edges G vs) vs M \<noteq> []"
proof-
  assume "hopcroft_karp_axiom_rbt G vs" "mate_invar nil (ugraph_abs_rbt G) M"
         "\<exists>p. graph_augmenting_path (ugraph_abs_rbt G) (mate_matching nil M) p"
  moreover obtain X Y where "bipartite (ugraph_abs_rbt G) X Y"
    using bipartite_of_axiom \<open>hopcroft_karp_axiom_rbt G vs\<close>
    by blast
  ultimately show ?thesis
    using free_vertices_nonempty phase_paths_nonempty
    by blast
=======
  assumes "hopcroft_karp_axiom_rbt G vs" "mate_invar (ugraph_abs_rbt G) M"
    "p \<in> set (hopcroft_karp_phase (adjacency_edges G vs) vs M)"
  shows "graph_augmenting_path (ugraph_abs_rbt G) (mate_matching M) p"
proof -
  obtain X Y where "bipartite (ugraph_abs_rbt G) X Y"
    using bipartite_of_axiom[OF assms(1)] by blast
  then show ?thesis
    using phase.phase_sound[OF _ _ adjacency_edges_set[OF assms(1)]] assms
    unfolding ugraph_abs_rbt_def hopcroft_karp_axiom_rbt_def by blast
qed

lemma phase_disjoint:
  assumes "hopcroft_karp_axiom_rbt G vs" "mate_invar (ugraph_abs_rbt G) M"
  shows "sorted_wrt (\<lambda>p q. set p \<inter> set q = {}) (hopcroft_karp_phase (adjacency_edges G vs) vs M)"
proof -
  obtain X Y where "bipartite (ugraph_abs_rbt G) X Y"
    using bipartite_of_axiom[OF assms(1)] by blast
  then show ?thesis
    using phase.phase_disjoint[OF _ _ adjacency_edges_set[OF assms(1)]] assms
    unfolding ugraph_abs_rbt_def hopcroft_karp_axiom_rbt_def by blast
qed

lemma phase_complete:
  assumes "hopcroft_karp_axiom_rbt G vs" "mate_invar (ugraph_abs_rbt G) M"
    "\<exists>p. graph_augmenting_path (ugraph_abs_rbt G) (mate_matching M) p"
  shows "hopcroft_karp_phase (adjacency_edges G vs) vs M \<noteq> []"
proof -
  obtain X Y where "bipartite (ugraph_abs_rbt G) X Y"
    using bipartite_of_axiom[OF assms(1)] by blast
  then show ?thesis
    using phase.phase_complete[OF _ _ adjacency_edges_set[OF assms(1)]] assms
    unfolding ugraph_abs_rbt_def hopcroft_karp_axiom_rbt_def by blast
>>>>>>> main
qed

lemmas phase = phase_sound phase_disjoint phase_complete

end
