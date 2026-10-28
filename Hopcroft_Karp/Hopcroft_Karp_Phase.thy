theory Hopcroft_Karp_Phase
  imports Hopcroft_Karp_Top_Loop Disjoint_Paths_Search Alt_BFS_Bipartite Micali_Vazirani.IDFS
          "Basic_Matching.Matching_Augmentation_Executable"
begin

section \<open>The Phase of the Hopcroft-Karp Algorithm\<close>

text \<open>One phase of the Hopcroft-Karp algorithm, over abstract operations: the input graph and
  the vertex sets of the alternating BFS (@{locale Pair_Graph_Specs} and @{locale Set2}), the
  graph of copies and its vertex sets searched by the incremental DFS (a second instance), the
  map of distances of the BFS, and the matching, represented by its mate function
  (@{locale Matching_Augmentation_Specs}). The BFS sub-operations are parameters as well; they
  are assumed to meet the specification of @{locale Alt_BFS.BFS} for all sources and graphs. The
  phase meets the contract of the top loop (@{locale Hopcroft_Karp_Loop}).\<close>

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

lemma finite_neighbourhood_of_finite:
  "finite E \<Longrightarrow> finite (Pair_Graph.neighbourhood E u)"
  unfolding Pair_Graph.neighbourhood_def
  by (rule finite_subset[where B = "snd ` E"]) (auto intro: rev_image_eqI)


subsection \<open>The locale\<close>

locale Hopcroft_Karp_Phase =
  G: Pair_Graph_Specs where lookup = lookup +
  set_ops: Set2 vset_empty vset_delete _ t_set vset_inv insert +
  CGraph: Pair_Graph_Specs where empty = c_empty and delete = c_delete and lookup = c_lookup
    and insert = c_insert and isin = c_isin and t_set = c_t_set and sel = c_sel
    and update = c_update and adjmap_inv = c_adjmap_inv and vset_empty = c_vset_empty
    and vset_delete = c_vset_delete and vset_inv = c_vset_inv +
  c_set_ops: Set2 c_vset_empty c_vset_delete c_isin c_t_set c_vset_inv c_insert c_union c_inter
    c_diff +
  mate: Matching_Augmentation_Specs mate_empty mate_update mate_delete mate_lookup mate_map_invar
  for lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option"
  and c_empty c_delete and c_lookup :: "'cadjmap \<Rightarrow> 'v labelled_vtx \<Rightarrow> 'cvset option"
  and c_insert c_isin c_t_set c_sel c_update c_adjmap_inv c_vset_empty c_vset_delete c_vset_inv
    c_union c_inter c_diff
  and mate_empty mate_update mate_delete and mate_lookup :: "'mate \<Rightarrow> 'v \<Rightarrow> 'v option"
  and mate_map_invar +
  fixes lookup_dist :: "'dmap \<Rightarrow> 'v labelled_vtx \<Rightarrow> enat option"
    and empty_dist update_dist delete_dist invar_dist
    and expand_tree :: "'adjmap \<Rightarrow> 'adjmap \<Rightarrow> 'vset \<Rightarrow> 'vset \<Rightarrow> 'adjmap"
    and next_frontier_impl :: "'adjmap \<Rightarrow> 'vset \<Rightarrow> 'vset \<Rightarrow> 'vset"
    and upd_dists :: "parity \<Rightarrow> 'adjmap \<Rightarrow> 'dmap \<Rightarrow> 'vset \<Rightarrow> 'vset \<Rightarrow> 'dmap"
    and init_dists_of :: "'vset \<Rightarrow> 'dmap"
  assumes BFS: "\<And>srcs.
    Alt_BFS.BFS empty delete insert isin t_set sel update adjmap_inv vset_empty vset_delete vset_inv
      union inter diff lookup lookup_dist empty_dist update_dist delete_dist invar_dist srcs
      expand_tree next_frontier_impl upd_dists (init_dists_of srcs)"
begin

text \<open>The alternating BFS, for arbitrary sources and graphs.\<close>

sublocale phase_bfs: Alt_BFS.BFS
  where lookup_neighb = lookup and lookup_dist = lookup_dist and empty_dist = empty_dist
    and update_dist = update_dist and delete_dist = delete_dist and invar_dist = invar_dist
    and srcs = srcs and matching = matching and unmatching = unmatching
    and expand_tree = expand_tree and next_frontier_impl = next_frontier_impl
    and upd_dists = upd_dists and init_dists = "init_dists_of srcs"
  for srcs matching unmatching
  by (rule BFS)

subsection \<open>The matching, represented by its mate function\<close>

sublocale mate_thms: matching_augmentation mate_empty mate_update mate_delete mate_lookup mate_map_invar
  by unfold_locales

abbreviation "mate_invar \<equiv> mate.invar_matching"
abbreviation "mate_matching \<equiv> mate.\<M>"
abbreviation "mate_augment \<equiv> mate.augment_impl"

lemmas mate_augmentation_correct = mate_thms.augmentation_correct
lemmas mate_empty_props = mate_thms.empty_matching_props
lemmas mate_invarD = mate.invar_matchingD
lemmas mate_matching_eq = mate.\<M>_def'

lemma mate_matching_iff:
  "mate_invar G m \<Longrightarrow> {u, v} \<in> mate_matching m \<longleftrightarrow> mate_lookup m u = Some v"
  by (auto simp: mate_matching_eq doubleton_eq_iff dest: mate_invarD(2) mate.symmetric_buddiesD)

lemma mate_Vs_iff:
  "mate_invar G m \<Longrightarrow> v \<in> Vs (mate_matching m) \<longleftrightarrow> mate_lookup m v \<noteq> None"
  by (auto simp: Vs_def mate_matching_eq dest: mate_invarD(2) mate.symmetric_buddiesD)

subsection \<open>The input\<close>

sublocale hk_input: Hopcroft_Karp_Input
  where lookup = lookup and G = Gr and vertex_list = vs
  for Gr vs
  by unfold_locales

subsection \<open>Builders\<close>

definition "matched_edges edges m = filter (\<lambda>(u, v). mate_lookup m u = Some v) edges"

definition "unmatched_edges edges m = filter (\<lambda>(u, v). mate_lookup m u \<noteq> Some v) edges"

definition "free_vertices vs m = filter (\<lambda>v. mate_lookup m v = None) vs"

definition "free_vertex_set vs m = foldr insert (free_vertices vs m) vset_empty"

definition "copies_edges edges m dag =
  concat (map (\<lambda>(u, v).
     if isin (G.neighbourhood dag u) v
     then (if mate_lookup m u = Some v then [(Vtx Even v, Vtx Odd u)] else [(Vtx Odd v, Vtx Even u)])
     else []) edges)"

definition "copy_level dists w = the_enat (the (lookup_dist dists w))"

definition "phase_roots vs m odd_visited dists =
  (let free_odd = filter (\<lambda>t. isin odd_visited t) (free_vertices vs m) in
   if free_odd = [] then [] else
   let k = fold min (map (\<lambda>t. copy_level dists (Vtx Odd t)) (tl free_odd))
                    (copy_level dists (Vtx Odd (hd free_odd)))
   in map (Vtx Odd) (filter (\<lambda>t. copy_level dists (Vtx Odd t) = k) free_odd))"

definition "c_vset_of_list xs = foldr c_insert xs c_vset_empty"

definition "blocked_copies copies p =
  c_vset_of_list
    (filter (\<lambda>w. w \<in> set copies) (concat (map (\<lambda>w. [Vtx Even (vtx w), Vtx Odd (vtx w)]) p)))"

definition "IDFS_stack0_c avoid vis p =
  (if p \<noteq> [] \<and> (c_isin avoid (hd p) \<or> c_isin vis (hd p)) then tl p else p)"

definition "IDFS_impl_c CG P avoid p vis =
  (let state = DFS_avoid.avoid_final_state_impl c_insert c_isin c_sel c_vset_empty c_union c_diff
                 c_lookup CG (IDFS_stack0_c avoid vis p) vis avoid P
   in (DFS_avoid_state.ret state, DFS_avoid_state.visited state))"

lemma c_vset_of_list_props[simp]:
  "c_vset_inv (c_vset_of_list xs)" "c_t_set (c_vset_of_list xs) = set xs"
  by (induction xs)
     (simp_all add: c_vset_of_list_def CGraph.vset.set.invar_empty CGraph.vset.set.set_empty
                    CGraph.vset.set.invar_insert CGraph.vset.set.set_insert)

lemma foldr_insert_props[simp]:
  "vset_inv (foldr insert xs vset_empty)" "t_set (foldr insert xs vset_empty) = set xs"
  by (induction xs)
     (simp_all add: G.vset.set.invar_empty G.vset.set.set_empty G.vset.set.invar_insert
                    G.vset.set.set_insert)

subsection \<open>The incremental DFS meets the contract of the search step\<close>

context
  fixes CG lev
  assumes layered: "CGraph.layered_graph_input CG lev"
begin

interpretation idfs_witness: IDFS_witness
  where empty = c_empty and delete = c_delete and insert = c_insert and isin = c_isin
    and t_set = c_t_set and sel = c_sel and update = c_update and adjmap_inv = c_adjmap_inv
    and vset_empty = c_vset_empty and vset_delete = c_vset_delete and vset_inv = c_vset_inv
    and union = c_union and inter = c_inter and diff = c_diff and lookup = c_lookup
    and G = CG and lev = lev
proof(intro IDFS.IDFS_witness.intro IDFS.IDFS_witness_axioms.intro, goal_cases)
  case 1
  show ?case
    by (rule CGraph.Pair_Graph_Specs_axioms)
next
  case 2
  show ?case
    by (rule c_set_ops.Set2_axioms)
next
  case 3
  show ?case
    by (rule layered)
qed

lemma IDFS_impl_c_eq: "IDFS_impl_c CG = idfs_witness.IDFS_impl"
  by (intro ext)
     (simp add: IDFS_impl_c_def IDFS_stack0_c_def idfs_witness.IDFS_impl_def
                idfs_witness.IDFS_stack0_def)

lemma search_step:
  assumes "c_vset_inv avoid" "c_vset_inv vis" "c_t_set avoid \<subseteq> dVs (CGraph.digraph_abs CG)"
          "c_t_set vis \<subseteq> dVs (CGraph.digraph_abs CG)" "r \<in> dVs (CGraph.digraph_abs CG)"
  shows "IDFS_impl_c CG P avoid [r] vis = (res, vis') \<Longrightarrow> c_vset_inv vis'"
        "IDFS_impl_c CG P avoid [r] vis = (res, vis') \<Longrightarrow>
           c_t_set vis' \<subseteq> dVs (CGraph.digraph_abs CG)"
        "IDFS_impl_c CG P avoid [r] vis = (res, vis') \<Longrightarrow> c_t_set vis \<subseteq> c_t_set vis'"
        "\<lbrakk>IDFS_impl_c CG P avoid [r] vis = (None, vis'); r \<notin> c_t_set avoid\<rbrakk>
         \<Longrightarrow> r \<in> c_t_set vis'"
        "\<lbrakk>IDFS_impl_c CG P avoid [r] vis = (None, vis'); v \<in> c_t_set vis' - c_t_set vis;
          (v, w) \<in> CGraph.digraph_abs CG\<rbrakk>
         \<Longrightarrow> w \<in> c_t_set avoid \<union> c_t_set vis'"
        "\<lbrakk>IDFS_impl_c CG P avoid [r] vis = (res, vis'); v \<in> c_t_set vis' - c_t_set vis\<rbrakk>
         \<Longrightarrow> \<not> P v"
        "IDFS_impl_c CG P avoid [r] vis = (Some p, vis') \<Longrightarrow>
           Vwalk.vwalk (CGraph.digraph_abs CG) (rev p) \<and> p \<noteq> [] \<and> distinct p \<and> P (hd p) \<and>
           last p = r \<and> set p \<inter> (c_t_set avoid \<union> c_t_set vis') = {}"
proof-
  have "dpath (CGraph.digraph_abs CG) (rev [r])" "distinct [r]"
    using assms(5)
    by (auto intro: vwalk1)
  note pre = this assms(1-4)
  show "c_vset_inv vis'" if "IDFS_impl_c CG P avoid [r] vis = (res, vis')"
    by (rule idfs_witness.IDFS_vis_works_4[OF pre that[unfolded IDFS_impl_c_eq]])
  show "c_t_set vis' \<subseteq> dVs (CGraph.digraph_abs CG)"
    if "IDFS_impl_c CG P avoid [r] vis = (res, vis')"
    by (rule idfs_witness.IDFS_dVs_bound[OF pre that[unfolded IDFS_impl_c_eq]])
  show "c_t_set vis \<subseteq> c_t_set vis'" if "IDFS_impl_c CG P avoid [r] vis = (res, vis')"
    by (rule idfs_witness.IDFS_vis_works_3[OF pre that[unfolded IDFS_impl_c_eq]])
  show "r \<in> c_t_set vis'" if "IDFS_impl_c CG P avoid [r] vis = (None, vis')" "r \<notin> c_t_set avoid"
    using idfs_witness.IDFS_complete_w[OF pre, where P = P and vis' = vis']
          that[unfolded IDFS_impl_c_eq]
    by auto
  show "w \<in> c_t_set avoid \<union> c_t_set vis'"
    if "IDFS_impl_c CG P avoid [r] vis = (None, vis')" "v \<in> c_t_set vis' - c_t_set vis"
       "(v, w) \<in> CGraph.digraph_abs CG"
    using idfs_witness.IDFS_closed_None[OF pre, where P = P and vis' = vis' and v = v and w = w]
          that[unfolded IDFS_impl_c_eq]
    by auto
  show "\<not> P v" if "IDFS_impl_c CG P avoid [r] vis = (res, vis')" "v \<in> c_t_set vis' - c_t_set vis"
    using that(2)
    by (rule idfs_witness.IDFS_vis_works_1[OF pre that(1)[unfolded IDFS_impl_c_eq]])
  show "Vwalk.vwalk (CGraph.digraph_abs CG) (rev p) \<and> p \<noteq> [] \<and> distinct p \<and> P (hd p) \<and>
          last p = r \<and> set p \<inter> (c_t_set avoid \<union> c_t_set vis') = {}"
    if "IDFS_impl_c CG P avoid [r] vis = (Some p, vis')"
    using idfs_witness.IDFS_sound_1[OF pre, where P = P and vis' = vis' and p' = p]
          idfs_witness.IDFS_sound_2[OF pre, where P = P and vis' = vis' and p' = p]
          idfs_witness.IDFS_sound_3[OF pre, where P = P and vis' = vis' and p' = p]
          idfs_witness.IDFS_sound_6[OF pre, where P = P and vis' = vis' and p' = p]
          idfs_witness.IDFS_sound_7[OF pre, where P = P and vis' = vis' and p' = p]
          idfs_witness.IDFS_sound_8[OF pre, where P = P and vis' = vis' and p' = p]
          that[unfolded IDFS_impl_c_eq]
    by auto
qed

end

subsection \<open>The disjoint-paths search\<close>

sublocale phase_search: Disjoint_Paths_Search
  where empty = c_empty and delete = c_delete and insert = c_insert and isin = c_isin
    and t_set = c_t_set and sel = c_sel and update = c_update and adjmap_inv = c_adjmap_inv
    and vset_empty = c_vset_empty and vset_delete = c_vset_delete and vset_inv = c_vset_inv
    and union = c_union and inter = c_inter and diff = c_diff and lookup = c_lookup
    and G = CG and target = P and blocked = blk and initial_roots = rs
    and search_step = "\<lambda>avoid r vis. IDFS_impl_c CG P avoid [r] vis"
  for CG P blk rs
proof(intro Disjoint_Paths_Search.intro Disjoint_Paths_Search_axioms.intro, goal_cases)
  case 1
  show ?case
    by (rule CGraph.Pair_Graph_Specs_axioms)
next
  case 2
  show ?case
    by (rule c_set_ops.Set2_axioms)
qed (fact search_step)+

subsection \<open>The phase\<close>

definition "hopcroft_karp_phase edges vs m =
  (if free_vertices vs m = [] then [] else
   let matching_graph = G.from_list (matched_edges edges m);
       non_matching_graph = G.from_list (unmatched_edges edges m);
       bfs_state = phase_bfs.BFS_impl matching_graph non_matching_graph
                     (phase_bfs.initial_state (free_vertex_set vs m));
       copies_edge_list = copies_edges edges m (Alt_BFS.BFS_state.parents bfs_state);
       copies_graph = CGraph.from_list copies_edge_list;
       level = copy_level (distances bfs_state)
   in map (map vtx)
        (paths (phase_search.Disjoint_Paths_Search_run_impl
                  (blocked_copies (map fst copies_edge_list @ map snd copies_edge_list))
                  (phase_roots vs m (visited_odd bfs_state) (distances bfs_state))
                  copies_graph (\<lambda>w. level w = 0))))"

lemma hopcroft_karp_phase_no_free:
  "free_vertices vs m = [] \<Longrightarrow> hopcroft_karp_phase edges vs m = []"
  by (simp add: hopcroft_karp_phase_def)

subsection \<open>The input graph\<close>

context
  fixes Gin vs edges X Y
  assumes input: "hk_input.Hopcroft_Karp_axiom Gin vs" "bipartite (hk_input.ugraph_abs Gin) X Y"
    and edges: "set edges = G.digraph_abs Gin"
  notes edges_set[simp] = edges
begin

lemma input_props[simp]:
  "G.graph_inv Gin" "G.finite_graph Gin" "G.finite_vsets Gin"
  "(u, u) \<notin> G.digraph_abs Gin" "set vs = dVs (G.digraph_abs Gin)"
  using input(1)
  by (auto simp: hk_input.Hopcroft_Karp_axiom_def)

lemma input_sym: "(u, v) \<in> G.digraph_abs Gin \<Longrightarrow> (v, u) \<in> G.digraph_abs Gin"
  using input(1)
  by (auto simp: hk_input.Hopcroft_Karp_axiom_def)


lemma ugraph_abs_edge_iff[simp]:
  "{u, v} \<in> hk_input.ugraph_abs Gin \<longleftrightarrow> (u, v) \<in> G.digraph_abs Gin"
  by (auto simp: hk_input.ugraph_abs_def doubleton_eq_iff dest: input_sym)

lemma Vs_ugraph_abs[simp]: "Vs (hk_input.ugraph_abs Gin) = set vs"
  by (auto simp: hk_input.ugraph_abs_def Vs_def dVs_def)

lemma ugraph_abs_graph_invar: "graph_invar (hk_input.ugraph_abs Gin)"
proof-
  have "u \<noteq> v" if "(u, v) \<in> G.digraph_abs Gin" for u v
    using that input_props(4)
    by auto
  hence "dblton_graph (hk_input.ugraph_abs Gin)"
    unfolding dblton_graph_def hk_input.ugraph_abs_def
    by blast
  thus ?thesis
    using finite_set[of vs]
    by simp
qed

subsection \<open>One phase, for a fixed matching\<close>

context
  fixes m
  assumes m_invar: "mate_invar (hk_input.ugraph_abs Gin) m" and m_free: "free_vertices vs m \<noteq> []"
begin

abbreviation "matching_graph \<equiv> G.from_list (matched_edges edges m)"
abbreviation "non_matching_graph \<equiv> G.from_list (unmatched_edges edges m)"
abbreviation "bfs_sources \<equiv> free_vertex_set vs m"
abbreviation "bfs_state \<equiv> phase_bfs.BFS_impl matching_graph non_matching_graph (phase_bfs.initial_state bfs_sources)"
abbreviation "bfs_dag \<equiv> Alt_BFS.BFS_state.parents bfs_state"
abbreviation "copies_edge_list \<equiv> copies_edges edges m bfs_dag"
abbreviation "copies_graph \<equiv> CGraph.from_list copies_edge_list"
abbreviation "level \<equiv> copy_level (distances bfs_state)"
abbreviation "copy_roots \<equiv> phase_roots vs m (visited_odd bfs_state) (distances bfs_state)"
abbreviation "blocked \<equiv> blocked_copies (map fst copies_edge_list @ map snd copies_edge_list)"
abbreviation "search_state \<equiv>
  phase_search.Disjoint_Paths_Search blocked copies_graph (\<lambda>w. level w = 0)
    (phase_search.initial_state copy_roots)"

lemma mate_matching_subset: "mate_matching m \<subseteq> hk_input.ugraph_abs Gin"
  using mate_invarD(4)[OF m_invar]
  by auto

lemma matching_graph_abs: "G.digraph_abs matching_graph = {(u, v). {u, v} \<in> mate_matching m}"
proof-
  have "(u, v) \<in> G.digraph_abs Gin" if "mate_lookup m u = Some v" for u v
    using mate_matching_subset that mate_matching_iff[OF m_invar, of u v]
    by auto
  thus ?thesis
    by (auto simp: matched_edges_def mate_matching_iff[OF m_invar])
qed

lemma non_matching_graph_abs:
  "G.digraph_abs non_matching_graph = {(u, v). {u, v} \<in> hk_input.ugraph_abs Gin - mate_matching m}"
  by (auto simp: unmatched_edges_def mate_matching_iff[OF m_invar])

lemma bfs_sources_props:
  "vset_inv bfs_sources" "t_set bfs_sources = set (free_vertices vs m)"
  "t_set bfs_sources = Vs (hk_input.ugraph_abs Gin) - Vs (mate_matching m)"
  by (auto simp: free_vertex_set_def free_vertices_def mate_Vs_iff[OF m_invar])

lemma bfs_sources_in_graph: "t_set bfs_sources \<subseteq> dVs (G.digraph_abs non_matching_graph)"
proof
  fix v
  assume "v \<in> t_set bfs_sources"
  then obtain w where "(v, w) \<in> G.digraph_abs Gin" "mate_lookup m v = None"
    by (auto simp: bfs_sources_props(2) free_vertices_def dVs_eq dest: input_sym)
  thus "v \<in> dVs (G.digraph_abs non_matching_graph)"
    unfolding non_matching_graph_abs
    by (auto simp: mate_matching_iff[OF m_invar])
qed

lemma phase_bfs_axiom:
  "phase_bfs.BFS_axiom bfs_sources matching_graph non_matching_graph"
proof-
  have "finite (G.digraph_abs matching_graph)" "finite (G.digraph_abs non_matching_graph)"
    by simp_all
  hence "\<forall>u. finite (Pair_Graph.neighbourhood (G.digraph_abs matching_graph) u)"
        "\<forall>u. finite (Pair_Graph.neighbourhood (G.digraph_abs non_matching_graph) u)"
    by (auto intro: finite_neighbourhood_of_finite)
  moreover have "t_set bfs_sources \<noteq> {}"
    using bfs_sources_props(2) m_free
    by simp
  moreover have "G.digraph_abs matching_graph \<inter> G.digraph_abs non_matching_graph = {}"
    unfolding matching_graph_abs non_matching_graph_abs
    by auto
  ultimately show ?thesis
    unfolding phase_bfs.BFS_axiom_def
    using G.from_list_correct(1-3) bfs_sources_props(1) bfs_sources_in_graph
    by blast
qed

lemma bipartite_matching_input_phase:
  "phase_bfs.bipartite_matching_input bfs_sources matching_graph non_matching_graph
     (hk_input.ugraph_abs Gin) (mate_matching m) X Y"
  using ugraph_abs_graph_invar mate_matching_subset matching_graph_abs non_matching_graph_abs
        bfs_sources_props(3) input(2)
  by (simp add: phase_bfs.bipartite_matching_input_def)

lemma bfs_state_eq: "bfs_state = phase_bfs.BFS matching_graph non_matching_graph (phase_bfs.initial_state bfs_sources)"
  by (rule phase_bfs.BFS_impl_same[OF phase_bfs.initial_state_props(13)[OF phase_bfs_axiom]])

lemma bfs_state_valid_impl:
  "phase_bfs.valid_alt_BFS_DAG_impl bfs_sources matching_graph non_matching_graph bfs_dag
     (distances bfs_state) (visited_even bfs_state) (visited_odd bfs_state)"
  unfolding bfs_state_eq
  by (rule phase_bfs.BFS_valid_DAG_impl[OF phase_bfs_axiom])

lemma bfs_state_valid:
  "phase_bfs.valid_alt_BFS_DAG bfs_sources matching_graph non_matching_graph bfs_dag
     (distances bfs_state) (visited_even bfs_state) (visited_odd bfs_state)"
  by (rule phase_bfs.valid_alt_BFS_DAG_impl_props(7)[OF phase_bfs_axiom bfs_state_valid_impl])

lemma bfs_dag_subset: "G.digraph_abs bfs_dag \<subseteq> G.digraph_abs Gin"
proof
  fix e
  assume "e \<in> G.digraph_abs bfs_dag"
  then obtain u v where "e = (u, v)" "(u, v) \<in> G.digraph_abs bfs_dag"
    by (cases e) auto
  hence "(u, v) \<in> G.digraph_abs non_matching_graph \<or> (u, v) \<in> G.digraph_abs matching_graph"
    using phase_bfs.valid_alt_BFS_DAG_props(3)[OF phase_bfs_axiom bfs_state_valid]
    by blast
  thus "e \<in> G.digraph_abs Gin"
    unfolding matching_graph_abs non_matching_graph_abs
    using \<open>e = (u, v)\<close> mate_matching_subset
    by auto
qed

lemma bfs_dag_graph_inv: "G.graph_inv bfs_dag"
  by (rule phase_bfs.valid_alt_BFS_DAG_impl_props(1)[OF phase_bfs_axiom bfs_state_valid_impl])

lemma isin_bfs_dag: "isin (G.neighbourhood bfs_dag u) v \<longleftrightarrow> (u, v) \<in> G.digraph_abs bfs_dag"
  using G.are_connected_abs[OF bfs_dag_graph_inv, of v u]
        G.vset.set.set_isin[OF G.neighbourhood_invars'[OF bfs_dag_graph_inv, of u], of v]
  by simp

lemma copies_graph_abs:
  "CGraph.digraph_abs copies_graph =
     phase_bfs.copies_dag matching_graph non_matching_graph (G.digraph_abs bfs_dag)"
  using bfs_dag_subset
  by (auto simp: copies_edges_def isin_bfs_dag phase_bfs.copies_dag_def
                 matching_graph_abs[unfolded G.from_list_correct(4)]
                 non_matching_graph_abs[unfolded G.from_list_correct(4)] mate_matching_iff[OF m_invar]
           split: if_splits)

lemma copies_graph_level:
  "w \<in> dVs (CGraph.digraph_abs copies_graph) \<Longrightarrow>
   level w = phase_bfs.copies_lev bfs_sources matching_graph non_matching_graph w"
proof-
  assume "w \<in> dVs (CGraph.digraph_abs copies_graph)"
  hence "w \<in> dVs (phase_bfs.copies_dag matching_graph non_matching_graph (G.digraph_abs bfs_dag))"
    by (simp only: copies_graph_abs)
  thus ?thesis
    using phase_bfs.copies_lev_by_lookup[OF phase_bfs_axiom bfs_state_valid]
    by (simp add: copy_level_def)
qed

lemma copies_graph_layered: "CGraph.layered_graph_input copies_graph level"
proof-
  have "layered_dgraph (CGraph.digraph_abs copies_graph)
          (phase_bfs.copies_lev bfs_sources matching_graph non_matching_graph)"
    using phase_bfs.valid_DAG_layered[OF phase_bfs_axiom bfs_state_valid_impl]
    by (simp only: copies_graph_abs)
  hence "layered_dgraph (CGraph.digraph_abs copies_graph) level"
    by (intro layered_dgraph_cong[OF copies_graph_level[symmetric]])
  thus ?thesis
    by (auto intro!: CGraph.layered_graph_inputI simp: CGraph.from_list_correct(2,3,5))
qed

lemma visited_odd_inv: "vset_inv (visited_odd bfs_state)"
  by (rule phase_bfs.valid_alt_BFS_DAG_impl_props(3)[OF phase_bfs_axiom bfs_state_valid_impl])

lemma copy_roots_free_odd:
  "set copy_roots \<subseteq> Vtx Odd ` (t_set bfs_sources \<inter> t_set (visited_odd bfs_state))"
  using G.vset.set.set_isin[OF visited_odd_inv]
  by (auto simp: phase_roots_def bfs_sources_props(2) Let_def split: if_splits)

lemma copy_roots_in_graph: "set copy_roots \<subseteq> dVs (CGraph.digraph_abs copies_graph)"
proof
  fix w
  assume "w \<in> set copy_roots"
  then obtain t where "w = Vtx Odd t" "t \<in> t_set (visited_odd bfs_state)"
    using copy_roots_free_odd
    by auto
  thus "w \<in> dVs (CGraph.digraph_abs copies_graph)"
    using phase_bfs.VisO_copies_dVs[OF phase_bfs_axiom bfs_state_valid]
    by (simp only: copies_graph_abs)
qed

lemma copy_roots_nonempty:
  "filter (\<lambda>t. isin (visited_odd bfs_state) t) (free_vertices vs m) \<noteq> [] \<Longrightarrow> copy_roots \<noteq> []"
proof(cases "filter (\<lambda>t. isin (visited_odd bfs_state) t) (free_vertices vs m)")
  case (Cons t0 ts)
  let ?L = "\<lambda>t. copy_level (distances bfs_state) (Vtx Odd t)"
  have "fold min (map ?L ts) (?L t0) \<in> ?L ` set (t0 # ts)"
    using fold_min_mem[of "map ?L ts" "?L t0"]
    by auto
  thus ?thesis
    using Cons
    by (auto simp: phase_roots_def filter_empty_conv Let_def)
qed simp

lemma dVs_copies_graph:
  "dVs (CGraph.digraph_abs copies_graph) = set (map fst copies_edge_list @ map snd copies_edge_list)"
  by (simp add: dVs_eq image_Un)

lemma blocked_copies_props:
  "c_vset_inv (blocked p)"
  "c_t_set (blocked p) \<subseteq> dVs (CGraph.digraph_abs copies_graph)"
  "\<lbrakk>w \<in> dVs (CGraph.digraph_abs copies_graph); vtx w \<in> vtx ` set p\<rbrakk> \<Longrightarrow> w \<in> c_t_set (blocked p)"
proof-
  show "c_vset_inv (blocked p)" "c_t_set (blocked p) \<subseteq> dVs (CGraph.digraph_abs copies_graph)"
    by (auto simp: blocked_copies_def dVs_copies_graph)
  show "w \<in> c_t_set (blocked p)"
    if "w \<in> dVs (CGraph.digraph_abs copies_graph)" "vtx w \<in> vtx ` set p"
    using that
    by (cases w; cases "label w") (auto simp: blocked_copies_def dVs_copies_graph dVs_eq)
qed

text \<open>The search at this phase, with its proofs locale.\<close>

interpretation phase_search_proofs: Disjoint_Paths_Search_thms
  where empty = c_empty and delete = c_delete and insert = c_insert and isin = c_isin
    and t_set = c_t_set and sel = c_sel and update = c_update and adjmap_inv = c_adjmap_inv
    and vset_empty = c_vset_empty and vset_delete = c_vset_delete and vset_inv = c_vset_inv
    and union = c_union and inter = c_inter and diff = c_diff and lookup = c_lookup
    and G = copies_graph and target = "\<lambda>w. level w = 0" and blocked = blocked
    and initial_roots = copy_roots
    and search_step = "\<lambda>avoid r vis. IDFS_impl_c copies_graph (\<lambda>w. level w = 0) avoid [r] vis"
  using phase_search.Disjoint_Paths_Search_axioms copies_graph_layered copy_roots_in_graph
        blocked_copies_props(1,2)
  by (auto intro!: Disjoint_Paths_Search_thms.intro Disjoint_Paths_Search_thms_axioms.intro
           simp: phase_search.Disjoint_Paths_Search_axiom_def)

lemmas phase_search_correct_1 =
  phase_search_proofs.Disjoint_Paths_Search_correct_1

lemmas phase_search_correct_2 =
  phase_search_proofs.Disjoint_Paths_Search_correct_2

lemmas phase_search_correct_3 =
  phase_search_proofs.Disjoint_Paths_Search_correct_3

lemma hopcroft_karp_phase_unfold:
  "hopcroft_karp_phase edges vs m = map (map vtx) (paths search_state)"
  using m_free
  by (simp add: hopcroft_karp_phase_def phase_search.Disjoint_Paths_Search_run_impl_def
                phase_search_proofs.Disjoint_Paths_Search_impl_to_Disjoint_Paths_Search Let_def)

text \<open>A path of the phase is the projection of a walk of the copies graph from a free odd copy
  down to level 0, hence an augmenting path (Alt_BFS_Bipartite).\<close>

lemma phase_paths_augmenting:
  "P \<in> set (hopcroft_karp_phase edges vs m) \<Longrightarrow>
   graph_augmenting_path (hk_input.ugraph_abs Gin) (mate_matching m) P"
proof-
  assume "P \<in> set (hopcroft_karp_phase edges vs m)"
  then obtain q where "q \<in> set (paths search_state)" "P = map vtx q"
    by (auto simp: hopcroft_karp_phase_unfold)
  note q = phase_search_correct_1[OF this(1)]
  then obtain t where "last q = Vtx Odd t" "t \<in> t_set bfs_sources"
    using copy_roots_free_odd
    by blast
  moreover have "Vwalk.vwalk_bet (CGraph.digraph_abs copies_graph) (last q) (rev q) (hd q)"
    using q
    by (auto intro: found_vwalk_bet)
  moreover hence "phase_bfs.copies_lev bfs_sources matching_graph non_matching_graph (hd q) = 0"
    using q copies_graph_level[OF vwalk_bet_endpoints(2)]
    by simp
  ultimately have "graph_augmenting_path (hk_input.ugraph_abs Gin) (mate_matching m) (rev (map vtx (rev q)))"
    by (intro phase_bfs.copies_walk_augmenting(1)[OF phase_bfs_axiom bipartite_matching_input_phase
                                                      bfs_state_valid])
       (simp_all only: copies_graph_abs)
  thus "graph_augmenting_path (hk_input.ugraph_abs Gin) (mate_matching m) P"
    using \<open>P = map vtx q\<close>
    by (simp add: rev_map)
qed

lemma phase_paths_disjoint: "sorted_wrt (\<lambda>P Q. set P \<inter> set Q = {}) (hopcroft_karp_phase edges vs m)"
proof-
  have "set q \<subseteq> dVs (CGraph.digraph_abs copies_graph)" if "q \<in> set (paths search_state)" for q
  proof-
    have "Vwalk.vwalk_bet (CGraph.digraph_abs copies_graph) (last q) (rev q) (hd q)"
      using phase_search_correct_1[OF that]
      by (auto intro: found_vwalk_bet)
    hence "set (rev q) \<subseteq> dVs (CGraph.digraph_abs copies_graph)"
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
  "\<exists>P. graph_augmenting_path (hk_input.ugraph_abs Gin) (mate_matching m) P \<Longrightarrow>
   hopcroft_karp_phase edges vs m \<noteq> []"
proof-
  assume "\<exists>P. graph_augmenting_path (hk_input.ugraph_abs Gin) (mate_matching m) P"
  then obtain t where "t \<in> t_set bfs_sources"
      "Vtx Odd t \<in> dVs (phase_bfs.copies_dag matching_graph non_matching_graph (G.digraph_abs bfs_dag))"
    using phase_bfs.augmenting_path_iff_free_odd_copy[OF phase_bfs_axiom bipartite_matching_input_phase
                                                         bfs_state_valid]
    by blast
  moreover hence "t \<in> t_set (visited_odd bfs_state)"
    using phase_bfs.copies_dag_dVs[OF phase_bfs_axiom bfs_state_valid]
    by blast
  ultimately have "copy_roots \<noteq> []"
    using G.vset.set.set_isin[OF visited_odd_inv]
    by (auto intro!: copy_roots_nonempty simp: bfs_sources_props(2) filter_empty_conv)
  then obtain r where "r \<in> set copy_roots"
    by (cases copy_roots) auto
  moreover hence "r \<in> dVs (phase_bfs.copies_dag matching_graph non_matching_graph (G.digraph_abs bfs_dag))"
    by (rule subsetD[OF copy_roots_in_graph[unfolded copies_graph_abs]])
  then obtain q z where "Vwalk.vwalk_bet (phase_bfs.copies_dag matching_graph non_matching_graph (G.digraph_abs bfs_dag)) r q z"
                        "phase_bfs.copies_lev bfs_sources matching_graph non_matching_graph z = 0"
    by (elim phase_bfs.copies_reach_zero[OF phase_bfs_axiom bfs_state_valid])
  hence "Vwalk.vwalk_bet (CGraph.digraph_abs copies_graph) r q z"
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
  "\<lbrakk>mate_invar (hk_input.ugraph_abs Gin) m;
    \<exists>P. graph_augmenting_path (hk_input.ugraph_abs Gin) (mate_matching m) P\<rbrakk>
   \<Longrightarrow> free_vertices vs m \<noteq> []"
  by (fastforce simp: free_vertices_def filter_empty_conv matching_augmenting_path_def
                      mate_Vs_iff
               dest: mem_path_Vs[OF _ hd_in_set])

subsection \<open>The phase meets the contract of the top loop\<close>

lemma phase_sound:
  "\<lbrakk>mate_invar (hk_input.ugraph_abs Gin) M; p \<in> set (hopcroft_karp_phase edges vs M)\<rbrakk>
   \<Longrightarrow> graph_augmenting_path (hk_input.ugraph_abs Gin) (mate_matching M) p"
  by (rule phase_paths_augmenting)
     (auto simp: hopcroft_karp_phase_no_free[of vs M edges] simp del: edges_set)

lemma phase_disjoint:
  "mate_invar (hk_input.ugraph_abs Gin) M
   \<Longrightarrow> sorted_wrt (\<lambda>p q. set p \<inter> set q = {}) (hopcroft_karp_phase edges vs M)"
  by (cases "free_vertices vs M = []")
     (simp_all add: hopcroft_karp_phase_no_free phase_paths_disjoint del: edges_set)

lemma phase_complete:
  "\<lbrakk>mate_invar (hk_input.ugraph_abs Gin) M;
    \<exists>p. graph_augmenting_path (hk_input.ugraph_abs Gin) (mate_matching M) p\<rbrakk>
   \<Longrightarrow> hopcroft_karp_phase edges vs M \<noteq> []"
  using free_vertices_nonempty phase_paths_nonempty by blast

lemmas phase = phase_sound phase_disjoint phase_complete

end


end

end
