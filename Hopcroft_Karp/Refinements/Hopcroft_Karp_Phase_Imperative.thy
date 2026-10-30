theory Hopcroft_Karp_Phase_Imperative
  imports Hopcroft_Karp.Hopcroft_Karp_Phase Micali_Vazirani.Alt_BFS_Imperative
          Micali_Vazirani.IDFS_Imperative Disjoint_Paths_Search_Imperative
begin

provenance ai


section \<open>Imperative Refinement of the Phase\<close>

text \<open>The imperative phase composes the imperative alternating BFS
  (@{locale Alt_BFS_Imperative}), the imperative incremental DFS (@{locale IDFS_Imperative}) and
  the imperative disjoint-paths search (@{locale Disjoint_Paths_Search_Imperative}), the latter
  with the incremental DFS as its search step. The remaining steps of the phase, i.e.\ building
  the matching graphs, the sources, the graph of copies and the roots, testing the target level
  and committing a found path, are parameters whose Hoare triples are stated against the
  functional builders of @{locale Hopcroft_Karp_Phase}. As the imperative BFS does not build the
  BFS DAG, the graph of copies and the roots are specified by the visited sets and the distances
  instead; this agrees with the functional phase. The imperative phase computes the paths of the
  functional phase @{const Hopcroft_Karp_Phase.hopcroft_karp_phase}.\<close>

instance parity :: countable
  by countable_datatype

instance labelled_vtx :: (countable) countable
  by countable_datatype

instance labelled_vtx :: (heap) heap ..

subsection \<open>The builders, specified by the visited sets and the distances\<close>

context Hopcroft_Karp_Phase
begin

definition "copies_edges_dist edges m VE VO d =
  concat (map (\<lambda>(u, v).
     if mate_get m u = v
     then (if u \<in> VO \<and> v \<in> VE \<and> d (Vtx Even v) = d (Vtx Odd u) + 1
           then [(Vtx Even v, Vtx Odd u)] else [])
     else (if u \<in> VE \<and> v \<in> VO \<and> d (Vtx Odd v) = d (Vtx Even u) + 1
           then [(Vtx Odd v, Vtx Even u)] else [])) edges)"

definition "phase_roots_dist vs m VO (d :: 'v labelled_vtx \<Rightarrow> nat) =
  (let free_odd = filter (\<lambda>t. t \<in> VO) (free_vertices vs m) in
   if free_odd = [] then [] else
   let k = fold min (map (\<lambda>t. d (Vtx Odd t)) (tl free_odd)) (d (Vtx Odd (hd free_odd)))
   in map (Vtx Odd) (filter (\<lambda>t. d (Vtx Odd t) = k) free_odd))"

end

subsection \<open>The program\<close>

text \<open>The builders: the sources with a test for their emptiness, the matching and the
  non-matching graphs, the graph of copies together with the set of its vertices, the roots on a
  fresh stack, the test whether a copy has level 0, the commitment of a found path left on the
  stack of the incremental DFS (which blocks the copies of its vertices in the graph of copies),
  and the allocation of the auxiliary structures. The operations of the BFS and of the incremental DFS
  are those of @{locale Alt_BFS_Imperative_spec} and @{locale IDFS_Imperative_spec}; one stack
  implementation is used for the incremental DFS and for the roots of the disjoint-paths
  search.\<close>

locale Hopcroft_Karp_Phase_Imperative_spec =
  fixes free_sources_imp :: "'vi \<Rightarrow> 'mi \<Rightarrow> (bool \<times> 'imp_src) Heap"
    and alt_graphs_imp :: "'ei \<Rightarrow> 'mi \<Rightarrow> ('imp_G \<times> 'imp_G) Heap"
    and vis_empty_imp :: "'imp_vis Heap"
    and dist_init_imp :: "'imp_dist Heap"
    and copies_graph_imp :: "'ei \<Rightarrow> 'mi \<Rightarrow> 'imp_vis \<Rightarrow> 'imp_vis \<Rightarrow> 'imp_dist \<Rightarrow> ('gi \<times> 'si) Heap"
    and phase_roots_imp :: "'vi \<Rightarrow> 'mi \<Rightarrow> 'imp_vis \<Rightarrow> 'imp_dist \<Rightarrow> 'stki Heap"
    and level_zero_imp :: "'imp_dist \<Rightarrow> 'v::heap labelled_vtx \<Rightarrow> bool Heap"
    and commit_path_imp :: "'si \<Rightarrow> 'stki \<Rightarrow> 'si \<Rightarrow> 'ips \<Rightarrow> ('si \<times> 'ips) Heap"
    and set_empty_imp :: "'si Heap"
    and paths_empty_imp :: "'ips Heap"
    and imp_cf_is_empty :: "'imp_cf \<Rightarrow> bool Heap"
    and next_frontier_and_visited_imp :: "'imp_G \<Rightarrow> 'imp_cf \<Rightarrow> 'imp_vis \<Rightarrow> ('imp_cf \<times> 'imp_vis) Heap"
    and set_all_dists_imp :: "'imp_dist \<Rightarrow> parity \<Rightarrow> 'imp_cf \<Rightarrow> nat \<Rightarrow> 'imp_dist Heap"
    and imp_src_to_cf :: "'imp_src \<Rightarrow> 'imp_cf Heap"
    and set_srcs_visited :: "'imp_vis \<Rightarrow> 'imp_src \<Rightarrow> 'imp_vis Heap"
    and sel_unseen_imp :: "'gi \<Rightarrow> 'v labelled_vtx \<Rightarrow> 'si \<Rightarrow> 'v labelled_vtx option Heap"
    and seen_init_imp :: "'si \<Rightarrow> 'si \<Rightarrow> 'si \<Rightarrow> unit Heap"
    and set_isin_imp :: "'si \<Rightarrow> 'v labelled_vtx \<Rightarrow> bool Heap"
    and set_insert_imp :: "'v labelled_vtx \<Rightarrow> 'si \<Rightarrow> unit Heap"
    and stack_empty_imp :: "'stki Heap"
    and stack_is_empty_imp :: "'stki \<Rightarrow> bool Heap"
    and stack_top_imp :: "'stki \<Rightarrow> 'v labelled_vtx Heap"
    and stack_push_imp :: "'stki \<Rightarrow> 'v labelled_vtx \<Rightarrow> unit Heap"
    and stack_pop_imp :: "'stki \<Rightarrow> unit Heap"
begin

sublocale bfs: Alt_BFS_Imperative_spec
  where matching_imp = Mgi and unmatching_imp = Ugi
  for Mgi Ugi .

sublocale idfs: IDFS_Imperative_spec
  where target_imp = "level_zero_imp Di"
  for Di .

sublocale dps: Disjoint_Paths_Search_Imperative_spec
  where search_step_imp = "\<lambda>Ai r Vi. idfs.IDFS_imp Di Gi Ai r Vi SNi Si"
    and commit_path_imp = "commit_path_imp CVi Si"
  for Di Gi CVi SNi Si .

definition "hopcroft_karp_phase_imp Ei Vi Mi =
  do { (nofree, Fi) \<leftarrow> free_sources_imp Vi Mi;
       if nofree then paths_empty_imp
       else do { (Mgi, Ugi) \<leftarrow> alt_graphs_imp Ei Mi;
                 VEi \<leftarrow> vis_empty_imp;
                 VOi \<leftarrow> vis_empty_imp;
                 Di \<leftarrow> dist_init_imp;
                 st \<leftarrow> bfs.Alt_BFS_run_imp Mgi Ugi VEi VOi Fi Di;
                 (Gi, CVi) \<leftarrow> copies_graph_imp Ei Mi (i_vis_even st) (i_vis_odd st) (i_dists st);
                 Ri \<leftarrow> phase_roots_imp Vi Mi (i_vis_odd st) (i_dists st);
                 Ai \<leftarrow> set_empty_imp;
                 Xi \<leftarrow> set_empty_imp;
                 SNi \<leftarrow> set_empty_imp;
                 Si \<leftarrow> stack_empty_imp;
                 Psi \<leftarrow> paths_empty_imp;
                 res \<leftarrow> dps.Disjoint_Paths_Search_run_imp (i_dists st) Gi SNi Si CVi Ri Ai Xi Psi;
                 return (i_paths res) } }"

end

subsection \<open>The refinement locale\<close>

text \<open>The vertices are drawn from a universe @{term univ}, and their copies from its preimage
  under @{const vtx}; the universe may be the whole type. The operations of the distance BFS of
  @{locale Alt_BFS_distance} and the imperative operations are specified for all graphs and sets
  within the universe, the builders against the functional builders of the phase. The sets of the
  incremental DFS are related to sets of copies by @{term set_assn}, the stack by
  @{term stack_assn} (@{locale bounded_stack_imp}).\<close>

locale Hopcroft_Karp_Phase_Imperative =
  Hopcroft_Karp_Phase where K = univ and lookup = lookup and c_lookup = c_lookup and mate_get = mate_get
    and lookup_dist = lookup_dist +
  Hopcroft_Karp_Phase_Imperative_spec where free_sources_imp = free_sources_imp
    and copies_graph_imp = copies_graph_imp and alt_graphs_imp = alt_graphs_imp
    and commit_path_imp = commit_path_imp and imp_cf_is_empty = imp_cf_is_empty
    and level_zero_imp = level_zero_imp +
  stk: bounded_stack_imp where stack_abstract = stack_abstract +
  cset: fixed_univ_set_basic_imp where U = "vtx -` univ"
    and fixed_univ_set_invar = "\<lambda>S. S \<subseteq> vtx -` univ"
    and fixed_univ_set_abstract = id and fixed_univ_set_empty = "{}"
    and fixed_univ_set_insert = Set.insert and fixed_univ_set_delete = "\<lambda>x S. S - {x}"
    and fixed_univ_set_isin = "\<lambda>S x. x \<in> S" and fixed_univ_set_assn = set_assn
    and fixed_univ_set_insert_imp = set_insert_imp and fixed_univ_set_isin_imp = set_isin_imp
  for lookup :: "'adjmap \<Rightarrow> 'v::heap \<Rightarrow> 'vset option"
  and c_lookup :: "'cadjmap \<Rightarrow> 'v labelled_vtx \<Rightarrow> 'cvset option"
  and mate_get :: "'mate \<Rightarrow> 'v \<Rightarrow> 'v"
  and lookup_dist :: "'dmap \<Rightarrow> 'v labelled_vtx \<Rightarrow> enat option"
  and free_sources_imp :: "'vi \<Rightarrow> 'mi \<Rightarrow> (bool \<times> 'imp_src) Heap"
  and copies_graph_imp :: "'ei \<Rightarrow> 'mi \<Rightarrow> 'imp_vis \<Rightarrow> 'imp_vis \<Rightarrow> 'imp_dist \<Rightarrow> ('gi \<times> 'si) Heap"
  and alt_graphs_imp :: "'ei \<Rightarrow> 'mi \<Rightarrow> ('imp_G \<times> 'imp_G) Heap"
  and commit_path_imp :: "'si \<Rightarrow> 'stki \<Rightarrow> 'si \<Rightarrow> 'ips \<Rightarrow> ('si \<times> 'ips) Heap"
  and imp_cf_is_empty :: "'imp_cf \<Rightarrow> bool Heap"
  and level_zero_imp :: "'imp_dist \<Rightarrow> 'v labelled_vtx \<Rightarrow> bool Heap"
  and stack_abstract :: "'s \<Rightarrow> 'v labelled_vtx list"
  and univ :: "'v set"
  and set_assn :: "'v labelled_vtx set \<Rightarrow> 'si \<Rightarrow> assn" +
  fixes next_frontier_and_visited :: "'adjmap \<Rightarrow> 'vset \<Rightarrow> 'vset \<Rightarrow> 'vset \<times> 'vset"
    and set_all_dists :: "'dist \<Rightarrow> parity \<Rightarrow> 'vset \<Rightarrow> nat \<Rightarrow> 'dist"
    and dist_lookup :: "'dist \<Rightarrow> 'v labelled_vtx \<Rightarrow> nat"
    and dist_invar :: "'dist \<Rightarrow> 'v labelled_vtx set \<Rightarrow> bool"
    and some_dist :: 'dist
    and edges_assn :: "('v \<times> 'v) list \<Rightarrow> 'ei \<Rightarrow> assn"
    and verts_assn :: "'v list \<Rightarrow> 'vi \<Rightarrow> assn"
    and mate_assn :: "'mate \<Rightarrow> 'mi \<Rightarrow> assn"
    and graph_assn :: "'adjmap \<Rightarrow> 'imp_G \<Rightarrow> assn"
    and imp_src_assn :: "'vset \<Rightarrow> 'imp_src \<Rightarrow> assn"
    and imp_cf_assn :: "'vset \<Rightarrow> 'imp_cf \<Rightarrow> assn"
    and imp_vis_assn :: "'vset \<Rightarrow> 'imp_vis \<Rightarrow> assn"
    and imp_dist_assn :: "'dist \<Rightarrow> 'imp_dist \<Rightarrow> assn"
    and cgraph_assn :: "'cadjmap \<Rightarrow> 'gi \<Rightarrow> assn"
    and paths_assn :: "'v labelled_vtx list list \<Rightarrow> 'ips \<Rightarrow> assn"
  assumes next_frontier_and_visited:
    "\<And>H F V F' V'. \<lbrakk>vset_inv F; vset_inv V; G.graph_inv H; G.digraph_abs H \<subseteq> univ \<times> univ;
        t_set F \<subseteq> univ; t_set V \<subseteq> univ; next_frontier_and_visited H F V = (F', V')\<rbrakk>
       \<Longrightarrow> vset_inv F'"
    "\<And>H F V F' V'. \<lbrakk>vset_inv F; vset_inv V; G.graph_inv H; G.digraph_abs H \<subseteq> univ \<times> univ;
        t_set F \<subseteq> univ; t_set V \<subseteq> univ; next_frontier_and_visited H F V = (F', V')\<rbrakk>
       \<Longrightarrow> t_set F' = next_frontier (G.digraph_abs H) (t_set F) (t_set V)"
    "\<And>H F V F' V'. \<lbrakk>vset_inv F; vset_inv V; G.graph_inv H; G.digraph_abs H \<subseteq> univ \<times> univ;
        t_set F \<subseteq> univ; t_set V \<subseteq> univ; next_frontier_and_visited H F V = (F', V')\<rbrakk>
       \<Longrightarrow> vset_inv V'"
    "\<And>H F V F' V'. \<lbrakk>vset_inv F; vset_inv V; G.graph_inv H; G.digraph_abs H \<subseteq> univ \<times> univ;
        t_set F \<subseteq> univ; t_set V \<subseteq> univ; next_frontier_and_visited H F V = (F', V')\<rbrakk>
       \<Longrightarrow> t_set V' = t_set V \<union> t_set F'"
  and set_all_dists:
    "\<And>d S p F n. \<lbrakk>vset_inv F; t_set F \<subseteq> univ; dist_invar d S\<rbrakk>
       \<Longrightarrow> dist_invar (set_all_dists d p F n) (S \<union> Vtx p ` t_set F)"
    "\<And>d S p F n x. \<lbrakk>vset_inv F; t_set F \<subseteq> univ; dist_invar d S; x \<in> t_set F\<rbrakk>
       \<Longrightarrow> dist_lookup (set_all_dists d p F n) (Vtx p x) = n"
    "\<And>d S p F n w. \<lbrakk>vset_inv F; t_set F \<subseteq> univ; dist_invar d S; w \<in> S - Vtx p ` t_set F\<rbrakk>
       \<Longrightarrow> dist_lookup (set_all_dists d p F n) w = dist_lookup d w"
  and some_dist: "dist_invar some_dist {}"
  and vset_empty_unique: "\<And>V. \<lbrakk>vset_inv V; t_set V = {}\<rbrakk> \<Longrightarrow> V = vset_empty"
  and imp_cf_is_empty_rule:
    "\<And>S Si. <imp_cf_assn S Si> imp_cf_is_empty Si <\<lambda>b. imp_cf_assn S Si * \<up>(b \<longleftrightarrow> S = vset_empty)>"
  and next_frontier_and_visited_imp_rule:
    "\<And>H Hi F Fi V Vi. \<lbrakk>vset_inv F; vset_inv V; G.graph_inv H; G.digraph_abs H \<subseteq> univ \<times> univ;
        t_set F \<subseteq> univ; t_set V \<subseteq> univ\<rbrakk> \<Longrightarrow>
     <imp_cf_assn F Fi * imp_vis_assn V Vi * graph_assn H Hi>
       next_frontier_and_visited_imp Hi Fi Vi
     <\<lambda>(Fi', Vi'). imp_cf_assn (fst (next_frontier_and_visited H F V)) Fi' *
                   imp_vis_assn (snd (next_frontier_and_visited H F V)) Vi' * graph_assn H Hi>"
  and set_all_dists_imp_rule:
    "\<And>d di p F Fi n. \<lbrakk>vset_inv F; t_set F \<subseteq> univ\<rbrakk> \<Longrightarrow>
     <imp_dist_assn d di * imp_cf_assn F Fi> set_all_dists_imp di p Fi n
     <\<lambda>r. imp_dist_assn (set_all_dists d p F n) r * imp_cf_assn F Fi>"
  and imp_src_to_cf_rule: "\<And>S Si. <imp_src_assn S Si> imp_src_to_cf Si <\<lambda>r. imp_cf_assn S r>"
  and set_srcs_visited_rule:
    "\<And>S Si Vi. <imp_src_assn S Si * imp_vis_assn vset_empty Vi> set_srcs_visited Vi Si
               <\<lambda>r. imp_vis_assn S r * imp_src_assn S Si>"
  and sel_unseen_rule:
    "\<And>CG Gi v S Si Sf. \<lbrakk>CGraph.graph_inv CG; dVs (CGraph.digraph_abs CG) \<subseteq> vtx -` univ;
        c_vset_inv Sf; c_t_set Sf = S; S \<subseteq> vtx -` univ; v \<in> vtx -` univ\<rbrakk> \<Longrightarrow>
     <cgraph_assn CG Gi * set_assn S Si> sel_unseen_imp Gi v Si
     <\<lambda>r. cgraph_assn CG Gi * set_assn S Si *
          \<up>(r = (if c_diff (CGraph.neighbourhood CG v) Sf \<noteq> c_vset_empty
                 then Some (c_sel (c_diff (CGraph.neighbourhood CG v) Sf)) else None))>"
  and seen_init_rule:
    "\<And>A Ai V Vi S SNi. \<lbrakk>A \<subseteq> vtx -` univ; V \<subseteq> vtx -` univ; S \<subseteq> vtx -` univ\<rbrakk> \<Longrightarrow>
     <set_assn A Ai * set_assn V Vi * set_assn S SNi> seen_init_imp SNi Ai Vi
     <\<lambda>_. set_assn A Ai * set_assn V Vi * set_assn (A \<union> V) SNi>"
  and free_sources_rule:
    "\<And>vs Vi m Mi. set vs \<subseteq> univ \<Longrightarrow>
     <verts_assn vs Vi * mate_assn m Mi> free_sources_imp Vi Mi
     <\<lambda>(b, Fi). verts_assn vs Vi * mate_assn m Mi * imp_src_assn (free_vertex_set vs m) Fi *
               \<up>(b \<longleftrightarrow> free_vertices vs m = [])>"
  and alt_graphs_rule:
    "\<And>edges Ei m Mi. set edges \<subseteq> univ \<times> univ \<Longrightarrow>
     <edges_assn edges Ei * mate_assn m Mi> alt_graphs_imp Ei Mi
     <\<lambda>(Mgi, Ugi). edges_assn edges Ei * mate_assn m Mi *
                   graph_assn (G.from_list (matched_edges edges m)) Mgi *
                   graph_assn (G.from_list (unmatched_edges edges m)) Ugi>"
  and vis_empty_rule: "<emp> vis_empty_imp <imp_vis_assn vset_empty>"
  and dist_init_rule: "<emp> dist_init_imp <imp_dist_assn some_dist>"
  and copies_graph_rule:
    "\<And>edges Ei m Mi VE VEi VO VOi D Di S. \<lbrakk>set edges \<subseteq> univ \<times> univ; vset_inv VE; vset_inv VO;
        t_set VE \<subseteq> univ; t_set VO \<subseteq> univ; dist_invar D S;
        Vtx Even ` t_set VE \<union> Vtx Odd ` t_set VO \<subseteq> S\<rbrakk> \<Longrightarrow>
     <edges_assn edges Ei * mate_assn m Mi * imp_vis_assn VE VEi * imp_vis_assn VO VOi *
      imp_dist_assn D Di>
       copies_graph_imp Ei Mi VEi VOi Di
     <\<lambda>(Gi, CVi). edges_assn edges Ei * mate_assn m Mi * imp_vis_assn VE VEi * imp_vis_assn VO VOi *
           imp_dist_assn D Di *
           cgraph_assn (CGraph.from_list (copies_edges_dist edges m (t_set VE) (t_set VO) (dist_lookup D)))
             Gi *
           set_assn (dVs (set (copies_edges_dist edges m (t_set VE) (t_set VO) (dist_lookup D)))) CVi>"
  and phase_roots_rule:
    "\<And>vs Vi m Mi VO VOi D Di S. \<lbrakk>set vs \<subseteq> univ; length vs \<le> cap; vset_inv VO; t_set VO \<subseteq> univ; dist_invar D S;
        Vtx Odd ` t_set VO \<subseteq> S\<rbrakk> \<Longrightarrow>
     <verts_assn vs Vi * mate_assn m Mi * imp_vis_assn VO VOi * imp_dist_assn D Di>
       phase_roots_imp Vi Mi VOi Di
     <\<lambda>Ri. verts_assn vs Vi * mate_assn m Mi * imp_vis_assn VO VOi * imp_dist_assn D Di *
           (\<exists>\<^sub>AR. stack_assn R Ri *
                  \<up>(stack_invar R \<and> stack_abstract R = phase_roots_dist vs m (t_set VO) (dist_lookup D)))>"
  and level_zero_rule:
    "\<And>D Di w. vtx w \<in> univ \<Longrightarrow>
     <imp_dist_assn D Di> level_zero_imp Di w <\<lambda>r. imp_dist_assn D Di * \<up>(r \<longleftrightarrow> dist_lookup D w = 0)>"
  and commit_path_rule:
    "\<And>C Ci p Si A Ai ps Psi. \<lbrakk>C \<subseteq> vtx -` univ; A \<subseteq> vtx -` univ; set p \<subseteq> vtx -` univ\<rbrakk> \<Longrightarrow>
     <set_assn C Ci * (\<exists>\<^sub>AR. stack_assn R Si * \<up>(stack_invar R \<and> stack_abstract R = p)) *
      set_assn A Ai * paths_assn ps Psi>
       commit_path_imp Ci Si Ai Psi
     <\<lambda>(Ai', Psi'). set_assn C Ci *
                   (\<exists>\<^sub>AR. stack_assn R Si * \<up>(stack_invar R \<and> stack_abstract R = [])) *
                   set_assn (A \<union> {w \<in> C. vtx w \<in> vtx ` set p}) Ai' *
                   paths_assn (p # ps) Psi'>"
  and set_empty_rule: "<emp> set_empty_imp <set_assn {}>"
  and paths_empty_rule: "<emp> paths_empty_imp <paths_assn []>"
begin

subsection \<open>One phase, for a fixed input and matching\<close>

context
  fixes Gin vs edges X Y
  assumes input: "hk_input.Hopcroft_Karp_axiom Gin vs" "bipartite (hk_input.ugraph_abs Gin) X Y"
    and edges: "set edges = G.digraph_abs Gin"
    and input_univ: "dVs (G.digraph_abs Gin) \<subseteq> univ"
    and capacity: "2 * length vs \<le> cap"
begin

context
  fixes m
  assumes m_invar: "mate_invar (hk_input.ugraph_abs Gin) m" and m_free: "free_vertices vs m \<noteq> []"
begin

lemmas phase_bfs_axiom' = phase_bfs_axiom[OF input edges m_invar m_free]
lemmas bfs_state_eq' = bfs_state_eq[OF input edges m_invar m_free]
lemmas isin_bfs_dag' = isin_bfs_dag[OF input edges m_invar m_free]
lemmas copies_graph_layered' = copies_graph_layered[OF input edges m_invar m_free]
lemmas copy_roots_in_graph' = copy_roots_in_graph[OF input edges m_invar m_free]
lemmas blocked_copies_props' = blocked_copies_props[OF input edges m_invar m_free]
lemmas hopcroft_karp_phase_unfold' = hopcroft_karp_phase_unfold[OF input edges m_invar m_free]
lemmas bfs_sources_props' = bfs_sources_props[OF input edges m_invar]
lemmas visited_odd_inv' = visited_odd_inv[OF input edges m_invar m_free]

lemma input_in_univ:
  "set edges \<subseteq> univ \<times> univ" "set vs \<subseteq> univ"
  "G.digraph_abs (matching_graph edges m) \<subseteq> univ \<times> univ"
  "G.digraph_abs (non_matching_graph edges m) \<subseteq> univ \<times> univ"
proof-
  show E: "set edges \<subseteq> univ \<times> univ"
  proof clarify
    fix u v
    assume "(u, v) \<in> set edges"
    hence "u \<in> dVs (G.digraph_abs Gin)" "v \<in> dVs (G.digraph_abs Gin)"
      unfolding edges
      by blast+
    thus "u \<in> univ \<and> v \<in> univ"
      using input_univ
      by blast
  qed
  show "set vs \<subseteq> univ"
    using input_univ input_props(5)[OF input edges]
    by simp
  show "G.digraph_abs (matching_graph edges m) \<subseteq> univ \<times> univ"
       "G.digraph_abs (non_matching_graph edges m) \<subseteq> univ \<times> univ"
    using E
    by (auto simp: matched_edges_def unmatched_edges_def)
qed

lemma bfs_G_univ:
  "E \<subseteq> phase_bfs.G (matching_graph edges m) (non_matching_graph edges m) \<Longrightarrow> E \<subseteq> univ \<times> univ"
  "A \<subseteq> dVs (phase_bfs.G (matching_graph edges m) (non_matching_graph edges m)) \<Longrightarrow> A \<subseteq> univ"
proof-
  have "phase_bfs.G (matching_graph edges m) (non_matching_graph edges m) \<subseteq> univ \<times> univ"
    using input_in_univ(3,4)
    by (simp add: phase_bfs.G_def)
  thus "E \<subseteq> phase_bfs.G (matching_graph edges m) (non_matching_graph edges m) \<Longrightarrow> E \<subseteq> univ \<times> univ"
       "A \<subseteq> dVs (phase_bfs.G (matching_graph edges m) (non_matching_graph edges m)) \<Longrightarrow> A \<subseteq> univ"
    by (fastforce simp: dVs_def)+
qed

text \<open>The distance BFS of this phase.\<close>

interpretation bfs_dist: Alt_BFS_distance
  where lookup_neighb = lookup and lookup_dist = lookup_dist and empty_dist = empty_dist
    and update_dist = update_dist and delete_dist = delete_dist and invar_dist = invar_dist
    and srcs = "bfs_sources vs m" and matching = "matching_graph edges m"
    and unmatching = "non_matching_graph edges m"
    and expand_tree = expand_tree and next_frontier_impl = next_frontier_impl
    and upd_dists = upd_dists and init_dists = "init_dists_of (bfs_sources vs m)"
    and next_frontier_and_visited = next_frontier_and_visited and set_all_dists = set_all_dists
    and dist_lookup = dist_lookup and dist_invar = dist_invar and some_dist = some_dist
proof(intro Alt_BFS_distance.intro Alt_BFS_distance_axioms.intro)
  show "Alt_BFS.BFS empty delete insert isin t_set sel update adjmap_inv vset_empty vset_delete
          vset_inv union inter diff lookup lookup_dist empty_dist update_dist delete_dist invar_dist
          (bfs_sources vs m) expand_tree next_frontier_impl upd_dists
          (init_dists_of (bfs_sources vs m))"
    by (rule BFS)
qed ((erule next_frontier_and_visited[OF _ _ _ bfs_G_univ(1) bfs_G_univ(2) bfs_G_univ(2)];
      assumption) |
     (rule set_all_dists[OF _ bfs_G_univ(2)]; assumption) |
     (rule some_dist) | (rule vset_empty_unique; assumption))+

text \<open>The final state of the distance BFS determines the visited sets, the distances of the
  visited copies and the DAG of the BFS of the phase.\<close>

abbreviation "dist_final \<equiv> bfs_dist.Alt_BFS_dist_impl bfs_dist.initial_dist_state"

lemma dist_final_props:
  "vset_inv (d_vis_even dist_final)" "vset_inv (d_vis_odd dist_final)"
  "dist_invar (d_dists dist_final)
     (Vtx Even ` t_set (d_vis_even dist_final) \<union> Vtx Odd ` t_set (d_vis_odd dist_final))"
  "t_set (d_vis_even dist_final) \<subseteq> univ" "t_set (d_vis_odd dist_final) \<subseteq> univ"
  "t_set (d_vis_odd dist_final) = t_set (visited_odd (bfs_state vs edges m))"
  "G.digraph_abs (bfs_dag vs edges m) =
     bfs_dist.dist_dag (t_set (d_vis_even dist_final)) (t_set (d_vis_odd dist_final))
       (dist_lookup (d_dists dist_final))"
  "v \<in> t_set (d_vis_even dist_final) \<Longrightarrow>
     lookup_dist (distances (bfs_state vs edges m)) (Vtx Even v) =
       Some (enat (dist_lookup (d_dists dist_final) (Vtx Even v)))"
  "v \<in> t_set (d_vis_odd dist_final) \<Longrightarrow>
     lookup_dist (distances (bfs_state vs edges m)) (Vtx Odd v) =
       Some (enat (dist_lookup (d_dists dist_final) (Vtx Odd v)))"
proof-
  have "bfs_dist.dist_rel (bfs_state vs edges m) dist_final"
    using bfs_dist.dist_rel_final[OF phase_bfs_axiom']
    by (simp add: bfs_state_eq')
  note R = this[unfolded bfs_dist.dist_rel_def]
  show "vset_inv (d_vis_even dist_final)"
    using R by blast
  show "vset_inv (d_vis_odd dist_final)"
    using R by blast
  show "dist_invar (d_dists dist_final)
          (Vtx Even ` t_set (d_vis_even dist_final) \<union> Vtx Odd ` t_set (d_vis_odd dist_final))"
    using R by blast
  show "t_set (d_vis_odd dist_final) = t_set (visited_odd (bfs_state vs edges m))"
    using R by blast
  show "G.digraph_abs (bfs_dag vs edges m) =
          bfs_dist.dist_dag (t_set (d_vis_even dist_final)) (t_set (d_vis_odd dist_final))
            (dist_lookup (d_dists dist_final))"
    using R by blast
  show "t_set (d_vis_even dist_final) \<subseteq> univ"
    using R bfs_G_univ(2)[of "t_set (d_vis_even dist_final)"] by blast
  show "t_set (d_vis_odd dist_final) \<subseteq> univ"
    using R bfs_G_univ(2)[of "t_set (d_vis_odd dist_final)"] by blast
  show "v \<in> t_set (d_vis_even dist_final) \<Longrightarrow>
          lookup_dist (distances (bfs_state vs edges m)) (Vtx Even v) =
            Some (enat (dist_lookup (d_dists dist_final) (Vtx Even v)))"
    using R by blast
  show "v \<in> t_set (d_vis_odd dist_final) \<Longrightarrow>
          lookup_dist (distances (bfs_state vs edges m)) (Vtx Odd v) =
            Some (enat (dist_lookup (d_dists dist_final) (Vtx Odd v)))"
    using R by blast
qed
text \<open>Hence the graph of copies, its levels and the roots are determined by the visited sets and
  the distances.\<close>

lemma copies_edges_dist_eq:
  "copies_edge_list vs edges m =
     copies_edges_dist edges m (t_set (d_vis_even dist_final)) (t_set (d_vis_odd dist_final))
       (dist_lookup (d_dists dist_final))"
proof-
  have dag: "isin (G.neighbourhood (bfs_dag vs edges m) u) v \<longleftrightarrow>
               (u, v) \<in> bfs_dist.dist_dag (t_set (d_vis_even dist_final))
                          (t_set (d_vis_odd dist_final)) (dist_lookup (d_dists dist_final))" for u v
    by (simp only: isin_bfs_dag' dist_final_props(7))
  show ?thesis (*takes long*)
    unfolding copies_edges_def copies_edges_dist_def dag bfs_dist.dist_dag_def
    by (intro arg_cong[where f = concat] map_cong refl)
       (auto simp: matched_edges_def unmatched_edges_def)
qed

lemma copies_graph_dVs:
  "dVs (CGraph.digraph_abs (copies_graph vs edges m)) \<subseteq>
     Vtx Even ` t_set (d_vis_even dist_final) \<union> Vtx Odd ` t_set (d_vis_odd dist_final)"
  by (fastforce simp: copies_edges_dist_eq copies_edges_dist_def dVs_def split: if_splits)

lemma level_eq:
  "w \<in> dVs (CGraph.digraph_abs (copies_graph vs edges m)) \<Longrightarrow>
   level vs edges m w = dist_lookup (d_dists dist_final) w"
  using copies_graph_dVs dist_final_props(8,9)
  by (auto simp: copy_level_def)

lemma copy_roots_eq:
  "copy_roots vs edges m =
     phase_roots_dist vs m (t_set (d_vis_odd dist_final)) (dist_lookup (d_dists dist_final))"
proof-
  let ?FO = "filter (\<lambda>t. t \<in> t_set (d_vis_odd dist_final)) (free_vertices vs m)"
  have F: "filter (\<lambda>t. isin (visited_odd (bfs_state vs edges m)) t) (free_vertices vs m) = ?FO"
    by (simp add: G.vset.set.set_isin[OF visited_odd_inv'] dist_final_props(6))
  have L: "copy_level (distances (bfs_state vs edges m)) (Vtx Odd t) =
             dist_lookup (d_dists dist_final) (Vtx Odd t)" if "t \<in> set ?FO" for t
    using that dist_final_props(9)
    by (simp add: copy_level_def)
  show ?thesis
  proof(cases ?FO)
    case (Cons t0 ts)
    have M: "map (\<lambda>t. copy_level (distances (bfs_state vs edges m)) (Vtx Odd t)) ts =
             map (\<lambda>t. dist_lookup (d_dists dist_final) (Vtx Odd t)) ts"
      using L
      by (intro map_cong) (simp_all add: Cons)
    have T: "copy_level (distances (bfs_state vs edges m)) (Vtx Odd t0) =
             dist_lookup (d_dists dist_final) (Vtx Odd t0)"
      using L
      by (simp add: Cons)
    have P: "filter (\<lambda>t. copy_level (distances (bfs_state vs edges m)) (Vtx Odd t) = k) (t0 # ts) =
             filter (\<lambda>t. dist_lookup (d_dists dist_final) (Vtx Odd t) = k) (t0 # ts)" for k
      using L
      by (intro filter_cong refl) (simp add: Cons)
    show ?thesis
      unfolding phase_roots_def phase_roots_dist_def F Let_def Cons list.sel M T P
      by simp  qed (simp add: phase_roots_def phase_roots_dist_def F)
qed

subsection \<open>The imperative BFS of the phase\<close>

context
  fixes Mgi Ugi :: 'imp_G
begin

interpretation bfs_imp: Alt_BFS_Imperative
  where lookup_neighb = lookup and lookup_dist = lookup_dist and empty_dist = empty_dist
    and update_dist = update_dist and delete_dist = delete_dist and invar_dist = invar_dist
    and srcs = "bfs_sources vs m" and matching = "matching_graph edges m"
    and unmatching = "non_matching_graph edges m"
    and expand_tree = expand_tree and next_frontier_impl = next_frontier_impl
    and upd_dists = upd_dists and init_dists = "init_dists_of (bfs_sources vs m)"
    and next_frontier_and_visited = next_frontier_and_visited and set_all_dists = set_all_dists
    and dist_lookup = dist_lookup and dist_invar = dist_invar and some_dist = some_dist
    and next_frontier_and_visited_imp = next_frontier_and_visited_imp
    and set_all_dists_imp = set_all_dists_imp and imp_cf_is_empty = imp_cf_is_empty
    and imp_src_to_cf = imp_src_to_cf and set_srcs_visited = set_srcs_visited
    and matching_imp = Mgi and unmatching_imp = Ugi
    and graph_assn = graph_assn and imp_src_assn = imp_src_assn and imp_cf_assn = imp_cf_assn
    and imp_vis_assn = imp_vis_assn and imp_dist_assn = imp_dist_assn
proof(intro Alt_BFS_Imperative.intro Alt_BFS_Imperative_axioms.intro
            bfs_dist.Alt_BFS_distance_axioms)
qed (rule imp_cf_is_empty_rule imp_src_to_cf_rule set_srcs_visited_rule |     (rule next_frontier_and_visited_imp_rule[OF _ _ _ bfs_G_univ(1) bfs_G_univ(2) bfs_G_univ(2)];
      assumption) |
     (rule set_all_dists_imp_rule[OF _ bfs_G_univ(2)]; assumption))+

lemma bfs_run_rule:
  "<graph_assn (matching_graph edges m) Mgi * graph_assn (non_matching_graph edges m) Ugi *
    imp_vis_assn vset_empty VEi * imp_vis_assn vset_empty VOi * imp_src_assn (bfs_sources vs m) Fi *
    imp_dist_assn some_dist Di>
     bfs.Alt_BFS_run_imp Mgi Ugi VEi VOi Fi Di
   <\<lambda>ti. graph_assn (matching_graph edges m) Mgi * graph_assn (non_matching_graph edges m) Ugi *
         imp_cf_assn (d_frontier dist_final) (i_frontier ti) *
         imp_vis_assn (d_vis_even dist_final) (i_vis_even ti) *
         imp_vis_assn (d_vis_odd dist_final) (i_vis_odd ti) *
         imp_dist_assn (d_dists dist_final) (i_dists ti)>"
  by (sep_auto heap: bfs_imp.Alt_BFS_run_imp_rule[OF phase_bfs_axiom'] simp: bfs_imp.state_assn_def)

end

subsection \<open>The graph of copies within the universe\<close>

lemma copies_graph_vtx:
  "dVs (CGraph.digraph_abs (copies_graph vs edges m)) \<subseteq> vtx -` dVs (G.digraph_abs Gin)"
proof
  fix w
  assume "w \<in> dVs (CGraph.digraph_abs (copies_graph vs edges m))"
  then obtain e where "e \<in> set (copies_edge_list vs edges m)" "w = fst e \<or> w = snd e"
    by (auto simp: dVs_def)
  then obtain u v where "(u, v) \<in> set edges" "vtx w = u \<or> vtx w = v"
    by (auto simp: copies_edges_def split: if_splits)
  thus "w \<in> vtx -` dVs (G.digraph_abs Gin)"
    unfolding edges
    by auto
qed

lemma copies_graph_univ: "dVs (CGraph.digraph_abs (copies_graph vs edges m)) \<subseteq> vtx -` univ"
  using copies_graph_vtx input_univ
  by blast

lemma vtx_vimage: "vtx -` A = Vtx Even ` A \<union> Vtx Odd ` A"
proof(intro set_eqI iffI)
  fix w
  assume "w \<in> vtx -` A"
  moreover obtain p x where "w = Vtx p x"
    by (cases w)
  ultimately show "w \<in> Vtx Even ` A \<union> Vtx Odd ` A"
    by (cases p) auto
qed auto

lemma copies_graph_card: "card (dVs (CGraph.digraph_abs (copies_graph vs edges m))) \<le> cap"
proof-
  have fin: "finite (dVs (G.digraph_abs Gin))"
    using input_props(5)[OF input edges]
    by (metis List.finite_set)
  have "card (dVs (CGraph.digraph_abs (copies_graph vs edges m))) \<le>
          card (vtx -` dVs (G.digraph_abs Gin))"
    using fin
    by (intro card_mono copies_graph_vtx) (simp add: vtx_vimage)
  also have "\<dots> \<le> card (Vtx Even ` dVs (G.digraph_abs Gin)) + card (Vtx Odd ` dVs (G.digraph_abs Gin))"
    unfolding vtx_vimage
    by (rule card_Un_le)
  also have "\<dots> \<le> 2 * card (dVs (G.digraph_abs Gin))"
    using card_image_le[OF fin, of "Vtx Even"] card_image_le[OF fin, of "Vtx Odd"]
    by simp
  also have "\<dots> \<le> 2 * length vs"
    using card_length[of vs] input_props(5)[OF input edges]
    by simp
  finally show ?thesis
    using capacity
    by simp
qed

lemma copies_graph_finite: "finite (dVs (CGraph.digraph_abs (copies_graph vs edges m)))"
  by (simp add: dVs_eq)

lemma blocked_set:
  "c_t_set (blocked vs edges m p) =
     {w \<in> dVs (CGraph.digraph_abs (copies_graph vs edges m)). vtx w \<in> vtx ` set p}"
proof(intro set_eqI iffI)
  fix w
  assume "w \<in> c_t_set (blocked vs edges m p)"
  thus "w \<in> {w \<in> dVs (CGraph.digraph_abs (copies_graph vs edges m)). vtx w \<in> vtx ` set p}"
    by (auto simp: blocked_copies_def dVs_copies_graph[OF input edges m_invar m_free])
next
  fix w
  assume "w \<in> {w \<in> dVs (CGraph.digraph_abs (copies_graph vs edges m)). vtx w \<in> vtx ` set p}"
  moreover obtain q x where "w = Vtx q x"
    by (cases w)
  ultimately show "w \<in> c_t_set (blocked vs edges m p)"
    by (cases q) (auto simp: blocked_copies_def dVs_eq image_Un)
qed

subsection \<open>The imperative incremental DFS of the phase\<close>

context
  fixes Di :: 'imp_dist
begin

interpretation idfs_imp: IDFS_Imperative
  where empty = c_empty and delete = c_delete and lookup = c_lookup and insert = c_insert
    and isin = c_isin and t_set = c_t_set and sel = c_sel and update = c_update
    and adjmap_inv = c_adjmap_inv and vset_empty = c_vset_empty and vset_delete = c_vset_delete
    and vset_inv = c_vset_inv and union = c_union and inter = c_inter and diff = c_diff
    and G = "copies_graph vs edges m" and lev = "level vs edges m"
    and sel_unseen_imp = sel_unseen_imp and target_imp = "level_zero_imp Di"
    and seen_init_imp = seen_init_imp and set_isin_imp = set_isin_imp
    and set_insert_imp = set_insert_imp and stack_abstract = stack_abstract
    and U = "dVs (CGraph.digraph_abs (copies_graph vs edges m))" and set_assn = set_assn
    and fixed_univ_set_delete_imp = fixed_univ_set_delete_imp
    and P = "\<lambda>w. level vs edges m w = 0" and graph_assn = cgraph_assn
    and target_assn = "imp_dist_assn (d_dists dist_final) Di"
proof(intro IDFS_Imperative.intro IDFS_Imperative_axioms.intro stk.bounded_stack_imp_axioms,
      goal_cases)
  case 1
  show ?case
    by (intro IDFS.IDFS_witness.intro IDFS.IDFS_witness_axioms.intro CGraph.Pair_Graph_Specs_axioms
              c_set_ops.Set2_axioms copies_graph_layered')
next
  case 2
  show ?case
  proof(intro fixed_univ_set_basic_imp.intro fixed_univ_set_basic_imp_axioms.intro
              set_fixed_univ_set)
  qed (rule cset.fixed_univ_set_insert_rule cset.fixed_univ_set_delete_rule
            cset.fixed_univ_set_isin_rule;
       use copies_graph_univ in blast)+
next
  case 3
  then show ?case
    by (intro sel_unseen_rule) (use copies_graph_univ in auto)
next
  case (4 v)
  then show ?case
    using level_zero_rule[of v "d_dists dist_final" Di] level_eq[OF 4] copies_graph_univ
    by auto
next
  case 5
  then show ?case
    by (intro seen_init_rule) (use copies_graph_univ in blast)+
qed (rule subset_refl copies_graph_finite copies_graph_card)+

subsection \<open>The imperative disjoint-paths search of the phase\<close>

text \<open>The search step is the imperative incremental DFS. Its resources are the graph of copies
  and the set of its vertices, the distances (for the target test), the seen set and the stack,
  which holds the found path.\<close>

context
  fixes Gi :: 'gi and CVi :: 'si and SNi :: 'si and Si :: 'stki
begin

definition "step_assn res =
  cgraph_assn (copies_graph vs edges m) Gi *
  set_assn (dVs (CGraph.digraph_abs (copies_graph vs edges m))) CVi *
  imp_dist_assn (d_dists dist_final) Di *
  idfs_imp.seen_assn SNi * idfs_imp.path_assn res Si *
  \<up>(case res of None \<Rightarrow> True | Some p \<Rightarrow> set p \<subseteq> dVs (CGraph.digraph_abs (copies_graph vs edges m)))"

interpretation dps_imp: Disjoint_Paths_Search_Imperative
  where empty = c_empty and delete = c_delete and lookup = c_lookup and insert = c_insert
    and isin = c_isin and t_set = c_t_set and sel = c_sel and update = c_update
    and adjmap_inv = c_adjmap_inv and vset_empty = c_vset_empty and vset_delete = c_vset_delete
    and vset_inv = c_vset_inv and union = c_union and inter = c_inter and diff = c_diff
    and G = "copies_graph vs edges m" and target = "\<lambda>w. level vs edges m w = 0"
    and blocked = "blocked vs edges m" and initial_roots = "copy_roots vs edges m"
    and search_step = "\<lambda>avoid r vis. IDFS_impl_c (copies_graph vs edges m)
                                       (\<lambda>w. level vs edges m w = 0) avoid [r] vis"
    and search_step_imp = "\<lambda>Ai r Vi. idfs.IDFS_imp Di Gi Ai r Vi SNi Si"
    and commit_path_imp = "commit_path_imp CVi Si" and stack_abstract = stack_abstract
    and step_assn = step_assn and avoided_assn = "\<lambda>A Ai. set_assn (c_t_set A) Ai"
    and explored_assn = "\<lambda>V Vi. set_assn (c_t_set V) Vi" and paths_assn = paths_assn
proof(intro Disjoint_Paths_Search_Imperative.intro Disjoint_Paths_Search_Imperative_axioms.intro
            stk.bounded_stack_imp_axioms, goal_cases)
  case 1
  show ?case
    using phase_search.Disjoint_Paths_Search_axioms copies_graph_layered' copy_roots_in_graph'
          blocked_copies_props'(1,2)
    by (auto intro!: Disjoint_Paths_Search_thms.intro Disjoint_Paths_Search_thms_axioms.intro
             simp: phase_search.Disjoint_Paths_Search_axiom_def)
next
  case (2 A Ai r V Vi)
  have eq: "IDFS_impl_c (copies_graph vs edges m) = idfs_imp.IDFS_impl"
    by (rule IDFS_impl_c_eq[OF copies_graph_layered'])
  have path: "case fst (IDFS_impl_c (copies_graph vs edges m) (\<lambda>w. level vs edges m w = 0) A [r] V)
                of None \<Rightarrow> True | Some p \<Rightarrow> set p \<subseteq> dVs (CGraph.digraph_abs (copies_graph vs edges m))"
  proof(cases "IDFS_impl_c (copies_graph vs edges m) (\<lambda>w. level vs edges m w = 0) A [r] V")
    case (Pair res vis')
    show ?thesis
    proof(cases res)
      case (Some p)
      hence "Vwalk.vwalk (CGraph.digraph_abs (copies_graph vs edges m)) (rev p)"
        using search_step(7)[OF copies_graph_layered' 2, of _ p vis'] Pair
        by blast
      thus ?thesis
        using Pair Some vwalk_then_in_dVs[of _ "rev p"]
        by auto
    qed (simp add: Pair)
  qed
  show ?case
    using 2 path
    unfolding step_assn_def eq
    by (sep_auto heap: idfs_imp.IDFS_imp_rule)
next
  case (3 A Ai p ps Psi)
  have "c_t_set (c_union A (blocked vs edges m p)) =
          c_t_set A \<union> {w \<in> dVs (CGraph.digraph_abs (copies_graph vs edges m)). vtx w \<in> vtx ` set p}"
    using c_set_ops.set_union[OF 3(1) blocked_copies_props'(1)]
    by (simp add: blocked_set)
  then show ?case
    using 3 copies_graph_univ
    unfolding step_assn_def idfs_imp.path_assn_def idfs_imp.stk_assn_def
    by (sep_auto heap: commit_path_rule[of "dVs (CGraph.digraph_abs (copies_graph vs edges m))"])
qed

lemma dps_run_rule:
  "<cgraph_assn (copies_graph vs edges m) Gi * set_assn (dVs (set (copies_edge_list vs edges m))) CVi *
    imp_dist_assn (d_dists dist_final) Di * set_assn {} SNi * stack_assn stack_empty Si *
    (\<exists>\<^sub>AR. stack_assn R Ri * \<up>(stack_invar R \<and> stack_abstract R = copy_roots vs edges m)) *
    set_assn {} Ai * set_assn {} Xi * paths_assn [] Psi>
     dps.Disjoint_Paths_Search_run_imp Di Gi SNi Si CVi Ri Ai Xi Psi
   <\<lambda>si. \<exists>\<^sub>Aps. paths_assn ps (i_paths si) * \<up>(map (map vtx) ps = hopcroft_karp_phase edges vs m)>"
proof-
  have pre:
    "cgraph_assn (copies_graph vs edges m) Gi * set_assn (dVs (set (copies_edge_list vs edges m))) CVi *
     imp_dist_assn (d_dists dist_final) Di * set_assn {} SNi * stack_assn stack_empty Si *
     (\<exists>\<^sub>AR. stack_assn R Ri * \<up>(stack_invar R \<and> stack_abstract R = copy_roots vs edges m)) *
     set_assn {} Ai * set_assn {} Xi * paths_assn [] Psi \<Longrightarrow>\<^sub>A
     step_assn None * dps_imp.roots_assn (copy_roots vs edges m) Ri *
     set_assn (c_t_set c_vset_empty) Ai * set_assn (c_t_set c_vset_empty) Xi * paths_assn [] Psi"
    unfolding step_assn_def idfs_imp.seen_assn_def idfs_imp.path_assn_def idfs_imp.stk_assn_def
              dps_imp.roots_assn_def
    by (sep_auto simp: stk.stack_empty CGraph.vset.set.set_empty)
  have H: "hopcroft_karp_phase edges vs m =
             map (map vtx) (paths (phase_search.Disjoint_Paths_Search_run_impl (blocked vs edges m)
                                     (copy_roots vs edges m) (copies_graph vs edges m)
                                     (\<lambda>w. level vs edges m w = 0)))"
    using m_free
    by (simp add: hopcroft_karp_phase_def Let_def)
  show ?thesis
    by (rule ht_cons_pre[OF pre])
       (sep_auto heap: dps_imp.Disjoint_Paths_Search_run_imp_rule simp: dps_imp.state_assn_def H)
qed

end

end

subsection \<open>The imperative phase\<close>

lemma capacity_vs: "length vs \<le> cap"
  using capacity by simp

lemma hopcroft_karp_phase_imp_rule_free:
  "<edges_assn edges Ei * verts_assn vs Vi * mate_assn m Mi>
     hopcroft_karp_phase_imp Ei Vi Mi
   <\<lambda>Psi. edges_assn edges Ei * verts_assn vs Vi * mate_assn m Mi *
          (\<exists>\<^sub>Aps. paths_assn ps Psi * \<up>(map (map vtx) ps = hopcroft_karp_phase edges vs m))>"
  unfolding hopcroft_karp_phase_imp_def
  using m_free input_in_univ(1,2) dist_final_props(1-5) capacity_vs
  by (sep_auto heap: free_sources_rule alt_graphs_rule vis_empty_rule dist_init_rule bfs_run_rule
                     copies_graph_rule phase_roots_rule set_empty_rule stk.stack_empty_rule
                     paths_empty_rule dps_run_rule
               simp: copies_edges_dist_eq[symmetric] copy_roots_eq[symmetric])

end

text \<open>The imperative phase computes the paths of the functional phase.\<close>

theorem hopcroft_karp_phase_imp_rule:
  assumes "mate_invar (hk_input.ugraph_abs Gin) m"
  shows "<edges_assn edges Ei * verts_assn vs Vi * mate_assn m Mi>
           hopcroft_karp_phase_imp Ei Vi Mi
         <\<lambda>Psi. edges_assn edges Ei * verts_assn vs Vi * mate_assn m Mi *
                (\<exists>\<^sub>Aps. paths_assn ps Psi * \<up>(map (map vtx) ps = hopcroft_karp_phase edges vs m))>"
proof(cases "free_vertices vs m = []")
  case True
  thus ?thesis
    unfolding hopcroft_karp_phase_imp_def
    using input_univ input_props(5)[OF input edges]
    by (sep_auto heap: free_sources_rule paths_empty_rule simp: hopcroft_karp_phase_no_free)
next
  case False
  thus ?thesis
    by (rule hopcroft_karp_phase_imp_rule_free[OF assms])
qed

end

end

end
