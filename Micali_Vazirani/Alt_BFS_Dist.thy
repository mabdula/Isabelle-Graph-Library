theory Alt_BFS_Dist
  imports Alt_BFS
begin

section \<open>The Alternating BFS with Distances Only\<close>

text \<open>A variant of the alternating BFS that does not build the BFS DAG. It keeps the frontier,
      the two visited sets, and the distances of the even and odd copies of the vertices, all of
      which are refined imperatively later on. The visited even set includes the frontier. One
      round is again an odd half-step along the unmatched edges and an even half-step along the
      matched edges. The DAG of the original BFS is determined by the distances: it consists of
      the unmatched edges from an even copy to an odd copy one level further, and of the matched
      edges from an odd copy to an even copy one level further.\<close>

record ('dist, 'vset) Alt_BFS_dist_state =
  d_frontier :: 'vset
  d_vis_even :: 'vset
  d_vis_odd :: 'vset
  d_dists :: 'dist
  d_level :: nat

lemma Vtx_in_image_Vtx[simp]: "Vtx p x \<in> Vtx q ` A \<longleftrightarrow> p = q \<and> x \<in> A"
  by auto

locale Alt_BFS_distance =
  BFS where lookup_neighb = lookup_neighb and lookup_dist = lookup_dist
  for lookup_neighb :: "'adjmap \<Rightarrow> 'ver \<Rightarrow> 'vset option"
  and lookup_dist :: "'dmap \<Rightarrow> 'ver labelled_vtx \<Rightarrow> enat option" +
  fixes next_frontier_and_visited :: "'adjmap \<Rightarrow> 'vset \<Rightarrow> 'vset \<Rightarrow> 'vset \<times> 'vset"
    and set_all_dists :: "'dist \<Rightarrow> parity \<Rightarrow> 'vset \<Rightarrow> nat \<Rightarrow> 'dist"
    and dist_lookup :: "'dist \<Rightarrow> 'ver labelled_vtx \<Rightarrow> nat"
    and dist_invar :: "'dist \<Rightarrow> 'ver labelled_vtx set \<Rightarrow> bool"
    and some_dist :: 'dist
  assumes next_frontier_and_visited:
    "\<And>H F V F' V'. \<lbrakk>vset_inv F; vset_inv V; Graph.graph_inv H; Graph.digraph_abs H \<subseteq> G;
        t_set F \<subseteq> dVs G; t_set V \<subseteq> dVs G; next_frontier_and_visited H F V = (F', V')\<rbrakk>
       \<Longrightarrow> vset_inv F'"
    "\<And>H F V F' V'. \<lbrakk>vset_inv F; vset_inv V; Graph.graph_inv H; Graph.digraph_abs H \<subseteq> G;
        t_set F \<subseteq> dVs G; t_set V \<subseteq> dVs G; next_frontier_and_visited H F V = (F', V')\<rbrakk>
       \<Longrightarrow> t_set F' = next_frontier (Graph.digraph_abs H) (t_set F) (t_set V)"
    "\<And>H F V F' V'. \<lbrakk>vset_inv F; vset_inv V; Graph.graph_inv H; Graph.digraph_abs H \<subseteq> G;
        t_set F \<subseteq> dVs G; t_set V \<subseteq> dVs G; next_frontier_and_visited H F V = (F', V')\<rbrakk>
       \<Longrightarrow> vset_inv V'"
    "\<And>H F V F' V'. \<lbrakk>vset_inv F; vset_inv V; Graph.graph_inv H; Graph.digraph_abs H \<subseteq> G;
        t_set F \<subseteq> dVs G; t_set V \<subseteq> dVs G; next_frontier_and_visited H F V = (F', V')\<rbrakk>
       \<Longrightarrow> t_set V' = t_set V \<union> t_set F'"
  and set_all_dists:
    "\<And>d S p F n. \<lbrakk>vset_inv F; t_set F \<subseteq> dVs G; dist_invar d S\<rbrakk>
       \<Longrightarrow> dist_invar (set_all_dists d p F n) (S \<union> Vtx p ` t_set F)"
    "\<And>d S p F n x. \<lbrakk>vset_inv F; t_set F \<subseteq> dVs G; dist_invar d S; x \<in> t_set F\<rbrakk>
       \<Longrightarrow> dist_lookup (set_all_dists d p F n) (Vtx p x) = n"
    "\<And>d S p F n w. \<lbrakk>vset_inv F; t_set F \<subseteq> dVs G; dist_invar d S; w \<in> S - Vtx p ` t_set F\<rbrakk>
       \<Longrightarrow> dist_lookup (set_all_dists d p F n) w = dist_lookup d w"
  and some_dist: "dist_invar some_dist {}"
  and vset_empty_unique: "\<And>V. \<lbrakk>vset_inv V; t_set V = {}\<rbrakk> \<Longrightarrow> V = \<emptyset>\<^sub>N"
begin

definition "Alt_BFS_dist_upd s =
  (let (F', VO') = next_frontier_and_visited unmatching (d_frontier s) (d_vis_odd s);
       D' = set_all_dists (d_dists s) Odd F' (Suc (d_level s));
       (F'', VE') = next_frontier_and_visited matching F' (d_vis_even s);
       D'' = set_all_dists D' Even F'' (Suc (Suc (d_level s)))
   in s\<lparr>d_frontier := F'', d_vis_even := VE', d_vis_odd := VO', d_dists := D'',
        d_level := Suc (Suc (d_level s))\<rparr>)"

partial_function (tailrec) Alt_BFS_dist_impl ::
  "('dist, 'vset) Alt_BFS_dist_state \<Rightarrow> ('dist, 'vset) Alt_BFS_dist_state" where
  "Alt_BFS_dist_impl s =
     (if d_frontier s \<noteq> \<emptyset>\<^sub>N then
        let (F', VO') = next_frontier_and_visited unmatching (d_frontier s) (d_vis_odd s);
            D' = set_all_dists (d_dists s) Odd F' (Suc (d_level s));
            (F'', VE') = next_frontier_and_visited matching F' (d_vis_even s);
            D'' = set_all_dists D' Even F'' (Suc (Suc (d_level s)))
        in Alt_BFS_dist_impl (s\<lparr>d_frontier := F'', d_vis_even := VE', d_vis_odd := VO',
                                d_dists := D'', d_level := Suc (Suc (d_level s))\<rparr>)
      else s)"

lemma Alt_BFS_dist_impl_simps:
  "d_frontier s \<noteq> \<emptyset>\<^sub>N \<Longrightarrow> Alt_BFS_dist_impl s = Alt_BFS_dist_impl (Alt_BFS_dist_upd s)"
  "d_frontier s = \<emptyset>\<^sub>N \<Longrightarrow> Alt_BFS_dist_impl s = s"
  by (subst Alt_BFS_dist_impl.simps, simp add: Alt_BFS_dist_upd_def Let_def split: prod.split)+

definition "initial_dist_state =
  \<lparr>d_frontier = srcs, d_vis_even = srcs, d_vis_odd = \<emptyset>\<^sub>N,
   d_dists = set_all_dists some_dist Even srcs 0, d_level = 0\<rparr>"

lemmas [code] = Alt_BFS_dist_impl.simps initial_dist_state_def

text \<open>The DAG determined by the visited sets and the distances.\<close>

definition "dist_dag VE VO d =
  {(u, v) | u v. (u, v) \<in> Graph.digraph_abs unmatching \<and> u \<in> VE \<and> v \<in> VO \<and>
                 d (Vtx Odd v) = d (Vtx Even u) + 1} \<union>
  {(u, v) | u v. (u, v) \<in> Graph.digraph_abs matching \<and> u \<in> VO \<and> v \<in> VE \<and>
                 d (Vtx Even v) = d (Vtx Odd u) + 1}"

lemma next_frontier_dVs: "next_frontier H A B \<subseteq> dVs H"
  by (auto simp: next_frontier_def Pair_Graph.neighbourhood_def dVs_def)

lemma next_frontier_disjoint: "next_frontier H A B \<inter> B = {}"
  by (auto simp: next_frontier_def)

lemma unmatching_matching_in_G: "Graph.digraph_abs unmatching \<subseteq> G" "Graph.digraph_abs matching \<subseteq> G"
  by (auto simp: G_def)

subsection \<open>Simulation of the original BFS\<close>

text \<open>The relation between a state of the original BFS and a state of the distance BFS.\<close>

definition "dist_rel s t =
  (vset_inv (d_frontier t) \<and> vset_inv (d_vis_even t) \<and> vset_inv (d_vis_odd t) \<and>
   dist_invar (d_dists t) (Vtx Even ` t_set (d_vis_even t) \<union> Vtx Odd ` t_set (d_vis_odd t)) \<and>
   t_set (d_frontier t) = t_set (current s) \<and>
   t_set (d_vis_even t) = t_set (visited_even s) \<union> t_set (current s) \<and>
   t_set (d_vis_odd t) = t_set (visited_odd s) \<and>
   t_set (d_frontier t) \<subseteq> t_set (d_vis_even t) \<and>
   t_set (d_vis_even t) \<subseteq> dVs G \<and> t_set (d_vis_odd t) \<subseteq> dVs G \<and>
   (\<forall>v \<in> t_set (d_vis_even t).
      lookup_dist (distances s) (Vtx Even v) = Some (enat (dist_lookup (d_dists t) (Vtx Even v))) \<and>
      dist_lookup (d_dists t) (Vtx Even v) \<le> d_level t \<and>
      (v \<in> t_set (d_frontier t) \<longleftrightarrow> dist_lookup (d_dists t) (Vtx Even v) = d_level t)) \<and>
   (\<forall>v \<in> t_set (d_vis_odd t).
      lookup_dist (distances s) (Vtx Odd v) = Some (enat (dist_lookup (d_dists t) (Vtx Odd v))) \<and>
      dist_lookup (d_dists t) (Vtx Odd v) < d_level t) \<and>
   Graph.digraph_abs (parents s) =
     dist_dag (t_set (d_vis_even t)) (t_set (d_vis_odd t)) (dist_lookup (d_dists t)))"

context
  includes Graph.adjmap.automation and Graph.vset.set.automation and set_ops.automation2
  assumes BFS_axiom: BFS_axiom
begin

lemma srcs_props: "vset_inv srcs" "t_set srcs \<subseteq> dVs G"
  using srcs_invar(2)[OF BFS_axiom] srcs_in_G[OF BFS_axiom] dVs_subset[OF unmatching_matching_in_G(1)]
  by auto

lemma dist_rel_initial: "dist_rel initial_state initial_dist_state"
  using set_all_dists(1)[OF srcs_props some_dist, of Even 0]
        set_all_dists(2)[OF srcs_props some_dist, of _ Even 0] srcs_props
  by (auto simp: dist_rel_def initial_state_def initial_dist_state_def dist_dag_def zero_enat_def)
lemma dist_rel_frontier_empty:
  assumes "dist_rel s t" "invar_well_formed s"
  shows "current s = \<emptyset>\<^sub>N \<longleftrightarrow> d_frontier t = \<emptyset>\<^sub>N"
  using assms vset_empty_unique[of "d_frontier t"] vset_empty_unique[of "current s"]
  by (auto simp: dist_rel_def invar_well_formed_def)

lemma dist_rel_step:
  assumes "current s \<noteq> \<emptyset>\<^sub>N" "invar_well_formed s" "dist_rel s t"
  shows "dist_rel (BFS_upd1 s) (Alt_BFS_dist_upd t)"
proof-
  obtain F' VO' where nf1: "next_frontier_and_visited unmatching (d_frontier t) (d_vis_odd t) = (F', VO')"
    by (cases "next_frontier_and_visited unmatching (d_frontier t) (d_vis_odd t)") auto
  obtain F'' VE' where nf2: "next_frontier_and_visited matching F' (d_vis_even t) = (F'', VE')"
    by (cases "next_frontier_and_visited matching F' (d_vis_even t)") auto
  define k where "k = d_level t"
  define d where "d = d_dists t"
  define D' where "D' = set_all_dists d Odd F' (Suc k)"
  define D'' where "D'' = set_all_dists D' Even F'' (Suc (Suc k))"
  have upd: "Alt_BFS_dist_upd t = t\<lparr>d_frontier := F'', d_vis_even := VE', d_vis_odd := VO',
                                    d_dists := D'', d_level := Suc (Suc k)\<rparr>"
    by (simp add: Alt_BFS_dist_upd_def nf1 nf2 D'_def D''_def d_def k_def)
  note wf = assms(2)[unfolded invar_well_formed_def]
  note gi = graph_inv[OF BFS_axiom]
  define L where "L = dist_lookup d"
  have R: "vset_inv (d_frontier t)" "vset_inv (d_vis_even t)" "vset_inv (d_vis_odd t)"
     "dist_invar d (Vtx Even ` t_set (d_vis_even t) \<union> Vtx Odd ` t_set (d_vis_odd t))"
     "t_set (d_frontier t) = t_set (current s)"
     "t_set (d_vis_even t) = t_set (visited_even s) \<union> t_set (current s)"
     "t_set (d_vis_odd t) = t_set (visited_odd s)"
     "t_set (d_frontier t) \<subseteq> t_set (d_vis_even t)"
     "t_set (d_vis_even t) \<subseteq> dVs G" "t_set (d_vis_odd t) \<subseteq> dVs G"
     "\<And>v. v \<in> t_set (d_vis_even t) \<Longrightarrow>
        lookup_dist (distances s) (Vtx Even v) = Some (enat (L (Vtx Even v)))"
     "\<And>v. v \<in> t_set (d_vis_even t) \<Longrightarrow> L (Vtx Even v) \<le> k"
     "\<And>v. v \<in> t_set (d_vis_even t) \<Longrightarrow> v \<in> t_set (d_frontier t) \<longleftrightarrow> L (Vtx Even v) = k"
     "\<And>v. v \<in> t_set (d_vis_odd t) \<Longrightarrow>
        lookup_dist (distances s) (Vtx Odd v) = Some (enat (L (Vtx Odd v)))"
     "\<And>v. v \<in> t_set (d_vis_odd t) \<Longrightarrow> L (Vtx Odd v) < k"
     "Graph.digraph_abs (parents s) = dist_dag (t_set (d_vis_even t)) (t_set (d_vis_odd t)) L"
    using assms(3) unfolding dist_rel_def L_def d_def k_def by blast+
  have F_G: "t_set (d_frontier t) \<subseteq> dVs G"
    using R(8,9) by blast
  note N1 = next_frontier_and_visited[OF R(1,3) gi(3) unmatching_matching_in_G(1) F_G R(10) nf1]
  have F'_G: "t_set F' \<subseteq> dVs G"
    unfolding N1(2) by (rule subset_trans[OF next_frontier_dVs dVs_subset[OF unmatching_matching_in_G(1)]])
  have F'_TO: "t_set F' \<inter> t_set (d_vis_odd t) = {}"
    unfolding N1(2) by (rule next_frontier_disjoint)
  note N2 = next_frontier_and_visited[OF N1(1) R(2) gi(1) unmatching_matching_in_G(2) F'_G R(9) nf2]
  have F''_G: "t_set F'' \<subseteq> dVs G"
    unfolding N2(2) by (rule subset_trans[OF next_frontier_dVs dVs_subset[OF unmatching_matching_in_G(2)]])
  have F''_TE: "t_set F'' \<inter> t_set (d_vis_even t) = {}"
    unfolding N2(2) by (rule next_frontier_disjoint)  text \<open>The distances of the distance BFS.\<close>
  have DI1: "dist_invar D' (Vtx Even ` t_set (d_vis_even t) \<union> Vtx Odd ` t_set (d_vis_odd t) \<union>
                             Vtx Odd ` t_set F')"
    unfolding D'_def by (rule set_all_dists(1)[OF N1(1) F'_G R(4)])
  have DI2: "dist_invar D'' (Vtx Even ` t_set (d_vis_even t) \<union> Vtx Odd ` t_set (d_vis_odd t) \<union>
                              Vtx Odd ` t_set F' \<union> Vtx Even ` t_set F'')"
    unfolding D''_def by (rule set_all_dists(1)[OF N2(1) F''_G DI1])
  have LO2: "dist_lookup D'' (Vtx Odd x) = Suc k" if "x \<in> t_set F'" for x
    using that set_all_dists(3)[OF N2(1) F''_G DI1, where w = "Vtx Odd x" and p = Even
                                and n = "Suc (Suc k)"]
          set_all_dists(2)[OF N1(1) F'_G R(4) that, where p = Odd and n = "Suc k"]
    by (auto simp add: D''_def D'_def)
  have LO1: "dist_lookup D'' (Vtx Odd x) = L (Vtx Odd x)" if "x \<in> t_set (d_vis_odd t)" for x
  proof-
    have "x \<notin> t_set F'"
      using that F'_TO by blast
    hence "dist_lookup D' (Vtx Odd x) = L (Vtx Odd x)"
      using that set_all_dists(3)[OF N1(1) F'_G R(4), where w = "Vtx Odd x" and p = Odd and n = "Suc k"]
      by (auto simp add: D'_def L_def)
    moreover have "dist_lookup D'' (Vtx Odd x) = dist_lookup D' (Vtx Odd x)"
      using that set_all_dists(3)[OF N2(1) F''_G DI1, where w = "Vtx Odd x" and p = Even
                                   and n = "Suc (Suc k)"]
      by (auto simp add: D''_def)
    ultimately show ?thesis
      by simp
  qed  have LE2: "dist_lookup D'' (Vtx Even x) = Suc (Suc k)" if "x \<in> t_set F''" for x
    using set_all_dists(2)[OF N2(1) F''_G DI1 that] by (simp add: D''_def)
  have LE1: "dist_lookup D'' (Vtx Even x) = L (Vtx Even x)" if "x \<in> t_set (d_vis_even t)" for x
  proof-
    have "x \<notin> t_set F''"
      using that F''_TE by blast
    hence "dist_lookup D'' (Vtx Even x) = dist_lookup D' (Vtx Even x)"
      using that set_all_dists(3)[OF N2(1) F''_G DI1, where w = "Vtx Even x" and p = Even
                                   and n = "Suc (Suc k)"]
      by (auto simp add: D''_def)
    moreover have "dist_lookup D' (Vtx Even x) = L (Vtx Even x)"
      using that set_all_dists(3)[OF N1(1) F'_G R(4), where w = "Vtx Even x" and p = Odd and n = "Suc k"]
      by (auto simp add: D'_def L_def)
    ultimately show ?thesis
      by simp
  qed
  text \<open>The step of the original BFS.\<close>  have wfs: "vset_inv (visited_even s)" "vset_inv (visited_odd s)" "vset_inv (current s)"
            "Graph.graph_inv (parents s)" "invar_dist (distances s)"
    using wf by auto
  define C' where "C' = next_frontier_impl unmatching (current s) (visited_odd s)"
  define VEs where "VEs = visited_even s \<union>\<^sub>G current s"
  define C'' where "C'' = next_frontier_impl matching C' VEs"
  define VOs where "VOs = visited_odd s \<union>\<^sub>G C'"
  define D1 where "D1 = upd_dists Odd unmatching (distances s) (current s) (visited_odd s)"
  define D2 where "D2 = upd_dists Even matching D1 C' VEs"
  define P1 where "P1 = expand_tree unmatching (parents s) (current s) (visited_odd s)"
  define P2 where "P2 = expand_tree matching P1 C' VEs"
  have upd1: "BFS_upd1 s = s\<lparr>parents := P2, visited_even := VEs, visited_odd := VOs,
                             current := C'', distances := D2\<rparr>"
    by (simp add: BFS_upd1_def Let_def C'_def VEs_def C''_def VOs_def D1_def D2_def P1_def P2_def)
  have C': "vset_inv C'" "t_set C' = t_set F'"
    using next_frontier[OF wfs(3,2) gi(3)] N1(2) R(5,7) by (simp_all add: C'_def)
  have VEs: "vset_inv VEs" "t_set VEs = t_set (d_vis_even t)"
    using wfs R(6) by (simp_all add: VEs_def)
  have C'': "vset_inv C''" "t_set C'' = t_set F''"
    using next_frontier[OF C'(1) VEs(1) gi(1)] N2(2) C'(2) VEs(2) by (simp_all add: C''_def)
  have VOs: "vset_inv VOs" "t_set VOs = t_set VO'"
    using wfs C' N1(4) R(7) by (simp_all add: VOs_def)
  have D1_inv: "invar_dist D1"
    using wfs gi by (simp add: D1_def)
  have SD1: "lookup_dist D1 (Vtx Odd x) = Some (enat (Suc k))" if "x \<in> t_set F'" for x
  proof-
    have "x \<in> next_frontier (Graph.digraph_abs unmatching) (t_set (current s)) (t_set (visited_odd s))"
      using that N1(2) R(5,7) by simp
    then obtain u where u: "u \<in> t_set (current s)"
        "lookup_dist D1 (Vtx Odd x) = Some (the (lookup_dist (distances s) (Vtx Even u)) + 1)"
      using upd_dists(2)[OF wfs(5,3,2) gi(3), where parity = Odd] unfolding D1_def
      by (auto simp: other_parity)    have "u \<in> t_set (d_vis_even t)" "u \<in> t_set (d_frontier t)"
      using u(1) R(5,8) by auto
    hence "lookup_dist (distances s) (Vtx Even u) = Some (enat k)"
      using R(11,13) by auto
    thus ?thesis
      using u(2) by (simp add: eSuc_plus_1)
  qed
  have SD2_O: "lookup_dist D2 (Vtx Odd x) = Some (enat (Suc k))" if "x \<in> t_set F'" for x
    using SD1[OF that] upd_dists(3)[OF D1_inv C'(1) VEs(1) gi(1), where parity = Even and w = "Vtx Odd x"]
    by (simp add: D2_def)
  have SD2_E: "lookup_dist D2 (Vtx Even x) = Some (enat (Suc (Suc k)))" if "x \<in> t_set F''" for x
  proof-
    have "x \<in> next_frontier (Graph.digraph_abs matching) (t_set C') (t_set VEs)"
      using that N2(2) C'(2) VEs(2) by simp
    then obtain u where u: "u \<in> t_set C'"
        "lookup_dist D2 (Vtx Even x) = Some (the (lookup_dist D1 (Vtx Odd u)) + 1)"
      using upd_dists(2)[OF D1_inv C'(1) VEs(1) gi(1), where parity = Even] unfolding D2_def
      by (auto simp: other_parity)
    thus ?thesis
      using SD1[of u] C'(2) by (simp add: eSuc_plus_1)
  qed
  have SD2_O_old: "lookup_dist D2 (Vtx Odd x) = lookup_dist (distances s) (Vtx Odd x)"
    if "x \<in> t_set (d_vis_odd t)" for x
  proof-
    have "x \<notin> next_frontier (Graph.digraph_abs unmatching) (t_set (current s)) (t_set (visited_odd s))"
      using that R(7) by (auto simp: next_frontier_def)
    thus ?thesis
      using upd_dists(3)[OF wfs(5,3,2) gi(3), where parity = Odd and w = "Vtx Odd x"]
            upd_dists(3)[OF D1_inv C'(1) VEs(1) gi(1), where parity = Even and w = "Vtx Odd x"]
      by (auto simp: D2_def D1_def)
  qed
  have SD2_E_old: "lookup_dist D2 (Vtx Even x) = lookup_dist (distances s) (Vtx Even x)"
    if "x \<in> t_set (d_vis_even t)" for x
  proof-
    have "x \<notin> next_frontier (Graph.digraph_abs matching) (t_set C') (t_set VEs)"
      using that VEs(2) by (auto simp: next_frontier_def)
    thus ?thesis
      using upd_dists(3)[OF wfs(5,3,2) gi(3), where parity = Odd and w = "Vtx Even x"]
            upd_dists(3)[OF D1_inv C'(1) VEs(1) gi(1), where parity = Even and w = "Vtx Even x"]
      by (auto simp: D2_def D1_def)
  qed
  have P1_inv: "Graph.graph_inv P1"
    using expand_tree(1)[OF wfs(4,3,2) gi(3)] by (simp add: P1_def)
  have P1_abs: "Graph.digraph_abs P1 = Graph.digraph_abs (parents s) \<union>
                  new_edges (Graph.digraph_abs unmatching) (t_set (d_frontier t)) (t_set (d_vis_odd t))"
    using expand_tree(2)[OF wfs(4,3,2) gi(3)] R(5,7) by (simp add: P1_def)
  have P2_abs: "Graph.digraph_abs P2 = Graph.digraph_abs P1 \<union>
                  new_edges (Graph.digraph_abs matching) (t_set F') (t_set (d_vis_even t))"
    using expand_tree(2)[OF P1_inv C'(1) VEs(1) gi(1)] C'(2) VEs(2) by (simp add: P2_def)
  have U: "{(u, v) | u v. (u, v) \<in> Graph.digraph_abs unmatching \<and>
              u \<in> t_set (d_vis_even t) \<union> t_set F'' \<and> v \<in> t_set (d_vis_odd t) \<union> t_set F' \<and>
              dist_lookup D'' (Vtx Odd v) = dist_lookup D'' (Vtx Even u) + 1} =
           {(u, v) | u v. (u, v) \<in> Graph.digraph_abs unmatching \<and>
              u \<in> t_set (d_vis_even t) \<and> v \<in> t_set (d_vis_odd t) \<and>
              L (Vtx Odd v) = L (Vtx Even u) + 1} \<union>
           new_edges (Graph.digraph_abs unmatching) (t_set (d_frontier t)) (t_set (d_vis_odd t))"
  proof(intro equalityI subsetI)
    fix e
    assume "e \<in> {(u, v) | u v. (u, v) \<in> Graph.digraph_abs unmatching \<and>
              u \<in> t_set (d_vis_even t) \<union> t_set F'' \<and> v \<in> t_set (d_vis_odd t) \<union> t_set F' \<and>
              dist_lookup D'' (Vtx Odd v) = dist_lookup D'' (Vtx Even u) + 1}"
    then obtain u v where e: "e = (u, v)" "(u, v) \<in> Graph.digraph_abs unmatching"
        "u \<in> t_set (d_vis_even t) \<union> t_set F''" "v \<in> t_set (d_vis_odd t) \<union> t_set F'"
        "dist_lookup D'' (Vtx Odd v) = dist_lookup D'' (Vtx Even u) + 1"
      by blast
    have v_le: "dist_lookup D'' (Vtx Odd v) \<le> Suc k"
      using e(4) LO1 LO2 R(15) by (fastforce simp: L_def)
    have u: "u \<in> t_set (d_vis_even t)"
      using e(3,5) v_le LE2 by force
    hence u_val: "dist_lookup D'' (Vtx Even u) = L (Vtx Even u)"
      by (rule LE1)
    show "e \<in> {(u, v) | u v. (u, v) \<in> Graph.digraph_abs unmatching \<and>
              u \<in> t_set (d_vis_even t) \<and> v \<in> t_set (d_vis_odd t) \<and>
              L (Vtx Odd v) = L (Vtx Even u) + 1} \<union>
           new_edges (Graph.digraph_abs unmatching) (t_set (d_frontier t)) (t_set (d_vis_odd t))"
    proof(cases "v \<in> t_set (d_vis_odd t)")
      case True
      thus ?thesis
        using e u u_val LO1[OF True] by auto
    next
      case False
      hence "v \<in> t_set F'"
        using e(4) by blast
      hence "L (Vtx Even u) = k"
        using e(5) u_val LO2 by simp
      hence "u \<in> t_set (d_frontier t)"
        using R(13)[OF u] by simp
      thus ?thesis
        using e(1,2) False by (auto simp: new_edges_def Pair_Graph.neighbourhood_def)
    qed
  next
    fix e
    assume "e \<in> {(u, v) | u v. (u, v) \<in> Graph.digraph_abs unmatching \<and>
              u \<in> t_set (d_vis_even t) \<and> v \<in> t_set (d_vis_odd t) \<and>
              L (Vtx Odd v) = L (Vtx Even u) + 1} \<union>
           new_edges (Graph.digraph_abs unmatching) (t_set (d_frontier t)) (t_set (d_vis_odd t))"
    thus "e \<in> {(u, v) | u v. (u, v) \<in> Graph.digraph_abs unmatching \<and>
              u \<in> t_set (d_vis_even t) \<union> t_set F'' \<and> v \<in> t_set (d_vis_odd t) \<union> t_set F' \<and>
              dist_lookup D'' (Vtx Odd v) = dist_lookup D'' (Vtx Even u) + 1}"
    proof(elim UnE)
      assume "e \<in> {(u, v) | u v. (u, v) \<in> Graph.digraph_abs unmatching \<and>
              u \<in> t_set (d_vis_even t) \<and> v \<in> t_set (d_vis_odd t) \<and>
              L (Vtx Odd v) = L (Vtx Even u) + 1}"
      thus ?thesis
        using LE1 LO1 by auto
    next
      assume "e \<in> new_edges (Graph.digraph_abs unmatching) (t_set (d_frontier t)) (t_set (d_vis_odd t))"
      then obtain u v where e: "e = (u, v)" "u \<in> t_set (d_frontier t)" "(u, v) \<in> Graph.digraph_abs unmatching"
          "v \<notin> t_set (d_vis_odd t)"
        by (auto simp: new_edges_def Pair_Graph.neighbourhood_def)
      hence "v \<in> t_set F'"
        using N1(2) by (auto simp: next_frontier_def Pair_Graph.neighbourhood_def)
      moreover have "u \<in> t_set (d_vis_even t)" "L (Vtx Even u) = k"
        using e(2) R(8,13) by auto
      ultimately show ?thesis
        using e(1,3) LE1 LO2 by auto
    qed
  qed
  have M: "{(u, v) | u v. (u, v) \<in> Graph.digraph_abs matching \<and>
              u \<in> t_set (d_vis_odd t) \<union> t_set F' \<and> v \<in> t_set (d_vis_even t) \<union> t_set F'' \<and>
              dist_lookup D'' (Vtx Even v) = dist_lookup D'' (Vtx Odd u) + 1} =
           {(u, v) | u v. (u, v) \<in> Graph.digraph_abs matching \<and>
              u \<in> t_set (d_vis_odd t) \<and> v \<in> t_set (d_vis_even t) \<and>
              L (Vtx Even v) = L (Vtx Odd u) + 1} \<union>
           new_edges (Graph.digraph_abs matching) (t_set F') (t_set (d_vis_even t))"
  proof(intro equalityI subsetI)
    fix e
    assume "e \<in> {(u, v) | u v. (u, v) \<in> Graph.digraph_abs matching \<and>
              u \<in> t_set (d_vis_odd t) \<union> t_set F' \<and> v \<in> t_set (d_vis_even t) \<union> t_set F'' \<and>
              dist_lookup D'' (Vtx Even v) = dist_lookup D'' (Vtx Odd u) + 1}"
    then obtain u v where e: "e = (u, v)" "(u, v) \<in> Graph.digraph_abs matching"
        "u \<in> t_set (d_vis_odd t) \<union> t_set F'" "v \<in> t_set (d_vis_even t) \<union> t_set F''"
        "dist_lookup D'' (Vtx Even v) = dist_lookup D'' (Vtx Odd u) + 1"
      by blast
    show "e \<in> {(u, v) | u v. (u, v) \<in> Graph.digraph_abs matching \<and>
              u \<in> t_set (d_vis_odd t) \<and> v \<in> t_set (d_vis_even t) \<and>
              L (Vtx Even v) = L (Vtx Odd u) + 1} \<union>
           new_edges (Graph.digraph_abs matching) (t_set F') (t_set (d_vis_even t))"
    proof(cases "u \<in> t_set (d_vis_odd t)")
      case True
      hence u_val: "dist_lookup D'' (Vtx Odd u) < k"
        using LO1 R(15) by (simp add: L_def)
      have v: "v \<in> t_set (d_vis_even t)"
        using e(4,5) u_val LE2 by force
      thus ?thesis
        using e True LO1[OF True] LE1[OF v] by auto
    next
      case False
      hence u: "u \<in> t_set F'"
        using e(3) by blast
      hence "dist_lookup D'' (Vtx Even v) = Suc (Suc k)"
        using e(5) LO2 by simp
      hence "v \<notin> t_set (d_vis_even t)"
        using LE1 R(12) by fastforce
      thus ?thesis
        using e(1,2) u by (auto simp: new_edges_def Pair_Graph.neighbourhood_def)
    qed
  next
    fix e
    assume "e \<in> {(u, v) | u v. (u, v) \<in> Graph.digraph_abs matching \<and>
              u \<in> t_set (d_vis_odd t) \<and> v \<in> t_set (d_vis_even t) \<and>
              L (Vtx Even v) = L (Vtx Odd u) + 1} \<union>
           new_edges (Graph.digraph_abs matching) (t_set F') (t_set (d_vis_even t))"
    thus "e \<in> {(u, v) | u v. (u, v) \<in> Graph.digraph_abs matching \<and>
              u \<in> t_set (d_vis_odd t) \<union> t_set F' \<and> v \<in> t_set (d_vis_even t) \<union> t_set F'' \<and>
              dist_lookup D'' (Vtx Even v) = dist_lookup D'' (Vtx Odd u) + 1}"
    proof(elim UnE)
      assume "e \<in> {(u, v) | u v. (u, v) \<in> Graph.digraph_abs matching \<and>
              u \<in> t_set (d_vis_odd t) \<and> v \<in> t_set (d_vis_even t) \<and>
              L (Vtx Even v) = L (Vtx Odd u) + 1}"
      thus ?thesis
        using LE1 LO1 by auto
    next
      assume "e \<in> new_edges (Graph.digraph_abs matching) (t_set F') (t_set (d_vis_even t))"
      then obtain u v where e: "e = (u, v)" "u \<in> t_set F'" "(u, v) \<in> Graph.digraph_abs matching"
          "v \<notin> t_set (d_vis_even t)"
        by (auto simp: new_edges_def Pair_Graph.neighbourhood_def)
      hence "v \<in> t_set F''"
        using N2(2) by (auto simp: next_frontier_def Pair_Graph.neighbourhood_def)
      thus ?thesis
        using e(1-3) LE2 LO2 by auto
    qed
  qed
  have DAG: "Graph.digraph_abs P2 = dist_dag (t_set VE') (t_set VO') (dist_lookup D'')"
    unfolding P2_abs P1_abs R(16) N1(4) N2(4) dist_dag_def U M
    by (simp only: Un_ac)
  have EV: "\<forall>v \<in> t_set VE'.
      lookup_dist D2 (Vtx Even v) = Some (enat (dist_lookup D'' (Vtx Even v))) \<and>
      dist_lookup D'' (Vtx Even v) \<le> Suc (Suc k) \<and>
      (v \<in> t_set F'' \<longleftrightarrow> dist_lookup D'' (Vtx Even v) = Suc (Suc k))"
  proof
    fix v
    assume "v \<in> t_set VE'"
    hence "v \<in> t_set (d_vis_even t) \<or> v \<in> t_set F''"
      using N2(4) by blast
    thus "lookup_dist D2 (Vtx Even v) = Some (enat (dist_lookup D'' (Vtx Even v))) \<and>
      dist_lookup D'' (Vtx Even v) \<le> Suc (Suc k) \<and>
      (v \<in> t_set F'' \<longleftrightarrow> dist_lookup D'' (Vtx Even v) = Suc (Suc k))"
    proof
      assume v: "v \<in> t_set (d_vis_even t)"
      hence "v \<notin> t_set F''"
        using F''_TE by blast
      thus ?thesis
        using v LE1[OF v] SD2_E_old[OF v] R(11,12)[OF v] by simp
    qed (simp add: LE2 SD2_E)
  qed
  have OD: "\<forall>v \<in> t_set VO'.
      lookup_dist D2 (Vtx Odd v) = Some (enat (dist_lookup D'' (Vtx Odd v))) \<and>
      dist_lookup D'' (Vtx Odd v) < Suc (Suc k)"
  proof
    fix v
    assume "v \<in> t_set VO'"
    hence "v \<in> t_set (d_vis_odd t) \<or> v \<in> t_set F'"
      using N1(4) by blast
    thus "lookup_dist D2 (Vtx Odd v) = Some (enat (dist_lookup D'' (Vtx Odd v))) \<and>
      dist_lookup D'' (Vtx Odd v) < Suc (Suc k)"
    proof
      assume v: "v \<in> t_set (d_vis_odd t)"
      thus ?thesis
        using LO1[OF v] SD2_O_old[OF v] R(14,15)[OF v] by simp
    qed (simp add: LO2 SD2_O)
  qed
  have DI: "dist_invar D'' (Vtx Even ` t_set VE' \<union> Vtx Odd ` t_set VO')"
  proof-
    have "Vtx Even ` t_set VE' \<union> Vtx Odd ` t_set VO' =
          Vtx Even ` t_set (d_vis_even t) \<union> Vtx Odd ` t_set (d_vis_odd t) \<union>
          Vtx Odd ` t_set F' \<union> Vtx Even ` t_set F''"
      using N1(4) N2(4) by auto
    thus ?thesis
      using DI2 by simp
  qed
  have VE'_G: "t_set VE' \<subseteq> dVs G" and VO'_G: "t_set VO' \<subseteq> dVs G"
    using N1(4) N2(4) R(9,10) F'_G F''_G by auto
  show ?thesis
    unfolding dist_rel_def upd upd1
    using N1(1,3) N2(1,3) DI C''(2) VEs(2) N2(4) VOs(2) VE'_G VO'_G EV OD DAG
    by (auto simp: k_def)
qed

lemma dist_rel_holds:
  assumes "BFS_dom s" "invar_well_formed s" "dist_rel s t"
  shows "dist_rel (BFS s) (Alt_BFS_dist_impl t)"
  using assms(2,3)
proof(induction arbitrary: t rule: BFS_induct[OF BFS_axiom assms(1)])
  case (1 s)
  show ?case
  proof(cases "current s = \<emptyset>\<^sub>N")
    case True
    hence "d_frontier t = \<emptyset>\<^sub>N"
      using dist_rel_frontier_empty[OF 1(4,3)] by simp
    thus ?thesis
      using True 1(4) BFS_simps(2)[OF BFS_axiom 1(1) BFS_ret_1_condsI[OF BFS_axiom True]]
            Alt_BFS_dist_impl_simps(2)
      by simp
  next
    case False
    hence call: "BFS_call_1_conds s"
      by (simp add: BFS_call_1_conds_def)
    have "d_frontier t \<noteq> \<emptyset>\<^sub>N"
      using False dist_rel_frontier_empty[OF 1(4,3)] by simp
    thus ?thesis
      using 1(2)[OF call invar_well_formed_holds_upd1[OF BFS_axiom call 1(3)]
                 dist_rel_step[OF False 1(3,4)]]
            BFS_simps(1)[OF BFS_axiom 1(1) call] Alt_BFS_dist_impl_simps(1)
      by simp
  qed
qed

subsection \<open>Correctness\<close>

lemma dist_rel_final: "dist_rel (BFS initial_state) (Alt_BFS_dist_impl initial_dist_state)"
  by (rule dist_rel_holds[OF BFS_terminates[OF BFS_axiom] _ dist_rel_initial])
     (intro initial_state_props[OF BFS_axiom])+

text \<open>The distance BFS computes the visited sets and the distances of the original BFS, and its
      distances determine the DAG of the original BFS. Thus all results on the latter, e.g.\
      @{thm [source] BFS_valid_DAG}, carry over.\<close>

theorem Alt_BFS_dist_correct:
  defines "final \<equiv> Alt_BFS_dist_impl initial_dist_state"
  shows "vset_inv (d_vis_even final)" "vset_inv (d_vis_odd final)"
        "dist_invar (d_dists final) (Vtx Even ` t_set (d_vis_even final) \<union> Vtx Odd ` t_set (d_vis_odd final))"
        "t_set (d_vis_even final) = t_set (visited_even (BFS initial_state))"
        "t_set (d_vis_odd final) = t_set (visited_odd (BFS initial_state))"
        "v \<in> t_set (d_vis_even final) \<Longrightarrow> enat (dist_lookup (d_dists final) (Vtx Even v)) = altd_G Even v"
        "v \<in> t_set (d_vis_odd final) \<Longrightarrow> enat (dist_lookup (d_dists final) (Vtx Odd v)) = altd_G Odd v"
        "Graph.digraph_abs (parents (BFS initial_state)) =
           dist_dag (t_set (d_vis_even final)) (t_set (d_vis_odd final)) (dist_lookup (d_dists final))"
proof-
  note R = dist_rel_final[folded final_def, unfolded dist_rel_def]
  note P = valid_alt_BFS_DAG_props[OF BFS_axiom BFS_valid_DAG[OF BFS_axiom]]
  note CE = BFS_final_current_empty[OF BFS_axiom]
  show "vset_inv (d_vis_even final)" "vset_inv (d_vis_odd final)"
       "dist_invar (d_dists final) (Vtx Even ` t_set (d_vis_even final) \<union> Vtx Odd ` t_set (d_vis_odd final))"
       "t_set (d_vis_even final) = t_set (visited_even (BFS initial_state))"
       "t_set (d_vis_odd final) = t_set (visited_odd (BFS initial_state))"
       "Graph.digraph_abs (parents (BFS initial_state)) =
          dist_dag (t_set (d_vis_even final)) (t_set (d_vis_odd final)) (dist_lookup (d_dists final))"
    using R CE by auto
  show "enat (dist_lookup (d_dists final) (Vtx Even v)) = altd_G Even v"
    if "v \<in> t_set (d_vis_even final)"
    using that R CE P(9)[of v] by auto
  show "enat (dist_lookup (d_dists final) (Vtx Odd v)) = altd_G Odd v"
    if "v \<in> t_set (d_vis_odd final)"
    using that R P(8)[of v] by auto
qed

end

end

end