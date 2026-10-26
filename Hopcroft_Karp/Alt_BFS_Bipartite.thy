theory Alt_BFS_Bipartite
  imports Micali_Vazirani.Top_Loop "Basic_Matching.Berge"
begin

section \<open>Walks of the Alternating BFS Copies Graph in Bipartite Graphs\<close>

text \<open>In a bipartite graph, the walks of the alternating BFS copies graph from a free odd
  copy down to level 0 are exactly the (reversed) augmenting paths.\<close>

subsection \<open>Walk lemmas\<close>

lemma vwalk_bet_level_distinct:
  assumes "Vwalk.vwalk_bet E w q z" "\<And>a b. (a, b) \<in> E \<Longrightarrow> lv b < (lv a :: nat)"
  shows "distinct q \<and> (\<forall>x \<in> set q. lv x \<le> lv w)"
  using assms(1)
proof(induction rule: induct_vwalk_bet)
  case (path2 v v' vs b)
  hence "lv v' < lv v"
    by (auto intro: assms(2))
  thus ?case
    using path2(3)
    by (fastforce dest: leD intro: less_imp_le_nat le_less_trans)
qed simp

lemma alt_list_edges_of_vwalk_path:
  "\<lbrakk>alt_list P1 P2 (edges_of_vwalk p); \<And>u v. P1 (u, v) \<Longrightarrow> Q1 {u, v};
    \<And>u v. P2 (u, v) \<Longrightarrow> Q2 {u, v}\<rbrakk>
   \<Longrightarrow> alt_list Q1 Q2 (edges_of_path p)"
  by (induction p arbitrary: P1 P2 Q1 Q2 rule: edges_of_path.induct)
     (auto simp: alt_list_empty alt_list_step)

lemma alt_list_edges_of_path_vwalk:
  "\<lbrakk>alt_list Q1 Q2 (edges_of_path p);
    \<And>u v. \<lbrakk>{u, v} \<in> set (edges_of_path p); Q1 {u, v}\<rbrakk> \<Longrightarrow> P1 (u, v);
    \<And>u v. \<lbrakk>{u, v} \<in> set (edges_of_path p); Q2 {u, v}\<rbrakk> \<Longrightarrow> P2 (u, v)\<rbrakk>
   \<Longrightarrow> alt_list P1 P2 (edges_of_vwalk p)"
  by (induction p arbitrary: P1 P2 Q1 Q2 rule: edges_of_path.induct)
     (auto simp: alt_list_empty alt_list_step)

context BFS
begin

subsection \<open>Edges of the copies graph\<close>

lemma copies_dag_cases:
  assumes "(w, w') \<in> copies_dag (Graph.digraph_abs T)"
  obtains u v where "w = Vtx Odd v" "w' = Vtx Even u"
      "(u, v) \<in> Graph.digraph_abs T" "(u, v) \<in> Graph.digraph_abs unmatching"
    | u v where "w = Vtx Even v" "w' = Vtx Odd u"
      "(u, v) \<in> Graph.digraph_abs T" "(u, v) \<in> Graph.digraph_abs matching"
  using assms
  by (auto simp: copies_dag_def)

lemma copies_dag_vtx_dVs:
  "w \<in> dVs (copies_dag (Graph.digraph_abs T)) \<Longrightarrow> vtx w \<in> dVs (Graph.digraph_abs T)"
  by (auto simp: dVs_eq elim!: copies_dag_cases intro: rev_image_eqI)

lemma copies_walk_alt_walk:
  assumes "Vwalk.vwalk_bet (copies_dag (Graph.digraph_abs T)) w q z"
  shows "label z = Even \<longrightarrow>
           alt_walk (label w) (Graph.digraph_abs T) (vtx z) (rev (map vtx q)) (vtx w)"
  using assms
proof(induction rule: induct_vwalk_bet)
  case (path1 v)
  thus ?case
    by (auto dest!: copies_dag_vtx_dVs simp: alt_dist.alt_vwalk_bet_def parity_simps alt_list_empty)
next
  case (path2 v v' vs b)
  show ?case
  proof
    assume "label b = Even"
    hence IH: "alt_walk (label v') (Graph.digraph_abs T) (vtx b) (rev (map vtx (v' # vs))) (vtx v')"
      using path2(3)
      by blast
    from path2(1)
    show "alt_walk (label v) (Graph.digraph_abs T) (vtx b) (rev (map vtx (v # v' # vs))) (vtx v)"
    proof(cases rule: copies_dag_cases)
      case (1 u x)
      hence step: "alt_walk Odd (Graph.digraph_abs T) u [u, x] x"
        by (auto simp: alt_dist.alt_vwalk_bet_def parity_simps unmatched_edge_def
                       alt_list_empty alt_list_step edge_iff_vwalk_bet[symmetric])
      have w1: "alt_walk Even (Graph.digraph_abs T) (vtx b) (rev (map vtx (v' # vs))) (last (rev (map vtx (v' # vs))))"
        using IH 1
        by simp
      have w2: "next_alt_list_parity Even alt_dist.alt_vwalk_bet unmatched_edge matched_edge
                  (other_parity Even) (Graph.digraph_abs T) (last (rev (map vtx (v' # vs))))
                  (last (rev (map vtx (v' # vs))) # [x]) x"
        using step 1
        by (simp add: parity_simps)
      have "alt_walk Odd (Graph.digraph_abs T) (vtx b) (rev (map vtx (v' # vs)) @ [x]) x"
        by (rule alt_vwalk_bet_append_3[where parity = Even, OF w1 w2]) simp
      thus ?thesis
        using 1
        by simp
    next
      case (2 u x)
      hence step: "alt_dist.alt_vwalk_bet matched_edge unmatched_edge Odd (Graph.digraph_abs T) u [u, x] x"
        by (auto simp: alt_dist.alt_vwalk_bet_def parity_simps matched_edge_def
                       alt_list_empty alt_list_step edge_iff_vwalk_bet[symmetric])
      have w1: "alt_walk Odd (Graph.digraph_abs T) (vtx b) (rev (map vtx (v' # vs))) (last (rev (map vtx (v' # vs))))"
        using IH 2
        by simp
      have w2: "next_alt_list_parity Odd alt_dist.alt_vwalk_bet unmatched_edge matched_edge
                  Odd (Graph.digraph_abs T) (last (rev (map vtx (v' # vs))))
                  (last (rev (map vtx (v' # vs))) # [x]) x"
        using step 2
        by (simp add: parity_simps)
      have "alt_walk Even (Graph.digraph_abs T) (vtx b) (rev (map vtx (v' # vs)) @ [x]) x"
        by (rule alt_vwalk_bet_append_2[where parity = Odd, OF w1 w2]) simp
      thus ?thesis
        using 2
        by simp
    qed
  qed
qed

definition "bipartite_matching_input UG M X Y =
  (graph_invar UG \<and> M \<subseteq> UG \<and>
   Graph.digraph_abs matching = {(u, v). {u, v} \<in> M} \<and>
   Graph.digraph_abs unmatching = {(u, v). {u, v} \<in> UG - M} \<and>
   t_set srcs = Vs UG - Vs M \<and> bipartite UG X Y)"

context
  includes Graph.adjmap.automation and Graph.vset.set.automation
       and set_ops.automation2
  assumes BFS_axiom
begin

subsection \<open>Walks of the copies graph under the BFS axiom\<close>

lemma copies_lev_zero:
  assumes "valid_alt_BFS_DAG T dists VisE VisO" "z \<in> dVs (copies_dag (Graph.digraph_abs T))"
          "copies_lev z = 0"
  shows "label z = Even" "vtx z \<in> t_set srcs"
proof-
  note P = valid_alt_BFS_DAG_props[OF \<open>BFS_axiom\<close> assms(1)]
  have "z \<in> Vtx Even ` t_set VisE \<union> Vtx Odd ` t_set VisO"
    using copies_dag_dVs[OF \<open>BFS_axiom\<close> assms(1)] assms(2)
    by blast
  moreover have False if "x \<in> t_set VisO" "copies_lev (Vtx Odd x) = 0" for x
    using P(4)[OF that(1)] that(2) altd_G_parity[OF \<open>BFS_axiom\<close>]
    by (cases "altd_G Odd x") (fastforce simp: copies_lev_def parity_simps)+
  moreover have "x \<in> t_set srcs" if "x \<in> t_set VisE" "copies_lev (Vtx Even x) = 0" for x
  proof-
    have "x \<in> dVs G"
    proof(rule ccontr)
      assume "x \<notin> dVs G"
      hence "altd_G Even x = \<infinity>"
        by (simp add: alt_distance_set_def alt_dist.alt_dist_set_inf)
      thus False
        using P(5)[OF that(1)]
        by simp
    qed
    moreover have "altd_G Even x = 0"
      using P(5)[OF that(1)] that(2)
      by (cases "altd_G Even x") (auto simp: copies_lev_def zero_enat_def)
    ultimately show ?thesis
      by (auto simp: alt_distance_set_def)
  qed
  ultimately show "label z = Even" "vtx z \<in> t_set srcs"
    using assms(3)
    by auto
qed

lemma copies_walk_from_odd:
  assumes "valid_alt_BFS_DAG T dists VisE VisO"
          "Vwalk.vwalk_bet (copies_dag (Graph.digraph_abs T)) (Vtx Odd t) q z" "copies_lev z = 0"
  shows "vtx z \<in> t_set srcs"
        "alt_walk Odd G (vtx z) (rev (map vtx q)) t"
        "enat (length q - 1) = altd_G Odd t"
proof-
  note P = valid_alt_BFS_DAG_props[OF \<open>BFS_axiom\<close> assms(1)]
  have "z \<in> dVs (copies_dag (Graph.digraph_abs T))"
    using assms(2)
    by (auto intro: vwalk_bet_in_dVs simp: Vwalk.vwalk_bet_def)
  note lz = copies_lev_zero[OF assms(1) this assms(3)]
  hence aw: "alt_walk Odd (Graph.digraph_abs T) (vtx z) (rev (map vtx q)) t"
    using copies_walk_alt_walk[OF assms(2)]
    by simp
  show "vtx z \<in> t_set srcs"
    by (rule lz(2))
  show "alt_walk Odd G (vtx z) (rev (map vtx q)) t"
    by (rule alt_dist.alt_vwalk_bet_subset[OF aw P(1)])
  show "enat (length q - 1) = altd_G Odd t"
    using P(12)[OF lz(2) aw]
    by simp
qed

lemma VisO_copies_dVs:
  assumes "valid_alt_BFS_DAG T dists VisE VisO" "t \<in> t_set VisO"
  shows "Vtx Odd t \<in> dVs (copies_dag (Graph.digraph_abs T))"
proof-
  note P = valid_alt_BFS_DAG_props[OF \<open>BFS_axiom\<close> assms(1)]
  have ne: "alt_distance_set (Graph.digraph_abs T) Odd t \<noteq> \<infinity>"
    using P(4,10)[OF assms(2)]
    by simp
  obtain s p where "s \<in> t_set srcs" and w: "alt_walk Odd (Graph.digraph_abs T) s p t"
    using altd_set_witness[OF \<open>BFS_axiom\<close> ne]
    by blast
  hence len: "1 < length p"
    by (cases p) (auto simp: alt_dist.alt_vwalk_bet_def parity_simps)
  obtain y where "(y, t) \<in> Graph.digraph_abs T" "unmatched_edge (y, t)"
    by (rule alt_walk_snocE[OF \<open>BFS_axiom\<close> w len]) simp
  thus ?thesis
    by (auto simp: copies_dag_def unmatched_edge_def)
qed

subsection \<open>The bipartite matching instance\<close>

context
  fixes UG M :: "'ver set set" and X Y :: "'ver set"
  assumes bipartite_matching_input: "bipartite_matching_input UG M X Y"
begin

lemma bipartite_matching_input_props[simp]:
  "graph_invar UG" "M \<subseteq> UG"
  "Graph.digraph_abs matching = {(u, v). {u, v} \<in> M}"
  "Graph.digraph_abs unmatching = {(u, v). {u, v} \<in> UG - M}"
  "t_set srcs = Vs UG - Vs M" "bipartite UG X Y"
  using bipartite_matching_input
  by (auto simp: bipartite_matching_input_def)

lemma G_eq_undirected_edges: "G = {(u, v). {u, v} \<in> UG}"
  using bipartite_matching_input_props(2)
  by (auto simp: G_def subset_iff)

lemma dVs_G_subset_Vs: "dVs G \<subseteq> Vs UG"
  by (force simp: G_eq_undirected_edges dVs_eq intro: edges_are_Vs edges_are_Vs_2)

lemma vwalk_G_iff_path: "Vwalk.vwalk G p \<longleftrightarrow> path UG p"
proof
  show "Vwalk.vwalk G p \<Longrightarrow> path UG p"
    by (induction rule: Vwalk.vwalk.induct)
       (auto simp: G_eq_undirected_edges dest: subsetD[OF dVs_G_subset_Vs[unfolded G_eq_undirected_edges]])
  show "path UG p \<Longrightarrow> Vwalk.vwalk G p"
  proof(induction rule: path.induct)
    case (path1 v)
    then obtain e where e: "e \<in> UG" "v \<in> e"
      by (auto simp: vs_member)
    then obtain a b where "e = {a, b}"
      using bipartite_matching_input_props(1)
      by (auto simp: dblton_graph_def)
    thus ?case
      using e
      by (auto simp: G_eq_undirected_edges insert_commute)
  qed (auto simp: G_eq_undirected_edges)
qed

lemma alt_walk_alt_path:
  "alt_walk parity G u p v \<Longrightarrow> alt_path M p"
  by (auto intro!: alt_list_edges_of_vwalk_path
             simp: alt_dist.alt_vwalk_bet_def unmatched_edge_def matched_edge_def)

lemma alt_path_imp_alt_list:
  "\<lbrakk>path UG p; alt_path M p\<rbrakk> \<Longrightarrow> alt_list unmatched_edge matched_edge (edges_of_vwalk p)"
  by (auto intro!: alt_list_edges_of_path_vwalk dest: path_edges_subset
             simp: unmatched_edge_def matched_edge_def)

lemma augmenting_path_alt_walk:
  assumes "graph_augmenting_path UG M p"
  shows "hd p \<in> t_set srcs" "last p \<in> t_set srcs" "alt_walk Odd G (hd p) p (last p)"
proof-
  have "path UG p" "matching_augmenting_path M p"
    using assms
    by simp_all
  moreover hence "p \<noteq> []"
    by (auto simp: matching_augmenting_path_def)
  ultimately show "hd p \<in> t_set srcs" "last p \<in> t_set srcs"
    by (auto simp: matching_augmenting_path_def intro: mem_path_Vs)
  show "alt_walk Odd G (hd p) p (last p)"
    unfolding alt_dist.alt_vwalk_bet_def
    using \<open>path UG p\<close> \<open>matching_augmenting_path M p\<close> \<open>p \<noteq> []\<close> aug_paths_are_even
    by (auto simp: Vwalk.vwalk_bet_def parity_simps vwalk_G_iff_path matching_augmenting_path_def
            intro: alt_path_imp_alt_list)
qed

lemma copies_walk_label_side:
  assumes "Vwalk.vwalk_bet (copies_dag (Graph.digraph_abs T)) w q z" "Graph.digraph_abs T \<subseteq> G"
          "bipartite UG Xs Ys"
  shows "(label w = Odd \<longleftrightarrow> vtx w \<in> Xs) \<longrightarrow> (\<forall>w' \<in> set q. label w' = Odd \<longleftrightarrow> vtx w' \<in> Xs)"
  using assms(1)
proof(induction rule: induct_vwalk_bet)
  case (path2 v v' vs b)
  have step: "label v' = Odd \<longleftrightarrow> vtx v' \<in> Xs" if "label v = Odd \<longleftrightarrow> vtx v \<in> Xs"
    using path2(1)
  proof(cases rule: copies_dag_cases)
    case (1 u x)
    thus ?thesis
      using that assms(2,3)
      by (auto simp: G_eq_undirected_edges dest!: bipartite_edgeD(3))
  next
    case (2 u x)
    thus ?thesis
      using that assms(2,3) bipartite_vs_subset[OF assms(3)]
      by (fastforce simp: G_eq_undirected_edges dest: bipartite_edgeD(4) edges_are_Vs_2)
  qed
  show ?case
  proof
    assume hv: "label v = Odd \<longleftrightarrow> vtx v \<in> Xs"
    hence "label v' = Odd \<longleftrightarrow> vtx v' \<in> Xs"
      by (rule step)
    hence "\<forall>w' \<in> set (v' # vs). label w' = Odd \<longleftrightarrow> vtx w' \<in> Xs"
      by (rule mp[OF path2(3)])
    thus "\<forall>w' \<in> set (v # v' # vs). label w' = Odd \<longleftrightarrow> vtx w' \<in> Xs"
      using hv
      by simp
  qed
qed simp

lemma copies_walk_distinct_vtx:
  assumes "valid_alt_BFS_DAG T dists VisE VisO"
          "Vwalk.vwalk_bet (copies_dag (Graph.digraph_abs T)) w q z"
  shows "distinct (map vtx q)"
proof-
  note P = valid_alt_BFS_DAG_props[OF \<open>BFS_axiom\<close> assms(1)]
  have "distinct q"
    by (rule conjunct1[OF vwalk_bet_level_distinct[OF assms(2) copies_lev_decrease[OF \<open>BFS_axiom\<close> assms(1)]]])
  moreover have "vtx w \<in> Vs UG"
  proof-
    have "w \<in> dVs (copies_dag (Graph.digraph_abs T))"
      using vwalk_bet_in_dVs[OF assms(2)] hd_of_vwalk_bet''[OF assms(2)]
      by blast
    hence "vtx w \<in> dVs (Graph.digraph_abs T)"
      by (rule copies_dag_vtx_dVs)
    thus ?thesis
      using dVs_subset[OF P(1)] dVs_G_subset_Vs
      by blast
  qed
  text \<open>Choose the side of the bipartition that contains the odd copies of the walk.\<close>
  then obtain Z Z' where "bipartite UG Z Z'" "label w = Odd \<longleftrightarrow> vtx w \<in> Z"
  proof(cases "label w = Odd \<longleftrightarrow> vtx w \<in> X")
    case True
    thus thesis
      by (rule that[OF bipartite_matching_input_props(6)])
  next
    case False
    hence "label w = Odd \<longleftrightarrow> vtx w \<in> Y"
      using \<open>vtx w \<in> Vs UG\<close> bipartite_vs_subset[OF bipartite_matching_input_props(6)]
            bipartite_matching_input_props(6)
      by (auto simp: bipartite_def)
    thus thesis
      by (rule that[OF bipartite_commute[OF bipartite_matching_input_props(6)]])
  qed
  hence side: "\<forall>w' \<in> set q. label w' = Odd \<longleftrightarrow> vtx w' \<in> Z"
    using copies_walk_label_side[OF assms(2) P(1)]
    by blast
  moreover have "inj_on vtx (set q)"
  proof(rule inj_onI)
    fix a b
    assume ab: "a \<in> set q" "b \<in> set q" "vtx a = vtx b"
    hence "label a = Odd \<longleftrightarrow> label b = Odd"
      using side
      by auto
    hence "label a = label b"
      by (cases "label a"; cases "label b") simp_all
    thus "a = b"
      using ab(3)
      by (cases a; cases b) simp_all
  qed
  ultimately show ?thesis
    by (simp add: distinct_map)
qed

theorem copies_walk_augmenting:
  assumes "valid_alt_BFS_DAG T dists VisE VisO" "t \<in> t_set srcs"
          "Vwalk.vwalk_bet (copies_dag (Graph.digraph_abs T)) (Vtx Odd t) q z" "copies_lev z = 0"
  shows "graph_augmenting_path UG M (rev (map vtx q))"
        "enat (length q - 1) = altd_G Odd t"
proof-
  note W = copies_walk_from_odd[OF assms(1,3,4)]
  hence vb: "Vwalk.vwalk_bet G (vtx z) (rev (map vtx q)) t" and "even (length q)"
    by (auto simp: alt_dist.alt_vwalk_bet_def parity_simps)
  hence "2 \<le> length (rev (map vtx q))"
    by (cases q) (auto simp: Vwalk.vwalk_bet_def, presburger)
  moreover have "path UG (rev (map vtx q))"
    using vb
    by (auto simp: Vwalk.vwalk_bet_def vwalk_G_iff_path)
  moreover have "distinct (rev (map vtx q))"
    using copies_walk_distinct_vtx[OF assms(1,3)]
    by simp
  moreover have "alt_path M (rev (map vtx q))"
    by (rule alt_walk_alt_path[OF W(2)])
  moreover have "hd (rev (map vtx q)) \<notin> Vs M" "last (rev (map vtx q)) \<notin> Vs M"
    using W(1) assms(2) hd_of_vwalk_bet'[OF vb] last_of_vwalk_bet[OF vb]
    by simp_all
  ultimately show "graph_augmenting_path UG M (rev (map vtx q))"
    by (simp add: matching_augmenting_path_def)
  show "enat (length q - 1) = altd_G Odd t"
    by (rule W(3))
qed

theorem augmenting_path_copies_start:
  assumes "valid_alt_BFS_DAG T dists VisE VisO" "graph_augmenting_path UG M p"
  obtains t q z where "t \<in> t_set srcs"
      "Vwalk.vwalk_bet (copies_dag (Graph.digraph_abs T)) (Vtx Odd t) q z" "copies_lev z = 0"
proof-
  note P = valid_alt_BFS_DAG_props[OF \<open>BFS_axiom\<close> assms(1)]
  note W = augmenting_path_alt_walk[OF assms(2)]
  hence "Vtx Odd (last p) \<in> dVs (copies_dag (Graph.digraph_abs T))"
    using P(6)
    by (blast intro: VisO_copies_dVs[OF assms(1)])
  thus thesis
    using W(2)
    by (blast intro: that elim: copies_reach_zero[OF \<open>BFS_axiom\<close> assms(1)])
qed

theorem augmenting_path_iff_free_odd_copy:
  assumes "valid_alt_BFS_DAG T dists VisE VisO"
  shows "(\<exists>p. graph_augmenting_path UG M p) \<longleftrightarrow>
         (\<exists>t \<in> t_set srcs. Vtx Odd t \<in> dVs (copies_dag (Graph.digraph_abs T)))"
proof
  assume "\<exists>p. graph_augmenting_path UG M p"
  then obtain p where "graph_augmenting_path UG M p"
    by blast
  then obtain t q z where tqz: "t \<in> t_set srcs"
      "Vwalk.vwalk_bet (copies_dag (Graph.digraph_abs T)) (Vtx Odd t) q z" "copies_lev z = 0"
    by (rule augmenting_path_copies_start[OF assms])
  hence "Vtx Odd t \<in> dVs (copies_dag (Graph.digraph_abs T))"
    by (blast intro: vwalk_bet_in_vertices[OF tqz(2) hd_of_vwalk_bet''[OF tqz(2)]])
  thus "\<exists>t \<in> t_set srcs. Vtx Odd t \<in> dVs (copies_dag (Graph.digraph_abs T))"
    using tqz(1)
    by blast
next
  assume "\<exists>t \<in> t_set srcs. Vtx Odd t \<in> dVs (copies_dag (Graph.digraph_abs T))"
  then obtain t where t: "t \<in> t_set srcs" "Vtx Odd t \<in> dVs (copies_dag (Graph.digraph_abs T))"
    by blast
  obtain q z where "Vwalk.vwalk_bet (copies_dag (Graph.digraph_abs T)) (Vtx Odd t) q z"
      "copies_lev z = 0"
    by (rule copies_reach_zero[OF \<open>BFS_axiom\<close> assms t(2)])
  thus "\<exists>p. graph_augmenting_path UG M p"
    using copies_walk_augmenting(1)[OF assms t(1)]
    by blast
qed

corollary BFS_augmenting_path_iff:
  "(\<exists>p. graph_augmenting_path UG M p) \<longleftrightarrow>
   (\<exists>t \<in> t_set srcs.
      Vtx Odd t \<in> dVs (copies_dag (Graph.digraph_abs (parents (BFS initial_state)))))"
  by (rule augmenting_path_iff_free_odd_copy[OF BFS_valid_DAG[OF \<open>BFS_axiom\<close>]])

corollary BFS_copies_walk_augmenting:
  "\<lbrakk>t \<in> t_set srcs;
    Vwalk.vwalk_bet (copies_dag (Graph.digraph_abs (parents (BFS initial_state)))) (Vtx Odd t) q z;
    copies_lev z = 0\<rbrakk>
   \<Longrightarrow> graph_augmenting_path UG M (rev (map vtx q))"
  by (rule copies_walk_augmenting(1)[OF BFS_valid_DAG[OF \<open>BFS_axiom\<close>]])

end

end

end

end


