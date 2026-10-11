theory Unit_Flows
  imports
    Directed_Set_Graphs.Vwalk
    Flow_Theory.STFlow
begin

section \<open>Unit Flows\<close>

text \<open>A unit network is a flow network, i.e. a multigraph, in which all edges have capacity one.
A unit flow is an integral flow in such a network, so it takes the values \<open>0\<close> and \<open>1\<close> only.
For a unit flow, exactly one of the two residual edges of an original edge has positive residual
capacity, and that capacity is one. Augmenting by one along a path of residual edges replaces the
residual edges on the path by their reverses. Residual reachability is reachability in the
projection of the residual edges to pairs of vertices, so unit flows can be maximised by a plain
graph search on the projection.\<close>

subsection \<open>Walks\<close>

lemma cas_hd_last:
  "\<lbrakk>cas u es v; es \<noteq> []\<rbrakk> \<Longrightarrow> fst (hd es) = u"
  "\<lbrakk>cas u es v; es \<noteq> []\<rbrakk> \<Longrightarrow> snd (last es) = v"
  by (induction u es v rule: cas.induct) (auto elim: cas.elims)

lemma edges_of_vwalk_distinct_swap:
  "\<lbrakk>distinct p; (u, v) \<in> set (edges_of_vwalk p)\<rbrakk> \<Longrightarrow> (v, u) \<notin> set (edges_of_vwalk p)"
  by (induction p rule: edges_of_vwalk.induct) (auto dest: v_in_edge_in_vwalk)

subsection \<open>Residual Edges\<close>

context flow_network_spec
begin

lemma oedge_eq_cases: "oedge x = oedge y \<Longrightarrow> x = y \<or> x = erev y"
  by (cases x; cases y) auto

lemma augment_edges_distinct:
  "distinct (map oedge es) \<Longrightarrow>
    augment_edges f \<gamma> es d =
      (if F d \<in> set es then f d + \<gamma> else if B d \<in> set es then f d - \<gamma> else f d)"
proof (induction es)
  case (Cons e es)
  have "oedge e \<notin> oedge ` set es"
    using Cons.prems by simp
  then have "F (oedge e) \<notin> set es" "B (oedge e) \<notin> set es"
    using imageI[of "F (oedge e)" "set es" oedge] imageI[of "B (oedge e)" "set es" oedge]
    by auto
  then show ?case
    using Cons by (cases e) auto
qed simp

end

subsection \<open>Residual Reachability as Reachability in the Projection\<close>

context flow_network
begin

text \<open>Residual reachability between distinct vertices is the existence of a walk in the
projection of the residual edges of positive capacity.\<close>

lemma resreach_iff_vwalk:
  assumes "u \<noteq> v"
  shows "resreach f u v \<longleftrightarrow>
    (\<exists>p. vwalk_bet (to_vertex_pair ` {e | e. e \<in> \<EE> \<and> rcap f e > 0}) u p v)"
proof
  assume "resreach f u v"
  then obtain p where p: "awalk (to_vertex_pair ` \<EE>) u (map to_vertex_pair p) v"
    "Rcap f (set p) > 0" "p \<noteq> []" "set p \<subseteq> \<EE>"
    by (rule resreachE)
  have "set (map to_vertex_pair p) \<subseteq> to_vertex_pair ` {e | e. e \<in> \<EE> \<and> rcap f e > 0}"
    using p(2,4) rcap_extr_strict[of _ p 0 f] by auto
  then have "awalk (to_vertex_pair ` {e | e. e \<in> \<EE> \<and> rcap f e > 0}) u (map to_vertex_pair p) v"
    using subset_mono_awalk'[OF p(1)] p(3) by simp
  then have "vwalk_bet (to_vertex_pair ` {e | e. e \<in> \<EE> \<and> rcap f e > 0}) u
      (awalk_verts u (map to_vertex_pair p)) v"
    by (rule awalk_imp_vwalk)
  then show "\<exists>p. vwalk_bet (to_vertex_pair ` {e | e. e \<in> \<EE> \<and> rcap f e > 0}) u p v"
    by (rule exI)
next
  assume "\<exists>p. vwalk_bet (to_vertex_pair ` {e | e. e \<in> \<EE> \<and> rcap f e > 0}) u p v"
  then obtain p where p: "vwalk_bet (to_vertex_pair ` {e | e. e \<in> \<EE> \<and> rcap f e > 0}) u p v"
    by blast
  have aw: "awalk (to_vertex_pair ` {e | e. e \<in> \<EE> \<and> rcap f e > 0}) u (edges_of_vwalk p) v"
    using p by (rule vwalk_imp_awalk)
  then have "set (edges_of_vwalk p) \<subseteq> to_vertex_pair ` {e | e. e \<in> \<EE> \<and> rcap f e > 0}"
    by (simp add: awalk_def)
  then obtain pp where pp: "map to_vertex_pair pp = edges_of_vwalk p"
    "set pp \<subseteq> {e | e. e \<in> \<EE> \<and> rcap f e > 0}"
    using list_in_image_map by blast
  have "edges_of_vwalk p \<noteq> []"
    using aw assms by (auto simp: awalk_Nil_iff)
  then have pp_ne: "pp \<noteq> []"
    using pp(1) by auto
  have aw': "awalk (to_vertex_pair ` \<EE>) u (map to_vertex_pair pp) v"
    using subset_mono_awalk[OF aw] pp by auto
  have Rc: "Rcap f (set pp) > 0"
    by (rule Rcap_strictI') (use pp(2) in auto)
  have sub: "set pp \<subseteq> \<EE>"
    using pp(2) by auto
  show "resreach f u v"
    by (rule resreachI[OF aw' Rc pp_ne sub])
qed

text \<open>Hence an \<open>s\<close>-\<open>t\<close> flow is maximum iff there is no walk from \<open>s\<close> to \<open>t\<close> in the projection.\<close>

lemma max_flow_iff_no_vwalk:
  assumes "f is s -- t flow"
  shows "is_max_flow s t f \<longleftrightarrow>
    \<not> (\<exists>p. vwalk_bet (to_vertex_pair ` {e | e. e \<in> \<EE> \<and> rcap f e > 0}) s p t)"
proof -
  have "s \<in> \<V>" "t \<in> \<V>" "s \<noteq> t"
    using assms by (auto elim: is_s_t_flowE)
  then show ?thesis
    using max_flow_iff_not_resreach[of s t f] assms resreach_iff_vwalk[of s t f] by simp
qed

text \<open>A vertex \<open>w\<close> with more inflow than outflow reaches \<open>s\<close> in the residual graph, if \<open>s\<close> is the
only other vertex that may have more outflow than inflow: otherwise the vertices reachable from
\<open>w\<close> would form a set into which no flow enters, but whose balances sum up to a negative value.\<close>

lemma neg_balance_resreach:
  assumes f: "f is b flow" and w: "w \<in> \<V>" "b w < 0" and sw: "s \<noteq> w"
    and others: "\<And>v. \<lbrakk>v \<in> \<V>; v \<noteq> s; v \<noteq> w\<rbrakk> \<Longrightarrow> b v \<le> 0"
  shows "resreach f w s"
proof (rule ccontr)
  assume nr: "\<not> resreach f w s"
  let ?R = "Rescut f w"
  have R: "?R \<subseteq> \<V>"
    by (rule Rescut_around_in_V[OF w(1)])
  have wR: "w \<in> ?R" and sR: "s \<notin> ?R"
    using nr sw by (auto simp: Rescut_def)
  have "sum b (?R - {w}) \<le> 0"
    using R sR by (intro sum_nonpos) (auto intro: others)
  then have "sum b ?R < 0"
    using sum.remove[OF finite_Rescut[OF w(1)] wR, of b] w(2) by simp
  moreover have "0 \<le> sum f (\<Delta>\<^sup>+ ?R)"
    using f by (intro sum_nonneg) (auto simp: Delta_plus_def isbflow_def isuflow_def)
  ultimately show False
    using rescut_all_edges_sat[OF f R] by simp
qed

end

subsection \<open>Unit Networks and Unit Flows\<close>

locale unit_network = flow_network +
  assumes unit_caps: "\<And>e. e \<in> \<E> \<Longrightarrow> \<u> e = 1"
begin

abbreviation unit_flow where
  "unit_flow f \<equiv> isuflow f \<and> is_integral_flow f"

lemma unit_flow_values:
  assumes "unit_flow f" "e \<in> \<E>"
  shows "f e = 0 \<or> f e = 1"
proof -
  obtain n :: int where n: "f e = real_of_int n"
    using assms by (auto simp: is_integral_flow_def)
  have "0 \<le> f e" "ereal (f e) \<le> 1"
    using assms unit_caps[of e] by (auto elim!: isuflowE)
  then have "0 \<le> n" "n \<le> 1"
    unfolding n by (simp_all add: one_ereal_def)
  then have "n = 0 \<or> n = 1"
    by auto
  then show ?thesis
    using n by auto
qed

text \<open>The residual edges of positive capacity of a unit flow.\<close>

lemma unit_residual:
  assumes "unit_flow f"
  shows "F d \<in> \<EE> \<and> rcap f (F d) > 0 \<longleftrightarrow> d \<in> \<E> \<and> f d = 0"
    and "B d \<in> \<EE> \<and> rcap f (B d) > 0 \<longleftrightarrow> d \<in> \<E> \<and> f d = 1"
proof -
  have F: "F d \<in> \<EE> \<longleftrightarrow> d \<in> \<E>" and B: "B d \<in> \<EE> \<longleftrightarrow> d \<in> \<E>"
    using o_edge_res[of "F d"] o_edge_res[of "B d"] by simp_all
  have "rcap f (F d) > 0 \<longleftrightarrow> f d = 0" "rcap f (B d) > 0 \<longleftrightarrow> f d = 1" if d: "d \<in> \<E>"
    using unit_flow_values[OF assms d] unit_caps[OF d] by (auto simp: one_ereal_def)
  then show "F d \<in> \<EE> \<and> rcap f (F d) > 0 \<longleftrightarrow> d \<in> \<E> \<and> f d = 0"
    and "B d \<in> \<EE> \<and> rcap f (B d) > 0 \<longleftrightarrow> d \<in> \<E> \<and> f d = 1"
    using F B by blast+
qed

lemma unit_residual_rcap:
  assumes "unit_flow f" "r \<in> \<EE>" "rcap f r > 0"
  shows "rcap f r = 1" and "\<not> rcap f (erev r) > 0"
proof -
  have "rcap f r = 1 \<and> \<not> rcap f (erev r) > 0"
  proof (cases r)
    case (F d)
    then have "d \<in> \<E>" "f d = 0"
      using assms unit_residual(1)[OF assms(1), of d] by simp_all
    then show ?thesis
      using F unit_caps[of d] by (simp add: one_ereal_def)
  next
    case (B d)
    then have "d \<in> \<E>" "f d = 1"
      using assms unit_residual(2)[OF assms(1), of d] by simp_all
    then show ?thesis
      using B unit_caps[of d] by (simp add: one_ereal_def)
  qed
  then show "rcap f r = 1" and "\<not> rcap f (erev r) > 0"
    by simp_all
qed

lemma zero_unit_flow:
  shows "unit_flow (\<lambda>_. 0)"
    and "{e | e. e \<in> \<EE> \<and> rcap (\<lambda>_. 0) e > 0} = F ` \<E>"
proof -
  have "isuflow (\<lambda>_. 0)"
    using u_non_neg by (auto intro!: isuflowI simp: zero_ereal_def)
  moreover have "is_integral_flow (\<lambda>_. 0)"
    unfolding is_integral_flow_def by (auto intro!: exI[of _ "0::int"])
  ultimately show zero: "unit_flow (\<lambda>_. 0)"
    by simp
  show "{e | e. e \<in> \<EE> \<and> rcap (\<lambda>_. 0) e > 0} = F ` \<E>"
  proof (rule set_eqI)
    fix r
    show "r \<in> {e | e. e \<in> \<EE> \<and> rcap (\<lambda>_. 0) e > 0} \<longleftrightarrow> r \<in> F ` \<E>"
      using unit_residual[OF zero] by (cases r) auto
  qed
qed

subsection \<open>Augmenting a Unit Flow by One\<close>

text \<open>Every walk in the projection lifts to a list of residual edges.\<close>

lemma lift_vwalk:
  assumes "vwalk_bet (to_vertex_pair ` {e | e. e \<in> \<EE> \<and> rcap f e > 0}) u p v"
  obtains rs where "map to_vertex_pair rs = edges_of_vwalk p"
    "set rs \<subseteq> {e | e. e \<in> \<EE> \<and> rcap f e > 0}"
  using list_in_image_map[OF vwalk_bet_edges_in_edges[OF assms]] by blast

text \<open>Augmenting along the lift of a distinct walk from \<open>s\<close> to \<open>t\<close> moves one unit of balance from
\<open>t\<close> to \<open>s\<close>, and swaps the residual edges on the walk for their reverses.\<close>

theorem augment_unit_walk:
  assumes f: "f is b flow" "unit_flow f"
    and p: "distinct p" "vwalk_bet (to_vertex_pair ` {e | e. e \<in> \<EE> \<and> rcap f e > 0}) s p t"
      "s \<noteq> t"
    and rs: "map to_vertex_pair rs = edges_of_vwalk p"
      "set rs \<subseteq> {e | e. e \<in> \<EE> \<and> rcap f e > 0}"
  defines "g \<equiv> augment_edges f 1 rs"
  shows "g is (\<lambda>v. if v = s then b v + 1 else if v = t then b v - 1 else b v) flow"
    "unit_flow g"
    "{e | e. e \<in> \<EE> \<and> rcap g e > 0} =
       {e | e. e \<in> \<EE> \<and> rcap f e > 0} - set rs \<union> erev ` set rs"
    "d \<notin> \<E> \<Longrightarrow> g d = f d"
proof -
  have st: "s \<noteq> t"
    by (rule p(3))
  have P_ne: "edges_of_vwalk p \<noteq> []"
    using p(2) st by (cases p rule: edges_of_vwalk.cases) (auto simp: vwalk_bet_def)
  then have rs_ne: "rs \<noteq> []"
    using rs(1) by auto
  have aw: "awalk (to_vertex_pair ` {e | e. e \<in> \<EE> \<and> rcap f e > 0}) s (edges_of_vwalk p) t"
    using p(2) by (rule vwalk_imp_awalk)
  have hd_P: "prod.fst (hd (edges_of_vwalk p)) = s"
    and last_P: "prod.snd (last (edges_of_vwalk p)) = t"
    using aw P_ne by (auto simp: awalk_def intro: cas_hd_last)
  have fst_hd: "fstv (hd rs) = s"
    using hd_P hd_map[OF rs_ne, of to_vertex_pair] by (simp add: rs(1)[symmetric] to_vertex_pair_fst_snd)
  have snd_last: "sndv (last rs) = t"
    using last_P last_map[OF rs_ne, of to_vertex_pair]
    by (simp add: rs(1)[symmetric] to_vertex_pair_fst_snd)
  have rs_EE: "set rs \<subseteq> \<EE>"
    using rs(2) by auto
  have rcap_rs: "rcap f r = 1" "\<not> rcap f (erev r) > 0" if "r \<in> set rs" for r
    using unit_residual_rcap[OF f(2)] that rs(2) by auto
  have Rcap: "ereal 1 \<le> Rcap f (set rs)"
    by (rule RcapI) (use rcap_rs rs_ne in auto)
  have dist: "distinct rs"
    using distinct_edges_of_vwalk[OF p(1)] distinct_map[of to_vertex_pair rs] rs(1) by simp
  have "inj_on oedge (set rs)"
  proof (rule inj_onI)
    fix x y
    assume xy: "x \<in> set rs" "y \<in> set rs" "oedge x = oedge y"
    show "x = y"
      using oedge_eq_cases[OF xy(3)] rcap_rs(1)[OF xy(1)] rcap_rs(2)[OF xy(2)] by auto
  qed
  then have dist_oedge: "distinct (map oedge rs)"
    using dist by (simp add: distinct_map)
  have "prepath rs"
  proof (rule prepathI)
    show "awalk UNIV (fstv (hd rs)) (map to_vertex_pair rs) (sndv (last rs))"
      unfolding fst_hd snd_last rs(1) using subset_mono_awalk[OF aw] by simp
  qed (rule rs_ne)
  moreover have "0 < Rcap f (set rs)"
    using Rcap by (rule order.strict_trans2[rotated]) simp
  ultimately have augpath: "augpath f rs"
    by (rule augpathI)
  show g_flow: "g is (\<lambda>v. if v = s then b v + 1 else if v = t then b v - 1 else b v) flow"
    using augment_path_validness_b_pres_source_target_distinct[OF f(1) _ augpath Rcap rs_EE dist]
      st unfolding fst_hd snd_last g_def by simp
  show g_unit: "unit_flow g"
    using g_flow augment_edges_integral[OF _ _ rs_EE, of f 1] f(2)
    by (auto simp: g_def elim: isbflowE)
  have g_val: "g d = (if F d \<in> set rs then f d + 1 else if B d \<in> set rs then f d - 1 else f d)" for d
    unfolding g_def by (rule augment_edges_distinct[OF dist_oedge])
  show "g d = f d" if d: "d \<notin> \<E>"
  proof -
    have "F d \<notin> \<EE>" "B d \<notin> \<EE>"
      using d o_edge_res[of "F d"] o_edge_res[of "B d"] by simp_all
    then have "F d \<notin> set rs" "B d \<notin> set rs"
      using rs_EE by blast+
    then show ?thesis
      using g_val[of d] by simp
  qed  have res_g: "r \<in> \<EE> \<and> rcap g r > 0 \<longleftrightarrow>
      (r \<in> \<EE> \<and> rcap f r > 0 \<and> r \<notin> set rs) \<or> erev r \<in> set rs" for r
  proof (cases "oedge r \<in> \<E>")
    case False
    have "erev r \<notin> \<EE>"
      using False o_edge_res[of "erev r"] oedge_and_reversed[of r] by simp
    then have "r \<notin> \<EE>" "erev r \<notin> set rs"
      using False o_edge_res[of r] rs_EE by auto
    then show ?thesis
      by blast
  next
    case True
    define d where "d = oedge r"
    have d: "d \<in> \<E>"
      using True by (simp add: d_def)
    have FE: "F d \<in> \<EE>" and BE: "B d \<in> \<EE>"
      using d o_edge_res[of "F d"] o_edge_res[of "B d"] by simp_all
    have fF: "rcap f (F d) > 0 \<longleftrightarrow> f d = 0" and fB: "rcap f (B d) > 0 \<longleftrightarrow> f d = 1"
      using unit_residual[OF f(2), of d] FE BE d by simp_all
    have gF: "rcap g (F d) > 0 \<longleftrightarrow> g d = 0" and gB: "rcap g (B d) > 0 \<longleftrightarrow> g d = 1"
      using unit_residual[OF g_unit, of d] FE BE d by simp_all
    have memF: "F d \<in> set rs \<Longrightarrow> f d = 0" and memB: "B d \<in> set rs \<Longrightarrow> f d = 1"
      using rs(2) fF fB by auto
    have "r = F d \<or> r = B d"
      by (cases r) (simp_all add: d_def)
    then show ?thesis
    proof
      assume r: "r = F d"
      consider (c1) "F d \<in> set rs" | (c2) "F d \<notin> set rs" "B d \<in> set rs"
        | (c3) "F d \<notin> set rs" "B d \<notin> set rs"
        by blast
      then show ?thesis
      proof cases
        case c1
        then have nB: "B d \<notin> set rs"
          using memF memB by force
        then have "g d = 1"
          using c1 memF g_val[of d] by simp
        then have "\<not> rcap g (F d) > 0"
          using gF by simp
        then show ?thesis
          using r c1 nB by simp
      next
        case c2
        then have "g d = 0"
          using memB g_val[of d] by simp
        then show ?thesis
          using r c2(2) FE gF by simp
      next
        case c3
        then have "g d = f d"
          using g_val[of d] by simp
        then have "rcap g (F d) > 0 \<longleftrightarrow> rcap f (F d) > 0"
          using gF fF by simp
        then show ?thesis
          using r c3 by simp
      qed
    next
      assume r: "r = B d"
      consider (c1) "B d \<in> set rs" | (c2) "B d \<notin> set rs" "F d \<in> set rs"
        | (c3) "F d \<notin> set rs" "B d \<notin> set rs"
        by blast
      then show ?thesis
      proof cases
        case c1
        then have nF: "F d \<notin> set rs"
          using memF memB by force
        then have "g d = 0"
          using c1 memB g_val[of d] by simp
        then have "\<not> rcap g (B d) > 0"
          using gB by simp
        then show ?thesis
          using r c1 nF by simp
      next
        case c2
        then have "g d = 1"
          using memF g_val[of d] by simp
        then show ?thesis
          using r c2(2) BE gB by simp
      next
        case c3
        then have "g d = f d"
          using g_val[of d] by simp
        then have "rcap g (B d) > 0 \<longleftrightarrow> rcap f (B d) > 0"
          using gB fB by simp
        then show ?thesis
          using r c3 by simp
      qed
    qed
  qed
  have erev_img: "r \<in> erev ` set rs \<longleftrightarrow> erev r \<in> set rs" for r  proof
    assume "r \<in> erev ` set rs"
    then obtain x where "x \<in> set rs" "r = erev x"
      by blast
    then show "erev r \<in> set rs"
      by (simp add: erve_erve_id)
  next
    assume "erev r \<in> set rs"
    then show "r \<in> erev ` set rs"
      using image_eqI[of r erev "erev r"] erve_erve_id[of r] by simp
  qed
  show "{e | e. e \<in> \<EE> \<and> rcap g e > 0} =
      {e | e. e \<in> \<EE> \<and> rcap f e > 0} - set rs \<union> erev ` set rs"
  proof (rule set_eqI)
    fix r
    have "r \<in> {e | e. e \<in> \<EE> \<and> rcap g e > 0} \<longleftrightarrow> r \<in> \<EE> \<and> rcap g r > 0"
      by blast
    moreover have "r \<in> {e | e. e \<in> \<EE> \<and> rcap f e > 0} - set rs \<union> erev ` set rs \<longleftrightarrow>
        (r \<in> \<EE> \<and> rcap f r > 0 \<and> r \<notin> set rs) \<or> erev r \<in> set rs"
      using erev_img[of r] by blast
    ultimately show "r \<in> {e | e. e \<in> \<EE> \<and> rcap g e > 0} \<longleftrightarrow>
        r \<in> {e | e. e \<in> \<EE> \<and> rcap f e > 0} - set rs \<union> erev ` set rs"
      using res_g[of r] by blast
  qed
qed

text \<open>For a walk from \<open>s\<close> to \<open>t\<close>, the augmentation increases the value of an \<open>s\<close>-\<open>t\<close> flow by one.\<close>

theorem augment_unit:
  assumes f: "f is s -- t flow" "unit_flow f"
    and p: "distinct p" "vwalk_bet (to_vertex_pair ` {e | e. e \<in> \<EE> \<and> rcap f e > 0}) s p t"
    and rs: "map to_vertex_pair rs = edges_of_vwalk p"
      "set rs \<subseteq> {e | e. e \<in> \<EE> \<and> rcap f e > 0}"
  defines "g \<equiv> augment_edges f 1 rs"
  shows "g is s -- t flow" "unit_flow g" "ex g t = ex f t + 1"
    "{e | e. e \<in> \<EE> \<and> rcap g e > 0} =
       {e | e. e \<in> \<EE> \<and> rcap f e > 0} - set rs \<union> erev ` set rs"
    "d \<notin> \<E> \<Longrightarrow> g d = f d"
proof -
  have sV: "s \<in> \<V>" and tV: "t \<in> \<V>" and st: "s \<noteq> t" and fs: "ex f s \<le> 0"
    and cons: "\<And>v. \<lbrakk>v \<in> \<V>; v \<noteq> s; v \<noteq> t\<rbrakk> \<Longrightarrow> ex f v = 0"
    using f(1) by (auto elim: is_s_t_flowE)
  have bflow: "f is (\<lambda>v. - ex f v) flow"
    using f(1) by (auto intro: isbflowI elim: is_s_t_flowE)
  note aug = augment_unit_walk[OF bflow f(2) p st rs, folded g_def]
  have ex_g: "ex g v = (if v = s then ex f v - 1 else if v = t then ex f v + 1 else ex f v)"
    if "v \<in> \<V>" for v
    using aug(1) that by (auto elim!: isbflowE)
  show "g is s -- t flow"
    using aug(1) sV tV st fs cons ex_g by (auto intro!: is_s_t_flowI elim: isbflowE)
  show "ex g t = ex f t + 1"
    using ex_g[OF tV] st by simp
  show "unit_flow g" "{e | e. e \<in> \<EE> \<and> rcap g e > 0} =
       {e | e. e \<in> \<EE> \<and> rcap f e > 0} - set rs \<union> erev ` set rs"
    by (rule aug(2), rule aug(3))
  show "g d = f d" if "d \<notin> \<E>"
    by (rule aug(4)[OF that])
qed

end

end
