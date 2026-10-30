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
subsection \<open>Unit Networks and Unit Flows\<close>

locale unit_network = flow_network +
  assumes unit_caps: "\<And>e. e \<in> \<E> \<Longrightarrow> \<u> e = 1"
begin

abbreviation unit_flow where
  "unit_flow f \<equiv> isuflow f \<and> is_integral_flow f"

lemma unit_flow_values:
  assumes "unit_flow f" "e \<in> \<E>"
  shows "f e = 0 \<or> f e = 1"
proof-
  obtain n :: int where "f e = n"
    using assms
    by (auto simp: is_integral_flow_def)
  moreover have "0 \<le> f e" "ereal (f e) \<le> 1"
    using assms unit_caps[of e]
    by (auto elim!: isuflowE)
  ultimately show ?thesis
    by (auto simp: one_ereal_def)
qed

text \<open>The residual edges of positive capacity of a unit flow.\<close>

lemma unit_residual:
  assumes "unit_flow f"
  shows "F d \<in> \<EE> \<and> rcap f (F d) > 0 \<longleftrightarrow> d \<in> \<E> \<and> f d = 0"
    and "B d \<in> \<EE> \<and> rcap f (B d) > 0 \<longleftrightarrow> d \<in> \<E> \<and> f d = 1"
  using o_edge_res[of "F d"] o_edge_res[of "B d"] unit_flow_values[OF assms, of d] unit_caps[of d]
  by (auto simp: one_ereal_def)

lemma unit_residual_rcap:
  assumes "unit_flow f" "r \<in> \<EE>" "rcap f r > 0"
  shows "rcap f r = 1" and "\<not> rcap f (erev r) > 0"
  using assms unit_residual[OF assms(1), of "oedge r"] unit_caps[of "oedge r"]
  by (cases r; auto simp: one_ereal_def)+

lemma zero_unit_flow:
  shows "unit_flow (\<lambda>_. 0)"
    and "{e | e. e \<in> \<EE> \<and> rcap (\<lambda>_. 0) e > 0} = F ` \<E>"
proof-
  show "unit_flow (\<lambda>_. 0)"
    using u_non_neg
    by (auto intro!: isuflowI exI[of _ "0::int"] simp: is_integral_flow_def zero_ereal_def)
  show "{e | e. e \<in> \<EE> \<and> rcap (\<lambda>_. 0) e > 0} = F ` \<E>"
  proof(rule set_eqI)
    show "r \<in> {e | e. e \<in> \<EE> \<and> rcap (\<lambda>_. 0) e > 0} \<longleftrightarrow> r \<in> F ` \<E>" for r
      using unit_residual[OF \<open>unit_flow (\<lambda>_. 0)\<close>]
      by (cases r) auto
  qed
qed

subsection \<open>Augmenting a Unit Flow by One\<close>

text \<open>Augmenting along the lift of a distinct walk from \<open>s\<close> to \<open>t\<close> moves one unit of balance from
\<open>t\<close> to \<open>s\<close>, and swaps the residual edges on the walk for their reverses.\<close>

lemma augment_unit_walk:
  assumes "f is b flow" "unit_flow f" "distinct p"
    "vwalk_bet (to_vertex_pair ` {e | e. e \<in> \<EE> \<and> rcap f e > 0}) s p t" "s \<noteq> t"
    "map to_vertex_pair rs = edges_of_vwalk p" "set rs \<subseteq> {e | e. e \<in> \<EE> \<and> rcap f e > 0}"
  defines "g \<equiv> augment_edges f 1 rs"
  shows "g is (\<lambda>v. if v = s then b v + 1 else if v = t then b v - 1 else b v) flow"
    and "unit_flow g"
    and "{e | e. e \<in> \<EE> \<and> rcap g e > 0} =
      {e | e. e \<in> \<EE> \<and> rcap f e > 0} - set rs \<union> erev ` set rs"
    and "d \<notin> \<E> \<Longrightarrow> g d = f d"
proof-
  have "awalk UNIV s (map to_vertex_pair rs) t" "rs \<noteq> []"
    using vwalk_imp_awalk[OF assms(4)] assms(5,6)
    by (auto simp: awalk_Nil_iff intro: subset_mono_awalk)
  moreover from this have "fstv (hd rs) = s" "sndv (last rs) = t"
    using cas_hd_last[of s "map to_vertex_pair rs" t]
    by (auto simp: awalk_def hd_map last_map to_vertex_pair_fst_snd)
  moreover have "ereal 1 \<le> Rcap f (set rs)"
    using assms(7) unit_residual_rcap(1)[OF assms(2)] \<open>rs \<noteq> []\<close>
    by (intro RcapI) (auto simp: one_ereal_def subset_iff)
  ultimately have "augpath f rs"
    by (auto intro!: augpathI prepathI intro: order.strict_trans2[of 0 "ereal 1"])
  moreover have "distinct (map oedge rs)"
  proof-
    have "x = y" if "x \<in> set rs" "y \<in> set rs" "oedge x = oedge y" for x y
      using oedge_eq_cases[OF that(3)] that(1,2) assms(7) unit_residual_rcap(2)[OF assms(2), of y]
      by blast
    then show ?thesis
      using distinct_edges_of_vwalk[OF assms(3)] assms(6)[symmetric]
      by (auto simp: distinct_map inj_on_def)
  qed
  ultimately show "g is (\<lambda>v. if v = s then b v + 1 else if v = t then b v - 1 else b v) flow"
    using assms(5,7)
    by (auto simp: distinct_map
        intro!: augment_path_validness_b_pres_source_target_distinct[OF assms(1) _ _
          \<open>ereal 1 \<le> Rcap f (set rs)\<close>, unfolded \<open>fstv (hd rs) = s\<close> \<open>sndv (last rs) = t\<close>,
          folded g_def])
  then show "unit_flow g"
    using assms(2,7) augment_edges_integral[of f 1 rs]
    by (auto simp: g_def elim: isbflowE)
  have "F d \<in> set rs \<Longrightarrow> d \<in> \<E> \<and> f d = 0"
    "B d \<in> set rs \<Longrightarrow> d \<in> \<E> \<and> f d = 1" for d
    using assms(7) unit_residual[OF assms(2), of d]
    by blast+
  moreover from this show "d \<notin> \<E> \<Longrightarrow> g d = f d"
    using augment_edges_distinct[OF \<open>distinct (map oedge rs)\<close>, of f 1 d, folded g_def]
    by (cases "F d \<in> set rs"; cases "B d \<in> set rs") simp_all
  ultimately have "(F d \<in> \<EE> \<and> rcap g (F d) > 0) \<longleftrightarrow>
      (F d \<in> \<EE> \<and> rcap f (F d) > 0) \<and> F d \<notin> set rs \<or> B d \<in> set rs"
    "(B d \<in> \<EE> \<and> rcap g (B d) > 0) \<longleftrightarrow>
      (B d \<in> \<EE> \<and> rcap f (B d) > 0) \<and> B d \<notin> set rs \<or> F d \<in> set rs" for d
    unfolding unit_residual[OF assms(2)] unit_residual[OF \<open>unit_flow g\<close>]
    using augment_edges_distinct[OF \<open>distinct (map oedge rs)\<close>, of f 1 d, folded g_def]
    by (cases "F d \<in> set rs"; cases "B d \<in> set rs"; force)+
  then have "r \<in> {e | e. e \<in> \<EE> \<and> rcap g e > 0} \<longleftrightarrow>
      r \<in> {e | e. e \<in> \<EE> \<and> rcap f e > 0} - set rs \<union> erev ` set rs" for r
    using inj_image_mem_iff[OF inj_erev_general, of "erev r" "set rs", unfolded erve_erve_id]
    by (cases r) simp_all
  then show "{e | e. e \<in> \<EE> \<and> rcap g e > 0} =
      {e | e. e \<in> \<EE> \<and> rcap f e > 0} - set rs \<union> erev ` set rs"
    by blast
qed

text \<open>For a walk from \<open>s\<close> to \<open>t\<close>, the augmentation increases the value of an \<open>s\<close>-\<open>t\<close> flow
by one.\<close>

lemma augment_unit:
  assumes "f is s -- t flow" "unit_flow f" "distinct p"
    "vwalk_bet (to_vertex_pair ` {e | e. e \<in> \<EE> \<and> rcap f e > 0}) s p t"
    "map to_vertex_pair rs = edges_of_vwalk p" "set rs \<subseteq> {e | e. e \<in> \<EE> \<and> rcap f e > 0}"
  defines "g \<equiv> augment_edges f 1 rs"
  shows "g is s -- t flow" "unit_flow g" "ex g t = ex f t + 1"
    "{e | e. e \<in> \<EE> \<and> rcap g e > 0} =
      {e | e. e \<in> \<EE> \<and> rcap f e > 0} - set rs \<union> erev ` set rs"
    "d \<notin> \<E> \<Longrightarrow> g d = f d"
proof-
  have "f is (\<lambda>v. - ex f v) flow" "s \<noteq> t"
    using assms(1)
    by (auto intro: isbflowI elim: is_s_t_flowE)
  note aug = augment_unit_walk[OF this(1) assms(2-4) this(2) assms(5,6), folded g_def]
  then show "unit_flow g"
    "{e | e. e \<in> \<EE> \<and> rcap g e > 0} =
      {e | e. e \<in> \<EE> \<and> rcap f e > 0} - set rs \<union> erev ` set rs"
    "d \<notin> \<E> \<Longrightarrow> g d = f d"
    by simp_all
  have "ex g v = (if v = s then ex f v - 1 else if v = t then ex f v + 1 else ex f v)" if "v \<in> \<V>" for v
    using aug(1) that
    by (auto elim!: isbflowE)
  then show "g is s -- t flow" "ex g t = ex f t + 1"
    using aug(1) assms(1) \<open>s \<noteq> t\<close>
    by (auto intro!: is_s_t_flowI elim!: is_s_t_flowE isbflowE)
qed

end

end
