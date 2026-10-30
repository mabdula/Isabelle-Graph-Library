theory Optimality_Certification
  imports Cost_Optimality Directed_Set_Graphs.Multigraph_Potentials
begin

provenance human

context
  cost_flow_network
begin

text \<open>Around an augmenting cycle the potentials telescope away, so a lower bound \<open>-\<epsilon>\<close> on
      the reduced cost of each arc bounds the cost of the cycle by \<open>-\<epsilon>\<close> times its length.\<close>

lemma augcycle_cost_ge_reduced_cost_bound:
  assumes "augcycle f C"
    "\<And>e. e \<in> set C \<Longrightarrow> - \<epsilon> \<le> \<cc> e + \<pi> (fstv e) - \<pi> (sndv e)"
  shows "- \<epsilon> * length C \<le> \<CC> C"
proof-
  have "prepath C" "fstv (hd C) = sndv (last C)" "distinct C"
    using assms(1)
    by (auto simp: augcycle_def augpath_def)
  moreover have "(\<Sum>e\<leftarrow>C. \<pi> (fstv e) - \<pi> (sndv e)) = \<pi> (fstv (hd C)) - \<pi> (sndv (last C))"
    by (induction rule: prepath_induct[OF \<open>prepath C\<close>]) auto
  ultimately have "(\<Sum>e\<in>set C. \<pi> (fstv e) - \<pi> (sndv e)) = 0"
    by (simp add: sum.distinct_set_conv_list)
  moreover have "(\<Sum>e\<in>set C. - \<epsilon>) \<le> (\<Sum>e\<in>set C. \<cc> e + \<pi> (fstv e) - \<pi> (sndv e))"
    by (intro sum_mono assms(2))
  ultimately show ?thesis
    using \<open>distinct C\<close>
    by (simp add: \<CC>_def sum.distrib sum_subtractf distinct_card mult.commute)
qed

lemma optimality_from_potentials:
  assumes "f is b flow"
    "\<And>e. \<lbrakk>e \<in> \<E>; f e = 0; \<u> e \<noteq> 0\<rbrakk>
       \<Longrightarrow> \<c> e + \<pi> (fst e) - \<pi> (snd e) \<ge> 0"
    "\<And>e. \<lbrakk>e \<in> \<E>; f e = \<u> e; \<u> e \<noteq> 0\<rbrakk>
       \<Longrightarrow> \<c> e + \<pi> (fst e) - \<pi> (snd e) \<le> 0"
    "\<And>e. \<lbrakk>e \<in> \<E>; f e > 0; f e < \<u> e\<rbrakk>
       \<Longrightarrow> \<c> e + \<pi> (fst e) - \<pi> (snd e) = 0"
  shows "is_Opt b f"
proof(rule ccontr)
  assume "\<not> is_Opt b f"
  then obtain C where "augcycle f C"
    using is_opt_iff_no_augcycle assms(1)
    by blast
  have "\<And>d. d \<in> \<E> \<Longrightarrow> 0 \<le> f d \<and> ereal (f d) \<le> \<u> d"
    using assms(1)
    by (auto simp: isbflow_def isuflow_def)
  hence "\<And>d. \<lbrakk>d \<in> \<E>; ereal (f d) < \<u> d\<rbrakk>
           \<Longrightarrow> 0 \<le> \<c> d + \<pi> (fst d) - \<pi> (snd d)"
    and "\<And>d. \<lbrakk>d \<in> \<E>; 0 < f d\<rbrakk> \<Longrightarrow> \<c> d + \<pi> (fst d) - \<pi> (snd d) \<le> 0"
    using assms(2-4)
    by (force simp: le_less)+
  moreover have "0 < \<u> d - ereal (f d) \<Longrightarrow> ereal (f d) < \<u> d" for d
    by (cases "\<u> d") auto
  moreover have "\<And>e. e \<in> set C \<Longrightarrow> 0 < rcap f e \<and> e \<in> \<EE>"
    using \<open>augcycle f C\<close>
    by (auto simp: augcycle_def intro: augpath_rcap_pos_strict')
  ultimately have "\<And>e. e \<in> set C \<Longrightarrow> - 0 \<le> \<cc> e + \<pi> (fstv e) - \<pi> (sndv e)"
    by (fastforce simp: \<EE>_def)
  thus False
    using augcycle_cost_ge_reduced_cost_bound[of f C 0 \<pi>] \<open>augcycle f C\<close>
    by (auto simp: augcycle_def)
qed

text \<open>\<open>Cost_Optimality\<close> interprets \<open>residual_flow\<close> inside its own
      \<open>context\<close> block only, so the interpretation is repeated here.\<close>

interpretation residual_flow: cost_flow_network where
  fst = fstv and snd = sndv and create_edge = create_edge_residual and
  \<E> = \<EE> and \<c> = \<cc> and \<u> = "\<lambda> _. PInfty"
  using make_pair create_edge E_not_empty oedge_on_\<EE>
  by (auto simp: finite_\<EE> make_pair[OF refl refl] create_edge cost_flow_network_def
                 flow_network_axioms_def flow_network_def multigraph_def)

text \<open>For integral costs, an \<^emph>\<open>M-scaled\<close> relaxation of
      \<open>optimality_from_potentials\<close> also certifies optimality: it only asks
      \<open>M \<sqdot> (reduced cost) \<ge> -1\<close> on every residual arc, for an integer \<open>M\<close> above
      the vertex count. If \<open>f\<close> were not optimal, there would be a negative augmenting cycle
      \<open>C\<close> with at most \<open>n\<close> arcs. Summing over \<open>C\<close>, the potentials telescope
      away and \<open>M \<sqdot> cost(C) \<ge> -n\<close>; as \<open>cost(C)\<close> is a negative integer,
      \<open>M \<sqdot> cost(C) \<le> -M < -n\<close>. The length bound needs a \<^emph>\<open>vertex-simple\<close>
      cycle: \<open>augcycle\<close> only asks for distinct arcs. \<open>exists_short_neg_augcycle\<close> obtains
      one from \<open>find_flow_cycle_in_circ\<close>, which visits every vertex at most once.\<close>

lemma residual_flow_vertices_eq: "residual_flow.\<V> = \<V>"
  using fst_E_V snd_E_V
  unfolding residual_flow_make_pair \<EE>_def
  by (auto elim!: in_dVsE simp: make_pair_def) force+

text \<open>If each vertex has at most one outgoing and one incoming arc of a cycle, the tails of its arcs are
      distinct, so the cycle has at most \<open>card \<V>\<close> arcs.\<close>

lemma vertex_simple_bound:
  assumes "set es \<subseteq> \<EE>" "distinct es"
    "\<forall>v\<in>\<V>. (\<exists> eov eiv. residual_flow.delta_plus v \<inter> set es = {eov} \<and>
                       residual_flow.delta_minus v \<inter> set es = {eiv}) \<or>
           (residual_flow.delta_plus v \<inter> set es = {} \<and> residual_flow.delta_minus v \<inter> set es = {})"
  shows "length es \<le> card \<V>"
proof-
  have "fstv ` set es \<subseteq> \<V>"
    using assms(1) residual_flow.fst_E_V residual_flow_vertices_eq
    by auto
  moreover have "inj_on fstv (set es)"
  proof(rule inj_onI)
    fix e1 e2
    assume "e1 \<in> set es" "e2 \<in> set es" "fstv e1 = fstv e2"
    moreover hence "{e1, e2} \<subseteq> residual_flow.delta_plus (fstv e1) \<inter> set es" "fstv e1 \<in> \<V>"
      using assms(1) \<open>fstv ` set es \<subseteq> \<V>\<close>
      by (auto simp: residual_flow.delta_plus_def)
    ultimately obtain eov where "residual_flow.delta_plus (fstv e1) \<inter> set es = {eov}"
      using assms(3)
      by blast
    thus "e1 = e2"
      using \<open>{e1, e2} \<subseteq> residual_flow.delta_plus (fstv e1) \<inter> set es\<close>
      by auto
  qed
  hence "length es = card (fstv ` set es)"
    using assms(2)
    by (simp add: card_image distinct_card)
  thus ?thesis
    using \<open>fstv ` set es \<subseteq> \<V>\<close> \<V>_finite
    by (simp add: card_mono)
qed

lemma flowcycle_min_value_props:
  assumes "residual_flow.flowcycle g es"
  shows "\<And>e. e \<in> set es \<Longrightarrow> Min (g ` set es) \<le> g e"
    "\<exists>e\<in>set es. g e = Min (g ` set es)"
    "Min (g ` set es) > 0"
proof-
  have "es \<noteq> []" "\<forall>e\<in>set es. 0 < g e"
    using assms residual_flow.flowpath_es_non_neg
    by (auto simp: residual_flow.flowcycle_def)
  thus "\<And>e. e \<in> set es \<Longrightarrow> Min (g ` set es) \<le> g e"
    "\<exists>e\<in>set es. g e = Min (g ` set es)"
    "Min (g ` set es) > 0"
    using Min_in[of "g ` set es"]
    by (auto simp: image_iff Min_le_iff)
qed

lemma cycle_indicator_is_circ:
  assumes "\<forall>v\<in>\<V>. (\<exists> eov eiv. residual_flow.delta_plus v \<inter> set es = {eov} \<and>
                             residual_flow.delta_minus v \<inter> set es = {eiv}) \<or>
                  (residual_flow.delta_plus v \<inter> set es = {} \<and> residual_flow.delta_minus v \<inter> set es = {})"
  shows "residual_flow.is_circ (\<lambda>e. if e \<in> set es then \<gamma> else 0)"
  unfolding residual_flow.is_circ_def residual_flow.ex_def residual_flow_vertices_eq
  using assms residual_flow.delta_minus_finite residual_flow.delta_plus_finite
  by (auto simp: sum.If_cases)

lemma is_circ_diff:
  "\<lbrakk>residual_flow.is_circ g1; residual_flow.is_circ g2\<rbrakk>
   \<Longrightarrow> residual_flow.is_circ (\<lambda>e. g1 e - g2 e)"
  by (auto simp: residual_flow.is_circ_def residual_flow.ex_def sum_subtractf)

text \<open>A non-negative circulation of negative cost contains a vertex-simple cycle of negative cost. As in
      \<open>flowcycle_decomposition\<close>, a cycle is peeled off by \<open>find_flow_cycle_in_circ\<close>; if its
      cost is not negative, the remaining circulation has smaller support and negative cost.\<close>

lemma exists_short_neg_augcycle:
  assumes "n = card (residual_flow.support g)" "residual_flow.flow_non_neg g"
    "residual_flow.is_circ g" "residual_flow.\<C> g < 0"
  shows "\<exists>es. residual_flow.flowcycle g es \<and> set es \<subseteq> residual_flow.support g \<and> distinct es \<and>
              length es \<le> card \<V> \<and> (\<Sum>e\<in>set es. \<cc> e) < 0"
  using assms
proof(induction n arbitrary: g rule: less_induct)
  case (less n)
  have "\<exists>e\<in>\<EE>. 0 < g e"
  proof(rule ccontr)
    assume "\<not> (\<exists>e\<in>\<EE>. 0 < g e)"
    hence "residual_flow.\<C> g = 0"
      using less.prems(2)
      by (force simp: residual_flow.\<C>_def residual_flow.flow_non_neg_def intro!: sum.neutral)
    thus False
      using less.prems(4)
      by simp
  qed
  hence "0 < residual_flow.Abs g"
    using less.prems(2) finite_\<EE>
    by (force simp: residual_flow.Abs_def residual_flow.flow_non_neg_def intro: sum_pos2)
  then obtain es where "residual_flow.flowcycle g es" "set es \<subseteq> residual_flow.support g" "distinct es"
    "\<forall>v\<in>\<V>. (\<exists> eov eiv. residual_flow.delta_plus v \<inter> set es = {eov} \<and>
                       residual_flow.delta_minus v \<inter> set es = {eiv}) \<or>
           (residual_flow.delta_plus v \<inter> set es = {} \<and> residual_flow.delta_minus v \<inter> set es = {})"
    using residual_flow.find_flow_cycle_in_circ less.prems(2,3) residual_flow_vertices_eq
    by force
  moreover hence "set es \<subseteq> \<EE>"
    "\<And>\<gamma>. residual_flow.is_circ (\<lambda>e. if e \<in> set es then \<gamma> else 0)"
    by (auto simp: residual_flow.support_def cycle_indicator_is_circ)
  ultimately have "length es \<le> card \<V>"
    by (blast intro: vertex_simple_bound)
  show ?case
  proof(cases "(\<Sum>e\<in>set es. \<cc> e) < 0")
    case True
    thus ?thesis
      using \<open>residual_flow.flowcycle g es\<close> \<open>set es \<subseteq> residual_flow.support g\<close>
        \<open>distinct es\<close>
        \<open>length es \<le> card \<V>\<close>
      by blast
  next
    case False
    define \<gamma> where "\<gamma> = Min (g ` set es)"
    define g' where "g' = (\<lambda>e. g e - (if e \<in> set es then \<gamma> else 0))"
    have "residual_flow.\<C> g' = residual_flow.\<C> g - \<gamma> * (\<Sum>e\<in>set es. \<cc> e)"
      using \<open>set es \<subseteq> \<EE>\<close> finite_\<EE>
      by (simp add: g'_def residual_flow.\<C>_def left_diff_distrib sum_subtractf sum_distrib_left
                    sum.If_cases Int_absorb1 if_distrib if_distribR Diff_eq sum.subset_diff[of "set es" \<EE>])
    moreover have \<gamma>: "\<And>e. e \<in> set es \<Longrightarrow> \<gamma> \<le> g e"
      "\<exists>e\<in>set es. g e = \<gamma>" "\<gamma> > 0"
      using flowcycle_min_value_props \<open>residual_flow.flowcycle g es\<close>
      unfolding \<gamma>_def
      by auto
    ultimately have "residual_flow.\<C> g' < 0"
      using False less.prems(4) mult_nonneg_nonneg[of \<gamma> "\<Sum>e\<in>set es. \<cc> e"]
      by linarith
    moreover have "residual_flow.flow_non_neg g'" "residual_flow.support g' \<subset> residual_flow.support g"
      using \<gamma> less.prems(2) \<open>set es \<subseteq> residual_flow.support g\<close>
      by (auto simp: g'_def residual_flow.flow_non_neg_def residual_flow.support_def)
    moreover have "residual_flow.is_circ g'"
      using less.prems(3) \<open>\<And>\<gamma>. residual_flow.is_circ (\<lambda>e. if e \<in> set es then \<gamma> else 0)\<close>
      by (simp add: g'_def is_circ_diff)
    moreover have "card (residual_flow.support g') < n"
      using \<open>residual_flow.support g' \<subset> residual_flow.support g\<close> less.prems(1) finite_\<EE>
      by (auto intro!: psubset_card_mono simp: residual_flow.support_def)
    ultimately obtain es' where "residual_flow.flowcycle g' es'" "set es' \<subseteq> residual_flow.support g'"
      "distinct es'" "length es' \<le> card \<V>" "(\<Sum>e\<in>set es'. \<cc> e) < 0"
      using less.IH
      by blast
    thus ?thesis
      using residual_flow.flow_cyc_mono[of g' es' g]
        \<open>residual_flow.support g' \<subset> residual_flow.support g\<close> \<gamma>(3)
      by (fastforce simp: g'_def)
  qed
qed

text \<open>A non-optimal \<open>b\<close>-flow \<open>f\<close> has an \<open>augcycle\<close> of length at most the
      vertex count: the difference to a cheaper \<open>b\<close>-flow is a residual circulation of negative cost.\<close>

lemma short_augcycle_from_not_opt:
  assumes "f is b flow" "\<not> is_Opt b f"
  shows "\<exists>es. augcycle f es \<and> length es \<le> card \<V>"
proof-
  obtain f' where f': "\<C> f' < \<C> f" "f' is b flow"
    using assms
    unfolding is_Opt_def
    by force
  moreover hence "isuflow f" "isuflow f'"
    using assms(1)
    by (auto simp: isbflow_def)
  ultimately obtain es where es: "residual_flow.flowcycle (difference f' f) es"
    "set es \<subseteq> residual_flow.support (difference f' f)" "distinct es" "length es \<le> card \<V>"
    "(\<Sum>e\<in>set es. \<cc> e) < 0"
    using exists_short_neg_augcycle[OF refl difference_flow_pos[of f f'] diff_is_res_circ[OF assms(1) f'(2)]]
      rcost_difference[of f' f]
    by auto
  have "\<forall>e\<in>set es. 0 < rcap f e"
    using es(2) pos_difference_pos_rcap[OF \<open>isuflow f\<close> \<open>isuflow f'\<close>]
    by (auto simp: residual_flow.support_def)
  hence "augpath f es"
    using es(1) ext[of to_vertex_pair make_pair_residual] Min_gr_iff[of "rcap f ` set es"]
    by (auto simp: augpath_def prepath_def residual_flow.flowcycle_def residual_flow.flowpath_def
                   to_vertex_pair_fst_snd residual_flow.multigraph_path_def Rcap_def)
  thus ?thesis
    using es
    by (intro exI[of _ es])
       (auto simp: augcycle_def \<CC>_def residual_flow.flowcycle_def residual_flow.support_def
                   sum.distinct_set_conv_list)
qed

text \<open>The cost of a \<open>b\<close>-flow in terms of reduced costs, and the bounds \<open>L\<close> and
      \<open>U\<close> on it that follow from \<open>0 \<le> g e \<le> u e\<close> for finite capacities.\<close>

lemma flow_cost_reduced_cost:
  assumes "g is b flow"
  shows "\<C> g = (\<Sum>e\<in>\<E>. (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * g e) - (\<Sum>v\<in>\<V>. \<pi> v * b v)"
proof-
  have "fst ` \<E> \<subseteq> \<V>" "snd ` \<E> \<subseteq> \<V>"
    using fst_E_V snd_E_V
    by auto
  hence "(\<Sum>e\<in>\<E>. \<pi> (fst e) * g e) = (\<Sum>v\<in>\<V>. \<pi> v * sum g (\<delta>\<^sup>+ v))"
    "(\<Sum>e\<in>\<E>. \<pi> (snd e) * g e) = (\<Sum>v\<in>\<V>. \<pi> v * sum g (\<delta>\<^sup>- v))"
    using sum.group[OF finite_E \<V>_finite, of fst "\<lambda>e. \<pi> (fst e) * g e"]
      sum.group[OF finite_E \<V>_finite, of snd "\<lambda>e. \<pi> (snd e) * g e"]
    by (simp_all add: delta_plus_def delta_minus_def sum_distrib_left)
  moreover have "\<forall>v\<in>\<V>. b v = sum g (\<delta>\<^sup>+ v) - sum g (\<delta>\<^sup>- v)"
    using assms
    unfolding isbflow_def ex_def
    by force
  hence "(\<Sum>v\<in>\<V>. \<pi> v * b v)
         = (\<Sum>v\<in>\<V>. \<pi> v * sum g (\<delta>\<^sup>+ v)) - (\<Sum>v\<in>\<V>. \<pi> v * sum g (\<delta>\<^sup>- v))"
    by (simp add: right_diff_distrib sum_subtractf)
  moreover have "(\<Sum>e\<in>\<E>. (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * g e)
                 = \<C> g + (\<Sum>e\<in>\<E>. \<pi> (fst e) * g e) - (\<Sum>e\<in>\<E>. \<pi> (snd e) * g e)"
    by (simp add: \<C>_def ring_distribs sum.distrib sum_subtractf mult.commute)
  ultimately show ?thesis
    by linarith
qed

lemma flow_cost_ge_min_bound:
  assumes "g is b flow" "\<forall>e\<in>\<E>. \<u> e \<noteq> \<infinity>"
  shows "(\<Sum>e\<in>\<E>. min 0 (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * real_of_ereal (\<u> e))
         - (\<Sum>v\<in>\<V>. \<pi> v * b v)
         \<le> \<C> g"
proof-
  have "(\<Sum>e\<in>\<E>. min 0 (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * real_of_ereal (\<u> e))
        \<le> (\<Sum>e\<in>\<E>. (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * g e)"
    using flow_le_real_capacity[OF assms]
    by (intro sum_mono) (auto simp: min_def mult_left_mono_neg)
  thus ?thesis
    using flow_cost_reduced_cost[OF assms(1), of \<pi>]
    by linarith
qed

lemma flow_cost_le_max_bound:
  assumes "g is b flow" "\<forall>e\<in>\<E>. \<u> e \<noteq> \<infinity>"
  shows "\<C> g
         \<le> (\<Sum>e\<in>\<E>. max 0 (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * real_of_ereal (\<u> e))
           - (\<Sum>v\<in>\<V>. \<pi> v * b v)"
proof-
  have "(\<Sum>e\<in>\<E>. (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * g e)
        \<le> (\<Sum>e\<in>\<E>. max 0 (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * real_of_ereal (\<u> e))"
    using flow_le_real_capacity[OF assms]
    by (intro sum_mono) (auto simp: max_def mult_left_mono mult_nonpos_nonneg)
  thus ?thesis
    using flow_cost_reduced_cost[OF assms(1), of \<pi>]
    by linarith
qed

text \<open>Two consequences of \<open>\<epsilon>\<close>-complementary slackness (no residual arc has reduced cost
      below \<open>-\<epsilon>\<close>). Without any integrality, \<open>f\<close> is
      \<open>\<delta>\<close>-cost-optimal for \<open>\<delta>\<close> = \<open>\<epsilon>\<close> times the total
      capacity (\<open>eps_dual_slack_imp_eps_cost_optimal\<close>). With integral costs and
      \<open>n \<epsilon> < 1\<close>, \<open>f\<close> is exactly optimal
      (\<open>optimality_from_eps_potentials\<close>, Tardos 1985, Goldberg--Tarjan 1990).\<close>

definition eps_cost_optimal ::
  "real \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('edge \<Rightarrow> real) \<Rightarrow> bool" where
  "eps_cost_optimal \<delta> b f \<longleftrightarrow>
     (\<exists> fstar. is_Opt b fstar \<and> \<bar>\<C> f - \<C> fstar\<bar> / (1 + \<bar>\<C> fstar\<bar>) \<le> \<delta>)"

lemma eps_dual_slack_imp_eps_cost_optimal:
  assumes "f is b flow" "0 \<le> \<epsilon>" "\<forall>e\<in>\<E>. \<u> e \<noteq> \<infinity>"
    "\<forall>e\<in>\<EE>. \<uu>\<^bsub>f\<^esub>e > 0 \<longrightarrow> \<cc> e + \<pi> (fstv e) - \<pi> (sndv e) \<ge> - \<epsilon>"
    "is_Opt b fstar"
  shows "eps_cost_optimal (\<epsilon> * (\<Sum>e\<in>\<E>. real_of_ereal (\<u> e))) b f"
proof-
  have "(\<c> e + \<pi> (fst e) - \<pi> (snd e)) * f e
        - min 0 (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * real_of_ereal (\<u> e)
        \<le> \<epsilon> * real_of_ereal (\<u> e)" if "e \<in> \<E>" for e
  proof-
    have "0 \<le> f e" "f e \<le> real_of_ereal (\<u> e)"
      using flow_le_real_capacity[OF assms(1,3) that]
      by auto
    moreover have "f e < real_of_ereal (\<u> e) \<Longrightarrow> - \<epsilon> \<le> \<c> e + \<pi> (fst e) - \<pi> (snd e)"
      "0 < f e \<Longrightarrow> \<c> e + \<pi> (fst e) - \<pi> (snd e) \<le> \<epsilon>"
      using assms(3,4) that u_non_neg[of e]
      by (cases "\<u> e"; force simp: \<EE>_def)+
    ultimately show ?thesis
      using assms(2) mult_mono[of "\<c> e + \<pi> (fst e) - \<pi> (snd e)" \<epsilon> "f e" "real_of_ereal (\<u> e)"]
        mult_mono[of "\<pi> (snd e) - \<c> e - \<pi> (fst e)" \<epsilon>
          "real_of_ereal (\<u> e) - f e" "real_of_ereal (\<u> e)"]
      by (cases "f e = 0"; cases "f e = real_of_ereal (\<u> e)") (auto simp: min_def algebra_simps)
  qed
  hence "(\<Sum>e\<in>\<E>. (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * f e)
         - (\<Sum>e\<in>\<E>. min 0 (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * real_of_ereal (\<u> e))
         \<le> \<epsilon> * (\<Sum>e\<in>\<E>. real_of_ereal (\<u> e))"
    unfolding sum_distrib_left sum_subtractf[symmetric]
    by (rule sum_mono)
  moreover have "fstar is b flow" "\<C> fstar \<le> \<C> f"
    using assms(1,5)
    by (auto simp: is_Opt_def)
  ultimately have "0 \<le> \<C> f - \<C> fstar"
    "\<C> f - \<C> fstar \<le> \<epsilon> * (\<Sum>e\<in>\<E>. real_of_ereal (\<u> e))"
    using flow_cost_ge_min_bound[of fstar b \<pi>] flow_cost_reduced_cost[OF assms(1), of \<pi>] assms(3)
    by linarith+
  moreover have "(\<C> f - \<C> fstar) / (1 + \<bar>\<C> fstar\<bar>) \<le> (\<C> f - \<C> fstar) / 1"
    using calculation(1)
    by (intro divide_left_mono) auto
  ultimately show ?thesis
    using assms(5)
    unfolding eps_cost_optimal_def
    by (intro exI[of _ fstar]) auto
qed

lemma optimality_from_eps_potentials:
  fixes \<epsilon> :: real
  assumes "f is b flow" "0 < \<epsilon>" "real (card \<V>) * \<epsilon> < 1"
    "\<And>e. e \<in> \<EE> \<Longrightarrow> \<cc> e \<in> \<int>"
    "\<forall>e\<in>\<EE>. \<uu>\<^bsub>f\<^esub>e > 0 \<longrightarrow> \<cc> e + \<pi> (fstv e) - \<pi> (sndv e) \<ge> - \<epsilon>"
  shows "is_Opt b f"
proof(rule ccontr)
  assume "\<not> is_Opt b f"
  then obtain C where "augcycle f C" "length C \<le> card \<V>"
    using short_augcycle_from_not_opt assms(1)
    by blast
  moreover hence "\<And>e. e \<in> set C \<Longrightarrow> 0 < rcap f e \<and> e \<in> \<EE>"
    by (auto simp: augcycle_def intro: augpath_rcap_pos_strict')
  hence "- \<epsilon> * length C \<le> \<CC> C"
    using assms(5) \<open>augcycle f C\<close>
    by (intro augcycle_cost_ge_reduced_cost_bound[of f C \<epsilon> \<pi>]) auto
  moreover have "\<CC> C \<in> \<int>" "\<CC> C < 0"
    using \<open>augcycle f C\<close> assms(4)
    by (auto simp: augcycle_def \<CC>_def)
  hence "\<CC> C \<le> -1"
    by (auto elim!: Ints_cases)
  moreover have "\<epsilon> * length C \<le> \<epsilon> * card \<V>"
    using assms(2) \<open>length C \<le> card \<V>\<close>
    by simp
  ultimately show False
    using assms(3)
    by (simp add: mult.commute[of \<epsilon>])
qed

lemma optimality_from_scaled_potentials:
  fixes M :: nat
  assumes "f is b flow" "card \<V> < M" "\<And>e. e \<in> \<EE> \<Longrightarrow> \<cc> e \<in> \<int>"
    "\<And>e. \<lbrakk>e \<in> \<EE>; \<uu>\<^bsub>f\<^esub>e > 0\<rbrakk>
          \<Longrightarrow> real M * \<cc> e + \<pi> (fstv e) - \<pi> (sndv e) \<ge> -1"
  shows "is_Opt b f"
proof-
  have "- (1 / real M) \<le> \<cc> e + \<pi> (fstv e) / real M - \<pi> (sndv e) / real M"
    if "e \<in> \<EE>" "\<uu>\<^bsub>f\<^esub>e > 0" for e
    using assms(2) divide_right_mono[OF assms(4)[OF that], of "real M"]
    by (simp add: diff_divide_distrib add_divide_distrib)
  moreover have "0 < 1 / real M" "real (card \<V>) * (1 / real M) < 1"
    using assms(2)
    by (auto simp: field_simps)
  ultimately show ?thesis
    using optimality_from_eps_potentials[OF assms(1) _ _ assms(3), of "1 / real M" "\<lambda>v. \<pi> v / real M"]
    by auto
qed

text \<open>Conversely, an optimal \<open>b\<close>-flow has no negative augmenting cycle, so the residual arcs of
      positive capacity carry a conservative cost function and admit potentials with exact
      complementary slackness. As slackness is monotone in \<open>\<epsilon>\<close>, this gives
      \<open>\<epsilon>\<close>-slackness for every \<open>\<epsilon> \<ge> 0\<close>.\<close>

lemma eps_complementary_slack_mono:
  "\<lbrakk>\<forall>e\<in>\<EE>. \<uu>\<^bsub>f\<^esub>e > 0 \<longrightarrow> \<cc> e + \<pi> (fstv e) - \<pi> (sndv e) \<ge> - \<epsilon>;
    \<epsilon> \<le> \<epsilon>'\<rbrakk> \<Longrightarrow>
   \<forall>e\<in>\<EE>. \<uu>\<^bsub>f\<^esub>e > 0 \<longrightarrow> \<cc> e + \<pi> (fstv e) - \<pi> (sndv e) \<ge> - \<epsilon>'"
  by fastforce

lemma is_Opt_imp_exact_complementary_slack:
  assumes "f is b flow" "is_Opt b f"
  shows "\<exists>\<pi>. \<forall>e\<in>\<EE>. \<uu>\<^bsub>f\<^esub>e > 0
                 \<longrightarrow> \<cc> e + \<pi> (fstv e) - \<pi> (sndv e) \<ge> 0"
proof(cases "{e \<in> \<EE>. \<uu>\<^bsub>f\<^esub>e > 0} = {}")
  case False
  interpret EF: multigraph where
    \<E> = "{e \<in> \<EE>. \<uu>\<^bsub>f\<^esub>e > 0}" and fst = fstv and snd = sndv
    and create_edge = create_edge_residual
    using False finite_\<EE> residual_flow.fst_create_edge residual_flow.snd_create_edge
    by unfold_locales auto
  have "EF.make_pair = to_vertex_pair"
    using EF.make_pair_function to_vertex_pair_fst_snd
    by simp
  hence "EF.conservative \<cc>"
  proof(intro EF.conservative_of_simple)
    fix es v
    assume "EF.make_pair = to_vertex_pair" "es \<noteq> []" "EF.path_bet es v v" "distinct es"
    moreover hence "prepath es" "set es \<subseteq> {e \<in> \<EE>. \<uu>\<^bsub>f\<^esub>e > 0}"
      using EF.path_bet_multigraph_path EF.path_bet_edges_subset
      by (auto simp: EF.multigraph_path_def prepath_def)
    ultimately have "augpath f es" "fstv (hd es) = sndv (last es)"
      using EF.path_bet_hd EF.path_bet_last
      by (auto simp: augpath_def intro!: Rcap_strictI)
    thus "EF.weight \<cc> es \<ge> 0"
      using min_cost_flow_no_augcycle[OF assms(2)] \<open>distinct es\<close> \<open>set es \<subseteq> _\<close>
      by (force simp: augcycle_def \<CC>_def EF.weight_def sum_list_distinct_conv_sum_set)
  qed
  then obtain \<pi>
    where "\<forall>e\<in>{e \<in> \<EE>. \<uu>\<^bsub>f\<^esub>e > 0}. \<cc> e + \<pi> (fstv e) - \<pi> (sndv e) \<ge> 0"
    using EF.potential_of_conservative
    by blast
  thus ?thesis
    by auto
qed auto

lemma is_Opt_imp_eps_complementary_slack:
  assumes "f is b flow" "is_Opt b f" "0 \<le> \<epsilon>"
  shows "\<exists>\<pi>. \<forall>e\<in>\<EE>. \<uu>\<^bsub>f\<^esub>e > 0
                 \<longrightarrow> \<cc> e + \<pi> (fstv e) - \<pi> (sndv e) \<ge> - \<epsilon>"
proof-
  obtain \<pi>
    where "\<forall>e\<in>\<EE>. \<uu>\<^bsub>f\<^esub>e > 0 \<longrightarrow> \<cc> e + \<pi> (fstv e) - \<pi> (sndv e) \<ge> 0"
    using is_Opt_imp_exact_complementary_slack[OF assms(1,2)]
    by blast
  thus ?thesis
    using assms(3)
    by (intro exI[of _ \<pi>]) fastforce
qed

text \<open>A computable a-posteriori bound. With
      \<open>c\<^sup>\<pi> e = c e + \<pi> (fst e) - \<pi> (snd e)\<close>, every \<open>b\<close>-flow
      \<open>g\<close> satisfies \<open>C g = (\<Sum>e. c\<^sup>\<pi> e * g e) - (\<Sum>v. \<pi> v * b v)\<close>.
      Since \<open>0 \<le> g e \<le> u e\<close>, the optimum \<open>C f\<^sup>*\<close> lies between \<open>L\<close>
      (\<open>min 0 c\<^sup>\<pi>\<close>) and \<open>U\<close> (\<open>max 0 c\<^sup>\<pi>\<close>). Hence the distance of
      \<open>C f\<close> to the farther end of \<open>[L, U]\<close>, divided by \<open>1\<close> plus the least
      absolute value \<open>M_min\<close> in \<open>[L, U]\<close>, bounds the relative error of \<open>f\<close>.\<close>

lemma cost_optimality_relative_bound:
  assumes "is_Opt b \<f>" "\<forall>e\<in>\<E>. \<u> e \<noteq> \<infinity>"
    "L = (\<Sum>e\<in>\<E>. min 0 (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * real_of_ereal (\<u> e))
         - (\<Sum>v\<in>\<V>. \<pi> v * b v)"
    "U = (\<Sum>e\<in>\<E>. max 0 (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * real_of_ereal (\<u> e))
         - (\<Sum>v\<in>\<V>. \<pi> v * b v)"
    "M_min = (if L \<le> 0 \<and> 0 \<le> U then 0 else if 0 < L then L else -U)"
    "max \<bar>\<C> f - L\<bar> \<bar>\<C> f - U\<bar> / (1 + M_min) < \<delta>"
  shows "\<bar>\<C> f - \<C> \<f>\<bar> / (1 + \<bar>\<C> \<f>\<bar>) < \<delta>"
proof-
  have "L \<le> \<C> \<f>" "\<C> \<f> \<le> U"
    using assms(1-4) flow_cost_ge_min_bound[of \<f> b \<pi>] flow_cost_le_max_bound[of \<f> b \<pi>]
    by (auto simp: is_Opt_def)
  hence "0 \<le> M_min" "M_min \<le> \<bar>\<C> \<f>\<bar>"
    "\<bar>\<C> f - \<C> \<f>\<bar> \<le> max \<bar>\<C> f - L\<bar> \<bar>\<C> f - U\<bar>"
    using assms(5)
    by (auto simp: abs_real_def max_def)
  hence "\<bar>\<C> f - \<C> \<f>\<bar> / (1 + \<bar>\<C> \<f>\<bar>)
         \<le> max \<bar>\<C> f - L\<bar> \<bar>\<C> f - U\<bar> / (1 + M_min)"
    by (auto intro!: frac_le)
  thus ?thesis
    using assms(6)
    by linarith
qed

end
end