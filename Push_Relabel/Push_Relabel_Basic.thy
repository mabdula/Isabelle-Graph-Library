theory Push_Relabel_Basic
  imports
    Flow_Theory.Unit_Flows
begin

section \<open>Preflows, Labellings, and the Basic Operations of Push-Relabel\<close>

text \<open>This is a port of the mathematical part of the push-relabel formalisation by Lammich and
      Sefidgar (AFP entry \<open>Prpu_Maxflow\<close>, theory \<open>Generic_Push_Relabel\<close>) to the multigraph
      flow library. Residual edges are the forward and backward copies @{term "F e"} and @{term "B e"}
      of the original edges. Parallel and antiparallel edges, self-loops, edges into the source and
      edges out of the target are all allowed.\<close>

subsection \<open>Setup\<close>

context flow_network_spec
begin

text \<open>A preflow respects the capacities, and no vertex except the source has more outflow than
      inflow.\<close>

definition "is_preflow s f = (isuflow f \<and> (\<forall> v \<in> \<V>. v \<noteq> s \<longrightarrow> ex f v \<ge> 0))"

lemma is_preflowI:
  "\<lbrakk>isuflow f; \<And> v. \<lbrakk>v \<in> \<V>; v \<noteq> s\<rbrakk> \<Longrightarrow> ex f v \<ge> 0\<rbrakk>
   \<Longrightarrow> is_preflow s f"
  by (auto simp: is_preflow_def)

lemma is_preflowE:
  "\<lbrakk>is_preflow s f;
    \<lbrakk>isuflow f; \<And> v. \<lbrakk>v \<in> \<V>; v \<noteq> s\<rbrakk> \<Longrightarrow> ex f v \<ge> 0\<rbrakk>
     \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by (auto simp: is_preflow_def)

text \<open>A valid labelling: the source is labelled with the number of vertices, the target with
      \<open>0\<close>, and no residual edge of positive capacity goes down by more than one.\<close>

definition "valid_labelling s t f (l::'a \<Rightarrow> nat) =
  (l s = card \<V> \<and> l t = 0 \<and>
   (\<forall> e \<in> \<EE>. rcap f e > 0 \<longrightarrow> l (fstv e) \<le> l (sndv e) + 1))"

lemma valid_labellingI:
  "\<lbrakk>l s = card \<V>; l t = 0;
    \<And> e. \<lbrakk>e \<in> \<EE>; rcap f e > 0\<rbrakk> \<Longrightarrow> l (fstv e) \<le> l (sndv e) + 1\<rbrakk>
   \<Longrightarrow> valid_labelling s t f l"
  by (auto simp: valid_labelling_def)

lemma valid_labellingE:
  "\<lbrakk>valid_labelling s t f l;
    \<lbrakk>l s = card \<V>; l t = 0;
     \<And> e. \<lbrakk>e \<in> \<EE>; rcap f e > 0\<rbrakk> \<Longrightarrow> l (fstv e) \<le> l (sndv e) + 1\<rbrakk>
      \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by (auto simp: valid_labelling_def)

definition "height_bounded l = (\<forall> v \<in> \<V>. l v \<le> 2 * card \<V> - 1)"

lemma height_boundedI:
  "(\<And> v. v \<in> \<V> \<Longrightarrow> l v \<le> 2 * card \<V> - 1) \<Longrightarrow> height_bounded l"
  by (auto simp: height_bounded_def)

lemma height_boundedD:
  "\<lbrakk>height_bounded l; v \<in> \<V>\<rbrakk> \<Longrightarrow> l v \<le> 2 * card \<V> - 1"
  by (auto simp: height_bounded_def)

definition "admissible f (l::'a \<Rightarrow> nat) e = (e \<in> \<EE> \<and> rcap f e > 0 \<and> l (fstv e) = l (sndv e) + 1)"

lemma admissibleI:
  "\<lbrakk>e \<in> \<EE>; rcap f e > 0; l (fstv e) = l (sndv e) + 1\<rbrakk> \<Longrightarrow> admissible f l e"
  by (auto simp: admissible_def)

lemma admissibleE:
  "\<lbrakk>admissible f l e;
    \<lbrakk>e \<in> \<EE>; rcap f e > 0; l (fstv e) = l (sndv e) + 1\<rbrakk> \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by (auto simp: admissible_def)

definition "active_vertex s t f v = (v \<in> \<V> \<and> v \<noteq> s \<and> v \<noteq> t \<and> ex f v > 0)"

lemma active_vertexI:
  "\<lbrakk>v \<in> \<V>; v \<noteq> s; v \<noteq> t; ex f v > 0\<rbrakk> \<Longrightarrow> active_vertex s t f v"
  by (auto simp: active_vertex_def)

lemma active_vertexE:
  "\<lbrakk>active_vertex s t f v;
    \<lbrakk>v \<in> \<V>; v \<noteq> s; v \<noteq> t; ex f v > 0\<rbrakk> \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by (auto simp: active_vertex_def)

text \<open>Pushing along a residual edge sends the minimum of the excess of its tail and its residual
      capacity.\<close>

definition "push_amount f e = min (ex f (fstv e)) (real_of_ereal (rcap f e))"

definition "push_effect f e = augment_edge f (push_amount f e) e"

definition "push_precond s t f l e = (active_vertex s t f (fstv e) \<and> admissible f l e)"

lemma push_precondI:
  "\<lbrakk>active_vertex s t f (fstv e); admissible f l e\<rbrakk> \<Longrightarrow> push_precond s t f l e"
  by (auto simp: push_precond_def)

lemma push_precondE:
  "\<lbrakk>push_precond s t f l e;
    \<lbrakk>active_vertex s t f (fstv e); admissible f l e\<rbrakk> \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by (auto simp: push_precond_def)

text \<open>An active vertex without admissible residual edges leaving it may be relabelled to one more
      than the least label of a residual neighbour.\<close>

definition "relabel_precond s t f l u =
  (active_vertex s t f u \<and> (\<forall> e \<in> \<EE>. fstv e = u \<longrightarrow> \<not> admissible f l e))"

lemma relabel_precondI:
  "\<lbrakk>active_vertex s t f u; \<And> e. \<lbrakk>e \<in> \<EE>; fstv e = u\<rbrakk>
   \<Longrightarrow> \<not> admissible f l e\<rbrakk>
   \<Longrightarrow> relabel_precond s t f l u"
  by (auto simp: relabel_precond_def)

lemma relabel_precondE:
  "\<lbrakk>relabel_precond s t f l u;
    \<lbrakk>active_vertex s t f u;
     \<And> e. \<lbrakk>e \<in> \<EE>; fstv e = u\<rbrakk> \<Longrightarrow> \<not> admissible f l e\<rbrakk>
     \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by (auto simp: relabel_precond_def)

definition "relabel_labels f (l::'a \<Rightarrow> nat) u =
  {l (sndv e) | e. e \<in> \<EE> \<and> fstv e = u \<and> rcap f e > 0}"

definition "relabel_effect f l u = l(u := Min (relabel_labels f l u) + 1)"

text \<open>Gap heuristic: if no vertex has label \<open>k\<close>, then no vertex with a label between \<open>k\<close>
      and the number of vertices can reach the target, and all these vertices may be lifted above the
      source. As in the AFP entry, a gap is only looked for right after a relabelling, at the old
      label of the relabelled vertex.\<close>

definition "gap_precond l k = (k < card \<V> \<and> (\<forall> v \<in> \<V>. l v \<noteq> k))"

lemma gap_precondI:
  "\<lbrakk>k < card \<V>; \<And> v. v \<in> \<V> \<Longrightarrow> l v \<noteq> k\<rbrakk>
   \<Longrightarrow> gap_precond l k"
  by (auto simp: gap_precond_def)

lemma gap_precondE:
  "\<lbrakk>gap_precond l k;
    \<lbrakk>k < card \<V>; \<And> v. v \<in> \<V> \<Longrightarrow> l v \<noteq> k\<rbrakk>
     \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by (auto simp: gap_precond_def)

definition "gap_effect l k =
  (\<lambda> v. if v \<in> \<V> \<and> k < l v \<and> l v < card \<V> then card \<V> + 1 else l v)"

definition "relabel_gap_effect f l u =
  (let l' = relabel_effect f l u in if gap_precond l' (l u) then gap_effect l' (l u) else l')"

text \<open>Initially, all edges leaving the source are saturated, the source is labelled with the
      number of vertices, and all other vertices with \<open>0\<close>.\<close>

definition "init_flow s e =
  (if e \<in> \<E> \<and> fst e = s \<and> snd e \<noteq> s then real_of_ereal (\<u> e) else 0)"

definition "init_labels s = (\<lambda> v. 0)(s := card \<V>)"

text \<open>Measures for termination.\<close>

definition "label_measure l = (\<Sum> v \<in> \<V>. 2 * card \<V> - l v)"

definition "admissible_count f l = card {e. admissible f l e}"

definition "active_potential s t f l = (\<Sum> v \<in> {v. active_vertex s t f v}. l v)"

end

locale push_relabel_network = flow_network +
  fixes s t
  assumes s_in_V: "s \<in> \<V>"
      and t_in_V: "t \<in> \<V>"
      and s_neq_t: "s \<noteq> t"
      and finite_capacities: "\<forall> e \<in> \<E>. \<u> e < PInfty"
begin

subsection \<open>Residual Edges\<close>

lemma fstv_in_V: "e \<in> \<EE> \<Longrightarrow> fstv e \<in> \<V>"
  and sndv_in_V: "e \<in> \<EE> \<Longrightarrow> sndv e \<in> \<V>"
  by (cases e; auto simp: \<EE>_def intro: fst_E_V snd_E_V)+

lemma rcap_finite:
  assumes "e \<in> \<EE>"
  obtains r where "rcap f e = ereal r"
  using assms o_edge_res[of e] finite_capacities u_non_neg[of "oedge e"]
  by (cases e; cases "\<u> (oedge e)") (auto intro: that)

lemma rcap_real: "e \<in> \<EE> \<Longrightarrow> rcap f e = ereal (real_of_ereal (rcap f e))"
  by (rule rcap_finite[of e f]) auto

lemma rcap_augment_edge_same:
  "rcap (augment_edge f \<gamma> e) e = rcap f e - ereal \<gamma>"
  by (cases e; cases "\<u> (oedge e)") (auto simp: algebra_simps)

lemma rcap_augment_edge_other:
  "\<lbrakk>d \<noteq> e; d \<noteq> erev e\<rbrakk> \<Longrightarrow> rcap (augment_edge f \<gamma> e) d = rcap f d"
  by (cases d; cases e) auto

lemma ex_augment_edge:
  assumes "e \<in> \<EE>"
  shows "ex (augment_edge f \<gamma> e) v =
         ex f v - (if v = fstv e then \<gamma> else 0) + (if v = sndv e then \<gamma> else 0)"
proof(cases e)
  case (F d)
  hence d: "d \<in> \<E>"
    using assms o_edge_res[of e] by simp
  show ?thesis
    using F augment_edge_away_from_node[of e v f \<gamma>] augment_loop_forward[OF fst_E_V[OF d] d refl]
          augment_edge_head_forward[OF fst_E_V[OF d] snd_E_V[OF d] d _ refl refl]
          augment_edge_tail_forward[OF fst_E_V[OF d] snd_E_V[OF d] d _ refl refl]
    by (cases "v = fst d"; cases "v = snd d") simp_all
next
  case (B d)
  hence d: "d \<in> \<E>"
    using assms o_edge_res[of e] by simp
  show ?thesis
    using B augment_edge_away_from_node[of e v f \<gamma>] augment_loop_backward[OF fst_E_V[OF d] d refl]
          augment_edge_head_backward[OF fst_E_V[OF d] snd_E_V[OF d] d _ refl refl]
          augment_edge_tail_backward[OF fst_E_V[OF d] snd_E_V[OF d] d _ refl refl]
    by (cases "v = fst d"; cases "v = snd d") simp_all
qed

subsection \<open>Labels along Residual Walks\<close>

abbreviation "res_graph f \<equiv> to_vertex_pair ` {e | e. e \<in> \<EE> \<and> rcap f e > 0}"

lemma label_vwalk_bound:
  "\<lbrakk>\<And> a b. (a, b) \<in> G \<Longrightarrow> l a \<le> l b + 1; vwalk_bet G u p v\<rbrakk>
   \<Longrightarrow> l u \<le> l v + (length p - 1)"
proof(induction p arbitrary: u)
  case (Cons x p)
  from Cons.prems(2) show ?case
  proof(rule vwalk_betE)
    fix p' y
    assume "x # p = u # y # p'" "(u, y) \<in> G" "vwalk_bet G y (y # p') v"
    thus ?thesis
      using Cons.IH[of y, OF Cons.prems(1)] Cons.prems(1)[of u y] by simp
  qed simp
qed simp

lemma res_graph_valid_labelling:
  "\<lbrakk>valid_labelling s t f l; (a, b) \<in> res_graph f\<rbrakk> \<Longrightarrow> l a \<le> l b + 1"
  by (auto simp: to_vertex_pair_fst_snd elim: valid_labellingE)

lemma res_graph_vertices: "dVs (res_graph f) \<subseteq> \<V>"
proof
  fix x
  assume "x \<in> dVs (res_graph f)"
  then obtain e where "e \<in> \<EE>" "x = fstv e \<or> x = sndv e"
    by (auto simp: dVs_def to_vertex_pair_fst_snd)
  thus "x \<in> \<V>"
    using fstv_in_V sndv_in_V by auto
qed

lemma resreach_short_vwalk:
  assumes "resreach f u v" "u \<noteq> v"
  obtains p where "vwalk_bet (res_graph f) u p v" "length p \<le> card \<V>"
proof-
  obtain q where "vwalk_bet (res_graph f) u q v"
    using assms resreach_iff_vwalk by blast
  hence "distinct_vwalk_bet (res_graph f) u (vwalk_bet_to_distinct (res_graph f) q) v"
    by (rule vwalk_bet_to_distinct_is_distinct_vwalk_bet)
  moreover have "card (dVs (res_graph f)) \<le> card \<V>"
    using res_graph_vertices \<V>_finite by (rule card_mono[rotated])
  ultimately show ?thesis
    using that distinct_vwalk_bet_length_le_card_vertices finite_\<EE>
    by (fastforce elim: distinct_vwalk_betE)
qed

lemma valid_labelling_resreach_bound:
  assumes "valid_labelling s t f l" "resreach f u v" "u \<noteq> v"
  shows "l u \<le> l v + (card \<V> - 1)"
proof-
  obtain p where "vwalk_bet (res_graph f) u p v" "length p \<le> card \<V>"
    using assms(2,3) by (rule resreach_short_vwalk)
  thus ?thesis
    using label_vwalk_bound[OF res_graph_valid_labelling[OF assms(1)]] by fastforce
qed

subsection \<open>Valid Labellings and Preflows\<close>

lemma valid_labelling_no_resreach: "valid_labelling s t f l \<Longrightarrow> \<not> resreach f s t"
  using valid_labelling_resreach_bound[of f l s t] s_neq_t cardV_0
  by (fastforce elim: valid_labellingE)

lemma active_resreach_source:
  "\<lbrakk>is_preflow s f; active_vertex s t f u\<rbrakk> \<Longrightarrow> resreach f u s"
  by (rule neg_balance_resreach[of f "\<lambda> v. - ex f v"])
     (auto intro: isbflowI elim!: active_vertexE is_preflowE)

lemma active_label_bound:
  "\<lbrakk>is_preflow s f; valid_labelling s t f l; active_vertex s t f u\<rbrakk>
   \<Longrightarrow> l u \<le> 2 * card \<V> - 1"
  using valid_labelling_resreach_bound[of f l u s] active_resreach_source cardV_0
  by (fastforce elim: valid_labellingE active_vertexE)

lemma active_residual_out_edge:
  assumes "is_preflow s f" "active_vertex s t f u"
  obtains e where "e \<in> \<EE>" "fstv e = u" "rcap f e > 0"
proof-
  have "u \<noteq> s"
    using assms(2) by (auto elim: active_vertexE)
  then obtain p where "vwalk_bet (res_graph f) u p s"
    using active_resreach_source[OF assms] resreach_iff_vwalk by blast
  hence "\<exists> y. (u, y) \<in> res_graph f"
  proof(rule vwalk_betE)
    fix p' x
    assume "(u, x) \<in> res_graph f"
    thus ?thesis
      by blast
  qed (use \<open>u \<noteq> s\<close> in simp)
  then obtain y e where "e \<in> \<EE>" "rcap f e > 0" "(u, y) = to_vertex_pair e"
    by blast
  thus ?thesis
    using that by (auto simp: to_vertex_pair_fst_snd)
qed

lemma card_V_ge_2: "card \<V> \<ge> 2"
  using card_mono[OF \<V>_finite, of "{s, t}"] s_in_V t_in_V s_neq_t by simp

text \<open>If no vertex is active any more, the preflow is a maximum flow: all vertices except the source
      and the target have excess \<open>0\<close>, and the excesses sum up to \<open>0\<close>.\<close>

lemma no_active_max_flow:
  assumes "is_preflow s f" "valid_labelling s t f l" "\<And> v. \<not> active_vertex s t f v"
  shows "is_max_flow s t f"
proof-
  have "isuflow f"
    using assms(1) by (auto elim: is_preflowE)
  moreover have "(\<Sum> v \<in> \<V> - {s}. ex f v) \<ge> 0"
    using assms(1) by (intro sum_nonneg) (auto elim: is_preflowE)
  ultimately have "ex f s \<le> 0"
    using uflow_zero_total_excess sum.remove[OF \<V>_finite s_in_V, of "ex f"] by fastforce
  hence "f is s -- t flow"
    using assms(1,3) s_in_V t_in_V s_neq_t \<open>isuflow f\<close>
    by (intro is_s_t_flowI) (force simp: is_preflow_def active_vertex_def)+
  thus ?thesis
    using no_max_flow_resreach[OF s_in_V t_in_V s_neq_t] valid_labelling_no_resreach[OF assms(2)]
    by blast
qed

subsection \<open>Initialisation\<close>

lemma init_flow_nonneg: "init_flow s e \<ge> 0"
  using u_non_neg[of e] by (auto simp: init_flow_def real_of_ereal_pos)

lemma init_flow_isuflow: "isuflow (init_flow s)"
proof(rule isuflowI)
  fix e
  assume "e \<in> \<E>"
  thus "ereal (init_flow s e) \<le> \<u> e"
    using u_non_neg[of e] finite_capacities by (cases "\<u> e") (auto simp: init_flow_def)
qed (rule init_flow_nonneg)

lemma init_flow_preflow: "is_preflow s (init_flow s)"
proof(rule is_preflowI[OF init_flow_isuflow])
  fix v
  assume "v \<in> \<V>" "v \<noteq> s"
  hence "(\<Sum> e \<in> \<delta>\<^sup>+ v. init_flow s e) = 0"
    by (intro sum.neutral) (auto simp: delta_plus_def init_flow_def)
  thus "ex (init_flow s) v \<ge> 0"
    by (simp add: ex_def sum_nonneg init_flow_nonneg)
qed

lemma init_labels_valid: "valid_labelling s t (init_flow s) (init_labels s)"
proof(rule valid_labellingI)
  fix e
  assume "e \<in> \<EE>" "rcap (init_flow s) e > 0"
  thus "init_labels s (fstv e) \<le> init_labels s (sndv e) + 1"
    using o_edge_res[of e] finite_capacities u_non_neg[of "oedge e"]
    by (cases e; cases "\<u> (oedge e)") (auto simp: init_flow_def init_labels_def split: if_splits)
qed (use s_neq_t in \<open>auto simp: init_labels_def\<close>)

lemma init_labels_height_bounded: "height_bounded (init_labels s)"
  using cardV_0 by (auto intro!: height_boundedI simp: init_labels_def)

lemma init_not_admissible: "\<not> admissible (init_flow s) (init_labels s) e"
  using card_V_ge_2 by (auto simp: init_labels_def elim!: admissibleE split: if_splits)

text \<open>Increasing labels does not make residual edges admissible whose tail keeps its label.\<close>

lemma admissible_increased_labels:
  "\<lbrakk>valid_labelling s t f l; \<And> x. x \<in> \<V> \<Longrightarrow> l x \<le> l' x; l' (fstv e) = l (fstv e);
    admissible f l' e\<rbrakk>
   \<Longrightarrow> admissible f l e"
  by (fastforce elim!: admissibleE valid_labellingE intro: admissibleI dest: sndv_in_V)

subsection \<open>Push\<close>

lemma push_amount_props:
  assumes "push_precond s t f l e"
  shows "push_amount f e > 0" "ereal (push_amount f e) \<le> rcap f e"
        "push_amount f e \<le> ex f (fstv e)"
proof-
  have "e \<in> \<EE>" "rcap f e > 0" "ex f (fstv e) > 0"
    using assms by (auto elim!: push_precondE admissibleE active_vertexE)
  moreover then obtain r where "rcap f e = ereal r"
    by (elim rcap_finite)
  ultimately show "push_amount f e > 0" "ereal (push_amount f e) \<le> rcap f e"
                  "push_amount f e \<le> ex f (fstv e)"
    by (auto simp: push_amount_def)
qed

lemma push_fstv_sndv:
  assumes "push_precond s t f l e"
  shows "fstv e \<noteq> sndv e" "e \<in> \<EE>" "l (fstv e) = l (sndv e) + 1"
  using assms by (auto elim!: push_precondE admissibleE)

lemma ex_push:
  assumes "push_precond s t f l e"
  shows "ex (push_effect f e) v =
         (if v = fstv e then ex f v - push_amount f e else if v = sndv e then ex f v + push_amount f e else ex f v)"
  unfolding push_effect_def ex_augment_edge[OF push_fstv_sndv(2)[OF assms]]
  using push_fstv_sndv(1)[OF assms] by auto

lemma push_preserves_preflow:
  assumes "is_preflow s f" "push_precond s t f l e"
  shows "is_preflow s (push_effect f e)"
proof(rule is_preflowI)
  show "isuflow (push_effect f e)"
    unfolding push_effect_def
    using assms push_amount_props[OF assms(2)]
    by (intro augment_edge_validness_pres) (auto elim: is_preflowE)
qed (use assms push_amount_props[OF assms(2)] in \<open>auto simp: ex_push elim!: is_preflowE\<close>)

lemma push_rcap_pos:
  "\<lbrakk>push_precond s t f l e; rcap (push_effect f e) d > 0\<rbrakk>
   \<Longrightarrow> rcap f d > 0 \<or> d = erev e"
  by (cases "d = e")
     (auto simp: push_effect_def rcap_augment_edge_other simp del: augment_edge.simps
           elim!: push_precondE admissibleE)

lemma push_preserves_valid:
  "\<lbrakk>valid_labelling s t f l; push_precond s t f l e\<rbrakk>
   \<Longrightarrow> valid_labelling s t (push_effect f e) l"
  using push_fstv_sndv[of f l e] push_rcap_pos[of f l e]
  by (fastforce simp: vs_erev elim!: valid_labellingE intro!: valid_labellingI)

lemma push_saturating_rcap:
  "\<lbrakk>push_precond s t f l e; real_of_ereal (rcap f e) \<le> ex f (fstv e)\<rbrakk>
   \<Longrightarrow> rcap (push_effect f e) e = 0"
  using push_fstv_sndv(2)[of f l e]
  by (rule rcap_finite[of e f])
     (auto simp: push_effect_def rcap_augment_edge_same push_amount_def simp del: augment_edge.simps)

lemma push_nonsaturating_ex:
  "\<lbrakk>push_precond s t f l e; ex f (fstv e) < real_of_ereal (rcap f e)\<rbrakk>
   \<Longrightarrow> ex (push_effect f e) (fstv e) = 0"
  by (simp add: ex_push push_amount_def)

lemma push_nonsaturating_rcap:
  "\<lbrakk>push_precond s t f l e; ex f (fstv e) < real_of_ereal (rcap f e)\<rbrakk>
   \<Longrightarrow> rcap (push_effect f e) e > 0"
  using push_fstv_sndv(2)[of f l e]
  by (rule rcap_finite[of e f])
     (auto simp: push_effect_def rcap_augment_edge_same push_amount_def simp del: augment_edge.simps)

lemma push_admissible:
  "\<lbrakk>push_precond s t f l e; admissible (push_effect f e) l d\<rbrakk> \<Longrightarrow> admissible f l d"
  using push_fstv_sndv[of f l e] push_rcap_pos[of f l e d]
  by (auto simp: vs_erev elim!: admissibleE intro!: admissibleI)

lemma push_active:
  "\<lbrakk>push_precond s t f l e; active_vertex s t (push_effect f e) v\<rbrakk>
   \<Longrightarrow> v = sndv e \<or> active_vertex s t f v"
  using push_amount_props(1)[of f l e]
  by (auto simp: ex_push elim!: active_vertexE intro!: active_vertexI split: if_splits)

subsection \<open>Relabel\<close>

lemma relabel_labels_finite: "finite (relabel_labels f l u)"
  using finite_\<EE> by (auto simp: relabel_labels_def)

lemma relabel_labels_nonempty:
  "\<lbrakk>is_preflow s f; active_vertex s t f u\<rbrakk> \<Longrightarrow> relabel_labels f l u \<noteq> {}"
  by (auto simp: relabel_labels_def elim: active_residual_out_edge)

lemma relabel_labels_ge:
  "\<lbrakk>valid_labelling s t f l; relabel_precond s t f l u; x \<in> relabel_labels f l u\<rbrakk>
   \<Longrightarrow> l u \<le> x"
  by (fastforce simp: relabel_labels_def elim!: valid_labellingE relabel_precondE intro: admissibleI)

lemma relabel_increases:
  "\<lbrakk>is_preflow s f; valid_labelling s t f l; relabel_precond s t f l u\<rbrakk>
   \<Longrightarrow> l u < relabel_effect f l u u"
  using relabel_labels_nonempty[of f u l] relabel_labels_ge[of f l u] relabel_labels_finite[of f l u]
  by (auto simp: relabel_effect_def less_Suc_eq_le elim: relabel_precondE)

lemma relabel_mono:
  "\<lbrakk>is_preflow s f; valid_labelling s t f l; relabel_precond s t f l u\<rbrakk>
   \<Longrightarrow> l v \<le> relabel_effect f l u v"
  using relabel_increases[of f l u] by (cases "v = u") (auto simp: relabel_effect_def)

lemma relabel_preserves_valid:
  assumes "is_preflow s f" "valid_labelling s t f l" "relabel_precond s t f l u"
  shows "valid_labelling s t f (relabel_effect f l u)"
proof(rule valid_labellingI)
  fix d
  assume "d \<in> \<EE>" "rcap f d > 0"
  moreover hence "fstv d = u \<Longrightarrow> Min (relabel_labels f l u) \<le> l (sndv d)"
    by (intro Min_le[OF relabel_labels_finite]) (auto simp: relabel_labels_def)
  ultimately show "relabel_effect f l u (fstv d) \<le> relabel_effect f l u (sndv d) + 1"
    using relabel_mono[OF assms, of "sndv d"] assms(2)
    by (fastforce simp: relabel_effect_def elim: valid_labellingE)
qed (use assms(2,3) in \<open>auto simp: relabel_effect_def elim: valid_labellingE relabel_precondE
                                 active_vertexE\<close>)

lemma relabel_preserves_height_bounded:
  assumes "is_preflow s f" "valid_labelling s t f l" "relabel_precond s t f l u" "height_bounded l"
  shows "height_bounded (relabel_effect f l u)"
  using active_label_bound[OF assms(1) relabel_preserves_valid[OF assms(1-3)], of u]
        height_boundedD[OF assms(4)] assms(3)
  by (auto intro!: height_boundedI simp: relabel_effect_def elim: relabel_precondE)

subsection \<open>Gap Relabelling\<close>

lemma gap_mono: "l v \<le> gap_effect l k v"
  by (auto simp: gap_effect_def)

lemma gap_preserves_valid:
  assumes "valid_labelling s t f l" "gap_precond l k"
  shows "valid_labelling s t f (gap_effect l k)"
proof(rule valid_labellingI)
  fix d
  assume "d \<in> \<EE>" "rcap f d > 0"
  thus "gap_effect l k (fstv d) \<le> gap_effect l k (sndv d) + 1"
    using assms fstv_in_V sndv_in_V gap_mono[of l "sndv d" k]
    by (fastforce simp: gap_effect_def elim!: valid_labellingE gap_precondE)
qed (use assms(1) in \<open>auto simp: gap_effect_def elim: valid_labellingE\<close>)

lemma gap_preserves_height_bounded: "height_bounded l \<Longrightarrow> height_bounded (gap_effect l k)"
  using card_V_ge_2 by (auto simp: gap_effect_def height_bounded_def)

lemma relabel_gap_mono:
  "\<lbrakk>is_preflow s f; valid_labelling s t f l; relabel_precond s t f l u\<rbrakk>
   \<Longrightarrow> l v \<le> relabel_gap_effect f l u v"
  using relabel_mono[of f l u v] gap_mono[of "relabel_effect f l u" v "l u"]
  by (auto simp: relabel_gap_effect_def Let_def)

lemma relabel_gap_increases:
  "\<lbrakk>is_preflow s f; valid_labelling s t f l; relabel_precond s t f l u\<rbrakk>
   \<Longrightarrow> l u < relabel_gap_effect f l u u"
  using relabel_increases[of f l u] gap_mono[of "relabel_effect f l u" u "l u"]
  by (auto simp: relabel_gap_effect_def Let_def)

lemma relabel_gap_preserves_valid:
  "\<lbrakk>is_preflow s f; valid_labelling s t f l; relabel_precond s t f l u\<rbrakk>
   \<Longrightarrow> valid_labelling s t f (relabel_gap_effect f l u)"
  using relabel_preserves_valid[of f l u] gap_preserves_valid
  by (auto simp: relabel_gap_effect_def Let_def)

lemma relabel_gap_preserves_height_bounded:
  "\<lbrakk>is_preflow s f; valid_labelling s t f l; relabel_precond s t f l u; height_bounded l\<rbrakk>
   \<Longrightarrow> height_bounded (relabel_gap_effect f l u)"
  using relabel_preserves_height_bounded[of f l u] gap_preserves_height_bounded
  by (auto simp: relabel_gap_effect_def Let_def)

subsection \<open>Termination Measures\<close>

lemma label_measure_decrease:
  assumes "\<And> v. v \<in> \<V> \<Longrightarrow> l v \<le> l' v" "height_bounded l'" "v \<in> \<V>" "l v < l' v"
  shows "label_measure l' < label_measure l"
  unfolding label_measure_def
  using assms height_boundedD[OF assms(2,3)] cardV_0
  by (intro sum_strict_mono_ex1[OF \<V>_finite]) (auto intro!: bexI[of _ v] diff_le_mono2)

lemma relabel_label_measure:
  "\<lbrakk>is_preflow s f; valid_labelling s t f l; relabel_precond s t f l u; height_bounded l\<rbrakk>
   \<Longrightarrow> label_measure (relabel_effect f l u) < label_measure l"
  using relabel_mono[of f l u] relabel_preserves_height_bounded[of f l u] relabel_increases[of f l u]
  by (intro label_measure_decrease[of _ _ u]) (auto elim: relabel_precondE active_vertexE)

lemma relabel_gap_label_measure:
  "\<lbrakk>is_preflow s f; valid_labelling s t f l; relabel_precond s t f l u; height_bounded l\<rbrakk>
   \<Longrightarrow> label_measure (relabel_gap_effect f l u) < label_measure l"
  using relabel_gap_mono[of f l u] relabel_gap_preserves_height_bounded[of f l u]
        relabel_gap_increases[of f l u]
  by (intro label_measure_decrease[of _ _ u]) (auto elim: relabel_precondE active_vertexE)

lemma admissible_finite: "finite {e. admissible f l e}"
  using finite_\<EE> by (rule finite_subset[rotated]) (auto elim: admissibleE)

lemma push_admissible_count_mono:
  "push_precond s t f l e \<Longrightarrow> admissible_count (push_effect f e) l \<le> admissible_count f l"
  unfolding admissible_count_def
  using push_admissible admissible_finite by (intro card_mono) auto

lemma push_saturating_admissible_count:
  assumes "push_precond s t f l e" "real_of_ereal (rcap f e) \<le> ex f (fstv e)"
  shows "admissible_count (push_effect f e) l < admissible_count f l"
proof-
  have "{d. admissible (push_effect f e) l d} \<subseteq> {d. admissible f l d} - {e}"
    using push_admissible[OF assms(1)] push_saturating_rcap[OF assms] by (auto elim: admissibleE)
  moreover have "e \<in> {d. admissible f l d}"
    using assms(1) by (auto elim: push_precondE)
  ultimately show ?thesis
    unfolding admissible_count_def
    using admissible_finite[of f l]
    by (intro le_less_trans[OF card_mono card_Diff1_less]) auto
qed

lemma active_finite: "finite {v. active_vertex s t f v}"
  using \<V>_finite by (rule finite_subset[rotated]) (auto elim: active_vertexE)

text \<open>A non-saturating push deactivates the tail and may activate the head, whose label is one
      less.\<close>

lemma push_nonsaturating_active_potential:
  assumes "push_precond s t f l e" "ex f (fstv e) < real_of_ereal (rcap f e)"
  shows "active_potential s t (push_effect f e) l < active_potential s t f l"
proof-
  let ?A = "{w. active_vertex s t f w}"
  have "{w. active_vertex s t (push_effect f e) w} \<subseteq> insert (sndv e) (?A - {fstv e})"
    using push_nonsaturating_ex[OF assms] push_active[OF assms(1)] by (auto elim: active_vertexE)
  hence "active_potential s t (push_effect f e) l \<le> sum l (insert (sndv e) (?A - {fstv e}))"
    unfolding active_potential_def using active_finite by (intro sum_mono2) auto
  also have "\<dots> < l (fstv e) + sum l (?A - {fstv e})"
    using push_fstv_sndv(3)[OF assms(1)] active_finite by (simp add: sum.insert_if)
  also have "\<dots> = active_potential s t f l"
    using sum.remove[OF active_finite[of f], of "fstv e" l] assms(1)
    by (auto simp: active_potential_def elim: push_precondE)
  finally show ?thesis .
qed

end

end
