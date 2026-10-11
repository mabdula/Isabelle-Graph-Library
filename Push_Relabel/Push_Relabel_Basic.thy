theory Push_Relabel_Basic
  imports
    Flow_Theory.Unit_Flows
begin

section \<open>Preflows, Labellings, and the Basic Operations of Push-Relabel\<close>

text \<open>This is a port of the mathematical part of the push-relabel formalisation by Lammich and
      Sefidgar (AFP entry \<open>Prpu_Maxflow\<close>, theory \<open>Generic_Push_Relabel\<close>) to the multigraph flow
      library. Residual edges are the forward and backward copies @{term "F e"} and @{term "B e"}
      of the original edges. Parallel and antiparallel edges, self-loops, edges into the source and
      edges out of the target are all allowed.\<close>

subsection \<open>Setup\<close>

context flow_network_spec
begin

text \<open>A preflow respects the capacities, and no vertex except the source has more outflow than
      inflow.\<close>

definition "is_preflow s f = (isuflow f \<and> (\<forall> v \<in> \<V>. v \<noteq> s \<longrightarrow> ex f v \<ge> 0))"

lemma is_preflowI:
  "\<lbrakk>isuflow f; \<And> v. \<lbrakk>v \<in> \<V>; v \<noteq> s\<rbrakk> \<Longrightarrow> ex f v \<ge> 0\<rbrakk> \<Longrightarrow> is_preflow s f"
  by (auto simp add: is_preflow_def)

lemma is_preflowE:
  "\<lbrakk>is_preflow s f; \<lbrakk>isuflow f; \<And> v. \<lbrakk>v \<in> \<V>; v \<noteq> s\<rbrakk> \<Longrightarrow> ex f v \<ge> 0\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp add: is_preflow_def)

text \<open>A valid labelling: the source is labelled with the number of vertices, the target with
      \<open>0\<close>, and no residual edge of positive capacity goes down by more than one.\<close>

definition "valid_labelling s t f (l::'a \<Rightarrow> nat) =
  (l s = card \<V> \<and> l t = 0 \<and>
   (\<forall> e \<in> \<EE>. rcap f e > 0 \<longrightarrow> l (fstv e) \<le> l (sndv e) + 1))"

lemma valid_labellingI:
  "\<lbrakk>l s = card \<V>; l t = 0;
    \<And> e. \<lbrakk>e \<in> \<EE>; rcap f e > 0\<rbrakk> \<Longrightarrow> l (fstv e) \<le> l (sndv e) + 1\<rbrakk>
   \<Longrightarrow> valid_labelling s t f l"
  by (auto simp add: valid_labelling_def)

lemma valid_labellingE:
  "\<lbrakk>valid_labelling s t f l;
    \<lbrakk>l s = card \<V>; l t = 0;
     \<And> e. \<lbrakk>e \<in> \<EE>; rcap f e > 0\<rbrakk> \<Longrightarrow> l (fstv e) \<le> l (sndv e) + 1\<rbrakk> \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by (auto simp add: valid_labelling_def)

definition "height_bounded l = (\<forall> v \<in> \<V>. l v \<le> 2 * card \<V> - 1)"

lemma height_boundedI:
  "(\<And> v. v \<in> \<V> \<Longrightarrow> l v \<le> 2 * card \<V> - 1) \<Longrightarrow> height_bounded l"
  by (auto simp add: height_bounded_def)

lemma height_boundedD:
  "\<lbrakk>height_bounded l; v \<in> \<V>\<rbrakk> \<Longrightarrow> l v \<le> 2 * card \<V> - 1"
  by (auto simp add: height_bounded_def)

definition "admissible f (l::'a \<Rightarrow> nat) e = (e \<in> \<EE> \<and> rcap f e > 0 \<and> l (fstv e) = l (sndv e) + 1)"

lemma admissibleI:
  "\<lbrakk>e \<in> \<EE>; rcap f e > 0; l (fstv e) = l (sndv e) + 1\<rbrakk> \<Longrightarrow> admissible f l e"
  by (auto simp add: admissible_def)

lemma admissibleE:
  "\<lbrakk>admissible f l e; \<lbrakk>e \<in> \<EE>; rcap f e > 0; l (fstv e) = l (sndv e) + 1\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp add: admissible_def)

definition "active_vertex s t f v = (v \<in> \<V> \<and> v \<noteq> s \<and> v \<noteq> t \<and> ex f v > 0)"

lemma active_vertexI:
  "\<lbrakk>v \<in> \<V>; v \<noteq> s; v \<noteq> t; ex f v > 0\<rbrakk> \<Longrightarrow> active_vertex s t f v"
  by (auto simp add: active_vertex_def)

lemma active_vertexE:
  "\<lbrakk>active_vertex s t f v; \<lbrakk>v \<in> \<V>; v \<noteq> s; v \<noteq> t; ex f v > 0\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp add: active_vertex_def)

text \<open>Pushing along a residual edge sends the minimum of the excess of its tail and its residual
      capacity.\<close>

definition "push_amount f e = min (ex f (fstv e)) (real_of_ereal (rcap f e))"

definition "push_effect f e = augment_edge f (push_amount f e) e"

definition "push_precond s t f l e = (active_vertex s t f (fstv e) \<and> admissible f l e)"

lemma push_precondI:
  "\<lbrakk>active_vertex s t f (fstv e); admissible f l e\<rbrakk> \<Longrightarrow> push_precond s t f l e"
  by (auto simp add: push_precond_def)

lemma push_precondE:
  "\<lbrakk>push_precond s t f l e; \<lbrakk>active_vertex s t f (fstv e); admissible f l e\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp add: push_precond_def)

text \<open>An active vertex without admissible residual edges leaving it may be relabelled to one more
      than the least label of a residual neighbour.\<close>

definition "relabel_precond s t f l u =
  (active_vertex s t f u \<and> (\<forall> e \<in> \<EE>. fstv e = u \<longrightarrow> \<not> admissible f l e))"

lemma relabel_precondI:
  "\<lbrakk>active_vertex s t f u; \<And> e. \<lbrakk>e \<in> \<EE>; fstv e = u\<rbrakk> \<Longrightarrow> \<not> admissible f l e\<rbrakk>
   \<Longrightarrow> relabel_precond s t f l u"
  by (auto simp add: relabel_precond_def)

lemma relabel_precondE:
  "\<lbrakk>relabel_precond s t f l u;
    \<lbrakk>active_vertex s t f u; \<And> e. \<lbrakk>e \<in> \<EE>; fstv e = u\<rbrakk> \<Longrightarrow> \<not> admissible f l e\<rbrakk> \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by (auto simp add: relabel_precond_def)

definition "relabel_labels f (l::'a \<Rightarrow> nat) u =
  {l (sndv e) | e. e \<in> \<EE> \<and> fstv e = u \<and> rcap f e > 0}"

definition "relabel_effect f l u = l(u := Min (relabel_labels f l u) + 1)"

text \<open>Gap heuristic: if no vertex has label \<open>k\<close>, then no vertex with a label between \<open>k\<close> and
      the number of vertices can reach the target, and all these vertices may be lifted above the
      source. As in the AFP entry, a gap is only looked for right after a relabelling, at the old
      label of the relabelled vertex.\<close>

definition "gap_precond l k = (k < card \<V> \<and> (\<forall> v \<in> \<V>. l v \<noteq> k))"

lemma gap_precondI:
  "\<lbrakk>k < card \<V>; \<And> v. v \<in> \<V> \<Longrightarrow> l v \<noteq> k\<rbrakk> \<Longrightarrow> gap_precond l k"
  by (auto simp add: gap_precond_def)

lemma gap_precondE:
  "\<lbrakk>gap_precond l k; \<lbrakk>k < card \<V>; \<And> v. v \<in> \<V> \<Longrightarrow> l v \<noteq> k\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp add: gap_precond_def)

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

context flow_network
begin

context
  fixes s t :: 'a
  assumes s_in_V: "s \<in> \<V>"
      and t_in_V: "t \<in> \<V>"
      and s_neq_t: "s \<noteq> t"
      and finite_capacities: "\<forall> e \<in> \<E>. \<u> e < PInfty"
begin

subsection \<open>Residual Edges\<close>

lemma fstv_in_V: "e \<in> \<EE> \<Longrightarrow> fstv e \<in> \<V>"
  and sndv_in_V: "e \<in> \<EE> \<Longrightarrow> sndv e \<in> \<V>"
  by (cases e; auto simp add: \<EE>_def intro: fst_E_V snd_E_V)+

lemma rcap_finite:
  assumes "e \<in> \<EE>"
  obtains r where "rcap f e = ereal r"
proof(cases e)
  case (F d)
  hence "d \<in> \<E>"
    using assms o_edge_res[of e] by simp
  hence "\<u> d < PInfty" "\<u> d \<ge> 0"
    using finite_capacities u_non_neg by auto
  then obtain c where "\<u> d = ereal c"
    by (cases "\<u> d") auto
  thus ?thesis
    using F that[of "c - f d"] by simp
next
  case (B d)
  thus ?thesis
    using that[of "f d"] by simp
qed

lemma rcap_real: "e \<in> \<EE> \<Longrightarrow> rcap f e = ereal (real_of_ereal (rcap f e))"
  by (rule rcap_finite[of e f]) auto

lemma rcap_augment_edge_same:
  "rcap (augment_edge f \<gamma> e) e = rcap f e - ereal \<gamma>"
  by (cases e; cases "\<u> (oedge e)") (auto simp add: algebra_simps)

lemma rcap_augment_edge_other:
  assumes "d \<noteq> e" "d \<noteq> erev e"
  shows "rcap (augment_edge f \<gamma> e) d = rcap f d"
proof-
  have "erev d \<noteq> e"
    using assms(2) erve_erve_id[of d] by metis
  thus ?thesis
    using e_not_in_p_aug[of d "[e]" f \<gamma>] assms(1) by simp
qed

lemma ex_augment_edge:
  assumes "e \<in> \<EE>"
  shows "ex (augment_edge f \<gamma> e) v =
         ex f v - (if v = fstv e then \<gamma> else 0) + (if v = sndv e then \<gamma> else 0)"
proof(cases e)
  case (F d)
  hence d: "d \<in> \<E>"
    using assms o_edge_res[of e] by simp
  consider "v \<noteq> fst d" "v \<noteq> snd d" | "v = fst d" "fst d = snd d"
         | "v = fst d" "fst d \<noteq> snd d" | "v = snd d" "fst d \<noteq> snd d"
    by auto
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
      using augment_edge_away_from_node[of e v f \<gamma>] F by simp
  next
    case 2
    then show ?thesis
      using augment_loop_forward[OF fst_E_V[OF d] d] F by simp
  next
    case 3
    then show ?thesis
      using augment_edge_head_forward[OF fst_E_V[OF d] snd_E_V[OF d] d] F by simp
  next
    case 4
    then show ?thesis
      using augment_edge_tail_forward[OF fst_E_V[OF d] snd_E_V[OF d] d] F by simp
  qed
next
  case (B d)
  hence d: "d \<in> \<E>"
    using assms o_edge_res[of e] by simp
  consider "v \<noteq> fst d" "v \<noteq> snd d" | "v = fst d" "fst d = snd d"
         | "v = fst d" "fst d \<noteq> snd d" | "v = snd d" "fst d \<noteq> snd d"
    by auto
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
      using augment_edge_away_from_node[of e v f \<gamma>] B by simp
  next
    case 2
    then show ?thesis
      using augment_loop_backward[OF fst_E_V[OF d] d] B by simp
  next
    case 3
    then show ?thesis
      using augment_edge_head_backward[OF fst_E_V[OF d] snd_E_V[OF d] d] B by simp
  next
    case 4
    then show ?thesis
      using augment_edge_tail_backward[OF fst_E_V[OF d] snd_E_V[OF d] d] B by simp
  qed
qed

subsection \<open>Labels along Residual Walks\<close>

abbreviation "res_graph f \<equiv> to_vertex_pair ` {e | e. e \<in> \<EE> \<and> rcap f e > 0}"

lemma label_vwalk_bound:
  assumes "\<And> a b. (a, b) \<in> G \<Longrightarrow> l a \<le> l b + 1" "vwalk_bet G u p v"
  shows "l u \<le> l v + (length p - 1)"
  using assms(2)
proof(induction p arbitrary: u)
  case Nil
  then show ?case by simp
next
  case (Cons x p)
  from Cons.prems show ?case
  proof(rule vwalk_betE)
    assume "v \<in> dVs G" "u = v"
    thus ?thesis by simp
  next
    fix p' y
    assume asm: "x # p = u # y # p'" "(u, y) \<in> G" "vwalk_bet G y (y # p') v"
    hence "l y \<le> l v + (length p - 1)"
      using Cons.IH[of y] by simp
    moreover have "l u \<le> l y + 1"
      using assms(1) asm(2) by blast
    ultimately show ?thesis
      using asm(1) by simp
  qed
qed

lemma res_graph_valid_labelling:
  assumes "valid_labelling s t f l" "(a, b) \<in> res_graph f"
  shows "l a \<le> l b + 1"
proof-
  obtain e where e: "e \<in> \<EE>" "rcap f e > 0" "(a, b) = to_vertex_pair e"
    using assms(2) by blast
  hence "a = fstv e" "b = sndv e"
    by (auto simp add: to_vertex_pair_fst_snd)
  thus ?thesis
    using assms(1) e(1,2) by (auto elim: valid_labellingE)
qed

lemma res_graph_vertices: "dVs (res_graph f) \<subseteq> \<V>"
proof
  fix x
  assume "x \<in> dVs (res_graph f)"
  then obtain e where "e \<in> \<EE>" "x = fstv e \<or> x = sndv e"
    by (auto simp add: dVs_def to_vertex_pair_fst_snd)
  thus "x \<in> \<V>"
    using fstv_in_V sndv_in_V by auto
qed

lemma res_graph_finite: "finite (res_graph f)"
  using finite_\<EE> by simp

lemma resreach_short_vwalk:
  assumes "resreach f u v" "u \<noteq> v"
  obtains p where "vwalk_bet (res_graph f) u p v" "length p \<le> card \<V>"
proof-
  obtain q where "vwalk_bet (res_graph f) u q v"
    using assms resreach_iff_vwalk by blast
  hence dist: "distinct_vwalk_bet (res_graph f) u (vwalk_bet_to_distinct (res_graph f) q) v"
    by (rule vwalk_bet_to_distinct_is_distinct_vwalk_bet)
  have "length (vwalk_bet_to_distinct (res_graph f) q) \<le> card (dVs (res_graph f))"
    using distinct_vwalk_bet_length_le_card_vertices[OF dist res_graph_finite] .
  also have "\<dots> \<le> card \<V>"
    using res_graph_vertices \<V>_finite by (rule card_mono[rotated])
  finally show ?thesis
    using that dist by (auto elim: distinct_vwalk_betE)
qed

lemma valid_labelling_resreach_bound:
  assumes "valid_labelling s t f l" "resreach f u v" "u \<noteq> v"
  shows "l u \<le> l v + (card \<V> - 1)"
proof-
  obtain p where p: "vwalk_bet (res_graph f) u p v" "length p \<le> card \<V>"
    using assms(2,3) by (rule resreach_short_vwalk)
  have "l u \<le> l v + (length p - 1)"
    using res_graph_valid_labelling[OF assms(1)] p(1) by (rule label_vwalk_bound)
  thus ?thesis
    using p(2) by simp
qed

subsection \<open>Valid Labellings and Preflows\<close>

lemma valid_labelling_no_resreach:
  assumes "valid_labelling s t f l"
  shows "\<not> resreach f s t"
proof
  assume "resreach f s t"
  hence "l s \<le> l t + (card \<V> - 1)"
    using assms s_neq_t by (intro valid_labelling_resreach_bound)
  thus False
    using assms cardV_0 by (auto elim: valid_labellingE)
qed

lemma active_resreach_source:
  assumes "is_preflow s f" "active_vertex s t f u"
  shows "resreach f u s"
proof-
  have flow: "f is (\<lambda> v. - ex f v) flow"
    using assms(1) by (auto intro: isbflowI elim: is_preflowE)
  show ?thesis
    using assms
    by (intro neg_balance_resreach[OF flow])
       (auto elim!: active_vertexE is_preflowE)
qed

lemma active_label_bound:
  assumes "is_preflow s f" "valid_labelling s t f l" "active_vertex s t f u"
  shows "l u \<le> 2 * card \<V> - 1"
proof-
  have "u \<noteq> s"
    using assms(3) by (auto elim: active_vertexE)
  hence "l u \<le> l s + (card \<V> - 1)"
    using assms active_resreach_source by (intro valid_labelling_resreach_bound) auto
  thus ?thesis
    using assms(2) cardV_0 by (auto elim: valid_labellingE)
qed

lemma active_residual_out_edge:
  assumes "is_preflow s f" "active_vertex s t f u"
  obtains e where "e \<in> \<EE>" "fstv e = u" "rcap f e > 0"
proof-
  have "u \<noteq> s"
    using assms(2) by (auto elim: active_vertexE)
  then obtain p where p: "vwalk_bet (res_graph f) u p s"
    using active_resreach_source[OF assms] resreach_iff_vwalk by blast
  have "\<exists> y. (u, y) \<in> res_graph f"
    using p
  proof(rule vwalk_betE)
    assume "s \<in> dVs (res_graph f)" "u = s"
    thus ?thesis using \<open>u \<noteq> s\<close> by simp
  next
    fix p' x
    assume "(u, x) \<in> res_graph f"
    thus ?thesis by blast
  qed
  then obtain y e where "e \<in> \<EE>" "rcap f e > 0" "(u, y) = to_vertex_pair e"
    by blast
  thus ?thesis
    using that by (auto simp add: to_vertex_pair_fst_snd)
qed

lemma card_V_ge_2: "card \<V> \<ge> 2"
proof-
  have "card {s, t} \<le> card \<V>"
    using s_in_V t_in_V \<V>_finite by (intro card_mono) auto
  thus ?thesis
    using s_neq_t by simp
qed

text \<open>If no vertex is active any more, the preflow is a maximum flow.\<close>

theorem no_active_max_flow:
  assumes "is_preflow s f" "valid_labelling s t f l" "\<And> v. \<not> active_vertex s t f v"
  shows "is_max_flow s t f"
proof-
  have uflow: "isuflow f"
    using assms(1) by (auto elim: is_preflowE)
  have ex_zero: "ex f v = 0" if "v \<in> \<V>" "v \<noteq> s" "v \<noteq> t" for v
    using assms(1) assms(3)[of v] that by (force elim: is_preflowE intro: active_vertexI)
  have ex_t: "ex f t \<ge> 0"
    using assms(1) t_in_V s_neq_t by (auto elim: is_preflowE)
  have "ex f s + (\<Sum> v \<in> \<V> - {s}. ex f v) = 0"
    using uflow_zero_total_excess[OF uflow] sum.remove[OF \<V>_finite s_in_V, of "ex f"] by simp
  moreover have "(\<Sum> v \<in> \<V> - {s}. ex f v) \<ge> 0"
    using assms(1) by (intro sum_nonneg) (auto elim: is_preflowE)
  ultimately have ex_s: "ex f s \<le> 0"
    by simp
  have "f is s -- t flow"
    using uflow ex_s s_in_V t_in_V s_neq_t ex_zero by (intro is_s_t_flowI)
  thus ?thesis
    using no_max_flow_resreach[OF s_in_V t_in_V s_neq_t] valid_labelling_no_resreach[OF assms(2)]
    by blast
qed

subsection \<open>Initialisation\<close>

lemma init_flow_nonneg: "init_flow s e \<ge> 0"
  using u_non_neg[of e] by (auto simp add: init_flow_def real_of_ereal_pos)

lemma init_flow_isuflow: "isuflow (init_flow s)"
proof(rule isuflowI)
  fix e
  assume e: "e \<in> \<E>"
  have "\<u> e \<ge> 0" "\<u> e < PInfty"
    using u_non_neg finite_capacities e by auto
  then obtain c where c: "\<u> e = ereal c"
    by (cases "\<u> e") auto
  show "ereal (init_flow s e) \<le> \<u> e"
    using c u_non_neg[of e] by (simp add: init_flow_def)
qed (rule init_flow_nonneg)

lemma init_flow_preflow: "is_preflow s (init_flow s)"
proof(rule is_preflowI[OF init_flow_isuflow])
  fix v
  assume v: "v \<in> \<V>" "v \<noteq> s"
  have "(\<Sum> e \<in> \<delta>\<^sup>+ v. init_flow s e) = 0"
    using v(2) by (intro sum.neutral) (auto simp add: delta_plus_def init_flow_def)
  moreover have "(\<Sum> e \<in> \<delta>\<^sup>- v. init_flow s e) \<ge> 0"
    by (intro sum_nonneg init_flow_nonneg)
  ultimately show "ex (init_flow s) v \<ge> 0"
    by (simp add: ex_def)
qed

lemma init_labels_valid: "valid_labelling s t (init_flow s) (init_labels s)"
proof(rule valid_labellingI)
  show "init_labels s s = card \<V>" "init_labels s t = 0"
    using s_neq_t by (auto simp add: init_labels_def)
next
  fix e
  assume e: "e \<in> \<EE>" "rcap (init_flow s) e > 0"
  show "init_labels s (fstv e) \<le> init_labels s (sndv e) + 1"
  proof(cases e)
    case (F d)
    hence d: "d \<in> \<E>"
      using e(1) o_edge_res[of e] by simp
    have "\<u> d \<ge> 0" "\<u> d < PInfty"
      using u_non_neg finite_capacities d by auto
    then obtain c where c: "\<u> d = ereal c"
      by (cases "\<u> d") auto
    have "\<not> (fst d = s \<and> snd d \<noteq> s)"
    proof
      assume "fst d = s \<and> snd d \<noteq> s"
      hence "init_flow s d = c"
        using c d by (simp add: init_flow_def)
      thus False
        using e(2) F c by simp
    qed
    thus ?thesis
      using F by (cases "fst d = s") (auto simp add: init_labels_def)
  next
    case (B d)
    note Bd = this
    have "init_flow s d > 0"
      using e(2) Bd by simp
    hence "fst d = s \<and> snd d \<noteq> s"
      by (auto simp add: init_flow_def split: if_splits)
    thus ?thesis
      using Bd by (auto simp add: init_labels_def)
  qed
qed

lemma init_labels_height_bounded: "height_bounded (init_labels s)"
  using cardV_0 by (auto intro!: height_boundedI simp add: init_labels_def)

lemma init_not_admissible: "\<not> admissible (init_flow s) (init_labels s) e"
proof
  assume adm: "admissible (init_flow s) (init_labels s) e"
  have "init_labels s (fstv e) \<noteq> 0"
    using adm by (auto elim: admissibleE)
  hence "fstv e = s"
    by (auto simp add: init_labels_def split: if_splits)
  hence "init_labels s (sndv e) = card \<V> - 1"
    using adm by (auto elim!: admissibleE simp add: init_labels_def)
  moreover have "card \<V> - 1 \<noteq> 0" "card \<V> - 1 \<noteq> card \<V>"
    using card_V_ge_2 by simp_all
  ultimately show False
    unfolding init_labels_def by (cases "sndv e = s") simp_all
qed

text \<open>Increasing labels does not make residual edges admissible whose tail keeps its label.\<close>

lemma admissible_increased_labels:
  assumes "valid_labelling s t f l" "\<And> x. x \<in> \<V> \<Longrightarrow> l x \<le> l' x"
          "l' (fstv e) = l (fstv e)" "admissible f l' e"
  shows "admissible f l e"
proof-
  have e: "e \<in> \<EE>" "rcap f e > 0" "l' (fstv e) = l' (sndv e) + 1"
    using assms(4) by (auto elim: admissibleE)
  have "l (fstv e) \<le> l (sndv e) + 1"
    using assms(1) e by (auto elim: valid_labellingE)
  moreover have "l (sndv e) \<le> l' (sndv e)"
    using assms(2) sndv_in_V[OF e(1)] .
  ultimately have "l (fstv e) = l (sndv e) + 1"
    using e(3) assms(3) by simp
  thus ?thesis
    using e by (auto intro: admissibleI)
qed

subsection \<open>Push\<close>

lemma push_amount_props:
  assumes "push_precond s t f l e"
  shows "push_amount f e > 0" "ereal (push_amount f e) \<le> rcap f e"
        "push_amount f e \<le> ex f (fstv e)"
proof-
  have e: "e \<in> \<EE>" "rcap f e > 0" "ex f (fstv e) > 0"
    using assms by (auto elim!: push_precondE admissibleE active_vertexE)
  obtain r where r: "rcap f e = ereal r"
    using e(1) by (rule rcap_finite)
  show "push_amount f e > 0" "ereal (push_amount f e) \<le> rcap f e"
       "push_amount f e \<le> ex f (fstv e)"
    using e r by (auto simp add: push_amount_def)
qed

lemma push_fstv_sndv:
  assumes "push_precond s t f l e"
  shows "fstv e \<noteq> sndv e" "e \<in> \<EE>" "l (fstv e) = l (sndv e) + 1"
  using assms by (auto elim!: push_precondE admissibleE)

lemma ex_push:
  assumes "push_precond s t f l e"
  shows "ex (push_effect f e) v =
         (if v = fstv e then ex f v - push_amount f e
          else if v = sndv e then ex f v + push_amount f e else ex f v)"
  unfolding push_effect_def ex_augment_edge[OF push_fstv_sndv(2)[OF assms]]
  using push_fstv_sndv(1)[OF assms] by auto

lemma push_preserves_preflow:
  assumes "is_preflow s f" "push_precond s t f l e"
  shows "is_preflow s (push_effect f e)"
proof(rule is_preflowI)
  show "isuflow (push_effect f e)"
    unfolding push_effect_def
  proof(rule augment_edge_validness_pres)
    show "isuflow f"
      using assms(1) by (auto elim: is_preflowE)
    show "0 \<le> push_amount f e"
      using push_amount_props(1)[OF assms(2)] by simp
    show "ereal (push_amount f e) \<le> rcap f e"
      using push_amount_props(2)[OF assms(2)] .
  qed
next
  fix v
  assume v: "v \<in> \<V>" "v \<noteq> s"
  have "ex f v \<ge> 0"
    using assms(1) v by (auto elim: is_preflowE)
  thus "ex (push_effect f e) v \<ge> 0"
    using push_amount_props[OF assms(2)] by (auto simp add: ex_push[OF assms(2)])
qed

lemma push_rcap_pos:
  assumes "push_precond s t f l e" "rcap (push_effect f e) d > 0"
  shows "rcap f d > 0 \<or> d = erev e"
proof-
  consider "d = erev e" | "d = e" | "d \<noteq> e" "d \<noteq> erev e"
    by blast
  thus ?thesis
  proof cases
    case 2
    thus ?thesis
      using assms by (auto elim!: push_precondE admissibleE)
  next
    case 3
    thus ?thesis
      using assms(2) unfolding push_effect_def rcap_augment_edge_other[OF 3] by simp
  qed simp
qed

lemma push_preserves_valid:
  assumes "valid_labelling s t f l" "push_precond s t f l e"
  shows "valid_labelling s t (push_effect f e) l"
proof(rule valid_labellingI)
  show "l s = card \<V>" "l t = 0"
    using assms(1) by (auto elim: valid_labellingE)
next
  fix d
  assume d: "d \<in> \<EE>" "rcap (push_effect f e) d > 0"
  show "l (fstv d) \<le> l (sndv d) + 1"
  proof(cases "d = erev e")
    case True
    thus ?thesis
      using push_fstv_sndv[OF assms(2)] by (simp add: vs_erev)
  next
    case False
    hence "rcap f d > 0"
      using push_rcap_pos[OF assms(2) d(2)] by simp
    thus ?thesis
      using assms(1) d(1) by (auto elim: valid_labellingE)
  qed
qed

lemma push_saturating_rcap:
  assumes "push_precond s t f l e" "real_of_ereal (rcap f e) \<le> ex f (fstv e)"
  shows "rcap (push_effect f e) e = 0"
proof-
  have "e \<in> \<EE>"
    using push_fstv_sndv[OF assms(1)] by simp
  then obtain r where r: "rcap f e = ereal r"
    by (rule rcap_finite)
  thus ?thesis
    unfolding push_effect_def rcap_augment_edge_same
    using assms(2) by (simp add: push_amount_def)
qed

lemma push_nonsaturating_ex:
  assumes "push_precond s t f l e" "ex f (fstv e) < real_of_ereal (rcap f e)"
  shows "ex (push_effect f e) (fstv e) = 0"
  using assms(2) by (simp add: ex_push[OF assms(1)] push_amount_def)

lemma push_nonsaturating_rcap:
  assumes "push_precond s t f l e" "ex f (fstv e) < real_of_ereal (rcap f e)"
  shows "rcap (push_effect f e) e > 0"
proof-
  have "e \<in> \<EE>"
    using push_fstv_sndv[OF assms(1)] by simp
  then obtain r where r: "rcap f e = ereal r"
    by (rule rcap_finite)
  thus ?thesis
    unfolding push_effect_def rcap_augment_edge_same
    using assms(2) by (simp add: push_amount_def)
qed

lemma push_admissible:
  assumes "push_precond s t f l e" "admissible (push_effect f e) l d"
  shows "admissible f l d"
proof-
  have d: "d \<in> \<EE>" "rcap (push_effect f e) d > 0" "l (fstv d) = l (sndv d) + 1"
    using assms(2) by (auto elim: admissibleE)
  have "d \<noteq> erev e"
    using push_fstv_sndv[OF assms(1)] d(3) by (auto simp add: vs_erev)
  hence "rcap f d > 0"
    using push_rcap_pos[OF assms(1) d(2)] by simp
  thus ?thesis
    using d by (auto intro: admissibleI)
qed

lemma push_active:
  assumes "push_precond s t f l e" "active_vertex s t (push_effect f e) v"
  shows "v = sndv e \<or> active_vertex s t f v"
proof(cases "v = sndv e")
  case False
  have v: "v \<in> \<V>" "v \<noteq> s" "v \<noteq> t" "ex (push_effect f e) v > 0"
    using assms(2) by (auto elim: active_vertexE)
  have "ex (push_effect f e) v \<le> ex f v"
    using False push_amount_props(1)[OF assms(1)] by (simp add: ex_push[OF assms(1)])
  thus ?thesis
    using v by (auto intro: active_vertexI)
qed simp

subsection \<open>Relabel\<close>

lemma relabel_labels_finite: "finite (relabel_labels f l u)"
proof-
  have "relabel_labels f l u \<subseteq> (\<lambda> e. l (sndv e)) ` \<EE>"
    by (auto simp add: relabel_labels_def)
  thus ?thesis
    using finite_\<EE> finite_subset by blast
qed

lemma relabel_labels_nonempty:
  assumes "is_preflow s f" "active_vertex s t f u"
  shows "relabel_labels f l u \<noteq> {}"
  using active_residual_out_edge[OF assms] by (auto simp add: relabel_labels_def)

lemma relabel_labels_ge:
  assumes "valid_labelling s t f l" "relabel_precond s t f l u" "x \<in> relabel_labels f l u"
  shows "l u \<le> x"
proof-
  obtain e where e: "x = l (sndv e)" "e \<in> \<EE>" "fstv e = u" "rcap f e > 0"
    using assms(3) by (auto simp add: relabel_labels_def)
  have "l u \<le> l (sndv e) + 1"
    using assms(1) e by (auto elim: valid_labellingE)
  moreover have "\<not> admissible f l e"
    using assms(2) e by (auto elim: relabel_precondE)
  ultimately show ?thesis
    using e by (auto intro: admissibleI)
qed

lemma relabel_increases:
  assumes "is_preflow s f" "valid_labelling s t f l" "relabel_precond s t f l u"
  shows "l u < relabel_effect f l u u"
proof-
  have act: "active_vertex s t f u"
    using assms(3) by (auto elim: relabel_precondE)
  have "l u \<le> Min (relabel_labels f l u)"
    using relabel_labels_nonempty[OF assms(1) act] relabel_labels_ge[OF assms(2,3)]
    by (subst Min_ge_iff[OF relabel_labels_finite]) auto
  thus ?thesis
    by (simp add: relabel_effect_def)
qed

lemma relabel_mono:
  assumes "is_preflow s f" "valid_labelling s t f l" "relabel_precond s t f l u"
  shows "l v \<le> relabel_effect f l u v"
  using relabel_increases[OF assms] by (cases "v = u") (auto simp add: relabel_effect_def)

lemma relabel_preserves_valid:
  assumes "is_preflow s f" "valid_labelling s t f l" "relabel_precond s t f l u"
  shows "valid_labelling s t f (relabel_effect f l u)"
proof-
  have act: "u \<noteq> s" "u \<noteq> t"
    using assms(3) by (auto elim: relabel_precondE active_vertexE)
  show ?thesis
  proof(rule valid_labellingI)
    show "relabel_effect f l u s = card \<V>" "relabel_effect f l u t = 0"
      using assms(2) act by (auto simp add: relabel_effect_def elim: valid_labellingE)
  next
    fix d
    assume d: "d \<in> \<EE>" "rcap f d > 0"
    have mono: "l (sndv d) \<le> relabel_effect f l u (sndv d)"
      by (rule relabel_mono[OF assms])
    show "relabel_effect f l u (fstv d) \<le> relabel_effect f l u (sndv d) + 1"
    proof(cases "fstv d = u")
      case True
      hence "l (sndv d) \<in> relabel_labels f l u"
        using d by (auto simp add: relabel_labels_def)
      hence "Min (relabel_labels f l u) \<le> l (sndv d)"
        by (rule Min_le[OF relabel_labels_finite])
      thus ?thesis
        using True mono by (simp add: relabel_effect_def)
    next
      case False
      have "l (fstv d) \<le> l (sndv d) + 1"
        using assms(2) d by (auto elim: valid_labellingE)
      thus ?thesis
        using False mono by (simp add: relabel_effect_def)
    qed
  qed
qed

lemma relabel_preserves_height_bounded:
  assumes "is_preflow s f" "valid_labelling s t f l" "relabel_precond s t f l u" "height_bounded l"
  shows "height_bounded (relabel_effect f l u)"
proof(rule height_boundedI)
  fix v
  assume v: "v \<in> \<V>"
  show "relabel_effect f l u v \<le> 2 * card \<V> - 1"
  proof(cases "v = u")
    case True
    have "active_vertex s t f u"
      using assms(3) by (auto elim: relabel_precondE)
    thus ?thesis
      using active_label_bound[OF assms(1) relabel_preserves_valid[OF assms(1-3)]] True by simp
  next
    case False
    thus ?thesis
      using height_boundedD[OF assms(4) v] by (simp add: relabel_effect_def)
  qed
qed

subsection \<open>Gap Relabelling\<close>

lemma gap_mono: "l v \<le> gap_effect l k v"
  by (auto simp add: gap_effect_def)

lemma gap_preserves_valid:
  assumes "valid_labelling s t f l" "gap_precond l k"
  shows "valid_labelling s t f (gap_effect l k)"
proof-
  have gap: "\<And> v. v \<in> \<V> \<Longrightarrow> l v \<noteq> k"
    using assms(2) by (auto simp add: gap_precond_def)
  show ?thesis
  proof(rule valid_labellingI)
    show "gap_effect l k s = card \<V>" "gap_effect l k t = 0"
      using assms(1) by (auto simp add: gap_effect_def elim: valid_labellingE)
  next
    fix d
    assume d: "d \<in> \<EE>" "rcap f d > 0"
    define a b where "a = fstv d" "b = sndv d"
    have ab: "a \<in> \<V>" "b \<in> \<V>" "l a \<le> l b + 1"
      using fstv_in_V sndv_in_V d assms(1) by (auto simp add: a_b_def elim: valid_labellingE)
    show "gap_effect l k (fstv d) \<le> gap_effect l k (sndv d) + 1"
    proof(cases "k < l a \<and> l a < card \<V>")
      case True
      have "l b \<noteq> k"
        using gap ab(2) .
      hence "k < l b"
        using True ab(3) by simp
      hence "gap_effect l k b \<ge> card \<V>"
        using ab(2) by (auto simp add: gap_effect_def)
      thus ?thesis
        using True ab(1) by (simp add: gap_effect_def a_b_def[symmetric])
    next
      case False
      hence "gap_effect l k a = l a"
        by (simp add: gap_effect_def)
      thus ?thesis
        using ab(3) gap_mono[of l b k] by (simp add: a_b_def[symmetric])
    qed
  qed
qed

lemma gap_preserves_height_bounded:
  assumes "height_bounded l"
  shows "height_bounded (gap_effect l k)"
  using height_boundedD[OF assms] card_V_ge_2
  by (auto intro!: height_boundedI simp add: gap_effect_def)

lemma relabel_gap_mono:
  assumes "is_preflow s f" "valid_labelling s t f l" "relabel_precond s t f l u"
  shows "l v \<le> relabel_gap_effect f l u v"
  using relabel_mono[OF assms, of v] gap_mono[of "relabel_effect f l u" v "l u"]
  by (auto simp add: relabel_gap_effect_def Let_def)

lemma relabel_gap_increases:
  assumes "is_preflow s f" "valid_labelling s t f l" "relabel_precond s t f l u"
  shows "l u < relabel_gap_effect f l u u"
  using relabel_increases[OF assms] gap_mono[of "relabel_effect f l u" u "l u"]
  by (auto simp add: relabel_gap_effect_def Let_def)

lemma relabel_gap_preserves_valid:
  assumes "is_preflow s f" "valid_labelling s t f l" "relabel_precond s t f l u"
  shows "valid_labelling s t f (relabel_gap_effect f l u)"
  using relabel_preserves_valid[OF assms] gap_preserves_valid
  by (auto simp add: relabel_gap_effect_def Let_def)

lemma relabel_gap_preserves_height_bounded:
  assumes "is_preflow s f" "valid_labelling s t f l" "relabel_precond s t f l u" "height_bounded l"
  shows "height_bounded (relabel_gap_effect f l u)"
  using relabel_preserves_height_bounded[OF assms] gap_preserves_height_bounded
  by (auto simp add: relabel_gap_effect_def Let_def)

subsection \<open>Termination Measures\<close>

lemma label_measure_decrease:
  assumes "\<And> v. v \<in> \<V> \<Longrightarrow> l v \<le> l' v" "height_bounded l'" "v \<in> \<V>" "l v < l' v"
  shows "label_measure l' < label_measure l"
  unfolding label_measure_def
proof(rule sum_strict_mono_ex1[OF \<V>_finite])
  show "\<forall> x \<in> \<V>. 2 * card \<V> - l' x \<le> 2 * card \<V> - l x"
    using assms(1) by (simp add: diff_le_mono2)
  have "l' v < 2 * card \<V>"
    using height_boundedD[OF assms(2,3)] cardV_0 by simp
  thus "\<exists> x \<in> \<V>. 2 * card \<V> - l' x < 2 * card \<V> - l x"
    using assms(3,4) by (intro bexI[of _ v]) auto
qed

lemma relabel_label_measure:
  assumes "is_preflow s f" "valid_labelling s t f l" "relabel_precond s t f l u" "height_bounded l"
  shows "label_measure (relabel_effect f l u) < label_measure l"
proof-
  have "u \<in> \<V>"
    using assms(3) by (auto elim: relabel_precondE active_vertexE)
  thus ?thesis
    using relabel_mono[OF assms(1-3)] relabel_preserves_height_bounded[OF assms]
          relabel_increases[OF assms(1-3)]
    by (intro label_measure_decrease) auto
qed

lemma relabel_gap_label_measure:
  assumes "is_preflow s f" "valid_labelling s t f l" "relabel_precond s t f l u" "height_bounded l"
  shows "label_measure (relabel_gap_effect f l u) < label_measure l"
proof-
  have "u \<in> \<V>"
    using assms(3) by (auto elim: relabel_precondE active_vertexE)
  thus ?thesis
    using relabel_gap_mono[OF assms(1-3)] relabel_gap_preserves_height_bounded[OF assms]
          relabel_gap_increases[OF assms(1-3)]
    by (intro label_measure_decrease) auto
qed

lemma admissible_finite: "finite {e. admissible f l e}"
  using finite_\<EE> by (rule finite_subset[rotated]) (auto elim: admissibleE)

lemma push_admissible_count_mono:
  assumes "push_precond s t f l e"
  shows "admissible_count (push_effect f e) l \<le> admissible_count f l"
  unfolding admissible_count_def
  using push_admissible[OF assms] admissible_finite by (intro card_mono) auto

lemma push_saturating_admissible_count:
  assumes "push_precond s t f l e" "real_of_ereal (rcap f e) \<le> ex f (fstv e)"
  shows "admissible_count (push_effect f e) l < admissible_count f l"
proof-
  have "{d. admissible (push_effect f e) l d} \<subseteq> {d. admissible f l d} - {e}"
    using push_admissible[OF assms(1)] push_saturating_rcap[OF assms]
    by (auto elim: admissibleE)
  moreover have "e \<in> {d. admissible f l d}"
    using assms(1) by (auto elim: push_precondE)
  ultimately show ?thesis
    unfolding admissible_count_def
    using admissible_finite
    by (meson card_Diff1_less card_mono finite_Diff le_less_trans)
qed

lemma active_finite: "finite {v. active_vertex s t f v}"
  using \<V>_finite by (rule finite_subset[rotated]) (auto elim: active_vertexE)

lemma push_nonsaturating_active_potential:
  assumes "push_precond s t f l e" "ex f (fstv e) < real_of_ereal (rcap f e)"
  shows "active_potential s t (push_effect f e) l < active_potential s t f l"
proof-
  define u v A A' where "u = fstv e" "v = sndv e"
    "A = {w. active_vertex s t f w}" "A' = {w. active_vertex s t (push_effect f e) w}"
  have uv: "l u = l v + 1"
    using push_fstv_sndv[OF assms(1)] by (simp add: u_v_A_A'_def)
  have uA: "u \<in> A"
    using assms(1) by (auto elim: push_precondE simp add: u_v_A_A'_def)
  have "A' \<subseteq> insert v (A - {u})"
  proof
    fix w
    assume "w \<in> A'"
    hence w: "active_vertex s t (push_effect f e) w"
      by (simp add: u_v_A_A'_def)
    hence "w \<noteq> u"
      using push_nonsaturating_ex[OF assms] by (auto elim: active_vertexE simp add: u_v_A_A'_def)
    thus "w \<in> insert v (A - {u})"
      using push_active[OF assms(1) w] by (auto simp add: u_v_A_A'_def)
  qed
  hence "sum l A' \<le> sum l (insert v (A - {u}))"
    using active_finite by (intro sum_mono2) (auto simp add: u_v_A_A'_def)
  also have "\<dots> \<le> l v + sum l (A - {u})"
    using active_finite by (simp add: sum.insert_if u_v_A_A'_def)
  also have "\<dots> < l u + sum l (A - {u})"
    using uv by simp
  also have "\<dots> = sum l A"
    using sum.remove[OF _ uA, of l] active_finite by (simp add: u_v_A_A'_def)
  finally show ?thesis
    by (simp add: active_potential_def u_v_A_A'_def)
qed

end

end

end

