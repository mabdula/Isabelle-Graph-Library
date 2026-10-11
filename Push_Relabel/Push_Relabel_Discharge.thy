theory Push_Relabel_Discharge
  imports
    Push_Relabel_Generic
begin

section \<open>The Discharge Step\<close>

text \<open>The step shared by all strategies when working on an active vertex \<open>u\<close>: if the current
      residual edge of \<open>u\<close> is admissible, push along it; if it is not, advance to the next one;
      if \<open>u\<close> has no current residual edge left, relabel \<open>u\<close> (with the gap heuristic iff
      @{term gap}).\<close>

context push_relabel_ops
begin

definition "discharge_op gap fw bw l og ig u =
  (if out_has og u
   then (let d = out_current og u in
         if admissible_fwd_impl fw l d then Push_Fwd d else Advance u)
   else if in_has ig u
   then (let d = in_current ig u in
         if admissible_bwd_impl bw l d then Push_Bwd d else Advance u)
   else if gap then Relabel_Gap u else Relabel u)"

lemmas [code] = discharge_op_def


end

context push_relabel_ops_correct
begin

text \<open>How a push changes the set of active vertices.\<close>

lemma push_active_iff:
  assumes "push_precond s t f l e" "is_preflow s f"
  shows "active_vertex s t (push_effect f e) v \<longleftrightarrow>
         (if v = fstv e then real_of_ereal (rcap f e) < ex f v
          else if v = sndv e then v \<noteq> s \<and> v \<noteq> t
          else active_vertex s t f v)"
proof-
  note pa = push_amount_props[OF net_assms assms(1)]
  note ps = push_fstv_sndv[OF net_assms assms(1)]
  note exp = ex_push[OF net_assms assms(1)]
  have u: "active_vertex s t f (fstv e)"
    using assms(1) by (auto elim: push_precondE)
  show ?thesis
  proof(cases "v = fstv e")
    case True
    have "ex (push_effect f e) v = ex f v - min (ex f v) (real_of_ereal (rcap f e))"
      using True by (simp add: exp push_amount_def)
    thus ?thesis
      using u True by (auto simp add: active_vertex_def)
  next
    case False
    note F = this
    show ?thesis
    proof(cases "v = sndv e")
      case True
      have v: "v \<in> \<V>"
        using sndv_in_V[OF net_assms ps(2)] True by simp
      have "v \<noteq> s \<Longrightarrow> ex f v \<ge> 0"
        using assms(2) v by (simp add: is_preflow_def)
      moreover have "ex (push_effect f e) v = ex f v + push_amount f e"
        using True F by (simp add: exp)
      ultimately show ?thesis
        using v pa(1) True F by (auto simp add: active_vertex_def)
    next
      case False
      thus ?thesis
        using F by (simp add: exp active_vertex_def)
    qed
  qed
qed

text \<open>How the operations change the set of active vertices, in terms of the data structures.\<close>

lemma apply_op_active:
  assumes "invar_state st" "good_op st op"
  shows "active_vertex s t (flow_abs (apply_op op st)) v \<longleftrightarrow>
         (case op of
            Push_Fwd d \<Rightarrow> (if v = fst d then emap_get (pr_fwd st) d < ex_get (pr_excess st) v
                           else if v = snd d then v \<noteq> s \<and> v \<noteq> t
                           else active_vertex s t (flow_abs st) v)
          | Push_Bwd d \<Rightarrow> (if v = snd d then emap_get (pr_bwd st) d < ex_get (pr_excess st) v
                           else if v = fst d then v \<noteq> s \<and> v \<noteq> t
                           else active_vertex s t (flow_abs st) v)
          | _ \<Rightarrow> active_vertex s t (flow_abs st) v)"
proof-
  note inv = invar_stateD[OF assms(1)]
  show ?thesis
  proof(cases op)
    case (Push_Fwd d)
    have pp: "push_precond s t (flow_abs st) (labels_abs st) (F d)"
      using assms(2) by (simp add: Push_Fwd good_op_def)
    have d: "d \<in> \<E>"
      using push_fstv_sndv(2)[OF net_assms pp] by (auto simp add: \<EE>_def)
    have r: "real_of_ereal (rcap (flow_abs st) (F d)) = emap_get (pr_fwd st) d"
      using rcap_fwd[OF inv(14) d] by simp
    have x: "ex_get (pr_excess st) (fst d) = ex (flow_abs st) (fst d)"
      using inv(6) d by (auto intro: fst_E_V)
    have fl: "flow_abs (apply_op op st) = push_effect (flow_abs st) (F d)"
      using push_impl_props(2)[OF assms(1) _ pp, of op d] Push_Fwd by simp
    show ?thesis
      unfolding fl push_active_iff[OF pp inv(8)] using r x
      by (cases "v = fst d") (simp_all add: Push_Fwd)
  next
    case (Push_Bwd d)
    have pp: "push_precond s t (flow_abs st) (labels_abs st) (B d)"
      using assms(2) by (simp add: Push_Bwd good_op_def)
    have d: "d \<in> \<E>"
      using push_fstv_sndv(2)[OF net_assms pp] by (auto simp add: \<EE>_def)
    have x: "ex_get (pr_excess st) (snd d) = ex (flow_abs st) (snd d)"
      using inv(6) d by (auto intro: snd_E_V)
    have fl: "flow_abs (apply_op op st) = push_effect (flow_abs st) (B d)"
      using push_impl_props(2)[OF assms(1) _ pp, of op d] Push_Bwd by simp
    show ?thesis
      unfolding fl push_active_iff[OF pp inv(8)] using x
      by (cases "v = snd d") (simp_all add: Push_Bwd)
  next
    case (Advance u)
    hence "u \<in> \<V>" "\<exists> e. current_res st u = Some e \<and> \<not> admissible (flow_abs st) (labels_abs st) e"
      using assms(2) by (simp_all add: good_op_def)
    thus ?thesis
      using advance_impl_props(2)[OF assms(1)] by (auto simp add: Advance)
  next
    case (Relabel u)
    thus ?thesis
      using relabel_impl_props(3)[OF assms(1)] assms(2) by (simp add: good_op_def)
  next
    case (Relabel_Gap u)
    thus ?thesis
      using relabel_gap_impl_props(3)[OF assms(1)] assms(2) by (simp add: good_op_def)
  qed simp
qed

text \<open>The discharge step requests an operation that is allowed, never stops, and pushes along
      a residual edge leaving the vertex being discharged.\<close>

lemma discharge_op_props:
  assumes "invar_state st" "active_vertex s t (flow_abs st) u"
          "discharge_op gap (pr_fwd st) (pr_bwd st) (pr_labels st) (pr_out st) (pr_in st) u = op"
  shows "good_op st op \<and> op \<noteq> Done \<and> (\<forall> d. op = Push_Fwd d \<longrightarrow> fst d = u) \<and>
         (\<forall> d. op = Push_Bwd d \<longrightarrow> snd d = u)"
proof-
  note inv = invar_stateD[OF assms(1)]
  have u: "u \<in> \<V>"
    using assms(2) by (simp add: active_vertex_def)
  show ?thesis
  proof(cases "out_has (pr_out st) u")
    case True
    define d where "d = out_current (pr_out st) u"
    have "d \<in> out_remaining (pr_out st) u"
      using outg.idx_current[OF inv(5) u] outg.idx_has[OF inv(5) u] True by (simp add: d_def)
    hence "d \<in> \<delta>\<^sup>+ u"
      using outg.idx_partition_union[OF inv(5) u] inv(11)[OF u] by blast
    hence d: "d \<in> \<E>" "fst d = u"
      by (auto simp add: delta_plus_def)
    have cur: "current_res st u = Some (F d)"
      using True by (simp add: current_res_def d_def)
    have dop: "op = (if admissible_fwd_impl (pr_fwd st) (pr_labels st) d then Push_Fwd d else Advance u)"
      using True by (simp add: assms(3)[symmetric] discharge_op_def d_def)
    show ?thesis
      unfolding dop admissible_fwd_impl[OF inv(14) d(1)]
      using assms(2) u cur d(2) by (simp add: good_op_def push_precond_def)
  next
    case out: False
    show ?thesis
    proof(cases "in_has (pr_in st) u")
      case True
      define d where "d = in_current (pr_in st) u"
      have "d \<in> in_remaining (pr_in st) u"
        using ing.idx_current[OF inv(15) u] ing.idx_has[OF inv(15) u] True by (simp add: d_def)
      hence "d \<in> \<delta>\<^sup>- u"
        using ing.idx_partition_union[OF inv(15) u] inv(16)[OF u] by blast
      hence d: "d \<in> \<E>" "snd d = u"
        by (auto simp add: delta_minus_def)
      have cur: "current_res st u = Some (B d)"
        using out True by (simp add: current_res_def d_def)
      have dop: "op = (if admissible_bwd_impl (pr_bwd st) (pr_labels st) d then Push_Bwd d else Advance u)"
        using out True by (simp add: assms(3)[symmetric] discharge_op_def d_def)
      show ?thesis
        unfolding dop admissible_bwd_impl[OF d(1)]
        using assms(2) u cur d(2) by (simp add: good_op_def push_precond_def)
    next
      case False
      have oi: "out_iterated (pr_out st) u = \<delta>\<^sup>+ u"
        using outg.idx_partition_union[OF inv(5) u] outg.idx_has[OF inv(5) u] out inv(11)[OF u]
        by simp
      have ii: "in_iterated (pr_in st) u = \<delta>\<^sup>- u"
        using ing.idx_partition_union[OF inv(15) u] ing.idx_has[OF inv(15) u] False inv(16)[OF u]
        by simp
      have rp: "relabel_precond s t (flow_abs st) (labels_abs st) u"
      proof(rule relabel_precondI[OF assms(2)])
        fix e
        assume e: "e \<in> \<EE>" "fstv e = u"
        have "e \<in> iterated_res st u"
          using e by (auto simp add: \<EE>_def iterated_res_def oi ii delta_plus_def delta_minus_def)
        thus "\<not> admissible (flow_abs st) (labels_abs st) e"
          using inv(12)[OF u] by blast
      qed
      show ?thesis
        using out False rp by (simp add: assms(3)[symmetric] discharge_op_def good_op_def)
    qed
  qed
qed

end

end
