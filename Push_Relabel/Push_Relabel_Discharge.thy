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
  using assms push_amount_props(1)[of f l e] push_fstv_sndv(2)[of f l e]
  by (auto simp: active_vertex_def push_amount_def is_preflow_def sndv_in_V ex_push elim: push_precondE)

lemma active_vertex_iff:
  "\<lbrakk>invar_state st; v \<in> \<V>\<rbrakk>
   \<Longrightarrow> active_vertex s t (flow_abs st) v \<longleftrightarrow>
       v \<noteq> s \<and> v \<noteq> t \<and> 0 < ex_get (pr_excess st) v"
  by (auto simp: active_vertex_def elim!: invar_props_elims)
text \<open>How the operations change the set of active vertices, in terms of the data structures.\<close>

lemma push_fwd_impl_active:
  assumes "invar_state st" "push_precond s t (flow_abs st) (labels_abs st) (F d)"
  shows "active_vertex s t (flow_abs (push_fwd_impl d st)) v \<longleftrightarrow>
         (if v = fst d then emap_get (pr_fwd st) d < ex_get (pr_excess st) v
          else if v = snd d then v \<noteq> s \<and> v \<noteq> t else active_vertex s t (flow_abs st) v)"
  using assms push_fstv_sndv(2)[of "flow_abs st" "labels_abs st" "F d"]
        push_impl_props(2)[of st "Push_Fwd d" d "F d"]
  by (auto simp: push_active_iff res_correct_def \<EE>_def fst_E_V elim!: invar_props_elims elim: active_vertexE)

lemma push_bwd_impl_active:
  assumes "invar_state st" "push_precond s t (flow_abs st) (labels_abs st) (B d)"
  shows "active_vertex s t (flow_abs (push_bwd_impl d st)) v \<longleftrightarrow>
         (if v = snd d then emap_get (pr_bwd st) d < ex_get (pr_excess st) v
          else if v = fst d then v \<noteq> s \<and> v \<noteq> t else active_vertex s t (flow_abs st) v)"
  using assms push_fstv_sndv(2)[of "flow_abs st" "labels_abs st" "B d"]
        push_impl_props(2)[of st "Push_Bwd d" d "B d"]
  by (auto simp: push_active_iff \<EE>_def snd_E_V elim!: invar_props_elims elim: active_vertexE)

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
  using assms
  by (cases op) (auto simp: good_op_def push_fwd_impl_active push_bwd_impl_active advance_impl_props(2)
                            relabel_impl_props(3) relabel_gap_impl_props(3))

lemma no_current_relabel_precond:
  assumes "invar_state st" "active_vertex s t (flow_abs st) u" "\<not> out_has (pr_out st) u"
          "\<not> in_has (pr_in st) u"
  shows "relabel_precond s t (flow_abs st) (labels_abs st) u"
  using assms outg.idx_partition_union[of "pr_out st" u] outg.idx_has[of "pr_out st" u]
        ing.idx_partition_union[of "pr_in st" u] ing.idx_has[of "pr_in st" u]
  by (intro relabel_precondI)
     (auto simp: active_vertex_def out_graph_inv_delta in_graph_inv_delta \<EE>_def iterated_res_def
                 delta_plus_def delta_minus_def elim!: invar_props_elims)

text \<open>The discharge step requests an operation that is allowed, never stops, and pushes along
      a residual edge leaving the vertex being discharged.\<close>

lemma discharge_op_props:
  assumes "invar_state st" "active_vertex s t (flow_abs st) u"
          "discharge_op gap (pr_fwd st) (pr_bwd st) (pr_labels st) (pr_out st) (pr_in st) u = op"
  shows "good_op st op \<and> op \<noteq> Done \<and> (\<forall> d. op = Push_Fwd d \<longrightarrow> fst d = u) \<and>
         (\<forall> d. op = Push_Bwd d \<longrightarrow> snd d = u)"
  using assms no_current_relabel_precond[OF assms(1,2)] out_graph_inv_delta(6)[of "pr_out st" u]
        in_graph_inv_delta(6)[of "pr_in st" u]
  by (auto simp: discharge_op_def Let_def current_res_def good_op_def push_precond_def delta_plus_def
                 delta_minus_def active_vertex_def admissible_fwd_impl admissible_bwd_impl
           split: if_splits elim!: invar_props_elims)

end

end
