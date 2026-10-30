theory Push_Relabel_Discharge_Imperative
  imports
    Push_Relabel_Generic_Imperative
    Push_Relabel_Discharge
begin

provenance ai


section \<open>Imperative Refinement of the Discharge Step\<close>

text \<open>The discharge step only reads the data structures: it looks at the current residual edge
      of the vertex and decides on the operation.\<close>

text \<open>A strategy discharges one vertex at a time. The current vertex, if any, is kept in a flag
      reference and a vertex reference, so that changing it allocates nothing.\<close>

definition cur_assn :: "'v option \<Rightarrow> bool ref \<Rightarrow> 'v::heap ref \<Rightarrow> assn" where
  "cur_assn cur Cf Cu = (\<exists>\<^sub>A f u. Cf \<mapsto>\<^sub>r f * Cu \<mapsto>\<^sub>r u * \<up>(cur = (if f then Some u else None)))"

definition "cur_flag_imp Cf = !Cf"

definition "cur_get_imp Cu = !Cu"

definition "cur_set_imp Cf Cu u = do { Cf := True; Cu := u }"

definition "cur_clear_imp Cf = (Cf := False)"

lemma cur_flag_rule:
  "<cur_assn cur Cf Cu> cur_flag_imp Cf <\<lambda>f. cur_assn cur Cf Cu * \<up>(f = (cur \<noteq> None))>"
  unfolding cur_assn_def cur_flag_imp_def
  by sep_auto

lemma cur_get_rule:
  "cur = Some u \<Longrightarrow> <cur_assn cur Cf Cu> cur_get_imp Cu <\<lambda>r. cur_assn cur Cf Cu * \<up>(r = u)>"
  unfolding cur_assn_def cur_get_imp_def
  by (sep_auto split: if_splits)

lemma cur_set_rule: "<cur_assn cur Cf Cu> cur_set_imp Cf Cu u <\<lambda>_. cur_assn (Some u) Cf Cu>"
  unfolding cur_assn_def cur_set_imp_def
  by sep_auto

lemma cur_clear_rule: "<cur_assn cur Cf Cu> cur_clear_imp Cf <\<lambda>_. cur_assn None Cf Cu>"
  unfolding cur_assn_def cur_clear_imp_def
  by sep_auto

context push_relabel_ops_imp_code
begin

definition "discharge_op_imp gap Si u = do {
   b \<leftarrow> out_has_imp (pi_out Si) u;
   if b then do {
     d \<leftarrow> out_current_imp (pi_out Si) u;
     a \<leftarrow> admissible_fwd_imp (pi_ends Si) (pi_fwd Si) (pi_lab Si) d;
     return (if a then Push_Fwd d else Advance u) }
   else do {
     c \<leftarrow> in_has_imp (pi_in Si) u;
     if c then do {
       d \<leftarrow> in_current_imp (pi_in Si) u;
       a \<leftarrow> admissible_bwd_imp (pi_ends Si) (pi_bwd Si) (pi_lab Si) d;
       return (if a then Push_Bwd d else Advance u) }
     else return (if gap then Relabel_Gap u else Relabel u) } }"

end

context push_relabel_ops_imp
begin

lemma discharge_op_imp_rule:
  assumes "invar_basic st" "u \<in> \<V>"
  shows "<state_assn st Si> discharge_op_imp gap Si u
         <\<lambda>r. state_assn st Si *
              \<up>(r = discharge_op gap (pr_fwd st) (pr_bwd st) (pr_labels st) (pr_out st) (pr_in st) u)>"
proof(cases "out_has (pr_out st) u")
  case True
  note I = invar_basic_maps[OF assms(1)] invar_basic_iters[OF assms]
  have ne: "out_remaining (pr_out st) u \<noteq> {}" "out_current (pr_out st) u \<in> \<E>"
    using assms True I(6) out_graph_inv_delta(6)[of "pr_out st" u]
    by (auto elim!: invar_basic_props simp: delta_plus_def outg.idx_has)
  show ?thesis
    unfolding discharge_op_imp_def state_assn_def
    by (sep_auto heap: out_imp.idx_has_rule[OF I(6) assms(2)]
                       out_imp.idx_current_rule[OF I(6) assms(2) ne(1)]
                       admissible_fwd_imp_rule[OF I(1,4) ne(2)]
                 simp: True discharge_op_def)
next
  case False
  note I = invar_basic_maps[OF assms(1)] invar_basic_iters[OF assms]
  show ?thesis
  proof(cases "in_has (pr_in st) u")
    case True
    have ne: "in_remaining (pr_in st) u \<noteq> {}" "in_current (pr_in st) u \<in> \<E>"
      using assms True ing.idx_has[OF I(7) assms(2)] in_graph_inv_delta(6)[of "pr_in st" u]
      by (auto elim!: invar_basic_props simp: delta_minus_def)
    show ?thesis
      unfolding discharge_op_imp_def state_assn_def
      by (sep_auto heap: out_imp.idx_has_rule[OF I(6) assms(2)]
                         in_imp.idx_has_rule[OF I(7) assms(2)]
                         in_imp.idx_current_rule[OF I(7) assms(2) ne(1)]
                         admissible_bwd_imp_rule[OF I(2,4) ne(2)]
                   simp: False True discharge_op_def)
  next
    case F2: False
    show ?thesis
      unfolding discharge_op_imp_def state_assn_def
      by (sep_auto heap: out_imp.idx_has_rule[OF I(6) assms(2)]
                         in_imp.idx_has_rule[OF I(7) assms(2)]
                   simp: False F2 discharge_op_def)
  qed
qed

end

end
