theory Worst_Out_Greedy
  imports
    Greedy_Common
begin

section \<open>The Worst-Out-Greedy Algorithm for Independence Systems\<close>

text \<open>We formalise the worst-out greedy algorithm (Korte, Vygen, 6th ed., Section 13.4) for the
problem of finding a basis of minimum weight in an independence system and Theorem 13.22.
The elements are processed by non-increasing weight and an element is removed from the current
set if the remaining set still contains a basis.

The algorithm accesses the independence system only via a \emph{weak basis superset oracle}:
provided that the current set F contains a basis and given an element x of F, the oracle tells
whether F - {x} still contains a basis. This is weaker than the basis-superset oracle assumed in
the book, which decides for an arbitrary subset of the carrier whether it contains a basis.
It nevertheless suffices, since the algorithm queries the oracle only in states where the current
set contains a basis. The oracle is the analogue of the weak independence oracle used for the
best-in greedy algorithm, in fact it is the weak independence oracle of the dual independence
system: with D the set of removed elements, F - {x} contains a basis iff insert x D is independent
in the dual system. Hence, there is just a single algorithm and the proofs mirror those for the
best-in greedy algorithm, applied to the dual.\<close>

locale Worst_Out_Greedy = Greedy_Common set_insert set_delete set_isin set_inv union inter diff
  cardinality to_set set_empty carrier indep_fn sort_desc
  for set_insert :: "'a::linorder \<Rightarrow> 's \<Rightarrow> 's" and set_delete set_isin set_inv union inter diff
    cardinality to_set set_empty carrier indep_fn sort_desc +
  fixes basis_superset_oracle :: "'a \<Rightarrow> 'wrps \<Rightarrow> bool"
    and remove_wrapper :: "'wrps \<Rightarrow> 's"
    and wrapper_invar :: "'wrps \<Rightarrow> bool"
    and wrapper_delete :: "'a \<Rightarrow> 'wrps \<Rightarrow> 'wrps"
    and wrapper_carrier :: "'wrps"
  assumes wrapper_axioms:
    "\<And>S x. wrapper_invar S \<Longrightarrow> wrapper_invar (wrapper_delete x S)"
    "\<And>S. wrapper_invar S \<Longrightarrow> set_inv (remove_wrapper S)"
    "\<And>S x. wrapper_invar S \<Longrightarrow> remove_wrapper (wrapper_delete x S) = set_delete x (remove_wrapper S)"
    "carrier = remove_wrapper wrapper_carrier"
    "wrapper_invar wrapper_carrier"
begin

text \<open>The state stores the remaining (sorted) elements and the current set F, which initially is
the whole carrier. The head x of the list is removed from F iff F - {x} still contains a basis.
Unlike for the best-in greedy algorithm, termination does not depend on the oracle.\<close>

function WorstOutGreedy :: "('a, 'wrps) greedy_state \<Rightarrow> ('a, 'wrps) greedy_state" where
  "WorstOutGreedy state =
    (case (carrier_list state) of
      [] \<Rightarrow> state
    | (x # xs) \<Rightarrow>
        (if basis_superset_oracle x (result state) then
          WorstOutGreedy (state \<lparr>carrier_list := xs, result := wrapper_delete x (result state)\<rparr>)
        else
          WorstOutGreedy (state \<lparr>carrier_list := xs\<rparr>)
        )
    )"
  by pat_completeness auto

termination
  by (relation "measure call_measure") (auto simp: call_measure_def)

lemmas [code] = WorstOutGreedy.simps

declare WorstOutGreedy.simps[simp del]

definition "WorstOutGreedy_call_1_conds state =
    (case (carrier_list state) of
      [] \<Rightarrow> False
    | (x # xs) \<Rightarrow> basis_superset_oracle x (result state))"

lemma WorstOutGreedy_call_1_conds[call_cond_elims]:
  "WorstOutGreedy_call_1_conds state \<Longrightarrow>
   \<lbrakk>\<lbrakk>\<exists>x xs. carrier_list state = x # xs;
    basis_superset_oracle (hd (carrier_list state)) (result state)\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow>
   P"
  by (auto simp: WorstOutGreedy_call_1_conds_def split: list.splits)

definition "WorstOutGreedy_upd1 state = (
  let
    x = hd (carrier_list state);
    xs = tl (carrier_list state)
  in
    state \<lparr>carrier_list := xs, result := wrapper_delete x (result state)\<rparr>
  )"

definition "WorstOutGreedy_call_2_conds state =
    (case (carrier_list state) of
      [] \<Rightarrow> False
    | (x # xs) \<Rightarrow> \<not> basis_superset_oracle x (result state))"

lemma WorstOutGreedy_call_2_conds[call_cond_elims]:
  "WorstOutGreedy_call_2_conds state \<Longrightarrow>
   \<lbrakk>\<lbrakk>\<exists>x xs. carrier_list state = x # xs;
    \<not> basis_superset_oracle (hd (carrier_list state)) (result state)\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow>
   P"
  by (auto simp: WorstOutGreedy_call_2_conds_def split: list.splits)

definition "WorstOutGreedy_upd2 state = (
  let
    xs = tl (carrier_list state)
  in
    state \<lparr>carrier_list := xs\<rparr>
  )"

definition "WorstOutGreedy_ret_1_conds state = (carrier_list state = [])"

lemma WorstOutGreedy_ret_1_conds[call_cond_elims]:
  "WorstOutGreedy_ret_1_conds state \<Longrightarrow> \<lbrakk>\<lbrakk>carrier_list state = []\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: WorstOutGreedy_ret_1_conds_def)

lemma WorstOutGreedy_ret_1_condsI[call_cond_intros]:
  "\<lbrakk>carrier_list state = []\<rbrakk> \<Longrightarrow> WorstOutGreedy_ret_1_conds state"
  by (auto simp: WorstOutGreedy_ret_1_conds_def)

definition "WorstOutGreedy_ret1 state = state"

lemma WorstOutGreedy_cases:
  assumes "WorstOutGreedy_call_1_conds state \<Longrightarrow> P"
    "WorstOutGreedy_call_2_conds state \<Longrightarrow> P"
    "WorstOutGreedy_ret_1_conds state \<Longrightarrow> P"
  shows "P"
proof-
  have "WorstOutGreedy_call_1_conds state \<or> WorstOutGreedy_call_2_conds state \<or>
        WorstOutGreedy_ret_1_conds state"
    by (auto simp add: WorstOutGreedy_call_1_conds_def WorstOutGreedy_call_2_conds_def
        WorstOutGreedy_ret_1_conds_def split: list.split)
  then show ?thesis
    using assms
    by auto
qed

lemma WorstOutGreedy_simps:
  "WorstOutGreedy_call_1_conds state \<Longrightarrow>
     WorstOutGreedy state = WorstOutGreedy (WorstOutGreedy_upd1 state)"
  "WorstOutGreedy_call_2_conds state \<Longrightarrow>
     WorstOutGreedy state = WorstOutGreedy (WorstOutGreedy_upd2 state)"
  "WorstOutGreedy_ret_1_conds state \<Longrightarrow>
     WorstOutGreedy state = WorstOutGreedy_ret1 state"
  by (subst WorstOutGreedy.simps[of state],
      auto simp add: Let_def WorstOutGreedy_call_1_conds_def WorstOutGreedy_upd1_def
        WorstOutGreedy_call_2_conds_def WorstOutGreedy_upd2_def WorstOutGreedy_ret_1_conds_def
        WorstOutGreedy_ret1_def split: list.splits)+

lemma WorstOutGreedy_induct:
  fixes state :: "('a, 'wrps) greedy_state"
  assumes "\<And>state. \<lbrakk>WorstOutGreedy_call_1_conds state \<Longrightarrow> P (WorstOutGreedy_upd1 state);
    WorstOutGreedy_call_2_conds state \<Longrightarrow> P (WorstOutGreedy_upd2 state)\<rbrakk> \<Longrightarrow>
      P state"
  shows "P state"
proof(induction state rule: WorstOutGreedy.induct)
  case (1 state)
  show ?case
    by (rule assms)
      (use 1 in \<open>auto simp: WorstOutGreedy_call_1_conds_def WorstOutGreedy_upd1_def
        WorstOutGreedy_call_2_conds_def WorstOutGreedy_upd2_def split: list.splits\<close>)
qed

definition "initial_state c order =
  \<lparr>carrier_list = (sort_desc c order), result = wrapper_carrier\<rparr>"

lemmas [code] = initial_state_def

subsection \<open>Invariants\<close>

text \<open>We write F for the current set and E for the carrier. \<open>invar_3\<close> states that F contains all
elements that have not been processed yet. \<open>invar_4\<close> is the invariant from the book: for every j
up to the number of processed elements, E_j - F is a basis of E_j w.r.t. the dual independence
system, where E_j is the set of the first j elements in the sorted order.\<close>

definition "invar_1 state = wrapper_invar (result state)"

definition "invar_3 c order state =
  (to_set carrier - carrier_pref c order (num_iter c order state) \<subseteq> to_set (remove_wrapper (result state)) \<and>
   to_set (remove_wrapper (result state)) \<subseteq> to_set carrier)"

definition "invar_4 c order state =
  (\<forall>j \<in> {0..(num_iter c order state)}.
    indep_system.basis_in (dual (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn))
      (carrier_pref c order j) (pref c order (to_set carrier - to_set (remove_wrapper (result state))) j))"

context
  includes matroid.set.custom_automation
  assumes greedy_ax: greedy_axioms sort_desc_axioms "matroid.indep_system_axioms carrier indep_fn"
    and basis_superset_oracle_spec:
    "\<And>S x. \<lbrakk>wrapper_invar S; subseteq (remove_wrapper S) carrier; x \<in> to_set (remove_wrapper S);
      \<exists>B. indep_system.basis (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) B \<and>
        B \<subseteq> to_set (remove_wrapper S)\<rbrakk> \<Longrightarrow>
      basis_superset_oracle x S \<longleftrightarrow>
      (\<exists>B. indep_system.basis (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) B \<and>
        B \<subseteq> to_set (remove_wrapper S) - {x})"
  notes matroid_inv = matroid_inv[OF greedy_ax]
    and indep_system_axioms_abs = indep_system_axioms_abs[OF greedy_ax]
    and set_inv_carrier = set_inv_carrier[OF greedy_ax]
    and simps[simp] = simps[OF greedy_ax]
    and cost_nonnegative = cost_nonnegative[OF greedy_ax]
    and valid_solution_c_set_nonnegative = valid_solution_c_set_nonnegative[OF greedy_ax]
    and carrier_sorted_sorted_desc = carrier_sorted_sorted_desc[OF greedy_ax]
    and sort_desc_stable = sort_desc_stable[OF greedy_ax]
    and carrier_sorted_set = carrier_sorted_set[OF greedy_ax]
    and length_carrier_sorted = length_carrier_sorted[OF greedy_ax]
    and carrier_sorted_distinct = carrier_sorted_distinct[OF greedy_ax]
    and invar_2_props = invar_2_props[OF greedy_ax]
    and invar_2_intro = invar_2_intro[OF greedy_ax]
    and carrier_pref_subset = carrier_pref_subset[OF greedy_ax]
    and num_iter_tl = num_iter_tl[OF greedy_ax]
    and carrier_pref_tl = carrier_pref_tl[OF greedy_ax]
    and invar_2_tl = invar_2_tl[OF greedy_ax]
    and hd_in_carrier = hd_in_carrier[OF greedy_ax]
    and hd_not_in_carrier_pref = hd_not_in_carrier_pref[OF greedy_ax]
    and carrier_sorted_nth_nonneg = carrier_sorted_nth_nonneg[OF greedy_ax]
    and c_diff_nonneg = c_diff_nonneg[OF greedy_ax]
    and c_set_pref_sum = c_set_pref_sum[OF greedy_ax]
    and card_pref_complement = card_pref_complement[OF greedy_ax]
begin

lemma dual_indep_system_abs:
  "indep_system (matroid.carrier_abs carrier)
    (dual (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn))"
  using dual_indep_system[OF indep_system_axioms_abs] .

lemma invar_1_props[invar_props_elims]:
  "invar_1 state \<Longrightarrow> (\<lbrakk>wrapper_invar (result state)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_1_def)

lemma invar_1_intro[invar_props_intros]:
  "\<lbrakk>wrapper_invar (result state)\<rbrakk> \<Longrightarrow> invar_1 state"
  by (auto simp: invar_1_def)

lemma result_upd1:
  "invar_1 state \<Longrightarrow> to_set (remove_wrapper (result (WorstOutGreedy_upd1 state))) =
    to_set (remove_wrapper (result state)) - {hd (carrier_list state)}"
  by (auto simp: invar_1_def WorstOutGreedy_upd1_def Let_def wrapper_axioms(2,3))

lemma result_upd2:
  "result (WorstOutGreedy_upd2 state) = result state"
  by (simp add: WorstOutGreedy_upd2_def Let_def)

lemma invar_1_holds_upd1[invar_holds_intros]:
  "\<lbrakk>WorstOutGreedy_call_1_conds state; invar_1 state\<rbrakk> \<Longrightarrow> invar_1 (WorstOutGreedy_upd1 state)"
  by (auto simp: Let_def WorstOutGreedy_upd1_def wrapper_axioms(1)
      elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_1_holds_upd2[invar_holds_intros]:
  "\<lbrakk>WorstOutGreedy_call_2_conds state; invar_1 state\<rbrakk> \<Longrightarrow> invar_1 (WorstOutGreedy_upd2 state)"
  by (auto simp: result_upd2 elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_1_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>WorstOutGreedy_ret_1_conds state; invar_1 state\<rbrakk> \<Longrightarrow> invar_1 (WorstOutGreedy_ret1 state)"
  by (auto simp: WorstOutGreedy_ret1_def)

lemma invar_1_holds[invar_holds_intros]:
  fixes state :: "('a, 'wrps) greedy_state"
  assumes "invar_1 state"
  shows "invar_1 (WorstOutGreedy state)"
  using assms
proof(induction state rule: WorstOutGreedy_induct)
  case IH: (1 state)
  show ?case
    apply(rule WorstOutGreedy_cases[where state = state])
    by (auto intro!: IH invar_holds_intros simp: WorstOutGreedy_simps)
qed

lemma WorstOutGreedy_ret_1[ret_holds_intros]:
  "WorstOutGreedy_ret_1_conds state \<Longrightarrow> WorstOutGreedy_ret_1_conds (WorstOutGreedy_ret1 state)"
  by (auto simp: WorstOutGreedy_ret1_def)

lemma ret1_holds[ret_holds_intros]:
  fixes state :: "('a, 'wrps) greedy_state"
  shows "WorstOutGreedy_ret_1_conds (WorstOutGreedy state)"
proof(induction state rule: WorstOutGreedy_induct)
  case IH: (1 state)
  show ?case
    apply(rule WorstOutGreedy_cases[where state = state])
    by (auto intro: ret_holds_intros intro!: IH simp: WorstOutGreedy_simps)
qed

context
  fixes c :: "'a \<Rightarrow> rat" and order :: "'a list"
  assumes c_order: "nonnegative c" "valid_order order"
  notes cost_nonnegative = cost_nonnegative[OF c_order]
    and valid_solution_c_set_nonnegative = valid_solution_c_set_nonnegative[OF c_order]
    and carrier_sorted_sorted_desc = carrier_sorted_sorted_desc[OF c_order]
    and sort_desc_stable = sort_desc_stable[OF c_order]
    and carrier_sorted_set = carrier_sorted_set[OF c_order]
    and length_carrier_sorted = length_carrier_sorted[OF c_order]
    and carrier_sorted_distinct = carrier_sorted_distinct[OF c_order]
    and invar_2_props[invar_props_elims] = invar_2_props[OF c_order]
    and invar_2_intro[invar_props_intros] = invar_2_intro[OF c_order]
    and carrier_pref_subset = carrier_pref_subset[OF c_order]
    and num_iter_tl = num_iter_tl[OF c_order]
    and carrier_pref_tl = carrier_pref_tl[OF c_order]
    and invar_2_tl = invar_2_tl[OF c_order]
    and hd_in_carrier = hd_in_carrier[OF c_order]
    and hd_not_in_carrier_pref = hd_not_in_carrier_pref[OF c_order]
    and carrier_sorted_nth_nonneg = carrier_sorted_nth_nonneg[OF c_order]
    and c_diff_nonneg = c_diff_nonneg[OF c_order]
    and c_set_pref_sum = c_set_pref_sum[OF c_order]
    and card_pref_complement = card_pref_complement[OF c_order]
begin

lemma call_conds_carrier_list:
  "WorstOutGreedy_call_1_conds state \<Longrightarrow> carrier_list state \<noteq> []"
  "WorstOutGreedy_call_2_conds state \<Longrightarrow> carrier_list state \<noteq> []"
  "carrier_list (WorstOutGreedy_upd1 state) = tl (carrier_list state)"
  "carrier_list (WorstOutGreedy_upd2 state) = tl (carrier_list state)"
  by (auto simp: WorstOutGreedy_upd1_def WorstOutGreedy_upd2_def Let_def elim!: call_cond_elims)

lemma invar_2_holds_upd1[invar_holds_intros]:
  "\<lbrakk>WorstOutGreedy_call_1_conds state; invar_2 c order state\<rbrakk> \<Longrightarrow>
    invar_2 c order (WorstOutGreedy_upd1 state)"
  using invar_2_tl call_conds_carrier_list by blast

lemma invar_2_holds_upd2[invar_holds_intros]:
  "\<lbrakk>WorstOutGreedy_call_2_conds state; invar_2 c order state\<rbrakk> \<Longrightarrow>
    invar_2 c order (WorstOutGreedy_upd2 state)"
  using invar_2_tl call_conds_carrier_list by blast

lemma invar_2_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>WorstOutGreedy_ret_1_conds state; invar_2 c order state\<rbrakk> \<Longrightarrow>
    invar_2 c order (WorstOutGreedy_ret1 state)"
  by (auto simp: WorstOutGreedy_ret1_def)

lemma invar_2_holds[invar_holds_intros]:
  fixes state :: "('a, 'wrps) greedy_state"
  assumes "invar_2 c order state"
  shows "invar_2 c order (WorstOutGreedy state)"
  using assms
proof(induction state rule: WorstOutGreedy_induct)
  case IH: (1 state)
  show ?case
    apply(rule WorstOutGreedy_cases[where state = state])
    by (auto intro!: IH invar_holds_intros simp: WorstOutGreedy_simps)
qed

lemma invar_3_props[invar_props_elims]:
  "invar_3 c order state \<Longrightarrow>
    (\<lbrakk>to_set carrier - carrier_pref c order (num_iter c order state) \<subseteq> to_set (remove_wrapper (result state));
      to_set (remove_wrapper (result state)) \<subseteq> to_set carrier\<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
    P"
  by (auto simp: invar_3_def)

lemma invar_3_intro[invar_props_intros]:
  "\<lbrakk>to_set carrier - carrier_pref c order (num_iter c order state) \<subseteq> to_set (remove_wrapper (result state));
    to_set (remove_wrapper (result state)) \<subseteq> to_set carrier\<rbrakk> \<Longrightarrow> invar_3 c order state"
  by (auto simp: invar_3_def)

lemma invar_3_holds_upd1[invar_holds_intros]:
  assumes "WorstOutGreedy_call_1_conds state" "invar_1 state" "invar_2 c order state"
    "invar_3 c order state"
  shows "invar_3 c order (WorstOutGreedy_upd1 state)"
  using assms(4) result_upd1[OF assms(2)]
    carrier_pref_tl[OF assms(3) call_conds_carrier_list(1)[OF assms(1)] call_conds_carrier_list(3)]
  by (auto elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_3_holds_upd2[invar_holds_intros]:
  assumes "WorstOutGreedy_call_2_conds state" "invar_2 c order state" "invar_3 c order state"
  shows "invar_3 c order (WorstOutGreedy_upd2 state)"
  using assms(3) result_upd2[of state]
    carrier_pref_tl[OF assms(2) call_conds_carrier_list(2)[OF assms(1)] call_conds_carrier_list(4)]
  by (auto elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_3_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>WorstOutGreedy_ret_1_conds state; invar_3 c order state\<rbrakk> \<Longrightarrow>
    invar_3 c order (WorstOutGreedy_ret1 state)"
  by (auto simp: WorstOutGreedy_ret1_def)

lemma invar_3_holds[invar_holds_intros]:
  fixes state :: "('a, 'wrps) greedy_state"
  assumes "invar_1 state" "invar_2 c order state" "invar_3 c order state"
  shows "invar_3 c order (WorstOutGreedy state)"
  using assms
proof(induction state rule: WorstOutGreedy_induct)
  case IH: (1 state)
  show ?case
    apply(rule WorstOutGreedy_cases[where state = state])
    by (auto intro!: IH invar_holds_intros simp: WorstOutGreedy_simps)
qed

lemma invar_4_props[invar_props_elims]:
  "invar_4 c order state \<Longrightarrow>
    (\<lbrakk>\<And>j. j \<in> {0..(num_iter c order state)} \<Longrightarrow>
      indep_system.basis_in (dual (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn))
        (carrier_pref c order j) (pref c order (to_set carrier - to_set (remove_wrapper (result state))) j)\<rbrakk>
      \<Longrightarrow> P) \<Longrightarrow>
    P"
  by (auto simp: invar_4_def)

lemma invar_4_intro[invar_props_intros]:
  "\<lbrakk>\<And>j. j \<in> {0..(num_iter c order state)} \<Longrightarrow>
    indep_system.basis_in (dual (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn))
      (carrier_pref c order j) (pref c order (to_set carrier - to_set (remove_wrapper (result state))) j)\<rbrakk>
    \<Longrightarrow> invar_4 c order state"
  by (auto simp: invar_4_def)

text \<open>The set of removed elements is independent in the dual system, i.e.\ the current set contains a
basis. Hence, the precondition of the oracle holds and the oracle decides whether adding the head of the
list to the removed elements preserves independence in the dual system.\<close>

lemma removed_dual_basis_in:
  assumes "invar_3 c order state" "invar_4 c order state"
  shows "indep_system.basis_in (dual (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn))
    (carrier_pref c order (num_iter c order state))
    (to_set carrier - to_set (remove_wrapper (result state)))"
proof-
  have "pref c order (to_set carrier - to_set (remove_wrapper (result state))) (num_iter c order state) =
    to_set carrier - to_set (remove_wrapper (result state))"
    using assms(1) by (auto simp: pref_def elim!: invar_props_elims)
  then show ?thesis
    using assms(2) by (auto elim!: invar_props_elims)
qed

lemma oracle_iff_dual_indep:
  assumes "carrier_list state \<noteq> []" "invar_1 state" "invar_2 c order state" "invar_3 c order state"
    "invar_4 c order state"
  shows "basis_superset_oracle (hd (carrier_list state)) (result state) \<longleftrightarrow>
    dual (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn)
      (insert (hd (carrier_list state)) (to_set carrier - to_set (remove_wrapper (result state))))"
proof-
  let ?x = "hd (carrier_list state)"
  let ?F = "to_set (remove_wrapper (result state))"
  let ?E = "matroid.carrier_abs carrier"
  let ?I = "matroid.indep_abs indep_fn"
  have E: "?E = to_set carrier"
    by (simp add: matroid.carrier_abs_def)
  have F_sub: "?F \<subseteq> to_set carrier"
    and rest_sub: "to_set carrier - carrier_pref c order (num_iter c order state) \<subseteq> ?F"
    using assms(4) by (auto elim!: invar_props_elims)
  have x_E: "?x \<in> to_set carrier"
    using hd_in_carrier[OF assms(3,1)] .
  have x_F: "?x \<in> ?F"
    using x_E rest_sub hd_not_in_carrier_pref[OF assms(3,1) order.refl] by blast
  have set_inv_F: "set_inv (remove_wrapper (result state))"
    using assms(2) wrapper_axioms(2) by (auto elim!: invar_props_elims)
  have "subseteq (remove_wrapper (result state)) carrier"
    using F_sub set_inv_F set_inv_carrier by simp
  moreover have "dual ?E ?I (to_set carrier - ?F)"
    using indep_system.indep_in_indep[OF dual_indep_system_abs
        indep_system.basis_in_indep_in[OF dual_indep_system_abs _ removed_dual_basis_in[OF assms(4,5)]]]
      carrier_pref_subset E by simp
  then have "\<exists>B. indep_system.basis ?E ?I B \<and> B \<subseteq> ?F"
    using indep_system.dual_indep_iff_contains_basis[OF indep_system_axioms_abs] F_sub E
    by (simp add: Diff_Diff_Int inf.absorb2)
  ultimately have "basis_superset_oracle ?x (result state) \<longleftrightarrow>
    (\<exists>B. indep_system.basis ?E ?I B \<and> B \<subseteq> ?F - {?x})"
    using basis_superset_oracle_spec[OF _ _ x_F] assms(2) by (auto elim!: invar_props_elims)
  moreover have "?E - insert ?x (to_set carrier - ?F) = ?F - {?x}"
    using F_sub E by auto
  moreover have "insert ?x (to_set carrier - ?F) \<subseteq> ?E"
    using x_E E by auto
  ultimately show ?thesis
    using indep_system.dual_indep_iff_contains_basis[OF indep_system_axioms_abs] by simp
qed

lemma invar_4_holds_upd1[invar_holds_intros]:
  assumes "WorstOutGreedy_call_1_conds state" "invar_1 state" "invar_2 c order state"
    "invar_3 c order state" "invar_4 c order state"
  shows "invar_4 c order (WorstOutGreedy_upd1 state)"
proof(rule invar_props_intros, goal_cases)
  case (1 j)
  let ?x = "hd (carrier_list state)"
  let ?D = "to_set carrier - to_set (remove_wrapper (result state))"
  let ?k = "num_iter c order state"
  let ?DUAL = "dual (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn)"
  note L = call_conds_carrier_list(1)[OF assms(1)] call_conds_carrier_list(3)
  have D_upd: "to_set carrier - to_set (remove_wrapper (result (WorstOutGreedy_upd1 state))) = insert ?x ?D"
    using result_upd1[OF assms(2)] hd_in_carrier[OF assms(3) L(1)] by auto
  show ?case
  proof (cases "j \<le> ?k")
    case True
    have "pref c order (insert ?x ?D) j = pref c order ?D j"
      using hd_not_in_carrier_pref[OF assms(3) L(1) True] by (auto simp: pref_def)
    then show ?thesis
      using assms(5) True D_upd by (auto elim!: invar_props_elims)
  next
    case False
    then have j: "j = num_iter c order (WorstOutGreedy_upd1 state)"
      using 1 num_iter_tl[OF assms(3) L] by auto
    have E_j: "carrier_pref c order j = insert ?x (carrier_pref c order ?k)"
      using carrier_pref_tl[OF assms(3) L] j by simp
    have sub: "insert ?x (carrier_pref c order ?k) \<subseteq> matroid.carrier_abs carrier"
      using carrier_pref_subset hd_in_carrier[OF assms(3) L(1)] by (simp add: matroid.carrier_abs_def)
    have "?DUAL (insert ?x ?D)"
      using oracle_iff_dual_indep[OF L(1) assms(2-5)] assms(1) by (auto elim!: call_cond_elims)
    then have "indep_system.basis_in ?DUAL (carrier_pref c order j) (insert ?x ?D)"
      using indep_system.basis_in_preserved_indep[OF dual_indep_system_abs sub
          removed_dual_basis_in[OF assms(4,5)]] E_j by simp
    moreover have "pref c order (insert ?x ?D) j = insert ?x ?D"
      using assms(4) E_j by (auto simp: pref_def elim!: invar_props_elims)
    ultimately show ?thesis
      using D_upd by simp
  qed
qed

lemma invar_4_holds_upd2[invar_holds_intros]:
  assumes "WorstOutGreedy_call_2_conds state" "invar_1 state" "invar_2 c order state"
    "invar_3 c order state" "invar_4 c order state"
  shows "invar_4 c order (WorstOutGreedy_upd2 state)"
proof(rule invar_props_intros, goal_cases)
  case (1 j)
  let ?x = "hd (carrier_list state)"
  let ?D = "to_set carrier - to_set (remove_wrapper (result state))"
  let ?k = "num_iter c order state"
  let ?DUAL = "dual (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn)"
  note L = call_conds_carrier_list(2)[OF assms(1)] call_conds_carrier_list(4)
  show ?case
  proof (cases "j \<le> ?k")
    case True
    then show ?thesis
      using assms(5) by (auto simp: result_upd2 elim!: invar_props_elims)
  next
    case False
    then have j: "j = num_iter c order (WorstOutGreedy_upd2 state)"
      using 1 num_iter_tl[OF assms(3) L] by auto
    have E_j: "carrier_pref c order j = insert ?x (carrier_pref c order ?k)"
      using carrier_pref_tl[OF assms(3) L] j by simp
    have sub: "insert ?x (carrier_pref c order ?k) \<subseteq> matroid.carrier_abs carrier"
      using carrier_pref_subset hd_in_carrier[OF assms(3) L(1)] by (simp add: matroid.carrier_abs_def)
    have "\<not> ?DUAL (insert ?x ?D)"
      using oracle_iff_dual_indep[OF L(1) assms(2-5)] assms(1) by (auto elim!: call_cond_elims)
    then have "indep_system.basis_in ?DUAL (carrier_pref c order j) ?D"
      using indep_system.basis_in_preserved_not_indep[OF dual_indep_system_abs sub
          removed_dual_basis_in[OF assms(4,5)]] E_j by simp
    moreover have "pref c order ?D j = ?D"
      using assms(4) E_j by (auto simp: pref_def elim!: invar_props_elims)
    ultimately show ?thesis
      by (simp add: result_upd2)
  qed
qed

lemma invar_4_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>WorstOutGreedy_ret_1_conds state; invar_4 c order state\<rbrakk> \<Longrightarrow>
    invar_4 c order (WorstOutGreedy_ret1 state)"
  by (auto simp: WorstOutGreedy_ret1_def)

lemma invar_4_holds[invar_holds_intros]:
  fixes state :: "('a, 'wrps) greedy_state"
  assumes "invar_1 state" "invar_2 c order state" "invar_3 c order state" "invar_4 c order state"
  shows "invar_4 c order (WorstOutGreedy state)"
  using assms
proof(induction state rule: WorstOutGreedy_induct)
  case IH: (1 state)
  show ?case
    apply(rule WorstOutGreedy_cases[where state = state])
    by (auto intro!: IH invar_holds_intros simp: WorstOutGreedy_simps)
qed

lemma initial_state_props[invar_holds_intros]:
  "invar_1 (initial_state c order)" "invar_2 c order (initial_state c order)"
  "invar_3 c order (initial_state c order)" "invar_4 c order (initial_state c order)"
  by (auto simp: initial_state_def num_iter_def carrier_pref_def pref_def wrapper_axioms(4)[symmetric]
      wrapper_axioms(5)
      intro!: invar_props_intros indep_system.basis_inI[OF dual_indep_system_abs]
      indep_system.indep_inI[OF dual_indep_system_abs] indep_system.indep_empty[OF dual_indep_system_abs])

lemma final_state_props:
  "WorstOutGreedy_ret_1_conds (WorstOutGreedy (initial_state c order))"
  "invar_1 (WorstOutGreedy (initial_state c order))"
  "invar_3 c order (WorstOutGreedy (initial_state c order))"
  "invar_4 c order (WorstOutGreedy (initial_state c order))"
  by (auto intro: invar_holds_intros ret_holds_intros)

subsection \<open>Correctness\<close>

lemma num_iter_ret:
  "WorstOutGreedy_ret_1_conds state \<Longrightarrow> num_iter c order state = length (sort_desc c order)"
  by (auto simp: num_iter_def elim!: call_cond_elims)

text \<open>When the algorithm returns, the removed elements form a basis of the dual system.\<close>

lemma removed_dual_basis_ret:
  assumes "WorstOutGreedy_ret_1_conds state" "invar_3 c order state" "invar_4 c order state"
  shows "indep_system.basis (matroid.carrier_abs carrier)
    (dual (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn))
    (matroid.carrier_abs carrier - to_set (remove_wrapper (result state)))"
proof-
  have "carrier_pref c order (num_iter c order state) = to_set carrier"
    using num_iter_ret[OF assms(1)] carrier_sorted_set by (simp add: carrier_pref_def)
  then show ?thesis
    using removed_dual_basis_in[OF assms(2,3)]
      indep_system.basis_iff_basis_in[OF dual_indep_system_abs]
    by (simp add: matroid.carrier_abs_def)
qed

lemma WorstOutGreedy_correct_3_ret_1:
  assumes "WorstOutGreedy_ret_1_conds state" "invar_3 c order state" "invar_4 c order state"
  shows "indep_system.basis (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn)
    (to_set (remove_wrapper (result state)))"
proof-
  let ?E = "matroid.carrier_abs carrier"
  let ?F = "to_set (remove_wrapper (result state))"
  have F_sub: "?F \<subseteq> ?E"
    using assms(2) by (auto simp: matroid.carrier_abs_def elim!: invar_props_elims)
  from removed_dual_basis_ret[OF assms] dual_basis_complement[OF indep_system_axioms_abs, of "?E - ?F"]
  obtain B where B: "indep_system.basis ?E (matroid.indep_abs indep_fn) B" "?E - ?F = ?E - B"
    by auto
  moreover have "B \<subseteq> ?E"
    using indep_system.basis_subset_carrier[OF indep_system_axioms_abs B(1)] .
  ultimately have "?F = B"
    using F_sub by blast
  with B(1) show ?thesis
    by simp
qed

lemma WorstOutGreedy_correct_1_ret_1:
  assumes "WorstOutGreedy_ret_1_conds state" "invar_1 state" "invar_3 c order state"
    "invar_4 c order state"
  shows "wrapper_invar (result state) \<and> valid_solution (remove_wrapper (result state))"
proof-
  have inv: "wrapper_invar (result state)"
    using assms(2) by (auto elim!: invar_props_elims)
  then have set_inv: "set_inv (remove_wrapper (result state))"
    using wrapper_axioms(2) by blast
  have "matroid.indep_abs indep_fn (to_set (remove_wrapper (result state)))"
    using indep_system.basis_indep[OF indep_system_axioms_abs
        WorstOutGreedy_correct_3_ret_1[OF assms(1,3,4)]] .
  moreover have "to_set (remove_wrapper (result state)) \<subseteq> to_set carrier"
    using assms(3) by (auto elim!: invar_props_elims)
  ultimately show ?thesis
    using inv set_inv set_inv_carrier by (simp add: valid_solution_def)
qed

text \<open>Theorem 13.22 (upper bound). Let G_j and O_j be the elements of the greedy solution and of a
basis O among the first j elements E_j. Since E_j - G_j is a basis of E_j in the dual system and
E_j - O_j is independent in the dual system, we have
@{text "|G_j| <= |E_j| - rho*(E_j)"} and @{text "|O_j| >= |E_j| - r*(E_j)"}.\<close>

lemma WorstOutGreedy_correct_2_ret_1:
  assumes "WorstOutGreedy_ret_1_conds state" "invar_3 c order state" "invar_4 c order state"
    "indep_system.basis (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) (to_set X)"
  shows "c_set c (to_set (remove_wrapper (result state))) \<le>
    indep_system.worst_out_ratio (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) *
    c_set c (to_set X)"
proof-
  let ?E = "matroid.carrier_abs carrier"
  let ?I = "matroid.indep_abs indep_fn"
  let ?DUAL = "dual ?E ?I"
  let ?r = "indep_system.worst_out_ratio ?E ?I"
  let ?n = "length (sort_desc c order)"
  let ?d = "c_diff c order ?n"
  let ?G = "to_set (remove_wrapper (result state))"
  let ?O = "to_set X"
  have E: "?E = to_set carrier"
    by (simp add: matroid.carrier_abs_def)
  have G_sub: "?G \<subseteq> to_set carrier"
    using assms(2) by (auto elim!: invar_props_elims)
  have O_sub_E: "?O \<subseteq> ?E"
    using indep_system.basis_subset_carrier[OF indep_system_axioms_abs assms(4)] .
  then have O_sub: "?O \<subseteq> to_set carrier"
    using E by simp
  have E_j_sub: "\<And>j. carrier_pref c order j \<subseteq> ?E"
    using carrier_pref_subset E by simp
  have r_nonneg: "?r \<ge> 0"
    using indep_system.worst_out_ratio_geq_1[OF indep_system_axioms_abs] by simp
  have dual_O: "?DUAL (to_set carrier - ?O)"
    unfolding E[symmetric] indep_system.dual_indep_iff_contains_basis[OF indep_system_axioms_abs]
    using assms(4) O_sub_E by blast

  have G_j: "rat_of_nat (card (pref c order ?G j)) \<le> ?r * rat_of_nat (card (pref c order ?O j))"
    if j: "j \<in> {1..?n}" for j
  proof-
    let ?Ej = "carrier_pref c order j"
    have "indep_system.basis_in ?DUAL ?Ej (pref c order (to_set carrier - ?G) j)"
      using assms(3) num_iter_ret[OF assms(1)] j by (auto elim!: invar_props_elims)
    then have "indep_system.lower_rank_of ?DUAL ?Ej \<le> card (pref c order (to_set carrier - ?G) j)"
      using indep_system.lower_rank_of_leq_card_basis_in[OF dual_indep_system_abs E_j_sub] by blast
    then have G_le: "card (pref c order ?G j) \<le> card ?Ej - indep_system.lower_rank_of ?DUAL ?Ej"
      using card_pref_complement[of ?G j] by arith
    have "pref c order (to_set carrier - ?O) j \<subseteq> to_set carrier - ?O"
      by (simp add: pref_def)
    then have "indep_system.indep_in ?DUAL ?Ej (pref c order (to_set carrier - ?O) j)"
      using indep_system.indep_subset[OF dual_indep_system_abs dual_O]
      unfolding indep_system.indep_in_def[OF dual_indep_system_abs] by (simp add: pref_def)
    then have "card (pref c order (to_set carrier - ?O) j) \<le> indep_system.rank ?DUAL ?Ej"
      using indep_system.rank_geq_card_indep_in[OF dual_indep_system_abs E_j_sub] by blast
    then have O_ge: "card ?Ej - indep_system.rank ?DUAL ?Ej \<le> card (pref c order ?O j)"
      using card_pref_complement[of ?O j] by arith
    have "rat_of_nat (card (pref c order ?G j)) \<le>
      rat_of_nat (card ?Ej - indep_system.lower_rank_of ?DUAL ?Ej)"
      using G_le by simp
    also have "\<dots> \<le> ?r * rat_of_nat (card ?Ej - indep_system.rank ?DUAL ?Ej)"
      using indep_system.card_minus_dual_lower_rank_leq_ratio_prod[OF indep_system_axioms_abs E_j_sub] .
    also have "\<dots> \<le> ?r * rat_of_nat (card (pref c order ?O j))"
      using O_ge r_nonneg by (simp add: mult_left_mono)
    finally show ?thesis .
  qed

  have "c_set c ?G = (\<Sum>j = 1..?n. rat_of_nat (card (pref c order ?G j)) * ?d j)"
    using c_set_pref_sum[OF G_sub] .
  also have "\<dots> \<le> (\<Sum>j = 1..?n. ?r * rat_of_nat (card (pref c order ?O j)) * ?d j)"
    using G_j c_diff_nonneg by (intro sum_mono mult_right_mono) auto
  also have "\<dots> = ?r * (\<Sum>j = 1..?n. rat_of_nat (card (pref c order ?O j)) * ?d j)"
    by (simp add: sum_distrib_left mult.assoc)
  also have "\<dots> = ?r * c_set c ?O"
    using c_set_pref_sum[OF O_sub] by simp
  finally show ?thesis .
qed

lemma WorstOutGreedy_correct_1:
  "wrapper_invar (result (WorstOutGreedy (initial_state c order))) \<and>
   valid_solution (remove_wrapper (result (WorstOutGreedy (initial_state c order))))"
  using WorstOutGreedy_correct_1_ret_1[OF final_state_props] .

lemma WorstOutGreedy_correct_2:
  "indep_system.basis (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) (to_set X) \<Longrightarrow>
   c_set c (to_set (remove_wrapper (result (WorstOutGreedy (initial_state c order))))) \<le>
   indep_system.worst_out_ratio (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) *
   c_set c (to_set X)"
  using WorstOutGreedy_correct_2_ret_1[OF final_state_props(1,3,4)] .

lemma WorstOutGreedy_correct_3:
  "indep_system.basis (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn)
    (to_set (remove_wrapper (result (WorstOutGreedy (initial_state c order)))))"
  using WorstOutGreedy_correct_3_ret_1[OF final_state_props(1,3,4)] .

end

subsection \<open>Tightness of the Bound and Matroids\<close>

text \<open>Theorem 13.22 is tight. Choose X0 for which the maximum in the definition of
\<open>worst_out_ratio\<close> is attained, and bases B1 and B2 of X0 in the dual system of minimum and maximum
cardinality. Take costs 1 on X0 and 0 elsewhere and an order that starts with B1 followed by the
rest of X0. Then the algorithm removes exactly B1 from X0. The complement of a dual basis
extending B2 is a basis whose costs are @{text "|X0| - |B2|"}.\<close>

lemma WorstOutGreedy_bound_tight_aux:
  "\<exists>c order X n m. nonnegative c \<and> valid_order order \<and> valid_solution X \<and>
    indep_system.basis (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) (to_set X) \<and>
    c_set c (to_set (remove_wrapper (result (WorstOutGreedy (initial_state c order))))) = rat_of_nat n \<and>
    c_set c (to_set X) = rat_of_nat m \<and> (0 < m \<or> n = m) \<and>
    indep_system.worst_out_ratio (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) =
      Frac (int n) (int m)"
proof-
  let ?E = "matroid.carrier_abs carrier"
  let ?I = "matroid.indep_abs indep_fn"
  interpret dual: indep_system ?E "dual ?E ?I"
    using dual_indep_system_abs .
  have E: "?E = to_set carrier"
    by (simp add: matroid.carrier_abs_def)
  have fin_E: "finite ?E"
    using dual.carrier_finite .

  obtain X0 where X0: "X0 \<subseteq> ?E"
    "Frac (int (card X0 - dual.lower_rank_of X0)) (int (card X0 - dual.rank X0)) =
      indep_system.worst_out_ratio ?E ?I"
    using indep_system.worst_out_ratio_attained[OF indep_system_axioms_abs] by blast
  let ?cards = "{card B | B. dual.basis_in X0 B}"
  have cards_ne: "?cards \<noteq> {}"
    using dual.basis_in_ex[OF X0(1)] by blast
  have cards_fin: "finite ?cards"
    using dual.collect_basis_in_finite[OF X0(1)] by simp
  have "\<exists>B1. dual.basis_in X0 B1 \<and> card B1 = dual.lower_rank_of X0"
    using Min_in[OF cards_fin cards_ne] unfolding dual.lower_rank_of_def by auto
  then obtain B1 where B1: "dual.basis_in X0 B1" "card B1 = dual.lower_rank_of X0"
    by blast
  have "\<exists>B2. dual.basis_in X0 B2 \<and> card B2 = dual.upper_rank_of X0"
    using Max_in[OF cards_fin cards_ne] unfolding dual.upper_rank_of_def by auto
  then obtain B2 where B2: "dual.basis_in X0 B2" "card B2 = dual.rank X0"
    using dual.upper_rank_equiv_rank[OF X0(1)] by auto
  have B1_X0: "B1 \<subseteq> X0"
    using dual.basis_in_subset_carrier[OF X0(1) B1(1)] .
  have B2_X0: "B2 \<subseteq> X0"
    using dual.basis_in_subset_carrier[OF X0(1) B2(1)] .
  have fin_X0: "finite X0"
    using X0(1) fin_E finite_subset by blast
  have fin_B1: "finite B1"
    using B1_X0 fin_X0 finite_subset by blast
  have fin_B2: "finite B2"
    using B2_X0 fin_X0 finite_subset by blast

  let ?l_B1 = "sorted_list_of_set B1"
  let ?l_X0_B1 = "sorted_list_of_set (X0 - B1)"
  let ?l_X0 = "?l_B1 @ ?l_X0_B1"
  let ?l_rest = "sorted_list_of_set (?E - X0)"
  let ?order = "?l_X0 @ ?l_rest"
  let ?c = "\<lambda>x. if x \<in> X0 then (1::rat) else 0"

  have set_l_X0: "set ?l_X0 = X0"
    using fin_B1 fin_X0 B1_X0 by auto
  have set_l_rest: "set ?l_rest = ?E - X0"
    using fin_E by simp
  have len_l_X0: "length ?l_X0 = card X0"
    using card_mono[OF fin_X0 B1_X0] card_Diff_subset[OF fin_B1 B1_X0] by simp
  have distinct_order: "distinct ?order"
    using fin_B1 fin_X0 fin_E B1_X0 by auto
  have set_order: "set ?order = to_set carrier"
    using set_l_X0 set_l_rest X0(1) E by auto
  have valid: "valid_order ?order"
    unfolding valid_order_def using set_order distinct_card[OF distinct_order] set_inv_carrier
    by simp
  have nonneg: "nonnegative ?c"
    by (simp add: nonnegative_def)

  text \<open>The sorted carrier coincides with the chosen order.\<close>
  have filter1: "filter (\<lambda>y. ?c y = 1) ?order = ?l_X0"
  proof-
    have "filter (\<lambda>y. ?c y = 1) ?l_X0 = ?l_X0"
      unfolding filter_id_conv using set_l_X0 by auto
    moreover have "filter (\<lambda>y. ?c y = 1) ?l_rest = []"
      unfolding filter_empty_conv using set_l_rest by auto
    ultimately show ?thesis
      by (simp only: filter_append[of _ ?l_X0 ?l_rest] append_Nil2)
  qed
  have filter0: "filter (\<lambda>y. ?c y = 0) ?order = ?l_rest"
  proof-
    have "filter (\<lambda>y. ?c y = 0) ?l_X0 = []"
      unfolding filter_empty_conv using set_l_X0 by auto
    moreover have "filter (\<lambda>y. ?c y = 0) ?l_rest = ?l_rest"
      unfolding filter_id_conv using set_l_rest by auto
    ultimately show ?thesis
      by (simp only: filter_append[of _ ?l_X0 ?l_rest] append_Nil)
  qed
  have c01: "\<forall>x. ?c x = 1 \<or> ?c x = 0"
    by simp
  have c_ne1: "(\<lambda>y. ?c y \<noteq> 1) = (\<lambda>y. ?c y = 0)"
    by auto
  have "sort_desc ?c ?order = filter (\<lambda>y. ?c y = 1) (sort_desc ?c ?order) @
    filter (\<lambda>y. ?c y \<noteq> 1) (sort_desc ?c ?order)"
    using sorted_aux5[OF carrier_sorted_distinct[OF nonneg valid]
        carrier_sorted_sorted_desc[OF nonneg valid] c01 refl length_filter_le] .
  then have sorted_eq: "sort_desc ?c ?order = ?order"
    unfolding c_ne1 sort_desc_stable[OF nonneg valid] filter1 filter0 .

  text \<open>The algorithm removes exactly B1 from X0.\<close>
  let ?st = "WorstOutGreedy (initial_state ?c ?order)"
  let ?G = "to_set (remove_wrapper (result ?st))"
  let ?D = "to_set carrier - ?G"
  note final = final_state_props[OF nonneg valid]
  have G_sub: "?G \<subseteq> to_set carrier"
    using final(3) unfolding invar_3_def by blast
  have n: "num_iter ?c ?order ?st = length (sort_desc ?c ?order)"
    using num_iter_ret[OF nonneg valid final(1)] .
  have basis_in_j: "dual.basis_in (carrier_pref ?c ?order j) (?D \<inter> carrier_pref ?c ?order j)"
    if "j \<le> length ?order" for j
    using final(4) n sorted_eq that unfolding invar_4_def pref_def by auto
  have E_B1: "carrier_pref ?c ?order (card B1) = B1"
    unfolding carrier_pref_def sorted_eq using fin_B1 by simp
  have E_X0: "carrier_pref ?c ?order (card X0) = X0"
  proof-
    have "take (length ?l_X0) ?order = ?l_X0"
      by simp
    then show ?thesis
      using set_l_X0 unfolding carrier_pref_def sorted_eq len_l_X0[symmetric] by metis
  qed
  have j_B1: "card B1 \<le> length ?order" and j_X0: "card X0 \<le> length ?order"
    using len_l_X0 card_mono[OF fin_X0 B1_X0] by auto
  have B1_E: "B1 \<subseteq> ?E"
    using B1_X0 X0(1) by blast
  have B1_indep: "dual ?E ?I B1"
    using dual.indep_in_indep[OF dual.basis_in_indep_in[OF X0(1) B1(1)]] .
  have B1_B1: "dual.basis_in B1 B1"
    by (rule dual.basis_inI[OF B1_E]) (auto simp: dual.indep_in_def B1_indep)
  have "dual.basis_in B1 (?D \<inter> B1)"
    using basis_in_j[OF j_B1] E_B1 by simp
  then have "?D \<inter> B1 = B1"
    using dual.basis_in_subset_eq[OF B1_E _ B1_B1 Int_lower2] by blast
  then have B1_D: "B1 \<subseteq> ?D \<inter> X0"
    using B1_X0 by blast
  have "dual.basis_in X0 (?D \<inter> X0)"
    using basis_in_j[OF j_X0] E_X0 by simp
  then have D_X0: "B1 = ?D \<inter> X0"
    using dual.basis_in_subset_eq[OF X0(1) B1(1) _ B1_D] by blast
  have G_X0: "?G \<inter> X0 = X0 - B1"
    using D_X0 G_sub X0(1) E by blast
  have fin_G: "finite ?G"
    using G_sub fin_E E finite_subset by metis
  have "c_set ?c ?G = rat_of_nat (card (?G \<inter> X0))"
    unfolding c_set_def using sum.inter_restrict[OF fin_G, where B = X0 and g = "\<lambda>_. (1::rat)"]
    by simp
  then have c_G: "c_set ?c ?G = rat_of_nat (card X0 - card B1)"
    using G_X0 card_Diff_subset[OF fin_B1 B1_X0] by simp

  text \<open>A basis of costs @{text "|X0| - |B2|"}.\<close>
  obtain B' where B': "dual.basis B'" "B' \<inter> X0 = B2"
    using dual.basis_in_extend_to_basis[OF X0(1) B2(1)] by blast
  have B'_E: "B' \<subseteq> ?E"
    using dual.basis_subset_carrier[OF B'(1)] .
  obtain Bo where Bo: "indep_system.basis ?E ?I Bo" "B' = ?E - Bo"
    using dual_basis_complement[OF indep_system_axioms_abs B'_E] B'(1) by blast
  have Bo_E: "Bo \<subseteq> ?E"
    using indep_system.basis_subset_carrier[OF indep_system_axioms_abs Bo(1)] .
  have Bo_X0: "Bo \<inter> X0 = X0 - B2"
    using Bo(2) B'(2) Bo_E X0(1) by blast
  have fin_Bo: "finite Bo"
    using Bo_E fin_E finite_subset by blast
  let ?X = "matroid.from_set Bo"
  have to_set_X: "to_set ?X = Bo"
    using matroid.from_set_correct[OF fin_Bo] .
  have valid_X: "valid_solution ?X"
    using matroid.invar_from_set[of Bo] to_set_X Bo_E E set_inv_carrier
      indep_system.basis_indep[OF indep_system_axioms_abs Bo(1)]
    by (simp add: valid_solution_def)
  have "c_set ?c Bo = rat_of_nat (card (Bo \<inter> X0))"
    unfolding c_set_def using sum.inter_restrict[OF fin_Bo, where B = X0 and g = "\<lambda>_. (1::rat)"]
    by simp
  then have c_X: "c_set ?c (to_set ?X) = rat_of_nat (card X0 - card B2)"
    using Bo_X0 card_Diff_subset[OF fin_B2 B2_X0] to_set_X by simp

  have m_cases: "0 < card X0 - card B2 \<or> card X0 - card B1 = card X0 - card B2"
  proof (cases "card X0 - card B2 = 0")
    case True
    have "dual.rank X0 \<le> card X0"
      using dual.upper_rank_of_le[OF X0(1)] dual.upper_rank_equiv_rank[OF X0(1)] by simp
    with True B2(2) have "dual.rank X0 = card X0"
      by simp
    with dual.rank_eq_card_imp_lower_rank_eq_card[OF X0(1)] B1(2) True show ?thesis
      by simp
  qed simp
  have "nonnegative ?c \<and> valid_order ?order \<and> valid_solution ?X \<and>
    indep_system.basis ?E ?I (to_set ?X) \<and>
    c_set ?c ?G = rat_of_nat (card X0 - card B1) \<and>
    c_set ?c (to_set ?X) = rat_of_nat (card X0 - card B2) \<and>
    (0 < card X0 - card B2 \<or> card X0 - card B1 = card X0 - card B2) \<and>
    indep_system.worst_out_ratio ?E ?I = Frac (int (card X0 - card B1)) (int (card X0 - card B2))"
    using nonneg valid valid_X Bo(1) to_set_X c_G c_X m_cases X0(2) B1(2) B2(2) by simp
  then show ?thesis
    by blast
qed

lemma WorstOutGreedy_bound_tight:
  "\<exists>c order X. nonnegative c \<and> valid_order order \<and> valid_solution X \<and>
    indep_system.basis (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) (to_set X) \<and>
    c_set c (to_set (remove_wrapper (result (WorstOutGreedy (initial_state c order))))) =
    indep_system.worst_out_ratio (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) *
    c_set c (to_set X)"
proof-
  from WorstOutGreedy_bound_tight_aux obtain c order X n m where
    t: "nonnegative c" "valid_order order" "valid_solution X"
    "indep_system.basis (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) (to_set X)"
    "c_set c (to_set (remove_wrapper (result (WorstOutGreedy (initial_state c order))))) = rat_of_nat n"
    "c_set c (to_set X) = rat_of_nat m" "0 < m \<or> n = m"
    "indep_system.worst_out_ratio (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) =
      Frac (int n) (int m)"
    by blast
  then have "c_set c (to_set (remove_wrapper (result (WorstOutGreedy (initial_state c order))))) =
    indep_system.worst_out_ratio (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) *
    c_set c (to_set X)"
    using Frac_of_int_quotient_mult[OF t(7,8)] by simp
  with t(1-4) show ?thesis
    by blast
qed

text \<open>The worst-out greedy algorithm finds a basis of minimum costs for all nonnegative cost
functions iff the independence system is a matroid.\<close>

lemma WorstOutGreedy_matroid_iff_opt:
  "matroid.matroid_axioms carrier indep_fn \<longleftrightarrow>
    (\<forall>c. nonnegative c \<longrightarrow> (\<forall>order. valid_order order \<longrightarrow> (\<forall>X.
      indep_system.basis (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) (to_set X) \<longrightarrow>
      c_set c (to_set (remove_wrapper (result (WorstOutGreedy (initial_state c order))))) \<le>
      c_set c (to_set X))))"
proof-
  let ?r = "indep_system.worst_out_ratio (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn)"
  have "(\<forall>c. nonnegative c \<longrightarrow> (\<forall>order. valid_order order \<longrightarrow> (\<forall>X.
      indep_system.basis (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) (to_set X) \<longrightarrow>
      c_set c (to_set (remove_wrapper (result (WorstOutGreedy (initial_state c order))))) \<le>
      c_set c (to_set X)))) \<longleftrightarrow> ?r = 1"
  proof
    assume opt: "\<forall>c. nonnegative c \<longrightarrow> (\<forall>order. valid_order order \<longrightarrow> (\<forall>X.
      indep_system.basis (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) (to_set X) \<longrightarrow>
      c_set c (to_set (remove_wrapper (result (WorstOutGreedy (initial_state c order))))) \<le>
      c_set c (to_set X)))"
    show "?r = 1"
    proof (rule ccontr)
      assume "?r \<noteq> 1"
      with indep_system.worst_out_ratio_geq_1[OF indep_system_axioms_abs]
      have r_gt: "?r > 1"
        by simp
      from WorstOutGreedy_bound_tight_aux obtain c order X n m where
        t: "nonnegative c" "valid_order order" "valid_solution X"
        "indep_system.basis (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) (to_set X)"
        "c_set c (to_set (remove_wrapper (result (WorstOutGreedy (initial_state c order))))) = rat_of_nat n"
        "c_set c (to_set X) = rat_of_nat m" "0 < m \<or> n = m"
        "?r = Frac (int n) (int m)"
        by blast
      have "0 < m"
        using t(7,8) \<open>?r \<noteq> 1\<close> by (auto simp: Frac_def)
      then have pos: "c_set c (to_set X) > 0"
        using t(6) by simp
      have "c_set c (to_set (remove_wrapper (result (WorstOutGreedy (initial_state c order))))) =
        ?r * c_set c (to_set X)"
        using Frac_of_int_quotient_mult[OF t(7,8)] t(5,6) by simp
      moreover have "c_set c (to_set X) < ?r * c_set c (to_set X)"
        using mult_strict_right_mono[OF r_gt pos] by simp
      moreover have "c_set c (to_set (remove_wrapper (result (WorstOutGreedy (initial_state c order))))) \<le>
        c_set c (to_set X)"
        using opt t(1,2,4) by blast
      ultimately show False
        by simp
    qed
  next
    assume r1: "?r = 1"
    show "\<forall>c. nonnegative c \<longrightarrow> (\<forall>order. valid_order order \<longrightarrow> (\<forall>X.
      indep_system.basis (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) (to_set X) \<longrightarrow>
      c_set c (to_set (remove_wrapper (result (WorstOutGreedy (initial_state c order))))) \<le>
      c_set c (to_set X)))"
      using WorstOutGreedy_correct_2 r1 by simp
  qed
  moreover have "?r = 1 \<longleftrightarrow> matroid (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn)"
    using indep_system.worst_out_ratio_eq_1_iff_matroid[OF indep_system_axioms_abs] .
  ultimately show ?thesis
    using matroid.matroid_abs_equiv[OF matroid_inv] by simp
qed

end

end

section \<open>Using the Worst-Out-Greedy Algorithm\<close>

text \<open>A client provides the independence system as a predicate on sets, the wrapper operations and a
weak basis superset oracle whose specification is stated in terms of the abstract independence
system. The correctness results are exported in terms of the abstract independence system.\<close>

locale Use_Worst_Out_Thms
  = Use_Greedy_Common +
  fixes sort_desc :: "('b \<Rightarrow> rat) \<Rightarrow> 'b list \<Rightarrow> 'b list"
    and basis_superset_oracle :: "'b \<Rightarrow> 'wrps \<Rightarrow> bool"
    and remove_wrapper :: "'wrps \<Rightarrow> 'a"
    and wrapper_invar :: "'wrps \<Rightarrow> bool"
    and wrapper_delete :: "'b \<Rightarrow> 'wrps \<Rightarrow> 'wrps"
    and wrapper_carrier :: "'wrps"
  assumes sort_desc_axioms: "sort_desc_axioms' sort_desc"
  assumes wrapper_axioms:
    "\<And>S x. wrapper_invar S \<Longrightarrow> wrapper_invar (wrapper_delete x S)"
    "\<And>S. wrapper_invar S \<Longrightarrow> set_inv (remove_wrapper S)"
    "\<And>S x. wrapper_invar S \<Longrightarrow> remove_wrapper (wrapper_delete x S) = set_delete x (remove_wrapper S)"
    "input_G = remove_wrapper wrapper_carrier"
    "wrapper_invar wrapper_carrier"
  assumes basis_superset_oracle_spec:
    "\<And>S x. \<lbrakk>wrapper_invar S; to_set (remove_wrapper S) \<subseteq> to_set input_G;
      x \<in> to_set (remove_wrapper S);
      \<exists>B. indep_system.basis (to_set input_G) indep_predicate B \<and> B \<subseteq> to_set (remove_wrapper S)\<rbrakk> \<Longrightarrow>
      basis_superset_oracle x S \<longleftrightarrow>
      (\<exists>B. indep_system.basis (to_set input_G) indep_predicate B \<and> B \<subseteq> to_set (remove_wrapper S) - {x})"
begin

interpretation greedy: Worst_Out_Greedy set_insert set_delete set_isin set_inv union inter
  diff cardinality to_set set_empty input_G "(\<lambda>Z. indep_predicate (to_set Z))" sort_desc
  basis_superset_oracle remove_wrapper wrapper_invar wrapper_delete wrapper_carrier
  by (auto intro!: Worst_Out_Greedy.intro Greedy_Common.intro Matroid_Specs.intro
      Worst_Out_Greedy_axioms.intro simp add: Indep_System_Specs_axioms wrapper_axioms)

lemma nonnegative: "greedy.nonnegative c"
  by (simp add: G_good greedy.nonnegative_def non_negative_c set.set_isin)

lemma valid_order: "greedy.valid_order order"
  by (simp add: greedy.valid_order_def order_is_G size_G_length_order)

lemma worstoutgreedy_axioms: "greedy.greedy_axioms"
  unfolding greedy.greedy_axioms_def finite_sets_def
  by (auto simp add: invar_input_G finite_sets)

lemma greedy_sort_desc_axioms: "greedy.sort_desc_axioms"
  using sort_desc_axioms
  by (auto simp add: greedy.sort_desc_axioms_def)

lemma basis_superset_oracle_spec_abs:
  "\<lbrakk>wrapper_invar S; greedy.subseteq (remove_wrapper S) input_G; x \<in> to_set (remove_wrapper S);
    \<exists>B. indep_system.basis (carrier_abs input_G) (indep_abs (\<lambda>Z. indep_predicate (to_set Z))) B \<and>
      B \<subseteq> to_set (remove_wrapper S)\<rbrakk> \<Longrightarrow>
    basis_superset_oracle x S \<longleftrightarrow>
    (\<exists>B. indep_system.basis (carrier_abs input_G) (indep_abs (\<lambda>Z. indep_predicate (to_set Z))) B \<and>
      B \<subseteq> to_set (remove_wrapper S) - {x})"
  using basis_superset_oracle_spec[of S x] wrapper_axioms(2)[of S]
  by (simp add: indep_abs_id_indep_predicate carrier_abs_def G_good set.set_subseteq)

lemmas WorstOutGreedy_correct_1 = greedy.WorstOutGreedy_correct_1[OF worstoutgreedy_axioms
    greedy_sort_desc_axioms indep_system_axioms_input_G basis_superset_oracle_spec_abs
    nonnegative valid_order]

lemmas WorstOutGreedy_correct_2 = greedy.WorstOutGreedy_correct_2[OF worstoutgreedy_axioms
    greedy_sort_desc_axioms indep_system_axioms_input_G basis_superset_oracle_spec_abs
    nonnegative valid_order]

lemmas WorstOutGreedy_correct_3 = greedy.WorstOutGreedy_correct_3[OF worstoutgreedy_axioms
    greedy_sort_desc_axioms indep_system_axioms_input_G basis_superset_oracle_spec_abs
    nonnegative valid_order]

lemma algo_result_invar:
  "wrapper_invar (result (greedy.WorstOutGreedy (greedy.initial_state c order))) \<and>
   set_inv (remove_wrapper (result (greedy.WorstOutGreedy (greedy.initial_state c order))))"
  using WorstOutGreedy_correct_1 by (simp add: greedy.valid_solution_def)

lemma algo_gives_basis:
  "indep_system.basis (to_set input_G) indep_predicate
    (to_set (remove_wrapper (result (greedy.WorstOutGreedy (greedy.initial_state c order)))))"
  using WorstOutGreedy_correct_3 by (simp add: indep_abs_id_indep_predicate carrier_abs_def)

lemma basis_greedy_correct:
  assumes "indep_system.basis (to_set input_G) indep_predicate X"
  shows "sum c (to_set (remove_wrapper (result (greedy.WorstOutGreedy (greedy.initial_state c order))))) \<le>
    indep_system.worst_out_ratio (to_set input_G) indep_predicate * sum c X"
proof-
  have X: "to_set (from_set X) = X"
    using indep_to_set_from_set_inv indep_system.basis_indep[OF indep_system assms] .
  show ?thesis
    using WorstOutGreedy_correct_2[of "from_set X"] assms
    by (simp add: X indep_abs_id_indep_predicate carrier_abs_def greedy.c_set_def)
qed

end

end
