(*
  Author: Adem Rimpapa
*)

theory BestInGreedy_stablesort
  imports BestInGreedy_base
begin

provenance human

section \<open>The Best-In-Greedy Algorithm with a Stable Sorting Function\<close>

definition "sort_desc_axioms_stable sort_desc =(
  sort_desc_axioms' sort_desc \<and>
  (\<forall>c order k. filter (\<lambda>y. c y = k) (sort_desc c order) = filter (\<lambda>y. c y = k) order))"
abbreviation "sort_desc_axioms_stable' == sort_desc_axioms_stable"
hide_const sort_desc_axioms_stable

locale BestInGreedy_stablesort = BestInGreedy_base
  where set_empty = "set_empty :: 's" 
    and sort_desc = "sort_desc :: ('a::linorder \<Rightarrow> rat) \<Rightarrow> 'a list \<Rightarrow> 'a list"
  for set_empty sort_desc
begin

abbreviation "sort_desc_axioms_stable \<equiv> sort_desc_axioms_stable' sort_desc"

lemma sort_desc_axioms_stable_def: "sort_desc_axioms_stable =(
  sort_desc_axioms \<and>
  (\<forall>c order k. filter (\<lambda>y. c y = k) (sort_desc c order) = filter (\<lambda>y. c y = k) order))"
  using sort_desc_axioms_stable_def by blast

context
  includes matroid.set.custom_automation
  assumes BestInGreedy_base_axioms sort_desc_axioms_stable "matroid.indep_system_axioms carrier indep_fn"
begin

lemma sort_desc_axioms: "sort_desc_axioms"
  using \<open>sort_desc_axioms_stable\<close> by (simp add: sort_desc_axioms_stable_def)

(* The results of BestInGreedy_base, instantiated with the assumptions of this context. *)
lemmas base_assms = 
  \<open>BestInGreedy_base_axioms\<close> sort_desc_axioms \<open>matroid.indep_system_axioms carrier indep_fn\<close>

lemmas matroid_inv = matroid_inv[OF base_assms]
lemmas indep_system_axioms_abs = indep_system_axioms_abs[OF base_assms]
lemmas set_inv_carrier = set_inv_carrier[OF base_assms]
lemmas simps[simp] = matroid.indep_abs_equiv[OF matroid_inv(1) matroid_inv(2)]

lemmas valid_solution_c_set_nonnegative = valid_solution_c_set_nonnegative[OF base_assms]
lemmas carrier_sorted_sorted_desc = carrier_sorted_sorted_desc[OF base_assms]
lemmas carrier_sorted_set = carrier_sorted_set[OF base_assms]
lemmas length_carrier_sorted = length_carrier_sorted[OF base_assms]
lemmas carrier_sorted_distinct = carrier_sorted_distinct[OF base_assms]
lemmas invar_1_props = invar_1_props[OF base_assms]
lemmas invar_2_props = invar_2_props[OF base_assms]
lemmas invar_3_props = invar_3_props[OF base_assms]
lemmas invar_1_holds_upd1 = invar_1_holds_upd1[OF base_assms]
lemmas invar_1_holds_upd2 = invar_1_holds_upd2[OF base_assms]
lemmas invar_2_holds_upd1 = invar_2_holds_upd1[OF base_assms]
lemmas invar_2_holds_upd2 = invar_2_holds_upd2[OF base_assms]
lemmas invar_3_holds_upd1 = invar_3_holds_upd1[OF base_assms]
lemmas invar_3_holds_upd2 = invar_3_holds_upd2[OF base_assms]
lemmas initial_state_props = initial_state_props[OF base_assms]
lemmas BestInGreedy_base_correct_1 = BestInGreedy_base_correct_1[OF base_assms]
lemmas BestInGreedy_base_correct_2 = BestInGreedy_base_correct_2[OF base_assms]

lemma sort_desc_stable:
  "nonnegative c \<Longrightarrow> valid_order order \<Longrightarrow>
   filter (\<lambda>y. c y = k) (sort_desc c order) = filter (\<lambda>y. c y = k) order"
  using \<open>sort_desc_axioms_stable\<close> by (simp add: sort_desc_axioms_stable_def)

context
  includes matroid.set.custom_automation
begin

lemma BestInGreedy_stablesort_bound_tight_aux:
  "\<exists>F B1 B2 c order X.
  F \<subseteq> (matroid.carrier_abs carrier) \<and> (indep_system.basis_in (matroid.indep_abs indep_fn) F B1) \<and>
  (indep_system.basis_in (matroid.indep_abs indep_fn) F B2) \<and> nonnegative c \<and> valid_order order \<and> valid_solution X \<and> 
  c_set c (to_set (result (BestInGreedy_base (initial_state c order)))) = rat_of_nat (card B1) \<and>
  c_set c (to_set X) = rat_of_nat (card B2) \<and> card B1 \<le> card B2 \<and>
  indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) =
  Frac (int (card B1)) (int (card B2))"
proof-
  let ?carrier_abs = "(matroid.carrier_abs carrier)"

  from indep_system.carrier_finite[OF indep_system_axioms_abs]
  have "finite ?carrier_abs" by simp

  from indep_system.ex_rank_quotient_frac[OF indep_system_axioms_abs]
  have "\<exists>F B1 B2. F \<subseteq> (matroid.carrier_abs carrier) \<and>
    indep_system.basis_in (matroid.indep_abs indep_fn) F B1 \<and>
    indep_system.basis_in (matroid.indep_abs indep_fn) F B2 \<and>
    card B1 \<le> card B2 \<and>
    indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) = Frac (int (card B1)) (int (card B2))" by metis
  then obtain F B1 B2 where "F \<subseteq> (matroid.carrier_abs carrier)"
    "indep_system.basis_in (matroid.indep_abs indep_fn) F B1"
    "indep_system.basis_in (matroid.indep_abs indep_fn) F B2"
    "card B1 \<le> card B2"
    "indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) = Frac (int (card B1)) (int (card B2))"
    by blast

  from indep_system.basis_in_subset_carrier[OF indep_system_axioms_abs \<open>F \<subseteq> (matroid.carrier_abs carrier)\<close>
      \<open>indep_system.basis_in (matroid.indep_abs indep_fn) F B1\<close>]
  have "B1 \<subseteq> F" .
  from indep_system.indep_in_indep[OF indep_system_axioms_abs
      indep_system.basis_in_indep_in[OF indep_system_axioms_abs \<open>F \<subseteq> (matroid.carrier_abs carrier)\<close>
        \<open>indep_system.basis_in (matroid.indep_abs indep_fn) F B1\<close>]]
  have "(matroid.indep_abs indep_fn) B1" .

  from indep_system.basis_in_subset_carrier[OF indep_system_axioms_abs \<open>F \<subseteq> (matroid.carrier_abs carrier)\<close>
      \<open>indep_system.basis_in (matroid.indep_abs indep_fn) F B2\<close>]
  have "B2 \<subseteq> F" .

  from indep_system.basis_in_finite[OF indep_system_axioms_abs \<open>F \<subseteq> (matroid.carrier_abs carrier)\<close>
      \<open>indep_system.basis_in (matroid.indep_abs indep_fn) F B1\<close>]
  have "finite B1" .
  from indep_system.carrier_finite[OF indep_system_axioms_abs] \<open>F \<subseteq> (matroid.carrier_abs carrier)\<close>
    finite_subset have "finite (F - B1)" by blast
  from indep_system.carrier_finite[OF indep_system_axioms_abs]
    finite_subset have "finite (?carrier_abs - F)" by blast

  let ?l_B1 = "sorted_list_of_set B1"
  have "length ?l_B1 = card B1" by simp
  from \<open>finite B1\<close> have "set ?l_B1 = B1" by simp

  let ?l_F_not_B1 = "sorted_list_of_set (F - B1)"
  have "length ?l_F_not_B1 = card (F - B1)" by simp
  from \<open>finite (F - B1)\<close> have "set ?l_F_not_B1 = (F - B1)" by simp

  let ?l_not_F = "sorted_list_of_set (?carrier_abs - F)"
  have "length ?l_not_F = card (?carrier_abs - F)" by simp
  from \<open>finite (?carrier_abs - F)\<close> have "set ?l_not_F = (?carrier_abs - F)" by simp

  let ?order = "?l_B1 @ ?l_F_not_B1 @ ?l_not_F"

  let ?l_F = "?l_B1 @ ?l_F_not_B1"

  from \<open>length ?l_B1 = card B1\<close> \<open>length ?l_F_not_B1 = card (F - B1)\<close>
  have "length ?l_F = card F" 
    by (metis Diff_disjoint Int_Diff_Un \<open>B1 \<subseteq> F\<close> \<open>finite (F - B1)\<close> \<open>finite B1\<close> card_Un_disjoint
        inf.absorb_iff2 length_append)
  from \<open>set ?l_B1 = B1\<close> \<open>set ?l_F_not_B1 = (F - B1)\<close> set_append[of ?l_B1 ?l_F_not_B1] \<open>B1 \<subseteq> F\<close>
  have "set ?l_F = F" by auto

  let ?l_not_B1 = "?l_F_not_B1 @ ?l_not_F"

  from \<open>length ?l_F_not_B1 = card (F - B1)\<close> \<open>length ?l_not_F = card (?carrier_abs - F)\<close>
  have "length ?l_not_B1 = card (?carrier_abs - B1)" 
    by (smt (verit) \<open>B1 \<subseteq> F\<close> \<open>F \<subseteq> matroid.carrier_abs carrier\<close> \<open>finite (matroid.carrier_abs carrier)\<close>
        card_Diff_subset card_mono dual_order.trans finite_subset le_add_diff_inverse length_append
        ordered_cancel_comm_monoid_diff_class.add_diff_assoc2)
  from \<open>set ?l_F_not_B1 = (F - B1)\<close> \<open>set ?l_not_F = (?carrier_abs - F)\<close> set_append[of ?l_F_not_B1 ?l_not_F]
    \<open>B1 \<subseteq> F\<close> \<open>F \<subseteq> matroid.carrier_abs carrier\<close>
  have "set ?l_not_B1 = (?carrier_abs - B1)"
    by auto

  from \<open>set ?l_B1 = B1\<close> \<open>set ?l_not_B1 = (?carrier_abs - B1)\<close>
  have "set ?l_B1 \<inter> set ?l_not_B1 = {}" by blast

  have order_expr1: "?order = ?l_F @ ?l_not_F" by simp
  have order_expr2: "?order = ?l_B1 @ ?l_not_B1" by simp

  from \<open>length ?l_F = card F\<close> \<open>length ?l_not_F = card (?carrier_abs - F)\<close> order_expr1
  have "length ?order = card ?carrier_abs"
    by (metis Diff_partition \<open>F \<subseteq> ?carrier_abs\<close> \<open>length ?l_not_B1 = card (?carrier_abs - B1)\<close>
        \<open>set ?l_not_B1 = ?carrier_abs - B1\<close> \<open>set ?l_not_F = ?carrier_abs - F\<close>
        \<open>set ?l_F = F\<close> \<open>set ?l_B1 \<inter> set ?l_not_B1 = {}\<close>
        card_distinct distinct_append distinct_card set_append)
  from \<open>set ?l_F = F\<close> \<open>set ?l_not_F = (?carrier_abs - F)\<close> order_expr1
  have "set ?order = ?carrier_abs"
    using \<open>F \<subseteq> matroid.carrier_abs carrier\<close> by auto

  from \<open>length ?order = card ?carrier_abs\<close> \<open>set ?order = ?carrier_abs\<close> 
  have "valid_order ?order" unfolding valid_order_def
    by (simp add: matroid.carrier_abs_def set_inv_carrier)
  then have "distinct ?order" unfolding valid_order_def using set_inv_carrier card_distinct
    by (metis matroid.set.set_cardinality)

  let ?c = "\<lambda>(x::'a). if x \<in> F then (1::rat) else 0"
  have "nonnegative ?c" using nonnegative_def by simp

  have "\<And>x. x \<in> F \<longleftrightarrow> ?c x = 1" by simp
  have "\<And>x. x \<notin> F \<longleftrightarrow> ?c x = 0" by simp
  have "\<And>x. ?c x = 1 \<longleftrightarrow> ?c x \<noteq> 0" by simp
  have "\<forall>x. ?c x = 1 \<or> ?c x = 0" by simp 

  have "(\<And>x. x \<in> set ?order \<Longrightarrow> (?c x = 1 \<longleftrightarrow> x \<in> set ?l_F))"
  proof (rule iffI, rule ccontr, goal_cases)
    case (1 x)
    with \<open>?order = ?l_F @ ?l_not_F\<close> have "x \<in> set ?l_not_F" by simp
    with \<open>set ?l_not_F = (?carrier_abs - F)\<close> have "?c x = 0" by simp
    with 1 show ?case by simp
  next
    case (2 x)
    with \<open>set ?l_F = F\<close> show ?case by auto
  qed

  with sorted_aux3[OF \<open>distinct ?order\<close> \<open>?order = ?l_F @ ?l_not_F\<close>]
  have "?l_F = filter (\<lambda>y. ?c y = 1) ?order" by presburger

  with \<open>?order = ?l_F @ ?l_not_F\<close>
  have "?order = (filter (\<lambda>y. ?c y = 1) ?order) @ ?l_not_F" by auto

  from sorted_aux4[OF \<open>distinct ?order\<close> this]
  have "?l_not_F = (filter (\<lambda>y. ?c y \<noteq> 1) ?order)" .
  with \<open>\<And>x. ?c x = 1 \<longleftrightarrow> ?c x \<noteq> 0\<close>
  have "?l_not_F = (filter (\<lambda>y. ?c y = 0) ?order)" by simp

  from \<open>?l_F = filter (\<lambda>y. ?c y = 1) ?order\<close>
  have "length (filter (\<lambda>y. ?c y = 1) ?order) = card F"
    using \<open>length ?l_F = card F\<close> by simp
  then have "length (filter (\<lambda>y. ?c y = 1) (sort_desc ?c ?order)) = card F"
    using sort_desc_stable[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>] by auto

  from carrier_sorted_distinct[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>]
  have "distinct (sort_desc ?c ?order)" by simp

  from \<open>length ?order = card ?carrier_abs\<close> order_expr1 \<open>length ?l_F = card F\<close>
  have "card F \<le> card ?carrier_abs"
    using \<open>F \<subseteq> matroid.carrier_abs carrier\<close> \<open>finite (matroid.carrier_abs carrier)\<close> card_mono by blast
  with length_carrier_sorted[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>]
  have "card F \<le> length (sort_desc ?c ?order)"
    using set_inv_carrier \<open>length ?order = card (matroid.carrier_abs carrier)\<close> sort_desc_axioms sort_desc_axioms_def
    by presburger
  from sorted_aux5[OF \<open>distinct (sort_desc ?c ?order)\<close> carrier_sorted_sorted_desc[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>] \<open>\<forall>x. ?c x = 1 \<or> ?c x = 0\<close>
      \<open>length (filter (\<lambda>y. ?c y = 1) (sort_desc ?c ?order)) = card F\<close> \<open>card F \<le> length (sort_desc ?c ?order)\<close>]
  have "sort_desc ?c ?order = (filter (\<lambda>y. ?c y = 1) (sort_desc ?c ?order)) @
    (filter (\<lambda>y. ?c y \<noteq> 1) (sort_desc ?c ?order))" .
  with \<open>\<And>x. ?c x = 1 \<longleftrightarrow> ?c x \<noteq> 0\<close>
  have "sort_desc ?c ?order = (filter (\<lambda>y. ?c y = 1) (sort_desc ?c ?order)) @
    (filter (\<lambda>y. ?c y = 0) (sort_desc ?c ?order))"
    by simp
  with sort_desc_stable[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>]
  have "sort_desc ?c ?order = (filter (\<lambda>y. ?c y = 1) ?order) @ (filter (\<lambda>y. ?c y = 0) ?order)"
    by simp

  with \<open>?l_F = filter (\<lambda>y. ?c y = 1) ?order\<close> \<open>?l_not_F = (filter (\<lambda>y. ?c y = 0) ?order)\<close>
  have carrier_sorted_expr: "sort_desc ?c ?order = ?l_B1 @ ?l_not_B1" by fastforce


  have num_iter_in_B1: "\<And>best_in_greedy_state. length (carrier_list best_in_greedy_state) \<ge> 1 \<Longrightarrow>
    (carrier_list best_in_greedy_state) = drop (num_iter ?c ?order best_in_greedy_state) (sort_desc ?c ?order) \<Longrightarrow>
    hd (carrier_list best_in_greedy_state) \<in> B1 \<Longrightarrow> num_iter ?c ?order best_in_greedy_state < length ?l_B1"
    using carrier_sorted_expr \<open>set ?l_B1 \<inter> set ?l_not_B1 = {}\<close> \<open>set ?l_B1 = B1\<close>
    by (smt (verit) append_Nil disjoint_iff_not_equal drop_all drop_append in_set_dropD length_greater_0_conv
        less_numeral_extra(1) linorder_le_less_linear list.set_sel(1) order_less_le_trans)
  have num_iter_not_in_B1: "\<And>best_in_greedy_state. hd (carrier_list best_in_greedy_state) \<notin> B1 \<Longrightarrow>
    (carrier_list best_in_greedy_state) = drop (num_iter ?c ?order best_in_greedy_state) (sort_desc ?c ?order) \<Longrightarrow>
    num_iter ?c ?order best_in_greedy_state \<ge> length ?l_B1"
    by (metis \<open>set ?l_B1 = B1\<close> carrier_sorted_expr drop_append drop_eq_Nil hd_append2 in_set_dropD list.set_sel(1))

  let ?prop = "\<lambda>best_in_greedy_state.
    (set (take (num_iter ?c ?order best_in_greedy_state) ?l_B1) \<subseteq> to_set (result (best_in_greedy_state))) \<and>
    (to_set (result (best_in_greedy_state)) \<subseteq> (matroid.carrier_abs carrier) - (F - B1))"


  have prop_holds_upd1:
    "\<And>best_in_greedy_state.
      BestInGreedy_base_call_1_conds best_in_greedy_state \<Longrightarrow> invar_1 best_in_greedy_state \<Longrightarrow>
      invar_2 ?c ?order best_in_greedy_state \<Longrightarrow> ?prop best_in_greedy_state \<Longrightarrow>
      ?prop (BestInGreedy_base_upd1 best_in_greedy_state)"
  proof-
    fix best_in_greedy_state::"('a, 's, 'b) best_in_greedy_state_scheme"
    assume "BestInGreedy_base_call_1_conds best_in_greedy_state" "invar_1 best_in_greedy_state"
      "invar_2 ?c ?order best_in_greedy_state" "?prop best_in_greedy_state"

    have "length (carrier_list (BestInGreedy_base_upd1 best_in_greedy_state)) =
      length (carrier_list best_in_greedy_state) - 1"
      using \<open>BestInGreedy_base_call_1_conds best_in_greedy_state\<close> 
      by (auto simp add: BestInGreedy_base_upd1_def Let_def elim!: call_cond_elims)
    moreover have "length (carrier_list best_in_greedy_state) \<ge> 1"
      using \<open>BestInGreedy_base_call_1_conds best_in_greedy_state\<close> 
      by (auto elim!: call_cond_elims)
    ultimately have num_iter_upd: "num_iter ?c ?order (BestInGreedy_base_upd1 best_in_greedy_state) =
      1 + (num_iter ?c ?order best_in_greedy_state)"
      unfolding num_iter_def 
      using \<open>invar_2 ?c ?order best_in_greedy_state\<close> \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>
      by (fastforce elim!: invar_2_props)




    have "hd (carrier_list best_in_greedy_state) \<notin> F - B1"
    proof (rule ccontr, goal_cases)
      case 1
      then have "hd (carrier_list best_in_greedy_state) \<in> F - B1" by simp

      with num_iter_not_in_B1 have "num_iter ?c ?order best_in_greedy_state \<ge> length ?l_B1"
        using \<open>invar_2 ?c ?order best_in_greedy_state\<close>
        by (auto elim!: invar_2_props[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>])

      with \<open>?prop best_in_greedy_state\<close> \<open>set ?l_B1 = B1\<close>
      have "B1 \<subseteq> to_set (result (best_in_greedy_state))"
        by simp 

      with \<open>?prop best_in_greedy_state\<close>
      have "to_set (result (best_in_greedy_state)) \<subseteq> (matroid.carrier_abs carrier) - (F - B1)"
        by blast

      from bound_tight_set_aux[OF \<open>F \<subseteq> (matroid.carrier_abs carrier)\<close> \<open>B1 \<subseteq> F\<close> \<open>B1 \<subseteq> to_set (result (best_in_greedy_state))\<close> this]
      have "\<exists>Y. to_set (result best_in_greedy_state) = Y \<union> B1 \<and> Y \<subseteq> matroid.carrier_abs carrier - F" .
      then obtain Y where "to_set (result best_in_greedy_state) = Y \<union> B1" "Y \<subseteq> matroid.carrier_abs carrier - F"
        by blast

      from indep_system.basis_in_max_indep_in[OF indep_system_axioms_abs \<open>F \<subseteq> (matroid.carrier_abs carrier)\<close>
          \<open>indep_system.basis_in (matroid.indep_abs indep_fn) F B1\<close>]
      have "\<forall>x \<in> F - B1. \<not>(matroid.indep_abs indep_fn) (insert x B1)"
        using indep_system.indep_in_def[OF indep_system_axioms_abs]
        by (metis DiffD1 \<open>F \<subseteq> matroid.carrier_abs carrier\<close> \<open>indep_system.basis_in (matroid.indep_abs indep_fn) F B1\<close>
            indep_system.basis_in_indep_in indep_system_axioms_abs insert_subset)
      moreover have "\<forall>x \<in> F - B1. insert x B1 \<subseteq> insert x (B1 \<union> Y)" by blast
      ultimately have "\<forall>x \<in> F - B1. \<not>(matroid.indep_abs indep_fn) (insert x (B1 \<union> Y))"
        using indep_system.indep_subset[OF indep_system_axioms_abs] by metis
      then have "\<forall>x \<in> F - B1. \<not>(matroid.indep_abs indep_fn)
        (insert x (to_set (result best_in_greedy_state)))"
        using \<open>to_set (result best_in_greedy_state) = Y \<union> B1\<close>
        by (simp add: Un_commute)

      with \<open>hd (carrier_list best_in_greedy_state) \<in> F - B1\<close> 
      have "\<not>(indep' (set_insert (hd (carrier_list best_in_greedy_state)) (result best_in_greedy_state)))"
        using \<open>invar_1 best_in_greedy_state\<close>
        by (metis insert_is_Un invar_1_def matroid.indep_impl_to_abs matroid.set.invar_insert matroid.set.set_insert matroid_inv(1) matroid_inv(2) sup.commute)

      then show ?case
        using \<open>BestInGreedy_base_call_1_conds best_in_greedy_state\<close>
        by (auto elim!: call_cond_elims)
    qed

    moreover have "hd (carrier_list best_in_greedy_state) \<in> (matroid.carrier_abs carrier)"
      using \<open>invar_2 ?c ?order best_in_greedy_state\<close> \<open>BestInGreedy_base_call_1_conds best_in_greedy_state\<close>
      by (metis BestInGreedy_base_call_1_conds carrier_sorted_set[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>] in_set_dropD
          invar_2_props[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>] list.set_sel(1) list.simps(3) matroid.carrier_abs_def)
    ultimately have 
      "hd (carrier_list best_in_greedy_state) \<in> (matroid.carrier_abs carrier) - (F - B1)" by auto

    have to_set_upd: "to_set (result (BestInGreedy_base_upd1 best_in_greedy_state)) =
      insert (hd (carrier_list best_in_greedy_state)) (to_set (result best_in_greedy_state))"
      using \<open>invar_1 best_in_greedy_state\<close>
      by (auto simp add: BestInGreedy_base_upd1_def elim!: invar_1_props[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>])

    from \<open>hd (carrier_list best_in_greedy_state) \<in> (matroid.carrier_abs carrier) - (F - B1)\<close>
      \<open>B1 \<subseteq> F\<close> \<open>F \<subseteq> (matroid.carrier_abs carrier)\<close> indep_system.carrier_finite[OF indep_system_axioms_abs]
    consider "hd (carrier_list best_in_greedy_state) \<in> B1" |
      "hd (carrier_list best_in_greedy_state) \<in> (matroid.carrier_abs carrier) - F" by blast
    then have 
      prop1: "set (take (num_iter ?c ?order (BestInGreedy_base_upd1 best_in_greedy_state)) ?l_B1) \<subseteq>
      to_set (result (BestInGreedy_base_upd1 best_in_greedy_state))"
    proof (cases)
      case 1
      with num_iter_in_B1 have "num_iter ?c ?order best_in_greedy_state < length ?l_B1"
        using \<open>1 \<le> length (carrier_list best_in_greedy_state)\<close>
          \<open>invar_2 ?c ?order best_in_greedy_state\<close> 
        by (auto elim!: invar_2_props[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>])
      with carrier_sorted_expr have "num_iter ?c ?order best_in_greedy_state < length (sort_desc ?c ?order)" by auto 

      then have "set (take (num_iter ?c ?order (BestInGreedy_base_upd1 best_in_greedy_state)) (sort_desc ?c ?order)) =
        insert (hd (drop (num_iter ?c ?order best_in_greedy_state) (sort_desc ?c ?order)))
        (set (take (num_iter ?c ?order best_in_greedy_state) (sort_desc ?c ?order)))"
        apply (simp add: num_iter_upd)
        by (metis list.set(2) rotate1.simps(2) set_rotate1 take_hd_drop)
      then have "set (take (num_iter ?c ?order (BestInGreedy_base_upd1 best_in_greedy_state)) (sort_desc ?c ?order)) =
        insert (hd (carrier_list best_in_greedy_state))
        (set (take (num_iter ?c ?order best_in_greedy_state) (sort_desc ?c ?order)))"
        using \<open>invar_2 ?c ?order best_in_greedy_state\<close> 
        by (simp add: invar_2_def)

      moreover have
        "take (num_iter ?c ?order (BestInGreedy_base_upd1 best_in_greedy_state)) (sort_desc ?c ?order) =
          take (num_iter ?c ?order (BestInGreedy_base_upd1 best_in_greedy_state)) ?l_B1"
        using \<open>num_iter ?c ?order best_in_greedy_state < length ?l_B1\<close> num_iter_upd carrier_sorted_expr by simp
      moreover have
        "take (num_iter ?c ?order best_in_greedy_state) (sort_desc ?c ?order) =
          take (num_iter ?c ?order best_in_greedy_state) ?l_B1"
        using \<open>num_iter ?c ?order best_in_greedy_state < length ?l_B1\<close> carrier_sorted_expr by simp
      ultimately have "set (take (num_iter ?c ?order (BestInGreedy_base_upd1 best_in_greedy_state)) ?l_B1) =
        insert (hd (carrier_list best_in_greedy_state))
        (set (take (num_iter ?c ?order best_in_greedy_state) ?l_B1))" by auto   

      with \<open>?prop best_in_greedy_state\<close> to_set_upd 
      show ?thesis by blast
    next
      case 2
      with \<open>B1 \<subseteq> F\<close> num_iter_not_in_B1 have "num_iter ?c ?order best_in_greedy_state \<ge> length ?l_B1"
        using \<open>invar_2 ?c ?order best_in_greedy_state\<close>
        by (auto elim!: invar_2_props[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>]) 

      then have "set (take (num_iter ?c ?order (BestInGreedy_base_upd1 best_in_greedy_state)) ?l_B1) =
        set (take (num_iter ?c ?order best_in_greedy_state) ?l_B1)" using num_iter_upd by auto
      with \<open>?prop best_in_greedy_state\<close> to_set_upd 
      show ?thesis by blast
    qed

    with \<open>hd (carrier_list best_in_greedy_state) \<in> (matroid.carrier_abs carrier) - (F - B1)\<close>
      \<open>?prop best_in_greedy_state\<close>
    have "insert (hd (carrier_list best_in_greedy_state)) (to_set (result best_in_greedy_state))
        \<subseteq> matroid.carrier_abs carrier - (F - B1)"
      by blast

    then have prop2:
      "to_set (result (BestInGreedy_base_upd1 best_in_greedy_state)) \<subseteq> (matroid.carrier_abs carrier) - (F - B1)"
      using \<open>invar_1 best_in_greedy_state\<close>
      by (auto simp add: BestInGreedy_base_upd1_def elim!: invar_1_props[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>])

    from prop1 prop2 show
      "?prop (BestInGreedy_base_upd1 best_in_greedy_state)" by blast
  qed

  have prop_holds_upd2:
    "\<And>best_in_greedy_state.
      BestInGreedy_base_call_2_conds best_in_greedy_state \<Longrightarrow> invar_1 best_in_greedy_state \<Longrightarrow>
      invar_2 ?c ?order best_in_greedy_state \<Longrightarrow> invar_3 ?c ?order best_in_greedy_state \<Longrightarrow> ?prop best_in_greedy_state \<Longrightarrow>
      ?prop (BestInGreedy_base_upd2 best_in_greedy_state)"
  proof-
    fix best_in_greedy_state::"('a, 's, 'b) best_in_greedy_state_scheme"
    assume "BestInGreedy_base_call_2_conds best_in_greedy_state" "invar_1 best_in_greedy_state"
      "invar_2 ?c ?order best_in_greedy_state" "invar_3 ?c ?order best_in_greedy_state" "?prop best_in_greedy_state"


    have "length (carrier_list (BestInGreedy_base_upd2 best_in_greedy_state)) =
      length (carrier_list best_in_greedy_state) - 1"
      using \<open>BestInGreedy_base_call_2_conds best_in_greedy_state\<close> 
      by (auto simp add: BestInGreedy_base_upd2_def Let_def elim!: call_cond_elims)
    moreover have "length (carrier_list best_in_greedy_state) \<ge> 1"
      using \<open>BestInGreedy_base_call_2_conds best_in_greedy_state\<close> 
      by (auto elim!: call_cond_elims)
    ultimately have num_iter_upd: "num_iter ?c ?order (BestInGreedy_base_upd2 best_in_greedy_state) =
      1 + (num_iter ?c ?order best_in_greedy_state)"
      unfolding num_iter_def 
      using \<open>invar_2 ?c ?order best_in_greedy_state\<close>
      by (fastforce elim!: invar_2_props[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>])


    have "hd (carrier_list best_in_greedy_state) \<notin> B1"
    proof (rule ccontr, goal_cases)
      case 1
      then have "hd (carrier_list best_in_greedy_state) \<in> B1" by blast

      with num_iter_in_B1 have "num_iter ?c ?order best_in_greedy_state < length ?l_B1"
        using \<open>1 \<le> length (carrier_list best_in_greedy_state)\<close>
          \<open>invar_2 ?c ?order best_in_greedy_state\<close> 
        by (auto elim!: invar_2_props[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>])

      have "(to_set (result best_in_greedy_state)) \<subseteq> 
        set (take (num_iter ?c ?order best_in_greedy_state) (?l_B1 @ ?l_not_B1))"
        using \<open>invar_3 ?c ?order best_in_greedy_state\<close>
        by (auto simp add: carrier_pref_def carrier_sorted_expr elim!: invar_3_props[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>])
      with \<open>num_iter ?c ?order best_in_greedy_state < length ?l_B1\<close> \<open>set ?l_B1 = B1\<close> set_take_subset
      have "(to_set (result best_in_greedy_state)) \<subseteq> B1"
        by force

      with \<open>hd (carrier_list best_in_greedy_state) \<in> B1\<close>
      have "insert (hd (carrier_list best_in_greedy_state)) (to_set (result best_in_greedy_state)) \<subseteq> B1"
        by auto

      from indep_system.indep_subset[OF indep_system_axioms_abs \<open>(matroid.indep_abs (indep_fn)) B1\<close> this]
      have "matroid.indep_abs indep_fn (insert (hd (carrier_list best_in_greedy_state))
          (to_set (result best_in_greedy_state)))" .

      show ?case
        using \<open>invar_1 best_in_greedy_state\<close> \<open>BestInGreedy_base_call_2_conds best_in_greedy_state\<close>
        by (metis BestInGreedy_base_call_2_conds\<open>matroid.indep_abs indep_fn (insert (hd (carrier_list best_in_greedy_state))
          (to_set (result best_in_greedy_state)))\<close> inf_sup_aci(5) insert_is_Un invar_1_def local.simps matroid.set.invar_insert
            matroid.set.set_insert)
    qed

    with num_iter_not_in_B1 have "num_iter ?c ?order best_in_greedy_state \<ge> length ?l_B1"
      using \<open>invar_2 ?c ?order best_in_greedy_state\<close>
      by (auto elim!: invar_2_props[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>])

    then have "set (take (num_iter ?c ?order (BestInGreedy_base_upd2 best_in_greedy_state)) ?l_B1) =
      set (take (num_iter ?c ?order best_in_greedy_state) ?l_B1)" using num_iter_upd by auto
    with \<open>?prop best_in_greedy_state\<close>
    have prop1: "set (take (num_iter ?c ?order (BestInGreedy_base_upd2 best_in_greedy_state)) ?l_B1) \<subseteq>
        to_set (result (BestInGreedy_base_upd2 best_in_greedy_state))"
      using \<open>BestInGreedy_base_call_2_conds best_in_greedy_state\<close>
      by (auto simp add: BestInGreedy_base_upd2_def elim!: call_cond_elims)

    with \<open>?prop best_in_greedy_state\<close>
    have prop2: "to_set (result (BestInGreedy_base_upd2 best_in_greedy_state)) \<subseteq> (matroid.carrier_abs carrier) - (F - B1)"
      by (auto simp add: BestInGreedy_base_upd2_def)

    from prop1 prop2 show "?prop (BestInGreedy_base_upd2 best_in_greedy_state)" by blast
  qed

  have prop_holds: "(\<And>best_in_greedy_state. 
    BestInGreedy_base_dom best_in_greedy_state \<Longrightarrow> invar_1 best_in_greedy_state \<Longrightarrow>
      invar_2 ?c ?order best_in_greedy_state \<Longrightarrow> invar_3 ?c ?order best_in_greedy_state \<Longrightarrow>
       ?prop best_in_greedy_state \<Longrightarrow> ?prop (BestInGreedy_base best_in_greedy_state))"
  proof-
    fix best_in_greedy_state
    assume assms: "BestInGreedy_base_dom best_in_greedy_state" "invar_1 best_in_greedy_state"
      "invar_2 ?c ?order best_in_greedy_state" "invar_3 ?c ?order best_in_greedy_state"
      "?prop best_in_greedy_state"

    show "?prop (BestInGreedy_base best_in_greedy_state)"
      using \<open>invar_1 best_in_greedy_state\<close> \<open>invar_2 ?c ?order best_in_greedy_state\<close>
        \<open>invar_3 ?c ?order best_in_greedy_state\<close> \<open>?prop best_in_greedy_state\<close>
    proof (induction rule: BestInGreedy_base_induct[OF \<open>BestInGreedy_base_dom best_in_greedy_state\<close>])
      case IH: (1 best_in_greedy_state)
      show ?case
        apply(rule BestInGreedy_base_cases[where best_in_greedy_state = best_in_greedy_state])
        subgoal
          apply(simp add: BestInGreedy_base_simps(1)[OF IH(1)])
          apply(rule IH(2))
          apply(assumption)
          apply (fastforce intro!: IH(4-) invar_1_holds_upd1[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>])
          apply (fastforce intro!: IH(4-) invar_2_holds_upd1[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>])
          apply (fastforce intro!: IH(4-) invar_3_holds_upd1[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>])
          using prop_holds_upd1 IH(4-) by fastforce
        subgoal
          apply(simp add: BestInGreedy_base_simps(2)[OF IH(1)])
          apply(rule IH(3))
          apply(assumption)
          apply (fastforce intro!: IH(4-) invar_1_holds_upd2[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>])
          apply (fastforce intro!: IH(4-) invar_2_holds_upd2[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>])
          apply (fastforce intro!: IH(4-) invar_3_holds_upd2[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>])
          using prop_holds_upd2 IH(4-) by fastforce
        subgoal
          apply(simp add: BestInGreedy_base_simps(3)[OF IH(1)])
          using IH(7) by (simp add: BestInGreedy_base_ret1_def)
        done
    qed
  qed

  have "?prop (initial_state ?c ?order)"
    unfolding num_iter_def initial_state_def by auto
  with prop_holds initial_state_props[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>]
  have "?prop (BestInGreedy_base (initial_state ?c ?order))" by blast


  have "length ?order = length (sort_desc ?c ?order)"
    using sort_desc_axioms sort_desc_axioms_def by blast

  have "\<And>best_in_greedy_state. BestInGreedy_base_dom best_in_greedy_state \<Longrightarrow> 
    carrier_list (BestInGreedy_base best_in_greedy_state) = []"
  proof-
    fix best_in_greedy_state
    assume "BestInGreedy_base_dom best_in_greedy_state"
    show "carrier_list (BestInGreedy_base best_in_greedy_state) = []"
    proof (induction rule: BestInGreedy_base_induct[OF \<open>BestInGreedy_base_dom best_in_greedy_state\<close>])
      case IH: (1 best_in_greedy_state)
      show ?case 
        apply(rule BestInGreedy_base_cases[where best_in_greedy_state = best_in_greedy_state])
        by (auto simp add: IH BestInGreedy_base_ret1_def BestInGreedy_base_simps[OF \<open>BestInGreedy_base_dom best_in_greedy_state\<close>] 
            elim!: BestInGreedy_base_ret_1_conds)
    qed
  qed

  with initial_state_props[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>]
  have "num_iter ?c ?order (BestInGreedy_base (initial_state ?c ?order)) = length (sort_desc ?c ?order)"
    unfolding num_iter_def by auto
  with order_expr2 \<open>length ?order = length (sort_desc ?c ?order)\<close>
  have "num_iter ?c ?order (BestInGreedy_base (initial_state ?c ?order)) \<ge> length ?l_B1" by simp

  with \<open>?prop (BestInGreedy_base (initial_state ?c ?order))\<close> \<open>set ?l_B1 = B1\<close> 
  have "B1 \<subseteq> to_set (result (BestInGreedy_base (initial_state ?c ?order)))" by simp
  from \<open>?prop (BestInGreedy_base (initial_state ?c ?order))\<close>
  have "to_set (result (BestInGreedy_base (initial_state ?c ?order))) \<subseteq> (matroid.carrier_abs carrier) - (F - B1)"
    by blast

  from bound_tight_set_aux[OF \<open>F \<subseteq> (matroid.carrier_abs carrier)\<close> \<open>B1 \<subseteq> F\<close> \<open>B1 \<subseteq> to_set (result (BestInGreedy_base (initial_state ?c ?order)))\<close>
      \<open>to_set (result (BestInGreedy_base (initial_state ?c ?order))) \<subseteq> (matroid.carrier_abs carrier) - (F - B1)\<close>]
  have "\<exists>X. to_set (result (BestInGreedy_base (initial_state ?c ?order))) = X \<union> B1 \<and>
    X \<subseteq> (matroid.carrier_abs carrier) - F"
    by simp
  then obtain X where 
    "to_set (result (BestInGreedy_base (initial_state ?c ?order))) = X \<union> B1" "X \<subseteq> (matroid.carrier_abs carrier) - F"
    by blast
  with \<open>B1 \<subseteq> F\<close> have "X \<inter> B1 = {}" by blast

(* Cost of greedy solution *)
  from \<open>X \<subseteq> (matroid.carrier_abs carrier) - F\<close> indep_system.carrier_finite[OF indep_system_axioms_abs]
    finite_subset
  have "finite X" by auto
  from \<open>B1 \<subseteq> F\<close> \<open>F \<subseteq> (matroid.carrier_abs carrier)\<close> indep_system.carrier_finite[OF indep_system_axioms_abs]
    finite_subset
  have "finite B1" by metis

  from sum.union_disjoint[OF \<open>finite X\<close> \<open>finite B1\<close> \<open>X \<inter> B1 = {}\<close>] 
    \<open>to_set (result (BestInGreedy_base (initial_state ?c ?order))) = X \<union> B1\<close>
  have "sum ?c (to_set (result (BestInGreedy_base (initial_state ?c ?order)))) = sum ?c X + sum ?c B1" by auto
  also have "... = sum ?c B1" using \<open>X \<subseteq> (matroid.carrier_abs carrier) - F\<close>
    using in_mono by fastforce
  also have "... = rat_of_nat (card B1)"
    using in_mono \<open>B1 \<subseteq> F\<close> by fastforce
  finally have "sum ?c (to_set (result (BestInGreedy_base (initial_state ?c ?order)))) = rat_of_nat (card B1)" .
  then have "c_set ?c (to_set (result (BestInGreedy_base (initial_state ?c ?order)))) = rat_of_nat (card B1)"
    using c_set_def by metis

(* Cost of B2 solution *)
  have "\<exists>X_B2. set_inv X_B2 \<and> to_set X_B2 = B2"
    by (metis \<open>B2 \<subseteq> F\<close> \<open>F \<subseteq> matroid.carrier_abs carrier\<close> indep_system_axioms_abs indep_system_def
        matroid.from_set_correct matroid.invar_from_set rev_finite_subset)
  then obtain X_B2 where "set_inv X_B2" "to_set X_B2 = B2" by blast
  then have "sum ?c (to_set X_B2) = rat_of_nat (card B2)"
    using in_mono \<open>B2 \<subseteq> F\<close> by fastforce
  then have "c_set ?c (to_set X_B2) = rat_of_nat (card B2)"
    using c_set_def by metis

(* B2 solution is valid *)
  from \<open>B2 \<subseteq> F\<close> \<open>F \<subseteq> (matroid.carrier_abs carrier)\<close> set_inv_carrier matroid.carrier_abs_def \<open>to_set X_B2 = B2\<close>
  have "subseteq X_B2 carrier"
    using set_inv_carrier \<open>set_inv X_B2\<close> by force

  from indep_system.basis_in_indep_in[OF indep_system_axioms_abs \<open>F \<subseteq> (matroid.carrier_abs carrier)\<close>
      \<open>indep_system.basis_in (matroid.indep_abs indep_fn) F B2\<close>]
    indep_system.indep_in_def[OF indep_system_axioms_abs] \<open>to_set X_B2 = B2\<close> \<open>set_inv X_B2\<close>
  have "indep' X_B2" by simp

  from \<open>set_inv X_B2\<close> \<open>subseteq X_B2 carrier\<close> \<open>indep' X_B2\<close> valid_solution_def 
  have "valid_solution X_B2" by simp

  from \<open>F \<subseteq> matroid.carrier_abs carrier\<close> \<open>indep_system.basis_in (matroid.indep_abs indep_fn) F B1\<close>
    \<open>indep_system.basis_in (matroid.indep_abs indep_fn) F B2\<close> \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>
    \<open>valid_solution X_B2\<close> \<open>c_set ?c (to_set (result (BestInGreedy_base (initial_state ?c ?order)))) = rat_of_nat (card B1)\<close>
    \<open>c_set ?c (to_set X_B2) = rat_of_nat (card B2)\<close> \<open>card B1 \<le> card B2\<close>
    \<open>indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) = Frac (int (card B1)) (int (card B2))\<close>
  show ?thesis by blast
qed

lemma BestInGreedy_stablesort_bound_tight:
  "(\<exists>c. nonnegative c \<and> (\<exists>order. valid_order order \<and> (\<exists>X. valid_solution X \<and> 
     c_set c (to_set (result (BestInGreedy_base (initial_state c order)))) = 
     indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) * 
     c_set c (to_set X))))"
  using BestInGreedy_stablesort_bound_tight_aux Frac_of_int_leq_quotient by fastforce

lemma BestInGreedy_stablesort_matroid_iff_opt:
  "(matroid.matroid_axioms carrier indep_fn) = 
    (\<forall>c. nonnegative c \<longrightarrow> (\<forall>order. valid_order order \<longrightarrow> (\<forall>X. valid_solution X \<longrightarrow>
    c_set c (to_set (result (BestInGreedy_base (initial_state c order)))) \<ge> c_set c (to_set X))))"
proof-

  have greedy_opt_iff_rq_eq_1: "(\<forall>c. nonnegative c \<longrightarrow> (\<forall>order. valid_order order \<longrightarrow> (\<forall>X. valid_solution X \<longrightarrow>
    c_set c (to_set (result (BestInGreedy_base (initial_state c order)))) \<ge> c_set c (to_set X)))) = 
    (indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) = 1)"
  proof (rule iffI, erule HOL.contrapos_pp)
    assume "indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) \<noteq> 1"
    with indep_system.rank_quotient_leq_1[OF indep_system_axioms_abs]
    have rq_less_1: "indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) < 1" 
      by simp

    from BestInGreedy_stablesort_bound_tight_aux obtain F B1 B2 c order X 
      where bound_tight: 
        "F \<subseteq> (matroid.carrier_abs carrier)" "(indep_system.basis_in (matroid.indep_abs indep_fn) F B1)"
        "(indep_system.basis_in (matroid.indep_abs indep_fn) F B2)" "nonnegative c" "valid_order order" "valid_solution X"
        "c_set c (to_set (result (BestInGreedy_base (initial_state c order)))) = rat_of_nat (card B1)"
        "c_set c (to_set X) = rat_of_nat (card B2)" "card B1 \<le> card B2"
        "indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) =
      Frac (int (card B1)) (int (card B2))" by blast

    have
      c_greedy_nonneg: "c_set c (to_set (result (BestInGreedy_base (initial_state c order)))) \<ge> 0"
      using valid_solution_c_set_nonnegative[OF \<open>nonnegative c\<close> \<open>valid_order order\<close> BestInGreedy_base_correct_1[OF \<open>nonnegative c\<close> \<open>valid_order order\<close>]]
      by simp
    have
      c_X_nonneg: "c_set c (to_set X) \<ge> 0"
      using valid_solution_c_set_nonnegative[OF \<open>nonnegative c\<close> \<open>valid_order order\<close> \<open>valid_solution X\<close>] by simp

    from rq_less_1 Frac_def bound_tight
    have "card B1 \<noteq> card B2" by auto
    with bound_tight Frac_def have
      "indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) =
      Fract (int (card B1)) (int (card B2))" by auto

    from bound_tight Frac_of_int_leq_quotient \<open>card B1 \<le> card B2\<close> have rank_quotient_prod:
      "c_set c (to_set (result (BestInGreedy_base (initial_state c order)))) =
      indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) * c_set c (to_set X)"
      by simp

    have c_X_pos: "c_set c (to_set X) > 0"
    proof (rule ccontr, goal_cases)
      case 1
      with c_X_nonneg have "c_set c (to_set X) = 0" by simp
      with \<open>c_set c (to_set X) = rat_of_nat (card B2)\<close>
      have "card B2 = 0" by simp

      with \<open>card B1 \<le> card B2\<close> have "card B1 = 0" by simp

      from \<open>card B1 = 0\<close> \<open>card B2 = 0\<close>
        \<open>indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) =
        Frac (int (card B1)) (int (card B2))\<close>
      have "indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) = 1"
        using Frac_def by auto

      with rq_less_1 show ?case by simp
    qed

    from c_greedy_nonneg c_X_pos rank_quotient_prod rq_less_1
    have "c_set c (to_set (result (BestInGreedy_base (initial_state c order)))) < c_set c (to_set X)"
      by auto
    with \<open>nonnegative c\<close> \<open>valid_order order\<close> \<open>valid_solution X\<close>
    show "\<not>(\<forall>c. nonnegative c \<longrightarrow> (\<forall>order. valid_order order \<longrightarrow> (\<forall>X. valid_solution X \<longrightarrow>
      c_set c (to_set (result (BestInGreedy_base (initial_state c order)))) \<ge> c_set c (to_set X))))"
      by force
  next
    assume "(indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) = 1)"
    then show "(\<forall>c. nonnegative c \<longrightarrow> (\<forall>order. valid_order order \<longrightarrow> (\<forall>X. valid_solution X \<longrightarrow>
      c_set c (to_set (result (BestInGreedy_base (initial_state c order)))) \<ge> c_set c (to_set X))))"
      using BestInGreedy_base_correct_2 by simp
  qed

  from indep_system.matroid_iff_rq_eq_1[OF indep_system_axioms_abs] greedy_opt_iff_rq_eq_1
  show ?thesis 
    using BestInGreedy_base_axioms_def matroid.matroid_abs_equiv \<open>BestInGreedy_base_axioms\<close> by presburger
qed

end

end

end

end
