theory Greedy_Common
  imports
    Main
    Indep_System_Matroids_Specs
begin

section \<open>Common Setup for Greedy Algorithms on Independence Systems\<close>

text \<open>Definitions and lemmas shared by the best-in greedy and the worst-out greedy algorithm:
  the state record, sorting by costs, prefixes of the sorted carrier and costs of sets.\<close>

record ('a, 's) greedy_state = carrier_list :: "'a list" result :: 's

named_theorems call_cond_elims
named_theorems call_cond_intros
named_theorems ret_holds_intros
named_theorems invar_props_intros
named_theorems invar_props_elims
named_theorems invar_holds_intros

definition "sort_desc_axioms sort_desc =(
  (\<forall>c order. sorted_wrt (\<lambda>x1 x2. c x1 \<ge> c x2) (sort_desc c order) \<and>
  set order = set (sort_desc c order) \<and> length order = length (sort_desc c order) \<and>
  (\<forall>k. filter (\<lambda>y. c y = k) (sort_desc c order) = filter (\<lambda>y. c y = k) order)))"
abbreviation "sort_desc_axioms' == sort_desc_axioms"
hide_const sort_desc_axioms

locale Greedy_Common = matroid: Matroid_Specs 
  where set_empty = set_empty for set_empty :: "'s" +
  fixes carrier :: "'s" and indep_fn :: "'s \<Rightarrow> bool" and
    sort_desc :: "('a \<Rightarrow> rat) \<Rightarrow> 'a list \<Rightarrow> 'a list" 
begin

abbreviation "sort_desc_axioms \<equiv> sort_desc_axioms' sort_desc"

lemma sort_desc_axioms_def: "sort_desc_axioms =(
  (\<forall>c order. sorted_wrt (\<lambda>x1 x2. c x1 \<ge> c x2) (sort_desc c order) \<and>
  set order = set (sort_desc c order) \<and> length order = length (sort_desc c order) \<and>
  (\<forall>k. filter (\<lambda>y. c y = k) (sort_desc c order) = filter (\<lambda>y. c y = k) order)))"
  using sort_desc_axioms_def by blast

definition "greedy_axioms =
  (matroid.invar carrier indep_fn \<and> matroid.finite_sets)"

abbreviation "indep' \<equiv> indep_fn"

definition "call_measure state = length (carrier_list state)"

definition "nonnegative (c::('a \<Rightarrow> rat)) = (\<forall>x. set_isin carrier x \<longrightarrow> c x \<ge> 0)"

definition "valid_order order =( to_set carrier = set order \<and> cardinality carrier = length order)"


abbreviation "subseteq \<equiv> matroid.set.subseteq"

definition
  "num_iter c order state = (length (sort_desc c order) - length (carrier_list state))"

definition
  "carrier_pref c order j = set (take j (sort_desc c order))"

definition
  "pref c order S j = S \<inter> (carrier_pref c order j)"

definition "invar_2 c order state =
  ((carrier_list state) = (drop (num_iter c order state) (sort_desc c order)))"

definition "c_set c S = sum c S"

definition "c_diff c order n j =
  (if j < n then c ((sort_desc c order) ! (j - 1)) - c ((sort_desc c order) ! j) 
  else c ((sort_desc c order) ! (j - 1)))"

definition "valid_solution X =
  (set_inv X \<and> subseteq X carrier \<and> indep' X)"

context
  includes matroid.set.custom_automation
  assumes greedy_axioms sort_desc_axioms "matroid.indep_system_axioms carrier indep_fn"
begin

lemma matroid_inv:
  "matroid.invar carrier indep_fn"
  "matroid.finite_sets"
  using \<open>greedy_axioms\<close>
  by (auto simp: greedy_axioms_def) 

lemma indep_system_axioms_abs:
  "indep_system (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn)"
  using matroid.indep_system_impl_to_abs[OF matroid_inv(1) matroid_inv(2)]
    \<open>matroid.indep_system_axioms carrier indep_fn\<close> by simp

lemma set_inv_carrier:
  "set_inv carrier"
  using \<open>greedy_axioms\<close> greedy_axioms_def by auto

lemmas simps[simp] = matroid.indep_abs_equiv[OF matroid_inv(1) matroid_inv(2)]

context
  fixes c :: "'a \<Rightarrow> rat" and order :: "'a list"
  assumes "nonnegative c" "valid_order order"
begin

abbreviation "carrier_sorted \<equiv> sort_desc c order"

lemma cost_nonnegative:
  "set_isin carrier x \<Longrightarrow> c x \<ge> 0"
  using \<open>nonnegative c\<close>
  by (auto simp: nonnegative_def) 

lemma valid_solution_c_set_nonnegative:
  "valid_solution X \<Longrightarrow> c_set c (to_set X) \<ge> 0"
proof-
  assume "valid_solution X"
  from \<open>valid_solution X\<close> valid_solution_def set_inv_carrier
  have "(to_set X) \<subseteq> (to_set carrier)"
    by force
  with set_inv_carrier \<open>nonnegative c\<close> nonnegative_def have
    "\<forall>x \<in> (to_set X). c x \<ge> 0"
    by auto
  then show "c_set c (to_set X) \<ge> 0"
    unfolding c_set_def by (simp add: sum_nonneg)
qed


lemma carrier_sorted_sorted_desc:
  "sorted_wrt (\<lambda>x1 x2. c x1 \<ge> c x2) (carrier_sorted)"
  using \<open>sort_desc_axioms\<close>
  by (auto simp: sort_desc_axioms_def) 

lemma sort_desc_stable:
  "filter (\<lambda>y. c y = k) carrier_sorted = filter (\<lambda>y. c y = k) order"
  using \<open>sort_desc_axioms\<close> sort_desc_axioms_def by auto

lemma carrier_sorted_set:
  "to_set carrier = set (carrier_sorted)"
  using \<open>sort_desc_axioms\<close> \<open>valid_order order\<close>
  by (auto simp: sort_desc_axioms_def valid_order_def)

lemma length_carrier_sorted:
  "cardinality carrier = length (carrier_sorted)"
  using \<open>sort_desc_axioms\<close> \<open>valid_order order\<close>
  by (auto simp: sort_desc_axioms_def valid_order_def)

lemma carrier_sorted_distinct:
  "distinct (carrier_sorted)"
  unfolding sort_desc_axioms_def using card_distinct set_inv_carrier matroid.set.set_cardinality 
  by (metis carrier_sorted_set length_carrier_sorted) 

text \<open>Auxiliary facts on a step of a greedy algorithm that consumes the head of the remaining list:
the head is a new element of the carrier and the number of processed elements increases by one.\<close>

lemma carrier_pref_subset:
  "carrier_pref c order j \<subseteq> to_set carrier"
  using carrier_sorted_set set_take_subset by (metis carrier_pref_def)

lemma num_iter_tl:
  assumes "invar_2 c order state" "carrier_list state \<noteq> []"
    "carrier_list state' = tl (carrier_list state)"
  shows "num_iter c order state' = Suc (num_iter c order state)"
proof-
  have "length (carrier_list state) \<le> length (sort_desc c order)"
    using assms(1) unfolding invar_2_def by (metis diff_le_self length_drop)
  moreover have "length (carrier_list state) \<noteq> 0"
    using assms(2) by simp
  ultimately show ?thesis
    unfolding num_iter_def assms(3) length_tl by arith
qed

lemma carrier_pref_tl:
  assumes "invar_2 c order state" "carrier_list state \<noteq> []"
    "carrier_list state' = tl (carrier_list state)"
  shows "carrier_pref c order (num_iter c order state') =
    insert (hd (carrier_list state)) (carrier_pref c order (num_iter c order state))"
proof-
  have "carrier_list state =
    drop (length (sort_desc c order) - length (carrier_list state)) (sort_desc c order)"
    using assms(1) unfolding invar_2_def num_iter_def .
  from set_take_aux_lemma[OF list.collapse[OF assms(2), symmetric] this]
  show ?thesis
    unfolding carrier_pref_def num_iter_def assms(3) .
qed

lemma invar_2_tl:
  assumes "invar_2 c order state" "carrier_list state \<noteq> []"
    "carrier_list state' = tl (carrier_list state)"
  shows "invar_2 c order state'"
proof-
  have "carrier_list state = drop (num_iter c order state) (sort_desc c order)"
    using assms(1) unfolding invar_2_def .
  then show ?thesis
    unfolding invar_2_def num_iter_tl[OF assms] assms(3)
    by (simp add: drop_Suc tl_drop)
qed

lemma hd_in_carrier:
  assumes "invar_2 c order state" "carrier_list state \<noteq> []"
  shows "hd (carrier_list state) \<in> to_set carrier"
proof-
  have "set (carrier_list state) \<subseteq> set (sort_desc c order)"
    using assms(1) unfolding invar_2_def by (metis set_drop_subset)
  then show ?thesis
    using hd_in_set[OF assms(2)] carrier_sorted_set by auto
qed

lemma hd_not_in_carrier_pref:
  assumes "invar_2 c order state" "carrier_list state \<noteq> []" "j \<le> num_iter c order state"
  shows "hd (carrier_list state) \<notin> carrier_pref c order j"
proof-
  have "carrier_pref c order j \<inter> set (carrier_list state) = {}"
    using set_take_disj_set_drop_if_distinct[OF carrier_sorted_distinct assms(3)] assms(1)
    unfolding carrier_pref_def invar_2_def by metis
  then show ?thesis
    using hd_in_set[OF assms(2)] by auto
qed

text \<open>The costs of a set are expressed by the cardinalities of its intersections with the prefixes of
the sorted carrier.\<close>

lemma carrier_sorted_nth_nonneg:
  "\<forall>j \<in> {1..length (sort_desc c order)}. c (sort_desc c order ! (j - 1)) \<ge> 0"
proof-
  have "\<forall>j \<in> {1..length (sort_desc c order)}. sort_desc c order ! (j - 1) \<in> to_set carrier"
    using carrier_sorted_set nth_mem by fastforce
  then show ?thesis
    using cost_nonnegative set_inv_carrier by simp
qed

lemma c_diff_nonneg:
  "\<forall>j \<in> {1..length (sort_desc c order)}. c_diff c order (length (sort_desc c order)) j \<ge> 0"
  unfolding c_diff_def using sorted_wrt_iff_nth_less carrier_sorted_nth_nonneg
  by (smt (verit, ccfv_SIG) carrier_sorted_sorted_desc diff_ge_0_iff_ge
      diff_le_self dual_order.refl nat_less_le)

lemma c_set_pref_sum:
  assumes "S \<subseteq> to_set carrier"
  shows "c_set c S = (\<Sum>j = 1..length (sort_desc c order).
    rat_of_nat (card (pref c order S j)) * c_diff c order (length (sort_desc c order)) j)"
proof-
  let ?n = "length (sort_desc c order)"
  have n: "?n = length (sort_desc c order)"
    by simp
  have set_carrier_sorted: "set (sort_desc c order) = to_set carrier"
    using carrier_sorted_set by simp
  have length_carrier_sorted': "length (sort_desc c order) = card (to_set carrier)"
    using length_carrier_sorted set_inv_carrier by auto
  have g_pos: "\<forall>j \<in> {0..?n}. rat_of_nat (card (pref c order S j)) \<ge> 0"
    by simp
  have g_zero: "rat_of_nat (card (pref c order S 0)) = 0"
    unfolding pref_def carrier_pref_def by simp
  have g_leq: "\<forall>j \<in> {1..?n}. card (pref c order S (j - 1)) \<le> card (pref c order S j)"
    unfolding pref_def carrier_pref_def
    by (meson Int_mono List.finite_set card_mono diff_le_self finite_Int order_eq_refl
        set_take_subset_set_take)
  have "c_set c S = (\<Sum>j = 1..?n. rat_of_nat (card (pref c order S j) - card (pref c order S (j - 1))) *
    c (sort_desc c order ! (j - 1)))"
    using sum_set_union_expr[OF n set_carrier_sorted length_carrier_sorted' assms] c_set_def[of c]
      carrier_pref_def[of c] pref_def[of c] by simp
  also have "\<dots> = (\<Sum>j = 1..?n. rat_of_nat (card (pref c order S j)) * c_diff c order ?n j)"
    using sum_diff_mult_distr[OF g_pos carrier_sorted_nth_nonneg g_zero]
      semiring_1_cancel_class.of_nat_diff g_leq c_diff_def
    by (smt (verit) sum.cong)
  finally show ?thesis .
qed

lemma card_pref_complement:
  "card (pref c order A j) = card (carrier_pref c order j) - card (pref c order (to_set carrier - A) j)"
proof-
  have "pref c order (to_set carrier - A) j = carrier_pref c order j - A"
    using carrier_pref_subset by (auto simp: pref_def)
  moreover have "pref c order A j = carrier_pref c order j \<inter> A"
    by (auto simp: pref_def)
  moreover have "finite (carrier_pref c order j)"
    by (simp add: carrier_pref_def)
  ultimately show ?thesis
    using card_Int_Diff[of "carrier_pref c order j" A] by simp
qed

text \<open>The two lemmas below are declared as \<open>invar_props_elims\<close>/\<open>invar_props_intros\<close> only
  where the assumptions of this context are discharged, to avoid conditional rules.\<close>

lemma invar_2_props:
  "invar_2 c order state \<Longrightarrow>
    (\<lbrakk>carrier_list state = drop (num_iter c order state) (carrier_sorted)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
    P"
  by (auto simp: invar_2_def)

lemma invar_2_intro:
  "\<lbrakk>carrier_list state = drop (num_iter c order state) (carrier_sorted)\<rbrakk> \<Longrightarrow> invar_2 c order state"
  by (auto simp: invar_2_def)

end

end

end

section \<open>Common Setup for Clients of Greedy Algorithms\<close>

text \<open>A client provides an independence system as a predicate on sets of elements, a carrier
  implemented by the set data structure, costs and an order of the carrier. The facts below relate
  the abstract independence system to the one seen by the greedy algorithms.\<close>

locale Use_Greedy_Common
  =  Indep_System_Specs +
  fixes indep_predicate input_G c order
  assumes indep_system: "indep_system (to_set input_G) indep_predicate"
  assumes indep_finite: "(\<And>X. indep_predicate X \<Longrightarrow> finite X)"
  assumes indep_in_input_G: "(\<And>X. indep_predicate X \<Longrightarrow> X \<subseteq> to_set input_G)"
  assumes G_good: "set_inv input_G"
  assumes non_negative_c:"\<And> e. e \<in> to_set input_G \<Longrightarrow> c e \<ge> (0::rat)"
  assumes order_is_G: "to_set input_G = set order"
  assumes order_length_is_G_card: "distinct order"
  assumes finite_sets: "\<And> X. finite (to_set X)"
begin

lemma indep_system_abs_lift:"
    indep_system (to_set input_G) (indep_abs (\<lambda>Z. indep_predicate (to_set Z)))"
  using indep_system indep_finite
  by(subst indep_abs_def, subst to_function_def)
    (auto simp add: to_function_def from_set_def set_correct_insert_elements indep_system_def)

lemma indep_predicate_same:"
(\<lambda>S. (finite S \<longrightarrow> indep_predicate (set (sorted_list_of_set S))) \<and> finite S) = indep_predicate"
  using indep_finite by auto

lemma indep_abs_id_indep_predicate: "(Indep_System_Specs.indep_abs set_empty set_insert (\<lambda>Z. indep_predicate (to_set Z)))
       = indep_predicate"
  apply(subst indep_abs_def)
  apply(subst to_function_def)
  apply(subst from_set_def)
  apply(subst set_correct_insert_elements)
  using  indep_system indep_finite indep_in_input_G 
  by auto

lemma indep_in_same_indep:"
    (indep_system.indep_in
       (Indep_System_Specs.indep_abs set_empty set_insert (\<lambda>Z. indep_predicate (to_set Z)))
       (Indep_System_Specs.carrier_abs to_set input_G)) = indep_predicate"
  apply(subst indep_abs_id_indep_predicate)
  apply(subst carrier_abs_def)
  using  indep_system indep_finite indep_in_input_G 
  by (fastforce simp add: indep_system.indep_in_def)

lemma basis_predicate_same:
  "(indep_system.basis (to_set input_G) (indep_predicate) S) =
(indep_system.basis_in (indep_abs (\<lambda> Z. indep_predicate (to_set Z)))(carrier_abs input_G) S)"
  apply(subst indep_system.basis_in_def[OF indep_system_abs_lift])
  apply(subst indep_in_same_indep)
  by(auto simp add: carrier_abs_def)

lemma size_G_length_order:"cardinality input_G = length order"
  by (simp add: G_good distinct_card order_is_G order_length_is_G_card set.set_cardinality)

lemma invar_input_G: "invar input_G (\<lambda>Z. indep_predicate (to_set Z))"
  by (simp add: invar_def G_good)

lemma indep_system_axioms_input_G: "indep_system_axioms input_G (\<lambda>Z. indep_predicate (to_set Z))"
  using indep_system_abs_to_impl[OF invar_input_G] indep_system_abs_lift finite_sets
  by (simp add: carrier_abs_def finite_sets_def)

lemma indep_to_set_from_set_inv:"indep_predicate S \<Longrightarrow> to_set (from_set S) = S"
  by (simp add: from_set_correct indep_finite)

end

end
