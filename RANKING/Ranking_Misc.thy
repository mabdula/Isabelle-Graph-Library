(*
  Author: Christoph Madlener
*)
subsection\<open>Miscellaneous Preliminaries\label{sec:misc}\<close>
theory Ranking_Misc
  imports
    Complex_Main
    "HOL-Library.FuncSet"
    "HOL-Probability.Probability"
    "Monad_Normalisation.Monad_Normalisation"
    "HOL-Library.LaTeXsugar"
begin

text \<open>
  This theory contains auxiliary lemmas for the probabilistic part, i.e.\ mainly inequalities
  including sums, rewriting \<^term>\<open>infsetsum\<close>s to \<^term>\<open>sum\<close>s in the finite probability spaces we deal
  with and some material on \<^typ>\<open>'a pmf\<close>s.
\<close>

lemma bounded_by_sum_bounds_sum_aux:
  fixes x :: "nat \<Rightarrow> real"
  assumes "n > 0"
  assumes "1 - x (Suc t) \<le> 1/n * (\<Sum>s\<le>Suc t. x s)"
  shows "(\<Sum>s\<le>(Suc t). x s) \<ge> (1+(\<Sum>s\<le>t. x s)) / (1 + 1/n)"
  using assms
proof -
  from assms have "1 + (\<Sum>s\<le>t. x s) \<le> (\<Sum>s\<le>Suc t. x s) + 1/n * (\<Sum>s\<le>Suc t. x s)"
    by fastforce

  then have "1 + (\<Sum>s\<le>t. x s) \<le> (\<Sum>s\<le>Suc t. x s) * (1 + 1/n)"
    by argo

  with assms show ?thesis
    by (auto intro!: mult_imp_div_pos_le simp: add_pos_pos)
qed

lemma bounded_by_sum_bounds_sum:
  fixes x :: "nat \<Rightarrow> real"
  assumes "\<And>t. t < n \<Longrightarrow> 1 - x t \<le> 1/n * (\<Sum>s\<le>t. x s)"
  assumes "1 - 1/(n+1) \<le> x 0"
  assumes "t < (n::nat)"
  assumes "0 < n"
  shows "(\<Sum>s\<le>t. x s) \<ge> (\<Sum>s\<le>t. (1 - 1/(n+1))^(s+1))"
  using assms
proof (induction t)
  case 0
  then show ?case
    by simp
next
  case (Suc t)

  then have IH: "(\<Sum>s\<le>t. x s) \<ge> (\<Sum>s\<le>t. (1-1/(real n+1))^(s+1))"
    by (auto intro: Suc.IH)

  from Suc have bound_rewrite_sum: "(\<Sum>s\<le>Suc t. x s) \<ge> (1+(\<Sum>s\<le>t. x s)) / (1+1/n)"
    by (intro bounded_by_sum_bounds_sum_aux) simp

  have "(1+(\<Sum>s\<le>t. x s)) / (1+1/n) = (1 - 1/(n+1)) * (1 + (\<Sum>s\<le>t. x s))" (is "?LHS = _")
    using \<open>n > 0\<close>
    by (simp add: field_simps)

  also have "\<dots> = (1 - 1/(n+1)) + (1-1/(n+1)) * (\<Sum>s\<le>t. x s)"
    by argo

  also have "\<dots> \<ge> (1-1/(n+1)) + (1-1/(n+1))*(\<Sum>s\<le>t. (1-1/(real n+1))^(s+1))" (is "_ \<ge> ?S2")
    using IH
    by (auto intro: add_left_mono mult_left_mono)

  finally have IH_applied: "?LHS \<ge> ?S2" .

  have "?S2 = (1-1/(n+1)) + (\<Sum>s\<le>t. (1-1/(n+1))^(s+2))"
    by (auto simp: sum_distrib_left field_simps)

  also have "\<dots> = (1-1/(n+1)) + (\<Sum>s\<in>{0+1..t+1}. (1-1/(n+1))^(s+1))"
    by (subst sum.atLeastAtMost_shift_bounds)
       (auto simp: atLeast0AtMost)

  also have "\<dots> = (1-1/(n+1)) + (\<Sum>s=Suc 0..Suc t. (1-1/(n+1))^(s+1))"
    by simp

  also have "\<dots> = (1-1/(n+1))^(0+1) + (\<Sum>s=Suc 0..Suc t. (1-1/(n+1))^(s+1))"
    by simp

  also have "\<dots> = (\<Sum>s\<le>Suc t. (1-1/(n+1))^(s+1))" (is "_ = ?RHS")
  proof (cases t)
    case (Suc n)
    then show ?thesis
      by (simp only: sum.atMost_shift sum.atLeast_Suc_atMost_Suc_shift atLeast0AtMost lessThan_Suc_atMost)
         simp
  qed simp

  finally have final: "?S2 = ?RHS" .

  show ?case 
    by (intro order_trans[OF _ bound_rewrite_sum] ord_eq_le_trans[OF _ IH_applied], subst final)
       (simp add: ac_simps)
qed

lemma pos_pow_plus_nonneg_neq_0: "0 < (a::real) \<Longrightarrow> 0 \<le> b \<Longrightarrow> a ^ n + b = 0 \<Longrightarrow> False"
  by (auto dest: zero_less_power[of a n] simp: add_eq_0_iff)

lemma pow_n_plus_n_times_pow_n_neq_0: "(1 + real n) ^ n + real n * (1 + real n) ^ n = 0 \<Longrightarrow> False"
  by (auto intro!: pos_pow_plus_nonneg_neq_0[of "1 + real n" "real n * (1 + real n) ^ n"])

lemma sum_gp_strict_Suc: "(\<Sum>s<n. (1 - 1/(n+1))^(s+1)) = n - n*(n/(n+1))^n" (is "?L = ?R")
proof -
  have "?L = (1 - 1/(n+1)) * (\<Sum>s<n. (1-1/(n+1))^s)"
    by (auto simp: sum_distrib_left)

  also have "\<dots> = (1-1/(n+1)) * (1-(1-1/(n+1))^n)/(1/(n+1))"
    by (auto simp: sum_gp_strict)

  also have "\<dots> = ?R"
    by (auto simp: field_split_simps dest: pow_n_plus_n_times_pow_n_neq_0)

  finally show ?thesis .
qed

lemma card_singleton_UN:
  assumes "\<forall>x \<in> X. \<exists>y. x = {y}"
  shows "card (\<Union> X) = card X"
  using assms
  by (auto intro!: bij_betw_same_card[of "\<lambda>x. {x}"] intro!: bij_betwI[where g = "\<lambda>X. (THE x. X = {x})"])

lemma expectation_sum_pmf_of_set:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> real"
  assumes "S \<noteq> {}" "finite S"
  shows "measure_pmf.expectation (pmf_of_set S) (\<lambda>e. \<Sum>x\<in>A. f x e) =
    (\<Sum>x\<in>A. measure_pmf.expectation (pmf_of_set S) (\<lambda>e. f x e))"
  using assms
  by (simp add: integral_pmf_of_set flip: sum_divide_distrib, subst sum.swap) blast

lemma bool_pmf_is_bernoulli_pmf:
  "\<exists>p. bool_pmf = bernoulli_pmf p \<and> 0 \<le> p \<and> p \<le> 1"
  by (auto simp: pmf_eq_iff)
     (metis (full_types) pmf_False_conv_True pmf_bernoulli_True pmf_le_1 pmf_nonneg)

lemma bool_pmf_is_bernoulli_pmfE:
  obtains p where "bool_pmf = bernoulli_pmf p" "0 \<le> p" "p \<le> 1"
  using bool_pmf_is_bernoulli_pmf
  by blast

lemma bernoulli_prob_True_expectation:
  "measure_pmf.prob p {True} = measure_pmf.expectation p of_bool"
proof -
  obtain p' where p': "p = bernoulli_pmf p'" "0 \<le> p'" "p' \<le> 1"
    using bool_pmf_is_bernoulli_pmfE by blast

  then show ?thesis
    by (auto simp: measure_pmf_single)
qed

lemma indicator_singleton: "indicator {x} y = (if  x = y then 1 else 0)"
  by (auto simp add: indicator_eq_1_iff)

lemma sum_eq_card_where_One:
  assumes "finite A"
  assumes "card {x \<in> A. f x = 1} = n"
  assumes "\<forall>x. f x \<noteq> 0 \<longrightarrow> f x = 1"
  shows "sum f A = real n"
proof -
  have "sum f A = sum f ({a \<in> A. f a = 0} \<union> {a \<in> A. f a \<noteq> 0})"
    by (auto intro: sum.cong)

  also have "\<dots> = sum f {a \<in> A. f a = 0} + sum f {a \<in> A. f a \<noteq> 0}"
    by (rule sum.union_disjoint)
       (use \<open>finite A\<close> in auto)

  also have "\<dots> = sum f {a \<in> A. f a \<noteq> 0}"
    by (auto intro: sum.neutral)

  also have "\<dots> = sum f {a \<in> A. f a = 1}"
    using \<open>\<forall>x. f x \<noteq> 0 \<longrightarrow> f x = 1\<close>
    by (metis zero_neq_one)

  also have "\<dots> = n"
    using assms
    by simp

  finally show ?thesis .
qed

lemma infsetsum_sum_cong:
  assumes "finite {a \<in> A. f a \<noteq> 0}"
  assumes "finite B"
  assumes "\<And>a. a \<in> B - A \<Longrightarrow> f a = 0"
  assumes "\<And>a. a \<in> B - A \<Longrightarrow> g a = 0"
  assumes "\<And>a. a \<in> A \<Longrightarrow> f a \<noteq> 0 \<Longrightarrow> a \<in> B"
  assumes "\<And>a. a \<in> A \<Longrightarrow> a \<in> B \<Longrightarrow> f a = g a"
  shows "infsetsum f A = sum g B"
proof -
  have "infsetsum f A = infsetsum g B"
    using assms
    by (intro infsetsum_cong_neutral) blast+

  also have "\<dots> = sum g B"
    using assms
    by simp

  finally show ?thesis .
qed

lemma bool_pmf_imp_prob_leq:
  assumes finite_support: "finite (set_pmf p)"
  assumes imp: "\<forall>\<sigma> \<in> set_pmf p. P \<sigma> \<longrightarrow> Q \<sigma>"
  shows "measure_pmf.prob (do {\<sigma> \<leftarrow> p; return_pmf (P \<sigma>)}) {True} \<le> measure_pmf.prob (do {\<sigma> \<leftarrow> p; return_pmf (Q \<sigma>)}) {True}"
proof -
  have "infsetsum (\<lambda>x. pmf p x * (if P x then 1 else 0)) UNIV = infsetsum (\<lambda>x. pmf p x * (if P x then 1 else 0)) (set_pmf p)"
    by (auto simp: set_pmf_iff intro: infsetsum_cong_neutral)

  also have "\<dots> = sum (\<lambda>x. pmf p x * (if P x then 1 else 0)) (set_pmf p)"
    using finite_support by simp

  also have "\<dots> \<le> sum (\<lambda>x. pmf p x * (if Q x then 1 else 0)) (set_pmf p)"
    using imp
    by (simp add: sum_mono)

  also have "\<dots> = infsetsum (\<lambda>x. pmf p x * (if Q x then 1 else 0)) (set_pmf p)"
    using finite_support by simp

  also have "\<dots> = infsetsum (\<lambda>x. pmf p x * (if Q x then 1 else 0)) UNIV"
    by (auto simp: set_pmf_iff intro: infsetsum_cong_neutral)

  finally have "infsetsum (\<lambda>x. pmf p x * (if P x then 1 else 0)) UNIV \<le> infsetsum (\<lambda>x. pmf p x * (if Q x then 1 else 0)) UNIV" .

  then show ?thesis
    by (auto simp: pmf_bind measure_pmf_conv_infsetsum pmf_expectation_eq_infsetsum indicator_singleton)
qed

lemma bind_bind_pair_pmf:
  includes monad_normalisation
  shows
  "do {
    x \<leftarrow> p1;
    y \<leftarrow> p2;
    return_pmf (f x y)
   }
   =
   do {
    (x,y) \<leftarrow> pair_pmf p1 p2;
    return_pmf (f x y)
   }"
  by (simp add: pair_pmf_def)

lemma bool_pmf_imp_prob_leq2:
  assumes finite_support: "finite (set_pmf p1)" "finite (set_pmf p2)"
  assumes imp: "\<forall>x\<in>set_pmf p1. \<forall>y\<in>set_pmf p2. P x y \<longrightarrow> Q x y"
  shows "measure_pmf.prob (do {x \<leftarrow> p1; y \<leftarrow> p2; return_pmf (P x y)}) {True} \<le>
    measure_pmf.prob (do {x \<leftarrow> p1; y \<leftarrow> p2; return_pmf (Q x y)}) {True}" (is "?L \<le> ?R")
proof -
  have "?L =
    measure_pmf.prob (do {xy \<leftarrow> pair_pmf p1 p2; return_pmf (P (fst xy) (snd xy))}) {True}"
    by (simp add: bind_bind_pair_pmf case_prod_beta')

  also have "\<dots> \<le> measure_pmf.prob (do {xy \<leftarrow> pair_pmf p1 p2; return_pmf (Q (fst xy) (snd xy))}) {True}"
    using assms
    by (auto intro!: bool_pmf_imp_prob_leq)

  also have "\<dots> = ?R"
    by (simp add: bind_bind_pair_pmf case_prod_beta')

  finally show "?L \<le> ?R" .
qed

lemma card_True: "card {x. x} = 1"
proof -
  have "{x. x} = {True}"
    by blast

  then show ?thesis
    by simp
qed

lemma snd_some_disj: "snd (SOME x. x = (0, k) \<or> x = (Suc 0, k)) = k"
proof -
  let ?some = "SOME x. x = (0,k) \<or> x =(Suc 0,k)"
  have "?some = (0,k) \<or> ?some = (Suc 0, k)"
    by (auto intro!: someI)

  then show ?thesis
    by auto
qed
end
