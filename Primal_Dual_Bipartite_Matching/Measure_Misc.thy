theory Measure_Misc
  imports "HOL-Probability.Probability"
begin

lemma restrict_space_UNIV[simp]: "restrict_space M UNIV = M"
  unfolding restrict_space_def
  by (auto simp: measure_of_of_measure)

lemma borel_measurable_restrict_space_empty[simp,intro]:
  fixes f :: "'a \<Rightarrow> 'b :: {banach,second_countable_topology}"
  shows "f \<in> borel_measurable (restrict_space M {})"
  by (auto intro: borel_measurable_integrable simp: integrable_restrict_space)

lemma measurable_add_dim'[measurable]:
  assumes "i \<in> L"
  shows "(\<lambda>(y, Y). Y(i := y)) \<in> M i \<Otimes>\<^sub>M Pi\<^sub>M (L - {i}) M \<rightarrow>\<^sub>M Pi\<^sub>M L M" (is "?f \<in> M i \<Otimes>\<^sub>M ?PiM' \<rightarrow>\<^sub>M ?PiM")
proof -
  have "(\<lambda>(Y,y). Y(i := y)) \<in> ?PiM' \<Otimes>\<^sub>M M i \<rightarrow>\<^sub>M Pi\<^sub>M (insert i (L - {i})) M"
    by (rule measurable_add_dim)

  with assms show ?thesis
    by (subst measurable_pair_swap_iff) (auto simp: insert_absorb)
qed

lemma AE_uniform_measure_in_set_mono:
  "A \<in> sets M \<Longrightarrow> A \<subseteq> B \<Longrightarrow> AE x in uniform_measure M A. x \<in> B" 
  by (auto intro: AE_uniform_measureI)

lemma AE_PiM_uniform_measure_component_in_set:
  assumes "\<And>i. i \<in> I \<Longrightarrow> emeasure (M i) (A i) \<noteq> 0"
  assumes "\<And>i. i \<in> I \<Longrightarrow> emeasure (M i) (A i) \<noteq> \<infinity>"
  assumes "\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets (M i)"
  assumes "\<And>i. i \<in> I \<Longrightarrow> A i \<subseteq> B i"
  assumes "i \<in> I"
  shows "AE f in PiM I (\<lambda>i. uniform_measure (M i) (A i)). f i \<in> B i"
  using assms
  by (intro AE_PiM_component prob_space_uniform_measure AE_uniform_measure_in_set_mono)

lemma AE_PiM_uniform_measure_PiE_countable:
  assumes "\<And>i. i \<in> I \<Longrightarrow> emeasure (M i) (A i) \<noteq> 0"
  assumes "\<And>i. i \<in> I \<Longrightarrow> emeasure (M i) (A i) \<noteq> \<infinity>"
  assumes "\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets (M i)"
  assumes "countable I"
  shows "AE f in PiM I (\<lambda>i. uniform_measure (M i) (A i)). f \<in> Pi I A"
  using assms
  by (subst Pi_iff) (rule AE_ball_countable', intro AE_PiM_uniform_measure_component_in_set; auto)

lemma (in pair_sigma_finite) AE_pair_measure_swap:
  "AE (x,y) in M1 \<Otimes>\<^sub>M M2. P x y \<Longrightarrow> (AE (y,x) in M2 \<Otimes>\<^sub>M M1. P x y)"
  by (auto simp: case_prod_beta 
           intro!: AE_distrD[where M = "M2 \<Otimes>\<^sub>M M1" and  M' = "M1 \<Otimes>\<^sub>M M2" and P = "\<lambda>(x,y). P x y" and f = "\<lambda>(x,y). (y,x)", simplified case_prod_beta fst_conv snd_conv])
     (subst distr_pair_swap[symmetric])

lemma (in pair_sigma_finite) pair_sigma_finite_swap: "pair_sigma_finite M2 M1"
  by (simp add: M1.sigma_finite_measure_axioms M2.sigma_finite_measure_axioms pair_sigma_finite_def)

lemma ennreal_divide_one: "(x::ennreal) / 1 = x"
  unfolding divide_ennreal_def
  by simp

lemma exp_minus_One_integral_indicator:
  fixes \<theta> :: real
  assumes "0 \<le> \<theta>" "\<theta> \<le> 1"
  shows "\<integral>y. exp(y-1) * indicator {..<\<theta>} y \<partial>uniform_measure lborel {0..1} = exp(\<theta>-1) - exp(-1)"
    (is "?L = ?R")
proof -
  from \<open>\<theta> \<le> 1\<close> have interval_Int: "{..<\<theta>} \<inter> {0..1} = {0..<\<theta>}"
    unfolding atLeastLessThan_def atLeastAtMost_def lessThan_def atMost_def
    by auto

  from \<open>0 \<le> \<theta>\<close> have sym_diff_singleton: "sym_diff {0..<\<theta>} {0..\<theta>} = {\<theta>}"
    by auto

  then have *: "(\<integral>\<^sup>+x\<in>{0..<\<theta>}. f x \<partial>lborel) = (\<integral>\<^sup>+x\<in>{0..\<theta>}. f x \<partial>lborel)" for f
    by (auto intro!: nn_integral_null_delta)

  have "?L = enn2real (\<integral>\<^sup>+y. (exp(y-1) * indicator {..<\<theta>} y) \<partial>uniform_measure lborel {0..1})"
    by (auto simp: integral_eq_nn_integral)

  also have "\<dots> = enn2real (\<integral>\<^sup>+y. exp(y-1) * indicator {..<\<theta>} y * indicator {0..1} y \<partial>lborel)"
    by (subst nn_integral_uniform_measure, measurable)
       (simp add: ennreal_divide_one ennreal_mult'' flip: ennreal_indicator)

  also have "\<dots> = enn2real (\<integral>\<^sup>+y. exp(y-1) * indicator {0..<\<theta>} y \<partial>lborel)"
    using assms
    by (auto simp flip: indicator_inter_arith simp: mult.assoc interval_Int)

  also have "\<dots> = enn2real (\<integral>\<^sup>+y\<in>{0..\<theta>}. exp(y-1) \<partial>lborel)"
    by (auto simp: ennreal_mult'' ennreal_indicator *)

  also from \<open>0 \<le> \<theta>\<close> have "\<dots> = exp(\<theta> - 1) - exp(-1)"
    by (subst nn_integral_FTC_Icc[where F = "\<lambda>x. exp (x-1)"])
       (auto intro!: DERIV_fun_exp[where m = 1, simplified]
                     Deriv.field_differentiable_diff[where g' = 0, simplified])

  finally show ?thesis .
qed


end