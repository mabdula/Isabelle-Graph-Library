theory More_Lattices_Big
  imports Main
begin


lemma ex_max_if_finite:
  "\<lbrakk> finite S; S \<noteq> {} \<rbrakk> \<Longrightarrow> \<exists>m\<in>S. \<not>(\<exists>x\<in>S. (m::'a::order) < x)"
  by (induction rule: finite.induct)
     (auto intro: order.strict_trans)

lemma ex_is_arg_max_if_finite: fixes f :: "'a \<Rightarrow> 'b :: order"
  shows "\<lbrakk> finite S; S \<noteq> {} \<rbrakk> \<Longrightarrow> \<exists>x. is_arg_max f (\<lambda>x. x \<in> S) x"
  unfolding is_arg_max_def
  using ex_max_if_finite[of "f ` S"]
  by auto

lemma arg_max_SOME_Max:
  "finite S \<Longrightarrow> arg_max_on f S = (SOME y. y \<in> S \<and> f y = Max (f ` S))"
  unfolding arg_max_on_def arg_max_def is_arg_max_linorder
  by (auto intro!: arg_cong[where f = Eps] Max_eqI[symmetric] simp: fun_eq_iff)

lemma arg_max_if_finite: fixes f :: "'a \<Rightarrow> 'b :: order"
  assumes "finite S" "S \<noteq> {}"
  shows "arg_max_on f S \<in> S" and "\<not>(\<exists>x\<in>S. f (arg_max_on f S) < f x)"
  using ex_is_arg_max_if_finite[OF assms, of f]
  unfolding arg_max_on_def arg_max_def is_arg_max_def
  by (auto dest!: someI_ex)

lemma arg_max_greatest: fixes f :: "'a \<Rightarrow> 'b :: linorder"
  shows "\<lbrakk> finite S; y \<in> S \<rbrakk> \<Longrightarrow> f y \<le> f (arg_max_on f S)"
proof -
  assume "finite S" "y \<in> S"
  then have "S \<noteq> {}"
    by blast

  from \<open>y \<in> S\<close> show ?thesis
    using arg_max_if_finite[OF \<open>finite S\<close> \<open>S \<noteq> {}\<close>]
    by (auto intro: leI)
qed

end