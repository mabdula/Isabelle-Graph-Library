(*
  Author: Christoph Madlener
*)

theory Order_Relations
  imports Comparison_Sort_Lower_Bound.Linorder_Relations
begin


text \<open>Weaker versions of \<^term>\<open>refl_on\<close> (and \<^term>\<open>preorder_on\<close>/\<^term>\<open>linorder_on\<close>) that don't enforce
that the relation is only defined on the given set. Alternative would be to weaken later lemmas
by using stronger assumptions.\<close>
definition "refl_on' S r \<longleftrightarrow> (\<forall>x\<in>S. (x,x) \<in> r)"
definition "preorder_on' S r \<longleftrightarrow> refl_on' S r \<and> trans r"
definition "linorder_on' S r \<longleftrightarrow> refl_on' S r \<and> antisym r \<and> trans r \<and> total_on S r"

definition "preorders_on S = {r. preorder_on S r}"


lemma refl_on'D: "refl_on' S r \<Longrightarrow> a \<in> S \<Longrightarrow> (a,a) \<in> r"
  unfolding refl_on'_def
  by blast

lemma refl_on'_Restr: "refl_on' S r \<Longrightarrow> refl_on' S (Restr r S)"
  unfolding refl_on'_def
  by blast

lemma linorder_on'_refl_on'D: "linorder_on' S r \<Longrightarrow> refl_on' S r"
  unfolding linorder_on'_def
  by blast

lemma linorder_on'_transD: "linorder_on' S r \<Longrightarrow> trans r"
  unfolding linorder_on'_def
  by blast

lemma linorder_on'_antisymD: "linorder_on' S r \<Longrightarrow> antisym r"
  unfolding linorder_on'_def
  by blast

lemma preorders_onD: "r \<in> preorders_on S \<Longrightarrow> preorder_on S r"
  unfolding preorders_on_def
  by blast

lemma preorders_onI[intro]: "preorder_on S r \<Longrightarrow> r \<in> preorders_on S"
  unfolding preorders_on_def
  by blast

lemma preorder_on_subset_Times: "preorder_on S r \<Longrightarrow> r \<subseteq> S \<times> S"
  unfolding preorder_on_def
  by (auto dest: refl_onD1 refl_onD2)

lemma preorders_on_subset_Pow: "preorders_on S \<subseteq> Pow (S \<times> S)"
  by (auto dest: preorders_onD preorder_on_subset_Times)

lemma finite_preorders_on[intro]:
  assumes "finite S"
  shows "finite (preorders_on S)"
  using assms
  by (auto intro: finite_subset[OF preorders_on_subset_Pow])

lemma refl_on_imp_refl_on': "refl_on S r \<Longrightarrow> refl_on' S r"
  unfolding refl_on_def refl_on'_def
  by blast

lemma linorder_on_imp_linorder_on': "linorder_on S r \<Longrightarrow> linorder_on' S r"
  unfolding linorder_on_def linorder_on'_def
  by (auto dest: refl_on_imp_refl_on')

lemma linorder_on_imp_preorder_on: "linorder_on S r \<Longrightarrow> preorder_on S r"
  unfolding linorder_on_def preorder_on_def
  by blast

lemma linorder_on'_imp_preorder_on': "linorder_on' S r \<Longrightarrow> preorder_on' S r"
  unfolding linorder_on'_def preorder_on'_def
  by blast

lemma preorder_on_imp_preorder_on': "preorder_on S r \<Longrightarrow> preorder_on' S r"
  unfolding preorder_on_def preorder_on'_def
  by (blast intro: refl_on_imp_refl_on')

lemma refl_on'_subset:
  "refl_on' S r \<Longrightarrow> T \<subseteq> S \<Longrightarrow> refl_on' T r"
  unfolding refl_on'_def
  by blast

lemma linorder_on'_subset:
  "linorder_on' S r \<Longrightarrow> T \<subseteq> S \<Longrightarrow> linorder_on' T r"
  unfolding linorder_on'_def
  by (auto intro: refl_on'_subset total_on_subset)

lemma preorder_on'_subset:
  "preorder_on' S r \<Longrightarrow> T \<subseteq> S \<Longrightarrow> preorder_on' T r"
  unfolding preorder_on'_def
  by (auto intro: refl_on'_subset total_on_subset)

lemma total_on_Restr:
  "total_on S r \<Longrightarrow> total_on S (Restr r S)"
  unfolding total_on_def
  by blast

lemma linorder_on'_Restr:
  "linorder_on' S r \<Longrightarrow> linorder_on' S (Restr r S)"
  unfolding linorder_on'_def
  by (auto intro: refl_on'_Restr antisym_subset trans_Restr total_on_Restr)

definition is_min_rel :: "('a \<Rightarrow> bool) \<Rightarrow> 'a rel \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_min_rel P r x = (P x \<and> (\<nexists>y. P y \<and> (y, x) \<in> r \<and> (x, y) \<notin> r))"

definition min_rel :: "('a \<Rightarrow> bool) \<Rightarrow> 'a rel \<Rightarrow> 'a" where
  "min_rel P r = (SOME x. is_min_rel P r x)"

\<comment> \<open>use \<^term>\<open>Restr\<close> to make minimum deterministic in some cases\<close>
definition min_on_rel :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a" where
  "min_on_rel S r = min_rel (\<lambda>x. x \<in> S) (Restr r S)"

lemma ex_min_if_finite:
  "\<lbrakk> finite S; S \<noteq> {}; preorder_on' S r \<rbrakk> \<Longrightarrow> \<exists>m\<in>S. \<not>(\<exists>x\<in>S. (x,m) \<in> Restr r S \<and> (m,x) \<notin> Restr r S)"
proof (induction arbitrary: r rule: finite.induct)
  case (insertI A a)
  then show ?case
  proof (cases "A \<noteq> {}")
    case True
    from insertI have "preorder_on' A r"
      by (auto intro: preorder_on'_subset)

    with True insertI obtain m where m: "m\<in>A" "\<not>(\<exists>x\<in>A. (x,m) \<in> r \<and> (m,x) \<notin> r)"
      by blast

    with \<open>preorder_on' (insert a A) r\<close> show ?thesis
      unfolding preorder_on'_def
      by (auto dest: transD)
  qed simp
qed simp

lemma ex_is_min_if_finite:
  assumes "preorder_on' S r"
  assumes "finite S" "S \<noteq> {}"
  shows "\<exists>x. is_min_rel (\<lambda>x. x \<in> S) (Restr r S) x"
  using assms
  unfolding is_min_rel_def
  using ex_min_if_finite
  by fast

lemma min_if_finite':
  assumes "preorder_on' S r"
  assumes "finite S" "S \<noteq> {}"
  shows "min_on_rel S r \<in> S" and "\<not>(\<exists>x\<in>S. (x, min_on_rel S r) \<in> Restr r S \<and> (min_on_rel S r, x) \<notin> Restr r S)"
  using assms
  by (metis ex_is_min_if_finite is_min_rel_def min_on_rel_def min_rel_def some_eq_ex)+

lemma min_if_finite:
  assumes "preorder_on' S r"
  assumes "finite S" and "S \<noteq> {}"
  shows "min_on_rel S r \<in> S"
    and "\<not>(\<exists>x\<in>S. (x, min_on_rel S r) \<in> r \<and> (min_on_rel S r, x) \<notin> r)"
  using assms min_if_finite' by force+

lemma min_rel_linorder_eq:
  assumes "linorder_on' {x. P x} r"
  assumes "P a"
  assumes "\<forall>y. P y \<longrightarrow> (a,y) \<in> r"
  shows "min_rel P r = a"
  unfolding min_rel_def is_min_rel_def
  by (rule someI2[of _ a])
     (use assms in \<open>auto simp add: antisym_def linorder_on'_def\<close>)

lemma min_on_rel_linorder_eq:
  assumes "linorder_on' S r"
  assumes "a \<in> S"
  assumes "\<forall>y\<in>S. (a,y) \<in> r"
  shows "min_on_rel S r = a"
  using assms
  unfolding min_on_rel_def
  by (auto intro!: min_rel_linorder_eq intro: linorder_on'_Restr)

lemma min_on_rel_singleton:
  shows "min_on_rel {a} r = a"
  by (auto simp: min_on_rel_def min_rel_def is_min_rel_def)

lemma min_on_rel_least:
  assumes "linorder_on' S r"
  assumes S: "finite S" "S \<noteq> {}"
  assumes "y \<in> S"
  shows "(min_on_rel S r, y) \<in> r"
  using S assms
proof (induction S arbitrary: y rule: finite_induct)
  case (insert s S)

  show ?case
  proof (cases "S = {}")
    case True
    with insert.prems show ?thesis
      by (auto simp: min_on_rel_singleton linorder_on'_def refl_on'_def)
  next
    case False
    let ?min = "min_on_rel S r"

    from insert.prems False have IH: "y' \<in> S \<Longrightarrow> (?min, y') \<in> r" for y'
      by (intro insert.IH) (auto intro: linorder_on'_subset)

    from False insert.prems have "?min \<in> S"
      by (auto intro: min_if_finite linorder_on'_imp_preorder_on' dest: linorder_on'_subset)

    with insert.prems
    consider (less) "(s, ?min) \<in> r" "(?min, s) \<notin> r" | (eq) "(s, ?min) \<in> r" "(?min, s) \<in> r" | (gt) "(s, ?min) \<notin> r" "(?min, s) \<in> r"
      unfolding total_on_def linorder_on'_def refl_on'_def
      by force

    then show ?thesis
    proof cases
      case less
      with insert.prems have "min_on_rel (insert s S) r = s"
        by (intro min_on_rel_linorder_eq)
           (auto dest: linorder_on'_refl_on'D refl_on'D linorder_on'_transD IH transD)

      with insert.prems less show ?thesis
        by (auto dest: linorder_on'_refl_on'D refl_on'D linorder_on'_transD IH transD)
    next
      case eq
      with insert.prems \<open>?min \<in> S\<close> \<open>s \<notin> S\<close> have "min_on_rel (insert s S) r = s"
        by (auto dest!: linorder_on'_antisymD simp: antisym_def) blast+

      with insert.prems eq show ?thesis
        by (auto dest: linorder_on'_refl_on'D refl_on'D linorder_on'_transD IH transD)
    next
      case gt
      with insert.prems \<open>?min \<in> S\<close> have "min_on_rel (insert s S) r = ?min"
        by (intro min_on_rel_linorder_eq) (auto dest: IH)

      with insert.prems gt show ?thesis
        by (auto dest: IH)
    qed
  qed
qed blast

subsection \<open>\<^term>\<open>\<pi> permutes A\<close>\<close>
lemma refl_on_permutes: "refl_on A r \<Longrightarrow> \<pi> permutes A \<Longrightarrow> refl_on A {(x,y). x \<in> A \<and> y \<in> A \<and> (\<pi> x, \<pi> y) \<in> r}"
  unfolding refl_on_def
  by (auto simp: permutes_in_image)

lemma trans_permutes: "trans r \<Longrightarrow> trans {(x,y). x \<in> A \<and> y \<in> A \<and> (\<pi> x, \<pi> y) \<in> r}"
  unfolding trans_def
  by auto

lemma preorder_on_permutes: "preorder_on A r \<Longrightarrow> \<pi> permutes A \<Longrightarrow> preorder_on A {(x,y). x \<in> A \<and> y \<in> A \<and> (\<pi> x, \<pi> y) \<in> r}"
  unfolding preorder_on_def
  by (auto intro: refl_on_permutes trans_permutes)
  
end
