subsection \<open>More on Graphs\label{sec:more-graph}\<close>
theory Even_More_Graph
  imports
    RANKING.More_Graph
    "HOL-Library.FuncSet"
begin

subsubsection \<open>One-sided Matchings\<close>
definition one_sided_matching :: "'a graph \<Rightarrow> 'a graph \<Rightarrow> 'a set \<Rightarrow> bool" where
  "one_sided_matching G M A = ( M \<subseteq> G \<and> (\<forall>a\<in>A. card {e\<in>M. a \<in> e} \<le> 1))"

lemma one_sided_matchingI:
  assumes "M \<subseteq> G"
  assumes "\<And>a. a \<in> A \<Longrightarrow> card {e\<in>M. a \<in> e} \<le> 1"
  shows "one_sided_matching G M A"
  unfolding one_sided_matching_def
  using assms
  by blast

lemma one_sided_matching_empty[intro,simp]:
  "one_sided_matching G {} R"
  by (auto intro: one_sided_matchingI)

lemma one_sided_matching_subgraphD: "one_sided_matching G M A \<Longrightarrow> M \<subseteq> G"
  unfolding one_sided_matching_def by blast

lemma one_sided_matching_subgraphD': "one_sided_matching G M A \<Longrightarrow> e \<in> M \<Longrightarrow> e \<in> G"
  by (auto dest: one_sided_matching_subgraphD)

lemma one_sided_matching_insertI:
  assumes "{i,j} \<in> G"
  assumes "j \<notin> Vs M"
  assumes "i \<notin> A"
  assumes "one_sided_matching G M A"
  shows "one_sided_matching G (insert {i,j} M) A"
proof (intro one_sided_matchingI)
  from assms show "insert {i,j} M \<subseteq> G"
    by (auto dest: one_sided_matching_subgraphD)
next
  fix a assume "a \<in> A"

  then show "card {e \<in> insert {i,j} M. a \<in> e} \<le> 1"
  proof (cases "a = j")
    case True
    with \<open>j \<notin> Vs M\<close> have "{e \<in> insert {i, j} M. a \<in> e} = {{i,j}}"
      by (auto simp: vs_member_intro)

    then show ?thesis
      by simp
  next
    case False
    with \<open>a \<in> A\<close> \<open>i \<notin> A\<close> have *: "{e \<in> insert {i,j} M. a \<in> e} = {e \<in> M. a \<in> e}"
      by auto

    with \<open>a \<in> A\<close> \<open>one_sided_matching G M A\<close> show ?thesis
      unfolding one_sided_matching_def
      by simp
  qed
qed


lemma matching_partner_eqI: "matching M \<Longrightarrow> {i,j} \<in> M \<Longrightarrow> {i',j} \<in> M \<Longrightarrow> i = i'"
  by (metis doubleton_eq_iff insertI1 matching_unique_match)

end
