theory Kruskal_Min
  imports Kruskal
begin

provenance ai_human

section \<open>Kruskal's Algorithm for Minimum Spanning Forests\<close>

text \<open>Kruskal's algorithm computes a minimum-weight spanning forest if it is run with the negated
  costs. The correctness theorems for the maximum version require nonnegative costs, which the
  negated costs are in general not. Instead, we use that the algorithm only depends on the
  costs through the sorted list of edges: if sorting by the negated costs \<open>- c\<close> yields the same
  list as sorting by the shifted costs \<open>M - c\<close> (for an upper bound \<open>M\<close> of the costs), then the
  algorithm computes the same result for both. The shifted costs are nonnegative, and the result
  is a maximum-weight spanning forest w.r.t. them. Since all spanning forests have the same
  number of edges (they are the bases of the graphic matroid), this result is a minimum-weight
  spanning forest w.r.t. the original costs \<open>c\<close>.

  Note that there are no assumptions on the signs of the costs \<open>c\<close>. The bound \<open>M\<close> is only needed
  for the proof, it is not used by the algorithm.\<close>

context Kruskal
begin

lemma kruskal_sort_eq:
  "sort_desc c1 order = sort_desc c2 order \<Longrightarrow> kruskal c1 = kruskal c2"
  by (simp add: kruskal_def kruskal_greedy.initial_state'_def)

theorem kruskal_min_weight:
  assumes "\<And>e. e \<in> set order \<Longrightarrow> c e \<le> M"
    and "sort_desc (\<lambda>e. - c e) order = sort_desc (\<lambda>e. M - c e) order"
  shows "set (kruskal_result (\<lambda>e. - c e)) \<subseteq> set order"
    "graph_abs.is_spanning_forest E (set_of_edge ` set (kruskal_result (\<lambda>e. - c e)))"
    "\<And>X. X \<subseteq> set order \<Longrightarrow> graph_abs.is_spanning_forest E (set_of_edge ` X) \<Longrightarrow>
      sum c (set (kruskal_result (\<lambda>e. - c e))) \<le> sum c X"
proof -
  let ?c' = "\<lambda>e. M - c e"
  let ?R = "set (kruskal_result (\<lambda>e. - c e))"
  have nonneg: "\<And>e. e \<in> set order \<Longrightarrow> ?c' e \<ge> 0"
    using assms(1) by simp
  have R: "?R = set (kruskal_result ?c')"
    using kruskal_sort_eq[OF assms(2)] by simp
  show sub: "?R \<subseteq> set order"
    using kruskal_subset[OF nonneg] R by simp
  show sf: "graph_abs.is_spanning_forest E (set_of_edge ` ?R)"
    using kruskal_spanning_forest[OF nonneg] R by simp
  fix X
  assume X: "X \<subseteq> set order" "graph_abs.is_spanning_forest E (set_of_edge ` X)"
  have bases: "indep_system.basis (set order) kruskal_indep_abs X"
    "indep_system.basis (set order) kruskal_indep_abs ?R"
    using basis_iff_spanning_forest X sub sf by auto
  have card: "card X = card ?R"
    using matroid.basis_card[OF kruskal_matroid bases] .
  have "kruskal_indep_abs X"
    using indep_system.basis_indep[OF kruskal_indep_system bases(1)] .
  hence "graph_abs.has_no_cycle E (set_of_edge ` X)"
    by (simp add: kruskal_indep_abs_def)
  hence "sum ?c' X \<le> sum ?c' ?R"
    using kruskal_max_weight[OF nonneg X(1)] R by simp
  thus "sum c ?R \<le> sum c X"
    using card by (simp add: sum_subtractf)
qed

end

end
