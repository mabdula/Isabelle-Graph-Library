(*
  Author: Christoph Madlener
*)

theory Bipartite_Vertex_Weighted_Matching_LP
  imports Bipartite_Matching_LP
begin

locale bipartite_vertex_weighted_matching_lp = bipartite_matching_lp +
  fixes v :: "'a \<Rightarrow> real"
  assumes weights_pos: "i \<in> L \<Longrightarrow> 0 < v i"
begin

abbreviation "matching_value M \<equiv> \<Sum>e\<in>M. v (THE l. l \<in> L \<and> l \<in> e)"

definition "max_value_matching M \<longleftrightarrow> M \<subseteq> G \<and> matching M \<and>
  (\<forall>M'. M' \<subseteq> G \<and> matching M' \<longrightarrow> matching_value M' \<le> matching_value M)"

abbreviation vertex_weighted_coeffs :: "real vec" where
  "vertex_weighted_coeffs \<equiv> vec m (\<lambda>i. v (THE l. l \<in> L \<and> l \<in> from_nat_into G i))"

lemma max_value_matchingD:
  assumes "max_value_matching M"
  shows "M \<subseteq> G" "matching M"
  using assms
  unfolding max_value_matching_def
  by auto

lemma value_pos:
  "e \<in> G \<Longrightarrow> 0 < v (THE l. l \<in> L \<and> l \<in> e)"
  by (auto elim: the_lE intro: weights_pos)

lemma max_value_matching_non_empty:
  assumes "max_value_matching M"
  assumes "G \<noteq> {}"
  shows "M \<noteq> {}"
proof (rule ccontr, simp)
  assume "M = {}"

  then have M_zero: "matching_value M = 0"
    by auto

  from assms obtain e where "e \<in> G"
    by blast

  with bipartite_graph obtain l r where lr: "e = {l,r}" "l \<in> L" "r \<in> R"
    by (auto elim: bipartite_edgeE)

  from \<open>e \<in> G\<close> have e: "matching {e}" "{e} \<subseteq> G"
    unfolding matching_def
    by blast+

  with lr have the_l: "(THE l. l \<in> L \<and> l \<in> e) = l"
    by auto

  with \<open>l \<in> L\<close> have "0 < matching_value {e}"
    by (auto dest: weights_pos)

  with M_zero e \<open>max_value_matching M\<close> show False
    unfolding max_value_matching_def
    by auto
qed

lemma non_empty_matching_value_pos:
  assumes "M \<subseteq> G"
  assumes "M \<noteq> {}"
  shows "0 < matching_value M"
  using assms
  by (auto intro!: sum_pos intro: finite_subset value_pos)

lemma primal_dot_coeffs_eq_value:
  assumes "M \<subseteq> G"
  shows "vertex_weighted_coeffs \<bullet> primal_sol M = matching_value M"
  unfolding scalar_prod_def primal_sol_def
  using assms
  by (auto intro!: sum.reindex_bij_witness[where j = "from_nat_into G" and i = "to_nat_on G"]
           intro: to_nat_on_from_nat_into_less simp: to_nat_on_less_card countable_finite)

lemma matching_value_bound_by_feasible_dual:
  fixes y :: "real vec"
  assumes "M \<subseteq> G"
  assumes "matching M"

  assumes "incidence_matrix\<^sup>T *\<^sub>v y \<ge> vertex_weighted_coeffs"
  assumes "y \<ge> 0\<^sub>v n"

  shows "matching_value M \<le> 1\<^sub>v n \<bullet> y"
proof -
  from \<open>M \<subseteq> G\<close> have "matching_value M = vertex_weighted_coeffs \<bullet> primal_sol M"
    by (auto simp: primal_dot_coeffs_eq_value)
  also from assms have "\<dots> \<le> 1\<^sub>v n \<bullet> y"
    by (auto intro!: weak_duality_theorem_nonneg_primal[where A = incidence_matrix] matching_feasible)
 finally show ?thesis .
qed

lemma max_value_matching_bound_by_feasible_dual:
  fixes y :: "real vec"
  assumes "max_value_matching M"

  assumes "incidence_matrix\<^sup>T *\<^sub>v y \<ge> vertex_weighted_coeffs"
  assumes "y \<ge> 0\<^sub>v n"

  shows "matching_value M \<le> 1\<^sub>v n \<bullet> y"
  using assms
  by (auto intro: matching_value_bound_by_feasible_dual dest: max_value_matchingD)

end

end
