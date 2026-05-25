(*
  Author: Christoph Madlener
*)

theory Bipartite_Vertex_Priorities
  imports 
    Matching_LPs.Bipartite_Matching_LP
    Measure_Misc
begin

lemma funcset_update:
  assumes "Y \<in> L - {i} \<rightarrow> S"
  assumes "y \<in> S"
  shows "Y(i := y) \<in> L \<rightarrow> S"
  using assms
  by auto

locale bipartite_vertex_priorities = bipartite_matching_lp
begin

abbreviation "\<U> \<equiv> uniform_measure lborel {0..1::real}"
abbreviation "\<Y> \<equiv> \<Pi>\<^sub>M i \<in> L. \<U>"

sublocale component_prob_space: prob_space \<U>
  by (auto intro: prob_space_uniform_measure)

lemmas component_prob_space.prob_space_axioms[intro]

sublocale prob_space \<Y>
  by (auto intro: prob_space_PiM)

lemma prob_space_PiM_\<U>:
  "prob_space (PiM I (\<lambda>_. \<U>))"
  by (auto intro: prob_space_PiM)

lemma emeasure_space_PiM_\<U>[simp]:
  shows "emeasure (PiM I (\<lambda>_. \<U>)) (space (PiM I (\<lambda>_. \<U>))) = 1"
  by (intro prob_space.emeasure_space_1 prob_space_PiM_\<U>)

lemma pair_sigma_finite_split_dim[intro]: "pair_sigma_finite \<U> (Pi\<^sub>M (L - {i}) (\<lambda>i. \<U>))"
  by (intro pair_sigma_finite.intro prob_space_imp_sigma_finite prob_space_PiM) blast+

lemmas pair_sigma_finite_split_dim'[intro] = pair_sigma_finite.pair_sigma_finite_swap[OF pair_sigma_finite_split_dim]

lemma AE_PiM_subset_L_\<U>_funcset:
  assumes "L' \<subseteq> L"
  shows "AE Y in \<Pi>\<^sub>M i \<in> L'. \<U>. Y \<in> L' \<rightarrow> {0..1}"
  using finite_L assms
  by (intro AE_PiM_uniform_measure_PiE_countable)
     (auto intro: countable_finite finite_subset)

lemmas AE_\<Y>_funcset = AE_PiM_subset_L_\<U>_funcset[where L' = L, OF subset_refl]

lemma AE_\<U>_in_range: "AE y in \<U>. y \<in> {0..1}"
  by (auto intro: AE_uniform_measureI)

lemma AE_add_dim_in_range:
  "AE (y,Y) in (\<U> \<Otimes>\<^sub>M Pi\<^sub>M (L - {i}) (\<lambda>i. \<U>)). y \<in> {0..1}"
  by (subst pair_sigma_finite.AE_pair_measure_swap)
     (auto simp: case_prod_beta space_pair_measure intro!: pair_sigma_finite.AE_pair_measure AE_uniform_measureI)

lemma AE_add_dim_funcset:
  "AE (y,Y) in (\<U> \<Otimes>\<^sub>M Pi\<^sub>M (L - {i}) (\<lambda>i. \<U>)). Y \<in> L - {i} \<rightarrow> {0..1}"
  using finite_L
  by (auto intro!: pair_sigma_finite.AE_pair_measure AE_PiM_subset_L_\<U>_funcset simp: case_prod_beta space_pair_measure)

lemma AE_split_dim_funcset:
  shows "AE (y, Y) in \<U> \<Otimes>\<^sub>M Pi\<^sub>M (L - {i}) (\<lambda>i. \<U>). Y(i := y) \<in> L \<rightarrow> {0..1}"
  using AE_add_dim_in_range AE_add_dim_funcset
  by eventually_elim auto

lemma AE_\<U>_funcset:
  "i \<in> L \<Longrightarrow> Y \<in> L - {i} \<rightarrow> {0..1} \<Longrightarrow> AE y in \<U>. Y(i:=y) \<in> L \<rightarrow> {0..1}"
  using AE_\<U>_in_range
  by eventually_elim auto


end

end
