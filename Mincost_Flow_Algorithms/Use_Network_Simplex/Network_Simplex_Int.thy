theory Network_Simplex_Int
  imports Network_Simplex_Initial_Basis_Selector
begin

provenance ai


section \<open>The integer instance\<close>

text \<open>The executable pipeline is generic over a linearly ordered integral domain @{typ 'n} that embeds into
      the reals via @{locale real_embedding}. Here @{typ 'n} is @{typ int} and the embedding is @{const of_int}:
      the generic correctness statement becomes one about an arbitrary-precision integer program, and code
      generation emits SML \<open>IntInf\<close>, OCaml \<open>zarith\<close> or Haskell \<open>Integer\<close>
      arithmetic --- no floating point.\<close>

interpretation int_embedding: real_embedding "of_int :: int \<Rightarrow> real"
  by unfold_locales simp_all

text \<open>The integer solver locale. Every assumption is a condition on the input lists alone: the obligations
      of @{locale real_embedding} are discharged once and for all by @{const of_int}.\<close>

locale \<^marker>\<open>provenance ai_human\<close> int_selector =
  initial_basis_code_spec where capacity_list = capacity_list
  for capacity_list :: "int list" +
  assumes length_edges: "length capacity_list = m"
      and length_cost: "length cost_list = length capacity_list"
      and length_fst: "length fst_list = length capacity_list"
      and length_snd: "length snd_list = length capacity_list"
      and length_flow: "length flow_list = length capacity_list"
      and length_b: "length b_list = n"
      and cap_neg: "\<forall> c \<in> set capacity_list. 0 \<le> c \<or> c = - 1"
      and edges_in_range: "set fst_list \<union> set snd_list \<subseteq> {1..n}"
      and num_edges_gtr_0: "m > 0"
      and isolated_zero:
        "\<And>i. \<lbrakk>i < n; Suc i \<notin> set fst_list \<union> set snd_list\<rbrakk>
              \<Longrightarrow> b_list ! i = 0"
      and flow_nonneg: "\<And>e. e < m \<Longrightarrow> 0 \<le> flow_list ! e"
      and flow_le_cap:
        "\<And>e. \<lbrakk>e < m; capacity_list ! e \<noteq> - 1\<rbrakk>
              \<Longrightarrow> flow_list ! e \<le> capacity_list ! e"
      and balance_sum_zero: "sum_list b_list = 0"
      and block_size_pos: "0 < block_size"
      and min_candidates_pos: "0 < min_candidates"
      and min_le_max: "min_candidates \<le> max_candidates"
begin

sublocale initial_basis_selector where capacity_list = capacity_list and h = "of_int :: int \<Rightarrow> real"
  by (intro initial_basis_selector.intro initial_basis_correct.intro initial_basis_lists.intro
        int_embedding.real_embedding_axioms initial_basis_lists_axioms.intro initial_basis_correct_axioms.intro
        initial_basis_selector_axioms.intro length_edges length_cost length_fst length_snd length_flow length_b
        cap_neg edges_in_range num_edges_gtr_0 isolated_zero flow_nonneg flow_le_cap balance_sum_zero
        block_size_pos min_candidates_pos min_le_max)

text \<open>The three verdicts for the integer program. The returned flow @{term fs} is an @{typ "int list"}, read
      as the real-valued flow @{term \<open>of_int \<circ> nth fs\<close>} to meet the library's specification.\<close>

theorem int_solve_correct:
  "solve = Optimum fs \<Longrightarrow>
     length fs = m \<and> original_network.is_Opt (\<lambda>v. of_int (b_lookup v)) (of_int \<circ> nth fs)"
  "solve = Infeasible \<Longrightarrow> \<nexists> f. original_network.isbflow f (\<lambda>v. of_int (b_lookup v))"
  "solve = Neg_inf_cycle \<Longrightarrow> neg_infty_cycle"
  by (rule solve_correct; assumption)+

end

end
