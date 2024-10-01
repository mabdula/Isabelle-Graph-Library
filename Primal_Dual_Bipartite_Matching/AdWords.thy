theory AdWords
  imports 
    Bipartite_Matching_LP
    More_Lattices_Big
    "HOL-Combinatorics.Multiset_Permutations"
begin

sledgehammer_params [provers = cvc4 vampire verit e spass z3 zipperposition]

lemma finite_image_set2':
  assumes "finite {(x,y). P x y}"
  shows "finite {f x y| x y. P x y}"
proof -
  have "{f x y| x y. P x y} = (\<lambda>(x,y). f x y) ` {(x,y). P x y}"
    by auto

  also from assms have "finite \<dots>"
    by blast

  finally show "finite {f x y| x y. P x y}" .
qed

lemma (in linordered_nonzero_semiring) mult_right_le: "c \<le> 1 \<Longrightarrow> 0 \<le> a \<Longrightarrow> c * a \<le> a"
  using mult_right_mono[of c 1 a] by simp

lemma ln_one_plus_x_over_x_deriv':
  assumes "0 < x"
  shows "((\<lambda>x. ln (1 + x) / x) has_real_derivative (((1/(1+x) * (0 + 1)) * x - ln (1+x) * 1) / (x * x))) (at x)"
  using assms
  by (intro derivative_intros)
     auto
  
lemmas ln_one_plus_x_over_x_deriv = ln_one_plus_x_over_x_deriv'[simplified]

lemma ln_1_plus_x_ge:
  fixes x :: real
  assumes "0 < x"
  shows "x / (1 + x) \<le> ln (1 + x)"
  using assms
  by (smt (verit) divide_minus_left ln_diff_le ln_one)

lemma ln_1_plus_x_over_x_mono:
  fixes x y :: real
  assumes "0 < x" "x \<le> y"
  shows "ln (1 + y) / y \<le> ln (1 + x) / x"
proof (intro DERIV_nonpos_imp_nonincreasing[OF \<open>x \<le> y\<close>])
  fix z assume "x \<le> z"

  with \<open>0 < x\<close> have 
    deriv: "((\<lambda>x. ln (1 + x) / x) has_real_derivative (z / (1 + z) - ln (1 + z)) / (z * z)) (at z)"
    by (auto intro: ln_one_plus_x_over_x_deriv)

  from \<open>0 < x\<close> \<open>x \<le> z\<close> have "z / (1 + z) - ln (1 + z) \<le> 0"
    by (auto intro: ln_1_plus_x_ge)

  then have "(z / (1 + z) - ln (1 + z)) / (z * z) \<le> 0"
    by (auto intro: divide_nonpos_nonneg)

  with deriv show "\<exists>y. ((\<lambda>a. ln (1 + a) / a) has_real_derivative y) (at z) \<and> y \<le> 0"
    by blast
qed

record 'a adwords_state =
  allocation :: "'a graph"
  x :: "'a \<Rightarrow> real"      \<comment> \<open>dual solution for offline vertices\<close>
  z :: "'a \<Rightarrow> real"      \<comment> \<open>dual solution for online vertices\<close>

locale adwords_lp = bipartite_matching_lp +
  fixes B :: "'a \<Rightarrow> real"       \<comment> \<open>budgets\<close>
  fixes b :: "'a set \<Rightarrow> real"   \<comment> \<open>bids\<close>
  fixes \<pi> :: "'a list"          \<comment> \<open>arrival order of online vertices\<close>

  assumes perm: "\<pi> \<in> permutations_of_set R"

  assumes budgets_pos: "\<And>i. i \<in> L \<Longrightarrow> B i > 0"
  assumes bids_pos: "\<And>e. e \<in> G \<Longrightarrow> b e > 0"
  assumes bids_le_budgets: "\<And>i j. {i,j} \<in> G \<Longrightarrow> i \<in> L \<Longrightarrow> b {i,j} \<le> B i"

  assumes graph_non_empty[intro]: "G \<noteq> {}"
begin

lemma 
  shows L_non_empty[intro,simp]: "L \<noteq> {}"
    and R_non_empty[intro,simp]: "R \<noteq> {}"
  using bipartite_edgeE bipartite_graph graph_non_empty by blast+

text \<open>
  We cannot charge a buyer more than their budget. In the analysis we establish a connection
  between how much we actually charge any buyer and the sum of the bids of the products we
  assign to them.
\<close>
abbreviation "total_bid_of M i \<equiv> \<Sum>e\<in>{e \<in> M. i \<in> e}. b e"
abbreviation "charge_of M i \<equiv> min (B i) (total_bid_of M i)"
definition "allocation_value M \<equiv> \<Sum>i\<in>L. charge_of M i"

definition "max_value_allocation M \<longleftrightarrow> one_sided_matching G M R \<and>
  (\<forall>M'. one_sided_matching G M' R \<longrightarrow> allocation_value M' \<le> allocation_value M)"

abbreviation bids_vec :: "real vec" where
  "bids_vec \<equiv> vec m (\<lambda>i. b (from_nat_into G i))"

definition budget_constraint_mat :: "real mat" where
  "budget_constraint_mat \<equiv> mat (card L) m (\<lambda>(i,j). b (from_nat_into G j) * of_bool (from_nat_into L i \<in> from_nat_into G j))"

definition budget_constraint_vec :: "real vec" where
  "budget_constraint_vec \<equiv> vec (card L) (\<lambda>i. B (from_nat_into L i))"

definition allocation_constraint_mat :: "real mat" where
  "allocation_constraint_mat \<equiv> mat (card R) m (\<lambda>(i,j). of_bool (from_nat_into R i \<in> from_nat_into G j))"

definition constraint_matrix :: "real mat" where
  "constraint_matrix \<equiv> budget_constraint_mat @\<^sub>r allocation_constraint_mat"

definition constraint_vec :: "real vec" where
  "constraint_vec \<equiv> budget_constraint_vec @\<^sub>v 1\<^sub>v (card R)"

text \<open>
  Just taking \<^term>\<open>primal_sol\<close> of some produced allocation is not necessarily a feasible solution,
  since it may ignore the budget constraint. The analysis constructs a feasible dual solution for
  the fractional assignment LP. Hence, by weak LP duality we get an upper bound for the optimum
  of the fractional assignment problem. In order to also bound the optimum of the integral
  assignment problem we construct for each feasible solution of the integral assignment problem
  a feasible solution for the fractional assignment problem of the same value. Note that this is
  necessary, since the fractional assignment problem is not just a straightforward LP relaxation
  of the integral assignment problem (in fact, the integral assignment problem is not an LP at at
  all, since we use \<^term>\<open>min\<close> in the objective function).
\<close>
definition adwords_primal_sol :: "'a graph \<Rightarrow> real vec" where
  "adwords_primal_sol M \<equiv> vec m 
  (\<lambda>k. of_bool (from_nat_into G k \<in> M) * (let i = (THE i. i \<in> L \<and> i \<in> from_nat_into G k) in
    if total_bid_of M i \<le> B i
    \<comment> \<open>if budget is not used up, use assignment as is\<close>
    then 1
    \<comment> \<open>otherwise split up overspend over all edges\<close>
    else B i / total_bid_of M i))"

definition offline_dual :: "'a adwords_state \<Rightarrow> real vec" where
  "offline_dual s \<equiv> vec (card L) (\<lambda>i. x s (from_nat_into L i))"

definition online_dual :: "'a adwords_state \<Rightarrow> real vec" where
  "online_dual s \<equiv> vec (card R) (\<lambda>i. z s (from_nat_into R i))"

definition dual_sol :: "'a adwords_state \<Rightarrow> real vec" where
  "dual_sol s \<equiv> offline_dual s @\<^sub>v online_dual s"

lemma total_bid_of_nonneg[intro]:
  assumes "M \<subseteq> G"
  shows "total_bid_of M i \<ge> 0"
  using assms
  by (auto intro!: sum_nonneg dest!: bids_pos subsetD)

lemma total_bid_of_insert:
  assumes "{i,j} \<notin> M" "finite M"
  shows "total_bid_of (insert {i,j} M) i = b {i,j} + total_bid_of M i"
proof -
  have *: "{e \<in> insert {i,j} M. i \<in> e} = insert {i,j} {e \<in> M. i \<in> e}"
    by auto

  from assms show ?thesis
    by (subst *) simp
qed

lemma total_bid_of_insert':
  assumes "i \<in> L" "i' \<in> L" "i \<noteq> i'" "{i,j} \<in> G"
  shows "total_bid_of (insert {i,j} M) i' = total_bid_of M i'"
proof -
  from assms bipartite_graph have *: "{e \<in> insert {i,j} M. i' \<in> e} = {e \<in> M. i' \<in> e}"
    by (auto dest: bipartite_edgeD)

  from assms show ?thesis
    by (subst *) simp
qed

lemma max_value_allocationD: "max_value_allocation M \<Longrightarrow> one_sided_matching G M R"
  unfolding max_value_allocation_def by blast

lemma allocation_value_empty[simp]: "allocation_value {} = 0"
  unfolding allocation_value_def
  by (auto intro!: sum.neutral intro: min_absorb2 dest: budgets_pos)

lemma allocation_value_nonneg: "M \<subseteq> G \<Longrightarrow> allocation_value M \<ge> 0"
  unfolding allocation_value_def
  by (force intro!: sum_nonneg dest!: budgets_pos bids_pos)

lemma allocation_value_gt_0: "M \<subseteq> G \<Longrightarrow> M \<noteq> {} \<Longrightarrow> allocation_value M > 0"
proof -
  assume "M \<subseteq> G" "M \<noteq> {}"
  then obtain e where e: "e \<in> M" "e \<in> G" by blast

  with bipartite_graph obtain i j where ij: "e = {i,j}" "i \<in> L" "j \<in> R"
    by (auto elim: bipartite_edgeE)

  from \<open>M \<subseteq> G\<close> have "finite M"
    by (auto intro: finite_subset)

  show "allocation_value M > 0"
    unfolding allocation_value_def
    by (rule sum_pos2[where i = i])
       (use e ij \<open>M \<subseteq> G\<close> \<open>finite M\<close> in \<open>auto dest!: bids_pos budgets_pos intro!: sum_pos2[where i = e]\<close>)
qed

lemma allocation_value_zero_iff: "M \<subseteq> G \<Longrightarrow> allocation_value M = 0 \<longleftrightarrow> M = {}"
  by (auto dest: allocation_value_gt_0)

lemma max_value_allocation_non_empty: "max_value_allocation {} \<Longrightarrow> False"
proof -
  assume "max_value_allocation {}"
  from graph_non_empty obtain e where "e \<in> G"
    by blast

  with bipartite_graph obtain i j where ij: "e = {i,j}" "i \<in> L" "j \<in> R"
    by (auto elim: bipartite_edgeE)

  then have "j' \<in> R \<Longrightarrow> {e. e = {i, j} \<and> j' \<in> e} = (if j' = j then {{i,j}} else {})" for j'
    by auto

  with \<open>e \<in> G\<close> have "one_sided_matching G {e} R"
    by (intro one_sided_matchingI)
       (simp_all add: ij)

  from \<open>j \<in> R\<close> have *: "i' \<in> L \<Longrightarrow> {e. e = {i, j} \<and> i' \<in> e} = (if i' = i then {{i,j}} else {})" for i'
    by auto

  have "allocation_value {e} > 0"
    unfolding allocation_value_def
    by (rule sum_pos2[where i = i])
       (use ij \<open>e \<in> G\<close> in \<open>auto dest: budgets_pos bids_pos simp: *\<close>)

  with \<open>max_value_allocation {}\<close> \<open>one_sided_matching G {e} R\<close> show False
    unfolding max_value_allocation_def
    by auto
qed

lemma max_value_allocation_pos_value: "max_value_allocation M \<Longrightarrow> allocation_value M > 0"
  by (metis allocation_value_gt_0 max_value_allocation_def max_value_allocation_non_empty one_sided_matching_subgraphD)

lemma 
  shows dim_row_budget_constraint_mat[simp]: "dim_row budget_constraint_mat = card L"
    and  budget_constraint_carrier_mat[intro]: "budget_constraint_mat \<in> carrier_mat (card L) m"
  unfolding budget_constraint_mat_def
  by simp_all

lemma 
  shows dim_budget_constraint_vec[simp]: "dim_vec budget_constraint_vec = card L"
    and budget_constraint_vec_carrier_vec[intro]: "budget_constraint_vec \<in> carrier_vec (card L)"
  unfolding budget_constraint_vec_def by simp_all

lemma 
  shows dim_row_allocation_constraint_mat[simp]: "dim_row allocation_constraint_mat = card R"
    and allocation_constraint_carrier_mat[intro]: "allocation_constraint_mat \<in> carrier_mat (card R) m"
  unfolding allocation_constraint_mat_def by simp_all

lemma 
  shows constraint_matrix_carrier_mat[intro]: "constraint_matrix \<in> carrier_mat n m"
    and dim_row_constraint_matrix[simp]: "dim_row constraint_matrix = n"
    and dim_col_constraint_matrix[simp]: "dim_col constraint_matrix = m"
  unfolding constraint_matrix_def
  by (auto intro: carrier_matD simp: n_sum)

lemma 
  shows dim_constraint_vec[simp]: "dim_vec constraint_vec = n"
    and constraint_vec_carrier_vec[intro]: "constraint_vec \<in> carrier_vec n"
  unfolding constraint_vec_def
  by (auto simp: n_sum)

lemma 
  shows dim_adwords_primal[simp]: "dim_vec (adwords_primal_sol M) = m"
    and adwords_primal_carrier_vec[intro]: "adwords_primal_sol M \<in> carrier_vec m"
  unfolding adwords_primal_sol_def by simp_all

lemma 
  shows dim_offline_dual[simp]: "dim_vec (offline_dual s) = card L"
    and offline_dual_carrier_vec[intro]: "offline_dual s \<in> carrier_vec (card L)"
  unfolding offline_dual_def by simp_all

lemma 
  shows dim_online_dual[simp]: "dim_vec (online_dual s) = card R"
    and online_dual_carrier_vec[intro]: "online_dual s \<in> carrier_vec (card R)"
  unfolding online_dual_def by simp_all

lemma
  shows dim_dual_sol[simp]: "dim_vec (dual_sol s) = n"
    and dual_sol_carrier_vec[intro]: "dual_sol s \<in> carrier_vec n"
  unfolding dual_sol_def
  by (auto simp: n_sum)

lemma dual_sol_init[simp]:
  "dual_sol \<lparr> allocation = M, x = \<lambda>_. 0, z = \<lambda>_. 0 \<rparr> = 0\<^sub>v n"
  unfolding dual_sol_def offline_dual_def online_dual_def append_vec_def
  by (auto simp: Let_def n_sum)

lemma subgraph_UNION_decomp:
  assumes "M \<subseteq> G"
  shows "M = (\<Union>i\<in>L. {e \<in> M. i \<in> e})"
  using assms bipartite_subgraph[OF bipartite_graph assms]
  by (force elim: bipartite_edgeE)

lemma subgraph_decomp_disjoint:
  assumes "M \<subseteq> G"
  assumes "i \<in> L" "i' \<in> L" "i \<noteq> i'"
  shows "{e \<in> M. i \<in> e} \<inter> {e \<in> M. i' \<in> e} = {}"
  using assms bipartite_subgraph[OF bipartite_graph \<open>M \<subseteq> G\<close>]
  by (auto elim: bipartite_edgeE)

lemma sum_edges_eq_sum_vs:
  assumes "M \<subseteq> G"
  shows "(\<Sum>e\<in>M. f e) = (\<Sum>i\<in>L. sum f {e\<in>M. i \<in> e})"
  using assms
  by (subst subgraph_UNION_decomp[OF \<open>M \<subseteq> G\<close>], subst sum.UNION_disjoint)
     (auto intro: finite_subset[where B = G] dest: subgraph_decomp_disjoint)

lemma adwords_primal_sol_nonneg[intro]:
  assumes "M \<subseteq> G"
  shows "adwords_primal_sol M \<ge> 0\<^sub>v m"
  unfolding adwords_primal_sol_def less_eq_vec_def
  using total_bid_of_nonneg[OF assms] assms
  by (auto simp: Let_def intro!: divide_nonneg_nonneg[OF order_less_imp_le] dest: budgets_pos the_l_subset_in_LI)

lemma adwords_primal_dot_bids_eq_value:
  assumes "M \<subseteq> G"
  shows "bids_vec \<bullet> adwords_primal_sol M = allocation_value M"
proof -
  have "bids_vec \<bullet> adwords_primal_sol M = 
    (\<Sum>k \<in> {0..<m} \<inter> {k. from_nat_into G k \<in> M}. b (from_nat_into G k) *
      (let i = (THE i. i \<in> L \<and> i \<in> from_nat_into G k) in if total_bid_of M i \<le> B i then 1 else B i / total_bid_of M i))"
    unfolding scalar_prod_def adwords_primal_sol_def
    by (auto simp flip: sum_of_bool_mult_eq simp: algebra_simps)

  also from \<open>M \<subseteq> G\<close> have "\<dots> = (\<Sum>e\<in>M. b e *
    (let i = (THE i. i \<in> L \<and> i \<in> e) in if total_bid_of M i \<le> B i then 1 else B i / total_bid_of M i))"
    by (auto intro!: sum.reindex_bij_witness[where j = "from_nat_into G" and i = G_enum]
             intro: to_nat_on_from_nat_into_less simp: countable_finite to_nat_on_less_card)

  also from bipartite_graph \<open>M \<subseteq> G\<close> have "\<dots> = (\<Sum>i\<in>L. (\<Sum>e\<in>{e\<in>M. i \<in> e}. b e * (if total_bid_of M i \<le> B i then 1 else B i / total_bid_of M i)))"
    apply (auto simp: sum_edges_eq_sum_vs Let_def intro!: sum.cong)
     apply (smt (verit, ccfv_threshold) Collect_cong bipartite_commute bipartite_eqI in_mono the_equality)+
    done

  also have "\<dots> = allocation_value M"
    unfolding allocation_value_def
    by (auto intro!: sum.cong simp flip: sum_distrib_right sum_divide_distrib dest: budgets_pos)

  finally show ?thesis .
qed

lemma primal_dot_bids_eq_sum_edges:
  assumes "M \<subseteq> G"
  shows "bids_vec \<bullet> primal_sol M = (\<Sum>e\<in>M. b e)"
  unfolding scalar_prod_def primal_sol_def
  using assms
  by (auto intro!: sum.reindex_bij_witness[where j = "from_nat_into G" and i = G_enum]
           intro: to_nat_on_from_nat_into_less simp: to_nat_on_less_card countable_finite)

lemma subgraph_budget_constraint:
  assumes "M \<subseteq> G"
  shows "budget_constraint_mat *\<^sub>v adwords_primal_sol M \<le> budget_constraint_vec"
  unfolding less_eq_vec_def
proof (intro conjI allI impI, simp_all)
  fix k assume [intro,simp]: "k < card L"
  let ?i = "from_nat_into L k"

  have "?i \<in> L"
    by (simp add: from_nat_into)

  with bipartite_subgraph[OF bipartite_graph \<open>M \<subseteq> G\<close>] have the_i: "e \<in> M \<Longrightarrow> ?i \<in> e \<Longrightarrow> (THE i. i \<in> L \<and> i \<in> e) = ?i" for e
    by (auto elim: bipartite_edgeE)

  from assms have "row budget_constraint_mat k \<bullet> adwords_primal_sol M = 
    (\<Sum>k \<in> {0..<m} \<inter> {k. ?i \<in> from_nat_into G k} \<inter> {k. from_nat_into G k \<in> M}. b (from_nat_into G k) *
      (let i' = (THE i'. i' \<in> L \<and> i' \<in> from_nat_into G k) in if total_bid_of M i' \<le> B i' then 1 else B i' / total_bid_of M i'))"
    unfolding scalar_prod_def budget_constraint_mat_def adwords_primal_sol_def
    by (auto simp flip: sum_of_bool_mult_eq simp: algebra_simps)

  also from \<open>M \<subseteq> G\<close> \<open>?i \<in> L\<close> have "\<dots> = (\<Sum>e\<in>{e\<in>M. ?i \<in> e}. b e * (if total_bid_of M ?i \<le> B ?i then 1 else B ?i / total_bid_of M ?i))"
    by (auto intro!: sum.reindex_bij_witness[where j = "from_nat_into G" and i = G_enum]
             intro: to_nat_on_from_nat_into_less
             simp: countable_finite to_nat_on_less_card Let_def dest: the_i)

  also from \<open>?i \<in> L\<close> have "\<dots> \<le> B ?i"
    by (auto simp flip: sum_distrib_right dest: budgets_pos)

  also have "\<dots> = budget_constraint_vec $ k"
    unfolding budget_constraint_vec_def by simp

  finally show "row budget_constraint_mat k \<bullet> adwords_primal_sol M \<le> budget_constraint_vec $ k" .
qed

lemma one_sided_matching_allocation_constraint:
  assumes "one_sided_matching G M R"
  shows "allocation_constraint_mat *\<^sub>v adwords_primal_sol M \<le> 1\<^sub>v (card R)"
  unfolding less_eq_vec_def
proof (intro conjI allI impI, simp_all)
  fix k assume [intro,simp]: "k < card R"
  let ?j = "from_nat_into R k"

  from assms have "M \<subseteq> G" by (auto dest: one_sided_matching_subgraphD)

  have online: "?j \<in> R"
    by (metis \<open>k < card R\<close> bot_nat_0.extremum_strict card.empty from_nat_into)

  from online \<open>M \<subseteq> G\<close> have "row allocation_constraint_mat k \<bullet> adwords_primal_sol M = 
    (\<Sum>e\<in>{e\<in>M. ?j \<in> e}. let i = THE i. i \<in> L \<and> i \<in> e in if total_bid_of M i \<le> B i then 1 else B i / total_bid_of M i)"
    unfolding scalar_prod_def allocation_constraint_mat_def adwords_primal_sol_def
    by (auto intro!: sum.reindex_bij_witness[where j = "from_nat_into G" and i = G_enum]
             intro: to_nat_on_from_nat_into_less simp: countable_finite to_nat_on_less_card)

  also from \<open>M \<subseteq> G\<close> have "\<dots> \<le> (\<Sum>e\<in>{e\<in>M. ?j \<in> e}. 1)"
    by (intro sum_mono)
       (auto simp: Let_def dest: the_l_subset_in_LI dest!: budgets_pos bids_pos)

  also from assms online have "\<dots> \<le> 1"
    unfolding one_sided_matching_def
    by auto

  finally show "row allocation_constraint_mat k \<bullet> adwords_primal_sol M \<le> 1" .
qed

lemma one_sided_matching_feasible:
  assumes "one_sided_matching G M R"
  shows "constraint_matrix *\<^sub>v adwords_primal_sol M \<le> constraint_vec"
  unfolding constraint_matrix_def constraint_vec_def
  by (subst append_rows_le)
     (use assms in \<open>auto intro: subgraph_budget_constraint one_sided_matching_allocation_constraint
                         dest: one_sided_matching_subgraphD\<close>)

lemma allocation_value_bound_by_feasible_dual:
  fixes y :: "real vec"
  assumes "one_sided_matching G M R"

  assumes "constraint_matrix\<^sup>T *\<^sub>v y \<ge> bids_vec"
  assumes "y \<ge> 0\<^sub>v n"

  shows "allocation_value M \<le> constraint_vec \<bullet> y"
proof -
  from assms have "allocation_value M = bids_vec \<bullet> adwords_primal_sol M"
    by (auto simp: adwords_primal_dot_bids_eq_value dest: one_sided_matching_subgraphD)

  also from assms have "\<dots> \<le> constraint_vec \<bullet> y"
    by (auto intro!: weak_duality_theorem_nonneg_primal[where A = constraint_matrix] one_sided_matching_feasible 
             dest: one_sided_matching_subgraphD)

  finally show ?thesis .
qed

lemma max_value_allocation_bound_by_feasible_dual:
  fixes y :: "real vec"
  assumes "max_value_allocation M"

  assumes "constraint_matrix\<^sup>T *\<^sub>v y \<ge> bids_vec"
  assumes "y \<ge> 0\<^sub>v n"

  shows "allocation_value M \<le> constraint_vec \<bullet> y"
  using assms
  by (auto intro: allocation_value_bound_by_feasible_dual dest: max_value_allocationD)

definition "R_max \<equiv> Max {b {i, j} / B i | i j. {i,j} \<in> G \<and> i \<in> L \<and> j \<in> R}"
definition "c \<equiv> (1 + R_max) powr (1 / R_max)"

definition adwords_step :: "'a adwords_state \<Rightarrow> 'a \<Rightarrow> 'a adwords_state" where
  "adwords_step s j \<equiv> 
    let ns = {i. {i, j} \<in> G} in
    if ns \<noteq> {} \<and> j \<notin> Vs (allocation s)
    then
      let i = arg_max_on (\<lambda>i. b {i, j} * (1 - (x s) i)) ns in
        if (x s) i \<ge> 1 
        then s
        else \<lparr> 
          allocation = insert {i, j} (allocation s),
          x = (x s)(i := (x s) i * (1 + b {i, j} / B i) + b {i, j} / ((c-1) * B i)),
          z = (z s)(j := b {i, j} * (1 - (x s) i))
        \<rparr>
    else s"

definition "adwords' s \<equiv> foldl adwords_step s"
abbreviation "adwords \<equiv> adwords' \<lparr> allocation = {}, x = \<lambda>_. 0, z = \<lambda>_. 0 \<rparr>"

lemma adwords_Nil[simp]: "adwords' s [] = s"
  unfolding adwords'_def by simp

lemma adwords_Cons: "adwords' s (j#js) = adwords' (adwords_step s j) js"
  unfolding adwords'_def by simp

lemma adwords_append: "adwords' s (js@js') = adwords' (adwords' s js) js'"
  unfolding adwords'_def by simp

lemma adwords_step_cases[case_names no_neighbor j_matched no_budget new_match]:
  fixes j s
  defines "i \<equiv> arg_max_on (\<lambda>i. b {i,j} * (1 - x s i)) {i. {i,j} \<in> G}"

  assumes "{i. {i, j} \<in> G} = {} \<Longrightarrow> P"
  assumes "j \<in> Vs (allocation s) \<Longrightarrow> P"
  assumes "x s i \<ge> 1 \<Longrightarrow> P"
  assumes "\<lbrakk> j \<notin> Vs (allocation s); {i, j} \<in> G; x s i < 1; {i. {i, j} \<in> G} \<noteq> {}; \<comment> \<open>keep this redundant assumption for simplification\<close>
    \<not>(\<exists>i' \<in> {i. {i, j} \<in> G}. b {i',j} * (1 - x s i') > b {i, j} * (1 - x s i)) \<rbrakk> \<Longrightarrow> P"
  shows P
proof -
  consider "{i. {i,j} \<in> G} = {}" | "j \<in> Vs (allocation s)" | "x s i \<ge> 1" | "{i. {i,j} \<in> G} \<noteq> {} \<and> j \<notin> Vs (allocation s) \<and> x s i < 1"
    by fastforce

  then show P
  proof cases
    case 4
    then have "i \<in> {i. {i,j} \<in> G} \<and> \<not>(\<exists>i'\<in>{i. {i,j} \<in> G}. b {i',j} * (1 - x s i') > b {i,j} * (1 - x s i))"
      unfolding i_def
      by (intro conjI arg_max_if_finite)
         (auto intro: finite_subset[where B = "Vs G"] dest: edges_are_Vs)

    with 4 assms show P
      by blast
  qed (use assms in auto)
qed

lemma adwords_step_casesR[consumes 1, case_names no_neighbor j_matched no_budget new_match]:
  fixes j s
  defines "i \<equiv> arg_max_on (\<lambda>i. b {i,j} * (1 - x s i)) {i. {i,j} \<in> G}"
  assumes "j \<in> R"
  assumes "{i. {i,j} \<in> G} = {} \<Longrightarrow> P"
  assumes "j \<in> Vs (allocation s) \<Longrightarrow> P"
  assumes "x s i \<ge> 1 \<Longrightarrow> P"
  assumes "\<lbrakk> j \<notin> Vs (allocation s); {i,j} \<in> G; x s i < 1; {i. {i,j} \<in> G} \<noteq> {}; \<comment> \<open>keep this redundant assumption for simplification\<close>
    i \<in> L;
    \<not>(\<exists>i'\<in>{i. {i,j} \<in> G}. b {i',j} * (1 - x s i') > b {i,j} * (1 - x s i)) \<rbrakk> \<Longrightarrow> P"
  shows P
proof (cases j rule: adwords_step_cases[where s = s])
  case new_match
  with bipartite_graph \<open>j \<in> R\<close> have "i \<in> L"
    unfolding i_def
    by (auto dest: bipartite_edgeD)

  with new_match assms show ?thesis
    by blast
qed (use assms in auto)

lemma finite_bid_ratios:
  "finite {b {i, j} / B i |i j. {i, j} \<in> G \<and> i \<in> L \<and> j \<in> R}"
  apply(rule finite_image_set2')
  apply(rule finite_subset[where B = "Vs G \<times> Vs G"] )
  by auto

lemma finite_bids: "finite {b {i,j} |j. {i,j} \<in> G}"
  by (auto intro!: finite_image_set intro: finite_subset dest: edges_are_Vs_2)

lemma max_bid_pos: "i \<in> L \<Longrightarrow> Max {b {i, j} |j. {i, j} \<in> G} > 0"
  by (subst Max_gr_iff)
     (force intro: finite_bids elim: left_neighborE dest: bids_pos)+

lemma bid_ratios_non_empty: "{b {i, j} / B i |i j. {i, j} \<in> G \<and> i \<in> L \<and> j \<in> R} \<noteq> {}"
  using graph_non_empty bipartite_graph
  by auto (metis bipartite_edgeE)

lemma bid_ratio_pos: "i \<in> L \<Longrightarrow> {i,j} \<in> G \<Longrightarrow> b {i,j} / B i > 0"
  by (auto intro: divide_pos_pos budgets_pos bids_pos)

lemma R_max_pos: "0 < R_max"
  unfolding R_max_def
  using bid_ratios_non_empty
  by (subst Max_gr_iff)
     (auto intro: finite_bid_ratios divide_pos_pos dest: bids_pos budgets_pos)

lemma R_max_ge:
  assumes "i \<in> L"
  assumes "{i,j} \<in> G"
  shows "b {i,j} / B i \<le> R_max"
  unfolding R_max_def
  using assms bipartite_graph
  by (auto intro: Max_ge finite_bid_ratios dest: bipartite_edgeD)

lemma R_max_le_1:
  shows "R_max \<le> 1"
  unfolding R_max_def
  by (auto intro!: Max.boundedI finite_bid_ratios bid_ratios_non_empty mult_imp_div_pos_le budgets_pos bids_le_budgets)

lemma c_gt_1: "1 < c"
  unfolding c_def
  using R_max_pos
  by auto

lemma c_powr_bid_ratio_le:
  assumes "i \<in> L"
  assumes "{i,j} \<in> G"
  shows "c powr (b {i, j} / B i) \<le> 1 + b {i, j} / B i"
proof -
  from c_gt_1 have *: "0 < y \<Longrightarrow> c powr y \<le> 1 + y \<longleftrightarrow> ln c \<le> ln (1 + y) / y" for y
    by (subst powr_le_iff) (auto simp: log_def field_simps)

  from assms have ratio_pos: "0 < b {i,j} / B i"
    by (auto dest!: budgets_pos bids_pos simp: field_simps)

  from R_max_pos have "ln c = ln (1 + R_max) / R_max"
    unfolding c_def
    by (auto simp: ln_powr)

  also from assms have "\<dots> \<le> ln (1 + b {i,j} / B i) / (b {i,j} / B i)"
    by (intro ln_1_plus_x_over_x_mono)
       (auto intro: ratio_pos R_max_ge)

  finally show ?thesis
    using ratio_pos
    by (simp add: *)
qed

lemma budget_over_budget_plus_bid_ge:
  assumes "{i,j} \<in> G" "i \<in> L" "j \<in> R"
  shows "B i / (B i + b {i,j}) \<ge> 1 - R_max"
proof (intro mult_imp_le_div_pos add_pos_pos)
  from assms have "R_max * B i \<ge> b {i,j}"
    by (subst pos_divide_le_eq[symmetric])
       (auto intro: R_max_ge budgets_pos)

  with assms R_max_pos show "B i \<ge> (1 - R_max) * (B i + b {i,j})"
    using linordered_semiring_strict_class.mult_pos_pos
    by (fastforce simp: distrib_left left_diff_distrib dest!: bids_pos)
qed (use assms in \<open>auto intro: budgets_pos bids_pos\<close>)

lemma adwords_step_subgraph:
  assumes "allocation s \<subseteq> G"
  shows "allocation (adwords_step s j) \<subseteq> G"
  using assms
  by (cases j rule: adwords_step_cases[where s = s])
     (auto simp: adwords_step_def Let_def)

lemma adwords_subgraph:
  assumes "allocation s \<subseteq> G"
  shows "allocation (adwords' s js) \<subseteq> G"
  using assms
  by (induction js arbitrary: s)
     (auto simp: adwords_Cons dest: adwords_step_subgraph)

lemma one_sided_matching_adwords_step:
  assumes "j \<in> R"
  assumes "one_sided_matching G (allocation s) R"
  shows "one_sided_matching G (allocation (adwords_step s j)) R"
  using assms
  by (cases j rule: adwords_step_casesR[where s = s])
     (auto simp: adwords_step_def Let_def intro: one_sided_matching_insertI)

lemma one_sided_matching_adwords:
  assumes "set js \<subseteq> R"
  assumes "one_sided_matching G (allocation s) R"
  shows "one_sided_matching G (allocation (adwords' s js)) R"
  using assms
  by (induction js arbitrary: s)
     (auto simp: adwords_Cons dest: one_sided_matching_adwords_step)

lemma finite_adwords_step:
  assumes "finite (allocation s)"
  shows "finite (allocation (adwords_step s j))"
  using assms
  by (cases j rule: adwords_step_cases[where s = s])
     (auto simp: adwords_step_def Let_def)

lemma adwords_step_x_mono:
  assumes "0 \<le> x s i"
  assumes "j \<in> R"
  shows "x s i \<le> x (adwords_step s j) i"
  using \<open>j \<in> R\<close>
proof (cases j rule: adwords_step_casesR[where s = s])
  case new_match
  let ?i' = "arg_max_on (\<lambda>i. b {i,j} * (1 - x s i)) {i. {i,j} \<in> G}"

  show ?thesis
  proof (cases "?i' = i")
    case True

    with new_match \<open>0 \<le> x s i\<close> have "x s i \<le> x s i * (1 + b {i, j} / B i)"
      by (auto simp: mult_le_cancel_left1 True dest!: budgets_pos bids_pos)

    also from new_match c_gt_1 \<open>?i' \<in> L\<close> have "\<dots> \<le> x s i * (1 + b {i,j} / B i) + b {i,j} / ((c-1) * B i)"
      by (auto simp: True dest!: budgets_pos bids_pos)

    finally show ?thesis
      by (auto simp: True adwords_step_def)
  next
    case False
    with new_match show ?thesis
      by (auto simp: adwords_step_def Let_def)
  qed
qed (simp_all add: adwords_step_def)

lemma adwords_x_mono:
  assumes "0 \<le> x s i"
  assumes "set js \<subseteq> R"
  shows "x s i \<le> x (adwords' s js) i"
  using assms
proof (induction js arbitrary: s)
  case (Cons j js)
  then have "x s i \<le> x (adwords_step s j) i"
    by (auto intro: adwords_step_x_mono)

  also with Cons.prems have "\<dots> \<le> x (adwords' (adwords_step s j) js) i"
    by (auto intro: Cons.IH)

  finally show ?case
    by (simp add: adwords_Cons)    
qed simp

lemma adwords_x_nonneg: "set js \<subseteq> R \<Longrightarrow> 0 \<le> x s i \<Longrightarrow> 0 \<le> x (adwords' s js) i"
  using adwords_x_mono by fastforce

lemma adwords_step_z_nonneg:
  assumes "0 \<le> z s i"
  shows "z (adwords_step s j) i \<ge> 0"
proof (cases j rule: adwords_step_cases[where s = s])
  case new_match
  with assms show ?thesis
    by (auto simp: adwords_step_def Let_def intro: mult_nonneg_nonneg dest: bids_pos)
qed (use assms in \<open>simp_all add: adwords_step_def\<close>)

lemma adwords_z_nonneg: "0 \<le> z s i \<Longrightarrow> z (adwords' s js) i \<ge> 0"
  by (induction js arbitrary: s)
     (auto simp: adwords_Cons dest: adwords_step_z_nonneg)

lemma adwords_step_z_unchanged:
  assumes "j \<noteq> j'"
  shows "z (adwords_step s j') j = z s j"
  using assms
  by (cases j' rule: adwords_step_cases[where s = s])
     (auto simp: adwords_step_def Let_def)

lemma adwords_z_unchanged:
  assumes "j \<notin> set js"
  shows "z (adwords' s js) j = z s j"
  using assms
  by (induction js arbitrary: s)
     (auto simp: adwords_Cons dest: adwords_step_z_unchanged)

lemma unmatched_R_in_adwords_step_if:
  assumes "j \<in> R" "j' \<in> R"
  assumes "j \<noteq> j'"
  assumes "j \<notin> Vs (allocation s)"
  shows "j \<notin> Vs (allocation (adwords_step s j'))"
  using \<open>j' \<in> R\<close>
  by (cases j' rule: adwords_step_casesR[where s = s])
     (use assms in \<open>auto simp: adwords_step_def Let_def vs_insert\<close>)

lemma unmatched_R_in_adwords_if:
  assumes "j \<notin> set js" "j \<in> R"
  assumes "set js \<subseteq> R"
  assumes "j \<notin> Vs (allocation s)"
  shows "j \<notin> Vs (allocation (adwords' s js))"
  using assms
proof (induction js arbitrary: s)
  case (Cons j' js)

  then have "j \<notin> Vs (allocation (adwords_step s j'))"
    by (intro unmatched_R_in_adwords_step_if) auto

  with Cons show ?case
    by (simp add: adwords_Cons)
qed simp

lemma dual_feasible_edge:
  assumes "i \<in> L"
  assumes "j \<in> R"
  assumes "{i,j} \<in> G"

  shows "b {i,j} * x (adwords \<pi>) i + z (adwords \<pi>) j \<ge> b {i,j}"
proof (cases "x (adwords \<pi>) i \<ge> 1")
  case True
  with \<open>{i,j} \<in> G\<close> have "b {i,j} \<le> b {i,j} * x (adwords \<pi>) i"
    by (auto dest: bids_pos)

  also have "\<dots> \<le> b {i,j} * x (adwords \<pi>) i + z (adwords \<pi>) j"
    by (auto intro: adwords_z_nonneg)

  finally show ?thesis .
next
  case False

  from perm \<open>j \<in> R\<close> obtain pre suff where \<pi>_decomp: "\<pi> = pre @ j # suff"
    by (metis permutations_of_setD(1) split_list)

  with perm have set_pre: "set pre \<subseteq> R" and set_suff: "set suff \<subseteq> R"
    by (auto dest: permutations_of_setD)

  let ?i' = "arg_max_on (\<lambda>i. b {i,j} * (1 - x (adwords pre) i)) {i. {i,j} \<in> G}"

  show ?thesis
  proof (cases j rule: adwords_step_cases[where s = "adwords pre"])
    case no_neighbor
    with \<open>{i,j} \<in> G\<close> show ?thesis by blast
  next
    case j_matched
    from \<pi>_decomp set_pre perm \<open>j \<in> R\<close> have "j \<notin> Vs (allocation (adwords pre))"
      by (intro unmatched_R_in_adwords_if) (auto dest: permutations_of_setD)

    with j_matched show ?thesis by blast
  next
    case no_budget

    from \<open>{i,j} \<in> G\<close> have "?i' \<in> {i. {i,j} \<in> G}"
      by (intro arg_max_if_finite)
         (auto intro: finite_subset[where B = "Vs G"] dest: edges_are_Vs)

    with bipartite_graph \<open>j \<in> R\<close> have "{?i',j} \<in> G"
      by (auto dest: bipartite_edgeD)

    from perm have "x (adwords pre) i \<le> x (adwords \<pi>) i"
      by (auto simp: adwords_append \<pi>_decomp intro!: adwords_x_mono adwords_x_nonneg dest: permutations_of_setD)

    also from False have "\<dots> < 1"
      by simp

    finally have "x (adwords pre) i < 1" .

    with \<open>{i,j} \<in> G\<close> have i_gt_0: "b {i,j} * (1 - x (adwords pre) i) > 0"
      by (auto dest: bids_pos)

    from \<open>{i,j} \<in> G\<close> have i_le_i': "b {i,j} * (1 - x (adwords pre) i) \<le> b {?i',j} * (1 - x (adwords pre) ?i')"
      by (auto intro!: arg_max_greatest intro: finite_subset[where B = "Vs G"] dest: edges_are_Vs)

    have "x (adwords pre) ?i' < 1"
    proof (rule ccontr, simp add: not_less)
      assume "1 \<le> x (adwords pre) ?i'"

      with \<open>{?i',j} \<in> G\<close> have "b {?i',j} * (1 - x (adwords pre) ?i') \<le> 0"
        by (auto dest: bids_pos simp: field_simps)

      with i_gt_0 i_le_i' show False
        by linarith
    qed

    with no_budget show ?thesis by simp
  next
    case new_match
    with \<open>{i,j} \<in> G\<close> have z_step: "z (adwords_step (adwords pre) j) j = b {?i',j} * (1 - x (adwords pre) ?i')"
      by (auto simp: adwords_step_def Let_def)

    from perm \<pi>_decomp have "j \<notin> set suff"
      by (auto dest: permutations_of_setD)

    have "b {i,j} = b {i,j} * x (adwords pre) i + b {i,j} * (1 - x (adwords pre) i)"
      by argo

    also from set_pre set_suff \<open>{i,j} \<in> G\<close> \<open>j \<in> R\<close> have "\<dots> \<le> b {i,j} * x (adwords \<pi>) i + b {i,j} * (1 - x (adwords pre) i)"
      by (force dest: bids_pos simp: \<pi>_decomp adwords_append intro: adwords_x_mono adwords_x_nonneg)

    also from new_match \<open>{i,j} \<in> G\<close>
    have "\<dots> \<le> b {i,j} * x (adwords \<pi>) i + b {?i',j} * (1 - x (adwords pre) ?i')"
      by force

    also from \<open>j \<notin> set suff\<close> have "\<dots> = b {i,j} * x (adwords \<pi>) i + z (adwords \<pi>) j"
      by (auto simp: \<pi>_decomp adwords_append adwords_Cons adwords_z_unchanged z_step)

    finally show ?thesis .
  qed
qed

lemma dual_feasible:
  shows "constraint_matrix\<^sup>T *\<^sub>v dual_sol (adwords \<pi>) \<ge> bids_vec"
  unfolding less_eq_vec_def
proof (intro conjI allI impI, simp_all)
  fix k assume "k < m"

  then have col_k: "col constraint_matrix k = col budget_constraint_mat k @\<^sub>v col allocation_constraint_mat k"
    unfolding constraint_matrix_def append_rows_def
    by (auto intro!: col_four_block_mat)

  from \<open>k < m\<close> have col_carrier_vec[intro]: "col budget_constraint_mat k \<in> carrier_vec (card L)" "col allocation_constraint_mat k \<in> carrier_vec (card R)"
    by (auto intro: col_carrier_vec)
    
  from \<open>k < m\<close> obtain i j where ij: "{i,j} \<in> G" "from_nat_into G k = {i,j}" "i \<in> L" "j \<in> R"
    by (auto elim: from_nat_into_G_E)

  then have [simp]: "from_nat_into L (to_nat_on L i) = i" "from_nat_into R (to_nat_on R j) = j"
    by simp_all

  from \<open>i \<in> L\<close> \<open>j \<in> R\<close> have indicat_online: "{0..<card R} \<inter> {l. from_nat_into R l \<in> from_nat_into G k} = {to_nat_on R j}"
    by (auto simp: \<open>from_nat_into G k = {i,j}\<close> from_nat_into R_enum_less_card)

  from \<open>k < m\<close> have [simp]: "col allocation_constraint_mat k \<bullet> online_dual (adwords \<pi>) = z (adwords \<pi>) j"
    unfolding allocation_constraint_mat_def online_dual_def scalar_prod_def
    by (auto simp: indicat_online)

  from from_nat_into[OF L_non_empty] \<open>i \<in> L\<close> \<open>j \<in> R\<close> have indicat_offline: "{0..<card L} \<inter> {i. from_nat_into L i \<in> from_nat_into G k} = {to_nat_on L i}"
    by (auto simp: \<open>from_nat_into G k = {i,j}\<close> L_enum_less_card)

  from \<open>k <  m\<close> have [simp]: "col budget_constraint_mat k \<bullet> offline_dual (adwords \<pi>) = b {i,j} * x (adwords \<pi>) i"
    unfolding budget_constraint_mat_def offline_dual_def scalar_prod_def
    by (auto simp: ac_simps indicat_offline simp flip: sum_distrib_left intro: arg_cong[OF ij(2)])

  from ij have "b (from_nat_into G k) \<le> b {i,j} * x (adwords \<pi>) i + z (adwords \<pi>) j"
    by (auto intro: dual_feasible_edge)

  also from \<open>k < m\<close> have "\<dots> = col constraint_matrix k \<bullet> dual_sol (adwords \<pi>)"
    unfolding dual_sol_def
    by (subst col_k, subst scalar_prod_append) auto

  finally show "b (from_nat_into G k) \<le> col constraint_matrix k \<bullet> dual_sol (adwords \<pi>)" .
qed

lemma dual_nonneg:
  "dual_sol (adwords \<pi>) \<ge> 0\<^sub>v n"
  unfolding less_eq_vec_def dual_sol_def online_dual_def offline_dual_def
  using perm
  by (auto simp: n_sum intro: adwords_x_nonneg adwords_z_nonneg dest: permutations_of_setD)

lemma dual_primal_times_adwords_step:
  assumes "j \<in> R"
  assumes "z s j = 0"
  assumes "constraint_vec \<bullet> dual_sol s * (1 - 1 / c) = bids_vec \<bullet> primal_sol (allocation s)"
  shows "constraint_vec \<bullet> dual_sol (adwords_step s j) * (1 - 1 / c) = bids_vec \<bullet> primal_sol (allocation (adwords_step s j))"
  using \<open>j \<in> R\<close>
proof (cases j rule: adwords_step_casesR[where s = s])
  case new_match
  let ?i = "arg_max_on (\<lambda>i. b {i, j} * (1 - x s i)) {i. {i, j} \<in> G}"

  from new_match 
  have allocation_insert: "allocation (adwords_step s j) = insert {?i,j} (allocation s)"
    and edge: "{?i,j} \<in> G"
    and x_upd: "x (adwords_step s j) = (x s)(?i := (x s) ?i * (1 + b {?i, j} / B ?i) + b {?i, j} / ((c-1) * B ?i))"
    and z_upd: "z (adwords_step s j) = (z s)(j := b {?i, j} * (1 - (x s) ?i))"
    by (simp_all add: adwords_step_def Let_def)

  from new_match have "{?i,j} \<notin> allocation s"
    by (auto dest: edges_are_Vs)

  with edge have insert_indices: "{0..<m} \<inter> {i. from_nat_into G i \<in> allocation (adwords_step s j)} = 
    insert (G_enum {?i,j}) ({0..<m} \<inter> {i. from_nat_into G i \<in> allocation s})"
    by (auto simp: allocation_insert countable_finite intro: G_enum_less_m dest!: to_nat_on_from_nat_into_less[OF finite_graph])

  from \<open>{?i,j} \<notin> allocation s\<close> have "G_enum {?i,j} \<notin> ({0..<m} \<inter> {i. from_nat_into G i \<in> allocation s})"
    by (auto simp: countable_finite edge)

  then have \<Delta>_primal: "bids_vec \<bullet> primal_sol (allocation (adwords_step s j)) = b {?i,j} + bids_vec \<bullet> primal_sol (allocation s)"
    by (auto simp: scalar_prod_def primal_sol_def insert_indices countable_finite edge)

  have \<Delta>_offline: "budget_constraint_vec \<bullet> offline_dual (adwords_step s j) = B ?i * (x s ?i * b {?i,j} / B ?i + b {?i,j} / ((c-1) * B ?i)) +
    budget_constraint_vec \<bullet> offline_dual s" (is "?B' = ?\<Delta> + ?B")
  proof -
    from \<open>?i \<in> L\<close> have "to_nat_on L ?i < card L"
      by (auto intro: L_enum_less_card)

    with \<open>?i \<in> L\<close> have "?B' = B ?i * x (adwords_step s j) ?i + (\<Sum>i\<in>{0..<card L} - {to_nat_on L ?i}. B (from_nat_into L i) * x (adwords_step s j) (from_nat_into L i))"
      unfolding budget_constraint_vec_def offline_dual_def scalar_prod_def
      by (auto simp: sum.remove[where x = "to_nat_on L ?i"])

    also have "\<dots> = B ?i * (x s ?i * (1 + b {?i, j} / B ?i) + b {?i, j} / ((c-1) * B ?i)) +
      (\<Sum>i\<in>{0..<card L} - {to_nat_on L ?i}. B (from_nat_into L i) * x s (from_nat_into L i))"
      by (rule arg_cong2[where f= plus])
         (auto simp add: x_upd intro!: sum.cong split: if_splits dest!: L_enum_inv)

    also have "\<dots> = B ?i * (x s ?i * b {?i,j} / B ?i + b {?i,j} / ((c-1) * B ?i)) + B ?i * x s ?i +
      (\<Sum>i\<in>{0..<card L} - {to_nat_on L ?i}. B (from_nat_into L i) * x s (from_nat_into L i))"
      by (auto simp: field_simps)

    also from \<open>?i \<in> L\<close> \<open>to_nat_on L ?i < card L\<close> have "\<dots> = ?\<Delta> +
      (\<Sum>i\<in>{0..<card L}. B (from_nat_into L i) * x s (from_nat_into L i))"
      by (auto simp: sum.remove[where x = "to_nat_on L ?i"])

    finally show ?thesis
      unfolding budget_constraint_vec_def offline_dual_def scalar_prod_def
      by simp
  qed

  from \<open>j \<in> R\<close> have *: "{0..<card R} \<inter> {i. from_nat_into R i = j} = {to_nat_on R j}"
    by (auto intro: R_enum_less_card)

  from \<open>j \<in> R\<close> have **: "{0..<card R} \<inter> - {i. from_nat_into R i = j} = {0..<card R} - {to_nat_on R j}"
    by auto

  from \<open>j \<in> R\<close> have "to_nat_on R j \<in> {0..<card R}"
    by (auto intro: R_enum_less_card)

  with \<open>z s j = 0\<close> \<open>j \<in> R\<close> have \<Delta>_online: "1\<^sub>v (card R) \<bullet> online_dual (adwords_step s j) = b {?i,j} * (1 - x s ?i) + 1\<^sub>v (card R) \<bullet> online_dual s"
    unfolding scalar_prod_def online_dual_def
    by (auto simp add: z_upd sum.If_cases * ** sum.remove)

  have "constraint_vec \<bullet> dual_sol (adwords_step s j) = budget_constraint_vec \<bullet> offline_dual (adwords_step s j) +
    1\<^sub>v (card R) \<bullet> online_dual (adwords_step s j)"
    unfolding constraint_vec_def dual_sol_def
    by (auto intro!: scalar_prod_append)

  also have "\<dots> = ?\<Delta> + ?B + b {?i,j} * (1 - x s ?i) + 1\<^sub>v (card R) \<bullet> online_dual s"
    by (simp add: \<Delta>_offline \<Delta>_online)

  also have "\<dots> = ?\<Delta> + b {?i,j} * (1 - x s ?i) + constraint_vec \<bullet> dual_sol s"
    unfolding constraint_vec_def dual_sol_def
    by (auto intro!: scalar_prod_append[symmetric])

  finally have \<Delta>_dual: "constraint_vec \<bullet> dual_sol (adwords_step s j) = 
    ?\<Delta> + b {?i,j} * (1 - x s ?i) + constraint_vec \<bullet> dual_sol s" .

  have "\<dots> * (1 - 1/c) = (?\<Delta> + b {?i,j} * (1 - x s ?i)) * (1 - 1/c) + bids_vec \<bullet> primal_sol (allocation s)"
    by (auto simp: field_simps assms)

  also from c_gt_1 \<open>?i \<in> L\<close> have "\<dots> = b {?i,j} + bids_vec \<bullet> primal_sol (allocation s)"
    by (auto simp: field_simps dest: budgets_pos)

  finally show ?thesis 
    by (auto simp flip: \<Delta>_primal simp: \<Delta>_dual)
qed (use assms in \<open>auto simp: adwords_step_def\<close>)

lemma dual_primal_times_adwords':
  assumes "constraint_vec \<bullet> dual_sol s * (1 - 1 / c) = bids_vec \<bullet> primal_sol (allocation s)"
  assumes "distinct js"
  assumes "set js \<subseteq> R"
  assumes "\<forall>j \<in> set js. z s j = 0"
  shows "constraint_vec \<bullet> dual_sol (adwords' s js) * (1 - 1 / c) = bids_vec \<bullet> primal_sol (allocation (adwords' s js))"
  using assms
proof (induction js arbitrary: s)
  case (Cons j js)

  then have step: "constraint_vec \<bullet> dual_sol (adwords_step s j) * (1 - 1/c) = bids_vec \<bullet> primal_sol (allocation (adwords_step s j))"
    by (auto intro: dual_primal_times_adwords_step)

  from Cons.prems have "\<forall>j' \<in> set js. z (adwords_step s j) j' = z s j'"
    by (intro ballI adwords_step_z_unchanged) auto

  with Cons.prems have "\<forall>j' \<in> set js. z (adwords_step s j) j' = 0"
    by simp

  with Cons step show ?case
    by (auto simp: adwords_Cons)
qed simp

lemma dual_primal_times_adwords:
  shows "constraint_vec \<bullet> dual_sol (adwords \<pi>) * (1 - 1/c) = bids_vec \<bullet> primal_sol (allocation (adwords \<pi>))"
  using perm c_gt_1
  by (auto intro!: dual_primal_times_adwords' scalar_prod_right_zero dest: permutations_of_setD)

lemma primal_almost_feasible_aux_adwords_step:
  assumes "i \<in> L"
  assumes "j \<in> R"
  assumes "allocation s \<subseteq> G"
  assumes "1/(c-1) * (c powr (total_bid_of (allocation s) i / B i) - 1) \<le> x s i"
  shows "1/(c-1) * (c powr (total_bid_of (allocation (adwords_step s j)) i / B i) - 1) \<le> x (adwords_step s j) i"
proof (cases j rule: adwords_step_cases[where s = s])
  case new_match
  let ?i' = "arg_max_on (\<lambda>i. b {i, j} * (1 - x s i)) {i. {i, j} \<in> G}"

  from new_match have allocation_eq: "allocation (adwords_step s j) = insert {?i',j} (allocation s)"
    by (simp add: adwords_step_def Let_def)

  show ?thesis
  proof (cases "?i' = i")
    case True
    then have *: "{e\<in>allocation (adwords_step s j). i \<in> e} = insert {i,j} {e\<in>allocation s. i \<in> e}"
      by (auto simp: allocation_eq)

    from new_match True have "{i,j} \<in> G"
      by blast

    with \<open>j \<notin> Vs (allocation s)\<close> have "1/(c-1) * (c powr (total_bid_of (allocation (adwords_step s j)) i / B i) - 1) =
      1/(c-1) * (c powr (total_bid_of (allocation s) i / B i) * c powr (b {i,j} / B i) - 1)"
      by (subst *, subst sum.insert)
         (auto dest: edges_are_Vs simp: ac_simps add_divide_distrib powr_add
               intro: finite_subset[OF _ finite_subset[OF \<open>allocation s \<subseteq> G\<close>]])

    also from c_gt_1 \<open>i \<in> L\<close> \<open>{i,j} \<in> G\<close> have "\<dots> \<le> 1/(c-1) * (c powr (total_bid_of (allocation s) i / B i) * (1 + b {i,j} / B i) - 1)"
      by (auto intro!: divide_right_mono c_powr_bid_ratio_le)

    also from c_gt_1 \<open>i \<in> L\<close> \<open>{i,j} \<in> G\<close> have "\<dots> = 1/(c-1) * (c powr (total_bid_of (allocation s) i / B i) - 1) * (1 + b {i,j} / B i) + b {i,j} / ((c-1) * B i)"
      by (auto simp: field_simps dest: budgets_pos)

    also from assms \<open>i \<in> L\<close> \<open>{i,j} \<in> G\<close> have "\<dots> \<le> x s i * (1 + b {i,j} / B i) + b {i,j} / ((c-1) * B i)"
      by (subst add_le_cancel_right, intro mult_right_mono)
         (auto dest!: bids_pos budgets_pos)

    also from new_match True have "\<dots> = x (adwords_step s j) i"
      by (simp add: adwords_step_def)

    finally show ?thesis .
  next
    case False
    with \<open>i \<in> L\<close> \<open>j \<in> R\<close> have *: "{e \<in> allocation (adwords_step s j). i \<in> e} = {e \<in> allocation s. i \<in> e}"
      by (auto simp: allocation_eq)

    from new_match assms False show ?thesis
      by (subst *) (simp add: adwords_step_def Let_def)
  qed
qed (use assms in \<open>simp_all add: adwords_step_def\<close>)

lemma no_charge_over_budget_adwords_step:
  assumes "i \<in> L" "j \<in> R"
  assumes total_bid_dual_bound: "\<And>i. i \<in> L \<Longrightarrow> 1/(c-1) * (c powr (total_bid_of (allocation s) i / B i) - 1) \<le> x s i"
  assumes "total_bid_of (allocation s) i > B i"
  shows "{e \<in> allocation (adwords_step s j). i \<in> e} = {e \<in> allocation s. i \<in> e}"
  using \<open>j \<in> R\<close>
proof (cases j rule: adwords_step_casesR[where s = s])
  case new_match
  let ?i' = "arg_max_on (\<lambda>i. b {i, j} * (1 - x s i)) {i. {i, j} \<in> G}"
  
  from \<open>?i' \<in> L\<close> \<open>x s ?i' < 1\<close> have "total_bid_of (allocation s) ?i' < B ?i'"
    apply (auto dest!: total_bid_dual_bound)
    by (smt (verit) budgets_pos c_gt_1 le_divide_eq_1_pos new_match(5) powr_mono powr_one)

  with \<open>total_bid_of (allocation s) i > B i\<close> have "i \<noteq> ?i'"
    by auto

  from new_match have "allocation (adwords_step s j) = insert {?i',j} (allocation s)"
    by (simp add: adwords_step_def Let_def)

  with \<open>i \<noteq> ?i'\<close> \<open>i \<in> L\<close> \<open>j \<in> R\<close> show ?thesis
    by auto
qed (use assms in \<open>simp_all add: adwords_step_def\<close>)

lemma max_over_budget_adwords_step:
  assumes "i \<in> L" "j \<in> R"
  assumes finite_M: "finite (allocation s)"
  assumes under_budget_before: "total_bid_of (allocation s) i \<le> B i"
  assumes over_budget_after: "total_bid_of (allocation (adwords_step s j)) i > B i"
  shows "total_bid_of (allocation (adwords_step s j)) i \<le> B i + Max {b {i,j} |j. {i,j} \<in> G}"
  using \<open>j \<in> R\<close>
proof (cases j rule: adwords_step_casesR[where s = s])
  case new_match
  let ?i' = "arg_max_on (\<lambda>i. b {i, j} * (1 - x s i)) {i. {i, j} \<in> G}"

  from new_match have allocation_insert: "allocation (adwords_step s j) = insert {?i',j} (allocation s)"
    by (simp add: adwords_step_def Let_def)

  have [simp]: "?i' = i"
  proof (rule ccontr)
    assume "?i' \<noteq> i"

    with \<open>i \<in> L\<close> \<open>?i' \<in> L\<close> \<open>{?i',j} \<in> G\<close> have "total_bid_of (allocation (adwords_step s j)) i = total_bid_of (allocation s) i"
      by (subst allocation_insert, subst total_bid_of_insert') auto

    with under_budget_before over_budget_after show False
      by linarith
  qed

  from finite_M \<open>j \<notin> Vs (allocation s)\<close>
  have "total_bid_of (allocation (adwords_step s j)) i = b {i,j} + total_bid_of (allocation s) i"
    by (subst allocation_insert, simp only: \<open>?i' = i\<close>, subst total_bid_of_insert)
       (auto dest: edges_are_Vs)

  also from under_budget_before \<open>{?i',j} \<in> G\<close> have "\<dots> \<le> Max {b {i,j} |j. {i,j} \<in> G} + B i"
    by (auto intro!: add_mono Max_ge intro: finite_bids simp: allocation_insert)

  finally show ?thesis
    by linarith
qed (use assms in \<open>auto simp: adwords_step_def split: if_splits\<close>)

lemma no_charge_over_budget_adwords:
  assumes "i \<in> L" "set js \<subseteq> R"
  assumes "allocation s \<subseteq> G"
  assumes "\<And>i. i \<in> L \<Longrightarrow> 1/(c-1) * (c powr (total_bid_of (allocation s) i / B i) - 1) \<le> x s i"
  assumes "total_bid_of (allocation s) i > B i"
  shows "{e \<in> allocation (adwords' s js). i \<in> e} = {e \<in> allocation s. i \<in> e}"
  using assms
proof (induction js arbitrary: s)
  case (Cons j js)

  then have edges_step: "{e \<in> allocation (adwords_step s j). i \<in> e} = {e \<in> allocation s. i \<in> e}"
    by (intro no_charge_over_budget_adwords_step) auto

  from Cons.prems have "{e \<in> allocation (adwords' s (j#js)). i \<in> e} = {e \<in> allocation (adwords_step s j). i \<in> e}"
    by (subst adwords_Cons, intro Cons.IH primal_almost_feasible_aux_adwords_step adwords_step_subgraph)
       (auto simp: edges_step)

  also from Cons.prems have "\<dots> = {e \<in> allocation s. i \<in> e}"
    by (intro no_charge_over_budget_adwords_step)  auto

  finally show ?case .
qed simp

lemma max_over_budget_adwords':
  assumes "i \<in> L" "set js \<subseteq> R"
  assumes "allocation s \<subseteq> G"
  assumes "\<And>i. i \<in> L \<Longrightarrow> 1/(c-1) * (c powr (total_bid_of (allocation s) i / B i) - 1) \<le> x s i"
  assumes "total_bid_of (allocation s) i \<le> B i + Max {b {i,j} |j. {i,j} \<in> G}"
  shows "total_bid_of (allocation (adwords' s js)) i \<le> B i + Max {b {i,j} |j. {i,j} \<in> G}"
  using assms
proof (induction js arbitrary: s)
  case (Cons j js)
  consider (over_budget_before) "total_bid_of (allocation s) i > B i" | (under_budget_before) "total_bid_of (allocation s) i \<le> B i"
    by linarith

  then show ?case
  proof cases
    case over_budget_before

    with Cons.prems have edges_eq: "{e \<in> allocation (adwords' s (j#js)). i \<in> e} = {e \<in> allocation s. i \<in> e}"
      by (intro no_charge_over_budget_adwords) auto

    then have "total_bid_of (allocation (adwords' s (j#js))) i = total_bid_of (allocation s) i"
      by simp

    also from Cons.prems over_budget_before have "\<dots> \<le> B i + Max {b {i,j} |j. {i,j} \<in> G}"
      by blast

    finally show ?thesis .
  next
    case under_budget_before
    consider (over_budget_after_step) "total_bid_of (allocation (adwords_step s j)) i > B i" |
      (under_budget_after_step) "total_bid_of (allocation (adwords_step s j)) i \<le> B i"
      by linarith

    then show ?thesis
    proof cases
      case over_budget_after_step

      with Cons.prems under_budget_before show ?thesis
        by (simp only: adwords_Cons, intro Cons.IH adwords_step_subgraph primal_almost_feasible_aux_adwords_step max_over_budget_adwords_step)
           (auto intro: finite_subset[where B = G])
    next
      case under_budget_after_step

      from \<open>i \<in> L\<close> have "B i \<le> B i + Max {b {i,j} |j. {i,j} \<in> G}"
        by (subst le_add_same_cancel1)
           (auto dest: max_bid_pos)
      
      with under_budget_after_step Cons.prems show ?thesis
        by (simp only: adwords_Cons, intro Cons.IH adwords_step_subgraph primal_almost_feasible_aux_adwords_step)
           auto
    qed
  qed
qed simp

lemma max_over_budget_adwords:
  assumes "i \<in> L" "set js \<subseteq> R"
  shows "total_bid_of (allocation (adwords js)) i \<le> B i + Max {b {i,j} |j. {i,j} \<in> G}"
  using assms c_gt_1
  by (force intro!: max_over_budget_adwords' intro: add_nonneg_nonneg dest: budgets_pos max_bid_pos)

lemma adwords_charge_of_ge_total_bid_of:
  assumes "i \<in> L" "set js \<subseteq> R"
  shows "charge_of (allocation (adwords js)) i \<ge> (1 - R_max) * (total_bid_of (allocation (adwords js)) i)"
proof (cases "total_bid_of (allocation (adwords js)) i > B i")
  case True

  have [intro!]: "allocation (adwords js) \<subseteq> G"
    by (auto intro!: adwords_subgraph)

  from \<open>i \<in> L\<close> parts_minimal have "finite {b {i,j} |j. {i,j} \<in> G}" "{b {i,j} |j. {i,j} \<in> G} \<noteq> {}"
    by (auto intro: finite_bids elim: left_neighborE)

  then obtain j where "{i,j} \<in> G" and [simp]: "Max {b {i,j} |j. {i,j} \<in> G} = b {i,j}"
    using Max_in by auto

  with bipartite_graph \<open>i \<in> L\<close> have "j \<in> R"
    by (auto dest: bipartite_edgeD)

  with \<open>{i,j} \<in> G\<close> \<open>i \<in> L\<close> have "total_bid_of (allocation (adwords js)) i * (1 - R_max) \<le>
    total_bid_of (allocation (adwords js)) i * (B i / (B i + Max {b {i,j} |j. {i,j} \<in> G}))"
    by (intro mult_left_mono)
       (auto intro: budget_over_budget_plus_bid_ge)

  also from True assms have "\<dots> \<le> B i"
    apply (auto dest!: max_over_budget_adwords)
    by (smt (verit, ccfv_SIG) assms(1) budgets_pos frac_less2 linordered_semiring_strict_class.mult_pos_pos nonzero_mult_div_cancel_left)

  also from True have "\<dots> = charge_of (allocation (adwords js)) i"
    by simp

  finally show ?thesis
    by (simp add: mult.commute)
next
  case False

  with assms R_max_pos show ?thesis
    by (auto intro!: mult_right_le adwords_subgraph)
qed

lemma adwords_allocation_value_ge:
  assumes "set js \<subseteq> R"
  shows "allocation_value (allocation (adwords js)) \<ge> (1 - R_max) * (bids_vec \<bullet> primal_sol (allocation (adwords js)))"
proof -
  have subgraph[intro]: "allocation (adwords js) \<subseteq> G"
    by (auto intro!: adwords_subgraph)

  have "(1 - R_max) * (bids_vec \<bullet> primal_sol (allocation (adwords js))) =
    (\<Sum>i\<in>L. (1 - R_max) * total_bid_of (allocation (adwords js)) i)"
    by (auto simp: sum_edges_eq_sum_vs[OF subgraph] primal_dot_bids_eq_sum_edges[OF subgraph] sum_distrib_left)

  also from assms have "\<dots> \<le> (\<Sum>i\<in>L. charge_of (allocation (adwords js)) i)"
    by (auto intro: sum_mono adwords_charge_of_ge_total_bid_of)

  finally show ?thesis 
    unfolding allocation_value_def .
qed

lemma adwords_integral:
  shows "one_sided_matching G (allocation (adwords \<pi>)) R"
  using perm
  by (auto intro: one_sided_matching_adwords dest: permutations_of_setD)

theorem adwords_competitive_ratio:
  assumes "max_value_allocation M"
  shows "allocation_value (allocation (adwords \<pi>)) / allocation_value M \<ge> (1 - 1/c) * (1 - R_max)"
  using assms
proof (intro mult_imp_le_div_pos max_value_allocation_pos_value)
  from assms c_gt_1 R_max_le_1 have "(1 - 1 / c) * (1 - R_max) * allocation_value M \<le> (1 - 1/c) * (1 - R_max) * (constraint_vec \<bullet> (dual_sol (adwords \<pi>)))"
    by (auto intro!: mult_left_mono max_value_allocation_bound_by_feasible_dual dual_feasible dual_nonneg)

  also have "\<dots> = (1 - R_max) * (bids_vec \<bullet> primal_sol (allocation (adwords \<pi>)))"
    by (simp flip: dual_primal_times_adwords)

  also from perm have "\<dots> \<le> allocation_value (allocation (adwords \<pi>))"
    by (auto intro: adwords_allocation_value_ge dest: permutations_of_setD)

  finally show "(1 - 1 / c) * (1 - R_max) * allocation_value M \<le> allocation_value (allocation (adwords \<pi>))" .
qed
end

end
