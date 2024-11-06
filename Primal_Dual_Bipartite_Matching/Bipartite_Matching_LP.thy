theory Bipartite_Matching_LP
  imports
    Even_More_Graph
    Jordan_Normal_Form.Matrix
begin

definition one_vec :: "nat \<Rightarrow> 'a :: one vec" ("1\<^sub>v") where
  "1\<^sub>v n = vec n (\<lambda>i. 1)"

lemma one_carrier_vec[simp]: "1\<^sub>v n \<in> carrier_vec n"
  unfolding one_vec_def carrier_vec_def by simp

lemma index_one_vec[simp]: "i < n \<Longrightarrow> 1\<^sub>v n $ i = 1" "dim_vec (1\<^sub>v n) = n"
  unfolding one_vec_def by simp_all

lemma to_nat_on_from_nat_into_less:
  assumes "finite A"
  assumes "i < card A"
  shows "to_nat_on A (from_nat_into A i) = i"
  using assms
  by (auto intro!: to_nat_on_from_nat_into dest!: to_nat_on_finite simp: bij_betw_def)

lemma to_nat_on_less_card:
  assumes "finite A"
  assumes "a \<in> A"
  shows "to_nat_on A a < card A"
  using assms
  by (auto dest: to_nat_on_finite bij_betwE)

text \<open>A version of the weak duality theorem which does not require equality
in the dual constraints, but non-negativity of the primal variables.\<close>
lemma weak_duality_theorem_nonneg_primal: 
  fixes A :: "'a :: linordered_comm_semiring_strict mat" 
  assumes A: "A \<in> carrier_mat nr nc" 
    and b: "b \<in> carrier_vec nr" 
    and c: "c \<in> carrier_vec nc"
    and x: "x \<in> carrier_vec nc" 
    and Axb: "A *\<^sub>v x \<le> b"
    and x0: "x \<ge> 0\<^sub>v nc"
    and y0: "y \<ge> 0\<^sub>v nr" 
    and yA: "A\<^sup>T *\<^sub>v y \<ge> c"
  shows "c \<bullet> x \<le> b \<bullet> y" 
proof -
  from y0 have y: "y \<in> carrier_vec nr" unfolding less_eq_vec_def by auto
  have "c \<bullet> x \<le> (A\<^sup>T *\<^sub>v y) \<bullet> x"
    unfolding scalar_prod_def
    using A c x yA x0
    by (auto intro!: sum_mono mult_right_mono simp: less_eq_vec_def)
  also have "\<dots> = y \<bullet> (A *\<^sub>v x)" using x y A by (metis transpose_vec_mult_scalar)
  also have "\<dots> \<le> y \<bullet> b" 
    unfolding scalar_prod_def using A b Axb y0
    by (auto intro!: sum_mono mult_left_mono simp: less_eq_vec_def)
  also have "\<dots> = b \<bullet> y" using y b by (metis comm_scalar_prod)
  finally show ?thesis . 
qed

locale bipartite_matching_lp = 
  fixes L :: "'a set" and R :: "'a set"
  fixes G :: "'a graph"

  assumes finite_L[intro,simp]: "finite L" and finite_R[intro,simp]: "finite R"
  assumes bipartite_graph: "bipartite G L R"
  assumes parts_minimal: "Vs G = L \<union> R"
begin

sublocale graph_abs G
  apply unfold_locales
  using bipartite_graph finite_L finite_R
  apply (intro finite_parts_bipartite_graph_invar)
  by auto

lemmas finite_graph[intro,simp] = finite_E
lemmas finite_vs[intro] = graph[THEN conjunct2]

lemma parts_disjoint[intro,simp]: "L \<inter> R = {}"
  using bipartite_graph
  by (auto dest: bipartite_disjointD)

lemma bipartite_FalseD[dest]:  "x \<in> L \<Longrightarrow> x \<in> R \<Longrightarrow> False"
  using bipartite_graph
  by (auto dest: bipartite_disjointD)

lemma left_neighborE:
  assumes "i \<in> L"
  obtains j where "j \<in> R" "{i,j} \<in> G"
proof -
  assume *: "(\<And>j. j \<in> R \<Longrightarrow> {i, j} \<in> G \<Longrightarrow> thesis)"
  from \<open>i \<in> L\<close> parts_minimal have "i \<in> Vs G" by blast

  then obtain e where "e \<in> G" "i \<in> e"
    by (auto elim: vs_member_elim)

  with \<open>i \<in> L\<close> bipartite_graph obtain j where "e = {i,j}" "j \<in> R"
    by (auto elim: bipartite_edgeE)

  with \<open>e \<in> G\<close> show "thesis"
    by (auto intro!: *)
qed

definition "n = card (Vs G)"
abbreviation "m \<equiv> card G"

definition Vs_enum :: "'a \<Rightarrow> nat" where
  "Vs_enum x = ( if x \<in> L then to_nat_on L x else to_nat_on R x + card L)"

definition Vs_enum_inv :: "nat \<Rightarrow> 'a" where
  "Vs_enum_inv i = ( if i < card L then from_nat_into L i else from_nat_into R (i - card L))"

abbreviation G_enum :: "'a set \<Rightarrow> nat" where
  "G_enum \<equiv> to_nat_on G"

definition incidence_matrix :: "real mat" where
  "incidence_matrix = mat n m (\<lambda>(i,j). of_bool (Vs_enum_inv i \<in> from_nat_into G j))"

definition primal_sol :: "'a graph \<Rightarrow> real vec" where
  "primal_sol M = vec m (\<lambda>i. of_bool (from_nat_into G i \<in> M))"

lemma incidence_matrix_carrier_mat[intro]: "incidence_matrix \<in> carrier_mat n m"
  unfolding incidence_matrix_def by simp

lemma dim_primal_sol[simp]: "dim_vec (primal_sol M) = m"
  by (simp add: primal_sol_def)

lemma primal_sol_carrier_vec[intro]: "primal_sol M \<in> carrier_vec m"
  unfolding carrier_vec_def by simp

lemma primal_sol_nonneg[intro]: "primal_sol M \<ge> 0\<^sub>v m"
  unfolding primal_sol_def less_eq_vec_def
  by simp

lemma primal_sol_empty[simp]: "primal_sol {} = 0\<^sub>v m"
  unfolding primal_sol_def by auto

lemma n_sum: "n = card L + card R"
  using parts_minimal
  by (auto simp: card_Un_disjoint n_def)

lemma geq_L_less_n_less_R: "card L \<le> i \<Longrightarrow> i < n \<Longrightarrow> i - card L < card R"
  by (auto simp: n_sum)

lemma geq_L_less_n_less_R': "\<not> i < card L \<Longrightarrow> i < n \<Longrightarrow> i - card L < card R"
  by (auto intro: geq_L_less_n_less_R)

lemma Vs_cases: 
  assumes "x \<in> Vs G"
  obtains "x \<in> L \<and> x \<notin> R" | "x \<in> R \<and> x \<notin> L"
  using assms parts_minimal
  by auto

lemma i_cases:
  assumes "i < n"
  obtains "i < card L" | "card L \<le> i" "i < card L + card R"
  using assms
  by (auto simp: n_sum) linarith

lemma
  shows L_inv_enum[simp]: "l \<in> L \<Longrightarrow> from_nat_into L (to_nat_on L l) = l"
    and L_enum_inv[simp]: "i < card L \<Longrightarrow> to_nat_on L (from_nat_into L i) = i"
    and R_inv_enum[simp]: "r \<in> R \<Longrightarrow> from_nat_into R (to_nat_on R r) = r"
    and R_enum_inv[simp]: "j < card R \<Longrightarrow> to_nat_on R (from_nat_into R j) = j"
  by (auto simp: countable_finite intro: to_nat_on_from_nat_into_less)

lemma
  shows L_enum_less_card: "l \<in> L \<Longrightarrow> to_nat_on L l < card L"
    and R_enum_less_card: "r \<in> R \<Longrightarrow> to_nat_on R r < card R"
  by (auto intro: to_nat_on_less_card)

lemma
  shows L_enum_less_n: "l \<in> L \<Longrightarrow> to_nat_on L l < n"
    and R_enum_less_n: "r \<in> R \<Longrightarrow> to_nat_on R r + card L < n"
  by (auto simp: n_sum dest: L_enum_less_card R_enum_less_card)

lemma
  shows Vs_enum_L: "l \<in> L \<Longrightarrow> Vs_enum l = to_nat_on L l"
    and Vs_enum_inv_from_nat_into_L: "i < card L \<Longrightarrow> Vs_enum_inv i = from_nat_into L i"
  unfolding Vs_enum_def Vs_enum_inv_def
  by auto

lemma
  shows Vs_enum_R: "r \<in> R \<Longrightarrow> Vs_enum r = to_nat_on R r + card L"
    and "card L \<le> i \<Longrightarrow> Vs_enum_inv i = from_nat_into R (i - card L)"
  unfolding Vs_enum_def Vs_enum_inv_def
  by auto

lemma Vs_enum_less_n: "x \<in> Vs G \<Longrightarrow> Vs_enum x < n"
  by (auto elim!: Vs_cases simp: Vs_enum_L Vs_enum_R intro: L_enum_less_n R_enum_less_n)

lemma 
  shows Vs_enum_less_n_L: "i \<in> L \<Longrightarrow> Vs_enum i < n"
    and Vs_enum_less_n_R: "j \<in> R \<Longrightarrow> Vs_enum j < n"
  by (auto simp: parts_minimal intro: Vs_enum_less_n)

lemma Vs_enum_less_card_L: "l \<in> L \<Longrightarrow> Vs_enum l < card L"
  by (auto simp: Vs_enum_L intro: L_enum_less_card)

lemma Vs_enum_geq_card_L: "r \<in> R \<Longrightarrow> card L \<le> Vs_enum r"
  by (auto simp: Vs_enum_R)

lemma
  shows Vs_inv_enum[simp]: "x \<in> Vs G \<Longrightarrow> Vs_enum_inv (Vs_enum x) = x"
    and Vs_enum_inv[simp]: "i < n \<Longrightarrow> Vs_enum (Vs_enum_inv i) = i"
  by (auto elim!: Vs_cases simp: Vs_enum_inv_def Vs_enum_def n_sum dest: L_enum_less_card intro!: from_nat_into)

lemma
  shows Vs_inv_enum_L[simp]: "i \<in> L \<Longrightarrow> Vs_enum_inv (Vs_enum i) = i"
    and Vs_inv_enum_R[simp]: "j \<in> R \<Longrightarrow> Vs_enum_inv (Vs_enum j) = j"
  by (simp_all add: parts_minimal)

lemma Vs_enum_inv_leftE:
  assumes "i < card L"
  obtains j where "j \<in> L" "Vs_enum_inv i = j"
  using assms
  by (metis Vs_enum_inv_def card.empty from_nat_into not_less_zero)

lemma Vs_enum_inv_rightE:
  assumes "i < n"
  assumes "\<not> i < card L"
  obtains j where "j \<in> R" "Vs_enum_inv i = j"
  using assms
  by (metis Vs_enum_inv_def add.right_neutral card.empty from_nat_into n_sum)

lemma G_enum_less_m: "e \<in> G \<Longrightarrow> G_enum e < m"
  using finite_E
  by (auto intro: to_nat_on_less_card)

lemma G_not_empty_if:
  assumes "i < m"
  shows "G \<noteq> {}"
  using assms
  by fastforce

lemma from_nat_into_G_E_aux:
  assumes "i < m"
  obtains e where "e \<in> G" "from_nat_into G i = e"
  using assms
  by (metis G_not_empty_if from_nat_into)

lemma from_nat_into_G_E:
  assumes "i < m"
  obtains l r where "{l,r} \<in> G" "from_nat_into G i = {l,r}" "l \<in> L" "r \<in> R"
  using assms bipartite_graph
  by (metis bipartite_edgeE from_nat_into_G_E_aux)

lemma Vs_enum_neqI: "v \<in> Vs G \<Longrightarrow> v' \<in> Vs G \<Longrightarrow> v \<noteq> v' \<Longrightarrow> Vs_enum v \<noteq> Vs_enum v'"
  by (metis Vs_inv_enum)

lemma G_enum_neqI: "e \<in> G \<Longrightarrow> e' \<in> G \<Longrightarrow> e \<noteq> e' \<Longrightarrow> G_enum e \<noteq> G_enum e'"
  by (simp add: countable_finite)

lemma the_lE:
  assumes "e \<in> G"
  obtains "(THE l. l \<in> L \<and> l \<in> e) \<in> L" "(THE l. l \<in> L \<and> l \<in> e) \<in> e"
proof
  from assms bipartite_graph obtain l r where "e = {l,r}" "l \<in> L" "r \<in> R"
    by (auto elim: bipartite_edgeE)

  then have "(THE l. l \<in> L \<and> l \<in> e) = l"
    by auto

  with \<open>e = {l,r}\<close> \<open>l \<in> L\<close> show "(THE l. l \<in> L \<and> l \<in> e) \<in> L" "(THE l. l \<in> L \<and> l \<in> e) \<in> e"
    by auto
qed

lemma the_l_subsetE:
  assumes "M \<subseteq> G"
  assumes "e \<in> M"
  obtains "(THE l. l \<in> L \<and> l \<in> e) \<in> L" "(THE l. l \<in> L \<and> l \<in> e) \<in> e"
  using assms
  by (auto elim: the_lE)

lemma the_l_subset_in_LI:
  assumes "M \<subseteq> G"
  assumes "e \<in> M"
  shows "(THE l. l \<in> L \<and> l \<in> e) \<in> L"
  using assms
  by (auto elim: the_l_subsetE)

lemma index_set_Int_is_doubleton:
  assumes "i \<in> L" "j \<in> R"
  shows "{0..<n} \<inter> {k. Vs_enum_inv k = i \<or> Vs_enum_inv k = j} = {Vs_enum i, Vs_enum j}"
  using assms
  by (auto intro: Vs_enum_less_n_L Vs_enum_less_n_R)

lemma primal_dot_One_card: "M \<subseteq> G \<Longrightarrow> 1\<^sub>v m \<bullet> primal_sol M = card M"
  by (auto simp: scalar_prod_def primal_sol_def countable_finite in_mono
           intro!: bij_betw_same_card[where f = "from_nat_into G"] bij_betwI[where g = G_enum] 
                   to_nat_on_less_card to_nat_on_from_nat_into_less)

lemma matching_feasible:
  assumes "matching M"
  shows "incidence_matrix *\<^sub>v primal_sol M \<le> 1\<^sub>v n"
  unfolding incidence_matrix_def primal_sol_def less_eq_vec_def mult_mat_vec_def scalar_prod_def
proof (intro conjI allI impI, simp_all, rule ccontr, simp add: not_le)
  fix i
  assume "i < n"
  let ?indices = "{0..<m} \<inter> {e. from_nat_into G e \<in> M} \<inter> {e. local.Vs_enum_inv i \<in> from_nat_into G e}"
  assume "1 < real (card ?indices)"

  then have gt_1: "1 < card ?indices"
    by simp

  then obtain ei1 where ei1: "ei1 \<in> ?indices"
    by (metis card_eq_0_iff ex_in_conv not_less0)

  with gt_1 have "0 < card (?indices - {ei1})"
    by auto

  then obtain ei2 where ei2: "ei2 \<in> ?indices" "ei1 \<noteq> ei2"
    by (metis Diff_eq_empty_iff card_0_eq card_ge_0_finite insertCI not_gr_zero subsetI)

  with ei1 have "from_nat_into G ei1 \<in> M" "from_nat_into G ei2 \<in> M" 
    "Vs_enum_inv i \<in> from_nat_into G ei1" "Vs_enum_inv i \<in> from_nat_into G ei2"
    by auto

  with \<open>matching M\<close> have "from_nat_into G ei1 = from_nat_into G ei2"
    by (auto dest: matching_unique_match)

  with ei1 ei2 \<open>ei1 \<noteq> ei2\<close> show False
    by (auto dest!: to_nat_on_from_nat_into_less[OF finite_E])
qed

lemma feasible_matching:
  assumes "M \<subseteq> G"
  assumes "incidence_matrix *\<^sub>v primal_sol M \<le> 1\<^sub>v n"
  shows "matching M"
proof (use assms in \<open>simp add: incidence_matrix_def primal_sol_def mult_mat_vec_def scalar_prod_def less_eq_vec_def\<close>, intro ccontr[where P = "matching M"])
  assume "M \<subseteq> G"
  let ?indices = "\<lambda>i. {0..<m} \<inter> {i. from_nat_into G i \<in> M} \<inter> {x. Vs_enum_inv i \<in> from_nat_into G x}"
  assume at_most_One: "\<forall>i<n. real (card (?indices i)) \<le> 1"
  assume "\<not>matching M"

  then obtain e1 e2 where "e1 \<in> M" "e2 \<in> M" "e1 \<noteq> e2" "e1 \<inter> e2 \<noteq> {}"
    unfolding matching_def
    by blast

  then obtain v where "v \<in> e1" "v \<in> e2"
    by blast

  with \<open>M \<subseteq> G\<close> \<open>e1 \<in> M\<close> have "v \<in> Vs G"
    by (auto intro: vs_member_intro)

  then have v_le_n: "Vs_enum v < n"
    by (auto intro: Vs_enum_less_n)

  from \<open>e1 \<in> M\<close> \<open>M \<subseteq> G\<close> \<open>v \<in> Vs G\<close> \<open>v \<in> e1\<close> have e1_in_indices: "G_enum e1 \<in> ?indices (Vs_enum v)"
    by (auto intro: G_enum_less_m simp: countable_finite[OF finite_E])

  from \<open>e2 \<in> M\<close> \<open>M \<subseteq> G\<close> \<open>v \<in> Vs G\<close> \<open>v \<in> e2\<close> have e2_in_indices: "G_enum e2 \<in> ?indices (Vs_enum v)"
    by (auto intro: G_enum_less_m simp: countable_finite[OF finite_E])

  from \<open>e1 \<in> M\<close> \<open>e2 \<in> M\<close> \<open>M \<subseteq> G\<close> \<open>e1 \<noteq> e2\<close> have "G_enum e1 \<noteq> G_enum e2"
    by (intro G_enum_neqI) auto

  with e1_in_indices have "0 < card (?indices (Vs_enum v) - {G_enum e2})"
    by (auto simp: card_gt_0_iff)

  with e2_in_indices have "1 < card (?indices (Vs_enum v))"
    by simp

  also from at_most_One v_le_n have "\<dots> \<le> 1"
    by auto

  finally have "1 < 1" ..

  then show False
    by fast
qed

lemma matching_iff_feasible:
  assumes "M \<subseteq> G"
  shows "matching M \<longleftrightarrow> incidence_matrix *\<^sub>v primal_sol M \<le> 1\<^sub>v n"
  using assms
  by (auto intro: feasible_matching matching_feasible)

lemma card_matching_bound_by_feasible_dual:
  fixes y :: "real vec"
  assumes "M \<subseteq> G"
  assumes "matching M"

  assumes "incidence_matrix\<^sup>T *\<^sub>v y \<ge> 1\<^sub>v m"
  assumes "y \<ge> 0\<^sub>v n"

  shows "card M \<le> 1\<^sub>v n \<bullet> y"
proof -
  from \<open>M \<subseteq> G\<close> have "card M = 1\<^sub>v m \<bullet> primal_sol M"
    by (auto simp: primal_dot_One_card)

  also from assms have "\<dots> \<le> 1\<^sub>v n \<bullet> y"
    by (auto intro: weak_duality_theorem_nonneg_primal[where A = incidence_matrix] matching_feasible)

  finally show ?thesis .
qed

lemma max_card_matching_bound_by_feasible_dual:
  fixes y :: "real vec"
  assumes "max_card_matching G M"

  assumes "incidence_matrix\<^sup>T *\<^sub>v y \<ge> 1\<^sub>v m"
  assumes "y \<ge> 0\<^sub>v n"

  shows "card M \<le> 1\<^sub>v n \<bullet> y"
  using assms
  by (auto intro: card_matching_bound_by_feasible_dual dest: max_card_matchingD)

end

end