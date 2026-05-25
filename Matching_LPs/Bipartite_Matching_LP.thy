(*
  Author: Christoph Madlener
*)

theory Bipartite_Matching_LP
  imports
    Matching_LP
begin

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

definition Vs_enum :: "'a \<Rightarrow> nat" where
  "Vs_enum = (\<lambda> x. (if x \<in> L then to_nat_on L x else to_nat_on R x + card L))"

definition Vs_enum_inv :: "nat \<Rightarrow> 'a" where
  "Vs_enum_inv = ( \<lambda> i. (if i < card L then from_nat_into L i else from_nat_into R (i - card L)))"

abbreviation G_enum :: "'a set \<Rightarrow> nat" where
  "G_enum \<equiv> to_nat_on G"

abbreviation G_enum_inv :: " nat \<Rightarrow> 'a set" where
  "G_enum_inv \<equiv> from_nat_into G"

lemma LR_and_G: "finite (L \<union> R)" 
  by simp

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

lemma bijections:"bij_betw Vs_enum (L \<union> R) {0..<card (L \<union> R)}"
                 "bij_betw G_enum G {0..<card G}"
proof-
  have L_collect_rewrite:"(L \<union> R) \<inter> {x . x \<notin> L} =  R"
    by blast
  have helper:"\<lbrakk>x < card (L \<union> R); \<forall>xa\<in>R. x \<noteq> to_nat_on R xa + card L\<rbrakk>
               \<Longrightarrow> \<exists>xa\<in>L. x = to_nat_on L xa" for x
  proof(goal_cases)
    case 1
    have x_le_L:"x < card L"
    proof(rule ccontr)
      assume asm: "\<not> x < card L"
      have a: "x - card L < card R"
        using "1"(1) asm card_Un_disjoint[OF finite_L finite_R parts_disjoint]
        by simp
       obtain xa where "to_nat_on R xa =  x - card L" "xa \<in> R"
         using R_enum_inv[OF a]  bot_nat_0.extremum_strict card.empty from_nat_into[of R] a 
         by fastforce
       moreover hence "x = to_nat_on R xa + card L"
         using asm by linarith
       ultimately show False
         using "1"(2) by blast
     qed
     show ?thesis 
       using L_enum_inv[OF x_le_L] from_nat_into[of L x] x_le_L by force
   qed
   have helpers: "\<lbrakk>x \<in> L; y \<in> L; to_nat_on L x = to_nat_on L y\<rbrakk> \<Longrightarrow> x = y"
                 "\<lbrakk>x \<in> L; y \<in> R; y \<notin> L; to_nat_on L x = to_nat_on R y + card L\<rbrakk> \<Longrightarrow> x = y"
                 "\<lbrakk>x \<in> R; x \<notin> L; y \<in> L; to_nat_on R x + card L = to_nat_on L y\<rbrakk> \<Longrightarrow> x = y"
                 "\<lbrakk>x \<in> R; x \<notin> L; y \<in> R; y \<notin> L; to_nat_on R x = to_nat_on R y\<rbrakk> \<Longrightarrow> x = y"
                 for x y
       using L_inv_enum L_enum_less_card  R_inv_enum  R_enum_less_card by fastforce+
  show "bij_betw Vs_enum (L \<union> R) {0..<card (L \<union> R)}"
    by(auto simp add: Vs_enum_def atLeast0LessThan bij_betw_def inj_on_def  image_def
                      L_collect_rewrite L_enum_less_card card_Un_disjoint trans_less_add1
                      R_enum_less_card 
               intro: helper helpers)
  show "bij_betw G_enum G {0..<card G}"
    using  to_nat_on_finite[OF  finite_graph]
    by(auto simp add: bij_betw_def inj_on_def countable_finite to_nat_on_less_card)
qed

lemma inversions: 
  "x \<in> L \<union> R \<Longrightarrow> Vs_enum_inv (Vs_enum x) = x"
  "e \<in> G \<Longrightarrow> G_enum_inv (G_enum e) = e"
  by(auto simp add: Vs_enum_def Vs_enum_inv_def countable_finite L_enum_less_card)

interpretation lp: matching_lp_basic "L \<union> R" G Vs_enum Vs_enum_inv G_enum G_enum_inv
  by(auto intro!: matching_lp_basic.intro bijections inversions simp add: parts_minimal)

abbreviation "m \<equiv> lp.m"
abbreviation "n \<equiv> lp.n"
abbreviation "primal_sol \<equiv> lp.primal_sol"
abbreviation "dual_sol \<equiv> lp.dual_sol"
abbreviation "incidence_matrix \<equiv> lp.incidence_matrix"

lemmas incidence_matrix_carrier_mat[intro] = lp.incidence_matrix_carrier_mat
lemmas dim_primal_sol[intro] = lp.dim_primal_sol
lemmas primal_sol_carrier_vec[intro] = lp.primal_sol_carrier_vec
lemmas primal_sol_nonneg[intro] = lp.primal_sol_nonneg
lemmas primal_sol_empty[simp] = lp.primal_sol_empty
lemmas n_def=lp.n_def
lemmas incidence_matrix_def = lp.incidence_matrix_def
lemmas primal_sol_def=lp.primal_sol_def
lemmas dual_sol_def=lp.dual_sol_def

lemma n_sum: "n = card L + card R"
  using parts_minimal
  by (auto simp: card_Un_disjoint n_def)

lemma geq_L_less_n_less_R: "\<lbrakk>card L \<le> i; i < n\<rbrakk> \<Longrightarrow> i - card L < card R"
  by (auto simp: n_sum)

lemma geq_L_less_n_less_R': "\<lbrakk>\<not> i < card L; i < n\<rbrakk> \<Longrightarrow> i - card L < card R"
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

lemma Vs_enum_neqI: "\<lbrakk>v \<in> Vs G; v' \<in> Vs G; v \<noteq> v'\<rbrakk> \<Longrightarrow> Vs_enum v \<noteq> Vs_enum v'"
  by (metis Vs_inv_enum)

lemma G_enum_neqI: "\<lbrakk>e \<in> G; e' \<in> G; e \<noteq> e'\<rbrakk> \<Longrightarrow> G_enum e \<noteq> G_enum e'"
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

lemmas primal_dot_One_card = lp.primal_dot_One_card
lemmas matching_feasible = lp.matching_feasible

lemma feasible_matching:
  assumes "M \<subseteq> G"
  assumes "incidence_matrix *\<^sub>v primal_sol M \<le> 1\<^sub>v n"
  shows "matching M"
proof (use assms in \<open>simp add: incidence_matrix_def primal_sol_def 
           mult_mat_vec_def scalar_prod_def less_eq_vec_def\<close>, intro ccontr[where P = "matching M"])
  assume "M \<subseteq> G"
  let ?indices = "\<lambda>i. {0..<m} \<inter> {i. from_nat_into G i \<in> M} \<inter> {x. Vs_enum_inv i \<in> from_nat_into G x}"
  assume at_most_One: "\<forall>i<n. (card (?indices i)) \<le> Suc 0"
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

lemmas card_matching_bound_by_feasible_dual = lp.card_matching_bound_by_feasible_dual
lemmas max_card_matching_bound_by_feasible_dual= lp.max_card_matching_bound_by_feasible_dual

end
end