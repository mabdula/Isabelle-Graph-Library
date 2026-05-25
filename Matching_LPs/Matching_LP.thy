(*
Authors: Christoph Madlener and Thomas Ammer
*)

theory Matching_LP
  imports
    Basic_Matching.Matching
    Jordan_Normal_Form.Matrix 
begin
subsection \<open>Definitions of certain matchings, to be moved\<close>

definition "feasible_max_dual V E w (y::'v \<Rightarrow> real) = 
 ((\<forall> v \<in> V. y v \<ge> 0) \<and> 
(\<forall> e \<in> E. \<forall> u v. e ={u, v} \<longrightarrow> y u +  y v \<ge> w e) \<and> 
Vs E \<subseteq> V \<and> finite V)"

lemma feasible_max_dualI:
  "\<lbrakk>\<And> v. v \<in> V \<Longrightarrow> y v \<ge> 0;
    \<And> e u v. e \<in> E \<Longrightarrow> e ={u, v} \<Longrightarrow> y u +  y v \<ge> w e;
    Vs E \<subseteq> V; finite V\<rbrakk>
  \<Longrightarrow> feasible_max_dual V E w y"
and feasible_max_dualE:
  "\<lbrakk>feasible_max_dual V E w y;
    \<lbrakk>\<And> v. v \<in> V \<Longrightarrow> y v \<ge> 0; \<And> e u v. e \<in> E \<Longrightarrow> e ={u, v} \<Longrightarrow> y u +  y v \<ge> w e;
     Vs E \<subseteq> V; finite V\<rbrakk> \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
and feasible_max_dualD:
  "\<lbrakk>feasible_max_dual V E w y; v \<in> V\<rbrakk> \<Longrightarrow> y v \<ge> 0"
  "\<lbrakk>feasible_max_dual V E w y; e \<in> E; e ={u, v}\<rbrakk> \<Longrightarrow> y u +  y v \<ge> w e"
  "feasible_max_dual V E w y \<Longrightarrow>  Vs E \<subseteq> V"
  "feasible_max_dual V E w y \<Longrightarrow>  finite V"
  by(auto simp add: feasible_max_dual_def)

definition "min_feasible_max_dual V E w y =
 (feasible_max_dual V E w y \<and>
 (\<forall> y'. feasible_max_dual V E w y' \<longrightarrow> sum y V \<le> sum y' V))"

lemma min_feasible_max_dualE:
  "\<lbrakk>min_feasible_max_dual V E w y;
     \<lbrakk>feasible_max_dual V E w y; \<And> y'. feasible_max_dual V E w y' \<Longrightarrow> sum y V \<le> sum y' V\<rbrakk> \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
and min_feasible_max_dualI:
  "\<lbrakk>feasible_max_dual V E w y; \<And> y'. feasible_max_dual V E w y' \<Longrightarrow> sum y V \<le> sum y' V\<rbrakk>
   \<Longrightarrow> min_feasible_max_dual V E w y"
and min_feasible_max_dualD:
  "min_feasible_max_dual V E w y \<Longrightarrow>feasible_max_dual V E w y"
  "\<lbrakk>min_feasible_max_dual V E w y; feasible_max_dual V E w y'\<rbrakk> \<Longrightarrow> sum y V \<le> sum y' V"
  by(auto simp add: min_feasible_max_dual_def)

definition "tight_subgraph E w y = {{u, v} | u v. {u, v} \<in> E \<and> w {u, v} = y u + y v}"

lemma in_tight_subgraphI:
  "\<lbrakk>e = {u, v}; {u, v} \<in> E; w {u, v} = y u + y v\<rbrakk> \<Longrightarrow> e \<in> tight_subgraph E w y"
and in_tight_subgraphE:
  "\<lbrakk>e \<in> tight_subgraph E w y;
    \<And> u v. \<lbrakk>e = {u, v}; {u, v} \<in> E; w {u, v} = y u + y v\<rbrakk> \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
and in_tight_subgraphD:
  "\<lbrakk>e \<in> tight_subgraph E w y; e = {u, v}\<rbrakk>  \<Longrightarrow> w {u, v} = (y::'v \<Rightarrow> real) u + y v"
  by(auto simp add: tight_subgraph_def doubleton_eq_iff insert_commute)

lemma tight_subgraph_is_subgraph:
  "tight_subgraph E w y \<subseteq> E"
  by(auto simp add: tight_subgraph_def)

definition "non_zero_vertices V y = {v | v. v \<in> V \<and> y v \<noteq> 0}"

lemma in_non_zero_verticesI:
  "\<lbrakk>v \<in> V; y v \<noteq> 0\<rbrakk> \<Longrightarrow> v \<in> non_zero_vertices V y"
and in_non_zero_verticesE:
  "\<lbrakk>v \<in> non_zero_vertices V y; \<lbrakk>v \<in> V; y v \<noteq> 0\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto simp add:  non_zero_vertices_def)

definition "feasible_min_perfect_dual E w (y::'v \<Rightarrow> real) = 
 ((\<forall> e \<in> E. \<forall> u v. e = {u, v} \<longrightarrow> y u +  y v \<le> w e) )"

lemma feasible_min_perfect_dualI:
  "\<lbrakk>\<And> e u v. \<lbrakk>e \<in> E; e = {u, v}\<rbrakk> \<Longrightarrow> y u +  y v \<le> w e\<rbrakk>
   \<Longrightarrow> feasible_min_perfect_dual E w y"
and feasible_min_perfect_dualE:
  "\<lbrakk>feasible_min_perfect_dual E w y;
    (\<And> e u v. \<lbrakk>e \<in> E; e = {u, v}\<rbrakk> \<Longrightarrow> y u +  y v \<le> w e) \<Longrightarrow>P\<rbrakk> \<Longrightarrow> P"
and feasible_min_perfect_dualD:
  "\<lbrakk>feasible_min_perfect_dual E w y; e \<in> E; e = {u, v}\<rbrakk> \<Longrightarrow> y u +  y v \<le> w e"
  by(auto simp add: feasible_min_perfect_dual_def)

definition "max_feasible_min_perfect_dual E w y =
 (feasible_min_perfect_dual E w y \<and>
 (\<forall> y'. feasible_min_perfect_dual E w y' \<longrightarrow> sum y (Vs E) \<ge> sum y' (Vs E)))"

lemma max_feasible_min_perfect_dualE:
  "\<lbrakk>max_feasible_min_perfect_dual E w y;
    \<lbrakk>feasible_min_perfect_dual E w y;
     \<And> y'. feasible_min_perfect_dual  E w y' \<Longrightarrow> sum y (Vs E) \<ge> sum y' (Vs E)\<rbrakk> \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
and max_feasible_min_perfect_dualI:
  "\<lbrakk>feasible_min_perfect_dual E w y;
   \<And> y'. feasible_min_perfect_dual E w y' \<Longrightarrow> sum y (Vs E) \<ge> sum y' (Vs E)\<rbrakk>
   \<Longrightarrow> max_feasible_min_perfect_dual E w y"
and max_feasible_min_perfect_dualD:
  "max_feasible_min_perfect_dual E w y \<Longrightarrow>feasible_min_perfect_dual E w y"
  "\<lbrakk>max_feasible_min_perfect_dual E w y; feasible_min_perfect_dual E w y'\<rbrakk>
   \<Longrightarrow> sum y (Vs E) \<ge> sum y' (Vs E)"
  by(auto simp add: max_feasible_min_perfect_dual_def)

subsection \<open>Translations between matchings and LPs\<close>

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

subsection \<open>LP Theory: Weak Duality and Slackness\<close>

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
(*TODO fix type*)
lemma general_complementary_slackness: 
  fixes A :: "real mat" 
  assumes A: "A \<in> carrier_mat nr nc" 
    and b: "b \<in> carrier_vec nr" 
    and c: "c \<in> carrier_vec nc"
    and x: "x \<in> carrier_vec nc" 
    and y: "y \<in> carrier_vec nr"
    and slack_primal: "(b - A *\<^sub>v x)\<bullet>y = 0"
    and slack_dual: "(c - A\<^sup>T *\<^sub>v y)\<bullet>x = 0"
  shows "c \<bullet> x = b \<bullet> y" 
proof-
  have a1:"b\<bullet>y - (A *\<^sub>v x) \<bullet>y = 0" 
    using slack_primal by (metis A b minus_scalar_prod_distrib mult_mat_vec_carrier x y)
  hence a2:"b\<bullet>y  =  (A *\<^sub>v x) \<bullet>y" by auto
  have "c\<bullet>x - (A\<^sup>T *\<^sub>v y)\<bullet>x = 0"
    using slack_dual
    by (metis A c carrier_matD(2) carrier_vecI dim_mult_mat_vec index_transpose_mat(2)
        minus_scalar_prod_distrib x)
  hence a3:  "c\<bullet>x = (A\<^sup>T *\<^sub>v y)\<bullet>x " by simp
  moreover have "... = (A *\<^sub>v x) \<bullet>y"
    by (metis A comm_scalar_prod mult_mat_vec_carrier transpose_vec_mult_scalar x y)
  ultimately show ?thesis
    using a2 by simp
qed
(*Very similar to what is in the AFP*)
lemma weak_duality_theorem_primal_eq: 
  fixes A :: "'a :: linordered_comm_semiring_strict mat" 
  assumes A: "A \<in> carrier_mat nr nc" 
    and c: "c \<in> carrier_vec nc"
    and x: "x \<in> carrier_vec nc" 
    and y: "y \<in> carrier_vec nr" 
    and Axb: "A *\<^sub>v x = b"   
    and x0: "x \<ge> 0\<^sub>v nc" 
    and yA: "A\<^sup>T *\<^sub>v y \<le> c"
  shows "c \<bullet> x \<ge> b \<bullet> y" 
proof -
  have "b \<bullet> y = (A *\<^sub>v x) \<bullet> y" 
    by (simp add: Axb)
  also have "\<dots> = x \<bullet> (A\<^sup>T *\<^sub>v y)"
    by(auto simp add: transpose_vec_mult_scalar[symmetric, of _ nc nr] A x y)
  also have "\<dots> \<le> x \<bullet> c"  
    using yA A x0
    by(auto intro!: sum_mono mult_left_mono simp: scalar_prod_def less_eq_vec_def)
  finally show ?thesis 
    by(simp add: comm_scalar_prod[OF c x])
qed

lemma eq_primal_complementary_slackness: 
  fixes A :: "real mat" 
  assumes A: "A \<in> carrier_mat nr nc" 
    and b: "b \<in> carrier_vec nr" 
    and c: "c \<in> carrier_vec nc"
    and x: "x \<in> carrier_vec nc" 
    and y: "y \<in> carrier_vec nr"
    and primal_feasible: "A *\<^sub>v x = b"
    and slack_dual: "(c - A\<^sup>T *\<^sub>v y)\<bullet>x = 0"
  shows "c \<bullet> x = b \<bullet> y" 
  using assms
  by(auto intro!: general_complementary_slackness )

subsection \<open>Translations between Graphs and LPs\<close>

locale matching_lp_basic = 
  fixes V :: "'a set"
  fixes G :: "'a graph"
  fixes Vs_enum::"'a \<Rightarrow> nat"
  fixes Vs_enum_inv::"nat \<Rightarrow> 'a"
  fixes G_enum::"'a set \<Rightarrow> nat"
  fixes G_enum_inv::"nat \<Rightarrow> 'a set"
  assumes G_in_V: "Vs G \<subseteq> V" (*and finite_V: "finite V"*)
  and bij_Vs_enum: "bij_betw Vs_enum V {0..< card V}"
  and Vs_enum_Vs_enum_inv: "\<And> x. x \<in> V \<Longrightarrow> Vs_enum_inv (Vs_enum x) = x"
  and bij_G_enum: "bij_betw G_enum G {0..< card G}"
  and G_enum_G_enum_inv: "\<And> e. e \<in> G \<Longrightarrow> G_enum_inv (G_enum e) = e"
begin

named_theorems matching_lp_theorems

lemma bij_Vs_enum_inv[matching_lp_theorems]: "bij_betw Vs_enum_inv {0..< card V} V"
proof-
  have "\<lbrakk>x < card V; y < card V; Vs_enum_inv x = Vs_enum_inv y\<rbrakk> \<Longrightarrow> x = y" for x y
    by (metis Vs_enum_Vs_enum_inv atLeastLessThan_iff bij_Vs_enum bij_betw_def imageE zero_le)
  moreover have "xa < card V \<Longrightarrow> Vs_enum_inv xa \<in> V" for xa
    by (metis (full_types) atLeastLessThan_iff bij_Vs_enum bij_betw_def imageE
        Vs_enum_Vs_enum_inv  zero_le)
  moreover have "x \<in> V \<Longrightarrow> x \<in> Vs_enum_inv ` {0..<card V}" for x
    by (metis Vs_enum_Vs_enum_inv bij_Vs_enum bij_betwE imageI)
  ultimately show ?thesis
    by(auto simp add: bij_betw_def inj_on_def)
qed

lemma bij_G_enum_inv[matching_lp_theorems]: "bij_betw G_enum_inv {0..< card G} G"
proof-
  have "\<lbrakk>x < card G; y < card G; G_enum_inv x = G_enum_inv y\<rbrakk> \<Longrightarrow> x = y" for x y
    by (metis G_enum_G_enum_inv atLeastLessThan_iff bij_G_enum bij_betw_def imageE
        zero_le)
  moreover have "xa < card G \<Longrightarrow> G_enum_inv xa \<in> G" for xa
    by (metis (no_types, lifting) G_enum_G_enum_inv atLeastLessThan_iff bij_G_enum bij_betw_def
        imageE zero_le)
  moreover have "x \<in> G \<Longrightarrow> x \<in> G_enum_inv ` {0..<card G}" for x
    by (metis G_enum_G_enum_inv bij_G_enum bij_betwE image_eqI)
  ultimately show ?thesis
    by(auto simp add: bij_betw_def inj_on_def)
qed

definition "n = card V"
abbreviation "m \<equiv> card G"

definition incidence_matrix :: "real mat" where
  "incidence_matrix = mat n m (\<lambda>(i,j). of_bool (Vs_enum_inv i \<in> G_enum_inv j))"

definition primal_sol :: "'a graph \<Rightarrow> real vec" where
  "primal_sol M = vec m (\<lambda>i. of_bool (G_enum_inv i \<in> M))"

definition weight_vect::"('a set \<Rightarrow> real) \<Rightarrow> real vec" where
  "weight_vect w = vec m (\<lambda> i. w (G_enum_inv i))"

definition dual_sol::"('a \<Rightarrow> real) \<Rightarrow> real vec" where
  "dual_sol y = vec n (\<lambda> i. y (Vs_enum_inv i))"

lemmas [matching_lp_theorems] = 
  primal_sol_def incidence_matrix_def weight_vect_def dual_sol_def n_def

lemma incidence_matrix_carrier_mat[intro, matching_lp_theorems]: 
  "incidence_matrix \<in> carrier_mat n m"
  unfolding incidence_matrix_def by simp

lemma dim_primal_sol[simp,matching_lp_theorems]: "dim_vec (primal_sol M) = m"
  by (simp add: primal_sol_def)

lemma primal_sol_carrier_vec[intro,matching_lp_theorems]: "primal_sol M \<in> carrier_vec m"
  unfolding carrier_vec_def by simp

lemma primal_sol_nonneg[intro,matching_lp_theorems]: "primal_sol M \<ge> 0\<^sub>v m"
  unfolding primal_sol_def less_eq_vec_def
  by simp

lemma primal_sol_empty[simp]: "primal_sol {} = 0\<^sub>v m"
  unfolding primal_sol_def by auto

lemma unit_weight_vect_is_1_vect[simp,matching_lp_theorems]: "weight_vect (\<lambda>e. 1) = 1\<^sub>v m"
  by(auto simp add: weight_vect_def)

lemma dim_weight_vect[simp,matching_lp_theorems]: "dim_vec (weight_vect w) = m" 
and weight_vect_carrier_vec[intro,matching_lp_theorems]: " weight_vect w \<in> carrier_vec m"
  by(auto simp add: weight_vect_def)

lemma dim_weight_dual_sol[simp,matching_lp_theorems]: "dim_vec (dual_sol y) = n" 
and dual_sol_carrier_vec[intro,matching_lp_theorems]: "dual_sol y \<in> carrier_vec n"
  by(auto simp add: dual_sol_def)

lemma V_inv_enum[simp,matching_lp_theorems]: "v \<in> V \<Longrightarrow> Vs_enum_inv (Vs_enum v) = v"
  by(auto intro!: Vs_enum_Vs_enum_inv)

lemma G_inv_enum[simp,matching_lp_theorems]: "e \<in> G \<Longrightarrow> G_enum_inv (G_enum e) = e"
  by(auto intro!: G_enum_G_enum_inv)

lemma V_enum_inv[simp,matching_lp_theorems]: 
  assumes"i < card V" 
  shows "Vs_enum (Vs_enum_inv i) = i"
proof(rule ccontr)
  assume asm: "Vs_enum (Vs_enum_inv i) \<noteq> i"
  have "i \<in> {0..<card V}"
    using assms by auto
  show False
  using bij_Vs_enum bij_Vs_enum_inv asm Vs_enum_Vs_enum_inv \<open>i \<in> {0..<card V}\<close>
  unfolding bij_betw_def inj_on_def 
  by blast
qed

lemma G_enum_inv[simp,matching_lp_theorems]: 
  assumes"i < card G" 
  shows "G_enum (G_enum_inv i) = i"
proof(rule ccontr)
  assume asm: "G_enum (G_enum_inv i) \<noteq> i"
  have "i \<in> {0..<card G}"
    using assms by auto
  show False
    using bij_G_enum bij_G_enum_inv asm G_enum_G_enum_inv \<open>i \<in> {0..<card G}\<close> image_iff[of i G_enum]
    unfolding bij_betw_def inj_on_def 
    by fastforce
qed

lemma  Vs_enum_less_card[matching_lp_theorems]: "v \<in> V \<Longrightarrow> Vs_enum v < card V"
  by (metis atLeastLessThan_iff bij_Vs_enum bij_betw_def imageI)

lemma Vs_enum_less_n[matching_lp_theorems]: "v \<in> V \<Longrightarrow> Vs_enum v  < n"
  by (simp add: Vs_enum_less_card n_def)

lemma Vs_of_G_enum_less_n[matching_lp_theorems]: "x \<in> Vs G \<Longrightarrow> Vs_enum x < n"
  using G_in_V Vs_enum_less_n by auto

lemma
  shows Vs_inv_enum[simp,matching_lp_theorems]: "x \<in> Vs G \<Longrightarrow> Vs_enum_inv (Vs_enum x) = x"
    and Vs_enum_inv[simp,matching_lp_theorems]: "i < n \<Longrightarrow> Vs_enum (Vs_enum_inv i) = i"
    and Vs_enum_inv_in_G[simp,matching_lp_theorems]: "i < n \<Longrightarrow> (Vs_enum_inv i) \<in> V"
  using G_in_V V_inv_enum apply blast
  apply (simp add: n_def)
  by (metis atLeastLessThan_iff bij_Vs_enum_inv bij_betwE n_def zero_le)

lemma G_enum_inv_in_G[simp,matching_lp_theorems]: "i < m \<Longrightarrow> (G_enum_inv i) \<in> G"
and G_enum_less_card_G[simp,matching_lp_theorems]: "e \<in> G \<Longrightarrow> (G_enum e) < card G"
  using atLeastLessThan_iff bij_G_enum_inv bij_G_enum bij_betwE
  by force+

lemma Vs_enum_inv_inj_below_n[matching_lp_theorems]:
  "\<lbrakk>Vs_enum_inv i = Vs_enum_inv j; i < n; j < n\<rbrakk> \<Longrightarrow> i = j"
  using Vs_enum_inv by fastforce

lemma dual_sol_i_is[matching_lp_theorems]: "i < n \<Longrightarrow> dual_sol y $ i =  y (Vs_enum_inv i)"
  by(auto simp add: dual_sol_def)

lemma G_enum_inv_same_args_same[matching_lp_theorems]:
  "\<lbrakk>i < m; j < m; G_enum_inv i = G_enum_inv j\<rbrakk> \<Longrightarrow> i = j"
  by (metis G_enum_inv)

lemma matching_zero_one_entries[matching_lp_theorems]:
  assumes "matching M" 
  shows  "\<forall> i < n. (incidence_matrix *\<^sub>v primal_sol M ) $ i = 0 \<or>
                   (incidence_matrix *\<^sub>v primal_sol M ) $ i = 1"
  unfolding incidence_matrix_def primal_sol_def mult_mat_vec_def scalar_prod_def
proof (intro conjI allI impI, simp_all, rule ccontr, simp add: not_le)
  fix i
  assume "i < n"
  let ?indices = "{0..<m} \<inter> {e. G_enum_inv  e \<in> M} \<inter> {e. Vs_enum_inv i \<in> G_enum_inv  e}"
  assume "?indices \<noteq> {} \<and> (card ?indices) \<noteq>  Suc 0"
  moreover have "finite ?indices" 
    by blast
  ultimately have gt_1: "1 < card ?indices" 
    using Suc_lessI   card_gt_0_iff 
    by (metis One_nat_def)
  then obtain ei1 where ei1: "ei1 \<in> ?indices"
    by (metis card_eq_0_iff ex_in_conv not_less0)
  with gt_1 have "0 < card (?indices - {ei1})"
    by auto
  then obtain ei2 where ei2: "ei2 \<in> ?indices" "ei1 \<noteq> ei2"
    by (metis Diff_eq_empty_iff card_0_eq card_ge_0_finite insertCI not_gr_zero subsetI)
  with ei1 have "G_enum_inv ei1 \<in> M" "G_enum_inv ei2 \<in> M" 
    "Vs_enum_inv i \<in> G_enum_inv ei1" "Vs_enum_inv i \<in> G_enum_inv ei2"
    by auto
  with \<open>matching M\<close> have "G_enum_inv ei1 = G_enum_inv ei2"
    by (auto dest: matching_unique_match)
  with ei1 ei2 \<open>ei1 \<noteq> ei2\<close> show False
    using G_enum_inv by fastforce
qed

subsection \<open>Optimality Criteria\<close>

lemma matching_feasible[matching_lp_theorems]:
  assumes "matching M"
  shows "incidence_matrix *\<^sub>v primal_sol M \<le> 1\<^sub>v n"
  using  matching_zero_one_entries[OF assms]  incidence_matrix_carrier_mat 
  by (auto simp add: less_eq_vec_def)

lemma primal_dot_weight_vect_weight_sum[matching_lp_theorems]:
 "M \<subseteq> G \<Longrightarrow> weight_vect w \<bullet> primal_sol M = sum w M"
  by (auto simp: scalar_prod_def primal_sol_def countable_finite in_mono weight_vect_def
           intro!: bij_betwI[where g = G_enum] comm_monoid_add_class.sum.reindex_bij_betw)
  
lemma dual_sol_lp_feasible[matching_lp_theorems]:
  assumes "feasible_max_dual V G w y" "dblton_graph G"
  shows "incidence_matrix\<^sup>T *\<^sub>v dual_sol y \<ge> weight_vect w" "dual_sol y \<ge> 0\<^sub>v n"
  unfolding incidence_matrix_def dual_sol_def less_eq_vec_def mult_mat_vec_def scalar_prod_def
            weight_vect_def
proof (all \<open>intro conjI allI impI\<close>, simp_all, goal_cases)
  case (1 i)
  let ?indices = "{0..<n} \<inter> {ix. Vs_enum_inv ix \<in>  G_enum_inv i}"
  have ei_in_G:"G_enum_inv i \<in> G"
    by (simp add: "1")
  then obtain u v where uv:" G_enum_inv i = {u, v}" "u \<noteq> v" 
    using assms(2) by auto
  hence uv_inG: "u \<in> Vs G" "v \<in> Vs G" 
    using ei_in_G by auto
  obtain ui vi where ui_vi:"ui < n" "vi < n" "ui \<noteq> vi"
    "Vs_enum_inv ui = u" "Vs_enum_inv vi = v"  "Vs_enum_inv ui \<noteq> Vs_enum_inv vi"
    using Vs_inv_enum[OF uv_inG(1)] Vs_inv_enum[OF uv_inG(2)]
          Vs_of_G_enum_less_n[OF uv_inG(1)] Vs_of_G_enum_less_n[OF uv_inG(2)] uv(2)
    by fastforce
  have "w (G_enum_inv i) \<le> y (Vs_enum_inv ui) + y (Vs_enum_inv vi)"
    using feasible_max_dualD(2)[OF assms(1) ei_in_G uv(1)] ui_vi(4,5) by auto
  moreover have "{0..<n} \<inter> {ia . Vs_enum_inv ia \<in> G_enum_inv i} = { ui,  vi}" 
    using ui_vi uv Vs_enum_inv_inj_below_n by auto
  ultimately show ?case 
    using ui_vi(3) by simp
next
  case (2 i)
  then have "Vs_enum_inv i \<in> V" 
    using Vs_enum_inv_in_G by simp
  thus ?case
    using feasible_max_dualD(1)[OF assms(1)] by auto
qed

lemma dual_dot_y_vect_y_sum[matching_lp_theorems]: "1\<^sub>v n \<bullet> dual_sol y = sum y V"
  by(auto simp: scalar_prod_def dual_sol_def countable_finite in_mono weight_vect_def
                  Vs_enum_less_n
        intro!: Vs_enum_inv_in_G  bij_betwI[where f = Vs_enum_inv and g = Vs_enum]
                comm_monoid_add_class.sum.reindex_bij_betw)

lemma max_weight_matching_bound_by_feasible_dual[matching_lp_theorems]:
  fixes y :: "real vec"
  assumes "graph_matching G M"
  assumes "incidence_matrix\<^sup>T *\<^sub>v y \<ge> weight_vect w"
  assumes "y \<ge> 0\<^sub>v n"
  shows "sum w M \<le> 1\<^sub>v n \<bullet> y"
proof -
   have a1:"weight_vect w \<bullet> primal_sol M = sum w M"
    using assms(1) by (auto simp: primal_dot_weight_vect_weight_sum)
  moreover from assms have "\<dots> \<le> 1\<^sub>v n \<bullet> y"
    unfolding a1[symmetric]
    by(auto intro: weak_duality_theorem_nonneg_primal[OF incidence_matrix_carrier_mat]
                   matching_feasible)    
  ultimately show ?thesis by simp
qed

corollary max_matching_weak_duality[matching_lp_theorems]:
  assumes "feasible_max_dual V G w y" "graph_matching G M"
          "graph_invar G"
  shows   "sum w M \<le> sum y V"
proof-
  have G_props: "matching M" "M \<subseteq> G" " dblton_graph G"
    using assms (2,3) by auto
  show ?thesis
  using dual_dot_y_vect_y_sum[of y] 
        max_weight_matching_bound_by_feasible_dual[OF assms(2)]
        dual_sol_lp_feasible[OF assms(1) G_props(3)]
  by force
qed

corollary max_matching_pd_optimality[matching_lp_theorems]:
  assumes "feasible_max_dual V G w y" "graph_matching G M"
          "graph_invar G"  "sum w M = sum y V"
    shows "max_weight_matching G w M" "min_feasible_max_dual V G w y"
  using assms max_matching_weak_duality
  by(force intro!: max_weight_matchingI min_feasible_max_dualI)+

lemma primal_non_zero_iff[matching_lp_theorems]: "i < m \<Longrightarrow> 
    (primal_sol M) $ i \<noteq> 0 \<longleftrightarrow> (\<exists> e. G_enum_inv i = e \<and> e \<in> M)" 
  by(auto simp add: primal_sol_def)

lemma primal_gtr_zero_iff[matching_lp_theorems]: "i < m \<Longrightarrow> 
    (primal_sol M) $ i > 0 \<longleftrightarrow> (\<exists> e. G_enum_inv i = e \<and> e \<in> M)" 
  by(auto simp add: primal_sol_def)

lemma primal_geq_zero[matching_lp_theorems]: "i < m \<Longrightarrow> 
    (primal_sol M) $ i \<ge> 0" 
  by(auto simp add: primal_sol_def)

lemma 
  assumes "graph_matching G M" "graph_invar G" "M \<subseteq> tight_subgraph G w y"
    shows zero_slack_if_tight_matching[matching_lp_theorems]:
    "(incidence_matrix\<^sup>T *\<^sub>v dual_sol y  - weight_vect w) \<bullet> primal_sol M = 0"
    "(weight_vect w - incidence_matrix\<^sup>T *\<^sub>v dual_sol y) \<bullet> primal_sol M = 0"
   and zero_slack_if_tight_matching_covers_non_zero_verts[matching_lp_theorems]:
    "non_zero_vertices V y \<subseteq> Vs M \<Longrightarrow>
               (incidence_matrix *\<^sub>v primal_sol M - 1\<^sub>v n) \<bullet> dual_sol y = 0"
    "non_zero_vertices V y \<subseteq> Vs M \<Longrightarrow> (1\<^sub>v n - incidence_matrix *\<^sub>v primal_sol M ) \<bullet> dual_sol y = 0"
proof-
  have a1: "dblton_graph G" "matching M"
    by(auto simp add: assms(2,1))
  have "(incidence_matrix\<^sup>T *\<^sub>v dual_sol y - weight_vect w) $ i = 0"
     if asm:"i <dim_vec (primal_sol M)" " primal_sol M $ i \<noteq> 0" for i
  proof-
    obtain e where e_prop:"e \<in> M" "G_enum_inv i = e"
      using asm by(simp add: primal_sol_def)
    then obtain u v where uv:"e = {u, v}" "u \<noteq> v"
      using a1(1) assms(1) by auto
    have uv_in_G: "u \<in> Vs G" "v \<in> Vs G" 
      using assms(1) e_prop(1,2) uv(1) by blast+
    have helpers: "Vs_enum u < n" "Vs_enum v < n" "Vs_enum_inv (Vs_enum u) = u"
                  "Vs_enum_inv (Vs_enum v) = v" "Vs_enum u \<noteq> Vs_enum v"
    using Vs_inv_enum[OF uv_in_G(1)] Vs_inv_enum[OF uv_in_G(2)]
          Vs_of_G_enum_less_n[OF uv_in_G(1)] Vs_of_G_enum_less_n[OF uv_in_G(2)] uv(2)
    by auto
    have indices_unfold:"{0..<n} \<inter> { i. Vs_enum_inv i \<in> e} = {Vs_enum u, Vs_enum v}"
      using uv by (auto simp add: helpers)
    have "(incidence_matrix\<^sup>T *\<^sub>v dual_sol y - weight_vect w) $ i = y u + y v - w e"
      using asm helpers(3,4,5)
      by (auto simp add:incidence_matrix_def dual_sol_def weight_vect_def mult_mat_vec_def
                scalar_prod_def e_prop(2) indices_unfold)
    thus ?thesis 
      using assms(3) e_prop(1) in_tight_subgraphD uv(1) by fastforce
  qed
  thus ths1: "(incidence_matrix\<^sup>T *\<^sub>v dual_sol y - weight_vect w) \<bullet> primal_sol M = 0"
   using sum.not_neutral_contains_not_neutral
    by(force simp add: scalar_prod_def)
  have "dual_sol y $ i = 0" 
    if asm: "i <dim_vec (dual_sol y)" "(incidence_matrix *\<^sub>v primal_sol M - 1\<^sub>v n) $ i\<noteq>0" 
            "non_zero_vertices V y \<subseteq> Vs M"for i
  proof-
    have "(incidence_matrix *\<^sub>v primal_sol M) $ i\<noteq>1" 
      using that(1,2) by force
    hence "(incidence_matrix *\<^sub>v primal_sol M) $ i = 0"
      using assms(1) matching_zero_one_entries that(1) by auto
    hence  "\<lbrakk>j < m; Vs_enum_inv i \<in> G_enum_inv j; G_enum_inv j \<in> M\<rbrakk> \<Longrightarrow> False" for j
      using asm(1)
      by(auto simp add: incidence_matrix_def primal_sol_def  mult_mat_vec_def scalar_prod_def)
    hence a2:"\<lbrakk>e \<in> M; Vs_enum_inv i \<in> e\<rbrakk> \<Longrightarrow> False" for e 
      using G_inv_enum assms(1)   G_enum_less_card_G[of e] 
      by fastforce
    have a3:"Vs_enum_inv i \<in> V"
      using Vs_enum_inv_in_G that(1) by auto
    have "y (Vs_enum_inv i) = 0"
      using asm(3) in_non_zero_verticesI[OF a3, of y] a2 
      by(auto elim!: vs_member_elim)
    thus ?thesis
      using  that(1) by (auto simp add: dual_sol_i_is)
  qed
  thus ths2:
    "non_zero_vertices V y \<subseteq> Vs M \<Longrightarrow>(incidence_matrix *\<^sub>v primal_sol M - 1\<^sub>v n) \<bullet> dual_sol y = 0"
    using sum.not_neutral_contains_not_neutral by (force simp add: scalar_prod_def )
  have dim_I_times_y:"incidence_matrix\<^sup>T *\<^sub>v dual_sol y \<in> carrier_vec m"
    by (simp add: carrier_dim_vec incidence_matrix_def)
  show "(weight_vect w - incidence_matrix\<^sup>T *\<^sub>v dual_sol y) \<bullet> primal_sol M = 0" 
    using ths1 
    by(simp add: 
      minus_scalar_prod_distrib[OF dim_I_times_y weight_vect_carrier_vec primal_sol_carrier_vec]
      minus_scalar_prod_distrib[OF weight_vect_carrier_vec dim_I_times_y primal_sol_carrier_vec])
  have dim_I_times_M: "incidence_matrix *\<^sub>v primal_sol M \<in> carrier_vec n"
    using mult_mat_vec_carrier by blast
  show "non_zero_vertices V y \<subseteq> Vs M \<Longrightarrow> (1\<^sub>v n - incidence_matrix *\<^sub>v primal_sol M) \<bullet> dual_sol y = 0"
    using ths2
    by(simp add:  minus_scalar_prod_distrib[OF dim_I_times_M _ dual_sol_carrier_vec]
          minus_scalar_prod_distrib[OF _  dim_I_times_M dual_sol_carrier_vec]) 
qed

corollary max_weight_if_tight_matching_covers_bads[matching_lp_theorems]:
  assumes "feasible_max_dual V G w y" "graph_matching G M"
          "graph_invar G" "M \<subseteq> tight_subgraph G w y"
          "non_zero_vertices V y \<subseteq> Vs M"
    shows "max_weight_matching G w M" "min_feasible_max_dual V G w y"
          "sum w M = sum y V"
  using assms dual_dot_y_vect_y_sum[of y, symmetric] 
        primal_dot_weight_vect_weight_sum[of M w, symmetric]
   by(auto intro!: general_complementary_slackness[OF incidence_matrix_carrier_mat]
                   max_matching_pd_optimality zero_slack_if_tight_matching
                   zero_slack_if_tight_matching_covers_non_zero_verts)

lemma primal_dot_One_card[matching_lp_theorems]: "M \<subseteq> G \<Longrightarrow> 1\<^sub>v m \<bullet> primal_sol M = card M" 
  using primal_dot_weight_vect_weight_sum[of M "\<lambda> e. 1"] by simp

lemma card_matching_bound_by_feasible_dual[matching_lp_theorems]:
  fixes y :: "real vec"
  assumes "M \<subseteq> G"
  assumes "matching M"
  assumes "incidence_matrix\<^sup>T *\<^sub>v y \<ge> 1\<^sub>v m"
  assumes "y \<ge> 0\<^sub>v n"
    shows "card M \<le> 1\<^sub>v n \<bullet> y"
  using max_weight_matching_bound_by_feasible_dual[OF conjI[OF assms(2,1)], of "\<lambda> e. 1"]
        assms(3,4)
  by simp

lemma max_card_matching_bound_by_feasible_dual[matching_lp_theorems]:
  fixes y :: "real vec"
  assumes "max_card_matching G M"
  assumes "incidence_matrix\<^sup>T *\<^sub>v y \<ge> 1\<^sub>v m"
  assumes "y \<ge> 0\<^sub>v n"
  shows "card M \<le> 1\<^sub>v n \<bullet> y"
  using assms
  by (auto intro: card_matching_bound_by_feasible_dual dest: max_card_matchingD)

lemma perfect_matching_feasible[matching_lp_theorems]:
  assumes "perfect_matching G M" "Vs G = V"
  shows "incidence_matrix *\<^sub>v primal_sol M = 1\<^sub>v n" 
proof-
  have p_m_unfolded: "M \<subseteq> G" "matching M" "Vs G = Vs M"
    using assms by (auto simp add: perfect_matchingD)
  have "incidence_matrix *\<^sub>v primal_sol M \<le> 1\<^sub>v n"
    by (simp add: matching_feasible p_m_unfolded(2))
  moreover hence "incidence_matrix *\<^sub>v primal_sol M < 1\<^sub>v n \<Longrightarrow> False"
    using matching_zero_one_entries[OF p_m_unfolded(2)]
  unfolding incidence_matrix_def less_vec_def mult_mat_vec_def scalar_prod_def
            weight_vect_def one_vec_def less_eq_vec_def
  proof(clarsimp, goal_cases)
    case (1 i)
    note one = this
    let ?indices = "{0..<m} \<inter> {ei. Vs_enum_inv i \<in> G_enum_inv ei}"
    have sum_zero:"sum (($) (primal_sol M)) ?indices = 0" 
      using 1 by auto
    have "\<not> (\<exists> e. e \<in> M \<and> Vs_enum_inv i \<in> e)"
    proof(rule ccontr, goal_cases)
      case 1
      then obtain e where e: "e \<in> M" "Vs_enum_inv i \<in> e"
        by auto
      then obtain ei where ei:"ei < m" "e = G_enum_inv ei"
        using p_m_unfolded(1)  G_enum_less_card_G[of e] G_inv_enum[of e] subset_iff by fast
      hence "sum (($) (primal_sol M)) ?indices > 0"
        using e primal_gtr_zero_iff[of ei M]
        by(auto intro!: ordered_comm_monoid_add_class.sum_pos2 simp add: primal_geq_zero)
      thus False
        using sum_zero by simp
    qed
    moreover have "Vs_enum_inv i \<in> Vs G" 
      using 1(2)Vs_enum_inv_in_G[of i] assms(2) one(3) by blast
    ultimately have "Vs G \<noteq> Vs M"
      by (auto elim!: vs_member_elim)
    thus False
      by (simp add: p_m_unfolded(3))
  qed
  ultimately show ?thesis by force
qed

lemma dual_sol_lp_feasible'[matching_lp_theorems]:
  assumes "feasible_min_perfect_dual G w y" "dblton_graph G"
  shows "incidence_matrix\<^sup>T *\<^sub>v dual_sol y \<le> weight_vect w"
  unfolding incidence_matrix_def dual_sol_def less_eq_vec_def mult_mat_vec_def scalar_prod_def
            weight_vect_def
proof (all \<open>intro conjI allI impI\<close>, simp_all, goal_cases)
  case (1 i)
  let ?indices = "{0..<n} \<inter> {ix. Vs_enum_inv ix \<in> G_enum_inv i}"
  have ei_in_G:"G_enum_inv i \<in> G" 
    using 1 by simp
  then obtain u v where uv:"G_enum_inv i = {u, v}" "u \<noteq> v" 
    using assms(2) by auto
  hence uv_inG: "u \<in> Vs G" "v \<in> Vs G" 
    using ei_in_G by auto
  obtain ui vi where ui_vi:"ui < n" "vi < n" "ui \<noteq> vi"
    "Vs_enum_inv ui = u" "Vs_enum_inv vi = v"  "Vs_enum_inv ui \<noteq> Vs_enum_inv vi"
    using Vs_inv_enum[OF uv_inG(1)] Vs_of_G_enum_less_n[OF uv_inG(1)]
          Vs_inv_enum[OF uv_inG(2)] Vs_of_G_enum_less_n[OF uv_inG(2)] uv(2)
    by fastforce
  have "w (G_enum_inv i) \<ge> y (Vs_enum_inv ui) + y (Vs_enum_inv vi)"
    using feasible_min_perfect_dualD[OF assms(1) ei_in_G uv(1)] ui_vi(4,5) by auto
  moreover have "{0..<n} \<inter> {ia . Vs_enum_inv ia \<in> G_enum_inv i} = { ui,  vi}" 
    using ui_vi uv Vs_enum_inv_inj_below_n by auto
  ultimately show ?case 
    using ui_vi(3) by simp
qed

lemma min_weight_perfect_matching_bound_by_feasible_dual[matching_lp_theorems]:
  fixes y :: "real vec"
  assumes "graph_matching G M" 
  assumes "y \<in> carrier_vec n"
  assumes "incidence_matrix\<^sup>T *\<^sub>v y \<le> weight_vect w"
  assumes "incidence_matrix *\<^sub>v primal_sol M = 1\<^sub>v n"
  shows "sum w M \<ge> 1\<^sub>v n \<bullet> y"
proof -
   have a1:"weight_vect w \<bullet> primal_sol M = sum w M"
    using assms(1) by (auto simp: primal_dot_weight_vect_weight_sum)
  moreover from assms have "\<dots> \<ge> 1\<^sub>v n \<bullet> y"
    unfolding a1[symmetric]
    by(auto intro!: weak_duality_theorem_primal_eq[OF incidence_matrix_carrier_mat]
                   perfect_matching_feasible)    
  ultimately show ?thesis by simp
qed

corollary min_perfect_matching_weak_duality[matching_lp_theorems]:
  assumes "feasible_min_perfect_dual G w y" "perfect_matching G M"
          "graph_invar G" "Vs G = V"
  shows   "sum w M \<ge> sum y (Vs G)"
proof-
  have G_props: "matching M" "M \<subseteq> G" " dblton_graph G" "graph_matching G M"
    using assms (2,3) by (auto simp add: perfect_matchingD)
  show ?thesis
  using dual_dot_y_vect_y_sum[of y] 
        min_weight_perfect_matching_bound_by_feasible_dual[OF G_props(4), of "dual_sol y" w]
        dual_sol_lp_feasible'[OF assms(1) G_props(3)] 
        perfect_matching_feasible[OF assms(2,4)] assms(4) dual_sol_carrier_vec
  by auto
qed

corollary min_perfect_matching_pd_optimality[matching_lp_theorems]:
  assumes "feasible_min_perfect_dual G w y" "perfect_matching G M"
          "Vs G = V"
          "graph_invar G"  "sum w M = sum y V"
    shows "min_weight_perfect_matching G w M" "max_feasible_min_perfect_dual G w y"
  using assms min_perfect_matching_weak_duality
  by(force intro!: min_weight_perfect_matchingI max_feasible_min_perfect_dualI)+

corollary min_weight_perfect_if_tight_perfect_matching[matching_lp_theorems]:
  assumes "feasible_min_perfect_dual G w y" "perfect_matching G M"
          "graph_invar G"  "Vs G = V" "M \<subseteq> tight_subgraph G w y"
     and finite_V: "finite V"
   shows "min_weight_perfect_matching G w M" "max_feasible_min_perfect_dual G w y"
         "sum w M = sum y V"
proof-
  have M_in_G:"M \<subseteq> G "
    by (simp add: assms(2) perfect_matchingD(1))
  show "min_weight_perfect_matching G w M" "max_feasible_min_perfect_dual G w y"
       "sum w M = sum y V"
    using M_in_G  assms(5)
    by(auto intro!:  min_perfect_matching_pd_optimality 
                    eq_primal_complementary_slackness[OF incidence_matrix_carrier_mat]
                    perfect_matching_feasible zero_slack_if_tight_matching(2)
            intro: assms 
          simp add: assms(4) assms(3) finite_V
                    primal_dot_weight_vect_weight_sum[OF M_in_G, of w, symmetric]
                    dual_dot_y_vect_y_sum[of y, symmetric] weight_vect_carrier_vec
                    primal_sol_carrier_vec dual_sol_carrier_vec assms(2)
                    perfect_matchingD(2)[OF assms(2)] )
qed
end

locale matching_LP_standard =
  fixes V::"'v set"
  fixes G::"'v set set"
  assumes V_and_G: "finite V" "Vs G \<subseteq> V"
begin

definition Vs_enum :: "'v \<Rightarrow> nat" where
  "Vs_enum = to_nat_on V"

definition Vs_enum_inv :: "nat \<Rightarrow> 'v" where
  "Vs_enum_inv= from_nat_into V"

definition G_enum :: "'v set \<Rightarrow> nat" where
  "G_enum \<equiv> to_nat_on G"

definition G_enum_inv :: "nat \<Rightarrow> 'v set" where
  "G_enum_inv \<equiv> from_nat_into G"

lemma finite_Vs_G: "finite (Vs G)" "finite G"
  using V_and_G(1,2) finite_subset 
  by (auto simp add: finite_Vs_then_finite finite_subset)

lemma bijections:"bij_betw Vs_enum V {0..<card V}"
                 "bij_betw G_enum G {0..<card G}"
  using to_nat_on_finite[OF  V_and_G(1)] to_nat_on_finite[OF finite_Vs_G(2)]
  by(auto simp add: Vs_enum_def G_enum_def  atLeast0LessThan)

lemma inversions: "x \<in> V \<Longrightarrow> Vs_enum_inv (Vs_enum x) = x"
                  "e \<in> G \<Longrightarrow> G_enum_inv (G_enum e) = e"
  by(auto simp add: V_and_G(1) Vs_enum_def Vs_enum_inv_def countable_finite
                     G_enum_def G_enum_inv_def finite_Vs_G(2))

interpretation lp: matching_lp_basic V G Vs_enum Vs_enum_inv G_enum G_enum_inv
  using V_and_G by(auto intro!: matching_lp_basic.intro bijections inversions)
thm lp.max_matching_weak_duality

lemmas max_matching_weak_duality= lp.max_matching_weak_duality
lemmas max_matching_pd_optimality= lp.max_matching_pd_optimality
lemmas max_weight_if_tight_matching_covers_bads=
          lp.max_weight_if_tight_matching_covers_bads
lemmas min_perfect_matching_weak_duality= lp.min_perfect_matching_weak_duality
lemmas min_perfect_matching_pd_optimality=lp.min_perfect_matching_pd_optimality
lemmas min_weight_perfect_if_tight_perfect_matching=
lp.min_weight_perfect_if_tight_perfect_matching[OF _ _ _ _ _ V_and_G(1)]
abbreviation "incidence_matrix == lp.incidence_matrix"
abbreviation "n == lp.n" 
abbreviation "m == lp.m"
abbreviation "primal_sol == lp.primal_sol"
lemmas matching_lp_theorems = lp.matching_lp_theorems
lemmas incidence_matrix_def = lp.incidence_matrix_def
lemmas dim_primal_sol= lp.dim_primal_sol
lemmas primal_sol_empty= lp.primal_sol_empty
lemmas primal_sol_nonneg= lp.primal_sol_nonneg
lemmas n_def = lp.n_def
lemma m_def: "m = card G" 
  by auto
end

lemma matching_lp_standard_intro:
 "finite V \<Longrightarrow> Vs E \<subseteq> V \<Longrightarrow>matching_LP_standard V E"
  by(auto intro!: matching_LP_standard.intro)

(*Obtain Lemmas on Graphs only*)

corollary max_matching_weak_duality:
  assumes "feasible_max_dual V E w y" "graph_matching E M"
          "graph_invar E"
  shows   "sum w M \<le> sum y V"
  using assms
  by(auto intro!: matching_LP_standard.max_matching_weak_duality[OF 
            matching_lp_standard_intro, simplified, OF _ _ assms]
       dest: feasible_max_dualD)

corollary max_matching_pd_optimality:
  assumes "feasible_max_dual V E w y" "graph_matching E M"
          "graph_invar E"  "sum w M = sum y V"
    shows "max_weight_matching E w M" "min_feasible_max_dual V E w y"
  using assms
  by(auto intro!: matching_LP_standard.max_matching_pd_optimality[OF 
           matching_lp_standard_intro, simplified, OF _ _ assms]
       dest: feasible_max_dualD)

corollary max_weight_if_tight_matching_covers_bads:
  assumes "feasible_max_dual V E w y" "graph_matching E M"
          "graph_invar E" "M \<subseteq> tight_subgraph E w y"
          "non_zero_vertices V y \<subseteq> Vs M"
    shows "max_weight_matching E w M" "min_feasible_max_dual V E w y"
          "sum w M = sum y V"
  using assms
  by(auto intro!: matching_LP_standard.max_weight_if_tight_matching_covers_bads[OF 
             matching_lp_standard_intro, simplified, OF _ _ assms]
       dest: feasible_max_dualD)

lemma min_perfect_matching_weak_duality:
  assumes "feasible_min_perfect_dual E w y" "perfect_matching E M"
          "graph_invar E"                                  
  shows   "sum w M \<ge> sum y (Vs E)"
 by(auto intro!: matching_LP_standard.min_perfect_matching_weak_duality[OF 
             matching_lp_standard_intro, of "Vs E", simplified, OF _ _ assms]
       simp add: assms(3))

corollary min_perfect_matching_pd_optimality:
  assumes "feasible_min_perfect_dual E w y" "perfect_matching E M"
          "graph_invar E"  "sum w M = sum y (Vs E)"
    shows "min_weight_perfect_matching E w M" "max_feasible_min_perfect_dual E w y"
  using assms
  by(auto intro!: matching_LP_standard.min_perfect_matching_pd_optimality[OF 
            matching_lp_standard_intro, of "Vs E", simplified, OF _ _ assms(1,2)])

corollary min_weight_perfect_if_tight:
  assumes "feasible_min_perfect_dual E w y" "perfect_matching E M"
          "graph_invar E"  "M \<subseteq> tight_subgraph E w y"
    shows "min_weight_perfect_matching E w M" "max_feasible_min_perfect_dual E w y"
          "sum w M = sum y (Vs E)"
  using assms
  by(auto intro!: matching_LP_standard.min_weight_perfect_if_tight_perfect_matching[OF 
            matching_lp_standard_intro]
       dest: feasible_max_dualD)
end