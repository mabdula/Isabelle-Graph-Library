theory Faces
  imports  
    Linear_Inequalities.Decomposition_Theorem 
    Linear_Inequalities.Missing_Matrix
    LP_Duality.LP_Duality
    Jordan_Normal_Form.Matrix
    Jordan_Normal_Form.DL_Rank_Submatrix
    Subsystems
    Matching_LP
begin 
(*

definition undef_vec :: "nat \<Rightarrow> 'a" where
  "undef_vec i \<equiv> [] ! i"

definition mk_vec :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "mk_vec n f \<equiv> \<lambda> i. if i < n then f i else undef_vec (i - n)"

typedef 'a vec = "{(n, mk_vec n f) | n f :: nat \<Rightarrow> 'a. True}"
  by auto

definition mk_mat :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<Rightarrow> 'a) \<Rightarrow> (nat \<times> nat \<Rightarrow> 'a)" where
  "mk_mat nr nc f \<equiv> \<lambda> (i,j). if i < nr \<and> j < nc then f (i,j) else undef_mat nr nc f (i,j)"

lemma cong_mk_mat: assumes "\<And> i j. i < nr \<Longrightarrow> j < nc \<Longrightarrow> f (i,j) = f' (i,j)"
  shows "mk_mat nr nc f = mk_mat nr nc f'"
  using undef_cong_mat[of nr nc f f', OF assms]
  using assms unfolding mk_mat_def
  by auto

typedef 'a mat = "{(nr, nc, mk_mat nr nc f) | nr nc f :: nat \<times> nat \<Rightarrow> 'a. True}"
  by auto
*)(*
definition
  one_vec :: "nat \<Rightarrow> 'a :: one vec" ("1\<^sub>v")
  where "1\<^sub>v n = vec n (\<lambda> i. 1)"
*)
lemma one_carrier_vec[simp]: "1\<^sub>v n \<in> carrier_vec n"
  unfolding one_vec_def carrier_vec_def by auto

lemma index_one_vec[simp]: "i < n \<Longrightarrow> 1\<^sub>v n $ i = 1" "dim_vec (1\<^sub>v n) = n"
  unfolding one_vec_def by auto

lemma vec_of_dim_1[simp]: "dim_vec v = 0 \<longleftrightarrow> v = 1\<^sub>v 0" by auto

lemma scalar_prod_left_one[simp]:
  "(v :: 'a :: semiring_1 vec) \<in> carrier_vec n \<Longrightarrow> 1\<^sub>v n \<bullet> v = sum (\<lambda> i. v $ i) {0..<n}"
  unfolding scalar_prod_def 
  by auto

lemma scalar_prod_right_one[simp]: 
  "(v :: 'a :: semiring_1 vec) \<in> carrier_vec n \<Longrightarrow> v \<bullet> 1\<^sub>v n = sum (\<lambda> i. v $ i) {0..<n}"
  unfolding scalar_prod_def
  by auto

context gram_schmidt
begin

definition support_hyp where
  "support_hyp P \<alpha> \<beta> =( (\<beta> = Maximum { \<alpha> \<bullet> x | x. x \<in> P}) 
                        \<and> has_Maximum { \<alpha> \<bullet> x | x. x \<in> P} 
                        \<and> \<alpha> \<in> carrier_vec n)"

definition valid_ineq where
  "valid_ineq P \<alpha> \<beta> =( (\<forall>x \<in> P. \<alpha> \<bullet> x \<le> \<beta>) \<and> \<alpha> \<in> carrier_vec n)" 

lemma suport_hypE:
  "support_hyp P \<alpha> \<beta> \<Longrightarrow>
   (\<lbrakk>\<beta> = Maximum { \<alpha> \<bullet> x | x. x \<in> P};
   has_Maximum { \<alpha> \<bullet> x | x. x \<in> P};
   \<alpha> \<in> carrier_vec n\<rbrakk> \<Longrightarrow> R)
   \<Longrightarrow> R"
  by(auto simp: support_hyp_def)

lemma support_hypI[intro]:
  assumes "has_Maximum { \<alpha> \<bullet> x | x. x \<in> P}"
  assumes "\<beta> = Maximum { \<alpha> \<bullet> x | x. x \<in> P}"
  assumes "\<alpha> \<in> carrier_vec n" 
  shows "support_hyp P \<alpha> \<beta>" 
  unfolding support_hyp_def
  using assms 
  by auto

lemma valid_ineqE[elim]:
"valid_ineq P \<alpha> \<beta> \<Longrightarrow>
   (\<lbrakk>\<forall>x \<in> P. \<alpha> \<bullet> x \<le> \<beta>;
   \<alpha> \<in> carrier_vec n\<rbrakk> \<Longrightarrow> R)
   \<Longrightarrow> R"
  unfolding valid_ineq_def
  by auto

lemma valid_ineq_intro[intro]:
  assumes "\<forall>x \<in> P. \<alpha> \<bullet> x \<le> \<beta>"
  assumes "\<alpha> \<in> carrier_vec n" 
  shows "valid_ineq P \<alpha> \<beta>"
  unfolding valid_ineq_def
  using assms
  by auto

lemma exists_greater_if_not_Maximum:
  assumes "a \<in> A"
  assumes "a \<noteq> Maximum A"
  shows "\<exists> m \<in> A. m > a"
  using assms 
proof -
  show ?thesis
  proof (rule ccontr)
    assume nex: "\<not> (\<exists>m\<in>A. m > a)"
    have le: "y \<le> a" if "y \<in> A" for y
    proof (rule leI)
      show "\<not> a < y" using nex that by blast
    qed
    have "Maximum A = a"
      by (rule eqMaximumI[OF assms(1) le])
    with assms(2) show False by simp
  qed
qed

lemma valid_ineq_non_empty_is_support:
  assumes "valid_ineq P \<alpha> \<beta>"
  assumes "{x. \<alpha> \<bullet> x = \<beta>} \<inter> P \<noteq> {}"
  shows "support_hyp P \<alpha> \<beta>"
proof
  obtain x where "x \<in> P \<and> \<alpha> \<bullet> x = \<beta>" using assms(2) 
    by blast
  then have " \<beta> \<in> {\<alpha> \<bullet> x |x. x \<in> P}"
    by auto
 show "\<beta> = Maximum {\<alpha> \<bullet> x |x. x \<in> P}" 
 using assms(1)
  apply(elim valid_ineqE)
  using eqMaximumI[of \<beta> "{\<alpha> \<bullet> x |x. x \<in> P}"] mem_Collect_eq `\<beta> \<in> {\<alpha> \<bullet> x |x. x \<in> P}`
  by blast
  show "has_Maximum {\<alpha> \<bullet> x |x. x \<in> P}"
    using assms(1)
    apply(elim valid_ineqE)
    using \<open>\<beta> \<in> {\<alpha> \<bullet> x |x. x \<in> P}\<close> has_Maximum_def by auto
  show "\<alpha> \<in> carrier_vec n" 
    using assms(1) valid_ineqE by blast
qed

lemma support_hyp_is_valid:
  assumes "support_hyp P \<alpha> \<beta>"
  shows  "valid_ineq P \<alpha> \<beta>" (is ?g1)
     and "{x. \<alpha> \<bullet> x = \<beta>} \<inter> P \<noteq> {}" (is ?g2)
proof-
  have \<beta>_max: "\<beta> = Maximum {\<alpha> \<bullet> x |x. x \<in> P}" "has_Maximum {\<alpha> \<bullet> x |x. x \<in> P}" 
    using assms suport_hypE by blast+
  then show ?g1
    using \<open>support_hyp P \<alpha> \<beta>\<close>
    by (auto elim: suport_hypE dest: has_MaximumD(2))
  have "\<beta> \<in> {\<alpha> \<bullet> x |x. x \<in> P}" 
    using \<beta>_max has_MaximumD(1) by blast
  then show "{x. \<alpha> \<bullet> x = \<beta>} \<inter> P \<noteq> {}" 
    by blast
qed

definition face :: "'a vec set \<Rightarrow> 'a vec set \<Rightarrow> bool" where
  "face P F = ( P \<noteq> {} \<and> (\<exists> \<alpha> \<beta>. F = P \<inter> {x |x. \<alpha> \<bullet> x = \<beta>} \<and> support_hyp P \<alpha> \<beta> ))"

lemma faceE[elim]:
"face P F \<Longrightarrow>
   (\<lbrakk>P \<noteq> {};
   (\<exists> \<alpha> \<beta>. F = P \<inter> {x |x. \<alpha> \<bullet> x = \<beta>} \<and> support_hyp P \<alpha> \<beta> )\<rbrakk> \<Longrightarrow> R)
   \<Longrightarrow> R"
 unfolding face_def by auto

lemma faceI[intro]:
  assumes "P \<noteq> {}"  
  assumes "F = P \<inter> {x |x. \<alpha> \<bullet> x = \<beta>}"
  assumes "support_hyp P \<alpha> \<beta>" 
  shows "face P F" 
  unfolding face_def
  using assms 
  by auto

lemma faceE':
"face P F \<Longrightarrow>
   (\<lbrakk>(\<exists> \<alpha> \<beta>. F = P \<inter> {x |x. \<alpha> \<bullet> x = \<beta>} \<and> valid_ineq P \<alpha> \<beta> \<and> F \<noteq> {})\<rbrakk> \<Longrightarrow> R)
   \<Longrightarrow> R"
  proof -
    assume face: "face P F"
    assume ih: "(\<exists> \<alpha> \<beta>. F = P \<inter> {x |x. \<alpha> \<bullet> x = \<beta>} \<and> valid_ineq P \<alpha> \<beta> \<and> F \<noteq> {}) \<Longrightarrow> R"
    from face obtain a c
      where F_eq: "F = P \<inter> {x |x. a \<bullet> x = c}"
        and sh: "support_hyp P a c"
      by (auto simp: face_def)
    have valid: "valid_ineq P a c"
      by (rule support_hyp_is_valid(1)[OF sh])
    have "{x. a \<bullet> x = c} \<inter> P \<noteq> {}"
      by (rule support_hyp_is_valid(2)[OF sh])
    then obtain z where z_eq: "a \<bullet> z = c" and z_P: "z \<in> P"
      by blast
    have "z \<in> F"
      using F_eq z_eq z_P by blast
    then have F_ne: "F \<noteq> {}"
      by blast
    have "\<exists> \<alpha> \<beta>. F = P \<inter> {x |x. \<alpha> \<bullet> x = \<beta>} \<and> valid_ineq P \<alpha> \<beta> \<and> F \<noteq> {}"
      using F_eq valid F_ne by blast
    then show R
      by (rule ih)
  qed

lemma face_intro'[intro]:
  assumes "valid_ineq P \<alpha> \<beta>"
  assumes "F = P \<inter> {x |x. \<alpha> \<bullet> x = \<beta>}"
  assumes "F \<noteq> {}"
  shows "face P F"
  unfolding face_def
  using valid_ineq_non_empty_is_support[of P \<alpha> \<beta>] assms
  by blast

lemma face_non_empty:
  assumes "face P F"
  shows "F \<noteq> {}" 
  using faceE'  
  using assms by blast

lemma face_subset_polyhedron:
  assumes "face P F"
  shows "F \<subseteq> P"
  using assms unfolding face_def 
  by auto

lemma face_is_Max':
  assumes "{x. \<alpha> \<bullet> x = \<beta>  \<and> x \<in> P} \<noteq> {}"
  assumes "valid_ineq P \<alpha> \<beta>"
  shows "\<beta> =  Maximum {\<alpha> \<bullet> x | x. x \<in> P}" (is "\<beta> = Maximum ?Ineq")
  and "has_Maximum {\<alpha> \<bullet> x | x. x \<in> P}"  (is "has_Maximum ?Ineq")
proof - 
  have "\<beta> \<in> {\<alpha> \<bullet> x | x. x \<in> P}" using assms(1)  by auto
  then show "\<beta> = Maximum ?Ineq" 
    proof (rule eqMaximumI[symmetric] eqMaximumI)
      fix y assume "y \<in> {\<alpha> \<bullet> x |x. x \<in> P}"
      then obtain z where z: "z \<in> P" "y = \<alpha> \<bullet> z"
        by blast
      have "\<forall>x \<in> P. \<alpha> \<bullet> x \<le> \<beta>"
        using assms by (auto simp: valid_ineq_def)
      then show "y \<le> \<beta>"
        using z by simp
    qed
  show "has_Maximum ?Ineq"
    unfolding has_Maximum_def
    using assms(2) \<open>\<beta> \<in> {\<alpha> \<bullet> x |x. x \<in> P}\<close>
    by(auto simp: valid_ineqE)
qed

lemma face_primal_bounded:
  fixes A b
  defines "P \<equiv> polyhedron A b"
  assumes "valid_ineq P \<alpha> \<beta>"
  shows "\<forall> x \<in> carrier_vec n. A *\<^sub>v x \<le> b \<longrightarrow> \<alpha> \<bullet> x \<le> \<beta>"
  using assms
  unfolding polyhedron_def valid_ineq_def
  by simp

lemma valid_ineq_dual:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "valid_ineq P \<alpha> \<beta>"
  assumes "P \<noteq> {}" 
  shows "Maximum {\<alpha> \<bullet> x | x. x \<in> P} = Minimum {b \<bullet> y | y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = \<alpha>}"
    and "has_Maximum {\<alpha> \<bullet> x | x. x \<in> P}" 
    and "has_Minimum {b \<bullet> y | y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = \<alpha>}" 
proof -
  have "\<alpha> \<in> carrier_vec n"  
    using assms(4) valid_ineqE by blast
  have sat: "\<exists> x \<in> carrier_vec n. A *\<^sub>v x \<le> b" 
    using assms(3) assms(5) unfolding polyhedron_def by auto
  have bounded: "\<forall> x \<in> carrier_vec n. A *\<^sub>v x \<le> b \<longrightarrow> \<alpha> \<bullet> x \<le> \<beta>" 
    using P_def assms(4) face_primal_bounded by blast
  show "Maximum {\<alpha> \<bullet> x | x. x \<in> P} = Minimum {b \<bullet> y | y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = \<alpha>}"
    "has_Maximum {\<alpha> \<bullet> x | x. x \<in> P}" "has_Minimum {b \<bullet> y | y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = \<alpha>}"
    using strong_duality_theorem_primal_sat_bounded_min_max[of A nr n b \<alpha> \<beta>]
    using A \<open>\<alpha> \<in> carrier_vec n\<close> b bounded sat 
    by (auto simp: P_def polyhedron_def)
qed

lemma valid_ineq_dual_min:
 fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
 assumes A: "A \<in> carrier_mat nr n"
 assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "valid_ineq P \<alpha> \<beta>"
  assumes "{x. \<alpha> \<bullet> x = \<beta> \<and> x \<in> P} \<noteq> {}" 
  shows "\<beta> = Minimum {b \<bullet> y | y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = \<alpha>}"
    and "has_Minimum {b \<bullet> y | y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = \<alpha>}"
proof -
  have "P \<noteq> {}" using assms(5) by blast 
  show "has_Minimum {b \<bullet> y | y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = \<alpha>}" 
  using valid_ineq_dual(3)[of A nr b \<alpha> \<beta>] `P \<noteq> {}` 
    using A P_def assms(4) b by fastforce
  show "\<beta> = Minimum {b \<bullet> y | y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = \<alpha>}"
     using valid_ineq_dual(1)[of A nr b \<alpha> \<beta>] face_is_Max'(1)[of \<alpha> \<beta> P]
     using A P_def \<open>P \<noteq> {}\<close>  assms(4) assms(5) b by fastforce
 qed

lemma if_sum_0_then_all_0:
  fixes f :: "nat \<Rightarrow> 'a :: trivial_conjugatable_linordered_field"
  assumes "(\<Sum>i = 0..<nr. f i) = 0"
  assumes "\<forall> i < nr. f i \<ge> 0"
  shows "(\<Sum>i = 0..<nr. f i) = 0 \<longleftrightarrow> (\<forall> i < nr. f i = 0)" 
proof -
  have zero: "f i = 0" if i: "i < nr" for i
  proof -
    have fin: "finite {0..<nr}" by simp
    have mem: "i \<in> {0..<nr}" using i by simp
    have split: "(\<Sum>j = 0..<nr. f j) = f i + (\<Sum>j \<in> {0..<nr} - {i}. f j)"
      by (rule sum.remove[OF fin mem])
    have rest: "0 \<le> (\<Sum>j \<in> {0..<nr} - {i}. f j)"
      using assms(2) by (intro sum_nonneg) auto
    have fi: "0 \<le> f i"
      using assms(2) i by blast
    have "f i + (\<Sum>j \<in> {0..<nr} - {i}. f j) = 0"
      unfolding split[symmetric] by (rule assms(1))
    then show "f i = 0"
      using add_nonneg_eq_0_iff[OF fi rest] by simp
  qed
  show ?thesis
  proof
    assume "(\<Sum>i = 0..<nr. f i) = 0"
    show "\<forall>i<nr. f i = 0"
      using zero by blast
  next
    assume "\<forall>i<nr. f i = 0"
    show "(\<Sum>i = 0..<nr. f i) = 0"
      by (rule assms(1))
  qed
qed

lemma eq_vec_zero_diff_in_mult:
  fixes a :: "'a :: trivial_conjugatable_linordered_field vec"
  assumes "a \<in> carrier_vec nr"
  assumes "b \<in> carrier_vec nr"
  assumes "y \<in> carrier_vec nr"
  assumes "a \<le> b" 
  assumes "y \<ge> 0\<^sub>v nr" 
  shows "y \<bullet> a = y \<bullet> b \<longleftrightarrow> (\<forall> i < nr. y $ i * (b - a) $ i = 0)" 
proof -
  have ge0:"\<forall> i < nr. y $ i * (b - a) $ i \<ge> 0" 
    proof (intro allI impI)
      fix i :: nat
      assume i: "i < nr"
      have dim_a: "dim_vec a = nr" using assms(1) by auto
      have dim_b: "dim_vec b = nr" using assms(2) by auto
      have dim_y: "dim_vec y = nr" using assms(3) by auto
      have "0\<^sub>v nr $ i \<le> y $ i"
        using assms(5) dim_y i by (simp add: less_eq_vec_def)
      hence y_nonneg: "0 \<le> y $ i"
        using i by simp
      have "a $ i \<le> b $ i"
        using assms(4) dim_b i by (simp add: less_eq_vec_def)
      hence "0 \<le> b $ i - a $ i" by simp
      moreover have "(b - a) $ i = b $ i - a $ i"
        using i dim_a dim_b by simp
      ultimately have diff_nonneg: "0 \<le> (b - a) $ i" by simp
      show "y $ i * (b - a) $ i \<ge> 0"
        by (rule mult_nonneg_nonneg[OF y_nonneg diff_nonneg])
    qed
  have "y \<bullet> a = y \<bullet> b \<longleftrightarrow> y \<bullet> b - y \<bullet> a  = 0" using assms(5)  by auto
  also have "\<dots> \<longleftrightarrow> y \<bullet> (b - a) = 0" 
  proof -
    have "y \<bullet> (b - a) = y \<bullet> b - y \<bullet> a"
      by (rule scalar_prod_minus_distrib[OF assms(3) assms(2) assms(1)])
    thus ?thesis
      by simp
  qed
  also have "\<dots> \<longleftrightarrow> (\<Sum>i = 0..<nr. y $ i * (b - a) $ i) = 0"
    unfolding scalar_prod_def 
    using assms(1)  by auto
  also have "\<dots> \<longleftrightarrow> (\<forall> i < nr. y $ i * (b - a) $ i = 0)" 
    by (meson ge0 atLeastLessThan_iff finsum_zero' if_sum_0_then_all_0)
  finally show ?thesis by auto
qed

lemma complementary_slackness:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  assumes "y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = \<alpha> \<and> b \<bullet> y = \<beta>" 
  assumes "x \<in> polyhedron A b" 
  shows "\<alpha> \<bullet> x = \<beta> \<longleftrightarrow> (\<forall> i < nr. y $ i = 0 \<or> (row A i) \<bullet> x = b $ i)"
proof -
  have "dim_row A = nr" using A by auto
  have "y \<in> carrier_vec nr" 
  proof -
    have y_ge: "0\<^sub>v nr \<le> y"
      using assms(3) by blast
    have "dim_vec y = dim_vec (0\<^sub>v nr)"
      using y_ge by (simp add: less_eq_vec_def)
    then have "dim_vec y = nr"
      by simp
    then show "y \<in> carrier_vec nr"
      by (rule carrier_dim_vec[THEN iffD2])
  qed
  then  have "(A\<^sup>T *\<^sub>v y) \<bullet> x = y \<bullet> (A *\<^sub>v x)" 
    using transpose_vec_mult_scalar[of A nr n x y] assms(1) assms(3) 
    using assms(4) gram_schmidt.polyhedron_def by blast
  then have " \<alpha> \<bullet> x = \<beta>  \<longleftrightarrow> y \<bullet> (A *\<^sub>v x) = y \<bullet> b" 
  proof -
    note y_carr = \<open>y \<in> carrier_vec nr\<close>
    have x_carr: "x \<in> carrier_vec n"
      using assms(4) unfolding polyhedron_def by blast
    have alpha_eq: "A\<^sup>T *\<^sub>v y = \<alpha>" and beta_eq: "b \<bullet> y = \<beta>"
      using assms(3) by blast+
    have trans: "(A\<^sup>T *\<^sub>v y) \<bullet> x = y \<bullet> (A *\<^sub>v x)"
      using transpose_vec_mult_scalar[of A nr n x y] A x_carr y_carr by blast
    have lhs: "\<alpha> \<bullet> x = y \<bullet> (A *\<^sub>v x)"
      using trans alpha_eq by simp
    have rhs: "\<beta> = y \<bullet> b"
      using beta_eq comm_scalar_prod[OF b y_carr] by simp
    show ?thesis
      using lhs rhs by simp
  qed
  also have "\<dots> \<longleftrightarrow> (\<forall> i < nr. y $ i * (b - A *\<^sub>v x) $ i = 0)"
    using eq_vec_zero_diff_in_mult[of "A *\<^sub>v x" nr b y]  
    using A \<open>y \<in> carrier_vec nr\<close> assms(3) assms(4) b mult_mat_vec_carrier 
    by (simp add: gram_schmidt.polyhedron_def)
  also have "\<dots> \<longleftrightarrow>  (\<forall> i < nr. y $ i = 0 \<or> (row A i) \<bullet> x = b $ i)" 
    unfolding mult_mat_vec_def 
    using \<open>dim_row A = nr\<close> by auto
  finally show ?thesis 
    by blast
qed

lemma complementary_slackness_subsystem:
 fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  assumes "y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = \<alpha> \<and> b \<bullet> y = \<beta>"
  assumes "x \<in> polyhedron A b" 
  shows "\<alpha> \<bullet> x = \<beta> \<longleftrightarrow> 
  fst (sub_system A b {i. y $ i > 0 \<and> i < nr}) *\<^sub>v x = snd (sub_system A b {i. y $ i > 0 \<and> i < nr})"
   (is "\<alpha> \<bullet> x = \<beta> \<longleftrightarrow> ?A' *\<^sub>v x = ?b'")
proof -
   have "\<alpha> \<bullet> x = \<beta> \<longleftrightarrow> (\<forall> i < nr. y $ i = 0 \<or> (row A i) \<bullet> x = b $ i)" 
    using assms complementary_slackness by blast
  also have "\<dots> \<longleftrightarrow>
    (\<forall>i \<in> {i. y $ i > 0 \<and> i < nr} \<inter> {0..<dim_row A}. (row A i) \<bullet> x = b $ i)" 
  proof -
    have dimA: "dim_row A = nr"
      using A by simp
    have y0: "(0\<^sub>v nr) $ i \<le> y $ i" if "i < nr" for i
      using assms(3) that unfolding less_eq_vec_def by auto
    have y_nonneg: "0 \<le> y $ i" if "i < nr" for i
      using y0[OF that] that by simp
    show ?thesis
    proof (rule iffI)
      assume lhs: "\<forall>i<nr. y $ i = 0 \<or> row A i \<bullet> x = b $ i"
      show "\<forall>i\<in>{i. y $ i > 0 \<and> i < nr} \<inter> {0..<dim_row A}. row A i \<bullet> x = b $ i"
      proof (rule ballI)
        fix i
        assume "i \<in> {i. y $ i > 0 \<and> i < nr} \<inter> {0..<dim_row A}"
        then have i_pos: "0 < y $ i" and i_lt: "i < nr"
          by auto
        have "y $ i = 0 \<or> row A i \<bullet> x = b $ i"
          using lhs i_lt by blast
        then show "row A i \<bullet> x = b $ i"
          using i_pos by auto
      qed
    next
      assume rhs: "\<forall>i\<in>{i. y $ i > 0 \<and> i < nr} \<inter> {0..<dim_row A}. row A i \<bullet> x = b $ i"
      show "\<forall>i<nr. y $ i = 0 \<or> row A i \<bullet> x = b $ i"
      proof (intro allI impI)
        fix i
        assume i_lt: "i < nr"
        show "y $ i = 0 \<or> row A i \<bullet> x = b $ i"
        proof (cases "y $ i = 0")
          case True
          then show ?thesis by blast
        next
          case False
          have "0 < y $ i \<or> 0 = y $ i"
            using y_nonneg[OF i_lt] by (rule order_le_imp_less_or_eq)
          then have i_pos: "0 < y $ i"
            using False by auto
          have "i \<in> {i. y $ i > 0 \<and> i < nr} \<inter> {0..<dim_row A}"
            using i_pos i_lt dimA by simp
          then have "row A i \<bullet> x = b $ i"
            using rhs by blast
          then show ?thesis by blast
        qed
      qed
    qed
  qed
  also have "\<dots> \<longleftrightarrow> (\<forall> i < dim_row ?A'. (row ?A' i) \<bullet> x = ?b' $ i)"
  proof -
    let ?I = "{i. y $ i > 0 \<and> i < nr}"
    have dims: "dim_row A = dim_vec b"
      using carrier_matD(1)[OF A] carrier_vecD[OF b] by simp
    have sub: "(?A', ?b') = sub_system A b ?I"
      by simp
    show ?thesis
    proof
      assume "\<forall>i\<in>?I \<inter> {0..<dim_row A}. row A i \<bullet> x = b $ i"
      then show "\<forall>i<dim_row ?A'. row ?A' i \<bullet> x = ?b' $ i"
        using subsystem_fulfills_P'[of A b ?A' ?b' ?I "\<lambda>a c. a \<bullet> x = c"] dims sub A b
        by blast
    next
      assume "\<forall>i<dim_row ?A'. row ?A' i \<bullet> x = ?b' $ i"
      then show "\<forall>i\<in>?I \<inter> {0..<dim_row A}. row A i \<bullet> x = b $ i"
        using subsystem_fulfills_P[of A b ?A' ?b' ?I "\<lambda>a c. a \<bullet> x = c"] dims sub A b
        by blast
    qed
  qed
  also have "(\<forall> i < dim_row ?A'. (row ?A' i) \<bullet> x = ?b' $ i) \<longleftrightarrow> ?A' *\<^sub>v x = ?b'" 
  proof -
    have dimAb: "dim_row A = dim_vec b"
      using A b by auto
    have dims: "dim_row ?A' = dim_vec ?b'"
      using dims_subsyst_same'[OF dimAb] by simp
    show ?thesis
    proof
      assume asm: "\<forall> i < dim_row ?A'. (row ?A' i) \<bullet> x = ?b' $ i"
      show "?A' *\<^sub>v x = ?b'"
      proof (rule eq_vecI)
        fix i
        assume "i < dim_vec ?b'"
        then have i: "i < dim_row ?A'"
          using dims by simp
        have "(?A' *\<^sub>v x) $ i = row ?A' i \<bullet> x"
          by (rule index_mult_mat_vec[OF i])
        also have "\<dots> = ?b' $ i"
          using asm i by blast
        finally show "(?A' *\<^sub>v x) $ i = ?b' $ i" .
      next
        show "dim_vec (?A' *\<^sub>v x) = dim_vec ?b'"
          using dims by simp
      qed
    next
      assume eq: "?A' *\<^sub>v x = ?b'"
      show "\<forall> i < dim_row ?A'. (row ?A' i) \<bullet> x = ?b' $ i"
      proof (intro allI impI)
        fix i
        assume i: "i < dim_row ?A'"
        have "row ?A' i \<bullet> x = (?A' *\<^sub>v x) $ i"
          by (rule index_mult_mat_vec[OF i, symmetric])
        also have "\<dots> = ?b' $ i"
          by (simp only: eq)
        finally show "row ?A' i \<bullet> x = ?b' $ i" .
      qed
    qed
  qed
  finally show ?thesis 
    by blast
qed

lemma char_face1:
 fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
 assumes A: "A \<in> carrier_mat nr n"
 assumes b: "b \<in> carrier_vec nr"
 defines "P \<equiv> polyhedron A b"
 assumes "face P F"
 obtains A' b' I where "((A', b') = sub_system A b I)" "F = {x. A' *\<^sub>v x = b' \<and> x \<in> P}"
proof -
  obtain \<alpha> \<beta> where face:" F = P \<inter> {x |x. \<alpha> \<bullet> x = \<beta>} \<and> valid_ineq P \<alpha> \<beta> \<and> F \<noteq> {}" 
    using assms(4)
    apply (elim faceE') 
  by presburger
  then have "{x. \<alpha> \<bullet> x = \<beta> \<and> x \<in> polyhedron A b} \<noteq> {}" 
    using P_def face by fastforce
  then obtain y' where y': "y' \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y' = \<alpha> \<and> b \<bullet> y' = \<beta>" 
    using valid_ineq_dual_min[of A nr b \<alpha> \<beta>]  
  proof -
  have vi: "valid_ineq (polyhedron A b) \<alpha> \<beta>"
    using face by (simp add: P_def)
  from face have "F \<noteq> {}" by auto
  then obtain z where z: "z \<in> F" by blast
  have z_P: "z \<in> P" and z_eq: "\<alpha> \<bullet> z = \<beta>"
    using face z by auto
  have "z \<in> {x. \<alpha> \<bullet> x = \<beta> \<and> x \<in> polyhedron A b}"
    using z_P z_eq by (simp add: P_def)
  then have ne: "{x. \<alpha> \<bullet> x = \<beta> \<and> x \<in> polyhedron A b} \<noteq> {}"
    by blast
  have hasmin: "has_Minimum {b \<bullet> y | y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = \<alpha>}"
    using valid_ineq_dual_min(2)[of A nr b \<alpha> \<beta>] A b vi ne by blast
  have beta: "\<beta> = Minimum {b \<bullet> y | y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = \<alpha>}"
    using valid_ineq_dual_min(1)[of A nr b \<alpha> \<beta>] A b vi ne by blast
  have "\<beta> \<in> {b \<bullet> y | y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = \<alpha>}"
    using has_MinimumD(1)[OF hasmin] beta by simp
  then obtain y where y: "\<beta> = b \<bullet> y" "y \<ge> 0\<^sub>v nr" "A\<^sup>T *\<^sub>v y = \<alpha>"
    by blast
  show thesis
  proof (rule that)
    show "y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = \<alpha> \<and> b \<bullet> y = \<beta>"
      using y by simp
  qed
  qed
  let ?A' = "fst (sub_system A b {i. y' $ i > 0 \<and> i < nr})" 
  let ?b' = "snd (sub_system A b {i. y' $ i > 0 \<and> i < nr})"
  have "{x. \<alpha> \<bullet> x = \<beta> \<and> x \<in> P} = {x. ?A' *\<^sub>v x = ?b' \<and> x \<in> P}"
    unfolding P_def using complementary_slackness_subsystem A y' b by blast 
  moreover have "((?A', ?b') = sub_system A b {i. 0 < y' $ i \<and> i < nr})" 
    by simp
  ultimately show ?thesis 
    using face that by blast
qed

lemma subsyst_valid:
 assumes "x \<in> polyhedron A b" 
 shows "fst (sub_system A b I) *\<^sub>v x \<le> snd (sub_system A b I)" 
  using assms 
  unfolding polyhedron_def 
proof -
  let ?A' = "fst (sub_system A b I)"
  let ?b' = "snd (sub_system A b I)"
  have sub_eq: "(?A', ?b') = sub_system A b I" by simp
  have Ax: "A *\<^sub>v x \<le> b"
    using assms by (auto simp: polyhedron_def)
  have dim_Ab: "dim_row A = dim_vec b"
    using Ax by (auto simp: less_eq_vec_def)
  have Ax_idx: "(A *\<^sub>v x) $ k \<le> b $ k" if "k < dim_vec b" for k
    using Ax that by (auto simp: less_eq_vec_def)
  have dims': "dim_row ?A' = dim_vec ?b'"
    using dims_subsyst_same dim_Ab sub_eq by blast
  show ?thesis
    unfolding less_eq_vec_def
  proof (intro conjI allI impI)
    show "dim_vec (?A' *\<^sub>v x) = dim_vec ?b'"
      using dims' by simp
  next
    fix i
    assume i: "i < dim_vec ?b'"
    have i_row: "i < dim_row ?A'"
      using i dims' by simp
    have "\<exists>k. k < dim_row A \<and> row ?A' i = row A k \<and> ?b' $ i = b $ k"
      using exist_index_in_A[of A b i I] dim_Ab sub_eq i i_row by fastforce
    then obtain k where k1: "k < dim_row A"
      and k2: "row ?A' i = row A k"
      and k3: "?b' $ i = b $ k" by blast
    have k_b: "k < dim_vec b"
      using k1 dim_Ab by simp
    have "(?A' *\<^sub>v x) $ i = row ?A' i \<bullet> x"
      using i_row by simp
    also have "\<dots> = row A k \<bullet> x"
      using k2 by simp
    also have "\<dots> = (A *\<^sub>v x) $ k"
      using k1 by simp
    also have "\<dots> \<le> b $ k"
      using Ax_idx[OF k_b] .
    also have "\<dots> = ?b' $ i"
      using k3 by simp
    finally show "(?A' *\<^sub>v x) $ i \<le> ?b' $ i" .
  qed
qed

lemma eq_iff_sum_eq_for_el_in_P:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes "((A', b') = sub_system A b I)" 
  assumes "x \<in> polyhedron A b" 
  shows "A' *\<^sub>v x = b' \<longleftrightarrow> 1\<^sub>v (dim_vec b') \<bullet> (A' *\<^sub>v x) = 1\<^sub>v (dim_vec b') \<bullet> b'"
  apply rule+
   apply blast
proof -
  assume  " 1\<^sub>v (dim_vec b') \<bullet> (A' *\<^sub>v x) = 1\<^sub>v (dim_vec b') \<bullet> b'"
  then have "A' *\<^sub>v x \<le> b'" 
  proof -
  have le: "fst (sub_system A b I) *\<^sub>v x \<le> snd (sub_system A b I)"
    by (rule subsyst_valid[OF assms(2)])
  have A'_eq: "fst (sub_system A b I) = A'" and b'_eq: "snd (sub_system A b I) = b'"
    using assms(1)[symmetric] by simp_all
  from le show "A' *\<^sub>v x \<le> b'"
    by (simp add: A'_eq b'_eq)
  qed
  then have "\<forall>i<dim_vec b'. (A' *\<^sub>v x) $ i \<le> b' $ i" 
    using less_eq_vec_def by blast
  show "A' *\<^sub>v x = b'"
  proof(rule ccontr)
    assume "A' *\<^sub>v x \<noteq> b'" 
    then obtain i where "i < dim_vec b'\<and> (A' *\<^sub>v x) $ i < b' $ i"
    proof -
      have dims: "dim_vec (A' *\<^sub>v x) = dim_vec b'"
        using \<open>A' *\<^sub>v x \<le> b'\<close> by (simp add: less_eq_vec_def)
      have le: "\<And>i. i < dim_vec b' \<Longrightarrow> (A' *\<^sub>v x) $ i \<le> b' $ i"
        using \<open>\<forall>i<dim_vec b'. (A' *\<^sub>v x) $ i \<le> b' $ i\<close> by blast
      have "\<exists>i < dim_vec b'. (A' *\<^sub>v x) $ i \<noteq> b' $ i"
      proof (rule ccontr)
        assume "\<not> (\<exists>i < dim_vec b'. (A' *\<^sub>v x) $ i \<noteq> b' $ i)"
        then have all_eq: "\<And>i. i < dim_vec b' \<Longrightarrow> (A' *\<^sub>v x) $ i = b' $ i"
          by blast
        have "A' *\<^sub>v x = b'"
        proof (rule eq_vecI)
          fix i assume "i < dim_vec b'"
          then show "(A' *\<^sub>v x) $ i = b' $ i" by (rule all_eq)
        next
          show "dim_vec (A' *\<^sub>v x) = dim_vec b'" by (rule dims)
        qed
        then show False using \<open>A' *\<^sub>v x \<noteq> b'\<close> by simp
      qed
      then obtain i where i_lt: "i < dim_vec b'"
                      and i_neq: "(A' *\<^sub>v x) $ i \<noteq> b' $ i"
        by blast
      have "(A' *\<^sub>v x) $ i < b' $ i"
        using le[OF i_lt] i_neq by (simp add: order_less_le)
      then show thesis using that i_lt by blast
    qed
    then have "sum (\<lambda> i. (A' *\<^sub>v x) $ i) {0..<dim_vec b'}  < sum (\<lambda> i. b' $ i) {0..<dim_vec b'}"
      proof -
      have le: "\<forall>j \<in> {0..<dim_vec b'}. (A' *\<^sub>v x) $ j \<le> b' $ j"
        using lesseq_vecD[OF carrier_vec_dim_vec \<open>A' *\<^sub>v x \<le> b'\<close>] by auto
      have lt: "\<exists>j \<in> {0..<dim_vec b'}. (A' *\<^sub>v x) $ j < b' $ j"
        using \<open>i < dim_vec b' \<and> (A' *\<^sub>v x) $ i < b' $ i\<close> by auto
      show ?thesis
        by (rule sum_strict_mono_ex1[OF finite_atLeastLessThan le lt])
    qed
    then have "1\<^sub>v (dim_vec b') \<bullet> (A' *\<^sub>v x) < 1\<^sub>v (dim_vec b') \<bullet> b'"
    proof -
      have dim_eq: "dim_vec (A' *\<^sub>v x) = dim_vec b'"
        using \<open>A' *\<^sub>v x \<le> b'\<close> by (simp add: less_eq_vec_def)
      have carr: "A' *\<^sub>v x \<in> carrier_vec (dim_vec b')"
        using dim_eq carrier_vecI by blast
      have e1: "1\<^sub>v (dim_vec b') \<bullet> (A' *\<^sub>v x) = (\<Sum>i = 0..<dim_vec b'. (A' *\<^sub>v x) $ i)"
        by (rule scalar_prod_left_one[OF carr])
      have e2: "1\<^sub>v (dim_vec b') \<bullet> b' = (\<Sum>i = 0..<dim_vec b'. b' $ i)"
        by (rule scalar_prod_left_one[OF carrier_vec_dim_vec])
      show ?thesis
        using e1 e2
          \<open>(\<Sum>i = 0..<dim_vec b'. (A' *\<^sub>v x) $ i) < (\<Sum>i = 0..<dim_vec b'. b' $ i)\<close>
        by linarith
    qed
    then show False 
      using \<open>1\<^sub>v (dim_vec b') \<bullet> (A' *\<^sub>v x) = 1\<^sub>v (dim_vec b') \<bullet> b'\<close> by linarith
  qed
qed

lemma char_face2:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "((A', b') = sub_system A b I)" 
  assumes "F = {x. A' *\<^sub>v x = b' \<and> x \<in> P}"
  assumes "F \<noteq> {}" 
  shows  "face P F"
proof -
  let ?\<alpha> = "A'\<^sup>T *\<^sub>v 1\<^sub>v (dim_vec b')"
  let ?\<beta> = " 1\<^sub>v (dim_vec b') \<bullet> b'"
  have "?\<beta> = sum (\<lambda> i. b' $ i) {0..<dim_vec b'}"   
    by auto
  have "A' \<in> carrier_mat (dim_vec b') n" using carrier_mat_subsyst 
  proof -
    have dimAb: "dim_row A = dim_vec b"
      using carrier_matD(1)[OF A] carrier_vecD[OF b] by simp
    have colA: "dim_col A = n"
      by (rule carrier_matD(2)[OF A])
    have A'_eq: "A' = fst (sub_system A b I)"
      by (simp add: assms(4)[symmetric])
    have rows: "dim_row A' = dim_vec b'"
      using dims_subsyst_same' dimAb assms(4) by blast
    have cols: "dim_col A' = n"
    proof -
      have "dim_col A' = dim_col (fst (sub_system A b I))"
        by (simp add: A'_eq)
      also have "\<dots> = dim_col A"
        by (simp add: dim_col_subsyst_mat)
      also have "\<dots> = n"
        by (rule colA)
      finally show ?thesis .
    qed
    show ?thesis
      by (rule carrier_matI[OF rows cols])
  qed
  have 1: "\<forall> x\<in> carrier_vec n. (A'\<^sup>T *\<^sub>v 1\<^sub>v (dim_vec b')) \<bullet> x =  1\<^sub>v (dim_vec b') \<bullet> (A' *\<^sub>v x)" 
    using transpose_vec_mult_scalar[of A' "dim_vec b'" n  _ "1\<^sub>v (dim_vec b')"]
    using `A' \<in> carrier_mat (dim_vec b') n`  by simp
  have "\<forall>x \<in> P. A' *\<^sub>v x = b' \<longleftrightarrow> 1\<^sub>v (dim_vec b') \<bullet> (A' *\<^sub>v x) = 1\<^sub>v (dim_vec b') \<bullet> b'"
    using eq_iff_sum_eq_for_el_in_P 
    using P_def assms(4) by blast
  then have "\<forall>x \<in> P. A' *\<^sub>v x = b' \<longleftrightarrow> (A'\<^sup>T *\<^sub>v 1\<^sub>v (dim_vec b')) \<bullet> x = 1\<^sub>v (dim_vec b') \<bullet> b'"
    by (simp add: P_def 1 gram_schmidt.polyhedron_def)
  then have "{x. A' *\<^sub>v x = b' \<and> x \<in> P} = {x. ?\<alpha> \<bullet> x = ?\<beta> \<and> x \<in> P}"
    by blast 
  have "\<forall> x \<in> P. A' *\<^sub>v x \<le> b'" 
  proof (intro ballI)
    fix x
    assume xP: "x \<in> P"
    then have x: "x \<in> polyhedron A b"
      by (simp add: P_def)
    have eq: "sub_system A b I = (A', b')"
      using assms(4) by simp
    from x have "fst (sub_system A b I) *\<^sub>v x \<le> snd (sub_system A b I)"
      by (rule subsyst_valid)
    then show "A' *\<^sub>v x \<le> b'"
      by (simp add: eq)
  qed
  then have "\<forall> x \<in> P.  1\<^sub>v (dim_vec b') \<bullet> (A' *\<^sub>v x) \<le> 1\<^sub>v (dim_vec b') \<bullet> b'"
  proof -
    assume subsyst_le: "\<forall> x \<in> P. A' *\<^sub>v x \<le> b'"
    show ?thesis
    proof (rule ballI)
      fix x
      assume "x \<in> P"
      then have le: "A' *\<^sub>v x \<le> b'"
        using subsyst_le by blast
      have dim_eq: "dim_vec (A' *\<^sub>v x) = dim_vec b'"
        using le unfolding less_eq_vec_def by blast
      have carr: "A' *\<^sub>v x \<in> carrier_vec (dim_vec b')"
        using dim_eq unfolding carrier_vec_def by simp
      have le_index: "\<forall> i < dim_vec b'. (A' *\<^sub>v x) $ i \<le> b' $ i"
        using le unfolding less_eq_vec_def by blast
      have "1\<^sub>v (dim_vec b') \<bullet> (A' *\<^sub>v x) = (\<Sum> i = 0..<dim_vec b'. (A' *\<^sub>v x) $ i)"
        by (rule scalar_prod_left_one[OF carr])
      also have "\<dots> \<le> (\<Sum> i = 0..<dim_vec b'. b' $ i)"
      proof (rule sum_mono)
        fix i
        assume "i \<in> {0..<dim_vec b'}"
        then have "i < dim_vec b'" by simp
        then show "(A' *\<^sub>v x) $ i \<le> b' $ i"
          using le_index by blast
      qed
      also have "\<dots> = 1\<^sub>v (dim_vec b') \<bullet> b'"
        by (rule scalar_prod_left_one[OF carrier_vec_dim_vec, symmetric])
      finally show "1\<^sub>v (dim_vec b') \<bullet> (A' *\<^sub>v x) \<le> 1\<^sub>v (dim_vec b') \<bullet> b'" .
    qed
  qed
  then have "valid_ineq P ?\<alpha> ?\<beta>" 
    unfolding valid_ineq_def P_def polyhedron_def 
    using "1" \<open>A' \<in> carrier_mat (dim_vec b') n\<close> by force
  then show "face P F" using face_intro'[of P ?\<alpha> ?\<beta> F] assms(5-6)
      `{x. A' *\<^sub>v x = b' \<and> x \<in> P} = {x. ?\<alpha> \<bullet> x = ?\<beta> \<and> x \<in> P}` by auto 
qed

lemma set_of_sub_dims_finite:
  shows "finite {dim_vec d| C d I. (C, d) = sub_system A b I}" (is "finite ?M")
proof -
  have "\<forall> nd \<in> ?M. nd\<le> dim_vec b"
  proof (rule ballI, goal_cases)
    case (1 nd)
    then obtain C d I where nd_eq: "nd = dim_vec d"
      and sub: "(C, d) = sub_system A b I"
      by blast
    have snd_eq: "snd (sub_system A b I) = d"
      by (simp add: sub [symmetric])
    have "dim_vec (snd (sub_system A b I)) \<le> dim_vec b"
      by (rule dim_subsyst_vec_less_b)
    then show ?case
      using nd_eq snd_eq by simp
  qed
   then have "?M \<subseteq> {0..<dim_vec b+1}" by fastforce 
  then show "finite ?M" 
    using subset_eq_atLeast0_lessThan_finite by blast
qed

lemma subset_set_of_sub_dims_finite:
  assumes "M \<subseteq> {dim_vec d| C d I. (C, d) = sub_system A b I}"
  shows "finite M" 
  using set_of_sub_dims_finite[of A b] finite_subset
  using assms by blast

lemma exist_max_subsystem:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
 assumes A: "A \<in> carrier_mat nr n"
 assumes b: "b \<in> carrier_vec nr"
 defines "P \<equiv> polyhedron A b"
 assumes "face P F"
 obtains A' b' I  where "((A', b') = sub_system A b I)" 
                      "F = {x. A' *\<^sub>v x = b' \<and> x \<in> P}"
                      "dim_vec b' = Max {dim_vec d| C d I. (C, d) = sub_system A b I \<and> 
                                                                    F = {x. C *\<^sub>v x = d \<and> x \<in> P}}"
proof-
  have "dim_vec b = nr" using b by auto
  let ?M = "{dim_vec d| C d I.  (C, d) = sub_system A b I \<and> F = {x. C *\<^sub>v x = d \<and> x \<in> P}}"
  have "?M \<noteq> {}"
  proof -
    have faceP: "face (polyhedron A b) F"
      using assms by (simp add: P_def)
    obtain A' b' I' where A'b': "(A', b') = sub_system A b I'"
      and F_eq: "F = {x. A' *\<^sub>v x = b' \<and> x \<in> polyhedron A b}"
      by (rule char_face1[OF A b faceP])
    have F_eq_P: "F = {x. A' *\<^sub>v x = b' \<and> x \<in> P}"
      using F_eq by (simp add: P_def)
    have mem: "dim_vec b' \<in> ?M"
      using A'b' F_eq_P by blast
    show ?thesis
    proof
      assume "?M = {}"
      with mem show False by blast
    qed
  qed
  then have "finite ?M"
    using subset_set_of_sub_dims_finite[of ?M A b] by blast
  then have "Max ?M \<in> ?M \<and> (\<forall>a \<in> ?M. a \<le> (Max ?M))"
    using eq_Max_iff[of ?M] `?M \<noteq> {}`
    by auto
  then show ?thesis 
    using that by force
qed

lemma exist_min_ineq_subsystem:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
 assumes A: "A \<in> carrier_mat nr n"
 assumes b: "b \<in> carrier_vec nr"
 defines "P \<equiv> polyhedron A b"
 assumes "((A', b') = sub_system A b I')"
 assumes "F = {x. A' *\<^sub>v x = b' \<and> x \<in> P}"
 obtains A'' b'' I''
 where  "((A'', b'') = sub_system A b I'')"
       "F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> A'' *\<^sub>v x \<le> b'' }"
       "dim_vec b'' = Min {dim_vec d| C d I.  (C, d) = sub_system A b I 
                                  \<and> F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d}}"
proof -
  let ?M = "{dim_vec d| C d I.  (C, d) = sub_system A b I \<and>
           F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d}}"
   have "(A, b) = sub_system A b UNIV" using itself_is_subsyst by auto
   have "F = {x. x \<in> carrier_vec n \<and>  A' *\<^sub>v x = b' \<and> A *\<^sub>v x \<le> b}" 
    using assms(5) P_def  unfolding polyhedron_def 
    by blast
  then  have "?M \<noteq> {}" using `(A, b) = sub_system A b UNIV` by auto
  then have "finite ?M" 
using subset_set_of_sub_dims_finite[of ?M A b] by blast 
  then have "Min ?M \<in> ?M \<and> (\<forall>a \<in> ?M. a \<ge> (Min ?M))"
    using eq_Min_iff[of ?M] `?M \<noteq> {}`
    by auto
  then show ?thesis using that by force
qed

lemma exist_min_ineq_subsystem':
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  assumes "((A', b') = sub_system A b I')"
  assumes "((A'', b'') = sub_system A b I'')"
  assumes "F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> A'' *\<^sub>v x \<le> b'' }"
  assumes "dim_vec b'' = Min {dim_vec d| C d I.  (C, d) = sub_system A b I 
                                  \<and> F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d}}"
  shows "I' \<inter> I'' \<inter> {0..<nr} = {}" 
proof(rule ccontr)
  let ?N =  "{dim_vec d| C d I.  (C, d) = sub_system A b I 
                                  \<and> F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d}}" 
  have 2:"finite ?N"  
    using subset_set_of_sub_dims_finite[of ?N A b] by blast 
  have "dim_vec b = nr" using b by auto
  assume "I' \<inter> I'' \<inter> {0..<nr}\<noteq> {}" 
  then obtain i where i:"i \<in> I' \<and> i \<in> I'' \<and> i < nr" by fastforce
  then obtain C d where "(C, d) = sub_system A b (I'' - {i})" 
  proof -
    show ?thesis
      by (rule that[OF prod.collapse])
  qed
  then have "{x. A'' *\<^sub>v x \<le> b''} = {x. C *\<^sub>v x \<le> d \<and> row A i \<bullet> x \<le> b $ i}"
    using remove_index_sub_system assms(4) i  A \<open>dim_vec b = nr\<close> by blast
  then have "F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d \<and> row A i \<bullet> x \<le> b $ i}"
    using assms(5) by blast
  have "\<forall> x \<in> carrier_vec n. b' = A' *\<^sub>v x \<longrightarrow> row A i \<bullet> x = b $ i"
    proof (intro ballI impI)
      fix z :: "'a vec"
      assume z: "z \<in> carrier_vec n"
      assume eq: "b' = A' *\<^sub>v z"
      obtain C d where Cd: "(C, d) = sub_system A b (I' - {i})"
        using prod.collapse by blast
      have set_eq: "{y. A' *\<^sub>v y = b'} = {y. C *\<^sub>v y = d \<and> row A i \<bullet> y = b $ i}"
        using remove_index_sub_system_eq Cd assms(3) i A \<open>dim_vec b = nr\<close> by blast
      have "z \<in> {y. A' *\<^sub>v y = b'}"
        using eq by simp
      then show "row A i \<bullet> z = b $ i"
        using set_eq by blast
    qed
  then have "F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d}" 
    using \<open>F = {x \<in> carrier_vec n. A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d \<and> row A i \<bullet> x \<le> b $ i}\<close> by fastforce
  then have "dim_vec d \<in> ?N" 
    using `(C, d) = sub_system A b (I'' - {i})` by blast
  then have "dim_vec d \<ge> dim_vec b''"
    using 2 assms(6) `(C, d) = sub_system A b (I'' - {i})`
    by auto
  have "dim_vec d + 1 = dim_vec b''"
  proof -
    have i_in: "i \<in> I''"
      using i by auto
    have i_lt: "i < dim_vec b"
      using i carrier_vecD[OF b] by auto
    show ?thesis
      using remove_index_sub_system_dims[of i I'' b A'' b'' A]
            i_in i_lt assms(4) \<open>(C, d) = sub_system A b (I'' - {i})\<close>
      by simp
  qed
  then have "dim_vec d < dim_vec b''" by auto
  then show False 
    using \<open>dim_vec b'' \<le> dim_vec d\<close> linorder_not_le by blast
qed

text \<open>Minimal Faces\<close>

text \<open>Minimal faces are faces that doesn't contain any other face. They are affine spaces\<close>

definition min_face where
  "min_face P F = (face P F \<and> (\<nexists> F'. F' \<subset> F \<and> face P F'))"

lemma min_face_elim[elim]:
  assumes "min_face P F" 
  shows "face P F" 
       "(\<nexists> F'. F' \<subset> F \<and> face P F')"
  using assms unfolding min_face_def by auto

lemma min_face_intro[intro]:
  assumes "face P F"
  assumes "(\<nexists> F'. F' \<subset> F \<and> face P F')"
  shows "min_face P F"
  unfolding min_face_def using assms by auto
     
lemma smult_minus_distrib_vec:
  assumes "v \<in> carrier_vec n" "w \<in> carrier_vec n"
  shows "(a::'b::ring) \<cdot>\<^sub>v (v - w) = a \<cdot>\<^sub>v v - a \<cdot>\<^sub>v w"
  apply (rule eq_vecI)
  unfolding smult_vec_def minus_vec_def  
  using assms(1) assms(2) right_diff_distrib 
   apply force
  by force

lemma char_min_face1:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
 fixes b
 assumes A: "A \<in> carrier_mat nr n"
 assumes b: "b \<in> carrier_vec nr"
 defines "P \<equiv> polyhedron A b"
 assumes "min_face P F"
 obtains A' b' I where  " F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'}" "(A', b') = sub_system A b I" 
proof -
  have "face P F" using assms(4) min_face_elim by auto
  have "dim_vec b = nr" using b by auto
  let ?M = "{dim_vec d| C d I.  (C, d) = sub_system A b I \<and> F = {x. C *\<^sub>v x = d \<and> x \<in> P}}"
  have 7:"finite ?M"  
    using subset_set_of_sub_dims_finite[of ?M A b] by blast 

  then obtain A' b' I  where sub_A:"((A', b') = sub_system A b I)" 
                      "F = {x. A' *\<^sub>v x = b' \<and> x \<in> P}"
                      "dim_vec b' = Max ?M"
    using exist_max_subsystem[of A nr b F] assms min_face_elim
    by auto

  let ?N =  "{dim_vec d| C d I.  (C, d) = sub_system A b I 
                                  \<and> F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d}}" 
 have 2:"finite ?N"  
    using subset_set_of_sub_dims_finite[of ?N A b] by blast 
  obtain A'' b'' I''
    where  sub_A'':"((A'', b'') = sub_system A b I'')"
       "F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> A'' *\<^sub>v x \<le> b'' }"
       "dim_vec b'' = Min ?N"
    using  exist_min_ineq_subsystem[of A nr b A' b' I F] sub_A assms(1-3) by auto
  have "dim_vec b = nr"
    using b by auto
  have "I \<inter> I'' \<inter> {0..<nr}= {}"
    using exist_min_ineq_subsystem'[of A nr b A' b' I A'' b'' I'']
      assms  sub_A sub_A'' 
    by presburger
  have "dim_vec b'' = 0" 
  proof(rule ccontr)
    assume "dim_vec b'' \<noteq> 0" 
    then have "dim_vec b'' > 0" by auto
    then obtain j where "j < dim_vec b''" by auto
    then obtain i where i:"i < nr \<and> i \<in> I'' \<and> row A'' j = row A i \<and> b'' $ j = b $ i" 
    proof -
      have dim_A: "dim_row A = nr"
        using A by (rule carrier_matD(1))
      have dim_b: "dim_vec b = nr"
        using b by (rule carrier_vecD)
      have dims: "dim_row A = dim_vec b"
        using dim_A dim_b by simp
      have sub_eq: "sub_system A b I'' = (A'', b'')"
        using sub_A''(1) by (rule sym)
      have fst_eq: "fst (sub_system A b I'') = A''"
        by (simp add: sub_eq)
      have snd_eq: "snd (sub_system A b I'') = b''"
        by (simp add: sub_eq)
      have j_lt: "j < dim_vec (snd (sub_system A b I''))"
        using \<open>j < dim_vec b''\<close> snd_eq by simp
      obtain k where k_lt: "k < dim_vec b"
        and k_in: "k \<in> I''"
        and k_row: "row (fst (sub_system A b I'')) j = row A k"
        and k_val: "snd (sub_system A b I'') $ j = b $ k"
        using exist_index_in_A[OF dims j_lt] by blast
      have "k < nr"
        using k_lt dim_b by simp
      moreover have "row A'' j = row A k"
        using k_row fst_eq by simp
      moreover have "b'' $ j = b $ k"
        using k_val snd_eq by simp
      ultimately show thesis
        using that k_in by blast
    qed
    obtain C d where sub_C: "((C, d) = sub_system A b (I'' - {i}))" 
      using that[OF prod.collapse] by blast
    have "{x. A'' *\<^sub>v x \<le> b''} = {x. C *\<^sub>v x \<le> d \<and> row A i \<bullet> x \<le> b $ i}"    
      using remove_index_sub_system
      using sub_A''(1) sub_C(1)  i 
      using A \<open>dim_vec b = nr\<close> by blast
    then have F_by_Cd: "F = {x. x \<in> carrier_vec n \<and> 
                                A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d \<and> 
                                row A i \<bullet> x \<le> b $ i}"
      using sub_A''(2) by fastforce

    show False 
    proof(cases "{x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d} \<inter> 
                 {x. row A i \<bullet> x > b $ i} = {}")
      case True
      then have "F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d}"
        using True F_by_Cd by fastforce
      then have "dim_vec d \<in> ?N"
        using  `((C, d) = sub_system A b (I'' - {i}))`
        by auto 
      then have "dim_vec d \<ge> dim_vec b''" 
        using `dim_vec b'' = Min ?N` 2 by simp
      have "dim_vec d + 1 = dim_vec b''" 
        using remove_index_sub_system_dims[of i I'' b A'' b'' A]
        using \<open>dim_vec b = nr\<close> i sub_A''(1) sub_C by presburger   
      then show ?thesis using `dim_vec d \<ge> dim_vec b''` by simp 
    next
      case False
      have 1:"row A i \<in> carrier_vec n" 
        using A i row_carrier_vec by blast
      then obtain y where 
        "y \<in> {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d} \<inter> {x. row A i \<bullet> x > b $ i}"
        using False  by auto
      then have y: "y \<in> carrier_vec n \<and> A' *\<^sub>v y = b' \<and> C *\<^sub>v y \<le> d \<and> row A i \<bullet> y > b $ i"  
        by fastforce
      then have y_n:"y \<in> carrier_vec n" by auto
      obtain x  where "x\<in> F" 
        proof -
          have "F \<noteq> {}"
            by (rule face_non_empty[OF \<open>face P F\<close>])
          then have "\<exists>z. z \<in> F"
            by (simp add: ex_in_conv)
          then obtain z where "z \<in> F"
            by blast
          then show thesis
            by (rule that)
        qed
      then have x: "x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d \<and> row A i \<bullet> x \<le> b $ i" 
        using F_by_Cd by fastforce
      then have x_n:"x \<in> carrier_vec n" by auto
      have 2: "row A i \<bullet> x - row A i \<bullet> y \<noteq> 0" 
        using x y by linarith
      let ?z = "y + ((b $ i - row A i \<bullet> y)/(row A i \<bullet> x - row A i \<bullet> y)) \<cdot>\<^sub>v (x - y)"
      have "row A i \<bullet> ?z = 
            row A i \<bullet> y + row A i \<bullet> (((b $ i - row A i \<bullet> y)/(row A i \<bullet> x - row A i \<bullet> y)) \<cdot>\<^sub>v (x - y))" 
        by (meson 1 x_n y_n minus_carrier_vec scalar_prod_add_distrib smult_closed)
      then have "row A i \<bullet> ?z = row A i \<bullet> y + ((b $ i - row A i \<bullet> y)/(row A i \<bullet> x - row A i \<bullet> y)) * 
                                               (row A i \<bullet> (x - y))" 
        proof -
          have xy_carr: "x - y \<in> carrier_vec n"
            using x_n y_n by auto
          have smult_dist: "row A i \<bullet> (c \<cdot>\<^sub>v (x - y)) = c * (row A i \<bullet> (x - y))" for c
            using 1 xy_carr by (rule scalar_prod_smult_distrib)
          have add_dist: "row A i \<bullet> (y + c \<cdot>\<^sub>v (x - y)) = row A i \<bullet> y + row A i \<bullet> (c \<cdot>\<^sub>v (x - y))" for c
            using 1 y_n smult_closed xy_carr by (blast intro: scalar_prod_add_distrib)

          show ?thesis
            by (simp only: add_dist smult_dist)
        qed
      then have "row A i \<bullet> ?z = row A i \<bullet> y + (b $ i - row A i \<bullet> y)" 
      proof -
        have xy: "x - y \<in> carrier_vec n"
          by (simp add: x_n y_n)
        have sm: "((b $ i - row A i \<bullet> y) / (row A i \<bullet> x - row A i \<bullet> y)) \<cdot>\<^sub>v (x - y) \<in> carrier_vec n"
          by (simp add: x_n y_n)
        have zsplit: "row A i \<bullet> ?z =
            row A i \<bullet> y +
            row A i \<bullet> (((b $ i - row A i \<bullet> y) / (row A i \<bullet> x - row A i \<bullet> y)) \<cdot>\<^sub>v (x - y))"
          by (rule scalar_prod_add_distrib[OF 1 y_n sm])
        have smult_out:
          "row A i \<bullet> (((b $ i - row A i \<bullet> y) / (row A i \<bullet> x - row A i \<bullet> y)) \<cdot>\<^sub>v (x - y)) =
           ((b $ i - row A i \<bullet> y) / (row A i \<bullet> x - row A i \<bullet> y)) * (row A i \<bullet> (x - y))"
          by (rule scalar_prod_smult_distrib[OF 1 xy])
        have minus_out: "row A i \<bullet> (x - y) = row A i \<bullet> x - row A i \<bullet> y"
          by (rule scalar_prod_minus_distrib[OF 1 x_n y_n])
        have cancel:
          "((b $ i - row A i \<bullet> y) / (row A i \<bullet> x - row A i \<bullet> y)) * (row A i \<bullet> x - row A i \<bullet> y) =
           b $ i - row A i \<bullet> y"
          using 2 by (simp add: field_simps)
        show ?thesis
          by (simp only: zsplit smult_out minus_out cancel)
      qed
      then have 4:"row A i \<bullet> ?z = b $ i" 
        by simp
      let ?l = "(b $ i - row A i \<bullet> y)/(row A i \<bullet> x - row A i \<bullet> y)"
      have "?z = y + ?l \<cdot>\<^sub>v (x - y)" by simp
      then have "?z =  y  + ?l  \<cdot>\<^sub>v x - ?l \<cdot>\<^sub>v y " 
        using smult_minus_distrib_vec[of x y ?l] x_n y_n by fastforce
      have "y  + ?l  \<cdot>\<^sub>v x - ?l \<cdot>\<^sub>v y = y   - ?l \<cdot>\<^sub>v y + ?l  \<cdot>\<^sub>v x" 
        using x_n y_n by auto
      have "1  \<cdot>\<^sub>v y = y" 
        by simp
      have "?z =  1  \<cdot>\<^sub>v y  - ?l \<cdot>\<^sub>v y  + ?l  \<cdot>\<^sub>v x" 
        apply (auto simp:`1  \<cdot>\<^sub>v y = y`)
        using `?z =  y  + ?l  \<cdot>\<^sub>v x - ?l \<cdot>\<^sub>v y ` 
        by (simp add: `y  + ?l  \<cdot>\<^sub>v x - ?l \<cdot>\<^sub>v y = y   - ?l \<cdot>\<^sub>v y + ?l  \<cdot>\<^sub>v x`)
      then have "?z = (1 - ?l) \<cdot>\<^sub>v y + ?l  \<cdot>\<^sub>v x"
        using diff_smult_distrib_vec[of 1 ?l y] `?z =  y  + ?l  \<cdot>\<^sub>v x - ?l \<cdot>\<^sub>v y `  
        by presburger
      have "0 < ?l" using x y 
        by (meson less_iff_diff_less_0 order_le_less_trans zero_less_divide_iff)
      have "?l \<le> 1" using x y 
        by auto
      have 5:"?z \<in> carrier_vec n" 
        by (simp add: \<open>x \<in> carrier_vec n\<close> \<open>y \<in> carrier_vec n\<close>)
      have "A' \<in> carrier_mat (dim_row A') n" 
      proof -
        have A'_eq: "A' = fst (sub_system A b I)"
          by (simp add: sub_A(1)[symmetric])
        have "dim_col A' = dim_col A"
          by (simp add: A'_eq dim_col_subsyst_mat)
        also have "\<dots> = n"
          using A by (rule carrier_matD(2))
        finally have dc: "dim_col A' = n" .
        show "A' \<in> carrier_mat (dim_row A') n"
          by (rule carrier_matI[OF refl dc])
      qed
      then have 3:"A' *\<^sub>v ?z = b'" 
      proof -
        note A'_carr = \<open>A' \<in> carrier_mat (dim_row A') n\<close>
        note l_pos = \<open>0 < ?l\<close>
        note l_le1 = \<open>?l \<le> 1\<close>
        note z_carr = \<open>?z \<in> carrier_vec n\<close>
        note z_eq_yx = \<open>?z = (1 - ?l) \<cdot>\<^sub>v y + ?l  \<cdot>\<^sub>v x\<close>
        have xc: "x \<in> carrier_vec n" by (rule x_n)
        have yc: "y \<in> carrier_vec n" by (rule y_n)
        have Ax: "A' *\<^sub>v x = b'" using x by blast
        have Ay: "A' *\<^sub>v y = b'" using y by blast
        have l_nonneg: "0 \<le> ?l" using l_pos by (rule less_imp_le)
        have l1_nonneg: "0 \<le> 1 - ?l" using l_le1 by linarith
        have l1_le1: "1 - ?l \<le> 1" using l_nonneg by linarith
        have sx: "?l \<cdot>\<^sub>v x \<in> carrier_vec n" using xc by simp
        have sy: "(1 - ?l) \<cdot>\<^sub>v y \<in> carrier_vec n" using yc by simp
        have z_eq_xy: "?z = ?l \<cdot>\<^sub>v x + (1 - ?l) \<cdot>\<^sub>v y"
          using z_eq_yx comm_add_vec[OF sy sx] by simp
        have z_eq_xy': "?z = (1 - (1 - ?l)) \<cdot>\<^sub>v x + (1 - ?l) \<cdot>\<^sub>v y"
          using z_eq_xy by simp
        have z_eq_yx': "?z = (1 - ?l) \<cdot>\<^sub>v y + (1 - (1 - ?l)) \<cdot>\<^sub>v x"
          using z_eq_yx by simp
        show ?thesis
          using linear_comb_holds_eq[of A' "dim_row A'" n x y ?z b' ?l]
                linear_comb_holds_eq[of A' "dim_row A'" n y x ?z b' "1 - ?l"]
                A'_carr xc yc z_carr Ax Ay
                z_eq_xy z_eq_yx z_eq_xy' z_eq_yx'
                z_eq_xy[symmetric] z_eq_yx[symmetric]
                z_eq_xy'[symmetric] z_eq_yx'[symmetric]
                l_pos l_le1 l_nonneg l1_nonneg l1_le1
          by blast
      qed
      have "C \<in> carrier_mat (dim_row C) n" 
      proof -
        have C_eq: "C = fst (sub_system A b (I'' - {i}))"
          by (simp add: sub_C [symmetric])
        have "dim_col C = dim_col (fst (sub_system A b (I'' - {i})))"
          by (simp add: C_eq)
        also have "\<dots> = dim_col A"
          by (simp add: dim_col_subsyst_mat)
        also have "\<dots> = n"
          by (rule carrier_matD(2)[OF A])
        finally have dc: "dim_col C = n" .
        show ?thesis
          by (rule carrier_matI[OF refl dc])
      qed
      then have " C *\<^sub>v ?z \<le> d" 
        using linear_comb_holds_less_eq[of C _ n x y ?z d ?l]
          x y `?z = (1 - ?l) \<cdot>\<^sub>v y + ?l  \<cdot>\<^sub>v x` `?z \<in> carrier_vec n` 
        by (simp add: M.add.m_comm  zero_le_divide_iff)
      then have "?z \<in> {x \<in> carrier_vec n. A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d \<and> row A i \<bullet> x \<le> b $ i}" 
        by (simp add: 3 4 5)
      then have "?z \<in> F" 
        using F_by_Cd by presburger
      then have "?z \<in> P" using `face P F`  
        using face_subset_polyhedron[OF \<open>face P F\<close>] by blast
      have "i \<notin> I" using `I \<inter> I'' \<inter> {0..<nr}= {}` 
        using \<open>i < nr \<and> i \<in> I'' \<and> row A'' j = row A i \<and> b'' $ j = b $ i\<close>
        by fastforce
      obtain C' d'  where "(C', d') = sub_system A b (I \<union> {i})" 
        by (rule that[OF prod.collapse])
      then have "{x. C' *\<^sub>v x = d'} = {x. A' *\<^sub>v x = b' \<and> row A i \<bullet> x = b $ i}" 
        using insert_sub_system_eq[of A b i  A' b' I  C' d'] 
              \<open>i \<notin> I\<close> sub_A(1) A \<open>dim_vec b = nr\<close> i by blast
      then have 6:"{x. C' *\<^sub>v x = d' \<and> x \<in> P} = {x. A' *\<^sub>v x = b' \<and> row A i \<bullet> x = b $ i \<and> x \<in> P}" 
        by blast
      have "?z \<in>  {x. A' *\<^sub>v x = b' \<and> row A i \<bullet> x = b $ i \<and> x \<in> P}" 
        using `?z \<in> P` 
        using \<open>A' *\<^sub>v ?z = b'\<close> \<open>row A i \<bullet> ?z = b $ i\<close> by blast
      then have "{x. C' *\<^sub>v x = d' \<and> x \<in> P} \<noteq> {}" 
        using 6 by blast
      then have "face P {x. C' *\<^sub>v x = d' \<and> x \<in> P}" using char_face2 
        using P_def \<open>(C', d') = sub_system A b (I \<union> {i})\<close> assms(1) b by blast
      have "{x. C' *\<^sub>v x = d' \<and> x \<in> P} \<subseteq> F" 
        using 6 sub_A(2) by blast
      then have "{x. C' *\<^sub>v x = d' \<and> x \<in> P} = F" 
        using \<open>face P {x. C' *\<^sub>v x = d' \<and> x \<in> P}\<close> assms(4) min_face_def by auto
      then have "(C', d') = sub_system A b (I\<union>{i}) \<and> F = {x. C' *\<^sub>v x = d' \<and> x \<in> P}" 
        using \<open>(C', d') = sub_system A b (I \<union> {i})\<close> by fastforce
      then have "dim_vec d' \<in> 
                {dim_vec d| C d I.  (C, d) = sub_system A b I \<and> F = {x. C *\<^sub>v x = d \<and> x \<in> P}}"
        by blast
      then have "dim_vec d' \<le> 
                 Max {dim_vec d| C d I.  (C, d) = sub_system A b I \<and> F = {x. C *\<^sub>v x = d \<and> x \<in> P}}" 
        using "7" by auto
      then have "dim_vec d' \<le> dim_vec b'" 
        using sub_A(3) by presburger
      have "dim_vec d' = dim_vec b' + 1" using add_index_sub_system_dims 
        using \<open>(C', d') = sub_system A b (I \<union> {i})\<close> \<open>i \<notin> I\<close> sub_A(1) \<open>dim_vec b = nr\<close> i by blast
      then show ?thesis 
        using \<open>dim_vec d' \<le> dim_vec b'\<close> by linarith
    qed
  qed 
    then have "\<exists> x. x\<in> {x.  A'' *\<^sub>v x \<le> b''}" 
      using sub_A'' \<open>face P F\<close> face_non_empty by auto 
    then have "{x.  A'' *\<^sub>v x \<le> b''} = UNIV" using `dim_vec b'' = 0`
    proof -
      have dimAb: "dim_row A = dim_vec b"
        using A b by auto
      have "dim_row (fst (sub_system A b I'')) = dim_vec (snd (sub_system A b I''))"
        by (rule dims_subsyst_same[OF dimAb])
      then have rows: "dim_row A'' = dim_vec b''"
        by (simp add: sub_A''(1)[symmetric])
      have all: "A'' *\<^sub>v v \<le> b''" for v
      proof -
        have dimz: "dim_vec (A'' *\<^sub>v v) = dim_vec b''"
          by (simp only: dim_mult_mat_vec rows)
        have idx: "\<forall>i < dim_vec b''. (A'' *\<^sub>v v) $ i \<le> b'' $ i"
          using \<open>dim_vec b'' = 0\<close> by simp
        show ?thesis
          using dimz idx unfolding less_eq_vec_def by blast
      qed
      show ?thesis
        using all by simp
    qed
    then have "{x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> A'' *\<^sub>v x \<le> b''}
                 = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'}" 
      by blast
    then have " F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'}" 
      using \<open>F = {x \<in> carrier_vec n. A' *\<^sub>v x = b' \<and> A'' *\<^sub>v x \<le> b''}\<close> by fastforce
    then show ?thesis
      using sub_A(1) that by blast
  qed

lemma eq_system_is_leq_system:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes "dim_vec x = dim_col A"
  shows "A *\<^sub>v x = b \<longleftrightarrow> A *\<^sub>v x \<le> b \<and> (-A) *\<^sub>v x \<le> - b"
proof -
  have neg: "(- A) *\<^sub>v x = - (A *\<^sub>v x)"
    using uminus_mult_mat_vec[of x A] assms by simp
  show ?thesis
  proof (rule iffI, goal_cases fwd bwd)
    case fwd
    show ?case
      using fwd neg by (simp add: less_eq_vec_def)
  next
    case bwd
    have le1: "A *\<^sub>v x \<le> b"
      using bwd by blast
    have le2: "(- A) *\<^sub>v x \<le> - b"
      using bwd by blast
    have dims: "dim_vec (A *\<^sub>v x) = dim_vec b"
      using le1 unfolding less_eq_vec_def by blast
    have upper: "(A *\<^sub>v x) $ i \<le> b $ i" if "i < dim_vec b" for i
      using le1 that unfolding less_eq_vec_def by blast
    have lower: "b $ i \<le> (A *\<^sub>v x) $ i" if i: "i < dim_vec b" for i
    proof -
      have m: "- (A *\<^sub>v x) \<le> - b"
        using le2 neg by simp
      have lt: "i < dim_vec (A *\<^sub>v x)"
        using i dims by simp
      have e1: "(- (A *\<^sub>v x)) $ i = - ((A *\<^sub>v x) $ i)"
        using lt by (rule index_uminus_vec)
      have e2: "(- b) $ i = - (b $ i)"
        using i by (rule index_uminus_vec)
      have lt2: "i < dim_vec (- b)"
        using i by simp
      have comp: "(- (A *\<^sub>v x)) $ i \<le> (- b) $ i"
        using m i lt2 unfolding less_eq_vec_def by blast
      then show ?thesis
        using e1 e2 by (simp add: neg_le_iff_le)
    qed
    show ?case
    proof (rule eq_vecI)
      fix i
      assume i: "i < dim_vec b"
      show "(A *\<^sub>v x) $ i = b $ i"
        by (rule order_antisym[OF upper[OF i] lower[OF i]])
    next
      show "dim_vec (A *\<^sub>v x) = dim_vec b"
        by (rule dims)
    qed
  qed
qed

lemma face_is_polyhedron':
   fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
 fixes b
 assumes A: "A \<in> carrier_mat nr n"
 assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
 assumes "(A', b') = sub_system A b I'"
  assumes " F = {x.  x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'}"
  shows "F = polyhedron (A' @\<^sub>r (-A')) (b' @\<^sub>v (-b'))" 
        "dim_row (A' @\<^sub>r (-A')) = dim_vec (b' @\<^sub>v (-b'))"
        "dim_col (A' @\<^sub>r (-A')) = n"
  unfolding polyhedron_def
proof(safe)
  show "\<And>x. x \<in> F \<Longrightarrow> x \<in> carrier_vec n" 
    using assms(5) by blast
 have "dim_col A' = n" using dim_col_subsyst_mat A 
  proof -
    have A'_eq: "A' = fst (sub_system A b I')"
      by (simp add: assms(4)[symmetric])
    have "dim_col A' = dim_col (fst (sub_system A b I'))"
      by (simp add: A'_eq)
    also have "\<dots> = dim_col A"
      by (simp add: dim_col_subsyst_mat)
    also have "\<dots> = n"
      by (rule carrier_matD(2)[OF A])
    finally show ?thesis .
  qed
    then have 1:"A' \<in> carrier_mat (dim_row A') n" 
      by blast
    then have 2:"- A' \<in> carrier_mat (dim_row A') n" 
      using uminus_carrier_mat by blast
    have 3:" b' \<in> carrier_vec (dim_row A')"  
      proof -
    have dim_Ab: "dim_row A = dim_vec b"
      using carrier_matD(1)[OF A] carrier_vecD[OF b] by simp
    have rows: "dim_row A' = dim_vec b'"
      using dims_subsyst_same' dim_Ab assms(4) by blast
    have "dim_vec b' = dim_row A'"
      using rows by simp
    then show ?thesis
      unfolding carrier_dim_vec by simp
  qed
  show "\<And>x. x \<in> F \<Longrightarrow> (A' @\<^sub>r - A') *\<^sub>v x \<le> b' @\<^sub>v - b'" 
  proof -
    fix x 
    assume "x \<in> F" 
    have "dim_col A' = n" using dim_col_subsyst_mat A 
  proof -
    have A'_eq: "A' = fst (sub_system A b I')"
      by (simp add: assms(4)[symmetric])
    have "dim_col A' = dim_col (fst (sub_system A b I'))"
      by (simp add: A'_eq)
    also have "\<dots> = dim_col A"
      by (simp add: dim_col_subsyst_mat)
    also have "\<dots> = n"
      by (rule carrier_matD(2)[OF A])
    finally show ?thesis .
  qed
    have 4:"x \<in> carrier_vec n" using `x \<in> F` assms(5) by blast
    have "A' *\<^sub>v x \<le> b' \<and> (-A') *\<^sub>v x \<le> - b'" using eq_system_is_leq_system 
      using \<open>dim_col A' = n\<close> \<open>x \<in> F\<close> assms(5) carrier_vecD by blast
    then show "(A' @\<^sub>r - A') *\<^sub>v x \<le> b' @\<^sub>v - b'" 
      using append_rows_le[of A' "dim_row A'" n "-A'" "dim_row A'" b' x "-b'"]  
      1 2 3 4 
      by blast
  qed
  {
  fix x
  assume "x \<in> carrier_vec n" "(A' @\<^sub>r - A') *\<^sub>v x \<le> b' @\<^sub>v - b'"
  then have  "A' *\<^sub>v x \<le> b' \<and> (-A') *\<^sub>v x \<le> - b'" 
      using "1" "2" "3" append_rows_le by blast
    then have "A' *\<^sub>v x = b'" using eq_system_is_leq_system[of x A' b'] 
      using \<open>dim_col A' = n\<close> \<open>x \<in> carrier_vec n\<close> carrier_vecD by blast
  then show "x \<in> F" 
    using \<open>x \<in> carrier_vec n\<close> assms(5) by blast
}
  show "dim_row (A' @\<^sub>r (-A')) = dim_vec (b' @\<^sub>v (-b'))" 
  proof -
    have b'_dim: "dim_vec b' = dim_row A'"
      by (rule carrier_vecD[OF 3])
    have "dim_row (A' @\<^sub>r (- A')) = dim_row A' + dim_row (- A')"
      unfolding append_rows_def by simp
    also have "\<dots> = dim_vec b' + dim_vec (- b')"
      using b'_dim by simp
    also have "\<dots> = dim_vec (b' @\<^sub>v (- b'))"
      by simp
    finally show ?thesis .
  qed
  show "dim_col (A' @\<^sub>r (-A')) = n" 
    by (meson "1" "2" carrier_append_rows carrier_matD(2))
qed

lemma eq_polyhedron_neg_indices:
   fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
 fixes b
 assumes A: "A \<in> carrier_mat nr n"
 assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
 assumes "(A', b') = sub_system A b I'"
 assumes " F = {x.  x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'}"
 assumes "i < dim_row (A' @\<^sub>r (-A'))"
 obtains j where "j < dim_row (A' @\<^sub>r (-A'))"
                 "row (A' @\<^sub>r (-A')) i = - (row (A' @\<^sub>r (-A')) j)"
                 "(b' @\<^sub>v (-b')) $ i = - ((b' @\<^sub>v (-b')) $ j)"
proof(cases "i < dim_row A'")
  case True
  have "row (A' @\<^sub>r (-A')) i = row A' i" 
    by (meson True append_rows_nth(1) carrier_matI uminus_carrier_mat)
  have "i < dim_vec b'" using True assms(4) A b 
  proof -
    have dim_Ab: "dim_row A = dim_vec b"
      using carrier_matD(1)[OF A] carrier_vecD[OF b] by simp
    have dims: "dim_row A' = dim_vec b'"
      using dims_subsyst_same' dim_Ab assms(4) by blast
    then show ?thesis
      using True by simp
  qed
  then have "(b' @\<^sub>v (-b')) $ i = b' $ i" using index_append_vec 
proof -
  have dim_Ab: "dim_row A = dim_vec b"
    using carrier_matD(1)[OF A] carrier_vecD[OF b] by simp
  have rows: "dim_row A' = dim_vec b'"
    using dims_subsyst_same' dim_Ab assms(4) by blast
  have i_lt: "i < dim_vec b'"
    using True rows by simp
  have i_app: "i < dim_vec b' + dim_vec (- b')"
  proof -
    have "dim_vec (b' @\<^sub>v - b') = dim_vec b' + dim_vec (- b')"
      by (rule index_append_vec(2))
    then show ?thesis
      using i_lt by linarith
  qed
  have "(b' @\<^sub>v - b') $ i
          = (if i < dim_vec b' then b' $ i else (- b') $ (i - dim_vec b'))"
    by (rule index_append_vec(1)[OF i_app])
  then show ?thesis
    using i_lt by simp
qed
  let ?i' = "i + dim_row A'"
  have "row (A' @\<^sub>r (-A')) ?i' = row (-A') i" using append_rows_nth(2) 
    proof -
  have carr1: "A' \<in> carrier_mat (dim_row A') (dim_col A')"
    unfolding carrier_mat_def by simp
  have carr2: "- A' \<in> carrier_mat (dim_row A') (dim_col A')"
    unfolding carrier_mat_def by simp
  have ge: "dim_row A' \<le> i + dim_row A'"
    by simp
  have lt: "i + dim_row A' < dim_row A' + dim_row A'"
    using True by simp
  have "row (A' @\<^sub>r (- A')) (i + dim_row A')
          = row (- A') (i + dim_row A' - dim_row A')"
    using append_rows_nth(2)[OF carr1 carr2 ge lt] by simp
  then show ?thesis
    by simp
  qed
  then have 2:"row (A' @\<^sub>r (-A')) i = - (row (A' @\<^sub>r (-A')) ?i')" 
  proof -
  note i'_row = \<open>row (A' @\<^sub>r (- A')) ?i' = row (- A') i\<close>
  note i_row = \<open>row (A' @\<^sub>r (- A')) i = row A' i\<close>
  have neg: "row (- A') i = - row A' i"
    using True by (simp add: row_uminus)
  have "- (row (A' @\<^sub>r (- A')) ?i') = - (- row A' i)"
    by (simp only: i'_row neg)
  also have "\<dots> = row A' i"
    by (rule uminus_uminus_vec)
  also have "\<dots> = row (A' @\<^sub>r (- A')) i"
    by (simp only: i_row)
  finally show ?thesis
    by (rule sym)
  qed  have "?i' = i + dim_vec b'"
    proof -
      have dimAb: "dim_row A = dim_vec b"
        using carrier_matD(1)[OF A] carrier_vecD[OF b] by simp
      have "dim_row A' = dim_vec b'"
        using dims_subsyst_same' dimAb assms(4) by blast
      then show ?thesis by simp
    qed
  then have "(b' @\<^sub>v (-b')) $ ?i' = - b' $ i" 
    by (simp add: \<open>i < dim_vec b'\<close>)
  then have 1:"(b' @\<^sub>v (-b')) $ i = - ((b' @\<^sub>v (-b')) $ ?i')" 
    using R.minus_minus \<open>(b' @\<^sub>v - b') $ i = b' $ i\<close> by presburger
  have "?i' < dim_row (A' @\<^sub>r (-A'))" 
    using A True \<open>i + dim_row A' = i + dim_vec b'\<close> assms(4) b face_is_polyhedron'(2) by auto
  then show ?thesis 
    using 1 2 that by blast
next
  case False
  have 1:"i \<ge> dim_row A'" using False by auto 
  have 2:"i < dim_row A' + dim_row (-A')" 
  proof -
    have "dim_row (A' @\<^sub>r (-A')) = dim_row A' + dim_row (-A')"
      unfolding append_rows_def by simp
    then show "i < dim_row A' + dim_row (-A')"
      using assms(6) by simp
  qed
  let ?i' = "i - dim_row A'"
  have "row (A' @\<^sub>r (-A')) i = row (-A') ?i'" 
    using append_rows_nth(2)[of A' "dim_row A'" _ "-A'" "dim_row (-A')" i] 
    proof -
      have cA': "A' \<in> carrier_mat (dim_row A') (dim_col A')"
        by (rule carrier_mat_triv)
      have cmA': "- A' \<in> carrier_mat (dim_row (- A')) (dim_col A')"
        by (rule carrier_matI) simp_all
      have app: "A' @\<^sub>r - A' \<in> carrier_mat (dim_row A' + dim_row (- A')) (dim_col A')"
        by (rule carrier_append_rows[OF cA' cmA'])
      have i_lt: "i < dim_row A' + dim_row (- A')"
        using assms(6) carrier_matD(1)[OF app] by simp
      have not_lt: "dim_row A' \<le> i"
        using False by simp
      show ?thesis
        by (rule append_rows_nth(2)[OF cA' cmA' not_lt i_lt])
    qed
  then have 3:"row (A' @\<^sub>r (-A')) i = - (row (A' @\<^sub>r (-A')) ?i')" 
    proof -
      have carrA': "A' \<in> carrier_mat (dim_row A') (dim_col A')"
        by (rule carrier_mat_triv)
      have carrA'': "- A' \<in> carrier_mat (dim_row A') (dim_col A')"
        using carrA' uminus_carrier_mat by blast
      have i_lt2: "i < dim_row A' + dim_row A'"
        using 2 by simp
      have lt: "i - dim_row A' < dim_row A'"
        using 1 i_lt2 by (simp add: less_diff_conv2)
      have lt2: "i - dim_row A' < dim_row A' + dim_row A'"
        using lt by (rule trans_less_add1)
      have row_i: "row (A' @\<^sub>r - A') i = row (- A') (i - dim_row A')"
        by (rule append_rows_nth(2)[OF carrA' carrA'' 1 i_lt2])
      have row_k: "row (A' @\<^sub>r - A') (i - dim_row A') = row A' (i - dim_row A')"
        by (rule append_rows_nth(1)[OF carrA' carrA'' lt])
      have neg: "row (- A') (i - dim_row A') = - row A' (i - dim_row A')"
        using lt by (simp add: row_uminus)
      show ?thesis
        by (simp add: row_i row_k neg)
    qed
  have "?i' = i - dim_vec b'"
  proof -
    have dimAb: "dim_row A = dim_vec b"
      using carrier_matD(1)[OF A] carrier_vecD[OF b] by simp
    have eq: "dim_row A' = dim_vec b'"
      using dims_subsyst_same' dimAb assms(4) by blast
    show ?thesis
      by (simp add: eq)
  qed
  then have "(b' @\<^sub>v (-b')) $ i = - b' $ ?i'" 
  proof -
    have dimAb: "dim_row A = dim_vec b"
      using carrier_matD(1)[OF A] carrier_vecD[OF b] by simp
    have dims: "dim_row A' = dim_vec b'"
      using dims_subsyst_same' dimAb assms(4) by blast
    have ge': "dim_vec b' \<le> i"
      using 1 dims by simp
    have lt': "i < dim_vec b' + dim_vec b'"
      using 2 dims by simp
    have ncond: "\<not> i < dim_vec b'"
      using ge' by linarith
    have app: "(b' @\<^sub>v - b') $ i =
                 (if i < dim_vec b' then b' $ i else (- b') $ (i - dim_vec b'))"
    proof (rule index_append_vec(1))
      show "i < dim_vec b' + dim_vec (- b')"
        using lt' by simp
    qed
    have step1: "(b' @\<^sub>v - b') $ i = (- b') $ (i - dim_vec b')"
      using app by (simp add: ncond)
    have lt2: "i - dim_vec b' < dim_vec b'"
      using lt' by (simp add: less_diff_conv2[OF ge'])
    have step2: "(- b') $ (i - dim_vec b') = - (b' $ (i - dim_vec b'))"
      by (rule index_uminus_vec(1)[OF lt2])
    have "(b' @\<^sub>v - b') $ i = - (b' $ (i - dim_vec b'))"
      using step1 step2 by simp
    then show ?thesis
      using dims by simp
  qed
  then have "(b' @\<^sub>v (-b')) $ i = - ((b' @\<^sub>v (-b')) $ ?i')" 
  proof -
    have dimAb: "dim_row A = dim_vec b"
      using carrier_matD(1)[OF A] carrier_vecD[OF b] by simp
    have dim_eq: "dim_row A' = dim_vec b'"
      using dims_subsyst_same' dimAb assms(4) by blast
    have le_i: "dim_vec b' \<le> i"
      using 1 dim_eq by simp
    have i_lt2: "i < dim_vec b' + dim_vec b'"
      using 2 dim_eq by simp
    have sub_lt: "i - dim_vec b' < dim_vec b'"
      using less_diff_conv2[OF le_i] i_lt2 by simp
    have sub_lt': "i - dim_vec b' < dim_vec b' + dim_vec (- b')"
      by (rule trans_less_add1[OF sub_lt])
    have i_big: "i < dim_vec b' + dim_vec (- b')"
      using i_lt2 by simp
    have not_lt: "\<not> i < dim_vec b'"
      using le_i by simp
    have idx: "(b' @\<^sub>v - b') $ i = (- b') $ (i - dim_vec b')"
      using index_append_vec(1)[OF i_big] not_lt by simp
    have neg_idx: "(- b') $ (i - dim_vec b') = - (b' $ (i - dim_vec b'))"
      using sub_lt by simp
    have idx2: "(b' @\<^sub>v - b') $ (i - dim_vec b') = b' $ (i - dim_vec b')"
      using index_append_vec(1)[OF sub_lt'] sub_lt by simp
    have i_eq: "i - dim_row A' = i - dim_vec b'"
      using dim_eq by simp
    show ?thesis
      by (simp only: i_eq idx idx2 neg_idx)
  qed
  then show ?thesis 
    by (rule that[OF le_less_trans[OF diff_le_self assms(6)] 3])
qed

lemma subset_is_face:
  assumes "face P F"
  assumes "face P F'"
  assumes "F' \<subseteq> F" 
  shows "face F F'" 
proof -
  have "F \<subseteq> P" using assms(1) 
    by (simp add: face_subset_polyhedron)
  obtain \<alpha> \<beta> where \<alpha>_\<beta>:"valid_ineq P \<alpha> \<beta> \<and> F = P \<inter> {x |x. \<alpha> \<bullet> x = \<beta>} \<and> F \<noteq> {}"
    using assms(1) 
    by (blast elim: faceE') 
 obtain \<gamma> \<delta> where \<gamma>_\<delta>:"valid_ineq P \<gamma> \<delta> \<and> F' = P \<inter> {x |x. \<gamma> \<bullet> x = \<delta>} \<and> F' \<noteq> {}"
   using assms(2)
   by (blast elim: faceE') 
  have "F' = F' \<inter> {x |x. \<alpha> \<bullet> x = \<beta>}" 
    using \<alpha>_\<beta> assms(3) by blast
  then have "F' = P \<inter> {x |x. \<gamma> \<bullet> x = \<delta>} \<inter> {x |x. \<alpha> \<bullet> x = \<beta>}" 
    using \<gamma>_\<delta> by fastforce
  then have "F' = F \<inter> {x |x. \<gamma> \<bullet> x = \<delta>}" 
    using \<alpha>_\<beta> by fastforce
  have "valid_ineq F \<gamma> \<delta>" 
    using \<open>F \<subseteq> P\<close> \<gamma>_\<delta> by blast
  then show "face F F'" 
    using \<open>F' = F \<inter> {x |x. \<gamma> \<bullet> x = \<delta>}\<close> \<gamma>_\<delta> by blast
qed
 
lemma char_min_face2:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
 fixes b
 assumes A: "A \<in> carrier_mat nr n"
 assumes b: "b \<in> carrier_vec nr"
 defines "P \<equiv> polyhedron A b"
 assumes " F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'}" 
 assumes "(A', b') = sub_system A b I'"
 assumes "F \<subseteq> P"
 assumes "F \<noteq> {}"
 shows "min_face P F"
proof 
  have "F = {x. A' *\<^sub>v x = b' \<and> x \<in> P}" 
    using  assms(4) assms(6)
    unfolding P_def polyhedron_def
    by blast
  then show "face P F" using char_face2 
    using A P_def assms(5) assms(7) b by blast
  show "\<not> (\<exists>F'\<subset>F. face P F')" 
  proof(rule ccontr)
    assume "\<not> \<not> (\<exists>F'\<subset>F. face P F')"
    then obtain F' where "F'\<subset>F \<and> face P F'" 
      by presburger
    then have "face F F'" 
      by (meson \<open>face P F\<close> subset_is_face psubset_imp_subset)
    obtain C d where C_d:"F = polyhedron C d" "C = (A' @\<^sub>r (-A'))" "d = (b' @\<^sub>v (-b'))"
      using P_def \<open>face P F\<close> face_is_polyhedron' 
      using A assms(4) assms(5) b 
      by algebra
    then have "face (polyhedron C d) F'" using `face F F'` 
      by presburger
    have 1:"dim_row C = dim_vec d"
      using P_def \<open>face P F\<close> face_is_polyhedron'(2) 
      using A assms(4) assms(5) b  
      using \<open>C = A' @\<^sub>r - A'\<close> \<open>d = b' @\<^sub>v - b'\<close> by blast
    have "F = {x. x \<in> carrier_vec n \<and> C *\<^sub>v x \<le> d }"
      using `F = polyhedron C d` unfolding polyhedron_def 
      by blast 
    have "C \<in> carrier_mat (dim_vec d) n"  
 using P_def \<open>face P F\<close> face_is_polyhedron'(3) 
      using A assms(4) assms(5) b  
      using \<open>C = A' @\<^sub>r - A'\<close> \<open>d = b' @\<^sub>v - b'\<close> 
      using \<open>dim_row C = dim_vec d\<close> by blast
    have "d \<in> carrier_vec (dim_vec d)" 
      using carrier_vec_dim_vec by blast
    obtain C' d' I'' where C'_d':"((C', d') = sub_system C d I'')" "F' = {x. C' *\<^sub>v x = d' \<and> x \<in> F}"
      using char_face1[of C "dim_vec d" d F']
      using `F = polyhedron C d`
        `face (polyhedron C d) F'`
       `C \<in> carrier_mat (dim_vec d) n` `d \<in> carrier_vec (dim_vec d)` 
      by blast 
     obtain x where "x \<in> F - F'" 
      using \<open>F' \<subset> F \<and> face P F'\<close> by blast
    then have x:"\<not> (C' *\<^sub>v x = d') \<and>  x \<in> carrier_vec n \<and> C *\<^sub>v x \<le> d" 
  by (auto simp: P_def \<open>F = {x. x \<in> carrier_vec n \<and> C *\<^sub>v x \<le> d }\<close> \<open>F' = {x. C'*\<^sub>v x = d' \<and> x \<in> F}\<close>
          gram_schmidt.polyhedron_def)
  then obtain i where i: "i < dim_row C' \<and> \<not> (row C' i \<bullet> x = d' $ i)"
    using index_mult_mat_vec 
  proof -
    have neq: "C' *\<^sub>v x \<noteq> d'"
      using x by blast
    have dimC: "dim_row C = dim_vec d"
      using \<open>C \<in> carrier_mat (dim_vec d) n\<close> by (rule carrier_matD(1))
    have dims: "dim_row C' = dim_vec d'"
      using dims_subsyst_same' dimC C'_d'(1) by blast
    have "\<exists>i. i < dim_row C' \<and> row C' i \<bullet> x \<noteq> d' $ i"
    proof (rule ccontr)
      assume "\<not> (\<exists>i. i < dim_row C' \<and> row C' i \<bullet> x \<noteq> d' $ i)"
      then have all_eq: "\<And>i. i < dim_row C' \<Longrightarrow> row C' i \<bullet> x = d' $ i"
        by blast
      have "C' *\<^sub>v x = d'"
      proof (rule eq_vecI)
        fix i
        assume "i < dim_vec d'"
        then have i: "i < dim_row C'"
          using dims by simp
        have "(C' *\<^sub>v x) $ i = row C' i \<bullet> x"
          by (rule index_mult_mat_vec[OF i])
        also have "\<dots> = d' $ i"
          by (rule all_eq[OF i])
        finally show "(C' *\<^sub>v x) $ i = d' $ i" .
      next
        show "dim_vec (C' *\<^sub>v x) = dim_vec d'"
          using dims by simp
      qed
      with neq show False by simp
    qed
    then show thesis
      using that by blast
  qed
  then obtain j where j:"j < dim_row C \<and>  row C' i = row C j \<and> d' $ i = d $ j" 
    using exist_index_in_A
  proof -
    have i_row: "i < dim_row C'"
      using i by blast
    have sub_eq: "sub_system C d I'' = (C', d')"
      by (rule C'_d'(1)[symmetric])
    have fst_eq: "fst (sub_system C d I'') = C'"
      by (simp add: sub_eq)
    have snd_eq: "snd (sub_system C d I'') = d'"
      by (simp add: sub_eq)
    have dims0: "dim_row (fst (sub_system C d I'')) = dim_vec (snd (sub_system C d I''))"
      by (rule dims_subsyst_same[OF \<open>dim_row C = dim_vec d\<close>])
    have dims': "dim_row C' = dim_vec d'"
      using dims0 by (simp only: fst_eq snd_eq)
    have i_lt: "i < dim_vec (snd (sub_system C d I''))"
      using i_row dims' snd_eq by simp
    obtain k where k_lt: "k < dim_vec d"
      and k_row: "row (fst (sub_system C d I'')) i = row C k"
      and k_val: "snd (sub_system C d I'') $ i = d $ k"
      using exist_index_in_A[OF \<open>dim_row C = dim_vec d\<close> i_lt] by blast
    have k1: "k < dim_row C"
      using k_lt \<open>dim_row C = dim_vec d\<close> by simp
    have k2: "row C' i = row C k"
      using k_row by (simp only: fst_eq)
    have k3: "d' $ i = d $ k"
      using k_val by (simp only: snd_eq)
    have "k < dim_row C \<and> row C' i = row C k \<and> d' $ i = d $ k"
      using k1 k2 k3 by blast
    then show thesis
      by (rule that)
  qed
  have "\<not> (row C j \<bullet> x = d $ j)" 
    using \<open>j < dim_row C \<and> row C' i = row C j \<and> d' $ i = d $ j\<close> i by presburger
  then obtain j' where j :"j < dim_row C" "row C j = - (row C j')" "d $ j = - (d $ j')"
  proof -
    have j_lt: "j < dim_row (A' @\<^sub>r - A')"
      using j C_d(2) by simp
    obtain k where
      k_lt: "k < dim_row (A' @\<^sub>r - A')" and
      k_row: "row (A' @\<^sub>r - A') j = - (row (A' @\<^sub>r - A') k)" and
      k_val: "(b' @\<^sub>v - b') $ j = - ((b' @\<^sub>v - b') $ k)"
      by (rule eq_polyhedron_neg_indices[OF A b assms(5) assms(4) j_lt])
    show thesis
    proof (rule that[of k])
      show "j < dim_row C"
        using j_lt C_d(2) by simp
      show "row C j = - (row C k)"
        unfolding C_d(2) by (rule k_row)
      show "d $ j = - (d $ k)"
        unfolding C_d(3) by (rule k_val)
    qed
  qed
  have "x \<in>  carrier_vec n \<and> C *\<^sub>v x \<le> d"     
    by (simp add: x)
  then have "row C j \<bullet> x \<le> d $ j \<and> row C j' \<bullet> x \<le> d $ j'" 
    using A C_d j 1
  proof -
  have Cxd: "C *\<^sub>v x \<le> d"
    using x by blast
  have dims: "dim_row C = dim_vec d"
    using Cxd by (simp add: less_eq_vec_def)
  have le: "row C m \<bullet> x \<le> d $ m" if m: "m < dim_row C" for m
  proof -
    have m_d: "m < dim_vec d"
      using m dims by simp
    have "row C m \<bullet> x = (C *\<^sub>v x) $ m"
      by (rule index_mult_mat_vec[OF m, symmetric])
    also have "\<dots> \<le> d $ m"
      by (rule lesseq_vecD[OF carrier_vec_dim_vec Cxd m_d])
    finally show ?thesis .
  qed
  have first: "row C j \<bullet> x \<le> d $ j"
    by (rule le[OF j(1)])
  have j_lt: "j < dim_row (A' @\<^sub>r (- A'))"
    using j(1) C_d(2) by simp
  obtain k where k1: "k < dim_row (A' @\<^sub>r (- A'))"
    and k2: "row (A' @\<^sub>r (- A')) j = - row (A' @\<^sub>r (- A')) k"
    and k3: "(b' @\<^sub>v (- b')) $ j = - ((b' @\<^sub>v (- b')) $ k)"
    by (rule eq_polyhedron_neg_indices[OF A b assms(5) assms(4) j_lt])
  have k_lt: "k < dim_row C"
    using k1 C_d(2) by simp
  have rowk: "row C j = - row C k"
    using k2 C_d(2) by simp
  have dk: "d $ j = - (d $ k)"
    using k3 C_d(3) by simp
  have rj: "row C j' = row C k"
  proof -
    have "row C j' = - (- row C j')"
      by (simp add: uminus_uminus_vec)
    also have "\<dots> = - (row C j)"
      by (simp add: j(2))
    also have "\<dots> = - (- row C k)"
      by (simp add: rowk)
    also have "\<dots> = row C k"
      by (simp add: uminus_uminus_vec)
    finally show ?thesis .
  qed
  have dj: "d $ j' = d $ k"
    using j(3) dk by simp
  have second: "row C j' \<bullet> x \<le> d $ j'"
    using le[OF k_lt] rj dj by simp
  show ?thesis
    by (rule conjI[OF first second])
  qed
  then have "row C j \<bullet> x \<le> d $ j \<and> - (row C j) \<bullet> x \<le> - d $ j"
  proof -
    note prev = \<open>row C j \<bullet> x \<le> d $ j \<and> row C j' \<bullet> x \<le> d $ j'\<close>
    have c1: "row C j \<bullet> x \<le> d $ j"
      using prev by (rule conjunct1)
    have c2: "row C j' \<bullet> x \<le> d $ j'"
      using prev by (rule conjunct2)
    have row_eq: "- (row C j) = row C j'"
      by (simp add: j(2) uminus_uminus_vec)
    have d_eq: "- d $ j = d $ j'"
      by (simp add: j(3))
    have c2': "- (row C j) \<bullet> x \<le> - d $ j"
      unfolding row_eq d_eq by (rule c2)
    show ?thesis
      by (rule conjI[OF c1 c2'])
  qed
  then have "row C j \<bullet> x \<le> d $ j \<and>  (row C j) \<bullet> x \<ge>  d $ j"
  proof -
    note prev = \<open>row C j \<bullet> x \<le> d $ j \<and> - (row C j) \<bullet> x \<le> - d $ j\<close>
    have le1: "row C j \<bullet> x \<le> d $ j"
      using prev by blast
    have le2: "(- (row C j)) \<bullet> x \<le> - (d $ j)"
      using prev by blast
    have xn: "x \<in> carrier_vec n"
      using \<open>x \<in> carrier_vec n \<and> C *\<^sub>v x \<le> d\<close> by blast
    have dimx: "dim_vec x = n"
      using xn by (rule carrier_vecD)
    have dimC: "dim_col C = n"
      using \<open>C \<in> carrier_mat (dim_vec d) n\<close> by (rule carrier_matD(2))
    have dimrow: "dim_vec (row C j) = n"
      using dimC by simp
    have neg: "(- (row C j)) \<bullet> x = - (row C j \<bullet> x)"
    proof -
      have "(- (row C j)) \<bullet> x = (\<Sum>i = 0..<dim_vec x. (- (row C j)) $ i * x $ i)"
        by (simp add: scalar_prod_def)
      also have "\<dots> = (\<Sum>i = 0..<dim_vec x. - (row C j $ i * x $ i))"
      proof (intro sum.cong refl)
        fix i
        assume "i \<in> {0..<dim_vec x}"
        then have "i < dim_vec (row C j)"
          using dimx dimrow by simp
        then show "(- (row C j)) $ i * x $ i = - (row C j $ i * x $ i)"
          by simp
      qed
      also have "\<dots> = - (\<Sum>i = 0..<dim_vec x. row C j $ i * x $ i)"
        by (simp add: sum_negf)
      also have "\<dots> = - (row C j \<bullet> x)"
        by (simp add: scalar_prod_def)
      finally show ?thesis .
    qed
    have ge: "d $ j \<le> row C j \<bullet> x"
      using le2 by (simp add: neg)
    show ?thesis
      using le1 ge by (rule conjI)
  qed
    then have "row C j \<bullet> x = d $ j" 
      using nle_le by blast
    then show False 
      by (simp add: \<open>row C j \<bullet> x \<noteq> d $ j\<close>)
  qed
qed

lemma char_min_face:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
 assumes A: "A \<in> carrier_mat nr n"
 assumes b: "b \<in> carrier_vec nr"
 defines "P \<equiv> polyhedron A b"
 shows "min_face P F \<longleftrightarrow> F \<subseteq> P \<and> F \<noteq> {} \<and> 
        (\<exists> A' b' I'. (A', b') = sub_system A b I' \<and> F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'})"
proof (rule iffI)
  assume mf: "min_face P F"
  have fc: "face P F"
    by (rule min_face_elim(1)[OF mf])
  have ne: "F \<noteq> {}"
    by (rule face_non_empty[OF fc])
  have sub: "F \<subseteq> P"
    by (rule face_subset_polyhedron[OF fc])
  obtain A1 b1 I1 where
      F_eq: "F = {x. x \<in> carrier_vec n \<and> A1 *\<^sub>v x = b1}" and
      sys: "(A1, b1) = sub_system A b I1"
    by (rule char_min_face1[OF A b mf[unfolded P_def]])
  have ex: "\<exists>A' b' I'. (A', b') = sub_system A b I' \<and>
                       F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'}"
    using sys F_eq by blast
  show "F \<subseteq> P \<and> F \<noteq> {} \<and>
        (\<exists> A' b' I'. (A', b') = sub_system A b I' \<and>
                    F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'})"
    using sub ne ex by blast
next
  assume rhs: "F \<subseteq> P \<and> F \<noteq> {} \<and>
        (\<exists> A' b' I'. (A', b') = sub_system A b I' \<and>
                    F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'})"
  have sub: "F \<subseteq> P"
    using rhs by blast
  have ne: "F \<noteq> {}"
    using rhs by blast
  obtain A1 b1 I1 where
      sys: "(A1, b1) = sub_system A b I1" and
      F_eq: "F = {x. x \<in> carrier_vec n \<and> A1 *\<^sub>v x = b1}"
    using rhs by blast
  have mf2: "min_face (polyhedron A b) F"
    by (rule char_min_face2[OF A b F_eq sys sub[unfolded P_def] ne])
  show "min_face P F"
    unfolding P_def by (rule mf2)
qed

lemma face_is_polyhedron'':
   fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
 fixes b
 assumes A: "A \<in> carrier_mat nr n"
 assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
 assumes "(A', b') = sub_system A b I'"
  assumes " F = {x.  x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> A *\<^sub>v x \<le> b}"
  shows "F = polyhedron ((A' @\<^sub>r (-A')) @\<^sub>r A) ((b' @\<^sub>v (-b')) @\<^sub>v b)" 
        "dim_row ((A' @\<^sub>r (-A')) @\<^sub>r A) = dim_vec ((b' @\<^sub>v (-b')) @\<^sub>v b)"
        "dim_col ((A' @\<^sub>r (-A')) @\<^sub>r A) = n"
  unfolding polyhedron_def
proof(safe)
  show "\<And>x. x \<in> F \<Longrightarrow> x \<in> carrier_vec n" 
    using assms(5) by blast
 have "dim_col A' = n" using dim_col_subsyst_mat A 
  proof -
    have A'_eq: "fst (sub_system A b I') = A'"
      by (simp add: assms(4)[symmetric])
    have "dim_col A' = dim_col (fst (sub_system A b I'))"
      by (simp only: A'_eq)
    also have "\<dots> = dim_col A"
      by (simp add: dim_col_subsyst_mat)
    also have "\<dots> = n"
      by (rule carrier_matD(2)[OF A])
    finally show ?thesis .
  qed
    then have 1:"A' \<in> carrier_mat (dim_row A') n" 
      by blast
    then have 2:"- A' \<in> carrier_mat (dim_row A') n" 
      using uminus_carrier_mat by blast
    have 3:" b' \<in> carrier_vec (dim_row A')"  
    proof -
      have dimAb: "dim_row A = dim_vec b"
        using carrier_matD(1)[OF A] carrier_vecD[OF b] by simp
      have rows: "dim_row A' = dim_vec b'"
        using dims_subsyst_same' dimAb assms(4) by blast
      show "b' \<in> carrier_vec (dim_row A')"
        by (rule carrier_vecI[OF rows[symmetric]])
    qed
  show "\<And>x. x \<in> F \<Longrightarrow> ((A' @\<^sub>r - A') @\<^sub>r A) *\<^sub>v x \<le> (b' @\<^sub>v - b') @\<^sub>v b" 
  proof -
    fix x 
    assume "x \<in> F" 
    have "dim_col A' = n" using dim_col_subsyst_mat A 
      proof -
        have A'_eq: "A' = fst (sub_system A b I')"
          by (simp add: assms(4)[symmetric])
        have "dim_col A' = dim_col A"
          by (simp add: A'_eq dim_col_subsyst_mat)
        moreover have "dim_col A = n"
          by (rule carrier_matD(2)[OF A])
        ultimately show "dim_col A' = n"
          by simp
      qed
    have 4:"x \<in> carrier_vec n" using `x \<in> F` assms(5) by blast
    have "A' *\<^sub>v x \<le> b' \<and> (-A') *\<^sub>v x \<le> - b'" using eq_system_is_leq_system 
      using \<open>dim_col A' = n\<close> \<open>x \<in> F\<close> assms(5) carrier_vecD by blast
    then show "((A' @\<^sub>r - A') @\<^sub>r A) *\<^sub>v x \<le> (b' @\<^sub>v - b') @\<^sub>v b" 
    proof -
      have xF: "x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> A *\<^sub>v x \<le> b"
        using \<open>x \<in> F\<close> assms(5) by blast
      have Axb: "A *\<^sub>v x \<le> b"
        using xF by blast
      have A'x: "A' *\<^sub>v x = b'"
        using xF by blast
      have dimx: "dim_vec x = dim_col A'"
      proof -
        have "dim_vec x = n" using 4 by (rule carrier_vecD)
        moreover have "dim_col A' = n" using 1 by (rule carrier_matD(2))
        ultimately show ?thesis by simp
      qed
      have both: "A' *\<^sub>v x \<le> b' \<and> (- A') *\<^sub>v x \<le> - b'"
        using eq_system_is_leq_system dimx A'x by blast
      have mb': "- b' \<in> carrier_vec (dim_row A')"
        using 3 uminus_carrier_vec by blast
      have AA: "A' @\<^sub>r - A' \<in> carrier_mat (dim_row A' + dim_row A') n"
        using 1 2 carrier_append_rows by blast
      have bb: "b' @\<^sub>v - b' \<in> carrier_vec (dim_row A' + dim_row A')"
        using 3 mb' append_carrier_vec by blast
      have inner: "(A' @\<^sub>r - A') *\<^sub>v x \<le> b' @\<^sub>v - b'"
        using append_rows_le 1 2 3 4 mb' both by blast
      show "((A' @\<^sub>r - A') @\<^sub>r A) *\<^sub>v x \<le> (b' @\<^sub>v - b') @\<^sub>v b"
        using append_rows_le AA A bb b 4 inner Axb by blast
    qed
  qed
  {
  fix x
  assume "x \<in> carrier_vec n" "((A' @\<^sub>r - A') @\<^sub>r A) *\<^sub>v x \<le> (b' @\<^sub>v - b') @\<^sub>v b"
  then have  "A' *\<^sub>v x \<le> b' \<and> (-A') *\<^sub>v x \<le> - b' \<and> A *\<^sub>v x \<le> b" 
  proof -
  have xn: "x \<in> carrier_vec n"
    and le: "((A' @\<^sub>r - A') @\<^sub>r A) *\<^sub>v x \<le> (b' @\<^sub>v - b') @\<^sub>v b"
    by fact+
  have mb': "- b' \<in> carrier_vec (dim_row A')"
    using "3" uminus_carrier_vec by blast
  have AA: "A' @\<^sub>r - A' \<in> carrier_mat (dim_row A' + dim_row A') n"
    using "1" "2" by (rule carrier_append_rows)
  have bb: "b' @\<^sub>v - b' \<in> carrier_vec (dim_row A' + dim_row A')"
    using "3" mb' by (rule append_carrier_vec)
  have outer: "(((A' @\<^sub>r - A') @\<^sub>r A) *\<^sub>v x \<le> (b' @\<^sub>v - b') @\<^sub>v b) =
               ((A' @\<^sub>r - A') *\<^sub>v x \<le> b' @\<^sub>v - b' \<and> A *\<^sub>v x \<le> b)"
    using append_rows_le[of "A' @\<^sub>r - A'" "dim_row A' + dim_row A'" n A nr
                            "b' @\<^sub>v - b'" x b]
          AA A bb xn
    by blast
  have inner: "((A' @\<^sub>r - A') *\<^sub>v x \<le> b' @\<^sub>v - b') =
               (A' *\<^sub>v x \<le> b' \<and> - A' *\<^sub>v x \<le> - b')"
    using append_rows_le[of A' "dim_row A'" n "- A'" "dim_row A'" b' x "- b'"]
          "1" "2" "3" xn
    by blast
  show ?thesis
    using le outer inner by blast
  qed
    then have "A' *\<^sub>v x = b'" using eq_system_is_leq_system[of x A' b'] 
      using \<open>dim_col A' = n\<close> \<open>x \<in> carrier_vec n\<close> carrier_vecD by blast
  then show "x \<in> F" 
    using \<open>x \<in> carrier_vec n\<close> assms(5) 
    using \<open>A' *\<^sub>v x \<le> b' \<and> - A' *\<^sub>v x \<le> - b' \<and> A *\<^sub>v x \<le> b\<close> by blast
}
  show "dim_row ((A' @\<^sub>r - A') @\<^sub>r A) = dim_vec ((b' @\<^sub>v - b') @\<^sub>v b)" 
  proof -
    have rows1: "dim_row (A' @\<^sub>r - A') = dim_row A' + dim_row A'"
      by (simp add: append_rows_def)
    have rows2: "dim_row ((A' @\<^sub>r - A') @\<^sub>r A) = dim_row (A' @\<^sub>r - A') + dim_row A"
      by (simp add: append_rows_def)
    have dA: "dim_row A = nr"
      using carrier_matD(1)[OF A] by simp
    have db: "dim_vec b = nr"
      using carrier_vecD[OF b] by simp
    have db': "dim_vec b' = dim_row A'"
      using "3" carrier_vecD by blast
    have lhs: "dim_row ((A' @\<^sub>r - A') @\<^sub>r A) = dim_row A' + dim_row A' + nr"
      by (simp add: rows1 rows2 dA)
    have rhs: "dim_vec ((b' @\<^sub>v - b') @\<^sub>v b) = dim_row A' + dim_row A' + nr"
      by (simp add: db db')
    show ?thesis
      by (simp only: lhs rhs)
  qed
  show " dim_col ((A' @\<^sub>r - A') @\<^sub>r A) = n" 
    using "1" "2" carrier_append_rows carrier_matD(2) 
  proof -
    have step1: "A' @\<^sub>r - A' \<in> carrier_mat (dim_row A' + dim_row A') n"
      using "1" "2" by (rule carrier_append_rows)
    have step2: "(A' @\<^sub>r - A') @\<^sub>r A \<in> carrier_mat (dim_row A' + dim_row A' + nr) n"
      using step1 A by (rule carrier_append_rows)
    show ?thesis
      using step2 by (rule carrier_matD(2))
  qed
qed

lemma face_is_polyhedron''2:
   fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
 fixes b
 assumes A: "A \<in> carrier_mat nr n"
 assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
 assumes "(A', b') = sub_system A b I'"
  assumes " F = {x.  x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> A *\<^sub>v x \<le> b}"
  shows "F = polyhedron (A @\<^sub>r (A' @\<^sub>r (-A'))) ( b @\<^sub>v(b' @\<^sub>v (-b')))" 
        "dim_row (A @\<^sub>r(A' @\<^sub>r (-A'))) = dim_vec (b @\<^sub>v(b' @\<^sub>v (-b')))"
        "dim_col (A @\<^sub>r(A' @\<^sub>r (-A'))) = n"
proof - 
have "dim_col A' = n" using dim_col_subsyst_mat A 
    proof -
    have A'_eq: "A' = fst (sub_system A b I')"
      by (simp add: assms(4)[symmetric])
    have "dim_col A' = dim_col A"
      by (simp add: A'_eq dim_col_subsyst_mat)
    also have "\<dots> = n"
      by (rule carrier_matD(2)[OF A])
    finally show ?thesis .
  qed
    then have 1:"A' \<in> carrier_mat (dim_row A') n" 
      by blast
    then have 2:"- A' \<in> carrier_mat (dim_row A') n" 
      using uminus_carrier_mat by blast
  have "F = polyhedron ((A' @\<^sub>r (-A')) @\<^sub>r A) ((b' @\<^sub>v (-b')) @\<^sub>v b)"
    using face_is_polyhedron'' assms 
    by blast
  then show "F = polyhedron (A @\<^sub>r A' @\<^sub>r - A') (b @\<^sub>v b' @\<^sub>v - b')" 
  proof -
    have dimAb: "dim_row A = dim_vec b"
      using A b by auto
    have A'_eq: "A' = fst (sub_system A b I')"
      by (simp add: assms(4)[symmetric])
    have dc: "dim_col A' = n"
    proof -
      have "dim_col A' = dim_col (fst (sub_system A b I'))"
        by (simp add: A'_eq)
      also have "\<dots> = dim_col A"
        by (simp add: dim_col_subsyst_mat)
      also have "\<dots> = n"
        using A by (rule carrier_matD(2))
      finally show ?thesis .
    qed
    have carr_A': "A' \<in> carrier_mat (dim_row A') n"
      by (rule carrier_matI[OF refl dc])
    have carr_uA': "- A' \<in> carrier_mat (dim_row A') n"
      using carr_A' uminus_carrier_mat by blast
    have carr_app: "A' @\<^sub>r (- A') \<in> carrier_mat (dim_row A' + dim_row A') n"
      by (rule carrier_append_rows[OF carr_A' carr_uA'])
    have rows_eq: "dim_row A' = dim_vec b'"
      using dims_subsyst_same' dimAb assms(4) by blast
    have carr_b': "b' \<in> carrier_vec (dim_row A')"
      unfolding carrier_dim_vec using rows_eq by simp
    have key: "((A @\<^sub>r (A' @\<^sub>r (- A'))) *\<^sub>v x \<le> b @\<^sub>v (b' @\<^sub>v (- b'))) \<longleftrightarrow>
               (A' *\<^sub>v x = b' \<and> A *\<^sub>v x \<le> b)"
      if x: "x \<in> carrier_vec n" for x
    proof -
      have s1: "((A @\<^sub>r (A' @\<^sub>r (- A'))) *\<^sub>v x \<le> b @\<^sub>v (b' @\<^sub>v (- b'))) \<longleftrightarrow>
                (A *\<^sub>v x \<le> b \<and> (A' @\<^sub>r (- A')) *\<^sub>v x \<le> b' @\<^sub>v (- b'))"
        by (rule append_rows_le[OF A carr_app b x])
      have s2: "((A' @\<^sub>r (- A')) *\<^sub>v x \<le> b' @\<^sub>v (- b')) \<longleftrightarrow>
                (A' *\<^sub>v x \<le> b' \<and> (- A') *\<^sub>v x \<le> - b')"
        by (rule append_rows_le[OF carr_A' carr_uA' carr_b' x])
      have dimn: "dim_vec x = n"
        using x by (rule carrier_vecD)
      have dimx: "dim_vec x = dim_col A'"
        using dimn dc by simp
      have s3: "(A' *\<^sub>v x = b') \<longleftrightarrow> (A' *\<^sub>v x \<le> b' \<and> (- A') *\<^sub>v x \<le> - b')"
        by (rule eq_system_is_leq_system[OF dimx])
      show ?thesis
        using s1 s2 s3 by blast
    qed
    have F_eq: "F = {x. x \<in> carrier_vec n \<and>
                        (A @\<^sub>r (A' @\<^sub>r (- A'))) *\<^sub>v x \<le> b @\<^sub>v (b' @\<^sub>v (- b'))}"
    proof (rule Set.set_eqI)
      fix x
      have "(x \<in> F) \<longleftrightarrow> (x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> A *\<^sub>v x \<le> b)"
        using assms(5) by blast
      also have "\<dots> \<longleftrightarrow> (x \<in> carrier_vec n \<and>
                          (A @\<^sub>r (A' @\<^sub>r (- A'))) *\<^sub>v x \<le> b @\<^sub>v (b' @\<^sub>v (- b')))"
        using key by blast
      finally show "(x \<in> F) =
        (x \<in> {x. x \<in> carrier_vec n \<and>
                  (A @\<^sub>r (A' @\<^sub>r (- A'))) *\<^sub>v x \<le> b @\<^sub>v (b' @\<^sub>v (- b'))})"
        by blast
    qed
    show ?thesis
      using F_eq unfolding polyhedron_def by blast
  qed
  have "dim_row ((A' @\<^sub>r - A') @\<^sub>r A) = dim_vec ((b' @\<^sub>v - b') @\<^sub>v b)" 
    using face_is_polyhedron''(2) assms by blast
  have "dim_row ((A' @\<^sub>r - A') @\<^sub>r A) = dim_row (A @\<^sub>r (A' @\<^sub>r - A'))"
    unfolding append_rows_def 
    by (simp add: add.commute)
  have "dim_vec ((b' @\<^sub>v - b') @\<^sub>v b) =  dim_vec (b @\<^sub>v b' @\<^sub>v - b')" 
    unfolding append_vec_def 
    by (simp add: Let_def add.commute)
  then show "dim_row (A @\<^sub>r A' @\<^sub>r - A') = dim_vec (b @\<^sub>v b' @\<^sub>v - b')" 
    proof -
      have base: "dim_row ((A' @\<^sub>r - A') @\<^sub>r A) = dim_vec ((b' @\<^sub>v - b') @\<^sub>v b)"
        using face_is_polyhedron''(2) assms by blast
      have rows: "dim_row (A @\<^sub>r A' @\<^sub>r - A') = dim_row ((A' @\<^sub>r - A') @\<^sub>r A)"
        by (simp add: append_rows_def ac_simps)
      have vecs: "dim_vec ((b' @\<^sub>v - b') @\<^sub>v b) = dim_vec (b @\<^sub>v b' @\<^sub>v - b')"
        by (simp add: ac_simps)
      show ?thesis
        using rows base vecs by simp
    qed
  show "dim_col (A @\<^sub>r(A' @\<^sub>r (-A'))) = n"
    using "1" "2" carrier_append_rows carrier_matD(2) 
    using A by blast
qed

lemma face_is_polyhedron:
   fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
 fixes b
 assumes A: "A \<in> carrier_mat nr n"
 assumes b: "b \<in> carrier_vec nr"
 defines "P \<equiv> polyhedron A b"
 assumes "face P F"
 obtains A' b' where "F = polyhedron A' b'" "dim_row A' = dim_vec b'" "dim_col A' = n"
proof -
  obtain  A' b' I'  where  "(A', b') = sub_system A b I'" 
                      " F = {x.  A' *\<^sub>v x = b' \<and> x \<in> P}"
    using char_face1[of A nr b F]
    using A P_def assms(4) b by blast
  then show ?thesis using face_is_polyhedron'' 
    by (smt (verit, best) A Collect_cong P_def b gram_schmidt.polyhedron_def mem_Collect_eq that)
qed

end
end
