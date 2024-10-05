theory Faces
  imports  
    Linear_Inequalities.Decomposition_Theorem 
    Linear_Inequalities.Missing_Matrix
    LP_Duality.LP_Duality
    Jordan_Normal_Form.Matrix
    Jordan_Normal_Form.DL_Rank_Submatrix
    Subsystems
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
*)
definition
  one_vec :: "nat \<Rightarrow> 'a :: one vec" ("1\<^sub>v")
  where "1\<^sub>v n \<equiv> vec n (\<lambda> i. 1)"

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
  "support_hyp P \<alpha> \<beta> \<equiv> (\<beta> = Maximum { \<alpha> \<bullet> x | x. x \<in> P}) 
                        \<and> has_Maximum { \<alpha> \<bullet> x | x. x \<in> P} 
                        \<and> \<alpha> \<in> carrier_vec n"

definition valid_ineq where
  "valid_ineq P \<alpha> \<beta> \<equiv> (\<forall>x \<in> P. \<alpha> \<bullet> x \<le> \<beta>) \<and> \<alpha> \<in> carrier_vec n" 

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
  by (metis assms(2) eqMaximumI leI) 

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
  "face P F \<equiv> P \<noteq> {} \<and> (\<exists> \<alpha> \<beta>. F = P \<inter> {x |x. \<alpha> \<bullet> x = \<beta>} \<and> support_hyp P \<alpha> \<beta> )"

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
  apply (elim faceE)
  using support_hyp_is_valid 
  by (metis  inf.commute)

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
    by (smt (verit, best) assms(2) eqMaximumI valid_ineq_def mem_Collect_eq)
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
  using assms
  apply (induct rule: nat_induct)
   apply blast
  by (metis add_nonneg_eq_0_iff atLeastLessThan_iff less_Suc_eq 
      sum.atLeast0_lessThan_Suc sum_nonneg)

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
    by (metis assms(1-5) carrier_vecD diff_ge_0_iff_ge index_minus_vec(1) index_zero_vec(1)
        lesseq_vecD zero_le_mult_iff)
  have "y \<bullet> a = y \<bullet> b \<longleftrightarrow> y \<bullet> b - y \<bullet> a  = 0" using assms(5)  by auto
  also have "\<dots> \<longleftrightarrow> y \<bullet> (b - a) = 0" 
    by (metis assms(1-3) scalar_prod_minus_distrib)
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
    by (metis assms(3) carrier_dim_vec index_zero_vec(2) less_eq_vec_def)
  then  have "(A\<^sup>T *\<^sub>v y) \<bullet> x = y \<bullet> (A *\<^sub>v x)" 
    using transpose_vec_mult_scalar[of A nr n x y] assms(1) assms(3) 
    using assms(4) gram_schmidt.polyhedron_def by blast
  then have " \<alpha> \<bullet> x = \<beta>  \<longleftrightarrow> y \<bullet> (A *\<^sub>v x) = y \<bullet> b" 
    by (metis \<open>y \<in> carrier_vec nr\<close> assms(3) b comm_scalar_prod)
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
    by (smt (verit) A Int_iff assms(3) atLeastLessThan_iff carrier_matD(1) index_zero_vec(1)
        index_zero_vec(2) le0 less_eq_vec_def less_numeral_extra(3) mem_Collect_eq
        order_le_imp_less_or_eq)
  also have "\<dots> \<longleftrightarrow> (\<forall> i < dim_row ?A'. (row ?A' i) \<bullet> x = ?b' $ i)"
    using subsystem_fulfills_P'[of A b ?A' ?b' _ "(\<lambda> a c. a \<bullet> x = c)"] 
 using subsystem_fulfills_P[of A b ?A' ?b' _ "(\<lambda> a c. a \<bullet> x = c)"]
    by (metis (no_types, lifting) A b carrier_matD(1) carrier_vecD prod.collapse)
  also have "(\<forall> i < dim_row ?A'. (row ?A' i) \<bullet> x = ?b' $ i) \<longleftrightarrow> ?A' *\<^sub>v x = ?b'" 
    unfolding mult_mat_vec_def 
    by (smt (verit, ccfv_SIG) A b carrier_matD(1) carrier_vecD dim_vec dims_subsyst_same 
        eq_vecI index_vec)
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
    by (smt (verit, best) A P_def b face has_MinimumD(1) mem_Collect_eq)
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
  by (smt (verit, best) dim_mult_mat_vec dims_subsyst_same exist_index_in_A
       index_mult_mat_vec less_eq_vec_def mem_Collect_eq)

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
    by (metis (no_types, lifting) assms polyhedron_def subsyst_valid  prod.sel(1) prod.sel(2))
  then have "\<forall>i<dim_vec b'. (A' *\<^sub>v x) $ i \<le> b' $ i" 
    using less_eq_vec_def by blast
  show "A' *\<^sub>v x = b'"
  proof(rule ccontr)
    assume "A' *\<^sub>v x \<noteq> b'" 
    then obtain i where "i < dim_vec b'\<and> (A' *\<^sub>v x) $ i < b' $ i"
      by (metis \<open>A' *\<^sub>v x \<le> b'\<close> antisym less_eq_vec_def linorder_le_less_linear)
    then have "sum (\<lambda> i. (A' *\<^sub>v x) $ i) {0..<dim_vec b'}  < sum (\<lambda> i. b' $ i) {0..<dim_vec b'}"
      by (metis \<open>A' *\<^sub>v x \<le> b'\<close> atLeastLessThan_iff bot_nat_0.extremum carrier_vec_dim_vec
          finite_atLeastLessThan lesseq_vecD sum_strict_mono_ex1)
    then have "1\<^sub>v (dim_vec b') \<bullet> (A' *\<^sub>v x) < 1\<^sub>v (dim_vec b') \<bullet> b'"
      by (metis \<open>A' *\<^sub>v x \<le> b'\<close> carrier_vec_dim_vec less_eq_vec_def scalar_prod_left_one)
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
    by (metis A assms(4) b carrier_matD(1) carrier_matD(2) carrier_vecD dims_subsyst_same' fst_conv)
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
    by (metis (no_types, lifting) assms(3-4) polyhedron_def subsyst_valid  prod.sel(1) prod.sel(2))
  then have "\<forall> x \<in> P.  1\<^sub>v (dim_vec b') \<bullet> (A' *\<^sub>v x) \<le> 1\<^sub>v (dim_vec b') \<bullet> b'"
    by (metis (no_types, lifting) atLeastLessThan_iff carrier_vec_dim_vec 
         less_eq_vec_def scalar_prod_left_one sum_mono)
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
    by (smt (verit, ccfv_SIG) dim_subsyst_vec_less_b mem_Collect_eq snd_eqD)
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
  have "?M \<noteq> {}"  using char_face1[of A nr b F] assms
    by (smt (verit, best) Collect_cong Collect_empty_eq)
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
    by (metis surj_pair)
  then have "{x. A'' *\<^sub>v x \<le> b''} = {x. C *\<^sub>v x \<le> d \<and> row A i \<bullet> x \<le> b $ i}"
    using remove_index_sub_system assms(4) i  A \<open>dim_vec b = nr\<close> by blast
  then have "F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d \<and> row A i \<bullet> x \<le> b $ i}"
    using assms(5) by blast
  have "\<forall> x \<in> carrier_vec n. b' = A' *\<^sub>v x \<longrightarrow> row A i \<bullet> x = b $ i"
    using remove_index_sub_system_eq[of A b i I' A' b']
    by (metis (mono_tags, lifting) A \<open>dim_vec b = nr\<close> assms(3) carrier_vecD dim_mult_mat_vec i 
        mem_Collect_eq mult_mat_vec_carrier surj_pair)
  then have "F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d}" 
    using \<open>F = {x \<in> carrier_vec n. A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d \<and> row A i \<bullet> x \<le> b $ i}\<close> by fastforce
  then have "dim_vec d \<in> ?N" 
    using `(C, d) = sub_system A b (I'' - {i})` by blast
  then have "dim_vec d \<ge> dim_vec b''"
    using 2 assms(6) `(C, d) = sub_system A b (I'' - {i})`
    by auto
  have "dim_vec d + 1 = dim_vec b''"
    using \<open>(A'', b'') = sub_system A b I''\<close> \<open>(C, d) = sub_system A b (I'' - {i})\<close> 
      i remove_index_sub_system_dims 
    by (metis \<open>dim_vec b = nr\<close>)
  then have "dim_vec d < dim_vec b''" by auto
  then show False 
    using \<open>dim_vec b'' \<le> dim_vec d\<close> linorder_not_le by blast
qed

text \<open>Minimal Faces\<close>

text \<open>Minimal faces are faces that doesn't contain any other face. They are affine spaces\<close>

definition min_face where
  "min_face P F \<equiv> face P F \<and> (\<nexists> F'. F' \<subset> F \<and> face P F')"

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
      using exist_index_in_A[of A  b j I''] 
      by (metis A sub_A''(1) \<open>dim_vec b = nr\<close> carrier_matD(1) fst_conv snd_conv)
    obtain C d where sub_C: "((C, d) = sub_system A b (I'' - {i}))" 
      by (metis surj_pair)
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
        by (metis \<open>face P F\<close> equals0I gram_schmidt.face_non_empty)
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
        by (metis 1 x_n y_n minus_carrier_vec scalar_prod_smult_distrib)
      then have "row A i \<bullet> ?z = row A i \<bullet> y + (b $ i - row A i \<bullet> y)" 
        by (metis 2 1 x_n y_n nonzero_eq_divide_eq scalar_prod_minus_distrib)
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
        by (metis A carrier_matD(2) carrier_matI dim_col_subsyst_mat prod.sel(1) sub_A(1))
      then have 3:"A' *\<^sub>v ?z = b'" 
        using linear_comb_holds_eq[of A' _ n x y ?z b' ?l] 
          x y `?z = (1 - ?l) \<cdot>\<^sub>v y + ?l  \<cdot>\<^sub>v x` `?z \<in> carrier_vec n` 
        by (smt (verit, ccfv_SIG) M.add.m_comm \<open>?l \<le> 1\<close> \<open>0 < ?l\<close> divide_nonneg_pos 
            divide_nonpos_neg smult_closed zero_le_divide_iff zero_less_divide_iff 
            zero_less_one_class.zero_le_one)
      have "C \<in> carrier_mat (dim_row C) n" 
        by (metis A carrier_matD(2) carrier_mat_triv dim_col_subsyst_mat prod.sel(1) sub_C)
      then have " C *\<^sub>v ?z \<le> d" 
        using linear_comb_holds_less_eq[of C _ n x y ?z d ?l]
          x y `?z = (1 - ?l) \<cdot>\<^sub>v y + ?l  \<cdot>\<^sub>v x` `?z \<in> carrier_vec n` 
        by (simp add: M.add.m_comm  zero_le_divide_iff)
      then have "?z \<in> {x \<in> carrier_vec n. A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d \<and> row A i \<bullet> x \<le> b $ i}" 
        by (simp add: 3 4 5)
      then have "?z \<in> F" 
        using F_by_Cd by presburger
      then have "?z \<in> P" using `face P F`  
        by (metis IntE gram_schmidt.face_def)
      have "i \<notin> I" using `I \<inter> I'' \<inter> {0..<nr}= {}` 
        using \<open>i < nr \<and> i \<in> I'' \<and> row A'' j = row A i \<and> b'' $ j = b $ i\<close>
        by fastforce
      obtain C' d'  where "(C', d') = sub_system A b (I \<union> {i})" 
        by (metis surj_pair)
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
      by (metis (no_types, lifting) UNIV_eq_I dim_mult_mat_vec less_eq_vec_def
          mem_Collect_eq vec_of_dim_1) 
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
  apply safe
  using uminus_mult_mat_vec[of x A] assms 
   apply simp
  using uminus_mult_mat_vec[of x A] assms 
  apply simp
  apply (auto simp:less_eq_vec_def  order_le_imp_less_or_eq)
  apply rule
   apply (metis index_mult_mat_vec order_antisym_conv)
  by (metis dim_mult_mat_vec)

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
      by (metis assms(4) carrier_matD(2) prod.sel(1))
    then have 1:"A' \<in> carrier_mat (dim_row A') n" 
      by blast
    then have 2:"- A' \<in> carrier_mat (dim_row A') n" 
      using uminus_carrier_mat by blast
    have 3:" b' \<in> carrier_vec (dim_row A')"  
      by (metis A assms(4) b carrier_dim_vec carrier_matD(1) dims_subsyst_same')
  show "\<And>x. x \<in> F \<Longrightarrow> (A' @\<^sub>r - A') *\<^sub>v x \<le> b' @\<^sub>v - b'" 
  proof -
    fix x 
    assume "x \<in> F" 
    have "dim_col A' = n" using dim_col_subsyst_mat A 
      by (metis assms(4) carrier_matD(2) prod.sel(1))
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
    by (metis "1" "2" "3" append_carrier_vec carrier_append_rows carrier_matD(1)
 carrier_vecD uminus_carrier_vec)
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
    by (metis carrier_matD(1) carrier_vecD dims_subsyst_same')
  then have "(b' @\<^sub>v (-b')) $ i = b' $ i" using index_append_vec 
    by (metis trans_less_add1) 
  let ?i' = "i + dim_row A'"
  have "row (A' @\<^sub>r (-A')) ?i' = row (-A') i" using append_rows_nth(2) 
    by (smt (verit, ccfv_threshold) True add.commute add_diff_cancel_right'
        add_less_le_mono carrier_matI index_uminus_mat(2) index_uminus_mat(3) trans_less_add1 
        verit_comp_simplify1(2) verit_comp_simplify1(3))
  then have 2:"row (A' @\<^sub>r (-A')) i = - (row (A' @\<^sub>r (-A')) ?i')" 
    by (metis True \<open>row (A' @\<^sub>r - A') i = row A' i\<close> row_uminus uminus_uminus_vec)
  have "?i' = i + dim_vec b'"
    by (metis A assms(4) b carrier_matD(1) carrier_vecD dims_subsyst_same')
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
    by (metis (mono_tags, lifting) A assms(4) assms(6) b carrier_matD(1) carrier_vecD 
        dims_subsyst_same' face_is_polyhedron'(2) index_append_vec(2) index_uminus_mat(2) 
        index_uminus_vec(2))
  let ?i' = "i - dim_row A'"
  have "row (A' @\<^sub>r (-A')) i = row (-A') ?i'" 
    using append_rows_nth(2)[of A' "dim_row A'" _ "-A'" "dim_row (-A')" i] 
    by (metis \<open>dim_row A' \<le> i\<close> \<open>i < dim_row A' + dim_row (- A')\<close> carrier_matI index_uminus_mat(3))
  then have 3:"row (A' @\<^sub>r (-A')) i = - (row (A' @\<^sub>r (-A')) ?i')" 
    by (smt (verit, best) 1 2 append_rows_nth(1) carrier_matI index_uminus_mat(2) 
        index_uminus_mat(3) less_diff_conv2 row_uminus)
  have "?i' = i - dim_vec b'"
    by (metis A assms(4) b carrier_matD(1) carrier_vecD dims_subsyst_same')
  then have "(b' @\<^sub>v (-b')) $ i = - b' $ ?i'" 
    by (metis A False 1 2 assms(4) assms(6) b carrier_matD(1) carrier_vecD dims_subsyst_same' 
        face_is_polyhedron'(2) index_append_vec(1) index_append_vec(2) index_uminus_mat(2) 
        index_uminus_vec(1) less_diff_conv2)
  then have "(b' @\<^sub>v (-b')) $ i = - ((b' @\<^sub>v (-b')) $ ?i')" 
    by (metis A 1 2 assms(4) b carrier_matD(1) carrier_vecD dims_subsyst_same'
        index_append_vec(1) index_uminus_mat(2) less_diff_conv2 trans_less_add1)
  then show ?thesis 
    by (metis 1 3 add_lessD1 assms(6) ordered_cancel_comm_monoid_diff_class.diff_add that)
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
    by (metis C'_d'(1) \<open>C \<in> carrier_mat (dim_vec d) n\<close> carrier_matD(1) 
        dim_mult_mat_vec dims_subsyst_same' eq_vecI)
  then obtain j where j:"j < dim_row C \<and>  row C' i = row C j \<and> d' $ i = d $ j" 
    using exist_index_in_A
    by (metis C'_d'(1) \<open>dim_row C = dim_vec d\<close> dims_subsyst_same fst_conv snd_conv)
  have "\<not> (row C j \<bullet> x = d $ j)" 
    using \<open>j < dim_row C \<and> row C' i = row C j \<and> d' $ i = d $ j\<close> i by presburger
  then obtain j' where j :"j < dim_row C" "row C j = - (row C j')" "d $ j = - (d $ j')"
    using eq_polyhedron_neg_indices A \<open>C = A' @\<^sub>r - A'\<close> j assms(5) b \<open>d = b' @\<^sub>v - b'\<close> 
    by metis
  have "x \<in>  carrier_vec n \<and> C *\<^sub>v x \<le> d"     
    by (simp add: x)
  then have "row C j \<bullet> x \<le> d $ j \<and> row C j' \<bullet> x \<le> d $ j'" 
    using A C_d j 1
    by (smt (verit, best) assms(5) b eq_polyhedron_neg_indices index_mult_mat_vec less_eq_vec_def
        neg_equal_iff_equal uminus_eq_vec)
  then have "row C j \<bullet> x \<le> d $ j \<and> - (row C j) \<bullet> x \<le> - d $ j"
    by (metis j(2-3) R.minus_minus uminus_uminus_vec)
  then have "row C j \<bullet> x \<le> d $ j \<and>  (row C j) \<bullet> x \<ge>  d $ j"
    by (metis \<open>C \<in> carrier_mat (dim_vec d) n\<close> \<open>x \<in> carrier_vec n \<and> C *\<^sub>v x \<le> d\<close> carrier_matD(2) 
        carrier_vecD neg_le_iff_le row_carrier scalar_prod_uminus_left)
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
  using char_min_face1 char_min_face2 
  by (smt (verit, best) A P_def b face_non_empty face_subset_polyhedron min_face_elim(1))

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
      by (metis assms(4) carrier_matD(2) prod.sel(1))
    then have 1:"A' \<in> carrier_mat (dim_row A') n" 
      by blast
    then have 2:"- A' \<in> carrier_mat (dim_row A') n" 
      using uminus_carrier_mat by blast
    have 3:" b' \<in> carrier_vec (dim_row A')"  
      by (metis A assms(4) b carrier_dim_vec carrier_matD(1) dims_subsyst_same')
  show "\<And>x. x \<in> F \<Longrightarrow> ((A' @\<^sub>r - A') @\<^sub>r A) *\<^sub>v x \<le> (b' @\<^sub>v - b') @\<^sub>v b" 
  proof -
    fix x 
    assume "x \<in> F" 
    have "dim_col A' = n" using dim_col_subsyst_mat A 
      by (metis assms(4) carrier_matD(2) prod.sel(1))
    have 4:"x \<in> carrier_vec n" using `x \<in> F` assms(5) by blast
    have "A' *\<^sub>v x \<le> b' \<and> (-A') *\<^sub>v x \<le> - b'" using eq_system_is_leq_system 
      using \<open>dim_col A' = n\<close> \<open>x \<in> F\<close> assms(5) carrier_vecD by blast
    then show "((A' @\<^sub>r - A') @\<^sub>r A) *\<^sub>v x \<le> (b' @\<^sub>v - b') @\<^sub>v b" 
      using append_rows_le[of A' "dim_row A'" n "-A'" "dim_row A'" b' x "-b'"]  
      1 2 3 4  
      by (metis (no_types, lifting) A \<open>x \<in> F\<close> append_rows_le assms(4) assms(5) b carrier_matI 
          carrier_vec_dim_vec face_is_polyhedron'(2) face_is_polyhedron'(3) mem_Collect_eq)
  qed
  {
  fix x
  assume "x \<in> carrier_vec n" "((A' @\<^sub>r - A') @\<^sub>r A) *\<^sub>v x \<le> (b' @\<^sub>v - b') @\<^sub>v b"
  then have  "A' *\<^sub>v x \<le> b' \<and> (-A') *\<^sub>v x \<le> - b' \<and> A *\<^sub>v x \<le> b" 
    using "1" "2" "3" append_rows_le 
    by (smt (verit, ccfv_threshold) A assms(4) b carrier_matI carrier_vec_dim_vec 
        face_is_polyhedron'(2) face_is_polyhedron'(3))
    then have "A' *\<^sub>v x = b'" using eq_system_is_leq_system[of x A' b'] 
      using \<open>dim_col A' = n\<close> \<open>x \<in> carrier_vec n\<close> carrier_vecD by blast
  then show "x \<in> F" 
    using \<open>x \<in> carrier_vec n\<close> assms(5) 
    using \<open>A' *\<^sub>v x \<le> b' \<and> - A' *\<^sub>v x \<le> - b' \<and> A *\<^sub>v x \<le> b\<close> by blast
}
  show "dim_row ((A' @\<^sub>r - A') @\<^sub>r A) = dim_vec ((b' @\<^sub>v - b') @\<^sub>v b)" 
    using "1" "2" "3" append_carrier_vec carrier_append_rows carrier_matD(1) 
      carrier_vecD uminus_carrier_vec
    by (smt (verit, ccfv_SIG) A b)
  show " dim_col ((A' @\<^sub>r - A') @\<^sub>r A) = n" 
    using "1" "2" carrier_append_rows carrier_matD(2) 
    by (metis append_rows_def index_mat_four_block(3) index_zero_mat(3))
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
      by (metis assms(4) carrier_matD(2) prod.sel(1))
    then have 1:"A' \<in> carrier_mat (dim_row A') n" 
      by blast
    then have 2:"- A' \<in> carrier_mat (dim_row A') n" 
      using uminus_carrier_mat by blast
  have "F = polyhedron ((A' @\<^sub>r (-A')) @\<^sub>r A) ((b' @\<^sub>v (-b')) @\<^sub>v b)"
    using face_is_polyhedron'' assms 
    by blast
  then show "F = polyhedron (A @\<^sub>r A' @\<^sub>r - A') (b @\<^sub>v b' @\<^sub>v - b')" 
    by (smt (verit, best) A Collect_cong append_rows_le assms(4) b carrier_matI 
        carrier_vec_dim_vec face_is_polyhedron'(2) face_is_polyhedron'(3)
        gram_schmidt.polyhedron_def)
  have "dim_row ((A' @\<^sub>r - A') @\<^sub>r A) = dim_vec ((b' @\<^sub>v - b') @\<^sub>v b)" 
    using face_is_polyhedron''(2) assms by blast
  have "dim_row ((A' @\<^sub>r - A') @\<^sub>r A) = dim_row (A @\<^sub>r (A' @\<^sub>r - A'))"
    unfolding append_rows_def 
    by (simp add: add.commute)
  have "dim_vec ((b' @\<^sub>v - b') @\<^sub>v b) =  dim_vec (b @\<^sub>v b' @\<^sub>v - b')" 
    unfolding append_vec_def 
    by (metis add.commute dim_vec)
  then show "dim_row (A @\<^sub>r A' @\<^sub>r - A') = dim_vec (b @\<^sub>v b' @\<^sub>v - b')" 
    by (metis \<open>dim_row ((A' @\<^sub>r - A') @\<^sub>r A) = dim_row (A @\<^sub>r A' @\<^sub>r - A')\<close>
        \<open>dim_row ((A' @\<^sub>r - A') @\<^sub>r A) = dim_vec ((b' @\<^sub>v - b') @\<^sub>v b)\<close>)
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
