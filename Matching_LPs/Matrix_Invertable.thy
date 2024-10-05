theory Matrix_Invertable
  imports Jordan_Normal_Form.Determinant
  Smith_Normal_Form.SNF_Missing_Lemmas
begin

lemma invertible_right_inverse1:
  fixes A :: "'a::{semiring_1, comm_ring_1} mat"
  assumes "A \<in> carrier_mat n n"
  shows "invertible_mat A \<longleftrightarrow> (\<exists>B \<in> carrier_mat n n. A * B = 1\<^sub>m n)"
  by (metis (no_types, lifting) Determinant.det_mult assms det_one dvdI 
      invertible_iff_is_unit_JNF  inverts_mat_def left_mult_one_mat
      obtain_inverse_matrix one_carrier_mat similar_mat_witD(2) similar_mat_wit_refl)

lemma  invertible_det_nz1:
  fixes A::"'a::field mat"
  assumes "A \<in> carrier_mat n n"
  shows "invertible_mat A \<longleftrightarrow> det A \<noteq> 0"
proof(cases "n=0")
  case True
  then show ?thesis 
    using assms invertible_mat_zero by auto
next
  case False
  then show ?thesis 
  using invertible_det_nz[untransferred, cancel_card_constraint, of A n]
  assms 
  by fast 
qed

proposition  cramer1:
  fixes A::"'a::field mat"
  assumes "A \<in> carrier_mat n n"
  assumes "b \<in> carrier_vec n"
  assumes "x \<in> carrier_vec n"
  assumes d0: "det A \<noteq> 0"
  shows "A *\<^sub>v x = b \<longleftrightarrow> x = vec n (\<lambda> k. det (replace_col A b k) / det A)"
proof -
  from d0 obtain B where B: "B \<in> carrier_mat n n" "A * B = 1\<^sub>m n" "B * A = 1\<^sub>m n"
    unfolding invertible_det_nz1[symmetric] invertible_mat_def
    by (meson Determinant.mat_mult_left_right_inverse 
        \<open>\<And>n A. A \<in> carrier_mat n n \<Longrightarrow> (Determinant.det A \<noteq> 0) = invertible_mat A\<close> assms(1)
        invertible_right_inverse1)
  have "(A * B) *\<^sub>v b = b"
    by (simp add: B assms(2))
  then have "A *\<^sub>v (B *\<^sub>v b) = b" 
    using B(1) assms(1) assms(2) by force
  then have xe: "\<exists>x. A *\<^sub>v x = b"
    by blast
  {
    fix x
    assume x: "A *\<^sub>v x = b"
    assume "x \<in> carrier_vec n" 
    have "x = vec n (\<lambda> k. det (replace_col A b k) / det A)"
      unfolding x[symmetric]
      using d0 
      by (auto simp: vec_eq_iff cramer_lemma_mat[of A n x] field_simps assms `x \<in> carrier_vec n`)
  }
  with xe show ?thesis
    using \<open>\<And>xa. \<lbrakk>A *\<^sub>v xa = b; xa \<in> carrier_vec n\<rbrakk> \<Longrightarrow> 
          xa = Matrix.vec n (\<lambda>k. Determinant.det (replace_col A b k) / Determinant.det A)\<close> assms(3) 
    by (metis B(1) \<open>A *\<^sub>v (B *\<^sub>v b) = b\<close> assms(2) mult_mat_vec_carrier)
qed

end