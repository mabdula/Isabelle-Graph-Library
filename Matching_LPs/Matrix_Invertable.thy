(*
  Author: Ralitsa Dordjonova
  Author: Mohammad Abdulaziz
*)

theory Matrix_Invertable
  imports Jordan_Normal_Form.Determinant
  Smith_Normal_Form.SNF_Missing_Lemmas AI_Provenance.Provenance
begin

provenance human

lemma invertible_right_inverse1:
  fixes A :: "'a::{semiring_1, comm_ring_1} mat"
  assumes "A \<in> carrier_mat n n"
  shows "invertible_mat A \<longleftrightarrow> (\<exists>B \<in> carrier_mat n n. A * B = 1\<^sub>m n)"
proof \<^marker>\<open>provenance ai\<close>
  assume inv: "invertible_mat A"
  obtain B where B: "B \<in> carrier_mat n n" "inverts_mat A B" "inverts_mat B A"
    using obtain_inverse_matrix[OF assms inv] by blast
  from B(2) assms have "A * B = 1\<^sub>m n"
    by (simp add: inverts_mat_def)
  with B(1) show "\<exists>B \<in> carrier_mat n n. A * B = 1\<^sub>m n" by blast
next
  assume "\<exists>B \<in> carrier_mat n n. A * B = 1\<^sub>m n"
  then obtain B where B: "B \<in> carrier_mat n n" "A * B = 1\<^sub>m n" by blast
  have detAB: "det (A * B) = det A * det B"
    using Determinant.det_mult[OF assms B(1)] .
  have "1 = det A * det B"
    using detAB B(2) by (simp add: det_one)
  then have "det A dvd 1" by (rule dvdI)
  then show "invertible_mat A"
    using invertible_iff_is_unit_JNF[OF assms] by simp
qed

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
  proof \<^marker>\<open>provenance ai\<close> (intro iffI)
    assume "A *\<^sub>v x = b"
    then show "x = vec n (\<lambda>k. det (replace_col A b k) / det A)"
      using assms(3)
        \<open>\<And>xa. \<lbrakk>A *\<^sub>v xa = b; xa \<in> carrier_vec n\<rbrakk> \<Longrightarrow>
            xa = Matrix.vec n (\<lambda>k. Determinant.det (replace_col A b k) / Determinant.det A)\<close>
      by blast
  next
    assume h: "x = vec n (\<lambda>k. det (replace_col A b k) / det A)"
    have Bb: "B *\<^sub>v b \<in> carrier_vec n"
      using B(1) assms(2) mult_mat_vec_carrier by blast
    have eq1: "B *\<^sub>v b = vec n (\<lambda>k. det (replace_col A b k) / det A)"
      using Bb \<open>A *\<^sub>v (B *\<^sub>v b) = b\<close>
        \<open>\<And>xa. \<lbrakk>A *\<^sub>v xa = b; xa \<in> carrier_vec n\<rbrakk> \<Longrightarrow>
            xa = Matrix.vec n (\<lambda>k. Determinant.det (replace_col A b k) / Determinant.det A)\<close>
      by blast
    have "x = B *\<^sub>v b"
    proof -
      from h have "x = vec n (\<lambda>k. det (replace_col A b k) / det A)" .
      also have "... = B *\<^sub>v b" by (rule eq1[symmetric])
      finally show ?thesis .
    qed
    then have "A *\<^sub>v x = A *\<^sub>v (B *\<^sub>v b)" by simp
    also have "... = b" by (rule \<open>A *\<^sub>v (B *\<^sub>v b) = b\<close>)
    finally show "A *\<^sub>v x = b" .
  qed
qed

end