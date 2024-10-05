theory Integer_hull_f_to_a
  imports 
    Matrix_Invertable
    Faces
    Linear_Inequalities.Integer_Hull
    Linear_Inequalities.Farkas_Lemma
    Integer_Polyhedron
    Missing_Sums 
begin

context gram_schmidt
begin

no_notation inner (infix "\<bullet>" 70)
no_notation Finite_Cartesian_Product.vec.vec_nth (infixl "$" 90)

lemma integer_hull_is_integer_hull:
  assumes "P \<subseteq> carrier_vec n"
  shows "integer_hull (integer_hull P) = integer_hull P"  
proof -
  have int_in_carr: "P \<inter> \<int>\<^sub>v \<subseteq> carrier_vec n" 
    using assms by auto
  show ?thesis unfolding integer_hull_def
    apply rule
    using convex_convex_hull 
     apply (metis Int_lower1 int_in_carr convex_hull_mono convex_hulls_are_convex)
    by (simp add:int_in_carr set_in_convex_hull convex_hull_mono)
qed

lemma integer_hull_in_carrier:
  assumes "P \<subseteq> carrier_vec n"
  shows "integer_hull P \<subseteq> carrier_vec n"
proof -
   have int_in_carr: "P \<inter> \<int>\<^sub>v \<subseteq> carrier_vec n" 
     using assms by auto
   then show ?thesis 
     by (simp add: gram_schmidt.convex_hull_carrier gram_schmidt.integer_hull_def)
 qed

lemma min_face_min_subsyst:
  fixes A :: "'a  mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "min_face P F"
  obtains A' b' I'  where "((A', b') = sub_system A b I')" 
    " F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'}"
    "dim_vec b' = Min {dim_vec d| C d I. (C, d) = sub_system A b I \<and> 
                                             F = {x. x \<in> carrier_vec n \<and> C *\<^sub>v x = d}}"
proof-
  have "dim_vec b = nr" using b by auto
  let ?M = "{dim_vec d| C d I. (C, d) = sub_system A b I \<and> F = {x. x \<in> carrier_vec n \<and> C *\<^sub>v x = d}}"
  have "finite ?M"
    using subset_set_of_sub_dims_finite[of ?M A b] by blast
  have "finite ?M" using subset_set_of_sub_dims_finite[of ?M A b] by blast
  obtain A' b' I where " F \<subseteq> P \<and> F \<noteq> {} \<and>
            F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'} \<and> (A', b') = sub_system A b I"
    using char_min_face 
    using A P_def assms(4) b by auto
  then have "dim_vec b' \<in> ?M" by auto
  then have "?M \<noteq> {}"  
    by blast
  then have "Min ?M \<in> ?M \<and> (\<forall>a \<in> ?M. a \<ge> (Min ?M))"
    using eq_Min_iff[of ?M] `?M \<noteq> {}` `finite ?M`
    by auto
  then show ?thesis 
    using that by force
qed

lemma subsyst_indx_neq_syst_indx_neq:
  assumes "i1 = pick I j1"
  assumes "i2 = pick I j2"
  assumes "(A', b') = sub_system A b I"
  assumes "j1 < dim_row A'"
  assumes "j2 < dim_row A'" 
  assumes "j1 \<noteq> j2"
  shows "i1 \<noteq> i2" 
proof(cases "infinite I")
  case True
  then show ?thesis 
    using assms(1) assms(2) assms(6) pick_eq_iff_inf by blast
next
  case False
  then show ?thesis using dim_row_less_card_I[of I A b] 
    by (metis assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) fst_conv 
        not_less_iff_gr_or_eq order_less_le_trans pick_mono_le)
qed

lemma elems_ge_min:
  assumes "finite S"
  assumes "b \<in> S"
  assumes "a = Min S" 
  shows "b \<ge> a" 
  by (simp add: assms)

lemma bounded_min_faces_are_vertex:
  fixes A :: "'a  mat"
  fixes bound:: "'a" 
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "P \<noteq> {}"
  assumes "min_face P F"
  assumes bounded: "\<forall> x \<in> P. \<forall> i < n.  x $ i \<le> bound" 
  shows "card F = 1"
proof(cases "n = 0")
  case True
  have "{x |x. x \<in> carrier_vec 0} = {0\<^sub>v 0}" 
    using eq_vecI ex_in_conv  by fastforce
  then have "P = {0\<^sub>v 0}" 
    using assms(4) unfolding P_def polyhedron_def  using True by auto
  have "F = {0\<^sub>v 0}"
    using  face_subset_polyhedron[OF min_face_elim(1)[OF assms(5)]] 
      face_non_empty[OF min_face_elim(1)[OF assms(5)]]
    using \<open>P = {0\<^sub>v 0}\<close> by blast
  then show ?thesis 
    using card_eq_1_iff by blast
next
  case False
  have bound_scalar:"\<forall> x \<in> P. \<forall> i < n. unit_vec n i \<bullet> x \<le> bound"
    using bounded scalar_prod_left_unit 
    unfolding P_def polyhedron_def  
    by auto
  have "n > 0" using False by auto
  have "F \<noteq> {}" 
    using A P_def assms(5) b char_min_face by blast
  obtain \<alpha> \<beta> where \<alpha>_\<beta>:"support_hyp P \<alpha> \<beta> \<and> F = P \<inter> {x |x. \<alpha> \<bullet> x = \<beta>}"
    using assms(5)
    by (metis faceE min_face_elim(1))
  obtain C d where C_d: "F = polyhedron C d"  "dim_row C = dim_vec d" "dim_col C = n" 
    using face_is_polyhedron 
    by (metis A P_def assms(5) b min_face_elim(1))
  have "\<exists>x\<in>carrier_vec n. C *\<^sub>v x \<le> d" 
    apply (insert assms(5) char_min_face[of A nr b F])
    by(auto simp: \<open>F = polyhedron C d\<close>  A b P_def polyhedron_def)
  have "\<forall> i < n. \<exists> \<beta>\<^sub>i. \<forall>x \<in> F. x $ i = \<beta>\<^sub>i" 
  proof(safe)
    fix i
    assume "i < n" 
    have "\<forall> x \<in> F. unit_vec n i  \<bullet> x \<le> bound" 
      by (simp add: bound_scalar \<open>i < n\<close> \<alpha>_\<beta>)
    then have  "\<forall> x \<in> carrier_vec n. C *\<^sub>v x \<le> d \<longrightarrow> unit_vec n i  \<bullet> x \<le> bound"
      by (simp add: \<open>F = polyhedron C d\<close> gram_schmidt.polyhedron_def)
    then have "has_Maximum {unit_vec n i  \<bullet> x | x. x \<in> carrier_vec n \<and> C *\<^sub>v x \<le> d}"
      using strong_duality_theorem_primal_sat_bounded_min_max(2)[of C _ n d "unit_vec n i"]
        C_d `\<exists>x\<in>carrier_vec n. C *\<^sub>v x \<le> d`  unit_vec_carrier  carrier_dim_vec by blast
    then obtain \<beta>\<^sub>i where "\<beta>\<^sub>i \<in> {unit_vec n i  \<bullet> x | x. x \<in> carrier_vec n \<and> C *\<^sub>v x \<le> d} 
        \<and> \<beta>\<^sub>i = Maximum {unit_vec n i  \<bullet> x | x. x \<in> carrier_vec n \<and> C *\<^sub>v x \<le> d}" 
      using has_MaximumD(1) by blast
    then have "support_hyp F (unit_vec n i) \<beta>\<^sub>i " 
      apply(intro support_hypI)
      unfolding C_d polyhedron_def
      using \<open>has_Maximum {unit_vec n i \<bullet> x |x. x \<in> carrier_vec n \<and> C *\<^sub>v x \<le> d}\<close> by auto+
    then have "face F (F\<inter>{x |x. (unit_vec n i) \<bullet> x = \<beta>\<^sub>i})" 
      using `F \<noteq> {}` by blast
    then have "face P (F\<inter>{x |x. (unit_vec n i) \<bullet> x = \<beta>\<^sub>i})" 
      using face_trans[of A nr b F "(F\<inter>{x |x. (unit_vec n i) \<bullet> x = \<beta>\<^sub>i})"] 
        A P_def  assms(5) b min_face_elim(1) by presburger
    then have "\<forall> x \<in> F. (unit_vec n i) \<bullet> x = \<beta>\<^sub>i"
      using assms(5) unfolding min_face_def using  basic_trans_rules(17) by blast
    then show "(\<exists>\<beta>\<^sub>i. \<forall>x\<in>F. x $ i = \<beta>\<^sub>i)"
      by (simp add: C_d(1) \<open>i < n\<close> polyhedron_def)
  qed
  have "\<exists>! x. x \<in> F" 
  proof(rule ccontr)
    assume "\<nexists>!x. x \<in> F"
    then obtain x y where x_y:"x \<in> F \<and> y \<in> F \<and> x \<noteq> y" 
      using \<open>F \<noteq> {}\<close> by blast
    have "\<forall>x \<in> F. x  \<in> carrier_vec n" 
      by (metis (no_types, lifting) C_d(1) polyhedron_def mem_Collect_eq)
    then obtain i where i:"i < n \<and> x $ i \<noteq> y $ i"
      using eq_vecI x_y carrier_vecD by metis 
    have "\<exists>\<beta>\<^sub>i. \<forall>x\<in>F. x $ i = \<beta>\<^sub>i" 
      using \<open>\<forall>i<n. \<exists>\<beta>\<^sub>i. \<forall>x\<in>F. x $ i = \<beta>\<^sub>i\<close> i by presburger
    then show False 
      by (metis i x_y)
  qed
  then show "card F = 1" 
    by (metis \<open>F \<noteq> {}\<close> is_singletonI' is_singleton_altdef)
qed

lemma bounded_min_faces_are_vertex':
  fixes A :: "'a  mat"
  fixes bound:: "'a" 
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "P \<noteq> {}"
  assumes "min_face P F"
  assumes bounded: "\<forall> x \<in> P. \<forall> i < n. x $ i \<ge> bound" 
  shows "card F = 1"
proof(cases "n = 0")
  case True
  have "{x |x. x \<in> carrier_vec 0} = {0\<^sub>v 0}" 
    using eq_vecI ex_in_conv  by fastforce
  then have "P = {0\<^sub>v 0}" 
    using assms(4) unfolding P_def polyhedron_def  using True by auto
  have "F = {0\<^sub>v 0}"
    using  face_subset_polyhedron[OF min_face_elim(1)[OF assms(5)]] 
      face_non_empty[OF min_face_elim(1)[OF assms(5)]]
    using \<open>P = {0\<^sub>v 0}\<close> by blast
  then show ?thesis 
    using card_eq_1_iff by blast
next
  case False
  have bound_scalar:"\<forall> x \<in> P. \<forall> i < n. - unit_vec n i \<bullet> x \<le> - bound"
    using bounded scalar_prod_left_unit 
    unfolding P_def polyhedron_def 
    by auto
  have "n > 0" using False by auto
  have "F \<noteq> {}" 
    using A P_def assms(5) b char_min_face by blast
  obtain \<alpha> \<beta> where \<alpha>_\<beta>:"support_hyp P \<alpha> \<beta> \<and> F = P \<inter> {x |x. \<alpha> \<bullet> x = \<beta>}"
    using assms(5)
    by (metis faceE min_face_elim(1))
  obtain C d where C_d: "F = polyhedron C d"  "dim_row C = dim_vec d" "dim_col C = n" 
    using face_is_polyhedron 
    by (metis A P_def assms(5) b min_face_elim(1))
  have "\<exists>x\<in>carrier_vec n. C *\<^sub>v x \<le> d" 
    apply (insert assms(5) char_min_face[of A nr b F])
    by(auto simp: \<open>F = polyhedron C d\<close>  A b P_def polyhedron_def)
  have "\<forall> i < n. \<exists> \<beta>\<^sub>i. \<forall>x \<in> F. x $ i = \<beta>\<^sub>i" 
  proof(safe)
    fix i
    assume "i < n" 
    have "\<forall> x \<in> F. - unit_vec n i  \<bullet> x \<le> - bound" 
      by (simp add: bound_scalar \<open>i < n\<close> \<alpha>_\<beta>)
    then have  "\<forall> x \<in> carrier_vec n. C *\<^sub>v x \<le> d \<longrightarrow> - unit_vec n i  \<bullet> x \<le> - bound"
      apply (simp add: \<open>F = polyhedron C d\<close> gram_schmidt.polyhedron_def)
      by (metis neg_le_iff_le uminus_scalar_prod unit_vec_carrier)
    then have "has_Maximum {- unit_vec n i  \<bullet> x | x. x \<in> carrier_vec n \<and> C *\<^sub>v x \<le> d}"
      using strong_duality_theorem_primal_sat_bounded_min_max(2)[of C _ n d " - unit_vec n i"]
        C_d `\<exists>x\<in>carrier_vec n. C *\<^sub>v x \<le> d`  unit_vec_carrier  carrier_dim_vec 
      by (smt (verit, del_insts) carrier_matI index_uminus_vec(2))
    then obtain \<beta>\<^sub>i where "\<beta>\<^sub>i \<in> { - unit_vec n i  \<bullet> x | x. x \<in> carrier_vec n \<and> C *\<^sub>v x \<le> d} 
        \<and> \<beta>\<^sub>i = Maximum { - unit_vec n i  \<bullet> x | x. x \<in> carrier_vec n \<and> C *\<^sub>v x \<le> d}" 
      using has_MaximumD(1) by blast
    then have "support_hyp F (- unit_vec n i) \<beta>\<^sub>i " 
      apply(intro support_hypI)
      unfolding C_d polyhedron_def
      using \<open>has_Maximum { - unit_vec n i \<bullet> x |x. x \<in> carrier_vec n \<and> C *\<^sub>v x \<le> d}\<close> by auto+
    then have "face F (F\<inter>{x |x. (- unit_vec n i) \<bullet> x = \<beta>\<^sub>i})" 
      using `F \<noteq> {}` by blast
    then have "face P (F\<inter>{x |x. (- unit_vec n i) \<bullet> x = \<beta>\<^sub>i})" 
      using face_trans[of A nr b F "(F\<inter>{x |x. (- unit_vec n i) \<bullet> x = \<beta>\<^sub>i})"] 
        A P_def  assms(5) b min_face_elim(1) by presburger
    then have "\<forall> x \<in> F. (- unit_vec n i) \<bullet> x = \<beta>\<^sub>i"
      using assms(5) unfolding min_face_def using  basic_trans_rules(17) by blast
    then show "(\<exists>\<beta>\<^sub>i. \<forall>x\<in>F. x $ i = \<beta>\<^sub>i)"
      apply (simp add: C_d(1) \<open>i < n\<close> polyhedron_def)
      by (metis R.minus_minus \<open>i < n\<close> scalar_prod_left_unit uminus_scalar_prod unit_vec_carrier)
  qed
  have "\<exists>! x. x \<in> F" 
  proof(rule ccontr)
    assume "\<nexists>!x. x \<in> F"
    then obtain x y where x_y:"x \<in> F \<and> y \<in> F \<and> x \<noteq> y" 
      using \<open>F \<noteq> {}\<close> by blast
    have "\<forall>x \<in> F. x  \<in> carrier_vec n" 
      by (metis (no_types, lifting) C_d(1) polyhedron_def mem_Collect_eq)
    then obtain i where i:"i < n \<and> x $ i \<noteq> y $ i"
      using eq_vecI x_y carrier_vecD by metis 
    have "\<exists>\<beta>\<^sub>i. \<forall>x\<in>F. x $ i = \<beta>\<^sub>i" 
      using \<open>\<forall>i<n. \<exists>\<beta>\<^sub>i. \<forall>x\<in>F. x $ i = \<beta>\<^sub>i\<close> i by presburger
    then show False 
      by (metis i x_y)
  qed
  then show "card F = 1" 
    by (metis \<open>F \<noteq> {}\<close> is_singletonI' is_singleton_altdef)
qed

lemma min_face_distinct:
  fixes A :: "'a  Matrix.mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "P \<noteq> {}"
  assumes "min_face P F"
  assumes "dim_vec b' = Min {dim_vec d | C d I'.  F = {x. x \<in> carrier_vec n \<and> C *\<^sub>v x = d} \<and> 
          (C, d) = sub_system A b I'}"
  assumes " F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'}"  
  assumes "(A', b') = sub_system A b I"
  shows "distinct (Matrix.rows A')" 
proof(rule ccontr)
  let ?M = "{dim_vec d | C d I'.  F = {x. x \<in> carrier_vec n \<and> C *\<^sub>v x = d} \<and> 
          (C, d) = sub_system A b I'}" 
  have dims_eq: "dim_row A = dim_vec b" 
    by (metis assms(1) assms(2) carrier_matD(1) carrier_vecD)
  assume "\<not> distinct (Matrix.rows A') "
  then obtain j1 j2 where j1j2: "j1 \<noteq> j2 \<and> j1 < dim_row A' \<and> 
                                 j2 < dim_row A' \<and> row A' j1 = row A' j2" 
    by (metis distinct_conv_nth length_rows nth_rows)
  obtain i1 where i1:"i1 < dim_row A \<and> i1 \<in> I \<and> row A i1 = row A' j1 \<and>
                      i1 = (pick I j1) \<and> b' $ j1 = b $ i1" 
    by (metis assms(8) dims_eq dims_subsyst_same exist_index_in_A fst_conv j1j2 snd_conv)
  obtain i2 where i2: "i2 < dim_row A \<and> i2 \<in> I \<and> row A i2 = row A' j2 \<and> 
                       i2 = (pick I j2) \<and> b' $ j2 = b $ i2" 
    by (metis assms(8) dims_eq dims_subsyst_same exist_index_in_A fst_conv j1j2 snd_conv)
  then have "i1 \<noteq> i2" using subsyst_indx_neq_syst_indx_neq[of i1 I j1 i2 j2 A' b' A b] 
    using i1 j1j2 assms(8) by presburger
  have " b $ i1 =  b $ i2" 
  proof(rule ccontr)
    assume "b $ i1 \<noteq> b $ i2"
    then have "b' $ j1 \<noteq> b' $ j2" using i1 i2 by auto
    obtain x where "x \<in> F" 
      by (metis A P_def assms(5) b equals0I gram_schmidt.char_min_face)
    then have "x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'" 
      using assms(7) by blast
    have "row A' j1 = row A' j2" using j1j2 
      by blast
    then show False 
      using j1j2 \<open>x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'\<close> index_mult_mat_vec
      using \<open>b' $ j1 \<noteq> b' $ j2\<close> 
      by metis  
  qed
  obtain C d where C_d: "(C, d) = sub_system A b (I - {i1})"
    by (metis surj_pair)
  have "{x.  A' *\<^sub>v x = b'} = {x.  C *\<^sub>v x = d \<and> row A i1 \<bullet> x = b $ i1 }"
    using remove_index_sub_system_eq[of A b i1 I A' b' C d] 
    by (metis A C_d i1 assms(8) b carrier_matD(1) carrier_vecD)
  have "\<forall>x.  C *\<^sub>v x = d \<longrightarrow> row A i1 \<bullet> x = b $ i1"
  proof(safe)
    fix x
    assume "d = C *\<^sub>v x" 
    have "i2 \<in> I - {i1}" 
      using \<open>i1 \<noteq> i2\<close> i2 by blast
    then obtain j where j: "j < dim_row C \<and> row A i2 = row C j \<and> b $ i2 = d $ j" 
      by (metis C_d dims_eq dims_subsyst_same' exist_index_in_A' fst_conv i2 snd_conv)
    then have "row A i1 = row C j \<and> b $ i1 = d $ j" 
      by (metis \<open>b $ i1 = b $ i2\<close> i1 i2 j1j2)
    then have "row C j \<bullet> x = d $ j" using `d = C *\<^sub>v x`  j 
      by (metis index_mult_mat_vec)
    then show "row A i1 \<bullet> x = b $ i1" 
      by (metis \<open>b $ i1 = b $ i2\<close> i1 i2 j j1j2)
  qed
  then have "{x.  A' *\<^sub>v x = b'} = {x. C *\<^sub>v x = d}"
    using \<open>{x. A' *\<^sub>v x = b'} = {x. C *\<^sub>v x = d \<and> row A i1 \<bullet> x = b $ i1}\<close> by blast
  have "dim_vec d + 1 = dim_vec b'" 
    using remove_index_sub_system_dims[of i1 I b A' b' A C d] 
    by (metis C_d assms(8) dims_eq i1)
  have "dim_vec d \<ge> dim_vec b'" 
    using elems_ge_min[of ?M "dim_vec d" "dim_vec b'"] 
      C_d \<open>{x. A' *\<^sub>v x = b'} = {x. C *\<^sub>v x = d}\<close> assms(7)  
      subset_set_of_sub_dims_finite[of ?M A b]  assms(6) by blast
  then show False
    using \<open>dim_vec d + 1 = dim_vec b'\<close> by linarith
qed

lemma subsyst_rows_carr:
  assumes "A \<in> carrier_mat nr n"
  assumes "(A', b') = sub_system A b I"
  shows "set (rows A') \<subseteq> carrier_vec n" 
  using dim_col_subsyst_mat[of A b I]
  using assms carrier_matD(2) prod.sel(1) rows_carrier 
  by metis

lemma itself_is_subsyst_set_idcs:
  fixes A :: "'a  mat"
  fixes b:: "'a vec" 
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr" 
  shows "(A, b) = sub_system A b {0..<nr}"
  by  (auto simp: itself_is_subsyst same_subsyst_I_intersect_rows[of A nr b UNIV] assms) 

lemma sum_list_of_map_eq:
  assumes "\<forall>i \<in> set L. f i = g i"
  shows "sum_list (map f L) = sum_list (map g L)" 
  by (metis assms map_eq_conv)

lemma list_range_lt: "i \<in> set [0..<l] \<longleftrightarrow> i < l" 
  using atLeast_upt by blast

lemma sumlist_system_result:
  assumes "x \<in> carrier_vec n"
  assumes "C *\<^sub>v x = d"
  assumes "set (rows C) \<subseteq> carrier_vec n" 
  assumes "u \<in> carrier_vec n"
  assumes "u = sumlist (map (\<lambda>i. c i \<cdot>\<^sub>v  (rows C) ! i) [0..<length (rows C)])" 
  shows "u \<bullet> x = sum_list  (map (\<lambda>i. (c i *  d $ i)) [0..<length (rows C)])" 
proof -
  let ?Cl = "[0..<length (rows C)]" 
  have Cl_map_carr:"(\<And>v. v \<in> set (map (\<lambda>i. c i \<cdot>\<^sub>v  (rows C) ! i) ?Cl) \<Longrightarrow> v \<in> carrier_vec n)"
    using assms(3) lincomb_map_set_carrier by blast
  have "u \<bullet> x =  x \<bullet> u" 
    using assms(1) assms(4) comm_scalar_prod by blast
  have "u \<bullet> x = sum_list (map ((\<bullet>) x) (map (\<lambda>i. c i \<cdot>\<^sub>v (rows C) ! i) ?Cl))"
    using scalar_prod_right_sum_distrib[OF Cl_map_carr] 
    by(simp only: `u \<bullet> x =  x \<bullet> u`,simp only: assms(5) assms(1)) 
  also have "\<dots> = sum_list (map (\<lambda>i. (c i \<cdot>\<^sub>v (rows C) ! i) \<bullet> x) ?Cl)"
    apply(simp only: map_map comp_def, intro sum_list_of_map_eq, safe)
    apply(intro comm_scalar_prod, blast intro: assms(1))
    using list_range_lt assms(3) nth_mem  by blast
  also have "\<dots> = sum_list (map (\<lambda>i. (c i * (((rows C) ! i) \<bullet> x))) ?Cl)"
    apply(intro sum_list_of_map_eq, safe, simp only: list_range_lt)
    using assms(1) assms(3) nth_mem smult_scalar_prod_distrib by blast
  also have "\<dots> = sum_list (map (\<lambda>i. (c i * d $ i)) ?Cl)"
    apply(intro sum_list_of_map_eq, safe, simp only: list_range_lt)
    using assms(2) by force
  ultimately show "u \<bullet> x = sum_list (map (\<lambda>i. (c i * d $ i)) ?Cl)"
    by presburger
qed

lemma min_face_lin_indpt:
  fixes A :: "'a  mat"
  fixes b:: "'a vec" 
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "P \<noteq> {}"
  assumes "min_face P F"
  assumes "dim_vec b' = Min {dim_vec d | C d I'.  F = {x. x \<in> carrier_vec n \<and> C *\<^sub>v x = d} \<and> 
          (C, d) = sub_system A b I'}"
  assumes " F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'}"  
  assumes "(A', b') = sub_system A b I"
  shows "lin_indpt (set (rows A'))"
proof
  let ?M = "{dim_vec d | C d I'.  F = {x. x \<in> carrier_vec n \<and> C *\<^sub>v x = d} \<and> 
     (C, d) = sub_system A b I'}"
  assume lindpA':"lin_dep (set (rows A'))" 
  have carrA': "set (rows A') \<subseteq> carrier_vec n" using subsyst_rows_carr A assms(8) 
    by blast
  have "finite (set (rows A'))" 
    by simp
  have dim_sameAb: "dim_row A = dim_vec b" 
    using assms(1) assms(2) carrier_vecD by blast
  have 1:"(\<exists>u\<in>(set (rows A')). u \<in> span ((set (rows A')) - {u}))" 
    using lindpA' carrA' lindep_span by blast
  then obtain u where u:"u\<in>(set (rows A'))\<and> u \<in> span ((set (rows A')) - {u})" by auto
  then obtain j where "j < length (rows  A') \<and> rows A' ! j = u" using in_set_conv_nth 
    by metis
  then have j:"j < dim_row A' \<and> row A' j = u" using nth_rows length_rows 
    by metis
  obtain i where i:"i < dim_row A \<and> i \<in> I \<and> row A i = row A' j \<and> i = (pick I j) \<and>  b $ i = b' $ j" 
    by (metis assms(8) dim_sameAb dims_subsyst_same exist_index_in_A fst_conv j snd_conv)
  obtain C d where C_d: "(C, d) = sub_system A b (I - {i})"
    by (metis surj_pair)
  have 4: "{x. A' *\<^sub>v x = b'} = {x.  C *\<^sub>v x = d \<and> row A i \<bullet> x = b $ i }"
    using remove_index_sub_system_eq[of A b i I A' b' C d]  C_d assms(8) dim_sameAb i by linarith 
  have "u \<in> carrier_vec n" 
    using carrA' u by blast
  have Cd_non_empty: "{x. x \<in> carrier_vec n \<and>  C *\<^sub>v x = d \<and> row A' j \<bullet> x = b' $ j } \<noteq> {}" 
    using assms(5)  
    unfolding min_face_def
    by (smt (verit, best) face_non_empty assms(7) "4" Collect_empty_eq Collect_mono_iff i)
  have "\<forall>x \<in> carrier_vec n.  C *\<^sub>v x = d \<longrightarrow> row A i \<bullet> x = b $ i"
  proof(cases "u \<in> set (rows C)")
    case True
    then obtain j' where "j' < length (rows C) \<and> (rows C) ! j' = u"  
      by (meson in_set_conv_nth)
    then have  j': "j' < dim_row C \<and> row C  j' = u"  using length_rows nth_rows by metis  
    obtain i' where i':"i' < nr \<and> i' \<in> (I - {i}) \<and> row A i' = row C j' \<and> d $ j' = b $ i'" 
      by (metis exist_index_in_A_carr[of A nr n b C d _ j'] C_d assms(1) b  j')
    then show ?thesis 
      by (smt (verit, best) Cd_non_empty Collect_empty_eq i index_mult_mat_vec j j')
  next
    case False
    have "set (rows C) \<subseteq> carrier_vec n"
      using subsyst_rows_carr  C_d assms(1) by blast
    have "set (rows C) = set (rows A') - {u}" 
      using remove_index_remove_row[of A b i I A' b' C d]
      by (metis C_d False assms(8) dim_sameAb i j)
    then obtain c where "u = lincomb_list c (rows C)" 
      using  `set (rows C) \<subseteq> carrier_vec n`
      by (metis List.finite_set finite_in_span lincomb_then_lincomb_list u)
    then have "u = sumlist (map (\<lambda>i. c i \<cdot>\<^sub>v  (rows C) ! i) [0..<length (rows C)])"
      using lincomb_list_def by presburger
    then have 6:"\<forall>x \<in> carrier_vec n.  C *\<^sub>v x = d \<longrightarrow>
                 row A' j \<bullet> x = sum_list  (map (\<lambda>i. (c i *  d $ i)) [0..<length (rows C)])" 
      using sumlist_system_result \<open>set (Matrix.rows C) \<subseteq> carrier_vec n\<close> j `u \<in> carrier_vec n`
      by presburger
    have "b' $ j = sum_list (map (\<lambda>i. (c i *  d $ i)) [0..<length (rows C)])"
      apply(rule ccontr)
      using "6" Cd_non_empty 
      by force
    then show "\<forall>x \<in> carrier_vec n.  C *\<^sub>v x = d \<longrightarrow> row A i \<bullet> x = b $ i"
      using 6 i 
      by (metis 6  i)
  qed
  then have "dim_vec b' \<le> dim_vec d"  
    using elems_ge_min[of ?M "dim_vec d" "dim_vec b'"]
      C_d  assms(6-7) 4 subset_set_of_sub_dims_finite[of ?M A b] by blast
  have "dim_vec b' = dim_vec d + 1"  
    using remove_index_sub_system_dims[of i I b A' b' A C d]  C_d assms(8) dim_sameAb i by linarith
  then show False using `dim_vec b' \<le> dim_vec d` 
    by linarith
qed



lemma lin_dep_cols_iff_rows:
  assumes "A \<in> carrier_mat n n"
  assumes "distinct (cols A)"
  assumes "distinct (rows A)"
  shows "lin_dep (set (rows A)) = lin_dep (set (cols A))"
proof
  show "lin_dep (set (Matrix.rows A)) \<Longrightarrow> lin_dep (set (cols A))" 
    using  idom_vec.lin_dep_rows_imp_det_0[OF assms(1)]
    using assms(1) assms(2) det_rank_iff lin_indpt_full_rank by blast
  have A_t: "A\<^sup>T \<in> carrier_mat n n" 
    by (simp add: assms(1))
  show "lin_dep (set (cols A)) \<Longrightarrow> lin_dep (set (Matrix.rows A))"
    using idom_vec.lin_dep_rows_imp_det_0[OF A_t]
    by (metis A_t Matrix.rows_transpose assms(3) cols_transpose det_rank_iff lin_indpt_full_rank)
qed

lemma mult_unit_vec_is_col:
  fixes A :: "'a  mat"
  assumes "A \<in> carrier_mat nr n"
  assumes "i < n"
  shows "A *\<^sub>v unit_vec n i = col A i" 
proof
  show "dim_vec (A *\<^sub>v unit_vec n i) = dim_vec (col A i)" 
    by (metis dim_col dim_mult_mat_vec)
  fix j
  assume j_in_dim:"j < dim_vec (col A i)"
  have "(A *\<^sub>v unit_vec n i) $ j = row A j \<bullet> unit_vec n i" 
    using j_in_dim by fastforce  
  also have "\<dots> = row A j $ i" 
    using assms(2) scalar_prod_right_unit by blast
  also have "\<dots> = col A i $ j" 
    using assms(1) assms(2) j_in_dim  by force
  ultimately show "(A *\<^sub>v unit_vec n i) $ j = col A i $ j"
    by presburger
qed

lemma distinct_cols_append_rows:
  fixes A :: "'a  mat"
  assumes "A \<in> carrier_mat nr1 n"
  assumes "B \<in> carrier_mat nr2 n"
  assumes "distinct (cols A)"
  shows "distinct (cols (A @\<^sub>r B))"
proof -
  have AB_dim_row: "dim_row (A @\<^sub>r B) = nr1 + nr2" 
    using assms(1) assms(2) carrier_matD(1) by blast
  have AB_dim_col:"dim_col (A @\<^sub>r B) = n" 
    using assms(1) assms(2) carrier_matD(2) by blast
  have "(submatrix (A @\<^sub>r B) {0..<nr1} UNIV) = A"
  proof
    have "{i. i<dim_row (A @\<^sub>r B) \<and> i\<in> {0..<nr1}} = {0..<nr1}" 
      using AB_dim_row by fastforce 
    then have "(card {i. i<dim_row (A @\<^sub>r B) \<and> i\<in> {0..<nr1}}) =  nr1" 
      by auto  
    then show "dim_row (submatrix (A @\<^sub>r B) {0..<nr1} UNIV) = dim_row A" 
      using dim_submatrix[of "(A @\<^sub>r B)" "{0..<nr1}"] 
        carrier_matD(1)[OF assms(1)]  by presburger
    show "dim_col (submatrix (A @\<^sub>r B) {0..<nr1} UNIV) = dim_col A" 
      using dim_col_submatrix_UNIV[of "(A @\<^sub>r B)" "{0..<nr1}"]
        AB_dim_col carrier_matD(2)[OF assms(1)] by argo
    fix i j
    assume i_dimA:"i < dim_row A"
    assume j_dimA:"j < dim_col A"
    have i_dimAB:"i < dim_row (A @\<^sub>r B)" 
      by (metis AB_dim_row \<open>i < dim_row A\<close> assms(1) carrier_matD(1) trans_less_add1)
    have j_dimAB:"j < dim_col (A @\<^sub>r B)" 
      by (metis AB_dim_col \<open>j < dim_col A\<close> assms(1) carrier_matD(2))
    show " submatrix (A @\<^sub>r B) {0..<nr1} UNIV $$ (i, j) = A $$ (i, j)"
    proof -
      have "i < nr1" using `i < dim_row A` 
        using assms(1) by blast
      then have "{a\<in>{0..<nr1}. a < i} = {0..<i}" 
        by auto
      then have "card {a\<in>{0..<nr1}. a < i} = i" 
        by simp
      then have "submatrix (A @\<^sub>r B) {0..<nr1} UNIV $$ (i, j) =  (A @\<^sub>r B) $$ (i, j)" 
        using submatrix_index_card[of i "A @\<^sub>r B" j "{0..<nr1}" UNIV] 
          i_dimAB \<open>i < nr1\<close> j_dimAB by force
      also have " (A @\<^sub>r B) $$ (i, j) =  A $$ (i, j)" 
        using append_rows_index_same[of A nr1 B nr2] assms(1-2) 
        by (metis i_dimA i_dimAB j_dimA j_dimAB  index_row(1))
      ultimately show "submatrix (A @\<^sub>r B) {0..<nr1} UNIV $$ (i, j) = A $$ (i, j)" 
        by presburger
    qed
  qed
  then show ?thesis
    by (metis distinct_cols_submatrix_UNIV assms(3))
qed

lemma append_rows_eq: assumes A: "A \<in> carrier_mat nr1 nc" 
  and B: "B \<in> carrier_mat nr2 nc" 
  and a: "a \<in> carrier_vec nr1" 
  and v: "v \<in> carrier_vec nc"
shows "(A @\<^sub>r B) *\<^sub>v v = (a @\<^sub>v b) \<longleftrightarrow> A *\<^sub>v v = a \<and> B *\<^sub>v v = b" 
  unfolding mat_mult_append[OF A B v]
  by (rule append_vec_eq[OF _ a], insert A v, auto)

lemma mult_vec_in_lin_dep_set:
  assumes "v \<in> carrier_vec n"
  assumes "u \<in> carrier_vec n"
  assumes "v = k \<cdot>\<^sub>v u"
  assumes "v \<noteq> u"
  assumes "u \<in> S"
  assumes "v \<in> S"
  shows "lin_dep S"
proof -
  have "0\<^sub>v n = v - k \<cdot>\<^sub>v u " 
    using assms(1) assms(3) by force
  let ?a = "(\<lambda> x. 0)(u:= -k, v:= 1)"
  have "lincomb ?a {u, v} = lincomb ?a {v} + ?a u \<cdot>\<^sub>v u" 
    using M.add.m_comm assms(1) assms(2) assms(4) lincomb_insert by force
  then have "lincomb ?a {u, v} = ?a v \<cdot>\<^sub>v v + ?a u \<cdot>\<^sub>v u + lincomb ?a {}" 
    using assms(1) assms(3) lincomb_insert by fastforce
  then have "lincomb ?a {u, v} = ?a v \<cdot>\<^sub>v v + ?a u \<cdot>\<^sub>v u + 0\<^sub>v n" 
    using lincomb_empty by presburger
  then have "lincomb ?a {u, v} = 1 \<cdot>\<^sub>v v + (-k)\<cdot>\<^sub>v u" 
    using assms(2) assms(3) assms(4) by force
  then have "0\<^sub>v n = lincomb ?a {u, v}" 
    using assms(2) assms(3) by force
  have "finite {u, v}" by auto
  have "{u, v} \<subseteq> S" using assms(5-6) by auto
  have "?a v \<noteq> 0" by auto
  then show ?thesis unfolding lin_dep_def  `0\<^sub>v n = lincomb ?a {u, v}`  
    using \<open>finite {u, v}\<close> \<open>{u, v} \<subseteq> S\<close> by blast
qed

lemma row_in_set_rows:
  fixes A :: "'a  mat"
  assumes "i < dim_row A"
  shows "row A i \<in> set (rows A)"
  by (metis assms in_set_conv_nth length_rows nth_rows)

lemma  mult_row_lin_dep:
  fixes A :: "'a  mat"
  assumes"A \<in> carrier_mat nr n"
  assumes "i < nr"
  assumes "j < nr"
  assumes "k \<noteq> 1" 
  assumes "row A i = k \<cdot>\<^sub>v row A j"
  shows "lin_dep (set (rows A))"
proof -
  have i_dim: "i < dim_row A" 
    using assms(1) assms(2) by blast
  have j_dim: "j < dim_row A" 
    using assms(1) assms(3) by blast
  show ?thesis
  proof(cases "row A j = 0\<^sub>v n")
    case True
    then have "0\<^sub>v n \<in> (set (rows A))" 
      apply(simp add: in_set_conv_nth sym[OF nth_rows[OF j_dim]])
      using j_dim by blast
    then show ?thesis 
      using field.one_not_zero one_zeroI zero_lin_dep by presburger
  next
    case False
    have "row A i \<noteq> row A j" 
    proof(rule ccontr)
      assume " \<not> row A i \<noteq> row A j"
      then have "row A i = row A j" by auto
      then have "row A j = k \<cdot>\<^sub>v row A j" using  assms(5) 
        by auto
      then have "(1 - k) \<cdot>\<^sub>v row A j = 0\<^sub>v n" 
        apply(auto simp: diff_smult_distrib_vec)
        by (meson assms(1) assms(3) minus_cancel_vec row_carrier_vec)
      then have "1 - k = 0"
        by (metis False rmult_0 smult_vec_nonneg_eq)
      then show False
        by (simp add: assms(4))
    qed
    show ?thesis 
      using mult_vec_in_lin_dep_set[of "row A i" "row A j" k " (set (rows A))"] 
      apply(simp add: assms(3))
      apply (simp add: sym[OF assms(5)] `row A i \<noteq> row A j`) 
      using row_in_set_rows i_dim j_dim  assms(1) row_carrier_vec by blast
  qed
qed

lemma add_left_diff_then_eq:
  fixes x :: "'a vec" 
  assumes "x \<in> carrier_vec n"
  assumes "a \<in> carrier_vec n"
  assumes " b \<in> carrier_vec n" 
  assumes "x = x + a - b"
  shows "a = b" 
proof -
  have "a - b = 0\<^sub>v n" 
    using add.l_cancel_one[of x "a-b"] assms
    by (simp add: add_diff_eq_vec)
  then have "a - b + b = 0\<^sub>v n + b" 
    by argo
  then show ?thesis 
    apply(auto simp: comm_add_vec[OF zero_carrier_vec assms(3)] right_zero_vec[OF assms(3)])
    using M.minus_equality assms(2) assms(3) minus_add_uminus_vec  by fastforce
qed

lemma lin_indpt_rows_le_dim_cols:
  fixes A :: "'a  mat"
  assumes "A \<in> carrier_mat nr n"
  assumes "lin_indpt (set (rows A))" 
  assumes "distinct (rows A)"
  shows "nr \<le> n"
proof -
  have "rank A\<^sup>T = nr" 
    by (simp add: assms vec_space.lin_indpt_full_rank)
  have "set (rows A) \<subseteq> carrier_vec n" 
    using assms(1) set_rows_carrier by blast
  then have "(set (cols A\<^sup>T)) \<subseteq> carrier_vec n" 
    by simp 
  then have "dim_span (set (cols A\<^sup>T)) \<le> n" 
    using dim_span_le_n  by blast
  have "rank A\<^sup>T = dim_span (set (cols A\<^sup>T))" 
    by (metis \<open>rank A\<^sup>T = nr\<close> \<open>set (cols A\<^sup>T) \<subseteq> carrier_vec n\<close> assms carrier_matD(1) cols_length
        cols_transpose distinct_card index_transpose_mat(3) same_span_imp_card_eq_dim_span)
  then show "nr \<le> n" 
    using \<open>dim_span (set (cols A\<^sup>T)) \<le> n\<close> \<open>rank A\<^sup>T = nr\<close> by presburger
qed

lemma mat_of_rows_rows:
  assumes "\<forall>x \<in> set l. x \<in> carrier_vec n"
  shows "rows (mat_of_rows n l) = l"
  by (simp add: assms subsetI)

lemma  one_solution_system_sq_mat:
  fixes A :: "'a  mat"
  assumes "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  assumes "\<exists>! x \<in> carrier_vec n. A *\<^sub>v x = b"
  assumes "lin_indpt (set (rows A))"
  assumes "distinct (rows A)"
  shows "nr = n" 
proof(cases "nr = 0")
  case True
  then have "nr = 0" by auto
  then have dim_rowA: "dim_row A = 0" 
    using assms(1) by blast 
  have dim_vecb:" dim_vec b = 0" 
    using True assms(2) carrier_vecD by blast
  then have "\<forall>x \<in> carrier_vec n. A *\<^sub>v x = b" 
    by (insert dim_mult_mat_vec[of A], simp only: dim_rowA vec_of_dim_0, blast)
  then  have "\<exists>!(x:: 'a vec).  x \<in> carrier_vec n" 
    using  assms(3) by auto
  have "n = 0" 
  proof(rule ccontr)
    assume "n \<noteq> 0" 
    have "(1\<^sub>v n:: 'a vec) \<noteq> (0\<^sub>v n:: 'a vec)"
      by (metis \<open>n \<noteq> 0\<close> index_one_vec(1) index_zero_vec(1) neq0_conv zero_neq_one)
    then show False 
      using \<open>\<exists>!x. x \<in> carrier_vec n\<close> one_carrier_vec by blast
  qed
  then show ?thesis using True by auto
next
  case False
  then have "nr > 0" by auto
  have dim_colA: "dim_col A = n" 
    using assms(1) by blast
  have "distinct (cols A)"
  proof(rule ccontr)
    assume "\<not> distinct (cols A)" 
    then obtain i j where "i < length (cols A) \<and> j < length (cols A) \<and>
                           i \<noteq> j \<and> cols A ! i = cols A ! j" 
      using distinct_conv_nth by blast
    then have i_j:"i < n \<and> j < n \<and> i \<noteq> j \<and> col A  i = col A j" 
      by(simp only: cols_length cols_nth, simp add: dim_colA)
    obtain x where x:"x \<in> carrier_vec n \<and> A *\<^sub>v x = b" 
      using assms(3) by auto

    let ?y = "x + (unit_vec n i) - (unit_vec n j)"
    have "?y \<in> carrier_vec n" 
      by (simp add: x)

    have colA_carr:"col A j \<in> carrier_vec nr" 
      by (meson assms(1) col_carrier_vec i_j)
    have " A *\<^sub>v ?y= b"
    proof -
      have "A *\<^sub>v ?y = A *\<^sub>v x + A *\<^sub>v unit_vec n i - A *\<^sub>v unit_vec n j" 
        apply(insert mult_minus_distrib_mat_vec[of A nr n "(x + unit_vec n i)" "unit_vec n j"])
        apply(insert mult_add_distrib_mat_vec[of A nr n "x" "unit_vec n i"])
        by (simp add: x assms(1))
      then show "A *\<^sub>v ?y= b" 
        apply(simp, insert mult_unit_vec_is_col[OF assms(1)], simp add: i_j)
        using colA_carr x add_diff_cancel_right_vec b by blast
    qed
    have "unit_vec n i \<noteq> unit_vec n j" 
      by (simp add: i_j)
    have "x \<noteq> ?y" 
      using add_left_diff_then_eq[of x "unit_vec n i" "unit_vec n j"]  
      by (meson \<open>unit_vec n i \<noteq> unit_vec n j\<close> unit_vec_carrier x)
    then show False 
      using \<open>A *\<^sub>v ?y = b\<close> \<open>?y \<in> carrier_vec n\<close> assms(3) x by blast
  qed
  have "nr \<le> n" using lin_indpt_rows_le_dim_cols assms(1) assms(4) assms(5) 
    by blast
  show "nr = n"
  proof(cases "nr < n")
    case True
    then show ?thesis 
    proof -
      define fullb where fullb: "fullb = b @\<^sub>v (vec n (\<lambda> k. (of_int k + 2) * b $ 0 ))"
      define app_rows where app_rows: "app_rows = mat_of_rows n 
                                         (map (\<lambda> k. (of_int k + 2) \<cdot>\<^sub>v row A 0) [0..<n-nr])"
      define fullA where fullA: "fullA = A @\<^sub>r app_rows"
      have app_rows_dims: "app_rows \<in> carrier_mat (n-nr) n" 
        by (simp add: app_rows mat_of_rows_def)
      have sq_fullA: "fullA \<in> carrier_mat n n" 
        unfolding fullA 
        apply(insert carrier_append_rows[of A nr n app_rows "n-nr"])
        by (simp add: app_rows_dims \<open>nr \<le> n\<close> assms(1))
      have len_rows: "length (rows A) = nr" 
        using assms(1) length_rows by blast
      have dim_rowA: "dim_row A = nr"
        using assms(1) by blast
      have distinct_rows:"distinct (rows fullA)"
      proof(rule ccontr)
        assume "\<not> distinct (rows fullA)" 
        then obtain i j where "i < n \<and> j < n \<and> i \<noteq> j \<and> rows fullA ! i = rows fullA ! j" 
          by (metis carrier_matD(1) distinct_conv_nth length_rows sq_fullA)
        then have i_j:"i < n \<and> j < n \<and> i \<noteq> j \<and> row fullA i = row fullA j"  
          by (metis sq_fullA carrier_matD(1) nth_rows)
        show False
        proof(cases "i < nr")
          case True
          have "row fullA i = row A i"
            unfolding fullA app_rows
            using append_rows_nth(1) True app_rows_dims app_rows assms(1) by blast
          show ?thesis
          proof(cases "j < nr")
            case True
            have "row fullA j = row A j"
              unfolding fullA app_rows
              using append_rows_nth(1) True app_rows_dims app_rows assms(1) by blast
            then have "rows A ! i = rows A ! j" 
              apply(auto simp: `i < nr` `j < nr` dim_rowA) 
              using \<open>row fullA i =row A i\<close> i_j by presburger
            then  show ?thesis 
              using len_rows `i < nr` assms(5) distinct_conv_nth i_j True by blast
          next
            case False
            then have "j - nr < dim_row app_rows" 
              by (simp add: app_rows diff_less_mono i_j) 
            have "nr \<le> j"
              using False by auto
            have "j < nr + (n - nr)" 
              using False i_j by linarith
            then have "row fullA  j = row app_rows (j-nr)" 
              using fullA
                append_rows_nth(2) `nr \<le> j` app_rows_dims assms(1) by blast 
            also have "\<dots> = rows app_rows ! (j-nr)" 
              by(auto simp: \<open>j - nr < dim_row app_rows\<close>) 
            also have 1: "\<dots> = (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr])) ! (j-nr)"
              using \<open>0 < nr\<close> \<open>j - nr < dim_row app_rows\<close> app_rows assms(1) by auto
            also have "\<dots> =  of_int ((j - nr) + 2) \<cdot>\<^sub>v row A 0" 
              using \<open>j - nr < dim_row app_rows\<close>  app_rows  by auto
            finally have "row A i = of_int ((j - nr) + 2) \<cdot>\<^sub>v row A 0" 
              using \<open>row fullA i = row A i\<close> i_j by presburger 
            then show ?thesis 
              using  mult_row_lin_dep[of A nr i 0 "of_int ((j - nr) + 2)"] 
              using True assms(1) assms(4) by fastforce
          qed
        next
          case False
          then have "i \<ge> nr" by auto 
          then have "i - nr < dim_row app_rows" 
            by (simp add: diff_less_mono i_j app_rows) 
          have "i < nr + (n - nr)" using False i_j 
            by linarith
          then have "row fullA i = row app_rows (i-nr)" 
            using fullA
              append_rows_nth(2) `nr \<le> i` app_rows_dims assms(1) by blast 
          also have "row app_rows (i-nr) = rows app_rows ! (i-nr)" 
            by (auto simp: \<open>i - nr < dim_row app_rows\<close>)
          also have 1: "\<dots> = (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr])) ! (i-nr)"
            using \<open>0 < nr\<close> \<open>i - nr < dim_row app_rows\<close> app_rows assms(1) by auto
          also have "\<dots> =  of_int ((i - nr) + 2) \<cdot>\<^sub>v row A 0" 
            using \<open>i - nr < dim_row app_rows\<close>  app_rows  by auto
          finally have "row fullA i = of_int ((i - nr) + 2) \<cdot>\<^sub>v row A 0" 
            using \<open>row fullA i = row app_rows (i-nr)\<close> i_j by presburger 
          show ?thesis 
          proof(cases "j < nr")
            case True
            have "row fullA j = row A j"
              unfolding fullA app_rows
              using append_rows_nth(1) True app_rows_dims app_rows assms(1) by blast
            have "row A j = of_int ((i - nr) + 2) \<cdot>\<^sub>v row A 0" 
              using `row fullA i = of_int ((i - nr) + 2) \<cdot>\<^sub>v row A 0` 
                \<open>row fullA j = row A j\<close> i_j by presburger
            then show ?thesis using mult_row_lin_dep[of A nr j 0 "of_int ((i - nr) + 2)"] `nr \<noteq> 0` 
              using True assms(1) assms(4) by fastforce
          next
            case False
            then have "j - nr < dim_row app_rows" 
              by (simp add: diff_less_mono i_j app_rows) 
            have "nr \<le> j" using False by auto
            have "j < nr + (n - nr)" using False i_j 
              by linarith
            then have "row fullA  j = row app_rows (j-nr)" 
              using fullA
                append_rows_nth(2) `nr \<le> j` app_rows_dims assms(1) by blast 
            also have "\<dots> = rows app_rows ! (j-nr)" 
              by(auto simp: \<open>j - nr < dim_row app_rows\<close>) 
            also have 1: "\<dots> = (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr])) ! (j-nr)"
              using \<open>0 < nr\<close> \<open>j - nr < dim_row app_rows\<close> app_rows assms(1) by auto
            also have "\<dots> =  of_int ((j - nr) + 2) \<cdot>\<^sub>v row A 0" 
              using \<open>j - nr < dim_row app_rows\<close>  app_rows  by auto
            finally have "row fullA j = of_int ((j - nr) + 2) \<cdot>\<^sub>v row A 0" 
              using  i_j by presburger 


            then have "of_int ((i - nr) + 2) \<cdot>\<^sub>v row A 0 = of_int ((j - nr) + 2) \<cdot>\<^sub>v row A 0"
              using \<open>row fullA i = of_int (int (i - nr + 2)) \<cdot>\<^sub>v row A 0\<close> i_j by presburger
            then have "of_int ((i - nr) + 2) \<cdot>\<^sub>v row A 0 - of_int ((j - nr) + 2) \<cdot>\<^sub>v row A 0 = 0\<^sub>v n"
              using \<open>0 < nr\<close> assms(1) by auto
            then have smult_zero:"(of_int ((i - nr) + 2) - of_int ((j - nr) + 2)) \<cdot>\<^sub>v row A 0 = 0\<^sub>v n"
              by (metis diff_smult_distrib_vec)
            show ?thesis
            proof(cases "row A 0 = 0\<^sub>v n")
              case True
              then have "0\<^sub>v n \<in> (set (rows A))"  
                by (metis \<open>0 < nr\<close> dim_rowA row_in_set_rows)
              then show ?thesis 
                using assms(4) field.one_not_zero zero_lin_dep by blast
            next
              case False
              then show False 
                by (metis False R.minus_other_side smult_zero \<open>nr \<le> i\<close> \<open>nr \<le> j\<close> diff_add_inverse2 
                    eq_diff_iff i_j of_int_of_nat_eq of_nat_eq_iff smult_r_null smult_vec_nonneg_eq)
            qed
          qed
        qed
      qed
      have distinct_cols:"distinct (cols fullA)" 
        using \<open>distinct (cols A)\<close> app_rows_dims assms(1) fullA distinct_cols_append_rows by blast
      have "lin_dep (set (rows fullA))"
      proof -
        have "row fullA nr = row app_rows 0" 
          using True app_rows_dims append_rows_index_same' assms(1) fullA  by auto
        have "row app_rows 0 = (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr])) ! 0" 
          using True assms(1) `nr > 0` app_rows  by fastforce
        then have "row fullA nr = 2 \<cdot>\<^sub>v row A 0" 
          by(simp add: \<open>row fullA nr = row app_rows 0\<close> True)
        moreover have "row fullA 0 = row A 0" 
          using append_rows_nth(1) \<open>0 < nr\<close> app_rows_dims assms(1) fullA by blast
        ultimately show ?thesis 
          using mult_row_lin_dep[of fullA n nr 0 2] True sq_fullA by simp 
      qed
      then have "lin_dep (set (cols fullA))"
        using lin_dep_cols_iff_rows[of fullA] distinct_rows distinct_cols sq_fullA by fastforce
      then obtain v where v:"v \<in> carrier_vec n" "v \<noteq> 0\<^sub>v n" "fullA *\<^sub>v v = 0\<^sub>v n" 
        using lin_depE[of fullA] sq_fullA distinct_cols  by blast
      then have "(A @\<^sub>r app_rows) *\<^sub>v v = A *\<^sub>v v @\<^sub>v app_rows *\<^sub>v v"
        by (meson app_rows_dims assms(1) mat_mult_append)
      have " 0\<^sub>v nr @\<^sub>v 0\<^sub>v (n - nr) = 0\<^sub>v n"
        using \<open>nr \<le> n\<close> by fastforce 
      have "A *\<^sub>v v = 0\<^sub>v nr"
        using append_rows_eq[of A nr n app_rows "n-nr" "0\<^sub>v nr" v "0\<^sub>v (n-nr)" ]
        apply(simp add: `0\<^sub>v nr @\<^sub>v 0\<^sub>v (n - nr) = 0\<^sub>v n` app_rows_dims assms(1) v(1))
        using fullA v(3) by blast+
      obtain x where x:"x \<in> carrier_vec n \<and> A *\<^sub>v x = b" 
        using assms(3) by auto
      then have "x + v \<noteq> x" 
        by (simp add: v(1-2))
      have "A *\<^sub>v (x + v) = b" 
      proof -
        have "A *\<^sub>v (x + v) = A *\<^sub>v x + A *\<^sub>v v" 
          using v(1) x assms(1) mult_add_distrib_mat_vec by blast
        then show ?thesis 
          by (simp add: \<open>A *\<^sub>v v = 0\<^sub>v nr\<close> x b)
      qed
      then show ?thesis 
        by (metis \<open>x + v \<noteq> x\<close> add_carrier_vec assms(3) v(1) x)
    qed
  next
    case False
    then show ?thesis 
      by (simp add: \<open>nr \<le> n\<close> nless_le)
  qed
qed

lemma bounded_min_faces_square_mat:
  fixes A :: "'a  mat"
  fixes bound:: "'a" 
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "P \<noteq> {}"
  assumes bounded: "(\<forall> x \<in> P. \<forall> i < n. x $ i \<le> bound) \<or> (\<forall> x \<in> P. \<forall> i < n. x $ i \<ge> bound)" 
  assumes "min_face P F"
  assumes "dim_vec b' = Min {dim_vec d | C d I'.  F = {x. x \<in> carrier_vec n \<and> C *\<^sub>v x = d} \<and> 
          (C, d) = sub_system A b I'}"
  assumes " F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'}"  
  assumes "(A', b') = sub_system A b I"
  shows "dim_row A' = n"
proof -
  have "card F = 1" using bounded_min_faces_are_vertex bounded_min_faces_are_vertex' assms(1-6)
    by metis
  then have "\<exists>!x. x \<in> F" using card_eq_Suc_0_ex1 
    by (metis One_nat_def)
  then have 1:"\<exists>!x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'" 
    using assms(8) 
    by auto
  have "lin_indpt (set (rows A'))" using min_face_lin_indpt[of A nr b F b' A' I] 
    using A P_def assms(4) assms(6) assms(7) assms(8) assms(9) b by fastforce
  have "distinct (rows A')" using min_face_distinct
    using A P_def assms(4) assms(6) assms(7) assms(8) assms(9) b 
    by blast
  have 2:"A' \<in> carrier_mat (dim_row A') n" 
    by (metis A assms(9) b carrier_matD(1) carrier_matD(2) carrier_mat_subsyst 
        carrier_vecD fst_conv)
  have "b' \<in> carrier_vec (dim_row A')" 
    by (metis \<open>A' \<in> carrier_mat (dim_row A') n\<close> 1 mult_mat_vec_carrier)
  then show "dim_row A' = n" 
    using one_solution_system_sq_mat[of A' "dim_row A'" b']
      2 1 \<open>distinct (rows A')\<close> \<open>lin_indpt (set (rows A'))\<close> by blast
qed

lemma minus_mult_minus_one:
  fixes v :: "'a vec" 
  shows "- v = - 1 \<cdot>\<^sub>v v"
  unfolding smult_vec_def
proof
  show "dim_vec (- v) = dim_vec (vec (dim_vec v) (\<lambda>i. - 1 * v $ i))" 
    by simp
  fix i
  assume asmi:"i < dim_vec (vec (dim_vec v) (\<lambda>i. - 1 * v $ i))"
  have "(- v) $ i = - (v $ i)" 
    using \<open>i < dim_vec (vec (dim_vec v) (\<lambda>i. - 1 * v $ i))\<close> by force
  have "- (v $ i) = - 1 * v $ i" 
    by simp
  then show " (- v) $ i = vec (dim_vec v) (\<lambda>i. - 1 * v $ i) $ i" 
    by (metis \<open>(- v) $ i = - v $ i\<close> asmi dim_vec index_vec)
qed

lemma vec_carr_add_mono:
  fixes x y:: "'a vec" 
  assumes "x \<in> carrier_vec n"
  assumes "y \<in> carrier_vec n"
  assumes "a \<in> carrier_vec n"
  assumes "b \<in> carrier_vec n"
  assumes "x \<le> a"
  assumes "y \<le> b"
  shows "x + y \<le> a + b" 
  by (metis assms(3) assms(4) assms(5) assms(6) carrier_vecD vec_add_mono)

lemma bound_vec_smult_bound:
  fixes S :: "'a vec set"
  assumes "S \<subseteq> carrier_vec n" 
  assumes "\<forall> x \<in> S. \<forall> i < n.  x $ i \<le> 1"
  assumes "\<forall> x \<in> S. \<forall> i < n.  x $ i \<ge> - 1"
  assumes "n > 0"
  assumes "c \<in> carrier_vec n"
  shows "\<exists> bnd. \<forall> x \<in>S. c \<bullet> x \<le> bnd" 
proof -
  have "\<forall> x \<in>S.  c \<bullet> x \<le> of_int n * Max (abs ` (vec_set c))" 
  proof 
    fix x
    assume "x \<in> S"
    have 1:"x \<in> carrier_vec n" using `x \<in> S` 
      using assms(1) by blast
    have 2:"\<forall> i < n.  x $ i \<le> 1" 
      using \<open>x \<in> S\<close> assms(2) by blast 
    have 3:"\<forall> i < n.  x $ i \<ge> -1" 
      using \<open>x \<in> S\<close> assms(3) by blast 
    have "set\<^sub>v c \<noteq> {}" using `n > 0` 
      by (metis carrier_vecD equals0D  vec_setI assms(5))
    have "Max (abs ` (vec_set c)) \<ge> 0" 
      by (metis (mono_tags, lifting) Max_in \<open>set\<^sub>v c \<noteq> {}\<close> abs_ge_zero finite_imageI
          finite_vec_set imageE image_is_empty)
    have "c \<bullet> 1\<^sub>v n = sum (\<lambda> i. c $ i) {0..<n}" 
      using assms(5) scalar_prod_right_one by blast
    have "\<forall> i < n. c $ i * x $ i \<le> abs (c $ i)" 
    proof(safe)
      fix i
      assume "i< n"
      show "c $ i * x $ i \<le> \<bar>c $ i\<bar>"
      proof(cases "x $ i = 0")
        case True
        then show ?thesis 
          by simp
      next
        case False
        then show ?thesis
        proof(cases "c $ i > 0")
          case True
          have "x $ i \<le> 1" 
            by (simp add: "2" \<open>i < n\<close>)
          then have "c $ i * x $ i \<le> c $ i" 
            by (simp add: True)
          then show ?thesis 
            by linarith
        next
          case False
          have "x $ i \<ge> - 1" 
            by (simp add: "3" \<open>i < n\<close>)
          then have "c $ i * x $ i \<le> - c $ i" using False 
            by (metis mult_le_cancel_left mult_minus1_right)
          then show ?thesis by linarith
        qed
      qed
    qed
    then have "\<forall> i < n. c $ i * x $ i \<le> Max (abs ` (vec_set c))" 
      by (smt (verit) Max_ge assms(5) carrier_vecD dual_order.order_iff_strict finite_imageI 
          finite_vec_set image_eqI order_less_le_trans vec_setI)
    then have "(\<And>i. i \<in> {0..<n} \<Longrightarrow> c $ i * x $ i \<le> Max (abs ` set\<^sub>v c))" by auto
    then have "sum (\<lambda> i. c $ i * x $ i ) {0..<n} \<le> of_int n * Max (abs ` (vec_set c))"
      using sum_bounded_above[of "{0..<n}" "(\<lambda> i. c $ i * x $ i )" "Max (abs ` (vec_set c))"]
      by fastforce
    then have " c \<bullet> x \<le> of_int n * Max (abs ` (vec_set c))" 
      unfolding scalar_prod_def  
      using "1" carrier_vecD by blast
    then show " c \<bullet> x \<le> of_int (int n) * Max (abs ` set\<^sub>v c)"
      by blast
  qed
  then show " \<exists>bnd. \<forall>x\<in>S. c \<bullet> x \<le> bnd" by auto
qed

lemma int_mat_replace_col_int_mat:
  assumes "A \<in> carrier_mat n n"
  assumes "b \<in> carrier_vec n"
  assumes "A \<in> \<int>\<^sub>m"
  assumes "b \<in> \<int>\<^sub>v"
  assumes "k < n"
  shows "det (replace_col A b k) \<in> \<int>"
proof -
  have 1:"(replace_col A b k) = 
    mat (dim_row A) (dim_col A) (\<lambda> (i,j). if j = k then b $ i else A $$ (i,j))"
    unfolding replace_col_def by auto
  have "(replace_col A b k) \<in> \<int>\<^sub>m" 
    unfolding Ints_mat_def
  proof(safe)
    fix i j
    assume asmi:"i < dim_row (replace_col A b k)"
    assume asmj:"j < dim_col (replace_col A b k)" 
    show "replace_col A b k $$ (i, j) \<in> \<int>"
    proof(cases "j = k")
      case True
      have "replace_col A b k $$ (i, j) = b $ i" 
        unfolding replace_col_def 
        using "1" True asmi assms(1) assms(5) by auto
      then show ?thesis 
        by (metis (no_types, lifting) Ints_vec_def asmi 1 assms(1,2,4) carrier_matD(1) 
            carrier_vecD dim_row_mat(1) mem_Collect_eq)
    next
      case False
      have "replace_col A b k $$ (i, j) = A $$ (i,j)" 
        unfolding replace_col_def 
        using "1" False asmi asmj by fastforce
      then show ?thesis 
        using Ints_mat_def asmi asmj 1 assms(3) by auto
    qed
  qed
  then show "det (replace_col A b k) \<in> \<int>"  using Ints_det 
    using Ints_mat_def 
    by blast 
qed

lemma submatrix_int_mat:
  assumes "A \<in> \<int>\<^sub>m"
  shows "submatrix A I J \<in> \<int>\<^sub>m"
proof -
  show "submatrix A I J \<in> \<int>\<^sub>m"
    using assms unfolding Ints_mat_def submatrix_def
  proof(safe)
    fix i j
    assume "\<forall>i<dim_row A. \<forall>j<dim_col A. A $$ (i, j) \<in> \<int>"
    assume asmi:"i < dim_row
                (Matrix.mat (card {i. i < dim_row A \<and> i \<in> I})
                  (card {j. j < dim_col A \<and> j \<in> J}) (\<lambda>(i, j). A $$ (pick I i, pick J j)))"
    assume asmj:"j < dim_col
                (Matrix.mat (card {i. i < dim_row A \<and> i \<in> I})
                  (card {j. j < dim_col A \<and> j \<in> J}) (\<lambda>(i, j). A $$ (pick I i, pick J j)))"
    show "Matrix.mat (card {i. i < dim_row A \<and> i \<in> I}) (card {j. j < dim_col A \<and> j \<in> J})
             (\<lambda>(i, j). A $$ (pick I i, pick J j)) $$ (i, j) \<in> \<int>"
    proof -
      have "A $$ (pick I i, pick J j) \<in> \<int>" 
      proof -
        have "i < (card {i. i < dim_row A \<and> i \<in> I})" 
          using asmi by auto
        then have "pick I i < dim_row A" 
          using pick_le by presburger
        have "j < (card {i. i < dim_col A \<and> i \<in> J})" 
          using asmj by fastforce
        then have "pick J j < dim_col A" 
          using pick_le  by presburger
        then show ?thesis 
          using \<open>\<forall>i<dim_row A. \<forall>j<dim_col A. A $$ (i, j) \<in> \<int>\<close> \<open>pick I i < dim_row A\<close> by blast
      qed
      then show ?thesis 
        using asmi asmj by simp
    qed
  qed
qed

lemma append_int_mat_is_int:
  assumes "A \<in> carrier_mat nr1 n"
  assumes "B \<in> carrier_mat nr2 n"
  assumes "A \<in> \<int>\<^sub>m"
  assumes "B \<in> \<int>\<^sub>m"
  shows "A @\<^sub>r B \<in> \<int>\<^sub>m" 
proof -
  show "A @\<^sub>r B \<in> \<int>\<^sub>m" 
    unfolding Ints_mat_def  
  proof(safe)
    fix i j
    assume asmi:"i < dim_row (A @\<^sub>r B)"
    assume asmj:"j < dim_col (A @\<^sub>r B)" 
    show "(A @\<^sub>r B) $$ (i, j) \<in> \<int>"
    proof(cases "i<dim_row A")
      case True
      have 1:"row (A @\<^sub>r B) i = row A i"
        using True Missing_Matrix.append_rows_nth(1) assms(1) assms(2) by blast
      have 2:"(A @\<^sub>r B) $$ (i, j) = row (A @\<^sub>r B) i $ j" 
        by (simp add: asmi asmj)
      have "j < dim_col A" 
        by (metis 1 asmj index_row(2))
      then have "A $$ (i, j) = row A i $ j" 
        by (simp add: True)
      then have "(A @\<^sub>r B) $$ (i, j) = A $$ (i, j)" 
        using 1 2 by presburger
      then show ?thesis 
        using assms(3) unfolding Ints_mat_def 
        using True \<open>j < dim_col A\<close> by force
    next
      case False
      have 1:"row (A @\<^sub>r B) i = row B (i - nr1)"
        using False Missing_Matrix.append_rows_nth(2) assms(1) assms(2) 
        by (metis (no_types, lifting) asmi append_rows_def carrier_matD(1) 
            index_mat_four_block(2) index_zero_mat(2) not_less)
      have 2:"(A @\<^sub>r B) $$ (i, j) = row (A @\<^sub>r B) i $ j" 
        by (simp add: asmi asmj)
      have "j < dim_col B" 
        by (metis 1 asmj index_row(2))
      then have "B $$ (i-nr1, j) = row B (i-nr1) $ j"
        using False 1 2 
        by (metis (mono_tags, lifting) asmi add_0_right append_rows_def assms(1-2) carrier_matD(1) 
            carrier_matD(2) index_mat_four_block(1) index_mat_four_block(2) index_zero_mat(3))
      then have "(A @\<^sub>r B) $$ (i, j) = B $$ (i - nr1, j)" 
        using 2 1 by presburger
      then show ?thesis 
        using assms(4) unfolding Ints_mat_def 
        by (metis (no_types, lifting) False asmi \<open>j < dim_col B\<close> append_rows_def assms(1)
            carrier_matD(1) index_mat_four_block(2) index_zero_mat(2) le_add_diff_inverse
            mem_Collect_eq nat_add_left_cancel_less not_less)
    qed
  qed
qed

lemma append_int_vec_is_int:
  assumes "v \<in> carrier_vec nr1"
  assumes "w \<in> carrier_vec nr2"
  assumes "v \<in> \<int>\<^sub>v"
  assumes "w \<in> \<int>\<^sub>v"
  shows "v @\<^sub>v w \<in> \<int>\<^sub>v" 
  unfolding Ints_vec_def 
proof(safe)
  fix i
  assume asmi:"i < dim_vec (v @\<^sub>v w) "
  show "(v @\<^sub>v w) $v i \<in> \<int>"
  proof(cases "i < nr1")
    case True
    have "(v @\<^sub>v w) $v i = v $ i" 
      using True 
      by (metis asmi assms(1) carrier_vecD index_append_vec(1) index_append_vec(2))
    then show ?thesis 
      using assms(3) unfolding Ints_vec_def  using True assms(1) by auto
  next
    case False
    have "(v @\<^sub>v w) $v i = w $ (i - nr1)" 
      by (metis False asmi assms(1) carrier_vecD index_append_vec(1) index_append_vec(2))
    then show ?thesis using assms(4) unfolding Ints_vec_def 
      using False assms(2) 
      using \<open>i < dim_vec (v @\<^sub>v w)\<close> assms(1) by auto
  qed
qed

lemma one_mat_int: "1\<^sub>m n \<in> \<int>\<^sub>m" 
  unfolding Ints_mat_def one_mat_def
proof(safe)
  fix i j
  assume asmi:"i < dim_row (Matrix.mat n n (\<lambda>(i, j). if i = j then 1 else 0))"
  assume asmj:"j < dim_col (Matrix.mat n n (\<lambda>(i, j). if i = j then 1 else 0))"
  show "Matrix.mat n n (\<lambda>(i, j). if i = j then 1 else 0) $$ (i, j) \<in> \<int>"
  proof(cases "i=j")
    case True
    have "Matrix.mat n n (\<lambda>(i, j). if i = j then 1 else 0) $$ (i, j) = 1" 
      using True asmi by auto
    then show ?thesis  
      by (smt (verit, ccfv_SIG) Ints_1)
  next
    case False
    have "Matrix.mat n n (\<lambda>(i, j). if i = j then 1 else 0) $$ (i, j) = 0" 
      using False asmi asmj by simp
    then show ?thesis 
      by (smt (verit) Ints_0)
  qed
qed

lemma subvec_int_int:
  assumes bI: "b \<in> \<int>\<^sub>v"
  shows "vec_of_list (nths (list_of_vec b) I) \<in> \<int>\<^sub>v"
  using assms unfolding Ints_vec_def
proof(safe) 
  fix i
  assume "\<forall>i<dim_vec b. b $v i \<in> \<int> " 
  assume asmi:"i < dim_vec (vec_of_list (nths (list_of_vec b) I))" 
  show " vec_of_list (nths (list_of_vec b) I) $v i \<in> \<int>" 
  proof -
    have "vec_of_list (nths (list_of_vec b) I) $v i = (nths (list_of_vec b) I) ! i" 
      by (metis  vec_of_list_index)
    obtain j where "j< length (list_of_vec b)" "(list_of_vec b) ! j = (nths (list_of_vec b) I) ! i"
      by (metis Matrix.dim_vec_of_list asmi in_set_conv_nth notin_set_nthsI)
    then have "(list_of_vec b) ! j \<in> \<int>" 
      by (metis Matrix.length_list_of_vec \<open>\<forall>i<dim_vec b. b $v i \<in> \<int>\<close> list_of_vec_index)
    then show ?thesis 
      by (simp add: \<open>list_of_vec b ! j = nths (list_of_vec b) I ! i\<close>)
  qed
qed

lemma one_vec_int: "1\<^sub>v n  \<in> \<int>\<^sub>v "
  unfolding Ints_vec_def  
  by fastforce

lemma bounded_min_faces_det_non_zero:
  fixes A :: "'a  mat"
  fixes bound:: "'a" 
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "P \<noteq> {}"
  assumes bounded: "(\<forall> x \<in> P. \<forall> i < n. x $ i \<le> bound) \<or> (\<forall> x \<in> P. \<forall> i < n. x $ i \<ge> bound)" 
  assumes "min_face P F"
  assumes "dim_vec b' = Min {dim_vec d | C d I'.  F = {x. x \<in> carrier_vec n \<and> C *\<^sub>v x = d} \<and> 
          (C, d) = sub_system A b I'}"
  assumes " F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'}"  
  assumes "(A', b') = sub_system A b I"
  shows "det A' \<noteq> 0"
proof -
  have 1: "polyhedron A b \<noteq> {}" 
    using assms(3) assms(4) by blast
  have 2: "(\<forall> x \<in> polyhedron A b. \<forall> i < n. x $ i \<le> bound) \<or> 
    (\<forall> x \<in> polyhedron A b. \<forall> i < n. x $ i \<ge> bound)" 
    using assms(3) assms(5) by fastforce
  have 3: "min_face (polyhedron A b) F" 
    using assms(3) assms(6) by blast
  have "dim_row A' = n" 
    using bounded_min_faces_square_mat[OF A b 1 2 3]
    using assms(7-9) by blast
  then have "A' \<in> carrier_mat n n" 
    using  A  carrier_matD(2) carrier_matI dim_col_subsyst_mat fst_conv
    by (metis assms(9))
  then have "lin_indpt (set (rows A'))"
    using min_face_lin_indpt[OF A b 1 3] 
    using assms(7-9) by blast
  have "distinct (rows A')"
    using min_face_distinct[OF A b 1 3]  using assms(7-9) by blast
  have "(rows A') = cols (A'\<^sup>T)" 
    by simp
  have "lin_indpt (set (cols A'\<^sup>T))" using `lin_indpt (set (rows A'))` by auto
  have "distinct (cols A'\<^sup>T)" using `distinct (rows A')` by auto
  have "A' \<in> carrier_mat (dim_row A') n" 
    by (metis assms(1,9) carrier_matD(2) carrier_matI dim_col_subsyst_mat fst_conv)
  then have "rank A'\<^sup>T = dim_row A'" 
    using lin_indpt_full_rank[of "A'\<^sup>T" "dim_row A'"]
      `lin_indpt (set (cols A'\<^sup>T))` `distinct (cols A'\<^sup>T)`  transpose_carrier_mat by blast
  then show "det A' \<noteq> 0" 
    by (metis \<open>A' \<in> carrier_mat (dim_row A') n\<close> \<open>dim_row A' = n\<close> det_rank_iff
        det_transpose transpose_carrier_mat)
qed

lemma min_face_has_int:
  fixes A :: "'a  mat"
  fixes bound:: "'a" 
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  assumes AI: "A \<in> \<int>\<^sub>m"
  assumes bI: "b \<in> \<int>\<^sub>v"
  defines "P \<equiv> polyhedron A b"
  assumes "P \<noteq> {}"
  assumes bounded: "(\<forall> x \<in> P. \<forall> i < n. x $ i \<le> bound) \<or> (\<forall> x \<in> P. \<forall> i < n. x $ i \<ge> bound)" 
  assumes "min_face P F"
  assumes "dim_vec b' = Min {dim_vec d | C d I'.  F = {x. x \<in> carrier_vec n \<and> C *\<^sub>v x = d} \<and> 
          (C, d) = sub_system A b I'}"
  assumes " F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'}"  
  assumes "(A', b') = sub_system A b I"
  shows "\<exists> x \<in> F. abs(det A') \<cdot>\<^sub>v x \<in>  \<int>\<^sub>v"
proof -
  obtain z where "z \<in> F" using assms(8)
    by (metis ex_in_conv face_non_empty gram_schmidt.min_face_elim(1))
  have 1: "polyhedron A b \<noteq> {}"
    using assms(5) assms(6) by auto
  have 2: " (\<forall>x\<in>local.polyhedron A b. \<forall>i<n. x $v i \<le> bound) \<or>
  (\<forall>x\<in>local.polyhedron A b. \<forall>i<n. bound \<le> x $v i) " 
    using assms(5) assms(7) by fastforce
  have 3: "min_face (polyhedron A b) F " 
    using assms(5) assms(8) by blast
  have "det A' \<noteq> 0" 
    using bounded_min_faces_det_non_zero[OF A b 1 2 3 assms(9) assms(10) assms(11)]
    by blast
  have "dim_row A' = n"
    using bounded_min_faces_square_mat[OF A b 1 2 3]
    using assms(9-11) 
    by blast
  then have "A' \<in> carrier_mat n n" 
    by (metis  A assms(11) carrier_matD(2) carrier_matI dim_col_subsyst_mat fst_conv)
  have 5:"A' *\<^sub>v z = b' \<longleftrightarrow> z = vec n (\<lambda> k. det (replace_col A' b' k) / det A')" 
    using cramer1[of A' n  b' z] `det A' \<noteq> 0` `A' \<in> carrier_mat n n` 
    using \<open>z \<in> F\<close> assms(10) by fastforce
  then have 4:"z = vec n (\<lambda> k. det (replace_col A' b' k) / det A')" 
    using assms(10) \<open>z \<in> F\<close> by force
  have "det A \<in> \<int>" using Ints_det AI 
    using Ints_mat_def by blast
  have "dim_vec z = n" 
    using 4 dim_vec by blast
  have "A' \<in> \<int>\<^sub>m" 
    using submatrix_int_mat[of A I UNIV]  assms(11) `A \<in> \<int>\<^sub>m` 
    unfolding sub_system_def 
    by blast 
  have "b' \<in> \<int>\<^sub>v" 
    using subvec_int_int[of b I] assms(11) `b \<in> \<int>\<^sub>v`
    unfolding sub_system_def 
    by blast 
  have "\<forall> k < n. det (replace_col A' b' k) \<in> \<int>" 
    using int_mat_replace_col_int_mat[of A' b'] dim_mult_mat_vec
      5 \<open>A' \<in> \<int>\<^sub>m\<close> \<open>A' \<in> carrier_mat n n\<close> \<open>b' \<in> \<int>\<^sub>v\<close> \<open>dim_row A' = n\<close> 4 carrier_dim_vec by blast
  let ?z' = "abs(det A') \<cdot>\<^sub>v z"
  have "?z' \<in> \<int>\<^sub>v"
  proof -
    have "\<forall>k < n. z $ k = det (replace_col A' b' k) / det A'" 
      using 4 index_vec by blast
    then have "\<forall>k < n.  (\<lambda>i. \<bar>det A'\<bar> * z $v i) k =
     (\<lambda>k. \<bar>det A'\<bar> * det (replace_col A' b' k) / det A') k  " 
      by (metis times_divide_eq_right)
    then have 6:"?z' =  vec n (\<lambda> k. \<bar>det A'\<bar> * det (replace_col A' b' k) / det A')" 
      unfolding smult_vec_def 
      by (auto simp: `dim_vec z = n` 4) 
    have "\<bar>det A'\<bar> /det A' \<in> \<int>" 
    proof(cases "det A' > 0")
      case True
      have "\<bar>det A'\<bar> /det A' = 1" 
        by (metis True \<open>Determinant.det A' \<noteq> 0\<close> abs_of_pos divide_self)
      then show ?thesis 
        by fastforce
    next
      case False
      have "\<bar>det A'\<bar> /det A' = - 1" 
        using False  \<open>Determinant.det A' \<noteq> 0\<close>  
        by (metis abs_if divide_eq_minus_1_iff linorder_neqE_linordered_idom)
      then show ?thesis by auto
    qed
    then have "\<forall>k < n.\<bar>det A'\<bar> * det (replace_col A' b' k) / det A' \<in> \<int>" 
      by (metis Ints_mult \<open>\<forall>k<n. Determinant.det (replace_col A' b' k) \<in> \<int>\<close> times_divide_eq_left)
    then have "vec n (\<lambda> k. \<bar>det A'\<bar> * det (replace_col A' b' k) / det A') \<in> \<int>\<^sub>v" 
      unfolding Ints_vec_def  
      by simp
    then show ?thesis 
      using 6 by presburger
  qed
  show " \<exists>x\<in>F. \<bar>Determinant.det A'\<bar> \<cdot>\<^sub>v x \<in> \<int>\<^sub>v" 
    using \<open>\<bar>Determinant.det A'\<bar> \<cdot>\<^sub>v z \<in> \<int>\<^sub>v\<close> \<open>z \<in> F\<close> by blast
qed

end 
context gram_schmidt_floor
begin

lemma int_hull_bound_then_poly_bounded:
  fixes A :: "'a  mat"
  fixes b:: "'a vec" 
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes c: "c \<in> carrier_vec n"
  assumes "has_Maximum {c \<bullet> x | x. x \<in> integer_hull P}"
  assumes AI: "A \<in> \<int>\<^sub>m"
  assumes bI: "b \<in> \<int>\<^sub>v"
  assumes "integer_hull P \<noteq> {}"
  shows "has_Maximum { c \<bullet> x | x. x \<in> P}"
proof(rule ccontr)
  assume "\<not> has_Maximum {c \<bullet> x |x. x \<in> P}" 
  then have "\<not> (\<exists> x. x \<in> {c \<bullet> x |x. x \<in> P} \<and> (\<forall> y \<in> {c \<bullet> x |x. x \<in> P}. y \<le> x))" 
    unfolding has_Maximum_def 
    by blast
  then have "\<forall>x \<in> {c \<bullet> x |x. x \<in> P}. \<not> (\<forall> y \<in> {c \<bullet> x |x. x \<in> P}. y \<le> x)" 
    by blast
  then have "\<forall>x \<in> {c \<bullet> x |x. x \<in> P}. (\<exists> y \<in> {c \<bullet> x |x. x \<in> P}. y > x)" 
    by fastforce
  then have "\<forall>x \<in> P. \<exists> y \<in> P. c \<bullet> y > c \<bullet> x" 
    by auto
  have "P \<noteq> {}" using assms(8) 
    by (metis P_def assms(1) b gram_schmidt.int_hull_subset subset_empty) 
  have "\<forall> v. \<exists> x \<in> P. c \<bullet> x \<ge> v"
  proof(rule ccontr)
    assume "\<not> (\<forall>v. \<exists>x\<in>P. v \<le> c \<bullet> x)"
    then obtain Bnd where "\<forall> y \<in> P. c \<bullet> y < Bnd" 
      by (meson less_le_not_le linorder_linear)
    then have "\<forall> x \<in> carrier_vec n. A *\<^sub>v x \<le> b \<longrightarrow> c \<bullet> x \<le> Bnd"
      unfolding P_def polyhedron_def 
      using order_le_less by auto
    then have "has_Maximum {c \<bullet> x | x. x \<in> carrier_vec n \<and> A *\<^sub>v x \<le> b}"
      using 
        strong_duality_theorem_primal_sat_bounded_min_max(2)[OF A b c]
      by (metis (no_types, lifting) Collect_empty_eq P_def `P \<noteq> {}` local.polyhedron_def) 
    then show False using `\<not> has_Maximum {c \<bullet> x |x. x \<in> P}`
      unfolding P_def polyhedron_def 
      by fastforce
  qed
  then have "\<forall>v. \<exists>x\<in>carrier_vec n. A *\<^sub>v x \<le> b \<and> v \<le> c \<bullet> x" 
    unfolding P_def polyhedron_def 
    by auto
  then have "\<not> (\<exists> y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = c)" 
    using unbounded_primal_solutions[of A nr n b c] A b c by blast
  then have "\<not>  (\<forall> y. y \<in> carrier_vec n \<longrightarrow> A *\<^sub>v y \<ge> 0\<^sub>v nr \<longrightarrow> y \<bullet> c \<ge> 0)"
    using Farkas_Lemma[of "A\<^sup>T" nr c] c
    using c  A
    by force
  then obtain y where y: "y \<in> carrier_vec n \<and> A *\<^sub>v y \<ge> 0\<^sub>v nr \<and> y \<bullet> c < 0" 
    using leI by blast
  have "(-y) \<bullet> c > 0" 
    using assms(4) y by auto 
  have "A *\<^sub>v (-y) \<le> 0\<^sub>v nr" 
    by (smt (verit, ccfv_SIG) A carrier_matD(1) class_ring.minus_zero dim_mult_mat_vec
        minus_mult_minus_one index_uminus_vec(1) index_zero_vec(1) less_eq_vec_def 
        mult_mat_vec neg_le_iff_le y)
  then obtain y' where y': "y' \<in> carrier_vec n \<and> A *\<^sub>v y' \<le> 0\<^sub>v nr \<and> y' \<bullet> c > 0" 
    using \<open>0 < - y \<bullet> c\<close> uminus_carrier_vec y by blast
  have "y' \<noteq> 0\<^sub>v n"
  proof
    assume "y' = 0\<^sub>v n"
    then have "y' \<bullet> c = 0" 
      using c assms(7) row_carrier scalar_prod_left_zero by blast
    then show False using y' 
      by linarith
  qed
  have "n \<noteq> 0"
  proof
    assume "n=0"
    then have "y' = 0\<^sub>v 0" 
      using carrier_vecD vec_of_dim_0 y' by blast
    then show False using `y' \<noteq> 0\<^sub>v n` 
      using \<open>n = 0\<close> by blast
  qed
  then have "set\<^sub>v y' \<noteq> {}" 
    by (metis carrier_vecD equals0D not_gr_zero vec_setI y')
  have "Max (abs ` (vec_set y')) > 0"
  proof(rule ccontr)
    assume "\<not> 0 < Max (abs ` set\<^sub>v y')"
    have "\<forall> y \<in> (abs ` set\<^sub>v y'). y \<ge> 0" 
      by fastforce
    have "finite (abs ` set\<^sub>v y')" 
      by fastforce
    have "(abs ` set\<^sub>v y') \<noteq> {}" 
      using \<open>set\<^sub>v y' \<noteq> {}\<close> by blast
    then have " Max (abs ` set\<^sub>v y') \<ge> 0" 
      by (meson Max_in \<open>\<forall>y\<in>abs ` set\<^sub>v y'. 0 \<le> y\<close> \<open>finite (abs ` set\<^sub>v y')\<close>)
    then have "Max (abs ` (vec_set y')) = 0" 
      using \<open>\<not> 0 < Max (abs ` set\<^sub>v y')\<close> by linarith
    then have "\<forall> y' \<in> (abs ` set\<^sub>v y'). y' = 0" 
      by (metis Max_ge \<open>\<forall>y'\<in>abs ` set\<^sub>v y'. 0 \<le> y'\<close> \<open>finite (abs ` set\<^sub>v y')\<close> order_antisym_conv)
    then have "\<forall>y' \<in> set\<^sub>v y'. y' = 0" 
      by auto
    then have "y' = 0\<^sub>v n" unfolding zero_vec_def 
      by (metis M.zero_closed \<open>y' \<noteq> 0\<^sub>v n\<close> carrier_vecD eq_vecI index_zero_vec(1) vec_setI y')
    then show False 
      using \<open>y' \<noteq> 0\<^sub>v n\<close> by auto
  qed
  let ?y' = " (1/Max (abs ` (vec_set y'))) \<cdot>\<^sub>v  y'" 
  let ?fullA = "A @\<^sub>r (1\<^sub>m n) @\<^sub>r (- 1\<^sub>m n)"
  let ?fullb = "0\<^sub>v nr @\<^sub>v 1\<^sub>v n @\<^sub>v 1\<^sub>v n" 
  let ?c = "c"
  let ?P' = "polyhedron ?fullA ?fullb"
  have 2:"?fullA \<in> carrier_mat (nr+2*n) n" 
    by (metis A carrier_append_rows mult_2 one_carrier_mat uminus_carrier_iff_mat)
  have 3:"?fullb \<in> carrier_vec (nr+2*n)" 
    by (simp add: mult_2)
  have "?y' \<in> ?P'" 
  proof -
    have "A *\<^sub>v y' \<le> 0\<^sub>v nr" using y' by auto
    then have "(1/Max (abs ` (vec_set y'))) \<cdot>\<^sub>v (A *\<^sub>v y') \<le> 0\<^sub>v nr" 
      using \<open>Max (abs ` (vec_set y')) > 0\<close> 
      by (meson divide_nonneg_pos smult_nneg_npos_vec zero_less_one_class.zero_le_one)
    then have "A *\<^sub>v ?y' \<le> 0\<^sub>v nr" 
      by (metis A mult_mat_vec y')
    have "\<forall> i < n. row (1\<^sub>m n) i \<bullet> ?y' \<le> 1" 
    proof(safe)
      fix i
      assume "i< n" 
      have 2:"row (1\<^sub>m n) i = unit_vec n i" 
        using \<open>i < n\<close> row_one by blast
      have 1:"unit_vec n i \<bullet> ?y' = ?y' $ i" 
        by (meson \<open>i < n\<close> scalar_prod_left_unit smult_closed y')
      have "y' $ i \<le>  Max (abs ` set\<^sub>v y')" 
        by (metis (mono_tags, lifting) Max_ge \<open>0 < Max (abs ` set\<^sub>v y')\<close> \<open>i < n\<close> abs_of_pos 
            carrier_vecD finite_imageI finite_vec_set image_eqI linorder_le_less_linear 
            order.asym order_less_le_trans vec_setI y')
      then have "(1 / Max (abs ` set\<^sub>v y')) * (y' $ i) \<le> 1" 
        by (metis \<open>0 < Max (abs ` set\<^sub>v y')\<close> divide_pos_pos mult_le_cancel_left_pos 
            nonzero_eq_divide_eq order_less_irrefl zero_less_one_class.zero_less_one)
      have "(1 / Max (abs ` set\<^sub>v y') \<cdot>\<^sub>v y') $ i \<le> 1" 
        by (metis \<open>1 / Max (abs ` set\<^sub>v y') * y' $ i \<le> 1\<close> \<open>i < n\<close> carrier_vecD index_smult_vec(1) y')
      then show "row (1\<^sub>m n) i \<bullet> ?y' \<le> 1" 
        by (simp add: 2 1)
    qed
    then have "1\<^sub>m n *\<^sub>v ?y' \<le> 1\<^sub>v n" 
      unfolding mult_mat_vec_def 
      by (simp add: less_eq_vec_def)
    have "\<forall> i < n. row (- 1\<^sub>m n) i \<bullet> ?y' \<le> 1" 
    proof(safe)
      fix i
      assume "i< n" 
      have " row (- 1\<^sub>m n) i =  - unit_vec n i" 
        using \<open>i < n\<close> row_one 
        by simp 
      have 3:"- unit_vec n i \<bullet> ?y' = - ?y' $ i" 
        by (metis \<open>i < n\<close> scalar_prod_left_unit smult_closed 
            uminus_scalar_prod unit_vec_carrier y')
      have "- y' $ i \<le>  Max (abs ` set\<^sub>v y')" 
        by (metis Max_ge \<open>i < n\<close> abs_le_D2 carrier_vecD finite_imageI 
            finite_vec_set image_eqI vec_setI y') 
      then have "(1 / Max (abs ` set\<^sub>v y')) * (- y' $ i) \<le> 1" 
        by (metis \<open>0 < Max (abs ` set\<^sub>v y')\<close> divide_pos_pos mult_le_cancel_left_pos
            nonzero_eq_divide_eq order_less_irrefl zero_less_one_class.zero_less_one)
      have " - (1 / Max (abs ` set\<^sub>v y') \<cdot>\<^sub>v y') $ i \<le> 1" 
        by (metis \<open>1 / Max (abs ` set\<^sub>v y') * - y' $ i \<le> 1\<close> \<open>i < n\<close> carrier_vecD index_smult_vec(1)
            mult_minus_right y')
      then show "row (- 1\<^sub>m n) i \<bullet> ?y' \<le> 1" 
        by (simp add: \<open>row (- 1\<^sub>m n) i = - unit_vec n i\<close> 3)
    qed
    then have "- 1\<^sub>m n *\<^sub>v ?y' \<le> 1\<^sub>v n" 
      unfolding mult_mat_vec_def 
      by (simp add: less_eq_vec_def)
    have "(1\<^sub>m n @\<^sub>r - 1\<^sub>m n)  *\<^sub>v ?y' \<le>  ( 1\<^sub>v n @\<^sub>v 1\<^sub>v n)"
      using `- 1\<^sub>m n *\<^sub>v ?y' \<le> 1\<^sub>v n` `1\<^sub>m n *\<^sub>v ?y' \<le> 1\<^sub>v n` 
        append_rows_le 
      by (metis carrier_matI index_one_mat(2) index_one_mat(3) index_uminus_mat(3)
          one_carrier_vec smult_closed y')
    then have "(A @\<^sub>r 1\<^sub>m n @\<^sub>r - 1\<^sub>m n) *\<^sub>v ?y' \<le>  (0\<^sub>v nr @\<^sub>v 1\<^sub>v n @\<^sub>v 1\<^sub>v n)" 
      using `- 1\<^sub>m n *\<^sub>v ?y' \<le> 1\<^sub>v n` 
        append_rows_le[of "A" nr n "1\<^sub>m n @\<^sub>r - 1\<^sub>m n" "2*n" "0\<^sub>v nr" ?y' "1\<^sub>v n @\<^sub>v 1\<^sub>v n"] 
      by (metis A \<open> A *\<^sub>v (1 / Max (abs ` set\<^sub>v y') \<cdot>\<^sub>v y') \<le> 0\<^sub>v nr\<close> carrier_append_rows mult.commute
          mult_2_right one_carrier_mat smult_closed uminus_carrier_iff_mat y' zero_carrier_vec)
    then show "?y' \<in> ?P'" unfolding polyhedron_def 
      using y' by blast
  qed
  then have 1:"?P' \<noteq> {}" by auto
  have "\<exists> x \<in> carrier_vec n. ?fullA *\<^sub>v x \<le> ?fullb" using `?y' \<in> ?P'`
    unfolding polyhedron_def by auto
  have  4:"\<forall> x \<in> ?P'. \<forall> i < n.  x $ i \<le> 1"
  proof
    fix x
    assume "x \<in> ?P'"
    have "x \<in> carrier_vec n" 
      using `x \<in> ?P'` unfolding polyhedron_def by auto
    have "(A @\<^sub>r 1\<^sub>m n @\<^sub>r - 1\<^sub>m n) *\<^sub>v x \<le>  (0\<^sub>v nr @\<^sub>v 1\<^sub>v n @\<^sub>v 1\<^sub>v n)" 
      using `x \<in> ?P'` unfolding polyhedron_def by auto
    then have "(1\<^sub>m n @\<^sub>r - 1\<^sub>m n)  *\<^sub>v x \<le>  ( 1\<^sub>v n @\<^sub>v 1\<^sub>v n)" 
      using  append_rows_le[of "A" nr n "1\<^sub>m n @\<^sub>r - 1\<^sub>m n" "2*n" "0\<^sub>v nr" x "1\<^sub>v n @\<^sub>v 1\<^sub>v n"] 
      by (metis A \<open>x \<in> carrier_vec n\<close> carrier_append_rows mult_2 one_carrier_mat 
          uminus_carrier_mat zero_carrier_vec)
    then have "1\<^sub>m n *\<^sub>v x \<le> 1\<^sub>v n" 
      using  append_rows_le[of "1\<^sub>m n" n n "- 1\<^sub>m n" n "1\<^sub>v n" x "1\<^sub>v n"] 
      by (simp add: \<open>x \<in> carrier_vec n\<close>) 
    then have "\<forall> i < n. row (1\<^sub>m n) i \<bullet> x \<le> 1" unfolding mult_mat_vec_def 
      by (simp add: less_eq_vec_def)
    then show " \<forall> i < n.  x $ i \<le> 1" 
      by (simp add: \<open>x \<in> carrier_vec n\<close>)
  qed
  have 5:"\<forall> x \<in> ?P'. \<forall> i < n.  x $ i \<ge> - 1"
  proof
    fix x
    assume "x \<in> ?P'"
    have "x \<in> carrier_vec n" 
      using `x \<in> ?P'` unfolding polyhedron_def by auto
    have "(A @\<^sub>r 1\<^sub>m n @\<^sub>r - 1\<^sub>m n) *\<^sub>v x \<le>  (0\<^sub>v nr @\<^sub>v 1\<^sub>v n @\<^sub>v 1\<^sub>v n)" 
      using `x \<in> ?P'` unfolding polyhedron_def by auto
    then have "(1\<^sub>m n @\<^sub>r - 1\<^sub>m n)  *\<^sub>v x \<le>  ( 1\<^sub>v n @\<^sub>v 1\<^sub>v n)" 
      using  append_rows_le[of "A" nr n "1\<^sub>m n @\<^sub>r - 1\<^sub>m n" "2*n" "0\<^sub>v nr" x "1\<^sub>v n @\<^sub>v 1\<^sub>v n"] 
      by (metis A \<open>x \<in> carrier_vec n\<close> carrier_append_rows mult_2 one_carrier_mat 
          uminus_carrier_mat zero_carrier_vec)
    then have " -  1\<^sub>m n *\<^sub>v x \<le> 1\<^sub>v n" 
      using  append_rows_le[of "1\<^sub>m n" n n "- 1\<^sub>m n" n "1\<^sub>v n" x "1\<^sub>v n"] 
      by (simp add: \<open>x \<in> carrier_vec n\<close>) 
    then have "\<forall> i < n. row (- 1\<^sub>m n) i \<bullet> x \<le> 1" unfolding mult_mat_vec_def 
      by (simp add: less_eq_vec_def)
    then have "\<forall> i < n. - unit_vec n i \<bullet> x \<le> 1" 
      by simp
    then have "\<forall> i < n. - x $ i \<le> 1" 
      by (metis \<open>x \<in> carrier_vec n\<close> carrier_vecD index_unit_vec(3) 
          scalar_prod_left_unit scalar_prod_uminus_left)
    then show " \<forall> i < n.  x $ i \<ge> - 1" 
      by (simp add: \<open>x \<in> carrier_vec n\<close>)
  qed
  have "?P' \<subseteq> carrier_vec n"  unfolding polyhedron_def  by auto  
  have "?c \<in> carrier_vec n" 
    using c by blast
  have "\<exists> bnd. \<forall> x \<in> carrier_vec n. ?fullA *\<^sub>v x \<le> ?fullb \<longrightarrow> ?c \<bullet> x \<le> bnd" 
    using bound_vec_smult_bound[of ?P' ?c] 
    apply (auto simp: 4 5 `n\<noteq>0` `?P' \<subseteq> carrier_vec n` `?c \<in> carrier_vec n`) 
    unfolding polyhedron_def 
    using \<open>n \<noteq> 0\<close> by auto
  then have 4:"has_Maximum {?c \<bullet> x | x. x \<in> carrier_vec n \<and> ?fullA *\<^sub>v x \<le> ?fullb}"
    using strong_duality_theorem_primal_sat_bounded_min_max[of ?fullA "nr+2*n" n ?fullb ?c]
    using 2 3 assms(7) row_carrier `\<exists> x \<in> carrier_vec n. ?fullA *\<^sub>v x \<le> ?fullb` c
    by blast 
  then obtain \<beta> where beta: "\<beta> = Maximum {?c \<bullet> x | x. x \<in> carrier_vec n \<and> ?fullA *\<^sub>v x \<le> ?fullb}"
    by auto
  then have 4:"support_hyp ?P' ?c \<beta>" unfolding support_hyp_def  
    by (smt (verit, best) c Collect_cong 4 assms(7) mem_Collect_eq polyhedron_def row_carrier)
  let ?F = " ?P' \<inter> {x |x. ?c \<bullet> x = \<beta>}"
  have "face ?P' ?F" unfolding face_def using 1 4 
    by blast 
  then obtain F where F_def:"min_face ?P' F \<and> F \<subseteq> ?F" 
    using 2 3 face_contains_min_face[of ?fullA "nr+2*n" ?fullb ?F] 
    by blast
  then obtain z where "z \<in> F" 
    by (metis ex_in_conv face_non_empty gram_schmidt.min_face_elim(1))
  obtain A' b' I where A'_b':" F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'}"
    "(A', b') = sub_system ?fullA ?fullb I" 
    "dim_vec b' = Min {dim_vec d| C d I. (C, d) = sub_system ?fullA ?fullb I \<and> 
                                             F = {x. x \<in> carrier_vec n \<and> C *\<^sub>v x = d}}"
    using F_def min_face_min_subsyst[of ?fullA "(nr + 2*n)" ?fullb F]  
    using 2 3
    by (smt (verit, ccfv_SIG))
  have 9: "(\<forall>x\<in>local.polyhedron (A @\<^sub>r 1\<^sub>m n @\<^sub>r - 1\<^sub>m n) (0\<^sub>v nr @\<^sub>v 1\<^sub>v n @\<^sub>v 1\<^sub>v n).
        \<forall>i<n. x $v i \<le> 1) \<or>
    (\<forall>x\<in>local.polyhedron (A @\<^sub>r 1\<^sub>m n @\<^sub>r - 1\<^sub>m n) (0\<^sub>v nr @\<^sub>v 1\<^sub>v n @\<^sub>v 1\<^sub>v n).
        \<forall>i<n. 1 \<le> x $v i)" using `\<forall> x \<in> ?P'. \<forall> i < n.  x $ i \<le> 1` 
    by blast
  have 10:"dim_vec b' = Min {dim_vec d| C d I.   F = {x. x \<in> carrier_vec n \<and> C *\<^sub>v x = d} \<and>
              (C, d) = sub_system ?fullA ?fullb I}" 
    by (smt (verit) A'_b'(3) Collect_cong)
  have "det A' \<noteq> 0" 
    using bounded_min_faces_det_non_zero[OF 2 3 1 9] F_def A'_b' 10 
    by fast
  have "dim_row A' = n" 
    using bounded_min_faces_square_mat[of ?fullA "nr+ 2*n" ?fullb 1 F b' A' I]
    using A'_b' `\<forall> x \<in> ?P'. \<forall> i < n.  x $ i \<le> 1` 1 2 3 
    by (smt (verit, ccfv_SIG) Collect_cong F_def)
  then have "A' \<in> carrier_mat n n" 
    by (metis "2" A'_b'(2) carrier_matD(2) carrier_matI dim_col_subsyst_mat fst_conv)
  have 7:"A' *\<^sub>v z = b' \<longleftrightarrow> z = vec n (\<lambda> k. det (replace_col A' b' k) / det A')" 
    using cramer1[of A' n  b' z] `det A' \<noteq> 0` `A' \<in> carrier_mat n n` 
    using A'_b'(1) \<open>z \<in> F\<close> carrier_dim_vec dim_mult_mat_vec by blast
  then have 6:"z = vec n (\<lambda> k. det (replace_col A' b' k) / det A')" 
    using A'_b'(1) \<open>z \<in> F\<close> by force
  have "det A \<in> \<int>" using Ints_det AI 
    using Ints_mat_def by blast
  have "dim_vec z = n" 
    using 6 dim_vec by blast
  have "1\<^sub>m n \<in> \<int>\<^sub>m" using one_mat_int by auto
  have "- 1\<^sub>m n \<in> \<int>\<^sub>m" using one_mat_int by auto
  have "?fullA \<in> \<int>\<^sub>m" using append_int_mat_is_int
    by (metis A \<open>- 1\<^sub>m n \<in> \<int>\<^sub>m\<close> assms(6) carrier_append_rows one_carrier_mat 
        one_mat_int uminus_carrier_mat) 
  have "?fullb \<in> \<int>\<^sub>v" using append_int_vec_is_int one_vec_int 
    by (metis carrier_vec_dim_vec gram_schmidt.zero_vec_is_int)
  have "A' \<in> \<int>\<^sub>m" 
    using submatrix_int_mat[of ?fullA I UNIV]  A'_b'(2) `?fullA \<in> \<int>\<^sub>m` 
    unfolding sub_system_def 
    by blast 
  have "b' \<in> \<int>\<^sub>v"
    using subvec_int_int[of ?fullb I] A'_b'(2) `?fullb \<in> \<int>\<^sub>v`
    unfolding sub_system_def 
    by blast 
  have "\<forall> k < n. det (replace_col A' b' k) \<in> \<int>"
    using int_mat_replace_col_int_mat[of A' b'] dim_mult_mat_vec
    using 7 \<open>A' \<in> \<int>\<^sub>m\<close> \<open>A' \<in> carrier_mat n n\<close> \<open>b' \<in> \<int>\<^sub>v\<close> \<open>dim_row A' = n\<close> 6 carrier_dim_vec by blast
  let ?z' = "abs(det A') \<cdot>\<^sub>v z"
  have "?z' \<in> \<int>\<^sub>v"
  proof -
    have "\<forall>k < n. z $ k = det (replace_col A' b' k) / det A'" 
      using 6 index_vec by blast
    then have "\<forall>k < n.  (\<lambda>i. \<bar>det A'\<bar> * z $v i) k =
     (\<lambda>k. \<bar>det A'\<bar> * det (replace_col A' b' k) / det A') k  " 
      by (metis times_divide_eq_right)
    then have 8:"?z' =  vec n (\<lambda> k. \<bar>det A'\<bar> * det (replace_col A' b' k) / det A')" 
      unfolding smult_vec_def using 6
      by (auto simp: `dim_vec z = n`) 
    have "\<bar>det A'\<bar> /det A' \<in> \<int>" 
    proof(cases "det A' > 0")
      case True
      have "\<bar>det A'\<bar> /det A' = 1" 
        by (metis True \<open>Determinant.det A' \<noteq> 0\<close> abs_of_pos divide_self)
      then show ?thesis 
        by fastforce
    next
      case False
      have "\<bar>det A'\<bar> /det A' = - 1" 
        using False  \<open>Determinant.det A' \<noteq> 0\<close>  
        by (metis abs_if divide_eq_minus_1_iff linorder_neqE_linordered_idom)
      then show ?thesis by auto
    qed
    then have "\<forall>k < n.\<bar>det A'\<bar> * det (replace_col A' b' k) / det A' \<in> \<int>" 
      by (metis Ints_mult \<open>\<forall>k<n. Determinant.det (replace_col A' b' k) \<in> \<int>\<close> times_divide_eq_left)
    then have "vec n (\<lambda> k. \<bar>det A'\<bar> * det (replace_col A' b' k) / det A') \<in> \<int>\<^sub>v" 
      unfolding Ints_vec_def  
      by simp
    then show ?thesis 
      using 8 by presburger
  qed
  have 9:"?c \<bullet> ?y' =  (1 / Max (abs ` set\<^sub>v y')) * (?c \<bullet>  y')" 
    using y' assms(7) row_carrier scalar_prod_smult_distrib c
    by force
  have "(1 / Max (abs ` set\<^sub>v y')) > 0" 
    using \<open>0 < Max (abs ` set\<^sub>v y')\<close> zero_less_divide_1_iff by blast
  then have "?c \<bullet> ?y' > 0" using y' 
    by (metis "4" 9 comm_scalar_prod gram_schmidt.support_hyp_def 
        linordered_semiring_strict_class.mult_pos_pos)
  have "\<beta> \<ge> ?c \<bullet> ?y'" using `?y' \<in> ?P'` unfolding polyhedron_def
    using beta 
    using "4" \<open>?y' \<in> ?P'\<close> gram_schmidt.support_hyp_is_valid(1) by blast
  then have "\<beta> > 0" 
    using \<open>0 < c \<bullet> (1 / Max (abs ` set\<^sub>v y') \<cdot>\<^sub>v y')\<close> by linarith
  have "z \<in> carrier_vec n" 
    using A'_b'(1) \<open>z \<in> F\<close>  by force
  have 12:"z \<in> ?F" 
    using F_def \<open>z \<in> F\<close> by blast
  then have "A *\<^sub>v z \<le> 0\<^sub>v nr" 
    unfolding polyhedron_def 
    using append_rows_le[of "A" nr n "1\<^sub>m n @\<^sub>r - 1\<^sub>m n" "2*n" "0\<^sub>v nr" z "1\<^sub>v n @\<^sub>v 1\<^sub>v n"]
    by (simp add: A mult_2 )
  then have "(A *\<^sub>v z) \<le> 0\<^sub>v nr" 
    using A A'_b'(1) \<open>z \<in> F\<close> by force
  then have "A *\<^sub>v ?z' \<le> 0\<^sub>v nr" 
    using A A'_b'(1) \<open>z \<in> F\<close> 
    by (simp add: mult_mat_vec smult_nneg_npos_vec)
  have "c \<in> carrier_vec n" 
    using c by blast
  have "P \<subseteq> carrier_vec n" unfolding P_def polyhedron_def 
    by blast 
  then have "integer_hull P \<subseteq> carrier_vec n"
    by (simp add: gram_schmidt.integer_hull_in_carrier)
  have "\<forall> \<alpha> \<in> carrier_vec n. has_Maximum { \<alpha> \<bullet> x | x. x \<in> integer_hull P} \<longrightarrow>
   (\<exists>x. x \<in> integer_hull P \<and> \<alpha> \<bullet> x = Maximum { \<alpha> \<bullet> x | x. x \<in> integer_hull P}  \<and> x \<in> \<int>\<^sub>v)" 
 proof -
    have "integer_hull P = integer_hull (integer_hull P)" 
      using assms(5) unfolding P_def polyhedron_def 
      by (metis (no_types, lifting) integer_hull_is_integer_hull mem_Collect_eq subset_iff)
    then have "(\<forall> F. face (integer_hull P) F \<longrightarrow> (\<exists> x \<in> F. x \<in> \<int>\<^sub>v))"
      using P_int_then_face_int \<open>integer_hull P \<subseteq> carrier_vec n\<close> by presburger
    then show ?thesis
      using int_face_then_max_suphyp_int `integer_hull P \<subseteq> carrier_vec n` 
      using assms(7) carrier_vec_dim_vec by blast 
  qed
  then obtain v where v:"v \<in> integer_hull P \<and> 
                         ?c \<bullet> v = Maximum { ?c \<bullet> x | x. x \<in> integer_hull P} \<and> 
                         v \<in> \<int>\<^sub>v" 
    using assms(5) `c \<in> carrier_vec n` 
    by meson
  then have "v \<in> integer_hull P" using assms(5) 
    by blast 
  then have "v \<in> P" 
    using A P_def b int_hull_subset by blast
  have "A *\<^sub>v v \<le> b" using `v \<in> P` unfolding P_def polyhedron_def by auto
  have "v \<in> carrier_vec n" using v unfolding integer_hull_def  P_def polyhedron_def 
    using P_def \<open>v \<in> P\<close> gram_schmidt.polyhedron_def by blast
  have "?z' \<in> carrier_vec n" using `z \<in> carrier_vec n` 
    by blast 
  have 11:"\<forall> m::nat. v + of_int m \<cdot>\<^sub>v ?z' \<in> P"
  proof
    fix m::nat
    have " m \<ge> 0" 
      by simp 
    have "A *\<^sub>v (of_int m \<cdot>\<^sub>v ?z') = of_int m \<cdot>\<^sub>v ( A *\<^sub>v ?z')" 
      using mult_mat_vec[of A nr n z "of_int m"]  using A A'_b'(1) \<open>z \<in> F\<close> by force
    have "of_int m \<cdot>\<^sub>v ( A *\<^sub>v ?z') \<le> 0\<^sub>v nr" 
      using smult_nneg_npos_vec[of "of_int m" "A *\<^sub>v ?z'" nr] 
      by (simp add:  ` m \<ge> 0` `A *\<^sub>v ?z' \<le> 0\<^sub>v nr`)
    then have "A *\<^sub>v (of_int m \<cdot>\<^sub>v ?z') \<le> 0\<^sub>v nr" 
      using `A *\<^sub>v (of_int m \<cdot>\<^sub>v ?z') = of_int m \<cdot>\<^sub>v ( A *\<^sub>v ?z')` by auto
    have "v + of_int m \<cdot>\<^sub>v ?z' \<in> carrier_vec n" 
      using \<open>\<bar>det A'\<bar> \<cdot>\<^sub>v z \<in> carrier_vec n\<close> \<open>v \<in> carrier_vec n\<close> by blast
    have 10:"A *\<^sub>v (v + of_int m \<cdot>\<^sub>v ?z') = A *\<^sub>v v + A *\<^sub>v (of_int m \<cdot>\<^sub>v ?z')" 
      by (meson A \<open>\<bar>det A'\<bar> \<cdot>\<^sub>v z \<in> carrier_vec n\<close> \<open>v \<in> carrier_vec n\<close> mult_add_distrib_mat_vec
          smult_closed)
    have "A *\<^sub>v v + A *\<^sub>v (of_int m \<cdot>\<^sub>v ?z') \<le> b + 0\<^sub>v nr"
      using `A *\<^sub>v v \<le> b` `A *\<^sub>v (of_int m \<cdot>\<^sub>v ?z') \<le> 0\<^sub>v nr` using vec_add_mono 
      by (metis b carrier_vecD index_zero_vec(2))
    then have "A *\<^sub>v (v + of_int m \<cdot>\<^sub>v ?z') \<le> b" 
      by (metis 10 b right_zero_vec)
    then show "v + of_int (int m) \<cdot>\<^sub>v (\<bar>det A'\<bar> \<cdot>\<^sub>v z) \<in> P"
      unfolding P_def polyhedron_def 
      using \<open>v + of_int (int m) \<cdot>\<^sub>v (\<bar>det A'\<bar> \<cdot>\<^sub>v z) \<in> carrier_vec n\<close> by blast
  qed
  have "\<forall> m::nat. v + of_int m \<cdot>\<^sub>v ?z' \<in> \<int>\<^sub>v"
  proof
    fix m::nat
    have " m \<in> \<int>"  by simp 
    then have "of_int m \<cdot>\<^sub>v ?z' \<in> \<int>\<^sub>v" using int_mult_int_vec 
      using Ints_of_int \<open>\<bar>det A'\<bar> \<cdot>\<^sub>v z \<in> \<int>\<^sub>v\<close> by blast
    then show "v + of_int m \<cdot>\<^sub>v ?z' \<in> \<int>\<^sub>v" 
      using v \<open>\<bar>det A'\<bar> \<cdot>\<^sub>v z \<in> carrier_vec n\<close> \<open>v \<in> carrier_vec n\<close> sum_int_is_int by blast
  qed
  then have "\<forall> m::nat. v + of_int m \<cdot>\<^sub>v ?z' \<in> integer_hull P" 
    by (metis A Diff_iff P_def 11 b gram_schmidt.not_in_int_hull_not_int)
  have "?c \<bullet> z = \<beta>" 
    using 12 by blast
  then have "?c \<bullet> ?z' = abs (det A') * \<beta>" 
    by (metis \<open>\<bar>det A'\<bar> \<cdot>\<^sub>v z \<in> carrier_vec n\<close> \<open>c \<in> carrier_vec n\<close> carrier_vecD 
        index_smult_vec(2) scalar_prod_smult_right)
  have "v + ?z' \<in> \<int>\<^sub>v" using `\<forall> m::nat. v + of_int m \<cdot>\<^sub>v ?z' \<in> \<int>\<^sub>v` 
    using \<open>\<bar>det A'\<bar> \<cdot>\<^sub>v z \<in> \<int>\<^sub>v\<close> \<open>\<bar>det A'\<bar> \<cdot>\<^sub>v z \<in> carrier_vec n\<close> \<open>v \<in> carrier_vec n\<close>
      gram_schmidt.sum_int_is_int v by blast
  have "v + ?z' \<in> P"
  proof -
    have " v + of_int 1 \<cdot>\<^sub>v ?z' \<in> P" 
      using `\<forall> m::nat. v + of_int m \<cdot>\<^sub>v ?z' \<in> P` 
      by (metis int_ops(2))
    then show ?thesis 
      by (metis of_int_hom.hom_one scalar_vec_one)  
  qed
  then have "v + ?z' \<in> integer_hull P" 
    by (metis \<open>\<forall>x. v + of_int (int x) \<cdot>\<^sub>v (\<bar>det A'\<bar> \<cdot>\<^sub>v z) \<in> integer_hull P\<close> of_int_hom.hom_one
        of_nat_1 scalar_vec_one)
  then have "v + ?z' \<in> integer_hull P " 
    using assms(5) by blast
  then have "?c \<bullet> (v + ?z') \<le> Maximum { ?c \<bullet> x | x. x \<in> integer_hull P}" 
    using assms(5) has_MaximumD(2) by blast
  have "?c \<bullet> (v + ?z') = ?c \<bullet> v + ?c \<bullet> ?z'" 
    using \<open>\<bar>det A'\<bar> \<cdot>\<^sub>v z \<in> carrier_vec n\<close> \<open>c \<in> carrier_vec n\<close> \<open>v \<in> carrier_vec n\<close>
      scalar_prod_add_distrib by blast
  then have "?c \<bullet> (v + ?z') = Maximum { ?c \<bullet> x | x. x \<in> integer_hull P} + abs (det A') * \<beta>"
    using `?c \<bullet> ?z' = abs (det A') * \<beta>` v 
    by presburger
  then have "?c \<bullet> (v + ?z') > Maximum { ?c \<bullet> x | x. x \<in> integer_hull P}" 
    by (simp add: \<open>0 < \<beta>\<close> \<open>det A' \<noteq> 0\<close>)
  then show False 
    using \<open>c \<bullet> (v + \<bar>det A'\<bar> \<cdot>\<^sub>v z) \<le> Maximum {c \<bullet> x |x. x \<in> integer_hull P}\<close> 
      linorder_not_le by blast
qed

lemma int_support_hyp_then_int_polyhedron:
  fixes A :: "'a  mat"
  fixes b:: "'a vec" 
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
    and AI: "A \<in> \<int>\<^sub>m"
    and bI: "b \<in> \<int>\<^sub>v"
  defines "P \<equiv> polyhedron A b"
  assumes "\<forall> \<alpha> \<in> carrier_vec n. has_Maximum { \<alpha> \<bullet> x | x. x \<in> P} \<longrightarrow>
   (\<exists>x. x \<in> P \<and> \<alpha> \<bullet> x = Maximum { \<alpha> \<bullet> x | x. x \<in> P}  \<and> x \<in> \<int>\<^sub>v)"
  shows "P = integer_hull P" 
proof(cases "P = {}")
  case True
  then show ?thesis 
    by (metis A P_def b int_hull_subset subset_empty)
next
  case False
  obtain C d nr' where C_d:"C \<in> carrier_mat nr' n \<and>
                            d \<in> carrier_vec nr' \<and> 
                            integer_hull P = polyhedron C d"
    using gram_schmidt_floor.integer_hull_of_polyhedron[of A nr n b P] assms 
    by blast
  have "\<exists> Bnd. Bnd =  Max (abs ` (elements_mat A \<union> vec_set b))" 
    by blast
  have "integer_hull P \<noteq> {}"
  proof(rule ccontr)
    assume "\<not> integer_hull P \<noteq> {}"
    then have "convex_hull (P \<inter> \<int>\<^sub>v) = {}" unfolding integer_hull_def  
      by argo
    then have "P \<inter> \<int>\<^sub>v = {}" using set_in_convex_hull 
      by (metis A Diff_empty P_def \<open>\<not> integer_hull P \<noteq> {}\<close> b disjoint_iff_not_equal
          gram_schmidt.not_in_int_hull_not_int)
    have "nr > 0"
    proof(rule ccontr)
      assume "\<not> 0 < nr"
      then have "nr = 0" by auto
      then have "\<forall> x. A *\<^sub>v x \<le> b" 
        by (metis A b carrier_matD(1) carrier_vecD leq_for_all_index_then_eq less_nat_zero_code)
      then have "P = carrier_vec n " 
        unfolding P_def polyhedron_def 
        by fast 
      have "0\<^sub>v n \<in> \<int>\<^sub>v" 
        using zero_vec_is_int by blast
      then show False using `P \<inter> \<int>\<^sub>v = {}` 
        using \<open>P = carrier_vec n\<close> by blast
    qed

    then obtain i where "i < nr" by auto
    then have "has_Maximum { row A i \<bullet> x | x. x \<in> P}" using eq_in_P_has_max 
      using A False P_def b by blast
    then have "\<exists>x. x \<in> P \<and> row A i \<bullet> x = Maximum { row A i \<bullet> x | x. x \<in> P} \<and> x \<in> \<int>\<^sub>v" 
      using assms(6)
      by (meson A \<open>i < nr\<close> row_carrier_vec)
    then show False 
      using \<open>P \<inter> \<int>\<^sub>v = {}\<close> by blast
  qed
  show ?thesis
  proof(rule ccontr)
    assume"P \<noteq> integer_hull P"
    then obtain y where y: "y \<in> P - integer_hull P" 
      by (metis A Diff_iff P_def b int_hull_subset set_eq_subset subset_iff)
    then have "y \<in> carrier_vec n" 
      unfolding P_def polyhedron_def 
      by blast
    have "y \<notin> polyhedron C d" 
      using C_d y 
      by blast                                                 
    then obtain j where "j<nr' \<and> row C j \<bullet> y > d $ j" 
      using y exists_eq_in_P_for_outside_elem [of C nr' d y] C_d  
        `y \<in> carrier_vec n` 
      by blast
    let ?\<alpha> = "row C j"
    let ?\<beta> = "d $ j"
    have "?\<alpha> \<in> carrier_vec n" 
      by (meson C_d \<open>j < nr' \<and> d $ j < row C j \<bullet> y\<close> row_carrier_vec)
    have " has_Maximum { ?\<alpha> \<bullet> x | x. x \<in> P}" 
      using int_hull_bound_then_poly_bounded[of A nr b ?\<alpha>] 
      using A AI C_d False P_def \<open>integer_hull P \<noteq> {}\<close> \<open>j < nr' \<and> d $ j < row C j \<bullet> y\<close> 
        assms(6) b bI eq_in_P_has_max by force
    then obtain x where x:"x \<in> P \<and> ?\<alpha> \<bullet> x = Maximum { ?\<alpha> \<bullet> x | x. x \<in> P}  \<and> x \<in> \<int>\<^sub>v" 
      using assms(6)  
      by (meson \<open>row C j \<in> carrier_vec n\<close>) 
    then have "?\<alpha> \<bullet> y \<le> ?\<alpha> \<bullet> x" 
      using \<open>has_Maximum {row C j \<bullet> x |x. x \<in> P}\<close> has_MaximumD(2) y by fastforce
    have "x \<in> integer_hull P" unfolding integer_hull_def 
      by (metis (no_types, lifting) A Diff_iff P_def x b integer_hull_def not_in_int_hull_not_int)
    have "?\<alpha> \<bullet> x \<le> d $ j" 
    proof -
      have "x \<in> polyhedron C d" using C_d `x \<in> integer_hull P` by auto
      then have "x \<in> carrier_vec n \<and> C *\<^sub>v x \<le> d" unfolding polyhedron_def by auto
      then show ?thesis unfolding mult_mat_vec_def 
        by (metis C_d \<open>j < nr' \<and> d $ j < row C j \<bullet> y\<close> \<open>x \<in> carrier_vec n \<and> C *\<^sub>v x \<le> d\<close>
            carrier_matD(1) carrier_vecD index_mult_mat_vec less_eq_vec_def)
    qed
    then have "?\<alpha> \<bullet> y \<le> d $ j" 
      using \<open>row C j \<bullet> y \<le> row C j \<bullet> x\<close> by linarith
    then show False 
      using \<open>j < nr' \<and> d $ j < row C j \<bullet> y\<close> linorder_not_le by blast
  qed
qed

lemma min_face_iff_int_polyh:
  fixes A :: "'a  mat"
  fixes b:: "'a vec" 
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
    and AI: "A \<in> \<int>\<^sub>m"
    and bI: "b \<in> \<int>\<^sub>v"
  defines "P \<equiv> polyhedron A b"
  shows "(\<forall> F. min_face P F \<longrightarrow> (\<exists> x \<in> F. x \<in> \<int>\<^sub>v)) \<longleftrightarrow> P = integer_hull P"
proof
  have carr_P: "P \<subseteq> carrier_vec n" unfolding P_def polyhedron_def by auto
  show " \<forall>F. min_face P F \<longrightarrow> (\<exists>x\<in>F. x \<in> \<int>\<^sub>v) \<Longrightarrow> P = integer_hull P"
  proof -
    assume asm: "\<forall>F. min_face P F \<longrightarrow> (\<exists>x\<in>F. x \<in> \<int>\<^sub>v)"

    have "(\<forall> F. face P F \<longrightarrow> (\<exists> x \<in> F. x \<in> \<int>\<^sub>v))"
      using A asm assms(2) assms(5) int_all_min_faces_then_int_all_faces by presburger
    then have "\<forall> \<alpha> \<in> carrier_vec n. has_Maximum { \<alpha> \<bullet> x | x. x \<in> P} \<longrightarrow>
   (\<exists>x. x \<in> P \<and> \<alpha> \<bullet> x = Maximum { \<alpha> \<bullet> x | x. x \<in> P}  \<and> x \<in> \<int>\<^sub>v)"
      using int_face_then_max_suphyp_int carr_P by fastforce
    then show "P = integer_hull P" using int_support_hyp_then_int_polyhedron[OF A b AI bI] 
      using assms(5) by fastforce
  qed
  show  "P = integer_hull P \<Longrightarrow> \<forall>F. min_face P F \<longrightarrow> (\<exists>x\<in>F. x \<in> \<int>\<^sub>v)" 
    using carr_P
    by (metis P_int_then_face_int gram_schmidt.min_face_elim(1))
qed

lemma face_iff_int_polyh:
  fixes A :: "'a  mat"
  fixes b:: "'a vec" 
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
    and AI: "A \<in> \<int>\<^sub>m"
    and bI: "b \<in> \<int>\<^sub>v"
  defines "P \<equiv> polyhedron A b"
  shows "(\<forall> F. face P F \<longrightarrow> (\<exists> x \<in> F. x \<in> \<int>\<^sub>v)) \<longleftrightarrow> P = integer_hull P"
proof
  have carr_P: "P \<subseteq> carrier_vec n" unfolding P_def polyhedron_def by auto
  show " \<forall>F. face P F \<longrightarrow> (\<exists>x\<in>F. x \<in> \<int>\<^sub>v) \<Longrightarrow> P = integer_hull P"
  proof -
    assume asm: "\<forall>F. face P F \<longrightarrow> (\<exists>x\<in>F. x \<in> \<int>\<^sub>v)"
    then have "\<forall> \<alpha> \<in> carrier_vec n. has_Maximum { \<alpha> \<bullet> x | x. x \<in> P} \<longrightarrow>
   (\<exists>x. x \<in> P \<and> \<alpha> \<bullet> x = Maximum { \<alpha> \<bullet> x | x. x \<in> P}  \<and> x \<in> \<int>\<^sub>v)"
      using int_face_then_max_suphyp_int carr_P by fastforce
    then show "P = integer_hull P" using int_support_hyp_then_int_polyhedron[OF A b AI bI] 
      using assms(5) by fastforce
  qed
  show  "P = integer_hull P \<Longrightarrow> \<forall>F. face P F \<longrightarrow> (\<exists>x\<in>F. x \<in> \<int>\<^sub>v)" 
    using carr_P
    by (metis P_int_then_face_int)
qed

end
end