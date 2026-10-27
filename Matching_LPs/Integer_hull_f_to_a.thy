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
  have hull_carr: "convex_hull (P \<inter> \<int>\<^sub>v) \<subseteq> carrier_vec n"
    using int_in_carr convex_hull_carrier by blast
  have int_carr: "convex_hull (P \<inter> \<int>\<^sub>v) \<inter> \<int>\<^sub>v \<subseteq> carrier_vec n"
    using hull_carr by blast
  have conv: "convex (convex_hull (P \<inter> \<int>\<^sub>v))"
    using int_in_carr convex_hulls_are_convex by blast
  have idem: "convex_hull (convex_hull (P \<inter> \<int>\<^sub>v)) = convex_hull (P \<inter> \<int>\<^sub>v)"
    using conv hull_carr convex_convex_hull by blast
  have sub_hull: "convex_hull (P \<inter> \<int>\<^sub>v) \<inter> \<int>\<^sub>v \<subseteq> convex_hull (P \<inter> \<int>\<^sub>v)"
    by blast
  have le1: "convex_hull (convex_hull (P \<inter> \<int>\<^sub>v) \<inter> \<int>\<^sub>v) \<subseteq> convex_hull (P \<inter> \<int>\<^sub>v)"
  proof -
    have "convex_hull (convex_hull (P \<inter> \<int>\<^sub>v) \<inter> \<int>\<^sub>v)
            \<subseteq> convex_hull (convex_hull (P \<inter> \<int>\<^sub>v))"
      using sub_hull hull_carr convex_hull_mono by blast
    then show ?thesis
      by (simp add: idem)
  qed
  have le2: "convex_hull (P \<inter> \<int>\<^sub>v) \<subseteq> convex_hull (convex_hull (P \<inter> \<int>\<^sub>v) \<inter> \<int>\<^sub>v)"
  proof -
    have "P \<inter> \<int>\<^sub>v \<subseteq> convex_hull (P \<inter> \<int>\<^sub>v) \<inter> \<int>\<^sub>v"
      using int_in_carr set_in_convex_hull by blast
    then show ?thesis
      using int_carr convex_hull_mono by blast
  qed
  show ?thesis
    unfolding integer_hull_def
    using le1 le2 by blast
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
    have fin: "finite I"
      using False by simp
    have A'_fst: "A' = fst (sub_system A b I)"
      using assms(3)[symmetric] by simp
    have le: "dim_row A' \<le> card I"
      using dim_row_less_card_I[of I A b] fin A'_fst by simp
    have j1_card: "j1 < card I"
      using assms(4) le by linarith
    have j2_card: "j2 < card I"
      using assms(5) le by linarith
    have "pick I j1 \<noteq> pick I j2"
    proof (cases j1 j2 rule: linorder_cases)
      case less
      then have "pick I j1 < pick I j2"
        using pick_mono_le j2_card fin by blast
      then show "pick I j1 \<noteq> pick I j2" by linarith
    next
      case equal
      then show "pick I j1 \<noteq> pick I j2"
        using assms(6) by simp
    next
      case greater
      then have "pick I j2 < pick I j1"
        using pick_mono_le j1_card fin by blast
      then show "pick I j1 \<noteq> pick I j2" by linarith
    qed
    then show ?thesis
      using assms(1) assms(2) by simp
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
  proof -
    have face_P_F: "face P F"
      by (rule min_face_elim(1)[OF assms(5)])
    show thesis
      using that face_P_F by (blast elim!: faceE)
  qed
  have face_P_F: "face P F"
    by (rule min_face_elim(1)[OF assms(5)])
  obtain C d where C_d: "F = polyhedron C d"  "dim_row C = dim_vec d" "dim_col C = n" 
    using face_is_polyhedron[OF A b face_P_F[unfolded P_def]] by blast
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
    proof (intro ballI)
    have F_eq: "F = {v. v \<in> carrier_vec n \<and> C *\<^sub>v v \<le> d}"
      using C_d(1) by (simp add: polyhedron_def)
    fix x
    assume "x \<in> F"
    then have "x \<in> {v. v \<in> carrier_vec n \<and> C *\<^sub>v v \<le> d}"
      using F_eq by simp
    then show "x \<in> carrier_vec n"
      by blast
  qed
    then obtain i where i:"i < n \<and> x $ i \<noteq> y $ i"
    proof -
      have xF: "x \<in> F" and yF: "y \<in> F" and xy: "x \<noteq> y"
        using x_y by blast+
      have xc: "x \<in> carrier_vec n" and yc: "y \<in> carrier_vec n"
        using xF yF \<open>\<forall>x\<in>F. x \<in> carrier_vec n\<close> by blast+
      have dx: "dim_vec x = n" and dy: "dim_vec y = n"
        using xc yc carrier_vecD by blast+
      have "\<exists>i<n. x $ i \<noteq> y $ i"
      proof (rule ccontr)
        assume contr: "\<not> (\<exists>i<n. x $ i \<noteq> y $ i)"
        have "x = y"
        proof (rule eq_vecI)
          fix i
          assume "i < dim_vec y"
          then have "i < n" using dy by simp
          then show "x $ i = y $ i" using contr by blast
        next
          show "dim_vec x = dim_vec y" using dx dy by simp
        qed
        then show False using xy by blast
      qed
      then show thesis using that by blast
    qed
    have "\<exists>\<beta>\<^sub>i. \<forall>x\<in>F. x $ i = \<beta>\<^sub>i" 
      using \<open>\<forall>i<n. \<exists>\<beta>\<^sub>i. \<forall>x\<in>F. x $ i = \<beta>\<^sub>i\<close> i by presburger
    then show False 
    proof (elim exE)
      fix \<gamma>
      assume gamma: "\<forall>z \<in> F. z $ i = \<gamma>"
      have "x $ i = \<gamma>"
        using gamma x_y by blast
      moreover have "y $ i = \<gamma>"
        using gamma x_y by blast
      ultimately have "x $ i = y $ i"
        by simp
      then show False
        using i by simp
    qed
  qed
  then show "card F = 1" 
  proof -
    from \<open>\<exists>!x. x \<in> F\<close> obtain x
      where x_in: "x \<in> F" and x_uniq: "\<And>y. y \<in> F \<Longrightarrow> y = x"
      by blast
    have "F \<subseteq> {x}" using x_uniq by blast
    moreover have "{x} \<subseteq> F" using x_in by blast
    ultimately have "F = {x}" by (rule subset_antisym)
    then show "card F = 1" by simp
  qed
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
  proof -
    have face_P_F: "face P F"
      by (rule min_face_elim(1)[OF assms(5)])
    have "\<exists>\<alpha> \<beta>. support_hyp P \<alpha> \<beta> \<and> F = P \<inter> {x |x. \<alpha> \<bullet> x = \<beta>}"
      using face_P_F unfolding face_def by blast
    then show ?thesis
      using that by blast
  qed
  obtain C d where C_d: "F = polyhedron C d"  "dim_row C = dim_vec d" "dim_col C = n" 
    proof -
      have face_F: "face P F"
        using min_face_elim(1)[OF assms(5)] .
      then have face_F': "face (polyhedron A b) F"
        unfolding P_def .
      show thesis
        using face_is_polyhedron[OF A b face_F'] that by blast
    qed
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
    proof -
      have inF: "\<forall>x \<in> carrier_vec n. C *\<^sub>v x \<le> d \<longrightarrow> x \<in> F"
        unfolding C_d(1) polyhedron_def by blast
      show ?thesis
        using inF \<open>\<forall> x \<in> F. - unit_vec n i  \<bullet> x \<le> - bound\<close> by blast
    qed
    then have "has_Maximum {- unit_vec n i  \<bullet> x | x. x \<in> carrier_vec n \<and> C *\<^sub>v x \<le> d}"
      using strong_duality_theorem_primal_sat_bounded_min_max(2)
          [OF carrier_matI[OF C_d(2) C_d(3)] carrier_vecI[OF refl]
               uminus_carrier_vec[THEN iffD2, OF unit_vec_carrier]
               `\<exists>x\<in>carrier_vec n. C *\<^sub>v x \<le> d`]
      by blast
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
    proof -
      assume key: "\<forall>x\<in>F. - unit_vec n i \<bullet> x = \<beta>\<^sub>i"
      have "\<forall>x\<in>F. x $ i = - \<beta>\<^sub>i"
      proof (rule ballI)
        fix x
        assume xF: "x \<in> F"
        then have xc: "x \<in> carrier_vec n"
          using C_d(1) by (simp add: polyhedron_def)
        have key_x: "(- unit_vec n i) \<bullet> x = \<beta>\<^sub>i"
          using key xF by blast
        have neg: "(- unit_vec n i) \<bullet> x = - (x $ i)"
        proof -
          have "(- unit_vec n i) \<bullet> x = - (unit_vec n i \<bullet> x)"
            using xc unit_vec_carrier by (simp add: uminus_scalar_prod)
          also have "\<dots> = - (x $ i)"
            using xc \<open>i < n\<close> by (simp add: scalar_prod_left_unit)
          finally show ?thesis .
        qed
        have "x $ i = - ((- unit_vec n i) \<bullet> x)"
          using neg by simp
        then show "x $ i = - \<beta>\<^sub>i"
          using key_x by simp
      qed
      then show ?thesis by blast
    qed
  qed
  have "\<exists>! x. x \<in> F" 
  proof(rule ccontr)
    assume "\<nexists>!x. x \<in> F"
    then obtain x y where x_y:"x \<in> F \<and> y \<in> F \<and> x \<noteq> y" 
      using \<open>F \<noteq> {}\<close> by blast
    have "\<forall>x \<in> F. x  \<in> carrier_vec n" 
    proof (intro ballI)
      fix x
      assume "x \<in> F"
      then have "x \<in> {v. v \<in> carrier_vec n \<and> C *\<^sub>v v \<le> d}"
        using C_d(1) by (simp add: polyhedron_def)
      then show "x \<in> carrier_vec n"
        by blast
    qed
    then obtain i where i:"i < n \<and> x $ i \<noteq> y $ i"
      proof -
      have xc: "x \<in> carrier_vec n"
        using x_y \<open>\<forall>x \<in> F. x  \<in> carrier_vec n\<close> by blast
      have yc: "y \<in> carrier_vec n"
        using x_y \<open>\<forall>x \<in> F. x  \<in> carrier_vec n\<close> by blast
      have dx: "dim_vec x = n" using xc by (rule carrier_vecD)
      have dy: "dim_vec y = n" using yc by (rule carrier_vecD)
      have "\<exists>i<n. x $ i \<noteq> y $ i"
      proof (rule ccontr)
        assume "\<not> (\<exists>i<n. x $ i \<noteq> y $ i)"
        then have eq: "\<And>i. i < n \<Longrightarrow> x $ i = y $ i" by blast
        have "x = y"
        proof (rule eq_vecI)
          fix i
          assume "i < dim_vec y"
          then have "i < n" by (simp add: dy)
          then show "x $ i = y $ i" by (rule eq)
        next
          show "dim_vec x = dim_vec y" by (simp add: dx dy)
        qed
        then show False using x_y by simp
      qed
      then show thesis using that by blast
    qed
    have "\<exists>\<beta>\<^sub>i. \<forall>x\<in>F. x $ i = \<beta>\<^sub>i" 
      using \<open>\<forall>i<n. \<exists>\<beta>\<^sub>i. \<forall>x\<in>F. x $ i = \<beta>\<^sub>i\<close> i by presburger
    then show False 
    proof (elim exE)
      fix \<beta>\<^sub>i
      assume beta: "\<forall>x\<in>F. x $ i = \<beta>\<^sub>i"
      have "x $ i = \<beta>\<^sub>i"
        using beta x_y by blast
      moreover have "y $ i = \<beta>\<^sub>i"
        using beta x_y by blast
      ultimately have "x $ i = y $ i"
        by simp
      then show False
        using i by simp
    qed
  qed
  then show "card F = 1" 
  proof -
    from \<open>\<exists>!x. x \<in> F\<close> obtain v where vF: "v \<in> F" and vuniq: "\<forall>y. y \<in> F \<longrightarrow> y = v"
      by blast
    have "F = {v}"
    proof (intro equalityI subsetI)
      fix y assume "y \<in> F"
      then have "y = v" using vuniq by blast
      then show "y \<in> {v}" by simp
    next
      fix y assume "y \<in> {v}"
      then have "y = v" by simp
      then show "y \<in> F" using vF by simp
    qed
    then show "card F = 1" by simp
  qed
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
    proof -
      have "dim_row A = nr"
        using assms(1) by (rule carrier_matD(1))
      moreover have "dim_vec b = nr"
        using assms(2) by (rule carrier_vecD)
      ultimately show ?thesis by simp
    qed
  assume "\<not> distinct (Matrix.rows A') "
  then obtain j1 j2 where j1j2: "j1 \<noteq> j2 \<and> j1 < dim_row A' \<and> 
                                 j2 < dim_row A' \<and> row A' j1 = row A' j2" 
  proof -
    assume nd: "\<not> distinct (Matrix.rows A')"
    have len: "length (Matrix.rows A') = dim_row A'"
      by (simp add: length_rows)
    from nd have "\<not> (\<forall>i<length (Matrix.rows A'). \<forall>j<length (Matrix.rows A').
                       i \<noteq> j \<longrightarrow> Matrix.rows A' ! i \<noteq> Matrix.rows A' ! j)"
      by (unfold distinct_conv_nth)
    then obtain k1 k2
      where k1: "k1 < length (Matrix.rows A')"
        and k2: "k2 < length (Matrix.rows A')"
        and kneq: "k1 \<noteq> k2"
        and keq: "Matrix.rows A' ! k1 = Matrix.rows A' ! k2"
      by blast
    have k1': "k1 < dim_row A'" using k1 len by simp
    have k2': "k2 < dim_row A'" using k2 len by simp
    have "row A' k1 = row A' k2"
      using keq k1' k2' by (simp add: nth_rows)
    with kneq k1' k2'
    have "k1 \<noteq> k2 \<and> k1 < dim_row A' \<and> k2 < dim_row A' \<and> row A' k1 = row A' k2"
      by blast
    then show thesis by (rule that)
  qed
  obtain i1 where i1:"i1 < dim_row A \<and> i1 \<in> I \<and> row A i1 = row A' j1 \<and>
                      i1 = (pick I j1) \<and> b' $ j1 = b $ i1" 
  proof -
  have A'_eq: "A' = fst (sub_system A b I)"
    using assms(8)[symmetric] by simp
  have b'_eq: "b' = snd (sub_system A b I)"
    using assms(8)[symmetric] by simp
  have dims_A'b': "dim_row A' = dim_vec b'"
    using dims_subsyst_same[OF dims_eq] by (simp add: A'_eq b'_eq)
  have j1_A': "j1 < dim_row A'"
    using j1j2 by simp
  have j1_b': "j1 < dim_vec b'"
    using j1_A' dims_A'b' by simp
  have j1_snd: "j1 < dim_vec (snd (sub_system A b I))"
    using j1_b' by (simp add: b'_eq)
  obtain i where i_dimB: "i < dim_vec b" and i_I: "i \<in> I"
    and i_row: "row A' j1 = row A i" and i_pick: "i = pick I j1"
    and i_b: "b' $ j1 = b $ i"
    using exist_index_in_A[OF dims_eq j1_snd] by (simp add: A'_eq b'_eq)
  have i_dim: "i < dim_row A"
    using i_dimB by (simp add: dims_eq)
  have i_row': "row A i = row A' j1"
    using i_row by (rule sym)
  have i_b': "b $ i = b' $ j1"
    using i_b by (rule sym)
  have i_all: "i < dim_row A \<and> i \<in> I \<and> row A i = row A' j1 \<and> i = pick I j1 \<and> b' $ j1 = b $ i"
    using i_dim i_I i_row' i_pick i_b by simp
  from i_all show thesis by (rule that)
  qed
  obtain i2 where i2: "i2 < dim_row A \<and> i2 \<in> I \<and> row A i2 = row A' j2 \<and> 
                       i2 = (pick I j2) \<and> b' $ j2 = b $ i2" 
  proof -
  have dims_A'b': "dim_row A' = dim_vec b'"
    using dims_subsyst_same[OF dims_eq, of I]
    by (simp add: assms(8)[symmetric])
  have j2_dim: "j2 < dim_vec b'"
    using j1j2 dims_A'b' by simp
  have j2_snd: "j2 < dim_vec (snd (sub_system A b I))"
    using j2_dim by (simp add: assms(8)[symmetric])
  have "\<exists>i. i < dim_row A \<and> i \<in> I \<and> row A i = row A' j2 \<and>
             i = pick I j2 \<and> b' $ j2 = b $ i"
    using exist_index_in_A[OF dims_eq j2_snd] by (simp add: assms(8)[symmetric] dims_eq)
  then show thesis
    using that by blast
  qed
  then have "i1 \<noteq> i2" using subsyst_indx_neq_syst_indx_neq[of i1 I j1 i2 j2 A' b' A b] 
    using i1 j1j2 assms(8) by presburger
  have " b $ i1 =  b $ i2" 
  proof(rule ccontr)
    assume "b $ i1 \<noteq> b $ i2"
    then have "b' $ j1 \<noteq> b' $ j2" using i1 i2 by auto
    obtain x where "x \<in> F" 
      proof -
      have "face P F"
        using min_face_elim(1)[OF assms(5)] by blast
      then have "F \<noteq> {}"
        by (rule face_non_empty)
      then show thesis
        using that by blast
    qed
    then have "x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'" 
      using assms(7) by blast
    have "row A' j1 = row A' j2" using j1j2 
      by blast
    show False
    proof -
      have j1_lt: "j1 < dim_row A'" and j2_lt: "j2 < dim_row A'"
        and rows_eq: "row A' j1 = row A' j2"
        using j1j2 by simp_all
      have Ax: "A' *\<^sub>v x = b'"
        using \<open>x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'\<close> by simp
      have "b' $ j1 = (A' *\<^sub>v x) $ j1"
        using Ax by simp
      also have "\<dots> = row A' j1 \<bullet> x"
        by (rule index_mult_mat_vec[OF j1_lt])
      also have "\<dots> = row A' j2 \<bullet> x"
        using rows_eq by simp
      also have "\<dots> = (A' *\<^sub>v x) $ j2"
        by (rule index_mult_mat_vec[OF j2_lt, symmetric])
      also have "\<dots> = b' $ j2"
        using Ax by simp
      finally have "b' $ j1 = b' $ j2" .
      then show False
        using \<open>b' $ j1 \<noteq> b' $ j2\<close> by simp
    qed
  qed
  obtain C d where C_d: "(C, d) = sub_system A b (I - {i1})"
    by (rule that[OF prod.collapse])
  have "{x.  A' *\<^sub>v x = b'} = {x.  C *\<^sub>v x = d \<and> row A i1 \<bullet> x = b $ i1 }"
  proof -
    have dim_Ab: "dim_row A = dim_vec b"
      using carrier_matD(1)[OF A] carrier_vecD[OF b] by simp
    have i1_in: "i1 \<in> I"
      using i1 by blast
    have i1_lt: "i1 < dim_vec b"
      using i1 dim_Ab by fastforce
    show ?thesis
      using remove_index_sub_system_eq[OF dim_Ab i1_in i1_lt assms(8) C_d] .
  qed
  have "\<forall>x.  C *\<^sub>v x = d \<longrightarrow> row A i1 \<bullet> x = b $ i1"
  proof(safe)
    fix x
    assume "d = C *\<^sub>v x" 
    have "i2 \<in> I - {i1}" 
      using \<open>i1 \<noteq> i2\<close> i2 by blast
    then obtain j where j: "j < dim_row C \<and> row A i2 = row C j \<and> b $ i2 = d $ j" 
      proof -
        have i2_mem: "i2 \<in> I - {i1}"
          using i2 \<open>i1 \<noteq> i2\<close> by blast
        have i2_dim: "i2 < dim_vec b"
          using i2 dims_eq by simp
        have sub_C_d: "sub_system A b (I - {i1}) = (C, d)"
          using C_d by simp
        have dimsC: "dim_row C = dim_vec d"
          by (rule dims_subsyst_same'[OF dims_eq C_d])
        have "\<exists>j. j < dim_row C \<and> row A i2 = row C j \<and> b $ i2 = d $ j"
          using exist_index_in_A'[OF dims_eq i2_dim i2_mem]
          by (auto simp: sub_C_d dimsC)
        then show ?thesis
          using that by blast
      qed
    then have "row A i1 = row C j \<and> b $ i1 = d $ j" 
      proof -
        have rA2: "row A i2 = row A' j2"
          using i2 by blast
        have "row A i1 = row A' j1"
          using i1 by blast
        also have "\<dots> = row A' j2"
          using j1j2 by blast
        also have "\<dots> = row A i2"
          using rA2 by (rule sym)
        also have "\<dots> = row C j"
          using j by blast
        finally have rows_eq: "row A i1 = row C j" .
        have bs_eq: "b $ i1 = d $ j"
        proof -
          have "b $ i2 = d $ j"
            using j by blast
          with \<open>b $ i1 = b $ i2\<close> show ?thesis
            by (rule trans)
        qed
        from rows_eq bs_eq show ?thesis
          by (rule conjI)
      qed
    then have "row C j \<bullet> x = d $ j" using `d = C *\<^sub>v x`  j 
      proof -
        have jlt: "j < dim_row C"
          using j by blast
        have "row C j \<bullet> x = (C *\<^sub>v x) $ j"
          using jlt by simp
        also have "\<dots> = d $ j"
          using \<open>d = C *\<^sub>v x\<close> by simp
        finally show ?thesis .
      qed
    then show "row A i1 \<bullet> x = b $ i1" 
      proof -
      have "row A i1 = row A' j1" using i1 by blast
      also have "\<dots> = row A' j2" using j1j2 by simp
      also have "\<dots> = row A i2" using i2[THEN conjunct2, THEN conjunct2, THEN conjunct1] by simp
      also have "\<dots> = row C j" using j by simp
      finally have row_eq: "row A i1 = row C j" .
      have "row A i1 \<bullet> x = row C j \<bullet> x" using row_eq by simp
      also have "\<dots> = d $ j" using \<open>row C j \<bullet> x = d $ j\<close> by simp
      also have "\<dots> = b $ i2" using j by simp
      also have "\<dots> = b $ i1" using \<open>b $ i1 = b $ i2\<close> by simp
      finally show "row A i1 \<bullet> x = b $ i1" .
    qed
  qed
  then have "{x.  A' *\<^sub>v x = b'} = {x. C *\<^sub>v x = d}"
    using \<open>{x. A' *\<^sub>v x = b'} = {x. C *\<^sub>v x = d \<and> row A i1 \<bullet> x = b $ i1}\<close> by blast
  have "dim_vec d + 1 = dim_vec b'" 
  proof -
    have i1_I: "i1 \<in> I"
      using i1 by blast
    have i1_A: "i1 < dim_row A"
      using i1 by blast
    have i1_b: "i1 < dim_vec b"
      using i1 dims_eq by auto
    have Ab: "dim_row A = dim_vec b"
      using dims_eq by simp
    have bA: "dim_vec b = dim_row A"
      using dims_eq by simp
    have sub_I: "(A', b') = sub_system A b I"
      using assms(8) by simp
    have sub_I': "(C, d) = sub_system A b (I - {i1})"
      using C_d by simp
    show ?thesis
      using remove_index_sub_system_dims[of i1 I b A' b' A C d,
        OF i1_I i1_b sub_I sub_I']
      by simp
  qed
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
proof -
  have A'_eq: "A' = fst (sub_system A b I)"
    by (simp add: assms(2)[symmetric])
  have dim_A: "dim_col A = n"
    by (rule carrier_matD(2)[OF assms(1)])
  have dim_A': "dim_col A' = n"
    using dim_col_subsyst_mat[of A b I] dim_A by (simp add: A'_eq)
  have "set (rows A') \<subseteq> carrier_vec (dim_col A')"
    by (rule rows_carrier)
  then show ?thesis
    by (simp add: dim_A')
qed

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
proof -
  have maps_eq: "map f L = map g L"
  proof (rule map_cong)
    show "L = L" by (rule refl)
  next
    fix x
    assume "x \<in> set L"
    then show "f x = g x" using assms by blast
  qed
  show ?thesis by (simp only: maps_eq)
qed

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
  proof -
    have "u \<in> set (rows A')"
      using u by blast
    then obtain k where "k < length (rows A')" "rows A' ! k = u"
      by (auto simp: in_set_conv_nth)
    then show thesis
      using that by blast
  qed
  then have j:"j < dim_row A' \<and> row A' j = u" using nth_rows length_rows 
    proof -
    have jlen: "j < length (rows A')" and jnth: "rows A' ! j = u"
      using \<open>j < length (rows A') \<and> rows A' ! j = u\<close> by auto
    have jlt: "j < dim_row A'"
      using jlen by (simp add: length_rows)
    moreover have "row A' j = u"
      using jlt jnth by (simp add: nth_rows)
    ultimately show ?thesis
      by (rule conjI)
  qed
  obtain i where i:"i < dim_row A \<and> i \<in> I \<and> row A i = row A' j \<and> i = (pick I j) \<and>  b $ i = b' $ j" 
  proof -
  have sub_eq: "sub_system A b I = (A', b')"
    by (rule assms(8)[symmetric])
  have fstA': "fst (sub_system A b I) = A'"
    by (simp add: sub_eq)
  have sndb': "snd (sub_system A b I) = b'"
    by (simp add: sub_eq)
  have jvec: "j < dim_vec (snd (sub_system A b I))"
    using j dims_subsyst_same[OF dim_sameAb, of I] by (simp add: fstA' sndb')
  obtain i0 where i0:
      "i0 < dim_vec b" "i0 \<in> I"
      "row (fst (sub_system A b I)) j = row A i0"
      "snd (sub_system A b I) $ j = b $ i0"
      "i0 = pick I j"
    using exist_index_in_A[OF dim_sameAb jvec] by auto
  have "i0 < dim_row A \<and> i0 \<in> I \<and> row A i0 = row A' j \<and> i0 = pick I j \<and> b $ i0 = b' $ j"
    using i0 by (simp add: fstA' sndb' dim_sameAb)
  then show thesis
    by (rule that)
  qed
  obtain C d where C_d: "(C, d) = sub_system A b (I - {i})"
    by (rule that[OF prod.collapse])
  have 4: "{x. A' *\<^sub>v x = b'} = {x.  C *\<^sub>v x = d \<and> row A i \<bullet> x = b $ i }"
    using remove_index_sub_system_eq[of A b i I A' b' C d]  C_d assms(8) dim_sameAb i by linarith 
  have "u \<in> carrier_vec n" 
    using carrA' u by blast
  have Cd_non_empty: "{x. x \<in> carrier_vec n \<and>  C *\<^sub>v x = d \<and> row A' j \<bullet> x = b' $ j } \<noteq> {}" 
  proof -
    have facePF: "face P F"
      using assms(5) by (rule min_face_elim(1))
    have "F \<noteq> {}"
      using face_non_empty[OF facePF] .
    then obtain x where xF: "x \<in> F" by blast
    have x_carr: "x \<in> carrier_vec n"
      using xF assms(7) by simp
    have x_eq: "A' *\<^sub>v x = b'"
      using xF assms(7) by simp
    have split: "C *\<^sub>v x = d \<and> row A i \<bullet> x = b $ i"
    proof -
      from 4 have "(A' *\<^sub>v x = b') \<longleftrightarrow> (C *\<^sub>v x = d \<and> row A i \<bullet> x = b $ i)"
        by (simp add: set_eq_iff)
      then show ?thesis using x_eq by blast
    qed
    have Cx: "C *\<^sub>v x = d" using split by blast
    have rx: "row A i \<bullet> x = b $ i" using split by blast
    have rowj: "row A i = row A' j" using i by blast
    have bj: "b $ i = b' $ j" using i by blast
    have rowjx: "row A' j \<bullet> x = b' $ j"
    proof -
      have "row A' j \<bullet> x = row A i \<bullet> x" using rowj by simp
      also have "\<dots> = b $ i" using rx by simp
      also have "\<dots> = b' $ j" using bj by simp
      finally show ?thesis .
    qed    have "x \<in> {x. x \<in> carrier_vec n \<and>  C *\<^sub>v x = d \<and> row A' j \<bullet> x = b' $ j }"
      using x_carr Cx rowjx by simp
    then show ?thesis by blast
  qed
  have "\<forall>x \<in> carrier_vec n.  C *\<^sub>v x = d \<longrightarrow> row A i \<bullet> x = b $ i"
  proof(cases "u \<in> set (rows C)")
    case True
    then obtain j' where "j' < length (rows C) \<and> (rows C) ! j' = u"  
      by (meson in_set_conv_nth)
    then have  j': "j' < dim_row C \<and> row C  j' = u"
    proof -
      assume asm: "j' < length (rows C) \<and> (rows C) ! j' = u"
      have len: "j' < dim_row C"
        using asm by (simp add: length_rows)
      have "row C j' = rows C ! j'"
        using nth_rows[OF len] by simp
      then have "row C j' = u"
        using asm by simp
      with len show ?thesis by blast
    qed    obtain i' where i':"i' < nr \<and> i' \<in> (I - {i}) \<and> row A i' = row C j' \<and> d $ j' = b $ i'" 
      proof -
    have jC: "j' < dim_row C"
      using j' by blast
    have "\<exists>k. k < nr \<and> k \<in> I - {i} \<and> row A k = row C j' \<and> d $ j' = b $ k"
      using exist_index_in_A_carr[of A nr n b C d "I - {i}" j'] A b C_d jC
      by auto
    then show thesis
      using that by blast
  qed
    then show ?thesis 
      by (smt (verit, best) Cd_non_empty Collect_empty_eq i index_mult_mat_vec j j')
  next
    case False
    have "set (rows C) \<subseteq> carrier_vec n"
      using subsyst_rows_carr  C_d assms(1) by blast
    have "set (rows C) = set (rows A') - {u}" 
      using remove_index_remove_row[of A b i I A' b' C d]
    proof -
      have rowAi: "row A i = row A' j"
        using i by blast
      have rowA'j: "row A' j = u"
        using j by blast
      have u_eq: "row A i = u"
        using rowAi rowA'j by simp
      have i_in_I: "i \<in> I"
        using i by blast
      have i_dim: "i < dim_row A"
        using i by blast
      have notin: "row A i \<notin> set (rows C)"
        using False u_eq by simp
      have "set (rows C) = set (rows A') - {row A i}"
        using remove_index_remove_row[of A b i I A' b' C d]
          dim_sameAb i_dim i_in_I assms(8) C_d notin
        by auto
      then show ?thesis
        using u_eq by simp
    qed
    then obtain c where "u = lincomb_list c (rows C)" 
      using  `set (rows C) \<subseteq> carrier_vec n`
    proof -
      note carr = \<open>set (rows C) \<subseteq> carrier_vec n\<close>
      have fin: "finite (set (rows C))"
        by simp
      have "u \<in> span (set (rows C))"
        using u \<open>set (rows C) = set (rows A') - {u}\<close> by simp
      then obtain a where a: "u = lincomb a (set (rows C))"
        using finite_in_span[OF fin carr] by blast
      then have "\<exists>c'. u = lincomb_list c' (rows C)"
        using carr lincomb_then_lincomb_list by blast
      then show thesis
        using that by blast
    qed
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
  proof -
    have eq: "row A i \<bullet> x = b $ i" if "x \<in> carrier_vec n" and "C *\<^sub>v x = d" for x
    proof -
      have "row A i \<bullet> x = row A' j \<bullet> x"
        using i by auto
      also have "\<dots> = sum_list (map (\<lambda>i. c i * d $ i) [0..<length (rows C)])"
        using 6 that by blast
      also have "\<dots> = b' $ j"
        using \<open>b' $ j = sum_list (map (\<lambda>i. c i * d $ i) [0..<length (rows C)])\<close> by simp
      also have "\<dots> = b $ i"
        using i by auto
      finally show ?thesis .
    qed
    show ?thesis
      using eq by blast
  qed
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
  proof -
    assume dep_cols: "lin_dep (set (cols A))"
    show "lin_dep (set (Matrix.rows A))"
    proof (rule ccontr)
      assume indpt: "\<not> lin_dep (set (Matrix.rows A))"
      have cT: "cols A\<^sup>T = Matrix.rows A"
        by (rule cols_transpose)
      have rT: "Matrix.rows A\<^sup>T = cols A"
        by (rule Matrix.rows_transpose)
      have dist: "distinct (cols A\<^sup>T)"
        using assms(3) by (simp add: cT)
      have ind: "lin_indpt (set (cols A\<^sup>T))"
        using indpt by (simp add: cT)
      have "rank A\<^sup>T = n"
        using lin_indpt_full_rank[OF A_t] dist ind by blast
      then have nonzero: "det A\<^sup>T \<noteq> 0"
        using det_rank_iff[OF A_t] by simp
      have "lin_dep (set (Matrix.rows A\<^sup>T))"
        using dep_cols by (simp add: rT)
      then have "det A\<^sup>T = 0"
        using idom_vec.lin_dep_rows_imp_det_0[OF A_t] by blast
      then show False using nonzero by simp
    qed
  qed
qed

lemma mult_unit_vec_is_col:
  fixes A :: "'a  mat"
  assumes "A \<in> carrier_mat nr n"
  assumes "i < n"
  shows "A *\<^sub>v unit_vec n i = col A i" 
proof
  show "dim_vec (A *\<^sub>v unit_vec n i) = dim_vec (col A i)" 
  proof -
    have "dim_vec (A *\<^sub>v unit_vec n i) = dim_row A"
      by simp
    moreover have "dim_vec (col A i) = dim_row A"
      by simp
    ultimately show ?thesis
      by simp
  qed
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
    proof -
      have "dim_row A = nr1"
        using assms(1) by (rule carrier_matD(1))
      with i_dimA have "i < nr1" by simp
      then have "i < nr1 + nr2" by simp
      then show "i < dim_row (A @\<^sub>r B)" by (simp add: AB_dim_row)
    qed
    have j_dimAB:"j < dim_col (A @\<^sub>r B)" 
      proof -
        have "dim_col A = n"
          by (rule carrier_matD(2)[OF assms(1)])
        then show ?thesis
          using AB_dim_col \<open>j < dim_col A\<close> by simp
      qed
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
    proof -
      have row_eq: "row (A @\<^sub>r B) i = row A i"
        using Missing_Matrix.append_rows_nth(1) assms(1) assms(2) i_dimA by blast
      have "(A @\<^sub>r B) $$ (i, j) = row (A @\<^sub>r B) i $ j"
        using i_dimAB j_dimAB by (simp add: index_row(1))
      also have "\<dots> = row A i $ j"
        using row_eq by simp
      also have "\<dots> = A $$ (i, j)"
        using i_dimA j_dimA by (simp add: index_row(1))
      finally show ?thesis .
    qed
      ultimately show "submatrix (A @\<^sub>r B) {0..<nr1} UNIV $$ (i, j) = A $$ (i, j)" 
        by presburger
    qed
  qed
  then have "distinct (cols (submatrix (A @\<^sub>r B) {0..<nr1} UNIV))"
    using assms(3) by simp
  then show ?thesis
    by (rule distinct_cols_submatrix_UNIV)
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
proof -
  have "i < length (rows A)"
    using assms by (simp add: length_rows)
  then have "rows A ! i \<in> set (rows A)"
    by (rule nth_mem)
  then show ?thesis
    using assms by (simp add: nth_rows)
qed

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
        proof -
          assume eq0: "(1 - k) \<cdot>\<^sub>v row A j = 0\<^sub>v n"
          have dim_j: "dim_vec (row A j) = n"
            using carrier_matD(2)[OF assms(1)] by simp
          have "\<exists>l<n. row A j $ l \<noteq> 0"
          proof (rule ccontr)
            assume "\<not> (\<exists>l<n. row A j $ l \<noteq> 0)"
            then have all0: "\<And>l. l < n \<Longrightarrow> row A j $ l = 0" by auto
            have "row A j = 0\<^sub>v n"
              by (rule eq_vecI)
                (auto simp: dim_j all0 carrier_matD(2)[OF assms(1)])
            with False show False by simp
          qed
          then obtain l where l_lt: "l < n" and l_nz: "row A j $ l \<noteq> 0" by blast
          have l_dim: "l < dim_vec (row A j)"
            using l_lt dim_j by simp
          have z1: "((1 - k) \<cdot>\<^sub>v row A j) $ l = 0"
            by (simp only: eq0 index_zero_vec(1)[OF l_lt])
          have z2: "((1 - k) \<cdot>\<^sub>v row A j) $ l = (1 - k) * row A j $ l"
            using l_dim by simp
          from z1 z2 have "(1 - k) * row A j $ l = 0" by simp
          then show "1 - k = 0" using l_nz by simp
        qed
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
  proof -
    have set_eq: "set (cols A\<^sup>T) = set (rows A)"
      by (simp add: cols_transpose)
    have fin: "finite (set (cols A\<^sup>T))"
      by simp
    have lin: "lin_indpt (set (cols A\<^sup>T))"
      using assms(2) by (simp add: set_eq)
    have card_nr: "card (set (cols A\<^sup>T)) = nr"
      by (simp add: set_eq distinct_card[OF assms(3)] length_rows
          carrier_matD(1)[OF assms(1)])
    have span_refl: "span (set (cols A\<^sup>T)) = span (set (cols A\<^sup>T))"
      by (rule refl)
    have card_dim: "card (set (cols A\<^sup>T)) = dim_span (set (cols A\<^sup>T))"
      using same_span_imp_card_eq_dim_span \<open>set (cols A\<^sup>T) \<subseteq> carrier_vec n\<close> lin fin span_refl
      by blast
    have "rank A\<^sup>T = nr" by fact
    also have "\<dots> = card (set (cols A\<^sup>T))" using card_nr by simp
    also have "\<dots> = dim_span (set (cols A\<^sup>T))" by (rule card_dim)
    finally show ?thesis .
  qed
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
    proof
      assume eq: "(1\<^sub>v n :: 'a vec) = (0\<^sub>v n :: 'a vec)"
      from \<open>n \<noteq> 0\<close> have n0: "0 < n" by simp
      have e1: "(1\<^sub>v n :: 'a vec) $ 0 = 1"
        using index_one_vec(1)[OF n0] by simp
      have e0: "(0\<^sub>v n :: 'a vec) $ 0 = 0"
        using index_zero_vec(1)[OF n0] by simp
      have "(1\<^sub>v n :: 'a vec) $ 0 = (0\<^sub>v n :: 'a vec) $ 0"
        using eq by simp
      with e1 e0 have "(1 :: 'a) = 0" by simp
      then show False using zero_neq_one by simp
    qed
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
        proof -
          have len_fullA: "length (rows fullA) = n"
            using carrier_matD(1)[OF sq_fullA] by (simp add: length_rows)
          have neq: "\<not> (\<forall>i<n. \<forall>j<n. i \<noteq> j \<longrightarrow> rows fullA ! i \<noteq> rows fullA ! j)"
            using \<open>\<not> distinct (rows fullA)\<close> len_fullA
            by (simp add: distinct_conv_nth)
          have "\<exists>i j. i < n \<and> j < n \<and> i \<noteq> j \<and> rows fullA ! i = rows fullA ! j"
            using neq by blast
          then show thesis
            using that by blast
        qed
        then have i_j:"i < n \<and> j < n \<and> i \<noteq> j \<and> row fullA i = row fullA j"  
          by (auto simp: carrier_matD(1)[OF sq_fullA] nth_rows)
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
              by (simp only: diff_smult_distrib_vec)
            show ?thesis
            proof(cases "row A 0 = 0\<^sub>v n")
              case True
              then have "0\<^sub>v n \<in> (set (rows A))"  
              proof -
                have "0 < dim_row A"
                  using \<open>0 < nr\<close> dim_rowA by simp
                then have "row A 0 \<in> set (rows A)"
                  by (rule row_in_set_rows)
                then show ?thesis
                  using True by simp
              qed
              then show ?thesis 
                using assms(4) field.one_not_zero zero_lin_dep by blast
            next
              case False
              then show False 
                proof -
                  assume nz: "row A 0 \<noteq> 0\<^sub>v n"
                  have dimn: "dim_vec (row A 0) = n"
                    using assms(1) by auto
                  have gen: "\<And>c. c \<cdot>\<^sub>v row A 0 = 0\<^sub>v n \<Longrightarrow> c = 0"
                  proof -
                    fix c
                    assume czero: "c \<cdot>\<^sub>v row A 0 = 0\<^sub>v n"
                    show "c = 0"
                    proof (rule ccontr)
                      assume cnz: "c \<noteq> 0"
                      have "row A 0 = 0\<^sub>v n"
                      proof (rule eq_vecI)
                        show "dim_vec (row A 0) = dim_vec (0\<^sub>v n)"
                          using dimn by simp
                      next
                        fix k
                        assume "k < dim_vec (0\<^sub>v n)"
                        then have kn: "k < n" by simp
                        have "c * (row A 0 $ k) = (c \<cdot>\<^sub>v row A 0) $ k"
                          using kn dimn by simp
                        also have "\<dots> = 0"
                          using czero kn by simp
                        finally have "c * (row A 0 $ k) = 0" .
                        then have "row A 0 $ k = 0"
                          using cnz by simp
                        then show "row A 0 $ k = 0\<^sub>v n $ k"
                          using kn by simp
                      qed
                      then show False using nz by simp
                    qed
                  qed
                  have eq_diff: "i - nr = j - nr"
                    using gen[OF smult_zero] by simp
                  have "i = i - nr + nr"
                    using \<open>nr \<le> i\<close> by simp
                  also have "\<dots> = j - nr + nr"
                    using eq_diff by simp
                  also have "\<dots> = j"
                    using \<open>nr \<le> j\<close> by simp
                  finally have "i = j" .
                  then show False using i_j by auto
                qed
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
        proof -
          have xv_carr: "x + v \<in> carrier_vec n"
            using x v(1) by (blast intro: add_carrier_vec)
          have xv_sol: "x + v \<in> carrier_vec n \<and> A *\<^sub>v (x + v) = b"
            using xv_carr \<open>A *\<^sub>v (x + v) = b\<close> by (rule conjI)
          have eq1: "(THE y. y \<in> carrier_vec n \<and> A *\<^sub>v y = b) = x + v"
            using assms(3) xv_sol by (rule the1_equality)
          have eq2: "(THE y. y \<in> carrier_vec n \<and> A *\<^sub>v y = b) = x"
            using assms(3) x by (rule the1_equality)
          have "x + v = x"
            using eq1[symmetric] eq2 by (rule trans)
          with \<open>x + v \<noteq> x\<close> show ?thesis by blast
        qed
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
  have "card F = 1"
  proof -
  have ne: "polyhedron A b \<noteq> {}"
    using assms(3) assms(4) by blast
  have bnd: "(\<forall> x \<in> polyhedron A b. \<forall> i < n. x $ i \<le> bound) \<or>
             (\<forall> x \<in> polyhedron A b. \<forall> i < n. bound \<le> x $ i)"
    using assms(3) assms(5) by fastforce
  have mf: "min_face (polyhedron A b) F"
    using assms(3) assms(6) by blast
  show ?thesis
  proof (cases "\<forall> x \<in> polyhedron A b. \<forall> i < n. x $ i \<le> bound")
    case True
    show ?thesis
      by (rule bounded_min_faces_are_vertex[OF A b ne mf True])
  next
    case False
    have ge: "\<forall> x \<in> polyhedron A b. \<forall> i < n. bound \<le> x $ i"
      using bnd False by blast
    show ?thesis
      by (rule bounded_min_faces_are_vertex'[OF A b ne mf ge])
  qed
  qed
  then have "\<exists>!x. x \<in> F" using card_eq_Suc_0_ex1 
  proof -
    have "is_singleton F"
      using \<open>card F = 1\<close> by (simp add: is_singleton_altdef)
    then obtain xF where Fx: "F = {xF}"
      by (auto simp: is_singleton_def)
    show "\<exists>!x. x \<in> F"
    proof (rule ex1I[of _ xF])
      show "xF \<in> F"
        by (simp add: Fx)
    next
      fix y
      assume "y \<in> F"
      then show "y = xF"
        by (simp add: Fx)
    qed
  qed
  then have 1:"\<exists>!x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'" 
    using assms(8) 
    by auto
  have "lin_indpt (set (rows A'))" using min_face_lin_indpt[of A nr b F b' A' I] 
    using A P_def assms(4) assms(6) assms(7) assms(8) assms(9) b by fastforce
  have "distinct (rows A')" using min_face_distinct
    using A P_def assms(4) assms(6) assms(7) assms(8) assms(9) b 
    by blast
  have 2:"A' \<in> carrier_mat (dim_row A') n" 
  proof -
    have A'_fst: "A' = fst (sub_system A b I)"
      by (simp add: assms(9)[symmetric])
    have "dim_col A' = dim_col A"
      by (simp add: A'_fst dim_col_subsyst_mat)
    moreover have "dim_col A = n"
      using A by (rule carrier_matD(2))
    ultimately have dimcol: "dim_col A' = n"
      by simp
    show ?thesis
      by (rule carrier_matI[OF refl dimcol])
  qed
  have "b' \<in> carrier_vec (dim_row A')" 
  proof -
  from 1 obtain x where xcarr: "x \<in> carrier_vec n" and xeq: "A' *\<^sub>v x = b'"
    by blast
  have "A' *\<^sub>v x \<in> carrier_vec (dim_row A')"
    by (rule mult_mat_vec_carrier[OF \<open>A' \<in> carrier_mat (dim_row A') n\<close> xcarr])
  then show ?thesis
    by (simp add: xeq)
  qed
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
  proof -
    have i_lt: "i < dim_vec v" using asmi by simp
    have "(- v) $ i = - (v $ i)" using i_lt by simp
    also have "\<dots> = - 1 * v $ i" by simp
    also have "\<dots> = vec (dim_vec v) (\<lambda>i. - 1 * v $ i) $ i" using i_lt by simp
    finally show ?thesis .
  qed
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
proof -
  have dx: "dim_vec x = n" and dy: "dim_vec y = n"
    and da: "dim_vec a = n" and db: "dim_vec b = n"
    using assms(1) assms(2) assms(3) assms(4) by auto
  have le_xa: "\<forall>i<dim_vec x. x $ i \<le> a $ i"
    using assms(5) unfolding less_eq_vec_def by simp
  have le_yb: "\<forall>i<dim_vec y. y $ i \<le> b $ i"
    using assms(6) unfolding less_eq_vec_def by simp
  have dim_eq: "dim_vec (x + y) = dim_vec (a + b)"
    using dy db by simp
  have entries: "(x + y) $ i \<le> (a + b) $ i" if i: "i < dim_vec (x + y)" for i
  proof -
    have i_n: "i < n" using i dy by simp
    have "(x + y) $ i = x $ i + y $ i" using i_n dy by simp
    moreover have "(a + b) $ i = a $ i + b $ i" using i_n db by simp
    moreover have "x $ i + y $ i \<le> a $ i + b $ i"
      using le_xa le_yb i_n dx dy by (intro add_mono) auto
    ultimately show ?thesis by simp
  qed
  show ?thesis
    unfolding less_eq_vec_def using dim_eq entries by auto
qed

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
  proof -
    have dim_c: "dim_vec c = n"
      using assms(5) by (rule carrier_vecD)
    have "c $ 0 \<in> set\<^sub>v c"
    proof (rule vec_setI)
      show "c $ 0 = c $ 0" by (rule refl)
      show "0 < dim_vec c" using dim_c assms(4) by simp
    qed
    then show ?thesis by blast
  qed
    have "Max (abs ` (vec_set c)) \<ge> 0" 
    proof -
      have fin: "finite (abs ` set\<^sub>v c)"
        using finite_vec_set finite_imageI by blast
      have ne: "abs ` set\<^sub>v c \<noteq> {}"
        using \<open>set\<^sub>v c \<noteq> {}\<close> by blast
      have mem: "Max (abs ` set\<^sub>v c) \<in> abs ` set\<^sub>v c"
        by (rule Max_in[OF fin ne])
      have nonneg: "\<forall>x \<in> abs ` set\<^sub>v c. 0 \<le> x"
        by auto
      show ?thesis
        using mem nonneg by blast
    qed
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
          proof -
            have c_le: "c $ i \<le> 0"
              using False by linarith
            have "c $ i * x $ i \<le> c $ i * (- 1)"
              by (rule mult_left_mono_neg[OF \<open>- 1 \<le> x $ i\<close> c_le])
            also have "c $ i * (- 1) = - c $ i"
              by simp
            finally show ?thesis .
          qed
          then show ?thesis by linarith
        qed
      qed
    qed
    then have "\<forall> i < n. c $ i * x $ i \<le> Max (abs ` (vec_set c))" 
    proof (intro allI impI)
      fix i
      assume i: "i < n"
      have i_dim: "i < dim_vec c"
        using i carrier_vecD[OF assms(5)] by simp
      have mem: "c $ i \<in> vec_set c"
        using i_dim by (blast intro: vec_setI)
      have mem_abs: "\<bar>c $ i\<bar> \<in> abs ` (vec_set c)"
        using mem by (rule imageI)
      have fin: "finite (abs ` (vec_set c))"
        by (rule finite_imageI[OF finite_vec_set])
      have le_max: "\<bar>c $ i\<bar> \<le> Max (abs ` (vec_set c))"
        by (rule Max_ge[OF fin mem_abs])
      have prev: "c $ i * x $ i \<le> \<bar>c $ i\<bar>"
        using \<open>\<forall> i < n. c $ i * x $ i \<le> abs (c $ i)\<close> i by blast
      show "c $ i * x $ i \<le> Max (abs ` (vec_set c))"
        using prev le_max by (rule order_trans)
    qed
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
      proof -
        have dr: "dim_row A = n"
          by (rule carrier_matD(1)[OF assms(1)])
        have dv: "dim_vec b = n"
          by (rule carrier_vecD[OF assms(2)])
        have "i < dim_row A"
          using asmi "1" by simp
        then have "i < dim_vec b"
          using dr dv by simp
        then have "b $ i \<in> \<int>"
          using assms(4) by (auto simp: Ints_vec_def)
        then show ?thesis
          using \<open>replace_col A b k $$ (i, j) = b $ i\<close> by simp
      qed
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
        proof -
          have "j < dim_vec (row (A @\<^sub>r B) i)"
            using asmj by (simp only: index_row(2))
          then show ?thesis
            by (simp only: 1 index_row(2))
        qed
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
      proof -
        have dimA: "dim_row A = nr1"
          using assms(1) by (rule carrier_matD(1))
        have AB: "A @\<^sub>r B \<in> carrier_mat (nr1 + nr2) n"
          using assms(1) assms(2) by (rule carrier_append_rows)
        have dimAB: "dim_row (A @\<^sub>r B) = nr1 + nr2"
          using AB by (rule carrier_matD(1))
        have i_lt: "i < nr1 + nr2"
          using asmi dimAB by simp
        have i_nlt: "\<not> i < nr1"
          using False dimA by simp
        have i_ge: "nr1 \<le> i"
          using i_nlt by linarith
        show ?thesis
          using Missing_Matrix.append_rows_nth(2)[OF assms(1) assms(2)] i_lt i_nlt i_ge
          by blast
      qed
      have 2:"(A @\<^sub>r B) $$ (i, j) = row (A @\<^sub>r B) i $ j" 
        by (simp add: asmi asmj)
      have "j < dim_col B" 
      proof -
        have "dim_col (A @\<^sub>r B) = n"
          using assms(1) assms(2) carrier_matD(2) by blast
        moreover have "dim_col B = n"
          using assms(2) carrier_matD(2) by blast
        ultimately show ?thesis
          using asmj by simp
      qed
      then have "B $$ (i-nr1, j) = row B (i-nr1) $ j"
      proof -
        have dimA: "dim_row A = nr1"
          by (rule carrier_matD(1)[OF assms(1)])
        have dimB: "dim_row B = nr2"
          by (rule carrier_matD(1)[OF assms(2)])
        have dimAB: "dim_row (A @\<^sub>r B) = nr1 + nr2"
          by (simp add: append_rows_def dimA dimB)
        have i_lt: "i < nr1 + nr2"
          using asmi dimAB by simp
        have nr1_le: "nr1 \<le> i"
          using False dimA by simp
        have idx_lt: "i - nr1 < dim_row B"
          using i_lt nr1_le dimB by arith
        show ?thesis
          using idx_lt \<open>j < dim_col B\<close> by simp
      qed
      then have "(A @\<^sub>r B) $$ (i, j) = B $$ (i - nr1, j)" 
        using 2 1 by presburger
      then show ?thesis 
      proof -
        have dimA: "dim_row A = nr1" "dim_col A = n"
          using assms(1) by blast+
        have dimB: "dim_row B = nr2" "dim_col B = n"
          using assms(2) by blast+
        have dim_r: "dim_row (A @\<^sub>r B) = nr1 + nr2"
          by (simp add: append_rows_def dimA(1) dimB(1))
        have dim_c: "dim_col (A @\<^sub>r B) = n"
          by (simp add: append_rows_def dimA(2))
        have i_nlt: "\<not> i < nr1"
          using False dimA(1) by simp
        have i_lt: "i < nr1 + nr2"
          using asmi dim_r by simp
        have iB: "i - nr1 < dim_row B"
          using i_nlt i_lt dimB(1) by arith
        have jB: "j < dim_col B"
          using asmj dim_c dimB(2) by simp
        have row_eq: "row (A @\<^sub>r B) i = row B (i - nr1)"
          using Missing_Matrix.append_rows_nth(2)[OF assms(1) assms(2)] i_lt i_nlt by simp
        have "(A @\<^sub>r B) $$ (i, j) = row (A @\<^sub>r B) i $ j"
          using asmi asmj by simp
        also have "\<dots> = row B (i - nr1) $ j"
          using row_eq by simp
        also have "\<dots> = B $$ (i - nr1, j)"
          using iB jB by simp
        finally have eq: "(A @\<^sub>r B) $$ (i, j) = B $$ (i - nr1, j)" .
        have "B $$ (i - nr1, j) \<in> \<int>"
          using assms(4) iB jB by (auto simp: Ints_mat_def)
        then show ?thesis
          using eq by simp
      qed
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
      using True asmi by (simp add: index_append_vec(1) index_append_vec(2) carrier_vecD[OF assms(1)])
    then show ?thesis 
      using assms(3) unfolding Ints_vec_def  using True assms(1) by auto
  next
    case False
    have "(v @\<^sub>v w) $v i = w $ (i - nr1)" 
    proof -
      have dim_v: "dim_vec v = nr1"
        using assms(1) by (rule carrier_vecD)
      then show ?thesis
        using asmi False index_append_vec(1) by simp    qed
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
      by (insert True asmi asmj, simp add: Ints_1)
  next
    case False
    have "Matrix.mat n n (\<lambda>(i, j). if i = j then 1 else 0) $$ (i, j) = 0" 
      using False asmi asmj by simp
    then show ?thesis 
      by (insert False asmi asmj, simp add: Ints_0)
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
      by (simp add: vec_of_list_index)
    obtain j where "j< length (list_of_vec b)" "(list_of_vec b) ! j = (nths (list_of_vec b) I) ! i"
  proof -
    have i_len: "i < length (nths (list_of_vec b) I)"
      using asmi by (simp add: Matrix.dim_vec_of_list)
    then have "nths (list_of_vec b) I ! i \<in> set (nths (list_of_vec b) I)"
      by (rule nth_mem)
    then have mem: "nths (list_of_vec b) I ! i \<in> set (list_of_vec b)"
      by (rule in_set_nthsD)
    from mem have ex_j: "\<exists>j<length (list_of_vec b). list_of_vec b ! j = nths (list_of_vec b) I ! i"
      by (simp add: in_set_conv_nth)
    then obtain j where "j < length (list_of_vec b)"
      and "list_of_vec b ! j = nths (list_of_vec b) I ! i"
      by blast
    then show thesis
      using that by blast
  qed
    then have "(list_of_vec b) ! j \<in> \<int>" 
      proof -
        have j_dim: "j < dim_vec b"
          using \<open>j < length (list_of_vec b)\<close>
          by (simp add: Matrix.length_list_of_vec)
        have "list_of_vec b ! j = b $v j"
          using j_dim by (simp add: list_of_vec_index)
        moreover have "b $v j \<in> \<int>"
          using j_dim \<open>\<forall>i<dim_vec b. b $v i \<in> \<int>\<close> by blast
        ultimately show ?thesis by simp
      qed
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
    using dim_col_subsyst_mat[of A b I] carrier_matD(2)[OF A]
    by (auto simp: assms(9)[symmetric] intro!: carrier_matI)
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
  proof -
  have fstA': "fst (sub_system A b I) = A'"
    using assms(9)[symmetric] by simp
  have "dim_col A' = dim_col A"
    using dim_col_subsyst_mat[of A b I] by (simp add: fstA')
  moreover have "dim_col A = n"
    using A by (rule carrier_matD(2))
  ultimately have "dim_col A' = n" by simp
  then show ?thesis
    by (intro carrier_matI) auto
  qed
  then have "rank A'\<^sup>T = dim_row A'" 
    using lin_indpt_full_rank[of "A'\<^sup>T" "dim_row A'"]
      `lin_indpt (set (cols A'\<^sup>T))` `distinct (cols A'\<^sup>T)`  transpose_carrier_mat by blast
  then show "det A' \<noteq> 0" 
  proof -
    assume rankAT: "rank A'\<^sup>T = dim_row A'"
    have Asq: "A' \<in> carrier_mat n n"
      using \<open>A' \<in> carrier_mat (dim_row A') n\<close> \<open>dim_row A' = n\<close> by simp
    have ATsq: "A'\<^sup>T \<in> carrier_mat n n"
      using Asq transpose_carrier_mat by blast
    have "rank A'\<^sup>T = n"
      using rankAT \<open>dim_row A' = n\<close> by simp
    then have "det A'\<^sup>T \<noteq> 0"
      using det_rank_iff[OF ATsq] by simp
    then show "det A' \<noteq> 0"
      using det_transpose[OF Asq] by simp
  qed
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
  by (blast dest: gram_schmidt.min_face_elim(1) face_non_empty)
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
  proof -
    have A'_eq: "A' = fst (sub_system A b I)"
      using arg_cong[OF assms(11), of fst] by simp
    have "dim_col A' = n"
      using dim_col_subsyst_mat[of A b I] A'_eq A carrier_matD(2) by simp
    then show "A' \<in> carrier_mat n n"
      using \<open>dim_row A' = n\<close> by (intro carrier_matI)
  qed
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
    proof (intro allI impI)
      assume z_eq: "\<forall>k < n. z $ k = det (replace_col A' b' k) / det A'"
      fix k
      assume k_lt: "k < n"
      have "z $ k = det (replace_col A' b' k) / det A'"
        using z_eq k_lt by blast
      then show "(\<lambda>i. \<bar>det A'\<bar> * z $v i) k = (\<lambda>k. \<bar>det A'\<bar> * det (replace_col A' b' k) / det A') k"
        by simp
    qed
    then have 6:"?z' =  vec n (\<lambda> k. \<bar>det A'\<bar> * det (replace_col A' b' k) / det A')" 
      unfolding smult_vec_def 
      by (auto simp: `dim_vec z = n` 4) 
    have "\<bar>det A'\<bar> /det A' \<in> \<int>" 
    proof(cases "det A' > 0")
      case True
      have "\<bar>det A'\<bar> /det A' = 1" 
      proof -
        have "\<bar>Determinant.det A'\<bar> = Determinant.det A'"
          using True by (rule abs_of_pos)
        then show ?thesis
          using \<open>Determinant.det A' \<noteq> 0\<close> by (simp add: divide_self)
      qed
      then show ?thesis 
        by fastforce
    next
      case False
      have "\<bar>det A'\<bar> /det A' = - 1" 
        using False  \<open>Determinant.det A' \<noteq> 0\<close>  
      proof -
        have "det A' < 0"
          using False \<open>Determinant.det A' \<noteq> 0\<close> by linarith
        hence "\<bar>det A'\<bar> = - det A'"
          by simp
        thus "\<bar>det A'\<bar> / det A' = - 1"
          using \<open>Determinant.det A' \<noteq> 0\<close> by (simp add: divide_self)
      qed
      then show ?thesis by auto
    qed
    then have "\<forall>k < n.\<bar>det A'\<bar> * det (replace_col A' b' k) / det A' \<in> \<int>" 
    proof (intro allI impI)
      fix k
      assume "k < n"
      have "\<bar>det A'\<bar> * det (replace_col A' b' k) / det A'
              = \<bar>det A'\<bar> / det A' * det (replace_col A' b' k)"
        by (rule times_divide_eq_left[symmetric])
      also have "\<dots> \<in> \<int>"
        using Ints_mult[OF \<open>\<bar>det A'\<bar> /det A' \<in> \<int>\<close>]
              \<open>\<forall> k < n. det (replace_col A' b' k) \<in> \<int>\<close> \<open>k < n\<close>
        by blast
      finally show "\<bar>det A'\<bar> * det (replace_col A' b' k) / det A' \<in> \<int>" .
    qed
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
  proof -
    have "integer_hull P \<subseteq> P"
      unfolding P_def
      using gram_schmidt.int_hull_subset[OF assms(1) b] .
    then show ?thesis
      using assms(8) by blast
  qed
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
    proof -
      have "\<exists> x \<in> carrier_vec n. A *\<^sub>v x \<le> b"
      proof -
        obtain x where "x \<in> P" using `P \<noteq> {}` by blast
        then have "x \<in> carrier_vec n \<and> A *\<^sub>v x \<le> b"
          by (simp add: P_def local.polyhedron_def)
        then show ?thesis by blast
      qed
      then show ?thesis
        using strong_duality_theorem_primal_sat_bounded_min_max(2)[OF A b c]
          `\<forall> x \<in> carrier_vec n. A *\<^sub>v x \<le> b \<longrightarrow> c \<bullet> x \<le> Bnd`
        by blast
    qed
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
  proof -
    have y_carr: "y \<in> carrier_vec n" and Ay_ge: "0\<^sub>v nr \<le> A *\<^sub>v y"
      using y by auto
    have Ay_dim: "dim_vec (A *\<^sub>v y) = nr"
      using dim_mult_mat_vec carrier_matD(1)[OF A] by simp
    have eq: "A *\<^sub>v (- y) = - (A *\<^sub>v y)"
    proof -
      have "A *\<^sub>v (- y) = A *\<^sub>v ((-1) \<cdot>\<^sub>v y)"
        using minus_mult_minus_one[of y] by simp
      also have "\<dots> = (-1) \<cdot>\<^sub>v (A *\<^sub>v y)"
        using mult_mat_vec[of A nr n y "-1"] A y_carr by auto
      also have "\<dots> = - (A *\<^sub>v y)"
        using minus_mult_minus_one[of "A *\<^sub>v y"] by simp
      finally show ?thesis .
    qed
    have "- (A *\<^sub>v y) \<le> 0\<^sub>v nr"
    proof (unfold less_eq_vec_def, safe)
      show "dim_vec (- (A *\<^sub>v y)) = dim_vec (0\<^sub>v nr)"
        using Ay_dim by simp
    next
      fix i
      assume "i < dim_vec (0\<^sub>v nr)"
      then have i_nr: "i < nr"
        using Ay_dim by simp
      have "0\<^sub>v nr $ i \<le> (A *\<^sub>v y) $ i"
        using Ay_ge[unfolded less_eq_vec_def] i_nr Ay_dim by auto
      then show "(- (A *\<^sub>v y)) $ i \<le> 0\<^sub>v nr $ i"
        using i_nr Ay_dim by (simp add: index_uminus_vec index_zero_vec)
    qed
    then show ?thesis
      using eq by simp
  qed
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
proof -

    have y'_carr: "y' \<in> carrier_vec n" using y' by simp
    have "dim_vec y' = n" using y'_carr by (rule carrier_vecD)
    moreover have "0 < n" using \<open>n \<noteq> 0\<close> by simp
    ultimately have d: "0 < dim_vec y'" by simp
    have "y' $ 0 \<in> set\<^sub>v y'" by (rule vec_setI[of y' 0 "y' $ 0"], simp, fact d)
    then show "set\<^sub>v y' \<noteq> {}" by blast
  qed
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
    proof -
      assume Max0: "Max (abs ` set\<^sub>v y') = 0"
      show "\<forall>y' \<in> abs ` set\<^sub>v y'. y' = 0"
      proof (intro ballI)
        fix z
        assume z_mem: "z \<in> abs ` set\<^sub>v y'"
        have le0: "z \<le> Max (abs ` set\<^sub>v y')"
          using Max_ge[of "abs ` set\<^sub>v y'" z] z_mem \<open>finite (abs ` set\<^sub>v y')\<close> by blast
        also have "\<dots> = 0"
          using Max0 by simp
        finally have z_le: "z \<le> 0" .
        have z_ge: "0 \<le> z"
          using z_mem \<open>\<forall>y \<in> abs ` set\<^sub>v y'. 0 \<le> y\<close> by blast
        from z_le z_ge show "z = 0" by simp
      qed
    qed
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
    proof -
      have m1: "1\<^sub>m n \<in> carrier_mat n n" 
        by (rule one_carrier_mat)
      have m2: "- 1\<^sub>m n \<in> carrier_mat n n" 
        by (simp add: uminus_carrier_iff_mat one_carrier_mat)
      have m12: "(1\<^sub>m n) @\<^sub>r (- 1\<^sub>m n) \<in> carrier_mat (2 * n) n" 
        using carrier_append_rows[OF m1 m2] by (simp add: mult_2)
      show "A @\<^sub>r (1\<^sub>m n) @\<^sub>r (- 1\<^sub>m n) \<in> carrier_mat (nr + 2 * n) n" 
        using carrier_append_rows[OF A m12] by simp
    qed
  have 3:"?fullb \<in> carrier_vec (nr+2*n)" 
    by (simp add: mult_2)
  have "?y' \<in> ?P'" 
  proof -
    have "A *\<^sub>v y' \<le> 0\<^sub>v nr" using y' by auto
    then have "(1/Max (abs ` (vec_set y'))) \<cdot>\<^sub>v (A *\<^sub>v y') \<le> 0\<^sub>v nr" 
      using \<open>Max (abs ` (vec_set y')) > 0\<close> 
      by (meson divide_nonneg_pos smult_nneg_npos_vec zero_less_one_class.zero_le_one)
    then have "A *\<^sub>v ?y' \<le> 0\<^sub>v nr" 
      by (simp add: mult_mat_vec[OF A y'[THEN conjunct1]])
    have "\<forall> i < n. row (1\<^sub>m n) i \<bullet> ?y' \<le> 1" 
    proof(safe)
      fix i
      assume "i< n" 
      have 2:"row (1\<^sub>m n) i = unit_vec n i" 
        using \<open>i < n\<close> row_one by blast
      have 1:"unit_vec n i \<bullet> ?y' = ?y' $ i" 
        by (meson \<open>i < n\<close> scalar_prod_left_unit smult_closed y')
      have "y' $ i \<le>  Max (abs ` set\<^sub>v y')" 
        proof -
  have i_dim: "i < dim_vec y'"
    using \<open>i < n\<close> y' carrier_vecD by auto
  have mem: "y' $ i \<in> set\<^sub>v y'"
    by (rule vec_setI[of y' i "y' $ i", OF refl i_dim])
  have mem_abs: "\<bar>y' $ i\<bar> \<in> abs ` set\<^sub>v y'"
    using mem by (rule imageI)
  have fin: "finite (abs ` set\<^sub>v y')"
    by (intro finite_imageI finite_vec_set)
  have le_max: "\<bar>y' $ i\<bar> \<le> Max (abs ` set\<^sub>v y')"
    using fin mem_abs by (rule Max_ge)
  have le_abs: "y' $ i \<le> \<bar>y' $ i\<bar>"
    by simp
  show "y' $ i \<le> Max (abs ` set\<^sub>v y')"
    using le_abs le_max by linarith
qed
      then have "(1 / Max (abs ` set\<^sub>v y')) * (y' $ i) \<le> 1"
      proof -
        assume le: "y' $ i \<le> Max (abs ` set\<^sub>v y')"
        have pos: "0 < Max (abs ` set\<^sub>v y')"
          using \<open>0 < Max (abs ` set\<^sub>v y')\<close> by blast
        have inv_pos: "0 < 1 / Max (abs ` set\<^sub>v y')"
          using pos zero_less_divide_1_iff by blast
        from mult_left_mono[OF le less_imp_le[OF inv_pos]]
        have "(1 / Max (abs ` set\<^sub>v y')) * (y' $ i) \<le> (1 / Max (abs ` set\<^sub>v y')) * Max (abs ` set\<^sub>v y')" .
        also have "(1 / Max (abs ` set\<^sub>v y')) * Max (abs ` set\<^sub>v y') = 1"
          using pos by simp
        finally show "(1 / Max (abs ` set\<^sub>v y')) * (y' $ i) \<le> 1" .
      qed
      have "(1 / Max (abs ` set\<^sub>v y') \<cdot>\<^sub>v y') $ i \<le> 1" 
      proof -
        have "y' \<in> carrier_vec n" using y' by blast
        then have "i < dim_vec y'" using \<open>i < n\<close> by (simp add: carrier_vecD)
        then have "(1 / Max (abs ` set\<^sub>v y') \<cdot>\<^sub>v y') $ i = 1 / Max (abs ` set\<^sub>v y') * y' $ i"
          by (simp add: index_smult_vec)
        then show "(1 / Max (abs ` set\<^sub>v y') \<cdot>\<^sub>v y') $ i \<le> 1"
          using \<open>1 / Max (abs ` set\<^sub>v y') * y' $ i \<le> 1\<close> by simp
      qed
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
      proof -
        have y'_carr: "?y' \<in> carrier_vec n"
          using y' by (blast intro: smult_closed)
        have "unit_vec n i \<bullet> ?y' = ?y' $ i"
          using \<open>i < n\<close> y'_carr scalar_prod_left_unit by blast
        then show "- unit_vec n i \<bullet> ?y' = - ?y' $ i"
          using uminus_scalar_prod[OF unit_vec_carrier y'_carr, symmetric] by simp
      qed
      have "- y' $ i \<le>  Max (abs ` set\<^sub>v y')" 
        proof -
          have "i < dim_vec y'"
            using \<open>i < n\<close> y' carrier_vecD by blast
          then have "y' $ i \<in> set\<^sub>v y'"
            unfolding vec_set_def by auto
          then have mem: "\<bar>y' $ i\<bar> \<in> abs ` set\<^sub>v y'"
            by blast
          have fin: "finite (abs ` set\<^sub>v y')"
            using finite_vec_set finite_imageI by blast
          from fin mem have "\<bar>y' $ i\<bar> \<le> Max (abs ` set\<^sub>v y')"
            by (rule Max_ge)
          then show "- y' $ i \<le> Max (abs ` set\<^sub>v y')"
            using abs_le_D2 by blast
        qed
      then have "(1 / Max (abs ` set\<^sub>v y')) * (- y' $ i) \<le> 1" 
      proof -
        assume le: "- y' $ i \<le> Max (abs ` set\<^sub>v y')"
        have "(1 / Max (abs ` set\<^sub>v y')) * (- y' $ i) = - y' $ i / Max (abs ` set\<^sub>v y')"
          by simp
        also have "\<dots> \<le> 1"
        proof -
          from \<open>0 < Max (abs ` set\<^sub>v y')\<close> have eq: "- y' $ i / Max (abs ` set\<^sub>v y') \<le> 1 \<longleftrightarrow> - y' $ i \<le> 1 * Max (abs ` set\<^sub>v y')"
            by (rule pos_divide_le_eq)
          with le show ?thesis by simp
        qed
        finally show ?thesis .
      qed
      have " - (1 / Max (abs ` set\<^sub>v y') \<cdot>\<^sub>v y') $ i \<le> 1" 
      proof -
        have y'_carr: "y' \<in> carrier_vec n" using y' by blast
        have i_dim: "i < dim_vec y'"
          using \<open>i < n\<close> y'_carr carrier_vecD by blast
        have eq1: "(1 / Max (abs ` set\<^sub>v y') \<cdot>\<^sub>v y') $ i = 1 / Max (abs ` set\<^sub>v y') * y' $ i"
          using index_smult_vec(1)[OF i_dim] by simp
        have "- (1 / Max (abs ` set\<^sub>v y') \<cdot>\<^sub>v y') $ i = 1 / Max (abs ` set\<^sub>v y') * (- y' $ i)"
          using eq1 by (simp add: mult_minus_right)
        also have "\<dots> \<le> 1"
          using \<open>1 / Max (abs ` set\<^sub>v y') * - y' $ i \<le> 1\<close> by simp
        finally show ?thesis .
      qed
      then show "row (- 1\<^sub>m n) i \<bullet> ?y' \<le> 1" 
        by (simp add: \<open>row (- 1\<^sub>m n) i = - unit_vec n i\<close> 3)
    qed
    then have "- 1\<^sub>m n *\<^sub>v ?y' \<le> 1\<^sub>v n" 
      unfolding mult_mat_vec_def 
      by (simp add: less_eq_vec_def)
    have "(1\<^sub>m n @\<^sub>r - 1\<^sub>m n)  *\<^sub>v ?y' \<le>  ( 1\<^sub>v n @\<^sub>v 1\<^sub>v n)"
    proof -
      have y'_carr: "?y' \<in> carrier_vec n"
      proof -
        have "y' \<in> carrier_vec n" using y' by blast
        then show ?thesis by (simp add: smult_closed)
      qed
      show ?thesis
        using append_rows_le[of "1\<^sub>m n" n n "- 1\<^sub>m n" n "1\<^sub>v n" ?y' "1\<^sub>v n"]
          `- 1\<^sub>m n *\<^sub>v ?y' \<le> 1\<^sub>v n` `1\<^sub>m n *\<^sub>v ?y' \<le> 1\<^sub>v n` y'_carr
        by auto
    qed
    then have "(A @\<^sub>r 1\<^sub>m n @\<^sub>r - 1\<^sub>m n) *\<^sub>v ?y' \<le>  (0\<^sub>v nr @\<^sub>v 1\<^sub>v n @\<^sub>v 1\<^sub>v n)" 
      using `- 1\<^sub>m n *\<^sub>v ?y' \<le> 1\<^sub>v n` 
        append_rows_le[of "A" nr n "1\<^sub>m n @\<^sub>r - 1\<^sub>m n" "2*n" "0\<^sub>v nr" ?y' "1\<^sub>v n @\<^sub>v 1\<^sub>v n"] 
      proof -
        have B_carr: "(1\<^sub>m n @\<^sub>r - 1\<^sub>m n) \<in> carrier_mat (2 * n) n"
        proof -
          have "- 1\<^sub>m n \<in> carrier_mat n n"
            using one_carrier_mat uminus_carrier_iff_mat by blast
          then have "(1\<^sub>m n @\<^sub>r - 1\<^sub>m n) \<in> carrier_mat (n + n) n"
            using one_carrier_mat carrier_append_rows by blast
          then show ?thesis by (simp add: mult_2)
        qed
        have y'_carr: "(1 / Max (abs ` set\<^sub>v y') \<cdot>\<^sub>v y') \<in> carrier_vec n"
          using y' smult_closed by blast
        have b_carr: "(1\<^sub>v n @\<^sub>v 1\<^sub>v n) \<in> carrier_vec (2 * n)"
          by (simp add: mult_2)
        show ?thesis
          using append_rows_le[OF A B_carr zero_carrier_vec y'_carr]
            \<open>A *\<^sub>v (1 / Max (abs ` set\<^sub>v y') \<cdot>\<^sub>v y') \<le> 0\<^sub>v nr\<close>
            \<open>(1\<^sub>m n @\<^sub>r - 1\<^sub>m n) *\<^sub>v (1 / Max (abs ` set\<^sub>v y') \<cdot>\<^sub>v y') \<le> 1\<^sub>v n @\<^sub>v 1\<^sub>v n\<close>
          by blast
      qed
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
    proof -
      have B_carr: "1\<^sub>m n @\<^sub>r - 1\<^sub>m n \<in> carrier_mat (n + n) n"
        using carrier_append_rows[OF one_carrier_mat uminus_carrier_mat[OF one_carrier_mat]] .
      have b_carr: "1\<^sub>v n @\<^sub>v 1\<^sub>v n \<in> carrier_vec (n + n)"
        by simp
      have prem: "(A @\<^sub>r (1\<^sub>m n @\<^sub>r - 1\<^sub>m n)) *\<^sub>v x \<le> (0\<^sub>v nr @\<^sub>v (1\<^sub>v n @\<^sub>v 1\<^sub>v n))"
        using \<open>x \<in> ?P'\<close> unfolding polyhedron_def by auto
      have "(A @\<^sub>r (1\<^sub>m n @\<^sub>r - 1\<^sub>m n)) *\<^sub>v x \<le> (0\<^sub>v nr @\<^sub>v (1\<^sub>v n @\<^sub>v 1\<^sub>v n)) \<longleftrightarrow>
        A *\<^sub>v x \<le> 0\<^sub>v nr \<and> (1\<^sub>m n @\<^sub>r - 1\<^sub>m n) *\<^sub>v x \<le> (1\<^sub>v n @\<^sub>v 1\<^sub>v n)"
        using append_rows_le[OF A B_carr zero_carrier_vec \<open>x \<in> carrier_vec n\<close>] .
      with prem show ?thesis by blast
    qed
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
      by (fastforce simp: A \<open>x \<in> carrier_vec n\<close> carrier_append_rows mult_2 one_carrier_mat
          uminus_carrier_mat zero_carrier_vec)
    then have " -  1\<^sub>m n *\<^sub>v x \<le> 1\<^sub>v n" 
      using  append_rows_le[of "1\<^sub>m n" n n "- 1\<^sub>m n" n "1\<^sub>v n" x "1\<^sub>v n"] 
      by (simp add: \<open>x \<in> carrier_vec n\<close>) 
    then have "\<forall> i < n. row (- 1\<^sub>m n) i \<bullet> x \<le> 1" unfolding mult_mat_vec_def 
      by (simp add: less_eq_vec_def)
    then have "\<forall> i < n. - unit_vec n i \<bullet> x \<le> 1" 
      by simp
    then have "\<forall> i < n. - x $ i \<le> 1" 
    proof (intro allI impI)
      fix i
      assume i: "i < n"
      have eq: "- unit_vec n i \<bullet> x = - x $ i"
        using \<open>x \<in> carrier_vec n\<close> i
        by (simp add: scalar_prod_left_unit scalar_prod_uminus_left)
      from \<open>\<forall>i<n. - unit_vec n i \<bullet> x \<le> 1\<close>[rule_format, OF i]
      have b: "- unit_vec n i \<bullet> x \<le> 1" by simp
      from b show "- x $ i \<le> 1" unfolding eq[symmetric] by simp
    qed
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
  using beta 4 c by (auto simp: polyhedron_def)
  let ?F = " ?P' \<inter> {x |x. ?c \<bullet> x = \<beta>}"
  have "face ?P' ?F" unfolding face_def using 1 4 
    by blast 
  then obtain F where F_def:"min_face ?P' F \<and> F \<subseteq> ?F" 
    using 2 3 face_contains_min_face[of ?fullA "nr+2*n" ?fullb ?F] 
    by blast
  then obtain z where "z \<in> F" 
  proof -
    have "min_face ?P' F" using F_def by blast
    then have "face ?P' F" using gram_schmidt.min_face_elim(1) by blast
    then have "F \<noteq> {}" using face_non_empty by blast
    then show thesis using that by blast
  qed
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
  proof -
    have "{dim_vec d | C d I. (C, d) = sub_system ?fullA ?fullb I \<and>
          F = {x. x \<in> carrier_vec n \<and> C *\<^sub>v x = d}}
      = {dim_vec d | C d I. F = {x. x \<in> carrier_vec n \<and> C *\<^sub>v x = d} \<and>
          (C, d) = sub_system ?fullA ?fullb I}"
      by blast
    then show ?thesis
      using A'_b'(3) by simp
  qed
  have "det A' \<noteq> 0" 
    using bounded_min_faces_det_non_zero[OF 2 3 1 9] F_def A'_b' 10 
    by fast
  have "dim_row A' = n"
    using bounded_min_faces_square_mat[OF 2 3 1 9 conjunct1[OF F_def] 10 A'_b'(1) A'_b'(2)] .
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
    proof -
      have one_carr: "(1\<^sub>m n) \<in> carrier_mat n n"
        by (rule one_carrier_mat)
      have minus_one_carr: "(- 1\<^sub>m n) \<in> carrier_mat n n"
        by (simp add: uminus_carrier_iff_mat one_carr)
      have inner_carr: "(1\<^sub>m n @\<^sub>r - 1\<^sub>m n) \<in> carrier_mat (n + n) n"
        using carrier_append_rows[OF one_carr minus_one_carr] .
      have inner_int: "(1\<^sub>m n @\<^sub>r - 1\<^sub>m n) \<in> \<int>\<^sub>m"
        using append_int_mat_is_int[OF one_carr minus_one_carr \<open>1\<^sub>m n \<in> \<int>\<^sub>m\<close> \<open>- 1\<^sub>m n \<in> \<int>\<^sub>m\<close>] .
      show ?thesis
        using append_int_mat_is_int[OF A inner_carr AI inner_int] .
    qed
  have "?fullb \<in> \<int>\<^sub>v" using append_int_vec_is_int one_vec_int 
    proof -
      have one_int: "1\<^sub>v n \<in> \<int>\<^sub>v"
        using one_vec_int by blast
      have zero_int: "0\<^sub>v nr \<in> \<int>\<^sub>v"
        using gram_schmidt.zero_vec_is_int by blast
      have one_carr: "1\<^sub>v n \<in> carrier_vec n"
        by (rule one_carrier_vec)
      have zero_carr: "0\<^sub>v nr \<in> carrier_vec nr"
        by (rule zero_carrier_vec)
      have inner_int: "1\<^sub>v n @\<^sub>v 1\<^sub>v n \<in> \<int>\<^sub>v"
        using append_int_vec_is_int[OF one_carr one_carr one_int one_int] by blast
      have inner_carr: "1\<^sub>v n @\<^sub>v 1\<^sub>v n \<in> carrier_vec (n + n)"
        by (rule append_carrier_vec[OF one_carr one_carr])
      show ?thesis
        using append_int_vec_is_int[OF zero_carr inner_carr zero_int inner_int] by blast
    qed
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
      by simp
    then have 8:"?z' =  vec n (\<lambda> k. \<bar>det A'\<bar> * det (replace_col A' b' k) / det A')" 
      unfolding smult_vec_def using 6
      by (auto simp: `dim_vec z = n`) 
    have "\<bar>det A'\<bar> /det A' \<in> \<int>" 
    proof(cases "det A' > 0")
      case True
      have "\<bar>det A'\<bar> /det A' = 1" 
        by (simp add: abs_of_pos[OF True] \<open>Determinant.det A' \<noteq> 0\<close>)
      then show ?thesis 
        by fastforce
    next
      case False
      have "\<bar>det A'\<bar> /det A' = - 1" 
        proof -
          have det_neg: "Determinant.det A' < 0"
            using False \<open>Determinant.det A' \<noteq> 0\<close> by linarith
          have abs_eq: "\<bar>Determinant.det A'\<bar> = - Determinant.det A'"
            using det_neg by simp
          show "\<bar>Determinant.det A'\<bar> / Determinant.det A' = - 1"
            using abs_eq \<open>Determinant.det A' \<noteq> 0\<close> by simp
        qed
      then show ?thesis by auto
    qed
    then have "\<forall>k < n.\<bar>det A'\<bar> * det (replace_col A' b' k) / det A' \<in> \<int>" 
    proof -
      have ratio: "\<bar>det A'\<bar> / det A' \<in> \<int>"
        by fact
      show ?thesis
      proof (intro allI impI)
        fix k
        assume "k < n"
        then have "det (replace_col A' b' k) \<in> \<int>"
          using \<open>\<forall>k<n. Determinant.det (replace_col A' b' k) \<in> \<int>\<close> by blast
        with ratio have "(\<bar>det A'\<bar> / det A') * det (replace_col A' b' k) \<in> \<int>"
          using Ints_mult by blast
        then show "\<bar>det A'\<bar> * det (replace_col A' b' k) / det A' \<in> \<int>"
          by (simp add: times_divide_eq_left)
      qed
    qed
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
  proof -
  have y'_carr: "y' \<in> carrier_vec n"
    using y' by blast
  have y'_pos: "y' \<bullet> c > 0"
    using y' by blast
  have comm: "c \<bullet> y' = y' \<bullet> c"
    using c y'_carr comm_scalar_prod by blast
  have cy'_pos: "c \<bullet> y' > 0"
    using comm y'_pos by simp
  have factor_pos: "(1 / Max (abs ` set\<^sub>v y')) > 0"
    using \<open>0 < Max (abs ` set\<^sub>v y')\<close> zero_less_divide_1_iff by blast
  have "0 < (1 / Max (abs ` set\<^sub>v y')) * (c \<bullet> y')"
    using ordered_semiring_strict_class.mult_pos_pos[OF factor_pos cy'_pos] by simp
  then show "?c \<bullet> ?y' > 0"
    using 9 by simp
qed
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

    proof -
      have subsetP: "P \<subseteq> carrier_vec n"
        unfolding P_def polyhedron_def by blast
      from integer_hull_is_integer_hull[OF subsetP]
      show ?thesis
        by (simp add: P_def polyhedron_def)
    qed
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
proof (unfold less_eq_vec_def, intro conjI allI impI)
      show "dim_vec (A *\<^sub>v v + A *\<^sub>v (of_int m \<cdot>\<^sub>v ?z')) = dim_vec (b + 0\<^sub>v nr)"
        using \<open>A *\<^sub>v v \<le> b\<close> \<open>A *\<^sub>v (of_int m \<cdot>\<^sub>v ?z') \<le> 0\<^sub>v nr\<close>
        unfolding less_eq_vec_def by simp
    next
      fix i
      assume i_lt: "i < dim_vec (b + 0\<^sub>v nr)"
      have dvb: "dim_vec (A *\<^sub>v v) = dim_vec b"
        using \<open>A *\<^sub>v v \<le> b\<close> unfolding less_eq_vec_def by blast
      have i_b: "i < dim_vec b" using i_lt b[THEN carrier_vecD] by simp
      have i_z: "i < dim_vec (0\<^sub>v nr)" using i_b b carrier_vecD index_zero_vec by fastforce
      have le1: "(A *\<^sub>v v) $ i \<le> b $ i"
        using \<open>A *\<^sub>v v \<le> b\<close> i_b unfolding less_eq_vec_def by blast
      have le2: "(A *\<^sub>v (of_int m \<cdot>\<^sub>v ?z')) $ i \<le> (0\<^sub>v nr) $ i"
        using \<open>A *\<^sub>v (of_int m \<cdot>\<^sub>v ?z') \<le> 0\<^sub>v nr\<close> i_z unfolding less_eq_vec_def by blast
      have lhs_eq: "(A *\<^sub>v v + A *\<^sub>v (of_int m \<cdot>\<^sub>v ?z')) $ i = (A *\<^sub>v v) $ i + (A *\<^sub>v (of_int m \<cdot>\<^sub>v ?z')) $ i"
        using dvb i_b by simp
      have rhs_eq: "(b + 0\<^sub>v nr) $ i = b $ i + (0\<^sub>v nr) $ i"
        using i_z by simp
      show "(A *\<^sub>v v + A *\<^sub>v (of_int m \<cdot>\<^sub>v ?z')) $ i \<le> (b + 0\<^sub>v nr) $ i"
        unfolding lhs_eq rhs_eq using le1 le2 by (rule add_mono)
    qed
    then have "A *\<^sub>v (v + of_int m \<cdot>\<^sub>v ?z') \<le> b" 
      proof -
        assume prem: "A *\<^sub>v v + A *\<^sub>v (of_int (int m) \<cdot>\<^sub>v (\<bar>det A'\<bar> \<cdot>\<^sub>v z)) \<le> b + 0\<^sub>v nr"
        have eq: "A *\<^sub>v (v + of_int m \<cdot>\<^sub>v (\<bar>det A'\<bar> \<cdot>\<^sub>v z)) =
                   A *\<^sub>v v + A *\<^sub>v (of_int m \<cdot>\<^sub>v (\<bar>det A'\<bar> \<cdot>\<^sub>v z))"
          by (rule 10)
        also have "\<dots> \<le> b + 0\<^sub>v nr"
          by (rule prem)
        also have "\<dots> = b"
          by (rule right_zero_vec[OF b])
        finally show ?thesis .
      qed
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
  have "\<forall> m::nat. v + of_int m \<cdot>\<^sub>v ?z' \<in> integer_hull P"
  proof
    fix m :: nat
    have int_part: "v + of_int m \<cdot>\<^sub>v ?z' \<in> \<int>\<^sub>v"
      using \<open>\<forall> m::nat. v + of_int m \<cdot>\<^sub>v ?z' \<in> \<int>\<^sub>v\<close> by blast
    have in_P: "v + of_int m \<cdot>\<^sub>v ?z' \<in> polyhedron A b"
      using 11 unfolding P_def by blast
    show "v + of_int m \<cdot>\<^sub>v ?z' \<in> integer_hull P"
      unfolding P_def
    proof (rule ccontr)
      assume not_in: "v + of_int m \<cdot>\<^sub>v ?z' \<notin> integer_hull (polyhedron A b)"
      have "v + of_int m \<cdot>\<^sub>v ?z' \<in> polyhedron A b - integer_hull (polyhedron A b)"
        using in_P not_in by blast
      then have "v + of_int m \<cdot>\<^sub>v ?z' \<notin> \<int>\<^sub>v"
        using A b gram_schmidt.not_in_int_hull_not_int by blast
      with int_part show False by blast
    qed
  qed
  have "?c \<bullet> z = \<beta>" 
    using 12 by blast
  then have "?c \<bullet> ?z' = abs (det A') * \<beta>" 
  proof -
    have "c \<bullet> (\<bar>det A'\<bar> \<cdot>\<^sub>v z) = \<bar>det A'\<bar> * (c \<bullet> z)"
      using \<open>c \<in> carrier_vec n\<close> \<open>z \<in> carrier_vec n\<close> carrier_vecD scalar_prod_smult_right
      by force
    also have "\<dots> = \<bar>det A'\<bar> * \<beta>"
      using \<open>c \<bullet> z = \<beta>\<close> by simp
    finally show ?thesis .
  qed
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
