theory Integer_Polyhedron
  imports Faces
    Linear_Inequalities.Integer_Hull
    Missing_Sums 
begin

context gram_schmidt
begin

lemma all_elem_fulfill_empty:
  assumes "(A', b') = sub_system A b {}"
  shows "A' *\<^sub>v x = b'" 
proof
  have "A' = submatrix A {} UNIV" 
  proof -
    have "fst (A', b') = fst (sub_system A b {})" using assms by simp
    then show ?thesis using sub_system_fst by simp
  qed
  then have "dim_row A' = 0" 
    by (simp add: dim_submatrix(1))
  have "b' = vec_of_list (nths (list_of_vec b) {})" 
  proof -
    have "b' = snd (A', b')" by (rule snd_conv[symmetric])
    also have "... = snd (sub_system A b {})" using assms by simp
    also have "... = vec_of_list (nths (list_of_vec b) {})" by (rule sub_system_snd)
    finally show "b' = vec_of_list (nths (list_of_vec b) {})" .
  qed
  then have "dim_vec b' = 0" 
    by fastforce
  show "dim_vec (A' *\<^sub>v x) = dim_vec b'" 
    by (simp add: \<open>dim_row A' = 0\<close> \<open>dim_vec b' = 0\<close>)
  show "\<And>i. i < dim_vec b' \<Longrightarrow>
         (A' *\<^sub>v x) $ i = b' $ i" 
    using \<open>dim_vec b' = 0\<close> by linarith
qed

lemma subsyst_with_max_ineq:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "P \<noteq> {}"
  obtains A' b' I'  where "((A', b') = sub_system A b I')" 
    "{x. A' *\<^sub>v x = b' \<and> x \<in> P} \<noteq> {}"
    "dim_vec b' = Max {dim_vec d| C d I. (C, d) = sub_system A b I \<and> 
                                                {x. C *\<^sub>v x = d \<and> x \<in> P} \<noteq> {}}"
proof-
  have "dim_vec b = nr" using b by auto
  let ?M = "{dim_vec d| C d I. (C, d) = sub_system A b I \<and> {x. C *\<^sub>v x = d \<and> x \<in> P} \<noteq> {}}"
  have "finite ?M"
    using subset_set_of_sub_dims_finite[of ?M A b] by blast
  let ?emp_A = "fst (sub_system A b {})"
  let ?emp_b = "snd (sub_system A b {})" 
  have "{x. ?emp_A *\<^sub>v x = ?emp_b \<and> x \<in> P} = P" 
  proof -
    have "(?emp_A, ?emp_b) = sub_system A b {}"
      by (simp add: prod.collapse)
    then have "\<And>x. ?emp_A *\<^sub>v x = ?emp_b"
      using all_elem_fulfill_empty by blast
    then show "{x. ?emp_A *\<^sub>v x = ?emp_b \<and> x \<in> P} = P"
      by blast
  qed
  then have "dim_vec ?emp_b \<in> ?M" using assms(4) 
    proof -
      have "(?emp_A, ?emp_b) = sub_system A b {}"
        by simp
      moreover have "{x. ?emp_A *\<^sub>v x = ?emp_b \<and> x \<in> P} \<noteq> {}"
        using \<open>{x. ?emp_A *\<^sub>v x = ?emp_b \<and> x \<in> P} = P\<close> assms(4) by simp
      ultimately show "dim_vec ?emp_b \<in> ?M"
        by blast
    qed
  then have "?M \<noteq> {}"  
    by blast
  then have "Max ?M \<in> ?M \<and> (\<forall>a \<in> ?M. a \<le> (Max ?M))"
    using eq_Max_iff[of ?M] `?M \<noteq> {}` `finite ?M` 
    by auto
  then show ?thesis 
    using that by force
qed

lemma submatrix_same_I_interesect_rows:
  shows "submatrix A I UNIV = submatrix A (I \<inter> {0..<dim_row A}) UNIV"
proof
  show 1:"dim_row (submatrix A I UNIV) = dim_row (submatrix A (I \<inter> {0..<dim_row A}) UNIV)" 
    using dim_submatrix 
  proof -
    have eq_sets: "{i. i < dim_row A \<and> i \<in> I} = {i. i < dim_row A \<and> i \<in> I \<inter> {0..<dim_row A}}"
      by auto
    show ?thesis
      unfolding dim_submatrix(1) using eq_sets by simp
  qed
  show 2:"dim_col (submatrix A I UNIV) = dim_col (submatrix A (I \<inter> {0..<dim_row A}) UNIV)" 
    using dim_submatrix 
  proof -
    have "{i. i < dim_row A \<and> i \<in> I} = {i. i < dim_row A \<and> i \<in> I \<inter> {0..<dim_row A}}"
      by (auto simp: atLeastLessThan_iff)
    then show ?thesis
      unfolding dim_submatrix(2) by simp
  qed
  show "\<And>i j. i < dim_row (submatrix A (I \<inter> {0..<dim_row A}) UNIV) \<Longrightarrow>
           j < dim_col (submatrix A (I \<inter> {0..<dim_row A}) UNIV) \<Longrightarrow>
           submatrix A I UNIV $$ (i, j) = submatrix A (I \<inter> {0..<dim_row A}) UNIV $$ (i, j)" 
  proof -
    fix i j
    assume asmi:"i < dim_row (submatrix A (I \<inter> {0..<dim_row A}) UNIV)" 
    assume asmj:"j < dim_col (submatrix A (I \<inter> {0..<dim_row A}) UNIV)" 
    have 2:"submatrix A I UNIV $$ (i, j) = A $$ (pick I i, pick UNIV j)" using submatrix_index
proof -
      have row_bound: "i < card {a. a < dim_row A \<and> a \<in> I}"
      proof -
        have "card {a. a < dim_row A \<and> a \<in> I} = dim_row (submatrix A I UNIV)"
          by (simp add: dim_submatrix(1))
        also have "... = dim_row (submatrix A (I \<inter> {0..<dim_row A}) UNIV)"
          using 1 by simp
        finally have eq: "card {a. a < dim_row A \<and> a \<in> I}
                         = dim_row (submatrix A (I \<inter> {0..<dim_row A}) UNIV)" .
        show ?thesis using asmi eq by simp
      qed
      have col_bound: "j < card {a. a < dim_col A \<and> a \<in> (UNIV :: nat set)}"
      proof -
        have eq: "dim_col (submatrix A (I \<inter> {0..<dim_row A}) UNIV)
                = card {a. a < dim_col A \<and> a \<in> (UNIV :: nat set)}"
          by (simp add: dim_submatrix(2))
        show ?thesis using asmj eq by simp
      qed
      from row_bound col_bound show ?thesis by (rule submatrix_index)
    qed
    have 3:"{a. a < dim_row A \<and> a \<in> I} = (I \<inter> {0..<dim_row A})" 
      by fastforce
    have "i < card {a. a < dim_row A \<and> a \<in> I}"
    proof -
      have "i < dim_row (submatrix A I UNIV)"
        using asmi by (simp add: 1)
      then show "i < card {a. a < dim_row A \<and> a \<in> I}"
        by (simp add: dim_submatrix(1))
    qed
    then have "pick (I  \<inter> {0..<dim_row A}) i= pick I i"
      using pick_reduce_set[of i "dim_row A" I] 3
      by presburger
    then show " submatrix A I UNIV $$ (i, j) = submatrix A (I \<inter> {0..<dim_row A}) UNIV $$ (i, j)"
  proof -
  have card_row: "i < card {a. a < dim_row A \<and> a \<in> (I \<inter> {0..<dim_row A})}"
    using asmi by (simp add: dim_submatrix(1))
  have card_col: "j < card {a. a < dim_col A \<and> a \<in> (UNIV :: nat set)}"
    using asmj by (simp add: dim_submatrix(2))
  have set_eq: "{a. a < dim_row A \<and> a \<in> (I \<inter> {0..<dim_row A})} = {a. a < dim_row A \<and> a \<in> I}"
    by auto
  have card_I: "i < card {a. a < dim_row A \<and> a \<in> I}"
    using card_row set_eq by simp
  have pick_eq: "pick (I \<inter> {0..<dim_row A}) i = pick I i"
    using pick_reduce_set [OF card_I] 3 by simp
  have step1: "submatrix A (I \<inter> {0..<dim_row A}) UNIV $$ (i, j)
        = A $$ (pick (I \<inter> {0..<dim_row A}) i, pick UNIV j)"
    by (rule submatrix_index [OF card_row card_col])
  have eq_final: "submatrix A (I \<inter> {0..<dim_row A}) UNIV $$ (i, j) = submatrix A I UNIV $$ (i, j)"
    using step1 pick_eq 2 by simp
  show "submatrix A I UNIV $$ (i, j) = submatrix A (I \<inter> {0..<dim_row A}) UNIV $$ (i, j)"
    by (simp add: eq_final)
qed
  qed
qed

lemma nths_intersect_length_same:
  shows "(nths l I) = (nths l {a. a < (length l) \<and> a \<in> I})" 
proof -
  have "\<forall> p \<in> set (zip l [0..<length l]). snd p \<in> I \<longleftrightarrow> snd p \<in> {a. a < length l \<and> a \<in> I}" 
    using zip_snd by force
  then have "filter (\<lambda>p. snd p \<in> I) (zip l [0..<length l]) = 
            filter (\<lambda>p. snd p \<in> {a. a < length l \<and> a \<in> I}) (zip l [0..<length l])"
    by (intro filter_cong[OF refl]) (use zip_snd in force)
  then show ?thesis 
    unfolding nths_def by argo
qed

lemma same_subsyst_I_intersect_rows:
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  shows "sub_system A b I = sub_system A b (I \<inter> {0..<nr})"
proof
  have "submatrix A I UNIV = submatrix A (I \<inter> {0..<dim_row A}) UNIV" 
    using submatrix_same_I_interesect_rows by blast

  have dim_eq: "dim_row A = nr" using A by (rule carrier_matD(1))
  have sub_eq: "submatrix A I UNIV = submatrix A (I \<inter> {0..<dim_row A}) UNIV" 
    using submatrix_same_I_interesect_rows by blast
  have "submatrix A I UNIV = submatrix A (I \<inter> {0..<nr}) UNIV" 
    using sub_eq dim_eq by simp
  thus "fst (sub_system A b I) = fst (sub_system A b (I \<inter> {0..<nr}))" 
    by (simp add: sub_system_fst)
  have "(nths (list_of_vec b) I) = (nths (list_of_vec b) {a. a < dim_vec b \<and> a \<in> I})"
    using nths_intersect_length_same 
    using nths_intersect_length_same[of "list_of_vec b" I]
    by (simp add: Matrix.length_list_of_vec)
  then have "vec_of_list (nths (list_of_vec b) I) = 
      vec_of_list (nths (list_of_vec b) (I\<inter> {0..<dim_vec b}))" 
  proof -
    assume prev: "nths (list_of_vec b) I = nths (list_of_vec b) {a. a < dim_vec b \<and> a \<in> I}"
    have "{a. a < dim_vec b \<and> a \<in> I} = I \<inter> {0..<dim_vec b}"
      by fastforce
    with prev have "nths (list_of_vec b) I = nths (list_of_vec b) (I \<inter> {0..<dim_vec b})"
      by simp
    then show ?thesis by simp
  qed
  then show "snd (sub_system A b I) = snd (sub_system A b (I \<inter> {0..<nr}))"
  proof -
    assume eq1: "vec_of_list (nths (list_of_vec b) I)
      = vec_of_list (nths (list_of_vec b) (I \<inter> {0..<dim_vec b}))"
    have dim_b: "dim_vec b = nr" using b carrier_vecD by blast
    have "snd (sub_system A b I) = vec_of_list (nths (list_of_vec b) I)"
      by (simp add: sub_system_snd)
    also have "\<dots> = vec_of_list (nths (list_of_vec b) (I \<inter> {0..<dim_vec b}))"
      using eq1 by simp
    also have "\<dots> = vec_of_list (nths (list_of_vec b) (I \<inter> {0..<nr}))"
      using dim_b by simp
    also have "\<dots> = snd (sub_system A b (I \<inter> {0..<nr}))"
      by (simp add: sub_system_snd)
    finally show "snd (sub_system A b I) = snd (sub_system A b (I \<inter> {0..<nr}))" .
  qed
qed

lemma obtain_I_for_subface:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "((A', b') = sub_system A b I)" 
  assumes "F = {x. A' *\<^sub>v x = b' \<and> x \<in> P}"
  assumes "face P F"
  assumes "face P F'"
  assumes "F' \<subset> F"
  obtains C d I' where "((C, d) = sub_system A b I')" 
    "F' = {x. C *\<^sub>v x = d \<and> x \<in> P}" "(I \<inter> {0..<nr}) \<subset> (I' \<inter> {0..<nr})"
proof -
  obtain C d J where C_d:"((C, d) = sub_system A b J)" 
    "F' = {x. C *\<^sub>v x = d \<and> x \<in> P}" using char_face1 
    using A P_def assms(7) b by blast
  obtain C' d' where  C'_d':"((C', d') = sub_system A b (J \<union> I))" 
    using prod.collapse[of "sub_system A b (J \<union> I)"] by blast
  have "dim_row A = dim_vec b"
    using carrier_matD(1)[OF A] carrier_vecD[OF b] by simp
  have "{x. C *\<^sub>v x = d \<and> x \<in> P} = {x. C' *\<^sub>v x = d' \<and> x \<in> P}"
  proof(safe)
    {
      fix x
      assume "x \<in> P" "d = C *\<^sub>v x"  
      have "x \<in> F" 
        using C_d(2) \<open>d = C *\<^sub>v x\<close> \<open>x \<in> P\<close> assms(8) by blast
      then have "A' *\<^sub>v x = b'" using assms(5) by auto
      then have "\<forall>i < dim_row A'. row A' i \<bullet> x = b' $ i" 
        proof (intro allI impI)
          fix i
          assume "i < dim_row A'"
          then have "(A' *\<^sub>v x) $ i = row A' i \<bullet> x"
            by (rule index_mult_mat_vec)
          then show "row A' i \<bullet> x = b' $ i"
            using \<open>A' *\<^sub>v x = b'\<close> by simp
        qed
      then have "\<forall>i \<in> I \<inter> {0..<dim_row A}.  (row A i) \<bullet> x = (b $ i)"
        using subsystem_fulfills_P[of A b A' b' I "\<lambda> p q. p \<bullet> x = q"] assms(4)
          `dim_row A = dim_vec b`  by blast
      have "\<forall>i < dim_row C. row C i \<bullet> x = d $ i" using `d = C *\<^sub>v x`
        by (simp add: index_mult_mat_vec)
      then have "\<forall>i \<in> J \<inter> {0..<dim_row A}.  (row A i) \<bullet> x = (b $ i)"
        using subsystem_fulfills_P[of A b C d J "\<lambda> p q. p \<bullet> x = q"] C_d
          `dim_row A = dim_vec b`  by blast
      have "\<forall>i \<in> (I \<union> J) \<inter> {0..<dim_row A}. (row A i) \<bullet> x = (b $ i)"
      proof
        fix i
        assume "i \<in> (I \<union> J) \<inter> {0..<dim_row A}"
        then have "i \<in> (I \<inter> {0..<dim_row A}) \<union> (J \<inter> {0..<dim_row A})"
          by (simp add: Int_Un_distrib2)
        then show "(row A i) \<bullet> x = (b $ i)"
          using \<open>\<forall>i\<in>I \<inter> {0..<dim_row A}. row A i \<bullet> x = b $ i\<close>
            \<open>\<forall>i\<in>J \<inter> {0..<dim_row A}. row A i \<bullet> x = b $ i\<close>
          by blast
      qed
      then have "\<forall>i < dim_row C'. row C' i \<bullet> x = d' $ i" 
        using subsystem_fulfills_P'[of A b C' d' _ "\<lambda> p q. p \<bullet> x = q"] C'_d'
        using \<open>dim_row A = dim_vec b\<close> by blast
      then show "C' *\<^sub>v x = d'" 
        by (meson C'_d' \<open>dim_row A = dim_vec b\<close> dims_subsyst_same' eq_for_all_index_then_eq)
    }
    fix x
    assume "x \<in> P" "d' = C' *\<^sub>v x"
    then have "\<forall>i < dim_row C'. row C' i \<bullet> x = d' $ i"
    proof (intro allI impI)
      fix i
      assume "i < dim_row C'"
      then show "row C' i \<bullet> x = d' $ i"
        using \<open>d' = C' *\<^sub>v x\<close> by (simp add: index_mult_mat_vec)
    qed
    then have "\<forall>i \<in> (I \<union> J) \<inter> {0..<dim_row A}. (row A i) \<bullet> x = (b $ i)"
      using subsystem_fulfills_P[of A b C' d' _ "\<lambda> p q. p \<bullet> x = q"] C'_d'
      using \<open>dim_row A = dim_vec b\<close> by blast
    then have "\<forall>i \<in> J \<inter> {0..<dim_row A}.  (row A i) \<bullet> x = (b $ i)" by auto
    then have "\<forall>i < dim_row C. row C i \<bullet> x = d $ i"
      using subsystem_fulfills_P'[of A b C d J "\<lambda> p q. p \<bullet> x = q"] C_d
        `dim_row A = dim_vec b`  by blast
    then show "C *\<^sub>v x = d"
      by (meson C_d \<open>dim_row A = dim_vec b\<close> dims_subsyst_same' eq_for_all_index_then_eq)
  qed  
  then have "F' = {x. C' *\<^sub>v x = d' \<and> x \<in> P}" using C_d by auto
  have "(I \<inter> {0..<nr}) \<subseteq> ((J \<union> I) \<inter> {0..<nr})" 
    by blast
  have "(I \<inter> {0..<nr}) \<noteq> ((J \<union> I) \<inter> {0..<nr})"
  proof
    assume "I \<inter> {0..<nr} = (J \<union> I) \<inter> {0..<nr}" 
    then have "sub_system A b I = sub_system A b (J \<union> I)" 
    proof -
      have "sub_system A b I = sub_system A b (I \<inter> {0..<nr})"
        using same_subsyst_I_intersect_rows[OF A b] .
      also have "\<dots> = sub_system A b ((J \<union> I) \<inter> {0..<nr})"
        by (simp only: \<open>I \<inter> {0..<nr} = (J \<union> I) \<inter> {0..<nr}\<close>)
      also have "\<dots> = sub_system A b (J \<union> I)"
        using same_subsyst_I_intersect_rows[OF A b] by simp
      finally show ?thesis .
    qed
    then have "{x. A' *\<^sub>v x = b' \<and> x \<in> P} = {x. C *\<^sub>v x = d \<and> x \<in> P}" 
    proof -
      have "(A', b') = sub_system A b (J \<union> I)"
        using assms(4) \<open>sub_system A b I = sub_system A b (J \<union> I)\<close> by simp
      also have "\<dots> = (C', d')"
        using \<open>(C', d') = sub_system A b (J \<union> I)\<close> by simp
      finally have pair_eq: "(A', b') = (C', d')" .
      then have "A' = C'" "b' = d'" by simp_all
      then show ?thesis
        using \<open>{x. C *\<^sub>v x = d \<and> x \<in> P} = {x. C' *\<^sub>v x = d' \<and> x \<in> P}\<close> by simp
    qed
    then show False using assms(8) 
      using C_d(2) assms(5) by blast
  qed
  then have "(I \<inter> {0..<nr}) \<subset> ((J \<union> I) \<inter> {0..<nr})" 
    by blast
  then show ?thesis using C'_d' `F' = {x. C' *\<^sub>v x = d' \<and> x \<in> P}` 
    using that by presburger
qed

lemma less_I_less_dims_subsystem:
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  assumes "(I \<inter> {0..<nr}) \<subset> (J \<inter> {0..<nr})" 
  assumes "((A', b') = sub_system A b I)"
  assumes  "((C, d) = sub_system A b J)"
  shows "dim_row A' < dim_row C"
    "dim_vec b' < dim_vec d" 
proof -
  have "sub_system A b I = sub_system A b (I \<inter> {0..<nr})"
    using same_subsyst_I_intersect_rows A b 
    by blast
  then have "dim_row A' = card (I \<inter> {0..<nr})" using I_subsys_same_card(2)
  proof -
  have eq_sub: "sub_system A b I = sub_system A b (I \<inter> {0..<nr})"
    using same_subsyst_I_intersect_rows A b by blast
  have AB': "(A', b') = sub_system A b (I \<inter> {0..<nr})"
    using assms(4) eq_sub by simp
  have subs: "I \<inter> {0..<nr} \<subseteq> {0..<nr}"
    by (rule inf.cobounded2)
  have dimA: "dim_row A = dim_vec b" using A b by simp
  have dims_eq: "dim_row A' = dim_vec b'"
    using dimA assms(4) dims_subsyst_same' by blast
  have snd_eq: "snd (sub_system A b (I \<inter> {0..<nr})) = b'"
    by (simp add: AB'[symmetric] snd_conv)
  have bcard: "dim_vec b' = card (I \<inter> {0..<nr})"
    using I_subsys_same_card(2)[OF A b subs] snd_eq by simp
  show "dim_row A' = card (I \<inter> {0..<nr})"
    using dims_eq bcard by simp
  qed
  have "sub_system A b J = sub_system A b (J \<inter> {0..<nr})"
    using same_subsyst_I_intersect_rows A b 
    by blast
  have "dim_row C = card (J \<inter> {0..<nr})"
  proof -
    have same_sub: "sub_system A b J = sub_system A b (J \<inter> {0..<nr})"
      using same_subsyst_I_intersect_rows A b by blast
    have pair_eq: "(C, d) = sub_system A b (J \<inter> {0..<nr})"
      using assms(5) same_sub by simp
    have subset_J: "J \<inter> {0..<nr} \<subseteq> {0..<nr}"
      by (rule inf.cobounded2)
    have snd_eq: "snd (sub_system A b (J \<inter> {0..<nr})) = d"
      by (simp add: pair_eq[symmetric] snd_conv)
    have card_eq: "card (J \<inter> {0..<nr}) = dim_vec d"
      using I_subsys_same_card(2)[OF A b subset_J] snd_eq by simp
    have dr_eq: "dim_row A = dim_vec b"
      using A b carrier_matD(1) carrier_vecD by fastforce
    have "dim_row C = dim_vec d"
      using dr_eq assms(5) dims_subsyst_same' by blast
    with card_eq show "dim_row C = card (J \<inter> {0..<nr})" by simp
  qed
  have "finite (J \<inter> {0..<nr})" 
    by blast
  then have "card (I \<inter> {0..<nr}) < card (J \<inter> {0..<nr})" 
    by (meson assms(3) psubset_card_mono)
  then show "dim_row A' < dim_row C" 
    using \<open>dim_row A' = card (I \<inter> {0..<nr})\<close> \<open>dim_row C = card (J \<inter> {0..<nr})\<close> by presburger
  have "dim_row A' = dim_vec b'" 
  proof -
    have "dim_row A = nr" using A carrier_matD(1) by blast
    moreover have "dim_vec b = nr" using b carrier_vecD by blast
    ultimately have "dim_row A = dim_vec b" by simp
    then show ?thesis using assms(4) dims_subsyst_same' by blast
  qed
  have "dim_row C = dim_vec d" 
  proof -
    have "dim_row A = nr" using A carrier_matD(1) by blast
    moreover have "dim_vec b = nr" using b carrier_vecD by blast
    ultimately have "dim_row A = dim_vec b" by simp
    then show "dim_row C = dim_vec d" using assms(5) dims_subsyst_same' by blast
  qed
  then show "dim_vec b' < dim_vec d" 
    using \<open>dim_row A' < dim_row C\<close> \<open>dim_row A' = dim_vec b'\<close> by presburger
qed

lemma append_rows_index_same:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes A: "A \<in> carrier_mat nr1 n"
  assumes "B \<in> carrier_mat nr2 n" 
  shows "\<forall> i < dim_row A. (row (A @\<^sub>r B)i) = row A i" 
proof (intro allI impI)
  fix i
  assume i_lt: "i < dim_row A"
  have dim_A: "dim_row A = nr1"
    using A by (rule carrier_matD(1))
  from i_lt dim_A have i_lt_nr1: "i < nr1"
    by simp
  show "row (A @\<^sub>r B) i = row A i"
    using append_rows_nth(1)[OF A assms(2) i_lt_nr1] by simp
qed

lemma append_rows_index_same':
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes A: "A \<in> carrier_mat nr1 n"
  assumes "B \<in> carrier_mat nr2 n" 
  shows "\<lbrakk> i \<ge> nr1; i < nr1 + nr2 \<rbrakk> \<Longrightarrow> (row (A @\<^sub>r B)i) = row B (i - nr1)" 
proof -
  assume i1: "i \<ge> nr1" and i2: "i < nr1 + nr2"
  show "row (A @\<^sub>r B) i = row B (i - nr1)"
    using A assms(2) i1 i2 append_rows_nth(2) by blast
qed

lemma face_trans:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "face P F"
  assumes "face F F'"
  shows "face P F'"
proof -
  obtain A' b' I' where A'_b':"((A', b') = sub_system A b I')
                              \<and> F = {x. A' *\<^sub>v x = b' \<and> x \<in> P}"
    using char_face1[of A nr b F] assms(1-4) 
    unfolding P_def 
    by blast
  then obtain C d  where C_d:"C = (A @\<^sub>r(A' @\<^sub>r (-A')))" "d = (b @\<^sub>v (b' @\<^sub>v (-b')))"  
    "F = polyhedron C d"
    "dim_row (A @\<^sub>r (A' @\<^sub>r (-A'))) = dim_vec (b @\<^sub>v(b' @\<^sub>v (-b')))"
    "dim_col (A @\<^sub>r(A' @\<^sub>r (-A'))) = n"
    using face_is_polyhedron''2[of A nr b A' b' I' F] 
  proof -
    have sub: "(A', b') = sub_system A b I'"
      using A'_b' by simp
    have FP: "F = {x \<in> carrier_vec n. A' *\<^sub>v x = b' \<and> A *\<^sub>v x \<le> b}"
      using A'_b' A b unfolding P_def gram_schmidt.polyhedron_def
      by auto
    show ?thesis
      by (rule that[OF refl refl
            face_is_polyhedron''2(1)[OF A b sub FP]
            face_is_polyhedron''2(2)[OF A b sub FP]
            face_is_polyhedron''2(3)[OF A b sub FP]])
  qed

  have C_dims: "dim_row C = dim_vec d"
    using C_d(1) C_d(2) C_d(4) by simp
  have C_cols: "dim_col C = n"
    using C_d(1) C_d(5) by simp
  have C_carr: "C \<in> carrier_mat (dim_row C) n"
    using C_cols by blast
  have d_carr: "d \<in> carrier_vec (dim_row C)"
    using C_dims by simp
  obtain C' d' J where C'_d': "((C', d') = sub_system C d J)
                              \<and> F' = {x. C' *\<^sub>v x = d' \<and> x \<in> F}"
    using char_face1[of C "dim_row C" d F'] assms(1-5) C_carr d_carr
    unfolding `F = polyhedron C d`
    by blast
  obtain A'' b'' where A''_b'': "((A'', b'') = sub_system A b (I' \<union> J))" 
    proof -
      obtain A''' b''' where "sub_system A b (I' \<union> J) = (A''', b''')"
        by (cases "sub_system A b (I' \<union> J)") auto
      then show thesis
        by (intro that[of A''' b''']) simp
    qed
  have "dim_row A'' = dim_vec b''" 
  proof -
    have "dim_row A = dim_vec b" using A b by (simp add: carrier_matD(1) carrier_vecD)
    then show "dim_row A'' = dim_vec b''" using A''_b'' dims_subsyst_same' by blast
  qed
  have "dim_row A \<le> dim_row C" using C_d 
proof -
  have "dim_row C = dim_row (A @\<^sub>r (A' @\<^sub>r (-A')))"
    using C_d(1) by simp
  also have "... = dim_vec (b @\<^sub>v (b' @\<^sub>v (-b')))"
    using C_d(4) by simp
  also have "... = dim_vec b + dim_vec (b' @\<^sub>v (-b'))"
    using index_append_vec(2) by simp
  finally have "dim_row C = dim_vec b + dim_vec (b' @\<^sub>v (-b'))" .
  moreover have "dim_vec b = nr"
    using b carrier_vecD by blast
  moreover have "dim_row A = nr"
    using A carrier_matD(1) by blast
  ultimately show "dim_row A \<le> dim_row C" by simp
qed
  have "\<forall> i < dim_row A. (row C i) = row A i" 
    using C_d(1) append_rows_index_same[of A nr "A' @\<^sub>r - A'" _]  
  proof -
    have "dim_col A' = n"
    proof -
      have fa: "fst (sub_system A b I') = A'"
        using arg_cong[where f = fst, OF A'_b'[THEN conjunct1]] by simp
      have "dim_col (fst (sub_system A b I')) = n"
        using dim_col_subsyst_mat[of A b I'] carrier_matD(2)[OF A] by simp
      then show "dim_col A' = n"
        using fa by simp
    qed
    then have "dim_col (A' @\<^sub>r - A') = n"
      using A A'_b' b face_is_polyhedron'(3) by blast
    then have "A' @\<^sub>r - A' \<in> carrier_mat (dim_row (A' @\<^sub>r - A')) n"
      using carrier_matI by blast
    then have "\<forall> i < dim_row A. row (A @\<^sub>r (A' @\<^sub>r - A')) i = row A i"
      using A append_rows_index_same[of A nr "A' @\<^sub>r - A'" "dim_row (A' @\<^sub>r - A')"]
      by blast
    then show "\<forall> i < dim_row A. (row C i) = row A i"
      using C_d(1) by simp
  qed
  have "\<forall> i < dim_vec b. d $ i = b $ i" 
    unfolding C_d(2)
    by (meson index_append_vec(1) trans_less_add1)
  then have 3:"\<forall> i < dim_row A. (row C i) = row A i \<and> d $ i = b $ i" 
  proof -
    have "dim_row A = dim_vec b"
      using carrier_matD(1)[OF A] carrier_vecD[OF b] by simp
    then show ?thesis
      using \<open>\<forall> i < dim_row A. (row C i) = row A i\<close> \<open>\<forall> i < dim_vec b. d $ i = b $ i\<close>
      by auto
  qed
  have "dim_row A' = dim_vec b'" 
  proof -
    have "dim_row A = dim_vec b"
      using A b carrier_matD(1) carrier_vecD by fastforce
    then show "dim_row A' = dim_vec b'"
      using A'_b' dims_subsyst_same' by blast
  qed
  have "dim_col A' = n"
  proof -
    have "A' = fst (sub_system A b I')"
    proof -
      have "(A', b') = sub_system A b I'" using A'_b' by simp
      then have "fst (A', b') = fst (sub_system A b I')" by (rule arg_cong)
      then show ?thesis by simp
    qed
    then have "dim_col A' = dim_col A"
      by (simp add: dim_col_subsyst_mat)
    then show ?thesis
      using A by (simp add: carrier_matD(2))
  qed
  then have "dim_col (A' @\<^sub>r - A') = n" 
    using A A'_b' b face_is_polyhedron'(3) by blast
  then have "A' @\<^sub>r - A' \<in> carrier_mat (dim_row (A' @\<^sub>r - A')) n" 
    by blast
  have "dim_row C = nr + dim_row (A' @\<^sub>r - A')" 
    using A A'_b' C_d(1) C_d(4) b face_is_polyhedron'(2) by force
  have 1:"\<forall> i. (i \<ge> nr \<and> i < dim_row C) \<longrightarrow> (row C i) = row  (A' @\<^sub>r - A') (i - nr)" 
    using C_d(1) append_rows_index_same'[of A nr "A' @\<^sub>r - A'" "dim_row (A' @\<^sub>r - A')"] 
      `A' @\<^sub>r - A' \<in> carrier_mat (dim_row (A' @\<^sub>r - A')) n` A
  proof (intro allI impI)
    fix i
    assume "i \<ge> nr \<and> i < dim_row C"
    then have i_ge: "i \<ge> nr" and i_lt: "i < dim_row C" by auto
    then have "i < nr + dim_row (A' @\<^sub>r - A')"
      using \<open>dim_row C = nr + dim_row (A' @\<^sub>r - A')\<close> by simp
    then have "row (A @\<^sub>r (A' @\<^sub>r - A')) i = row (A' @\<^sub>r - A') (i - nr)"
      using append_rows_index_same'[of A nr "A' @\<^sub>r - A'" "dim_row (A' @\<^sub>r - A')" i]
        \<open>A' @\<^sub>r - A' \<in> carrier_mat (dim_row (A' @\<^sub>r - A')) n\<close> A i_ge
      by blast
    then show "row C i = row (A' @\<^sub>r - A') (i - nr)"
      using C_d(1) by simp
  qed
  have "\<forall> i. i > nr \<and> i < dim_vec d \<longrightarrow> d $ i =  (b' @\<^sub>v (-b')) $ (i - nr)" 
    unfolding C_d(2) 
    using b by auto
  then have 5:"\<forall> i \<in> {nr..<dim_row C}. (row C i) = row  (A' @\<^sub>r - A') (i - nr) 
            \<and> d $ i =  (b' @\<^sub>v (-b')) $ (i - nr)" 
  proof (intro ballI)
    fix i
    assume i_mem: "i \<in> {nr..<dim_row C}"
    then have i_ge: "i \<ge> nr" and i_lt: "i < dim_row C"
      by auto
    have row_eq: "row C i = row (A' @\<^sub>r - A') (i - nr)"
      using 1 i_ge i_lt by blast
    have dim_row_C: "dim_row C = dim_vec d"
      using C_d(1) C_d(2) C_d(4) by simp
    have i_lt_d: "i < dim_vec d"
      using i_lt dim_row_C by simp
    have dim_b: "dim_vec b = nr"
      using b by simp
    have d_eq: "d $ i = (b' @\<^sub>v (-b')) $ (i - nr)"
    proof -
      have dim_sum: "dim_vec d = dim_vec b + dim_vec (b' @\<^sub>v (-b'))"
        using C_d(2) index_append_vec(2) by simp
      have i_lt_sum: "i < dim_vec b + dim_vec (b' @\<^sub>v (-b'))"
        using i_lt_d dim_sum by simp
      have not_lt: "\<not> i < dim_vec b"
        using dim_b i_ge by simp
      have "d $ i = (if i < dim_vec b then b $ i else (b' @\<^sub>v (-b')) $ (i - dim_vec b))"
        using C_d(2) i_lt_sum index_append_vec(1) by simp
      also have "... = (b' @\<^sub>v (-b')) $ (i - dim_vec b)"
        using not_lt by simp
      also have "... = (b' @\<^sub>v (-b')) $ (i - nr)"
        using dim_b by simp
      finally show ?thesis .
    qed
    from row_eq d_eq show "row C i = row (A' @\<^sub>r - A') (i - nr) \<and> d $ i = (b' @\<^sub>v (-b')) $ (i - nr)"
      by blast
  qed
  have " \<forall> x \<in> F. A' *\<^sub>v x = b' "using A'_b' by auto
  then have "\<forall> x \<in> F. \<forall>i < dim_row A'. row A' i \<bullet> x = b' $ i" 
    using index_mult_mat_vec
    by (auto simp: index_mult_mat_vec)
  have 2:"\<forall> x \<in> F. \<forall>i \<in> I' \<inter> {0..<dim_row A}.  (row A i) \<bullet> x = (b $ i)"
  proof
    fix x
    assume "x \<in> F"
    then have "A' *\<^sub>v x = b'"
      using A'_b' by blast
    have "\<forall>i < dim_row A'. row A' i \<bullet> x = b' $ i"
    proof (intro allI impI)
      fix i
      assume "i < dim_row A'"
      then have "(A' *\<^sub>v x) $ i = row A' i \<bullet> x"
        by (simp add: index_mult_mat_vec)
      then show "row A' i \<bullet> x = b' $ i"
        using \<open>A' *\<^sub>v x = b'\<close> by simp
    qed
    moreover have "dim_row A = dim_vec b"
      using carrier_matD(1)[OF A] carrier_vecD[OF b] by simp
    ultimately show "\<forall>i \<in> I' \<inter> {0..<dim_row A}. row A i \<bullet> x = b $ i"
      using subsystem_fulfills_P[of A b A' b' I' "\<lambda> p q. p \<bullet> x = q"] A b A'_b'
      by blast
  qed
  have "\<forall>x \<in> F. dim_vec x = dim_col A'" 
  proof
    fix x
    assume "x \<in> F"
    then have "x \<in> P" 
      using assms(4) face_subset_polyhedron by blast
    then have "x \<in> carrier_vec n" unfolding P_def polyhedron_def by blast
    have "dim_col A' = n" using A'_b' dim_col_subsyst_mat 
    proof -
      have "fst (A', b') = fst (sub_system A b I')"
        using A'_b' by simp
      hence A'_eq: "A' = fst (sub_system A b I')"
        by simp
      have dim_col_eq: "dim_col (fst (sub_system A b I')) = dim_col A"
        by (rule dim_col_subsyst_mat)
      have "dim_col A' = dim_col A"
        using A'_eq dim_col_eq by simp
      also have "\<dots> = n"
        using A by (rule carrier_matD(2))
      finally show ?thesis .
    qed
    then show "dim_vec x = dim_col A'" 
      using \<open>x \<in> carrier_vec n\<close> carrier_vecD by blast
  qed
  then have "\<forall> x \<in> F. A' *\<^sub>v x \<le> b' \<and> (-A') *\<^sub>v x \<le> - b'" 
    using `\<forall> x \<in> F. A' *\<^sub>v x = b'` eq_system_is_leq_system by blast 
  then have "\<forall> x \<in> F. (A' @\<^sub>r (-A')) *\<^sub>v x = (b' @\<^sub>v (-b'))" using append_rows_le 
proof (intro ballI)
  fix x
  assume "x \<in> F"
  then have eq: "A' *\<^sub>v x = b'"
    using \<open>\<forall>x\<in>F. A' *\<^sub>v x = b'\<close> by blast
  from \<open>x \<in> F\<close> have dimx: "dim_vec x = dim_col A'"
    using \<open>\<forall>x\<in>F. dim_vec x = dim_col A'\<close> by blast
  have xcarr: "x \<in> carrier_vec (dim_col A')"
    unfolding dimx[symmetric] by (rule carrier_vec_dim_vec)
  have A'carr: "A' \<in> carrier_mat (dim_row A') (dim_col A')"
    by (rule carrier_mat_triv)
  have negA'carr: "(-A') \<in> carrier_mat (dim_row A') (dim_col A')"
  proof -
    have "dim_row (-A') = dim_row A'" "dim_col (-A') = dim_col A'"
      by simp_all
    then show ?thesis using carrier_mat_triv[of "-A'"] by simp
  qed
  have negeq: "(-A') *\<^sub>v x = - (A' *\<^sub>v x)"
    using A'carr xcarr by (simp add: uminus_mult_mat_vec)
  have "(A' @\<^sub>r (-A')) *\<^sub>v x = (A' *\<^sub>v x) @\<^sub>v ((-A') *\<^sub>v x)"
    using A'carr negA'carr xcarr by (rule mat_mult_append)
  also have "\<dots> = b' @\<^sub>v (- b')"
    using eq negeq by simp
  finally show "(A' @\<^sub>r (-A')) *\<^sub>v x = (b' @\<^sub>v (-b'))" .
qed
  have "dim_row C = dim_vec d" 
    using C_d(1) C_d(2) C_d(4) by blast
  have "dim_row C' = dim_vec d'" using C'_d' 
    using \<open>dim_row C = dim_vec d\<close> dims_subsyst_same' by blast
  have "{x. C' *\<^sub>v x = d' \<and> x \<in> F} = {x. A'' *\<^sub>v x = b'' \<and> x \<in> P}"
  proof(safe)
    {
      fix x
      assume "x \<in> F" "d' = C' *\<^sub>v x" 
      have "\<forall>i < dim_row C'. row C' i \<bullet> x = d' $ i" using `d' = C' *\<^sub>v x`
        by (simp add: index_mult_mat_vec)
      then have "\<forall>i \<in> J \<inter> {0..<dim_row C}.  (row C i) \<bullet> x = (d $ i)"
        using subsystem_fulfills_P[of C d C' d' J "\<lambda> p q. p \<bullet> x = q"] C_d
        using C'_d' by blast
      then have "\<forall>i \<in> J \<inter> {0..<dim_row A}.  (row C i) \<bullet> x = (d $ i)" 
      proof -
        show ?thesis
        proof
          fix i
          assume "i \<in> J \<inter> {0..<dim_row A}"
          then have iC: "i \<in> J \<inter> {0..<dim_row C}"
            using \<open>dim_row A \<le> dim_row C\<close> by auto
          then show "row C i \<bullet> x = d $ i"
            using \<open>\<forall>i\<in>J \<inter> {0..<dim_row C}.  (row C i) \<bullet> x = (d $ i)\<close> by blast
        qed
      qed
      have "\<forall>i \<in> J \<inter> {0..<dim_row A}.  (row A i) \<bullet> x = (b $ i)"
        proof
          fix i
          assume i_mem: "i \<in> J \<inter> {0..<dim_row A}"
          then have i_lt: "i < dim_row A" by simp
          have eq1: "row C i = row A i" and eq2: "d $ i = b $ i"
            using i_lt `\<forall> i < dim_row A. (row C i) = row A i \<and> d $ i = b $ i` by auto
          have eq3: "row C i \<bullet> x = d $ i"
            using \<open>\<forall>i\<in>J \<inter> {0..<dim_row A}. row C i \<bullet> x = d $ i\<close> i_mem by blast
          have "row A i \<bullet> x = row C i \<bullet> x" using eq1 by simp
          also have "... = d $ i" using eq3 by simp
          also have "... = b $ i" using eq2 by simp
          finally show "row A i \<bullet> x = b $ i" .
        qed
      note fact_J = this
      have fact_I': "\<forall>i \<in> I' \<inter> {0..<dim_row A}.  (row A i) \<bullet> x = (b $ i)"
        using 2 \<open>x \<in> F\<close> by blast
      have "\<forall>i \<in> (I' \<union> J) \<inter> {0..<dim_row A}.  (row A i) \<bullet> x = (b $ i)"
        unfolding Int_Un_distrib2
        using fact_I' fact_J by blast
      then have "\<forall> i < dim_row A''. (row A'' i) \<bullet> x =  (b'' $ i)" 
        using subsystem_fulfills_P'[of A b A'' b'' "I' \<union> J" "\<lambda> p q. p \<bullet> x = q"] 
        using A A''_b'' b carrier_vecD carrier_matD(1)
        by fastforce
      then show " A'' *\<^sub>v x = b''"
        using eq_for_all_index_then_eq[of A'' b'' x] `dim_row A'' = dim_vec b''` by auto
    }
    show "\<And>x.  x \<in> F \<Longrightarrow> d' = C' *\<^sub>v x \<Longrightarrow> x \<in> P" 
      using assms(4) gram_schmidt.face_subset_polyhedron by blast
    {
      fix x
      assume "x \<in> P" "b'' = A'' *\<^sub>v x" 
      then have "\<forall> i < dim_row A''. (row A'' i) \<bullet> x =  (b'' $ i)"
        proof (intro allI impI)
          fix i
          assume "i < dim_row A''"
          then have "(A'' *\<^sub>v x) $ i = row A'' i \<bullet> x"
            by (rule index_mult_mat_vec)
          then show "row A'' i \<bullet> x = b'' $ i"
            using \<open>b'' = A'' *\<^sub>v x\<close> by simp
        qed
      then have 4:"\<forall>i \<in> (J \<union> I') \<inter> {0..<dim_row A}.  (row A i) \<bullet> x = (b $ i)"
        using subsystem_fulfills_P[of A b A'' b'' _ "\<lambda> p q. p \<bullet> x = q"] 
        using A A''_b'' b carrier_vecD by blast
      then have 6:"\<forall>i \<in> J \<inter> {0..<dim_row A}.  (row C i) \<bullet> x = (d $ i)"  
      proof -
        show "\<forall>i \<in> J \<inter> {0..<dim_row A}.  (row C i) \<bullet> x = (d $ i)"
        proof
          fix i
          assume "i \<in> J \<inter> {0..<dim_row A}"
          then have iJ: "i \<in> J" and iA: "i < dim_row A" by auto
          have iUnion: "i \<in> (J \<union> I') \<inter> {0..<dim_row A}" using iJ iA by auto
          have eqA: "row A i \<bullet> x = b $ i" using 4 iUnion by blast
          have eqC: "row C i = row A i \<and> d $ i = b $ i" using 3 iA by blast
          from eqC eqA show "row C i \<bullet> x = d $ i" by simp
        qed
      qed
      have "\<forall>i \<in> I' \<inter> {0..<dim_row A}.  (row A i) \<bullet> x = (b $ i)"  
        using 4 by auto
      then have "\<forall> i < dim_row A'. (row A' i) \<bullet> x =  (b' $ i)"
        using subsystem_fulfills_P'[of A b A' b' I' "\<lambda> p q. p \<bullet> x = q"] 
          A'_b'
        using A b carrier_vecD by blast
      then have "A' *\<^sub>v x = b'" 
        using eq_for_all_index_then_eq[of A' b' x] `dim_row A' = dim_vec b'` by auto
      have "dim_vec x = dim_col A'" 
      proof -
        have "x \<in> carrier_vec n" 
          using `x \<in> P`unfolding P_def polyhedron_def by blast
        have "dim_col A' = n" using A'_b' dim_col_subsyst_mat 
        proof -
          have AB': "(A', b') = sub_system A b I'"
            using A'_b' by blast
          have A'_eq: "A' = fst (sub_system A b I')"
            by (simp add: AB'[symmetric])
          have "dim_col A' = dim_col A"
            using A'_eq dim_col_subsyst_mat by simp
          then show "dim_col A' = n"
            using A by (simp add: carrier_matD(2))
        qed
        then show "dim_vec x = dim_col A'" 
          using \<open>x \<in> carrier_vec n\<close> carrier_vecD by blast
      qed
      then have "A' *\<^sub>v x \<le> b' \<and> (-A') *\<^sub>v x \<le> - b'"
        using eq_system_is_leq_system `A' *\<^sub>v x = b'` by blast
      then have "(A' @\<^sub>r (-A')) *\<^sub>v x = (b' @\<^sub>v (-b'))"  
      proof -
        have xA': "x \<in> carrier_vec (dim_col A')"
          using carrier_vec_dim_vec[of x] \<open>dim_vec x = dim_col A'\<close> by simp
        have A'car: "A' \<in> carrier_mat (dim_row A') (dim_col A')"
          by (rule carrier_mat_triv)
        have negA'car: "(-A') \<in> carrier_mat (dim_row A') (dim_col A')"
          using carrier_mat_triv[of "-A'"] by (simp add: index_uminus_mat)
        have split: "(A' @\<^sub>r (-A')) *\<^sub>v x = (A' *\<^sub>v x) @\<^sub>v ((-A') *\<^sub>v x)"
          using mat_mult_append[OF A'car negA'car xA'] by simp
        have neg: "(-A') *\<^sub>v x = - (A' *\<^sub>v x)"
          using uminus_mult_mat_vec[of x A'] \<open>dim_vec x = dim_col A'\<close> by simp
        show "(A' @\<^sub>r (-A')) *\<^sub>v x = (b' @\<^sub>v (-b'))"
          using split neg \<open>A' *\<^sub>v x = b'\<close> by simp
      qed
      then have "\<forall>i \<in> {dim_row A..<dim_row C}.  (row C i) \<bullet> x = (d $ i)"
      proof -
        have dimA: "dim_row A = nr" using A carrier_matD(1) by blast
        show "\<forall>i \<in> {dim_row A..<dim_row C}.  (row C i) \<bullet> x = (d $ i)"
        proof
          fix i
          assume "i \<in> {dim_row A..<dim_row C}"
          then have i_range: "i \<ge> nr" "i < dim_row C" using dimA by auto
          then have i_in: "i \<in> {nr..<dim_row C}" by simp
          have "row C i = row (A' @\<^sub>r - A') (i - nr) \<and> d $ i = (b' @\<^sub>v (-b')) $ (i - nr)"
            using 5 i_in by blast
          then have row_eq: "row C i = row (A' @\<^sub>r - A') (i - nr)"
            and d_eq: "d $ i = (b' @\<^sub>v (-b')) $ (i - nr)"
            by auto
          have i_lt: "i - nr < dim_row (A' @\<^sub>r - A')"
            using i_range \<open>dim_row C = nr + dim_row (A' @\<^sub>r - A')\<close> by linarith
          have "((A' @\<^sub>r (-A')) *\<^sub>v x) $ (i - nr) = (b' @\<^sub>v (-b')) $ (i - nr)"
            using \<open>(A' @\<^sub>r (-A')) *\<^sub>v x = (b' @\<^sub>v (-b'))\<close> by simp
          then have "row (A' @\<^sub>r - A') (i - nr) \<bullet> x = (b' @\<^sub>v (-b')) $ (i - nr)"
            using index_mult_mat_vec i_lt by simp
          then show "(row C i) \<bullet> x = (d $ i)"
            using row_eq d_eq by simp
        qed
      qed
      then have "\<forall>i \<in> J \<inter> {0..<dim_row C}.  (row C i) \<bullet> x = (d $ i)" 
      proof -
        show "\<forall>i \<in> J \<inter> {0..<dim_row C}.  (row C i) \<bullet> x = (d $ i)"
        proof (rule ballI)
          fix i
          assume "i \<in> J \<inter> {0..<dim_row C}"
          then have "i \<in> J" and "i < dim_row C" by auto
          show "row C i \<bullet> x = d $ i"
          proof (cases "i < dim_row A")
            case True
            then have "i \<in> J \<inter> {0..<dim_row A}" using \<open>i \<in> J\<close> by simp
            then show ?thesis using 6 by blast
          next
            case False
            then have "i \<in> {dim_row A..<dim_row C}" using \<open>i < dim_row C\<close> by (simp add: atLeastLessThan_iff)
            then show ?thesis
              using \<open>\<forall>i \<in> {dim_row A..<dim_row C}.  (row C i) \<bullet> x = (d $ i)\<close> by blast
          qed
        qed
      qed
      then have "\<forall> i < dim_row C'. (row C' i) \<bullet> x =  (d' $ i)"
        using subsystem_fulfills_P'[of C d C' d' J "\<lambda> p q. p \<bullet> x = q"] C'_d'   
        using C_d by blast
      then show " C' *\<^sub>v x = d'"
        using eq_for_all_index_then_eq[of C' d' x] `dim_row C' = dim_vec d'` by auto
      show "x \<in> F" using  A'_b' `A' *\<^sub>v x = b'` `x \<in> P` by blast
    }
  qed
  have "F' = {x. A'' *\<^sub>v x = b'' \<and> x \<in> P}" 
    using C'_d' \<open>{x. C' *\<^sub>v x = d' \<and> x \<in> F} = {x. A'' *\<^sub>v x = b'' \<and> x \<in> P}\<close> by fastforce
  then show ?thesis using char_face2[of A nr b A'' b'' "(I' \<union> J)" F'] 
    using A A''_b'' P_def assms(5) b face_non_empty by presburger
qed

lemma subsyst_with_max_ineq_is_min_face:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "((A', b') = sub_system A b I)" 
  assumes "{x. A' *\<^sub>v x = b' \<and> x \<in> P} \<noteq> {}"
  assumes "dim_vec b' = Max {dim_vec d| C d I. (C, d) = sub_system A b I \<and> 
                                                {x. C *\<^sub>v x = d \<and> x \<in> P} \<noteq> {}}"
  shows "min_face P {x. A' *\<^sub>v x = b' \<and> x \<in> P}"
proof
  show "face P {x. A' *\<^sub>v x = b' \<and> x \<in> P}" 
    using char_face2[of A nr b A' b' I "{x. A' *\<^sub>v x = b' \<and> x \<in> P}"]
    unfolding P_def 
    using A P_def assms(4) assms(5) b by blast
  show " \<not> (\<exists>F'\<subset>{x. A' *\<^sub>v x = b' \<and> x \<in> P}. face P F')" 
  proof
    assume "\<exists>F'\<subset>{x. A' *\<^sub>v x = b' \<and> x \<in> P}. face P F'" 
    obtain F' where F':"F'\<subset>{x. A' *\<^sub>v x = b' \<and> x \<in> P} \<and> face P F'" 
      using \<open>\<exists>F'\<subset>{x. A' *\<^sub>v x = b' \<and> x \<in> P}. face P F'\<close> by presburger
    then obtain C d I' where C_d:"((C, d) = sub_system A b I')
                              \<and> F' = {x. C *\<^sub>v x = d \<and> x \<in> P}" "(I \<inter> {0..<nr}) \<subset> (I' \<inter> {0..<nr})" 
      using obtain_I_for_subface[of A nr b A' b' I "{x. A' *\<^sub>v x = b' \<and> x \<in> P}" F']
      using A b P_def `face P {x. A' *\<^sub>v x = b' \<and> x \<in> P}` assms(4) 
      by force
    then have "dim_vec b' < dim_vec d" 
      using less_I_less_dims_subsystem[of A nr b I I' A' b' C d]
            A assms(4) b by blast
    have 1:"dim_vec d \<in> {dim_vec d| C d I. (C, d) = sub_system A b I \<and> 
                                                {x. C *\<^sub>v x = d \<and> x \<in> P} \<noteq> {}}" 
    proof -
      have "{x. C *\<^sub>v x = d \<and> x \<in> P} \<noteq> {}"
        using C_d(1) F' face_non_empty by blast
      then show ?thesis
        using C_d(1) by blast
    qed
    have "dim_vec b = nr" using b by auto
    let ?M = "{dim_vec d| C d I. (C, d) = sub_system A b I \<and> {x. C *\<^sub>v x = d \<and> x \<in> P} \<noteq> {}}"
    have "finite ?M"
      using subset_set_of_sub_dims_finite[of ?M A b] by blast
    have "?M \<noteq> {}" using 1
      by blast
    then have "Max ?M \<in> ?M \<and> (\<forall>a \<in> ?M. a \<le> (Max ?M))"
      using eq_Max_iff[of ?M] `?M \<noteq> {}` `finite ?M` 
      by auto
    then have "dim_vec d \<le> dim_vec b'"
      using eq_Max_iff 
      using "1" assms(6) by auto
    then show False 
      using \<open>dim_vec b' < dim_vec d\<close> linorder_not_less by blast
  qed
qed

lemma obtain_min_face_polyhedron:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "P \<noteq> {}"
  obtains F where "min_face P F"
proof -
  obtain A' b' I'  where "((A', b') = sub_system A b I')" 
    "{x. A' *\<^sub>v x = b' \<and> x \<in> P} \<noteq> {}"
    "dim_vec b' = Max {dim_vec d| C d I. (C, d) = sub_system A b I \<and> 
                                                {x. C *\<^sub>v x = d \<and> x \<in> P} \<noteq> {}}"
    using  subsyst_with_max_ineq[of A nr b] assms 
    by blast 
  then have "min_face P {x. A' *\<^sub>v x = b' \<and> x \<in> P}" 
    using subsyst_with_max_ineq_is_min_face[of A nr b A' b' I'] assms by fast
  then show ?thesis 
    by (simp add: that)
qed

lemma face_contains_min_face:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "face P F" 
  shows "\<exists> F'. F' \<subseteq> F \<and> min_face P F'"
proof -
  obtain C d where C_d:"F = polyhedron C d" "dim_row C = dim_vec d" "dim_col C = n"
    using A b P_def assms(4) face_is_polyhedron by blast
  have "F \<noteq> {}" 
    using assms(4) face_non_empty by auto
  have C_carrier: "C \<in> carrier_mat (dim_row C) n"
    using carrier_mat_triv[of C] C_d(3) by blast
  have d_carrier: "d \<in> carrier_vec (dim_row C)"
    using carrier_vec_dim_vec[of d] C_d(2) by simp
  have poly_ne: "polyhedron C d \<noteq> {}"
    using C_d(1) \<open>F \<noteq> {}\<close> by simp
  obtain F' where minF: "min_face (polyhedron C d) F'"
    using obtain_min_face_polyhedron[OF C_carrier d_carrier poly_ne] by blast
  then have "min_face F F'"
    using C_d(1) by simp
  have "face P F'" 
    using A P_def \<open>min_face F F'\<close> assms(4) b min_face_elim(1) face_trans by presburger
  have "\<not> (\<exists>S\<subset>F'. face F S)" 
    by (simp add: \<open>min_face F F'\<close> min_face_elim(2))
  then have "\<not> (\<exists>S\<subset>F'. face P S)" 
    by (meson \<open>min_face F F'\<close> assms(4) face_subset_polyhedron subset_is_face min_face_elim(1)
        psubset_imp_subset subset_trans)
  then have "min_face P F'" 
    using \<open>face P F'\<close> by blast
  then show ?thesis 
    by (meson \<open>min_face F F'\<close> face_subset_polyhedron min_face_elim(1))
qed

lemma int_all_min_faces_then_int_all_faces:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "\<forall> F. min_face P F \<longrightarrow> (\<exists> x \<in> F. x \<in> \<int>\<^sub>v)"
  shows "\<forall> F. face P F \<longrightarrow> (\<exists> x \<in> F. x \<in> \<int>\<^sub>v)"
proof safe
  fix F
  assume "face P F" 
  then obtain F' where "F' \<subseteq> F \<and> min_face P F'"
    using face_contains_min_face[OF A b \<open>face P F\<close>[unfolded P_def], folded P_def] by blast
  then show "\<exists> x \<in> F. x \<in> \<int>\<^sub>v" 
    by (meson assms(4) subset_iff)
qed

lemma int_all_faces_then_int_all_min_faces:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "\<forall> F. face P F \<longrightarrow> (\<exists> x \<in> F. x \<in> \<int>\<^sub>v)"
  shows "\<forall> F. min_face P F \<longrightarrow> (\<exists> x \<in> F. x \<in> \<int>\<^sub>v)" 
  using assms(4) min_face_elim(1) 
  by presburger

lemma int_all_min_faces_iff_int_all_faces:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  shows "(\<forall> F. min_face P F \<longrightarrow> (\<exists> x \<in> F. x \<in> \<int>\<^sub>v)) \<longleftrightarrow> (\<forall> F. face P F \<longrightarrow> (\<exists> x \<in> F. x \<in> \<int>\<^sub>v))"
  using int_all_min_faces_then_int_all_faces[of A nr b]
    int_all_faces_then_int_all_min_faces[of A nr b]  assms 
  by blast

text \<open>a ==> b\<close>

lemma lin_comb_in_hyp:
  fixes y :: "'a :: trivial_conjugatable_linordered_field vec"
  assumes "P \<subseteq> carrier_vec n" 
  assumes "y \<in> P"
  assumes "z \<in> P"
  assumes "support_hyp P \<alpha> \<beta>" 
  assumes "\<beta> = \<alpha> \<bullet> (l \<cdot>\<^sub>v y + (1 - l) \<cdot>\<^sub>v z)"
  assumes "l > 0 \<and> l < 1" 
  shows "\<alpha> \<bullet> y = \<beta>" 
proof -
  have "\<alpha> \<in> carrier_vec n" 
    using assms(4) unfolding support_hyp_def by auto
  have " \<beta> = \<alpha> \<bullet> (l \<cdot>\<^sub>v y) + \<alpha> \<bullet> ((1 - l) \<cdot>\<^sub>v z)" 
    using scalar_prod_add_distrib[of \<alpha> n "l \<cdot>\<^sub>v y" "(1 - l) \<cdot>\<^sub>v z"] `\<alpha> \<in> carrier_vec n`
      assms(1-3) assms(5) by blast
  then have 1: "l * (\<alpha> \<bullet> y) + (1 - l) * (\<alpha> \<bullet> z) = \<beta>" 
    using \<open>\<alpha> \<in> carrier_vec n\<close> assms(1-3) in_mono by fastforce
  have "\<alpha> \<bullet> y \<le> \<beta>" 
    using assms(2) assms(4) support_hyp_is_valid(1) valid_ineqE by blast
  have "\<alpha> \<bullet> z \<le> \<beta>" 
    using assms(3) assms(4) support_hyp_is_valid(1) valid_ineqE by blast 
  show "\<alpha> \<bullet> y = \<beta>" 
  proof(cases "\<alpha> \<bullet> z = \<beta>")
    case True
    then show ?thesis 
      using  assms(6) 1 
      by (simp add: left_diff_distrib)
  next
    case False
    have "\<alpha> \<bullet> z < \<beta>" 
      by (simp add: False \<open>\<alpha> \<bullet> z \<le> \<beta>\<close> order.strict_iff_order)
    then have "(1 - l) * (\<alpha> \<bullet> z) < (1 - l) * \<beta>" using assms(6) 
      by auto
    have "l * (\<alpha> \<bullet> y) \<le> l * \<beta>" 
      by (simp add: \<open>0 < l \<and> l < 1\<close> \<open>\<alpha> \<bullet> y \<le> \<beta>\<close>)
    then have "l * (\<alpha> \<bullet> y) + (1 - l) * (\<alpha> \<bullet> z) < l * \<beta> + (1 - l) * \<beta>" 
      using \<open>(1 - l) * (\<alpha> \<bullet> z) < (1 - l) * \<beta>\<close> add_mono_thms_linordered_field(4) by blast
    then have "l * (\<alpha> \<bullet> y) + (1 - l) * (\<alpha> \<bullet> z) < \<beta>" by algebra
    then show ?thesis using 1 by blast  
  qed
qed

lemma P_int_then_face_int:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes "P \<subseteq> carrier_vec n" 
  assumes "P = integer_hull P" 
  shows "(\<forall> F. face P F \<longrightarrow> (\<exists> x \<in> F. x \<in> \<int>\<^sub>v))" 
proof
  fix F
  show " face P F \<longrightarrow> (\<exists>x\<in>F. x \<in> \<int>\<^sub>v)"
  proof 
    assume "face P F"
    obtain x where "x \<in> F" 
      using \<open>face P F\<close> face_non_empty by fastforce
    show "\<exists>x\<in>F. x \<in> \<int>\<^sub>v" 
    proof(cases "x \<in> \<int>\<^sub>v")
      case True
      then show ?thesis using `x \<in> F` 
        by blast
    next
      case False
      obtain \<alpha> \<beta>  where \<alpha>_\<beta>:"P \<noteq> {} \<and>  F = P \<inter> {x |x. \<alpha> \<bullet> x = \<beta>} \<and> support_hyp P \<alpha> \<beta> " 
        using \<open>face P F\<close> face_def by auto
      obtain y z l where lin_comb_x:"y \<in> P \<inter> \<int>\<^sub>v" "z \<in> P" "x = l \<cdot>\<^sub>v y + (1 - l) \<cdot>\<^sub>v z" "l > 0 \<and> l < 1"
        using elem_of_P_is_lin_comb[of P x] 
        using assms gram_schmidt.polyhedron_def False \<open>x \<in> F\<close> 
        using \<open>face P F\<close> face_subset_polyhedron by blast 
      have "\<alpha> \<bullet> y = \<beta>" 
        using lin_comb_in_hyp[of P y z \<alpha> \<beta> l] 
          \<alpha>_\<beta> lin_comb_x `P \<subseteq> carrier_vec n` \<open>x \<in> F\<close> by fastforce
      then have "y \<in> F" using `y \<in> P \<inter> \<int>\<^sub>v`  \<alpha>_\<beta> by blast
      then show ?thesis 
        using \<open>y \<in> P \<inter> \<int>\<^sub>v\<close> by blast
    qed
  qed
qed

text\<open>$b \Rightarrow f$\<close>

lemma int_face_then_max_suphyp_int:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes "P \<subseteq> carrier_vec n"
  assumes "(\<forall> F. face P F \<longrightarrow> (\<exists> x \<in> F. x \<in> \<int>\<^sub>v))" 
  shows "\<forall> \<alpha> \<in> carrier_vec n. has_Maximum { \<alpha> \<bullet> x | x. x \<in> P} \<longrightarrow>
   (\<exists>x. x \<in> P \<and> \<alpha> \<bullet> x = Maximum { \<alpha> \<bullet> x | x. x \<in> P}  \<and> x \<in> \<int>\<^sub>v)"
proof(safe)
  fix \<alpha> :: "'a vec"
  assume "\<alpha> \<in> carrier_vec n" "has_Maximum {\<alpha> \<bullet> x |x. x \<in> P}"
  let ?\<beta> = "Maximum { \<alpha> \<bullet> x | x. x \<in> P}" 

  have "?\<beta> \<in>  { \<alpha> \<bullet> x | x. x \<in> P}" 
    apply(rule has_MaximumD \<open>has_Maximum {\<alpha> \<bullet> x |x. x \<in> P}\<close>) 
    by (simp add: \<open>has_Maximum {\<alpha> \<bullet> x |x. x \<in> P}\<close>)
  have "support_hyp P \<alpha> ?\<beta>" unfolding support_hyp_def 
    using \<open>\<alpha> \<in> carrier_vec n\<close> \<open>has_Maximum {\<alpha> \<bullet> x |x. x \<in> P}\<close> by blast
  have "face P (P \<inter> {y |y. \<alpha> \<bullet> y = ?\<beta>})"
    unfolding face_def
    apply(auto)
    using \<open>Maximum {\<alpha> \<bullet> x |x. x \<in> P} \<in> {\<alpha> \<bullet> x |x. x \<in> P}\<close> apply blast
    using \<open>support_hyp P \<alpha> (Maximum {\<alpha> \<bullet> x |x. x \<in> P})\<close> by blast
  then show "\<exists>x. x \<in> P \<and> \<alpha> \<bullet> x = Maximum { \<alpha> \<bullet> x | x. x \<in> P}  \<and> x \<in> \<int>\<^sub>v" using assms(1-2)
    by blast
qed

text \<open>f ==> a\<close>

lemma int_hull_subset:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  shows "integer_hull P \<subseteq> P"
proof -
  have subset_int: "P \<inter> \<int>\<^sub>v \<subseteq> P" by blast
  have convex_P: "convex P"
    unfolding P_def using A b polyhedra_are_convex by blast
  have hull_eq: "convex_hull P = P"
    using convex_P convex_def by blast
  have hull_mono: "convex_hull (P \<inter> \<int>\<^sub>v) \<subseteq> convex_hull P"
    using convex_hull_mono subset_int by blast
  have "convex_hull (P \<inter> \<int>\<^sub>v) \<subseteq> P"
    using hull_mono hull_eq by simp
  then show "integer_hull P \<subseteq> P"
    unfolding integer_hull_def by blast
qed

lemma not_in_int_hull_not_int:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "y \<in> P - integer_hull P"
  shows "y \<notin> \<int>\<^sub>v"
proof
  assume " y \<in> \<int>\<^sub>v"
  then have "y \<in> P \<inter>  \<int>\<^sub>v" using assms(4) by auto
  have "P \<inter> \<int>\<^sub>v \<subseteq> carrier_vec n" using P_def unfolding polyhedron_def 
    by blast
  then have "y \<in> integer_hull P" 
    unfolding integer_hull_def using set_in_convex_hull[of "P \<inter> \<int>\<^sub>v"] 
    using \<open>y \<in> P \<inter> \<int>\<^sub>v\<close> by blast
  then show False using assms(4) 
    by blast
qed

lemma exists_eq_in_P_for_outside_elem:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "y \<notin> P"
  assumes "y \<in> carrier_vec n"
  shows "\<exists>j. j < nr \<and> (row A j) \<bullet> y >  b $ j"
proof(rule ccontr)
  assume "\<not> (\<exists>j<nr. b $ j < row A j \<bullet> y)"
  then have 1: "\<forall>j<dim_row A.  row A j \<bullet> y \<le> b $ j" 
    by (metis A carrier_matD(1) leI)
  have 2: "dim_row A = dim_vec b" 
    using A b carrier_vecD by blast
  have "A *\<^sub>v y \<le> b" using leq_for_all_index_then_eq 1 2 
    by blast
  have "y \<in> P"  
    unfolding P_def polyhedron_def 
    using \<open>A *\<^sub>v y \<le> b\<close> assms(5) by blast
  then show False 
    by (simp add: assms(4))
qed

lemma eq_in_P_has_max:
  fixes A :: "'a  mat"
  fixes b:: "'a vec" 
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "i < nr"
  assumes "P \<noteq> {}" 
  shows "has_Maximum { row A i \<bullet> x | x. x \<in> P}"
proof -
  have "\<forall> x \<in> P. row A i \<bullet> x \<le> b $ i" 
    using P_def unfolding polyhedron_def 
      mult_mat_vec_def 
    apply  (auto simp:  less_eq_vec_def) 
    using assms(4) b by force
  then have "valid_ineq P (row A i) (b $ i)" unfolding valid_ineq_def 
    using A assms(4) row_carrier_vec by blast
  then show ?thesis 
    using A P_def assms(5) b valid_ineq_dual(2) by auto
qed

end
end
