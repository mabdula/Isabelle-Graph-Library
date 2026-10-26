theory Subsystems
  imports  Linear_Inequalities.Decomposition_Theorem 
    Jordan_Normal_Form.DL_Rank_Submatrix

begin 

definition sub_system where
  "sub_system A b I = (submatrix A I UNIV,  vec_of_list (nths (list_of_vec b) I))"

lemma sub_system_fst:
  shows "fst (sub_system A b I) = submatrix A I UNIV" 
  unfolding sub_system_def
  by force

lemma sub_system_snd:
  shows "snd (sub_system A b I) = vec_of_list (nths (list_of_vec b) I)" 
  unfolding sub_system_def
  by force

lemma dim_row_subsyst_mat:
  shows "dim_row (fst (sub_system A b I)) = card {i. i < dim_row A \<and> i \<in> I}" 
proof -
  have "dim_row (fst (sub_system A b I)) = dim_row (submatrix A I UNIV)"
    by (simp add: sub_system_fst)
  also have "\<dots> = card {i. i < dim_row A \<and> i \<in> I}"
    by (rule dim_submatrix(1))
  finally show ?thesis .
qed

lemma dim_col_submatrix_UNIV:
  shows "dim_col (submatrix A I UNIV) = dim_col A"
  using dim_submatrix(2)[of A I UNIV]
  by fastforce

lemma dim_col_subsyst_mat:
  shows "dim_col (fst (sub_system A b I)) = dim_col A" 
proof -
  have "dim_col (fst (sub_system A b I)) = dim_col (submatrix A I UNIV)"
    by (simp add: sub_system_fst)
  also have "\<dots> = dim_col A"
    by (rule dim_col_submatrix_UNIV)
  finally show ?thesis .
qed

lemma dim_row_less_card_I:
  assumes "finite I" 
  shows "dim_row (fst (sub_system A b I)) \<le> card I" 
proof -
  have "{i. i < dim_row A \<and> i \<in> I} \<subseteq> I" by auto
  then have "card {i. i < dim_row A \<and> i \<in> I} \<le> card I" 
    using assms card_mono by blast
  then show ?thesis 
    unfolding dim_row_subsyst_mat[of A b I] .
qed

lemma dim_subsyst_vec:
  shows "dim_vec (snd (sub_system A b I)) = card {i. i < dim_vec b \<and> i \<in> I}"
proof -
  have "dim_vec (snd (sub_system A b I)) = length (nths (list_of_vec b) I)"
    by (simp add: sub_system_snd Matrix.dim_vec_of_list)
  also have "\<dots> = card {i. i < length (list_of_vec b) \<and> i \<in> I}"
    by (rule length_nths)
  also have "\<dots> = card {i. i < dim_vec b \<and> i \<in> I}"
    by (simp only: Matrix.length_list_of_vec)
  finally show ?thesis .
qed

lemma  dim_subsyst_vec_less_b:
  shows "dim_vec (snd (sub_system A b I)) \<le> dim_vec b"
proof -
  have "{i. i < dim_vec b \<and> i \<in> I} \<subseteq> {0..<dim_vec b}" by auto
  then have "card {i. i < dim_vec b \<and> i \<in> I} \<le> card  {0..<dim_vec b}" 
    by (rule card_mono[OF finite_atLeastLessThan])
  then show ?thesis 
  proof -
    have fin: "finite {0..<dim_vec b}"
      by simp
    have sub: "{i. i < dim_vec b \<and> i \<in> I} \<subseteq> {0..<dim_vec b}"
      by auto
    have "dim_vec (snd (sub_system A b I)) = card {i. i < dim_vec b \<and> i \<in> I}"
      by (rule dim_subsyst_vec)
    also have "\<dots> \<le> card {0..<dim_vec b}"
      using fin sub by (rule card_mono)
    also have "\<dots> = dim_vec b"
      by simp
    finally show ?thesis .
  qed
qed

lemma  dim_subsyst_mat_less_A:
  shows "dim_row (fst (sub_system A b I)) \<le> dim_row A"
proof -
  have "{i. i < dim_row A \<and> i \<in> I} \<subseteq> {0..<dim_row A}" by auto
  then have "card {i. i < dim_row A \<and> i \<in> I} \<le> card  {0..<dim_row A}" 
    by (rule card_mono[OF finite_atLeastLessThan])
  then show ?thesis 
    by (simp add: dim_row_subsyst_mat)
qed

lemma dims_subsyst_same:
  assumes "dim_row A = dim_vec b"
  shows "dim_row (fst (sub_system A b I)) = dim_vec (snd (sub_system A b I))" 
proof -
  have "dim_row (fst (sub_system A b I)) = card {i. i < dim_row A \<and> i \<in> I}"
    by (rule dim_row_subsyst_mat)
  also have "\<dots> = card {i. i < dim_vec b \<and> i \<in> I}"
    using assms by simp
  also have "\<dots> = dim_vec (snd (sub_system A b I))"
    by (rule dim_subsyst_vec[symmetric])
  finally show ?thesis .
qed

lemma dims_subsyst_same':
  assumes "dim_row A = dim_vec b"
  assumes "(A', b') = (sub_system A b I)" 
  shows "dim_row A' = dim_vec b'"
proof -
  have eq: "sub_system A b I = (A', b')"
    using assms(2) by (rule sym)
  have "dim_row A' = dim_row (fst (sub_system A b I))"
    by (simp add: eq)
  also have "\<dots> = dim_vec (snd (sub_system A b I))"
    by (rule dims_subsyst_same[OF assms(1)])
  also have "\<dots> = dim_vec b'"
    by (simp add: eq)
  finally show ?thesis .
qed

lemma dims_subsyst_same_carr:
  assumes "A \<in> carrier_mat nr n"
  assumes "b \<in> carrier_vec nr" 
  assumes "(A', b') = (sub_system A b I)" 
  shows "dim_row A' = dim_vec b'"
proof -
  have "dim_row A = nr"
    using assms(1) by (rule carrier_matD(1))
  moreover have "dim_vec b = nr"
    using assms(2) by (rule carrier_vecD)
  ultimately have "dim_row A = dim_vec b"
    by simp
  then show ?thesis
    by (rule dims_subsyst_same'[OF _ assms(3)])
qed

lemma I_subsys_same_card:
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  assumes "I \<subseteq> {0..<nr}"
  shows "dim_row (fst (sub_system A b I)) = card I"
    "dim_vec (snd (sub_system A b I)) = card I" 
proof -
  have "{i. i < nr \<and> i \<in> I} = I" using assms(3) by auto 
  then have " card {i. i < dim_row A \<and> i \<in> I} = card I" using A by auto
  then have eq_card: "card {i. i < dim_row A \<and> i \<in> I} = card I" .
  have "dim_row (fst (sub_system A b I)) = card {i. i < dim_row A \<and> i \<in> I}"
    by (rule dim_row_subsyst_mat)
  also have "\<dots> = card I"
    by (rule eq_card)
  finally show "dim_row (fst (sub_system A b I)) = card I" .
  then show "dim_vec (snd (sub_system A b I)) = card I" using b 
    by (simp add: \<open>{i. i < nr \<and> i \<in> I} = I\<close> dim_subsyst_vec)
qed

lemma carrier_mat_subsyst:
  assumes "dim_row A = dim_vec b"
  shows "(fst (sub_system A b I)) \<in> carrier_mat (dim_row (fst (sub_system A b I))) (dim_col A)" 
  using dim_col_subsyst_mat by blast

lemma subsyst_rows_carr:
  assumes "A \<in> carrier_mat nr n"
  shows "set (rows (submatrix A I UNIV)) \<subseteq> carrier_vec n"
proof -
  have dc: "dim_col (submatrix A I UNIV) = n"
    using dim_col_submatrix_UNIV[of A I] carrier_matD(2)[OF assms] by simp
  show ?thesis
  proof
    fix v
    assume "v \<in> set (rows (submatrix A I UNIV))"
    then obtain i where i: "i < dim_row (submatrix A I UNIV)"
      and v: "v = row (submatrix A I UNIV) i"
      unfolding rows_def by auto
    have "dim_vec v = dim_col (submatrix A I UNIV)"
      unfolding v by simp
    then show "v \<in> carrier_vec n"
      unfolding carrier_vec_def using dc by simp
  qed
qed

lemma nths_list_pick_vec_same:
  shows "vec_of_list (nths (list_of_vec b) I) = 
    vec (card {i. i<dim_vec b \<and> i\<in>I})  (\<lambda> i. b $ (pick I i))"
proof -
  have len_lv: "length (list_of_vec b) = dim_vec b"
    by (simp add: Matrix.length_list_of_vec)
  have len: "length (nths (list_of_vec b) I) = card {i. i < dim_vec b \<and> i \<in> I}"
    using length_nths[of "list_of_vec b" I] len_lv by simp
  have entries: "vec_of_list (nths (list_of_vec b) I) $ i = b $ pick I i"
    if i_lt: "i < card {i. i < dim_vec b \<and> i \<in> I}" for i
  proof -
    have i_len: "i < length (nths (list_of_vec b) I)"
      using i_lt len by simp
    have i_card: "i < card {i. i < length (list_of_vec b) \<and> i \<in> I}"
      using i_lt len_lv by simp
    have pick_lt: "pick I i < dim_vec b"
    proof -
      have "i < card {a. a < dim_vec b \<and> a \<in> I}"
        using i_lt by simp
      then show ?thesis by (rule pick_le)
    qed
    have "vec_of_list (nths (list_of_vec b) I) $ i = nths (list_of_vec b) I ! i"
      by (simp add: vec_of_list_index)
    also have "\<dots> = list_of_vec b ! pick I i"
      by (rule nth_nths[OF i_card])
    also have "\<dots> = b $ pick I i"
      using pick_lt len_lv by (simp add: list_of_vec_index)
    finally show ?thesis .
  qed
  show ?thesis
  proof (rule eq_vecI)
    fix i
    assume "i < dim_vec (vec (card {i. i < dim_vec b \<and> i \<in> I}) (\<lambda>i. b $ pick I i))"
    then have i_lt: "i < card {i. i < dim_vec b \<and> i \<in> I}"
      by simp
    have "vec_of_list (nths (list_of_vec b) I) $ i = b $ pick I i"
      by (rule entries[OF i_lt])
    also have "\<dots> = vec (card {i. i < dim_vec b \<and> i \<in> I}) (\<lambda>i. b $ pick I i) $ i"
      by (rule index_vec[OF i_lt, symmetric])
    finally show "vec_of_list (nths (list_of_vec b) I) $ i =
                  vec (card {i. i < dim_vec b \<and> i \<in> I}) (\<lambda>i. b $ pick I i) $ i" .
  next
    show "dim_vec (vec_of_list (nths (list_of_vec b) I)) =
          dim_vec (vec (card {i. i < dim_vec b \<and> i \<in> I}) (\<lambda>i. b $ pick I i))"
      using len by simp
  qed
qed

lemma subsyst_b_i:
  assumes "i < dim_vec (snd (sub_system A b I))"  
  shows "(snd (sub_system A b I)) $ i = b $ (pick I i)" 
proof -
  have idx: "i < card {j. j < dim_vec b \<and> j \<in> I}"
    using assms by (simp add: dim_subsyst_vec)
  have eq: "snd (sub_system A b I) = vec (card {j. j < dim_vec b \<and> j \<in> I}) (\<lambda>j. b $ pick I j)"
    by (simp only: sub_system_snd nths_list_pick_vec_same)
  have "snd (sub_system A b I) $ i
          = vec (card {j. j < dim_vec b \<and> j \<in> I}) (\<lambda>j. b $ pick I j) $ i"
    by (simp only: eq)
  also have "\<dots> = b $ pick I i"
    using idx by simp
  finally show ?thesis .
qed

lemma nths_UNIV_same:
  "nths xs UNIV = xs"
  unfolding nths_def
  using filter_True by auto

lemma itself_is_subsyst:
  shows "(A, b) = sub_system A b UNIV" 
proof
  have "A = submatrix A UNIV UNIV"
    apply rule
      apply (simp add: dim_submatrix(1) dim_submatrix(2) pick_UNIV submatrix_index)
     apply (fastforce simp: dim_submatrix(1))
    apply (fastforce simp: dim_submatrix(2))
    done
  then show "fst (A, b) = fst (sub_system A b UNIV)"
    unfolding sub_system_fst fst_conv .
  show "snd (A, b) = snd (sub_system A b UNIV)" 
  proof -
  have "snd (sub_system A b UNIV) = vec_of_list (nths (list_of_vec b) UNIV)"
    by (rule sub_system_snd)
  also have "\<dots> = vec_of_list (list_of_vec b)"
    by (simp add: nths_UNIV_same)
  also have "\<dots> = b"
    by (rule vec_list)
  finally show ?thesis
    by simp
  qed
qed  

lemma pick_index_row_in_A:
  assumes "j < dim_row (fst (sub_system A b I))" 
  shows "row (fst (sub_system A b I)) j = row A (pick I j)"
proof -
  have j: "j < card {i. i < dim_row A \<and> i \<in> I}"
    using assms by (simp add: dim_row_subsyst_mat)
  have "row (fst (sub_system A b I)) j = row (submatrix A I UNIV) j"
    by (simp only: sub_system_fst)
  also have "\<dots> = row A (pick I j)"
    by (rule row_submatrix_UNIV[OF j])
  finally show ?thesis .
qed

lemma exist_index_in_A:
  assumes "dim_row A = dim_vec b"
  assumes "j < dim_vec (snd (sub_system A b I))"
  shows "\<exists> i < dim_vec b. i \<in> I \<and> row (fst (sub_system A b I)) j = row A i 
          \<and> (snd (sub_system A b I)) $ j = b $ i \<and> i = pick I j"
proof -
  have "(pick I j) < dim_vec b" 
  proof -
    have "j < card {i. i < dim_vec b \<and> i \<in> I}"
      using assms(2) by (simp add: dim_subsyst_vec)
    then show ?thesis
      by (rule pick_le)
  qed
  moreover have "(pick I j) \<in> I" 
  proof (cases "finite I")
    case True
    have "j < dim_row (fst (sub_system A b I))"
      using assms(2) dims_subsyst_same[OF assms(1)] by simp
    moreover have "dim_row (fst (sub_system A b I)) \<le> card I"
      using dim_row_less_card_I[OF True] by blast
    ultimately have "j < card I" by linarith
    then show ?thesis by (rule pick_in_set_le)
  next
    case False
    then show ?thesis by (rule pick_in_set_inf)
  qed
  moreover have "row (fst (sub_system A b I)) j = row A (pick I j)"
  proof -
    have "j < dim_row (fst (sub_system A b I))"
      using assms(2) dims_subsyst_same[OF assms(1)] by simp
    from pick_index_row_in_A[OF this] show ?thesis .
  qed
  moreover have "snd (sub_system A b I) $ j = b $ (pick I j)"
    by (rule subsyst_b_i[OF assms(2)])
  ultimately show ?thesis by blast
qed

lemma exist_index_in_A_carr:
  assumes "A \<in> carrier_mat nr n"
  assumes "b \<in> carrier_vec nr" 
  assumes "(C, d) = sub_system A b I" 
  assumes "j < dim_row C"
  shows "\<exists> i < nr. i \<in> I \<and> row C j = row A i 
          \<and> d $ j = b $ i \<and> i = pick I j"
proof -
  have Cd: "sub_system A b I = (C, d)"
    by (rule assms(3)[symmetric])
  have C_eq: "fst (sub_system A b I) = C"
    by (simp add: Cd)
  have d_eq: "snd (sub_system A b I) = d"
    by (simp add: Cd)
  have dim_A: "dim_row A = nr"
    by (rule carrier_matD(1)[OF assms(1)])
  have dim_b: "dim_vec b = nr"
    by (rule carrier_vecD[OF assms(2)])
  have dims: "dim_row A = dim_vec b"
    using dim_A dim_b by simp
  have "dim_row C = dim_vec d"
    by (rule dims_subsyst_same_carr[OF assms(1,2,3)])
  then have j_lt: "j < dim_vec (snd (sub_system A b I))"
    using assms(4) d_eq by simp
  obtain i where i_lt: "i < dim_vec b"
    and i_I: "i \<in> I"
    and i_row: "row (fst (sub_system A b I)) j = row A i"
    and i_b: "snd (sub_system A b I) $ j = b $ i"
    and i_pick: "i = pick I j"
    using exist_index_in_A[OF dims j_lt] by blast
  have "i < nr"
    using i_lt dim_b by simp
  moreover have "row C j = row A i"
    using i_row C_eq by simp
  moreover have "d $ j = b $ i"
    using i_b d_eq by simp
  ultimately show ?thesis
    using i_I i_pick by blast
qed

lemma card_of_smaller_is_index_in_subsystem:
  assumes "j < dim_vec b"
  assumes "j \<in> I"
  shows "card {a\<in>I. a < j} < dim_vec (snd (sub_system A b I))"
proof -
  let ?i = "card {a\<in>I. a < j}" 
  have "pick I ?i = j" using pick_card_in_set assms(2) by auto
  have "dim_vec (snd (sub_system A b I)) = card {i. i < dim_vec b \<and> i \<in> I}" 
    by (rule dim_subsyst_vec)
  have "j \<notin> {a\<in>I. a < j} \<and> j \<in> {i. i < dim_vec b \<and> i \<in> I}" using assms(1-2) by auto
  then  have "{a\<in>I. a < j} \<subset> {i. i < dim_vec b \<and> i \<in> I}" 
    by auto
  then have "?i < card {i. i < dim_vec b \<and> i \<in> I}" 
    by (simp add: psubset_card_mono)
  then show "?i <  dim_vec (snd (sub_system A b I))" 
    using \<open>dim_vec (snd (sub_system A b I)) = card {i. i < dim_vec b \<and> i \<in> I}\<close> by presburger
qed

lemma exist_index_in_A':
  assumes "dim_row A = dim_vec b"
  assumes "j < dim_vec b"
  assumes "j \<in> I"
  shows " \<exists> i < dim_vec (snd (sub_system A b I)).
       row (fst (sub_system A b I)) i = row A j \<and> (snd (sub_system A b I)) $ i = b $ j"
proof -
  let ?A' = "(fst (sub_system A b I))" 
  let ?b' = "(snd (sub_system A b I))"
  let ?i = "card {a\<in>I. a < j}" 

  have pick_of_I: "pick I ?i = j" 
    using assms(3) pick_card_in_set by presburger
  have  index: "?i <  dim_vec ?b'"
    using card_of_smaller_is_index_in_subsystem assms(2-3) by blast
  then have "row ?A' ?i = row A j" 
    by (simp add: assms(1) dims_subsyst_same index pick_index_row_in_A pick_of_I)
  moreover have "?b' $ ?i= b $ j" 
    by (simp add: index pick_of_I subsyst_b_i)
  ultimately show ?thesis 
    using index by blast
qed

lemma subsystem_fulfills_P:
  assumes "dim_row A = dim_vec b"
  assumes "(A', b') = sub_system A b I"
  assumes "\<forall> i < dim_row A'. P (row A' i) (b' $ i)"
  shows "\<forall>i \<in> I \<inter> {0..<dim_row A}. P (row A i) (b $ i)" 
proof 
  fix i
  assume "i \<in> I \<inter> {0..<dim_row A}" 
  have "dim_row A' = dim_vec b'" using assms(1) 
    by (simp add: dims_subsyst_same'[OF assms(1,2)])
  then obtain j where "j<dim_row A' \<and> row A' j = row A i \<and> b' $ j = b $ i" 
    using exist_index_in_A'[of A b i I]  assms(1-2) 
  proof -
    have i_in: "i \<in> I"
      using \<open>i \<in> I \<inter> {0..<dim_row A}\<close> by auto
    have i_lt: "i < dim_row A"
      using \<open>i \<in> I \<inter> {0..<dim_row A}\<close> by auto
    have i_b: "i < dim_vec b"
      using i_lt assms(1) by simp
    have A'_eq: "A' = fst (sub_system A b I)"
      using assms(2)[symmetric] by simp
    have b'_eq: "b' = snd (sub_system A b I)"
      using assms(2)[symmetric] by simp
    have dims: "dim_row A' = dim_vec b'"
      by (rule dims_subsyst_same'[OF assms(1) assms(2)])
    obtain k where k1: "k < dim_vec (snd (sub_system A b I))"
      and k2: "row (fst (sub_system A b I)) k = row A i"
      and k3: "snd (sub_system A b I) $ k = b $ i"
      using exist_index_in_A'[OF assms(1) i_b i_in] by blast
    have "k < dim_row A'"
      using k1 dims b'_eq by simp
    moreover have "row A' k = row A i"
      using k2 A'_eq by simp
    moreover have "b' $ k = b $ i"
      using k3 b'_eq by simp
    ultimately have "k < dim_row A' \<and> row A' k = row A i \<and> b' $ k = b $ i"
      by blast
    then show thesis
      by (rule that)
  qed
  then show "P (row A i) (b $ i)" using assms(3) by auto
qed

lemma subsystem_fulfills_P':
  assumes "dim_row A = dim_vec b"
  assumes "(A', b') = sub_system A b I"
  assumes "\<forall>i \<in> I \<inter> {0..<dim_row A}. P (row A i) (b $ i)"
  shows "\<forall> i < dim_row A'. P (row A' i) (b' $ i)"
proof(rule)+
  fix i
  assume "i < dim_row A'"
  have "dim_row A' = dim_vec b'" using assms(1) 
  proof -
    have subsys: "sub_system A b I = (A', b')"
      using assms(2) by (rule sym)
    have "dim_row A' = dim_row (fst (sub_system A b I))"
      by (simp add: subsys)
    also have "\<dots> = dim_vec (snd (sub_system A b I))"
      using assms(1) by (rule dims_subsyst_same)
    also have "\<dots> = dim_vec b'"
      by (simp add: subsys)
    finally show ?thesis .
  qed
  have A'_eq: "fst (sub_system A b I) = A'" and b'_eq: "snd (sub_system A b I) = b'"
    by (simp_all add: assms(2)[symmetric])
  have "i < dim_vec (snd (sub_system A b I))"
    using \<open>i < dim_row A'\<close> dims_subsyst_same'[OF assms(1) assms(2)] b'_eq by simp
  from exist_index_in_A[OF assms(1) this]
  obtain j where j_props: "j < dim_vec b" "j \<in> I"
    "row (fst (sub_system A b I)) i = row A j"
    "snd (sub_system A b I) $ i = b $ j"
    by blast
  have "j \<in> I \<and> j < dim_row A \<and> row A j = row A' i \<and> b $ j = b' $ i"
    using j_props assms(1) A'_eq b'_eq by simp
  then have "P (row A j) (b $ j)" using assms(3) 
    by fastforce
  then show " P (row A' i) (b' $ i)" 
    by (simp add: \<open>j \<in> I \<and> j < dim_row A \<and> row A j = row A' i \<and> b $ j = b' $ i\<close>)
qed

lemma insert_elem_sub_system_fulfills_P:
  assumes "dim_row A = dim_vec b"
  assumes "i < dim_vec b" 
  assumes "(A', b') = sub_system A b I" 
  assumes "(A'', b'') = sub_system A b (I \<union> {i})"
  shows "(\<forall> i < dim_row A''. P (row A'' i) (b'' $ i)) \<longleftrightarrow>
         (\<forall> j < dim_row A'. P (row A' j) (b' $ j)) \<and> P (row A i) (b $ i)" 
    (is "?P_A'' \<longleftrightarrow> ?P_A'")
proof
  show "?P_A'' \<Longrightarrow> ?P_A'" 
  proof -
    assume "?P_A''" 
    then have "\<forall>i \<in> (I \<union> {i}) \<inter> {0..<dim_row A}. P (row A i) (b $ i)" 
      using subsystem_fulfills_P  assms(1) assms(4) by blast
    note P_all = this
    have i_lt: "i < dim_row A"
      using assms(1,2) by simp
    have P_i: "P (row A i) (b $ i)"
      using P_all i_lt by auto
    have "\<forall> j \<in> I \<inter> {0..<dim_row A}. P (row A j) (b $ j)"
      using P_all by auto
    note P_sub = subsystem_fulfills_P'[OF assms(1) assms(3) this]
    show "?P_A'"
      using P_sub P_i by blast
  qed
  show "?P_A' \<Longrightarrow> ?P_A''" 
  proof -
    assume "?P_A'"
    then have "\<forall>i \<in> (I \<union> {i}) \<inter> {0..<dim_row A}. P (row A i) (b $ i)" 
      using subsystem_fulfills_P  assms(1) assms(3) by blast
    then show "?P_A''"
      using subsystem_fulfills_P' 
      using assms(1) assms(4) by blast
  qed
qed

lemma eq_for_all_index_then_eq:
  assumes "dim_row A = dim_vec b"
  assumes "\<forall>i<dim_row A. row A i \<bullet> x = b $ i"
  shows "A *\<^sub>v x = b"
  unfolding mult_mat_vec_def
  by (simp add: assms(1) assms(2) eq_vecI)

lemma leq_for_all_index_then_eq:
  assumes "dim_row A = dim_vec b"
  assumes "\<forall>i<dim_row A. row A i \<bullet> x \<le> b $ i"
  shows "A *\<^sub>v x \<le> b"
  unfolding mult_mat_vec_def 
  by (simp add: assms(1) assms(2) less_eq_vec_def) 

lemma insert_sub_system_eq:
  assumes "dim_row A = dim_vec b"
  assumes "i < dim_vec b" 
  assumes "(A', b') = sub_system A b I" 
  assumes "(A'', b'') = sub_system A b (I \<union> {i})"
  shows "{x. A'' *\<^sub>v x = b''} = {x. A' *\<^sub>v x = b' \<and> row A i \<bullet> x = b $ i}"
proof -
  have "\<forall>x.  A'' *\<^sub>v x = b'' \<longleftrightarrow>  A' *\<^sub>v x = b' \<and> row A i \<bullet> x = b $ i"
  proof
    fix x
    have "(\<forall>i<dim_row A''. row A'' i \<bullet> x = b'' $ i) =
    ((\<forall>j<dim_row A'. row A' j \<bullet> x = b' $ j) \<and> row A i \<bullet> x = b $ i)"   
      using insert_elem_sub_system_fulfills_P[of A b i A' b' I A'' b'' "(\<lambda> r y.   r \<bullet> x = y)"] 
        assms by fast
    then show "A'' *\<^sub>v x = b'' \<longleftrightarrow>  A' *\<^sub>v x = b' \<and> row A i \<bullet> x = b $ i"
    proof -
      have d': "dim_row A' = dim_vec b'"
        by (rule dims_subsyst_same'[OF assms(1) assms(3)])
      have d'': "dim_row A'' = dim_vec b''"
        by (rule dims_subsyst_same'[OF assms(1) assms(4)])
      have pointwise: "(M *\<^sub>v x = c) = (\<forall>j<dim_row M. row M j \<bullet> x = c $ j)"
        if dims: "dim_row M = dim_vec c" for M c
      proof
        assume eq: "M *\<^sub>v x = c"
        show "\<forall>j<dim_row M. row M j \<bullet> x = c $ j"
        proof (intro allI impI)
          fix j
          assume j: "j < dim_row M"
          have "row M j \<bullet> x = (M *\<^sub>v x) $ j"
            using j by (simp add: index_mult_mat_vec)
          also have "\<dots> = c $ j"
            using eq by simp
          finally show "row M j \<bullet> x = c $ j" .
        qed
      next
        assume "\<forall>j<dim_row M. row M j \<bullet> x = c $ j"
        then show "M *\<^sub>v x = c"
          by (rule eq_for_all_index_then_eq[OF dims])
      qed
      have key: "(\<forall>k<dim_row A''. row A'' k \<bullet> x = b'' $ k) =
                 ((\<forall>j<dim_row A'. row A' j \<bullet> x = b' $ j) \<and> row A i \<bullet> x = b $ i)"
        using insert_elem_sub_system_fulfills_P[of A b i A' b' I A'' b'' "\<lambda>r y. r \<bullet> x = y"]
          assms by fast
      show ?thesis
        unfolding pointwise[OF d''] pointwise[OF d']
        by (rule key)
    qed
  qed
  then show ?thesis by presburger
qed

lemma insert_sub_system_leq:
  assumes "dim_row A = dim_vec b"
  assumes "i < dim_vec b" 
  assumes "(A', b') = sub_system A b I" 
  assumes "(A'', b'') = sub_system A b (I \<union> {i})"
  shows "{x. A'' *\<^sub>v x \<le> b''} = {x. A' *\<^sub>v x \<le> b' \<and> row A i \<bullet> x \<le> b $ i}"
proof -
  have "\<forall>x.  A'' *\<^sub>v x \<le> b'' \<longleftrightarrow>  A' *\<^sub>v x \<le> b' \<and> row A i \<bullet> x \<le> b $ i"
  proof
    fix x
    have "(\<forall>i<dim_row A''. row A'' i \<bullet> x \<le> b'' $ i) =
    ((\<forall>j<dim_row A'. row A' j \<bullet> x \<le> b' $ j) \<and> row A i \<bullet> x \<le> b $ i)"   
      using insert_elem_sub_system_fulfills_P[of A b i A' b' I A'' b'' "(\<lambda> r y.   r \<bullet> x \<le> y)"] 
        assms by fast
    then show "A'' *\<^sub>v x \<le> b'' \<longleftrightarrow>  A' *\<^sub>v x \<le> b' \<and> row A i \<bullet> x \<le> b $ i"
    proof -
      have dA': "dim_row A' = dim_vec b'"
        using assms(1) assms(3) by (rule dims_subsyst_same')
      have dA'': "dim_row A'' = dim_vec b''"
        using assms(1) assms(4) by (rule dims_subsyst_same')
      have pointwise: "(M *\<^sub>v x \<le> v) = (\<forall>k<dim_row M. row M k \<bullet> x \<le> v $ k)"
        if dims: "dim_row M = dim_vec v" for M v
      proof (rule iffI)
        assume "M *\<^sub>v x \<le> v"
        then show "\<forall>k<dim_row M. row M k \<bullet> x \<le> v $ k"
          using dims by (auto simp add: less_eq_vec_def index_mult_mat_vec)
      next
        assume "\<forall>k<dim_row M. row M k \<bullet> x \<le> v $ k"
        then show "M *\<^sub>v x \<le> v"
          by (rule leq_for_all_index_then_eq[OF dims])
      qed
      have key: "(\<forall>k<dim_row A''. row A'' k \<bullet> x \<le> b'' $ k) =
                 ((\<forall>j<dim_row A'. row A' j \<bullet> x \<le> b' $ j) \<and> row A i \<bullet> x \<le> b $ i)"
        using insert_elem_sub_system_fulfills_P[of A b i A' b' I A'' b'' "\<lambda>r y. r \<bullet> x \<le> y"]
          assms by blast
      have "(A'' *\<^sub>v x \<le> b'') = (\<forall>k<dim_row A''. row A'' k \<bullet> x \<le> b'' $ k)"
        by (rule pointwise[OF dA''])
      also have "\<dots> = ((\<forall>j<dim_row A'. row A' j \<bullet> x \<le> b' $ j) \<and> row A i \<bullet> x \<le> b $ i)"
        by (rule key)
      also have "\<dots> = (A' *\<^sub>v x \<le> b' \<and> row A i \<bullet> x \<le> b $ i)"
        using pointwise[OF dA'] by blast
      finally show ?thesis .
    qed
  qed
  then show ?thesis by presburger
qed

lemma remove_index_sub_system:
  assumes "dim_row A = dim_vec b" 
  assumes "i \<in> I"
  assumes "i < dim_vec b"
  assumes "(A', b') = sub_system A b I" 
  assumes "(A'', b'') = sub_system A b (I - {i})"
  shows "{x. A' *\<^sub>v x \<le> b'} = {x. A'' *\<^sub>v x \<le> b'' \<and> row A i \<bullet> x \<le> b $ i}"
proof -
  have "i \<notin> (I - {i})" using assms(2) by auto
  moreover have "I = (I - {i}) \<union> {i}" using assms(2) by auto
  ultimately show ?thesis 
    using insert_sub_system_leq[of A b i  A'' b'' "I - {i}" A' b'] assms(1) assms(3-5)
    by argo
qed

lemma remove_index_sub_system_eq:
  assumes "dim_row A = dim_vec b" 
  assumes "i \<in> I"
  assumes "i < dim_vec b"
  assumes "(A', b') = sub_system A b I" 
  assumes "(A'', b'') = sub_system A b (I - {i})"
  shows "{x. A' *\<^sub>v x = b'} = {x. A'' *\<^sub>v x = b'' \<and> row A i \<bullet> x = b $ i}"
proof -
  have "i \<notin> (I - {i})" using assms(2) by auto
  moreover have "I = (I - {i}) \<union> {i}" using assms(2) by auto
  ultimately show ?thesis 
    using insert_sub_system_eq[of A b i  A'' b'' "I - {i}" A' b'] assms(1) assms(3-5)
    by argo
qed

lemma remove_index_remove_row:
  assumes "dim_row A = dim_vec b" 
  assumes "i \<in> I"
  assumes "i < dim_vec b"
  assumes "(A', b') = sub_system A b I" 
  assumes "(C, d) = sub_system A b (I - {i})"
  assumes "row A i \<notin> set (rows C)" 
  shows "set (rows C) = set (rows A') - {row A i}" 
proof(safe) 
  {
    fix r
    assume "r \<in> set (rows C)" 
    then obtain j' where j': "j' < dim_row C \<and> row C j' = r" 
    proof -
      from \<open>r \<in> set (rows C)\<close> obtain k
        where k: "k < length (rows C)" and rk: "rows C ! k = r"
        by (auto simp: in_set_conv_nth)
      have kdim: "k < dim_row C"
        using k by (simp add: length_rows)
      have "row C k = r"
        using rk kdim by (simp add: nth_rows)
      show thesis
        using that kdim \<open>row C k = r\<close> by blast
    qed
    obtain i' where i:"i' < dim_row A \<and> i' \<in> (I - {i}) \<and> row A i' = row C j' \<and> d $ j' = b $ i'" 
  proof -
    have C_eq: "fst (sub_system A b (I - {i})) = C"
      using assms(5)[symmetric] by simp
    have d_eq: "snd (sub_system A b (I - {i})) = d"
      using assms(5)[symmetric] by simp
    have dim_Cd: "dim_row C = dim_vec d"
      by (rule dims_subsyst_same'[OF assms(1) assms(5)])
    have "j' < dim_vec (snd (sub_system A b (I - {i})))"
      using j' dim_Cd d_eq by simp
    from exist_index_in_A[OF assms(1) this] obtain k where
      k1: "k < dim_vec b" and
      k2: "k \<in> I - {i}" and
      k3: "row (fst (sub_system A b (I - {i}))) j' = row A k" and
      k4: "snd (sub_system A b (I - {i})) $ j' = b $ k"
      by blast
    have "k < dim_row A \<and> k \<in> I - {i} \<and> row A k = row C j' \<and> d $ j' = b $ k"
      using k1 k2 k3 k4 assms(1) C_eq d_eq by simp
    then show thesis by (rule that)
  qed
    then obtain j where j: "j < dim_row A' \<and> row A' j = row A i'"
    proof -
      have i'_in_I: "i' \<in> I"
        using i by blast
      have i'_lt: "i' < dim_vec b"
        using i assms(1) by simp
      have A'_eq: "A' = fst (sub_system A b I)"
        by (simp add: assms(4)[symmetric])
      have b'_eq: "b' = snd (sub_system A b I)"
        by (simp add: assms(4)[symmetric])
      have dims: "dim_row A' = dim_vec b'"
        by (rule dims_subsyst_same'[OF assms(1) assms(4)])
      obtain k where k_lt: "k < dim_vec (snd (sub_system A b I))"
        and k_row: "row (fst (sub_system A b I)) k = row A i'"
        using exist_index_in_A'[OF assms(1) i'_lt i'_in_I] by blast
      have "k < dim_row A'"
        using k_lt dims b'_eq by simp
      moreover have "row A' k = row A i'"
        using k_row A'_eq by simp
      ultimately show thesis
        using that by blast
    qed
    then show "r \<in> set (rows A')" 
      proof -
        have "r = row C j'"
          using j' by simp
        also have "\<dots> = row A i'"
          using i by simp
        also have "\<dots> = row A' j"
          using j by simp
        finally have r_eq: "r = row A' j" .
        have jlen: "j < length (rows A')"
          using j by (simp add: length_rows)
        have "rows A' ! j = row A' j"
          using j by (simp add: nth_rows)
        moreover have "rows A' ! j \<in> set (rows A')"
          using jlen by (rule nth_mem)
        ultimately show "r \<in> set (rows A')"
          using r_eq by simp
      qed
  }
  show "\<And>x. row A i \<in> set (rows C) \<Longrightarrow> False" using assms(6) by auto

  fix r
  assume "r \<in> set (rows A')" 
  assume "r \<notin> set (rows C)"
  then obtain j' where j': "j' < dim_row A' \<and> row A' j' = r" using `r \<in> set (rows A')`
    by (auto simp add: in_set_conv_nth length_rows nth_rows)
  obtain i' where i:"i' < dim_row A \<and> i' \<in> I \<and> row A i' = row A' j' \<and> b' $ j' = b $ i'" 
    using exist_index_in_A[of A b j' "I"] 
      dims_subsyst_same' fst_conv j' snd_conv 
  proof -
    note eq = assms(4)[symmetric]
    note dims = dims_subsyst_same'[OF assms(1) assms(4)]
    have j'_lt: "j' < dim_vec (snd (sub_system A b I))"
      using j' dims by (simp add: eq)
    from exist_index_in_A[OF assms(1) j'_lt]
    obtain i0 where i0: "i0 < dim_vec b" "i0 \<in> I"
      "row (fst (sub_system A b I)) j' = row A i0"
      "snd (sub_system A b I) $ j' = b $ i0"
      by blast
    have "i0 < dim_row A"
      using i0(1) assms(1) by simp
    moreover have "row A i0 = row A' j'"
      using i0(3) by (simp add: eq)
    moreover have "b' $ j' = b $ i0"
      using i0(4) by (simp add: eq)
    ultimately have "i0 < dim_row A \<and> i0 \<in> I \<and> row A i0 = row A' j' \<and> b' $ j' = b $ i0"
      using i0(2) by blast
    then show thesis by (rule that)
  qed
  show "r = row A i" 
  proof(cases "i' \<in> (I - {i})")
    case True
    then obtain j where j: "j < dim_row C \<and> row C j = row A i'" 
      using exist_index_in_A'[of A b i' "I - {i}"] 
    proof -
      have C_eq: "fst (sub_system A b (I - {i})) = C"
        by (simp add: assms(5)[symmetric])
      have d_eq: "snd (sub_system A b (I - {i})) = d"
        by (simp add: assms(5)[symmetric])
      have i'_lt: "i' < dim_vec b"
        using i assms(1) by simp
      have "\<exists>k<dim_vec d. row C k = row A i' \<and> d $ k = b $ i'"
        using exist_index_in_A'[OF assms(1) i'_lt True] by (simp add: C_eq d_eq)
      then obtain k where k_lt: "k < dim_vec d" and k_row: "row C k = row A i'"
        by blast
      have "k < dim_row C"
        using k_lt dims_subsyst_same'[OF assms(1) assms(5)] by simp
      then have "k < dim_row C \<and> row C k = row A i'"
        using k_row by simp
      then show thesis
        by (rule that)
    qed
    then show ?thesis 
      proof -
        have jC: "j < dim_row C"
          using j by simp
        have "rows C ! j = row C j"
          using jC by simp
        also have "\<dots> = row A i'"
          using j by simp
        also have "\<dots> = row A' j'"
          using i by simp
        also have "\<dots> = r"
          using j' by simp
        finally have rj: "rows C ! j = r" .
        have "j < length (rows C)"
          using jC by simp
        then have "rows C ! j \<in> set (rows C)"
          by (rule nth_mem)
        then have "r \<in> set (rows C)"
          using rj by simp
        then show ?thesis
          using \<open>r \<notin> set (rows C)\<close> by blast
      qed
  next
    case False
    then have "i' = i" 
      using i by blast
    then show ?thesis 
      using i j' by presburger
  qed
qed

lemma add_index_sub_system_dims:
  assumes "i \<notin> I"
  assumes "i < dim_vec b"
  assumes "(A', b') = sub_system A b I" 
  assumes "(A'', b'') = sub_system A b (I \<union> {i})"
  shows "dim_vec b'' = dim_vec b' + 1"
proof -
  have 1:"dim_vec b' = card {i. i < dim_vec b \<and> i \<in> I}" 
  proof -
    have "snd (sub_system A b I) = b'"
      by (simp add: assms(3)[symmetric])
    then have "dim_vec b' = dim_vec (snd (sub_system A b I))"
      by simp
    also have "\<dots> = card {i. i < dim_vec b \<and> i \<in> I}"
      by (rule dim_subsyst_vec)
    finally show ?thesis .
  qed
  have "{i. i < dim_vec b \<and> i \<in> I} = {i. i < dim_vec b} \<inter> I" by auto
  have 2:"dim_vec b'' = card {j. j < dim_vec b \<and> j \<in> (I \<union> {i})}" 
    proof -
      have "snd (A'', b'') = snd (sub_system A b (I \<union> {i}))"
        using assms(4) by simp
      then have b''_eq: "b'' = snd (sub_system A b (I \<union> {i}))"
        by simp
      show ?thesis
        unfolding b''_eq by (rule dim_subsyst_vec)
    qed
  then have "{j. j < dim_vec b \<and> j \<in> (I \<union> {i})} = 
      ({i. i < dim_vec b} \<inter> I) \<union> {i}" using assms(2) by auto
  then have "card {i. i < dim_vec b \<and> i \<in> I} + 1 = card {j. j < dim_vec b \<and> j \<in> (I \<union> {i})}"
    by (simp add: \<open>{i. i < dim_vec b \<and> i \<in> I} = {i. i < dim_vec b} \<inter> I\<close> assms(1))
  then show ?thesis 
    using 1 2 by presburger
qed

lemma remove_index_sub_system_dims:
  assumes "i \<in> I"
  assumes "i < dim_vec b"
  assumes "(A', b') = sub_system A b I" 
  assumes "(A'', b'') = sub_system A b (I - {i})"
  shows "dim_vec b' = dim_vec b'' + 1"
proof -
  have "i \<notin> (I - {i})" using assms(2) by auto
  moreover have "I = (I - {i}) \<union> {i}" using assms(1) by auto
  ultimately show ?thesis 
    using add_index_sub_system_dims[of i "I - {i}" b A'' b'' A A' b'] assms(1-4)
    by argo
qed

lemma linear_comb_holds_eq:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes "A \<in> carrier_mat nr n" 
  assumes "x \<in> carrier_vec n"
  assumes "y \<in> carrier_vec n"
  assumes "z \<in> carrier_vec n"
  assumes "A *\<^sub>v x = b"
  assumes "A *\<^sub>v y = b"
  assumes "z = l \<cdot>\<^sub>v x + (1 - l) \<cdot>\<^sub>v y"
  assumes "0 \<le> l \<and> l \<le> 1" 
  shows "A *\<^sub>v z = b" 
proof -
  have "A *\<^sub>v z = A *\<^sub>v (l \<cdot>\<^sub>v x) + A *\<^sub>v ((1 - l) \<cdot>\<^sub>v y)" 
    using mult_add_distrib_mat_vec[of A nr n "l \<cdot>\<^sub>v x" "(1 - l) \<cdot>\<^sub>v y"] 
    using assms(1) assms(2) assms(3) assms(7) smult_carrier_vec by blast
  also have "\<dots> = l \<cdot>\<^sub>v (A *\<^sub>v x) + (1 - l) \<cdot>\<^sub>v (A *\<^sub>v y)"
    using mult_mat_vec[of A] 
    using assms(1) assms(2) assms(3) by presburger
  also have "\<dots> = l \<cdot>\<^sub>v b + (1 - l) \<cdot>\<^sub>v b" 
    using assms(5) assms(6) by presburger
  finally show "A *\<^sub>v z = b" 
  proof (rule trans)
    show "l \<cdot>\<^sub>v b + (1 - l) \<cdot>\<^sub>v b = b"
    proof (rule eq_vecI)
      fix i
      assume i: "i < dim_vec b"
      then have "(l \<cdot>\<^sub>v b + (1 - l) \<cdot>\<^sub>v b) $ i = l * (b $ i) + (1 - l) * (b $ i)"
        by simp
      also have "\<dots> = (l + (1 - l)) * (b $ i)"
        by (simp add: ring_distribs)
      also have "\<dots> = b $ i"
        by (simp add: algebra_simps)
      finally show "(l \<cdot>\<^sub>v b + (1 - l) \<cdot>\<^sub>v b) $ i = b $ i" .
    next
      show "dim_vec (l \<cdot>\<^sub>v b + (1 - l) \<cdot>\<^sub>v b) = dim_vec b"
        by simp
    qed
  qed
qed

lemma multiply_by_zero_eq:
  fixes a :: "'a :: trivial_conjugatable_linordered_field vec"
  assumes "dim_vec a = dim_vec b"
  shows "0 \<cdot>\<^sub>v a = 0 \<cdot>\<^sub>v b" 
  apply rule
   apply (simp add: assms)
  by (simp add: assms)

lemma linear_comb_holds_less_eq:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes "A \<in> carrier_mat nr n" 
  assumes "x \<in> carrier_vec n"
  assumes "y \<in> carrier_vec n"
  assumes "z \<in> carrier_vec n"
  assumes "A *\<^sub>v x \<le> b"
  assumes "A *\<^sub>v y \<le> b"
  assumes "z = l \<cdot>\<^sub>v x + (1 - l) \<cdot>\<^sub>v y"
  assumes "0 \<le> l \<and> l \<le> 1" 
  shows "A *\<^sub>v z \<le> b" 
proof -
  have "l \<cdot>\<^sub>v (A *\<^sub>v x) \<le> l \<cdot>\<^sub>v b" 
  proof (unfold less_eq_vec_def, intro conjI allI impI)
    show "dim_vec (l \<cdot>\<^sub>v (A *\<^sub>v x)) = dim_vec (l \<cdot>\<^sub>v b)"
      using assms(5) unfolding less_eq_vec_def by simp
  next
    fix i
    assume i: "i < dim_vec (l \<cdot>\<^sub>v b)"
    hence ib: "i < dim_vec b" by simp
    have ix: "i < dim_vec (A *\<^sub>v x)"
      using assms(5) ib unfolding less_eq_vec_def by simp
    have "(l \<cdot>\<^sub>v (A *\<^sub>v x)) $ i = l * ((A *\<^sub>v x) $ i)"
      using ix by simp
    also have "\<dots> \<le> l * (b $ i)"
    proof (rule mult_left_mono)
      show "(A *\<^sub>v x) $ i \<le> b $ i"
        using assms(5) ib unfolding less_eq_vec_def by blast
      show "0 \<le> l"
        using assms(8) by simp
    qed
    also have "\<dots> = (l \<cdot>\<^sub>v b) $ i"
      using ib by simp
    finally show "(l \<cdot>\<^sub>v (A *\<^sub>v x)) $ i \<le> (l \<cdot>\<^sub>v b) $ i" .
  qed
  have "(1 - l) \<cdot>\<^sub>v (A *\<^sub>v y) \<le> (1 - l) \<cdot>\<^sub>v b" 
    apply (cases "l = 0")
    using assms(6) apply force
    by (smt (verit, best) Orderings.order_eq_iff assms(6) assms(8) diff_gt_0_iff_gt
        diff_numeral_special(9) index_smult_vec(1) index_smult_vec(2) less_eq_vec_def
        mult_le_cancel_left_pos multiply_by_zero_eq order_le_imp_less_or_eq)
  have "A *\<^sub>v z \<le> A *\<^sub>v (l \<cdot>\<^sub>v x) + A *\<^sub>v ((1 - l) \<cdot>\<^sub>v y)" 
    using mult_add_distrib_mat_vec[of A nr n "l \<cdot>\<^sub>v x" "(1 - l) \<cdot>\<^sub>v y"] 
    using assms(1) assms(2) assms(3) assms(7) smult_carrier_vec 
    by (metis dual_order.refl)
  also have "\<dots> = l \<cdot>\<^sub>v (A *\<^sub>v x) + (1 - l) \<cdot>\<^sub>v (A *\<^sub>v y)"
    using mult_mat_vec[of A] 
    using assms(1) assms(2) assms(3) by presburger
  also have "\<dots> \<le> l \<cdot>\<^sub>v b + (1 - l) \<cdot>\<^sub>v b" 
    using `l \<cdot>\<^sub>v (A *\<^sub>v x) \<le> l \<cdot>\<^sub>v b` `(1 - l) \<cdot>\<^sub>v (A *\<^sub>v y) \<le> (1 - l) \<cdot>\<^sub>v b`
    by (metis index_smult_vec(2) vec_add_mono)
  finally show "A *\<^sub>v z \<le> b" 
    by (metis add_smult_distrib_vec assms(8) le_add_diff_inverse one_smult_vec)
qed

end