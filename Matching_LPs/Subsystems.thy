theory Subsystems
  imports  Linear_Inequalities.Decomposition_Theorem 
    Jordan_Normal_Form.DL_Rank_Submatrix

begin 

definition sub_system where
  "sub_system A b I \<equiv> (submatrix A I UNIV,  vec_of_list (nths (list_of_vec b) I))"

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
  using dim_submatrix(1)[of A I UNIV] sub_system_fst by metis

lemma dim_col_submatrix_UNIV:
  shows "dim_col (submatrix A I UNIV) = dim_col A"
  using dim_submatrix(2)[of A I UNIV]
  by fastforce

lemma dim_col_subsyst_mat:
  shows "dim_col (fst (sub_system A b I)) = dim_col A" 
  using dim_col_submatrix_UNIV 
  by (metis sub_system_fst)

lemma dim_row_less_card_I:
  assumes "finite I" 
  shows "dim_row (fst (sub_system A b I)) \<le> card I" 
proof -
  have "{i. i < dim_row A \<and> i \<in> I} \<subseteq> I" by auto
  then have "card {i. i < dim_row A \<and> i \<in> I} \<le> card I" 
    using assms card_mono by blast
  then show ?thesis 
    using dim_row_subsyst_mat by metis
qed

lemma dim_subsyst_vec:
  shows "dim_vec (snd (sub_system A b I)) = card {i. i < dim_vec b \<and> i \<in> I}"
proof -
  have "length (list_of_vec b) = dim_vec b" 
    using Matrix.length_list_of_vec  carrier_vecD by blast
  then show ?thesis
    using sub_system_snd length_nths 
    by (metis Matrix.length_list_of_vec list_of_vec_vec_of_list)
qed

lemma  dim_subsyst_vec_less_b:
  shows "dim_vec (snd (sub_system A b I)) \<le> dim_vec b"
proof -
  have "{i. i < dim_vec b \<and> i \<in> I} \<subseteq> {0..<dim_vec b}" by auto
  then have "card {i. i < dim_vec b \<and> i \<in> I} \<le> card  {0..<dim_vec b}" 
    by (metis card_mono finite_atLeastLessThan)
  then show ?thesis 
    by (metis card_atLeastLessThan diff_zero dim_subsyst_vec)
qed

lemma  dim_subsyst_mat_less_A:
  shows "dim_row (fst (sub_system A b I)) \<le> dim_row A"
proof -
  have "{i. i < dim_row A \<and> i \<in> I} \<subseteq> {0..<dim_row A}" by auto
  then have "card {i. i < dim_row A \<and> i \<in> I} \<le> card  {0..<dim_row A}" 
    by (metis card_mono finite_atLeastLessThan)
  then show ?thesis 
    by (metis card_atLeastLessThan diff_zero dim_row_subsyst_mat)
qed

lemma dims_subsyst_same:
  assumes "dim_row A = dim_vec b"
  shows "dim_row (fst (sub_system A b I)) = dim_vec (snd (sub_system A b I))" 
  by (metis  assms dim_row_subsyst_mat dim_subsyst_vec) 

lemma dims_subsyst_same':
  assumes "dim_row A = dim_vec b"
  assumes "(A', b') = (sub_system A b I)" 
  shows "dim_row A' = dim_vec b'"
  using dims_subsyst_same assms 
  by (metis fst_conv snd_conv)

lemma dims_subsyst_same_carr:
  assumes "A \<in> carrier_mat nr n"
  assumes "b \<in> carrier_vec nr" 
  assumes "(A', b') = (sub_system A b I)" 
  shows "dim_row A' = dim_vec b'"
  by (metis assms carrier_matD(1) carrier_vecD dims_subsyst_same')

lemma I_subsys_same_card:
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  assumes "I \<subseteq> {0..<nr}"
  shows "dim_row (fst (sub_system A b I)) = card I"
    "dim_vec (snd (sub_system A b I)) = card I" 
proof -
  have "{i. i < nr \<and> i \<in> I} = I" using assms(3) by auto 
  then have " card {i. i < dim_row A \<and> i \<in> I} = card I" using A by auto
  then show "dim_row (fst (sub_system A b I)) = card I" using dim_row_subsyst_mat by metis 
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
  by (metis assms dim_col_submatrix_UNIV carrier_matD(2) rows_carrier)

lemma nths_list_pick_vec_same:
  shows "vec_of_list (nths (list_of_vec b) I) = 
    vec (card {i. i<dim_vec b \<and> i\<in>I})  (\<lambda> i. b $ (pick I i))"
  by (smt (verit, best) Collect_cong Matrix.dim_vec_of_list Matrix.length_list_of_vec
      dim_vec eq_vecI index_vec length_nths list_of_vec_index nth_nths vec_of_list_index)

lemma subsyst_b_i:
  assumes "i < dim_vec (snd (sub_system A b I))"  
  shows "(snd (sub_system A b I)) $ i = b $ (pick I i)" 
  using nths_list_pick_vec_same sub_system_snd 
  by (metis (no_types, lifting) assms dim_subsyst_vec index_vec)

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
    by (metis fst_eqD sub_system_fst)
  show "snd (A, b) = snd (sub_system A b UNIV)" 
    by (metis snd_eqD nths_UNIV_same vec_list sub_system_snd)
qed  

lemma pick_index_row_in_A:
  assumes "j < dim_row (fst (sub_system A b I))" 
  shows "row (fst (sub_system A b I)) j = row A (pick I j)"
  using row_submatrix_UNIV[of j A I]
  by (metis assms dim_row_subsyst_mat sub_system_fst)

lemma exist_index_in_A:
  assumes "dim_row A = dim_vec b"
  assumes "j < dim_vec (snd (sub_system A b I))"
  shows "\<exists> i < dim_vec b. i \<in> I \<and> row (fst (sub_system A b I)) j = row A i 
          \<and> (snd (sub_system A b I)) $ j = b $ i \<and> i = pick I j"
proof -
  have "(pick I j) < dim_vec b" 
    by (metis assms(2)  dim_subsyst_vec pick_le)
  moreover have "(pick I j) \<in> I" 
    apply(cases "finite I") 
     apply (metis (mono_tags, lifting) assms dim_row_less_card_I dims_subsyst_same 
        order_less_le_trans pick_in_set_le)
    using pick_in_set_inf by auto
  ultimately show ?thesis
    using  assms dims_subsyst_same pick_index_row_in_A subsyst_b_i 
    by metis
qed

lemma exist_index_in_A_carr:
  assumes "A \<in> carrier_mat nr n"
  assumes "b \<in> carrier_vec nr" 
  assumes "(C, d) = sub_system A b I" 
  assumes "j < dim_row C"
  shows "\<exists> i < nr. i \<in> I \<and> row C j = row A i 
          \<and> d $ j = b $ i \<and> i = pick I j"
  by (metis assms carrier_matD(1) carrier_vecD dims_subsyst_same_carr 
      exist_index_in_A fst_conv snd_conv)

lemma card_of_smaller_is_index_in_subsystem:
  assumes "j < dim_vec b"
  assumes "j \<in> I"
  shows "card {a\<in>I. a < j} < dim_vec (snd (sub_system A b I))"
proof -
  let ?i = "card {a\<in>I. a < j}" 
  have "pick I ?i = j" using pick_card_in_set assms(2) by auto
  have "dim_vec (snd (sub_system A b I)) = card {i. i < dim_vec b \<and> i \<in> I}" 
    by (metis dim_subsyst_vec)
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
    by (metis assms(2) dims_subsyst_same prod.sel(1) prod.sel(2))
  then obtain j where "j<dim_row A' \<and> row A' j = row A i \<and> b' $ j = b $ i" 
    using exist_index_in_A'[of A b i I]  assms(1-2) 
    by (metis IntD1 IntD2 \<open>i \<in> I \<inter> {0..<dim_row A}\<close> atLeastLessThan_iff fst_conv snd_conv)
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
    by (metis assms(2) dims_subsyst_same prod.sel(1) prod.sel(2))
  then obtain j where "j \<in> I \<and> j <dim_row A \<and> (row A j) = (row A' i) \<and> b $ j = b' $ i"
    using exist_index_in_A[of A b i] assms(1-2) `i < dim_row A'`
    by (metis fst_conv snd_conv) 
  then have "P (row A j) (b $ j)" using assms(3) 
    by (metis Int_iff atLeastLessThan_iff zero_le)
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
    then show "?P_A'"
      using subsystem_fulfills_P'[of A b A' b' I P] 
      by (metis Int_iff assms(1-3) atLeastLessThan_iff insert_iff insert_union le_less_linear
          less_nat_zero_code)
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
      using eq_for_all_index_then_eq 
      by (metis dims_subsyst_same' assms(1) assms(3-4) index_mult_mat_vec)
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
      using leq_for_all_index_then_eq 
      by (metis assms(1) assms(3-4) dims_subsyst_same' index_mult_mat_vec less_eq_vec_def)
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
      by (metis in_set_conv_nth length_rows nth_rows)
    obtain i' where i:"i' < dim_row A \<and> i' \<in> (I - {i}) \<and> row A i' = row C j' \<and> d $ j' = b $ i'" 
      using exist_index_in_A[of A b j' "I - {i}"] 
        dims_subsyst_same' fst_conv j' snd_conv 
      by (metis assms(1) assms(5))
    then obtain j where j: "j < dim_row A' \<and> row A' j = row A i'" 
      using exist_index_in_A'[of A b i' I] 
      by (metis Diff_iff assms(1) assms(4) dims_subsyst_same fst_conv)
    then show "r \<in> set (rows A')" 
      by (metis i in_set_conv_nth j' length_rows nth_rows)
  }
  show "\<And>x. row A i \<in> set (rows C) \<Longrightarrow> False" using assms(6) by auto

  fix r
  assume "r \<in> set (rows A')" 
  assume "r \<notin> set (rows C)"
  then obtain j' where j': "j' < dim_row A' \<and> row A' j' = r" using `r \<in> set (rows A')`
    by (metis in_set_conv_nth length_rows nth_rows)
  obtain i' where i:"i' < dim_row A \<and> i' \<in> I \<and> row A i' = row A' j' \<and> b' $ j' = b $ i'" 
    using exist_index_in_A[of A b j' "I"] 
      dims_subsyst_same' fst_conv j' snd_conv 
    by (metis assms(1) assms(4))
  show "r = row A i" 
  proof(cases "i' \<in> (I - {i})")
    case True
    then obtain j where j: "j < dim_row C \<and> row C j = row A i'" 
      using exist_index_in_A'[of A b i' "I - {i}"] 
      by (metis assms(1) assms(5) dims_subsyst_same fst_conv i) 
    then show ?thesis 
      by (metis \<open>r \<notin> set (rows C)\<close> i in_set_conv_nth j' length_rows nth_rows)
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
    using dim_subsyst_vec using assms(3) 
    by (metis snd_conv)
  have "{i. i < dim_vec b \<and> i \<in> I} = {i. i < dim_vec b} \<inter> I" by auto
  have 2:"dim_vec b'' = card {j. j < dim_vec b \<and> j \<in> (I \<union> {i})}" 
    using dim_subsyst_vec using assms(4) 
    by (metis snd_conv)
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
    by (metis add_smult_distrib_vec assms(8) le_add_diff_inverse one_smult_vec)
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
    apply (cases "l = 0")
     apply (metis multiply_by_zero_eq Orderings.order_eq_iff assms(5) less_eq_vec_def)
    by (smt (verit, del_insts) assms(5) assms(8) index_smult_vec(1) index_smult_vec(2) 
        less_eq_vec_def mult_le_cancel_left_pos order_le_imp_less_or_eq)
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