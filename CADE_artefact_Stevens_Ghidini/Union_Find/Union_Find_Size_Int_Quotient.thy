(* Source: Stevens & Ghidini (2025),
   https://doi.org/10.5281/zenodo.15557955
   License: CC-BY 4.0 (https://creativecommons.org/licenses/by/4.0/)
   No modifications made. *)

theory Union_Find_Size_Int_Quotient
  imports Union_Find_Size_Int
begin

lemma ufsi_of_ufs_eq_if_eq_ufs:
  includes ufa.lifting and ufs.lifting and ufsi.lifting
  assumes "eq_ufs ufs1 ufs2"
  shows "ufsi_of_ufs ufs1 = ufsi_of_ufs ufs2"
  using assms unfolding eq_ufs_def ufs_\<alpha>_def ufs_rep_of_def ufs_size_def
  apply (transfer, unfold ufs_invar_def, transfer)
  by (auto simp add: ufsi_of_uf_def rep_of.psimps rep_of.domintros
      intro!: map_index_cong split: prod.splits)

lemma eq_ufs_if_ufsi_of_ufs_eq:
  includes ufa.lifting and ufs.lifting and ufsi.lifting
  assumes "ufsi_of_ufs ufs1 = ufsi_of_ufs ufs2"
  shows "eq_ufs ufs1 ufs2"
  using assms unfolding eq_ufs_def ufs_\<alpha>_def ufs_rep_of_def ufs_size_def
  apply (transfer, unfold ufs_invar_def case_prod_unfold)
  by (metis Rep_ufa_inject gr_zeroI uf_of_ufsi_ufsi_of_uf_Rep_ufa ufa_size_neq_0)

definition "ufs_ufsi_rel ufs ufsi \<equiv> ufsi = ufsi_of_ufs ufs"

lemma right_unique_ufs_ufsi_rel[transfer_rule]:
  "right_unique ufs_ufsi_rel"
  unfolding right_unique_def ufs_ufsi_rel_def by blast

lemma bi_total_ufs_ufsi_rel[transfer_rule]:
  "bi_total ufs_ufsi_rel"
  unfolding bi_total_def right_total_def ufs_ufsi_rel_def
  by (metis ufsi_of_ufs_ufs_of_ufsi)

lemma Quotient_ufsi_ufs:
  "Quotient eq_ufs ufsi_of_ufs ufs_of_ufsi ufs_ufsi_rel"
  using ufsi_of_ufs_ufs_of_ufsi ufsi_of_ufs_eq_if_eq_ufs eq_ufs_if_ufsi_of_ufs_eq
  unfolding ufs_ufsi_rel_def
  by (intro QuotientI) blast+

setup_lifting Quotient_ufsi_ufs reflp_eq_ufs

lift_definition ufsi_\<alpha> :: "ufsi \<Rightarrow> nat rel" is ufs_\<alpha>
  unfolding eq_ufs_def ufs_rep_of_def ufs_\<alpha>_def ufs_size_def
  including ufs.lifting
  by transfer auto

lift_definition ufsi_parent_of :: "ufsi \<Rightarrow> nat \<Rightarrow> nat" is ufs_parent_of
  unfolding eq_ufs_def ufs_parent_of_def ufs_rep_of_def ufs_\<alpha>_def ufs_size_def
  including ufs.lifting
  by transfer auto

lift_definition ufsi_rep_of :: "ufsi \<Rightarrow> nat \<Rightarrow> nat" is ufs_rep_of
  unfolding eq_ufs_def ufs_rep_of_def ufs_\<alpha>_def ufs_size_def
  including ufs.lifting
  by transfer auto

lift_definition ufsi_size :: "ufsi \<Rightarrow> nat \<Rightarrow> nat" is ufs_size
  unfolding eq_ufs_def ufs_parent_of_def ufs_rep_of_def ufs_\<alpha>_def ufs_size_def
  including ufs.lifting
  by transfer auto

lemma ufsi_rep_of_induct[case_names "parametric" rep not_rep, consumes 1]:
  includes lifting_syntax
  assumes "i \<in> Field (ufsi_\<alpha> uf)"
  assumes
    "(ufa_ufs_rel ===> (=) ===> (=))
      (\<lambda>ufa. P (ufsi_of_ufs (ufs_of_ufa ufa))) (\<lambda>ufs. P (ufsi_of_ufs ufs))"
  assumes rep: "\<And>i. \<lbrakk> i \<in> Field (ufsi_\<alpha> uf); ufsi_parent_of uf i = i \<rbrakk> \<Longrightarrow> P uf i"
  assumes not_rep:
    "\<And>i. \<lbrakk> i \<in> Field (ufsi_\<alpha> uf); ufsi_parent_of uf i \<noteq> i; P uf (ufsi_parent_of uf i) \<rbrakk>
    \<Longrightarrow> P uf i"
  shows "P uf i"
proof -
  from assms(2) have [transfer_rule]:
    "(pcr_ufsi ===> (=) ===> (=)) (\<lambda>ufs. P (ufsi_of_ufs ufs)) P"
    using ufs_ufsi_rel_def ufsi.pcr_cr_eq by fastforce
  from assms(1,3-) show ?thesis
    by (transfer fixing: P) (rule ufs_rep_of_induct[OF _ assms(2)])
qed  

lift_definition ufsi_init :: "nat \<Rightarrow> ufsi" is ufs_init .

lemma eq_ufs_ufs_union_if_eq_ufs:
  assumes "eq_ufs ufs1 ufs2"
  shows "eq_ufs (ufs_union ufs1 x y) (ufs_union ufs2 x y)"
  using assms
  unfolding eq_ufs_def ufs_rep_of_def ufs_parent_of_def ufs_\<alpha>_def ufs_size_def
  including ufs.lifting
  by transfer (simp add: case_prod_unfold ufa_rep_of_ufa_union Let_def split: if_splits)

lift_definition ufsi_union :: "ufsi \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ufsi" is ufs_union
  by (fact eq_ufs_ufs_union_if_eq_ufs)

lift_definition ufsi_union_size :: "ufsi \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ufsi" is ufs_union_size
proof -
  fix ufs1 ufs2 x y
  assume "eq_ufs ufs1 ufs2"
  show "?thesis ufs1 ufs2 x y"
  proof(cases "x \<in> Field (ufs_\<alpha> ufs1) \<and> y \<in> Field (ufs_\<alpha> ufs2)")
    case False
    with ufs_\<alpha>_eq_if_eq_ufs[OF \<open>eq_ufs ufs1 ufs2\<close>] have
      "ufs_union ufs1 x y = ufs1" "ufs_union ufs1 y x = ufs1"
      "ufs_union ufs2 x y = ufs2" "ufs_union ufs2 y x = ufs2"
      including ufs.lifting unfolding ufs_\<alpha>_def by (transfer; auto)+  
    with \<open>eq_ufs ufs1 ufs2\<close> show ?thesis
      unfolding ufs_union_size_def by simp
  next
    case True
    with \<open>eq_ufs ufs1 ufs2\<close> show ?thesis
      unfolding ufs_union_size_def
      by (auto simp: eq_ufs_ufs_union_if_eq_ufs ufs_size_eq_if_eq_ufs)
  qed
qed
 
lift_definition ufsi_compress :: "ufsi \<Rightarrow> nat \<Rightarrow> ufsi" is ufs_compress
  unfolding eq_ufs_def ufs_rep_of_def ufs_\<alpha>_def ufs_size_def
  including ufs.lifting
  by transfer (simp add: case_prod_unfold)

lemma ufs_of_ufsi_Abs_ufsi_transfer[transfer_rule]:
  includes lifting_syntax
  shows "((=) ===> pcr_ufsi) (\<lambda>ufsi. ufs_of_ufsi (Abs_ufsi ufsi)) Abs_ufsi"
  unfolding ufsi.pcr_cr_eq ufs_ufsi_rel_def using ufsi_of_ufs_ufs_of_ufsi
  by (intro rel_funI) simp

lemma ufa_of_ufs_ufs_of_ufsi_transfer[transfer_rule]:
  includes lifting_syntax
  shows "(pcr_ufsi ===> ufa_ufs_rel) ufa_of_ufs ufs_of_ufsi"
  unfolding ufsi.pcr_cr_eq ufs_ufsi_rel_def ufa_ufs_rel_def
  by (metis (mono_tags, lifting) Quotient_rep_abs_fold_unmap Quotient_ufsi_ufs eq_ufs_def rel_funI)

lemma ufs_of_ufa_ufsi_of_ufs_transfer[transfer_rule]:
  includes lifting_syntax
  shows "(ufa_ufs_rel ===> pcr_ufsi) ufs_of_ufa ufsi_of_ufs"
  unfolding ufa_ufs_rel_def ufs_ufsi_rel_def ufsi.pcr_cr_eq
  by (intro rel_funI, transfer)
    (auto simp: eq_ufs_ufs_of_ufa_ufa_of_ufs)

lemma ufa_of_ufsi_eq_ufa_of_ufs_ufs_of_ufsi:
  "ufa_of_ufsi ufsi = ufa_of_ufs (ufs_of_ufsi ufsi)"
  by (simp add: Rep_ufsi_inverse ufa_of_ufs.rep_eq ufs_of_ufsi.rep_eq)

lemma ufa_of_ufsi_transfer[transfer_rule]:
  includes lifting_syntax and ufa_ufs_transfer
  notes [transfer_rule] = ufa_of_ufs_transfer
  shows "(pcr_ufsi ===> (=)) ufa_of_ufs ufa_of_ufsi"
  unfolding ufa_of_ufsi_eq_ufa_of_ufs_ufs_of_ufsi ufsi.pcr_cr_eq ufs_ufsi_rel_def
  by (intro rel_funI, transfer)
    (metis eq_ufs_def fst_conv ufa_of_ufs.rep_eq ufs_of_ufa.rep_eq)

lemma ufsi_of_ufs_ufs_of_ufa_ufa_of_ufs[simp]:
  includes ufa_ufs_transfer
  notes ufa_of_ufs_transfer[transfer_rule]
  shows "ufsi_of_ufs (ufs_of_ufa (ufa_of_ufs ufs)) = ufsi_of_ufs ufs"
  by transfer simp

lemma ufa_of_ufs_ufs_of_ufsi_Abs_ufsi_eq:
  assumes "ufsi_invar ufsi"
  shows "ufa_of_ufs (ufs_of_ufsi (Abs_ufsi ufsi)) = Abs_ufa (uf_of_ufsi ufsi)"
  using assms
  by (simp add: Rep_ufsi_inverse eq_onp_same_args
      ufa_of_ufs.rep_eq ufa_of_ufsi.abs_eq ufs_of_ufsi.rep_eq)

lemma map_index_congL':
  assumes "\<forall>i < length xs. f i (xs ! i) = ys ! i"
  assumes "length xs = length ys"
  shows "map_index f xs = ys"
  using assms
  by (metis length_map_index' nth_equalityI nth_map_index)

lemma uf_of_ufsi_replicate_neg_1_eq[simp]:
  "uf_of_ufsi (replicate n (-1)) = [0..<n]"
  unfolding uf_of_ufsi_def 
  by (intro map_index_congL') auto

lemma size_of_ufsi_replicate_neg_1_eq:
  assumes "i < n"
  shows "size_of_ufsi (replicate n (-1)) i = (if i < n then 1 else undefined)"
  using assms size_of_ufsi_def by force

lemma ufsi_invar_replicate_neg_1:
  "ufsi_invar (replicate n (-1))"
proof -
  have "ufa_invar (uf_of_ufsi (replicate n (-1)))"
    unfolding ufa_invar_def
    by (auto intro: rep_of.domintros)
  moreover have
    "ufs_invar (Abs_ufa (uf_of_ufsi (replicate n (-1))), size_of_ufsi (replicate n (-1)))"
    using ufa_\<alpha>_ufa_init ufa_size_ufa_init
    unfolding ufs_invar_def ufa_init.abs_eq
    by (auto simp: size_of_ufsi_replicate_neg_1_eq Field_iff)
  ultimately show ?thesis
    unfolding ufsi_invar_def by blast
qed

lemma Abs_ufsi_replicate_neg_1_eq_ufsi_init:
  includes ufa.lifting and ufa_ufs_transfer
  notes [transfer_rule] = Rep_ufa_ufa_of_ufs_transfer
  shows "Abs_ufsi (replicate n (-1)) = ufsi_init n"
  apply (transfer, transfer, transfer)
  using ufa_of_ufs_ufs_of_ufsi_Abs_ufsi_eq[OF ufsi_invar_replicate_neg_1]
  using ufa_init.rep_eq ufa_init.abs_eq
  by simp

lemma ufsi_rep_of_in_Field_ufsi_\<alpha>I[simp, intro]:
  includes ufa_ufs_transfer
  assumes "i \<in> Field (ufsi_\<alpha> ufsi)"
  shows "ufsi_rep_of ufsi i \<in> Field (ufsi_\<alpha> ufsi)"
  using assms by (transfer, transfer) simp

lemma ufsi_rep_of_ufsi_rep_of[simp]:
  includes ufa_ufs_transfer
  assumes "i \<in> Field (ufsi_\<alpha> ufsi)"
  shows "ufsi_rep_of ufsi (ufsi_rep_of ufsi i) = ufsi_rep_of ufsi i"
  using assms by (transfer, transfer) simp

lemma lt_length_if_in_Field_ufsi_\<alpha>_Abs_ufsi:
  includes ufa_ufs_transfer and ufa.lifting
  notes [transfer_rule] = Rep_ufa_ufa_of_ufs_transfer
  assumes "ufsi_invar ufsi"
  assumes "i \<in> Field (ufsi_\<alpha> (Abs_ufsi ufsi))"
  shows "i < length ufsi"
  using assms
  apply(transfer, transfer, transfer)
  using Abs_ufsi_inverse ufa_of_ufs.rep_eq ufa_of_ufsi.rep_eq ufs_of_ufsi.rep_eq
  by auto

lemma Field_ufsi_\<alpha>_Abs_ufsi_eq:
  includes ufa_ufs_transfer and ufa.lifting
  notes [transfer_rule] = Rep_ufa_ufa_of_ufs_transfer
  assumes "ufsi_invar ufsi"
  shows "Field (ufsi_\<alpha> (Abs_ufsi ufsi)) = {0..<length ufsi}"
  using assms
  apply(transfer, transfer, transfer)
  by (auto simp: Abs_ufa_inverse ufa_of_ufs_ufs_of_ufsi_Abs_ufsi_eq ufsi_invarD(1))

lemma eq_uf_of_ufsi[simp]:
  assumes "ufsi_invar ufsi"
  shows "Rep_ufa (ufa_of_ufs (ufs_of_ufsi (Abs_ufsi ufsi))) = uf_of_ufsi ufsi"
  using assms
  by (simp add: Abs_ufsi_inverse ufa_of_ufs.rep_eq ufa_of_ufsi.rep_eq ufs_of_ufsi.rep_eq)

lemma ufsi_parent_of_Abs_ufsi_eq:
  includes ufa.lifting and ufa_ufs_transfer
  notes [transfer_rule] = Rep_ufa_ufa_of_ufs_transfer
  assumes "ufsi_invar ufsi"
  assumes "i \<in> Field (ufsi_\<alpha> (Abs_ufsi ufsi))"
  shows "ufsi_parent_of (Abs_ufsi ufsi) i = (if ufsi ! i < 0 then i else nat (ufsi ! i))"
  using assms
  apply transfer
  apply transfer
  apply transfer
  by (simp add: uf_of_ufsi_def)

lemma ufsi_rep_of_Abs_ufsi_eq:
  includes ufa.lifting and ufa_ufs_transfer
  notes [transfer_rule] = Rep_ufa_ufa_of_ufs_transfer
  assumes "ufsi_invar ufsi"
  assumes "i \<in> Field (ufsi_\<alpha> (Abs_ufsi ufsi))"
  shows "ufsi_rep_of (Abs_ufsi ufsi) i =
    (let pi = ufsi_parent_of (Abs_ufsi ufsi) i
    in if pi = i then i else ufsi_rep_of (Abs_ufsi ufsi) pi)"
  using assms
  apply transfer
  apply transfer
  apply transfer
  by (simp add: Let_def rep_of.psimps ufa_invarD(1) ufsi_invarD(1))

lemma ufsi_size_Abs_ufsi:
  assumes "ufsi_invar ufsi"
  assumes "x \<in> Field (ufsi_\<alpha> (Abs_ufsi ufsi))"
  assumes "ufsi_rep_of (Abs_ufsi ufsi) x = x"
  shows "ufsi_size (Abs_ufsi ufsi) x = size_of_ufsi ufsi x"
  using assms ufs_size_Abs_ufs[OF assms(1)[THEN ufsi_invarD(2)]]
  by transfer (auto simp: ufs_of_ufsi.abs_eq ufa_of_ufsi.abs_eq eq_onp_same_args)

lemma map_index_list_update:
  "map_index f (list_update xs i x) = list_update (map_index f xs) i (f i x)"
  apply(intro map_index_congL')
  by (cases "i < length xs") (auto simp: nth_list_update)

lemma uf_of_ufsi_list_update:
  "uf_of_ufsi (ufsi[i := x]) = (uf_of_ufsi ufsi)[i := (if x < 0 then i else nat x)]"
  unfolding uf_of_ufsi_def map_index_list_update by blast

lemma ufsi_union_Abs_ufsi:
  notes [transfer_rule] = Rep_ufa_ufa_of_ufs_transfer
  assumes "ufsi_invar ufsi"
  assumes "x \<in> Field (ufsi_\<alpha> (Abs_ufsi ufsi))"
  assumes "y \<in> Field (ufsi_\<alpha> (Abs_ufsi ufsi))"
  defines "rep_x \<equiv> ufsi_rep_of (Abs_ufsi ufsi) x"
  defines "rep_y \<equiv> ufsi_rep_of (Abs_ufsi ufsi) y"
  defines "sz_rep_x \<equiv> ufsi_size (Abs_ufsi ufsi) rep_x"
  defines "sz_rep_y \<equiv> ufsi_size (Abs_ufsi ufsi) rep_y"
  assumes "rep_x \<noteq> rep_y"
  shows
    "ufsi_invar (ufsi[rep_x := int rep_y, rep_y := - int (sz_rep_x + sz_rep_y)])"
      (is "ufsi_invar ?ufsi'")
  and
    "ufsi_union (Abs_ufsi ufsi) x y =
    Abs_ufsi (ufsi[rep_x := int rep_y, rep_y := - int (sz_rep_x + sz_rep_y)])"
proof -
  let ?ufa = "Abs_ufa (uf_of_ufsi ufsi)"
  
  note ufa_invar = \<open>ufsi_invar ufsi\<close>[THEN ufsi_invarD(1)]
  from ufa_invar assms(2,3) have in_Field_ufa_\<alpha>:
    "x \<in> Field (ufa_\<alpha> ?ufa)" "y \<in> Field (ufa_\<alpha> ?ufa)"
    using lt_length_if_in_Field_ufsi_\<alpha>_Abs_ufsi[OF assms(1)]
    by (simp_all add: Abs_ufa_inverse ufa_\<alpha>.rep_eq)
  from assms(1) have rep_eq_ufa_rep_of:
    "rep_x = ufa_rep_of ?ufa x"
    "rep_y = ufa_rep_of ?ufa y"
    unfolding rep_x_def rep_y_def including ufa_ufs_transfer
    by (transfer, transfer, metis Rep_ufa_inverse eq_uf_of_ufsi)+
  from assms(1) have r_rep_eq_ufa_size:
    "sz_rep_x = ufa_size ?ufa (ufa_rep_of ?ufa x) "
    "sz_rep_y = ufa_size ?ufa (ufa_rep_of ?ufa y)"
    unfolding sz_rep_x_def sz_rep_y_def rep_eq_ufa_rep_of
    including ufa_ufs_transfer
    by (transfer, transfer, metis Rep_ufa_inverse eq_uf_of_ufsi)+
 
  from assms(1-3) have "ufa_invar (uf_of_ufsi (ufsi[rep_x := int rep_y]))"
    unfolding rep_x_def rep_y_def uf_of_ufsi_list_update
    including ufa_ufs_transfer and ufa.lifting
    by (transfer, transfer, transfer)
      (auto simp: ufsi_invarD(1) intro!: ufa_invar_list_update_rep_of)
  moreover have swap:
    "ufsi[rep_y := - int (sz_rep_x + sz_rep_y), rep_x := int rep_y] =
    ufsi[rep_x := int rep_y, rep_y := - int (sz_rep_x + sz_rep_y)]"
    using \<open>rep_x \<noteq> rep_y\<close> by (metis list_update_swap)
  moreover have
    "uf_of_ufsi (ufsi[rep_y := - int (sz_rep_x + sz_rep_y)]) = uf_of_ufsi ufsi"
  proof -
    from in_Field_ufa_\<alpha> ufa_size_neq_0 have "sz_rep_x > 0" "sz_rep_y > 0"
      unfolding r_rep_eq_ufa_size by simp_all
    moreover from ufa_invar in_Field_ufa_\<alpha> have "uf_of_ufsi ufsi ! rep_y = rep_y"
      unfolding rep_eq_ufa_rep_of
      by (metis ufa_parent_of.abs_eq ufa_parent_of_ufa_rep_of eq_onp_eqD)
    ultimately show ?thesis
      unfolding uf_of_ufsi_list_update by simp (metis list_update_id)
  qed
  ultimately have uf_of_ufsi'_eq:
    "uf_of_ufsi ?ufsi' = uf_of_ufsi (ufsi[rep_x := int rep_y])"
    by (metis uf_of_ufsi_list_update)
  with \<open>ufa_invar (uf_of_ufsi (ufsi[rep_x := int rep_y]))\<close> have "ufa_invar (uf_of_ufsi ?ufsi')"
    by simp

  from assms(1-3) have uf_of_ufsi'_eq_ufa_union:
    "Abs_ufa (uf_of_ufsi ?ufsi') = ufa_union ?ufa x y"
  proof -
    from assms(1) have eq_onp_ufa_invar_uf_of_ufsi:
      "eq_onp ufa_invar (uf_of_ufsi ufsi) (uf_of_ufsi ufsi)"
      by (simp add: eq_onp_same_args ufsi_invarD(1))
    from assms(1-3) show ?thesis
      unfolding uf_of_ufsi'_eq
      unfolding ufa_union.abs_eq[OF eq_onp_ufa_invar_uf_of_ufsi]
      unfolding rep_x_def rep_y_def sz_rep_x_def sz_rep_y_def
      including ufa_ufs_transfer and ufa.lifting
      by (transfer, transfer, transfer) (simp add: uf_of_ufsi_list_update)
  qed

  have "ufs_invar (Abs_ufa (uf_of_ufsi ?ufsi'), size_of_ufsi ?ufsi')"
  proof (rule ufs_invarI)
    fix i
    assume i_in_Field': "i \<in> Field (ufa_\<alpha> (Abs_ufa (uf_of_ufsi ?ufsi')))"
    assume i_is_ufa_rep': "ufa_rep_of (Abs_ufa (uf_of_ufsi ?ufsi')) i = i"
    from i_in_Field' have i_in_Field:
      "i \<in> Field (ufa_\<alpha> ?ufa)"
      unfolding uf_of_ufsi'_eq_ufa_union by force
    from in_Field_ufa_\<alpha> i_in_Field i_is_ufa_rep' have i_is_ufa_rep:
      "ufa_rep_of ?ufa i = i"
      unfolding uf_of_ufsi'_eq_ufa_union
      by (metis ufa_rep_of_ufa_rep_of ufa_rep_of_ufa_union)
    from i_in_Field' i_is_ufa_rep' \<open>rep_x \<noteq> rep_y\<close> have "i \<noteq> rep_x"
      unfolding uf_of_ufsi'_eq_ufa_union
      using in_Field_ufa_\<alpha> rep_eq_ufa_rep_of by auto    
    have size_of_ufsi'_eq: "size_of_ufsi ?ufsi' i =
      (if i = rep_y then sz_rep_x + sz_rep_y else size_of_ufsi ufsi i)"
    proof -
      from assms(1-3) have "rep_x < length ufsi" "rep_y < length ufsi"
        using lt_length_if_in_Field_ufsi_\<alpha>_Abs_ufsi unfolding rep_x_def rep_y_def
        by blast+
      with \<open>i \<noteq> rep_x\<close> show ?thesis
        unfolding size_of_ufsi_def by (auto simp: nth_list_update)
    qed
    note ufa_size_ufa_union_if_ufa_rep_of_neq[OF \<open>rep_x \<noteq> rep_y\<close>[unfolded rep_eq_ufa_rep_of]]
    note [simp] = this[OF in_Field_ufa_\<alpha> i_in_Field]
    from i_in_Field i_is_ufa_rep \<open>i \<noteq> rep_x\<close> in_Field_ufa_\<alpha> show
      "size_of_ufsi ?ufsi' i = ufa_size (Abs_ufa (uf_of_ufsi ?ufsi')) i"
      unfolding size_of_ufsi'_eq uf_of_ufsi'_eq_ufa_union
      unfolding rep_eq_ufa_rep_of r_rep_eq_ufa_size
      using assms(1)[unfolded ufsi_invar_def ufs_invar_def] by simp
  qed
  with \<open>ufa_invar (uf_of_ufsi ?ufsi')\<close> show "ufsi_invar ?ufsi'"
    unfolding ufsi_invar_def by simp

  with assms(1) uf_of_ufsi'_eq_ufa_union show "ufsi_union (Abs_ufsi ufsi) x y = Abs_ufsi ?ufsi'"
    including ufa_ufs_transfer
    by (transfer, transfer) (metis Rep_ufa_inverse eq_uf_of_ufsi)
qed

lemma ufsi_compress_Abs_ufsi_eq_if_neq_ufsi_rep_of:
  notes [transfer_rule] = Rep_ufa_ufa_of_ufs_transfer
  assumes "ufsi_invar ufsi"
  assumes "x \<in> Field (ufsi_\<alpha> (Abs_ufsi ufsi))"
  defines "rep_x \<equiv> ufsi_rep_of (Abs_ufsi ufsi) x"
  assumes "rep_x \<noteq> x"
  shows "ufsi_invar (ufsi[x := int rep_x])" (is "ufsi_invar ?ufsi'")
    and "ufsi_compress (Abs_ufsi ufsi) x = Abs_ufsi (ufsi[x := int rep_x])"
proof -
  let ?ufa = "Abs_ufa (uf_of_ufsi ufsi)"
  
  note ufa_invar = \<open>ufsi_invar ufsi\<close>[THEN ufsi_invarD(1)]

  from assms(1) have rep_eq_ufa_rep_of:
    "rep_x = ufa_rep_of ?ufa x"
    unfolding rep_x_def including ufa_ufs_transfer
    by (transfer, transfer, metis Rep_ufa_inverse eq_uf_of_ufsi)+
 
  from assms(1-2) have "ufa_invar (uf_of_ufsi ?ufsi')"
    unfolding rep_x_def uf_of_ufsi_list_update
    including ufa_ufs_transfer and ufa.lifting
    by (transfer, transfer, transfer)
      (auto simp: ufsi_invarD(1) intro!: ufa_invar_list_update_rep_of)

  from assms(1-3) have uf_of_ufsi'_eq_ufa_compress:
    "Abs_ufa (uf_of_ufsi ?ufsi') = ufa_compress ?ufa x"
  proof -
    from assms(1) have eq_onp_ufa_invar_uf_of_ufsi:
      "eq_onp ufa_invar (uf_of_ufsi ufsi) (uf_of_ufsi ufsi)"
      by (simp add: eq_onp_same_args ufsi_invarD(1))
    from assms(1,2,4) show ?thesis
      unfolding ufa_compress.abs_eq[OF eq_onp_ufa_invar_uf_of_ufsi]
      unfolding rep_x_def
      including ufa_ufs_transfer and ufa.lifting
      by (transfer, transfer, transfer) (simp add: uf_of_ufsi_list_update)
  qed

  have "ufs_invar (Abs_ufa (uf_of_ufsi ?ufsi'), size_of_ufsi ?ufsi')"
  proof (rule ufs_invarI)
    fix i
    assume i_in_Field': "i \<in> Field (ufa_\<alpha> (Abs_ufa (uf_of_ufsi ?ufsi')))"
    assume i_is_ufa_rep': "ufa_rep_of (Abs_ufa (uf_of_ufsi ?ufsi')) i = i"

    from i_in_Field' have i_in_Field:
      "i \<in> Field (ufa_\<alpha> ?ufa)"
      unfolding uf_of_ufsi'_eq_ufa_compress by force

    with assms(1) have "i \<in> Field (ufsi_\<alpha> (Abs_ufsi ufsi))"
      including ufa_ufs_transfer apply transfer apply transfer
      using ufa_of_ufs_ufs_of_ufsi_Abs_ufsi_eq by fastforce
    from assms(1) i_in_Field i_is_ufa_rep' have
      "ufsi_rep_of (Abs_ufsi ufsi) i = i"
      unfolding uf_of_ufsi'_eq_ufa_compress
      including ufa_ufs_transfer apply transfer apply transfer
      by (simp add: ufa_of_ufs_ufs_of_ufsi_Abs_ufsi_eq)

     with assms(4)[unfolded rep_x_def] have "size_of_ufsi ?ufsi' i = size_of_ufsi ufsi i"
      using size_of_ufsi_def by (metis nth_list_update_neq)
    also have "\<dots> = ufsi_size (Abs_ufsi ufsi) i"
      using \<open>i \<in> Field (ufsi_\<alpha> (Abs_ufsi ufsi))\<close> \<open>ufsi_rep_of (Abs_ufsi ufsi) i = i\<close>
      by (intro ufsi_size_Abs_ufsi[symmetric] assms)
    also have "\<dots> = ufa_size (Abs_ufa (uf_of_ufsi ?ufsi')) i"
      using assms(1) unfolding uf_of_ufsi'_eq_ufa_compress ufa_size_ufa_compress
      including ufa_ufs_transfer apply transfer apply transfer
      using ufa_of_ufs_ufs_of_ufsi_Abs_ufsi_eq by fastforce
    finally show "size_of_ufsi (ufsi[x := int rep_x]) i =
      ufa_size (Abs_ufa (uf_of_ufsi (ufsi[x := int rep_x]))) i" .
  qed
  with \<open>ufa_invar (uf_of_ufsi ?ufsi')\<close> show "ufsi_invar ?ufsi'"
    unfolding ufsi_invar_def by simp

  with assms(1) uf_of_ufsi'_eq_ufa_compress show "ufsi_compress (Abs_ufsi ufsi) x = Abs_ufsi ?ufsi'"
    including ufa_ufs_transfer
    by (transfer, transfer) (metis Rep_ufa_inverse eq_uf_of_ufsi)
qed

lemma ufsi_compress_Abs_ufsi_eq:
  notes [transfer_rule] = Rep_ufa_ufa_of_ufs_transfer
  assumes "ufsi_invar ufsi"
  assumes "x \<in> Field (ufsi_\<alpha> (Abs_ufsi ufsi))"
  defines "rep_x \<equiv> ufsi_rep_of (Abs_ufsi ufsi) x"
  shows "ufsi_invar (ufsi[x := if rep_x = x then ufsi ! x else int rep_x])" (is "ufsi_invar ?ufsi'")
    and "ufsi_compress (Abs_ufsi ufsi) x =
      Abs_ufsi (ufsi[x := if rep_x = x then ufsi ! x else int rep_x])"
proof -
  from assms(1,2) show "ufsi_invar ?ufsi'"
    unfolding rep_x_def using ufsi_compress_Abs_ufsi_eq_if_neq_ufsi_rep_of(1)
    by simp

  show "ufsi_compress (Abs_ufsi ufsi) x = Abs_ufsi ?ufsi'"
  proof(cases "rep_x = x")
    case False
    with assms(1,2) show ?thesis
      unfolding rep_x_def using ufsi_compress_Abs_ufsi_eq_if_neq_ufsi_rep_of(2)
      by simp
  next
    case True
    with assms(1,2) have "ufsi_compress (Abs_ufsi ufsi) x = Abs_ufsi ufsi"
      unfolding rep_x_def including ufa.lifting and ufa_ufs_transfer    
      apply transfer apply transfer
      using ufa_compress_ufa_rep_of_eq by fastforce
    with True show ?thesis
      by force
  qed
qed
  
lifting_update ufsi.lifting
lifting_forget ufsi.lifting

end