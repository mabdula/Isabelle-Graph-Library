(* Source: Stevens & Ghidini (2025),
   https://doi.org/10.5281/zenodo.15557955
   License: CC-BY 4.0 (https://creativecommons.org/licenses/by/4.0/)
   No modifications made. *)

theory Union_Find_Size_Int
  imports Union_Find_Size "List-Index.List_Index"
begin

definition "uf_of_ufsi \<equiv> map_index (\<lambda>i x. if x < 0 then i else nat x)"

definition "size_of_ufsi ufsi i \<equiv> nat (- (ufsi ! i))"

definition "ufsi_invar ufsi \<equiv>
  ufa_invar (uf_of_ufsi ufsi) \<and> ufs_invar (Abs_ufa (uf_of_ufsi ufsi), size_of_ufsi ufsi)"

lemma ufsi_invarD:
  assumes "ufsi_invar ufsi"
  shows
    "ufa_invar (uf_of_ufsi ufsi)"
    "ufs_invar (Abs_ufa (uf_of_ufsi ufsi), size_of_ufsi ufsi)"
  using assms unfolding ufsi_invar_def by safe

typedef ufsi = "{ufsi. ufsi_invar ufsi}"
proof -
  have "ufa_\<alpha> (Abs_ufa []) = {}"
    unfolding ufa_\<alpha>.rep_eq
    by (simp add: Abs_ufa_inverse Union_Find.\<alpha>_def ufa_invar_def)
  then have "ufsi_invar []"
    unfolding ufsi_invar_def ufs_invar_def ufa_invar_def uf_of_ufsi_def size_of_ufsi_def
    by simp
  then show ?thesis
    by blast
qed

setup_lifting type_definition_ufsi

lemma length_uf_of_ufsi[simp]:
  "length (uf_of_ufsi ufsi) = length ufsi"
  unfolding uf_of_ufsi_def by simp

context
  includes ufa.lifting and ufs.lifting
begin

lift_definition ufa_of_ufsi :: "ufsi \<Rightarrow> ufa" is uf_of_ufsi
  unfolding ufsi_invar_def by blast

lift_definition ufs_of_ufsi :: "ufsi \<Rightarrow> ufs" is
  "\<lambda>ufsi. (ufa_of_ufsi (Abs_ufsi ufsi), size_of_ufsi ufsi)"
  using Abs_ufsi_inverse unfolding ufa_of_ufsi_def ufsi_invar_def
  by simp

definition "ufsi_of_uf uf sz \<equiv> map_index (\<lambda>i x. if x = i then - (int (sz i)) else int x) uf"

lemma uf_of_ufsi_ufsi_of_uf:
  assumes "ufa_invar uf" "\<forall>i < length uf. uf ! i = i \<longrightarrow> sz i > 0"
  shows "uf_of_ufsi (ufsi_of_uf uf sz) = uf"
  using assms
  unfolding uf_of_ufsi_def ufsi_of_uf_def map_index'_comp
  by (intro map_index_congL) auto

lemma uf_of_ufsi_ufsi_of_uf_Rep_ufa:
  assumes "\<forall>i \<in> Field (ufa_\<alpha> ufa). ufa_rep_of ufa i = i \<longrightarrow> sz i > 0"
  shows "uf_of_ufsi (ufsi_of_uf (Rep_ufa ufa) sz) = Rep_ufa ufa"
  using assms uf_of_ufsi_ufsi_of_uf ufa_rep_of_if_refl_ufa_parent_of
  by transfer simp

lemma size_of_ufsi_ufsi_of_uf:
  assumes "i < length uf" "uf ! i = i"
  shows "size_of_ufsi (ufsi_of_uf uf sz) i = sz i"
  using assms unfolding ufsi_of_uf_def size_of_ufsi_def by auto

lemma size_of_ufsi_ufsi_of_uf_Rep_ufa:
  assumes "i \<in> Field (ufa_\<alpha> ufa)" "ufa_rep_of ufa i = i"
  shows "size_of_ufsi (ufsi_of_uf (Rep_ufa ufa) sz) i = sz i"
  using assms size_of_ufsi_ufsi_of_uf nth_rep_of_eq_rep_of
  by transfer fastforce

lift_definition ufsi_of_ufs :: "ufs \<Rightarrow> ufsi" is
  "\<lambda>(ufa, sz). ufsi_of_uf (Rep_ufa ufa) sz"
proof -
  fix ufs
  assume "ufs_invar ufs"
  show "?thesis ufs"
  proof(cases ufs)
    case (Pair ufa sz)
    with \<open>ufs_invar ufs\<close> have "sz i > 0"
      if "i \<in> Field (ufa_\<alpha> ufa)" "ufa_rep_of ufa i = i" for i
      using that card_gt_0_iff
      unfolding ufa_size_def ufs_invar_def by auto
    
    with \<open>ufs_invar ufs\<close> show ?thesis
      unfolding ufsi_invar_def ufs_invar_def Pair
      using Rep_ufa Rep_ufa_inverse
      by (auto simp: uf_of_ufsi_ufsi_of_uf_Rep_ufa size_of_ufsi_ufsi_of_uf_Rep_ufa)
  qed
qed

end

lemma nth_lt_0_if_ufsi_invar:
  assumes "ufsi_invar ufsi"
  assumes "i < length ufsi"
  assumes "uf_of_ufsi ufsi ! i = i"
  shows "ufsi ! i < 0"
proof -
  from assms have "i \<in> Field (ufa_\<alpha> (Abs_ufa (uf_of_ufsi ufsi)))"
    unfolding ufa_\<alpha>.rep_eq ufsi_invar_def Abs_ufa_inverse
    by (simp add: Abs_ufa_inverse)
  moreover from assms have "ufa_parent_of (Abs_ufa (uf_of_ufsi ufsi)) i = i"
    unfolding ufa_parent_of_def ufsi_invar_def
    by (simp add: Abs_ufa_inverse)
  note ufa_rep_of_if_refl_ufa_parent_of[OF this]
  moreover from calculation have
    "size_of_ufsi ufsi i = ufa_size (Abs_ufa (uf_of_ufsi ufsi)) i"
    using assms unfolding ufsi_invar_def ufs_invar_def by auto
  ultimately show ?thesis
    unfolding size_of_ufsi_def using ufa_size_neq_0
    by (metis linorder_not_le nat_le_0 neg_le_0_iff_le)
qed

lemma ufsi_of_uf_uf_of_ufsi:
  assumes "ufsi_invar ufsi"
  shows "ufsi_of_uf (uf_of_ufsi ufsi) (size_of_ufsi ufsi) = ufsi"
  using assms nth_lt_0_if_ufsi_invar[OF assms]
  unfolding ufsi_of_uf_def uf_of_ufsi_def size_of_ufsi_def map_index'_comp
  by (intro map_index_congL) fastforce

lemma ufsi_of_ufs_ufs_of_ufsi:
  "ufsi_of_ufs (ufs_of_ufsi ufsi) = ufsi"
proof -
  have [simp]: "Rep_ufa (ufa_of_ufsi (Abs_ufsi ufsi)) = uf_of_ufsi ufsi"
    if "ufsi_invar ufsi" for ufsi
    using that
    by (simp add: Abs_ufsi_inverse ufa_of_ufsi.rep_eq)
  show ?thesis
    by transfer (simp add: ufsi_of_uf_uf_of_ufsi)
qed

lemma Abs_ufsi_eq:
  assumes "ufsi_invar ufsi"
  shows "Abs_ufsi ufsi = ufsi_of_ufs (Abs_ufs (Abs_ufa (uf_of_ufsi ufsi), size_of_ufsi ufsi))"
  using assms unfolding ufsi_of_ufs_def
  by (simp add: ufsi_invar_def Abs_ufs_inverse Abs_ufa_inverse ufsi_of_uf_uf_of_ufsi)

lifting_update ufsi.lifting
lifting_forget ufsi.lifting

end