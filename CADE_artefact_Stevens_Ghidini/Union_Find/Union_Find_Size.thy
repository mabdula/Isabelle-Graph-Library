(* Source: Stevens & Ghidini (2025),
   https://doi.org/10.5281/zenodo.15557955
   License: CC-BY 4.0 (https://creativecommons.org/licenses/by/4.0/)
   No modifications made. *)

theory Union_Find_Size
  imports Union_Find
begin

definition "ufs_invar ufs \<equiv> (case ufs of (ufa, sz) \<Rightarrow>
  (\<forall>i \<in> Field (ufa_\<alpha> ufa). ufa_rep_of ufa i = i \<longrightarrow> sz i = ufa_size ufa i))"

lemma ufs_invarI:
  assumes "\<And>i. \<lbrakk> i \<in> Field (ufa_\<alpha> ufa); ufa_rep_of ufa i = i \<rbrakk> \<Longrightarrow> sz i = ufa_size ufa i"
  shows "ufs_invar (ufa, sz)"
  using assms unfolding ufs_invar_def by blast

typedef ufs = "{ufs. ufs_invar ufs}"
proof -
  have "ufs_invar (ufa_init 0, (\<lambda>x. 1))"
    unfolding ufs_invar_def ufa_invar_def
    by auto
  then show ?thesis
    by blast
qed

setup_lifting type_definition_ufs

lift_definition ufa_of_ufs :: "ufs \<Rightarrow> ufa" is fst
  unfolding ufs_invar_def .

lift_definition ufs_of_ufa :: "ufa \<Rightarrow> ufs" is
  "\<lambda>uf. (uf, ufa_size uf)"
  unfolding ufs_invar_def by simp

lift_definition ufs_init :: "nat \<Rightarrow> ufs" is
  "\<lambda>n. (ufa_init n, (\<lambda>_. 1))"
proof -
  have "ufa_size (ufa_init n) i = 1" if "i < n" for n i
    using that unfolding ufa_size_def ufa_eq_class_def ufa_\<alpha>_ufa_init
    by (auto simp: Image_def)
  then show "ufs_invar (ufa_init n, \<lambda>_. 1)" for n
    unfolding ufs_invar_def by auto
qed

definition "ufs_parent_of ufs \<equiv> ufa_parent_of (ufa_of_ufs ufs)"

definition "ufs_rep_of ufs \<equiv> ufa_rep_of (ufa_of_ufs ufs)"

definition "ufs_\<alpha> ufs \<equiv> ufa_\<alpha> (ufa_of_ufs ufs)"

definition "ufs_size ufs \<equiv> ufa_size (ufa_of_ufs ufs)"

lift_definition ufs_union :: "ufs \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ufs" is
  "\<lambda>(ufa, sz) x y.
    if x \<notin> Field (ufa_\<alpha> ufa) \<or> y \<notin> Field (ufa_\<alpha> ufa) then (ufa, sz)
    else
      let
        rep_x = ufa_rep_of ufa x;
        rep_y = ufa_rep_of ufa y
      in
        if rep_x = rep_y then (ufa, sz)
        else (ufa_union ufa x y, sz(rep_y := sz rep_y + sz rep_x))"
proof -
  fix ufs x y
  assume "ufs_invar ufs"
  then show "?thesis ufs x y"
  proof(cases "x \<notin> Field (ufa_\<alpha> (fst ufs)) \<or> y \<notin> Field (ufa_\<alpha> (fst ufs))")
    case in_Field_ufa_\<alpha>: False
    with \<open>ufs_invar ufs\<close> show ?thesis
    proof(cases "ufa_rep_of (fst ufs) x = ufa_rep_of (fst ufs) y")
      case ufa_rep_of_neq: False
      note [simp] = ufa_rep_of_ufa_union ufa_size_ufa_union_if_ufa_rep_of_neq
      from \<open>ufs_invar ufs\<close> in_Field_ufa_\<alpha> ufa_rep_of_neq show ?thesis
        unfolding ufs_invar_def
        by (auto simp: Let_def split: prod.splits)
    qed (use \<open>ufs_invar ufs\<close> in \<open>auto split: prod.splits\<close>)
  qed (auto split: prod.splits)
qed

definition "ufs_union_size ufs x y \<equiv>
  let
    rep_x = ufs_rep_of ufs x;
    rep_y = ufs_rep_of ufs y
  in
    if ufs_size ufs rep_x < ufs_size ufs rep_y
    then ufs_union ufs x y
    else ufs_union ufs y x"

lift_definition ufs_compress :: "ufs \<Rightarrow> nat \<Rightarrow> ufs" is
  "\<lambda>(ufa, sz) x. (ufa_compress ufa x, sz)"
  unfolding ufs_invar_def
  by (auto split: prod.splits)

context includes lifting_syntax
begin

named_theorems ufa_ufs_transfer

definition "ufa_ufs_rel ufa ufs \<equiv> ufa = ufa_of_ufs ufs"

lemma left_unique_ufa_ufs_rel[ufa_ufs_transfer]:
  "left_unique ufa_ufs_rel"
  unfolding left_unique_def ufa_ufs_rel_def by blast

lemma bi_total_ufa_ufs_rel[ufa_ufs_transfer]:
  "bi_total ufa_ufs_rel"
  unfolding bi_total_def ufa_ufs_rel_def
  by (metis fst_conv ufa_of_ufs.rep_eq ufs_of_ufa.rep_eq)

lemma ufa_of_ufs_transfer:
  "(ufa_ufs_rel ===> (=)) id ufa_of_ufs"
  using ufa_ufs_rel_def by auto

lemma ufs_of_ufa_transfer[ufa_ufs_transfer]:
  "((=) ===> ufa_ufs_rel) id ufs_of_ufa"
  unfolding ufa_ufs_rel_def
  by (intro rel_funI, transfer) simp

lemma ufa_of_ufs_ufs_of_ufa_eq[simp]:
  notes [transfer_rule] = ufa_ufs_transfer ufa_of_ufs_transfer
  shows "ufa_of_ufs (ufs_of_ufa ufa) = ufa"
  by transfer simp

lemma Rep_ufa_ufa_of_ufs_transfer:
  "(ufa_ufs_rel ===> pcr_ufa) Rep_ufa ufa_of_ufs"
  unfolding ufa_ufs_rel_def
  by (metis (mono_tags, lifting) cr_ufa_def rel_funI ufa.pcr_cr_eq)

lemma ufs_parent_of_transfer[ufa_ufs_transfer]:
  "(ufa_ufs_rel ===> (=) ===> (=)) ufa_parent_of ufs_parent_of"
  unfolding ufa_ufs_rel_def ufs_parent_of_def by blast

lemma ufs_rep_of_transfer[ufa_ufs_transfer]:
  "(ufa_ufs_rel ===> (=) ===> (=)) ufa_rep_of ufs_rep_of"
  unfolding ufa_ufs_rel_def ufs_rep_of_def by blast

lemma ufs_\<alpha>_transfer[ufa_ufs_transfer]:
  "(ufa_ufs_rel ===> (=)) ufa_\<alpha> ufs_\<alpha>"
  unfolding ufa_ufs_rel_def ufs_\<alpha>_def by blast

lemma ufs_size_transfer[ufa_ufs_transfer]:
  "(ufa_ufs_rel ===> (=) ===> (=)) ufa_size ufs_size"
  unfolding ufa_ufs_rel_def ufs_size_def by blast

lemma ufa_of_ufs_ufs_init:
  "ufa_of_ufs (ufs_init n) = ufa_init n"
  by transfer simp

lemma ufa_init_ufs_union_transfer[ufa_ufs_transfer]:
  "((=) ===> ufa_ufs_rel) ufa_init ufs_init"
  by (intro rel_funI) (auto simp: ufa_ufs_rel_def ufa_of_ufs_ufs_init)

lemma ufa_of_ufs_ufs_union:
  "ufa_of_ufs (ufs_union ufs x y) = ufa_union (ufa_of_ufs ufs) x y"
  by transfer (auto simp: Let_def)

lemma ufa_union_ufs_union_transfer[ufa_ufs_transfer]:
  "(ufa_ufs_rel ===> (=) ===> (=) ===> ufa_ufs_rel) ufa_union ufs_union"
  by (intro rel_funI) (auto simp: ufa_ufs_rel_def ufa_of_ufs_ufs_union case_prod_unfold Let_def)

lemma ufa_of_ufs_ufs_compress:
  "ufa_of_ufs (ufs_compress ufs x) = ufa_compress (ufa_of_ufs ufs) x"
  by transfer (simp split: prod.splits)

lemma ufa_compress_ufs_compress_transfer[ufa_ufs_transfer]:
  "(ufa_ufs_rel ===> (=) ===> ufa_ufs_rel) ufa_compress ufs_compress"
  unfolding ufa_ufs_rel_def
  by (intro rel_funI) (simp add: ufa_of_ufs_ufs_compress)

lemma ufa_of_ufs_ufs_union_size:
  "ufa_of_ufs (ufs_union_size ufs x y) = ufa_union_size (ufa_of_ufs ufs) x y"
  unfolding ufs_union_size_def ufs_rep_of_def ufs_size_def
  by transfer (auto simp: ufa_union_size_def Let_def)

lemma ufa_union_size_ufs_union_size_transfer[ufa_ufs_transfer]:
  "(ufa_ufs_rel ===> (=) ===> (=) ===> ufa_ufs_rel) ufa_union_size ufs_union_size"
  unfolding ufa_ufs_rel_def
  by (intro rel_funI) (simp add: ufa_of_ufs_ufs_union_size)

end

lemma ufs_rep_of_induct[case_names "parametric" rep not_rep, consumes 1]:
  includes lifting_syntax
  notes [transfer_rule] = ufa_ufs_transfer
  assumes "i \<in> Field (ufs_\<alpha> uf)"
  assumes [transfer_rule]:
    "(ufa_ufs_rel ===> (=) ===> (=)) (\<lambda>ufa. P (ufs_of_ufa ufa)) P"
  assumes rep: "\<And>i. \<lbrakk> i \<in> Field (ufs_\<alpha> uf); ufs_parent_of uf i = i \<rbrakk> \<Longrightarrow> P uf i"
  assumes not_rep:
    "\<And>i. \<lbrakk> i \<in> Field (ufs_\<alpha> uf); ufs_parent_of uf i \<noteq> i; P uf (ufs_parent_of uf i) \<rbrakk>
    \<Longrightarrow> P uf i"
  shows "P uf i"
  using assms(1,3-)
  by (transfer fixing: P) (rule ufa_rep_of_induct)

lifting_update ufs.lifting
lifting_forget ufs.lifting

definition "eq_ufs ufs1 ufs2 \<equiv> ufa_of_ufs ufs1 = ufa_of_ufs ufs2 \<and>
  (\<forall>i \<in> Field (ufs_\<alpha> ufs1). ufs_rep_of ufs1 i = i \<longrightarrow> ufs_size ufs1 i = ufs_size ufs2 i)"

lemma refl_eq_ufs[simp, intro]: "eq_ufs ufs ufs"
  unfolding eq_ufs_def by simp

lemma reflp_eq_ufs: "reflp eq_ufs"
  by (intro reflpI) simp

lemma sym_eq_ufs: "eq_ufs ufs1 ufs2 \<Longrightarrow> eq_ufs ufs2 ufs1"
  unfolding eq_ufs_def ufs_rep_of_def ufs_\<alpha>_def including ufs.lifting
  by transfer auto

lemma trans_eq_ufs: "eq_ufs ufs1 ufs2 \<Longrightarrow> eq_ufs ufs2 ufs3 \<Longrightarrow> eq_ufs ufs1 ufs3"
  unfolding eq_ufs_def ufs_rep_of_def ufs_\<alpha>_def including ufs.lifting
  by transfer auto

lemma equivp_eq_ufs: "equivp eq_ufs"
  using sym_eq_ufs trans_eq_ufs
  by (intro equivpI reflpI sympI transpI) blast+

lemma eq_ufs_eq_transfer[ufa_ufs_transfer]:
  includes lifting_syntax
  shows "(ufa_ufs_rel ===> ufa_ufs_rel ===> (=)) (=) eq_ufs"
  unfolding eq_ufs_def
  apply(intro rel_funI)
  using ufa_ufs_rel_def ufs_size_def by auto

lemma eq_ufs_ufs_of_ufa_ufa_of_ufs:
  "eq_ufs ufs (ufs_of_ufa (ufa_of_ufs ufs))"
  unfolding eq_ufs_def ufs_size_def
  by (simp add: eq_ufs_def ufa_of_ufs.rep_eq ufs_of_ufa.rep_eq)

lemma id_eq_ufs_ufs_of_ufa_ufa_of_ufs:
  includes lifting_syntax
  shows "(eq_ufs ===> eq_ufs) id (\<lambda>ufs. ufs_of_ufa (ufa_of_ufs ufs))"
  unfolding eq_ufs_def unfolding ufs_size_def
  by (intro rel_funI) (simp add: ufa_of_ufs.rep_eq ufs_of_ufa.rep_eq)

lemma ufs_rep_of_eq_if_eq_ufs:
  notes [transfer_rule] = ufa_ufs_transfer ufa_of_ufs_transfer
  assumes "eq_ufs ufs1 ufs2"
  shows "ufs_rep_of ufs1 i = ufs_rep_of ufs2 i"
  using assms unfolding eq_ufs_def
  by transfer simp

lemma ufs_size_eq_if_eq_ufs:
  notes [transfer_rule] = ufa_ufs_transfer ufa_of_ufs_transfer
  assumes "eq_ufs ufs1 ufs2"
  assumes "i \<in> Field (ufs_\<alpha> ufs1)"
  shows "ufs_size ufs1 (ufs_rep_of ufs1 i) = ufs_size ufs2 (ufs_rep_of ufs2 i)"
  using assms unfolding eq_ufs_def
  by transfer simp

lemma ufs_\<alpha>_eq_if_eq_ufs[simp]:
  notes [transfer_rule] = ufa_ufs_transfer ufa_of_ufs_transfer
  assumes "eq_ufs ufs1 ufs2"
  shows "ufs_\<alpha> ufs1 = ufs_\<alpha> ufs2"
  using assms unfolding eq_ufs_def
  by transfer simp

lemma ufs_size_Abs_ufs:
  assumes "ufs_invar ufs"
  assumes "x \<in> Field (ufs_\<alpha> (Abs_ufs ufs))"
  assumes "ufs_rep_of (Abs_ufs ufs) x = x"
  shows "ufs_size (Abs_ufs ufs) x = snd ufs x"
proof -
  from assms have [simp]:
    "ufa_of_ufs (Abs_ufs ufs) = fst ufs"
    using Abs_ufs_inverse ufa_of_ufs.rep_eq by simp
  from assms show ?thesis
    unfolding ufs_invar_def ufs_size_def ufs_rep_of_def ufs_\<alpha>_def
    by (transfer fixing: ufs) auto
qed

lemma ufs_union_Abs_ufs:
  assumes "ufs_invar ufs"
  assumes "x \<in> Field (ufs_\<alpha> (Abs_ufs ufs))" "y \<in> Field (ufs_\<alpha> (Abs_ufs ufs))"
  assumes "ufs_rep_of (Abs_ufs ufs) x \<noteq> ufs_rep_of (Abs_ufs ufs) y"
  shows "ufs_union (Abs_ufs ufs) x y =
    Abs_ufs (ufa_union (fst ufs) x y,
      (snd ufs)(ufs_rep_of (Abs_ufs ufs) y := ufs_size (Abs_ufs ufs) x + ufs_size (Abs_ufs ufs) y))"
proof -
  from assms have [simp]:
    "ufa_of_ufs (Abs_ufs ufs) = fst ufs"
    using Abs_ufs_inverse ufa_of_ufs.rep_eq by simp
  from assms show ?thesis
    unfolding ufs_\<alpha>_def ufs_rep_of_def ufs_size_def
    by (subst ufs_union.abs_eq)
      (auto simp: eq_onp_same_args ufs_invar_def add.commute Let_def case_prod_unfold)
qed

bundle ufa_ufs_transfer = ufa_ufs_transfer[transfer_rule]

end