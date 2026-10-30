(* Based on: Stevens & Ghidini (2025),
   https://doi.org/10.5281/zenodo.15557955
   License of original: CC-BY 4.0 (https://creativecommons.org/licenses/by/4.0/)
   This file has been modified from the original. *)

theory Union_Find_Size_Int_Imp_Partial
  imports Union_Find.Union_Find_Size_Int_Quotient Separation_Logic_Imperative_HOL_Partial.Sep_Main
begin

(* Port to Separation_Logic_Imperative_HOL_Partial: avoid ambiguity with list update. *)
no_notation Ref.update (\<open>_ := _\<close> 62)

section \<open>Basic Union-Find Operations\<close>

type_synonym ufsi_imp = "int array"

definition is_ufsi :: "ufsi \<Rightarrow> ufsi_imp \<Rightarrow> assn" where
  "is_ufsi ufsi ufsi_imp \<equiv> \<exists>\<^sub>Aufsi_list. ufsi_imp \<mapsto>\<^sub>a ufsi_list * 
    \<up>(ufsi_invar ufsi_list \<and> ufsi = Abs_ufsi ufsi_list)"

definition ufsi_imp_init :: "nat \<Rightarrow> ufsi_imp Heap" where
  "ufsi_imp_init n \<equiv> Array.new n (-1)"

lemma ufsi_imp_init_rule[sep_heap_rules]:
  "<emp> ufsi_imp_init n <is_ufsi (ufsi_init n)>"
  unfolding ufsi_imp_init_def is_ufsi_def[abs_def]
  using ufsi_invar_replicate_neg_1  
  by (sep_auto simp: Abs_ufsi_replicate_neg_1_eq_ufsi_init)
  
definition "ufsi_imp_parent_of ufsi_imp i \<equiv>
  do {
    n \<leftarrow> Array.nth ufsi_imp i;
    return (if n < 0 then i else nat n)
  }"

lemma ufsi_parent_of_rule[sep_heap_rules]:
  assumes "i \<in> Field (ufsi_\<alpha> ufsi)"
  shows
    "<is_ufsi ufsi ufsi_imp>
      ufsi_imp_parent_of ufsi_imp i
    <\<lambda>r. is_ufsi ufsi ufsi_imp * \<up>(r = ufsi_parent_of ufsi i)>"
  using assms lt_length_if_in_Field_ufsi_\<alpha>_Abs_ufsi
  unfolding ufsi_imp_parent_of_def is_ufsi_def
  by (sep_auto simp: ufsi_parent_of_Abs_ufsi_eq)

definition "ufsi_imp_size ufsi_imp x \<equiv> do {
  sz \<leftarrow> Array.nth ufsi_imp x;
  if sz < 0 then return (nat (- sz)) else return 0
}"

lemma ufsi_imp_size_rule[sep_heap_rules]:
  assumes "i \<in> Field (ufsi_\<alpha> ufsi)"
  assumes "ufsi_rep_of ufsi i = i"
  shows
    "<is_ufsi ufsi ufsi_imp>
      ufsi_imp_size ufsi_imp i
    <\<lambda>r. is_ufsi ufsi ufsi_imp * \<up>(r = ufsi_size ufsi i)>"
  using assms lt_length_if_in_Field_ufsi_\<alpha>_Abs_ufsi
  unfolding is_ufsi_def ufsi_imp_size_def
  by (sep_auto simp: Abs_ufsi_inverse size_of_ufsi_def ufsi_size_Abs_ufsi)

definition "ufsi_imp_link ufsi_imp rep_x rep_y sz \<equiv> do {
  Array.upd rep_x (int rep_y) ufsi_imp;
  Array.upd rep_y (- int sz) ufsi_imp
}"

lemma ufsi_imp_link_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufsi_\<alpha> ufsi)" "y \<in> Field (ufsi_\<alpha> ufsi)"
  defines "rep_x \<equiv> ufsi_rep_of ufsi x"
  defines "rep_y \<equiv> ufsi_rep_of ufsi y"
  defines "sz_rep_x \<equiv> ufsi_size ufsi rep_x"
  defines "sz_rep_y \<equiv> ufsi_size ufsi rep_y"
  assumes "rep_x \<noteq> rep_y"
  shows 
    "<is_ufsi ufsi ufsi_imp>
      ufsi_imp_link ufsi_imp rep_x rep_y (sz_rep_x + sz_rep_y)
    <is_ufsi (ufsi_union ufsi x y)>"
  using assms lt_length_if_in_Field_ufsi_\<alpha>_Abs_ufsi ufsi_union_Abs_ufsi
  unfolding ufsi_imp_link_def by (sep_auto simp: is_ufsi_def)

section \<open>Union-Find Operations with Path Compression\<close>

subsection \<open>Equivalence of @{typ ufsi} w.r.t. @{const ufsi_rep_of}}\<close>

definition "eq_on_ufsi_rep_of ufsi1 ufsi2 \<equiv>
  ufsi_\<alpha> ufsi1 = ufsi_\<alpha> ufsi2 \<and>
  (\<forall>x \<in> Field (ufsi_\<alpha> ufsi2). ufsi_rep_of ufsi1 x = ufsi_rep_of ufsi2 x)"

lemma reflp_eq_on_ufsi_rep_of[intro!]:
  "reflp eq_on_ufsi_rep_of"
  unfolding reflp_def eq_on_ufsi_rep_of_def by blast

lemma symp_eq_on_ufsi_rep_of[intro!]:
  "symp eq_on_ufsi_rep_of"
  unfolding symp_def eq_on_ufsi_rep_of_def by simp

lemma transp_eq_on_ufsi_rep_of[intro!]:
  "transp eq_on_ufsi_rep_of"
  unfolding transp_def eq_on_ufsi_rep_of_def by simp

lemma ufsi_\<alpha>_eq_if_eq_on_ufsi_rep_of[simp]:
  assumes "eq_on_ufsi_rep_of ufsi1 ufsi2"
  shows "ufsi_\<alpha> ufsi1 = ufsi_\<alpha> ufsi2"
  using assms unfolding eq_on_ufsi_rep_of_def by blast

lemma ufsi_rep_of_eq_if_eq_on_ufsi_rep_of:
  assumes "eq_on_ufsi_rep_of ufsi1 ufsi2"
  assumes "x \<in> Field (ufsi_\<alpha> ufsi2)"
  shows "ufsi_rep_of ufsi1 x = ufsi_rep_of ufsi2 x"
  using assms unfolding eq_on_ufsi_rep_of_def by blast

lemma ufsi_parent_of_in_Field_ufsi_\<alpha>I[simp, intro]:
  assumes "x \<in> Field (ufsi_\<alpha> ufsi)"
  shows "ufsi_parent_of ufsi x \<in> Field (ufsi_\<alpha> ufsi)"
  using assms
  including ufsi.lifting and ufa_ufs_transfer
  by (transfer, transfer) (metis ufa_parent_of_in_Field_ufa_\<alpha>I)

lemma ufsi_parent_of_in_Field_ufsi_\<alpha>_if_eq_on_ufsi_rep_of:
  assumes "eq_on_ufsi_rep_of ufsi1 ufsi2"
  assumes "x \<in> Field (ufsi_\<alpha> ufsi2)"
  shows "ufsi_parent_of ufsi1 x \<in> Field (ufsi_\<alpha> ufsi2)"
  using assms
  by (metis ufsi_parent_of_in_Field_ufsi_\<alpha>I ufsi_\<alpha>_eq_if_eq_on_ufsi_rep_of)

lemma ufsi_rep_of_refl_iff_ufsi_parent_of_refl:
  assumes "x \<in> Field (ufsi_\<alpha> ufsi)"
  shows "ufsi_rep_of ufsi x = x \<longleftrightarrow> ufsi_parent_of ufsi x = x"
  using assms
  including ufsi.lifting and ufa_ufs_transfer
  by (transfer, transfer) (simp add: ufa_rep_of_refl_iff_ufa_parent_of_refl)

lemma ufsi_parent_of_refl_iff_if_eq_on_ufsi_rep_of:
  assumes "eq_on_ufsi_rep_of ufsi1 ufsi2"
  assumes "x \<in> Field (ufsi_\<alpha> ufsi2)"
  shows "ufsi_parent_of ufsi1 x = x \<longleftrightarrow> ufsi_parent_of ufsi2 x = x"
  using assms unfolding eq_on_ufsi_rep_of_def
  using ufsi_rep_of_refl_iff_ufsi_parent_of_refl by metis

lemma ufsi_size_ufsi_rep_of_if_eq_on_ufsi_rep_of:
  assumes "eq_on_ufsi_rep_of ufsi1 ufsi2"
  assumes "x \<in> Field (ufsi_\<alpha> ufsi2)"
  shows "ufsi_size ufsi1 x = ufsi_size ufsi2 x"
  using assms unfolding eq_on_ufsi_rep_of_def
  including ufsi.lifting and ufa_ufs_transfer
  by (transfer, transfer) (simp add: ufa_eq_class_def ufa_size_def)

lemma eq_on_ufsi_rep_of_ufsi_union:
  assumes "eq_on_ufsi_rep_of ufsi1 ufsi2"
  assumes "x \<in> Field (ufsi_\<alpha> ufsi2)" "y \<in> Field (ufsi_\<alpha> ufsi2)"
  shows "eq_on_ufsi_rep_of (ufsi_union ufsi1 x y) (ufsi_union ufsi2 x y)"
  using assms unfolding eq_on_ufsi_rep_of_def
  including ufsi.lifting and ufa_ufs_transfer
  by (transfer, transfer) (simp add: ufa_rep_of_ufa_union)

lemma eq_on_ufsi_rep_of_ufsi_compressI:
  assumes "eq_on_ufsi_rep_of ufsi1 ufsi2"
  assumes "x \<in> Field (ufsi_\<alpha> ufsi2)"
  shows "eq_on_ufsi_rep_of (ufsi_compress ufsi1 x) ufsi2"
    and "eq_on_ufsi_rep_of ufsi1 (ufsi_compress ufsi2 x)"
  using assms unfolding eq_on_ufsi_rep_of_def
  including ufsi.lifting and ufa_ufs_transfer
  by (transfer, transfer; simp)+

subsection \<open>Heap Assertion\<close>

definition "is_ufsi_c ufsi ufsi_imp \<equiv>
  (\<exists>\<^sub>Aufsi'. is_ufsi ufsi' ufsi_imp * \<up>(eq_on_ufsi_rep_of ufsi' ufsi))"

lemma is_ufsi_entails_is_ufsi_c:
  "is_ufsi ufsi ufsi_imp \<Longrightarrow>\<^sub>A is_ufsi_c ufsi ufsi_imp"
  unfolding is_ufsi_def is_ufsi_c_def eq_on_ufsi_rep_of_def
  by sep_auto

lemma is_ufsi_entails_is_ufsi_c_if_eq_on_ufsi_rep_of:
  "eq_on_ufsi_rep_of ufsi ufsi' \<Longrightarrow> is_ufsi ufsi ufsi_imp \<Longrightarrow>\<^sub>A is_ufsi_c ufsi' ufsi_imp"
  unfolding is_ufsi_c_def by sep_auto

subsection \<open>Operations\<close>

definition "ufsi_imp_compress ufsi_imp i rep_i \<equiv> 
  if rep_i = i then return ufsi_imp else Array.upd i (int rep_i) ufsi_imp"

lemma ufsi_imp_compress_is_ufsi_rule:
  assumes "x \<in> Field (ufsi_\<alpha> ufsi)"
  shows "<is_ufsi ufsi ufsi_imp>
    ufsi_imp_compress ufsi_imp x (ufsi_rep_of ufsi x)
  <\<lambda>r. is_ufsi (ufsi_compress ufsi x) ufsi_imp * \<up>(r = ufsi_imp)>"
  using assms ufsi_compress_Abs_ufsi_eq reflp_eq_on_ufsi_rep_of[unfolded reflp_def]
  unfolding ufsi_imp_compress_def is_ufsi_def
  (* Port to Separation_Logic_Imperative_HOL_Partial: the existential in the postcondition
     is instantiated explicitly. *)
  apply (sep_auto simp: lt_length_if_in_Field_ufsi_\<alpha>_Abs_ufsi)
  subgoal premises prems for ufsi_list a b
    using prems
    by (intro mod_exI[where x = "ufsi_list[x := int (ufsi_rep_of (Abs_ufsi ufsi_list) x)]"])
      (force simp: mod_pure_star_dist)
  done

partial_function (heap) ufsi_imp_rep_of_c :: "ufsi_imp \<Rightarrow> nat \<Rightarrow> nat Heap" 
  where [code]: 
  "ufsi_imp_rep_of_c ufsi_imp i = do {
    pi \<leftarrow> ufsi_imp_parent_of ufsi_imp i;
    if pi = i then return i
    else do {
      rep_i \<leftarrow> ufsi_imp_rep_of_c ufsi_imp pi;
      ufsi_imp_compress ufsi_imp i rep_i;
      return rep_i
    }
  }"

lemma ufsi_imp_rep_of_c_is_ufsi_rule[sep_heap_rules]:
  assumes "i \<in> Field (ufsi_\<alpha> ufsi)"
  shows
    "<is_ufsi ufsi ufsi_imp>
      ufsi_imp_rep_of_c ufsi_imp i
    <\<lambda>r. is_ufsi_c ufsi ufsi_imp * \<up>(r = ufsi_rep_of ufsi i)>"
  using assms
proof(induction rule: ufsi_rep_of_induct)
  case "parametric"
  then show ?case
    unfolding ufa_ufs_rel_def
    by (intro rel_funI) simp
next
  case (rep i)
  from rep have rep_eq: "ufsi_rep_of ufsi i = i"
    including ufa_ufs_transfer and ufsi.lifting
    using ufa_rep_of_if_refl_ufa_parent_of by (transfer, transfer)
  (* Port to Separation_Logic_Imperative_HOL_Partial: weaken the postcondition explicitly
     instead of using the sep_auto option "eintros add: is_ufsi_entails_is_ufsi_c". *)
  show ?case
    apply (rule ht_cons_post_prec[where Q = "\<lambda>r. is_ufsi ufsi ufsi_imp * \<up>(r = ufsi_rep_of ufsi i)"])
    subgoal
      (* The first step is done manually, so that sep_auto does not explore the unreachable
         recursive branch. *)
      apply (subst ufsi_imp_rep_of_c.simps)
      apply (rule ht_bind[OF ufsi_parent_of_rule[OF rep(1)]])
      apply (rule ht_extract_pre_pure(1))
      using rep(2) rep_eq by sep_auto
    by (rule ent_star_mono[OF is_ufsi_entails_is_ufsi_c ent_refl])
next
  case (not_rep i)
  from not_rep.hyps have [simp]:
    "ufsi_rep_of ufsi (ufsi_parent_of ufsi i) = ufsi_rep_of ufsi i"
    including ufa_ufs_transfer and ufsi.lifting
    using ufa_rep_of_ufa_parent_of by (transfer, transfer)
  have compress_rule:
    "<is_ufsi ufsi' ufsi_imp>
      ufsi_imp_compress ufsi_imp i (ufsi_rep_of ufsi i)
    <\<lambda>r. is_ufsi (ufsi_compress ufsi' i) ufsi_imp * \<up>(r = ufsi_imp)>"
    if "eq_on_ufsi_rep_of ufsi' ufsi" for ufsi'
  proof -
    note [sep_heap_rules] = ufsi_imp_compress_is_ufsi_rule
    from not_rep.hyps(1) that show ?thesis
      by (sep_auto simp: ufsi_rep_of_eq_if_eq_on_ufsi_rep_of[symmetric])
  qed
  (* Port to Separation_Logic_Imperative_HOL_Partial: the compression step is first lifted to
     is_ufsi_c, so that sep_auto does not have to instantiate existentials. *)
  have compress_c_rule[sep_heap_rules]:
    "<is_ufsi_c ufsi ufsi_imp>
      ufsi_imp_compress ufsi_imp i (ufsi_rep_of ufsi i)
    <\<lambda>r. is_ufsi_c ufsi ufsi_imp * \<up>(r = ufsi_imp)>"
  proof -
    have rule': "<is_ufsi ufsi' ufsi_imp>
      ufsi_imp_compress ufsi_imp i (ufsi_rep_of ufsi i)
      <\<lambda>r. is_ufsi_c ufsi ufsi_imp * \<up>(r = ufsi_imp)>"
      if eq: "eq_on_ufsi_rep_of ufsi' ufsi" for ufsi'
      by (rule ht_cons_post_prec[OF compress_rule[OF eq]])
        (rule ent_star_mono[OF is_ufsi_entails_is_ufsi_c_if_eq_on_ufsi_rep_of[OF
                eq_on_ufsi_rep_of_ufsi_compressI(1)[OF eq not_rep.hyps(1)]] ent_refl])
    show ?thesis
      apply (rule ht_cons_pre[where
            P' = "\<exists>\<^sub>Aufsi'. is_ufsi ufsi' ufsi_imp * \<up>(eq_on_ufsi_rep_of ufsi' ufsi)"])
      subgoal unfolding is_ufsi_c_def by (rule ent_refl)
      by (intro ht_exEI ht_extract_pre_pure(1) rule')
  qed
  note [sep_heap_rules] = not_rep.IH
  show ?case
    apply (subst ufsi_imp_rep_of_c.simps)
    apply (rule ht_bind[OF ufsi_parent_of_rule[OF not_rep.hyps(1)]])
    apply (rule ht_extract_pre_pure(1))
    using not_rep.hyps(1,2) by sep_auto
qed

lemma ufsi_imp_rep_of_c_rule[sep_heap_rules]:
  assumes "i \<in> Field (ufsi_\<alpha> ufsi)"
  shows
    "<is_ufsi_c ufsi ufsi_imp>
      ufsi_imp_rep_of_c ufsi_imp i
    <\<lambda>r. is_ufsi_c ufsi ufsi_imp * \<up>(r = ufsi_rep_of ufsi i)>"
proof -
  (* Port to Separation_Logic_Imperative_HOL_Partial: the original proof used the sep_auto
     option "eintros del: exI", which is not available here. *)
  have rule': "<is_ufsi ufsi' ufsi_imp> ufsi_imp_rep_of_c ufsi_imp i
    <\<lambda>r. is_ufsi_c ufsi ufsi_imp * \<up>(r = ufsi_rep_of ufsi i)>"
    if eq: "eq_on_ufsi_rep_of ufsi' ufsi" for ufsi'
  proof (rule ht_cons_post_prec[OF ufsi_imp_rep_of_c_is_ufsi_rule])
    show "i \<in> Field (ufsi_\<alpha> ufsi')"
      using assms eq by simp
  next
    fix r
    show "is_ufsi_c ufsi' ufsi_imp * \<up>(r = ufsi_rep_of ufsi' i)
      \<Longrightarrow>\<^sub>A is_ufsi_c ufsi ufsi_imp * \<up>(r = ufsi_rep_of ufsi i)"
      using eq assms unfolding is_ufsi_c_def
      by (sep_auto intro: transp_eq_on_ufsi_rep_of[THEN transpD]
          simp: ufsi_rep_of_eq_if_eq_on_ufsi_rep_of)
  qed
  show ?thesis
    apply (rule ht_cons_pre[where
          P' = "\<exists>\<^sub>Aufsi'. is_ufsi ufsi' ufsi_imp * \<up>(eq_on_ufsi_rep_of ufsi' ufsi)"])
    subgoal unfolding is_ufsi_c_def by (rule ent_refl)
    by (intro ht_exEI ht_extract_pre_pure(1) rule')
qed

definition "ufsi_imp_union_size_c ufsi_imp x y \<equiv> do {
  rep_x \<leftarrow> ufsi_imp_rep_of_c ufsi_imp x;
  rep_y \<leftarrow> ufsi_imp_rep_of_c ufsi_imp y;
  if rep_x = rep_y then return ufsi_imp
  else do {
    sz_rep_x \<leftarrow> ufsi_imp_size ufsi_imp rep_x;
    sz_rep_y \<leftarrow> ufsi_imp_size ufsi_imp rep_y;
    if sz_rep_x < sz_rep_y then do {
      ufsi_imp_link ufsi_imp rep_x rep_y (sz_rep_x + sz_rep_y)
    }
    else do {
      ufsi_imp_link ufsi_imp rep_y rep_x (sz_rep_y + sz_rep_x)
    }
  }
}"

lemma ufsi_imp_size_is_ufsi_c_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufsi_\<alpha> ufsi)"
  assumes "ufsi_rep_of ufsi x = x"
  shows
    "<is_ufsi_c ufsi ufsi_imp> ufsi_imp_size ufsi_imp x
    <\<lambda>r. is_ufsi_c ufsi ufsi_imp * \<up>(r = ufsi_size ufsi x)>"
  using assms ufsi_size_ufsi_rep_of_if_eq_on_ufsi_rep_of
  by (sep_auto simp: is_ufsi_c_def ufsi_rep_of_eq_if_eq_on_ufsi_rep_of)

lemma ufsi_imp_link_is_ufsi_c_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufsi_\<alpha> ufsi)" "y \<in> Field (ufsi_\<alpha> ufsi)"
  defines "rep_x \<equiv> ufsi_rep_of ufsi x"
  defines "rep_y \<equiv> ufsi_rep_of ufsi y"
  defines "sz_rep_x \<equiv> ufsi_size ufsi rep_x"
  defines "sz_rep_y \<equiv> ufsi_size ufsi rep_y"
  assumes "rep_x \<noteq> rep_y"
  shows 
    "<is_ufsi_c ufsi ufsi_imp>
      ufsi_imp_link ufsi_imp rep_x rep_y (sz_rep_x + sz_rep_y)
    <is_ufsi_c (ufsi_union ufsi x y)>"
proof -
  let ?rep = "\<lambda>ufsi x. ufsi_rep_of ufsi x"
  let ?sz = "\<lambda>ufsi x. ufsi_size ufsi (?rep ufsi x)"
  have [sep_heap_rules]:
    "<is_ufsi ufsi' ufsi_imp>
      ufsi_imp_link ufsi_imp rep_x rep_y (sz_rep_x + sz_rep_y)
    <is_ufsi_c (ufsi_union ufsi x y)>"
    if "eq_on_ufsi_rep_of ufsi' ufsi" for ufsi'
  proof -
    have "ufsi_imp_link ufsi_imp rep_x rep_y (sz_rep_x + sz_rep_y) =
      ufsi_imp_link ufsi_imp (?rep ufsi' x) (?rep ufsi' y) (?sz ufsi' x + ?sz ufsi' y)"
      using assms(1,2) that unfolding assms(3-6)
      using ufsi_rep_of_eq_if_eq_on_ufsi_rep_of ufsi_size_ufsi_rep_of_if_eq_on_ufsi_rep_of
      by simp
    moreover from assms(1,2) that have "x \<in> Field (ufsi_\<alpha> ufsi')" "y \<in> Field (ufsi_\<alpha> ufsi')"
      by simp_all
    moreover from assms(1-4,7) that have "?rep ufsi' x \<noteq> ?rep ufsi' y"
      using ufsi_rep_of_eq_if_eq_on_ufsi_rep_of by simp
    ultimately show ?thesis
      using that
      by (sep_auto simp: is_ufsi_c_def intro': eq_on_ufsi_rep_of_ufsi_union)
  qed
  from assms(1,2,7) show ?thesis
    by (sep_auto simp: is_ufsi_c_def)
qed

lemma ufsi_imp_union_size_c_is_ufsi_c_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufsi_\<alpha> ufsi)" "y \<in> Field (ufsi_\<alpha> ufsi)"
  shows
    "<is_ufsi_c ufsi ufsi_imp>
      ufsi_imp_union_size_c ufsi_imp x y
    <is_ufsi_c (ufsi_union_size ufsi x y)>"
proof -
  include ufa_ufs_transfer and Union_Find_Size_Int_Quotient.ufsi.lifting
  
  have "ufsi_union_size ufsi x y = ufsi"
    if "ufsi_rep_of ufsi x = ufsi_rep_of ufsi y"
    using assms(1,2) that
    by (transfer, transfer)
      (use ufa_union_eq_if_rep_eq ufa_union_size_def in simp)
  moreover have "ufsi_union_size ufsi x y = ufsi_union ufsi x y"
    if "ufsi_rep_of ufsi x \<noteq> ufsi_rep_of ufsi y"
      "ufsi_size ufsi (ufsi_rep_of ufsi x) < ufsi_size ufsi (ufsi_rep_of ufsi y)"
    using assms(1,2) that
    by transfer (simp add: ufs_union_size_def)
  moreover have "ufsi_union_size ufsi x y = ufsi_union ufsi y x"
    if "ufsi_rep_of ufsi x \<noteq> ufsi_rep_of ufsi y"
      "\<not> ufsi_size ufsi (ufsi_rep_of ufsi x) < ufsi_size ufsi (ufsi_rep_of ufsi y)" 
    using assms(1,2) that
    by transfer (simp add: ufs_union_size_def)
   ultimately show ?thesis
    using assms(1,2) unfolding ufsi_imp_union_size_c_def
    by sep_auto  
qed

end