(* Source: Stevens & Ghidini (2025),
   https://doi.org/10.5281/zenodo.15557955
   License: CC-BY 4.0 (https://creativecommons.org/licenses/by/4.0/)
   No modifications made. *)

theory Union_Find
  imports Collections.Partial_Equivalence_Relation
begin

lemma Field_per_union[simp]:
  "Field (per_union r x y) = Field r"
  unfolding Field_def per_union_def by blast

lemma mono_per_union[simp]:
  assumes "p \<in> r"
  shows "p \<in> per_union r x y"
  using assms unfolding per_union_def by simp

function (domintros) rep_of 
  where "rep_of uf i = (let pi = uf ! i in if pi = i then i else rep_of uf pi)"
  by pat_completeness auto

definition "ufa_invar uf \<equiv> \<forall>i < length uf. rep_of_dom (uf, i) \<and> uf ! i < length uf"

lemma ufa_invarD:
  assumes "ufa_invar uf"
  assumes "i < length uf"
  shows "rep_of_dom (uf, i)" "uf ! i < length uf"
  using assms unfolding ufa_invar_def by blast+

typedef ufa = "{uf. ufa_invar uf}"
proof -
  have "ufa_invar []"
    unfolding ufa_invar_def by simp
  then show ?thesis
    by blast
qed

setup_lifting type_definition_ufa

context
begin

qualified definition "\<alpha> uf \<equiv> {(x, y). x < length uf \<and> y < length uf \<and> rep_of uf x = rep_of uf y}"

lemma Field_\<alpha>[simp]: "x \<in> Field (\<alpha> uf) \<longleftrightarrow> x < length uf"
  unfolding \<alpha>_def Field_iff by blast

lemma in_\<alpha>I[intro]:
  assumes "x < length uf" "y < length uf" "rep_of uf x = rep_of uf y"
  shows "(x, y) \<in> \<alpha> uf"
  using assms unfolding \<alpha>_def by blast

lemma in_\<alpha>E[elim]:
  assumes "(x, y) \<in> \<alpha> uf"
  obtains "x < length uf" "y < length uf" "rep_of uf x = rep_of uf y"
  using assms unfolding \<alpha>_def by blast+

lemma rep_of_lt_lengthI[simp, intro]:
  assumes "ufa_invar uf" "x < length uf"
  shows "rep_of uf x < length uf"
  using ufa_invarD(1)[OF assms] assms
  by (induction rule: rep_of.pinduct) (auto simp: rep_of.psimps Let_def ufa_invarD(2))

lemma nth_rep_of_eq_rep_of:
  assumes "ufa_invar uf" "x < length uf"
  shows "uf ! rep_of uf x = rep_of uf x"
  using ufa_invarD(1)[OF assms] assms
  by (induction rule: rep_of.pinduct) (auto simp: rep_of.psimps Let_def ufa_invarD(2))

lemma rep_of_dom_list_update_rep_of:
  assumes "ufa_invar uf" "x < length uf" "y < length uf"
  assumes "i < length uf"
  shows "rep_of_dom (uf[x := rep_of uf y], i)"
proof -
  from assms have "rep_of_dom (uf, i)"
    using ufa_invarD by simp
  then show ?thesis
    using assms
  proof(induction rule: rep_of.pinduct)
    case (1 uf i)
    note [intro!] =
      rep_of.domintros[where i=i]
      rep_of.domintros[where i="rep_of uf y" for uf]
    from 1 show ?case
      using nth_list_update[OF \<open>x < length uf\<close>]
      using nth_rep_of_eq_rep_of
      by (auto dest: ufa_invarD simp: ufa_invarD(2))
  qed
qed

lemma ufa_invar_list_update_rep_of:
  assumes "ufa_invar uf"
  assumes "x < length uf" "y < length uf"
  shows "ufa_invar (uf[x := rep_of uf y])"
proof -
  from assms have "rep_of uf y < length uf"
    by blast+
  with rep_of_dom_list_update_rep_of show ?thesis
    using assms unfolding ufa_invar_def by (auto simp: nth_list_update)
qed

lemma ufa_invar_list_update:
  assumes "ufa_invar uf"
  assumes "x < length uf" "y < length uf"
  assumes "uf ! y = y"
  shows "ufa_invar (uf[x := y])"
proof -
  from assms have "rep_of uf y = y"
    by (simp add: ufa_invarD rep_of.psimps)
  with ufa_invar_list_update_rep_of[OF assms(1-3)] show ?thesis
    by simp
qed

end

lift_definition ufa_\<alpha> :: "ufa \<Rightarrow> nat rel" is Union_Find.\<alpha> .

lift_definition ufa_parent_of :: "ufa \<Rightarrow> nat \<Rightarrow> nat" is "\<lambda>uf i. uf ! i" .

lift_definition ufa_rep_of :: "ufa \<Rightarrow> nat \<Rightarrow> nat" is rep_of .

lemma part_equiv_ufa_\<alpha>: "part_equiv (ufa_\<alpha> uf)"
  by (transfer, rule part_equivI) (auto simp: Union_Find.\<alpha>_def intro: symI transI)

lemma equiv_Field_ufa_\<alpha>_ufa_\<alpha>:
  "equiv (Field (ufa_\<alpha> uf)) (ufa_\<alpha> uf)"
  by (transfer, rule equivI) (auto simp: Union_Find.\<alpha>_def Field_iff refl_on_def intro: symI transI)

lemma finite_Field_ufa_\<alpha>: "finite (Field (ufa_\<alpha> uf))"
  by transfer (meson Field_\<alpha> bounded_nat_set_is_finite)

lemma ufa_\<alpha>I:
  assumes "x \<in> Field (ufa_\<alpha> uf)" "y \<in> Field (ufa_\<alpha> uf)" "ufa_rep_of uf x = ufa_rep_of uf y"
  shows "(x, y) \<in> ufa_\<alpha> uf"
  using assms
  by transfer auto

lemma ufa_rep_of_eq_if_in_ufa_\<alpha>:
  assumes "(x, y) \<in> ufa_\<alpha> uf"
  shows "ufa_rep_of uf x = ufa_rep_of uf y"
  using assms by transfer blast

lemma ufa_parent_of_in_Field_ufa_\<alpha>I[simp, intro]:
  assumes "i \<in> Field (ufa_\<alpha> uf)"
  shows "ufa_parent_of uf i \<in> Field (ufa_\<alpha> uf)"
  using assms by transfer (auto simp: ufa_invar_def)

lemma ufa_rep_of_simp:
  assumes "i \<in> Field (ufa_\<alpha> uf)"
  shows "ufa_rep_of uf i = (let pi = ufa_parent_of uf i in if pi = i then i else ufa_rep_of uf pi)"
  using assms unfolding Let_def
  by (transfer, subst rep_of.psimps)(simp_all add: ufa_invarD)

lemma ufa_rep_of_if_refl_ufa_parent_of:
  "ufa_parent_of uf i = i \<Longrightarrow> ufa_rep_of uf i = i"
  by transfer (simp add: rep_of.domintros rep_of.psimps)

lemma ufa_rep_of_refl_iff_ufa_parent_of_refl:
  assumes "i \<in> Field (ufa_\<alpha> uf)"
  shows "ufa_parent_of uf i = i \<longleftrightarrow> ufa_rep_of uf i = i"
  using assms nth_rep_of_eq_rep_of
  by transfer (force simp: rep_of.domintros rep_of.psimps)
  
lemma ufa_rep_of_if_irrefl_ufa_parent_of:
  assumes "i \<in> Field (ufa_\<alpha> uf)"
  assumes "ufa_parent_of uf i \<noteq> i"
  shows "ufa_rep_of uf i = ufa_rep_of uf (ufa_parent_of uf i)"
  using assms
  by transfer (auto simp: rep_of.psimps dest: ufa_invarD(1))

lemmas ufa_rep_of_simps = ufa_rep_of_if_refl_ufa_parent_of ufa_rep_of_if_irrefl_ufa_parent_of

lemma ufa_rep_of_induct[case_names rep not_rep, consumes 1]:
  assumes "i \<in> Field (ufa_\<alpha> uf)"
  assumes rep: "\<And>i. \<lbrakk> i \<in> Field (ufa_\<alpha> uf); ufa_parent_of uf i = i \<rbrakk> \<Longrightarrow> P uf i"
  assumes not_rep:
    "\<And>i. \<lbrakk> i \<in> Field (ufa_\<alpha> uf); ufa_parent_of uf i \<noteq> i; P uf (ufa_parent_of uf i) \<rbrakk>
    \<Longrightarrow> P uf i"
  shows "P uf i"
proof -
  define uf' where "uf' \<equiv> Rep_ufa uf"
  have "ufa_invar uf'"
    unfolding uf'_def using Rep_ufa by auto
  from assms(1) have "i < length uf'"
    unfolding uf'_def ufa_\<alpha>.rep_eq by simp

  note ufa_invarD[OF \<open>ufa_invar uf'\<close> \<open>i < length uf'\<close>]
  then have "P uf i"
    using uf'_def using \<open>ufa_invar uf'\<close> \<open>i < length uf'\<close>
  proof (induction uf\<equiv>uf' i rule: rep_of.pinduct)
    case (1 i)
    with rep not_rep show ?case
      by transfer (auto dest: ufa_invarD(2))
  qed

  with \<open>i \<in> Field (ufa_\<alpha> uf)\<close> show ?thesis
    using uf'_def by simp
qed

lemma ufa_rep_of_in_Field_ufa_\<alpha>I[simp, intro!]:
  assumes "x \<in> Field (ufa_\<alpha> uf)"
  shows "ufa_rep_of uf x \<in> Field (ufa_\<alpha> uf)"
  using assms
  by (induction rule: ufa_rep_of_induct) (auto simp: ufa_rep_of_simps)

lemma ufa_parent_of_ufa_rep_of[simp]:
  assumes "i \<in> Field (ufa_\<alpha> uf)"
  shows "ufa_parent_of uf (ufa_rep_of uf i) = ufa_rep_of uf i"
  using assms nth_rep_of_eq_rep_of by transfer simp

lemma ufa_rep_of_ufa_rep_of[simp]:
  assumes "i \<in> Field (ufa_\<alpha> uf)"
  shows "ufa_rep_of uf (ufa_rep_of uf i) = ufa_rep_of uf i"
  using assms by (auto simp: ufa_rep_of_simps)

lemma ufa_rep_of_ufa_parent_of[simp]:
  assumes "i \<in> Field (ufa_\<alpha> uf)"
  shows "ufa_rep_of uf (ufa_parent_of uf i) = ufa_rep_of uf i"
  using assms by (metis ufa_rep_of_if_irrefl_ufa_parent_of)

lemma ufa_rep_of_eq_iff_in_ufa_\<alpha>:
  assumes "x \<in> Field (ufa_\<alpha> uf)" "y \<in> Field (ufa_\<alpha> uf)"
  shows "ufa_rep_of uf x = ufa_rep_of uf y \<longleftrightarrow> (x, y) \<in> ufa_\<alpha> uf"
  using assms ufa_rep_of_eq_if_in_ufa_\<alpha> ufa_\<alpha>I by blast

lift_definition ufa_init :: "nat \<Rightarrow> ufa" is "\<lambda>n. [0..<n]"
  by (auto simp: ufa_invar_def intro: rep_of.domintros)

lemma Field_ufa_\<alpha>_ufa_init[simp]: "Field (ufa_\<alpha> (ufa_init n)) = {0..<n}"
  by transfer auto

lemma ufa_parent_of_ufa_init[simp]:
  assumes "i \<in> Field (ufa_\<alpha> (ufa_init n))"
  shows "ufa_parent_of (ufa_init n) i = i"
  using assms by transfer simp

lemma rep_of_upt:
  assumes "i < n"
  shows "rep_of [0..<n] i = i"
  using assms rep_of.domintros rep_of.psimps by fastforce

lemma ufa_\<alpha>_ufa_init: "ufa_\<alpha> (ufa_init n) = {(x, x) |x. x < n}"
  by transfer (auto simp: Union_Find.\<alpha>_def rep_of_upt)

lift_definition ufa_union :: "ufa \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ufa" is
  "\<lambda>uf x y. if x < length uf \<and> y < length uf then uf[rep_of uf x := rep_of uf y] else uf"
  using ufa_invar_list_update_rep_of by auto

lemma ufa_union_eq_if_not_in_Field_ufa_\<alpha>[simp]:
  assumes "x \<notin> Field (ufa_\<alpha> uf) \<or> y \<notin> Field (ufa_\<alpha> uf)"
  shows "ufa_union uf x y = uf"
  using assms by transfer auto

lemma ufa_union_eq_if_rep_eq[simp]:
  assumes "x \<in> Field (ufa_\<alpha> uf)" "y \<in> Field (ufa_\<alpha> uf)"
  assumes "ufa_rep_of uf x = ufa_rep_of uf y"
  shows "ufa_union uf x y = uf"
  using assms
  by transfer (auto simp: nth_rep_of_eq_rep_of list_update_same_conv)

lemma Field_ufa_\<alpha>_ufa_union[simp]:
  "Field (ufa_\<alpha> (ufa_union uf x y)) = Field (ufa_\<alpha> uf)"
  by transfer auto

lemma ufa_parent_of_ufa_union:
  assumes "x \<in> Field (ufa_\<alpha> uf)" "y \<in> Field (ufa_\<alpha> uf)" "z \<in> Field (ufa_\<alpha> uf)"
  shows "ufa_parent_of (ufa_union uf x y) z =
    (if z = ufa_rep_of uf x then ufa_rep_of uf y else ufa_parent_of uf z)"
  using assms
  by transfer auto

lemma ufa_rep_of_ufa_union_ufa_rep_of[simp]:
  assumes "x \<in> Field (ufa_\<alpha> uf)" "y \<in> Field (ufa_\<alpha> uf)"
  shows "ufa_rep_of (ufa_union uf x y) (ufa_rep_of uf x) = ufa_rep_of uf y"
  using assms
proof -
  have "ufa_rep_of (ufa_union uf x y) (ufa_rep_of uf x) =
    ufa_rep_of (ufa_union uf x y) (ufa_parent_of (ufa_union uf x y) (ufa_rep_of uf x))"
    using assms by auto
  also have "\<dots> = ufa_rep_of (ufa_union uf x y) (ufa_rep_of uf y)"
    using assms ufa_parent_of_ufa_union by simp
  also have "\<dots> = ufa_rep_of uf y"
    using assms by (auto simp: ufa_parent_of_ufa_union ufa_rep_of_if_refl_ufa_parent_of)
  finally show ?thesis .
qed

lemma ufa_rep_of_ufa_union:
  assumes "x \<in> Field (ufa_\<alpha> uf)" "y \<in> Field (ufa_\<alpha> uf)"
  assumes "i \<in> Field (ufa_\<alpha> uf)"
  shows "ufa_rep_of (ufa_union uf x y) i =
    (if ufa_rep_of uf i = ufa_rep_of uf x then ufa_rep_of uf y else ufa_rep_of uf i)"
  using \<open>i \<in> Field (ufa_\<alpha> uf)\<close>
proof(induction rule: ufa_rep_of_induct)
  case (rep i)
  then have "ufa_rep_of uf i = i"
    by (simp add: ufa_rep_of_if_refl_ufa_parent_of)
  show ?case
  proof(cases "i = ufa_rep_of uf x")
    case True
    with rep assms(1,2) ufa_rep_of_ufa_union_ufa_rep_of show ?thesis
      by simp
  next
    case False
    with assms(1,2) rep have "ufa_rep_of (ufa_union uf x y) i = ufa_rep_of uf i"
      by (simp add: ufa_parent_of_ufa_union ufa_rep_of_if_refl_ufa_parent_of)
    with False \<open>ufa_rep_of uf i = i\<close> show ?thesis
      by (simp add: ufa_rep_of_if_refl_ufa_parent_of)
  qed
next
  case (not_rep i)
  with assms(1,2) have "ufa_parent_of (ufa_union uf x y) i = ufa_parent_of uf i"
    using ufa_parent_of_ufa_union by auto
  with assms(1,2) not_rep show ?case
    by (subst ufa_rep_of_if_irrefl_ufa_parent_of) auto
qed

lemma ufa_union_ufa_rep_of_left[simp]:
  assumes "x \<in> Field (ufa_\<alpha> ufa)" "y \<in> Field (ufa_\<alpha> ufa)"
  shows "ufa_union ufa (ufa_rep_of ufa x) y = ufa_union ufa x y"
  using assms nth_rep_of_eq_rep_of including ufa.lifting
  by transfer (use rep_of.psimps rep_of_lt_lengthI ufa_invarD(1) in force)

lemma ufa_union_ufa_rep_of_right[simp]:
  assumes "x \<in> Field (ufa_\<alpha> ufa)" "y \<in> Field (ufa_\<alpha> ufa)"
  shows "ufa_union ufa x (ufa_rep_of ufa y) = ufa_union ufa x y"
  using assms nth_rep_of_eq_rep_of including ufa.lifting
  by transfer (use rep_of.psimps rep_of_lt_lengthI ufa_invarD(1) in force)

lemma ufa_\<alpha>_ufa_union_eq_per_union_ufa_\<alpha>[simp]:
  "ufa_\<alpha> (ufa_union uf x y) = per_union (ufa_\<alpha> uf) x y"
  unfolding per_union_def
  using ufa_rep_of_ufa_union
  by transfer (auto elim!: in_\<alpha>E intro!: in_\<alpha>I split: if_splits)

lift_definition ufa_compress :: "ufa \<Rightarrow> nat \<Rightarrow> ufa" is 
  "\<lambda>uf x. if x < length uf then uf[x := rep_of uf x] else uf"
  by (auto intro!: ufa_invar_list_update_rep_of)
    
lemma Field_ufa_\<alpha>_ufa_compress[simp]:
  "Field (ufa_\<alpha> (ufa_compress uf x)) = Field (ufa_\<alpha> uf)"
  by transfer auto

lemma ufa_parent_of_ufa_compress:
  assumes "x \<in> Field (ufa_\<alpha> uf)"
  assumes "i \<in> Field (ufa_\<alpha> uf)"
  shows "ufa_parent_of (ufa_compress uf x) i =
    (if i = x then ufa_rep_of uf x else ufa_parent_of uf i)"
  using assms by transfer auto

lemma ufa_rep_of_ufa_compress_if_in_Field_ufa_\<alpha>:
  assumes "x \<in> Field (ufa_\<alpha> uf)"
  assumes "i \<in> Field (ufa_\<alpha> uf)"
  shows "ufa_rep_of (ufa_compress uf x) i = ufa_rep_of uf i"
  using assms(2,1)
proof(induction rule: ufa_rep_of_induct)
  case (rep i)
  then have "ufa_parent_of (ufa_compress uf x) i = i"
    by (auto simp: ufa_parent_of_ufa_compress ufa_rep_of_simps)
  with rep show ?case
    by (simp add: ufa_rep_of_if_refl_ufa_parent_of)
next
  case (not_rep i)
  then have "ufa_parent_of (ufa_compress uf x) i \<noteq> i"
    by (metis ufa_parent_of_ufa_rep_of ufa_parent_of_ufa_compress)
  from not_rep have "ufa_rep_of (ufa_compress uf x) i =
    ufa_rep_of (ufa_compress uf x) (ufa_parent_of (ufa_compress uf x) i)"
    by simp
  also from not_rep have "\<dots> = ufa_rep_of (ufa_compress uf x) (ufa_parent_of uf i)"
    by (simp add: ufa_parent_of_ufa_compress ufa_rep_of_if_refl_ufa_parent_of)
  also from not_rep have "\<dots> = ufa_rep_of uf (ufa_parent_of uf i)"
    by blast
  also from not_rep have "\<dots> = ufa_rep_of uf i"
    by simp
  finally show ?case .
qed

lemma ufa_\<alpha>_ufa_compress[simp]:
  "ufa_\<alpha> (ufa_compress uf x) = ufa_\<alpha> uf"
  using ufa_rep_of_ufa_compress_if_in_Field_ufa_\<alpha>
  by transfer (auto intro!: in_\<alpha>I)

lemma ufa_rep_of_ufa_compress[simp]:
  assumes "i \<in> Field (ufa_\<alpha> uf)"
  shows "ufa_rep_of (ufa_compress uf x) i = ufa_rep_of uf i"
  using assms ufa_rep_of_ufa_compress_if_in_Field_ufa_\<alpha>
  by (simp_all add: ufa_\<alpha>.rep_eq ufa_compress.rep_eq ufa_rep_of.rep_eq)

lemma ufa_compress_ufa_rep_of_eq[simp]:
  assumes "x \<in> Field (ufa_\<alpha> uf)"
  shows "ufa_compress uf (ufa_rep_of uf x) = uf"
proof -
  from assms have "ufa_rep_of uf (ufa_rep_of uf x) = ufa_rep_of uf x"
    by simp
  with assms show ?thesis
    by transfer (simp add: list_update_same_conv nth_rep_of_eq_rep_of)
qed

definition "ufa_eq_class uf i \<equiv> ufa_\<alpha> uf `` {i}"

definition "ufa_size uf i \<equiv> card (ufa_eq_class uf i)"

lemma ufa_eq_class_transfer[transfer_rule]:
  includes lifting_syntax
  shows "(pcr_ufa ===> (=) ===> (=)) (\<lambda>uf x. Union_Find.\<alpha> uf `` {x}) ufa_eq_class"
  unfolding ufa_eq_class_def
  using rel_funD ufa_\<alpha>.transfer by fastforce

lemma ufa_size_transfer[transfer_rule]:
  includes lifting_syntax
  shows "(pcr_ufa ===> (=) ===> (=)) (\<lambda>uf x. card (Union_Find.\<alpha> uf `` {x})) ufa_size"
  unfolding ufa_size_def using ufa_eq_class_transfer
  by (intro rel_funI) (metis (mono_tags, lifting) rel_funD)

lemma ufa_eq_class_ufa_init:
  "ufa_eq_class (ufa_init n) i = (if i < n then {i} else {})"
  unfolding ufa_eq_class_def ufa_\<alpha>_ufa_init by auto

lemma ufa_size_ufa_init:
  "ufa_size (ufa_init n) i = (if i < n then 1 else 0)"
  unfolding ufa_size_def ufa_eq_class_ufa_init by simp

lemma finite_ufa_eq_class[simp, intro!]:
  "finite (ufa_eq_class uf i)"
  unfolding ufa_eq_class_def
  by transfer (auto simp: Union_Find.\<alpha>_def)

lemma ufa_size_neq_0:
  assumes "x \<in> Field (ufa_\<alpha> uf)"
  shows "ufa_size uf x \<noteq> 0"
  using assms finite_ufa_eq_class
  by transfer auto

lemma ufa_size_ufa_compress[simp]:
  "ufa_size (ufa_compress uf x) = ufa_size uf"
  unfolding ufa_size_def ufa_eq_class_def by simp

lemma ufa_eq_class_ufa_rep_of[simp]:
  assumes "x \<in> Field (ufa_\<alpha> uf)"
  shows "ufa_eq_class uf (ufa_rep_of uf x) = ufa_eq_class uf x"
  using assms unfolding ufa_eq_class_def
  by (intro equiv_class_eq[OF equiv_Field_ufa_\<alpha>_ufa_\<alpha>] ufa_\<alpha>I) auto

lemma disjoint_ufa_eq_class_if_ufa_rep_of_neq:
  assumes "ufa_rep_of uf x \<noteq> ufa_rep_of uf y"
  shows "ufa_eq_class uf x \<inter> ufa_eq_class uf y = {}"
  using assms ufa_rep_of_eq_if_in_ufa_\<alpha>
  unfolding ufa_eq_class_def by force

lemma self_in_ufa_eq_class[simp, intro]:
  assumes "x \<in> Field (ufa_\<alpha> uf)"
  shows "x \<in> ufa_eq_class uf x"
  using assms ufa_\<alpha>I unfolding ufa_eq_class_def by force

lemma ufa_size_ufa_rep_of[simp]:
  assumes "x \<in> Field (ufa_\<alpha> uf)"
  shows "ufa_size uf (ufa_rep_of uf x) = ufa_size uf x"
  using assms unfolding ufa_size_def by simp

lemma ufa_eq_class_ufa_union:
  assumes "x \<in> Field (ufa_\<alpha> uf)" "y \<in> Field (ufa_\<alpha> uf)"
  shows "ufa_eq_class (ufa_union uf x y) i =
    (if i \<in> ufa_eq_class uf x \<or> i \<in> ufa_eq_class uf y then ufa_eq_class uf x \<union> ufa_eq_class uf y
    else ufa_eq_class uf i)"
  unfolding ufa_eq_class_def ufa_\<alpha>_ufa_union_eq_per_union_ufa_\<alpha> per_union_def
  using part_equiv_ufa_\<alpha> by (auto dest: part_equiv_sym part_equiv_trans)

lemma ufa_size_ufa_union_if_ufa_rep_of_neq:
  assumes "ufa_rep_of uf x \<noteq> ufa_rep_of uf y"
  assumes "x \<in> Field (ufa_\<alpha> uf)" "y \<in> Field (ufa_\<alpha> uf)"
  assumes "i \<in> Field (ufa_\<alpha> uf)"
  shows "ufa_size (ufa_union uf x y) i =
    (if ufa_rep_of uf i = ufa_rep_of uf x \<or> ufa_rep_of uf i = ufa_rep_of uf y
      then ufa_size uf x + ufa_size uf y
    else ufa_size uf i)"
proof(cases "ufa_rep_of uf i = ufa_rep_of uf x \<or> ufa_rep_of uf i = ufa_rep_of uf y")
  case True
  with assms have "i \<in> ufa_eq_class uf x \<or> i \<in> ufa_eq_class uf y"
    by (auto intro: ufa_\<alpha>I simp: ufa_eq_class_def)
  with assms True show ?thesis
    using disjoint_ufa_eq_class_if_ufa_rep_of_neq[OF assms(1)]
    unfolding ufa_size_def
    by (auto simp: ufa_eq_class_ufa_union card_Un_disjoint)
next
  case False
  with assms have "i \<notin> ufa_eq_class uf x" "i \<notin> ufa_eq_class uf y"
    using ufa_rep_of_eq_if_in_ufa_\<alpha>
    by (auto intro: ufa_\<alpha>I simp: ufa_eq_class_def)
  with assms False show ?thesis
    unfolding ufa_size_def by (auto simp: ufa_eq_class_ufa_union)
qed

definition "ufa_union_size ufa x y \<equiv>
  let
    rep_x = ufa_rep_of ufa x;
    rep_y = ufa_rep_of ufa y
  in
    if ufa_size ufa rep_x < ufa_size ufa rep_y then ufa_union ufa x y
    else ufa_union ufa y x"


lifting_update ufa.lifting
lifting_forget ufa.lifting

end