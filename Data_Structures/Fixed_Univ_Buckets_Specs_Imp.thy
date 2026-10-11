theory Fixed_Univ_Buckets_Specs_Imp
  imports
    Separation_Logic_Imperative_HOL_Partial.Sep_Main
    Fixed_Univ_Buckets_Specs
begin

text \<open>Imperative buckets over a fixed universe. Updates work in place; the only allocating
      operation is @{term buckets_empty_imp}, which is used during initialisation only.\<close>

locale fixed_univ_buckets_imp =
  fixed_univ_buckets where U = U
    and K = K
    and buckets_invar = buckets_invar
    and buckets_abstract = buckets_abstract
    and buckets_empty = buckets_empty
    and buckets_insert = buckets_insert
    and buckets_remove = buckets_remove
    and buckets_pick = buckets_pick
    and buckets_move = buckets_move
  for U :: "'a::heap set"
    and K :: "'k set"
    and buckets_invar :: "'b \<Rightarrow> bool"
    and buckets_abstract :: "'b \<Rightarrow> 'a \<Rightarrow> 'k option"
    and buckets_empty :: "'b"
    and buckets_insert :: "'b \<Rightarrow> 'a \<Rightarrow> 'k \<Rightarrow> 'b"
    and buckets_remove :: "'b \<Rightarrow> 'a \<Rightarrow> 'k \<Rightarrow> 'b"
    and buckets_pick :: "'b \<Rightarrow> 'k \<Rightarrow> 'a option"
    and buckets_move :: "'b \<Rightarrow> 'k \<Rightarrow> 'k \<Rightarrow> 'b" +
  fixes buckets_assn :: "'b \<Rightarrow> 'bi \<Rightarrow> assn"
    and buckets_empty_imp :: "'bi Heap"
    and buckets_insert_imp :: "'bi \<Rightarrow> 'a \<Rightarrow> 'k \<Rightarrow> unit Heap"
    and buckets_remove_imp :: "'bi \<Rightarrow> 'a \<Rightarrow> 'k \<Rightarrow> unit Heap"
    and buckets_pick_imp :: "'bi \<Rightarrow> 'k \<Rightarrow> 'a option Heap"
    and buckets_move_imp :: "'bi \<Rightarrow> 'k \<Rightarrow> 'k \<Rightarrow> unit Heap"
  assumes buckets_empty_rule[sep_heap_rules]:
      "<emp> buckets_empty_imp <\<lambda>Bi. buckets_assn buckets_empty Bi>"
    and buckets_insert_rule[sep_heap_rules]:
      "\<lbrakk>buckets_invar B; x \<in> U; k \<in> K; buckets_abstract B x = None\<rbrakk> \<Longrightarrow>
       <buckets_assn B Bi> buckets_insert_imp Bi x k
       <\<lambda>_. buckets_assn (buckets_insert B x k) Bi>"
    and buckets_remove_rule[sep_heap_rules]:
      "\<lbrakk>buckets_invar B; buckets_abstract B x = Some k\<rbrakk> \<Longrightarrow>
       <buckets_assn B Bi> buckets_remove_imp Bi x k
       <\<lambda>_. buckets_assn (buckets_remove B x k) Bi>"
    and buckets_pick_rule[sep_heap_rules]:
      "\<lbrakk>buckets_invar B; k \<in> K\<rbrakk> \<Longrightarrow>
       <buckets_assn B Bi> buckets_pick_imp Bi k
       <\<lambda>r. buckets_assn B Bi * \<up>(r = buckets_pick B k)>"
    and buckets_move_rule[sep_heap_rules]:
      "\<lbrakk>buckets_invar B; j \<in> K; j' \<in> K; j \<noteq> j'\<rbrakk> \<Longrightarrow>
       <buckets_assn B Bi> buckets_move_imp Bi j j'
       <\<lambda>_. buckets_assn (buckets_move B j j') Bi>"

lemma (in fixed_univ_buckets_imp) fixed_univ_buckets_imp_restrict:
  assumes "U' \<subseteq> U"
  shows "fixed_univ_buckets_imp U' K (restr_buckets_invar U' buckets_invar buckets_abstract)
           buckets_abstract buckets_empty buckets_insert buckets_remove buckets_pick buckets_move
           buckets_assn buckets_empty_imp buckets_insert_imp buckets_remove_imp buckets_pick_imp
           buckets_move_imp"
proof(intro fixed_univ_buckets_imp.intro fixed_univ_buckets_restrict[OF assms]
            fixed_univ_buckets_imp_axioms.intro, goal_cases)
  case 1 show ?case
    by (rule buckets_empty_rule)
next
  case (2 B x k) then show ?case
    using assms by (intro buckets_insert_rule) (auto simp add: restr_buckets_invar_def)
next
  case (3 B x k) then show ?case
    by (intro buckets_remove_rule) (simp_all add: restr_buckets_invar_def)
next
  case (4 B k) then show ?case
    by (intro buckets_pick_rule) (simp_all add: restr_buckets_invar_def)
next
  case (5 B j j') then show ?case
    by (intro buckets_move_rule) (simp_all add: restr_buckets_invar_def)
qed

end
