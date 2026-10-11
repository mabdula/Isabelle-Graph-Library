theory Fixed_Univ_List_Specs_Imp
  imports
    Separation_Logic_Imperative_HOL_Partial.Sep_Main
    Fixed_Univ_List_Specs
begin

text \<open>Imperative distinct lists over a fixed universe. Updates work in place; the only allocating
      operation is @{term list_empty_imp}, which is used during initialisation only.\<close>

locale fixed_univ_list_imp =
  fixed_univ_list where U = U
    and list_invar = list_invar
    and list_abstract = list_abstract
    and list_empty = list_empty
    and list_push_front = list_push_front
    and list_move_to_front = list_move_to_front
    and list_first = list_first
    and list_next = list_next
  for U :: "'a::heap set"
    and list_invar :: "'l \<Rightarrow> bool"
    and list_abstract :: "'l \<Rightarrow> 'a list"
    and list_empty :: "'l"
    and list_push_front :: "'l \<Rightarrow> 'a \<Rightarrow> 'l"
    and list_move_to_front :: "'l \<Rightarrow> 'a \<Rightarrow> 'l"
    and list_first :: "'l \<Rightarrow> 'a option"
    and list_next :: "'l \<Rightarrow> 'a \<Rightarrow> 'a option" +
  fixes list_assn :: "'l \<Rightarrow> 'li \<Rightarrow> assn"
    and list_empty_imp :: "'li Heap"
    and list_push_front_imp :: "'li \<Rightarrow> 'a \<Rightarrow> unit Heap"
    and list_move_to_front_imp :: "'li \<Rightarrow> 'a \<Rightarrow> unit Heap"
    and list_first_imp :: "'li \<Rightarrow> 'a option Heap"
    and list_next_imp :: "'li \<Rightarrow> 'a \<Rightarrow> 'a option Heap"
  assumes list_empty_rule[sep_heap_rules]:
      "<emp> list_empty_imp <\<lambda>Li. list_assn list_empty Li>"
    and list_push_front_rule[sep_heap_rules]:
      "\<lbrakk>list_invar L; x \<in> U; x \<notin> set (list_abstract L)\<rbrakk> \<Longrightarrow>
       <list_assn L Li> list_push_front_imp Li x
       <\<lambda>_. list_assn (list_push_front L x) Li>"
    and list_move_to_front_rule[sep_heap_rules]:
      "\<lbrakk>list_invar L; x \<in> set (list_abstract L)\<rbrakk> \<Longrightarrow>
       <list_assn L Li> list_move_to_front_imp Li x
       <\<lambda>_. list_assn (list_move_to_front L x) Li>"
    and list_first_rule[sep_heap_rules]:
      "list_invar L \<Longrightarrow>
       <list_assn L Li> list_first_imp Li
       <\<lambda>r. list_assn L Li * \<up>(r = list_first L)>"
    and list_next_rule[sep_heap_rules]:
      "\<lbrakk>list_invar L; x \<in> set (list_abstract L)\<rbrakk> \<Longrightarrow>
       <list_assn L Li> list_next_imp Li x
       <\<lambda>r. list_assn L Li * \<up>(r = list_next L x)>"

lemma (in fixed_univ_list_imp) fixed_univ_list_imp_restrict:
  assumes "U' \<subseteq> U"
  shows "fixed_univ_list_imp U' (restr_list_invar U' list_invar list_abstract) list_abstract
           list_empty list_push_front list_move_to_front list_first list_next list_assn
           list_empty_imp list_push_front_imp list_move_to_front_imp list_first_imp list_next_imp"
proof(intro fixed_univ_list_imp.intro fixed_univ_list_restrict[OF assms]
            fixed_univ_list_imp_axioms.intro, goal_cases)
  case 1 show ?case
    by (rule list_empty_rule)
next
  case (2 L x) then show ?case
    using assms by (intro list_push_front_rule) (auto simp add: restr_list_invar_def)
next
  case (3 L x) then show ?case
    by (intro list_move_to_front_rule) (simp_all add: restr_list_invar_def)
next
  case (4 L) then show ?case
    by (intro list_first_rule) (simp add: restr_list_invar_def)
next
  case (5 L x) then show ?case
    by (intro list_next_rule) (simp_all add: restr_list_invar_def)
qed

end
