theory Fixed_Univ_List_Specs
  imports
    Main
begin

section \<open>Distinct Lists over a Fixed Universe\<close>

text \<open>A distinct list of elements of a fixed universe @{term U}, with a cursor-free traversal
      (first element, successor of an element) and move-to-front. An implementation may be a
      doubly-linked list in two arrays (successor and predecessor) over @{term U}, allocated once.\<close>

locale fixed_univ_list =
  fixes U :: "'a set"
  and list_invar :: "'l \<Rightarrow> bool"
  and list_abstract :: "'l \<Rightarrow> 'a list"
  and list_empty :: "'l"
  and list_push_front :: "'l \<Rightarrow> 'a \<Rightarrow> 'l"
  and list_move_to_front :: "'l \<Rightarrow> 'a \<Rightarrow> 'l"
  and list_first :: "'l \<Rightarrow> 'a option"
  and list_next :: "'l \<Rightarrow> 'a \<Rightarrow> 'a option"
  assumes list_universe:
      "\<And> L. list_invar L \<Longrightarrow> distinct (list_abstract L) \<and> set (list_abstract L) \<subseteq> U"
  and list_empty:
      "list_invar list_empty"
      "list_abstract list_empty = []"
  and list_push_front:
      "\<And> L x. \<lbrakk>list_invar L; x \<in> U; x \<notin> set (list_abstract L)\<rbrakk> \<Longrightarrow>
          list_invar (list_push_front L x)"
      "\<And> L x. \<lbrakk>list_invar L; x \<in> U; x \<notin> set (list_abstract L)\<rbrakk> \<Longrightarrow>
          list_abstract (list_push_front L x) = x # list_abstract L"
  and list_move_to_front:
      "\<And> L x. \<lbrakk>list_invar L; x \<in> set (list_abstract L)\<rbrakk> \<Longrightarrow> list_invar (list_move_to_front L x)"
      "\<And> L x. \<lbrakk>list_invar L; x \<in> set (list_abstract L)\<rbrakk> \<Longrightarrow>
          list_abstract (list_move_to_front L x) = x # remove1 x (list_abstract L)"
  and list_first:
      "\<And> L. list_invar L \<Longrightarrow> list_first L = (case list_abstract L of [] \<Rightarrow> None | x # _ \<Rightarrow> Some x)"
  and list_next:
      "\<And> L xs x ys. \<lbrakk>list_invar L; list_abstract L = xs @ x # ys\<rbrakk> \<Longrightarrow>
          list_next L x = (case ys of [] \<Rightarrow> None | y # _ \<Rightarrow> Some y)"

text \<open>Restricting the elements to a smaller universe @{term U'}: the invariant additionally
      requires that only elements of @{term U'} lie in the list.\<close>

definition "restr_list_invar U' list_invar list_abstract L =
  (list_invar L \<and> set (list_abstract L) \<subseteq> U')"

lemma (in fixed_univ_list) fixed_univ_list_restrict:
  assumes "U' \<subseteq> U"
  shows "fixed_univ_list U' (restr_list_invar U' list_invar list_abstract) list_abstract list_empty
           list_push_front list_move_to_front list_first list_next"
proof(unfold_locales, goal_cases)
  case (1 L) then show ?case
    using list_universe by (simp add: restr_list_invar_def)
next
  case 2 show ?case
    using list_empty by (simp add: restr_list_invar_def)
next
  case 3 show ?case
    using list_empty by simp
next
  case (4 L x)
  have "x \<in> U" "list_invar L"
    using 4 assms by (auto simp add: restr_list_invar_def)
  then show ?case
    using 4 list_push_front[of L x] by (auto simp add: restr_list_invar_def)
next
  case (5 L x)
  have "x \<in> U" "list_invar L"
    using 5 assms by (auto simp add: restr_list_invar_def)
  then show ?case
    using 5 list_push_front(2)[of L x] by simp
next
  case (6 L x) then show ?case
    using list_move_to_front[of L x] set_remove1_subset[of x "list_abstract L"]
    by (auto simp add: restr_list_invar_def)
next
  case (7 L x) then show ?case
    using list_move_to_front(2)[of L x] by (simp add: restr_list_invar_def)
next
  case (8 L) then show ?case
    using list_first[of L] by (simp add: restr_list_invar_def)
next
  case (9 L xs x ys) then show ?case
    using list_next[of L xs x ys] by (simp add: restr_list_invar_def)
qed

end
