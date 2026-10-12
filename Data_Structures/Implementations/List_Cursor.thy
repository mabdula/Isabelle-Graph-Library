theory List_Cursor
  imports Data_Structures.Iterable_Set_Specs
begin

section \<open>A Cursor over a List of Distinct Elements\<close>

text \<open>An immutable set, given as a list of distinct elements, together with a cursor into the
      list. The set is iterated once, in list order: only the cursor moves.\<close>

record 'a list_cursor = lc_list :: "'a list"  lc_pos :: nat

definition lc_invar :: "'a list_cursor \<Rightarrow> bool" where
  "lc_invar V \<longleftrightarrow> distinct (lc_list V) \<and> lc_pos V \<le> length (lc_list V)"
definition lc_abstract :: "'a list_cursor \<Rightarrow> 'a set" where
  "lc_abstract V = set (lc_list V)"
definition lc_iterated :: "'a list_cursor \<Rightarrow> 'a set" where
  "lc_iterated V = set (take (lc_pos V) (lc_list V))"
definition lc_remaining :: "'a list_cursor \<Rightarrow> 'a set" where
  "lc_remaining V = set (drop (lc_pos V) (lc_list V))"
definition lc_has :: "'a list_cursor \<Rightarrow> bool" where
  "lc_has V \<longleftrightarrow> lc_pos V < length (lc_list V)"
definition lc_current :: "'a list_cursor \<Rightarrow> 'a" where
  "lc_current V = lc_list V ! lc_pos V"
definition lc_move :: "'a list_cursor \<Rightarrow> 'a list_cursor" where
  "lc_move V = V\<lparr>lc_pos := Suc (lc_pos V)\<rparr>"

lemma lc_remaining_ne: "lc_remaining V \<noteq> {} \<longleftrightarrow> lc_pos V < length (lc_list V)"
  by (simp add: lc_remaining_def not_le)

interpretation lc: iterable_set lc_invar lc_abstract lc_current lc_has lc_iterated lc_remaining
    lc_move
proof (unfold_locales, goal_cases)
  case (1 V) then show ?case
    using set_take_disj_set_drop_if_distinct[of "lc_list V" "lc_pos V" "lc_pos V"]
    by (simp add: lc_invar_def lc_iterated_def lc_remaining_def)
next
  case (2 V) show ?case
    by (simp add: lc_iterated_def lc_remaining_def lc_abstract_def flip: set_append)
next
  case (3 V) show ?case by (simp add: lc_has_def lc_remaining_ne)
next
  case (4 V) then show ?case
    by (simp add: lc_current_def lc_remaining_def lc_remaining_ne Cons_nth_drop_Suc[symmetric])
next
  case (5 V) show ?case by (simp add: lc_abstract_def lc_move_def)
next
  case (6 V)
  then have j: "lc_pos V < length (lc_list V)" and d: "distinct (lc_list V)"
    by (simp_all add: lc_remaining_ne lc_invar_def)
  have "drop (lc_pos V) (lc_list V) = lc_current V # drop (Suc (lc_pos V)) (lc_list V)"
    using j by (simp add: lc_current_def Cons_nth_drop_Suc)
  moreover have "distinct (drop (lc_pos V) (lc_list V))" using d by simp
  ultimately show ?case by (simp add: lc_remaining_def lc_move_def)
next
  case (7 V) then show ?case
    by (simp add: lc_iterated_def lc_move_def lc_current_def take_Suc_conv_app_nth lc_remaining_ne)
next
  case (8 V) then show ?case by (simp add: lc_invar_def lc_move_def lc_remaining_ne)
qed

end
