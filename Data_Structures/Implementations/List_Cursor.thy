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

lemmas lc_defs = lc_invar_def lc_iterated_def lc_remaining_def lc_abstract_def lc_has_def
  lc_current_def lc_move_def

interpretation lc: iterable_set lc_invar lc_abstract lc_current lc_has lc_iterated lc_remaining
    lc_move
  by unfold_locales
     (auto simp: lc_defs not_le set_take_disj_set_drop_if_distinct take_Suc_conv_app_nth
        Cons_nth_drop_Suc[symmetric] set_append[of "take _ _" "drop _ _", symmetric]
        in_set_conv_nth nth_eq_iff_index_eq)

end
