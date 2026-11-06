theory List_Cursor_Imperative
  imports List_Cursor Data_Structures.Iterable_Set_Specs_Imp
begin

section \<open>The List Cursor in the Heap\<close>

text \<open>The list is stored in an array, which is only read, and the cursor in a reference.\<close>

type_synonym 'a list_cursor_imp = "'a array \<times> nat ref"

definition lc_assn :: "'a::heap list_cursor \<Rightarrow> 'a list_cursor_imp \<Rightarrow> assn" where
  "lc_assn V = (\<lambda>(Sa, r). Sa \<mapsto>\<^sub>a lc_list V * r \<mapsto>\<^sub>r lc_pos V)"

definition lc_has_imp :: "'a::heap list_cursor_imp \<Rightarrow> bool Heap" where
  "lc_has_imp = (\<lambda>(Sa, r). do { j \<leftarrow> !r; l \<leftarrow> Array.len Sa; return (j < l) })"

definition lc_current_imp :: "'a::heap list_cursor_imp \<Rightarrow> 'a Heap" where
  "lc_current_imp = (\<lambda>(Sa, r). do { j \<leftarrow> !r; Array.nth Sa j })"

definition lc_move_imp :: "'a::heap list_cursor_imp \<Rightarrow> unit Heap" where
  "lc_move_imp = (\<lambda>(Sa, r). do { j \<leftarrow> !r; Ref.update r (Suc j) })"

interpretation lc: iterable_set_imp lc_invar lc_abstract lc_current lc_has lc_iterated
    lc_remaining lc_move lc_assn lc_current_imp lc_has_imp lc_move_imp
  by unfold_locales
     (sep_auto simp: lc_assn_def lc_current_imp_def lc_current_def lc_remaining_ne lc_has_imp_def
        lc_has_def lc_move_imp_def lc_move_def split: prod.splits)+

end
