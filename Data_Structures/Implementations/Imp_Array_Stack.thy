theory Imp_Array_Stack
  imports
    Data_Structures.Bounded_Stack_Specs_Imp
begin

section \<open>Bounded Stacks as Arrays\<close>

text \<open>A LIFO stack of capacity \<open>cap\<close>: an array of length \<open>cap\<close>, allocated once, holding the
      elements bottom first at the positions below the stack pointer \<open>sp\<close>. Every operation takes at
      most one array access. The functional model is the array contents together with \<open>sp\<close>.\<close>

type_synonym 'a ars = "'a list \<times> nat"

definition ars_empty :: "nat \<Rightarrow> 'a \<Rightarrow> 'a ars" where
  "ars_empty cap d = (replicate cap d, 0)"

definition ars_push :: "'a ars \<Rightarrow> 'a \<Rightarrow> 'a ars" where
  "ars_push = (\<lambda> (A, sp) x. (list_update A sp x, Suc sp))"

definition ars_pop :: "'a ars \<Rightarrow> 'a ars" where
  "ars_pop = (\<lambda> (A, sp). (A, sp - 1))"

definition ars_top :: "'a ars \<Rightarrow> 'a" where
  "ars_top = (\<lambda> (A, sp). A ! (sp - 1))"

definition ars_is_empty :: "'a ars \<Rightarrow> bool" where
  "ars_is_empty = (\<lambda> (A, sp). sp = 0)"

definition ars_invar :: "nat \<Rightarrow> 'a ars \<Rightarrow> bool" where
  "ars_invar cap = (\<lambda> (A, sp). length A = cap \<and> sp \<le> cap)"

definition ars_abstract :: "'a ars \<Rightarrow> 'a list" where
  "ars_abstract = (\<lambda> (A, sp). rev (take sp A))"

lemma ars_bounded_stack:
  "bounded_stack cap (ars_invar cap) ars_abstract (ars_empty cap d) ars_push ars_pop ars_top
     ars_is_empty"
  by unfold_locales
     (auto simp: split_paired_all ars_invar_def ars_abstract_def ars_empty_def ars_push_def ars_pop_def
       ars_top_def ars_is_empty_def take_Suc_conv_app_nth list_update_append gr0_conv_Suc)

section \<open>The Array and the Stack Pointer\<close>

type_synonym 'a arsi = "'a array \<times> nat ref"

fun ars_assn :: "'a::heap ars \<Rightarrow> 'a arsi \<Rightarrow> assn" where
  "ars_assn (A, sp) (Aa, sr) = Aa \<mapsto>\<^sub>a A * sr \<mapsto>\<^sub>r sp"

definition ars_empty_imp :: "nat \<Rightarrow> 'a::heap \<Rightarrow> 'a arsi Heap" where
  "ars_empty_imp cap d = do { Aa \<leftarrow> Array.new cap d; sr \<leftarrow> ref 0; return (Aa, sr) }"

definition ars_push_imp :: "'a::heap arsi \<Rightarrow> 'a \<Rightarrow> unit Heap" where
  "ars_push_imp = (\<lambda> (Aa, sr) x. do {
     sp \<leftarrow> !sr;
     _ \<leftarrow> Array.upd sp x Aa;
     sr := Suc sp })"

definition ars_pop_imp :: "'a::heap arsi \<Rightarrow> unit Heap" where
  "ars_pop_imp = (\<lambda> (Aa, sr). do { sp \<leftarrow> !sr; sr := sp - 1 })"

definition ars_top_imp :: "'a::heap arsi \<Rightarrow> 'a Heap" where
  "ars_top_imp = (\<lambda> (Aa, sr). do { sp \<leftarrow> !sr; Array.nth Aa (sp - 1) })"

definition ars_is_empty_imp :: "'a::heap arsi \<Rightarrow> bool Heap" where
  "ars_is_empty_imp = (\<lambda> (Aa, sr). do { sp \<leftarrow> !sr; return (sp = 0) })"

lemmas ars_imp_defs = ars_empty_imp_def ars_push_imp_def ars_pop_imp_def ars_top_imp_def
  ars_is_empty_imp_def

lemma ars_bounded_stack_imp:
  "bounded_stack_imp cap (ars_invar cap) ars_abstract (ars_empty cap d) ars_push ars_pop ars_top
     ars_is_empty ars_assn (ars_empty_imp cap d) ars_push_imp ars_pop_imp ars_top_imp
     ars_is_empty_imp"
  by (intro bounded_stack_imp.intro ars_bounded_stack bounded_stack_imp_axioms.intro)
     (sep_auto simp: split_paired_all ars_defs ars_imp_defs)+

end

