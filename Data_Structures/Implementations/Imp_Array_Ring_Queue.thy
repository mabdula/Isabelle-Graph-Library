theory Imp_Array_Ring_Queue
  imports
    Imp_Array_Fun
    Bounded_Queue_Specs_Imp
    More_Arith
begin

section \<open>Bounded Queues as Ring Buffers\<close>

text \<open>A FIFO queue of capacity \<open>cap\<close>: an array of length \<open>cap\<close>, allocated once, holding the
      elements from position \<open>h\<close> on, cyclically, and the number \<open>sz\<close> of elements. Pushing and
      popping take a constant number of array accesses; positions wrap around by one subtraction.
      The functional model is the array as a function together with \<open>h\<close> and \<open>sz\<close>.\<close>

type_synonym 'a arq = "(nat \<Rightarrow> 'a) \<times> nat \<times> nat"

definition wrap :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "wrap cap i = (if i < cap then i else i - cap)"

lemma wrap_mod: "i < 2 * cap \<Longrightarrow> wrap cap i = i mod cap"
  by (cases "i < cap") (simp_all add: wrap_def le_mod_geq)

definition arq_empty :: "'a \<Rightarrow> 'a arq" where
  "arq_empty d = ((\<lambda> _. d), 0, 0)"

definition arq_push :: "nat \<Rightarrow> 'a arq \<Rightarrow> 'a \<Rightarrow> 'a arq" where
  "arq_push cap = (\<lambda> (A, h, sz) x. (A(wrap cap (h + sz) := x), h, Suc sz))"

definition arq_pop :: "nat \<Rightarrow> 'a arq \<Rightarrow> 'a \<times> 'a arq" where
  "arq_pop cap = (\<lambda> (A, h, sz). (A h, (A, wrap cap (Suc h), sz - 1)))"

definition arq_is_empty :: "'a arq \<Rightarrow> bool" where
  "arq_is_empty = (\<lambda> (A, h, sz). sz = 0)"

definition arq_invar :: "nat \<Rightarrow> 'a arq \<Rightarrow> bool" where
  "arq_invar cap = (\<lambda> (A, h, sz). sz \<le> cap \<and> (0 < cap \<longrightarrow> h < cap))"

definition arq_abstract :: "nat \<Rightarrow> 'a arq \<Rightarrow> 'a list" where
  "arq_abstract cap = (\<lambda> (A, h, sz). map (\<lambda> i. A ((h + i) mod cap)) [0..<sz])"

lemma arq_abstract_length: "length (arq_abstract cap (A, h, sz)) = sz"
  by (simp add: arq_abstract_def)

lemma arq_abstract_Nil_iff: "arq_abstract cap (A, h, sz) = [] \<longleftrightarrow> sz = 0"
  by (simp add: arq_abstract_def)

lemma arq_abstract_push:
  "\<lbrakk>sz < cap; h < cap\<rbrakk> \<Longrightarrow>
    arq_abstract cap (fun_upd A ((h + sz) mod cap) x, h, Suc sz) = arq_abstract cap (A, h, sz) @ [x]"
  by (simp add: arq_abstract_def mod_neq_below cong: map_cong)

lemma arq_abstract_pop:
  "\<lbrakk>0 < sz; h < cap\<rbrakk> \<Longrightarrow>
    tl (arq_abstract cap (A, h, sz)) = arq_abstract cap (A, Suc h mod cap, sz - 1)"
  by (cases sz) (simp_all add: arq_abstract_def map_upt_Suc mod_add_left_eq del: upt_Suc)

lemma arq_abstract_hd: "\<lbrakk>0 < sz; h < cap\<rbrakk> \<Longrightarrow> hd (arq_abstract cap (A, h, sz)) = A h"
  by (simp add: arq_abstract_def hd_map upt_conv_Cons)

lemma arq_bounded_queue:
  "bounded_queue cap (arq_invar cap) (arq_abstract cap) (arq_empty d) (arq_push cap) (arq_pop cap)
     arq_is_empty"
  by unfold_locales
     (auto simp: split_paired_all arq_invar_def arq_empty_def arq_is_empty_def arq_push_def arq_pop_def
       wrap_mod arq_abstract_length arq_abstract_Nil_iff arq_abstract_push arq_abstract_pop
       arq_abstract_hd)

section \<open>The Arrays\<close>

type_synonym 'a arqi = "'a array \<times> nat ref \<times> nat ref"

fun arq_assn :: "nat \<Rightarrow> 'a::heap arq \<Rightarrow> 'a arqi \<Rightarrow> assn" where
  "arq_assn cap (A, h, sz) (Aa, hr, sr) = array_fun_assn cap A Aa * hr \<mapsto>\<^sub>r h * sr \<mapsto>\<^sub>r sz"

definition arq_empty_imp :: "nat \<Rightarrow> 'a::heap \<Rightarrow> 'a arqi Heap" where
  "arq_empty_imp cap d = do { Aa \<leftarrow> Array.new cap d; hr \<leftarrow> ref 0; sr \<leftarrow> ref 0; return (Aa, hr, sr) }"

definition arq_push_imp :: "nat \<Rightarrow> 'a::heap arqi \<Rightarrow> 'a \<Rightarrow> unit Heap" where
  "arq_push_imp cap = (\<lambda> (Aa, hr, sr) x. do {
     h \<leftarrow> !hr; s \<leftarrow> !sr;
     _ \<leftarrow> Array.upd (wrap cap (h + s)) x Aa;
     sr := Suc s })"

definition arq_pop_imp :: "nat \<Rightarrow> 'a::heap arqi \<Rightarrow> 'a Heap" where
  "arq_pop_imp cap = (\<lambda> (Aa, hr, sr). do {
     h \<leftarrow> !hr; s \<leftarrow> !sr;
     x \<leftarrow> Array.nth Aa h;
     hr := wrap cap (Suc h);
     sr := s - 1;
     return x })"

definition arq_is_empty_imp :: "'a::heap arqi \<Rightarrow> bool Heap" where
  "arq_is_empty_imp = (\<lambda> (Aa, hr, sr). do { s \<leftarrow> !sr; return (s = 0) })"

lemma arq_bounded_queue_imp:
  "bounded_queue_imp cap (arq_invar cap) (arq_abstract cap) (arq_empty d) (arq_push cap) (arq_pop cap)
     arq_is_empty (arq_assn cap) (arq_empty_imp cap d) (arq_push_imp cap) (arq_pop_imp cap)
     arq_is_empty_imp"
  by (intro bounded_queue_imp.intro arq_bounded_queue bounded_queue_imp_axioms.intro)
     (sep_auto simp: split_paired_all arq_invar_def arq_empty_def arq_push_def arq_pop_def
       arq_is_empty_def arq_empty_imp_def arq_push_imp_def arq_pop_imp_def arq_is_empty_imp_def
       arq_abstract_length arq_abstract_Nil_iff wrap_def
       heap: array_fun_assn_new array_fun_upd_rule array_fun_lookup_rule)+

end
