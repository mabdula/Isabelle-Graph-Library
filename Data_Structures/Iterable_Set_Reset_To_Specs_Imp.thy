theory Iterable_Set_Reset_To_Specs_Imp
  imports
    Iterable_Set_Specs_Imp
    Iterable_Set_Reset_To_Specs
begin

text \<open>Imperative version of @{locale indexed_iterable_set_reset_to}: the jump is done in place.\<close>

locale indexed_iterable_set_reset_to_imp =
  indexed_iterable_set_imp where idx_invar = idx_invar
    and idx_abstract = idx_abstract
    and idx_current = idx_current
    and idx_has = idx_has
    and idx_iterated = idx_iterated
    and idx_remaining = idx_remaining
    and idx_move = idx_move
    and idx_reset = idx_reset
    and K = K
    and idx_assn = idx_assn
    and idx_current_imp = idx_current_imp
    and idx_has_imp = idx_has_imp
    and idx_move_imp = idx_move_imp
    and idx_reset_imp = idx_reset_imp +
  indexed_iterable_set_reset_to where idx_invar = idx_invar
    and idx_abstract = idx_abstract
    and idx_current = idx_current
    and idx_has = idx_has
    and idx_iterated = idx_iterated
    and idx_remaining = idx_remaining
    and idx_move = idx_move
    and idx_reset = idx_reset
    and K = K
    and idx_reset_to = idx_reset_to
  for idx_invar :: "'coll \<Rightarrow> bool"
    and idx_abstract :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a::heap set"
    and idx_current :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a"
    and idx_has :: "'coll \<Rightarrow> 'i \<Rightarrow> bool"
    and idx_iterated :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and idx_remaining :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and idx_move :: "'coll \<Rightarrow> 'i \<Rightarrow> 'coll"
    and idx_reset :: "'coll \<Rightarrow> 'i \<Rightarrow> 'coll"
    and K :: "'i set"
    and idx_assn :: "'coll \<Rightarrow> 'colli \<Rightarrow> assn"
    and idx_current_imp :: "'colli \<Rightarrow> 'i \<Rightarrow> 'a Heap"
    and idx_has_imp :: "'colli \<Rightarrow> 'i \<Rightarrow> bool Heap"
    and idx_move_imp :: "'colli \<Rightarrow> 'i \<Rightarrow> unit Heap"
    and idx_reset_imp :: "'colli \<Rightarrow> 'i \<Rightarrow> unit Heap"
    and idx_reset_to :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a \<Rightarrow> 'coll" +
  fixes idx_reset_to_imp :: "'colli \<Rightarrow> 'i \<Rightarrow> 'a \<Rightarrow> unit Heap"
  assumes idx_reset_to_rule[sep_heap_rules]:
      "\<lbrakk>idx_invar C; i \<in> K; x \<in> idx_abstract C i\<rbrakk> \<Longrightarrow>
       <idx_assn C Ci> idx_reset_to_imp Ci i x
       <\<lambda>_. idx_assn (idx_reset_to C i x) Ci>"

end
