theory Iterable_Set_Specs_Imp
  imports Separation_Logic_Imperative_HOL_Partial.Sep_Main Iterable_Set_Specs
begin

locale iterable_set_imp =
  iterable_set where iterable_set_invar = iterable_set_invar
    and iterable_set_abstract = iterable_set_abstract
    and current_element = current_element
    and has_current = has_current
    and iterated = iterated
    and remaining = remaining
    and move_on = move_on
  for iterable_set_invar :: "'iset \<Rightarrow> bool"
    and iterable_set_abstract :: "'iset \<Rightarrow> 'a::heap set"
    and current_element :: "'iset \<Rightarrow> 'a"
    and has_current :: "'iset \<Rightarrow> bool"
    and iterated :: "'iset \<Rightarrow> 'a set"
    and remaining :: "'iset \<Rightarrow> 'a set"
    and move_on :: "'iset \<Rightarrow> 'iset" +
  fixes iterable_set_assn :: "'iset \<Rightarrow> 'iseti \<Rightarrow> assn"
    and current_element_imp :: "'iseti \<Rightarrow> 'a Heap"
    and has_current_imp :: "'iseti \<Rightarrow> bool Heap"
    and move_on_imp :: "'iseti \<Rightarrow> unit Heap"
  assumes current_element_rule[sep_heap_rules]:
      "\<lbrakk>iterable_set_invar S; remaining S \<noteq> {}\<rbrakk> \<Longrightarrow>
       <iterable_set_assn S Si> current_element_imp Si
       <\<lambda>x. iterable_set_assn S Si * \<up>(x = current_element S)>"
    and has_current_rule[sep_heap_rules]:
      "iterable_set_invar S \<Longrightarrow>
       <iterable_set_assn S Si> has_current_imp Si
       <\<lambda>r. iterable_set_assn S Si * \<up>(r = has_current S)>"
    and move_on_rule[sep_heap_rules]:
      "\<lbrakk>iterable_set_invar S; remaining S \<noteq> {}\<rbrakk> \<Longrightarrow>
       <iterable_set_assn S Si> move_on_imp Si
       <\<lambda>_. iterable_set_assn (move_on S) Si>"

section \<open>Imperative Indexed Collections of Sets\<close>

text \<open>The imperative mirrors of the layers of @{locale indexed_set_collection}. Each layer only
      adds the Hoare triples of its own operations.\<close>

locale indexed_set_collection_imp =
  indexed_set_collection where idx_invar = idx_invar and idx_abstract = idx_abstract and K = K
  for idx_invar :: "'coll \<Rightarrow> bool"
    and idx_abstract :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and K :: "'i set" +
  fixes idx_assn :: "'coll \<Rightarrow> 'colli \<Rightarrow> assn"

text \<open>The imperative fold runs a heap function over the elements of a set and threads an
      accumulator through. It refines the fold of @{locale indexed_set_fold}: if the heap
      function refines the function folded, so does the imperative fold.\<close>

locale indexed_set_fold_imp =
  indexed_set_fold where idx_invar = idx_invar and idx_abstract = idx_abstract and K = K
    and idx_fold = idx_fold +
  indexed_set_collection_imp where idx_invar = idx_invar and idx_abstract = idx_abstract and K = K
    and idx_assn = idx_assn
  for idx_invar :: "'coll \<Rightarrow> bool"
    and idx_abstract :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and K :: "'i set"
    and idx_fold :: "'coll \<Rightarrow> 'i \<Rightarrow> ('a \<Rightarrow> 'acc \<Rightarrow> 'acc) \<Rightarrow> 'acc \<Rightarrow> 'acc"
    and idx_assn :: "'coll \<Rightarrow> 'colli \<Rightarrow> assn" +
  fixes idx_fold_imp :: "'colli \<Rightarrow> 'i \<Rightarrow> ('a \<Rightarrow> 'acci \<Rightarrow> 'acci Heap) \<Rightarrow> 'acci \<Rightarrow> 'acci Heap"
  assumes idx_fold_rule:
      "\<lbrakk>idx_invar C; i \<in> K;
        \<And>acc acci x. x \<in> idx_abstract C i \<Longrightarrow>
          <acc_assn acc acci> fi x acci <\<lambda>r. acc_assn (f x acc) r>\<rbrakk> \<Longrightarrow>
       <idx_assn C Ci * acc_assn acc acci> idx_fold_imp Ci i fi acci
       <\<lambda>r. idx_assn C Ci * acc_assn (idx_fold C i f acc) r>"

locale indexed_set_cursor_imp =
  indexed_set_cursor where idx_invar = idx_invar and idx_abstract = idx_abstract and K = K
    and idx_current = idx_current and idx_has = idx_has and idx_iterated = idx_iterated
    and idx_remaining = idx_remaining and idx_move = idx_move +
  indexed_set_collection_imp where idx_invar = idx_invar and idx_abstract = idx_abstract and K = K
    and idx_assn = idx_assn
  for idx_invar :: "'coll \<Rightarrow> bool"
    and idx_abstract :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and K :: "'i set"
    and idx_current :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a"
    and idx_has :: "'coll \<Rightarrow> 'i \<Rightarrow> bool"
    and idx_iterated :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and idx_remaining :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and idx_move :: "'coll \<Rightarrow> 'i \<Rightarrow> 'coll"
    and idx_assn :: "'coll \<Rightarrow> 'colli \<Rightarrow> assn" +
  fixes idx_current_imp :: "'colli \<Rightarrow> 'i \<Rightarrow> 'a Heap"
    and idx_has_imp :: "'colli \<Rightarrow> 'i \<Rightarrow> bool Heap"
    and idx_move_imp :: "'colli \<Rightarrow> 'i \<Rightarrow> unit Heap"
  assumes idx_current_rule[sep_heap_rules]:
      "\<lbrakk>idx_invar C; i \<in> K; idx_remaining C i \<noteq> {}\<rbrakk> \<Longrightarrow>
       <idx_assn C Ci> idx_current_imp Ci i
       <\<lambda>x. idx_assn C Ci * \<up>(x = idx_current C i)>"
    and idx_has_rule[sep_heap_rules]:
      "\<lbrakk>idx_invar C; i \<in> K\<rbrakk> \<Longrightarrow>
       <idx_assn C Ci> idx_has_imp Ci i
       <\<lambda>r. idx_assn C Ci * \<up>(r = idx_has C i)>"
    and idx_move_rule[sep_heap_rules]:
      "\<lbrakk>idx_invar C; i \<in> K; idx_remaining C i \<noteq> {}\<rbrakk> \<Longrightarrow>
       <idx_assn C Ci> idx_move_imp Ci i
       <\<lambda>_. idx_assn (idx_move C i) Ci>"

locale indexed_set_reset_imp =
  indexed_set_reset where idx_invar = idx_invar and idx_abstract = idx_abstract and K = K
    and idx_iterated = idx_iterated and idx_remaining = idx_remaining and idx_reset = idx_reset +
  indexed_set_collection_imp where idx_invar = idx_invar and idx_abstract = idx_abstract and K = K
    and idx_assn = idx_assn
  for idx_invar :: "'coll \<Rightarrow> bool"
    and idx_abstract :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and K :: "'i set"
    and idx_iterated :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and idx_remaining :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and idx_reset :: "'coll \<Rightarrow> 'i \<Rightarrow> 'coll"
    and idx_assn :: "'coll \<Rightarrow> 'colli \<Rightarrow> assn" +
  fixes idx_reset_imp :: "'colli \<Rightarrow> 'i \<Rightarrow> unit Heap"
  assumes idx_reset_rule[sep_heap_rules]:
      "\<lbrakk>idx_invar C; i \<in> K\<rbrakk> \<Longrightarrow>
       <idx_assn C Ci> idx_reset_imp Ci i
       <\<lambda>_. idx_assn (idx_reset C i) Ci>"

text \<open>Iterable sets: cursor and reset.\<close>

locale indexed_iterable_set_imp =
  indexed_iterable_set where idx_invar = idx_invar
    and idx_abstract = idx_abstract
    and idx_current = idx_current
    and idx_has = idx_has
    and idx_iterated = idx_iterated
    and idx_remaining = idx_remaining
    and idx_move = idx_move
    and idx_reset = idx_reset
    and K = K +
  indexed_set_cursor_imp where idx_invar = idx_invar and idx_abstract = idx_abstract and K = K
    and idx_current = idx_current and idx_has = idx_has and idx_iterated = idx_iterated
    and idx_remaining = idx_remaining and idx_move = idx_move and idx_assn = idx_assn
    and idx_current_imp = idx_current_imp and idx_has_imp = idx_has_imp
    and idx_move_imp = idx_move_imp +
  indexed_set_reset_imp where idx_invar = idx_invar and idx_abstract = idx_abstract and K = K
    and idx_iterated = idx_iterated and idx_remaining = idx_remaining and idx_reset = idx_reset
    and idx_assn = idx_assn and idx_reset_imp = idx_reset_imp
  for idx_invar :: "'coll \<Rightarrow> bool"
    and idx_abstract :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
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

text \<open>Setting a cursor to an element (@{locale indexed_set_reset_to}), done in place.\<close>

locale indexed_set_reset_to_imp =
  indexed_set_reset_to where idx_invar = idx_invar and idx_abstract = idx_abstract and K = K
    and idx_current = idx_current and idx_has = idx_has and idx_iterated = idx_iterated
    and idx_remaining = idx_remaining and idx_move = idx_move and idx_reset_to = idx_reset_to +
  indexed_set_collection_imp where idx_invar = idx_invar and idx_abstract = idx_abstract and K = K
    and idx_assn = idx_assn
  for idx_invar :: "'coll \<Rightarrow> bool"
    and idx_abstract :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and K :: "'i set"
    and idx_current :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a"
    and idx_has :: "'coll \<Rightarrow> 'i \<Rightarrow> bool"
    and idx_iterated :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and idx_remaining :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and idx_move :: "'coll \<Rightarrow> 'i \<Rightarrow> 'coll"
    and idx_reset_to :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a \<Rightarrow> 'coll"
    and idx_assn :: "'coll \<Rightarrow> 'colli \<Rightarrow> assn" +
  fixes idx_reset_to_imp :: "'colli \<Rightarrow> 'i \<Rightarrow> 'a \<Rightarrow> unit Heap"
  assumes idx_reset_to_rule[sep_heap_rules]:
      "\<lbrakk>idx_invar C; i \<in> K; x \<in> idx_abstract C i\<rbrakk> \<Longrightarrow>
       <idx_assn C Ci> idx_reset_to_imp Ci i x
       <\<lambda>_. idx_assn (idx_reset_to C i x) Ci>"

text \<open>Iterable sets with both resets.\<close>

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
    and idx_reset_to = idx_reset_to +
  indexed_set_reset_to_imp where idx_invar = idx_invar and idx_abstract = idx_abstract and K = K
    and idx_current = idx_current and idx_has = idx_has and idx_iterated = idx_iterated
    and idx_remaining = idx_remaining and idx_move = idx_move and idx_reset_to = idx_reset_to
    and idx_assn = idx_assn and idx_reset_to_imp = idx_reset_to_imp
  for idx_invar :: "'coll \<Rightarrow> bool"
    and idx_abstract :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
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
    and idx_reset_to :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a \<Rightarrow> 'coll"
    and idx_reset_to_imp :: "'colli \<Rightarrow> 'i \<Rightarrow> 'a \<Rightarrow> unit Heap"
end