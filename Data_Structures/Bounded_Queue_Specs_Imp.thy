theory Bounded_Queue_Specs_Imp
  imports
    Separation_Logic_Imperative_HOL_Partial.Sep_Main
    Bounded_Queue_Specs
begin

text \<open>Imperative bounded queues. Pushing and popping work in place; the only allocating operation
      is @{term queue_empty_imp}, which is used during initialisation only.\<close>

locale bounded_queue_imp =
  bounded_queue where cap = cap
    and queue_invar = queue_invar
    and queue_abstract = queue_abstract
    and queue_empty = queue_empty
    and queue_push = queue_push
    and queue_pop = queue_pop
    and queue_is_empty = queue_is_empty
  for cap :: nat
    and queue_invar :: "'q \<Rightarrow> bool"
    and queue_abstract :: "'q \<Rightarrow> 'a::heap list"
    and queue_empty :: "'q"
    and queue_push :: "'q \<Rightarrow> 'a \<Rightarrow> 'q"
    and queue_pop :: "'q \<Rightarrow> 'a \<times> 'q"
    and queue_is_empty :: "'q \<Rightarrow> bool" +
  fixes queue_assn :: "'q \<Rightarrow> 'qi \<Rightarrow> assn"
    and queue_empty_imp :: "'qi Heap"
    and queue_push_imp :: "'qi \<Rightarrow> 'a \<Rightarrow> unit Heap"
    and queue_pop_imp :: "'qi \<Rightarrow> 'a Heap"
    and queue_is_empty_imp :: "'qi \<Rightarrow> bool Heap"
  assumes queue_empty_rule[sep_heap_rules]:
      "<emp> queue_empty_imp <\<lambda>Qi. queue_assn queue_empty Qi>"
    and queue_push_rule[sep_heap_rules]:
      "\<lbrakk>queue_invar Q; length (queue_abstract Q) < cap\<rbrakk> \<Longrightarrow>
       <queue_assn Q Qi> queue_push_imp Qi x
       <\<lambda>_. queue_assn (queue_push Q x) Qi>"
    and queue_pop_rule[sep_heap_rules]:
      "\<lbrakk>queue_invar Q; queue_abstract Q \<noteq> []\<rbrakk> \<Longrightarrow>
       <queue_assn Q Qi> queue_pop_imp Qi
       <\<lambda>x. queue_assn (snd (queue_pop Q)) Qi * \<up>(x = fst (queue_pop Q))>"
    and queue_is_empty_rule[sep_heap_rules]:
      "queue_invar Q \<Longrightarrow>
       <queue_assn Q Qi> queue_is_empty_imp Qi
       <\<lambda>r. queue_assn Q Qi * \<up>(r = queue_is_empty Q)>"

end
