theory Bounded_Stack_Specs_Imp
  imports
    Separation_Logic_Imperative_HOL_Partial.Sep_Main
    Bounded_Stack_Specs
begin

text \<open>Imperative bounded stacks. Pushing and popping work in place; the only allocating operation
      is @{term stack_empty_imp}, which is used during initialisation only.\<close>

locale bounded_stack_imp =
  bounded_stack where cap = cap
    and stack_invar = stack_invar
    and stack_abstract = stack_abstract
    and stack_empty = stack_empty
    and stack_push = stack_push
    and stack_pop = stack_pop
    and stack_top = stack_top
    and stack_is_empty = stack_is_empty
  for cap :: nat
    and stack_invar :: "'s \<Rightarrow> bool"
    and stack_abstract :: "'s \<Rightarrow> 'a::heap list"
    and stack_empty :: "'s"
    and stack_push :: "'s \<Rightarrow> 'a \<Rightarrow> 's"
    and stack_pop :: "'s \<Rightarrow> 's"
    and stack_top :: "'s \<Rightarrow> 'a"
    and stack_is_empty :: "'s \<Rightarrow> bool" +
  fixes stack_assn :: "'s \<Rightarrow> 'si \<Rightarrow> assn"
    and stack_empty_imp :: "'si Heap"
    and stack_push_imp :: "'si \<Rightarrow> 'a \<Rightarrow> unit Heap"
    and stack_pop_imp :: "'si \<Rightarrow> unit Heap"
    and stack_top_imp :: "'si \<Rightarrow> 'a Heap"
    and stack_is_empty_imp :: "'si \<Rightarrow> bool Heap"
  assumes stack_empty_rule[sep_heap_rules]:
      "<emp> stack_empty_imp <\<lambda>Si. stack_assn stack_empty Si>"
    and stack_push_rule[sep_heap_rules]:
      "\<lbrakk>stack_invar S; length (stack_abstract S) < cap\<rbrakk> \<Longrightarrow>
       <stack_assn S Si> stack_push_imp Si x
       <\<lambda>_. stack_assn (stack_push S x) Si>"
    and stack_pop_rule[sep_heap_rules]:
      "\<lbrakk>stack_invar S; stack_abstract S \<noteq> []\<rbrakk> \<Longrightarrow>
       <stack_assn S Si> stack_pop_imp Si
       <\<lambda>_. stack_assn (stack_pop S) Si>"
    and stack_top_rule[sep_heap_rules]:
      "\<lbrakk>stack_invar S; stack_abstract S \<noteq> []\<rbrakk> \<Longrightarrow>
       <stack_assn S Si> stack_top_imp Si
       <\<lambda>x. stack_assn S Si * \<up>(x = stack_top S)>"
    and stack_is_empty_rule[sep_heap_rules]:
      "stack_invar S \<Longrightarrow>
       <stack_assn S Si> stack_is_empty_imp Si
       <\<lambda>r. stack_assn S Si * \<up>(r = stack_is_empty S)>"

end
