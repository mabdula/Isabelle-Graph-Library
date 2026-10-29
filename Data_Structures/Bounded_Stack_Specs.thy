theory Bounded_Stack_Specs
  imports
    Main
begin

section \<open>LIFO Stacks of Bounded Length\<close>

text \<open>A LIFO stack abstracted to a list (top first). As for @{text bounded_queue}, an
      implementation is bounded by a capacity @{term cap}: elements may only be pushed while the
      stack holds fewer than @{term cap} elements. An implementation may therefore be an array of
      length @{term cap}, allocated once.\<close>

locale bounded_stack =
  fixes cap :: nat
  and stack_invar :: "'s \<Rightarrow> bool"
  and stack_abstract :: "'s \<Rightarrow> 'a list"
  and stack_empty :: "'s"
  and stack_push :: "'s \<Rightarrow> 'a \<Rightarrow> 's"
  and stack_pop :: "'s \<Rightarrow> 's"
  and stack_top :: "'s \<Rightarrow> 'a"
  and stack_is_empty :: "'s \<Rightarrow> bool"
  assumes stack_capacity:
      "\<And> S. stack_invar S \<Longrightarrow> length (stack_abstract S) \<le> cap"
  and stack_empty:
      "stack_invar stack_empty"
      "stack_abstract stack_empty = []"
  and stack_push:
      "\<And> S x. \<lbrakk>stack_invar S; length (stack_abstract S) < cap\<rbrakk> \<Longrightarrow>
          stack_invar (stack_push S x)"
      "\<And> S x. \<lbrakk>stack_invar S; length (stack_abstract S) < cap\<rbrakk> \<Longrightarrow>
          stack_abstract (stack_push S x) = x # stack_abstract S"
  and stack_pop:
      "\<And> S. \<lbrakk>stack_invar S; stack_abstract S \<noteq> []\<rbrakk> \<Longrightarrow>
          stack_invar (stack_pop S)"
      "\<And> S. \<lbrakk>stack_invar S; stack_abstract S \<noteq> []\<rbrakk> \<Longrightarrow>
          stack_abstract (stack_pop S) = tl (stack_abstract S)"
  and stack_top:
      "\<And> S. \<lbrakk>stack_invar S; stack_abstract S \<noteq> []\<rbrakk> \<Longrightarrow>
          stack_top S = hd (stack_abstract S)"
  and stack_is_empty:
      "\<And> S. stack_invar S \<Longrightarrow> stack_is_empty S \<longleftrightarrow> stack_abstract S = []"

end
