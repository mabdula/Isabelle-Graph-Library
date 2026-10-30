theory Weighted_Neighbourhoods_Imperative_Spec
  imports Data_Structures.Iterable_Set_Specs_Imp
          Separation_Logic_Imperative_HOL_Partial.Sep_Main
          Complex_Main
begin

provenance ai


section \<open>Imperative Collections of Weighted Neighbourhoods\<close>

text \<open>The imperative collection of neighbourhoods with cursors,
      @{locale indexed_iterable_set_imp}, is extended by two operations. The algorithms that use such a collection read the weights of the
      edges through a separate weight function @{term cost}. Imperatively, the weights are only
      available \<^emph>\<open>at the cursor\<close>: @{term current_cost_imp} returns the weight of the edge from the
      index @{term i} to its current element, as an executable value that @{term wval} maps to the
      functional weight. How this weight is found is not visible to the user of the collection
      (in a CSR representation, it is stored next to the current element).

      @{term reset_all_imp} resets all cursors at once, in place, bringing the collection back to
      its initial state @{term nb_init}.\<close>

locale weighted_neighbourhoods_imp_spec =
  indexed_iterable_set_imp where idx_invar = idx_invar
    and idx_abstract = idx_abstract
    and idx_current = idx_current
    and idx_has = idx_has
    and idx_iterated = idx_iterated
    and idx_remaining = idx_remaining
    and idx_move = idx_move
    and idx_reset = idx_reset
    and K = K
    and idx_assn = nb_assn
    and idx_current_imp = current_imp
    and idx_has_imp = has_imp
    and idx_move_imp = move_imp
    and idx_reset_imp = reset_imp
  for idx_invar :: "'coll \<Rightarrow> bool"
    and idx_abstract :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a::heap set"
    and idx_current :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a"
    and idx_has :: "'coll \<Rightarrow> 'i \<Rightarrow> bool"
    and idx_iterated :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and idx_remaining :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and idx_move :: "'coll \<Rightarrow> 'i \<Rightarrow> 'coll"
    and idx_reset :: "'coll \<Rightarrow> 'i \<Rightarrow> 'coll"
    and K :: "'i set"
    and nb_assn :: "'coll \<Rightarrow> 'colli \<Rightarrow> assn"
    and current_imp :: "'colli \<Rightarrow> 'i \<Rightarrow> 'a Heap"
    and has_imp :: "'colli \<Rightarrow> 'i \<Rightarrow> bool Heap"
    and move_imp :: "'colli \<Rightarrow> 'i \<Rightarrow> unit Heap"
    and reset_imp :: "'colli \<Rightarrow> 'i \<Rightarrow> unit Heap" +
  fixes cost :: "'i \<Rightarrow> 'a \<Rightarrow> real"
    and wval :: "'w \<Rightarrow> real"
    and nb_init :: "'coll"
    and current_cost_imp :: "'colli \<Rightarrow> 'i \<Rightarrow> 'w Heap"
    and reset_all_imp :: "'colli \<Rightarrow> unit Heap"
  assumes nb_init_invar: "idx_invar nb_init"
    and current_cost_rule[sep_heap_rules]:
      "\<lbrakk>idx_invar C; i \<in> K; idx_remaining C i \<noteq> {}\<rbrakk> \<Longrightarrow>
       <nb_assn C Ci> current_cost_imp Ci i
       <\<lambda>c. nb_assn C Ci * \<up>(wval c = cost i (idx_current C i))>"
    and reset_all_rule[sep_heap_rules]:
      "\<lbrakk>idx_invar C; \<forall>i\<in>K. idx_abstract C i = idx_abstract nb_init i\<rbrakk> \<Longrightarrow>
       <nb_assn C Ci> reset_all_imp Ci <\<lambda>_. nb_assn nb_init Ci>"

end
