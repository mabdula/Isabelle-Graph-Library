theory Alternating_Forest_Specs_Imp
  imports
    Separation_Logic_Imperative_HOL_Partial.Sep_Main
    Basic_Matching.Alternating_Forest_Spec
begin

provenance ai_human

section \<open>Imperative alternating forests\<close>

text \<open>The imperative interface of the alternating forests of @{locale
  alternating_forest_ordinary_extension_spec}. A forest is stored on the heap and related to its
  functional counterpart by @{term forest_assn}. The operations are those that the alternating
  forest search uses: allocating the forest that consists of a set of roots, testing whether a
  vertex is even or odd, extending the forest in place by an edge to an unlabelled vertex and its
  partner, and reading off the path from an even vertex to its root. Their Hoare triples are
  stated against the functional operations.

  The set of roots and the path read off the forest are heap objects, too. They are related to
  their functional counterparts by the parameters @{term vset_assn} and @{term path_assn}; the
  interface does not fix their representation. The roots are handed over to the forest, which may
  reuse them.\<close>

locale alternating_forest_imp =
  alternating_forest_ordinary_extension_spec
    where evens = evens and odds = odds and get_path = get_path
      and abstract_forest = abstract_forest and forest_invar = forest_invar and roots = roots
      and vset_invar = vset_invar and vset_to_set = vset_to_set
      and extend_forest_even_unclassified = extend_forest_even_unclassified
      and empty_forest = empty_forest and forest_univ = forest_univ and vset_empty = vset_empty
  for evens odds roots :: "'forest \<Rightarrow> 'vset"
    and get_path :: "'forest \<Rightarrow> 'v \<Rightarrow> 'v list"
    and abstract_forest :: "'forest \<Rightarrow> 'v set set"
    and forest_invar :: "'v set set \<Rightarrow> 'forest \<Rightarrow> bool"
    and vset_invar :: "'vset \<Rightarrow> bool"
    and vset_to_set :: "'vset \<Rightarrow> 'v set"
    and extend_forest_even_unclassified :: "'forest \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'forest"
    and empty_forest :: "'vset \<Rightarrow> 'forest"
    and forest_univ :: "'v set"
    and vset_empty :: 'vset +
  fixes forest_assn :: "'forest \<Rightarrow> 'foresti \<Rightarrow> assn"
    and vset_assn :: "'vset \<Rightarrow> 'vseti \<Rightarrow> assn"
    and path_assn :: "'v list \<Rightarrow> 'pathi \<Rightarrow> assn"
    and empty_forest_imp :: "'vseti \<Rightarrow> 'foresti Heap"
    and evens_isin_imp :: "'foresti \<Rightarrow> 'v \<Rightarrow> bool Heap"
    and odds_isin_imp :: "'foresti \<Rightarrow> 'v \<Rightarrow> bool Heap"
    and extend_forest_even_unclassified_imp :: "'foresti \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and get_path_imp :: "'foresti \<Rightarrow> 'v \<Rightarrow> 'pathi Heap"
  assumes empty_forest_rule[sep_heap_rules]:
      "\<lbrakk>vset_invar R; vset_to_set R \<subseteq> forest_univ\<rbrakk> \<Longrightarrow>
       <vset_assn R Ri> empty_forest_imp Ri <\<lambda>Fi. forest_assn (empty_forest R) Fi>"
    and evens_isin_rule[sep_heap_rules]:
      "\<lbrakk>forest_invar M F; v \<in> forest_univ\<rbrakk> \<Longrightarrow>
       <forest_assn F Fi> evens_isin_imp Fi v
       <\<lambda>r. forest_assn F Fi * \<up>(r \<longleftrightarrow> v \<in> vset_to_set (evens F))>"
    and odds_isin_rule[sep_heap_rules]:
      "\<lbrakk>forest_invar M F; v \<in> forest_univ\<rbrakk> \<Longrightarrow>
       <forest_assn F Fi> odds_isin_imp Fi v
       <\<lambda>r. forest_assn F Fi * \<up>(r \<longleftrightarrow> v \<in> vset_to_set (odds F))>"
    and extend_forest_even_unclassified_rule[sep_heap_rules]:
      "\<lbrakk>forest_extension_precond F M x y z; {x, y, z} \<subseteq> forest_univ\<rbrakk> \<Longrightarrow>
       <forest_assn F Fi> extend_forest_even_unclassified_imp Fi x y z
       <\<lambda>_. forest_assn (extend_forest_even_unclassified F x y z) Fi>"
    and get_path_rule[sep_heap_rules]:
      "\<lbrakk>forest_invar M F; v \<in> vset_to_set (evens F)\<rbrakk> \<Longrightarrow>
       <forest_assn F Fi> get_path_imp Fi v
       <\<lambda>Pti. forest_assn F Fi * path_assn (get_path F v) Pti>"

end
