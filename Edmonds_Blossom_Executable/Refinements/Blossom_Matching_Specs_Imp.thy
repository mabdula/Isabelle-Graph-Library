theory Blossom_Matching_Specs_Imp
  imports
    Separation_Logic_Imperative_HOL_Partial.Sep_Main
    Blossom_Executable.Matching_Contraction_Expansion
begin

provenance ai_human

section \<open>Imperative matchings for the blossom algorithm\<close>

text \<open>The imperative interface of the matchings of @{locale blossom_matching}. A matching is
  stored on the heap and related to its functional counterpart by @{term matching_assn}. The
  operations are those that the blossom algorithm uses: allocating the empty matching, looking up
  the partner of a vertex, augmenting along a path in place, and contracting a path to a single
  vertex in place. Their Hoare triples are stated against the functional operations.

  The functional algorithm keeps the matching of every contracted graph for the lifting of paths,
  which comes for free with functional values. The imperative algorithm copies a matching before
  it contracts it in place, so the interface adds an operation that copies a matching.

  The paths passed to augmentation and contraction are heap objects, too. They are related to
  their functional counterparts by the parameter @{term path_assn}; the interface does not fix
  their representation.\<close>

locale blossom_matching_imp =
  blossom_matching
    where K = K and empty_matching = empty_matching and matching_invar = matching_invar
      and lookup_partner = lookup_partner and get_partner = get_partner and augment = augment
      and matching_abstract = matching_abstract and contract_path = contract_path
      and expand_path_at_matched = expand_path_at_matched
      and add_alternatingly = add_alternatingly
  for K :: "'v set"
    and empty_matching :: 'matching
    and matching_invar :: "'v set set \<Rightarrow> 'matching \<Rightarrow> bool"
    and lookup_partner :: "'matching \<Rightarrow> 'v \<Rightarrow> 'v option"
    and get_partner :: "'matching \<Rightarrow> 'v \<Rightarrow> 'v"
    and augment :: "'matching \<Rightarrow> 'v list \<Rightarrow> 'matching"
    and matching_abstract :: "'matching \<Rightarrow> 'v set set"
    and contract_path :: "'matching \<Rightarrow> 'v list \<Rightarrow> 'v \<Rightarrow> 'matching"
    and expand_path_at_matched :: "'matching \<Rightarrow> 'v list \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'matching"
    and add_alternatingly :: "'matching \<Rightarrow> 'v list \<Rightarrow> 'matching" +
  fixes matching_assn :: "'matching \<Rightarrow> 'matchingi \<Rightarrow> assn"
    and path_assn :: "'v list \<Rightarrow> 'pathi \<Rightarrow> assn"
    and empty_matching_imp :: "'matchingi Heap"
    and lookup_partner_imp :: "'matchingi \<Rightarrow> 'v \<Rightarrow> 'v option Heap"
    and augment_imp :: "'matchingi \<Rightarrow> 'pathi \<Rightarrow> unit Heap"
    and contract_path_imp :: "'matchingi \<Rightarrow> 'pathi \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and copy_matching_imp :: "'matchingi \<Rightarrow> 'matchingi Heap"
  assumes empty_matching_rule[sep_heap_rules]:
      "<emp> empty_matching_imp <\<lambda>Mi. matching_assn empty_matching Mi>"
    and lookup_partner_rule[sep_heap_rules]:
      "\<lbrakk>matching_invar G M; x \<in> K\<rbrakk> \<Longrightarrow>
       <matching_assn M Mi> lookup_partner_imp Mi x
       <\<lambda>r. matching_assn M Mi * \<up>(r = lookup_partner M x)>"
    and augment_rule[sep_heap_rules]:
      "\<lbrakk>matching_invar G M; graph_augmenting_path G (matching_abstract M) p; set p \<subseteq> K\<rbrakk> \<Longrightarrow>
       <matching_assn M Mi * path_assn p Pti> augment_imp Mi Pti
       <\<lambda>_. matching_assn (augment M p) Mi * path_assn p Pti>"
    and contract_path_rule[sep_heap_rules]:
      "contract_path_precond G M p new_vert contr \<Longrightarrow>
       <matching_assn M Mi * path_assn p Pti> contract_path_imp Mi Pti new_vert
       <\<lambda>_. matching_assn (contract_path M p new_vert) Mi * path_assn p Pti>"
    and copy_matching_rule[sep_heap_rules]:
      "matching_invar G M \<Longrightarrow>
       <matching_assn M Mi> copy_matching_imp Mi
       <\<lambda>Mi'. matching_assn M Mi * matching_assn M Mi'>"

end
