(*
  Author: Peter Lammich
*)

theory Pair_Graph_Imperative
imports Pair_Graph_Specs Imperative.Imperative_DS Imperative.Array_Range_Iteration
begin

provenance human

  type_synonym 'v id_dl_graph = "'v \<Rightarrow> 'v list option"
    
  locale Pair_Graph_Imperative =
    imp_map_empty where empty=mempty_impl +
    imp_map_lookup where lookup=mlookup_impl +
    imp_map_update where update=mupdate_impl
    for mempty_impl mlookup_impl mupdate_impl
    +
    constrains is_map :: "('v \<rightharpoonup> 'v list) \<Rightarrow> 'gimpl \<Rightarrow> assn"
    
  begin
  
    (* We fix the set implementation to lists *)
    (* TODO @M: parameter ordering appears completely random here *)
    sublocale Pair_Graph_Specs 
      idm_empty idm_delete idm_lookup 
      dls_insert dls_isin dls_set dls_sel
      idm_update idm_invar
      dls_empty dls_delete dls_invar
      by unfold_locales


    definition 
      graph_assn :: "'v id_dl_graph \<Rightarrow> 'gimpl \<Rightarrow> assn"
      where "graph_assn lg lgi \<equiv> is_map lg lgi * \<up>(graph_inv lg)"  
      
    definition empty_graph_impl :: "'gimpl Heap" where "empty_graph_impl \<equiv> mempty_impl"
  
    lemma empty_graph_impl_rule[sep_heap_rules]: "<emp> empty_graph_impl <graph_assn (\<lambda>_. None)>"
      unfolding empty_graph_impl_def graph_assn_def by sep_auto
      
      
    definition 
      neighbourhood_impl :: "'gimpl \<Rightarrow> 'v \<Rightarrow> 'v list Heap"
      where "neighbourhood_impl G v \<equiv> do {
        l \<leftarrow> mlookup_impl v G;
        return (the_default [] l)
      }"  
  
    lemma neighbourhood_impl_rule[sep_heap_rules]: 
      "<graph_assn lg lgi> neighbourhood_impl lgi v <\<lambda>r. graph_assn lg lgi * \<up>( r = neighbourhood lg v \<and> distinct r )>"
      unfolding graph_assn_def neighbourhood_impl_def neighbourhood_def
      by (sep_auto split: option.split 
                    simp: More_Logic.the_default_def)
          
    definition add_edge_impl :: "'gimpl \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'gimpl Heap" where "add_edge_impl G u v = do {
      l \<leftarrow> mlookup_impl u G;
      let l = the_default [] l;
      let l = dls_insert v l;
      G \<leftarrow> mupdate_impl u l G;
      return G
    }"
    
    lemma add_edge_impl_rule[sep_heap_rules]: 
      "<graph_assn lg lgi> add_edge_impl lgi u v <\<lambda>r. graph_assn (add_edge lg u v) r>"
      unfolding add_edge_impl_def graph_assn_def
      by sep_auto (sep_auto split: option.split 
                             simp: add_edge_def More_Logic.the_default_def)


    definition "from_list_impl xs \<equiv> do { G \<leftarrow> empty_graph_impl; foldM (\<lambda>(u,v) G. add_edge_impl G u v) xs G }"
      
    lemma from_list_impl_rule[sep_heap_rules]:
      shows "<emp> from_list_impl xs <graph_assn (from_list xs)>"
      supply R = foldM_refine[where I="\<lambda>_ _ G Gi. (graph_assn G Gi)"] \<comment> \<open>Coupling relation is straightforward\<close>
      supply R[sep_heap_rules] = R[where f="\<lambda>(u, v) G. add_edge G u v"] \<comment> \<open>The pair causes unification problems, so we need explicit instantiation\<close>
      unfolding from_list_impl_def from_list_def'
      apply sep_auto
      done

  end

  text \<open>The same buildup from two arrays of equal length holding the first and the second
        endpoints of the edges. Storing vertices in arrays needs them to be of sort \<open>heap\<close>.\<close>

  declare iterate_range_infoed.simps[code]

  locale Pair_Graph_Imperative_Arrays =
    Pair_Graph_Imperative is_map mempty_impl mlookup_impl mupdate_impl
    for is_map :: "('v::heap \<rightharpoonup> 'v list) \<Rightarrow> 'gimpl \<Rightarrow> assn"
      and mempty_impl mlookup_impl mupdate_impl
  begin

    definition "from_arrays_impl Fa Ta \<equiv> do {
      l \<leftarrow> Array.len Fa;
      G \<leftarrow> empty_graph_impl;
      if l = 0 then return G
      else iterate_range_infoed Fa Ta 0 (l - 1) (\<lambda>u v G. add_edge_impl G u v) G
    }"

    lemma from_arrays_impl_rule[sep_heap_rules]:
      assumes "length ts = length fs"
      shows "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts> from_arrays_impl Fa Ta
               <\<lambda>G. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * graph_assn (from_list (zip fs ts)) G>"
    proof -
      have "{0..length fs - 1} = {..<length fs}" if "fs \<noteq> []"
        using that by (cases "length fs") auto
      thus ?thesis
        unfolding from_arrays_impl_def
        by (sep_auto heap: iterate_range_infoed_rule[where acc_assn=graph_assn
              and f="\<lambda>G (u, v). add_edge G u v" and F=emp, simplified]
            simp: from_list_def assms)
    qed

  end




end
