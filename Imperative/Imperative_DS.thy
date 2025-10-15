theory Imperative_DS
imports Imperative_Base "Data_Structures.Set_Choose" "Data_Structures.Map_Addons"
begin

  (* Marrying functional Set-ADT and its imperative version, using a multi-valued refinement assertion *)
  locale imp_set_conn = Set + imp_set 
    + imp_set_empty where empty=empty_impl 
    + imp_set_ins where ins=insert_impl 
    + imp_set_delete where delete=delete_impl 
    + imp_set_memb where memb=isin_impl 
    for empty_impl isin_impl insert_impl delete_impl
    +
    constrains set :: "'s \<Rightarrow> 'a set"
    and is_set :: "'a set \<Rightarrow> _"
    
    
  begin  
    definition "assn xs xsi \<equiv> \<up>(invar xs) * is_set (set xs) xsi"
     
    context
      includes automation
      notes [simp] = assn_def 
    begin  
    
      lemma empty_rule[sep_heap_rules]: "<emp> empty_impl <assn empty>"
        by sep_auto

      lemma insert_rule[sep_heap_rules]: "<assn xs xsi > insert_impl x xsi <assn (insert x xs)>"
        by sep_auto
            
      lemma delete_rule[sep_heap_rules]: "<assn xs xsi > delete_impl x xsi <assn (delete x xs)>"
        by sep_auto
    
      lemma isin_rule[sep_heap_rules]: "<assn xs xsi > isin_impl x xsi <\<lambda>r. assn xs xsi * \<up>(r = isin xs x)>"
        by sep_auto
        
    end  
  end

  
  abbreviation (input) "idm_empty \<equiv> Map.empty"
  abbreviation (input) "idm_update \<equiv> \<lambda>k v m. m(k\<mapsto>v)"
  abbreviation (input) "idm_delete \<equiv> \<lambda>k m. m(k:=None)"
  abbreviation (input) "idm_lookup \<equiv> \<lambda>m k. m k"
  abbreviation (input) "idm_invar \<equiv> \<lambda>_. True"
  
  
  interpretation id_map: Map idm_empty idm_update idm_delete idm_lookup idm_invar
    apply unfold_locales
    by auto
  

  abbreviation (input) "dls_empty \<equiv> []"  
  definition "dls_insert x xs \<equiv> if x\<in>set xs then xs else x#xs"  
  abbreviation (input) "dls_insert_dj x xs \<equiv> x#xs"  
  definition "dls_delete x xs \<equiv> filter (\<lambda>y. y\<noteq>x) xs"
  definition "dls_isin xs x \<equiv> x\<in>set xs"
  abbreviation (input) "dls_set \<equiv> set"
  abbreviation (input) "dls_invar \<equiv> distinct"
  
  abbreviation (input) "dls_sel \<equiv> hd"
  
  definition "dls_union a b \<equiv> remdups (a@b)"
  definition "dls_inter a b \<equiv> filter (\<lambda>x. x\<in>set b) a"
  definition "dls_diff a b \<equiv> filter (\<lambda>x. x\<notin>set b) a"
  
    
  lemmas dls_defs = dls_insert_def dls_delete_def dls_isin_def dls_union_def dls_inter_def dls_diff_def
  
  
  
  
  
  (* TODO @M: locale parameters should'nt be swapped, makes it harder to use *)
  interpretation dlist_set: Set dls_empty dls_insert dls_delete dls_isin dls_set dls_invar
    apply unfold_locales
    unfolding dls_defs
    apply auto
    done
  
  
  interpretation dlist_set: Set2 dls_empty dls_delete dls_isin dls_set dls_invar dls_insert dls_union dls_inter dls_diff
    apply unfold_locales
    unfolding dls_defs
    by auto
    
  interpretation dlist_set: Set_Choose dls_empty dls_insert dls_delete dls_isin dls_invar dls_set dls_sel
    apply unfold_locales
    unfolding dls_defs
    by auto
    
    
  (* Connect array-set and dlist-set *)  

  locale imp_set_dls = 
    imp_set is_set 
    + imp_set_empty is_set empty_impl 
    (* + imp_set_is_empty is_set is_empty_impl *)
    + imp_set_memb is_set member_impl
    + imp_set_ins is_set ins_impl 
    + imp_set_delete is_set del_impl 
    for is_set :: "'a set \<Rightarrow> 'si \<Rightarrow> assn" 
    and empty_impl member_impl ins_impl del_impl
  begin
    
    sublocale imp_set_conn 
      dls_empty dls_insert dls_delete dls_isin dls_set dls_invar
      is_set empty_impl member_impl ins_impl del_impl 
      by unfold_locales
  
     
        
    (* Diff-operation: subtract imp-set from dls. We implemented that directly, though it's a filterM *)
    fun dls_diff_imp where
      "dls_diff_imp [] ias = return []"
    | "dls_diff_imp (x#xs) ias = do {
        b \<leftarrow> member_impl x ias;
        xs' \<leftarrow> dls_diff_imp xs ias;
        if b then return xs' else return (x#xs')
      }"    
  
  
    (* Correctness lemma. The proof is a bit more technical, as it requires combining details of the data structures *)
    lemma dls_diff_imp_rule[sep_heap_rules]: 
      "dls_invar xs\<^sub>1 \<Longrightarrow> < assn xs\<^sub>2 xsi\<^sub>2 > dls_diff_imp xs\<^sub>1 xsi\<^sub>2 <\<lambda>r. assn xs\<^sub>2 xsi\<^sub>2 * \<up>(r = dls_diff xs\<^sub>1 xs\<^sub>2 \<and> dls_invar r )>"    
    proof (induction xs\<^sub>1)
      case Nil
      then show ?case by (sep_auto simp: dls_diff_def)
    next
      case (Cons a xs\<^sub>1)
      hence [sep_heap_rules]: "<assn xs\<^sub>2 xsi\<^sub>2> dls_diff_imp xs\<^sub>1 xsi\<^sub>2 <\<lambda>r. assn xs\<^sub>2 xsi\<^sub>2 * \<up> (r = dls_diff xs\<^sub>1 xs\<^sub>2 \<and> dls_invar r)>" by simp
      
      include dlist_set.automation
      
      show ?case 
        (* Extract dls_invar for xs\<^sub>2 from assertion in precondition *)
        apply (rule hoare_triple_preI)
        apply (subst (asm) assn_def)
        
        using Cons.prems
        apply (sep_auto simp: dls_diff_def)
        done
    qed    
      
      
      
      
  end        








end
