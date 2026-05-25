theory DFS_Imperative
imports DFS Directed_Set_Graphs.Pair_Graph_Imperative DFS_Example
begin

  
    
  section \<open>Imperative DFS Locale\<close>
  
  subsection \<open>Setup\<close>
  
  (* We gather the imperative ADT-locales, and then sublocale DFS.
  
    The functional ADTs here are implemented to standard data structures, that contain just enough
    information to implement the operations:
  
    Sets: we implement these with distinct lists, as we have to provide a choose operation.
    
      The DFS locale uses the same set ADT for the successor set of graphs, and for the seen-set,
      however, in our imperative implementation, we want to separate the two:
        * the successors are implemented as lists. As they occur inside the imperative graph 
          data structure, implementing them imperatively would yield a nested imperative data structure,
          which is more complicated. 
          Also, the choose function cannot be lifted over a further refinement,
          unless that refinement goes from lists. However, the imperative set data structures typically 
          refine to set. This is the price to pay for not having genuine nondeterminism on the abstract level.
        
        * the seen set is implemented imperatively. Note that no choose function is needed here.
        
      The imp_set_dls locale handles the connection to the imperative set ADTs.
  
  *)

  locale imp_DFS = Pair_Graph_Imperative is_map mempty_impl mlookup_impl mupdate_impl
    + s: imp_set_dls is_set sempty_impl smember_impl sins_impl sdel_impl 
    for is_map :: "('v \<rightharpoonup> 'v list) \<Rightarrow> 'gimpl \<Rightarrow> assn"
    and mempty_impl mlookup_impl mupdate_impl
    and is_set :: "'v set \<Rightarrow> 'simpl \<Rightarrow> assn"
    and sempty_impl smember_impl sins_impl sdel_impl 
  begin

    sublocale DFS 
      idm_empty idm_delete 
      dls_insert dls_isin dls_set dls_sel
      idm_update idm_invar
      dls_empty dls_delete dls_invar dls_union dls_inter dls_diff  
      idm_lookup for G :: "'v \<rightharpoonup> 'v list" and s t
      by unfold_locales

      
    subsection \<open>State\<close>
      
    definition "DFS_state_assn s si \<equiv> \<up>(
        stack si = stack s 
      \<and> DFS_state.return si = DFS_state.return s) 
      * s.assn (seen s) (seen si)"
    
    definition "DFS_initial_state_impl s = do {
      seen \<leftarrow> sempty_impl;
      seen \<leftarrow> sins_impl s seen;
      Heap_Monad.return \<lparr> stack = [s], seen = seen, return = NotReachable \<rparr>
    }"

    subsection \<open>Main Algorithm\<close>
    
      
    partial_function (heap) DFS_imperative::"_ \<Rightarrow> _ \<Rightarrow> ('v, 'simpl) DFS_state \<Rightarrow> ('v, 'simpl) DFS_state Heap" where
      "DFS_imperative G t dfs_state = do {
         (case stack dfs_state of (v # stack_tl) \<Rightarrow>
           (if v = t then 
              Heap_Monad.return (dfs_state\<lparr>return:=Reachable\<rparr>)
            else do {
              ns \<leftarrow> neighbourhood_impl G v;
              ns \<leftarrow> s.dls_diff_imp ns (seen dfs_state);
              if ns\<noteq>[] then do {
                let u = dls_sel ns;
                
                let stack' = u# (stack dfs_state);
                seen' \<leftarrow> sins_impl u (seen dfs_state);
                DFS_imperative G t (dfs_state \<lparr>stack := stack', seen := seen' \<rparr>)
              }
              else do {
                DFS_imperative G t (dfs_state \<lparr>stack := stack_tl\<rparr>)
              }
            }
          )
         | _ \<Rightarrow> Heap_Monad.return (dfs_state \<lparr>return := NotReachable\<rparr>)
        )}"
    
  
    lemmas [code] = DFS_imperative.simps DFS_impl.simps initial_state_def
        
    
    lemma DFS_initial_state_rule[sep_heap_rules]: "<emp> DFS_initial_state_impl s <DFS_state_assn (initial_state s)>"
      unfolding DFS_initial_state_impl_def initial_state_def DFS_state_assn_def
      by sep_auto
  
    
    lemma DFS_imperative_rule[sep_heap_rules]: "<graph_assn G Gi * DFS_state_assn dfs_state dfs_statei> DFS_imperative Gi t dfs_statei <\<lambda>ri. graph_assn G Gi * DFS_state_assn (DFS_impl G t dfs_state) ri>"
    proof (induction arbitrary: dfs_state dfs_statei rule: DFS_imperative.fixp_induct)
      case 1
      then show ?case by simp
    next
      case 2
      then show ?case by (simp)
    next
      case (3 f)
      
      (* We face a design decision here:   
      
        Either we unfold the DFS-state assertion during the proof, 
        or we introduce operations (with hoare-triples) for reading and writing the state. 
        The latter choice, though, comes with ownership problems: 
        we cannot simply copy-out and then copy-back heap-based components (except for actually copying), 
        but we would have to reflect this information in the assertions, e.g., two assertions, 
        DFS_state_assn and DFS_state_without_seen_assn.  
      
        The only realistic choices are:
          * unfold DFS_state_assn for the whole proof
          * define specialized operations on state, e.g., \<open>filter_out_seen ls dfs_state\<close>, such that
            these operations do not extract heap-based components. 
            For the proofs of the specialized operations, the state assertion is unfolded.
  
        We decided to unfold the assertion
      *)
      
      
      note IH = "3.IH"[of "\<lparr>stack=stk,seen=sn,return=ret\<rparr>" "\<lparr>stack=stk,seen=sni,return=ret\<rparr>" for stk sn ret sni]
      note IH[sep_heap_rules] = IH[unfolded DFS_state_assn_def, simplified, rule_format]
      
      term ?case
      let "<?P> ?body <\<lambda>r. ?post (DFS_impl G t dfs_state) r>" = ?case
      define P where "P=?P"
      define body where "body=?body"
      define post where "post=?post"
      
      note IMP_DEFS = P_def body_def post_def DFS_state_assn_def
      
      show "<P> body <\<lambda>r. post (DFS_impl G t dfs_state) r>"
        apply (cases dfs_state; cases dfs_statei; simp)
        subgoal for stack seen return stacki seeni returni
          (* Abstract algorithm controls splitting! We split everything at once. *)
          (*<*)apply (rewrite in "<_> _ <\<hole>>" DFS_impl.simps)(*>*)
          apply (clarsimp split!: list.split if_split simp: Let_def) (* This process can be done more manually, using explicit split, cases, etc. *)
          
          (* Now let concrete algorithm follow. Note that we unfold per subgoal, and label the subgoals with comments, for better readability and maintainability *)
          
          subgoal (* stack = [] *)
            unfolding IMP_DEFS by sep_auto
            
          subgoal (* stack = t#_ *)
            unfolding IMP_DEFS by sep_auto
  
          subgoal (* stack = v#_, \<N>\<^sub>G v - seen = {} *)
            (* @M: here we see the implementation bias in DFS_impl: 
              the goal states _ = [], coming from an abstract comparison of concrete values. 
              Cleaner would be an abstract is_empty operation on the set ADT:
                1. it does not assume uniqueness of the data structure representing the empty set
                2. we can safely rewrite \<open>is_empty ds \<longleftrightarrow> set(ds) = {}\<close>, whereas such a rewrite rule for the concrete data structure
                   is typically not compatible with standard simpsets, e.g., adding "xs=[] \<longleftrightarrow> set xs = {}" to the simpset will likely cause havoc on other list based proofs.
  
                Fortunately, in this case, the automation handles the proof nicely. But this is not the norm!
            *)
            unfolding IMP_DEFS by sep_auto
                    
          subgoal (* stack = v#_, \<N>\<^sub>G v - seen \<noteq> {} *)
            unfolding IMP_DEFS by sep_auto
          done
        done
    qed    

    subsection \<open>Algorithm combined with Initial State\<close>
    
    (* DFS is always called on initial state, so it makes sense to define that as a function. 
    
      While 'user-interface' lemmas for the functional implementation might just so work, 
      it gets ughly when not having a single constant to talk about at the monad level.
    *)

    definition "DFS_imperative' G s t \<equiv> do { state\<leftarrow>DFS_initial_state_impl s; DFS_imperative G t state }"
    
lemma DFS_imperative'_rule[sep_heap_rules]: 
        "<graph_assn G Gi> DFS_imperative' Gi s t
           <\<lambda>ri. graph_assn G Gi * DFS_state_assn (DFS_run_impl G s t) ri>"
      unfolding DFS_imperative'_def DFS_run_def DFS_run_impl_def by sep_auto
              

  end  

  
  section \<open>Combined Correctness Theorem\<close>
  
  locale imp_DFS_thms = 
    imp_DFS is_map mempty_impl mlookup_impl mupdate_impl is_set sempty_impl smember_impl sins_impl sdel_impl
  +   
    DFS_thms 
      idm_empty idm_delete 
      dls_insert dls_isin dls_set dls_sel
      idm_update idm_invar
      dls_empty dls_delete dls_invar dls_union dls_inter dls_diff  
      idm_lookup G s t
    for is_map :: "('v \<rightharpoonup> 'v list) \<Rightarrow> 'gimpl \<Rightarrow> assn" and mempty_impl mlookup_impl mupdate_impl 
    and is_set :: "'v set \<Rightarrow> 'simpl \<Rightarrow> assn" and  sempty_impl smember_impl sins_impl sdel_impl
    and G :: "'v \<rightharpoonup> 'v list" and s t
  begin
  

    (* Typically, for the important algorithms, you want a correctness statement that eliminates as much of the intermediate steps as possible.
      I.e., it combines all the refinements, and relates implementation directly with abstract concept.
      
      I've partially done that below. The cleaner solution may be to define a combined assertion 
        is_imp_graph' G Gi = \<exists>\<^sub>AG'. is_imp_graph G' Gi * \<up>(G = digraph_abs G')
      from abstract graphs to imp-graphs, and refactor the lemma below accordingly.
    *)  
    thm DFS_correct_1 DFS_correct_2
  
lemma DFS_imperative'_absrl: 
      "<graph_assn G Gi> DFS_imperative' Gi s t <\<lambda>ri. graph_assn G Gi * \<up>(
      case DFS_state.return ri of
        NotReachable \<Rightarrow> \<nexists>p. distinct p \<and> vwalk_bet (digraph_abs G) s p t
      | Reachable \<Rightarrow> vwalk_bet (digraph_abs G) s (rev (stack (local.DFS G t (initial_state s)))) t
    )>"
      apply sep_auto
      unfolding DFS_state_assn_def
      using DFS_correct_1 DFS_correct_2
      apply (sep_auto 
        split: return.splits 
        simp: DFS_impl_to_DFS DFS_run_impl_def
      )
      done
  
  end
  
  section \<open>Example Instantiations and Execution\<close>
  
  setup Locale_Code.open_block  
  interpretation iam_graph: Pair_Graph_Imperative  
    is_iam iam_new iam_lookup iam_update 
    by unfold_locales
  setup Locale_Code.close_block  

  setup Locale_Code.open_block  
  interpretation iam_dfs: imp_DFS 
    is_iam iam_new iam_lookup iam_update 
    is_ias ias_new ias_memb ias_ins ias_delete
    by unfold_locales
  setup Locale_Code.close_block  
  print_theorems  
   

  setup Locale_Code.open_block  
  interpretation hm_graph: Pair_Graph_Imperative  
    is_hashmap hm_new hm_lookup hm_update 
    by unfold_locales
  setup Locale_Code.close_block  

  setup Locale_Code.open_block  
  interpretation hm_dfs: imp_DFS 
    is_hashmap hm_new hm_lookup hm_update 
    is_hashset hs_new hs_memb hs_ins hs_delete
    by unfold_locales
  setup Locale_Code.close_block  
  print_theorems  
  
  
  type_synonym hnode_t = String.literal
  definition hm_dfs_imp :: "(hnode_t, _) hashtable \<Rightarrow> _" where "hm_dfs_imp = hm_dfs.DFS_imperative"
  definition hm_dfs_initial_state :: "hnode_t \<Rightarrow> _" where "hm_dfs_initial_state = hm_dfs.DFS_initial_state_impl"
  definition  hm_graph_from_list :: "(hnode_t \<times> hnode_t) list \<Rightarrow> _" where "hm_graph_from_list \<equiv> hm_graph.from_list_impl"
  
  export_code hm_dfs_imp hm_dfs_initial_state hm_graph_from_list  checking SML_imp

  ML_val \<open>@{code hm_dfs_imp}\<close>
  
  ML_val \<open>
    val dfs_init = @{code hm_dfs_initial_state}
    val dfs = @{code hm_dfs_imp}
    val graph_from_list = @{code hm_graph_from_list}
  
    
    
    val g = graph_from_list [("start","a"),("b","a"),("a","end")] ()
    val s = dfs_init "start" ()
    val r = dfs g "end" s ()
  \<close>
  

  
  
  
                                     
  definition "iam_dfs_imp = iam_dfs.DFS_imperative"
  definition "iam_dfs_initial_state = iam_dfs.DFS_initial_state_impl"
  definition "iam_graph_from_list \<equiv> iam_graph.from_list_impl"
  definition "sstack \<equiv> DFS_state.stack"
  definition "sseen \<equiv> DFS_state.stack"
  definition "rreturn \<equiv> DFS_state.return"
  definition "rreachable \<equiv> return.Reachable"
  definition "not_reachable \<equiv> return.NotReachable"

  definition "iam_dfs_fun = iam_dfs.DFS_impl"
  definition "iam_dfs_initial_state_fun = iam_dfs.initial_state"

  type_synonym hinode_t = nat
  definition him_dfs_imp :: "(hinode_t, _) hashtable \<Rightarrow> _" where "him_dfs_imp = hm_dfs.DFS_imperative"
  definition him_dfs_initial_state :: "hinode_t \<Rightarrow> _" where "him_dfs_initial_state = hm_dfs.DFS_initial_state_impl"
  definition  him_graph_from_list :: "(hinode_t \<times> hinode_t) list \<Rightarrow> _" where "him_graph_from_list \<equiv> hm_graph.from_list_impl"

definition "rbt_dfs_initial_state = (dfs_initial_state::nat \<Rightarrow> (nat, (nat \<times> color) tree) DFS_state)"
definition "rbt_add_edge = (add_edge::((nat \<times> (nat \<times> color) tree) \<times> color) tree
     \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ((nat \<times> (nat \<times> color) tree) \<times> color) tree)"
definition "rbt_dfs_impl = (dfs_impl::((nat \<times> (nat \<times> color) tree) \<times> color) tree
     \<Rightarrow> nat \<Rightarrow> (nat, (nat \<times> color) tree) DFS_state \<Rightarrow> (nat, (nat \<times> color) tree) DFS_state)"
definition "rbt_neighbourhood =(neighbourhood::((nat \<times> (nat \<times> color) tree) \<times> color) tree \<Rightarrow> nat \<Rightarrow> (nat \<times> color) tree)"
definition "rbt_from_list = (from_list::(nat \<times> nat) list \<Rightarrow> ((nat \<times> (nat \<times> color) tree) \<times> color) tree)"

  find_theorems iam_dfs.DFS_impl

export_code iam_dfs_imp iam_dfs_initial_state iam_graph_from_list 

hm_dfs_imp hm_dfs_initial_state hm_graph_from_list 

him_dfs_imp him_dfs_initial_state him_graph_from_list 

sstack sseen rreturn rreachable not_reachable

nat_of_integer integer_of_nat

rbt_dfs_initial_state rbt_neighbourhood rbt_dfs_impl rbt_add_edge
rbt_from_list

in SML_imp module_name exported file_prefix DFS_imperative
(* checking SML_imp*)

  ML_val \<open>
    val noi = @{code nat_of_integer}
    val dfs_init = @{code iam_dfs_initial_state}
    val dfs = @{code iam_dfs_imp}
    val graph_from_list = @{code iam_graph_from_list} o map (apply2 noi)
    
    val g = graph_from_list [(0,1),(1,2),(2,3),(3,1),(4,1)] ()
    val s = dfs_init (noi 0) ()
    val r = dfs g (noi 3) s ()

    val rbt_from_list = @{code rbt_from_list}o map (apply2 noi)
    val g' = rbt_from_list [(0,1),(1,2),(2,3),(3,1),(4,1)]

    val higraph_from_list = @{code him_graph_from_list} o map (apply2 noi)
    val g'' =  higraph_from_list [(0,1),(1,2),(2,3),(3,1),(4,1)]
  \<close>
  
end