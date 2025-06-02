(*MOVE to Graph_Algorithms_Dev?*)
theory DFS_Collect_Backtrack
  imports  Graph_Algorithms_Dev.DFS
begin 

record ('ver, 'vset) DFS_backtrack_state = stack:: "'ver list" seen:: "'vset"  return:: return 
  backtrack::"('ver \<times> 'ver) list"

abbreviation "to_ordinary_DFS_state (state::('ver, 'vset) DFS_backtrack_state) ==
              \<lparr>DFS_state.stack = stack state, DFS_state.seen = seen state, DFS_state.return = return state \<rparr>"

context DFS
begin

function (domintros) DFS_collect_backtrack::"('v, 'vset) DFS_backtrack_state \<Rightarrow> ('v, 'vset) DFS_backtrack_state" where
  "DFS_collect_backtrack dfs_state = 
     (case (stack dfs_state) of (v # stack_tl) \<Rightarrow>
       (if v = t then 
          (dfs_state \<lparr>return := Reachable\<rparr>)
        else ((if (\<N>\<^sub>G v -\<^sub>G (seen dfs_state)) \<noteq> \<emptyset>\<^sub>N then
                  let u = (sel ((\<N>\<^sub>G v) -\<^sub>G (seen dfs_state)));
                      stack' = u# (stack dfs_state);
                      seen' = insert u (seen dfs_state)                      
                  in
                    (DFS_collect_backtrack (dfs_state \<lparr>stack := stack',   seen := seen' \<rparr>))
                else
                  let stack' = stack_tl;
                      backtrack = backtrack dfs_state;
                      backtrack'=(case stack' of [] \<Rightarrow> backtrack | (x#xs) \<Rightarrow> (x, v)#backtrack)
                   in
                      DFS_collect_backtrack (dfs_state \<lparr>stack := stack', backtrack := backtrack'\<rparr>))
              )
      )
     | _ \<Rightarrow> (dfs_state \<lparr>return := NotReachable\<rparr>)
    )"
  by pat_completeness auto

partial_function (tailrec) DFS_collect_backtrack_impl::"('v, 'vset) DFS_backtrack_state \<Rightarrow> ('v, 'vset) DFS_backtrack_state" where
  "DFS_collect_backtrack_impl dfs_state = 
     (case (stack dfs_state) of (v # stack_tl) \<Rightarrow>
       (if v = t then 
          (dfs_state \<lparr>return := Reachable\<rparr>)
        else ((if (\<N>\<^sub>G v -\<^sub>G (seen dfs_state)) \<noteq> \<emptyset>\<^sub>N then
                  let u = (sel ((\<N>\<^sub>G v) -\<^sub>G (seen dfs_state)));
                      stack' = u# (stack dfs_state);
                      seen' = insert u (seen dfs_state)                      
                  in
                    (DFS_collect_backtrack_impl (dfs_state \<lparr>stack := stack',   seen := seen' \<rparr>))
                else
                  let stack' = stack_tl;
                      backtrack = backtrack dfs_state;
                      backtrack'=(case stack' of [] \<Rightarrow> backtrack | (x#xs) \<Rightarrow> (x, v)#backtrack)
                   in
                      DFS_collect_backtrack_impl (dfs_state \<lparr>stack := stack', backtrack := backtrack'\<rparr>))
              ))
     | _ \<Rightarrow> (dfs_state \<lparr>return := NotReachable\<rparr>))"

lemma DFS_collect_backtrack_impl_same: 
  assumes "DFS_collect_backtrack_dom state"
  shows   "DFS_collect_backtrack_impl state = DFS_collect_backtrack state"
  by(induction rule: DFS_collect_backtrack.pinduct[OF assms])
    (auto split: list.split simp add: DFS_collect_backtrack.psimps DFS_collect_backtrack_impl.simps)

definition "dfs_backtrack_initial_state = \<lparr>stack = [s], seen = insert s \<emptyset>\<^sub>N, return = NotReachable, backtrack=Nil\<rparr>"

lemmas [code] = DFS_collect_backtrack_impl.simps dfs_backtrack_initial_state_def

lemma dfs_backtrack_initial_state_to_ordinary_same: 
  "to_ordinary_DFS_state dfs_backtrack_initial_state = initial_state"
  by(auto simp add: dfs_backtrack_initial_state_def initial_state_def)

definition "DFS_backtrack_upd1 dfs_state = (
    let
      N = (\<N>\<^sub>G (hd (stack dfs_state)));
      u = (sel ((N -\<^sub>G (seen dfs_state))));
      stack' = u # (stack dfs_state);
      seen' = insert u (seen dfs_state)
    in
      dfs_state \<lparr>stack := stack', seen := seen'\<rparr>)" 

lemma DFS_backtrack_upd1_homo:
  "to_ordinary_DFS_state (DFS_backtrack_upd1 dfs_state) = 
 DFS_upd1 (to_ordinary_DFS_state  dfs_state)"
  by(auto simp add: DFS_backtrack_upd1_def DFS_upd1_def Let_def)

definition "DFS_backtrack_upd2 dfs_state = 
  ((dfs_state \<lparr>stack := tl (stack dfs_state),
        backtrack := (case (tl (stack dfs_state)) of Nil \<Rightarrow> backtrack dfs_state
              | (x#xs) \<Rightarrow> (x, hd (stack dfs_state)) # backtrack dfs_state)\<rparr>))"

lemma DFS_backtrack_upd2_cases:
  "( (tl (stack dfs_state)) = Nil \<Longrightarrow> P ((dfs_state \<lparr>stack := tl (stack dfs_state)\<rparr>))) \<Longrightarrow>
    (\<And> x xs. (tl (stack dfs_state)) = x#xs 
              \<Longrightarrow> P(dfs_state \<lparr>stack := tl (stack dfs_state), backtrack :=  (x, hd (stack dfs_state)) # backtrack dfs_state\<rparr>))
  \<Longrightarrow> P (DFS_backtrack_upd2 dfs_state)"
  by(auto simp add: DFS_backtrack_upd2_def 
      intro: list.exhaust[of "tl (DFS_backtrack_state.stack dfs_state)"])

lemma DFS_backtrack_upd2_homo:
  "to_ordinary_DFS_state (DFS_backtrack_upd2 dfs_state) = 
 DFS_upd2 (to_ordinary_DFS_state  dfs_state)"
  by(auto simp add: DFS_backtrack_upd2_def DFS_upd2_def Let_def)

definition "DFS_backtrack_ret1 dfs_state = (dfs_state \<lparr>return := NotReachable\<rparr>)"

lemma DFS_backtrack_ret1_homo:
  "to_ordinary_DFS_state (DFS_backtrack_ret1 dfs_state) = 
 DFS_ret1 (to_ordinary_DFS_state  dfs_state)"
  by(auto simp add: DFS_backtrack_ret1_def DFS_ret1_def Let_def)

definition "DFS_backtrack_ret2 dfs_state = (dfs_state \<lparr>return := Reachable\<rparr>)"

lemma DFS_backtrack_ret2_homo:
  "to_ordinary_DFS_state (DFS_backtrack_ret2 dfs_state) = 
 DFS_ret2 (to_ordinary_DFS_state  dfs_state)"
  by(auto simp add: DFS_backtrack_ret2_def DFS_ret2_def Let_def)

lemmas DFS_backtrack_cases = DFS_cases[of "to_ordinary_DFS_state dfs_state" for dfs_state]

lemma DFS_backtrack_simps:
  assumes "DFS_collect_backtrack_dom dfs_state" 
  shows"DFS_call_1_conds (to_ordinary_DFS_state dfs_state)
            \<Longrightarrow> DFS_collect_backtrack dfs_state = DFS_collect_backtrack (DFS_backtrack_upd1 dfs_state)"
    "DFS_call_2_conds (to_ordinary_DFS_state dfs_state) 
            \<Longrightarrow> DFS_collect_backtrack dfs_state = DFS_collect_backtrack (DFS_backtrack_upd2 dfs_state)"
    "DFS_ret_1_conds (to_ordinary_DFS_state dfs_state) 
            \<Longrightarrow> DFS_collect_backtrack dfs_state = DFS_backtrack_ret1 dfs_state"
    "DFS_ret_2_conds  (to_ordinary_DFS_state dfs_state) 
           \<Longrightarrow> DFS_collect_backtrack dfs_state = DFS_backtrack_ret2 dfs_state"
  by (auto simp add: DFS_collect_backtrack.psimps[OF assms] Let_def
      DFS_call_1_conds_def DFS_backtrack_upd1_def DFS_call_2_conds_def 
      DFS_backtrack_upd2_def
      DFS_ret_1_conds_def DFS_backtrack_ret1_def
      DFS_ret_2_conds_def DFS_backtrack_ret2_def                    
      split: list.splits option.splits if_splits)

lemma DFS_backtrack_induct: 
  assumes "DFS_collect_backtrack_dom dfs_state"
  assumes "\<And>dfs_state. \<lbrakk>DFS_collect_backtrack_dom dfs_state;
                        DFS_call_1_conds (to_ordinary_DFS_state dfs_state) 
                         \<Longrightarrow> P (DFS_backtrack_upd1 dfs_state);
                        DFS_call_2_conds (to_ordinary_DFS_state dfs_state) 
                         \<Longrightarrow> P (DFS_backtrack_upd2 dfs_state)\<rbrakk> \<Longrightarrow> P dfs_state"
  shows "P dfs_state"
  apply(rule DFS_collect_backtrack.pinduct[OF assms(1)])
  apply(rule assms(2)[simplified DFS_call_1_conds_def DFS_backtrack_upd1_def 
        DFS_call_2_conds_def DFS_backtrack_upd2_def])
  by (auto simp: Let_def split: list.splits option.splits if_splits)

lemma dom_same: "DFS_dom (to_ordinary_DFS_state dfs_state) \<Longrightarrow> DFS_collect_backtrack_dom dfs_state" (is "?goal2 \<Longrightarrow> ?goal1")
  and  "DFS_collect_backtrack_dom dfs_state \<Longrightarrow> DFS_dom (to_ordinary_DFS_state dfs_state)" (is "?goal1 \<Longrightarrow> ?goal2")
  and  "DFS_dom (to_ordinary_DFS_state dfs_state) = DFS_collect_backtrack_dom dfs_state"   (is ?goal3)
proof-
  have "old_state = (to_ordinary_DFS_state dfs_state)
           \<Longrightarrow> DFS_collect_backtrack_dom dfs_state" 
    if asm: "DFS_dom old_state"for old_state
    by(induction arbitrary: dfs_state rule: DFS.pinduct[OF asm])
      (auto intro: DFS_collect_backtrack.domintros)
  moreover have "old_state = (to_ordinary_DFS_state dfs_state)
           \<Longrightarrow> DFS_dom old_state" 
    if asm: " DFS_collect_backtrack_dom dfs_state"for old_state
    by(induction arbitrary: old_state rule: DFS_collect_backtrack.pinduct[OF asm])
      (auto intro: DFS.domintros) 
  ultimately show "?goal2 \<Longrightarrow> ?goal1" and "?goal1 \<Longrightarrow> ?goal2" and ?goal3
    by auto
qed

definition "invar_dfs_backtrack_1 state = ((dVs (set (backtrack state))) \<subseteq> t_set (seen state))"

definition "invar_dfs_backtrack_2 state = ((set (backtrack state)) \<subseteq> Graph.digraph_abs G)"

definition "invar_dfs_backtrack_3 state = ( set (backtrack state) \<inter> set (edges_of_vwalk (rev (stack state))) = {})"

definition "invar_dfs_backtrack_4 state = (distinct (backtrack state))"

definition "invar_dfs_backtrack_5 state = (\<forall> e \<in> set (backtrack state). 
                            \<nexists> p.  e \<in> set (edges_of_vwalk p) \<and> 
                            Vwalk.vwalk_bet (Graph.digraph_abs G) s p t)"

lemma invar_dfs_backtrack_1I: "((dVs (set (backtrack state))) \<subseteq> t_set (seen state)) \<Longrightarrow> invar_dfs_backtrack_1 state"
  by(auto simp add: invar_dfs_backtrack_1_def)

lemma invar_dfs_backtrack_1E: "invar_dfs_backtrack_1 state \<Longrightarrow> 
                      (((dVs (set (backtrack state))) \<subseteq> t_set (seen state)) \<Longrightarrow> P) \<Longrightarrow> P"
  by(auto simp add: invar_dfs_backtrack_1_def)

lemma invar_dfs_backtrack_2I: " ((set (backtrack state)) \<subseteq> Graph.digraph_abs G) \<Longrightarrow> invar_dfs_backtrack_2 state"
  by(auto simp add: invar_dfs_backtrack_2_def)

lemma invar_dfs_backtrack_2E: " invar_dfs_backtrack_2 state \<Longrightarrow>
           (((set (backtrack state)) \<subseteq> Graph.digraph_abs G) \<Longrightarrow>P) \<Longrightarrow> P"
  by(auto simp add: invar_dfs_backtrack_2_def)

lemma invar_dfs_backtrack_3I:"set (backtrack state) \<inter> set (edges_of_vwalk (rev (stack state))) = {} \<Longrightarrow> invar_dfs_backtrack_3 state"
  by(auto simp add: invar_dfs_backtrack_3_def)

lemma invar_dfs_backtrack_3E:"invar_dfs_backtrack_3 state \<Longrightarrow>
        (set (backtrack state) \<inter> set (edges_of_vwalk (rev (stack state))) = {} \<Longrightarrow> P) \<Longrightarrow> P"
  by(auto simp add: invar_dfs_backtrack_3_def)

lemma invar_dfs_backtrack_4I: "distinct (backtrack state) \<Longrightarrow> invar_dfs_backtrack_4 state"
  by(auto simp add: invar_dfs_backtrack_4_def)

lemma invar_dfs_backtrack_4E: "invar_dfs_backtrack_4 state \<Longrightarrow> (distinct (backtrack state) \<Longrightarrow> P) \<Longrightarrow> P"
  by(auto simp add: invar_dfs_backtrack_4_def)

lemma invar_dfs_backtrack_5I: "(\<And> e. e \<in> set (backtrack state) \<Longrightarrow>  
                            \<nexists> p.  e \<in> set (edges_of_vwalk p) \<and> 
                            Vwalk.vwalk_bet (Graph.digraph_abs G) s p t) \<Longrightarrow> invar_dfs_backtrack_5 state"
  by(auto simp add: invar_dfs_backtrack_5_def)

lemma invar_dfs_backtrack_5E: "invar_dfs_backtrack_5 state \<Longrightarrow> ((\<And> e. e \<in> set (backtrack state) \<Longrightarrow>  
                            \<nexists> p. e \<in> set (edges_of_vwalk p) \<and> 
                            Vwalk.vwalk_bet (Graph.digraph_abs G) s p t) \<Longrightarrow> P) \<Longrightarrow> P"
  by(auto simp add: invar_dfs_backtrack_5_def)

lemma same_as_old_dfs: 
  assumes "DFS_dom state"
          "to_ordinary_DFS_state dfs_state = state"
  shows "(to_ordinary_DFS_state (DFS_collect_backtrack dfs_state)) 
                = DFS state"
  using assms(2)
proof(induction arbitrary: dfs_state rule: DFS_induct[OF assms(1)])
  case (1 dfs_state state)
  note IH=this
  note backtrack_dom = dom_same[OF IH(1)[simplified IH(4)[symmetric]]]
  show ?case
    using DFS_simps[OF IH(1)] 
    by (cases dfs_state rule: DFS_cases) 
       (auto simp add: "1.prems" DFS_backtrack_ret1_homo backtrack_dom DFS_backtrack_ret2_homo
                       DFS_backtrack_simps DFS_backtrack_upd2_homo  IH(2,3) DFS_backtrack_upd1_homo)
qed

end

context DFS_thms
begin
context
  includes set_ops.automation and Graph.adjmap.automation and Graph.vset.set.automation 
begin

lemma invar_dfs_backtrack_1_holds_1[invar_holds_intros]:
  "\<lbrakk>DFS_call_1_conds (to_ordinary_DFS_state dfs_state); invar_dfs_backtrack_1 dfs_state;
       invar_1 (to_ordinary_DFS_state dfs_state)\<rbrakk> \<Longrightarrow> 
      invar_dfs_backtrack_1 (DFS_backtrack_upd1 dfs_state)"
  by(auto intro!: invar_dfs_backtrack_1I simp add: DFS_backtrack_upd1_def Let_def
      elim!: DFS_call_1_conds invar_dfs_backtrack_1E invar_1_props)

lemma invar_dfs_backtrack_1_holds_2[invar_holds_intros]:
  "\<lbrakk>DFS_call_2_conds (to_ordinary_DFS_state dfs_state); invar_dfs_backtrack_1 dfs_state;
       invar_1 (to_ordinary_DFS_state dfs_state);
       invar_seen_stack (to_ordinary_DFS_state dfs_state)\<rbrakk> \<Longrightarrow>
      invar_dfs_backtrack_1 (DFS_backtrack_upd2 dfs_state)"
  by(rule  DFS_backtrack_upd2_cases)
    (auto intro!: invar_dfs_backtrack_1I 
      simp add: DFS_backtrack_upd2_def Let_def
      elim!: DFS_call_2_conds invar_dfs_backtrack_1E invar_1_props invar_seen_stack_props)+

lemma invar_dfs_backtrack_1_holds_3[invar_holds_intros]:
  "\<lbrakk>invar_dfs_backtrack_1 dfs_state\<rbrakk> \<Longrightarrow> 
      invar_dfs_backtrack_1 (DFS_backtrack_ret1 dfs_state)"
  by(auto intro!: invar_dfs_backtrack_1I simp add: DFS_backtrack_ret1_def elim!: invar_dfs_backtrack_1E)

lemma invar_dfs_backtrack_1_holds_4[invar_holds_intros]:
  "\<lbrakk>invar_dfs_backtrack_1 dfs_state\<rbrakk> \<Longrightarrow> 
      invar_dfs_backtrack_1 (DFS_backtrack_ret2 dfs_state)"
  by(auto intro!: invar_dfs_backtrack_1I simp add: DFS_backtrack_ret2_def elim!: invar_dfs_backtrack_1E)

lemma invar_dfs_backtrack_1_holds: 
  assumes "DFS_collect_backtrack_dom dfs_state" "invar_dfs_backtrack_1 dfs_state"
    "invar_1 (to_ordinary_DFS_state dfs_state)"
    "invar_seen_stack (to_ordinary_DFS_state dfs_state)"
  shows "invar_dfs_backtrack_1 (DFS_collect_backtrack dfs_state)"
  using assms(2-)
proof(induction rule: DFS_backtrack_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule DFS_backtrack_cases[where dfs_state = dfs_state])
    by(auto intro!: IH(2-) invar_holds_intros 
        simp: DFS_backtrack_simps[OF IH(1)] DFS_backtrack_upd1_homo DFS_backtrack_upd2_homo)
qed

lemma invar_dfs_backtrack_2_holds_1[invar_holds_intros]:
  "\<lbrakk>DFS_call_1_conds (to_ordinary_DFS_state dfs_state); invar_dfs_backtrack_2 dfs_state;
       invar_1 (to_ordinary_DFS_state dfs_state)\<rbrakk> \<Longrightarrow> 
      invar_dfs_backtrack_2 (DFS_backtrack_upd1 dfs_state)"
  by(auto intro!: invar_dfs_backtrack_2I simp add: DFS_backtrack_upd1_def Let_def
      elim!: DFS_call_1_conds invar_dfs_backtrack_2E invar_1_props)

lemma invar_dfs_backtrack_2_holds_2[invar_holds_intros]:
  "\<lbrakk>DFS_call_2_conds (to_ordinary_DFS_state dfs_state); invar_dfs_backtrack_2 dfs_state;
       invar_1 (to_ordinary_DFS_state dfs_state);
       invar_2 (to_ordinary_DFS_state dfs_state)\<rbrakk> \<Longrightarrow>
      invar_dfs_backtrack_2 (DFS_backtrack_upd2 dfs_state)"
  apply(rule  DFS_backtrack_upd2_cases)
  using append_vwalk_suff 
  by(fastforce intro!: invar_dfs_backtrack_2I 
      simp add: DFS_backtrack_upd2_def Let_def
      elim!: DFS_call_2_conds invar_dfs_backtrack_2E invar_1_props invar_2_props)+

lemma invar_dfs_backtrack_2_holds_3[invar_holds_intros]:
  "\<lbrakk>invar_dfs_backtrack_2 dfs_state\<rbrakk> \<Longrightarrow> 
      invar_dfs_backtrack_2 (DFS_backtrack_ret1 dfs_state)"
  by(auto intro!: invar_dfs_backtrack_2I simp add: DFS_backtrack_ret1_def elim!: invar_dfs_backtrack_2E)

lemma invar_dfs_backtrack_2_holds_4[invar_holds_intros]:
  "\<lbrakk>invar_dfs_backtrack_2 dfs_state\<rbrakk> \<Longrightarrow> 
      invar_dfs_backtrack_2 (DFS_backtrack_ret2 dfs_state)"
  by(auto intro!: invar_dfs_backtrack_2I simp add: DFS_backtrack_ret2_def elim!: invar_dfs_backtrack_2E)

lemma invar_dfs_backtrack_2_holds: 
  assumes "DFS_collect_backtrack_dom dfs_state" "invar_dfs_backtrack_2 dfs_state"
    "invar_1 (to_ordinary_DFS_state dfs_state)"
    "invar_2 (to_ordinary_DFS_state dfs_state)"
  shows  "invar_dfs_backtrack_2 (DFS_collect_backtrack dfs_state)"
  using assms(2-)
proof(induction rule: DFS_backtrack_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule DFS_backtrack_cases[where dfs_state = dfs_state])
    by(auto intro!: IH(2-) invar_holds_intros 
        simp: DFS_backtrack_simps[OF IH(1)] DFS_backtrack_upd1_homo DFS_backtrack_upd2_homo)
qed

lemma invar_dfs_backtrack_3_holds_1[invar_holds_intros]:
  "\<lbrakk>DFS_call_1_conds (to_ordinary_DFS_state dfs_state); invar_dfs_backtrack_3 dfs_state;
       invar_dfs_backtrack_1 dfs_state;
       invar_1 (to_ordinary_DFS_state dfs_state);
        invar_seen_stack (to_ordinary_DFS_state dfs_state)\<rbrakk> \<Longrightarrow> 
      invar_dfs_backtrack_3 (DFS_backtrack_upd1 dfs_state)"
  by(auto intro!: invar_dfs_backtrack_3I
      simp add: DFS_backtrack_upd1_def Let_def
      edges_of_vwalk_append_2[of "[_, _]", simplified]
      elim!: DFS_call_1_conds invar_dfs_backtrack_3E invar_1_props invar_seen_stack_props
      invar_dfs_backtrack_1E
      dest!: Graph.vset.choose')+

lemma invar_dfs_backtrack_3_holds_2[invar_holds_intros]:
  "\<lbrakk>DFS_call_2_conds (to_ordinary_DFS_state dfs_state);
       invar_dfs_backtrack_3 dfs_state;
       invar_1 (to_ordinary_DFS_state dfs_state);
       invar_seen_stack (to_ordinary_DFS_state dfs_state)\<rbrakk> \<Longrightarrow>
      invar_dfs_backtrack_3 (DFS_backtrack_upd2 dfs_state)"
  using v_in_edge_in_vwalk(2) 
  by (cases rule:  DFS_backtrack_upd2_cases)
    (fastforce intro!: invar_dfs_backtrack_3I 
      simp add: DFS_backtrack_upd2_def Let_def edges_of_vwalk_append_2[of "[_, _]", simplified]
      elim!: DFS_call_2_conds  invar_dfs_backtrack_3E invar_1_props invar_seen_stack_props)+

lemma invar_dfs_backtrack_3_holds_3[invar_holds_intros]:
  "\<lbrakk>invar_dfs_backtrack_3 dfs_state\<rbrakk> \<Longrightarrow> 
      invar_dfs_backtrack_3 (DFS_backtrack_ret1 dfs_state)"
  by(auto intro!: invar_dfs_backtrack_3I simp add: DFS_backtrack_ret1_def elim!: invar_dfs_backtrack_3E)

lemma invar_dfs_backtrack_3_holds_4[invar_holds_intros]:
  "\<lbrakk>invar_dfs_backtrack_3 dfs_state\<rbrakk> \<Longrightarrow> 
      invar_dfs_backtrack_3 (DFS_backtrack_ret2 dfs_state)"
  by(auto intro!: invar_dfs_backtrack_3I simp add: DFS_backtrack_ret2_def elim!: invar_dfs_backtrack_3E)

lemma invar_dfs_backtrack_3_holds: 
  assumes "DFS_collect_backtrack_dom dfs_state" "invar_dfs_backtrack_3 dfs_state"
    "invar_dfs_backtrack_1 dfs_state"
    "invar_1 (to_ordinary_DFS_state dfs_state)"
    "invar_seen_stack (to_ordinary_DFS_state dfs_state)"
  shows  "invar_dfs_backtrack_3 (DFS_collect_backtrack dfs_state)"
  using assms(2-)
proof(induction rule: DFS_backtrack_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule DFS_backtrack_cases[where dfs_state = dfs_state])
    by(auto intro!: IH(2-) invar_holds_intros 
        simp: DFS_backtrack_simps[OF IH(1)] DFS_backtrack_upd1_homo DFS_backtrack_upd2_homo)
qed

lemma invar_dfs_backtrack_4_holds_1[invar_holds_intros]:
  "\<lbrakk>DFS_call_1_conds (to_ordinary_DFS_state dfs_state); invar_dfs_backtrack_4 dfs_state\<rbrakk> \<Longrightarrow> 
      invar_dfs_backtrack_4 (DFS_backtrack_upd1 dfs_state)"
  by(auto intro!: invar_dfs_backtrack_4I
      simp add: DFS_backtrack_upd1_def Let_def
      elim!:  invar_dfs_backtrack_4E)

lemma invar_dfs_backtrack_4_holds_2[invar_holds_intros]:
  "\<lbrakk>DFS_call_2_conds (to_ordinary_DFS_state dfs_state);
       invar_dfs_backtrack_4 dfs_state;
       invar_dfs_backtrack_3 dfs_state\<rbrakk> \<Longrightarrow>
      invar_dfs_backtrack_4 (DFS_backtrack_upd2 dfs_state)"
  by(cases rule:  DFS_backtrack_upd2_cases)
    (auto intro!: invar_dfs_backtrack_4I 
      simp add: DFS_backtrack_upd2_def Let_def edges_of_vwalk_append_2[of "[_, _]", simplified]
      elim!: DFS_call_2_conds  invar_dfs_backtrack_3E  invar_dfs_backtrack_4E)

lemma invar_dfs_backtrack_4_holds_3[invar_holds_intros]:
  "\<lbrakk>invar_dfs_backtrack_4 dfs_state\<rbrakk> \<Longrightarrow> 
      invar_dfs_backtrack_4 (DFS_backtrack_ret1 dfs_state)"
  by(auto intro!: invar_dfs_backtrack_4I simp add: DFS_backtrack_ret1_def elim!: invar_dfs_backtrack_4E)

lemma invar_dfs_backtrack_4_holds_4[invar_holds_intros]:
  "\<lbrakk>invar_dfs_backtrack_4 dfs_state\<rbrakk> \<Longrightarrow> 
      invar_dfs_backtrack_4 (DFS_backtrack_ret2 dfs_state)"
  by(auto intro!: invar_dfs_backtrack_4I simp add: DFS_backtrack_ret2_def elim!: invar_dfs_backtrack_4E)

lemma invar_dfs_backtrack_4_holds: 
  assumes "DFS_collect_backtrack_dom dfs_state" "invar_dfs_backtrack_4 dfs_state" 
    "invar_dfs_backtrack_3 dfs_state"
    "invar_dfs_backtrack_1 dfs_state"
    "invar_1 (to_ordinary_DFS_state dfs_state)"
    "invar_seen_stack (to_ordinary_DFS_state dfs_state)"
  shows  "invar_dfs_backtrack_4 (DFS_collect_backtrack dfs_state)"
  using assms(2-)
proof(induction rule: DFS_backtrack_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule DFS_backtrack_cases[where dfs_state = dfs_state])
    by(auto intro!: IH(2-) invar_holds_intros 
        simp: DFS_backtrack_simps[OF IH(1)] DFS_backtrack_upd1_homo DFS_backtrack_upd2_homo)
qed

lemma invar_dfs_backtrack_5_holds_1[invar_holds_intros]:
  "\<lbrakk>DFS_call_1_conds (to_ordinary_DFS_state dfs_state); invar_dfs_backtrack_5 dfs_state\<rbrakk> \<Longrightarrow> 
      invar_dfs_backtrack_5 (DFS_backtrack_upd1 dfs_state)"
  by(auto intro!: invar_dfs_backtrack_5I
      simp add: DFS_backtrack_upd1_def Let_def
      elim!:  invar_dfs_backtrack_5E)

lemma invar_dfs_backtrack_5_holds_2[invar_holds_intros]:
  assumes "DFS_call_2_conds (to_ordinary_DFS_state dfs_state)"
    "\<nexists> p v. vwalk_bet (Graph.digraph_abs G) v p v \<and> length p \<ge> 2"
    "invar_dfs_backtrack_5 dfs_state"
    "invar_dfs_backtrack_4 dfs_state"
    "invar_dfs_backtrack_3 dfs_state"
    "invar_dfs_backtrack_1 dfs_state"
    "invar_seen_stack (to_ordinary_DFS_state dfs_state)"
    "invar_visited_through_seen (to_ordinary_DFS_state dfs_state)"
    "invar_1 (to_ordinary_DFS_state dfs_state)"
    "invar_2 (to_ordinary_DFS_state dfs_state)"
  shows  "invar_dfs_backtrack_5 (DFS_backtrack_upd2 dfs_state)"
proof(insert assms(3-), rule DFS_call_2_conds[OF assms(1)], cases rule:  DFS_backtrack_upd2_cases, goal_cases)
  case 1
  then show ?case
    by(auto intro!: invar_dfs_backtrack_5I 
        simp add: DFS_backtrack_upd2_def Let_def
        elim!:  invar_dfs_backtrack_5E )
next
  case (2 u tail)
  note two = 2
  show ?case
  proof(rule invar_dfs_backtrack_5I, clarsimp simp add: 2, goal_cases)
    case (1 a b p)
    note one = this
    show ?case 
    proof(cases rule: disjE[OF 1(1)])
      case 1
      hence 1: "a = u" "b = hd (DFS_backtrack_state.stack dfs_state)" by auto
      hence "b \<in> set p" using one(2) v_in_edge_in_vwalk_gen(2) by force
      then obtain p1 p2 where p_split: "p = p1@[b]@p2"
        by(auto simp add: in_set_conv_decomp)
      have p2_no_empty: "p2 \<noteq> []"
        using p_split one(3) 1(2) two(10)
        by (auto simp add: vwalk_bet_snoc)
      hence "vwalk_bet [G]\<^sub>g b (b#p2) t"
        using one(3)
        by (simp add: p_split vwalk_bet_suff) 
      then obtain p2' where "vwalk_bet [G]\<^sub>g b (p2') t" "distinct p2'"
        by(auto dest!: vwalk_bet_to_distinct_is_distinct_vwalk_bet
            simp add: distinct_vwalk_bet_def)
      moreover have "b \<in> t_set (seen dfs_state)" 
        using two 2(5) 1(2)
        by(auto elim!: invar_seen_stack_props invar_dfs_backtrack_1E)
      moreover have "DFS_state.stack (to_ordinary_DFS_state dfs_state) = stack dfs_state" 
        by simp
      ultimately have "set (tl (DFS_backtrack_state.stack dfs_state)) \<inter> set (p2') \<noteq> {}"
        using invar_visited_through_seen_holds_2[OF assms(1) two(7,5,6)]
        by(fastforce simp add: invar_visited_through_seen_def DFS_upd2_def)
      then obtain x where x_prop: "x \<in> set (tl (DFS_backtrack_state.stack dfs_state)) \<inter> set (p2')"
        by auto
      then obtain stck1 stck2 where stack_split:"tl (DFS_backtrack_state.stack dfs_state) = stck1@[x]@stck2"
        by(auto simp add: in_set_conv_decomp)
      have vwalk_stack: "Vwalk.vwalk   [G]\<^sub>g (rev (DFS_backtrack_state.stack dfs_state))" 
        using two
        by (simp add: invar_2_def)
      obtain pp1 pp2 where "p2'  = pp1@[x]@pp2"
        using IntD2[OF x_prop, simplified in_set_conv_decomp] by auto
      hence walk_b_x:"vwalk_bet [G]\<^sub>g b (pp1@[x]) x" 
        using  \<open>vwalk_bet [G]\<^sub>g b (p2') t\<close> vwalk_bet_pref by force
      have "Vwalk.vwalk   [G]\<^sub>g (x#rev stck1)" 
        using vwalk_stack  stack_split  two(9) 
        by (force intro:  append_vwalk_suff[of _ "rev stck2"] 
            append_vwalk_pref[of _ _ "[hd (DFS_backtrack_state.stack dfs_state)]"])
      hence walk_x_u:"vwalk_bet [G]\<^sub>g x (x#rev stck1) u"   
        using stack_split[symmetric] two(12) hd_append2[of "stck1@[x]" stck2, simplified] last_rev
        by (auto simp add: vwalk_bet_def )
      have walk_u_b:"vwalk_bet [G]\<^sub>g u [u, b] b" 
        using  "1"(1) edges_are_vwalk_bet one(2,3) 
        by(auto elim!: vwalk_bet_props intro: vwalk_ball_edges)
      have "vwalk_bet  [G]\<^sub>g u (u#pp1@[x]@ rev stck1) u"
        by(auto intro!: vwalk_bet_transitive_2[OF walk_u_b, simplified] 
            vwalk_bet_transitive_2[OF walk_b_x, simplified] 
            simp add: walk_x_u)
      moreover have "length (u#pp1@[x]@ rev stck1) \<ge> 2" by auto
      ultimately show False
        using assms(2) by blast
    next
      case 2
      then show ?thesis 
        using one two
        by(auto intro!: invar_dfs_backtrack_5I 
            simp add: DFS_backtrack_upd2_def Let_def 
            elim!: DFS_call_2_conds invar_dfs_backtrack_5E)
    qed
  qed
qed

lemma invar_dfs_backtrack_5_holds_3[invar_holds_intros]:
  "\<lbrakk>invar_dfs_backtrack_5 dfs_state\<rbrakk> \<Longrightarrow> 
      invar_dfs_backtrack_5 (DFS_backtrack_ret1 dfs_state)"
  by(auto intro!: invar_dfs_backtrack_5I simp add: DFS_backtrack_ret1_def elim!: invar_dfs_backtrack_5E)

lemma invar_dfs_backtrack_5_holds_4[invar_holds_intros]:
  "\<lbrakk>invar_dfs_backtrack_5 dfs_state\<rbrakk> \<Longrightarrow> 
      invar_dfs_backtrack_5 (DFS_backtrack_ret2 dfs_state)"
  by(auto intro!: invar_dfs_backtrack_5I simp add: DFS_backtrack_ret2_def elim!: invar_dfs_backtrack_5E)

lemma invar_dfs_backtrack_5_holds: 
  assumes "DFS_collect_backtrack_dom dfs_state" 
    "\<nexists> p v. vwalk_bet (Graph.digraph_abs G) v p v \<and> length p \<ge> 2"
    "invar_dfs_backtrack_5 dfs_state" "invar_dfs_backtrack_4 dfs_state" 
    "invar_dfs_backtrack_3 dfs_state"
    "invar_dfs_backtrack_1 dfs_state"
    "invar_1 (to_ordinary_DFS_state dfs_state)"
    "invar_2 (to_ordinary_DFS_state dfs_state)"
    "invar_seen_stack (to_ordinary_DFS_state dfs_state)"
    "invar_visited_through_seen (to_ordinary_DFS_state dfs_state)"
  shows  "invar_dfs_backtrack_5 (DFS_collect_backtrack dfs_state)"
  using assms(3-)
proof(induction rule: DFS_backtrack_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    using assms(2) 
    by(cases rule: DFS_backtrack_cases[where dfs_state = dfs_state])
      (auto intro!: IH(2-) invar_holds_intros 
        simp: DFS_backtrack_simps[OF IH(1)] DFS_backtrack_upd1_homo DFS_backtrack_upd2_homo)
qed

lemma dfs_backtrack_initial_state: 
  "invar_dfs_backtrack_1 dfs_backtrack_initial_state"
  "invar_dfs_backtrack_2 dfs_backtrack_initial_state"
  "invar_dfs_backtrack_3 dfs_backtrack_initial_state"
  "invar_dfs_backtrack_4 dfs_backtrack_initial_state"
  "invar_dfs_backtrack_5 dfs_backtrack_initial_state"
  "DFS_collect_backtrack_dom dfs_backtrack_initial_state"
  by(auto intro: invar_dfs_backtrack_1I invar_dfs_backtrack_3I invar_dfs_backtrack_4I
      invar_dfs_backtrack_5I invar_dfs_backtrack_2I
      intro!: dom_same initial_state_props(6)[simplified initial_state_def]
      simp add: dfs_backtrack_initial_state_def)

lemma dfs_backtrack_final: 
  "invar_dfs_backtrack_1 (DFS_collect_backtrack dfs_backtrack_initial_state)"
  "invar_dfs_backtrack_2 (DFS_collect_backtrack dfs_backtrack_initial_state)"
  "invar_dfs_backtrack_3 (DFS_collect_backtrack dfs_backtrack_initial_state)"
  "invar_dfs_backtrack_4 (DFS_collect_backtrack dfs_backtrack_initial_state)"
  "\<nexists> p v. vwalk_bet (Graph.digraph_abs G) v p v \<and> length p \<ge> 2 \<Longrightarrow> 
 invar_dfs_backtrack_5 (DFS_collect_backtrack dfs_backtrack_initial_state)"
  by(auto intro!: invar_dfs_backtrack_1_holds invar_dfs_backtrack_3_holds
      invar_dfs_backtrack_4_holds invar_dfs_backtrack_5_holds
      invar_dfs_backtrack_2_holds dfs_backtrack_initial_state
      simp add: dfs_backtrack_initial_state_to_ordinary_same initial_state_props)

lemma DFS_collect_backtrack_impl_same_on_initial: 
  shows   "DFS_collect_backtrack_impl dfs_backtrack_initial_state =
           DFS_collect_backtrack dfs_backtrack_initial_state"
  using DFS_collect_backtrack_impl_same dfs_backtrack_initial_state(6) by blast

lemma same_as_old_dfs_on_initial: 
  shows "(to_ordinary_DFS_state (DFS_collect_backtrack dfs_backtrack_initial_state)) 
                = DFS initial_state" 
  using dfs_backtrack_initial_state_to_ordinary_same initial_state_props(6) same_as_old_dfs
  by blast
end
end

context DFS
begin
function (domintros) DFS_collect_backtrack_iterations::"('v, 'vset) DFS_backtrack_state \<Rightarrow> nat" where
  "DFS_collect_backtrack_iterations dfs_state = 
     (case (stack dfs_state) of (v # stack_tl) \<Rightarrow>
       (if v = t then 1
        else ((if (\<N>\<^sub>G v -\<^sub>G (seen dfs_state)) \<noteq> \<emptyset>\<^sub>N then
                  let u = (sel ((\<N>\<^sub>G v) -\<^sub>G (seen dfs_state)));
                      stack' = u# (stack dfs_state);
                      seen' = insert u (seen dfs_state)                      
                  in
                    (1 + DFS_collect_backtrack_iterations (dfs_state \<lparr>stack := stack',   seen := seen' \<rparr>))
                else
                  let stack' = stack_tl;
                      backtrack = backtrack dfs_state;
                      backtrack'=(case stack' of [] \<Rightarrow> backtrack | (x#xs) \<Rightarrow> (x, v)#backtrack)
                   in
                   1 + DFS_collect_backtrack_iterations (dfs_state \<lparr>stack := stack', backtrack := backtrack'\<rparr>))
              )
      )
     | _ \<Rightarrow> 1
    )"
  by pat_completeness auto

lemma backtrack_dom_itme_dom:assumes"DFS_collect_backtrack_dom state"
  shows "DFS_collect_backtrack_iterations_dom (state)"
  apply(induction  rule: DFS_collect_backtrack.pinduct[OF assms])
  apply(auto intro: DFS_collect_backtrack_iterations.domintros)
  done

lemma DFS_backtrack_iterations_simps:
  assumes "DFS_collect_backtrack_iterations_dom ( dfs_state)" 
  shows"DFS_call_1_conds (to_ordinary_DFS_state dfs_state)
            \<Longrightarrow> DFS_collect_backtrack_iterations dfs_state = 1 + DFS_collect_backtrack_iterations (DFS_backtrack_upd1 dfs_state)"
    "DFS_call_2_conds (to_ordinary_DFS_state dfs_state) 
            \<Longrightarrow> DFS_collect_backtrack_iterations  dfs_state = 1+ DFS_collect_backtrack_iterations (DFS_backtrack_upd2 dfs_state)"
    "DFS_ret_1_conds (to_ordinary_DFS_state dfs_state) 
            \<Longrightarrow> DFS_collect_backtrack_iterations  dfs_state = 1 "
    "DFS_ret_2_conds  (to_ordinary_DFS_state dfs_state) 
           \<Longrightarrow> DFS_collect_backtrack_iterations  dfs_state = 1"
  by (auto simp add: DFS_collect_backtrack_iterations.psimps[OF assms] Let_def
      DFS_call_1_conds_def DFS_backtrack_upd1_def DFS_call_2_conds_def 
      DFS_backtrack_upd2_def
      DFS_ret_1_conds_def DFS_backtrack_ret1_def
      DFS_ret_2_conds_def DFS_backtrack_ret2_def                    
      split: list.splits option.splits if_splits)
end

context DFS_thms
begin
lemma DFS_collect_backtrack_iterations_bound_general:
  assumes "DFS_collect_backtrack_dom state"
  defines "T st == (let finstack = stack (DFS_collect_backtrack st);
                        stck= stack st;
                        finbacktrack=backtrack (DFS_collect_backtrack st);
                        dl= backtrack st in
                         (int (length finstack)  - int (length stck) +
                          2*(int (length finbacktrack) - int (length dl)))
                           ) + 3"
  shows  "int (DFS_collect_backtrack_iterations  state) \<le>  T state "
proof(induction  rule: DFS_backtrack_induct[OF assms(1)])
  case (1 state)
  note IH=this
  show ?case 
  proof(cases state rule: DFS_backtrack_cases)
    case 1
    have length_change: 
      "1 + length (DFS_backtrack_state.stack state) = 
         length (DFS_backtrack_state.stack (DFS_backtrack_upd1 state))"
      using 1 by (auto  elim!: DFS_call_1_conds simp add: DFS_backtrack_upd1_def Let_def)
    show ?thesis 
      apply(insert 1)
      apply(subst DFS_backtrack_iterations_simps(1)[OF  backtrack_dom_itme_dom[OF IH(1)]])
      using int_plus[of 1, simplified int_ops(2)]
      using sym[OF DFS_backtrack_simps(1)[OF IH(1)]]  
      by(fastforce intro!:  order.trans[OF add_mono[of 1 1, OF _ IH(2)]] 
          simp add: sym[OF DFS_backtrack_simps(1)[OF IH(1)] ] DFS_backtrack_upd1_def T_def 
          Let_def length_change[symmetric]
          |subst int_plus[of 1, simplified int_ops(2)])+
  next
    case 2
    show ?thesis
    proof(cases "tl (stack state)")
      case (Cons a list)
      have length_change: 
        "length (DFS_backtrack_state.stack state) = 
         length (DFS_backtrack_state.stack (DFS_backtrack_upd2 state)) + 1"
        using 2 by (auto  elim!: DFS_call_2_conds simp add: DFS_backtrack_upd2_def Let_def)
      have backtrack_change: 
        "length (DFS_backtrack_state.backtrack state) +1 = 
         length (DFS_backtrack_state.backtrack (DFS_backtrack_upd2 state))"
        using 2 Cons by (auto  elim!: DFS_call_2_conds simp add: DFS_backtrack_upd2_def Let_def)
      have empty_stack_dom: "DFS_collect_backtrack_dom (state\<lparr>DFS_backtrack_state.stack := []\<rparr>)" 
        by(auto intro: DFS_collect_backtrack.domintros)
      have ret_1_conds_empty_stack: "DFS_ret_1_conds (to_ordinary_DFS_state (state\<lparr>DFS_backtrack_state.stack := []\<rparr>))"
        by(auto simp add: DFS_ret_1_conds_def)
      show ?thesis 
        apply(insert 2)
        apply(subst DFS_backtrack_iterations_simps(2)[OF backtrack_dom_itme_dom[OF IH(1)]])
        using sym[OF DFS_backtrack_simps(2)[OF IH(1)] ]
        by(fastforce intro: order.trans[OF  add_mono[of 1 1, OF _ IH(3)]] 
            simp add: backtrack_change[symmetric]  length_change T_def Let_def
            |subst int_plus[of 1, simplified int_ops(2)])+
    next
      case Nil
      have length_change: 
        "length (DFS_backtrack_state.stack state) = 
         length (DFS_backtrack_state.stack (DFS_backtrack_upd2 state)) + 1"
        using 2 by (auto  elim!: DFS_call_2_conds simp add: DFS_backtrack_upd2_def Let_def)
      have backtrack_it_is:"DFS_collect_backtrack_iterations (state\<lparr>DFS_backtrack_state.stack := []\<rparr>) = 1"
        by(subst DFS_collect_backtrack_iterations.psimps)
          (auto intro: DFS_collect_backtrack_iterations.domintros )
      have finstack_is:"DFS_backtrack_state.stack (DFS_collect_backtrack (state\<lparr>DFS_backtrack_state.stack := []\<rparr>)) = []"
        by(subst DFS_collect_backtrack.psimps)
          (auto intro: DFS_collect_backtrack.domintros )
      have finbacktrack_is: "backtrack (DFS_collect_backtrack (state\<lparr>DFS_backtrack_state.stack := []\<rparr>)) = backtrack state"
        by(subst DFS_collect_backtrack.psimps)
          (auto intro: DFS_collect_backtrack.domintros )
      have len_less_1:"length (DFS_backtrack_state.stack state) \<le> Suc 0"
        by (auto simp add: Nitpick.size_list_simp(2) local.Nil)
      then show  ?thesis
        using DFS_backtrack_iterations_simps(2)[OF backtrack_dom_itme_dom[OF IH(1)]] 2
        by(auto simp add: DFS_backtrack_upd2_def Nil backtrack_it_is finstack_is T_def
            DFS_backtrack_simps(2)[OF IH(1) 2] finbacktrack_is )
    qed
  next
    case 3
    show ?thesis
      by(auto simp add: T_def Let_def 
          DFS_backtrack_iterations_simps(3)[OF backtrack_dom_itme_dom[OF IH(1)] 3]
          DFS_backtrack_simps(3)[OF IH(1) 3] DFS_backtrack_ret1_def)
  next
    case 4
    show ?thesis
      by(auto simp add: T_def Let_def 
          DFS_backtrack_iterations_simps(4)[OF backtrack_dom_itme_dom[OF IH(1)] 4]
          DFS_backtrack_simps(4)[OF IH(1) 4] DFS_backtrack_ret2_def)
  qed
qed

lemma DFS_collect_backtrack_iterations_bound:
  assumes "DFS_collect_backtrack_dom dfs_backtrack_initial_state"
  shows  "DFS_collect_backtrack_iterations dfs_backtrack_initial_state \<le>
         length (stack (DFS_collect_backtrack dfs_backtrack_initial_state)) 
       + 2 * length (backtrack (DFS_collect_backtrack dfs_backtrack_initial_state)) + 3"
  using DFS_collect_backtrack_iterations_bound_general
    [OF dfs_backtrack_initial_state(6), simplified Let_def] 
  by simp
end
end