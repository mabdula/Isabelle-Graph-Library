theory DFS_Reach_Skel
  imports DFS DFS_Skeletons.DFS_Skeleton
begin

section \<open>Reachability by DFS (skeleton instance)\<close>

text \<open>Whether @{term t} is reachable from @{term s}, as an instance of the generic DFS skeleton:
the search reports @{term Reachable} as soon as @{term t} reaches the top of the stack, and
@{term NotReachable} when the stack runs empty. Nothing is maintained on push or on backtracking,
so the callbacks are the no-ops @{term no_push} and @{term reach_on_backtrack}; the whole
per-algorithm content is the found test and the two return slots.

The reachability invariants of \<open>DFS\<close> are re-derived here against the skeleton, and the two
correctness theorems come out in the same form: a @{term NotReachable} verdict means there is no
walk at all from @{term s} to @{term t}, and a @{term Reachable} verdict hands back the reversed
stack as a distinct walk from @{term s} to @{term t}.\<close>

subsection \<open>Setup\<close>

record ('ver, 'vset) DFS_reach_state = "('ver, 'vset) DFS_skeleton_state" +
  return :: return

locale DFS_Reach =
  Graph: Pair_Graph_Specs where lookup = lookup +
 set_ops: Set2 vset_empty vset_delete _ t_set vset_inv insert
for lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option" +
fixes G::"'adjmap" and s::"'v" and t::"'v"
begin

abbreviation "neighbourhood' \<equiv> Graph.neighbourhood G"
notation "neighbourhood'" ("\<N>\<^sub>G _" 100)

lemma subtract_from_empty:
"vset_inv A \<Longrightarrow> \<emptyset>\<^sub>N -\<^sub>G A = \<emptyset>\<^sub>N"
  using Graph.vset.emptyD(4) Graph.vset.set.invar_empty Graph.vset.set.set_empty empty_Diff
      set_ops.invar_diff set_ops.set_diff
  by force

subsection \<open>Semantics via the skeleton callbacks\<close>

text \<open>The found test reads the stack head; the two return slots are written on the two exits.\<close>

definition "reach_found (st::('v,'vset) DFS_reach_state) =
   (case stack st of [] \<Rightarrow> False | v # _ \<Rightarrow> v = t)"

definition "reach_on_found (st::('v,'vset) DFS_reach_state) = (st \<lparr>return := Reachable\<rparr>)"

definition "reach_on_empty (st::('v,'vset) DFS_reach_state) = (st \<lparr>return := NotReachable\<rparr>)"

definition "reach_on_backtrack v (st::('v,'vset) DFS_reach_state) = st"

definition "initial_state = \<lparr>stack = [s], seen = insert s \<emptyset>\<^sub>N, return = NotReachable\<rparr>"

definition "DFS_axioms =
  (Graph.graph_inv G \<and> Graph.finite_graph G \<and> Graph.finite_vsets G \<and> s \<in> dVs (Graph.digraph_abs G))"

sublocale reach: DFS_skeleton
  where lookup = lookup and G = G and s = s
    and found = reach_found and on_found = reach_on_found
    and on_empty = reach_on_empty and on_backtrack = reach_on_backtrack
    and on_push = no_push
  by unfold_locales

abbreviation "DFS_reach \<equiv> reach.DFS_skeleton"
abbreviation "DFS_reach_impl \<equiv> reach.DFS_skeleton_impl"

end

locale DFS_Reach_thms = DFS_Reach +
  assumes DFS_axioms: DFS_axioms
begin

lemma spine_preservation:
  "stack (reach_on_found st) = stack st" "seen (reach_on_found st) = seen st"
  "stack (reach_on_empty st) = stack st" "seen (reach_on_empty st) = seen st"
  "stack (reach_on_backtrack v st) = stack st" "seen (reach_on_backtrack v st) = seen st"
  by (auto simp: reach_on_found_def reach_on_empty_def reach_on_backtrack_def no_push_def split: list.splits)

sublocale reach: DFS_skeleton_thms
  where lookup = lookup and G = G and s = s
    and found = reach_found and on_found = reach_on_found
    and on_empty = reach_on_empty and on_backtrack = reach_on_backtrack
    and on_push = no_push
  using DFS_axioms
  by (unfold_locales)
     (auto simp: reach.DFS_skeleton_axioms_def DFS_axioms_def
                 reach_on_found_def reach_on_empty_def reach_on_backtrack_def no_push_def split: list.splits)

subsection \<open>Unfolding of the skeleton updates\<close>

lemma upd1_unfold:
  "stack (reach.DFS_skeleton_upd1 st) = sel ((\<N>\<^sub>G (hd (stack st))) -\<^sub>G seen st) # stack st"
  "seen (reach.DFS_skeleton_upd1 st) = insert (sel ((\<N>\<^sub>G (hd (stack st))) -\<^sub>G seen st)) (seen st)"
  "return (reach.DFS_skeleton_upd1 st) = return st"
  by (auto simp: reach.DFS_skeleton_upd1_def no_push_def Let_def)

lemma upd2_unfold:
  "stack (reach.DFS_skeleton_upd2 st) = tl (stack st)"
  "seen (reach.DFS_skeleton_upd2 st) = seen st"
  "return (reach.DFS_skeleton_upd2 st) = return st"
  by (auto simp: reach.DFS_skeleton_upd2_def reach_on_backtrack_def split: list.splits)

lemma ret1_unfold:
  "stack (reach.DFS_skeleton_ret1 st) = stack st"
  "seen (reach.DFS_skeleton_ret1 st) = seen st"
  "return (reach.DFS_skeleton_ret1 st) = NotReachable"
  by (auto simp: reach.DFS_skeleton_ret1_def reach_on_empty_def)

lemma ret2_unfold:
  "stack (reach.DFS_skeleton_ret2 st) = stack st"
  "seen (reach.DFS_skeleton_ret2 st) = seen st"
  "return (reach.DFS_skeleton_ret2 st) = Reachable"
  by (auto simp: reach.DFS_skeleton_ret2_def reach_on_found_def)

lemma found_unfold:
  "stack st = v # stack_tl \<Longrightarrow> reach_found st = (v = t)"
  by (auto simp: reach_found_def)

subsection \<open>Reachability invariants (re-derived against the skeleton)\<close>

definition "invar_2 dfs_state = (Vwalk.vwalk (Graph.digraph_abs G) (rev (stack dfs_state)))"

definition "invar_s_in_stack dfs_state \<longleftrightarrow>
  (stack (dfs_state) \<noteq> [] \<longrightarrow> last (stack dfs_state) = s)"

definition "invar_visited_through_seen dfs_state =
    (\<forall>v \<in> t_set (seen dfs_state).
       (\<forall>p. Vwalk.vwalk_bet (Graph.digraph_abs G) v p t \<and> distinct p \<longrightarrow> (set p \<inter> set (stack dfs_state) \<noteq> {})))"

definition "state_rel_1 dfs_state_1 dfs_state_2
              = ( t_set (seen dfs_state_1) \<subseteq> t_set (seen dfs_state_2))"

context
includes set_ops.automation2 and Graph.adjmap.automation and Graph.vset.set.automation
begin

lemma initial_invars[simp,intro]:
  "reach.invar_1 initial_state"
  "reach.invar_seen_stack initial_state"
  using DFS_axioms
  by (auto simp: reach.invar_1_def reach.invar_seen_stack_def initial_state_def DFS_axioms_def)

lemma initial_dom: "reach.DFS_skeleton_dom initial_state"
  by (intro reach.DFS_skeleton_terminates initial_invars)

subsubsection \<open>\<open>invar_2\<close>\<close>

lemma invar_2_props[invar_props_elims]:
  "invar_2 dfs_state \<Longrightarrow> (Vwalk.vwalk (Graph.digraph_abs G) (rev (stack dfs_state)) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_2_def)

lemma invar_2_intro[invar_props_intros]:
  "Vwalk.vwalk (Graph.digraph_abs G) (rev (stack dfs_state)) \<Longrightarrow> invar_2 dfs_state"
  by (auto simp: invar_2_def)

lemma invar_2_holds_1[invar_holds_intros]:
  assumes "reach.DFS_skeleton_call_1_conds dfs_state" "reach.invar_1 dfs_state" "invar_2 dfs_state"
  shows "invar_2 (reach.DFS_skeleton_upd1 dfs_state)"
  using assms reach.graph_inv
  by (force simp: Let_def reach.DFS_skeleton_upd1_def elim!: call_cond_elims
            elim!: invar_props_elims intro!: Vwalk.vwalk_append2 neighbourhoodI invar_props_intros)

lemma invar_2_holds_2[invar_holds_intros]:
  "\<lbrakk>reach.DFS_skeleton_call_2_conds dfs_state; invar_2 dfs_state\<rbrakk> \<Longrightarrow> invar_2 (reach.DFS_skeleton_upd2 dfs_state)"
  by (auto simp: upd2_unfold dest!: append_vwalk_pref elim!: invar_props_elims
           intro!: invar_props_intros elim: call_cond_elims)

lemma invar_2_holds_4[invar_holds_intros]:
  "\<lbrakk>reach.DFS_skeleton_ret_1_conds dfs_state; invar_2 dfs_state\<rbrakk> \<Longrightarrow> invar_2 (reach.DFS_skeleton_ret1 dfs_state)"
  by (auto elim!: invar_props_elims intro: invar_props_intros simp: ret1_unfold)

lemma invar_2_holds_5[invar_holds_intros]:
  "\<lbrakk>reach.DFS_skeleton_ret_2_conds dfs_state; invar_2 dfs_state\<rbrakk> \<Longrightarrow> invar_2 (reach.DFS_skeleton_ret2 dfs_state)"
  by (auto elim!: invar_props_elims intro: invar_props_intros simp: ret2_unfold)

lemma invar_2_holds[invar_holds_intros]:
   assumes "reach.DFS_skeleton_dom dfs_state" "reach.invar_1 dfs_state" "invar_2 dfs_state"
   shows "invar_2 (reach.DFS_skeleton dfs_state)"
  using assms(2-3)
proof(induction rule: reach.DFS_skeleton_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule reach.DFS_skeleton_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-) invar_holds_intros simp: reach.DFS_skeleton_simps[OF IH(1)])
qed

subsubsection \<open>\<open>invar_s_in_stack\<close>\<close>

lemma invar_s_in_stack_props[invar_props_elims]:
   "invar_s_in_stack dfs_state \<Longrightarrow>
     (\<lbrakk>(stack (dfs_state) \<noteq> [] \<Longrightarrow> last (stack dfs_state) = s)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P "
  by (auto simp: invar_s_in_stack_def)

lemma invar_s_in_stack_intro[invar_props_intros]:
  "\<lbrakk>(stack (dfs_state) \<noteq> [] \<Longrightarrow> last (stack dfs_state) = s)\<rbrakk> \<Longrightarrow> invar_s_in_stack dfs_state"
  by (auto simp: invar_s_in_stack_def)

lemma invar_s_in_stack_holds_1[invar_holds_intros]:
  "\<lbrakk>reach.DFS_skeleton_call_1_conds dfs_state; reach.invar_1 dfs_state; invar_s_in_stack dfs_state\<rbrakk> \<Longrightarrow>
     invar_s_in_stack (reach.DFS_skeleton_upd1 dfs_state)"
  by (force simp: Let_def reach.DFS_skeleton_upd1_def dest!: append_vwalk_pref elim!: call_cond_elims
            elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_s_in_stack_holds_2[invar_holds_intros]:
  "\<lbrakk>reach.DFS_skeleton_call_2_conds dfs_state; reach.invar_1 dfs_state; invar_s_in_stack dfs_state\<rbrakk> \<Longrightarrow>
     invar_s_in_stack (reach.DFS_skeleton_upd2 dfs_state)"
  by (auto elim!: call_cond_elims simp: upd2_unfold elim: vwalk_betE
           elim!: invar_props_elims dest!: Graph.vset.emptyD append_vwalk_pref intro!: invar_props_intros)

lemma invar_s_in_stack_holds_4[invar_holds_intros]:
   "\<lbrakk>reach.DFS_skeleton_ret_1_conds dfs_state; invar_s_in_stack dfs_state\<rbrakk> \<Longrightarrow>
       invar_s_in_stack (reach.DFS_skeleton_ret1 dfs_state)"
  by (auto elim!: invar_props_elims intro!: invar_props_intros simp: ret1_unfold)

lemma invar_s_in_stack_holds_5[invar_holds_intros]:
  "\<lbrakk>reach.DFS_skeleton_ret_2_conds dfs_state; invar_s_in_stack dfs_state\<rbrakk> \<Longrightarrow>
     invar_s_in_stack (reach.DFS_skeleton_ret2 dfs_state)"
  by (auto elim!: invar_props_elims intro!: invar_props_intros simp: ret2_unfold)

lemma invar_s_in_stack_holds[invar_holds_intros]:
   assumes "reach.DFS_skeleton_dom dfs_state" "reach.invar_1 dfs_state" "invar_s_in_stack dfs_state"
   shows "invar_s_in_stack (reach.DFS_skeleton dfs_state)"
   using assms(2-)
proof(induction rule: reach.DFS_skeleton_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule reach.DFS_skeleton_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-) invar_holds_intros simp: reach.DFS_skeleton_simps[OF IH(1)])
qed

subsubsection \<open>\<open>invar_visited_through_seen\<close>\<close>

lemma invar_visited_through_seen_props[elim!]:
   "invar_visited_through_seen dfs_state \<Longrightarrow>
     (\<lbrakk>\<And>v p. \<lbrakk>v \<in> t_set (seen dfs_state);
              (Vwalk.vwalk_bet (Graph.digraph_abs G) v p t); distinct p \<rbrakk> \<Longrightarrow>
              set p \<inter> set (stack dfs_state) \<noteq> {}\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P "
  by (auto simp: invar_visited_through_seen_def)

lemma invar_visited_through_seen_intro[invar_props_intros]:
  "\<lbrakk>\<And>v p. \<lbrakk>v \<in> t_set (seen dfs_state);
           (Vwalk.vwalk_bet (Graph.digraph_abs G) v p t); distinct p\<rbrakk> \<Longrightarrow>
           set p \<inter> set (stack dfs_state) \<noteq> {}\<rbrakk> \<Longrightarrow> invar_visited_through_seen dfs_state"
  by (auto simp: invar_visited_through_seen_def)

lemma invar_visited_through_seen_holds_1[invar_holds_intros]:
  "\<lbrakk>reach.DFS_skeleton_call_1_conds dfs_state; reach.invar_1 dfs_state; reach.invar_seen_stack dfs_state;
    invar_visited_through_seen dfs_state\<rbrakk>
    \<Longrightarrow> invar_visited_through_seen (reach.DFS_skeleton_upd1 dfs_state)"
  by(fastforce simp: Let_def reach.DFS_skeleton_upd1_def dest: append_vwalk_pref hd_of_vwalk_bet''
               elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_visited_through_seen_holds_2[invar_holds_intros]:
  "\<lbrakk>reach.DFS_skeleton_call_2_conds dfs_state; reach.invar_1 dfs_state; reach.invar_seen_stack dfs_state;
    invar_visited_through_seen dfs_state\<rbrakk> \<Longrightarrow> invar_visited_through_seen (reach.DFS_skeleton_upd2 dfs_state)"
proof(rule invar_props_intros, elim invar_visited_through_seen_props call_cond_elims exE, goal_cases)
  case (1 v1 p v2 stack_tl)
  hence "set p \<inter> set (stack dfs_state) \<noteq> {}"
    by (auto simp: upd2_unfold)
  then obtain u where u: "u \<in> set p \<inter> set (stack dfs_state)"
    by auto
  show ?case
  proof(cases "u \<in> set stack_tl")
    case True
    thus ?thesis
      using 1 u by (auto simp: upd2_unfold)
  next
    case False
    hence uv2: "u = v2"
      using 1 u by auto
    then obtain p1 p2 where pdec[simp]: "p = p1 @ [v2] @ p2"
      using u by (auto simp: in_set_conv_decomp)
    hence "set (v2 # p2) \<inter> set (stack dfs_state) \<noteq> {}"
      using 1 by (auto simp: upd2_unfold)
    have vne: "v2 \<noteq> t"
      using 1 by (auto simp: found_unfold)
    show ?thesis
    proof(cases "p2 = []")
      case True
      thus ?thesis
        using 1 vne by (auto simp: vwalk_bet_snoc)
    next
      case False
      hence "hd p2 \<in> t_set (\<N>\<^sub>G v2)"
        using \<open>vwalk_bet (Graph.digraph_abs G) v1 p t\<close>
        by (auto dest!: split_vwalk simp: neq_Nil_conv)
      hence "hd p2 \<in> t_set (seen dfs_state)"
        using 1 by (fastforce elim!: invar_props_elims simp del: pdec)
      hence "set p2 \<inter> set (stack dfs_state) \<noteq> {}"
        using 1 False by (fastforce simp: upd2_unfold neq_Nil_conv dest!: split_vwalk)
      moreover have "v2 \<notin> set p2"
        using \<open>distinct p\<close> by auto
      ultimately have "set p2 \<inter> set (stack (reach.DFS_skeleton_upd2 dfs_state)) \<noteq> {}"
        using 1 by (auto simp: upd2_unfold)
      thus ?thesis by auto
    qed
  qed
qed

lemma invar_visited_through_seen_holds_4[invar_holds_intros]:
  "\<lbrakk>reach.DFS_skeleton_ret_1_conds dfs_state; invar_visited_through_seen dfs_state\<rbrakk> \<Longrightarrow>
     invar_visited_through_seen (reach.DFS_skeleton_ret1 dfs_state)"
  by (auto intro: invar_props_intros simp: ret1_unfold)

lemma invar_visited_through_seen_holds_5[invar_holds_intros]:
  "\<lbrakk>reach.DFS_skeleton_ret_2_conds dfs_state; invar_visited_through_seen dfs_state\<rbrakk> \<Longrightarrow>
     invar_visited_through_seen (reach.DFS_skeleton_ret2 dfs_state)"
  by (auto intro: invar_props_intros simp: ret2_unfold)

lemma invar_visited_through_seen_holds[invar_holds_intros]:
   assumes "reach.DFS_skeleton_dom dfs_state" "reach.invar_1 dfs_state" "reach.invar_seen_stack dfs_state"
           "invar_visited_through_seen dfs_state"
   shows "invar_visited_through_seen (reach.DFS_skeleton dfs_state)"
   using assms(2-)
proof(induction rule: reach.DFS_skeleton_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule reach.DFS_skeleton_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-) invar_holds_intros simp: reach.DFS_skeleton_simps[OF IH(1)])
qed

subsubsection \<open>state relation\<close>

lemma state_rel_1_props[elim!]: "state_rel_1 dfs_state_1 dfs_state_2 \<Longrightarrow>
                                  (t_set (seen dfs_state_1) \<subseteq> t_set (seen dfs_state_2) \<Longrightarrow> P) \<Longrightarrow> P "
  by (auto simp: state_rel_1_def)

lemma state_rel_1_intro[state_rel_intros]:
  "\<lbrakk>t_set (seen dfs_state_1) \<subseteq> t_set (seen dfs_state_2)\<rbrakk> \<Longrightarrow> state_rel_1 dfs_state_1 dfs_state_2"
  by (auto simp: state_rel_1_def)

lemma state_rel_1_trans:
  "\<lbrakk>state_rel_1 dfs_state_1 dfs_state_2; state_rel_1 dfs_state_2 dfs_state_3\<rbrakk> \<Longrightarrow>
   state_rel_1 dfs_state_1 dfs_state_3"
  by (auto intro!: state_rel_intros)

lemma state_rel_1_holds_1[state_rel_holds_intros]:
  "\<lbrakk>reach.DFS_skeleton_call_1_conds dfs_state; reach.invar_1 dfs_state\<rbrakk> \<Longrightarrow> state_rel_1 dfs_state (reach.DFS_skeleton_upd1 dfs_state)"
  by (auto simp: Let_def reach.DFS_skeleton_upd1_def elim!: invar_props_elims intro!: state_rel_intros)

lemma state_rel_1_holds_2[state_rel_holds_intros]:
  "\<lbrakk>reach.DFS_skeleton_call_2_conds dfs_state; reach.invar_1 dfs_state\<rbrakk> \<Longrightarrow> state_rel_1 dfs_state (reach.DFS_skeleton_upd2 dfs_state)"
  by (auto simp: upd2_unfold intro!: state_rel_intros elim: call_cond_elims)

lemma state_rel_1_holds_4[state_rel_holds_intros]:
  "\<lbrakk>reach.DFS_skeleton_ret_1_conds dfs_state\<rbrakk> \<Longrightarrow> state_rel_1 dfs_state (reach.DFS_skeleton_ret1 dfs_state)"
  by (auto intro!: state_rel_intros simp: ret1_unfold)

lemma state_rel_1_holds_5[state_rel_holds_intros]:
  "\<lbrakk>reach.DFS_skeleton_ret_2_conds dfs_state\<rbrakk> \<Longrightarrow> state_rel_1 dfs_state (reach.DFS_skeleton_ret2 dfs_state)"
  by (auto intro!: state_rel_intros simp: ret2_unfold)

lemma state_rel_1_holds[state_rel_holds_intros]:
   assumes "reach.DFS_skeleton_dom dfs_state" "reach.invar_1 dfs_state"
   shows "state_rel_1 dfs_state (reach.DFS_skeleton dfs_state)"
   using assms(2-)
proof(induction rule: reach.DFS_skeleton_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule reach.DFS_skeleton_cases[where dfs_state = dfs_state])
    by (auto intro: state_rel_1_trans invar_holds_intros state_rel_holds_intros intro!: IH(2-) simp: reach.DFS_skeleton_simps[OF IH(1)])
qed

subsubsection \<open>Return-condition tracking + reachability correctness\<close>

lemma ret_1[ret_holds_intros]: "reach.DFS_skeleton_ret_1_conds (dfs_state) \<Longrightarrow> reach.DFS_skeleton_ret_1_conds (reach.DFS_skeleton_ret1 dfs_state)"
  by (auto elim!: call_cond_elims intro!: call_cond_intros simp: ret1_unfold)

lemma ret1_holds[ret_holds_intros]:
   assumes "reach.DFS_skeleton_dom dfs_state" "return (reach.DFS_skeleton dfs_state) = NotReachable"
   shows "reach.DFS_skeleton_ret_1_conds (reach.DFS_skeleton dfs_state)"
   using assms(2-)
proof(induction rule: reach.DFS_skeleton_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule reach.DFS_skeleton_cases[where dfs_state = dfs_state])
    using IH(4)
    by (auto intro: ret_holds_intros intro!: IH(2-) simp: reach.DFS_skeleton_simps[OF IH(1)] ret2_unfold)
qed

lemma DFS_correct_ret_1:
  "\<lbrakk>invar_visited_through_seen dfs_state; reach.DFS_skeleton_ret_1_conds dfs_state; u \<in> t_set (seen dfs_state)\<rbrakk>
         \<Longrightarrow> \<nexists>p. distinct p \<and> vwalk_bet (Graph.digraph_abs G) u p t"
  by (auto elim!: call_cond_elims invar_props_elims)

lemma ret_2[ret_holds_intros]: "reach.DFS_skeleton_ret_2_conds (dfs_state) \<Longrightarrow> reach.DFS_skeleton_ret_2_conds (reach.DFS_skeleton_ret2 dfs_state)"
  by (auto elim!: call_cond_elims intro!: call_cond_intros simp: ret2_unfold reach_found_def)

lemma ret2_holds[ret_holds_intros]:
   assumes "reach.DFS_skeleton_dom dfs_state" "return (reach.DFS_skeleton dfs_state) = Reachable"
   shows "reach.DFS_skeleton_ret_2_conds (reach.DFS_skeleton dfs_state)"
   using assms(2-)
proof(induction rule: reach.DFS_skeleton_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule reach.DFS_skeleton_cases[where dfs_state = dfs_state])
    using IH(4)
    by (auto intro: ret_holds_intros intro!: IH(2-) simp: reach.DFS_skeleton_simps[OF IH(1)] ret1_unfold)
qed

lemma DFS_correct_ret_2:
  "\<lbrakk>invar_2 dfs_state; reach.DFS_skeleton_ret_2_conds dfs_state\<rbrakk>
         \<Longrightarrow> vwalk_bet (Graph.digraph_abs G) (last (stack dfs_state)) (rev (stack dfs_state)) t"
  by (auto elim!: call_cond_elims invar_props_elims simp: hd_rev vwalk_bet_def reach_found_def
           split: list.splits)

lemma initial_state_props[invar_holds_intros]:
  "invar_2 initial_state" "invar_s_in_stack initial_state"
  "invar_visited_through_seen initial_state"
  using DFS_axioms
  by (auto simp: initial_state_def invar_2_def invar_s_in_stack_def
                 invar_visited_through_seen_def DFS_axioms_def
                 hd_of_vwalk_bet''
           elim: vwalk_betE
           intro!: invar_props_intros)

theorem DFS_correct_1:
  assumes "return (DFS_reach initial_state) = NotReachable"
  shows   "\<nexists>p. distinct p \<and> vwalk_bet (Graph.digraph_abs G) s p t"
proof-
  have "s \<in> t_set (seen (DFS_reach initial_state))"
    using state_rel_1_holds[OF initial_dom initial_invars(1)]
    by (auto simp: initial_state_def state_rel_1_def)
  thus ?thesis
    using assms
    by(intro DFS_correct_ret_1[where dfs_state = "DFS_reach initial_state"])
      (auto intro!: invar_holds_intros ret_holds_intros initial_dom initial_invars initial_state_props)
qed

theorem DFS_correct_1_strong:
  assumes "return (DFS_reach initial_state) = NotReachable"
  shows   "\<nexists>p. vwalk_bet (Graph.digraph_abs G) s p t"
  using DFS_correct_1[OF assms] vwalk_bet_to_distinct_is_distinct_vwalk_bet
  by(force simp add: distinct_vwalk_bet_def)

theorem DFS_correct_2:
  assumes  "return (DFS_reach initial_state) = Reachable"
  shows "vwalk_bet (Graph.digraph_abs G) s (rev (stack (DFS_reach initial_state))) t" (is ?thesis1)
        "distinct (rev (stack (DFS_reach initial_state)))" (is ?thesis2)
proof-
  have "vwalk_bet
              (Graph.digraph_abs G)
              (last (stack (DFS_reach initial_state)))
              (rev (stack (DFS_reach initial_state))) t"
    using assms
    by(auto intro!: invar_holds_intros ret_holds_intros initial_dom initial_invars initial_state_props
                       DFS_correct_ret_2[where dfs_state = "DFS_reach initial_state"])
  moreover hence "(last (stack (DFS_reach initial_state))) = s"
    by(fastforce intro!: invar_holds_intros initial_dom initial_invars initial_state_props
                 intro: invar_s_in_stack_props[where dfs_state = "DFS_reach initial_state"])+
  ultimately show ?thesis1
    by auto
  show ?thesis2
    using initial_dom initial_invars reach.invar_seen_stack_holds reach.invar_seen_stack_props
    by auto
qed
end

end

end
