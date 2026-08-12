theory DFS_CB_Skel
  imports Graph_Algorithms_Dev.DFS_Reach_Skel
begin

section ‹A DFS with Collection of Dead-End Edges (skeleton instance)›

text ‹When DFS backtracks from an edge without finding a path, we call this a dead-end edge. This is
a self-contained instance of the generic DFS skeleton: the reachability behaviour is exactly that of
the reachability instance, and the extra @{term backtrack} slot collects, on every pop, the edge
from the new stack head to the popped vertex. The reachability invariants/correctness are re-derived
against the skeleton, and the backtrack-specific invariants are proved on top.›

subsection ‹Setup›

record ('ver, 'vset) DFS_bt_state = "('ver, 'vset) DFS_skeleton_state" +
  return :: return
  backtrack :: "('ver × 'ver) list"

locale DFS_CB =
  Graph: Pair_Graph_Specs where lookup = lookup +
 set_ops: Set2 vset_empty vset_delete _ t_set vset_inv insert
for lookup :: "'adjmap ⇒ 'v ⇒ 'vset option" +
fixes G::"'adjmap" and s::"'v" and t::"'v"
begin

abbreviation "neighbourhood' ≡ Graph.neighbourhood G"
notation "neighbourhood'" ("𝒩⇩G _" 100)

lemma subtract_from_empty:
"vset_inv A ⟹ ∅⇩N -⇩G A = ∅⇩N"
  using Graph.vset.emptyD(4) Graph.vset.set.invar_empty Graph.vset.set.set_empty empty_Diff
      set_ops.invar_diff set_ops.set_diff
  by force

subsection ‹Semantics via the skeleton callbacks›

text ‹Reachability callbacks are as in the reachability instance; the only new behaviour is on
backtracking, where the dead-end edge (new head, popped vertex) is prepended to @{term backtrack}.›

definition "cb_found (st::('v,'vset) DFS_bt_state) =
   (case stack st of [] ⇒ False | v # _ ⇒ v = t)"

definition "cb_on_found (st::('v,'vset) DFS_bt_state) = (st ⦇return := Reachable⦈)"

definition "cb_on_empty (st::('v,'vset) DFS_bt_state) = (st ⦇return := NotReachable⦈)"

definition "cb_on_backtrack v (st::('v,'vset) DFS_bt_state) =
   (case stack st of [] ⇒ st | x # _ ⇒ st ⦇backtrack := (x, v) # backtrack st⦈)"

definition "initial_state = ⦇stack = [s], seen = insert s ∅⇩N, return = NotReachable, backtrack = []⦈"

definition "DFS_axioms =
  (Graph.graph_inv G ∧ Graph.finite_graph G ∧ Graph.finite_vsets G ∧ s ∈ dVs (Graph.digraph_abs G))"

sublocale cb: DFS_skeleton
  where lookup = lookup and G = G and s = s
    and found = cb_found and on_found = cb_on_found
    and on_empty = cb_on_empty and on_backtrack = cb_on_backtrack
    and on_push = no_push
  by unfold_locales

abbreviation "DFS_collect_backtrack ≡ cb.DFS_skeleton"
abbreviation "DFS_collect_backtrack_impl ≡ cb.DFS_skeleton_impl"

end

locale DFS_CB_thms = DFS_CB +
  assumes DFS_axioms: DFS_axioms
begin

lemma spine_preservation:
  "stack (cb_on_found st) = stack st" "seen (cb_on_found st) = seen st"
  "stack (cb_on_empty st) = stack st" "seen (cb_on_empty st) = seen st"
  "stack (cb_on_backtrack v st) = stack st" "seen (cb_on_backtrack v st) = seen st"
  by (auto simp: cb_on_found_def cb_on_empty_def cb_on_backtrack_def no_push_def split: list.splits)

sublocale cb: DFS_skeleton_thms
  where lookup = lookup and G = G and s = s
    and found = cb_found and on_found = cb_on_found
    and on_empty = cb_on_empty and on_backtrack = cb_on_backtrack
    and on_push = no_push
  using DFS_axioms
  by (unfold_locales)
     (auto simp: cb.DFS_skeleton_axioms_def DFS_axioms_def
                 cb_on_found_def cb_on_empty_def cb_on_backtrack_def no_push_def split: list.splits)

subsection ‹Unfolding of the skeleton updates›

lemma upd1_unfold:
  "stack (cb.DFS_skeleton_upd1 st) = sel ((𝒩⇩G (hd (stack st))) -⇩G seen st) # stack st"
  "seen (cb.DFS_skeleton_upd1 st) = insert (sel ((𝒩⇩G (hd (stack st))) -⇩G seen st)) (seen st)"
  "return (cb.DFS_skeleton_upd1 st) = return st"
  "backtrack (cb.DFS_skeleton_upd1 st) = backtrack st"
  by (auto simp: cb.DFS_skeleton_upd1_def no_push_def Let_def)

lemma upd2_unfold:
  "stack (cb.DFS_skeleton_upd2 st) = tl (stack st)"
  "seen (cb.DFS_skeleton_upd2 st) = seen st"
  "return (cb.DFS_skeleton_upd2 st) = return st"
  "backtrack (cb.DFS_skeleton_upd2 st) =
     (case tl (stack st) of [] ⇒ backtrack st | x # _ ⇒ (x, hd (stack st)) # backtrack st)"
  by (auto simp: cb.DFS_skeleton_upd2_def cb_on_backtrack_def split: list.splits)

lemma ret1_unfold:
  "stack (cb.DFS_skeleton_ret1 st) = stack st"
  "seen (cb.DFS_skeleton_ret1 st) = seen st"
  "return (cb.DFS_skeleton_ret1 st) = NotReachable"
  "backtrack (cb.DFS_skeleton_ret1 st) = backtrack st"
  by (auto simp: cb.DFS_skeleton_ret1_def cb_on_empty_def)

lemma ret2_unfold:
  "stack (cb.DFS_skeleton_ret2 st) = stack st"
  "seen (cb.DFS_skeleton_ret2 st) = seen st"
  "return (cb.DFS_skeleton_ret2 st) = Reachable"
  "backtrack (cb.DFS_skeleton_ret2 st) = backtrack st"
  by (auto simp: cb.DFS_skeleton_ret2_def cb_on_found_def)

lemma found_unfold:
  "stack st = v # stack_tl ⟹ cb_found st = (v = t)"
  by (auto simp: cb_found_def)

subsection ‹Reachability invariants (re-derived against the skeleton)›

definition "invar_2 dfs_state = (Vwalk.vwalk (Graph.digraph_abs G) (rev (stack dfs_state)))"

definition "invar_s_in_stack dfs_state ⟷
  (stack (dfs_state) ≠ [] ⟶ last (stack dfs_state) = s)"

definition "invar_visited_through_seen dfs_state =
    (∀v ∈ t_set (seen dfs_state).
       (∀p. Vwalk.vwalk_bet (Graph.digraph_abs G) v p t ∧ distinct p ⟶ (set p ∩ set (stack dfs_state) ≠ {})))"

definition "state_rel_1 dfs_state_1 dfs_state_2
              = ( t_set (seen dfs_state_1) ⊆ t_set (seen dfs_state_2))"

subsection ‹Backtrack-collection invariants›

definition "invar_dfs_backtrack_1 state = ((dVs (set (backtrack state))) ⊆ t_set (seen state))"
definition "invar_dfs_backtrack_2 state = ((set (backtrack state)) ⊆ Graph.digraph_abs G)"
definition "invar_dfs_backtrack_3 state = ( set (backtrack state) ∩ set (edges_of_vwalk (rev (stack state))) = {})"
definition "invar_dfs_backtrack_4 state = (distinct (backtrack state))"
definition "invar_dfs_backtrack_5 state = (∀ e ∈ set (backtrack state).
                            ∄ p.  e ∈ set (edges_of_vwalk p) ∧
                            Vwalk.vwalk_bet (Graph.digraph_abs G) s p t)"

context
includes set_ops.automation2 and Graph.adjmap.automation and Graph.vset.set.automation
begin

lemma initial_invars[simp,intro]:
  "cb.invar_1 initial_state"
  "cb.invar_seen_stack initial_state"
  using DFS_axioms
  by (auto simp: cb.invar_1_def cb.invar_seen_stack_def initial_state_def DFS_axioms_def)

lemma initial_dom: "cb.DFS_skeleton_dom initial_state"
  by (intro cb.DFS_skeleton_terminates initial_invars)

subsubsection ‹invar_2›

lemma invar_2_props[invar_props_elims]:
  "invar_2 dfs_state ⟹ (Vwalk.vwalk (Graph.digraph_abs G) (rev (stack dfs_state)) ⟹ P) ⟹ P"
  by (auto simp: invar_2_def)

lemma invar_2_intro[invar_props_intros]:
  "Vwalk.vwalk (Graph.digraph_abs G) (rev (stack dfs_state)) ⟹ invar_2 dfs_state"
  by (auto simp: invar_2_def)

lemma invar_2_holds_1[invar_holds_intros]:
  assumes "cb.DFS_skeleton_call_1_conds dfs_state" "cb.invar_1 dfs_state" "invar_2 dfs_state"
  shows "invar_2 (cb.DFS_skeleton_upd1 dfs_state)"
  using assms cb.graph_inv
  by (force simp: Let_def cb.DFS_skeleton_upd1_def elim!: call_cond_elims
            elim!: invar_props_elims intro!: Vwalk.vwalk_append2 neighbourhoodI invar_props_intros)

lemma invar_2_holds_2[invar_holds_intros]:
  "⟦cb.DFS_skeleton_call_2_conds dfs_state; invar_2 dfs_state⟧ ⟹ invar_2 (cb.DFS_skeleton_upd2 dfs_state)"
  by (auto simp: upd2_unfold dest!: append_vwalk_pref elim!: invar_props_elims
           intro!: invar_props_intros elim: call_cond_elims)

lemma invar_2_holds_4[invar_holds_intros]:
  "⟦cb.DFS_skeleton_ret_1_conds dfs_state; invar_2 dfs_state⟧ ⟹ invar_2 (cb.DFS_skeleton_ret1 dfs_state)"
  by (auto elim!: invar_props_elims intro: invar_props_intros simp: ret1_unfold)

lemma invar_2_holds_5[invar_holds_intros]:
  "⟦cb.DFS_skeleton_ret_2_conds dfs_state; invar_2 dfs_state⟧ ⟹ invar_2 (cb.DFS_skeleton_ret2 dfs_state)"
  by (auto elim!: invar_props_elims intro: invar_props_intros simp: ret2_unfold)

lemma invar_2_holds[invar_holds_intros]:
   assumes "cb.DFS_skeleton_dom dfs_state" "cb.invar_1 dfs_state" "invar_2 dfs_state"
   shows "invar_2 (cb.DFS_skeleton dfs_state)"
  using assms(2-3)
proof(induction rule: cb.DFS_skeleton_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule cb.DFS_skeleton_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-) invar_holds_intros simp: cb.DFS_skeleton_simps[OF IH(1)])
qed

subsubsection ‹invar_s_in_stack›

lemma invar_s_in_stack_props[invar_props_elims]:
   "invar_s_in_stack dfs_state ⟹
     (⟦(stack (dfs_state) ≠ [] ⟹ last (stack dfs_state) = s)⟧ ⟹ P) ⟹ P "
  by (auto simp: invar_s_in_stack_def)

lemma invar_s_in_stack_intro[invar_props_intros]:
  "⟦(stack (dfs_state) ≠ [] ⟹ last (stack dfs_state) = s)⟧ ⟹ invar_s_in_stack dfs_state"
  by (auto simp: invar_s_in_stack_def)

lemma invar_s_in_stack_holds_1[invar_holds_intros]:
  "⟦cb.DFS_skeleton_call_1_conds dfs_state; cb.invar_1 dfs_state; invar_s_in_stack dfs_state⟧ ⟹
     invar_s_in_stack (cb.DFS_skeleton_upd1 dfs_state)"
  by (force simp: Let_def cb.DFS_skeleton_upd1_def dest!: append_vwalk_pref elim!: call_cond_elims
            elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_s_in_stack_holds_2[invar_holds_intros]:
  "⟦cb.DFS_skeleton_call_2_conds dfs_state; cb.invar_1 dfs_state; invar_s_in_stack dfs_state⟧ ⟹
     invar_s_in_stack (cb.DFS_skeleton_upd2 dfs_state)"
  by (auto elim!: call_cond_elims simp: upd2_unfold elim: vwalk_betE
           elim!: invar_props_elims dest!: Graph.vset.emptyD append_vwalk_pref intro!: invar_props_intros)

lemma invar_s_in_stack_holds_4[invar_holds_intros]:
   "⟦cb.DFS_skeleton_ret_1_conds dfs_state; invar_s_in_stack dfs_state⟧ ⟹
       invar_s_in_stack (cb.DFS_skeleton_ret1 dfs_state)"
  by (auto elim!: invar_props_elims intro!: invar_props_intros simp: ret1_unfold)

lemma invar_s_in_stack_holds_5[invar_holds_intros]:
  "⟦cb.DFS_skeleton_ret_2_conds dfs_state; invar_s_in_stack dfs_state⟧ ⟹
     invar_s_in_stack (cb.DFS_skeleton_ret2 dfs_state)"
  by (auto elim!: invar_props_elims intro!: invar_props_intros simp: ret2_unfold)

lemma invar_s_in_stack_holds[invar_holds_intros]:
   assumes "cb.DFS_skeleton_dom dfs_state" "cb.invar_1 dfs_state" "invar_s_in_stack dfs_state"
   shows "invar_s_in_stack (cb.DFS_skeleton dfs_state)"
   using assms(2-)
proof(induction rule: cb.DFS_skeleton_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule cb.DFS_skeleton_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-) invar_holds_intros simp: cb.DFS_skeleton_simps[OF IH(1)])
qed

subsubsection ‹invar_visited_through_seen›

lemma invar_visited_through_seen_props[elim!]:
   "invar_visited_through_seen dfs_state ⟹
     (⟦⋀v p. ⟦v ∈ t_set (seen dfs_state);
              (Vwalk.vwalk_bet (Graph.digraph_abs G) v p t); distinct p ⟧ ⟹
              set p ∩ set (stack dfs_state) ≠ {}⟧ ⟹ P) ⟹ P "
  by (auto simp: invar_visited_through_seen_def)

lemma invar_visited_through_seen_intro[invar_props_intros]:
  "⟦⋀v p. ⟦v ∈ t_set (seen dfs_state);
           (Vwalk.vwalk_bet (Graph.digraph_abs G) v p t); distinct p⟧ ⟹
           set p ∩ set (stack dfs_state) ≠ {}⟧ ⟹ invar_visited_through_seen dfs_state"
  by (auto simp: invar_visited_through_seen_def)

lemma invar_visited_through_seen_holds_1[invar_holds_intros]:
  "⟦cb.DFS_skeleton_call_1_conds dfs_state; cb.invar_1 dfs_state; cb.invar_seen_stack dfs_state;
    invar_visited_through_seen dfs_state⟧
    ⟹ invar_visited_through_seen (cb.DFS_skeleton_upd1 dfs_state)"
  by(fastforce simp: Let_def cb.DFS_skeleton_upd1_def dest: append_vwalk_pref hd_of_vwalk_bet''
               elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_visited_through_seen_holds_2[invar_holds_intros]:
  "⟦cb.DFS_skeleton_call_2_conds dfs_state; cb.invar_1 dfs_state; cb.invar_seen_stack dfs_state;
    invar_visited_through_seen dfs_state⟧ ⟹ invar_visited_through_seen (cb.DFS_skeleton_upd2 dfs_state)"
proof(rule invar_props_intros, elim invar_visited_through_seen_props call_cond_elims exE, goal_cases)
  case (1 v1 p v2 stack_tl)
  hence "set p ∩ set (stack dfs_state) ≠ {}"
    by (auto simp: upd2_unfold)
  then obtain u where u: "u ∈ set p ∩ set (stack dfs_state)"
    by auto
  show ?case
  proof(cases "u ∈ set stack_tl")
    case True
    thus ?thesis
      using 1 u by (auto simp: upd2_unfold)
  next
    case False
    hence uv2: "u = v2"
      using 1 u by auto
    then obtain p1 p2 where pdec[simp]: "p = p1 @ [v2] @ p2"
      using u by (auto simp: in_set_conv_decomp)
    hence "set (v2 # p2) ∩ set (stack dfs_state) ≠ {}"
      using 1 by (auto simp: upd2_unfold)
    have vne: "v2 ≠ t"
      using 1 by (auto simp: found_unfold)
    show ?thesis
    proof(cases "p2 = []")
      case True
      thus ?thesis
        using 1 vne by (auto simp: vwalk_bet_snoc)
    next
      case False
      hence "hd p2 ∈ t_set (𝒩⇩G v2)"
        using ‹vwalk_bet (Graph.digraph_abs G) v1 p t›
        by (auto dest!: split_vwalk simp: neq_Nil_conv)
      hence "hd p2 ∈ t_set (seen dfs_state)"
        using 1 by (fastforce elim!: invar_props_elims simp del: pdec)
      hence "set p2 ∩ set (stack dfs_state) ≠ {}"
        using 1 False by (fastforce simp: upd2_unfold neq_Nil_conv dest!: split_vwalk)
      moreover have "v2 ∉ set p2"
        using ‹distinct p› by auto
      ultimately have "set p2 ∩ set (stack (cb.DFS_skeleton_upd2 dfs_state)) ≠ {}"
        using 1 by (auto simp: upd2_unfold)
      thus ?thesis by auto
    qed
  qed
qed

lemma invar_visited_through_seen_holds_4[invar_holds_intros]:
  "⟦cb.DFS_skeleton_ret_1_conds dfs_state; invar_visited_through_seen dfs_state⟧ ⟹
     invar_visited_through_seen (cb.DFS_skeleton_ret1 dfs_state)"
  by (auto intro: invar_props_intros simp: ret1_unfold)

lemma invar_visited_through_seen_holds_5[invar_holds_intros]:
  "⟦cb.DFS_skeleton_ret_2_conds dfs_state; invar_visited_through_seen dfs_state⟧ ⟹
     invar_visited_through_seen (cb.DFS_skeleton_ret2 dfs_state)"
  by (auto intro: invar_props_intros simp: ret2_unfold)

lemma invar_visited_through_seen_holds[invar_holds_intros]:
   assumes "cb.DFS_skeleton_dom dfs_state" "cb.invar_1 dfs_state" "cb.invar_seen_stack dfs_state"
           "invar_visited_through_seen dfs_state"
   shows "invar_visited_through_seen (cb.DFS_skeleton dfs_state)"
   using assms(2-)
proof(induction rule: cb.DFS_skeleton_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule cb.DFS_skeleton_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-) invar_holds_intros simp: cb.DFS_skeleton_simps[OF IH(1)])
qed

subsubsection ‹state relation›

lemma state_rel_1_props[elim!]: "state_rel_1 dfs_state_1 dfs_state_2 ⟹
                                  (t_set (seen dfs_state_1) ⊆ t_set (seen dfs_state_2) ⟹ P) ⟹ P "
  by (auto simp: state_rel_1_def)

lemma state_rel_1_intro[state_rel_intros]:
  "⟦t_set (seen dfs_state_1) ⊆ t_set (seen dfs_state_2)⟧ ⟹ state_rel_1 dfs_state_1 dfs_state_2"
  by (auto simp: state_rel_1_def)

lemma state_rel_1_trans:
  "⟦state_rel_1 dfs_state_1 dfs_state_2; state_rel_1 dfs_state_2 dfs_state_3⟧ ⟹
   state_rel_1 dfs_state_1 dfs_state_3"
  by (auto intro!: state_rel_intros)

lemma state_rel_1_holds_1[state_rel_holds_intros]:
  "⟦cb.DFS_skeleton_call_1_conds dfs_state; cb.invar_1 dfs_state⟧ ⟹ state_rel_1 dfs_state (cb.DFS_skeleton_upd1 dfs_state)"
  by (auto simp: Let_def cb.DFS_skeleton_upd1_def elim!: invar_props_elims intro!: state_rel_intros)

lemma state_rel_1_holds_2[state_rel_holds_intros]:
  "⟦cb.DFS_skeleton_call_2_conds dfs_state; cb.invar_1 dfs_state⟧ ⟹ state_rel_1 dfs_state (cb.DFS_skeleton_upd2 dfs_state)"
  by (auto simp: upd2_unfold intro!: state_rel_intros elim: call_cond_elims)

lemma state_rel_1_holds_4[state_rel_holds_intros]:
  "⟦cb.DFS_skeleton_ret_1_conds dfs_state⟧ ⟹ state_rel_1 dfs_state (cb.DFS_skeleton_ret1 dfs_state)"
  by (auto intro!: state_rel_intros simp: ret1_unfold)

lemma state_rel_1_holds_5[state_rel_holds_intros]:
  "⟦cb.DFS_skeleton_ret_2_conds dfs_state⟧ ⟹ state_rel_1 dfs_state (cb.DFS_skeleton_ret2 dfs_state)"
  by (auto intro!: state_rel_intros simp: ret2_unfold)

lemma state_rel_1_holds[state_rel_holds_intros]:
   assumes "cb.DFS_skeleton_dom dfs_state" "cb.invar_1 dfs_state"
   shows "state_rel_1 dfs_state (cb.DFS_skeleton dfs_state)"
   using assms(2-)
proof(induction rule: cb.DFS_skeleton_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule cb.DFS_skeleton_cases[where dfs_state = dfs_state])
    by (auto intro: state_rel_1_trans invar_holds_intros state_rel_holds_intros intro!: IH(2-) simp: cb.DFS_skeleton_simps[OF IH(1)])
qed

subsubsection ‹Return-condition tracking + reachability correctness›

lemma ret_1[ret_holds_intros]: "cb.DFS_skeleton_ret_1_conds (dfs_state) ⟹ cb.DFS_skeleton_ret_1_conds (cb.DFS_skeleton_ret1 dfs_state)"
  by (auto elim!: call_cond_elims intro!: call_cond_intros simp: ret1_unfold)

lemma ret1_holds[ret_holds_intros]:
   assumes "cb.DFS_skeleton_dom dfs_state" "return (cb.DFS_skeleton dfs_state) = NotReachable"
   shows "cb.DFS_skeleton_ret_1_conds (cb.DFS_skeleton dfs_state)"
   using assms(2-)
proof(induction rule: cb.DFS_skeleton_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule cb.DFS_skeleton_cases[where dfs_state = dfs_state])
    using IH(4)
    by (auto intro: ret_holds_intros intro!: IH(2-) simp: cb.DFS_skeleton_simps[OF IH(1)] ret2_unfold)
qed

lemma DFS_correct_ret_1:
  "⟦invar_visited_through_seen dfs_state; cb.DFS_skeleton_ret_1_conds dfs_state; u ∈ t_set (seen dfs_state)⟧
         ⟹ ∄p. distinct p ∧ vwalk_bet (Graph.digraph_abs G) u p t"
  by (auto elim!: call_cond_elims invar_props_elims)

lemma ret_2[ret_holds_intros]: "cb.DFS_skeleton_ret_2_conds (dfs_state) ⟹ cb.DFS_skeleton_ret_2_conds (cb.DFS_skeleton_ret2 dfs_state)"
  by (auto elim!: call_cond_elims intro!: call_cond_intros simp: ret2_unfold cb_found_def)

lemma ret2_holds[ret_holds_intros]:
   assumes "cb.DFS_skeleton_dom dfs_state" "return (cb.DFS_skeleton dfs_state) = Reachable"
   shows "cb.DFS_skeleton_ret_2_conds (cb.DFS_skeleton dfs_state)"
   using assms(2-)
proof(induction rule: cb.DFS_skeleton_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule cb.DFS_skeleton_cases[where dfs_state = dfs_state])
    using IH(4)
    by (auto intro: ret_holds_intros intro!: IH(2-) simp: cb.DFS_skeleton_simps[OF IH(1)] ret1_unfold)
qed

lemma DFS_correct_ret_2:
  "⟦invar_2 dfs_state; cb.DFS_skeleton_ret_2_conds dfs_state⟧
         ⟹ vwalk_bet (Graph.digraph_abs G) (last (stack dfs_state)) (rev (stack dfs_state)) t"
  by (auto elim!: call_cond_elims invar_props_elims simp: hd_rev vwalk_bet_def cb_found_def
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
  assumes "return (DFS_collect_backtrack initial_state) = NotReachable"
  shows   "∄p. distinct p ∧ vwalk_bet (Graph.digraph_abs G) s p t"
proof-
  have "s ∈ t_set (seen (DFS_collect_backtrack initial_state))"
    using state_rel_1_holds[OF initial_dom initial_invars(1)]
    by (auto simp: initial_state_def state_rel_1_def)
  thus ?thesis
    using assms
    by(intro DFS_correct_ret_1[where dfs_state = "DFS_collect_backtrack initial_state"])
      (auto intro!: invar_holds_intros ret_holds_intros initial_dom initial_invars initial_state_props)
qed

theorem DFS_correct_1_strong:
  assumes "return (DFS_collect_backtrack initial_state) = NotReachable"
  shows   "∄p. vwalk_bet (Graph.digraph_abs G) s p t"
  using DFS_correct_1[OF assms] vwalk_bet_to_distinct_is_distinct_vwalk_bet
  by(force simp add: distinct_vwalk_bet_def)

theorem DFS_correct_2:
  assumes  "return (DFS_collect_backtrack initial_state) = Reachable"
  shows "vwalk_bet (Graph.digraph_abs G) s (rev (stack (DFS_collect_backtrack initial_state))) t" (is ?thesis1)
        "distinct (rev (stack (DFS_collect_backtrack initial_state)))" (is ?thesis2)
proof-
  have "vwalk_bet
              (Graph.digraph_abs G)
              (last (stack (DFS_collect_backtrack initial_state)))
              (rev (stack (DFS_collect_backtrack initial_state))) t"
    using assms
    by(auto intro!: invar_holds_intros ret_holds_intros initial_dom initial_invars initial_state_props
                       DFS_correct_ret_2[where dfs_state = "DFS_collect_backtrack initial_state"])
  moreover hence "(last (stack (DFS_collect_backtrack initial_state))) = s"
    by(fastforce intro!: invar_holds_intros initial_dom initial_invars initial_state_props
                 intro: invar_s_in_stack_props[where dfs_state = "DFS_collect_backtrack initial_state"])+
  ultimately show ?thesis1
    by auto
  show ?thesis2
    using initial_dom initial_invars cb.invar_seen_stack_holds cb.invar_seen_stack_props
    by auto
qed

subsection ‹Backtrack-collection invariants hold›

lemma invar_dfs_backtrack_1I: "((dVs (set (backtrack state))) ⊆ t_set (seen state)) ⟹ invar_dfs_backtrack_1 state"
  by(auto simp add: invar_dfs_backtrack_1_def)
lemma invar_dfs_backtrack_1E: "invar_dfs_backtrack_1 state ⟹
                      (((dVs (set (backtrack state))) ⊆ t_set (seen state)) ⟹ P) ⟹ P"
  by(auto simp add: invar_dfs_backtrack_1_def)
lemma invar_dfs_backtrack_2I: " ((set (backtrack state)) ⊆ Graph.digraph_abs G) ⟹ invar_dfs_backtrack_2 state"
  by(auto simp add: invar_dfs_backtrack_2_def)
lemma invar_dfs_backtrack_2E: " invar_dfs_backtrack_2 state ⟹
           (((set (backtrack state)) ⊆ Graph.digraph_abs G) ⟹P) ⟹ P"
  by(auto simp add: invar_dfs_backtrack_2_def)
lemma invar_dfs_backtrack_3I:"set (backtrack state) ∩ set (edges_of_vwalk (rev (stack state))) = {} ⟹ invar_dfs_backtrack_3 state"
  by(auto simp add: invar_dfs_backtrack_3_def)
lemma invar_dfs_backtrack_3E:"invar_dfs_backtrack_3 state ⟹
        (set (backtrack state) ∩ set (edges_of_vwalk (rev (stack state))) = {} ⟹ P) ⟹ P"
  by(auto simp add: invar_dfs_backtrack_3_def)
lemma invar_dfs_backtrack_4I: "distinct (backtrack state) ⟹ invar_dfs_backtrack_4 state"
  by(auto simp add: invar_dfs_backtrack_4_def)
lemma invar_dfs_backtrack_4E: "invar_dfs_backtrack_4 state ⟹ (distinct (backtrack state) ⟹ P) ⟹ P"
  by(auto simp add: invar_dfs_backtrack_4_def)
lemma invar_dfs_backtrack_5I: "(⋀ e. e ∈ set (backtrack state) ⟹
                            ∄ p.  e ∈ set (edges_of_vwalk p) ∧
                            Vwalk.vwalk_bet (Graph.digraph_abs G) s p t) ⟹ invar_dfs_backtrack_5 state"
  by(auto simp add: invar_dfs_backtrack_5_def)
lemma invar_dfs_backtrack_5E: "invar_dfs_backtrack_5 state ⟹ ((⋀ e. e ∈ set (backtrack state) ⟹
                            ∄ p. e ∈ set (edges_of_vwalk p) ∧
                            Vwalk.vwalk_bet (Graph.digraph_abs G) s p t) ⟹ P) ⟹ P"
  by(auto simp add: invar_dfs_backtrack_5_def)

subsubsection ‹invar_dfs_backtrack_1: collected endpoints are seen›

lemma invar_dfs_backtrack_1_holds_1[invar_holds_intros]:
  "⟦cb.DFS_skeleton_call_1_conds dfs_state; invar_dfs_backtrack_1 dfs_state; cb.invar_1 dfs_state⟧ ⟹
      invar_dfs_backtrack_1 (cb.DFS_skeleton_upd1 dfs_state)"
  by(auto intro!: invar_dfs_backtrack_1I simp add: upd1_unfold
      elim!: call_cond_elims invar_dfs_backtrack_1E cb.invar_1_props)

lemma invar_dfs_backtrack_1_holds_2[invar_holds_intros]:
  assumes "cb.DFS_skeleton_call_2_conds dfs_state" "invar_dfs_backtrack_1 dfs_state" "cb.invar_1 dfs_state"
       "cb.invar_seen_stack dfs_state"
  shows "invar_dfs_backtrack_1 (cb.DFS_skeleton_upd2 dfs_state)"
proof(cases "tl (stack dfs_state)")
  case Nil
  then show ?thesis
    using assms(2) by (auto intro!: invar_dfs_backtrack_1I simp: upd2_unfold elim!: invar_dfs_backtrack_1E)
next
  case (Cons x xs)
  have stk: "stack dfs_state ≠ []" using assms(1) by (auto elim!: call_cond_elims)
  have sub: "set (stack dfs_state) ⊆ t_set (seen dfs_state)"
    using assms(4) by (auto elim!: cb.invar_seen_stack_props)
  have "x ∈ set (stack dfs_state)" using Cons stk by (cases "stack dfs_state") auto
  moreover have "hd (stack dfs_state) ∈ set (stack dfs_state)" using stk by (cases "stack dfs_state") auto
  ultimately have xy: "x ∈ t_set (seen dfs_state)" "hd (stack dfs_state) ∈ t_set (seen dfs_state)"
    using sub by auto
  have "dVs (set (backtrack dfs_state)) ⊆ t_set (seen dfs_state)"
    using assms(2) by (auto elim!: invar_dfs_backtrack_1E)
  then have "dVs (Set.insert (x, hd (stack dfs_state)) (set (backtrack dfs_state))) ⊆ t_set (seen dfs_state)"
    using xy by (auto elim!: dVs_insert)
  then show ?thesis
    using Cons by (auto intro!: invar_dfs_backtrack_1I simp: upd2_unfold)
qed

lemma invar_dfs_backtrack_1_holds_3[invar_holds_intros]:
  "⟦invar_dfs_backtrack_1 dfs_state⟧ ⟹ invar_dfs_backtrack_1 (cb.DFS_skeleton_ret1 dfs_state)"
  by(auto intro!: invar_dfs_backtrack_1I simp add: ret1_unfold elim!: invar_dfs_backtrack_1E)

lemma invar_dfs_backtrack_1_holds_4[invar_holds_intros]:
  "⟦invar_dfs_backtrack_1 dfs_state⟧ ⟹ invar_dfs_backtrack_1 (cb.DFS_skeleton_ret2 dfs_state)"
  by(auto intro!: invar_dfs_backtrack_1I simp add: ret2_unfold elim!: invar_dfs_backtrack_1E)

lemma invar_dfs_backtrack_1_holds:
  assumes "cb.DFS_skeleton_dom dfs_state" "invar_dfs_backtrack_1 dfs_state"
    "cb.invar_1 dfs_state" "cb.invar_seen_stack dfs_state"
  shows "invar_dfs_backtrack_1 (cb.DFS_skeleton dfs_state)"
  using assms(2-)
proof(induction rule: cb.DFS_skeleton_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule cb.DFS_skeleton_cases[where dfs_state = dfs_state])
    by(auto intro!: IH(2-) invar_holds_intros simp: cb.DFS_skeleton_simps[OF IH(1)])
qed

subsubsection ‹invar_dfs_backtrack_2: collected edges are graph edges›

lemma invar_dfs_backtrack_2_holds_1[invar_holds_intros]:
  "⟦cb.DFS_skeleton_call_1_conds dfs_state; invar_dfs_backtrack_2 dfs_state; cb.invar_1 dfs_state⟧ ⟹
      invar_dfs_backtrack_2 (cb.DFS_skeleton_upd1 dfs_state)"
  by(auto intro!: invar_dfs_backtrack_2I simp add: upd1_unfold
      elim!: call_cond_elims invar_dfs_backtrack_2E cb.invar_1_props)

lemma invar_dfs_backtrack_2_holds_2[invar_holds_intros]:
  "⟦cb.DFS_skeleton_call_2_conds dfs_state; invar_dfs_backtrack_2 dfs_state; cb.invar_1 dfs_state;
       invar_2 dfs_state⟧ ⟹
      invar_dfs_backtrack_2 (cb.DFS_skeleton_upd2 dfs_state)"
  using append_vwalk_suff
  by(cases "tl (stack dfs_state)")
    (fastforce intro!: invar_dfs_backtrack_2I simp add: upd2_unfold
      elim!: call_cond_elims invar_dfs_backtrack_2E cb.invar_1_props invar_2_props)+

lemma invar_dfs_backtrack_2_holds_3[invar_holds_intros]:
  "⟦invar_dfs_backtrack_2 dfs_state⟧ ⟹ invar_dfs_backtrack_2 (cb.DFS_skeleton_ret1 dfs_state)"
  by(auto intro!: invar_dfs_backtrack_2I simp add: ret1_unfold elim!: invar_dfs_backtrack_2E)

lemma invar_dfs_backtrack_2_holds_4[invar_holds_intros]:
  "⟦invar_dfs_backtrack_2 dfs_state⟧ ⟹ invar_dfs_backtrack_2 (cb.DFS_skeleton_ret2 dfs_state)"
  by(auto intro!: invar_dfs_backtrack_2I simp add: ret2_unfold elim!: invar_dfs_backtrack_2E)

lemma invar_dfs_backtrack_2_holds:
  assumes "cb.DFS_skeleton_dom dfs_state" "invar_dfs_backtrack_2 dfs_state"
    "cb.invar_1 dfs_state" "invar_2 dfs_state"
  shows  "invar_dfs_backtrack_2 (cb.DFS_skeleton dfs_state)"
  using assms(2-)
proof(induction rule: cb.DFS_skeleton_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule cb.DFS_skeleton_cases[where dfs_state = dfs_state])
    by(auto intro!: IH(2-) invar_holds_intros simp: cb.DFS_skeleton_simps[OF IH(1)])
qed

subsubsection ‹invar_dfs_backtrack_3: collected edges are off the current search path›

lemma invar_dfs_backtrack_3_holds_1[invar_holds_intros]:
  "⟦cb.DFS_skeleton_call_1_conds dfs_state; invar_dfs_backtrack_3 dfs_state;
       invar_dfs_backtrack_1 dfs_state; cb.invar_1 dfs_state; cb.invar_seen_stack dfs_state⟧ ⟹
      invar_dfs_backtrack_3 (cb.DFS_skeleton_upd1 dfs_state)"
  by(auto intro!: invar_dfs_backtrack_3I
      simp add: upd1_unfold edges_of_vwalk_append_2[of "[_, _]", simplified]
      elim!: call_cond_elims invar_dfs_backtrack_3E cb.invar_1_props cb.invar_seen_stack_props
      invar_dfs_backtrack_1E
      dest!: Graph.vset.choose')+

lemma invar_dfs_backtrack_3_holds_2[invar_holds_intros]:
  assumes "cb.DFS_skeleton_call_2_conds dfs_state" "invar_dfs_backtrack_3 dfs_state"
       "cb.invar_1 dfs_state" "cb.invar_seen_stack dfs_state"
  shows "invar_dfs_backtrack_3 (cb.DFS_skeleton_upd2 dfs_state)"
proof(cases "tl (stack dfs_state)")
  case Nil
  have disj: "set (backtrack dfs_state) ∩ set (edges_of_vwalk (rev (stack dfs_state))) = {}"
    using assms(2) by (auto elim!: invar_dfs_backtrack_3E)
  have "set (edges_of_vwalk (rev (tl (stack dfs_state)))) ⊆ set (edges_of_vwalk (rev (stack dfs_state)))"
    using Nil by (cases "stack dfs_state") auto
  then show ?thesis
    using disj Nil by (auto intro!: invar_dfs_backtrack_3I simp: upd2_unfold)
next
  case (Cons x xs)
  have stk: "stack dfs_state = hd (stack dfs_state) # x # xs"
    using Cons by (cases "stack dfs_state") auto
  have dist: "distinct (stack dfs_state)"
    using assms(4) by (auto elim!: cb.invar_seen_stack_props)
  have disj: "set (backtrack dfs_state) ∩ set (edges_of_vwalk (rev (stack dfs_state))) = {}"
    using assms(2) by (auto elim!: invar_dfs_backtrack_3E)
  have rev_eq: "rev (stack dfs_state) = rev (x # xs) @ [hd (stack dfs_state)]"
  proof -
    have "rev (stack dfs_state) = rev (hd (stack dfs_state) # x # xs)" using stk by simp
    also have "... = rev (x # xs) @ [hd (stack dfs_state)]" by simp
    finally show ?thesis .
  qed
  have rne: "rev (x # xs) ≠ []" by simp
  have last_eq: "last (rev (x # xs)) = x" by (simp add: last_rev)
  have edges_eq: "edges_of_vwalk (rev (stack dfs_state))
        = edges_of_vwalk (rev (x # xs)) @ [(x, hd (stack dfs_state))]"
    using edges_of_vwalk_append_3[OF rne, of "[hd (stack dfs_state)]"] rev_eq last_eq by simp
  have edges_split: "set (edges_of_vwalk (rev (stack dfs_state)))
        = set (edges_of_vwalk (rev (x # xs))) ∪ {(x, hd (stack dfs_state))}"
    using edges_eq by simp
  have "distinct (hd (stack dfs_state) # x # xs)" using dist stk by simp
  hence hd_notin_tl: "hd (stack dfs_state) ∉ set (x # xs)" by simp
  have newedge_notin: "(x, hd (stack dfs_state)) ∉ set (edges_of_vwalk (rev (x # xs)))"
  proof
    assume "(x, hd (stack dfs_state)) ∈ set (edges_of_vwalk (rev (x # xs)))"
    then have "hd (stack dfs_state) ∈ set (rev (x # xs))"
      using v_in_edge_in_vwalk(2) by fastforce
    then have "hd (stack dfs_state) ∈ set (x # xs)" by simp
    then show False using hd_notin_tl by simp
  qed
  have bt_disj: "set (backtrack dfs_state) ∩ set (edges_of_vwalk (rev (x # xs))) = {}"
    using disj edges_split by auto
  have bt2: "backtrack (cb.DFS_skeleton_upd2 dfs_state) = (x, hd (stack dfs_state)) # backtrack dfs_state"
    using Cons by (simp add: upd2_unfold)
  have st2: "stack (cb.DFS_skeleton_upd2 dfs_state) = x # xs"
    using Cons by (simp add: upd2_unfold)
  have "set (backtrack (cb.DFS_skeleton_upd2 dfs_state))
        ∩ set (edges_of_vwalk (rev (stack (cb.DFS_skeleton_upd2 dfs_state)))) = {}"
    unfolding bt2 st2 using bt_disj newedge_notin by auto
  then show ?thesis
    by (rule invar_dfs_backtrack_3I)
qed

lemma invar_dfs_backtrack_3_holds_3[invar_holds_intros]:
  "⟦invar_dfs_backtrack_3 dfs_state⟧ ⟹ invar_dfs_backtrack_3 (cb.DFS_skeleton_ret1 dfs_state)"
  by(auto intro!: invar_dfs_backtrack_3I simp add: ret1_unfold elim!: invar_dfs_backtrack_3E)

lemma invar_dfs_backtrack_3_holds_4[invar_holds_intros]:
  "⟦invar_dfs_backtrack_3 dfs_state⟧ ⟹ invar_dfs_backtrack_3 (cb.DFS_skeleton_ret2 dfs_state)"
  by(auto intro!: invar_dfs_backtrack_3I simp add: ret2_unfold elim!: invar_dfs_backtrack_3E)

lemma invar_dfs_backtrack_3_holds:
  assumes "cb.DFS_skeleton_dom dfs_state" "invar_dfs_backtrack_3 dfs_state"
    "invar_dfs_backtrack_1 dfs_state" "cb.invar_1 dfs_state" "cb.invar_seen_stack dfs_state"
  shows  "invar_dfs_backtrack_3 (cb.DFS_skeleton dfs_state)"
  using assms(2-)
proof(induction rule: cb.DFS_skeleton_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule cb.DFS_skeleton_cases[where dfs_state = dfs_state])
    by(auto intro!: IH(2-) invar_holds_intros simp: cb.DFS_skeleton_simps[OF IH(1)])
qed

subsubsection ‹invar_dfs_backtrack_4: collected edges are distinct›

lemma invar_dfs_backtrack_4_holds_1[invar_holds_intros]:
  "⟦cb.DFS_skeleton_call_1_conds dfs_state; invar_dfs_backtrack_4 dfs_state⟧ ⟹
      invar_dfs_backtrack_4 (cb.DFS_skeleton_upd1 dfs_state)"
  by(auto intro!: invar_dfs_backtrack_4I simp add: upd1_unfold elim!: invar_dfs_backtrack_4E)

lemma invar_dfs_backtrack_4_holds_2[invar_holds_intros]:
  "⟦cb.DFS_skeleton_call_2_conds dfs_state; invar_dfs_backtrack_4 dfs_state;
       invar_dfs_backtrack_3 dfs_state⟧ ⟹
      invar_dfs_backtrack_4 (cb.DFS_skeleton_upd2 dfs_state)"
  by(cases "tl (stack dfs_state)")
    (auto intro!: invar_dfs_backtrack_4I
      simp add: upd2_unfold edges_of_vwalk_append_2[of "[_, _]", simplified]
      elim!: call_cond_elims invar_dfs_backtrack_3E invar_dfs_backtrack_4E)

lemma invar_dfs_backtrack_4_holds_3[invar_holds_intros]:
  "⟦invar_dfs_backtrack_4 dfs_state⟧ ⟹ invar_dfs_backtrack_4 (cb.DFS_skeleton_ret1 dfs_state)"
  by(auto intro!: invar_dfs_backtrack_4I simp add: ret1_unfold elim!: invar_dfs_backtrack_4E)

lemma invar_dfs_backtrack_4_holds_4[invar_holds_intros]:
  "⟦invar_dfs_backtrack_4 dfs_state⟧ ⟹ invar_dfs_backtrack_4 (cb.DFS_skeleton_ret2 dfs_state)"
  by(auto intro!: invar_dfs_backtrack_4I simp add: ret2_unfold elim!: invar_dfs_backtrack_4E)

lemma invar_dfs_backtrack_4_holds:
  assumes "cb.DFS_skeleton_dom dfs_state" "invar_dfs_backtrack_4 dfs_state"
    "invar_dfs_backtrack_3 dfs_state" "invar_dfs_backtrack_1 dfs_state"
    "cb.invar_1 dfs_state" "cb.invar_seen_stack dfs_state"
  shows  "invar_dfs_backtrack_4 (cb.DFS_skeleton dfs_state)"
  using assms(2-)
proof(induction rule: cb.DFS_skeleton_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule cb.DFS_skeleton_cases[where dfs_state = dfs_state])
    by(auto intro!: IH(2-) invar_holds_intros simp: cb.DFS_skeleton_simps[OF IH(1)])
qed

subsubsection ‹invar_dfs_backtrack_5: on an acyclic graph, collected edges lie on no s-t walk›

lemma invar_dfs_backtrack_5_holds_1[invar_holds_intros]:
  "⟦cb.DFS_skeleton_call_1_conds dfs_state; invar_dfs_backtrack_5 dfs_state⟧ ⟹
      invar_dfs_backtrack_5 (cb.DFS_skeleton_upd1 dfs_state)"
  by(auto intro!: invar_dfs_backtrack_5I simp add: upd1_unfold elim!: invar_dfs_backtrack_5E)

lemma invar_dfs_backtrack_5_holds_2[invar_holds_intros]:
  assumes "cb.DFS_skeleton_call_2_conds dfs_state"
    "dir_acyc (Graph.digraph_abs G)"
    "invar_dfs_backtrack_5 dfs_state"
    "invar_dfs_backtrack_4 dfs_state"
    "invar_dfs_backtrack_3 dfs_state"
    "invar_dfs_backtrack_1 dfs_state"
    "cb.invar_seen_stack dfs_state"
    "invar_visited_through_seen dfs_state"
    "cb.invar_1 dfs_state"
    "invar_2 dfs_state"
  shows  "invar_dfs_backtrack_5 (cb.DFS_skeleton_upd2 dfs_state)"
proof(cases "tl (stack dfs_state)")
  case Nil
  then show ?thesis
    using assms(3) by(auto intro!: invar_dfs_backtrack_5I simp add: upd2_unfold elim!: invar_dfs_backtrack_5E)
next
  case (Cons u tail)
  have stk: "stack dfs_state ≠ []" using assms(1) by (auto elim!: call_cond_elims)
  have hd_ne_t: "hd (stack dfs_state) ≠ t"
    using assms(1) stk by (auto elim!: call_cond_elims simp: cb_found_def split: list.splits)
  have bt2: "backtrack (cb.DFS_skeleton_upd2 dfs_state) = (u, hd (stack dfs_state)) # backtrack dfs_state"
    using Cons by (simp add: upd2_unfold)
  have False
    if "a = u ∧ b = hd (stack dfs_state) ∨ (a, b) ∈ set (backtrack dfs_state)"
       "(a, b) ∈ set (edges_of_vwalk p)" "vwalk_bet [G]⇩g s p t" for a b p
  proof-
    note one = that
    show ?thesis
    proof(cases rule: disjE[OF one(1)])
      case 1
      hence 1: "a = u" "b = hd (stack dfs_state)" by auto
      hence "b ∈ set p" using one(2) v_in_edge_in_vwalk_gen(2) by force
      then obtain p1 p2 where p_split: "p = p1@[b]@p2"
        by(auto simp add: in_set_conv_decomp)
      have p2_no_empty: "p2 ≠ []"
        using p_split one(3) 1(2) hd_ne_t
        by (auto simp add: vwalk_bet_snoc)
      hence "vwalk_bet [G]⇩g b (b#p2) t"
        using one(3)
        by (simp add: p_split vwalk_bet_suff)
      then obtain p2' where p2'_walk: "vwalk_bet [G]⇩g b (p2') t" and p2'_dist: "distinct p2'"
        by(auto dest!: vwalk_bet_to_distinct_is_distinct_vwalk_bet
            simp add: distinct_vwalk_bet_def)
      have b_seen: "b ∈ t_set (seen dfs_state)"
        using assms(6,7) 1(2) stk
        by(auto elim!: cb.invar_seen_stack_props invar_dfs_backtrack_1E
                simp: subset_iff hd_in_set)
      have vts_upd2: "invar_visited_through_seen (cb.DFS_skeleton_upd2 dfs_state)"
        by (rule invar_visited_through_seen_holds_2[OF assms(1,9,7,8)])
      have b_seen2: "b ∈ t_set (seen (cb.DFS_skeleton_upd2 dfs_state))"
        using b_seen by (simp add: upd2_unfold)
      have "∀p. vwalk_bet [G]⇩g b p t ∧ distinct p ⟶ set p ∩ set (stack (cb.DFS_skeleton_upd2 dfs_state)) ≠ {}"
        using vts_upd2 b_seen2 unfolding invar_visited_through_seen_def by blast
      then have "set p2' ∩ set (stack (cb.DFS_skeleton_upd2 dfs_state)) ≠ {}"
        using p2'_walk p2'_dist by blast
      then have "set (tl (stack dfs_state)) ∩ set (p2') ≠ {}"
        by (auto simp add: upd2_unfold)
      then obtain x where x_prop: "x ∈ set (tl (stack dfs_state)) ∩ set (p2')"
        by auto
      then obtain stck1 stck2 where stack_split:"tl (stack dfs_state) = stck1@[x]@stck2"
        by(auto simp add: in_set_conv_decomp)
      have vwalk_stack: "Vwalk.vwalk [G]⇩g (rev (stack dfs_state))"
        using assms(10) by (simp add: invar_2_def)
      obtain pp1 pp2 where "p2'  = pp1@[x]@pp2"
        using IntD2[OF x_prop, simplified in_set_conv_decomp] by auto
      hence walk_b_x:"vwalk_bet [G]⇩g b (pp1@[x]) x"
        using p2'_walk vwalk_bet_pref by force
      have rev_decomp: "rev (stack dfs_state) = (rev stck2 @ (x # rev stck1)) @ [hd (stack dfs_state)]"
        using stack_split stk by (cases "stack dfs_state") auto
      have "Vwalk.vwalk [G]⇩g ((rev stck2 @ (x # rev stck1)) @ [hd (stack dfs_state)])"
        using vwalk_stack rev_decomp by simp
      then have "Vwalk.vwalk [G]⇩g (rev stck2 @ (x # rev stck1))"
        using append_vwalk_pref by blast
      then have vwalk_seg: "Vwalk.vwalk [G]⇩g (x # rev stck1)"
        using append_vwalk_suff by blast
      have hd_seg: "hd (x # rev stck1) = x" by simp
      have last_seg: "last (x # rev stck1) = u"
        using stack_split Cons last_rev by (cases stck1) auto
      have walk_x_u:"vwalk_bet [G]⇩g x (x#rev stck1) u"
        using vwalk_seg hd_seg last_seg by (auto simp add: vwalk_bet_def)
      have walk_u_b:"vwalk_bet [G]⇩g u [u, b] b"
        using 1(1) edges_are_vwalk_bet one(2,3)
        by(auto elim!: vwalk_bet_props intro: vwalk_ball_edges)
      have "vwalk_bet [G]⇩g u (u#pp1@[x]@ rev stck1) u"
        by(auto intro!: vwalk_bet_transitive_2[OF walk_u_b, simplified]
            vwalk_bet_transitive_2[OF walk_b_x, simplified]
            simp add: walk_x_u)
      moreover have "length (u#pp1@[x]@ rev stck1) ≥ 2" by auto
      ultimately show False
        using assms(2) by(force elim: dir_acycE)
    next
      case 2
      then show ?thesis
        using one assms(3)
        by(auto elim!: invar_dfs_backtrack_5E)
    qed
  qed
  thus ?thesis
    by(force intro!: invar_dfs_backtrack_5I simp add: bt2)
qed

lemma invar_dfs_backtrack_5_holds_3[invar_holds_intros]:
  "invar_dfs_backtrack_5 dfs_state ⟹ invar_dfs_backtrack_5 (cb.DFS_skeleton_ret1 dfs_state)"
  by(auto intro!: invar_dfs_backtrack_5I simp add: ret1_unfold elim!: invar_dfs_backtrack_5E)

lemma invar_dfs_backtrack_5_holds_4[invar_holds_intros]:
  "invar_dfs_backtrack_5 dfs_state ⟹ invar_dfs_backtrack_5 (cb.DFS_skeleton_ret2 dfs_state)"
  by(auto intro!: invar_dfs_backtrack_5I simp add: ret2_unfold elim!: invar_dfs_backtrack_5E)

lemma invar_dfs_backtrack_5_holds:
  assumes "cb.DFS_skeleton_dom dfs_state"
    "dir_acyc (Graph.digraph_abs G)"
    "invar_dfs_backtrack_5 dfs_state" "invar_dfs_backtrack_4 dfs_state"
    "invar_dfs_backtrack_3 dfs_state" "invar_dfs_backtrack_1 dfs_state"
    "cb.invar_1 dfs_state" "invar_2 dfs_state"
    "cb.invar_seen_stack dfs_state" "invar_visited_through_seen dfs_state"
  shows  "invar_dfs_backtrack_5 (cb.DFS_skeleton dfs_state)"
  using assms(3-)
proof(induction rule: cb.DFS_skeleton_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    using assms(2)
    by(cases rule: cb.DFS_skeleton_cases[where dfs_state = dfs_state])
      (auto intro!: IH(2-) invar_holds_intros simp: cb.DFS_skeleton_simps[OF IH(1)])
qed

subsection ‹Correctness›

lemma dfs_backtrack_initial_state:
  "invar_dfs_backtrack_1 initial_state"
  "invar_dfs_backtrack_2 initial_state"
  "invar_dfs_backtrack_3 initial_state"
  "invar_dfs_backtrack_4 initial_state"
  "invar_dfs_backtrack_5 initial_state"
  by(auto intro!: invar_dfs_backtrack_1I invar_dfs_backtrack_3I invar_dfs_backtrack_4I
      invar_dfs_backtrack_5I invar_dfs_backtrack_2I
      simp add: initial_state_def)

lemma dfs_backtrack_final:
  "invar_dfs_backtrack_1 (DFS_collect_backtrack initial_state)"
  "invar_dfs_backtrack_2 (DFS_collect_backtrack initial_state)"
  "invar_dfs_backtrack_3 (DFS_collect_backtrack initial_state)"
  "invar_dfs_backtrack_4 (DFS_collect_backtrack initial_state)"
  "dir_acyc (Graph.digraph_abs G) ⟹
       invar_dfs_backtrack_5 (DFS_collect_backtrack initial_state)"
  by(auto intro!: invar_dfs_backtrack_1_holds invar_dfs_backtrack_3_holds
      invar_dfs_backtrack_4_holds invar_dfs_backtrack_5_holds
      invar_dfs_backtrack_2_holds dfs_backtrack_initial_state
      initial_dom initial_invars initial_state_props)

lemma DFS_collect_backtrack_impl_same_on_initial:
  shows   "DFS_collect_backtrack_impl initial_state = DFS_collect_backtrack initial_state"
  using cb.DFS_skeleton_impl_same[OF initial_dom] .

end

end

end

