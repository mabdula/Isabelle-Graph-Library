theory DFS_Reach_Skel_Refine
  imports DFS_Reach_Skel DFS_Skeletons.DFS_Skeleton_Refine
begin

section \<open>Reachability on the prune-at-push refined skeleton\<close>

text \<open>The reachability search of \<^theory>\<open>Graph_Algorithms_Dev.DFS_Reach_Skel\<close> as an instance of
  \<^locale>\<open>DFS_skeleton_refine\<close> --- the \<^emph>\<open>unseen-neighbours\<close> refinement: the adjacency map moves
  into the state and \<open>on_push u\<close> deletes every edge entering \<open>u\<close>, so the carried neighbourhoods
  hold exactly the unseen out-neighbours and the loop reads \<open>\<N> (adj st) v\<close> where the plain
  search recomputes \<open>(\<N>\<^sub>G v) -\<^sub>G (seen st)\<close> twice per step.

  Reachability is the natural client of \<^emph>\<open>this\<close> sibling (rather than the prune-at-backtrack
  \<open>DFS_Skeleton_Refine_Unfin\<close> that the directed-cycle chain uses): its \<open>found\<close> test looks only
  at the stack head, never at edges into seen vertices, so nothing is lost by pruning them at
  push --- and everything is gained, because the skeleton's lockstep equivalence then applies
  verbatim: forgetting the carried map, the refined run \<^emph>\<open>is\<close> the plain run
  (\<open>reach_refine_agrees\<close>), and the two correctness theorems transport unchanged.

  \<^bold>\<open>Deleting in-edges needs a reverse map.\<close> \<open>Pair_Graph_Specs.delete_edge\<close> is keyed by an
  edge's source, so removing the edges into \<open>u\<close> means enumerating \<open>u\<close>'s predecessors. The
  locale therefore fixes a \<^emph>\<open>static\<close> reverse adjacency map \<open>R\<close> --- the predecessors in the
  original \<open>G\<close>, built once, never updated --- and \<open>del_in_edges u\<close> walks \<open>\<N> R u\<close> deleting
  \<open>(p, u)\<close> for each predecessor \<open>p\<close>. Each vertex is pushed at most once, so over a whole run the
  deletions amount to a single pass over the edges and the search stays linear. (A state-carried
  inverse, as in the directed-cycle chain, would not fit this skeleton's unconditional \<open>on_push\<close>
  obligation --- and is not needed: the pruned edges are never read back.)\<close>

record ('ver, 'vset, 'adjmap) DFS_reach_refine_state =
  "('ver, 'vset) DFS_reach_state" +
  adj :: "'adjmap"

locale DFS_Reach_Refine =
  DFS_Reach where lookup = lookup
  for lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option" +
  fixes R :: "'adjmap"
begin

subsection \<open>Deleting every edge into a vertex\<close>

text \<open>\<open>del_preds P u M\<close> removes \<open>{(p, u) | p. p \<in> t_set P}\<close> from \<open>M\<close>, peeling \<open>P\<close> one
  \<open>sel\<close>-chosen element at a time. It is only ever called with \<open>P\<close> the predecessor set
  \<open>\<N> R u\<close>, which is what \<open>del_in_edges\<close> fixes. It is a \<^theory_text>\<open>partial_function\<close> rather than a
  \<^theory_text>\<open>function\<close>: the recursion is a plain tail recursion over a shrinking vset, and every fact
  below is proved by induction on \<open>card (t_set P)\<close> off the two unfolding rules, so no domain
  predicate is needed.\<close>

partial_function (tailrec) del_preds :: "'vset \<Rightarrow> 'v \<Rightarrow> 'adjmap \<Rightarrow> 'adjmap" where
  "del_preds P u M =
     (if P = \<emptyset>\<^sub>N then M
      else del_preds (vset_delete (sel P) P) u (Graph.delete_edge M (sel P) u))"

lemmas [code] = del_preds.simps

definition "del_in_edges u M = del_preds (Graph.neighbourhood R u) u M"

lemmas [code] = del_in_edges_def

lemma del_preds_empty[simp]: "del_preds \<emptyset>\<^sub>N u M = M"
  using del_preds.simps[of "\<emptyset>\<^sub>N" u M] by simp

lemma del_preds_unfold:
  assumes "P \<noteq> \<emptyset>\<^sub>N"
  shows "del_preds P u M = del_preds (vset_delete (sel P) P) u (Graph.delete_edge M (sel P) u)"
  using del_preds.simps[of P u M] assms by simp

lemma vset_empty_of_t_set:
  assumes "vset_inv P" and "t_set P = {}"
  shows "P = \<emptyset>\<^sub>N"
  using assms Graph.vset.emptyD(2) by blast

lemma del_preds_graph_inv_card:
  assumes "vset_inv P"
      and "finite (t_set P)"
      and "card (t_set P) \<le> n"
      and "Graph.graph_inv M"
  shows "Graph.graph_inv (del_preds P u M)"
  using assms
proof (induction n arbitrary: P M)
  case 0
  hence "P = \<emptyset>\<^sub>N" by (simp add: vset_empty_of_t_set)
  thus ?case using 0(4) by simp
next
  case (Suc n)
  show ?case
  proof (cases "P = \<emptyset>\<^sub>N")
    case True
    thus ?thesis using Suc.prems(4) by simp
  next
    case False
    have mem: "sel P \<in> t_set P"
      by (rule Graph.vset.choose'[OF False Suc.prems(1)])
    have inv': "vset_inv (vset_delete (sel P) P)"
      using Suc.prems(1) by (simp add: Graph.vset.set.invar_delete)
    have set': "t_set (vset_delete (sel P) P) = t_set P - {sel P}"
      using Suc.prems(1) by (simp add: Graph.vset.set.set_delete)
    have "card (t_set P - {sel P}) < card (t_set P)"
      by (rule card_Diff1_less[OF Suc.prems(2) mem])
    hence le': "card (t_set (vset_delete (sel P) P)) \<le> n"
      using Suc.prems(3) set' by simp
    have gi': "Graph.graph_inv (Graph.delete_edge M (sel P) u)"
      using Suc.prems(4) by (rule Graph.adjmap_inv_delete)
    have fin': "finite (t_set (vset_delete (sel P) P))"
      using Suc.prems(2) set' by simp
    show ?thesis
      using Suc.IH[OF inv' fin' le' gi']
      by (simp add: del_preds_unfold[OF False])
  qed
qed

lemma del_preds_abs_card:
  assumes "vset_inv P"
      and "finite (t_set P)"
      and "card (t_set P) \<le> n"
      and "Graph.graph_inv M"
  shows "Graph.digraph_abs (del_preds P u M) = Graph.digraph_abs M - (t_set P \<times> {u})"
  using assms
proof (induction n arbitrary: P M)
  case 0
  hence "P = \<emptyset>\<^sub>N" by (simp add: vset_empty_of_t_set)
  thus ?case using Graph.vset.emptyD(1)[of P] by simp
next
  case (Suc n)
  show ?case
  proof (cases "P = \<emptyset>\<^sub>N")
    case True
    thus ?thesis using Graph.vset.emptyD(1)[of P] by simp
  next
    case False
    have mem: "sel P \<in> t_set P"
      by (rule Graph.vset.choose'[OF False Suc.prems(1)])
    have inv': "vset_inv (vset_delete (sel P) P)"
      using Suc.prems(1) by (simp add: Graph.vset.set.invar_delete)
    have set': "t_set (vset_delete (sel P) P) = t_set P - {sel P}"
      using Suc.prems(1) by (simp add: Graph.vset.set.set_delete)
    have "card (t_set P - {sel P}) < card (t_set P)"
      by (rule card_Diff1_less[OF Suc.prems(2) mem])
    hence le': "card (t_set (vset_delete (sel P) P)) \<le> n"
      using Suc.prems(3) set' by simp
    have gi': "Graph.graph_inv (Graph.delete_edge M (sel P) u)"
      using Suc.prems(4) by (rule Graph.adjmap_inv_delete)
    have fin': "finite (t_set (vset_delete (sel P) P))"
      using Suc.prems(2) set' by simp
    have "Graph.digraph_abs (del_preds P u M)
            = Graph.digraph_abs (Graph.delete_edge M (sel P) u)
                - (t_set (vset_delete (sel P) P) \<times> {u})"
      using Suc.IH[OF inv' fin' le' gi'] by (simp add: del_preds_unfold[OF False])
    also have "\<dots> = (Graph.digraph_abs M - {(sel P, u)}) - ((t_set P - {sel P}) \<times> {u})"
      using set' by (simp add: Graph.digraph_abs_delete[OF Suc.prems(4)])
    also have "\<dots> = Graph.digraph_abs M - (t_set P \<times> {u})"
      using mem by blast
    finally show ?thesis .
  qed
qed

lemma del_preds_graph_inv:
  assumes "vset_inv P" and "finite (t_set P)" and "Graph.graph_inv M"
  shows "Graph.graph_inv (del_preds P u M)"
  by (rule del_preds_graph_inv_card[OF assms(1,2) order.refl assms(3)])

lemma del_preds_abs:
  assumes "vset_inv P" and "finite (t_set P)" and "Graph.graph_inv M"
  shows "Graph.digraph_abs (del_preds P u M) = Graph.digraph_abs M - (t_set P \<times> {u})"
  by (rule del_preds_abs_card[OF assms(1,2) order.refl assms(3)])

subsection \<open>The refined search\<close>

text \<open>The callbacks of \<^theory>\<open>Graph_Algorithms_Dev.DFS_Reach_Skel\<close> at the extended state, plus
  the one job this refinement adds: \<open>rreach_on_push\<close> prunes the carried graph.\<close>

definition "rreach_found (st::('v,'vset,'adjmap) DFS_reach_refine_state) =
   (case stack st of [] \<Rightarrow> False | v # _ \<Rightarrow> v = t)"

definition "rreach_on_found (st::('v,'vset,'adjmap) DFS_reach_refine_state) =
  (st \<lparr>return := Reachable\<rparr>)"

definition "rreach_on_empty (st::('v,'vset,'adjmap) DFS_reach_refine_state) =
  (st \<lparr>return := NotReachable\<rparr>)"

definition "rreach_on_backtrack v (st::('v,'vset,'adjmap) DFS_reach_refine_state) = st"

definition "rreach_on_push u (st::('v,'vset,'adjmap) DFS_reach_refine_state) =
  (st \<lparr>adj := del_in_edges u (adj st)\<rparr>)"

text \<open>The initial state is the plain one plus the pruned graph the root demands: the root is
  seen from the start, so its in-edges go before the loop begins.\<close>
definition "rreach_initial_state =
  \<lparr>stack = [s], seen = insert s \<emptyset>\<^sub>N, return = NotReachable, adj = del_in_edges s G\<rparr>"

lemmas [code] = rreach_initial_state_def

sublocale rr: DFS_skeleton_refine
  where lookup = lookup and G = G and s = s
    and found = rreach_found and on_found = rreach_on_found
    and on_empty = rreach_on_empty and on_backtrack = rreach_on_backtrack
    and on_push = rreach_on_push and adjmap = adj
  by unfold_locales

abbreviation "DFS_reach_refine_impl \<equiv> rr.DFS_skeleton_refine_impl"

lemma rreach_spine[simp]:
  "stack (rreach_on_found st) = stack st"
  "seen (rreach_on_found st) = seen st"
  "stack (rreach_on_empty st) = stack st"
  "seen (rreach_on_empty st) = seen st"
  "stack (rreach_on_backtrack v st) = stack st"
  "seen (rreach_on_backtrack v st) = seen st"
  "stack (rreach_on_push u st) = stack st"
  "seen (rreach_on_push u st) = seen st"
  by (auto simp: rreach_on_found_def rreach_on_empty_def rreach_on_backtrack_def
                 rreach_on_push_def)

lemma rreach_adj[simp]:
  "adj (rreach_on_found st) = adj st"
  "adj (rreach_on_empty st) = adj st"
  "adj (rreach_on_backtrack v st) = adj st"
  "adj (rreach_on_push u st) = del_in_edges u (adj st)"
  by (auto simp: rreach_on_found_def rreach_on_empty_def rreach_on_backtrack_def
                 rreach_on_push_def)

end

text \<open>The reasoning layer, on top of \<^locale>\<open>DFS_Reach_thms\<close>. Three further assumptions, and no
  others:
  \<^item> \<open>sel_cong\<close> --- \<open>sel\<close> is determined by the element set. It comes straight from
    \<^locale>\<open>DFS_skeleton_refine_thms\<close> and is \<^emph>\<open>not\<close> dischargeable here: the refined loop hands
    \<open>sel\<close> a vset built by repeated deletion where the plain loop hands it one built by \<open>-\<^sub>G\<close>,
    and \<^locale>\<open>Set_Choose\<close> does not make \<open>sel\<close> a function of the underlying set (at the
    red-black-tree instantiation it is the root label). It has to be passed on to whoever
    instantiates the vset ADT, who must supply a set-determined choice --- for a search tree, the
    leftmost element rather than the root.
  \<^item> \<open>R\<close> is a well-formed adjacency map holding the \<^emph>\<open>predecessors\<close> in \<open>G\<close> (\<open>R_preds\<close>). It is
    read but never written.\<close>

locale DFS_Reach_Refine_thms =
  DFS_Reach_Refine + DFS_Reach_thms +
  assumes sel_cong: "vset_inv X \<Longrightarrow> vset_inv Y \<Longrightarrow> t_set X = t_set Y \<Longrightarrow> sel X = sel Y"
      and R_graph_inv: "Graph.graph_inv R"
      and R_preds: "t_set (Graph.neighbourhood R u) = {p. (p, u) \<in> Graph.digraph_abs G}"
begin

subsection \<open>What \<open>del_in_edges\<close> does\<close>

lemma finite_digraph_abs: "finite (Graph.digraph_abs G)"
  by (rule Graph.finite_graph[OF reach.graph_inv(1) reach.graph_inv(2) reach.graph_inv(3)])

lemma preds_finite: "finite {p. (p, u) \<in> Graph.digraph_abs G}"
proof -
  have "{p. (p, u) \<in> Graph.digraph_abs G} \<subseteq> fst ` Graph.digraph_abs G"
    by force
  thus ?thesis using finite_digraph_abs by (simp add: finite_subset)
qed

lemma preds_inv: "vset_inv (Graph.neighbourhood R u)"
  by (rule Graph.neighbourhood_invars'[OF R_graph_inv])

lemma preds_fin: "finite (t_set (Graph.neighbourhood R u))"
  by (simp add: R_preds preds_finite)

lemma del_in_edges_graph_inv:
  assumes "Graph.graph_inv M"
  shows "Graph.graph_inv (del_in_edges u M)"
  unfolding del_in_edges_def
  by (rule del_preds_graph_inv[OF preds_inv preds_fin assms])

text \<open>On a map below \<open>G\<close>, deleting the edges from \<open>u\<close>'s \<^emph>\<open>\<open>G\<close>-predecessors\<close> deletes all
  edges into \<open>u\<close>: there are no others to delete.\<close>
lemma del_in_edges_abs:
  assumes "Graph.graph_inv M"
      and "Graph.digraph_abs M \<subseteq> Graph.digraph_abs G"
  shows "Graph.digraph_abs (del_in_edges u M) = Graph.digraph_abs M - (UNIV \<times> {u})"
proof -
  have "Graph.digraph_abs (del_in_edges u M)
          = Graph.digraph_abs M - (t_set (Graph.neighbourhood R u) \<times> {u})"
    unfolding del_in_edges_def
    by (rule del_preds_abs[OF preds_inv preds_fin assms(1)])
  also have "\<dots> = Graph.digraph_abs M - (UNIV \<times> {u})"
    using assms(2) by (auto simp: R_preds)
  finally show ?thesis .
qed

subsection \<open>The instance of the refined skeleton\<close>

sublocale rr: DFS_skeleton_refine_thms
  where lookup = lookup and G = G and s = s
    and found = rreach_found and on_found = rreach_on_found
    and on_empty = rreach_on_empty and on_backtrack = rreach_on_backtrack
    and on_push = rreach_on_push and adjmap = adj
proof unfold_locales
  show "rr.DFS_skeleton_axioms"
    using DFS_axioms
    by (simp add: rr.DFS_skeleton_axioms_def DFS_axioms_def)
  show "stack (rreach_on_found st) = stack st" for st by simp
  show "seen (rreach_on_found st) = seen st" for st by simp
  show "stack (rreach_on_empty st) = stack st" for st by simp
  show "seen (rreach_on_empty st) = seen st" for st by simp
  show "stack (rreach_on_backtrack v st) = stack st" for v st by simp
  show "seen (rreach_on_backtrack v st) = seen st" for v st by simp
  show "stack (rreach_on_push u st) = stack st" for u st by simp
  show "seen (rreach_on_push u st) = seen st" for u st by simp
  show "sel X = sel Y" if "vset_inv X" and "vset_inv Y" and "t_set X = t_set Y" for X Y
    by (rule sel_cong[OF that])
  show "adj (st \<lparr>stack := xs\<rparr>) = adj st" for st xs by simp
  show "adj (st \<lparr>seen := S\<rparr>) = adj st" for st S by simp
  show "adj (rreach_on_found st) = adj st" for st by simp
  show "adj (rreach_on_empty st) = adj st" for st by simp
  show "adj (rreach_on_backtrack v st) = adj st" for v st by simp
  show "Graph.graph_inv (adj (rreach_on_push u st))"
    if "Graph.graph_inv (adj st)" for u st
    using that by (simp add: del_in_edges_graph_inv)
  show "Graph.digraph_abs (adj (rreach_on_push u st))
          = Graph.digraph_abs (adj st) - (UNIV \<times> {u})"
    if "Graph.graph_inv (adj st)"
   and "Graph.digraph_abs (adj st) \<subseteq> Graph.digraph_abs G" for u st
    using that by (simp add: del_in_edges_abs)
qed

context
includes set_ops.automation2 and Graph.adjmap.automation and Graph.vset.set.automation
begin

subsection \<open>The refinement invariant at the initial state\<close>

lemma initial_refine_invars[simp, intro]:
  "rr.invar_1 rreach_initial_state"
  "rr.invar_seen_stack rreach_initial_state"
  using DFS_axioms
  by (auto simp: rr.invar_1_def rr.invar_seen_stack_def rreach_initial_state_def
                 DFS_axioms_def)

lemma initial_refine_invar_adj: "rr.invar_adj rreach_initial_state"
proof -
  have gi: "Graph.graph_inv (del_in_edges s G)"
    by (rule del_in_edges_graph_inv[OF reach.graph_inv(1)])
  have "Graph.digraph_abs (del_in_edges s G) = Graph.digraph_abs G - (UNIV \<times> {s})"
    by (rule del_in_edges_abs[OF reach.graph_inv(1) subset_refl])
  also have "\<dots> = Graph.digraph_abs G - (UNIV \<times> t_set (insert s \<emptyset>\<^sub>N))"
    by auto
  finally show ?thesis
    using gi by (simp add: rr.invar_adj_def rreach_initial_state_def)
qed

lemma rreach_initial_dom: "rr.DFS_skeleton_refine_dom rreach_initial_state"
  using rr.DFS_skeleton_terminates[OF initial_refine_invars]
  by (simp add: rr.DFS_skeleton_refine_dom_iff[OF initial_refine_invar_adj
                                               initial_refine_invars(1)])

abbreviation "reach_refine_result \<equiv> rr.DFS_skeleton_refine rreach_initial_state"

text \<open>The skeleton's own equivalence: the loop that reads the state's pruned map is the loop
  that recomputes the difference.\<close>

theorem reach_refine_eq_more:
  "reach_refine_result = rr.DFS_skeleton rreach_initial_state"
  by (rule rr.DFS_skeleton_refine_eq_DFS_skeleton
             [OF rreach_initial_dom initial_refine_invar_adj initial_refine_invars(1)])

corollary reach_refine_impl_eq_more:
  "rr.DFS_skeleton_refine_impl rreach_initial_state
     = rr.DFS_skeleton rreach_initial_state"
  by (rule rr.DFS_skeleton_refine_impl_eq_DFS_skeleton
             [OF rreach_initial_dom initial_refine_invar_adj initial_refine_invars(1)])

section \<open>The refined search against the plain one\<close>

text \<open>The refined state record \<^emph>\<open>extends\<close> the plain one, so the projection that forgets \<open>adj\<close>
  is the record package's own \<open>truncate\<close>, and the two runs are compared by an equation rather
  than by a bespoke agreement relation. Because \<open>rreach_found\<close> reads only the stack, and every
  callback moves the shared fields exactly as the plain one's does, the two searches take the
  same branch at every step and the projection commutes with the whole run.\<close>

lemma truncate_sel[simp]:
  "stack (DFS_reach_state.truncate st) = stack st"
  "seen (DFS_reach_state.truncate st) = seen st"
  "return (DFS_reach_state.truncate st) = return st"
  by (simp_all add: DFS_reach_state.truncate_def)

lemma truncate_found[simp]:
  "reach_found (DFS_reach_state.truncate st) = rreach_found st"
  by (cases "stack st") (simp_all add: reach_found_def rreach_found_def)

lemma truncate_invars[simp]:
  "reach.invar_1 (DFS_reach_state.truncate st) = rr.invar_1 st"
  "reach.invar_seen_stack (DFS_reach_state.truncate st) = rr.invar_seen_stack st"
  by (simp_all add: rr.invar_1_def rr.invar_seen_stack_def
                    reach.invar_1_def reach.invar_seen_stack_def)

lemma truncate_conds[simp]:
  "reach.DFS_skeleton_call_1_conds (DFS_reach_state.truncate st)
     = rr.DFS_skeleton_call_1_conds st"
  "reach.DFS_skeleton_call_2_conds (DFS_reach_state.truncate st)
     = rr.DFS_skeleton_call_2_conds st"
  "reach.DFS_skeleton_ret_1_conds (DFS_reach_state.truncate st)
     = rr.DFS_skeleton_ret_1_conds st"
  "reach.DFS_skeleton_ret_2_conds (DFS_reach_state.truncate st)
     = rr.DFS_skeleton_ret_2_conds st"
  by (simp_all add: reach.DFS_skeleton_call_1_conds_def rr.DFS_skeleton_call_1_conds_def
                    reach.DFS_skeleton_call_2_conds_def rr.DFS_skeleton_call_2_conds_def
                    reach.DFS_skeleton_ret_1_conds_def rr.DFS_skeleton_ret_1_conds_def
                    reach.DFS_skeleton_ret_2_conds_def rr.DFS_skeleton_ret_2_conds_def
              split: list.splits)

lemma truncate_steps[simp]:
  "reach.DFS_skeleton_upd1 (DFS_reach_state.truncate st)
     = DFS_reach_state.truncate (rr.DFS_skeleton_upd1 st)"
  "reach.DFS_skeleton_upd2 (DFS_reach_state.truncate st)
     = DFS_reach_state.truncate (rr.DFS_skeleton_upd2 st)"
  "reach.DFS_skeleton_ret1 (DFS_reach_state.truncate st)
     = DFS_reach_state.truncate (rr.DFS_skeleton_ret1 st)"
  "reach.DFS_skeleton_ret2 (DFS_reach_state.truncate st)
     = DFS_reach_state.truncate (rr.DFS_skeleton_ret2 st)"
  by (simp_all add: reach.DFS_skeleton_upd1_def rr.DFS_skeleton_upd1_def
                    reach.DFS_skeleton_upd2_def rr.DFS_skeleton_upd2_def
                    reach.DFS_skeleton_ret1_def rr.DFS_skeleton_ret1_def
                    reach.DFS_skeleton_ret2_def rr.DFS_skeleton_ret2_def
                    no_push_def rreach_on_push_def
                    reach_on_backtrack_def rreach_on_backtrack_def
                    reach_on_empty_def rreach_on_empty_def
                    reach_on_found_def rreach_on_found_def
                    DFS_reach_state.truncate_def Let_def)

subsection \<open>The projection commutes with the whole run\<close>

theorem refine_run_agree:
  assumes dom: "rr.DFS_skeleton_dom st"
      and "rr.invar_1 st"
      and "rr.invar_seen_stack st"
  shows "DFS_reach_state.truncate (rr.DFS_skeleton st)
           = reach.DFS_skeleton (DFS_reach_state.truncate st)"
  using assms(2-)
proof (induction rule: rr.DFS_skeleton_induct[OF dom])
  case IH: (1 st)
  have t1: "reach.invar_1 (DFS_reach_state.truncate st)"
    using IH(4) by simp
  have t2: "reach.invar_seen_stack (DFS_reach_state.truncate st)"
    using IH(5) by simp
  note simps = rr.DFS_skeleton_simps[OF IH(1)]
  note tsimps = reach.DFS_skeleton_simps[OF reach.DFS_skeleton_terminates[OF t1 t2]]
  show ?case
  proof (rule rr.DFS_skeleton_cases[where dfs_state = st])
    assume c: "rr.DFS_skeleton_call_1_conds st"
    have tc: "reach.DFS_skeleton_call_1_conds (DFS_reach_state.truncate st)"
      using c by simp
    have "DFS_reach_state.truncate (rr.DFS_skeleton (rr.DFS_skeleton_upd1 st))
            = reach.DFS_skeleton (DFS_reach_state.truncate (rr.DFS_skeleton_upd1 st))"
      by (rule IH(2)[OF c rr.invar_1_holds_1[OF c IH(4)]
                          rr.invar_seen_stack_holds_1[OF c IH(4) IH(5)]])
    thus ?thesis by (simp add: simps(1)[OF c] tsimps(1)[OF tc])
  next
    assume c: "rr.DFS_skeleton_call_2_conds st"
    have tc: "reach.DFS_skeleton_call_2_conds (DFS_reach_state.truncate st)"
      using c by simp
    have "DFS_reach_state.truncate (rr.DFS_skeleton (rr.DFS_skeleton_upd2 st))
            = reach.DFS_skeleton (DFS_reach_state.truncate (rr.DFS_skeleton_upd2 st))"
      by (rule IH(3)[OF c rr.invar_1_holds_2[OF c IH(4)]
                          rr.invar_seen_stack_holds_2[OF c IH(4) IH(5)]])
    thus ?thesis by (simp add: simps(2)[OF c] tsimps(2)[OF tc])
  next
    assume c: "rr.DFS_skeleton_ret_1_conds st"
    have tc: "reach.DFS_skeleton_ret_1_conds (DFS_reach_state.truncate st)"
      using c by simp
    show ?thesis by (simp add: simps(3)[OF c] tsimps(3)[OF tc])
  next
    assume c: "rr.DFS_skeleton_ret_2_conds st"
    have tc: "reach.DFS_skeleton_ret_2_conds (DFS_reach_state.truncate st)"
      using c by simp
    show ?thesis by (simp add: simps(4)[OF c] tsimps(4)[OF tc])
  qed
qed

lemma truncate_initial:
  "DFS_reach_state.truncate rreach_initial_state = initial_state"
  by (simp add: DFS_reach_state.truncate_def rreach_initial_state_def initial_state_def)

text \<open>The capstone: forgetting the carried graph, the refined run \<^emph>\<open>is\<close> the plain reachability
  run --- it does the same thing. Everything proved of \<open>DFS_reach\<close> therefore holds of the
  refined run verbatim.\<close>

theorem reach_refine_agrees:
  "DFS_reach_state.truncate reach_refine_result = DFS_reach initial_state"
proof -
  have "DFS_reach_state.truncate (rr.DFS_skeleton rreach_initial_state)
          = reach.DFS_skeleton (DFS_reach_state.truncate rreach_initial_state)"
    by (rule refine_run_agree[OF rr.DFS_skeleton_terminates[OF initial_refine_invars]
                                 initial_refine_invars])
  thus ?thesis by (simp add: reach_refine_eq_more truncate_initial)
qed

corollary reach_refine_components:
  shows "stack reach_refine_result = stack (DFS_reach initial_state)"
    and "seen reach_refine_result = seen (DFS_reach initial_state)"
    and "return reach_refine_result = return (DFS_reach initial_state)"
  using arg_cong[where f = stack, OF reach_refine_agrees]
  using arg_cong[where f = seen, OF reach_refine_agrees]
  using arg_cong[where f = return, OF reach_refine_agrees]
  by simp_all

subsection \<open>Correctness, transported\<close>

theorem DFS_reach_refine_correct_1:
  assumes "return reach_refine_result = NotReachable"
  shows "\<nexists>p. vwalk_bet (Graph.digraph_abs G) s p t"
  using DFS_correct_1_strong assms reach_refine_components(3) by simp

theorem DFS_reach_refine_correct_2:
  assumes "return reach_refine_result = Reachable"
  shows "vwalk_bet (Graph.digraph_abs G) s (rev (stack reach_refine_result)) t"
    and "distinct (rev (stack reach_refine_result))"
  using DFS_correct_2 assms reach_refine_components(1,3) by simp_all

corollary reach_refine_impl_agrees:
  "DFS_reach_state.truncate (rr.DFS_skeleton_refine_impl rreach_initial_state)
     = DFS_reach initial_state"
  by (simp add: rr.DFS_skeleton_refine_impl_same[OF rreach_initial_dom] reach_refine_agrees)

end

end

end
