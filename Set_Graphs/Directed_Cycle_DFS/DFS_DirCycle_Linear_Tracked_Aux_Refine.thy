theory DFS_DirCycle_Linear_Tracked_Aux_Refine
  imports DFS_Skel_More_Refine DFS_DirCycle_Linear_Tracked_Aux
begin

text \<open>Level 2 of the refinement chain at the \<^emph>\<open>inner\<close> (pre-seeded) directed-cycle DFS: the
  instance of \<^locale>\<open>DFS_skel_more_refine\<close> that the tracked search of
  \<^theory>\<open>Directed_Cycle_DFS.DFS_DirCycle_Linear_Tracked_Aux\<close> becomes once the adjacency map moves into the
  state.

  The state record gains one field, \<open>adj\<close>, and \<open>on_push\<close> gains one job: besides growing
  \<open>gray\<close> it deletes every edge \<^emph>\<open>entering\<close> the vertex just pushed. The loop then reads a plain
  \<open>\<N> (adj st) v\<close> where level 1 reads \<open>(\<N>\<^sub>G v) -\<^sub>G (seen st)\<close> --- the last set operation in the
  inner loop, and the one the skeleton evaluates twice per step, is gone.

  \<^bold>\<open>The back-edge test still reads \<open>G\<close>.\<close> \<open>rcyc_found\<close> intersects \<open>\<N>\<^sub>G v\<close> --- the
  \<^emph>\<open>original\<close> neighbourhood --- with \<open>gray\<close>, exactly as level 1 does. It must: a back edge
  points at a vertex that is on the stack and therefore \<^emph>\<open>seen\<close>, so back edges are precisely
  the edges the state's pruned map no longer holds. Only the \<^emph>\<open>descend\<close> step consumes \<open>adj\<close>.

  \<^bold>\<open>Deleting in-edges needs a reverse map.\<close> \<open>Pair_Graph_Specs.delete_edge\<close> is keyed by an
  edge's source, so removing the edges into \<open>u\<close> means enumerating \<open>u\<close>'s predecessors. The
  locale therefore fixes a \<^emph>\<open>static\<close> reverse adjacency map \<open>R\<close> --- the predecessors in the
  original \<open>G\<close>, built once, never updated --- and \<open>del_in_edges u\<close> walks \<open>\<N> R u\<close> deleting
  \<open>(p, u)\<close> for each predecessor \<open>p\<close>. Each vertex is pushed at most once, so over a whole run the
  deletions amount to a single pass over the edges and the search stays linear. (Scanning every
  vertex's neighbour set per push would cost \<open>O(V)\<close> a step --- exactly the price this level exists
  to remove.)

  \<^bold>\<open>The incoming map \<open>A\<close>.\<close> The run is pre-seeded with a finished region \<open>f\<close>, so it is also
  pre-seeded with the adjacency map appropriate to it: \<open>A\<close> is assumed to be \<open>G\<close> with the
  in-edges of \<open>t_set f\<close> already gone. The initial state deletes the in-edges of the root and
  starts from there. An outer whole-graph sweep threads \<open>A\<close> from one call to the next, so the
  pruning is never redone.\<close>

record ('ver, 'vset, 'adjmap) DFS_dircycle_linear_tracked_aux_refine_state =
  "('ver, 'vset) DFS_dircycle_linear_tracked_aux_state" +
  adj :: "'adjmap"

locale DFS_dircycle_linear_tracked_aux_refine =
  DFS_dircycle_linear_tracked_aux where lookup = lookup
  for lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option" +
  fixes R :: "'adjmap" and A :: "'adjmap"
begin

section \<open>Deleting every edge into a vertex\<close>

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

text \<open>The two unfolding rules. They are stated at a fixed instance rather than schematically:
  \<open>del_preds.simps\<close> itself is a looping rewrite rule.\<close>

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

section \<open>The refined search\<close>

text \<open>The callbacks of \<^theory>\<open>Directed_Cycle_DFS.DFS_DirCycle_Linear_Tracked_Aux\<close> verbatim, except that
  \<open>rcyc_on_push\<close> also prunes the carried graph. Note again that \<open>rcyc_found\<close> reads \<open>\<N>\<^sub>G v\<close>,
  the \<^emph>\<open>original\<close> neighbourhood.\<close>

definition "rcyc_found (dfs_state::('v,'vset,'adjmap) DFS_dircycle_linear_tracked_aux_refine_state) =
   (case stack dfs_state of [] \<Rightarrow> False
    | (v # stack_tl) \<Rightarrow> (((\<N>\<^sub>G v) \<inter>\<^sub>G (gray dfs_state)) \<noteq> \<emptyset>\<^sub>N))"

definition "rcyc_on_found (dfs_state::('v,'vset,'adjmap) DFS_dircycle_linear_tracked_aux_refine_state) =
  (dfs_state \<lparr>cycle := True\<rparr>)"

definition "rcyc_on_empty (dfs_state::('v,'vset,'adjmap) DFS_dircycle_linear_tracked_aux_refine_state) = dfs_state"

definition "rcyc_on_push u (dfs_state::('v,'vset,'adjmap) DFS_dircycle_linear_tracked_aux_refine_state) =
  (dfs_state \<lparr>gray := insert u (gray dfs_state), adj := del_in_edges u (adj dfs_state)\<rparr>)"

definition "rcyc_on_backtrack v (dfs_state::('v,'vset,'adjmap) DFS_dircycle_linear_tracked_aux_refine_state) =
  (dfs_state \<lparr>finished := insert v (finished dfs_state),
              gray := vset_delete v (gray dfs_state),
              unfinished := vset_delete v (unfinished dfs_state)\<rparr>)"

text \<open>The initial state is level 1's, plus the pruned graph the root demands: the caller's \<open>A\<close>
  already lacks the in-edges of \<open>t_set f\<close>, and the root is pushed here rather than by
  \<open>on_push\<close>, so its in-edges must go here too.\<close>
definition "dircycle_refine_initial_state =
  \<lparr>stack = [s], seen = insert s f, finished = f, gray = insert s \<emptyset>\<^sub>N,
   unfinished = uf, cycle = False, adj = del_in_edges s A\<rparr>"

lemmas [code] = dircycle_refine_initial_state_def

sublocale rdc: DFS_skel_more_refine
  where lookup = lookup and G = G and s = s
    and found = rcyc_found and on_found = rcyc_on_found
    and on_empty = rcyc_on_empty and on_backtrack = rcyc_on_backtrack
    and on_push = rcyc_on_push and adjmap = adj
  by unfold_locales

abbreviation "find_dircycle_refine \<equiv> rdc.DFS_skel_more_refine_impl"

lemma rcyc_spine[simp]:
  "stack (rcyc_on_found st) = stack st"
  "seen (rcyc_on_found st) = seen st"
  "stack (rcyc_on_empty st) = stack st"
  "seen (rcyc_on_empty st) = seen st"
  "stack (rcyc_on_backtrack v st) = stack st"
  "seen (rcyc_on_backtrack v st) = seen st"
  "stack (rcyc_on_push u st) = stack st"
  "seen (rcyc_on_push u st) = seen st"
  by (auto simp: rcyc_on_found_def rcyc_on_empty_def rcyc_on_backtrack_def rcyc_on_push_def)

lemma rcyc_adj[simp]:
  "adj (rcyc_on_found st) = adj st"
  "adj (rcyc_on_empty st) = adj st"
  "adj (rcyc_on_backtrack v st) = adj st"
  "adj (rcyc_on_push u st) = del_in_edges u (adj st)"
  by (auto simp: rcyc_on_found_def rcyc_on_empty_def rcyc_on_backtrack_def rcyc_on_push_def)

end

text \<open>The reasoning layer, on top of level 1's \<^locale>\<open>DFS_dircycle_linear_tracked_aux_thms\<close>. Three further
  assumptions, and no others:
  \<^item> \<open>sel_cong\<close> --- \<open>sel\<close> is determined by the element set. It comes straight from
    \<^locale>\<open>DFS_skel_more_refine_thms\<close> and is \<^emph>\<open>not\<close> dischargeable here: the refined loop hands
    \<open>sel\<close> a vset built by repeated deletion where level 1 hands it one built by \<open>-\<^sub>G\<close>, and
    \<^locale>\<open>Set_Choose\<close> does not make \<open>sel\<close> a function of the underlying set (at the
    red-black-tree instantiation it is the root label). It has to be passed on to whoever
    instantiates the vset ADT, who must supply a set-determined choice --- for a search tree, the
    leftmost element rather than the root.
  \<^item> \<open>R\<close> is a well-formed adjacency map holding the \<^emph>\<open>predecessors\<close> in \<open>G\<close> (\<open>R_preds\<close>). It is
    read but never written.
  \<^item> \<open>A\<close> is a well-formed adjacency map, namely \<open>G\<close> with the in-edges of the seed \<open>f\<close> already
    deleted.\<close>

locale DFS_dircycle_linear_tracked_aux_refine_thms =
  DFS_dircycle_linear_tracked_aux_refine + DFS_dircycle_linear_tracked_aux_thms +
  assumes sel_cong: "vset_inv X \<Longrightarrow> vset_inv Y \<Longrightarrow> t_set X = t_set Y \<Longrightarrow> sel X = sel Y"
      and R_graph_inv: "Graph.graph_inv R"
      and R_preds: "t_set (Graph.neighbourhood R u) = {p. (p, u) \<in> Graph.digraph_abs G}"
      and A_graph_inv: "Graph.graph_inv A"
      and A_abs: "Graph.digraph_abs A = Graph.digraph_abs G - (UNIV \<times> t_set f)"
begin

subsection \<open>What \<open>del_in_edges\<close> does\<close>

lemma finite_digraph_abs: "finite (Graph.digraph_abs G)"
  by (rule Graph.finite_graph[OF dc.graph_inv(1) dc.graph_inv(2) dc.graph_inv(3)])

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

sublocale rdc: DFS_skel_more_refine_thms
  where lookup = lookup and G = G and s = s
    and found = rcyc_found and on_found = rcyc_on_found
    and on_empty = rcyc_on_empty and on_backtrack = rcyc_on_backtrack
    and on_push = rcyc_on_push and adjmap = adj
proof unfold_locales
  show "rdc.DFS_skel_more_axioms"
    using dircycle_tracked_axioms
    by (simp add: rdc.DFS_skel_more_axioms_def DFS_dircycle_linear_tracked_aux_axioms_def)
  show "stack (rcyc_on_found st) = stack st" for st by simp
  show "seen (rcyc_on_found st) = seen st" for st by simp
  show "stack (rcyc_on_empty st) = stack st" for st by simp
  show "seen (rcyc_on_empty st) = seen st" for st by simp
  show "stack (rcyc_on_backtrack v st) = stack st" for v st by simp
  show "seen (rcyc_on_backtrack v st) = seen st" for v st by simp
  show "stack (rcyc_on_push u st) = stack st" for u st by simp
  show "seen (rcyc_on_push u st) = seen st" for u st by simp
  show "sel X = sel Y" if "vset_inv X" and "vset_inv Y" and "t_set X = t_set Y" for X Y
    by (rule sel_cong[OF that])
  show "adj (st \<lparr>stack := xs\<rparr>) = adj st" for st xs by simp
  show "adj (st \<lparr>seen := S\<rparr>) = adj st" for st S by simp
  show "adj (rcyc_on_found st) = adj st" for st by simp
  show "adj (rcyc_on_empty st) = adj st" for st by simp
  show "adj (rcyc_on_backtrack v st) = adj st" for v st by simp
  show "Graph.graph_inv (adj (rcyc_on_push u st))"
    if "Graph.graph_inv (adj st)" for u st
    using that by (simp add: del_in_edges_graph_inv)
  show "Graph.digraph_abs (adj (rcyc_on_push u st))
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
  "rdc.invar_1 dircycle_refine_initial_state"
  "rdc.invar_seen_stack dircycle_refine_initial_state"
  using dircycle_tracked_axioms
  by (auto simp: rdc.invar_1_def rdc.invar_seen_stack_def dircycle_refine_initial_state_def
                 DFS_dircycle_linear_tracked_aux_axioms_def)

lemma initial_refine_invar_adj: "rdc.invar_adj dircycle_refine_initial_state"
proof -
  have gi: "Graph.graph_inv (del_in_edges s A)"
    by (rule del_in_edges_graph_inv[OF A_graph_inv])
  have sub: "Graph.digraph_abs A \<subseteq> Graph.digraph_abs G"
    by (simp add: A_abs)
  have "Graph.digraph_abs (del_in_edges s A) = Graph.digraph_abs A - (UNIV \<times> {s})"
    by (rule del_in_edges_abs[OF A_graph_inv sub])
  also have "\<dots> = Graph.digraph_abs G - (UNIV \<times> t_set (insert s f))"
    using dircycle_tracked_axioms
    by (auto simp: A_abs DFS_dircycle_linear_tracked_aux_axioms_def)
  finally show ?thesis
    using gi by (simp add: rdc.invar_adj_def dircycle_refine_initial_state_def)
qed

lemma dircycle_refine_initial_dom: "rdc.DFS_skel_more_refine_dom dircycle_refine_initial_state"
  using rdc.DFS_skel_more_terminates[OF initial_refine_invars]
  by (simp add: rdc.DFS_skel_more_refine_dom_iff[OF initial_refine_invar_adj
                                               initial_refine_invars(1)])

abbreviation "dircycle_refine_result \<equiv> rdc.DFS_skel_more_refine dircycle_refine_initial_state"

text \<open>Level 2's own equivalence, from \<^theory>\<open>Directed_Cycle_DFS.DFS_Skel_More_Refine\<close>: the loop
  that reads the state's pruned map is the loop that recomputes the difference.\<close>

theorem dircycle_refine_eq_more:
  "dircycle_refine_result = rdc.DFS_skel_more dircycle_refine_initial_state"
  by (rule rdc.DFS_skel_more_refine_eq_DFS_skel_more
             [OF dircycle_refine_initial_dom initial_refine_invar_adj
                 initial_refine_invars(1)])

corollary dircycle_refine_impl_eq_more:
  "rdc.DFS_skel_more_refine_impl dircycle_refine_initial_state
     = rdc.DFS_skel_more dircycle_refine_initial_state"
  by (rule rdc.DFS_skel_more_refine_impl_eq_DFS_skel_more
             [OF dircycle_refine_initial_dom initial_refine_invar_adj
                 initial_refine_invars(1)])

section \<open>Level 2 against level 1\<close>

text \<open>The level-2 state record \<^emph>\<open>extends\<close> level 1's, so the projection that forgets \<open>adj\<close> is
  the record package's own \<open>truncate\<close>, and the two runs can be compared by an equation rather
  than by a bespoke agreement relation. Because \<open>rcyc_found\<close> reads only \<open>stack\<close> and \<open>gray\<close>,
  and every callback moves the shared fields exactly as level 1's does, the two searches take the
  same branch at every step and the projection commutes with the whole run.\<close>

lemma truncate_sel[simp]:
  "stack (DFS_dircycle_linear_tracked_aux_state.truncate st) = stack st"
  "seen (DFS_dircycle_linear_tracked_aux_state.truncate st) = seen st"
  "finished (DFS_dircycle_linear_tracked_aux_state.truncate st) = finished st"
  "gray (DFS_dircycle_linear_tracked_aux_state.truncate st) = gray st"
  "unfinished (DFS_dircycle_linear_tracked_aux_state.truncate st) = unfinished st"
  "cycle (DFS_dircycle_linear_tracked_aux_state.truncate st) = cycle st"
  by (simp_all add: DFS_dircycle_linear_tracked_aux_state.truncate_def)

lemma truncate_found[simp]:
  "cyc_found (DFS_dircycle_linear_tracked_aux_state.truncate st) = rcyc_found st"
  by (cases "stack st") (simp_all add: cyc_found_def rcyc_found_def)

lemma truncate_invars[simp]:
  "dc.invar_1 (DFS_dircycle_linear_tracked_aux_state.truncate st) = rdc.invar_1 st"
  "dc.invar_seen_stack (DFS_dircycle_linear_tracked_aux_state.truncate st) = rdc.invar_seen_stack st"
  by (simp_all add: rdc.invar_1_def rdc.invar_seen_stack_def)

lemma truncate_conds[simp]:
  "dc.DFS_skel_more_call_1_conds (DFS_dircycle_linear_tracked_aux_state.truncate st)
     = rdc.DFS_skel_more_call_1_conds st"
  "dc.DFS_skel_more_call_2_conds (DFS_dircycle_linear_tracked_aux_state.truncate st)
     = rdc.DFS_skel_more_call_2_conds st"
  "dc.DFS_skel_more_ret_1_conds (DFS_dircycle_linear_tracked_aux_state.truncate st)
     = rdc.DFS_skel_more_ret_1_conds st"
  "dc.DFS_skel_more_ret_2_conds (DFS_dircycle_linear_tracked_aux_state.truncate st)
     = rdc.DFS_skel_more_ret_2_conds st"
  by (simp_all add: dc.DFS_skel_more_call_1_conds_def rdc.DFS_skel_more_call_1_conds_def
                    dc.DFS_skel_more_call_2_conds_def rdc.DFS_skel_more_call_2_conds_def
                    rdc.DFS_skel_more_ret_1_conds_def
                    dc.DFS_skel_more_ret_2_conds_def rdc.DFS_skel_more_ret_2_conds_def
              split: list.splits)

lemma truncate_steps[simp]:
  "dc.DFS_skel_more_upd1 (DFS_dircycle_linear_tracked_aux_state.truncate st)
     = DFS_dircycle_linear_tracked_aux_state.truncate (rdc.DFS_skel_more_upd1 st)"
  "dc.DFS_skel_more_upd2 (DFS_dircycle_linear_tracked_aux_state.truncate st)
     = DFS_dircycle_linear_tracked_aux_state.truncate (rdc.DFS_skel_more_upd2 st)"
  "dc.DFS_skel_more_ret1 (DFS_dircycle_linear_tracked_aux_state.truncate st)
     = DFS_dircycle_linear_tracked_aux_state.truncate (rdc.DFS_skel_more_ret1 st)"
  "dc.DFS_skel_more_ret2 (DFS_dircycle_linear_tracked_aux_state.truncate st)
     = DFS_dircycle_linear_tracked_aux_state.truncate (rdc.DFS_skel_more_ret2 st)"
  by (simp_all add: dc.DFS_skel_more_upd1_def rdc.DFS_skel_more_upd1_def
                    dc.DFS_skel_more_upd2_def rdc.DFS_skel_more_upd2_def
                    dc.DFS_skel_more_ret1_def rdc.DFS_skel_more_ret1_def
                    dc.DFS_skel_more_ret2_def rdc.DFS_skel_more_ret2_def
                    cyc_on_push_def rcyc_on_push_def
                    cyc_on_backtrack_def rcyc_on_backtrack_def
                    cyc_on_empty_def rcyc_on_empty_def
                    cyc_on_found_def rcyc_on_found_def
                    DFS_dircycle_linear_tracked_aux_state.truncate_def Let_def)

subsection \<open>The projection commutes with the whole run\<close>

theorem refine_run_agree:
  assumes dom: "rdc.DFS_skel_more_dom st"
      and "rdc.invar_1 st"
      and "rdc.invar_seen_stack st"
  shows "DFS_dircycle_linear_tracked_aux_state.truncate (rdc.DFS_skel_more st)
           = dc.DFS_skel_more (DFS_dircycle_linear_tracked_aux_state.truncate st)"
  using assms(2-)
proof (induction rule: rdc.DFS_skel_more_induct[OF dom])
  case IH: (1 st)
  have t1: "dc.invar_1 (DFS_dircycle_linear_tracked_aux_state.truncate st)"
    using IH(4) by simp
  have t2: "dc.invar_seen_stack (DFS_dircycle_linear_tracked_aux_state.truncate st)"
    using IH(5) by simp
  note simps = rdc.DFS_skel_more_simps[OF IH(1)]
  note tsimps = dc.DFS_skel_more_simps[OF dc.DFS_skel_more_terminates[OF t1 t2]]
  show ?case
  proof (rule rdc.DFS_skel_more_cases[where dfs_state = st])
    assume c: "rdc.DFS_skel_more_call_1_conds st"
    have tc: "dc.DFS_skel_more_call_1_conds (DFS_dircycle_linear_tracked_aux_state.truncate st)"
      using c by simp
    have "DFS_dircycle_linear_tracked_aux_state.truncate (rdc.DFS_skel_more (rdc.DFS_skel_more_upd1 st))
            = dc.DFS_skel_more
                (DFS_dircycle_linear_tracked_aux_state.truncate (rdc.DFS_skel_more_upd1 st))"
      by (rule IH(2)[OF c rdc.invar_1_holds_1[OF c IH(4)]
                          rdc.invar_seen_stack_holds_1[OF c IH(4) IH(5)]])
    thus ?thesis by (simp add: simps(1)[OF c] tsimps(1)[OF tc])
  next
    assume c: "rdc.DFS_skel_more_call_2_conds st"
    have tc: "dc.DFS_skel_more_call_2_conds (DFS_dircycle_linear_tracked_aux_state.truncate st)"
      using c by simp
    have "DFS_dircycle_linear_tracked_aux_state.truncate (rdc.DFS_skel_more (rdc.DFS_skel_more_upd2 st))
            = dc.DFS_skel_more
                (DFS_dircycle_linear_tracked_aux_state.truncate (rdc.DFS_skel_more_upd2 st))"
      by (rule IH(3)[OF c rdc.invar_1_holds_2[OF c IH(4)]
                          rdc.invar_seen_stack_holds_2[OF c IH(4) IH(5)]])
    thus ?thesis by (simp add: simps(2)[OF c] tsimps(2)[OF tc])
  next
    assume c: "rdc.DFS_skel_more_ret_1_conds st"
    have tc: "dc.DFS_skel_more_ret_1_conds (DFS_dircycle_linear_tracked_aux_state.truncate st)"
      using c by simp
    show ?thesis by (simp add: simps(3)[OF c] tsimps(3)[OF tc])
  next
    assume c: "rdc.DFS_skel_more_ret_2_conds st"
    have tc: "dc.DFS_skel_more_ret_2_conds (DFS_dircycle_linear_tracked_aux_state.truncate st)"
      using c by simp
    show ?thesis by (simp add: simps(4)[OF c] tsimps(4)[OF tc])
  qed
qed

lemma truncate_initial:
  "DFS_dircycle_linear_tracked_aux_state.truncate dircycle_refine_initial_state
     = dircycle_tracked_initial_state"
  by (simp add: DFS_dircycle_linear_tracked_aux_state.truncate_def
                dircycle_refine_initial_state_def dircycle_tracked_initial_state_def)

text \<open>The capstone of this theory: forgetting the carried graph, the refined run \<^emph>\<open>is\<close> the
  tracked run of \<^theory>\<open>Directed_Cycle_DFS.DFS_DirCycle_Linear_Tracked_Aux\<close>. Everything proved there ---
  soundness, completeness, and the nine exports the outer sweep consumes --- therefore holds of the
  refined run verbatim.\<close>

theorem dircycle_refine_agrees_tracked:
  "DFS_dircycle_linear_tracked_aux_state.truncate dircycle_refine_result = dircycle_tracked_result"
proof -
  have "DFS_dircycle_linear_tracked_aux_state.truncate (rdc.DFS_skel_more dircycle_refine_initial_state)
          = dc.DFS_skel_more
              (DFS_dircycle_linear_tracked_aux_state.truncate dircycle_refine_initial_state)"
    by (rule refine_run_agree[OF rdc.DFS_skel_more_terminates[OF initial_refine_invars]
                                 initial_refine_invars])
  thus ?thesis by (simp add: dircycle_refine_eq_more truncate_initial)
qed

corollary dircycle_refine_components:
  shows "stack dircycle_refine_result = stack dircycle_tracked_result"
    and "seen dircycle_refine_result = seen dircycle_tracked_result"
    and "finished dircycle_refine_result = finished dircycle_tracked_result"
    and "gray dircycle_refine_result = gray dircycle_tracked_result"
    and "unfinished dircycle_refine_result = unfinished dircycle_tracked_result"
    and "DFS_dircycle_linear_tracked_aux_state.cycle dircycle_refine_result
           = DFS_dircycle_linear_tracked_aux_state.cycle dircycle_tracked_result"
  using arg_cong[where f = stack, OF dircycle_refine_agrees_tracked]
  using arg_cong[where f = seen, OF dircycle_refine_agrees_tracked]
  using arg_cong[where f = finished, OF dircycle_refine_agrees_tracked]
  using arg_cong[where f = gray, OF dircycle_refine_agrees_tracked]
  using arg_cong[where f = unfinished, OF dircycle_refine_agrees_tracked]
  using arg_cong[where f = DFS_dircycle_linear_tracked_aux_state.cycle,
                 OF dircycle_refine_agrees_tracked]
  by simp_all

subsection \<open>The one genuinely new export: the carried graph\<close>

text \<open>Everything level 1 exports transfers along \<open>dircycle_refine_agrees_tracked\<close> unchanged.
  What is new at level 2 is the adjacency map the run hands back, and it is exactly the \<open>A\<close>
  contract of the \<^emph>\<open>next\<close> call: on a clean run it is \<open>G\<close> with the in-edges of the enlarged
  finished region removed. So an outer whole-graph sweep threads it from call to call and never
  re-prunes.\<close>

lemma dircycle_refine_invar_adj: "rdc.invar_adj dircycle_refine_result"
  using rdc.invar_adj_holds[OF rdc.DFS_skel_more_terminates[OF initial_refine_invars]
                               initial_refine_invar_adj initial_refine_invars(1)]
  by (simp add: dircycle_refine_eq_more)

lemma dircycle_refine_adj_graph_inv: "Graph.graph_inv (adj dircycle_refine_result)"
  using dircycle_refine_invar_adj by (simp add: rdc.invar_adj_def)

lemma dircycle_refine_adj_abs:
  "Graph.digraph_abs (adj dircycle_refine_result)
     = Graph.digraph_abs G - (UNIV \<times> t_set (seen dircycle_refine_result))"
  using dircycle_refine_invar_adj by (simp add: rdc.invar_adj_def)

lemma dircycle_refine_adj_abs_finished:
  assumes "\<not> DFS_dircycle_linear_tracked_aux_state.cycle dircycle_refine_result"
  shows "Graph.digraph_abs (adj dircycle_refine_result)
           = Graph.digraph_abs G - (UNIV \<times> t_set (finished dircycle_refine_result))"
proof -
  have ncyc: "\<not> DFS_dircycle_linear_tracked_aux_state.cycle dircycle_tracked_result"
    using assms dircycle_refine_components(6) by simp
  have empty: "stack dircycle_tracked_result = []"
    using no_cycle_ret_1[OF dircycle_tracked_initial_dom ncyc]
    by (auto simp: dc.DFS_skel_more_ret_1_conds_def split: list.splits)
  have "t_set (finished dircycle_tracked_result) = t_set (seen dircycle_tracked_result)"
    using dircycle_tracked_invars(3) empty by (auto simp: invar_ssf_def)
  thus ?thesis
    using dircycle_refine_adj_abs dircycle_refine_components(2,3) by simp
qed

end

end

end
