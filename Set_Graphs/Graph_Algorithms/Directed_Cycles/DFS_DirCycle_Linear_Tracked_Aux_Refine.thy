theory DFS_DirCycle_Linear_Tracked_Aux_Refine
  imports DFS_Skeletons.DFS_Skeleton_Refine_Unfin DFS_DirCycle_Linear_Tracked_Aux
begin

text \<open>Level 2 of the refinement chain at the \<^emph>\<open>inner\<close> (pre-seeded) directed-cycle DFS: the
  instance of \<^locale>\<open>DFS_skeleton_refine_unfin\<close> that the tracked search of
  \<^theory>\<open>Directed_Cycle_DFS.DFS_DirCycle_Linear_Tracked_Aux\<close> becomes once the adjacency map moves into the
  state and is pruned \<^emph>\<open>at backtrack\<close>.

  The state record gains one field, \<open>adj\<close>, and \<open>on_backtrack\<close> gains one job: besides moving the
  finished vertex out of \<open>gray\<close> and \<open>unfinished\<close> it deletes every edge \<^emph>\<open>entering\<close> it. The
  carried map then offers exactly the \<^emph>\<open>unfinished\<close> out-neighbours --- the unseen ones plus those
  still on the stack --- so the loop reads a plain \<open>\<N> (adj st) v\<close> where level 1 reads
  \<open>(\<N>\<^sub>G v) -\<^sub>G (seen st)\<close>, and the selected vertex is either unseen (descend) or on the stack:
  a back edge.

  \<^bold>\<open>The back-edge test is one membership.\<close> \<open>rcyc_found\<close> asks whether \<open>sel (\<N> (adj st) v)\<close> is
  gray. Level 1 (and the prune-at-push variant this theory replaces) intersects the \<^emph>\<open>original\<close>
  neighbourhood \<open>\<N>\<^sub>G v\<close> with \<open>gray\<close> at every step, at \<open>O(deg v)\<close> a step; here the original
  \<open>G\<close> is not consulted by the loop at all, and the whole search is \<open>O(V + E)\<close>.

  \<^bold>\<open>The price: a weaker equivalence to level 1.\<close> Level 1 halts at the \<^emph>\<open>first\<close> moment the top
  of the stack has a gray neighbour; this search halts when \<open>sel\<close> \<^emph>\<open>hands it\<close> a gray neighbour,
  which may be later --- \<open>sel\<close> may first pick a white sibling and descend. The two runs are
  therefore lockstep-equal only while no back edge is adjacent to the stack, which is every step
  of a \<^emph>\<open>clean\<close> run: on clean runs the two results agree as states
  (\<open>dircycle_refine_agrees_tracked_clean\<close>), and the verdicts agree \<^emph>\<open>unconditionally\<close>
  (\<open>dircycle_refine_verdict\<close>) because a back edge adjacent to the stack can never be backtracked
  past --- its target stays in the carried neighbourhood --- so it forces a report
  (\<open>back_edge_wit_forces_cycle\<close>). The outer sweep only ever reads the finished/unfinished sets
  of a clean call, so this is exactly the contract it needs.

  \<^bold>\<open>Deleting in-edges needs a reverse map --- carried in the state.\<close>
  \<open>Pair_Graph_Specs.delete_edge\<close> is keyed by an edge's source, so removing the edges into \<open>u\<close>
  means enumerating \<open>u\<close>'s predecessors. The state therefore carries \<open>radj\<close>, kept the \<^emph>\<open>exact
  inverse\<close> of the carried map (\<open>invar_radj\<close>): backtracking \<open>v\<close> walks \<open>v\<close>'s predecessor row
  \<open>\<N> (radj st) v\<close> deleting \<open>(p, v)\<close> from \<open>adj\<close> for each predecessor \<open>p\<close>, and then deletes
  the reverse edges too --- dropping the row \<open>v\<close> from \<open>radj\<close>, one key deletion, which is
  exactly the inverse image of the in-edges just removed. Each vertex's row is walked at most
  once, so over a whole run the deletions amount to a single pass over the edges and the search
  stays linear.

  \<^bold>\<open>The incoming maps \<open>A\<close> and \<open>RA\<close>.\<close> The run is pre-seeded with a finished region \<open>f\<close>, so
  it is also pre-seeded with the maps appropriate to it: \<open>A\<close> is assumed to be \<open>G\<close> with the
  in-edges of \<open>t_set f\<close> already gone, and \<open>RA\<close> its inverse. Unlike the prune-at-push variant
  the initial state does \<^emph>\<open>not\<close> delete the root's in-edges --- the root is merely gray, and a
  back edge into it is caught by the membership test. An outer whole-graph sweep threads both
  maps from one call to the next, so the pruning is never redone and no inverse is ever
  rebuilt.\<close>

record ('ver, 'vset, 'adjmap) DFS_dircycle_linear_tracked_aux_refine_state =
  "('ver, 'vset) DFS_dircycle_linear_tracked_aux_state" +
  adj  :: "'adjmap"
  radj :: "'adjmap"

locale DFS_dircycle_linear_tracked_aux_refine =
  DFS_dircycle_linear_tracked_aux where lookup = lookup
  for lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option" +
  fixes A :: "'adjmap" and RA :: "'adjmap"
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

definition "del_in_edges rm u M = del_preds (Graph.neighbourhood rm u) u M"

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

text \<open>The callbacks of \<^theory>\<open>Directed_Cycle_DFS.DFS_DirCycle_Linear_Tracked_Aux\<close>, except that
  \<open>rcyc_on_backtrack\<close> also prunes the carried graph, and \<open>rcyc_found\<close> tests the \<^emph>\<open>selected\<close>
  vertex for grayness --- one membership, no intersection, and no read of the original \<open>G\<close>.\<close>

definition "rcyc_found (dfs_state::('v,'vset,'adjmap) DFS_dircycle_linear_tracked_aux_refine_state) =
   (case stack dfs_state of [] \<Rightarrow> False
    | (v # stack_tl) \<Rightarrow>
        (Graph.neighbourhood (adj dfs_state) v \<noteq> \<emptyset>\<^sub>N
         \<and> isin (gray dfs_state) (sel (Graph.neighbourhood (adj dfs_state) v))))"

definition "rcyc_on_found (dfs_state::('v,'vset,'adjmap) DFS_dircycle_linear_tracked_aux_refine_state) =
  (dfs_state \<lparr>cycle := True\<rparr>)"

definition "rcyc_on_empty (dfs_state::('v,'vset,'adjmap) DFS_dircycle_linear_tracked_aux_refine_state) = dfs_state"

definition "rcyc_on_push u (dfs_state::('v,'vset,'adjmap) DFS_dircycle_linear_tracked_aux_refine_state) =
  (dfs_state \<lparr>gray := insert u (gray dfs_state)\<rparr>)"

definition "rcyc_on_backtrack v (dfs_state::('v,'vset,'adjmap) DFS_dircycle_linear_tracked_aux_refine_state) =
  (dfs_state \<lparr>finished := insert v (finished dfs_state),
              gray := vset_delete v (gray dfs_state),
              unfinished := vset_delete v (unfinished dfs_state),
              adj := del_in_edges (radj dfs_state) v (adj dfs_state),
              radj := delete v (radj dfs_state)\<rparr>)"

text \<open>The initial state is level 1's plus the two carried maps, which are the caller's \<open>A\<close> and
  \<open>RA\<close> \<^emph>\<open>verbatim\<close>: \<open>A\<close> already lacks the in-edges of the finished seed \<open>t_set f\<close> and \<open>RA\<close>
  is its inverse, and the root is merely gray, so its in-edges stay --- a back edge into the
  root is caught by the membership test, not by pruning.\<close>
definition "dircycle_refine_initial_state =
  \<lparr>stack = [s], seen = insert s f, finished = f, gray = insert s \<emptyset>\<^sub>N,
   unfinished = uf, cycle = False, adj = A, radj = RA\<rparr>"

lemmas [code] = dircycle_refine_initial_state_def

sublocale rdc: DFS_skeleton_refine_unfin
  where lookup = lookup and G = G and s = s
    and found = rcyc_found and on_found = rcyc_on_found
    and on_empty = rcyc_on_empty and on_backtrack = rcyc_on_backtrack
    and on_push = rcyc_on_push and adjmap = adj
  by unfold_locales

abbreviation "find_dircycle_refine \<equiv> rdc.DFS_skeleton_refine_unfin_impl"

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
  "adj (rcyc_on_push u st) = adj st"
  "adj (rcyc_on_backtrack v st) = del_in_edges (radj st) v (adj st)"
  by (auto simp: rcyc_on_found_def rcyc_on_empty_def rcyc_on_backtrack_def rcyc_on_push_def)

lemma rcyc_radj[simp]:
  "radj (rcyc_on_found st) = radj st"
  "radj (rcyc_on_empty st) = radj st"
  "radj (rcyc_on_push u st) = radj st"
  "radj (rcyc_on_backtrack v st) = delete v (radj st)"
  by (auto simp: rcyc_on_found_def rcyc_on_empty_def rcyc_on_backtrack_def rcyc_on_push_def)

text \<open>The inverse-map invariant: \<open>radj\<close> is the exact inverse of the carried \<open>adj\<close>. It is what
  legitimises reading a vertex's predecessors off \<open>radj\<close> at backtrack, and dropping its row
  afterwards is what re-establishes it.\<close>
definition "invar_radj st \<longleftrightarrow>
  Graph.graph_inv (radj st)
  \<and> Graph.digraph_abs (radj st) = {(u, p). (p, u) \<in> Graph.digraph_abs (adj st)}"

end


text \<open>The reasoning layer, on top of level 1's \<^locale>\<open>DFS_dircycle_linear_tracked_aux_thms\<close>. Three further
  assumption groups, and no others:
  \<^item> \<open>sel_cong\<close> --- \<open>sel\<close> is determined by the element set. It is \<^emph>\<open>not\<close> needed by the
    skeleton any more (the refined loop is not compared to the plain one there); it is needed
    \<^emph>\<open>here\<close>, for the clean-run lockstep against level 1: on a clean run the refined loop hands
    \<open>sel\<close> a vset built by repeated edge deletion where level 1 hands it one built by \<open>-\<^sub>G\<close>, and
    \<^locale>\<open>Set_Choose\<close> does not make \<open>sel\<close> a function of the underlying set (at the
    red-black-tree instantiation it is the root label). It has to be passed on to whoever
    instantiates the vset ADT, who must supply a set-determined choice --- for a search tree, the
    leftmost element rather than the root.
  \<^item> \<open>A\<close> is a well-formed adjacency map, namely \<open>G\<close> with the in-edges of the seed \<open>f\<close> already
    deleted, and \<open>RA\<close> is a well-formed adjacency map holding exactly the \<^emph>\<open>inverse\<close> of \<open>A\<close>
    --- the seed instance of \<open>invar_radj\<close>.\<close>

locale DFS_dircycle_linear_tracked_aux_refine_thms =
  DFS_dircycle_linear_tracked_aux_refine + DFS_dircycle_linear_tracked_aux_thms +
  assumes sel_cong: "vset_inv X \<Longrightarrow> vset_inv Y \<Longrightarrow> t_set X = t_set Y \<Longrightarrow> sel X = sel Y"
      and A_graph_inv: "Graph.graph_inv A"
      and A_abs: "Graph.digraph_abs A = Graph.digraph_abs G - (UNIV \<times> t_set f)"
      and RA_graph_inv: "Graph.graph_inv RA"
      and RA_abs: "Graph.digraph_abs RA = {(u, p). (p, u) \<in> Graph.digraph_abs A}"
begin

text \<open>The instance invariant handed to \<^locale>\<open>DFS_skeleton_refine_unfin_thms\<close>'s \<open>aux_invar\<close> slot:
  level 1's structural invariants, bundled. It is what turns a surviving selection into an unseen
  vertex (\<open>sel_unseen\<close>): the selection is not finished (the carried map offers no finished
  vertex), and \<open>found\<close> failing means it is not gray, i.e.\ not on the stack --- and
  \<open>seen = finished \<union> stack\<close>.\<close>
definition "rcyc_aux_invar st \<longleftrightarrow>
  invar_ssf st \<and> invar_fin st \<and> invar_gray st \<and> invar_gray_stack st
  \<and> invar_unfin st \<and> invar_fin_unfin st \<and> invar_seed st \<and> invar_radj st"

lemma rcyc_aux_invar_props[invar_props_elims]:
  "rcyc_aux_invar st \<Longrightarrow>
     (\<lbrakk>invar_ssf st; invar_fin st; invar_gray st; invar_gray_stack st;
       invar_unfin st; invar_fin_unfin st; invar_seed st; invar_radj st\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: rcyc_aux_invar_def)

lemma rcyc_aux_invar_intro[invar_props_intros]:
  "\<lbrakk>invar_ssf st; invar_fin st; invar_gray st; invar_gray_stack st;
    invar_unfin st; invar_fin_unfin st; invar_seed st; invar_radj st\<rbrakk> \<Longrightarrow> rcyc_aux_invar st"
  by (auto simp: rcyc_aux_invar_def)

subsection \<open>What \<open>del_in_edges\<close> and the row deletion do\<close>

lemma finite_digraph_abs: "finite (Graph.digraph_abs G)"
  by (rule Graph.finite_graph[OF dc.graph_inv(1) dc.graph_inv(2) dc.graph_inv(3)])

lemma preds_finite: "finite {p. (p, u) \<in> Graph.digraph_abs G}"
proof -
  have "{p. (p, u) \<in> Graph.digraph_abs G} \<subseteq> fst ` Graph.digraph_abs G"
    by force
  thus ?thesis using finite_digraph_abs by (simp add: finite_subset)
qed

text \<open>Under the inverse invariant, \<open>u\<close>'s row of the reverse map holds \<^emph>\<open>exactly\<close> the sources
  of the in-edges of \<open>u\<close> still present in the carried map --- so walking it deletes all of
  them, and there are no others to delete. No sub-\<open>G\<close> side condition is needed any more: the
  row is correct by the invariant, not by reference to the original graph.\<close>
lemma del_in_edges_inv:
  assumes gi: "Graph.graph_inv M"
      and gir: "Graph.graph_inv RM"
      and inv_abs: "Graph.digraph_abs RM = {(u, p). (p, u) \<in> Graph.digraph_abs M}"
      and sub: "Graph.digraph_abs M \<subseteq> Graph.digraph_abs G"
  shows "Graph.graph_inv (del_in_edges RM u M)"
    and "Graph.digraph_abs (del_in_edges RM u M) = Graph.digraph_abs M - (UNIV \<times> {u})"
proof -
  have pinv: "vset_inv (Graph.neighbourhood RM u)"
    by (rule Graph.neighbourhood_invars'[OF gir])
  have pset: "t_set (Graph.neighbourhood RM u) = {p. (p, u) \<in> Graph.digraph_abs M}"
    by (auto simp: Graph.are_connected_abs_general[OF gir] inv_abs)
  have psub: "t_set (Graph.neighbourhood RM u) \<subseteq> {p. (p, u) \<in> Graph.digraph_abs G}"
    using pset sub by auto
  have pfin: "finite (t_set (Graph.neighbourhood RM u))"
    by (rule finite_subset[OF psub preds_finite])
  show "Graph.graph_inv (del_in_edges RM u M)"
    unfolding del_in_edges_def
    by (rule del_preds_graph_inv[OF pinv pfin gi])
  have "Graph.digraph_abs (del_in_edges RM u M)
          = Graph.digraph_abs M - (t_set (Graph.neighbourhood RM u) \<times> {u})"
    unfolding del_in_edges_def
    by (rule del_preds_abs[OF pinv pfin gi])
  also have "\<dots> = Graph.digraph_abs M - (UNIV \<times> {u})"
    using pset by auto
  finally show "Graph.digraph_abs (del_in_edges RM u M)
                  = Graph.digraph_abs M - (UNIV \<times> {u})" .
qed

text \<open>Deleting a key of a well-formed adjacency map removes exactly that key's row of edges.\<close>
lemma adjmap_delete_key:
  assumes "Graph.graph_inv M"
  shows "Graph.graph_inv (delete v M)"
    and "Graph.digraph_abs (delete v M) = Graph.digraph_abs M - ({v} \<times> UNIV)"
  using assms
  by (auto simp: Graph.graph_inv_def Graph.digraph_abs_def Graph.neighbourhood_def
                 Graph.adjmap.invar_delete Graph.adjmap.map_delete
                 Graph.vset.set.invar_empty Graph.vset.set.set_empty Graph.vset.set.set_isin
           split: option.splits if_splits)

subsection \<open>The two steps, at this instance\<close>

context
includes set_ops.automation2 and Graph.adjmap.automation and Graph.vset.set.automation
begin

lemma refine_upd1_unfold:
  "stack (rdc.DFS_skeleton_refine_unfin_upd1 st)
     = sel (Graph.neighbourhood (adj st) (hd (stack st))) # stack st"
  "seen (rdc.DFS_skeleton_refine_unfin_upd1 st)
     = insert (sel (Graph.neighbourhood (adj st) (hd (stack st)))) (seen st)"
  "finished (rdc.DFS_skeleton_refine_unfin_upd1 st) = finished st"
  "gray (rdc.DFS_skeleton_refine_unfin_upd1 st)
     = insert (sel (Graph.neighbourhood (adj st) (hd (stack st)))) (gray st)"
  "unfinished (rdc.DFS_skeleton_refine_unfin_upd1 st) = unfinished st"
  "adj (rdc.DFS_skeleton_refine_unfin_upd1 st) = adj st"
  "radj (rdc.DFS_skeleton_refine_unfin_upd1 st) = radj st"
  "cycle (rdc.DFS_skeleton_refine_unfin_upd1 st) = cycle st"
  by (simp_all add: rdc.DFS_skeleton_refine_unfin_upd1_def rcyc_on_push_def Let_def)

lemma refine_upd2_unfold:
  "stack (rdc.DFS_skeleton_refine_unfin_upd2 st) = tl (stack st)"
  "seen (rdc.DFS_skeleton_refine_unfin_upd2 st) = seen st"
  "finished (rdc.DFS_skeleton_refine_unfin_upd2 st) = insert (hd (stack st)) (finished st)"
  "gray (rdc.DFS_skeleton_refine_unfin_upd2 st) = vset_delete (hd (stack st)) (gray st)"
  "unfinished (rdc.DFS_skeleton_refine_unfin_upd2 st) = vset_delete (hd (stack st)) (unfinished st)"
  "adj (rdc.DFS_skeleton_refine_unfin_upd2 st) = del_in_edges (radj st) (hd (stack st)) (adj st)"
  "radj (rdc.DFS_skeleton_refine_unfin_upd2 st) = delete (hd (stack st)) (radj st)"
  "cycle (rdc.DFS_skeleton_refine_unfin_upd2 st) = cycle st"
  by (simp_all add: rdc.DFS_skeleton_refine_unfin_upd2_def rcyc_on_backtrack_def)

subsection \<open>What the carried map offers, at this instance\<close>

text \<open>Under \<open>invar_adj\<close> and the instance invariants, \<open>\<N> (adj st) v\<close> is \<open>v\<close>'s unfinished
  \<open>G\<close>-neighbourhood.\<close>
lemma adj_nbr_set_fin:
  assumes "rdc.invar_adj st" and "rcyc_aux_invar st"
  shows "t_set (Graph.neighbourhood (adj st) v)
           = {w. (v, w) \<in> Graph.digraph_abs G} - t_set (finished st)"
proof -
  have fin_char: "t_set (finished st) = t_set (seen st) - set (stack st)"
    using assms(2) by (auto simp: rcyc_aux_invar_def invar_ssf_def)
  thus ?thesis using rdc.adj_nbr_set[OF assms(1), of v] by simp
qed

text \<open>A surviving selection --- offered, but not reported gray --- is unseen: not finished
  because the map offers no finished vertex, not on the stack because \<open>found\<close> said so, and
  \<open>seen\<close> is the union of the two.\<close>
lemma rcyc_sel_unseen:
  assumes c: "rdc.DFS_skeleton_refine_unfin_call_1_conds st"
      and ax: "rcyc_aux_invar st"
      and ia: "rdc.invar_adj st"
  shows "sel (Graph.neighbourhood (adj st) (hd (stack st))) \<notin> t_set (seen st)"
proof -
  let ?v = "hd (stack st)"
  let ?u = "sel (Graph.neighbourhood (adj st) ?v)"
  have ne: "Graph.neighbourhood (adj st) ?v \<noteq> \<emptyset>\<^sub>N"
    and nf: "\<not> rcyc_found st"
    and stk: "stack st \<noteq> []"
    using c by (auto elim!: call_cond_elims)
  have mem: "?u \<in> t_set (Graph.neighbourhood (adj st) ?v)"
    by (rule Graph.vset.choose'[OF ne rdc.adj_nbr_inv[OF ia]])
  have nfin: "?u \<notin> t_set (finished st)"
    using mem adj_nbr_set_fin[OF ia ax] by auto
  have "\<not> isin (gray st) ?u"
    using nf ne stk by (auto simp: rcyc_found_def split: list.splits)
  hence ngray: "?u \<notin> t_set (gray st)"
    using ax by (auto simp: rcyc_aux_invar_def invar_gray_def Graph.vset.set.set_isin)
  have "t_set (gray st) = set (stack st)"
    and "t_set (finished st) = t_set (seen st) - set (stack st)"
    and "set (stack st) \<subseteq> t_set (seen st)"
    using ax by (auto simp: rcyc_aux_invar_def invar_gray_stack_def invar_ssf_def)
  thus ?thesis using nfin ngray by auto
qed

subsection \<open>The backtrack step's effect on the two carried maps\<close>

text \<open>What the skeleton's \<open>upd2\<close> obligations demand, and what re-establishes \<open>invar_radj\<close>:
  the carried map loses exactly the popped vertex's in-edges (its row of the reverse map is
  correct by \<open>invar_radj\<close>), and the reverse map loses exactly that row --- the inverse image of
  those in-edges.\<close>

lemma rcyc_upd2_adj:
  assumes c: "rdc.DFS_skeleton_refine_unfin_call_2_conds st"
      and ax: "rcyc_aux_invar st"
      and ia: "rdc.invar_adj st"
  shows "Graph.graph_inv (adj (rdc.DFS_skeleton_refine_unfin_upd2 st))"
    and "Graph.digraph_abs (adj (rdc.DFS_skeleton_refine_unfin_upd2 st))
           = Graph.digraph_abs (adj st) - (UNIV \<times> {hd (stack st)})"
proof -
  have gir: "Graph.graph_inv (radj st)"
    and inv_abs: "Graph.digraph_abs (radj st) = {(u, p). (p, u) \<in> Graph.digraph_abs (adj st)}"
    using ax by (auto simp: rcyc_aux_invar_def invar_radj_def)
  have gi: "Graph.graph_inv (adj st)"
    and sub: "Graph.digraph_abs (adj st) \<subseteq> Graph.digraph_abs G"
    using ia by (auto simp: rdc.invar_adj_def)
  show "Graph.graph_inv (adj (rdc.DFS_skeleton_refine_unfin_upd2 st))"
    and "Graph.digraph_abs (adj (rdc.DFS_skeleton_refine_unfin_upd2 st))
           = Graph.digraph_abs (adj st) - (UNIV \<times> {hd (stack st)})"
    using del_in_edges_inv[OF gi gir inv_abs sub]
    by (simp_all add: refine_upd2_unfold)
qed

lemma rcyc_upd2_radj:
  assumes c: "rdc.DFS_skeleton_refine_unfin_call_2_conds st"
      and ax: "rcyc_aux_invar st"
      and ia: "rdc.invar_adj st"
  shows "invar_radj (rdc.DFS_skeleton_refine_unfin_upd2 st)"
proof -
  have gir: "Graph.graph_inv (radj st)"
    and inv_abs: "Graph.digraph_abs (radj st) = {(u, p). (p, u) \<in> Graph.digraph_abs (adj st)}"
    using ax by (auto simp: rcyc_aux_invar_def invar_radj_def)
  have "Graph.digraph_abs (delete (hd (stack st)) (radj st))
          = Graph.digraph_abs (radj st) - ({hd (stack st)} \<times> UNIV)"
    by (rule adjmap_delete_key(2)[OF gir])
  also have "\<dots> = {(u, p). (p, u) \<in> Graph.digraph_abs (adj st) - (UNIV \<times> {hd (stack st)})}"
    using inv_abs by auto
  finally show ?thesis
    using adjmap_delete_key(1)[OF gir] rcyc_upd2_adj(2)[OF c ax ia]
    by (simp add: invar_radj_def refine_upd2_unfold)
qed

subsection \<open>The instance invariant is preserved by the refined steps\<close>

lemma rcyc_aux_invar_holds_upd1:
  assumes c: "rdc.DFS_skeleton_refine_unfin_call_1_conds st"
      and ax: "rcyc_aux_invar st"
      and ia: "rdc.invar_adj st"
      and i1: "rdc.invar_1 st"
      and iss: "rdc.invar_seen_stack st"
  shows "rcyc_aux_invar (rdc.DFS_skeleton_refine_unfin_upd1 st)"
proof -
  let ?u = "sel (Graph.neighbourhood (adj st) (hd (stack st)))"
  have unseen: "?u \<notin> t_set (seen st)" by (rule rcyc_sel_unseen[OF c ax ia])
  have ustack: "?u \<notin> set (stack st)"
    and ufin: "?u \<notin> t_set (finished st)"
    using unseen ax by (auto simp: rcyc_aux_invar_def invar_ssf_def)
  have dv: "?u \<in> dVs (Graph.digraph_abs G)"
    using rdc.sel_adj_nbr_props(3)[OF c ia] by simp
  show ?thesis
    using ax i1 unseen ustack ufin dv
    by (auto simp: rcyc_aux_invar_def invar_ssf_def invar_fin_def invar_gray_def
                   invar_gray_stack_def invar_unfin_def invar_fin_unfin_def invar_seed_def
                   invar_radj_def refine_upd1_unfold
             elim!: invar_props_elims)
qed

lemma rcyc_aux_invar_holds_upd2:
  assumes c: "rdc.DFS_skeleton_refine_unfin_call_2_conds st"
      and ax: "rcyc_aux_invar st"
      and ia: "rdc.invar_adj st"
      and i1: "rdc.invar_1 st"
      and iss: "rdc.invar_seen_stack st"
  shows "rcyc_aux_invar (rdc.DFS_skeleton_refine_unfin_upd2 st)"
proof -
  obtain v stack_tl where stk: "stack st = v # stack_tl"
    using c by (auto elim!: call_cond_elims)
  have dist: "distinct (stack st)"
    and sub: "set (stack st) \<subseteq> t_set (seen st)"
    and fin_char: "t_set (finished st) = t_set (seen st) - set (stack st)"
    and seen_dVs: "t_set (seen st) \<subseteq> dVs (Graph.digraph_abs G)"
    using ax by (auto simp: rcyc_aux_invar_def invar_ssf_def)
  have vseen: "v \<in> t_set (seen st)" and vnotl: "v \<notin> set stack_tl"
    using stk dist sub by auto
  have vnfin: "v \<in> dVs (Graph.digraph_abs G)"
    using vseen seen_dVs by auto
  have vunfin: "v \<in> t_set (unfinished st)"
    using ax vnfin stk fin_char
    by (auto simp: rcyc_aux_invar_def invar_fin_unfin_def)
  show ?thesis
    using ax i1 stk dist vseen vnotl vnfin vunfin rcyc_upd2_radj[OF c ax ia]
    by (auto simp: rcyc_aux_invar_def invar_ssf_def invar_fin_def invar_gray_def
                   invar_gray_stack_def invar_unfin_def invar_fin_unfin_def invar_seed_def
                   refine_upd2_unfold
             elim!: invar_props_elims)
qed

end

subsection \<open>The instance of the refined skeleton\<close>

sublocale rdc: DFS_skeleton_refine_unfin_thms
  where lookup = lookup and G = G and s = s
    and found = rcyc_found and on_found = rcyc_on_found
    and on_empty = rcyc_on_empty and on_backtrack = rcyc_on_backtrack
    and on_push = rcyc_on_push and adjmap = adj and aux_invar = rcyc_aux_invar
proof unfold_locales
  show "rdc.DFS_skeleton_axioms"
    using dircycle_tracked_axioms
    by (simp add: rdc.DFS_skeleton_axioms_def DFS_dircycle_linear_tracked_aux_axioms_def)
  show "stack (rcyc_on_found st) = stack st" for st by simp
  show "seen (rcyc_on_found st) = seen st" for st by simp
  show "stack (rcyc_on_empty st) = stack st" for st by simp
  show "seen (rcyc_on_empty st) = seen st" for st by simp
  show "stack (rcyc_on_backtrack v st) = stack st" for v st by simp
  show "seen (rcyc_on_backtrack v st) = seen st" for v st by simp
  show "stack (rcyc_on_push u st) = stack st" for u st by simp
  show "seen (rcyc_on_push u st) = seen st" for u st by simp
  show "adj (st \<lparr>stack := xs\<rparr>) = adj st" for st xs by simp
  show "adj (st \<lparr>seen := S\<rparr>) = adj st" for st S by simp
  show "adj (rcyc_on_found st) = adj st" for st by simp
  show "adj (rcyc_on_empty st) = adj st" for st by simp
  show "adj (rcyc_on_push u st) = adj st" for u st by simp
  show "Graph.graph_inv (adj (rdc.DFS_skeleton_refine_unfin_upd2 st))"
    if "rdc.DFS_skeleton_refine_unfin_call_2_conds st" and "rcyc_aux_invar st"
   and "rdc.invar_adj st" and "rdc.invar_1 st" and "rdc.invar_seen_stack st" for st
    by (rule rcyc_upd2_adj(1)[OF that(1,2,3)])
  show "Graph.digraph_abs (adj (rdc.DFS_skeleton_refine_unfin_upd2 st))
          = Graph.digraph_abs (adj st) - (UNIV \<times> {hd (stack st)})"
    if "rdc.DFS_skeleton_refine_unfin_call_2_conds st" and "rcyc_aux_invar st"
   and "rdc.invar_adj st" and "rdc.invar_1 st" and "rdc.invar_seen_stack st" for st
    by (rule rcyc_upd2_adj(2)[OF that(1,2,3)])
  show "sel (rdc.adj_nbr st (hd (stack st))) \<notin> t_set (seen st)"
    if "rdc.DFS_skeleton_refine_unfin_call_1_conds st" and "rcyc_aux_invar st"
   and "rdc.invar_adj st" and "rdc.invar_1 st" and "rdc.invar_seen_stack st" for st
    using rcyc_sel_unseen[OF that(1,2,3)] by simp
  show "rcyc_aux_invar (rdc.DFS_skeleton_refine_unfin_upd1 st)"
    if "rdc.DFS_skeleton_refine_unfin_call_1_conds st" and "rcyc_aux_invar st"
   and "rdc.invar_adj st" and "rdc.invar_1 st" and "rdc.invar_seen_stack st" for st
    by (rule rcyc_aux_invar_holds_upd1[OF that])
  show "rcyc_aux_invar (rdc.DFS_skeleton_refine_unfin_upd2 st)"
    if "rdc.DFS_skeleton_refine_unfin_call_2_conds st" and "rcyc_aux_invar st"
   and "rdc.invar_adj st" and "rdc.invar_1 st" and "rdc.invar_seen_stack st" for st
    by (rule rcyc_aux_invar_holds_upd2[OF that])
qed

context
includes set_ops.automation2 and Graph.adjmap.automation and Graph.vset.set.automation
begin

subsection \<open>The invariants at the initial state\<close>

lemma initial_refine_invars[simp, intro]:
  "rdc.invar_1 dircycle_refine_initial_state"
  "rdc.invar_seen_stack dircycle_refine_initial_state"
  using dircycle_tracked_axioms
  by (auto simp: rdc.invar_1_def rdc.invar_seen_stack_def dircycle_refine_initial_state_def
                 DFS_dircycle_linear_tracked_aux_axioms_def)

lemma initial_refine_aux_invar: "rcyc_aux_invar dircycle_refine_initial_state"
  using dircycle_tracked_axioms RA_graph_inv RA_abs
  by (auto simp: rcyc_aux_invar_def invar_ssf_def invar_fin_def invar_gray_def
                 invar_gray_stack_def invar_unfin_def invar_fin_unfin_def invar_seed_def
                 invar_radj_def dircycle_refine_initial_state_def
                 DFS_dircycle_linear_tracked_aux_axioms_def dVsI)

lemma initial_refine_invar_adj: "rdc.invar_adj dircycle_refine_initial_state"
proof -
  have "t_set (insert s f) - set [s] = t_set f"
    using dircycle_tracked_axioms
    by (auto simp: DFS_dircycle_linear_tracked_aux_axioms_def)
  thus ?thesis
    using A_graph_inv
    by (simp add: rdc.invar_adj_def dircycle_refine_initial_state_def A_abs)
qed

lemma dircycle_refine_initial_dom: "rdc.DFS_skeleton_refine_unfin_dom dircycle_refine_initial_state"
  by (intro rdc.DFS_skeleton_refine_unfin_terminates initial_refine_aux_invar
            initial_refine_invar_adj initial_refine_invars)

abbreviation "dircycle_refine_result \<equiv> rdc.DFS_skeleton_refine_unfin dircycle_refine_initial_state"

subsection \<open>The instance invariant survives a whole run\<close>

lemma rcyc_aux_invar_holds:
  assumes dom: "rdc.DFS_skeleton_refine_unfin_dom st"
      and "rcyc_aux_invar st" "rdc.invar_adj st" "rdc.invar_1 st" "rdc.invar_seen_stack st"
  shows "rcyc_aux_invar (rdc.DFS_skeleton_refine_unfin st)"
  using assms(2-)
proof (induction rule: rdc.DFS_skeleton_refine_unfin_induct[OF dom])
  case IH: (1 st)
  show ?case
  proof (rule rdc.DFS_skeleton_refine_unfin_cases[where dfs_state = st])
    show ?case if c: "rdc.DFS_skeleton_refine_unfin_call_1_conds st"
      using IH(2)[OF c rcyc_aux_invar_holds_upd1[OF c IH(4-7)]
                       rdc.refine_invar_adj_holds_1[OF c IH(4-7)]
                       rdc.refine_invar_1_holds_1[OF c IH(6)]
                       rdc.refine_invar_seen_stack_holds_1[OF c IH(4-7)]]
      by (simp add: rdc.DFS_skeleton_refine_unfin_simps(1)[OF IH(1) c])
    show ?case if c: "rdc.DFS_skeleton_refine_unfin_call_2_conds st"
      using IH(3)[OF c rcyc_aux_invar_holds_upd2[OF c IH(4) IH(5) IH(6) IH(7)]
                       rdc.refine_invar_adj_holds_2[OF c IH(4) IH(5) IH(6) IH(7)]
                       rdc.refine_invar_1_holds_2[OF c IH(6)]
                       rdc.refine_invar_seen_stack_holds_2[OF c IH(6) IH(7)]]
      by (simp add: rdc.DFS_skeleton_refine_unfin_simps(2)[OF IH(1) c])
    show ?case if c: "rdc.DFS_skeleton_refine_unfin_ret_1_conds st"
      using IH(4)
      by (subst rdc.DFS_skeleton_refine_unfin_simps(3)[OF IH(1) c])
         (simp add: rdc.DFS_skeleton_refine_unfin_ret1_def rcyc_on_empty_def)
    show ?case if c: "rdc.DFS_skeleton_refine_unfin_ret_2_conds st"
      using IH(4)
      by (subst rdc.DFS_skeleton_refine_unfin_simps(4)[OF IH(1) c])
         (auto simp: rdc.DFS_skeleton_refine_unfin_ret2_def rcyc_on_found_def rcyc_aux_invar_def
                     invar_ssf_def invar_fin_def invar_gray_def invar_gray_stack_def
                     invar_unfin_def invar_fin_unfin_def invar_seed_def invar_radj_def)
  qed
qed

section \<open>Level 2 against level 1\<close>

text \<open>The level-2 state record \<^emph>\<open>extends\<close> level 1's, so the projection that forgets \<open>adj\<close> is
  the record package's own \<open>truncate\<close>. The comparison is \<^emph>\<open>weaker\<close> than the prune-at-push
  variant's: the projection commutes with the whole run only while no back edge is adjacent to
  the stack --- which is every step of a clean run --- and on cyclic runs only the verdicts
  agree. Both facts rest on the same observation: a gray neighbour of a stack vertex is
  unfinished, so it stays in the carried neighbourhood of that vertex, which therefore can never
  be backtracked --- the run cannot end without reporting.\<close>

lemma truncate_sel[simp]:
  "stack (DFS_dircycle_linear_tracked_aux_state.truncate st) = stack st"
  "seen (DFS_dircycle_linear_tracked_aux_state.truncate st) = seen st"
  "finished (DFS_dircycle_linear_tracked_aux_state.truncate st) = finished st"
  "gray (DFS_dircycle_linear_tracked_aux_state.truncate st) = gray st"
  "unfinished (DFS_dircycle_linear_tracked_aux_state.truncate st) = unfinished st"
  "cycle (DFS_dircycle_linear_tracked_aux_state.truncate st) = cycle st"
  by (simp_all add: DFS_dircycle_linear_tracked_aux_state.truncate_def)

lemma truncate_invars[simp]:
  "dc.invar_1 (DFS_dircycle_linear_tracked_aux_state.truncate st) = rdc.invar_1 st"
  "dc.invar_seen_stack (DFS_dircycle_linear_tracked_aux_state.truncate st) = rdc.invar_seen_stack st"
  by (simp_all add: rdc.invar_1_def rdc.invar_seen_stack_def dc.invar_1_def dc.invar_seen_stack_def)

lemma truncate_cyc_found:
  "cyc_found (DFS_dircycle_linear_tracked_aux_state.truncate st)
     = (case stack st of [] \<Rightarrow> False
        | (v # stack_tl) \<Rightarrow> (((\<N>\<^sub>G v) \<inter>\<^sub>G (gray st)) \<noteq> \<emptyset>\<^sub>N))"
  by (cases "stack st") (simp_all add: cyc_found_def)

text \<open>With no gray neighbour at the top, the two searches read the same set: the carried
  neighbourhood is the \<open>G\<close>-neighbourhood minus finished, the tracked one is minus seen, and the
  difference --- the gray neighbours --- is empty.\<close>
lemma adj_nbr_eq_diff:
  assumes ia: "rdc.invar_adj st"
      and ax: "rcyc_aux_invar st"
      and i1: "rdc.invar_1 st"
      and nogray: "t_set (\<N>\<^sub>G v) \<inter> t_set (gray st) = {}"
  shows "t_set (Graph.neighbourhood (adj st) v) = t_set ((\<N>\<^sub>G v) -\<^sub>G (seen st))"
proof -
  have gs: "t_set (gray st) = set (stack st)"
    and fin_char: "t_set (finished st) = t_set (seen st) - set (stack st)"
    and sub: "set (stack st) \<subseteq> t_set (seen st)"
    using ax by (auto simp: rcyc_aux_invar_def invar_gray_stack_def invar_ssf_def)
  have nbr: "t_set (\<N>\<^sub>G v) = {w. (v, w) \<in> Graph.digraph_abs G}"
    by (simp add: dc.simps(1) neighbourhood_def)
  have "t_set (Graph.neighbourhood (adj st) v)
          = {w. (v, w) \<in> Graph.digraph_abs G} - t_set (finished st)"
    by (rule adj_nbr_set_fin[OF ia ax])
  also have "\<dots> = t_set (\<N>\<^sub>G v) - t_set (seen st)"
    using nogray gs fin_char sub nbr by auto
  also have "\<dots> = t_set ((\<N>\<^sub>G v) -\<^sub>G (seen st))"
    using i1 by (auto simp: rdc.invar_1_def elim!: invar_props_elims)
  finally show ?thesis .
qed

lemma diff_inv:
  assumes "rdc.invar_1 st"
  shows "vset_inv ((\<N>\<^sub>G v) -\<^sub>G (seen st))"
  using assms Graph.neighbourhood_invars'[of G v]
  by (auto simp: rdc.invar_1_def set_ops.invar_diff elim!: invar_props_elims)

subsection \<open>A back edge adjacent to the stack forces a report\<close>

text \<open>The witness: some stack vertex \<open>x\<close> has a \<open>G\<close>-neighbour among its stack ancestors ---
  itself included. A push extends the prefix; a backtrack pops a vertex strictly above \<open>x\<close>
  (popping \<open>x\<close> itself is impossible: the witness \<open>w\<close> is on the stack, hence unfinished, hence
  still in \<open>x\<close>'s carried neighbourhood, which a backtrack requires to be empty); an empty stack
  contradicts the witness; so the run ends at \<open>found\<close>, reporting.\<close>
definition "back_edge_wit st \<longleftrightarrow>
  (\<exists>pre x suf w. stack st = pre @ x # suf
     \<and> w \<in> t_set (\<N>\<^sub>G x) \<and> w \<in> set (x # suf))"

lemma back_edge_wit_forces_cycle:
  assumes dom: "rdc.DFS_skeleton_refine_unfin_dom st"
      and "rcyc_aux_invar st" "rdc.invar_adj st" "rdc.invar_1 st" "rdc.invar_seen_stack st"
      and "back_edge_wit st"
  shows "cycle (rdc.DFS_skeleton_refine_unfin st)"
  using assms(2-)
proof (induction rule: rdc.DFS_skeleton_refine_unfin_induct[OF dom])
  case IH: (1 st)
  from IH(8) obtain pre x suf w
    where wit: "stack st = pre @ x # suf" "w \<in> t_set (\<N>\<^sub>G x)" "w \<in> set (x # suf)"
    by (auto simp: back_edge_wit_def)
  show ?case
  proof (rule rdc.DFS_skeleton_refine_unfin_cases[where dfs_state = st])
    assume c: "rdc.DFS_skeleton_refine_unfin_call_1_conds st"
    let ?u = "sel (Graph.neighbourhood (adj st) (hd (stack st)))"
    have "stack (rdc.DFS_skeleton_refine_unfin_upd1 st) = (?u # pre) @ x # suf"
      by (simp add: refine_upd1_unfold wit(1))
    hence wit': "back_edge_wit (rdc.DFS_skeleton_refine_unfin_upd1 st)"
      using wit(2,3) unfolding back_edge_wit_def by blast
    show ?case
      using IH(2)[OF c rcyc_aux_invar_holds_upd1[OF c IH(4-7)]
                       rdc.refine_invar_adj_holds_1[OF c IH(4-7)]
                       rdc.refine_invar_1_holds_1[OF c IH(6)]
                       rdc.refine_invar_seen_stack_holds_1[OF c IH(4-7)] wit']
      by (simp add: rdc.DFS_skeleton_refine_unfin_simps(1)[OF IH(1) c])
  next
    assume c: "rdc.DFS_skeleton_refine_unfin_call_2_conds st"
    have ne_stack: "stack st \<noteq> []" and empty: "Graph.neighbourhood (adj st) (hd (stack st)) = \<emptyset>\<^sub>N"
      using c by (auto elim!: call_cond_elims)
    have gs: "t_set (gray st) = set (stack st)"
      and fin_char: "t_set (finished st) = t_set (seen st) - set (stack st)"
      using IH(4) by (auto simp: rcyc_aux_invar_def invar_gray_stack_def invar_ssf_def)
    have wstack: "w \<in> set (stack st)"
      using wit by auto
    have wnfin: "w \<notin> t_set (finished st)"
      using wstack fin_char by auto
    have "pre \<noteq> []"
    proof
      assume "pre = []"
      hence hx: "hd (stack st) = x" using wit(1) by simp
      have "w \<in> t_set (Graph.neighbourhood (adj st) x)"
        using wit(2) wnfin adj_nbr_set_fin[OF IH(5) IH(4)]
        by (auto simp: dc.simps(1))
      thus False using empty hx by simp
    qed
    then obtain p pre' where pre: "pre = p # pre'" by (cases pre) auto
    have "stack (rdc.DFS_skeleton_refine_unfin_upd2 st) = pre' @ x # suf"
      by (simp add: refine_upd2_unfold wit(1) pre)
    hence wit': "back_edge_wit (rdc.DFS_skeleton_refine_unfin_upd2 st)"
      using wit(2,3) unfolding back_edge_wit_def by blast
    show ?case
      using IH(3)[OF c rcyc_aux_invar_holds_upd2[OF c IH(4) IH(5) IH(6) IH(7)]
                       rdc.refine_invar_adj_holds_2[OF c IH(4) IH(5) IH(6) IH(7)]
                       rdc.refine_invar_1_holds_2[OF c IH(6)]
                       rdc.refine_invar_seen_stack_holds_2[OF c IH(6) IH(7)] wit']
      by (simp add: rdc.DFS_skeleton_refine_unfin_simps(2)[OF IH(1) c])
  next
    assume c: "rdc.DFS_skeleton_refine_unfin_ret_1_conds st"
    have "stack st = []" using c by (auto elim!: call_cond_elims)
    thus ?case using wit(1) by simp
  next
    assume c: "rdc.DFS_skeleton_refine_unfin_ret_2_conds st"
    show ?case
      by (subst rdc.DFS_skeleton_refine_unfin_simps(4)[OF IH(1) c])
         (simp add: rdc.DFS_skeleton_refine_unfin_ret2_def rcyc_on_found_def)
  qed
qed

text \<open>In particular: a gray neighbour of the \<^emph>\<open>top\<close> --- level 1's \<open>found\<close> --- forces a report
  here too, eventually.\<close>
lemma top_gray_nbr_forces_cycle:
  assumes dom: "rdc.DFS_skeleton_refine_unfin_dom st"
      and ax: "rcyc_aux_invar st"
      and ia: "rdc.invar_adj st"
      and i1: "rdc.invar_1 st"
      and iss: "rdc.invar_seen_stack st"
      and ne: "stack st \<noteq> []"
      and gray: "t_set (\<N>\<^sub>G (hd (stack st))) \<inter> t_set (gray st) \<noteq> {}"
  shows "cycle (rdc.DFS_skeleton_refine_unfin st)"
proof -
  have gs: "t_set (gray st) = set (stack st)"
    using ax by (auto simp: rcyc_aux_invar_def invar_gray_stack_def)
  obtain w where w: "w \<in> t_set (\<N>\<^sub>G (hd (stack st)))" "w \<in> set (stack st)"
    using gray gs by auto
  have cons: "stack st = [] @ hd (stack st) # tl (stack st)"
    using ne by simp
  have "back_edge_wit st"
    using w cons unfolding back_edge_wit_def by (metis append_Nil)
  thus ?thesis
    by (rule back_edge_wit_forces_cycle[OF dom ax ia i1 iss])
qed

subsection \<open>Clean runs are lockstep runs\<close>

text \<open>Two inductions of the same shape, differing in which side's cleanliness is assumed. In
  both, cleanliness rules out any gray neighbour at the top (on the refined side via
  \<open>top_gray_nbr_forces_cycle\<close>, on the tracked side because its \<open>found\<close> would have fired), so
  the two searches read the same element set, \<open>sel_cong\<close> aligns the choice, and the step
  commutes with the projection.\<close>

theorem refine_run_agree_of_tracked_clean:
  assumes dom: "rdc.DFS_skeleton_refine_unfin_dom st"
      and "rcyc_aux_invar st" "rdc.invar_adj st" "rdc.invar_1 st" "rdc.invar_seen_stack st"
      and "\<not> cycle (dc.DFS_skeleton (DFS_dircycle_linear_tracked_aux_state.truncate st))"
  shows "DFS_dircycle_linear_tracked_aux_state.truncate (rdc.DFS_skeleton_refine_unfin st)
           = dc.DFS_skeleton (DFS_dircycle_linear_tracked_aux_state.truncate st)"
  using assms(2-)
proof (induction rule: rdc.DFS_skeleton_refine_unfin_induct[OF dom])
  case IH: (1 st)
  let ?T = "DFS_dircycle_linear_tracked_aux_state.truncate
              :: ('v,'vset,'adjmap) DFS_dircycle_linear_tracked_aux_refine_state
                   \<Rightarrow> ('v,'vset) DFS_dircycle_linear_tracked_aux_state"
  have t1: "dc.invar_1 (?T st)" using IH(6) by simp
  have t2: "dc.invar_seen_stack (?T st)" using IH(7) by simp
  have tdom: "dc.DFS_skeleton_dom (?T st)"
    by (rule dc.DFS_skeleton_terminates[OF t1 t2])
  note tsimps = dc.DFS_skeleton_simps[OF tdom]
  show ?case
  proof (cases "stack st")
    case Nil
    hence r: "rdc.DFS_skeleton_refine_unfin_ret_1_conds st"
      and tr: "dc.DFS_skeleton_ret_1_conds (?T st)"
      by (auto simp: rdc.DFS_skeleton_refine_unfin_ret_1_conds_def dc.DFS_skeleton_ret_1_conds_def)
    show ?thesis
      by (subst rdc.DFS_skeleton_refine_unfin_simps(3)[OF IH(1) r], subst tsimps(3)[OF tr])
         (simp add: rdc.DFS_skeleton_refine_unfin_ret1_def dc.DFS_skeleton_ret1_def
                    rcyc_on_empty_def cyc_on_empty_def)
  next
    case (Cons v stack_tl)
    have nogray: "t_set (\<N>\<^sub>G v) \<inter> t_set (gray st) = {}"
    proof (rule ccontr)
      assume "t_set (\<N>\<^sub>G v) \<inter> t_set (gray st) \<noteq> {}"
      hence "t_set ((\<N>\<^sub>G v) \<inter>\<^sub>G (gray st)) \<noteq> {}"
        using IH(4) dc.graph_inv
        by (auto simp: rcyc_aux_invar_def invar_gray_def)
      hence "((\<N>\<^sub>G v) \<inter>\<^sub>G (gray st)) \<noteq> \<emptyset>\<^sub>N"
        by auto
      hence "cyc_found (?T st)"
        using Cons by (simp add: truncate_cyc_found)
      hence "dc.DFS_skeleton_ret_2_conds (?T st)"
        using Cons by (auto simp: dc.DFS_skeleton_ret_2_conds_def)
      hence "cycle (dc.DFS_skeleton (?T st))"
        by (simp add: tsimps(4) dc.DFS_skeleton_ret2_def cyc_on_found_def)
      thus False using IH(8) by simp
    qed
    have ncf: "\<not> cyc_found (?T st)"
    proof -
      have "((\<N>\<^sub>G v) \<inter>\<^sub>G (gray st)) = \<emptyset>\<^sub>N"
        using nogray IH(4) dc.graph_inv
        by (intro vset_empty_of_t_set)
           (auto simp: rcyc_aux_invar_def invar_gray_def)
      thus ?thesis using Cons by (simp add: truncate_cyc_found)
    qed
    have set_eq: "t_set (Graph.neighbourhood (adj st) v) = t_set ((\<N>\<^sub>G v) -\<^sub>G (seen st))"
      using adj_nbr_eq_diff[OF IH(5) IH(4) IH(6) nogray] .
    have inv_adjnbr: "vset_inv (Graph.neighbourhood (adj st) v)"
      using rdc.adj_nbr_inv[OF IH(5)] by simp
    have inv_diff: "vset_inv ((\<N>\<^sub>G v) -\<^sub>G (seen st))"
      by (rule diff_inv[OF IH(6)])
    have ne_eq: "(Graph.neighbourhood (adj st) v \<noteq> \<emptyset>\<^sub>N) = (((\<N>\<^sub>G v) -\<^sub>G (seen st)) \<noteq> \<emptyset>\<^sub>N)"
      by (rule rdc.vset_ne_cong[OF inv_adjnbr inv_diff set_eq])
    have nrf: "\<not> rcyc_found st"
    proof (cases "Graph.neighbourhood (adj st) v = \<emptyset>\<^sub>N")
      case True
      thus ?thesis using Cons by (simp add: rcyc_found_def)
    next
      case False
      have "sel (Graph.neighbourhood (adj st) v) \<in> t_set (Graph.neighbourhood (adj st) v)"
        by (rule Graph.vset.choose'[OF False inv_adjnbr])
      hence "sel (Graph.neighbourhood (adj st) v) \<notin> t_set (gray st)"
        using set_eq nogray dc.simps(1) IH(6)
        by (auto simp: rdc.invar_1_def elim!: invar_props_elims)
      thus ?thesis
        using Cons IH(4)
        by (auto simp: rcyc_found_def rcyc_aux_invar_def invar_gray_def
                       Graph.vset.set.set_isin
                 elim!: invar_props_elims)
    qed
    show ?thesis
    proof (cases "Graph.neighbourhood (adj st) v = \<emptyset>\<^sub>N")
      case False
      have c: "rdc.DFS_skeleton_refine_unfin_call_1_conds st"
        using Cons False nrf by (auto simp: rdc.DFS_skeleton_refine_unfin_call_1_conds_def)
      have tc: "dc.DFS_skeleton_call_1_conds (?T st)"
        using Cons False ncf ne_eq by (auto simp: dc.DFS_skeleton_call_1_conds_def)
      have sel_eq: "sel (Graph.neighbourhood (adj st) v) = sel ((\<N>\<^sub>G v) -\<^sub>G (seen st))"
        by (rule sel_cong[OF inv_adjnbr inv_diff set_eq])
      have step: "?T (rdc.DFS_skeleton_refine_unfin_upd1 st) = dc.DFS_skeleton_upd1 (?T st)"
        using Cons sel_eq
        by (simp add: DFS_dircycle_linear_tracked_aux_state.truncate_def refine_upd1_unfold
                      upd1_unfold)
      have clean': "\<not> cycle (dc.DFS_skeleton (?T (rdc.DFS_skeleton_refine_unfin_upd1 st)))"
        using IH(8) by (simp add: step tsimps(1)[OF tc, symmetric])
      have "?T (rdc.DFS_skeleton_refine_unfin (rdc.DFS_skeleton_refine_unfin_upd1 st))
              = dc.DFS_skeleton (?T (rdc.DFS_skeleton_refine_unfin_upd1 st))"
        by (rule IH(2)[OF c rcyc_aux_invar_holds_upd1[OF c IH(4-7)]
                            rdc.refine_invar_adj_holds_1[OF c IH(4-7)]
                            rdc.refine_invar_1_holds_1[OF c IH(6)]
                            rdc.refine_invar_seen_stack_holds_1[OF c IH(4-7)] clean'])
      thus ?thesis
        by (simp add: rdc.DFS_skeleton_refine_unfin_simps(1)[OF IH(1) c] tsimps(1)[OF tc] step)
    next
      case True
      have c: "rdc.DFS_skeleton_refine_unfin_call_2_conds st"
        using Cons True nrf by (auto simp: rdc.DFS_skeleton_refine_unfin_call_2_conds_def)
      have tc: "dc.DFS_skeleton_call_2_conds (?T st)"
        using Cons True ncf ne_eq by (auto simp: dc.DFS_skeleton_call_2_conds_def)
      have step: "?T (rdc.DFS_skeleton_refine_unfin_upd2 st) = dc.DFS_skeleton_upd2 (?T st)"
        using Cons
        by (simp add: DFS_dircycle_linear_tracked_aux_state.truncate_def refine_upd2_unfold
                      upd2_unfold)
      have clean': "\<not> cycle (dc.DFS_skeleton (?T (rdc.DFS_skeleton_refine_unfin_upd2 st)))"
        using IH(8) by (simp add: step tsimps(2)[OF tc, symmetric])
      have "?T (rdc.DFS_skeleton_refine_unfin (rdc.DFS_skeleton_refine_unfin_upd2 st))
              = dc.DFS_skeleton (?T (rdc.DFS_skeleton_refine_unfin_upd2 st))"
        by (rule IH(3)[OF c rcyc_aux_invar_holds_upd2[OF c IH(4) IH(5) IH(6) IH(7)]
                            rdc.refine_invar_adj_holds_2[OF c IH(4) IH(5) IH(6) IH(7)]
                            rdc.refine_invar_1_holds_2[OF c IH(6)]
                            rdc.refine_invar_seen_stack_holds_2[OF c IH(6) IH(7)] clean'])
      thus ?thesis
        by (simp add: rdc.DFS_skeleton_refine_unfin_simps(2)[OF IH(1) c] tsimps(2)[OF tc] step)
    qed
  qed
qed

theorem refine_run_agree_of_refine_clean:
  assumes dom: "rdc.DFS_skeleton_refine_unfin_dom st"
      and "rcyc_aux_invar st" "rdc.invar_adj st" "rdc.invar_1 st" "rdc.invar_seen_stack st"
      and "\<not> cycle (rdc.DFS_skeleton_refine_unfin st)"
  shows "DFS_dircycle_linear_tracked_aux_state.truncate (rdc.DFS_skeleton_refine_unfin st)
           = dc.DFS_skeleton (DFS_dircycle_linear_tracked_aux_state.truncate st)"
  using assms(2-)
proof (induction rule: rdc.DFS_skeleton_refine_unfin_induct[OF dom])
  case IH: (1 st)
  let ?T = "DFS_dircycle_linear_tracked_aux_state.truncate
              :: ('v,'vset,'adjmap) DFS_dircycle_linear_tracked_aux_refine_state
                   \<Rightarrow> ('v,'vset) DFS_dircycle_linear_tracked_aux_state"
  have t1: "dc.invar_1 (?T st)" using IH(6) by simp
  have t2: "dc.invar_seen_stack (?T st)" using IH(7) by simp
  have tdom: "dc.DFS_skeleton_dom (?T st)"
    by (rule dc.DFS_skeleton_terminates[OF t1 t2])
  note tsimps = dc.DFS_skeleton_simps[OF tdom]
  show ?case
  proof (cases "stack st")
    case Nil
    hence r: "rdc.DFS_skeleton_refine_unfin_ret_1_conds st"
      and tr: "dc.DFS_skeleton_ret_1_conds (?T st)"
      by (auto simp: rdc.DFS_skeleton_refine_unfin_ret_1_conds_def dc.DFS_skeleton_ret_1_conds_def)
    show ?thesis
      by (subst rdc.DFS_skeleton_refine_unfin_simps(3)[OF IH(1) r], subst tsimps(3)[OF tr])
         (simp add: rdc.DFS_skeleton_refine_unfin_ret1_def dc.DFS_skeleton_ret1_def
                    rcyc_on_empty_def cyc_on_empty_def)
  next
    case (Cons v stack_tl)
    have nogray: "t_set (\<N>\<^sub>G v) \<inter> t_set (gray st) = {}"
    proof (rule ccontr)
      assume "t_set (\<N>\<^sub>G v) \<inter> t_set (gray st) \<noteq> {}"
      hence "cycle (rdc.DFS_skeleton_refine_unfin st)"
        using Cons by (intro top_gray_nbr_forces_cycle[OF IH(1) IH(4-7)]) auto
      thus False using IH(8) by simp
    qed
    have ncf: "\<not> cyc_found (?T st)"
    proof -
      have "((\<N>\<^sub>G v) \<inter>\<^sub>G (gray st)) = \<emptyset>\<^sub>N"
        using nogray IH(4) dc.graph_inv
        by (intro vset_empty_of_t_set)
           (auto simp: rcyc_aux_invar_def invar_gray_def)
      thus ?thesis using Cons by (simp add: truncate_cyc_found)
    qed
    have set_eq: "t_set (Graph.neighbourhood (adj st) v) = t_set ((\<N>\<^sub>G v) -\<^sub>G (seen st))"
      using adj_nbr_eq_diff[OF IH(5) IH(4) IH(6) nogray] .
    have inv_adjnbr: "vset_inv (Graph.neighbourhood (adj st) v)"
      using rdc.adj_nbr_inv[OF IH(5)] by simp
    have inv_diff: "vset_inv ((\<N>\<^sub>G v) -\<^sub>G (seen st))"
      by (rule diff_inv[OF IH(6)])
    have ne_eq: "(Graph.neighbourhood (adj st) v \<noteq> \<emptyset>\<^sub>N) = (((\<N>\<^sub>G v) -\<^sub>G (seen st)) \<noteq> \<emptyset>\<^sub>N)"
      by (rule rdc.vset_ne_cong[OF inv_adjnbr inv_diff set_eq])
    have nrf: "\<not> rcyc_found st"
    proof (cases "Graph.neighbourhood (adj st) v = \<emptyset>\<^sub>N")
      case True
      thus ?thesis using Cons by (simp add: rcyc_found_def)
    next
      case False
      have "sel (Graph.neighbourhood (adj st) v) \<in> t_set (Graph.neighbourhood (adj st) v)"
        by (rule Graph.vset.choose'[OF False inv_adjnbr])
      hence "sel (Graph.neighbourhood (adj st) v) \<notin> t_set (gray st)"
        using set_eq nogray dc.simps(1) IH(6)
        by (auto simp: rdc.invar_1_def elim!: invar_props_elims)
      thus ?thesis
        using Cons IH(4)
        by (auto simp: rcyc_found_def rcyc_aux_invar_def invar_gray_def
                       Graph.vset.set.set_isin
                 elim!: invar_props_elims)
    qed
    show ?thesis
    proof (cases "Graph.neighbourhood (adj st) v = \<emptyset>\<^sub>N")
      case False
      have c: "rdc.DFS_skeleton_refine_unfin_call_1_conds st"
        using Cons False nrf by (auto simp: rdc.DFS_skeleton_refine_unfin_call_1_conds_def)
      have tc: "dc.DFS_skeleton_call_1_conds (?T st)"
        using Cons False ncf ne_eq by (auto simp: dc.DFS_skeleton_call_1_conds_def)
      have sel_eq: "sel (Graph.neighbourhood (adj st) v) = sel ((\<N>\<^sub>G v) -\<^sub>G (seen st))"
        by (rule sel_cong[OF inv_adjnbr inv_diff set_eq])
      have step: "?T (rdc.DFS_skeleton_refine_unfin_upd1 st) = dc.DFS_skeleton_upd1 (?T st)"
        using Cons sel_eq
        by (simp add: DFS_dircycle_linear_tracked_aux_state.truncate_def refine_upd1_unfold
                      upd1_unfold)
      have clean': "\<not> cycle (rdc.DFS_skeleton_refine_unfin (rdc.DFS_skeleton_refine_unfin_upd1 st))"
        using IH(8) by (simp add: rdc.DFS_skeleton_refine_unfin_simps(1)[OF IH(1) c, symmetric])
      have "?T (rdc.DFS_skeleton_refine_unfin (rdc.DFS_skeleton_refine_unfin_upd1 st))
              = dc.DFS_skeleton (?T (rdc.DFS_skeleton_refine_unfin_upd1 st))"
        by (rule IH(2)[OF c rcyc_aux_invar_holds_upd1[OF c IH(4-7)]
                            rdc.refine_invar_adj_holds_1[OF c IH(4-7)]
                            rdc.refine_invar_1_holds_1[OF c IH(6)]
                            rdc.refine_invar_seen_stack_holds_1[OF c IH(4-7)] clean'])
      thus ?thesis
        by (simp add: rdc.DFS_skeleton_refine_unfin_simps(1)[OF IH(1) c] tsimps(1)[OF tc] step)
    next
      case True
      have c: "rdc.DFS_skeleton_refine_unfin_call_2_conds st"
        using Cons True nrf by (auto simp: rdc.DFS_skeleton_refine_unfin_call_2_conds_def)
      have tc: "dc.DFS_skeleton_call_2_conds (?T st)"
        using Cons True ncf ne_eq by (auto simp: dc.DFS_skeleton_call_2_conds_def)
      have step: "?T (rdc.DFS_skeleton_refine_unfin_upd2 st) = dc.DFS_skeleton_upd2 (?T st)"
        using Cons
        by (simp add: DFS_dircycle_linear_tracked_aux_state.truncate_def refine_upd2_unfold
                      upd2_unfold)
      have clean': "\<not> cycle (rdc.DFS_skeleton_refine_unfin (rdc.DFS_skeleton_refine_unfin_upd2 st))"
        using IH(8) by (simp add: rdc.DFS_skeleton_refine_unfin_simps(2)[OF IH(1) c, symmetric])
      have "?T (rdc.DFS_skeleton_refine_unfin (rdc.DFS_skeleton_refine_unfin_upd2 st))
              = dc.DFS_skeleton (?T (rdc.DFS_skeleton_refine_unfin_upd2 st))"
        by (rule IH(3)[OF c rcyc_aux_invar_holds_upd2[OF c IH(4) IH(5) IH(6) IH(7)]
                            rdc.refine_invar_adj_holds_2[OF c IH(4) IH(5) IH(6) IH(7)]
                            rdc.refine_invar_1_holds_2[OF c IH(6)]
                            rdc.refine_invar_seen_stack_holds_2[OF c IH(6) IH(7)] clean'])
      thus ?thesis
        by (simp add: rdc.DFS_skeleton_refine_unfin_simps(2)[OF IH(1) c] tsimps(2)[OF tc] step)
    qed
  qed
qed

subsection \<open>The verdicts agree, unconditionally\<close>

lemma truncate_initial:
  "DFS_dircycle_linear_tracked_aux_state.truncate dircycle_refine_initial_state
     = dircycle_tracked_initial_state"
  by (simp add: DFS_dircycle_linear_tracked_aux_state.truncate_def
                dircycle_refine_initial_state_def dircycle_tracked_initial_state_def)

theorem dircycle_refine_verdict:
  "cycle dircycle_refine_result = cycle dircycle_tracked_result"
proof (cases "cycle dircycle_refine_result")
  case False
  have "DFS_dircycle_linear_tracked_aux_state.truncate dircycle_refine_result
          = dircycle_tracked_result"
    using refine_run_agree_of_refine_clean[OF dircycle_refine_initial_dom
            initial_refine_aux_invar initial_refine_invar_adj initial_refine_invars False]
    by (simp add: truncate_initial)
  thus ?thesis using False by (metis truncate_sel(6))
next
  case True
  show ?thesis
  proof (rule ccontr)
    assume "cycle dircycle_refine_result \<noteq> cycle dircycle_tracked_result"
    hence ntc: "\<not> cycle dircycle_tracked_result" using True by simp
    have "DFS_dircycle_linear_tracked_aux_state.truncate dircycle_refine_result
            = dircycle_tracked_result"
      using refine_run_agree_of_tracked_clean[OF dircycle_refine_initial_dom
              initial_refine_aux_invar initial_refine_invar_adj initial_refine_invars]
            ntc
      by (simp add: truncate_initial)
    hence "cycle dircycle_refine_result = cycle dircycle_tracked_result"
      by (metis truncate_sel(6))
    thus False using True ntc by simp
  qed
qed

subsection \<open>What one clean run exports\<close>

text \<open>On a clean run the refined result \<^emph>\<open>is\<close> the tracked result under the projection ---
  everything level 1 exports (finished/unfinished vsets, root membership, acyclicity of the
  finished region) transfers verbatim, conditioned on the verdict. The outer sweep reads the
  finished/unfinished sets only in its recursive branch, i.e.\ exactly when the verdict is
  clean.\<close>

theorem dircycle_refine_agrees_tracked_clean:
  assumes "\<not> cycle dircycle_refine_result"
  shows "DFS_dircycle_linear_tracked_aux_state.truncate dircycle_refine_result
           = dircycle_tracked_result"
  using refine_run_agree_of_refine_clean[OF dircycle_refine_initial_dom
          initial_refine_aux_invar initial_refine_invar_adj initial_refine_invars assms]
  by (simp add: truncate_initial)

corollary dircycle_refine_components:
  assumes "\<not> cycle dircycle_refine_result"
  shows "stack dircycle_refine_result = stack dircycle_tracked_result"
    and "seen dircycle_refine_result = seen dircycle_tracked_result"
    and "finished dircycle_refine_result = finished dircycle_tracked_result"
    and "gray dircycle_refine_result = gray dircycle_tracked_result"
    and "unfinished dircycle_refine_result = unfinished dircycle_tracked_result"
  using arg_cong[where f = stack, OF dircycle_refine_agrees_tracked_clean[OF assms]]
  using arg_cong[where f = seen, OF dircycle_refine_agrees_tracked_clean[OF assms]]
  using arg_cong[where f = finished, OF dircycle_refine_agrees_tracked_clean[OF assms]]
  using arg_cong[where f = gray, OF dircycle_refine_agrees_tracked_clean[OF assms]]
  using arg_cong[where f = unfinished, OF dircycle_refine_agrees_tracked_clean[OF assms]]
  by simp_all

subsection \<open>The carried graph at the end of the run\<close>

text \<open>Unlike the prune-at-push variant, the map's relation to the \<^emph>\<open>finished\<close> region is an
  invariant of every state, so the export needs no clean-run detour: the run hands back \<open>G\<close>
  minus the in-edges of whatever it finished, cycle or not. (The outer sweep still only consumes
  it on clean runs.)\<close>

lemma dircycle_refine_invar_adj: "rdc.invar_adj dircycle_refine_result"
  by (rule rdc.refine_invar_adj_holds[OF dircycle_refine_initial_dom initial_refine_aux_invar
             initial_refine_invar_adj initial_refine_invars])

lemma dircycle_refine_aux_invar: "rcyc_aux_invar dircycle_refine_result"
  by (rule rcyc_aux_invar_holds[OF dircycle_refine_initial_dom initial_refine_aux_invar
             initial_refine_invar_adj initial_refine_invars])

lemma dircycle_refine_adj_graph_inv: "Graph.graph_inv (adj dircycle_refine_result)"
  using dircycle_refine_invar_adj by (simp add: rdc.invar_adj_def)

lemma dircycle_refine_adj_abs_finished:
  "Graph.digraph_abs (adj dircycle_refine_result)
     = Graph.digraph_abs G - (UNIV \<times> t_set (finished dircycle_refine_result))"
proof -
  have "t_set (finished dircycle_refine_result)
          = t_set (seen dircycle_refine_result) - set (stack dircycle_refine_result)"
    using dircycle_refine_aux_invar
    by (auto simp: rcyc_aux_invar_def invar_ssf_def)
  thus ?thesis
    using dircycle_refine_invar_adj by (simp add: rdc.invar_adj_def)
qed

text \<open>And the reverse map alongside: still the exact inverse of the carried map --- which,
  with the previous export, is the \<open>RA\<close> contract of the \<^emph>\<open>next\<close> call for the enlarged
  finished region. Like the \<open>adj\<close> exports, unconditional.\<close>

lemma dircycle_refine_radj_graph_inv: "Graph.graph_inv (radj dircycle_refine_result)"
  using dircycle_refine_aux_invar by (auto simp: rcyc_aux_invar_def invar_radj_def)

lemma dircycle_refine_radj_abs:
  "Graph.digraph_abs (radj dircycle_refine_result)
     = {(u, p). (p, u) \<in> Graph.digraph_abs (adj dircycle_refine_result)}"
  using dircycle_refine_aux_invar by (auto simp: rcyc_aux_invar_def invar_radj_def)

end

end

end
