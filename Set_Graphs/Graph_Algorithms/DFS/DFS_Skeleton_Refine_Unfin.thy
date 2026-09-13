theory DFS_Skeleton_Refine_Unfin
  imports DFS_Skeleton
begin

text \<open>A refinement of \<^locale>\<open>DFS_skeleton\<close> that removes the set difference from the search's
  inner loop.

  \<^bold>\<open>The cost being removed.\<close> Both the library skeleton and \<^locale>\<open>DFS_skeleton\<close> pick the next
  vertex with \<open>(\<N>\<^sub>G v) -\<^sub>G (seen dfs_state)\<close>, and they evaluate that expression \<^emph>\<open>twice\<close> per
  step --- once for the emptiness test, once inside the \<open>sel\<close>. It is recomputed from scratch on
  every iteration, so a vertex of out-degree \<open>d\<close> performs \<open>d+1\<close> differences over its own
  neighbourhood before it is exhausted. At the red-black-tree instantiation \<open>-\<^sub>G\<close> is
  \<open>RBT.diff\<close>, the join/split-based difference, whose cost scales with \<^emph>\<open>both\<close> operands rather
  than with the neighbourhood alone.

  \<^bold>\<open>The refinement.\<close> Carry the graph itself in the state --- \<open>adjmap\<close> below is a selector into
  the extensible \<open>'more\<close> slot --- and have \<open>on_backtrack v\<close> delete every edge \<^emph>\<open>entering\<close> \<open>v\<close>
  when \<open>v\<close> is \<^emph>\<open>finished\<close>. The state's adjacency map then offers exactly the \<^emph>\<open>unfinished\<close>
  out-neighbours --- the unseen ones plus those still on the stack --- and the loop reads a plain
  neighbourhood: \<open>(\<N> (adjmap st) v) \<noteq> \<emptyset>\<^sub>N\<close> and \<open>sel (\<N> (adjmap st) v)\<close>. This is the
  invariant \<open>invar_adj\<close>:
  \<open>[adjmap st]\<^sub>g = [G]\<^sub>g - (UNIV \<times> (t_set (seen st) - set (stack st)))\<close>.

  \<^bold>\<open>Pruning at backtrack, not at push.\<close> Pruning the in-edges of a vertex when it is \<^emph>\<open>pushed\<close>
  --- the sibling refinement \<open>DFS_Skeleton_Refine\<close> (a sibling, not an ancestor, so named in
  prose), which this theory does not replace --- makes the map track \<open>seen\<close> and the refined
  loop lockstep-equal to
  \<open>DFS_skeleton\<close> --- but it also deletes precisely the back edges, so an instance that needs
  them (directed cycle detection) must re-read the original \<open>G\<close> at every step, at \<open>O(deg v)\<close>
  a step. Pruning at
  \<^emph>\<open>backtrack\<close> keeps the edges into on-stack vertices available: the selected next vertex is
  either unseen (descend) or on the stack (for a cycle search: a back edge, detected by one \<open>O(1)\<close>
  membership in \<open>found\<close>). The price is the crux of this locale: the offered set \<^emph>\<open>does\<close> contain
  on-stack vertices, so pushing \<open>sel (\<N> (adjmap st) v)\<close> is sound only if the instance's
  \<open>found\<close> fires first. That is the obligation \<open>sel_unseen\<close> below: whenever the descend branch is
  taken (\<open>\<not> found\<close>, non-empty neighbourhood), the selected vertex is unseen. It cannot be proved
  generically --- it is exactly the discipline the instance's \<open>found\<close> must enforce --- and it is
  what makes the structural invariants and termination go through.

  \<^bold>\<open>No lockstep equivalence with \<open>DFS_skeleton\<close>.\<close> The plain skeleton selects from
  \<open>(\<N>\<^sub>G v) -\<^sub>G (seen st)\<close>, this loop from the unfinished neighbours --- the two sets differ by
  the on-stack neighbours, so the runs diverge in general and no run-equality is stated here
  (hence also no \<open>sel_cong\<close> assumption; an instance that proves a run-level relation to another
  search assumes what it needs itself). Instead the reasoning layer proves, directly against the
  refined loop: preservation of \<open>invar_1\<close>, \<open>invar_seen_stack\<close>, \<open>invar_adj\<close> and an
  instance-supplied invariant \<open>aux_invar\<close> (the vehicle by which the instance's \<open>found\<close>
  discipline enters \<open>sel_unseen\<close>), and termination by the plain skeleton's own measure.

  \<^bold>\<open>How an instance deletes in-edges.\<close> The locale says only what the backtrack step must
  \<^emph>\<open>achieve\<close>, not how. That matters, because \<open>Pair_Graph_Specs.delete_edge\<close> is keyed by an
  edge's \<^emph>\<open>source\<close>, so deleting the in-edges of \<open>v\<close> means knowing \<open>v\<close>'s predecessors. An
  instance should carry a \<^emph>\<open>reverse adjacency map in the state\<close>, kept the exact inverse of the
  carried map by its \<open>aux_invar\<close>: the backtrack reads the popped vertex's predecessor row and
  then drops that row, so each vertex's row is walked at most once, the total deletion work is
  one pass over the edges, and the search stays linear. Instantiating instead by scanning every
  vertex's neighbour set per backtrack costs \<open>O(V)\<close> a step --- exactly the price this
  refinement exists to remove.\<close>

text \<open>The inherited parameters are re-declared in the \<open>for\<close> clause purely to \<^emph>\<open>name\<close> the type
  variables, so that \<open>adjmap\<close>'s type can be tied to the same \<open>'adjmap\<close> as \<open>lookup\<close>'s and the same
  state scheme as the callbacks'. Written as a bare \<open>DFS_skeleton + fixes adjmap :: \<dots>\<close> the type
  variables in the new \<open>fixes\<close> would be fresh, and nothing would connect them to the inherited
  ones.\<close>

locale DFS_skeleton_refine_unfin =
  DFS_skeleton where lookup = lookup and on_push = on_push
  for lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option"
  and on_push :: "'v \<Rightarrow> ('v,'vset,'more) DFS_skeleton_state_scheme
                     \<Rightarrow> ('v,'vset,'more) DFS_skeleton_state_scheme" +
  fixes adjmap :: "('v,'vset,'more) DFS_skeleton_state_scheme \<Rightarrow> 'adjmap"
begin

abbreviation adj_nbr :: "('v,'vset,'more) DFS_skeleton_state_scheme \<Rightarrow> 'v \<Rightarrow> 'vset" where
  "adj_nbr st v \<equiv> Graph.neighbourhood (adjmap st) v"

subsection \<open>The refined search\<close>

text \<open>Identical to \<open>DFS_skeleton\<close> except that the unexplored neighbours are read off the
  state's own adjacency map instead of being recomputed as a difference.\<close>

function (domintros) DFS_skeleton_refine_unfin::
  "('v,'vset,'more) DFS_skeleton_state_scheme \<Rightarrow> ('v,'vset,'more) DFS_skeleton_state_scheme" where
  "DFS_skeleton_refine_unfin dfs_state =
     (case (stack dfs_state) of (v # stack_tl) \<Rightarrow>
       (if found dfs_state then on_found dfs_state
        else (if adj_nbr dfs_state v \<noteq> \<emptyset>\<^sub>N then
                let u = sel (adj_nbr dfs_state v);
                    stack' = u # (stack dfs_state);
                    seen' = insert u (seen dfs_state)
                in DFS_skeleton_refine_unfin (on_push u (dfs_state \<lparr>stack := stack', seen := seen'\<rparr>))
              else
                DFS_skeleton_refine_unfin (on_backtrack v (dfs_state \<lparr>stack := stack_tl\<rparr>))))
     | _ \<Rightarrow> on_empty dfs_state)"
  by pat_completeness auto

partial_function (tailrec) DFS_skeleton_refine_unfin_impl::
  "('v,'vset,'more) DFS_skeleton_state_scheme \<Rightarrow> ('v,'vset,'more) DFS_skeleton_state_scheme" where
  "DFS_skeleton_refine_unfin_impl dfs_state =
     (case (stack dfs_state) of (v # stack_tl) \<Rightarrow>
       (if found dfs_state then on_found dfs_state
        else (if adj_nbr dfs_state v \<noteq> \<emptyset>\<^sub>N then
                let u = sel (adj_nbr dfs_state v);
                    stack' = u # (stack dfs_state);
                    seen' = insert u (seen dfs_state)
                in DFS_skeleton_refine_unfin_impl (on_push u (dfs_state \<lparr>stack := stack', seen := seen'\<rparr>))
              else
                DFS_skeleton_refine_unfin_impl (on_backtrack v (dfs_state \<lparr>stack := stack_tl\<rparr>))))
     | _ \<Rightarrow> on_empty dfs_state)"

lemmas [code] = DFS_skeleton_refine_unfin_impl.simps

lemma DFS_skeleton_refine_unfin_impl_same:
  assumes "DFS_skeleton_refine_unfin_dom state"
  shows   "DFS_skeleton_refine_unfin_impl state = DFS_skeleton_refine_unfin state"
  by(induction rule: DFS_skeleton_refine_unfin.pinduct[OF assms])
    (subst DFS_skeleton_refine_unfin.psimps, simp, subst DFS_skeleton_refine_unfin_impl.simps,
     auto split: list.split if_split simp add: Let_def)

subsection \<open>Call conditions\<close>

definition "DFS_skeleton_refine_unfin_call_1_conds dfs_state =
    (case (stack dfs_state) of (v # stack_tl) \<Rightarrow>
       (if found dfs_state then False
        else (if adj_nbr dfs_state v \<noteq> \<emptyset>\<^sub>N then True else False))
     | _ \<Rightarrow> False)"

lemma DFS_skeleton_refine_unfin_call_1_conds[call_cond_elims]:
  "DFS_skeleton_refine_unfin_call_1_conds dfs_state \<Longrightarrow>
   \<lbrakk>\<lbrakk>\<exists>v stack_tl. stack dfs_state = v # stack_tl;
    \<not> found dfs_state;
    adj_nbr dfs_state (hd (stack dfs_state)) \<noteq> \<emptyset>\<^sub>N\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto simp: DFS_skeleton_refine_unfin_call_1_conds_def split: list.splits option.splits if_splits)

definition "DFS_skeleton_refine_unfin_upd1 dfs_state = (
    let
      u = sel (adj_nbr dfs_state (hd (stack dfs_state)));
      stack' = u # (stack dfs_state);
      seen' = insert u (seen dfs_state)
    in
      on_push u (dfs_state \<lparr>stack := stack', seen := seen'\<rparr>))"

definition "DFS_skeleton_refine_unfin_call_2_conds dfs_state =
    (case (stack dfs_state) of (v # stack_tl) \<Rightarrow>
       (if found dfs_state then False
        else (if adj_nbr dfs_state v \<noteq> \<emptyset>\<^sub>N then False else True))
     | _ \<Rightarrow> False)"

lemma DFS_skeleton_refine_unfin_call_2_conds[call_cond_elims]:
  "DFS_skeleton_refine_unfin_call_2_conds dfs_state \<Longrightarrow>
   \<lbrakk>\<lbrakk>\<exists>v stack_tl. stack dfs_state = v # stack_tl;
    \<not> found dfs_state;
    adj_nbr dfs_state (hd (stack dfs_state)) = \<emptyset>\<^sub>N\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto simp: DFS_skeleton_refine_unfin_call_2_conds_def split: list.splits option.splits if_splits)

definition "DFS_skeleton_refine_unfin_upd2 dfs_state =
  on_backtrack (hd (stack dfs_state)) (dfs_state \<lparr>stack := tl (stack dfs_state)\<rparr>)"

definition "DFS_skeleton_refine_unfin_ret_1_conds dfs_state =
    (case (stack dfs_state) of (v # stack_tl) \<Rightarrow> False | _ \<Rightarrow> True)"

lemma DFS_skeleton_refine_unfin_ret_1_conds[call_cond_elims]:
  "DFS_skeleton_refine_unfin_ret_1_conds dfs_state \<Longrightarrow> \<lbrakk>\<lbrakk>stack dfs_state = []\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto simp: DFS_skeleton_refine_unfin_ret_1_conds_def split: list.splits if_splits)

lemma DFS_skeleton_refine_unfin_ret_1_condsI[call_cond_intros]:
  "\<lbrakk>stack dfs_state = []\<rbrakk> \<Longrightarrow> DFS_skeleton_refine_unfin_ret_1_conds dfs_state"
  by(auto simp: DFS_skeleton_refine_unfin_ret_1_conds_def split: list.splits if_splits)

definition "DFS_skeleton_refine_unfin_ret1 dfs_state = on_empty dfs_state"

definition "DFS_skeleton_refine_unfin_ret_2_conds dfs_state =
    (case (stack dfs_state) of (v # stack_tl) \<Rightarrow>
       (if found dfs_state then True else False)
     | _ \<Rightarrow> False)"

lemma DFS_skeleton_refine_unfin_ret_2_conds[call_cond_elims]:
  "DFS_skeleton_refine_unfin_ret_2_conds dfs_state \<Longrightarrow>
   \<lbrakk>\<lbrakk>\<exists>v stack_tl. stack dfs_state = v # stack_tl; found dfs_state\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto simp: DFS_skeleton_refine_unfin_ret_2_conds_def split: list.splits option.splits if_splits)

lemma DFS_skeleton_refine_unfin_ret_2_condsI[call_cond_intros]:
  "\<lbrakk>stack dfs_state = v # stack_tl; found dfs_state\<rbrakk> \<Longrightarrow> DFS_skeleton_refine_unfin_ret_2_conds dfs_state"
  by(auto simp: DFS_skeleton_refine_unfin_ret_2_conds_def split: list.splits option.splits if_splits)

definition "DFS_skeleton_refine_unfin_ret2 dfs_state = on_found dfs_state"

lemma DFS_skeleton_refine_unfin_cases:
  assumes "DFS_skeleton_refine_unfin_call_1_conds dfs_state \<Longrightarrow> P"
      "DFS_skeleton_refine_unfin_call_2_conds dfs_state \<Longrightarrow> P"
      "DFS_skeleton_refine_unfin_ret_1_conds dfs_state \<Longrightarrow> P"
      "DFS_skeleton_refine_unfin_ret_2_conds dfs_state \<Longrightarrow> P"
  shows "P"
proof-
  have "DFS_skeleton_refine_unfin_call_1_conds dfs_state \<or> DFS_skeleton_refine_unfin_call_2_conds dfs_state \<or>
        DFS_skeleton_refine_unfin_ret_1_conds dfs_state \<or> DFS_skeleton_refine_unfin_ret_2_conds dfs_state"
    by (auto simp add: DFS_skeleton_refine_unfin_call_1_conds_def DFS_skeleton_refine_unfin_call_2_conds_def
                       DFS_skeleton_refine_unfin_ret_1_conds_def DFS_skeleton_refine_unfin_ret_2_conds_def
           split: list.split_asm option.split_asm if_splits)
  then show ?thesis
    using assms by auto
qed

lemma DFS_skeleton_refine_unfin_simps:
  assumes "DFS_skeleton_refine_unfin_dom dfs_state"
  shows"DFS_skeleton_refine_unfin_call_1_conds dfs_state \<Longrightarrow>
          DFS_skeleton_refine_unfin dfs_state = DFS_skeleton_refine_unfin (DFS_skeleton_refine_unfin_upd1 dfs_state)"
      "DFS_skeleton_refine_unfin_call_2_conds dfs_state \<Longrightarrow>
          DFS_skeleton_refine_unfin dfs_state = DFS_skeleton_refine_unfin (DFS_skeleton_refine_unfin_upd2 dfs_state)"
      "DFS_skeleton_refine_unfin_ret_1_conds dfs_state \<Longrightarrow>
          DFS_skeleton_refine_unfin dfs_state = DFS_skeleton_refine_unfin_ret1 dfs_state"
      "DFS_skeleton_refine_unfin_ret_2_conds dfs_state \<Longrightarrow>
          DFS_skeleton_refine_unfin dfs_state = DFS_skeleton_refine_unfin_ret2 dfs_state"
  by (auto simp add: DFS_skeleton_refine_unfin.psimps[OF assms] Let_def
                     DFS_skeleton_refine_unfin_call_1_conds_def DFS_skeleton_refine_unfin_upd1_def
                     DFS_skeleton_refine_unfin_call_2_conds_def DFS_skeleton_refine_unfin_upd2_def
                     DFS_skeleton_refine_unfin_ret_1_conds_def DFS_skeleton_refine_unfin_ret1_def
                     DFS_skeleton_refine_unfin_ret_2_conds_def DFS_skeleton_refine_unfin_ret2_def
            split: list.splits option.splits if_splits)

lemma DFS_skeleton_refine_unfin_induct:
  assumes "DFS_skeleton_refine_unfin_dom dfs_state"
  assumes "\<And>dfs_state. \<lbrakk>DFS_skeleton_refine_unfin_dom dfs_state;
            DFS_skeleton_refine_unfin_call_1_conds dfs_state \<Longrightarrow> P (DFS_skeleton_refine_unfin_upd1 dfs_state);
            DFS_skeleton_refine_unfin_call_2_conds dfs_state \<Longrightarrow> P (DFS_skeleton_refine_unfin_upd2 dfs_state)\<rbrakk>
              \<Longrightarrow> P dfs_state"
  shows "P dfs_state"
  apply(rule DFS_skeleton_refine_unfin.pinduct[OF assms(1)])
  apply(rule assms(2)[simplified DFS_skeleton_refine_unfin_call_1_conds_def DFS_skeleton_refine_unfin_upd1_def
                                 DFS_skeleton_refine_unfin_call_2_conds_def DFS_skeleton_refine_unfin_upd2_def])
  by (auto simp: Let_def split: list.splits option.splits if_splits)

lemma DFS_skeleton_refine_unfin_domintros:
  assumes "DFS_skeleton_refine_unfin_call_1_conds dfs_state \<Longrightarrow>
             DFS_skeleton_refine_unfin_dom (DFS_skeleton_refine_unfin_upd1 dfs_state)"
      and "DFS_skeleton_refine_unfin_call_2_conds dfs_state \<Longrightarrow>
             DFS_skeleton_refine_unfin_dom (DFS_skeleton_refine_unfin_upd2 dfs_state)"
  shows "DFS_skeleton_refine_unfin_dom dfs_state"
proof(rule DFS_skeleton_refine_unfin.domintros, goal_cases)
  case (1 x)
  then show ?case
    using assms(1)[simplified DFS_skeleton_refine_unfin_call_1_conds_def DFS_skeleton_refine_unfin_upd1_def]
    by (force simp: Let_def split: list.splits option.splits if_splits)
next
  case (2 x)
  then show ?case
    using assms(2)[simplified DFS_skeleton_refine_unfin_call_2_conds_def DFS_skeleton_refine_unfin_upd2_def]
    by (force simp: Let_def split: list.splits option.splits if_splits)
qed

subsection \<open>The refinement invariant\<close>

text \<open>The state's adjacency map is the original graph with every edge into a \<^emph>\<open>finished\<close> vertex
  removed --- finished meaning seen and no longer on the stack. Equivalently --- and this is the
  form the loop consumes --- \<open>\<N> (adjmap st) v\<close> holds exactly \<open>v\<close>'s \<^emph>\<open>unfinished\<close>
  out-neighbours in \<open>G\<close>.\<close>

definition "invar_adj dfs_state \<longleftrightarrow>
  Graph.graph_inv (adjmap dfs_state)
  \<and> Graph.digraph_abs (adjmap dfs_state)
      = Graph.digraph_abs G
          - (UNIV \<times> (t_set (seen dfs_state) - set (stack dfs_state)))"

subsection \<open>What the carried map offers\<close>

text \<open>These read nothing but \<open>invar_adj\<close> and the graph ADT, so they live here rather than in
  the reasoning layer: an instance can use them \<^emph>\<open>before\<close> it has discharged the reasoning
  layer's obligations --- which it typically must, since those obligations (\<open>sel_unseen\<close> and
  the preservation of its own invariant) are proved with exactly these facts.\<close>

context
includes Graph.adjmap.automation and Graph.vset.set.automation
begin

lemma adj_nbr_inv:
  assumes "invar_adj st"
  shows "vset_inv (adj_nbr st v)"
  using assms Graph.neighbourhood_invars'[of "adjmap st" v] by (simp add: invar_adj_def)

lemma adj_nbr_set:
  assumes "invar_adj st"
  shows "t_set (adj_nbr st v)
           = {w. (v, w) \<in> Graph.digraph_abs G} - (t_set (seen st) - set (stack st))"
proof -
  have gi: "Graph.graph_inv (adjmap st)"
    and abs: "Graph.digraph_abs (adjmap st)
                = Graph.digraph_abs G - (UNIV \<times> (t_set (seen st) - set (stack st)))"
    using assms by (auto simp: invar_adj_def)
  have "t_set (adj_nbr st v) = {w. (v, w) \<in> Graph.digraph_abs (adjmap st)}"
    by (auto simp: Graph.are_connected_abs_general[OF gi])
  thus ?thesis by (auto simp: abs)
qed

text \<open>Emptiness \<^emph>\<open>is\<close> decided by the element set: one direction is \<open>t_set \<emptyset>\<^sub>N = {}\<close>, the
  other is \<^locale>\<open>Set_Choose\<close>'s \<open>choose\<close> (a non-empty vset yields a member). Kept for
  instances comparing differently-built vsets.\<close>
lemma vset_ne_cong:
  assumes "vset_inv X"
      and "vset_inv Y"
      and "t_set X = t_set Y"
  shows "(X \<noteq> \<emptyset>\<^sub>N) = (Y \<noteq> \<emptyset>\<^sub>N)"
  using assms Graph.vset.emptyD by metis

text \<open>The selected vertex is a real out-neighbour in \<open>G\<close> --- in particular a graph vertex, which
  is what the seen-set inclusion in \<open>invar_seen_stack\<close> and the termination measure consume.\<close>
lemma sel_adj_nbr_props:
  assumes c: "DFS_skeleton_refine_unfin_call_1_conds st"
      and ia: "invar_adj st"
  shows "sel (adj_nbr st (hd (stack st))) \<in> t_set (adj_nbr st (hd (stack st)))"
    and "(hd (stack st), sel (adj_nbr st (hd (stack st)))) \<in> Graph.digraph_abs G"
    and "sel (adj_nbr st (hd (stack st))) \<in> dVs (Graph.digraph_abs G)"
proof -
  have ne: "adj_nbr st (hd (stack st)) \<noteq> \<emptyset>\<^sub>N"
    using c by (auto elim!: call_cond_elims)
  show mem: "sel (adj_nbr st (hd (stack st))) \<in> t_set (adj_nbr st (hd (stack st)))"
    by (rule Graph.vset.choose'[OF ne adj_nbr_inv[OF ia]])
  thus edge: "(hd (stack st), sel (adj_nbr st (hd (stack st)))) \<in> Graph.digraph_abs G"
    using adj_nbr_set[OF ia] by auto
  thus "sel (adj_nbr st (hd (stack st))) \<in> dVs (Graph.digraph_abs G)"
    by (auto intro: dVsI)
qed

end

end

text \<open>The reasoning layer. On top of \<^locale>\<open>DFS_skeleton_thms\<close> --- whose spine-preservation
  assumptions we inherit --- three groups of assumptions. First, \<open>adjmap\<close> must be blind to the
  spine, which is automatic when it selects a \<open>'more\<close> field. Second, the backtrack step must
  treat the carried graph correctly --- it deletes exactly the in-edges of the popped vertex ---
  and the other callbacks, \<open>on_push\<close> included, must leave it alone. The backtrack obligations
  are stated about the whole step \<open>DFS_skeleton_refine_unfin_upd2\<close> \<^emph>\<open>under the invariants\<close>,
  not about \<open>on_backtrack\<close> at an arbitrary state: an instance typically enumerates the popped
  vertex's predecessors from a \<^emph>\<open>state-carried reverse map\<close> (kept the inverse of \<open>adjmap\<close> by
  its \<open>aux_invar\<close>), and what that walk deletes coincides with \<open>UNIV \<times> {v}\<close> only on states
  where that inverse relationship actually holds.

  Third, the two obligations that replace what prune-at-push got for free. The carried map offers
  the \<^emph>\<open>unfinished\<close> neighbours, on-stack vertices included, so the descend branch is sound only
  under a discipline the instance's \<open>found\<close> must enforce: \<open>sel_unseen\<close> says that whenever the
  descend branch is taken (\<open>\<not> found\<close>, non-empty offered set), the selected vertex is unseen.
  The instance discharges it through \<open>aux_invar\<close>, its own invariant --- for a cycle search:
  the gray set is the stack, and \<open>found\<close> halts on gray selections, so a surviving selection is
  neither gray nor finished, i.e.\ unseen --- which the last two assumptions keep in force along
  the two recursive steps.\<close>

locale DFS_skeleton_refine_unfin_thms =
  DFS_skeleton_refine_unfin where lookup = lookup and on_push = on_push and adjmap = adjmap +
  DFS_skeleton_thms where lookup = lookup and on_push = on_push
  for lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option"
  and on_push :: "'v \<Rightarrow> ('v,'vset,'more) DFS_skeleton_state_scheme
                     \<Rightarrow> ('v,'vset,'more) DFS_skeleton_state_scheme"
  and adjmap :: "('v,'vset,'more) DFS_skeleton_state_scheme \<Rightarrow> 'adjmap" +
  fixes aux_invar :: "('v,'vset,'more) DFS_skeleton_state_scheme \<Rightarrow> bool"
  assumes adjmap_stack[simp]: "adjmap (st \<lparr>stack := xs\<rparr>) = adjmap st"
      and adjmap_seen[simp]:  "adjmap (st \<lparr>seen := S\<rparr>) = adjmap st"
      and on_found_adjmap[simp]:     "adjmap (on_found st) = adjmap st"
      and on_empty_adjmap[simp]:     "adjmap (on_empty st) = adjmap st"
      and on_push_adjmap[simp]:      "adjmap (on_push u st) = adjmap st"
      and upd2_adjmap_graph_inv:
            "\<lbrakk>DFS_skeleton_refine_unfin_call_2_conds st; aux_invar st; invar_adj st;
              invar_1 st; invar_seen_stack st\<rbrakk> \<Longrightarrow>
               Graph.graph_inv (adjmap (DFS_skeleton_refine_unfin_upd2 st))"
      and upd2_adjmap_digraph_abs:
            "\<lbrakk>DFS_skeleton_refine_unfin_call_2_conds st; aux_invar st; invar_adj st;
              invar_1 st; invar_seen_stack st\<rbrakk> \<Longrightarrow>
               Graph.digraph_abs (adjmap (DFS_skeleton_refine_unfin_upd2 st))
                 = Graph.digraph_abs (adjmap st) - (UNIV \<times> {hd (stack st)})"
      and sel_unseen:
            "\<lbrakk>DFS_skeleton_refine_unfin_call_1_conds st; aux_invar st; invar_adj st;
              invar_1 st; invar_seen_stack st\<rbrakk> \<Longrightarrow>
               sel (adj_nbr st (hd (stack st))) \<notin> t_set (seen st)"
      and aux_invar_upd1:
            "\<lbrakk>DFS_skeleton_refine_unfin_call_1_conds st; aux_invar st; invar_adj st;
              invar_1 st; invar_seen_stack st\<rbrakk> \<Longrightarrow>
               aux_invar (DFS_skeleton_refine_unfin_upd1 st)"
      and aux_invar_upd2:
            "\<lbrakk>DFS_skeleton_refine_unfin_call_2_conds st; aux_invar st; invar_adj st;
              invar_1 st; invar_seen_stack st\<rbrakk> \<Longrightarrow>
               aux_invar (DFS_skeleton_refine_unfin_upd2 st)"
begin

context
includes Graph.adjmap.automation and Graph.vset.set.automation
begin

subsection \<open>The two steps, unfolded\<close>

lemma refine_upd1_unfold:
  "stack (DFS_skeleton_refine_unfin_upd1 st) = sel (adj_nbr st (hd (stack st))) # stack st"
  "seen (DFS_skeleton_refine_unfin_upd1 st)
     = insert (sel (adj_nbr st (hd (stack st)))) (seen st)"
  "adjmap (DFS_skeleton_refine_unfin_upd1 st) = adjmap st"
  by (simp_all add: DFS_skeleton_refine_unfin_upd1_def Let_def)

lemma refine_upd2_unfold:
  "stack (DFS_skeleton_refine_unfin_upd2 st) = tl (stack st)"
  "seen (DFS_skeleton_refine_unfin_upd2 st) = seen st"
  by (simp_all add: DFS_skeleton_refine_unfin_upd2_def)

lemma refine_upd2_adjmap:
  "adjmap (DFS_skeleton_refine_unfin_upd2 st)
     = adjmap (on_backtrack (hd (stack st)) (st \<lparr>stack := tl (stack st)\<rparr>))"
  by (simp add: DFS_skeleton_refine_unfin_upd2_def)

subsection \<open>The structural invariants are preserved by the refined loop\<close>

lemma refine_invar_1_holds_1[invar_holds_intros]:
  "\<lbrakk>DFS_skeleton_refine_unfin_call_1_conds st; invar_1 st\<rbrakk>
     \<Longrightarrow> invar_1 (DFS_skeleton_refine_unfin_upd1 st)"
  by (auto simp: refine_upd1_unfold elim!: invar_props_elims intro!: invar_props_intros)

lemma refine_invar_1_holds_2[invar_holds_intros]:
  "\<lbrakk>DFS_skeleton_refine_unfin_call_2_conds st; invar_1 st\<rbrakk>
     \<Longrightarrow> invar_1 (DFS_skeleton_refine_unfin_upd2 st)"
  by (auto simp: refine_upd2_unfold elim!: invar_props_elims intro!: invar_props_intros)

lemma refine_invar_1_holds_4[invar_holds_intros]:
  "\<lbrakk>DFS_skeleton_refine_unfin_ret_1_conds st; invar_1 st\<rbrakk>
     \<Longrightarrow> invar_1 (DFS_skeleton_refine_unfin_ret1 st)"
  by (auto simp: DFS_skeleton_refine_unfin_ret1_def elim!: invar_props_elims intro!: invar_props_intros)

lemma refine_invar_1_holds_5[invar_holds_intros]:
  "\<lbrakk>DFS_skeleton_refine_unfin_ret_2_conds st; invar_1 st\<rbrakk>
     \<Longrightarrow> invar_1 (DFS_skeleton_refine_unfin_ret2 st)"
  by (auto simp: DFS_skeleton_refine_unfin_ret2_def elim!: invar_props_elims intro!: invar_props_intros)

lemma refine_invar_seen_stack_holds_1[invar_holds_intros]:
  assumes c: "DFS_skeleton_refine_unfin_call_1_conds st"
      and ax: "aux_invar st"
      and ia: "invar_adj st"
      and i1: "invar_1 st"
      and iss: "invar_seen_stack st"
  shows "invar_seen_stack (DFS_skeleton_refine_unfin_upd1 st)"
proof -
  let ?u = "sel (adj_nbr st (hd (stack st)))"
  have unseen: "?u \<notin> t_set (seen st)" by (rule sel_unseen[OF c ax ia i1 iss])
  have dv: "?u \<in> dVs (Graph.digraph_abs G)" by (rule sel_adj_nbr_props(3)[OF c ia])
  show ?thesis
    using iss i1 unseen dv
    by (auto simp: refine_upd1_unfold elim!: invar_props_elims intro!: invar_props_intros)
qed

lemma refine_invar_seen_stack_holds_2[invar_holds_intros]:
  "\<lbrakk>DFS_skeleton_refine_unfin_call_2_conds st; invar_1 st; invar_seen_stack st\<rbrakk>
     \<Longrightarrow> invar_seen_stack (DFS_skeleton_refine_unfin_upd2 st)"
  by (auto simp: refine_upd2_unfold elim!: call_cond_elims invar_props_elims
           intro!: invar_props_intros dest: list.set_sel(2))

lemma refine_invar_seen_stack_holds_4[invar_holds_intros]:
  "\<lbrakk>DFS_skeleton_refine_unfin_ret_1_conds st; invar_seen_stack st\<rbrakk>
     \<Longrightarrow> invar_seen_stack (DFS_skeleton_refine_unfin_ret1 st)"
  by (auto simp: DFS_skeleton_refine_unfin_ret1_def elim!: invar_props_elims intro!: invar_props_intros)

lemma refine_invar_seen_stack_holds_5[invar_holds_intros]:
  "\<lbrakk>DFS_skeleton_refine_unfin_ret_2_conds st; invar_seen_stack st\<rbrakk>
     \<Longrightarrow> invar_seen_stack (DFS_skeleton_refine_unfin_ret2 st)"
  by (auto simp: DFS_skeleton_refine_unfin_ret2_def elim!: invar_props_elims intro!: invar_props_intros)

subsection \<open>The refinement invariant is preserved\<close>

text \<open>The push leaves both sides of \<open>invar_adj\<close> alone: the carried map is untouched, and the
  finished region \<open>seen - stack\<close> is unchanged because the pushed vertex enters \<^emph>\<open>both\<close> sets ---
  freshly, by \<open>sel_unseen\<close>. The backtrack moves them together: \<open>seen - stack\<close> gains exactly the
  popped vertex (it is seen, and by distinctness not on the tail), and the map loses exactly its
  in-edges.\<close>

lemma refine_invar_adj_holds_1[invar_holds_intros]:
  assumes c: "DFS_skeleton_refine_unfin_call_1_conds st"
      and ax: "aux_invar st"
      and ia: "invar_adj st"
      and i1: "invar_1 st"
      and iss: "invar_seen_stack st"
  shows "invar_adj (DFS_skeleton_refine_unfin_upd1 st)"
proof -
  let ?u = "sel (adj_nbr st (hd (stack st)))"
  have unseen: "?u \<notin> t_set (seen st)" by (rule sel_unseen[OF c ax ia i1 iss])
  have "t_set (insert ?u (seen st)) - set (?u # stack st)
          = t_set (seen st) - set (stack st)"
    using unseen i1 by (auto elim!: invar_props_elims)
  thus ?thesis
    using ia by (simp add: invar_adj_def refine_upd1_unfold)
qed

lemma refine_invar_adj_holds_2[invar_holds_intros]:
  assumes c: "DFS_skeleton_refine_unfin_call_2_conds st"
      and ax: "aux_invar st"
      and ia: "invar_adj st"
      and i1: "invar_1 st"
      and iss: "invar_seen_stack st"
  shows "invar_adj (DFS_skeleton_refine_unfin_upd2 st)"
proof -
  obtain v stack_tl where stk: "stack st = v # stack_tl"
    using c by (auto elim!: call_cond_elims)
  have abs: "Graph.digraph_abs (adjmap st)
                = Graph.digraph_abs G - (UNIV \<times> (t_set (seen st) - set (stack st)))"
    using ia by (auto simp: invar_adj_def)
  have gi': "Graph.graph_inv (adjmap (DFS_skeleton_refine_unfin_upd2 st))"
    by (rule upd2_adjmap_graph_inv[OF c ax ia i1 iss])
  have seen_v: "v \<in> t_set (seen st)" and dist: "v \<notin> set stack_tl"
    using iss stk by (auto elim!: invar_props_elims)
  have "Graph.digraph_abs (adjmap (DFS_skeleton_refine_unfin_upd2 st))
          = Graph.digraph_abs (adjmap st) - (UNIV \<times> {hd (stack st)})"
    by (rule upd2_adjmap_digraph_abs[OF c ax ia i1 iss])
  also have "\<dots> = Graph.digraph_abs G
                    - (UNIV \<times> (t_set (seen st) - set (tl (stack st))))"
    using seen_v dist stk by (auto simp: abs)
  finally show ?thesis
    using gi' by (simp add: invar_adj_def refine_upd2_unfold)
qed

lemma refine_invar_adj_holds_4[invar_holds_intros]:
  "\<lbrakk>DFS_skeleton_refine_unfin_ret_1_conds st; invar_adj st\<rbrakk>
     \<Longrightarrow> invar_adj (DFS_skeleton_refine_unfin_ret1 st)"
  by (simp add: invar_adj_def DFS_skeleton_refine_unfin_ret1_def)

lemma refine_invar_adj_holds_5[invar_holds_intros]:
  "\<lbrakk>DFS_skeleton_refine_unfin_ret_2_conds st; invar_adj st\<rbrakk>
     \<Longrightarrow> invar_adj (DFS_skeleton_refine_unfin_ret2 st)"
  by (simp add: invar_adj_def DFS_skeleton_refine_unfin_ret2_def)

subsection \<open>Termination\<close>

text \<open>The plain skeleton's measure, verbatim: the descend step pushes an unseen graph vertex
  (\<open>sel_unseen\<close> plus \<open>sel_adj_nbr_props\<close>), so the unseen count drops; the backtrack step leaves
  \<open>seen\<close> alone and shortens the stack.\<close>

lemma refine_call_1_terminates[termination_intros]:
  assumes c: "DFS_skeleton_refine_unfin_call_1_conds st"
      and ax: "aux_invar st"
      and ia: "invar_adj st"
      and i1: "invar_1 st"
      and iss: "invar_seen_stack st"
  shows "(DFS_skeleton_refine_unfin_upd1 st, st) \<in> call_1_measure <*mlex*> r"
proof -
  let ?u = "sel (adj_nbr st (hd (stack st)))"
  have unseen: "?u \<notin> t_set (seen st)" by (rule sel_unseen[OF c ax ia i1 iss])
  have dv: "?u \<in> dVs (Graph.digraph_abs G)" by (rule sel_adj_nbr_props(3)[OF c ia])
  have fin: "finite (dVs (Graph.digraph_abs G))"
    using graph_inv by (auto intro!: Graph.finite_vertices)
  have "dVs (Graph.digraph_abs G) - t_set (insert ?u (seen st))
          \<subset> dVs (Graph.digraph_abs G) - t_set (seen st)"
    using unseen dv i1 by (auto elim!: invar_props_elims)
  hence "card (dVs (Graph.digraph_abs G) - t_set (insert ?u (seen st)))
           < card (dVs (Graph.digraph_abs G) - t_set (seen st))"
    using fin by (auto intro!: psubset_card_mono)
  thus ?thesis
    by (auto simp: call_1_measure_def refine_upd1_unfold intro!: mlex_less)
qed

lemma refine_call_2_measure_1[termination_intros]:
  "call_1_measure st = call_1_measure (DFS_skeleton_refine_unfin_upd2 st)"
  by (simp add: call_1_measure_def refine_upd2_unfold)

lemma refine_call_2_terminates[termination_intros]:
  assumes c: "DFS_skeleton_refine_unfin_call_2_conds st"
      and iss: "invar_seen_stack st"
  shows "(DFS_skeleton_refine_unfin_upd2 st, st) \<in> call_2_measure <*mlex*> r"
proof -
  obtain v stack_tl where stk: "stack st = v # stack_tl"
    using c by (auto elim!: call_cond_elims)
  have "distinct (stack st)" using iss by (auto elim!: invar_props_elims)
  hence "card (set (tl (stack st))) < card (set (stack st))"
    using stk by (auto simp: distinct_card)
  thus ?thesis
    by (auto simp: call_2_measure_def refine_upd2_unfold intro!: mlex_less)
qed

lemma in_DFS_skeleton_refine_unfin_term_rel'[termination_intros]:
  "\<lbrakk>DFS_skeleton_refine_unfin_call_1_conds st; aux_invar st; invar_adj st; invar_1 st;
    invar_seen_stack st\<rbrakk> \<Longrightarrow>
      (DFS_skeleton_refine_unfin_upd1 st, st) \<in> DFS_skeleton_term_rel'"
  "\<lbrakk>DFS_skeleton_refine_unfin_call_2_conds st; invar_seen_stack st\<rbrakk> \<Longrightarrow>
      (DFS_skeleton_refine_unfin_upd2 st, st) \<in> DFS_skeleton_term_rel'"
  by (simp_all add: DFS_skeleton_term_rel'_def refine_call_1_terminates
                    refine_call_2_terminates refine_call_2_measure_1[symmetric] in_prod_relI)

lemma DFS_skeleton_refine_unfin_terminates[termination_intros]:
  assumes "aux_invar st" "invar_adj st" "invar_1 st" "invar_seen_stack st"
  shows "DFS_skeleton_refine_unfin_dom st"
  using wf_term_rel assms
proof (induction rule: wf_induct_rule)
  case (less x)
  show ?case
    by (rule DFS_skeleton_refine_unfin_domintros)
       (auto intro!: less aux_invar_upd1 aux_invar_upd2 invar_holds_intros
                     in_DFS_skeleton_refine_unfin_term_rel')
qed

subsection \<open>The invariants survive a whole run\<close>

text \<open>What an instance needs in order to read the carried graph off the result and hand it on:
  the returns touch neither the spine nor the map, so only the two recursive steps matter, and
  those are the preservation lemmas above.\<close>

lemma refine_invars_hold:
  assumes dom: "DFS_skeleton_refine_unfin_dom st"
      and "aux_invar st" "invar_adj st" "invar_1 st" "invar_seen_stack st"
  shows "invar_adj (DFS_skeleton_refine_unfin st)
           \<and> invar_1 (DFS_skeleton_refine_unfin st) \<and> invar_seen_stack (DFS_skeleton_refine_unfin st)"
  using assms(2-)
proof (induction rule: DFS_skeleton_refine_unfin_induct[OF dom])
  case IH: (1 st)
  show ?case
  proof (rule DFS_skeleton_refine_unfin_cases[where dfs_state = st])
    show ?case if c: "DFS_skeleton_refine_unfin_call_1_conds st"
      using IH(2)[OF c aux_invar_upd1[OF c IH(4-7)] refine_invar_adj_holds_1[OF c IH(4-7)]
                       refine_invar_1_holds_1[OF c IH(6)]
                       refine_invar_seen_stack_holds_1[OF c IH(4-7)]]
      by (simp add: DFS_skeleton_refine_unfin_simps(1)[OF IH(1) c])
    show ?case if c: "DFS_skeleton_refine_unfin_call_2_conds st"
      using IH(3)[OF c aux_invar_upd2[OF c IH(4-7)] refine_invar_adj_holds_2[OF c IH(4) IH(5) IH(6) IH(7)]
                       refine_invar_1_holds_2[OF c IH(6)]
                       refine_invar_seen_stack_holds_2[OF c IH(6) IH(7)]]
      by (simp add: DFS_skeleton_refine_unfin_simps(2)[OF IH(1) c])
    show ?case if c: "DFS_skeleton_refine_unfin_ret_1_conds st"
      using IH(4-7)
      by (auto simp: DFS_skeleton_refine_unfin_simps(3)[OF IH(1) c]
               intro: refine_invar_adj_holds_4[OF c] refine_invar_1_holds_4[OF c]
                      refine_invar_seen_stack_holds_4[OF c])
    show ?case if c: "DFS_skeleton_refine_unfin_ret_2_conds st"
      using IH(4-7)
      by (auto simp: DFS_skeleton_refine_unfin_simps(4)[OF IH(1) c]
               intro: refine_invar_adj_holds_5[OF c] refine_invar_1_holds_5[OF c]
                      refine_invar_seen_stack_holds_5[OF c])
  qed
qed

lemmas refine_invar_adj_holds = refine_invars_hold[THEN conjunct1]
   and refine_invar_1_holds = refine_invars_hold[THEN conjunct2, THEN conjunct1]
   and refine_invar_seen_stack_holds = refine_invars_hold[THEN conjunct2, THEN conjunct2]

end

end

end
