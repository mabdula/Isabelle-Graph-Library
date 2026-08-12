theory DFS_Skel_More_Refine
  imports DFS_Skel_More
begin

text \<open>A refinement of \<^locale>\<open>DFS_skel_more\<close> that removes the set difference from the search's
  inner loop.

  \<^bold>\<open>The cost being removed.\<close> Both the library skeleton and \<^locale>\<open>DFS_skel_more\<close> pick the next
  vertex with \<open>(\<N>\<^sub>G v) -\<^sub>G (seen dfs_state)\<close>, and they evaluate that expression \<^emph>\<open>twice\<close> per
  step --- once for the emptiness test, once inside the \<open>sel\<close>. It is recomputed from scratch on
  every iteration, so a vertex of out-degree \<open>d\<close> performs \<open>d+1\<close> differences over its own
  neighbourhood before it is exhausted. At the red-black-tree instantiation \<open>-\<^sub>G\<close> is
  \<open>RBT.diff\<close>, the join/split-based difference, whose cost scales with \<^emph>\<open>both\<close> operands rather
  than with the neighbourhood alone.

  \<^bold>\<open>The refinement.\<close> Carry the graph itself in the state --- \<open>adjmap\<close> below is a selector into
  the extensible \<open>'more\<close> slot --- and have \<open>on_push u\<close> delete every edge \<^emph>\<open>entering\<close> \<open>u\<close>. Then
  the state's adjacency map never offers a seen vertex, the difference is redundant, and the loop
  reads a plain neighbourhood: \<open>(\<N> (adjmap st) v) \<noteq> \<emptyset>\<^sub>N\<close> and \<open>sel (\<N> (adjmap st) v)\<close>. This
  is the invariant \<open>invar_adj\<close>: \<open>[adjmap st]\<^sub>g = [G]\<^sub>g - (UNIV \<times> t_set (seen st))\<close>.

  \<^bold>\<open>What this locale does and does not fix.\<close> It says only what \<open>on_push\<close> must \<^emph>\<open>achieve\<close>, not
  how. That matters, because \<open>Pair_Graph_Specs.delete_edge\<close> is keyed by an edge's
  \<^emph>\<open>source\<close>, so deleting the in-edges of \<open>u\<close> means knowing \<open>u\<close>'s predecessors. An instance
  should carry a \<^emph>\<open>static\<close> reverse adjacency map (the predecessors in the original \<open>G\<close>, built
  once): each vertex is pushed at most once, so the total deletion work is one pass over the edges
  and the search stays linear. Instantiating instead by scanning every vertex's neighbour set per
  push costs \<open>O(V)\<close> a step --- exactly the price this refinement exists to remove.

  \<^bold>\<open>Why \<open>sel_cong\<close> is needed, and it really is needed.\<close> The equivalence below is an equality of
  \<^emph>\<open>runs\<close>, so the two loops must select the same vertex at every step. \<^locale>\<open>Set_Choose\<close>
  assumes only \<open>s \<noteq> \<emptyset>\<^sub>N \<Longrightarrow> isin s (sel s)\<close>; it does not make \<open>sel\<close> a function of the
  underlying set. And at the red-black-tree instantiation it is not one --- there \<open>sel\<close> is the
  \<^emph>\<open>root label\<close>, so two trees holding the same elements in different shapes select differently.
  Since \<open>\<N> (adjmap st) v\<close> is built by repeated deletion and \<open>(\<N>\<^sub>G v) -\<^sub>G (seen st)\<close> by
  \<open>RBT.diff\<close>, they agree on elements but not on shape. Hence the assumption
  \<open>sel_cong\<close> in \<open>DFS_skel_more_refine_thms\<close>: a \<open>sel\<close> determined by the element set (for a
  search tree, the leftmost element rather than the root). Without it the refined search is still a
  perfectly good DFS, but it is a \<^emph>\<open>different\<close> one, and none of the invariant machinery above
  \<^theory>\<open>DFS_Skeletons.DFS_Skel_More\<close> transfers.

  \<^bold>\<open>What the equivalence buys.\<close> Both locales share the same \<open>on_push\<close> --- the refinement changes
  only which map the loop \<^emph>\<open>reads\<close>, not how the state evolves --- so the two runs produce
  literally identical states, \<open>'more\<close> slot included. Everything proved about
  \<open>DFS_skel_more\<close> therefore applies verbatim to \<open>DFS_skel_more_refine\<close>, with no invariant
  re-proved.\<close>

text \<open>The inherited parameters are re-declared in the \<open>for\<close> clause purely to \<^emph>\<open>name\<close> the type
  variables, so that \<open>adjmap\<close>'s type can be tied to the same \<open>'adjmap\<close> as \<open>lookup\<close>'s and the same
  state scheme as the callbacks'. Written as a bare \<open>DFS_skel_more + fixes adjmap :: \<dots>\<close> the type
  variables in the new \<open>fixes\<close> would be fresh, and nothing would connect them to the inherited
  ones.\<close>

locale DFS_skel_more_refine =
  DFS_skel_more where lookup = lookup and on_push = on_push
  for lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option"
  and on_push :: "'v \<Rightarrow> ('v,'vset,'more) DFS_skel_state_scheme
                     \<Rightarrow> ('v,'vset,'more) DFS_skel_state_scheme" +
  fixes adjmap :: "('v,'vset,'more) DFS_skel_state_scheme \<Rightarrow> 'adjmap"
begin

abbreviation adj_nbr :: "('v,'vset,'more) DFS_skel_state_scheme \<Rightarrow> 'v \<Rightarrow> 'vset" where
  "adj_nbr st v \<equiv> Graph.neighbourhood (adjmap st) v"

subsection \<open>The refined search\<close>

text \<open>Identical to \<open>DFS_skel_more\<close> except that the unexplored neighbours are read off the
  state's own adjacency map instead of being recomputed as a difference.\<close>

function (domintros) DFS_skel_more_refine::
  "('v,'vset,'more) DFS_skel_state_scheme \<Rightarrow> ('v,'vset,'more) DFS_skel_state_scheme" where
  "DFS_skel_more_refine dfs_state =
     (case (stack dfs_state) of (v # stack_tl) \<Rightarrow>
       (if found dfs_state then on_found dfs_state
        else (if adj_nbr dfs_state v \<noteq> \<emptyset>\<^sub>N then
                let u = sel (adj_nbr dfs_state v);
                    stack' = u # (stack dfs_state);
                    seen' = insert u (seen dfs_state)
                in DFS_skel_more_refine (on_push u (dfs_state \<lparr>stack := stack', seen := seen'\<rparr>))
              else
                DFS_skel_more_refine (on_backtrack v (dfs_state \<lparr>stack := stack_tl\<rparr>))))
     | _ \<Rightarrow> on_empty dfs_state)"
  by pat_completeness auto

partial_function (tailrec) DFS_skel_more_refine_impl::
  "('v,'vset,'more) DFS_skel_state_scheme \<Rightarrow> ('v,'vset,'more) DFS_skel_state_scheme" where
  "DFS_skel_more_refine_impl dfs_state =
     (case (stack dfs_state) of (v # stack_tl) \<Rightarrow>
       (if found dfs_state then on_found dfs_state
        else (if adj_nbr dfs_state v \<noteq> \<emptyset>\<^sub>N then
                let u = sel (adj_nbr dfs_state v);
                    stack' = u # (stack dfs_state);
                    seen' = insert u (seen dfs_state)
                in DFS_skel_more_refine_impl (on_push u (dfs_state \<lparr>stack := stack', seen := seen'\<rparr>))
              else
                DFS_skel_more_refine_impl (on_backtrack v (dfs_state \<lparr>stack := stack_tl\<rparr>))))
     | _ \<Rightarrow> on_empty dfs_state)"

lemmas [code] = DFS_skel_more_refine_impl.simps

lemma DFS_skel_more_refine_impl_same:
  assumes "DFS_skel_more_refine_dom state"
  shows   "DFS_skel_more_refine_impl state = DFS_skel_more_refine state"
  by(induction rule: DFS_skel_more_refine.pinduct[OF assms])
    (subst DFS_skel_more_refine.psimps, simp, subst DFS_skel_more_refine_impl.simps,
     auto split: list.split if_split simp add: Let_def)

subsection \<open>Call conditions\<close>

definition "DFS_skel_more_refine_call_1_conds dfs_state =
    (case (stack dfs_state) of (v # stack_tl) \<Rightarrow>
       (if found dfs_state then False
        else (if adj_nbr dfs_state v \<noteq> \<emptyset>\<^sub>N then True else False))
     | _ \<Rightarrow> False)"

lemma DFS_skel_more_refine_call_1_conds[call_cond_elims]:
  "DFS_skel_more_refine_call_1_conds dfs_state \<Longrightarrow>
   \<lbrakk>\<lbrakk>\<exists>v stack_tl. stack dfs_state = v # stack_tl;
    \<not> found dfs_state;
    adj_nbr dfs_state (hd (stack dfs_state)) \<noteq> \<emptyset>\<^sub>N\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto simp: DFS_skel_more_refine_call_1_conds_def split: list.splits option.splits if_splits)

definition "DFS_skel_more_refine_upd1 dfs_state = (
    let
      u = sel (adj_nbr dfs_state (hd (stack dfs_state)));
      stack' = u # (stack dfs_state);
      seen' = insert u (seen dfs_state)
    in
      on_push u (dfs_state \<lparr>stack := stack', seen := seen'\<rparr>))"

definition "DFS_skel_more_refine_call_2_conds dfs_state =
    (case (stack dfs_state) of (v # stack_tl) \<Rightarrow>
       (if found dfs_state then False
        else (if adj_nbr dfs_state v \<noteq> \<emptyset>\<^sub>N then False else True))
     | _ \<Rightarrow> False)"

lemma DFS_skel_more_refine_call_2_conds[call_cond_elims]:
  "DFS_skel_more_refine_call_2_conds dfs_state \<Longrightarrow>
   \<lbrakk>\<lbrakk>\<exists>v stack_tl. stack dfs_state = v # stack_tl;
    \<not> found dfs_state;
    adj_nbr dfs_state (hd (stack dfs_state)) = \<emptyset>\<^sub>N\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto simp: DFS_skel_more_refine_call_2_conds_def split: list.splits option.splits if_splits)

definition "DFS_skel_more_refine_upd2 dfs_state =
  on_backtrack (hd (stack dfs_state)) (dfs_state \<lparr>stack := tl (stack dfs_state)\<rparr>)"

definition "DFS_skel_more_refine_ret_1_conds dfs_state =
    (case (stack dfs_state) of (v # stack_tl) \<Rightarrow> False | _ \<Rightarrow> True)"

lemma DFS_skel_more_refine_ret_1_conds[call_cond_elims]:
  "DFS_skel_more_refine_ret_1_conds dfs_state \<Longrightarrow> \<lbrakk>\<lbrakk>stack dfs_state = []\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto simp: DFS_skel_more_refine_ret_1_conds_def split: list.splits if_splits)

lemma DFS_skel_more_refine_ret_1_condsI[call_cond_intros]:
  "\<lbrakk>stack dfs_state = []\<rbrakk> \<Longrightarrow> DFS_skel_more_refine_ret_1_conds dfs_state"
  by(auto simp: DFS_skel_more_refine_ret_1_conds_def split: list.splits if_splits)

definition "DFS_skel_more_refine_ret1 dfs_state = on_empty dfs_state"

definition "DFS_skel_more_refine_ret_2_conds dfs_state =
    (case (stack dfs_state) of (v # stack_tl) \<Rightarrow>
       (if found dfs_state then True else False)
     | _ \<Rightarrow> False)"

lemma DFS_skel_more_refine_ret_2_conds[call_cond_elims]:
  "DFS_skel_more_refine_ret_2_conds dfs_state \<Longrightarrow>
   \<lbrakk>\<lbrakk>\<exists>v stack_tl. stack dfs_state = v # stack_tl; found dfs_state\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto simp: DFS_skel_more_refine_ret_2_conds_def split: list.splits option.splits if_splits)

lemma DFS_skel_more_refine_ret_2_condsI[call_cond_intros]:
  "\<lbrakk>stack dfs_state = v # stack_tl; found dfs_state\<rbrakk> \<Longrightarrow> DFS_skel_more_refine_ret_2_conds dfs_state"
  by(auto simp: DFS_skel_more_refine_ret_2_conds_def split: list.splits option.splits if_splits)

definition "DFS_skel_more_refine_ret2 dfs_state = on_found dfs_state"

lemma DFS_skel_more_refine_cases:
  assumes "DFS_skel_more_refine_call_1_conds dfs_state \<Longrightarrow> P"
      "DFS_skel_more_refine_call_2_conds dfs_state \<Longrightarrow> P"
      "DFS_skel_more_refine_ret_1_conds dfs_state \<Longrightarrow> P"
      "DFS_skel_more_refine_ret_2_conds dfs_state \<Longrightarrow> P"
  shows "P"
proof-
  have "DFS_skel_more_refine_call_1_conds dfs_state \<or> DFS_skel_more_refine_call_2_conds dfs_state \<or>
        DFS_skel_more_refine_ret_1_conds dfs_state \<or> DFS_skel_more_refine_ret_2_conds dfs_state"
    by (auto simp add: DFS_skel_more_refine_call_1_conds_def DFS_skel_more_refine_call_2_conds_def
                       DFS_skel_more_refine_ret_1_conds_def DFS_skel_more_refine_ret_2_conds_def
           split: list.split_asm option.split_asm if_splits)
  then show ?thesis
    using assms by auto
qed

lemma DFS_skel_more_refine_simps:
  assumes "DFS_skel_more_refine_dom dfs_state"
  shows"DFS_skel_more_refine_call_1_conds dfs_state \<Longrightarrow>
          DFS_skel_more_refine dfs_state = DFS_skel_more_refine (DFS_skel_more_refine_upd1 dfs_state)"
      "DFS_skel_more_refine_call_2_conds dfs_state \<Longrightarrow>
          DFS_skel_more_refine dfs_state = DFS_skel_more_refine (DFS_skel_more_refine_upd2 dfs_state)"
      "DFS_skel_more_refine_ret_1_conds dfs_state \<Longrightarrow>
          DFS_skel_more_refine dfs_state = DFS_skel_more_refine_ret1 dfs_state"
      "DFS_skel_more_refine_ret_2_conds dfs_state \<Longrightarrow>
          DFS_skel_more_refine dfs_state = DFS_skel_more_refine_ret2 dfs_state"
  by (auto simp add: DFS_skel_more_refine.psimps[OF assms] Let_def
                     DFS_skel_more_refine_call_1_conds_def DFS_skel_more_refine_upd1_def
                     DFS_skel_more_refine_call_2_conds_def DFS_skel_more_refine_upd2_def
                     DFS_skel_more_refine_ret_1_conds_def DFS_skel_more_refine_ret1_def
                     DFS_skel_more_refine_ret_2_conds_def DFS_skel_more_refine_ret2_def
            split: list.splits option.splits if_splits)

lemma DFS_skel_more_refine_induct:
  assumes "DFS_skel_more_refine_dom dfs_state"
  assumes "\<And>dfs_state. \<lbrakk>DFS_skel_more_refine_dom dfs_state;
            DFS_skel_more_refine_call_1_conds dfs_state \<Longrightarrow> P (DFS_skel_more_refine_upd1 dfs_state);
            DFS_skel_more_refine_call_2_conds dfs_state \<Longrightarrow> P (DFS_skel_more_refine_upd2 dfs_state)\<rbrakk>
              \<Longrightarrow> P dfs_state"
  shows "P dfs_state"
  apply(rule DFS_skel_more_refine.pinduct[OF assms(1)])
  apply(rule assms(2)[simplified DFS_skel_more_refine_call_1_conds_def DFS_skel_more_refine_upd1_def
                                 DFS_skel_more_refine_call_2_conds_def DFS_skel_more_refine_upd2_def])
  by (auto simp: Let_def split: list.splits option.splits if_splits)

lemma DFS_skel_more_refine_domintros:
  assumes "DFS_skel_more_refine_call_1_conds dfs_state \<Longrightarrow>
             DFS_skel_more_refine_dom (DFS_skel_more_refine_upd1 dfs_state)"
      and "DFS_skel_more_refine_call_2_conds dfs_state \<Longrightarrow>
             DFS_skel_more_refine_dom (DFS_skel_more_refine_upd2 dfs_state)"
  shows "DFS_skel_more_refine_dom dfs_state"
proof(rule DFS_skel_more_refine.domintros, goal_cases)
  case (1 x)
  then show ?case
    using assms(1)[simplified DFS_skel_more_refine_call_1_conds_def DFS_skel_more_refine_upd1_def]
    by (force simp: Let_def split: list.splits option.splits if_splits)
next
  case (2 x)
  then show ?case
    using assms(2)[simplified DFS_skel_more_refine_call_2_conds_def DFS_skel_more_refine_upd2_def]
    by (force simp: Let_def split: list.splits option.splits if_splits)
qed

subsection \<open>The refinement invariant\<close>

text \<open>The state's adjacency map is the original graph with every edge into a seen vertex removed.
  Equivalently --- and this is the form the loop consumes --- \<open>\<N> (adjmap st) v\<close> \<^emph>\<open>is\<close>
  \<open>(\<N>\<^sub>G v) -\<^sub>G (seen st)\<close> at the level of element sets.\<close>

definition "invar_adj dfs_state \<longleftrightarrow>
  Graph.graph_inv (adjmap dfs_state)
  \<and> Graph.digraph_abs (adjmap dfs_state)
      = Graph.digraph_abs G - (UNIV \<times> t_set (seen dfs_state))"

end

text \<open>The reasoning layer. On top of \<^locale>\<open>DFS_skel_more_thms\<close> --- whose spine-preservation
  assumptions we inherit --- three groups: \<open>sel\<close> must be determined by the element set (see the
  header);  \<open>adjmap\<close> must be blind to the spine, which is automatic when it selects a \<open>'more\<close>
  field; and the callbacks must treat the carried graph correctly --- \<open>on_push u\<close> deletes exactly
  the in-edges of \<open>u\<close>, the others leave it alone.

  \<open>on_push\<close> is only ever asked to delete in-edges of a map that is \<^emph>\<open>below\<close> \<open>G\<close>
  (\<open>[adjmap st]\<^sub>g \<subseteq> [G]\<^sub>g\<close>, which \<open>invar_adj\<close> supplies), and \<open>on_push_digraph_abs\<close> takes that as
  a hypothesis. It has to: an instance deleting the in-edges of \<open>u\<close> via a \<^emph>\<open>static\<close> reverse
  adjacency map of \<open>G\<close> removes \<open>preds\<^sub>G u \<times> {u}\<close>, which coincides with \<open>UNIV \<times> {u}\<close> only on
  sub-maps of \<open>G\<close>.\<close>

locale DFS_skel_more_refine_thms = DFS_skel_more_refine + DFS_skel_more_thms +
  assumes sel_cong: "vset_inv X \<Longrightarrow> vset_inv Y \<Longrightarrow> t_set X = t_set Y \<Longrightarrow> sel X = sel Y"
      and adjmap_stack[simp]: "adjmap (st \<lparr>stack := xs\<rparr>) = adjmap st"
      and adjmap_seen[simp]:  "adjmap (st \<lparr>seen := S\<rparr>) = adjmap st"
      and on_found_adjmap[simp]:     "adjmap (on_found st) = adjmap st"
      and on_empty_adjmap[simp]:     "adjmap (on_empty st) = adjmap st"
      and on_backtrack_adjmap[simp]: "adjmap (on_backtrack v st) = adjmap st"
      and on_push_graph_inv:
            "Graph.graph_inv (adjmap st) \<Longrightarrow> Graph.graph_inv (adjmap (on_push u st))"
      and on_push_digraph_abs:
            "Graph.graph_inv (adjmap st) \<Longrightarrow>
             Graph.digraph_abs (adjmap st) \<subseteq> Graph.digraph_abs G \<Longrightarrow>
               Graph.digraph_abs (adjmap (on_push u st))
                 = Graph.digraph_abs (adjmap st) - (UNIV \<times> {u})"
begin

context
includes Graph.adjmap.automation and Graph.vset.set.automation
begin

subsection \<open>The invariant makes the two neighbour computations agree\<close>

text \<open>The refined loop's \<open>\<N> (adjmap st) v\<close> and the original's \<open>(\<N>\<^sub>G v) -\<^sub>G (seen st)\<close> are
  different vsets --- one built by deletion, the other by \<open>RBT.diff\<close> --- but under the invariant
  they carry the same elements. That is all the loop needs: emptiness is decided by the element set,
  and \<open>sel_cong\<close> makes the choice depend on nothing else.\<close>

lemma adj_nbr_inv:
  assumes "invar_adj st"
  shows "vset_inv (adj_nbr st v)"
  using assms Graph.neighbourhood_invars'[of "adjmap st" v] by (simp add: invar_adj_def)

lemma diff_inv:
  assumes "invar_1 st"
  shows "vset_inv ((\<N>\<^sub>G v) -\<^sub>G (seen st))"
  using assms Graph.neighbourhood_invars'[of G v]
  by (auto simp: invar_1_def set_ops.invar_diff elim!: invar_props_elims)

lemma adj_nbr_set:
  assumes "invar_adj st" and "invar_1 st"
  shows "t_set (adj_nbr st v) = t_set ((\<N>\<^sub>G v) -\<^sub>G (seen st))"
proof -
  have gi: "Graph.graph_inv (adjmap st)"
    and abs: "Graph.digraph_abs (adjmap st)
                = Graph.digraph_abs G - (UNIV \<times> t_set (seen st))"
    using assms(1) by (auto simp: invar_adj_def)
  have "t_set (adj_nbr st v) = {w. (v, w) \<in> Graph.digraph_abs (adjmap st)}"
    by (auto simp: Graph.are_connected_abs_general[OF gi])
  also have "\<dots> = {w. (v, w) \<in> Graph.digraph_abs G} - t_set (seen st)"
    by (auto simp: abs)
  also have "\<dots> = t_set (\<N>\<^sub>G v) - t_set (seen st)"
    by auto
  also have "\<dots> = t_set ((\<N>\<^sub>G v) -\<^sub>G (seen st))"
    using assms(2) by (auto simp: invar_1_def set_ops.set_diff)
  finally show ?thesis .
qed

text \<open>Emptiness \<^emph>\<open>is\<close> decided by the element set: one direction is \<open>t_set \<emptyset>\<^sub>N = {}\<close>, the
  other is \<^locale>\<open>Set_Choose\<close>'s \<open>choose\<close> (a non-empty vset yields a member).\<close>
lemma vset_ne_cong:
  assumes "vset_inv X"
      and "vset_inv Y"
      and "t_set X = t_set Y"
  shows "(X \<noteq> \<emptyset>\<^sub>N) = (Y \<noteq> \<emptyset>\<^sub>N)"
  using assms Graph.vset.emptyD by metis

lemma adj_nbr_empty_iff:
  assumes "invar_adj st" and "invar_1 st"
  shows "(adj_nbr st v \<noteq> \<emptyset>\<^sub>N) = (((\<N>\<^sub>G v) -\<^sub>G (seen st)) \<noteq> \<emptyset>\<^sub>N)"
  by (rule vset_ne_cong[OF adj_nbr_inv[OF assms(1)] diff_inv[OF assms(2)] adj_nbr_set[OF assms]])

lemma adj_nbr_sel:
  assumes "invar_adj st" and "invar_1 st"
  shows "sel (adj_nbr st v) = sel ((\<N>\<^sub>G v) -\<^sub>G (seen st))"
  by (rule sel_cong[OF adj_nbr_inv[OF assms(1)] diff_inv[OF assms(2)] adj_nbr_set[OF assms]])

subsection \<open>Hence the call conditions and the updates coincide\<close>

lemma refine_conds_eq:
  assumes "invar_adj st" and "invar_1 st"
  shows "DFS_skel_more_refine_call_1_conds st = DFS_skel_more_call_1_conds st"
    and "DFS_skel_more_refine_call_2_conds st = DFS_skel_more_call_2_conds st"
    and "DFS_skel_more_refine_ret_1_conds st = DFS_skel_more_ret_1_conds st"
    and "DFS_skel_more_refine_ret_2_conds st = DFS_skel_more_ret_2_conds st"
  using adj_nbr_empty_iff[OF assms]
  by (auto simp: DFS_skel_more_refine_call_1_conds_def DFS_skel_more_call_1_conds_def
                 DFS_skel_more_refine_call_2_conds_def DFS_skel_more_call_2_conds_def
                 DFS_skel_more_refine_ret_1_conds_def DFS_skel_more_ret_1_conds_def
                 DFS_skel_more_refine_ret_2_conds_def DFS_skel_more_ret_2_conds_def
           split: list.splits if_splits)

lemma refine_upd1_eq:
  assumes "invar_adj st" and "invar_1 st"
  shows "DFS_skel_more_refine_upd1 st = DFS_skel_more_upd1 st"
  using adj_nbr_sel[OF assms]
  by (simp add: DFS_skel_more_refine_upd1_def DFS_skel_more_upd1_def Let_def)

lemma refine_upd2_ret_eq:
  "DFS_skel_more_refine_upd2 st = DFS_skel_more_upd2 st"
  "DFS_skel_more_refine_ret1 st = DFS_skel_more_ret1 st"
  "DFS_skel_more_refine_ret2 st = DFS_skel_more_ret2 st"
  by (simp_all add: DFS_skel_more_refine_upd2_def DFS_skel_more_upd2_def
                    DFS_skel_more_refine_ret1_def DFS_skel_more_ret1_def
                    DFS_skel_more_refine_ret2_def DFS_skel_more_ret2_def)

subsection \<open>The invariant is preserved\<close>

text \<open>The push is the interesting case, and it is exactly the design: \<open>seen\<close> gains \<open>u\<close> and
  \<open>adjmap\<close> loses the in-edges of \<open>u\<close>, so the two sides of \<open>invar_adj\<close> move together. The
  backtrack changes neither.\<close>

lemma invar_adj_holds_upd1[invar_holds_intros]:
  assumes "DFS_skel_more_call_1_conds st" and "invar_adj st" and "invar_1 st"
  shows "invar_adj (DFS_skel_more_upd1 st)"
proof -
  let ?u = "sel ((\<N>\<^sub>G (hd (stack st))) -\<^sub>G (seen st))"
  let ?st' = "st \<lparr>stack := ?u # stack st, seen := insert ?u (seen st)\<rparr>"
  have upd: "DFS_skel_more_upd1 st = on_push ?u ?st'"
    by (simp add: DFS_skel_more_upd1_def Let_def)
  have gi: "Graph.graph_inv (adjmap st)"
    and abs: "Graph.digraph_abs (adjmap st)
                = Graph.digraph_abs G - (UNIV \<times> t_set (seen st))"
    using assms(2) by (auto simp: invar_adj_def)
  have sub: "Graph.digraph_abs (adjmap st) \<subseteq> Graph.digraph_abs G"
    by (simp add: abs)
  have adj': "adjmap ?st' = adjmap st" by simp
  have gi': "Graph.graph_inv (adjmap (on_push ?u ?st'))"
    using on_push_graph_inv[of ?st' ?u] gi adj' by simp
  have "Graph.digraph_abs (adjmap (on_push ?u ?st'))
          = Graph.digraph_abs (adjmap st) - (UNIV \<times> {?u})"
    using on_push_digraph_abs[of ?st' ?u] gi sub adj' by simp
  also have "\<dots> = Graph.digraph_abs G - (UNIV \<times> t_set (insert ?u (seen st)))"
    using assms(3) by (auto simp: abs invar_1_def elim!: invar_props_elims)
  finally show ?thesis
    using gi' by (simp add: upd invar_adj_def)
qed

lemma invar_adj_holds_upd2[invar_holds_intros]:
  assumes "invar_adj st"
  shows "invar_adj (DFS_skel_more_upd2 st)"
  using assms by (simp add: invar_adj_def DFS_skel_more_upd2_def)

text \<open>Hence it survives a whole run --- what an instance needs in order to read the carried graph
  off the result and hand it on.\<close>

lemma invar_adj_holds[invar_holds_intros]:
  assumes dom: "DFS_skel_more_dom st" and "invar_adj st" and "invar_1 st"
  shows "invar_adj (DFS_skel_more st)"
  using assms(2-)
proof (induction rule: DFS_skel_more_induct[OF dom])
  case (1 dfs_state)
  show ?case
  proof (rule DFS_skel_more_cases[where dfs_state = dfs_state])
    show ?case if c: "DFS_skel_more_call_1_conds dfs_state"
      using 1(2)[OF c invar_adj_holds_upd1[OF c 1(4,5)] invar_1_holds_1[OF c 1(5)]]
      by (simp add: DFS_skel_more_simps(1)[OF 1(1) c])
    show ?case if c: "DFS_skel_more_call_2_conds dfs_state"
      using 1(3)[OF c invar_adj_holds_upd2[OF 1(4)] invar_1_holds_2[OF c 1(5)]]
      by (simp add: DFS_skel_more_simps(2)[OF 1(1) c])
    show ?case if c: "DFS_skel_more_ret_1_conds dfs_state"
      using 1(4)
      by (simp add: DFS_skel_more_simps(3)[OF 1(1) c] DFS_skel_more_ret1_def invar_adj_def)
    show ?case if c: "DFS_skel_more_ret_2_conds dfs_state"
      using 1(4)
      by (simp add: DFS_skel_more_simps(4)[OF 1(1) c] DFS_skel_more_ret2_def invar_adj_def)
  qed
qed

subsection \<open>Termination transfers both ways\<close>

lemma refine_dom_imp_more_dom:
  assumes "DFS_skel_more_refine_dom st" and "invar_adj st" and "invar_1 st"
  shows "DFS_skel_more_dom st"
  using assms(2-)
proof (induction rule: DFS_skel_more_refine_induct[OF assms(1)])
  case (1 dfs_state)
  show ?case
  proof (rule DFS_skel_more_domintros)
    show "DFS_skel_more_dom (DFS_skel_more_upd1 dfs_state)"
      if c: "DFS_skel_more_call_1_conds dfs_state"
      using 1(2)[OF refine_conds_eq(1)[OF 1(4,5), THEN iffD2, OF c]]
      using invar_adj_holds_upd1[OF c 1(4,5)] invar_1_holds_1[OF c 1(5)]
      by (simp add: refine_upd1_eq[OF 1(4,5)])
  next
    show "DFS_skel_more_dom (DFS_skel_more_upd2 dfs_state)"
      if c: "DFS_skel_more_call_2_conds dfs_state"
      using 1(3)[OF refine_conds_eq(2)[OF 1(4,5), THEN iffD2, OF c]]
      using invar_adj_holds_upd2[OF 1(4)] invar_1_holds_2[OF c 1(5)]
      by (simp add: refine_upd2_ret_eq(1))
  qed
qed

lemma more_dom_imp_refine_dom:
  assumes "DFS_skel_more_dom st" and "invar_adj st" and "invar_1 st"
  shows "DFS_skel_more_refine_dom st"
  using assms(2-)
proof (induction rule: DFS_skel_more_induct[OF assms(1)])
  case (1 dfs_state)
  show ?case
  proof (rule DFS_skel_more_refine_domintros)
    show "DFS_skel_more_refine_dom (DFS_skel_more_refine_upd1 dfs_state)"
      if c: "DFS_skel_more_refine_call_1_conds dfs_state"
    proof -
      have c': "DFS_skel_more_call_1_conds dfs_state"
        using c refine_conds_eq(1)[OF 1(4,5)] by simp
      show ?thesis
        using 1(2)[OF c'] invar_adj_holds_upd1[OF c' 1(4,5)] invar_1_holds_1[OF c' 1(5)]
        by (simp add: refine_upd1_eq[OF 1(4,5)])
    qed
  next
    show "DFS_skel_more_refine_dom (DFS_skel_more_refine_upd2 dfs_state)"
      if c: "DFS_skel_more_refine_call_2_conds dfs_state"
    proof -
      have c': "DFS_skel_more_call_2_conds dfs_state"
        using c refine_conds_eq(2)[OF 1(4,5)] by simp
      show ?thesis
        using 1(3)[OF c'] invar_adj_holds_upd2[OF 1(4)] invar_1_holds_2[OF c' 1(5)]
        by (simp add: refine_upd2_ret_eq(1))
    qed
  qed
qed

theorem DFS_skel_more_refine_dom_iff:
  assumes "invar_adj st" and "invar_1 st"
  shows "DFS_skel_more_refine_dom st \<longleftrightarrow> DFS_skel_more_dom st"
  using refine_dom_imp_more_dom[OF _ assms] more_dom_imp_refine_dom[OF _ assms] by blast

subsection \<open>The equivalence\<close>

text \<open>The two searches agree \<^emph>\<open>as runs\<close>: at every step they take the same branch and push the
  same vertex, and since they share \<open>on_push\<close> the states they build are literally equal --- the
  \<open>'more\<close> slot, carried graph included, evolves identically. So every fact proved of
  \<open>DFS_skel_more\<close> holds of \<open>DFS_skel_more_refine\<close> unchanged.\<close>

theorem DFS_skel_more_refine_eq_DFS_skel_more:
  assumes dom: "DFS_skel_more_refine_dom st" and "invar_adj st" and "invar_1 st"
  shows "DFS_skel_more_refine st = DFS_skel_more st"
  using assms(2-)
proof (induction rule: DFS_skel_more_refine_induct[OF dom])
  case (1 dfs_state)
  have mdom: "DFS_skel_more_dom dfs_state"
    using refine_dom_imp_more_dom[OF 1(1) 1(4,5)] .
  show ?case
  proof (rule DFS_skel_more_refine_cases[where dfs_state = dfs_state])
    show ?case if c: "DFS_skel_more_refine_call_1_conds dfs_state"
    proof -
      have c': "DFS_skel_more_call_1_conds dfs_state"
        using c refine_conds_eq(1)[OF 1(4,5)] by simp
      have "DFS_skel_more_refine dfs_state = DFS_skel_more_refine (DFS_skel_more_refine_upd1 dfs_state)"
        using DFS_skel_more_refine_simps(1)[OF 1(1) c] .
      also have "\<dots> = DFS_skel_more (DFS_skel_more_refine_upd1 dfs_state)"
        using 1(2)[OF c] invar_adj_holds_upd1[OF c' 1(4,5)] invar_1_holds_1[OF c' 1(5)]
        by (simp add: refine_upd1_eq[OF 1(4,5)])
      also have "\<dots> = DFS_skel_more (DFS_skel_more_upd1 dfs_state)"
        by (simp add: refine_upd1_eq[OF 1(4,5)])
      also have "\<dots> = DFS_skel_more dfs_state"
        using DFS_skel_more_simps(1)[OF mdom c'] by simp
      finally show ?thesis .
    qed
    show ?case if c: "DFS_skel_more_refine_call_2_conds dfs_state"
    proof -
      have c': "DFS_skel_more_call_2_conds dfs_state"
        using c refine_conds_eq(2)[OF 1(4,5)] by simp
      have "DFS_skel_more_refine dfs_state = DFS_skel_more_refine (DFS_skel_more_refine_upd2 dfs_state)"
        using DFS_skel_more_refine_simps(2)[OF 1(1) c] .
      also have "\<dots> = DFS_skel_more (DFS_skel_more_refine_upd2 dfs_state)"
        using 1(3)[OF c] invar_adj_holds_upd2[OF 1(4)] invar_1_holds_2[OF c' 1(5)]
        by (simp add: refine_upd2_ret_eq(1))
      also have "\<dots> = DFS_skel_more (DFS_skel_more_upd2 dfs_state)"
        by (simp add: refine_upd2_ret_eq(1))
      also have "\<dots> = DFS_skel_more dfs_state"
        using DFS_skel_more_simps(2)[OF mdom c'] by simp
      finally show ?thesis .
    qed
    show ?case if c: "DFS_skel_more_refine_ret_1_conds dfs_state"
      using DFS_skel_more_refine_simps(3)[OF 1(1) c]
      using DFS_skel_more_simps(3)[OF mdom refine_conds_eq(3)[OF 1(4,5), THEN iffD1, OF c]]
      by (simp add: refine_upd2_ret_eq)
    show ?case if c: "DFS_skel_more_refine_ret_2_conds dfs_state"
      using DFS_skel_more_refine_simps(4)[OF 1(1) c]
      using DFS_skel_more_simps(4)[OF mdom refine_conds_eq(4)[OF 1(4,5), THEN iffD1, OF c]]
      by (simp add: refine_upd2_ret_eq)
  qed
qed

text \<open>The executable form, for the code generator: it is the refined loop that runs, and it agrees
  with the original's specification.\<close>

corollary DFS_skel_more_refine_impl_eq_DFS_skel_more:
  assumes "DFS_skel_more_refine_dom st" and "invar_adj st" and "invar_1 st"
  shows "DFS_skel_more_refine_impl st = DFS_skel_more st"
  using DFS_skel_more_refine_impl_same[OF assms(1)] DFS_skel_more_refine_eq_DFS_skel_more[OF assms] by simp

end

end

end
