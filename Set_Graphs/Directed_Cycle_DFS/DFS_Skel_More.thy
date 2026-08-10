theory DFS_Skel_More
  imports DFS_Skeleton
begin

text \<open>A \<^emph>\<open>duplicate\<close> of the graph library's generic DFS skeleton
  (\<open>DFS_Skeleton\<close>, the skeleton \<open>DFS_DirCycle\<close> is built
  on) whose sole change is one further callback, \<open>on_push\<close>, applied to the freshly-pushed state
  in the descend step:

    \<open>DFS_skel_more (on_push u (dfs_state \<lparr>stack := stack', seen := seen'\<rparr>))\<close>

  The library's skeleton hard-codes that step as
  \<open>DFS_skel (dfs_state \<lparr>stack := stack', seen := seen'\<rparr>)\<close>, hooking only the backtrack, so an
  instance cannot maintain state that must change when a vertex \<^emph>\<open>enters\<close> the stack. In
  particular the set of gray (on-stack) vertices cannot be carried explicitly: the library's
  directed-cycle detector is forced to rebuild it as \<open>seen - finished\<close> by an \<open>O(V)\<close> set
  difference at \<^emph>\<open>every\<close> skeleton step, making the DFS \<open>O(V \<cdot> (V + E))\<close> instead of
  \<open>O(V + E)\<close>. With \<open>on_push\<close> an instance maintains gray (and, dually, an \<open>unfinished\<close> set for
  an outer whole-graph sweep) incrementally.

  \<open>on_push\<close> runs \<^emph>\<open>after\<close> the stack/seen update and carries the same spine-preservation
  contract as the other callbacks (it must not disturb \<open>stack\<close>/\<open>seen\<close>); everything else ---
  state type (generic in the extensible-record slot \<open>'more\<close>), step structure, call/return
  conditions, invariants, termination --- is the library's, verbatim.

  Two theorems below justify the duplication, by comparing \<open>DFS_skel_more\<close> against the
  library's \<open>DFS_skel\<close> interpreted with the same graph and callbacks (the \<open>plain:\<close>
  sublocale):
  \<^item> \<open>DFS_skel_more_eq_DFS_skel\<close>: with the identity hook \<open>on_push = (\<lambda>u st. st)\<close> the two
    functions (and their domains, \<open>DFS_skel_more_dom_iff_id_push\<close>) coincide outright ---
    the conservativity check that the duplicate did not change the skeleton's semantics.
  \<^item> \<open>DFS_skel_more_stack_eq\<close>/\<open>DFS_skel_more_seen_eq\<close> (with \<open>DFS_skel_more_dom_iff\<close>): for an
    \<^emph>\<open>arbitrary\<close> spine-preserving \<open>on_push\<close>, both runs take the same branches and agree on
    \<open>stack\<close> and \<open>seen\<close> --- \<^emph>\<open>provided\<close> \<open>found\<close> is spine-determined (equal on states with
    equal \<open>stack\<close>/\<open>seen\<close>). That hypothesis is not dischargeable in general: \<open>found\<close> may read
    the \<open>'more\<close> slot, which \<open>DFS_skel\<close> --- never applying \<open>on_push\<close> --- does not maintain,
    so without it the runs can branch apart. Caveat: our instantiation
    \<open>DFS_dircycle_tracked\<close> does \<^emph>\<open>not\<close> satisfy it as a raw property of \<open>cyc_found\<close> (which
    reads \<open>gray\<close>); it holds only along reachable states via the invariant
    \<open>t_set (gray st) = set (stack st)\<close> (\<open>invar_gray_stack\<close> in \<open>DFS_DirCycle_Tracked\<close>), so
    the agreement theorems do not apply to the tracked DFS off the shelf.

  The spine is exactly what the library skeleton's own machinery reads --- its \<open>invar_1\<close> is
  \<open>vset_inv (seen st)\<close>, and its domain predicate and termination measures depend only on
  \<open>stack\<close>/\<open>seen\<close> --- so spine agreement is what makes the duplication safe, and it is the
  route by which \<open>DFS_skel\<close>'s termination and invariant results could later be transferred
  here rather than re-proved. This duplication should still be resolved upstream by adding
  \<open>on_push\<close> to the library's \<open>DFS_Skeleton\<close> itself, after which this theory disappears.\<close>

locale DFS_skel_more =
  Graph: Pair_Graph_Specs where lookup = lookup +
 set_ops: Set2 vset_empty vset_delete _ t_set vset_inv insert
for lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option" +
fixes G::"'adjmap" and s::"'v"
  and found       :: "('v,'vset,'more) DFS_skel_state_scheme \<Rightarrow> bool"
  and on_found    :: "('v,'vset,'more) DFS_skel_state_scheme \<Rightarrow> ('v,'vset,'more) DFS_skel_state_scheme"
  and on_empty    :: "('v,'vset,'more) DFS_skel_state_scheme \<Rightarrow> ('v,'vset,'more) DFS_skel_state_scheme"
  and on_backtrack:: "'v \<Rightarrow> ('v,'vset,'more) DFS_skel_state_scheme \<Rightarrow> ('v,'vset,'more) DFS_skel_state_scheme"
  and on_push     :: "'v \<Rightarrow> ('v,'vset,'more) DFS_skel_state_scheme \<Rightarrow> ('v,'vset,'more) DFS_skel_state_scheme"
begin

abbreviation "neighbourhood' \<equiv> Graph.neighbourhood G"
notation "neighbourhood'" ("\<N>\<^sub>G _" 100)

function (domintros) DFS_skel_more::"('v,'vset,'more) DFS_skel_state_scheme \<Rightarrow> ('v,'vset,'more) DFS_skel_state_scheme" where
  "DFS_skel_more dfs_state =
     (case (stack dfs_state) of (v # stack_tl) \<Rightarrow>
       (if found dfs_state then on_found dfs_state
        else (if ((\<N>\<^sub>G v) -\<^sub>G (seen dfs_state)) \<noteq> \<emptyset>\<^sub>N then
                let u = (sel ((\<N>\<^sub>G v) -\<^sub>G (seen dfs_state)));
                    stack' = u # (stack dfs_state);
                    seen' = insert u (seen dfs_state)
                in DFS_skel_more (on_push u (dfs_state \<lparr>stack := stack', seen := seen'\<rparr>))
              else
                DFS_skel_more (on_backtrack v (dfs_state \<lparr>stack := stack_tl\<rparr>))))
     | _ \<Rightarrow> on_empty dfs_state)"
  by pat_completeness auto

partial_function (tailrec) DFS_skel_more_impl::"('v,'vset,'more) DFS_skel_state_scheme \<Rightarrow> ('v,'vset,'more) DFS_skel_state_scheme" where
  "DFS_skel_more_impl dfs_state =
     (case (stack dfs_state) of (v # stack_tl) \<Rightarrow>
       (if found dfs_state then on_found dfs_state
        else (if ((\<N>\<^sub>G v) -\<^sub>G (seen dfs_state)) \<noteq> \<emptyset>\<^sub>N then
                let u = (sel ((\<N>\<^sub>G v) -\<^sub>G (seen dfs_state)));
                    stack' = u # (stack dfs_state);
                    seen' = insert u (seen dfs_state)
                in DFS_skel_more_impl (on_push u (dfs_state \<lparr>stack := stack', seen := seen'\<rparr>))
              else
                DFS_skel_more_impl (on_backtrack v (dfs_state \<lparr>stack := stack_tl\<rparr>))))
     | _ \<Rightarrow> on_empty dfs_state)"

lemmas [code] = DFS_skel_more_impl.simps

lemma DFS_skel_more_impl_same:
  assumes "DFS_skel_more_dom state"
  shows   "DFS_skel_more_impl state = DFS_skel_more state"
  by(induction rule: DFS_skel_more.pinduct[OF assms])
    (subst DFS_skel_more.psimps, simp, subst DFS_skel_more_impl.simps,
     auto split: list.split if_split simp add: Let_def)

definition "DFS_skel_more_call_1_conds dfs_state =
    (case (stack dfs_state) of (v # stack_tl) \<Rightarrow>
       (if found dfs_state then False
        else (if ((\<N>\<^sub>G v) -\<^sub>G (seen dfs_state)) \<noteq> \<emptyset>\<^sub>N then True else False))
     | _ \<Rightarrow> False)"

lemma DFS_skel_more_call_1_conds[call_cond_elims]:
  "DFS_skel_more_call_1_conds dfs_state \<Longrightarrow>
   \<lbrakk>\<lbrakk>\<exists>v stack_tl. stack dfs_state = v # stack_tl;
    \<not> found dfs_state;
    (\<N>\<^sub>G (hd (stack dfs_state))) -\<^sub>G (seen dfs_state) \<noteq> \<emptyset>\<^sub>N\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto simp: DFS_skel_more_call_1_conds_def split: list.splits option.splits if_splits)

definition "DFS_skel_more_upd1 dfs_state = (
    let
      N = (\<N>\<^sub>G (hd (stack dfs_state)));
      u = (sel ((N -\<^sub>G (seen dfs_state))));
      stack' = u # (stack dfs_state);
      seen' = insert u (seen dfs_state)
    in
      on_push u (dfs_state \<lparr>stack := stack', seen := seen'\<rparr>))"

definition "DFS_skel_more_call_2_conds dfs_state =
    (case (stack dfs_state) of (v # stack_tl) \<Rightarrow>
       (if found dfs_state then False
        else (if ((\<N>\<^sub>G v) -\<^sub>G (seen dfs_state)) \<noteq> \<emptyset>\<^sub>N then False else True))
     | _ \<Rightarrow> False)"

lemma DFS_skel_more_call_2_conds[call_cond_elims]:
  "DFS_skel_more_call_2_conds dfs_state \<Longrightarrow>
   \<lbrakk>\<lbrakk>\<exists>v stack_tl. stack dfs_state = v # stack_tl;
    \<not> found dfs_state;
    (\<N>\<^sub>G (hd (stack dfs_state))) -\<^sub>G (seen dfs_state) = \<emptyset>\<^sub>N\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto simp: DFS_skel_more_call_2_conds_def split: list.splits option.splits if_splits)

definition "DFS_skel_more_upd2 dfs_state =
  on_backtrack (hd (stack dfs_state)) (dfs_state \<lparr>stack := tl (stack dfs_state)\<rparr>)"

definition "DFS_skel_more_ret_1_conds dfs_state =
    (case (stack dfs_state) of (v # stack_tl) \<Rightarrow> False | _ \<Rightarrow> True)"

lemma DFS_skel_more_ret_1_conds[call_cond_elims]:
  "DFS_skel_more_ret_1_conds dfs_state \<Longrightarrow> \<lbrakk>\<lbrakk>stack dfs_state = []\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto simp: DFS_skel_more_ret_1_conds_def split: list.splits if_splits)

lemma DFS_skel_more_ret_1_condsI[call_cond_intros]:
  "\<lbrakk>stack dfs_state = []\<rbrakk> \<Longrightarrow> DFS_skel_more_ret_1_conds dfs_state"
  by(auto simp: DFS_skel_more_ret_1_conds_def split: list.splits if_splits)

definition "DFS_skel_more_ret1 dfs_state = on_empty dfs_state"

definition "DFS_skel_more_ret_2_conds dfs_state =
    (case (stack dfs_state) of (v # stack_tl) \<Rightarrow> (if found dfs_state then True else False) | _ \<Rightarrow> False)"

lemma DFS_skel_more_ret_2_conds[call_cond_elims]:
  "DFS_skel_more_ret_2_conds dfs_state \<Longrightarrow>
   \<lbrakk>\<lbrakk>\<exists>v stack_tl. stack dfs_state = v # stack_tl; found dfs_state\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto simp: DFS_skel_more_ret_2_conds_def split: list.splits if_splits)

lemma DFS_skel_more_ret_2_condsI[call_cond_intros]:
  "\<lbrakk>\<exists>v stack_tl. stack dfs_state = v # stack_tl; found dfs_state\<rbrakk> \<Longrightarrow> DFS_skel_more_ret_2_conds dfs_state"
  by(auto simp: DFS_skel_more_ret_2_conds_def split: list.splits if_splits)

definition "DFS_skel_more_ret2 dfs_state = on_found dfs_state"

lemma DFS_skel_more_cases:
  assumes "DFS_skel_more_call_1_conds dfs_state \<Longrightarrow> P"
      "DFS_skel_more_call_2_conds dfs_state \<Longrightarrow> P"
      "DFS_skel_more_ret_1_conds dfs_state \<Longrightarrow> P"
      "DFS_skel_more_ret_2_conds dfs_state \<Longrightarrow> P"
  shows "P"
proof-
  have "DFS_skel_more_call_1_conds dfs_state \<or> DFS_skel_more_call_2_conds dfs_state \<or>
        DFS_skel_more_ret_1_conds dfs_state \<or> DFS_skel_more_ret_2_conds dfs_state"
    by (auto simp add: DFS_skel_more_call_1_conds_def DFS_skel_more_call_2_conds_def
                        DFS_skel_more_ret_1_conds_def DFS_skel_more_ret_2_conds_def
           split: list.split_asm option.split_asm if_splits)
  then show ?thesis
    using assms by auto
qed

lemma DFS_skel_more_simps:
  assumes "DFS_skel_more_dom dfs_state"
  shows "DFS_skel_more_call_1_conds dfs_state \<Longrightarrow> DFS_skel_more dfs_state = DFS_skel_more (DFS_skel_more_upd1 dfs_state)"
      "DFS_skel_more_call_2_conds dfs_state \<Longrightarrow> DFS_skel_more dfs_state = DFS_skel_more (DFS_skel_more_upd2 dfs_state)"
      "DFS_skel_more_ret_1_conds dfs_state \<Longrightarrow> DFS_skel_more dfs_state = DFS_skel_more_ret1 dfs_state"
      "DFS_skel_more_ret_2_conds dfs_state \<Longrightarrow> DFS_skel_more dfs_state = DFS_skel_more_ret2 dfs_state"
  by (auto simp add: DFS_skel_more.psimps[OF assms] Let_def
                       DFS_skel_more_call_1_conds_def DFS_skel_more_upd1_def DFS_skel_more_call_2_conds_def DFS_skel_more_upd2_def
                       DFS_skel_more_ret_1_conds_def DFS_skel_more_ret1_def
                       DFS_skel_more_ret_2_conds_def DFS_skel_more_ret2_def
            split: list.splits option.splits if_splits)

lemma DFS_skel_more_induct:
  assumes "DFS_skel_more_dom dfs_state"
  assumes "\<And>dfs_state. \<lbrakk>DFS_skel_more_dom dfs_state;
                        DFS_skel_more_call_1_conds dfs_state \<Longrightarrow> P (DFS_skel_more_upd1 dfs_state);
                        DFS_skel_more_call_2_conds dfs_state \<Longrightarrow> P (DFS_skel_more_upd2 dfs_state)\<rbrakk> \<Longrightarrow> P dfs_state"
  shows "P dfs_state"
  apply(rule DFS_skel_more.pinduct[OF assms(1)])
  apply(rule assms(2)[simplified DFS_skel_more_call_1_conds_def DFS_skel_more_upd1_def DFS_skel_more_call_2_conds_def DFS_skel_more_upd2_def])
  by (auto simp: Let_def split: list.splits option.splits if_splits)

lemma DFS_skel_more_domintros:
  assumes "DFS_skel_more_call_1_conds dfs_state \<Longrightarrow> DFS_skel_more_dom (DFS_skel_more_upd1 dfs_state)"
  assumes "DFS_skel_more_call_2_conds dfs_state \<Longrightarrow> DFS_skel_more_dom (DFS_skel_more_upd2 dfs_state)"
  shows "DFS_skel_more_dom dfs_state"
proof(rule DFS_skel_more.domintros, goal_cases)
  case (1 x21 x22)
  then show ?case
    using assms(1)[simplified DFS_skel_more_call_1_conds_def DFS_skel_more_upd1_def]
    by (force simp: Let_def split: list.splits option.splits if_splits)
next
  case (2 x21 x22)
  then show ?case
    using assms(2)[simplified DFS_skel_more_call_2_conds_def DFS_skel_more_upd2_def]
    by (force simp: Let_def split: list.splits option.splits if_splits)
qed

definition "DFS_skel_more_axioms = (Graph.graph_inv G \<and> Graph.finite_graph G \<and> Graph.finite_vsets G)"

definition "invar_1 dfs_state = vset_inv (seen dfs_state)"

definition "invar_seen_stack dfs_state \<longleftrightarrow>
    distinct (stack dfs_state)
    \<and> set (stack dfs_state) \<subseteq> t_set (seen dfs_state)
    \<and> t_set (seen dfs_state) \<subseteq> dVs (Graph.digraph_abs G)"

definition "call_1_measure dfs_state = card (dVs (Graph.digraph_abs G) - t_set (seen dfs_state))"

definition "call_2_measure dfs_state = card (set (stack dfs_state))"

definition "DFS_skel_more_term_rel' = (call_1_measure) <*mlex*> (call_2_measure) <*mlex*> {}"

end

text \<open>Comparison with the library skeleton. The interpretation \<open>plain\<close> is the library's
  \<open>DFS_skel\<close> over the same graph and the same \<open>found\<close>/\<open>on_found\<close>/\<open>on_empty\<close>/\<open>on_backtrack\<close>
  --- the run that never applies \<open>on_push\<close>. \<open>DFS_skel_state.truncate\<close> projects a state scheme
  onto the spine (\<open>stack\<close>, \<open>seen\<close>), i.e. onto exactly the fields \<open>DFS_skel\<close> references.\<close>

lemma DFS_skel_state_truncate_stack:
  "stack (DFS_skel_state.truncate st) = stack st"
  by (simp add: DFS_skel_state.truncate_def)

lemma DFS_skel_state_truncate_seen:
  "seen (DFS_skel_state.truncate st) = seen st"
  by (simp add: DFS_skel_state.truncate_def)

lemma DFS_skel_state_truncate_eq_iff:
  "DFS_skel_state.truncate st1 = DFS_skel_state.truncate st2 \<longleftrightarrow>
     stack st1 = stack st2 \<and> seen st1 = seen st2"
  by (simp add: DFS_skel_state.truncate_def)

sublocale DFS_skel_more \<subseteq> plain: DFS_skel
  where lookup = lookup and G = G and s = s and found = found
    and on_found = on_found and on_empty = on_empty and on_backtrack = on_backtrack
  by intro_locales

context DFS_skel_more
begin

text \<open>The call/return conditions are spine-determined: they transfer between the two
  skeletons across any two states that agree on \<open>stack\<close>, \<open>seen\<close> and \<open>found\<close>.\<close>

lemma plain_call_1_conds_spine:
  assumes "stack st1 = stack st2"
      and "seen st1 = seen st2"
      and "found st1 = found st2"
  shows "DFS_skel_more_call_1_conds st1 = plain.DFS_skel_call_1_conds st2"
  using assms
  by (auto simp: DFS_skel_more_call_1_conds_def plain.DFS_skel_call_1_conds_def
           split: list.splits if_splits)

lemma plain_call_2_conds_spine:
  assumes "stack st1 = stack st2"
      and "seen st1 = seen st2"
      and "found st1 = found st2"
  shows "DFS_skel_more_call_2_conds st1 = plain.DFS_skel_call_2_conds st2"
  using assms
  by (auto simp: DFS_skel_more_call_2_conds_def plain.DFS_skel_call_2_conds_def
           split: list.splits if_splits)

lemma plain_ret_1_conds_spine:
  assumes "stack st1 = stack st2"
  shows "DFS_skel_more_ret_1_conds st1 = plain.DFS_skel_ret_1_conds st2"
  using assms
  by (auto simp: DFS_skel_more_ret_1_conds_def plain.DFS_skel_ret_1_conds_def
           split: list.splits)

lemma plain_ret_2_conds_spine:
  assumes "stack st1 = stack st2"
      and "found st1 = found st2"
  shows "DFS_skel_more_ret_2_conds st1 = plain.DFS_skel_ret_2_conds st2"
  using assms
  by (auto simp: DFS_skel_more_ret_2_conds_def plain.DFS_skel_ret_2_conds_def
           split: list.splits if_splits)

lemmas plain_conds_eq =
  plain_call_1_conds_spine[OF refl refl refl]
  plain_call_2_conds_spine[OF refl refl refl]
  plain_ret_1_conds_spine[OF refl]
  plain_ret_2_conds_spine[OF refl refl]

lemma plain_upd2_ret_eq:
  "DFS_skel_more_upd2 st = plain.DFS_skel_upd2 st"
  "DFS_skel_more_ret1 st = plain.DFS_skel_ret1 st"
  "DFS_skel_more_ret2 st = plain.DFS_skel_ret2 st"
  by (simp_all add: DFS_skel_more_upd2_def plain.DFS_skel_upd2_def
      DFS_skel_more_ret1_def plain.DFS_skel_ret1_def
      DFS_skel_more_ret2_def plain.DFS_skel_ret2_def)

text \<open>The degenerate (conservativity) check: with the identity push hook the two recursions
  are syntactically identical, so \<open>DFS_skel_more\<close> \<^emph>\<open>is\<close> \<open>DFS_skel\<close> --- same domain, same
  result. No spine-preservation axioms are needed for this.\<close>

lemma plain_upd1_eq_id_push:
  assumes "on_push = (\<lambda>u st. st)"
  shows "DFS_skel_more_upd1 st = plain.DFS_skel_upd1 st"
  unfolding DFS_skel_more_upd1_def plain.DFS_skel_upd1_def
  by (simp add: assms)

lemma plain_dom_id_push:
  assumes idp: "on_push = (\<lambda>u st. st)"
      and dom: "DFS_skel_more_dom st"
  shows "plain.DFS_skel_dom st"
proof (induction rule: DFS_skel_more_induct[OF dom])
  case (1 dfs_state)
  show ?case
  proof (rule plain.DFS_skel_domintros)
    show "plain.DFS_skel_dom (plain.DFS_skel_upd1 dfs_state)"
      if "plain.DFS_skel_call_1_conds dfs_state"
      using 1(2) that
      by (simp add: plain_conds_eq plain_upd1_eq_id_push[OF idp, symmetric])
    show "plain.DFS_skel_dom (plain.DFS_skel_upd2 dfs_state)"
      if "plain.DFS_skel_call_2_conds dfs_state"
      using 1(3) that
      by (simp add: plain_conds_eq plain_upd2_ret_eq(1)[symmetric])
  qed
qed

lemma more_dom_id_push:
  assumes idp: "on_push = (\<lambda>u st. st)"
      and dom: "plain.DFS_skel_dom st"
  shows "DFS_skel_more_dom st"
proof (induction rule: plain.DFS_skel_induct[OF dom])
  case (1 dfs_state)
  show ?case
  proof (rule DFS_skel_more_domintros)
    show "DFS_skel_more_dom (DFS_skel_more_upd1 dfs_state)"
      if "DFS_skel_more_call_1_conds dfs_state"
      using 1(2) that
      by (simp add: plain_conds_eq plain_upd1_eq_id_push[OF idp])
    show "DFS_skel_more_dom (DFS_skel_more_upd2 dfs_state)"
      if "DFS_skel_more_call_2_conds dfs_state"
      using 1(3) that
      by (simp add: plain_conds_eq plain_upd2_ret_eq(1))
  qed
qed

lemma DFS_skel_more_dom_iff_id_push:
  assumes "on_push = (\<lambda>u st. st)"
  shows "DFS_skel_more_dom st \<longleftrightarrow> plain.DFS_skel_dom st"
  using plain_dom_id_push[OF assms] more_dom_id_push[OF assms]
  by blast

theorem DFS_skel_more_eq_DFS_skel:
  assumes idp: "on_push = (\<lambda>u st. st)"
      and dom: "DFS_skel_more_dom st"
  shows "DFS_skel_more st = plain.DFS_skel st"
proof (induction rule: DFS_skel_more_induct[OF dom])
  case (1 dfs_state)
  have pdom: "plain.DFS_skel_dom dfs_state"
    using plain_dom_id_push[OF idp 1(1)] .
  show ?case
  proof (rule DFS_skel_more_cases[where dfs_state = dfs_state])
    show ?case if c: "DFS_skel_more_call_1_conds dfs_state"
    proof -
      have "DFS_skel_more dfs_state = DFS_skel_more (DFS_skel_more_upd1 dfs_state)"
        using DFS_skel_more_simps(1)[OF 1(1) c] .
      also have "\<dots> = plain.DFS_skel (DFS_skel_more_upd1 dfs_state)"
        using 1(2)[OF c] .
      also have "\<dots> = plain.DFS_skel (plain.DFS_skel_upd1 dfs_state)"
        by (simp add: plain_upd1_eq_id_push[OF idp])
      also have "\<dots> = plain.DFS_skel dfs_state"
        using plain.DFS_skel_simps(1)[OF pdom] c
        by (simp add: plain_conds_eq)
      finally show ?thesis .
    qed
    show ?case if c: "DFS_skel_more_call_2_conds dfs_state"
    proof -
      have "DFS_skel_more dfs_state = DFS_skel_more (DFS_skel_more_upd2 dfs_state)"
        using DFS_skel_more_simps(2)[OF 1(1) c] .
      also have "\<dots> = plain.DFS_skel (DFS_skel_more_upd2 dfs_state)"
        using 1(3)[OF c] .
      also have "\<dots> = plain.DFS_skel (plain.DFS_skel_upd2 dfs_state)"
        by (simp add: plain_upd2_ret_eq(1))
      also have "\<dots> = plain.DFS_skel dfs_state"
        using plain.DFS_skel_simps(2)[OF pdom] c
        by (simp add: plain_conds_eq)
      finally show ?thesis .
    qed
    show ?case if c: "DFS_skel_more_ret_1_conds dfs_state"
      using DFS_skel_more_simps(3)[OF 1(1) c] plain.DFS_skel_simps(3)[OF pdom] c
      by (simp add: plain_conds_eq plain_upd2_ret_eq)
    show ?case if c: "DFS_skel_more_ret_2_conds dfs_state"
      using DFS_skel_more_simps(4)[OF 1(1) c] plain.DFS_skel_simps(4)[OF pdom] c
      by (simp add: plain_conds_eq plain_upd2_ret_eq)
  qed
qed

end

text \<open>The reasoning layer: the callbacks --- now including \<open>on_push\<close> --- must not disturb the
search spine (stack/seen), and the graph is well-formed. Under these the structural invariants
and termination hold generically.\<close>

locale DFS_skel_more_thms = DFS_skel_more +
  assumes DFS_skel_more_axioms: DFS_skel_more_axioms
    and on_found_stack[simp]:     "stack (on_found st) = stack st"
    and on_found_seen[simp]:      "seen (on_found st) = seen st"
    and on_empty_stack[simp]:     "stack (on_empty st) = stack st"
    and on_empty_seen[simp]:      "seen (on_empty st) = seen st"
    and on_backtrack_stack[simp]: "stack (on_backtrack v st) = stack st"
    and on_backtrack_seen[simp]:  "seen (on_backtrack v st) = seen st"
    and on_push_stack[simp]:      "stack (on_push u st) = stack st"
    and on_push_seen[simp]:       "seen (on_push u st) = seen st"
begin

context
includes set_ops.automation2 and Graph.adjmap.automation and Graph.vset.set.automation
begin

lemma graph_inv[simp,intro]:
          "Graph.graph_inv G"
          "Graph.finite_graph G"
          "Graph.finite_vsets G"
  using DFS_skel_more_axioms
  by (auto simp: DFS_skel_more_axioms_def)

lemma finite_neighbourhoods[simp]:
          "lookup G v = Some N \<Longrightarrow> finite (t_set N)"
  using graph_inv(3)
  by fastforce

lemmas simps[simp] = Graph.neighbourhood_abs[OF graph_inv(1)] Graph.are_connected_abs[OF graph_inv(1)]

lemma invar_1_props[invar_props_elims]:
  "invar_1 dfs_state \<Longrightarrow> (\<lbrakk>vset_inv (seen dfs_state)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_1_def)

lemma invar_1_intro[invar_props_intros]: "\<lbrakk>vset_inv (seen dfs_state)\<rbrakk> \<Longrightarrow> invar_1 dfs_state"
  by (auto simp: invar_1_def)

lemma invar_1_holds_1[invar_holds_intros]:
  "\<lbrakk>DFS_skel_more_call_1_conds dfs_state; invar_1 dfs_state\<rbrakk> \<Longrightarrow> invar_1 (DFS_skel_more_upd1 dfs_state)"
  by (auto simp: Let_def DFS_skel_more_upd1_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_1_holds_2[invar_holds_intros]:
  "\<lbrakk>DFS_skel_more_call_2_conds dfs_state; invar_1 dfs_state\<rbrakk> \<Longrightarrow> invar_1 (DFS_skel_more_upd2 dfs_state)"
  by (auto simp: DFS_skel_more_upd2_def elim!: invar_props_elims intro: invar_props_intros)

lemma invar_1_holds_4[invar_holds_intros]:
  "\<lbrakk>DFS_skel_more_ret_1_conds dfs_state; invar_1 dfs_state\<rbrakk> \<Longrightarrow> invar_1 (DFS_skel_more_ret1 dfs_state)"
  by (auto elim!: invar_props_elims intro: invar_props_intros simp: DFS_skel_more_ret1_def)

lemma invar_1_holds_5[invar_holds_intros]:
  "\<lbrakk>DFS_skel_more_ret_2_conds dfs_state; invar_1 dfs_state\<rbrakk> \<Longrightarrow> invar_1 (DFS_skel_more_ret2 dfs_state)"
  by (auto elim!: invar_props_elims intro: invar_props_intros simp: DFS_skel_more_ret2_def)

lemma invar_1_holds[invar_holds_intros]:
   assumes "DFS_skel_more_dom dfs_state" "invar_1 dfs_state"
   shows "invar_1 (DFS_skel_more dfs_state)"
  using assms(2)
proof(induction rule: DFS_skel_more_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule DFS_skel_more_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-4) invar_holds_intros simp: DFS_skel_more_simps[OF IH(1)])
qed

lemma invar_seen_stack_props[invar_props_elims]:
   "invar_seen_stack dfs_state \<Longrightarrow>
     (\<lbrakk>distinct (stack dfs_state); set (stack dfs_state) \<subseteq> t_set (seen dfs_state);
       t_set (seen dfs_state) \<subseteq> dVs (Graph.digraph_abs G)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P "
  by (auto simp: invar_seen_stack_def)

lemma invar_seen_stack_intro[invar_props_intros]:
  "\<lbrakk>distinct (stack dfs_state); set (stack dfs_state) \<subseteq> t_set (seen dfs_state);
    t_set (seen dfs_state) \<subseteq> dVs (Graph.digraph_abs G)\<rbrakk> \<Longrightarrow> invar_seen_stack dfs_state"
  by (auto simp: invar_seen_stack_def)

lemma invar_seen_stack_holds_1[invar_holds_intros]:
  "\<lbrakk>DFS_skel_more_call_1_conds dfs_state; invar_1 dfs_state; invar_seen_stack dfs_state\<rbrakk> \<Longrightarrow>
     invar_seen_stack (DFS_skel_more_upd1 dfs_state)"
  by (force simp: Let_def DFS_skel_more_upd1_def elim!: call_cond_elims
            elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_seen_stack_holds_2[invar_holds_intros]:
  "\<lbrakk>DFS_skel_more_call_2_conds dfs_state; invar_1 dfs_state; invar_seen_stack dfs_state\<rbrakk> \<Longrightarrow>
     invar_seen_stack (DFS_skel_more_upd2 dfs_state)"
  by (auto elim!: call_cond_elims simp: DFS_skel_more_upd2_def
           elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_seen_stack_holds_4[invar_holds_intros]:
   "\<lbrakk>DFS_skel_more_ret_1_conds dfs_state; invar_seen_stack dfs_state\<rbrakk> \<Longrightarrow>
       invar_seen_stack (DFS_skel_more_ret1 dfs_state)"
  by (auto elim!: invar_props_elims intro!: invar_props_intros simp: DFS_skel_more_ret1_def)

lemma invar_seen_stack_holds_5[invar_holds_intros]:
   "\<lbrakk>DFS_skel_more_ret_2_conds dfs_state; invar_seen_stack dfs_state\<rbrakk> \<Longrightarrow>
       invar_seen_stack (DFS_skel_more_ret2 dfs_state)"
  by (auto elim!: invar_props_elims intro!: invar_props_intros simp: DFS_skel_more_ret2_def)

lemma invar_seen_stack_holds[invar_holds_intros]:
   assumes "DFS_skel_more_dom dfs_state" "invar_1 dfs_state" "invar_seen_stack dfs_state"
   shows "invar_seen_stack (DFS_skel_more dfs_state)"
   using assms(2-)
proof(induction rule: DFS_skel_more_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule DFS_skel_more_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-5) invar_holds_intros simp: DFS_skel_more_simps[OF IH(1)])
qed

named_theorems termination_intros

lemma in_prod_relI[intro!,termination_intros]:
  "\<lbrakk>f1 a = f1 a'; (a, a') \<in> f2 <*mlex*> r\<rbrakk> \<Longrightarrow> (a,a') \<in> (f1 <*mlex*> f2 <*mlex*> r)"
   by (simp add: mlex_iff)

definition "less_rel = {(x::nat, y::nat). x < y}"

lemma wf_less_rel[intro!]: "wf less_rel"
  by(auto simp: less_rel_def wf_less)

lemma call_1_measure_nonsym[simp]: "(call_1_measure dfs_state, call_1_measure dfs_state) \<notin> less_rel"
  by (auto simp: less_rel_def)

lemma call_1_terminates[termination_intros]:
  "\<lbrakk>DFS_skel_more_call_1_conds dfs_state; invar_1 dfs_state; invar_seen_stack dfs_state\<rbrakk> \<Longrightarrow>
     (DFS_skel_more_upd1 dfs_state, dfs_state) \<in> call_1_measure <*mlex*> r"
  by(fastforce elim!: invar_props_elims call_cond_elims
          simp add: DFS_skel_more_upd1_def call_1_measure_def Let_def
          intro!: mlex_less psubset_card_mono
          dest!: Graph.vset.choose')

lemma call_2_measure_nonsym[simp]: "(call_2_measure dfs_state, call_2_measure dfs_state) \<notin> less_rel"
  by (auto simp: less_rel_def)

lemma call_2_measure_1[termination_intros]:
  "\<lbrakk>DFS_skel_more_call_2_conds dfs_state; invar_1 dfs_state\<rbrakk> \<Longrightarrow>
    call_1_measure dfs_state = call_1_measure (DFS_skel_more_upd2 dfs_state)"
  by(auto simp add: DFS_skel_more_upd2_def call_1_measure_def Let_def)

lemma call_2_terminates[termination_intros]:
  "\<lbrakk>DFS_skel_more_call_2_conds dfs_state; invar_1 dfs_state; invar_seen_stack dfs_state\<rbrakk> \<Longrightarrow>
     (DFS_skel_more_upd2 dfs_state, dfs_state) \<in> call_2_measure <*mlex*> r"
  by(auto elim!: invar_props_elims call_cond_elims
          simp add: DFS_skel_more_upd2_def call_2_measure_def
          intro!: mlex_less)

lemma wf_term_rel: "wf DFS_skel_more_term_rel'"
  by(auto simp: wf_mlex DFS_skel_more_term_rel'_def)

lemma in_DFS_skel_more_term_rel'[termination_intros]:
  "\<lbrakk>DFS_skel_more_call_1_conds dfs_state; invar_1 dfs_state; invar_seen_stack dfs_state\<rbrakk> \<Longrightarrow>
            (DFS_skel_more_upd1 dfs_state, dfs_state) \<in> DFS_skel_more_term_rel'"
  "\<lbrakk>DFS_skel_more_call_2_conds dfs_state; invar_1 dfs_state; invar_seen_stack dfs_state\<rbrakk> \<Longrightarrow>
            (DFS_skel_more_upd2 dfs_state, dfs_state) \<in> DFS_skel_more_term_rel'"
  by (simp_all add: DFS_skel_more_term_rel'_def termination_intros)

lemma DFS_skel_more_terminates[termination_intros]:
  assumes "invar_1 dfs_state" "invar_seen_stack dfs_state"
  shows "DFS_skel_more_dom dfs_state"
  using wf_term_rel assms
proof(induction rule: wf_induct_rule)
  case (less x)
  show ?case
    by (rule DFS_skel_more_domintros) (auto intro!: invar_holds_intros less in_DFS_skel_more_term_rel')
qed

end

text \<open>Spine agreement for an \<^emph>\<open>arbitrary\<close> spine-preserving \<open>on_push\<close>: provided \<open>found\<close> is
  spine-determined, the two runs take the same branches throughout, have the same domain, and
  agree on \<open>stack\<close>/\<open>seen\<close>. The hypothesis is genuinely needed --- \<open>found\<close> is a locale
  parameter and may read the \<open>'more\<close> slot, which only \<open>DFS_skel_more\<close> maintains, so without
  it the two runs can take different branches. It is taken per-theorem rather than as a
  locale axiom because instances such as the tracked cycle DFS satisfy it only along
  reachable states, via an invariant, not unconditionally.\<close>

lemma upd1_stack_spine:
  assumes "stack st1 = stack st2"
      and "seen st1 = seen st2"
  shows "stack (DFS_skel_more_upd1 st1) = stack (plain.DFS_skel_upd1 st2)"
  by (simp add: DFS_skel_more_upd1_def plain.DFS_skel_upd1_def Let_def assms)

lemma upd1_seen_spine:
  assumes "stack st1 = stack st2"
      and "seen st1 = seen st2"
  shows "seen (DFS_skel_more_upd1 st1) = seen (plain.DFS_skel_upd1 st2)"
  by (simp add: DFS_skel_more_upd1_def plain.DFS_skel_upd1_def Let_def assms)

lemma upd2_stack_spine:
  assumes "stack st1 = stack st2"
  shows "stack (DFS_skel_more_upd2 st1) = stack (plain.DFS_skel_upd2 st2)"
  by (simp add: DFS_skel_more_upd2_def plain.DFS_skel_upd2_def assms)

lemma upd2_seen_spine:
  assumes "seen st1 = seen st2"
  shows "seen (DFS_skel_more_upd2 st1) = seen (plain.DFS_skel_upd2 st2)"
  by (simp add: DFS_skel_more_upd2_def plain.DFS_skel_upd2_def assms)

lemma plain_dom_of_spine:
  assumes found_spine: "\<And>s1 s2. stack s1 = stack s2 \<Longrightarrow> seen s1 = seen s2 \<Longrightarrow> found s1 = found s2"
      and dom: "DFS_skel_more_dom st"
      and "stack st = stack st'"
      and "seen st = seen st'"
  shows "plain.DFS_skel_dom st'"
  using assms(3,4)
proof (induction arbitrary: st' rule: DFS_skel_more_induct[OF dom])
  case (1 dfs_state)
  have fnd: "found dfs_state = found st'"
    using found_spine[OF 1(4) 1(5)] .
  show ?case
  proof (rule plain.DFS_skel_domintros)
    show "plain.DFS_skel_dom (plain.DFS_skel_upd1 st')"
      if "plain.DFS_skel_call_1_conds st'"
      using 1(2)[OF _ upd1_stack_spine[OF 1(4) 1(5)] upd1_seen_spine[OF 1(4) 1(5)]] that
      by (simp add: plain_call_1_conds_spine[OF 1(4) 1(5) fnd])
    show "plain.DFS_skel_dom (plain.DFS_skel_upd2 st')"
      if "plain.DFS_skel_call_2_conds st'"
      using 1(3)[OF _ upd2_stack_spine[OF 1(4)] upd2_seen_spine[OF 1(5)]] that
      by (simp add: plain_call_2_conds_spine[OF 1(4) 1(5) fnd])
  qed
qed

lemma more_dom_of_spine:
  assumes found_spine: "\<And>s1 s2. stack s1 = stack s2 \<Longrightarrow> seen s1 = seen s2 \<Longrightarrow> found s1 = found s2"
      and dom: "plain.DFS_skel_dom st"
      and "stack st = stack st'"
      and "seen st = seen st'"
  shows "DFS_skel_more_dom st'"
  using assms(3,4)
proof (induction arbitrary: st' rule: plain.DFS_skel_induct[OF dom])
  case (1 dfs_state)
  have fnd: "found st' = found dfs_state"
    using found_spine[OF 1(4)[symmetric] 1(5)[symmetric]] .
  show ?case
  proof (rule DFS_skel_more_domintros)
    show "DFS_skel_more_dom (DFS_skel_more_upd1 st')"
      if "DFS_skel_more_call_1_conds st'"
      using 1(2)[OF _ upd1_stack_spine[OF 1(4)[symmetric] 1(5)[symmetric], symmetric]
                    upd1_seen_spine[OF 1(4)[symmetric] 1(5)[symmetric], symmetric]] that
      by (simp add: plain_call_1_conds_spine[OF 1(4)[symmetric] 1(5)[symmetric] fnd])
    show "DFS_skel_more_dom (DFS_skel_more_upd2 st')"
      if "DFS_skel_more_call_2_conds st'"
      using 1(3)[OF _ upd2_stack_spine[OF 1(4)[symmetric], symmetric]
                    upd2_seen_spine[OF 1(5)[symmetric], symmetric]] that
      by (simp add: plain_call_2_conds_spine[OF 1(4)[symmetric] 1(5)[symmetric] fnd])
  qed
qed

theorem DFS_skel_more_dom_iff:
  assumes found_spine: "\<And>s1 s2. stack s1 = stack s2 \<Longrightarrow> seen s1 = seen s2 \<Longrightarrow> found s1 = found s2"
  shows "DFS_skel_more_dom st \<longleftrightarrow> plain.DFS_skel_dom st"
  using plain_dom_of_spine[OF found_spine _ refl refl]
  using more_dom_of_spine[OF found_spine _ refl refl]
  by blast

lemma DFS_skel_more_truncate_eq:
  assumes found_spine: "\<And>s1 s2. stack s1 = stack s2 \<Longrightarrow> seen s1 = seen s2 \<Longrightarrow> found s1 = found s2"
      and dom: "DFS_skel_more_dom st"
      and "stack st = stack st'"
      and "seen st = seen st'"
  shows "DFS_skel_state.truncate (DFS_skel_more st) = DFS_skel_state.truncate (plain.DFS_skel st')"
  using assms(3,4)
proof (induction arbitrary: st' rule: DFS_skel_more_induct[OF dom])
  case (1 dfs_state)
  have fnd: "found dfs_state = found st'"
    using found_spine[OF 1(4) 1(5)] .
  have pdom: "plain.DFS_skel_dom st'"
    using plain_dom_of_spine[OF found_spine 1(1) 1(4) 1(5)] .
  show ?case
  proof (rule DFS_skel_more_cases[where dfs_state = dfs_state])
    show ?case if c: "DFS_skel_more_call_1_conds dfs_state"
    proof -
      have c': "plain.DFS_skel_call_1_conds st'"
        using c by (simp add: plain_call_1_conds_spine[OF 1(4) 1(5) fnd])
      have "DFS_skel_state.truncate (DFS_skel_more dfs_state)
              = DFS_skel_state.truncate (DFS_skel_more (DFS_skel_more_upd1 dfs_state))"
        by (simp add: DFS_skel_more_simps(1)[OF 1(1) c])
      also have "\<dots> = DFS_skel_state.truncate (plain.DFS_skel (plain.DFS_skel_upd1 st'))"
        using 1(2)[OF c upd1_stack_spine[OF 1(4) 1(5)] upd1_seen_spine[OF 1(4) 1(5)]] .
      also have "\<dots> = DFS_skel_state.truncate (plain.DFS_skel st')"
        by (simp add: plain.DFS_skel_simps(1)[OF pdom c'])
      finally show ?thesis .
    qed
    show ?case if c: "DFS_skel_more_call_2_conds dfs_state"
    proof -
      have c': "plain.DFS_skel_call_2_conds st'"
        using c by (simp add: plain_call_2_conds_spine[OF 1(4) 1(5) fnd])
      have "DFS_skel_state.truncate (DFS_skel_more dfs_state)
              = DFS_skel_state.truncate (DFS_skel_more (DFS_skel_more_upd2 dfs_state))"
        by (simp add: DFS_skel_more_simps(2)[OF 1(1) c])
      also have "\<dots> = DFS_skel_state.truncate (plain.DFS_skel (plain.DFS_skel_upd2 st'))"
        using 1(3)[OF c upd2_stack_spine[OF 1(4)] upd2_seen_spine[OF 1(5)]] .
      also have "\<dots> = DFS_skel_state.truncate (plain.DFS_skel st')"
        by (simp add: plain.DFS_skel_simps(2)[OF pdom c'])
      finally show ?thesis .
    qed
    show ?case if c: "DFS_skel_more_ret_1_conds dfs_state"
    proof -
      have c': "plain.DFS_skel_ret_1_conds st'"
        using c by (simp add: plain_ret_1_conds_spine[OF 1(4)])
      show ?thesis
        by (simp add: DFS_skel_more_simps(3)[OF 1(1) c] plain.DFS_skel_simps(3)[OF pdom c']
                      DFS_skel_more_ret1_def plain.DFS_skel_ret1_def
                      DFS_skel_state_truncate_eq_iff 1(4) 1(5))
    qed
    show ?case if c: "DFS_skel_more_ret_2_conds dfs_state"
    proof -
      have c': "plain.DFS_skel_ret_2_conds st'"
        using c by (simp add: plain_ret_2_conds_spine[OF 1(4) fnd])
      show ?thesis
        by (simp add: DFS_skel_more_simps(4)[OF 1(1) c] plain.DFS_skel_simps(4)[OF pdom c']
                      DFS_skel_more_ret2_def plain.DFS_skel_ret2_def
                      DFS_skel_state_truncate_eq_iff 1(4) 1(5))
    qed
  qed
qed

theorem DFS_skel_more_stack_eq:
  assumes found_spine: "\<And>s1 s2. stack s1 = stack s2 \<Longrightarrow> seen s1 = seen s2 \<Longrightarrow> found s1 = found s2"
      and dom: "DFS_skel_more_dom st"
  shows "stack (DFS_skel_more st) = stack (plain.DFS_skel st)"
  using DFS_skel_more_truncate_eq[OF found_spine dom refl refl]
  by (simp add: DFS_skel_state_truncate_eq_iff)

theorem DFS_skel_more_seen_eq:
  assumes found_spine: "\<And>s1 s2. stack s1 = stack s2 \<Longrightarrow> seen s1 = seen s2 \<Longrightarrow> found s1 = found s2"
      and dom: "DFS_skel_more_dom st"
  shows "seen (DFS_skel_more st) = seen (plain.DFS_skel st)"
  using DFS_skel_more_truncate_eq[OF found_spine dom refl refl]
  by (simp add: DFS_skel_state_truncate_eq_iff)

end
end
