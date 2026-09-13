theory DFS_Skeleton
  imports Directed_Set_Graphs.Pair_Graph_Specs Data_Structures.Set2_Addons
begin

text \<open>A generic DFS skeleton: the search spine (stack/seen) is fixed; per-algorithm semantics
are supplied as the callbacks found/on_found/on_empty/on_backtrack/on_push, which may only write
the extensible-record slot 'more.

\<open>on_push\<close> is applied to the freshly-pushed state in the descend step, i.e. after the
stack/seen update, so that an instance can maintain data that has to change when a vertex
\<^emph>\<open>enters\<close> the stack --- e.g. the set of gray (on-stack) vertices, which an instance
without the hook must rebuild as \<open>seen - finished\<close> by a set difference at every step. Like
the other callbacks it carries the spine-preservation contract of \<open>DFS_skeleton_thms\<close> below: it
must not disturb \<open>stack\<close>/\<open>seen\<close>. Instances that need no such data pass
\<open>on_push = (\<lambda>u st. st)\<close>.\<close>

record ('ver, 'vset) DFS_skeleton_state = stack:: "'ver list" seen:: "'vset"

named_theorems call_cond_elims
named_theorems call_cond_intros
named_theorems ret_holds_intros
named_theorems invar_props_intros
named_theorems invar_props_elims
named_theorems invar_holds_intros
named_theorems state_rel_intros
named_theorems state_rel_holds_intros

text \<open>The no-op push hook, for instances that maintain nothing on push. It is a constant rather
than \<open>\<lambda>u st. st\<close> so that the spine-preservation assumptions of
\<open>DFS_skeleton_thms\<close> do not instantiate to reflexive simplification rules.\<close>

definition no_push :: "'v \<Rightarrow> ('v,'vset,'more) DFS_skeleton_state_scheme
                              \<Rightarrow> ('v,'vset,'more) DFS_skeleton_state_scheme" where
  "no_push u st = st"

lemma no_push_simps[simp]:
  "stack (no_push u st) = stack st"
  "seen (no_push u st) = seen st"
  by (simp_all add: no_push_def)

locale DFS_skeleton =
  Graph: Pair_Graph_Specs where lookup = lookup +
 set_ops: Set2 vset_empty vset_delete _ t_set vset_inv insert
for lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option" +
fixes G::"'adjmap" and s::"'v"
  and found       :: "('v,'vset,'more) DFS_skeleton_state_scheme \<Rightarrow> bool"
  and on_found    :: "('v,'vset,'more) DFS_skeleton_state_scheme \<Rightarrow> ('v,'vset,'more) DFS_skeleton_state_scheme"
  and on_empty    :: "('v,'vset,'more) DFS_skeleton_state_scheme \<Rightarrow> ('v,'vset,'more) DFS_skeleton_state_scheme"
  and on_backtrack:: "'v \<Rightarrow> ('v,'vset,'more) DFS_skeleton_state_scheme \<Rightarrow> ('v,'vset,'more) DFS_skeleton_state_scheme"
  and on_push     :: "'v \<Rightarrow> ('v,'vset,'more) DFS_skeleton_state_scheme \<Rightarrow> ('v,'vset,'more) DFS_skeleton_state_scheme"
begin

abbreviation "neighbourhood' \<equiv> Graph.neighbourhood G"
notation "neighbourhood'" ("\<N>\<^sub>G _" 100)

function (domintros) DFS_skeleton::"('v,'vset,'more) DFS_skeleton_state_scheme \<Rightarrow> ('v,'vset,'more) DFS_skeleton_state_scheme" where
  "DFS_skeleton dfs_state =
     (case (stack dfs_state) of (v # stack_tl) \<Rightarrow>
       (if found dfs_state then on_found dfs_state
        else (if ((\<N>\<^sub>G v) -\<^sub>G (seen dfs_state)) \<noteq> \<emptyset>\<^sub>N then
                let u = (sel ((\<N>\<^sub>G v) -\<^sub>G (seen dfs_state)));
                    stack' = u # (stack dfs_state);
                    seen' = insert u (seen dfs_state)
                in DFS_skeleton (on_push u (dfs_state \<lparr>stack := stack', seen := seen'\<rparr>))
              else
                DFS_skeleton (on_backtrack v (dfs_state \<lparr>stack := stack_tl\<rparr>))))
     | _ \<Rightarrow> on_empty dfs_state)"
  by pat_completeness auto

partial_function (tailrec) DFS_skeleton_impl::"('v,'vset,'more) DFS_skeleton_state_scheme \<Rightarrow> ('v,'vset,'more) DFS_skeleton_state_scheme" where
  "DFS_skeleton_impl dfs_state =
     (case (stack dfs_state) of (v # stack_tl) \<Rightarrow>
       (if found dfs_state then on_found dfs_state
        else (if ((\<N>\<^sub>G v) -\<^sub>G (seen dfs_state)) \<noteq> \<emptyset>\<^sub>N then
                let u = (sel ((\<N>\<^sub>G v) -\<^sub>G (seen dfs_state)));
                    stack' = u # (stack dfs_state);
                    seen' = insert u (seen dfs_state)
                in DFS_skeleton_impl (on_push u (dfs_state \<lparr>stack := stack', seen := seen'\<rparr>))
              else
                DFS_skeleton_impl (on_backtrack v (dfs_state \<lparr>stack := stack_tl\<rparr>))))
     | _ \<Rightarrow> on_empty dfs_state)"

lemmas [code] = DFS_skeleton_impl.simps

lemma DFS_skeleton_impl_same:
  assumes "DFS_skeleton_dom state"
  shows   "DFS_skeleton_impl state = DFS_skeleton state"
  by(induction rule: DFS_skeleton.pinduct[OF assms])
    (subst DFS_skeleton.psimps, simp, subst DFS_skeleton_impl.simps,
     auto split: list.split if_split simp add: Let_def)

definition "DFS_skeleton_call_1_conds dfs_state =
    (case (stack dfs_state) of (v # stack_tl) \<Rightarrow>
       (if found dfs_state then False
        else (if ((\<N>\<^sub>G v) -\<^sub>G (seen dfs_state)) \<noteq> \<emptyset>\<^sub>N then True else False))
     | _ \<Rightarrow> False)"

lemma DFS_skeleton_call_1_conds[call_cond_elims]:
  "DFS_skeleton_call_1_conds dfs_state \<Longrightarrow>
   \<lbrakk>\<lbrakk>\<exists>v stack_tl. stack dfs_state = v # stack_tl;
    \<not> found dfs_state;
    (\<N>\<^sub>G (hd (stack dfs_state))) -\<^sub>G (seen dfs_state) \<noteq> \<emptyset>\<^sub>N\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto simp: DFS_skeleton_call_1_conds_def split: list.splits option.splits if_splits)

definition "DFS_skeleton_upd1 dfs_state = (
    let
      N = (\<N>\<^sub>G (hd (stack dfs_state)));
      u = (sel ((N -\<^sub>G (seen dfs_state))));
      stack' = u # (stack dfs_state);
      seen' = insert u (seen dfs_state)
    in
      on_push u (dfs_state \<lparr>stack := stack', seen := seen'\<rparr>))"

definition "DFS_skeleton_call_2_conds dfs_state =
    (case (stack dfs_state) of (v # stack_tl) \<Rightarrow>
       (if found dfs_state then False
        else (if ((\<N>\<^sub>G v) -\<^sub>G (seen dfs_state)) \<noteq> \<emptyset>\<^sub>N then False else True))
     | _ \<Rightarrow> False)"

lemma DFS_skeleton_call_2_conds[call_cond_elims]:
  "DFS_skeleton_call_2_conds dfs_state \<Longrightarrow>
   \<lbrakk>\<lbrakk>\<exists>v stack_tl. stack dfs_state = v # stack_tl;
    \<not> found dfs_state;
    (\<N>\<^sub>G (hd (stack dfs_state))) -\<^sub>G (seen dfs_state) = \<emptyset>\<^sub>N\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto simp: DFS_skeleton_call_2_conds_def split: list.splits option.splits if_splits)

definition "DFS_skeleton_upd2 dfs_state =
  on_backtrack (hd (stack dfs_state)) (dfs_state \<lparr>stack := tl (stack dfs_state)\<rparr>)"

definition "DFS_skeleton_ret_1_conds dfs_state =
    (case (stack dfs_state) of (v # stack_tl) \<Rightarrow> False | _ \<Rightarrow> True)"

lemma DFS_skeleton_ret_1_conds[call_cond_elims]:
  "DFS_skeleton_ret_1_conds dfs_state \<Longrightarrow> \<lbrakk>\<lbrakk>stack dfs_state = []\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto simp: DFS_skeleton_ret_1_conds_def split: list.splits if_splits)

lemma DFS_skeleton_ret_1_condsI[call_cond_intros]:
  "\<lbrakk>stack dfs_state = []\<rbrakk> \<Longrightarrow> DFS_skeleton_ret_1_conds dfs_state"
  by(auto simp: DFS_skeleton_ret_1_conds_def split: list.splits if_splits)

definition "DFS_skeleton_ret1 dfs_state = on_empty dfs_state"

definition "DFS_skeleton_ret_2_conds dfs_state =
    (case (stack dfs_state) of (v # stack_tl) \<Rightarrow> (if found dfs_state then True else False) | _ \<Rightarrow> False)"

lemma DFS_skeleton_ret_2_conds[call_cond_elims]:
  "DFS_skeleton_ret_2_conds dfs_state \<Longrightarrow>
   \<lbrakk>\<lbrakk>\<exists>v stack_tl. stack dfs_state = v # stack_tl; found dfs_state\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto simp: DFS_skeleton_ret_2_conds_def split: list.splits if_splits)

lemma DFS_skeleton_ret_2_condsI[call_cond_intros]:
  "\<lbrakk>\<exists>v stack_tl. stack dfs_state = v # stack_tl; found dfs_state\<rbrakk> \<Longrightarrow> DFS_skeleton_ret_2_conds dfs_state"
  by(auto simp: DFS_skeleton_ret_2_conds_def split: list.splits if_splits)

definition "DFS_skeleton_ret2 dfs_state = on_found dfs_state"

lemma DFS_skeleton_cases:
  assumes "DFS_skeleton_call_1_conds dfs_state \<Longrightarrow> P"
      "DFS_skeleton_call_2_conds dfs_state \<Longrightarrow> P"
      "DFS_skeleton_ret_1_conds dfs_state \<Longrightarrow> P"
      "DFS_skeleton_ret_2_conds dfs_state \<Longrightarrow> P"
  shows "P"
proof-
  have "DFS_skeleton_call_1_conds dfs_state \<or> DFS_skeleton_call_2_conds dfs_state \<or>
        DFS_skeleton_ret_1_conds dfs_state \<or> DFS_skeleton_ret_2_conds dfs_state"
    by (auto simp add: DFS_skeleton_call_1_conds_def DFS_skeleton_call_2_conds_def
                        DFS_skeleton_ret_1_conds_def DFS_skeleton_ret_2_conds_def
           split: list.split_asm option.split_asm if_splits)
  then show ?thesis
    using assms by auto
qed

lemma DFS_skeleton_simps:
  assumes "DFS_skeleton_dom dfs_state"
  shows "DFS_skeleton_call_1_conds dfs_state \<Longrightarrow> DFS_skeleton dfs_state = DFS_skeleton (DFS_skeleton_upd1 dfs_state)"
      "DFS_skeleton_call_2_conds dfs_state \<Longrightarrow> DFS_skeleton dfs_state = DFS_skeleton (DFS_skeleton_upd2 dfs_state)"
      "DFS_skeleton_ret_1_conds dfs_state \<Longrightarrow> DFS_skeleton dfs_state = DFS_skeleton_ret1 dfs_state"
      "DFS_skeleton_ret_2_conds dfs_state \<Longrightarrow> DFS_skeleton dfs_state = DFS_skeleton_ret2 dfs_state"
  by (auto simp add: DFS_skeleton.psimps[OF assms] Let_def
                       DFS_skeleton_call_1_conds_def DFS_skeleton_upd1_def DFS_skeleton_call_2_conds_def DFS_skeleton_upd2_def
                       DFS_skeleton_ret_1_conds_def DFS_skeleton_ret1_def
                       DFS_skeleton_ret_2_conds_def DFS_skeleton_ret2_def
            split: list.splits option.splits if_splits)

lemma DFS_skeleton_induct:
  assumes "DFS_skeleton_dom dfs_state"
  assumes "\<And>dfs_state. \<lbrakk>DFS_skeleton_dom dfs_state;
                        DFS_skeleton_call_1_conds dfs_state \<Longrightarrow> P (DFS_skeleton_upd1 dfs_state);
                        DFS_skeleton_call_2_conds dfs_state \<Longrightarrow> P (DFS_skeleton_upd2 dfs_state)\<rbrakk> \<Longrightarrow> P dfs_state"
  shows "P dfs_state"
  apply(rule DFS_skeleton.pinduct[OF assms(1)])
  apply(rule assms(2)[simplified DFS_skeleton_call_1_conds_def DFS_skeleton_upd1_def DFS_skeleton_call_2_conds_def DFS_skeleton_upd2_def])
  by (auto simp: Let_def split: list.splits option.splits if_splits)

lemma DFS_skeleton_domintros:
  assumes "DFS_skeleton_call_1_conds dfs_state \<Longrightarrow> DFS_skeleton_dom (DFS_skeleton_upd1 dfs_state)"
  assumes "DFS_skeleton_call_2_conds dfs_state \<Longrightarrow> DFS_skeleton_dom (DFS_skeleton_upd2 dfs_state)"
  shows "DFS_skeleton_dom dfs_state"
proof(rule DFS_skeleton.domintros, goal_cases)
  case (1 x21 x22)
  then show ?case
    using assms(1)[simplified DFS_skeleton_call_1_conds_def DFS_skeleton_upd1_def]
    by (force simp: Let_def split: list.splits option.splits if_splits)
next
  case (2 x21 x22)
  then show ?case
    using assms(2)[simplified DFS_skeleton_call_2_conds_def DFS_skeleton_upd2_def]
    by (force simp: Let_def split: list.splits option.splits if_splits)
qed

definition "DFS_skeleton_axioms = (Graph.graph_inv G \<and> Graph.finite_graph G \<and> Graph.finite_vsets G)"

definition "invar_1 dfs_state = vset_inv (seen dfs_state)"

definition "invar_seen_stack dfs_state \<longleftrightarrow>
    distinct (stack dfs_state)
    \<and> set (stack dfs_state) \<subseteq> t_set (seen dfs_state)
    \<and> t_set (seen dfs_state) \<subseteq> dVs (Graph.digraph_abs G)"

definition "call_1_measure dfs_state = card (dVs (Graph.digraph_abs G) - t_set (seen dfs_state))"

definition "call_2_measure dfs_state = card (set (stack dfs_state))"

definition "DFS_skeleton_term_rel' = (call_1_measure) <*mlex*> (call_2_measure) <*mlex*> {}"

end

text \<open>The reasoning layer: the callbacks --- \<open>on_push\<close> included --- must not disturb the
search spine (stack/seen), and the graph is well-formed. Under these the structural invariants
and termination hold generically.\<close>

locale DFS_skeleton_thms = DFS_skeleton +
  assumes DFS_skeleton_axioms: DFS_skeleton_axioms
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
  using DFS_skeleton_axioms
  by (auto simp: DFS_skeleton_axioms_def)

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
  "\<lbrakk>DFS_skeleton_call_1_conds dfs_state; invar_1 dfs_state\<rbrakk> \<Longrightarrow> invar_1 (DFS_skeleton_upd1 dfs_state)"
  by (auto simp: Let_def DFS_skeleton_upd1_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_1_holds_2[invar_holds_intros]:
  "\<lbrakk>DFS_skeleton_call_2_conds dfs_state; invar_1 dfs_state\<rbrakk> \<Longrightarrow> invar_1 (DFS_skeleton_upd2 dfs_state)"
  by (auto simp: DFS_skeleton_upd2_def elim!: invar_props_elims intro: invar_props_intros)

lemma invar_1_holds_4[invar_holds_intros]:
  "\<lbrakk>DFS_skeleton_ret_1_conds dfs_state; invar_1 dfs_state\<rbrakk> \<Longrightarrow> invar_1 (DFS_skeleton_ret1 dfs_state)"
  by (auto elim!: invar_props_elims intro: invar_props_intros simp: DFS_skeleton_ret1_def)

lemma invar_1_holds_5[invar_holds_intros]:
  "\<lbrakk>DFS_skeleton_ret_2_conds dfs_state; invar_1 dfs_state\<rbrakk> \<Longrightarrow> invar_1 (DFS_skeleton_ret2 dfs_state)"
  by (auto elim!: invar_props_elims intro: invar_props_intros simp: DFS_skeleton_ret2_def)

lemma invar_1_holds[invar_holds_intros]:
   assumes "DFS_skeleton_dom dfs_state" "invar_1 dfs_state"
   shows "invar_1 (DFS_skeleton dfs_state)"
  using assms(2)
proof(induction rule: DFS_skeleton_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule DFS_skeleton_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-4) invar_holds_intros simp: DFS_skeleton_simps[OF IH(1)])
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
  "\<lbrakk>DFS_skeleton_call_1_conds dfs_state; invar_1 dfs_state; invar_seen_stack dfs_state\<rbrakk> \<Longrightarrow>
     invar_seen_stack (DFS_skeleton_upd1 dfs_state)"
  by (force simp: Let_def DFS_skeleton_upd1_def elim!: call_cond_elims
            elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_seen_stack_holds_2[invar_holds_intros]:
  "\<lbrakk>DFS_skeleton_call_2_conds dfs_state; invar_1 dfs_state; invar_seen_stack dfs_state\<rbrakk> \<Longrightarrow>
     invar_seen_stack (DFS_skeleton_upd2 dfs_state)"
  by (auto elim!: call_cond_elims simp: DFS_skeleton_upd2_def
           elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_seen_stack_holds_4[invar_holds_intros]:
   "\<lbrakk>DFS_skeleton_ret_1_conds dfs_state; invar_seen_stack dfs_state\<rbrakk> \<Longrightarrow>
       invar_seen_stack (DFS_skeleton_ret1 dfs_state)"
  by (auto elim!: invar_props_elims intro!: invar_props_intros simp: DFS_skeleton_ret1_def)

lemma invar_seen_stack_holds_5[invar_holds_intros]:
   "\<lbrakk>DFS_skeleton_ret_2_conds dfs_state; invar_seen_stack dfs_state\<rbrakk> \<Longrightarrow>
       invar_seen_stack (DFS_skeleton_ret2 dfs_state)"
  by (auto elim!: invar_props_elims intro!: invar_props_intros simp: DFS_skeleton_ret2_def)

lemma invar_seen_stack_holds[invar_holds_intros]:
   assumes "DFS_skeleton_dom dfs_state" "invar_1 dfs_state" "invar_seen_stack dfs_state"
   shows "invar_seen_stack (DFS_skeleton dfs_state)"
   using assms(2-)
proof(induction rule: DFS_skeleton_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule DFS_skeleton_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-5) invar_holds_intros simp: DFS_skeleton_simps[OF IH(1)])
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
  "\<lbrakk>DFS_skeleton_call_1_conds dfs_state; invar_1 dfs_state; invar_seen_stack dfs_state\<rbrakk> \<Longrightarrow>
     (DFS_skeleton_upd1 dfs_state, dfs_state) \<in> call_1_measure <*mlex*> r"
  by(fastforce elim!: invar_props_elims call_cond_elims
          simp add: DFS_skeleton_upd1_def call_1_measure_def Let_def
          intro!: mlex_less psubset_card_mono
          dest!: Graph.vset.choose')

lemma call_2_measure_nonsym[simp]: "(call_2_measure dfs_state, call_2_measure dfs_state) \<notin> less_rel"
  by (auto simp: less_rel_def)

lemma call_2_measure_1[termination_intros]:
  "\<lbrakk>DFS_skeleton_call_2_conds dfs_state; invar_1 dfs_state\<rbrakk> \<Longrightarrow>
    call_1_measure dfs_state = call_1_measure (DFS_skeleton_upd2 dfs_state)"
  by(auto simp add: DFS_skeleton_upd2_def call_1_measure_def Let_def)

lemma call_2_terminates[termination_intros]:
  "\<lbrakk>DFS_skeleton_call_2_conds dfs_state; invar_1 dfs_state; invar_seen_stack dfs_state\<rbrakk> \<Longrightarrow>
     (DFS_skeleton_upd2 dfs_state, dfs_state) \<in> call_2_measure <*mlex*> r"
  by(auto elim!: invar_props_elims call_cond_elims
          simp add: DFS_skeleton_upd2_def call_2_measure_def
          intro!: mlex_less)

lemma wf_term_rel: "wf DFS_skeleton_term_rel'"
  by(auto simp: wf_mlex DFS_skeleton_term_rel'_def)

lemma in_DFS_skeleton_term_rel'[termination_intros]:
  "\<lbrakk>DFS_skeleton_call_1_conds dfs_state; invar_1 dfs_state; invar_seen_stack dfs_state\<rbrakk> \<Longrightarrow>
            (DFS_skeleton_upd1 dfs_state, dfs_state) \<in> DFS_skeleton_term_rel'"
  "\<lbrakk>DFS_skeleton_call_2_conds dfs_state; invar_1 dfs_state; invar_seen_stack dfs_state\<rbrakk> \<Longrightarrow>
            (DFS_skeleton_upd2 dfs_state, dfs_state) \<in> DFS_skeleton_term_rel'"
  by (simp_all add: DFS_skeleton_term_rel'_def termination_intros)

lemma DFS_skeleton_terminates[termination_intros]:
  assumes "invar_1 dfs_state" "invar_seen_stack dfs_state"
  shows "DFS_skeleton_dom dfs_state"
  using wf_term_rel assms
proof(induction rule: wf_induct_rule)
  case (less x)
  show ?case
    by (rule DFS_skeleton_domintros) (auto intro!: invar_holds_intros less in_DFS_skeleton_term_rel')
qed

end

end
end
