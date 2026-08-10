theory DFS_DirCycle_Linear_Tracked_Aux
  imports DFS_Skel_More Directed_Set_Graphs.Component_Defs
begin


text \<open>The pre-seeded directed-cycle DFS of \<open>DFS_DirCycle_Linear_Aux\<close>,
  rebuilt on \<^locale>\<open>DFS_skel_more\<close> so that the gray (on-stack) set and the complement of the
  finished region are carried \<^emph>\<open>explicitly\<close> and maintained \<^emph>\<open>incrementally\<close>:

  \<^item> The library's \<open>DFS_dircycle\<close> tests for a back edge with
    \<open>(\<N>\<^sub>G v) \<inter>\<^sub>G (seen - finished)\<close>, rebuilding the gray set by an \<open>O(V)\<close> set difference at
    \<^emph>\<open>every\<close> skeleton step, which makes the DFS \<open>O(V \<cdot> (V + E))\<close>. Here \<open>cyc_found\<close> tests
    \<open>(\<N>\<^sub>G v) \<inter>\<^sub>G gray\<close>, where \<open>gray\<close> is grown at \<open>on_push\<close> (the hook the duplicated skeleton
    exists for) and shrunk at backtrack. The invariant \<open>invar_gray_stack\<close> --- \<open>t_set gray = set stack\<close>
    --- together with \<open>invar_ssf\<close>'s \<open>finished = seen - stack\<close> shows the two tests agree
    (\<open>cyc_found_agrees\<close>), so the library's soundness/completeness arguments carry over with the
    back-edge witness read off \<open>gray\<close> directly.
  \<^item> An \<open>unfinished\<close> set is maintained alongside (shrunk at backtrack), so the outer
    whole-graph sweep can pick its next root by \<open>sel unfinished\<close> instead of computing
    \<open>V -\<^sub>G finished\<close> --- another per-iteration \<open>O(V)\<close> difference gone. Its invariant
    \<open>invar_fin_unfin\<close> keeps it the \<^emph>\<open>exact complement\<close> of \<open>finished\<close> in the vertex set: the
    caller hands in \<open>uf\<close> as the complement of the seed \<open>f\<close>, and each backtrack moves one
    vertex from \<open>unfinished\<close> to \<open>finished\<close>.

  As in the \<open>_Linear_Aux\<close> variant, the run starts pre-seeded with an already-finished region
  \<open>f\<close>: both \<open>seen\<close> and \<open>finished\<close> start at \<open>f\<close>, and the caller warrants that \<open>f\<close> is
  successor-closed and acyclic. The exports at the end are the aux's seven --- what one run must
  hand the outer loop --- plus the two for \<open>unfinished\<close>.\<close>

record ('ver, 'vset) DFS_dircycle_tracked_state = "('ver, 'vset) DFS_skel_state" +
  finished   :: "'vset"
  gray       :: "'vset"
  unfinished :: "'vset"
  cycle      :: bool

locale DFS_dircycle_tracked =
  Graph: Pair_Graph_Specs where lookup = lookup +
 set_ops: Set2 vset_empty vset_delete _ t_set vset_inv insert
for lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option" +
fixes G::"'adjmap" and s::"'v" and f::"'vset" and uf::"'vset"
begin

abbreviation "neighbourhood' \<equiv> Graph.neighbourhood G"
notation "neighbourhood'" ("\<N>\<^sub>G _" 100)

text \<open>The point of the exercise: the back-edge test reads the incrementally maintained gray set,
  no set difference.\<close>
definition "cyc_found (dfs_state::('v,'vset) DFS_dircycle_tracked_state) =
   (case stack dfs_state of [] \<Rightarrow> False
    | (v # stack_tl) \<Rightarrow> (((\<N>\<^sub>G v) \<inter>\<^sub>G (gray dfs_state)) \<noteq> \<emptyset>\<^sub>N))"

definition "cyc_on_found (dfs_state::('v,'vset) DFS_dircycle_tracked_state) = (dfs_state \<lparr>cycle := True\<rparr>)"

definition "cyc_on_empty (dfs_state::('v,'vset) DFS_dircycle_tracked_state) = dfs_state"

definition "cyc_on_push u (dfs_state::('v,'vset) DFS_dircycle_tracked_state) =
  (dfs_state \<lparr>gray := insert u (gray dfs_state)\<rparr>)"

definition "cyc_on_backtrack v (dfs_state::('v,'vset) DFS_dircycle_tracked_state) =
  (dfs_state \<lparr>finished := insert v (finished dfs_state),
              gray := vset_delete v (gray dfs_state),
              unfinished := vset_delete v (unfinished dfs_state)\<rparr>)"

text \<open>The root \<open>s\<close> is pushed by the initial state rather than by \<open>on_push\<close>, so \<open>gray\<close> must
  already account for it: \<open>gray\<close> starts at \<open>{s}\<close>. The \<open>unfinished\<close> set starts at the caller's
  \<open>uf\<close> unchanged: since \<open>s \<notin> t_set f\<close> and \<open>t_set uf \<union> t_set f\<close> covers the vertex set, \<open>s\<close>
  \<^emph>\<open>is\<close> in the initial \<open>unfinished\<close>, and it leaves it only when it is backtracked --- a vertex
  moves from \<open>unfinished\<close> to \<open>finished\<close> on being finished, never merely on entering the
  search.\<close>
definition "dircycle_tracked_initial_state =
  \<lparr>stack = [s], seen = insert s f, finished = f, gray = insert s \<emptyset>\<^sub>N,
   unfinished = uf, cycle = False\<rparr>"

text \<open>The library's graph/root conditions, the \<open>_Linear_Aux\<close> seed contract on \<open>f\<close> (the root is
  fresh; \<open>f\<close> is a well-formed vset inside the vertex set, successor-closed, and acyclic when
  restricted to), and the contract on the caller's unfinished set \<open>uf\<close>: a well-formed vset that
  is \<^emph>\<open>exactly\<close> the complement of \<open>f\<close> in the vertex set. The run maintains that partition
  between \<open>unfinished\<close> and \<open>finished\<close> (see \<open>invar_fin_unfin\<close>); the outer loop consumes it to
  pick fresh roots without ever computing a set difference.\<close>
definition "DFS_dircycle_tracked_axioms =
  (Graph.graph_inv G \<and> Graph.finite_graph G \<and> Graph.finite_vsets G
  \<and> s \<in> dVs (Graph.digraph_abs G)
  \<and> s \<notin> t_set f
  \<and> vset_inv f
  \<and> t_set f \<subseteq> dVs (Graph.digraph_abs G)
  \<and> (\<forall>u w. u \<in> t_set f \<longrightarrow> (u, w) \<in> Graph.digraph_abs G \<longrightarrow> w \<in> t_set f)
  \<and> (\<nexists>c. Awalk_Defs.cycle (Graph.digraph_abs G \<downharpoonright> t_set f) c)
  \<and> vset_inv uf
  \<and> t_set uf \<union> t_set f = dVs (Graph.digraph_abs G)
  \<and> t_set uf \<inter> t_set f = {})"

sublocale dc: DFS_skel_more
  where lookup = lookup and G = G and s = s
    and found = cyc_found and on_found = cyc_on_found
    and on_empty = cyc_on_empty and on_backtrack = cyc_on_backtrack
    and on_push = cyc_on_push
  by unfold_locales

abbreviation "find_dircycle_tracked \<equiv> dc.DFS_skel_more_impl"

end

locale DFS_dircycle_tracked_thms = DFS_dircycle_tracked +
  assumes dircycle_tracked_axioms: DFS_dircycle_tracked_axioms
begin

lemma spine_preservation:
  "stack (cyc_on_found st) = stack st" "seen (cyc_on_found st) = seen st"
  "stack (cyc_on_empty st) = stack st" "seen (cyc_on_empty st) = seen st"
  "stack (cyc_on_backtrack v st) = stack st" "seen (cyc_on_backtrack v st) = seen st"
  "stack (cyc_on_push u st) = stack st" "seen (cyc_on_push u st) = seen st"
  by (auto simp: cyc_on_found_def cyc_on_empty_def cyc_on_backtrack_def cyc_on_push_def)

sublocale dc: DFS_skel_more_thms
  where lookup = lookup and G = G and s = s
    and found = cyc_found and on_found = cyc_on_found
    and on_empty = cyc_on_empty and on_backtrack = cyc_on_backtrack
    and on_push = cyc_on_push
  using dircycle_tracked_axioms
  by (unfold_locales)
     (auto simp: dc.DFS_skel_more_axioms_def DFS_dircycle_tracked_axioms_def
                 cyc_on_found_def cyc_on_empty_def cyc_on_backtrack_def cyc_on_push_def)

definition "invar_2 dfs_state = Vwalk.vwalk (Graph.digraph_abs G) (rev (stack dfs_state))"

definition "invar_ssf dfs_state \<longleftrightarrow>
    distinct (stack dfs_state)
    \<and> set (stack dfs_state) \<subseteq> t_set (seen dfs_state)
    \<and> t_set (finished dfs_state) \<subseteq> t_set (seen dfs_state)
    \<and> t_set (finished dfs_state) = t_set (seen dfs_state) - set (stack dfs_state)
    \<and> t_set (seen dfs_state) \<subseteq> dVs (Graph.digraph_abs G)"

definition "invar_fin dfs_state = vset_inv (finished dfs_state)"

text \<open>The gray set \<^emph>\<open>is\<close> the stack: this is what lets \<open>cyc_found\<close> stand in for the library's
  \<open>seen - finished\<close> test.\<close>
definition "invar_gray dfs_state \<longleftrightarrow>
    vset_inv (gray dfs_state)"

definition "invar_gray_stack dfs_state \<longleftrightarrow>
  t_set (gray dfs_state) = set (stack dfs_state)"

definition "invar_unfin dfs_state \<longleftrightarrow>
    vset_inv (unfinished dfs_state)"

definition "invar_fin_unfin dfs_state \<equiv>
 t_set (unfinished dfs_state) \<union> (t_set (finished dfs_state)) = dVs (Graph.digraph_abs G)
\<and> t_set (unfinished dfs_state) \<inter> (t_set (finished dfs_state)) = {}"

definition "invar_seed dfs_state \<longleftrightarrow>
    Set.insert s (t_set f) \<subseteq> t_set (seen dfs_state)
  \<and> t_set f \<subseteq> t_set (finished dfs_state)"

definition "invar_cycle_true dfs_state =
    (cycle dfs_state \<longrightarrow> (\<exists>c. Awalk_Defs.cycle (Graph.digraph_abs G) c))"

definition "invar_finished_closed dfs_state =
  (\<forall>u w. u \<in> t_set (finished dfs_state) \<longrightarrow> (u, w) \<in> Graph.digraph_abs G \<longrightarrow> w \<in> t_set (finished dfs_state))"

definition "invar_cycle_false dfs_state =
  (\<not> cycle dfs_state \<longrightarrow> (\<nexists>c. Awalk_Defs.cycle (Graph.digraph_abs G \<downharpoonright> t_set (finished dfs_state)) c))"

context
includes set_ops.automation2 and Graph.adjmap.automation and Graph.vset.set.automation
begin

subsection \<open>The invariants hold at the seeded initial state\<close>

lemma initial_invars[simp,intro]:
  "dc.invar_1 dircycle_tracked_initial_state"
  "dc.invar_seen_stack dircycle_tracked_initial_state"
  using dircycle_tracked_axioms
  by (auto simp: dc.invar_1_def dc.invar_seen_stack_def dircycle_tracked_initial_state_def
                 DFS_dircycle_tracked_axioms_def)

lemma dircycle_tracked_initial_dom: "dc.DFS_skel_more_dom dircycle_tracked_initial_state"
  by (intro dc.DFS_skel_more_terminates initial_invars)

lemma initial_struct[simp,intro]:
  "invar_2 dircycle_tracked_initial_state"
  "invar_ssf dircycle_tracked_initial_state"
  using dircycle_tracked_axioms
  by (auto simp: invar_2_def invar_ssf_def dircycle_tracked_initial_state_def
                 DFS_dircycle_tracked_axioms_def)

lemma initial_fin[simp,intro]: "invar_fin dircycle_tracked_initial_state"
  using dircycle_tracked_axioms[unfolded DFS_dircycle_tracked_axioms_def]
  by (simp add: invar_fin_def dircycle_tracked_initial_state_def)

lemma initial_gray[simp,intro]: "invar_gray dircycle_tracked_initial_state"
  by (auto simp: invar_gray_def dircycle_tracked_initial_state_def)

lemma initial_gray_stack[simp,intro]: "invar_gray_stack dircycle_tracked_initial_state"
  by (auto simp: invar_gray_stack_def dircycle_tracked_initial_state_def)

lemma initial_unfin[simp,intro]: "invar_unfin dircycle_tracked_initial_state"
  using dircycle_tracked_axioms[unfolded DFS_dircycle_tracked_axioms_def]
  by (auto simp: invar_unfin_def dircycle_tracked_initial_state_def)

lemma initial_fin_unfin[simp,intro]: "invar_fin_unfin dircycle_tracked_initial_state"
  using dircycle_tracked_axioms[unfolded DFS_dircycle_tracked_axioms_def]
  by (auto simp: invar_fin_unfin_def dircycle_tracked_initial_state_def)

lemma initial_seed[simp,intro]: "invar_seed dircycle_tracked_initial_state"
  using dircycle_tracked_axioms
  by (auto simp: invar_seed_def dircycle_tracked_initial_state_def
                 DFS_dircycle_tracked_axioms_def)

lemma initial_fc[simp,intro]:
  "invar_finished_closed dircycle_tracked_initial_state"
  "invar_cycle_false dircycle_tracked_initial_state"
  using dircycle_tracked_axioms[unfolded DFS_dircycle_tracked_axioms_def]
  by (auto simp: invar_finished_closed_def invar_cycle_false_def
                 dircycle_tracked_initial_state_def)

subsection \<open>The step functions, explicitly\<close>

lemma upd1_unfold:
  "stack (dc.DFS_skel_more_upd1 st) = sel ((\<N>\<^sub>G (hd (stack st))) -\<^sub>G seen st) # stack st"
  "seen (dc.DFS_skel_more_upd1 st) = insert (sel ((\<N>\<^sub>G (hd (stack st))) -\<^sub>G seen st)) (seen st)"
  "finished (dc.DFS_skel_more_upd1 st) = finished st"
  "gray (dc.DFS_skel_more_upd1 st) = insert (sel ((\<N>\<^sub>G (hd (stack st))) -\<^sub>G seen st)) (gray st)"
  "unfinished (dc.DFS_skel_more_upd1 st) = unfinished st"
  "cycle (dc.DFS_skel_more_upd1 st) = cycle st"
  by (auto simp: dc.DFS_skel_more_upd1_def cyc_on_push_def Let_def)

lemma upd2_unfold:
  "stack (dc.DFS_skel_more_upd2 st) = tl (stack st)"
  "seen (dc.DFS_skel_more_upd2 st) = seen st"
  "finished (dc.DFS_skel_more_upd2 st) = insert (hd (stack st)) (finished st)"
  "gray (dc.DFS_skel_more_upd2 st) = vset_delete (hd (stack st)) (gray st)"
  "unfinished (dc.DFS_skel_more_upd2 st) = vset_delete (hd (stack st)) (unfinished st)"
  "cycle (dc.DFS_skel_more_upd2 st) = cycle st"
  by (auto simp: dc.DFS_skel_more_upd2_def cyc_on_backtrack_def)

subsection \<open>Structural invariants\<close>

lemma invar_fin_props[invar_props_elims]:
  "invar_fin dfs_state \<Longrightarrow> (vset_inv (finished dfs_state) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_fin_def)

lemma invar_fin_intro[invar_props_intros]:
  "vset_inv (finished dfs_state) \<Longrightarrow> invar_fin dfs_state"
  by (auto simp: invar_fin_def)

lemma invar_fin_holds_upd1[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skel_more_call_1_conds dfs_state; invar_fin dfs_state\<rbrakk> \<Longrightarrow> invar_fin (dc.DFS_skel_more_upd1 dfs_state)"
  by (auto simp: upd1_unfold elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_fin_holds_upd2[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skel_more_call_2_conds dfs_state; invar_fin dfs_state\<rbrakk> \<Longrightarrow> invar_fin (dc.DFS_skel_more_upd2 dfs_state)"
  by (auto simp: upd2_unfold elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_fin_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skel_more_ret_1_conds dfs_state; invar_fin dfs_state\<rbrakk> \<Longrightarrow> invar_fin (dc.DFS_skel_more_ret1 dfs_state)"
  by (auto simp: dc.DFS_skel_more_ret1_def cyc_on_empty_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_fin_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skel_more_ret_2_conds dfs_state; invar_fin dfs_state\<rbrakk> \<Longrightarrow> invar_fin (dc.DFS_skel_more_ret2 dfs_state)"
  by (auto simp: dc.DFS_skel_more_ret2_def cyc_on_found_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_fin_holds[invar_holds_intros]:
  assumes "dc.DFS_skel_more_dom dfs_state" "invar_fin dfs_state"
  shows "invar_fin (dc.DFS_skel_more dfs_state)"
  using assms(2-)
proof(induction rule: dc.DFS_skel_more_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule dc.DFS_skel_more_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-) invar_holds_intros simp: dc.DFS_skel_more_simps[OF IH(1)])
qed

lemma invar_2_props[invar_props_elims]:
  "invar_2 dfs_state \<Longrightarrow> (Vwalk.vwalk (Graph.digraph_abs G) (rev (stack dfs_state)) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_2_def)

lemma invar_2_intro[invar_props_intros]:
  "Vwalk.vwalk (Graph.digraph_abs G) (rev (stack dfs_state)) \<Longrightarrow> invar_2 dfs_state"
  by (auto simp: invar_2_def)

lemma invar_2_holds_upd1[invar_holds_intros]:
  assumes "dc.DFS_skel_more_call_1_conds dfs_state" "dc.invar_1 dfs_state" "invar_2 dfs_state"
  shows "invar_2 (dc.DFS_skel_more_upd1 dfs_state)"
  using assms dc.graph_inv
  by (force simp: upd1_unfold elim!: call_cond_elims
            elim!: invar_props_elims intro!: Vwalk.vwalk_append2 invar_props_intros)

lemma invar_2_holds_upd2[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skel_more_call_2_conds dfs_state; invar_2 dfs_state\<rbrakk> \<Longrightarrow> invar_2 (dc.DFS_skel_more_upd2 dfs_state)"
  by (auto simp: upd2_unfold dest!: append_vwalk_pref elim!: invar_props_elims
           intro!: invar_props_intros elim: call_cond_elims)

lemma invar_2_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skel_more_ret_1_conds dfs_state; invar_2 dfs_state\<rbrakk> \<Longrightarrow> invar_2 (dc.DFS_skel_more_ret1 dfs_state)"
  by (auto simp: dc.DFS_skel_more_ret1_def cyc_on_empty_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_2_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skel_more_ret_2_conds dfs_state; invar_2 dfs_state\<rbrakk> \<Longrightarrow> invar_2 (dc.DFS_skel_more_ret2 dfs_state)"
  by (auto simp: dc.DFS_skel_more_ret2_def cyc_on_found_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_2_holds[invar_holds_intros]:
  assumes "dc.DFS_skel_more_dom dfs_state" "dc.invar_1 dfs_state" "invar_2 dfs_state"
  shows "invar_2 (dc.DFS_skel_more dfs_state)"
  using assms(2-)
proof(induction rule: dc.DFS_skel_more_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule dc.DFS_skel_more_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-) invar_holds_intros simp: dc.DFS_skel_more_simps[OF IH(1)])
qed

lemma invar_ssf_props[invar_props_elims]:
  "invar_ssf dfs_state \<Longrightarrow>
     (\<lbrakk>distinct (stack dfs_state); set (stack dfs_state) \<subseteq> t_set (seen dfs_state);
       t_set (finished dfs_state) \<subseteq> t_set (seen dfs_state);
       t_set (finished dfs_state) = t_set (seen dfs_state) - set (stack dfs_state);
       t_set (seen dfs_state) \<subseteq> dVs (Graph.digraph_abs G)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_ssf_def)

lemma invar_ssf_intro[invar_props_intros]:
  "\<lbrakk>distinct (stack dfs_state); set (stack dfs_state) \<subseteq> t_set (seen dfs_state);
    t_set (finished dfs_state) \<subseteq> t_set (seen dfs_state);
    t_set (finished dfs_state) = t_set (seen dfs_state) - set (stack dfs_state);
    t_set (seen dfs_state) \<subseteq> dVs (Graph.digraph_abs G)\<rbrakk> \<Longrightarrow> invar_ssf dfs_state"
  by (auto simp: invar_ssf_def)

lemma invar_ssf_holds_upd1[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skel_more_call_1_conds dfs_state; dc.invar_1 dfs_state; invar_ssf dfs_state\<rbrakk> \<Longrightarrow>
    invar_ssf (dc.DFS_skel_more_upd1 dfs_state)"
proof (intro invar_props_intros, goal_cases)
  case 1
  let ?v = "hd (stack dfs_state)"
  let ?w = "sel ((\<N>\<^sub>G ?v) -\<^sub>G (seen dfs_state))"
  have w: "?w \<in> t_set (\<N>\<^sub>G ?v) - t_set (seen dfs_state)"
    using \<open>dc.DFS_skel_more_call_1_conds dfs_state\<close> \<open>dc.invar_1 dfs_state\<close>
    by (auto elim!: invar_props_elims call_cond_elims)
  show ?case using 1 w by (auto simp: upd1_unfold elim!: invar_props_elims)
next
  case 2
  let ?v = "hd (stack dfs_state)"
  let ?w = "sel ((\<N>\<^sub>G ?v) -\<^sub>G (seen dfs_state))"
  have w: "?w \<in> t_set (\<N>\<^sub>G ?v) - t_set (seen dfs_state)"
    using \<open>dc.DFS_skel_more_call_1_conds dfs_state\<close> \<open>dc.invar_1 dfs_state\<close>
    by (auto elim!: invar_props_elims call_cond_elims)
  show ?case using 2 w by (auto simp: upd1_unfold elim!: invar_props_elims)
next
  case 3
  then show ?case by (auto simp: upd1_unfold elim!: invar_props_elims)
next
  case 4
  let ?v = "hd (stack dfs_state)"
  let ?w = "sel ((\<N>\<^sub>G ?v) -\<^sub>G (seen dfs_state))"
  have w: "?w \<in> t_set (\<N>\<^sub>G ?v) - t_set (seen dfs_state)"
    using \<open>dc.DFS_skel_more_call_1_conds dfs_state\<close> \<open>dc.invar_1 dfs_state\<close>
    by (auto elim!: invar_props_elims call_cond_elims)
  show ?case using 4 w by (auto simp: upd1_unfold elim!: invar_props_elims)
next
  case 5
  let ?v = "hd (stack dfs_state)"
  let ?w = "sel ((\<N>\<^sub>G ?v) -\<^sub>G (seen dfs_state))"
  have w: "?w \<in> t_set (\<N>\<^sub>G ?v) - t_set (seen dfs_state)"
    using \<open>dc.DFS_skel_more_call_1_conds dfs_state\<close> \<open>dc.invar_1 dfs_state\<close>
    by (auto elim!: invar_props_elims call_cond_elims)
  show ?case using 5 w by (auto simp: upd1_unfold elim!: invar_props_elims)
qed

lemma invar_ssf_holds_upd2[invar_holds_intros]:
  assumes "dc.DFS_skel_more_call_2_conds dfs_state" "dc.invar_1 dfs_state" "invar_fin dfs_state"
          "invar_ssf dfs_state"
  shows "invar_ssf (dc.DFS_skel_more_upd2 dfs_state)"
proof -
  obtain v stack_tl where stk: "stack dfs_state = v # stack_tl"
    using assms(1) by (auto elim!: call_cond_elims)
  have finv: "vset_inv (finished dfs_state)" using assms(3) by (auto simp: invar_fin_def)
  have props: "distinct (stack dfs_state)" "set (stack dfs_state) \<subseteq> t_set (seen dfs_state)"
       "t_set (finished dfs_state) \<subseteq> t_set (seen dfs_state)"
       "t_set (finished dfs_state) = t_set (seen dfs_state) - set (stack dfs_state)"
       "t_set (seen dfs_state) \<subseteq> dVs (Graph.digraph_abs G)"
    using assms(4) by (auto simp: invar_ssf_def)
  have fin2: "t_set (finished (dc.DFS_skel_more_upd2 dfs_state)) = Set.insert v (t_set (finished dfs_state))"
    using finv stk by (auto simp: upd2_unfold)
  have st2: "stack (dc.DFS_skel_more_upd2 dfs_state) = stack_tl"
    by (simp add: upd2_unfold stk)
  have se2: "seen (dc.DFS_skel_more_upd2 dfs_state) = seen dfs_state"
    by (simp add: upd2_unfold)
  show ?thesis
    unfolding invar_ssf_def st2 se2 fin2
    using props stk by auto
qed

lemma invar_ssf_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skel_more_ret_1_conds dfs_state; invar_ssf dfs_state\<rbrakk> \<Longrightarrow> invar_ssf (dc.DFS_skel_more_ret1 dfs_state)"
  by (force simp: dc.DFS_skel_more_ret1_def cyc_on_empty_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_ssf_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skel_more_ret_2_conds dfs_state; invar_ssf dfs_state\<rbrakk> \<Longrightarrow> invar_ssf (dc.DFS_skel_more_ret2 dfs_state)"
  by (force simp: dc.DFS_skel_more_ret2_def cyc_on_found_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_ssf_holds[invar_holds_intros]:
  assumes "dc.DFS_skel_more_dom dfs_state" "dc.invar_1 dfs_state" "invar_fin dfs_state" "invar_ssf dfs_state"
  shows "invar_ssf (dc.DFS_skel_more dfs_state)"
  using assms(2-)
proof(induction rule: dc.DFS_skel_more_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule dc.DFS_skel_more_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-) invar_holds_intros simp: dc.DFS_skel_more_simps[OF IH(1)])
qed

subsection \<open>The gray set is the stack\<close>

lemma invar_gray_props[invar_props_elims]:
  "invar_gray dfs_state \<Longrightarrow> (vset_inv (gray dfs_state) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_gray_def)

lemma invar_gray_intro[invar_props_intros]:
  "vset_inv (gray dfs_state) \<Longrightarrow> invar_gray dfs_state"
  by (auto simp: invar_gray_def)

lemma invar_gray_stack_props[invar_props_elims]:
  "invar_gray_stack dfs_state \<Longrightarrow>
    (t_set (gray dfs_state) = set (stack dfs_state) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_gray_stack_def)

lemma invar_gray_stack_intro[invar_props_intros]:
  "t_set (gray dfs_state) = set (stack dfs_state) \<Longrightarrow> invar_gray_stack dfs_state"
  by (auto simp: invar_gray_stack_def)

lemma invar_gray_holds_upd1[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skel_more_call_1_conds dfs_state; invar_gray dfs_state\<rbrakk> \<Longrightarrow>
    invar_gray (dc.DFS_skel_more_upd1 dfs_state)"
  by (auto simp: upd1_unfold elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_gray_holds_upd2[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skel_more_call_2_conds dfs_state; invar_gray dfs_state\<rbrakk> \<Longrightarrow>
    invar_gray (dc.DFS_skel_more_upd2 dfs_state)"
  by (auto simp: upd2_unfold elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_gray_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skel_more_ret_1_conds dfs_state; invar_gray dfs_state\<rbrakk> \<Longrightarrow> invar_gray (dc.DFS_skel_more_ret1 dfs_state)"
  by (auto simp: dc.DFS_skel_more_ret1_def cyc_on_empty_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_gray_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skel_more_ret_2_conds dfs_state; invar_gray dfs_state\<rbrakk> \<Longrightarrow> invar_gray (dc.DFS_skel_more_ret2 dfs_state)"
  by (auto simp: dc.DFS_skel_more_ret2_def cyc_on_found_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_gray_holds[invar_holds_intros]:
  assumes "dc.DFS_skel_more_dom dfs_state" "invar_gray dfs_state"
  shows "invar_gray (dc.DFS_skel_more dfs_state)"
  using assms(2-)
proof(induction rule: dc.DFS_skel_more_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule dc.DFS_skel_more_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-) invar_holds_intros simp: dc.DFS_skel_more_simps[OF IH(1)])
qed

lemma invar_gray_stack_holds_upd1[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skel_more_call_1_conds dfs_state; invar_gray dfs_state; invar_gray_stack dfs_state\<rbrakk> \<Longrightarrow>
    invar_gray_stack (dc.DFS_skel_more_upd1 dfs_state)"
  by (auto simp: upd1_unfold elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_gray_stack_holds_upd2[invar_holds_intros]:
  assumes "dc.DFS_skel_more_call_2_conds dfs_state" "invar_ssf dfs_state" "invar_gray dfs_state"
          "invar_gray_stack dfs_state"
  shows "invar_gray_stack (dc.DFS_skel_more_upd2 dfs_state)"
proof -
  obtain v stack_tl where stk: "stack dfs_state = v # stack_tl"
    using assms(1) by (auto elim!: call_cond_elims)
  have dis: "distinct (stack dfs_state)" using assms(2) by (auto simp: invar_ssf_def)
  have ginv: "vset_inv (gray dfs_state)" using assms(3) by (auto simp: invar_gray_def)
  have geq: "t_set (gray dfs_state) = set (stack dfs_state)"
    using assms(4) by (auto simp: invar_gray_stack_def)
  have "t_set (gray (dc.DFS_skel_more_upd2 dfs_state)) = t_set (gray dfs_state) - {v}"
    using ginv stk by (auto simp: upd2_unfold)
  also have "\<dots> = set stack_tl"
    using geq dis stk by auto
  finally have "t_set (gray (dc.DFS_skel_more_upd2 dfs_state))
      = set (stack (dc.DFS_skel_more_upd2 dfs_state))"
    by (simp add: upd2_unfold(1) stk)
  thus ?thesis by (rule invar_gray_stack_intro)
qed

lemma invar_gray_stack_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skel_more_ret_1_conds dfs_state; invar_gray_stack dfs_state\<rbrakk> \<Longrightarrow> invar_gray_stack (dc.DFS_skel_more_ret1 dfs_state)"
  by (auto simp: dc.DFS_skel_more_ret1_def cyc_on_empty_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_gray_stack_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skel_more_ret_2_conds dfs_state; invar_gray_stack dfs_state\<rbrakk> \<Longrightarrow> invar_gray_stack (dc.DFS_skel_more_ret2 dfs_state)"
  by (auto simp: dc.DFS_skel_more_ret2_def cyc_on_found_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_gray_stack_holds[invar_holds_intros]:
  assumes "dc.DFS_skel_more_dom dfs_state" "dc.invar_1 dfs_state" "invar_fin dfs_state"
          "invar_ssf dfs_state" "invar_gray dfs_state" "invar_gray_stack dfs_state"
  shows "invar_gray_stack (dc.DFS_skel_more dfs_state)"
  using assms(2-)
proof(induction rule: dc.DFS_skel_more_induct[OF assms(1)])
  case IH: (1 dfs_state)
  note simps = dc.DFS_skel_more_simps[OF IH(1)]
  show ?case
  proof (rule dc.DFS_skel_more_cases[where dfs_state = dfs_state])
    assume c: "dc.DFS_skel_more_call_1_conds dfs_state"
    have "invar_gray_stack (dc.DFS_skel_more (dc.DFS_skel_more_upd1 dfs_state))"
      by (rule IH(2)[OF c dc.invar_1_holds_1[OF c IH(4)] invar_fin_holds_upd1[OF c IH(5)]
                     invar_ssf_holds_upd1[OF c IH(4) IH(6)] invar_gray_holds_upd1[OF c IH(7)]
                     invar_gray_stack_holds_upd1[OF c IH(7) IH(8)]])
    thus "invar_gray_stack (dc.DFS_skel_more dfs_state)"
      by (simp add: simps(1)[OF c])
  next
    assume c: "dc.DFS_skel_more_call_2_conds dfs_state"
    have "invar_gray_stack (dc.DFS_skel_more (dc.DFS_skel_more_upd2 dfs_state))"
      by (rule IH(3)[OF c dc.invar_1_holds_2[OF c IH(4)] invar_fin_holds_upd2[OF c IH(5)]
                     invar_ssf_holds_upd2[OF c IH(4) IH(5) IH(6)] invar_gray_holds_upd2[OF c IH(7)]
                     invar_gray_stack_holds_upd2[OF c IH(6) IH(7) IH(8)]])
    thus "invar_gray_stack (dc.DFS_skel_more dfs_state)"
      by (simp add: simps(2)[OF c])
  next
    assume c: "dc.DFS_skel_more_ret_1_conds dfs_state"
    have "invar_gray_stack (dc.DFS_skel_more_ret1 dfs_state)"
      by (rule invar_gray_stack_holds_ret_1[OF c IH(8)])
    thus "invar_gray_stack (dc.DFS_skel_more dfs_state)"
      by (simp add: simps(3)[OF c])
  next
    assume c: "dc.DFS_skel_more_ret_2_conds dfs_state"
    have "invar_gray_stack (dc.DFS_skel_more_ret2 dfs_state)"
      by (rule invar_gray_stack_holds_ret_2[OF c IH(8)])
    thus "invar_gray_stack (dc.DFS_skel_more dfs_state)"
      by (simp add: simps(4)[OF c])
  qed
qed

text \<open>The promised agreement: under the structural invariants, the incremental back-edge test
  coincides with the library's \<open>seen - finished\<close> one. The invariant proofs below use \<open>gray\<close>
  directly (it is the simpler route); this records that nothing was changed semantically.\<close>
lemma cyc_found_agrees:
  assumes "dc.invar_1 dfs_state"
      and "invar_fin dfs_state"
      and "invar_ssf dfs_state"
      and "invar_gray dfs_state"
      and "invar_gray_stack dfs_state"
      and "stack dfs_state \<noteq> []"
  shows "cyc_found dfs_state \<longleftrightarrow>
         ((\<N>\<^sub>G (hd (stack dfs_state))) \<inter>\<^sub>G (seen dfs_state -\<^sub>G finished dfs_state)) \<noteq> \<emptyset>\<^sub>N"
proof -
  obtain v stack_tl where stk: "stack dfs_state = v # stack_tl"
    using assms(6) by (cases "stack dfs_state") auto
  have sinv: "vset_inv (seen dfs_state)" using assms(1) by (auto simp: dc.invar_1_def)
  have finv: "vset_inv (finished dfs_state)" using assms(2) by (auto simp: invar_fin_def)
  have ginv: "vset_inv (gray dfs_state)" using assms(4) by (auto simp: invar_gray_def)
  have geq: "t_set (gray dfs_state) = set (stack dfs_state)"
    using assms(5) by (auto simp: invar_gray_stack_def)
  have ninv: "vset_inv (\<N>\<^sub>G v)" using dc.graph_inv by auto
  have sf: "t_set (seen dfs_state) - t_set (finished dfs_state) = set (stack dfs_state)"
    using assms(3) by (auto simp: invar_ssf_def)
  have lhs_set: "t_set ((\<N>\<^sub>G v) \<inter>\<^sub>G (gray dfs_state)) = t_set (\<N>\<^sub>G v) \<inter> set (stack dfs_state)"
    using ninv ginv geq by auto
  have dinv: "vset_inv (seen dfs_state -\<^sub>G finished dfs_state)"
    using sinv finv by auto
  have rhs_set: "t_set ((\<N>\<^sub>G v) \<inter>\<^sub>G (seen dfs_state -\<^sub>G finished dfs_state))
                   = t_set (\<N>\<^sub>G v) \<inter> set (stack dfs_state)"
    using ninv dinv sinv finv sf by auto
  have linv: "vset_inv ((\<N>\<^sub>G v) \<inter>\<^sub>G (gray dfs_state))"
    using ninv ginv by auto
  have rinv: "vset_inv ((\<N>\<^sub>G v) \<inter>\<^sub>G (seen dfs_state -\<^sub>G finished dfs_state))"
    using ninv dinv by auto
  have l_iff: "((\<N>\<^sub>G v) \<inter>\<^sub>G (gray dfs_state)) \<noteq> \<emptyset>\<^sub>N \<longleftrightarrow>
               t_set (\<N>\<^sub>G v) \<inter> set (stack dfs_state) \<noteq> {}"
    using linv lhs_set by (force dest: Graph.vset.emptyD)
  have r_iff: "((\<N>\<^sub>G v) \<inter>\<^sub>G (seen dfs_state -\<^sub>G finished dfs_state)) \<noteq> \<emptyset>\<^sub>N \<longleftrightarrow>
               t_set (\<N>\<^sub>G v) \<inter> set (stack dfs_state) \<noteq> {}"
    using rinv rhs_set by (force dest: Graph.vset.emptyD)
  show ?thesis
    unfolding cyc_found_def stk using l_iff r_iff by simp
qed

subsection \<open>The unfinished set\<close>

lemma invar_unfin_props[invar_props_elims]:
  "invar_unfin dfs_state \<Longrightarrow> (vset_inv (unfinished dfs_state) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_unfin_def)

lemma invar_unfin_intro[invar_props_intros]:
  "vset_inv (unfinished dfs_state) \<Longrightarrow> invar_unfin dfs_state"
  by (auto simp: invar_unfin_def)

lemma invar_fin_unfin_props[invar_props_elims]:
  "invar_fin_unfin dfs_state \<Longrightarrow>
    (\<lbrakk>t_set (unfinished dfs_state) \<union> t_set (finished dfs_state) = dVs (Graph.digraph_abs G);
      t_set (unfinished dfs_state) \<inter> t_set (finished dfs_state) = {}\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_fin_unfin_def)

lemma invar_fin_unfin_intro[invar_props_intros]:
  "\<lbrakk>t_set (unfinished dfs_state) \<union> t_set (finished dfs_state) = dVs (Graph.digraph_abs G);
    t_set (unfinished dfs_state) \<inter> t_set (finished dfs_state) = {}\<rbrakk> \<Longrightarrow> invar_fin_unfin dfs_state"
  by (auto simp: invar_fin_unfin_def)

lemma invar_seed_props[invar_props_elims]:
  "invar_seed dfs_state \<Longrightarrow>
     (\<lbrakk>Set.insert s (t_set f) \<subseteq> t_set (seen dfs_state);
       t_set f \<subseteq> t_set (finished dfs_state)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_seed_def)

lemma invar_seed_intro[invar_props_intros]:
  "\<lbrakk>Set.insert s (t_set f) \<subseteq> t_set (seen dfs_state);
    t_set f \<subseteq> t_set (finished dfs_state)\<rbrakk> \<Longrightarrow> invar_seed dfs_state"
  by (auto simp: invar_seed_def)

lemma invar_unfin_holds_upd1[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skel_more_call_1_conds dfs_state; invar_unfin dfs_state\<rbrakk> \<Longrightarrow>
    invar_unfin (dc.DFS_skel_more_upd1 dfs_state)"
  by (auto simp: upd1_unfold elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_unfin_holds_upd2[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skel_more_call_2_conds dfs_state; invar_unfin dfs_state\<rbrakk> \<Longrightarrow>
    invar_unfin (dc.DFS_skel_more_upd2 dfs_state)"
  by (auto simp: upd2_unfold elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_unfin_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skel_more_ret_1_conds dfs_state; invar_unfin dfs_state\<rbrakk> \<Longrightarrow> invar_unfin (dc.DFS_skel_more_ret1 dfs_state)"
  by (auto simp: dc.DFS_skel_more_ret1_def cyc_on_empty_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_unfin_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skel_more_ret_2_conds dfs_state; invar_unfin dfs_state\<rbrakk> \<Longrightarrow> invar_unfin (dc.DFS_skel_more_ret2 dfs_state)"
  by (auto simp: dc.DFS_skel_more_ret2_def cyc_on_found_def elim!: invar_props_elims intro!: invar_props_intros)

subsection \<open>The seed is never lost\<close>

lemma invar_seed_holds_upd1[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skel_more_call_1_conds dfs_state; dc.invar_1 dfs_state; invar_seed dfs_state\<rbrakk> \<Longrightarrow>
    invar_seed (dc.DFS_skel_more_upd1 dfs_state)"
  by (auto simp: upd1_unfold elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_seed_holds_upd2[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skel_more_call_2_conds dfs_state; invar_fin dfs_state; invar_seed dfs_state\<rbrakk> \<Longrightarrow>
    invar_seed (dc.DFS_skel_more_upd2 dfs_state)"
  by (auto simp: upd2_unfold elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_seed_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skel_more_ret_1_conds dfs_state; invar_seed dfs_state\<rbrakk> \<Longrightarrow> invar_seed (dc.DFS_skel_more_ret1 dfs_state)"
  by (auto simp: dc.DFS_skel_more_ret1_def cyc_on_empty_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_seed_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skel_more_ret_2_conds dfs_state; invar_seed dfs_state\<rbrakk> \<Longrightarrow> invar_seed (dc.DFS_skel_more_ret2 dfs_state)"
  by (auto simp: dc.DFS_skel_more_ret2_def cyc_on_found_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_seed_holds[invar_holds_intros]:
  assumes "dc.DFS_skel_more_dom dfs_state" "dc.invar_1 dfs_state" "invar_fin dfs_state" "invar_seed dfs_state"
  shows "invar_seed (dc.DFS_skel_more dfs_state)"
  using assms(2-)
proof(induction rule: dc.DFS_skel_more_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule dc.DFS_skel_more_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-) invar_holds_intros simp: dc.DFS_skel_more_simps[OF IH(1)])
qed

lemma invar_unfin_holds[invar_holds_intros]:
  assumes "dc.DFS_skel_more_dom dfs_state" "invar_unfin dfs_state"
  shows "invar_unfin (dc.DFS_skel_more dfs_state)"
  using assms(2-)
proof(induction rule: dc.DFS_skel_more_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule dc.DFS_skel_more_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-) invar_holds_intros simp: dc.DFS_skel_more_simps[OF IH(1)])
qed

subsection \<open>The unfinished set stays the complement of the finished region\<close>

lemma invar_fin_unfin_holds_upd1[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skel_more_call_1_conds dfs_state; invar_fin_unfin dfs_state\<rbrakk> \<Longrightarrow>
    invar_fin_unfin (dc.DFS_skel_more_upd1 dfs_state)"
  by (auto simp: upd1_unfold elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_fin_unfin_holds_upd2[invar_holds_intros]:
  assumes "dc.DFS_skel_more_call_2_conds dfs_state" "invar_fin dfs_state" "invar_ssf dfs_state"
          "invar_unfin dfs_state" "invar_fin_unfin dfs_state"
  shows "invar_fin_unfin (dc.DFS_skel_more_upd2 dfs_state)"
proof -
  let ?v = "hd (stack dfs_state)"
  have vstack: "?v \<in> set (stack dfs_state)"
    using assms(1) by (auto elim!: call_cond_elims)
  have finv: "vset_inv (finished dfs_state)" using assms(2) by (auto simp: invar_fin_def)
  have vdVs: "?v \<in> dVs (Graph.digraph_abs G)"
   and vnotfin: "?v \<notin> t_set (finished dfs_state)"
    using assms(3) vstack by (auto simp: invar_ssf_def)
  have uinv: "vset_inv (unfinished dfs_state)" using assms(4) by (auto simp: invar_unfin_def)
  have un: "t_set (unfinished dfs_state) \<union> t_set (finished dfs_state) = dVs (Graph.digraph_abs G)"
   and dis: "t_set (unfinished dfs_state) \<inter> t_set (finished dfs_state) = {}"
    using assms(5) by (auto simp: invar_fin_unfin_def)
  have fin': "t_set (finished (dc.DFS_skel_more_upd2 dfs_state))
                = Set.insert ?v (t_set (finished dfs_state))"
    using finv by (auto simp: upd2_unfold)
  have unf': "t_set (unfinished (dc.DFS_skel_more_upd2 dfs_state))
                = t_set (unfinished dfs_state) - {?v}"
    using uinv by (auto simp: upd2_unfold)
  have vunf: "?v \<in> t_set (unfinished dfs_state)"
    using un vdVs vnotfin by auto
  show ?thesis
  proof (rule invar_fin_unfin_intro)
    show "t_set (unfinished (dc.DFS_skel_more_upd2 dfs_state))
            \<union> t_set (finished (dc.DFS_skel_more_upd2 dfs_state)) = dVs (Graph.digraph_abs G)"
      unfolding unf' fin' using un vunf by auto
    show "t_set (unfinished (dc.DFS_skel_more_upd2 dfs_state))
            \<inter> t_set (finished (dc.DFS_skel_more_upd2 dfs_state)) = {}"
      unfolding unf' fin' using dis by auto
  qed
qed

lemma invar_fin_unfin_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skel_more_ret_1_conds dfs_state; invar_fin_unfin dfs_state\<rbrakk> \<Longrightarrow> invar_fin_unfin (dc.DFS_skel_more_ret1 dfs_state)"
  by (auto simp: dc.DFS_skel_more_ret1_def cyc_on_empty_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_fin_unfin_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skel_more_ret_2_conds dfs_state; invar_fin_unfin dfs_state\<rbrakk> \<Longrightarrow> invar_fin_unfin (dc.DFS_skel_more_ret2 dfs_state)"
  by (auto simp: dc.DFS_skel_more_ret2_def cyc_on_found_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_fin_unfin_holds[invar_holds_intros]:
  assumes "dc.DFS_skel_more_dom dfs_state" "dc.invar_1 dfs_state" "invar_fin dfs_state"
          "invar_ssf dfs_state" "invar_unfin dfs_state" "invar_fin_unfin dfs_state"
  shows "invar_fin_unfin (dc.DFS_skel_more dfs_state)"
  using assms(2-)
proof(induction rule: dc.DFS_skel_more_induct[OF assms(1)])
  case IH: (1 dfs_state)
  note simps = dc.DFS_skel_more_simps[OF IH(1)]
  show ?case
  proof (rule dc.DFS_skel_more_cases[where dfs_state = dfs_state])
    assume c: "dc.DFS_skel_more_call_1_conds dfs_state"
    have "invar_fin_unfin (dc.DFS_skel_more (dc.DFS_skel_more_upd1 dfs_state))"
      by (rule IH(2)[OF c dc.invar_1_holds_1[OF c IH(4)] invar_fin_holds_upd1[OF c IH(5)]
                     invar_ssf_holds_upd1[OF c IH(4) IH(6)] invar_unfin_holds_upd1[OF c IH(7)]
                     invar_fin_unfin_holds_upd1[OF c IH(8)]])
    thus "invar_fin_unfin (dc.DFS_skel_more dfs_state)"
      by (simp add: simps(1)[OF c])
  next
    assume c: "dc.DFS_skel_more_call_2_conds dfs_state"
    have "invar_fin_unfin (dc.DFS_skel_more (dc.DFS_skel_more_upd2 dfs_state))"
      by (rule IH(3)[OF c dc.invar_1_holds_2[OF c IH(4)] invar_fin_holds_upd2[OF c IH(5)]
                     invar_ssf_holds_upd2[OF c IH(4) IH(5) IH(6)] invar_unfin_holds_upd2[OF c IH(7)]
                     invar_fin_unfin_holds_upd2[OF c IH(5) IH(6) IH(7) IH(8)]])
    thus "invar_fin_unfin (dc.DFS_skel_more dfs_state)"
      by (simp add: simps(2)[OF c])
  next
    assume c: "dc.DFS_skel_more_ret_1_conds dfs_state"
    have "invar_fin_unfin (dc.DFS_skel_more_ret1 dfs_state)"
      by (rule invar_fin_unfin_holds_ret_1[OF c IH(8)])
    thus "invar_fin_unfin (dc.DFS_skel_more dfs_state)"
      by (simp add: simps(3)[OF c])
  next
    assume c: "dc.DFS_skel_more_ret_2_conds dfs_state"
    have "invar_fin_unfin (dc.DFS_skel_more_ret2 dfs_state)"
      by (rule invar_fin_unfin_holds_ret_2[OF c IH(8)])
    thus "invar_fin_unfin (dc.DFS_skel_more dfs_state)"
      by (simp add: simps(4)[OF c])
  qed
qed

subsection \<open>Soundness: a reported cycle is a real directed cycle\<close>

lemma invar_cycle_true_props[invar_props_elims]:
  "invar_cycle_true dfs_state \<Longrightarrow>
     ((cycle dfs_state \<Longrightarrow> \<exists>c. Awalk_Defs.cycle (Graph.digraph_abs G) c) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_cycle_true_def)

lemma invar_cycle_true_intro[invar_props_intros]:
  "(cycle dfs_state \<Longrightarrow> \<exists>c. Awalk_Defs.cycle (Graph.digraph_abs G) c) \<Longrightarrow> invar_cycle_true dfs_state"
  by (auto simp: invar_cycle_true_def)

lemma invar_cycle_true_holds_upd1[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skel_more_call_1_conds dfs_state; invar_cycle_true dfs_state\<rbrakk> \<Longrightarrow> invar_cycle_true (dc.DFS_skel_more_upd1 dfs_state)"
  by (auto simp: upd1_unfold elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_cycle_true_holds_upd2[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skel_more_call_2_conds dfs_state; invar_cycle_true dfs_state\<rbrakk> \<Longrightarrow> invar_cycle_true (dc.DFS_skel_more_upd2 dfs_state)"
  by (auto simp: upd2_unfold elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_cycle_true_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skel_more_ret_1_conds dfs_state; invar_cycle_true dfs_state\<rbrakk> \<Longrightarrow> invar_cycle_true (dc.DFS_skel_more_ret1 dfs_state)"
  by (auto simp: dc.DFS_skel_more_ret1_def cyc_on_empty_def elim!: invar_props_elims intro!: invar_props_intros)

text \<open>The found-hook fires on a nonempty \<open>(\<N>\<^sub>G v) \<inter>\<^sub>G gray\<close>; via \<open>invar_gray_stack\<close> the witness
  is a neighbour \<^emph>\<open>on the stack\<close>, and the stack prefix up to it closes into a cycle exactly as in
  the library's proof.\<close>
lemma invar_cycle_true_holds_ret_2[invar_holds_intros]:
  assumes "dc.DFS_skel_more_ret_2_conds dfs_state" "dc.invar_1 dfs_state" "invar_fin dfs_state"
          "invar_2 dfs_state" "invar_ssf dfs_state" "invar_gray dfs_state"
          "invar_gray_stack dfs_state" "invar_cycle_true dfs_state"
  shows "invar_cycle_true (dc.DFS_skel_more_ret2 dfs_state)"
proof (intro invar_props_intros)
  let ?v = "hd (stack dfs_state)"
  have ne: "(\<N>\<^sub>G ?v) \<inter>\<^sub>G (gray dfs_state) \<noteq> \<emptyset>\<^sub>N"
   and stk: "stack dfs_state \<noteq> []"
    using assms(1) by (auto simp: dc.DFS_skel_more_ret_2_conds_def cyc_found_def split: list.splits)
  have ginv: "vset_inv (gray dfs_state)"
    using assms(6) by (auto simp: invar_gray_def)
  have geq: "t_set (gray dfs_state) = set (stack dfs_state)"
    using assms(7) by (auto simp: invar_gray_stack_def)
  have ninv: "vset_inv (\<N>\<^sub>G ?v)" using dc.graph_inv by auto
  have iinv: "vset_inv ((\<N>\<^sub>G ?v) \<inter>\<^sub>G (gray dfs_state))"
    using ninv ginv by auto
  obtain x where x_mem: "x \<in> t_set ((\<N>\<^sub>G ?v) \<inter>\<^sub>G (gray dfs_state))"
    using ne iinv by (force dest!: Graph.vset.choose')
  have xN: "x \<in> t_set (\<N>\<^sub>G ?v)"
   and xstack: "x \<in> set (stack dfs_state)"
    using x_mem ninv ginv geq by auto
  have edge: "(?v, x) \<in> Graph.digraph_abs G"
    using xN by auto
  have vverts: "?v \<in> dVs (Graph.digraph_abs G)"
   and xverts: "x \<in> dVs (Graph.digraph_abs G)"
    using edge by (auto simp: dVs_def)
  have "x \<in> set (rev (stack dfs_state))" using xstack by simp
  then obtain xs zs where xz: "rev (stack dfs_state) = xs @ x # zs"
    using split_list by fastforce
  define p where "p = x # zs"
  have rs: "rev (stack dfs_state) = xs @ p" and pne: "p \<noteq> []" and hdp: "hd p = x"
    by (simp_all add: p_def xz)
  have vwp: "Vwalk.vwalk (Graph.digraph_abs G) p"
    using rs assms(4) append_vwalk_suff by (force elim!: invar_props_elims)
  have lastp: "last p = ?v"
  proof -
    have "last (rev (stack dfs_state)) = ?v" using stk by (simp add: last_rev)
    moreover
    have "last (rev (stack dfs_state)) = last p" using rs pne by (simp add: last_appendR)
    ultimately
    show ?thesis by simp
  qed
  have vbet: "Vwalk.vwalk_bet (Graph.digraph_abs G) x p ?v"
    using vwp hdp pne lastp unfolding vwalk_bet_def by blast
  have awp: "awalk (Graph.digraph_abs G) x (edges_of_vwalk p) ?v"
    using vwalk_imp_awalk[OF vbet] by blast
  have awe: "awalk (Graph.digraph_abs G) ?v [(?v, x)] x"
    using edge vverts xverts unfolding awalk_def by auto
  have closed: "awalk (Graph.digraph_abs G) x ((edges_of_vwalk p) @ [(?v, x)]) x"
    using awalk_appendI[OF awp awe] by simp
  have edeq: "(edges_of_vwalk p) @ [(?v, x)] = edges_of_vwalk (p @ [x])"
    using lastp pne by (simp add: edges_of_vwalk_append_3)
  have verts: "awalk_verts x ((edges_of_vwalk p) @ [(?v, x)]) = p @ [x]"
  proof -
    have hdpx: "hd (p @ [x]) = x" using hdp pne by (simp add: hd_append)
    have "awalk_verts x (edges_of_vwalk (p @ [x])) = p @ [x]"
      using awalk_vwalk_id[OF _ hdpx] by simp
    thus ?thesis by (simp add: edeq)
  qed
  have distinct_rev: "distinct (rev (stack dfs_state))"
    using assms(5) by (force elim!: invar_props_elims)
  hence dp: "distinct p" using rs by force
  have dtl: "distinct (tl (p @ [x]))"
  proof -
    obtain p' where pcons: "p = x # p'" using pne hdp by (cases p) auto
    have "distinct (x # p')" using dp pcons by simp
    hence "distinct p'" "x \<notin> set p'" by auto
    hence "distinct (p' @ [x])" by simp
    thus ?thesis using pcons by simp
  qed
  have "Awalk_Defs.cycle (Graph.digraph_abs G) ((edges_of_vwalk p) @ [(?v, x)])"
    unfolding Awalk_Defs.cycle_def using closed dtl verts by auto
  thus "cycle (dc.DFS_skel_more_ret2 dfs_state) \<Longrightarrow> \<exists>c. Awalk_Defs.cycle (Graph.digraph_abs G) c" by blast
qed

lemma invar_cycle_true_holds[invar_holds_intros]:
  assumes "dc.DFS_skel_more_dom dfs_state" "dc.invar_1 dfs_state" "invar_fin dfs_state"
          "invar_2 dfs_state" "invar_ssf dfs_state" "invar_gray dfs_state"
          "invar_gray_stack dfs_state" "invar_cycle_true dfs_state"
  shows "invar_cycle_true (dc.DFS_skel_more dfs_state)"
  using assms(2-)
proof(induction rule: dc.DFS_skel_more_induct[OF assms(1)])
  case IH: (1 dfs_state)
  note simps = dc.DFS_skel_more_simps[OF IH(1)]
  show ?case
  proof (rule dc.DFS_skel_more_cases[where dfs_state = dfs_state])
    assume c: "dc.DFS_skel_more_call_1_conds dfs_state"
    have "invar_cycle_true (dc.DFS_skel_more (dc.DFS_skel_more_upd1 dfs_state))"
      by (rule IH(2)[OF c dc.invar_1_holds_1[OF c IH(4)] invar_fin_holds_upd1[OF c IH(5)]
                     invar_2_holds_upd1[OF c IH(4) IH(6)] invar_ssf_holds_upd1[OF c IH(4) IH(7)]
                     invar_gray_holds_upd1[OF c IH(8)]
                     invar_gray_stack_holds_upd1[OF c IH(8) IH(9)]
                     invar_cycle_true_holds_upd1[OF c IH(10)]])
    thus "invar_cycle_true (dc.DFS_skel_more dfs_state)"
      by (simp add: simps(1)[OF c])
  next
    assume c: "dc.DFS_skel_more_call_2_conds dfs_state"
    have "invar_cycle_true (dc.DFS_skel_more (dc.DFS_skel_more_upd2 dfs_state))"
      by (rule IH(3)[OF c dc.invar_1_holds_2[OF c IH(4)] invar_fin_holds_upd2[OF c IH(5)]
                     invar_2_holds_upd2[OF c IH(6)] invar_ssf_holds_upd2[OF c IH(4) IH(5) IH(7)]
                     invar_gray_holds_upd2[OF c IH(8)]
                     invar_gray_stack_holds_upd2[OF c IH(7) IH(8) IH(9)]
                     invar_cycle_true_holds_upd2[OF c IH(10)]])
    thus "invar_cycle_true (dc.DFS_skel_more dfs_state)"
      by (simp add: simps(2)[OF c])
  next
    assume c: "dc.DFS_skel_more_ret_1_conds dfs_state"
    have "invar_cycle_true (dc.DFS_skel_more_ret1 dfs_state)"
      by (rule invar_cycle_true_holds_ret_1[OF c IH(10)])
    thus "invar_cycle_true (dc.DFS_skel_more dfs_state)"
      by (simp add: simps(3)[OF c])
  next
    assume c: "dc.DFS_skel_more_ret_2_conds dfs_state"
    have "invar_cycle_true (dc.DFS_skel_more_ret2 dfs_state)"
      by (rule invar_cycle_true_holds_ret_2[OF c IH(4) IH(5) IH(6) IH(7) IH(8) IH(9) IH(10)])
    thus "invar_cycle_true (dc.DFS_skel_more dfs_state)"
      by (simp add: simps(4)[OF c])
  qed
qed

theorem DFS_dircycle_tracked_sound:
  assumes "cycle (dc.DFS_skel_more dircycle_tracked_initial_state)"
  shows "\<exists>c. Awalk_Defs.cycle (Graph.digraph_abs G) c"
proof -
  have "invar_cycle_true (dc.DFS_skel_more dircycle_tracked_initial_state)"
    by (intro invar_cycle_true_holds dircycle_tracked_initial_dom initial_invars
              initial_fin initial_struct initial_gray initial_gray_stack)
       (auto simp: invar_cycle_true_def dircycle_tracked_initial_state_def)
  thus ?thesis using assms by (auto elim!: invar_props_elims)
qed

subsection \<open>Completeness: no report means the finished subgraph is acyclic\<close>

lemma invar_finished_closed_props[invar_props_elims]:
  "invar_finished_closed dfs_state \<Longrightarrow>
    ((\<And>u w. u \<in> t_set (finished dfs_state) \<Longrightarrow> (u, w) \<in> Graph.digraph_abs G \<Longrightarrow> w \<in> t_set (finished dfs_state)) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_finished_closed_def)

lemma invar_finished_closed_intro[invar_props_intros]:
  "(\<And>u w. u \<in> t_set (finished dfs_state) \<Longrightarrow> (u, w) \<in> Graph.digraph_abs G \<Longrightarrow> w \<in> t_set (finished dfs_state))
    \<Longrightarrow> invar_finished_closed dfs_state"
  by (auto simp: invar_finished_closed_def)

text \<open>Out-neighbours of the popped vertex are all already finished: none is unseen (else
  \<open>call_1\<close> would fire), none is gray (else \<open>cyc_found\<close> would fire), and via \<open>invar_gray_stack\<close> +
  \<open>invar_ssf\<close> non-gray seen vertices are finished.\<close>
lemma upd2_vout:
  assumes "dc.DFS_skel_more_call_2_conds dfs_state" "dc.invar_1 dfs_state" "invar_fin dfs_state"
          "invar_ssf dfs_state" "invar_gray dfs_state" "invar_gray_stack dfs_state"
    and "(hd (stack dfs_state), w) \<in> Graph.digraph_abs G"
  shows "w \<in> t_set (finished dfs_state)"
proof -
  let ?v = "hd (stack dfs_state)"
  have sinv: "vset_inv (seen dfs_state)" using assms(2) by (auto simp: dc.invar_1_def)
  have ginv: "vset_inv (gray dfs_state)" using assms(5) by (auto simp: invar_gray_def)
  have geq: "t_set (gray dfs_state) = set (stack dfs_state)"
    using assms(6) by (auto simp: invar_gray_stack_def)
  have ninv: "vset_inv (\<N>\<^sub>G ?v)" using dc.graph_inv by auto
  have wN: "w \<in> t_set (\<N>\<^sub>G ?v)"
    using assms(7) dc.graph_inv by (auto intro!: Graph.are_connected_absI)
  have d_empty: "(\<N>\<^sub>G ?v) -\<^sub>G (seen dfs_state) = \<emptyset>\<^sub>N"
    using assms(1) by (auto elim!: call_cond_elims)
  have i_empty: "(\<N>\<^sub>G ?v) \<inter>\<^sub>G (gray dfs_state) = \<emptyset>\<^sub>N"
  proof -
    obtain v stack_tl where stk: "stack dfs_state = v # stack_tl"
      using assms(1) by (auto elim!: call_cond_elims)
    have "\<not> cyc_found dfs_state" using assms(1) by (auto elim!: call_cond_elims)
    thus ?thesis using stk by (simp add: cyc_found_def)
  qed
  have nsub: "t_set (\<N>\<^sub>G ?v) \<subseteq> t_set (seen dfs_state)"
  proof -
    have "t_set (\<N>\<^sub>G ?v) - t_set (seen dfs_state) = t_set ((\<N>\<^sub>G ?v) -\<^sub>G (seen dfs_state))"
      using ninv sinv by auto
    also have "... = {}" by (simp add: d_empty)
    finally show ?thesis by blast
  qed
  have nint: "t_set (\<N>\<^sub>G ?v) \<inter> set (stack dfs_state) = {}"
  proof -
    have "t_set (\<N>\<^sub>G ?v) \<inter> t_set (gray dfs_state) = t_set ((\<N>\<^sub>G ?v) \<inter>\<^sub>G (gray dfs_state))"
      using ninv ginv by auto
    also have "... = {}" by (simp add: i_empty)
    finally show ?thesis using geq by simp
  qed
  have feq: "t_set (finished dfs_state) = t_set (seen dfs_state) - set (stack dfs_state)"
    using assms(4) by (auto simp: invar_ssf_def)
  show ?thesis using wN nsub nint feq by blast
qed

lemma invar_finished_closed_holds_upd1[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skel_more_call_1_conds dfs_state; invar_finished_closed dfs_state\<rbrakk> \<Longrightarrow>
    invar_finished_closed (dc.DFS_skel_more_upd1 dfs_state)"
  by (auto simp: invar_finished_closed_def upd1_unfold)

lemma invar_finished_closed_holds_upd2[invar_holds_intros]:
  assumes "dc.DFS_skel_more_call_2_conds dfs_state" "dc.invar_1 dfs_state" "invar_fin dfs_state"
          "invar_ssf dfs_state" "invar_gray dfs_state" "invar_gray_stack dfs_state"
          "invar_finished_closed dfs_state"
  shows "invar_finished_closed (dc.DFS_skel_more_upd2 dfs_state)"
proof (intro invar_props_intros)
  fix u w
  assume uin: "u \<in> t_set (finished (dc.DFS_skel_more_upd2 dfs_state))"
     and edge: "(u, w) \<in> Graph.digraph_abs G"
  have fin2: "t_set (finished (dc.DFS_skel_more_upd2 dfs_state)) = Set.insert (hd (stack dfs_state)) (t_set (finished dfs_state))"
    using assms(3) by (auto simp: upd2_unfold elim!: invar_props_elims)
  consider "u = hd (stack dfs_state)" | "u \<in> t_set (finished dfs_state)"
    using uin fin2 by auto
  then have "w \<in> t_set (finished dfs_state)"
  proof cases
    case 1 thus ?thesis using upd2_vout[OF assms(1,2,3,4,5,6)] edge by auto
  next
    case 2 thus ?thesis using assms(7) edge by (auto elim!: invar_props_elims)
  qed
  thus "w \<in> t_set (finished (dc.DFS_skel_more_upd2 dfs_state))" using fin2 by simp
qed

lemma invar_finished_closed_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skel_more_ret_1_conds dfs_state; invar_finished_closed dfs_state\<rbrakk> \<Longrightarrow>
    invar_finished_closed (dc.DFS_skel_more_ret1 dfs_state)"
  by (auto simp: invar_finished_closed_def dc.DFS_skel_more_ret1_def cyc_on_empty_def)

lemma invar_finished_closed_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skel_more_ret_2_conds dfs_state; invar_finished_closed dfs_state\<rbrakk> \<Longrightarrow>
    invar_finished_closed (dc.DFS_skel_more_ret2 dfs_state)"
  by (auto simp: invar_finished_closed_def dc.DFS_skel_more_ret2_def cyc_on_found_def)

lemma invar_finished_closed_holds[invar_holds_intros]:
  assumes "dc.DFS_skel_more_dom dfs_state" "dc.invar_1 dfs_state" "invar_fin dfs_state"
          "invar_ssf dfs_state" "invar_gray dfs_state" "invar_gray_stack dfs_state"
          "invar_finished_closed dfs_state"
  shows "invar_finished_closed (dc.DFS_skel_more dfs_state)"
  using assms(2-)
proof(induction rule: dc.DFS_skel_more_induct[OF assms(1)])
  case IH: (1 dfs_state)
  note simps = dc.DFS_skel_more_simps[OF IH(1)]
  show ?case
  proof (rule dc.DFS_skel_more_cases[where dfs_state = dfs_state])
    assume c: "dc.DFS_skel_more_call_1_conds dfs_state"
    have "invar_finished_closed (dc.DFS_skel_more (dc.DFS_skel_more_upd1 dfs_state))"
      by (rule IH(2)[OF c dc.invar_1_holds_1[OF c IH(4)] invar_fin_holds_upd1[OF c IH(5)]
                     invar_ssf_holds_upd1[OF c IH(4) IH(6)] invar_gray_holds_upd1[OF c IH(7)]
                     invar_gray_stack_holds_upd1[OF c IH(7) IH(8)]
                     invar_finished_closed_holds_upd1[OF c IH(9)]])
    thus "invar_finished_closed (dc.DFS_skel_more dfs_state)"
      by (simp add: simps(1)[OF c])
  next
    assume c: "dc.DFS_skel_more_call_2_conds dfs_state"
    have "invar_finished_closed (dc.DFS_skel_more (dc.DFS_skel_more_upd2 dfs_state))"
      by (rule IH(3)[OF c dc.invar_1_holds_2[OF c IH(4)] invar_fin_holds_upd2[OF c IH(5)]
                     invar_ssf_holds_upd2[OF c IH(4) IH(5) IH(6)] invar_gray_holds_upd2[OF c IH(7)]
                     invar_gray_stack_holds_upd2[OF c IH(6) IH(7) IH(8)]
                     invar_finished_closed_holds_upd2[OF c IH(4) IH(5) IH(6) IH(7) IH(8) IH(9)]])
    thus "invar_finished_closed (dc.DFS_skel_more dfs_state)"
      by (simp add: simps(2)[OF c])
  next
    assume c: "dc.DFS_skel_more_ret_1_conds dfs_state"
    have "invar_finished_closed (dc.DFS_skel_more_ret1 dfs_state)"
      by (rule invar_finished_closed_holds_ret_1[OF c IH(9)])
    thus "invar_finished_closed (dc.DFS_skel_more dfs_state)"
      by (simp add: simps(3)[OF c])
  next
    assume c: "dc.DFS_skel_more_ret_2_conds dfs_state"
    have "invar_finished_closed (dc.DFS_skel_more_ret2 dfs_state)"
      by (rule invar_finished_closed_holds_ret_2[OF c IH(9)])
    thus "invar_finished_closed (dc.DFS_skel_more dfs_state)"
      by (simp add: simps(4)[OF c])
  qed
qed

text \<open>A vertex on a closed walk is the target of one of its edges.\<close>
lemma closed_walk_has_in_edge:
  assumes "awalk E u c u" "c \<noteq> []" "x \<in> set (awalk_verts u c)"
  shows "\<exists>e \<in> set c. snd e = x"
proof -
  have cas: "cas u c u" using assms(1) by (simp add: awalk_def)
  hence "fst (hd c) = u" using assms(2) by (cases c) auto
  hence av: "awalk_verts u c = u # map snd c" using cas by (simp add: awalk_verts_conv')
  have sndlast: "snd (last c) = u" using awalk_last[OF assms(1) assms(2)] .
  have "map snd c \<noteq> []" using assms(2) by simp
  moreover
  have "last (map snd c) = u" using sndlast assms(2) by (simp add: last_map)
  ultimately
  have "u \<in> set (map snd c)" using last_in_set by blast
  thus ?thesis using av assms(3) by auto
qed

lemma invar_cycle_false_props[invar_props_elims]:
  "invar_cycle_false dfs_state \<Longrightarrow>
    ((\<not> cycle dfs_state \<Longrightarrow> \<nexists>c. Awalk_Defs.cycle (Graph.digraph_abs G \<downharpoonright> t_set (finished dfs_state)) c) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_cycle_false_def)

lemma invar_cycle_false_intro[invar_props_intros]:
  "(\<not> cycle dfs_state \<Longrightarrow> \<nexists>c. Awalk_Defs.cycle (Graph.digraph_abs G \<downharpoonright> t_set (finished dfs_state)) c) \<Longrightarrow>
    invar_cycle_false dfs_state"
  by (auto simp: invar_cycle_false_def)

lemma invar_cycle_false_holds_upd1[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skel_more_call_1_conds dfs_state; invar_cycle_false dfs_state\<rbrakk> \<Longrightarrow> invar_cycle_false (dc.DFS_skel_more_upd1 dfs_state)"
  by (auto simp: upd1_unfold elim!: invar_props_elims intro!: invar_props_intros)


lemma invar_cycle_false_holds_upd2[invar_holds_intros]:
  assumes "dc.DFS_skel_more_call_2_conds dfs_state" "dc.invar_1 dfs_state" "invar_fin dfs_state"
          "invar_ssf dfs_state" "invar_gray dfs_state" "invar_gray_stack dfs_state"
          "invar_finished_closed dfs_state" "invar_cycle_false dfs_state"
  shows "invar_cycle_false (dc.DFS_skel_more_upd2 dfs_state)"
proof (intro invar_props_intros)
  assume notcyc': "\<not> cycle (dc.DFS_skel_more_upd2 dfs_state)"
  let ?v = "hd (stack dfs_state)"
  let ?F = "t_set (finished dfs_state)"
  let ?DG = "Graph.digraph_abs G"
  have notcyc: "\<not> cycle dfs_state" using notcyc' by (simp add: upd2_unfold)
  have finup: "t_set (finished (dc.DFS_skel_more_upd2 dfs_state)) = Set.insert ?v ?F"
    using assms(3) by (auto simp: upd2_unfold invar_fin_def)
  have acycF: "\<nexists>c. Awalk_Defs.cycle (?DG \<downharpoonright> ?F) c"
    using assms(8) notcyc by (auto simp: invar_cycle_false_def)
  have vstack: "?v \<in> set (stack dfs_state)" using assms(1) by (auto elim!: call_cond_elims)
  have vnotF: "?v \<notin> ?F" using vstack assms(4) by (auto simp: invar_ssf_def)
  have closedF: "\<And>u w. u \<in> ?F \<Longrightarrow> (u, w) \<in> ?DG \<Longrightarrow> w \<in> ?F"
    using assms(7) unfolding invar_finished_closed_def by blast
  have no_in: "(u, ?v) \<notin> (?DG \<downharpoonright> Set.insert ?v ?F)" for u
  proof
    assume e: "(u, ?v) \<in> (?DG \<downharpoonright> Set.insert ?v ?F)"
    have uin: "u \<in> Set.insert ?v ?F" and edge: "(u, ?v) \<in> ?DG"
      using e by (auto simp: induce_subgraph_def)
    show False
    proof (cases "u = ?v")
      case True
      hence "?v \<in> t_set (finished dfs_state)"
        using upd2_vout[OF assms(1,2,3,4,5,6)] edge by blast
      thus False using vnotF by blast
    next
      case False
      hence "u \<in> ?F" using uin by blast
      thus False using closedF edge vnotF by blast
    qed
  qed
  show "\<nexists>c. Awalk_Defs.cycle (?DG \<downharpoonright> t_set (finished (dc.DFS_skel_more_upd2 dfs_state))) c"
    unfolding finup
  proof (rule notI, erule exE)
    fix c assume cyc: "Awalk_Defs.cycle (?DG \<downharpoonright> Set.insert ?v ?F) c"
    then obtain u where
        aw: "awalk (?DG \<downharpoonright> Set.insert ?v ?F) u c u"
        and cne: "c \<noteq> []"
        and dtl: "distinct (tl (awalk_verts u c))"
      by (auto simp: Awalk_Defs.cycle_def)
    have edges_sub: "set c \<subseteq> (?DG \<downharpoonright> Set.insert ?v ?F)" using aw by (auto simp: awalk_def)
    have ucas: "cas u c u" using aw by (simp add: awalk_def)
    have vnotverts: "?v \<notin> set (awalk_verts u c)"
    proof
      assume "?v \<in> set (awalk_verts u c)"
      then obtain e where emem: "e \<in> set c" and esnd: "snd e = ?v"
        using closed_walk_has_in_edge[OF aw cne] by blast
      have "e \<in> (?DG \<downharpoonright> Set.insert ?v ?F)" using emem edges_sub by blast
      hence "(fst e, snd e) \<in> (?DG \<downharpoonright> Set.insert ?v ?F)" by simp
      hence "(fst e, ?v) \<in> (?DG \<downharpoonright> Set.insert ?v ?F)" using esnd by simp
      thus False using no_in by blast
    qed
    have verts_eq: "set (awalk_verts u c) = set (map fst c) \<union> set (map snd c)"
      using set_awalk_verts_not_Nil_cas[OF ucas cne] by simp
    have subF: "set c \<subseteq> (?DG \<downharpoonright> ?F)"
    proof
      fix e assume ec: "e \<in> set c"
      hence ein: "e \<in> (?DG \<downharpoonright> Set.insert ?v ?F)" using edges_sub by auto
      have fv: "fst e \<in> set (awalk_verts u c)" using ec by (auto simp: verts_eq)
      have sv: "snd e \<in> set (awalk_verts u c)" using ec by (auto simp: verts_eq)
      show "e \<in> (?DG \<downharpoonright> ?F)"
        using fv sv vnotverts ein by (cases e) (auto simp: induce_subgraph_def)
    qed
    have "fst (hd c) = u" using ucas cne by (cases c) auto
    then obtain w cs where c_eq: "c = (u, w) # cs" using cne by (cases c) auto
    have uinF: "u \<in> dVs (?DG \<downharpoonright> ?F)"
      using subF c_eq by (auto simp: dVs_def)
    have "awalk (?DG \<downharpoonright> ?F) u c u" using subF uinF ucas by (simp add: awalk_def)
    hence "Awalk_Defs.cycle (?DG \<downharpoonright> ?F) c" using cne dtl by (auto simp: Awalk_Defs.cycle_def)
    thus False using acycF by blast
  qed
qed

lemma invar_cycle_false_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skel_more_ret_1_conds dfs_state; invar_cycle_false dfs_state\<rbrakk> \<Longrightarrow> invar_cycle_false (dc.DFS_skel_more_ret1 dfs_state)"
  by (simp add: dc.DFS_skel_more_ret1_def cyc_on_empty_def)

lemma invar_cycle_false_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skel_more_ret_2_conds dfs_state; invar_cycle_false dfs_state\<rbrakk> \<Longrightarrow> invar_cycle_false (dc.DFS_skel_more_ret2 dfs_state)"
  by (simp add: dc.DFS_skel_more_ret2_def cyc_on_found_def invar_cycle_false_def)

text \<open>Unlike the sibling invariants, the generic
  \<open>by (auto intro!: IH(2-) invar_holds_intros simp: \<dots>)\<close> script diverges here (the accumulated
  \<open>invar_holds_intros\<close>/\<open>invar_props_intros\<close> sets are much larger than the library's by this
  point), so the four skeleton cases are discharged by explicit rule application instead.\<close>
lemma invar_cycle_false_holds[invar_holds_intros]:
  assumes "dc.DFS_skel_more_dom dfs_state" "dc.invar_1 dfs_state" "invar_fin dfs_state"
          "invar_ssf dfs_state" "invar_gray dfs_state" "invar_gray_stack dfs_state"
          "invar_finished_closed dfs_state" "invar_cycle_false dfs_state"
  shows "invar_cycle_false (dc.DFS_skel_more dfs_state)"
  using assms(2-)
proof(induction rule: dc.DFS_skel_more_induct[OF assms(1)])
  case IH: (1 dfs_state)
  note simps = dc.DFS_skel_more_simps[OF IH(1)]
  show ?case
  proof (rule dc.DFS_skel_more_cases[where dfs_state = dfs_state])
    assume c: "dc.DFS_skel_more_call_1_conds dfs_state"
    have "invar_cycle_false (dc.DFS_skel_more (dc.DFS_skel_more_upd1 dfs_state))"
      by (rule IH(2)[OF c dc.invar_1_holds_1[OF c IH(4)] invar_fin_holds_upd1[OF c IH(5)]
                     invar_ssf_holds_upd1[OF c IH(4) IH(6)] invar_gray_holds_upd1[OF c IH(7)]
                     invar_gray_stack_holds_upd1[OF c IH(7) IH(8)]
                     invar_finished_closed_holds_upd1[OF c IH(9)]
                     invar_cycle_false_holds_upd1[OF c IH(10)]])
    thus "invar_cycle_false (dc.DFS_skel_more dfs_state)"
      by (simp add: simps(1)[OF c])
  next
    assume c: "dc.DFS_skel_more_call_2_conds dfs_state"
    have "invar_cycle_false (dc.DFS_skel_more (dc.DFS_skel_more_upd2 dfs_state))"
      by (rule IH(3)[OF c dc.invar_1_holds_2[OF c IH(4)] invar_fin_holds_upd2[OF c IH(5)]
                     invar_ssf_holds_upd2[OF c IH(4) IH(5) IH(6)]
                     invar_gray_holds_upd2[OF c IH(7)]
                     invar_gray_stack_holds_upd2[OF c IH(6) IH(7) IH(8)]
                     invar_finished_closed_holds_upd2[OF c IH(4) IH(5) IH(6) IH(7) IH(8) IH(9)]
                     invar_cycle_false_holds_upd2[OF c IH(4) IH(5) IH(6) IH(7) IH(8) IH(9) IH(10)]])
    thus "invar_cycle_false (dc.DFS_skel_more dfs_state)"
      by (simp add: simps(2)[OF c])
  next
    assume c: "dc.DFS_skel_more_ret_1_conds dfs_state"
    have "invar_cycle_false (dc.DFS_skel_more_ret1 dfs_state)"
      by (rule invar_cycle_false_holds_ret_1[OF c IH(10)])
    thus "invar_cycle_false (dc.DFS_skel_more dfs_state)"
      by (simp add: simps(3)[OF c])
  next
    assume c: "dc.DFS_skel_more_ret_2_conds dfs_state"
    have "invar_cycle_false (dc.DFS_skel_more_ret2 dfs_state)"
      by (rule invar_cycle_false_holds_ret_2[OF c IH(10)])
    thus "invar_cycle_false (dc.DFS_skel_more dfs_state)"
      by (simp add: simps(4)[OF c])
  qed
qed

text \<open>When the run reports no cycle it ended at the empty-stack return.\<close>
lemma no_cycle_ret_1:
  assumes "dc.DFS_skel_more_dom dfs_state" "\<not> cycle (dc.DFS_skel_more dfs_state)"
  shows "dc.DFS_skel_more_ret_1_conds (dc.DFS_skel_more dfs_state)"
  using assms(2)
proof(induction rule: dc.DFS_skel_more_induct[OF assms(1)])
  case IH: (1 dfs_state)
  note simps = dc.DFS_skel_more_simps[OF IH(1)]
  show ?case
  proof (rule dc.DFS_skel_more_cases[where dfs_state = dfs_state])
    assume c: "dc.DFS_skel_more_call_1_conds dfs_state"
    have ncyc: "\<not> cycle (dc.DFS_skel_more (dc.DFS_skel_more_upd1 dfs_state))"
      using IH(4) c by (simp add: simps(1))
    have "dc.DFS_skel_more_ret_1_conds (dc.DFS_skel_more (dc.DFS_skel_more_upd1 dfs_state))"
      using IH(2)[OF c] ncyc by blast
    thus "dc.DFS_skel_more_ret_1_conds (dc.DFS_skel_more dfs_state)"
      using c by (simp add: simps(1))
  next
    assume c: "dc.DFS_skel_more_call_2_conds dfs_state"
    have ncyc: "\<not> cycle (dc.DFS_skel_more (dc.DFS_skel_more_upd2 dfs_state))"
      using IH(4) c by (simp add: simps(2))
    have "dc.DFS_skel_more_ret_1_conds (dc.DFS_skel_more (dc.DFS_skel_more_upd2 dfs_state))"
      using IH(3)[OF c] ncyc by blast
    thus "dc.DFS_skel_more_ret_1_conds (dc.DFS_skel_more dfs_state)"
      using c by (simp add: simps(2))
  next
    assume c: "dc.DFS_skel_more_ret_1_conds dfs_state"
    thus "dc.DFS_skel_more_ret_1_conds (dc.DFS_skel_more dfs_state)"
      by (simp add: simps(3) dc.DFS_skel_more_ret1_def cyc_on_empty_def)
  next
    assume c: "dc.DFS_skel_more_ret_2_conds dfs_state"
    have "cycle (dc.DFS_skel_more dfs_state)"
      using c by (simp add: simps(4) dc.DFS_skel_more_ret2_def cyc_on_found_def)
    thus "dc.DFS_skel_more_ret_1_conds (dc.DFS_skel_more dfs_state)"
      using IH(4) by blast
  qed
qed

text \<open>Completeness reports on \<open>finished\<close> rather than \<open>seen\<close>: the outer loop consumes exactly the
  finished region.\<close>
theorem DFS_dircycle_tracked_complete:
  assumes "\<not> cycle (dc.DFS_skel_more dircycle_tracked_initial_state)"
  shows "\<nexists>c. Awalk_Defs.cycle (Graph.digraph_abs G \<downharpoonright> t_set (finished (dc.DFS_skel_more dircycle_tracked_initial_state))) c"
proof -
  have dom: "dc.DFS_skel_more_dom dircycle_tracked_initial_state"
    by (rule dircycle_tracked_initial_dom)
  have cf: "invar_cycle_false (dc.DFS_skel_more dircycle_tracked_initial_state)"
    by (rule invar_cycle_false_holds[OF dom initial_invars(1) initial_fin initial_struct(2)
             initial_gray initial_gray_stack initial_fc(1) initial_fc(2)])
  thus ?thesis using assms by (simp add: invar_cycle_false_def)
qed

subsection \<open>What one run exports to the outer (linear) loop\<close>

text \<open>The seven exports of \<open>DFS_DirCycle_Linear_Aux\<close> --- the enlarged finished region again
  satisfies the seed contract, the seed and the root are absorbed, and the run is sound and
  complete --- plus the two \<open>unfinished\<close> exports the tracked outer loop consumes \<^emph>\<open>instead of\<close>
  computing \<open>V -\<^sub>G fin\<close>: the result's unfinished set is a well-formed vset, and it is
  \<^emph>\<open>exactly\<close> the complement of the result's finished region in the vertex set
  (\<open>invar_fin_unfin\<close> re-established).\<close>


abbreviation "dircycle_tracked_result \<equiv> dc.DFS_skel_more dircycle_tracked_initial_state"

lemma dircycle_tracked_invars:
  shows "dc.invar_1 dircycle_tracked_result"
    and "invar_fin dircycle_tracked_result"
    and "invar_ssf dircycle_tracked_result"
    and "invar_finished_closed dircycle_tracked_result"
    and "invar_seed dircycle_tracked_result"
    and "invar_gray dircycle_tracked_result"
    and "invar_unfin dircycle_tracked_result"
    and "invar_gray_stack dircycle_tracked_result"
    and "invar_fin_unfin dircycle_tracked_result"
proof -
  note dom = dircycle_tracked_initial_dom
  show "dc.invar_1 dircycle_tracked_result"
    by (rule dc.invar_1_holds[OF dom initial_invars(1)])
  show "invar_fin dircycle_tracked_result"
    by (rule invar_fin_holds[OF dom initial_fin])
  show "invar_ssf dircycle_tracked_result"
    by (rule invar_ssf_holds[OF dom initial_invars(1) initial_fin initial_struct(2)])
  show "invar_finished_closed dircycle_tracked_result"
    by (rule invar_finished_closed_holds[OF dom initial_invars(1) initial_fin initial_struct(2)
             initial_gray initial_gray_stack initial_fc(1)])
  show "invar_seed dircycle_tracked_result"
    by (rule invar_seed_holds[OF dom initial_invars(1) initial_fin initial_seed])
  show "invar_gray dircycle_tracked_result"
    by (rule invar_gray_holds[OF dom initial_gray])
  show "invar_unfin dircycle_tracked_result"
    by (rule invar_unfin_holds[OF dom initial_unfin])
  show "invar_gray_stack dircycle_tracked_result"
    by (rule invar_gray_stack_holds[OF dom initial_invars(1) initial_fin initial_struct(2)
             initial_gray initial_gray_stack])
  show "invar_fin_unfin dircycle_tracked_result"
    by (rule invar_fin_unfin_holds[OF dom initial_invars(1) initial_fin initial_struct(2)
             initial_unfin initial_fin_unfin])
qed

text \<open>\<^bold>\<open>Export 1--3\<close>: the enlarged finished region again satisfies this locale's structural
  assumptions on \<open>f\<close> --- a well-formed vset, inside the vertex set, and successor-closed --- so it
  may be handed to the next call as its seed.\<close>

lemma dircycle_tracked_finished_inv: "vset_inv (finished dircycle_tracked_result)"
  using dircycle_tracked_invars(2) unfolding invar_fin_def apply assumption done

lemma dircycle_tracked_finished_subset_dVs:
  "t_set (finished dircycle_tracked_result) \<subseteq> dVs (Graph.digraph_abs G)"
  using dircycle_tracked_invars(3) by (auto simp: invar_ssf_def)

lemma dircycle_tracked_finished_closed:
  assumes "u \<in> t_set (finished dircycle_tracked_result)" and "(u, w) \<in> Graph.digraph_abs G"
  shows "w \<in> t_set (finished dircycle_tracked_result)"
  using dircycle_tracked_invars(4) assms by (auto simp: invar_finished_closed_def)

text \<open>\<^bold>\<open>Export 4\<close>: the seed is never lost --- the finished region only grows.\<close>

lemma dircycle_tracked_seed_subset: "t_set f \<subseteq> t_set (finished dircycle_tracked_result)"
  using dircycle_tracked_invars(5) by (simp add: invar_seed_def)

text \<open>\<^bold>\<open>Export 5\<close>: \<^emph>\<open>progress\<close>. On a clean run the stack is empty at the return, so
  \<open>invar_ssf\<close> collapses to \<open>finished = seen\<close>, and \<open>seen\<close> has contained the root since the
  initial state. Without this the outer loop's measure need not decrease.\<close>

lemma dircycle_tracked_root_finished:
  assumes "\<not> cycle dircycle_tracked_result"
  shows "s \<in> t_set (finished dircycle_tracked_result)"
proof -
  have empty: "stack dircycle_tracked_result = []"
    using no_cycle_ret_1[OF dircycle_tracked_initial_dom assms]
    by (auto simp: dc.DFS_skel_more_ret_1_conds_def split: list.splits)
  have "t_set (finished dircycle_tracked_result) = t_set (seen dircycle_tracked_result)"
    using dircycle_tracked_invars(3) empty by (auto simp: invar_ssf_def)
  thus ?thesis using dircycle_tracked_invars(5) by (auto simp: invar_seed_def)
qed

text \<open>\<^bold>\<open>Exports 6--7\<close> (new here): the unfinished set the run hands back. It is a well-formed
  vset and, by \<open>invar_fin_unfin\<close>, it partitions the vertex set with the result's finished
  region --- so it \<^emph>\<open>is\<close> \<open>t_set V - t_set fin'\<close>, re-established with \<^emph>\<open>no\<close> set difference
  computed, and the outer loop may pick its next root from it directly.\<close>

lemma dircycle_tracked_unfinished_inv: "vset_inv (unfinished dircycle_tracked_result)"
  using dircycle_tracked_invars(7) by (auto simp: invar_unfin_def)

lemma dircycle_tracked_unfinished_char:
  shows "t_set (unfinished dircycle_tracked_result) \<union> t_set (finished dircycle_tracked_result)
           = dVs (Graph.digraph_abs G)"
    and "t_set (unfinished dircycle_tracked_result) \<inter> t_set (finished dircycle_tracked_result)
           = {}"
  using dircycle_tracked_invars(9) by (auto simp: invar_fin_unfin_def)

text \<open>Equivalently, as the set difference the outer loop never has to compute:\<close>

lemma dircycle_tracked_unfinished_compl:
  "t_set (unfinished dircycle_tracked_result)
     = dVs (Graph.digraph_abs G) - t_set (finished dircycle_tracked_result)"
  using dircycle_tracked_unfinished_char by auto


end

end

end
