theory DFS_DirCycle
  imports DFS_Skeletons.DFS_Skeleton Directed_Set_Graphs.Component_Defs
begin

text \<open>Directed-graph cycle detection as an instance of the DFS skeleton. The state extends the
skeleton spine (stack/seen) with a finished set and a cycle flag. A directed cycle is detected
when the current vertex has an out-neighbour that is currently on the stack, i.e. seen but not
yet finished (a back edge). Unlike the undirected case there is no parent exclusion, so self-loops
and 2-cycles are reported. No symmetry / no-self-loop axiom is needed.\<close>

record ('ver, 'vset) DFS_dircycle_state = "('ver, 'vset) DFS_skeleton_state" +
  finished :: "'vset"
  cycle    :: bool

locale DFS_dircycle =
  Graph: Pair_Graph_Specs where lookup = lookup +
 set_ops: Set2 vset_empty vset_delete _ t_set vset_inv insert
for lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option" +
fixes G::"'adjmap" and s::"'v"
begin

abbreviation "neighbourhood' \<equiv> Graph.neighbourhood G"
notation "neighbourhood'" ("\<N>\<^sub>G _" 100)

definition "cyc_found (dfs_state::('v,'vset) DFS_dircycle_state) =
   (case stack dfs_state of [] \<Rightarrow> False
    | (v # stack_tl) \<Rightarrow> (((\<N>\<^sub>G v) \<inter>\<^sub>G (seen dfs_state -\<^sub>G finished dfs_state)) \<noteq> \<emptyset>\<^sub>N))"

definition "cyc_on_found (dfs_state::('v,'vset) DFS_dircycle_state) = (dfs_state \<lparr>cycle := True\<rparr>)"

definition "cyc_on_empty (dfs_state::('v,'vset) DFS_dircycle_state) = dfs_state"

definition "cyc_on_backtrack v (dfs_state::('v,'vset) DFS_dircycle_state) = (dfs_state \<lparr>finished := insert v (finished dfs_state)\<rparr>)"

definition "dircycle_initial_state =
  \<lparr>stack = [s], seen = insert s \<emptyset>\<^sub>N, finished = \<emptyset>\<^sub>N, cycle = False\<rparr>"

definition "DFS_dircycle_axioms =
  (Graph.graph_inv G \<and> Graph.finite_graph G \<and> Graph.finite_vsets G \<and> s \<in> dVs (Graph.digraph_abs G))"

sublocale dc: DFS_skeleton
  where lookup = lookup and G = G and s = s
    and found = cyc_found and on_found = cyc_on_found
    and on_empty = cyc_on_empty and on_backtrack = cyc_on_backtrack
    and on_push = no_push
  by unfold_locales

abbreviation "find_dircycle \<equiv> dc.DFS_skeleton_impl"

end

locale DFS_dircycle_thms = DFS_dircycle +
  assumes dircycle_axioms: DFS_dircycle_axioms
begin

lemma spine_preservation:
  "stack (cyc_on_found st) = stack st" "seen (cyc_on_found st) = seen st"
  "stack (cyc_on_empty st) = stack st" "seen (cyc_on_empty st) = seen st"
  "stack (cyc_on_backtrack v st) = stack st" "seen (cyc_on_backtrack v st) = seen st"
  by (auto simp: cyc_on_found_def cyc_on_empty_def cyc_on_backtrack_def no_push_def)

sublocale dc: DFS_skeleton_thms
  where lookup = lookup and G = G and s = s
    and found = cyc_found and on_found = cyc_on_found
    and on_empty = cyc_on_empty and on_backtrack = cyc_on_backtrack
    and on_push = no_push
  using dircycle_axioms
  by (unfold_locales)
     (auto simp: dc.DFS_skeleton_axioms_def DFS_dircycle_axioms_def
                 cyc_on_found_def cyc_on_empty_def cyc_on_backtrack_def no_push_def)

definition "invar_2 dfs_state = Vwalk.vwalk (Graph.digraph_abs G) (rev (stack dfs_state))"

definition "invar_ssf dfs_state \<longleftrightarrow>
    distinct (stack dfs_state)
    \<and> set (stack dfs_state) \<subseteq> t_set (seen dfs_state)
    \<and> t_set (finished dfs_state) \<subseteq> t_set (seen dfs_state)
    \<and> t_set (finished dfs_state) = t_set (seen dfs_state) - set (stack dfs_state)
    \<and> t_set (seen dfs_state) \<subseteq> dVs (Graph.digraph_abs G)"

definition "invar_fin dfs_state = vset_inv (finished dfs_state)"

definition "invar_cycle_true dfs_state =
    (cycle dfs_state \<longrightarrow> (\<exists>c. Awalk_Defs.cycle (Graph.digraph_abs G) c))"

definition "invar_finished_closed dfs_state =
  (\<forall>u w. u \<in> t_set (finished dfs_state) \<longrightarrow> (u, w) \<in> Graph.digraph_abs G \<longrightarrow> w \<in> t_set (finished dfs_state))"

definition "invar_cycle_false dfs_state =
  (\<not> cycle dfs_state \<longrightarrow> (\<nexists>c. Awalk_Defs.cycle (Graph.digraph_abs G \<downharpoonright> t_set (finished dfs_state)) c))"

context
includes set_ops.automation2 and Graph.adjmap.automation and Graph.vset.set.automation
begin

lemma initial_invars[simp,intro]:
  "dc.invar_1 dircycle_initial_state"
  "dc.invar_seen_stack dircycle_initial_state"
  using dircycle_axioms
  by (auto simp: dc.invar_1_def dc.invar_seen_stack_def dircycle_initial_state_def
                 DFS_dircycle_axioms_def)

lemma dircycle_initial_dom: "dc.DFS_skeleton_dom dircycle_initial_state"
  by (intro dc.DFS_skeleton_terminates initial_invars)

text \<open>upd2 explicitly: pop the head and mark it finished.\<close>
lemma upd2_unfold:
  "stack (dc.DFS_skeleton_upd2 st) = tl (stack st)"
  "seen (dc.DFS_skeleton_upd2 st) = seen st"
  "finished (dc.DFS_skeleton_upd2 st) = insert (hd (stack st)) (finished st)"
  "cycle (dc.DFS_skeleton_upd2 st) = cycle st"
  by (auto simp: dc.DFS_skeleton_upd2_def cyc_on_backtrack_def)

lemma upd1_unfold:
  "stack (dc.DFS_skeleton_upd1 st) = sel ((\<N>\<^sub>G (hd (stack st))) -\<^sub>G seen st) # stack st"
  "seen (dc.DFS_skeleton_upd1 st) = insert (sel ((\<N>\<^sub>G (hd (stack st))) -\<^sub>G seen st)) (seen st)"
  "finished (dc.DFS_skeleton_upd1 st) = finished st"
  "cycle (dc.DFS_skeleton_upd1 st) = cycle st"
  by (auto simp: dc.DFS_skeleton_upd1_def no_push_def Let_def)

lemma invar_fin_props[invar_props_elims]:
  "invar_fin dfs_state \<Longrightarrow> (vset_inv (finished dfs_state) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_fin_def)

lemma invar_fin_intro[invar_props_intros]:
  "vset_inv (finished dfs_state) \<Longrightarrow> invar_fin dfs_state"
  by (auto simp: invar_fin_def)

lemma invar_fin_holds_upd1[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skeleton_call_1_conds dfs_state; invar_fin dfs_state\<rbrakk> \<Longrightarrow> invar_fin (dc.DFS_skeleton_upd1 dfs_state)"
  by (auto simp: upd1_unfold elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_fin_holds_upd2[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skeleton_call_2_conds dfs_state; invar_fin dfs_state\<rbrakk> \<Longrightarrow> invar_fin (dc.DFS_skeleton_upd2 dfs_state)"
  by (auto simp: upd2_unfold elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_fin_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skeleton_ret_1_conds dfs_state; invar_fin dfs_state\<rbrakk> \<Longrightarrow> invar_fin (dc.DFS_skeleton_ret1 dfs_state)"
  by (auto simp: dc.DFS_skeleton_ret1_def cyc_on_empty_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_fin_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skeleton_ret_2_conds dfs_state; invar_fin dfs_state\<rbrakk> \<Longrightarrow> invar_fin (dc.DFS_skeleton_ret2 dfs_state)"
  by (auto simp: dc.DFS_skeleton_ret2_def cyc_on_found_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_fin_holds[invar_holds_intros]:
  assumes "dc.DFS_skeleton_dom dfs_state" "invar_fin dfs_state"
  shows "invar_fin (dc.DFS_skeleton dfs_state)"
  using assms(2-)
proof(induction rule: dc.DFS_skeleton_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule dc.DFS_skeleton_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-) invar_holds_intros simp: dc.DFS_skeleton_simps[OF IH(1)])
qed

lemma invar_2_props[invar_props_elims]:
  "invar_2 dfs_state \<Longrightarrow> (Vwalk.vwalk (Graph.digraph_abs G) (rev (stack dfs_state)) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_2_def)

lemma invar_2_intro[invar_props_intros]:
  "Vwalk.vwalk (Graph.digraph_abs G) (rev (stack dfs_state)) \<Longrightarrow> invar_2 dfs_state"
  by (auto simp: invar_2_def)

lemma invar_2_holds_upd1[invar_holds_intros]:
  assumes "dc.DFS_skeleton_call_1_conds dfs_state" "dc.invar_1 dfs_state" "invar_2 dfs_state"
  shows "invar_2 (dc.DFS_skeleton_upd1 dfs_state)"
  using assms dc.graph_inv
  by (force simp: Let_def dc.DFS_skeleton_upd1_def elim!: call_cond_elims
            elim!: invar_props_elims intro!: Vwalk.vwalk_append2 invar_props_intros)

lemma invar_2_holds_upd2[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skeleton_call_2_conds dfs_state; invar_2 dfs_state\<rbrakk> \<Longrightarrow> invar_2 (dc.DFS_skeleton_upd2 dfs_state)"
  by (auto simp: upd2_unfold dest!: append_vwalk_pref elim!: invar_props_elims
           intro!: invar_props_intros elim: call_cond_elims)

lemma invar_2_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skeleton_ret_1_conds dfs_state; invar_2 dfs_state\<rbrakk> \<Longrightarrow> invar_2 (dc.DFS_skeleton_ret1 dfs_state)"
  by (auto simp: dc.DFS_skeleton_ret1_def cyc_on_empty_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_2_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skeleton_ret_2_conds dfs_state; invar_2 dfs_state\<rbrakk> \<Longrightarrow> invar_2 (dc.DFS_skeleton_ret2 dfs_state)"
  by (auto simp: dc.DFS_skeleton_ret2_def cyc_on_found_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_2_holds[invar_holds_intros]:
  assumes "dc.DFS_skeleton_dom dfs_state" "dc.invar_1 dfs_state" "invar_2 dfs_state"
  shows "invar_2 (dc.DFS_skeleton dfs_state)"
  using assms(2-)
proof(induction rule: dc.DFS_skeleton_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule dc.DFS_skeleton_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-) invar_holds_intros simp: dc.DFS_skeleton_simps[OF IH(1)])
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
  "\<lbrakk>dc.DFS_skeleton_call_1_conds dfs_state; dc.invar_1 dfs_state; invar_ssf dfs_state\<rbrakk> \<Longrightarrow>
    invar_ssf (dc.DFS_skeleton_upd1 dfs_state)"
proof (intro invar_props_intros, goal_cases)
  case 1
  let ?v = "hd (stack dfs_state)"
  let ?w = "sel ((\<N>\<^sub>G ?v) -\<^sub>G (seen dfs_state))"
  have w: "?w \<in> t_set (\<N>\<^sub>G ?v) - t_set (seen dfs_state)"
    using \<open>dc.DFS_skeleton_call_1_conds dfs_state\<close> \<open>dc.invar_1 dfs_state\<close>
    by (auto elim!: invar_props_elims call_cond_elims)
  from 1 w show ?case by (auto simp: upd1_unfold elim!: invar_props_elims)
next
  case 2
  let ?v = "hd (stack dfs_state)"
  let ?w = "sel ((\<N>\<^sub>G ?v) -\<^sub>G (seen dfs_state))"
  have w: "?w \<in> t_set (\<N>\<^sub>G ?v) - t_set (seen dfs_state)"
    using \<open>dc.DFS_skeleton_call_1_conds dfs_state\<close> \<open>dc.invar_1 dfs_state\<close>
    by (auto elim!: invar_props_elims call_cond_elims)
  from 2 w show ?case by (auto simp: upd1_unfold elim!: invar_props_elims)
next
  case 3
  then show ?case by (auto simp: upd1_unfold elim!: invar_props_elims)
next
  case 4
  let ?v = "hd (stack dfs_state)"
  let ?w = "sel ((\<N>\<^sub>G ?v) -\<^sub>G (seen dfs_state))"
  have w: "?w \<in> t_set (\<N>\<^sub>G ?v) - t_set (seen dfs_state)"
    using \<open>dc.DFS_skeleton_call_1_conds dfs_state\<close> \<open>dc.invar_1 dfs_state\<close>
    by (auto elim!: invar_props_elims call_cond_elims)
  from 4 w show ?case by (auto simp: upd1_unfold elim!: invar_props_elims)
next
  case 5
  let ?v = "hd (stack dfs_state)"
  let ?w = "sel ((\<N>\<^sub>G ?v) -\<^sub>G (seen dfs_state))"
  have w: "?w \<in> t_set (\<N>\<^sub>G ?v) - t_set (seen dfs_state)"
    using \<open>dc.DFS_skeleton_call_1_conds dfs_state\<close> \<open>dc.invar_1 dfs_state\<close>
    by (auto elim!: invar_props_elims call_cond_elims)
  from 5 w show ?case by (auto simp: upd1_unfold elim!: invar_props_elims)
qed

lemma invar_ssf_holds_upd2[invar_holds_intros]:
  assumes "dc.DFS_skeleton_call_2_conds dfs_state" "dc.invar_1 dfs_state" "invar_fin dfs_state"
          "invar_ssf dfs_state"
  shows "invar_ssf (dc.DFS_skeleton_upd2 dfs_state)"
proof -
  obtain v stack_tl where stk: "stack dfs_state = v # stack_tl"
    using assms(1) by (auto elim!: call_cond_elims)
  have finv: "vset_inv (finished dfs_state)" using assms(3) by (auto simp: invar_fin_def)
  have props: "distinct (stack dfs_state)" "set (stack dfs_state) \<subseteq> t_set (seen dfs_state)"
       "t_set (finished dfs_state) \<subseteq> t_set (seen dfs_state)"
       "t_set (finished dfs_state) = t_set (seen dfs_state) - set (stack dfs_state)"
       "t_set (seen dfs_state) \<subseteq> dVs (Graph.digraph_abs G)"
    using assms(4) by (auto simp: invar_ssf_def)
  have fin2: "t_set (finished (dc.DFS_skeleton_upd2 dfs_state)) = Set.insert v (t_set (finished dfs_state))"
    using finv stk by (auto simp: upd2_unfold)
  have st2: "stack (dc.DFS_skeleton_upd2 dfs_state) = stack_tl"
    by (simp add: upd2_unfold stk)
  have se2: "seen (dc.DFS_skeleton_upd2 dfs_state) = seen dfs_state"
    by (simp add: upd2_unfold)
  show ?thesis
    unfolding invar_ssf_def st2 se2 fin2
    using props stk by auto
qed

lemma invar_ssf_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skeleton_ret_1_conds dfs_state; invar_ssf dfs_state\<rbrakk> \<Longrightarrow> invar_ssf (dc.DFS_skeleton_ret1 dfs_state)"
  by (force simp: dc.DFS_skeleton_ret1_def cyc_on_empty_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_ssf_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skeleton_ret_2_conds dfs_state; invar_ssf dfs_state\<rbrakk> \<Longrightarrow> invar_ssf (dc.DFS_skeleton_ret2 dfs_state)"
  by (force simp: dc.DFS_skeleton_ret2_def cyc_on_found_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_ssf_holds[invar_holds_intros]:
  assumes "dc.DFS_skeleton_dom dfs_state" "dc.invar_1 dfs_state" "invar_fin dfs_state" "invar_ssf dfs_state"
  shows "invar_ssf (dc.DFS_skeleton dfs_state)"
  using assms(2-)
proof(induction rule: dc.DFS_skeleton_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule dc.DFS_skeleton_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-) invar_holds_intros simp: dc.DFS_skeleton_simps[OF IH(1)])
qed

lemma initial_struct[simp,intro]:
  "invar_2 dircycle_initial_state"
  "invar_ssf dircycle_initial_state"
  using dircycle_axioms
  by (auto simp: invar_2_def invar_ssf_def dircycle_initial_state_def DFS_dircycle_axioms_def)

subsection \<open>Soundness: a reported cycle is a real directed cycle\<close>

lemma invar_cycle_true_props[invar_props_elims]:
  "invar_cycle_true dfs_state \<Longrightarrow>
     ((cycle dfs_state \<Longrightarrow> \<exists>c. Awalk_Defs.cycle (Graph.digraph_abs G) c) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_cycle_true_def)

lemma invar_cycle_true_intro[invar_props_intros]:
  "(cycle dfs_state \<Longrightarrow> \<exists>c. Awalk_Defs.cycle (Graph.digraph_abs G) c) \<Longrightarrow> invar_cycle_true dfs_state"
  by (auto simp: invar_cycle_true_def)

lemma invar_cycle_true_holds_upd1[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skeleton_call_1_conds dfs_state; invar_cycle_true dfs_state\<rbrakk> \<Longrightarrow> invar_cycle_true (dc.DFS_skeleton_upd1 dfs_state)"
  by (auto simp: upd1_unfold elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_cycle_true_holds_upd2[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skeleton_call_2_conds dfs_state; invar_cycle_true dfs_state\<rbrakk> \<Longrightarrow> invar_cycle_true (dc.DFS_skeleton_upd2 dfs_state)"
  by (auto simp: upd2_unfold elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_cycle_true_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skeleton_ret_1_conds dfs_state; invar_cycle_true dfs_state\<rbrakk> \<Longrightarrow> invar_cycle_true (dc.DFS_skeleton_ret1 dfs_state)"
  by (auto simp: dc.DFS_skeleton_ret1_def cyc_on_empty_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_cycle_true_holds_ret_2[invar_holds_intros]:
  assumes "dc.DFS_skeleton_ret_2_conds dfs_state" "dc.invar_1 dfs_state" "invar_fin dfs_state"
          "invar_2 dfs_state" "invar_ssf dfs_state" "invar_cycle_true dfs_state"
  shows "invar_cycle_true (dc.DFS_skeleton_ret2 dfs_state)"
proof (intro invar_props_intros)
  let ?v = "hd (stack dfs_state)"
  have ne: "(\<N>\<^sub>G ?v) \<inter>\<^sub>G (seen dfs_state -\<^sub>G finished dfs_state) \<noteq> \<emptyset>\<^sub>N"
       and stk: "stack dfs_state \<noteq> []"
    using assms(1) by (auto simp: dc.DFS_skeleton_ret_2_conds_def cyc_found_def split: list.splits)
  obtain x where x_mem: "x \<in> t_set ((\<N>\<^sub>G ?v) \<inter>\<^sub>G (seen dfs_state -\<^sub>G finished dfs_state))"
    using ne assms(2,3) by (force elim!: invar_props_elims dest!: Graph.vset.choose')
  then have xN: "x \<in> t_set (\<N>\<^sub>G ?v)" and xsf: "x \<in> t_set (seen dfs_state -\<^sub>G finished dfs_state)"
    using assms(2,3) by (auto elim!: invar_props_elims)
  have xstack: "x \<in> set (stack dfs_state)"
    using xsf assms(2,3,5) by (force elim!: invar_props_elims)
  have edge: "(?v, x) \<in> Graph.digraph_abs G"
    using xN by auto
  have vverts: "?v \<in> dVs (Graph.digraph_abs G)" and xverts: "x \<in> dVs (Graph.digraph_abs G)"
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
    moreover have "last (rev (stack dfs_state)) = last p" using rs pne by (simp add: last_appendR)
    ultimately show ?thesis by simp
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
    then show ?thesis by (simp add: edeq)
  qed
  have distinct_rev: "distinct (rev (stack dfs_state))"
    using assms(5) by (force elim!: invar_props_elims)
  with rs have dp: "distinct p" by force
  have dtl: "distinct (tl (p @ [x]))"
  proof -
    obtain p' where pcons: "p = x # p'" using pne hdp by (cases p) auto
    have "distinct (x # p')" using dp pcons by simp
    then have "distinct p'" "x \<notin> set p'" by auto
    then have "distinct (p' @ [x])" by simp
    then show ?thesis using pcons by simp
  qed
  have "Awalk_Defs.cycle (Graph.digraph_abs G) ((edges_of_vwalk p) @ [(?v, x)])"
    unfolding Awalk_Defs.cycle_def using closed dtl verts by auto
  then show "cycle (dc.DFS_skeleton_ret2 dfs_state) \<Longrightarrow> \<exists>c. Awalk_Defs.cycle (Graph.digraph_abs G) c" by blast
qed

lemma invar_cycle_true_holds[invar_holds_intros]:
  assumes "dc.DFS_skeleton_dom dfs_state" "dc.invar_1 dfs_state" "invar_fin dfs_state"
          "invar_2 dfs_state" "invar_ssf dfs_state" "invar_cycle_true dfs_state"
  shows "invar_cycle_true (dc.DFS_skeleton dfs_state)"
  using assms(2-)
proof(induction rule: dc.DFS_skeleton_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule dc.DFS_skeleton_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-) invar_holds_intros simp: dc.DFS_skeleton_simps[OF IH(1)])
qed

lemma initial_fin[simp,intro]: "invar_fin dircycle_initial_state"
  by (auto simp: invar_fin_def dircycle_initial_state_def)

theorem DFS_dircycle_sound:
  assumes "cycle (dc.DFS_skeleton dircycle_initial_state)"
  shows "\<exists>c. Awalk_Defs.cycle (Graph.digraph_abs G) c"
proof -
  have "invar_cycle_true (dc.DFS_skeleton dircycle_initial_state)"
    by (intro invar_cycle_true_holds dircycle_initial_dom initial_invars initial_fin initial_struct)
       (auto simp: invar_cycle_true_def dircycle_initial_state_def)
  thus ?thesis using assms by (auto elim!: invar_props_elims)
qed

subsection \<open>Completeness: no report means the explored subgraph is acyclic\<close>

lemma invar_finished_closed_props[invar_props_elims]:
  "invar_finished_closed dfs_state \<Longrightarrow>
    ((\<And>u w. u \<in> t_set (finished dfs_state) \<Longrightarrow> (u, w) \<in> Graph.digraph_abs G \<Longrightarrow> w \<in> t_set (finished dfs_state)) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_finished_closed_def)

lemma invar_finished_closed_intro[invar_props_intros]:
  "(\<And>u w. u \<in> t_set (finished dfs_state) \<Longrightarrow> (u, w) \<in> Graph.digraph_abs G \<Longrightarrow> w \<in> t_set (finished dfs_state))
    \<Longrightarrow> invar_finished_closed dfs_state"
  by (auto simp: invar_finished_closed_def)

text \<open>Out-neighbours of the popped vertex are all already finished (no unseen, no gray neighbour).\<close>
lemma upd2_vout:
  assumes "dc.DFS_skeleton_call_2_conds dfs_state" "dc.invar_1 dfs_state" "invar_fin dfs_state"
    and "(hd (stack dfs_state), w) \<in> Graph.digraph_abs G"
  shows "w \<in> t_set (finished dfs_state)"
proof -
  let ?v = "hd (stack dfs_state)"
  have sinv: "vset_inv (seen dfs_state)" using assms(2) by (auto simp: dc.invar_1_def)
  have finv: "vset_inv (finished dfs_state)" using assms(3) by (auto simp: invar_fin_def)
  have ninv: "vset_inv (\<N>\<^sub>G ?v)" using dc.graph_inv by auto
  have wN: "w \<in> t_set (\<N>\<^sub>G ?v)"
    using assms(4) dc.graph_inv by (auto intro!: Graph.are_connected_absI)
  have d_empty: "(\<N>\<^sub>G ?v) -\<^sub>G (seen dfs_state) = \<emptyset>\<^sub>N"
    using assms(1) by (auto elim!: call_cond_elims)
  have i_empty: "(\<N>\<^sub>G ?v) \<inter>\<^sub>G (seen dfs_state -\<^sub>G finished dfs_state) = \<emptyset>\<^sub>N"
  proof -
    obtain v stack_tl where stk: "stack dfs_state = v # stack_tl"
      using assms(1) by (auto elim!: call_cond_elims)
    have "\<not> cyc_found dfs_state" using assms(1) by (auto elim!: call_cond_elims)
    thus ?thesis using stk by (simp add: cyc_found_def)
  qed
  have nsub: "t_set (\<N>\<^sub>G ?v) \<subseteq> t_set (seen dfs_state)"
  proof -
    have "t_set (\<N>\<^sub>G ?v) - t_set (seen dfs_state) = t_set ((\<N>\<^sub>G ?v) -\<^sub>G (seen dfs_state))"
      by (simp add: set_ops.set_diff[OF ninv sinv])
    also have "... = {}" by (simp add: d_empty)
    finally show ?thesis by blast
  qed
  have dinv: "vset_inv (seen dfs_state -\<^sub>G finished dfs_state)"
    by (simp add: set_ops.invar_diff[OF sinv finv])
  have nint: "t_set (\<N>\<^sub>G ?v) \<inter> (t_set (seen dfs_state) - t_set (finished dfs_state)) = {}"
  proof -
    have "t_set (\<N>\<^sub>G ?v) \<inter> (t_set (seen dfs_state) - t_set (finished dfs_state))
          = t_set ((\<N>\<^sub>G ?v) \<inter>\<^sub>G (seen dfs_state -\<^sub>G finished dfs_state))"
      by (simp add: set_ops.set_inter[OF ninv dinv] set_ops.set_diff[OF sinv finv])
    also have "... = {}" by (simp add: i_empty)
    finally show ?thesis .
  qed
  from wN nsub nint show ?thesis by blast
qed

lemma invar_finished_closed_holds_upd1[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skeleton_call_1_conds dfs_state; invar_finished_closed dfs_state\<rbrakk> \<Longrightarrow>
    invar_finished_closed (dc.DFS_skeleton_upd1 dfs_state)"
  by (auto simp: invar_finished_closed_def upd1_unfold)

lemma invar_finished_closed_holds_upd2[invar_holds_intros]:
  assumes "dc.DFS_skeleton_call_2_conds dfs_state" "dc.invar_1 dfs_state" "invar_fin dfs_state"
          "invar_finished_closed dfs_state"
  shows "invar_finished_closed (dc.DFS_skeleton_upd2 dfs_state)"
proof (intro invar_props_intros)
  fix u w
  assume uin: "u \<in> t_set (finished (dc.DFS_skeleton_upd2 dfs_state))" and edge: "(u, w) \<in> Graph.digraph_abs G"
  have fin2: "t_set (finished (dc.DFS_skeleton_upd2 dfs_state)) = Set.insert (hd (stack dfs_state)) (t_set (finished dfs_state))"
    using assms(3) by (auto simp: upd2_unfold elim!: invar_props_elims)
  from uin fin2 consider "u = hd (stack dfs_state)" | "u \<in> t_set (finished dfs_state)" by auto
  then have "w \<in> t_set (finished dfs_state)"
  proof cases
    case 1 thus ?thesis using upd2_vout[OF assms(1,2,3)] edge by auto
  next
    case 2 thus ?thesis using assms(4) edge by (auto elim!: invar_props_elims)
  qed
  thus "w \<in> t_set (finished (dc.DFS_skeleton_upd2 dfs_state))" using fin2 by simp
qed

lemma invar_finished_closed_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skeleton_ret_1_conds dfs_state; invar_finished_closed dfs_state\<rbrakk> \<Longrightarrow>
    invar_finished_closed (dc.DFS_skeleton_ret1 dfs_state)"
  by (auto simp: invar_finished_closed_def dc.DFS_skeleton_ret1_def cyc_on_empty_def)

lemma invar_finished_closed_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skeleton_ret_2_conds dfs_state; invar_finished_closed dfs_state\<rbrakk> \<Longrightarrow>
    invar_finished_closed (dc.DFS_skeleton_ret2 dfs_state)"
  by (auto simp: invar_finished_closed_def dc.DFS_skeleton_ret2_def cyc_on_found_def)

lemma invar_finished_closed_holds[invar_holds_intros]:
  assumes "dc.DFS_skeleton_dom dfs_state" "dc.invar_1 dfs_state" "invar_fin dfs_state" "invar_finished_closed dfs_state"
  shows "invar_finished_closed (dc.DFS_skeleton dfs_state)"
  using assms(2-)
proof(induction rule: dc.DFS_skeleton_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule dc.DFS_skeleton_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-) invar_holds_intros simp: dc.DFS_skeleton_simps[OF IH(1)])
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
  moreover have "last (map snd c) = u" using sndlast assms(2) by (simp add: last_map)
  ultimately have "u \<in> set (map snd c)" using last_in_set by blast
  with av assms(3) show ?thesis by auto
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
  "\<lbrakk>dc.DFS_skeleton_call_1_conds dfs_state; invar_cycle_false dfs_state\<rbrakk> \<Longrightarrow> invar_cycle_false (dc.DFS_skeleton_upd1 dfs_state)"
  by (auto simp: upd1_unfold elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_cycle_false_holds_upd2[invar_holds_intros]:
  assumes "dc.DFS_skeleton_call_2_conds dfs_state" "dc.invar_1 dfs_state" "invar_fin dfs_state"
          "invar_ssf dfs_state" "invar_finished_closed dfs_state" "invar_cycle_false dfs_state"
  shows "invar_cycle_false (dc.DFS_skeleton_upd2 dfs_state)"
proof (intro invar_props_intros)
  assume notcyc': "\<not> cycle (dc.DFS_skeleton_upd2 dfs_state)"
  let ?v = "hd (stack dfs_state)"
  let ?F = "t_set (finished dfs_state)"
  let ?DG = "Graph.digraph_abs G"
  have notcyc: "\<not> cycle dfs_state" using notcyc' by (simp add: upd2_unfold)
  have finup: "t_set (finished (dc.DFS_skeleton_upd2 dfs_state)) = Set.insert ?v ?F"
    using assms(3) by (auto simp: upd2_unfold invar_fin_def)
  have acycF: "\<nexists>c. Awalk_Defs.cycle (?DG \<downharpoonright> ?F) c" using assms(6) notcyc by (auto simp: invar_cycle_false_def)
  have vstack: "?v \<in> set (stack dfs_state)" using assms(1) by (auto elim!: call_cond_elims)
  have vnotF: "?v \<notin> ?F" using vstack assms(4) by (auto simp: invar_ssf_def)
  have closedF: "\<And>u w. u \<in> ?F \<Longrightarrow> (u, w) \<in> ?DG \<Longrightarrow> w \<in> ?F"
    using assms(5) unfolding invar_finished_closed_def by blast
  have no_in: "(u, ?v) \<notin> (?DG \<downharpoonright> Set.insert ?v ?F)" for u
  proof
    assume e: "(u, ?v) \<in> (?DG \<downharpoonright> Set.insert ?v ?F)"
    from e have uin: "u \<in> Set.insert ?v ?F" and edge: "(u, ?v) \<in> ?DG"
      by (auto simp: induce_subgraph_def)
    show False
    proof (cases "u = ?v")
      case True
      then have "?v \<in> t_set (finished dfs_state)"
        using upd2_vout[OF assms(1,2,3)] edge by blast
      then show False using vnotF by blast
    next
      case False
      then have "u \<in> ?F" using uin by blast
      then show False using closedF edge vnotF by blast
    qed
  qed
  show "\<nexists>c. Awalk_Defs.cycle (?DG \<downharpoonright> t_set (finished (dc.DFS_skeleton_upd2 dfs_state))) c"
    unfolding finup
  proof (rule notI, erule exE)
    fix c assume cyc: "Awalk_Defs.cycle (?DG \<downharpoonright> Set.insert ?v ?F) c"
    then obtain u where aw: "awalk (?DG \<downharpoonright> Set.insert ?v ?F) u c u" and cne: "c \<noteq> []"
      and dtl: "distinct (tl (awalk_verts u c))" by (auto simp: Awalk_Defs.cycle_def)
    have edges_sub: "set c \<subseteq> (?DG \<downharpoonright> Set.insert ?v ?F)" using aw by (auto simp: awalk_def)
    have ucas: "cas u c u" using aw by (simp add: awalk_def)
    have vnotverts: "?v \<notin> set (awalk_verts u c)"
    proof
      assume "?v \<in> set (awalk_verts u c)"
      from closed_walk_has_in_edge[OF aw cne this] obtain e
        where emem: "e \<in> set c" and esnd: "snd e = ?v" by blast
      have "e \<in> (?DG \<downharpoonright> Set.insert ?v ?F)" using emem edges_sub by blast
      then have "(fst e, snd e) \<in> (?DG \<downharpoonright> Set.insert ?v ?F)" by simp
      then have "(fst e, ?v) \<in> (?DG \<downharpoonright> Set.insert ?v ?F)" using esnd by simp
      then show False using no_in by blast
    qed
    have verts_eq: "set (awalk_verts u c) = set (map fst c) \<union> set (map snd c)"
      using set_awalk_verts_not_Nil_cas[OF ucas cne] by simp
    have subF: "set c \<subseteq> (?DG \<downharpoonright> ?F)"
    proof
      fix e assume ec: "e \<in> set c"
      then have ein: "e \<in> (?DG \<downharpoonright> Set.insert ?v ?F)" using edges_sub by auto
      have fv: "fst e \<in> set (awalk_verts u c)" using ec by (auto simp: verts_eq)
      have sv: "snd e \<in> set (awalk_verts u c)" using ec by (auto simp: verts_eq)
      from fv sv vnotverts ein show "e \<in> (?DG \<downharpoonright> ?F)" by (cases e) (auto simp: induce_subgraph_def)
    qed
    have "fst (hd c) = u" using ucas cne by (cases c) auto
    then obtain w cs where c_eq: "c = (u, w) # cs" using cne by (cases c) auto
    have uinF: "u \<in> dVs (?DG \<downharpoonright> ?F)"
      using subF c_eq by (auto simp: dVs_def)
    have "awalk (?DG \<downharpoonright> ?F) u c u" using subF uinF ucas by (simp add: awalk_def)
    then have "Awalk_Defs.cycle (?DG \<downharpoonright> ?F) c" using cne dtl by (auto simp: Awalk_Defs.cycle_def)
    then show False using acycF by blast
  qed
qed

lemma invar_cycle_false_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skeleton_ret_1_conds dfs_state; invar_cycle_false dfs_state\<rbrakk> \<Longrightarrow> invar_cycle_false (dc.DFS_skeleton_ret1 dfs_state)"
  by (auto simp: dc.DFS_skeleton_ret1_def cyc_on_empty_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_cycle_false_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skeleton_ret_2_conds dfs_state; invar_cycle_false dfs_state\<rbrakk> \<Longrightarrow> invar_cycle_false (dc.DFS_skeleton_ret2 dfs_state)"
  by (auto simp: dc.DFS_skeleton_ret2_def cyc_on_found_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_cycle_false_holds[invar_holds_intros]:
  assumes "dc.DFS_skeleton_dom dfs_state" "dc.invar_1 dfs_state" "invar_fin dfs_state" "invar_ssf dfs_state"
          "invar_finished_closed dfs_state" "invar_cycle_false dfs_state"
  shows "invar_cycle_false (dc.DFS_skeleton dfs_state)"
  using assms(2-)
proof(induction rule: dc.DFS_skeleton_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule dc.DFS_skeleton_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-) invar_holds_intros simp: dc.DFS_skeleton_simps[OF IH(1)])
qed

lemma initial_fc[simp,intro]:
  "invar_finished_closed dircycle_initial_state" "invar_cycle_false dircycle_initial_state"
  by (auto simp: invar_finished_closed_def invar_cycle_false_def dircycle_initial_state_def
                 Awalk_Defs.cycle_def awalk_def induce_subgraph_def dVs_def)

text \<open>When the run reports no cycle it ended at the empty-stack return.\<close>
lemma no_cycle_ret_1:
  assumes "dc.DFS_skeleton_dom dfs_state" "\<not> cycle (dc.DFS_skeleton dfs_state)"
  shows "dc.DFS_skeleton_ret_1_conds (dc.DFS_skeleton dfs_state)"
  using assms(2)
proof(induction rule: dc.DFS_skeleton_induct[OF assms(1)])
  case IH: (1 dfs_state)
  note simps = dc.DFS_skeleton_simps[OF IH(1)]
  show ?case
  proof (rule dc.DFS_skeleton_cases[where dfs_state = dfs_state])
    assume c: "dc.DFS_skeleton_call_1_conds dfs_state"
    have ncyc: "\<not> cycle (dc.DFS_skeleton (dc.DFS_skeleton_upd1 dfs_state))"
      using IH(4) c by (simp add: simps(1))
    have "dc.DFS_skeleton_ret_1_conds (dc.DFS_skeleton (dc.DFS_skeleton_upd1 dfs_state))"
      using IH(2)[OF c] ncyc by blast
    then show "dc.DFS_skeleton_ret_1_conds (dc.DFS_skeleton dfs_state)"
      using c by (simp add: simps(1))
  next
    assume c: "dc.DFS_skeleton_call_2_conds dfs_state"
    have ncyc: "\<not> cycle (dc.DFS_skeleton (dc.DFS_skeleton_upd2 dfs_state))"
      using IH(4) c by (simp add: simps(2))
    have "dc.DFS_skeleton_ret_1_conds (dc.DFS_skeleton (dc.DFS_skeleton_upd2 dfs_state))"
      using IH(3)[OF c] ncyc by blast
    then show "dc.DFS_skeleton_ret_1_conds (dc.DFS_skeleton dfs_state)"
      using c by (simp add: simps(2))
  next
    assume c: "dc.DFS_skeleton_ret_1_conds dfs_state"
    then show "dc.DFS_skeleton_ret_1_conds (dc.DFS_skeleton dfs_state)"
      by (simp add: simps(3) dc.DFS_skeleton_ret1_def cyc_on_empty_def)
  next
    assume c: "dc.DFS_skeleton_ret_2_conds dfs_state"
    have "cycle (dc.DFS_skeleton dfs_state)"
      using c by (simp add: simps(4) dc.DFS_skeleton_ret2_def cyc_on_found_def)
    then show "dc.DFS_skeleton_ret_1_conds (dc.DFS_skeleton dfs_state)"
      using IH(4) by blast
  qed
qed

theorem DFS_dircycle_complete:
  assumes "\<not> cycle (dc.DFS_skeleton dircycle_initial_state)"
  shows "\<nexists>c. Awalk_Defs.cycle (Graph.digraph_abs G \<downharpoonright> t_set (seen (dc.DFS_skeleton dircycle_initial_state))) c"
proof -
  let ?r = "dc.DFS_skeleton dircycle_initial_state"
  have dom: "dc.DFS_skeleton_dom dircycle_initial_state" by (rule dircycle_initial_dom)
  have cf: "invar_cycle_false ?r"
    by (intro invar_cycle_false_holds dom initial_invars initial_fin initial_struct initial_fc)
  have ssf: "invar_ssf ?r"
    by (intro invar_ssf_holds dom initial_invars initial_fin initial_struct)
  have empty: "stack ?r = []"
    using no_cycle_ret_1[OF dom assms] by (auto simp: dc.DFS_skeleton_ret_1_conds_def split: list.splits)
  have "t_set (finished ?r) = t_set (seen ?r)"
    using ssf empty by (auto elim!: invar_props_elims)
  moreover have "\<nexists>c. Awalk_Defs.cycle (Graph.digraph_abs G \<downharpoonright> t_set (finished ?r)) c"
    using cf assms by (auto elim!: invar_props_elims)
  ultimately show ?thesis by simp
qed

end

end

end

