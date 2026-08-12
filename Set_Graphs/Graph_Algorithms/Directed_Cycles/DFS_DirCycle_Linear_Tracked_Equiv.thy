theory DFS_DirCycle_Linear_Tracked_Equiv
  imports DFS_DirCycle_Linear DFS_DirCycle_Linear_Tracked DFS_DirCycle_Linear_Tracked_Aux_Equiv
begin

text \<open>Level 1 of the refinement chain --- the \<^emph>\<open>tracked\<close> directed-cycle search of
  \<open>DFS_dircycle_linear_tracked\<close> --- against level 0, \<open>DFS_dircycle_linear\<close> on the
  skeleton, at the level of the outer sweeps. The inner searches are compared step for step in
  \<^theory>\<open>Directed_Cycle_DFS.DFS_DirCycle_Linear_Tracked_Aux_Equiv\<close>; the two levels agree in
  a weaker sense here, and the section heading below says which.\<close>

section \<open>The outer sweeps: the verdict agrees, the visiting order need not\<close>

text \<open>The inner runs above agree \<^emph>\<open>step for step\<close> because both loops hand \<open>sel\<close> the
  \<^emph>\<open>same\<close> expression, \<open>(\<N>\<^sub>G v) -\<^sub>G seen st\<close>, built from vsets the two runs hold in common. The
  outer sweeps do not: level 0 picks its next root with \<open>sel (V -\<^sub>G fin st)\<close>, level 1 with
  \<open>sel (sweep_unfin st)\<close>. Under the partition invariant those two vsets hold the same
  \<^emph>\<open>elements\<close>, but \<open>sel\<close> is not determined by the element set --- \<^locale>\<open>Set_Choose\<close>
  assumes only \<open>s \<noteq> \<emptyset>\<^sub>N \<Longrightarrow> isin s (sel s)\<close>, and at the red-black-tree instantiation \<open>sel\<close> is the
  tree's root label, which depends on the insertion history. So the two sweeps may well pick
  different roots and visit the search forest in a different order, and a step-for-step equality
  of the two sweep runs is \<^emph>\<open>not\<close> provable (and, for the RBT instance, not true).

  What is nevertheless true is everything order-\<^emph>\<open>independent\<close>, and that is what this section
  proves, from the two sweeps' own soundness and completeness rather than by matching the runs:
  \<^item> the reported flags always agree, because each is equivalent to \<open>G\<close> having a directed cycle;
  \<^item> when no cycle is reported the two final finished regions denote the same set, namely all of
    \<open>dVs G\<close>.

  When a cycle \<^emph>\<open>is\<close> reported the finished regions genuinely need not agree: both sweeps stop at
  the first inner call that reports, and which vertices have been absorbed by then depends on the
  root order. That is the one place the \<open>sel\<close> gap is visible in the results, and it is a
  difference in reported bookkeeping only, not in the verdict.\<close>

locale DFS_dircycle_sweeps_agree =
  lin: DFS_dircycle_linear_thms
        where dfs_aux = dfs_aux\<^sub>L and fin_aux = fin_aux\<^sub>L and cycle_aux = cycle_aux\<^sub>L +
  trk: DFS_dircycle_linear_tracked_thms
        where dfs_aux = dfs_aux\<^sub>T and fin_aux = fin_aux\<^sub>T and unfin_aux = unfin_aux\<^sub>T
          and cycle_aux = cycle_aux\<^sub>T
  for dfs_aux\<^sub>L :: "'v \<Rightarrow> 'vset \<Rightarrow> 'stateL"
    and fin_aux\<^sub>L :: "'stateL \<Rightarrow> 'vset"
    and cycle_aux\<^sub>L :: "'stateL \<Rightarrow> bool"
    and dfs_aux\<^sub>T :: "'v \<Rightarrow> 'vset \<Rightarrow> 'vset \<Rightarrow> 'stateT"
    and fin_aux\<^sub>T :: "'stateT \<Rightarrow> 'vset"
    and unfin_aux\<^sub>T :: "'stateT \<Rightarrow> 'vset"
    and cycle_aux\<^sub>T :: "'stateT \<Rightarrow> bool"
begin

text \<open>Both sweeps run on the \<^emph>\<open>same\<close> graph \<open>G\<close> and vertex set \<open>V\<close> --- those parameters are
  identified by the locale merge --- but take their own (abstract) inner DFS. Because the two
  \<open>Pair_Graph_Specs\<close> interpretations are then literally the same one, it is registered once, and
  \<open>lin.Graph.digraph_abs G\<close> below \<^emph>\<open>is\<close> the graph both sweeps talk about; \<open>trk.Graph.\<dots>\<close> is
  simply not a second name for it.\<close>

abbreviation "lin_run \<equiv> lin.DFS_dircycle_linear lin.initial_state"
abbreviation "trk_run \<equiv> trk.DFS_dircycle_linear_tracked trk.initial_state"

context
includes lin.Graph.adjmap.automation and lin.Graph.vset.set.automation
begin

subsection \<open>Both flags decide the same question\<close>

lemma lin_cyc_iff:
  "cyc lin_run \<longleftrightarrow> (\<exists>c. Awalk_Defs.cycle (lin.Graph.digraph_abs G) c)"
  using lin.DFS_dircycle_linear_sound lin.DFS_dircycle_linear_complete by blast

lemma trk_cyc_iff:
  "sweep_cyc trk_run \<longleftrightarrow> (\<exists>c. Awalk_Defs.cycle (lin.Graph.digraph_abs G) c)"
  using trk.DFS_dircycle_linear_tracked_sound trk.DFS_dircycle_linear_tracked_complete by blast

theorem sweeps_cyc_agree: "cyc lin_run = sweep_cyc trk_run"
  by (simp add: lin_cyc_iff trk_cyc_iff)

subsection \<open>On a clean sweep both finished regions are the whole vertex set\<close>

lemma lin_fin_eq_dVs:
  assumes ncyc: "\<not> cyc lin_run"
  shows "t_set (fin lin_run) = dVs (lin.Graph.digraph_abs G)"
proof -
  note ini = lin.initial_state_props
  have dom: "lin.DFS_dircycle_linear_dom lin.initial_state" by (rule ini(4))
  have i1: "lin.invar_1 lin_run" by (intro lin.invar_1_holds dom ini)
  have isd: "lin.invar_seed lin_run" by (intro lin.invar_seed_holds dom ini)
  have "lin.DFS_dircycle_linear_ret_2_conds lin_run"
    by (intro lin.ret_2_holds dom ini ncyc)
  hence empty: "V -\<^sub>G (fin lin_run) = \<emptyset>\<^sub>N" by (auto elim!: call_cond_elims)
  have inv: "vset_inv (fin lin_run)" using i1 by (auto elim!: invar_props_elims)
  have "t_set V \<subseteq> t_set (fin lin_run)" using empty inv lin.V_inv by force
  hence covers: "dVs (lin.Graph.digraph_abs G) \<subseteq> t_set (fin lin_run)"
    using lin.V_graph_verts by blast
  have "t_set (fin lin_run) \<subseteq> dVs (lin.Graph.digraph_abs G)"
    using isd by (auto simp: lin.invar_seed_def lin.seed_ok_def)
  thus ?thesis using covers by blast
qed

lemma trk_fin_eq_dVs:
  assumes ncyc: "\<not> sweep_cyc trk_run"
  shows "t_set (sweep_fin trk_run) = dVs (lin.Graph.digraph_abs G)"
proof -
  note ini = trk.initial_state_props
  have dom: "trk.DFS_dircycle_linear_tracked_dom trk.initial_state" by (rule ini(5))
  have ip: "trk.invar_part trk_run" by (intro trk.invar_part_holds dom ini)
  have isd: "trk.invar_seed trk_run" by (intro trk.invar_seed_holds dom ini)
  have "trk.DFS_dircycle_linear_tracked_ret_2_conds trk_run"
    by (intro trk.ret_2_holds dom ini ncyc)
  hence empty: "sweep_unfin trk_run = \<emptyset>\<^sub>N" by (auto elim!: call_cond_elims)
  have covers: "dVs (lin.Graph.digraph_abs G) \<subseteq> t_set (sweep_fin trk_run)"
    using ip empty by (force elim!: invar_props_elims)
  have "t_set (sweep_fin trk_run) \<subseteq> dVs (lin.Graph.digraph_abs G)"
    using isd by (auto simp: trk.invar_seed_def trk.seed_ok_def)
  thus ?thesis using covers by blast
qed

theorem sweeps_fin_agree:
  assumes "\<not> cyc lin_run"
  shows "t_set (fin lin_run) = t_set (sweep_fin trk_run)"
  using lin_fin_eq_dVs[OF assms] trk_fin_eq_dVs[OF assms[unfolded sweeps_cyc_agree]]
  by simp

end

end

end
