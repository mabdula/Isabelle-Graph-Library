theory DFS_DirCycle_Linear_Tracked_Equiv
  imports DFS_DirCycle_Linear DFS_DirCycle_Linear_Tracked
begin

text \<open>Level 1 of the refinement chain --- the \<^emph>\<open>tracked\<close> directed-cycle search of
  \<^theory>\<open>Directed_Cycle_DFS.DFS_DirCycle_Linear_Tracked_Aux\<close> / \<open>DFS_dircycle_linear_tracked\<close> --- against level 0,
  the reference implementation of \<^theory>\<open>Directed_Cycle_DFS.DFS_DirCycle_Linear_Aux\<close> /
  \<open>DFS_dircycle_linear\<close> on the library's skeleton. Inner DFS first, then the outer sweeps; the
  two levels agree in quite different senses, and the section headings say which.\<close>

section \<open>The inner (pre-seeded) DFS: step-for-step equality\<close>

text \<open>The tracked locale's assumptions subsume the reference locale's, so a tracked setup
  \<^emph>\<open>is\<close> a reference setup at the same graph, root and seed: no separate combined locale is
  needed, only a \<^theory_text>\<open>sublocale\<close> making the reference run available as \<open>lin.\<close>.\<close>

sublocale DFS_dircycle_linear_tracked_aux \<subseteq> lin: DFS_dircycle_linear_aux
  by unfold_locales

sublocale DFS_dircycle_linear_tracked_aux_thms \<subseteq>
  lin: DFS_dircycle_linear_aux_thms
  using dircycle_tracked_axioms
  by unfold_locales
     (auto simp: lin.DFS_dircycle_linear_aux_axioms_def lin.DFS_dircycle_axioms_def
                 DFS_dircycle_linear_tracked_aux_axioms_def)

text \<open>The two inner runs live in different state types --- the tracked one carries \<open>gray\<close> and
  \<open>unfinished\<close> as well --- so they cannot be compared by equality. \<open>dircycle_agree\<close> is the
  comparison on the \<^emph>\<open>common\<close> components: the search spine (\<open>stack\<close>, \<open>seen\<close>), the finished
  region and the cycle flag. Note this is equality of the \<open>finished\<close> \<^emph>\<open>vsets\<close>, not merely of the
  sets they denote --- both runs build that vset by the same chain of \<open>insert\<close>s.\<close>
definition dircycle_agree ::
  "('v, 'vset) DFS_dircycle_linear_tracked_aux_state \<Rightarrow> ('v, 'vset) DFS_dircycle_state \<Rightarrow> bool" where
  "dircycle_agree st st' \<longleftrightarrow>
     stack st = stack st'
   \<and> seen st = seen st'
   \<and> DFS_dircycle_linear_tracked_aux_state.finished st = DFS_dircycle_state.finished st'
   \<and> DFS_dircycle_linear_tracked_aux_state.cycle st = DFS_dircycle_state.cycle st'"

lemma dircycle_agree_intro[intro]:
  assumes "stack st = stack st'"
      and "seen st = seen st'"
      and "DFS_dircycle_linear_tracked_aux_state.finished st = DFS_dircycle_state.finished st'"
      and "DFS_dircycle_linear_tracked_aux_state.cycle st = DFS_dircycle_state.cycle st'"
  shows "dircycle_agree st st'"
  using assms by (simp add: dircycle_agree_def)

lemma dircycle_agree_props[elim]:
  "dircycle_agree st st' \<Longrightarrow>
     (\<lbrakk>stack st = stack st'; seen st = seen st';
       DFS_dircycle_linear_tracked_aux_state.finished st = DFS_dircycle_state.finished st';
       DFS_dircycle_linear_tracked_aux_state.cycle st = DFS_dircycle_state.cycle st'\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (simp add: dircycle_agree_def)

lemma dircycle_agreeD:
  assumes "dircycle_agree st st'"
  shows "stack st = stack st'"
    and "seen st = seen st'"
    and "DFS_dircycle_linear_tracked_aux_state.finished st = DFS_dircycle_state.finished st'"
    and "DFS_dircycle_linear_tracked_aux_state.cycle st = DFS_dircycle_state.cycle st'"
  using assms by (simp_all add: dircycle_agree_def)

context DFS_dircycle_linear_tracked_aux_thms
begin

subsection \<open>The five invariants the agreement argument runs on\<close>

text \<open>Exactly the bundle \<open>invar_gray_stack_holds\<close> needs: they are what makes the two back-edge
  tests coincide, and (through \<open>invar_ssf\<close>) what gives the reference run its domain.\<close>
definition "tracked_spine_invar st \<longleftrightarrow>
    dc.invar_1 st \<and> invar_fin st \<and> invar_ssf st \<and> invar_gray st \<and> invar_gray_stack st"

lemma tracked_spine_invar_intro:
  assumes "dc.invar_1 st"
      and "invar_fin st"
      and "invar_ssf st"
      and "invar_gray st"
      and "invar_gray_stack st"
  shows "tracked_spine_invar st"
  using assms by (simp add: tracked_spine_invar_def)

lemma tracked_spine_invarD:
  assumes "tracked_spine_invar st"
  shows "dc.invar_1 st"
    and "invar_fin st"
    and "invar_ssf st"
    and "invar_gray st"
    and "invar_gray_stack st"
  using assms by (simp_all add: tracked_spine_invar_def)

lemma tracked_spine_invar_initial: "tracked_spine_invar dircycle_tracked_initial_state"
  by (simp add: tracked_spine_invar_def)

lemma tracked_spine_invar_upd1:
  assumes c: "dc.DFS_skel_more_call_1_conds st"
      and i: "tracked_spine_invar st"
  shows "tracked_spine_invar (dc.DFS_skel_more_upd1 st)"
  using dc.invar_1_holds_1[OF c tracked_spine_invarD(1)[OF i]]
  using invar_fin_holds_upd1[OF c tracked_spine_invarD(2)[OF i]]
  using invar_ssf_holds_upd1[OF c tracked_spine_invarD(1)[OF i] tracked_spine_invarD(3)[OF i]]
  using invar_gray_holds_upd1[OF c tracked_spine_invarD(4)[OF i]]
  using invar_gray_stack_holds_upd1[OF c tracked_spine_invarD(4)[OF i]
                                       tracked_spine_invarD(5)[OF i]]
  by (rule tracked_spine_invar_intro)

lemma tracked_spine_invar_upd2:
  assumes c: "dc.DFS_skel_more_call_2_conds st"
      and i: "tracked_spine_invar st"
  shows "tracked_spine_invar (dc.DFS_skel_more_upd2 st)"
  using dc.invar_1_holds_2[OF c tracked_spine_invarD(1)[OF i]]
  using invar_fin_holds_upd2[OF c tracked_spine_invarD(2)[OF i]]
  using invar_ssf_holds_upd2[OF c tracked_spine_invarD(1)[OF i] tracked_spine_invarD(2)[OF i]
                                tracked_spine_invarD(3)[OF i]]
  using invar_gray_holds_upd2[OF c tracked_spine_invarD(4)[OF i]]
  using invar_gray_stack_holds_upd2[OF c tracked_spine_invarD(3)[OF i]
                                       tracked_spine_invarD(4)[OF i]
                                       tracked_spine_invarD(5)[OF i]]
  by (rule tracked_spine_invar_intro)

subsection \<open>Step-for-step agreement\<close>

text \<open>The crux, and the only place the tracked run genuinely differs: its \<open>found\<close> reads \<open>gray\<close>
  where the reference recomputes \<open>seen - finished\<close>. Under the invariants
  \<open>cyc_found_agrees\<close> identifies the two.\<close>
lemma cyc_found_agree:
  assumes i: "tracked_spine_invar st"
      and ag: "dircycle_agree st st'"
  shows "cyc_found st = lin.cyc_found st'"
proof (cases "stack st")
  case Nil
  thus ?thesis
    using dircycle_agreeD(1)[OF ag]
    by (simp add: cyc_found_def lin.cyc_found_def)
next
  case (Cons v vs)
  have stk: "stack st' = v # vs"
    using dircycle_agreeD(1)[OF ag] Cons by simp
  have "cyc_found st \<longleftrightarrow>
          ((\<N>\<^sub>G v) \<inter>\<^sub>G (seen st' -\<^sub>G DFS_dircycle_state.finished st')) \<noteq> \<emptyset>\<^sub>N"
    using cyc_found_agrees[OF tracked_spine_invarD(1)[OF i] tracked_spine_invarD(2)[OF i]
                              tracked_spine_invarD(3)[OF i] tracked_spine_invarD(4)[OF i]
                              tracked_spine_invarD(5)[OF i]]
    using Cons dircycle_agreeD(2)[OF ag] dircycle_agreeD(3)[OF ag]
    by simp
  thus ?thesis by (simp add: lin.cyc_found_def stk)
qed

text \<open>With the back-edge tests identified, both loops branch on the same data, so all four
  call/return conditions coincide.\<close>
lemma dircycle_conds_agree:
  assumes ag: "dircycle_agree st st'"
      and fnd: "cyc_found st = lin.cyc_found st'"
  shows "dc.DFS_skel_more_call_1_conds st = lin.dc.DFS_skel_call_1_conds st'"
    and "dc.DFS_skel_more_call_2_conds st = lin.dc.DFS_skel_call_2_conds st'"
    and "dc.DFS_skel_more_ret_1_conds st = lin.dc.DFS_skel_ret_1_conds st'"
    and "dc.DFS_skel_more_ret_2_conds st = lin.dc.DFS_skel_ret_2_conds st'"
  by (simp_all add: dircycle_agreeD(1)[OF ag] dircycle_agreeD(2)[OF ag] fnd
                    dc.DFS_skel_more_call_1_conds_def lin.dc.DFS_skel_call_1_conds_def
                    dc.DFS_skel_more_call_2_conds_def lin.dc.DFS_skel_call_2_conds_def
                    dc.DFS_skel_more_ret_1_conds_def lin.dc.DFS_skel_ret_1_conds_def
                    dc.DFS_skel_more_ret_2_conds_def lin.dc.DFS_skel_ret_2_conds_def
              split: list.splits)

text \<open>And the four step functions move the shared components identically: \<open>on_push\<close> and the
  tracked backtrack touch only \<open>gray\<close> and \<open>unfinished\<close>.\<close>
lemma dircycle_upd1_agree:
  assumes "dircycle_agree st st'"
  shows "dircycle_agree (dc.DFS_skel_more_upd1 st) (lin.dc.DFS_skel_upd1 st')"
  using assms by (auto simp: dircycle_agree_def upd1_unfold lin.upd1_unfold)

lemma dircycle_upd2_agree:
  assumes "dircycle_agree st st'"
  shows "dircycle_agree (dc.DFS_skel_more_upd2 st) (lin.dc.DFS_skel_upd2 st')"
  using assms by (auto simp: dircycle_agree_def upd2_unfold lin.upd2_unfold)

lemma dircycle_ret1_agree:
  assumes "dircycle_agree st st'"
  shows "dircycle_agree (dc.DFS_skel_more_ret1 st) (lin.dc.DFS_skel_ret1 st')"
  using assms
  by (simp add: dc.DFS_skel_more_ret1_def cyc_on_empty_def
                lin.dc.DFS_skel_ret1_def lin.cyc_on_empty_def)

lemma dircycle_ret2_agree:
  assumes "dircycle_agree st st'"
  shows "dircycle_agree (dc.DFS_skel_more_ret2 st) (lin.dc.DFS_skel_ret2 st')"
  using assms
  by (simp add: dircycle_agree_def dc.DFS_skel_more_ret2_def cyc_on_found_def
                lin.dc.DFS_skel_ret2_def lin.cyc_on_found_def)

text \<open>The reference run's domain comes for free from the tracked invariants: the skeleton's own
  termination argument reads only the spine.\<close>
lemma lin_dom_of_agree:
  assumes i: "tracked_spine_invar st"
      and ag: "dircycle_agree st st'"
  shows "lin.dc.DFS_skel_dom st'"
proof (rule lin.dc.DFS_skel_terminates)
  show "lin.dc.invar_1 st'"
    using tracked_spine_invarD(1)[OF i] dircycle_agreeD(2)[OF ag]
    by (simp add: dc.invar_1_def lin.dc.invar_1_def)
  show "lin.dc.invar_seen_stack st'"
    using tracked_spine_invarD(3)[OF i] dircycle_agreeD(1)[OF ag] dircycle_agreeD(2)[OF ag]
    by (simp add: invar_ssf_def lin.dc.invar_seen_stack_def)
qed

theorem dircycle_run_agree:
  assumes dom: "dc.DFS_skel_more_dom st"
      and "tracked_spine_invar st"
      and "dircycle_agree st st'"
  shows "dircycle_agree (dc.DFS_skel_more st) (lin.dc.DFS_skel st')"
  using assms(2-)
proof (induction arbitrary: st' rule: dc.DFS_skel_more_induct[OF dom])
  case IH: (1 st)
  note simps = dc.DFS_skel_more_simps[OF IH(1)]
  note lsimps = lin.dc.DFS_skel_simps[OF lin_dom_of_agree[OF IH(4) IH(5)]]
  note conds = dircycle_conds_agree[OF IH(5) cyc_found_agree[OF IH(4) IH(5)]]
  show ?case
  proof (rule dc.DFS_skel_more_cases[where dfs_state = st])
    assume c: "dc.DFS_skel_more_call_1_conds st"
    have "dircycle_agree (dc.DFS_skel_more (dc.DFS_skel_more_upd1 st))
                         (lin.dc.DFS_skel (lin.dc.DFS_skel_upd1 st'))"
      by (rule IH(2)[OF c tracked_spine_invar_upd1[OF c IH(4)] dircycle_upd1_agree[OF IH(5)]])
    thus "dircycle_agree (dc.DFS_skel_more st) (lin.dc.DFS_skel st')"
      by (simp add: simps(1)[OF c] lsimps(1)[OF conds(1)[THEN iffD1, OF c]])
  next
    assume c: "dc.DFS_skel_more_call_2_conds st"
    have "dircycle_agree (dc.DFS_skel_more (dc.DFS_skel_more_upd2 st))
                         (lin.dc.DFS_skel (lin.dc.DFS_skel_upd2 st'))"
      by (rule IH(3)[OF c tracked_spine_invar_upd2[OF c IH(4)] dircycle_upd2_agree[OF IH(5)]])
    thus "dircycle_agree (dc.DFS_skel_more st) (lin.dc.DFS_skel st')"
      by (simp add: simps(2)[OF c] lsimps(2)[OF conds(2)[THEN iffD1, OF c]])
  next
    assume c: "dc.DFS_skel_more_ret_1_conds st"
    show "dircycle_agree (dc.DFS_skel_more st) (lin.dc.DFS_skel st')"
      using dircycle_ret1_agree[OF IH(5)]
      by (simp add: simps(3)[OF c] lsimps(3)[OF conds(3)[THEN iffD1, OF c]])
  next
    assume c: "dc.DFS_skel_more_ret_2_conds st"
    show "dircycle_agree (dc.DFS_skel_more st) (lin.dc.DFS_skel st')"
      using dircycle_ret2_agree[OF IH(5)]
      by (simp add: simps(4)[OF c] lsimps(4)[OF conds(4)[THEN iffD1, OF c]])
  qed
qed

subsection \<open>The two inner runs\<close>

lemma dircycle_initial_agree:
  "dircycle_agree dircycle_tracked_initial_state lin.dircycle_linear_initial_state"
  by (simp add: dircycle_agree_def dircycle_tracked_initial_state_def
                lin.dircycle_linear_initial_state_def)

theorem dircycle_tracked_agrees_linear:
  "dircycle_agree dircycle_tracked_result lin.dircycle_linear_result"
  by (rule dircycle_run_agree[OF dircycle_tracked_initial_dom tracked_spine_invar_initial
                                dircycle_initial_agree])

corollary dircycle_tracked_stack_eq:
  "stack dircycle_tracked_result = stack lin.dircycle_linear_result"
  by (rule dircycle_agreeD(1)[OF dircycle_tracked_agrees_linear])

corollary dircycle_tracked_seen_eq:
  "seen dircycle_tracked_result = seen lin.dircycle_linear_result"
  by (rule dircycle_agreeD(2)[OF dircycle_tracked_agrees_linear])

corollary dircycle_tracked_finished_eq:
  "DFS_dircycle_linear_tracked_aux_state.finished dircycle_tracked_result
     = DFS_dircycle_state.finished lin.dircycle_linear_result"
  by (rule dircycle_agreeD(3)[OF dircycle_tracked_agrees_linear])

corollary dircycle_tracked_cycle_eq:
  "DFS_dircycle_linear_tracked_aux_state.cycle dircycle_tracked_result
     = DFS_dircycle_state.cycle lin.dircycle_linear_result"
  by (rule dircycle_agreeD(4)[OF dircycle_tracked_agrees_linear])

end

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
