theory DFS_DirCycle_Linear_Aux
  imports DFS_DirCycle
begin

text \<open>An \<^emph>\<open>extension\<close> of the graph library's directed-cycle detector \<^locale>\<open>DFS_dircycle\<close>
  (\<open>DFS_DirCycle\<close>): the same state, step functions and invariants, generalized from
  a \<^emph>\<open>fresh\<close> start to one \<^emph>\<open>pre-seeded\<close> with an already-processed region \<open>f\<close> --- a single run of
  the outer loop of a linear (whole-graph) directed-cycle search, which sweeps the roots and hands
  each call the vertices the earlier calls already finished. Both \<open>seen\<close> and \<open>finished\<close> start at
  \<open>f\<close> --- seeding \<^emph>\<open>only\<close> \<open>finished\<close> would break \<open>invar_ssf\<close>'s \<open>finished \<subseteq> seen\<close>, and would also
  let \<open>call_1\<close> walk back into \<open>f\<close>, which is exactly the re-exploration this variant exists to
  avoid.

  Because the library's invariant-preservation lemmas quantify over an \<^emph>\<open>arbitrary\<close> state, they
  apply to the seeded run verbatim and are \<^emph>\<open>inherited\<close>, not repeated: this theory adds only the
  seed parameter \<open>f\<close>, the seeded initial state, the extra axioms on \<open>f\<close> that make the inherited
  invariants hold at that state (instead of trivially at \<open>finished = \<emptyset>\<^sub>N\<close>), one new invariant
  (\<open>invar_seed\<close>: the seed is never lost), and the exports the outer loop needs.\<close>

locale DFS_dircycle_linear_aux = DFS_dircycle where lookup = lookup
  for lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option" +
fixes f::"'vset"
begin

definition "dircycle_linear_initial_state =
  \<lparr>stack = [s], seen = insert s f, finished = f, cycle = False\<rparr>"

text \<open>The library's \<open>DFS_dircycle_axioms\<close> plus five conditions on the seed \<open>f\<close>. Three make
  \<^const>\<open>dircycle_linear_initial_state\<close> well-formed:
  \<^item> \<open>s \<notin> t_set f\<close> --- so the stack \<open>[s]\<close> is disjoint from \<open>finished\<close>, giving
    \<open>finished = seen - stack\<close> at the start (and re-running from an already-finished root would be
    pointless anyway);
  \<^item> \<open>vset_inv f\<close> --- \<open>f\<close> is a well-formed vset, needed for \<open>invar_fin\<close> and for \<open>t_set\<close> to commute
    with \<^const>\<open>insert\<close>;
  \<^item> \<open>t_set f \<subseteq> dVs\<close> --- since \<open>seen\<close> now starts at \<open>insert s f\<close>, the \<open>seen \<subseteq> dVs\<close> conjunct
    reaches into \<open>f\<close>.

  The remaining two are the caller's contract, i.e. what the outer loop must have established about
  the region it already searched: \<open>f\<close> is closed under successors, and \<open>G\<close> restricted to \<open>f\<close> is
  acyclic. Together they are what lets \<open>invar_finished_closed\<close> and \<open>invar_cycle_false\<close> hold at the
  seeded initial state instead of trivially at \<open>finished = \<emptyset>\<^sub>N\<close>.\<close>
definition "DFS_dircycle_linear_aux_axioms =
  (DFS_dircycle_axioms
  \<and> s \<notin> t_set f
  \<and> vset_inv f
  \<and> t_set f \<subseteq> dVs (Graph.digraph_abs G)
  \<and> (\<forall>u w. u \<in> t_set f \<longrightarrow> (u, w) \<in> Graph.digraph_abs G \<longrightarrow> w \<in> t_set f)
  \<and> (\<nexists>c. Awalk_Defs.cycle (Graph.digraph_abs G \<downharpoonright> t_set f) c))"

abbreviation "find_dircycle_linear \<equiv> dc.DFS_skeleton_impl"

end

locale DFS_dircycle_linear_aux_thms = DFS_dircycle_linear_aux +
  assumes dircycle_linear_axioms: DFS_dircycle_linear_aux_axioms
begin

text \<open>The seeded axioms subsume the library's, so all of \<^locale>\<open>DFS_dircycle_thms\<close> --- the
  \<open>dc\<close> skeleton theorems and every invariant definition and preservation lemma --- is inherited.\<close>
sublocale DFS_dircycle_thms
  using dircycle_linear_axioms
  by unfold_locales (auto simp: DFS_dircycle_linear_aux_axioms_def)

context
includes set_ops.automation2 and Graph.adjmap.automation and Graph.vset.set.automation
begin

subsection \<open>The inherited invariants hold at the seeded initial state\<close>

text \<open>This is where the seeded run genuinely differs from the library's fresh one: each inherited
  invariant must be re-established at \<^const>\<open>dircycle_linear_initial_state\<close>, which is exactly
  what the extra axioms on \<open>f\<close> provide.\<close>

lemma linear_initial_invars[simp,intro]:
  "dc.invar_1 dircycle_linear_initial_state"
  "dc.invar_seen_stack dircycle_linear_initial_state"
  using dircycle_linear_axioms
  by (auto simp: dc.invar_1_def dc.invar_seen_stack_def dircycle_linear_initial_state_def
                 DFS_dircycle_linear_aux_axioms_def DFS_dircycle_axioms_def)

lemma dircycle_linear_initial_dom: "dc.DFS_skeleton_dom dircycle_linear_initial_state"
  by (intro dc.DFS_skeleton_terminates linear_initial_invars)

lemma linear_initial_struct[simp,intro]:
  "invar_2 dircycle_linear_initial_state"
  "invar_ssf dircycle_linear_initial_state"
  using dircycle_linear_axioms
  by (auto simp: invar_2_def invar_ssf_def dircycle_linear_initial_state_def
                 DFS_dircycle_linear_aux_axioms_def DFS_dircycle_axioms_def)

lemma linear_initial_fin[simp,intro]: "invar_fin dircycle_linear_initial_state"
  using dircycle_linear_axioms[unfolded DFS_dircycle_linear_aux_axioms_def]
  by (simp add: invar_fin_def dircycle_linear_initial_state_def)

lemma linear_initial_fc[simp,intro]:
  "invar_finished_closed dircycle_linear_initial_state"
  "invar_cycle_false dircycle_linear_initial_state"
  using dircycle_linear_axioms[unfolded DFS_dircycle_linear_aux_axioms_def]
  by (auto simp: invar_finished_closed_def invar_cycle_false_def
                 dircycle_linear_initial_state_def)

subsection \<open>Soundness and completeness of the seeded run\<close>

theorem DFS_dircycle_linear_sound:
  assumes "cycle (dc.DFS_skeleton dircycle_linear_initial_state)"
  shows "\<exists>c. Awalk_Defs.cycle (Graph.digraph_abs G) c"
proof -
  have "invar_cycle_true (dc.DFS_skeleton dircycle_linear_initial_state)"
    by (intro invar_cycle_true_holds dircycle_linear_initial_dom linear_initial_invars
              linear_initial_fin linear_initial_struct)
       (auto simp: invar_cycle_true_def dircycle_linear_initial_state_def)
  thus ?thesis using assms by (auto elim!: invar_props_elims)
qed

text \<open>Completeness reports on \<open>finished\<close> rather than \<open>seen\<close> (contrast the library's
  \<open>DFS_dircycle_complete\<close>): the outer loop consumes exactly the finished region.\<close>
theorem DFS_dircycle_linear_complete:
  assumes "\<not> cycle (dc.DFS_skeleton dircycle_linear_initial_state)"
  shows "\<nexists>c. Awalk_Defs.cycle (Graph.digraph_abs G \<downharpoonright> t_set (finished (dc.DFS_skeleton dircycle_linear_initial_state))) c"
proof -
  let ?r = "dc.DFS_skeleton dircycle_linear_initial_state"
  have dom: "dc.DFS_skeleton_dom dircycle_linear_initial_state" by (rule dircycle_linear_initial_dom)
  have cf: "invar_cycle_false ?r"
    by (intro invar_cycle_false_holds dom linear_initial_invars linear_initial_fin
              linear_initial_struct linear_initial_fc)
  have acyc: "\<nexists>c. Awalk_Defs.cycle (Graph.digraph_abs G \<downharpoonright> t_set (finished ?r)) c"
    using cf assms by (auto elim!: invar_props_elims)
  show ?thesis
  proof (rule notI, erule exE)
    fix c assume "Awalk_Defs.cycle (Graph.digraph_abs G \<downharpoonright> t_set (finished ?r)) c"
    thus False using acyc by blast
  qed
qed

subsection \<open>What one run exports to the outer (linear) loop\<close>

text \<open>The outer loop of a whole-graph search calls this DFS once per remaining root, threading the
  accumulated finished region through as the next call's \<open>f\<close>. To do that it needs more than
  soundness and completeness: it must re-establish this locale's \<^emph>\<open>own\<close> assumptions on \<open>f\<close> for
  the enlarged region, and it needs progress (the root really was absorbed) so the loop's measure
  decreases. Those are the five exports below.\<close>

definition "invar_seed dfs_state \<longleftrightarrow>
    Set.insert s (t_set f) \<subseteq> t_set (seen dfs_state)
  \<and> t_set f \<subseteq> t_set (finished dfs_state)"

lemma invar_seed_props[invar_props_elims]:
  "invar_seed dfs_state \<Longrightarrow>
     (\<lbrakk>Set.insert s (t_set f) \<subseteq> t_set (seen dfs_state);
       t_set f \<subseteq> t_set (finished dfs_state)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_seed_def)

lemma invar_seed_intro[invar_props_intros]:
  "\<lbrakk>Set.insert s (t_set f) \<subseteq> t_set (seen dfs_state);
    t_set f \<subseteq> t_set (finished dfs_state)\<rbrakk> \<Longrightarrow> invar_seed dfs_state"
  by (auto simp: invar_seed_def)

lemma invar_seed_holds_upd1[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skeleton_call_1_conds dfs_state; dc.invar_1 dfs_state; invar_seed dfs_state\<rbrakk> \<Longrightarrow>
    invar_seed (dc.DFS_skeleton_upd1 dfs_state)"
  by (auto simp: upd1_unfold elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_seed_holds_upd2[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skeleton_call_2_conds dfs_state; invar_fin dfs_state; invar_seed dfs_state\<rbrakk> \<Longrightarrow>
    invar_seed (dc.DFS_skeleton_upd2 dfs_state)"
  by (auto simp: upd2_unfold elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_seed_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skeleton_ret_1_conds dfs_state; invar_seed dfs_state\<rbrakk> \<Longrightarrow> invar_seed (dc.DFS_skeleton_ret1 dfs_state)"
  by (auto simp: dc.DFS_skeleton_ret1_def cyc_on_empty_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_seed_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>dc.DFS_skeleton_ret_2_conds dfs_state; invar_seed dfs_state\<rbrakk> \<Longrightarrow> invar_seed (dc.DFS_skeleton_ret2 dfs_state)"
  by (auto simp: dc.DFS_skeleton_ret2_def cyc_on_found_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_seed_holds[invar_holds_intros]:
  assumes "dc.DFS_skeleton_dom dfs_state" "dc.invar_1 dfs_state" "invar_fin dfs_state" "invar_seed dfs_state"
  shows "invar_seed (dc.DFS_skeleton dfs_state)"
  using assms(2-)
proof(induction rule: dc.DFS_skeleton_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule dc.DFS_skeleton_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-) invar_holds_intros simp: dc.DFS_skeleton_simps[OF IH(1)])
qed

lemma initial_seed[simp,intro]: "invar_seed dircycle_linear_initial_state"
  using dircycle_linear_axioms
  by (auto simp: invar_seed_def dircycle_linear_initial_state_def
                 DFS_dircycle_linear_aux_axioms_def)

abbreviation "dircycle_linear_result \<equiv> dc.DFS_skeleton dircycle_linear_initial_state"

lemma dircycle_linear_invars:
  "dc.invar_1 dircycle_linear_result"
  "invar_fin dircycle_linear_result"
  "invar_ssf dircycle_linear_result"
  "invar_finished_closed dircycle_linear_result"
  "invar_seed dircycle_linear_result"
  by (intro dc.invar_1_holds invar_fin_holds invar_ssf_holds invar_finished_closed_holds
            invar_seed_holds dircycle_linear_initial_dom linear_initial_invars linear_initial_fin
            linear_initial_struct linear_initial_fc initial_seed)+

text \<open>\<^bold>\<open>Export 1--3\<close>: the enlarged finished region again satisfies this locale's structural
  assumptions on \<open>f\<close> --- a well-formed vset, inside the vertex set, and successor-closed --- so it
  may be handed to the next call as its seed.\<close>

lemma dircycle_linear_finished_inv: "vset_inv (finished dircycle_linear_result)"
  using dircycle_linear_invars(2) by (auto simp: invar_fin_def)

lemma dircycle_linear_finished_subset_dVs:
  "t_set (finished dircycle_linear_result) \<subseteq> dVs (Graph.digraph_abs G)"
  using dircycle_linear_invars(3) by (auto elim!: invar_props_elims)

lemma dircycle_linear_finished_closed:
  assumes "u \<in> t_set (finished dircycle_linear_result)" and "(u, w) \<in> Graph.digraph_abs G"
  shows "w \<in> t_set (finished dircycle_linear_result)"
  using dircycle_linear_invars(4) assms by (auto simp: invar_finished_closed_def)

text \<open>\<^bold>\<open>Export 4\<close>: the seed is never lost --- the finished region only grows.\<close>

lemma dircycle_linear_seed_subset: "t_set f \<subseteq> t_set (finished dircycle_linear_result)"
  using dircycle_linear_invars(5) by (auto elim!: invar_props_elims)

text \<open>\<^bold>\<open>Export 5\<close>: \<^emph>\<open>progress\<close>. On a clean run the stack is empty at the return, so
  \<open>invar_ssf\<close> collapses to \<open>finished = seen\<close>, and \<open>seen\<close> has contained the root since the initial
  state. Without this the outer loop's measure need not decrease.\<close>

lemma dircycle_linear_root_finished:
  assumes "\<not> cycle dircycle_linear_result"
  shows "s \<in> t_set (finished dircycle_linear_result)"
proof -
  have empty: "stack dircycle_linear_result = []"
    using no_cycle_ret_1[OF dircycle_linear_initial_dom assms]
    by (auto simp: dc.DFS_skeleton_ret_1_conds_def split: list.splits)
  have "t_set (finished dircycle_linear_result) = t_set (seen dircycle_linear_result)"
    using dircycle_linear_invars(3) empty by (auto elim!: invar_props_elims)
  thus ?thesis using dircycle_linear_invars(5) by (auto elim!: invar_props_elims)
qed

end

end

end

