theory DFS_DirCycle_Linear
  imports DFS_DirCycle_Linear_Aux
begin

text \<open>The directed counterpart of \<open>DFS_Cycles\<close>: a whole-graph (linear) cycle search whose outer
  loop sweeps the vertices and calls a directed-cycle DFS --- the library's \<open>DFS_DirCycle\<close>
  extended with a pre-seeded initial state, \<^theory>\<open>Directed_Cycle_DFS.DFS_DirCycle_Linear_Aux\<close> ---
  once per remaining root.

  \<^bold>\<open>The one structural difference from \<open>DFS_Cycles\<close>.\<close> The undirected version fixes
  \<open>dfs_aux :: 'v \<Rightarrow> 'state\<close> --- the inner call takes only a root, runs on a \<^emph>\<open>fresh\<close> state, and the
  outer loop unions the result into its own \<open>seen\<close>. That works there because in an undirected graph
  the vertices reachable from a fresh root form a whole connected component, so the regions the
  calls return are disjoint and can simply be accumulated. Directed reachability has no such
  property: a later root can reach into an earlier call's region, and re-exploring it is both
  wasteful and unsound to union blindly. So here the inner call takes the accumulated region as
  well, \<open>dfs_aux :: 'v \<Rightarrow> 'vset \<Rightarrow> 'state\<close>, and returns the \<^emph>\<open>enlarged\<close> region --- the outer loop
  overwrites rather than unions.

  \<^bold>\<open>Why the invariant is simpler than the undirected one.\<close> \<open>DFS_Cycles\<close> carries \<open>invar_seen\<close>,
  which says seen and unseen vertices are mutually unreachable --- a connected-component argument
  that needs the symmetry axiom. The directed version needs no reachability invariant at all: it
  carries \<open>seed_ok\<close>, i.e. exactly the contract
  \<^locale>\<open>DFS_dircycle_linear_aux_thms\<close> places on its seed \<open>f\<close> (successor-closed, and acyclic when
  restricted to). Successor-closedness is what makes accumulation sound in a directed graph, and it
  is precisely what the inner DFS re-establishes for the region it finished.\<close>

text \<open>\<open>DFS_Skeleton\<close> declares the \<open>call_cond_*\<close> / \<open>invar_*\<close> / \<open>ret_holds_intros\<close> bundles, but
  \<open>termination_intros\<close> is declared locally in \<open>DFS_Cycles\<close> (the outer loop is where termination is
  argued), so it must be declared here too.\<close>
named_theorems termination_intros

record ('ver, 'vset) DFS_dircycle_linear_state = fin :: "'vset" cyc :: bool

locale DFS_dircycle_linear =
  Graph: Pair_Graph_Specs where lookup = lookup +
  set_ops: Set2 vset_empty vset_delete _ t_set vset_inv insert
for lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option" +
fixes G::"'adjmap" and V::"'vset"
  and dfs_aux::"'v \<Rightarrow> 'vset \<Rightarrow> 'state"
  and fin_aux::"'state \<Rightarrow> 'vset" and cycle_aux::"'state \<Rightarrow> bool"
begin

abbreviation "neighbourhood' \<equiv> Graph.neighbourhood G"
notation "neighbourhood'" ("\<N>\<^sub>G _" 100)

text \<open>No symmetry and no loop-freeness: unlike \<open>DFS_Cycles_axioms\<close> this is a genuinely directed
  graph.\<close>
definition "DFS_dircycle_linear_axioms = (
  Graph.graph_inv G \<and> Graph.finite_graph G \<and> Graph.finite_vsets G \<and>
  vset_inv V \<and> (t_set V = dVs (Graph.digraph_abs G)))"

text \<open>The seed contract, i.e. what the accumulated region must satisfy for the next inner call to
  be legitimate. It is exactly the \<open>f\<close>-part of \<open>DFS_dircycle_linear_aux_axioms\<close>.\<close>
definition "seed_ok fs \<longleftrightarrow>
  vset_inv fs \<and> t_set fs \<subseteq> dVs (Graph.digraph_abs G)
  \<and> (\<forall>u w. u \<in> t_set fs \<longrightarrow> (u, w) \<in> Graph.digraph_abs G \<longrightarrow> w \<in> t_set fs)
  \<and> (\<nexists>c. Awalk_Defs.cycle (Graph.digraph_abs G \<downharpoonright> t_set fs) c)"

text \<open>What the inner DFS must deliver. Every conjunct is discharged for the concrete DFS by the
  exports of \<^theory>\<open>Directed_Cycle_DFS.DFS_DirCycle_Linear_Aux\<close>: \<open>dircycle_linear_finished_inv\<close>,
  \<open>_seed_subset\<close>, \<open>_finished_subset_dVs\<close>, \<open>_finished_closed\<close>, \<open>DFS_dircycle_linear_sound\<close>,
  \<open>_root_finished\<close> and \<open>DFS_dircycle_linear_complete\<close>, in that order.\<close>
definition "dfs_aux_axioms = (
  \<forall>s \<in> dVs (Graph.digraph_abs G). \<forall>fs. seed_ok fs \<longrightarrow> s \<notin> t_set fs \<longrightarrow>
    (vset_inv (fin_aux (dfs_aux s fs))
     \<and> t_set fs \<subseteq> t_set (fin_aux (dfs_aux s fs))
     \<and> t_set (fin_aux (dfs_aux s fs)) \<subseteq> dVs (Graph.digraph_abs G)
     \<and> (\<forall>u w. u \<in> t_set (fin_aux (dfs_aux s fs)) \<longrightarrow> (u, w) \<in> Graph.digraph_abs G \<longrightarrow>
          w \<in> t_set (fin_aux (dfs_aux s fs)))
     \<and> (cycle_aux (dfs_aux s fs) \<longrightarrow> (\<exists>c. Awalk_Defs.cycle (Graph.digraph_abs G) c))
     \<and> (\<not> cycle_aux (dfs_aux s fs) \<longrightarrow>
          s \<in> t_set (fin_aux (dfs_aux s fs))
          \<and> (\<nexists>c. Awalk_Defs.cycle (Graph.digraph_abs G \<downharpoonright> t_set (fin_aux (dfs_aux s fs))) c))))"

function (domintros) DFS_dircycle_linear::
  "('v, 'vset) DFS_dircycle_linear_state \<Rightarrow> ('v, 'vset) DFS_dircycle_linear_state" where
  "DFS_dircycle_linear st =
    (if V -\<^sub>G (fin st) \<noteq> \<emptyset>\<^sub>N
     then
      (let
        s = sel (V -\<^sub>G (fin st));
        aux = dfs_aux s (fin st)
      in
        (if cycle_aux aux
         then st \<lparr>cyc := True\<rparr>
         else DFS_dircycle_linear (st \<lparr>fin := fin_aux aux\<rparr>)))
     else st)"
  by pat_completeness auto

partial_function (tailrec) DFS_dircycle_linear_impl::
  "('v, 'vset) DFS_dircycle_linear_state \<Rightarrow> ('v, 'vset) DFS_dircycle_linear_state" where
  "DFS_dircycle_linear_impl st =
    (if V -\<^sub>G (fin st) \<noteq> \<emptyset>\<^sub>N
     then
      (let
        s = sel (V -\<^sub>G (fin st));
        aux = dfs_aux s (fin st)
      in
        (if cycle_aux aux
         then st \<lparr>cyc := True\<rparr>
         else DFS_dircycle_linear_impl (st \<lparr>fin := fin_aux aux\<rparr>)))
     else st)"

lemmas [code] = DFS_dircycle_linear_impl.simps

lemma DFS_dircycle_linear_impl_same:
  assumes "DFS_dircycle_linear_dom st"
  shows "DFS_dircycle_linear_impl st = DFS_dircycle_linear st"
  by(induction rule: DFS_dircycle_linear.pinduct[OF assms])
    (subst DFS_dircycle_linear.psimps, simp, subst DFS_dircycle_linear_impl.simps,
     auto split: if_split simp add: Let_def)

subsection \<open>Call conditions\<close>

definition "DFS_dircycle_linear_call_1_conds st =
    (if V -\<^sub>G (fin st) \<noteq> \<emptyset>\<^sub>N
     then (if cycle_aux (dfs_aux (sel (V -\<^sub>G (fin st))) (fin st)) then False else True)
     else False)"

lemma DFS_dircycle_linear_call_1_conds[call_cond_elims]:
  "DFS_dircycle_linear_call_1_conds st \<Longrightarrow>
   \<lbrakk>\<lbrakk>V -\<^sub>G (fin st) \<noteq> \<emptyset>\<^sub>N; \<not> cycle_aux (dfs_aux (sel (V -\<^sub>G (fin st))) (fin st))\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto simp: DFS_dircycle_linear_call_1_conds_def split: if_splits)

definition "DFS_dircycle_linear_upd1 st =
    (let
      s = sel (V -\<^sub>G (fin st));
      aux = dfs_aux s (fin st)
    in
      (st \<lparr>fin := fin_aux aux\<rparr>))"

definition "DFS_dircycle_linear_ret_1_conds st =
    (if V -\<^sub>G (fin st) \<noteq> \<emptyset>\<^sub>N
     then (if cycle_aux (dfs_aux (sel (V -\<^sub>G (fin st))) (fin st)) then True else False)
     else False)"

lemma DFS_dircycle_linear_ret_1_conds[call_cond_elims]:
  "DFS_dircycle_linear_ret_1_conds st \<Longrightarrow>
   \<lbrakk>\<lbrakk>V -\<^sub>G (fin st) \<noteq> \<emptyset>\<^sub>N; cycle_aux (dfs_aux (sel (V -\<^sub>G (fin st))) (fin st))\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto simp: DFS_dircycle_linear_ret_1_conds_def split: if_splits)

lemma DFS_dircycle_linear_ret_1_condsI[call_cond_intros]:
  "\<lbrakk>V -\<^sub>G (fin st) \<noteq> \<emptyset>\<^sub>N; cycle_aux (dfs_aux (sel (V -\<^sub>G (fin st))) (fin st))\<rbrakk> \<Longrightarrow>
    DFS_dircycle_linear_ret_1_conds st"
  by(auto simp: DFS_dircycle_linear_ret_1_conds_def split: if_splits)

definition "DFS_dircycle_linear_ret1 st = (st \<lparr>cyc := True\<rparr>)"

definition "DFS_dircycle_linear_ret_2_conds st =
    (if V -\<^sub>G (fin st) \<noteq> \<emptyset>\<^sub>N then False else True)"

lemma DFS_dircycle_linear_ret_2_conds[call_cond_elims]:
  "DFS_dircycle_linear_ret_2_conds st \<Longrightarrow> \<lbrakk>V -\<^sub>G (fin st) = \<emptyset>\<^sub>N \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto simp: DFS_dircycle_linear_ret_2_conds_def split: if_splits)

lemma DFS_dircycle_linear_ret_2_condsI[call_cond_intros]:
  "V -\<^sub>G (fin st) = \<emptyset>\<^sub>N \<Longrightarrow> DFS_dircycle_linear_ret_2_conds st"
  by(auto simp: DFS_dircycle_linear_ret_2_conds_def split: if_splits)

definition "DFS_dircycle_linear_ret2 st = st"

lemma DFS_dircycle_linear_cases:
  assumes "DFS_dircycle_linear_call_1_conds st \<Longrightarrow> P"
      "DFS_dircycle_linear_ret_1_conds st \<Longrightarrow> P"
      "DFS_dircycle_linear_ret_2_conds st \<Longrightarrow> P"
  shows "P"
proof-
  have "DFS_dircycle_linear_call_1_conds st \<or>
        DFS_dircycle_linear_ret_1_conds st \<or> DFS_dircycle_linear_ret_2_conds st"
    by (auto simp add: DFS_dircycle_linear_call_1_conds_def
                       DFS_dircycle_linear_ret_1_conds_def DFS_dircycle_linear_ret_2_conds_def
           split: list.split_asm option.split_asm if_splits)
  then show ?thesis using assms by auto
qed

lemma DFS_dircycle_linear_simps:
  assumes "DFS_dircycle_linear_dom st"
  shows "DFS_dircycle_linear_call_1_conds st \<Longrightarrow>
           DFS_dircycle_linear st = DFS_dircycle_linear (DFS_dircycle_linear_upd1 st)"
        "DFS_dircycle_linear_ret_1_conds st \<Longrightarrow>
           DFS_dircycle_linear st = DFS_dircycle_linear_ret1 st"
        "DFS_dircycle_linear_ret_2_conds st \<Longrightarrow>
           DFS_dircycle_linear st = DFS_dircycle_linear_ret2 st"
  by (auto simp add: DFS_dircycle_linear.psimps[OF assms] Let_def
                     DFS_dircycle_linear_call_1_conds_def DFS_dircycle_linear_upd1_def
                     DFS_dircycle_linear_ret_1_conds_def DFS_dircycle_linear_ret1_def
                     DFS_dircycle_linear_ret_2_conds_def DFS_dircycle_linear_ret2_def
            split: list.splits option.splits if_splits)

lemma DFS_dircycle_linear_induct:
  assumes "DFS_dircycle_linear_dom st"
  assumes "\<And>st. \<lbrakk>DFS_dircycle_linear_dom st;
     DFS_dircycle_linear_call_1_conds st \<Longrightarrow> P (DFS_dircycle_linear_upd1 st)\<rbrakk> \<Longrightarrow> P st"
  shows "P st"
  apply(rule DFS_dircycle_linear.pinduct[OF assms(1)])
  apply(rule assms(2)[simplified DFS_dircycle_linear_call_1_conds_def DFS_dircycle_linear_upd1_def])
  by (auto simp: Let_def split: list.splits option.splits if_splits)

lemma DFS_dircycle_linear_domintros:
  assumes "DFS_dircycle_linear_call_1_conds st \<Longrightarrow>
             DFS_dircycle_linear_dom (DFS_dircycle_linear_upd1 st)"
  shows "DFS_dircycle_linear_dom st"
proof(rule DFS_dircycle_linear.domintros, goal_cases)
  case 1
  then show ?case
    using assms(1)[simplified DFS_dircycle_linear_call_1_conds_def DFS_dircycle_linear_upd1_def]
    by (force simp: Let_def split: list.splits option.splits if_splits)
qed

definition "call_measure st = card (t_set (V -\<^sub>G fin st))"
definition "DFS_dircycle_linear_term_rel' = call_measure <*mlex*> {}"

definition "initial_state = \<lparr>fin = \<emptyset>\<^sub>N, cyc = False\<rparr>"
lemmas [code] = initial_state_def

subsection \<open>Invariants\<close>

definition "invar_1 st = vset_inv (fin st)"
definition "invar_seed st = seed_ok (fin st)"
definition "invar_cyc_true st = (cyc st \<longrightarrow> (\<exists>c. Awalk_Defs.cycle (Graph.digraph_abs G) c))"

end

locale DFS_dircycle_linear_thms = DFS_dircycle_linear +
  assumes graph_axioms: DFS_dircycle_linear_axioms
      and aux_axioms: dfs_aux_axioms
begin

context
includes Graph.adjmap.automation and Graph.vset.set.automation
begin

text \<open>\<open>DFS_Cycles\<close> makes the set-operation equations available to the automation inside its own
  \<open>includes\<close> context; without them nothing can reduce \<open>V -\<^sub>G fin st\<close>, and every
  \<open>force\<close>/\<open>auto\<close> over the unfinished region searches unboundedly instead of failing.\<close>
declare set_ops.set_union[simp] set_ops.set_inter[simp]
        set_ops.set_diff[simp] set_ops.invar_union[simp]
        set_ops.invar_inter[simp] set_ops.invar_diff[simp]
lemma V_graph_verts: "t_set V = dVs (Graph.digraph_abs G)"
  using graph_axioms by (auto simp: DFS_dircycle_linear_axioms_def)

lemma V_inv[simp, intro]: "vset_inv V"
  using graph_axioms by (auto simp: DFS_dircycle_linear_axioms_def)

lemma graph_inv[simp, intro]:
  "Graph.graph_inv G"
  "Graph.finite_graph G"
  "Graph.finite_vsets G"
  using graph_axioms by (auto simp: DFS_dircycle_linear_axioms_def)

lemma finite_vertices[simp, intro]: "finite (dVs (Graph.digraph_abs G))"
  using Graph.finite_vertices[OF graph_inv(1,2,3)] .

lemma invar_1_props[invar_props_elims]:
  "invar_1 st \<Longrightarrow> (vset_inv (fin st) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_1_def)

lemma invar_1_intro[invar_props_intros]: "vset_inv (fin st) \<Longrightarrow> invar_1 st"
  by (auto simp: invar_1_def)

lemma invar_seed_props[invar_props_elims]:
  "invar_seed st \<Longrightarrow> (seed_ok (fin st) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_seed_def)

lemma invar_seed_intro[invar_props_intros]: "seed_ok (fin st) \<Longrightarrow> invar_seed st"
  by (auto simp: invar_seed_def)

lemma invar_cyc_true_props[invar_props_elims]:
  "invar_cyc_true st \<Longrightarrow> ((cyc st \<Longrightarrow> \<exists>c. Awalk_Defs.cycle (Graph.digraph_abs G) c) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_cyc_true_def)

lemma invar_cyc_true_intro[invar_props_intros]:
  "(cyc st \<Longrightarrow> \<exists>c. Awalk_Defs.cycle (Graph.digraph_abs G) c) \<Longrightarrow> invar_cyc_true st"
  by (auto simp: invar_cyc_true_def)

text \<open>The selected root really is an unfinished vertex of the graph --- the side condition every
  use of \<open>dfs_aux_axioms\<close> needs.\<close>
lemma sel_mem:
  assumes "V -\<^sub>G (fin st) \<noteq> \<emptyset>\<^sub>N" and "invar_1 st"
  shows "sel (V -\<^sub>G (fin st)) \<in> t_set (V -\<^sub>G (fin st))"
  using assms V_inv by (force elim!: invar_props_elims)

lemma sel_root:
  assumes "V -\<^sub>G (fin st) \<noteq> \<emptyset>\<^sub>N" and "invar_1 st"
  shows "sel (V -\<^sub>G (fin st)) \<in> dVs (Graph.digraph_abs G)"
    and "sel (V -\<^sub>G (fin st)) \<notin> t_set (fin st)"
  using sel_mem[OF assms] assms(2) V_inv V_graph_verts
  by (force elim!: invar_props_elims, force elim!: invar_props_elims)

text \<open>The inner call's guarantees, instantiated at the selected root.\<close>
lemma aux_spec:
  assumes "V -\<^sub>G (fin st) \<noteq> \<emptyset>\<^sub>N" and "invar_1 st" and "invar_seed st"
  shows "vset_inv (fin_aux (dfs_aux (sel (V -\<^sub>G (fin st))) (fin st)))"
    and "t_set (fin st) \<subseteq> t_set (fin_aux (dfs_aux (sel (V -\<^sub>G (fin st))) (fin st)))"
    and "t_set (fin_aux (dfs_aux (sel (V -\<^sub>G (fin st))) (fin st))) \<subseteq> dVs (Graph.digraph_abs G)"
    and "\<And>u w. u \<in> t_set (fin_aux (dfs_aux (sel (V -\<^sub>G (fin st))) (fin st))) \<Longrightarrow>
           (u, w) \<in> Graph.digraph_abs G \<Longrightarrow>
           w \<in> t_set (fin_aux (dfs_aux (sel (V -\<^sub>G (fin st))) (fin st)))"
    and "cycle_aux (dfs_aux (sel (V -\<^sub>G (fin st))) (fin st)) \<Longrightarrow>
           \<exists>c. Awalk_Defs.cycle (Graph.digraph_abs G) c"
    and "\<not> cycle_aux (dfs_aux (sel (V -\<^sub>G (fin st))) (fin st)) \<Longrightarrow>
           sel (V -\<^sub>G (fin st)) \<in> t_set (fin_aux (dfs_aux (sel (V -\<^sub>G (fin st))) (fin st)))"
    and "\<not> cycle_aux (dfs_aux (sel (V -\<^sub>G (fin st))) (fin st)) \<Longrightarrow>
           \<nexists>c. Awalk_Defs.cycle
                 (Graph.digraph_abs G \<downharpoonright> t_set (fin_aux (dfs_aux (sel (V -\<^sub>G (fin st))) (fin st)))) c"
  using aux_axioms[unfolded dfs_aux_axioms_def, rule_format,
                   OF sel_root(1)[OF assms(1,2)] assms(3)[unfolded invar_seed_def]
                      sel_root(2)[OF assms(1,2)]]
  by auto

subsection \<open>Invariant preservation\<close>

lemma call_1_ne:
  assumes "DFS_dircycle_linear_call_1_conds st"
  shows "V -\<^sub>G (fin st) \<noteq> \<emptyset>\<^sub>N"
  using assms by (auto elim!: call_cond_elims)

lemma ret_1_ne:
  assumes "DFS_dircycle_linear_ret_1_conds st"
  shows "V -\<^sub>G (fin st) \<noteq> \<emptyset>\<^sub>N"
  using assms by (auto elim!: call_cond_elims)

lemma invar_1_holds_upd1[invar_holds_intros]:
  assumes "DFS_dircycle_linear_call_1_conds st" "invar_1 st" "invar_seed st"
  shows "invar_1 (DFS_dircycle_linear_upd1 st)"
  using aux_spec(1)[OF call_1_ne[OF assms(1)] assms(2,3)]
  by (auto simp: DFS_dircycle_linear_upd1_def Let_def intro!: invar_props_intros)

lemma invar_1_holds_ret_1[invar_holds_intros]:
  "invar_1 st \<Longrightarrow> invar_1 (DFS_dircycle_linear_ret1 st)"
  by (auto simp: DFS_dircycle_linear_ret1_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_1_holds_ret_2[invar_holds_intros]:
  "invar_1 st \<Longrightarrow> invar_1 (DFS_dircycle_linear_ret2 st)"
  by (auto simp: DFS_dircycle_linear_ret2_def elim!: invar_props_elims intro!: invar_props_intros)

text \<open>The heart of the outer loop: the enlarged region again satisfies the seed contract. Both
  interesting conjuncts --- successor-closedness and acyclicity of the induced subgraph --- come
  straight from the inner DFS, which is why no reachability argument (and hence no symmetry
  assumption) is needed here.\<close>
lemma invar_seed_holds_upd1[invar_holds_intros]:
  assumes "DFS_dircycle_linear_call_1_conds st" "invar_1 st" "invar_seed st"
  shows "invar_seed (DFS_dircycle_linear_upd1 st)"
proof -
  note ne = call_1_ne[OF assms(1)]
  have ncyc: "\<not> cycle_aux (dfs_aux (sel (V -\<^sub>G (fin st))) (fin st))"
    using assms(1) by (auto elim!: call_cond_elims)
  have fin': "fin (DFS_dircycle_linear_upd1 st) = fin_aux (dfs_aux (sel (V -\<^sub>G (fin st))) (fin st))"
    by (simp add: DFS_dircycle_linear_upd1_def Let_def)
  show ?thesis
    unfolding invar_seed_def seed_ok_def fin'
    using aux_spec(1)[OF ne assms(2,3)] aux_spec(3)[OF ne assms(2,3)]
    using aux_spec(4)[OF ne assms(2,3)] aux_spec(7)[OF ne assms(2,3) ncyc]
    by blast
qed

lemma invar_seed_holds_ret_1[invar_holds_intros]:
  "invar_seed st \<Longrightarrow> invar_seed (DFS_dircycle_linear_ret1 st)"
  by (auto simp: DFS_dircycle_linear_ret1_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_seed_holds_ret_2[invar_holds_intros]:
  "invar_seed st \<Longrightarrow> invar_seed (DFS_dircycle_linear_ret2 st)"
  by (auto simp: DFS_dircycle_linear_ret2_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_cyc_true_holds_upd1[invar_holds_intros]:
  "\<lbrakk>DFS_dircycle_linear_call_1_conds st; invar_cyc_true st\<rbrakk> \<Longrightarrow>
     invar_cyc_true (DFS_dircycle_linear_upd1 st)"
  by (auto simp: DFS_dircycle_linear_upd1_def Let_def
           elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_cyc_true_holds_ret_1[invar_holds_intros]:
  assumes "DFS_dircycle_linear_ret_1_conds st" "invar_1 st" "invar_seed st" "invar_cyc_true st"
  shows "invar_cyc_true (DFS_dircycle_linear_ret1 st)"
proof -
  have cyc: "cycle_aux (dfs_aux (sel (V -\<^sub>G (fin st))) (fin st))"
    using assms(1) by (auto elim!: call_cond_elims)
  show ?thesis
    using aux_spec(5)[OF ret_1_ne[OF assms(1)] assms(2,3) cyc]
    by (auto simp: DFS_dircycle_linear_ret1_def intro!: invar_props_intros)
qed

lemma invar_cyc_true_holds_ret_2[invar_holds_intros]:
  "invar_cyc_true st \<Longrightarrow> invar_cyc_true (DFS_dircycle_linear_ret2 st)"
  by (auto simp: DFS_dircycle_linear_ret2_def elim!: invar_props_elims intro!: invar_props_intros)

subsection \<open>Termination\<close>

definition "less_rel = {(x::nat, y::nat). x < y}"

lemma wf_less_rel[intro!]: "wf less_rel"
  by(auto simp: less_rel_def wf_less)

text \<open>The measure drops because the inner call \<^emph>\<open>absorbs its root\<close> (export 5): the root was
  unfinished before the call and finished after it, while nothing already finished is lost
  (export 4).\<close>
lemma call_1_terminates[termination_intros]:
  assumes "DFS_dircycle_linear_call_1_conds st" "invar_1 st" "invar_seed st"
  shows "(DFS_dircycle_linear_upd1 st, st) \<in> call_measure <*mlex*> r"
proof -
  let ?s = "sel (V -\<^sub>G (fin st))"
  let ?fs' = "fin_aux (dfs_aux ?s (fin st))"
  have ne: "V -\<^sub>G (fin st) \<noteq> \<emptyset>\<^sub>N" using assms(1) by (auto elim!: call_cond_elims)
  have ncyc: "\<not> cycle_aux (dfs_aux ?s (fin st))" using assms(1) by (auto elim!: call_cond_elims)
  have inv: "vset_inv (fin st)" using assms(2) by (auto elim!: invar_props_elims)
  have inv': "vset_inv ?fs'" using aux_spec(1)[OF ne assms(2,3)] .
  have grow: "t_set (fin st) \<subseteq> t_set ?fs'" using aux_spec(2)[OF ne assms(2,3)] .
  have snew: "?s \<in> t_set ?fs'" using aux_spec(6)[OF ne assms(2,3)] ncyc by blast
  have sold: "?s \<notin> t_set (fin st)" using sel_root(2)[OF ne assms(2)] .
  have sV: "?s \<in> t_set V" using sel_root(1)[OF ne assms(2)] V_graph_verts by blast
  have fin_sub: "t_set (V -\<^sub>G ?fs') \<subset> t_set (V -\<^sub>G fin st)"
  proof (rule psubsetI)
    show "t_set (V -\<^sub>G ?fs') \<subseteq> t_set (V -\<^sub>G fin st)"
      using grow inv inv' by auto
    have "?s \<in> t_set (V -\<^sub>G fin st)" using sV sold inv by simp
    moreover
    have "?s \<notin> t_set (V -\<^sub>G ?fs')" using snew inv' by simp
    ultimately
    show "t_set (V -\<^sub>G ?fs') \<noteq> t_set (V -\<^sub>G fin st)" by blast
  qed
  have "finite (t_set (V -\<^sub>G fin st))"
    using inv V_inv finite_vertices by (simp add: V_graph_verts)
  hence "card (t_set (V -\<^sub>G ?fs')) < card (t_set (V -\<^sub>G fin st))"
    using fin_sub by (rule psubset_card_mono)
  thus ?thesis
    by (auto simp: DFS_dircycle_linear_upd1_def Let_def call_measure_def intro!: mlex_less)
qed

lemma wf_term_rel: "wf DFS_dircycle_linear_term_rel'"
  by (auto simp: wf_mlex DFS_dircycle_linear_term_rel'_def)

lemma in_term_rel'[termination_intros]:
  "\<lbrakk>DFS_dircycle_linear_call_1_conds st; invar_1 st; invar_seed st\<rbrakk> \<Longrightarrow>
     (DFS_dircycle_linear_upd1 st, st) \<in> DFS_dircycle_linear_term_rel'"
  by (simp add: DFS_dircycle_linear_term_rel'_def termination_intros)

lemma DFS_dircycle_linear_terminates[termination_intros]:
  assumes "invar_1 st" "invar_seed st"
  shows "DFS_dircycle_linear_dom st"
  using wf_term_rel assms
proof(induction rule: wf_induct_rule)
  case (less x)
  show ?case
    by (rule DFS_dircycle_linear_domintros) (auto intro!: invar_holds_intros less in_term_rel')
qed

text \<open>The empty region trivially satisfies the seed contract: it is successor-closed vacuously, and
  the subgraph it induces has no vertices at all, hence no cycle.\<close>
lemma initial_state_props[invar_holds_intros, termination_intros]:
  shows "invar_1 initial_state"
    and "invar_seed initial_state"
    and "invar_cyc_true initial_state"
    and "DFS_dircycle_linear_dom initial_state"
proof -
  have empty: "t_set (fin initial_state) = {}" by (simp add: initial_state_def)
  show i1: "invar_1 initial_state" by (simp add: invar_1_def initial_state_def)
  have "Graph.digraph_abs G \<downharpoonright> t_set (fin initial_state) = {}"
    by (simp add: empty induce_subgraph_def)
  hence "\<nexists>c. Awalk_Defs.cycle (Graph.digraph_abs G \<downharpoonright> t_set (fin initial_state)) c"
    by (simp add: Awalk_Defs.cycle_def Awalk_Defs.awalk_def)
  hence isd: "invar_seed initial_state"
    unfolding invar_seed_def seed_ok_def
    by (simp add: empty initial_state_def)
  show "invar_seed initial_state" by (rule isd)
  show "invar_cyc_true initial_state" by (simp add: invar_cyc_true_def initial_state_def)
  show "DFS_dircycle_linear_dom initial_state"
    by (rule DFS_dircycle_linear_terminates[OF i1 isd])
qed

subsection \<open>Correctness\<close>

lemma invar_1_holds[invar_holds_intros]:
  assumes "DFS_dircycle_linear_dom st" "invar_1 st" "invar_seed st"
  shows "invar_1 (DFS_dircycle_linear st)"
  using assms(2-)
proof(induction rule: DFS_dircycle_linear_induct[OF assms(1)])
  case IH: (1 st)
  show ?case
    apply(rule DFS_dircycle_linear_cases[where st = st])
    by (auto intro!: IH(2-) invar_holds_intros simp: DFS_dircycle_linear_simps[OF IH(1)])
qed

lemma invar_seed_holds[invar_holds_intros]:
  assumes "DFS_dircycle_linear_dom st" "invar_1 st" "invar_seed st"
  shows "invar_seed (DFS_dircycle_linear st)"
  using assms(2-)
proof(induction rule: DFS_dircycle_linear_induct[OF assms(1)])
  case IH: (1 st)
  show ?case
    apply(rule DFS_dircycle_linear_cases[where st = st])
    by (auto intro!: IH(2-) invar_holds_intros simp: DFS_dircycle_linear_simps[OF IH(1)])
qed

lemma invar_cyc_true_holds[invar_holds_intros]:
  assumes "DFS_dircycle_linear_dom st" "invar_1 st" "invar_seed st" "invar_cyc_true st"
  shows "invar_cyc_true (DFS_dircycle_linear st)"
  using assms(2-)
proof(induction rule: DFS_dircycle_linear_induct[OF assms(1)])
  case IH: (1 st)
  show ?case
    apply(rule DFS_dircycle_linear_cases[where st = st])
    by (auto intro!: IH(2-) invar_holds_intros simp: DFS_dircycle_linear_simps[OF IH(1)])
qed

text \<open>On termination the loop has swept every vertex. The \<open>ret_1\<close> branch is impossible: it sets
  \<open>cyc\<close>, which the assumption rules out.\<close>
lemma ret_2_holds[ret_holds_intros]:
  assumes "DFS_dircycle_linear_dom st" "invar_1 st" "invar_seed st" "\<not> cyc (DFS_dircycle_linear st)"
  shows "DFS_dircycle_linear_ret_2_conds (DFS_dircycle_linear st)"
  using assms(2-)
proof(induction rule: DFS_dircycle_linear_induct[OF assms(1)])
  case IH: (1 st)
  show ?case
  proof(rule DFS_dircycle_linear_cases[where st = st], goal_cases)
    case 1
    then show ?case
      using IH(2)[OF 1 invar_1_holds_upd1[OF 1 IH(3,4)] invar_seed_holds_upd1[OF 1 IH(3,4)]]
      using IH(5)
      by (simp add: DFS_dircycle_linear_simps[OF IH(1)])
  next
    case 2
    then show ?case
      using IH(5)
      by (simp add: DFS_dircycle_linear_simps[OF IH(1)] DFS_dircycle_linear_ret1_def)
  next
    case 3
    then show ?case by (auto simp: DFS_dircycle_linear_simps[OF IH(1)] DFS_dircycle_linear_ret2_def)
  qed
qed

theorem DFS_dircycle_linear_sound:
  assumes "cyc (DFS_dircycle_linear initial_state)"
  shows "\<exists>c. Awalk_Defs.cycle (Graph.digraph_abs G) c"
  using invar_cyc_true_holds[OF initial_state_props(4) initial_state_props(1,2,3)] assms
  by (auto elim!: invar_props_elims)

text \<open>\<^bold>\<open>Completeness\<close>: no report means the \<^emph>\<open>whole\<close> graph is acyclic. At the return the loop has
  finished every vertex, so the region the seed contract certifies acyclic is all of \<open>dVs G\<close>, and
  \<open>G \<downharpoonright> dVs G\<close> is \<open>G\<close>. Contrast \<open>DFS_Cycles\<close>, which reaches the same conclusion through
  \<open>invar_seen\<close>'s mutual-unreachability argument; here it is immediate from successor-closedness.\<close>
theorem DFS_dircycle_linear_complete:
  assumes "\<not> cyc (DFS_dircycle_linear initial_state)"
  shows "\<nexists>c. Awalk_Defs.cycle (Graph.digraph_abs G) c"
proof -
  let ?r = "DFS_dircycle_linear initial_state"
  have dom: "DFS_dircycle_linear_dom initial_state" by (rule initial_state_props(4))
  have i1: "invar_1 ?r" by (intro invar_1_holds dom initial_state_props)
  have isd: "invar_seed ?r" by (intro invar_seed_holds dom initial_state_props)
  have "DFS_dircycle_linear_ret_2_conds ?r"
    by (intro ret_2_holds dom initial_state_props assms)
  hence empty: "V -\<^sub>G (fin ?r) = \<emptyset>\<^sub>N" by (auto elim!: call_cond_elims)
  have inv: "vset_inv (fin ?r)" using i1 by (auto elim!: invar_props_elims)
  have "t_set V \<subseteq> t_set (fin ?r)" using empty inv V_inv by force
  hence covers: "dVs (Graph.digraph_abs G) \<subseteq> t_set (fin ?r)" using V_graph_verts by blast
  have acyc: "\<nexists>c. Awalk_Defs.cycle (Graph.digraph_abs G \<downharpoonright> t_set (fin ?r)) c"
    using isd by (auto simp: invar_seed_def seed_ok_def)
  have "Graph.digraph_abs G \<downharpoonright> t_set (fin ?r) = Graph.digraph_abs G"
    using covers by (auto simp: induce_subgraph_def dVs_def)
  thus ?thesis using acyc by simp
qed

end

end

end
