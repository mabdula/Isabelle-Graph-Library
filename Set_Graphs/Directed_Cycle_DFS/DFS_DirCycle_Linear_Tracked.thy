theory DFS_DirCycle_Linear_Tracked
  imports DFS_DirCycle_Linear_Tracked_Aux
begin

text \<open>The whole-graph (linear) directed-cycle search of
  \<open>DFS_DirCycle_Linear\<close>, rebuilt on the \<^emph>\<open>tracked\<close> inner DFS of
  \<^theory>\<open>Directed_Cycle_DFS.DFS_DirCycle_Linear_Tracked_Aux\<close>. The algorithm is the same sweep --- pick a
  vertex the earlier calls have not finished, run a directed-cycle DFS seeded with the region they
  did finish, stop at the first report --- and the correctness argument is the same. The single
  difference is \<^emph>\<open>how the next root is found\<close>, and it is the whole point of the exercise:

  \<^item> \<open>DFS_DirCycle_Linear\<close> computes \<open>V -\<^sub>G fin st\<close>, an \<open>O(V)\<close> set difference against the full
    vertex set, \<^emph>\<open>twice\<close> per iteration (the emptiness test and the \<open>sel\<close>) and once more in each
    call condition. With one iteration per DFS tree that is \<open>O(V\<^sup>2)\<close> on top of the search itself.
  \<^item> Here the unfinished set is a \<^emph>\<open>state component\<close>: the inner DFS hands it back shrunk by
    exactly the vertices it finished (\<open>dircycle_tracked_unfinished_char\<close>), so the sweep tests
    \<open>sweep_unfin st \<noteq> \<emptyset>\<^sub>N\<close> and selects \<open>sel (sweep_unfin st)\<close> with no set difference at all.
    \<open>V\<close> is touched exactly once, to build the initial state.

  \<^bold>\<open>What that costs in the proof.\<close> One extra invariant, \<open>invar_part\<close>: the state's unfinished and
  finished sets partition \<open>dVs G\<close>. It replaces the definitional identity
  \<open>t_set (V -\<^sub>G fin st) = t_set V - t_set (fin st)\<close> that the \<open>_Linear\<close> version got for free from
  the set-operation simp rules, and it is re-established at each step by the inner DFS's exports 8--9
  --- which is why those exports exist. Everything downstream is then \<^emph>\<open>simpler\<close> than in
  \<open>_Linear\<close>: the termination measure is \<open>card (t_set (sweep_unfin st))\<close> directly, and completeness
  reads \<open>t_set (sweep_fin st) = dVs G\<close> off the partition at the return instead of arguing from an
  empty difference.

  The seed contract \<open>seed_ok\<close> and the inner-DFS contract \<open>dfs_aux_axioms\<close> are those of
  \<open>DFS_DirCycle_Linear\<close>, with \<open>dfs_aux\<close> taking the unfinished set as a third
  argument and returning one, and with the extra conjunct \<open>part_ok\<close> on the result. All nine
  conjuncts are discharged for the concrete tracked DFS by the exports at the end of
  \<^theory>\<open>Directed_Cycle_DFS.DFS_DirCycle_Linear_Tracked_Aux\<close>.

  (\<open>DFS_DirCycle_Linear\<close> is a sibling, not an ancestor --- the two sweeps share no theory ---
  so it is named in prose here rather than as a \<open>\<^theory>\<close> reference.)\<close>

text \<open>\<^theory>\<open>Directed_Cycle_DFS.DFS_Skel_More\<close> declares \<open>termination_intros\<close> \<^emph>\<open>inside\<close>
  \<^locale>\<open>DFS_skel_more_thms\<close> (as \<open>DFS_Cycles\<close> does in the library), which scopes the attribute to
  that locale; at theory level it is undeclared. So, exactly as in \<open>DFS_DirCycle_Linear\<close>, the outer
  loop --- which is where termination is argued --- has to introduce it.\<close>
named_theorems termination_intros

record ('ver, 'vset) DFS_DirCycle_Tracked_state =
  sweep_fin   :: "'vset"
  sweep_unfin :: "'vset"
  sweep_cyc   :: bool

locale DFS_DirCycle_Tracked =
  Graph: Pair_Graph_Specs where lookup = lookup +
  set_ops: Set2 vset_empty vset_delete _ t_set vset_inv insert
for lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option" +
fixes G::"'adjmap" and V::"'vset"
  and dfs_aux::"'v \<Rightarrow> 'vset \<Rightarrow> 'vset \<Rightarrow> 'state"
  and fin_aux::"'state \<Rightarrow> 'vset" and unfin_aux::"'state \<Rightarrow> 'vset"
  and cycle_aux::"'state \<Rightarrow> bool"
begin

abbreviation "neighbourhood' \<equiv> Graph.neighbourhood G"
notation "neighbourhood'" ("\<N>\<^sub>G _" 100)

text \<open>As in \<open>DFS_DirCycle_Linear\<close>: a genuinely directed graph, no symmetry and no loop-freeness.
  \<open>V\<close> is still fixed, but only the initial state reads it.\<close>
definition "DFS_DirCycle_Tracked_axioms = (
  Graph.graph_inv G \<and> Graph.finite_graph G \<and> Graph.finite_vsets G \<and>
  vset_inv V \<and> (t_set V = dVs (Graph.digraph_abs G)))"

text \<open>The seed contract --- what the accumulated finished region must satisfy for the next inner
  call to be legitimate. Verbatim the \<open>f\<close>-part of \<open>DFS_dircycle_tracked_axioms\<close>.\<close>
definition "seed_ok fs \<longleftrightarrow>
  vset_inv fs \<and> t_set fs \<subseteq> dVs (Graph.digraph_abs G)
  \<and> (\<forall>u w. u \<in> t_set fs \<longrightarrow> (u, w) \<in> Graph.digraph_abs G \<longrightarrow> w \<in> t_set fs)
  \<and> (\<nexists>c. Awalk_Defs.cycle (Graph.digraph_abs G \<downharpoonright> t_set fs) c)"

text \<open>The partition contract on the pair (finished, unfinished) --- verbatim the \<open>uf\<close>-part of
  \<open>DFS_dircycle_tracked_axioms\<close>, and the state invariant that stands in for the set difference
  the \<open>_Linear\<close> sweep recomputes.\<close>
definition "part_ok fs us \<longleftrightarrow>
  vset_inv us \<and> t_set us \<union> t_set fs = dVs (Graph.digraph_abs G)
  \<and> t_set us \<inter> t_set fs = {}"

text \<open>What the inner DFS must deliver. The first six conjuncts are those of
  \<open>DFS_DirCycle_Linear.dfs_aux_axioms\<close>, discharged by exports 1--7 of
  \<^theory>\<open>Directed_Cycle_DFS.DFS_DirCycle_Linear_Tracked_Aux\<close> (\<open>dircycle_tracked_finished_inv\<close>,
  \<open>_seed_subset\<close>, \<open>_finished_subset_dVs\<close>, \<open>_finished_closed\<close>,
  \<open>DFS_dircycle_tracked_sound\<close>, \<open>_root_finished\<close>, \<open>DFS_dircycle_tracked_complete\<close>). The last is
  new: the returned unfinished set again partitions the vertex set with the returned finished
  region, discharged by exports 8--9 (\<open>dircycle_tracked_unfinished_inv\<close>,
  \<open>dircycle_tracked_unfinished_char\<close>).\<close>
definition "dfs_aux_axioms = (
  \<forall>s \<in> dVs (Graph.digraph_abs G). \<forall>fs us. seed_ok fs \<longrightarrow> s \<notin> t_set fs \<longrightarrow> part_ok fs us \<longrightarrow>
    (vset_inv (fin_aux (dfs_aux s fs us))
     \<and> t_set fs \<subseteq> t_set (fin_aux (dfs_aux s fs us))
     \<and> t_set (fin_aux (dfs_aux s fs us)) \<subseteq> dVs (Graph.digraph_abs G)
     \<and> (\<forall>u w. u \<in> t_set (fin_aux (dfs_aux s fs us)) \<longrightarrow> (u, w) \<in> Graph.digraph_abs G \<longrightarrow>
          w \<in> t_set (fin_aux (dfs_aux s fs us)))
     \<and> (cycle_aux (dfs_aux s fs us) \<longrightarrow> (\<exists>c. Awalk_Defs.cycle (Graph.digraph_abs G) c))
     \<and> (\<not> cycle_aux (dfs_aux s fs us) \<longrightarrow>
          s \<in> t_set (fin_aux (dfs_aux s fs us))
          \<and> (\<nexists>c. Awalk_Defs.cycle
                    (Graph.digraph_abs G \<downharpoonright> t_set (fin_aux (dfs_aux s fs us))) c))
     \<and> part_ok (fin_aux (dfs_aux s fs us)) (unfin_aux (dfs_aux s fs us))))"

function (domintros) DFS_DirCycle_Tracked::
  "('v, 'vset) DFS_DirCycle_Tracked_state \<Rightarrow> ('v, 'vset) DFS_DirCycle_Tracked_state" where
  "DFS_DirCycle_Tracked st =
    (if sweep_unfin st \<noteq> \<emptyset>\<^sub>N
     then
      (let
        s = sel (sweep_unfin st);
        aux = dfs_aux s (sweep_fin st) (sweep_unfin st)
      in
        (if cycle_aux aux
         then st \<lparr>sweep_cyc := True\<rparr>
         else DFS_DirCycle_Tracked
                (st \<lparr>sweep_fin := fin_aux aux, sweep_unfin := unfin_aux aux\<rparr>)))
     else st)"
  by pat_completeness auto

partial_function (tailrec) DFS_DirCycle_Tracked_impl::
  "('v, 'vset) DFS_DirCycle_Tracked_state \<Rightarrow> ('v, 'vset) DFS_DirCycle_Tracked_state" where
  "DFS_DirCycle_Tracked_impl st =
    (if sweep_unfin st \<noteq> \<emptyset>\<^sub>N
     then
      (let
        s = sel (sweep_unfin st);
        aux = dfs_aux s (sweep_fin st) (sweep_unfin st)
      in
        (if cycle_aux aux
         then st \<lparr>sweep_cyc := True\<rparr>
         else DFS_DirCycle_Tracked_impl
                (st \<lparr>sweep_fin := fin_aux aux, sweep_unfin := unfin_aux aux\<rparr>)))
     else st)"

lemmas [code] = DFS_DirCycle_Tracked_impl.simps

lemma DFS_DirCycle_Tracked_impl_same:
  assumes "DFS_DirCycle_Tracked_dom st"
  shows "DFS_DirCycle_Tracked_impl st = DFS_DirCycle_Tracked st"
  by(induction rule: DFS_DirCycle_Tracked.pinduct[OF assms])
    (subst DFS_DirCycle_Tracked.psimps, simp, subst DFS_DirCycle_Tracked_impl.simps,
     auto split: if_split simp add: Let_def)

subsection \<open>Call conditions\<close>

definition "DFS_DirCycle_Tracked_call_1_conds st =
    (if sweep_unfin st \<noteq> \<emptyset>\<^sub>N
     then (if cycle_aux (dfs_aux (sel (sweep_unfin st)) (sweep_fin st) (sweep_unfin st))
           then False else True)
     else False)"

lemma DFS_DirCycle_Tracked_call_1_conds[call_cond_elims]:
  "DFS_DirCycle_Tracked_call_1_conds st \<Longrightarrow>
   \<lbrakk>\<lbrakk>sweep_unfin st \<noteq> \<emptyset>\<^sub>N;
     \<not> cycle_aux (dfs_aux (sel (sweep_unfin st)) (sweep_fin st) (sweep_unfin st))\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto simp: DFS_DirCycle_Tracked_call_1_conds_def split: if_splits)

definition "DFS_DirCycle_Tracked_upd1 st =
    (let
      s = sel (sweep_unfin st);
      aux = dfs_aux s (sweep_fin st) (sweep_unfin st)
    in
      (st \<lparr>sweep_fin := fin_aux aux, sweep_unfin := unfin_aux aux\<rparr>))"

definition "DFS_DirCycle_Tracked_ret_1_conds st =
    (if sweep_unfin st \<noteq> \<emptyset>\<^sub>N
     then (if cycle_aux (dfs_aux (sel (sweep_unfin st)) (sweep_fin st) (sweep_unfin st))
           then True else False)
     else False)"

lemma DFS_DirCycle_Tracked_ret_1_conds[call_cond_elims]:
  "DFS_DirCycle_Tracked_ret_1_conds st \<Longrightarrow>
   \<lbrakk>\<lbrakk>sweep_unfin st \<noteq> \<emptyset>\<^sub>N;
     cycle_aux (dfs_aux (sel (sweep_unfin st)) (sweep_fin st) (sweep_unfin st))\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto simp: DFS_DirCycle_Tracked_ret_1_conds_def split: if_splits)

lemma DFS_DirCycle_Tracked_ret_1_condsI[call_cond_intros]:
  "\<lbrakk>sweep_unfin st \<noteq> \<emptyset>\<^sub>N;
    cycle_aux (dfs_aux (sel (sweep_unfin st)) (sweep_fin st) (sweep_unfin st))\<rbrakk> \<Longrightarrow>
    DFS_DirCycle_Tracked_ret_1_conds st"
  by(auto simp: DFS_DirCycle_Tracked_ret_1_conds_def split: if_splits)

definition "DFS_DirCycle_Tracked_ret1 st = (st \<lparr>sweep_cyc := True\<rparr>)"

definition "DFS_DirCycle_Tracked_ret_2_conds st =
    (if sweep_unfin st \<noteq> \<emptyset>\<^sub>N then False else True)"

lemma DFS_DirCycle_Tracked_ret_2_conds[call_cond_elims]:
  "DFS_DirCycle_Tracked_ret_2_conds st \<Longrightarrow> \<lbrakk>sweep_unfin st = \<emptyset>\<^sub>N \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto simp: DFS_DirCycle_Tracked_ret_2_conds_def split: if_splits)

lemma DFS_DirCycle_Tracked_ret_2_condsI[call_cond_intros]:
  "sweep_unfin st = \<emptyset>\<^sub>N \<Longrightarrow> DFS_DirCycle_Tracked_ret_2_conds st"
  by(auto simp: DFS_DirCycle_Tracked_ret_2_conds_def split: if_splits)

definition "DFS_DirCycle_Tracked_ret2 st = st"

lemma DFS_DirCycle_Tracked_cases:
  assumes "DFS_DirCycle_Tracked_call_1_conds st \<Longrightarrow> P"
      "DFS_DirCycle_Tracked_ret_1_conds st \<Longrightarrow> P"
      "DFS_DirCycle_Tracked_ret_2_conds st \<Longrightarrow> P"
  shows "P"
proof-
  have "DFS_DirCycle_Tracked_call_1_conds st \<or>
        DFS_DirCycle_Tracked_ret_1_conds st \<or> DFS_DirCycle_Tracked_ret_2_conds st"
    by (auto simp add: DFS_DirCycle_Tracked_call_1_conds_def
                       DFS_DirCycle_Tracked_ret_1_conds_def DFS_DirCycle_Tracked_ret_2_conds_def
           split: list.split_asm option.split_asm if_splits)
  then show ?thesis using assms by auto
qed

lemma DFS_DirCycle_Tracked_simps:
  assumes "DFS_DirCycle_Tracked_dom st"
  shows "DFS_DirCycle_Tracked_call_1_conds st \<Longrightarrow>
           DFS_DirCycle_Tracked st = DFS_DirCycle_Tracked (DFS_DirCycle_Tracked_upd1 st)"
        "DFS_DirCycle_Tracked_ret_1_conds st \<Longrightarrow>
           DFS_DirCycle_Tracked st = DFS_DirCycle_Tracked_ret1 st"
        "DFS_DirCycle_Tracked_ret_2_conds st \<Longrightarrow>
           DFS_DirCycle_Tracked st = DFS_DirCycle_Tracked_ret2 st"
  by (auto simp add: DFS_DirCycle_Tracked.psimps[OF assms] Let_def
                     DFS_DirCycle_Tracked_call_1_conds_def DFS_DirCycle_Tracked_upd1_def
                     DFS_DirCycle_Tracked_ret_1_conds_def DFS_DirCycle_Tracked_ret1_def
                     DFS_DirCycle_Tracked_ret_2_conds_def DFS_DirCycle_Tracked_ret2_def
            split: list.splits option.splits if_splits)

lemma DFS_DirCycle_Tracked_induct:
  assumes "DFS_DirCycle_Tracked_dom st"
  assumes "\<And>st. \<lbrakk>DFS_DirCycle_Tracked_dom st;
     DFS_DirCycle_Tracked_call_1_conds st \<Longrightarrow> P (DFS_DirCycle_Tracked_upd1 st)\<rbrakk> \<Longrightarrow> P st"
  shows "P st"
  apply(rule DFS_DirCycle_Tracked.pinduct[OF assms(1)])
  apply(rule assms(2)[simplified DFS_DirCycle_Tracked_call_1_conds_def
                                 DFS_DirCycle_Tracked_upd1_def])
  by (auto simp: Let_def split: list.splits option.splits if_splits)

lemma DFS_DirCycle_Tracked_domintros:
  assumes "DFS_DirCycle_Tracked_call_1_conds st \<Longrightarrow>
             DFS_DirCycle_Tracked_dom (DFS_DirCycle_Tracked_upd1 st)"
  shows "DFS_DirCycle_Tracked_dom st"
proof(rule DFS_DirCycle_Tracked.domintros, goal_cases)
  case 1
  then show ?case
    using assms(1)[simplified DFS_DirCycle_Tracked_call_1_conds_def DFS_DirCycle_Tracked_upd1_def]
    by (force simp: Let_def split: list.splits option.splits if_splits)
qed

text \<open>The measure is the unfinished set itself --- no difference to compute, neither in the
  algorithm nor in the proof.\<close>
definition "call_measure st = card (t_set (sweep_unfin st))"
definition "DFS_DirCycle_Tracked_term_rel' = call_measure <*mlex*> {}"

text \<open>The one place \<open>V\<close> is read: nothing is finished yet, so everything is unfinished.\<close>
definition "initial_state = \<lparr>sweep_fin = \<emptyset>\<^sub>N, sweep_unfin = V, sweep_cyc = False\<rparr>"
lemmas [code] = initial_state_def

subsection \<open>Invariants\<close>

definition "invar_1 st = vset_inv (sweep_fin st)"
definition "invar_part st = part_ok (sweep_fin st) (sweep_unfin st)"
definition "invar_seed st = seed_ok (sweep_fin st)"
definition "invar_cyc_true st = (sweep_cyc st \<longrightarrow> (\<exists>c. Awalk_Defs.cycle (Graph.digraph_abs G) c))"

end

locale DFS_DirCycle_Tracked_thms = DFS_DirCycle_Tracked +
  assumes graph_axioms: DFS_DirCycle_Tracked_axioms
      and aux_axioms: dfs_aux_axioms
begin

context
includes Graph.adjmap.automation and Graph.vset.set.automation
begin

text \<open>As in \<open>DFS_Cycles\<close> and \<open>DFS_DirCycle_Linear\<close>: without the set-operation equations the
  automation cannot reduce the vset operations and every \<open>force\<close>/\<open>auto\<close> over them searches
  unboundedly instead of failing.\<close>
declare set_ops.set_union[simp] set_ops.set_inter[simp]
        set_ops.set_diff[simp] set_ops.invar_union[simp]
        set_ops.invar_inter[simp] set_ops.invar_diff[simp]

lemma V_graph_verts: "t_set V = dVs (Graph.digraph_abs G)"
  using graph_axioms by (auto simp: DFS_DirCycle_Tracked_axioms_def)

lemma V_inv[simp, intro]: "vset_inv V"
  using graph_axioms by (auto simp: DFS_DirCycle_Tracked_axioms_def)

lemma graph_inv[simp, intro]:
  "Graph.graph_inv G"
  "Graph.finite_graph G"
  "Graph.finite_vsets G"
  using graph_axioms by (auto simp: DFS_DirCycle_Tracked_axioms_def)

lemma finite_vertices[simp, intro]: "finite (dVs (Graph.digraph_abs G))"
  using Graph.finite_vertices[OF graph_inv(1,2,3)] .

lemma invar_1_props[invar_props_elims]:
  "invar_1 st \<Longrightarrow> (vset_inv (sweep_fin st) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_1_def)

lemma invar_1_intro[invar_props_intros]: "vset_inv (sweep_fin st) \<Longrightarrow> invar_1 st"
  by (auto simp: invar_1_def)

lemma invar_part_props[invar_props_elims]:
  "invar_part st \<Longrightarrow>
   (\<lbrakk>vset_inv (sweep_unfin st);
     t_set (sweep_unfin st) \<union> t_set (sweep_fin st) = dVs (Graph.digraph_abs G);
     t_set (sweep_unfin st) \<inter> t_set (sweep_fin st) = {}\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_part_def part_ok_def)

lemma invar_part_intro[invar_props_intros]:
  "part_ok (sweep_fin st) (sweep_unfin st) \<Longrightarrow> invar_part st"
  by (auto simp: invar_part_def)

lemma invar_seed_props[invar_props_elims]:
  "invar_seed st \<Longrightarrow> (seed_ok (sweep_fin st) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_seed_def)

lemma invar_seed_intro[invar_props_intros]: "seed_ok (sweep_fin st) \<Longrightarrow> invar_seed st"
  by (auto simp: invar_seed_def)

lemma invar_cyc_true_props[invar_props_elims]:
  "invar_cyc_true st \<Longrightarrow>
   ((sweep_cyc st \<Longrightarrow> \<exists>c. Awalk_Defs.cycle (Graph.digraph_abs G) c) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_cyc_true_def)

lemma invar_cyc_true_intro[invar_props_intros]:
  "(sweep_cyc st \<Longrightarrow> \<exists>c. Awalk_Defs.cycle (Graph.digraph_abs G) c) \<Longrightarrow> invar_cyc_true st"
  by (auto simp: invar_cyc_true_def)

text \<open>The selected root is a graph vertex outside the finished region --- read straight off the
  partition, where the \<open>_Linear\<close> version had to unfold a set difference.\<close>
lemma sel_mem:
  assumes "sweep_unfin st \<noteq> \<emptyset>\<^sub>N" and "invar_part st"
  shows "sel (sweep_unfin st) \<in> t_set (sweep_unfin st)"
  using assms by (force elim!: invar_props_elims)

lemma sel_root:
  assumes "sweep_unfin st \<noteq> \<emptyset>\<^sub>N" and "invar_part st"
  shows "sel (sweep_unfin st) \<in> dVs (Graph.digraph_abs G)"
    and "sel (sweep_unfin st) \<notin> t_set (sweep_fin st)"
  using sel_mem[OF assms] assms(2)
  by (force elim!: invar_props_elims, force elim!: invar_props_elims)

text \<open>The inner call's guarantees, instantiated at the selected root.\<close>
lemma aux_spec:
  assumes "sweep_unfin st \<noteq> \<emptyset>\<^sub>N" and "invar_part st" and "invar_seed st"
  shows "vset_inv (fin_aux (dfs_aux (sel (sweep_unfin st)) (sweep_fin st) (sweep_unfin st)))"
    and "t_set (sweep_fin st)
           \<subseteq> t_set (fin_aux (dfs_aux (sel (sweep_unfin st)) (sweep_fin st) (sweep_unfin st)))"
    and "t_set (fin_aux (dfs_aux (sel (sweep_unfin st)) (sweep_fin st) (sweep_unfin st)))
           \<subseteq> dVs (Graph.digraph_abs G)"
    and "\<And>u w. u \<in> t_set (fin_aux (dfs_aux (sel (sweep_unfin st)) (sweep_fin st)
                                            (sweep_unfin st))) \<Longrightarrow>
           (u, w) \<in> Graph.digraph_abs G \<Longrightarrow>
           w \<in> t_set (fin_aux (dfs_aux (sel (sweep_unfin st)) (sweep_fin st) (sweep_unfin st)))"
    and "cycle_aux (dfs_aux (sel (sweep_unfin st)) (sweep_fin st) (sweep_unfin st)) \<Longrightarrow>
           \<exists>c. Awalk_Defs.cycle (Graph.digraph_abs G) c"
    and "\<not> cycle_aux (dfs_aux (sel (sweep_unfin st)) (sweep_fin st) (sweep_unfin st)) \<Longrightarrow>
           sel (sweep_unfin st)
             \<in> t_set (fin_aux (dfs_aux (sel (sweep_unfin st)) (sweep_fin st) (sweep_unfin st)))"
    and "\<not> cycle_aux (dfs_aux (sel (sweep_unfin st)) (sweep_fin st) (sweep_unfin st)) \<Longrightarrow>
           \<nexists>c. Awalk_Defs.cycle
                 (Graph.digraph_abs G \<downharpoonright>
                    t_set (fin_aux (dfs_aux (sel (sweep_unfin st)) (sweep_fin st)
                                            (sweep_unfin st)))) c"
    and "part_ok (fin_aux (dfs_aux (sel (sweep_unfin st)) (sweep_fin st) (sweep_unfin st)))
                 (unfin_aux (dfs_aux (sel (sweep_unfin st)) (sweep_fin st) (sweep_unfin st)))"
  using aux_axioms[unfolded dfs_aux_axioms_def, rule_format,
                   OF sel_root(1)[OF assms(1,2)] assms(3)[unfolded invar_seed_def]
                      sel_root(2)[OF assms(1,2)] assms(2)[unfolded invar_part_def]]
  by auto

subsection \<open>Invariant preservation\<close>

lemma call_1_ne:
  assumes "DFS_DirCycle_Tracked_call_1_conds st"
  shows "sweep_unfin st \<noteq> \<emptyset>\<^sub>N"
  using assms by (auto elim!: call_cond_elims)

lemma ret_1_ne:
  assumes "DFS_DirCycle_Tracked_ret_1_conds st"
  shows "sweep_unfin st \<noteq> \<emptyset>\<^sub>N"
  using assms by (auto elim!: call_cond_elims)

lemma upd1_unfold:
  "sweep_fin (DFS_DirCycle_Tracked_upd1 st)
     = fin_aux (dfs_aux (sel (sweep_unfin st)) (sweep_fin st) (sweep_unfin st))"
  "sweep_unfin (DFS_DirCycle_Tracked_upd1 st)
     = unfin_aux (dfs_aux (sel (sweep_unfin st)) (sweep_fin st) (sweep_unfin st))"
  "sweep_cyc (DFS_DirCycle_Tracked_upd1 st) = sweep_cyc st"
  by (simp_all add: DFS_DirCycle_Tracked_upd1_def Let_def)

lemma invar_1_holds_upd1[invar_holds_intros]:
  assumes "DFS_DirCycle_Tracked_call_1_conds st" "invar_1 st" "invar_part st" "invar_seed st"
  shows "invar_1 (DFS_DirCycle_Tracked_upd1 st)"
  using aux_spec(1)[OF call_1_ne[OF assms(1)] assms(3,4)]
  by (auto simp: upd1_unfold intro!: invar_props_intros)

lemma invar_1_holds_ret_1[invar_holds_intros]:
  "invar_1 st \<Longrightarrow> invar_1 (DFS_DirCycle_Tracked_ret1 st)"
  by (auto simp: DFS_DirCycle_Tracked_ret1_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_1_holds_ret_2[invar_holds_intros]:
  "invar_1 st \<Longrightarrow> invar_1 (DFS_DirCycle_Tracked_ret2 st)"
  by (auto simp: DFS_DirCycle_Tracked_ret2_def elim!: invar_props_elims intro!: invar_props_intros)

text \<open>The invariant that replaces the \<open>_Linear\<close> sweep's set difference: it is re-established
  wholesale by the inner DFS's export 8--9, with nothing for the outer loop to recompute.\<close>
lemma invar_part_holds_upd1[invar_holds_intros]:
  assumes "DFS_DirCycle_Tracked_call_1_conds st" "invar_1 st" "invar_part st" "invar_seed st"
  shows "invar_part (DFS_DirCycle_Tracked_upd1 st)"
  using aux_spec(8)[OF call_1_ne[OF assms(1)] assms(3,4)]
  by (auto simp: upd1_unfold intro!: invar_props_intros)

lemma invar_part_holds_ret_1[invar_holds_intros]:
  "invar_part st \<Longrightarrow> invar_part (DFS_DirCycle_Tracked_ret1 st)"
  by (auto simp: DFS_DirCycle_Tracked_ret1_def invar_part_def)

lemma invar_part_holds_ret_2[invar_holds_intros]:
  "invar_part st \<Longrightarrow> invar_part (DFS_DirCycle_Tracked_ret2 st)"
  by (auto simp: DFS_DirCycle_Tracked_ret2_def invar_part_def)

text \<open>The heart of the outer loop, unchanged from \<open>DFS_DirCycle_Linear\<close>: the enlarged region
  again satisfies the seed contract, both interesting conjuncts coming straight from the inner
  DFS.\<close>
lemma invar_seed_holds_upd1[invar_holds_intros]:
  assumes "DFS_DirCycle_Tracked_call_1_conds st" "invar_1 st" "invar_part st" "invar_seed st"
  shows "invar_seed (DFS_DirCycle_Tracked_upd1 st)"
proof -
  note ne = call_1_ne[OF assms(1)]
  have ncyc: "\<not> cycle_aux (dfs_aux (sel (sweep_unfin st)) (sweep_fin st) (sweep_unfin st))"
    using assms(1) by (auto elim!: call_cond_elims)
  show ?thesis
    unfolding invar_seed_def seed_ok_def upd1_unfold
    using aux_spec(1)[OF ne assms(3,4)] aux_spec(3)[OF ne assms(3,4)]
    using aux_spec(4)[OF ne assms(3,4)] aux_spec(7)[OF ne assms(3,4) ncyc]
    by blast
qed

lemma invar_seed_holds_ret_1[invar_holds_intros]:
  "invar_seed st \<Longrightarrow> invar_seed (DFS_DirCycle_Tracked_ret1 st)"
  by (auto simp: DFS_DirCycle_Tracked_ret1_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_seed_holds_ret_2[invar_holds_intros]:
  "invar_seed st \<Longrightarrow> invar_seed (DFS_DirCycle_Tracked_ret2 st)"
  by (auto simp: DFS_DirCycle_Tracked_ret2_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_cyc_true_holds_upd1[invar_holds_intros]:
  "\<lbrakk>DFS_DirCycle_Tracked_call_1_conds st; invar_cyc_true st\<rbrakk> \<Longrightarrow>
     invar_cyc_true (DFS_DirCycle_Tracked_upd1 st)"
  by (auto simp: upd1_unfold elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_cyc_true_holds_ret_1[invar_holds_intros]:
  assumes "DFS_DirCycle_Tracked_ret_1_conds st" "invar_1 st" "invar_part st" "invar_seed st"
      and "invar_cyc_true st"
  shows "invar_cyc_true (DFS_DirCycle_Tracked_ret1 st)"
proof -
  have cyc: "cycle_aux (dfs_aux (sel (sweep_unfin st)) (sweep_fin st) (sweep_unfin st))"
    using assms(1) by (auto elim!: call_cond_elims)
  show ?thesis
    using aux_spec(5)[OF ret_1_ne[OF assms(1)] assms(3,4) cyc]
    by (auto simp: DFS_DirCycle_Tracked_ret1_def intro!: invar_props_intros)
qed

lemma invar_cyc_true_holds_ret_2[invar_holds_intros]:
  "invar_cyc_true st \<Longrightarrow> invar_cyc_true (DFS_DirCycle_Tracked_ret2 st)"
  by (auto simp: DFS_DirCycle_Tracked_ret2_def elim!: invar_props_elims intro!: invar_props_intros)

subsection \<open>Termination\<close>

definition "less_rel = {(x::nat, y::nat). x < y}"

lemma wf_less_rel[intro!]: "wf less_rel"
  by(auto simp: less_rel_def wf_less)

text \<open>The measure drops because the inner call \<^emph>\<open>absorbs its root\<close> (export 5) while the finished
  region only grows (export 4) --- and by the partition the unfinished set is the exact complement
  of the finished one, so both facts transfer to it directly.\<close>
lemma call_1_terminates[termination_intros]:
  assumes "DFS_DirCycle_Tracked_call_1_conds st" "invar_1 st" "invar_part st" "invar_seed st"
  shows "(DFS_DirCycle_Tracked_upd1 st, st) \<in> call_measure <*mlex*> r"
proof -
  let ?s = "sel (sweep_unfin st)"
  let ?a = "dfs_aux ?s (sweep_fin st) (sweep_unfin st)"
  have ne: "sweep_unfin st \<noteq> \<emptyset>\<^sub>N" using assms(1) by (auto elim!: call_cond_elims)
  have ncyc: "\<not> cycle_aux ?a" using assms(1) by (auto elim!: call_cond_elims)
  have grow: "t_set (sweep_fin st) \<subseteq> t_set (fin_aux ?a)" using aux_spec(2)[OF ne assms(3,4)] .
  have snew: "?s \<in> t_set (fin_aux ?a)" using aux_spec(6)[OF ne assms(3,4)] ncyc by blast
  have part': "part_ok (fin_aux ?a) (unfin_aux ?a)" using aux_spec(8)[OF ne assms(3,4)] .
  have unfin': "t_set (unfin_aux ?a) = dVs (Graph.digraph_abs G) - t_set (fin_aux ?a)"
    using part' by (auto simp: part_ok_def)
  have unfin: "t_set (sweep_unfin st) = dVs (Graph.digraph_abs G) - t_set (sweep_fin st)"
    using assms(3) by (auto elim!: invar_props_elims)
  have sub: "t_set (unfin_aux ?a) \<subset> t_set (sweep_unfin st)"
  proof (rule psubsetI)
    show "t_set (unfin_aux ?a) \<subseteq> t_set (sweep_unfin st)" using unfin unfin' grow by blast
    have "?s \<in> t_set (sweep_unfin st)" by (rule sel_mem[OF ne assms(3)])
    moreover
    have "?s \<notin> t_set (unfin_aux ?a)" using snew unfin' by blast
    ultimately
    show "t_set (unfin_aux ?a) \<noteq> t_set (sweep_unfin st)" by blast
  qed
  have "finite (t_set (sweep_unfin st))" using unfin finite_vertices by simp
  hence "card (t_set (unfin_aux ?a)) < card (t_set (sweep_unfin st))"
    using sub by (rule psubset_card_mono)
  thus ?thesis
    by (auto simp: upd1_unfold call_measure_def intro!: mlex_less)
qed

lemma wf_term_rel: "wf DFS_DirCycle_Tracked_term_rel'"
  by (auto simp: wf_mlex DFS_DirCycle_Tracked_term_rel'_def)

lemma in_term_rel'[termination_intros]:
  "\<lbrakk>DFS_DirCycle_Tracked_call_1_conds st; invar_1 st; invar_part st; invar_seed st\<rbrakk> \<Longrightarrow>
     (DFS_DirCycle_Tracked_upd1 st, st) \<in> DFS_DirCycle_Tracked_term_rel'"
  by (simp add: DFS_DirCycle_Tracked_term_rel'_def termination_intros)

lemma DFS_DirCycle_Tracked_terminates[termination_intros]:
  assumes "invar_1 st" "invar_part st" "invar_seed st"
  shows "DFS_DirCycle_Tracked_dom st"
  using wf_term_rel assms
proof(induction rule: wf_induct_rule)
  case (less x)
  show ?case
    by (rule DFS_DirCycle_Tracked_domintros) (auto intro!: invar_holds_intros less in_term_rel')
qed

text \<open>The empty region trivially satisfies the seed contract, and \<open>V\<close> --- the whole vertex set ---
  is its complement, so the partition holds at the start.\<close>
lemma initial_state_props[invar_holds_intros, termination_intros]:
  shows "invar_1 initial_state"
    and "invar_part initial_state"
    and "invar_seed initial_state"
    and "invar_cyc_true initial_state"
    and "DFS_DirCycle_Tracked_dom initial_state"
proof -
  have empty: "t_set (sweep_fin initial_state) = {}" by (simp add: initial_state_def)
  show i1: "invar_1 initial_state" by (simp add: invar_1_def initial_state_def)
  show ip: "invar_part initial_state"
    by (simp add: invar_part_def part_ok_def initial_state_def V_graph_verts)
  have "Graph.digraph_abs G \<downharpoonright> t_set (sweep_fin initial_state) = {}"
    by (simp add: empty induce_subgraph_def)
  hence "\<nexists>c. Awalk_Defs.cycle (Graph.digraph_abs G \<downharpoonright> t_set (sweep_fin initial_state)) c"
    by (simp add: Awalk_Defs.cycle_def Awalk_Defs.awalk_def)
  hence isd: "invar_seed initial_state"
    unfolding invar_seed_def seed_ok_def
    by (simp add: empty initial_state_def)
  show "invar_seed initial_state" by (rule isd)
  show "invar_cyc_true initial_state" by (simp add: invar_cyc_true_def initial_state_def)
  show "DFS_DirCycle_Tracked_dom initial_state"
    by (rule DFS_DirCycle_Tracked_terminates[OF i1 ip isd])
qed

subsection \<open>Correctness\<close>

lemma invar_1_holds[invar_holds_intros]:
  assumes "DFS_DirCycle_Tracked_dom st" "invar_1 st" "invar_part st" "invar_seed st"
  shows "invar_1 (DFS_DirCycle_Tracked st)"
  using assms(2-)
proof(induction rule: DFS_DirCycle_Tracked_induct[OF assms(1)])
  case IH: (1 st)
  show ?case
    apply(rule DFS_DirCycle_Tracked_cases[where st = st])
    by (auto intro!: IH(2-) invar_holds_intros simp: DFS_DirCycle_Tracked_simps[OF IH(1)])
qed

lemma invar_part_holds[invar_holds_intros]:
  assumes "DFS_DirCycle_Tracked_dom st" "invar_1 st" "invar_part st" "invar_seed st"
  shows "invar_part (DFS_DirCycle_Tracked st)"
  using assms(2-)
proof(induction rule: DFS_DirCycle_Tracked_induct[OF assms(1)])
  case IH: (1 st)
  show ?case
    apply(rule DFS_DirCycle_Tracked_cases[where st = st])
    by (auto intro!: IH(2-) invar_holds_intros simp: DFS_DirCycle_Tracked_simps[OF IH(1)])
qed

lemma invar_seed_holds[invar_holds_intros]:
  assumes "DFS_DirCycle_Tracked_dom st" "invar_1 st" "invar_part st" "invar_seed st"
  shows "invar_seed (DFS_DirCycle_Tracked st)"
  using assms(2-)
proof(induction rule: DFS_DirCycle_Tracked_induct[OF assms(1)])
  case IH: (1 st)
  show ?case
    apply(rule DFS_DirCycle_Tracked_cases[where st = st])
    by (auto intro!: IH(2-) invar_holds_intros simp: DFS_DirCycle_Tracked_simps[OF IH(1)])
qed

lemma invar_cyc_true_holds[invar_holds_intros]:
  assumes "DFS_DirCycle_Tracked_dom st" "invar_1 st" "invar_part st" "invar_seed st"
      and "invar_cyc_true st"
  shows "invar_cyc_true (DFS_DirCycle_Tracked st)"
  using assms(2-)
proof(induction rule: DFS_DirCycle_Tracked_induct[OF assms(1)])
  case IH: (1 st)
  show ?case
    apply(rule DFS_DirCycle_Tracked_cases[where st = st])
    by (auto intro!: IH(2-) invar_holds_intros simp: DFS_DirCycle_Tracked_simps[OF IH(1)])
qed

text \<open>On termination the loop has swept every vertex. The \<open>ret_1\<close> branch is impossible: it sets
  \<open>sweep_cyc\<close>, which the assumption rules out.\<close>
lemma ret_2_holds[ret_holds_intros]:
  assumes "DFS_DirCycle_Tracked_dom st" "invar_1 st" "invar_part st" "invar_seed st"
      and "\<not> sweep_cyc (DFS_DirCycle_Tracked st)"
  shows "DFS_DirCycle_Tracked_ret_2_conds (DFS_DirCycle_Tracked st)"
  using assms(2-)
proof(induction rule: DFS_DirCycle_Tracked_induct[OF assms(1)])
  case IH: (1 st)
  show ?case
  proof(rule DFS_DirCycle_Tracked_cases[where st = st], goal_cases)
    case 1
    then show ?case
      using IH(2)[OF 1 invar_1_holds_upd1[OF 1 IH(3,4,5)]
                       invar_part_holds_upd1[OF 1 IH(3,4,5)]
                       invar_seed_holds_upd1[OF 1 IH(3,4,5)]]
      using IH(6)
      by (simp add: DFS_DirCycle_Tracked_simps[OF IH(1)])
  next
    case 2
    then show ?case
      using IH(6)
      by (simp add: DFS_DirCycle_Tracked_simps[OF IH(1)] DFS_DirCycle_Tracked_ret1_def)
  next
    case 3
    then show ?case
      by (auto simp: DFS_DirCycle_Tracked_simps[OF IH(1)] DFS_DirCycle_Tracked_ret2_def)
  qed
qed

theorem DFS_DirCycle_Tracked_sound:
  assumes "sweep_cyc (DFS_DirCycle_Tracked initial_state)"
  shows "\<exists>c. Awalk_Defs.cycle (Graph.digraph_abs G) c"
  using invar_cyc_true_holds[OF initial_state_props(5) initial_state_props(1,2,3,4)] assms
  by (auto elim!: invar_props_elims)

text \<open>\<^bold>\<open>Completeness\<close>: no report means the \<^emph>\<open>whole\<close> graph is acyclic. The empty unfinished set is,
  by the partition, exactly the statement that the finished region is all of \<open>dVs G\<close> --- so unlike
  the \<open>_Linear\<close> proof there is no set difference to unfold, and \<open>G \<downharpoonright> dVs G = G\<close> finishes it.\<close>
theorem DFS_DirCycle_Tracked_complete:
  assumes "\<not> sweep_cyc (DFS_DirCycle_Tracked initial_state)"
  shows "\<nexists>c. Awalk_Defs.cycle (Graph.digraph_abs G) c"
proof -
  let ?r = "DFS_DirCycle_Tracked initial_state"
  note ini = initial_state_props
  have dom: "DFS_DirCycle_Tracked_dom initial_state" by (rule ini(5))
  have ip: "invar_part ?r" by (intro invar_part_holds dom ini)
  have isd: "invar_seed ?r" by (intro invar_seed_holds dom ini)
  have "DFS_DirCycle_Tracked_ret_2_conds ?r" by (intro ret_2_holds dom ini assms)
  hence empty: "sweep_unfin ?r = \<emptyset>\<^sub>N" by (auto elim!: call_cond_elims)
  have covers: "dVs (Graph.digraph_abs G) \<subseteq> t_set (sweep_fin ?r)"
    using ip empty by (force elim!: invar_props_elims)
  have acyc: "\<nexists>c. Awalk_Defs.cycle (Graph.digraph_abs G \<downharpoonright> t_set (sweep_fin ?r)) c"
    using isd by (auto simp: invar_seed_def seed_ok_def)
  have "Graph.digraph_abs G \<downharpoonright> t_set (sweep_fin ?r) = Graph.digraph_abs G"
    using covers by (auto simp: induce_subgraph_def dVs_def)
  thus ?thesis using acyc by simp
qed

end

end

end
