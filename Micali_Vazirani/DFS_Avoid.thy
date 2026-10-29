theory DFS_Avoid
  imports Graph_Algorithms_Dev.DFS_Skeleton
begin

provenance human

text \<open>A reachability DFS that avoids a given vertex set, as an instance of the DFS skeleton.
It is resumable: the search starts from a given stack (\<^term>\<open>stack0\<close>) and a set of previously
visited vertices (\<^term>\<open>vis0\<close>), searches for a vertex satisfying the predicate \<^term>\<open>Pv\<close>,
never pushes vertices in \<^term>\<open>avoid\<close> or \<^term>\<open>vis0\<close> (both are seeded into the seen set),
and collects fully explored vertices outside \<^term>\<open>avoid\<close> into the visited set. This is
intended to realise the incremental DFS (IDFS) assumed by the DDFS development. The state
extends the skeleton spine (stack/seen) with the accumulated visited set and the result slot.\<close>

record ('ver, 'vset) DFS_avoid_state = "('ver, 'vset) DFS_skel_state" +
  visited :: "'vset"
  ret     :: "'ver list option"

locale DFS_avoid =
  Graph: Pair_Graph_Specs where lookup = lookup +
 set_ops: Set2 vset_empty vset_delete _ t_set vset_inv insert
for lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option" +
fixes G::"'adjmap" and stack0::"'v list" and vis0::"'vset" and avoid::"'vset"
  and Pv::"'v \<Rightarrow> bool" and level::"'v \<Rightarrow> nat"
begin

abbreviation "neighbourhood' \<equiv> Graph.neighbourhood G"
notation "neighbourhood'" ("\<N>\<^sub>G _" 100)

definition "av_found (dfs_state::('v,'vset) DFS_avoid_state) =
   (case stack dfs_state of [] \<Rightarrow> False
    | (v # stack_tl) \<Rightarrow> Pv v \<and> \<not> isin avoid v)"

definition "av_on_found (dfs_state::('v,'vset) DFS_avoid_state) =
  (dfs_state \<lparr>ret := Some (stack dfs_state)\<rparr>)"

definition "av_on_empty (dfs_state::('v,'vset) DFS_avoid_state) =
  (dfs_state \<lparr>ret := None\<rparr>)"

definition "av_on_backtrack v (dfs_state::('v,'vset) DFS_avoid_state) =
  (if isin avoid v then dfs_state
   else dfs_state \<lparr>visited := insert v (visited dfs_state)\<rparr>)"

definition "vset_of_list xs = foldr (\<lambda>x vs. insert x vs) xs \<emptyset>\<^sub>N"

definition "avoid_initial_state =
  \<lparr>stack = stack0, seen = (avoid \<union>\<^sub>G vis0) \<union>\<^sub>G (vset_of_list stack0),
   visited = vis0, ret = None\<rparr>"

text \<open>The axioms are plain definitions (not locale assumptions), following the library
methodology, so that executable interpretations stay \<^theory_text>\<open>by unfold_locales\<close>.
Besides graph well-formedness they demand: the initial stack is (the reverse of) a walk,
it is distinct, the graph is layered w.r.t.\ \<^term>\<open>level\<close>, and the previously visited
set is sound: it contains no \<^term>\<open>Pv\<close>-vertex and any walk from it to a \<^term>\<open>Pv\<close>-vertex
crosses \<^term>\<open>avoid\<close>.\<close>

definition "DFS_avoid_axioms =
  (Graph.graph_inv G \<and> Graph.finite_graph G \<and> Graph.finite_vsets G \<and>
   vset_inv avoid \<and> vset_inv vis0 \<and>
   t_set avoid \<subseteq> dVs (Graph.digraph_abs G) \<and>
   t_set vis0 \<subseteq> dVs (Graph.digraph_abs G) \<and>
   Vwalk.vwalk (Graph.digraph_abs G) (rev stack0) \<and>
   distinct stack0 \<and>
   (\<forall>u v. (u, v) \<in> Graph.digraph_abs G \<longrightarrow> level v < level u))"

sublocale av: DFS_skel
  where lookup = lookup and G = G and s = "hd stack0"
    and found = av_found and on_found = av_on_found
    and on_empty = av_on_empty and on_backtrack = av_on_backtrack
  by unfold_locales

abbreviation "DFS_avoid_impl \<equiv> av.DFS_skel_impl"

text \<open>The final state of the search.\<close>
definition "avoid_final_state = av.DFS_skel avoid_initial_state"
definition "avoid_final_state_impl = DFS_avoid_impl avoid_initial_state"

end

locale DFS_avoid_thms = DFS_avoid +
  assumes avoid_axioms: DFS_avoid_axioms
begin

lemma spine_preservation:
  "stack (av_on_found st) = stack st" "seen (av_on_found st) = seen st"
  "stack (av_on_empty st) = stack st" "seen (av_on_empty st) = seen st"
  "stack (av_on_backtrack v st) = stack st" "seen (av_on_backtrack v st) = seen st"
  by (auto simp: av_on_found_def av_on_empty_def av_on_backtrack_def)

sublocale av: DFS_skel_thms
  where lookup = lookup and G = G and s = "hd stack0"
    and found = av_found and on_found = av_on_found
    and on_empty = av_on_empty and on_backtrack = av_on_backtrack
  using avoid_axioms
  by (unfold_locales)
     (auto simp: av.DFS_skel_axioms_def DFS_avoid_axioms_def
                 av_on_found_def av_on_empty_def av_on_backtrack_def)

lemma avoid_axioms_props:
  "vset_inv avoid" "vset_inv vis0"
  "t_set avoid \<subseteq> dVs (Graph.digraph_abs G)"
  "t_set vis0 \<subseteq> dVs (Graph.digraph_abs G)"
  "Vwalk.vwalk (Graph.digraph_abs G) (rev stack0)"
  "distinct stack0"
  using avoid_axioms
  by (auto simp: DFS_avoid_axioms_def)

lemma layered: "(u, v) \<in> Graph.digraph_abs G \<Longrightarrow> level v < level u"
  using avoid_axioms
  by (auto simp: DFS_avoid_axioms_def)


context
includes set_ops.automation2 and Graph.adjmap.automation and Graph.vset.set.automation
begin

lemma vset_of_list_aux:
  "vset_inv (foldr (\<lambda>x vs. insert x vs) xs \<emptyset>\<^sub>N) \<and>
   t_set (foldr (\<lambda>x vs. insert x vs) xs \<emptyset>\<^sub>N) = set xs"
  by (induction xs) auto

lemma vset_of_list_inv[simp,intro]: "vset_inv (vset_of_list xs)"
  using vset_of_list_aux
  by (simp add: vset_of_list_def)

lemma vset_of_list_set[simp]: "t_set (vset_of_list xs) = set xs"
  using vset_of_list_aux
  by (simp add: vset_of_list_def)

lemma stack0_dVs: "set stack0 \<subseteq> dVs (Graph.digraph_abs G)"
proof
  fix v assume "v \<in> set stack0"
  then have "v \<in> set (rev stack0)"
    by simp
  then show "v \<in> dVs (Graph.digraph_abs G)"
    using vwalk_then_in_dVs[OF avoid_axioms_props(5)]
    by blast
qed

lemma initial_state_unfold:
  "stack avoid_initial_state = stack0"
  "t_set (seen avoid_initial_state) = t_set avoid \<union> t_set vis0 \<union> set stack0"
  "vset_inv (seen avoid_initial_state)"
  "visited avoid_initial_state = vis0"
  "ret avoid_initial_state = None"
  by (auto simp: avoid_initial_state_def avoid_axioms_props(1,2))

lemma initial_invars[simp,intro]:
  "av.invar_1 avoid_initial_state"
  "av.invar_seen_stack avoid_initial_state"
  using avoid_axioms_props(3,4,6) stack0_dVs
  by (auto simp: av.invar_1_def av.invar_seen_stack_def initial_state_unfold)

lemma avoid_initial_dom: "av.DFS_skel_dom avoid_initial_state"
  by (intro av.DFS_skel_terminates initial_invars)

lemma avoid_final_state_impl_same: "avoid_final_state_impl = avoid_final_state"
  unfolding avoid_final_state_impl_def avoid_final_state_def
  by (rule av.DFS_skel_impl_same[OF avoid_initial_dom])

text \<open>The two update steps and the two return steps, explicitly.\<close>
lemma upd1_unfold:
  "stack (av.DFS_skel_upd1 st) = sel ((\<N>\<^sub>G (hd (stack st))) -\<^sub>G seen st) # stack st"
  "seen (av.DFS_skel_upd1 st) = insert (sel ((\<N>\<^sub>G (hd (stack st))) -\<^sub>G seen st)) (seen st)"
  "visited (av.DFS_skel_upd1 st) = visited st"
  "ret (av.DFS_skel_upd1 st) = ret st"
  by (auto simp: av.DFS_skel_upd1_def Let_def)

lemma upd2_unfold:
  "stack (av.DFS_skel_upd2 st) = tl (stack st)"
  "seen (av.DFS_skel_upd2 st) = seen st"
  "visited (av.DFS_skel_upd2 st) =
     (if isin avoid (hd (stack st)) then visited st
      else insert (hd (stack st)) (visited st))"
  "ret (av.DFS_skel_upd2 st) = ret st"
  by (auto simp: av.DFS_skel_upd2_def av_on_backtrack_def)

lemma ret1_unfold:
  "stack (av.DFS_skel_ret1 st) = stack st"
  "seen (av.DFS_skel_ret1 st) = seen st"
  "visited (av.DFS_skel_ret1 st) = visited st"
  "ret (av.DFS_skel_ret1 st) = None"
  by (auto simp: av.DFS_skel_ret1_def av_on_empty_def)

lemma ret2_unfold:
  "stack (av.DFS_skel_ret2 st) = stack st"
  "seen (av.DFS_skel_ret2 st) = seen st"
  "visited (av.DFS_skel_ret2 st) = visited st"
  "ret (av.DFS_skel_ret2 st) = Some (stack st)"
  by (auto simp: av.DFS_skel_ret2_def av_on_found_def)

end

text \<open>Instance invariants. Writing S0, A, V0 for the initial stack, the avoid set and the
initially visited set: the visited slot tracks V0 plus the newly finished vertices (seen
minus stack minus A); the stack is a walk; the stack is newly pushed vertices (outside
A, V0 and S0) on top of a suffix of S0; the seen set always contains A, V0 and S0.\<close>

definition "invar_vis_vset dfs_state = vset_inv (visited dfs_state)"

definition "invar_visited dfs_state =
  (t_set (visited dfs_state) =
     t_set vis0 \<union> ((t_set (seen dfs_state) - set (stack dfs_state)) - t_set avoid))"

definition "invar_vwalk dfs_state = Vwalk.vwalk (Graph.digraph_abs G) (rev (stack dfs_state))"

definition "invar_comp dfs_state =
  (t_set avoid \<union> t_set vis0 \<union> set stack0 \<subseteq> t_set (seen dfs_state) \<and>
   (\<exists>q j. stack dfs_state = q @ drop j stack0 \<and>
          set q \<inter> (t_set avoid \<union> t_set vis0 \<union> set stack0) = {}))"

context
includes set_ops.automation2 and Graph.adjmap.automation and Graph.vset.set.automation
begin

text \<open>The vertex pushed by the first call is an unseen out-neighbour of the stack head.\<close>
lemma upd1_new_vertex:
  assumes "av.DFS_skel_call_1_conds dfs_state" "av.invar_1 dfs_state"
  shows "sel ((\<N>\<^sub>G (hd (stack dfs_state))) -\<^sub>G seen dfs_state)
           \<in> t_set (\<N>\<^sub>G (hd (stack dfs_state))) - t_set (seen dfs_state)" (is ?g1)
    and "(hd (stack dfs_state), sel ((\<N>\<^sub>G (hd (stack dfs_state))) -\<^sub>G seen dfs_state))
           \<in> Graph.digraph_abs G" (is ?g2)
proof -
  have "vset_inv (seen dfs_state)"
    using assms(2) by (auto elim: invar_props_elims)
  moreover have "(\<N>\<^sub>G (hd (stack dfs_state))) -\<^sub>G (seen dfs_state) \<noteq> \<emptyset>\<^sub>N"
    using assms(1) by (auto elim!: call_cond_elims)
  ultimately show ?g1
    by (fastforce dest!: Graph.vset.choose')
  then show ?g2
    by auto
qed

lemma invar_vis_vset_props[invar_props_elims]:
  "invar_vis_vset dfs_state \<Longrightarrow> (vset_inv (visited dfs_state) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_vis_vset_def)

lemma invar_vis_vset_intro[invar_props_intros]:
  "vset_inv (visited dfs_state) \<Longrightarrow> invar_vis_vset dfs_state"
  by (auto simp: invar_vis_vset_def)

lemma invar_vis_vset_holds_upd1[invar_holds_intros]:
  "\<lbrakk>av.DFS_skel_call_1_conds dfs_state; invar_vis_vset dfs_state\<rbrakk> \<Longrightarrow>
     invar_vis_vset (av.DFS_skel_upd1 dfs_state)"
  by (auto simp: upd1_unfold elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_vis_vset_holds_upd2[invar_holds_intros]:
  "\<lbrakk>av.DFS_skel_call_2_conds dfs_state; invar_vis_vset dfs_state\<rbrakk> \<Longrightarrow>
     invar_vis_vset (av.DFS_skel_upd2 dfs_state)"
  by (auto simp: upd2_unfold elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_vis_vset_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>av.DFS_skel_ret_1_conds dfs_state; invar_vis_vset dfs_state\<rbrakk> \<Longrightarrow>
     invar_vis_vset (av.DFS_skel_ret1 dfs_state)"
  by (auto simp: ret1_unfold invar_vis_vset_def)

lemma invar_vis_vset_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>av.DFS_skel_ret_2_conds dfs_state; invar_vis_vset dfs_state\<rbrakk> \<Longrightarrow>
     invar_vis_vset (av.DFS_skel_ret2 dfs_state)"
  by (auto simp: ret2_unfold invar_vis_vset_def)

lemma invar_vis_vset_holds[invar_holds_intros]:
  assumes "av.DFS_skel_dom dfs_state" "invar_vis_vset dfs_state"
  shows "invar_vis_vset (av.DFS_skel dfs_state)"
  using assms(2-)
proof(induction rule: av.DFS_skel_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule av.DFS_skel_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-) invar_holds_intros simp: av.DFS_skel_simps[OF IH(1)])
qed

lemma invar_visited_props[invar_props_elims]:
  "invar_visited dfs_state \<Longrightarrow>
    (t_set (visited dfs_state) =
       t_set vis0 \<union> ((t_set (seen dfs_state) - set (stack dfs_state)) - t_set avoid) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_visited_def)

lemma invar_visited_intro[invar_props_intros]:
  "t_set (visited dfs_state) =
     t_set vis0 \<union> ((t_set (seen dfs_state) - set (stack dfs_state)) - t_set avoid) \<Longrightarrow>
   invar_visited dfs_state"
  by (auto simp: invar_visited_def)

lemma invar_visited_holds_upd1[invar_holds_intros]:
  assumes "av.DFS_skel_call_1_conds dfs_state" "av.invar_1 dfs_state" "invar_visited dfs_state"
  shows "invar_visited (av.DFS_skel_upd1 dfs_state)"
proof -
  let ?u = "sel ((\<N>\<^sub>G (hd (stack dfs_state))) -\<^sub>G seen dfs_state)"
  have u: "?u \<notin> t_set (seen dfs_state)"
    using upd1_new_vertex[OF assms(1,2)] by blast
  have si: "vset_inv (seen dfs_state)"
    using assms(2) by (auto elim: invar_props_elims)
  have "t_set (seen (av.DFS_skel_upd1 dfs_state)) = t_set (seen dfs_state) \<union> {?u}"
    by (auto simp: upd1_unfold si)
  moreover have "set (stack (av.DFS_skel_upd1 dfs_state)) = Set.insert ?u (set (stack dfs_state))"
    by (auto simp: upd1_unfold)
  ultimately have "t_set (seen (av.DFS_skel_upd1 dfs_state)) - set (stack (av.DFS_skel_upd1 dfs_state))
        = t_set (seen dfs_state) - set (stack dfs_state)"
    using u by auto
  then show ?thesis
    using assms(3) by (auto simp: upd1_unfold elim!: invar_props_elims intro!: invar_props_intros)
qed

lemma invar_visited_holds_upd2[invar_holds_intros]:
  assumes "av.DFS_skel_call_2_conds dfs_state" "av.invar_seen_stack dfs_state"
          "invar_vis_vset dfs_state" "invar_visited dfs_state"
  shows "invar_visited (av.DFS_skel_upd2 dfs_state)"
proof -
  obtain v stack_tl where st: "stack dfs_state = v # stack_tl"
    using assms(1) by (auto elim!: call_cond_elims)
  have vin: "v \<in> t_set (seen dfs_state)" and vni: "v \<notin> set stack_tl"
    using assms(2) st by (auto elim!: invar_props_elims)
  have visin: "vset_inv (visited dfs_state)"
    using assms(3) by (auto elim: invar_props_elims)
  have expand: "t_set (seen dfs_state) - set stack_tl
        = (t_set (seen dfs_state) - set (stack dfs_state)) \<union> {v}"
    using vin vni st by auto
  have isin_iff: "isin avoid v \<longleftrightarrow> v \<in> t_set avoid"
    using avoid_axioms_props(1) by auto
  show ?thesis
  proof (cases "v \<in> t_set avoid")
    case True
    then show ?thesis
      using assms(4) st expand isin_iff
      by (auto simp: upd2_unfold st elim!: invar_props_elims intro!: invar_props_intros)
  next
    case False
    then have "t_set (visited (av.DFS_skel_upd2 dfs_state)) = t_set (visited dfs_state) \<union> {v}"
      by (auto simp: upd2_unfold st isin_iff visin)
    then show ?thesis
      using assms(4) st expand False
      by (auto simp: upd2_unfold elim!: invar_props_elims intro!: invar_props_intros)
  qed
qed

lemma invar_visited_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>av.DFS_skel_ret_1_conds dfs_state; invar_visited dfs_state\<rbrakk> \<Longrightarrow>
     invar_visited (av.DFS_skel_ret1 dfs_state)"
  by (auto simp: ret1_unfold invar_visited_def)

lemma invar_visited_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>av.DFS_skel_ret_2_conds dfs_state; invar_visited dfs_state\<rbrakk> \<Longrightarrow>
     invar_visited (av.DFS_skel_ret2 dfs_state)"
  by (auto simp: ret2_unfold invar_visited_def)

lemma invar_visited_holds[invar_holds_intros]:
  assumes "av.DFS_skel_dom dfs_state" "av.invar_1 dfs_state" "av.invar_seen_stack dfs_state"
          "invar_vis_vset dfs_state" "invar_visited dfs_state"
  shows "invar_visited (av.DFS_skel dfs_state)"
  using assms(2-)
proof(induction rule: av.DFS_skel_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule av.DFS_skel_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-) invar_holds_intros simp: av.DFS_skel_simps[OF IH(1)])
qed

lemma invar_vwalk_props[invar_props_elims]:
  "invar_vwalk dfs_state \<Longrightarrow>
    (Vwalk.vwalk (Graph.digraph_abs G) (rev (stack dfs_state)) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_vwalk_def)

lemma invar_vwalk_intro[invar_props_intros]:
  "Vwalk.vwalk (Graph.digraph_abs G) (rev (stack dfs_state)) \<Longrightarrow> invar_vwalk dfs_state"
  by (auto simp: invar_vwalk_def)

lemma invar_vwalk_holds_upd1[invar_holds_intros]:
  assumes "av.DFS_skel_call_1_conds dfs_state" "av.invar_1 dfs_state" "invar_vwalk dfs_state"
  shows "invar_vwalk (av.DFS_skel_upd1 dfs_state)"
proof -
  obtain v stack_tl where st: "stack dfs_state = v # stack_tl"
    using assms(1) by (auto elim!: call_cond_elims)
  let ?u = "sel ((\<N>\<^sub>G (hd (stack dfs_state))) -\<^sub>G seen dfs_state)"
  have edge: "(v, ?u) \<in> Graph.digraph_abs G"
    using upd1_new_vertex(2)[OF assms(1,2)] st by simp
  have w: "Vwalk.vwalk (Graph.digraph_abs G) (rev stack_tl @ [v])"
    using assms(3) st by (auto simp: invar_vwalk_def)
  have "Vwalk.vwalk (Graph.digraph_abs G) (v # [?u])"
    using edge by (auto simp: Pair_Graph.dVs_def)
  then have "Vwalk.vwalk (Graph.digraph_abs G) (rev stack_tl @ v # [?u])"
    using vwalk_append2[OF w] by simp
  then show ?thesis
    by (auto simp: upd1_unfold invar_vwalk_def st)
qed

lemma invar_vwalk_holds_upd2[invar_holds_intros]:
  assumes "av.DFS_skel_call_2_conds dfs_state" "invar_vwalk dfs_state"
  shows "invar_vwalk (av.DFS_skel_upd2 dfs_state)"
proof -
  obtain v stack_tl where st: "stack dfs_state = v # stack_tl"
    using assms(1) by (auto elim!: call_cond_elims)
  have "Vwalk.vwalk (Graph.digraph_abs G) (rev stack_tl @ [v])"
    using assms(2) st by (auto elim!: invar_props_elims)
  then have "Vwalk.vwalk (Graph.digraph_abs G) (rev stack_tl)"
    by (blast dest: append_vwalk_pref)
  then show ?thesis
    by (auto simp: upd2_unfold st intro!: invar_props_intros)
qed

lemma invar_vwalk_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>av.DFS_skel_ret_1_conds dfs_state; invar_vwalk dfs_state\<rbrakk> \<Longrightarrow>
     invar_vwalk (av.DFS_skel_ret1 dfs_state)"
  by (auto simp: ret1_unfold invar_vwalk_def)

lemma invar_vwalk_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>av.DFS_skel_ret_2_conds dfs_state; invar_vwalk dfs_state\<rbrakk> \<Longrightarrow>
     invar_vwalk (av.DFS_skel_ret2 dfs_state)"
  by (auto simp: ret2_unfold invar_vwalk_def)

lemma invar_vwalk_holds[invar_holds_intros]:
  assumes "av.DFS_skel_dom dfs_state" "av.invar_1 dfs_state" "invar_vwalk dfs_state"
  shows "invar_vwalk (av.DFS_skel dfs_state)"
  using assms(2-)
proof(induction rule: av.DFS_skel_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule av.DFS_skel_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-) invar_holds_intros simp: av.DFS_skel_simps[OF IH(1)])
qed

lemma invar_comp_props[invar_props_elims]:
  "invar_comp dfs_state \<Longrightarrow>
    (\<lbrakk>t_set avoid \<union> t_set vis0 \<union> set stack0 \<subseteq> t_set (seen dfs_state);
      \<exists>q j. stack dfs_state = q @ drop j stack0 \<and>
            set q \<inter> (t_set avoid \<union> t_set vis0 \<union> set stack0) = {}\<rbrakk>
      \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_comp_def)

lemma invar_comp_intro[invar_props_intros]:
  "\<lbrakk>t_set avoid \<union> t_set vis0 \<union> set stack0 \<subseteq> t_set (seen dfs_state);
    stack dfs_state = q @ drop j stack0;
    set q \<inter> (t_set avoid \<union> t_set vis0 \<union> set stack0) = {}\<rbrakk> \<Longrightarrow>
   invar_comp dfs_state"
  by (auto simp: invar_comp_def)

lemma invar_comp_holds_upd1[invar_holds_intros]:
  assumes "av.DFS_skel_call_1_conds dfs_state" "av.invar_1 dfs_state" "invar_comp dfs_state"
  shows "invar_comp (av.DFS_skel_upd1 dfs_state)"
proof -
  let ?u = "sel ((\<N>\<^sub>G (hd (stack dfs_state))) -\<^sub>G seen dfs_state)"
  have u: "?u \<notin> t_set (seen dfs_state)"
    using upd1_new_vertex[OF assms(1,2)] by blast
  have si: "vset_inv (seen dfs_state)"
    using assms(2) by (auto elim: invar_props_elims)
  from assms(3) obtain q j where qj: "stack dfs_state = q @ drop j stack0"
      "set q \<inter> (t_set avoid \<union> t_set vis0 \<union> set stack0) = {}"
    and sub: "t_set avoid \<union> t_set vis0 \<union> set stack0 \<subseteq> t_set (seen dfs_state)"
    by (auto simp: invar_comp_def)
  have eq: "stack (av.DFS_skel_upd1 dfs_state) = (?u # q) @ drop j stack0"
    by (auto simp: upd1_unfold qj(1))
  have disj: "set (?u # q) \<inter> (t_set avoid \<union> t_set vis0 \<union> set stack0) = {}"
    using qj(2) u sub by auto
  have subs: "t_set avoid \<union> t_set vis0 \<union> set stack0 \<subseteq> t_set (seen (av.DFS_skel_upd1 dfs_state))"
    using sub by (auto simp: upd1_unfold si)
  show ?thesis
    by (rule invar_comp_intro[OF subs eq disj])
qed

lemma invar_comp_holds_upd2[invar_holds_intros]:
  assumes "av.DFS_skel_call_2_conds dfs_state" "invar_comp dfs_state"
  shows "invar_comp (av.DFS_skel_upd2 dfs_state)"
proof -
  from assms(2) obtain q j where qj: "stack dfs_state = q @ drop j stack0"
      "set q \<inter> (t_set avoid \<union> t_set vis0 \<union> set stack0) = {}"
    and sub: "t_set avoid \<union> t_set vis0 \<union> set stack0 \<subseteq> t_set (seen dfs_state)"
    by (auto simp: invar_comp_def)
  have ne: "stack dfs_state \<noteq> []"
    using assms(1) by (auto elim!: call_cond_elims)
  show ?thesis
  proof (cases q)
    case Nil
    have g1: "t_set avoid \<union> t_set vis0 \<union> set stack0 \<subseteq> t_set (seen (av.DFS_skel_upd2 dfs_state))"
      using sub by (auto simp: upd2_unfold)
    have "tl (stack dfs_state) = drop (Suc j) stack0"
      using qj(1) ne Nil by (simp add: drop_Suc tl_drop)
    then have g2: "stack (av.DFS_skel_upd2 dfs_state) = [] @ drop (Suc j) stack0"
      by (auto simp: upd2_unfold)
    show ?thesis
      by (rule invar_comp_intro[OF g1 g2]) simp
  next
    case (Cons a q')
    have g1: "t_set avoid \<union> t_set vis0 \<union> set stack0 \<subseteq> t_set (seen (av.DFS_skel_upd2 dfs_state))"
      using sub by (auto simp: upd2_unfold)
    have g2: "stack (av.DFS_skel_upd2 dfs_state) = q' @ drop j stack0"
      using qj(1) Cons by (auto simp: upd2_unfold)
    have g3: "set q' \<inter> (t_set avoid \<union> t_set vis0 \<union> set stack0) = {}"
      using qj(2) Cons by auto
    show ?thesis
      by (rule invar_comp_intro[OF g1 g2 g3])
  qed
qed

lemma invar_comp_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>av.DFS_skel_ret_1_conds dfs_state; invar_comp dfs_state\<rbrakk> \<Longrightarrow>
     invar_comp (av.DFS_skel_ret1 dfs_state)"
  by (force simp: ret1_unfold invar_comp_def)

lemma invar_comp_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>av.DFS_skel_ret_2_conds dfs_state; invar_comp dfs_state\<rbrakk> \<Longrightarrow>
     invar_comp (av.DFS_skel_ret2 dfs_state)"
  by (force simp: ret2_unfold invar_comp_def)

lemma invar_comp_holds[invar_holds_intros]:
  assumes "av.DFS_skel_dom dfs_state" "av.invar_1 dfs_state" "invar_comp dfs_state"
  shows "invar_comp (av.DFS_skel dfs_state)"
  using assms(2-)
proof(induction rule: av.DFS_skel_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule av.DFS_skel_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-) invar_holds_intros simp: av.DFS_skel_simps[OF IH(1)])
qed

lemma initial_invars_2[simp,intro]:
  "invar_vis_vset avoid_initial_state"
  "invar_visited avoid_initial_state"
  "invar_vwalk avoid_initial_state"
  "invar_comp avoid_initial_state"
  by (auto simp: initial_state_unfold avoid_axioms_props(2,5)
           intro!: invar_props_intros invar_comp_intro[where q = "[]" and j = 0])

end

text \<open>The searched region is closed: a newly finished vertex (seen, off the stack, outside
A and V0) has all its out-neighbours seen, satisfies \<not>Pv, and has no edge back into the
current stack. Vertices below the stack head satisfy \<not>Pv unless they come from S0.\<close>

definition "invar_closed dfs_state =
  (\<forall>v \<in> t_set (seen dfs_state) - set (stack dfs_state) - t_set avoid - t_set vis0.
     t_set (\<N>\<^sub>G v) \<subseteq> t_set (seen dfs_state))"

definition "invar_notP dfs_state =
  (\<forall>v \<in> t_set (seen dfs_state) - set (stack dfs_state) - t_set avoid - t_set vis0. \<not> Pv v)"

definition "invar_tl_notP dfs_state =
  (\<forall>v \<in> set (tl (stack dfs_state)). v \<in> set stack0 \<or> \<not> Pv v)"

definition "invar_no_back dfs_state =
  (\<forall>v \<in> t_set (seen dfs_state) - set (stack dfs_state) - t_set avoid - t_set vis0.
   \<forall>w \<in> set (stack dfs_state). (v, w) \<notin> Graph.digraph_abs G)"

context
includes set_ops.automation2 and Graph.adjmap.automation and Graph.vset.set.automation
begin

text \<open>In a layered digraph, the last vertex of a walk has the strictly smallest level.\<close>
lemma level_walk_last:
  assumes "Vwalk.vwalk (Graph.digraph_abs G) p" "w \<in> set (butlast p)"
  shows "level (last p) < level w"
  using assms
proof (induction arbitrary: w rule: Vwalk.vwalk.induct)
  case vwalk0
  then show ?case by simp
next
  case (vwalk1 v)
  then show ?case by simp
next
  case (vwalk2 v v' vs)
  have lvv': "level v' < level v"
    using layered vwalk2.hyps(1) by blast
  show ?case
  proof (cases "w = v")
    case True
    have "level (last (v' # vs)) \<le> level v'"
    proof (cases vs)
      case Nil
      then show ?thesis by simp
    next
      case (Cons a as)
      then have "v' \<in> set (butlast (v' # vs))" by simp
      then show ?thesis using vwalk2.IH by fastforce
    qed
    then show ?thesis using True lvv' by simp
  next
    case False
    then have "w \<in> set (butlast (v' # vs))"
      using vwalk2.prems by (cases vs) auto
    then show ?thesis using vwalk2.IH by simp
  qed
qed

text \<open>Frame lemma for the descend step: the finished region is unchanged.\<close>
lemma upd1_frame:
  assumes "av.DFS_skel_call_1_conds dfs_state" "av.invar_1 dfs_state"
  shows "t_set (seen (av.DFS_skel_upd1 dfs_state)) - set (stack (av.DFS_skel_upd1 dfs_state))
         = t_set (seen dfs_state) - set (stack dfs_state)"
proof -
  let ?u = "sel ((\<N>\<^sub>G (hd (stack dfs_state))) -\<^sub>G seen dfs_state)"
  have u: "?u \<notin> t_set (seen dfs_state)"
    using upd1_new_vertex[OF assms] by blast
  have si: "vset_inv (seen dfs_state)"
    using assms(2) by (auto elim: invar_props_elims)
  show ?thesis
    using u by (auto simp: upd1_unfold si)
qed

lemma invar_closed_props[invar_props_elims]:
  "invar_closed dfs_state \<Longrightarrow>
    ((\<And>v. v \<in> t_set (seen dfs_state) - set (stack dfs_state) - t_set avoid - t_set vis0 \<Longrightarrow>
       t_set (\<N>\<^sub>G v) \<subseteq> t_set (seen dfs_state)) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_closed_def)

lemma invar_closed_intro[invar_props_intros]:
  "(\<And>v. v \<in> t_set (seen dfs_state) - set (stack dfs_state) - t_set avoid - t_set vis0 \<Longrightarrow>
     t_set (\<N>\<^sub>G v) \<subseteq> t_set (seen dfs_state)) \<Longrightarrow> invar_closed dfs_state"
  by (auto simp: invar_closed_def)

lemma invar_closed_holds_upd1[invar_holds_intros]:
  assumes "av.DFS_skel_call_1_conds dfs_state" "av.invar_1 dfs_state" "invar_closed dfs_state"
  shows "invar_closed (av.DFS_skel_upd1 dfs_state)"
proof (rule invar_closed_intro)
  fix v assume "v \<in> t_set (seen (av.DFS_skel_upd1 dfs_state)) -
                    set (stack (av.DFS_skel_upd1 dfs_state)) - t_set avoid - t_set vis0"
  then have "v \<in> t_set (seen dfs_state) - set (stack dfs_state) - t_set avoid - t_set vis0"
    using upd1_frame[OF assms(1,2)] by blast
  then have "t_set (\<N>\<^sub>G v) \<subseteq> t_set (seen dfs_state)"
    using assms(3) by (auto elim!: invar_props_elims)
  moreover have "t_set (seen dfs_state) \<subseteq> t_set (seen (av.DFS_skel_upd1 dfs_state))"
    using assms(2) by (auto simp: upd1_unfold elim: invar_props_elims)
  ultimately show "t_set (\<N>\<^sub>G v) \<subseteq> t_set (seen (av.DFS_skel_upd1 dfs_state))"
    by blast
qed

lemma invar_closed_holds_upd2[invar_holds_intros]:
  assumes "av.DFS_skel_call_2_conds dfs_state" "av.invar_1 dfs_state" "invar_closed dfs_state"
  shows "invar_closed (av.DFS_skel_upd2 dfs_state)"
proof (rule invar_closed_intro)
  obtain v stack_tl where st: "stack dfs_state = v # stack_tl"
    using assms(1) by (auto elim!: call_cond_elims)
  have si: "vset_inv (seen dfs_state)"
    using assms(2) by (auto elim: invar_props_elims)
  have hd_closed: "t_set (\<N>\<^sub>G v) \<subseteq> t_set (seen dfs_state)"
  proof -
    have "(\<N>\<^sub>G v) -\<^sub>G (seen dfs_state) = \<emptyset>\<^sub>N"
      using assms(1) st by (auto elim!: call_cond_elims)
    then have "t_set ((\<N>\<^sub>G v) -\<^sub>G (seen dfs_state)) = {}"
      by simp
    then show ?thesis
      using si by auto
  qed
  fix x assume "x \<in> t_set (seen (av.DFS_skel_upd2 dfs_state)) -
                    set (stack (av.DFS_skel_upd2 dfs_state)) - t_set avoid - t_set vis0"
  then have x: "x \<in> (t_set (seen dfs_state) - set stack_tl) - t_set avoid - t_set vis0"
    by (auto simp: upd2_unfold st)
  show "t_set (\<N>\<^sub>G x) \<subseteq> t_set (seen (av.DFS_skel_upd2 dfs_state))"
  proof (cases "x = v")
    case True
    then show ?thesis using hd_closed by (auto simp: upd2_unfold)
  next
    case False
    then have "x \<in> t_set (seen dfs_state) - set (stack dfs_state) - t_set avoid - t_set vis0"
      using x st by auto
    then show ?thesis
      using assms(3) by (auto simp: upd2_unfold elim!: invar_props_elims)
  qed
qed

lemma invar_closed_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>av.DFS_skel_ret_1_conds dfs_state; invar_closed dfs_state\<rbrakk> \<Longrightarrow>
     invar_closed (av.DFS_skel_ret1 dfs_state)"
  by (auto simp: ret1_unfold invar_closed_def)

lemma invar_closed_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>av.DFS_skel_ret_2_conds dfs_state; invar_closed dfs_state\<rbrakk> \<Longrightarrow>
     invar_closed (av.DFS_skel_ret2 dfs_state)"
  by (auto simp: ret2_unfold invar_closed_def)

lemma invar_closed_holds[invar_holds_intros]:
  assumes "av.DFS_skel_dom dfs_state" "av.invar_1 dfs_state" "invar_closed dfs_state"
  shows "invar_closed (av.DFS_skel dfs_state)"
  using assms(2-)
proof(induction rule: av.DFS_skel_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule av.DFS_skel_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-) invar_holds_intros simp: av.DFS_skel_simps[OF IH(1)])
qed

lemma invar_notP_props[invar_props_elims]:
  "invar_notP dfs_state \<Longrightarrow>
    ((\<And>v. v \<in> t_set (seen dfs_state) - set (stack dfs_state) - t_set avoid - t_set vis0 \<Longrightarrow>
       \<not> Pv v) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_notP_def)

lemma invar_notP_intro[invar_props_intros]:
  "(\<And>v. v \<in> t_set (seen dfs_state) - set (stack dfs_state) - t_set avoid - t_set vis0 \<Longrightarrow>
     \<not> Pv v) \<Longrightarrow> invar_notP dfs_state"
  by (auto simp: invar_notP_def)

lemma invar_notP_holds_upd1[invar_holds_intros]:
  assumes "av.DFS_skel_call_1_conds dfs_state" "av.invar_1 dfs_state" "invar_notP dfs_state"
  shows "invar_notP (av.DFS_skel_upd1 dfs_state)"
proof (rule invar_notP_intro)
  fix v assume "v \<in> t_set (seen (av.DFS_skel_upd1 dfs_state)) -
                    set (stack (av.DFS_skel_upd1 dfs_state)) - t_set avoid - t_set vis0"
  then have "v \<in> t_set (seen dfs_state) - set (stack dfs_state) - t_set avoid - t_set vis0"
    using upd1_frame[OF assms(1,2)] by blast
  then show "\<not> Pv v"
    using assms(3) by (auto elim!: invar_props_elims)
qed

lemma invar_notP_holds_upd2[invar_holds_intros]:
  assumes "av.DFS_skel_call_2_conds dfs_state" "invar_notP dfs_state"
  shows "invar_notP (av.DFS_skel_upd2 dfs_state)"
proof (rule invar_notP_intro)
  obtain v stack_tl where st: "stack dfs_state = v # stack_tl"
    using assms(1) by (auto elim!: call_cond_elims)
  have nf: "\<not> av_found dfs_state"
    using assms(1) by (auto elim!: call_cond_elims)
  fix x assume "x \<in> t_set (seen (av.DFS_skel_upd2 dfs_state)) -
                    set (stack (av.DFS_skel_upd2 dfs_state)) - t_set avoid - t_set vis0"
  then have x: "x \<in> (t_set (seen dfs_state) - set stack_tl) - t_set avoid - t_set vis0"
    by (auto simp: upd2_unfold st)
  show "\<not> Pv x"
  proof (cases "x = v")
    case True
    have "\<not> isin avoid v"
      using x True avoid_axioms_props(1) by auto
    then show ?thesis
      using nf st True by (auto simp: av_found_def)
  next
    case False
    then have "x \<in> t_set (seen dfs_state) - set (stack dfs_state) - t_set avoid - t_set vis0"
      using x st by auto
    then show ?thesis
      using assms(2) by (auto elim!: invar_props_elims)
  qed
qed

lemma invar_notP_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>av.DFS_skel_ret_1_conds dfs_state; invar_notP dfs_state\<rbrakk> \<Longrightarrow>
     invar_notP (av.DFS_skel_ret1 dfs_state)"
  by (auto simp: ret1_unfold invar_notP_def)

lemma invar_notP_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>av.DFS_skel_ret_2_conds dfs_state; invar_notP dfs_state\<rbrakk> \<Longrightarrow>
     invar_notP (av.DFS_skel_ret2 dfs_state)"
  by (auto simp: ret2_unfold invar_notP_def)

lemma invar_notP_holds[invar_holds_intros]:
  assumes "av.DFS_skel_dom dfs_state" "av.invar_1 dfs_state" "invar_notP dfs_state"
  shows "invar_notP (av.DFS_skel dfs_state)"
  using assms(2-)
proof(induction rule: av.DFS_skel_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule av.DFS_skel_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-) invar_holds_intros simp: av.DFS_skel_simps[OF IH(1)])
qed

lemma invar_tl_notP_props[invar_props_elims]:
  "invar_tl_notP dfs_state \<Longrightarrow>
    ((\<And>v. v \<in> set (tl (stack dfs_state)) \<Longrightarrow> v \<in> set stack0 \<or> \<not> Pv v) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_tl_notP_def)

lemma invar_tl_notP_intro[invar_props_intros]:
  "(\<And>v. v \<in> set (tl (stack dfs_state)) \<Longrightarrow> v \<in> set stack0 \<or> \<not> Pv v) \<Longrightarrow> invar_tl_notP dfs_state"
  by (auto simp: invar_tl_notP_def)

lemma invar_tl_notP_holds_upd1[invar_holds_intros]:
  assumes "av.DFS_skel_call_1_conds dfs_state" "invar_comp dfs_state" "invar_tl_notP dfs_state"
  shows "invar_tl_notP (av.DFS_skel_upd1 dfs_state)"
proof (rule invar_tl_notP_intro)
  obtain v stack_tl where st: "stack dfs_state = v # stack_tl"
    using assms(1) by (auto elim!: call_cond_elims)
  have nf: "\<not> av_found dfs_state"
    using assms(1) by (auto elim!: call_cond_elims)
  fix x assume "x \<in> set (tl (stack (av.DFS_skel_upd1 dfs_state)))"
  then have x: "x = v \<or> x \<in> set stack_tl"
    by (auto simp: upd1_unfold st)
  show "x \<in> set stack0 \<or> \<not> Pv x"
  proof (cases "x = v")
    case True
    show ?thesis
    proof (cases "Pv v")
      case False
      then show ?thesis using True by simp
    next
      case Pv: True
      then have "isin avoid v"
        using nf st by (auto simp: av_found_def)
      then have vA: "v \<in> t_set avoid"
        using avoid_axioms_props(1) by auto
      obtain q j where qj: "stack dfs_state = q @ drop j stack0"
          "set q \<inter> (t_set avoid \<union> t_set vis0 \<union> set stack0) = {}"
        using assms(2) by (auto simp: invar_comp_def)
      have "v \<in> set (drop j stack0)"
      proof (cases q)
        case Nil
        then have "drop j stack0 = v # stack_tl"
          using qj(1) st by simp
        then show ?thesis
          by simp
      next
        case (Cons a q')
        then have "v = a" using qj(1) st by auto
        then have "v \<in> set q" using Cons by auto
        then show ?thesis using qj(2) vA by auto
      qed
      then have "v \<in> set stack0"
        using set_drop_subset by fastforce
      then show ?thesis using True by simp
    qed
  next
    case False
    then have "x \<in> set (tl (stack dfs_state))"
      using x st by auto
    then show ?thesis
      using assms(3) by (auto elim!: invar_props_elims)
  qed
qed

lemma invar_tl_notP_holds_upd2[invar_holds_intros]:
  assumes "av.DFS_skel_call_2_conds dfs_state" "invar_tl_notP dfs_state"
  shows "invar_tl_notP (av.DFS_skel_upd2 dfs_state)"
proof (rule invar_tl_notP_intro)
  obtain v stack_tl where st: "stack dfs_state = v # stack_tl"
    using assms(1) by (auto elim!: call_cond_elims)
  fix x assume "x \<in> set (tl (stack (av.DFS_skel_upd2 dfs_state)))"
  then have "x \<in> set (tl (stack dfs_state))"
    using st by (cases stack_tl) (auto simp: upd2_unfold)
  then show "x \<in> set stack0 \<or> \<not> Pv x"
    using assms(2) by (auto elim!: invar_props_elims)
qed

lemma invar_tl_notP_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>av.DFS_skel_ret_1_conds dfs_state; invar_tl_notP dfs_state\<rbrakk> \<Longrightarrow>
     invar_tl_notP (av.DFS_skel_ret1 dfs_state)"
  by (auto simp: ret1_unfold invar_tl_notP_def)

lemma invar_tl_notP_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>av.DFS_skel_ret_2_conds dfs_state; invar_tl_notP dfs_state\<rbrakk> \<Longrightarrow>
     invar_tl_notP (av.DFS_skel_ret2 dfs_state)"
  by (auto simp: ret2_unfold invar_tl_notP_def)

lemma invar_tl_notP_holds[invar_holds_intros]:
  assumes "av.DFS_skel_dom dfs_state" "av.invar_1 dfs_state" "invar_comp dfs_state"
          "invar_tl_notP dfs_state"
  shows "invar_tl_notP (av.DFS_skel dfs_state)"
  using assms(2-)
proof(induction rule: av.DFS_skel_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule av.DFS_skel_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-) invar_holds_intros simp: av.DFS_skel_simps[OF IH(1)])
qed

lemma invar_no_back_props[invar_props_elims]:
  "invar_no_back dfs_state \<Longrightarrow>
    ((\<And>v w. \<lbrakk>v \<in> t_set (seen dfs_state) - set (stack dfs_state) - t_set avoid - t_set vis0;
             w \<in> set (stack dfs_state)\<rbrakk> \<Longrightarrow> (v, w) \<notin> Graph.digraph_abs G) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_no_back_def)

lemma invar_no_back_intro[invar_props_intros]:
  "(\<And>v w. \<lbrakk>v \<in> t_set (seen dfs_state) - set (stack dfs_state) - t_set avoid - t_set vis0;
           w \<in> set (stack dfs_state)\<rbrakk> \<Longrightarrow> (v, w) \<notin> Graph.digraph_abs G) \<Longrightarrow>
   invar_no_back dfs_state"
  by (auto simp: invar_no_back_def)

lemma invar_no_back_holds_upd1[invar_holds_intros]:
  assumes "av.DFS_skel_call_1_conds dfs_state" "av.invar_1 dfs_state"
          "invar_closed dfs_state" "invar_no_back dfs_state"
  shows "invar_no_back (av.DFS_skel_upd1 dfs_state)"
proof (rule invar_no_back_intro)
  let ?u = "sel ((\<N>\<^sub>G (hd (stack dfs_state))) -\<^sub>G seen dfs_state)"
  have u: "?u \<notin> t_set (seen dfs_state)"
    using upd1_new_vertex[OF assms(1,2)] by blast
  fix v w
  assume v: "v \<in> t_set (seen (av.DFS_skel_upd1 dfs_state)) -
                 set (stack (av.DFS_skel_upd1 dfs_state)) - t_set avoid - t_set vis0"
     and w: "w \<in> set (stack (av.DFS_skel_upd1 dfs_state))"
  have vold: "v \<in> t_set (seen dfs_state) - set (stack dfs_state) - t_set avoid - t_set vis0"
    using v upd1_frame[OF assms(1,2)] by blast
  show "(v, w) \<notin> Graph.digraph_abs G"
  proof (cases "w = ?u")
    case True
    show ?thesis
    proof
      assume "(v, w) \<in> Graph.digraph_abs G"
      then have "w \<in> t_set (\<N>\<^sub>G v)"
        by auto
      then have "w \<in> t_set (seen dfs_state)"
        using assms(3) vold by (auto elim!: invar_props_elims)
      then show False
        using True u by simp
    qed
  next
    case False
    then have "w \<in> set (stack dfs_state)"
      using w by (auto simp: upd1_unfold)
    then show ?thesis
      using assms(4) vold by (auto elim!: invar_props_elims)
  qed
qed

lemma invar_no_back_holds_upd2[invar_holds_intros]:
  assumes "av.DFS_skel_call_2_conds dfs_state" "av.invar_1 dfs_state"
          "invar_vwalk dfs_state" "invar_no_back dfs_state"
  shows "invar_no_back (av.DFS_skel_upd2 dfs_state)"
proof (rule invar_no_back_intro)
  obtain v stack_tl where st: "stack dfs_state = v # stack_tl"
    using assms(1) by (auto elim!: call_cond_elims)
  fix x w
  assume x: "x \<in> t_set (seen (av.DFS_skel_upd2 dfs_state)) -
                 set (stack (av.DFS_skel_upd2 dfs_state)) - t_set avoid - t_set vis0"
     and w: "w \<in> set (stack (av.DFS_skel_upd2 dfs_state))"
  have wtl: "w \<in> set stack_tl"
    using w st by (auto simp: upd2_unfold)
  show "(x, w) \<notin> Graph.digraph_abs G"
  proof (cases "x = v")
    case True
    show ?thesis
    proof
      assume edge: "(x, w) \<in> Graph.digraph_abs G"
      have "Vwalk.vwalk (Graph.digraph_abs G) (rev stack_tl @ [v])"
        using assms(3) st by (auto elim!: invar_props_elims)
      moreover have "w \<in> set (butlast (rev stack_tl @ [v]))"
        using wtl by simp
      moreover have "last (rev stack_tl @ [v]) = v"
        by simp
      ultimately have "level v < level w"
        using level_walk_last by fastforce
      moreover have "level w < level x"
        using layered edge by blast
      ultimately show False
        using True by simp
    qed
  next
    case False
    then have "x \<in> t_set (seen dfs_state) - set (stack dfs_state) - t_set avoid - t_set vis0"
      using x st by (auto simp: upd2_unfold)
    then show ?thesis
      using assms(4) wtl st by (auto elim!: invar_props_elims)
  qed
qed

lemma invar_no_back_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>av.DFS_skel_ret_1_conds dfs_state; invar_no_back dfs_state\<rbrakk> \<Longrightarrow>
     invar_no_back (av.DFS_skel_ret1 dfs_state)"
  by (auto simp: ret1_unfold invar_no_back_def)

lemma invar_no_back_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>av.DFS_skel_ret_2_conds dfs_state; invar_no_back dfs_state\<rbrakk> \<Longrightarrow>
     invar_no_back (av.DFS_skel_ret2 dfs_state)"
  by (auto simp: ret2_unfold invar_no_back_def)

lemma invar_no_back_holds[invar_holds_intros]:
  assumes "av.DFS_skel_dom dfs_state" "av.invar_1 dfs_state" "invar_vwalk dfs_state"
          "invar_closed dfs_state" "invar_no_back dfs_state"
  shows "invar_no_back (av.DFS_skel dfs_state)"
  using assms(2-)
proof(induction rule: av.DFS_skel_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule av.DFS_skel_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-) invar_holds_intros simp: av.DFS_skel_simps[OF IH(1)])
qed

lemma initial_invars_3[simp,intro]:
  "invar_closed avoid_initial_state"
  "invar_notP avoid_initial_state"
  "invar_tl_notP avoid_initial_state"
  "invar_no_back avoid_initial_state"
proof -
  have empty_new: "t_set (seen avoid_initial_state) - set (stack avoid_initial_state)
                     - t_set avoid - t_set vis0 = {}"
    by (auto simp: initial_state_unfold)
  show "invar_closed avoid_initial_state" "invar_notP avoid_initial_state"
       "invar_no_back avoid_initial_state"
    using empty_new by (auto simp: invar_closed_def invar_notP_def invar_no_back_def)
  show "invar_tl_notP avoid_initial_state"
  proof (rule invar_tl_notP_intro)
    fix v assume "v \<in> set (tl (stack avoid_initial_state))"
    then have "v \<in> set (tl stack0)"
      by (simp add: initial_state_unfold)
    then have "v \<in> set stack0"
      by (cases stack0) auto
    then show "v \<in> set stack0 \<or> \<not> Pv v"
      by simp
  qed
qed

end

text \<open>While the stack is nonempty its bottom element is the bottom of the initial stack:
vertices are only pushed on top, and once the stack empties the search stops.\<close>

definition "invar_last dfs_state =
  (stack dfs_state \<noteq> [] \<longrightarrow> (stack0 \<noteq> [] \<and> last (stack dfs_state) = last stack0))"

context
includes set_ops.automation2 and Graph.adjmap.automation and Graph.vset.set.automation
begin

lemma invar_last_props[invar_props_elims]:
  "invar_last dfs_state \<Longrightarrow>
    ((stack dfs_state \<noteq> [] \<Longrightarrow> stack0 \<noteq> [] \<and> last (stack dfs_state) = last stack0) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_last_def)

lemma invar_last_intro[invar_props_intros]:
  "(stack dfs_state \<noteq> [] \<Longrightarrow> stack0 \<noteq> [] \<and> last (stack dfs_state) = last stack0) \<Longrightarrow>
     invar_last dfs_state"
  by (auto simp: invar_last_def)

lemma invar_last_holds_upd1[invar_holds_intros]:
  assumes "av.DFS_skel_call_1_conds dfs_state" "invar_last dfs_state"
  shows "invar_last (av.DFS_skel_upd1 dfs_state)"
proof -
  obtain v stack_tl where st: "stack dfs_state = v # stack_tl"
    using assms(1) by (auto elim!: call_cond_elims)
  then show ?thesis
    using assms(2) by (auto simp: upd1_unfold invar_last_def)
qed

lemma invar_last_holds_upd2[invar_holds_intros]:
  assumes "av.DFS_skel_call_2_conds dfs_state" "invar_last dfs_state"
  shows "invar_last (av.DFS_skel_upd2 dfs_state)"
proof -
  obtain v stack_tl where st: "stack dfs_state = v # stack_tl"
    using assms(1) by (auto elim!: call_cond_elims)
  then show ?thesis
    using assms(2) by (cases "stack_tl") (auto simp: upd2_unfold invar_last_def)
qed

lemma invar_last_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>av.DFS_skel_ret_1_conds dfs_state; invar_last dfs_state\<rbrakk> \<Longrightarrow>
     invar_last (av.DFS_skel_ret1 dfs_state)"
  by (auto simp: ret1_unfold invar_last_def)

lemma invar_last_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>av.DFS_skel_ret_2_conds dfs_state; invar_last dfs_state\<rbrakk> \<Longrightarrow>
     invar_last (av.DFS_skel_ret2 dfs_state)"
  by (auto simp: ret2_unfold invar_last_def)

lemma invar_last_holds[invar_holds_intros]:
  assumes "av.DFS_skel_dom dfs_state" "invar_last dfs_state"
  shows "invar_last (av.DFS_skel dfs_state)"
  using assms(2-)
proof(induction rule: av.DFS_skel_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule av.DFS_skel_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-) invar_holds_intros simp: av.DFS_skel_simps[OF IH(1)])
qed

lemma initial_invar_last[simp,intro]: "invar_last avoid_initial_state"
  by (auto simp: invar_last_def initial_state_unfold)

text \<open>Exit characterisation: a run started with an empty result slot ends either with
\<^term>\<open>None\<close> and an empty stack, or with \<^term>\<open>Some\<close> of the final stack, whose head is a
\<^term>\<open>Pv\<close>-vertex outside the avoid set.\<close>
lemma ret_char:
  assumes "av.DFS_skel_dom dfs_state" "ret dfs_state = None"
  shows "(ret (av.DFS_skel dfs_state) = None \<longrightarrow> stack (av.DFS_skel dfs_state) = []) \<and>
         (\<forall>p'. ret (av.DFS_skel dfs_state) = Some p' \<longrightarrow>
             p' = stack (av.DFS_skel dfs_state) \<and> av_found (av.DFS_skel dfs_state))"
  using assms(2)
proof (induction rule: av.DFS_skel_induct[OF assms(1)])
  case IH: (1 dfs_state)
  note simps = av.DFS_skel_simps[OF IH(1)]
  show ?case
  proof (rule av.DFS_skel_cases[where dfs_state = dfs_state])
    assume c: "av.DFS_skel_call_1_conds dfs_state"
    have "ret (av.DFS_skel_upd1 dfs_state) = None"
      using IH(4) by (simp add: upd1_unfold)
    then show ?thesis
      using IH(2)[OF c] c by (simp add: simps(1))
  next
    assume c: "av.DFS_skel_call_2_conds dfs_state"
    have "ret (av.DFS_skel_upd2 dfs_state) = None"
      using IH(4) by (simp add: upd2_unfold)
    then show ?thesis
      using IH(3)[OF c] c by (simp add: simps(2))
  next
    assume c: "av.DFS_skel_ret_1_conds dfs_state"
    then have "stack (av.DFS_skel dfs_state) = []" "ret (av.DFS_skel dfs_state) = None"
      by (auto simp: simps(3) ret1_unfold elim!: call_cond_elims)
    then show ?thesis
      by simp
  next
    assume c: "av.DFS_skel_ret_2_conds dfs_state"
    have f: "av_found dfs_state"
      using c by (auto elim!: call_cond_elims)
    have res: "av.DFS_skel dfs_state = av.DFS_skel_ret2 dfs_state"
      using c by (simp add: simps(4))
    have "av_found (av.DFS_skel_ret2 dfs_state)"
      using f by (auto simp: av_found_def ret2_unfold split: list.splits)
    then show ?thesis
      using res by (simp add: ret2_unfold)
  qed
qed

end

text \<open>The collected invariants of the final state.\<close>

context
includes set_ops.automation2 and Graph.adjmap.automation and Graph.vset.set.automation
begin

lemma final_invars:
  "av.invar_1 avoid_final_state"
  "av.invar_seen_stack avoid_final_state"
  "invar_vis_vset avoid_final_state"
  "invar_visited avoid_final_state"
  "invar_vwalk avoid_final_state"
  "invar_comp avoid_final_state"
  "invar_closed avoid_final_state"
  "invar_notP avoid_final_state"
  "invar_tl_notP avoid_final_state"
  "invar_no_back avoid_final_state"
  "invar_last avoid_final_state"
  unfolding avoid_final_state_def
  by (intro invar_holds_intros avoid_initial_dom initial_invars initial_invars_2
            initial_invars_3 initial_invar_last)+

lemma final_ret_char:
  "(ret avoid_final_state = None \<longrightarrow> stack avoid_final_state = []) \<and>
   (\<forall>p'. ret avoid_final_state = Some p' \<longrightarrow>
       p' = stack avoid_final_state \<and> av_found avoid_final_state)"
  unfolding avoid_final_state_def
  by (intro ret_char avoid_initial_dom) (simp add: initial_state_unfold)

text \<open>Basic bookkeeping properties of the run (counterparts of the DDFS locale's
IDFS-vis-works family).\<close>

theorem DFS_avoid_vis_mono: "t_set vis0 \<subseteq> t_set (visited avoid_final_state)"
  using final_invars(4) by (auto elim!: invar_props_elims)

text \<open>Closure of the newly finished region under successors (Layer-1 export for the
closure-style DDFS interface): a successor of a newly visited vertex lands in the avoid
set, the (new) visited set, or the final stack.\<close>
theorem DFS_avoid_closure:
  assumes "v \<in> t_set (visited avoid_final_state) - t_set vis0"
          "(v, w) \<in> Graph.digraph_abs G"
  shows "w \<in> t_set avoid \<union> t_set (visited avoid_final_state) \<union> set (stack avoid_final_state)"
proof -
  have vFin: "v \<in> t_set (seen avoid_final_state) - set (stack avoid_final_state)
                    - t_set avoid - t_set vis0"
    using assms(1) final_invars(4) by (auto elim!: invar_props_elims)
  have "t_set (\<N>\<^sub>G v) \<subseteq> t_set (seen avoid_final_state)"
    using final_invars(7) vFin by (auto elim!: invar_props_elims)
  moreover have "w \<in> t_set (\<N>\<^sub>G v)"
    using assms(2) by auto
  ultimately have wseen: "w \<in> t_set (seen avoid_final_state)"
    by blast
  show ?thesis
  proof (cases "w \<in> set (stack avoid_final_state) \<or> w \<in> t_set avoid \<or> w \<in> t_set vis0")
    case True
    then show ?thesis
      using DFS_avoid_vis_mono by blast
  next
    case False
    then have "w \<in> t_set (seen avoid_final_state) - set (stack avoid_final_state)
                     - t_set avoid - t_set vis0"
      using wseen by blast
    then have "w \<in> t_set (visited avoid_final_state)"
      using final_invars(4) by (auto elim!: invar_props_elims)
    then show ?thesis by blast
  qed
qed

theorem DFS_avoid_vis_new_avoid:
  "(t_set (visited avoid_final_state) - t_set vis0) \<inter> t_set avoid = {}"
  using final_invars(4) by (auto elim!: invar_props_elims)

theorem DFS_avoid_vis_new_notP:
  assumes "v \<in> t_set (visited avoid_final_state) - t_set vis0"
  shows "\<not> Pv v"
proof -
  have "v \<in> t_set (seen avoid_final_state) - set (stack avoid_final_state)
          - t_set avoid - t_set vis0"
    using assms final_invars(4) by (auto elim!: invar_props_elims)
  then show ?thesis
    using final_invars(8) by (auto elim!: invar_props_elims)
qed

theorem DFS_avoid_vis_new_finite:
  "finite (t_set (visited avoid_final_state) - t_set vis0)"
proof -
  have "t_set (visited avoid_final_state) - t_set vis0 \<subseteq> dVs (Graph.digraph_abs G)"
    using final_invars(4) final_invars(2) by (auto elim!: invar_props_elims)
  moreover have "finite (dVs (Graph.digraph_abs G))"
    by (intro Graph.finite_vertices av.graph_inv)
  ultimately show ?thesis
    by (rule finite_subset)
qed

theorem DFS_avoid_complete:
  assumes "ret avoid_final_state = None"
  shows "set stack0 - t_set avoid \<subseteq> t_set (visited avoid_final_state)"
proof -
  have empty: "stack avoid_final_state = []"
    using final_ret_char assms by blast
  have "set stack0 \<subseteq> t_set (seen avoid_final_state)"
    using final_invars(6) by (auto simp: invar_comp_def)
  then show ?thesis
    using final_invars(4) empty by (auto elim!: invar_props_elims)
qed

text \<open>Soundness properties of a successful search (counterparts of IDFS-sound).\<close>

theorem DFS_avoid_sound_stack:
  assumes "ret avoid_final_state = Some p'"
  shows "p' = stack avoid_final_state"
  using final_ret_char assms by blast

theorem DFS_avoid_sound_nonempty:
  assumes "ret avoid_final_state = Some p'"
  shows "p' \<noteq> []"
proof -
  have "av_found avoid_final_state"
    using final_ret_char assms by blast
  then show ?thesis
    using DFS_avoid_sound_stack[OF assms]
    by (auto simp: av_found_def split: list.splits)
qed

theorem DFS_avoid_sound_hdP:
  assumes "ret avoid_final_state = Some p'"
  shows "Pv (hd p')" and "hd p' \<notin> t_set avoid"
proof -
  have f: "av_found avoid_final_state"
    using final_ret_char assms by blast
  have p': "p' = stack avoid_final_state"
    by (rule DFS_avoid_sound_stack[OF assms])
  from f p' show "Pv (hd p')" "hd p' \<notin> t_set avoid"
    using avoid_axioms_props(1)
    by (auto simp: av_found_def split: list.splits)
qed

theorem DFS_avoid_sound_vwalk:
  assumes "ret avoid_final_state = Some p'"
  shows "Vwalk.vwalk (Graph.digraph_abs G) (rev p')"
  using final_invars(5) DFS_avoid_sound_stack[OF assms]
  by (auto elim!: invar_props_elims)

theorem DFS_avoid_sound_distinct:
  assumes "ret avoid_final_state = Some p'"
  shows "distinct p'"
  using final_invars(2) DFS_avoid_sound_stack[OF assms]
  by (auto elim!: invar_props_elims)

theorem DFS_avoid_sound_last:
  assumes "ret avoid_final_state = Some p'"
  shows "stack0 \<noteq> []" and "last p' = last stack0"
  using final_invars(11) DFS_avoid_sound_stack[OF assms] DFS_avoid_sound_nonempty[OF assms]
  by (auto elim!: invar_props_elims)

theorem DFS_avoid_sound_new_disjoint:
  assumes "ret avoid_final_state = Some p'"
  shows "(set p' - set stack0) \<inter> (t_set avoid \<union> t_set (visited avoid_final_state)) = {}"
proof -
  have p': "p' = stack avoid_final_state"
    by (rule DFS_avoid_sound_stack[OF assms])
  obtain q j where qj: "stack avoid_final_state = q @ drop j stack0"
      "set q \<inter> (t_set avoid \<union> t_set vis0 \<union> set stack0) = {}"
    using final_invars(6) by (auto simp: invar_comp_def)
  have sub: "set p' - set stack0 \<subseteq> set q"
    using p' qj(1) set_drop_subset[of j stack0] by auto
  have qA: "set q \<inter> t_set avoid = {}" and qV: "set q \<inter> t_set vis0 = {}"
    using qj(2) by auto
  have "set q \<inter> (t_set (seen avoid_final_state) - set (stack avoid_final_state)) = {}"
    using qj(1) by auto
  then have "set q \<inter> t_set (visited avoid_final_state) = {}"
    using final_invars(4) qV by (auto elim!: invar_props_elims)
  then show ?thesis
    using sub qA by auto
qed

theorem DFS_avoid_sound_sub:
  assumes "ret avoid_final_state = Some p'"
  shows "set stack0 - set p' - t_set avoid \<subseteq> t_set (visited avoid_final_state)"
proof -
  have p': "p' = stack avoid_final_state"
    by (rule DFS_avoid_sound_stack[OF assms])
  have "set stack0 \<subseteq> t_set (seen avoid_final_state)"
    using final_invars(6) by (auto simp: invar_comp_def)
  then show ?thesis
    using final_invars(4) p' by (auto elim!: invar_props_elims)
qed

theorem DFS_avoid_sound_tl_notP:
  assumes "ret avoid_final_state = Some p'" "v \<in> set (tl p')"
  shows "v \<in> set stack0 \<or> \<not> Pv v"
  using final_invars(9) DFS_avoid_sound_stack[OF assms(1)] assms(2)
  by (auto elim!: invar_props_elims)

text \<open>Additional exports for the abstract adapter.\<close>

theorem DFS_avoid_visited_dVs:
  "t_set (visited avoid_final_state) \<subseteq> dVs (Graph.digraph_abs G)"
proof -
  have "t_set (seen avoid_final_state) \<subseteq> dVs (Graph.digraph_abs G)"
    using final_invars(2) by (auto elim!: invar_props_elims)
  then show ?thesis
    using final_invars(4) avoid_axioms_props(4) by (auto elim!: invar_props_elims)
qed

theorem DFS_avoid_stack_dVs:
  "set (stack avoid_final_state) \<subseteq> dVs (Graph.digraph_abs G)"
  using final_invars(2) by (auto elim!: invar_props_elims)

theorem DFS_avoid_visited_stack:
  "t_set (visited avoid_final_state) \<inter> set (stack avoid_final_state) \<subseteq> t_set vis0"
  using final_invars(4) by (auto elim!: invar_props_elims)

theorem DFS_avoid_found_immediately:
  assumes "ret avoid_final_state = Some p'" "stack0 \<noteq> []" "Pv (hd stack0)"
          "\<not> isin avoid (hd stack0)"
  shows "p' = stack0"
proof -
  have f: "av_found avoid_initial_state"
    using assms(2,3,4)
    by (auto simp: av_found_def initial_state_unfold neq_Nil_conv)
  have ne2: "\<exists>v stack_tl. stack avoid_initial_state = v # stack_tl"
    using assms(2) by (simp add: initial_state_unfold neq_Nil_conv)
  have r2: "av.DFS_skel_ret_2_conds avoid_initial_state"
    by (rule av.DFS_skel_ret_2_condsI[OF ne2 f])
  have "avoid_final_state = av.DFS_skel_ret2 avoid_initial_state"
    unfolding avoid_final_state_def
    by (simp add: av.DFS_skel_simps(4)[OF avoid_initial_dom r2])
  then show ?thesis
    using assms(1) by (simp add: ret2_unfold initial_state_unfold)
qed

text \<open>The central completeness-style property (counterpart of IDFS-vis-works(1)):
any walk from a newly visited vertex to a \<^term>\<open>Pv\<close>-vertex crosses the avoid set.
The proof: the newly finished region is closed under successors up to the avoid set,
the previously visited set and the final stack; edges into the final stack are excluded
by \<^term>\<open>invar_no_back\<close>; once the walk enters the previously visited set, the
soundness precondition on \<^term>\<open>vis0\<close> applies.\<close>

lemma explored_walk:
  assumes "Vwalk.vwalk (Graph.digraph_abs G) (v # p)"
          "v \<in> t_set (seen avoid_final_state) - set (stack avoid_final_state)
                 - t_set avoid - t_set vis0"
          "set (v # p) \<inter> t_set avoid = {}"
  shows "set (v # p) \<subseteq> t_set (seen avoid_final_state) - set (stack avoid_final_state)
                 - t_set avoid - t_set vis0
         \<or> (\<exists>pre u suf. v # p = pre @ u # suf \<and> u \<in> t_set vis0)"
  using assms
proof (induction p arbitrary: v)
  case Nil
  then show ?case by auto
next
  case (Cons w p')
  let ?Fin = "t_set (seen avoid_final_state) - set (stack avoid_final_state)
                 - t_set avoid - t_set vis0"
  have edge: "(v, w) \<in> Graph.digraph_abs G"
    using Cons.prems(1) by auto
  have wseen: "w \<in> t_set (seen avoid_final_state)"
  proof -
    have "t_set (\<N>\<^sub>G v) \<subseteq> t_set (seen avoid_final_state)"
      using final_invars(7) Cons.prems(2) by (auto elim!: invar_props_elims)
    moreover have "w \<in> t_set (\<N>\<^sub>G v)"
      using edge by auto
    ultimately show ?thesis by blast
  qed
  have wnstack: "w \<notin> set (stack avoid_final_state)"
    using final_invars(10) Cons.prems(2) edge by (auto elim!: invar_props_elims)
  have wnavoid: "w \<notin> t_set avoid"
    using Cons.prems(3) by auto
  show ?case
  proof (cases "w \<in> t_set vis0")
    case True
    then have "v # w # p' = [v] @ w # p'" by simp
    then show ?thesis using True by blast
  next
    case False
    then have wFin: "w \<in> ?Fin"
      using wseen wnstack wnavoid by blast
    have "Vwalk.vwalk (Graph.digraph_abs G) (w # p')"
      using Cons.prems(1) by (auto intro: append_vwalk_suff[of _ "[v]"])
    moreover have "set (w # p') \<inter> t_set avoid = {}"
      using Cons.prems(3) by auto
    ultimately have "set (w # p') \<subseteq> ?Fin \<or> (\<exists>pre u suf. w # p' = pre @ u # suf \<and> u \<in> t_set vis0)"
      using Cons.IH wFin by blast
    then show ?thesis
    proof
      assume "set (w # p') \<subseteq> ?Fin"
      then show ?thesis using Cons.prems(2) by auto
    next
      assume "\<exists>pre u suf. w # p' = pre @ u # suf \<and> u \<in> t_set vis0"
      then obtain pre u suf where "w # p' = pre @ u # suf" "u \<in> t_set vis0" by blast
      then have "v # w # p' = (v # pre) @ u # suf" by simp
      then show ?thesis using \<open>u \<in> t_set vis0\<close> by blast
    qed
  qed
qed

theorem DFS_avoid_vis_new_invar0:
  assumes "v \<in> t_set (visited avoid_final_state) - t_set vis0"
      and "p \<noteq> []"
      and "Vwalk.vwalk_bet (Graph.digraph_abs G) v (v # p) v'"
      and "Pv v'"
      and vis_notP: "\<And>u. u \<in> t_set vis0 \<Longrightarrow> \<not> Pv u"
      and vis_invar0: "\<And>u q w. u \<in> t_set vis0 \<Longrightarrow> q \<noteq> [] \<Longrightarrow>
                              Vwalk.vwalk_bet (Graph.digraph_abs G) u (u # q) w \<Longrightarrow>
                              Pv w \<Longrightarrow> set q \<inter> t_set avoid \<noteq> {}"
  shows "set p \<inter> t_set avoid \<noteq> {}"
proof (rule ccontr)
  assume dis: "\<not> set p \<inter> t_set avoid \<noteq> {}"
  let ?Fin = "t_set (seen avoid_final_state) - set (stack avoid_final_state)
                 - t_set avoid - t_set vis0"
  have vFin: "v \<in> ?Fin"
    using assms(1) final_invars(4) by (auto elim!: invar_props_elims)
  have walk: "Vwalk.vwalk (Graph.digraph_abs G) (v # p)"
    using assms(3) by (auto simp: vwalk_bet_def)
  have lastp: "last (v # p) = v'"
    using assms(3) by (auto simp: vwalk_bet_def)
  have noA: "set (v # p) \<inter> t_set avoid = {}"
    using dis vFin by auto
  from explored_walk[OF walk vFin noA]
  show False
  proof
    assume allFin: "set (v # p) \<subseteq> ?Fin"
    have "v' \<in> set (v # p)"
      using lastp last_in_set[of "v # p"] by auto
    then have "v' \<in> ?Fin"
      using allFin by blast
    then have "\<not> Pv v'"
      using final_invars(8) by (auto elim!: invar_props_elims)
    then show False using assms(4) by simp
  next
    assume "\<exists>pre u suf. v # p = pre @ u # suf \<and> u \<in> t_set vis0"
    then obtain pre u suf where split: "v # p = pre @ u # suf" and uV0: "u \<in> t_set vis0"
      by blast
    show False
    proof (cases suf)
      case Nil
      then have "v' = u"
        using split lastp by auto
      then have "\<not> Pv v'"
        using uV0 vis_notP by simp
      then show False using assms(4) by simp
    next
      case (Cons a suf')
      have "Vwalk.vwalk (Graph.digraph_abs G) (pre @ u # suf)"
        using walk split by simp
      then have "Vwalk.vwalk (Graph.digraph_abs G) (u # suf)"
        by (rule append_vwalk_suff)
      moreover have "last (u # suf) = v'"
        using split lastp Cons by auto
      ultimately have "Vwalk.vwalk_bet (Graph.digraph_abs G) u (u # suf) v'"
        by (auto simp: vwalk_bet_def)
      then have "set suf \<inter> t_set avoid \<noteq> {}"
        using vis_invar0[OF uV0 _ _ assms(4)] Cons by blast
      moreover have "set suf \<subseteq> set (v # p)"
        using split by auto
      ultimately show False
        using noA by auto
    qed
  qed
qed

end

end

end
