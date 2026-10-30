theory Network_Simplex_Final
  imports Network_Simplex_Preservation
Flow_Theory.Optimality_Certification
begin

text \<open>\<^bold>\<open>Consequences of the terminating branches.\<close> When the loop stops it does so in one
      of two terminal branches. In the success branch the selector found no entering edge, so the
      current flow is a genuine minimum-cost \<open>b\<close>-flow (via \<open>optimality_from_potentials\<close>). In
      the unbounded branch the bottleneck search exposed an all-infinite-capacity negative circuit,
      i.e. \<open>has_neg_infty_cycle\<close> holds and the instance is unbounded.\<close>

context network_simplex
begin

context
  fixes s
  assumes inv: "ns_invar s"
begin

private lemmas inv_impl = ns_invar_implD[OF ns_invarD(1)[OF inv]]
  and inv_bflow = ns_invar_bflowD[OF ns_invarD(2)[OF inv]]
  and inv_stp = ns_invar_partitionD[OF ns_invarD(3)[OF inv]]
  and inv_flow_fits = ns_invar_flow_fitsD[OF ns_invarD(4)[OF inv]]
  and inv_pot_fits = ns_invar_pot_fitsD[OF ns_invarD(5)[OF inv]]
  and inv_tree = ns_invarD(7)[OF inv]
  and inv_selfloop = ns_invarD(8)[OF inv]

subsection \<open>Success branch: the flow is optimal\<close>

text \<open>At @{const ns_success_cond} the selector returns @{term None}, so @{const no_entering_edge}
      holds: every @{term L}-edge has non-negative and every @{term U}-edge non-positive reduced cost.
      Together with the structural invariants (@{term L}-edges carry zero flow, @{term U}-edges are
      saturated, tree edges have zero reduced cost) every edge falls into one of three cases, which
      discharge the complementary-slackness hypotheses of @{thm optimality_from_potentials}.\<close>

lemma success_no_entering: "ns_success_cond s \<Longrightarrow> no_entering_edge (potentials s) (edge_state s)"
  using inv_impl inv_pot_fits
  by (auto elim!: ns_success_condE intro!: sel_select_NoneD
           simp: ns_select_def selection_precond_def potential_fits_spanning_tree_partition_def)

lemma success_edge_cases:
  assumes "ns_success_cond s" "e \<in> \<E>"
  obtains "\<c> e + ns_pot_of s (fst e) - ns_pot_of s (snd e) = 0"
  | "ns_flow_of s e = 0" "0 \<le> \<c> e + ns_pot_of s (fst e) - ns_pot_of s (snd e)"
  | "ereal (ns_flow_of s e) = \<u> e" "\<c> e + ns_pot_of s (fst e) - ns_pot_of s (snd e) \<le> 0"
proof-
  consider "e \<in> ns_tree_edges s" | "e \<in> ns_L_of s" | "e \<in> ns_selfloops_L" | "e \<in> ns_U_of s"
    | "e \<in> ns_selfloops_U"
    using assms(2) inv_stp spanning_tree_partitionD(1)
    by blast
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
      using inv_pot_fits
      unfolding potential_fits_spanning_tree_partition_def
      by (force intro: that(1))
  next
    case 2
    then show ?thesis
      using that(2) inv_flow_fits assms(1) success_no_entering
      by (simp add: flow_fits_spanning_tree_partition_def no_entering_edge_def ns_L_of_def reduced_cost_def)
  next
    case 3
    then show ?thesis
      using that(2) inv_selfloop
      by (simp add: ns_selfloops_L_def ns_invar_selfloop_def)
  next
    case 4
    then show ?thesis
      using that(3) inv_flow_fits assms(1) success_no_entering
      by (simp add: flow_fits_spanning_tree_partition_def no_entering_edge_def ns_U_of_def reduced_cost_def)
  next
    case 5
    then show ?thesis
      using that(3) inv_selfloop
      by (simp add: ns_selfloops_U_def ns_invar_selfloop_def)
  qed
qed

lemma ns_success_optimal: "ns_success_cond s \<Longrightarrow> is_Opt b (ns_flow_of s)"
  using inv_bflow
  by (rule optimality_from_potentials[where \<pi> = "ns_pot_of s"]) (auto elim: success_edge_cases simp: zero_ereal_def)

lemma par_edge_pair:
  "v \<in> \<V> - {r} \<Longrightarrow>
    make_pair (par_edge s v) = (if par_up s v then (v, par_vx s v) else (par_vx s v, v))"
  using inv_tree ns_invar_tree_dirD[of s v]
  by (auto simp: make_pair_def par_vx_def)

text \<open>Directed walk built from the parent edges along an up-path (all edges point
      child$\rightarrow$parent): @{term \<open>map (par_edge s) P\<close>} is a directed walk from
      @{term \<open>hd P\<close>} to the junction @{term a}.\<close>

lemma up_walk_cas:
  "\<lbrakk>set P \<subseteq> \<V> - {r}; \<And>v. v \<in> set P \<Longrightarrow> par_up s v;
    \<And>i. Suc i < length P \<Longrightarrow> par_vx s (P ! i) = P ! Suc i; P \<noteq> [];
    par_vx s (last P) = a\<rbrakk>
   \<Longrightarrow> cas (hd P) (map make_pair (map (par_edge s) P)) a"
proof(induction P)
  case (Cons v P)
  have "P \<noteq> [] \<Longrightarrow> cas (hd P) (map make_pair (map (par_edge s) P)) a"
    using Cons.prems(1,2,5) Cons.prems(3)[of "Suc i" for i]
    by (intro Cons.IH) auto
  then show ?case
    using Cons.prems(1,2,5) Cons.prems(3)[of 0] par_edge_pair[of v]
    by (cases P) auto
qed simp

text \<open>Directed walk from the parent edges along a down-path (all edges point parent$\rightarrow$child), taken in
      reverse: @{term \<open>map (par_edge s) (rev P)\<close>} is a directed walk from the junction @{term a} to
      @{term \<open>hd P\<close>}.\<close>

lemma dn_walk_cas:
  "\<lbrakk>set P \<subseteq> \<V> - {r}; \<And>v. v \<in> set P \<Longrightarrow> \<not> par_up s v;
    \<And>i. Suc i < length P \<Longrightarrow> par_vx s (P ! i) = P ! Suc i; P \<noteq> [];
    par_vx s (last P) = a\<rbrakk>
   \<Longrightarrow> cas a (map make_pair (map (par_edge s) (rev P))) (hd P)"
proof(induction P arbitrary: a rule: rev_induct)
  case (snoc v P)
  have "P \<noteq> [] \<Longrightarrow> cas v (map make_pair (map (par_edge s) (rev P))) (hd P)"
    using snoc.prems(1,2) snoc.prems(3)[of "length P - 1"] snoc.prems(3)
    by (intro snoc.IH) (auto simp: nth_append last_conv_nth)
  then show ?case
    using snoc.prems(1,2,5) par_edge_pair[of v]
    by (cases "P = []") (auto simp: hd_append)
qed simp

subsection \<open>Consequences of an infinite bottleneck\<close>

lemma res_fwd_m1_cap: "\<lbrakk>a \<in> \<E>; res_fwd s a = - 1\<rbrakk> \<Longrightarrow> cap a = - 1"
  using inv res_fwd_sign[of s a] cap_nonneg[of a] cap_finite[of a] inv_bflow
  by (cases "cap a = - 1") (auto simp: isbflow_def isuflow_def res_fwd_def)

lemma flow_nonneg: "a \<in> \<E> \<Longrightarrow> 0 \<le> ns_flow_of s a"
  using inv_bflow
  by (auto simp: isbflow_def isuflow_def)

lemma res_up_inf:
  "\<lbrakk>v \<in> \<V> - {r}; res_up s v = - 1\<rbrakk> \<Longrightarrow> par_up s v \<and> \<u> (par_edge s v) = \<infinity>"
  using inv inv_tree ns_invar_tree_edgeD[of s v] res_bwd_nonneg[of s "par_edge s v"] res_fwd_m1_cap cap_infinite
  by (cases "par_up s v") (simp_all add: res_up_def)

lemma res_down_inf:
  "\<lbrakk>v \<in> \<V> - {r}; res_down s v = - 1\<rbrakk> \<Longrightarrow> \<not> par_up s v \<and> \<u> (par_edge s v) = \<infinity>"
  using inv inv_tree ns_invar_tree_edgeD[of s v] res_bwd_nonneg[of s "par_edge s v"] res_fwd_m1_cap cap_infinite
  by (cases "par_up s v") (simp_all add: res_down_def)

lemma scan_up_all_inf:
  "\<lbrakk>scan_up s p = (- 1, best); v \<in> set p\<rbrakk> \<Longrightarrow> res_up s v = - 1"
  using scan_up_min[of s p "- 1" best v]
  by auto

lemma scan_down_all_inf:
  "\<lbrakk>scan_down s p = (- 1, best); v \<in> set p\<rbrakk> \<Longrightarrow> res_down s v = - 1"
  using scan_down_min[of s p "- 1" best v]
  by auto

lemma mininf_m1_iff:
  "mininf x y = - 1 \<longleftrightarrow> x = - 1 \<and> y = - 1" "- 1 = mininf x y \<longleftrightarrow> x = - 1 \<and> y = - 1"
  by (auto simp: mininf_def)

text \<open>In the unbounded branch the entering edge comes from @{term L}, has infinite capacity and negative
      reduced cost, and the two tree paths of its fundamental circuit consist of infinite-capacity edges
      pointing towards the junction @{term a} (the @{term p2} side) resp. away from it (the @{term p1} side).\<close>

lemma unbounded_circuit:
  assumes "ns_unbounded_cond s"
  obtains e p1 p2 a p3 where "e \<in> \<E>" "\<u> e = \<infinity>" "reduced_cost (potentials s) e < 0"
    "walk_betw (abstract_arborescense (spanning_tree s)) (fst e) (p1 @ a # p3) r" "distinct (p1 @ a # p3)"
    "set p1 \<subseteq> \<V> - {r}"
    "\<And>v. v \<in> set p1 \<Longrightarrow> \<not> par_up s v \<and> \<u> (par_edge s v) = \<infinity> \<and> par_edge s v \<in> \<E>"
    "walk_betw (abstract_arborescense (spanning_tree s)) (snd e) (p2 @ a # p3) r" "distinct (p2 @ a # p3)"
    "set p2 \<subseteq> \<V> - {r}"
    "\<And>v. v \<in> set p2 \<Longrightarrow> par_up s v \<and> \<u> (par_edge s v) = \<infinity> \<and> par_edge s v \<in> \<E>"
  using assms
proof(elim ns_unbounded_condE, goal_cases)
  case (1 e in_U \<gamma> sel' p1 p2 isf lv lfw lus)
  obtain mu vu md vd where su: "scan_up s (if in_U then p1 else p2) = (mu, vu)"
    and sd: "scan_down s (if in_U then p2 else p1) = (md, vd)"
    by fastforce
  then have m1: "(if in_U then res_bwd s e else res_fwd s e) = - 1" "mu = - 1" "md = - 1"
    using 1(4)
    by (simp_all add: bottleneck_def Let_def mininf_m1_iff split: if_split_asm)
  have "e \<in> \<E>"
    using inv 1(2)
    by (rule ns_select_SomeD(2))
  then have nU: "\<not> in_U"
    using m1(1) inv res_bwd_nonneg[of s e]
    by auto
  have pp: "get_path_pair (spanning_tree s) (fst e) (snd e) = (p1, p2)"
    using 1(3) \<open>e \<in> \<E>\<close>
    by simp
  then have "set p1 \<subseteq> \<V> - {r}" "set p2 \<subseteq> \<V> - {r}"
    using inv 1(2)
    by (simp_all add: select_path_verts)
  moreover have "\<not> par_up s v \<and> \<u> (par_edge s v) = \<infinity> \<and> par_edge s v \<in> \<E>"
    if "v \<in> set p1" for v
    using that calculation(1) sd nU m1(3) scan_down_all_inf[of p1 vd v] res_down_inf[of v] inv_tree
      ns_invar_tree_edgeD[of s v]
    by auto
  moreover have "par_up s v \<and> \<u> (par_edge s v) = \<infinity> \<and> par_edge s v \<in> \<E>"
    if "v \<in> set p2" for v
    using that calculation(2) su nU m1(2) scan_up_all_inf[of p2 vu v] res_up_inf[of v] inv_tree
      ns_invar_tree_edgeD[of s v]
    by auto
  moreover obtain a p3 where "walk_betw (abstract_arborescense (spanning_tree s)) (fst e) (p1 @ a # p3) r"
    "walk_betw (abstract_arborescense (spanning_tree s)) (snd e) (p2 @ a # p3) r"
    "distinct (p1 @ a # p3)" "distinct (p2 @ a # p3)"
    using inv 1(2) pp get_path_pair_align(1)[of s e in_U \<gamma> sel' p1 p2]
    by blast
  ultimately show ?thesis
    using \<open>e \<in> \<E>\<close> m1(1) nU res_fwd_m1_cap[of e] cap_infinite[of e] inv 1(2)
      ns_select_facts(4)[of s e in_U \<gamma> sel']
    by (intro 1(1)[of e p1 a p3 p2]) (simp_all add: entering_edge_def)
qed

subsection \<open>The negative infinite-capacity fundamental circuit\<close>

lemma foldr_c_sum_list: "foldr (\<lambda>e. (+) (\<c> e)) D 0 = (\<Sum>ee\<leftarrow>D. \<c> ee)"
  by (induct D) auto

text \<open>A tree path @{term \<open>P @ a # p3\<close>} from @{term u} to the root: the parent edges of @{term P}
      form a directed walk from @{term u} up to @{term a} when they all point upwards, and one from
      @{term a} down to @{term u} when they all point downwards.\<close>

context
  fixes u P a p3
  assumes path: "walk_betw (abstract_arborescense (spanning_tree s)) u (P @ a # p3) r" "distinct (P @ a # p3)"
    "set P \<subseteq> \<V> - {r}"
begin

lemma path_succ_par_vx: "Suc i < length P \<Longrightarrow> par_vx s (P ! i) = P ! Suc i"
  using walk_succ_is_par_vx[OF inv path(1,2), of i] subsetD[OF path(3) nth_mem[of i P]]
  by (simp add: nth_append)

lemma path_last_par_vx: "P \<noteq> [] \<Longrightarrow> par_vx s (last P) = a"
  using walk_succ_is_par_vx[OF inv path(1,2), of "length P - 1"] subsetD[OF path(3) last_in_set[of P]]
  by (simp add: nth_append last_conv_nth)

lemma path_ends_V: "u \<in> \<V>" "a \<in> \<V>"
  using walk_in_Vs[OF path(1)] general(4)[OF inv_impl(7)] hd_in_set[of "P @ a # p3"]
    walk_between_nonempty_pathD(3)[OF path(1)]
  by auto

lemma path_edges: "set (map make_pair (map (par_edge s) P)) \<subseteq> make_pair ` \<E>"
  using path(3) inv_tree ns_invar_tree_edgeD[of s]
  by (simp only: set_map) (intro image_mono; blast)

lemma up_path_awalk:
  "(\<And>v. v \<in> set P \<Longrightarrow> par_up s v) \<Longrightarrow>
    awalk (make_pair ` \<E>) u (map make_pair (map (par_edge s) P)) a"
  using up_walk_cas[OF path(3) _ path_succ_par_vx _ path_last_par_vx] path_ends_V path_edges
    walk_between_nonempty_pathD(3)[OF path(1)]
  by (cases P) (auto simp: awalk_def)

lemma dn_path_awalk:
  "(\<And>v. v \<in> set P \<Longrightarrow> \<not> par_up s v) \<Longrightarrow>
    awalk (make_pair ` \<E>) a (map make_pair (map (par_edge s) (rev P))) u"
  using dn_walk_cas[OF path(3) _ path_succ_par_vx _ path_last_par_vx] path_ends_V path_edges
    walk_between_nonempty_pathD(3)[OF path(1)]
  by (cases P) (auto simp: awalk_def)

end

text \<open>The fundamental circuit of the entering edge then consists of infinite-capacity edges only, and its
      cost telescopes to the (negative) reduced cost of the entering edge.\<close>

lemma ns_unbounded_neg_cycle: "ns_unbounded_cond s \<Longrightarrow> has_neg_infty_cycle make_pair \<E> \<c> \<u>"
proof(elim unbounded_circuit, goal_cases)
  case (1 e p1 p2 a p3)
  define D where "D = map (par_edge s) (rev p1) @ e # map (par_edge s) p2"
  have "(\<Sum>ee\<leftarrow>D. \<c> ee) = reduced_cost (potentials s) e"
    using 1(4-11) inv up_cost_sum[of s "snd e" p2 a p3 1] down_cost_sum[of s "fst e" p1 a p3 1]
    by (simp add: D_def comp_def reduced_cost_def cong: map_cong flip: rev_map)
  then have "foldr (\<lambda>e. (+) (\<c> e)) D 0 < 0"
    using 1(3)
    by (simp add: foldr_c_sum_list)
  moreover have "awalk (make_pair ` \<E>) a (map make_pair (map (par_edge s) (rev p1))) (fst e)"
    "awalk (make_pair ` \<E>) (snd e) (map make_pair (map (par_edge s) p2)) a"
    using 1(4-11)
    by (blast intro: dn_path_awalk up_path_awalk)+
  then have "closed_w (make_pair ` \<E>) (map make_pair D)"
    unfolding closed_w_def D_def map_append list.map(2)
    using 1(1)
    by (intro exI[of _ a] conjI awalk_appendI) (auto simp: awalk_Cons_iff make_pair_def)
  ultimately show ?case
    using 1(1,2,7,11)
    by (intro has_neg_infty_cycleI[where D = D]) (auto simp: D_def)
qed

end

subsection \<open>Total correctness of the loop\<close>

text \<open>The three ingredients --- termination, the success-branch optimality and the unbounded-branch
      circuit --- are assembled into statements about @{const ns_loop}, using the case analysis
      @{thm [source] ns_loop_cases}, the one-step unfoldings @{thm [source] ns_loop_simps}, the
      induction @{thm [source] ns_loop_induct} and the branch lemmas @{thm [source] invar_holds_intros}
      and @{thm [source] termination_intros}. The per-step decrease relation @{const ns_less} is
      well-founded: it embeds into the lexicographic product of the (finite) tree-count and the
      violation count.\<close>

lemma wf_ns_less: "wf {(s', s). ns_less s' s}"
  by (rule wf_subset[of "inv_image (less_than <*lex*> less_than) (\<lambda>s. (card (possible_trees s), ns_violation s))"])
     (auto simp: ns_less_def)

lemma ns_loop_dom_of_invar: "ns_invar s \<Longrightarrow> ns_loop_dom s"
proof(induction s rule: wf_induct_rule[OF wf_ns_less])
  case (1 s)
  then show ?case
    by (cases s rule: ns_loop_cases)
       (auto intro: ns_loop_dom_success ns_loop_dom_unbounded ns_loop_dom_flip ns_loop_dom_pivot
                    invar_holds_intros termination_intros)
qed

text \<open>Result classification, by induction along the loop's own recursion: the two recursive branches
      preserve the invariant, the two terminal branches are closed by @{thm [source] ns_success_optimal}
      and @{thm [source] ns_unbounded_neg_cycle}.\<close>

lemma ns_loop_correct_ret_1:
  assumes "ns_loop_dom s"
  shows "\<lbrakk>ns_invar s; return (ns_loop s) = success\<rbrakk>
    \<Longrightarrow> is_Opt b (ns_flow_of (ns_loop s))"
proof(induction rule: ns_loop_induct[OF assms])
  case (1 s)
  then show ?case
    using ns_success_optimal[of s]
    by (cases s rule: ns_loop_cases)
       (auto simp: ns_loop_simps ns_optimal_def ns_unbounded_upd_def comp_def intro: invar_holds_intros)
qed

lemma ns_loop_correct_ret_2:
  assumes "ns_loop_dom s"
  shows "\<lbrakk>ns_invar s; return (ns_loop s) = unbounded\<rbrakk>
    \<Longrightarrow> has_neg_infty_cycle make_pair \<E> \<c> \<u>"
proof(induction rule: ns_loop_induct[OF assms])
  case (1 s)
  then show ?case
    by (cases s rule: ns_loop_cases)
       (auto simp: ns_loop_simps ns_optimal_def ns_unbounded_upd_def intro: ns_unbounded_neg_cycle invar_holds_intros)
qed

text \<open>\<^bold>\<open>Total correctness.\<close> For every state meeting the loop invariant the algorithm
      terminates, and its terminal flag is faithful: @{const unbounded} exhibits a negative
      infinite-capacity cycle (so the instance has no finite optimum), and @{const success} certifies
      that the returned flow is a minimum-cost @{term b}-flow.\<close>

lemma ns_loop_correct:
  assumes "ns_invar s"
  shows "ns_loop_dom s"
    "return (ns_loop s) = unbounded \<Longrightarrow> has_neg_infty_cycle make_pair \<E> \<c> \<u>"
    "return (ns_loop s) = success \<Longrightarrow> is_Opt b (ns_flow_of (ns_loop s))"
  using assms ns_loop_dom_of_invar ns_loop_correct_ret_1 ns_loop_correct_ret_2
  by blast+

end

section \<open>A constructed initial state\<close>

text \<open>The correctness theorem @{thm [source] network_simplex.ns_loop_correct} presupposes an
      input state satisfying the loop invariant @{const network_simplex.ns_invar}. We package that
      presupposition as a locale extending @{locale network_simplex_spec}: it fixes the seven starting
      components (flow store, potential store, abstract tree, parent-edge array, direction array,
      edge-state tag array and entering-edge selector) and assumes exactly the componentwise
      unfoldings of the @{const network_simplex.ns_invar} conjuncts:
      \<^item> \<^bold>\<open>data-structure well-formedness\<close> of each store and of the abstract tree;
      \<^item> \<^bold>\<open>feasible \<open>b\<close>-flow\<close> (@{term init_bflow});
      \<^item> \<^bold>\<open>spanning-tree partition\<close> of @{term \<open>\<E>\<close>} into the tree edges, @{term L} and
        @{term U} (@{term init_partition});
      \<^item> \<^bold>\<open>flow and potential fit the partition\<close> (@{term init_flow_fits},
        @{term init_pot_fits});
      \<^item> \<^bold>\<open>strict feasibility on the tree\<close> (@{term init_strict});
      \<^item> \<^bold>\<open>array $\leftrightarrow$ tree correspondence\<close>: every parent edge is a graph edge
        oriented by the direction flag, its other endpoint is the predecessor towards the root, and
        the parent array denotes the abstract arborescence (@{term init_tree_corr});
      \<^item> \<^bold>\<open>self-loops\<close> carry zero flow or are saturated, by cost (@{term init_selfloop}).\<close>

text \<open>The initial-basis specification locale fixes the seven starting components and
      builds the concrete starting state @{term init_state}. It carries no assumptions.\<close>

locale network_simplex_init_spec =
  network_simplex_spec where flow_lookup = flow_lookup and pot_lookup = pot_lookup
    and parent_lookup = parent_lookup and dir_lookup = dir_lookup and es_lookup = es_lookup
    and sel_select = sel_select and swap_edge = swap_edge
  for flow_lookup :: "'farr \<Rightarrow> 'edge \<Rightarrow> ('n::linordered_idom)" and pot_lookup :: "'parr \<Rightarrow> 'a \<Rightarrow> 'p"
    and parent_lookup :: "'pearr \<Rightarrow> 'a \<Rightarrow> 'edge" and dir_lookup :: "'darr \<Rightarrow> 'a \<Rightarrow> bool"
    and es_lookup :: "'earr \<Rightarrow> 'edge \<Rightarrow> edge_tag"
    and sel_select :: "'selector \<Rightarrow> 'parr \<Rightarrow> 'earr \<Rightarrow> ('edge \<times> bool \<times> 'r \<times> 'selector) option"
    and swap_edge :: "'arbor \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'arbor" +
  fixes init_flow :: "'farr" and init_pot :: "'parr" and init_tree :: "'arbor"
    and init_parent :: "'pearr" and init_dir :: "'darr" and init_edge_state :: "'earr"
    and init_sel :: "'selector"
begin

text \<open>The constructed starting state, assembled from the fixed components with the loop still running.\<close>

definition "init_state \<equiv>
  \<lparr> current_flow = init_flow, potentials = init_pot,
    spanning_tree = init_tree, parent_edge = init_parent,
    edge_dir = init_dir, edge_state = init_edge_state,
    edge_sel = init_sel,
    return = notyetterm \<rparr>"

end

text \<open>The initial-basis proof locale adds the well-formedness / feasibility assumptions on
      the fixed components and derives total correctness for the constructed state.\<close>

locale network_simplex_init = network_simplex + network_simplex_init_spec +
  assumes
      init_flow_invar:   "flow_invar init_flow"
  and init_pot_valid:    "pot_valid init_pot"
  and init_parent_invar: "parent_invar init_parent"
  and init_dir_invar:    "dir_invar init_dir"
  and init_edge_state_invar: "es_invar init_edge_state"
  and init_sel_invar:    "sel_invar init_sel"
  and init_tree_invar:   "arborescense_invar init_tree"
  and init_bflow:        "(h \<circ> flow_lookup init_flow) is b flow"
  and init_partition:
        "spanning_tree_partition r (parent_lookup init_parent ` (\<V> - {r}))
             ({e \<in> \<E>. fst e \<noteq> snd e \<and> es_lookup init_edge_state e = InL} \<union> ns_selfloops_L)
             ({e \<in> \<E>. fst e \<noteq> snd e \<and> es_lookup init_edge_state e = InU} \<union> ns_selfloops_U)"
  and init_flow_fits:
        "flow_fits_spanning_tree_partition (parent_lookup init_parent ` (\<V> - {r}))
             {e \<in> \<E>. fst e \<noteq> snd e \<and> es_lookup init_edge_state e = InL}
             {e \<in> \<E>. fst e \<noteq> snd e \<and> es_lookup init_edge_state e = InU}
             (h \<circ> flow_lookup init_flow)"
  and init_pot_fits:
        "potential_fits_spanning_tree_partition r (parent_lookup init_parent ` (\<V> - {r}))
             (abstract_pot init_pot)"
  and init_strict:
        "\<forall> v \<in> \<V> - {r}.
           if dir_lookup init_dir v
           then ereal (h (flow_lookup init_flow (parent_lookup init_parent v))) < \<u> (parent_lookup init_parent v)
           else flow_lookup init_flow (parent_lookup init_parent v) > 0"
  and init_tree_corr:
        "(\<forall> v \<in> \<V> - {r}.
             parent_lookup init_parent v \<in> \<E>
           \<and> (if dir_lookup init_dir v then fst (parent_lookup init_parent v) = v
                                        else snd (parent_lookup init_parent v) = v)
           \<and> (\<exists> q. distinct (v # (if dir_lookup init_dir v then snd (parent_lookup init_parent v)
                                                            else fst (parent_lookup init_parent v)) # q)
                   \<and> walk_betw (abstract_arborescense init_tree) v
                       (v # (if dir_lookup init_dir v then snd (parent_lookup init_parent v)
                                                       else fst (parent_lookup init_parent v)) # q) r))
         \<and> (\<lambda> e. {fst e, snd e}) ` (parent_lookup init_parent ` (\<V> - {r}))
             = abstract_arborescense init_tree"
  and init_selfloop:
        "\<forall> e \<in> \<E>. fst e = snd e \<longrightarrow> (0 \<le> \<c> e \<longrightarrow> flow_lookup init_flow e = 0)
                                  \<and> (\<c> e < 0 \<longrightarrow> ereal (h (flow_lookup init_flow e)) = \<u> e)"
begin

text \<open>The assembled state satisfies the packaged loop invariant: the componentwise assumptions above
      are exactly the unfoldings of the seven @{const network_simplex.ns_invar} conjuncts (the
      only bridging step is a case split on the direction flag inside the tree-correspondence
      conjunct).\<close>

lemma init_state_invar: "ns_invar init_state"
proof(rule ns_invarI)
  show "ns_invar_tree init_state"
    using init_tree_corr
    by (simp only: ns_invar_tree_def par_vx_def par_up_def par_edge_def init_state_def
                   network_simplex_state.select_convs simp_thms)
       (erule conjunct1)
qed (use init_flow_invar init_pot_valid init_parent_invar init_dir_invar init_edge_state_invar init_sel_invar
       init_tree_invar init_bflow init_partition init_flow_fits init_pot_fits init_strict init_selfloop in
     \<open>simp_all add: ns_invar_impl_def ns_invar_bflow_def ns_invar_partition_def ns_invar_flow_fits_def
       ns_invar_pot_fits_def ns_invar_strict_def ns_invar_selfloop_def ns_L_of_def ns_U_of_def comp_def
       par_up_def par_edge_def init_state_def\<close>)

text \<open>Total correctness specialised to the constructed initial state: the loop terminates on it, an
      @{term unbounded} result witnesses an infinite-capacity negative circuit, and a @{term success}
      result is a minimum-cost \<open>b\<close>-flow.\<close>

lemma network_simplex_correct:
  "ns_loop_dom init_state"
  "return (ns_loop init_state) = unbounded \<Longrightarrow> has_neg_infty_cycle make_pair \<E> \<c> \<u>"
  "return (ns_loop init_state) = success \<Longrightarrow> is_Opt b (ns_flow_of (ns_loop init_state))"
  using init_state_invar ns_loop_correct
  by blast+

end

end