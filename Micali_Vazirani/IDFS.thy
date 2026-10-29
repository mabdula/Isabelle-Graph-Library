theory IDFS
  imports DFS_Avoid Layered_Digraph
begin

provenance human

text \<open>The incremental DFS assumed by the DDFS development, stated ops-generically over the
executable ADT (\<^locale>\<open>Pair_Graph_Specs\<close> + \<^locale>\<open>Set2\<close>), so that the very same
witness realises the DDFS interface under any backend --- plain sets (mathematical reading)
or RBTs (executable reading, see DDFS_Example.thy). The engine is \<^locale>\<open>DFS_avoid\<close>
itself an instance of \<^locale>\<open>DFS_skel\<close>; this theory wraps it, bridges the DDFS
vocabulary (\<^term>\<open>dpath\<close> \<equiv> \<^term>\<open>Vwalk.vwalk\<close>) and exports the DDFS-facing clauses
verbatim.\<close>

section \<open>Ops-generic witness locale\<close>

locale IDFS_witness =
  Graph: Pair_Graph_Specs where lookup = lookup +
  set_ops: Set2 vset_empty vset_delete _ t_set vset_inv insert
for lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option" +
fixes G :: "'adjmap" and lev :: "'v \<Rightarrow> nat"
  assumes layered_input: "Graph.layered_graph_input G lev"
begin

text \<open>Recovery of the historical fact names and shapes from the single
summarising assumption; every existing citation of wf_graph/L1/L2/L3 below is
unaffected.\<close>

lemma wf_graph: "Graph.graph_inv G" "Graph.finite_graph G" "Graph.finite_vsets G"
  using layered_input by (elim Graph.layered_graph_inputE; blast)+

lemma L1: "(v, v') \<in> Graph.digraph_abs G \<Longrightarrow> lev v' < lev v"
  using layered_input by (elim Graph.layered_graph_inputE layered_dgraphE) blast

lemma L2: "finite (dVs (Graph.digraph_abs G))"
  using layered_input by (elim Graph.layered_graph_inputE layered_dgraphE) blast

lemma L3: "v \<in> dVs (Graph.digraph_abs G) \<Longrightarrow>
           \<exists>p v'. p \<noteq> [] \<and> dpath_bet (Graph.digraph_abs G) p v v' \<and> lev v' = 0"
  using layered_input by (elim Graph.layered_graph_inputE layered_dgraphE) blast
(* abbreviation "dG \<equiv> Graph.digraph_abs G" -- removed to avoid clash with DDFS's identical abbreviation *)

text \<open>Head of the given stack is checked against the avoid and visited sets (via the Set2
isin operation) and dropped if it lies in either --- the algorithm backtracks over it,
matching the DDFS locale comment. Under IDFS_pre the inputs are already subset of dVs of the
digraph, so no intersection with dVs restriction is needed before seeding: the engine's vis0
equals the input visited and the final visited slot already contains the input visited.\<close>

definition "IDFS_stack0 avoid vis p =
   (if p \<noteq> [] \<and> (isin avoid (hd p) \<or> isin vis (hd p)) then tl p else p)"

text \<open>The DDFS-facing IDFS, wrapper over \<^term>\<open>DFS_avoid.avoid_final_state\<close> at the same
ops. Returns the result slot and the final visited slot (which is monotone in the input
visited, by the lemma DFS_avoid_vis_mono from the DFS_avoid locale).\<close>

definition "IDFS_impl P avoid p vis =
   (let st = DFS_avoid.avoid_final_state_impl
        insert isin sel vset_empty union diff lookup
        G (IDFS_stack0 avoid vis p) vis avoid P
    in (DFS_avoid_state.ret st, DFS_avoid_state.visited st))"

section \<open>DDFS-facing properties (ops-generic)\<close>

text \<open>The witness suite, stated verbatim as the DDFS locale clauses with the input
precondition IDFS_pre avoid visited (see DDFS.thy). The proofs specialise
DFS_avoid_thms at the SAME ops for the specific call (stack0 / vis0 / avoid /
Pv) and push the already-ops-generic DFS_avoid exports through; no t_set = id
collapse is needed (the boundary is cleaner than the former plain-set version).\<close>

context
  fixes P :: "'v \<Rightarrow> bool" and avoid vis :: "'vset" and p :: "'v list"
  assumes p_path: "dpath (Graph.digraph_abs G) (rev p)"
      and p_dist: "distinct p"
      and av_inv:  "vset_inv avoid" "vset_inv vis"
      and av_dVs:  "t_set avoid \<subseteq> dVs (Graph.digraph_abs G)" "t_set vis \<subseteq> dVs (Graph.digraph_abs G)"
begin

text \<open>The four input preconditions above are the expansion of IDFS_pre avoid
vis (defined in the DDFS locale). They are stated directly
here rather than as IDFS_pre avoid vis because IDFS_witness is
NOT a sublocale of DDFS (the inheritance goes the other way:
DDFS_layered = IDFS_witness and DDFS_layered \<subseteq> DDFS), so
IDFS_pre is out of scope inside IDFS_witness. The capstone sublocale
(Edit 4) bridges the two: each DDFS clause carries IDFS_pre avoid visited (one
premise); the matching show unfolds it to these four conjuncts via
IDFS_pre_def and applies the suite theorem.\<close>

lemma pre_inv: "vset_inv avoid" "vset_inv vis"
  and pre_dVs: "t_set avoid \<subseteq> dVs (Graph.digraph_abs G)" "t_set vis \<subseteq> dVs (Graph.digraph_abs G)"
  using av_inv av_dVs by auto

text \<open>Stack0 case lemma (ops-generic; list-level, so identical to the plain-set form).\<close>

lemma IDFS_stack0_cases:
  "(IDFS_stack0 avoid vis p = p \<and> (p = [] \<or> hd p \<notin> t_set avoid \<union> t_set vis)) \<or>
   (IDFS_stack0 avoid vis p = tl p \<and> p \<noteq> [] \<and> hd p \<in> t_set avoid \<union> t_set vis)"
  using pre_inv
  unfolding IDFS_stack0_def
  by (cases p)
     (auto simp: Graph.vset.set.set_isin)

text \<open>Two-step interpretation (mirror DFS_Reach_Skel.thy): first av: DFS_avoid
(base --- no axioms; gives av.avoid_final_state, av.DFS_avoid_axioms as a
definition), then av: DFS_avoid_thms (with the axioms fact; gives the exports).\<close>

interpretation av: DFS_avoid
  where lookup = lookup and update = update and adjmap_inv = adjmap_inv
    and vset_empty = vset_empty and vset_delete = vset_delete and vset_inv = vset_inv
    and empty = empty and delete = delete and insert = insert and isin = isin
    and t_set = t_set and sel = sel
    and union = union and inter = inter and diff = diff
    and G = G and stack0 = "IDFS_stack0 avoid vis p"
    and vis0 = vis and avoid = avoid and Pv = P and level = lev
  by unfold_locales

abbreviation "Rst \<equiv> av.avoid_final_state"

lemma av_axioms: av.DFS_avoid_axioms
  unfolding av.DFS_avoid_axioms_def
proof (intro conjI)
  show "Graph.graph_inv G" "Graph.finite_graph G" "Graph.finite_vsets G"
    using wf_graph by auto
  show "vset_inv avoid" "vset_inv vis"
    using pre_inv by auto
  show "t_set avoid \<subseteq> dVs (Graph.digraph_abs G)" "t_set vis \<subseteq> dVs (Graph.digraph_abs G)"
    using pre_dVs by auto
  show "Vwalk.vwalk (Graph.digraph_abs G) (rev (IDFS_stack0 avoid vis p))"
  proof -
    have w: "Vwalk.vwalk (Graph.digraph_abs G) (rev p)" using p_path by simp
    show ?thesis
    proof (cases "IDFS_stack0 avoid vis p = p")
      case True thus ?thesis using w by simp
    next
      case False
      hence s: "IDFS_stack0 avoid vis p = tl p" and ne: "p \<noteq> []"
        using IDFS_stack0_cases by auto
      have "rev p = rev (tl p) @ [hd p]" using ne by (cases p) auto
      hence "Vwalk.vwalk (Graph.digraph_abs G) (rev (tl p))" using w append_vwalk_pref by fastforce
      thus ?thesis using s by simp
    qed
  qed
  show "distinct (IDFS_stack0 avoid vis p)"
    using p_dist by (cases p) (auto simp: IDFS_stack0_def)
  show "\<forall>u v. (u, v) \<in> (Graph.digraph_abs G) \<longrightarrow> lev v < lev u" using L1 by auto
qed

interpretation av: DFS_avoid_thms
  where lookup = lookup and update = update and adjmap_inv = adjmap_inv
    and vset_empty = vset_empty and vset_delete = vset_delete and vset_inv = vset_inv
    and empty = empty and delete = delete and insert = insert and isin = isin
    and t_set = t_set and sel = sel
    and union = union and inter = inter and diff = diff
    and G = G and stack0 = "IDFS_stack0 avoid vis p"
    and vis0 = vis and avoid = avoid and Pv = P and level = lev
  using av_axioms
  by unfold_locales (auto simp: av.DFS_avoid_axioms_def)

text \<open>Unfold IDFS_impl (the fully-qualified call from Edit 1) against the
interpreted final state Rst = av.avoid_final_state. The two are the same
av.DFS_skel avoid_initial_state once the interpretation's op/G/call-arg
instantiation is unfolded.\<close>

lemma IDFS_impl_pair:
  "IDFS_impl P avoid p vis =
     (DFS_avoid_state.ret Rst, DFS_avoid_state.visited Rst)"
  by (simp add: IDFS_impl_def Let_def av.avoid_final_state_impl_same)

text \<open>The final visited slot stays inside dVs of the digraph (used by the closure/complete
soundness steps that need a dVs-side fact).\<close>

lemma slot_dVs: "t_set (DFS_avoid_state.visited Rst) \<subseteq> dVs (Graph.digraph_abs G)"
  using av.DFS_avoid_visited_dVs by (simp add: av.avoid_final_state_def)

text \<open>Witness suite --- the DDFS locale clauses verbatim (with IDFS_pre). Numbering
matches the DDFS locale assumptions. Theorems are conditional on p_path/p_dist/
pre from the enclosing context.\<close>

theorem IDFS_vis_works_1:
  assumes "IDFS_impl P avoid p vis = (ret_p, vis')" "v \<in> t_set vis' - t_set vis"
  shows "\<not> P v"
proof -
  from assms(1) have vis': "vis' = DFS_avoid_state.visited Rst"
                  and ret: "ret_p = DFS_avoid_state.ret Rst"
    by (auto simp: IDFS_impl_pair)
  from assms(2) vis' have "v \<in> t_set (DFS_avoid_state.visited Rst) - t_set vis" by simp
  then show ?thesis by (rule av.DFS_avoid_vis_new_notP)
qed

theorem IDFS_vis_works_2:
  assumes "IDFS_impl P avoid p vis = (ret_p, vis')"
  shows "(t_set vis' - t_set vis) \<inter> t_set avoid = {}"
proof -
  from assms have vis': "vis' = DFS_avoid_state.visited Rst"
    by (auto simp: IDFS_impl_pair)
  have "(t_set (DFS_avoid_state.visited Rst) - t_set vis) \<inter> t_set avoid = {}"
    by (rule av.DFS_avoid_vis_new_avoid)
  with vis' show ?thesis by simp
qed

theorem IDFS_vis_works_3:
  assumes "IDFS_impl P avoid p vis = (ret_p, vis')"
  shows "t_set vis \<subseteq> t_set vis'"
proof -
  from assms have vis': "vis' = DFS_avoid_state.visited Rst"
    by (auto simp: IDFS_impl_pair)
  have "t_set vis \<subseteq> t_set (DFS_avoid_state.visited Rst)" by (rule av.DFS_avoid_vis_mono)
  with vis' show ?thesis by simp
qed

theorem IDFS_vis_works_4:
  assumes "IDFS_impl P avoid p vis = (ret_p, vis')"
  shows "vset_inv vis'"
proof -
  from assms have vis': "vis' = DFS_avoid_state.visited Rst"
    by (auto simp: IDFS_impl_pair)
  have inv: "av.invar_vis_vset Rst"
    using av.final_invars by (simp add: av.avoid_final_state_def)
  with vis' show ?thesis by (simp add: av.invar_vis_vset_def)
qed

theorem IDFS_closed_None:
  assumes "IDFS_impl P avoid p vis = (None, vis')"
      and vnew: "v \<in> t_set vis' - t_set vis" and edge: "(v, w) \<in> Graph.digraph_abs G"
  shows "w \<in> t_set avoid \<union> t_set vis'"
proof -
  from assms(1) have retN: "DFS_avoid_state.ret Rst = None"
                   and vis': "vis' = DFS_avoid_state.visited Rst"
    by (auto simp: IDFS_impl_pair)
  have empty: "stack Rst = []"
    using av.final_ret_char retN by (simp add: av.avoid_final_state_def)
  from vnew vis' have vnR: "v \<in> t_set (DFS_avoid_state.visited Rst) - t_set vis" by simp
  have "w \<in> t_set avoid \<union> t_set (DFS_avoid_state.visited Rst) \<union> set (stack Rst)"
    using vnR edge by (rule av.DFS_avoid_closure)
  with empty vis' show ?thesis by auto
qed

theorem IDFS_closed_Some:
  assumes "IDFS_impl P avoid p vis = (Some p', vis')"
      and vnew: "v \<in> t_set vis' - t_set vis" and edge: "(v, w) \<in> Graph.digraph_abs G"
  shows "w \<in> t_set avoid \<union> t_set vis' \<union> set p'"
proof -
  from assms(1) have retS: "DFS_avoid_state.ret Rst = Some p'"
                    and vis': "vis' = DFS_avoid_state.visited Rst"
    by (auto simp: IDFS_impl_pair)
  have pstk: "p' = stack Rst"
    using retS by (rule av.DFS_avoid_sound_stack)
  with vis' vnew edge av.DFS_avoid_closure show ?thesis by auto
qed

theorem IDFS_complete_w:
  assumes "IDFS_impl P avoid p vis = (None, vis')"
  shows "set p - t_set avoid \<subseteq> t_set vis'"
proof
  fix x assume x: "x \<in> set p - t_set avoid"
  from assms have retN: "DFS_avoid_state.ret Rst = None"
                  and vis': "vis' = DFS_avoid_state.visited Rst"
    by (auto simp: IDFS_impl_pair)
  have compl: "set (IDFS_stack0 avoid vis p) - t_set avoid
                 \<subseteq> t_set (DFS_avoid_state.visited Rst)"
    using retN by (rule av.DFS_avoid_complete)
  have "x \<in> t_set vis'"
  proof (cases "x \<in> set (IDFS_stack0 avoid vis p)")
    case True
    with x compl show ?thesis by (auto simp: vis')
  next
    case False
    have "IDFS_stack0 avoid vis p = tl p \<and> p \<noteq> [] \<and> hd p \<in> t_set avoid \<union> t_set vis"
      using IDFS_stack0_cases
    proof (elim disjE)
      assume a: "IDFS_stack0 avoid vis p = p \<and> (p = [] \<or> hd p \<notin> t_set avoid \<union> t_set vis)"
      have "x \<in> set p" using x by auto
      with a False show ?thesis by auto
    next
      assume "IDFS_stack0 avoid vis p = tl p \<and> p \<noteq> [] \<and> hd p \<in> t_set avoid \<union> t_set vis"
      then show ?thesis by auto
    qed
    then have s: "IDFS_stack0 avoid vis p = tl p" and h: "hd p \<in> t_set avoid \<union> t_set vis" and ne: "p \<noteq> []"
      by auto
    have "x = hd p" using x False s ne by (cases p) auto
    with h x have "x \<in> t_set vis" by auto
    hence "x \<in> t_set (DFS_avoid_state.visited Rst)" using av.DFS_avoid_vis_mono by auto
    with vis' show ?thesis by simp
  qed
  thus "x \<in> t_set vis'" .
qed

theorem IDFS_sound_1:
  assumes "IDFS_impl P avoid p vis = (Some p', vis')"
  shows "dpath (Graph.digraph_abs G) (rev p')"
proof -
  from assms have retS: "DFS_avoid_state.ret Rst = Some p'"
    by (auto simp: IDFS_impl_pair)
  have "Vwalk.vwalk (Graph.digraph_abs G) (rev p')" by (rule av.DFS_avoid_sound_vwalk[OF retS])
  then show ?thesis by simp
qed

theorem IDFS_sound_2:
  assumes "IDFS_impl P avoid p vis = (Some p', vis')"
  shows "distinct p'"
proof -
  from assms have retS: "DFS_avoid_state.ret Rst = Some p'" by (auto simp: IDFS_impl_pair)
  then show ?thesis by (rule av.DFS_avoid_sound_distinct)
qed

theorem IDFS_sound_3:
  assumes "IDFS_impl P avoid p vis = (Some p', vis')"
  shows "(set p' - set (tl p)) \<inter> (t_set avoid \<union> t_set vis') = {}"
proof (rule ccontr)
  assume "(set p' - set (tl p)) \<inter> (t_set avoid \<union> t_set vis') \<noteq> {}"
  then obtain x where x: "x \<in> set p'" "x \<notin> set (tl p)" "x \<in> t_set avoid \<union> t_set vis'"
    by auto
  from assms have retS: "DFS_avoid_state.ret Rst = Some p'"
                    and vis': "vis' = DFS_avoid_state.visited Rst"
    by (auto simp: IDFS_impl_pair)
  have pstk: "p' = stack Rst" using retS by (rule av.DFS_avoid_sound_stack)
  have nd: "(set p' - set (IDFS_stack0 avoid vis p))
                \<inter> (t_set avoid \<union> t_set (DFS_avoid_state.visited Rst)) = {}"
    using retS by (rule av.DFS_avoid_sound_new_disjoint)
  show False
  proof (cases "x \<in> set (IDFS_stack0 avoid vis p)")
    case False
    moreover have "x \<in> t_set avoid \<union> t_set (DFS_avoid_state.visited Rst)"
      using x(3) vis' by simp
    ultimately show False using nd x(1) by auto
  next
    case True
    have "IDFS_stack0 avoid vis p = p"
    proof (rule ccontr)
      assume "IDFS_stack0 avoid vis p \<noteq> p"
      with IDFS_stack0_cases have "IDFS_stack0 avoid vis p = tl p" by auto
      with True have "x \<in> set (tl p)" by simp
      with x(2) show False by auto
    qed
    then have eq: "IDFS_stack0 avoid vis p = p" by simp
    have xp: "x \<in> set p" using True eq by simp
    have ne: "p \<noteq> []" using xp by auto
    have h_not: "hd p \<notin> t_set avoid \<union> t_set vis"
    proof
      assume "hd p \<in> t_set avoid \<union> t_set vis"
      with IDFS_stack0_cases eq have "IDFS_stack0 avoid vis p = tl p" by auto
      with eq have "p = tl p" by simp
      with ne show False by (cases p) auto
    qed
    have xhd: "x = hd p" using True eq x(2) ne by (cases p) auto
    show False
    proof (cases "x \<in> t_set avoid")
      case True thus False using xhd h_not ne by auto
    next
      case False_av: False
      hence xv: "x \<in> t_set (DFS_avoid_state.visited Rst)" using x(3) xhd vis' by auto
      have xstk: "x \<in> set (stack Rst)" using pstk x(1) by simp
      hence "x \<in> t_set (DFS_avoid_state.visited Rst) \<inter> set (stack Rst)" using xv xstk by auto
      then have "x \<in> t_set vis"
        using av.DFS_avoid_visited_stack by auto
      with xhd h_not ne show False by auto
    qed
  qed
qed

theorem IDFS_sound_4:
  assumes "IDFS_impl P avoid p vis = (Some p', vis')"
  shows "set p - set p' - t_set avoid \<subseteq> t_set vis'"
proof
  fix x assume x: "x \<in> set p - set p' - t_set avoid"
  from assms have retS: "DFS_avoid_state.ret Rst = Some p'"
                    and vis': "vis' = DFS_avoid_state.visited Rst"
    by (auto simp: IDFS_impl_pair)
  have sub: "set (IDFS_stack0 avoid vis p) - set p' - t_set avoid
               \<subseteq> t_set (DFS_avoid_state.visited Rst)"
    using retS by (rule av.DFS_avoid_sound_sub)
  show "x \<in> t_set vis'"
  proof (cases "x \<in> set (IDFS_stack0 avoid vis p)")
    case True
    with sub x vis' show ?thesis by auto
  next
    case False
    have s: "IDFS_stack0 avoid vis p = tl p" and h: "hd p \<in> t_set avoid \<union> t_set vis" and ne: "p \<noteq> []"
    proof -
      have "IDFS_stack0 avoid vis p = tl p \<and> hd p \<in> t_set avoid \<union> t_set vis \<and> p \<noteq> []"
        using IDFS_stack0_cases
      proof (elim disjE)
        assume a: "IDFS_stack0 avoid vis p = p \<and> (p = [] \<or> hd p \<notin> t_set avoid \<union> t_set vis)"
        have "x \<in> set p" using x by auto
        with a False show ?thesis by auto
      next
        assume "IDFS_stack0 avoid vis p = tl p \<and> p \<noteq> [] \<and> hd p \<in> t_set avoid \<union> t_set vis"
        then show ?thesis by auto
      qed
      thus "IDFS_stack0 avoid vis p = tl p" and h: "hd p \<in> t_set avoid \<union> t_set vis" and ne: "p \<noteq> []"
        by auto
    qed
    have "x = hd p" using x False s ne by (cases p) auto
    with h x have "x \<in> t_set vis" by auto
    hence "x \<in> t_set (DFS_avoid_state.visited Rst)" using av.DFS_avoid_vis_mono by auto
    with vis' show ?thesis by simp
  qed
qed

theorem IDFS_sound_5:
  assumes "IDFS_impl P avoid p vis = (Some p', vis')"
      and tlP: "\<And>v. v \<in> set (tl p) \<Longrightarrow> \<not> P v" and v: "v \<in> set (tl p')"
  shows "\<not> P v"
proof -
  from assms(1) have retS: "DFS_avoid_state.ret Rst = Some p'" by (auto simp: IDFS_impl_pair)
  have tl_char: "v \<in> set (IDFS_stack0 avoid vis p) \<or> \<not> P v"
    using av.DFS_avoid_sound_tl_notP[OF retS v] by blast
  show ?thesis
  proof (cases "v \<in> set (IDFS_stack0 avoid vis p)")
    case False
    with tl_char show ?thesis by simp
  next
    case True: True
    from IDFS_stack0_cases have
      disj: "(IDFS_stack0 avoid vis p = p \<and> (p = [] \<or> hd p \<notin> t_set avoid \<union> t_set vis)) \<or>
             (IDFS_stack0 avoid vis p = tl p \<and> p \<noteq> [] \<and> hd p \<in> t_set avoid \<union> t_set vis)" .
    show ?thesis
    proof (cases "IDFS_stack0 avoid vis p = tl p")
      case True_tl: True
      hence "IDFS_stack0 avoid vis p = tl p" .
      moreover have "v \<in> set (IDFS_stack0 avoid vis p)" using True .
      ultimately have "v \<in> set (tl p)" by simp
      with tlP show ?thesis by simp
    next
      case False_tl: False
      have eq: "IDFS_stack0 avoid vis p = p"
        using disj False_tl by auto
      have vp: "v \<in> set p" using True eq by simp
      have ne: "p \<noteq> []" using vp by auto
      have h_not: "hd p \<notin> t_set avoid \<union> t_set vis"
        using disj False_tl eq ne by auto
      show ?thesis
      proof (cases "P (hd p)")
        case Phd: True
        have im: "\<not> isin avoid (hd p)"
          using pre_inv(1) h_not
          by (simp add: Graph.vset.set.set_isin)
        have ne_stack0: "IDFS_stack0 avoid vis p \<noteq> []" using eq ne by simp
        have Phd_stack0: "P (hd (IDFS_stack0 avoid vis p))" using eq Phd by simp
        have im_stack0: "\<not> isin avoid (hd (IDFS_stack0 avoid vis p))"
          using eq im by simp
        have "p' = IDFS_stack0 avoid vis p"
          by (rule av.DFS_avoid_found_immediately[OF retS ne_stack0 Phd_stack0 im_stack0])
        with eq have "p' = p" by simp
        with v have "v \<in> set (tl p)" by simp
        with tlP show ?thesis by simp
      next
        case nPhd: False
        from tl_char True eq have char: "v \<in> set p \<or> \<not> P v" by simp
        show ?thesis
        proof (cases p)
          case Nil
          with ne show ?thesis by simp
        next
          case (Cons v0 vs)
          with char have "v = v0 \<or> v \<in> set vs \<or> \<not> P v" by auto
          with nPhd Cons tlP show ?thesis by auto
        qed
      qed
    qed
  qed
qed

theorem IDFS_sound_6:
  assumes "IDFS_impl P avoid p vis = (Some p', vis')" "p \<noteq> []"
  shows "last p = last p'"
proof -
  from assms(1) have retS: "DFS_avoid_state.ret Rst = Some p'" by (auto simp: IDFS_impl_pair)
  have l: "IDFS_stack0 avoid vis p \<noteq> []"
       and e: "last p' = last (IDFS_stack0 avoid vis p)"
    using av.DFS_avoid_sound_last[OF retS] by (auto simp: av.avoid_final_state_def)
  show ?thesis
  proof (cases "IDFS_stack0 avoid vis p = p")
    case True thus ?thesis using e by simp
  next
    case False
    hence s: "IDFS_stack0 avoid vis p = tl p" using IDFS_stack0_cases by auto
    have "last (tl p) = last p" using l s assms(2) by (cases p) auto
    with e s show ?thesis by simp
  qed
qed

theorem IDFS_sound_7:
  assumes "IDFS_impl P avoid p vis = (Some p', vis')"
  shows "p' \<noteq> []"
proof -
  from assms have retS: "DFS_avoid_state.ret Rst = Some p'" by (auto simp: IDFS_impl_pair)
  then show ?thesis by (rule av.DFS_avoid_sound_nonempty)
qed

theorem IDFS_sound_8:
  assumes "IDFS_impl P avoid p vis = (Some p', vis')"
  shows "P (hd p')"
proof -
  from assms have retS: "DFS_avoid_state.ret Rst = Some p'" by (auto simp: IDFS_impl_pair)
  from av.DFS_avoid_sound_hdP(1)[OF retS] show ?thesis .
qed

theorem IDFS_dVs_bound:
  assumes "IDFS_impl P avoid p vis = (ret_p, vis')"
  shows "t_set vis' \<subseteq> dVs (Graph.digraph_abs G)"
  using assms slot_dVs by (auto simp: IDFS_impl_pair)

end  (* inner context: avoid vis p, p_path, p_dist, av_inv, av_dVs *)

end  (* locale IDFS_witness *)

end (* IDFS *)
