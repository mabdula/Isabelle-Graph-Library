theory Weighted_Bipartite_B_Matching_Imp
  imports Bipartite_B_Matching_Imp Matroid_Weighted_Intersection_Imp
begin

(*TODO Once we have more b matching theory, set up own b-matching 
    theory in Basic_Matching Session and put b-matching defs there.*)

section \<open>Maximum Weight Bipartite b-Matching in Imperative HOL\<close>

subsection \<open>Maximum Weight b-Matchings\<close>

definition max_weight_b_matching ::
  "'a graph \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> ('a set \<Rightarrow> real) \<Rightarrow> 'a graph \<Rightarrow> bool" where
  "max_weight_b_matching G b w M \<longleftrightarrow>
     M \<subseteq> G \<and> b_matching b M \<and> (\<forall> M'. M' \<subseteq> G \<and> b_matching b M' \<longrightarrow> sum w M' \<le> sum w M)"

text \<open>The graph and the capacities are given as in
  @{theory Matroid_Intersection.Bipartite_B_Matching_Imp}, and a fourth array, of the length of the
  edge arrays, holds the edge weights, in an ordered ring \<open>'n\<close>. The matroids, the oracles and the
  solution handle are those of the unweighted instance; the algorithm is the generic one of
  @{theory Matroid_Intersection.Matroid_Weighted_Intersection_Imp}. The result is the Boolean array
  of the positions of a maximum weight b-matching, from the solution handle.\<close>

subsection \<open>Code\<close>

global_interpretation wbx: weighted_matroid_intersection_imp_spec n id id bb_memb bb_ins1 bb_exch1
  bb_ins2 bb_exch2 bb_ins bb_del part_npts_imp part_pt_imp part_npts_imp part_pt_imp
  for n
  defines wbx_teq = wbx.wids.teq_imp
    and wbx_tnbs = wbx.wids.tnbs
    and wbx_tround = wbx.wids.tround
    and wbx_tbfs_run = wbx.wids.tbfs_run
    and wbx_max = wbx.wids.max_imp
    and wbx_thas_nb = wbx.wids.thas_nb_imp
    and wbx_wst = wbx.wids.wst_imp
    and wbx_wsrc = wbx.wids.wsrc_imp
    and wbx_wtgt = wbx.wids.wtgt_imp
    and wbx_drop = wbx.wids.drop_imp
    and wbx_wsearch = wbx.wids.wsearch_imp
    and wbx_wtight_ctx = wbx.wids.wtight_ctx_imp
    and wbx_wctx_path = wbx.wids.wctx_path_imp
    and wbx_gap = wbx.wids.gap_imp
    and wbx_weps_step = wbx.wids.weps_step
    and wbx_weps = wbx.wids.weps_imp
    and wbx_wshift = wbx.wids.wshift_imp
    and wbx_ccopy = wbx.wids.ccopy_imp
    and wbx_czero = wbx.wids.czero_imp
    and wbx_wmi_ids = wbx.wids.wmi_imp
    and wbx_wmi = wbx.wmi_imp
  done

text \<open>A copy of the BFS core with the tight iterator fixed at code generation time.\<close>

global_interpretation wxbb: BFS_subprocedures_lists_code bset_memb bset_ins "wbx_tnbs n"
  for n
  defines wxbb_inner = wxbb.inner_loop
    and wxbb_outer = wxbb.outer_loop
    and wxbb_round = wxbb.next_frontier_current_parents_imp
  done

global_interpretation wxbbi: BFS_Imperative_spec bfs_src_to_cf bfs_set_srcs_visited
    "wxbb_round n Gh" bfs_cf_is_empty bset_memb bfs_set_dists Array.nth Array.nth
  for n Gh
  defines wxbb_loop = wxbbi.BFS_par_imp
    and wxbb_init = wxbbi.initial_state_imp
    and wxbb_run = wxbbi.visited_dists_parents_imp
  done

lemma wbx_tround_code [code]: "wbx_tround n = wxbb_round n"
  unfolding wbx.wids.tround_def wxbb_round_def ..

lemma wbx_tbfs_run_code [code]: "wbx_tbfs_run n Gh = wxbb_run n Gh"
  unfolding wbx.wids.tbfs_run_def wxbb_run_def wbx_tround_code ..

declare wxbbi.BFS_par_imp.simps[code]

text \<open>The edges are \<open>{Fa[i], Ta[i]}\<close> with weight \<open>Wa[i]\<close>, the capacity of vertex \<open>v\<close> is \<open>Ka[v]\<close>,
  and all vertices are below the length of \<open>Ka\<close>. After the prologue of the unweighted instance,
  the program allocates the two weight arrays of the algorithm.\<close>

definition "weighted_b_matching_imp Fa Ta Ka Wa =
   bb_setup_imp Fa Ta Ka (\<lambda> m H1 H2 Xi C1 C2. do {
     W1 \<leftarrow> Array.new m 0;
     W2 \<leftarrow> Array.new m 0;
     wbx_wmi m H1 H2 (Xi, C1, C2, Fa, Ta, Ka) Wa W1 W2;
     return Xi })"

export_code weighted_b_matching_imp checking SML_imp

text \<open>The example of @{theory Matroid_Intersection.Bipartite_B_Matching_Imp} with the weights of the
  weighted matching example: the edges of the returned array. The result is
  \<open>[(1, 8), (1, 10), (3, 6), (7, 10)]\<close>, of weight \<open>13\<close>. The weights are integers, fixed by a
  monomorphic copy, since the generated function expects the class dictionaries of the weight type.\<close>

definition "weighted_b_matching_int_imp Fa Ta Ka (Wa :: int array) = weighted_b_matching_imp Fa Ta Ka Wa"

ML_val \<open>
  let
    val nat = @{code nat_of_integer}
    val int = @{code int_of_integer}
    val es = [(1, 6), (1, 8), (1, 10), (3, 6), (3, 10), (9, 8), (7, 10)]
    val ws = [3, 2, 5, 4, 1, ~1, 2]
    val Fa = Array.fromList (map (nat o #1) es)
    val Ta = Array.fromList (map (nat o #2) es)
    val Ka = Array.fromList (map nat [0, 2, 0, 1, 0, 0, 1, 1, 1, 1, 2])
    val Wa = Array.fromList (map int ws)
    val r = @{code weighted_b_matching_int_imp} Fa Ta Ka Wa ()
  in
    List.filter (fn (j, _) => Array.sub (r, j)) (ListPair.zip (List.tabulate (length es, I), es))
    |> map #2
  end
\<close>

subsection \<open>Correctness\<close>

locale weighted_bipartite_b_matching_imp =
  bipartite_b_matching_imp fs ts ks + weighted_bipartite_arrays "length ks" fs ts h ws + real_embedding h
  for fs ts ks and h :: "'n :: {linordered_idom, heap} \<Rightarrow> real" and ws
begin

text \<open>The elements are the positions themselves, so the indexation is the identity.\<close>

interpretation m: weighted_matroid_intersection_imp "length fs" id id bb_memb bb_ins1 bb_exch1 bb_ins2
  bb_exch2 bb_ins bb_del part_npts_imp part_pt_imp part_npts_imp part_pt_imp "{0..<length fs}"
  "\<lambda> X. X" lf.cap_ins lf.cap_exch lf.cap_indep sb emp "part_pts fs" "part_pst (length fs) fs"
  "\<lambda> X. X" rt.cap_ins rt.cap_exch rt.cap_indep emp "part_pts ts" "part_pst (length fs) ts" h
  by (intro weighted_matroid_intersection_imp.intro mi_inst real_embedding_axioms)

lemma is_max_weight_b_matching:
  assumes "weighted_double_matroid.is_opt lf.cap_indep rt.cap_indep (\<lambda> i. h (ws ! i)) X"
  shows "max_weight_b_matching ((\<lambda> i. {fs ! i, ts ! i}) ` {0..<length fs}) (\<lambda> v. ks ! v) edge_weight
           ((\<lambda> i. {fs ! i, ts ! i}) ` X)"
proof-
  have X: "lf.cap_indep X" "rt.cap_indep X"
    and mx: "\<And> Y. lf.cap_indep Y \<and> rt.cap_indep Y \<Longrightarrow>
               sum (\<lambda> i. h (ws ! i)) Y \<le> sum (\<lambda> i. h (ws ! i)) X"
    using assms unfolding weighted_double_matroid.is_opt_def[OF
        weighted_double_matroid.intro[OF m.double_matroid_axioms]]
    by blast+
  have Xb: "X \<subseteq> {0..<length fs} \<and> b_matching (\<lambda> v. ks ! v) ((\<lambda> i. {fs ! i, ts ! i}) ` X)"
    unfolding indep_b_matching[symmetric] using X by (rule conjI)
  have le: "sum edge_weight M \<le> sum edge_weight ((\<lambda> i. {fs ! i, ts ! i}) ` X)"
    if M: "M \<subseteq> (\<lambda> i. {fs ! i, ts ! i}) ` {0..<length fs}" "b_matching (\<lambda> v. ks ! v) M" for M
  proof-
    let ?Y = "{i \<in> {0..<length fs}. {fs ! i, ts ! i} \<in> M}"
    have img: "M = (\<lambda> i. {fs ! i, ts ! i}) ` ?Y"
      using M(1) by blast
    have Y: "?Y \<subseteq> {0..<length fs}"
      by (rule subsetI) simp
    have "b_matching (\<lambda> v. ks ! v) ((\<lambda> i. {fs ! i, ts ! i}) ` ?Y)"
      by (rule subst[where P = "b_matching (\<lambda> v. ks ! v)", OF img M(2)])
    then have "lf.cap_indep ?Y \<and> rt.cap_indep ?Y"
      unfolding indep_b_matching by (rule conjI[OF Y])
    then have le: "sum (\<lambda> i. h (ws ! i)) ?Y \<le> sum (\<lambda> i. h (ws ! i)) X"
      by (rule mx)
    have "sum edge_weight M = sum (\<lambda> i. h (ws ! i)) ?Y"
      using arg_cong[OF img, of "sum edge_weight"] sum_img[OF Y] by (rule trans)
    then show ?thesis
      unfolding sum_img[OF conjunct1[OF Xb]] using le by simp
  qed
  show ?thesis
    unfolding max_weight_b_matching_def
  proof(intro conjI allI impI)
    show "(\<lambda> i. {fs ! i, ts ! i}) ` X \<subseteq> (\<lambda> i. {fs ! i, ts ! i}) ` {0..<length fs}"
      using conjunct1[OF Xb] by (rule image_mono)
    show "b_matching (\<lambda> v. ks ! v) ((\<lambda> i. {fs ! i, ts ! i}) ` X)"
      by (rule conjunct2[OF Xb])
  next
    fix M
    assume "M \<subseteq> (\<lambda> i. {fs ! i, ts ! i}) ` {0..<length fs} \<and> b_matching (\<lambda> v. ks ! v) M"
    then show "sum edge_weight M \<le> sum edge_weight ((\<lambda> i. {fs ! i, ts ! i}) ` X)"
      by (intro le) simp_all
  qed
qed

text \<open>The generic algorithm on the allocated handles.\<close>

theorem whandles_correct:
  "<(part_pst (length fs) fs H1) * part_pst (length fs) ts H2 * xset_assn (length fs) {} Xi *
    cnt_assn (length ks) fs {} C1 * cnt_assn (length ks) ts {} C2 *
    blocks_assn (length fs) (length ks) fs Fa * blocks_assn (length fs) (length ks) ts Ta *
    caps_assn (length ks) (\<lambda> v. ks ! v) Ka *
    warr_assn (length fs) h (\<lambda> i. if i < length fs then h (ws ! i) else 0) Wa *
    len_assn (length fs) W1 * len_assn (length fs) W2>
     wbx_wmi (length fs) H1 H2 (Xi, C1, C2, Fa, Ta, Ka) Wa W1 W2
   <\<lambda> _. \<exists>\<^sub>A X. xset_assn (length fs) X Xi * blocks_assn (length fs) (length ks) fs Fa *
              blocks_assn (length fs) (length ks) ts Ta * caps_assn (length ks) (\<lambda> v. ks ! v) Ka *
              warr_assn (length fs) h (\<lambda> i. if i < length fs then h (ws ! i) else 0) Wa * true *
              \<up>(max_weight_b_matching ((\<lambda> i. {fs ! i, ts ! i}) ` {0..<length fs}) (\<lambda> v. ks ! v)
                   edge_weight ((\<lambda> i. {fs ! i, ts ! i}) ` X))>"
  apply (rule ht_cons[OF _ _ m.wmi_imp_correct[where c = "\<lambda> i. h (ws ! i)", folded wbx_wmi_def]])
   apply (simp only: bb_sol_assn.simps id_apply star_aci, rule ent_refl)
  apply (simp only: id_apply image_id)
  apply (intro ent_ex_preI)
  apply (sep_auto dest: is_max_weight_b_matching)
  done

subsubsection \<open>The Program\<close>

theorem weighted_b_matching_imp_correct:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Ka \<mapsto>\<^sub>a ks * Wa \<mapsto>\<^sub>a ws> weighted_b_matching_imp Fa Ta Ka Wa
   <\<lambda> Xi. \<exists>\<^sub>A X. xset_assn (length fs) X Xi * Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Ka \<mapsto>\<^sub>a ks * Wa \<mapsto>\<^sub>a ws *
              true * \<up>(max_weight_b_matching ((\<lambda> i. {fs ! i, ts ! i}) ` {0..<length fs})
                        (\<lambda> v. ks ! v) edge_weight ((\<lambda> i. {fs ! i, ts ! i}) ` X))>"
proof-
  have W: "Wa \<mapsto>\<^sub>a ws = warr_assn (length fs) h (\<lambda> i. if i < length fs then h (ws ! i) else 0) Wa"
    using warr_of_list[OF real_embedding_axioms, of Wa ws] unfolding ws_length .
  show ?thesis
    unfolding weighted_b_matching_imp_def
    apply (rule ht_cons_pre[OF _ bb_setup_rule[where F = "Wa \<mapsto>\<^sub>a ws"]], simp only: star_aci, rule ent_refl)
    apply (rule alloc_bind[OF len_assn_new])+
    apply (rule ht_bind[OF ht_frame_ac[OF whandles_correct, where R = true]])
      prefer 3 apply (rule ht_return_wp)
     apply (simp only: W star_aci, rule ent_refl)
    apply (sep_auto simp: blocks_assn_def caps_assn_def map_nth W[symmetric])
    done
qed

end

end
