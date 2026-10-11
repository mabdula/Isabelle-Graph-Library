theory Weighted_Bipartite_Matching_Imp
  imports Bipartite_Matching_Imp Matroid_Weighted_Intersection_Imp
begin

section \<open>Maximum Weight Bipartite Matching in Imperative HOL\<close>

text \<open>The graph is given as in @{theory Matroid_Intersection.Bipartite_Matching_Imp}, and a third
  array of the same length holds the edge weights, in an ordered ring \<open>'n\<close>. The matroids, the
  oracles and the solution handle are those of the unweighted instance; the algorithm is the generic
  one of @{theory Matroid_Intersection.Matroid_Weighted_Intersection_Imp}. The result is the Boolean
  array of the positions of a maximum weight matching, from the solution handle.\<close>

subsection \<open>Code\<close>

global_interpretation wmx: weighted_matroid_intersection_imp_spec n id id bm_memb bm_ins1 bm_exch1
  bm_ins2 bm_exch2 bm_ins bm_del part_npts_imp part_pt_imp part_npts_imp part_pt_imp
  for n
  defines wmx_teq = wmx.wids.teq_imp
    and wmx_tnbs = wmx.wids.tnbs
    and wmx_tround = wmx.wids.tround
    and wmx_tbfs_run = wmx.wids.tbfs_run
    and wmx_max = wmx.wids.max_imp
    and wmx_thas_nb = wmx.wids.thas_nb_imp
    and wmx_wst = wmx.wids.wst_imp
    and wmx_wsrc = wmx.wids.wsrc_imp
    and wmx_wtgt = wmx.wids.wtgt_imp
    and wmx_drop = wmx.wids.drop_imp
    and wmx_wsearch = wmx.wids.wsearch_imp
    and wmx_wtight_ctx = wmx.wids.wtight_ctx_imp
    and wmx_wctx_path = wmx.wids.wctx_path_imp
    and wmx_gap = wmx.wids.gap_imp
    and wmx_weps_step = wmx.wids.weps_step
    and wmx_weps = wmx.wids.weps_imp
    and wmx_wshift = wmx.wids.wshift_imp
    and wmx_ccopy = wmx.wids.ccopy_imp
    and wmx_czero = wmx.wids.czero_imp
    and wmx_wmi_ids = wmx.wids.wmi_imp
    and wmx_wmi = wmx.wmi_imp
  done

text \<open>A copy of the BFS core with the tight iterator fixed at code generation time.\<close>

global_interpretation wxb: BFS_subprocedures_lists_code bset_memb bset_ins "wmx_tnbs n"
  for n
  defines wxb_inner = wxb.inner_loop
    and wxb_outer = wxb.outer_loop
    and wxb_round = wxb.next_frontier_current_parents_imp
  done

global_interpretation wxbi: BFS_Imperative_spec bfs_src_to_cf bfs_set_srcs_visited
    "wxb_round n Gh" bfs_cf_is_empty bset_memb bfs_set_dists Array.nth Array.nth
  for n Gh
  defines wxb_loop = wxbi.BFS_par_imp
    and wxb_init = wxbi.initial_state_imp
    and wxb_run = wxbi.visited_dists_parents_imp
  done

lemma wmx_tround_code [code]: "wmx_tround n = wxb_round n"
  unfolding wmx.wids.tround_def wxb_round_def ..

lemma wmx_tbfs_run_code [code]: "wmx_tbfs_run n Gh = wxb_run n Gh"
  unfolding wmx.wids.tbfs_run_def wxb_run_def wmx_tround_code ..

declare wxbi.BFS_par_imp.simps[code]

text \<open>The edges are \<open>{Fa[i], Ta[i]}\<close> with weight \<open>Wa[i]\<close>, and all vertices are below \<open>nv\<close>. After the
  prologue of the unweighted instance, the program allocates the two weight arrays of the
  algorithm.\<close>

definition "weighted_matching_imp nv Fa Ta Wa =
   bm_setup_imp nv Fa Ta (\<lambda> m H1 H2 Xi C1 C2. do {
     W1 \<leftarrow> Array.new m 0;
     W2 \<leftarrow> Array.new m 0;
     wmx_wmi m H1 H2 (Xi, C1, C2, Fa, Ta) Wa W1 W2;
     return Xi })"

export_code weighted_matching_imp checking SML_imp

text \<open>The example of @{theory Matroid_Intersection.Bipartite_Matching_Imp} with weights: the edges
  of the returned array. The result is \<open>[(1, 10), (3, 6)]\<close>, of weight \<open>9\<close>; every matching with
  three edges is lighter. The weights are integers, fixed by a monomorphic copy, since the generated
  function expects the class dictionaries of the weight type.\<close>

definition "weighted_matching_int_imp nv Fa Ta (Wa :: int array) = weighted_matching_imp nv Fa Ta Wa"

ML_val \<open>
  let
    val nat = @{code nat_of_integer}
    val int = @{code int_of_integer}
    val es = [(1, 6), (1, 8), (1, 10), (3, 6), (3, 10), (9, 8), (7, 10)]
    val ws = [3, 2, 5, 4, 1, ~1, 2]
    val Fa = Array.fromList (map (nat o #1) es)
    val Ta = Array.fromList (map (nat o #2) es)
    val Wa = Array.fromList (map int ws)
    val r = @{code weighted_matching_int_imp} (nat 11) Fa Ta Wa ()
  in
    List.filter (fn (j, _) => Array.sub (r, j)) (ListPair.zip (List.tabulate (length es, I), es))
    |> map #2
  end
\<close>

subsection \<open>Correctness\<close>

locale weighted_bipartite_matching_imp = weighted_bipartite_arrays nv fs ts h ws + real_embedding h
  for nv fs ts and h :: "'n :: {linordered_idom, heap} \<Rightarrow> real" and ws
begin

text \<open>The elements are the positions themselves, so the indexation is the identity.\<close>

interpretation m: weighted_matroid_intersection_imp "length fs" id id bm_memb bm_ins1 bm_exch1 bm_ins2
  bm_exch2 bm_ins bm_del part_npts_imp part_pt_imp part_npts_imp part_pt_imp "{0..<length fs}"
  lf.part_prep lf.part_ins lf.part_exch lf.part_indep sa emp "part_pts fs" "part_pst (length fs) fs"
  rt.part_prep rt.part_ins rt.part_exch rt.part_indep emp "part_pts ts" "part_pst (length fs) ts" h
  by (intro weighted_matroid_intersection_imp.intro mi_inst real_embedding_axioms)

lemma is_max_weight_matching:
  assumes "weighted_double_matroid.is_opt lf.part_indep rt.part_indep (\<lambda> i. h (ws ! i)) X"
  shows "max_weight_matching ((\<lambda> i. {fs ! i, ts ! i}) ` {0..<length fs}) edge_weight
           ((\<lambda> i. {fs ! i, ts ! i}) ` X)"
proof-
  have X: "lf.part_indep X" "rt.part_indep X"
    and mx: "\<And> Y. lf.part_indep Y \<and> rt.part_indep Y \<Longrightarrow>
               sum (\<lambda> i. h (ws ! i)) Y \<le> sum (\<lambda> i. h (ws ! i)) X"
    using assms unfolding weighted_double_matroid.is_opt_def[OF
        weighted_double_matroid.intro[OF m.double_matroid_axioms]]
    by blast+
  have Xs: "X \<subseteq> {0..<length fs}"
    using X(1) unfolding lf.part_indep_def by simp
  show ?thesis
  proof(rule max_weight_matchingI)
    show "graph_matching ((\<lambda> i. {fs ! i, ts ! i}) ` {0..<length fs}) ((\<lambda> i. {fs ! i, ts ! i}) ` X)"
      by (rule indep_matching[OF X])
  next
    fix M
    assume "graph_matching ((\<lambda> i. {fs ! i, ts ! i}) ` {0..<length fs}) M"
    then have M: "M \<subseteq> (\<lambda> i. {fs ! i, ts ! i}) ` {0..<length fs}" "matching M"
      by simp_all
    obtain Y where Y: "M = (\<lambda> i. {fs ! i, ts ! i}) ` Y" "lf.part_indep Y" "rt.part_indep Y"
      using matching_indep[OF M] .
    have Ys: "Y \<subseteq> {0..<length fs}"
      using Y(2) unfolding lf.part_indep_def by simp
    show "sum edge_weight M \<le> sum edge_weight ((\<lambda> i. {fs ! i, ts ! i}) ` X)"
      unfolding Y(1) sum_img[OF Ys] sum_img[OF Xs] using Y(2,3) by (intro mx) simp
  qed
qed

text \<open>The generic algorithm on the allocated handles.\<close>

theorem whandles_correct:
  "<(part_pst (length fs) fs H1) * part_pst (length fs) ts H2 * xset_assn (length fs) {} Xi *
    cnt_assn nv fs {} C1 * cnt_assn nv ts {} C2 *
    blocks_assn (length fs) nv fs Fa * blocks_assn (length fs) nv ts Ta *
    warr_assn (length fs) h (\<lambda> i. if i < length fs then h (ws ! i) else 0) Wa *
    len_assn (length fs) W1 * len_assn (length fs) W2>
     wmx_wmi (length fs) H1 H2 (Xi, C1, C2, Fa, Ta) Wa W1 W2
   <\<lambda> _. \<exists>\<^sub>A X. xset_assn (length fs) X Xi * blocks_assn (length fs) nv fs Fa *
              blocks_assn (length fs) nv ts Ta *
              warr_assn (length fs) h (\<lambda> i. if i < length fs then h (ws ! i) else 0) Wa * true *
              \<up>(max_weight_matching ((\<lambda> i. {fs ! i, ts ! i}) ` {0..<length fs}) edge_weight
                                     ((\<lambda> i. {fs ! i, ts ! i}) ` X))>"
  apply (rule ht_cons[OF _ _ m.wmi_imp_correct[where c = "\<lambda> i. h (ws ! i)", folded wmx_wmi_def]])
   apply (simp only: bm_sol_assn.simps id_apply star_aci, rule ent_refl)
  apply (simp only: id_apply image_id)
  apply (intro ent_ex_preI)
  apply (sep_auto dest: is_max_weight_matching)
  done

subsubsection \<open>The Program\<close>

theorem weighted_matching_imp_correct:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws> weighted_matching_imp nv Fa Ta Wa
   <\<lambda> Xi. \<exists>\<^sub>A X. xset_assn (length fs) X Xi * Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * true *
              \<up>(max_weight_matching ((\<lambda> i. {fs ! i, ts ! i}) ` {0..<length fs}) edge_weight
                                     ((\<lambda> i. {fs ! i, ts ! i}) ` X))>"
proof-
  have W: "Wa \<mapsto>\<^sub>a ws = warr_assn (length fs) h (\<lambda> i. if i < length fs then h (ws ! i) else 0) Wa"
    using warr_of_list[OF real_embedding_axioms, of Wa ws] unfolding ws_length .
  show ?thesis
    unfolding weighted_matching_imp_def
    apply (rule ht_cons_pre[OF _ bm_setup_rule[where F = "Wa \<mapsto>\<^sub>a ws"]], simp only: star_aci, rule ent_refl)
    apply (rule alloc_bind[OF len_assn_new])+
    apply (rule ht_bind[OF ht_frame_ac[OF whandles_correct, where R = true]])
      prefer 3 apply (rule ht_return_wp)
     apply (simp only: W star_aci, rule ent_refl)
    apply (sep_auto simp: blocks_assn_def W[symmetric])
    done
qed

end
end

