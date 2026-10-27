theory Matroid_Weighted_Intersection_Imp
  imports Matroid_Weighted_Intersection_Exchange_Graph_Imp Matroid_Intersection_Imp
begin

section \<open>Weighted Matroid Intersection in Imperative HOL\<close>

text \<open>The complete imperative algorithm for two matroids on the nats below \<open>n\<close>, given by
  oracles, and weights in an ordered ring \<open>'n\<close>, read in the reals through the embedding \<open>h\<close>.
    As
  @{theory Matroid_Intersection.Matroid_Intersection_Imp}, the program builds the CSR of the
  candidate graph, allocates the work arrays of the path search, and runs the loop on them; this is
  the only place where arrays are allocated. The caller provides the handle of the empty solution,
  the arrays for the two current weights, and the weight array. The result is a common independent
  set of maximum weight, in the solution handle.\<close>

subsection \<open>Code\<close>

declare weighted_intersection_imp_loop_spec.wmi_loop_imp.simps[code]
  weighted_intersection_imp_loop_spec.wmi_run_imp_def[code]
  weighted_intersection_imp_loop_spec.gain_imp_def[code]
  weighted_intersection_imp_loop_spec.reweight_imp_def[code]
  weighted_intersection_imp_loop_spec.winit_imp_def[code]

text \<open>The operations of the unweighted exchange graph that the weighted search reuses. An instance
  shares them with its unweighted interpretation, so they are not folded into its constants.\<close>

declare unweighted_intersection_exchange_imp_spec.nb1_imp_def[code]
  unweighted_intersection_exchange_imp_spec.nb2_imp_def[code]
  unweighted_intersection_exchange_imp_spec.filt_imp_def[code]
  unweighted_intersection_exchange_imp_spec.xnbs_def[code]
  unweighted_intersection_exchange_imp_spec.s_imp_def[code]
  unweighted_intersection_exchange_imp_spec.t_imp_def[code]
  unweighted_intersection_exchange_imp_spec.st_imp_def[code]
  unweighted_intersection_exchange_imp_spec.is_tgt_imp_def[code]

locale weighted_matroid_intersection_imp_ids_spec =
  matroid_intersection_imp_ids_spec n smemb_imp ins1_imp exch1_imp ins2_imp exch2_imp sins_imp sdel_imp
    npts1_imp pt1_imp npts2_imp pt2_imp +
  weighted_intersection_exchange_imp_spec n smemb_imp ins1_imp exch1_imp ins2_imp exch2_imp
  for n and smemb_imp :: "nat \<Rightarrow> 'si \<Rightarrow> bool Heap" and ins1_imp exch1_imp ins2_imp exch2_imp
    sins_imp sdel_imp npts1_imp pt1_imp npts2_imp pt2_imp
begin

definition "wmi_imp H1 H2 Si Co C1 C2 = do {
   Gc \<leftarrow> cand_csr_imp npts1_imp pt1_imp npts2_imp pt2_imp H1 H2 n;
   Vi \<leftarrow> Array.new n False;
   Fr \<leftarrow> Array.new (Suc n) 0;
   Bf \<leftarrow> Array.new (Suc n) 0;
   Da \<leftarrow> Array.new n 0;
   Pa \<leftarrow> Array.new n 0;
   Ra \<leftarrow> Array.new n 0;
   Mi \<leftarrow> Array.new 2 0;
   Ti \<leftarrow> Array.new 2 0;
   weighted_intersection_imp_loop_spec.wmi_run_imp sins_imp sdel_imp Array.nth ccopy_imp czero_imp
     (wtight_ctx_imp Gc Vi Fr Bf Da Pa Mi Ti) (wctx_path_imp Pa Ti) (weps_imp Gc Vi Mi)
     (wshift_imp Vi) Si Co C1 C2 Ra }"

end

subsection \<open>Correctness\<close>

text \<open>First for matroids on the ids below \<open>n\<close> themselves.\<close>

locale weighted_matroid_intersection_imp_ids =
  weighted_matroid_intersection_imp_ids_spec + matroid_intersection_imp_ids + real_embedding h
  for h :: "'n :: {linordered_idom, heap} \<Rightarrow> real"
begin

sublocale wm: weighted_intersection_exchange_imp where n = n and smemb_imp = smemb_imp
  and ins1_imp = ins1_imp and exch1_imp = exch1_imp and ins2_imp = ins2_imp
  and exch2_imp = exch2_imp and sol_assn = sol_assn and sins_imp = sins_imp
  and sdel_imp = sdel_imp and ost1 = ost1 and ost2 = ost2 and orcl_prep1 = orcl_prep1
  and ins_orcl1 = ins_orcl1 and exch_orcl1 = exch_orcl1 and orcl_prep2 = orcl_prep2
  and ins_orcl2 = ins_orcl2 and exch_orcl2 = exch_orcl2 and indep1 = indep1 and indep2 = indep2
  and es0 = "cand_list pts1 pts2 n" and h = h
  by (rule weighted_intersection_exchange_imp.intro[OF m.unweighted_intersection_exchange_imp_axioms
        weighted_intersection_exchange_csr.intro[OF unweighted_intersection_exchange_csr_axioms
          weighted_intersection_exchange_csr_axioms.intro] real_embedding_axioms]) simp_all


text \<open>The whole program.\<close>

lemma candidate_frame:
  "<F * pst1 H1 * pst2 H2> cand_csr_imp npts1_imp pt1_imp npts2_imp pt2_imp H1 H2 n
   <\<lambda> Gc. F * pst1 H1 * pst2 H2 * (case Gc of (Ba, Ga) \<Rightarrow>
     Ba \<mapsto>\<^sub>a map (csr_start (nbrs (cand_list pts1 pts2 n))) [0..<Suc n] *
     Ga \<mapsto>\<^sub>a csr_entries (nbrs (cand_list pts1 pts2 n)) n)>"
  by (rule ht_frame_ac[OF c.cand_csr_rule, where R = F])
     (simp only: star_aci, rule ent_refl, sep_auto split: prod.splits)

lemma wmi_imp_correct:
  "<(sol_assn {} Si) * ost1 * ost2 * pst1 H1 * pst2 H2 * warr_assn n h c Co *
    len_assn n C1 * len_assn n C2> wmi_imp H1 H2 Si Co C1 C2
   <\<lambda> _. \<exists>\<^sub>A X c1 c2. sol_assn X Si * warr_assn n h c1 C1 * warr_assn n h c2 C2 *
          warr_assn n h c Co * ost1 * ost2 * pst1 H1 * pst2 H2 * true *
          \<up>(weighted_double_matroid.is_opt indep1 indep2 c X)>"
  unfolding wmi_imp_def
  by (rule ht_cons_pre[OF _ ht_bind[OF candidate_frame[where F =
        "sol_assn {} Si * ost1 * ost2 * warr_assn n h c Co * len_assn n C1 * len_assn n C2"]]],
      (simp only: star_aci, rule ent_refl), (rule alloc_bind[OF len_assn_new])+,
      rule ht_frame_ac[OF wm.loop_correct[where c = c], where R = "pst1 H1 * pst2 H2"])
     ((simp only: wm.wws_def work_assn_def parr_len star_aci, rule ent_refl), sep_auto)

end

subsection \<open>Matroids on Any Type\<close>

text \<open>As in the unweighted case, the algorithm on the ids runs with every operation composed with
  \<open>elt\<close>. The weights are given on the ids, so the weight array is indexed by the ids. For
  the proof, an optimum on the ids is mapped back by \<open>elt\<close>.\<close>

locale weighted_matroid_intersection_imp_spec =
  matroid_intersection_imp_spec n idx elt smemb_imp ins1_imp exch1_imp ins2_imp exch2_imp
    sins_imp sdel_imp npts1_imp pt1_imp npts2_imp pt2_imp
  for n idx elt and smemb_imp :: "'a \<Rightarrow> 'si \<Rightarrow> bool Heap" and ins1_imp exch1_imp ins2_imp
    exch2_imp
    sins_imp sdel_imp npts1_imp pt1_imp npts2_imp pt2_imp
begin

sublocale wids: weighted_matroid_intersection_imp_ids_spec n "\<lambda> i. smemb_imp (elt i)"
  "\<lambda> Si i. ins1_imp Si (elt i)" "\<lambda> Si i j. exch1_imp Si (elt i) (elt j)"
  "\<lambda> Si i. ins2_imp Si (elt i)" "\<lambda> Si i j. exch2_imp Si (elt i) (elt j)"
  "\<lambda> i. sins_imp (elt i)" "\<lambda> i. sdel_imp (elt i)"
  "\<lambda> H i. npts1_imp H (elt i)" "pt_ids_imp idx elt pt1_imp"
  "\<lambda> H i. npts2_imp H (elt i)" "pt_ids_imp idx elt pt2_imp" .

definition "wmi_imp H1 H2 Si Co C1 C2 = wids.wmi_imp H1 H2 Si Co C1 C2"

end

context matroid_ids
begin

lemma pull_sum: "I \<subseteq> {0..<n} \<Longrightarrow> sum (\<lambda> i. if i < n then c (elt i) else 0) I = sum c
    (elt ` I)"
  by (subst sum.reindex) (auto intro: inj_on_subset[OF elt_inj] intro!: sum.cong)

lemma push_sum:
  "Y \<subseteq> carrier \<Longrightarrow> sum c Y = sum (\<lambda> i. if i < n then c (elt i) else 0) (idx ` Y)"
  using elt_surj[of Y] pull_sum[of "idx ` Y" c]
  by simp

lemma pull_weight_bound:
  assumes "I \<subseteq> {0..<n}"
    "\<And> J. \<lbrakk>pull indep1 J; pull indep2 J\<rbrakk> \<Longrightarrow>
      sum (\<lambda> i. if i < n then c (elt i) else 0) J \<le> sum (\<lambda> i. if i < n then c (elt i) else 0) I"
    "Y \<subseteq> carrier" "indep1 Y" "indep2 Y"
  shows "sum c Y \<le> sum c (elt ` I)"
  using assms elt_surj[of Y] push_sum[of Y c] pull_sum[of I c]
  by (auto simp: pull_def)

lemma pull_opt:
  assumes "double_matroid carrier indep1 indep2" "double_matroid {0..<n} (pull indep1) (pull indep2)"
    and "weighted_double_matroid.is_opt (pull indep1) (pull indep2)
                (\<lambda> i. if i < n then c (elt i) else 0) I"
  shows "weighted_double_matroid.is_opt indep1 indep2 c (elt ` I)"
proof-
  interpret D: double_matroid carrier indep1 indep2
    by (rule assms(1))
  note opt_defs = assms(1,2)[THEN weighted_double_matroid.intro, THEN weighted_double_matroid.is_opt_def]
  show ?thesis
    using assms(3) unfolding opt_defs
  proof(intro conjI allI impI, goal_cases)
    case 1
    then show ?case
      by (auto simp: pull_def)
  next
    case 2
    then show ?case
      by (auto simp: pull_def)
  next
    case (3 Y)
    show ?case
      by (rule pull_weight_bound[where I = I and c = c and Y = Y and ?indep1.0 = indep1 and ?indep2.0 =
        indep2]; insert 3; auto simp: pull_def dest: D.matroid1.indep_subset_carrier)
  qed

qed

end

text \<open>The algorithm for two matroids on \<open>'a\<close> with weights \<open>c\<close> on the elements.\<close>

locale weighted_matroid_intersection_imp =
  weighted_matroid_intersection_imp_spec + matroid_intersection_imp + real_embedding h
  for h :: "'n :: {linordered_idom, heap} \<Rightarrow> real"
begin

lemma wmi_imp_correct:
  "<(sol_assn {} Si) * ost1 * ost2 * pst1 H1 * pst2 H2 *
    warr_assn n h (\<lambda> i. if i < n then c (elt i) else 0) Co * len_assn n C1 * len_assn n C2>
     wmi_imp H1 H2 Si Co C1 C2
   <\<lambda> _. \<exists>\<^sub>A X c1 c2. sol_assn X Si * warr_assn n h c1 C1 * warr_assn n h c2 C2 *
          warr_assn n h (\<lambda> i. if i < n then c (elt i) else 0) Co *
          ost1 * ost2 * pst1 H1 * pst2 H2 * true * \<up>(weighted_double_matroid.is_opt indep1 indep2 c X)>"
proof-
  interpret m: weighted_matroid_intersection_imp_ids n "\<lambda> i. smemb_imp (elt i)"
    "\<lambda> Si i. ins1_imp Si (elt i)" "\<lambda> Si i j. exch1_imp Si (elt i) (elt j)"
    "\<lambda> Si i. ins2_imp Si (elt i)" "\<lambda> Si i j. exch2_imp Si (elt i) (elt j)"
    "\<lambda> i. sins_imp (elt i)" "\<lambda> i. sdel_imp (elt i)"
    "\<lambda> H i. npts1_imp H (elt i)" "pt_ids_imp idx elt pt1_imp"
    "\<lambda> H i. npts2_imp H (elt i)" "pt_ids_imp idx elt pt2_imp" o1.prep_ids o1.ins_ids o1.exch_ids
    o2.prep_ids o2.ins_ids o2.exch_ids "o1.pull indep1" "o1.pull indep2" "o1.sol_ids sol_assn"
    ost1 ost2 o1.pts_ids pst1 o2.pts_ids pst2 h
    by (intro weighted_matroid_intersection_imp_ids.intro ids_imp real_embedding_axioms)
  note opt = o1.pull_opt[OF double_matroid_axioms m.double_matroid_axioms]
  show ?thesis
    unfolding wmi_imp_def
    by (rule ht_cons[OF _ _ m.wmi_imp_correct[where c = "\<lambda> i. if i < n then c (elt i) else 0"]])
       (sep_auto simp: o1.sol_ids_def intro: opt)+

qed

end
end
