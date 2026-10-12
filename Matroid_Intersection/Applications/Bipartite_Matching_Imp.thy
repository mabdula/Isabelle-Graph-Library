theory Bipartite_Matching_Imp
  imports Matroid_Intersection_Imp Bipartite_Arrays
begin

section \<open>Maximum Bipartite Matching in Imperative HOL\<close>

text \<open>The input graph is given by two arrays of the same length \<open>m\<close>: edge \<open>i\<close> joins the
  left vertex \<open>fs ! i\<close> and the right vertex \<open>ts ! i\<close>, and all vertices are below \<open>nv\<close>. The
  elements of the matroids are the edges, i.e. their positions, and the matroids are the unit
  partition matroids of the left and the right endpoints; the algorithm is the generic one of
  @{theory Matroid_Intersection.Matroid_Intersection_Imp}. The two input arrays are the arrays of
  blocks of the two oracles. The solution handle consists of the Boolean array of the solution,
  the two arrays counting the solution elements per block and the two input arrays; the partner
  handles hold the edges grouped by block and the range of the block of every edge. The result
  is the Boolean array of the positions of a maximum matching.\<close>

subsection \<open>Code\<close>

definition bm_ins1 :: "bm_sol \<Rightarrow> nat \<Rightarrow> bool Heap" where
  "bm_ins1 Si y = (case Si of (Xi, C1, C2, Bl, Br) \<Rightarrow> part_ins_imp Bl C1 y)"

definition bm_exch1 :: "bm_sol \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool Heap" where
  "bm_exch1 Si x y = (case Si of (Xi, C1, C2, Bl, Br) \<Rightarrow> part_exch_imp Bl x y)"

definition bm_ins2 :: "bm_sol \<Rightarrow> nat \<Rightarrow> bool Heap" where
  "bm_ins2 Si y = (case Si of (Xi, C1, C2, Bl, Br) \<Rightarrow> part_ins_imp Br C2 y)"

definition bm_exch2 :: "bm_sol \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool Heap" where
  "bm_exch2 Si x y = (case Si of (Xi, C1, C2, Bl, Br) \<Rightarrow> part_exch_imp Br x y)"

global_interpretation mx: matroid_intersection_imp_spec n id id bm_memb bm_ins1 bm_exch1 
  bm_ins2 bm_exch2 bm_ins bm_del part_npts_imp part_pt_imp part_npts_imp part_pt_imp
  for n
  defines mx_nb1 = mx.ids.nb1_imp
    and mx_nb2 = mx.ids.nb2_imp
    and mx_filt = mx.ids.filt_imp
    and mx_xnbs = mx.ids.xnbs
    and mx_xround = mx.ids.xround
    and mx_bfs_run = mx.ids.bfs_run
    and mx_has_nb = mx.ids.has_nb_imp
    and mx_s = mx.ids.s_imp
    and mx_t = mx.ids.t_imp
    and mx_st = mx.ids.st_imp
    and mx_src = mx.ids.is_src_imp
    and mx_tgt = mx.ids.is_tgt_imp
    and mx_tail = mx.ids.tail_imp
    and mx_round = mx.ids.round_imp
    and mx_aug_path = mx.ids.aug_path_imp
    and mx_mi_ids = mx.ids.mi_imp
    and mx_mi = mx.mi_imp
  done

text \<open>A copy of the BFS core with the iterator fixed at code generation time.\<close>

global_interpretation xb: BFS_subprocedures_lists_code bset_memb bset_ins "mx_xnbs n"
  for n
  defines xb_inner = xb.inner_loop
    and xb_outer = xb.outer_loop
    and xb_round = xb.next_frontier_current_parents_imp
  done

global_interpretation xbi: BFS_Imperative_spec bfs_src_to_cf bfs_set_srcs_visited
    "xb_round n Gh" bfs_cf_is_empty bset_memb bfs_set_dists Array.nth Array.nth
  for n Gh
  defines xb_loop = xbi.BFS_par_imp
    and xb_init = xbi.initial_state_imp
    and xb_run = xbi.visited_dists_parents_imp
  done

lemma mx_xround_code [code]: "mx_xround n = xb_round n"
  unfolding mx.ids.xround_def xb_round_def ..

lemma mx_bfs_run_code [code]: "mx_bfs_run n Gh = xb_run n Gh"
  unfolding mx.ids.bfs_run_def xb_run_def mx_xround_code ..

declare xbi.BFS_par_imp.simps[code]

definition "matching_imp nv Fa Ta =
   bm_setup_imp nv Fa Ta (\<lambda> m H1 H2 Xi C1 C2. do {
     mx_mi m H1 H2 (Xi, C1, C2, Fa, Ta);
     return Xi })"

export_code matching_imp checking SML_imp

text \<open>A small example: the edges of the returned array. The result is
  \<open>[(1, 6), (3, 10), (9, 8)]\<close>.\<close>

ML_val \<open>
  let
    val nat = @{code nat_of_integer}
    val es = [(1, 6), (1, 8), (1, 10), (3, 6), (3, 10), (9, 8), (7, 10)]
    val Fa = Array.fromList (map (nat o #1) es)
    val Ta = Array.fromList (map (nat o #2) es)
    val r = @{code matching_imp} (nat 11) Fa Ta ()
  in
    List.filter (fn (j, _) => Array.sub (r, j)) (ListPair.zip (List.tabulate (length es, I), es))
    |> map #2
  end
\<close>


subsection \<open>Correctness\<close>

context bipartite_matching_imp
begin

abbreviation "sa \<equiv> bm_sol_assn (length fs) nv fs ts"

sublocale lf: unit_partition_oracle "\<lambda> i. fs ! i" sorted_list_of_set "{}" Set.insert
  "\<lambda> b B. b \<in> B" "{0..<length fs}" "\<lambda> X. X" finite "\<lambda> _. True" id
  by unfold_locales auto

sublocale rt: unit_partition_oracle "\<lambda> i. ts ! i" sorted_list_of_set "{}" Set.insert
  "\<lambda> b B. b \<in> B" "{0..<length fs}" "\<lambda> X. X" finite "\<lambda> _. True" id
  by unfold_locales auto

text \<open>Sets of positions independent in both partition matroids represent the matchings of
  the graph.\<close>

lemma indep_matching:
  assumes "lf.part_indep X" "rt.part_indep X"
  shows "graph_matching ((\<lambda> i. {fs ! i, ts ! i}) ` {0..<length fs}) ((\<lambda> i. {fs ! i, ts ! i}) ` X)"
proof
  have sub: "X \<subseteq> {0..<length fs}" and inj: "inj_on (\<lambda> i. fs ! i) X" "inj_on (\<lambda> i. ts ! i) X"
    using assms unfolding lf.part_indep_def rt.part_indep_def by simp_all
  show "(\<lambda> i. {fs ! i, ts ! i}) ` X \<subseteq> (\<lambda> i. {fs ! i, ts ! i}) ` {0..<length fs}"
    using sub by (rule image_mono)
  show "matching ((\<lambda> i. {fs ! i, ts ! i}) ` X)"
  proof(rule matchingI)
    fix e1 e2
    assume e: "e1 \<in> (\<lambda> i. {fs ! i, ts ! i}) ` X" "e2 \<in> (\<lambda> i. {fs ! i, ts ! i}) ` X" "e1 \<noteq> e2"
    obtain i where i: "i \<in> X" "e1 = {fs ! i, ts ! i}"
      using e(1) by (elim imageE) simp
    obtain j where j: "j \<in> X" "e2 = {fs ! j, ts ! j}"
      using e(2) by (elim imageE) simp
    have ij: "i < length fs" "j < length fs"
      using sub i(1) j(1) by auto
    have "i \<noteq> j"
      using e(3) i(2) j(2) by auto
    then have "fs ! i \<noteq> fs ! j" "ts ! i \<noteq> ts ! j"
      using inj_onD[OF inj(1) _ i(1) j(1)] inj_onD[OF inj(2) _ i(1) j(1)] by auto
    then show "e1 \<inter> e2 = {}"
      unfolding i(2) j(2) using left_right[OF ij] left_right[OF ij(2,1)] by auto
  qed
qed

lemma matching_indep:
  assumes "M \<subseteq> (\<lambda> i. {fs ! i, ts ! i}) ` {0..<length fs}" "matching M"
  obtains Y where "M = (\<lambda> i. {fs ! i, ts ! i}) ` Y" "lf.part_indep Y" "rt.part_indep Y"
proof-
  let ?Y = "{i \<in> {0..<length fs}. {fs ! i, ts ! i} \<in> M}"
  have img: "M = (\<lambda> i. {fs ! i, ts ! i}) ` ?Y"
    using assms(1) by blast
  have dis: "\<And> e1 e2. \<lbrakk>e1 \<in> M; e2 \<in> M; e1 \<noteq> e2\<rbrakk> \<Longrightarrow> e1 \<inter> e2 = {}"
    using assms(2) by (rule matchingE)
  have eq: "i = j" if "i \<in> ?Y" "j \<in> ?Y" "v \<in> {fs ! i, ts ! i}" "v \<in> {fs ! j, ts ! j}" for i j v
  proof-
    have "{fs ! i, ts ! i} = {fs ! j, ts ! j}"
    proof(rule ccontr)
      assume "{fs ! i, ts ! i} \<noteq> {fs ! j, ts ! j}"
      then have "{fs ! i, ts ! i} \<inter> {fs ! j, ts ! j} = {}"
        using that(1,2) by (intro dis) simp_all
      then show False
        using that(3,4) by blast
    qed
    then show "i = j"
      using that(1,2) by (intro inj_onD[OF dbltn_inj]) simp_all
  qed
  have "lf.part_indep ?Y"
    unfolding lf.part_indep_def
  proof(intro conjI inj_onI)
    fix i j
    assume "i \<in> ?Y" "j \<in> ?Y" "fs ! i = fs ! j"
    then show "i = j"
      by (intro eq[of i j "fs ! i"]) simp_all
  qed (rule subsetI, simp)
  moreover have "rt.part_indep ?Y"
    unfolding rt.part_indep_def
  proof(intro conjI inj_onI)
    fix i j
    assume "i \<in> ?Y" "j \<in> ?Y" "ts ! i = ts ! j"
    then show "i = j"
      by (intro eq[of i j "ts ! i"]) simp_all
  qed (rule subsetI, simp)
  ultimately show ?thesis
    by (rule that[OF img])
qed

lemma ins1_rule:
  "<(sa X Si) * emp * \<up>(y < length fs)> bm_ins1 Si y 
   <\<lambda> r. sa X Si * emp * \<up>(r = lf.part_ins (lf.part_prep X) y)>"
  by (cases Si rule: prod_cases5) (sep_auto simp: bm_ins1_def lf.part_ins heap: part_ins_imp_rule)

lemma ins2_rule:
  "<(sa X Si) * emp * \<up>(y < length fs)> bm_ins2 Si y 
   <\<lambda> r. sa X Si * emp * \<up>(r = rt.part_ins (rt.part_prep X) y)>"
  by (cases Si rule: prod_cases5) (sep_auto simp: bm_ins2_def rt.part_ins heap: part_ins_imp_rule)

lemma exch1_rule:
  "<(sa X Si) * emp * \<up>(x < length fs \<and> y < length fs)> bm_exch1 Si x y 
   <\<lambda> r. sa X Si * emp * \<up>(r = lf.part_exch (lf.part_prep X) x y)>"
  by (cases Si rule: prod_cases5) (sep_auto simp: bm_exch1_def lf.part_exch_def heap: part_exch_imp_rule)

lemma exch2_rule:
  "<(sa X Si) * emp * \<up>(x < length fs \<and> y < length fs)> bm_exch2 Si x y 
   <\<lambda> r. sa X Si * emp * \<up>(r = rt.part_exch (rt.part_prep X) x y)>"
  by (cases Si rule: prod_cases5) (sep_auto simp: bm_exch2_def rt.part_exch_def heap: part_exch_imp_rule)

text \<open>The elements are the positions themselves, so the indexation is the identity.\<close>

lemma mi_inst:
  "matroid_intersection_imp (length fs) id id bm_memb bm_ins1 bm_exch1 bm_ins2 bm_exch2 bm_ins bm_del
     part_npts_imp part_pt_imp part_npts_imp part_pt_imp {0..<length fs} lf.part_prep lf.part_ins 
     lf.part_exch lf.part_indep sa emp (part_pts fs) (part_pst (length fs) fs) rt.part_prep 
     rt.part_ins rt.part_exch rt.part_indep emp (part_pts ts) (part_pst (length fs) ts)"
  apply (intro matroid_intersection_imp.intro indexed_oracle_imp.intro matroid_ids.intro
        indexed_oracle_imp_axioms.intro fixed_univ_set_basic_imp.intro set_fixed_univ_set
        fixed_univ_set_basic_imp_axioms.intro)
  subgoal by (rule bij_betw_id)
  subgoal by simp
  subgoal by (rule lf.indep_oracle_axioms)
  subgoal using ins1_rule by simp
  subgoal using exch1_rule by simp
  subgoal by (simp add: part_pts_sorted)
  subgoal for x y using part_pts_bound[of y fs x] by simp
  subgoal by (intro part_pts_cover) (auto simp: lf.part_exch_def)
  subgoal using part_npts_rule by simp
  subgoal using part_pt_rule by simp
  subgoal by (rule bij_betw_id)
  subgoal by simp
  subgoal by (rule rt.indep_oracle_axioms)
  subgoal using ins2_rule by simp
  subgoal using exch2_rule by simp
  subgoal by (simp add: part_pts_sorted)
  subgoal for x y using part_pts_bound[of y ts x] lengths by simp
  subgoal using lengths by (intro part_pts_cover) (auto simp: rt.part_exch_def)
  subgoal using part_npts_rule by simp
  subgoal using part_pt_rule by simp
  subgoal by (sep_auto heap: bm_ins_rule)
  subgoal by (sep_auto heap: bm_del_rule)
  subgoal by (sep_auto heap: bm_memb_rule)
  done

interpretation m: matroid_intersection_imp where n = "length fs" and idx = id and elt = id
  and smemb_imp = bm_memb and ins1_imp = bm_ins1 and exch1_imp = bm_exch1 and ins2_imp = bm_ins2 
  and exch2_imp = bm_exch2 and sins_imp = bm_ins and sdel_imp = bm_del 
  and npts1_imp = part_npts_imp and pt1_imp = part_pt_imp and npts2_imp = part_npts_imp 
  and pt2_imp = part_pt_imp and carrier = "{0..<length fs}"
  and sol_assn = sa and ost1 = emp and ost2 = emp
  and orcl_prep1 = lf.part_prep and ins_orcl1 = lf.part_ins and exch_orcl1 = lf.part_exch
  and orcl_prep2 = rt.part_prep and ins_orcl2 = rt.part_ins and exch_orcl2 = rt.part_exch
  and indep1 = lf.part_indep and indep2 = rt.part_indep 
  and pts1 = "part_pts fs" and pst1 = "part_pst (length fs) fs"
  and pts2 = "part_pts ts" and pst2 = "part_pst (length fs) ts"
  by (rule mi_inst)

lemma is_max_matching:
  assumes "m.is_max X"
  shows "max_card_matching ((\<lambda> i. {fs ! i, ts ! i}) ` {0..<length fs}) ((\<lambda> i. {fs ! i, ts ! i}) ` X)"
proof-
  have ind: "lf.part_indep X" "rt.part_indep X"
    and mx: "\<nexists> Y. lf.part_indep Y \<and> rt.part_indep Y \<and> card Y > card X"
    using assms unfolding m.is_max_def by simp_all
  have card: "card ((\<lambda> i. {fs ! i, ts ! i}) ` Y) = card Y" if "lf.part_indep Y" for Y
  proof-
    have "Y \<subseteq> {0..<length fs}"
      using that unfolding lf.part_indep_def by simp
    then show ?thesis
      by (rule card_image[OF inj_on_subset[OF dbltn_inj]])
  qed
  have gm: "graph_matching ((\<lambda> i. {fs ! i, ts ! i}) ` {0..<length fs}) ((\<lambda> i. {fs ! i, ts ! i}) ` X)"
    by (rule indep_matching[OF ind])
  have le: "card M \<le> card ((\<lambda> i. {fs ! i, ts ! i}) ` X)"
    if M: "M \<subseteq> (\<lambda> i. {fs ! i, ts ! i}) ` {0..<length fs}" "matching M" for M
  proof-
    obtain Y where Y: "M = (\<lambda> i. {fs ! i, ts ! i}) ` Y" "lf.part_indep Y" "rt.part_indep Y"
      using matching_indep[OF M] .
    have "card Y \<le> card X"
      using mx Y(2,3) by (simp add: not_less)
    then show ?thesis
      unfolding Y(1) card[OF Y(2)] card[OF ind(1)] .
  qed
  show ?thesis
    unfolding max_card_matching_def
  proof(intro conjI allI impI)
    show "(\<lambda> i. {fs ! i, ts ! i}) ` X \<subseteq> (\<lambda> i. {fs ! i, ts ! i}) ` {0..<length fs}"
      using gm by (rule conjunct2)
    show "matching ((\<lambda> i. {fs ! i, ts ! i}) ` X)"
      using gm by (rule conjunct1)
  next
    fix M
    assume "M \<subseteq> (\<lambda> i. {fs ! i, ts ! i}) ` {0..<length fs} \<and> matching M"
    then show "card M \<le> card ((\<lambda> i. {fs ! i, ts ! i}) ` X)"
      by (intro le) simp_all
  qed
qed

text \<open>The generic algorithm on the allocated handles.\<close>

theorem handles_correct:
  "<(part_pst (length fs) fs H1) * part_pst (length fs) ts H2 * bool_array_set_assn (length fs) {} Xi * 
    cnt_assn nv fs {} C1 * cnt_assn nv ts {} C2 * 
    blocks_assn (length fs) nv fs Fa * blocks_assn (length fs) nv ts Ta>
     mx_mi (length fs) H1 H2 (Xi, C1, C2, Fa, Ta)
   <\<lambda> _. \<exists>\<^sub>A X. bool_array_set_assn (length fs) X Xi * blocks_assn (length fs) nv fs Fa * 
              blocks_assn (length fs) nv ts Ta * true * 
              \<up>(max_card_matching ((\<lambda> i. {fs ! i, ts ! i}) ` {0..<length fs}) 
                                   ((\<lambda> i. {fs ! i, ts ! i}) ` X))>"
  by (rule ht_cons[OF _ _ m.mi_imp_correct[folded mx_mi_def]])
     ((simp only: bm_sol_assn.simps star_aci, rule ent_refl), 
      sep_auto dest: is_max_matching)

subsubsection \<open>The Program\<close>

theorem matching_imp_correct:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts> matching_imp nv Fa Ta 
   <\<lambda> Xi. \<exists>\<^sub>A X. bool_array_set_assn (length fs) X Xi * Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * true * 
              \<up>(max_card_matching ((\<lambda> i. {fs ! i, ts ! i}) ` {0..<length fs}) 
                                   ((\<lambda> i. {fs ! i, ts ! i}) ` X))>"
  unfolding matching_imp_def
  apply (rule ht_cons_pre[OF _ bm_setup_rule[where F = emp]], simp)
  apply (rule ht_bind[OF ht_frame_ac[OF handles_correct, where R = true]])
    prefer 3 apply (rule ht_return_wp)
   apply (simp only: star_aci, rule ent_refl)
  apply (sep_auto simp: blocks_assn_def)
  done

end

end
