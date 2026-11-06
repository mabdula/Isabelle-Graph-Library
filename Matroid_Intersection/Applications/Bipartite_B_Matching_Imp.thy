theory Bipartite_B_Matching_Imp
  imports Matroid_Intersection_Imp Bipartite_Arrays Capacity_Partition_Oracle_Imp
begin

(*TODO Once we have more b matching theory, set up own b-matching
    theory in Basic_Matching Session and put b-matching defs there.*)

section \<open>Maximum Bipartite b-Matching in Imperative HOL\<close>

subsection \<open>b-Matchings\<close>

text \<open>Like a matching, but every vertex \<open>v\<close> may be covered by up to \<open>b v\<close> edges.\<close>

definition b_matching :: "('a \<Rightarrow> nat) \<Rightarrow> 'a graph \<Rightarrow> bool" where
  "b_matching b M \<longleftrightarrow> (\<forall> v. degree M v \<le> enat (b v))"

abbreviation "graph_b_matching G b M \<equiv> b_matching b M \<and> M \<subseteq> G"

definition max_card_b_matching :: "'a graph \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> 'a graph \<Rightarrow>
    bool" where
  "max_card_b_matching G b M \<longleftrightarrow>
     M \<subseteq> G \<and> b_matching b M \<and> (\<forall> M'. M' \<subseteq> G \<and> b_matching b M'
       \<longrightarrow> card M' \<le> card M)"

text \<open>The two endpoint arrays represent the edges \<open>{fs ! i, ts ! i}\<close>; a third array holds
  the vertex capacities. The partition matroids group edge positions by their left and right
  endpoints and enforce these capacities. The generic algorithm of
  @{theory Matroid_Intersection.Matroid_Intersection_Imp} uses a solution handle with the Boolean
  solution array, two block counters, both endpoint arrays and the shared capacity array. Partner
  handles group edges by endpoint and store the range of the block of each edge.\<close>

subsection \<open>Code\<close>

type_synonym bb_sol =
  "bool array \<times> nat array \<times> nat array \<times> nat array \<times> nat array \<times> nat array"

definition bb_memb :: "nat \<Rightarrow> bb_sol \<Rightarrow> bool Heap" where
  "bb_memb x Si = (case Si of (Xi, C1, C2, Bl, Br, K) \<Rightarrow> bm_memb x (Xi, C1, C2, Bl, Br))"

definition bb_ins :: "nat \<Rightarrow> bb_sol \<Rightarrow> unit Heap" where
  "bb_ins x Si = (case Si of (Xi, C1, C2, Bl, Br, K) \<Rightarrow> bm_ins x (Xi, C1, C2, Bl, Br))"

definition bb_del :: "nat \<Rightarrow> bb_sol \<Rightarrow> unit Heap" where
  "bb_del x Si = (case Si of (Xi, C1, C2, Bl, Br, K) \<Rightarrow> bm_del x (Xi, C1, C2, Bl, Br))"

definition bb_ins1 :: "bb_sol \<Rightarrow> nat \<Rightarrow> bool Heap" where
  "bb_ins1 Si y = (case Si of (Xi, C1, C2, Bl, Br, K) \<Rightarrow> part_cap_ins_imp Bl K C1 y)"

definition bb_exch1 :: "bb_sol \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool Heap" where
  "bb_exch1 Si x y = (case Si of (Xi, C1, C2, Bl, Br, K) \<Rightarrow> part_exch_imp Bl x y)"

definition bb_ins2 :: "bb_sol \<Rightarrow> nat \<Rightarrow> bool Heap" where
  "bb_ins2 Si y = (case Si of (Xi, C1, C2, Bl, Br, K) \<Rightarrow> part_cap_ins_imp Br K C2 y)"

definition bb_exch2 :: "bb_sol \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool Heap" where
  "bb_exch2 Si x y = (case Si of (Xi, C1, C2, Bl, Br, K) \<Rightarrow> part_exch_imp Br x y)"

global_interpretation bx: matroid_intersection_imp_spec n id id bb_memb bb_ins1 bb_exch1
  bb_ins2 bb_exch2 bb_ins bb_del part_npts_imp part_pt_imp part_npts_imp part_pt_imp
  for n
  defines bx_nb1 = bx.ids.nb1_imp
    and bx_nb2 = bx.ids.nb2_imp
    and bx_filt = bx.ids.filt_imp
    and bx_xnbs = bx.ids.xnbs
    and bx_x_inner = bx.ids.x_inner
    and bx_x_outer = bx.ids.x_outer
    and bx_xround = bx.ids.xround
    and bx_x_loop = bx.ids.x_loop
    and bx_bfs_run = bx.ids.bfs_run
    and bx_has_nb = bx.ids.has_nb_imp
    and bx_s = bx.ids.s_imp
    and bx_t = bx.ids.t_imp
    and bx_st = bx.ids.st_imp
    and bx_src = bx.ids.is_src_imp
    and bx_tgt = bx.ids.is_tgt_imp
    and bx_tail = bx.ids.tail_imp
    and bx_round = bx.ids.round_imp
    and bx_aug_path = bx.ids.aug_path_imp
    and bx_mi_ids = bx.ids.mi_imp
    and bx_mi = bx.mi_imp
  done

text \<open>The BFS of the library with the iterator fixed at code generation time.\<close>

declare bx.ids.x_inner_code[code] bx.ids.x_outer_code[code] bx.ids.xround_code[code]
  bx.ids.x_loop_code[code] bx.ids.bfs_run_code[code]

text \<open>The edges are \<open>{Fa[i], Ta[i]}\<close>, the capacity of vertex \<open>v\<close> is
    \<open>Ka[v]\<close>, and all vertices
  are below the length of \<open>Ka\<close>.\<close>

definition "bb_setup_imp Fa Ta Ka k = do { nv \<leftarrow> Array.len Ka; bm_setup_imp nv Fa Ta k }"

definition "b_matching_imp Fa Ta Ka =
   bb_setup_imp Fa Ta Ka (\<lambda> m H1 H2 Xi C1 C2. do {
     bx_mi m H1 H2 (Xi, C1, C2, Fa, Ta, Ka);
     return Xi })"

export_code b_matching_imp checking SML_imp

text \<open>A small example where the vertices \<open>1\<close> and \<open>10\<close> may be used twice and all others
  once: the edges of the returned array. The result is
  \<open>[(1, 6), (1, 8), (3, 10), (7, 10)]\<close>.\<close>

ML_val \<open>
  let
    val nat = @{code nat_of_integer}
    val es = [(1, 6), (1, 8), (1, 10), (3, 6), (3, 10), (9, 8), (7, 10)]
    val Fa = Array.fromList (map (nat o #1) es)
    val Ta = Array.fromList (map (nat o #2) es)
    val Ka = Array.fromList (map nat [0, 2, 0, 1, 0, 0, 1, 1, 1, 1, 2])
    val r = @{code b_matching_imp} Fa Ta Ka ()
  in
    List.filter (fn (j, _) => Array.sub (r, j)) (ListPair.zip (List.tabulate (length es, I), es))
    |> map #2
  end
\<close>

subsection \<open>Correctness\<close>

subsubsection \<open>The Solution Handle\<close>

fun bb_sol_assn ::
  "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> (nat \<Rightarrow> nat)
    \<Rightarrow> nat set \<Rightarrow> bb_sol \<Rightarrow> assn"
  where
  "bb_sol_assn m nb bl br cap X (Xi, C1, C2, Bl, Br, K) =
     bool_array_set_assn m X Xi * cnt_assn nb bl X C1 * cnt_assn nb br X C2 *
     blocks_assn m nb bl Bl * blocks_assn m nb br Br * caps_assn nb cap K"

lemma bb_memb_rule:
  "<bb_sol_assn m nb bl br cap X Si * \<up>(x < m)> bb_memb x Si
   <\<lambda> r. bb_sol_assn m nb bl br cap X Si * \<up>(r = (x \<in> X))>"
  by (cases Si rule: prod_cases6) (sep_auto simp: bb_memb_def bm_memb_def heap: bool_array_set_memb_rule)

lemma bb_ins_rule:
  "<bb_sol_assn m nb bl br cap X Si * \<up>(x < m)> bb_ins x Si
   <\<lambda> _. bb_sol_assn m nb bl br cap (Set.insert x X) Si>"
  by (cases Si rule: prod_cases6) (sep_auto simp: bb_ins_def bm_ins_def insert_absorb
      heap: bool_array_set_memb_rule bool_array_set_upd_rule part_cnt_ins_rule)

lemma bb_del_rule:
  "<bb_sol_assn m nb bl br cap X Si * \<up>(x < m)> bb_del x Si
   <\<lambda> _. bb_sol_assn m nb bl br cap (X - {x}) Si>"
  by (cases Si rule: prod_cases6) (sep_auto simp: bb_del_def bm_del_def
      heap: bool_array_set_memb_rule bool_array_set_upd_rule part_cnt_del_rule)

subsubsection \<open>The Instance\<close>

text \<open>The graph and its representation are those of
  @{locale bipartite_matching_imp}; the capacities are the list \<open>ks\<close>.\<close>

locale bipartite_b_matching_imp = bipartite_matching_imp "length ks" fs ts
  for fs ts ks :: "nat list"
begin

abbreviation "sb \<equiv> bb_sol_assn (length fs) (length ks) fs ts (\<lambda> v. ks ! v)"

sublocale lf: cap_partition_oracle "{0..<length fs}" "\<lambda> i. fs ! i" "\<lambda> v. ks ! v"
  by (unfold_locales; simp)

sublocale rt: cap_partition_oracle "{0..<length fs}" "\<lambda> i. ts ! i" "\<lambda> v. ks ! v"
  by (unfold_locales; simp)

text \<open>The degree of a vertex in the represented edge set counts the positions with this
  vertex as left or as right endpoint; one of the two counts is zero.\<close>

lemma blocks_disjoint: "X \<subseteq> {0..<length fs} \<Longrightarrow>
    {i \<in> X. fs ! i = v} \<inter> {i \<in> X. ts ! i = v} = {}"
  by (rule equals0I, rename_tac i, rule_tac P = "fs ! i = ts ! i" in notE, rule left_right) auto

lemma degree_img:
  assumes "X \<subseteq> {0..<length fs}"
  shows "degree ((\<lambda> i. {fs ! i, ts ! i}) ` X) v =
           enat (blk_card (\<lambda> i. fs ! i) X v + blk_card (\<lambda> i. ts ! i) X v)"
proof-
  note fin = finite_subset[OF assms finite_atLeastLessThan]
  have img: "{e \<in> (\<lambda> i. {fs ! i, ts ! i}) ` X. v \<in> e} =
      (\<lambda> i. {fs ! i, ts ! i}) ` ({i \<in> X. fs ! i = v} \<union> {i \<in> X. ts ! i = v})"
    by blast
  have "card {e \<in> (\<lambda> i. {fs ! i, ts ! i}) ` X. v \<in> e} =
      blk_card (\<lambda> i. fs ! i) X v + blk_card (\<lambda> i. ts ! i) X v"
    unfolding img
    using assms fin
    by (subst card_image)
       (auto intro: inj_on_subset[OF dbltn_inj] simp: blk_card_def card_Un_disjoint blocks_disjoint)
  then show ?thesis
    using fin unfolding degree_def2 card'_def
    by simp
qed

lemma one_side:
  assumes "X \<subseteq> {0..<length fs}"
  shows "blk_card (\<lambda> i. fs ! i) X v = 0 \<or> blk_card (\<lambda> i. ts ! i) X v = 0"
proof(rule ccontr)
  assume "\<not> (blk_card (\<lambda> i. fs ! i) X v = 0 \<or> blk_card (\<lambda> i. ts ! i) X v = 0)"
  then obtain i j where "i \<in> X" "j \<in> X" "fs ! i = v" "ts ! j = v"
    by (auto simp: blk_card_def card_gt_0_iff)
  then show False
    using assms left_right[of i j]
    by (fastforce)
qed

text \<open>Sets of positions independent in both matroids are those representing b-matchings.\<close>

lemma block_cap_sum: "X \<subseteq> {0..<length fs} \<Longrightarrow>
    (blk_card (\<lambda> i. fs ! i) X v + blk_card (\<lambda> i. ts ! i) X v \<le> k) =
    (blk_card (\<lambda> i. fs ! i) X v \<le> k \<and> blk_card (\<lambda> i. ts ! i) X v \<le> k)"
  by (drule one_side[where v = v]) auto

lemma indep_b_matching:
  "(lf.cap_indep X \<and> rt.cap_indep X) =
     (X \<subseteq> {0..<length fs} \<and> b_matching (\<lambda> v. ks ! v) ((\<lambda> i. {fs ! i, ts ! i}) ` X))"
  by (cases "X \<subseteq> {0..<length fs}")
     (auto simp: lf.cap_indep_def rt.cap_indep_def b_matching_def degree_img block_cap_sum)

lemma ins1_rule:
  "<(sb X Si) * emp * \<up>(y < length fs)> bb_ins1 Si y
   <\<lambda> r. sb X Si * emp * \<up>(r = lf.cap_ins X y)>"
  by (cases Si rule: prod_cases6) (sep_auto simp: bb_ins1_def lf.cap_ins_def heap: part_cap_ins_rule)

lemma ins2_rule:
  "<(sb X Si) * emp * \<up>(y < length fs)> bb_ins2 Si y
   <\<lambda> r. sb X Si * emp * \<up>(r = rt.cap_ins X y)>"
  by (cases Si rule: prod_cases6) (sep_auto simp: bb_ins2_def rt.cap_ins_def heap: part_cap_ins_rule)

lemma exch1_rule:
  "<(sb X Si) * emp * \<up>(x < length fs \<and> y < length fs)> bb_exch1 Si x y
   <\<lambda> r. sb X Si * emp * \<up>(r = lf.cap_exch X x y)>"
  by (cases Si rule: prod_cases6) (sep_auto simp: bb_exch1_def lf.cap_exch_def heap: part_exch_imp_rule)

lemma exch2_rule:
  "<(sb X Si) * emp * \<up>(x < length fs \<and> y < length fs)> bb_exch2 Si x y
   <\<lambda> r. sb X Si * emp * \<up>(r = rt.cap_exch X x y)>"
  by (cases Si rule: prod_cases6) (sep_auto simp: bb_exch2_def rt.cap_exch_def heap: part_exch_imp_rule)

text \<open>The elements are the positions themselves, so the indexation is the identity.\<close>

lemma mi_inst:
  "matroid_intersection_imp (length fs) id id bb_memb bb_ins1 bb_exch1 bb_ins2 bb_exch2 bb_ins bb_del
     part_npts_imp part_pt_imp part_npts_imp part_pt_imp {0..<length fs} (\<lambda> X. X) lf.cap_ins
     lf.cap_exch lf.cap_indep sb emp (part_pts fs) (part_pst (length fs) fs) (\<lambda> X. X) rt.cap_ins
     rt.cap_exch rt.cap_indep emp (part_pts ts) (part_pst (length fs) ts)"
  apply(intro matroid_intersection_imp.intro indexed_oracle_imp.intro matroid_ids.intro
        indexed_oracle_imp_axioms.intro fixed_univ_set_basic_imp.intro set_fixed_univ_set
        fixed_univ_set_basic_imp_axioms.intro)
  subgoal
  by (rule bij_betw_id)
  subgoal
  by simp
  subgoal
  by (rule lf.indep_oracle_axioms)
  subgoal
  by (use ins1_rule in simp)
  subgoal
  by (use exch1_rule in simp)
  subgoal
  by (simp add: part_pts_sorted)
  subgoal for x y
  using part_pts_bound[of y fs x]
  by simp
  subgoal
  by (intro part_pts_cover) (auto simp: lf.cap_exch_def)
  subgoal
  by (use part_npts_rule in simp)
  subgoal
  by (use part_pt_rule in simp)
  subgoal
  by (rule bij_betw_id)
  subgoal
  by simp
  subgoal
  by (rule rt.indep_oracle_axioms)
  subgoal
  by (use ins2_rule in simp)
  subgoal
  by (use exch2_rule in simp)
  subgoal
  by (simp add: part_pts_sorted)
  subgoal for x y
  using part_pts_bound[of y ts x] lengths
  by simp
  subgoal
  using lengths
  by (intro part_pts_cover) (auto simp: rt.cap_exch_def)
  subgoal
  by (use part_npts_rule in simp)
  subgoal
  by (use part_pt_rule in simp)
  subgoal
  by (sep_auto heap: bb_ins_rule)
  subgoal
  by (sep_auto heap: bb_del_rule)
  subgoal
  by (sep_auto heap: bb_memb_rule)
  done

interpretation m: matroid_intersection_imp where n = "length fs" and idx = id and elt = id
  and smemb_imp = bb_memb and ins1_imp = bb_ins1 and exch1_imp = bb_exch1 and ins2_imp = bb_ins2
  and exch2_imp = bb_exch2 and sins_imp = bb_ins and sdel_imp = bb_del
  and npts1_imp = part_npts_imp and pt1_imp = part_pt_imp and npts2_imp = part_npts_imp
  and pt2_imp = part_pt_imp and carrier = "{0..<length fs}"
  and sol_assn = sb and ost1 = emp and ost2 = emp
  and orcl_prep1 = "\<lambda> X. X" and ins_orcl1 = lf.cap_ins and exch_orcl1 = lf.cap_exch
  and orcl_prep2 = "\<lambda> X. X" and ins_orcl2 = rt.cap_ins and exch_orcl2 = rt.cap_exch
  and indep1 = lf.cap_indep and indep2 = rt.cap_indep
  and pts1 = "part_pts fs" and pst1 = "part_pst (length fs) fs"
  and pts2 = "part_pts ts" and pst2 = "part_pst (length fs) ts"
  by (rule mi_inst)

lemma b_matching_indep:
  assumes "M \<subseteq> (\<lambda> i. {fs ! i, ts ! i}) ` {0..<length fs}" "b_matching (\<lambda> v. ks ! v) M"
  obtains Y where "M = (\<lambda> i. {fs ! i, ts ! i}) ` Y" "lf.cap_indep Y" "rt.cap_indep Y"
proof-
  obtain Y where "Y \<subseteq> {0..<length fs}" "M = (\<lambda> i. {fs ! i, ts ! i}) ` Y"
    using assms(1)
    by (rule subset_imageE)
  then show ?thesis
    using assms(2) indep_b_matching[of Y] that[of Y]
    by auto
qed

lemma b_matching_card:
  "lf.cap_indep X \<Longrightarrow> card ((\<lambda> i. {fs ! i, ts ! i}) ` X) = card X"
  by (rule card_image, rule inj_on_subset[OF dbltn_inj]) (simp add: lf.cap_indep_def)

lemma is_max_b_matching:
  assumes "m.is_max X"
  shows "max_card_b_matching ((\<lambda> i. {fs ! i, ts ! i}) ` {0..<length fs}) (\<lambda> v. ks ! v)
           ((\<lambda> i. {fs ! i, ts ! i}) ` X)"
proof(unfold max_card_b_matching_def, intro conjI allI impI, goal_cases)
  case 1
  then show ?case
    using assms unfolding m.is_max_def lf.cap_indep_def
    by auto
next
  case 2
  show ?case
    using assms[unfolded m.is_max_def] indep_b_matching[of X]
    by auto
next
  case (3 M)
  then obtain Y where "M = (\<lambda> i. {fs ! i, ts ! i}) ` Y" "lf.cap_indep Y" "rt.cap_indep Y"
    by (auto elim: b_matching_indep)
  then show ?case
    using assms
    by (auto simp: m.is_max_def b_matching_card)
qed

text \<open>The generic algorithm on the allocated handles.\<close>

theorem handles_correct:
  "<(part_pst (length fs) fs H1) * part_pst (length fs) ts H2 * bool_array_set_assn (length fs) {} Xi *
    cnt_assn (length ks) fs {} C1 * cnt_assn (length ks) ts {} C2 *
    blocks_assn (length fs) (length ks) fs Fa * blocks_assn (length fs) (length ks) ts Ta *
    caps_assn (length ks) (\<lambda> v. ks ! v) Ka>
     bx_mi (length fs) H1 H2 (Xi, C1, C2, Fa, Ta, Ka)
   <\<lambda> _. \<exists>\<^sub>A X. bool_array_set_assn (length fs) X Xi * blocks_assn (length fs) (length ks) fs Fa *
              blocks_assn (length fs) (length ks) ts Ta * caps_assn (length ks) (\<lambda> v. ks ! v) Ka *
              true *
              \<up>(max_card_b_matching ((\<lambda> i. {fs ! i, ts ! i}) ` {0..<length fs}) (\<lambda> v. ks ! v)
                                     ((\<lambda> i. {fs ! i, ts ! i}) ` X))>"
  by (rule ht_cons[OF _ _ m.mi_imp_correct[folded bx_mi_def]])
     ((simp only: bb_sol_assn.simps star_aci, rule ent_refl),
      sep_auto dest: is_max_b_matching)

subsubsection \<open>The Program\<close>

lemma caps_in: "Ka \<mapsto>\<^sub>a ks = caps_assn (length ks) (\<lambda> v. ks ! v) Ka"
  unfolding caps_assn_def map_nth ..

text \<open>The allocation prologue of @{locale bipartite_matching_imp}, after reading the number of
  vertices from the capacity array.\<close>

lemma bb_len_rule:
  "<F * Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Ka \<mapsto>\<^sub>a ks> Array.len Ka
    <\<lambda> r. F * caps_assn (length ks) (\<lambda> v. ks ! v) Ka * Fa \<mapsto>\<^sub>a fs *
      Ta \<mapsto>\<^sub>a ts * \<up>(r = length ks)>"
  by (sep_auto simp: caps_assn_def map_nth)

lemma bb_setup_rule:
  assumes "\<And> H1 H2 Xi C1 C2.
    <F * caps_assn (length ks) (\<lambda> v. ks ! v) Ka * part_pst (length fs) fs H1 *
       part_pst (length fs) ts H2 * bool_array_set_assn (length fs) {} Xi *
       cnt_assn (length ks) fs {} C1 * cnt_assn (length ks) ts {} C2 *
       blocks_assn (length fs) (length ks) fs Fa * blocks_assn (length fs) (length ks) ts Ta * true>
      k (length fs) H1 H2 Xi C1 C2 <Q>"
  shows "<F * Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Ka \<mapsto>\<^sub>a ks> bb_setup_imp Fa Ta Ka k <Q>"
  unfolding bb_setup_imp_def
  by (rule ht_bind[OF bb_len_rule], rule ht_pure_pre, simp only:,
      rule bm_setup_rule[where F = "F * caps_assn (length ks) (\<lambda> v. ks ! v) Ka"
        and Fa = Fa and Ta = Ta and k = k, OF assms])

theorem b_matching_imp_correct:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Ka \<mapsto>\<^sub>a ks> b_matching_imp Fa Ta Ka
   <\<lambda> Xi. \<exists>\<^sub>A X. bool_array_set_assn (length fs) X Xi * Fa \<mapsto>\<^sub>a fs * Ta
     \<mapsto>\<^sub>a ts * Ka \<mapsto>\<^sub>a ks * true *
              \<up>(max_card_b_matching ((\<lambda> i. {fs ! i, ts ! i}) ` {0..<length fs}) (\<lambda> v. ks ! v)
                                     ((\<lambda> i. {fs ! i, ts ! i}) ` X))>"
  unfolding b_matching_imp_def
  apply(rule ht_cons_pre[OF _ bb_setup_rule[where F = emp]], simp)
  apply(rule ht_bind[OF ht_frame_ac[OF handles_correct, where R = true]])
    prefer 3 apply(rule ht_return_wp)
   apply(simp only: star_aci, rule ent_refl)
  apply(sep_auto simp: blocks_assn_def caps_assn_def map_nth)
  done

end

end
