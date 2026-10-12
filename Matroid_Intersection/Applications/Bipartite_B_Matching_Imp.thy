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

definition max_card_b_matching :: "'a graph \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> 'a graph \<Rightarrow> bool" where
  "max_card_b_matching G b M \<longleftrightarrow> 
     M \<subseteq> G \<and> b_matching b M \<and> (\<forall> M'. M' \<subseteq> G \<and> b_matching b M' \<longrightarrow> card M' \<le> card M)"

text \<open>The input graph is given by two arrays of the same length \<open>m\<close>: edge \<open>i\<close> joins the
  left vertex \<open>fs ! i\<close> and the right vertex \<open>ts ! i\<close>. A third array holds the vertex
  capacities, and all vertices are below its length. The elements of the matroids are the edges,
  i.e. their positions, and the matroids are the partition matroids of the left and the right
  endpoints with these capacities; the algorithm is the generic one of
  @{theory Matroid_Intersection.Matroid_Intersection_Imp}. The solution handle consists of the
  Boolean array of the solution, the two arrays counting the solution elements per block, the two
  input arrays of blocks and the capacity array, which both oracles share since the sides are
  disjoint; the partner handles hold the edges grouped by block and the range of the block of
  every edge.\<close>

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
    and bx_xround = bx.ids.xround
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

text \<open>A copy of the BFS core with the iterator fixed at code generation time.\<close>

global_interpretation xbb: BFS_subprocedures_lists_code bset_memb bset_ins "bx_xnbs n"
  for n
  defines xbb_inner = xbb.inner_loop
    and xbb_outer = xbb.outer_loop
    and xbb_round = xbb.next_frontier_current_parents_imp
  done

global_interpretation xbbi: BFS_Imperative_spec bfs_src_to_cf bfs_set_srcs_visited
    "xbb_round n Gh" bfs_cf_is_empty bset_memb bfs_set_dists Array.nth Array.nth
  for n Gh
  defines xbb_loop = xbbi.BFS_par_imp
    and xbb_init = xbbi.initial_state_imp
    and xbb_run = xbbi.visited_dists_parents_imp
  done

lemma bx_xround_code [code]: "bx_xround n = xbb_round n"
  unfolding bx.ids.xround_def xbb_round_def ..

lemma bx_bfs_run_code [code]: "bx_bfs_run n Gh = xbb_run n Gh"
  unfolding bx.ids.bfs_run_def xbb_run_def bx_xround_code ..

declare xbbi.BFS_par_imp.simps[code]

text \<open>The edges are \<open>{Fa[i], Ta[i]}\<close>, the capacity of vertex \<open>v\<close> is \<open>Ka[v]\<close>, and all vertices
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
  "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat set \<Rightarrow> bb_sol \<Rightarrow> assn"
  where
  "bb_sol_assn m nb bl br cap X (Xi, C1, C2, Bl, Br, K) =
     xset_assn m X Xi * cnt_assn nb bl X C1 * cnt_assn nb br X C2 *
     blocks_assn m nb bl Bl * blocks_assn m nb br Br * caps_assn nb cap K"

lemma bb_memb_rule:
  "<bb_sol_assn m nb bl br cap X Si * \<up>(x < m)> bb_memb x Si
   <\<lambda> r. bb_sol_assn m nb bl br cap X Si * \<up>(r = (x \<in> X))>"
  by (cases Si rule: prod_cases6) (sep_auto simp: bb_memb_def bm_memb_def heap: xset_memb_rule)

lemma bb_ins_rule:
  "<bb_sol_assn m nb bl br cap X Si * \<up>(x < m)> bb_ins x Si
   <\<lambda> _. bb_sol_assn m nb bl br cap (Set.insert x X) Si>"
  by (cases Si rule: prod_cases6)
     (sep_auto simp: bb_ins_def bm_ins_def insert_absorb
        heap: xset_memb_rule xset_upd_rule part_cnt_ins_rule)

lemma bb_del_rule:
  "<bb_sol_assn m nb bl br cap X Si * \<up>(x < m)> bb_del x Si
   <\<lambda> _. bb_sol_assn m nb bl br cap (X - {x}) Si>"
proof-
  have "x \<notin> X \<Longrightarrow> X - {x} = X"
    by blast
  then show ?thesis
    by (cases Si rule: prod_cases6)
       (sep_auto simp: bb_del_def bm_del_def heap: xset_memb_rule xset_upd_rule part_cnt_del_rule)
qed

subsubsection \<open>The Instance\<close>

text \<open>The graph and its representation are those of
  @{locale bipartite_matching_imp}; the capacities are the list \<open>ks\<close>.\<close>

locale bipartite_b_matching_imp = bipartite_matching_imp "length ks" fs ts
  for fs ts ks :: "nat list"
begin

abbreviation "sb \<equiv> bb_sol_assn (length fs) (length ks) fs ts (\<lambda> v. ks ! v)"

sublocale lf: cap_partition_oracle "{0..<length fs}" "\<lambda> i. fs ! i" "\<lambda> v. ks ! v"
  by unfold_locales simp

sublocale rt: cap_partition_oracle "{0..<length fs}" "\<lambda> i. ts ! i" "\<lambda> v. ks ! v"
  by unfold_locales simp

text \<open>The degree of a vertex in the represented edge set counts the positions with this
  vertex as left or as right endpoint; one of the two counts is zero.\<close>

lemma degree_img:
  assumes X: "X \<subseteq> {0..<length fs}"
  shows "degree ((\<lambda> i. {fs ! i, ts ! i}) ` X) v = 
           enat (blk_card (\<lambda> i. fs ! i) X v + blk_card (\<lambda> i. ts ! i) X v)"
proof-
  have fin: "finite X"
    by (rule finite_subset[OF X]) simp
  have img: "{e \<in> (\<lambda> i. {fs ! i, ts ! i}) ` X. v \<in> e} = 
               (\<lambda> i. {fs ! i, ts ! i}) ` ({i \<in> X. fs ! i = v} \<union> {i \<in> X. ts ! i = v})"
    by blast
  have dis: "{i \<in> X. fs ! i = v} \<inter> {i \<in> X. ts ! i = v} = {}"
  proof(rule equals0I)
    fix i
    assume "i \<in> {i \<in> X. fs ! i = v} \<inter> {i \<in> X. ts ! i = v}"
    then have "i < length fs" "fs ! i = ts ! i"
      using X by auto
    then show False
      using left_right[of i i] by simp
  qed
  have inj: "inj_on (\<lambda> i. {fs ! i, ts ! i}) ({i \<in> X. fs ! i = v} \<union> {i \<in> X. ts ! i = v})"
    by (rule inj_on_subset[OF dbltn_inj]) (use X in blast)
  have "card {e \<in> (\<lambda> i. {fs ! i, ts ! i}) ` X. v \<in> e} = 
          blk_card (\<lambda> i. fs ! i) X v + blk_card (\<lambda> i. ts ! i) X v"
    unfolding img card_image[OF inj] blk_card_def 
    by (rule card_Un_disjoint) (use fin dis in simp_all)
  moreover have "finite {e \<in> (\<lambda> i. {fs ! i, ts ! i}) ` X. v \<in> e}"
    using fin by simp
  ultimately show ?thesis
    unfolding degree_def2 card'_def by simp
qed

lemma one_side:
  assumes X: "X \<subseteq> {0..<length fs}"
  shows "blk_card (\<lambda> i. fs ! i) X v = 0 \<or> blk_card (\<lambda> i. ts ! i) X v = 0"
proof(rule ccontr)

  assume "\<not> (blk_card (\<lambda> i. fs ! i) X v = 0 \<or> blk_card (\<lambda> i. ts ! i) X v = 0)"
  then have "card {i \<in> X. fs ! i = v} \<noteq> 0" "card {i \<in> X. ts ! i = v} \<noteq> 0"
    unfolding blk_card_def by simp_all
  then have "{i \<in> X. fs ! i = v} \<noteq> {}" "{i \<in> X. ts ! i = v} \<noteq> {}"
    by (intro notI, simp)+
  then obtain i j where ij: "i \<in> X" "j \<in> X" "fs ! i = v" "ts ! j = v"
    by blast
  have "i < length fs" "j < length fs"
    using X ij(1,2) by auto
  then show False
    using left_right[of i j] ij(3,4) by simp
qed

text \<open>Sets of positions independent in both matroids are those representing b-matchings.\<close>

lemma indep_b_matching:
  "(lf.cap_indep X \<and> rt.cap_indep X) = 
     (X \<subseteq> {0..<length fs} \<and> b_matching (\<lambda> v. ks ! v) ((\<lambda> i. {fs ! i, ts ! i}) ` X))"
proof(cases "X \<subseteq> {0..<length fs}")
  case True
  have "(blk_card (\<lambda> i. fs ! i) X v \<le> ks ! v \<and> blk_card (\<lambda> i. ts ! i) X v \<le> ks ! v) = 
          (blk_card (\<lambda> i. fs ! i) X v + blk_card (\<lambda> i. ts ! i) X v \<le> ks ! v)" for v
    using one_side[OF True, of v] by auto
  then show ?thesis
    unfolding lf.cap_indep_def rt.cap_indep_def b_matching_def degree_img[OF True]
    using True by auto
qed (simp add: lf.cap_indep_def)

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
  apply (intro matroid_intersection_imp.intro indexed_oracle_imp.intro matroid_ids.intro
        indexed_oracle_imp_axioms.intro matroid_intersection_imp_axioms.intro)
  subgoal by (rule bij_betw_id)
  subgoal by simp
  subgoal by (rule lf.indep_oracle_axioms)
  subgoal using ins1_rule by simp
  subgoal using exch1_rule by simp
  subgoal by (simp add: part_pts_sorted)
  subgoal for x y using part_pts_bound[of y fs x] by simp
  subgoal by (intro part_pts_cover) (auto simp: lf.cap_exch_def)
  subgoal using part_npts_rule by simp
  subgoal using part_pt_rule by simp
  subgoal by (rule bij_betw_id)
  subgoal by simp
  subgoal by (rule rt.indep_oracle_axioms)
  subgoal using ins2_rule by simp
  subgoal using exch2_rule by simp
  subgoal by (simp add: part_pts_sorted)
  subgoal for x y using part_pts_bound[of y ts x] lengths by simp
  subgoal using lengths by (intro part_pts_cover) (auto simp: rt.cap_exch_def)
  subgoal using part_npts_rule by simp
  subgoal using part_pt_rule by simp
  subgoal using bb_memb_rule by simp
  subgoal using bb_ins_rule by simp
  subgoal using bb_del_rule by simp
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

lemma is_max_b_matching:
  assumes "m.is_max X"
  shows "max_card_b_matching ((\<lambda> i. {fs ! i, ts ! i}) ` {0..<length fs}) (\<lambda> v. ks ! v)
           ((\<lambda> i. {fs ! i, ts ! i}) ` X)"
proof-
  have ind: "lf.cap_indep X" "rt.cap_indep X"
    and mx: "\<nexists> Y. lf.cap_indep Y \<and> rt.cap_indep Y \<and> card Y > card X"
    using assms unfolding m.is_max_def by simp_all
  have "X \<subseteq> {0..<length fs} \<and> b_matching (\<lambda> v. ks ! v) ((\<lambda> i. {fs ! i, ts ! i}) ` X)"
    unfolding indep_b_matching[symmetric] using ind by (rule conjI)
  then have X: "X \<subseteq> {0..<length fs}" "b_matching (\<lambda> v. ks ! v) ((\<lambda> i. {fs ! i, ts ! i}) ` X)"
    by simp_all
  have card: "card ((\<lambda> i. {fs ! i, ts ! i}) ` Y) = card Y" if "Y \<subseteq> {0..<length fs}" for Y
    using that by (rule card_image[OF inj_on_subset[OF dbltn_inj]])
  have le: "card M \<le> card ((\<lambda> i. {fs ! i, ts ! i}) ` X)"
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
    then have le: "card ?Y \<le> card X"
      using mx by (simp add: not_less)
    have "card M = card ?Y"
      using arg_cong[OF img, of card] card[OF Y] by (rule trans)
    then show ?thesis
      unfolding card[OF X(1)] using le by simp
  qed
  show ?thesis
    unfolding max_card_b_matching_def
  proof(intro conjI allI impI)
    show "(\<lambda> i. {fs ! i, ts ! i}) ` X \<subseteq> (\<lambda> i. {fs ! i, ts ! i}) ` {0..<length fs}"
      using X(1) by (rule image_mono)
    show "b_matching (\<lambda> v. ks ! v) ((\<lambda> i. {fs ! i, ts ! i}) ` X)"
      by (rule X(2))
  next
    fix M
    assume "M \<subseteq> (\<lambda> i. {fs ! i, ts ! i}) ` {0..<length fs} \<and> b_matching (\<lambda> v. ks ! v) M"
    then show "card M \<le> card ((\<lambda> i. {fs ! i, ts ! i}) ` X)"
      by (intro le) simp_all
  qed
qed

text \<open>The generic algorithm on the allocated handles.\<close>

theorem handles_correct:
  "<(part_pst (length fs) fs H1) * part_pst (length fs) ts H2 * xset_assn (length fs) {} Xi *
    cnt_assn (length ks) fs {} C1 * cnt_assn (length ks) ts {} C2 *
    blocks_assn (length fs) (length ks) fs Fa * blocks_assn (length fs) (length ks) ts Ta *
    caps_assn (length ks) (\<lambda> v. ks ! v) Ka>
     bx_mi (length fs) H1 H2 (Xi, C1, C2, Fa, Ta, Ka)
   <\<lambda> _. \<exists>\<^sub>A X. xset_assn (length fs) X Xi * blocks_assn (length fs) (length ks) fs Fa * 
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

lemma bb_setup_rule:
  assumes k: "\<And> H1 H2 Xi C1 C2.
    <F * caps_assn (length ks) (\<lambda> v. ks ! v) Ka * part_pst (length fs) fs H1 *
       part_pst (length fs) ts H2 * xset_assn (length fs) {} Xi *
       cnt_assn (length ks) fs {} C1 * cnt_assn (length ks) ts {} C2 *
       blocks_assn (length fs) (length ks) fs Fa * blocks_assn (length fs) (length ks) ts Ta * true>
      k (length fs) H1 H2 Xi C1 C2 <Q>"
  shows "<F * Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Ka \<mapsto>\<^sub>a ks> bb_setup_imp Fa Ta Ka k <Q>"
proof-
  have len: "<F * Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Ka \<mapsto>\<^sub>a ks> Array.len Ka
             <\<lambda> r. F * caps_assn (length ks) (\<lambda> v. ks ! v) Ka * Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * \<up>(r = length ks)>"
    by (sep_auto simp: caps_assn_def map_nth)
  show ?thesis
    unfolding bb_setup_imp_def
    by (rule ht_bind[OF len], rule ht_pure_pre, simp only:, rule bm_setup_rule[where F = "F * caps_assn (length ks) (\<lambda> v. ks ! v) Ka"
          and Fa = Fa and Ta = Ta and k = k, OF k])
qed

theorem b_matching_imp_correct:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Ka \<mapsto>\<^sub>a ks> b_matching_imp Fa Ta Ka
   <\<lambda> Xi. \<exists>\<^sub>A X. xset_assn (length fs) X Xi * Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Ka \<mapsto>\<^sub>a ks * true *
              \<up>(max_card_b_matching ((\<lambda> i. {fs ! i, ts ! i}) ` {0..<length fs}) (\<lambda> v. ks ! v)
                                     ((\<lambda> i. {fs ! i, ts ! i}) ` X))>"
  unfolding b_matching_imp_def
  apply (rule ht_cons_pre[OF _ bb_setup_rule[where F = emp]], simp)
  apply (rule ht_bind[OF ht_frame_ac[OF handles_correct, where R = true]])
    prefer 3 apply (rule ht_return_wp)
   apply (simp only: star_aci, rule ent_refl)
  apply (sep_auto simp: blocks_assn_def caps_assn_def map_nth)
  done

end

end
