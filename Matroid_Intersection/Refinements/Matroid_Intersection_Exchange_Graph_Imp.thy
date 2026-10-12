theory Matroid_Intersection_Exchange_Graph_Imp
  imports Matroid_Intersection_Exchange_Graph_CSR Matroid_Intersection_Imp_Loop Exchange_Oracles_Imp
begin

section \<open>The Exchange Graph Search in Imperative HOL\<close>

text \<open>The imperative counterpart of the path search of
  @{theory Matroid_Intersection.Matroid_Intersection_Exchange_Graph_CSR}. It allocates nothing:
  it receives the solution handle, the path array, the CSR of a constant candidate graph \<open>es0\<close>
  (containing every exchange edge of every solution, with ascending neighbour lists) and the
  work arrays of the BFS. The BFS core of the library runs with an iterator that walks the CSR
  neighbours of a vertex and skips every edge that is not an exchange edge of the current
  solution, asking the membership test and the oracles on the fly. So the BFS sees exactly the
  exchange graph of the functional version. The visited array is exact on all elements, so the
  targets are scanned directly. The result is that of the functional path search with the set
  model of solutions.\<close>

subsection \<open>The BFS on a Filtered CSR\<close>

text \<open>The BFS core of the library on the graph of an edge list \<open>E\<close> below \<open>n\<close>, run with an
  iterator \<open>nbs\<close> on a graph handle that walks the neighbours of a vertex in \<open>E\<close> (e.g. the CSR
  neighbours of a constant larger graph, skipping the edges outside \<open>E\<close>). The visited set is exact
  on all elements below \<open>n\<close> and its handle is fixed. The graph assertion holds the data of the
  iterator and fixes the graph seen by the BFS to that of \<open>E\<close>.\<close>

lemma mem_nbrs: "v \<in> set (nbrs es u) \<longleftrightarrow> (u, v) \<in> set es"
  unfolding nbrs_def by force

lemma nbrs_append: "nbrs (xs @ ys) u = nbrs xs u @ nbrs ys u"
  unfolding nbrs_def by simp

lemma case_build_nhlists: "(case build_nhlists es v of None \<Rightarrow> [] | Some vs \<Rightarrow> vs) = nbrs es v"
  unfolding build_nhlists_def by simp

lemma foldl_filter_if:
  "foldl (\<lambda> a x. if p x then f a x else a) a xs = foldl f a (filter p xs)"
  by (induction xs arbitrary: a) simp_all

lemma foldl_True: "foldl (\<lambda> a x. True) b xs = (b \<or> xs \<noteq> [])"
  by (induction xs arbitrary: b) simp_all


lemma len_intro: "length l = m \<Longrightarrow> a \<mapsto>\<^sub>a l \<Longrightarrow>\<^sub>A len_assn m a"
  unfolding len_assn_def by (rule ent_ex_postI[where x = l]) simp

lemma len_fill_rule: "<len_assn n a> fill_range_imp f n a <\<lambda> r. a \<mapsto>\<^sub>a map f [0..<n] * \<up>(r = a)>"
  unfolding len_assn_def by (rule ht_ex_pre) (sep_auto heap: fill_range_imp_rule)

lemma clear_len: "<len_assn n Vi> bool_array_set_clear_imp n Vi <\<lambda> _. bool_array_set_assn n {} Vi>"
  by (rule ht_cons_post[OF bool_array_set_clear_rule]) sep_auto

lemma fill_len: "<len_assn n a> fill_range_imp f n a <\<lambda> _. a \<mapsto>\<^sub>a map f [0..<n]>"
  by (rule ht_cons_post[OF len_fill_rule]) sep_auto

lemma pure_mid: 
  assumes "b \<Longrightarrow> <P * Fm> c <Q>" 
  shows "<P * \<up>b * Fm> c <Q>"
  by (rule ht_cons_pre[OF _ ht_pure_pre[OF assms]]) (simp only: star_aci, rule ent_refl)

lemma ex_mid: 
  assumes "\<And> x. <P x * Fm> c <Q>" 
  shows "<(\<exists>\<^sub>A x. P x) * Fm> c <Q>"
proof-
  have "<\<exists>\<^sub>A x. P x * Fm> c <Q>"
    by (rule ht_ex_pre) (rule assms)
  then show ?thesis
    by (rule ht_cons_pre[rotated]) sep_auto
qed

lemma pull_len:
  assumes "\<And> l. length l = m \<Longrightarrow> <a \<mapsto>\<^sub>a l * Fm> c <Q>"
  shows "<len_assn m a * Fm> c <Q>"
proof-
  have "<\<exists>\<^sub>A l. a \<mapsto>\<^sub>a l * Fm * \<up>(length l = m)> c <Q>"
    by (rule ht_ex_pre, rule ht_pure_pre) (rule assms)
  then show ?thesis
    by (rule ht_cons_pre[rotated]) (unfold len_assn_def, sep_auto)
qed

lemma parr_len: "parr_assn n Ra = len_assn n Ra"
  unfolding parr_assn_def len_assn_def by (rule refl)

lemma path_None: "path_assn n None None Ra = parr_assn n Ra"
  unfolding path_assn_def parr_assn_def by simp

text \<open>The work arrays of the BFS, with arbitrary contents.\<close>

definition "work_assn n Vi Fr Bf Da Pa = 
  len_assn n Vi * len_assn (Suc n) Fr * len_assn (Suc n) Bf * len_assn n Da * len_assn n Pa"

locale csr_filtered_bfs =
  fixes n :: nat
    and E :: "(nat \<times> nat) list"
    and nbs :: "'gh \<Rightarrow> nat \<Rightarrow>
          (nat \<Rightarrow> nat \<Rightarrow> nat array \<times> nat \<times> bool array \<Rightarrow> (nat array \<times> nat \<times> bool array) Heap) \<Rightarrow>
          nat array \<times> nat \<times> bool array \<Rightarrow> (nat array \<times> nat \<times> bool array) Heap"
    and ga :: "'gh \<Rightarrow> assn"
  assumes E_bound: "(u, v) \<in> set E \<Longrightarrow> u < n \<and> v < n"
    and nbs_rule: "(\<And> acc acci x. x \<in> set (nbrs E u) \<Longrightarrow>
               <A acc acci * F> fi u x acci <\<lambda> r. A (f u acc x) r * F>) \<Longrightarrow>
         <ga Gh * (A :: nat list \<times> nat list \<times> (nat \<Rightarrow> nat) \<Rightarrow> nat array \<times> nat \<times> bool array \<Rightarrow> assn)
            acc acci * F> nbs Gh u fi acci
         <\<lambda> r. ga Gh * F * A (foldl (f u) acc (nbrs E u)) r>"
begin

text \<open>The BFS core of the library with this iterator.\<close>

abbreviation "nbs_bfs Gh \<equiv> BFS_Imperative_spec.visited_dists_parents_imp bfs_src_to_cf
  bfs_set_srcs_visited (BFS_subprocedures_lists_code.next_frontier_current_parents_imp bset_memb
  bset_ins nbs Gh) bfs_cf_is_empty bfs_set_dists"

definition "xvis Vh U Ss a = bool_array_set_assn n Ss a * \<up>(Ss \<subseteq> U \<and> U \<subseteq> {..<n} \<and> a = Vh)"

definition "gx G Gh = ga Gh * \<up>(G = build_nhlists E)"

lemma xvis_only: "xvis Vh U Ss a = xvis Vh U Ss a * \<up>(Ss \<subseteq> U)"
  unfolding xvis_def by (rule ent_iffI) sep_auto+

lemma xvis_memb: 
  "<xvis Vh U Ss a * \<up>(v \<in> U)> bset_memb v a <\<lambda> r. xvis Vh U Ss a * \<up>(r \<longleftrightarrow> v \<in> Ss)>"
  unfolding xvis_def bool_array_set_assn_def bset_memb_def by (sep_auto simp: subset_iff)

lemma xvis_ins: 
  "<xvis Vh U Ss a * \<up>(v \<in> U \<and> v \<notin> Ss)> bset_ins v a <xvis Vh U (Set.insert v Ss)>"
  unfolding xvis_def bset_ins_def by (sep_auto heap: bool_array_set_upd_rule simp: subset_iff)

lemma gx_iterate:
  fixes acc_assn :: "nat list \<times> nat list \<times> (nat \<Rightarrow> nat) \<Rightarrow> nat array \<times> nat \<times> bool array \<Rightarrow> assn"
  assumes fi: "\<And> acc acci x vs. \<lbrakk>nhlists v = Some vs; x \<in> set vs\<rbrakk> \<Longrightarrow>
               <acc_assn acc acci * F> fi v x acci <\<lambda> r. acc_assn (f v acc x) r * F>"
  shows "<gx nhlists Gi * acc_assn acc acci * F> nbs Gi v fi acci
         <\<lambda> r. gx nhlists Gi * F * 
               acc_assn (foldl (f v) acc (case nhlists v of None \<Rightarrow> [] | Some vs \<Rightarrow> vs)) r>"
proof(cases "nhlists = build_nhlists E")
  case False
  show ?thesis 
    unfolding gx_def using False by sep_auto
next
  case True
  have fi': "<acc_assn acc acci * F> fi v x acci <\<lambda> r. acc_assn (f v acc x) r * F>"
    if "x \<in> set (nbrs E v)" for acc acci x
    using that by (intro fi[of "nbrs E v"]) (auto simp: True build_nhlists_def)
  show ?thesis
    unfolding gx_def
    by (rule ht_cons[OF _ _ nbs_rule[where u = v and A = acc_assn and F = F and fi = fi and f = f,
                                      OF fi']])
       (sep_auto simp: True case_build_nhlists)+
qed

lemma BFS_sub: "BFS_subprocedures_lists (xvis Vh) bset_memb bset_ins nbs gx"
  by unfold_locales (rule xvis_only xvis_memb xvis_ins gx_iterate | assumption)+

lemma Vs_E: "BFS_subprocedures_lists.Vs (build_nhlists E) \<subseteq> {..<n}"
  unfolding Vs_build_nhlists using E_bound by (force simp: dVs_def)

lemma card_Vs: "card (BFS_subprocedures_lists.Vs (build_nhlists E)) \<le> n"
  using card_mono[OF finite_lessThan Vs_E] by simp

context
  fixes ss
  assumes b: "bfs_csr n E ss"
begin

interpretation b: bfs_csr n E ss
  by (rule b)

interpretation inst: BFS_lists_instance where is_visited_set = "xvis Vh"
  and visited_memb = bset_memb and distinct_ins = bset_ins and iterate_neighbourhood = nbs
  and graph_assn = gx and G = "build_nhlists E" and Gi = Gh and srcs = "rev ss"
  and N = n and Fr = Fr and Bf = Bf and Da = Da and Pa = Pa for Vh Gh Fr Bf Da Pa
  using BFS_sub Vs_E
  by (auto intro!: BFS_lists_instance.intro BFS_lists_instance_axioms.intro)

lemma code_eqs:
  "inst.imp_bfs.visited_dists_parents_imp Gh = nbs_bfs Gh" "inst.imp_bfs.path_imp = bfs_path"
  by (simp_all add: bfs_path_def bfs_src_to_cf_def bfs_set_srcs_visited_def bfs_cf_is_empty_def
                    bfs_set_dists_def)

definition "fin = inst.imp_bfs.BFS_par_impl inst.imp_bfs.initial_par_state"

lemma BFS_axiom: "inst.imp_bfs.BFS_axiom"
  by (rule b.BFS_axiom)

lemma cf_len: "inst.imp_cf_assn (Suc n) Fr Bf G cf cfi \<Longrightarrow>\<^sub>A len_assn (Suc n) Fr * len_assn (Suc n) Bf"
proof-
  obtain a b c where cfi: "cfi = (a, b, c)"
    by (cases cfi rule: prod_cases3)
  have e: "a \<mapsto>\<^sub>a l1 * c \<mapsto>\<^sub>a l2 \<Longrightarrow>\<^sub>A len_assn (Suc n) Fr * len_assn (Suc n) Bf"
    if l: "length l1 = Suc n" "length l2 = Suc n" and ac: "a = Fr \<and> c = Bf \<or> a = Bf \<and> c = Fr"
    for l1 l2
  proof(cases "a = Fr \<and> c = Bf")
    case True
    show ?thesis
      using ent_star_mono[OF len_intro[OF l(1), of a] len_intro[OF l(2), of c]] True by simp
  next
    case False
    then have "a = Bf" "c = Fr"
      using ac by blast+
    then show ?thesis
      using ent_star_mono[OF len_intro[OF l(2), of c] len_intro[OF l(1), of a]]
      by (simp add: mult.commute)
  qed
  show ?thesis
    unfolding cfi inst.imp_cf_assn.simps doubleton_eq_iff
    by (intro ent_ex_preI, unfold ent_pure_pre_iff, intro impI, elim conjE, rule e) assumption+
qed

lemma bfs_rule:
  assumes "length fl = Suc n" "take (length ss) fl = ss" "length bl = Suc n"
  shows "<bool_array_set_assn n {} Vi * Fr \<mapsto>\<^sub>a fl * Bf \<mapsto>\<^sub>a bl * Da \<mapsto>\<^sub>a map id [0..<n] *
          Pa \<mapsto>\<^sub>a map id [0..<n] * ga Gh>
           nbs_bfs Gh Vi (Fr, length ss, Bf) Da Pa
         <\<lambda> _. ga Gh * bool_array_set_assn n (set (BFS_dist_state.visited fin)) Vi *
            inst.imp_dist_assn n Da (build_nhlists E) (BFS_dist_state.dists fin) Da *
            inst.imp_par_assn n Pa (build_nhlists E) (BFS_par_state.parent fin) Pa *
            len_assn (Suc n) Fr * len_assn (Suc n) Bf>"
proof-
  let ?G = "build_nhlists E"
  have sV: "set ss \<subseteq> BFS_subprocedures_lists.Vs ?G"
    using b.ss_in_graph unfolding Vs_build_nhlists .
  have ls: "length ss \<le> n"
    using card_mono[OF finite_subset[OF Vs_E finite_lessThan] sV] distinct_card[OF b.ss_distinct]
          card_Vs by simp
  have ids: "\<forall>i \<in> BFS_subprocedures_lists.Vs ?G. i < length (map id [0..<n]) \<and> id i = map id [0..<n] ! i"
    using Vs_E by auto
  have pre: "bool_array_set_assn n {} Vi * Fr \<mapsto>\<^sub>a fl * Bf \<mapsto>\<^sub>a bl * Da \<mapsto>\<^sub>a map id [0..<n] *
             Pa \<mapsto>\<^sub>a map id [0..<n] * ga Gh
             \<Longrightarrow>\<^sub>A xvis Vi (BFS_subprocedures_lists.Vs ?G) (set []) Vi *
             inst.imp_src_assn (Suc n) Fr Bf ?G (rev ss) (Fr, length ss, Bf) *
             inst.imp_dist_assn n Da ?G id Da * inst.imp_par_assn n Pa ?G id Pa * gx ?G Gh"
    if "length bl = Suc n" for bl
  proof-
    have v: "bool_array_set_assn n {} Vi \<Longrightarrow>\<^sub>A xvis Vi (BFS_subprocedures_lists.Vs ?G) (set []) Vi"
      unfolding xvis_def using Vs_E by sep_auto
    have g: "ga Gh \<Longrightarrow>\<^sub>A gx ?G Gh"
      unfolding gx_def by sep_auto
    have s: "Fr \<mapsto>\<^sub>a fl * Bf \<mapsto>\<^sub>a bl \<Longrightarrow>\<^sub>A inst.imp_src_assn (Suc n) Fr Bf ?G (rev ss) (Fr, length ss, Bf)"
      by (rule inst.imp_src_assn_intro) (use assms that card_Vs ls sV in simp_all)
    show ?thesis
      by (rule ent_trans[OF _ ent_star_mono[OF ent_star_mono[OF ent_star_mono[OF ent_star_mono[OF v s]
             inst.imp_dist_assn_intro[OF ids] ] inst.imp_par_assn_intro[OF ids]] g]])
         (simp_all add: star_aci)
  qed
  have post: "gx ?G Gh * xvis Vi (BFS_subprocedures_lists.Vs ?G) (set V) visi *
              inst.imp_dist_assn n Da ?G d di * inst.imp_par_assn n Pa ?G p pari *
              (\<exists>\<^sub>A cf cfi. inst.imp_cf_assn (Suc n) Fr Bf ?G cf cfi)
              \<Longrightarrow>\<^sub>A ga Gh * bool_array_set_assn n (set V) Vi * inst.imp_dist_assn n Da ?G d Da *
              inst.imp_par_assn n Pa ?G p Pa * len_assn (Suc n) Fr * len_assn (Suc n) Bf"
    for V visi d di p pari
  proof-
    have c: "(\<exists>\<^sub>A cf cfi. inst.imp_cf_assn (Suc n) Fr Bf ?G cf cfi)
             \<Longrightarrow>\<^sub>A len_assn (Suc n) Fr * len_assn (Suc n) Bf"
      by (intro ent_ex_preI) (rule cf_len)
    show ?thesis
      unfolding gx_def xvis_def inst.imp_dist_assn_char inst.imp_par_assn_char
      by (rule ent_trans[OF ent_star_mono[OF ent_refl c]]) sep_auto
  qed
  show ?thesis
    by (rule ht_cons[OF pre[OF assms(3)] _
           inst.imp_bfs.visited_dists_parents_imp_frontier_rule[unfolded code_eqs, folded fin_def]])
       (unfold split_paired_all prod.case, rule ent_trans[OF post], sep_auto)
qed

lemma path_rule:
  assumes "find (\<lambda> y. y \<in> set (BFS_dist_state.visited fin)) ts = Some t" "length rl = n"
  shows "<inst.imp_dist_assn n Da (build_nhlists E) (BFS_dist_state.dists fin) di *
          inst.imp_par_assn n Pa (build_nhlists E) (BFS_par_state.parent fin) pari * Ra \<mapsto>\<^sub>a rl>
           bfs_path di pari Ra t
         <\<lambda> k. inst.imp_dist_assn n Da (build_nhlists E) (BFS_dist_state.dists fin) di *
               inst.imp_par_assn n Pa (build_nhlists E) (BFS_par_state.parent fin) pari *
               path_assn n (Some (inst.imp_bfs.parent_path (BFS_dist_state.dists fin)
                                   (BFS_par_state.parent fin) t [])) (Some k) Ra>"
proof-
  let ?pp = "inst.imp_bfs.parent_path (BFS_dist_state.dists fin) (BFS_par_state.parent fin) t []"
  have t: "t \<in> set (BFS_dist_state.visited fin)"
    by (rule conjunct1[OF find_SomeD[OF assms(1)]])
  have len: "length ?pp \<le> n"
  proof-
    have "length ?pp \<le> card (dVs (set E))"
      using inst.imp_bfs.parent_path_length[OF BFS_axiom fin_def t]
      unfolding b.digraph_abs_build b.\<E>_def .
    then show ?thesis
      using card_Vs[unfolded Vs_build_nhlists] by (rule le_trans)
  qed
  have p: "bfs_path di pari Ra t = inst.imp_bfs.path_rev_imp di pari Ra t 0"
    unfolding code_eqs(2)[symmetric] inst.imp_bfs.path_imp_def by (rule refl)
  have r: "<inst.imp_dist_assn n Da (build_nhlists E) (BFS_dist_state.dists fin) di *
            inst.imp_par_assn n Pa (build_nhlists E) (BFS_par_state.parent fin) pari * Ra \<mapsto>\<^sub>a r>
             bfs_path di pari Ra t
           <\<lambda> k. inst.imp_dist_assn n Da (build_nhlists E) (BFS_dist_state.dists fin) di *
                 inst.imp_par_assn n Pa (build_nhlists E) (BFS_par_state.parent fin) pari *
                 path_assn n (Some ?pp) (Some k) Ra>" if "length r = n" for r
    unfolding p path_assn_def option.case(2)
    by (rule ht_cons_post[OF inst.imp_bfs.path_rev_imp_rule[OF BFS_axiom fin_def t]])
       (use len that in \<open>sep_auto\<close>)+
  show ?thesis
    by (rule r[OF assms(2)])
qed

lemma dist_len: "inst.imp_dist_assn n Da (build_nhlists E) d di \<Longrightarrow>\<^sub>A len_assn n Da"
  unfolding inst.imp_dist_assn_char len_assn_def by sep_auto

lemma par_len: "inst.imp_par_assn n Pa (build_nhlists E) p pari \<Longrightarrow>\<^sub>A len_assn n Pa"
  unfolding inst.imp_par_assn_char len_assn_def by sep_auto

lemma work_ent:
  "bool_array_set_assn n V Vi * inst.imp_dist_assn n Da (build_nhlists E) d di *
   inst.imp_par_assn n Pa (build_nhlists E) p pari * len_assn (Suc n) Fr * len_assn (Suc n) Bf
   \<Longrightarrow>\<^sub>A work_assn n Vi Fr Bf Da Pa"
proof-
  note d = dist_len and p = par_len
  show ?thesis
    unfolding work_assn_def
    by (rule ent_trans[OF ent_star_mono[OF ent_star_mono[OF ent_star_mono[OF ent_star_mono[OF bool_array_set_len d] p]
                                    ent_refl] ent_refl]])
       (simp only: star_aci, rule ent_refl)
qed

lemma bfs_len_rule:
  assumes "length fl = Suc n" "take (length ss) fl = ss"
  shows "<len_assn (Suc n) Bf * (bool_array_set_assn n {} Vi * Fr \<mapsto>\<^sub>a fl * Da \<mapsto>\<^sub>a map id [0..<n] *
          Pa \<mapsto>\<^sub>a map id [0..<n] * ga Gh)>
           nbs_bfs Gh Vi (Fr, length ss, Bf) Da Pa
         <\<lambda> _. ga Gh * bool_array_set_assn n (set (BFS_dist_state.visited fin)) Vi *
            inst.imp_dist_assn n Da (build_nhlists E) (BFS_dist_state.dists fin) Da *
            inst.imp_par_assn n Pa (build_nhlists E) (BFS_par_state.parent fin) Pa *
            len_assn (Suc n) Fr * len_assn (Suc n) Bf>"
proof(rule pull_len)
  fix bl :: "nat list"
  assume bl: "length bl = Suc n"
  show "<Bf \<mapsto>\<^sub>a bl * (bool_array_set_assn n {} Vi * Fr \<mapsto>\<^sub>a fl * Da \<mapsto>\<^sub>a map id [0..<n] *
          Pa \<mapsto>\<^sub>a map id [0..<n] * ga Gh)>
           nbs_bfs Gh Vi (Fr, length ss, Bf) Da Pa
         <\<lambda> _. ga Gh * bool_array_set_assn n (set (BFS_dist_state.visited fin)) Vi *
            inst.imp_dist_assn n Da (build_nhlists E) (BFS_dist_state.dists fin) Da *
            inst.imp_par_assn n Pa (build_nhlists E) (BFS_par_state.parent fin) Pa *
            len_assn (Suc n) Fr * len_assn (Suc n) Bf>"
    by (rule ht_cons_pre[OF _ bfs_rule[OF assms bl]]) (simp only: star_aci, rule ent_refl)
qed

lemma path_len_rule:
  assumes "find (\<lambda> y. y \<in> set (BFS_dist_state.visited fin)) ts = Some t"
  shows "<parr_assn n Ra * (inst.imp_dist_assn n Da (build_nhlists E) (BFS_dist_state.dists fin) di *
          inst.imp_par_assn n Pa (build_nhlists E) (BFS_par_state.parent fin) pari)>
           bfs_path di pari Ra t
         <\<lambda> k. inst.imp_dist_assn n Da (build_nhlists E) (BFS_dist_state.dists fin) di *
               inst.imp_par_assn n Pa (build_nhlists E) (BFS_par_state.parent fin) pari *
               path_assn n (Some (inst.imp_bfs.parent_path (BFS_dist_state.dists fin)
                                   (BFS_par_state.parent fin) t [])) (Some k) Ra>"
  unfolding parr_len
proof(rule pull_len)
  fix rl :: "nat list"
  assume rl: "length rl = n"
  show "<Ra \<mapsto>\<^sub>a rl * (inst.imp_dist_assn n Da (build_nhlists E) (BFS_dist_state.dists fin) di *
          inst.imp_par_assn n Pa (build_nhlists E) (BFS_par_state.parent fin) pari)>
           bfs_path di pari Ra t
         <\<lambda> k. inst.imp_dist_assn n Da (build_nhlists E) (BFS_dist_state.dists fin) di *
               inst.imp_par_assn n Pa (build_nhlists E) (BFS_par_state.parent fin) pari *
               path_assn n (Some (inst.imp_bfs.parent_path (BFS_dist_state.dists fin)
                                   (BFS_par_state.parent fin) t [])) (Some k) Ra>"
    by (rule ht_cons_pre[OF _ path_rule[OF assms rl]]) (simp only: star_aci, rule ent_refl)
qed

end

end

subsection \<open>Code\<close>

locale unweighted_intersection_exchange_imp_spec =
  fixes n :: nat
    and smemb_imp :: "nat \<Rightarrow> 'si \<Rightarrow> bool Heap"
    and ins1_imp :: "'si \<Rightarrow> nat \<Rightarrow> bool Heap"
    and exch1_imp :: "'si \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool Heap"
    and ins2_imp :: "'si \<Rightarrow> nat \<Rightarrow> bool Heap"
    and exch2_imp :: "'si \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool Heap"
begin

text \<open>Exchange edges from an element \<open>u\<close> of the solution (first matroid) and from an element
  \<open>u\<close> outside the solution that is not a target (second matroid).\<close>

definition "nb1_imp Si u v = do {
   b \<leftarrow> smemb_imp v Si;
   if b then return False
   else do { s \<leftarrow> ins1_imp Si v; if s then return False else exch1_imp Si u v } }"

definition "nb2_imp Si u v = do { b \<leftarrow> smemb_imp v Si; if b then exch2_imp Si v u else return False }"

definition "filt_imp P Si fi = (\<lambda> u v a. do { ok \<leftarrow> P Si u v; if ok then fi u v a else return a })"

text \<open>The iterator over the exchange neighbours, on the solution handle and the CSR.\<close>

definition xnbs :: "'si \<times> (nat array \<times> nat array) \<Rightarrow> nat \<Rightarrow>
                     (nat \<Rightarrow> nat \<Rightarrow> 'acc \<Rightarrow> 'acc Heap) \<Rightarrow> 'acc \<Rightarrow> 'acc Heap" where
  "xnbs Gh u fi acc = (case Gh of (Si, Gc) \<Rightarrow>
     if u < n then do {
       b \<leftarrow> smemb_imp u Si;
       if b then bfs_csr_nbs Gc u (filt_imp nb1_imp Si fi) acc
       else do { t \<leftarrow> ins2_imp Si u;
                 if t then return acc else bfs_csr_nbs Gc u (filt_imp nb2_imp Si fi) acc } }
     else return acc)"

text \<open>The BFS core of the library with this iterator.\<close>

definition "xround = BFS_subprocedures_lists_code.next_frontier_current_parents_imp bset_memb bset_ins xnbs"

definition "bfs_run Gh = BFS_Imperative_spec.visited_dists_parents_imp bfs_src_to_cf bfs_set_srcs_visited
                           (xround Gh) bfs_cf_is_empty bfs_set_dists"

definition "has_nb_imp Gc Si y = xnbs (Si, Gc) y (\<lambda> _ _ _. return True) False"

text \<open>Sources and targets (elements outside the solution insertable in the first resp. second
  matroid), sources that are targets, sources having an exchange edge, and visited targets.\<close>

definition "s_imp Si y = do { b \<leftarrow> smemb_imp y Si; if b then return False else ins1_imp Si y }"

definition "t_imp Si y = do { b \<leftarrow> smemb_imp y Si; if b then return False else ins2_imp Si y }"

definition "st_imp Si y = do { s \<leftarrow> s_imp Si y; if s then ins2_imp Si y else return False }"

definition "is_src_imp Gc Si y = do { s \<leftarrow> s_imp Si y; if s then has_nb_imp Gc Si y else return False }"

definition "is_tgt_imp Si Vi y = do { v \<leftarrow> Array.nth Vi y; if v then t_imp Si y else return False }"

text \<open>One search: a source that is a target is a path on its own. Otherwise, the sources having
  an exchange edge are written into the frontier array, the visited, distance and parent arrays
  are reset in place, the BFS runs, and the first visited target gives the path.\<close>

definition "tail_imp Si Ra r = (case r of (Vi', Da', Pa') \<Rightarrow> do {
   t \<leftarrow> find_range_imp (is_tgt_imp Si Vi') 0 n;
   (case t of
      None \<Rightarrow> return None
    | Some t \<Rightarrow> do { l \<leftarrow> bfs_path Da' Pa' Ra t; return (Some l) }) })"

definition "round_imp Gc Vi Fr Bf Da Pa Si Ra k = do {
   bool_array_set_clear_imp n Vi;
   fill_range_imp id n Da;
   fill_range_imp id n Pa;
   bfs_run (Si, Gc) Vi (Fr, k, Bf) Da Pa;
   tail_imp Si Ra (Vi, Da, Pa) }"

definition "aug_path_imp Gc Vi Fr Bf Da Pa Si Ra = do {
   r \<leftarrow> find_range_imp (st_imp Si) 0 n;
   (case r of
      Some s \<Rightarrow> do { Array.upd 0 s Ra; return (Some 1) }
    | None \<Rightarrow> do {
        k \<leftarrow> collect_range_imp (is_src_imp Gc Si) n Fr;
        if k = 0 then return None else round_imp Gc Vi Fr Bf Da Pa Si Ra k }) }"

end

subsection \<open>Correctness\<close>

locale unweighted_intersection_exchange_imp =
  unweighted_intersection_exchange_imp_spec n smemb_imp ins1_imp exch1_imp ins2_imp exch2_imp +
  imp_nat_set n sol_assn smemb_imp sins_imp sdel_imp +
  unweighted_intersection_exchange_csr where set_insert = "Set.insert :: nat \<Rightarrow> nat set \<Rightarrow> nat set"
    and set_delete = "\<lambda> x X. X - {x}" and to_set = "\<lambda> X. X" and set_invar = finite
    and set_empty = "{}" and set_memb = "\<lambda> x X. x \<in> X" and carrier_list = "[0..<n]"
    and carrier = "{0..<n}" +
  o1: exchange_oracle_imp n orcl_prep1 ins_orcl1 exch_orcl1 sol_assn ins1_imp exch1_imp ost1 +
  o2: exchange_oracle_imp n orcl_prep2 ins_orcl2 exch_orcl2 sol_assn ins2_imp exch2_imp ost2
  for n smemb_imp ins1_imp exch1_imp ins2_imp exch2_imp sol_assn sins_imp sdel_imp ost1 ost2 +
  fixes es0 :: "(nat \<times> nat) list"
  assumes es0_bound: "(u, v) \<in> set es0 \<Longrightarrow> u < n \<and> v < n"
    and es0_sorted: "sorted_wrt (<) (nbrs es0 u)"
    and es0_cover1: "\<lbrakk>finite X; X \<subseteq> {0..<n}; indep1 X; indep2 X; u < n; v < n; u \<in> X; v \<notin> X;
                     \<not> ins_orcl1 (orcl_prep1 X) v; exch_orcl1 (orcl_prep1 X) u v\<rbrakk> \<Longrightarrow> (u, v) \<in> set es0"
    and es0_cover2: "\<lbrakk>finite X; X \<subseteq> {0..<n}; indep1 X; indep2 X; u < n; v < n; u \<notin> X; v \<in> X;
                     \<not> ins_orcl2 (orcl_prep2 X) u; exch_orcl2 (orcl_prep2 X) v u\<rbrakk> \<Longrightarrow> (u, v) \<in> set es0"
begin

subsubsection \<open>The Exchange Neighbours\<close>

definition "S0 X = {y. y < n \<and> y \<notin> X \<and> ins_orcl1 (orcl_prep1 X) y}"
definition "T0 X = {y. y < n \<and> y \<notin> X \<and> ins_orcl2 (orcl_prep2 X) y}"

definition "allowed1 X u v = (v \<notin> X \<and> \<not> ins_orcl1 (orcl_prep1 X) v \<and> exch_orcl1 (orcl_prep1 X) u v)"
definition "allowed2 X u v = (v \<in> X \<and> exch_orcl2 (orcl_prep2 X) v u)"
definition "exch_nb X u v = 
  (if u \<in> X then allowed1 X u v else \<not> ins_orcl2 (orcl_prep2 X) u \<and> allowed2 X u v)"

abbreviation "EE X \<equiv> csr.exch_edges (csr.exch_ctx X)"


lemma nbrs_concat:
  "nbrs (concat (map (\<lambda> x. map (Pair x) (L x)) xs)) u = concat (map (\<lambda> x. if x = u then L x else []) xs)"
  by (induction xs) (simp_all add: nbrs_def filter_map comp_def)

lemma concat_if_distinct:
  "distinct xs \<Longrightarrow> concat (map (\<lambda> x. if x = u then L x else []) xs) = (if u \<in> set xs then L u else [])"
  by (induction xs) auto


lemma ctx_parts:
  "ctx_o1 (csr.exch_ctx X) = orcl_prep1 X" "ctx_o2 (csr.exch_ctx X) = orcl_prep2 X"
  "ctx_notX (csr.exch_ctx X) = filter (\<lambda> y. y \<notin> X) [0..<n]"
  "ctx_inX (csr.exch_ctx X) = filter (\<lambda> y. y \<in> X) [0..<n]"
  by (simp_all add: csr.exch_ctx_def Let_def)

lemma ctx_ST: "ctx_S (csr.exch_ctx X) = S0 X" "ctx_T (csr.exch_ctx X) = T0 X"
proof-
  have sub: "set (filter (\<lambda> y. y \<notin> X) [0..<n]) \<subseteq> {0..<n}"
    by auto
  show "ctx_S (csr.exch_ctx X) = S0 X" "ctx_T (csr.exch_ctx X) = T0 X"
    by (auto simp: csr.exch_ctx_def Let_def csr.cache(2)[OF sub] S0_def T0_def)
qed

lemma in_ST:
  "csr.in_S (csr.exch_ctx X) = (\<lambda> y. y \<in> S0 X)" "csr.in_T (csr.exch_ctx X) = (\<lambda> y. y \<in> T0 X)"
  by (simp_all add: fun_eq_iff csr.in_S_def csr.in_T_def ctx_ST)

text \<open>The neighbours of an element in the exchange graph, in increasing order.\<close>

lemma nbrs_EE:
  assumes "u < n"
  shows "nbrs (EE X) u = filter (exch_nb X u) [0..<n]"
proof-
  have d: "distinct (filter (\<lambda> y. y \<in> X) [0..<n])" 
          "distinct (filter (\<lambda> y. y \<notin> T0 X) (filter (\<lambda> y. y \<notin> X) [0..<n]))"
    by simp_all
  have e: "nbrs (EE X) u = 
             (if u \<in> X then csr.out1 (csr.exch_ctx X) u else []) @
             (if u \<notin> X \<and> u \<notin> T0 X then csr.out2 (csr.exch_ctx X) u else [])"
    unfolding csr.exch_edges_def nbrs_append nbrs_concat ctx_parts in_ST concat_if_distinct[OF d(1)]
              concat_if_distinct[OF d(2)]
    using assms by simp
  show ?thesis
  proof(cases "u \<in> X")
    case True
    show ?thesis
      unfolding e csr.out1_def in_ST ctx_parts filter_filter exch_nb_def allowed1_def
      using True by (auto intro!: filter_cong simp: S0_def)
  next
    case False
    show ?thesis
    proof(cases "u \<in> T0 X")
      case True
      have "ins_orcl2 (orcl_prep2 X) u"
        using True by (simp add: T0_def)
      then show ?thesis
        unfolding e exch_nb_def using True False by simp
    next
      case nT: False
      have "\<not> ins_orcl2 (orcl_prep2 X) u"
        using nT False assms by (simp add: T0_def)
      then show ?thesis
        unfolding e csr.out2_def ctx_parts filter_filter exch_nb_def allowed2_def
        using nT False by (auto intro!: filter_cong)
    qed
  qed
qed

context
  fixes X
  assumes X: "finite X" "X \<subseteq> {0..<n}" "indep1 X" "indep2 X"
begin

lemma EE_set: "set (EE X) = A1 X \<union> A2 X"
  using csr.exchange_graph[OF X] unfolding csr.build_graph(4) .

lemma EE_bound: "(u, v) \<in> set (EE X) \<Longrightarrow> u < n \<and> v < n"
proof-
  assume "(u, v) \<in> set (EE X)"
  then have "u \<in> dVs (A1 X \<union> A2 X)" "v \<in> dVs (A1 X \<union> A2 X)"
    unfolding EE_set by (rule dVsI(1), rule dVsI(2))
  then show "u < n \<and> v < n"
    using dVs_A1A2_carrier[OF X(3,4)] by auto
qed

text \<open>Filtering the CSR neighbours gives the exchange neighbours, since both lists are
  ascending.\<close>

lemma nbrs_es0:
  assumes "u < n"
  shows "filter (exch_nb X u) (nbrs es0 u) = nbrs (EE X) u"
proof-
  have s1: "sorted_wrt (<) (filter (exch_nb X u) (nbrs es0 u))"
    by (rule sorted_wrt_filter[OF es0_sorted])
  have s2: "sorted_wrt (<) (filter (exch_nb X u) [0..<n])"
    by (rule sorted_wrt_filter) (simp add: sorted_wrt_upt)
  have st: "set (filter (exch_nb X u) (nbrs es0 u)) = set (filter (exch_nb X u) [0..<n])"
  proof(rule set_eqI, rule iffI)
    fix v
    assume "v \<in> set (filter (exch_nb X u) (nbrs es0 u))"
    then have "exch_nb X u v" "(u, v) \<in> set es0"
      by (simp_all add: mem_nbrs)
    then show "v \<in> set (filter (exch_nb X u) [0..<n])"
      using es0_bound by auto
  next
    fix v
    assume a: "v \<in> set (filter (exch_nb X u) [0..<n])"
    then have v: "v < n" "exch_nb X u v"
      by simp_all
    have "(u, v) \<in> set es0"
    proof(cases "u \<in> X")
      case True
      then show ?thesis
        using v(2) unfolding exch_nb_def allowed1_def
        by (intro es0_cover1[OF X assms v(1) True]) simp_all
    next
      case False
      then show ?thesis
        using v(2) unfolding exch_nb_def allowed2_def
        by (intro es0_cover2[OF X assms v(1) False]) simp_all
    qed
    then show "v \<in> set (filter (exch_nb X u) (nbrs es0 u))"
      using a by (simp add: mem_nbrs)
  qed
  show ?thesis
    unfolding nbrs_EE[OF assms] by (rule strict_sorted_equal[OF s2 s1 st])
qed

lemma nbrs_EE_out: "\<not> u < n \<Longrightarrow> nbrs (EE X) u = []"
  unfolding nbrs_def using EE_bound by (fastforce simp: filter_empty_conv)

end

subsubsection \<open>The Iterator\<close>

definition "gxs X Si Gc = sol_assn X Si * ost1 * ost2 * bcsr_assn (build_nhlists es0) Gc"


text \<open>(A triple must not start with \<open><sol_assn\<close> here, which is read as another token.)\<close>

lemma nb1_rule:
  "\<lbrakk>u < n; v < n\<rbrakk> \<Longrightarrow>
   <ost1 * ost2 * sol_assn X Si * Q> nb1_imp Si u v
   <\<lambda> r. ost1 * ost2 * sol_assn X Si * Q * \<up>(r = allowed1 X u v)>"
  unfolding nb1_imp_def allowed1_def by (sep_auto heap: smemb_rule o1.ins_imp o1.exch_imp)

lemma nb2_rule:
  "\<lbrakk>u < n; v < n\<rbrakk> \<Longrightarrow>
   <ost1 * ost2 * sol_assn X Si * Q> nb2_imp Si u v
   <\<lambda> r. ost1 * ost2 * sol_assn X Si * Q * \<up>(r = allowed2 X u v)>"
  unfolding nb2_imp_def allowed2_def by (sep_auto heap: smemb_rule o2.exch_imp)

lemma es0_nb: "build_nhlists es0 u = Some vs \<Longrightarrow> x \<in> set vs \<Longrightarrow> x < n \<and> x \<in> set (nbrs es0 u)"
  using es0_bound mem_nbrs[of x es0 u] unfolding build_nhlists_def
  by (auto split: if_splits)

lemma bfs_nbs_filt_rule:
  assumes P: "\<And> v Q. v < n \<Longrightarrow> <ost1 * ost2 * sol_assn X Si * Q> P Si u v
                                   <\<lambda> r. ost1 * ost2 * sol_assn X Si * Q * \<up>(r = p v)>"
    and fi: "\<And> acc acci x. x \<in> set (filter p (nbrs es0 u)) \<Longrightarrow>
               <A acc acci * F> fi u x acci <\<lambda> r. A (f u acc x) r * F>"
  shows "<gxs X Si Gc * A acc acci * F> bfs_csr_nbs Gc u (filt_imp P Si fi) acci
         <\<lambda> r. gxs X Si Gc * F * A (foldl (f u) acc (filter p (nbrs es0 u))) r>"
proof-
  let ?R = "ost1 * ost2 * sol_assn X Si"
  let ?g = "\<lambda> u a x. if p x then f u a x else a"
  have step: "<A a ai * (F * ?R)> filt_imp P Si fi u x ai <\<lambda> r. A (?g u a x) r * (F * ?R)>"
    if "build_nhlists es0 u = Some vs" "x \<in> set vs" for a ai x vs
  proof-
    note x = es0_nb[OF that]
    have p: "<A a ai * (F * ?R)> P Si u x <\<lambda> ok. A a ai * (F * ?R) * \<up>(ok = p x)>"
      by (rule ht_cons_pre[OF _ ht_cons_post[OF P[of x "A a ai * F", OF conjunct1[OF x]]]])
         sep_auto+
    show ?thesis
    proof(cases "p x")
      case True
      have x': "x \<in> set (filter p (nbrs es0 u))"
        using x True by simp
      have fi': "<A a ai * (F * ?R)> fi u x ai <\<lambda> r. A (f u a x) r * (F * ?R)>"
        using ht_frame[OF fi[OF x'], where R = ?R] by (simp add: mult.assoc)
      show ?thesis
        unfolding filt_imp_def by (rule ht_bind[OF p], rule ht_pure_pre) (simp add: True fi')
    next
      case False
      show ?thesis
        unfolding filt_imp_def by (rule ht_bind[OF p], rule ht_pure_pre) (sep_auto simp: False)
    qed
  qed
  have r: "<bcsr_assn (build_nhlists es0) Gc * A acc acci * (F * ?R)> bfs_csr_nbs Gc u (filt_imp P Si fi) acci
           <\<lambda> r. bcsr_assn (build_nhlists es0) Gc * (F * ?R) *
                 A (foldl (?g u) acc (case build_nhlists es0 u of None \<Rightarrow> [] | Some vs \<Rightarrow> vs)) r>"
    by (rule bfs_csr_nbs_rule[where G = "build_nhlists es0" and f = ?g]) (rule step)
  show ?thesis
    unfolding gxs_def
    by (rule ht_cons[OF _ _ r]) (sep_auto, simp only: case_build_nhlists foldl_filter_if, sep_auto)
qed

lemma xnbs_rule:
  assumes X: "finite X" "X \<subseteq> {0..<n}" "indep1 X" "indep2 X"
    and fi: "\<And> acc acci x. x \<in> set (nbrs (EE X) u) \<Longrightarrow>
               <A acc acci * F> fi u x acci <\<lambda> r. A (f u acc x) r * F>"
  shows "<gxs X Si Gc * A acc acci * F> xnbs (Si, Gc) u fi acci
         <\<lambda> r. gxs X Si Gc * F * A (foldl (f u) acc (nbrs (EE X) u)) r>"
proof(cases "u < n")
  case False
  show ?thesis
    unfolding xnbs_def prod.case if_not_P[OF False] nbrs_EE_out[OF X False] foldl_Nil
    by sep_auto
next
  case True
  have m: "<gxs X Si Gc * A acc acci * F> smemb_imp u Si 
           <\<lambda> b. gxs X Si Gc * A acc acci * F * \<up>(b = (u \<in> X))>"
    unfolding gxs_def using True by (sep_auto heap: smemb_rule)
  show ?thesis
  proof(cases "u \<in> X")
    case uX: True
    have e: "filter (allowed1 X u) (nbrs es0 u) = nbrs (EE X) u"
      using nbrs_es0[OF X True] uX unfolding exch_nb_def by simp
    have b: "<gxs X Si Gc * A acc acci * F> bfs_csr_nbs Gc u (filt_imp nb1_imp Si fi) acci
             <\<lambda> r. gxs X Si Gc * F * A (foldl (f u) acc (nbrs (EE X) u)) r>"
      unfolding e[symmetric] by (rule bfs_nbs_filt_rule) (rule nb1_rule[OF True], assumption, 
                                                         rule fi, unfold e)
    show ?thesis
      unfolding xnbs_def prod.case if_P[OF True]
      by (rule ht_bind[OF m], rule ht_pure_pre) (simp add: uX b)
  next
    case nX: False
    have i: "<gxs X Si Gc * A acc acci * F> ins2_imp Si u 
             <\<lambda> t. gxs X Si Gc * A acc acci * F * \<up>(t = ins_orcl2 (orcl_prep2 X) u)>"
      unfolding gxs_def using True by (sep_auto heap: o2.ins_imp)
    show ?thesis
    proof(cases "ins_orcl2 (orcl_prep2 X) u")
      case it: True
      have e: "nbrs (EE X) u = []"
        unfolding nbrs_es0[OF X True, symmetric] exch_nb_def using nX it by simp
      show ?thesis
        unfolding xnbs_def prod.case if_P[OF True] e foldl_Nil
        by (rule ht_bind[OF m], rule ht_pure_pre)
           (simp add: nX, rule ht_bind[OF i], rule ht_pure_pre, sep_auto simp: it)
    next
      case nit: False
      have e: "filter (allowed2 X u) (nbrs es0 u) = nbrs (EE X) u"
        using nbrs_es0[OF X True] nX nit unfolding exch_nb_def by simp
      have b: "<gxs X Si Gc * A acc acci * F> bfs_csr_nbs Gc u (filt_imp nb2_imp Si fi) acci
               <\<lambda> r. gxs X Si Gc * F * A (foldl (f u) acc (nbrs (EE X) u)) r>"
        unfolding e[symmetric] by (rule bfs_nbs_filt_rule) (rule nb2_rule[OF True], assumption,
                                                           rule fi, unfold e)
      show ?thesis
        unfolding xnbs_def prod.case if_P[OF True]
        by (rule ht_bind[OF m], rule ht_pure_pre)
           (simp add: nX, rule ht_bind[OF i], rule ht_pure_pre, simp add: nit b)
    qed
  qed
qed


subsubsection \<open>The BFS on the Exchange Graph\<close>

text \<open>The BFS of @{locale csr_filtered_bfs} on the exchange graph of a solution. The graph
  handle is the pair of the solution handle and the CSR; its assertion holds the solution, the
  static data of the oracles and the CSR.\<close>

context
  fixes X
  assumes X: "finite X" "X \<subseteq> {0..<n}" "indep1 X" "indep2 X"
begin

interpretation fb: csr_filtered_bfs n "EE X" xnbs "\<lambda> (Si, Gc). gxs X Si Gc"
proof(unfold_locales, goal_cases)
  case (1 u v)
  then show ?case
    by (rule EE_bound[OF X])
next
  case (2 u A F fi f Gh acc acci)
  then show ?case
    by (cases Gh) (simp only: prod.case, rule xnbs_rule[OF X], rule 2)
qed

subsubsection \<open>The Functional Values\<close>

lemma eq_find: 
  "find (\<lambda> y. (y \<notin> X \<and> y \<in> S0 X) \<and> y \<in> T0 X) [0..<n] = 
   find (csr.in_T (csr.exch_ctx X)) (csr.srcs (csr.exch_ctx X))"
  by (simp only: csr.srcs_def in_ST ctx_parts filter_filter find_filter)

lemma eq_srcs: 
  "filter (\<lambda> y. (y \<notin> X \<and> y \<in> S0 X) \<and> 
                 (y \<notin> T0 X \<and> find (\<lambda> x. x \<in> X \<and> exch_orcl2 (orcl_prep2 X) x y) [0..<n] \<noteq> None)) 
          [0..<n] = 
   filter (csr.has_nb (csr.exch_ctx X)) (csr.srcs (csr.exch_ctx X))"
  by (simp only: csr.has_nb_def csr.srcs_def in_ST ctx_parts filter_filter list_ex_filter list_ex_find
                 find_filter)

lemma eq_tgts: "filter (\<lambda> y. y \<notin> X \<and> y \<in> T0 X) [0..<n] = csr.tgts (csr.exch_ctx X)"
  by (simp only: csr.tgts_def in_ST ctx_parts filter_filter)

lemma ap_char: 
  "csr.augmenting_path X = 
     (case find (csr.in_T (csr.exch_ctx X)) (csr.srcs (csr.exch_ctx X)) of
        Some s \<Rightarrow> Some [s]
      | None \<Rightarrow> 
          (if filter (csr.has_nb (csr.exch_ctx X)) (csr.srcs (csr.exch_ctx X)) = [] then None 
           else csr.target_path (build_nhlists (EE X)) 
                  (filter (csr.has_nb (csr.exch_ctx X)) (csr.srcs (csr.exch_ctx X))) 
                  (csr.tgts (csr.exch_ctx X))))"
  by (simp only: csr.augmenting_path_def Let_def)

lemma bfs_ok:
  assumes "filter (csr.has_nb (csr.exch_ctx X)) (csr.srcs (csr.exch_ctx X)) \<noteq> []"
  shows "bfs_csr n (EE X) (filter (csr.has_nb (csr.exch_ctx X)) (csr.srcs (csr.exch_ctx X)))"
proof(rule bfs_csr.intro)
  fix u v
  assume "(u, v) \<in> set (EE X)"
  then show "u < n \<and> v < n"
    by (rule EE_bound[OF X])
next
  show "distinct (filter (csr.has_nb (csr.exch_ctx X)) (csr.srcs (csr.exch_ctx X)))"
    using csr.srcs(2)[OF X] by (rule distinct_filter)
next
  show "filter (csr.has_nb (csr.exch_ctx X)) (csr.srcs (csr.exch_ctx X)) \<noteq> []"
    by (rule assms)
next
  show "set (filter (csr.has_nb (csr.exch_ctx X)) (csr.srcs (csr.exch_ctx X))) \<subseteq> dVs (set (EE X))"
  proof
    fix u
    assume "u \<in> set (filter (csr.has_nb (csr.exch_ctx X)) (csr.srcs (csr.exch_ctx X)))"
    then have u: "u \<in> set (csr.srcs (csr.exch_ctx X))" "csr.has_nb (csr.exch_ctx X) u"
      by simp_all
    obtain v where "(u, v) \<in> set (EE X)"
      using csr.has_nb[OF X u(1)] u(2) unfolding csr.build_graph(4) by blast
    then show "u \<in> dVs (set (EE X))"
      by (rule dVsI(1))
  qed
qed

lemma nb_char:
  "\<lbrakk>y < n; y \<notin> X\<rbrakk> \<Longrightarrow> (nbrs (EE X) y \<noteq> []) = 
     (y \<notin> T0 X \<and> find (\<lambda> x. x \<in> X \<and> exch_orcl2 (orcl_prep2 X) x y) [0..<n] \<noteq> None)"
  by (auto simp: nbrs_EE exch_nb_def allowed2_def T0_def filter_empty_conv find_None_iff)

subsubsection \<open>The Steps of a Search\<close>

lemma s_imp_rule:
  "y < n \<Longrightarrow> <gxs X Si Gc> s_imp Si y <\<lambda> r. gxs X Si Gc * \<up>(r = (y \<notin> X \<and> y \<in> S0 X))>"
  unfolding s_imp_def gxs_def S0_def by (sep_auto heap: smemb_rule o1.ins_imp)

lemma t_imp_rule:
  "y < n \<Longrightarrow> <gxs X Si Gc> t_imp Si y <\<lambda> r. gxs X Si Gc * \<up>(r = (y \<notin> X \<and> y \<in> T0 X))>"
  unfolding t_imp_def gxs_def T0_def by (sep_auto heap: smemb_rule o2.ins_imp)

lemma st_imp_rule:
  "y < n \<Longrightarrow> <gxs X Si Gc> st_imp Si y
   <\<lambda> r. gxs X Si Gc * \<up>(r = ((y \<notin> X \<and> y \<in> S0 X) \<and> y \<in> T0 X))>"
  unfolding st_imp_def s_imp_def gxs_def S0_def T0_def by (sep_auto heap: smemb_rule o1.ins_imp o2.ins_imp)

lemma find_st_rule:
  "<gxs X Si Gc> find_range_imp (st_imp Si) 0 n
   <\<lambda> r. gxs X Si Gc * \<up>(r = find (csr.in_T (csr.exch_ctx X)) (csr.srcs (csr.exch_ctx X)))>"
  unfolding eq_find[symmetric] by (rule find_range_imp_rule, rule st_imp_rule, assumption)

lemma has_nb_rule:
  assumes "y < n"
  shows "<gxs X Si Gc> has_nb_imp Gc Si y <\<lambda> r. gxs X Si Gc * \<up>(r = (nbrs (EE X) y \<noteq> []))>"
proof-
  have r: "<gxs X Si Gc * \<up>(False = False) * emp> has_nb_imp Gc Si y
           <\<lambda> r. gxs X Si Gc * emp * \<up>(r = foldl (\<lambda> a x. True) False (nbrs (EE X) y))>"
    unfolding has_nb_imp_def
    by (rule xnbs_rule[where A = "\<lambda> b bi. \<up>(bi = b)" and F = emp and f = "\<lambda> u a x. True", OF X])
       sep_auto
  show ?thesis
    by (rule ht_cons[OF _ _ r]) (sep_auto simp: foldl_True)+
qed

lemma is_src_imp_rule:
  "y < n \<Longrightarrow> <gxs X Si Gc> is_src_imp Gc Si y
   <\<lambda> r. gxs X Si Gc * \<up>(r = ((y \<notin> X \<and> y \<in> S0 X) \<and> 
            (y \<notin> T0 X \<and> find (\<lambda> x. x \<in> X \<and> exch_orcl2 (orcl_prep2 X) x y) [0..<n] \<noteq> None)))>"
  unfolding is_src_imp_def s_imp_def
  by (sep_auto heap: smemb_rule[where X = X] o1.ins_imp has_nb_rule[unfolded gxs_def] 
               simp: gxs_def S0_def nb_char)

lemma collect_src_rule:
  assumes "n \<le> length fl"
  shows "<Fr \<mapsto>\<^sub>a fl * gxs X Si Gc> collect_range_imp (is_src_imp Gc Si) n Fr
         <\<lambda> k. \<exists>\<^sub>A fl'. Fr \<mapsto>\<^sub>a fl' * gxs X Si Gc * 
               \<up>(length fl' = length fl \<and> 
                 k = length (filter (csr.has_nb (csr.exch_ctx X)) (csr.srcs (csr.exch_ctx X))) \<and> 
                 take k fl' = filter (csr.has_nb (csr.exch_ctx X)) (csr.srcs (csr.exch_ctx X)))>"
  unfolding eq_srcs[symmetric] by (rule collect_range_imp_rule[OF is_src_imp_rule assms])

lemma is_tgt_imp_rule:
  "y < n \<Longrightarrow> <bool_array_set_assn n V Vi * gxs X Si Gc> is_tgt_imp Si Vi y
   <\<lambda> r. bool_array_set_assn n V Vi * gxs X Si Gc * \<up>(r = ((y \<notin> X \<and> y \<in> T0 X) \<and> y \<in> V))>"
  unfolding is_tgt_imp_def t_imp_def gxs_def T0_def by (sep_auto heap: bool_array_set_memb_rule smemb_rule o2.ins_imp)

lemma find_tgt_rule:
  "<bool_array_set_assn n V Vi * gxs X Si Gc> find_range_imp (is_tgt_imp Si Vi) 0 n
   <\<lambda> r. bool_array_set_assn n V Vi * gxs X Si Gc * \<up>(r = find (\<lambda> y. y \<in> V) (csr.tgts (csr.exch_ctx X)))>"
  unfolding eq_tgts[symmetric] find_filter by (rule find_range_imp_rule, rule is_tgt_imp_rule, assumption)

lemma single_path_rule:
  assumes "s < n"
  shows "<parr_assn n Ra> Array.upd 0 s Ra <\<lambda> _. path_assn n (Some [s]) (Some 1) Ra>"
proof-
  have "rev (take 1 (l[0 := s])) = [s]" if "l \<noteq> []" for l :: "nat list"
    using that by (cases l) simp_all
  then show ?thesis
    unfolding parr_assn_def path_assn_def option.case(2) using assms by sep_auto
qed

subsubsection \<open>The BFS\<close>

context
  fixes ss
  assumes b: "bfs_csr n (EE X) ss"
begin

interpretation inst: BFS_lists_instance where is_visited_set = "fb.xvis Vh" 
  and visited_memb = bset_memb and distinct_ins = bset_ins and iterate_neighbourhood = xnbs
  and graph_assn = fb.gx and G = "build_nhlists (EE X)" and Gi = Gh and srcs = "rev ss" 
  and N = n and Fr = Fr and Bf = Bf and Da = Da and Pa = Pa for Vh Gh Fr Bf Da Pa
  using fb.BFS_sub fb.Vs_E
  by (auto intro!: BFS_lists_instance.intro BFS_lists_instance_axioms.intro)

lemma fin_eq: "csr.bfs_final (build_nhlists (EE X)) ss = fb.fin ss"
  unfolding csr.bfs_final_def fb.fin_def[OF b] by (rule refl)


lemma target_path_eq:
  "csr.target_path (build_nhlists (EE X)) ss ts = 
   (case find (\<lambda> y. y \<in> set (BFS_dist_state.visited (fb.fin ss))) ts of
      None \<Rightarrow> None
    | Some t \<Rightarrow> Some (inst.imp_bfs.parent_path (BFS_dist_state.dists (fb.fin ss)) (BFS_par_state.parent (fb.fin ss)) t []))"
  unfolding csr.target_path_def Let_def fin_eq by (rule refl)

lemma tail_rule:
  "<bool_array_set_assn n (set (BFS_dist_state.visited (fb.fin ss))) Vi * gxs X Si Gc * parr_assn n Ra *
    (inst.imp_dist_assn n Da (build_nhlists (EE X)) (BFS_dist_state.dists (fb.fin ss)) di *
     inst.imp_par_assn n Pa (build_nhlists (EE X)) (BFS_par_state.parent (fb.fin ss)) pari)>
     tail_imp Si Ra (Vi, di, pari)
   <\<lambda> res. gxs X Si Gc * 
           path_assn n (csr.target_path (build_nhlists (EE X)) ss (csr.tgts (csr.exch_ctx X))) res Ra *
           (bool_array_set_assn n (set (BFS_dist_state.visited (fb.fin ss))) Vi * 
            inst.imp_dist_assn n Da (build_nhlists (EE X)) (BFS_dist_state.dists (fb.fin ss)) di *
            inst.imp_par_assn n Pa (build_nhlists (EE X)) (BFS_par_state.parent (fb.fin ss)) pari)>"
proof-
  let ?V = "set (BFS_dist_state.visited (fb.fin ss))" and ?ts = "csr.tgts (csr.exch_ctx X)"
  let ?DP = "inst.imp_dist_assn n Da (build_nhlists (EE X)) (BFS_dist_state.dists (fb.fin ss)) di *
             inst.imp_par_assn n Pa (build_nhlists (EE X)) (BFS_par_state.parent (fb.fin ss)) pari"
  let ?f = "find (\<lambda> y. y \<in> ?V) ?ts"
  have f: "<bool_array_set_assn n ?V Vi * gxs X Si Gc * parr_assn n Ra * ?DP> find_range_imp (is_tgt_imp Si Vi) 0 n
           <\<lambda> r. bool_array_set_assn n ?V Vi * gxs X Si Gc * (parr_assn n Ra * ?DP) * \<up>(r = ?f)>"
    by (rule ht_frame_ac[OF find_tgt_rule[where V = ?V and Vi = Vi and Si = Si and Gc = Gc], 
                         where R = "parr_assn n Ra * ?DP"]) 
       (simp only: star_aci, rule ent_refl)+
  show ?thesis
  proof(cases ?f)
    case None
    have tp: "csr.target_path (build_nhlists (EE X)) ss ?ts = None"
      unfolding target_path_eq None option.case(1) by (rule refl)
    show ?thesis
      unfolding tail_imp_def prod.case tp
      by (rule ht_bind[OF f], rule ht_pure_pre, simp only: None option.case(1),
          rule ht_cons_pre[OF _ ht_return_wp]) (simp only: path_None star_aci, rule ent_refl)
  next
    case (Some t)
    let ?pp = "inst.imp_bfs.parent_path (BFS_dist_state.dists (fb.fin ss)) (BFS_par_state.parent (fb.fin ss)) t []"
    have tp: "csr.target_path (build_nhlists (EE X)) ss ?ts = Some ?pp"
      unfolding target_path_eq Some option.case(2) by (rule refl)
    have p: "<parr_assn n Ra * ?DP * (bool_array_set_assn n ?V Vi * gxs X Si Gc)> bfs_path di pari Ra t
             <\<lambda> k. ?DP * path_assn n (Some ?pp) (Some k) Ra * (bool_array_set_assn n ?V Vi * gxs X Si Gc)>"
      using ht_frame[OF fb.path_len_rule[OF b Some], where R = "bool_array_set_assn n ?V Vi * gxs X Si Gc"]
      by (simp only: mult.assoc)
    show ?thesis
      unfolding tail_imp_def prod.case tp
      by (rule ht_bind[OF f], rule ht_pure_pre, simp only: Some option.case(2),
          rule ht_bind[OF ht_cons_pre[OF _ p]], (simp only: star_aci, rule ent_refl),
          rule ht_cons_pre[OF _ ht_return_wp]) (simp only: star_aci, rule ent_refl)
  qed
qed

lemma round_rule:
  assumes "length fl = Suc n" "take (length ss) fl = ss"
  shows "<Fr \<mapsto>\<^sub>a fl * gxs X Si Gc * parr_assn n Ra * len_assn n Vi * len_assn (Suc n) Bf * 
          len_assn n Da * len_assn n Pa>
           round_imp Gc Vi Fr Bf Da Pa Si Ra (length ss)
         <\<lambda> res. gxs X Si Gc * 
                 path_assn n (csr.target_path (build_nhlists (EE X)) ss (csr.tgts (csr.exch_ctx X))) res Ra *
                 work_assn n Vi Fr Bf Da Pa>"
proof-
  let ?Fl = "Fr \<mapsto>\<^sub>a fl" and ?G = "gxs X Si Gc" and ?R = "parr_assn n Ra" and ?B = "len_assn (Suc n) Bf"
  let ?V = "set (BFS_dist_state.visited (fb.fin ss))"
  let ?D = "inst.imp_dist_assn n Da (build_nhlists (EE X)) (BFS_dist_state.dists (fb.fin ss)) Da"
  let ?P = "inst.imp_par_assn n Pa (build_nhlists (EE X)) (BFS_par_state.parent (fb.fin ss)) Pa"
  let ?T = "csr.target_path (build_nhlists (EE X)) ss (csr.tgts (csr.exch_ctx X))"
  have raw: "<?Fl * ?G * ?R * len_assn n Vi * ?B * len_assn n Da * len_assn n Pa>
               round_imp Gc Vi Fr Bf Da Pa Si Ra (length ss)
             <\<lambda> res. ?G * path_assn n ?T res Ra * 
                    (bool_array_set_assn n ?V Vi * ?D * ?P * len_assn (Suc n) Fr * ?B)>"
    unfolding round_imp_def bfs_run_def xround_def
    by (rule ht_bind[OF ht_frame_ac[OF clear_len[where Vi = Vi], 
                       where R = "?Fl * ?G * ?R * ?B * len_assn n Da * len_assn n Pa"]],
        (simp only: star_aci, rule ent_refl), rule ent_refl,
        rule ht_bind[OF ht_frame_ac[OF fill_len[where a = Da and f = id], 
                       where R = "bool_array_set_assn n {} Vi * (?Fl * ?G * ?R * ?B * len_assn n Pa)"]],
        (simp only: star_aci, rule ent_refl), rule ent_refl,
        rule ht_bind[OF ht_frame_ac[OF fill_len[where a = Pa and f = id], 
                       where R = "Da \<mapsto>\<^sub>a map id [0..<n] * (bool_array_set_assn n {} Vi * (?Fl * ?G * ?R * ?B))"]],
        (simp only: star_aci, rule ent_refl), rule ent_refl,
        rule ht_bind[OF ht_frame_ac[OF fb.bfs_len_rule[OF b assms, where Bf = Bf and Vi = Vi and Fr = Fr and
                                       Da = Da and Pa = Pa and Gh = "(Si, Gc)", unfolded prod.case],
                                    where R = ?R]],
        (simp only: star_aci, rule ent_refl), rule ent_refl,
        rule ht_frame_ac[OF tail_rule[where Vi = Vi and Si = Si and Gc = Gc and Ra = Ra and Da = Da and
                                       Pa = Pa and di = Da and pari = Pa], 
                         where R = "len_assn (Suc n) Fr * ?B"])
       (simp only: star_aci, rule ent_refl)+
  show ?thesis
    by (rule ht_cons_post[OF raw]) 
       (rule ent_true_drop(2), rule ent_star_mono[OF ent_refl fb.work_ent[OF b]])
qed

end

subsubsection \<open>A Search\<close>

lemma collect_src_len:
  "<len_assn (Suc n) Fr * gxs X Si Gc> collect_range_imp (is_src_imp Gc Si) n Fr
   <\<lambda> k. \<exists>\<^sub>A fl'. Fr \<mapsto>\<^sub>a fl' * gxs X Si Gc * 
         \<up>(length fl' = Suc n \<and> 
           k = length (filter (csr.has_nb (csr.exch_ctx X)) (csr.srcs (csr.exch_ctx X))) \<and> 
           take k fl' = filter (csr.has_nb (csr.exch_ctx X)) (csr.srcs (csr.exch_ctx X)))>"
proof(rule pull_len)
  fix fl :: "nat list"
  assume fl: "length fl = Suc n"
  have r: "<Fr \<mapsto>\<^sub>a fl * gxs X Si Gc> collect_range_imp (is_src_imp Gc Si) n Fr
           <\<lambda> k. \<exists>\<^sub>A fl'. Fr \<mapsto>\<^sub>a fl' * gxs X Si Gc * 
             \<up>(length fl' = length fl \<and> 
               k = length (filter (csr.has_nb (csr.exch_ctx X)) (csr.srcs (csr.exch_ctx X))) \<and> 
               take k fl' = filter (csr.has_nb (csr.exch_ctx X)) (csr.srcs (csr.exch_ctx X)))>"
    by (rule collect_src_rule) (simp add: fl)
  show "<Fr \<mapsto>\<^sub>a fl * gxs X Si Gc> collect_range_imp (is_src_imp Gc Si) n Fr
   <\<lambda> k. \<exists>\<^sub>A fl'. Fr \<mapsto>\<^sub>a fl' * gxs X Si Gc * 
         \<up>(length fl' = Suc n \<and> 
           k = length (filter (csr.has_nb (csr.exch_ctx X)) (csr.srcs (csr.exch_ctx X))) \<and> 
           take k fl' = filter (csr.has_nb (csr.exch_ctx X)) (csr.srcs (csr.exch_ctx X)))>"
    unfolding fl[symmetric] by (rule r)
qed

lemma collect_src_none:
  "<len_assn (Suc n) Fr * gxs X Si Gc> collect_range_imp (is_src_imp Gc Si) n Fr
   <\<lambda> k. len_assn (Suc n) Fr * gxs X Si Gc * 
         \<up>(k = length (filter (csr.has_nb (csr.exch_ctx X)) (csr.srcs (csr.exch_ctx X))))>"
  by (rule ht_cons_post[OF collect_src_len]) (unfold len_assn_def, sep_auto)

theorem aug_path_imp_rule:
  "<parr_assn n Ra * gxs X Si Gc * work_assn n Vi Fr Bf Da Pa> aug_path_imp Gc Vi Fr Bf Da Pa Si Ra
   <\<lambda> res. path_assn n (csr.augmenting_path X) res Ra * gxs X Si Gc * work_assn n Vi Fr Bf Da Pa>"
proof(cases "find (csr.in_T (csr.exch_ctx X)) (csr.srcs (csr.exch_ctx X))")
  case (Some s)
  have "s \<in> S X"
    using conjunct2[OF find_SomeD[OF Some]] unfolding csr.srcs(1)[OF X] .
  then have s: "s < n"
    using S_in_carrier[OF X(3,4)] by auto
  show ?thesis 
    unfolding aug_path_imp_def ap_char Some option.case(2)
    by (sep_auto heap: find_st_rule single_path_rule[OF s] simp: Some)
next
  case None
  let ?ss = "filter (csr.has_nb (csr.exch_ctx X)) (csr.srcs (csr.exch_ctx X))"
  let ?W = "parr_assn n Ra * len_assn n Vi * len_assn (Suc n) Bf * len_assn n Da * len_assn n Pa"
  have st: "<parr_assn n Ra * gxs X Si Gc * work_assn n Vi Fr Bf Da Pa> find_range_imp (st_imp Si) 0 n 
            <\<lambda> r. gxs X Si Gc * \<up>(r = find (csr.in_T (csr.exch_ctx X)) (csr.srcs (csr.exch_ctx X))) * 
                  (parr_assn n Ra * work_assn n Vi Fr Bf Da Pa)>"
    by (rule ht_frame_ac[OF find_st_rule[where Si = Si and Gc = Gc], 
                         where R = "parr_assn n Ra * work_assn n Vi Fr Bf Da Pa"]) 
       (simp only: star_aci, rule ent_refl)+
  show ?thesis
  proof(cases "?ss = []")
    case True
    have ap: "csr.augmenting_path X = None"
      unfolding ap_char None option.case(1) if_P[OF True] by (rule refl)
    have co: "<gxs X Si Gc * (parr_assn n Ra * work_assn n Vi Fr Bf Da Pa)> 
                collect_range_imp (is_src_imp Gc Si) n Fr
              <\<lambda> k. len_assn (Suc n) Fr * gxs X Si Gc * \<up>(k = length ?ss) * ?W>"
      by (rule ht_frame_ac[OF collect_src_none[where Fr = Fr and Si = Si and Gc = Gc], where R = ?W])
         (simp only: work_assn_def star_aci, rule ent_refl)+
    show ?thesis 
      unfolding aug_path_imp_def ap
      by (rule ht_bind[OF st], rule pure_mid, simp only: None option.case(1),
          rule ht_bind[OF co], rule pure_mid, simp only: True list.size(3) simp_thms(6) if_True,
          rule ht_cons_pre[OF _ ht_return_wp])
         (simp only: path_None work_assn_def star_aci, rule ent_refl)
  next
    case False
    have co: "<gxs X Si Gc * (parr_assn n Ra * work_assn n Vi Fr Bf Da Pa)> 
                collect_range_imp (is_src_imp Gc Si) n Fr
              <\<lambda> k. (\<exists>\<^sub>A fl'. Fr \<mapsto>\<^sub>a fl' * gxs X Si Gc * 
                       \<up>(length fl' = Suc n \<and> k = length ?ss \<and> take k fl' = ?ss)) * ?W>"
      by (rule ht_frame_ac[OF collect_src_len[where Fr = Fr and Si = Si and Gc = Gc], where R = ?W])
         (simp only: work_assn_def star_aci, rule ent_refl)+
    show ?thesis 
      unfolding aug_path_imp_def ap_char None option.case(1) if_not_P[OF False]
      by (rule ht_bind[OF st], rule pure_mid, simp only: None option.case(1),
          rule ht_bind[OF co], rule ex_mid, rule pure_mid, elim conjE, 
          simp only: length_0_conv False if_False,
          rule ht_cons[OF _ _ round_rule[OF bfs_ok[OF False]]])
         ((simp only: mult.assoc, rule ent_refl), (rule ent_true_drop(2), simp only: star_aci, rule ent_refl),
          assumption+)
  qed
qed

end

subsubsection \<open>The Path Search of the Imperative Loop\<close>

text \<open>The static data of a search: the oracles, the CSR and the work arrays.\<close>

definition "mst Gc Vi Fr Bf Da Pa = ost1 * ost2 * bcsr_assn (build_nhlists es0) Gc * work_assn n Vi Fr Bf Da Pa"

theorem imp_loop:
  "unweighted_intersection_imp_loop csr.augmenting_path indep1 indep2 {0..<n} n sol_assn smemb_imp 
     sins_imp sdel_imp (aug_path_imp Gc Vi Fr Bf Da Pa) (mst Gc Vi Fr Bf Da Pa)"
proof(intro unweighted_intersection_imp_loop.intro unweighted_intersection_imp_loop_axioms.intro 
        allI impI, goal_cases)
  case 1
  show ?case
    by (rule intersection_augment_imp.intro[OF imp_nat_set_axioms])
next
  case 2
  show ?case
    by (rule csr.exch_loop.unweighted_intersection_path_loop_axioms)
next
  case 3
  show ?case
    by auto
next
  case (4 X Si Ra)
  show ?case
    by (rule ht_cons[OF _ _ aug_path_imp_rule[OF 4]])
       ((simp only: mst_def gxs_def star_aci, rule ent_refl), 
        (rule ent_true_drop(2), simp only: mst_def gxs_def star_aci, rule ent_refl))
qed

text \<open>The loop on preallocated arrays.\<close>

theorem loop_correct:
  "<(sol_assn {} Si) * parr_assn n Ra * mst Gc Vi Fr Bf Da Pa>
     unweighted_intersection_imp_loop_spec.mi_loop_imp sins_imp sdel_imp
       (aug_path_imp Gc Vi Fr Bf Da Pa) Si Ra
   <\<lambda> _. \<exists>\<^sub>A X. sol_assn X Si * parr_assn n Ra * mst Gc Vi Fr Bf Da Pa * \<up>(is_max X)>"
proof-
  interpret l: unweighted_intersection_imp_loop csr.augmenting_path indep1 indep2
    "{0..<n}" n sol_assn smemb_imp sins_imp sdel_imp "aug_path_imp Gc Vi Fr Bf Da Pa"
    "mst Gc Vi Fr Bf Da Pa"
    by (rule imp_loop)
  show ?thesis
    by (rule l.mi_loop_imp_correct)
qed

end

end
