theory BFS_Instantiation
  imports BFS_Refinement Directed_Set_Graphs.CSR_Neighbour_Lists
    Directed_Set_Graphs.CSR_Graph_Simple Directed_Set_Graphs.CSR_Buildup_Imperative
begin

section \<open>An Instantiation of the Imperative BFS\<close>

text \<open>The locale @{locale BFS_lists_instance} is instantiated with purely imperative data
      structures of fixed size, allocated once:

        \<^item> the visited set is a Boolean array over the vertices \<open>{..<n}\<close>,
        \<^item> distances and parents are arrays over the vertices,
        \<^item> the frontier is an array with a fill pointer and a buffer array of the same size, and
        \<^item> the graph is in compressed sparse row (CSR) form, built from the arrays of tails and
          heads by @{theory Directed_Set_Graphs.CSR_Buildup_Imperative}: an array of heads grouped
          by their tails, together with the array of the starts of the groups.

      The CSR of neighbours with first and last positions from
      @{theory Directed_Set_Graphs.CSR_Graph_Simple}, abstracted to the neighbour lists of an edge
      list from @{theory Directed_Set_Graphs.CSR_Neighbour_Lists}, is also set up as an instance
      of the subprocedures; it is used elsewhere.\<close>


subsection \<open>The visited set as a Boolean array\<close>

definition bset_assn :: "nat set \<Rightarrow> nat set \<Rightarrow> bool array \<Rightarrow> assn" where
  "bset_assn U S a =
     (\<exists>\<^sub>A l. a \<mapsto>\<^sub>a l * \<up>((\<forall>u \<in> U. u < length l \<and> (l ! u \<longleftrightarrow> u \<in> S)) \<and> S \<subseteq> U))"

definition bset_empty :: "nat \<Rightarrow> bool array Heap" where
  "bset_empty n = Array.new n False"

definition bset_memb :: "nat \<Rightarrow> bool array \<Rightarrow> bool Heap" where
  "bset_memb v a = Array.nth a v"

definition bset_ins :: "nat \<Rightarrow> bool array \<Rightarrow> bool array Heap" where
  "bset_ins v a = Array.upd v True a"

lemma bset_only_in_univ: "bset_assn U S a = bset_assn U S a * \<up>(S \<subseteq> U)"
  unfolding bset_assn_def by (rule ent_iffI) sep_auto+

lemma bset_empty_rule: "U \<subseteq> {..<n} \<Longrightarrow> <emp> bset_empty n <bset_assn U {}>"
  unfolding bset_assn_def bset_empty_def by (sep_auto simp: subset_iff)

lemma bset_memb_rule:
  "<bset_assn U S a * \<up>(v \<in> U)> bset_memb v a <\<lambda>r. bset_assn U S a * \<up>(r \<longleftrightarrow> v \<in> S)>"
  unfolding bset_assn_def bset_memb_def by sep_auto

lemma bset_ins_rule:
  "<bset_assn U S a * \<up>(v \<in> U \<and> v \<notin> S)> bset_ins v a <bset_assn U (Set.insert v S)>"
  unfolding bset_assn_def bset_ins_def by (sep_auto simp: nth_list_update)

subsection \<open>The graph as a CSR of neighbours\<close>

text \<open>The graph handle is the triple of the array of neighbours and the arrays of the first and
      the last positions.\<close>

fun csr3_assn :: "(nat \<Rightarrow> nat list option) \<Rightarrow> nat array \<times> nat array \<times> nat array \<Rightarrow> assn" where
  "csr3_assn G (Ga, Si, Ei) = CSR_assn G Ga Si Ei"

fun bfs_nbs where
  "bfs_nbs (Ga, Si, Ei) = iterate_neighbourhood Ga Si Ei"

lemma bfs_nbs_rule:
  "(\<And> acc acci x vs. \<lbrakk>G v = Some vs; x \<in> set vs\<rbrakk> \<Longrightarrow>
       <acc_assn acc acci * F> fi v x acci <\<lambda> r. acc_assn (f v acc x) r * F>) \<Longrightarrow>
   <csr3_assn G Gi * acc_assn acc acci * F>
     bfs_nbs Gi v fi acci
   <\<lambda> r. csr3_assn G Gi * F * acc_assn (foldl (f v) acc (case G v of None \<Rightarrow> [] | Some vs \<Rightarrow> vs)) r>"
  by (cases Gi rule: prod_cases3) (simp add: iterate_neighbourhood_rule)

lemma BFS_subprocedures_lists_bset:
  "BFS_subprocedures_lists bset_assn bset_memb bset_ins bfs_nbs csr3_assn"
  by unfold_locales (rule bset_only_in_univ bset_memb_rule bset_ins_rule bfs_nbs_rule | assumption)+

subsection \<open>The graph as a CSR built from arrays of endpoints\<close>

text \<open>The edges are given by the array \<open>Fa\<close> of their tails and the array \<open>Ta\<close> of their heads.
      The counting sort of @{theory Directed_Set_Graphs.CSR_Buildup_Imperative} iterates over the
      positions of the edges, reads the tail as the key and stores the head. The result is the
      array \<open>B\<close> of the starts of the blocks of the vertices, with \<open>n + 1\<close> entries, and the array
      \<open>E\<close> of the heads, grouped by their tails.\<close>

definition pos_has_next :: "nat array \<times> nat array \<Rightarrow> nat \<Rightarrow> bool Heap" where
  "pos_has_next = (\<lambda>(Fa, Ta) i. do { l \<leftarrow> Array.len Fa; return (i < l) })"

definition pos_cur :: "nat array \<times> nat array \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "pos_cur = (\<lambda>_ i. return i)"

definition pos_adv :: "nat array \<times> nat array \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "pos_adv = (\<lambda>_ i. return (Suc i))"

definition pos_tail :: "nat array \<times> nat array \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "pos_tail = (\<lambda>(Fa, Ta) i. Array.nth Fa i)"

definition pos_head :: "nat array \<times> nat array \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "pos_head = (\<lambda>(Fa, Ta) i. Array.nth Ta i)"

text \<open>The neighbours of \<open>v\<close> are the entries of \<open>E\<close> from \<open>B ! v\<close> to \<open>B ! (v + 1)\<close>, exclusive.\<close>

definition bfs_csr_nbs where
  "bfs_csr_nbs Gi v fi acci = (case Gi of (Ba, Ea) => do {
     l \<leftarrow> Array.len Ba;
     if Suc v < l then do {
       i \<leftarrow> Array.nth Ba v;
       j \<leftarrow> Array.nth Ba (Suc v);
       iterate_range_strict Ea i j (fi v) acci }
     else return acci })"

definition bcsr_rel :: "(nat => nat list option) => nat list => nat list => bool" where
  "bcsr_rel G Bs Es \<longleftrightarrow>
     (\<forall>v. Suc v < length Bs --> Bs ! v \<le> Bs ! Suc v \<and> Bs ! Suc v \<le> length Es) \<and>
     (\<forall>v. (case G v of None => [] | Some vs => vs) =
          (if Suc v < length Bs then nths Es {Bs ! v..<Bs ! Suc v} else []))"

definition bcsr_assn :: "(nat => nat list option) => nat array \<times> nat array => assn" where
  "bcsr_assn G = (\<lambda>(Ba, Ea). \<exists>\<^sub>A Bs Es. Ba \<mapsto>\<^sub>a Bs * Ea \<mapsto>\<^sub>a Es * \<up>(bcsr_rel G Bs Es))"

text \<open>The rule of @{const iterate_range_strict} in @{theory Imperative.Array_Range_Iteration}
      requires the end of the range to be a valid index; the last block ends at the length of
      the array.\<close>

lemma nths_strict_split_off_first_le:
  assumes "start < end" "end \<le> length list"
  shows "nths list {start..<end} = list ! start # nths list {Suc start..<end}"
proof -
  have "start < length (take end list)"
    using assms by simp
  then have "drop start (take end list) = take end list ! start # drop (Suc start) (take end list)"
    by (rule Cons_nth_drop_Suc[symmetric])
  then show ?thesis
    using assms(1) unfolding nths_intervall_strict_as_drop_and_take by simp
qed

lemma iterate_range_strict_le_rule:
 assumes "\<And> acc acci x. x \<in> set (nths list {start..<end}) \<Longrightarrow> <acc_assn acc acci * F> fi x acci
            <\<lambda> r. acc_assn (f acc x) r * F>"
  shows "<arr \<mapsto>\<^sub>a list * \<up> (end \<le> length list) *F * acc_assn acc acci>
          iterate_range_strict arr start end fi acci
         <\<lambda> r. arr \<mapsto>\<^sub>a list * acc_assn (foldl f acc (nths list {start..<end})) r *  F>"
  using assms
proof(induction arbitrary: start acc acci rule: iterate_range_strict.fixp_induct, goal_cases)
  case 1
  then show ?case
    by simp
next
  case 2
  then show ?case
    by simp
next
  case (3 fi start acc acci)
  note IH = this
  show ?case
     using IH(1)[of "Suc start" "f acc _"] IH(2)
     by (sep_auto simp: nths_strict_split_off_first_le[of start] split: if_split)
qed

lemma bfs_csr_nbs_raw_rule:
  assumes step: "\<And>acc acci x vs. [|G v = Some vs; x \<in> set vs|] ==>
                   <acc_assn acc acci * F> fi v x acci <\<lambda>r. acc_assn (f v acc x) r * F>"
    and rel: "bcsr_rel G Bs Es"
  shows "<Ba \<mapsto>\<^sub>a Bs * Ea \<mapsto>\<^sub>a Es * acc_assn acc acci * F> bfs_csr_nbs (Ba, Ea) v fi acci
         <\<lambda>r. Ba \<mapsto>\<^sub>a Bs * Ea \<mapsto>\<^sub>a Es * F *
              acc_assn (foldl (f v) acc (case G v of None => [] | Some vs => vs)) r>"
proof (cases "Suc v < length Bs")
  case True
  have nb: "(case G v of None => [] | Some vs => vs) = nths Es {Bs ! v..<Bs ! Suc v}"
    and le: "Bs ! Suc v \<le> length Es"
    using rel True unfolding bcsr_rel_def by auto
  have step': "<acc_assn acc acci * F> fi v x acci <\<lambda>r. acc_assn (f v acc x) r * F>"
    if "x \<in> set (nths Es {Bs ! v..<Bs ! Suc v})" for acc acci x
    using step[of _ x] that nb by (cases "G v") auto
  show ?thesis
    using True le unfolding bfs_csr_nbs_def
    by (sep_auto heap: iterate_range_strict_le_rule[where f = "f v", OF step'] simp: nb)
next
  case False
  have nb: "(case G v of None => [] | Some vs => vs) = []"
    using rel False unfolding bcsr_rel_def by auto
  show ?thesis
    using False unfolding bfs_csr_nbs_def by (sep_auto simp: nb)
qed

lemma bfs_csr_nbs_rule:
  "(\<And> acc acci x vs. [|G v = Some vs; x \<in> set vs|] ==>
       <acc_assn acc acci * F> fi v x acci <\<lambda> r. acc_assn (f v acc x) r * F>) ==>
   <bcsr_assn G Gi * acc_assn acc acci * F>
     bfs_csr_nbs Gi v fi acci
   <\<lambda> r. bcsr_assn G Gi * F * acc_assn (foldl (f v) acc (case G v of None => [] | Some vs => vs)) r>"
  unfolding bcsr_assn_def
  by (cases Gi) (sep_auto heap: bfs_csr_nbs_raw_rule)

lemma BFS_subprocedures_lists_bcsr:
  "BFS_subprocedures_lists bset_assn bset_memb bset_ins bfs_csr_nbs bcsr_assn"
  by unfold_locales (rule bset_only_in_univ bset_memb_rule bset_ins_rule bfs_csr_nbs_rule | assumption)+


section \<open>The Code\<close>

text \<open>The graph is given by the arrays \<open>Fa\<close> and \<open>Ta\<close> of the tails and the heads of its edges.
      The CSR is built by the counting sort of
      @{theory Directed_Set_Graphs.CSR_Buildup_Imperative} over the positions of the edges, with
      the tails as keys and the heads as stored values.

      The global interpretations of the code locales only fix operations and have no
      assumptions.\<close>

global_interpretation bfs_csr_code: imp_csr_buildup_code n pos_has_next pos_cur pos_adv pos_tail
    pos_head
  for n
  defines bfs_csr_build = bfs_csr_code.csr_build_imp
    and bfs_csr_count = bfs_csr_code.count_imp
    and bfs_csr_prefix = bfs_csr_code.prefix_imp
    and bfs_csr_init = bfs_csr_code.init_E_imp
    and bfs_csr_fill = bfs_csr_code.fill_imp
  done

global_interpretation bfs_sub_code: BFS_subprocedures_lists_code bset_memb bset_ins bfs_csr_nbs
  defines bfs_inner_loop = bfs_sub_code.inner_loop
    and bfs_outer_loop = bfs_sub_code.outer_loop
    and bfs_src_to_cf = bfs_sub_code.imp_src_to_cf
    and bfs_cf_is_empty = bfs_sub_code.imp_cf_is_empty
    and bfs_set_srcs_visited = bfs_sub_code.set_srcs_visited
    and bfs_set_dists = bfs_sub_code.set_all_dists_in_front_imp
    and bfs_round = bfs_sub_code.next_frontier_current_parents_imp
  done

global_interpretation bfs_code: BFS_Imperative_spec bfs_src_to_cf bfs_set_srcs_visited
    "bfs_round Gi" bfs_cf_is_empty bset_memb bfs_set_dists Array.nth Array.nth
  for Gi :: "nat array \<times> nat array"
  defines bfs_loop = bfs_code.BFS_par_imp
    and bfs_init = bfs_code.initial_state_imp
    and bfs_check_reachable = bfs_code.check_reachable
    and bfs_visited_dists_parents = bfs_code.visited_dists_parents_imp
    and bfs_path_rev = bfs_code.path_rev_imp
    and bfs_path = bfs_code.path_imp
  done

text \<open>Copying the sources into the first frontier array.\<close>

partial_function (heap) copy_prefix_imp :: "'a::heap array \<Rightarrow> 'a array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "copy_prefix_imp Sa Fa k i =
     (if i < k then do {
        x \<leftarrow> Array.nth Sa i;
        Array.upd i x Fa;
        copy_prefix_imp Sa Fa k (Suc i) }
      else return ())"

text \<open>The final program takes the number of vertices, the arrays of tails and heads and the array
      of distinct sources. It builds the CSR, allocates all other data structures and runs the BFS.
      The distance and the parent array are initialised with the identity. It returns the visited
      set, the distances and the parents.\<close>

definition bfs_csr_run :: "nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow>
                            (bool array \<times> nat array \<times> nat array) Heap" where
  "bfs_csr_run n Fa Ta Sa = do {
     Gi \<leftarrow> bfs_csr_build n (Fa, Ta) 0;
     k \<leftarrow> Array.len Sa;
     Fr \<leftarrow> Array.new (Suc n) 0;
     copy_prefix_imp Sa Fr k 0;
     Bf \<leftarrow> Array.new (Suc n) 0;
     Vi \<leftarrow> bset_empty n;
     Da \<leftarrow> Array.make n id;
     Pa \<leftarrow> Array.make n id;
     bfs_visited_dists_parents Gi Vi (Fr, k, Bf) Da Pa }"

declare copy_prefix_imp.simps[code] iterate_range_strict.simps[code] iterate_range.simps[code]
  bfs_csr_code.count_imp.simps[code] bfs_csr_code.prefix_imp.simps[code]
  bfs_csr_code.fill_imp.simps[code] bfs_code.BFS_par_imp.simps[code] bfs_code.path_rev_imp.simps[code]

export_code bfs_csr_run bfs_path checking SML_imp



section \<open>Correctness\<close>

text \<open>The input: the number of vertices \<open>n\<close>, the lists \<open>fs\<close> and \<open>ts\<close> of tails and heads of
      the edges, with endpoints below \<open>n\<close>, and the distinct list of sources \<open>ss\<close>, which are
      vertices of the graph.\<close>

lemma copy_prefix_imp_rule:
  "\<lbrakk>i \<le> length ss; length ss \<le> length fl; take i fl = take i ss\<rbrakk> \<Longrightarrow>
   <Sa \<mapsto>\<^sub>a ss * Fa \<mapsto>\<^sub>a fl> copy_prefix_imp Sa Fa (length ss) i
   <\<lambda>_. Sa \<mapsto>\<^sub>a ss * Fa \<mapsto>\<^sub>a (ss @ drop (length ss) fl)>"
proof(induction "length ss - i" arbitrary: i fl)
  case 0
  have i: "i = length ss"
    using 0 by simp
  have "ss @ drop (length ss) fl = fl"
    using 0(4) i append_take_drop_id[of "length ss" fl] by simp
  then show ?case
    using i by (subst copy_prefix_imp.simps) sep_auto
next
  case (Suc m)
  have i: "i < length ss"
    using Suc.hyps(2) by simp
  have m: "m = length ss - Suc i"
    using Suc.hyps(2) by simp
  have tk: "take (Suc i) (fl[i := ss ! i]) = take (Suc i) ss"
    using Suc.prems i by (simp add: take_Suc_conv_app_nth list_update_append)
  have dr: "drop (length ss) (fl[i := ss ! i]) = drop (length ss) fl"
    using i by (simp add: drop_update_cancel)
  show ?case
    using i Suc.prems(2)
    by (subst copy_prefix_imp.simps) (sep_auto heap: Suc.hyps(1)[OF m _ _ tk] simp: dr)
qed

locale bfs_csr =
  fixes n :: nat and es :: "(nat \<times> nat) list" and ss :: "nat list"
  assumes es_bound: "(u, v) \<in> set es \<Longrightarrow> u < n \<and> v < n"
    and ss_distinct: "distinct ss" and ss_nonempty: "ss \<noteq> []"
    and ss_in_graph: "set ss \<subseteq> dVs (set es)"
begin

text \<open>The graph described by the list of edges, and the set of sources.\<close>

definition \<E> :: "(nat \<times> nat) set" where
  "\<E> = set es"

definition \<S> :: "nat set" where
  "\<S> = set ss"

lemma Vs_build: "BFS_subprocedures_lists.Vs (build_nhlists es) = dVs \<E>"
proof-
  have key: "(\<exists>vs. build_nhlists es u = Some vs \<and> v \<in> set vs) \<longleftrightarrow> (u, v) \<in> set es" for u v
    by (auto simp: build_nhlists_def nbrs_def filter_empty_conv)
  show ?thesis
    unfolding BFS_subprocedures_lists.Vs_def[OF BFS_subprocedures_lists_bcsr] dVs_def \<E>_def
    by (simp add: key)
qed

lemma Vs_bound: "BFS_subprocedures_lists.Vs (build_nhlists es) \<subseteq> {..<n}"
proof
  fix x
  assume "x \<in> BFS_subprocedures_lists.Vs (build_nhlists es)"
  then obtain u v where uv: "(u, v) \<in> set es" "x = u \<or> x = v"
    unfolding Vs_build dVs_def \<E>_def by auto
  then show "x \<in> {..<n}"
    using es_bound[OF uv(1)] by auto
qed

interpretation inst: BFS_lists_instance where is_visited_set = bset_assn
  and visited_memb = bset_memb and distinct_ins = bset_ins and iterate_neighbourhood = bfs_csr_nbs
  and graph_assn = bcsr_assn and G = "build_nhlists es" and Gi = Gi and srcs = "rev ss" and N = n
  and Fr = Fr and Bf = Bf and Da = Da and Pa = Pa for Gi Fr Bf Da Pa
  using BFS_subprocedures_lists_bcsr Vs_bound
  by (auto intro!: BFS_lists_instance.intro BFS_lists_instance_axioms.intro)

lemma digraph_abs_build: "inst.Graph.digraph_abs (build_nhlists es) = \<E>"
proof-
  have nb: "set (case build_nhlists es u of None \<Rightarrow> [] | Some vs \<Rightarrow> vs) = set (nbrs es u)" for u
  proof(cases "nbrs es u = []")
    case True
    show ?thesis
      unfolding build_nhlists_def
      by (subst if_P[OF True], subst option.case(1), subst True) (rule refl)
  next
    case False
    show ?thesis
      unfolding build_nhlists_def
      by (subst if_not_P[OF False], subst option.case(2)) (rule refl)
  qed
  have key: "v \<in> set (case build_nhlists es u of None \<Rightarrow> [] | Some vs \<Rightarrow> vs) \<longleftrightarrow> (u, v) \<in> set es"
    for u v
  proof
    assume "v \<in> set (case build_nhlists es u of None \<Rightarrow> [] | Some vs \<Rightarrow> vs)"
    then obtain e where e: "e \<in> set es" "fst e = u" "v = snd e"
      unfolding nb nbrs_def set_map set_filter by blast
    show "(u, v) \<in> set es"
      using e(1) unfolding e(2)[symmetric] e(3) prod.collapse .
  next
    assume "(u, v) \<in> set es"
    then have "(u, v) \<in> {e \<in> set es. fst e = u}"
      unfolding mem_Collect_eq fst_conv by (rule conjI) (rule refl)
    then have "snd (u, v) \<in> snd ` {e \<in> set es. fst e = u}"
      by (rule imageI)
    then show "v \<in> set (case build_nhlists es u of None \<Rightarrow> [] | Some vs \<Rightarrow> vs)"
      unfolding nb nbrs_def set_map set_filter snd_conv .
  qed
  show ?thesis
    unfolding inst.Graph.digraph_abs_def inst.Graph.neighbourhood_def key \<E>_def
    by (rule set_eqI) (simp only: mem_Collect_eq case_prod_beta prod.collapse)
qed

lemma BFS_axiom: "inst.imp_bfs.BFS_axiom"
proof-
  have "{v. build_nhlists es v \<noteq> None} \<subseteq> fst ` set es"
    unfolding dom_def[symmetric] build_nhlists_dom nbrs_def map_is_Nil_conv filter_empty_conv
    by blast
  then have fin: "finite {v. build_nhlists es v \<noteq> None}"
    by (rule finite_subset) (rule finite_imageI[OF finite_set])
  have nbfin: "finite (neighbourhood (set es) u)" for u
    by (rule finite_subset[of _ "snd ` set es"]) (auto simp: neighbourhood_def)
  show ?thesis
    unfolding inst.imp_bfs.BFS_axiom_def digraph_abs_build \<E>_def inst.Graph.graph_inv_def
              inst.Graph.finite_graph_def inst.Graph.finite_vsets_def set_rev distinct_rev set_empty
    by (intro conjI allI impI TrueI finite_set fin nbfin ss_in_graph ss_nonempty ss_distinct)
qed

text \<open>The code constants are those of the instance.\<close>

lemma code_eqs:
  "inst.imp_bfs.visited_dists_parents_imp Gi = bfs_visited_dists_parents Gi"
  "inst.imp_bfs.path_imp = bfs_path"
  by (simp_all add: bfs_visited_dists_parents_def bfs_path_def bfs_src_to_cf_def
                    bfs_set_srcs_visited_def bfs_round_def bfs_cf_is_empty_def bfs_set_dists_def)

subsection \<open>The result of the BFS\<close>

text \<open>The arrays returned are correct if, for every vertex of the graph @{term \<E>}, the
      visited array says whether it is reachable from a source, the distance array holds its
      distance from the sources if it is reachable, and the parent array holds, for every reachable
      vertex that is not a source, a reachable vertex from which an edge leads to it and whose
      distance is one smaller.\<close>

definition bfs_arrays :: "bool list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "bfs_arrays vs ds ps \<longleftrightarrow> (\<forall>x \<in> dVs \<E>.
     x < length vs \<and> x < length ds \<and> x < length ps \<and>
     (vs ! x \<longleftrightarrow> (\<exists>u \<in> \<S>. \<exists>q. vwalk_bet \<E> u q x)) \<and>
     (vs ! x \<longrightarrow> enat (ds ! x) = distance_set \<E> \<S> x) \<and>
     ((vs ! x \<and> x \<notin> \<S>) \<longrightarrow>
        vs ! (ps ! x) \<and> (ps ! x, x) \<in> \<E> \<and> distance_set \<E> \<S> x = distance_set \<E> \<S> (ps ! x) + 1))"

lemma bfs_arrays_intro:
  assumes V: "\<forall>u \<in> dVs \<E>. u < length l \<and> (l ! u \<longleftrightarrow> u \<in> set vis)"
    and D: "\<forall>i \<in> dVs \<E>. i < length dl \<and> d i = dl ! i"
    and P: "\<forall>i \<in> dVs \<E>. i < length pl \<and> p i = pl ! i"
    and c1: "\<forall>x. x \<in> set vis \<longleftrightarrow> (\<exists>u \<in> \<S>. \<exists>q. vwalk_bet \<E> u q x)"
    and c2: "\<forall>x \<in> set vis. enat (d x) = distance_set \<E> \<S> x"
    and c3: "\<forall>x \<in> set vis - \<S>. p x \<in> set vis \<and> (p x, x) \<in> \<E> \<and>
               distance_set \<E> \<S> x = distance_set \<E> \<S> (p x) + 1"
  shows "bfs_arrays l dl pl"
  unfolding bfs_arrays_def
proof
  fix x assume x: "x \<in> dVs \<E>"
  note lx = bspec[OF V x] and dx = bspec[OF D x] and px = bspec[OF P x]
  have xv: "x \<in> set vis" if "l ! x"
    using conjunct2[OF lx] that by (rule iffD1)
  have par: "l ! (pl ! x) \<and> (pl ! x, x) \<in> \<E> \<and> distance_set \<E> \<S> x = distance_set \<E> \<S> (pl ! x) + 1"
    if "l ! x" "x \<notin> \<S>"
  proof-
    have c: "p x \<in> set vis" "(p x, x) \<in> \<E>" "distance_set \<E> \<S> x = distance_set \<E> \<S> (p x) + 1"
      using bspec[OF c3 DiffI[OF xv[OF that(1)] that(2)]] by blast+
    show ?thesis
      unfolding conjunct2[OF px, symmetric] using c bspec[OF V dVsI(1)[OF c(2)]] by blast
  qed
  have "enat (dl ! x) = distance_set \<E> \<S> x" if "l ! x"
    unfolding conjunct2[OF dx, symmetric] by (rule bspec[OF c2 xv[OF that]])
  then show "x < length l \<and> x < length dl \<and> x < length pl \<and>
             (l ! x \<longleftrightarrow> (\<exists>u \<in> \<S>. \<exists>q. vwalk_bet \<E> u q x)) \<and>
             (l ! x \<longrightarrow> enat (dl ! x) = distance_set \<E> \<S> x) \<and>
             ((l ! x \<and> x \<notin> \<S>) \<longrightarrow>
                l ! (pl ! x) \<and> (pl ! x, x) \<in> \<E> \<and> distance_set \<E> \<S> x = distance_set \<E> \<S> (pl ! x) + 1)"
    using lx dx px c1 par by blast
qed

lemma arrays_ent:
  assumes "\<And>l dl pl. \<lbrakk>pv l; pd dl; pp pl\<rbrakk> \<Longrightarrow> res l dl pl"
  shows "F * (\<exists>\<^sub>A l. Vi \<mapsto>\<^sub>a l * \<up>(pv l)) * (\<exists>\<^sub>A dl. Da \<mapsto>\<^sub>a dl * \<up>(pd dl)) *
         (\<exists>\<^sub>A pl. Pa \<mapsto>\<^sub>a pl * \<up>(pp pl)) \<Longrightarrow>\<^sub>A
         \<exists>\<^sub>A vs ds ps. Vi \<mapsto>\<^sub>a vs * Da \<mapsto>\<^sub>a ds * Pa \<mapsto>\<^sub>a ps * \<up>(res vs ds ps) * true"
  using assms by sep_auto

lemma bfs_arrays_ent:
  assumes "\<forall>x. x \<in> set vis \<longleftrightarrow> (\<exists>u \<in> \<S>. \<exists>q. vwalk_bet \<E> u q x)"
    and "\<forall>x \<in> set vis. enat (d x) = distance_set \<E> \<S> x"
    and "\<forall>x \<in> set vis - \<S>. p x \<in> set vis \<and> (p x, x) \<in> \<E> \<and>
           distance_set \<E> \<S> x = distance_set \<E> \<S> (p x) + 1"
  shows "F * bset_assn (BFS_subprocedures_lists.Vs (build_nhlists es)) (set vis) Vi *
         inst.imp_dist_assn n Dh (build_nhlists es) d Da * inst.imp_par_assn n Ph (build_nhlists es) p Pa \<Longrightarrow>\<^sub>A
         \<exists>\<^sub>A vs ds ps. Vi \<mapsto>\<^sub>a vs * Da \<mapsto>\<^sub>a ds * Pa \<mapsto>\<^sub>a ps * \<up>(bfs_arrays vs ds ps) * true"
  unfolding bset_assn_def inst.imp_dist_assn_char inst.imp_par_assn_char Vs_build
  by (rule arrays_ent, rule bfs_arrays_intro[OF _ _ _ assms], (erule conjunct1)+)

lemma run_then_path:
  assumes "<P> m <\<lambda>r. (\<exists>\<^sub>A g1 g2 g3 g4 g5. Q g1 g2 g3 g4 g5 r) * F * true>"
    and "\<And>g1 g2 g3 g4 g5 a b d. <Q g1 g2 g3 g4 g5 (a, b, d) * Ra \<mapsto>\<^sub>a r> m' b d 
           <\<lambda>k. \<exists>\<^sub>A ps. Ra \<mapsto>\<^sub>a ps * \<up>(q k ps) * true>"
  shows "<P * Ra \<mapsto>\<^sub>a r> do { (a, b, d) \<leftarrow> m; m' b d } <\<lambda>k. \<exists>\<^sub>A ps. Ra \<mapsto>\<^sub>a ps * \<up>(q k ps) * true>"
  by (sep_auto heap: assms(1,2))

lemma frame_last3: "(P1 :: assn) * P2 * P3 * P4 * P5 \<Longrightarrow>\<^sub>A (P3 * P4 * P5) * (P1 * P2)"
  by (simp only: star_aci, rule ent_refl)

lemma path_post_weaken:
  assumes "\<And>k ps. p k ps \<Longrightarrow> q k ps"
    and "<P> c <\<lambda>k. (X * (\<exists>\<^sub>A ps. Ra \<mapsto>\<^sub>a ps * \<up>(p k ps))) * F>"
  shows "<P> c <\<lambda>k. \<exists>\<^sub>A ps. Ra \<mapsto>\<^sub>a ps * \<up>(q k ps) * true>"
  by (rule ht_cons_post[OF assms(2)]) (sep_auto intro: assms(1))

end

text \<open>The graph given by the arrays of the tails and of the heads of its edges.\<close>

locale bfs_csr_arrays =
  fixes n :: nat and fs :: "nat list" and ts :: "nat list" and ss :: "nat list"
  assumes ts_length: "length ts = length fs"
    and fs_bound: "i < length fs \<Longrightarrow> fs ! i < n" and ts_bound: "i < length fs \<Longrightarrow> ts ! i < n"
    and srcs_distinct: "distinct ss" and srcs_nonempty: "ss \<noteq> []"
    and srcs_in_graph: "set ss \<subseteq> dVs (set (zip fs ts))"
begin

abbreviation es :: "(nat \<times> nat) list" where
  "es \<equiv> zip fs ts"

lemma es_conv: "es = map (\<lambda>i. (fs ! i, ts ! i)) [0..<length fs]"
  by (rule nth_equalityI) (simp_all add: ts_length)

sublocale bfs_csr n es ss
proof (unfold_locales)
  fix u v
  assume "(u, v) \<in> set es"
  then obtain i where "i < length fs" "u = fs ! i" "v = ts ! i"
    unfolding in_set_zip by auto
  then show "u < n \<and> v < n"
    using fs_bound ts_bound by simp
qed (rule srcs_distinct srcs_nonempty srcs_in_graph)+

interpretation inst: BFS_lists_instance where is_visited_set = bset_assn
  and visited_memb = bset_memb and distinct_ins = bset_ins and iterate_neighbourhood = bfs_csr_nbs
  and graph_assn = bcsr_assn and G = "build_nhlists es" and Gi = Gi and srcs = "rev ss" and N = n
  and Fr = Fr and Bf = Bf and Da = Da and Pa = Pa for Gi Fr Bf Da Pa
  using BFS_subprocedures_lists_bcsr Vs_bound
  by (auto intro!: BFS_lists_instance.intro BFS_lists_instance_axioms.intro)

text \<open>The CSR: the counting sort runs over the positions of the edges in the input arrays, with
      the tails as keys and the heads as stored values.\<close>

sublocale inp: csr_buildup "range_next (length fs)" "range_seq (length fs)" "\<lambda>_. True" "(!) fs" n 0
  by unfold_locales
     (auto simp: range_next_def range_seq_def upt_conv_Cons fs_bound split: if_splits)

sublocale ci: imp_csr_buildup "range_next (length fs)" "range_seq (length fs)" "\<lambda>_. True" "(!) fs" n 0
    pos_has_next pos_cur pos_adv pos_tail pos_head "(!) ts" "\<lambda>s si. si = s"
    "\<lambda>(Fa, Ta). Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts"
proof (unfold_locales, goal_cases)
  case (1 s si c) then show ?case
    by (cases c) (sep_auto simp: pos_has_next_def range_next_def)
next
  case (2 s si e s' c) then show ?case
    by (cases c) (sep_auto simp: pos_cur_def range_next_def split: if_splits)
next
  case (3 s si e s' c) then show ?case
    by (cases c) (sep_auto simp: pos_adv_def range_next_def split: if_splits)
next
  case (4 e c) then show ?case
    by (cases c) (sep_auto simp: pos_tail_def range_seq_def)
next
  case (5 e c) then show ?case
    using ts_length by (cases c) (sep_auto simp: pos_head_def range_seq_def)
qed

lemma nbrs_blk: "nbrs es v = map ((!) ts) (inp.blk v)"
  unfolding nbrs_def inp.blk_def inp.es_def range_seq_def es_conv
  by (simp add: filter_map comp_def)

lemma bcsr_rel_build: "bcsr_rel (build_nhlists es) inp.B_spec (map ((!) ts) inp.E_spec)"
proof -
  have nb: "(case build_nhlists es v of None \<Rightarrow> [] | Some vs \<Rightarrow> vs) = nbrs es v" for v
    by (simp add: build_nhlists_def)
  have out: "nbrs es v = []" if "n \<le> v" for v
    using es_bound that unfolding nbrs_def by (fastforce simp: filter_empty_conv)
  have blk: "nths (map ((!) ts) inp.E_spec) {inp.B_spec ! v..<inp.B_spec ! Suc v} = nbrs es v"
    if "v < n" for v
    using inp.csr_block[OF that]
    by (simp add: nths_intervall_strict_as_drop_and_take drop_take take_map drop_map nbrs_blk)
  have mono: "inp.B_spec ! v \<le> inp.B_spec ! Suc v \<and> inp.B_spec ! Suc v \<le> length (map ((!) ts) inp.E_spec)"
    if "v < n" for v
    using that inp.start_mono[of v "Suc v"] inp.start_mono[of "Suc v" n]
    by (simp add: inp.B_spec_nth inp.start_n inp.length_E_spec)
  show ?thesis
    unfolding bcsr_rel_def inp.length_B_spec nb
    using blk mono out by simp
qed

lemma bfs_csr_build_raw_rule:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts> bfs_csr_build n (Fa, Ta) 0
   <\<lambda>(Ba, Ea). Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Ba \<mapsto>\<^sub>a inp.B_spec * Ea \<mapsto>\<^sub>a map ((!) ts) inp.E_spec>"
  using ci.csr_build_imp_rule[of "(Fa, Ta)" 0] by (simp add: bfs_csr_build_def)

lemma bfs_csr_build_rule:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts> bfs_csr_build n (Fa, Ta) 0
   <\<lambda>Gi. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * bcsr_assn (build_nhlists es) Gi>"
  by (rule ht_cons_post[OF bfs_csr_build_raw_rule])
     (sep_auto simp: bcsr_assn_def intro: bcsr_rel_build split: prod.splits)

text \<open>The allocations of @{const bfs_csr_run} establish the precondition of the BFS on the
      instance.\<close>

lemma bfs_csr_run_rule:
  assumes Q: "\<And>Gi Vi Fr Bf Da Pa.
     <bset_assn (BFS_subprocedures_lists.Vs (build_nhlists es)) (set []) Vi *
      inst.imp_src_assn (Suc n) Fr Bf (build_nhlists es) (rev ss) (Fr, length ss, Bf) *
      inst.imp_dist_assn n Da (build_nhlists es) id Da * inst.imp_par_assn n Pa (build_nhlists es) id Pa *
      bcsr_assn (build_nhlists es) Gi>
       bfs_visited_dists_parents Gi Vi (Fr, length ss, Bf) Da Pa <Q Gi Fr Bf Da Pa>"
  shows "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Sa \<mapsto>\<^sub>a ss> bfs_csr_run n Fa Ta Sa
         <\<lambda>r. (\<exists>\<^sub>A Gi Fr Bf Da Pa. Q Gi Fr Bf Da Pa r) * (Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Sa \<mapsto>\<^sub>a ss) * true>"
proof-
  let ?V = "BFS_subprocedures_lists.Vs (build_nhlists es)"
  let ?FL = "ss @ drop (length ss) (replicate (Suc n) (0::nat))"
  let ?I = "Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Sa \<mapsto>\<^sub>a ss"
  have cV: "card ?V \<le> n"
    using card_mono[OF finite_lessThan Vs_bound] by simp
  have cS: "length ss \<le> card ?V"
    using card_mono[OF finite_subset[OF Vs_bound finite_lessThan] ss_in_graph[folded \<E>_def, folded Vs_build]]
          distinct_card[OF ss_distinct] by simp
  have sV: "set ss \<subseteq> ?V"
    using ss_in_graph unfolding Vs_build \<E>_def .
  have lenF: "length ?FL = Suc n"
    using cV cS by simp
  have lens: "length (replicate (Suc n) (0::nat)) = Suc n" "length (map id [0..<n]) = n"
    by simp_all
  have b: "card ?V < length ?FL" "card ?V < length (replicate (Suc n) (0::nat))"
          "length ss < length ?FL" "take (length ss) ?FL = ss"
    unfolding lenF length_replicate using cV cS by simp_all
  have ids: "\<forall>i \<in> ?V. i < length (map id [0..<n]) \<and> id i = map id [0..<n] ! i"
  proof
    fix i assume "i \<in> ?V"
    then have "i < n"
      by (rule lessThan_iff[THEN iffD1, OF subsetD[OF Vs_bound]])
    then show "i < length (map id [0..<n]) \<and> id i = map id [0..<n] ! i"
      unfolding list.map_id by simp
  qed
  have main:
    "<bset_assn ?V {} Vi * (Fr \<mapsto>\<^sub>a ?FL * Bf \<mapsto>\<^sub>a replicate (Suc n) (0::nat)) *
      Da \<mapsto>\<^sub>a map id [0..<n] * Pa \<mapsto>\<^sub>a map id [0..<n] * bcsr_assn (build_nhlists es) Gi * ?I>
       bfs_visited_dists_parents Gi Vi (Fr, length ss, Bf) Da Pa
     <\<lambda>r. (\<exists>\<^sub>A Gi Fr Bf Da Pa. Q Gi Fr Bf Da Pa r) * ?I * true>" for Gi Vi Fr Bf Da Pa
    by (rule ht_cons[OF _ _ ht_frame[OF Q[unfolded list.set(1)], where R = ?I]])
       (intro ent_star_mono ent_refl inst.imp_src_assn_intro[OF b sV lenF lens(1)]
              inst.imp_dist_assn_intro[OF ids lens(2)] inst.imp_par_assn_intro[OF ids lens(2)], sep_auto)
  show ?thesis
    unfolding bfs_csr_run_def
    using cV cS by (sep_auto heap: bfs_csr_build_rule copy_prefix_imp_rule bset_empty_rule[OF Vs_bound] main)
qed

text \<open>The final correctness theorem: the program returns a visited, a distance and a parent
      array with these properties.\<close>

theorem bfs_csr_run_correct:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Sa \<mapsto>\<^sub>a ss> bfs_csr_run n Fa Ta Sa
   <\<lambda>(Vi, Da, Pa). \<exists>\<^sub>A vs ds ps. Vi \<mapsto>\<^sub>a vs * Da \<mapsto>\<^sub>a ds * Pa \<mapsto>\<^sub>a ps * \<up>(bfs_arrays vs ds ps) * true>"
proof (rule ht_cons[OF ent_refl _ bfs_csr_run_rule[OF inst.imp_bfs.visited_dists_parents_imp_correct[OF
         BFS_axiom, unfolded code_eqs digraph_abs_build set_rev, folded \<S>_def]]], goal_cases)
  case (1 r)
  obtain Vi Da Pa where r: "r = (Vi, Da, Pa)"
    by (cases r)
  show ?case
    unfolding r prod.case
    by (rule ent_true_drop(1), rule ent_true_drop(1), intro ent_ex_preI, unfold ent_pure_pre_iff,
        intro impI, elim conjE, rule ent_true_drop(2), rule bfs_arrays_ent)
qed

text \<open>Path reconstruction: after the BFS, @{const bfs_path} writes a shortest path from the
      sources to any reachable vertex @{term v}, reversed, into the first cells of an array with
      at least @{term n} cells and returns its length.\<close>

theorem bfs_csr_path_correct:
  assumes v: "\<exists>u \<in> \<S>. \<exists>q. vwalk_bet \<E> u q v" and r: "n \<le> length r"
  shows "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Sa \<mapsto>\<^sub>a ss * Ra \<mapsto>\<^sub>a r>
           do { (Vi, Da, Pa) \<leftarrow> bfs_csr_run n Fa Ta Sa; bfs_path Da Pa Ra v }
         <\<lambda>k. \<exists>\<^sub>A ps. Ra \<mapsto>\<^sub>a ps * \<up>(length ps = length r \<and>
              (\<exists>u \<in> \<S>. vwalk_bet \<E> u (rev (take k ps)) v \<and> enat (k - 1) = distance_set \<E> \<S> v)) * true>"
proof-
  have vis: "v \<in> set (BFS_dist_state.visited (inst.imp_bfs.BFS_par_impl inst.imp_bfs.initial_par_state))"
    using v unfolding inst.imp_bfs.BFS_par_correct(1)[OF BFS_axiom refl] digraph_abs_build set_rev \<S>_def .
  have card: "card (dVs (inst.Graph.digraph_abs (build_nhlists es))) \<le> length r"
    using card_mono[OF finite_lessThan Vs_bound] r unfolding Vs_build digraph_abs_build by simp
  note pth = inst.imp_bfs.path_imp_correct[OF BFS_axiom refl vis card, unfolded code_eqs
               digraph_abs_build set_rev, folded \<S>_def]
  show ?thesis
    apply (rule run_then_path[OF bfs_csr_run_rule[OF inst.imp_bfs.visited_dists_parents_imp_rule[unfolded code_eqs]]])
    apply (simp only: prod.case)
    apply (rule path_post_weaken[OF _ ht_cons_pre[OF frame_last3 ht_frame[OF pth]]])
    apply blast
    done
qed

end

section \<open>Running the Code\<close>

text \<open>A test harness. \<open>bfs_query\<close> asks the arrays for a vertex \<open>v\<close>: if it is visited, it
      returns its distance and writes its path, reversed, into the array \<open>Ra\<close> the caller provides,
      together with the path length; otherwise it returns @{const None}. The \<open>code\<close> antiquotation
      compiles both into the running ML session; applying a @{typ "'a Heap"} computation to
      \<open>()\<close> runs it.\<close>

definition bfs_query where
  "bfs_query Vi Da Pa Ra v = do {
     b \<leftarrow> Array.nth Vi v;
     if b then do {
       d \<leftarrow> Array.nth Da v;
       k \<leftarrow> bfs_path Da Pa Ra v;
       return (Some (d, k)) }
     else return None }"

text \<open>A graph with the sources 0 and 5, given by the arrays of tails and heads. A path is read
      from the first \<open>k\<close> entries of the path array and reversed, so it is printed from its source to
      the vertex. The path array is allocated once and reused for every query. Vertex 6 is
      unreachable: its query returns @{const None}.\<close>

ML_val \<open>
  let
    val nat = @{code nat_of_integer}
    val i = @{code integer_of_nat}
    val n = 7
    val es = [(0, 1), (0, 2), (1, 2), (2, 3), (1, 3), (5, 4), (4, 3), (3, 4), (6, 0)]
    val fa = Array.fromList (map (fn (u, _) => nat u) es)
    val ta = Array.fromList (map (fn (_, v) => nat v) es)
    val sa = Array.fromList (map nat [0, 5])
    val (vi, (da, pa)) = @{code bfs_csr_run} (nat n) fa ta sa ()
    val ra = Array.array (n, nat 0)
    fun query v =
      (case @{code bfs_query} vi da pa ra (nat v) () of
         NONE => (v, NONE)
       | SOME (d, k) => (v, SOME (i d, rev (List.tabulate (i k, fn j => i (Array.sub (ra, j)))))))
  in
    map query [0, 1, 2, 3, 4, 5, 6]
  end
\<close>

end
