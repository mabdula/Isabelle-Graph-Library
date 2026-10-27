theory Matroid_Intersection_Exchange_Graph_Imp
  imports Matroid_Intersection_Exchange_Graph_CSR Matroid_Intersection_Imp_Loop Exchange_Candidates_Imp
          Data_Structures.More_Lists
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

text \<open>The BFS of the library (@{locale bfs_iterator_arrays}) on the graph of an edge list \<open>E\<close>
  below \<open>n\<close>, run with an iterator \<open>nbs\<close> on a graph handle that walks the neighbours of a
    vertex
  in \<open>E\<close> (e.g. the CSR neighbours of a constant larger graph, skipping the edges outside \<open>E\<close>).
  Here, the path is read in the form of @{const path_assn}, and the work arrays are kept with
  arbitrary contents.\<close>

lemma len_fill_rule: "<len_assn n a> fill_range_imp f n a <\<lambda> r. a \<mapsto>\<^sub>a map f [0..<n] * \<up>(r =
    a)>"
  unfolding len_assn_def
  by (rule ht_ex_pre) (sep_auto heap: fill_range_imp_rule)

lemma clear_len: "<len_assn n Vi> bool_array_set_clear_imp n Vi <\<lambda> _. bool_array_set_assn n {} Vi>"
  by (rule ht_cons_post[OF bool_array_set_clear_rule]) sep_auto

lemma fill_len: "<len_assn n a> fill_range_imp f n a <\<lambda> _. a \<mapsto>\<^sub>a map f [0..<n]>"
  by (rule ht_cons_post[OF len_fill_rule]) sep_auto

lemma parr_len: "parr_assn n Ra = len_assn n Ra"
  unfolding parr_assn_def len_assn_def
  by (rule refl)

lemma path_None: "path_assn n None None Ra = parr_assn n Ra"
  unfolding path_assn_def parr_assn_def
  by simp

text \<open>The work arrays of the BFS, with arbitrary contents.\<close>

definition "work_assn n Vi Fr Bf Da Pa =
  len_assn n Vi * len_assn (Suc n) Fr * len_assn (Suc n) Bf * len_assn n Da * len_assn n Pa"

locale csr_filtered_bfs = bfs_iterator_arrays n "nbrs_map E" nbs ga
  for n :: nat and E :: "(nat \<times> nat) list" and nbs :: "'gh \<Rightarrow> bfs_nbs_iterator" and ga :: "'gh
    \<Rightarrow> assn"
begin

lemma E_bound:
  assumes "(u, v) \<in> set E"
  shows "u < n \<and> v < n"
  using G_bound[unfolded nbrs_map_edges] assms
  by (auto dest: dVsI(1) dVsI(2))

context
  fixes ss
  assumes b: "bfs_sources ss"
begin

lemma path_rule:
  assumes "find (\<lambda> y. y \<in> set (BFS_dist_state.visited (fin ss))) ts = Some t" "length rl = n"
  shows "<parent_array.pa_parent_assn n (BFS_par_state.parent (fin ss)) Pa * Ra \<mapsto>\<^sub>a rl>
           bfs_path Pa Ra t
         <\<lambda> k. parent_array.pa_parent_assn n (BFS_par_state.parent (fin ss)) Pa *
               path_assn n (Some (rev (parent_array.pa_get_path n (BFS_par_state.parent (fin ss)) t)))
                 (Some k) Ra>"
proof-
  note t = find_SomeD[OF assms(1)]
  note card = card_Vs[unfolded Vs_G assms(2)[symmetric]]
  have len: "length (parent_array.pa_get_path n (BFS_par_state.parent (fin ss)) t) \<le> n"
    using fin_path_length[OF b] card assms(2) t by force
  show ?thesis
    unfolding path_assn_def option.case(2)
    by (rule ht_cons[OF _ _ path_rule[OF b t(1) card]]) 
       (use len assms(2) in sep_auto)+
qed

lemma bfs_len_rule:
  assumes "length fl = Suc n" "take (length ss) fl = ss"
  shows "<len_assn (Suc n) Bf * (bool_array_set_assn n {} Vi * Fr \<mapsto>\<^sub>a fl * Da \<mapsto>\<^sub>a map id
    [0..<n] *
          len_assn n Pa * ga Gh)>
           bfs_visited_dists_parents (nbs Gh) Vi (Fr, length ss, Bf) Da Pa
         <\<lambda> _. ga Gh * bool_array_set_assn n (set (BFS_dist_state.visited (fin ss))) Vi *
            BFS_subprocedures_lists.imp_dist_assn n Da (nbrs_map E) (BFS_dist_state.dists (fin ss)) Da *
            parent_array.pa_parent_assn n (BFS_par_state.parent (fin ss)) Pa *
            len_assn (Suc n) Fr * len_assn (Suc n) Bf>"
proof(rule pull_len, goal_cases)
  case (1 bl)
  show ?case
    by (rule ht_cons_prec[OF _ _ bfs_rule[OF b assms 1]])
       (simp only: star_aci, rule ent_refl, unfold ent_pure_pre_iff, rule impI, rule ent_refl)
qed

lemma path_len_rule:
  assumes "find (\<lambda> y. y \<in> set (BFS_dist_state.visited (fin ss))) ts = Some t"
  shows "<parr_assn n Ra * parent_array.pa_parent_assn n (BFS_par_state.parent (fin ss)) Pa>
           bfs_path Pa Ra t
         <\<lambda> k. parent_array.pa_parent_assn n (BFS_par_state.parent (fin ss)) Pa *
               path_assn n (Some (rev (parent_array.pa_get_path n (BFS_par_state.parent (fin ss)) t)))
                 (Some k) Ra>"
  unfolding parr_len
proof(rule pull_len, goal_cases)
  case (1 rl)
  show ?case
    by (rule ht_cons_pre[OF _ path_rule[OF assms 1]]) (simp only: star_aci, rule ent_refl)
qed

end

lemma work_ent:
  "bool_array_set_assn n V Vi * BFS_subprocedures_lists.imp_dist_assn n Da (nbrs_map E) d di *
   parent_array.pa_parent_assn n p Pa * len_assn (Suc n) Fr * len_assn (Suc n) Bf
   \<Longrightarrow>\<^sub>A work_assn n Vi Fr Bf Da Pa"
  unfolding work_assn_def
  by (rule ent_trans[OF ent_star_mono[OF ent_star_mono[OF ent_star_mono[OF ent_star_mono[OF
             bool_array_set_len dist_len] par_len] ent_refl] ent_refl]])
     (simp only: star_aci, rule ent_refl)

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

definition "filt_imp P Si u fi = (\<lambda> v a. do { ok \<leftarrow> P Si u v; if ok then fi v a else return a })"

text \<open>The iterator over the exchange neighbours, on the solution handle and the CSR.\<close>

definition xnbs :: "'si \<times> (nat array \<times> nat array) \<Rightarrow> nat \<Rightarrow>
                     (nat \<Rightarrow> 'acc \<Rightarrow> 'acc Heap) \<Rightarrow> 'acc \<Rightarrow> 'acc Heap" where
  "xnbs Gh u fi acc = (case Gh of (Si, Gc) \<Rightarrow>
     if u < n then do {
       b \<leftarrow> smemb_imp u Si;
       if b then csr_fold_imp Gc u (filt_imp nb1_imp Si u fi) acc
       else do { t \<leftarrow> ins2_imp Si u;
                 if t then return acc else csr_fold_imp Gc u (filt_imp nb2_imp Si u fi) acc } }
     else return acc)"

text \<open>The BFS of the library with this iterator. The iterator is fixed at code generation time by
  the code equations of the specialised procedures, so the generated code calls it directly.\<close>

definition "x_inner Gh = bfs_inner_loop (xnbs Gh)"

definition "x_outer Gh = bfs_outer_loop (xnbs Gh)"

definition "xround Gh = bfs_round (xnbs Gh)"

definition "x_loop Gh = bfs_loop (xnbs Gh)"

definition "bfs_run Gh = bfs_visited_dists_parents (xnbs Gh)"

lemmas x_inner_code = bfs_sub_code.inner_loop.simps[of "xnbs Gh" for Gh, folded x_inner_def]

lemmas x_outer_code =
  bfs_sub_code.outer_loop.simps[of "xnbs Gh" for Gh, folded x_outer_def x_inner_def]

lemmas xround_code =
  bfs_sub_code.next_frontier_current_parents_imp.simps[of "xnbs Gh" for Gh, folded xround_def x_outer_def]

lemmas x_loop_code = bfs_code.BFS_par_imp.simps[of "xnbs Gh" for Gh, folded x_loop_def xround_def]

lemmas bfs_run_code =
  bfs_code.visited_dists_parents_imp_def[of "xnbs Gh" for Gh, folded bfs_run_def x_loop_def]

definition "has_nb_imp Gc Si y = xnbs (Si, Gc) y (\<lambda> _ _. return True) False"

text \<open>Sources and targets (elements outside the solution insertable in the first resp. second
  matroid), sources that are targets, sources having an exchange edge, and visited targets.\<close>

definition "s_imp Si y = do { b \<leftarrow> smemb_imp y Si; if b then return False else ins1_imp Si y }"

definition "t_imp Si y = do { b \<leftarrow> smemb_imp y Si; if b then return False else ins2_imp Si y }"

definition "st_imp Si y = do { s \<leftarrow> s_imp Si y; if s then ins2_imp Si y else return False }"

definition "is_src_imp Gc Si y = do { s \<leftarrow> s_imp Si y; if s then has_nb_imp Gc Si y else return False }"

definition "is_tgt_imp Si Vi y = do { v \<leftarrow> Array.nth Vi y; if v then t_imp Si y else return False }"

text \<open>One search: a source that is a target is a path on its own. Otherwise, the sources having
  an exchange edge are written into the frontier array, the visited and distance arrays
  are reset in place (the BFS initialises the parent array itself), the BFS runs, and the first visited target gives
    the path.\<close>

definition "tail_imp Si Ra r = (case r of (Vi', Da', Pa') \<Rightarrow> do {
   t \<leftarrow> find_range_imp (is_tgt_imp Si Vi') 0 n;
   (case t of
      None \<Rightarrow> return None
    | Some t \<Rightarrow> do { l \<leftarrow> bfs_path Pa' Ra t; return (Some l) }) })"

definition "round_imp Gc Vi Fr Bf Da Pa Si Ra k = do {
   bool_array_set_clear_imp n Vi;
   fill_range_imp id n Da;
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
  unweighted_intersection_exchange_csr where set_insert = "Set.insert :: nat \<Rightarrow> nat set \<Rightarrow> nat
    set"
    and set_delete = "\<lambda> x X. X - {x}" and to_set = "\<lambda> X. X" and set_invar = finite
    and set_empty = "{}" and set_memb = "\<lambda> x X. x \<in> X" and carrier_list = "[0..<n]"
    and carrier = "{0..<n}" +
  o1: exchange_oracle_imp n orcl_prep1 ins_orcl1 exch_orcl1 sol_assn ins1_imp exch1_imp ost1 +
  o2: exchange_oracle_imp n orcl_prep2 ins_orcl2 exch_orcl2 sol_assn ins2_imp exch2_imp ost2
  for n smemb_imp ins1_imp exch1_imp ins2_imp exch2_imp sol_assn sins_imp sdel_imp ost1 ost2 +
  fixes es0 :: "(nat \<times> nat) list"
  assumes es0_bound: "(u, v) \<in> set es0 \<Longrightarrow> u < n \<and> v < n"
    and es0_sorted: "sorted_wrt (<) (nbrs es0 u)"
    and es0_cover1: "\<lbrakk>finite X; X \<subseteq> {0..<n}; indep1 X; indep2 X; u < n; v < n; u \<in> X; v \<notin>
      X;
                     \<not> ins_orcl1 (orcl_prep1 X) v; exch_orcl1 (orcl_prep1 X) u v\<rbrakk> \<Longrightarrow> (u,
                       v) \<in> set es0"
    and es0_cover2: "\<lbrakk>finite X; X \<subseteq> {0..<n}; indep1 X; indep2 X; u < n; v < n; u \<notin> X; v \<in>
      X;
                     \<not> ins_orcl2 (orcl_prep2 X) u; exch_orcl2 (orcl_prep2 X) v u\<rbrakk> \<Longrightarrow> (u,
                       v) \<in> set es0"
begin

subsubsection \<open>The Exchange Neighbours\<close>

definition "S0 X = {y. y < n \<and> y \<notin> X \<and> ins_orcl1 (orcl_prep1 X) y}"
definition "T0 X = {y. y < n \<and> y \<notin> X \<and> ins_orcl2 (orcl_prep2 X) y}"

definition "allowed1 X u v = (v \<notin> X \<and> \<not> ins_orcl1 (orcl_prep1 X) v \<and> exch_orcl1 (orcl_prep1 X) u
    v)"
definition "allowed2 X u v = (v \<in> X \<and> exch_orcl2 (orcl_prep2 X) v u)"
definition "exch_nb X u v =
  (if u \<in> X then allowed1 X u v else \<not> ins_orcl2 (orcl_prep2 X) u \<and> allowed2 X u v)"

abbreviation "EE X \<equiv> csr.exch_edges (csr.exch_ctx X)"

lemma ctx_parts:
  "ctx_o1 (csr.exch_ctx X) = orcl_prep1 X" "ctx_o2 (csr.exch_ctx X) = orcl_prep2 X"
  "ctx_notX (csr.exch_ctx X) = filter (\<lambda> y. y \<notin> X) [0..<n]"
  "ctx_inX (csr.exch_ctx X) = filter (\<lambda> y. y \<in> X) [0..<n]"
  by (simp_all add: csr.exch_ctx_def Let_def)

lemma ctx_ST: "ctx_S (csr.exch_ctx X) = S0 X" "ctx_T (csr.exch_ctx X) = T0 X"
  by (auto simp: csr.exch_ctx_def Let_def csr.cache(2) subset_iff S0_def T0_def)

lemma in_ST:
  "csr.in_S (csr.exch_ctx X) = (\<lambda> y. y \<in> S0 X)" "csr.in_T (csr.exch_ctx X) = (\<lambda> y. y \<in> T0 X)"
  by (simp_all add: fun_eq_iff csr.in_S_def csr.in_T_def ctx_ST)

text \<open>The neighbours of an element in the exchange graph, in increasing order.\<close>

lemma nbrs_EE:
  assumes "u < n"
  shows "nbrs (EE X) u = filter (exch_nb X u) [0..<n]"
  using assms
  by (auto simp: csr.exch_edges_def nbrs_append nbrs_concat_Pair ctx_parts in_ST concat_if_dist
      csr.out1_def csr.out2_def exch_nb_def allowed1_def allowed2_def S0_def T0_def filter_filter
      intro!: filter_cong split: if_splits)

context
  fixes X
  assumes X: "finite X" "X \<subseteq> {0..<n}" "indep1 X" "indep2 X"
begin

lemma EE_set: "set (EE X) = A1 X \<union> A2 X"
  using csr.exchange_graph[OF X] unfolding csr.build_graph(4) .

lemma EE_bound: "(u, v) \<in> set (EE X) \<Longrightarrow> u < n \<and> v < n"
  using X dVs_A1A2_carrier[of X]
  unfolding EE_set
  by (auto dest: dVsI(1) dVsI(2))

text \<open>Filtering the CSR neighbours gives the exchange neighbours, since both lists are
  ascending.\<close>

lemma exch_nb_es0:
  "\<lbrakk>u < n; v < n; exch_nb X u v\<rbrakk> \<Longrightarrow> (u, v) \<in> set es0"
  by (cases "u \<in> X")
     (auto simp: exch_nb_def allowed1_def allowed2_def intro: es0_cover1[OF X] es0_cover2[OF X])

lemma nbrs_es0:
  assumes "u < n"
  shows "filter (exch_nb X u) (nbrs es0 u) = nbrs (EE X) u"
  unfolding nbrs_EE[OF assms]
  by (intro strict_sorted_equal sorted_wrt_filter es0_sorted)
     (auto simp: sorted_wrt_upt mem_nbrs dest: es0_bound intro: exch_nb_es0[OF assms])

lemma nbrs_EE_out: "\<not> u < n \<Longrightarrow> nbrs (EE X) u = []"
  unfolding nbrs_def
  using EE_bound
  by (fastforce simp: filter_empty_conv)

end

subsubsection \<open>The Iterator\<close>

text \<open>The CSR of the candidate graph: the block array and the neighbour array.\<close>

sublocale cand: csr_concat "nbrs es0" n .

definition "gxs X Si Gc = sol_assn X Si * ost1 * ost2 *
  (case Gc of (Ba, Ga) \<Rightarrow> Ba \<mapsto>\<^sub>a map (csr_start (nbrs es0)) [0..<Suc n] *
     Ga \<mapsto>\<^sub>a csr_entries (nbrs es0) n)"


text \<open>(A triple must not start with \<open><sol_assn\<close> here, which is read as another token.)\<close>

lemma nb1_rule:
  "\<lbrakk>u < n; v < n\<rbrakk> \<Longrightarrow>
   <ost1 * ost2 * sol_assn X Si * Q> nb1_imp Si u v
   <\<lambda> r. ost1 * ost2 * sol_assn X Si * Q * \<up>(r = allowed1 X u v)>"
  unfolding nb1_imp_def allowed1_def
  by (sep_auto heap: smemb_rule o1.ins_imp o1.exch_imp)

lemma nb2_rule:
  "\<lbrakk>u < n; v < n\<rbrakk> \<Longrightarrow>
   <ost1 * ost2 * sol_assn X Si * Q> nb2_imp Si u v
   <\<lambda> r. ost1 * ost2 * sol_assn X Si * Q * \<up>(r = allowed2 X u v)>"
  unfolding nb2_imp_def allowed2_def
  by (sep_auto heap: smemb_rule o2.exch_imp)

lemma csr_nbs_filt_rule:
  assumes "u < n"
    and "\<And> v Q. v < n \<Longrightarrow> <ost1 * ost2 * sol_assn X Si * Q> P Si u v
                                   <\<lambda> r. ost1 * ost2 * sol_assn X Si * Q * \<up>(r = p v)>"
    and "\<And> acc acci x. x \<in> set (filter p (nbrs es0 u)) \<Longrightarrow>
               <A acc acci * F> fi x acci <\<lambda> r. A (f x acc) r * F>"
  shows "<gxs X Si Gc * A acc acci * F> csr_fold_imp Gc u (filt_imp P Si u fi) acci
         <\<lambda> r. gxs X Si Gc * F * A (foldl (\<lambda> acc x. f x acc) acc (filter p (nbrs es0 u))) r>"
proof-
  let ?R = "ost1 * ost2 * sol_assn X Si"
  let ?g = "\<lambda> x a. if p x then f x a else a"
  have step: "<A a ai * (F * ?R)> filt_imp P Si u fi x ai <\<lambda> r. A (?g x a) r * (F * ?R)>"
    if "x \<in> cand.csr_abstract c u" for a ai x c
  proof-
    note xs = that[unfolded cand.csr_list_set[symmetric] cand.csr_list_blk[OF assms(1)]]
    have "x < n"
      using es0_bound xs unfolding mem_nbrs
      by blast
    note px = assms(2)[of x "A a ai * F", OF this]
    have p: "<A a ai * (F * ?R)> P Si u x <\<lambda> ok. A a ai * (F * ?R) * \<up>(ok = p x)>"
      by (rule ht_cons_pre[OF _ ht_cons_post[OF px]]) sep_auto+
    show ?thesis
    proof(cases "p x")
      case True
      have "x \<in> set (filter p (nbrs es0 u))"
        using xs True
        by simp
      note fi' = ht_frame[OF assms(3)[OF this, of a ai], where R = ?R, simplified mult.assoc]
      show ?thesis
        unfolding filt_imp_def
        by (rule ht_bind[OF p], rule ht_pure_pre) (simp add: True mult.assoc fi')
    next
      case False
      show ?thesis
        unfolding filt_imp_def
        by (rule ht_bind[OF p], rule ht_pure_pre) (sep_auto simp: False)
    qed
  qed
  obtain Ba Ga where Gc: "Gc = (Ba, Ga)"
    by (cases Gc)
  note e = cand.csr_fold_def[of c u "?g" acc for c,
    unfolded cand.csr_list_blk[OF assms(1)] foldl_filter_if]
  have "<cand.csr_blocks_assn undefined Gc * (A acc acci * (F * ?R))>
             csr_fold_imp Gc u (filt_imp P Si u fi) acci
           <\<lambda> r. cand.csr_blocks_assn undefined Gc *
                 (A (cand.csr_fold undefined u ?g acc) r * (F * ?R))>"
    by (rule cand.csr_fold_imp_refine[where acc_assn = "\<lambda> a ai. A a ai * (F * ?R)"])
       (use assms(1) in simp, rule step)
  then show ?thesis
    unfolding gxs_def Gc prod.case cand.csr_blocks_assn_def e
    by (rule ht_cons[rotated 2]) sep_auto+
qed

lemma xnbs_rule:
  assumes "finite X" "X \<subseteq> {0..<n}" "indep1 X" "indep2 X"
    and "\<And> acc acci x. x \<in> set (nbrs (EE X) u) \<Longrightarrow>
               <A acc acci * F> fi x acci <\<lambda> r. A (f x acc) r * F>"
  shows "<gxs X Si Gc * A acc acci * F> xnbs (Si, Gc) u fi acci
         <\<lambda> r. gxs X Si Gc * F * A (foldl (\<lambda> acc x. f x acc) acc (nbrs (EE X) u)) r>"
proof(cases "u < n")
  case False
  show ?thesis
    unfolding xnbs_def prod.case if_not_P[OF False] nbrs_EE_out[OF assms(1-4) False] foldl_Nil
    by sep_auto
next
  case True
  have m: "<gxs X Si Gc * A acc acci * F> smemb_imp u Si
           <\<lambda> b. gxs X Si Gc * A acc acci * F * \<up>(b = (u \<in> X))>"
    unfolding gxs_def
    using True
    by (sep_auto heap: smemb_rule)
  show ?thesis
  proof(cases "u \<in> X")
    case uX: True
    note e = nbrs_es0[OF assms(1-4) True, unfolded exch_nb_def, simplified uX, simplified]
    note b = csr_nbs_filt_rule[where X = X and Si = Si and P = nb1_imp and p = "allowed1 X u"
          and A = A and f = f, OF True nb1_rule[OF True] assms(5)[folded e], unfolded e]
    show ?thesis
      unfolding xnbs_def prod.case if_P[OF True]
      by (rule ht_bind[OF m], rule ht_pure_pre) (simp add: uX b)
  next
    case nX: False
    have i: "<gxs X Si Gc * A acc acci * F> ins2_imp Si u
             <\<lambda> t. gxs X Si Gc * A acc acci * F * \<up>(t = ins_orcl2 (orcl_prep2 X) u)>"
      unfolding gxs_def
      using True
      by (sep_auto heap: o2.ins_imp)
    show ?thesis
    proof(cases "ins_orcl2 (orcl_prep2 X) u")
      case it: True
      note e = nbrs_es0[OF assms(1-4) True, unfolded exch_nb_def, simplified nX it, simplified, symmetric]
      show ?thesis
        unfolding xnbs_def prod.case if_P[OF True] e foldl_Nil
        by (rule ht_bind[OF m], rule ht_pure_pre)
           (simp add: nX, rule ht_bind[OF i], rule ht_pure_pre, sep_auto simp: it)
    next
      case nit: False
      note e = nbrs_es0[OF assms(1-4) True, unfolded exch_nb_def, simplified nX nit, simplified]
      note b = csr_nbs_filt_rule[where X = X and Si = Si and P = nb2_imp and p = "allowed2 X u"
          and A = A and f = f, OF True nb2_rule[OF True] assms(5)[folded e], unfolded e]
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
  case 1
  have "fst e < n" "snd e < n" if "e \<in> set (EE X)" for e
    using EE_bound[OF X, of "fst e" "snd e"] that
    by simp_all
  then show ?case
    unfolding nbrs_map_edges dVs_eq
    by (intro Un_least image_subsetI) (simp_all only: lessThan_iff)
next
  case 2
  show ?case
    by (rule finite_nbrs_map_dom)
next
  case (3 u A fi f Gh acc acci)
  obtain Si Gc where Gh: "Gh = (Si, Gc)"
    by (cases Gh)
  have r: "<gxs X Si Gc * A acc acci * emp> xnbs (Si, Gc) u fi acci
           <\<lambda> r. gxs X Si Gc * emp * A (foldl (\<lambda> acc x. f x acc) acc (nbrs (EE X) u)) r>"
    by (rule xnbs_rule[OF X]) (simp only: mult_1_right, rule 3(2)[unfolded case_nbrs_map])
  show ?case
    using r unfolding Gh prod.case mult_1_right case_nbrs_map .
qed

subsubsection \<open>The Functional Values\<close>

lemma eq_find:
  "find (\<lambda> y. (y \<notin> X \<and> y \<in> S0 X) \<and> y \<in> T0 X) [0..<n] =
   find (csr.in_T (csr.exch_ctx X)) (csr.srcs (csr.exch_ctx X))"
  by (simp only: csr.srcs_def in_ST ctx_parts filter_filter find_filter)

lemma eq_srcs:
  "filter (\<lambda> y. (y \<notin> X \<and> y \<in> S0 X) \<and>
                 (y \<notin> T0 X \<and> find (\<lambda> x. x \<in> X \<and> exch_orcl2 (orcl_prep2 X) x y) [0..<n]
                   \<noteq> None))
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
           else csr.target_path (nbrs_map (EE X))
                  (filter (csr.has_nb (csr.exch_ctx X)) (csr.srcs (csr.exch_ctx X)))
                  (csr.tgts (csr.exch_ctx X))))"
  by (simp only: csr.augmenting_path_def Let_def)

lemma bfs_ok:
  assumes "filter (csr.has_nb (csr.exch_ctx X)) (csr.srcs (csr.exch_ctx X)) \<noteq> []"
  shows "fb.bfs_sources (filter (csr.has_nb (csr.exch_ctx X)) (csr.srcs (csr.exch_ctx X)))"
  unfolding fb.bfs_sources_def nbrs_map_edges
  using assms csr.srcs(2)[OF X] csr.nb_srcs_dVs[OF X]
  by (auto simp: fb.bfs_sources_def nbrs_map_edges csr.build_graph(4))

lemma nb_char:
  "\<lbrakk>y < n; y \<notin> X\<rbrakk> \<Longrightarrow> (nbrs (EE X) y \<noteq> []) =
     (y \<notin> T0 X \<and> find (\<lambda> x. x \<in> X \<and> exch_orcl2 (orcl_prep2 X) x y) [0..<n] \<noteq> None)"
  by (auto simp: nbrs_EE exch_nb_def allowed2_def T0_def filter_empty_conv find_None_iff)

subsubsection \<open>The Steps of a Search\<close>

lemma s_imp_rule:
  "y < n \<Longrightarrow> <gxs X Si Gc> s_imp Si y <\<lambda> r. gxs X Si Gc * \<up>(r = (y \<notin> X \<and> y \<in>
    S0 X))>"
  unfolding s_imp_def gxs_def S0_def
  by (sep_auto heap: smemb_rule o1.ins_imp)

lemma t_imp_rule:
  "y < n \<Longrightarrow> <gxs X Si Gc> t_imp Si y <\<lambda> r. gxs X Si Gc * \<up>(r = (y \<notin> X \<and> y \<in>
    T0 X))>"
  unfolding t_imp_def gxs_def T0_def
  by (sep_auto heap: smemb_rule o2.ins_imp)

lemma st_imp_rule:
  "y < n \<Longrightarrow> <gxs X Si Gc> st_imp Si y
   <\<lambda> r. gxs X Si Gc * \<up>(r = ((y \<notin> X \<and> y \<in> S0 X) \<and> y \<in> T0 X))>"
  unfolding st_imp_def s_imp_def gxs_def S0_def T0_def
  by (sep_auto heap: smemb_rule o1.ins_imp o2.ins_imp)

lemma find_st_rule:
  "<gxs X Si Gc> find_range_imp (st_imp Si) 0 n
   <\<lambda> r. gxs X Si Gc * \<up>(r = find (csr.in_T (csr.exch_ctx X)) (csr.srcs (csr.exch_ctx X)))>"
  unfolding eq_find[symmetric]
  by (rule find_range_imp_rule, rule st_imp_rule, assumption)

lemma has_nb_rule:
  assumes "y < n"
  shows "<gxs X Si Gc> has_nb_imp Gc Si y <\<lambda> r. gxs X Si Gc * \<up>(r = (nbrs (EE X) y \<noteq> []))>"
proof-
  have "<gxs X Si Gc * \<up>(False = False) * emp> has_nb_imp Gc Si y
           <\<lambda> r. gxs X Si Gc * emp * \<up>(r = foldl (\<lambda> a x. True) False (nbrs (EE X) y))>"
    unfolding has_nb_imp_def
    by (rule xnbs_rule[where A = "\<lambda> b bi. \<up>(bi = b)" and F = emp and f = "\<lambda> x a. True", OF X])
       sep_auto
  then show ?thesis
    by (rule ht_cons[rotated 2]) (sep_auto simp: foldl_True)+
qed

lemma is_src_imp_rule:
  "y < n \<Longrightarrow> <gxs X Si Gc> is_src_imp Gc Si y
   <\<lambda> r. gxs X Si Gc * \<up>(r = ((y \<notin> X \<and> y \<in> S0 X) \<and>
            (y \<notin> T0 X \<and> find (\<lambda> x. x \<in> X \<and> exch_orcl2 (orcl_prep2 X) x y) [0..<n]
              \<noteq> None)))>"
  unfolding is_src_imp_def
  by (sep_auto heap: s_imp_rule has_nb_rule simp: nb_char)

lemma collect_src_rule:
  assumes "n \<le> length fl"
  shows "<Fr \<mapsto>\<^sub>a fl * gxs X Si Gc> collect_range_imp (is_src_imp Gc Si) n Fr
         <\<lambda> k. \<exists>\<^sub>A fl'. Fr \<mapsto>\<^sub>a fl' * gxs X Si Gc *
               \<up>(length fl' = length fl \<and>
                 k = length (filter (csr.has_nb (csr.exch_ctx X)) (csr.srcs (csr.exch_ctx X))) \<and>
                 take k fl' = filter (csr.has_nb (csr.exch_ctx X)) (csr.srcs (csr.exch_ctx X)))>"
  unfolding eq_srcs[symmetric]
  by (rule collect_range_imp_rule[OF is_src_imp_rule assms])

lemma is_tgt_imp_rule:
  "y < n \<Longrightarrow> <bool_array_set_assn n V Vi * gxs X Si Gc> is_tgt_imp Si Vi y
   <\<lambda> r. bool_array_set_assn n V Vi * gxs X Si Gc * \<up>(r = ((y \<notin> X \<and> y \<in> T0 X) \<and> y
     \<in> V))>"
  unfolding is_tgt_imp_def t_imp_def gxs_def T0_def
  by (sep_auto heap: bool_array_set_memb_rule smemb_rule o2.ins_imp)

lemma find_tgt_rule:
  "<bool_array_set_assn n V Vi * gxs X Si Gc> find_range_imp (is_tgt_imp Si Vi) 0 n
   <\<lambda> r. bool_array_set_assn n V Vi * gxs X Si Gc * \<up>(r = find (\<lambda> y. y \<in> V) (csr.tgts
     (csr.exch_ctx X)))>"
  unfolding eq_tgts[symmetric] find_filter
  by (rule find_range_imp_rule, rule is_tgt_imp_rule, assumption)

lemma single_path_rule:
  assumes "s < n"
  shows "<parr_assn n Ra> Array.upd 0 s Ra <\<lambda> _. path_assn n (Some [s]) (Some 1) Ra>"
proof-
  have "rev (take 1 (l[0 := s])) = [s]" if "l \<noteq> []" for l :: "nat list"
    using that
    by (cases l) simp_all
  then show ?thesis
    unfolding parr_assn_def path_assn_def option.case(2)
    using assms
    by sep_auto
qed

subsubsection \<open>The BFS\<close>

context
  fixes ss
  assumes b: "fb.bfs_sources ss"
begin

lemma fin_eq: "csr.bfs_final (nbrs_map (EE X)) ss = fb.fin ss"
  unfolding csr.bfs_final_def fb.fin_def[OF b]
  by (rule refl)


lemma target_path_eq:
  "csr.target_path (nbrs_map (EE X)) ss ts =
   (case find (\<lambda> y. y \<in> set (BFS_dist_state.visited (fb.fin ss))) ts of
      None \<Rightarrow> None
    | Some t \<Rightarrow> Some (rev (parent_array.pa_get_path n (BFS_par_state.parent (fb.fin ss)) t)))"
  unfolding csr.target_path_def unfolding Let_def fin_eq length_upt diff_zero
  by (rule refl)

lemma tail_rule:
  "<bool_array_set_assn n (set (BFS_dist_state.visited (fb.fin ss))) Vi * gxs X Si Gc * parr_assn n Ra *
    (BFS_subprocedures_lists.imp_dist_assn n Da (nbrs_map (EE X)) (BFS_dist_state.dists (fb.fin ss)) di *
     parent_array.pa_parent_assn n (BFS_par_state.parent (fb.fin ss)) Pa)>
     tail_imp Si Ra (Vi, di, Pa)
   <\<lambda> res. gxs X Si Gc *
           path_assn n (csr.target_path (nbrs_map (EE X)) ss (csr.tgts (csr.exch_ctx X))) res Ra *
           (bool_array_set_assn n (set (BFS_dist_state.visited (fb.fin ss))) Vi *
            BFS_subprocedures_lists.imp_dist_assn n Da (nbrs_map (EE X)) (BFS_dist_state.dists (fb.fin ss)) di *
            parent_array.pa_parent_assn n (BFS_par_state.parent (fb.fin ss)) Pa)>"
proof-
  let ?V = "set (BFS_dist_state.visited (fb.fin ss))" and ?ts = "csr.tgts (csr.exch_ctx X)"
  let ?D = "BFS_subprocedures_lists.imp_dist_assn n Da (nbrs_map (EE X)) (BFS_dist_state.dists (fb.fin ss)) di"
  let ?P = "parent_array.pa_parent_assn n (BFS_par_state.parent (fb.fin ss)) Pa"
  let ?DP = "?D * ?P"
  let ?f = "find (\<lambda> y. y \<in> ?V) ?ts"
  have f: "<bool_array_set_assn n ?V Vi * gxs X Si Gc * parr_assn n Ra * ?DP> find_range_imp (is_tgt_imp Si Vi) 0 n
           <\<lambda> r. bool_array_set_assn n ?V Vi * gxs X Si Gc * (parr_assn n Ra * ?DP) * \<up>(r = ?f)>"
    by (rule ht_frame_ac[OF find_tgt_rule[where V = ?V and Vi = Vi and Si = Si and Gc = Gc],
                         where R = "parr_assn n Ra * ?DP"])
       (simp only: star_aci, rule ent_refl)+
  show ?thesis
  proof(cases ?f)
    case None
    note tp = target_path_eq[of "?ts", unfolded None option.case(1)]
    show ?thesis
      unfolding tail_imp_def prod.case tp
      by (rule ht_bind[OF f], rule ht_pure_pre, simp only: None option.case(1),
          rule ht_cons_pre[OF _ ht_return_wp]) (simp only: path_None star_aci, rule ent_refl)
  next
    case (Some t)
    let ?pp = "rev (parent_array.pa_get_path n (BFS_par_state.parent (fb.fin ss)) t)"
    note tp = target_path_eq[of "?ts", unfolded Some option.case(2)]
    have p: "<parr_assn n Ra * ?DP * (bool_array_set_assn n ?V Vi * gxs X Si Gc)> bfs_path Pa Ra t
             <\<lambda> k. ?DP * path_assn n (Some ?pp) (Some k) Ra * (bool_array_set_assn n ?V Vi * gxs X Si Gc)>"
      by (rule ht_frame_ac[OF fb.path_len_rule[OF b Some],
                           where R = "?D * (bool_array_set_assn n ?V Vi * gxs X Si Gc)"])
         (simp only: star_aci, rule ent_refl)+
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
                 path_assn n (csr.target_path (nbrs_map (EE X)) ss (csr.tgts (csr.exch_ctx X))) res Ra *
                 work_assn n Vi Fr Bf Da Pa>"
proof-
  let ?Fl = "Fr \<mapsto>\<^sub>a fl" and ?G = "gxs X Si Gc" and ?R = "parr_assn n Ra" and ?B = "len_assn (Suc n) Bf"
  let ?V = "set (BFS_dist_state.visited (fb.fin ss))"
  let ?D = "BFS_subprocedures_lists.imp_dist_assn n Da (nbrs_map (EE X)) (BFS_dist_state.dists (fb.fin ss)) Da"
  let ?P = "parent_array.pa_parent_assn n (BFS_par_state.parent (fb.fin ss)) Pa"
  let ?T = "csr.target_path (nbrs_map (EE X)) ss (csr.tgts (csr.exch_ctx X))"
  have "<?Fl * ?G * ?R * len_assn n Vi * ?B * len_assn n Da * len_assn n Pa>
               round_imp Gc Vi Fr Bf Da Pa Si Ra (length ss)
             <\<lambda> res. ?G * path_assn n ?T res Ra *
                    (bool_array_set_assn n ?V Vi * ?D * ?P * len_assn (Suc n) Fr * ?B)>"
    unfolding round_imp_def bfs_run_def
    by (rule ht_bind[OF ht_frame_ac[OF clear_len[where Vi = Vi],
                       where R = "?Fl * ?G * ?R * ?B * len_assn n Da * len_assn n Pa"]],
        (simp only: star_aci, rule ent_refl), rule ent_refl,
        rule ht_bind[OF ht_frame_ac[OF fill_len[where a = Da and f = id],
                       where R = "bool_array_set_assn n {} Vi * (?Fl * ?G * ?R * ?B * len_assn n Pa)"]],
        (simp only: star_aci, rule ent_refl), rule ent_refl,
        rule ht_bind[OF ht_frame_ac[OF fb.bfs_len_rule[OF b assms, where Bf = Bf and Vi = Vi and Fr = Fr and
                                       Da = Da and Pa = Pa and Gh = "(Si, Gc)", unfolded prod.case],
                                    where R = ?R]],
        (simp only: star_aci, rule ent_refl), rule ent_refl,
        rule ht_frame_ac[OF tail_rule[where Vi = Vi and Si = Si and Gc = Gc and Ra = Ra and Da = Da and
                                       Pa = Pa and di = Da],
                         where R = "len_assn (Suc n) Fr * ?B"])
       (simp only: star_aci, rule ent_refl)+
  then show ?thesis
    by (rule ht_cons_post)
       (rule ent_true_drop(2), rule ent_star_mono[OF ent_refl fb.work_ent])
qed

end

subsubsection \<open>A Search\<close>

lemma collect_src_len:
  "<len_assn (Suc n) Fr * gxs X Si Gc> collect_range_imp (is_src_imp Gc Si) n Fr
   <\<lambda> k. \<exists>\<^sub>A fl'. Fr \<mapsto>\<^sub>a fl' * gxs X Si Gc *
         \<up>(length fl' = Suc n \<and>
           k = length (filter (csr.has_nb (csr.exch_ctx X)) (csr.srcs (csr.exch_ctx X))) \<and>
           take k fl' = filter (csr.has_nb (csr.exch_ctx X)) (csr.srcs (csr.exch_ctx X)))>"
proof(rule pull_len, goal_cases)
  case (1 fl)
  then show ?case
    using collect_src_rule[of fl Fr Si Gc]
    by simp
qed

lemma collect_src_none:
  "<len_assn (Suc n) Fr * gxs X Si Gc> collect_range_imp (is_src_imp Gc Si) n Fr
   <\<lambda> k. len_assn (Suc n) Fr * gxs X Si Gc *
         \<up>(k = length (filter (csr.has_nb (csr.exch_ctx X)) (csr.srcs (csr.exch_ctx X))))>"
  by (rule ht_cons_post[OF collect_src_len]) (unfold len_assn_def, sep_auto)

lemma aug_path_imp_rule:
  "<parr_assn n Ra * gxs X Si Gc * work_assn n Vi Fr Bf Da Pa> aug_path_imp Gc Vi Fr Bf Da Pa Si Ra
   <\<lambda> res. path_assn n (csr.augmenting_path X) res Ra * gxs X Si Gc * work_assn n Vi Fr Bf Da Pa>"
proof(cases "find (csr.in_T (csr.exch_ctx X)) (csr.srcs (csr.exch_ctx X))")
  case (Some s)
  have "s \<in> S X"
    using conjunct2[OF find_SomeD[OF Some]] unfolding csr.srcs(1)[OF X] .
  then have "s < n"
    using S_in_carrier[OF X(3,4)]
    by auto
  note single = single_path_rule[OF this]
  show ?thesis
    unfolding aug_path_imp_def ap_char Some option.case(2)
    by (sep_auto heap: find_st_rule single simp: Some)
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
      unfolding ap_char None option.case(1) if_P[OF True]
      by (rule refl)
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

definition "mst Gc Vi Fr Bf Da Pa = ost1 * ost2 *
  (case Gc of (Ba, Ga) \<Rightarrow> Ba \<mapsto>\<^sub>a map (csr_start (nbrs es0)) [0..<Suc n] *
     Ga \<mapsto>\<^sub>a csr_entries (nbrs es0) n) *
  work_assn n Vi Fr Bf Da Pa"

lemma imp_loop:
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

lemma loop_correct:
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
