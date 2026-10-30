theory Matroid_Weighted_Intersection_Exchange_Graph_Imp
  imports Matroid_Weighted_Intersection_Exchange_Graph_CSR Matroid_Weighted_Intersection_Imp_Loop
    Matroid_Intersection_Exchange_Graph_Imp
begin

section \<open>The Weighted Exchange Graph Search in Imperative HOL\<close>

text \<open>The imperative counterpart of the context of
  @{theory Matroid_Intersection.Matroid_Weighted_Intersection_Exchange_Graph_CSR}, as
  @{theory Matroid_Intersection.Matroid_Intersection_Exchange_Graph_Imp} is that of the unweighted
  path search. It allocates nothing. The weights are arrays over an ordered ring \<open>'n\<close>, read in the
  reals through the embedding \<open>h\<close>. The context of a round lives in the work arrays of the BFS and two
  small arrays: \<open>Mi\<close> holds the maximum weights of the sources and targets, \<open>Ti\<close> how the path
    is
  found (none, a single element, or the BFS) and its end. The BFS runs with the exchange iterator,
  additionally skipping the edges that are not tight, so it sees exactly the tight graph.
  Afterwards the visited array holds the reachable set when there is no path; the gaps and the
  shift read it there.\<close>

subsection \<open>Code\<close>

locale weighted_intersection_exchange_imp_spec =
  unweighted_intersection_exchange_imp_spec n smemb_imp ins1_imp exch1_imp ins2_imp exch2_imp
  for n smemb_imp
    and ins1_imp :: "'si \<Rightarrow> nat \<Rightarrow> bool Heap" and exch1_imp ins2_imp exch2_imp
begin

text \<open>The tight exchange neighbours: the exchange iterator, skipping the neighbours of different
  weight (\<open>C1\<close> for an element of the solution, \<open>C2\<close> otherwise).\<close>

definition "teq_imp C cu = (\<lambda> _ _ v. do { cv \<leftarrow> Array.nth C v; return (cu = cv) })"

definition tnbs :: "'si \<times> (nat array \<times> nat array) \<times> 'n::heap array \<times> 'n array
    \<Rightarrow> nat \<Rightarrow>
                     (nat \<Rightarrow> 'acc \<Rightarrow> 'acc Heap) \<Rightarrow> 'acc \<Rightarrow> 'acc Heap" where
  "tnbs Gh u fi acc = (case Gh of (Si, Gc, C1, C2) \<Rightarrow>
     if u < n then do {
       b \<leftarrow> smemb_imp u Si;
       cu \<leftarrow> Array.nth (if b then C1 else C2) u;
       xnbs (Si, Gc) u (filt_imp (teq_imp (if b then C1 else C2) cu) Si u fi) acc }
     else return acc)"

text \<open>The BFS of the library with this iterator, specialised to it as in
  @{theory Matroid_Intersection.Matroid_Intersection_Exchange_Graph_Imp}.\<close>

definition "t_inner Gh = bfs_inner_loop (tnbs Gh)"

definition "t_outer Gh = bfs_outer_loop (tnbs Gh)"

definition "tround Gh = bfs_round (tnbs Gh)"

definition "t_loop Gh = bfs_loop (tnbs Gh)"

definition "tbfs_run Gh = bfs_visited_dists_parents (tnbs Gh)"

lemmas t_inner_code = bfs_sub_code.inner_loop.simps[of "tnbs Gh" for Gh, folded t_inner_def]

lemmas t_outer_code =
  bfs_sub_code.outer_loop.simps[of "tnbs Gh" for Gh, folded t_outer_def t_inner_def]

lemmas tround_code =
  bfs_sub_code.next_frontier_current_parents_imp.simps[of "tnbs Gh" for Gh, folded tround_def t_outer_def]

lemmas t_loop_code = bfs_code.BFS_par_imp.simps[of "tnbs Gh" for Gh, folded t_loop_def tround_def]

lemmas tbfs_run_code =
  bfs_code.visited_dists_parents_imp_def[of "tnbs Gh" for Gh, folded tbfs_run_def t_loop_def]

text \<open>The maximum weight over a range, and the tests of a search: the unweighted ones with the
  weights compared and the tight iterator.\<close>

definition "max_imp P C = foldr_range_imp (\<lambda> y a. do {
   p \<leftarrow> P y;
   if p then do { x \<leftarrow> Array.nth C y; return (Some (case a of None \<Rightarrow> x | Some w \<Rightarrow>
     max w x)) }
   else return a }) n None"

definition "thas_nb_imp Gh y = tnbs Gh y (\<lambda> _ _. return True) False"

definition "wst_imp Si C1 C2 mS mT y = do {
   s \<leftarrow> st_imp Si y;
   if s then do {
     x \<leftarrow> Array.nth C1 y;
     if x = mS then do { z \<leftarrow> Array.nth C2 y; return (z = mT) } else return False }
   else return False }"

definition "wsrc_imp Gh mS y = (case Gh of (Si, Gc, C1, C2) \<Rightarrow> do {
   s \<leftarrow> s_imp Si y;
   if s then do { x \<leftarrow> Array.nth C1 y; if x = mS then thas_nb_imp Gh y else return False }
   else return False })"

definition "wtgt_imp Si Vi C2 mT y = do {
   t \<leftarrow> is_tgt_imp Si Vi y;
   if t then do { z \<leftarrow> Array.nth C2 y; return (z = mT) } else return False }"

text \<open>The sources of maximum weight without tight out-edge belong to the reachable set.\<close>

definition "drop_imp Gh mS Vi = (case Gh of (Si, Gc, C1, C2) \<Rightarrow> foldr_range_imp (\<lambda> y _. do {
   s \<leftarrow> s_imp Si y;
   if s then do {
     x \<leftarrow> Array.nth C1 y;
     if x = mS then do {
       e \<leftarrow> thas_nb_imp Gh y;
       if e then return () else do { Array.upd y True Vi; return () } }
     else return () }
   else return () }) n ())"

text \<open>The context of a round, the counterpart of @{const weighted_intersection_exchange_spec.wtight_ctx}:
  the maximum weights into \<open>Mi\<close>; a single-element path if a source of maximum weight is a target of
  maximum weight; otherwise the BFS from the sources of maximum weight with a tight out-edge, and
  the first visited target of maximum weight. Without a path the dropped sources are added to the
  visited array, which then holds the reachable set.\<close>

definition "wsearch_imp Gc Vi Fr Bf Da Pa Si C1 C2 mS mT = do {
   r \<leftarrow> find_range_imp (wst_imp Si C1 C2 mS mT) 0 n;
   (case r of
      Some s \<Rightarrow> return (1 :: nat, s)
    | None \<Rightarrow> do {
        k \<leftarrow> collect_range_imp (wsrc_imp (Si, Gc, C1, C2) mS) n Fr;
        bool_array_set_clear_imp n Vi;
        t \<leftarrow> (if k = 0 then return None
              else do {
                fill_range_imp id n Da;
                tbfs_run (Si, Gc, C1, C2) Vi (Fr, k, Bf) Da Pa;
                find_range_imp (wtgt_imp Si Vi C2 mT) 0 n });
        (case t of
           Some t \<Rightarrow> return (2, t)
         | None \<Rightarrow> do { drop_imp (Si, Gc, C1, C2) mS Vi; return (0, 0) }) }) }"

definition "wtight_ctx_imp Gc Vi Fr Bf Da Pa Mi Ti Si C1 C2 = do {
   m1 \<leftarrow> max_imp (s_imp Si) C1;
   m2 \<leftarrow> max_imp (t_imp Si) C2;
   let mS = (case m1 of None \<Rightarrow> 0 | Some x \<Rightarrow> x);
   let mT = (case m2 of None \<Rightarrow> 0 | Some x \<Rightarrow> x);
   Array.upd 0 mS Mi;
   Array.upd 1 mT Mi;
   t \<leftarrow> wsearch_imp Gc Vi Fr Bf Da Pa Si C1 C2 mS mT;
   Array.upd 0 (fst t) Ti;
   Array.upd 1 (snd t) Ti;
   return () }"

text \<open>The path of the context, written into the path array; the counterpart of
  @{const wctx_path}.\<close>

definition "wctx_path_imp Pa Ti Ra = do {
   k \<leftarrow> Array.nth Ti 0;
   v \<leftarrow> Array.nth Ti 1;
   if k = 1 then do { Array.upd 0 v Ra; return (Some 1) }
   else if k = 2 then do { l \<leftarrow> bfs_path Pa Ra v; return (Some l) }
   else return None }"

text \<open>The minimum gap, the counterpart of @{const weighted_intersection_exchange_spec.weps}: one pass
  over the elements with the exchange edges leaving the reachable set, the sources outside it and the
  targets inside it.\<close>

definition "gap_imp C1 C2 b Vi u = (\<lambda> v a. do {
   r \<leftarrow> Array.nth Vi v;
   if r then return a
   else do {
     g \<leftarrow> (if b then do { x \<leftarrow> Array.nth C1 u; y \<leftarrow> Array.nth C1 v; return (x - y) }
           else do { x \<leftarrow> Array.nth C2 v; y \<leftarrow> Array.nth C2 u; return (x - y) });
     return (eps_min a g) } })"

definition "weps_step Gc Vi Si C1 C2 mS mT u a = do {
   r \<leftarrow> Array.nth Vi u;
   b \<leftarrow> smemb_imp u Si;
   a1 \<leftarrow> (if r then xnbs (Si, Gc) u (gap_imp C1 C2 b Vi u) a else return a);
   s \<leftarrow> s_imp Si u;
   a2 \<leftarrow> (if s \<and> \<not> r then do { x \<leftarrow> Array.nth C1 u; return (eps_min a1 (mS - x)) } else
     return a1);
   t \<leftarrow> t_imp Si u;
   (if t \<and> r then do { x \<leftarrow> Array.nth C2 u; return (eps_min a2 (mT - x)) } else return a2) }"

definition "weps_imp Gc Vi Mi Si C1 C2 = do {
   mS \<leftarrow> Array.nth Mi 0;
   mT \<leftarrow> Array.nth Mi 1;
   foldr_range_imp (weps_step Gc Vi Si C1 C2 mS mT) n None }"

text \<open>The shift of a weight array on the reachable set.\<close>

definition "wshift_imp Vi e C = foldr_range_imp (\<lambda> i _. do {
   r \<leftarrow> Array.nth Vi i;
   if r then do { x \<leftarrow> Array.nth C i; Array.upd i (x + e) C; return () } else return () }) n ()"

text \<open>Copying and clearing weight arrays, in place.\<close>

definition "ccopy_imp C' C = copy_range_imp (\<lambda> i. Array.nth C' i) n C"

definition "czero_imp C = do { fill_range_imp (\<lambda> _. 0) n C; return () }"

end

subsection \<open>Correctness\<close>

text \<open>Weight arrays represent maps that vanish outside the elements.\<close>

definition warr_assn :: "nat \<Rightarrow> ('n :: heap \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real)
    \<Rightarrow> 'n array \<Rightarrow> assn" where
  "warr_assn n h c C = (\<exists>\<^sub>A l. C \<mapsto>\<^sub>a l * \<up>(length l = n \<and> c = (\<lambda> i. if i
    < n then h (l ! i) else 0)))"

lemma len_warr: "len_assn n C \<Longrightarrow>\<^sub>A \<exists>\<^sub>A c. warr_assn n h c C"
  by (unfold len_assn_def warr_assn_def) sep_auto

text \<open>An array holding a list is the weight array of the list read through the embedding.\<close>

lemma warr_of_list:
  fixes h :: "'n :: {linordered_idom, heap} \<Rightarrow> real"
  assumes "real_embedding h"
  shows "C \<mapsto>\<^sub>a l = warr_assn (length l) h (\<lambda> i. if i < length l then h (l ! i) else 0) C"
proof-
  interpret real_embedding h
    by (rule assms)
  have eq: "l' = l" if "length l' = length l"
    "(\<lambda> i. if i < length l then h (l ! i) else 0) =
     (\<lambda> i. if i < length l then h (l' ! i) else 0)" for l'
  proof(rule nth_equalityI[OF that(1)], goal_cases)
    case (1 i)
    with fun_cong[OF that(2), of i] show ?case
      using that(1)
      by simp
  qed
  show ?thesis
    unfolding warr_assn_def
    by (rule ent_iffI) (sep_auto, rule ent_ex_preI, sep_auto dest: eq)
qed

locale weighted_intersection_exchange_imp =
  weighted_intersection_exchange_imp_spec +
  unweighted_intersection_exchange_imp +
  weighted_intersection_exchange_csr where set_insert = "Set.insert :: nat \<Rightarrow> nat set \<Rightarrow> nat set"
    and set_delete = "\<lambda> x X. X - {x}" and to_set = "\<lambda> X. X" and set_invar = finite
    and set_empty = "{}" and set_memb = "\<lambda> x X. x \<in> X" and carrier_list = "[0..<n]"
    and carrier = "{0..<n}" and c_lookup = "\<lambda> c. c"
    and c_shift = "\<lambda> R e c x. if x \<in> set R then c x + e else c x" and c_zero = "\<lambda> _. 0"
    and c_invar = "\<lambda> _. True" +
  real_embedding h
  for h :: "'n :: {linordered_idom, heap} \<Rightarrow> real"
begin

text \<open>The fields of the tight context, in the form the simplifier produces (the bound of the parent
  paths, the length of the carrier list, simplified).\<close>

lemmas wtight_ctx_fields_n = csr.wtight_ctx_fields[unfolded length_upt diff_zero]
  and tight_iff_n = csr.tight_iff[unfolded length_upt diff_zero]

subsubsection \<open>The Tight Iterator\<close>

lemma warr_nth: "i < n \<Longrightarrow> <warr_assn n h c C> Array.nth C i <\<lambda> r. warr_assn n h c C * \<up>(h r
    = c i)>"
  by (unfold warr_assn_def) sep_auto

text \<open>The running minimum through the embedding.\<close>

lemma foldl_eps_of:
  "foldl (\<lambda> a x. if P x then eps_min a (g x) else a) a xs = eps_of (g ` {x \<in> set xs. P x}) a"
  by (simp only: foldl_conv_foldr foldr_eps_of set_rev)

lemma eps_min_h: "map_option h (eps_min a x) = eps_min (map_option h a) (h x)"
  by (cases a) (simp_all add: eps_min_def)

lemmas eps_of_h = trans[OF eps_min_h eps_of_single]

text \<open>The shift adds to the entries of a set.\<close>

lemma foldr_shift:
  "foldr (\<lambda> j c. if j \<in> V then fun_upd c j (c j + e) else c) [0..<k] c =
     (\<lambda> x. if x < k \<and> x \<in> V then c x + e else c x)"
  by (induction k arbitrary: c) (auto simp: fun_eq_iff less_Suc_eq)

lemma wshift_set_rule:
  "<bool_array_set_assn n V Vi * warr_assn n h c C> wshift_imp Vi e C
   <\<lambda> _. bool_array_set_assn n V Vi * warr_assn n h (\<lambda> x. if x \<in> V then c x + h e else c x) C>"
proof(cases "V \<subseteq> {..<n}")
  case True
  have step: "<warr_assn n h c' C * bool_array_set_assn n V Vi>
                do { r \<leftarrow> Array.nth Vi j;
                     if r then do { x \<leftarrow> Array.nth C j; Array.upd j (x + e) C; return () }
                     else return () }
              <\<lambda> _. warr_assn n h (if j \<in> V then fun_upd c' j (c' j + h e) else c') C *
                    bool_array_set_assn n V Vi>" if "j < n" for j c'
    using that unfolding warr_assn_def
    by (sep_auto heap: bool_array_set_memb_rule simp: h_add nth_list_update fun_eq_iff)
  have "<warr_assn n h c C * bool_array_set_assn n V Vi> wshift_imp Vi e C
           <\<lambda> _. warr_assn n h (\<lambda> x. if x < n \<and> x \<in> V then c x + h e else c x) C *
                 bool_array_set_assn n V Vi>"
    unfolding wshift_imp_def foldr_shift[symmetric]
    by (rule foldr_range_imp_rule[where A = "\<lambda> c' _. warr_assn n h c' C"], rule step)
  moreover have "(\<lambda> x. if x < n \<and> x \<in> V then c x + h e else c x) = (\<lambda> x. if x \<in> V then c
    x + h
    e else c x)"
    using True
    by (auto simp: fun_eq_iff)
  ultimately show ?thesis
    by (simp only: star_aci)
next
  case False
  show ?thesis
    unfolding bool_array_set_assn_def
    using False
    by sep_auto
qed

lemma nbrs_filter: "nbrs (filter P es) u = filter (\<lambda> v. P (u, v)) (nbrs es u)"
  by (induction es) (auto simp: nbrs_def)

text \<open>Copying and clearing weight arrays.\<close>

lemma ccopy_rule:
  "<warr_assn n h c C' * warr_assn n h d C> ccopy_imp C' C <\<lambda> _. warr_assn n h c C' * warr_assn n h c C>"
proof-
  have c: "<C \<mapsto>\<^sub>a l * C' \<mapsto>\<^sub>a l' * \<up>(length l = n)> ccopy_imp C' C
           <\<lambda> _. C \<mapsto>\<^sub>a map (\<lambda> i. l' ! i) [0..<n] * C' \<mapsto>\<^sub>a l'>" if "length
             l' = n" for l l'
    unfolding ccopy_imp_def
    by (rule copy_range_imp_rule) (sep_auto simp: that)
  show ?thesis
    unfolding warr_assn_def
    by (sep_auto heap: c)
qed

lemma czero_rule: "<warr_assn n h d C> czero_imp C <\<lambda> _. warr_assn n h (\<lambda> _. 0) C>"
  by (unfold czero_imp_def warr_assn_def) (sep_auto heap: fill_range_imp_rule)

text \<open>The weight arrays as immutable fixed-universe maps with copying and clearing.\<close>

lemma warr_copy_clear_imp:
  "fixed_univ_map_copy_imp {..<n} (\<lambda> _. True) (\<lambda> c. c) h (warr_assn n h) Array.nth ccopy_imp"
  "fixed_univ_map_clear_imp {..<n} (\<lambda> _. True) (\<lambda> c. c) h (warr_assn n h) Array.nth
     (\<lambda> _. 0) czero_imp"
  by (intro fixed_univ_map_copy_imp.intro fixed_univ_map_clear_imp.intro
        fixed_univ_map_basic_imp.intro fixed_univ_map_copy_imp_axioms.intro
        fixed_univ_map_clear_imp_axioms.intro ccopy_rule czero_rule warr_nth, simp)+

text \<open>The graph handle of the tight iterator: the solution, the CSR and the two weight arrays.\<close>

definition "gtx X c1 c2 Gh = (case Gh of (Si, Gc, C1, C2) \<Rightarrow>
  gxs X Si Gc * warr_assn n h c1 C1 * warr_assn n h c2 C2)"

text \<open>The context \<open>K\<close> in the arrays. Without a path the visited array holds the reachable set.
  A single-element path is its end \<open>t\<close>; a path of the BFS is given by its end \<open>t\<close> and the
  distance and parent arrays of some BFS run on the tight graph.\<close>

definition "wpath_assn Vi Da Pa (t :: nat \<times> nat) K = (case wctx_path K of
    None \<Rightarrow> bool_array_set_assn n (set (wctx_R K)) Vi * len_assn n Da * len_assn n Pa * \<up>(fst t = 0)
  | Some p \<Rightarrow> len_assn n Vi *
      (if fst t = 1 then len_assn n Da * len_assn n Pa * \<up>(p = [snd t] \<and> snd t < n)
       else (\<exists>\<^sub>A ss. BFS_subprocedures_lists.imp_dist_assn n Da (nbrs_map (wctx_es K))
                (BFS_dist_state.dists (bfs_iterator_arrays.fin (nbrs_map (wctx_es K)) ss)) Da *
              parent_array.pa_parent_assn n
                (BFS_par_state.parent (bfs_iterator_arrays.fin (nbrs_map (wctx_es K)) ss)) Pa *
              \<up>(fst t = 2 \<and> bfs_iterator_arrays.bfs_sources (nbrs_map (wctx_es K)) ss \<and>
                find (\<lambda> y. y \<in> set (BFS_dist_state.visited (bfs_iterator_arrays.fin (nbrs_map (wctx_es K))
                  ss)))
                  (wctx_tb K) = Some (snd t) \<and>
                p = rev (parent_array.pa_get_path n
                      (BFS_par_state.parent (bfs_iterator_arrays.fin (nbrs_map (wctx_es K)) ss)) (snd t))))))"

definition "wctx_assn Vi Fr Bf Da Pa Mi Ti K =
  (\<exists>\<^sub>A mi ti. Mi \<mapsto>\<^sub>a mi * Ti \<mapsto>\<^sub>a ti * len_assn (Suc n) Fr * len_assn (Suc n)
    Bf *
     \<up>(length mi = 2 \<and> length ti = 2 \<and>
       (csr.srcs (wctx_c K) \<noteq> [] \<longrightarrow> h (mi ! 0) = wctx_mS K) \<and>
       (csr.tgts (wctx_c K) \<noteq> [] \<longrightarrow> h (mi ! 1) = wctx_mT K)) *
     wpath_assn Vi Da Pa (ti ! 0, ti ! 1) K)"

text \<open>The work arrays with stale contents.\<close>

definition "wws Vi Fr Bf Da Pa Mi Ti = work_assn n Vi Fr Bf Da Pa * len_assn 2 Mi * len_assn 2 Ti"

context
  fixes X and c1 c2 :: "nat \<Rightarrow> real"
  assumes X: "finite X" "X \<subseteq> {0..<n}" "indep1 X" "indep2 X"
begin

lemma nbrs_tight:
  "nbrs (wctx_es (csr.wtight_ctx X c1 c2)) u =
     filter (\<lambda> v. if u \<in> X then c1 u = c1 v else c2 u = c2 v) (nbrs (EE X) u)"
  by (simp add: wtight_ctx_fields_n[OF X] nbrs_filter tight_iff_n[OF X])

lemma nbrs_tight_out: "\<not> u < n \<Longrightarrow> nbrs (wctx_es (csr.wtight_ctx X c1 c2)) u = []"
  unfolding nbrs_tight nbrs_EE_out[OF X]
  by simp

end

lemma read_frame:
  assumes "<A> c <\<lambda> r. A * \<up>(P r)>"
  shows "<A * F> c <\<lambda> r. A * F * \<up>(P r)>"
  by (rule ht_frame_ac[OF assms, where R = F]) sep_auto+

lemma teq_rule:
  assumes "h cu = c u" "<W> Array.nth C v <\<lambda> r. W * \<up>(h r = c v)>"
  shows "<W> teq_imp C cu Si u v <\<lambda> ok. W * \<up>(ok = (c u = c v))>"
  unfolding teq_imp_def
  by (sep_auto heap: assms(2) simp: h_eq_iff[symmetric] assms(1))

lemma teq_filt_rule:
  assumes "h cu = c u" "<W> Array.nth C v <\<lambda> r. W * \<up>(h r = c v)>"
    "c u = c v \<Longrightarrow> <A acc acci * F> fi v acci <\<lambda> r. A (f v acc) r * F>"
  shows "<A acc acci * (F * W)> filt_imp (teq_imp C cu) Si u fi v acci
         <\<lambda> r. A (if c u = c v then f v acc else acc) r * (F * W)>"
  unfolding filt_imp_def
  by (cases "c u = c v"; sep_auto heap: teq_rule[OF assms(1,2)] assms(3))

context
  fixes X and c1 c2 :: "nat \<Rightarrow> real"
  assumes X: "finite X" "X \<subseteq> {0..<n}" "indep1 X" "indep2 X"
  notes ctx_fields = csr.wtight_ctx_fields[OF X]
    and ctx_fields_n = wtight_ctx_fields_n[OF X]
    and edge_bounds = EE_bound[OF X]
    and tgts_eq = eq_tgts[OF X]
    and tight_nbrs = nbrs_tight[OF X]
begin

text \<open>The tight iterator walks the neighbours in the tight graph.\<close>

lemma gtx_memb:
  "u < n \<Longrightarrow> <gtx X c1 c2 (Si, Gc, C1, C2)> smemb_imp u Si
   <\<lambda> b. gtx X c1 c2 (Si, Gc, C1, C2) * \<up>(b = (u \<in> X))>"
  unfolding gtx_def gxs_def prod.case
  by (sep_auto heap: smemb_rule)

lemma tnbs_rule:
  assumes "\<And> acc acci x. x \<in> set (nbrs (wctx_es (csr.wtight_ctx X c1 c2)) u) \<Longrightarrow>
               <A acc acci * F> fi x acci <\<lambda> r. A (f x acc) r * F>"
  shows "<gtx X c1 c2 Gh * A acc acci * F> tnbs Gh u fi acci
         <\<lambda> r. gtx X c1 c2 Gh * F *
               A (foldl (\<lambda> acc x. f x acc) acc (nbrs (wctx_es (csr.wtight_ctx X c1 c2)) u)) r>"
proof-
  let ?E = "wctx_es (csr.wtight_ctx X c1 c2)"
  obtain Si Gc C1 C2 where Gh: "Gh = (Si, Gc, C1, C2)"
    by (cases Gh) auto
  let ?W = "warr_assn n h c1 C1 * warr_assn n h c2 C2"
  have main: "<gtx X c1 c2 Gh * A acc acci * F>
                do { cu \<leftarrow> Array.nth C u; xnbs (Si, Gc) u (filt_imp (teq_imp C cu) Si u fi) acci }
              <\<lambda> r. gtx X c1 c2 Gh * F * A (foldl (\<lambda> acc x. f x acc) acc (nbrs ?E u)) r>"
    if u: "u < n" and rd: "\<And> v. v < n \<Longrightarrow> <?W> Array.nth C v <\<lambda> r. ?W * \<up>(h r = c v)>"
      and nb: "nbrs ?E u = filter (\<lambda> v. c u = c v) (nbrs (EE X) u)" for c C
  proof-
    have r0: "<gtx X c1 c2 Gh * A acc acci * F> Array.nth C u
              <\<lambda> r. gxs X Si Gc * A acc acci * (F * ?W) * \<up>(h r = c u)>"
      by (rule ht_frame_ac[OF rd[OF u], where R = "gxs X Si Gc * A acc acci * F"])
         (simp only: Gh gtx_def prod.case star_aci, rule ent_refl)+
    have x: "<gxs X Si Gc * A acc acci * (F * ?W)> xnbs (Si, Gc) u (filt_imp (teq_imp C cu) Si u fi) acci
             <\<lambda> r. gxs X Si Gc * (F * ?W) *
                   A (foldl (\<lambda> a x. if c u = c x then f x a else a) acc (nbrs (EE X) u)) r>"
      if cu: "h cu = c u" for cu
    proof(rule xnbs_rule[OF X])
      fix acc acci x
      assume x: "x \<in> set (nbrs (EE X) u)"
      have "x < n"
        using edge_bounds x
        by (auto simp: mem_nbrs)
      note step = teq_filt_rule[OF cu rd[OF this]]
      show "<A acc acci * (F * ?W)> filt_imp (teq_imp C cu) Si u fi x acci
            <\<lambda> r. A (if c u = c x then f x acc else acc) r * (F * ?W)>"
        by (rule step, rule assms)
           (unfold nb set_filter mem_Collect_eq, rule conjI, rule x, assumption)
    qed
    show ?thesis
      unfolding nb foldl_filter_if[symmetric]
      by (rule ht_bind[OF r0], rule ht_pure_pre, rule ht_cons_post[OF x], assumption)
         (rule ent_true_drop(2), simp only: Gh gtx_def prod.case star_aci, rule ent_refl)
  qed
  show ?thesis
  proof(cases "u < n")
    case False
    show ?thesis
      unfolding Gh tnbs_def prod.case if_not_P[OF False] nbrs_tight_out[OF X False, folded Gh] foldl_Nil
      by sep_auto
  next
    case True
    note m = read_frame[OF read_frame[OF gtx_memb[OF True], where F = "A acc acci"], where F = F]
    note rd1 = read_frame[OF warr_nth[where c = c1 and C = C1], where F = "warr_assn n h c2 C2"]
    note rd2 = read_frame[OF warr_nth[where c = c2 and C = C2], where F = "warr_assn n h c1 C1",
      unfolded mult.commute[of "warr_assn n h c2 C2" "warr_assn n h c1 C1"]]
    show ?thesis
    proof(cases "u \<in> X")
      case uX: True
      show ?thesis
        unfolding Gh tnbs_def prod.case if_P[OF True]
        by (rule ht_bind[OF m[unfolded Gh]], rule ht_pure_pre)
           (simp only: uX if_True, rule main[OF True rd1, unfolded Gh], assumption,
            simp only: tight_nbrs uX if_True)
    next
      case nX: False
      show ?thesis
        unfolding Gh tnbs_def prod.case if_P[OF True]
        by (rule ht_bind[OF m[unfolded Gh]], rule ht_pure_pre)
           (simp only: nX if_False, rule main[OF True rd2, unfolded Gh], assumption,
            simp only: tight_nbrs nX if_False)
    qed
  qed
qed

text \<open>The BFS on the tight graph.\<close>

interpretation tb: csr_filtered_bfs n "wctx_es (csr.wtight_ctx X c1 c2)" tnbs "gtx X c1 c2"
proof(unfold_locales, goal_cases)
  case 1
  have "fst e < n" "snd e < n" if "e \<in> set (wctx_es (csr.wtight_ctx X c1 c2))" for e
    using edge_bounds[of "fst e" "snd e"] that
    by (auto simp: ctx_fields_n)
  then show ?case
    unfolding nbrs_map_edges dVs_eq
    by (intro Un_least image_subsetI) (simp_all only: lessThan_iff)
next
  case 2
  show ?case
    by (rule finite_nbrs_map_dom)
next
  case (3 u A fi f Gh acc acci)
  show ?case
    unfolding case_nbrs_map
    by (rule tnbs_rule[where F = emp, unfolded mult_1_right]) (rule 3(2)[unfolded case_nbrs_map])

qed

subsubsection \<open>The Steps of a Round\<close>

lemma srcs_eq: "csr.srcs (csr.exch_ctx X) = filter (\<lambda> y. y \<notin> X \<and> y \<in> S0 X) [0..<n]"
  by (simp only: csr.srcs_def in_ST ctx_parts filter_filter)

lemma set_srcs: "set (csr.srcs (csr.exch_ctx X)) = {y. y < n \<and> y \<notin> X \<and> y \<in> S0 X}"
  unfolding srcs_eq
  by auto

lemma set_tgts: "set (csr.tgts (csr.exch_ctx X)) = {y. y < n \<and> y \<notin> X \<and> y \<in> T0 X}"
  unfolding tgts_eq[symmetric]
  by auto

lemma src_ne: "\<lbrakk>y < n; y \<notin> X \<and> y \<in> S0 X\<rbrakk> \<Longrightarrow> csr.srcs (csr.exch_ctx X)
    \<noteq> []"
  unfolding srcs_eq filter_empty_conv
  by auto

lemma tgt_ne: "\<lbrakk>y < n; y \<notin> X \<and> y \<in> T0 X\<rbrakk> \<Longrightarrow> csr.tgts (csr.exch_ctx X)
    \<noteq> []"
  by (unfold tgts_eq[symmetric] filter_empty_conv) auto

text \<open>The unweighted steps on the solution and the oracles keep the weight arrays.\<close>

lemma src_max:
  assumes "y < n" "y \<notin> X \<and> y \<in> S0 X"
    "csr.srcs (csr.exch_ctx X) \<noteq> [] \<longrightarrow> h m = wctx_mS (csr.wtight_ctx X c1 c2)"
  shows "h m = wctx_mS (csr.wtight_ctx X c1 c2)"
  using assms src_ne[of y]
  by blast

lemma tgt_max:
  assumes "y < n" "y \<notin> X \<and> y \<in> T0 X"
    "csr.tgts (csr.exch_ctx X) \<noteq> [] \<longrightarrow> h m = wctx_mT (csr.wtight_ctx X c1 c2)"
  shows "h m = wctx_mT (csr.wtight_ctx X c1 c2)"
  using assms tgt_ne[of y]
  by blast

lemma gtx_frame:
  assumes "<B * gxs X Si Gc> c <\<lambda> r. B * gxs X Si Gc * \<up>(P r)>"
  shows "<B * gtx X c1 c2 (Si, Gc, C1, C2)> c
         <\<lambda> r. B * gtx X c1 c2 (Si, Gc, C1, C2) * \<up>(P r)>"
  unfolding gtx_def prod.case
  by (rule ht_frame_ac[OF assms, where R = "warr_assn n h c1 C1 * warr_assn n h c2 C2"])
     (simp only: star_aci, rule ent_refl)+

lemma gtx_lift:
  assumes "<gxs X Si Gc> c <\<lambda> r. gxs X Si Gc * \<up>(P r)>"
  shows "<gtx X c1 c2 (Si, Gc, C1, C2)> c <\<lambda> r. gtx X c1 c2 (Si, Gc, C1, C2) * \<up>(P r)>"
  by (rule gtx_frame[where B = emp, unfolded mult_1_left]) (rule assms)

lemma rd_c1: "y < n \<Longrightarrow> <gtx X c1 c2 (Si, Gc, C1, C2)> Array.nth C1 y
   <\<lambda> r. gtx X c1 c2 (Si, Gc, C1, C2) * \<up>(h r = c1 y)>"
  by (unfold gtx_def prod.case) (sep_auto heap: warr_nth)

lemma rd_c2: "y < n \<Longrightarrow> <gtx X c1 c2 (Si, Gc, C1, C2)> Array.nth C2 y
   <\<lambda> r. gtx X c1 c2 (Si, Gc, C1, C2) * \<up>(h r = c2 y)>"
  by (unfold gtx_def prod.case) (sep_auto heap: warr_nth)

text \<open>A read compared with a value in the reals.\<close>

lemma rd_eq:
  assumes "<G> Array.nth C y <\<lambda> r. G * \<up>(h r = b)>" "h m = a"
  shows "<G> Array.nth C y <\<lambda> r. G * \<up>((r = m) = (b = a))>"
  by (rule ht_cons_post[OF assms(1)])
     (sep_auto simp: h_eq_iff[symmetric] assms(2))

lemma foldr_max:
  "foldr (\<lambda> y a. if p y then Some (case a of None \<Rightarrow> g y | Some w \<Rightarrow> max w (g y)) else
    a) xs None =
   (if {y \<in> set xs. p y} = {} then None else Some (Max (g ` {y \<in> set xs. p y})))"
  unfolding set_filter[symmetric]
  by (induction xs) (auto simp add: Max_insert max.commute simp del: set_filter split: if_splits)

lemma max_imp_rule:
  assumes "\<And> y. y < n \<Longrightarrow> <G> P y <\<lambda> r. G * \<up>(r = p y)>"
    and "\<And> y. y < n \<Longrightarrow> <G> Array.nth C y <\<lambda> r. G * \<up>(h r = g y)>"
  shows "<G> max_imp P C <\<lambda> r. G * \<up>(map_option h r =
           (if {y. y < n \<and> p y} = {} then None else Some (Max (g ` {y. y < n \<and> p y}))))>"
proof-
  let ?f = "\<lambda> y a. if p y then Some (case a of None \<Rightarrow> g y | Some w \<Rightarrow> max w (g y)) else
    a"
  have step: "<\<up>(map_option h ai = a) * G> do { b \<leftarrow> P y; if b then do { x \<leftarrow> Array.nth C y;
    return (Some (case ai of None \<Rightarrow> x | Some w \<Rightarrow> max w x)) } else return ai }
              <\<lambda> r. \<up>(map_option h r = ?f y a) * G>" if "y < n" for y a ai
    by (sep_auto heap: assms(1)[OF that] assms(2)[OF that] split: option.splits)
  note r = foldr_range_imp_rule[where A = "\<lambda> a ai. \<up>(map_option h ai = a)" and i = n and g = ?f,
    OF step, simplified, where a = None and ai = None, folded max_imp_def]
  show ?thesis
    by (rule ht_cons_post[OF ht_cons_pre[OF _ r]]) (sep_auto simp: foldr_max)+
qed

lemma mS_rule:
  "<gtx X c1 c2 (Si, Gc, C1, C2)> max_imp (s_imp Si) C1
   <\<lambda> r. gtx X c1 c2 (Si, Gc, C1, C2) * \<up>(csr.srcs (csr.exch_ctx X) \<noteq> [] \<longrightarrow>
          h (case r of None \<Rightarrow> 0 | Some x \<Rightarrow> x) = wctx_mS (csr.wtight_ctx X c1 c2))>"
  by (rule ht_cons_post[OF max_imp_rule[OF gtx_lift[OF s_imp_rule[OF X]] rd_c1]])
     (sep_auto simp: ctx_fields_n list_max set_srcs[symmetric] split: option.splits if_splits)

lemma mT_rule:
  "<gtx X c1 c2 (Si, Gc, C1, C2)> max_imp (t_imp Si) C2
   <\<lambda> r. gtx X c1 c2 (Si, Gc, C1, C2) * \<up>(csr.tgts (csr.exch_ctx X) \<noteq> [] \<longrightarrow>
          h (case r of None \<Rightarrow> 0 | Some x \<Rightarrow> x) = wctx_mT (csr.wtight_ctx X c1 c2))>"
  by (rule ht_cons_post[OF max_imp_rule[OF gtx_lift[OF t_imp_rule[OF X]] rd_c2]])
     (sep_auto simp: ctx_fields_n list_max set_tgts[symmetric] split: option.splits if_splits)

lemma wst_imp_rule:
  assumes "y < n" and "csr.srcs (csr.exch_ctx X) \<noteq> [] \<longrightarrow> h mS = wctx_mS (csr.wtight_ctx X
    c1 c2)"
    and "csr.tgts (csr.exch_ctx X) \<noteq> [] \<longrightarrow> h mT = wctx_mT (csr.wtight_ctx X c1 c2)"
  shows "<gtx X c1 c2 (Si, Gc, C1, C2)> wst_imp Si C1 C2 mS mT y
         <\<lambda> r. gtx X c1 c2 (Si, Gc, C1, C2) * \<up>(r = (((y \<notin> X \<and> y \<in> S0 X) \<and>
                c1 y = wctx_mS (csr.wtight_ctx X c1 c2)) \<and> (y \<in> T0 X \<and> c2 y = wctx_mT (csr.wtight_ctx X
                  c1 c2))))>"
  unfolding wst_imp_def
  by (sep_auto heap: gtx_lift[OF st_imp_rule[OF X assms(1)]]
        rd_eq[OF rd_c1[OF assms(1)] src_max[OF assms(1) _ assms(2)]]
        rd_eq[OF rd_c2[OF assms(1)] tgt_max[OF assms(1) _ assms(3)]])

lemma thas_nb_rule:
  "<gtx X c1 c2 Gh> thas_nb_imp Gh y
   <\<lambda> r. gtx X c1 c2 Gh * \<up>(r = (nbrs (wctx_es (csr.wtight_ctx X c1 c2)) y \<noteq> []))>"
  unfolding thas_nb_imp_def
  by (rule ht_cons[OF _ _ tnbs_rule[where A = "\<lambda> b bi. \<up>(bi = b)" and F = emp
          and f = "\<lambda> x a. True"]]) (sep_auto simp: foldl_True)+

lemma nbrs_nonempty:
  "nbrs E u \<noteq> [] \<longleftrightarrow> (\<exists> v. (u, v) \<in> set E)"
  by (force simp: nbrs_def filter_empty_conv)

lemma htn_eq:
  assumes "y < n" "y \<notin> X \<and> y \<in> S0 X"
  shows "csr.has_tight_nb (csr.exch_ctx X) c2 y = (nbrs (wctx_es (csr.wtight_ctx X c1 c2)) y \<noteq> [])"
proof-
  have "y \<in> set (csr.srcs (csr.exch_ctx X))"
    using assms
    by (simp add: set_srcs)
  then show ?thesis
    unfolding ctx_fields nbrs_nonempty
    by (rule csr.has_tight_nb[OF X])
qed

lemma wsrc_imp_rule:
  assumes "y < n" and "csr.srcs (csr.exch_ctx X) \<noteq> [] \<longrightarrow> h mS = wctx_mS (csr.wtight_ctx X
    c1 c2)"
  shows "<gtx X c1 c2 (Si, Gc, C1, C2)> wsrc_imp (Si, Gc, C1, C2) mS y
         <\<lambda> r. gtx X c1 c2 (Si, Gc, C1, C2) * \<up>(r = (((y \<notin> X \<and> y \<in> S0 X) \<and>
                c1 y = wctx_mS (csr.wtight_ctx X c1 c2)) \<and> csr.has_tight_nb (csr.exch_ctx X) c2 y))>"
  unfolding wsrc_imp_def prod.case
  by (sep_auto heap: gtx_lift[OF s_imp_rule[OF X assms(1)]] thas_nb_rule
        rd_eq[OF rd_c1[OF assms(1)] src_max[OF assms(1) _ assms(2)]] simp: htn_eq[OF assms(1)])

lemma wtgt_imp_rule:
  assumes "y < n" and "csr.tgts (csr.exch_ctx X) \<noteq> [] \<longrightarrow> h mT = wctx_mT (csr.wtight_ctx X
    c1 c2)"
  shows "<bool_array_set_assn n V Vi * gtx X c1 c2 (Si, Gc, C1, C2)> wtgt_imp Si Vi C2 mT y
         <\<lambda> r. bool_array_set_assn n V Vi * gtx X c1 c2 (Si, Gc, C1, C2) * \<up>(r = (((y \<notin> X \<and> y
           \<in> T0 X) \<and>
                c2 y = wctx_mT (csr.wtight_ctx X c1 c2)) \<and> y \<in> V))>"
  unfolding wtgt_imp_def
  by (sep_auto heap: gtx_frame[OF is_tgt_imp_rule[OF X assms(1)]]
        rd_eq[OF rd_c2[OF assms(1)] tgt_max[OF assms(1) _ assms(2)]])

lemma foldr_ins: "foldr (\<lambda> y W. if P y then Set.insert y W else W) xs V = V \<union> {y \<in> set xs. P y}"
  by (induction xs) auto

lemma drop_imp_rule:
  assumes "csr.srcs (csr.exch_ctx X) \<noteq> [] \<longrightarrow> h mS = wctx_mS (csr.wtight_ctx X c1 c2)"
  shows "<bool_array_set_assn n V Vi * gtx X c1 c2 (Si, Gc, C1, C2)> drop_imp (Si, Gc, C1, C2) mS Vi
         <\<lambda> _. bool_array_set_assn n (V \<union> {y. y < n \<and> (((y \<notin> X \<and> y \<in> S0 X) \<and>
           c1 y = wctx_mS (csr.wtight_ctx X c1 c2)) \<and>
                \<not> csr.has_tight_nb (csr.exch_ctx X) c2 y)}) Vi * gtx X c1 c2 (Si, Gc, C1, C2)>"
proof-
  let ?P = "\<lambda> y. ((y \<notin> X \<and> y \<in> S0 X) \<and> c1 y = wctx_mS (csr.wtight_ctx X c1 c2)) \<and>
                 \<not> csr.has_tight_nb (csr.exch_ctx X) c2 y"
  have step: "<bool_array_set_assn n W Vi * gtx X c1 c2 (Si, Gc, C1, C2)> do { s \<leftarrow> s_imp Si y; if s then do
    { x \<leftarrow> Array.nth C1 y; if x = mS then do { e \<leftarrow> thas_nb_imp (Si, Gc, C1, C2) y; if e then
    return () else do { Array.upd y True Vi; return () } } else return () } else return () }
              <\<lambda> r. bool_array_set_assn n (if ?P y then Set.insert y W else W) Vi * gtx X c1 c2 (Si, Gc, C1,
                C2)>"
    if y: "y < n" for y W
  proof(cases "y \<notin> X \<and> y \<in> S0 X")
    case False
    show ?thesis
      by (rule ht_bind[OF ht_frame_ac[OF gtx_lift[OF s_imp_rule[OF X y]], where R = "bool_array_set_assn n W Vi"]],
          (simp only: star_aci, rule ent_refl), rule ent_refl, rule pure_mid) (sep_auto simp: False)
  next
    case True
    note hS = src_max[OF y True assms]
    show ?thesis
      by (rule ht_bind[OF ht_frame_ac[OF gtx_lift[OF s_imp_rule[OF X y]], where R = "bool_array_set_assn n W Vi"]],
          (simp only: star_aci, rule ent_refl), rule ent_refl, rule pure_mid, simp only: True simp_thms if_True)
         (sep_auto heap: rd_eq[OF rd_c1[OF y] hS] thas_nb_rule bool_array_set_upd_rule simp: y True htn_eq[OF y True])
  qed
  have "<bool_array_set_assn n V Vi * gtx X c1 c2 (Si, Gc, C1, C2)> drop_imp (Si, Gc, C1, C2) mS Vi
           <\<lambda> r. bool_array_set_assn n (foldr (\<lambda> y W. if ?P y then Set.insert y W else W) [0..<n] V)
             Vi *
                 gtx X c1 c2 (Si, Gc, C1, C2)>"
    unfolding drop_imp_def prod.case
    by (rule foldr_range_imp_rule[where A = "\<lambda> W u. bool_array_set_assn n W Vi"]) (rule step)
  then show ?thesis
    by (rule ht_cons_post) (sep_auto simp: foldr_ins)
qed

subsubsection \<open>A Round\<close>

text \<open>The context in terms of the ranges scanned by the code.\<close>

lemma path_char:
  "wctx_path (csr.wtight_ctx X c1 c2) =
     (case find (\<lambda> y. ((y \<notin> X \<and> y \<in> S0 X) \<and> c1 y = wctx_mS (csr.wtight_ctx X c1 c2)) \<and>
                      (y \<in> T0 X \<and> c2 y = wctx_mT (csr.wtight_ctx X c1 c2))) [0..<n] of
        Some s \<Rightarrow> Some [s]
      | None \<Rightarrow> (if filter (\<lambda> y. ((y \<notin> X \<and> y \<in> S0 X) \<and> c1 y = wctx_mS
        (csr.wtight_ctx X c1 c2)) \<and>
                              csr.has_tight_nb (csr.exch_ctx X) c2 y) [0..<n] = [] then None
                 else csr.target_path (nbrs_map (wctx_es (csr.wtight_ctx X c1 c2)))
                        (filter (\<lambda> y. ((y \<notin> X \<and> y \<in> S0 X) \<and> c1 y = wctx_mS
                          (csr.wtight_ctx X c1 c2)) \<and>
                                   csr.has_tight_nb (csr.exch_ctx X) c2 y) [0..<n])
                        (wctx_tb (csr.wtight_ctx X c1 c2))))"
  by (simp only: csr.wtight_ctx_path[OF X] Let_def ctx_fields srcs_eq in_ST filter_filter
        find_filter conj_assoc)

lemma R_char:
  "set (wctx_R (csr.wtight_ctx X c1 c2)) =
     {y. y < n \<and> ((y \<notin> X \<and> y \<in> S0 X) \<and> c1 y = wctx_mS (csr.wtight_ctx X c1 c2)) \<and>
         \<not> csr.has_tight_nb (csr.exch_ctx X) c2 y} \<union>
     (if filter (\<lambda> y. ((y \<notin> X \<and> y \<in> S0 X) \<and> c1 y = wctx_mS (csr.wtight_ctx X c1 c2)) \<and>
                    csr.has_tight_nb (csr.exch_ctx X) c2 y) [0..<n] = [] then {}
      else set (BFS_dist_state.visited (csr.bfs_final (nbrs_map (wctx_es (csr.wtight_ctx X c1 c2)))
                  (filter (\<lambda> y. ((y \<notin> X \<and> y \<in> S0 X) \<and> c1 y = wctx_mS (csr.wtight_ctx X c1
                    c2)) \<and>
                             csr.has_tight_nb (csr.exch_ctx X) c2 y) [0..<n]))))"
  by (simp only: csr.wtight_ctx_R[OF X] Let_def ctx_fields srcs_eq
        filter_filter foldr_conv_fold fold_Cons_rev rev_rev_ident set_append conj_assoc; auto)

lemma tb_find:
  "find P (wctx_tb (csr.wtight_ctx X c1 c2)) =
   find (\<lambda> y. ((y \<notin> X \<and> y \<in> T0 X) \<and> c2 y = wctx_mT (csr.wtight_ctx X c1 c2)) \<and> P y)
     [0..<n]"
  by (simp only: ctx_fields tgts_eq[symmetric] filter_filter find_filter)

lemma tbfs_ok:
  assumes "filter (\<lambda> y. ((y \<notin> X \<and> y \<in> S0 X) \<and> c1 y = wctx_mS (csr.wtight_ctx X c1 c2))
    \<and>
                        csr.has_tight_nb (csr.exch_ctx X) c2 y) [0..<n] \<noteq> []"
  shows "tb.bfs_sources
           (filter (\<lambda> y. ((y \<notin> X \<and> y \<in> S0 X) \<and> c1 y = wctx_mS (csr.wtight_ctx X c1 c2))
             \<and>
                      csr.has_tight_nb (csr.exch_ctx X) c2 y) [0..<n])"
  unfolding tb.bfs_sources_def nbrs_map_edges
proof(intro conjI subsetI, goal_cases)
  case 1
  show ?case
    by simp
next
  case 2
  show ?case
    by (rule assms)
next
  case (3 u)
  then have "nbrs (wctx_es (csr.wtight_ctx X c1 c2)) u \<noteq> []"
    using htn_eq
    by auto
  then show ?case
    by (auto simp: nbrs_nonempty intro: dVsI(1))
qed

lemma tfin_eq:
  "tb.bfs_sources ss \<Longrightarrow> csr.bfs_final (nbrs_map (wctx_es (csr.wtight_ctx X c1 c2))) ss = tb.fin ss"
  unfolding csr.bfs_final_def
  by (simp only: tb.fin_def)

lemma wsearch_single:
  assumes "csr.srcs (csr.exch_ctx X) \<noteq> [] \<longrightarrow> h mS = wctx_mS (csr.wtight_ctx X c1 c2)"
    and "csr.tgts (csr.exch_ctx X) \<noteq> [] \<longrightarrow> h mT = wctx_mT (csr.wtight_ctx X c1 c2)"
  shows "<gtx X c1 c2 (Si, Gc, C1, C2) * F> find_range_imp (wst_imp Si C1 C2 mS mT) 0 n
         <\<lambda> r. gtx X c1 c2 (Si, Gc, C1, C2) * F * \<up>(r = find (\<lambda> y. ((y \<notin> X \<and> y \<in>
           S0 X) \<and>
                c1 y = wctx_mS (csr.wtight_ctx X c1 c2)) \<and> (y \<in> T0 X \<and> c2 y = wctx_mT (csr.wtight_ctx X
                  c1 c2))) [0..<n])>"
  by (rule find_range_imp_rule, rule read_frame, rule wst_imp_rule[OF _ assms]) assumption

lemma wsearch_collect:
  assumes "csr.srcs (csr.exch_ctx X) \<noteq> [] \<longrightarrow> h mS = wctx_mS (csr.wtight_ctx X c1 c2)"
  shows "<len_assn (Suc n) Fr * gtx X c1 c2 (Si, Gc, C1, C2)> collect_range_imp (wsrc_imp (Si, Gc, C1, C2) mS) n Fr
         <\<lambda> k. \<exists>\<^sub>A fl'. Fr \<mapsto>\<^sub>a fl' * gtx X c1 c2 (Si, Gc, C1, C2) * \<up>(length
           fl' = Suc n \<and>
               k = length (filter (\<lambda> y. ((y \<notin> X \<and> y \<in> S0 X) \<and> c1 y = wctx_mS
                 (csr.wtight_ctx X c1 c2)) \<and>
                     csr.has_tight_nb (csr.exch_ctx X) c2 y) [0..<n]) \<and>
               take k fl' = filter (\<lambda> y. ((y \<notin> X \<and> y \<in> S0 X) \<and> c1 y = wctx_mS
                 (csr.wtight_ctx X c1 c2)) \<and>
                     csr.has_tight_nb (csr.exch_ctx X) c2 y) [0..<n])>"
proof(rule pull_len, goal_cases)
  case (1 fl)
  show ?case
    unfolding 1[symmetric]
    by (rule collect_range_imp_rule[OF wsrc_imp_rule[OF _ assms]]) (simp_all add: 1)
qed

lemma wsearch_bfs:
  assumes "csr.tgts (csr.exch_ctx X) \<noteq> [] \<longrightarrow> h mT = wctx_mT (csr.wtight_ctx X c1 c2)"
    and "tb.bfs_sources ss"
    and "length fl = Suc n" "take (length ss) fl = ss"
  shows "<gtx X c1 c2 (Si, Gc, C1, C2) * bool_array_set_assn n {} Vi * Fr \<mapsto>\<^sub>a fl * len_assn (Suc n) Bf *
    len_assn n Da *
          len_assn n Pa>
           do { fill_range_imp id n Da; tbfs_run (Si, Gc, C1, C2) Vi (Fr, length ss, Bf) Da Pa;
                find_range_imp (wtgt_imp Si Vi C2 mT) 0 n }
         <\<lambda> t. gtx X c1 c2 (Si, Gc, C1, C2) *
               bool_array_set_assn n (set (BFS_dist_state.visited (tb.fin ss))) Vi *
               BFS_subprocedures_lists.imp_dist_assn n Da (nbrs_map (wctx_es (csr.wtight_ctx X c1 c2)))
                 (BFS_dist_state.dists (tb.fin ss)) Da *
               parent_array.pa_parent_assn n (BFS_par_state.parent (tb.fin ss)) Pa *
               len_assn (Suc n) Fr * len_assn (Suc n) Bf *
               \<up>(t = find (\<lambda> y. y \<in> set (BFS_dist_state.visited (tb.fin ss))) (wctx_tb (csr.wtight_ctx
                 X c1 c2)))>"
proof-
  let ?G = "gtx X c1 c2 (Si, Gc, C1, C2)"
  let ?V = "set (BFS_dist_state.visited (tb.fin ss))"
  let ?DP = "BFS_subprocedures_lists.imp_dist_assn n Da (nbrs_map (wctx_es (csr.wtight_ctx X c1 c2)))
               (BFS_dist_state.dists (tb.fin ss)) Da *
             parent_array.pa_parent_assn n (BFS_par_state.parent (tb.fin ss)) Pa *
             len_assn (Suc n) Fr * len_assn (Suc n) Bf"
  note w = read_frame[OF wtgt_imp_rule[of _ mT ?V Vi Si Gc C1 C2, OF _ assms(1)], where F = ?DP]
  note f = find_range_imp_rule[where i = 0 and n = n and P = "wtgt_imp Si Vi C2 mT", OF w,
    unfolded le0, folded tb_find[where P = "\<lambda> y. y \<in> ?V"]]
  show ?thesis
    unfolding tbfs_run_def
    by (rule ht_bind[OF ht_frame_ac[OF fill_len[where a = Da and f = id],
            where R = "?G * bool_array_set_assn n {} Vi * Fr \<mapsto>\<^sub>a fl * len_assn (Suc n) Bf * len_assn n
              Pa"]],
        (simp only: star_aci, rule ent_refl), rule ent_refl,
        rule ht_bind[OF ht_cons_pre[OF _ tb.bfs_len_rule[OF assms(2-4), where Bf = Bf and Vi = Vi and Fr = Fr and
            Da = Da and Pa = Pa and Gh = "(Si, Gc, C1, C2)"]]],
        (simp only: star_aci, rule ent_refl),
        rule ht_cons_pre[OF _ ht_cons_post[OF f]])
       sep_auto+
qed

lemma wsearch_rest:
  assumes "csr.srcs (csr.exch_ctx X) \<noteq> [] \<longrightarrow> h mS = wctx_mS (csr.wtight_ctx X c1 c2)"
    and "csr.tgts (csr.exch_ctx X) \<noteq> [] \<longrightarrow> h mT = wctx_mT (csr.wtight_ctx X c1 c2)"
    and "find (\<lambda> y. ((y \<notin> X \<and> y \<in> S0 X) \<and> c1 y = wctx_mS (csr.wtight_ctx X c1 c2))
      \<and>
                 (y \<in> T0 X \<and> c2 y = wctx_mT (csr.wtight_ctx X c1 c2))) [0..<n] = None"
    and "length fl = Suc n"
      "k = length (filter (\<lambda> y. ((y \<notin> X \<and> y \<in> S0 X) \<and> c1 y = wctx_mS (csr.wtight_ctx X c1
        c2)) \<and>
             csr.has_tight_nb (csr.exch_ctx X) c2 y) [0..<n])"
      "take k fl = filter (\<lambda> y. ((y \<notin> X \<and> y \<in> S0 X) \<and> c1 y = wctx_mS (csr.wtight_ctx X c1
        c2)) \<and>
             csr.has_tight_nb (csr.exch_ctx X) c2 y) [0..<n]"
  shows "<Fr \<mapsto>\<^sub>a fl * gtx X c1 c2 (Si, Gc, C1, C2) *
          (len_assn n Vi * len_assn (Suc n) Bf * len_assn n Da * len_assn n Pa)>
           do { bool_array_set_clear_imp n Vi;
                t \<leftarrow> (if k = 0 then return None else do { fill_range_imp id n Da;
                       tbfs_run (Si, Gc, C1, C2) Vi (Fr, k, Bf) Da Pa; find_range_imp (wtgt_imp Si Vi C2 mT) 0 n });
                (case t of Some t \<Rightarrow> return (2 :: nat, t)
                 | None \<Rightarrow> do { drop_imp (Si, Gc, C1, C2) mS Vi; return (0 :: nat, 0) }) }
         <\<lambda> t. gtx X c1 c2 (Si, Gc, C1, C2) * len_assn (Suc n) Fr * len_assn (Suc n) Bf *
               wpath_assn Vi Da Pa t (csr.wtight_ctx X c1 c2)>"
proof-
  let ?ss = "filter (\<lambda> y. ((y \<notin> X \<and> y \<in> S0 X) \<and> c1 y = wctx_mS (csr.wtight_ctx X c1 c2))
    \<and>
                         csr.has_tight_nb (csr.exch_ctx X) c2 y) [0..<n]"
  let ?D = "{y. y < n \<and> (((y \<notin> X \<and> y \<in> S0 X) \<and> c1 y = wctx_mS (csr.wtight_ctx X c1 c2)) \<and>
                \<not> csr.has_tight_nb (csr.exch_ctx X) c2 y)}"
  let ?G = "gtx X c1 c2 (Si, Gc, C1, C2)"
  have cl: "<Fr \<mapsto>\<^sub>a fl * ?G * (len_assn n Vi * len_assn (Suc n) Bf * len_assn n Da * len_assn n Pa)>
              bool_array_set_clear_imp n Vi
            <\<lambda> _. bool_array_set_assn n {} Vi * (Fr \<mapsto>\<^sub>a fl * ?G * len_assn (Suc n) Bf * len_assn
              n Da * len_assn n Pa)>"
    by (rule ht_frame_ac[OF clear_len[where Vi = Vi],
          where R = "Fr \<mapsto>\<^sub>a fl * ?G * len_assn (Suc n) Bf * len_assn n Da * len_assn n Pa"])
       (simp only: star_aci, rule ent_refl)+
  show ?thesis
  proof(cases "?ss = []")
    case True
    note k = assms(5)[unfolded True list.size]
    note p = path_char[unfolded assms(3) option.case(1) if_P[OF True]]
    have d: "<bool_array_set_assn n {} Vi * (Fr \<mapsto>\<^sub>a fl * ?G * len_assn (Suc n) Bf * len_assn n Da *
      len_assn n Pa)>
               drop_imp (Si, Gc, C1, C2) mS Vi
             <\<lambda> _. bool_array_set_assn n ({} \<union> ?D) Vi * ?G * (Fr \<mapsto>\<^sub>a fl * len_assn (Suc
               n) Bf * len_assn n Da * len_assn n Pa)>"
      by (rule ht_frame_ac[OF drop_imp_rule[OF assms(1)],
            where R = "Fr \<mapsto>\<^sub>a fl * len_assn (Suc n) Bf * len_assn n Da * len_assn n Pa"])
         (simp only: star_aci, rule ent_refl)+
    show ?thesis
      unfolding k
      by (rule ht_bind[OF cl], simp only: if_P[OF refl] return_bind option.case(1),
          rule ht_bind[OF d], rule ht_cons_pre[OF _ ht_return_wp],
          unfold wpath_assn_def p option.case(1) fst_conv len_assn_def R_char if_P[OF True])
         (sep_auto simp: assms(4))
  next
    case False
    note b = tbfs_ok[OF False]
    note tk = assms(6)[unfolded assms(5)]
    note nonempty = if_not_P[OF False[folded length_0_conv]]
    note fin = tfin_eq[OF b]
    let ?fin = "tb.fin ?ss"
    let ?V = "set (BFS_dist_state.visited ?fin)"
    let ?DP = "BFS_subprocedures_lists.imp_dist_assn n Da (nbrs_map (wctx_es (csr.wtight_ctx X c1 c2)))
                 (BFS_dist_state.dists ?fin) Da *
               parent_array.pa_parent_assn n (BFS_par_state.parent ?fin) Pa"
    have p: "wctx_path (csr.wtight_ctx X c1 c2) =
             (case find (\<lambda> y. y \<in> ?V) (wctx_tb (csr.wtight_ctx X c1 c2)) of
                None \<Rightarrow> None
              | Some t \<Rightarrow> Some (rev (parent_array.pa_get_path n (BFS_par_state.parent ?fin) t)))"
      unfolding path_char assms(3) option.case(1) if_not_P[OF False] csr.target_path_def Let_def fin
      unfolding length_upt diff_zero ..
    have bf: "<bool_array_set_assn n {} Vi * (Fr \<mapsto>\<^sub>a fl * ?G * len_assn (Suc n) Bf * len_assn n Da *
      len_assn n Pa)>
                do { fill_range_imp id n Da; tbfs_run (Si, Gc, C1, C2) Vi (Fr, length ?ss, Bf) Da Pa;
                     find_range_imp (wtgt_imp Si Vi C2 mT) 0 n }
              <\<lambda> t. ?G * bool_array_set_assn n ?V Vi * ?DP * len_assn (Suc n) Fr * len_assn (Suc n) Bf *
                    \<up>(t = find (\<lambda> y. y \<in> ?V) (wctx_tb (csr.wtight_ctx X c1 c2)))>"
      by (rule ht_cons_pre[OF _ ht_cons_post[OF wsearch_bfs[OF assms(2) b assms(4) tk]]])
         ((simp only: star_aci, rule ent_refl) | (rule ent_true_drop(2), simp only: star_aci, rule ent_refl))+
    show ?thesis
    proof(cases "find (\<lambda> y. y \<in> ?V) (wctx_tb (csr.wtight_ctx X c1 c2))")
      case (Some t)
      note pS = p[unfolded Some option.case(2)]
      have e: "bool_array_set_assn n ?V Vi * ?DP \<Longrightarrow>\<^sub>A wpath_assn Vi Da Pa (2 :: nat, t)
        (csr.wtight_ctx X c1 c2)"
        unfolding wpath_assn_def pS option.case(2) fst_conv snd_conv numeral_eq_one_iff eq_num_simps if_False
        by (rule ent_star_mono[OF bool_array_set_len], rule ent_ex_postI[where x = ?ss]) (use b Some in sep_auto)
      show ?thesis
        unfolding assms(5)
        by (rule ht_bind[OF cl], simp only: nonempty,
            rule ht_bind[OF bf], rule ht_pure_pre, simp only: Some option.case(2),
            rule ht_cons_pre[OF _ ht_return_wp],
            rule ent_trans[where Q = "(bool_array_set_assn n ?V Vi * ?DP) *
              (?G * len_assn (Suc n) Fr * len_assn (Suc n) Bf)"],
            simp only: star_aci, rule ent_refl,
            rule ent_trans[OF ent_star_mono[OF e ent_refl]], simp only: star_aci, rule ent_refl)
    next
      case None
      note pN = p[unfolded None option.case(1)]
      have d: "<bool_array_set_assn n ?V Vi * (?G * ?DP * len_assn (Suc n) Fr * len_assn (Suc n) Bf)> drop_imp (Si,
        Gc, C1, C2) mS Vi
               <\<lambda> _. bool_array_set_assn n (?V \<union> ?D) Vi * ?G * (?DP * len_assn (Suc n) Fr * len_assn
                 (Suc n) Bf)>"
        by (rule ht_frame_ac[OF drop_imp_rule[OF assms(1), where V = ?V],
              where R = "?DP * len_assn (Suc n) Fr * len_assn (Suc n) Bf"])
           (simp only: star_aci, rule ent_refl)+
      note dp = ent_star_mono[OF tb.dist_len tb.par_len]
      show ?thesis
        unfolding assms(5)
        by (rule ht_bind[OF cl], simp only: nonempty,
            rule ht_bind[OF bf], rule ht_pure_pre, simp only: None option.case(1),
            rule ht_bind[OF ht_cons_pre[OF _ d]], simp only: star_aci, rule ent_refl,
            rule ht_cons_pre[OF _ ht_return_wp],
            unfold wpath_assn_def pN option.case(1) fst_conv R_char if_not_P[OF False] fin,
            rule ent_trans[OF ent_star_mono[OF ent_refl ent_star_mono[OF ent_star_mono[OF dp ent_refl] ent_refl]]])
           (sep_auto simp: Un_commute)
    qed
  qed
qed

lemma wsearch_rule:
  assumes "csr.srcs (csr.exch_ctx X) \<noteq> [] \<longrightarrow> h mS = wctx_mS (csr.wtight_ctx X c1 c2)"
    and "csr.tgts (csr.exch_ctx X) \<noteq> [] \<longrightarrow> h mT = wctx_mT (csr.wtight_ctx X c1 c2)"
  shows "<gtx X c1 c2 (Si, Gc, C1, C2) * work_assn n Vi Fr Bf Da Pa> wsearch_imp Gc Vi Fr Bf Da Pa Si C1 C2 mS mT
         <\<lambda> t. gtx X c1 c2 (Si, Gc, C1, C2) * len_assn (Suc n) Fr * len_assn (Suc n) Bf *
               wpath_assn Vi Da Pa t (csr.wtight_ctx X c1 c2)>"
proof(cases "find (\<lambda> y. ((y \<notin> X \<and> y \<in> S0 X) \<and> c1 y = wctx_mS (csr.wtight_ctx X c1 c2))
    \<and>
                 (y \<in> T0 X \<and> c2 y = wctx_mT (csr.wtight_ctx X c1 c2))) [0..<n]")
  case (Some s)
  note s = find_SomeD[OF Some, simplified]
  note p = path_char[unfolded Some option.case(2)]
  show ?thesis
    unfolding wsearch_imp_def
    by (rule ht_bind[OF wsearch_single[OF assms, where F = "work_assn n Vi Fr Bf Da Pa"]], rule ht_pure_pre,
        simp only: Some option.case(2), rule ht_cons_pre[OF _ ht_return_wp])
       (sep_auto simp: wpath_assn_def p[unfolded length_upt diff_zero] work_assn_def s)
next
  case None
  show ?thesis
    unfolding wsearch_imp_def
    by (rule ht_bind[OF wsearch_single[OF assms, where F = "work_assn n Vi Fr Bf Da Pa"]], rule ht_pure_pre,
        simp only: None option.case(1),
        rule ht_bind[OF ht_frame_ac[OF wsearch_collect[OF assms(1)],
          where R = "len_assn n Vi * len_assn (Suc n) Bf * len_assn n Da * len_assn n Pa"]],
        (simp only: work_assn_def star_aci, rule ent_refl), rule ent_refl,
        rule ex_mid, rule pure_mid, elim conjE, rule wsearch_rest[OF assms None]) assumption+
qed

lemma wctx_intro:
  assumes "length L = 2" "length M = 2"
    "csr.srcs (csr.exch_ctx X) \<noteq> [] \<longrightarrow> h (M ! 0) = wctx_mS (csr.wtight_ctx X c1 c2)"
    "csr.tgts (csr.exch_ctx X) \<noteq> [] \<longrightarrow> h (M ! 1) = wctx_mT (csr.wtight_ctx X c1 c2)"
  shows "Ti \<mapsto>\<^sub>a L * Mi \<mapsto>\<^sub>a M * len_assn (Suc n) Fr * len_assn (Suc n) Bf *
         wpath_assn Vi Da Pa (L ! 0, L ! 1) (csr.wtight_ctx X c1 c2)
         \<Longrightarrow>\<^sub>A wctx_assn Vi Fr Bf Da Pa Mi Ti (csr.wtight_ctx X c1 c2)"
  unfolding wctx_assn_def ctx_fields
  by (rule ent_ex_postI[where x = M], rule ent_ex_postI[where x = L])
     (use assms[unfolded ctx_fields] in sep_auto)

lemma wtight_ctx_tail_raw:
  assumes "csr.srcs (csr.exch_ctx X) \<noteq> [] \<longrightarrow> h mS = wctx_mS (csr.wtight_ctx X c1 c2)"
    and "csr.tgts (csr.exch_ctx X) \<noteq> [] \<longrightarrow> h mT = wctx_mT (csr.wtight_ctx X c1 c2)"
    and "length lm = 2" "length lt = 2"
  shows "<gtx X c1 c2 (Si, Gc, C1, C2) * work_assn n Vi Fr Bf Da Pa * Mi \<mapsto>\<^sub>a lm * Ti \<mapsto>\<^sub>a lt>
           do { Array.upd 0 mS Mi; Array.upd 1 mT Mi; t \<leftarrow> wsearch_imp Gc Vi Fr Bf Da Pa Si C1 C2 mS mT;
                Array.upd 0 (fst t) Ti; Array.upd 1 (snd t) Ti; return () }
         <\<lambda> _. \<exists>\<^sub>A a b. Ti \<mapsto>\<^sub>a list_update (list_update lt 0 a) 1 b * gtx X c1 c2
           (Si, Gc, C1, C2) *
               len_assn (Suc n) Fr * len_assn (Suc n) Bf * wpath_assn Vi Da Pa (a, b) (csr.wtight_ctx X c1 c2) *
               Mi \<mapsto>\<^sub>a list_update (list_update lm 0 mS) 1 mT>"
  by (sep_auto heap: wsearch_rule[OF assms(1) assms(2)] simp: assms(3,4))

lemma wtight_ctx_tail:
  assumes "csr.srcs (csr.exch_ctx X) \<noteq> [] \<longrightarrow> h mS = wctx_mS (csr.wtight_ctx X c1 c2)"
    and "csr.tgts (csr.exch_ctx X) \<noteq> [] \<longrightarrow> h mT = wctx_mT (csr.wtight_ctx X c1 c2)"
    and "length lm = 2" "length lt = 2"
  shows "<gtx X c1 c2 (Si, Gc, C1, C2) * work_assn n Vi Fr Bf Da Pa * Mi \<mapsto>\<^sub>a lm * Ti \<mapsto>\<^sub>a lt>
           do { Array.upd 0 mS Mi; Array.upd 1 mT Mi; t \<leftarrow> wsearch_imp Gc Vi Fr Bf Da Pa Si C1 C2 mS mT;
                Array.upd 0 (fst t) Ti; Array.upd 1 (snd t) Ti; return () }
         <\<lambda> _. gtx X c1 c2 (Si, Gc, C1, C2) * wctx_assn Vi Fr Bf Da Pa Mi Ti (csr.wtight_ctx X c1 c2)>"
proof(rule ht_cons_post[OF wtight_ctx_tail_raw[OF assms]], rule ent_ex_preI, rule ent_ex_preI, goal_cases)
  case (1 r a b)
  show ?case
    unfolding wctx_assn_def ex_assn_move_out ctx_fields
    by (rule ent_ex_postI[where x = "list_update (list_update lm 0 mS) 1 mT"],
        rule ent_ex_postI[where x = "list_update (list_update lt 0 a) 1 b"])
       (sep_auto simp: assms[unfolded ctx_fields])
qed

text \<open>The context of a round, as specified in the loop: (C).\<close>

lemma wtight_ctx_imp_rule:
  "<gtx X c1 c2 (Si, Gc, C1, C2) * wws Vi Fr Bf Da Pa Mi Ti> wtight_ctx_imp Gc Vi Fr Bf Da Pa Mi Ti Si C1 C2
   <\<lambda> _. gtx X c1 c2 (Si, Gc, C1, C2) * wctx_assn Vi Fr Bf Da Pa Mi Ti (csr.wtight_ctx X c1 c2)>"
proof-
  have main: "<gtx X c1 c2 (Si, Gc, C1, C2) * work_assn n Vi Fr Bf Da Pa * Mi \<mapsto>\<^sub>a lm * Ti
    \<mapsto>\<^sub>a lt>
                wtight_ctx_imp Gc Vi Fr Bf Da Pa Mi Ti Si C1 C2
              <\<lambda> _. gtx X c1 c2 (Si, Gc, C1, C2) * wctx_assn Vi Fr Bf Da Pa Mi Ti (csr.wtight_ctx X c1 c2)>"
    if l: "length lm = 2" "length lt = 2" for lm lt
    unfolding wtight_ctx_imp_def Let_def
    by (rule ht_bind[OF ht_frame_ac[OF mS_rule[of Si Gc C1 C2],
          where R = "work_assn n Vi Fr Bf Da Pa * Mi \<mapsto>\<^sub>a lm * Ti \<mapsto>\<^sub>a lt"]],
        (simp only: star_aci, rule ent_refl), rule ent_refl, rule pure_mid,
        rule ht_bind[OF ht_frame_ac[OF mT_rule[of Si Gc C1 C2],
          where R = "work_assn n Vi Fr Bf Da Pa * Mi \<mapsto>\<^sub>a lm * Ti \<mapsto>\<^sub>a lt"]],
        (simp only: star_aci, rule ent_refl), rule ent_refl, rule pure_mid)
       (rule ht_cons_pre[OF _ wtight_ctx_tail[OF _ _ l]], (simp only: star_aci, rule ent_refl), assumption+)
  show ?thesis
    unfolding wws_def len_assn_def
    by (sep_auto heap: main)
qed

text \<open>The path of the context: (P).\<close>

lemma ti_reads:
  assumes "length ti = 2"
    and "<Ti \<mapsto>\<^sub>a ti * F> (if ti ! 0 = 1 then do { Array.upd 0 (ti ! 1) Ra; return (Some 1) }
              else if ti ! 0 = 2 then do { l \<leftarrow> bfs_path Pa Ra (ti ! 1); return (Some l) } else return None)
                <Q>"
  shows "<Ti \<mapsto>\<^sub>a ti * F> wctx_path_imp Pa Ti Ra <Q>"
proof-
  note r = read_frame[OF nth_rule[where a = Ti and xs = ti], where F = F]
  show ?thesis
    unfolding wctx_path_imp_def
    by (rule ht_bind[OF r], rule ht_pure_pre, elim conjE,
        rule ht_bind[OF r], rule ht_pure_pre, elim conjE) (simp only: assms(2))
qed

lemma wctx_path_cases:
  assumes "length ti = 2"
  shows "<Ti \<mapsto>\<^sub>a ti * (wpath_assn Vi Da Pa (ti ! 0, ti ! 1) (csr.wtight_ctx X c1 c2) * parr_assn n Ra)>
           (if ti ! 0 = 1 then do { Array.upd 0 (ti ! 1) Ra; return (Some 1) }
            else if ti ! 0 = 2 then do { l \<leftarrow> bfs_path Pa Ra (ti ! 1); return (Some l) } else return None)
         <\<lambda> r. Ti \<mapsto>\<^sub>a ti * wpath_assn Vi Da Pa (ti ! 0, ti ! 1) (csr.wtight_ctx X c1 c2) *
               path_assn n (wctx_path (csr.wtight_ctx X c1 c2)) r Ra>"
proof(cases "wctx_path (csr.wtight_ctx X c1 c2)")
  case None
  show ?thesis
    unfolding wpath_assn_def None option.case(1) fst_conv
    by (sep_auto simp: path_None)
next
  case (Some p)
  show ?thesis
  proof(cases "ti ! 0 = 1")
    case True
    show ?thesis
      unfolding wpath_assn_def Some option.case(2) fst_conv snd_conv if_P[OF True]
      by (sep_auto heap: single_path_rule[OF X] simp: True)
  next
    case False
    show ?thesis
      unfolding wpath_assn_def Some option.case(2) fst_conv snd_conv if_not_P[OF False]
      by (sep_auto heap: tb.path_len_rule simp: False)
  qed
qed

lemma wctx_path_imp_rule:
  "<wctx_assn Vi Fr Bf Da Pa Mi Ti (csr.wtight_ctx X c1 c2) * parr_assn n Ra> wctx_path_imp Pa Ti Ra
   <\<lambda> r. wctx_assn Vi Fr Bf Da Pa Mi Ti (csr.wtight_ctx X c1 c2) *
         path_assn n (wctx_path (csr.wtight_ctx X c1 c2)) r Ra>"
  unfolding wctx_assn_def
  by (sep_auto heap: ti_reads[OF _ wctx_path_cases])

subsubsection \<open>The Minimum Gap\<close>

lemma gap_rule:
  assumes "u < n" "v < n"
  shows "<\<up>(map_option h ai = a) * (F * (bool_array_set_assn n V Vi * warr_assn n h c1 C1 * warr_assn n h c2 C2))>
           gap_imp C1 C2 (u \<in> X) Vi u v ai
         <\<lambda> r. \<up>(map_option h r = (if v \<notin> V then eps_min a (if u \<in> X then c1 u - c1 v else c2 v
           - c2 u)
                                  else a)) *
               (F * (bool_array_set_assn n V Vi * warr_assn n h c1 C1 * warr_assn n h c2 C2))>"
  unfolding gap_imp_def
  by (sep_auto heap: bool_array_set_memb_rule warr_nth simp: assms eps_min_h)

text \<open>The gaps of the exchange edges leaving an element.\<close>

lemma edge_part:
  assumes "u < n"
  shows "<gxs X Si Gc * \<up>(map_option h ai = a) *
          (bool_array_set_assn n V Vi * warr_assn n h c1 C1 * warr_assn n h c2 C2)>
           xnbs (Si, Gc) u (gap_imp C1 C2 (u \<in> X) Vi u) ai
         <\<lambda> r. gxs X Si Gc * (bool_array_set_assn n V Vi * warr_assn n h c1 C1 * warr_assn n h c2 C2) *
               \<up>(map_option h r = eps_of ((\<lambda> v. if u \<in> X then c1 u - c1 v else c2 v - c2 u) `
                                           {v \<in> set (nbrs (EE X) u). v \<notin> V}) a)>"
proof-
  have fi: "<\<up>(map_option h acci = acc) * (bool_array_set_assn n V Vi * warr_assn n h c1 C1 * warr_assn n h c2 C2)>
              gap_imp C1 C2 (u \<in> X) Vi u x acci
            <\<lambda> r. \<up>(map_option h r = (if x \<notin> V then eps_min acc (if u \<in> X then c1 u - c1 x else
              c2 x - c2 u)
                                     else acc)) *
                  (bool_array_set_assn n V Vi * warr_assn n h c1 C1 * warr_assn n h c2 C2)>"
    if "x \<in> set (nbrs (EE X) u)" for acc acci x
  proof-
    have "x < n"
      using edge_bounds that
      by (auto simp: mem_nbrs)
    note rule = gap_rule[OF assms this, where F = emp and V = V and Vi = Vi and ai = acci and a = acc,
      unfolded mult_1_left]
    show ?thesis
      by (rule rule)
  qed
  show ?thesis
    by (rule ht_cons_post[OF xnbs_rule[OF X, where A = "\<lambda> a ai. \<up>(map_option h ai = a)"
          and F = "bool_array_set_assn n V Vi * warr_assn n h c1 C1 * warr_assn n h c2 C2"
          and f = "\<lambda> v a. if v \<notin> V then eps_min a (if u \<in> X then c1 u - c1 v else c2 v - c2 u) else
            a"
          and u = u and fi = "gap_imp C1 C2 (u \<in> X) Vi u", OF fi]], assumption)
       (simp only: foldl_eps_of, rule ent_true_drop(2), rule ent_refl)
qed

text \<open>One element contributes the gaps of its edges, as a source and as a target.\<close>

lemma weps_step_rule:
  assumes "u < n"
    and "csr.srcs (csr.exch_ctx X) \<noteq> [] \<longrightarrow> h mS = wctx_mS (csr.wtight_ctx X c1 c2)"
    and "csr.tgts (csr.exch_ctx X) \<noteq> [] \<longrightarrow> h mT = wctx_mT (csr.wtight_ctx X c1 c2)"
  shows "<\<up>(map_option h ai = a) * (gtx X c1 c2 (Si, Gc, C1, C2) * bool_array_set_assn n V Vi)>
           weps_step Gc Vi Si C1 C2 mS mT u ai
         <\<lambda> r. \<up>(map_option h r =
                  eps_of (if (u \<notin> X \<and> u \<in> T0 X) \<and> u \<in> V then {wctx_mT (csr.wtight_ctx X c1
                    c2) - c2 u} else {})
                   (eps_of (if (u \<notin> X \<and> u \<in> S0 X) \<and> u \<notin> V then {wctx_mS (csr.wtight_ctx X
                     c1 c2) - c1 u}
                            else {})
                     (eps_of (if u \<in> V then (\<lambda> v. if u \<in> X then c1 u - c1 v else c2 v - c2 u) `
                                             {v \<in> set (nbrs (EE X) u). v \<notin> V} else {}) a))) *
               (gtx X c1 c2 (Si, Gc, C1, C2) * bool_array_set_assn n V Vi)>"
proof-
  let ?G = "gtx X c1 c2 (Si, Gc, C1, C2) * bool_array_set_assn n V Vi"
  note r1 = read_frame[OF bool_array_set_memb_rule[where i = u and n = n and Xi = Vi and X = V,
    simplified assms(1) pure_true mult_1_right],
    where F = "gtx X c1 c2 (Si, Gc, C1, C2)"]
  note r2 = read_frame[OF gtx_memb[OF assms(1)], where F = "bool_array_set_assn n V Vi"]
  have r3: "<\<up>(map_option h ai' = a') * ?G> xnbs (Si, Gc) u (gap_imp C1 C2 (u \<in> X) Vi u) ai'
            <\<lambda> r. ?G * \<up>(map_option h r = eps_of ((\<lambda> v. if u \<in> X then c1 u - c1 v else c2 v -
              c2 u) `
                                                {v \<in> set (nbrs (EE X) u). v \<notin> V}) a')>" for ai' a'
    by (rule ht_cons_pre[OF _ ht_cons_post[OF edge_part[OF assms(1), where Si = Si and Gc = Gc and V = V
          and Vi = Vi and ai = ai' and a = a' and ?C1.0 = C1 and ?C2.0 = C2]]])
       (sep_auto simp: gtx_def)+
  note r4 = read_frame[OF gtx_lift[OF s_imp_rule[OF X assms(1)]], where F = "bool_array_set_assn n V Vi"]
  note r5 = read_frame[OF gtx_lift[OF t_imp_rule[OF X assms(1)]], where F = "bool_array_set_assn n V Vi"]
  note r6 = read_frame[OF rd_c1[OF assms(1)], where F = "bool_array_set_assn n V Vi"]
  note r7 = read_frame[OF rd_c2[OF assms(1)], where F = "bool_array_set_assn n V Vi"]
  note hS = src_max[OF assms(1) _ assms(2)] and hT = tgt_max[OF assms(1) _ assms(3)]
  show ?thesis
    unfolding weps_step_def
    by (sep_auto heap: r1 r2 r3 r4 r5 r6 r7 simp: eps_of_h hS hT)
qed

lemma UN_edges:
  "(\<Union> u \<in> set [0..<n]. if u \<in> V then (\<lambda> v. g (u, v)) ` {v \<in> set (nbrs (EE X) u). v \<notin>
    V} else {}) =
     g ` {e \<in> set (EE X). fst e \<in> V \<and> snd e \<notin> V}"
proof(intro equalityI subsetI, goal_cases)
  case (1 z)
  then obtain u v where "u < n" "u \<in> V" "(u, v) \<in> set (EE X)" "v \<notin> V" "z = g (u, v)"
    by (auto simp: mem_nbrs split: if_splits)
  then show ?case
    by force
next
  case (2 z)
  then obtain u v where edge: "(u, v) \<in> set (EE X)" "u \<in> V" "v \<notin> V" "z = g (u, v)"
    by auto
  with edge_bounds[OF edge(1)] show ?case
    by (intro UN_I[where a = u]) (auto simp: mem_nbrs)
qed

text \<open>The pass over the elements computes @{const weighted_intersection_exchange_spec.weps}.\<close>

lemma weps_pass:
  fixes V K
  defines "K \<equiv> csr.wtight_ctx X c1 c2" and "V \<equiv> set (wctx_R (csr.wtight_ctx X c1 c2))"
  shows "foldr (\<lambda> u a. eps_of (if (u \<notin> X \<and> u \<in> T0 X) \<and> u \<in> V then {wctx_mT K - c2 u}
    else {})
                         (eps_of (if (u \<notin> X \<and> u \<in> S0 X) \<and> u \<notin> V then {wctx_mS K - c1 u}
                           else {})
                           (eps_of (if u \<in> V then (\<lambda> v. if u \<in> X then c1 u - c1 v else c2 v - c2 u) `
                                                   {v \<in> set (nbrs (EE X) u). v \<notin> V} else {}) a)))
           [0..<n] None = csr.weps K"
proof-
  define g where "g = (\<lambda> e. if fst e \<in> X then c1 (fst e) - c1 (snd e) else c2 (snd e) - c2 (fst e))"
  define GE where "GE = g ` {e \<in> set (EE X). fst e \<in> V \<and> snd e \<notin> V}"
  define GS where "GS = (\<lambda> y. wctx_mS K - c1 y) ` {y \<in> set (csr.srcs (csr.exch_ctx X)). y \<notin> V}"
  define GT where "GT = (\<lambda> y. wctx_mT K - c2 y) ` {y \<in> set (csr.tgts (csr.exch_ctx X)). y \<in> V}"
  define T where "T = (\<lambda> u. if (u \<notin> X \<and> u \<in> T0 X) \<and> u \<in> V then {wctx_mT K - c2 u}
    else {})"
  define S where "S = (\<lambda> u. if (u \<notin> X \<and> u \<in> S0 X) \<and> u \<notin> V then {wctx_mS K - c1 u}
    else {})"
  define E where "E = (\<lambda> u. if u \<in> V then (\<lambda> v. g (u, v)) ` {v \<in> set (nbrs (EE X) u). v
    \<notin> V} else {})"
  have "foldr (\<lambda> u a. eps_of (T u) (eps_of (S u) (eps_of (E u) a))) [0..<n] None =
      eps_of (\<Union> u \<in> set [0..<n]. T u \<union> (S u \<union> E u)) None"
    by (rule foldr_eps_of_gen) (simp_all add: eps_of_Un T_def S_def E_def)
  also have "eps_of (\<Union> u \<in> set [0..<n]. T u \<union> (S u \<union> E u)) None =
      eps_of (GT \<union> (GS \<union> GE)) None"
    unfolding UN_Un_distrib E_def UN_edges GE_def T_def S_def GT_def GS_def set_tgts set_srcs
    by (rule arg_cong[where f = "\<lambda> A. eps_of A None"]) auto
  also have "eps_of (GT \<union> (GS \<union> GE)) None = csr.weps K"
    unfolding csr.weps_def Let_def GE_def GS_def GT_def g_def V_def K_def
      ctx_fields csr.ctx_simps[OF X]
    by (simp only: foldr_eps_of) (simp add: eps_of_Un)
  finally show ?thesis
    unfolding T_def S_def E_def g_def fst_conv snd_conv .
qed

lemma weps_fold:
  assumes "csr.srcs (csr.exch_ctx X) \<noteq> [] \<longrightarrow> h mS = wctx_mS (csr.wtight_ctx X c1 c2)"
    and "csr.tgts (csr.exch_ctx X) \<noteq> [] \<longrightarrow> h mT = wctx_mT (csr.wtight_ctx X c1 c2)"
  shows "<\<up>(map_option h None = None) *
          (gtx X c1 c2 (Si, Gc, C1, C2) * bool_array_set_assn n (set (wctx_R (csr.wtight_ctx X c1 c2))) Vi)>
           foldr_range_imp (weps_step Gc Vi Si C1 C2 mS mT) n None
         <\<lambda> r. \<up>(map_option h r = csr.weps (csr.wtight_ctx X c1 c2)) *
               (gtx X c1 c2 (Si, Gc, C1, C2) * bool_array_set_assn n (set (wctx_R (csr.wtight_ctx X c1 c2))) Vi)>"
  unfolding weps_pass[symmetric]
  by (rule foldr_range_imp_rule[where A = "\<lambda> a ai. \<up>(map_option h ai = a)"], rule weps_step_rule[OF _
    assms])
     simp

text \<open>(E): without a path the visited array holds the reachable set.\<close>

lemma weps_imp_rule:
  assumes "wctx_path (csr.wtight_ctx X c1 c2) = None"
  shows "<gtx X c1 c2 (Si, Gc, C1, C2) * wctx_assn Vi Fr Bf Da Pa Mi Ti (csr.wtight_ctx X c1 c2)>
           weps_imp Gc Vi Mi Si C1 C2
         <\<lambda> r. gtx X c1 c2 (Si, Gc, C1, C2) * wctx_assn Vi Fr Bf Da Pa Mi Ti (csr.wtight_ctx X c1 c2) *
               \<up>(map_option h r = csr.weps (csr.wtight_ctx X c1 c2))>"
  unfolding wctx_assn_def wpath_assn_def assms option.case(1) ctx_fields(1) weps_imp_def
  by (sep_auto heap: weps_fold)

subsubsection \<open>The Shift and the Stale Context\<close>

text \<open>(S)\<close>

lemma wshift_imp_rule:
  assumes "wctx_path (csr.wtight_ctx X c1 c2) = None"
  shows "<wctx_assn Vi Fr Bf Da Pa Mi Ti (csr.wtight_ctx X c1 c2) * warr_assn n h c C> wshift_imp Vi e C
         <\<lambda> _. wctx_assn Vi Fr Bf Da Pa Mi Ti (csr.wtight_ctx X c1 c2) *
               warr_assn n h (\<lambda> x. if x \<in> set (wctx_R (csr.wtight_ctx X c1 c2)) then c x + h e else c x) C>"
  unfolding wctx_assn_def wpath_assn_def assms option.case(1)
  by (sep_auto heap: wshift_set_rule)

lemma wpath_stale:
  "wpath_assn Vi Da Pa t (csr.wtight_ctx X c1 c2) \<Longrightarrow>\<^sub>A len_assn n Vi * len_assn n Da * len_assn n
    Pa"
proof(cases "wctx_path (csr.wtight_ctx X c1 c2)")
  case None
  show ?thesis
    unfolding wpath_assn_def None option.case(1)
    by (rule ent_trans[OF _ ent_star_mono[OF ent_star_mono[OF bool_array_set_len ent_refl] ent_refl]]) sep_auto
next
  case (Some p)
  show ?thesis
  proof(cases "fst t = 1")
    case True
    show ?thesis
      unfolding wpath_assn_def Some option.case(2) if_P[OF True]
      by sep_auto
  next
    case False
    show ?thesis
      unfolding wpath_assn_def Some option.case(2) if_not_P[OF False] ex_assn_move_out(2)
      unfolding star_assoc[symmetric]
      by (rule ent_ex_preI, rule ent_pure_preI, elim conjE,
          rule ent_star_mono[OF ent_star_mono[OF ent_refl tb.dist_len] tb.par_len])
  qed
qed

text \<open>(W)\<close>

lemma wctx_stale: "wctx_assn Vi Fr Bf Da Pa Mi Ti (csr.wtight_ctx X c1 c2) \<Longrightarrow>\<^sub>A wws Vi Fr Bf Da
    Pa Mi Ti"
  unfolding wctx_assn_def
  by (rule ent_ex_preI, rule ent_ex_preI, rule ent_trans[OF ent_star_mono[OF ent_refl wpath_stale]])
     (sep_auto simp: wws_def work_assn_def len_assn_def)

end

subsubsection \<open>The Loop Instance\<close>

text \<open>The operations of the loop, with the BFS workspace, \<open>Mi\<close> and \<open>Ti\<close> as the context
    and the
  oracles and the CSR as the static data.\<close>

lemma imp_loop:
  "weighted_intersection_imp_loop wctx_path wctx_R csr.weps indep1 indep2 {0..<n} set (\<lambda> _. True)
     csr.wctx_invar (\<lambda> K. set (wctx_es K)) (\<lambda> K. set (wctx_sb K)) (\<lambda> K. set (wctx_tb K))
     n sol_assn smemb_imp sins_imp sdel_imp Array.nth ccopy_imp czero_imp
     (wtight_ctx_imp Gc Vi Fr Bf Da Pa Mi Ti) (wctx_path_imp Pa Ti) (weps_imp Gc Vi Mi) (wshift_imp Vi)
     h (\<lambda> R e c x. if x \<in> set R then c x + e else c x) csr.wtight_ctx
     (warr_assn n h) (wctx_assn Vi Fr Bf Da Pa Mi Ti)
     (wws Vi Fr Bf Da Pa Mi Ti) (ost1 * ost2 * (case Gc of (Ba, Ga) \<Rightarrow>
       Ba \<mapsto>\<^sub>a map (csr_start (nbrs es0)) [0..<Suc n] * Ga \<mapsto>\<^sub>a csr_entries (nbrs es0) n))"
proof(intro weighted_intersection_imp_loop.intro weighted_intersection_imp_loop_axioms.intro
      warr_copy_clear_imp, goal_cases)
  case 1
  show ?case
    by (rule intersection_augment_imp.intro[OF imp_nat_set_axioms])
next
  case 2
  show ?case
    by (rule real_embedding_axioms)
next
  case 3
  show ?case
    by (rule csr.exch_loop.weighted_intersection_path_loop_axioms)
next
  case 4
  show ?case
    by auto
next
  case (5 X c1 c2 Si C1 C2)
  show ?case
    by (rule ht_cons[OF _ _ wtight_ctx_imp_rule[OF 5(1-4)]])
       ((simp only: gtx_def gxs_def prod.case star_aci, rule ent_refl),
        (rule ent_true_drop(2), simp only: gtx_def gxs_def prod.case star_aci, rule ent_refl))
next
  case (6 X c1 c2 Ra)
  show ?case
    by (rule wctx_path_imp_rule[OF 6(1-4)])
next
  case (7 X c1 c2 Si C1 C2)
  show ?case
    by (rule ht_cons[OF _ _ weps_imp_rule[OF 7(1-4,7)]])
       ((simp only: gtx_def gxs_def prod.case star_aci, rule ent_refl),
        (rule ent_true_drop(2), simp only: gtx_def gxs_def prod.case star_aci, rule ent_refl))
next
  case (8 X c1 c2 c e C)
  show ?case
    by (rule wshift_imp_rule[OF 8(1-4,7)])
next
  case (9 X c1 c2)
  show ?case
    by (rule wctx_stale[OF 9])
qed

text \<open>The loop on preallocated arrays.\<close>

lemma loop_correct:
  "<(sol_assn {} Si) * warr_assn n h c Co * len_assn n C1 * len_assn n C2 *
    wws Vi Fr Bf Da Pa Mi Ti * (ost1 * ost2 * (case Gc of (Ba, Ga) \<Rightarrow>
      Ba \<mapsto>\<^sub>a map (csr_start (nbrs es0)) [0..<Suc n] * Ga \<mapsto>\<^sub>a csr_entries (nbrs es0) n)) *
        parr_assn n Ra>
     weighted_intersection_imp_loop_spec.wmi_run_imp sins_imp sdel_imp Array.nth
       ccopy_imp czero_imp (wtight_ctx_imp Gc Vi Fr Bf Da Pa Mi Ti) (wctx_path_imp Pa Ti)
       (weps_imp Gc Vi Mi) (wshift_imp Vi) Si Co C1 C2 Ra
   <\<lambda> _. \<exists>\<^sub>A X c1 c2. sol_assn X Si * warr_assn n h c1 C1 * warr_assn n h c2 C2 *
          warr_assn n h c Co * wws Vi Fr Bf Da Pa Mi Ti *
          (ost1 * ost2 * (case Gc of (Ba, Ga) \<Rightarrow>
             Ba \<mapsto>\<^sub>a map (csr_start (nbrs es0)) [0..<Suc n] * Ga \<mapsto>\<^sub>a csr_entries (nbrs es0)
               n)) * parr_assn n Ra *
          \<up>(weighted_double_matroid.is_opt indep1 indep2 c X)>"
proof-
  interpret l: weighted_intersection_imp_loop wctx_path wctx_R csr.weps indep1 indep2 "{0..<n}" set
    "\<lambda> _. True" csr.wctx_invar "\<lambda> K. set (wctx_es K)" "\<lambda> K. set (wctx_sb K)"
    "\<lambda> K. set (wctx_tb K)" n sol_assn smemb_imp sins_imp sdel_imp Array.nth
    ccopy_imp czero_imp "wtight_ctx_imp Gc Vi Fr Bf Da Pa Mi Ti" "wctx_path_imp Pa Ti"
    "weps_imp Gc Vi Mi" "wshift_imp Vi" h "\<lambda> R e c x. if x \<in> set R then c x + e else c x"
    csr.wtight_ctx "warr_assn n h"
    "wctx_assn Vi Fr Bf Da Pa Mi Ti" "wws Vi Fr Bf Da Pa Mi Ti"
    "ost1 * ost2 * (case Gc of (Ba, Ga) \<Rightarrow>
       Ba \<mapsto>\<^sub>a map (csr_start (nbrs es0)) [0..<Suc n] * Ga \<mapsto>\<^sub>a csr_entries (nbrs es0) n)"
    by (rule imp_loop)
  show ?thesis
    by (rule ht_cons_pre[OF _ l.wmi_run_imp_correct]) (intro ent_star_mono ent_refl len_warr)
qed
end

end
