theory Matroid_Weighted_Intersection_Exchange_Graph
  imports Matroid_Weighted_Intersection_Path_Loop Matroid_Intersection_Exchange_Graph
begin

section \<open>Weighted Matroid Intersection on the Exchange Graph\<close>

text \<open>The weighted counterpart of @{theory Matroid_Intersection.Matroid_Intersection_Exchange_Graph}:
  the loop of @{theory Matroid_Intersection.Matroid_Weighted_Intersection_Path_Loop} instantiated with
  the exchange edges of the unweighted exchange theory. The tight graph is the list of exchange edges
  filtered by equal weights, the path search is the BFS of the unweighted theory, and the reachable set
  is the visited set of the same BFS run, extended by the sources without tight out-edges.\<close>

record ('mset, 'o1, 'o2, 'a, 'cmap, 'vset) wexch_ctx =
  wctx_c :: "('mset, 'o1, 'o2, 'a) exch_ctx"
  wctx_c1 :: 'cmap
  wctx_c2 :: 'cmap
  wctx_ae :: "('a \<times> 'a) list"
  wctx_mS :: real
  wctx_mT :: real
  wctx_es :: "('a \<times> 'a) list"
  wctx_sb :: "'a list"
  wctx_tb :: "'a list"
  wctx_path :: "'a list option"
  wctx_R :: 'vset

subsection \<open>Code\<close>

locale weighted_intersection_exchange_spec =
  unweighted_intersection_exchange_spec where set_insert = "set_insert :: 'a \<Rightarrow> 'mset \<Rightarrow> 'mset"
    and vset_empty = "vset_empty :: 'vset"
  for set_insert vset_empty +
  fixes c_lookup :: "'cmap \<Rightarrow> 'a \<Rightarrow> real"
    and c_shift :: "'vset \<Rightarrow> real \<Rightarrow> 'cmap \<Rightarrow> 'cmap"
    and c_zero :: "'cmap"
    and vset_insert :: "'a \<Rightarrow> 'vset \<Rightarrow> 'vset"
begin

text \<open>An exchange edge is tight if its endpoints have equal weight: for the first matroid on edges
  leaving the solution, for the second matroid on edges entering it.\<close>

definition "tight c c1 c2 e =
  (if set_memb (fst e) (ctx_X c) then c_lookup c1 (fst e) = c_lookup c1 (snd e)
   else c_lookup c2 (fst e) = c_lookup c2 (snd e))"

text \<open>A source has a tight out-edge (only edges of the second matroid leave it).\<close>

definition "has_tight_nb c c2 y =
  (\<not> in_T c y \<and> list_ex (\<lambda> x. exch_orcl2 (ctx_o2 c) x y \<and> c_lookup c2 x = c_lookup c2 y)
    (ctx_inX c))"

text \<open>The context of one iteration. A maximum-weight source that is a maximum-weight target is a
  path on its own. Otherwise the maximum-weight sources with tight out-edges start the BFS; its final
  state yields both the path (as in @{term target_path}) and the reachable set.\<close>

definition "wtight_ctx X c1 c2 =
  (let c = exch_ctx X; ae = exch_edges c; es = filter (tight c c1 c2) ae;
       mS = list_max (c_lookup c1) (srcs c); mT = list_max (c_lookup c2) (tgts c);
       sb = filter (\<lambda> y. c_lookup c1 y = mS) (srcs c);
       tb = filter (\<lambda> y. c_lookup c2 y = mT) (tgts c);
       ss = filter (has_tight_nb c c2) sb;
       fin = bfs_final (build_graph es) ss;
       P = (case find (\<lambda> y. in_T c y \<and> c_lookup c2 y = mT) sb of
              Some s \<Rightarrow> Some [s]
            | None \<Rightarrow>
               (if ss = [] then None
                else (case find (isin (BFS_dist_state.visited fin)) tb of
                        None \<Rightarrow> None
                      | Some t \<Rightarrow> Some (rev (get_path (parent fin) t)))));
       vis = (if ss = [] then vset_empty else BFS_dist_state.visited fin)
   in \<lparr>wctx_c = c, wctx_c1 = c1, wctx_c2 = c2, wctx_ae = ae, wctx_mS = mS, wctx_mT = mT,
       wctx_es = es, wctx_sb = sb, wctx_tb = tb, wctx_path = P,
       wctx_R = foldr vset_insert (filter (\<lambda> y. \<not> has_tight_nb c c2 y) sb) vis\<rparr>)"

text \<open>The minimum gap: one pass over the exchange edges leaving the reachable set, the sources
  outside it and the targets inside it.\<close>

definition "weps K =
  (let c = wctx_c K; c1 = wctx_c1 K; c2 = wctx_c2 K; R = wctx_R K in
   foldr (\<lambda> y acc. if isin R y then eps_min acc (wctx_mT K - c_lookup c2 y) else acc) (tgts c)
     (foldr (\<lambda> y acc. if \<not> isin R y then eps_min acc (wctx_mS K - c_lookup c1 y) else acc) (srcs c)
       (foldr (\<lambda> e acc. if isin R (fst e) \<and> \<not> isin R (snd e)
                        then eps_min acc (if set_memb (fst e) (ctx_X c)
                                          then c_lookup c1 (fst e) - c_lookup c1 (snd e)
                                          else c_lookup c2 (snd e) - c_lookup c2 (fst e))
                        else acc) (wctx_ae K) None)))"

sublocale wexch_loop: weighted_intersection_path_loop_spec set_insert set_delete to_set set_invar
  set_empty c_shift c_zero c_lookup wtight_ctx wctx_path wctx_R weps .

lemmas [code] = tight_def has_tight_nb_def wtight_ctx_def weps_def

end

subsection \<open>Correctness\<close>

locale weighted_intersection_exchange =
  weighted_intersection_exchange_spec where set_insert = "set_insert :: 'a \<Rightarrow> 'mset \<Rightarrow> 'mset"
    and vset_empty = "vset_empty :: 'vset" and vset_insert = vset_insert
    and c_lookup = "c_lookup :: 'cmap \<Rightarrow> 'a \<Rightarrow> real"
  + unweighted_intersection_exchange where set_insert = set_insert and vset_empty = vset_empty
    and insert = vset_insert
  for set_insert vset_empty vset_insert c_lookup +
  fixes c_invar :: "'cmap \<Rightarrow> bool"
  assumes c_zero: "c_invar c_zero" "c_lookup c_zero = (\<lambda> _. 0)"
  assumes c_shift:
    "\<And> R e c. \<lbrakk>c_invar c; vset_inv R\<rbrakk> \<Longrightarrow> c_invar (c_shift R e c)"
    "\<And> R e c. \<lbrakk>c_invar c; vset_inv R\<rbrakk> \<Longrightarrow>
       c_lookup (c_shift R e c) = (\<lambda> x. if x \<in> t_set R then c_lookup c x + e else c_lookup c x)"
begin

lemma foldr_vset_insert:
  "vset_inv V \<Longrightarrow>
     vset_inv (foldr vset_insert xs V) \<and> t_set (foldr vset_insert xs V) = set xs \<union> t_set V"
  by (induction xs) (auto simp add: Graph.vset.set.set_insert Graph.vset.set.invar_insert)

text \<open>The path search and the reachable set of one iteration, for any tight edge list \<open>es\<close>, any
  source list \<open>sb\<close> and target list \<open>tb\<close>, the sources \<open>ss\<close> with out-edges and
    the remaining
  sources \<open>ds\<close>.\<close>

lemma path_search:
  fixes es :: "('a \<times> 'a) list" and ss sb tb :: "'a list"
  assumes "set es \<subseteq> carrier \<times> carrier" "distinct ss" "set ss = {u \<in> set sb. \<exists> v. (u, v)
    \<in> set es}"
  defines "P \<equiv> (case find (\<lambda> y. y \<in> set tb) sb of
                  Some s \<Rightarrow> Some [s]
                | None \<Rightarrow> (if ss = [] then None else target_path (build_graph es) ss tb))"
  shows "P = Some p \<Longrightarrow>
           \<exists> u v. (vwalk_bet (set es) u p v \<or> (p = [u] \<and> u = v)) \<and> u \<in> set sb \<and> v \<in>
             set tb \<and>
             (\<nexists> p'. (vwalk_bet (set es) u p' v \<or> (p' = [u] \<and> u = v)) \<and> length p' < length p)"
    and "P = None \<longleftrightarrow>
           (\<nexists> p u v. (vwalk_bet (set es) u p v \<or> (p = [u] \<and> u = v)) \<and> u \<in> set sb \<and> v
             \<in> set tb)"
proof-
  have "set ss \<subseteq> dVs (Graph.digraph_abs (build_graph es))"
    using assms(3) build_graph(4)
    by auto
  note tp = target_path[OF refl assms(2) _ this assms(1), unfolded build_graph(4)]
  show some: "P = Some p \<Longrightarrow>
           \<exists> u v. (vwalk_bet (set es) u p v \<or> (p = [u] \<and> u = v)) \<and> u \<in> set sb \<and> v \<in>
             set tb \<and>
             (\<nexists> p'. (vwalk_bet (set es) u p' v \<or> (p' = [u] \<and> u = v)) \<and> length p' < length p)"
               for p
  proof(cases "find (\<lambda> y. y \<in> set tb) sb")
    case None
    moreover assume "P = Some p"
    ultimately have "ss \<noteq> []" "target_path (build_graph es) ss tb = Some p"
      by (auto simp add: P_def split: if_splits)
    then obtain u v where "u \<in> set ss" "v \<in> set tb" "vwalk_bet (set es) u p v"
      "\<forall> u' p'. u' \<in> set ss \<and> vwalk_bet (set es) u' p' v \<longrightarrow> length p \<le> length p'"
      using tp(2)
      by blast
    moreover hence "u \<noteq> v" "u \<in> set sb"
      using None assms(3)
      by (auto simp add: find_None_iff)
    ultimately show ?thesis
      by fastforce
  next
    case (Some s)
    moreover assume "P = Some p"
    ultimately have "p = [s]"
      by (simp add: P_def)
    moreover have "s \<in> set sb" "s \<in> set tb"
      using Some
      by (auto simp add: find_Some_iff)
    ultimately show ?thesis
      by (auto simp add: vwalk_bet_def)
  qed
  show "P = None \<longleftrightarrow>
           (\<nexists> p u v. (vwalk_bet (set es) u p v \<or> (p = [u] \<and> u = v)) \<and> u \<in> set sb \<and> v
             \<in> set tb)"
  proof
    assume "P = None"
    hence nT: "u \<notin> set tb"
      and nw: "\<lbrakk>u \<in> set ss; v \<in> set tb\<rbrakk> \<Longrightarrow> \<not> vwalk_bet (set es) u p v"
      if "u \<in> set sb" for u p v
      using that tp(1)
      by (auto simp add: P_def find_None_iff split: option.splits if_splits)
    show "\<nexists> p u v. (vwalk_bet (set es) u p v \<or> (p = [u] \<and> u = v)) \<and> u \<in> set sb \<and> v
      \<in> set tb"
    proof(intro notI, elim exE conjE)
      fix p u v
      assume "vwalk_bet (set es) u p v \<or> (p = [u] \<and> u = v)" "u \<in> set sb" "v \<in> set tb"
      moreover hence "vwalk_bet (set es) u p v" "u \<noteq> v"
        using nT
        by auto
      moreover have "u \<in> set ss"
        using vwalk_then_edge[of "set es" u p v] calculation(2,4,5) assms(3)
        by auto
      ultimately show False
        using nw[of u v p]
        by blast
    qed
  next
    assume "\<nexists> p u v. (vwalk_bet (set es) u p v \<or> (p = [u] \<and> u = v)) \<and> u \<in> set sb \<and> v
      \<in> set tb"
    thus "P = None"
      using some
      by (cases P) blast+
  qed
qed

lemma reach_set:
  assumes "set es \<subseteq> carrier \<times> carrier" "distinct ss" "set ss = {u \<in> set sb. \<exists> v. (u, v)
    \<in> set es}"
    "set ds = {u \<in> set sb. u \<notin> set ss}"
  defines "R \<equiv> foldr vset_insert ds
                 (if ss = [] then vset_empty else BFS_dist_state.visited (bfs_final (build_graph es) ss))"
  shows "vset_inv R" and "t_set R = {v. \<exists> u \<in> set sb. u = v \<or> (\<exists> p. vwalk_bet (set es) u p v)}"
proof-
  have "vset_inv (BFS_dist_state.visited (bfs_final (build_graph es) ss)) \<and>
        t_set (BFS_dist_state.visited (bfs_final (build_graph es) ss))
          = {v. \<exists> u \<in> set ss. \<exists> q. vwalk_bet (set es) u q v}" if "ss \<noteq> []"
  proof-
    obtain exp_tree nfc dist_invar parent_abstract parent_invar par_U par_roots where B:
      "BFS_distance_parents (\<lambda> x. None) (\<lambda> x G. G(x := None)) vset_insert isin t_set sel
         (\<lambda> x N G. G(x := Some N)) (\<lambda> G. True) vset_empty vset_delete vset_inv union inter diff
         (build_graph es) exp_tree nfc vset_inv2 some_dist dist_lookup dist_invar (\<lambda> G x. G x)
         set_all_dists_in_set parent_abstract parent_invar par_U get_path par_roots parent_init
         (next_frontier_current_parents (build_graph es))"
      by (rule bfs_inst[OF refl assms(1)])
    have "set ss \<subseteq> dVs (Graph.digraph_abs (build_graph es))"
      using assms(3) build_graph(4)
      by auto
    note ax = bfs_axiomI[OF refl assms(2) that this assms(1)]
    show ?thesis
      using BFS_distance_parents.BFS_par_visited_inv[OF B ax]
        BFS_distance_parents.BFS_par_correct(1)[OF B ax refl] vset_of_list(2)[of ss] assms(2) build_graph(4)
      by (auto simp add: bfs_final_def)
  qed
  hence R: "vset_inv R" "t_set R = set ds \<union> {v. \<exists> u \<in> set ss. \<exists> q. vwalk_bet (set es) u q v}"
    using foldr_vset_insert Graph.vset.set.invar_empty Graph.vset.set.set_empty
    by (auto simp add: R_def)
  show "vset_inv R"
    by (rule R(1))
  show "t_set R = {v. \<exists> u \<in> set sb. u = v \<or> (\<exists> p. vwalk_bet (set es) u p v)}"
  proof(intro set_eqI iffI)
    fix v
    assume "v \<in> t_set R"
    thus "v \<in> {v. \<exists> u \<in> set sb. u = v \<or> (\<exists> p. vwalk_bet (set es) u p v)}"
      using R(2) assms(3,4)
      by auto
  next
    fix v
    assume "v \<in> {v. \<exists> u \<in> set sb. u = v \<or> (\<exists> p. vwalk_bet (set es) u p v)}"
    then obtain u where u: "u \<in> set sb" "u = v \<or> (\<exists> p. vwalk_bet (set es) u p v)"
      by blast
    show "v \<in> t_set R"
    proof(cases "u \<in> set ss")
      case True
      moreover hence "vwalk_bet (set es) u [u] u"
        using assms(3)
        by auto
      ultimately show ?thesis
        using R(2) u(2)
        by auto
    next
      case False
      hence "u = v" if "vwalk_bet (set es) u p v" for p
        using that vwalk_then_edge[of "set es" u p v] assms(3) u(1)
        by auto
      hence "u = v"
        using u(2)
        by blast
      thus ?thesis
        using R(2) assms(4) u(1) False
        by auto
    qed
  qed
qed

context
  fixes X and c1 c2 :: 'cmap
  assumes X: "set_invar X" "to_set X \<subseteq> carrier" "indep1 (to_set X)" "indep2 (to_set X)"
begin

interpretation W: weighted_intersection_graph carrier indep1 indep2 "c_lookup c1" "c_lookup c2"
  by unfold_locales

lemmas srcs_X = srcs[OF X] and tgts_X = tgts[OF X] and in_T_X = in_T[OF X]
  and ctx_simps_X = ctx_simps[OF X] and exchange_edges_X = exchange_edges[OF X]
  and exch_edge_X = exch_edge[OF X] and exch_edges_carrier_X = exch_edges_carrier[OF X]
  and set_memb_X = set_memb[OF X(1)] and A1_edges_X = A1_edges[OF X(3,4)] and A2_edges_X = A2_edges[OF X(3,4)]

subsubsection \<open>The Tight Graph and its Endpoints\<close>

lemma list_max_srcs:
  "S (to_set X) \<noteq> {} \<Longrightarrow> list_max f (srcs (exch_ctx X)) = Max (f ` S (to_set X))"
  using list_max[of "srcs (exch_ctx X)" f] srcs_X(1)[symmetric]
  by auto

lemma list_max_tgts:
  "T (to_set X) \<noteq> {} \<Longrightarrow> list_max f (tgts (exch_ctx X)) = Max (f ` T (to_set X))"
  using list_max[of "tgts (exch_ctx X)" f] tgts_X[symmetric]
  by auto

lemma sbar:
  "set (filter (\<lambda> y. c_lookup c1 y = list_max (c_lookup c1) (srcs (exch_ctx X))) (srcs (exch_ctx X)))
     = W.Sbar (to_set X)"
  using srcs_X(1) list_max_srcs[of "c_lookup c1"]
  by (cases "S (to_set X) = {}") (auto simp add: W.Sbar_def)

lemma tbar:
  "set (filter (\<lambda> y. c_lookup c2 y = list_max (c_lookup c2) (tgts (exch_ctx X))) (tgts (exch_ctx X)))
     = W.Tbar (to_set X)"
  using tgts_X list_max_tgts[of "c_lookup c2"]
  by (cases "T (to_set X) = {}") (auto simp add: W.Tbar_def)

lemma tight_iff:
  "tight (exch_ctx X) c1 c2 e \<longleftrightarrow>
     (if fst e \<in> to_set X then c_lookup c1 (fst e) = c_lookup c1 (snd e)
      else c_lookup c2 (fst e) = c_lookup c2 (snd e))"
  using set_memb_X
  by (simp add: tight_def ctx_simps_X)

lemma tight_edges:
  "set (filter (tight (exch_ctx X) c1 c2) (exch_edges (exch_ctx X))) = W.Gbar (to_set X)"
  using A1_edges_X(1) A2_edges_X(2)
  by (auto simp add: exchange_edges_X tight_iff W.Gbar_def W.Abar1_def W.Abar2_def)

lemma has_tight_nb:
  "u \<in> set (srcs (exch_ctx X)) \<Longrightarrow> has_tight_nb (exch_ctx X) c2 u \<longleftrightarrow>
     (\<exists> v. (u, v) \<in> set (filter (tight (exch_ctx X) c1 c2) (exch_edges (exch_ctx X))))"
  using srcs_X(1) in_T_X
  by (auto simp add: has_tight_nb_def exch_edge_X out2_def list_ex_iff tight_iff ctx_simps_X
        S_def)

subsubsection \<open>The Context\<close>

lemma wtight_ctx_fields:
  "wctx_c (wtight_ctx X c1 c2) = exch_ctx X" "wctx_c1 (wtight_ctx X c1 c2) = c1"
  "wctx_c2 (wtight_ctx X c1 c2) = c2" "wctx_ae (wtight_ctx X c1 c2) = exch_edges (exch_ctx X)"
  "wctx_mS (wtight_ctx X c1 c2) = list_max (c_lookup c1) (srcs (exch_ctx X))"
  "wctx_mT (wtight_ctx X c1 c2) = list_max (c_lookup c2) (tgts (exch_ctx X))"
  "wctx_es (wtight_ctx X c1 c2) = filter (tight (exch_ctx X) c1 c2) (exch_edges (exch_ctx X))"
  "wctx_sb (wtight_ctx X c1 c2) =
     filter (\<lambda> y. c_lookup c1 y = list_max (c_lookup c1) (srcs (exch_ctx X))) (srcs (exch_ctx X))"
  "wctx_tb (wtight_ctx X c1 c2) =
     filter (\<lambda> y. c_lookup c2 y = list_max (c_lookup c2) (tgts (exch_ctx X))) (tgts (exch_ctx X))"
  by (simp_all add: wtight_ctx_def Let_def)

lemma wctx_sets:
  "set (wctx_es (wtight_ctx X c1 c2)) = W.Gbar (to_set X)"
  "set (wctx_sb (wtight_ctx X c1 c2)) = W.Sbar (to_set X)"
  "set (wctx_tb (wtight_ctx X c1 c2)) = W.Tbar (to_set X)"
  by (simp_all only: wtight_ctx_fields tight_edges sbar tbar)

lemma wctx_es_carrier: "set (wctx_es (wtight_ctx X c1 c2)) \<subseteq> carrier \<times> carrier"
  using exch_edges_carrier_X
  by (auto simp add: wtight_ctx_fields)

lemma wctx_ss:
  "distinct (filter (has_tight_nb (exch_ctx X) c2) (wctx_sb (wtight_ctx X c1 c2)))"
  "set (filter (has_tight_nb (exch_ctx X) c2) (wctx_sb (wtight_ctx X c1 c2)))
     = {u \<in> set (wctx_sb (wtight_ctx X c1 c2)). \<exists> v. (u, v) \<in> set (wctx_es (wtight_ctx X c1 c2))}"
  using srcs_X(2) has_tight_nb
  by (auto simp add: wtight_ctx_fields)

lemma wtight_ctx_path:
  "wctx_path (wtight_ctx X c1 c2) =
     (let c = exch_ctx X; es = filter (tight c c1 c2) (exch_edges c);
          sb = filter (\<lambda> y. c_lookup c1 y = list_max (c_lookup c1) (srcs c)) (srcs c);
          tb = filter (\<lambda> y. c_lookup c2 y = list_max (c_lookup c2) (tgts c)) (tgts c);
          ss = filter (has_tight_nb c c2) sb
      in case find (\<lambda> y. in_T c y \<and> c_lookup c2 y = list_max (c_lookup c2) (tgts c)) sb of
           Some s \<Rightarrow> Some [s]
         | None \<Rightarrow> (if ss = [] then None else target_path (build_graph es) ss tb))"
  unfolding wtight_ctx_def target_path_def Let_def
  by simp

lemma tb_find_pred:
  "(\<lambda> y. in_T (exch_ctx X) y \<and> c_lookup c2 y = list_max (c_lookup c2) (tgts (exch_ctx X))) =
     (\<lambda> y. y \<in> set (filter (\<lambda> y. c_lookup c2 y = list_max (c_lookup c2) (tgts (exch_ctx X)))
                         (tgts (exch_ctx X))))"
  using in_T_X tgts_X
  by auto

lemma wtight_ctx_R:
  "wctx_R (wtight_ctx X c1 c2) =
     (let c = exch_ctx X; es = filter (tight c c1 c2) (exch_edges c);
          sb = filter (\<lambda> y. c_lookup c1 y = list_max (c_lookup c1) (srcs c)) (srcs c);
          ss = filter (has_tight_nb c c2) sb
      in foldr vset_insert (filter (\<lambda> y. \<not> has_tight_nb c c2 y) sb)
           (if ss = [] then vset_empty else BFS_dist_state.visited (bfs_final (build_graph es) ss)))"
  unfolding wtight_ctx_def Let_def
  by simp

lemma wctx_path:
  "wctx_path (wtight_ctx X c1 c2) = Some p \<Longrightarrow>
     \<exists> u v. (vwalk_bet (set (wctx_es (wtight_ctx X c1 c2))) u p v \<or> (p = [u] \<and> u = v))
       \<and> u \<in> set (wctx_sb (wtight_ctx X c1 c2)) \<and> v \<in> set (wctx_tb (wtight_ctx X c1 c2)) \<and>
       (\<nexists> p'. (vwalk_bet (set (wctx_es (wtight_ctx X c1 c2))) u p' v \<or> (p' = [u] \<and> u = v))
               \<and> length p' < length p)"
  "wctx_path (wtight_ctx X c1 c2) = None \<longleftrightarrow>
     (\<nexists> p u v. (vwalk_bet (set (wctx_es (wtight_ctx X c1 c2))) u p v \<or> (p = [u] \<and> u = v))
               \<and> u \<in> set (wctx_sb (wtight_ctx X c1 c2)) \<and> v \<in> set (wctx_tb (wtight_ctx X c1 c2)))"
  using path_search[OF wctx_es_carrier wctx_ss, where tb = "wctx_tb (wtight_ctx X c1 c2)"]
  unfolding wtight_ctx_path Let_def wtight_ctx_fields tb_find_pred
  by simp_all

text \<open>The reachable set: the BFS visits exactly the vertices reachable from the sources with
  tight out-edges, and the other sources reach only themselves.\<close>

lemma wctx_ds:
  "set (filter (\<lambda> y. \<not> has_tight_nb (exch_ctx X) c2 y) (wctx_sb (wtight_ctx X c1 c2))) =
     {u \<in> set (wctx_sb (wtight_ctx X c1 c2)). u \<notin> set (filter (has_tight_nb (exch_ctx X) c2) (wctx_sb
       (wtight_ctx X c1 c2)))}"
  by auto

lemma wctx_R:
  "vset_inv (wctx_R (wtight_ctx X c1 c2))"
  "t_set (wctx_R (wtight_ctx X c1 c2)) = {v. \<exists> u \<in> set (wctx_sb (wtight_ctx X c1 c2)).
     u = v \<or> (\<exists> p. vwalk_bet (set (wctx_es (wtight_ctx X c1 c2))) u p v)}"
  using reach_set[OF wctx_es_carrier wctx_ss wctx_ds]
  unfolding wtight_ctx_R Let_def wtight_ctx_fields
  by (simp_all only:)

subsubsection \<open>The Minimum Gap\<close>

lemma isin_wctx_R:
  "isin (wctx_R (wtight_ctx X c1 c2)) z \<longleftrightarrow> z \<in> W.Rbar (to_set X)"
  using Graph.vset.set.set_isin[OF wctx_R(1)] wctx_R(2) wctx_sets
  by (simp add: W.Rbar_def)

lemma edge_gaps:
  "(\<lambda> e. if set_memb (fst e) X then c_lookup c1 (fst e) - c_lookup c1 (snd e)
         else c_lookup c2 (snd e) - c_lookup c2 (fst e))
     ` {e \<in> set (exch_edges (exch_ctx X)). fst e \<in> R \<and> snd e \<notin> R}
   = {c_lookup c1 x - c_lookup c1 y | x y. (x, y) \<in> A1 (to_set X) \<and> x \<in> R \<and> y \<notin> R}
     \<union> {c_lookup c2 x - c_lookup c2 y | x y. (y, x) \<in> A2 (to_set X) \<and> y \<in> R \<and> x \<notin> R}"
  (is "?g ` ?E = ?A \<union> ?B")
proof(intro equalityI subsetI)
  fix v
  assume "v \<in> ?g ` ?E"
  thus "v \<in> ?A \<union> ?B"
    using A1_edges_X(1) A2_edges_X(2)
    by (auto simp add: exchange_edges_X set_memb_X)
next
  fix v
  assume "v \<in> ?A \<union> ?B"
  thus "v \<in> ?g ` ?E"
  proof(elim UnE CollectE exE conjE)
    fix x y
    assume "v = c_lookup c1 x - c_lookup c1 y" "(x, y) \<in> A1 (to_set X)" "x \<in> R" "y \<notin> R"
    thus ?thesis
      using A1_edges_X(1)
      by (auto simp add: exchange_edges_X set_memb_X intro!: image_eqI[where x = "(x, y)"])
  next
    fix x y
    assume "v = c_lookup c2 x - c_lookup c2 y" "(y, x) \<in> A2 (to_set X)" "y \<in> R" "x \<notin> R"
    thus ?thesis
      using A2_edges_X(2)
      by (auto simp add: exchange_edges_X set_memb_X intro!: image_eqI[where x = "(y, x)"])
  qed
qed

lemma src_gaps:
  "(\<lambda> y. list_max (c_lookup c1) (srcs (exch_ctx X)) - c_lookup c1 y)
     ` {y \<in> set (srcs (exch_ctx X)). y \<notin> R}
   = {Max (c_lookup c1 ` S (to_set X)) - c_lookup c1 y | y. y \<in> S (to_set X) \<and> y \<notin> R}"
  using srcs_X(1) list_max_srcs[of "c_lookup c1"]
  by (cases "S (to_set X) = {}") auto

lemma tgt_gaps:
  "(\<lambda> y. list_max (c_lookup c2) (tgts (exch_ctx X)) - c_lookup c2 y)
     ` {y \<in> set (tgts (exch_ctx X)). y \<in> R}
   = {Max (c_lookup c2 ` T (to_set X)) - c_lookup c2 y | y. y \<in> T (to_set X) \<and> y \<in> R}"
  using tgts_X list_max_tgts[of "c_lookup c2"]
  by (cases "T (to_set X) = {}") auto

text \<open>The pass of @{term weps} computes the minimum boundary gap of the reachable set.\<close>

lemma weps_eq:
  "weps (wtight_ctx X c1 c2) = eps_of (W.gaps (to_set X) (W.Rbar (to_set X))) None"
proof-
  define K where "K = wtight_ctx X c1 c2"
  define g where "g = (\<lambda> e. if set_memb (fst e) X then c_lookup c1 (fst e) - c_lookup c1 (snd e)
                           else c_lookup c2 (snd e) - c_lookup c2 (fst e))"
  define GE where "GE = g ` {e \<in> set (exch_edges (exch_ctx X)). isin (wctx_R K) (fst e)
                                  \<and> \<not> isin (wctx_R K) (snd e)}"
  define GS where "GS = (\<lambda> y. list_max (c_lookup c1) (srcs (exch_ctx X)) - c_lookup c1 y)
                          ` {y \<in> set (srcs (exch_ctx X)). \<not> isin (wctx_R K) y}"
  define GT where "GT = (\<lambda> y. list_max (c_lookup c2) (tgts (exch_ctx X)) - c_lookup c2 y)
                          ` {y \<in> set (tgts (exch_ctx X)). isin (wctx_R K) y}"
  have "weps K = eps_of GT (eps_of GS (eps_of GE None))"
    unfolding weps_def Let_def K_def wtight_ctx_fields ctx_simps_X GE_def GS_def GT_def g_def
    by (simp only: foldr_eps_of)
  also have "\<dots> = eps_of (GT \<union> (GS \<union> GE)) None"
    by (simp add: eps_of_Un GE_def GS_def GT_def)
  also have "GT \<union> (GS \<union> GE) = W.gaps (to_set X) (W.Rbar (to_set X))"
    using edge_gaps src_gaps tgt_gaps
    by (simp add: GE_def GS_def GT_def g_def K_def isin_wctx_R W.gaps_def Un_ac)
  finally show ?thesis
    unfolding K_def .
qed

end

subsubsection \<open>Total Correctness\<close>

text \<open>The invariant of a context: it was built for a common independent set.\<close>

definition "wctx_invar X c1 c2 K \<longleftrightarrow>
  K = wtight_ctx X c1 c2 \<and> set_invar X \<and> to_set X \<subseteq> carrier \<and> indep1 (to_set X) \<and> indep2
    (to_set X)"

lemma wtight_ctx_invar:
  "\<lbrakk>set_invar X; to_set X \<subseteq> carrier; indep1 (to_set X); indep2 (to_set X);
    c_invar c1; c_invar c2; matroid1.local_opt (c_lookup c1) (to_set X);
    matroid2.local_opt (c_lookup c2) (to_set X)\<rbrakk>
   \<Longrightarrow> wctx_invar X c1 c2 (wtight_ctx X c1 c2)"
  by (simp add: wctx_invar_def)

lemma wctx_abs:
  "wctx_invar X c1 c2 K \<Longrightarrow> set (wctx_es K) =
     weighted_intersection_graph.Gbar carrier indep1 indep2 (c_lookup c1) (c_lookup c2) (to_set X)"
  "wctx_invar X c1 c2 K \<Longrightarrow> set (wctx_sb K) =
     weighted_intersection_graph.Sbar carrier indep1 (c_lookup c1) (to_set X)"
  "wctx_invar X c1 c2 K \<Longrightarrow> set (wctx_tb K) =
     weighted_intersection_graph.Tbar carrier indep2 (c_lookup c2) (to_set X)"
  using wctx_sets
  by (auto simp add: wctx_invar_def)

lemma wctx_path_spec:
  "wctx_invar X c1 c2 K \<Longrightarrow> wctx_path K = None \<longleftrightarrow>
     (\<nexists> p u v. (vwalk_bet (set (wctx_es K)) u p v \<or> (p = [u] \<and> u = v))
               \<and> u \<in> set (wctx_sb K) \<and> v \<in> set (wctx_tb K))"
  "\<lbrakk>wctx_invar X c1 c2 K; wctx_path K = Some p\<rbrakk> \<Longrightarrow>
     \<exists> u v. (vwalk_bet (set (wctx_es K)) u p v \<or> (p = [u] \<and> u = v))
            \<and> u \<in> set (wctx_sb K) \<and> v \<in> set (wctx_tb K) \<and>
       (\<nexists> p'. (vwalk_bet (set (wctx_es K)) u p' v \<or> (p' = [u] \<and> u = v)) \<and> length p' < length p)"
  using wctx_path
  by (auto simp add: wctx_invar_def)

lemma wctx_reach_spec:
  "\<lbrakk>wctx_invar X c1 c2 K; wctx_path K = None\<rbrakk> \<Longrightarrow> vset_inv (wctx_R K)"
  "\<lbrakk>wctx_invar X c1 c2 K; wctx_path K = None\<rbrakk> \<Longrightarrow>
     t_set (wctx_R K) = {v. \<exists> u \<in> set (wctx_sb K). u = v \<or> (\<exists> p. vwalk_bet (set (wctx_es K)) u
       p v)}"
  using wctx_R
  by (auto simp add: wctx_invar_def)

lemma weps_spec:
  "\<lbrakk>wctx_invar X c1 c2 K; wctx_path K = None\<rbrakk> \<Longrightarrow>
     weps K = eps_of (weighted_intersection_graph.gaps carrier indep1 indep2 (c_lookup c1)
                 (c_lookup c2) (to_set X) (weighted_intersection_graph.Rbar carrier indep1 indep2
                 (c_lookup c1) (c_lookup c2) (to_set X))) None"
  using weps_eq
  by (auto simp add: wctx_invar_def)

sublocale exch_loop: weighted_intersection_path_loop
  where set_insert = set_insert and set_delete = set_delete and to_set = to_set
    and set_invar = set_invar and set_empty = set_empty and c_shift = c_shift and c_zero = c_zero
    and tight_ctx = wtight_ctx and tight_path = wctx_path and reach = wctx_R
    and eps = weps and carrier = carrier and indep1 = indep1 and indep2 = indep2
    and c_lookup = c_lookup and c_invar = c_invar and r_set = t_set and r_invar = vset_inv
    and ctx_invar = wctx_invar and ctx_edges = "\<lambda> K. set (wctx_es K)"
    and ctx_S = "\<lambda> K. set (wctx_sb K)" and ctx_T = "\<lambda> K. set (wctx_tb K)"
  by unfold_locales
     (fact set_insert set_delete set_empty c_zero c_shift wtight_ctx_invar wctx_abs
        wctx_path_spec wctx_reach_spec weps_spec)+

lemmas total_correctness = exch_loop.impl_total_correctness

end

end
