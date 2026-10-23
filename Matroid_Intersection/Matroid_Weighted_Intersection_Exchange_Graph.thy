theory Matroid_Weighted_Intersection_Exchange_Graph
  imports Matroid_Weighted_Intersection_Path_Loop Matroid_Intersection_Exchange_Graph
begin

section \<open>Weighted Matroid Intersection on the Exchange Graph\<close>

text \<open>The weighted counterpart of @{theory Matroid_Intersection.Matroid_Intersection_Exchange_Graph}:
  the loop of @{theory Matroid_Intersection.Matroid_Weighted_Intersection_Path_Loop} instantiated with
  the exchange edges of the unweighted exchange theory. The tight graph is the list of exchange edges
  filtered by equal weights, the path search is the BFS of the unweighted theory, and the reachable set
  is the visited set of the same BFS run, extended by the sources without tight out-edges.\<close>

text \<open>The maximum weight of a non-empty list.\<close>

definition "list_max f xs = fold max (map f (tl xs)) (f (hd xs))"

lemma list_max:
  fixes f :: "'a \<Rightarrow> 'b :: linorder"
  shows "xs \<noteq> [] \<Longrightarrow> list_max f xs = Max (f ` set xs)"
  by (cases xs) (simp_all add: list_max_def Max.set_eq_fold[symmetric])

lemmas [code] = list_max_def

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
  (\<not> in_T c y \<and> list_ex (\<lambda> x. exch_orcl2 (ctx_o2 c) x y \<and> c_lookup c2 x = c_lookup c2 y) (ctx_inX c))"

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
  "vset_inv V \<Longrightarrow> vset_inv (foldr vset_insert xs V) \<and> t_set (foldr vset_insert xs V) = set xs \<union> t_set V"
  by (induction xs) (auto simp add: Graph.vset.set.set_insert Graph.vset.set.invar_insert)

context
  fixes X and c1 c2 :: 'cmap
  assumes X: "set_invar X" "to_set X \<subseteq> carrier" "indep1 (to_set X)" "indep2 (to_set X)"
begin

subsubsection \<open>The Tight Graph and its Endpoints\<close>

lemma sbar:
  "set (filter (\<lambda> y. c_lookup c1 y = list_max (c_lookup c1) (srcs (exch_ctx X))) (srcs (exch_ctx X)))
     = weighted_intersection_graph.Sbar carrier indep1 (c_lookup c1) (to_set X)"
proof-
  interpret W: weighted_intersection_graph carrier indep1 indep2 "c_lookup c1" "c_lookup c2"
    by unfold_locales
  show ?thesis
  proof (cases "srcs (exch_ctx X) = []")
    case True thus ?thesis using srcs(1)[OF X] by (simp add: W.Sbar_def)
  next
    case False
    have "list_max (c_lookup c1) (srcs (exch_ctx X)) = Max (c_lookup c1 ` S (to_set X))"
      using list_max[OF False] srcs(1)[OF X] by simp
    thus ?thesis using srcs(1)[OF X] by (simp add: W.Sbar_def)
  qed
qed

lemma tbar:
  "set (filter (\<lambda> y. c_lookup c2 y = list_max (c_lookup c2) (tgts (exch_ctx X))) (tgts (exch_ctx X)))
     = weighted_intersection_graph.Tbar carrier indep2 (c_lookup c2) (to_set X)"
proof-
  interpret W: weighted_intersection_graph carrier indep1 indep2 "c_lookup c1" "c_lookup c2"
    by unfold_locales
  show ?thesis
  proof (cases "tgts (exch_ctx X) = []")
    case True thus ?thesis using tgts[OF X] by (simp add: W.Tbar_def)
  next
    case False
    have "list_max (c_lookup c2) (tgts (exch_ctx X)) = Max (c_lookup c2 ` T (to_set X))"
      using list_max[OF False] tgts[OF X] by simp
    thus ?thesis using tgts[OF X] by (simp add: W.Tbar_def)
  qed
qed

lemma tight_iff:
  "tight (exch_ctx X) c1 c2 e \<longleftrightarrow>
     (if fst e \<in> to_set X then c_lookup c1 (fst e) = c_lookup c1 (snd e)
      else c_lookup c2 (fst e) = c_lookup c2 (snd e))"
  using set_memb[OF X(1)] by (simp add: tight_def ctx_simps[OF X])

lemma tight_edges:
  "set (filter (tight (exch_ctx X) c1 c2) (exch_edges (exch_ctx X)))
     = weighted_intersection_graph.Gbar carrier indep1 indep2 (c_lookup c1) (c_lookup c2) (to_set X)"
proof-
  interpret W: weighted_intersection_graph carrier indep1 indep2 "c_lookup c1" "c_lookup c2"
    by unfold_locales
  have "e \<in> A1 (to_set X) \<Longrightarrow> fst e \<in> to_set X" "e \<in> A2 (to_set X) \<Longrightarrow> fst e \<notin> to_set X" for e
    using A1_edges(1)[OF X(3,4)] A2_edges(2)[OF X(3,4)] by auto
  thus ?thesis
    by (auto simp add: exchange_edges[OF X] tight_iff W.Gbar_def W.Abar1_def W.Abar2_def)
qed

lemma has_tight_nb:
  assumes "u \<in> set (srcs (exch_ctx X))"
  shows "has_tight_nb (exch_ctx X) c2 u \<longleftrightarrow>
           (\<exists> v. (u, v) \<in> set (filter (tight (exch_ctx X) c1 c2) (exch_edges (exch_ctx X))))"
proof-
  have u: "u \<in> carrier" "u \<notin> to_set X"
    using assms srcs(1)[OF X] by (auto simp add: S_def)
  show ?thesis
    using u in_T[OF X]
    by (auto simp add: has_tight_nb_def exch_edge[OF X] out2_def list_ex_iff tight_iff ctx_simps[OF X])
qed

subsubsection \<open>The Context\<close>

lemma wtight_ctx_path:
  "wctx_path (wtight_ctx X c1 c2) =
     (let c = exch_ctx X; es = filter (tight c c1 c2) (exch_edges c);
          sb = filter (\<lambda> y. c_lookup c1 y = list_max (c_lookup c1) (srcs c)) (srcs c);
          tb = filter (\<lambda> y. c_lookup c2 y = list_max (c_lookup c2) (tgts c)) (tgts c);
          ss = filter (has_tight_nb c c2) sb
      in case find (\<lambda> y. in_T c y \<and> c_lookup c2 y = list_max (c_lookup c2) (tgts c)) sb of
           Some s \<Rightarrow> Some [s]
         | None \<Rightarrow> (if ss = [] then None else target_path (build_graph es) ss tb))"
  unfolding wtight_ctx_def target_path_def Let_def by simp

text \<open>The context specification, stated for the components of the context.\<close>
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

lemma wtight_ctx_R:
  "wctx_R (wtight_ctx X c1 c2) =
     (let c = exch_ctx X; es = filter (tight c c1 c2) (exch_edges c);
          sb = filter (\<lambda> y. c_lookup c1 y = list_max (c_lookup c1) (srcs c)) (srcs c);
          ss = filter (has_tight_nb c c2) sb
      in foldr vset_insert (filter (\<lambda> y. \<not> has_tight_nb c c2 y) sb)
           (if ss = [] then vset_empty else BFS_dist_state.visited (bfs_final (build_graph es) ss)))"
  unfolding wtight_ctx_def Let_def by simp

text \<open>The context specification, stated for the components of the context.\<close>

lemma wtight_ctx_props:
  defines "K \<equiv> wtight_ctx X c1 c2"
  shows "set (wctx_es K) =
           weighted_intersection_graph.Gbar carrier indep1 indep2 (c_lookup c1) (c_lookup c2) (to_set X)"
    and "set (wctx_sb K) = weighted_intersection_graph.Sbar carrier indep1 (c_lookup c1) (to_set X)"
    and "set (wctx_tb K) = weighted_intersection_graph.Tbar carrier indep2 (c_lookup c2) (to_set X)"
    and "wctx_path K = None \<longleftrightarrow>
           (\<nexists> p u v. (vwalk_bet (set (wctx_es K)) u p v \<or> (p = [u] \<and> u = v))
                     \<and> u \<in> set (wctx_sb K) \<and> v \<in> set (wctx_tb K))"
    and "wctx_path K = Some p \<Longrightarrow>
           \<exists> u v. (vwalk_bet (set (wctx_es K)) u p v \<or> (p = [u] \<and> u = v))
                  \<and> u \<in> set (wctx_sb K) \<and> v \<in> set (wctx_tb K) \<and>
             (\<nexists> p'. (vwalk_bet (set (wctx_es K)) u p' v \<or> (p' = [u] \<and> u = v)) \<and> length p' < length p)"
    and "vset_inv (wctx_R K)"
    and "t_set (wctx_R K) =
           {v. \<exists> u \<in> set (wctx_sb K). u = v \<or> (\<exists> p. vwalk_bet (set (wctx_es K)) u p v)}"
proof-
  define c where "c = exch_ctx X"
  define es where "es = filter (tight c c1 c2) (exch_edges c)"
  define mT where "mT = list_max (c_lookup c2) (tgts c)"
  define sb where "sb = filter (\<lambda> y. c_lookup c1 y = list_max (c_lookup c1) (srcs c)) (srcs c)"
  define tb where "tb = filter (\<lambda> y. c_lookup c2 y = mT) (tgts c)"
  define ss where "ss = filter (has_tight_nb c c2) sb"
  define Gt where "Gt = build_graph es"
  have es_eq: "wctx_es K = es" and sb_eq: "wctx_sb K = sb" and tb_eq: "wctx_tb K = tb"
    by (simp_all add: K_def wtight_ctx_fields es_def sb_def tb_def mT_def c_def)
  have path_eq: "wctx_path K = (case find (\<lambda> y. in_T c y \<and> c_lookup c2 y = mT) sb of
                     Some s \<Rightarrow> Some [s]
                   | None \<Rightarrow> (if ss = [] then None else target_path Gt ss tb))"
    unfolding K_def wtight_ctx_path Let_def c_def es_def mT_def sb_def tb_def ss_def Gt_def ..
  have R_eq: "wctx_R K = foldr vset_insert (filter (\<lambda> y. \<not> has_tight_nb c c2 y) sb)
                  (if ss = [] then vset_empty else BFS_dist_state.visited (bfs_final Gt ss))"
    unfolding K_def wtight_ctx_R Let_def c_def es_def sb_def ss_def Gt_def ..
  show "set (wctx_es K) =
           weighted_intersection_graph.Gbar carrier indep1 indep2 (c_lookup c1) (c_lookup c2) (to_set X)"
    using tight_edges by (simp add: es_eq es_def c_def)
  show "set (wctx_sb K) = weighted_intersection_graph.Sbar carrier indep1 (c_lookup c1) (to_set X)"
    using sbar by (simp add: sb_eq sb_def c_def)
  show "set (wctx_tb K) = weighted_intersection_graph.Tbar carrier indep2 (c_lookup c2) (to_set X)"
    using tbar by (simp add: tb_eq tb_def mT_def c_def)
  have Gdig: "Graph.digraph_abs Gt = set es" by (simp add: Gt_def build_graph(4))
  have es_c: "set es \<subseteq> carrier \<times> carrier"
    using exch_edges_carrier[OF X] by (auto simp add: es_def c_def)
  have sb_srcs: "set sb \<subseteq> set (srcs c)" by (auto simp add: sb_def)
  have ss: "distinct ss" "set ss \<subseteq> set sb"
    using srcs(2)[OF X] by (auto simp add: ss_def sb_def c_def)
  have ss_iff: "u \<in> set ss \<longleftrightarrow> (\<exists> v. (u, v) \<in> set es)" if "u \<in> set sb" for u
    using that sb_srcs has_tight_nb by (auto simp add: ss_def es_def c_def)
  have ss_dVs: "set ss \<subseteq> dVs (Graph.digraph_abs Gt)"
  proof
    fix u assume u: "u \<in> set ss"
    then obtain v where "(u, v) \<in> set es" using ss_iff ss(2) by blast
    hence "(u, v) \<in> Graph.digraph_abs Gt" using Gdig by simp
    thus "u \<in> dVs (Graph.digraph_abs Gt)" by (rule dVsI(1))
  qed
  have intb: "in_T c y \<and> c_lookup c2 y = mT \<longleftrightarrow> y \<in> set tb" for y
    using in_T[OF X] tgts[OF X] by (auto simp add: tb_def c_def)
  have find_None: "find (\<lambda> y. in_T c y \<and> c_lookup c2 y = mT) sb = None \<longleftrightarrow> set sb \<inter> set tb = {}"
    using intb by (auto simp add: find_None_iff)
  have path_Some: "\<exists> u v. (vwalk_bet (set es) u p v \<or> (p = [u] \<and> u = v))
                  \<and> u \<in> set sb \<and> v \<in> set tb \<and>
             (\<nexists> p'. (vwalk_bet (set es) u p' v \<or> (p' = [u] \<and> u = v)) \<and> length p' < length p)"
    if P: "wctx_path K = Some p" for p
  proof(cases "find (\<lambda> y. in_T c y \<and> c_lookup c2 y = mT) sb")
    case None
    have ne: "ss \<noteq> []" and tp: "target_path Gt ss tb = Some p"
      using P None by (auto simp add: path_eq split: if_splits)
    obtain u v where uv: "u \<in> set ss" "v \<in> set tb" "vwalk_bet (Graph.digraph_abs Gt) u p v"
      "\<forall> u' p'. u' \<in> set ss \<and> vwalk_bet (Graph.digraph_abs Gt) u' p' v \<longrightarrow> length p \<le> length p'"
      using target_path(2)[OF Gt_def ss(1) ne ss_dVs es_c tp] by blast
    have "u \<noteq> v" using None find_None uv(1,2) ss(2) by auto
    hence short: "\<nexists> p'. (vwalk_bet (set es) u p' v \<or> (p' = [u] \<and> u = v)) \<and> length p' < length p"
      using uv(1,4) Gdig by (auto simp add: not_less[symmetric])
    have "vwalk_bet (set es) u p v" using uv(3) Gdig by simp
    thus ?thesis
      using uv(1,2) ss(2) short by (intro exI[of _ u] exI[of _ v]) auto
  next
    case (Some s)
    have p: "p = [s]" using P Some by (simp add: path_eq)
    have s: "s \<in> set sb" "s \<in> set tb" using Some intb by (auto simp add: find_Some_iff)
    show ?thesis
      using s p by (intro exI[of _ s] exI[of _ s]) (auto simp add: vwalk_bet_def)
  qed
  show "wctx_path K = Some p \<Longrightarrow>
           \<exists> u v. (vwalk_bet (set (wctx_es K)) u p v \<or> (p = [u] \<and> u = v))
                  \<and> u \<in> set (wctx_sb K) \<and> v \<in> set (wctx_tb K) \<and>
             (\<nexists> p'. (vwalk_bet (set (wctx_es K)) u p' v \<or> (p' = [u] \<and> u = v)) \<and> length p' < length p)"
    using path_Some unfolding es_eq sb_eq tb_eq .
  have no_path: False
    if none: "wctx_path K = None" and puv: "vwalk_bet (set es) u p v \<or> (p = [u] \<and> u = v)"
      "u \<in> set sb" "v \<in> set tb" for p u v
  proof-
    have fN: "find (\<lambda> y. in_T c y \<and> c_lookup c2 y = mT) sb = None"
      using none by (auto simp add: path_eq split: option.splits)
    hence "u \<noteq> v" using find_None puv(2,3) by auto
    hence walk: "vwalk_bet (set es) u p v" using puv(1) by auto
    obtain w where "(u, w) \<in> set es"
      using vwalk_then_edge[OF walk \<open>u \<noteq> v\<close>] by blast
    hence uss: "u \<in> set ss" using ss_iff puv(2) by blast
    hence ne: "ss \<noteq> []" by auto
    have "target_path Gt ss tb = None" using none fN ne by (simp add: path_eq)
    hence "\<nexists> u p v. u \<in> set ss \<and> v \<in> set tb \<and> vwalk_bet (Graph.digraph_abs Gt) u p v"
      by (rule target_path(1)[OF Gt_def ss(1) ne ss_dVs es_c])
    moreover have "vwalk_bet (Graph.digraph_abs Gt) u p v" using walk Gdig by simp
    ultimately show False using uss puv(3) by blast
  qed
  show "wctx_path K = None \<longleftrightarrow>
           (\<nexists> p u v. (vwalk_bet (set (wctx_es K)) u p v \<or> (p = [u] \<and> u = v))
                     \<and> u \<in> set (wctx_sb K) \<and> v \<in> set (wctx_tb K))"
    unfolding es_eq sb_eq tb_eq
  proof (rule iffI)
    assume "wctx_path K = None"
    thus "\<nexists> p u v. (vwalk_bet (set es) u p v \<or> (p = [u] \<and> u = v)) \<and> u \<in> set sb \<and> v \<in> set tb"
      using no_path by blast
  next
    assume np: "\<nexists> p u v. (vwalk_bet (set es) u p v \<or> (p = [u] \<and> u = v)) \<and> u \<in> set sb \<and> v \<in> set tb"
    show "wctx_path K = None"
    proof (cases "wctx_path K")
      case (Some p)
      then obtain u v where "(vwalk_bet (set es) u p v \<or> (p = [u] \<and> u = v)) \<and> u \<in> set sb \<and> v \<in> set tb"
        using path_Some by blast
      hence False using np by blast
      thus ?thesis ..
    qed
  qed
  text \<open>The reachable set: the BFS visits exactly the vertices reachable from the sources with
    tight out-edges, and the other sources reach only themselves.\<close>
  have vis: "vset_inv (if ss = [] then vset_empty else BFS_dist_state.visited (bfs_final Gt ss)) \<and>
             t_set (if ss = [] then vset_empty else BFS_dist_state.visited (bfs_final Gt ss))
               = {v. \<exists> u \<in> set ss. \<exists> q. vwalk_bet (set es) u q v}"
  proof(cases "ss = []")
    case True
    thus ?thesis by (simp add: Graph.vset.set.set_empty Graph.vset.set.invar_empty)
  next
    case False
    obtain exp_tree nfc dist_invar parent_abstract parent_invar par_U par_roots where B:
      "BFS_distance_parents (\<lambda> x. None) (\<lambda> x G. G(x := None)) vset_insert isin t_set sel 
         (\<lambda> x N G. G(x := Some N)) (\<lambda> G. True) vset_empty 
         vset_delete vset_inv union inter diff Gt exp_tree nfc vset_inv2 some_dist dist_lookup 
         dist_invar (\<lambda> G x. G x) set_all_dists_in_set parent_abstract parent_invar par_U get_path
         par_roots parent_init (next_frontier_current_parents Gt)"
      by (rule bfs_inst[OF Gt_def es_c])
    note ax = bfs_axiomI[OF Gt_def ss(1) False ss_dVs es_c]
    have fin_is: "bfs_final Gt ss = BFS_distance_parents.BFS_par_impl vset_empty set_all_dists_in_set 
       (next_frontier_current_parents Gt)
       (BFS_distance_parents.initial_par_state (vset_of_list ss) some_dist set_all_dists_in_set 
           parent_init)"
      by (simp add: bfs_final_def)
    have "vset_inv (BFS_dist_state.visited (bfs_final Gt ss))"
      using BFS_distance_parents.BFS_par_visited_inv[OF B ax] by (simp add: fin_is)
    moreover have "t_set (BFS_dist_state.visited (bfs_final Gt ss))
                     = {v. \<exists> u \<in> set ss. \<exists> q. vwalk_bet (set es) u q v}"
      using BFS_distance_parents.BFS_par_correct(1)[OF B ax fin_is] vset_of_list(2)[OF ss(1)]
      by (auto simp add: Gdig)
    ultimately show ?thesis using False by simp
  qed
  define dr where "dr = filter (\<lambda> y. \<not> has_tight_nb c c2 y) sb"
  have R: "vset_inv (wctx_R K)"
    "t_set (wctx_R K) = set dr \<union> {v. \<exists> u \<in> set ss. \<exists> q. vwalk_bet (set es) u q v}"
    using foldr_vset_insert[OF conjunct1[OF vis], of dr] vis by (simp_all add: R_eq dr_def)
  show "vset_inv (wctx_R K)" by (rule R(1))
  have dr_iff: "u \<in> set dr \<longleftrightarrow> u \<in> set sb \<and> u \<notin> set ss" for u
    by (auto simp add: dr_def ss_def)
  show "t_set (wctx_R K) =
           {v. \<exists> u \<in> set (wctx_sb K). u = v \<or> (\<exists> p. vwalk_bet (set (wctx_es K)) u p v)}"
    unfolding sb_eq es_eq
  proof (rule set_eqI, rule iffI)
    fix v assume "v \<in> t_set (wctx_R K)"
    thus "v \<in> {v. \<exists> u \<in> set sb. u = v \<or> (\<exists> p. vwalk_bet (set es) u p v)}"
      using R(2) dr_iff ss(2) by auto
  next
    fix v assume "v \<in> {v. \<exists> u \<in> set sb. u = v \<or> (\<exists> p. vwalk_bet (set es) u p v)}"
    then obtain u where u: "u \<in> set sb" "u = v \<or> (\<exists> p. vwalk_bet (set es) u p v)"
      by blast
    show "v \<in> t_set (wctx_R K)"
    proof (cases "u \<in> set ss")
      case True
      have "\<exists> q. vwalk_bet (set es) u q v"
      proof (cases "u = v")
        case True
        have "u \<in> dVs (set es)" using ss_dVs \<open>u \<in> set ss\<close> Gdig by auto
        thus ?thesis unfolding True by (blast intro: vwalk_bet_reflexive)
      qed (use u(2) in blast)
      thus ?thesis using R(2) True by auto
    next
      case False
      hence udr: "u \<in> set dr" using dr_iff u(1) by simp
      have "u = v"
      proof (rule ccontr)
        assume uv: "u \<noteq> v"
        then obtain p where p: "vwalk_bet (set es) u p v" using u(2) by auto
        obtain w where "(u, w) \<in> set es" using vwalk_then_edge[OF p uv] by auto
        hence "u \<in> set ss" using ss_iff[OF u(1)] by auto
        thus False using False by simp
      qed
      thus ?thesis using R(2) udr by auto
    qed
  qed
qed


text \<open>The pass of @{term weps} computes the minimum boundary gap of the reachable set.\<close>

lemma weps_eq:
  "weps (wtight_ctx X c1 c2) =
     eps_of (weighted_intersection_graph.gaps carrier indep1 indep2 (c_lookup c1) (c_lookup c2)
       (to_set X) (weighted_intersection_graph.Rbar carrier indep1 indep2 (c_lookup c1) (c_lookup c2)
       (to_set X))) None"
proof-
  interpret W: weighted_intersection_graph carrier indep1 indep2 "c_lookup c1" "c_lookup c2"
    by unfold_locales
  define K where "K = wtight_ctx X c1 c2"
  define R where "R = wctx_R K"
  note props = wtight_ctx_props[folded K_def]
  have Rinv: "vset_inv R" using props(6) by (simp add: R_def)
  have isinR: "isin R z \<longleftrightarrow> z \<in> t_set R" for z using Graph.vset.set.set_isin[OF Rinv] .
  have Rset: "t_set R = W.Rbar (to_set X)"
    using props(7) props(1,2) by (simp add: R_def W.Rbar_def)
  have A1X: "fst e \<in> to_set X" if "e \<in> A1 (to_set X)" for e
    using A1_edges(1)[OF X(3,4) that] .
  have A2X: "fst e \<notin> to_set X" if "e \<in> A2 (to_set X)" for e
    using A2_edges(2)[OF X(3,4) that] by simp
  define g where "g = (\<lambda> e. if set_memb (fst e) X then c_lookup c1 (fst e) - c_lookup c1 (snd e)
                           else c_lookup c2 (snd e) - c_lookup c2 (fst e))"
  define GE where "GE = g ` {e \<in> set (exch_edges (exch_ctx X)). isin R (fst e) \<and> \<not> isin R (snd e)}"
  define GS where "GS = (\<lambda> y. list_max (c_lookup c1) (srcs (exch_ctx X)) - c_lookup c1 y)
                          ` {y \<in> set (srcs (exch_ctx X)). \<not> isin R y}"
  define GT where "GT = (\<lambda> y. list_max (c_lookup c2) (tgts (exch_ctx X)) - c_lookup c2 y)
                          ` {y \<in> set (tgts (exch_ctx X)). isin R y}"
  have fins: "finite GE" "finite GS" "finite GT"
    unfolding GE_def GS_def GT_def by (rule finite_imageI, rule finite_subset[OF _ finite_set], blast)+
  have "weps K = eps_of GT (eps_of GS (eps_of GE None))"
    unfolding weps_def Let_def K_def wtight_ctx_fields R_def[unfolded K_def, symmetric]
      ctx_simps[OF X] GE_def GS_def GT_def g_def
    by (simp only: foldr_eps_of)
  also have "\<dots> = eps_of (GT \<union> (GS \<union> GE)) None"
    using fins by (simp add: eps_of_Un)
  also have "GT \<union> (GS \<union> GE) = W.gaps (to_set X) (t_set R)"
  proof-
    have GE: "GE = {c_lookup c1 x - c_lookup c1 y | x y. (x, y) \<in> A1 (to_set X) \<and> x \<in> t_set R \<and> y \<notin> t_set R}
               \<union> {c_lookup c2 x - c_lookup c2 y | x y. (y, x) \<in> A2 (to_set X) \<and> y \<in> t_set R \<and> x \<notin> t_set R}"
    proof (rule set_eqI, rule iffI)
      fix v assume "v \<in> GE"
      then obtain e where e: "e \<in> set (exch_edges (exch_ctx X))" "isin R (fst e)" "\<not> isin R (snd e)"
        "v = g e"
        unfolding GE_def by blast
      obtain a b where e_eq: "e = (a, b)" by (cases e)
      have ab: "(a, b) \<in> A1 (to_set X) \<union> A2 (to_set X)" "a \<in> t_set R" "b \<notin> t_set R"
        using e exchange_edges[OF X] isinR by (simp_all add: e_eq)
      show "v \<in> {c_lookup c1 x - c_lookup c1 y | x y. (x, y) \<in> A1 (to_set X) \<and> x \<in> t_set R \<and> y \<notin> t_set R}
               \<union> {c_lookup c2 x - c_lookup c2 y | x y. (y, x) \<in> A2 (to_set X) \<and> y \<in> t_set R \<and> x \<notin> t_set R}"
      proof (cases "(a, b) \<in> A1 (to_set X)")
        case True
        hence "v = c_lookup c1 a - c_lookup c1 b"
          using e(4) A1X[OF True] set_memb[OF X(1)] by (simp add: g_def e_eq)
        thus ?thesis using True ab(2,3) by auto
      next
        case False
        hence A2: "(a, b) \<in> A2 (to_set X)" using ab(1) by simp
        hence "v = c_lookup c2 b - c_lookup c2 a"
          using e(4) A2X[OF A2] set_memb[OF X(1)] by (simp add: g_def e_eq)
        thus ?thesis using A2 ab(2,3) by auto
      qed
    next
      fix v assume "v \<in> {c_lookup c1 x - c_lookup c1 y | x y. (x, y) \<in> A1 (to_set X) \<and> x \<in> t_set R \<and> y \<notin> t_set R}
               \<union> {c_lookup c2 x - c_lookup c2 y | x y. (y, x) \<in> A2 (to_set X) \<and> y \<in> t_set R \<and> x \<notin> t_set R}"
      thus "v \<in> GE"
      proof
        assume "v \<in> {c_lookup c1 x - c_lookup c1 y | x y. (x, y) \<in> A1 (to_set X) \<and> x \<in> t_set R \<and> y \<notin> t_set R}"
        then obtain x y where xy: "(x, y) \<in> A1 (to_set X)" "x \<in> t_set R" "y \<notin> t_set R"
          "v = c_lookup c1 x - c_lookup c1 y" by blast
        have "v = g (x, y)" using xy(4) A1X[OF xy(1)] set_memb[OF X(1)] by (simp add: g_def)
        thus "v \<in> GE" unfolding GE_def
          by (rule image_eqI) (use xy exchange_edges[OF X] isinR in auto)
      next
        assume "v \<in> {c_lookup c2 x - c_lookup c2 y | x y. (y, x) \<in> A2 (to_set X) \<and> y \<in> t_set R \<and> x \<notin> t_set R}"
        then obtain x y where xy: "(y, x) \<in> A2 (to_set X)" "y \<in> t_set R" "x \<notin> t_set R"
          "v = c_lookup c2 x - c_lookup c2 y" by blast
        have "v = g (y, x)" using xy(4) A2X[OF xy(1)] set_memb[OF X(1)] by (simp add: g_def)
        thus "v \<in> GE" unfolding GE_def
          by (rule image_eqI) (use xy exchange_edges[OF X] isinR in auto)
      qed
    qed
    have GS: "GS = {Max (c_lookup c1 ` S (to_set X)) - c_lookup c1 y | y. y \<in> S (to_set X) \<and> y \<notin> t_set R}"
    proof (cases "srcs (exch_ctx X) = []")
      case True thus ?thesis using srcs(1)[OF X] by (simp add: GS_def)
    next
      case False
      have "list_max (c_lookup c1) (srcs (exch_ctx X)) = Max (c_lookup c1 ` S (to_set X))"
        using list_max[OF False] srcs(1)[OF X] by simp
      thus ?thesis using srcs(1)[OF X] isinR by (auto simp add: GS_def)
    qed
    have GT: "GT = {Max (c_lookup c2 ` T (to_set X)) - c_lookup c2 y | y. y \<in> T (to_set X) \<and> y \<in> t_set R}"
    proof (cases "tgts (exch_ctx X) = []")
      case True thus ?thesis using tgts[OF X] by (simp add: GT_def)
    next
      case False
      have "list_max (c_lookup c2) (tgts (exch_ctx X)) = Max (c_lookup c2 ` T (to_set X))"
        using list_max[OF False] tgts[OF X] by simp
      thus ?thesis using tgts[OF X] isinR by (auto simp add: GT_def)
    qed
    show ?thesis unfolding W.gaps_def GE GS GT by (simp only: Un_ac)
  qed
  finally show ?thesis unfolding K_def Rset .
qed

end

subsubsection \<open>Total Correctness\<close>

text \<open>The invariant of a context: it was built for a common independent set.\<close>

definition "wctx_invar X c1 c2 K \<longleftrightarrow>
  K = wtight_ctx X c1 c2 \<and> set_invar X \<and> to_set X \<subseteq> carrier \<and> indep1 (to_set X) \<and> indep2 (to_set X)"

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
  using wtight_ctx_props(1-3) by (auto simp add: wctx_invar_def)

lemma wctx_path_spec:
  "wctx_invar X c1 c2 K \<Longrightarrow> wctx_path K = None \<longleftrightarrow>
     (\<nexists> p u v. (vwalk_bet (set (wctx_es K)) u p v \<or> (p = [u] \<and> u = v))
               \<and> u \<in> set (wctx_sb K) \<and> v \<in> set (wctx_tb K))"
  "\<lbrakk>wctx_invar X c1 c2 K; wctx_path K = Some p\<rbrakk> \<Longrightarrow>
     \<exists> u v. (vwalk_bet (set (wctx_es K)) u p v \<or> (p = [u] \<and> u = v))
            \<and> u \<in> set (wctx_sb K) \<and> v \<in> set (wctx_tb K) \<and>
       (\<nexists> p'. (vwalk_bet (set (wctx_es K)) u p' v \<or> (p' = [u] \<and> u = v)) \<and> length p' < length p)"
  using wtight_ctx_props(4,5) by (auto simp add: wctx_invar_def)

lemma wctx_reach_spec:
  "\<lbrakk>wctx_invar X c1 c2 K; wctx_path K = None\<rbrakk> \<Longrightarrow> vset_inv (wctx_R K)"
  "\<lbrakk>wctx_invar X c1 c2 K; wctx_path K = None\<rbrakk> \<Longrightarrow>
     t_set (wctx_R K) = {v. \<exists> u \<in> set (wctx_sb K). u = v \<or> (\<exists> p. vwalk_bet (set (wctx_es K)) u p v)}"
  using wtight_ctx_props(6,7) by (auto simp add: wctx_invar_def)

lemma weps_spec:
  "\<lbrakk>wctx_invar X c1 c2 K; wctx_path K = None\<rbrakk> \<Longrightarrow>
     weps K = eps_of (weighted_intersection_graph.gaps carrier indep1 indep2 (c_lookup c1)
                 (c_lookup c2) (to_set X) (weighted_intersection_graph.Rbar carrier indep1 indep2
                 (c_lookup c1) (c_lookup c2) (to_set X))) None"
  using weps_eq by (auto simp add: wctx_invar_def)

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

