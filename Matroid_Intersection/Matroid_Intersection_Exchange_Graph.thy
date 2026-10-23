theory Matroid_Intersection_Exchange_Graph
  imports Exchange_Oracles Matroid_Intersection_Path_Loop "Graph_Algorithms_Dev.BFS_3"
begin

section \<open>Matroid Intersection on the Exchange Graph\<close>

text \<open>The only layer connecting the augmentation loop
  (@{theory Matroid_Intersection.Matroid_Intersection_Path_Loop}), the oracle facts
  (@{theory Matroid_Intersection.Exchange_Oracles}) and the BFS
  (@{theory Graph_Algorithms_Dev.BFS_3}). Per iteration, the exchange edges are computed as a
  list from a context and turned into a graph by an abstract @{term build_graph}
  (CSR in the imperative instance). The BFS is used as it is; the only extra step is dropping
  sources without out-edges before calling it.\<close>

record ('mset, 'o1, 'o2, 'a) exch_ctx =
  ctx_X :: "'mset"
  ctx_o1 :: "'o1"
  ctx_o2 :: "'o2"
  ctx_S :: "'mset"
  ctx_T :: "'mset"
  ctx_inX :: "'a list"
  ctx_notX :: "'a list"

subsection \<open>Code\<close>

locale unweighted_intersection_exchange_spec =
  fixes set_insert :: "'a \<Rightarrow> 'mset \<Rightarrow> 'mset"
    and set_delete :: "'a \<Rightarrow> 'mset \<Rightarrow> 'mset"
    and to_set :: "'mset \<Rightarrow> 'a set"
    and set_invar :: "'mset \<Rightarrow> bool"
    and set_empty :: "'mset"
    and set_memb :: "'a \<Rightarrow> 'mset \<Rightarrow> bool"
    and carrier_list :: "'a list"
    and orcl_prep1 :: "'mset \<Rightarrow> 'o1"
    and ins_orcl1 :: "'o1 \<Rightarrow> 'a \<Rightarrow> bool"
    and exch_orcl1 :: "'o1 \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
    and orcl_prep2 :: "'mset \<Rightarrow> 'o2"
    and ins_orcl2 :: "'o2 \<Rightarrow> 'a \<Rightarrow> bool"
    and exch_orcl2 :: "'o2 \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
    and vset_empty :: "'vset"
    and isin :: "'vset \<Rightarrow> 'a \<Rightarrow> bool"
    and vset_of_list :: "'a list \<Rightarrow> 'vset"
    and some_dist :: "'dist"
    and set_all_dists_in_set :: "'dist \<Rightarrow> 'vset \<Rightarrow> nat \<Rightarrow> 'dist"
    and dist_lookup :: "'dist \<Rightarrow> 'a \<Rightarrow> nat"
    and parent_init :: "'vset \<Rightarrow> 'par"
    and get_path :: "'par \<Rightarrow> 'a \<Rightarrow> 'a list"
    and next_frontier_current_parents :: 
          "('a \<Rightarrow> 'vset option) \<Rightarrow> 'vset \<Rightarrow> 'vset \<Rightarrow> 'par \<Rightarrow> 'vset \<times> 'vset \<times> 'par"
    and build_graph :: "('a \<times> 'a) list \<Rightarrow> 'a \<Rightarrow> 'vset option"
begin

text \<open>A predicate cached as a set over a list of elements.\<close>

definition "cache P xs = foldl (\<lambda> S y. if P y then set_insert y S else S) set_empty xs"

text \<open>The context of one iteration: the solution, the prepared oracle contexts, the cached
  sources and targets and the elements inside and outside the solution.\<close>

definition "exch_ctx X =
  (let o1 = orcl_prep1 X; o2 = orcl_prep2 X;
       notX = filter (\<lambda> x. \<not> set_memb x X) carrier_list
   in \<lparr>ctx_X = X, ctx_o1 = o1, ctx_o2 = o2, 
       ctx_S = cache (ins_orcl1 o1) notX, ctx_T = cache (ins_orcl2 o2) notX,
       ctx_inX = filter (\<lambda> x. set_memb x X) carrier_list, ctx_notX = notX\<rparr>)"

definition "in_S c y = set_memb y (ctx_S c)"
definition "in_T c y = set_memb y (ctx_T c)"

text \<open>Out-neighbours of an element of the solution (exchange edges of the first matroid) and
  of an element outside the solution (exchange edges of the second matroid).\<close>

definition "out1 c x = filter (\<lambda> y. \<not> in_S c y \<and> exch_orcl1 (ctx_o1 c) x y) (ctx_notX c)"
definition "out2 c y = filter (\<lambda> x. exch_orcl2 (ctx_o2 c) x y) (ctx_inX c)"

text \<open>All exchange edges. Targets have no out-edges, since a shortest path ends at its first
  target.\<close>

definition "exch_edges c = 
  concat (map (\<lambda> x. map (Pair x) (out1 c x)) (ctx_inX c)) @
  concat (map (\<lambda> y. map (Pair y) (out2 c y)) (filter (\<lambda> y. \<not> in_T c y) (ctx_notX c)))"

text \<open>Sources are outside the solution, so only exchange edges of the second matroid matter.
  The test stops at the first neighbour found.\<close>

definition "has_nb c y = (\<not> in_T c y \<and> list_ex (\<lambda> x. exch_orcl2 (ctx_o2 c) x y) (ctx_inX c))"

definition "srcs c = filter (in_S c) (ctx_notX c)"
definition "tgts c = filter (in_T c) (ctx_notX c)"

definition "bfs_final G S = 
   BFS_distance_parents.BFS_par_impl vset_empty set_all_dists_in_set 
     (next_frontier_current_parents G)
     (BFS_distance_parents.initial_par_state (vset_of_list S) some_dist set_all_dists_in_set 
         parent_init)"

text \<open>The first target visited by the BFS and the parent path to it.\<close>

definition "target_path G S ts =
   (let fin = bfs_final G S in
     case find (isin (BFS_dist_state.visited fin)) ts of
       None \<Rightarrow> None
     | Some t \<Rightarrow> Some (rev (get_path (parent fin) t)))"

text \<open>A source that is a target is a path on its own. Otherwise, sources without out-edges
  are dropped before the BFS.\<close>

definition "augmenting_path X =
  (let c = exch_ctx X; ss = srcs c in
   case find (in_T c) ss of 
     Some s \<Rightarrow> Some [s]
   | None \<Rightarrow> 
      (let ss' = filter (has_nb c) ss in
        if ss' = [] then None else target_path (build_graph (exch_edges c)) ss' (tgts c)))"

sublocale path_loop: unweighted_intersection_path_loop_spec 
  set_insert set_delete to_set set_invar set_empty augmenting_path .

lemmas [code] = cache_def exch_ctx_def in_S_def in_T_def out1_def out2_def exch_edges_def has_nb_def
  srcs_def tgts_def bfs_final_def target_path_def augmenting_path_def

end

subsection \<open>Correctness\<close>

text \<open>The assumptions on the matroids, their oracles and the solution sets.\<close>

locale unweighted_intersection_exchange_matroids =
  double_matroid carrier indep1 indep2 +
  matroid1: indep_oracle orcl_prep1 ins_orcl1 exch_orcl1 carrier indep1 to_set set_invar +
  matroid2: indep_oracle orcl_prep2 ins_orcl2 exch_orcl2 carrier indep2 to_set set_invar
  for carrier :: "'a set" and indep1 indep2
    and orcl_prep1 :: "'mset \<Rightarrow> 'o1" and ins_orcl1 exch_orcl1
    and orcl_prep2 :: "'mset \<Rightarrow> 'o2" and ins_orcl2 exch_orcl2
    and to_set :: "'mset \<Rightarrow> 'a set" and set_invar +
  fixes set_insert :: "'a \<Rightarrow> 'mset \<Rightarrow> 'mset"
    and set_delete :: "'a \<Rightarrow> 'mset \<Rightarrow> 'mset"
    and set_empty :: "'mset"
    and set_memb :: "'a \<Rightarrow> 'mset \<Rightarrow> bool"
    and carrier_list :: "'a list"
  assumes set_insert: "\<And> S x. \<lbrakk>set_invar S; x \<in> carrier\<rbrakk> \<Longrightarrow> set_invar (set_insert x S)"
    "\<And> S x. \<lbrakk>set_invar S; x \<in> carrier\<rbrakk> \<Longrightarrow> to_set (set_insert x S) = Set.insert x (to_set S)"
  assumes set_delete: "\<And> S x. \<lbrakk>set_invar S; x \<in> carrier\<rbrakk> \<Longrightarrow> set_invar (set_delete x S)"
    "\<And> S x. \<lbrakk>set_invar S; x \<in> carrier\<rbrakk> \<Longrightarrow> to_set (set_delete x S) = (to_set S) - {x}"
  assumes set_empty: "set_invar set_empty" "to_set set_empty = {}"
  assumes set_memb: "\<And> S x. set_invar S \<Longrightarrow> set_memb x S \<longleftrightarrow> x \<in> to_set S"
  assumes carrier_list: "set carrier_list = carrier" "distinct carrier_list"

text \<open>The assumptions on the graph construction and the BFS.\<close>

locale unweighted_intersection_exchange =
  unweighted_intersection_exchange_spec set_insert set_delete to_set set_invar set_empty set_memb
    carrier_list orcl_prep1 ins_orcl1 exch_orcl1 orcl_prep2 ins_orcl2 exch_orcl2
    vset_empty isin vset_of_list some_dist set_all_dists_in_set dist_lookup parent_init
    get_path next_frontier_current_parents build_graph +
  unweighted_intersection_exchange_matroids carrier indep1 indep2 orcl_prep1 ins_orcl1 exch_orcl1
    orcl_prep2 ins_orcl2 exch_orcl2 to_set set_invar set_insert set_delete set_empty set_memb
    carrier_list +
  Graph: Pair_Graph_Specs 
  where lookup = "\<lambda> G x. G x" and empty = "\<lambda> x. None" and update = "\<lambda> x N G. G(x := Some N)"
    and delete = "\<lambda> x G. G(x := None)" and adjmap_inv = "\<lambda> G. True" 
    and vset_empty = vset_empty and isin = isin +
  set_ops: Set2 vset_empty vset_delete isin t_set vset_inv insert
  for set_insert :: "'a \<Rightarrow> 'mset \<Rightarrow> 'mset"
    and set_delete :: "'a \<Rightarrow> 'mset \<Rightarrow> 'mset"
    and to_set :: "'mset \<Rightarrow> 'a set"
    and set_invar :: "'mset \<Rightarrow> bool"
    and set_empty :: "'mset"
    and set_memb :: "'a \<Rightarrow> 'mset \<Rightarrow> bool"
    and carrier_list :: "'a list"
    and orcl_prep1 :: "'mset \<Rightarrow> 'o1"
    and ins_orcl1 :: "'o1 \<Rightarrow> 'a \<Rightarrow> bool"
    and exch_orcl1 :: "'o1 \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
    and orcl_prep2 :: "'mset \<Rightarrow> 'o2"
    and ins_orcl2 :: "'o2 \<Rightarrow> 'a \<Rightarrow> bool"
    and exch_orcl2 :: "'o2 \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
    and vset_empty :: "'vset"
    and isin :: "'vset \<Rightarrow> 'a \<Rightarrow> bool"
    and vset_of_list :: "'a list \<Rightarrow> 'vset"
    and some_dist :: "'dist"
    and set_all_dists_in_set :: "'dist \<Rightarrow> 'vset \<Rightarrow> nat \<Rightarrow> 'dist"
    and dist_lookup :: "'dist \<Rightarrow> 'a \<Rightarrow> nat"
    and parent_init :: "'vset \<Rightarrow> 'par"
    and get_path :: "'par \<Rightarrow> 'a \<Rightarrow> 'a list"
    and next_frontier_current_parents :: 
          "('a \<Rightarrow> 'vset option) \<Rightarrow> 'vset \<Rightarrow> 'vset \<Rightarrow> 'par \<Rightarrow> 'vset \<times> 'vset \<times> 'par"
    and build_graph :: "('a \<times> 'a) list \<Rightarrow> 'a \<Rightarrow> 'vset option"
    and carrier :: "'a set" and indep1 indep2 +
  fixes vset_inv2 :: "'vset \<Rightarrow> bool" 
  assumes build_graph: 
    "\<And> es. Graph.graph_inv (build_graph es)" "\<And> es. Graph.finite_graph (build_graph es)" 
    "\<And> es. Graph.finite_vsets (build_graph es)" 
    "\<And> es. Graph.digraph_abs (build_graph es) = set es"
  assumes bfs: 
    "\<And> es. set es \<subseteq> carrier \<times> carrier \<Longrightarrow>
       \<exists> exp_tree nfc dist_invar parent_abstract parent_invar par_U par_roots. 
       BFS_distance_parents (\<lambda> x. None) (\<lambda> x G. G(x := None)) insert isin t_set sel 
         (\<lambda> x N G. G(x := Some N)) (\<lambda> G. True) vset_empty 
         vset_delete vset_inv union inter diff (build_graph es) exp_tree nfc vset_inv2 some_dist 
         dist_lookup dist_invar (\<lambda> G x. G x) set_all_dists_in_set parent_abstract parent_invar
         par_U get_path par_roots parent_init (next_frontier_current_parents (build_graph es))"
  assumes vset_of_list:
    "\<And> xs. distinct xs \<Longrightarrow> vset_inv2 (vset_of_list xs)"
    "\<And> xs. distinct xs \<Longrightarrow> t_set (vset_of_list xs) = set xs"
begin

subsubsection \<open>The BFS on Built Graphs\<close>

abbreviation "graph_ok G \<equiv> Graph.graph_inv G \<and> Graph.finite_graph G \<and> Graph.finite_vsets G"

lemma bfs_inst:
  assumes "G = build_graph es" "set es \<subseteq> carrier \<times> carrier"
  obtains exp_tree nfc dist_invar parent_abstract parent_invar par_U par_roots where 
    "BFS_distance_parents (\<lambda> x. None) (\<lambda> x G. G(x := None)) insert isin t_set sel 
         (\<lambda> x N G. G(x := Some N)) (\<lambda> G. True) vset_empty 
         vset_delete vset_inv union inter diff G exp_tree nfc vset_inv2 some_dist dist_lookup 
         dist_invar (\<lambda> G x. G x) set_all_dists_in_set parent_abstract parent_invar par_U get_path
         par_roots parent_init (next_frontier_current_parents G)"
  using bfs[OF assms(2)] unfolding assms(1)[symmetric] by (elim exE) (rule that)

lemma bfs_of_bfs_dp:
  assumes "BFS_distance_parents (\<lambda> x. None) (\<lambda> x G. G(x := None)) insert isin t_set sel 
         (\<lambda> x N G. G(x := Some N)) (\<lambda> G. True) vset_empty 
         vset_delete vset_inv union inter diff G exp_tree nfc vset_inv2 some_dist dist_lookup 
         dist_invar (\<lambda> G x. G x) set_all_dists_in_set parent_abstract parent_invar par_U get_path
         par_roots parent_init (next_frontier_current_parents G)"
  shows "BFS_3.BFS (\<lambda> x. None) (\<lambda> x G. G(x := None)) insert isin t_set sel 
         (\<lambda> x N G. G(x := Some N)) (\<lambda> G. True) vset_empty vset_delete vset_inv 
         union inter diff (\<lambda> G x. G x) G exp_tree nfc vset_inv2"
  using assms unfolding BFS_distance_parents_def BFS_distance_def by blast

lemma vset_of_list_inv: "distinct xs \<Longrightarrow> vset_inv (vset_of_list xs)"
proof-
  assume "distinct xs"
  obtain exp_tree nfc dist_invar parent_abstract parent_invar par_U par_roots where B: 
    "BFS_distance_parents (\<lambda> x. None) (\<lambda> x G. G(x := None)) insert isin t_set sel 
         (\<lambda> x N G. G(x := Some N)) (\<lambda> G. True) vset_empty 
         vset_delete vset_inv union inter diff (build_graph []) exp_tree nfc vset_inv2 some_dist 
         dist_lookup dist_invar (\<lambda> G x. G x) set_all_dists_in_set parent_abstract parent_invar
         par_U get_path par_roots parent_init (next_frontier_current_parents (build_graph []))"
    by (rule bfs_inst[OF refl, where es = "[]"]) simp
  show ?thesis
    using BFS_3.BFS.vset_inv2[OF bfs_of_bfs_dp[OF B] vset_of_list(1)[OF \<open>distinct xs\<close>]] .
qed

lemma isin_vset_of_list: "distinct xs \<Longrightarrow> isin (vset_of_list xs) v \<longleftrightarrow> v \<in> set xs"
  using vset_of_list_inv[of xs] vset_of_list(2)[of xs] Graph.vset.set.set_isin by simp

lemma bfs_axiomI:
  assumes "G = build_graph es" "distinct ss" "ss \<noteq> []" "set ss \<subseteq> dVs (Graph.digraph_abs G)"
    "set es \<subseteq> carrier \<times> carrier"
  shows "BFS_3.BFS.BFS_axiom isin t_set (\<lambda> G. True) vset_empty vset_inv (\<lambda> G x. G x)
           (vset_of_list ss) G vset_inv2"
proof-
  obtain exp_tree nfc dist_invar parent_abstract parent_invar par_U par_roots where B: 
    "BFS_distance_parents (\<lambda> x. None) (\<lambda> x G. G(x := None)) insert isin t_set sel 
         (\<lambda> x N G. G(x := Some N)) (\<lambda> G. True) vset_empty 
         vset_delete vset_inv union inter diff G exp_tree nfc vset_inv2 some_dist dist_lookup 
         dist_invar (\<lambda> G x. G x) set_all_dists_in_set parent_abstract parent_invar par_U get_path
         par_roots parent_init (next_frontier_current_parents G)"
    by (rule bfs_inst[OF assms(1,5)])
  have "graph_ok G"
    using build_graph assms(1) by simp
  then show ?thesis
    using assms(2-4) vset_of_list[OF assms(2)] Graph.finite_neighbourhoods[of G]
    by (simp add: BFS_3.BFS.BFS_axiom_def[OF bfs_of_bfs_dp[OF B]])
qed

lemma target_path:
  assumes "G = build_graph es" "distinct ss" "ss \<noteq> []" "set ss \<subseteq> dVs (Graph.digraph_abs G)"
    "set es \<subseteq> carrier \<times> carrier"
  shows "target_path G ss ts = None \<Longrightarrow>
           \<nexists> u p v. u \<in> set ss \<and> v \<in> set ts \<and> vwalk_bet (Graph.digraph_abs G) u p v"
    and "target_path G ss ts = Some p \<Longrightarrow>
           \<exists> u v. u \<in> set ss \<and> v \<in> set ts \<and> vwalk_bet (Graph.digraph_abs G) u p v \<and>
             (\<forall> u' p'. u' \<in> set ss \<and> vwalk_bet (Graph.digraph_abs G) u' p' v 
                        \<longrightarrow> length p \<le> length p')"
proof-
  obtain exp_tree nfc dist_invar parent_abstract parent_invar par_U par_roots where B:
    "BFS_distance_parents (\<lambda> x. None) (\<lambda> x G. G(x := None)) insert isin t_set sel 
         (\<lambda> x N G. G(x := Some N)) (\<lambda> G. True) vset_empty 
         vset_delete vset_inv union inter diff G exp_tree nfc vset_inv2 some_dist dist_lookup 
         dist_invar (\<lambda> G x. G x) set_all_dists_in_set parent_abstract parent_invar par_U get_path
         par_roots parent_init (next_frontier_current_parents G)"
    by (rule bfs_inst[OF assms(1,5)])
  note ax = bfs_axiomI[OF assms]
  define fin where "fin = bfs_final G ss"
  have fin_is: "fin = BFS_distance_parents.BFS_par_impl vset_empty set_all_dists_in_set 
     (next_frontier_current_parents G)
     (BFS_distance_parents.initial_par_state (vset_of_list ss) some_dist set_all_dists_in_set 
         parent_init)"
    by (simp add: fin_def bfs_final_def)
  have srcs: "t_set (vset_of_list ss) = set ss"
    using vset_of_list(2)[OF assms(2)] .
  have isin_vis: "isin (BFS_dist_state.visited fin) x \<longleftrightarrow> x \<in> t_set (BFS_dist_state.visited fin)"
    for x
    using BFS_distance_parents.BFS_par_visited_inv[OF B ax] fin_is
    by (simp add: Graph.vset.set.set_isin)
  note correct = BFS_distance_parents.BFS_par_correct(1)[OF B ax fin_is]
  show "target_path G ss ts = None \<Longrightarrow>
           \<nexists> u p v. u \<in> set ss \<and> v \<in> set ts \<and> vwalk_bet (Graph.digraph_abs G) u p v"
  proof(rule notI, goal_cases)
    case 1
    then obtain u p v where uv: "u \<in> set ss" "v \<in> set ts" "vwalk_bet (Graph.digraph_abs G) u p v"
      by blast
    hence "isin (BFS_dist_state.visited fin) v"
      using correct[of v] srcs isin_vis by blast
    hence "find (isin (BFS_dist_state.visited fin)) ts \<noteq> None"
      using uv(2) by (auto simp add: find_None_iff)
    then show ?case 
      using 1(1) by (auto simp add: target_path_def fin_def[symmetric] split: option.splits)
  qed
  show "target_path G ss ts = Some p \<Longrightarrow>
           \<exists> u v. u \<in> set ss \<and> v \<in> set ts \<and> vwalk_bet (Graph.digraph_abs G) u p v \<and>
             (\<forall> u' p'. u' \<in> set ss \<and> vwalk_bet (Graph.digraph_abs G) u' p' v 
                        \<longrightarrow> length p \<le> length p')"
  proof(goal_cases)
    case 1
    then obtain t where t: "find (isin (BFS_dist_state.visited fin)) ts = Some t"
       "p = rev (get_path (parent fin) t)"
      by (auto simp add: target_path_def fin_def[symmetric] split: option.splits)
    hence t_props: "t \<in> set ts" "t \<in> t_set (BFS_dist_state.visited fin)"
      using isin_vis by (auto simp add: find_Some_iff)
    obtain u where u: "u \<in> set ss" "vwalk_bet (Graph.digraph_abs G) u p t"
      "\<And> u' p'. \<lbrakk>u' \<in> set ss; vwalk_bet (Graph.digraph_abs G) u' p' t\<rbrakk> \<Longrightarrow> length p \<le> length p'"
    proof(rule BFS_distance_parents.get_path_shortest[OF B ax fin_is t_props(2)], goal_cases)
      case (1 u)
      have len: "length p \<le> length p'"
        if "u' \<in> set ss" "vwalk_bet (Graph.digraph_abs G) u' p' t" for u' p'
        using 1(4)[of u' p'] that srcs t(2) by simp
      show ?case
        by (rule 1(1)[OF _ _ len]) (use 1(2,3) srcs t(2) in simp_all)
    qed
    show ?case 
      using u(1,2) t_props(1) u(3)
      by (intro exI[of _ u] exI[of _ t] conjI allI impI) auto
  qed
qed

subsubsection \<open>Caching\<close>

lemma cache_gen:
  assumes "set_invar M" "set xs \<subseteq> carrier"
  shows "set_invar (foldl (\<lambda> S y. if P y then set_insert y S else S) M xs) \<and>
         to_set (foldl (\<lambda> S y. if P y then set_insert y S else S) M xs) = 
           to_set M \<union> {y \<in> set xs. P y}"
  using assms
proof(induction xs arbitrary: M)
  case (Cons x xs)
  show ?case
  proof(cases "P x")
    case True
    have "set_invar (set_insert x M)" "to_set (set_insert x M) = Set.insert x (to_set M)"
      using set_insert Cons.prems by auto
    then show ?thesis 
      using Cons.IH[of "set_insert x M"] Cons.prems True by auto
  next
    case False
    then show ?thesis 
      using Cons.IH[of M] Cons.prems by auto
  qed
qed simp

lemma cache:
  assumes "set xs \<subseteq> carrier"
  shows "set_invar (cache P xs)" "to_set (cache P xs) = {y \<in> set xs. P y}"
  using cache_gen[OF set_empty(1) assms, of P] set_empty(2) by (auto simp add: cache_def)

subsubsection \<open>The Context and the Exchange Graph\<close>

context
  fixes X
  assumes X: "set_invar X" "to_set X \<subseteq> carrier" "indep1 (to_set X)" "indep2 (to_set X)"
begin

lemma ctx_simps: 
  "ctx_X (exch_ctx X) = X" "ctx_o1 (exch_ctx X) = orcl_prep1 X" "ctx_o2 (exch_ctx X) = orcl_prep2 X"
  by (simp_all add: exch_ctx_def Let_def)

lemma notX: 
  "set (ctx_notX (exch_ctx X)) = carrier - to_set X" "distinct (ctx_notX (exch_ctx X))"
  using X(1) carrier_list by (auto simp add: exch_ctx_def Let_def set_memb)

lemma inX: 
  "set (ctx_inX (exch_ctx X)) = to_set X" "distinct (ctx_inX (exch_ctx X))"
  using X(1,2) carrier_list by (auto simp add: exch_ctx_def Let_def set_memb)

lemma in_S: "in_S (exch_ctx X) y \<longleftrightarrow> y \<in> S (to_set X)"
proof-
  have "ctx_S (exch_ctx X) = cache (ins_orcl1 (orcl_prep1 X)) (ctx_notX (exch_ctx X))" 
    by (simp add: exch_ctx_def Let_def)
  hence S: "set_invar (ctx_S (exch_ctx X))" 
    "to_set (ctx_S (exch_ctx X)) = {y \<in> carrier - to_set X. ins_orcl1 (orcl_prep1 X) y}"
    using cache[of "ctx_notX (exch_ctx X)"] notX(1) by auto
  have "y \<in> carrier - to_set X \<Longrightarrow> ins_orcl1 (orcl_prep1 X) y \<longleftrightarrow> indep1 (Set.insert y (to_set X))"
    using matroid1.ins_orcl[OF X(1,2,3)] by simp
  thus ?thesis 
    using S by (auto simp add: in_S_def set_memb S_def)
qed

lemma in_T: "in_T (exch_ctx X) y \<longleftrightarrow> y \<in> T (to_set X)"
proof-
  have "ctx_T (exch_ctx X) = cache (ins_orcl2 (orcl_prep2 X)) (ctx_notX (exch_ctx X))" 
    by (simp add: exch_ctx_def Let_def)
  hence T: "set_invar (ctx_T (exch_ctx X))" 
    "to_set (ctx_T (exch_ctx X)) = {y \<in> carrier - to_set X. ins_orcl2 (orcl_prep2 X) y}"
    using cache[of "ctx_notX (exch_ctx X)"] notX(1) by auto
  have "y \<in> carrier - to_set X \<Longrightarrow> ins_orcl2 (orcl_prep2 X) y \<longleftrightarrow> indep2 (Set.insert y (to_set X))"
    using matroid2.ins_orcl[OF X(1,2,4)] by simp
  thus ?thesis 
    using T by (auto simp add: in_T_def set_memb T_def)
qed

lemma distinct_out: 
  "distinct (out1 (exch_ctx X) u)" "distinct (out2 (exch_ctx X) u)"
  by (simp_all add: out1_def out2_def notX(2) inX(2))

lemma exch_edges_set:
  "set (exch_edges (exch_ctx X)) = 
     {(u, v). u \<in> to_set X \<and> v \<in> set (out1 (exch_ctx X) u)} \<union>
     {(u, v). u \<in> carrier - to_set X \<and> u \<notin> T (to_set X) \<and> v \<in> set (out2 (exch_ctx X) u)}"
  using inX(1) notX(1) in_T by (auto simp add: exch_edges_def)

lemma exch_edge:
  "(u, v) \<in> set (exch_edges (exch_ctx X)) \<longleftrightarrow> 
     u \<in> carrier \<and> (if u \<in> to_set X then v \<in> set (out1 (exch_ctx X) u) 
                     else u \<notin> T (to_set X) \<and> v \<in> set (out2 (exch_ctx X) u))"
  using X(2) by (auto simp add: exch_edges_set)

lemma exch_edges_carrier: "set (exch_edges (exch_ctx X)) \<subseteq> carrier \<times> carrier"
  by (rule subrelI) 
     (use X(2) in \<open>auto simp add: exch_edge out1_def out2_def notX(1) inX(1) split: if_splits\<close>)

lemma exchange_edges: 
  "set (exch_edges (exch_ctx X)) = A1 (to_set X) \<union> A2 (to_set X)"
proof(rule set_eqI, goal_cases)
  case (1 e)
  obtain u v where e: "e = (u, v)" 
    by (cases e) 
  have out1: "v \<in> set (out1 (exch_ctx X) u) \<longleftrightarrow> 
                v \<in> carrier - to_set X \<and> v \<notin> S (to_set X) \<and> exch_orcl1 (orcl_prep1 X) u v"
    using notX(1) in_S by (auto simp add: out1_def ctx_simps)
  have out2: "v \<in> set (out2 (exch_ctx X) u) \<longleftrightarrow> v \<in> to_set X \<and> exch_orcl2 (orcl_prep2 X) v u"
    using inX(1) by (auto simp add: out2_def ctx_simps)
  show ?case
  proof(cases "u \<in> to_set X")
    case True
    hence "u \<in> carrier" 
      using X(2) by auto
    have "(u, v) \<notin> A2 (to_set X)" 
      using A2_exchange[OF X(4), where y = u and x = v] True by auto
    moreover have "v \<in> carrier - to_set X \<Longrightarrow> v \<notin> S (to_set X) \<longleftrightarrow> \<not> indep1 (Set.insert v (to_set X))"
      by (auto simp add: S_def)
    moreover have "\<lbrakk>v \<in> carrier - to_set X; \<not> indep1 (Set.insert v (to_set X))\<rbrakk> \<Longrightarrow>
       exch_orcl1 (orcl_prep1 X) u v \<longleftrightarrow> indep1 (Set.insert v (to_set X - {u}))"
      by (rule matroid1.exch_orcl[OF X(1,2,3) _ True])
    ultimately show ?thesis
      using e exch_edge out1 True \<open>u \<in> carrier\<close> A1_exchange[OF X(3), where x = u and y = v] 
      by auto
  next
    case False
    have "(u, v) \<notin> A1 (to_set X)" 
      using A1_exchange[OF X(3), where x = u and y = v] False by auto
    moreover have "u \<in> carrier - to_set X \<Longrightarrow> u \<notin> T (to_set X) \<longleftrightarrow> \<not> indep2 (Set.insert u (to_set X))"
      by (auto simp add: T_def)
    moreover have "\<lbrakk>u \<in> carrier - to_set X; \<not> indep2 (Set.insert u (to_set X)); v \<in> to_set X\<rbrakk> \<Longrightarrow>
       exch_orcl2 (orcl_prep2 X) v u \<longleftrightarrow> indep2 (Set.insert u (to_set X - {v}))"
      using matroid2.exch_orcl[OF X(1,2,4)] by blast
    ultimately show ?thesis
      using e exch_edge out2 False A2_exchange[OF X(4), where y = u and x = v] by auto
  qed
qed

lemma exchange_graph: 
  "Graph.digraph_abs (build_graph (exch_edges (exch_ctx X))) = A1 (to_set X) \<union> A2 (to_set X)"
  using exchange_edges build_graph(4) by simp

lemma srcs: "set (srcs (exch_ctx X)) = S (to_set X)" "distinct (srcs (exch_ctx X))"
  using notX in_S by (auto simp add: srcs_def S_def)

lemma tgts: "set (tgts (exch_ctx X)) = T (to_set X)"
  using notX in_T by (auto simp add: tgts_def T_def)

lemma has_nb: 
  assumes "u \<in> set (srcs (exch_ctx X))"
  shows "has_nb (exch_ctx X) u \<longleftrightarrow> 
           (\<exists> v. (u, v) \<in> Graph.digraph_abs (build_graph (exch_edges (exch_ctx X))))"
proof-
  have u: "u \<in> carrier" "u \<notin> to_set X"
    using assms srcs(1) by (auto simp add: S_def)
  have "(\<exists> v. v \<in> set (out2 (exch_ctx X) u)) \<longleftrightarrow> 
        list_ex (\<lambda> x. exch_orcl2 (ctx_o2 (exch_ctx X)) x u) (ctx_inX (exch_ctx X))"
    by (auto simp add: out2_def list_ex_iff)
  thus ?thesis
    using exch_edge u in_T by (auto simp add: has_nb_def build_graph(4))
qed

subsubsection \<open>Correctness of the Path Search\<close>

lemma augmenting_path_Some:
  assumes "augmenting_path X = Some p"
  shows "\<exists> u v. (vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p v \<or> (p = [u] \<and> u = v))
                  \<and> u \<in> S (to_set X) \<and> v \<in> T (to_set X) \<and>
             (\<nexists> p'. (vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p' v \<or> (p' = [u] \<and> u = v))
                         \<and> length p' < length p)"
proof(cases "find (in_T (exch_ctx X)) (srcs (exch_ctx X))")
  case None
  define ss' where "ss' = filter (has_nb (exch_ctx X)) (srcs (exch_ctx X))"
  have ss': "distinct ss'" "set ss' \<subseteq> S (to_set X)"
    using srcs by (auto simp add: ss'_def)
  have ss'_dVs: "set ss' \<subseteq> dVs (Graph.digraph_abs (build_graph (exch_edges (exch_ctx X))))"
  proof
    fix u
    assume "u \<in> set ss'" 
    hence "u \<in> set (srcs (exch_ctx X))" "has_nb (exch_ctx X) u" 
      by (auto simp add: ss'_def)
    then obtain v where "(u, v) \<in> Graph.digraph_abs (build_graph (exch_edges (exch_ctx X)))" 
      using has_nb by blast
    thus "u \<in> dVs (Graph.digraph_abs (build_graph (exch_edges (exch_ctx X))))" 
      by (rule dVsI(1))
  qed
  have ne: "ss' \<noteq> []" 
    and tp: "target_path (build_graph (exch_edges (exch_ctx X))) ss' (tgts (exch_ctx X)) = Some p"
    using assms None by (auto simp add: augmenting_path_def Let_def ss'_def split: if_splits)
  obtain u v where uv: "u \<in> set ss'" "v \<in> set (tgts (exch_ctx X))" 
    "vwalk_bet (Graph.digraph_abs (build_graph (exch_edges (exch_ctx X)))) u p v"
    "\<forall> u' p'. u' \<in> set ss' \<and> 
               vwalk_bet (Graph.digraph_abs (build_graph (exch_edges (exch_ctx X)))) u' p' v 
               \<longrightarrow> length p \<le> length p'"
    using target_path(2)[OF refl ss'(1) ne ss'_dVs exch_edges_carrier tp] by blast
  have u: "u \<in> S (to_set X)" 
    using uv(1) ss'(2) by auto
  have "u \<notin> T (to_set X)"
    using None uv(1) in_T by (auto simp add: find_None_iff ss'_def)
  hence "u \<noteq> v" 
    using uv(2) tgts by auto
  have short: "\<nexists> p'. (vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p' v \<or> (p' = [u] \<and> u = v))
                         \<and> length p' < length p"
  proof(rule notI, goal_cases shorter)
    case shorter
    then obtain p' where p': "vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p' v" 
                             "length p' < length p"
      using \<open>u \<noteq> v\<close> by blast
    have "length p \<le> length p'"
      using uv(1,4) p'(1) unfolding exchange_graph by blast
    then show ?case 
      using p'(2) by simp
  qed
  show ?thesis
    apply(rule exI[of _ u], rule exI[of _ v])
    using uv(2,3) u tgts short unfolding exchange_graph by blast
next
  case (Some s)
  have p: "p = [s]" 
    using assms Some by (simp add: augmenting_path_def Let_def)
  have "s \<in> set (srcs (exch_ctx X))" "in_T (exch_ctx X) s"
    using Some by (auto simp add: find_Some_iff)
  hence s: "s \<in> S (to_set X)" "s \<in> T (to_set X)" 
    using srcs(1) in_T by auto
  show ?thesis
    apply(rule exI[of _ s], rule exI[of _ s])
    using s p by (auto simp add: vwalk_bet_def)
qed

lemma augmenting_path_None:
  "augmenting_path X = None \<longleftrightarrow> 
     (\<nexists> p u v. (vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p v \<or> (p = [u] \<and> u = v)) \<and>
                 u \<in> S (to_set X) \<and> v \<in> T (to_set X))"
proof(rule, goal_cases none no_path)
  case none
  define ss' where "ss' = filter (has_nb (exch_ctx X)) (srcs (exch_ctx X))"
  have ss': "distinct ss'" 
    using srcs by (auto simp add: ss'_def)
  have ss'_dVs: "set ss' \<subseteq> dVs (Graph.digraph_abs (build_graph (exch_edges (exch_ctx X))))"
  proof
    fix u
    assume "u \<in> set ss'" 
    hence "u \<in> set (srcs (exch_ctx X))" "has_nb (exch_ctx X) u" 
      by (auto simp add: ss'_def)
    then obtain v where "(u, v) \<in> Graph.digraph_abs (build_graph (exch_edges (exch_ctx X)))" 
      using has_nb by blast
    thus "u \<in> dVs (Graph.digraph_abs (build_graph (exch_edges (exch_ctx X))))" 
      by (rule dVsI(1))
  qed
  show ?case
  proof(rule notI, goal_cases path)
    case path
    then obtain p u v where puv: 
      "vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p v \<or> (p = [u] \<and> u = v)" 
      "u \<in> S (to_set X)" "v \<in> T (to_set X)" 
      by blast
    have find_None: "find (in_T (exch_ctx X)) (srcs (exch_ctx X)) = None"
      using none by (auto simp add: augmenting_path_def Let_def split: option.splits)
    have "u \<notin> T (to_set X)" 
      using find_None puv(2) srcs(1) in_T by (auto simp add: find_None_iff)
    hence "u \<noteq> v"
      using puv(3) by auto
    hence walk: "vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p v"
      using puv(1) by auto
    obtain w where "(u, w) \<in> Graph.digraph_abs (build_graph (exch_edges (exch_ctx X)))"
      using vwalk_then_edge[OF walk \<open>u \<noteq> v\<close>] unfolding exchange_graph by blast
    hence "u \<in> set ss'"
      using has_nb[of u] puv(2) srcs(1) by (auto simp add: ss'_def)
    hence ne: "ss' \<noteq> []" by auto
    have "target_path (build_graph (exch_edges (exch_ctx X))) ss' (tgts (exch_ctx X)) = None"
      using none find_None ne by (simp add: augmenting_path_def Let_def ss'_def)
    then show ?case 
      using target_path(1)[where ts = "tgts (exch_ctx X)", OF refl ss' ne ss'_dVs exch_edges_carrier, 
                           unfolded exchange_graph tgts]
            \<open>u \<in> set ss'\<close> puv(3) walk 
      by blast
  qed
next
  case no_path
  show ?case
  proof(cases "augmenting_path X")
    case (Some p)
    then show ?thesis 
      using augmenting_path_Some[OF Some] no_path by blast
  qed simp
qed

end

subsubsection \<open>Total Correctness\<close>

sublocale exch_loop: unweighted_intersection_path_loop
  where set_insert = set_insert and set_delete = set_delete and to_set = to_set 
    and set_invar = set_invar and set_empty = set_empty and augmenting_path = augmenting_path 
    and carrier = carrier and indep1 = indep1 and indep2 = indep2
  by unfold_locales 
     (fact set_insert set_delete set_empty augmenting_path_None augmenting_path_Some)+

lemmas total_correctness = exch_loop.impl_total_correctness

end

end

