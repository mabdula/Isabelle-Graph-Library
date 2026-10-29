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
          "('a \<Rightarrow> 'vset option) \<Rightarrow> 'vset \<Rightarrow> 'vset \<Rightarrow> 'par \<Rightarrow>
            'vset \<times> 'vset \<times> 'par"
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
  assumes set_insert: "\<And> S x. \<lbrakk>set_invar S; x \<in> carrier\<rbrakk> \<Longrightarrow> set_invar
    (set_insert x S)"
    "\<And> S x. \<lbrakk>set_invar S; x \<in> carrier\<rbrakk> \<Longrightarrow> to_set (set_insert x S) = Set.insert
      x (to_set S)"
  assumes set_delete: "\<And> S x. \<lbrakk>set_invar S; x \<in> carrier\<rbrakk> \<Longrightarrow> set_invar
    (set_delete x S)"
    "\<And> S x. \<lbrakk>set_invar S; x \<in> carrier\<rbrakk> \<Longrightarrow> to_set (set_delete x S) = (to_set S)
      - {x}"
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
          "('a \<Rightarrow> 'vset option) \<Rightarrow> 'vset \<Rightarrow> 'vset \<Rightarrow> 'par \<Rightarrow>
            'vset \<times> 'vset \<times> 'par"
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
  using bfs[OF assms(2)]
  unfolding assms(1)[symmetric]
  by (elim exE) (rule that)

lemma bfs_of_bfs_dp:
  assumes "BFS_distance_parents (\<lambda> x. None) (\<lambda> x G. G(x := None)) insert isin t_set sel
         (\<lambda> x N G. G(x := Some N)) (\<lambda> G. True) vset_empty
         vset_delete vset_inv union inter diff G exp_tree nfc vset_inv2 some_dist dist_lookup
         dist_invar (\<lambda> G x. G x) set_all_dists_in_set parent_abstract parent_invar par_U get_path
         par_roots parent_init (next_frontier_current_parents G)"
  shows "BFS_3.BFS (\<lambda> x. None) (\<lambda> x G. G(x := None)) insert isin t_set sel
         (\<lambda> x N G. G(x := Some N)) (\<lambda> G. True) vset_empty vset_delete vset_inv
         union inter diff (\<lambda> G x. G x) G exp_tree nfc vset_inv2"
  using assms
  unfolding BFS_distance_parents_def BFS_distance_def
  by blast

lemma vset_of_list_inv: "distinct xs \<Longrightarrow> vset_inv (vset_of_list xs)"
  by (rule bfs_inst[OF refl, of "[]"])
     (auto intro: BFS_3.BFS.vset_inv2[OF bfs_of_bfs_dp] vset_of_list(1))

lemma isin_vset_of_list: "distinct xs \<Longrightarrow> isin (vset_of_list xs) v \<longleftrightarrow> v \<in> set xs"
  using vset_of_list_inv[of xs] vset_of_list(2)[of xs] Graph.vset.set.set_isin
  by simp

lemma bfs_axiomI:
  assumes "G = build_graph es" "distinct ss" "ss \<noteq> []" "set ss \<subseteq> dVs (Graph.digraph_abs G)"
    "set es \<subseteq> carrier \<times> carrier"
  shows "BFS_3.BFS.BFS_axiom isin t_set (\<lambda> G. True) vset_empty vset_inv (\<lambda> G x. G x)
           (vset_of_list ss) G vset_inv2"
  by (rule bfs_inst[OF assms(1,5)]; insert assms build_graph vset_of_list[of ss] Graph.finite_neighbourhoods[of G];
    simp add:
       BFS_3.BFS.BFS_axiom_def[OF bfs_of_bfs_dp])

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
  have visited: "isin (BFS_dist_state.visited (bfs_final G ss)) x \<longleftrightarrow>
          x \<in> t_set (BFS_dist_state.visited (bfs_final G ss))" for x
    using BFS_distance_parents.BFS_par_visited_inv[OF B ax]
    by (simp add: bfs_final_def Graph.vset.set.set_isin)
  moreover note BFS_distance_parents.BFS_par_correct(1)[OF B ax refl]
  ultimately show "target_path G ss ts = None \<Longrightarrow>
           \<nexists> u p v. u \<in> set ss \<and> v \<in> set ts \<and> vwalk_bet (Graph.digraph_abs G) u p v"
    using assms(2) vset_of_list(2)[of ss]
    by (auto simp: target_path_def Let_def bfs_final_def find_None_iff split: option.splits)
  show "target_path G ss ts = Some p \<Longrightarrow>
           \<exists> u v. u \<in> set ss \<and> v \<in> set ts \<and> vwalk_bet (Graph.digraph_abs G) u p v \<and>
             (\<forall> u' p'. u' \<in> set ss \<and> vwalk_bet (Graph.digraph_abs G) u' p' v
                        \<longrightarrow> length p \<le> length p')"
  proof-
    assume "target_path G ss ts = Some p"
    then obtain t where "find (isin (BFS_dist_state.visited (bfs_final G ss))) ts = Some t"
      "p = rev (get_path (parent (bfs_final G ss)) t)"
      by (auto simp: target_path_def Let_def split: option.splits)
    moreover hence "t \<in> set ts" "t \<in> t_set (BFS_dist_state.visited (bfs_final G ss))"
      using visited
      by (auto simp: find_Some_iff)
    ultimately show ?thesis
      using assms(2) vset_of_list(2)[of ss]
      by (elim BFS_distance_parents.get_path_shortest[OF B ax refl, folded bfs_final_def])
         (simp, blast)
  qed
qed

subsubsection \<open>Caching\<close>

lemma cache_gen:
  assumes "set_invar M" "set xs \<subseteq> carrier"
  shows "set_invar (foldl (\<lambda> S y. if P y then set_insert y S else S) M xs) \<and>
         to_set (foldl (\<lambda> S y. if P y then set_insert y S else S) M xs) =
           to_set M \<union> {y \<in> set xs. P y}"
  using assms
  by (induction xs arbitrary: M) (auto simp: set_insert)

lemma cache:
  assumes "set xs \<subseteq> carrier"
  shows "set_invar (cache P xs)" "to_set (cache P xs) = {y \<in> set xs. P y}"
  using cache_gen[of set_empty xs P] set_empty assms
  by (auto simp add: cache_def)

subsubsection \<open>The Context and the Exchange Graph\<close>

context
  fixes X
  assumes X: "set_invar X" "to_set X \<subseteq> carrier" "indep1 (to_set X)" "indep2 (to_set X)"
begin

lemma ctx_simps:
  "ctx_X (exch_ctx X) = X" "ctx_o1 (exch_ctx X) = orcl_prep1 X" "ctx_o2 (exch_ctx X) = orcl_prep2 X"
  by (simp_all add: exch_ctx_def Let_def)

lemma ctx_ST:
  "ctx_S (exch_ctx X) = cache (ins_orcl1 (orcl_prep1 X)) (ctx_notX (exch_ctx X))"
  "ctx_T (exch_ctx X) = cache (ins_orcl2 (orcl_prep2 X)) (ctx_notX (exch_ctx X))"
  by (simp_all add: exch_ctx_def Let_def)

lemma notX:
  "set (ctx_notX (exch_ctx X)) = carrier - to_set X" "distinct (ctx_notX (exch_ctx X))"
  using X(1) carrier_list
  by (auto simp add: exch_ctx_def Let_def set_memb)

lemma inX:
  "set (ctx_inX (exch_ctx X)) = to_set X" "distinct (ctx_inX (exch_ctx X))"
  using X(1,2) carrier_list
  by (auto simp add: exch_ctx_def Let_def set_memb)

lemma in_S: "in_S (exch_ctx X) y \<longleftrightarrow> y \<in> S (to_set X)"
  using cache[of "ctx_notX (exch_ctx X)" "ins_orcl1 (orcl_prep1 X)"] notX(1) X
    matroid1.ins_orcl[of X]
  by (auto simp add: in_S_def set_memb S_def ctx_ST)

lemma in_T: "in_T (exch_ctx X) y \<longleftrightarrow> y \<in> T (to_set X)"
  using cache[of "ctx_notX (exch_ctx X)" "ins_orcl2 (orcl_prep2 X)"] notX(1) X
    matroid2.ins_orcl[of X]
  by (auto simp add: in_T_def set_memb T_def ctx_ST)

lemma distinct_out:
  "distinct (out1 (exch_ctx X) u)" "distinct (out2 (exch_ctx X) u)"
  by (simp_all add: out1_def out2_def notX(2) inX(2))

lemma out1_iff:
  "v \<in> set (out1 (exch_ctx X) u) \<longleftrightarrow>
     v \<in> carrier - to_set X \<and> v \<notin> S (to_set X) \<and> exch_orcl1 (orcl_prep1 X) u v"
  using notX(1) in_S
  by (auto simp add: out1_def ctx_simps)

lemma out2_iff:
  "v \<in> set (out2 (exch_ctx X) u) \<longleftrightarrow> v \<in> to_set X \<and> exch_orcl2 (orcl_prep2 X) v u"
  using inX(1)
  by (auto simp add: out2_def ctx_simps)

lemma exch_edges_set:
  "set (exch_edges (exch_ctx X)) =
     {(u, v). u \<in> to_set X \<and> v \<in> set (out1 (exch_ctx X) u)} \<union>
     {(u, v). u \<in> carrier - to_set X \<and> u \<notin> T (to_set X) \<and> v \<in> set (out2 (exch_ctx X) u)}"
  using inX(1) notX(1) in_T
  by (auto simp add: exch_edges_def)

lemma exch_edge:
  "(u, v) \<in> set (exch_edges (exch_ctx X)) \<longleftrightarrow>
     u \<in> carrier \<and> (if u \<in> to_set X then v \<in> set (out1 (exch_ctx X) u)
                     else u \<notin> T (to_set X) \<and> v \<in> set (out2 (exch_ctx X) u))"
  using X(2)
  by (auto simp add: exch_edges_set)

lemma exch_edges_carrier: "set (exch_edges (exch_ctx X)) \<subseteq> carrier \<times> carrier"
  by (rule subrelI; insert X(2); auto simp add: exch_edge out1_def out2_def notX(1) inX(1) split: if_splits)

lemma exchange_edges:
  "set (exch_edges (exch_ctx X)) = A1 (to_set X) \<union> A2 (to_set X)"
proof-
  have "(u, v) \<in> set (exch_edges (exch_ctx X)) \<longleftrightarrow> (u, v) \<in> A1 (to_set X) \<union> A2
    (to_set X)"
    for u v
  proof(cases "u \<in> to_set X")
    case True
    moreover have "(u, v) \<notin> A2 (to_set X)"
      using X(4) A2_exchange[of "to_set X" u v] True
      by auto
    moreover have "\<lbrakk>v \<in> carrier - to_set X; \<not> indep1 (Set.insert v (to_set X))\<rbrakk>
      \<Longrightarrow>
       exch_orcl1 (orcl_prep1 X) u v \<longleftrightarrow> indep1 (Set.insert v (to_set X - {u}))"
      by (rule matroid1.exch_orcl[OF X(1,2,3) _ True])
    ultimately show ?thesis
      using X(2,3) exch_edge out1_iff A1_exchange[of "to_set X" u v]
      by (auto simp add: S_def)
  next
    case False
    moreover have "(u, v) \<notin> A1 (to_set X)"
      using X(3) A1_exchange[of "to_set X" u v] False
      by auto
    moreover have "\<lbrakk>u \<in> carrier - to_set X; \<not> indep2 (Set.insert u (to_set X)); v \<in> to_set
      X\<rbrakk> \<Longrightarrow>
       exch_orcl2 (orcl_prep2 X) v u \<longleftrightarrow> indep2 (Set.insert u (to_set X - {v}))"
      using matroid2.exch_orcl[OF X(1,2,4)]
      by blast
    ultimately show ?thesis
      using X(4) exch_edge out2_iff A2_exchange[of "to_set X" u v]
      by (auto simp add: T_def)
  qed
  thus ?thesis
    by (simp add: set_eq_iff)
qed

lemma exchange_graph:
  "Graph.digraph_abs (build_graph (exch_edges (exch_ctx X))) = A1 (to_set X) \<union> A2 (to_set X)"
  using exchange_edges build_graph(4)
  by simp

lemma srcs: "set (srcs (exch_ctx X)) = S (to_set X)" "distinct (srcs (exch_ctx X))"
  using notX in_S
  by (auto simp add: srcs_def S_def)

lemma tgts: "set (tgts (exch_ctx X)) = T (to_set X)"
  using notX in_T
  by (auto simp add: tgts_def T_def)

lemma has_nb:
  assumes "u \<in> set (srcs (exch_ctx X))"
  shows "has_nb (exch_ctx X) u \<longleftrightarrow>
           (\<exists> v. (u, v) \<in> Graph.digraph_abs (build_graph (exch_edges (exch_ctx X))))"
  using assms srcs(1) exch_edge in_T
  by (auto simp add: has_nb_def build_graph(4) out2_def list_ex_iff S_def)

lemma nb_srcs_dVs:
  "set (filter (has_nb (exch_ctx X)) (srcs (exch_ctx X)))
     \<subseteq> dVs (Graph.digraph_abs (build_graph (exch_edges (exch_ctx X))))"
  using has_nb
  by auto

subsubsection \<open>Correctness of the Path Search\<close>

lemma augmenting_path_Some:
  assumes "augmenting_path X = Some p"
  shows "\<exists> u v. (vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p v \<or> (p = [u] \<and> u = v))
                  \<and> u \<in> S (to_set X) \<and> v \<in> T (to_set X) \<and>
             (\<nexists> p'. (vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p' v \<or> (p' = [u] \<and> u = v))
                         \<and> length p' < length p)"
proof(cases "find (in_T (exch_ctx X)) (srcs (exch_ctx X))")
  case None
  hence "filter (has_nb (exch_ctx X)) (srcs (exch_ctx X)) \<noteq> []"
    "target_path (build_graph (exch_edges (exch_ctx X))) (filter (has_nb (exch_ctx X)) (srcs (exch_ctx X)))
       (tgts (exch_ctx X)) = Some p"
    using assms
    by (auto simp add: augmenting_path_def Let_def split: if_splits)
  then obtain u v where "u \<in> set (filter (has_nb (exch_ctx X)) (srcs (exch_ctx X)))"
    "v \<in> T (to_set X)" "vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p v"
    "\<forall> u' p'. u' \<in> set (filter (has_nb (exch_ctx X)) (srcs (exch_ctx X))) \<and>
       vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u' p' v \<longrightarrow> length p \<le> length p'"
    using target_path(2)[where ts = "tgts (exch_ctx X)",
        OF refl distinct_filter[OF srcs(2)] _ nb_srcs_dVs exch_edges_carrier]
    unfolding exchange_graph tgts
    by blast
  moreover hence "u \<in> S (to_set X)" "u \<notin> T (to_set X)"
    using None srcs(1) in_T
    by (auto simp add: find_None_iff)
  ultimately show ?thesis
    by fastforce
next
  case (Some s)
  hence "p = [s]"
    using assms
    by (simp add: augmenting_path_def Let_def)
  moreover have "s \<in> S (to_set X)" "s \<in> T (to_set X)"
    using Some srcs(1) in_T
    by (auto simp add: find_Some_iff)
  ultimately show ?thesis
    by (auto simp add: vwalk_bet_def)
qed

lemma augmenting_path_None:
  "augmenting_path X = None \<longleftrightarrow>
     (\<nexists> p u v. (vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p v \<or> (p = [u] \<and> u = v)) \<and>
                 u \<in> S (to_set X) \<and> v \<in> T (to_set X))"
proof
  assume "augmenting_path X = None"
  hence "find (in_T (exch_ctx X)) (srcs (exch_ctx X)) = None"
    "filter (has_nb (exch_ctx X)) (srcs (exch_ctx X)) \<noteq> [] \<Longrightarrow>
       target_path (build_graph (exch_edges (exch_ctx X)))
         (filter (has_nb (exch_ctx X)) (srcs (exch_ctx X))) (tgts (exch_ctx X)) = None"
    by (auto simp add: augmenting_path_def Let_def split: option.splits if_splits)
  hence nT: "u \<notin> T (to_set X)"
    and nw: "filter (has_nb (exch_ctx X)) (srcs (exch_ctx X)) \<noteq> [] \<Longrightarrow>
       \<nexists> u' p' v'. u' \<in> set (filter (has_nb (exch_ctx X)) (srcs (exch_ctx X))) \<and> v' \<in> T (to_set
         X) \<and>
         vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u' p' v'"
    if "u \<in> S (to_set X)" for u
    using that srcs in_T target_path(1)[where ts = "tgts (exch_ctx X)",
        OF refl distinct_filter[OF srcs(2)] _ nb_srcs_dVs exch_edges_carrier]
    unfolding exchange_graph tgts
    by (auto simp add: find_None_iff)
  have fl: "u \<in> set (filter (has_nb (exch_ctx X)) (srcs (exch_ctx X)))"
    if "vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p v" "u \<in> S (to_set X)" "u \<noteq> v" for u p v
    using that vwalk_then_edge[of "A1 (to_set X) \<union> A2 (to_set X)" u p v] has_nb[of u] srcs(1)
    unfolding exchange_graph
    by auto
  show "\<nexists> p u v. (vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p v \<or> (p = [u] \<and> u = v)) \<and>
                 u \<in> S (to_set X) \<and> v \<in> T (to_set X)"
  proof(intro notI, elim exE conjE)
    fix p u v
    assume "vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p v \<or> (p = [u] \<and> u = v)" "u \<in> S (to_set X)"
      "v \<in> T (to_set X)"
    moreover hence "vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p v" "u \<noteq> v"
      using nT
      by auto
    ultimately show False
      using fl[of u p v] nw[of u]
      by (auto simp: filter_empty_conv)
  qed
next
  assume "\<nexists> p u v. (vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p v \<or> (p = [u] \<and> u = v)) \<and>
                 u \<in> S (to_set X) \<and> v \<in> T (to_set X)"
  thus "augmenting_path X = None"
    using augmenting_path_Some
    by (cases "augmenting_path X") auto
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
