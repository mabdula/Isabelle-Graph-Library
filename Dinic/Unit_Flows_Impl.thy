theory Unit_Flows_Impl
  imports
    Residual_Buckets
    Flow_Theory.Unit_Flows
    Graph_Algorithms_Dev.DFS_Example
    Graph_Algorithms_Dev.RBT_Map_Extension
    "HOL-Library.Product_Lexorder"
begin

hide_const (open) RBT_Set.insert

section \<open>Executable Unit Flows\<close>

text \<open>We maximise unit flows by depth-first search. The residual edges of positive capacity are kept
in buckets indexed by pairs of vertices (@{locale residual_buckets_spec}), and their projection to
pairs of vertices is kept as an adjacency map, which is searched by @{const dfs_impl}. Augmenting
along a walk of the projection takes one residual edge from the bucket of every arc of the walk
and puts its reverse into the bucket of the reversed arc. Parallel and antiparallel edges are
allowed.\<close>

subsection \<open>Depth-First Search for Walks\<close>

text \<open>Depth-first search from \<open>s\<close> to \<open>t\<close> decides reachability and returns a distinct walk.\<close>

lemma dfs_walk:
  fixes Gr :: "('v::linorder \<times> 'v rbt) rbt"
  assumes inv: "dfs.Graph.graph_inv Gr" "dfs.Graph.finite_graph Gr" "dfs.Graph.finite_vsets Gr"
    and st: "s \<noteq> t"
  defines "r \<equiv> dfs_impl Gr t (dfs_initial_state s)"
  shows "(neighbourhood Gr s \<noteq> vset_empty \<and> return r = Reachable) \<longleftrightarrow>
      (\<exists>p. vwalk_bet (dfs.Graph.digraph_abs Gr) s p t)"
    and "\<lbrakk>neighbourhood Gr s \<noteq> vset_empty; return r = Reachable\<rbrakk> \<Longrightarrow>
      distinct (rev (stack r)) \<and> vwalk_bet (dfs.Graph.digraph_abs Gr) s (rev (stack r)) t"
proof -
  have walk_edge: "\<exists>u. (s, u) \<in> dfs.Graph.digraph_abs Gr" if "vwalk_bet (dfs.Graph.digraph_abs Gr) s p t" for p
    using that st by (cases p rule: edges_of_vwalk.cases) (auto simp: vwalk_bet_def)
  show goal2: "distinct (rev (stack r)) \<and> vwalk_bet (dfs.Graph.digraph_abs Gr) s (rev (stack r)) t"
    if nb: "neighbourhood Gr s \<noteq> vset_empty" and reach: "return r = Reachable"
  proof -
    have "t_set (neighbourhood Gr s) \<noteq> {}"
      using nb by (auto simp: RBT_Set.empty_def)
    then have "s \<in> dVs (dfs.Graph.digraph_abs Gr)"
      using inv(1) by blast
    then have DT: "DFS_thms map_empty RBT_Map.delete vset_insert isin t_set sel update adj_inv vset_empty
        vset_delete vset_inv vset_union vset_inter vset_diff lookup Gr s"
      using inv by (intro DFS_thms.intro dfs.DFS_axioms DFS_thms_axioms.intro)
        (simp add: DFS.DFS_axioms_def[OF dfs.DFS_axioms])
    show ?thesis
      using reach DFS_thms.DFS_correct_2[OF DT] unfolding r_def dfs_impl_def dfs_initial_state_def
      by (simp add: DFS_thms.DFS_impl_to_DFS[OF DT])
  qed
  show "(neighbourhood Gr s \<noteq> vset_empty \<and> return r = Reachable) \<longleftrightarrow>
      (\<exists>p. vwalk_bet (dfs.Graph.digraph_abs Gr) s p t)"
  proof
    assume "neighbourhood Gr s \<noteq> vset_empty \<and> return r = Reachable"
    then show "\<exists>p. vwalk_bet (dfs.Graph.digraph_abs Gr) s p t"
      using goal2 by blast
  next
    assume "\<exists>p. vwalk_bet (dfs.Graph.digraph_abs Gr) s p t"
    then obtain p where p: "vwalk_bet (dfs.Graph.digraph_abs Gr) s p t"
      by blast
    then obtain u where "(s, u) \<in> dfs.Graph.digraph_abs Gr"
      using walk_edge by blast
    then have "u \<in> t_set (neighbourhood Gr s)"
      using inv(1) by (simp add: Pair_Graph.neighbourhood_def)
    then have nb: "neighbourhood Gr s \<noteq> vset_empty"
      by (auto simp: RBT_Set.empty_def)
    have "s \<in> dVs (dfs.Graph.digraph_abs Gr)"
      using p by (auto dest: vwalk_bet_endpoints)
    then have DT: "DFS_thms map_empty RBT_Map.delete vset_insert isin t_set sel update adj_inv vset_empty
        vset_delete vset_inv vset_union vset_inter vset_diff lookup Gr s"
      using inv by (intro DFS_thms.intro dfs.DFS_axioms DFS_thms_axioms.intro)
        (simp add: DFS.DFS_axioms_def[OF dfs.DFS_axioms])
    have "return r = Reachable"
    proof (rule ccontr)
      assume "return r \<noteq> Reachable"
      then have "return r = NotReachable"
        by (cases "return r") auto
      then show False
        using DFS_thms.DFS_correct_1_strong[OF DT] p unfolding r_def dfs_impl_def dfs_initial_state_def
        by (simp add: DFS_thms.DFS_impl_to_DFS[OF DT])
    qed
    then show "neighbourhood Gr s \<noteq> vset_empty \<and> return r = Reachable"
      using nb by simp
  qed
qed

subsection \<open>The State and the Operations\<close>

record ('g, 'b) ustate = u_graph :: 'g  u_bkt :: 'b

locale unit_flow_impl_spec = residual_buckets_spec where fst = fst
  for fst :: "'e \<Rightarrow> 'v::linorder"
begin

text \<open>The state for a list of residual edges.\<close>

definition "u_init rs =
  \<lparr>u_graph = from_list (map to_vertex_pair rs), u_bkt = realising_edges_general rs\<rparr>"

text \<open>Adding a residual edge.\<close>

definition "u_add r st = (let d = to_vertex_pair r in
  \<lparr>u_graph = add_edge (u_graph st) (prod.fst d) (prod.snd d),
   u_bkt = realising_edges_update d (r # bucket (u_bkt st) d) (u_bkt st)\<rparr>)"

text \<open>Flipping one arc of the projection: one residual edge realising it is replaced by its
reverse.\<close>

definition "u_flip_arc st d = (case bucket (u_bkt st) d of
    [] \<Rightarrow> st
  | r # rs \<Rightarrow>
      let bkt = realising_edges_update d rs (u_bkt st);
          G = (if rs = [] then delete_edge (u_graph st) (prod.fst d) (prod.snd d) else u_graph st)
      in \<lparr>u_graph = add_edge G (prod.snd d) (prod.fst d),
          u_bkt = realising_edges_update (prod.swap d) (erev r # bucket bkt (prod.swap d)) bkt\<rparr>)"

definition "u_flip es st = foldl u_flip_arc st es"

text \<open>Searching a walk from \<open>s\<close> to \<open>t\<close> in the projection.\<close>

definition "u_search st s t =
  (if neighbourhood (u_graph st) s = vset_empty then None
   else let r = dfs_impl (u_graph st) t (dfs_initial_state s) in
     if return r = Reachable then Some (rev (stack r)) else None)"

lemmas [code] = u_init_def u_add_def u_flip_arc_def u_flip_def u_search_def

text \<open>The state represents the set \<open>RS\<close> of residual edges.\<close>

definition "u_invar RS st \<longleftrightarrow>
  dfs.Graph.graph_inv (u_graph st) \<and> dfs.Graph.finite_graph (u_graph st) \<and>
  dfs.Graph.finite_vsets (u_graph st) \<and> realising_edges_invar (u_bkt st) \<and>
  dfs.Graph.digraph_abs (u_graph st) = to_vertex_pair ` RS \<and>
  (\<forall>d. set (bucket (u_bkt st) d) = {r. r \<in> RS \<and> to_vertex_pair r = d} \<and>
       distinct (bucket (u_bkt st) d))"

subsection \<open>Correctness of the Operations\<close>

lemma to_vertex_pair_erev: "to_vertex_pair (erev r) = prod.swap (to_vertex_pair r)"
  by (cases r) (simp_all add: make_pair_def)

lemma u_invarD:
  assumes "u_invar RS st"
  shows "dfs.Graph.graph_inv (u_graph st)" "dfs.Graph.finite_graph (u_graph st)"
    "dfs.Graph.finite_vsets (u_graph st)" "realising_edges_invar (u_bkt st)"
    "dfs.Graph.digraph_abs (u_graph st) = to_vertex_pair ` RS"
    "set (bucket (u_bkt st) d) = {r. r \<in> RS \<and> to_vertex_pair r = d}"
    "distinct (bucket (u_bkt st) d)"
  using assms unfolding u_invar_def by blast+

lemma u_invar_pair_iff:
  assumes "u_invar RS st"
  shows "d \<in> to_vertex_pair ` RS \<longleftrightarrow> bucket (u_bkt st) d \<noteq> []"
proof -
  have bk: "set (bucket (u_bkt st) d) = {r. r \<in> RS \<and> to_vertex_pair r = d}"
    by (rule u_invarD(6)[OF assms])
  show ?thesis
  proof
    assume "d \<in> to_vertex_pair ` RS"
    then obtain r where "r \<in> RS" "to_vertex_pair r = d"
      by blast
    then have "r \<in> set (bucket (u_bkt st) d)"
      using bk by simp
    then show "bucket (u_bkt st) d \<noteq> []"
      by auto
  next
    assume "bucket (u_bkt st) d \<noteq> []"
    then obtain r where "r \<in> set (bucket (u_bkt st) d)"
      by (cases "bucket (u_bkt st) d") auto
    then have "r \<in> RS" "to_vertex_pair r = d"
      using bk by simp_all
    then show "d \<in> to_vertex_pair ` RS"
      by blast
  qed
qed

lemma graph_ops_inv:
  assumes "dfs.Graph.graph_inv G" "dfs.Graph.finite_graph G" "dfs.Graph.finite_vsets G"
  shows "dfs.Graph.graph_inv (add_edge G u v) \<and> dfs.Graph.finite_graph (add_edge G u v) \<and>
      dfs.Graph.finite_vsets (add_edge G u v)"
    and "dfs.Graph.graph_inv (delete_edge G u v) \<and> dfs.Graph.finite_graph (delete_edge G u v) \<and>
      dfs.Graph.finite_vsets (delete_edge G u v)"
  using assms
  by (auto intro: dfs.Graph.finite_graph_add_edge dfs.Graph.finite_vsets_add_edge
      dfs.Graph.finite_graph_delete_edge dfs.Graph.finite_vsets_delete_edge)

lemma u_init_correct:
  assumes "distinct rs"
  shows "u_invar (set rs) (u_init rs)"
proof -
  note fl = dfs.Graph.from_list_correct[where es = "map to_vertex_pair rs"]
  have bk: "set (bucket (realising_edges_general rs) d) = {r. r \<in> set rs \<and> to_vertex_pair r = d}"
    "distinct (bucket (realising_edges_general rs) d)" for d
  proof -
    obtain u v where d: "d = (u, v)"
      by (cases d)
    show "set (bucket (realising_edges_general rs) d) = {r. r \<in> set rs \<and> to_vertex_pair r = d}"
      using realising_edges_general_result_None_and_Some[OF refl, of rs u v]
      unfolding bucket_def d by blast
    show "distinct (bucket (realising_edges_general rs) d)"
      using realising_edges_general_result_distinct[OF assms refl, of u v]
      unfolding bucket_def d .
  qed
  show ?thesis
    unfolding u_invar_def u_init_def
    using fl(1-4) realising_edges_invar_pres[of rs] bk by simp
qed

lemma u_add_correct:
  assumes inv: "u_invar RS st" and r: "r \<notin> RS"
  shows "u_invar (insert r RS) (u_add r st)"
proof -
  obtain u v where uv: "to_vertex_pair r = (u, v)"
    by (cases "to_vertex_pair r")
  note g = u_invarD[OF inv]
  have res: "u_add r st = \<lparr>u_graph = add_edge (u_graph st) u v,
      u_bkt = realising_edges_update (u, v) (r # bucket (u_bkt st) (u, v)) (u_bkt st)\<rparr>"
    by (simp add: u_add_def uv)
  have bk: "set (bucket (realising_edges_update (u, v) (r # bucket (u_bkt st) (u, v)) (u_bkt st)) d) =
        {x. x \<in> insert r RS \<and> to_vertex_pair x = d} \<and>
      distinct (bucket (realising_edges_update (u, v) (r # bucket (u_bkt st) (u, v)) (u_bkt st)) d)"
    for d
    using g(6)[of d] g(7)[of d] g(6)[of "(u, v)"] g(7)[of "(u, v)"] r uv
    by (auto simp: bucket_update[OF g(4)])
  have abs: "dfs.Graph.digraph_abs (add_edge (u_graph st) u v) = to_vertex_pair ` insert r RS"
    using g(1,5) uv by simp
  show ?thesis
    unfolding u_invar_def res
    using graph_ops_inv(1)[OF g(1-3), of u v] Map_realising.invar_update[OF g(4)] abs bk by simp
qed

lemma u_flip_arc_correct:
  assumes inv: "u_invar RS st" and anti: "\<forall>r \<in> RS. erev r \<notin> RS"
    and d: "d \<in> to_vertex_pair ` RS" and loop: "prod.fst d \<noteq> prod.snd d"
  obtains r where "r \<in> RS" "to_vertex_pair r = d" "u_invar (RS - {r} \<union> {erev r}) (u_flip_arc st d)"
proof -
  obtain u v where uv: "d = (u, v)"
    by (cases d)
  note g = u_invarD[OF inv]
  obtain r rs where rrs: "bucket (u_bkt st) d = r # rs"
    using u_invar_pair_iff[OF inv, of d] d by (cases "bucket (u_bkt st) d") auto
  have r: "r \<in> RS" "to_vertex_pair r = d"
    using g(6)[of d] rrs by auto
  have er: "erev r \<notin> RS"
    using anti r(1) by blast
  have tvp_er: "to_vertex_pair (erev r) = (v, u)"
    using r(2) uv by (simp add: to_vertex_pair_erev)
  have vu: "(v, u) \<noteq> (u, v)"
    using loop uv by auto
  have rs: "set rs = {x. x \<in> RS \<and> to_vertex_pair x = d} - {r}" "distinct rs"
    using g(6)[of d] g(7)[of d] rrs by auto
  define bkt where "bkt = realising_edges_update (u, v) rs (u_bkt st)"
  define G where "G = (if rs = [] then delete_edge (u_graph st) u v else u_graph st)"
  define bkt' where "bkt' = realising_edges_update (v, u) (erev r # bucket bkt (v, u)) bkt"
  have res: "u_flip_arc st d = \<lparr>u_graph = add_edge G v u, u_bkt = bkt'\<rparr>"
    using rrs unfolding uv by (simp add: u_flip_arc_def bkt_def G_def bkt'_def Let_def)
  have bkt_inv: "realising_edges_invar bkt"
    using g(4) by (simp add: bkt_def Map_realising.invar_update)
  have bkt'_inv: "realising_edges_invar bkt'"
    using bkt_inv by (simp add: bkt'_def Map_realising.invar_update)
  have new: "bucket bkt' d' = (if d' = (v, u) then erev r # bucket (u_bkt st) (v, u)
      else if d' = (u, v) then rs else bucket (u_bkt st) d')" for d'
  proof -
    have old: "bucket bkt x = (if x = (u, v) then rs else bucket (u_bkt st) x)" for x
      unfolding bkt_def by (rule bucket_update[OF g(4)])
    show ?thesis
      unfolding bkt'_def bucket_update[OF bkt_inv] old using vu by simp
  qed
  have r_uv: "to_vertex_pair r = (u, v)"
    using r(2) uv by simp
  have oldx: "x \<in> set (bucket (u_bkt st) d'') \<longleftrightarrow> x \<in> RS \<and> to_vertex_pair x = d''" for x d''
    using g(6)[of d''] by blast
  have rsx: "x \<in> set rs \<longleftrightarrow> x \<in> RS \<and> to_vertex_pair x = (u, v) \<and> x \<noteq> r" for x
    using rs(1) uv by blast
  have set_new: "set (bucket bkt' d') = {x. x \<in> RS - {r} \<union> {erev r} \<and> to_vertex_pair x = d'}"
    for d'
  proof (rule set_eqI)
    fix x
    have nr: "x = r \<Longrightarrow> to_vertex_pair x = (u, v)" and ner: "x = erev r \<Longrightarrow> to_vertex_pair x = (v, u)"
      using r_uv tvp_er by simp_all
    consider (vu') "d' = (v, u)" | (uv') "d' = (u, v)" | (other) "d' \<noteq> (v, u)" "d' \<noteq> (u, v)"
      by blast
    then show "x \<in> set (bucket bkt' d') \<longleftrightarrow> x \<in> {x. x \<in> RS - {r} \<union> {erev r} \<and> to_vertex_pair x = d'}"
    proof cases
      case vu'
      then show ?thesis
        unfolding new[of d'] using oldx[of x "(v, u)"] nr ner vu by auto
    next
      case uv'
      then show ?thesis
        unfolding new[of d'] using rsx[of x] nr ner vu by auto
    next
      case other
      then show ?thesis
        unfolding new[of d'] using oldx[of x d'] nr ner by auto
    qed
  qed
  have er_old: "erev r \<notin> set (bucket (u_bkt st) (v, u))"
    using oldx[of "erev r" "(v, u)"] er by blast
  have dist_new: "distinct (bucket bkt' d')" for d'
    unfolding new[of d'] using g(7)[of d'] g(7)[of "(v, u)"] rs(2) er_old by simp
  have G_inv: "dfs.Graph.graph_inv G" "dfs.Graph.finite_graph G" "dfs.Graph.finite_vsets G"
    using graph_ops_inv(2)[OF g(1-3), of u v] g(1-3) by (simp_all add: G_def)
  have abs_G: "dfs.Graph.digraph_abs G =
      (if rs = [] then dfs.Graph.digraph_abs (u_graph st) - {(u, v)} else dfs.Graph.digraph_abs (u_graph st))"
    using g(1) by (simp add: G_def)
  have uv_old: "bucket (u_bkt st) (u, v) \<noteq> []"
    using rrs uv by simp
  have abs_new: "dfs.Graph.digraph_abs (add_edge G v u) = to_vertex_pair ` (RS - {r} \<union> {erev r})"
  proof (rule set_eqI)
    fix d'
    have img: "d' \<in> to_vertex_pair ` (RS - {r} \<union> {erev r}) \<longleftrightarrow> bucket bkt' d' \<noteq> []"
    proof
      assume "d' \<in> to_vertex_pair ` (RS - {r} \<union> {erev r})"
      then obtain x where "x \<in> RS - {r} \<union> {erev r}" "to_vertex_pair x = d'"
        by blast
      then have "x \<in> set (bucket bkt' d')"
        using set_new[of d'] by blast
      then show "bucket bkt' d' \<noteq> []"
        by auto
    next
      assume "bucket bkt' d' \<noteq> []"
      then obtain x where "x \<in> set (bucket bkt' d')"
        by (cases "bucket bkt' d'") auto
      then have "x \<in> RS - {r} \<union> {erev r}" "to_vertex_pair x = d'"
        using set_new[of d'] by blast+
      then show "d' \<in> to_vertex_pair ` (RS - {r} \<union> {erev r})"
        by blast
    qed
    have old: "d' \<in> dfs.Graph.digraph_abs (u_graph st) \<longleftrightarrow> bucket (u_bkt st) d' \<noteq> []"
      using u_invar_pair_iff[OF inv, of d'] g(5) by simp
    consider (vu') "d' = (v, u)" | (uv') "d' = (u, v)" | (other) "d' \<noteq> (v, u)" "d' \<noteq> (u, v)"
      by blast
    then show "d' \<in> dfs.Graph.digraph_abs (add_edge G v u) \<longleftrightarrow> d' \<in> to_vertex_pair ` (RS - {r} \<union> {erev r})"
    proof cases
      case vu'
      then show ?thesis
        unfolding img dfs.Graph.digraph_abs_insert[OF G_inv(1)] new[of d'] by simp
    next
      case uv'
      then show ?thesis
        unfolding img dfs.Graph.digraph_abs_insert[OF G_inv(1)] new[of d'] abs_G
        using old uv_old vu by simp
    next
      case other
      then show ?thesis
        unfolding img dfs.Graph.digraph_abs_insert[OF G_inv(1)] new[of d'] abs_G
        using old by simp
    qed
  qed
  have "u_invar (RS - {r} \<union> {erev r}) (u_flip_arc st d)"
    unfolding u_invar_def res
    using graph_ops_inv(1)[OF G_inv, of v u] bkt'_inv abs_new set_new dist_new by simp
  then show ?thesis
    using that r by blast
qed

text \<open>Flipping a list of arcs that are pairwise distinct, contain no loops and no reversed arcs.\<close>

lemma u_flip_correct_ex:
  assumes "u_invar RS st" "\<forall>r \<in> RS. erev r \<notin> RS" "set es \<subseteq> to_vertex_pair ` RS" "distinct es"
    "\<forall>(u, v) \<in> set es. u \<noteq> v \<and> (v, u) \<notin> set es"
  shows "\<exists>rs. map to_vertex_pair rs = es \<and> set rs \<subseteq> RS \<and>
    u_invar (RS - set rs \<union> erev ` set rs) (u_flip es st) \<and>
    (\<forall>r \<in> RS - set rs \<union> erev ` set rs. erev r \<notin> RS - set rs \<union> erev ` set rs)"
  using assms
proof (induction es arbitrary: RS st)
  case Nil
  then show ?case
    by (simp add: u_flip_def)
next
  case (Cons d es)
  obtain u v where uv: "d = (u, v)"
    by (cases d)
  have loop: "prod.fst d \<noteq> prod.snd d" and nswap: "prod.swap d \<notin> set es"
    using Cons.prems(5) uv by auto
  have dR: "d \<in> to_vertex_pair ` RS"
    using Cons.prems(3) by simp
  obtain r where r: "r \<in> RS" "to_vertex_pair r = d"
    and inv1: "u_invar (RS - {r} \<union> {erev r}) (u_flip_arc st d)"
    using u_flip_arc_correct[OF Cons.prems(1,2) dR loop] by blast
  let ?R1 = "RS - {r} \<union> {erev r}"
  have tvp_er: "to_vertex_pair (erev r) = prod.swap d"
    using r(2) by (simp add: to_vertex_pair_erev)
  have er: "erev r \<notin> RS"
    using Cons.prems(2) r(1) by blast
  have anti1: "\<forall>x \<in> ?R1. erev x \<notin> ?R1"
  proof
    fix x
    assume x: "x \<in> ?R1"
    show "erev x \<notin> ?R1"
    proof (cases "x = erev r")
      case True
      then have "erev x = r"
        by (simp add: erve_erve_id)
      then show ?thesis
        using er r(1) by auto
    next
      case False
      then have xr: "x \<in> RS" "x \<noteq> r"
        using x by auto
      then have "erev x \<notin> RS"
        using Cons.prems(2) by blast
      moreover have "erev x \<noteq> erev r"
      proof
        assume "erev x = erev r"
        then have "erev (erev x) = erev (erev r)"
          by simp
        then show False
          using xr(2) by (simp add: erve_erve_id)
      qed
      ultimately show ?thesis
        by blast
    qed
  qed
  have es1: "set es \<subseteq> to_vertex_pair ` ?R1"
  proof
    fix d'
    assume d': "d' \<in> set es"
    then obtain x where x: "x \<in> RS" "to_vertex_pair x = d'"
      using Cons.prems(3) by auto
    have "d \<notin> set es"
      using Cons.prems(4) by simp
    then have "x \<noteq> r"
      using x(2) r(2) d' by auto
    then show "d' \<in> to_vertex_pair ` ?R1"
      using x by blast
  qed
  have dist1: "distinct es"
    using Cons.prems(4) by simp
  have swap1: "\<forall>(u, v) \<in> set es. u \<noteq> v \<and> (v, u) \<notin> set es"
    using Cons.prems(5) by auto
  obtain rs where rs: "map to_vertex_pair rs = es" "set rs \<subseteq> ?R1"
    "u_invar (?R1 - set rs \<union> erev ` set rs) (u_flip es (u_flip_arc st d))"
    "\<forall>x \<in> ?R1 - set rs \<union> erev ` set rs. erev x \<notin> ?R1 - set rs \<union> erev ` set rs"
    using Cons.IH[OF inv1 anti1 es1 dist1 swap1] by blast
  have er_rs: "erev r \<notin> set rs"
  proof
    assume "erev r \<in> set rs"
    then have "to_vertex_pair (erev r) \<in> set es"
      unfolding rs(1)[symmetric] by simp
    then show False
      using nswap tvp_er by simp
  qed
  have r_rs: "r \<notin> set rs"
  proof
    assume "r \<in> set rs"
    then have "to_vertex_pair r \<in> set es"
      unfolding rs(1)[symmetric] by simp
    then show False
      using Cons.prems(4) r(2) by simp
  qed
  have rs_R: "set rs \<subseteq> RS"
    using rs(2) er_rs by auto
  have set_eq: "?R1 - set rs \<union> erev ` set rs = RS - set (r # rs) \<union> erev ` set (r # rs)"
    using er_rs r_rs by auto
  have flip_eq: "u_flip (d # es) st = u_flip es (u_flip_arc st d)"
    by (simp add: u_flip_def)
  show ?case
  proof (intro exI[of _ "r # rs"] conjI)
    show "map to_vertex_pair (r # rs) = d # es"
      using r(2) rs(1) by simp
    show "set (r # rs) \<subseteq> RS"
      using r(1) rs_R by simp
    show "u_invar (RS - set (r # rs) \<union> erev ` set (r # rs)) (u_flip (d # es) st)"
      using rs(3) unfolding set_eq flip_eq .
    show "\<forall>x \<in> RS - set (r # rs) \<union> erev ` set (r # rs).
        erev x \<notin> RS - set (r # rs) \<union> erev ` set (r # rs)"
      using rs(4) unfolding set_eq .
  qed
qed

lemma u_search_correct:
  assumes inv: "u_invar RS st" and st: "s \<noteq> t"
  shows "u_search st s t = None \<longleftrightarrow> \<not> (\<exists>p. vwalk_bet (to_vertex_pair ` RS) s p t)"
    and "u_search st s t = Some p \<Longrightarrow> distinct p \<and> vwalk_bet (to_vertex_pair ` RS) s p t"
proof -
  note g = u_invarD[OF inv]
  note dw = dfs_walk[OF g(1-3) st]
  show "u_search st s t = None \<longleftrightarrow> \<not> (\<exists>p. vwalk_bet (to_vertex_pair ` RS) s p t)"
  proof (cases "neighbourhood (u_graph st) s = vset_empty")
    case True
    then show ?thesis
      using dw(1) unfolding g(5) by (simp add: u_search_def)
  next
    case False
    then show ?thesis
      using dw(1) unfolding g(5) by (simp add: u_search_def Let_def)
  qed
  show "distinct p \<and> vwalk_bet (to_vertex_pair ` RS) s p t" if "u_search st s t = Some p"
  proof -
    have "neighbourhood (u_graph st) s \<noteq> vset_empty"
      "return (dfs_impl (u_graph st) t (dfs_initial_state s)) = Reachable"
      "p = rev (stack (dfs_impl (u_graph st) t (dfs_initial_state s)))"
      using that by (simp_all add: u_search_def Let_def split: if_splits)
    then show ?thesis
      using dw(2) unfolding g(5) by simp
  qed
qed

text \<open>The data structure invariants alone are preserved by all operations, whatever the state
represents.\<close>

definition "u_wf st \<longleftrightarrow>
  dfs.Graph.graph_inv (u_graph st) \<and> dfs.Graph.finite_graph (u_graph st) \<and>
  dfs.Graph.finite_vsets (u_graph st) \<and> realising_edges_invar (u_bkt st)"

lemma u_invar_wf: "u_invar RS st \<Longrightarrow> u_wf st"
  by (simp add: u_invar_def u_wf_def)

lemma u_wf_init: "u_wf (u_init rs)"
  using dfs.Graph.from_list_correct(1-3)[where es = "map to_vertex_pair rs"]
    realising_edges_invar_pres[of rs]
  by (simp add: u_wf_def u_init_def)

lemma u_wf_add:
  assumes "u_wf st"
  shows "u_wf (u_add r st)"
proof -
  have g: "dfs.Graph.graph_inv (u_graph st)" "dfs.Graph.finite_graph (u_graph st)"
    "dfs.Graph.finite_vsets (u_graph st)" "realising_edges_invar (u_bkt st)"
    using assms by (simp_all add: u_wf_def)
  show ?thesis
    using graph_ops_inv(1)[OF g(1-3)] Map_realising.invar_update[OF g(4)]
    by (simp add: u_wf_def u_add_def Let_def)
qed

lemma u_wf_flip_arc:
  assumes "u_wf st"
  shows "u_wf (u_flip_arc st d)"
proof (cases "bucket (u_bkt st) d")
  case Nil
  then show ?thesis
    using assms by (simp add: u_flip_arc_def)
next
  case (Cons r rs)
  have g: "dfs.Graph.graph_inv (u_graph st)" "dfs.Graph.finite_graph (u_graph st)"
    "dfs.Graph.finite_vsets (u_graph st)" "realising_edges_invar (u_bkt st)"
    using assms by (simp_all add: u_wf_def)
  define G where "G = (if rs = [] then delete_edge (u_graph st) (prod.fst d) (prod.snd d)
    else u_graph st)"
  have G: "dfs.Graph.graph_inv G" "dfs.Graph.finite_graph G" "dfs.Graph.finite_vsets G"
    using graph_ops_inv(2)[OF g(1-3)] g(1-3) by (simp_all add: G_def)
  have bkt: "realising_edges_invar (realising_edges_update d rs (u_bkt st))"
    using g(4) by (rule Map_realising.invar_update)
  show ?thesis
    using graph_ops_inv(1)[OF G] Map_realising.invar_update[OF bkt] Cons
    by (simp add: u_wf_def u_flip_arc_def G_def[symmetric] Let_def)
qed

lemma u_wf_flip: "u_wf st \<Longrightarrow> u_wf (u_flip es st)"
proof (induction es arbitrary: st)
  case (Cons d es)
  then show ?case
    using u_wf_flip_arc[OF Cons.prems] by (simp add: u_flip_def)
qed (simp add: u_flip_def)

subsection \<open>Augmenting Unit Flows\<close>

text \<open>For a unit network on the edges, flipping a distinct walk of the projection augments the
represented unit flow by one. The flow outside the network does not change.\<close>

theorem u_flip_augment:
  assumes U: "unit_network fst snd create_edge \<u> \<E>"
    and inv: "u_invar {e | e. e \<in> \<EE> \<and> rcap f e > 0} st"
    and f: "f is s -- t flow" "isuflow f" "is_integral_flow f"
    and p: "distinct p" "vwalk_bet (to_vertex_pair ` {e | e. e \<in> \<EE> \<and> rcap f e > 0}) s p t"
  obtains g where "g is s -- t flow" "isuflow g" "is_integral_flow g" "ex g t = ex f t + 1"
    "u_invar {e | e. e \<in> \<EE> \<and> rcap g e > 0} (u_flip (edges_of_vwalk p) st)"
    "\<forall>d. d \<notin> \<E> \<longrightarrow> g d = f d"
proof -
  interpret unit_network fst snd create_edge \<u> \<E>
    by (rule U)
  have uf: "unit_flow f"
    using f(2,3) by simp
  have anti: "\<forall>r \<in> {e | e. e \<in> \<EE> \<and> rcap f e > 0}. erev r \<notin> {e | e. e \<in> \<EE> \<and> rcap f e > 0}"
    using unit_residual_rcap(2)[OF uf] by blast
  have es: "set (edges_of_vwalk p) \<subseteq> to_vertex_pair ` {e | e. e \<in> \<EE> \<and> rcap f e > 0}"
    by (rule vwalk_bet_edges_in_edges[OF p(2)])
  have dist: "distinct (edges_of_vwalk p)"
    by (rule distinct_edges_of_vwalk[OF p(1)])
  have swap: "\<forall>(u, v) \<in> set (edges_of_vwalk p). u \<noteq> v \<and> (v, u) \<notin> set (edges_of_vwalk p)"
  proof (intro ballI, clarify)
    fix u v
    assume uv: "(u, v) \<in> set (edges_of_vwalk p)"
    then have "(v, u) \<notin> set (edges_of_vwalk p)"
      by (rule edges_of_vwalk_distinct_swap[OF p(1)])
    then show "u \<noteq> v \<and> (v, u) \<notin> set (edges_of_vwalk p)"
      using uv by auto
  qed
  obtain rs where rs: "map to_vertex_pair rs = edges_of_vwalk p"
    "set rs \<subseteq> {e | e. e \<in> \<EE> \<and> rcap f e > 0}"
    "u_invar ({e | e. e \<in> \<EE> \<and> rcap f e > 0} - set rs \<union> erev ` set rs)
       (u_flip (edges_of_vwalk p) st)"
    using u_flip_correct_ex[OF inv anti es dist swap] by blast
  note aug = augment_unit[OF f(1) uf p rs(1,2)]
  have inv': "u_invar {e | e. e \<in> \<EE> \<and> rcap (augment_edges f 1 rs) e > 0} (u_flip (edges_of_vwalk p) st)"
    unfolding aug(4) by (rule rs(3))
  show ?thesis
    by (rule that[OF aug(1) _ _ aug(3) inv']) (use aug(2) aug(5) in auto)
qed

end

subsection \<open>Executable Instance\<close>

global_interpretation unit_impl: unit_flow_impl_spec where
  fst = fst and snd = snd and create_edge = create_edge and \<E> = \<E> and \<u> = \<u> and
  realising_edges_empty = empty and realising_edges_update = update and
  realising_edges_delete = delete and realising_edges_lookup = lookup and
  realising_edges_invar = M.invar
  for fst snd create_edge \<E> \<u>
  defines unit_realising = unit_impl.realising_edges_general
    and unit_bucket = unit_impl.bucket
    and unit_init = unit_impl.u_init
    and unit_add = unit_impl.u_add
    and unit_flip_arc = unit_impl.u_flip_arc
    and unit_flip = unit_impl.u_flip
    and unit_search = unit_impl.u_search
    and unit_invar = unit_impl.u_invar
    and unit_wf = unit_impl.u_wf
  using M.Map_axioms by (simp add: unit_flow_impl_spec_def residual_buckets_spec_def)

text \<open>A multigraph with parallel and antiparallel edges. An edge \<open>(u, v, i)\<close> goes from \<open>u\<close> to
\<open>v\<close>, and \<open>i\<close> distinguishes parallel edges.\<close>

definition "test_es = [(1::nat, 2::nat, 0::nat), (1, 2, 1), (2, 1, 0), (2, 3, 0), (1, 3, 0)]"

definition "test_fst = (\<lambda>(u::nat, v::nat, i::nat). u)"
definition "test_snd = (\<lambda>(u::nat, v::nat, i::nat). v)"

definition "test_run =
  (let st0 = unit_init test_fst test_snd (map F test_es);
       p1 = the (unit_search st0 1 3);
       st1 = unit_flip (edges_of_vwalk p1) st0;
       p2 = the (unit_search st1 1 3);
       st2 = unit_flip (edges_of_vwalk p2) st1
   in (p1, p2, unit_search st2 1 3, Tree2.inorder (u_bkt st2)))"

value test_run

end

