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

text \<open>Depth-first search from \<open>s\<close> to \<open>t\<close> decides reachability
and returns a distinct walk.\<close>

lemma dfs_walk:
  fixes Gr :: "('v::linorder \<times> 'v rbt) rbt"
  assumes "dfs.Graph.graph_inv Gr" "dfs.Graph.finite_graph Gr" "dfs.Graph.finite_vsets Gr"
    "s \<noteq> t"
  defines "r \<equiv> dfs_impl Gr t (dfs_initial_state s)"
  shows "(neighbourhood Gr s \<noteq> vset_empty \<and> return r = Reachable) \<longleftrightarrow>
      (\<exists>p. vwalk_bet (dfs.Graph.digraph_abs Gr) s p t)"
    and "\<lbrakk>neighbourhood Gr s \<noteq> vset_empty; return r = Reachable\<rbrakk> \<Longrightarrow>
      distinct (rev (stack r)) \<and> vwalk_bet (dfs.Graph.digraph_abs Gr) s (rev (stack r)) t"
proof-
  have "(return r = Reachable \<longleftrightarrow> (\<exists>p. vwalk_bet (dfs.Graph.digraph_abs Gr) s p t)) \<and>
      (return r = Reachable \<longrightarrow>
        distinct (rev (stack r)) \<and> vwalk_bet (dfs.Graph.digraph_abs Gr) s (rev (stack r)) t)"
    if "neighbourhood Gr s \<noteq> vset_empty"
  proof-
    have "t_set (neighbourhood Gr s) \<noteq> {}"
      using that
      by (auto simp: RBT_Set.empty_def)
    then have "s \<in> dVs (dfs.Graph.digraph_abs Gr)"
      using assms(1)
      by blast
    then interpret search: DFS_thms map_empty RBT_Map.delete vset_insert isin t_set sel update adj_inv
      vset_empty vset_delete vset_inv vset_union vset_inter vset_diff lookup Gr s t
      using assms(1-3)
      by (intro DFS_thms.intro dfs.DFS_axioms DFS_thms_axioms.intro) (simp add: dfs.DFS_axioms_def)
    show ?thesis
      using search.DFS_correct_1_strong search.DFS_correct_2
      by (cases "return r")
        (auto simp: r_def dfs_impl_def dfs_initial_state_def search.DFS_impl_to_DFS)
  qed
  moreover have "neighbourhood Gr s \<noteq> vset_empty"
    if "vwalk_bet (dfs.Graph.digraph_abs Gr) s p t" for p
    using assms that
    by (cases p rule: edges_of_vwalk.cases)
      (auto simp: vwalk_bet_def Pair_Graph.neighbourhood_def RBT_Set.empty_def)
  ultimately show "(neighbourhood Gr s \<noteq> vset_empty \<and> return r = Reachable) \<longleftrightarrow>
      (\<exists>p. vwalk_bet (dfs.Graph.digraph_abs Gr) s p t)"
    "\<lbrakk>neighbourhood Gr s \<noteq> vset_empty; return r = Reachable\<rbrakk> \<Longrightarrow>
      distinct (rev (stack r)) \<and> vwalk_bet (dfs.Graph.digraph_abs Gr) s (rev (stack r)) t"
    by blast+
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

lemma u_invarD:
  assumes "u_invar RS st"
  shows "dfs.Graph.graph_inv (u_graph st)" "dfs.Graph.finite_graph (u_graph st)"
    "dfs.Graph.finite_vsets (u_graph st)" "realising_edges_invar (u_bkt st)"
    "dfs.Graph.digraph_abs (u_graph st) = to_vertex_pair ` RS"
    "set (bucket (u_bkt st) d) = {r. r \<in> RS \<and> to_vertex_pair r = d}"
    "distinct (bucket (u_bkt st) d)"
  using assms[unfolded u_invar_def]
  by blast+

lemma u_invar_pair_iff: "u_invar RS st \<Longrightarrow>
  d \<in> to_vertex_pair ` RS \<longleftrightarrow> bucket (u_bkt st) d \<noteq> []"
  by (drule u_invarD(6)[where d = d]; cases "bucket (u_bkt st) d") auto

lemma graph_ops_inv:
  assumes "dfs.Graph.graph_inv G" "dfs.Graph.finite_graph G" "dfs.Graph.finite_vsets G"
  shows "dfs.Graph.graph_inv (add_edge G u v) \<and> dfs.Graph.finite_graph (add_edge G u v) \<and>
      dfs.Graph.finite_vsets (add_edge G u v)"
    and "dfs.Graph.graph_inv (delete_edge G u v) \<and> dfs.Graph.finite_graph (delete_edge G u v) \<and>
      dfs.Graph.finite_vsets (delete_edge G u v)"
  by (auto intro: assms dfs.Graph.finite_graph_add_edge dfs.Graph.finite_vsets_add_edge
      dfs.Graph.finite_graph_delete_edge dfs.Graph.finite_vsets_delete_edge)

lemma u_init_correct: "distinct rs \<Longrightarrow> u_invar (set rs) (u_init rs)"
  by (simp add: u_invar_def u_init_def dfs.Graph.from_list_correct(2,3)
      realising_edges_invar_pres bucket_general)

lemma u_add_correct:
  "\<lbrakk>u_invar RS st; r \<notin> RS\<rbrakk> \<Longrightarrow> u_invar (insert r RS) (u_add r st)"
  by (auto simp: u_invar_def u_add_def bucket_update Map_realising.invar_update
      simp del: split_paired_All
      intro: dfs.Graph.finite_graph_add_edge dfs.Graph.finite_vsets_add_edge)

lemma u_flip_arc_correct:
  assumes "u_invar RS st" "\<forall>r \<in> RS. erev r \<notin> RS"
    "d \<in> to_vertex_pair ` RS" "prod.fst d \<noteq> prod.snd d"
  obtains r where "r \<in> RS" "to_vertex_pair r = d" "u_invar (RS - {r} \<union> {erev r}) (u_flip_arc st d)"
proof-
  obtain r rs where head: "bucket (u_bkt st) d = r # rs"
    using assms(1,3) u_invar_pair_iff[of RS st d]
    by (cases "bucket (u_bkt st) d") auto
  let ?G = "if rs = [] then delete_edge (u_graph st) (prod.fst d) (prod.snd d) else u_graph st"
  let ?st = "\<lparr>u_graph = ?G, u_bkt = realising_edges_update d rs (u_bkt st)\<rparr>"
  have tail: "r \<in> RS" "to_vertex_pair r = d" "r \<notin> set rs"
    "set rs = {x \<in> RS - {r}. to_vertex_pair x = d}" "distinct rs"
    using assms(1) head u_invarD(6,7)[of RS st d]
    by auto
  have "to_vertex_pair ` (RS - {r}) = (if rs = [] then to_vertex_pair ` RS - {d} else to_vertex_pair ` RS)"
  proof(cases rs)
    case Nil
    then show ?thesis
      using tail
      by auto
  next
    case (Cons a xs)
    have "a \<in> {x \<in> RS - {r}. to_vertex_pair x = d}"
      by (subst tail(4)[symmetric]) (simp add: Cons)
    then have "d \<in> to_vertex_pair ` (RS - {r})"
      by (auto simp only: mem_Collect_eq image_iff)
    moreover have "to_vertex_pair ` RS = insert d (to_vertex_pair ` (RS - {r}))"
      by (simp only: tail(2)[symmetric] image_insert[symmetric] insert_Diff[OF tail(1)])
    ultimately show ?thesis
      using Cons
      by (simp add: insert_absorb)
  qed
  then have "u_invar (RS - {r}) ?st"
    using assms(1) tail(1,2,4,5)
    by (auto simp: u_invar_def bucket_update Map_realising.invar_update
        simp del: split_paired_All
        intro: dfs.Graph.finite_graph_delete_edge dfs.Graph.finite_vsets_delete_edge
        split: if_splits)
  then have "u_invar (insert (erev r) (RS - {r})) (u_add (erev r) ?st)"
    by (rule u_add_correct) (use assms(2) tail(1) in auto)
  then have "u_invar (RS - {r} \<union> {erev r}) (u_flip_arc st d)"
    by (simp add: u_flip_arc_def u_add_def to_vertex_pair_erev tail(2) head)
  then show ?thesis
    by (rule that[OF tail(1,2)])
qed

text \<open>Flipping a list of arcs that are pairwise distinct, contain no loops and no reversed arcs.\<close>

lemma u_flip_correct_ex:
  assumes "u_invar RS st" "\<forall>r \<in> RS. erev r \<notin> RS" 
    "set es \<subseteq> to_vertex_pair ` RS" "distinct es"
    "\<forall>(u, v) \<in> set es. u \<noteq> v \<and> (v, u) \<notin> set es"
  shows "\<exists>rs. map to_vertex_pair rs = es \<and> set rs \<subseteq> RS \<and>
    u_invar (RS - set rs \<union> erev ` set rs) (u_flip es st) \<and>
    (\<forall>r \<in> RS - set rs \<union> erev ` set rs. erev r \<notin> RS - set rs \<union> erev ` set rs)"
  using assms
proof(induction es arbitrary: RS st)
  case Nil
  then show ?case
    by (simp add: u_flip_def)
next
  case (Cons d es)
  obtain r where edge: "r \<in> RS" "to_vertex_pair r = d"
    "u_invar (RS - {r} \<union> {erev r}) (u_flip_arc st d)"
    by (rule u_flip_arc_correct[OF Cons.prems(1,2), where d = d]) (use Cons.prems(3-5) in auto)
  have "\<forall>x \<in> RS - {r} \<union> {erev r}. erev x \<notin> RS - {r} \<union> {erev r}"
    using Cons.prems(2) edge(1) inj_erev_general
    by (auto simp: erve_erve_id dest: injD)
  moreover have "set es \<subseteq> to_vertex_pair ` (RS - {r} \<union> {erev r})"
  proof
    fix e
    assume "e \<in> set es"
    then have "e \<in> set (d # es)" "e \<noteq> d"
      using Cons.prems(4)
      by auto
    then obtain a where "a \<in> RS" "to_vertex_pair a = e" "e \<noteq> d"
      using Cons.prems(3)
      by blast
    then show "e \<in> to_vertex_pair ` (RS - {r} \<union> {erev r})"
      using edge(2)
      by (auto simp: image_iff)
  qed
  moreover have "distinct es" "\<forall>(u, v) \<in> set es. u \<noteq> v \<and> (v, u) \<notin> set es"
    using Cons.prems(4,5)
    by auto
  ultimately obtain rs where tail: "map to_vertex_pair rs = es" "set rs \<subseteq> RS - {r} \<union> {erev r}"
    "u_invar ((RS - {r} \<union> {erev r}) - set rs \<union> erev ` set rs) (u_flip es (u_flip_arc st d))"
    "\<forall>x \<in> (RS - {r} \<union> {erev r}) - set rs \<union> erev ` set rs.
      erev x \<notin> (RS - {r} \<union> {erev r}) - set rs \<union> erev ` set rs"
    using Cons.IH[OF edge(3)]
    by blast
  have "d \<notin> set es" "prod.swap d \<notin> set es"
    using Cons.prems(4,5)
    by (cases d; auto)+
  then have "to_vertex_pair r \<notin> to_vertex_pair ` set rs"
    "to_vertex_pair (erev r) \<notin> to_vertex_pair ` set rs"
    by (simp only: set_map[symmetric] tail(1) to_vertex_pair_erev edge(2); simp)+
  then have "r \<notin> set rs" "erev r \<notin> set rs"
    by auto
  moreover hence "(RS - {r} \<union> {erev r}) - set rs \<union> erev ` set rs =
      RS - set (r # rs) \<union> erev ` set (r # rs)"
    by auto
  ultimately show ?case
    using edge(1,2) tail
    by (intro exI[of _ "r # rs"]) (auto simp: u_flip_def)
qed

lemma u_search_correct:
  assumes "u_invar RS st" "s \<noteq> t"
  shows "u_search st s t = None \<longleftrightarrow> \<not> (\<exists>p. vwalk_bet (to_vertex_pair ` RS) s p t)"
    and "u_search st s t = Some p \<Longrightarrow> distinct p \<and> vwalk_bet (to_vertex_pair ` RS) s p t"
  using dfs_walk[of "u_graph st" s t] assms
  by (auto simp: u_invar_def u_search_def split: if_splits; blast)+

text \<open>The data structure invariants alone are preserved by all operations, whatever the state
represents.\<close>

definition "u_wf st \<longleftrightarrow>
  dfs.Graph.graph_inv (u_graph st) \<and> dfs.Graph.finite_graph (u_graph st) \<and>
  dfs.Graph.finite_vsets (u_graph st) \<and> realising_edges_invar (u_bkt st)"

lemma u_invar_wf: "u_invar RS st \<Longrightarrow> u_wf st"
  by (simp add: u_invar_def u_wf_def)

lemma u_wf_init: "u_wf (u_init rs)"
  by (simp add: u_wf_def u_init_def dfs.Graph.from_list_correct(2,3) realising_edges_invar_pres)

lemma u_wf_add: "u_wf st \<Longrightarrow> u_wf (u_add r st)"
  by (auto simp: u_wf_def u_add_def Map_realising.invar_update
      intro: dfs.Graph.finite_graph_add_edge dfs.Graph.finite_vsets_add_edge)

lemma u_wf_flip_arc: "u_wf st \<Longrightarrow> u_wf (u_flip_arc st d)"
  by (auto simp: u_wf_def u_flip_arc_def Map_realising.invar_update
      intro: dfs.Graph.finite_graph_add_edge dfs.Graph.finite_vsets_add_edge
        dfs.Graph.finite_graph_delete_edge dfs.Graph.finite_vsets_delete_edge
      split: list.splits if_splits)

lemma u_wf_flip: "u_wf st \<Longrightarrow> u_wf (u_flip es st)"
  by (induction es arbitrary: st) (auto simp: u_flip_def intro: u_wf_flip_arc[unfolded u_flip_def])

subsection \<open>Augmenting Unit Flows\<close>

text \<open>For a unit network on the edges, flipping a distinct walk of the projection augments the
represented unit flow by one. The flow outside the network does not change.\<close>

lemma u_flip_augment:
  assumes "unit_network fst snd create_edge \<u> \<E>"
    "u_invar {e | e. e \<in> \<EE> \<and> rcap f e > 0} st"
    "f is s -- t flow" "isuflow f" "is_integral_flow f"
    "distinct p" "vwalk_bet (to_vertex_pair ` {e | e. e \<in> \<EE> \<and> rcap f e > 0}) s p t"
  obtains g where "g is s -- t flow" "isuflow g" "is_integral_flow g" "ex g t = ex f t + 1"
    "u_invar {e | e. e \<in> \<EE> \<and> rcap g e > 0} (u_flip (edges_of_vwalk p) st)"
    "\<forall>d. d \<notin> \<E> \<longrightarrow> g d = f d"
proof-
  interpret unit_network fst snd create_edge \<u> \<E>
    by (rule assms(1))
  have "\<forall>r \<in> {e | e. e \<in> \<EE> \<and> rcap f e > 0}.
      erev r \<notin> {e | e. e \<in> \<EE> \<and> rcap f e > 0}"
    using assms(4,5) unit_residual_rcap(2)[of f]
    by blast
  moreover have "set (edges_of_vwalk p) \<subseteq> to_vertex_pair ` {e | e. e \<in> \<EE> \<and> rcap f e > 0}"
    using assms(7)
    by (rule vwalk_bet_edges_in_edges)
  moreover have "distinct (edges_of_vwalk p)"
    using assms(6)
    by (rule distinct_edges_of_vwalk)
  moreover have "\<forall>(u, v) \<in> set (edges_of_vwalk p).
      u \<noteq> v \<and> (v, u) \<notin> set (edges_of_vwalk p)"
    using assms(6) edges_of_vwalk_distinct_swap[of p]
    by fastforce
  ultimately obtain rs where "map to_vertex_pair rs = edges_of_vwalk p"
    "set rs \<subseteq> {e | e. e \<in> \<EE> \<and> rcap f e > 0}"
    "u_invar ({e | e. e \<in> \<EE> \<and> rcap f e > 0} - set rs \<union> erev ` set rs)
       (u_flip (edges_of_vwalk p) st)"
    using u_flip_correct_ex[OF assms(2), where es = "edges_of_vwalk p"]
    by blast
  then show ?thesis
    using assms(3-7) augment_unit[of f s t p rs] that
    by auto
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
  using M.Map_axioms
  by (simp add: unit_flow_impl_spec_def residual_buckets_spec_def)

text \<open>A multigraph with parallel and antiparallel edges. An edge \<open>(u, v, i)\<close>
goes from \<open>u\<close> to
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

