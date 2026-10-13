theory Kruskal
  imports Matroids_Greedy.BestInGreedy_exec Spanning_Trees Data_Structures.UnionFind_Specs
    Undirected_Set_Graphs.Directed_Undirected "HOL-Library.Product_Lexorder"
begin

(* TODO put in ROOT file *)

section \<open>Kruskal's Algorithm via the Best-In-Greedy Algorithm and Union-Find\<close>

subsection \<open>Adding an Edge to a Forest\<close>

context graph_abs
begin

text \<open>Adding a new edge \<open>{u, v}\<close> to a forest creates a cycle iff \<open>u\<close> and \<open>v\<close> are already
  connected in the forest.\<close>

lemma has_no_cycle_insert_iff:
  assumes "has_no_cycle Y" "{u, v} \<in> G" "{u, v} \<notin> Y" "u \<noteq> v"
  shows "has_no_cycle (insert {u, v} Y) \<longleftrightarrow> \<not> reachable Y u v"
proof
  assume no_cycle: "has_no_cycle (insert {u, v} Y)"
  show "\<not> reachable Y u v"
  proof
    assume "reachable Y u v"
    then obtain p where "walk_betw Y u p v"
      by (auto simp: reachable_def)
    moreover have "dblton_graph Y"
      using assms(1) graph_abs_subset by (auto simp: has_no_cycle_def graph_abs_def)
    ultimately have "epath Y u (edges_of_path p) v"
      by (rule walk_betw_imp_epath[rotated])
    then obtain q where q: "epath Y u q v" "set q \<subseteq> set (edges_of_path p)" "distinct q"
      using epath_distinct_epath[OF _ refl] by metis
    have "epath (insert {u, v} Y) u q v"
      using q(1) by (auto intro: epath_subset)
    moreover have "epath (insert {u, v} Y) v [{u, v}] u"
      using assms(4) by (auto intro!: epath_single)
    ultimately have epath_cycle: "epath (insert {u, v} Y) u (q @ [{u, v}]) u"
      by (rule epath_append)
    have q_in_Y: "set q \<subseteq> Y"
      using q(1) epath_edges_subset by fast
    have "length q \<ge> 1"
      using q(1) assms(4) by (rule epath_non_empty)
    moreover have "length q \<noteq> 1"
    proof
      assume "length q = 1"
      then obtain e where "q = [e]"
        by (cases q) auto
      hence "e = {u, v}"
        using q(1) by auto
      thus False
        using q_in_Y \<open>q = [e]\<close> assms(3) by auto
    qed
    ultimately have "length (q @ [{u, v}]) > 2"
      by simp
    moreover have "distinct (q @ [{u, v}])"
      using q(3) q_in_Y assms(3) by auto
    ultimately have "decycle (insert {u, v} Y) u (q @ [{u, v}])"
      using epath_cycle by (auto simp: decycle_def)
    thus False
      using no_cycle by (auto simp: has_no_cycle_def)
  qed
next
  assume not_reachable: "\<not> reachable Y u v"
  have insert_in_G: "insert {u, v} Y \<subseteq> G"
    using assms(1,2) by (auto simp: has_no_cycle_def)
  show "has_no_cycle (insert {u, v} Y)"
  proof (unfold has_no_cycle_def, intro conjI insert_in_G notI, elim exE)
    fix w C
    assume cycle: "decycle (insert {u, v} Y) w C"
    have "\<not> decycle Y w C"
      using assms(1) by (auto simp: has_no_cycle_def)
    hence "{u, v} \<in> set C"
      using cycle by (rule new_edge_in_decycle)
    then obtain q where "walk_betw Y v q u"
      using decycle_edge_path[OF insert_in_G cycle] by blast
    hence "reachable Y u v"
      by (auto simp: reachable_def intro: walk_symmetric)
    thus False
      using not_reachable by simp
  qed
qed

end

subsection \<open>The Locale\<close>

text \<open>The graph is given by the ADT \<open>Pair_Graph_U_Specs\<close> and is only used for stating
  the correctness theorems. The algorithm itself only uses the list of edges \<open>order\<close>, which
  contains every edge of the graph exactly once (as the pair \<open>(u, v)\<close> with \<open>u < v\<close>), and a
  union-find structure over a universe \<open>s\<close> containing all vertices of the graph.

  The edge set ADT \<open>'s\<close> is required by the Best-In-Greedy locale, but it is not used by the
  executable algorithm: the carrier and the result are only abstractions for the proofs.\<close>

locale Kruskal =
  graph: Pair_Graph_U_Specs where lookup = "lookup :: 'adjmap \<Rightarrow> ('v::linorder) \<Rightarrow> 'vset option"
    and insert = vset_insert +
  edges: Matroid_Specs where set_empty = "set_empty :: 's"
    and set_insert = "set_insert :: ('v \<times> 'v) \<Rightarrow> 's \<Rightarrow> 's" +
  uf: UnionFind_Specs where uf_invar = "uf_invar :: 'u \<Rightarrow> 'i \<Rightarrow> bool"
    and set_of_sets = "set_of_sets :: 'u \<Rightarrow> 'v set set" and set = uf_set
  for lookup vset_insert set_empty set_insert uf_invar set_of_sets uf_set +
  fixes G :: 'adjmap and order :: "('v \<times> 'v) list" and s :: 'i
    and sort_desc :: "(('v \<times> 'v) \<Rightarrow> rat) \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> ('v \<times> 'v) list"
  assumes G_invar: "graph.pair_graph_u_invar G"
    and order_is_G: "set order = {(u, v). (u, v) \<in> graph.digraph_abs G \<and> u < v}"
    and order_distinct: "distinct order"
    and vertices_in_universe: "graph.vertices G \<subseteq> uf_set s"
    and sort_desc_axioms: "sort_desc_axioms' sort_desc"
    and edges_finite_sets: "edges.finite_sets"
begin

text \<open>The (abstract) undirected graph.\<close>

abbreviation "E \<equiv> graph.ugraph_abs G"

subsubsection \<open>Instantiation of the Best-In-Greedy Algorithm\<close>

text \<open>The carrier and the independence function are only needed for the proofs.\<close>

definition "kruskal_carrier = edges.from_set (set order)"

definition "kruskal_indep X =
  (to_set X \<subseteq> set order \<and> graph_abs.has_no_cycle E (set_of_pair ` to_set X))"

text \<open>The wrapper of the result consists of the list of chosen edges and a union-find
  structure, whose sets are the connected components of the chosen edges (over the universe).
  The independence oracle only needs the union-find structure.\<close>

definition "kruskal_wrapper_empty = ([], uf_init s)"

definition "kruskal_wrapper_insert e W = (e # fst W, merge (snd W) (fst e) (snd e))"

definition "kruskal_remove_wrapper W = edges.insert_elements (fst W)"

definition "kruskal_oracle e W = (\<not> in_same_set (snd W) (fst e) (snd e))"

definition "kruskal_wrapper_invar W =
  (uf_invar (snd W) s \<and> set_of_sets (snd W) = comps (uf_set s) (set_of_pair ` set (fst W)))"

subsubsection \<open>Basic Properties of the Graph and the Edge List\<close>

lemma graph_abs_E: "graph_abs E"
  using graph.graph_abs_ugraph[OF G_invar] .

lemma order_edge_props:
  assumes "(u, v) \<in> set order"
  shows "u < v" "u \<noteq> v" "(u, v) \<in> graph.digraph_abs G" "{u, v} \<in> E" "u \<in> uf_set s" "v \<in> uf_set s"
proof-
  show uv: "(u, v) \<in> graph.digraph_abs G" "u < v"
    using assms order_is_G by auto
  thus "u \<noteq> v" by simp
  show "{u, v} \<in> E"
    using uv(1) by (auto simp: graph.ugraph_and_digraph_abs)
  show "u \<in> uf_set s" "v \<in> uf_set s"
    using uv(1) vertices_in_universe by (auto simp: graph.vertices_equiv_dVs dVs_def)
qed

lemma E_is_order: "E = set_of_pair ` set order"
proof (rule set_eqI, rule iffI)
  fix e
  assume "e \<in> E"
  then obtain u v where uv: "e = {u, v}" "(u, v) \<in> graph.digraph_abs G"
    by (auto simp: graph.ugraph_and_digraph_abs)
  hence "(v, u) \<in> graph.digraph_abs G"
    using graph.graph_abs_symmetric[OF G_invar] by blast
  moreover have "u \<noteq> v"
    using uv(2) graph.digraph_abs_irreflexive[OF G_invar] by (auto simp: dVs_def)
  ultimately have "(u, v) \<in> set order \<or> (v, u) \<in> set order"
    using uv(2) order_is_G by (cases "u < v") auto
  thus "e \<in> set_of_pair ` set order"
    using uv(1) by (auto simp: set_of_pair_def insert_commute)
next
  fix e
  assume "e \<in> set_of_pair ` set order"
  thus "e \<in> E"
    using order_edge_props(4) by (auto simp: set_of_pair_def)
qed

lemma set_of_pair_inj_order: "inj_on set_of_pair (set order)"
proof (rule inj_onI)
  fix x y
  assume asm: "x \<in> set order" "y \<in> set order" "set_of_pair x = set_of_pair y"
  obtain a b c d where xy: "x = (a, b)" "y = (c, d)"
    by fastforce
  have "a < b" "c < d"
    using asm(1,2) xy order_edge_props(1) by auto
  moreover have "{a, b} = {c, d}"
    using asm(3) xy by (simp add: set_of_pair_def)
  ultimately show "x = y"
    using xy by (auto simp: doubleton_eq_iff)
qed

lemma graph_abs_subset_order: "X \<subseteq> set order \<Longrightarrow> graph_abs (set_of_pair ` X)"
  by (rule graph_abs_mono[OF graph_abs_E]) (auto simp: E_is_order)

lemma has_no_cycle_subset:
  "\<lbrakk>graph_abs.has_no_cycle E Y; X \<subseteq> Y\<rbrakk> \<Longrightarrow> graph_abs.has_no_cycle E X"
  using graph_abs.has_no_cycle_indep_subset[OF graph_abs_E] by blast

subsubsection \<open>Union-Find and Connected Components\<close>

lemma in_same_set_iff_component:
  assumes "uf_invar uf s" "set_of_sets uf = comps (uf_set s) F" "u \<in> uf_set s" "v \<in> uf_set s"
  shows "in_same_set uf u v \<longleftrightarrow> v \<in> connected_component F u"
proof-
  have "in_same_set uf u v \<longleftrightarrow> (\<exists>w \<in> uf_set s. u \<in> connected_component F w \<and> v \<in> connected_component F w)"
    using uf.in_same_set_correct[OF assms(1,3,4)] assms(2) by (auto simp: comps_def)
  also have "\<dots> \<longleftrightarrow> v \<in> connected_component F u"
    using assms(3) connected_components_member_eq in_own_connected_component by metis
  finally show ?thesis .
qed

lemma component_iff_reachable:
  "u \<noteq> v \<Longrightarrow> v \<in> connected_component F u \<longleftrightarrow> reachable F u v"
  by (auto simp: connected_component_def)

subsubsection \<open>The Carrier\<close>

lemma kruskal_carrier_props:
  "set_inv kruskal_carrier" "to_set kruskal_carrier = set order"
  "cardinality kruskal_carrier = length order"
proof-
  show inv: "set_inv kruskal_carrier"
    by (simp add: kruskal_carrier_def edges.invar_from_set)
  show set: "to_set kruskal_carrier = set order"
    by (simp add: kruskal_carrier_def edges.from_set_correct)
  show "cardinality kruskal_carrier = length order"
    using edges.set.set_cardinality[OF inv] set order_distinct by (simp add: distinct_card)
qed

subsubsection \<open>The Wrapper and the Oracle\<close>

lemma to_set_kruskal_remove_wrapper: "to_set (kruskal_remove_wrapper W) = set (fst W)"
  by (simp add: kruskal_remove_wrapper_def edges.set_correct_insert_elements)

lemma set_inv_kruskal_remove_wrapper: "set_inv (kruskal_remove_wrapper W)"
  by (simp add: kruskal_remove_wrapper_def edges.invar_insert_elements)

lemma to_set_insert_kruskal_remove_wrapper:
  "to_set (set_insert e (kruskal_remove_wrapper W)) = insert e (set (fst W))"
  by (simp add: edges.set.set_insert[OF set_inv_kruskal_remove_wrapper]
      to_set_kruskal_remove_wrapper)

text \<open>The invariant of the union-find structure is only preserved when the inserted edge does
  not close a cycle, which is exactly the case in which the algorithm inserts it.\<close>

lemma kruskal_wrapper_invar_insert:
  assumes "kruskal_wrapper_invar W" "e \<in> set order"
    "kruskal_indep (set_insert e (kruskal_remove_wrapper W))"
  shows "kruskal_wrapper_invar (kruskal_wrapper_insert e W)"
proof-
  obtain R uf where W: "W = (R, uf)" by fastforce
  obtain u v where e: "e = (u, v)" by fastforce
  let ?F = "set_of_pair ` set R"
  have e_in: "(u, v) \<in> set order"
    using assms(2) e by simp
  have no_cycle_new: "graph_abs.has_no_cycle E (insert {u, v} ?F)"
    using assms(3)
    by (simp add: kruskal_indep_def to_set_insert_kruskal_remove_wrapper W e set_of_pair_def)
  have no_cycle_old: "graph_abs.has_no_cycle E ?F"
    using has_no_cycle_subset[OF no_cycle_new] by blast
  have uf_props: "uf_invar uf s" "set_of_sets uf = comps (uf_set s) ?F"
    using assms(1) by (auto simp: kruskal_wrapper_invar_def W)
  have uv: "u \<in> uf_set s" "v \<in> uf_set s" "u \<noteq> v" "{u, v} \<in> E"
    using order_edge_props[OF e_in] by auto
  have AB: "connected_component ?F u \<in> set_of_sets uf" "connected_component ?F v \<in> set_of_sets uf"
    using uf_props(2) uv(1,2) by (auto simp: comps_def)
  have merge_is: "set_of_sets (merge uf u v) =
    set_of_sets uf - {connected_component ?F u, connected_component ?F v} \<union>
      {connected_component ?F u \<union> connected_component ?F v}"
    using uf.merge_correct[OF uf_props(1) in_own_connected_component in_own_connected_component AB] .
  have "comps (uf_set s) (insert {u, v} ?F) =
    set_of_sets uf - {connected_component ?F u, connected_component ?F v} \<union>
      {connected_component ?F u \<union> connected_component ?F v}"
  proof (cases "connected_component ?F u = connected_component ?F v")
    case True
    show ?thesis
    proof (cases "{u, v} \<in> ?F")
      case True
      thus ?thesis
        using \<open>connected_component ?F u = connected_component ?F v\<close> AB uf_props(2)
        by (auto simp: insert_absorb)
    next
      case False
      have "v \<in> connected_component ?F u"
        using True in_own_connected_component by metis
      hence "reachable ?F u v"
        using component_iff_reachable[OF uv(3)] by simp
      thus ?thesis
        using graph_abs.has_no_cycle_insert_iff[OF graph_abs_E no_cycle_old uv(4) False uv(3)]
          no_cycle_new by blast
    qed
  next
    case False
    thus ?thesis
      using new_component_insert_edge[OF False uv(1,2)] uf_props(2) by simp
  qed
  thus ?thesis
    using uf.merge_invar[OF uf_props(1) uv(1,2)] merge_is
    by (auto simp: kruskal_wrapper_invar_def kruskal_wrapper_insert_def W e set_of_pair_def)
qed

lemma kruskal_wrapper_invar_empty: "kruskal_wrapper_invar kruskal_wrapper_empty"
  by (simp add: kruskal_wrapper_invar_def kruskal_wrapper_empty_def comps_def uf.uf_init_invar
      uf.uf_init_correct connected_components_notE_singletons Vs_def)

lemma kruskal_wrapper_axioms:
  "\<And>W e. kruskal_wrapper_invar W \<Longrightarrow> e \<in> to_set kruskal_carrier \<Longrightarrow>
     kruskal_indep (set_insert e (kruskal_remove_wrapper W)) \<Longrightarrow>
     kruskal_wrapper_invar (kruskal_wrapper_insert e W)"
  "\<And>W. kruskal_wrapper_invar W \<Longrightarrow> set_inv (kruskal_remove_wrapper W)"
  "\<And>W e. kruskal_wrapper_invar W \<Longrightarrow>
     kruskal_remove_wrapper (kruskal_wrapper_insert e W) = set_insert e (kruskal_remove_wrapper W)"
  "set_empty = kruskal_remove_wrapper kruskal_wrapper_empty"
  "kruskal_wrapper_invar kruskal_wrapper_empty"
  by (simp_all add: kruskal_wrapper_invar_insert kruskal_wrapper_invar_empty
      set_inv_kruskal_remove_wrapper kruskal_carrier_props)
    (simp_all add: kruskal_remove_wrapper_def kruskal_wrapper_insert_def kruskal_wrapper_empty_def)

lemma kruskal_oracle_correct:
  assumes "kruskal_wrapper_invar W" "kruskal_indep (kruskal_remove_wrapper W)"
    "e \<notin> to_set (kruskal_remove_wrapper W)" "e \<in> to_set kruskal_carrier"
  shows "kruskal_oracle e W \<longleftrightarrow> kruskal_indep (set_insert e (kruskal_remove_wrapper W))"
proof-
  obtain R uf where W: "W = (R, uf)" by fastforce
  obtain u v where e: "e = (u, v)" by fastforce
  let ?F = "set_of_pair ` set R"
  have e_in: "e \<in> set order"
    using assms(4) kruskal_carrier_props(2) by simp
  have R_props: "set R \<subseteq> set order" "graph_abs.has_no_cycle E ?F" "e \<notin> set R"
    using assms(2,3) by (auto simp: kruskal_indep_def to_set_kruskal_remove_wrapper W)
  have uf_props: "uf_invar uf s" "set_of_sets uf = comps (uf_set s) ?F"
    using assms(1) by (auto simp: kruskal_wrapper_invar_def W)
  have uv: "u \<in> uf_set s" "v \<in> uf_set s" "u \<noteq> v" "{u, v} \<in> E"
    using order_edge_props e_in e by auto
  have "{u, v} \<notin> ?F"
  proof
    assume "{u, v} \<in> ?F"
    then obtain d where "d \<in> set R" "set_of_pair d = set_of_pair e"
      by (auto simp: e set_of_pair_def)
    thus False
      using set_of_pair_inj_order R_props(1,3) e_in by (auto dest: inj_onD)
  qed
  have "kruskal_oracle e W \<longleftrightarrow> \<not> reachable ?F u v"
    using in_same_set_iff_component[OF uf_props uv(1,2)] component_iff_reachable[OF uv(3)]
    by (simp add: kruskal_oracle_def W e)
  also have "\<dots> \<longleftrightarrow> graph_abs.has_no_cycle E (insert {u, v} ?F)"
    using graph_abs.has_no_cycle_insert_iff[OF graph_abs_E R_props(2) uv(4) \<open>{u, v} \<notin> ?F\<close> uv(3)]
    by simp
  also have "\<dots> \<longleftrightarrow> kruskal_indep (set_insert e (kruskal_remove_wrapper W))"
    using R_props(1) e_in
    by (simp add: kruskal_indep_def to_set_insert_kruskal_remove_wrapper W e set_of_pair_def)
  finally show ?thesis .
qed

subsubsection \<open>The Functional Kruskal Algorithm\<close>

sublocale kruskal_greedy: BestInGreedy_exec where set_empty = set_empty and set_insert = set_insert
  and set_delete = set_delete and set_isin = set_isin and to_set = to_set and set_inv = set_inv
  and union = union and inter = inter and diff = diff and cardinality = cardinality
  and carrier = kruskal_carrier and indep_fn = kruskal_indep and sort_desc = sort_desc
  and local_indep_oracle = kruskal_oracle and remove_wrapper = kruskal_remove_wrapper
  and wrapper_invar = kruskal_wrapper_invar and wrapper_insert = kruskal_wrapper_insert
  and wrapper_empty = kruskal_wrapper_empty
  by (unfold BestInGreedy_exec_def BestInGreedy_base_def)
    (auto intro!: BestInGreedy_exec_axioms.intro edges.Matroid_Specs_axioms kruskal_wrapper_axioms)

text \<open>The (functional) Kruskal algorithm is the Best-In-Greedy algorithm with the
  union-find oracle.\<close>

definition "kruskal c = kruskal_greedy.BestInGreedy_exec (kruskal_greedy.initial_state' c order)"

subsubsection \<open>Assumptions of the Best-In-Greedy Algorithm\<close>

lemma kruskal_base_axioms: "kruskal_greedy.BestInGreedy_base_axioms"
  using kruskal_carrier_props(1) edges_finite_sets
  by (auto simp: kruskal_greedy.BestInGreedy_base_axioms_def kruskal_indep_def)

lemma kruskal_indep_system_axioms: "edges.indep_system_axioms kruskal_carrier kruskal_indep"
  unfolding edges.indep_system_axioms_def
proof (intro conjI allI impI)
  fix X
  assume "set_inv X" "kruskal_indep X"
  thus "edges.subseteq X kruskal_carrier"
    using kruskal_carrier_props(1,2) by (simp add: edges.set.set_subseteq kruskal_indep_def)
next
  show "\<exists>X. set_inv X \<and> kruskal_indep X"
    using graph_abs.has_no_cycle_indep_ex[OF graph_abs_E] has_no_cycle_subset[of _ "{}"]
      edges.set.invar_empty edges.set.set_empty
    by (auto intro!: exI[of _ set_empty] simp: kruskal_indep_def)
next
  fix X Y
  assume "set_inv X" "set_inv Y" "kruskal_indep X" "edges.subseteq Y X"
  thus "kruskal_indep Y"
    using has_no_cycle_subset[OF _ image_mono]
    by (auto simp: kruskal_indep_def edges.set.set_subseteq)
qed

lemma kruskal_nonnegative:
  "(\<And>e. e \<in> set order \<Longrightarrow> c e \<ge> 0) \<Longrightarrow> kruskal_greedy.nonnegative c"
  using kruskal_carrier_props(1,2) by (simp add: kruskal_greedy.nonnegative_def edges.set.set_isin)

lemma kruskal_valid_order: "kruskal_greedy.valid_order order"
  using kruskal_carrier_props by (simp add: kruskal_greedy.valid_order_def)

subsubsection \<open>Correspondence to the Abstract Best-In-Greedy Algorithm\<close>

lemma kruskal_corresp:
  assumes "\<And>e. e \<in> set order \<Longrightarrow> c e \<ge> 0"
  shows "kruskal_greedy.to_ordinary (kruskal c) =
    kruskal_greedy.BestInGreedy_base (kruskal_greedy.initial_state c order)"
  unfolding kruskal_def
proof (rule kruskal_greedy.BestInGreedy_exec_corresp, goal_cases)
  case (1 W e)
  thus ?case
    by (intro kruskal_oracle_correct)
qed (auto simp: kruskal_carrier_props kruskal_base_axioms sort_desc_axioms
    kruskal_indep_system_axioms kruskal_nonnegative assms kruskal_valid_order)

subsubsection \<open>The Graphic Matroid on the Edge List\<close>

definition "kruskal_indep_abs X = (X \<subseteq> set order \<and> graph_abs.has_no_cycle E (set_of_pair ` X))"

lemma kruskal_carrier_abs: "edges.carrier_abs kruskal_carrier = set order"
  by (simp add: edges.carrier_abs_def kruskal_carrier_props)

lemma kruskal_indep_abs_eq: "edges.indep_abs kruskal_indep = kruskal_indep_abs"
proof (rule ext)
  fix X
  show "edges.indep_abs kruskal_indep X = kruskal_indep_abs X"
  proof (cases "finite X")
    case True
    thus ?thesis
      by (simp add: edges.indep_abs_def edges.to_function_def edges.from_set_correct
          kruskal_indep_def kruskal_indep_abs_def)
  next
    case False
    hence "\<not> X \<subseteq> set order"
      using finite_subset by blast
    thus ?thesis
      using False by (simp add: edges.indep_abs_def edges.to_function_def kruskal_indep_abs_def)
  qed
qed

lemma kruskal_invar: "edges.invar kruskal_carrier kruskal_indep"
  using kruskal_base_axioms by (simp add: kruskal_greedy.BestInGreedy_base_axioms_def)

lemma kruskal_indep_system: "indep_system (set order) kruskal_indep_abs"
  using edges.indep_system_impl_to_abs[OF kruskal_invar edges_finite_sets
      kruskal_indep_system_axioms]
  by (simp add: kruskal_carrier_abs kruskal_indep_abs_eq)

lemma kruskal_matroid: "matroid (set order) kruskal_indep_abs"
proof (rule matroid.intro[OF kruskal_indep_system], rule matroid_axioms.intro)
  fix X Y
  assume asm: "kruskal_indep_abs X" "kruskal_indep_abs Y" "card X = Suc (card Y)"
  hence XY: "X \<subseteq> set order" "Y \<subseteq> set order"
    "graph_abs.has_no_cycle E (set_of_pair ` X)" "graph_abs.has_no_cycle E (set_of_pair ` Y)"
    by (auto simp: kruskal_indep_abs_def)
  have "card (set_of_pair ` X) = Suc (card (set_of_pair ` Y))"
    using asm(3) XY(1,2) set_of_pair_inj_order
    by (simp add: card_image inj_on_subset)
  then obtain e where e: "e \<in> set_of_pair ` X - set_of_pair ` Y"
    "graph_abs.has_no_cycle E (insert e (set_of_pair ` Y))"
    using graph_abs.has_no_cycle_augment[OF graph_abs_E XY(3,4)] by blast
  then obtain x where x: "x \<in> X" "e = set_of_pair x"
    by blast
  hence "x \<in> X - Y"
    using e(1) by blast
  moreover have "kruskal_indep_abs (insert x Y)"
    using e(2) x XY(1,2) by (auto simp: kruskal_indep_abs_def)
  ultimately show "\<exists>x \<in> X - Y. kruskal_indep_abs (insert x Y)"
    by blast
qed

lemma kruskal_matroid_axioms: "edges.matroid_axioms kruskal_carrier kruskal_indep"
  using edges.matroid_abs_to_impl[OF kruskal_invar edges_finite_sets] kruskal_matroid
  by (simp add: kruskal_carrier_abs kruskal_indep_abs_eq)

text \<open>A basis of the matroid on the edge list corresponds to a spanning forest of the graph.\<close>

lemma basis_iff_spanning_forest:
  assumes "B \<subseteq> set order"
  shows "indep_system.basis (set order) kruskal_indep_abs B \<longleftrightarrow>
    graph_abs.is_spanning_forest E (set_of_pair ` B)"
proof-
  have "indep_system.basis (set order) kruskal_indep_abs B \<longleftrightarrow>
    indep_system.basis E (graph_abs.has_no_cycle E) (set_of_pair ` B)"
  proof
    assume basis: "indep_system.basis (set order) kruskal_indep_abs B"
    show "indep_system.basis E (graph_abs.has_no_cycle E) (set_of_pair ` B)"
    proof (unfold indep_system.basis_def[OF graph_abs.graph_indep_system[OF graph_abs_E]],
        intro conjI ballI)
      show "graph_abs.has_no_cycle E (set_of_pair ` B)"
        using indep_system.basis_indep[OF kruskal_indep_system basis]
        by (simp add: kruskal_indep_abs_def)
    next
      fix e
      assume "e \<in> E - set_of_pair ` B"
      then obtain x where x: "x \<in> set order" "e = set_of_pair x" "x \<notin> B"
        using E_is_order by blast
      hence "\<not> kruskal_indep_abs (insert x B)"
        using basis by (auto simp: indep_system.basis_def[OF kruskal_indep_system])
      thus "\<not> graph_abs.has_no_cycle E (insert e (set_of_pair ` B))"
        using x assms by (auto simp: kruskal_indep_abs_def)
    qed
  next
    assume basis: "indep_system.basis E (graph_abs.has_no_cycle E) (set_of_pair ` B)"
    show "indep_system.basis (set order) kruskal_indep_abs B"
    proof (unfold indep_system.basis_def[OF kruskal_indep_system], intro conjI ballI)
      show "kruskal_indep_abs B"
        using indep_system.basis_indep[OF graph_abs.graph_indep_system[OF graph_abs_E] basis] assms
        by (simp add: kruskal_indep_abs_def)
    next
      fix x
      assume x: "x \<in> set order - B"
      hence "set_of_pair x \<notin> set_of_pair ` B"
        using set_of_pair_inj_order assms by (auto dest: inj_onD)
      moreover have "set_of_pair x \<in> E"
        using x E_is_order by blast
      ultimately have "\<not> graph_abs.has_no_cycle E (insert (set_of_pair x) (set_of_pair ` B))"
        using basis
        by (auto simp: indep_system.basis_def[OF graph_abs.graph_indep_system[OF graph_abs_E]])
      thus "\<not> kruskal_indep_abs (insert x B)"
        by (simp add: kruskal_indep_abs_def)
    qed
  qed
  thus ?thesis
    by (simp add: graph_abs.spanning_forest_iff_basis[OF graph_abs_E])
qed

subsubsection \<open>Correctness of Kruskal's Algorithm\<close>

text \<open>The result of Kruskal's algorithm is the list of chosen edges.\<close>

abbreviation "kruskal_result c \<equiv> fst (result (kruskal c))"

lemma kruskal_result_is_base:
  assumes "\<And>e. e \<in> set order \<Longrightarrow> c e \<ge> 0"
  shows "set (kruskal_result c) =
    to_set (result (kruskal_greedy.BestInGreedy_base (kruskal_greedy.initial_state c order)))"
  using arg_cong[where f = "\<lambda>S. to_set (result S)", OF kruskal_corresp[OF assms]]
  by (simp add: kruskal_greedy.to_ordinary_def to_set_kruskal_remove_wrapper)

theorem kruskal_subset:
  assumes "\<And>e. e \<in> set order \<Longrightarrow> c e \<ge> 0"
  shows "set (kruskal_result c) \<subseteq> set order"
  using kruskal_greedy.BestInGreedy_base_correct_1[OF kruskal_base_axioms sort_desc_axioms
      kruskal_indep_system_axioms kruskal_nonnegative[OF assms] kruskal_valid_order]
  by (simp add: kruskal_result_is_base[OF assms] kruskal_greedy.valid_solution_def
      kruskal_indep_def)

theorem kruskal_spanning_forest:
  assumes "\<And>e. e \<in> set order \<Longrightarrow> c e \<ge> 0"
  shows "graph_abs.is_spanning_forest E (set_of_pair ` set (kruskal_result c))"
proof-
  have "indep_system.basis_in kruskal_indep_abs (set order) (set (kruskal_result c))"
    using kruskal_greedy.BestInGreedy_base_correct_3[OF kruskal_base_axioms sort_desc_axioms
        kruskal_indep_system_axioms kruskal_nonnegative[OF assms] kruskal_valid_order]
    by (simp add: kruskal_result_is_base[OF assms] kruskal_carrier_abs kruskal_indep_abs_eq)
  thus ?thesis
    using basis_iff_spanning_forest[OF kruskal_subset[OF assms]]
      indep_system.basis_iff_basis_in[OF kruskal_indep_system]
    by simp
qed

theorem kruskal_max_weight:
  assumes "\<And>e. e \<in> set order \<Longrightarrow> c e \<ge> 0"
    and "X \<subseteq> set order" "graph_abs.has_no_cycle E (set_of_pair ` X)"
  shows "sum c X \<le> sum c (set (kruskal_result c))"
proof-
  have finite: "finite X"
    using assms(2) finite_subset by blast
  have "kruskal_greedy.valid_solution (edges.from_set X)"
    using assms(2,3) kruskal_carrier_props(1,2)
    by (simp add: kruskal_greedy.valid_solution_def edges.invar_from_set edges.set.set_subseteq
        edges.from_set_correct[OF finite] kruskal_indep_def)
  from kruskal_greedy.BestInGreedy_base_correct_matroid[OF kruskal_base_axioms sort_desc_axioms
      kruskal_matroid_axioms kruskal_nonnegative[OF assms(1)] kruskal_valid_order this]
  show ?thesis
    by (simp add: kruskal_greedy.c_set_def kruskal_result_is_base[OF assms(1)]
        edges.from_set_correct[OF finite])
qed

end

end
