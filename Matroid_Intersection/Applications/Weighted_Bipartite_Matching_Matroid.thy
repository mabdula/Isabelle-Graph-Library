theory Weighted_Bipartite_Matching_Matroid
  imports Max_Bipartite_Matching_Matroid Matroid_Weighted_Intersection_Algorithm
begin

section \<open>Maximum Weight Bipartite Matching via Weighted Matroid Intersection\<close>

text \<open>This file uses the weighted matroid intersection algorithm to obtain an algorithm for
maximum weight bipartite matching, analogously to how @{file "Max_Bipartite_Matching_Matroid.thy"}
solves (unweighted) maximum cardinality bipartite matching. The two matroids
    (\<open>indep1\<close>/\<open>indep2\<close>,
one-sided-matching on each side) are unchanged, so this theory \<^emph>\<open>extends\<close> the unweighted locales
@{locale compute_max_bimatch_by_matroid_spec}/@{locale compute_max_bimatch_by_matroid} rather than
duplicating them: only a weight-map ADT and the
    \<open>weight_Max\<close>/\<open>restrict_to_max\<close>/\<open>reach_set\<close> oracles
are new.\<close>

text \<open>Two small generic RBT facts (distinctness of a preorder key-listing) that are missing from
the base library; needed below to reason about folding an update over a vset.\<close>

lemma Tree2_set_tree_is_fst_of_tree_set_tree:
  "Tree2.set_tree T = fst ` tree.set_tree T"
  by(induction T) (auto simp add: in_image_with_fst_eq)

lemma bst_distinct_preorder: "bst V \<Longrightarrow> distinct (map fst (preorder V))"
  by(induction V rule: preorder.induct)
    (fastforce simp add: Tree2_set_tree_is_fst_of_tree_set_tree[symmetric] in_image_with_fst_eq)+

subsection \<open>The weight-map ADT, layered on top of the unweighted matching ADT\<close>

locale weighted_bimatch_by_matroid_spec =
  compute_max_bimatch_by_matroid_spec
  where Edges = Edges and X = X and Y = Y and to_dbltn = to_dbltn
    and left_vertex = left_vertex and right_vertex = right_vertex and Edges_impl = Edges_impl
  for Edges::"('e::linorder) set" and X::"('v::linorder) set" and Y::"'v set"
    and to_dbltn::"'e \<Rightarrow> 'v set" and left_vertex::"'e \<Rightarrow> 'v" and right_vertex::"'e \<Rightarrow>
      'v"
    and Edges_impl::"('e \<times> color) tree"
  + fixes cost_map :: "(('e \<times> real) \<times> color) tree"
begin

text \<open>The cost map is an RBT tree \<open>'e \<Rightarrow> real\<close>, reusing the very same generic
    \<open>lookup\<close>/\<open>update\<close>/
\<open>M.invar\<close> operations already fixed by @{locale compute_max_bimatch_by_matroid_spec} for the
adjacency maps, just instantiated at a different codomain. \<open>c_lookup\<close> defaults missing keys to
\<open>0\<close>, matching the meaning of \<open>c_zero\<close> being the identically-\<open>0\<close> cost.\<close>

definition "c_lookup cm x = (case lookup cm x of Some v \<Rightarrow> v | None \<Rightarrow> (0::real))"
definition "c_invar cm = M.invar cm"
definition "c_zero = (Leaf :: (('e \<times> real) \<times> color) tree)"

definition "c_shift Rv e cm = fold_rbt (\<lambda> x acc. update x (c_lookup acc x + e) acc) Rv cm"

definition "weight_Max (V::('e \<times> color) tree) cm =
  the (fold_rbt (\<lambda> x acc. Some (case acc of None \<Rightarrow> c_lookup cm x | Some m \<Rightarrow> max m
    (c_lookup cm x))) V None)"

definition "restrict_to_max (V::('e \<times> color) tree) cm =
  fold_rbt (\<lambda> x acc. if c_lookup cm x = weight_Max V cm then vset_insert x acc else acc) V vset_empty"

definition "eps_fold = inner_fold"
definition "eps_fold_red = outer_fold"

lemma c_zero_invar: "c_invar c_zero"
  by (simp add: c_invar_def c_zero_def M.invar_empty[simplified RBT_Set.empty_def])

lemma c_zero_lookup: "c_lookup c_zero = (\<lambda> _. 0)"
  by (auto simp add: c_lookup_def c_zero_def)

lemma c_lookup_update:
  assumes "c_invar t"
  shows "c_lookup (update x v t) = (\<lambda> z. if z = x then v else c_lookup t z)"
  using M.map_update[OF assms[unfolded c_invar_def]]
  by (auto simp add: c_lookup_def fun_eq_iff)

lemma fold_rbt_distinct_spec:
  "vset_inv Rv \<Longrightarrow> \<exists>xs. distinct xs \<and> set xs = t_set Rv \<and> fold_rbt f Rv acc = foldr f
    xs acc"
  by (intro exI[of _ "map fst (preorder Rv)"])
     (auto simp add: vset_inv_def bst_distinct_preorder preorder_witness
       Tree2_set_tree_is_fst_of_tree_set_tree)

lemma c_shift_props:
  assumes "c_invar cm" "vset_inv Rv"
  shows "c_invar (c_shift Rv e cm)"
    "c_lookup (c_shift Rv e cm) = (\<lambda> x. if x \<in> t_set Rv then c_lookup cm x + e else c_lookup cm x)"
proof-
  have "c_invar (foldr (\<lambda> x acc. update x (c_lookup acc x + e) acc) ys cm) \<and>
    c_lookup (foldr (\<lambda> x acc. update x (c_lookup acc x + e) acc) ys cm) =
      (\<lambda> x. if x \<in> set ys then c_lookup cm x + e else c_lookup cm x)" if "distinct ys" for ys
    using assms(1) that
    by (induction ys) (auto simp add: c_lookup_update fun_eq_iff c_invar_def intro: M.invar_update)
  thus "c_invar (c_shift Rv e cm)"
    "c_lookup (c_shift Rv e cm) = (\<lambda> x. if x \<in> t_set Rv then c_lookup cm x + e else c_lookup cm x)"
    using fold_rbt_distinct_spec[of Rv "\<lambda> x acc. update x (c_lookup acc x + e) acc" cm] assms(2)
    by (auto simp add: c_shift_def)
qed

lemma weight_Max_correct:
  assumes "c_invar cm" "vset_inv V" "t_set V \<noteq> {}"
  shows "weight_Max V cm = Max (c_lookup cm ` t_set V)"
proof-
  obtain xs where xs_prop: "distinct xs" "set xs = t_set V"
    "fold_rbt (\<lambda> x acc. Some (case acc of None \<Rightarrow> c_lookup cm x | Some m \<Rightarrow> max m
      (c_lookup cm x))) V None
       = foldr (\<lambda> x acc. Some (case acc of None \<Rightarrow> c_lookup cm x | Some m \<Rightarrow> max m
         (c_lookup cm x))) xs None"
    using fold_rbt_distinct_spec[of V _ None] assms(2)
    by auto
  have xs_ne: "xs \<noteq> []"
    using xs_prop(2) assms(3)
    by force
  have "weight_Max V cm = the (foldr (\<lambda> x acc. Some (case acc of None \<Rightarrow> c_lookup cm x
                    | Some m \<Rightarrow> max m (c_lookup cm x))) xs None)"
    unfolding weight_Max_def
    using xs_prop(3)
    by simp
  also have "... = Max (c_lookup cm ` set xs)"
    using foldr_max_some[of xs "c_lookup cm"] xs_ne
    by simp
  finally show ?thesis
    using xs_prop(2)
    by simp
qed

lemma restrict_to_max_props:
  assumes "c_invar cm" "vset_inv V"
  shows "vset_inv (restrict_to_max V cm)"
    "t_set (restrict_to_max V cm) = {y \<in> t_set V. c_lookup cm y = weight_Max V cm}"
proof-
  have "vset_inv (foldr (\<lambda> x acc. if c_lookup cm x = weight_Max V cm then vset_insert x acc else acc)
                   ys vset_empty) \<and>
     t_set (foldr (\<lambda> x acc. if c_lookup cm x = weight_Max V cm then vset_insert x acc else acc) ys vset_empty)
          = {y \<in> set ys. c_lookup cm y = weight_Max V cm}" for ys
    by (induction ys) (auto simp add: vset_inv_def RBT.inv_insert RBT.bst_insert RBT.set_tree_insert RBT_Set.empty_def)
  thus "vset_inv (restrict_to_max V cm)"
    "t_set (restrict_to_max V cm) = {y \<in> t_set V. c_lookup cm y = weight_Max V cm}"
    using assms(2)
      rbt_fold_spec[of V "\<lambda> x acc. if c_lookup cm x = weight_Max V cm then vset_insert x acc else acc"
        vset_empty]
    by (auto simp add: restrict_to_max_def)
qed

end

locale weighted_bimatch_by_matroid =
  weighted_bimatch_by_matroid_spec
  where Edges = Edges and X = X and Y = Y and to_dbltn = to_dbltn
    and left_vertex = left_vertex and right_vertex = right_vertex and Edges_impl = Edges_impl
  + compute_max_bimatch_by_matroid
  where Edges = Edges and X = X and Y = Y and to_dbltn = to_dbltn
    and left_vertex = left_vertex and right_vertex = right_vertex and Edges_impl = Edges_impl
  for Edges X Y to_dbltn left_vertex right_vertex Edges_impl
  + assumes cost_map_inv: "M.invar cost_map"
begin

end

subsection \<open>The \<open>reach_set\<close> oracle, obtained from the existing BFS\<close>

text \<open>\<open>reach_set Src G\<close> computes the set of vertices reachable from \<open>Src\<close> in
    \<open>G\<close> (including
\<open>Src\<close> itself), by running the BFS already interpreted concretely
(via \<open>Compute_Path.thy\<close>). BFS's precondition needs every source vertex to already be a
vertex of the graph (\<open>t_set Src \<subseteq> dVs G\<close>); to satisfy this unconditionally we augment the graph
with a self-loop at every source vertex before running BFS. The lemma @{thm reachable_selfloops} shows that this
augmentation does not change which vertices are reachable.\<close>

text \<open>\<open>reach_set_graph\<close> augments \<open>G\<close> with a self-loop at every source vertex, so that
    BFS's
precondition \<open>t_set Src \<subseteq> dVs G\<close> holds unconditionally.\<close>

definition "reach_set_graph Src G = fold_rbt (\<lambda> s acc. G.add_edge acc s s) Src G"

lemma reach_set_graph_props:
  assumes "G.graph_inv G" "vset_inv Src"
  shows "G.graph_inv (reach_set_graph Src G)"
    "G.digraph_abs (reach_set_graph Src G) = G.digraph_abs G \<union> {(s,s) |s. s \<in> t_set Src}"
proof-
  have "G.graph_inv (foldr (\<lambda> s acc. G.add_edge acc s s) ys G) \<and>
      G.digraph_abs (foldr (\<lambda> s acc. G.add_edge acc s s) ys G) = G.digraph_abs G \<union> {(s,s) |s. s \<in>
        set ys}"
    for ys
    using assms(1)
    by (induction ys) auto
  thus "G.graph_inv (reach_set_graph Src G)"
    "G.digraph_abs (reach_set_graph Src G) = G.digraph_abs G \<union> {(s,s) |s. s \<in> t_set Src}"
    using rbt_fold_spec[of Src "\<lambda> s acc. G.add_edge acc s s" G] assms(2)
    by (auto simp add: reach_set_graph_def)
qed

lemma finite_vsets_unconditional: "dfs.Graph.finite_vsets Gr"
  by (auto simp add: dfs.Graph.finite_vsets_def)

lemma lookup_dom_subs_set_tree: "{v. lookup Gr v \<noteq> None} \<subseteq> fst ` Tree2.set_tree Gr"
  by (induction Gr rule: tree2_induct) (auto simp: lookup.simps image_Un subset_iff split: if_splits)

lemma finite_graph_of_graph_inv: "dfs.Graph.finite_graph Gr"
  unfolding dfs.Graph.finite_graph_def
  by (rule finite_subset[OF lookup_dom_subs_set_tree]) (auto intro: finite_set_tree)

lemma reach_set_graph_finite_neighb:
  assumes "G.graph_inv G" "vset_inv Src"
  shows "finite (Pair_Graph.neighbourhood (G.digraph_abs (reach_set_graph Src G)) u)"
  using G.finite_neighbourhoods[of "reach_set_graph Src G" u, OF finite_vsets_unconditional]
    G.neighbourhood_abs[of "reach_set_graph Src G" u, OF reach_set_graph_props(1)[OF assms]]
  by simp

lemma reach_set_graph_srcs_in_dVs:
  assumes "G.graph_inv G" "vset_inv Src"
  shows "t_set Src \<subseteq> dVs (G.digraph_abs (reach_set_graph Src G))"
  using reach_set_graph_props(2)[OF assms]
  by (auto simp add: dVs_def)

lemma reach_set_bfs_axiom:
  assumes "G.graph_inv G" "vset_inv Src" "t_set Src \<noteq> {}"
  shows "BFS.BFS_axiom isin t_set M.invar \<langle>\<rangle> vset_inv lookup Src (reach_set_graph Src G)"
  unfolding bfs.BFS_axiom_def
  by (intro conjI allI reach_set_graph_props(1) finite_graph_of_graph_inv finite_vsets_unconditional
      reach_set_graph_srcs_in_dVs reach_set_graph_finite_neighb assms)

lemma bfs_current_empty:
  assumes "bfs.BFS_dom G state"
  shows "current (bfs.BFS G state) = vset_empty"
  using assms
  by (induction rule: bfs.BFS.pinduct) (auto simp add: bfs.BFS.psimps bfs.BFS_call_1_conds_def RBT_Set.empty_def)

text \<open>The BFS on the self-loop-augmented graph visits exactly the vertices reachable from a source
(the self-loops are stripped via @{thm [source] reachable_selfloops}).\<close>

lemma reach_set_correct_nonempty:
  assumes "G.graph_inv G" "vset_inv Src" "t_set Src \<noteq> {}"
  shows "t_set (visited (bfs.BFS (reach_set_graph Src G) (bfs_initial_state Src)))
          = {v. \<exists>u\<in>t_set Src. u = v \<or> (\<exists>p. vwalk_bet (G.digraph_abs G) u p v)}"
proof-
  note ax = reach_set_bfs_axiom[OF assms]
  note props = reach_set_graph_props(2)[OF assms(1,2)] reach_set_graph_srcs_in_dVs[OF assms(1,2)]
  show ?thesis
  proof(intro equalityI subsetI)
    fix x
    assume "x \<in> t_set (visited (bfs.BFS (reach_set_graph Src G) (bfs_initial_state Src)))"
    hence "distance_set (G.digraph_abs (reach_set_graph Src G)) (t_set Src) x < \<infinity>"
      using bfs.invar_current_reachable_props[OF ax bfs.invar_current_reachable_holds[OF ax
          bfs.initial_state_props(4,1,2,10)[OF ax]]]
      by auto
    then obtain s where "s \<in> t_set Src"
      "Pair_Graph.reachable (G.digraph_abs G \<union> {(s,s) |s. s \<in> t_set Src}) s x"
      using infty_dist_is_unreachable[of "G.digraph_abs (reach_set_graph Src G)" "t_set Src" x] props
      by auto
    thus "x \<in> {v. \<exists>u\<in>t_set Src. u = v \<or> (\<exists>p. vwalk_bet (G.digraph_abs G) u p v)}"
      using reachable_selfloops[of "G.digraph_abs G" "t_set Src" s x] reachable_vwalk_bet_iff[of "G.digraph_abs G" s x]
      by blast
  next
    fix x
    assume "x \<in> {v. \<exists>u\<in>t_set Src. u = v \<or> (\<exists>p. vwalk_bet (G.digraph_abs G) u p v)}"
    then obtain u where "u \<in> t_set Src" "u = x \<or> (\<exists>p. vwalk_bet (G.digraph_abs G) u p x)"
      by auto
    moreover hence "\<exists>p. vwalk_bet (G.digraph_abs (reach_set_graph Src G)) u p x"
      using props
      by (auto intro: vwalk_bet_subset[where G' = "G.digraph_abs G \<union> {(s, s) |s. s \<in> t_set Src}"])
    ultimately show "x \<in> t_set (visited (bfs.BFS (reach_set_graph Src G) (bfs_initial_state Src)))"
      using bfs.BFS_correct_1[OF ax, of u x]
      by blast
  qed
qed

text \<open>Finally, \<open>reach_set\<close> itself: falls back to the empty vset when \<open>Src\<close> is empty
    (BFS's own
precondition needs a nonempty source set), otherwise runs BFS on the self-loop-augmented graph.\<close>

definition "reach_set Src G =
  (if Src = vset_empty then vset_empty else visited (bfs_impl (reach_set_graph Src G) (bfs_initial_state Src)))"

lemma reach_set_final:
  assumes "G.graph_inv G" "vset_inv Src"
  shows "vset_inv (reach_set Src G)"
    "t_set (reach_set Src G) =
       {v. \<exists>u\<in>t_set Src. u = v \<or> (\<exists>p. vwalk_bet (G.digraph_abs G) u p v)}"
proof-
  have "vset_inv (reach_set Src G) \<and>
    t_set (reach_set Src G) =
      {v. \<exists>u\<in>t_set Src. u = v \<or> (\<exists>p. vwalk_bet (G.digraph_abs G) u p v)}"
  proof(cases "Src = vset_empty")
    case False
    hence nonempty: "t_set Src \<noteq> {}"
      using assms(2)
      by (auto simp add: vset_inv_def RBT_Set.empty_def)
    note ax = reach_set_bfs_axiom[OF assms this]
    show ?thesis
      using bfs.invar_1_holds[OF ax bfs.initial_state_props(4,1)[OF ax]] reach_set_correct_nonempty[OF assms]
        bfs.BFS_impl_same[OF bfs.initial_state_props(4)[OF ax]] False nonempty
      by (simp add: reach_set_def bfs.invar_1_def)
  qed (simp add: reach_set_def vset_inv_def RBT_Set.empty_def)
  thus "vset_inv (reach_set Src G)"
    "t_set (reach_set Src G) =
       {v. \<exists>u\<in>t_set Src. u = v \<or> (\<exists>p. vwalk_bet (G.digraph_abs G) u p v)}"
    by auto
qed

subsection \<open>Instantiating a concrete bipartite matching instance\<close>

text \<open>As in @{file "Max_Bipartite_Matching_Matroid.thy"}, we fix a concrete bipartite edge set and
build the weighted matroid intersection instance on top. The local definitions are named with a
\<open>W\<close>-prefix to avoid colliding with the globally-exported
    \<open>Edges\<close>/\<open>X\<close>/\<open>Y\<close>/\<open>to_dbltn\<close> constants of
the very same bottom context in @{file "Max_Bipartite_Matching_Matroid.thy"} (both files import
\<open>Matroid_Intersection_Algorithm.thy\<close> into the same name space).\<close>

context
  fixes left_vertex::"'e::linorder \<Rightarrow> 'v::linorder"
    and right_vertex::"'e \<Rightarrow> 'v"
    and s::'e
    and t::'e
    and Edges_impl::"('e \<times> color) tree"
    and cost_map::"(('e \<times> real) \<times> color) tree"
  assumes bipart:"\<not> (\<exists> e d. e \<in> t_set Edges_impl \<and> d \<in> t_set Edges_impl \<and>
                                 left_vertex e = right_vertex d)"
    and s_t: "s \<notin> t_set Edges_impl" "t \<notin> t_set Edges_impl" "s \<noteq> t"
    and Edges_impl_inv: "vset_inv Edges_impl"
    and left_not_right: "\<And> e. e \<in> WEdges \<Longrightarrow> left_vertex e \<noteq> right_vertex e "
    and injectivity:
         "\<And> e e'. \<lbrakk>e \<in> WEdges; e' \<in> WEdges; left_vertex e = left_vertex e';
                   right_vertex e= right_vertex e'\<rbrakk>
                   \<Longrightarrow>e = e'"
    and cost_map_inv: "M.invar cost_map"
begin

definition "Wto_dbltn e = {left_vertex e, right_vertex e}"
definition "WEdges = t_set Edges_impl"
definition "WX = left_vertex ` WEdges"
definition "WY = right_vertex ` WEdges"

lemma Edges_impl_is: "t_set Edges_impl = WEdges"
  by (simp add: WEdges_def)

lemma left_not_right': "e \<in> WEdges \<Longrightarrow> \<exists>u v. {left_vertex e, right_vertex e} = {u, v} \<and>
    u \<noteq> v"
  using bipart
  by (auto simp add: WEdges_def)

lemma Wbipartite: "bipartite (Wto_dbltn ` WEdges) WX WY"
  using bipart
  by (auto simp add: WEdges_def WX_def WY_def bipartite_def Wto_dbltn_def)

lemma Wto_dbltn_inj: "inj_on Wto_dbltn WEdges"
proof(rule inj_onI, goal_cases)
  case (1 x y)
  then show ?case
    using injectivity[OF 1(1,2)] bipart
    by (force simp add: Wto_dbltn_def WEdges_def)
qed

lemma Wcorrect_side: "e \<in> WEdges \<Longrightarrow> left_vertex e \<in> WX"
  "e \<in> WEdges \<Longrightarrow> right_vertex e \<in> WY"
  by (auto simp add: WEdges_def WX_def WY_def)

lemma Wfinite_Edges: "finite WEdges"
  by (simp add: WEdges_def)

interpretation matching_as_matroid_intersection: max_bimatch_by_matroid
  where to_dbltn=Wto_dbltn and Edges=WEdges and X = WX and Y = WY and left_vertex = left_vertex
    and right_vertex=right_vertex
  using Wbipartite bipart
  by(auto intro!: max_bimatch_by_matroid.intro
      left_not_right' Wbipartite Wcorrect_side Wfinite_Edges
      simp add: Wto_dbltn_def Wto_dbltn_inj Edges_impl_is)

interpretation matching_as_matroid_intersection_proofs: compute_max_bimatch_by_matroid
  where to_dbltn=Wto_dbltn and Edges=WEdges and X = WX and Y = WY and left_vertex = left_vertex
    and right_vertex=right_vertex
  by(auto simp add: compute_max_bimatch_by_matroid_def Edges_impl_inv Edges_impl_is
      matching_as_matroid_intersection.max_bimatch_by_matroid_axioms
      intro!: compute_max_bimatch_by_matroid_axioms.intro)

definition "Windep1 = matching_as_matroid_intersection.indep1"
definition "Windep2 = matching_as_matroid_intersection.indep2"

lemma Wdouble_matroid: "double_matroid WEdges Windep1 Windep2"
  by (auto intro: matching_as_matroid_intersection.double_matroid_concrete
      simp add: Windep1_def Windep2_def)

lemma Wsame_invar: "invar_matching left_vertex right_vertex =
            matching_as_matroid_intersection_proofs.invar_matching"
proof(rule ext)
  fix M
  show "invar_matching left_vertex right_vertex M = matching_as_matroid_intersection_proofs.invar_matching M"
    by (cases M) (simp add: matching_basic_operations.emap_lft_inv_def matching_basic_operations.emap_rht_inv_def)
qed

interpretation weighted_matching_as_matroid_intersection: weighted_bimatch_by_matroid
  where to_dbltn=Wto_dbltn and Edges=WEdges and X = WX and Y = WY and left_vertex = left_vertex
    and right_vertex=right_vertex and Edges_impl = Edges_impl and cost_map = cost_map
  by (auto simp add: weighted_bimatch_by_matroid_def compute_max_bimatch_by_matroid_def
      Edges_impl_inv Edges_impl_is cost_map_inv
      matching_as_matroid_intersection.max_bimatch_by_matroid_axioms
      intro!: compute_max_bimatch_by_matroid_axioms.intro weighted_bimatch_by_matroid_axioms.intro)

lemma Wset_matching_eq: "set_matching M = matching_as_matroid_intersection_proofs.set_matching M"
  by (simp add: set_matching_def matching_as_matroid_intersection_proofs.set_matching_def)

lemma Wto_set_red_eq: "to_set_red M = matching_as_matroid_intersection_proofs.to_set_red M"
  by (simp add: to_set_red_def matching_as_matroid_intersection_proofs.to_set_red_def)

lemma Wcircuit1_eq: "circuit1 left_vertex y M = matching_as_matroid_intersection_proofs.circuit1 y M"
  by (cases M) (simp add: circuit1_def matching_as_matroid_intersection_proofs.circuit1.simps)

lemma Wcircuit2_eq: "circuit2 right_vertex y M = matching_as_matroid_intersection_proofs.circuit2 y M"
  by (cases M) (simp add: circuit2_def matching_as_matroid_intersection_proofs.circuit2.simps)

subsection \<open>Assembling the weighted matroid intersection interpretation\<close>

interpretation weighted_matching_algorithm: weighted_intersection
  where empty = RBT_Set.empty and delete= RBT_Map.delete and lookup=lookup and insert=insert_rbt
    and isin=isin and vset=t_set and sel=sel and update=update and adjmap_inv =M.invar
    and vset_empty=Leaf and vset_delete= RBT.delete and vset_inv=vset_inv and to_set=set_matching
    and set_invar="invar_matching left_vertex right_vertex" and set_empty=empty_matching
    and inner_fold=inner_fold and outer_fold=outer_fold and inner_fold_circuit=outer_fold
    and set_insert="insert_matching left_vertex right_vertex"
    and set_delete="delete_matching left_vertex right_vertex"
    and weak_orcl1="weak_orcl1 left_vertex" and weak_orcl2="weak_orcl2 right_vertex"
    and circuit1="circuit1 left_vertex" and circuit2="circuit2 right_vertex"
    and find_path="\<lambda> S T G. find_path s t G S T " and complement="complement_matching Edges_impl"
    and carrier=WEdges and indep1=Windep1 and indep2=Windep2
    and to_set_red=to_set_red and set_invar_red=set_invar_red
    and c_lookup = weighted_matching_as_matroid_intersection.c_lookup
    and c_invar = weighted_matching_as_matroid_intersection.c_invar
    and c_shift = weighted_matching_as_matroid_intersection.c_shift
    and c_zero = weighted_matching_as_matroid_intersection.c_zero
    and weight_Max = weighted_matching_as_matroid_intersection.weight_Max
    and restrict_to_max = weighted_matching_as_matroid_intersection.restrict_to_max
    and reach_set = reach_set
    and eps_fold = weighted_matching_as_matroid_intersection.eps_fold
    and eps_fold_red = weighted_matching_as_matroid_intersection.eps_fold_red
proof(rule weighted_intersection.intro, goal_cases)
  case 1
  then show ?case
    by unfold_locales
next
  case 2
  then show ?case
    by (auto intro: Wdouble_matroid)
next
  case 3
  then show ?case
  proof(rule weighted_intersection_axioms.intro, goal_cases)
    case (1 S x)
    then show ?case
      by (simp add: matching_basic_operations.set_matching_insert(1))
  next
    case (2 S x)
    then show ?case
      by (simp add: matching_basic_operations.set_matching_insert(2))
  next
    case (3 S x)
    then show ?case
      by (simp add: matching_basic_operations.set_matching_delete(1))
  next
    case (4 S x)
    then show ?case
      by (simp add: matching_basic_operations.set_matching_delete(2))
  next
    case 5
    then show ?case
      by (simp add: matching_basic_operations.set_matching_empty(1))
  next
    case 6
    then show ?case
      by (simp add: matching_basic_operations.set_matching_empty(2))
  next
    case (7 X x)
    then show ?case
      by (auto simp add: matching_as_matroid_intersection_proofs.weak_orcl1_correct
          Wsame_invar Windep1_def weak_orcl1_def set_matching_def)
  next
    case (8 X x)
    then show ?case
      by (auto simp add: matching_as_matroid_intersection_proofs.weak_orcl2_correct
          Wsame_invar Windep2_def weak_orcl2_def set_matching_def)
  next
    case (9 X f G)
    then show ?case
      by (auto intro: matching_as_matroid_intersection_proofs.inner_fold_spec
          simp add: Wsame_invar Windep2_def weak_orcl2_def set_matching_def inner_fold_def)
  next
    case (10 X f G)
    then show ?case
      by(auto intro: matching_as_matroid_intersection_proofs.outer_fold_spec
          simp add: Wsame_invar Windep2_def weak_orcl2_def set_matching_def
          outer_fold_def set_invar_red_def to_set_red_def)
  next
    case (11 X f trip)
    then show ?case
      by(auto intro: matching_as_matroid_intersection_proofs.outer_fold_spec
          simp add: Wsame_invar Windep2_def weak_orcl2_def set_matching_def
          outer_fold_def set_invar_red_def to_set_red_def)
  next
    case (12 G S T)
    then show ?case
      unfolding G_and_dfs_graph(1)
      using compute_path.find_path1[of s WEdges t G S T]
      using WEdges_def s_t(1,2,3)
      by (auto intro: simp add: G_and_dfs_graph(1,2))
  next
    case (13 G S T p)
    then show ?case
      unfolding G_and_dfs_graph(1)
      using compute_path.find_path_weak(2)[of s WEdges t G S T p] s_t(1,2,3)
      by (auto intro: simp add: G_and_dfs_graph(1,2) WEdges_def)
  next
    case (14 S)
    then show ?case
      by (auto intro: matching_as_matroid_intersection_proofs.set_invar_red_of_complement
          simp add: complement_matching_def invar_matching_def set_invar_red_def
          matching_as_matroid_intersection_proofs.complement_is set_matching_def to_set_red_def)
  next
    case (15 S)
    then show ?case
      by (auto intro: matching_as_matroid_intersection_proofs.set_invar_red_of_complement
          simp add: complement_matching_def invar_matching_def set_invar_red_def
          matching_as_matroid_intersection_proofs.complement_is set_matching_def to_set_red_def
          WEdges_def)
  next
    case (16 X y)
    then show ?case
      by (simp add: Wcircuit1_eq Wto_set_red_eq Windep1_def Wset_matching_eq Wsame_invar
          matching_as_matroid_intersection_proofs.circuit1_correct[of X y,
            unfolded insert_is_Un[symmetric]])
  next
    case (17 X y)
    then show ?case
      by (auto intro: matching_as_matroid_intersection_proofs.circuit1_invar[unfolded
            matching_as_matroid_intersection_proofs.set_invar_red_def]
          simp add: Wcircuit1_eq Wsame_invar set_invar_red_def
          matching_as_matroid_intersection_proofs.set_invar_red_def)
  next
    case (18 X y)
    then show ?case
      by (simp add: Wcircuit2_eq Wto_set_red_eq Windep2_def Wset_matching_eq Wsame_invar
          matching_as_matroid_intersection_proofs.circuit2_correct[of X y,
            unfolded insert_is_Un[symmetric]])
  next
    case (19 X y)
    then show ?case
      by (auto intro: matching_as_matroid_intersection_proofs.circuit2_invar[unfolded
            matching_as_matroid_intersection_proofs.set_invar_red_def]
          simp add: Wcircuit2_eq Wsame_invar set_invar_red_def
          matching_as_matroid_intersection_proofs.set_invar_red_def)
  next
    case 20
    then show ?case
      by (rule weighted_matching_as_matroid_intersection.c_zero_invar)
  next
    case 21
    then show ?case
      by (rule weighted_matching_as_matroid_intersection.c_zero_lookup)
  next
    case (22 R e c)
    then show ?case
      by (auto intro: weighted_matching_as_matroid_intersection.c_shift_props(1))
  next
    case (23 R e c)
    then show ?case
      by (auto intro: weighted_matching_as_matroid_intersection.c_shift_props(2))
  next
    case (24 V c)
    then show ?case
      by (auto intro: weighted_matching_as_matroid_intersection.weight_Max_correct)
  next
    case (25 V c)
    then show ?case
      by (auto intro: weighted_matching_as_matroid_intersection.restrict_to_max_props(1))
  next
    case (26 V c)
    then show ?case
      by (cases "t_set V = {}")
         (auto simp add: weighted_matching_as_matroid_intersection.restrict_to_max_props(2)
             weighted_matching_as_matroid_intersection.weight_Max_correct)
  next
    case (27 Src G)
    then show ?case
      by (rule reach_set_final(1))
  next
    case (28 Src G)
    then show ?case
      by (rule reach_set_final(2))
  next
    case (29 X f a)
    then show ?case
      by (auto intro: matching_as_matroid_intersection_proofs.inner_fold_spec
          simp add: Wsame_invar set_matching_def
          weighted_matching_as_matroid_intersection.eps_fold_def inner_fold_def)
  next
    case (30 X f a)
    then show ?case
      by (auto intro: matching_as_matroid_intersection_proofs.outer_fold_spec
          simp add: set_invar_red_def to_set_red_def
          weighted_matching_as_matroid_intersection.eps_fold_red_def outer_fold_def)
  qed
qed

subsection \<open>The final theorem: the algorithm computes a maximum weight matching\<close>

text \<open>The weighted matroid intersection algorithm's output is transported from the abstract edge
type \<open>'e\<close> to genuine vertex-doubleton edges via \<open>Wto_dbltn\<close>, mirroring how
@{file "Max_Bipartite_Matching_Matroid.thy"}'s \<open>same_card_dbltn\<close> transports cardinality; here we
transport the sum of costs instead.\<close>

definition "Wweight e = weighted_matching_as_matroid_intersection.c_lookup cost_map (the_inv_into WEdges Wto_dbltn e)"

lemma Wsum_dbltn:
  assumes "Es \<subseteq> WEdges"
  shows "sum Wweight (Wto_dbltn ` Es) = sum (weighted_matching_as_matroid_intersection.c_lookup cost_map) Es"
  unfolding Wweight_def
  using assms Wto_dbltn_inj
  by (subst sum.reindex) (auto simp add: inj_on_def the_inv_into_f_f dest: subsetD intro!: sum.cong)

lemma weighted_solution:
  "max_weight_matching (Wto_dbltn ` WEdges) Wweight
     (Wto_dbltn ` (set_matching (wsol (weighted_matching_algorithm.weighted_matroid_intersection
                      (weighted_matching_algorithm.weighted_initial_state cost_map)))))"
proof-
  define sol where "sol = set_matching (wsol (weighted_matching_algorithm.weighted_matroid_intersection
                      (weighted_matching_algorithm.weighted_initial_state cost_map)))"
  have "weighted_double_matroid.is_opt Windep1 Windep2
          (weighted_matching_as_matroid_intersection.c_lookup cost_map) sol"
    using weighted_matching_algorithm.weighted_matroid_intersection_correct cost_map_inv
    by (simp add: sol_def weighted_matching_as_matroid_intersection.c_invar_def)
  hence opt: "Windep1 sol" "Windep2 sol"
    "\<lbrakk>Windep1 Y; Windep2 Y\<rbrakk> \<Longrightarrow>
       sum (weighted_matching_as_matroid_intersection.c_lookup cost_map) Y
         \<le> sum (weighted_matching_as_matroid_intersection.c_lookup cost_map) sol" for Y
    using Wdouble_matroid
    by (auto simp add: weighted_double_matroid.is_opt_def weighted_double_matroid_def)
  moreover have "sum Wweight M \<le> sum Wweight (Wto_dbltn ` sol)" if "graph_matching (Wto_dbltn ` WEdges) M" for M
  proof-
    from that obtain M' where "M = Wto_dbltn ` M'" "Windep1 M'" "Windep2 M'"
      using matching_as_matroid_intersection.graph_matching_to_double_indep[of M]
      by (auto simp add: Windep1_def Windep2_def)
    thus ?thesis
      using opt Wsum_dbltn
      by (auto simp add: Windep1_def matching_as_matroid_intersection.indep1_def)
  qed
  ultimately show ?thesis
    using matching_as_matroid_intersection.double_indep_to_graph_matching[of sol]
    by (auto simp add: sol_def[symmetric] max_weight_matching_def Windep1_def Windep2_def)
qed

end

end

