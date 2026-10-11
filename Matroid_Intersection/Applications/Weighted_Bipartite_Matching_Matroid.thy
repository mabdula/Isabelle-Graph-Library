theory Weighted_Bipartite_Matching_Matroid
  imports Max_Bipartite_Matching_Matroid Matroid_Weighted_Intersection_Algorithm
begin

section \<open>Maximum Weight Bipartite Matching via Weighted Matroid Intersection\<close>

text \<open>This file uses the weighted matroid intersection algorithm to obtain an algorithm for
maximum weight bipartite matching, analogously to how @{file "Max_Bipartite_Matching_Matroid.thy"}
solves (unweighted) maximum cardinality bipartite matching. The two matroids (\<open>indep1\<close>/\<open>indep2\<close>,
one-sided-matching on each side) are unchanged, so this theory \<^emph>\<open>extends\<close> the unweighted locales
@{locale compute_max_bimatch_by_matroid_spec}/@{locale compute_max_bimatch_by_matroid} rather than
duplicating them: only a weight-map ADT and the \<open>weight_Max\<close>/\<open>restrict_to_max\<close>/\<open>reach_set\<close> oracles
are new.\<close>

text \<open>Two small generic RBT facts (distinctness of a preorder key-listing) that are missing from
the base library; needed below to reason about folding an update over a vset.\<close>

lemma in_image_with_fst_eq: "a \<in> fst ` A \<longleftrightarrow> (\<exists> b. (a, b) \<in> A)"
  by force

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
    and to_dbltn::"'e \<Rightarrow> 'v set" and left_vertex::"'e \<Rightarrow> 'v" and right_vertex::"'e \<Rightarrow> 'v"
    and Edges_impl::"('e \<times> color) tree"
  + fixes cost_map :: "(('e \<times> real) \<times> color) tree"
begin

text \<open>The cost map is an RBT tree \<open>'e \<Rightarrow> real\<close>, reusing the very same generic \<open>lookup\<close>/\<open>update\<close>/
\<open>M.invar\<close> operations already fixed by @{locale compute_max_bimatch_by_matroid_spec} for the
adjacency maps, just instantiated at a different codomain. \<open>c_lookup\<close> defaults missing keys to
\<open>0\<close>, matching the meaning of \<open>c_zero\<close> being the identically-\<open>0\<close> cost.\<close>

definition "c_lookup cm x = (case lookup cm x of Some v \<Rightarrow> v | None \<Rightarrow> (0::real))"
definition "c_invar cm = M.invar cm"
definition "c_zero = (Leaf :: (('e \<times> real) \<times> color) tree)"

definition "c_shift Rv e cm = fold_rbt (\<lambda> x acc. update x (c_lookup acc x + e) acc) Rv cm"

definition "weight_Max (V::('e \<times> color) tree) cm =
  the (fold_rbt (\<lambda> x acc. Some (case acc of None \<Rightarrow> c_lookup cm x | Some m \<Rightarrow> max m (c_lookup cm x))) V None)"

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
  "vset_inv Rv \<Longrightarrow> \<exists>xs. distinct xs \<and> set xs = t_set Rv \<and> fold_rbt f Rv acc = foldr f xs acc"
  by (intro exI[of _ "map fst (preorder Rv)"])
     (auto simp add: vset_inv_def bst_distinct_preorder preorder_witness
       Tree2_set_tree_is_fst_of_tree_set_tree)

lemma c_shift_invar:
  assumes "c_invar cm" "vset_inv Rv"
  shows "c_invar (c_shift Rv e cm)"
proof-
  obtain xs where xs_prop: "distinct xs" "set xs = t_set Rv"
    "c_shift Rv e cm = foldr (\<lambda> x acc. update x (c_lookup acc x + e) acc) xs cm"
    using fold_rbt_distinct_spec[where f = "\<lambda> x acc. update x (c_lookup acc x + e) acc" and acc = cm,
        OF assms(2)]
    by (auto simp add: c_shift_def)
  show ?thesis
    using assms(1) unfolding xs_prop(3) c_invar_def
    by (induction xs) (auto intro: M.invar_update)
qed

lemma c_shift_lookup:
  assumes "c_invar cm" "vset_inv Rv"
  shows "c_lookup (c_shift Rv e cm) = (\<lambda> x. if x \<in> t_set Rv then c_lookup cm x + e else c_lookup cm x)"
proof-
  obtain xs where xs_prop: "distinct xs" "set xs = t_set Rv"
    "c_shift Rv e cm = foldr (\<lambda> x acc. update x (c_lookup acc x + e) acc) xs cm"
    using fold_rbt_distinct_spec[where f = "\<lambda> x acc. update x (c_lookup acc x + e) acc" and acc = cm,
        OF assms(2)]
    by (auto simp add: c_shift_def)
  have inv_pres: "c_invar (foldr (\<lambda> x acc. update x (c_lookup acc x + e) acc) ys cm)"
    if "c_invar cm" for ys
    using that unfolding c_invar_def by (induction ys) (auto intro: M.invar_update)
  have "\<And> y. distinct ys \<Longrightarrow>
    c_lookup (foldr (\<lambda> x acc. update x (c_lookup acc x + e) acc) ys cm) y
      = (if y \<in> set ys then c_lookup cm y + e else c_lookup cm y)" for ys
  proof(induction ys)
    case Nil
    then show ?case by simp
  next
    case (Cons x ys)
    have invys: "c_invar (foldr (\<lambda> x acc. update x (c_lookup acc x + e) acc) ys cm)"
      by (rule inv_pres[OF assms(1)])
    show ?case
    proof(cases "y = x")
      case True
      then show ?thesis
        using Cons(2) Cons.IH[OF distinct.simps(2)[THEN iffD1, OF Cons(2), THEN conjunct2]]
        by (simp add: c_lookup_update[OF invys])
    next
      case False
      then show ?thesis
        using Cons(2) Cons.IH[OF distinct.simps(2)[THEN iffD1, OF Cons(2), THEN conjunct2]]
        by (simp add: c_lookup_update[OF invys])
    qed
  qed
  thus ?thesis
    using xs_prop(1,2) unfolding xs_prop(3) by auto
qed

lemma foldr_max_some:
  "xs \<noteq> [] \<Longrightarrow>
   foldr (\<lambda> x acc. Some (case acc of None \<Rightarrow> f x | Some m \<Rightarrow> max m (f x))) xs None
     = Some (Max (f ` set xs))"
proof(induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof(cases "xs = []")
    case True
    then show ?thesis by simp
  next
    case False
    then show ?thesis
      using Cons.IH[OF False]
      by (simp add: Max_insert image_insert max.commute)
  qed
qed

lemma weight_Max_correct:
  assumes "c_invar cm" "vset_inv V" "t_set V \<noteq> {}"
  shows "weight_Max V cm = Max (c_lookup cm ` t_set V)"
proof-
  obtain xs where xs_prop: "distinct xs" "set xs = t_set V"
    "fold_rbt (\<lambda> x acc. Some (case acc of None \<Rightarrow> c_lookup cm x | Some m \<Rightarrow> max m (c_lookup cm x))) V None
       = foldr (\<lambda> x acc. Some (case acc of None \<Rightarrow> c_lookup cm x | Some m \<Rightarrow> max m (c_lookup cm x))) xs None"
    using fold_rbt_distinct_spec[OF assms(2), of _ None] by auto
  have xs_ne: "xs \<noteq> []" using xs_prop(2) assms(3) by force
  have "weight_Max V cm = the (foldr (\<lambda> x acc. Some (case acc of None \<Rightarrow> c_lookup cm x
                    | Some m \<Rightarrow> max m (c_lookup cm x))) xs None)"
    unfolding weight_Max_def using xs_prop(3) by simp
  also have "... = Max (c_lookup cm ` set xs)"
    using foldr_max_some[OF xs_ne, of "c_lookup cm"] by simp
  finally show ?thesis
    using xs_prop(2) by simp
qed

lemma restrict_to_max_invar:
  assumes "c_invar cm" "vset_inv V"
  shows "vset_inv (restrict_to_max V cm)"
proof-
  obtain xs where xs_prop: "set xs = t_set V"
    "fold_rbt (\<lambda> x acc. if c_lookup cm x = weight_Max V cm then vset_insert x acc else acc) V vset_empty
       = foldr (\<lambda> x acc. if c_lookup cm x = weight_Max V cm then vset_insert x acc else acc) xs vset_empty"
    using rbt_fold_spec[OF assms(2), of _ vset_empty] by auto
  have "vset_inv (foldr (\<lambda> x acc. if c_lookup cm x = weight_Max V cm then vset_insert x acc else acc)
                   ys vset_empty)" for ys
    by (induction ys) (auto simp add: vset_inv_def RBT.inv_insert RBT.bst_insert RBT_Set.empty_def)
  thus ?thesis
    unfolding restrict_to_max_def xs_prop(2) .
qed

lemma restrict_to_max_set:
  assumes "c_invar cm" "vset_inv V"
  shows "t_set (restrict_to_max V cm) = {y \<in> t_set V. c_lookup cm y = weight_Max V cm}"
proof-
  obtain xs where xs_prop: "set xs = t_set V"
    "fold_rbt (\<lambda> x acc. if c_lookup cm x = weight_Max V cm then vset_insert x acc else acc) V vset_empty
       = foldr (\<lambda> x acc. if c_lookup cm x = weight_Max V cm then vset_insert x acc else acc) xs vset_empty"
    using rbt_fold_spec[OF assms(2), of "\<lambda> x acc. if c_lookup cm x = weight_Max V cm
            then vset_insert x acc else acc" vset_empty]
    by auto
  have combined: "vset_inv (foldr (\<lambda> x acc. if c_lookup cm x = weight_Max V cm then vset_insert x acc else acc)
                   ys vset_empty) \<and>
     t_set (foldr (\<lambda> x acc. if c_lookup cm x = weight_Max V cm then vset_insert x acc else acc)
                   ys vset_empty)
          = {y \<in> set ys. c_lookup cm y = weight_Max V cm}" for ys
    by (induction ys) (auto simp add: vset_inv_def RBT.inv_insert RBT.bst_insert
        RBT.set_tree_insert RBT_Set.empty_def)
  thus ?thesis
    unfolding restrict_to_max_def xs_prop(2) xs_prop(1)[symmetric]
    using combined[of xs, THEN conjunct2] by simp
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

text \<open>\<open>reach_set Src G\<close> computes the set of vertices reachable from \<open>Src\<close> in \<open>G\<close> (including
\<open>Src\<close> itself), by running the BFS already interpreted concretely in 
(via \<open>Compute_Path.thy\<close>). BFS's precondition needs every source vertex to already be a
vertex of the graph (\<open>t_set Src \<subseteq> dVs G\<close>); to satisfy this unconditionally we augment the graph
with a self-loop at every source vertex before running BFS. The following lemma shows that this
augmentation does not change which vertices are reachable via genuine walks.\<close>

lemma vwalk_bet_selfloop_irrelevant:
  assumes "Vwalk.vwalk (G \<union> {(s,s) |s. s \<in> S}) p" "p \<noteq> []"
  shows "(\<exists> q. q \<noteq> [] \<and> Vwalk.vwalk G q \<and> hd q = hd p \<and> last q = last p) \<or> last p = hd p"
  using assms
proof(induction rule: Vwalk.vwalk.induct)
  case vwalk0
  then show ?case by simp
next
  case (vwalk1 v)
  then show ?case by simp
next
  case (vwalk2 v v' vs)
  show ?case
  proof(cases "(v,v') \<in> G")
    case True
    show ?thesis
    proof -
      have IH': "(\<exists>q. q \<noteq> [] \<and> Vwalk.vwalk G q \<and> hd q = v' \<and> last q = last (v'#vs))
                  \<or> last (v'#vs) = hd (v'#vs)"
        using vwalk2.IH by simp
      from IH' show ?thesis
      proof(rule disjE)
        assume "\<exists>q. q \<noteq> [] \<and> Vwalk.vwalk G q \<and> hd q = v' \<and> last q = last (v'#vs)"
        then obtain q where q_prop: "q \<noteq> []" "Vwalk.vwalk G q" "hd q = v'" "last q = last (v'#vs)"
          by auto
        have "Vwalk.vwalk G (v#q)"
          using True q_prop(1,2,3) by (cases q) auto
        thus ?thesis using q_prop(1,4) by (intro disjI1 exI[of _ "v#q"]) auto
      next
        assume "last (v'#vs) = hd (v'#vs)"
        hence lv: "last (v'#vs) = v'" by simp
        have "v' \<in> dVs G" using True by (auto simp add: dVs_def)
        hence "Vwalk.vwalk G [v,v']" using True by (auto intro: vwalk1 vwalk2)
        thus ?thesis using lv by (intro disjI1 exI[of _ "[v,v']"]) auto
      qed
    qed
  next
    case False
    hence self: "v = v'" "v \<in> S" using vwalk2.hyps(1) by auto
    show ?thesis
    proof -
      have IH': "(\<exists>q. q \<noteq> [] \<and> Vwalk.vwalk G q \<and> hd q = v' \<and> last q = last (v'#vs))
                  \<or> last (v'#vs) = hd (v'#vs)"
        using vwalk2.IH by simp
      from IH' show ?thesis
      proof(rule disjE)
        assume "\<exists>q. q \<noteq> [] \<and> Vwalk.vwalk G q \<and> hd q = v' \<and> last q = last (v'#vs)"
        then obtain q where q_prop: "q \<noteq> []" "Vwalk.vwalk G q" "hd q = v'" "last q = last (v'#vs)"
          by auto
        thus ?thesis using self(1) q_prop(1,4) by (intro disjI1 exI[of _ q]) auto
      next
        assume "last (v'#vs) = hd (v'#vs)"
        thus ?thesis using self(1) by (intro disjI2) auto
      qed
    qed
  qed
qed

text \<open>\<open>reach_set_graph\<close> augments \<open>G\<close> with a self-loop at every source vertex, so that BFS's
precondition \<open>t_set Src \<subseteq> dVs G\<close> holds unconditionally.\<close>

definition "reach_set_graph Src G = fold_rbt (\<lambda> s acc. G.add_edge acc s s) Src G"

lemma reach_set_graph_props:
  assumes "G.graph_inv G" "vset_inv Src"
  shows "G.graph_inv (reach_set_graph Src G)"
    "G.digraph_abs (reach_set_graph Src G) = G.digraph_abs G \<union> {(s,s) |s. s \<in> t_set Src}"
proof-
  obtain xs where xs_prop: "set xs = t_set Src"
    "reach_set_graph Src G = foldr (\<lambda> s acc. G.add_edge acc s s) xs G"
    using rbt_fold_spec[of Src "\<lambda> s acc. G.add_edge acc s s" G, OF assms(2)]
    by (auto simp add: reach_set_graph_def)
  have combined: "G.graph_inv (foldr (\<lambda> s acc. G.add_edge acc s s) ys G) \<and>
      G.digraph_abs (foldr (\<lambda> s acc. G.add_edge acc s s) ys G) = G.digraph_abs G \<union> {(s,s) |s. s \<in> set ys}"
    for ys
    using assms(1) by (induction ys) auto
  show "G.graph_inv (reach_set_graph Src G)"
    "G.digraph_abs (reach_set_graph Src G) = G.digraph_abs G \<union> {(s,s) |s. s \<in> t_set Src}"
    using combined[of xs] unfolding xs_prop(2) xs_prop(1)[symmetric] by auto
qed

lemma finite_vsets_unconditional: "dfs.Graph.finite_vsets Gr"
  by (auto simp add: dfs.Graph.finite_vsets_def)

lemma lookup_dom_subs_set_tree: "{v. lookup Gr v \<noteq> None} \<subseteq> fst ` Tree2.set_tree Gr"
  by (induction Gr) (fastforce simp add: lookup.simps split: if_splits)+

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
  apply(intro conjI allI)
  apply (rule reach_set_graph_props(1)[OF assms(1,2)])
  apply (rule finite_graph_of_graph_inv)
  apply (rule finite_vsets_unconditional)
  apply (rule reach_set_graph_srcs_in_dVs[OF assms(1,2)])
  apply (rule reach_set_graph_finite_neighb[OF assms(1,2)])
  apply (rule assms(3))
  apply (rule assms(2))
  done

lemma reach_set_bfs_dom:
  assumes "G.graph_inv G" "vset_inv Src" "t_set Src \<noteq> {}"
  shows "bfs.BFS_dom (reach_set_graph Src G) (bfs_initial_state Src)"
  by (rule bfs.initial_state_props(4)[OF reach_set_bfs_axiom[OF assms]])

lemma bfs_current_empty:
  assumes "bfs.BFS_dom G state"
  shows "current (bfs.BFS G state) = vset_empty"
  using assms
  by (induction rule: bfs.BFS.pinduct)
     (auto simp add: bfs.BFS.psimps bfs.BFS_call_1_conds_def RBT_Set.empty_def)

text \<open>Soundness: everything BFS marks as visited is genuinely reachable from some source
(modulo the self-loop augmentation, stripped via @{thm [source] vwalk_bet_selfloop_irrelevant}).\<close>

lemma reach_set_soundness:
  assumes "G.graph_inv G" "vset_inv Src" "t_set Src \<noteq> {}"
  shows "t_set (visited (bfs.BFS (reach_set_graph Src G) (bfs_initial_state Src)))
          \<subseteq> {v. \<exists>u\<in>t_set Src. u = v \<or> (\<exists>p. vwalk_bet (G.digraph_abs G) u p v)}"
proof
  fix x assume x_in: "x \<in> t_set (visited (bfs.BFS (reach_set_graph Src G) (bfs_initial_state Src)))"
  have ax: "BFS.BFS_axiom isin t_set M.invar \<langle>\<rangle> vset_inv lookup Src (reach_set_graph Src G)"
    using reach_set_bfs_axiom[OF assms] .
  have dom: "bfs.BFS_dom (reach_set_graph Src G) (bfs_initial_state Src)"
    using bfs.initial_state_props(4)[OF ax] .
  have i1: "bfs.invar_1 (bfs_initial_state Src)" using bfs.initial_state_props(1)[OF ax] .
  have i2: "bfs.invar_2 Src (reach_set_graph Src G) (bfs_initial_state Src)"
    using bfs.initial_state_props(2)[OF ax] .
  have icr: "bfs.invar_current_reachable Src (reach_set_graph Src G) (bfs_initial_state Src)"
    using bfs.initial_state_props(10)[OF ax] .
  have final_reach: "bfs.invar_current_reachable Src (reach_set_graph Src G)
       (bfs.BFS (reach_set_graph Src G) (bfs_initial_state Src))"
    using bfs.invar_current_reachable_holds[OF ax dom i1 i2 icr] .
  have dist_fin: "distance_set (G.digraph_abs (reach_set_graph Src G)) (t_set Src) x < \<infinity>"
    using bfs.invar_current_reachable_props[OF ax final_reach] x_in by auto
  have "\<exists>s\<in>t_set Src. Pair_Graph.reachable (G.digraph_abs (reach_set_graph Src G)) s x"
    using dist_fin infty_dist_is_unreachable[of "G.digraph_abs (reach_set_graph Src G)" "t_set Src" x]
    by auto
  then obtain s where s_prop: "s \<in> t_set Src" "Pair_Graph.reachable (G.digraph_abs (reach_set_graph Src G)) s x"
    by auto
  have "\<exists>p. vwalk_bet (G.digraph_abs (reach_set_graph Src G)) s p x"
    using s_prop(2) by (simp add: reachable_vwalk_bet_iff)
  then obtain p where p_prop: "vwalk_bet (G.digraph_abs (reach_set_graph Src G)) s p x" by auto
  have vw: "Vwalk.vwalk (G.digraph_abs (reach_set_graph Src G)) p" "p \<noteq> []" "hd p = s" "last p = x"
    using p_prop by (auto simp add: vwalk_bet_def)
  have vw': "Vwalk.vwalk (G.digraph_abs G \<union> {(t,t) |t. t \<in> t_set Src}) p"
    using vw(1) reach_set_graph_props(2)[OF assms(1,2)] by simp
  have "(\<exists>q. q \<noteq> [] \<and> Vwalk.vwalk (G.digraph_abs G) q \<and> hd q = hd p \<and> last q = last p) \<or> last p = hd p"
    using vwalk_bet_selfloop_irrelevant[OF vw' vw(2)] .
  thus "x \<in> {v. \<exists>u\<in>t_set Src. u = v \<or> (\<exists>p. vwalk_bet (G.digraph_abs G) u p v)}"
  proof(rule disjE)
    assume "\<exists>q. q \<noteq> [] \<and> Vwalk.vwalk (G.digraph_abs G) q \<and> hd q = hd p \<and> last q = last p"
    then obtain q where q_prop: "q \<noteq> []" "Vwalk.vwalk (G.digraph_abs G) q" "hd q = hd p" "last q = last p"
      by auto
    have "vwalk_bet (G.digraph_abs G) s q x"
      using q_prop(1,2) q_prop(3)[unfolded vw(3)] q_prop(4)[unfolded vw(4)]
      by (auto simp add: vwalk_bet_def)
    thus ?thesis using s_prop(1) by auto
  next
    assume "last p = hd p"
    hence "x = s" using vw(3,4) by simp
    thus ?thesis using s_prop(1) by auto
  qed
qed

text \<open>Completeness: every vertex reachable from some source ends up visited.\<close>

lemma reach_set_completeness:
  assumes "G.graph_inv G" "vset_inv Src" "t_set Src \<noteq> {}"
  shows "{v. \<exists>u\<in>t_set Src. u = v \<or> (\<exists>p. vwalk_bet (G.digraph_abs G) u p v)}
          \<subseteq> t_set (visited (bfs.BFS (reach_set_graph Src G) (bfs_initial_state Src)))"
proof
  fix x assume "x \<in> {v. \<exists>u\<in>t_set Src. u = v \<or> (\<exists>p. vwalk_bet (G.digraph_abs G) u p v)}"
  then obtain u where u_prop: "u \<in> t_set Src" "u = x \<or> (\<exists>p. vwalk_bet (G.digraph_abs G) u p x)"
    by auto
  have ax: "BFS.BFS_axiom isin t_set M.invar \<langle>\<rangle> vset_inv lookup Src (reach_set_graph Src G)"
    using reach_set_bfs_axiom[OF assms] .
  have walk_in_big: "\<exists>p. vwalk_bet (G.digraph_abs (reach_set_graph Src G)) u p x"
  proof(rule disjE[OF u_prop(2)])
    assume "u = x"
    have "u \<in> dVs (G.digraph_abs (reach_set_graph Src G))"
      using reach_set_graph_srcs_in_dVs[OF assms(1,2)] u_prop(1) by auto
    hence "vwalk_bet (G.digraph_abs (reach_set_graph Src G)) u [u] u"
      by (auto simp add: vwalk_bet_def intro: vwalk1)
    thus ?thesis using \<open>u = x\<close> by auto
  next
    assume "\<exists>p. vwalk_bet (G.digraph_abs G) u p x"
    then obtain p where "vwalk_bet (G.digraph_abs G) u p x" by auto
    hence "vwalk_bet (G.digraph_abs (reach_set_graph Src G)) u p x"
      using reach_set_graph_props(2)[OF assms(1,2)] by (auto intro: vwalk_bet_subset)
    thus ?thesis by auto
  qed
  show "x \<in> t_set (visited (bfs.BFS (reach_set_graph Src G) (bfs_initial_state Src)))"
  proof(rule ccontr)
    assume "x \<notin> t_set (visited (bfs.BFS (reach_set_graph Src G) (bfs_initial_state Src)))"
    hence "\<nexists>p. vwalk_bet (G.digraph_abs (reach_set_graph Src G)) u p x"
      using bfs.BFS_correct_1[OF ax u_prop(1)] by simp
    thus False using walk_in_big by simp
  qed
qed

lemma reach_set_correct_nonempty:
  assumes "G.graph_inv G" "vset_inv Src" "t_set Src \<noteq> {}"
  shows "t_set (visited (bfs.BFS (reach_set_graph Src G) (bfs_initial_state Src)))
          = {v. \<exists>u\<in>t_set Src. u = v \<or> (\<exists>p. vwalk_bet (G.digraph_abs G) u p v)}"
  using reach_set_soundness[OF assms] reach_set_completeness[OF assms] by (rule equalityI)

lemma reach_set_vset_inv_nonempty:
  assumes "G.graph_inv G" "vset_inv Src" "t_set Src \<noteq> {}"
  shows "vset_inv (visited (bfs.BFS (reach_set_graph Src G) (bfs_initial_state Src)))"
  using bfs.invar_1_holds[OF reach_set_bfs_axiom[OF assms] reach_set_bfs_dom[OF assms]
      bfs.initial_state_props(1)[OF reach_set_bfs_axiom[OF assms]]]
  by (simp add: bfs.invar_1_def)

text \<open>Finally, \<open>reach_set\<close> itself: falls back to the empty vset when \<open>Src\<close> is empty (BFS's own
precondition needs a nonempty source set), otherwise runs BFS on the self-loop-augmented graph.\<close>

definition "reach_set Src G =
  (if Src = vset_empty then vset_empty else visited (bfs_impl (reach_set_graph Src G) (bfs_initial_state Src)))"

lemma reach_set_final_invar:
  assumes "G.graph_inv G" "vset_inv Src"
  shows "vset_inv (reach_set Src G)"
proof(cases "Src = vset_empty")
  case True
  then show ?thesis by (simp add: reach_set_def vset_inv_def RBT_Set.empty_def)
next
  case False
  hence ne: "t_set Src \<noteq> {}" using assms(2) by (auto simp add: vset_inv_def RBT_Set.empty_def)
  show ?thesis
    using reach_set_vset_inv_nonempty[OF assms ne]
          bfs.BFS_impl_same[OF reach_set_bfs_dom[OF assms ne]]
    by (simp add: reach_set_def False)
qed

lemma reach_set_final_correct:
  assumes "G.graph_inv G" "vset_inv Src"
  shows "t_set (reach_set Src G) = {v. \<exists>u\<in>t_set Src. u = v \<or> (\<exists>p. vwalk_bet (G.digraph_abs G) u p v)}"
proof(cases "Src = vset_empty")
  case True
  hence "t_set Src = {}" using assms(2) by (auto simp add: vset_inv_def RBT_Set.empty_def)
  then show ?thesis using True by (simp add: reach_set_def RBT_Set.empty_def)
next
  case False
  hence ne: "t_set Src \<noteq> {}" using assms(2) by (auto simp add: vset_inv_def RBT_Set.empty_def)
  show ?thesis
    using reach_set_correct_nonempty[OF assms ne]
          bfs.BFS_impl_same[OF reach_set_bfs_dom[OF assms ne]]
    by (simp add: reach_set_def False)
qed

subsection \<open>Instantiating a concrete bipartite matching instance\<close>

text \<open>As in @{file "Max_Bipartite_Matching_Matroid.thy"}, we fix a concrete bipartite edge set and
build the weighted matroid intersection instance on top. The local definitions are named with a
\<open>W\<close>-prefix to avoid colliding with the globally-exported \<open>Edges\<close>/\<open>X\<close>/\<open>Y\<close>/\<open>to_dbltn\<close> constants of
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

lemma left_not_right': "e \<in> WEdges \<Longrightarrow> \<exists>u v. {left_vertex e, right_vertex e} = {u, v} \<and> u \<noteq> v"
  using bipart by (auto simp add: WEdges_def)

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
  apply(rule ext)
  subgoal for M
    apply(cases M)
    apply (simp add: matching_basic_operations.emap_lft_inv_def
        matching_basic_operations.emap_rht_inv_def)
    done
  done

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
  then show ?case by unfold_locales
next
  case 2
  then show ?case by (auto intro: Wdouble_matroid)
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
    from 16 show ?case
      by (simp add: Wcircuit1_eq Wto_set_red_eq Windep1_def Wset_matching_eq Wsame_invar
          matching_as_matroid_intersection_proofs.circuit1_correct[of X y,
            unfolded insert_is_Un[symmetric]])
  next
    case (17 X y)
    from 17 show ?case
      by (auto intro: matching_as_matroid_intersection_proofs.circuit1_invar[unfolded
            matching_as_matroid_intersection_proofs.set_invar_red_def]
          simp add: Wcircuit1_eq Wsame_invar set_invar_red_def
          matching_as_matroid_intersection_proofs.set_invar_red_def)
  next
    case (18 X y)
    from 18 show ?case
    proof -
      have key: "to_set_red (circuit2 right_vertex y X) =
                  matroid.the_circuit local.WEdges local.Windep2 ({y} \<union> set_matching X) - {y}"
        using "18"
        by (simp add: Windep2_def Wcircuit2_eq Wto_set_red_eq Wset_matching_eq Wsame_invar
            matching_as_matroid_intersection_proofs.circuit2_correct)
      have ins: "Set.insert y (set_matching X) = {y} \<union> set_matching X" by blast
      show ?case unfolding ins by (rule key)
    qed
  next
    case (19 X y)
    from 19 show ?case
    proof -
      have pre: "matching_as_matroid_intersection_proofs.invar_matching X"
        using "19" by (simp add: Wsame_invar)
      note fact2 = matching_as_matroid_intersection_proofs.circuit2_invar[OF pre]
      show ?case using fact2[where y=y]
        by (simp add: Wcircuit2_eq set_invar_red_def
            matching_as_matroid_intersection_proofs.set_invar_red_def)
    qed
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
      by (auto intro: weighted_matching_as_matroid_intersection.c_shift_invar)
  next
    case (23 R e c)
    then show ?case
      by (auto intro: weighted_matching_as_matroid_intersection.c_shift_lookup)
  next
    case (24 V c)
    then show ?case
      by (auto intro: weighted_matching_as_matroid_intersection.weight_Max_correct)
  next
    case (25 V c)
    then show ?case
      by (auto intro: weighted_matching_as_matroid_intersection.restrict_to_max_invar)
  next
    case (26 V c)
    then show ?case
      by (cases "t_set V = {}")
         (auto simp add: weighted_matching_as_matroid_intersection.restrict_to_max_set
             weighted_matching_as_matroid_intersection.weight_Max_correct)
  next
    case (27 Src G)
    then show ?case
      by (rule reach_set_final_invar)
  next
    case (28 Src G)
    then show ?case
      by (rule reach_set_final_correct)
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

theorem weighted_solution:
  "max_weight_matching (Wto_dbltn ` WEdges) Wweight
     (Wto_dbltn ` (set_matching (wsol (weighted_matching_algorithm.weighted_matroid_intersection
                      (weighted_matching_algorithm.weighted_initial_state cost_map)))))"
proof-
  define sol where "sol = set_matching (wsol (weighted_matching_algorithm.weighted_matroid_intersection
                      (weighted_matching_algorithm.weighted_initial_state cost_map)))"
  have ci: "weighted_matching_as_matroid_intersection.c_invar cost_map"
    using cost_map_inv by (simp add: weighted_matching_as_matroid_intersection.c_invar_def)
  have opt: "weighted_double_matroid.is_opt Windep1 Windep2
               (weighted_matching_as_matroid_intersection.c_lookup cost_map) sol"
    using weighted_matching_algorithm.weighted_matroid_intersection_correct[OF ci]
    by (simp add: sol_def)
  have dm: "weighted_double_matroid WEdges Windep1 Windep2"
    using Wdouble_matroid by (simp add: weighted_double_matroid_def)
  have opt': "Windep1 sol" "Windep2 sol"
    "\<And>Y. Windep1 Y \<Longrightarrow> Windep2 Y \<Longrightarrow>
       sum (weighted_matching_as_matroid_intersection.c_lookup cost_map) Y
         \<le> sum (weighted_matching_as_matroid_intersection.c_lookup cost_map) sol"
    using opt by (auto simp add: weighted_double_matroid.is_opt_def[OF dm])
  have sol_sub: "sol \<subseteq> WEdges"
    using opt'(1) by (simp add: Windep1_def matching_as_matroid_intersection.indep1_def)
  have gm: "graph_matching (Wto_dbltn ` WEdges) (Wto_dbltn ` sol)"
    using opt'(1,2)[unfolded Windep1_def Windep2_def]
    by (intro matching_as_matroid_intersection.double_indep_to_graph_matching)
  show ?thesis
    unfolding sol_def[symmetric] max_weight_matching_def
  proof(intro conjI allI impI)
    show "matching (Wto_dbltn ` sol)" using gm by auto
  next
    show "Wto_dbltn ` sol \<subseteq> Wto_dbltn ` WEdges" using gm by auto
  next
    fix M' assume M'_gm: "graph_matching (Wto_dbltn ` WEdges) M'"
    have "\<exists>M_impl. M' = Wto_dbltn ` M_impl \<and> matching_as_matroid_intersection.indep1 M_impl \<and>
                      matching_as_matroid_intersection.indep2 M_impl"
      using matching_as_matroid_intersection.graph_matching_to_double_indep[OF M'_gm] .
    then obtain M_impl where M_impl_prop: "M' = Wto_dbltn ` M_impl"
        "matching_as_matroid_intersection.indep1 M_impl" "matching_as_matroid_intersection.indep2 M_impl"
      by auto
    have sub: "M_impl \<subseteq> WEdges"
      using M_impl_prop(2) by (simp add: matching_as_matroid_intersection.indep1_def)
    show "sum Wweight M' \<le> sum Wweight (Wto_dbltn ` sol)"
      unfolding M_impl_prop(1) Wsum_dbltn[OF sub] Wsum_dbltn[OF sol_sub]
      using opt'(3)[of M_impl] M_impl_prop(2,3)
      by (simp add: Windep1_def Windep2_def)
  qed
qed

end

end

