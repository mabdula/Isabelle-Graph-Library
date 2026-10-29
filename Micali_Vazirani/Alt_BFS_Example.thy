theory Alt_BFS_Example
  imports Alt_BFS Graph_Algorithms_Dev.BFS_Example
begin

provenance human

instantiation parity :: linorder
begin
definition less_eq_parity :: "parity \<Rightarrow> parity \<Rightarrow> bool" where
  "less_eq_parity p q = (p = Even \<or> q = Odd)"
definition less_parity :: "parity \<Rightarrow> parity \<Rightarrow> bool" where
  "less_parity p q = (p = Even \<and> q = Odd)"
instance
proof
  fix x y z :: parity
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (cases x; cases y) (auto simp: less_eq_parity_def less_parity_def)
  show "x \<le> x" by (cases x) (auto simp: less_eq_parity_def)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (cases x; cases y; cases z) (auto simp: less_eq_parity_def)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (cases x; cases y) (auto simp: less_eq_parity_def)
  show "x \<le> y \<or> y \<le> x" by (cases x; cases y) (auto simp: less_eq_parity_def)
qed
end

instantiation labelled_vtx :: (linorder) linorder
begin
definition less_eq_labelled_vtx :: "'a labelled_vtx \<Rightarrow> 'a labelled_vtx \<Rightarrow> bool" where
  "less_eq_labelled_vtx u v =
     (label u < label v \<or> (label u = label v \<and> vtx u \<le> vtx v))"
definition less_labelled_vtx :: "'a labelled_vtx \<Rightarrow> 'a labelled_vtx \<Rightarrow> bool" where
  "less_labelled_vtx u v =
     (label u < label v \<or> (label u = label v \<and> vtx u < vtx v))"
instance
proof
  fix x y z :: "'a labelled_vtx"
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (cases x; cases y) (auto simp: less_eq_labelled_vtx_def less_labelled_vtx_def)
  show "x \<le> x" by (cases x) (auto simp: less_eq_labelled_vtx_def)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (cases x; cases y; cases z) (auto simp: less_eq_labelled_vtx_def)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (cases x; cases y) (auto simp: less_eq_labelled_vtx_def)
  show "x \<le> y \<or> y \<le> x"
    by (cases x; cases y) (auto simp: less_eq_labelled_vtx_def)
qed
end

locale Alt_BFS_dist_subprocedures =
  Pair_Graph_Sepcs_Set2 where lookup = lookup +
  dist_map: Map where empty = empty_dist and update = update_dist and
                      delete = delete_dist and lookup = lookup_dist and
                      invar = invar_dist
  for lookup :: "'adjmap \<Rightarrow> 'ver \<Rightarrow> 'vset option"
  and lookup_dist :: "'dmap \<Rightarrow> 'ver labelled_vtx \<Rightarrow> enat option"
  and empty_dist update_dist delete_dist invar_dist +
  fixes fold_dmap :: "('ver \<Rightarrow> 'dmap \<Rightarrow> 'dmap) \<Rightarrow> 'vset \<Rightarrow> 'dmap \<Rightarrow> 'dmap"
  assumes fold_dmap: "\<And>N f acc. \<exists>xs. set xs = t_set N \<and> fold_dmap f N acc = foldr f xs acc"
begin

definition upd_dists_impl :: "parity \<Rightarrow> 'adjmap \<Rightarrow> 'dmap \<Rightarrow> 'vset \<Rightarrow> 'vset \<Rightarrow> 'dmap" where
"upd_dists_impl parity G dm frontier vis =
   fold_dmap (\<lambda>u acc.
      fold_dmap (\<lambda>v acc'.
          update_dist (Vtx parity v)
            (the (lookup_dist dm (Vtx (other_parity parity) u)) + 1) acc')
        (diff (Graph.neighbourhood G u) vis) acc)
     frontier dm"

definition init_dists_impl :: "'vset \<Rightarrow> 'dmap" where
"init_dists_impl srcs = fold_dmap (\<lambda>u acc. update_dist (Vtx Even u) 0 acc) srcs empty_dist"

lemmas [code] = upd_dists_impl_def init_dists_impl_def

lemma foldr_const_writes:
  assumes "invar_dist acc"
  shows "invar_dist (foldr (\<lambda>v. update_dist (Vtx parity v) c) ys acc)"
    and "lookup_dist (foldr (\<lambda>v. update_dist (Vtx parity v) c) ys acc) w =
           (if w \<in> Vtx parity ` set ys then Some c else lookup_dist acc w)"
  using assms
  by (induction ys)
     (auto simp: dist_map.map_update dist_map.invar_update)

lemma upd_one_lookup:
  assumes "invar_dist acc" "vset_inv vis" "Graph.graph_inv G"
  shows "invar_dist (fold_dmap (\<lambda>v acc'.
            update_dist (Vtx parity v)
              (the (lookup_dist dm (Vtx (other_parity parity) u)) + 1) acc')
            (diff (Graph.neighbourhood G u) vis) acc)"
    and "lookup_dist (fold_dmap (\<lambda>v acc'.
            update_dist (Vtx parity v)
              (the (lookup_dist dm (Vtx (other_parity parity) u)) + 1) acc')
            (diff (Graph.neighbourhood G u) vis) acc) w =
          (if w \<in> Vtx parity ` (Pair_Graph.neighbourhood (Graph.digraph_abs G) u - t_set vis)
           then Some (the (lookup_dist dm (Vtx (other_parity parity) u)) + 1)
           else lookup_dist acc w)"
proof-
  obtain ys where ys: "set ys = t_set (diff (Graph.neighbourhood G u) vis)"
    "fold_dmap (\<lambda>v acc'. update_dist (Vtx parity v)
        (the (lookup_dist dm (Vtx (other_parity parity) u)) + 1) acc')
      (diff (Graph.neighbourhood G u) vis) acc =
     foldr (\<lambda>v. update_dist (Vtx parity v)
        (the (lookup_dist dm (Vtx (other_parity parity) u)) + 1)) ys acc"
    using fold_dmap by blast
  have set_ys: "set ys = Pair_Graph.neighbourhood (Graph.digraph_abs G) u - t_set vis"
    using ys(1) assms(2,3)
    by (auto simp: set_ops.set_diff set_ops.invar_diff Graph.neighbourhood_abs)
  show "invar_dist (fold_dmap (\<lambda>v acc'.
            update_dist (Vtx parity v)
              (the (lookup_dist dm (Vtx (other_parity parity) u)) + 1) acc')
            (diff (Graph.neighbourhood G u) vis) acc)"
    using foldr_const_writes[OF assms(1)] ys set_ys by auto
  show "lookup_dist (fold_dmap (\<lambda>v acc'.
            update_dist (Vtx parity v)
              (the (lookup_dist dm (Vtx (other_parity parity) u)) + 1) acc')
            (diff (Graph.neighbourhood G u) vis) acc) w =
          (if w \<in> Vtx parity ` (Pair_Graph.neighbourhood (Graph.digraph_abs G) u - t_set vis)
           then Some (the (lookup_dist dm (Vtx (other_parity parity) u)) + 1)
           else lookup_dist acc w)"
    using foldr_const_writes[OF assms(1)] ys set_ys by auto
qed

lemma foldr_upd_dists_invar:
  assumes "invar_dist dm" "vset_inv vis" "Graph.graph_inv G"
  shows "invar_dist (foldr (\<lambda>u acc. fold_dmap (\<lambda>v acc'.
            update_dist (Vtx parity v)
              (the (lookup_dist dm (Vtx (other_parity parity) u)) + 1) acc')
            (diff (Graph.neighbourhood G u) vis) acc) xs dm)"
proof(induction xs)
  case Nil
  thus ?case using assms(1) by simp
next
  case (Cons x xs)
  show ?case
    by (simp add: upd_one_lookup(1)[OF Cons.IH assms(2,3)])
qed

lemma foldr_upd_dists_miss:
  assumes "invar_dist dm" "vset_inv vis" "Graph.graph_inv G"
  shows "w \<notin> Vtx parity ` (\<Union>u \<in> set xs.
            Pair_Graph.neighbourhood (Graph.digraph_abs G) u - t_set vis) \<Longrightarrow>
         lookup_dist (foldr (\<lambda>u acc. fold_dmap (\<lambda>v acc'.
            update_dist (Vtx parity v)
              (the (lookup_dist dm (Vtx (other_parity parity) u)) + 1) acc')
            (diff (Graph.neighbourhood G u) vis) acc) xs dm) w = lookup_dist dm w"
proof(induction xs arbitrary: w)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  have w_x: "w \<notin> Vtx parity ` (Pair_Graph.neighbourhood (Graph.digraph_abs G) x - t_set vis)"
    using Cons.prems(1) by auto
  have w_xs: "w \<notin> Vtx parity ` (\<Union>u \<in> set xs. Pair_Graph.neighbourhood (Graph.digraph_abs G) u - t_set vis)"
    using Cons.prems(1) by auto
  show ?case
    using upd_one_lookup(2)[OF foldr_upd_dists_invar[OF assms] assms(2,3)] w_x Cons.IH[OF w_xs]
    by simp
qed

lemma foldr_upd_dists_hit:
  assumes "invar_dist dm" "vset_inv vis" "Graph.graph_inv G"
  shows "v2 \<in> (\<Union>u \<in> set xs.
            Pair_Graph.neighbourhood (Graph.digraph_abs G) u - t_set vis) \<Longrightarrow>
         \<exists>u \<in> set xs. v2 \<in> Pair_Graph.neighbourhood (Graph.digraph_abs G) u - t_set vis \<and>
           lookup_dist (foldr (\<lambda>u acc. fold_dmap (\<lambda>v acc'.
            update_dist (Vtx parity v)
              (the (lookup_dist dm (Vtx (other_parity parity) u)) + 1) acc')
            (diff (Graph.neighbourhood G u) vis) acc) xs dm) (Vtx parity v2) =
             Some (the (lookup_dist dm (Vtx (other_parity parity) u)) + 1)"
proof(induction xs arbitrary: v2)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  show ?case
  proof(cases "v2 \<in> Pair_Graph.neighbourhood (Graph.digraph_abs G) x - t_set vis")
    case True
    show ?thesis using True upd_one_lookup(2)[OF foldr_upd_dists_invar[OF assms] assms(2,3)]
      by (auto intro: bexI[of _ x])
  next
    case False
    have v_in_tail: "v2 \<in> (\<Union>u \<in> set xs. Pair_Graph.neighbourhood (Graph.digraph_abs G) u - t_set vis)"
      using Cons.prems(1) False by auto
    note ih_applied = Cons.IH[OF v_in_tail]
    note step_eq = upd_one_lookup(2)[OF foldr_upd_dists_invar[OF assms] assms(2,3)]
    show ?thesis using ih_applied step_eq False by (auto simp: labelled_vtx.inject)
  qed
qed

lemma foldr_upd_dists:
  assumes "invar_dist dm" "vset_inv vis" "Graph.graph_inv G"
  shows "invar_dist (foldr (\<lambda>u acc. fold_dmap (\<lambda>v acc'.
            update_dist (Vtx parity v)
              (the (lookup_dist dm (Vtx (other_parity parity) u)) + 1) acc')
            (diff (Graph.neighbourhood G u) vis) acc) xs dm)"
    and "w \<notin> Vtx parity ` (\<Union>u \<in> set xs.
            Pair_Graph.neighbourhood (Graph.digraph_abs G) u - t_set vis) \<Longrightarrow>
         lookup_dist (foldr (\<lambda>u acc. fold_dmap (\<lambda>v acc'.
            update_dist (Vtx parity v)
              (the (lookup_dist dm (Vtx (other_parity parity) u)) + 1) acc')
            (diff (Graph.neighbourhood G u) vis) acc) xs dm) w = lookup_dist dm w"
    and "v \<in> (\<Union>u \<in> set xs.
            Pair_Graph.neighbourhood (Graph.digraph_abs G) u - t_set vis) \<Longrightarrow>
         \<exists>u \<in> set xs. v \<in> Pair_Graph.neighbourhood (Graph.digraph_abs G) u - t_set vis \<and>
           lookup_dist (foldr (\<lambda>u acc. fold_dmap (\<lambda>v acc'.
            update_dist (Vtx parity v)
              (the (lookup_dist dm (Vtx (other_parity parity) u)) + 1) acc')
            (diff (Graph.neighbourhood G u) vis) acc) xs dm) (Vtx parity v) =
             Some (the (lookup_dist dm (Vtx (other_parity parity) u)) + 1)"
  using foldr_upd_dists_invar[OF assms] foldr_upd_dists_miss[OF assms]
        foldr_upd_dists_hit[OF assms] by blast+


lemma upd_dists_impl_axioms:
  assumes "invar_dist dm" "vset_inv frontier" "vset_inv vis" "Graph.graph_inv G"
  shows "invar_dist (upd_dists_impl parity G dm frontier vis)"
    and "v \<in> Alt_BFS.next_frontier (Graph.digraph_abs G) (t_set frontier) (t_set vis) \<Longrightarrow>
         \<exists>u \<in> t_set frontier.
           v \<in> Pair_Graph.neighbourhood (Graph.digraph_abs G) u - t_set vis \<and>
           lookup_dist (upd_dists_impl parity G dm frontier vis) (Vtx parity v) =
             Some (the (lookup_dist dm (Vtx (other_parity parity) u)) + 1)"
    and "w \<notin> Vtx parity ` Alt_BFS.next_frontier (Graph.digraph_abs G) (t_set frontier) (t_set vis) \<Longrightarrow>
         lookup_dist (upd_dists_impl parity G dm frontier vis) w = lookup_dist dm w"
proof-
  have xs_aux: "\<exists>xs. set xs = t_set frontier \<and>
    fold_dmap (\<lambda>u acc. fold_dmap (\<lambda>v acc'.
              update_dist (Vtx parity v)
                (the (lookup_dist dm (Vtx (other_parity parity) u)) + 1) acc')
              (diff (Graph.neighbourhood G u) vis) acc) frontier dm =
    foldr (\<lambda>u acc. fold_dmap (\<lambda>v acc'.
              update_dist (Vtx parity v)
                (the (lookup_dist dm (Vtx (other_parity parity) u)) + 1) acc')
              (diff (Graph.neighbourhood G u) vis) acc) xs dm"
    using fold_dmap by blast
  then obtain xs where xs: "set xs = t_set frontier"
    "upd_dists_impl parity G dm frontier vis =
     foldr (\<lambda>u acc. fold_dmap (\<lambda>v acc'.
              update_dist (Vtx parity v)
                (the (lookup_dist dm (Vtx (other_parity parity) u)) + 1) acc')
              (diff (Graph.neighbourhood G u) vis) acc) xs dm"
    unfolding upd_dists_impl_def by blast
  have nf_eq: "Alt_BFS.next_frontier (Graph.digraph_abs G) (t_set frontier) (t_set vis) =
               (\<Union>u \<in> set xs. Pair_Graph.neighbourhood (Graph.digraph_abs G) u - t_set vis)"
    using xs(1) by (auto simp: Alt_BFS.next_frontier_def)
  show "invar_dist (upd_dists_impl parity G dm frontier vis)"
    using foldr_upd_dists(1)[OF assms(1) assms(3,4)] xs(2) by simp
  show "v \<in> Alt_BFS.next_frontier (Graph.digraph_abs G) (t_set frontier) (t_set vis) \<Longrightarrow>
         \<exists>u \<in> t_set frontier.
           v \<in> Pair_Graph.neighbourhood (Graph.digraph_abs G) u - t_set vis \<and>
           lookup_dist (upd_dists_impl parity G dm frontier vis) (Vtx parity v) =
             Some (the (lookup_dist dm (Vtx (other_parity parity) u)) + 1)"
  proof-
    assume v_in: "v \<in> Alt_BFS.next_frontier (Graph.digraph_abs G) (t_set frontier) (t_set vis)"
    hence v_in': "v \<in> (\<Union>u \<in> set xs. Pair_Graph.neighbourhood (Graph.digraph_abs G) u - t_set vis)"
      by (simp add: nf_eq)
    from foldr_upd_dists(3)[OF assms(1) assms(3,4) v_in'] obtain u where u_props:
      "u \<in> set xs" "v \<in> Pair_Graph.neighbourhood (Graph.digraph_abs G) u - t_set vis"
      "lookup_dist (foldr (\<lambda>u acc. fold_dmap (\<lambda>v acc'.
                update_dist (Vtx parity v)
                  (the (lookup_dist dm (Vtx (other_parity parity) u)) + 1) acc')
                (diff (Graph.neighbourhood G u) vis) acc) xs dm) (Vtx parity v) =
         Some (the (lookup_dist dm (Vtx (other_parity parity) u)) + 1)"
      by blast
    thus "\<exists>u \<in> t_set frontier.
           v \<in> Pair_Graph.neighbourhood (Graph.digraph_abs G) u - t_set vis \<and>
           lookup_dist (upd_dists_impl parity G dm frontier vis) (Vtx parity v) =
             Some (the (lookup_dist dm (Vtx (other_parity parity) u)) + 1)"
      using xs by auto
  qed
  show "w \<notin> Vtx parity ` Alt_BFS.next_frontier (Graph.digraph_abs G) (t_set frontier) (t_set vis) \<Longrightarrow>
         lookup_dist (upd_dists_impl parity G dm frontier vis) w = lookup_dist dm w"
  proof-
    assume w_out: "w \<notin> Vtx parity ` Alt_BFS.next_frontier (Graph.digraph_abs G) (t_set frontier) (t_set vis)"
    hence w_out': "w \<notin> Vtx parity ` (\<Union>u \<in> set xs.
            Pair_Graph.neighbourhood (Graph.digraph_abs G) u - t_set vis)"
      by (simp add: nf_eq)
    thus "lookup_dist (upd_dists_impl parity G dm frontier vis) w = lookup_dist dm w"
      using foldr_upd_dists(2)[OF assms(1) assms(3,4) w_out'] xs by simp
  qed
qed

lemma init_dists_impl_axioms:
  shows "u \<in> t_set srcs \<Longrightarrow> lookup_dist (init_dists_impl srcs) (Vtx Even u) = Some 0"
    and "invar_dist (init_dists_impl srcs)"
proof-
  show "invar_dist (init_dists_impl srcs)"
  proof -
    have aux: "\<exists>xs. set xs = t_set srcs \<and>
      fold_dmap (\<lambda>u acc. update_dist (Vtx Even u) 0 acc) srcs empty_dist =
      foldr (\<lambda>u acc. update_dist (Vtx Even u) 0 acc) xs empty_dist"
      using fold_dmap by blast
    then obtain xs where xs_set: "set xs = t_set srcs"
      and xs_eq: "fold_dmap (\<lambda>u acc. update_dist (Vtx Even u) 0 acc) srcs empty_dist =
                  foldr (\<lambda>u acc. update_dist (Vtx Even u) 0 acc) xs empty_dist"
      by blast
    have inv_foldr: "invar_dist (foldr (\<lambda>u. update_dist (Vtx Even u) 0) xs empty_dist)"
      using foldr_const_writes(1)[OF dist_map.invar_empty] by simp
    show ?thesis using inv_foldr unfolding init_dists_impl_def xs_eq by simp
  qed
next
  assume u_in: "u \<in> t_set srcs"
  show "lookup_dist (init_dists_impl srcs) (Vtx Even u) = Some 0"
  proof -
    have aux: "\<exists>xs. set xs = t_set srcs \<and>
      fold_dmap (\<lambda>u acc. update_dist (Vtx Even u) 0 acc) srcs empty_dist =
      foldr (\<lambda>u acc. update_dist (Vtx Even u) 0 acc) xs empty_dist"
      using fold_dmap by blast
    then obtain xs where xs_set: "set xs = t_set srcs"
      and xs_eq: "fold_dmap (\<lambda>u acc. update_dist (Vtx Even u) 0 acc) srcs empty_dist =
                  foldr (\<lambda>u acc. update_dist (Vtx Even u) 0 acc) xs empty_dist"
      by blast
    have lup_xs: "u \<in> set xs \<Longrightarrow>
      lookup_dist (foldr (\<lambda>v. update_dist (Vtx Even v) 0) xs empty_dist) (Vtx Even u) = Some 0"
      using foldr_const_writes(2)[OF dist_map.invar_empty, of Even 0 xs] by simp
    show ?thesis using lup_xs u_in unfolding init_dists_impl_def xs_eq xs_set by simp
  qed
qed

end

global_interpretation alt_dist_subs: Alt_BFS_dist_subprocedures
  where insert = insert_rbt and sel = sel and vset_empty = Leaf and diff = diff_rbt
    and lookup = lookup and empty = RBT_Set.empty and delete = RBT_Map.delete
    and isin = isin and t_set = Tree2.set_tree and update = update
    and adjmap_inv = M.invar and vset_delete = delete_rbt and vset_inv = vset_inv
    and union = union_rbt and inter = inter_rbt
    and lookup_dist = lookup and empty_dist = RBT_Set.empty
    and update_dist = update and delete_dist = RBT_Map.delete and invar_dist = M.invar
    and fold_dmap = fold_rbt
  defines upd_dists_exec = alt_dist_subs.upd_dists_impl
    and init_dists_exec = alt_dist_subs.init_dists_impl
  apply unfold_locales
  apply (intro allI exI[of _ "map fst (preorder _)"])
  apply (simp only: preorder_witness fold_rbt_is_foldr_of_preorder)
  by (auto simp: prderorder_set[symmetric] Tree.set_preorder image_def intro: bexI)

global_interpretation alt_bfs: Alt_BFS.BFS
  where insert = insert_rbt and sel = sel and vset_empty = Leaf and diff = diff_rbt
    and lookup_neighb = lookup and empty = RBT_Set.empty and delete = RBT_Map.delete
    and isin = isin and t_set = Tree2.set_tree and update = update
    and adjmap_inv = M.invar and vset_delete = delete_rbt and vset_inv = vset_inv
    and union = union_rbt and inter = inter_rbt
    and lookup_dist = lookup and empty_dist = RBT_Set.empty and update_dist = update
    and delete_dist = RBT_Map.delete and invar_dist = M.invar
    and srcs = srcs and matching = matching and unmatching = unmatching
    and expand_tree = expand_tree
    and next_frontier_impl = next_frontier
    and upd_dists = upd_dists_exec
    and init_dists = "init_dists_exec srcs"
  for matching unmatching srcs
  defines alt_bfs_initial_state = alt_bfs.initial_state
    and alt_bfs_impl = alt_bfs.BFS_impl
  apply unfold_locales
  subgoal by (auto simp: bfs_subprocedures.expand_tree Alt_BFS.new_edges_def)
  subgoal by (auto simp: bfs_subprocedures.expand_tree Alt_BFS.new_edges_def)
  subgoal by (auto simp: bfs_subprocedures.next_frontier Alt_BFS.next_frontier_def)
  subgoal by (auto simp: bfs_subprocedures.next_frontier Alt_BFS.next_frontier_def)
  subgoal by (simp add: alt_dist_subs.init_dists_impl_axioms)
  subgoal by (simp add: alt_dist_subs.init_dists_impl_axioms)
  subgoal by (auto intro: alt_dist_subs.upd_dists_impl_axioms)
  subgoal by (fastforce intro: alt_dist_subs.upd_dists_impl_axioms)
  subgoal by (auto intro: alt_dist_subs.upd_dists_impl_axioms)
  done

declare alt_dist_subs.upd_dists_impl_def[code del]

lemma upd_dists_exec_code[code]:
  "upd_dists_exec parity G dm frontier vis =
   fold_rbt (\<lambda>u. fold_rbt (\<lambda>v acc.
       update (Vtx parity v) (the (lookup dm (Vtx (other_parity parity) u)) + 1) acc)
     (diff_rbt (case lookup G u of None \<Rightarrow> Leaf | Some N \<Rightarrow> N) vis)) frontier dm"
  by (simp add: alt_dist_subs.upd_dists_impl_def Pair_Graph_RBT.G.neighbourhood_def)

definition "unmatching_edges = [(0::nat,1::nat),(1,0),(0,2),(2,0),(2,3),(3,2)]"
definition "matching_edges = [(1::nat,2::nat),(2,1)]"
definition "unmatchingG = a_graph unmatching_edges"
definition "matchingG = a_graph matching_edges"
definition "src_list = [0::nat]"
definition "srcs = foldr (\<lambda>x tree. insert x tree) src_list Leaf"

value "alt_bfs_initial_state srcs"
value "alt_bfs_impl matchingG unmatchingG (alt_bfs_initial_state srcs)"
value "lookup (distances (alt_bfs_impl matchingG unmatchingG (alt_bfs_initial_state srcs))) (Vtx Odd (1::nat))"
value "lookup (distances (alt_bfs_impl matchingG unmatchingG (alt_bfs_initial_state srcs))) (Vtx Even (1::nat))"
value "lookup (distances (alt_bfs_impl matchingG unmatchingG (alt_bfs_initial_state srcs))) (Vtx Odd (0::nat))"
hide_const unmatching_edges matching_edges unmatchingG matchingG src_list srcs
end
