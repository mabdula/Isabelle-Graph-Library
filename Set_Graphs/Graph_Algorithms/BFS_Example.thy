theory BFS_Example 
  imports BFS_Subprocedures "HOL-Data_Structures.RBT_Map"
          Directed_Set_Graphs.Pair_Graph_RBT
begin


definition "fold_vset = (fold_rbt)"
definition "fold_adjmap = (fold_rbt)"

lemma prderorder_set:"set (map fst (preorder N)) = Tree2.set_tree N"
  by(induction N rule: preorder.induct)auto

lemma preorder_witness:"set (map fst (preorder N)) = Tree2.set_tree N \<and> fold_rbt f N acc = foldr f (map fst (preorder N)) acc"
  unfolding fold_rbt_is_foldr_of_preorder prderorder_set by auto

lemma rbt_fold_spec:"vset_inv N \<Longrightarrow> \<exists>xs. set xs = Tree2.set_tree N \<and> fold_rbt f N acc = foldr f xs acc"
  using preorder_witness by metis


global_interpretation bfs_subprocedures: BFS_subprocedures
where insert = insert_rbt 
and sel = sel 
and vset_empty = Leaf 
and diff = diff_rbt
and lookup = lookup 
and empty = empty 
and delete=delete 
and isin = isin 
and t_set=Tree2.set_tree
and update=update 
and adjmap_inv = M.invar
and vset_delete= delete_rbt
and vset_inv = vset_inv 
and union=union_rbt 
and inter=inter_rbt 
and fold_vset = fold_vset
and fold_adjmap=fold_adjmap
and G = G for G 
defines next_frontier = bfs_subprocedures.next_frontier
and expand_tree = bfs_subprocedures.expand_tree
and neighbourhood = G.neighbourhood
and add_neighbs = bfs_subprocedures.add_neighbs
  apply unfold_locales
  by (auto simp add: fold_vset_def  rbt_fold_spec  fold_adjmap_def vset_inv_def RBT.set_tree_union RBT.set_tree_inter RBT.set_tree_diff 
                RBT.bst_union RBT.inv_union RBT.bst_inter RBT.inv_inter RBT.bst_diff RBT.inv_diff)

lemmas neighbourhood_def[unfolded G.neighbourhood_def, code] 

global_interpretation bfs: BFS
where insert = insert_rbt 
and sel = sel 
and vset_empty = Leaf 
and diff = diff_rbt
and lookup = lookup 
and empty = empty 
and delete=delete 
and isin = isin 
and t_set=Tree2.set_tree
and update=update 
and adjmap_inv = M.invar
and vset_delete=delete_rbt
and vset_inv = vset_inv 
and union=union_rbt 
and inter=inter_rbt
and expand_tree = "expand_tree G"
and next_frontier = "next_frontier G"
and G = G and srcs = srcs for G srcs
defines bfs_initial_state = "bfs.initial_state"
and bfs_impl = bfs.BFS_impl
  apply unfold_locales
  by (auto simp add: bfs_subprocedures.expand_tree bfs_subprocedures.next_frontier)
  
definition "edges = [(0::nat, 1::nat), (0, 2), (2, 3), (2,4), (2,1), (1,5), (5,8), (8,7), (7,1),
                     (7,2), (7,4), (4,3), (3,4), (3,3), (9, 8), (8, 1), (4,5), (5,10)]"

definition "G = a_graph edges"

definition "src_list = [9::nat]"

definition "srcs =  foldr (\<lambda> x tree. insert x tree) src_list empty"

value edges
value "vertices edges"
value "diff_rbt (nbs edges 1) (nbs edges 2)"
value G
value "bfs_initial_state srcs"   
value "bfs_impl G (bfs_initial_state srcs)"
hide_const G src_list srcs edges
end