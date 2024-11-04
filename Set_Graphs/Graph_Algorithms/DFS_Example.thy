theory DFS_Example                   
  imports DFS Directed_Set_Graphs.Pair_Graph_RBT
begin

global_interpretation dfs: DFS 
where insert = insert_rbt 
and sel = sel 
and vset_empty = Leaf
and lookup=lookup 
and empty = RBT_Set.empty
and delete=delete
and isin = isin 
and t_set=Tree2.set_tree
and update=update
and adjmap_inv = M.invar
and vset_delete=delete_rbt
and vset_inv = vset_inv 
and union=union_rbt 
and inter=inter_rbt
and diff=diff_rbt
and G = F and t = "t::nat" and s = "s::nat"  for F t s
defines dfs_initial_state = dfs.initial_state 
and dfs_impl = dfs.DFS_impl
and neighbourhood=G.neighbourhood
  apply unfold_locales (*unfold_locales doesn't finish it due to different invariants used in
                         Set2_Join vs Set instantiations*) 
  by (simp add: vset_inv_def RBT.set_tree_union RBT.set_tree_inter RBT.set_tree_diff 
                RBT.bst_union RBT.inv_union RBT.bst_inter RBT.inv_inter RBT.bst_diff RBT.inv_diff)+

definition "edges = [(0::nat, 1::nat), (0, 2), (2, 3), (2,4), (2,1), (1,5), (5,8), (8,7), (7,1),
                     (7,2), (7,4), (4,3), (3,4), (3,3), (9, 8), (8, 1), (4,5), (5,10)]"

definition "vertices = remdups (map prod.fst edges @ map prod.snd edges)"

definition "nbs v = foldr (\<lambda> x tree. insert x tree) (remdups (map prod.snd (filter (\<lambda> e. prod.fst e = v) edges))) Leaf"

definition "G = foldr (\<lambda> x tree. update x (nbs x) tree) vertices  empty"

lemmas neighbourhood_def[unfolded G.neighbourhood_def, code]

value edges
value vertices
value G
value "neighbourhood G"
value "dfs_initial_state 1"
value "dfs_impl G 9 (dfs_initial_state 0)"
value "dfs_impl G 3 (dfs_initial_state 0)"

end