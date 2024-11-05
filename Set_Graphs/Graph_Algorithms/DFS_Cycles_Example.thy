theory DFS_Cycles_Example
  imports DFS_Cycles_Aux DFS_Cycles Directed_Set_Graphs.Pair_Graph_RBT
begin

global_interpretation dfs_cycle_aux: DFS_Aux
  where empty = empty
and delete = delete
and insert = insert_rbt
and isin = isin
and t_set = Tree2.set_tree
and sel = sel
and update = update
and adjmap_inv = M.invar
and vset_empty = Leaf
and vset_delete = delete_rbt
and vset_inv = vset_inv
and union = union_rbt
and inter = inter_rbt
and diff = diff_rbt
and lookup = lookup
and s = s and G = G for s G
defines initial_state_aux = dfs_cycle_aux.initial_state
and dfs_aux = dfs_cycle_aux.DFS_Aux_impl
and neighbourhood = dfs_cycle_aux.neighbourhood'
  apply unfold_locales (*unfold_locales doesn't finish it due to different invariants used in
                         Set2_Join vs Set instantiations*) 
  by (simp add: vset_inv_def RBT.set_tree_union RBT.set_tree_inter RBT.set_tree_diff 
                RBT.bst_union RBT.inv_union RBT.bst_inter RBT.inv_inter RBT.bst_diff RBT.inv_diff)+

global_interpretation dfs_cycles: DFS_Cycles
  where empty = empty
and delete = delete
and insert = insert_rbt
and isin = isin
and t_set = Tree2.set_tree
and sel = sel
and update = update
and adjmap_inv = M.invar
and vset_empty = Leaf
and vset_delete = delete_rbt
and vset_inv = vset_inv
and union= RBT.union
and inter = inter_rbt
and diff = RBT.diff
and lookup = lookup
and dfs_aux = "\<lambda> s. dfs_aux G (initial_state_aux s)"
and cycle_aux = DFS_Aux_state.cycle
and seen_aux = DFS_Aux_state.seen
and V = V and G = G for V G
defines initial = dfs_cycles.initial_state
and find_cycles_by_dfs = dfs_cycles.DFS_Cycles_impl
  by unfold_locales

definition "edges = [(0::nat, 1::nat), (0, 2), (2, 3), (2,4), (2,1), (1,5), (5,8), (8,7), (7,1),
                     (7,2), (7,4), (4,3), (3,4), (3,3), (9, 8), (8, 1), (4,5), (5,10)]"

definition "vertices = remdups (map prod.fst edges @ map prod.snd edges)"

definition "nbs v = foldr (\<lambda> x tree. insert x tree) (remdups (map prod.snd (filter (\<lambda> e. prod.fst e = v) edges))) Leaf"

definition "G = foldr (\<lambda> x tree. update x (nbs x) tree) vertices  empty"

definition "V = foldr (\<lambda> x tree. insert_rbt x  tree) vertices Leaf"

value edges
value vertices

value G
value V

value "initial_state_aux (1::nat)"
value "dfs_aux G (initial_state_aux (9::nat))"

value "find_cycles_by_dfs V G initial"
end
