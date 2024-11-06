theory DFS_Example                   
  imports DFS Directed_Set_Graphs.Pair_Graph_RBT
begin

global_interpretation dfs: DFS where insert = vset_insert and
 sel = sel and  vset_empty = vset_empty and  diff = vset_diff and
 lookup = lookup and empty = map_empty and delete=delete and isin = isin and t_set=t_set
and update=update and adjmap_inv = adj_inv and vset_delete= vset_delete
and vset_inv = vset_inv and union=vset_union and inter=vset_inter and G = F and
t = "t::'a::linorder" and s = s  for F t s
defines  dfs_initial_state = dfs.initial_state and
neighbourhood=dfs.Graph.neighbourhood and
dfs_impl = dfs.DFS_impl 
  using G.Pair_Graph_Specs_axioms RBT.Set2_axioms
  by(auto intro!: DFS.intro  simp add: edge_map_update_def RBT_Set.empty_def adj_inv_def map_empty_def
                                           vset_inv_def)

(*
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
*)
definition "edges = [(0::nat, 1::nat), (0, 2), (2, 3), (2,4), (2,1), (1,5), (5,8), (8,7), (7,1),
                     (7,2), (7,4), (4,3), (3,4), (3,3), (9, 8), (8, 1), (4,5), (5,10)]"

definition "G = a_graph edges"
(*
lemmas neighbourhood_def[unfolded G.neighbourhood_def, code]
*)
value edges
value "vertices edges"
value G
value "neighbourhood G"
value "dfs_initial_state (1::nat)"
value "dfs_impl G 9 (dfs_initial_state 0)"
value "dfs_impl G 3 (dfs_initial_state 0)"

hide_const edges G

end