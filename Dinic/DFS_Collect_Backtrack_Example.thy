theory DFS_Collect_Backtrack_Example                 
  imports DFS_Collect_Backtrack Directed_Set_Graphs.Pair_Graph_RBT
begin

text \<open>Instantion of the dead-end collecting DFS with Red-Back Trees.\<close>

global_interpretation dfs: DFS 
  where insert = vset_insert 
    and sel = sel 
    and vset_empty = vset_empty 
    and diff = vset_diff 
    and lookup = lookup 
    and empty = map_empty 
    and delete = delete 
    and isin = isin 
    and t_set = t_set
    and update = update 
    and adjmap_inv = adj_inv 
    and vset_delete = vset_delete
    and vset_inv = vset_inv 
    and union = vset_union 
    and inter = vset_inter 
    and G = F 
    and t = t 
    and s = s  for F t s
  defines  dfs_backtrack_initial_state = dfs.dfs_backtrack_initial_state
    and    neighbourhood=dfs.Graph.neighbourhood
    and    dfs_del_dead_impl = dfs.DFS_collect_backtrack_impl 
    and    add_edge = dfs.Graph.add_edge
    and    delete_edge = dfs.Graph.delete_edge
  using G.Pair_Graph_Specs_axioms RBT.Set2_axioms
  by(auto intro!: DFS.intro  
        simp add: edge_map_update_def RBT_Set.empty_def adj_inv_def map_empty_def
                                           vset_inv_def)

lemma empty_digraph_abs: "dfs.Graph.digraph_abs vset_empty = {}"
  by (metis G.digraph_abs_empty RBT_Set.empty_def)

thm Pair_Graph_Specs.add_edge_def

definition "edges = [(0::nat, 1::nat), (0, 2), (2, 3), (2,4), (1,5), (5,8), (8,7),
                     (7,2), (7,4), (0, 4), (4, 10), (4,3), (9, 8), (8, 10), (4,5), (5,10)]"

definition "G = a_graph edges"

value edges
value "vertices edges"
value G
value "neighbourhood G"
value "dfs_backtrack_initial_state (1::nat)"
value "dfs_del_dead_impl G 2 (dfs_backtrack_initial_state 0)"
value "dfs_del_dead_impl G 10 (dfs_backtrack_initial_state 0)"

(*hide_const edges G*)
end