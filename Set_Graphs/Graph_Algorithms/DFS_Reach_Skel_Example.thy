theory DFS_Reach_Skel_Example
  imports DFS_Reach_Skel Directed_Set_Graphs.Pair_Graph_RBT
begin

global_interpretation dfs: DFS_Reach where insert = vset_insert and
 sel = sel and  vset_empty = vset_empty and  diff = vset_diff and
 lookup = lookup and empty = map_empty and delete=delete and isin = isin and t_set=t_set
and update=update and adjmap_inv = adj_inv and vset_delete= vset_delete
and vset_inv = vset_inv and union=vset_union and inter=vset_inter and G = F and
t = t and s = s  for F t s
defines  dfs_initial_state = dfs.initial_state and
neighbourhood=dfs.Graph.neighbourhood and
reach_found = dfs.reach_found and
dfs_impl = dfs.reach.DFS_skel_impl  and
add_edge = dfs.Graph.add_edge and
delete_edge = dfs.Graph.delete_edge and
from_list = dfs.Graph.from_list
  using G.Pair_Graph_Specs_axioms RBT.Set2_axioms
  by(auto intro!: DFS_Reach.intro  simp add: edge_map_update_def RBT_Set.empty_def adj_inv_def map_empty_def
                                           vset_inv_def)

text ‹The partial-function unfolding equation cannot serve as a code equation directly (its head
carries the instantiated callbacks as compound arguments), so we restate it once at the concrete
instance, with the callbacks inlined.›
lemmas dfs_impl_code[code] =
  dfs.reach.DFS_skel_impl.simps[folded dfs_impl_def[folded reach_found_def],
    unfolded dfs.reach_on_found_def dfs.reach_on_empty_def dfs.reach_on_backtrack_def]

definition "edges = [(0::nat, 1::nat), (0, 2), (2, 3), (2,4), (2,1), (1,5), (5,8), (8,7), (7,1),
                     (7,2), (7,4), (4,3), (3,4), (3,3), (9, 8), (8, 1), (4,5), (5,10)]"

definition "G = a_graph edges"

value edges
value "vertices edges"
value G
value "neighbourhood G"
value "dfs_initial_state (1::nat)"
value "dfs_impl G 9 (dfs_initial_state 0)"
value "dfs_impl G 3 (dfs_initial_state 0)"

hide_const edges G

end
