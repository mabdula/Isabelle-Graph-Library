theory DFS_CB_Skel_Example
  imports DFS_CB_Skel Directed_Set_Graphs.Pair_Graph_RBT
begin

text ‹Instantiation of the dead-end collecting DFS (skeleton instance) with Red-Black Trees.›

global_interpretation dfs: DFS_CB
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
  defines  dfs_backtrack_initial_state = dfs.initial_state
    and    neighbourhood = dfs.Graph.neighbourhood
    and    cb_found = dfs.cb_found
    and    dfs_del_dead_impl = dfs.cb.DFS_skeleton_impl
    and    add_edge = dfs.Graph.add_edge
    and    delete_edge = dfs.Graph.delete_edge
  using G.Pair_Graph_Specs_axioms RBT.Set2_axioms
  by(auto intro!: DFS_CB.intro
        simp add: edge_map_update_def RBT_Set.empty_def adj_inv_def map_empty_def
                                           vset_inv_def)

text ‹The partial-function unfolding equation cannot serve as a code equation directly (its head
carries the instantiated callbacks as compound arguments), so we restate it once at the concrete
instance, with the callbacks inlined.›
lemmas dfs_del_dead_impl_code[code] =
  dfs.cb.DFS_skeleton_impl.simps[folded dfs_del_dead_impl_def[folded cb_found_def],
    unfolded dfs.cb_on_found_def dfs.cb_on_empty_def dfs.cb_on_backtrack_def]

definition "edges = [(0::nat, 1::nat), (0, 2), (2, 3), (2,4), (1,5), (5,8), (8,7),
                     (7,2), (7,4), (0, 4), (4, 10), (4,3), (9, 8), (8, 10), (4,5), (5,10)]"

definition "G = a_graph edges"

value edges
value "vertices edges"
value G
value "neighbourhood G"
text ‹The two runs below exercise the executable dead-end-collecting DFS. (The bare initial state is
not displayed via value: the fresh backtrack field's polymorphic list element type has no term_of
instance for direct printing; the concrete runs below fix the type and evaluate.)›
value "dfs_del_dead_impl G 2 (dfs_backtrack_initial_state 0)"
value "dfs_del_dead_impl G 10 (dfs_backtrack_initial_state 0)"

end

