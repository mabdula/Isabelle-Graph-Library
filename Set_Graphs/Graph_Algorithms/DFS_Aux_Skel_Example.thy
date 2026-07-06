theory DFS_Aux_Skel_Example
  imports DFS_Aux_Skel Directed_Set_Graphs.Pair_Graph_RBT
begin

text ‹RBT global interpretation of the undirected-cycle DFS skeleton.
  Mirrors the ‹DFS_Cycles_Example› pattern but wires up ‹DFS_Aux_Skel›
  instead of the original ‹DFS_Aux›.›

global_interpretation auxskel: DFS_Aux_Skel where insert = vset_insert and
 sel = sel and vset_empty = vset_empty and diff = vset_diff and
 lookup = lookup and empty = map_empty and delete = delete and isin = isin and t_set = t_set
and update = update and adjmap_inv = adj_inv and vset_delete = vset_delete
and vset_inv = vset_inv and union = vset_union and inter = vset_inter and G = F and
s = s for F s
defines initial_state_aux_skel = auxskel.initial_state and
find_dircycle_aux = auxskel.aux.DFS_skel_impl and
aux_found_skel = auxskel.aux_found and
neighbourhood_aux = auxskel.Graph.neighbourhood
  using G.Pair_Graph_Specs_axioms RBT.Set2_axioms
  by(auto intro!: DFS_Aux_Skel.intro simp add: edge_map_update_def RBT_Set.empty_def adj_inv_def map_empty_def
                                           vset_inv_def)

text ‹The partial-function unfolding equation with callbacks inlined as a code equation.›
lemmas find_dircycle_aux_code[code] =
  auxskel.aux.DFS_skel_impl.simps[folded find_dircycle_aux_def[folded aux_found_skel_def],
    unfolded auxskel.aux_on_found_def auxskel.aux_on_empty_def auxskel.aux_on_backtrack_def]

text ‹An undirected triangle: vertices 1,2,3 forming a cycle.
  Represented as a symmetric directed graph (both directions for each edge).›
definition "tri_edges = [(1::nat, 2::nat), (2, 1), (2, 3), (3, 2), (1, 3), (3, 1)]"
definition "G_tri = a_graph tri_edges"

text ‹A path graph (a tree): 1-2-3-4. No cycle.›
definition "path_edges = [(1::nat, 2::nat), (2, 1), (2, 3), (3, 2), (3, 4), (4, 3)]"
definition "G_path = a_graph path_edges"

text ‹A graph with an undirected cycle of length 4: 1-2-3-4-1.›
definition "quad_edges = [(1::nat, 2::nat), (2, 1), (2, 3), (3, 2),
                          (3, 4), (4, 3), (4, 1), (1, 4)]"
definition "G_quad = a_graph quad_edges"

value tri_edges
value G_tri
value "initial_state_aux_skel (1::nat)"

text ‹The undirected triangle has a cycle, reported from source 1.›
value "find_dircycle_aux G_tri (initial_state_aux_skel (1::nat))"
value "DFS_dircycle_state.cycle (find_dircycle_aux G_tri (initial_state_aux_skel (1::nat)))"

text ‹The path graph has no cycle.›
value "DFS_dircycle_state.cycle (find_dircycle_aux G_path (initial_state_aux_skel (1::nat)))"

text ‹The 4-cycle has a cycle, found from source 1.›
value "DFS_dircycle_state.cycle (find_dircycle_aux G_quad (initial_state_aux_skel (1::nat)))"

text ‹From source 9 (not in G_tri) we expect the result: no cycle reachable.›
value "DFS_dircycle_state.cycle (find_dircycle_aux G_tri (initial_state_aux_skel (9::nat)))"

hide_const tri_edges path_edges quad_edges G_tri G_path G_quad

end
