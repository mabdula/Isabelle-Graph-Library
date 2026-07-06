theory DFS_DirCycle_Example
  imports DFS_DirCycle Directed_Set_Graphs.Pair_Graph_RBT
begin

global_interpretation dircycle: DFS_dircycle where insert = vset_insert and
 sel = sel and vset_empty = vset_empty and diff = vset_diff and
 lookup = lookup and empty = map_empty and delete = delete and isin = isin and t_set = t_set
and update = update and adjmap_inv = adj_inv and vset_delete = vset_delete
and vset_inv = vset_inv and union = vset_union and inter = vset_inter and G = F and
s = s for F s
defines dircycle_initial_state = dircycle.dircycle_initial_state and
find_dircycle = dircycle.dc.DFS_skel_impl and
cyc_found = dircycle.cyc_found and
neighbourhood = dircycle.Graph.neighbourhood
  using G.Pair_Graph_Specs_axioms RBT.Set2_axioms
  by(auto intro!: DFS_dircycle.intro simp add: edge_map_update_def RBT_Set.empty_def adj_inv_def map_empty_def
                                           vset_inv_def)

text ‹The partial-function unfolding equation cannot serve as a code equation directly (its head
carries the instantiated callbacks as compound arguments), so we restate it once at the concrete
instance, with the callbacks inlined.›
lemmas find_dircycle_code[code] =
  dircycle.dc.DFS_skel_impl.simps[folded find_dircycle_def[folded cyc_found_def],
    unfolded dircycle.cyc_on_found_def dircycle.cyc_on_empty_def dircycle.cyc_on_backtrack_def]

text ‹A digraph containing the directed cycle 1→2→3→1 (plus a tail 3→4→5).›
definition "cyc_edges = [(1::nat, 2::nat), (2, 3), (3, 1), (3, 4), (4, 5)]"
definition "G_cyc = a_graph cyc_edges"

text ‹A DAG on the same vertices: the diamond 1→2→4, 1→3→4, then 4→5. No directed cycle.›
definition "dag_edges = [(1::nat, 2::nat), (1, 3), (2, 4), (3, 4), (4, 5)]"
definition "G_dag = a_graph dag_edges"

text ‹A self-loop is a directed cycle and is reported.›
definition "loop_edges = [(1::nat, 1::nat), (1, 2)]"
definition "G_loop = a_graph loop_edges"

text ‹A 2-cycle between 1 and 2 is a genuine directed cycle: unlike the undirected DFS (which
excludes the stack parent), the directed instance reports it.›
definition "two_cycle_edges = [(1::nat, 2::nat), (2, 1)]"
definition "G_two = a_graph two_cycle_edges"

value cyc_edges
value G_cyc
value "dircycle_initial_state (1::nat)"

value "find_dircycle G_cyc (dircycle_initial_state (1::nat))"

text ‹The cycle 1→2→3→1 is found ...›
value "DFS_dircycle_state.cycle (find_dircycle G_cyc (dircycle_initial_state (1::nat)))"
text ‹... but from source 4 only the tail 4→5 is reachable, so no cycle is seen (single-source!).›
value "DFS_dircycle_state.cycle (find_dircycle G_cyc (dircycle_initial_state (4::nat)))"
text ‹The DAG is cycle-free.›
value "DFS_dircycle_state.cycle (find_dircycle G_dag (dircycle_initial_state (1::nat)))"
text ‹Self-loops and 2-cycles are directed cycles and are reported.›
value "DFS_dircycle_state.cycle (find_dircycle G_loop (dircycle_initial_state (1::nat)))"
value "DFS_dircycle_state.cycle (find_dircycle G_two (dircycle_initial_state (1::nat)))"

hide_const cyc_edges dag_edges loop_edges two_cycle_edges G_cyc G_dag G_loop G_two

end

