theory Index_23_Modelling_Algorithms
  imports
    "Blossom_Executable.Find_Max_Matching"
    "Directed_Set_Graphs.Multigraph"
    "Graph_Algorithms_Dev.BFS_2"
    "Graph_Algorithms_Dev.DFS"
begin

section \<open>Section 2.3: Modelling Algorithms\<close>

text \<open>Index of the paper's listings for: Section 2.3: Modelling Algorithms.
  Each entry is machine-checked: the antiquotation resolves iff the named
  entity still exists in the library.\<close>

text \<open>\<^bold>\<open>Listing 48. locale multigraph_spec (Multigraph.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Directed_Graphs/Multigraph.thy\<close> (line 11).
  Checked reference: @{locale multigraph_spec}.\<close>

text \<open>\<^bold>\<open>Listing 49. function DFS (DFS.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Graph_Algorithms/DFS.thy\<close> (line 35).
  Checked reference: @{const DFS.DFS}.\<close>

text \<open>\<^bold>\<open>Listing 50. record DFS_state (DFS.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Graph_Algorithms/DFS.thy\<close> (line 19).
  Checked reference: @{type DFS_state}.\<close>

text \<open>\<^bold>\<open>Listing 51. locale find_max_match (Blossom_Algo_Main_Loop.thy)\<close>
  In this snapshot: \<^file>\<open>../../Edmonds_Blossom_Executable/Find_Max_Matching.thy\<close> (line 32).
  Note: paper: locale find_max_match (Blossom_Algo_Main_Loop.thy); in-tree name Find_Max_Matching.
  Checked reference: @{locale Find_Max_Matching}.\<close>

text \<open>\<^bold>\<open>Listing 52. locale BFS (BFS_2.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Graph_Algorithms/BFS_2.thy\<close> (line 15).
  Checked reference: @{locale BFS}.\<close>

end
