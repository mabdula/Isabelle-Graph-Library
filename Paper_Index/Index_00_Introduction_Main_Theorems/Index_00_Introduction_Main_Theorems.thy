theory Index_00_Introduction_Main_Theorems
  imports
    "Blossom_Executable.Find_Max_Matching"
    "Graph_Algorithms_Dev.BFS_2"
    "Graph_Algorithms_Dev.DFS"
    "Mincost_Flow_Algorithms.Orlins"
begin

section \<open>Main theorems cited in the introduction (Section 2 opening)\<close>

text \<open>Index of the paper's listings for: Main theorems cited in the introduction (Section 2 opening).
  Each entry is machine-checked: the antiquotation resolves iff the named
  entity still exists in the library.\<close>

text \<open>\<^bold>\<open>Listing 1. theorem initial_state_orlins_dom_and_results (Orlins.thy)\<close>
  In this snapshot: \<^file>\<open>../../Mincost_Flow_Algorithms/Orlins.thy\<close> (line 2814, locale orlins).
  Checked reference: @{thm orlins.initial_state_orlins_dom_and_results}.\<close>

text \<open>\<^bold>\<open>Listing 2. lemma find_max_matching_works (Blossom_Algo_Main_Loop.thy)\<close>
  In this snapshot: \<^file>\<open>../../Edmonds_Blossom_Executable/Find_Max_Matching.thy\<close> (line 317, locale Find_Max_Matching_thms).
  Note: the lemma of the listing is in Blossom_Algo_Main_Loop.thy of the session
  Edmonds_Blossom_Algorithm, which is not part of this artefact. This entry points at the
  corresponding theorem of the executable version instead: for a graph and a matching given by
  their implementations, it states \<open>max_card_matching\<close> of the abstractions of the graph and
  of the computed matching, where the listing states the same four properties for the abstract
  algorithm.
  Checked reference: @{thm Find_Max_Matching_thms.Find_Max_Matching_correct_1}.\<close>

text \<open>\<^bold>\<open>Listing 3. lemma DFS_correct_1 (DFS.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Graph_Algorithms/DFS.thy\<close> (line 739, locale DFS_thms).
  Note: FDS book version.
  Checked reference: @{thm DFS_thms.DFS_correct_1}.\<close>

text \<open>\<^bold>\<open>Listing 4. lemma BFS_correct_3 (BFS_2.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Graph_Algorithms/BFS_2.thy\<close> (line 1488, locale BFS).
  Note: FDS book version.
  Checked reference: @{thm BFS.BFS_correct_3}.\<close>

end
