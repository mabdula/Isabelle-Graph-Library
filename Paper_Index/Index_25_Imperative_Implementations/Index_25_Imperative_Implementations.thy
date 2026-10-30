theory Index_25_Imperative_Implementations
  imports
    "Data_Structures.Set_Choose"
    "Graph_Algorithms_Dev.DFS_Imperative"
    "Separation_Logic_Imperative_HOL_Partial.Array_Map_Impl"
begin

section \<open>Section 2.5: Imperative Implementations\<close>

text \<open>Index of the paper's listings for: Section 2.5: Imperative Implementations.
  Each entry is machine-checked: the antiquotation resolves iff the named
  entity still exists in the library.\<close>

text \<open>\<^bold>\<open>Listing 101. definition is_iam (Array_Map_Impl.thy)\<close>
  In this snapshot: \<^file>\<open>../../Imperative/Separation_Logic_Imperative_HOL_Partial/Examples/Array_Map_Impl.thy\<close> (line 20).
  Checked reference: @{const is_iam}.\<close>

text \<open>\<^bold>\<open>Listing 102. locale Set_Choose (Set_Choose.thy)\<close>
  In this snapshot: \<^file>\<open>../../Data_Structures/Set_Choose.thy\<close> (line 11).
  Note: branch bfs_refinement.
  Checked reference: @{locale Set_Choose}.\<close>

text \<open>\<^bold>\<open>Listing 103. interpretation iam_dfs: imp_DFS (DFS_Imperative.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Graph_Algorithms/Refinements/DFS_Imperative.thy\<close> (line 242).
  Note: branch bfs_refinement.
  interpretation @{text \<open>iam_dfs: imp_DFS\<close>}.
  Checked reference: @{locale imp_DFS}.\<close>

text \<open>\<^bold>\<open>Listing 104. interpretation hm_dfs: imp_DFS (DFS_Imperative.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Graph_Algorithms/Refinements/DFS_Imperative.thy\<close> (line 257).
  Note: branch bfs_refinement.
  interpretation @{text \<open>hm_dfs: imp_DFS\<close>}.
  Checked reference: @{locale imp_DFS}.\<close>

text \<open>\<^bold>\<open>Listing 105. lemma DFS_imperative_rule (DFS_Imperative.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Graph_Algorithms/Refinements/DFS_Imperative.thy\<close> (line 98).
  Checked reference: @{thm imp_DFS.DFS_imperative_rule}.\<close>

text \<open>\<^bold>\<open>Listing 106. lemma DFS_imperative'_absrl (DFS_Imperative.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Graph_Algorithms/Refinements/DFS_Imperative.thy\<close> (line 216).
  Note: branch bfs_refinement.
  Checked reference: @{thm imp_DFS_thms.DFS_imperative'_absrl}.\<close>

end
