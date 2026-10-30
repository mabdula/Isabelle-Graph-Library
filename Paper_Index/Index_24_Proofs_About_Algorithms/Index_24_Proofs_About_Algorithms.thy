theory Index_24_Proofs_About_Algorithms
  imports
    "Dinic.Dinic"
    "Graph_Algorithms_Dev.BFS_2"
    "Graph_Algorithms_Dev.DFS"
    "Hungarian_Method.Hungarian_Method_Top_Loop"
    "Matroid_Intersection.Matroid_Intersection_Path_Loop"
    "Matroids_Greedy.BestInGreedy_base"
    "Mincost_Flow_Algorithms.Maintain_Forest"
    "Mincost_Flow_Algorithms.Scaling"
    "Mincost_Flow_Algorithms.Send_Flow"
    "Mincost_Flow_Algorithms.Successive_Shortest_Path"
begin

section \<open>Section 2.4: Proofs about Algorithms\<close>

text \<open>Index of the paper's listings for: Section 2.4: Proofs about Algorithms.
  Each entry is machine-checked: the antiquotation resolves iff the named
  entity still exists in the library.\<close>

text \<open>\<^bold>\<open>Listing 83. definition DFS_call_1_conds (DFS.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Graph_Algorithms/DFS.thy\<close> (line 89, locale DFS).
  Checked reference: @{const DFS.DFS_call_1_conds}.\<close>

text \<open>\<^bold>\<open>Listing 84. definition DFS_upd1 (DFS.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Graph_Algorithms/DFS.thy\<close> (line 110, locale DFS).
  Checked reference: @{const DFS.DFS_upd1}.\<close>

text \<open>\<^bold>\<open>Listing 85. lemma DFS_cases (DFS.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Graph_Algorithms/DFS.thy\<close> (line 196, locale DFS).
  Checked reference: @{thm DFS.DFS_cases}.\<close>

text \<open>\<^bold>\<open>Listing 86. lemma DFS_simps (DFS.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Graph_Algorithms/DFS.thy\<close> (line 213, locale DFS).
  Note: the lemma has a fourth conclusion, for the branch \<open>DFS_ret_2_conds\<close>, which the listing
  leaves out.
  Checked reference: @{thm DFS.DFS_simps}.\<close>

text \<open>\<^bold>\<open>Listing 87. lemma DFS_induct (DFS.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Graph_Algorithms/DFS.thy\<close> (line 226, locale DFS).
  Checked reference: @{thm DFS.DFS_induct}.\<close>

text \<open>\<^bold>\<open>Listing 88. lemma DFS_call_1_conds (DFS.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Graph_Algorithms/DFS.thy\<close> (line 101, locale DFS).
  Checked reference: @{thm DFS.DFS_call_1_conds}.\<close>

text \<open>\<^bold>\<open>Listing 89. lemma invar_1_holds_1 (DFS.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Graph_Algorithms/DFS.thy\<close> (line 315, locale DFS_thms).
  Checked reference: @{thm DFS_thms.invar_1_holds_1}.\<close>

text \<open>\<^bold>\<open>Listing 90. lemma invar_1_holds (DFS.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Graph_Algorithms/DFS.thy\<close> (line 329, locale DFS_thms).
  Checked reference: @{thm DFS_thms.invar_1_holds}.\<close>

text \<open>\<^bold>\<open>Listing 91. collections of theorems (named_theorems) (DFS.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Graph_Algorithms/DFS.thy\<close> (lines 23 to 30).
  Checked references: @{thm DFS.call_cond_elims}, @{thm DFS.call_cond_intros},
  @{thm DFS.ret_holds_intros}, @{thm DFS.invar_props_intros}, @{thm DFS.invar_props_elims},
  @{thm DFS.invar_holds_intros}, @{thm DFS.state_rel_intros}, @{thm DFS.state_rel_holds_intros}.\<close>

text \<open>\<^bold>\<open>Listing 92. lemma BFS_induct (BFS_2.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Graph_Algorithms/BFS_2.thy\<close> (line 246, locale BFS).
  Checked reference: @{thm BFS.BFS_induct}.\<close>

text \<open>\<^bold>\<open>Listing 93. lemma BestInGreedy_induct (Best_In_Greedy.thy)\<close>
  In this snapshot: \<^file>\<open>../../Matroids_Greedy/BestInGreedy_base.thy\<close> (line 181, locale BestInGreedy_base).
  Note: the lemma is called \<open>BestInGreedy_base_induct\<close> in this snapshot.
  Checked reference: @{thm BestInGreedy_base.BestInGreedy_base_induct}.\<close>

text \<open>\<^bold>\<open>Listing 94. lemma SSP_induct (Successive_Shortest_Path.thy)\<close>
  In this snapshot: \<^file>\<open>../../Mincost_Flow_Algorithms/Successive_Shortest_Path.thy\<close> (line 258, locale SSP).
  Checked reference: @{thm SSP.SSP_induct}.\<close>

text \<open>\<^bold>\<open>Listing 95. lemma Scaling_induct (Scaling.thy)\<close>
  In this snapshot: \<^file>\<open>../../Mincost_Flow_Algorithms/Scaling.thy\<close> (line 1309, locale Scaling).
  Checked reference: @{thm Scaling.Scaling_induct}.\<close>

text \<open>\<^bold>\<open>Listing 96. lemma send_flow_induct (Send_Flow.thy)\<close>
  In this snapshot: \<^file>\<open>../../Mincost_Flow_Algorithms/Send_Flow.thy\<close> (line 421, locale send_flow_spec).
  Checked reference: @{thm send_flow_spec.send_flow_induct}.\<close>

text \<open>\<^bold>\<open>Listing 97. lemma maintain_forest_induct (Maintain_Forest.thy)\<close>
  In this snapshot: \<^file>\<open>../../Mincost_Flow_Algorithms/Maintain_Forest.thy\<close> (line 331, locale maintain_forest).
  Checked reference: @{thm maintain_forest.maintain_forest_induct}.\<close>

text \<open>\<^bold>\<open>Listing 98. lemma hungarian_loop_induct (Hungarian_Method_Top_Loop.thy)\<close>
  In this snapshot: \<^file>\<open>../../Hungarian_Method/Hungarian_Method_Top_Loop.thy\<close> (line 175, locale hungarian_loop_spec).
  Checked reference: @{thm hungarian_loop_spec.hungarian_loop_induct}.\<close>

text \<open>\<^bold>\<open>Listing 99. lemma dinic_induct (Dinic.thy)\<close>
  In this snapshot: \<^file>\<open>../../Dinic/Dinic.thy\<close> (line 99, locale dinic_spec).
  Checked reference: @{thm dinic_spec.dinic_induct}.\<close>

text \<open>\<^bold>\<open>Listing 100. lemma matroid_intersection_induct (Matroid_Intersection_Algorithm.thy)\<close>
  In this snapshot: \<^file>\<open>../../Matroid_Intersection/Matroid_Intersection_Path_Loop.thy\<close> (line 140, locale unweighted_intersection_path_loop_spec).
  Note: paper: Matroid_Intersection_Algorithm.thy; in this snapshot: Matroid_Intersection_Path_Loop.thy.
  Checked reference: @{thm unweighted_intersection_path_loop_spec.matroid_intersection_induct}.\<close>

end
