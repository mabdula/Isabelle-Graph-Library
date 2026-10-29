theory Index_Algorithms_Main_Theorems
  imports
    "Dinic.Compute_Blocking_Simple"
    "Dinic.DFS_Collect_Backtrack"
    "Dinic.Dinic"
    "Edmonds_Gallai_Decomposition.Edmonds_Gallai_Computation"
    "Edmonds_Weighted_Blossom.Naive_Weighted_Blossom"
    "Graph_Algorithms_Dev.BFS_2"
    "Graph_Algorithms_Dev.BFS_3"
    "Graph_Algorithms_Dev.Bellman_Ford"
    "Graph_Algorithms_Dev.DFS"
    "Graph_Algorithms_Dev.DFS_Cycles"
    "Graph_Algorithms_Dev.DFS_DirCycle"
    "Graph_Algorithms_Dev.Dijkstra"
    "Greedoids.Greedoids_Optimisation"
    "Hopcroft_Karp.Hopcroft_Karp_Top_Loop"
    "Hungarian_Method.Hungarian_Method_Top_Loop"
    "Hungarian_Method.Naive_Primal_Dual"
    "Matroid_Intersection.Matroid_Intersection_Algorithm"
    "Matroid_Intersection.Matroid_Partitioning"
    "Matroid_Intersection.Matroid_Weighted_Intersection_Path_Loop"
    "Matroids_Greedy.Best_In_Greedy"
    "Mincost_Flow_Algorithms.Acyclic_Flow"
    "Mincost_Flow_Algorithms.Network_Simplex_Final"
    "Mincost_Flow_Algorithms.Scaling"
    "Mincost_Flow_Algorithms.Successive_Shortest_Path"
    "Primal_Dual_Bipartite_Matching.AdWords"
    "Primal_Dual_Bipartite_Matching.Ranking_Order_Probabilistic"
    "Push_Relabel.Push_Relabel_Generic"
    "RANKING.Ranking_Probabilistic"
    "Spanning_Trees.Jarnik_Prim"
    "Spanning_Trees.Kruskal_Greedy"
begin

section \<open>Main theorems of the verified algorithms (Table 1)\<close>

text \<open>Index of the paper's listings for: Main theorems of the verified algorithms (Table 1).
  Each entry is machine-checked: the antiquotation resolves iff the named
  entity still exists in the library.\<close>

text \<open>\<^bold>\<open>Listing 53. lemmas DFS_correct_1, DFS_correct_1_strong and DFS_correct_2 (DFS.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Graph_Algorithms/DFS.thy\<close> (line 739, locale DFS_thms).
  Checked reference: @{thm DFS_thms.DFS_correct_1}.\<close>

text \<open>\<^bold>\<open>Listing 54. lemmas DFS_Cycles_correct_1 and DFS_Cycles_correct_2 (DFS_Cycles.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Graph_Algorithms/DFS_Cycles.thy\<close> (line 1076, locale DFS_Cycles).
  Checked reference: @{thm DFS_Cycles.DFS_Cycles_correct_1}.\<close>

text \<open>\<^bold>\<open>Listing 55. theorems DFS_dircycle_sound and DFS_dircycle_complete (DFS_DirCycle.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Graph_Algorithms/DFS_DirCycle.thy\<close> (line 401, locale DFS_dircycle_thms).
  Note: branch dfs_refactor.
  Checked reference: @{thm DFS_dircycle_thms.DFS_dircycle_sound}.\<close>

text \<open>\<^bold>\<open>Listing 56. lemmas BFS_correct_1, BFS_correct_2, BFS_correct_3 and BFS_correct_4 (BFS_2.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Graph_Algorithms/BFS_2.thy\<close> (line 1475, locale BFS).
  Checked reference: @{thm BFS.BFS_correct_1}.\<close>

text \<open>\<^bold>\<open>Listing 57. theorem BFS_par_correct (BFS_3.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Graph_Algorithms/BFS_3.thy\<close> (line 2898, locale BFS_distance_parents).
  Note: branch more_algorithms.
  Checked reference: @{thm BFS_distance_parents.BFS_par_correct}.\<close>

text \<open>\<^bold>\<open>Listing 58. theorem bellman_ford_computes_length_of_optpath (Bellman_Ford.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Graph_Algorithms/Bellman_Ford.thy\<close> (line 1860, locale bellman_ford).
  Checked reference: @{thm bellman_ford.bellman_ford_computes_length_of_optpath}.\<close>

text \<open>\<^bold>\<open>Listing 59. theorem dijkstra_compute_optimal (Dijkstra.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Graph_Algorithms/Dijkstra.thy\<close> (line 1642, locale dijkstra).
  Note: branch more_algorithms.
  Checked reference: @{thm dijkstra.dijkstra_compute_optimal}.\<close>

text \<open>\<^bold>\<open>Listing 60. lemma BestInGreedy_matroid_iff_opt (Best_In_Greedy.thy)\<close>
  In this snapshot: \<^file>\<open>../../Matroids_Greedy/Best_In_Greedy.thy\<close> (line 1462, locale Best_In_Greedy).
  Checked reference: @{thm Best_In_Greedy.BestInGreedy_matroid_iff_opt}.\<close>

text \<open>\<^bold>\<open>Listing 61. corollary kruskal_computes_max_spanning_forest (Kruskal_Greedy.thy)\<close>
  In this snapshot: \<^file>\<open>../../Spanning_Trees/Kruskal_Greedy.thy\<close> (line 981, locale Kruskal_Proof_Matroid_Edges').
  Checked reference: @{thm Kruskal_Proof_Matroid_Edges'.kruskal_computes_max_spanning_forest}.\<close>

text \<open>\<^bold>\<open>Listing 62. theorem greedoid_characterisation (Greedoids_Optimisation.thy)\<close>
  In this snapshot: \<^file>\<open>../../Greedoids/Greedoids_Optimisation.thy\<close> (line 1365, locale greedoid_algorithm).
  Checked reference: @{thm greedoid_algorithm.greedoid_characterisation}.\<close>

text \<open>\<^bold>\<open>Listing 63. theorem jp_maximum_stree (Jarnik_Prim.thy)\<close>
  In this snapshot: \<^file>\<open>../../Spanning_Trees/Jarnik_Prim.thy\<close> (line 497, locale jarnik_prim_correctness).
  Checked reference: @{thm jarnik_prim_correctness.jp_maximum_stree}.\<close>

text \<open>\<^bold>\<open>Listing 64. theorem total_correctness (Successive_Shortest_Path.thy)\<close>
  In this snapshot: \<^file>\<open>../../Mincost_Flow_Algorithms/Successive_Shortest_Path.thy\<close> (line 826, locale SSP).
  Checked reference: @{thm SSP.total_correctness}.\<close>

text \<open>\<^bold>\<open>Listing 65. theorem total_correctness (Scaling.thy)\<close>
  In this snapshot: \<^file>\<open>../../Mincost_Flow_Algorithms/Scaling.thy\<close> (line 922, locale SSP).
  Checked reference: @{thm SSP.total_correctness}.\<close>

text \<open>\<^bold>\<open>Listing 66. lemma dinic_total_correctness (Dinic.thy)\<close>
  In this snapshot: \<^file>\<open>../../Dinic/Dinic.thy\<close> (line 426, locale dinic).
  Checked reference: @{thm dinic.dinic_total_correctness}.\<close>

text \<open>\<^bold>\<open>Listing 67. lemma correctness (Compute_Blocking_Simple.thy)\<close>
  In this snapshot: \<^file>\<open>../../Dinic/Compute_Blocking_Simple.thy\<close> (line 587, locale blocking_simple_thms).
  Checked reference: @{thm blocking_simple_thms.correctness}.\<close>

text \<open>\<^bold>\<open>Listing 68. lemma dfs_backtrack_final (DFS_Collect_Backtrack.thy)\<close>
  In this snapshot: \<^file>\<open>../../Dinic/DFS_Collect_Backtrack.thy\<close> (line 577, locale DFS_thms).
  Checked reference: @{thm DFS_thms.dfs_backtrack_final}.\<close>

text \<open>\<^bold>\<open>Listing 69. theorem network_simplex_correct (Network_Simplex_Final.thy)\<close>
  In this snapshot: \<^file>\<open>../../Mincost_Flow_Algorithms/Network_Simplex_Final.thy\<close> (line 476, locale network_simplex_init).
  Note: branch more_algorithms.
  Checked reference: @{thm network_simplex_init.network_simplex_correct}.\<close>

text \<open>\<^bold>\<open>Listing 70. theorem make_acyclic_correct_unconditional_bflow (Acyclic_Flow.thy)\<close>
  In this snapshot: \<^file>\<open>../../Mincost_Flow_Algorithms/Acyclic_Flow.thy\<close> (line 5446, locale acyclic_flow_impl).
  Note: branch more_algorithms.
  Checked reference: @{thm acyclic_flow_impl.make_acyclic_correct_unconditional_bflow}.\<close>

text \<open>\<^bold>\<open>Listing 71. theorem push_relabel_correct (Push_Relabel_Generic.thy)\<close>
  In this snapshot: \<^file>\<open>../../Push_Relabel/Push_Relabel_Generic.thy\<close> (line 1968, locale push_relabel).
  Note: branch more_algorithms.
  Checked reference: @{thm push_relabel.push_relabel_correct}.\<close>

text \<open>\<^bold>\<open>Listing 72. theorem naive_min_weight_perfect_matching_partial_correctness (Naive_Weighted_Blossom.thy)\<close>
  In this snapshot: \<^file>\<open>../../Edmonds_Weighted_Blossom/Naive_Weighted_Blossom.thy\<close> (line 3702, locale naive_weighted_blossom_with_cleanup).
  Note: branch weighted_blossom.
  Checked reference: @{thm naive_weighted_blossom_with_cleanup.naive_min_weight_perfect_matching_partial_correctness}.\<close>

text \<open>\<^bold>\<open>Listing 73. lemma find_edg_correct (Edmonds_Gallai_Computation.thy)\<close>
  In this snapshot: \<^file>\<open>../../Edmonds_Gallai/Edmonds_Gallai_Computation.thy\<close> (line 570, locale find_aug_path_edg).
  Note: branch weighted_blossom.
  Checked reference: @{thm find_aug_path_edg.find_edg_correct}.\<close>

text \<open>\<^bold>\<open>Listing 74. lemma Hopcroft_Karp_Loop_correct_1 (Hopcroft_Karp_Top_Loop.thy)\<close>
  In this snapshot: \<^file>\<open>../../Hopcroft_Karp/Hopcroft_Karp_Top_Loop.thy\<close> (line 393, locale Hopcroft_Karp_Loop_thms).
  Note: development version.
  Checked reference: @{thm Hopcroft_Karp_Loop_thms.Hopcroft_Karp_Loop_correct_1}.\<close>

text \<open>\<^bold>\<open>Listing 75. theorem hungarian_correctness (Hungarian_Method_Top_Loop.thy)\<close>
  In this snapshot: \<^file>\<open>../../Hungarian_Method/Hungarian_Method_Top_Loop.thy\<close> (line 571, locale hungarian_loop).
  Checked reference: @{thm hungarian_loop.hungarian_correctness}.\<close>

text \<open>\<^bold>\<open>Listing 76. lemma naive_primal_dual_total_correctness (Naive_Primal_Dual.thy)\<close>
  In this snapshot: \<^file>\<open>../../Hungarian_Method/Naive_Primal_Dual.thy\<close> (line 1239, locale naive_primal_dual).
  Checked reference: @{thm naive_primal_dual.naive_primal_dual_total_correctness}.\<close>

text \<open>\<^bold>\<open>Listing 77. theorem ranking_comp_ratio (Ranking_Probabilistic.thy)\<close>
  In this snapshot: \<^file>\<open>../../RANKING/Ranking_Probabilistic.thy\<close> (line 1967, locale wf_ranking).
  Checked reference: @{thm wf_ranking.ranking_comp_ratio}.\<close>

text \<open>\<^bold>\<open>Listing 78. theorem ranking_competitive_ratio (Ranking_Order_Probabilistic.thy)\<close>
  In this snapshot: \<^file>\<open>../../Primal_Dual_Bipartite_Matching/Ranking_Order_Probabilistic.thy\<close> (line 1298).
  Checked reference: @{thm ranking_competitive_ratio}.\<close>

text \<open>\<^bold>\<open>Listing 79. theorem adwords_competitive_ratio (AdWords.thy)\<close>
  In this snapshot: \<^file>\<open>../../Primal_Dual_Bipartite_Matching/AdWords.thy\<close> (line 1286, locale adwords_lp).
  Checked reference: @{thm adwords_lp.adwords_competitive_ratio}.\<close>

text \<open>\<^bold>\<open>Listing 80. lemma matroid_intersection_total_correctness (Matroid_Intersection_Algorithm.thy)\<close>
  In this snapshot: \<^file>\<open>../../Matroid_Intersection/Matroid_Intersection_Algorithm.thy\<close> (line 973, locale unweighted_intersection).
  Checked reference: @{thm unweighted_intersection.matroid_intersection_total_correctness}.\<close>

text \<open>\<^bold>\<open>Listing 81. theorem weighted_matroid_intersection_correct (Matroid_Weighted_Intersection_Path_Loop.thy)\<close>
  In this snapshot: \<^file>\<open>../../Matroid_Intersection/Matroid_Weighted_Intersection_Path_Loop.thy\<close> (line 1144, locale weighted_intersection_path_loop).
  Note: branch more_algorithms.
  Checked reference: @{thm weighted_intersection_path_loop.weighted_matroid_intersection_correct}.\<close>

text \<open>\<^bold>\<open>Listing 82. corollary partition_opt_from_is_max (Matroid_Partitioning.thy)\<close>
  In this snapshot: \<^file>\<open>../../Matroid_Intersection/Matroid_Partitioning.thy\<close> (line 899, locale matroid_partition).
  Note: branch more_algorithms.
  Checked reference: @{thm matroid_partition.partition_opt_from_is_max}.\<close>

end
