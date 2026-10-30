theory Index_26_Other_Methodological_Points
  imports
    "Flow_Theory.Cost_Optimality"
    "Flow_Theory.Hitchcock_Reduction"
    "Matroid_Intersection.Max_Bipartite_Matching_Matroid"
    "Mincost_Flow_Algorithms.Orlins_Time"
    "Mincost_Flow_Algorithms.Path_Aug_Opt"
    "Spanning_Trees.Kruskal_Functional"
begin

section \<open>Section 2.6: Other Methodological Points\<close>

text \<open>Index of the paper's listings for: Section 2.6: Other Methodological Points.
  Each entry is machine-checked: the antiquotation resolves iff the named
  entity still exists in the library.\<close>

text \<open>\<^bold>\<open>Listing 107. global_interpretation Kruskal_Greedy: BestInGreedy_exec (Kruskal_Functional.thy)\<close>
  In this snapshot: \<^file>\<open>../../Spanning_Trees/Kruskal_Functional.thy\<close> (line 235).
  The constant defined as \<open>kruskal'\<close> is \<open>Kruskal_Greedy.BestInGreedy_exec\<close>.
  global_interpretation @{text \<open>Kruskal_Greedy: BestInGreedy_exec\<close>}.
  Checked reference: @{locale BestInGreedy_exec}.\<close>

text \<open>\<^bold>\<open>Listing 108. theorem solution (Max_Bipartite_Matching_Matroid.thy)\<close>
  In this snapshot: \<^file>\<open>../../Matroid_Intersection/Applications/Max_Bipartite_Matching_Matroid.thy\<close> (line 1545, in an unnamed context).
  Note: the field \<open>sol\<close> of the state is called \<open>solution\<close> in this snapshot.
  Checked reference: @{thm Max_Bipartite_Matching_Matroid.solution}.\<close>

text \<open>\<^bold>\<open>Listing 109. definition local_indep_oracle (Kruskal_Greedy.thy)\<close>
  In this snapshot: \<^file>\<open>../../Spanning_Trees/Kruskal_Functional.thy\<close> (line 218, locale Oracle).
  Checked reference: @{const Oracle.local_indep_oracle}.\<close>

text \<open>\<^bold>\<open>Listing 110. theorem reduction_of_min_cost_flow_to_hitchcock_general (Hitchcock_Reduction.thy)\<close>
  In this snapshot: \<^file>\<open>../../Flow_Theory/Hitchcock_Reduction.thy\<close> (line 72).
  Checked reference: @{thm reduction_of_min_cost_flow_to_hitchcock_general}.\<close>

text \<open>\<^bold>\<open>Listing 111. corollary correctness_of_implementation_success (Usage_Capacitated.thy)\<close>
  Indexed in \<^file>\<open>Index_26_Usage_Capacitated.thy\<close>: \<open>Usage_Capacitated\<close> imports
  \<open>Bellman_Ford_Example\<close>, whose order on pairs clashes with the one of
  \<open>HOL-Library.Product_Lexorder\<close> that the theories of Listings 107 to 109 import.\<close>

text \<open>\<^bold>\<open>Listing 112. corollary is_opt_iff_no_augcycle (Cost_Optimality.thy)\<close>
  In this snapshot: \<^file>\<open>../../Flow_Theory/Cost_Optimality.thy\<close> (line 634, locale cost_flow_network).
  Checked reference: @{thm cost_flow_network.is_opt_iff_no_augcycle}.\<close>

text \<open>\<^bold>\<open>Listing 113. theorem path_aug_opt_pres (Path_Aug_Opt.thy)\<close>
  In this snapshot: \<^file>\<open>../../Mincost_Flow_Algorithms/Path_Aug_Opt.thy\<close> (line 2435, locale cost_flow_network).
  Checked reference: @{thm cost_flow_network.path_aug_opt_pres}.\<close>

text \<open>\<^bold>\<open>Listing 114. locale orlins_time (Orlins_Time.thy)\<close>
  In this snapshot: \<^file>\<open>../../Mincost_Flow_Algorithms/Orlins_Time.thy\<close> (line 13).
  Checked reference: @{locale orlins_time}.\<close>

text \<open>\<^bold>\<open>Listing 115. theorem running_time_initial (Orlins_Time.thy)\<close>
  In this snapshot: \<^file>\<open>../../Mincost_Flow_Algorithms/Orlins_Time.thy\<close> (line 1727, locale orlins_time).
  Checked reference: @{thm orlins_time.running_time_initial}.\<close>

end
