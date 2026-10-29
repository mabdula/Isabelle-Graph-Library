theory Index_21_Graph_Models_And_Reasoning
  imports
    "Basic_Matching.Berge"
    "Berge_Formula.Berge_Formula"
    "Directed_Set_Graphs.Awalk"
    "Directed_Set_Graphs.Awalk_Defs"
    "Directed_Set_Graphs.Multigraph"
    "Directed_Set_Graphs.Pair_Graph"
    "Directed_Set_Graphs.Vwalk"
    "Edmonds_Gallai_Decomposition.Edmonds_Gallai"
    "Undirected_Set_Graphs.Connected_Components"
    "Undirected_Set_Graphs.Pair_Graph_Berge_Adaptor"
    "Undirected_Set_Graphs.Paths"
begin

section \<open>Section 2.1: Mathematical Models of Graphs and Reasoning Principles\<close>

text \<open>Index of the paper's listings for: Section 2.1: Mathematical Models of Graphs and Reasoning Principles.
  Each entry is machine-checked: the antiquotation resolves iff the named
  entity still exists in the library.\<close>

text \<open>\<^bold>\<open>Listing 5. inductive vwalk (Vwalk.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Directed_Graphs/Vwalk.thy\<close> (line 13).
  Checked reference: @{const vwalk}.\<close>

text \<open>\<^bold>\<open>Listing 6. definition awalk (Awalk_Defs.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Directed_Graphs/Awalk_Defs.thy\<close> (line 12).
  Checked reference: @{const awalk}.\<close>

text \<open>\<^bold>\<open>Listing 7. definition walk_betw (Paths.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Undirected_Graphs/Paths.thy\<close> (line 105).
  Checked reference: @{const walk_betw}.\<close>

text \<open>\<^bold>\<open>Listing 8. lemma walk_betw_iff_vwalk_bet (Pair_Graph_Berge_Adaptor.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Undirected_Graphs/Pair_Graph_Berge_Adaptor.thy\<close> (line 77, locale graph_abs).
  Checked reference: @{thm graph_abs.walk_betw_iff_vwalk_bet}.\<close>

text \<open>\<^bold>\<open>Listing 9. definition multigraph_path (Multigraph.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Directed_Graphs/Multigraph.thy\<close> (line 54, locale multigraph_spec).
  Checked reference: @{const multigraph_spec.multigraph_path}.\<close>

text \<open>\<^bold>\<open>Listing 10. theorem component_has_path_distinct (Connected_Components.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Undirected_Graphs/Connected_Components.thy\<close> (line 1856).
  Checked reference: @{thm component_has_path_distinct}.\<close>

text \<open>\<^bold>\<open>Listing 11. lemma in_insert_connected_componentE (Connected_Components.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Undirected_Graphs/Connected_Components.thy\<close> (line 1385).
  Checked reference: @{thm in_insert_connected_componentE}.\<close>

text \<open>\<^bold>\<open>Listing 12. lemma walk_betw_insertE (Paths.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Undirected_Graphs/Paths.thy\<close> (line 304).
  Checked reference: @{thm walk_betw_insertE}.\<close>

text \<open>\<^bold>\<open>Listing 13. lemma reachable_insertE (Paths.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Undirected_Graphs/Paths.thy\<close> (line 1692).
  Checked reference: @{thm reachable_insertE}.\<close>

text \<open>\<^bold>\<open>Listing 14. lemma vwalk_bet_insertE (Vwalk.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Directed_Graphs/Vwalk.thy\<close> (line 1242).
  Checked reference: @{thm vwalk_bet_insertE}.\<close>

text \<open>\<^bold>\<open>Listing 15. lemma walk_betw_unionE (Paths.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Undirected_Graphs/Paths.thy\<close> (line 401).
  Checked reference: @{thm walk_betw_unionE}.\<close>

text \<open>\<^bold>\<open>Listing 16. lemma reachability_split (Paths.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Undirected_Graphs/Paths.thy\<close> (line 1716).
  Checked reference: @{thm reachability_split}.\<close>

text \<open>\<^bold>\<open>Listing 17. lemma induct_walk_betw (Paths.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Undirected_Graphs/Paths.thy\<close> (line 197).
  Checked reference: @{thm induct_walk_betw}.\<close>

text \<open>\<^bold>\<open>Listing 18. lemma induct_vwalk_bet (Vwalk.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Directed_Graphs/Vwalk.thy\<close> (line 416).
  Checked reference: @{thm induct_vwalk_bet}.\<close>

text \<open>\<^bold>\<open>Listing 19. lemma vwalk_alt_induct (Vwalk.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Directed_Graphs/Vwalk.thy\<close> (line 484).
  Checked reference: @{thm vwalk_alt_induct}.\<close>

text \<open>\<^bold>\<open>Listing 20. lemma awalk_induct (Awalk.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Directed_Graphs/Awalk.thy\<close> (line 892).
  Checked reference: @{thm awalk_induct}.\<close>

text \<open>\<^bold>\<open>Listing 21. lemma multigraph_path_induct (Multigraph.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Directed_Graphs/Multigraph.thy\<close> (line 194, locale multigraph).
  Checked reference: @{thm multigraph.multigraph_path_induct}.\<close>

text \<open>\<^bold>\<open>Listing 22. lemma reachable_induct (Pair_Graph.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Directed_Graphs/Pair_Graph.thy\<close> (line 92).
  Checked reference: @{thm reachable_induct}.\<close>

text \<open>\<^bold>\<open>Listing 23. lemma converse_reachable_induct (Pair_Graph.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Directed_Graphs/Pair_Graph.thy\<close> (line 99).
  Checked reference: @{thm converse_reachable_induct}.\<close>

text \<open>\<^bold>\<open>Listing 24. lemma vwalk_bet_to_distinct_induct (Vwalk.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Directed_Graphs/Vwalk.thy\<close> (line 1040).
  Checked reference: @{thm vwalk_bet_to_distinct_induct}.\<close>

text \<open>\<^bold>\<open>Listing 25. theorem Berge (Berge.thy)\<close>
  In this snapshot: \<^file>\<open>../../Basic_Matching/Berge.thy\<close> (line 744).
  Checked reference: @{thm Berge}.\<close>

text \<open>\<^bold>\<open>Listing 26. lemma berge_formula (Berge_Formula.thy)\<close>
  In this snapshot: \<^file>\<open>../../Berge_Formula/Berge_Formula.thy\<close> (line 858, locale add_vertices).
  Checked reference: @{thm add_vertices.berge_formula}.\<close>

text \<open>\<^bold>\<open>Listing 27. theorem edmonds_gallai_decomposition_all (Edmonds_Gallai.thy)\<close>
  In this snapshot: \<^file>\<open>../../Edmonds_Gallai/Edmonds_Gallai.thy\<close> (line 1429).
  Note: branch weighted_blossom on a development fork.
  Checked reference: @{thm edmonds_gallai_decomposition_all}.\<close>

end
