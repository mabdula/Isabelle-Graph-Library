theory Index_22_Implementing_Graphs
  imports
    "Data_Structures.Iterable_Set_Specs"
    "Directed_Set_Graphs.CSR_Graph"
    "Directed_Set_Graphs.Edge_Iterators"
    "Directed_Set_Graphs.Multigraph"
    "Directed_Set_Graphs.Pair_Graph"
    "Directed_Set_Graphs.Pair_Graph_AVL"
    "Directed_Set_Graphs.Pair_Graph_Imperative"
    "Directed_Set_Graphs.Pair_Graph_Library_Adaptor"
    "Directed_Set_Graphs.Pair_Graph_RBT"
    "Directed_Set_Graphs.Pair_Graph_Specs"
    "Graph_Algorithms_Dev.DFS_Imperative"
    "Graph_Theory.Digraph"
    "Mincost_Flow_Algorithms.Orlins_Preparation"
    "Undirected_Set_Graphs.Pair_Graph_U_Specs"
    "Undirected_Set_Graphs.Undirected_Set_Graphs"
begin

section \<open>Section 2.2: Implementing Graphs\<close>

text \<open>Index of the paper's listings for: Section 2.2: Implementing Graphs.
  Each entry is machine-checked: the antiquotation resolves iff the named
  entity still exists in the library.\<close>

text \<open>\<^bold>\<open>Listing 28. locale wf_digraph (Digraph.thy)\<close>
  Location: Digraph.thy (AFP entry (Graph_Theory)).
  Table 4 also names the locale @{locale nomulti_digraph} of the same theory.
  Checked references: @{locale wf_digraph}, @{locale nomulti_digraph}.\<close>

text \<open>\<^bold>\<open>Listing 29. locale multigraph (Multigraph.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Directed_Graphs/Multigraph.thy\<close> (line 125).
  Checked reference: @{locale multigraph}.\<close>

text \<open>\<^bold>\<open>Listing 30. definition dVs (Pair_Graph.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Directed_Graphs/Pair_Graph.thy\<close> (line 17).
  Checked reference: @{const dVs}.\<close>

text \<open>\<^bold>\<open>Listing 31. locale graph_abs (Undirected_Set_Graphs.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Undirected_Graphs/Undirected_Set_Graphs.thy\<close> (line 747).
  Checked reference: @{locale graph_abs}.\<close>

text \<open>\<^bold>\<open>Listing 32. locale outgoing_edge_iterator (Acyclic_Flow.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Directed_Graphs/Edge_Iterators.thy\<close> (line 14).
  Note: paper locates it in Acyclic_Flow.thy (branch more_algorithms); in this snapshot: Edge_Iterators.thy.
  Checked reference: @{locale outgoing_edge_iterator}.\<close>

text \<open>\<^bold>\<open>Listing 33. locale Pair_Graph_Specs (Pair_Graph_Specs.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Directed_Graphs/Pair_Graph_Specs.thy\<close> (line 243).
  Note: in this snapshot the vertex set operations enter through @{locale Pair_Graph_Specs_Read_Only}
  instead of the parent \<open>vset: Set_Choose\<close> of the listing.
  Checked reference: @{locale Pair_Graph_Specs}.\<close>

text \<open>\<^bold>\<open>Listing 34. locale Pair_Graph_U_Specs (Pair_Graph_U_Specs.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Undirected_Graphs/Pair_Graph_U_Specs.thy\<close> (line 464).
  Note: in this snapshot the locale has the further parent \<open>Pair_Graph_U_Specs_Read_Only\<close>.
  Table 4 also names its abstraction \<open>ugraph_abs\<close> (line 57, locale Pair_Graph_U_Specs_Read_Only).
  Checked references: @{locale Pair_Graph_U_Specs}, @{const Pair_Graph_U_Specs_Read_Only.ugraph_abs}.\<close>

text \<open>\<^bold>\<open>Listing 35. locale csr_graph (CSR_Graph.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Directed_Graphs/CSR_Graph_Spec.thy\<close> (line 344).
  Note: branch more_algorithms. In this snapshot the locale is @{locale csr_ranges} with the range
  of a vertex \<open>v\<close> ending at \<open>B ! Suc v\<close>. It has the assumptions of the listing except that it
  asks the entries of each range to be distinct, not the whole list \<open>E\<close>, and the sort \<open>heap\<close>
  is only required by its imperative extension \<open>csr_graph_imp\<close> in \<open>CSR_Graph.thy\<close>.
  Checked reference: @{locale csr_graph}.\<close>

text \<open>\<^bold>\<open>Listing 36. interpretation G: Pair_Graph_Specs (Pair_Graph_RBT.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Directed_Graphs/Pair_Graph_RBT.thy\<close> (line 54).
  interpretation @{text \<open>G: Pair_Graph_Specs\<close>} with red-black trees.
  Checked reference: @{locale Pair_Graph_Specs}.\<close>

text \<open>\<^bold>\<open>Listing 37. interpretation G: Pair_Graph_Specs (Pair_Graph_AVL.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Directed_Graphs/Pair_Graph_AVL.thy\<close> (line 60).
  interpretation @{text \<open>G: Pair_Graph_Specs\<close>} with AVL trees.
  Checked reference: @{locale Pair_Graph_Specs}.\<close>

text \<open>\<^bold>\<open>Listing 38. locale Pair_Graph_Imperative (Pair_Graph_Imperative.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Directed_Graphs/Refinements/Pair_Graph_Imperative.thy\<close> (line 13).
  Table 4 also names its abstraction \<open>graph_assn\<close> (line 34).
  Checked references: @{locale Pair_Graph_Imperative}, @{const Pair_Graph_Imperative.graph_assn}.\<close>

text \<open>\<^bold>\<open>Listing 39. lemma vwalk_iff (Pair_Graph_Library_Adaptor.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Directed_Graphs/Adaptors/Pair_Graph_Library_Adaptor.thy\<close> (line 175, locale wf_digraph).
  Checked reference: @{thm wf_digraph.vwalk_iff}.\<close>

text \<open>\<^bold>\<open>Listing 40. definition digraph_abs (Pair_Graph_Specs.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Directed_Graphs/Pair_Graph_Specs.thy\<close> (line 111, locale Pair_Graph_Specs_Read_Only).
  Checked reference: @{const Pair_Graph_Specs_Read_Only.digraph_abs}.\<close>

text \<open>\<^bold>\<open>Listing 41. interpretation iam_graph: Pair_Graph_Imperative (DFS_Imperative.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Graph_Algorithms/Refinements/DFS_Imperative.thy\<close> (line 236).
  interpretation @{text \<open>iam_graph: Pair_Graph_Imperative_Arrays\<close>}.
  Checked reference: @{locale Pair_Graph_Imperative_Arrays}.\<close>

text \<open>\<^bold>\<open>Listing 42. interpretation hm_graph: Pair_Graph_Imperative (DFS_Imperative.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Graph_Algorithms/Refinements/DFS_Imperative.thy\<close> (line 251).
  interpretation @{text \<open>hm_graph: Pair_Graph_Imperative\<close>}.
  Checked reference: @{locale Pair_Graph_Imperative}.\<close>

text \<open>\<^bold>\<open>Listing 43. locale Adj_Map_Specs2 (Orlins_Preparation.thy)\<close>
  In this snapshot: \<^file>\<open>../../Mincost_Flow_Algorithms/Orlins_Preparation.thy\<close> (line 131).
  Checked reference: @{locale Adj_Map_Specs2}.\<close>

text \<open>\<^bold>\<open>Listing 44. locale Multi_Graph_Specs (BFS_Multi.thy)\<close>
  Prose only: development branch bfs_refinement (BFS_Multi.thy); NOT in this snapshot. There is no antiquotation, so this listing is not entity-checked in this snapshot.\<close>

text \<open>\<^bold>\<open>Listing 45. locale indexed_iterable_set (Iterable_Set_Specs.thy)\<close>
  In this snapshot: \<^file>\<open>../../Data_Structures/Iterable_Set_Specs.thy\<close> (line 145).
  Note: branch more_algorithms. In this snapshot the assumptions of the listing are those of the
  parent locales @{locale indexed_set_cursor} and @{locale indexed_set_reset}.
  Checked reference: @{locale indexed_iterable_set}.\<close>

text \<open>\<^bold>\<open>Listing 46. locale weighted_csr (CSR_Graph.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Directed_Graphs/Refinements/CSR_Graph.thy\<close> (line 393).
  Note: branch more_algorithms.
  Checked reference: @{locale weighted_csr}.\<close>

text \<open>\<^bold>\<open>Listing 47. locale ingoing_edge_iterator (Acyclic_Flow.thy)\<close>
  In this snapshot: \<^file>\<open>../../Set_Graphs/Directed_Graphs/Edge_Iterators.thy\<close> (line 45).
  Note: paper locates it in Acyclic_Flow.thy (branch more_algorithms); in this snapshot: Edge_Iterators.thy.
  Checked reference: @{locale ingoing_edge_iterator}.\<close>

end
