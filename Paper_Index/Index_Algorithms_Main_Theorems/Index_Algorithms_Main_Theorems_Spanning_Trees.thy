theory Index_Algorithms_Main_Theorems_Spanning_Trees
  imports
    "Spanning_Trees.Jarnik_Prim"
    "Spanning_Trees.Kruskal_Functional"
begin

text \<open>Listings 61 and 63 of Table 1, kept apart from \<open>Index_Algorithms_Main_Theorems\<close>
  because the spanning tree theories cannot be imported together with
  \<open>HOL-Library.Product_Order\<close>.\<close>

text \<open>\<^bold>\<open>Listing 61. corollary kruskal_computes_max_spanning_forest (Kruskal_Greedy.thy)\<close>
  In this snapshot: \<^file>\<open>../../Spanning_Trees/Kruskal_Functional.thy\<close> (line 1097, locale Kruskal_Proof_Matroid_Edges').
  Note: paper: Kruskal_Greedy.thy; in this snapshot: Kruskal_Functional.thy.
  Checked reference: @{thm Kruskal_Proof_Matroid_Edges'.kruskal_computes_max_spanning_forest}.\<close>

text \<open>\<^bold>\<open>Listing 63. theorem jp_maximum_stree (Jarnik_Prim.thy)\<close>
  In this snapshot: \<^file>\<open>../../Spanning_Trees/Jarnik_Prim.thy\<close> (line 497, locale jarnik_prim_correctness).
  Checked reference: @{thm jarnik_prim_correctness.jp_maximum_stree}.\<close>

end
