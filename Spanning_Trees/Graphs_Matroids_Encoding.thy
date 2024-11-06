theory Graphs_Matroids_Encoding
  imports Directed_Set_Graphs.Pair_Graph_U_Specs Matroids_Greedy.Indep_System_Matroids_Specs
begin


locale Graphs_Matroids_Encoding =
  pair_graph_u: Pair_Graph_U_Specs where lookup = lookup +
  matroid: Matroid_Specs where set_insert = set_insert and set_of_sets_isin = set_of_sets_isin
  for lookup :: "'adjmap \<Rightarrow> ('v::linorder) \<Rightarrow> 'vset option" and set_insert :: "('e::linorder) \<Rightarrow> 's \<Rightarrow> 's" and
    set_of_sets_isin :: "'t \<Rightarrow> 's \<Rightarrow> bool" and adjmap_fold :: "'adjmap \<Rightarrow> ('v \<Rightarrow> 'vset \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> 's \<Rightarrow> 's" and
    vset_fold :: "'vset \<Rightarrow> ('v \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> 's \<Rightarrow> 's" and set_fold_adjmap :: "'s \<Rightarrow> ('e \<Rightarrow> 'adjmap \<Rightarrow> 'adjmap) \<Rightarrow> 'adjmap \<Rightarrow> 'adjmap" and
    set_fold_vset :: "'s \<Rightarrow> ('e \<Rightarrow> 'vset \<Rightarrow> 'vset) \<Rightarrow> 'vset \<Rightarrow> 'vset" +
  fixes v1_of :: "'e \<Rightarrow> 'v" and v2_of :: "'e \<Rightarrow> 'v" and edge_of :: "'v \<Rightarrow> 'v \<Rightarrow> 'e" and c :: "('v set) \<Rightarrow> rat" and c' :: "'e \<Rightarrow> rat"
begin

(* TODO: Additional axioms/invariants necessary for proving properties *)

(* Iterate through graph itself, then through neighbourhood in nested fashion  *)
fun graph_to_edges :: "'adjmap \<Rightarrow> 's" where
  "graph_to_edges G =
    adjmap_fold G 
    (\<lambda>u N E. union E (vset_fold N 
        (\<lambda>v E. (let e = (edge_of u v)
                in (if \<not>(set_isin E e) then set_insert e E else E))) set_empty))
    set_empty"

(* Iterate through all edges, just use add_edge and v1_of, v2_of to build a graph, make
sure every edge is added symmetrically *)
fun edges_to_graph :: "'s \<Rightarrow> 'adjmap" where
  "edges_to_graph E =
    set_fold_adjmap E
    (\<lambda>e G. pair_graph_u.add_edge (pair_graph_u.add_edge G (v1_of e) (v2_of e)) (v2_of e) (v1_of e))
    empty"

fun edges_to_vertices :: "'s \<Rightarrow> 'vset" where
  "edges_to_vertices E = 
    set_fold_vset E
    (\<lambda>e N. if isin N (v1_of e)
           then (if isin N (v2_of e) then N else insert (v2_of e) N)
           else (if isin N (v2_of e) then insert (v1_of e) N else insert (v1_of e) (insert (v2_of e) N)))
    vset_empty"

(* Correctness properties *)

lemma graph_invar_imp_edges_invar:
  "pair_graph_u.pair_graph_u_invar G \<Longrightarrow> set_inv (graph_to_edges G)"
  sorry

lemma edges_invar_imp_graph_invar:
  "set_inv E \<Longrightarrow> pair_graph_u.pair_graph_u_invar (edges_to_graph E)"
  sorry

lemma edges_invar_imp_vertices_props:
  assumes "set_inv E"
  shows "vset_inv (edges_to_vertices E)"
    "t_set (edges_to_vertices E) = dVs (pair_graph_u.digraph_abs (edges_to_graph E))"
  sorry

  
lemma to_set_equal_imp_ugraph_abs_equal:
  assumes "set_inv X" "set_inv Y" "to_set X = to_set Y"
  shows "pair_graph_u.ugraph_abs (edges_to_graph X) = pair_graph_u.ugraph_abs (edges_to_graph Y)"
  sorry


lemma graph_to_edges_inverse:
  "pair_graph_u.pair_graph_u_invar G \<Longrightarrow> edges_to_graph (graph_to_edges G) = G"
  sorry

lemma edges_to_graph_subset_imp_subset:
  assumes "set_inv X" "set_inv Y" "pair_graph_u.ugraph_abs (edges_to_graph X) \<subseteq> pair_graph_u.ugraph_abs (edges_to_graph Y)"
  shows "to_set X \<subseteq> to_set Y"
  sorry

lemma subset_imp_edges_to_graph_subset:
  assumes "set_inv X" "set_inv Y" "subseteq X Y"
  shows "pair_graph_u.ugraph_abs (edges_to_graph X) \<subseteq> pair_graph_u.ugraph_abs (edges_to_graph Y)"
  sorry

lemma subset_iff_graph_to_edges_subset:
  assumes "set_inv X" "set_inv Y"
  shows "subseteq X Y = (pair_graph_u.ugraph_abs (edges_to_graph X) \<subseteq> pair_graph_u.ugraph_abs (edges_to_graph Y))"
  using edges_to_graph_subset_imp_subset[OF assms] subset_imp_edges_to_graph_subset[OF assms]
    matroid.set.set_subseteq[OF assms] by blast

(*
lemma diff_graph_to_edges:
  assumes "set_inv X" "set_inv Y"
  shows "diff X Y = pair_graph_u.ugraph_abs (edges_to_graph X) - pair_graph_u.ugraph_abs (edges_to_graph Y)"
  sorry
*)

lemma card_graph_to_edges:
  assumes "set_inv X"
  shows "cardinality X = card (pair_graph_u.ugraph_abs (edges_to_graph X))"
  sorry

lemma costs_transformation:
  "sum c' (to_set E') \<le> sum c' (to_set E'') \<Longrightarrow>
   sum c (pair_graph_u.ugraph_abs (Kruskal_E_to_G E')) \<ge>
    sum c (pair_graph_u.ugraph_abs (Kruskal_E_to_G E''))"
      sorry


end


end