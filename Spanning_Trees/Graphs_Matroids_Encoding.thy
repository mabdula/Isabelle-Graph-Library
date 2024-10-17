theory Graphs_Matroids_Encoding
  imports Directed_Set_Graphs.Pair_Graph_U_Specs Matroids_Greedy.Indep_System_Matroids_Specs
begin


(* TODO probably put everything here in locale with proper specs (although probably don't need any
additional assumptions *)

(* TODO link types properly based on 'v (should we already use uEdge here or just specify arbitrary
edge type?) \<Rightarrow> Do we even need to "connect" types here? *)
(* Do we need to specify all of matroid specs with indep function or just the custom set specs? *)
(* NOTE: !! definitely need either selection function or some sort of foreach which will enable us
to iterate through the sets !! *)

(* Do we need some assumption on edge type 'e? Or can this be left to the rest of the code? *)
(* CURRENT IDEA: Define two functions v1_of and v2_of from 'e to 'v which return first and second vertex
resp., assume additionally that for all edges e, v1_of e and v2_of e return different elements in an axioms
predicate 
\<Longrightarrow> ALSO: Assume function edge_of which takes two vertices, with assumption that edge_of a b = edge_of b a
\<Longrightarrow> maybe can assume that if a \<noteq> b then edge_of a b = edge_of b a? or not?
*)
locale Graphs_Matroids_Encoding =
  pair_graph_u: Pair_Graph_U_Specs where lookup = lookup +
  matroid: Matroid_Specs where set_insert = set_insert and set_of_sets_isin = set_of_sets_isin
  for lookup :: "'adj \<Rightarrow> ('v::linorder) \<Rightarrow> 'neighb option" and set_insert :: "('e::linorder) \<Rightarrow> 's \<Rightarrow> 's" and
    set_of_sets_isin :: "'t \<Rightarrow> 's \<Rightarrow> bool" and adj_fold :: "'adj \<Rightarrow> ('v \<Rightarrow> 'neighb \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> 's \<Rightarrow> 's" and
    neighb_fold :: "'neighb \<Rightarrow> ('v \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> 's \<Rightarrow> 's" and set_fold_adj :: "'s \<Rightarrow> ('e \<Rightarrow> 'adj \<Rightarrow> 'adj) \<Rightarrow> 'adj \<Rightarrow> 'adj" and
    set_fold_neighb :: "'s \<Rightarrow> ('e \<Rightarrow> 'neighb \<Rightarrow> 'neighb) \<Rightarrow> 'neighb \<Rightarrow> 'neighb" +
  fixes v1_of :: "'e \<Rightarrow> 'v" and v2_of :: "'e \<Rightarrow> 'v" and edge_of :: "'v \<Rightarrow> 'v \<Rightarrow> 'e"
  (* maybe also do something here related to cost? *)
  (* TODO WHERE DID I HAVE v1, v2, edge properties ?? \<Longrightarrow> Maybe put this in axioms ? *)
begin

(* TODO HERE NOW *)
thm pair_graph_u.pair_graph_u_invar_def
thm pair_graph_u.graph_inv_def
thm pair_graph_u.add_edge_def

(* What should invariants be? \<Rightarrow> On one side: pair_graph_u_invar G + neighb_inv V + relationship G V,
on other side: definitely set_inv, anything else? *)

(* Later just define state and functions, but nothing else *)

(* Iterate through graph itself, then through neighbourhood in nested fashion:
\<Rightarrow> will have two vertices, form edge_of
If edge is not in set insert it otherwise don't insert it *)
fun graph_to_edges :: "'adj \<Rightarrow> 's" where
  "graph_to_edges G =
    adj_fold G 
    (\<lambda>u N E. union E (neighb_fold N 
        (\<lambda>v E. (let e = (edge_of u v)
                in (if \<not>(set_isin E e) then set_insert e E else E))) set_empty))
    set_empty"

(* Iterate through all edges, just use add_edge and v1_of, v2_of from Pair_graph to build a graph, make
sure every edge is added symmetrically *)
fun edges_to_graph :: "'s \<Rightarrow> 'adj" where
  "edges_to_graph E =
    set_fold_adj E
    (\<lambda>e G. pair_graph_u.add_edge (pair_graph_u.add_edge G (v1_of e) (v2_of e)) (v2_of e) (v1_of e))
    empty"

fun edges_to_vertices :: "'s \<Rightarrow> 'neighb" where
  "edges_to_vertices E = 
    set_fold_neighb E
    (\<lambda>e N. if isin N (v1_of e)
           then (if isin N (v2_of e) then N else insert (v2_of e) N)
           else (if isin N (v2_of e) then insert (v1_of e) N else insert (v1_of e) (insert (v2_of e) N)))
    neighb_empty"

(* TODO put down outcommented value theorems (and/or) just note that these functions cannot be
executed with value since add_edge is a definition, not a fun *)

(* Correctness properties *)

lemma graph_invar_imp_edges_invar:
  "pair_graph_u.pair_graph_u_invar G \<Longrightarrow> set_inv (graph_to_edges G)"
  sorry

lemma edges_invar_imp_graph_invar:
  "set_inv E \<Longrightarrow> pair_graph_u.pair_graph_u_invar (edges_to_graph E)"
  sorry

lemma edges_invar_imp_vertices_props:
  assumes "set_inv E"
  shows "neighb_inv (edges_to_vertices E)"
    "t_set (edges_to_vertices E) = dVs (pair_graph_u.digraph_abs (edges_to_graph E))"
  sorry


(* probably need invars here additionally, TODO check whether this is the right "direction" *)
(* lemma
  "ugraph_abs (edges_to_graph E)" *)

(* If to_set of E1 E2 is the same, ugraph_abs of (edges_to_graph E1) (edges_to_graph E2) is the same *)
  
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

end


end