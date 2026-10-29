theory Graph_Matching_Specs
  imports Directed_Set_Graphs.Pair_Graph_Specs Matching_Contraction_Expansion
begin

provenance ai_human

section \<open>Graphs and matchings for the executable blossom algorithm\<close>

text \<open>An undirected graph is represented by an adjacency map that stores both orientations of
  every edge. Matchings are supplied by their abstract data type, including partner lookup,
  augmentation, contraction and expansion. The locale also requires an operation that lists the
  elements of a vertex set to scan neighbours and enumerate graph edges.\<close>

locale Graph_Matching_Specs =
  Graph: Pair_Graph_Specs where lookup = lookup +
  Mate: blossom_matching
    where K = K and empty_matching = mate_empty and matching_invar = matching_invar_abs
      and lookup_partner = mate_lookup and get_partner = mate_partner and augment = mate_augment
      and matching_abstract = matching_abs and contract_path = mate_contract
      and expand_path_at_matched = mate_expand and add_alternatingly = mate_add_alternatingly
  for K :: "'v set"
  and lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option"
  and mate_empty :: 'mate
  and matching_invar_abs :: "'v set set \<Rightarrow> 'mate \<Rightarrow> bool"
  and mate_lookup :: "'mate \<Rightarrow> 'v \<Rightarrow> 'v option"
  and mate_partner :: "'mate \<Rightarrow> 'v \<Rightarrow> 'v"
  and mate_augment :: "'mate \<Rightarrow> 'v list \<Rightarrow> 'mate"
  and matching_abs :: "'mate \<Rightarrow> 'v set set"
  and mate_contract :: "'mate \<Rightarrow> 'v list \<Rightarrow> 'v \<Rightarrow> 'mate"
  and mate_expand :: "'mate \<Rightarrow> 'v list \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'mate"
  and mate_add_alternatingly :: "'mate \<Rightarrow> 'v list \<Rightarrow> 'mate" +
  fixes vset_to_list :: "'vset \<Rightarrow> 'v list"
  assumes vset_to_list: "\<And>N. vset_inv N \<Longrightarrow> set (vset_to_list N) = t_set N"
begin

subsection \<open>Abstraction and input conditions\<close>

definition "ugraph_abs G = {{u, v} | u v. (u, v) \<in> Graph.digraph_abs G}"

text \<open>The conditions on a graph and its vertex list. The list may contain vertices without
  edges; it is used to enumerate the vertices.\<close>

definition "graph_input G vs \<longleftrightarrow>
   Graph.graph_inv G \<and> Graph.finite_graph G \<and> Graph.finite_vsets G \<and>
   (\<forall>u v. (u, v) \<in> Graph.digraph_abs G \<longrightarrow> (v, u) \<in> Graph.digraph_abs G) \<and>
   (\<forall>u. (u, u) \<notin> Graph.digraph_abs G) \<and>
   dVs (Graph.digraph_abs G) \<subseteq> set vs \<and> set vs \<subseteq> K"

definition "matching_invar G M = matching_invar_abs (ugraph_abs G) M"

subsection \<open>Operations\<close>

definition "neighbour_list G v = vset_to_list (Graph.neighbourhood G v)"

definition "adjacency_edges G vs = concat (map (\<lambda>v. map (Pair v) (neighbour_list G v)) vs)"

lemmas [code] = neighbour_list_def adjacency_edges_def

subsection \<open>Properties of the input conditions\<close>

lemma graph_inputD:
  "graph_input G vs \<Longrightarrow> Graph.graph_inv G"
  "graph_input G vs \<Longrightarrow> Graph.finite_graph G"
  "graph_input G vs \<Longrightarrow> Graph.finite_vsets G"
  "\<lbrakk>graph_input G vs; (u, v) \<in> Graph.digraph_abs G\<rbrakk> \<Longrightarrow> (v, u) \<in> Graph.digraph_abs G"
  "graph_input G vs \<Longrightarrow> (u, u) \<notin> Graph.digraph_abs G"
  "graph_input G vs \<Longrightarrow> dVs (Graph.digraph_abs G) \<subseteq> set vs"
  "graph_input G vs \<Longrightarrow> set vs \<subseteq> K"
  by (auto simp: graph_input_def)

lemma graph_inputI:
  "\<lbrakk>Graph.graph_inv G; Graph.finite_graph G; Graph.finite_vsets G;
    \<And>u v. (u, v) \<in> Graph.digraph_abs G \<Longrightarrow> (v, u) \<in> Graph.digraph_abs G;
    \<And>u. (u, u) \<notin> Graph.digraph_abs G; dVs (Graph.digraph_abs G) \<subseteq> set vs; set vs \<subseteq> K\<rbrakk>
   \<Longrightarrow> graph_input G vs"
  by (auto simp: graph_input_def)

lemma in_ugraph_abs_iff:
  "graph_input G vs \<Longrightarrow> {u, v} \<in> ugraph_abs G \<longleftrightarrow> (u, v) \<in> Graph.digraph_abs G"
  by (auto simp: ugraph_abs_def doubleton_eq_iff dest: graph_inputD(4))

lemma isin_neighbourhood_iff:
  "isin (Graph.neighbourhood G v) w \<longleftrightarrow> (v, w) \<in> Graph.digraph_abs G"
  by (simp add: Graph.digraph_abs_def)

lemma Vs_ugraph_abs:
  "Vs (ugraph_abs G) = dVs (Graph.digraph_abs G)"
  by (simp only: ugraph_abs_def Vs_dVs_UD[unfolded UD_def])

lemma ugraph_abs_graph_invar:
  assumes "graph_input G vs"
  shows "graph_invar (ugraph_abs G)"
proof
  show "dblton_graph (ugraph_abs G)"
    using graph_inputD(5)[OF assms]
    by (fastforce simp: dblton_graph_def ugraph_abs_def)
  show "finite (Vs (ugraph_abs G))"
    using Graph.finite_vertices[OF graph_inputD(1-3)[OF assms]]
    by (simp add: Vs_ugraph_abs)
qed

lemma Vs_ugraph_abs_subset_vs:
  "graph_input G vs \<Longrightarrow> Vs (ugraph_abs G) \<subseteq> set vs"
  using graph_inputD(6) by (simp add: Vs_ugraph_abs)

subsection \<open>Properties of the operations\<close>

lemma neighbour_list:
  assumes "graph_input G vs"
  shows "set (neighbour_list G v) = {w. (v, w) \<in> Graph.digraph_abs G}"
proof-
  have "Graph.graph_inv G"
    using assms
    by (rule graph_inputD(1))
  thus ?thesis
    by (auto simp: neighbour_list_def vset_to_list)
qed

lemma neighbour_list_ugraph_abs:
  assumes "graph_input G vs"
  shows "w \<in> set (neighbour_list G v) \<longleftrightarrow> {v, w} \<in> ugraph_abs G"
  by (simp add: neighbour_list[OF assms] in_ugraph_abs_iff[OF assms])

lemma neighbour_list_nonempty_iff:
  assumes "graph_input G vs"
  shows "neighbour_list G v \<noteq> [] \<longleftrightarrow> v \<in> Vs (ugraph_abs G)"
proof-
  interpret H: graph_abs "ugraph_abs G"
    by unfold_locales (rule ugraph_abs_graph_invar[OF assms])
  have "neighbour_list G v \<noteq> [] \<longleftrightarrow> (\<exists>w. w \<in> set (neighbour_list G v))"
    by (cases "neighbour_list G v") auto
  also have "\<dots> \<longleftrightarrow> (\<exists>w. {v, w} \<in> ugraph_abs G)"
    by (simp add: neighbour_list_ugraph_abs[OF assms])
  also have "\<dots> \<longleftrightarrow> v \<in> Vs (ugraph_abs G)"
    by (simp add: H.vs_member' insert_commute)
  finally show ?thesis .
qed

lemma adjacency_edges:
  assumes "graph_input G vs"
  shows "set (adjacency_edges G vs) = Graph.digraph_abs G"
proof-
  have "set (adjacency_edges G vs) = {(v, w). v \<in> set vs \<and> (v, w) \<in> Graph.digraph_abs G}"
    by (auto simp: adjacency_edges_def neighbour_list[OF assms])
  moreover have "v \<in> set vs" if "(v, w) \<in> Graph.digraph_abs G" for v w
    using that graph_inputD(6)[OF assms]
    by (auto intro: dVsI)
  ultimately show ?thesis
    by auto
qed

subsection \<open>The mate function\<close>

lemmas matching_abs_iff = Mate.lookup_partner[symmetric]

lemma Vs_matching_abs_iff:
  assumes "graph_input G vs" "matching_invar G M"
  shows "v \<in> Vs (matching_abs M) \<longleftrightarrow> mate_lookup M v \<noteq> None"
proof-
  have inv: "matching_invar_abs (ugraph_abs G) M"
    using assms(2) by (simp add: matching_invar_def)
  interpret H: graph_abs "matching_abs M"
    by unfold_locales
       (rule graph_invar_subset[OF ugraph_abs_graph_invar[OF assms(1)]
         conjunct2[OF Mate.matching(1)[OF inv]]])
  show ?thesis
    by (simp add: H.vs_member' not_None_eq Mate.lookup_partner[OF inv] insert_commute)
qed

lemma matching_invar_props:
  assumes "matching_invar G M"
  shows "matching_invar_abs (ugraph_abs G) M"
    "matching (matching_abs M)" "matching_abs M \<subseteq> ugraph_abs G"
    "graph_input G vs \<Longrightarrow> finite (matching_abs M)"
    "graph_input G vs \<Longrightarrow> Vs (ugraph_abs G) \<subseteq> K"
proof-
  show "matching_invar_abs (ugraph_abs G) M"
    using assms by (simp add: matching_invar_def)
  then show "matching (matching_abs M)" "matching_abs M \<subseteq> ugraph_abs G"
    using Mate.matching(1) by auto
  then show "graph_input G vs \<Longrightarrow> finite (matching_abs M)"
    using ugraph_abs_graph_invar finite_subset by (meson finite_Vs_then_finite)
  show "graph_input G vs \<Longrightarrow> Vs (ugraph_abs G) \<subseteq> K"
    using Vs_ugraph_abs_subset_vs graph_inputD(7) by blast
qed

subsection \<open>Graphs built from edge lists\<close>

lemma from_list_graph_input:
  assumes "\<And>a b. (a, b) \<in> set xs \<Longrightarrow> (b, a) \<in> set xs" "\<And>a. (a, a) \<notin> set xs"
          "dVs (set xs) \<subseteq> set vs" "set vs \<subseteq> K"
  shows "graph_input (Graph.from_list xs) vs"
  using assms
  by (auto intro!: graph_inputI simp: Graph.from_list_correct)

lemma ugraph_abs_from_list:
  "ugraph_abs (Graph.from_list xs) = {{a, b} | a b. (a, b) \<in> set xs}"
  by (simp add: ugraph_abs_def Graph.from_list_correct)

end

end
