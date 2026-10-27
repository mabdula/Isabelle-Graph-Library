theory Graph_Matching_Specs
  imports Directed_Set_Graphs.Pair_Graph_Specs Basic_Matching.Matching_Augmentation_Executable
begin

provenance ai_human

section \<open>Graphs and matchings for the executable blossom algorithm\<close>

text \<open>An undirected graph is represented by an adjacency map that stores both orientations of
  every edge. A matching is represented by its mate function, which maps every matched vertex to
  its partner. The locale below combines the two data structures with an operation that lists the
  elements of a vertex set, which is needed to scan the neighbours of a vertex and to enumerate
  the edges of a graph.\<close>

locale Graph_Matching_Specs =
  Graph: Pair_Graph_Specs where lookup = lookup +
  Mate_Map: Map mate_empty mate_update mate_delete mate_lookup mate_invar +
  Mate: matching_augmentation mate_empty mate_update mate_delete mate_lookup mate_invar
  for lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option"
  and mate_empty :: 'mate
  and mate_update :: "'v \<Rightarrow> 'v \<Rightarrow> 'mate \<Rightarrow> 'mate"
  and mate_delete :: "'v \<Rightarrow> 'mate \<Rightarrow> 'mate"
  and mate_lookup :: "'mate \<Rightarrow> 'v \<Rightarrow> 'v option"
  and mate_invar :: "'mate \<Rightarrow> bool" +
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
   dVs (Graph.digraph_abs G) \<subseteq> set vs"

abbreviation "matching_abs \<equiv> Mate.\<M>"

definition "matching_invar G M = Mate.invar_matching (ugraph_abs G) M"

subsection \<open>Operations\<close>

definition "neighbour_list G v = vset_to_list (Graph.neighbourhood G v)"

definition "adjacency_edges G vs = concat (map (\<lambda>v. map (Pair v) (neighbour_list G v)) vs)"

definition "matching_edges M vs =
   concat (map (\<lambda>v. case mate_lookup M v of Some w \<Rightarrow> [(v, w)] | None \<Rightarrow> []) vs)"

definition "mate_from_list ps = foldl (\<lambda>m (a, b). mate_update a b m) mate_empty ps"

lemmas [code] = neighbour_list_def adjacency_edges_def matching_edges_def mate_from_list_def

subsection \<open>Properties of the input conditions\<close>

lemma graph_inputD:
  "graph_input G vs \<Longrightarrow> Graph.graph_inv G"
  "graph_input G vs \<Longrightarrow> Graph.finite_graph G"
  "graph_input G vs \<Longrightarrow> Graph.finite_vsets G"
  "\<lbrakk>graph_input G vs; (u, v) \<in> Graph.digraph_abs G\<rbrakk> \<Longrightarrow> (v, u) \<in> Graph.digraph_abs G"
  "graph_input G vs \<Longrightarrow> (u, u) \<notin> Graph.digraph_abs G"
  "graph_input G vs \<Longrightarrow> dVs (Graph.digraph_abs G) \<subseteq> set vs"
  by (auto simp: graph_input_def)

lemma graph_inputI:
  "\<lbrakk>Graph.graph_inv G; Graph.finite_graph G; Graph.finite_vsets G;
    \<And>u v. (u, v) \<in> Graph.digraph_abs G \<Longrightarrow> (v, u) \<in> Graph.digraph_abs G;
    \<And>u. (u, u) \<notin> Graph.digraph_abs G; dVs (Graph.digraph_abs G) \<subseteq> set vs\<rbrakk>
   \<Longrightarrow> graph_input G vs"
  by (auto simp: graph_input_def)

lemma in_ugraph_abs_iff:
  "graph_input G vs \<Longrightarrow> {u, v} \<in> ugraph_abs G \<longleftrightarrow> (u, v) \<in> Graph.digraph_abs G"
  by (auto simp: ugraph_abs_def doubleton_eq_iff dest: graph_inputD(4))

lemma isin_neighbourhood_iff:
  "isin (Graph.neighbourhood G v) w \<longleftrightarrow> (v, w) \<in> Graph.digraph_abs G"
  by (simp add: Graph.digraph_abs_def)

lemma Vs_ugraph_abs_subset:
  "Vs (ugraph_abs G) \<subseteq> dVs (Graph.digraph_abs G)"
  by (auto simp: ugraph_abs_def Vs_def intro: dVsI)

lemma ugraph_abs_graph_invar:
  assumes "graph_input G vs"
  shows "graph_invar (ugraph_abs G)"
proof
  show "dblton_graph (ugraph_abs G)"
    using graph_inputD(5)[OF assms]
    by (fastforce simp: dblton_graph_def ugraph_abs_def)
  have "finite (dVs (Graph.digraph_abs G))"
    using graph_inputD(1-3)[OF assms]
    by (rule Graph.finite_vertices)
  thus "finite (Vs (ugraph_abs G))"
    using Vs_ugraph_abs_subset
    by (rule finite_subset[rotated])
qed

lemma Vs_ugraph_abs:
  assumes "graph_input G vs"
  shows "Vs (ugraph_abs G) = dVs (Graph.digraph_abs G)"
proof
  show "Vs (ugraph_abs G) \<subseteq> dVs (Graph.digraph_abs G)"
    by (rule Vs_ugraph_abs_subset)
  show "dVs (Graph.digraph_abs G) \<subseteq> Vs (ugraph_abs G)"
  proof
    fix x
    assume "x \<in> dVs (Graph.digraph_abs G)"
    then obtain u v where uv: "(u, v) \<in> Graph.digraph_abs G" "x = u \<or> x = v"
      by (auto simp: dVs_eq image_iff)
    hence "\<exists>w. (x, w) \<in> Graph.digraph_abs G"
      using graph_inputD(4)[OF assms, of u v]
      by auto
    then obtain w where "(x, w) \<in> Graph.digraph_abs G"
      by blast
    hence "{x, w} \<in> ugraph_abs G"
      by (auto simp: ugraph_abs_def)
    thus "x \<in> Vs (ugraph_abs G)"
      by (auto simp: Vs_def)
  qed
qed

lemma Vs_ugraph_abs_subset_vs:
  "graph_input G vs \<Longrightarrow> Vs (ugraph_abs G) \<subseteq> set vs"
  using Vs_ugraph_abs_subset graph_inputD(6)
  by blast

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
  have "neighbour_list G v \<noteq> [] \<longleftrightarrow> (\<exists>w. w \<in> set (neighbour_list G v))"
    by (cases "neighbour_list G v") auto
  also have "\<dots> \<longleftrightarrow> (\<exists>w. {v, w} \<in> ugraph_abs G)"
    by (simp add: neighbour_list_ugraph_abs[OF assms])
  also have "\<dots> \<longleftrightarrow> v \<in> Vs (ugraph_abs G)"
  proof
    assume "\<exists>w. {v, w} \<in> ugraph_abs G"
    thus "v \<in> Vs (ugraph_abs G)"
      by (auto simp: Vs_def)
  next
    assume "v \<in> Vs (ugraph_abs G)"
    then obtain e where e: "v \<in> e" "e \<in> ugraph_abs G"
      by (auto simp: Vs_def)
    then obtain a b where "e = {a, b}"
      using ugraph_abs_graph_invar[OF assms]
      by (auto simp: dblton_graph_def)
    thus "\<exists>w. {v, w} \<in> ugraph_abs G"
      using e
      by (auto simp: insert_commute)
  qed
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

lemma matching_abs_iff:
  "Mate.invar_matching E M \<Longrightarrow> {u, v} \<in> matching_abs M \<longleftrightarrow> mate_lookup M u = Some v"
  by (auto simp: Mate.\<M>_def' doubleton_eq_iff dest: Mate.invar_matchingD(2) Mate.symmetric_buddiesD)

lemma Vs_matching_abs_iff:
  "Mate.invar_matching E M \<Longrightarrow> v \<in> Vs (matching_abs M) \<longleftrightarrow> mate_lookup M v \<noteq> None"
  by (auto simp: Vs_def Mate.\<M>_def' dest: Mate.invar_matchingD(2) Mate.symmetric_buddiesD)

lemma matching_invar_props:
  assumes "matching_invar G M"
  shows "mate_invar M" "matching (matching_abs M)" "matching_abs M \<subseteq> ugraph_abs G"
        "finite (matching_abs M)"
  using assms
  by (auto simp: matching_invar_def dest: Mate.invar_matchingD)

lemma matching_invar_mate_edge:
  assumes "graph_input G vs" "matching_invar G M" "mate_lookup M u = Some v"
  shows "{u, v} \<in> matching_abs M" "{u, v} \<in> ugraph_abs G" "(u, v) \<in> Graph.digraph_abs G"
proof-
  show "{u, v} \<in> matching_abs M"
    using assms(2,3)
    by (simp add: matching_invar_def matching_abs_iff)
  thus "{u, v} \<in> ugraph_abs G"
    using matching_invar_props(3)[OF assms(2)]
    by blast
  thus "(u, v) \<in> Graph.digraph_abs G"
    by (simp add: in_ugraph_abs_iff[OF assms(1)])
qed

lemma matching_edges:
  assumes "graph_input G vs" "matching_invar G M"
  shows "set (matching_edges M vs) = {(u, v). mate_lookup M u = Some v}"
proof-
  have "u \<in> set vs" if "mate_lookup M u = Some v" for u v
    using matching_invar_mate_edge(3)[OF assms that] graph_inputD(6)[OF assms(1)]
    by (auto intro: dVsI)
  thus ?thesis
    by (force simp: matching_edges_def split: option.splits)
qed

lemma mate_foldl_update:
  assumes "mate_invar m" "\<And>a b b'. \<lbrakk>(a, b) \<in> set ps; (a, b') \<in> set ps\<rbrakk> \<Longrightarrow> b = b'"
  shows "mate_invar (foldl (\<lambda>m (a, b). mate_update a b m) m ps) \<and>
         (\<forall>a b. mate_lookup (foldl (\<lambda>m (a, b). mate_update a b m) m ps) a = Some b \<longleftrightarrow>
                (a, b) \<in> set ps \<or> ((\<forall>b'. (a, b') \<notin> set ps) \<and> mate_lookup m a = Some b))"
  using assms
proof(induction ps arbitrary: m)
  case Nil
  then show ?case
    by simp
next
  case (Cons p ps)
  obtain a0 b0 where p: "p = (a0, b0)"
    by (cases p)
  have inv: "mate_invar (mate_update a0 b0 m)"
    using Cons.prems(1)
    by (rule Mate_Map.invar_update)
  have func: "\<And>a b b'. \<lbrakk>(a, b) \<in> set ps; (a, b') \<in> set ps\<rbrakk> \<Longrightarrow> b = b'"
    using Cons.prems(2)
    by auto
  have IH: "mate_invar (foldl (\<lambda>m (a, b). mate_update a b m) (mate_update a0 b0 m) ps) \<and>
            (\<forall>a b. mate_lookup (foldl (\<lambda>m (a, b). mate_update a b m) (mate_update a0 b0 m) ps) a = Some b
                   \<longleftrightarrow> (a, b) \<in> set ps \<or>
                       ((\<forall>b'. (a, b') \<notin> set ps) \<and> mate_lookup (mate_update a0 b0 m) a = Some b))"
    using Cons.IH[OF inv func] .
  have upd: "mate_lookup (mate_update a0 b0 m) a = (if a = a0 then Some b0 else mate_lookup m a)" for a
    using Cons.prems(1)
    by (simp add: Mate_Map.map_update)
  have "(a0, b) \<in> set ps \<Longrightarrow> b = b0" for b
    using Cons.prems(2)[of a0 b b0]
    by (simp add: p)
  thus ?case
    using IH
    by (auto simp: p upd)
qed

lemma matching_set_functional:
  assumes "matching {{a, b} | a b. (a, b) \<in> set ps}" "\<And>a. (a, a) \<notin> set ps"
          "(a, b) \<in> set ps" "(a, b') \<in> set ps"
  shows "b = b'"
proof(rule ccontr)
  assume "b \<noteq> b'"
  hence "{a, b} \<noteq> {a, b'}"
    by (auto simp: doubleton_eq_iff)
  moreover have "{a, b} \<in> {{a, b} | a b. (a, b) \<in> set ps}" "{a, b'} \<in> {{a, b} | a b. (a, b) \<in> set ps}"
    using assms(3,4)
    by blast+
  ultimately have "{a, b} \<inter> {a, b'} = {}"
    using assms(1)
    by (auto simp: matching_def)
  thus False
    by blast
qed

lemma mate_from_list:
  assumes "graph_input G vs"
    and "\<And>a b. (a, b) \<in> set ps \<Longrightarrow> (b, a) \<in> set ps"
    and "\<And>a. (a, a) \<notin> set ps"
    and "matching {{a, b} | a b. (a, b) \<in> set ps}"
    and "\<And>a b. (a, b) \<in> set ps \<Longrightarrow> (a, b) \<in> Graph.digraph_abs G"
  shows "matching_invar G (mate_from_list ps)"
        "matching_abs (mate_from_list ps) = {{a, b} | a b. (a, b) \<in> set ps}"
proof-
  have func: "\<And>a b b'. \<lbrakk>(a, b) \<in> set ps; (a, b') \<in> set ps\<rbrakk> \<Longrightarrow> b = b'"
    using matching_set_functional[OF assms(4,3)]
    by blast
  have fold: "mate_invar (mate_from_list ps)"
    "\<And>a b. mate_lookup (mate_from_list ps) a = Some b \<longleftrightarrow> (a, b) \<in> set ps"
    using mate_foldl_update[OF Mate_Map.invar_empty func]
    by (auto simp: mate_from_list_def Mate_Map.map_empty)
  show abs: "matching_abs (mate_from_list ps) = {{a, b} | a b. (a, b) \<in> set ps}"
    by (simp add: Mate.\<M>_def' fold(2))
  have "Mate.symmetric_buddies (mate_from_list ps)"
    using assms(2)
    by (auto intro!: Mate.symmetric_buddiesI simp: fold(2))
  moreover have "Mate.no_self_loop_buddy (mate_from_list ps)"
    using assms(3)
    by (auto intro!: Mate.no_self_loop_buddyI simp: fold(2))
  moreover have "matching_abs (mate_from_list ps) \<subseteq> ugraph_abs G"
    using assms(5)
    by (auto simp: abs ugraph_abs_def)
  moreover have "finite (matching_abs (mate_from_list ps))"
  proof-
    have "{{a, b} | a b. (a, b) \<in> set ps} = (\<lambda>(a, b). {a, b}) ` set ps"
      by auto
    thus ?thesis
      by (simp add: abs)
  qed
  ultimately show "matching_invar G (mate_from_list ps)"
    using fold(1) assms(4)
    by (auto intro!: Mate.invar_matchingI simp: matching_invar_def abs)
qed

subsection \<open>Graphs built from edge lists\<close>

lemma from_list_graph_input:
  assumes "\<And>a b. (a, b) \<in> set xs \<Longrightarrow> (b, a) \<in> set xs" "\<And>a. (a, a) \<notin> set xs"
          "dVs (set xs) \<subseteq> set vs"
  shows "graph_input (Graph.from_list xs) vs"
  using assms
  by (auto intro!: graph_inputI simp: Graph.from_list_correct)

lemma ugraph_abs_from_list:
  "ugraph_abs (Graph.from_list xs) = {{a, b} | a b. (a, b) \<in> set xs}"
  by (simp add: ugraph_abs_def Graph.from_list_correct)

end

end
