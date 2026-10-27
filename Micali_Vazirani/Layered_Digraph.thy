theory Layered_Digraph
  imports Directed_Set_Graphs.Vwalk
          Directed_Set_Graphs.Pair_Graph_Specs
begin

text \<open>The layered digraphs searched by the incremental DFS (IDFS.thy) and by DDFS
(DDFS.thy), together with the path vocabulary of both. Split out of DDFS.thy so that the
incremental DFS and its users do not depend on DDFS.\<close>

section \<open>Paths in digraphs\<close>

abbreviation "dpath \<equiv> Vwalk.vwalk"

abbreviation "dpath_bet dG p v v' \<equiv> Vwalk.vwalk_bet dG v p v'"

section \<open>The layered-input predicate\<close>

text \<open>All assumptions DDFS makes about its input graph, summarised in one
predicate. Two layers: \<^term>\<open>layered_dgraph\<close> is the purely mathematical content
over the abstracted digraph --- finitely many vertices, strictly level-decreasing
edges, and from every vertex a directed path to a level-0 vertex.
Pair_Graph_Specs.layered_graph_input below adds the well-formedness of the
concrete adjacency-map value. The level condition is graded-decreasing
(lev v' < lev v), not unit-step layered: this is all DDFS needs, and it already
yields self-loop-freeness and acyclicity for free. The non-emptiness of the
witness path is not stated --- \<^term>\<open>dpath_bet\<close> forces it (vwalk_bet_nonempty) ---
but is recovered in layered_dgraph_base to match the historical clause shapes.\<close>

definition layered_dgraph :: "('v \<times> 'v) set \<Rightarrow> ('v \<Rightarrow> nat) \<Rightarrow> bool" where
  "layered_dgraph dG lev =
     (finite (dVs dG) \<and>
      (\<forall>v v'. (v, v') \<in> dG \<longrightarrow> lev v' < lev v) \<and>
      (\<forall>v \<in> dVs dG. \<exists>p v'. dpath_bet dG p v v' \<and> lev v' = 0))"

lemma layered_dgraphI:
  assumes "finite (dVs dG)"
          "\<And>v v'. (v, v') \<in> dG \<Longrightarrow> lev v' < lev v"
          "\<And>v. v \<in> dVs dG \<Longrightarrow> \<exists>p v'. dpath_bet dG p v v' \<and> lev v' = 0"
  shows "layered_dgraph dG lev"
  using assms unfolding layered_dgraph_def by blast

lemma layered_dgraph_finite:
  "layered_dgraph dG lev \<Longrightarrow> finite (dVs dG)"
  unfolding layered_dgraph_def by blast

lemma layered_dgraph_level:
  "layered_dgraph dG lev \<Longrightarrow> (v, v') \<in> dG \<Longrightarrow> lev v' < lev v"
  unfolding layered_dgraph_def by blast

lemma layered_dgraph_base:
  assumes "layered_dgraph dG lev" "v \<in> dVs dG"
  shows "\<exists>p v'. p \<noteq> [] \<and> dpath_bet dG p v v' \<and> lev v' = 0"
proof -
  obtain p v' where pw: "dpath_bet dG p v v'" and l0: "lev v' = 0"
    using assms unfolding layered_dgraph_def by blast
  have "p \<noteq> []" using vwalk_bet_nonempty[OF pw] .
  with pw l0 show ?thesis by blast
qed

lemmas layered_dgraphD =
  layered_dgraph_finite layered_dgraph_level layered_dgraph_base
lemma layered_dgraphE:
  assumes "layered_dgraph dG lev"
  obtains "finite (dVs dG)"
      and "\<And>v v'. (v, v') \<in> dG \<Longrightarrow> lev v' < lev v"
      and "\<And>v. v \<in> dVs dG \<Longrightarrow> \<exists>p v'. p \<noteq> [] \<and> dpath_bet dG p v v' \<and> lev v' = 0"
  by (rule that[OF layered_dgraph_finite[OF assms] layered_dgraph_level[OF assms]
                   layered_dgraph_base[OF assms]])

lemma layered_dgraph_no_self_loop:
  "layered_dgraph dG lev \<Longrightarrow> (v, v) \<notin> dG"
  by (elim layered_dgraphE) auto

context Pair_Graph_Specs
begin

definition "layered_graph_input G lev =
   (graph_inv G \<and> finite_graph G \<and> finite_vsets G \<and>
    layered_dgraph (digraph_abs G) lev)"

lemma layered_graph_inputI:
  "graph_inv G \<Longrightarrow> finite_graph G \<Longrightarrow> finite_vsets G \<Longrightarrow>
   layered_dgraph (digraph_abs G) lev \<Longrightarrow> layered_graph_input G lev"
  unfolding layered_graph_input_def by blast

lemma layered_graph_inputD:
  assumes "layered_graph_input G lev"
  shows "graph_inv G" "finite_graph G" "finite_vsets G"
        "layered_dgraph (digraph_abs G) lev"
  using assms unfolding layered_graph_input_def by blast+

lemma layered_graph_inputE:
  assumes "layered_graph_input G lev"
  obtains "graph_inv G" "finite_graph G" "finite_vsets G"
          "layered_dgraph (digraph_abs G) lev"
  by (rule that[OF layered_graph_inputD[OF assms]])

end

end
