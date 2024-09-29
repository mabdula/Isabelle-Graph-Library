(*Author: Christoph Madlener *)
theory Digraph_Component_More
  imports Graph_Theory.Digraph_Component
begin

text \<open>A maximum subgraph with regard to a property of the arcs will always contain all vertices.\<close>
lemma max_subgraph_P_arcs_verts:
  assumes "pre_digraph.max_subgraph G (P \<circ> arcs) H"
  shows "verts G = verts H"
proof -
  have sg_HG: "subgraph H G" using assms pre_digraph.subgraphI_max_subgraph by blast
  then have H_subs_G: "verts H \<subseteq> verts G" by blast

  { assume "verts G \<noteq> verts H"
    then obtain u where "u \<in> verts G" "u \<notin> verts H" using H_subs_G by blast
    let ?H' = "pre_digraph.add_vert H u"

    have sg_H'G: "subgraph ?H' G"
      using sg_HG
      unfolding Digraph_Component.subgraph_def compatible_def
      by (auto simp: \<open>u \<in> verts G\<close> wf_digraph.wf_digraph_add_vert pre_digraph.add_vert_simps)

    have P_H': "P (arcs ?H')"
      using assms
      by (auto simp: pre_digraph.arcs_add_vert dest: pre_digraph.max_subgraph_prop)

    have "verts ?H' \<noteq> verts H" using \<open>u \<notin> verts H\<close> by (auto simp: pre_digraph.add_vert_simps)
    then have uneq: "?H' \<noteq> H" by auto

    have sg_HH': "subgraph H ?H'"
      using sg_HG sg_H'G
      by (auto intro: Digraph_Component.subgraphI simp: pre_digraph.add_vert_simps compatible_def)

    have "\<not>pre_digraph.max_subgraph G (P \<circ> arcs) H"
      unfolding pre_digraph.max_subgraph_def
      using sg_H'G P_H' uneq sg_HH'
      by auto

    then have "False" using assms by blast
  }

  then show ?thesis by blast
qed

lemma strongly_connected_not_singleton_arcs_nonempty:
  assumes sc: "strongly_connected H"
  assumes not_singleton: "u \<in> verts H" "verts H \<noteq> {u}"
  shows "arcs H \<noteq> {}"
proof -
  obtain v w where "v \<in> verts H" "w \<in> verts H" "v \<noteq> w"
    using not_singleton by blast
  then obtain e where "e \<in> arcs H"
    by (meson pre_digraph.converse_reachable_cases reachableE sc strongly_connectedE)
  then show ?thesis by blast
qed

end