theory choose
  imports Undirected_Set_Graphs.Pair_Graph_Berge_Adaptor
          Undirected_Set_Graphs.Undirected_Set_Graphs 
begin

lemma neighbourhood_nempty: 
  "\<lbrakk>dblton_graph G; v \<in> Vs G\<rbrakk> \<Longrightarrow> neighbourhood G v \<noteq> {}"
  apply(auto simp: dblton_graph_def neighbourhood_def Vs_def)
  by (metis empty_iff insert_iff insert_commute)

lemma neighbourhood_subset_Vs: "neighbourhood G v \<subseteq> Vs G"
  using edges_are_Vs
  by blast

locale choose = 
  fixes sel
  assumes sel: "\<lbrakk>finite s; s \<noteq> {}\<rbrakk> \<Longrightarrow> (sel s) \<in> s"

begin

definition
  "sel_edge G =( 
     let v1 = sel (Vs G);
         v2 = sel (neighbourhood G v1)
     in
        {v1,v2})"

lemma sel_edge: 
  assumes "graph_invar G" "G \<noteq> {}"
  shows "sel_edge G \<in> G"
proof-
  have "finite (Vs G)"
    by (simp add: assms(1))
  hence "finite (neighbourhood G (sel (Vs G)))"
    by (meson neighbourhood_subset_Vs rev_finite_subset)
  moreover have "Vs G \<noteq> {}"
    using assms
    by (auto elim!: dblton_graphE simp: Vs_def)
  moreover hence "neighbourhood G (sel (Vs G)) \<noteq> {}"
    apply(intro neighbourhood_nempty)
    using assms sel
    by auto
  ultimately show ?thesis
    using sel[of "Vs G"] sel[of "neighbourhood G (sel (Vs G))"]
    by (auto simp: sel_edge_def Let_def insert_commute)
qed

definition
  "sel_pair (dG:: ('a \<times> 'a) set) =( 
     let v1 = sel (fst ` dG);
         v2 = sel (Pair_Graph.neighbourhood dG v1)
     in
        (v1,v2))"
end

lemma dir_neighbourhood_nempty: 
  "\<lbrakk>v1 \<in> (fst ` (dG::('a \<times> 'b) set))\<rbrakk> \<Longrightarrow> (Pair_Graph.neighbourhood dG v1) \<noteq> {}"
  by auto

context choose
begin

lemma sel_pair[intro!]:
  assumes "finite (dG::('a \<times> 'a) set)" "dG \<noteq> {}"
  shows "sel_pair dG \<in> dG"
proof-

  have "(fst ` dG) \<noteq> {}"
    using assms
    by auto
  hence"(Pair_Graph.neighbourhood dG (sel (fst ` dG)))  \<noteq> {}"
    apply(intro dir_neighbourhood_nempty)
    using assms sel
    by auto
  moreover have "finite (dVs dG)" 
   using \<open>finite dG\<close> 
   by (simp add: finite_vertices_iff)
  hence "finite (Pair_Graph.neighbourhood dG (sel (fst ` dG)))"
    using subset_neighbourhood_dVs rev_finite_subset 
    by fastforce

 ultimately show ?thesis
    using sel[of "fst ` dG"] sel[of "Pair_Graph.neighbourhood dG (sel (fst ` dG))"]
    by (auto simp: sel_pair_def )
qed

end

end