theory choose
  imports Main 
          Undirected_Set_Graphs.Pair_Graph_Berge_Adaptor
          Undirected_Set_Graphs.Undirected_Set_Graphs 
begin

lemma neighbourhood_nempty: 
  "\<lbrakk>dblton_graph G; v \<in> Vs G\<rbrakk> \<Longrightarrow> neighbourhood G v \<noteq> {}"
  apply(auto simp: dblton_graph_def neighbourhood_def Vs_def)
  by (metis empty_iff insert_iff insert_commute)

locale choose = 
  fixes sel
  assumes sel: "\<lbrakk>s \<noteq> {}\<rbrakk> \<Longrightarrow> (sel s) \<in> s"

begin

definition
  "sel_edge G \<equiv> 
     let v1 = sel (Vs G);
         v2 = sel (neighbourhood G v1)
     in
        {v1,v2}"


lemma sel_edge: 
  assumes "graph_invar G" "G \<noteq> {}"
  shows "sel_edge G \<in> G"
proof-

  have "Vs G \<noteq> {}"
    using assms
    by (auto elim!: dblton_graphE simp: Vs_def)
  moreover hence "neighbourhood G (sel (Vs G)) \<noteq> {}"
    apply(intro neighbourhood_nempty)
    using assms sel
    by auto
  thus ?thesis
    using sel[of "Vs G"] sel[of "neighbourhood G (sel (Vs G)) "]
    by (auto simp: sel_edge_def Let_def insert_commute neighbourhood_def)
qed

end

locale choose_pair = ch1: choose sel1 + ch2: choose sel2 for sel1 sel2 
begin

definition
  "sel_pair (dG:: ('a \<times> 'b) set) \<equiv> 
     let v1 = sel1 (fst ` dG);
         v2 = sel2 (Pair_Graph.neighbourhood dG v1)
     in
        (v1,v2)"

end


lemma dir_neighbourhood_nempty: 
  "\<lbrakk>v1 \<in> (fst ` (dG::('a \<times> 'b) set))\<rbrakk> \<Longrightarrow> (Pair_Graph.neighbourhood dG v1) \<noteq> {}"
  by auto


context choose_pair
begin

lemma sel_pair[intro!]:
  assumes "dG \<noteq> {}"
  shows "sel_pair dG \<in> dG"
proof-

  have "(fst ` dG) \<noteq> {}"
    using assms
    by auto
  moreover hence "(Pair_Graph.neighbourhood dG (sel1 (fst ` dG)))  \<noteq> {}"
    apply(intro dir_neighbourhood_nempty)
    using assms ch1.sel
    by auto
  thus ?thesis
    using ch1.sel[of "fst ` dG"] ch2.sel[of "Pair_Graph.neighbourhood dG (sel1 (fst ` dG))"]
    by (auto simp: sel_pair_def Let_def insert_commute Pair_Graph.neighbourhood_def image_def)
qed

end



end