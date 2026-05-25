theory Even_More_Graph_2
  imports Undirected_Set_Graphs.Undirected_Set_Graphs
begin

(*definition Vs where "Vs E \<equiv> \<Union> E"*)

(*abbreviation "graph_invar E \<equiv> (\<forall>e\<in>E. \<exists>u v. e = {u, v} \<and> u \<noteq> v) \<and> finite (Vs E)"*)

lemma card_edge:
  assumes "graph_invar E"
  shows "\<forall> e\<in> E. card e = 2" 
  using assms
  by (auto simp add: dblton_graph_def card_2_iff)

definition set_to_list :: "'b set \<Rightarrow> 'b list"
  where "set_to_list s = (SOME l. set l = s \<and> distinct l)"

lemma  set_set_to_list:
  "finite s \<Longrightarrow> set (set_to_list s) = s"
  unfolding set_to_list_def
  by (metis (mono_tags, lifting) finite_distinct_list someI)

lemma  set_set_to_list_distinct:
  "finite s \<Longrightarrow> distinct (set_to_list s)"
  unfolding set_to_list_def
  by (metis (mono_tags, lifting) finite_distinct_list someI)


definition edges_list :: "'b set set \<Rightarrow> ('b set) list" where
  "edges_list E = set_to_list E"

lemma edges_list_el_in_E:
  assumes "k < card E"
  shows "edges_list E ! k \<in> E"
proof -
  have "finite E" 
    by (metis assms(1) card.infinite not_less_zero)
  have "set (edges_list E) = E" 
    unfolding edges_list_def using set_set_to_list 
    using \<open>finite E\<close> by blast
  have "edges_list E ! k \<in> set (edges_list E)" 
    by (metis \<open>set (edges_list E) = E\<close> assms card_length not_less nth_mem order_trans_rules(23))
  show ?thesis 
    using \<open>edges_list E ! k \<in> set (edges_list E)\<close> \<open>set (edges_list E) = E\<close> by blast
qed

lemma distinct_edges_list:
  assumes "finite E" 
  shows "distinct (edges_list E)"
  unfolding edges_list_def
  using set_set_to_list_distinct assms 
  by blast

definition vertices_list :: "'b set set \<Rightarrow> 'b list" where
  "vertices_list E = set_to_list (Vs E)" 

lemma vert_list_el_in_VsE:
  assumes "k < card (Vs E)"
  shows "vertices_list E ! k \<in> Vs E"
proof -
  have "finite (Vs E)" 
    by (metis assms(1) card.infinite not_less_zero)
  have "set (vertices_list E) = Vs E" 
    unfolding vertices_list_def using set_set_to_list 
    using \<open>finite (Vs E)\<close> by blast
  then have "vertices_list E ! k \<in> set (vertices_list E)" 
    by (metis assms card_length not_less nth_mem order_trans_rules(23))
  then show ?thesis 
    using \<open>set (vertices_list E) = Vs E\<close> by blast
qed

lemma distinct_vert_list:
  assumes "finite (Vs E)" 
  shows "distinct (vertices_list E)"
  unfolding vertices_list_def
  using set_set_to_list_distinct assms 
  by blast

lemma diff_verts:
  assumes "i < card (Vs E)"
  assumes "j < card (Vs E)"
  assumes "i \<noteq> j"
  shows "vertices_list E ! i \<noteq> vertices_list E ! j"
proof -
  have "finite (Vs E)" 
    by (metis assms(1) card.infinite less_nat_zero_code)
  have "distinct (vertices_list E)" 
    by (simp add: \<open>finite (Vs E)\<close> distinct_vert_list)
  then show ?thesis 
    unfolding vertices_list_def
    by (metis \<open>finite (Vs E)\<close> assms distinct_card nth_eq_iff_index_eq set_set_to_list)
qed

end