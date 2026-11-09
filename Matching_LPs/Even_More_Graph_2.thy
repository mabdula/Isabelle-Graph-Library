(*
  Author: Ralitsa Dordjonova
  Author: Mohammad Abdulaziz
*)

theory Even_More_Graph_2
  imports Undirected_Set_Graphs.Undirected_Set_Graphs
begin

provenance human

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
proof \<^marker>\<open>provenance ai\<close> -
  assume "finite s"
  then have "\<exists>l. set l = s \<and> distinct l"
    using finite_distinct_list by blast
  then have "set (SOME l. set l = s \<and> distinct l) = s \<and> distinct (SOME l. set l = s \<and> distinct l)"
    by (rule someI_ex)
  then show "set (SOME l. set l = s \<and> distinct l) = s"
    by simp
qed

lemma  set_set_to_list_distinct:
  "finite s \<Longrightarrow> distinct (set_to_list s)"
  unfolding set_to_list_def
proof \<^marker>\<open>provenance ai\<close> -
  assume "finite s"
  then have "\<exists>l. set l = s \<and> distinct l"
    using finite_distinct_list by blast
  then show "distinct (SOME l. set l = s \<and> distinct l)"
    by (rule someI2_ex) simp
qed


definition edges_list :: "'b set set \<Rightarrow> ('b set) list" where
  "edges_list E = set_to_list E"

lemma edges_list_el_in_E:
  assumes "k < card E"
  shows "edges_list E ! k \<in> E"
proof -
  have "finite E" 
  proof \<^marker>\<open>provenance ai\<close> (rule ccontr)
    assume "\<not> finite E"
    then have "card E = 0"
      by (rule card.infinite)
    with assms(1) show False
      by simp
  qed
  have "set (edges_list E) = E" 
    unfolding edges_list_def using set_set_to_list 
    using \<open>finite E\<close> by blast
  have "edges_list E ! k \<in> set (edges_list E)" 
proof \<^marker>\<open>provenance ai\<close> -
  have "distinct (edges_list E)"
    unfolding edges_list_def using set_set_to_list_distinct \<open>finite E\<close> by blast
  hence len_eq: "length (edges_list E) = card (set (edges_list E))"
    by (simp add: distinct_card)
  have "card (set (edges_list E)) = card E"
    using \<open>set (edges_list E) = E\<close> by simp
  hence "length (edges_list E) = card E"
    using len_eq by simp
  hence "k < length (edges_list E)"
    using assms by simp
  then show "edges_list E ! k \<in> set (edges_list E)"
    by (rule nth_mem)
qed
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
proof \<^marker>\<open>provenance ai\<close> (rule ccontr)
  assume "infinite (Vs E)"
  then have "card (Vs E) = 0"
    by (rule card.infinite)
  with assms(1) show False
    by simp
qed
  have "set (vertices_list E) = Vs E" 
    unfolding vertices_list_def using set_set_to_list 
    using \<open>finite (Vs E)\<close> by blast
  then have "vertices_list E ! k \<in> set (vertices_list E)" 
proof \<^marker>\<open>provenance ai\<close> -
  assume E: "set (vertices_list E) = Vs E"
  have "card (set (vertices_list E)) \<le> length (vertices_list E)"
    by (rule card_length)
  with E have "card (Vs E) \<le> length (vertices_list E)"
    by simp
  with assms have "k < length (vertices_list E)"
    by simp
  then show ?thesis
    by (rule nth_mem)
qed
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
    proof \<^marker>\<open>provenance ai\<close> (rule ccontr)
      assume "\<not> finite (Vs E)"
      then have "card (Vs E) = 0"
        by (rule card.infinite)
      then show False
        using assms(1) by simp
    qed
  have "distinct (vertices_list E)" 
    by (simp add: \<open>finite (Vs E)\<close> distinct_vert_list)
  then show ?thesis
  proof \<^marker>\<open>provenance ai\<close> -
    have set_eq: "set (vertices_list E) = Vs E"
      unfolding vertices_list_def
      using set_set_to_list[OF \<open>finite (Vs E)\<close>] by simp
    have len_eq: "length (vertices_list E) = card (Vs E)"
    proof -
      have "length (vertices_list E) = card (set (vertices_list E))"
        using distinct_card[OF \<open>distinct (vertices_list E)\<close>] by simp
      also have "\<dots> = card (Vs E)"
        by (simp add: set_eq)
      finally show ?thesis .
    qed
    have i_lt: "i < length (vertices_list E)"
      using assms(1) len_eq by simp
    have j_lt: "j < length (vertices_list E)"
      using assms(2) len_eq by simp
    show ?thesis
      using nth_eq_iff_index_eq[OF \<open>distinct (vertices_list E)\<close> i_lt j_lt] assms(3)
      by auto
  qed
qed

end