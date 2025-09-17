theory Directed_Undirected 
  imports Directed_Set_Graphs.Awalk Undirected_Set_Graphs
begin

subsection \<open>Relationship between Symmetric Directed Graphs and Undirected Graphs\<close>

text \<open>This should have gone to Undirected-Set-Graphs, but importing certain bits of directed graph
           theory seems to make some force and fastforce calls loops in subsequent theories.\<close>

definition "symmetric_digraph E = (\<forall> u v. (u, v) \<in> E \<longrightarrow> (v, u) \<in> E)"

lemma symmetric_digraphI:
"(\<And> u v. (u, v) \<in> E \<Longrightarrow> (v, u) \<in> E) \<Longrightarrow> symmetric_digraph E"
and  symmetric_digraphE:
"symmetric_digraph E \<Longrightarrow> ((\<And> u v. (u, v) \<in> E \<Longrightarrow> (v, u) \<in> E) \<Longrightarrow> P) \<Longrightarrow> P"
and  symmetric_digraphD:
"symmetric_digraph E \<Longrightarrow>  (u, v) \<in> E \<Longrightarrow> (v, u) \<in> E"
  by(auto simp add: symmetric_digraph_def)

definition "UD G = { {u, v} | u v. (u, v) \<in>  G}"

lemma in_UDI: "(u, v) \<in> E \<Longrightarrow> {u, v} \<in> UD E"
and in_UDE: "{u, v} \<in> UD E \<Longrightarrow> ((u, v) \<in> E \<Longrightarrow> P) \<Longrightarrow> ((v, u) \<in> E \<Longrightarrow> P) \<Longrightarrow> P"
and in_UD_symE: "\<lbrakk>{u, v} \<in> UD E; symmetric_digraph E; ((u, v) \<in> E \<Longrightarrow> P)\<rbrakk> \<Longrightarrow> P"
and in_UD_symD: "\<lbrakk>{u, v} \<in> UD E; symmetric_digraph E\<rbrakk> \<Longrightarrow> (u, v) \<in> E"
  by(auto simp add: UD_def doubleton_eq_iff symmetric_digraph_def)

lemma symmetric_digraph_walk_betw_vwalk_bet:
  assumes "symmetric_digraph E" "walk_betw (UD E) u p v"
  shows "vwalk_bet E u p v"
  using assms (2,1)
  apply(induction rule: induct_walk_betw)
  apply (simp add: UD_def dVs_def vs_member vwalk_bet_reflexive )
  by (simp add: in_UD_symD)

lemma symmetric_digraph_vwalk_betw_walk_betw:
  assumes "symmetric_digraph E" "vwalk_bet E u p v"
  shows "walk_betw (UD E) u p v"
  using assms (2,1)
  apply(induction rule: induct_vwalk_bet)
  apply (simp add: UD_def dVs_def vs_member walk_reflexive)
  by (meson edges_are_walks in_UDI walk_betw_cons)

lemma symmetric_digraph_vwalk_bet_vwalk_bet:
  assumes "symmetric_digraph E" "vwalk_bet E u p v"
  shows "vwalk_bet E v (rev p) u"
  using assms (2,1)
  apply(induction rule: induct_vwalk_bet)
  apply (simp add: UD_def dVs_def vs_member vwalk_bet_reflexive)
  using symmetric_digraphD vwalk_append_intermediate_edge by fastforce

lemma undirected_edges_subset_directed_edges_subset:
  "\<lbrakk>set (edges_of_path Q) \<subseteq> UD E; symmetric_digraph E\<rbrakk>
     \<Longrightarrow> set (edges_of_vwalk Q) \<subseteq> E"
  by(induction Q rule: edges_of_path.induct)
    (auto simp add: doubleton_eq_iff UD_def elim: symmetric_digraphE)

lemma directed_edges_subset_undirected_edges_subset:
  "set (edges_of_vwalk Q) \<subseteq> E \<Longrightarrow> set (edges_of_path Q) \<subseteq> UD E"
  by(induction Q rule: edges_of_path.induct)
    (auto simp add: doubleton_eq_iff intro!: in_UDI)

end