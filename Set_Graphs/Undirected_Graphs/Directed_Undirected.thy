theory Directed_Undirected 
  imports Directed_Set_Graphs.Awalk Undirected_Set_Graphs Pair_Graph_Berge_Adaptor
begin

subsection \<open>Relationship between Symmetric Directed Graphs and Undirected Graphs\<close>

text \<open>This should have gone to Undirected-Set-Graphs, but importing certain bits of directed graph
           theory seems to make some force and fastforce calls loops in subsequent theories.\<close>

definition "symmetric_digraph E = (\<forall> u v. (u, v) \<in> E \<longrightarrow> (v, u) \<in> E)"

lemma symmetric_digraphI:
  "(\<And> u v. (u, v) \<in> E \<Longrightarrow> (v, u) \<in> E) \<Longrightarrow> symmetric_digraph E"
and  symmetric_digraphE:
  "\<lbrakk>symmetric_digraph E; (\<And> u v. (u, v) \<in> E \<Longrightarrow> (v, u) \<in> E) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
and  symmetric_digraphD:
  "\<lbrakk>symmetric_digraph E; (u, v) \<in> E\<rbrakk> \<Longrightarrow> (v, u) \<in> E"
  by(auto simp add: symmetric_digraph_def)

definition "UD G = { {u, v} | u v. (u, v) \<in>  G}"

lemma in_UDI: "(u, v) \<in> E \<Longrightarrow> {u, v} \<in> UD E"
and in_UDE: "\<lbrakk>{u, v} \<in> UD E; (u, v) \<in> E \<Longrightarrow> P; (v, u) \<in> E \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
and in_UD_symE: "\<lbrakk>{u, v} \<in> UD E; symmetric_digraph E; ((u, v) \<in> E \<Longrightarrow> P)\<rbrakk> \<Longrightarrow> P"
and in_UD_symD: "\<lbrakk>{u, v} \<in> UD E; symmetric_digraph E\<rbrakk> \<Longrightarrow> (u, v) \<in> E"
  by(auto simp add: UD_def doubleton_eq_iff symmetric_digraph_def)

lemma symmetric_digraph_walk_betw_vwalk_bet:
  assumes "symmetric_digraph E" "walk_betw (UD E) u p v"
  shows "vwalk_bet E u p v"
  using assms (2,1)
  apply(induction rule: induct_walk_betw)
  apply(simp add: UD_def dVs_def vs_member vwalk_bet_reflexive )
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
  "\<lbrakk>set (edges_of_path Q) \<subseteq> UD E; symmetric_digraph E\<rbrakk> \<Longrightarrow> set (edges_of_vwalk Q) \<subseteq> E"
  by(induction Q rule: edges_of_path.induct)
    (auto simp add: doubleton_eq_iff UD_def elim: symmetric_digraphE)

lemma directed_edges_subset_undirected_edges_subset:
  "set (edges_of_vwalk Q) \<subseteq> E \<Longrightarrow> set (edges_of_path Q) \<subseteq> UD E"
  by(induction Q rule: edges_of_path.induct)
    (auto simp add: doubleton_eq_iff intro!: in_UDI)

text \<open>Ordered pair to undirected edge\<close>

definition "set_of_pair = ( \<lambda>(u,v). {u,v})"

lemma set_of_pair_applied_to_pair: "set_of_pair (u, v) = {u, v}"
  by(auto simp add: set_of_pair_def)

lemma get_urlist_to_dbltn: 
  "set X \<subseteq> set_of_pair ` Y \<Longrightarrow> \<exists> urX. map set_of_pair urX = X \<and> set urX \<subseteq> Y" 
proof(induction X)
  case Nil
  then show ?case by auto
next
  case (Cons a X)
  then obtain ura where "ura \<in> Y" "set_of_pair ura = a" by auto
  moreover obtain urX where "map set_of_pair urX = X" "set urX \<subseteq> Y"
    using Cons by auto
  ultimately show ?case
    by(auto intro!: exI[of _ "ura#urX"])
qed

lemma to_dbltn_sym: "{fst x, snd x} = set_of_pair x" 
  by (auto simp add: set_of_pair_def)

definition "pick_one e = (SOME v. v \<in> e)"
definition "pick_another e = (SOME v. v \<in> e \<and> v \<noteq> pick_one e)"

lemma pick_one_of_singleton: "e = {u} \<Longrightarrow> pick_one e = u"
  by (simp add: pick_one_def)

lemma pick_one_and_another_props:
  assumes "\<exists> u v. e = {u, v} \<and> u \<noteq> v" 
  shows   "pick_one e \<in> e" "pick_another e \<in> e"
          "e = {pick_one e, pick_another e}"
proof-
  obtain u v where uv: "e = {u, v}" "u \<noteq> v" using assms by auto
  have "pick_one e = u \<or> pick_one e = v"
    using uv some_in_eq[of e]
    by(simp add: pick_one_def)
  moreover have "pick_one e = u \<Longrightarrow> pick_another e = v"
                "pick_one e = v \<Longrightarrow> pick_another e = u"
    using uv
    by(auto simp add: pick_another_def)
  ultimately show  "pick_one e \<in> e" "pick_another e \<in> e" "e = {pick_one e, pick_another e}"
    using uv by auto
qed

lemma distinct_no_self_loop_in_edges_of_vwalk:
  "distinct p \<Longrightarrow> \<nexists> x. (x,x) \<in> set (edges_of_vwalk p)"
  by(induction p rule: edges_of_vwalk.induct) auto

lemma path_edges_set_of_pair_of_vwalk_edges:
  "edges_of_path p = map set_of_pair (edges_of_vwalk p)"
  by(induction p rule: edges_of_vwalk.induct)
    (auto simp add: set_of_pair_def)

lemma UD_is_image_set_of_pair: "UD A = set_of_pair ` A"
  by(auto simp add: UD_def set_of_pair_def)

lemma "set (edges_of_path p) = UD (set (edges_of_vwalk p))"
  by(auto simp add: path_edges_set_of_pair_of_vwalk_edges UD_is_image_set_of_pair)

lemma UD_diff_hom: "symmetric_digraph B \<Longrightarrow> UD (A - B) = UD A - UD B"
  by(fastforce simp add: UD_def doubleton_eq_iff elim!: symmetric_digraphE)

lemma UD_union_hom: "UD (A \<union> B) = UD A \<union> UD B"
  by(auto simp add: UD_def)

lemma symmetric_union_pres:
   "\<lbrakk>symmetric_digraph A; symmetric_digraph B\<rbrakk> \<Longrightarrow> symmetric_digraph (A \<union> B)"
  by(auto simp add:  symmetric_digraph_def)

lemma symmetric_diff_pres:
   "\<lbrakk>symmetric_digraph A; symmetric_digraph B\<rbrakk> \<Longrightarrow> symmetric_digraph (A - B)"
  by(auto simp add:  symmetric_digraph_def)

lemma symmetric_digraph_by_def: "symmetric_digraph {(u, v). {u, v} \<in> G}"
  by (simp add: insert_commute symmetric_digraph_def)

lemma UD_inverse_of_D: "dblton_graph G \<Longrightarrow> UD {(u, v). {u, v} \<in> G} = G"
  unfolding UD_def dblton_graph_def 
  by auto metis

lemma distinc_p_dblton_edges: "distinct p \<Longrightarrow> dblton_graph (set (edges_of_path p))"
  using graph_abs_edges_of_distinct_path by blast

lemma D_of_edges_of_path:
  "{(u, v) | u v.  {u, v} \<in>  (set (edges_of_path p))} = 
    set (edges_of_vwalk p) \<union> prod.swap ` set (edges_of_vwalk p)"
  by(induction p rule: edges_of_path.induct)
    (auto split: prod.split simp add: doubleton_eq_iff)

context graph_abs
begin

lemma "UD D = G"
  apply(auto simp add: D_def UD_def)
  by blast

end
(*TODO MOVE*)
definition "dpairs_of_map m = {(x, y) | x y. m x = Some y}"
definition "upairs_of_map m = {{x, y} | x y. m x = Some y}"

lemma upairs_dpairs_of_map: "upairs_of_map m = UD (dpairs_of_map m)"
  by(auto simp add: upairs_of_map_def dpairs_of_map_def UD_def)

end