theory Pair_Graph_U_Specs
  imports Awalk "Map_Addons" "Set_Addons" Pair_Graph_Specs
begin

(* Note: This file is still a work-in-progress, might change/remove some things *)

definition "set_of_pair \<equiv> \<lambda>(u,v). {u,v}"

datatype 'v uedge = uEdge 'v 'v

definition "set_of_uedge e \<equiv> case e of uEdge u v \<Rightarrow> {u,v}"

locale Pair_Graph_U_Specs = Pair_Graph_Specs
  where lookup = lookup for lookup :: "'adj \<Rightarrow> ('v::linorder) \<Rightarrow> 'neighb option"
begin

definition "vertices G \<equiv> {u | u v. v \<in>\<^sub>G (\<N>\<^sub>G G u)} \<union> {v | u v. v \<in>\<^sub>G (\<N>\<^sub>G G u)}" 

lemma vertices_equiv_dVs:
  "vertices G = dVs (digraph_abs G)"
  unfolding vertices_def digraph_abs_def dVs_def by auto

fun rep :: "'v uedge \<Rightarrow> 'v uedge" where
  "rep (uEdge u v) = (if u \<le> v then uEdge u v else uEdge v u)"

lemma is_rep:
  "rep (uEdge u v) = rep (uEdge v u)" 
  "rep (uEdge u v) = uEdge u v \<or> rep (uEdge u v) = uEdge v u"
  by auto


definition "uedges G \<equiv> (\<lambda>(u,v). rep (uEdge u v)) ` (digraph_abs G)"  

(* Note: edges in other file corresponds to digraph_abs in Pair_Graph *)


(* TODO how to define this? Maybe relate to set_of_edge ` uedges? *)
definition ugraph_abs where "ugraph_abs G \<equiv> {{u, v} | u v. v \<in>\<^sub>G (\<N>\<^sub>G G u)}" 


context
  includes adj.automation neighb.set.automation
begin

lemma uedges_def2: "uedges G = {rep (uEdge u v) | u v. v \<in>\<^sub>G (\<N>\<^sub>G G u)}"
  unfolding uedges_def digraph_abs_def by force

lemma isin_uedges: "v \<in>\<^sub>G (\<N>\<^sub>G G u) \<Longrightarrow> rep (uEdge u v) = e \<Longrightarrow> e \<in> uedges G"
  unfolding uedges_def2 by force

thm adj.invar_empty
thm neighb.set.invar_empty

lemma uedges_empty: "uedges empty = {}"
  unfolding uedges_def digraph_abs_def neighbourhood_def 
  by (auto)

lemma finite_uedges:
  "graph_inv G \<Longrightarrow> finite_graph G \<Longrightarrow> finite_neighbs \<Longrightarrow> finite (uedges G)"
  unfolding uedges_def by auto

lemma set_of_uedge: "set_of_uedge (uEdge u v) = {u,v}"
  unfolding set_of_uedge_def by auto

(* Pair_Graph_Specs axioms + symmetric, irreflexive *)
(* The axioms in ugraph_adj_map_invar are covered by these axioms *)
definition "pair_graph_u_invar G \<equiv> 
  graph_inv G \<and> finite_graph G \<and> finite_neighbs \<and>
  (\<forall>v. \<not> v \<in>\<^sub>G (\<N>\<^sub>G G v)) \<and>
  (\<forall>u v. v \<in>\<^sub>G (\<N>\<^sub>G G u) \<longrightarrow> u \<in>\<^sub>G (\<N>\<^sub>G G v))"


context
  fixes G::'adj
  assumes "pair_graph_u_invar G"
begin

lemma invar_graph_inv[simp, intro!]:
  "graph_inv G"
  using \<open>pair_graph_u_invar G\<close>
  by (auto simp add: pair_graph_u_invar_def)

lemma invar_finite_graph[simp, intro!]:
  "finite_graph G"
  using \<open>pair_graph_u_invar G\<close>
  by (auto simp add: pair_graph_u_invar_def)

lemma invar_finite_neighbs[simp, intro!]:
  "finite_neighbs"
  using \<open>pair_graph_u_invar G\<close>
  by (auto simp add: pair_graph_u_invar_def)

lemma invar_finite_vertices[intro!]:
  "finite (dVs (digraph_abs G))"
  by blast

lemma graph_irreflexive[simp]:
  "\<not> v \<in>\<^sub>G (\<N>\<^sub>G G v)"
  using \<open>pair_graph_u_invar G\<close>
  by (auto simp add: pair_graph_u_invar_def)

lemma graph_symmetric[simp, intro]:
  "v \<in>\<^sub>G (\<N>\<^sub>G G u) \<Longrightarrow> u \<in>\<^sub>G (\<N>\<^sub>G G v)"
  using \<open>pair_graph_u_invar G\<close>
  by (auto simp add: pair_graph_u_invar_def)

lemma digraph_abs_irreflexive:
  "\<forall>x \<in> dVs (digraph_abs G). (x, x) \<notin> digraph_abs G"
  unfolding digraph_abs_def by fastforce

lemma digraph_abs_symmetric:
  "(\<forall>(x, y) \<in> (digraph_abs G). (y, x) \<in> digraph_abs G)"
  unfolding digraph_abs_def by blast



lemma adj_vertices_neq:
  assumes "v \<in>\<^sub>G (\<N>\<^sub>G G u)"
  shows "u \<noteq> v"
  using assms by force

lemma vertices_def2: 
  "vertices G = {u | u v. v \<in>\<^sub>G (\<N>\<^sub>G G u)}"
  unfolding vertices_def using graph_symmetric by auto

(* TODO vs_uedges_subset_vertices *)

lemma isin_neighborhood_set_edge: 
  assumes "v \<in>\<^sub>G (\<N>\<^sub>G G u)"
  shows "{u,v} \<in> set_of_uedge ` uedges G"
proof -
  have "rep (uEdge u v) \<in> uedges G"
    using assms by (auto simp: uedges_def2)
  then consider "uEdge u v \<in> uedges G" | "uEdge v u \<in> uedges G"
    using is_rep by metis
  then consider "set_of_uedge (uEdge u v) \<in> set_of_uedge ` uedges G" 
    | "set_of_uedge (uEdge v u) \<in> set_of_uedge ` uedges G"
    by cases (auto intro: imageI)
  thus "{u,v} \<in> set_of_uedge ` uedges G"
    by cases (auto simp: set_of_uedge doubleton_eq_iff)
qed

(*
lemma vertices_subset_vs_uedges:
  assumes "u \<in> vertices G"
  shows "u \<in> Vs (set_of_uedge ` uedges G)"
proof -
  consider v where "v \<in>\<^sub>G (\<N>\<^sub>G G u)" | v where "u \<in>\<^sub>G (\<N>\<^sub>G G v)"
    using assms[unfolded vertices_def] by auto
  then consider v where "{u,v} \<in> set_of_uedge ` uedges G"
    using isin_neighborhood_set_edge by cases fast+
  thus ?thesis
    sorry
qed
*)

lemma graph_abs_symmetric[simp]:
  "(u, v) \<in> (digraph_abs G) \<Longrightarrow> (v, u) \<in> (digraph_abs G)"
  unfolding digraph_abs_def using graph_symmetric by blast

lemma rev_vwalk:
  "Vwalk.vwalk (digraph_abs G) P \<Longrightarrow> Vwalk.vwalk (digraph_abs G) (rev P)"
  apply (induction P rule: vwalk.induct) 
  apply simp
  apply simp
  using vwalk_append_single graph_abs_symmetric last_rev
  by (metis last_rev list.sel(1) rev.simps(2))

lemma rev_vwalk_bet:
  "vwalk_bet (digraph_abs G) u P v \<Longrightarrow> vwalk_bet (digraph_abs G) v (rev P) u"
  unfolding vwalk_bet_def using rev_vwalk
  by (simp add: hd_rev last_rev)
  
(* finite paths, distinct_subpath *)

lemma rep_idem: "rep (rep e) = rep e"
proof -
  obtain u v where [simp]: "e = uEdge u v"
    by (cases e)
  then consider "rep e = uEdge u v" | "rep e = uEdge v u"
    using is_rep by auto
  thus ?thesis
    using is_rep by cases auto
qed

lemma rep_simps:
  assumes "rep e = uEdge u v"
  shows "rep e = rep (uEdge u v)" "rep e = rep (uEdge v u)" 
    "rep (uEdge u v) = uEdge u v" "rep (uEdge v u) = uEdge u v"
proof -
  show "rep e = rep (uEdge u v)" 
    apply (subst assms[symmetric])
    apply (rule rep_idem[symmetric])
    done
  thus "rep e = rep (uEdge v u)" 
    by (auto simp add: is_rep) 
  thus "rep (uEdge u v) = uEdge u v" "rep (uEdge v u) = uEdge u v"
    using assms by (auto simp only: is_rep) 
qed 

lemma rep_elim:
  assumes "rep e = rep (uEdge u v)"
  obtains "e = uEdge u v" | "e = uEdge v u"
  using assms is_rep by (cases e) (metis uedge.inject)

lemma rep_cases:
  assumes "rep e = rep (uEdge u v)"
  obtains "rep e = uEdge u v" | "rep e = uEdge v u"
  using assms is_rep by auto

lemma rep_isin_uedges_elim:
  assumes "rep e \<in> uedges G"
  obtains u v where "e = uEdge u v" "v \<in>\<^sub>G (\<N>\<^sub>G G u)"
proof -
  obtain u v where "rep e = rep (uEdge u v)" and v_isin_Nu: "v \<in>\<^sub>G (\<N>\<^sub>G G u)"
    using assms[unfolded uedges_def2] neighbourhood_def by auto
  then consider "e = uEdge u v" | "e = uEdge v u"
    by (elim rep_elim)
  thus ?thesis
    using that assms v_isin_Nu
    apply cases
    apply (simp add: neighbourhood_def uedges_def)
    using graph_symmetric by presburger
qed                       

lemma rep_isin_uedges_elim2:
  assumes "rep (uEdge u v) \<in> uedges G"
  shows "v \<in>\<^sub>G (\<N>\<^sub>G G u)"
  using assms rep_isin_uedges_elim by blast

lemma rep_of_edge: "e \<in> uedges G \<Longrightarrow> rep e = e"
  unfolding uedges_def2 by (auto simp add: rep_idem)

lemma rep_of_edge_is_edge: "e \<in> uedges G \<Longrightarrow> rep e \<in> uedges G"
  unfolding uedges_def by (force simp add: rep_idem)

lemma isin_uedges_elim:
  assumes "e \<in> uedges G"
  obtains u v where "e = uEdge u v" "v \<in>\<^sub>G (\<N>\<^sub>G G u)"
proof -
  have "rep e \<in> uedges G"
    using assms by (auto simp add: rep_of_edge)
  thus ?thesis
    using assms that by (elim rep_isin_uedges_elim)
qed

lemma uedge_not_refl_elim:
  assumes "e \<in> uedges G"
  obtains u v where "rep e = uEdge u v" "u \<noteq> v"
  using assms
proof (rule isin_uedges_elim)
  fix u v
  assume "e = uEdge u v" "v \<in>\<^sub>G (\<N>\<^sub>G G u)"
  moreover hence "u \<noteq> v"
    using assms by (force intro: adj_vertices_neq)
  ultimately show ?thesis
    using assms that by (auto simp: rep_of_edge simp del: rep.simps)
qed

lemma uedge_not_refl:
  assumes "rep (uEdge u v) \<in> uedges G"
  shows "u \<noteq> v"
proof -
  have "v \<in>\<^sub>G (\<N>\<^sub>G G u)" 
    using assms rep_isin_uedges_elim by blast
  thus "u \<noteq> v"
    using assms by (force intro: adj_vertices_neq)
qed

lemma rep_eq_iff: "rep (uEdge u\<^sub>1 v\<^sub>1) = rep (uEdge u\<^sub>2 v\<^sub>2) \<longleftrightarrow> (u\<^sub>1 = u\<^sub>2 \<and> v\<^sub>1 = v\<^sub>2) \<or> (u\<^sub>1 = v\<^sub>2 \<and> v\<^sub>1 = u\<^sub>2)"
proof
  consider "rep (uEdge u\<^sub>1 v\<^sub>1) = uEdge u\<^sub>1 v\<^sub>1" "rep (uEdge u\<^sub>2 v\<^sub>2) = uEdge u\<^sub>2 v\<^sub>2"
    | "rep (uEdge u\<^sub>1 v\<^sub>1) = uEdge u\<^sub>1 v\<^sub>1" "rep (uEdge u\<^sub>2 v\<^sub>2) = uEdge v\<^sub>2 u\<^sub>2"
    | "rep (uEdge u\<^sub>1 v\<^sub>1) = uEdge v\<^sub>1 u\<^sub>1" "rep (uEdge u\<^sub>2 v\<^sub>2) = uEdge u\<^sub>2 v\<^sub>2"
    | "rep (uEdge u\<^sub>1 v\<^sub>1) = uEdge v\<^sub>1 u\<^sub>1" "rep (uEdge u\<^sub>2 v\<^sub>2) = uEdge v\<^sub>2 u\<^sub>2"
    using is_rep by auto
  moreover assume "rep (uEdge u\<^sub>1 v\<^sub>1) = rep (uEdge u\<^sub>2 v\<^sub>2)"
  ultimately consider "uEdge u\<^sub>1 v\<^sub>1 = uEdge u\<^sub>2 v\<^sub>2" | "uEdge u\<^sub>1 v\<^sub>1 = uEdge v\<^sub>2 u\<^sub>2"
    | "uEdge v\<^sub>1 u\<^sub>1 = uEdge u\<^sub>2 v\<^sub>2" | "uEdge v\<^sub>1 u\<^sub>1 = uEdge v\<^sub>2 u\<^sub>2"
    by cases fastforce+
  thus "(u\<^sub>1 = u\<^sub>2 \<and> v\<^sub>1 = v\<^sub>2) \<or> (u\<^sub>1 = v\<^sub>2 \<and> v\<^sub>1 = u\<^sub>2)"
    by cases auto
next
  assume "(u\<^sub>1 = u\<^sub>2 \<and> v\<^sub>1 = v\<^sub>2) \<or> (u\<^sub>1 = v\<^sub>2 \<and> v\<^sub>1 = u\<^sub>2)"
  thus "rep (uEdge u\<^sub>1 v\<^sub>1) = rep (uEdge u\<^sub>2 v\<^sub>2)"
    using is_rep by auto
qed

lemma set_edge_isin_neighborhood: 
  assumes "{u,v} \<in> set_of_uedge ` uedges G"
  shows "v \<in>\<^sub>G (\<N>\<^sub>G G u)"
proof -
  obtain e\<^sub>u where [simp]: "{u,v} = set_of_uedge e\<^sub>u" and "e\<^sub>u \<in> uedges G"
    using assms by auto
  moreover then obtain x y where "e\<^sub>u = rep (uEdge x y)"
    and xy_isin: "y \<in>\<^sub>G (\<N>\<^sub>G G x)" "x \<in>\<^sub>G (\<N>\<^sub>G G y)"
    using assms using uedges_def2 graph_symmetric by auto
  moreover then consider "e\<^sub>u = uEdge x y" | "e\<^sub>u = uEdge y x"
    using is_rep by auto
  ultimately consider "{u,v} = set_of_uedge (uEdge x y)" | "{u,v} = set_of_uedge (uEdge y x)"
    by cases metis+
  hence "{u,v} = {x,y}" 
    by (auto simp: set_of_uedge)
  then consider "u = x" "v = y" | "u = y" "v = x"
    by fastforce
  thus "v \<in>\<^sub>G (\<N>\<^sub>G G u)"
    using xy_isin by cases auto
qed

lemma set_of_rep_uedge: "set_of_uedge (rep (uEdge u v)) = {u,v}"
  unfolding set_of_uedge_def by (rule rep_cases[of "uEdge u v"]) auto

lemma set_of_uedge_rep_idem: "set_of_uedge (rep e) = set_of_uedge e"
proof (cases e)
  fix u v
  assume e_case: "e = uEdge u v"
  then consider "rep e = uEdge u v" | "rep e = uEdge v u"
    using is_rep by auto
  thus ?thesis
    unfolding set_of_uedge_def using e_case by cases (auto simp add: doubleton_eq_iff)
qed

lemma set_edge_isin_neighborhood_elim: 
  assumes "e \<in> set_of_uedge ` uedges G"
  obtains u v where "e = {u,v}" and "v \<in>\<^sub>G (\<N>\<^sub>G G u)"
proof -
  obtain u v where "e = set_of_uedge (rep (uEdge u v))" "v \<in>\<^sub>G (\<N>\<^sub>G G u)"
    using assms[unfolded uedges_def2] by force
  moreover hence "e = {u,v}"
    using set_of_rep_uedge by auto
  ultimately show ?thesis
    using that by auto
qed

lemma set_edge_isin_neighborhood_iff:
  "e \<in> set_of_uedge ` uedges G \<longleftrightarrow> (\<exists>u v. e = {u,v} \<and> v \<in>\<^sub>G (\<N>\<^sub>G G u))"
  using isin_neighborhood_set_edge set_edge_isin_neighborhood_elim by metis

lemma inj_set_of_uedge:
  "inj_on set_of_uedge (uedges G)"
proof
  fix e\<^sub>1 e\<^sub>2
  assume "e\<^sub>1 \<in> uedges G"
  moreover then obtain u\<^sub>1 v\<^sub>1 where [simp]: "e\<^sub>1 = uEdge u\<^sub>1 v\<^sub>1" and "v\<^sub>1 \<in>\<^sub>G (\<N>\<^sub>G G u\<^sub>1)"
    by (elim isin_uedges_elim)
  moreover assume "e\<^sub>2 \<in> uedges G"
  moreover then obtain u\<^sub>2 v\<^sub>2 where [simp]: "e\<^sub>2 = uEdge u\<^sub>2 v\<^sub>2" and "v\<^sub>2 \<in>\<^sub>G (\<N>\<^sub>G G u\<^sub>2)"
    by (elim isin_uedges_elim)
  moreover assume "set_of_uedge e\<^sub>1 = set_of_uedge e\<^sub>2"
  moreover hence "rep e\<^sub>1 = rep e\<^sub>2"
    unfolding set_of_uedge_def by (auto simp add: rep_eq_iff doubleton_eq_iff)
  ultimately show "e\<^sub>1 = e\<^sub>2"
    by (auto simp add: rep_of_edge simp del: rep.simps)
qed

lemma
  "v \<in>\<^sub>G (\<N>\<^sub>G G u) \<Longrightarrow> u \<in>\<^sub>G (\<N>\<^sub>G G v)"
  by (auto simp del: neighbourhood_abs)
  

lemma neighborhood_eq_set_for_edge:
  "(\<lambda>u. {u,v}) ` t_set (\<N>\<^sub>G G v) = {e \<in> set_of_uedge ` uedges G. v \<in> e}"
proof
  show "(\<lambda>u. {u,v}) ` t_set (\<N>\<^sub>G G v) \<subseteq> {e \<in> set_of_uedge ` uedges G. v \<in> e}"
    by (auto intro!: isin_neighborhood_set_edge)
next
  show "{e \<in> set_of_uedge ` uedges G. v \<in> e} \<subseteq> (\<lambda>u. {u,v}) ` t_set (\<N>\<^sub>G G v)"
  proof
    fix e
    assume "e \<in> {e \<in> set_of_uedge ` uedges G. v \<in> e}"
    hence "e \<in> set_of_uedge ` uedges G" and "v \<in> e"
      by auto
    moreover then obtain u w where [simp]: "e = {u,w}" and w_isin_Nu: "w \<in>\<^sub>G (\<N>\<^sub>G G u)"
      by (elim set_edge_isin_neighborhood_elim) auto
    ultimately consider "v = u" | "v = w"
      by blast
    thus "e \<in> (\<lambda>u. {u,v}) ` t_set (\<N>\<^sub>G G v)"
      using w_isin_Nu by cases (auto simp del: neighbourhood_abs)
  qed
qed

lemma uedges_anti_sym:
  assumes "uEdge u v \<in> uedges G"
  shows "uEdge v u \<notin> uedges G"
proof (rule ccontr, simp)
  assume "uEdge v u \<in> uedges G"
  moreover have "set_of_uedge (uEdge u v) = set_of_uedge (uEdge v u)"
    unfolding set_of_uedge_def by auto
  ultimately have "uEdge u v = uEdge v u"
    using assms inj_set_of_uedge[unfolded inj_on_def] by auto
  moreover have "uEdge u v \<noteq> uEdge v u"
    using assms uedge_not_refl_elim rep_of_edge by auto
  ultimately show False by blast
qed

lemma card_uedges:
  "card (set_of_uedge ` uedges G) = card (uedges G)"
  using inj_set_of_uedge by (intro card_image)

(*
lemma path_equiv: 
  assumes "ugraph_adj_map_invar G" "path_betw G u P v"
  shows "walk_betw (set_of_uedge ` uedges G) u P v"
  oops (* TODO *)
*)


end

end


end


end