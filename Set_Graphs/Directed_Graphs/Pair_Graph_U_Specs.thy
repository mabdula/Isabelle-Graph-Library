theory Pair_Graph_U_Specs
  imports Awalk "Map_Addons" "Set_Addons" Pair_Graph_Specs "HOL-Eisbach.Eisbach"
begin

(* Note: Some of the definitions in this file are currently not relevant to the rest of
the formalisation. *)

definition "set_of_pair = ( \<lambda>(u,v). {u,v})"

datatype 'v uedge = uEdge 'v 'v

definition "set_of_uedge e = ( case e of uEdge u v \<Rightarrow> {u,v})"

locale Pair_Graph_U_Specs = 
pair_graph_specs: Pair_Graph_Specs
  where lookup = lookup for lookup :: "'adjmap \<Rightarrow> ('v::linorder) \<Rightarrow> 'vset option"
begin

abbreviation "neighbourhood' G v == pair_graph_specs.neighbourhood G v"
notation "neighbourhood'" ("\<N>\<^sub>G _ _" 100)
abbreviation "add_edge == pair_graph_specs.add_edge"
abbreviation "delete_edge == pair_graph_specs.delete_edge"

lemmas [code] = neighbourhood_def 
pair_graph_specs.add_edge_def 
pair_graph_specs.delete_edge_def

definition "vertices G = {u | u v. v \<in>\<^sub>G (\<N>\<^sub>G G u)} \<union> {v | u v. v \<in>\<^sub>G (\<N>\<^sub>G G u)}" 

lemmas digraph_abs_def = pair_graph_specs.digraph_abs_def
abbreviation "digraph_abs \<equiv> pair_graph_specs.digraph_abs"

lemma vertices_equiv_dVs:
  "vertices G = dVs (digraph_abs G)"
  unfolding vertices_def digraph_abs_def dVs_def by auto

fun rep :: "'v uedge \<Rightarrow> 'v uedge" where
  "rep (uEdge u v) = (if u \<le> v then uEdge u v else uEdge v u)"

lemma is_rep:
  "rep (uEdge u v) = rep (uEdge v u)" 
  "rep (uEdge u v) = uEdge u v \<or> rep (uEdge u v) = uEdge v u"
  by auto


definition "uedges G = (\<lambda>(u,v). rep (uEdge u v)) ` (digraph_abs G)"  


definition ugraph_abs where "ugraph_abs G = {{u, v} | u v. v \<in>\<^sub>G (\<N>\<^sub>G G u)}" 

lemma ugraph_and_digraph_abs:"ugraph_abs G = {{u, v} | u  v. (u, v) \<in> digraph_abs G}"
 by(simp add: ugraph_abs_def digraph_abs_def)

context
  includes pair_graph_specs.adjmap.automation and pair_graph_specs.vset.set.automation
begin

lemma uedges_def2: "uedges G = {rep (uEdge u v) | u v. v \<in>\<^sub>G (\<N>\<^sub>G G u)}"
  unfolding uedges_def digraph_abs_def by force

lemma isin_uedges: "v \<in>\<^sub>G (\<N>\<^sub>G G u) \<Longrightarrow> rep (uEdge u v) = e \<Longrightarrow> e \<in> uedges G"
  unfolding uedges_def2 by force

thm pair_graph_specs.adjmap.invar_empty
thm pair_graph_specs.vset.set.invar_empty

lemmas neighbourhood_def=pair_graph_specs.neighbourhood_def

lemma uedges_empty: "uedges empty = {}"
  unfolding uedges_def digraph_abs_def neighbourhood_def 
  by (auto)

abbreviation "graph_inv == pair_graph_specs.graph_inv"
abbreviation "finite_graph == pair_graph_specs.finite_graph"
abbreviation "finite_vsets == pair_graph_specs.finite_vsets"
lemmas graph_inv_def= pair_graph_specs.graph_inv_def
lemmas finite_graph_def= pair_graph_specs.finite_graph_def
lemmas finite_vsets_def= pair_graph_specs.finite_vsets_def

lemma finite_uedges:
  "graph_inv G \<Longrightarrow> finite_graph G \<Longrightarrow> finite_vsets \<Longrightarrow> finite (uedges G)"
  unfolding uedges_def by auto

lemma set_of_uedge: "set_of_uedge (uEdge u v) = {u,v}"
  unfolding set_of_uedge_def by auto

(* Pair_Graph_Specs axioms + symmetric, irreflexive *)
definition "pair_graph_u_invar G = (
  graph_inv G \<and> finite_graph G \<and> finite_vsets \<and>
  (\<forall>v. \<not> v \<in>\<^sub>G (\<N>\<^sub>G G v)) \<and>
  (\<forall>u v. v \<in>\<^sub>G (\<N>\<^sub>G G u) \<longrightarrow> u \<in>\<^sub>G (\<N>\<^sub>G G v)))"

definition "none_symmetry H = (\<forall> e \<in> digraph_abs H. lookup H (fst e) \<noteq> None 
             \<longleftrightarrow>  lookup H (snd e) \<noteq> None) "


lemmas neighbourhood_invars' = pair_graph_specs.neighbourhood_invars'

lemma pair_graph_u_invar_no_loop: 
   "pair_graph_u_invar G \<Longrightarrow> x \<in> dom (lookup G) \<Longrightarrow> y \<in> t_set (the (lookup G x)) \<Longrightarrow> x \<noteq> y"
  using  neighbourhood_invars'[of G]   
 by (subst (asm) pair_graph_specs.vset.set.set_isin[of "the (lookup G x)" y, symmetric])
    (auto simp add: pair_graph_u_invar_def local.neighbourhood_def   option.split, metis option.simps(5))

context
  fixes G::'adjmap
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

lemma invar_finite_vsets[simp, intro!]:
  "finite_vsets"
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



lemma adjmap_vertices_neq:
  assumes "v \<in>\<^sub>G (\<N>\<^sub>G G u)"
  shows "u \<noteq> v"
  using assms by force

lemma vertices_def2: 
  "vertices G = {u | u v. v \<in>\<^sub>G (\<N>\<^sub>G G u)}"
  unfolding vertices_def using graph_symmetric by auto

lemma isin_vsetorhood_set_edge: 
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
    using assms by (force intro: adjmap_vertices_neq)
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
    using assms by (force intro: adjmap_vertices_neq)
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

lemma set_edge_isin_vsetorhood: 
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

lemma set_edge_isin_vsetorhood_elim: 
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

lemma set_edge_isin_vsetorhood_iff:
  "e \<in> set_of_uedge ` uedges G \<longleftrightarrow> (\<exists>u v. e = {u,v} \<and> v \<in>\<^sub>G (\<N>\<^sub>G G u))"
  using isin_vsetorhood_set_edge set_edge_isin_vsetorhood_elim by metis

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

lemmas neighbourhood_abs=pair_graph_specs.neighbourhood_abs

lemma
  "v \<in>\<^sub>G (\<N>\<^sub>G G u) \<Longrightarrow> u \<in>\<^sub>G (\<N>\<^sub>G G v)"
  by (auto simp del: neighbourhood_abs)
  
lemma vsetorhood_eq_set_for_edge:
  "(\<lambda>u. {u,v}) ` t_set (\<N>\<^sub>G G v) = {e \<in> set_of_uedge ` uedges G. v \<in> e}"
proof
  show "(\<lambda>u. {u,v}) ` t_set (\<N>\<^sub>G G v) \<subseteq> {e \<in> set_of_uedge ` uedges G. v \<in> e}"
    by (auto intro!: isin_vsetorhood_set_edge)
next
  show "{e \<in> set_of_uedge ` uedges G. v \<in> e} \<subseteq> (\<lambda>u. {u,v}) ` t_set (\<N>\<^sub>G G v)"
  proof
    fix e
    assume "e \<in> {e \<in> set_of_uedge ` uedges G. v \<in> e}"
    hence "e \<in> set_of_uedge ` uedges G" and "v \<in> e"
      by auto
    moreover then obtain u w where [simp]: "e = {u,w}" and w_isin_Nu: "w \<in>\<^sub>G (\<N>\<^sub>G G u)"
      by (elim set_edge_isin_vsetorhood_elim) auto
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

lemmas finite_graphI=pair_graph_specs.finite_graphI

lemma pair_graph_u_invar_empty: "pair_graph_u_invar \<emptyset>\<^sub>G"
  by (simp add: finite_graphI graph_inv_def local.neighbourhood_def pair_graph_u_invar_def)

lemmas digraph_abs_insert= pair_graph_specs.digraph_abs_insert
lemmas add_edge_def = pair_graph_specs.add_edge_def
lemmas graph_invE = pair_graph_specs.graph_invE
lemmas adjmap_inv_insert =  pair_graph_specs.adjmap_inv_insert
lemmas finite_graph_add_edge = pair_graph_specs.finite_graph_add_edge
lemmas are_connected_abs = pair_graph_specs.are_connected_abs

lemma pair_graph_u_invar_add_edge_both:
  assumes "u \<noteq> v"
  shows "pair_graph_u_invar (add_edge (add_edge G u v) v u)" (is ?thesis1)
  and "\<forall> x y. lookup G x = Some y \<longrightarrow> y \<noteq> vset_empty
 \<Longrightarrow>\<forall> x y. lookup (add_edge (add_edge G u v) v u) x = Some y \<longrightarrow> y \<noteq> vset_empty" 
(is "?assm \<Longrightarrow> ?thesis2")
and "none_symmetry G \<Longrightarrow> none_symmetry (add_edge (add_edge G u v) v u)" (is "?assm3 \<Longrightarrow> ?thesis3")
proof-
  have set_is:"[add_edge G u v]\<^sub>g = Set.insert (u, v) [G]\<^sub>g"
    using  digraph_abs_insert[of G u v] assms by(auto simp add: pair_graph_u_invar_def)
  have finiteG: "finite_graph G" 
    by simp
  have adjmap_invG: "adjmap_inv G"
    using invar_graph_inv by blast
  have adjmap_invg': "adjmap_inv (add_edge G u v)"
    using graph_inv_def by blast
  have set_is':"{v. v \<noteq> u \<longrightarrow> (\<exists>y. lookup G v = Some y)} = Set.insert u {v.  (\<exists>y. lookup G v = Some y)}" by blast
  have finite_graph_after:"finite_graph (add_edge G u v)"
    using finiteG
    by (auto split: option.split simp add: finite_graph_def add_edge_def pair_graph_specs.adjmap.map_update[OF adjmap_invG] set_is') 
  have not_Refl:"\<not> va \<in>\<^sub>G \<N>\<^sub>G G va" for va by simp
  have not_Refl':"\<not> va \<in>\<^sub>G \<N>\<^sub>G add_edge G u v va" for va
    using assms not_Refl[of va]  
    by(auto split: option.split simp add: add_edge_def neighbourhood_def pair_graph_specs.adjmap.map_update[OF adjmap_invG] intro: graph_invE[of G] )
 have not_Refl_after:"\<not> va \<in>\<^sub>G \<N>\<^sub>G add_edge (add_edge G u v) v u va" for va
    using assms not_Refl'[of va]  
    by(auto split: option.split simp add: add_edge_def  pair_graph_specs.adjmap.map_update[OF adjmap_invg', simplified add_edge_def] 
                   neighbourhood_def pair_graph_specs.adjmap.map_update[OF adjmap_invg'] intro: graph_invE[of G] )
  have sym_before:"va \<in>\<^sub>G \<N>\<^sub>G G ua \<Longrightarrow> ua \<in>\<^sub>G \<N>\<^sub>G G va" for va ua by blast
  have sym_after: "va \<in>\<^sub>G \<N>\<^sub>G add_edge (add_edge G u v) v u ua \<Longrightarrow> ua \<in>\<^sub>G \<N>\<^sub>G add_edge (add_edge G u v) v u va " for ua va
  proof(goal_cases)
    case 1
    have"(ua, va) \<in> digraph_abs (add_edge (add_edge G u v) v u)"
      using 1 adjmap_inv_insert neighbourhoodI by (subst digraph_abs_insert) fastforce+
    hence "(ua, va) = (v, u) \<or> (ua, va) = (u, v) \<or> (ua, va) \<in> digraph_abs G"
      by(auto simp add: pair_graph_specs.adjmap_inv_insert) 
    hence "(ua, va) = (v, u) \<or> (ua, va) = (u, v) \<or> (va, ua) \<in> digraph_abs G" 
      by auto 
    hence"(va, ua) \<in> digraph_abs (add_edge (add_edge G u v) v u)"
      by(auto simp add: adjmap_inv_insert)  
    then show ?case 
      by (simp add: digraph_abs_def)
  qed
  show thesis1:?thesis1
    using assms 
    by(auto intro: adjmap_inv_insert finite_graph_add_edge simp add: pair_graph_u_invar_def not_Refl_after sym_after)
  show "?assm \<Longrightarrow> ?thesis2" 
  proof(rule, rule, goal_cases)
    case (1 x y)
    moreover have "lookup G v = Some vset \<Longrightarrow> vset_inv vset" for vset
      using graph_invE[OF invar_graph_inv] by auto
    moreover have "lookup G u = Some x2 \<Longrightarrow>
          lookup G v = None \<Longrightarrow> y = insert v x2 \<Longrightarrow> \<emptyset>\<^sub>N = insert v x2 \<Longrightarrow> False" for x2
      using graph_invE by fastforce
    moreover have "lookup G u = Some x2 \<Longrightarrow>
       lookup G v = Some x2a \<Longrightarrow> y = insert v x2 \<Longrightarrow> \<emptyset>\<^sub>N = insert v x2 \<Longrightarrow> False " for x2 x2a
      using graph_invE by fastforce
    ultimately show ?case 
      using  assms 
      by(auto split: option.split simp add: add_edge_def Let_def adjmap_invG  pair_graph_specs.adjmap.map_update)+
  qed
  show "?assm3 \<Longrightarrow> ?thesis3"
    unfolding none_symmetry_def
  proof(rule, goal_cases)
    case (1 e)
    have graph_abs_after:"[add_edge (add_edge G u v) v u]\<^sub>g = Set.insert (v, u) (Set.insert (u, v) [G]\<^sub>g)" 
                          "[(add_edge G u v)]\<^sub>g = (Set.insert (u, v) [G]\<^sub>g)" 
      by (simp add: adjmap_inv_insert)+
    have lookup_is1:"lookup (update v (insert u \<emptyset>\<^sub>N) (update u (insert v \<emptyset>\<^sub>N) G)) =
 ((lookup G)(u \<mapsto> insert v \<emptyset>\<^sub>N, v \<mapsto> insert u \<emptyset>\<^sub>N))" for u v
      by (simp add: adjmap_invG)
    obtain neighbs where neighbs_exists:"lookup (add_edge (add_edge G u v) v u) (fst e) = Some neighbs"
      using "1"(2) thesis1 are_connected_abs[of "(add_edge (add_edge G u v) v u)" "snd e" "fst e"] 
             pair_graph_specs.vset.set.set_empty
     by(fastforce simp add: local.neighbourhood_def  pair_graph_u_invar_def)
    have help1:"fst e \<noteq> v \<Longrightarrow> snd e \<noteq> v \<Longrightarrow> \<exists>y. lookup G (snd e) = Some y" 
      using "1"(1) "1"(2) adjmap_inv_insert[OF  invar_graph_inv]
       are_connected_abs[OF  invar_graph_inv, of "snd e" "fst e"] 
         invar_graph_inv  pair_graph_specs.vset.emptyD(3)
      by(auto simp add:  neighbourhood_def graph_abs_after)
    have help3: "
    snd e \<noteq> u \<Longrightarrow> v = fst e  \<Longrightarrow> lookup G (fst e) = None \<Longrightarrow> \<exists>y. lookup G (snd e) = Some y"   
      using "1"(2) adjmap_inv_insert[OF invar_graph_inv] are_connected_abs[OF invar_graph_inv, of "snd e" "fst e"]
                invar_graph_inv  pair_graph_specs.vset.emptyD(1)
      by(auto intro: prod.exhaust[of e] simp add: neighbourhood_def  graph_abs_after )
    have help4: " snd e \<noteq> u \<Longrightarrow>
          v = fst e \<Longrightarrow>  lookup G (fst e) = Some x2 \<Longrightarrow> \<exists>y. lookup G (snd e) = Some y" for x2 
      using "1"(2,1) adjmap_inv_insert[OF invar_graph_inv] are_connected_abs[OF invar_graph_inv, of "snd e" "fst e"]
                invar_graph_inv  pair_graph_specs.vset.emptyD(1)
      by(auto intro: prod.exhaust[of e] simp add: neighbourhood_def  graph_abs_after )
   show ?case
      using 1 assms neighbs_exists
      by(auto intro: help1 help3 help4 split: option.split if_split simp add: add_edge_def lookup_is1 adjmap_invG )
  qed
qed

lemmas pair_graph_u_invar_add_edge = pair_graph_u_invar_add_edge_both(1)
end
end
end
end