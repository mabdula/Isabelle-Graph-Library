(*Authors: Mohammad Abdulaziz, Thomas Ammer, Christoph Madlener, Adem Rimpapa,*)
theory Connected_Components
  imports Undirected_Set_Graphs Paths
begin
section \<open>Connected Components and Connectivity\<close>

subsection \<open>Basics of Connected Components\<close>

definition connected_component where
  "connected_component G v = {v'. v' = v \<or> reachable G v v'}"

text \<open>This is an easier to reason about characterisation, especially with automation\<close>

lemma connected_component_rechability:
  "connected_component G v = {v'. v' = v \<or> (reachable G v v')}"
  by (auto simp add: reachable_def connected_component_def)

lemma in_connected_componentE:
  "\<lbrakk>v \<in> connected_component G w; \<lbrakk>reachable G w v; w \<in> Vs G\<rbrakk> \<Longrightarrow> P; w = v \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: connected_component_def reachable_refl elim: reachableE dest: walk_endpoints(1))

lemma in_connected_componentI:
  "reachable G w v \<Longrightarrow> v \<in> connected_component G w"
  by (auto simp: connected_component_rechability)

lemma in_connected_componentI2:
  "w = v \<Longrightarrow> v \<in> connected_component G w"
  by (auto simp: connected_component_rechability)

definition "comps X E = connected_component E ` X"

text \<open>The abbreviation is there to allow for the definition as a lemma.\<close>

definition "connected_components_aux G = comps (Vs G) G"
abbreviation "connected_components G \<equiv> connected_components_aux G"

lemma connected_components_notE_singletons:
  "x \<notin> Vs G \<Longrightarrow> connected_component G x = {x}"
  by (fastforce simp add: connected_component_def reachable_def)

lemma connected_components_def: 
 "connected_components G = {vs. \<exists>v. vs = connected_component G v \<and> v \<in> (Vs G)}"
  by(auto simp add: connected_components_aux_def comps_def)

text \<open>The abbreviation is there to allow for the definition as a lemma.\<close>
definition "connected_components'_aux V X = comps (V \<union> (Vs X)) X"

abbreviation "connected_components' V X \<equiv> connected_components'_aux V X"

lemma connected_components'_def:
  "connected_components' V X = connected_components X \<union> ((\<lambda>v. {v}) ` (V - (Vs X)))"
  using connected_components_notE_singletons image_iff 
  by (fastforce simp add: connected_components'_aux_def connected_components_def comps_def)

lemma connected_components_member_sym:
  "v \<in> connected_component G w \<Longrightarrow> w \<in> connected_component G v"
  by (auto elim!: in_connected_componentE intro: in_connected_componentI in_connected_componentI2
           simp: reachable_sym)

lemma in_own_connected_component: "v \<in> connected_component G v"
  unfolding connected_component_def by simp

lemma in_connected_component_has_walk:
  assumes "v \<in> connected_component G w" "w \<in> Vs G"
  obtains p where "walk_betw G w p v"
proof(cases "v = w")
  case True thus ?thesis
   using that assms(2)
   by (auto dest: walk_reflexive )
next
  case False
  hence "reachable G w v"
    using assms(1) unfolding connected_component_def by blast
  thus ?thesis
    by (auto dest: reachableD that)
qed

(* TODO: Call in_connected_componentI *)

lemma has_path_in_connected_component:
  "walk_betw G u p v \<Longrightarrow> v \<in> connected_component G u"
  by(auto simp: connected_component_def reachable_def)

(* TODO: Call in_connected_componentI2 *)

lemma has_path_in_connected_component2:
  "(\<exists>p. walk_betw G u p v) \<Longrightarrow> v \<in> connected_component G u"
  unfolding connected_component_def reachable_def
  by blast

lemma in_con_comp_has_walk: 
  assumes "v \<in> connected_component G u" "v \<noteq> u"
  obtains p where "walk_betw G u p v"
  using assms
  by(auto simp: connected_component_def elim!: reachableE)

lemma connected_components_member_trans:
  "\<lbrakk>x \<in> connected_component G y; y \<in> connected_component G z\<rbrakk> \<Longrightarrow> x \<in> connected_component G z"
  by (auto elim!: in_connected_componentE dest: reachable_trans intro: in_connected_componentI
           simp: reachable_refl)

method in_tc uses tc_thm = 
  (match conclusion in "R x z" for R and x::'a and z::'a \<Rightarrow>
     \<open>match premises in a: "R x y" for  y \<Rightarrow>
       \<open>match premises in b: "R y z" \<Rightarrow>
          \<open>(insert tc_thm[OF a b])\<close>\<close>\<close>)

method in_tc_2 uses tc_thm refl_thm = 
  (match conclusion in "R x z" for R and x::'a and z::'a \<Rightarrow>
     \<open>match premises in a: "R x y" for  y \<Rightarrow>
       \<open>match premises in b: "R z y" \<Rightarrow>
          \<open>(insert tc_thm[OF a refl_thm[OF b]])\<close>\<close>\<close>)

method in_tc_3 uses tc_thm refl_thm = 
  (match conclusion in "R x z" for R and x::'a and z::'a \<Rightarrow>
     \<open>match premises in b: "R y z" for  y \<Rightarrow>
       \<open>match premises in a: "R y x" \<Rightarrow>
          \<open>(insert tc_thm[OF refl_thm[OF a] b])\<close>\<close>\<close>)

method in_tc_4 uses tc_thm refl_thm = 
  (match conclusion in "R x z" for R and x::'a and z::'a \<Rightarrow>
     \<open>match premises in a: "R y x" for  y \<Rightarrow>
       \<open>match premises in b: "R z y" \<Rightarrow>
          \<open>(insert tc_thm[OF refl_thm[OF a] refl_thm[OF b]])\<close>\<close>\<close>)

method in_rtc uses tc_thm refl_thm =
  (safe?; (in_tc tc_thm: tc_thm | in_tc_2 tc_thm: tc_thm refl_thm: refl_thm |
    in_tc_3 tc_thm: tc_thm refl_thm: refl_thm | in_tc_4 tc_thm: tc_thm refl_thm: refl_thm),
    assumption?)+

lemma connected_components_member_eq:
  "v \<in> connected_component G w \<Longrightarrow> connected_component G v = connected_component G w"
  by(in_rtc tc_thm: connected_components_member_trans refl_thm: connected_components_member_sym)

lemma connected_components_closed:
  "\<lbrakk>v1 \<in> connected_component G v4; v3 \<in> connected_component G v4\<rbrakk> 
  \<Longrightarrow> v3 \<in> connected_component G v1"
  by(in_rtc tc_thm: connected_components_member_trans refl_thm: connected_components_member_sym)

lemma C_is_componentE:
  assumes "C \<in> connected_components G"
  obtains v where "C = connected_component G v" "v \<in> Vs G"
  using assms
  by (fastforce simp add: connected_components_def)

lemma connected_components_closed':
  "\<lbrakk>v \<in> C; C \<in> connected_components G\<rbrakk> \<Longrightarrow> C = connected_component G v"
  by (fastforce elim: C_is_componentE simp: connected_components_member_eq)

lemma connected_components_closed'':
  "\<lbrakk>C \<in> connected_components G; v \<in> C\<rbrakk> \<Longrightarrow> C = connected_component G v"
  by (simp add: connected_components_closed')

lemma connected_components_eq:
  "\<lbrakk>v \<in> C ; v \<in> C'; C \<in> connected_components G; C' \<in> connected_components G\<rbrakk> \<Longrightarrow> C = C'"
  using connected_components_closed'[where G = G]
  by auto

lemma connected_components_eq':
  "\<lbrakk>C \<in> connected_components G; C' \<in> connected_components G; v \<in> C ; v \<in> C'\<rbrakk> \<Longrightarrow> C = C'"
  using connected_components_eq .

lemma connected_components_disj:
  "\<lbrakk>C \<noteq> C'; C \<in> connected_components G; C' \<in> connected_components G\<rbrakk> \<Longrightarrow> C \<inter> C' = {}"
  using connected_components_eq[where G = G]
  by auto

lemma own_connected_component_unique:
  assumes "x \<in> Vs G"
  shows "\<exists>!C \<in> connected_components G. x \<in> C"
proof(standard, intro conjI)
  show "connected_component G x \<in> connected_components G"
    using assms connected_components_def
    by blast
  show "x \<in> connected_component G x"
    using in_own_connected_component
    by fastforce
  fix C assume "C \<in> connected_components G \<and> x \<in> C"
  thus "C = connected_component G x"
    by (simp add: connected_components_closed')
qed

lemma connected_component_subs_Vs:
  "C \<in> connected_components G \<Longrightarrow> C \<subseteq> Vs G"
  by (auto simp: dest: reachable_in_Vs(2) elim: in_connected_componentE C_is_componentE)

lemma connected_comp_nempty:
  "C \<in> connected_components G \<Longrightarrow> C \<noteq> {}"
  using in_own_connected_component
  by (fastforce simp: connected_components_def)

lemma connected_comp_verts_in_verts:
  "\<lbrakk>v \<in> C; C \<in> connected_components G\<rbrakk> \<Longrightarrow> v \<in> Vs G"
  using connected_component_subs_Vs
  by blast

lemma connected_component_set:
  "\<lbrakk>u \<in> Vs G; \<And>x. x \<in> C \<Longrightarrow> reachable G u x; \<And>x. reachable G u x \<Longrightarrow> x \<in> C\<rbrakk> 
   \<Longrightarrow> connected_component G u = C"
  by (auto elim: in_connected_componentE intro: in_connected_componentI dest: reachable_refl)

lemma connected_comp_has_vert:
  assumes "C \<in> connected_components G"
  obtains w where "w \<in> Vs G" "C = connected_component G w"
  using C_is_componentE[OF assms]
  .

lemma path_subset_conn_comp:
  assumes "path G p"
  shows "set p \<subseteq> connected_component G (hd p)"
  using assms
proof(induction)
  case path0
  then show ?case by simp
next
  case path1
  then show ?case using in_own_connected_component by simp
next
  case (path2 v v' vs)
  hence "walk_betw G v' [v',v] v"
    by (simp add: edges_are_walks insert_commute)
  hence "v \<in> connected_component G v'"
    by (auto dest:has_path_in_connected_component) 
  moreover hence "connected_component G v = connected_component G v'"
    by (simp add: connected_components_member_eq)
  ultimately show ?case using path2.IH by fastforce
qed

lemma walk_betw_subset_conn_comp:
  "walk_betw G u p v \<Longrightarrow> set p \<subseteq> connected_component G u"
  using path_subset_conn_comp
  by (auto simp: walk_betw_def)

lemma path_in_connected_component:
  "\<lbrakk>path G p; hd p \<in> connected_component G x\<rbrakk> \<Longrightarrow> set p \<subseteq> connected_component G x"
  by (fastforce dest: path_subset_conn_comp simp: connected_components_member_eq)

lemma component_has_path:
  assumes "finite C'" "C' \<subseteq> C" "C \<in> connected_components G"
  shows "\<exists>p. path G p \<and> C' \<subseteq> (set p) \<and> (set p) \<subseteq> C"
  using assms
proof(induction C')
  case empty thus ?case
    using path0 by fastforce
next
  case ass: (insert x F)
  then obtain p where p: "path G p" "F \<subseteq> set p" "set p \<subseteq> C"
    by auto
  have "x \<in> C" using ass.prems(1) by blast
  hence C_def: "C = connected_component G x"
    by (simp add: assms(3) connected_components_closed')

  show ?case
  proof(cases "p = []")
    case True
    have "path G [x]" using ass connected_comp_verts_in_verts by force
    then show ?thesis using True p ass.prems(1) by fastforce
  next
    case F1: False
    then obtain h t where "p = h # t" using list.exhaust_sel by blast
    hence walkhp: "walk_betw G h p (last p)" using p(1) walk_betw_def by fastforce

    have "h \<in> C" using \<open>p = h # t\<close> p(3) by fastforce
    moreover have "x \<in> Vs G"
      using \<open>x \<in> C\<close> assms(3) connected_component_subs_Vs
      by auto
    ultimately obtain q where walkxh: "walk_betw G x q h"
      by (auto simp: C_def elim: in_connected_component_has_walk)
    hence walkxp: "walk_betw G x (q @ tl p) (last p)"
      by (simp add: walk_transitive walkhp)
    moreover hence "set (q @ tl p) \<subseteq> C"
      by(auto simp: C_def dest!: walk_betw_subset_conn_comp)
    moreover from walkxp have "path G (q @ tl p)"
      by (fastforce dest: walk_between_nonempty_pathD)
    moreover {
      from walkxh have "last q = h" "hd q = x" by (fastforce dest: walk_between_nonempty_pathD)+
      then have "insert x F \<subseteq> set (q @ tl p)" using \<open>p = h # t\<close> walkxh p(2) by fastforce
    }
    ultimately show ?thesis by blast
  qed
qed

lemma component_has_path':
  "\<lbrakk>finite C; C \<in> connected_components G\<rbrakk> \<Longrightarrow> \<exists>p. path G p \<and> C = (set p)"
  using component_has_path
  by fastforce

lemma in_connected_componentI3:
  "\<lbrakk>C \<in> connected_components G; w \<in> C; x \<in> C\<rbrakk> \<Longrightarrow> x \<in> connected_component G w"
  using connected_components_closed'
  by fastforce

lemma same_con_comp_reachable:
  "\<lbrakk>C \<in> connected_components G; w \<in> C; x \<in> C\<rbrakk> \<Longrightarrow> reachable G w x"
  using in_connected_componentI3
  by(fastforce intro: reachable_refl connected_comp_verts_in_verts elim: in_connected_componentE)

lemma same_con_comp_walk:
  assumes "C \<in> connected_components G" "w \<in> C" "x \<in> C"
  obtains pwx where "walk_betw G w pwx x"
proof-
  have "x \<in> connected_component G w" 
    using assms
    by (rule in_connected_componentI3)
  thus ?thesis
    using connected_comp_verts_in_verts[OF \<open>w \<in> C\<close> \<open>C \<in> connected_components G\<close>]
    by (auto elim: that in_connected_component_has_walk)
qed                             

lemma in_connected_componentI4:
  assumes "walk_betw G u puv v" "u \<in> C" "C \<in> connected_components G"
  shows "v \<in> C"
  using assms connected_components_closed'
  by (fastforce intro: has_path_in_connected_component)

lemma connected_component_in_components:
  "v \<in> Vs G \<Longrightarrow> connected_component G v \<in> connected_components G"
  by (fastforce simp: connected_components_def)

lemma in_connected_component_in_edges: "v \<in> connected_component G u \<Longrightarrow> v \<in> Vs G \<or> u = v"
  by(auto simp: connected_component_def Vs_def 
          dest: walk_endpoints(2)
         elim!: reachableE vs_member_elim)

lemma graph_component_partition:
  shows "\<Union> (connected_components G) = Vs G" 
  unfolding connected_components_def
proof(safe)
  fix y
  assume "y \<in> Vs G"
  then show "y \<in> \<Union> {connected_component G v |v. v \<in> Vs G}" 
    using  in_own_connected_component by fastforce
qed (metis in_connected_component_in_edges)

lemma con_comp_subset: "G1 \<subseteq> G2 \<Longrightarrow> connected_component G1 u \<subseteq> connected_component G2 u"
  by (auto dest: reachable_subset simp: connected_component_def)

lemma connected_components_empty: "connected_components {} = {}"
  by (auto simp: connected_components_def Vs_def)

lemma connected_components'_disj:
  "\<lbrakk>C \<noteq> C'; C \<in> connected_components' V X; C' \<in> connected_components' V X\<rbrakk> \<Longrightarrow> C \<inter> C' = {}"
proof-
  assume "C \<noteq> C'" "C \<in> connected_components' V X" "C' \<in> connected_components' V X"
  
  then consider (1) "C \<in> connected_components X \<and> C' \<in> connected_components X" |
                (2) "C \<in> {{v} | v. v \<in> V - (Vs X)} \<and> C' \<in> connected_components X" |
                (3) "C \<in> connected_components X \<and> C' \<in> {{v} | v. v \<in> V - (Vs X)}" |
                (4) "C \<in> {{v} | v. v \<in> V - (Vs X)} \<and> C' \<in> {{v} | v. v \<in> V - (Vs X)}"
    unfolding connected_components'_def by auto
  then show "C \<inter> C' = {}"
  proof (cases)
    case 1
    with connected_components_disj[OF \<open>C \<noteq> C'\<close>] show ?thesis by auto
  next
    case 2
    then have "C \<subseteq> V - Vs X" by blast
    moreover have "C' \<subseteq> Vs X" using 2
      by (simp add: connected_component_subs_Vs)
    ultimately show ?thesis by auto
  next
    case 3
    then have "C' \<subseteq> V - Vs X" by blast
    moreover have "C \<subseteq> Vs X" using 3
      by (simp add: connected_component_subs_Vs)
    ultimately show ?thesis by auto
  next
    case 4
    with \<open>C \<noteq> C'\<close> show ?thesis by blast
  qed
qed

lemma Union_connected_components:
  "dblton_graph G \<Longrightarrow> Union (connected_components G) = (Vs G)"
  by(intro graph_component_partition)

lemma union_connected_components':
  "\<lbrakk>dblton_graph X; Vs X \<subseteq> V\<rbrakk> \<Longrightarrow> \<Union> (connected_components' V X) = V"
  unfolding connected_components'_def
proof-
  assume "dblton_graph X" "Vs X \<subseteq> V"
  have "\<Union> (connected_components X \<union> ((\<lambda>v. {v}) ` (V - (Vs X)))) = 
    \<Union> (connected_components X) \<union> \<Union> ((\<lambda>v. {v}) ` (V - (Vs X)))" by simp  
  also have "... = Vs X \<union> \<Union> ((\<lambda>v. {v}) ` (V - (Vs X)))"
    using Union_connected_components[OF \<open>dblton_graph X\<close>] by metis
  also have "... = Vs X \<union> (V - Vs X)"
    by auto
  also have "... = V"
    using \<open>Vs X \<subseteq> V\<close> by auto
  finally show "\<Union> (connected_components X \<union> ((\<lambda>v. {v}) ` (V - (Vs X)))) = V" .
qed

lemma connected_component'_nonempty:
  "C' \<in> connected_components' V X \<Longrightarrow> C' \<noteq> {}"
  unfolding connected_components'_def using connected_comp_nempty by blast

lemma connected_component_empty_edges_is_self:
  "connected_component {} v = {v}"
  using not_reachable_empt[of v]
  by(auto simp add: connected_component_def)

lemma connected_component_non_empt: "connected_component A x \<noteq> {}"
  by(auto simp add: connected_component_def)

lemma unequal_components_disjoint: 
  "\<lbrakk>connected_component E u \<noteq> connected_component E v; u \<in> X; v \<in> X\<rbrakk> 
  \<Longrightarrow> connected_component E u \<inter> connected_component E v = {}"
  by (metis Int_emptyI connected_components_member_eq)

lemma same_component_set_mono: 
  "\<lbrakk>A \<subseteq> B; connected_component A x = connected_component A y\<rbrakk>
    \<Longrightarrow> connected_component B x = connected_component B y"
  using in_own_connected_component[of x A]
  by (cases "x=y") (auto intro!: connected_components_member_eq in_connected_componentI reachable_subset[of A _ _ B] in_connected_componentE[of x A y])

lemma same_connected_component_SOME:
 "x \<in> X \<Longrightarrow> connected_component A (SOME xa. xa \<in> connected_component A x \<and> xa \<in> X)
            = connected_component A x" 
  using in_own_connected_component some_eq_ex[of "\<lambda> xa. xa \<in> connected_component A x \<and> xa \<in> X"]
  by (force intro!: connected_components_member_eq)

subsection \<open>Edges and Connected Components\<close>

lemma edge_in_component:
  assumes "{x,y} \<in> G"
  shows "\<exists>C. C \<in> connected_components G \<and> {x,y} \<subseteq> C"
proof-
  have "y \<in> connected_component G x"
  proof(rule has_path_in_connected_component)
    show "walk_betw G x [x, y] y" 
      apply(rule nonempty_path_walk_between)
      using assms
      by auto
  qed
  moreover have "x \<in> Vs G" using assms
    by (auto dest: edges_are_Vs)
  ultimately show ?thesis
    unfolding connected_components_def
    using in_own_connected_component
    by fastforce
qed

lemma edge_in_unique_component:
  "{x,y} \<in> G \<Longrightarrow> \<exists>!C. C \<in> connected_components G \<and> {x,y} \<subseteq> C"
  by(force dest: connected_components_closed' edge_in_component )

text\<open>
  Now we should be able to partition the set of edges into equivalence classes
  corresponding to the connected components.\<close>

definition component_edges where
"component_edges G C = {{x, y} | x y.  {x, y} \<subseteq> C \<and> {x, y} \<in> G}"

lemma component_edges_disj_edges:
  assumes "C \<in> connected_components G" "C' \<in> connected_components G" "C \<noteq> C'"
  assumes "v \<in> component_edges G C" "w \<in> component_edges G C'"
  shows "v \<inter> w = {}"
proof(intro equals0I)
  fix x assume "x \<in> v \<inter> w"
  hence "x \<in> C" "x \<in> C'" using assms(4, 5) unfolding component_edges_def by blast+
  thus False
    using assms(1-3)
    by(auto dest: connected_components_closed')
qed

lemma component_edges_disj:
  assumes "C \<in> connected_components G" "C' \<in> connected_components G" "C \<noteq> C'"
  shows "component_edges G C \<inter> component_edges G C' = {}"
proof(intro equals0I, goal_cases)
  case (1 y)
  hence "y = {}"
    apply(subst Int_absorb[symmetric])
    apply(intro component_edges_disj_edges)
    using assms  
    by auto

  thus False using 1 unfolding component_edges_def by blast
qed

lemma component_edges_subset:
  shows "component_edges G C \<subseteq> G"
  by (auto simp: component_edges_def)

lemma edges_path_subset_edges:
  assumes "path G p" "set p \<subseteq> C"
  shows "set (edges_of_path p) \<subseteq> component_edges G C"
  using assms
  by (induction) (auto simp add: component_edges_def)

definition components_edges where
"components_edges G = {component_edges G C| C. C \<in> connected_components G}"

(* TODO replace  everywhere with C_componentE*)

lemma component_edges_partition:
  shows "\<Union> (components_edges G) = G \<inter> {{x,y}| x y. True}"
  unfolding components_edges_def
proof(safe)
  fix x y
  assume "{x, y} \<in> G"
  then obtain C where "{x, y} \<subseteq> C" "C \<in> connected_components G"
    by (auto elim!: exE[OF edge_in_component])
  moreover then have "{x, y} \<in> component_edges G C"
    using \<open>{x, y} \<in> G\<close> component_edges_def
    by fastforce
  ultimately show "{x, y} \<in> \<Union> {component_edges G C |C. C \<in> connected_components G}"
    by blast
qed (auto simp add: component_edges_def)

lemma edge_in_component_edges:
  assumes "graph_invar G"
  assumes "e \<in> G"
  assumes "e \<subseteq> C" 
  shows "e \<in> component_edges G C"
  using assms component_edges_def by fastforce 

lemma graph_component_edges_partition:
  assumes "graph_invar G"
  shows "\<Union> (components_edges G) = G"
  unfolding components_edges_def
proof(safe)
  fix e
  assume "e \<in> G" 
  then obtain C where "e \<subseteq> C" "C \<in> connected_components G"
    by (metis assms dblton_graphE edge_in_component)
  moreover then have "e \<in> component_edges G C" 
    by (simp add: \<open>e \<in> G\<close> assms edge_in_component_edges)
  ultimately show "e \<in> \<Union>{component_edges G C |C.  C \<in> connected_components G}" 
    by blast
qed (auto simp add: component_edges_def)

lemma Vs_component_edges:
  "\<lbrakk>dblton_graph G; C \<in> connected_components G\<rbrakk> \<Longrightarrow> Vs (component_edges G C) = C"
  unfolding component_edges_def Vs_def connected_components_def
proof (standard, goal_cases)
  case 1
  then show ?case by auto
next
  case 2
  then have "\<exists>v. v \<in> \<Union> G \<and> C = connected_component G v" by blast
  then obtain v where "v \<in> \<Union> G" "C = connected_component G v" by blast
  with in_connected_component_in_edges
    have "\<forall>x \<in> C. x \<in> \<Union> G" using Vs_def by fastforce

  have "\<forall>x \<in> C. \<exists>y \<in> C. {x, y} \<in> G"
  proof
    fix x
    assume "x \<in> C"
    with in_connected_component_in_edges \<open>v \<in> \<Union> G\<close> \<open>C = connected_component G v\<close>
      have "x \<in> \<Union> G" using Vs_def by fastforce
    then have "\<exists>e. e \<in> G \<and> x \<in> e" by blast
    with dblton_graphE[OF \<open>dblton_graph G\<close>] have "\<exists>y. x \<noteq> y \<and> {x, y} \<in> G"
      using insert_absorb
      by (smt (verit, ccfv_SIG) empty_iff insert_commute insert_iff)
    then obtain y where "x \<noteq> y" "{x, y} \<in> G" by blast
    then have "walk_betw G x [x, y] y" 
      unfolding walk_betw_def by auto
    from has_path_in_connected_component[OF this] connected_components_member_eq
      \<open>x \<in> C\<close> \<open>C = connected_component G v\<close>
      have "y \<in> connected_component G v" by fast
    with \<open>{x, y} \<in> G\<close> \<open>C = connected_component G v\<close>
    show "\<exists>y \<in> C. {x, y} \<in> G" by blast
  qed

  then have "\<forall>x \<in> C. \<exists>y. {x, y} \<subseteq> C \<and> {x, y} \<in> G \<and> x \<in> {x, y}"
     by auto 
  then show ?case
    using Complete_Lattices.Union_iff[where ?C = "{{x, y} |x y. {x, y} \<subseteq> C \<and> {x, y} \<in> G}"]
    by (smt (verit) mem_Collect_eq subsetI)
qed 

lemma components_edges_image_Vs:
  "dblton_graph G \<Longrightarrow> Vs ` (components_edges G) = connected_components G"
  unfolding components_edges_def Vs_def
proof-
  assume "dblton_graph G"
  have "\<Union> ` {component_edges G C |C. C \<in> connected_components G} = 
    {\<Union> (component_edges G C) |C. C \<in> connected_components G}" by blast
  also have "... = 
    {C |C. C \<in> connected_components G}"
    using Vs_component_edges[OF \<open>dblton_graph G\<close>] by (metis Vs_def)
  finally show "\<Union> ` {component_edges G C |C. C \<in> connected_components G} = connected_components G"
    by auto
qed 

lemma component_edges_nonempty:
  assumes "dblton_graph G"
  shows "C \<in> connected_components G \<Longrightarrow> component_edges G C \<noteq> {}"
  using Vs_component_edges assms connected_comp_nempty vs_member by fastforce

lemma component_edges_finite:
  "\<lbrakk>finite G; C \<in> connected_components G\<rbrakk> \<Longrightarrow> finite (component_edges G C)"
  by (meson component_edges_subset rev_finite_subset)

lemma degree_in_component_is_degree:
  assumes "dblton_graph G"
  shows "degree (component_edges G (connected_component G x)) x = degree G x"
proof-
  have "\<lbrakk>{x, v} \<in> G; x \<noteq> v\<rbrakk> \<Longrightarrow>
         \<exists>xa y.
            {x, v} = {xa, y} \<and>
            xa \<in> connected_component G x \<and> y \<in> connected_component G x \<and> {xa, y} \<in> G" for v
    by(auto intro!: exI[of "\<lambda> xa.\<exists> y. {x, v} = {xa, y} \<and> _ xa y" x] 
        exI[of "\<lambda> y. {x, v} = {x, y} \<and> _ y" v]
        simp add: in_own_connected_component edges_reachable in_connected_componentI)
  thus ?thesis
    using assms
    by(auto simp add: degree_def component_edges_def insert_commute 
        intro!: arg_cong[of  _ _ card'])
qed

lemma degree_in_component_is_degree_two_verts:
  assumes "dblton_graph G" "x \<in> connected_component G y"
  shows "degree (component_edges G (connected_component G y)) x = degree G x"
  using connected_components_member_eq[OF assms(2)] degree_in_component_is_degree[OF assms(1), of x]
  by simp

lemma Vs_of_component_edges_is_component:
  "\<lbrakk>x \<in> connected_component G y; y \<noteq> x; dblton_graph G\<rbrakk> \<Longrightarrow> 
      Vs (component_edges G (connected_component G y)) = connected_component G y"
proof(rule, goal_cases)
  case 2
  have obtain_edge:"\<exists> z. xx \<noteq> z \<and> {xx, z} \<in> G" if "xx \<in> connected_component G y" for xx
  proof(cases "xx = y")
    case False
    have y_xx:"y \<in> connected_component G xx"
      using that connected_components_member_sym by force
    then obtain p where "walk_betw G xx p y" 
      using 2(2) 
      by(auto intro: in_connected_component_has_walk in_connected_componentE[OF y_xx]
          in_connected_componentE[OF 2(1)] 
          in_con_comp_has_walk[OF connected_components_member_sym[OF 2(1)]])
    then obtain p where "walk_betw G xx p y" "distinct p" 
      using "2"(2) False by(auto dest: walk_betw_different_verts_to_ditinct)
    moreover hence "length p \<ge> 2" 
      using "2"(2) False by(auto intro: walk_betw_length)
    ultimately have "\<exists> z. xx \<noteq> z \<and> {xx, z} \<in> G"
      using 2(2) False by(all \<open>cases p rule: list_cases3\<close>)(auto simp add: walk_betw_def)
    thus ?thesis 
      by simp
  next
    case True
    then obtain p where "walk_betw G xx p x" 
      using  "2"(1,2) in_con_comp_has_walk[of x G y] by auto
    then obtain p where "walk_betw G xx p x" "distinct p" 
      using "2"(2) True by(auto dest: walk_betw_different_verts_to_ditinct)
    moreover hence "length p \<ge> 2" 
      using "2"(2) True by(auto intro: walk_betw_length)
    ultimately have "\<exists> z. xx \<noteq> z \<and> {xx, z} \<in> G"
      using 2(2) True by(all \<open>cases p rule: list_cases3\<close>)(auto simp add: walk_betw_def)
    thus ?thesis 
      by simp
  qed
  show ?case 
  proof(rule, goal_cases)
    case (1 x)
    then obtain z where "x \<noteq> z" "{x, z} \<in> G"
      by(auto dest: obtain_edge)
    moreover hence "z \<in> connected_component G y" 
      using  "1" connected_components_member_eq[of x G y] 
             in_connected_componentI[OF edges_reachable ] 
      by force
    ultimately show ?case
      using 1
      by (auto simp add: Vs_def component_edges_def 
          intro!: exI[of _ "{x, z}"] exI[of "\<lambda> xx.\<exists> ya. {x, z} = {xx, ya} \<and> _ xx ya" x]
          exI[of "\<lambda> ya. {x, z} = {x, ya} \<and> _ ya" z])
  qed
qed (auto simp add: Vs_def component_edges_def)

subsection \<open>Adding Edges to Components\<close>

lemma unchanged_connected_component:
  assumes "u \<notin> C" "v \<notin> C" 
  shows "C \<in> connected_components G \<longleftrightarrow> C \<in> connected_components (insert {u, v} G)"
proof-

  text \<open>This is to cover two symmetric cases\<close>
  have unchanged_con_comp_2:
    "C \<in> connected_components G \<longleftrightarrow> C \<in> connected_components (insert {u, v} G)"
    if "u \<notin> C" "v \<notin> C" "u \<in> Vs G" "v \<notin> Vs G"
    for u v
  proof-
    note assms = that
    show ?thesis
    proof(rule iffI, goal_cases)
      case 1
      then obtain v' where *: "C = connected_component G v'" "v' \<in> Vs G"
        by (rule C_is_componentE)
      hence "v' \<in> Vs (insert {u, v} G)"
        by(simp add: Vs_def)
      moreover have "x \<in> C \<Longrightarrow> reachable (insert {u, v} G) v' x"for x
        using *
        by (auto intro: in_Vs_insert reachable_refl dest: reachable_subset elim!: in_connected_componentE)
      moreover have "reachable (insert {u, v} G) v' x \<Longrightarrow> x \<in> C" for x
        using * assms
        by (auto dest: reachability_split_2 intro!: in_connected_componentI)
      ultimately have "connected_component (insert {u,v} G) v' = C"
        by (rule connected_component_set)
      then show ?case
        using \<open>v' \<in> Vs (insert {u, v} G)\<close> connected_component_in_components
        by auto
    next
      case 2
      then obtain v' where *: "C = connected_component (insert {u, v} G) v'" "v' \<in> Vs (insert {u, v} G)"
        by (rule C_is_componentE)
      hence "v' \<in> Vs G"
        using assms in_own_connected_component
        by (fastforce elim: in_Vs_insertE)
      moreover have "reachable (insert {u, v} G) v' x \<Longrightarrow> reachable G v' x" for x
        using *(1) assms \<open>v' \<in> Vs G\<close>
        by (auto dest: in_connected_componentI reachable_subset reachability_split_2) 
      hence "x \<in> C \<Longrightarrow> reachable G v' x" for x
        using *
        by (auto simp: reachable_refl elim: in_connected_componentE)
      moreover have "reachable G v' x \<Longrightarrow> x \<in> C" for x
        using *
        by (auto simp: reachable_refl dest: reachable_subset intro: in_connected_componentI)
      ultimately have "connected_component G v' = C"
        by (rule connected_component_set)
      then show ?case
        using \<open>v' \<in> Vs G\<close> connected_component_in_components
        by auto
    qed
  qed

  show ?thesis
  proof(cases \<open>u \<in> Vs G\<close>)
    assume "u \<in> Vs G"
    then show ?thesis
    proof(cases \<open>v \<in> Vs G\<close>)
      assume "v \<in> Vs G"
      note assms = assms \<open>u \<in> Vs G\<close> \<open>v \<in> Vs G\<close>
      show ?thesis
      proof(rule iffI, goal_cases)
        case 1
        then obtain v' where *: "C = connected_component G v'" "v' \<in> Vs G"
          by (rule C_is_componentE)
        hence "v' \<in> Vs (insert {u, v} G)"
          by(simp add: Vs_def)
        moreover have "x \<in> C \<Longrightarrow> reachable (insert {u, v} G) v' x"for x
          using * 
          by (auto intro: in_Vs_insert reachable_refl dest: reachable_subset
              elim!: in_connected_componentE)
        moreover have "reachable (insert {u, v} G) v' x \<Longrightarrow> x \<in> C" for x
          using *(1) assms
          by (auto dest: reachability_split intro!: in_connected_componentI)
        ultimately have "connected_component (insert {u,v} G) v' = C"
          by (rule connected_component_set)
        then show ?case
          using \<open>v' \<in> Vs (insert {u, v} G)\<close> connected_component_in_components
          by auto
      next
        case 2
        then obtain v' where *: "C = connected_component (insert {u, v} G) v'"
                                "v' \<in> Vs (insert {u, v} G)"
          by (rule C_is_componentE)
        hence "v' \<in> Vs G"
          using assms
          by (auto elim: in_Vs_insertE)
        moreover have "x \<in> C \<Longrightarrow> reachable G v' x" for x    
          using assms \<open>v' \<in> Vs G\<close>
          by (auto simp: *(1) elim!: in_connected_componentE 
              dest!: reachability_split dest: in_connected_componentI reachable_subset
              intro: reachable_refl)
        moreover have "reachable G v' x \<Longrightarrow> x \<in> C" for x
          using *
          by (auto dest: reachable_subset in_connected_componentI)
        ultimately have "connected_component G v' = C"
          by (rule connected_component_set)
        then show ?case
          using \<open>v' \<in> Vs G\<close> connected_component_in_components
          by auto
      qed

    next
      assume "v \<notin> Vs G"
      show ?thesis
        using unchanged_con_comp_2[OF assms \<open>u \<in> Vs G\<close> \<open>v \<notin> Vs G\<close>]
        .
    qed
  next
    assume "u \<notin> Vs G"
    then show ?thesis
    proof(cases \<open>v \<in> Vs G\<close>)
      assume "v \<in> Vs G"
      show ?thesis
        using unchanged_con_comp_2[OF assms(2,1) \<open>v \<in> Vs G\<close> \<open>u \<notin> Vs G\<close>]
        by (subst insert_commute)
    next
      assume "v \<notin> Vs G"
      note assms = assms \<open>u \<notin> Vs G\<close> \<open>v \<notin> Vs G\<close>
      show ?thesis
      proof(rule iffI, goal_cases)
        case 1
        then obtain v' where *: "C = connected_component G v'" "v' \<in> Vs G"
          by (rule C_is_componentE)
        hence "v' \<in> Vs (insert {u, v} G)"
          by(simp add: Vs_def)
        moreover have "x \<in> C \<Longrightarrow> reachable (insert {u, v} G) v' x"for x
          using *
          by (auto intro: reachable_refl in_Vs_insert dest: reachable_subset elim!: in_connected_componentE)
        moreover have "x \<in> C" if "reachable (insert {u, v} G) v' x" for x
        proof-
          have "\<not> reachable {{u, v}} v' x"
            using * assms \<open>u \<notin> Vs G\<close> \<open>v \<notin> Vs G\<close>
            by (auto dest: reachable_in_Vs(1) elim: vs_member_elim)
          thus ?thesis                                     
            using * that assms
            by (fastforce dest!: reachability_split3 simp add: in_connected_componentI)
        qed
        ultimately have "connected_component (insert {u,v} G) v' = C"
          by (rule connected_component_set)
        then show ?case
          using \<open>v' \<in> Vs (insert {u, v} G)\<close> connected_component_in_components
          by auto
      next
        case 2
        then obtain v' where *: "C = connected_component (insert {u, v} G) v'" "v' \<in> Vs (insert {u, v} G)"
          by (rule C_is_componentE)
        hence "v' \<in> Vs G"
          using assms in_own_connected_component
          by (force elim!: in_Vs_insertE)
        moreover have "reachable G v' x" if "reachable (insert {u, v} G) v' x" for x
        proof-
          have "\<not> reachable {{u, v}} v' x"
            using \<open>v' \<in> Vs G\<close> assms
            by (auto dest: reachable_in_Vs(1) elim: vs_member_elim)
          thus ?thesis
            using * assms that
            by (auto dest: reachability_split3)
        qed
        hence "x \<in> C \<Longrightarrow> reachable G v' x" for x
          using *
          by (auto simp: *(1) reachable_refl elim!: in_connected_componentE)
        moreover have "reachable G v' x \<Longrightarrow> x \<in> C" for x
          using *
          by (auto dest: reachable_subset in_connected_componentI)
        ultimately have "connected_component G v' = C"
          by (rule connected_component_set)
        then show ?case
          using \<open>v' \<in> Vs G\<close> connected_component_in_components
          by auto
      qed
    qed
  qed
qed

(*TODO rename connected_components_insert *)

lemma connected_components_union:
  assumes "Cu \<in> connected_components G" "Cv \<in> connected_components G"
  assumes "u \<in> Cu" "v \<in> Cv"
  shows "Cu \<union> Cv \<in> connected_components (insert {u, v} G)"
proof-
  have "u \<in> Vs (insert {u, v} G)" using assms(1) by (simp add: Vs_def)
  have "v \<in> Vs (insert {u, v} G)" using assms(1) by (simp add: Vs_def)

  have "reachable (insert {u, v} G) v x" if x_mem: "x \<in> Cu \<union> Cv" for x
  proof-
    have "reachable G u x \<or> reachable G v x"
      using x_mem assms
      by (auto dest: same_con_comp_reachable)
    then have "reachable (insert {u, v} G) u x \<or> reachable (insert {u, v} G) v x"
      by (auto dest: reachable_subset)
    thus ?thesis
      using edges_reachable[where G = "insert {u,v} G"]
      by (auto dest: reachable_trans)
  qed

  moreover note * = connected_comp_verts_in_verts[OF \<open>u \<in> Cu\<close> \<open>Cu \<in> connected_components G\<close>]
          connected_comp_verts_in_verts[OF \<open>v \<in> Cv\<close> \<open>Cv \<in> connected_components G\<close>]
  hence "reachable (insert {u, v} G) v x \<Longrightarrow> x \<in> Cu \<union> Cv" for x
    by(auto dest: in_connected_componentI reachability_split
            simp: connected_components_closed'[OF \<open>u \<in> Cu\<close> \<open>Cu \<in> connected_components G\<close>]
                  connected_components_closed'[OF \<open>v \<in> Cv\<close> \<open>Cv \<in> connected_components G\<close>])

  ultimately have "Cu \<union> Cv = connected_component (insert {u, v} G) v"
    apply(intro connected_component_set[symmetric])
    by(auto intro: in_Vs_insert)
  thus ?thesis
    using \<open>v \<in> Vs (insert {u, v} G)\<close> 
    by(auto intro: connected_component_in_components)
qed

lemma connected_components_insert_2:
  assumes "Cu \<in> connected_components G" "Cv \<in> connected_components G"
  assumes "u \<in> Cu" "v \<in> Cv"
  shows "connected_components (insert {u, v} G) = 
           insert (Cu \<union> Cv) ((connected_components G) - {Cu, Cv})"
proof-
  have Cuvins: "Cu \<union> Cv \<in> connected_components (insert {u, v} G)"
    by (simp add: assms connected_components_union)
  have "C \<in> connected_components (insert {u, v} G)" 
    if in_comps: "C \<in> insert (Cu \<union> Cv) (connected_components G - {Cu, Cv})" for C
  proof-
    consider (Cuv) "C = (Cu \<union> Cv)" | (other) "C \<in> connected_components G" "C \<noteq> Cu" "C \<noteq> Cv"
      using in_comps
      by blast
    thus ?thesis
    proof cases
      case other
      then show ?thesis
        using assms
        apply(subst unchanged_connected_component[symmetric])
        by (auto dest: connected_components_closed'[where C = C]
            connected_components_closed'[where C = Cu]
            connected_components_closed'[where C = Cv])
    qed (simp add: Cuvins)
  qed
  moreover have "C \<in> insert (Cu \<union> Cv) ((connected_components G) - {Cu, Cv})"
    if in_comps: "C \<in> connected_components (insert {u, v} G)" for C
  proof-
    have "u \<in> C \<or> v \<in> C \<Longrightarrow> C = Cu \<union> Cv"
      using Cuvins in_comps connected_components_closed'[where C = C] \<open>u \<in> Cu\<close> \<open>v \<in> Cv\<close>
            connected_components_closed'[where C = "Cu \<union> Cv"]
      by blast
    moreover have "C \<in> connected_components G" if "u \<notin> C"
    proof(cases \<open>v \<in> C\<close>)
      case True
      then show ?thesis
        using in_comps \<open>u \<in> Cu\<close> calculation that
        by auto
    next
      case False
      then show ?thesis
        apply(subst unchanged_connected_component[where u = u and v = v])
        using that in_comps
        by auto
    qed
    ultimately show ?thesis
      using assms(3, 4) by blast
  qed
  ultimately show ?thesis
    by auto

qed

lemma connected_components_insert_1:
  assumes "C \<in> connected_components G" "u \<in> C" "v \<in> C"
  shows "connected_components (insert {u, v} G) = connected_components G"
  using assms connected_components_insert_2 by fastforce

lemma in_con_comp_insert: "v \<in> connected_component (insert {u, v} G) u"
  using edges_are_walks[OF insertI1]
  by (force simp add: connected_component_def reachable_def)

lemma connected_components_insert:
  assumes "C \<in> connected_components G" "u \<in> C" "v \<notin> Vs G"
  shows "insert v C \<in> connected_components (insert {u, v} G)"
proof-
  have "u \<in> Vs (insert {u, v} G)" by (simp add: Vs_def)
  moreover have "connected_component (insert {u, v} G) u = insert v C"
  proof(standard, goal_cases)
    case 1
    thus ?case
      using assms
      by (fastforce elim: in_con_comp_has_walk dest!: vwalk_betw_can_be_split_2
                    simp add: in_connected_componentI4 connected_comp_verts_in_verts)
  next
    case 2
    have "C = connected_component G u"
      by (simp add: assms connected_components_closed')
    then show ?case
      by(auto intro!: insert_subsetI con_comp_subset[simplified]
              simp add: in_con_comp_insert)
  qed
  ultimately show ?thesis 
    using connected_components_closed' 
    by (fastforce dest: own_connected_component_unique)
qed

lemma connected_components_insert_3:
  assumes "C \<in> connected_components G" "u \<in> C" "v \<notin> Vs G"
  shows "connected_components (insert {u, v} G) = insert (insert v C) (connected_components G - {C})"
proof-
  have un_con_comp: "insert v C \<in> connected_components (insert {u, v} G)"
    by (simp add: assms connected_components_insert)
  have "D \<in> connected_components (insert {u, v} G)" 
    if "D \<in> insert (insert v C) (connected_components G - {C})"
    for D
  proof-
    from that consider (ins) "D = insert v C" | (other) "D \<in> connected_components G" "D \<noteq> C"
      by blast
    thus ?thesis
    proof cases
      case other
      moreover hence "v \<notin> D"
        using assms
        by (auto intro: connected_comp_verts_in_verts) 
      moreover have "u \<notin> D"
        using other assms 
        by (auto dest: connected_components_closed') 
      ultimately show ?thesis
        by(auto dest: unchanged_connected_component)
    qed (simp add: un_con_comp)
  qed
  moreover have "D \<in> insert (insert v C) (connected_components G - {C})"
    if "D \<in> connected_components (insert {u, v} G)"
    for D
  proof-
    have "u \<in> D \<longleftrightarrow> D = insert v C"
      using that assms(2) un_con_comp
      by (fastforce dest: connected_components_closed'')
    moreover hence "u \<in> D \<longleftrightarrow> v \<in> D"
      using that un_con_comp
      by (auto dest: connected_components_eq')
    ultimately show ?thesis 
        using that assms(2)
        by (auto simp: unchanged_connected_component[symmetric])
    qed
  ultimately show ?thesis by blast
qed

lemma connected_components_insert_1':
  "\<lbrakk>u \<in> Vs G; v \<in> Vs G\<rbrakk> \<Longrightarrow> 
     connected_components (insert {u, v} G)
       = insert (connected_component G u \<union> connected_component G v)
                     ((connected_components G) - {connected_component G u, connected_component G v})"
  by (auto simp add: connected_components_insert_2 in_own_connected_component
           dest!: connected_component_in_components)

lemma connected_components_insert_2':
  "\<lbrakk>u \<in> Vs G; v \<notin> Vs G\<rbrakk> 
   \<Longrightarrow> connected_components (insert {u, v} G)
         = insert (insert v (connected_component G u)) (connected_components G - {connected_component G u})"
  by (fastforce simp add: connected_components_insert_3 in_own_connected_component
                dest!: connected_component_in_components)

(*TODO: replace with connected_components_insert_4 everywhere*)

lemma connected_components_insert_4:
  assumes "u \<notin> Vs G" "v \<notin> Vs G"
  shows "connected_components (insert {u, v} G) = insert {u, v} (connected_components G)"
proof-
  have connected_components_small:
    "{u, v} \<in> connected_components (insert {u, v} G)"
  proof-
    have "u \<in> Vs (insert {u, v} G)"
      by (simp add: Vs_def)
    moreover have "connected_component (insert {u, v} G) u = {u, v}"
    proof(intro connected_component_set, goal_cases)
      case 1
      then show ?case
        by (simp add: Vs_def)
    next
      case (2 x)
      then show ?case
        by (auto simp add: \<open>u \<in> Vs (insert {u, v} G)\<close> reachable_refl edges_reachable)
    next
      case (3 x)
      then show ?case
        using reachable_in_Vs(1)
        by (fastforce simp add: assms dest: reachability_split3 walk_betw_singletonD elim: reachableE)
    qed
    ultimately show ?thesis
      by (fastforce dest: connected_component_in_components)
  qed

  have "{u, v} \<in> connected_components (insert {u, v} G)"
    by (simp add: assms connected_components_small)
  hence "C \<in> insert {u, v} (connected_components G)"
    if "C \<in> connected_components (insert {u, v} G)"
    for C
  proof(cases "C = {u, v}")
    case False
    hence "u \<notin> C" "v \<notin> C"
      using \<open>{u, v} \<in> connected_components (insert {u, v} G)\<close> that
      by (auto dest: connected_components_eq')
    hence "C \<in> connected_components G"
      using that
      by (auto dest: unchanged_connected_component)
    thus ?thesis
      by simp
  qed simp
  moreover have "C \<in> connected_components (insert {u, v} G)"
    if "C \<in> insert {u, v} (connected_components G)"
    for C
  proof(cases "C = {u, v}")
    case True
    thus ?thesis
      by (simp add: \<open>{u, v} \<in> connected_components (insert {u, v} G)\<close>)
  next
    case False
    hence "u \<notin> C" "v \<notin> C"
      using \<open>{u, v} \<in> connected_components (insert {u, v} G)\<close> that assms
      by (force simp add: insert_commute connected_comp_verts_in_verts)+
    thus ?thesis
      using that 
      by (auto dest: unchanged_connected_component)
  qed 
  ultimately show ?thesis
    by auto
qed

lemma connected_components_insert_3':
  "\<lbrakk>u \<notin> Vs G; v \<notin> Vs G\<rbrakk>
   \<Longrightarrow> connected_components (insert {u, v} G) = insert {u, v} (connected_components G)"
  using connected_components_insert_4
  .

text \<open>Elimination rule for proving lemmas about connected components by induction on graph edges.\<close>

lemma in_insert_connected_componentE[case_names both_nin one_in two_in]:
  assumes "C \<in> connected_components (insert {u,v} G)"
    "\<lbrakk>u \<notin> Vs G; v \<notin> Vs G;
     C \<in> insert {u,v} (connected_components G)\<rbrakk>
     \<Longrightarrow> P"
    "\<And>u' v'.
     \<lbrakk>u' \<in> {u,v}; v' \<in> {u, v}; u' \<in> Vs G; v' \<notin> Vs G;
     C \<in> insert (insert v' (connected_component G u')) (connected_components G - {connected_component G u'})\<rbrakk>
     \<Longrightarrow> P"
    "\<lbrakk>u \<in> Vs G; v \<in> Vs G; connected_component G u \<noteq> connected_component G v;
     C \<in> insert (connected_component G u \<union> connected_component G v)
                     ((connected_components G) - {connected_component G u, connected_component G v})\<rbrakk>
     \<Longrightarrow> P"
    "C \<in> (connected_components G) \<Longrightarrow> P"
  shows "P"
proof(cases \<open>u \<in> Vs G\<close>)
  assume \<open>u \<in> Vs G\<close>
  show ?thesis
  proof(cases \<open>v \<in> Vs G\<close>)
    assume \<open>v \<in> Vs G\<close>
    show ?thesis
    proof(cases "connected_component G u = connected_component G v")
      assume \<open>connected_component G u = connected_component G v\<close>
      hence "connected_components (insert {u,v} G) = connected_components G"        
        using \<open>u \<in> Vs G\<close>
        by (subst connected_components_insert_1[OF connected_component_in_components])
           (auto intro!: in_own_connected_component)
      thus ?thesis
        apply -
        apply(rule assms(5))
        using assms(1)
        by simp
    next
      assume \<open>connected_component G u \<noteq> connected_component G v\<close>
      then show ?thesis
      apply(rule assms(4)[OF \<open>u \<in> Vs G\<close> \<open>v \<in> Vs G\<close>])
      using assms(1)
      apply(subst connected_components_insert_1'[OF \<open>u \<in> Vs G\<close> \<open>v \<in> Vs G\<close>, symmetric])
      .
    qed
  next
    assume \<open>v \<notin> Vs G\<close>
    show ?thesis
      apply(rule assms(3)[where u' = u and v' = v])
      using assms(1) \<open>u \<in> Vs G\<close> \<open>v \<notin> Vs G\<close>
      by (auto simp: connected_components_insert_2'[symmetric])
  qed
next
  assume \<open>u \<notin> Vs G\<close>
  show ?thesis
  proof(cases \<open>v \<in> Vs G\<close>)
    assume \<open>v \<in> Vs G\<close>
    show ?thesis
      apply(rule assms(3)[where u' = v and v' = u])
      using assms(1) \<open>u \<notin> Vs G\<close> \<open>v \<in> Vs G\<close>
      by (auto simp: connected_components_insert_2'[symmetric] insert_commute)
  next
    assume \<open>v \<notin> Vs G\<close>
    show ?thesis
      apply(rule assms(2)[OF \<open>u \<notin> Vs G\<close> \<open>v \<notin> Vs G\<close>])
      using assms(1)
      apply(subst connected_components_insert_3'[OF \<open>u \<notin> Vs G\<close> \<open>v \<notin> Vs G\<close>, symmetric])
      .
  qed
qed

text \<open>If an edge is added between two different components, how do the components change?\<close>

lemma new_edge_disjoint_components: 
  assumes "u = u"  "v = v" "E = E"
  defines "E_new \<equiv> insert {u,v} E"
  shows "connected_component E_new u = connected_component E_new v"
  using connected_components_member_eq in_con_comp_insert
  by (fastforce simp add: E_new_def)

lemma unite_disjoint_components_by_new_edge:
  assumes "u \<notin>connected_component E x" "v \<notin>connected_component E x"
  defines "E_new \<equiv> insert {u,v} E"
  shows "connected_component E x =connected_component E_new x "
  using  assms(1,2) connected_component_in_components[of x ]
         unchanged_connected_component[of u "connected_component E x" v ] 
         connected_components_notE_singletons[of x ] in_Vs_insertE
  by (cases "x \<in> Vs E") 
     (auto intro: in_Vs_insertE[of x "{u, v}" E]
        simp add: connected_components_closed'' in_own_connected_component E_new_def)

lemma insert_edge_endpoints_same_component:
  assumes E_new_def: "E_new \<equiv> insert {u,v} E"
  shows "connected_component E u \<union> connected_component E v = connected_component E_new u "
    using assms  new_edge_disjoint_components[of u v E] con_comp_subset[of E "insert {u, v} E"] 
          unite_disjoint_components_by_new_edge[of u E _ v] connected_components_member_sym 
    by(fastforce simp add: E_new_def)

lemma new_component_insert_edge: 
  assumes "connected_component E u \<noteq> connected_component E v" "u \<in> X" "v \<in> X"
  defines "E_new \<equiv> insert {u,v} E"
    shows "comps X E_new = comps X E - {connected_component E u,  connected_component E v} \<union> 
                             {connected_component E u \<union> connected_component E v}"
proof
  show "comps X E_new
    \<subseteq> comps X E - {connected_component E u, connected_component E v} \<union>
       {connected_component E u \<union> connected_component E v}"
  proof
    fix x
    assume xasms:" x \<in> comps X E_new"
    thus "x \<in> comps X E - {connected_component E u, connected_component E v} \<union>
              {connected_component E u \<union> connected_component E v}"
    proof(cases "x = (connected_component E u \<union> connected_component E v)")
      case True
      then show ?thesis by simp
    next
      case False
      then obtain w where w: "w \<in> X " "x = connected_component E_new w" 
        using xasms unfolding comps_def E_new_def by blast
      have "connected_component E_new w = connected_component E w"
      proof(rule ccontr)
        assume "connected_component E_new w \<noteq> connected_component E w"
        hence 11:"connected_component E w \<subset> connected_component E_new w"
          by (simp add: E_new_def con_comp_subset psubsetI subset_insertI)
        hence 12:"u \<in> connected_component E w \<or> v \<in> connected_component E w" unfolding E_new_def 
          using unite_disjoint_components_by_new_edge[of u E w v] by auto
        have " x = connected_component E u \<union> connected_component E v"
        proof(subst w(2), rule)
          show "connected_component E_new w \<subseteq> connected_component E u \<union> connected_component E v"
            using 12 insert_edge_endpoints_same_component[of E_new u v E]  E_new_def connected_components_member_eq[of u E_new w] 
                     connected_components_member_sym[of u E ]  11 insert_edge_endpoints_same_component[of E_new u v E]
                     connected_components_member_eq[of v E_new w]
                     connected_components_member_sym[of v E ]  insert_edge_endpoints_same_component[of E_new v u E]
              by fastforce
            show " connected_component E u \<union> connected_component E v \<subseteq> connected_component E_new w"
                using 12 E_new_def 11 new_edge_disjoint_components[of u v E]
                    con_comp_subset[of E E_new] connected_components_member_eq[of u _ w] 
                connected_components_member_eq[of v _ w]
                by blast           
        qed
        thus False using False by simp
      qed 
      moreover hence "x \<noteq> connected_component E u" "x \<noteq> connected_component E v"
        using E_new_def assms(1) connected_components_member_eq[of u E_new w]
              in_con_comp_insert[of v u E]  connected_components_member_eq[of v E u]
              in_connected_componentI2[of u u E] w(2) connected_components_member_eq[of v E_new w]
              in_con_comp_insert[of u v E, simplified]  connected_components_member_eq[of u E v]
              in_connected_componentI2[of v v E] doubleton_eq_iff[of u v v u, simplified] 
        by auto
      ultimately have "x \<in> comps X E - {connected_component E u, connected_component E v}" 
        by (simp add: comps_def w(1) w(2))
      thus "x \<in> comps X E - {connected_component E u, connected_component E v} \<union>
         {connected_component E u \<union> connected_component E v}" by simp
    qed
  qed
  show "comps X E - {connected_component E u, connected_component E v} \<union>
       {connected_component E u \<union> connected_component E v}
        \<subseteq> comps X E_new"
  proof
    fix x
    assume xasms: "x \<in> comps X E - {connected_component E u, connected_component E v} \<union>
             {connected_component E u \<union> connected_component E v} "
    thus "x \<in> comps X E_new "
    proof(cases "x \<noteq> connected_component E u \<union> connected_component E v")
      case True
        then obtain w where w: "w \<in> X " "x = connected_component E w" "w \<noteq> u" "w\<noteq>v"
        using xasms True by (auto simp add: comps_def E_new_def)
      then show ?thesis 
        using unite_disjoint_components_by_new_edge[of u E w v]  True  connected_components_member_eq[of u E w] 
              connected_components_member_eq[of v E w] xasms
        by (auto simp add: E_new_def comps_def)
    next
      case False
      hence False: "x = connected_component E u \<union> connected_component E v" by simp
      then show ?thesis using insert_edge_endpoints_same_component[of E_new u v E, OF E_new_def] assms(2)
        by(simp add: comps_def)
    qed
  qed
qed

lemma same_component_after_insert: 
  assumes "u \<in> X" "v \<in> X" "E=E"
  defines "E_new \<equiv> insert {u,v} E"
    shows "connected_component E_new u = connected_component E_new v"
  using connected_components_member_eq[of v E_new u] in_con_comp_insert[of v u E] 
  by (simp add: E_new_def)

subsection \<open>Components and Cardinality\<close>

lemma finite_con_comps:
  "finite (Vs G) \<Longrightarrow> finite (connected_components G)"
  by (auto simp: connected_components_def)

lemma connected_component_finite:
  "\<lbrakk>finite G; dblton_graph G; C \<in> connected_components G\<rbrakk> \<Longrightarrow> finite C"
  by (meson connected_component_subs_Vs finite_dbl_finite_verts finite_subset)

lemma number_comps_below_vertex_card:
  assumes "finite E" "finite X"
  shows "card (comps X E) \<le> card X"
  using assms(2) card_image_le 
  by(auto simp add: comps_def connected_component_def)

lemma finite_verts_finite_no_comps: "finite E \<Longrightarrow> finite X \<Longrightarrow> finite (comps X E)" 
  by (simp add: comps_def)

text \<open>By adding an edge between two different components, the number of components decreases.\<close>

theorem card_decrease_component_join:
  assumes "connected_component E u \<noteq> connected_component E v" "u \<in> X" "v \<in> X" "finite X" "finite E"
  defines "E_new \<equiv> insert {u,v} E"
  shows   "card (comps X E_new) + 1 = card (comps X E)"
proof-
  have comps:"comps X E_new = comps X E - {connected_component E u,  connected_component E v} \<union> 
                             {connected_component E u \<union> connected_component E v}"
    using new_component_insert_edge assms by simp
  have aa:"connected_component E u \<union> connected_component E v
         \<in> comps X E - {connected_component E u, connected_component E v} \<Longrightarrow>
         connected_component E u \<union> connected_component E v = connected_component E x \<Longrightarrow>
         x \<in> X \<Longrightarrow> False" for x
    using connected_components_member_eq[of u E] in_own_connected_component[of u E]
    by blast
  have bb: "connected_component E u \<union> connected_component E v
    \<in> comps X E - {connected_component E u, connected_component E v} \<Longrightarrow>
    connected_component E u \<union> connected_component E v \<in> connected_component E ` X"
    using  comps_def[of X E] connected_components_member_eq[of v E_new u]  
     in_con_comp_insert[of v u E] E_new_def
    by simp
  have "card (comps X E_new) = card (comps X E - {connected_component E u,  connected_component E v}) + 1"
    using finite_verts_finite_no_comps assms  aa bb comps
    by (fastforce intro: card_insert_disjoint elim: imageE[of "connected_component E u \<union> connected_component E v"
                                       "connected_component E" X])+
  moreover have "card (comps X E - {connected_component E u,  connected_component E v}) = 
                card (comps X E - {connected_component E u}) -1"
    by (simp add: assms(1) assms(2) assms(3) comps_def)
  moreover have "card (comps X E - {connected_component E u}) > 0"
    using assms(1) assms(3) assms(4) assms(5)  
          card_0_eq[of "comps X E - {connected_component E u}"] comps_def[of X E] finite_verts_finite_no_comps[of E X] 
    by fastforce
  moreover have " card (comps X E - {connected_component E u}) = 
                  card (comps X E) -1"
    by (simp add: assms(1) assms(2) assms(3) comps_def)
  moreover have "card (comps X E) > 0" 
    using calculation(3) calculation(4) by linarith
  ultimately show ?thesis by simp
qed

lemma number_of_comps_anti_mono_strict:
  assumes "B \<subseteq> A" "finite A" "x \<in> X" "connected_component B x \<subset> connected_component A x"
          "Vs A \<subseteq> X" "finite X"
  shows "card (comps X B) > card (comps X A)" 
proof-
  define f where "f = (\<lambda> C. let v = (SOME v. C = connected_component A v \<and> v \<in> X) in connected_component B v)"
  have some_value:"C \<in> (comps X A) \<Longrightarrow> C= connected_component A (SOME v. C = connected_component A v \<and> v \<in> X) \<and> 
                            (SOME v. C = connected_component A v \<and> v \<in> X) \<in> X"
    for C 
    using some_eq_ex[of "\<lambda> v. C = connected_component A v \<and> v \<in> X"]
    by(force simp add: comps_def) 
  have uneq_comps_disj:"C \<in> (comps X A) \<Longrightarrow> D \<in> (comps X A) \<Longrightarrow> C \<noteq> D \<Longrightarrow> f C \<inter> f D = {}" for C D
    unfolding  f_def  Let_def 
    apply(rule unequal_components_disjoint[of _ _ _ UNIV, simplified])
    using some_value[of C] some_value[of D]
          same_component_set_mono[OF assms(1)]
    by blast
  have never_same:"C \<in> (comps X A) \<Longrightarrow> D \<in> (comps X A) \<Longrightarrow> C \<noteq> D \<Longrightarrow> f C \<noteq> f D" for C D
    using uneq_comps_disj[of C D]  connected_component_non_empt by (fastforce simp add:  f_def)
  have img_subs:"f ` (comps X A) \<subseteq>  (comps X B)"
    by (simp add: f_def comps_def image_subsetI some_value)
  obtain v where v_prop:"v \<in> X" "v \<in> connected_component A x" "v \<notin> connected_component B x"
    using assms in_connected_component_in_edges[of _ A x] by force 
  have x_not_in_comp_v: "x \<notin> connected_component B v"
    using connected_components_member_sym v_prop(3) by fastforce
  have "connected_component B x \<in>  f ` (comps X A) \<Longrightarrow>
        connected_component B v \<in>  f ` (comps X A) \<Longrightarrow> False"
    using  connected_components_member_eq[OF v_prop(2)] 
     in_own_connected_component[of v B] same_component_set_mono[OF assms(1)]
      some_value  v_prop(3) f_def  
    by (metis (no_types, lifting) imageE)
  hence not_all_b_comp_chosen:"f ` (comps X A) \<subset> (comps X B)"
    using v_prop(1) assms(3) img_subs by(auto simp add: comps_def)
  have "card (comps X A) = card ( f ` (comps X A))"
    using never_same by (force intro!: sym[OF card_image] simp add: inj_on_def)
  also have "... < card (comps X B)"
    using psubset_card_mono[OF _ not_all_b_comp_chosen] assms
    by(simp add: comps_def)
  finally show ?thesis by simp
qed

lemma number_of_comps_anti_mono:
  "\<lbrakk>B \<subseteq> A; finite B; finite X\<rbrakk> \<Longrightarrow> card (comps X B) \<ge> card (comps X A)"
  unfolding comps_def
proof(rule card_inj[where f = "\<lambda> C. (let x = (SOME x. x \<in> C \<and> x \<in> X) in connected_component B x)"], goal_cases)
  case 1
  thus ?case
    using  some_eq_ex[of "\<lambda> x. (x = _ \<or> reachable A _ x) \<and> x \<in> X"] 
    by(fastforce intro!: imageI simp add:  Pi_def connected_component_def Let_def Vs_def)
  case 2
  show ?case
  proof(rule inj_onI, goal_cases)
    case (1 x y)
    thus ?case
      using sym[OF same_connected_component_SOME[of _ X A]]
      by (smt (verit, best) "2"(1) Eps_cong image_iff same_component_set_mono)
  qed 
qed simp

lemma card_connected_components':
  "\<lbrakk>X \<subseteq> G; finite X; \<And> e. e\<in>X \<Longrightarrow> \<exists>u v. e = {u, v} \<and> u \<noteq> v; finite V\<rbrakk> \<Longrightarrow> 
    card (connected_components' V X) = card (connected_components X) + card (V - Vs X)"
proof(goal_cases)
  case 1
  then have "dblton_graph X" unfolding dblton_graph_def by simp
  from Union_connected_components[OF this]
  have "connected_components X \<inter> ((\<lambda>v. {v}) ` (V - (Vs X))) = {}"
    by (smt (verit) DiffD2 UnionI disjoint_iff imageE singletonI)
  have "card ((\<lambda>v. {v}) ` (V - (Vs X))) = card (V - Vs X)"
    by (simp add: card_image)
  have "finite (connected_components X)"
    by (simp add: "1"(2) \<open>dblton_graph X\<close> finite_dbl_finite_verts connected_components_def )
  have "finite ((\<lambda>v. {v}) ` (V - (Vs X)))"
    using \<open>finite V\<close> by auto
  show "card (connected_components' V X) = card (connected_components X) + card (V - Vs X)"
    unfolding connected_components'_def using card_Un_disjoint[OF \<open>finite (connected_components X)\<close>
        \<open>finite ((\<lambda>v. {v}) ` (V - (Vs X)))\<close> \<open>connected_components X \<inter> ((\<lambda>v. {v}) ` (V - (Vs X))) = {}\<close>]
      \<open>card ((\<lambda>v. {v}) ` (V - (Vs X))) = card (V - Vs X)\<close> by simp
qed

lemma con_comp_card_2:
  assumes con_comp: "C \<in> connected_components G"
  assumes finite_comp: "finite C"
  assumes doubleton_edges: "\<And>e. e\<in>G \<Longrightarrow> \<exists>u v. e = {u, v} \<and> u \<noteq> v"
  shows "card C \<ge> 2"
proof-
  obtain X where "X \<in> C" "X \<in> Vs G"
    using con_comp connected_comp_nempty connected_component_subs_Vs by blast
  then obtain F where "F \<in> G" "X \<in> F" unfolding Vs_def by blast
  then obtain Y where "X \<noteq> Y" "F = {X, Y}" using doubleton_edges by force
  hence "Y \<in> C"
    using \<open>F \<in> G\<close> \<open>X \<in> C\<close> con_comp 
    by (fastforce intro: in_connected_componentI4 dest: edges_are_walks)
  show "card C \<ge> 2"
    using finite_comp \<open>X \<in> C\<close> \<open>X \<noteq> Y\<close> \<open>Y \<in> C\<close>
    by(auto simp: eval_nat_numeral not_less_eq_eq[symmetric] dest: card_le_Suc0_iff_eq)
qed

subsection \<open>Components and Paths\<close>

lemma same_con_comp_path:
  "\<lbrakk>C \<in> connected_components G; w \<in> C; x \<in> C\<rbrakk> 
    \<Longrightarrow>\<exists>pwx. pwx \<noteq> [] \<and> path G pwx \<and> hd pwx = w \<and> last pwx = x"
  by(auto elim!: same_con_comp_walk[where x = x] simp: walk_betw_def)

lemma in_con_compI:
  assumes connected: "puv \<noteq> []" "path G puv" "hd puv = u" "last puv = v" and
    u_mv: "u\<in>Vs G" and
    uC: "u \<in> C" and
    C_in_comp: "C \<in> connected_components G"
  shows "v \<in> C"
proof(cases "u = v")
  case True
  then show ?thesis using assms by simp
next
  obtain w where w: "w \<in> Vs G" "C = connected_component G w"
    using C_in_comp
    by (smt connected_components_def mem_Collect_eq)
  then obtain pwu where pwu: "pwu \<noteq> []" "path G pwu" "hd pwu = w" "last pwu = u"
    using uC C_in_comp
    unfolding connected_components_def connected_component_def
    apply simp
    by (metis (no_types, lifting) C_in_comp in_own_connected_component same_con_comp_path uC w(2))
  moreover case False
  ultimately have "path G (pwu @ (tl puv))" "hd (pwu @ (tl puv)) = w" "last (pwu @ (tl puv)) = v"
    apply(intro path_append connected pwu tl_path_is_path; simp)
    using connected pwu path.simps
    by fastforce+
  then show ?thesis
    using w
    by (metis Nil_is_append_conv contra_subsetD last_in_set path_subset_conn_comp pwu(1))
qed

lemma component_has_path_no_cycle:
  assumes "finite C" "C \<in> connected_components G" "card C \<ge> 2"
  shows "\<exists>p. path G p \<and> C = (set p) \<and> hd p \<noteq> last p"
proof-
  obtain p where p: "path G p" "C = (set p)"
    using assms component_has_path'
    by auto
  then show ?thesis
    using remove_cycle_pfx_works_card_ge_2
    by (metis assms(3) path_suff remove_cycle_pfx_works)
qed

subsection \<open>Path-Shaped Components\<close>

theorem component_has_path_distinct:
  assumes "finite G" and "dblton_graph G" and
    "C \<in> connected_components G" and
    "\<And>v. v \<in> Vs G \<Longrightarrow> degree G v \<le> 2"
  shows "\<exists>p. path G p \<and> C = (set p) \<and> distinct p"
  using assms
proof(induction "G" arbitrary: C)    
  case (insert e G')
  then obtain u v where uv[simp]: "e = {u,v}" "u \<noteq> v"
    by (force elim!: exists_conj_elims simp: dblton_graph_def)
  hence "u \<in> Vs (insert e G')" "v \<in> Vs (insert e G')"
    using insert
    by (auto simp: Vs_def)
  moreover have "degree (insert e G') u \<noteq> 0" "degree (insert e G') v \<noteq> 0"
    by(fastforce simp: degree_neq_zeroI[where e = e])+
  moreover have "\<lbrakk>x \<noteq>0; x \<noteq> 1; x \<noteq> 2\<rbrakk> \<Longrightarrow> 2 < x" for x::enat
    by (fastforce simp: eval_enat_numeral one_eSuc dest!: ileI1[simplified order_le_less] dest: gr_zeroI)  
  ultimately have degree_uv:
    "degree (insert e G') u \<le> 2" "degree (insert e G') v \<le> 2"
    by (auto simp: linorder_not_le[symmetric] simp del: \<open>e = {u,v}\<close>
        dest!: \<open>\<And>v'. v' \<in> Vs (insert e G') \<Longrightarrow> degree (insert e G') v' \<le> 2\<close>)

  have "v \<in> Vs G' \<Longrightarrow> degree G' v \<le> 2" for v
    using subset_edges_less_degree[where G' = G' and G = "insert e G'"]
    by (fastforce intro: dual_order.trans dest!: insert.prems(3) dest: in_Vs_insert[where e = e])
  then have IH: "C \<in> connected_components G' \<Longrightarrow> \<exists>p. path G' p \<and> C = set p \<and> distinct p"    
    for C
    using insert.IH insert.prems(1)
    by fastforce

  have deg_3: False
    if "p1 \<noteq> []" "p2 \<noteq> []" "path G (p1 @ u' # p2)" "{u, v} \<in> G" "v' \<notin> set (p1 @ u' # p2)"
      "distinct (p1 @ u' # p2)" "u' \<in> {u,v}" "u \<noteq> v" "v' \<in> {u, v}"
      "degree G u' \<le> 2"
    for G p1 u' v' p2
  proof-
    obtain v1 p1' where [simp]: "p1 = p1' @ [v1]"
      using \<open>p1 \<noteq> []\<close>
      by (auto simp: neq_Nil_conv_snoc)
    moreover obtain v2 p2' where [simp]: "p2 = v2 # p2'"
      using \<open>p2 \<noteq> []\<close>
      by (auto simp: neq_Nil_conv)
    ultimately have "v1 \<noteq> v2"
      using \<open>distinct (p1 @ u' # p2)\<close> \<open>path G (p1 @ u' # p2)\<close> path_2 path_suff
      by fastforce+
    moreover have "{v1,u'} \<in> G" "{u',v2} \<in> G"
      using \<open>path G (p1 @ u' # p2)\<close> path_2 path_suff
      by fastforce+
    moreover have "v1 \<noteq> v" "v1 \<noteq> u" "v2 \<noteq> v" "v2 \<noteq> u"
      using \<open>u' \<in> {u,v}\<close> \<open>v' \<in> {u, v}\<close> \<open>distinct (p1 @ u' # p2)\<close> \<open>v' \<notin> set (p1 @ u' # p2)\<close>
        mem_path_Vs[OF \<open>path G (p1 @ u' # p2)\<close>] \<open>u \<noteq> v\<close>
      by fastforce+
    moreover have "{u', SOME x. x \<in> {u, v} - {u'}} = {u,v}"
    proof-
      have "{u,v} - {v} = {u}"
        using \<open>u \<noteq> v\<close>
        by auto
      thus ?thesis
        using \<open>u' \<in> {u, v}\<close> \<open>u \<noteq> v\<close>
        by (fastforce simp add: Hilbert_choice_singleton)
    qed
    moreover have "u' \<noteq> (SOME x. x \<in> {u, v} - {u'})"
      using \<open>u' \<in> {u,v}\<close> \<open>u \<noteq> v\<close>
      by (fastforce intro!: Hilbert_set_minus)
    ultimately have "3 \<le> degree G u'"
      using \<open>{u, v} \<in> G\<close> \<open>v' \<notin> set (p1 @ u' # p2)\<close> \<open>distinct (p1 @ u' # p2)\<close>
      by (intro degree_3[where u = v1 and w = v2 and x = "SOME x. x \<in> ({u,v} - {u'})"]) auto
    thus False
      using degree_uv \<open>u' \<in> {u,v}\<close> \<open>degree G u' \<le> 2\<close>
      by(auto simp add: eval_enat_numeral one_eSuc dest: order_trans[where z = "eSuc 1"])
  qed

  from \<open>C \<in> connected_components (insert e G')\<close>[simplified \<open>e = {u, v}\<close>]
  show ?case
  proof(elim in_insert_connected_componentE, goal_cases)
    case 1
    then show ?case
    proof(safe, goal_cases)
      case 1
      then show ?case
        using \<open>u \<noteq> v\<close> \<open>v \<in> Vs (insert e G')\<close> \<open>e = {u,v}\<close>
        by (fastforce intro!: exI[where x = "[u, v]"])
    qed (fastforce dest: IH intro: path_subset)
  next
    case (2 u' v')
    moreover obtain p where "path G' p" "(connected_component G' u') = set p" "distinct p"
      using \<open>u' \<in> Vs G'\<close>
      by (force elim!: exists_conj_elims intro: IH simp add: connected_component_in_components)
    moreover then obtain p1 p2 where [simp]: "p = p1 @ u' # p2" "u' \<notin> set p1"
      using in_own_connected_component iffD1[OF in_set_conv_decomp_first]
      by (force elim!: exists_conj_elims)
    moreover hence "u' \<notin> set p2"
      using \<open>distinct p\<close>
      by auto
    moreover have "v' \<notin> set (p1 @ u' # p2)"
      using \<open>v' \<notin> Vs G'\<close> mem_path_Vs[OF \<open>path G' p\<close> ]
      by auto
    ultimately have False
      if "p1 \<noteq> []" "p2 \<noteq> []"
      by (fastforce intro!: deg_3[OF that, where G = "insert e G'" and v' = v' and u' = u']
          intro!: insert in_Vs_insert dest: path_subset[where G' = "insert e G'"])
    hence "p1 = [] \<or> p2 = []"
      by auto

    from "2"(5) show ?case
    proof(elim insertE[where a = C], goal_cases)
      case 1
      moreover from 2 have "path (insert e G') (v' # u' # p2)"
        using \<open>path G' p\<close>[simplified]
        by (fastforce intro: path_subset dest: path_suff)
      moreover from 2 have "path (insert e G') (p1 @ [u', v'])" if "p2 = []"
        using \<open>path G' p\<close>[simplified ] that 
        by (subst rev_path_is_path_iff[symmetric], subst (asm) rev_path_is_path_iff[symmetric]) (auto intro: path_subset)

      ultimately show ?case
        using \<open>p1 = [] \<or> p2 = []\<close> \<open>distinct p\<close> \<open>u' \<notin> set p2\<close> mem_path_Vs \<open>path G' p\<close> "2"(1-4)
        by (force intro!: exI[where x = "if p1 = [] then  v' # u' # p2 else p1 @ [u', v']"]
            simp add: \<open>connected_component G' u' = set p\<close>)
    qed (fastforce dest: IH intro: path_subset)
  next
    case 3

    from \<open>connected_component G' u \<noteq> connected_component G' v\<close>
    have "v \<notin> connected_component G' u" "u \<notin> connected_component G' v"
      using connected_components_member_eq
      by (fastforce simp only:)+
    from \<open>connected_component G' u \<noteq> connected_component G' v\<close>
    have "connected_component G' u \<inter> connected_component G' v = {}"
      using connected_components_disj
      by(auto intro!: connected_component_in_components 3)

    {
      fix u'
      assume "u' \<in> {u,v}"
      then obtain v' where \<open>v' \<in> {u,v}\<close> \<open>u' \<noteq> v'\<close>
        using uv(2)
        by blast
      obtain p where i: "path G' p" "(connected_component G' u') = set p" "distinct p"
        using \<open>u \<in> Vs G'\<close> \<open>v \<in> Vs G'\<close> \<open>u' \<in> {u,v}\<close>
        by (force elim!: exists_conj_elims intro: IH simp add: connected_component_in_components)
      moreover then obtain p1 p2 where [simp]: "p = p1 @ u' # p2" "u' \<notin> set p1"
        using in_own_connected_component iffD1[OF in_set_conv_decomp_first]
        by (force elim!: exists_conj_elims)
      moreover hence "u' \<notin> set p2"
        using \<open>distinct p\<close>
        by auto
      moreover have "v' \<notin> set (p1 @ u' # p2)"
        using \<open>v \<notin> connected_component G' u\<close> \<open>u \<notin> connected_component G' v\<close>
          \<open>connected_component G' u' = set p\<close> \<open>u' \<in> {u,v}\<close> \<open>v' \<in> {u,v}\<close> \<open>u' \<noteq> v'\<close>
        by auto
      ultimately have False
        if "p1 \<noteq> []" "p2 \<noteq> []"
        using \<open>u' \<in> {u,v}\<close> \<open>v' \<in> {u,v}\<close> degree_uv
        by (intro deg_3[OF that, where G = "insert e G'" and v' = v' and u' = u']) 
          (force intro!: degree_uv(1) in_Vs_insert dest: path_subset[where G' = "insert e G'"])+
      hence "p1 = [] \<or> p2 = []"
        by auto
      hence "\<exists>p p1 p2. path G' p \<and> (connected_component G' u') = set p \<and> distinct p \<and>
                       p = p1 @ u' # p2 \<and> (p1 = [] \<or> p2 = [])"
        by (fastforce intro!: i intro: exI[where x = p])
    } note * = this

    obtain p p1 p2 where
      "path G' p" "(connected_component G' u) = set p" "distinct p" "(p1 = [] \<or> p2 = [])" and
      [simp]: "p = p1 @ u # p2"
      apply (elim exists_conj_elim_5_3)
      using *
      by blast

    obtain p' p1' p2' where
      "path G' p'" "(connected_component G' v) = set p'" "distinct p'" "(p1' = [] \<or> p2' = [])" and
      [simp]: "p' = p1' @ v # p2'"
      apply (elim exists_conj_elim_5_3)
      using *
      by blast
    from "3"(4) show ?case
    proof(elim insertE[where a = C], goal_cases)
      case 1
      define witness_p where
        "witness_p = 
               (if p1 = [] \<and> p1' = [] then
                  (rev p2 @ [u, v] @ p2')
                else if p1 = [] \<and> p2' = [] then
                  (rev p2 @ [u, v] @ rev p1')
                else if p2 = [] \<and> p1' = [] then
                  (p1 @ [u, v] @ p2')
                else if p2 = [] \<and> p2' = [] then
                  (p1 @ [u, v] @ rev p1')
                else
                  undefined)"

      from \<open>p1 = [] \<or> p2 = []\<close> \<open>p1' = [] \<or> p2' = []\<close> have "path (insert e G') witness_p"
        using \<open>path G' p\<close> \<open>path G' p'\<close>
        by (auto intro!: path_subset[where G' = "(insert {u, v} G')"]
            path_concat[where p = "p1 @ [u]" and q = "u # v # rev p1'", simplified]
            path_concat[where p = "rev p2 @ [u]" and q = "u # v # p2'", simplified]
            path_concat[where p = "rev p2 @ [u]" and q = "u # v # rev p1'", simplified]
            path_concat[where p = "p1 @ [u]" and q = "u # v # []", simplified]
            path_concat[where p = "p1 @ [u]" and q = "u # v # p2'", simplified]
            simp: rev_path_is_path_iff[symmetric, where p = "(rev p2 @ [u])"]
            rev_path_is_path_iff[symmetric, where p = "(rev p2 @ [u, v])"]
            rev_path_is_path_iff[symmetric, where p = "(v # rev p1')"]
            witness_p_def
            split: if_splits)
      moreover from \<open>p1 = [] \<or> p2 = []\<close> \<open>p1' = [] \<or> p2' = []\<close> have "distinct witness_p"
        using \<open>distinct p\<close> \<open>distinct p'\<close>
          \<open>(connected_component G' u) = set p\<close>
          \<open>v \<notin> connected_component G' u\<close>
          \<open>(connected_component G' v) = set p'\<close>
          \<open>u \<notin> connected_component G' v\<close>
          \<open>connected_component G' u \<inter> connected_component G' v = {}\<close>
        by (fastforce simp: witness_p_def  split: if_splits)
      moreover from \<open>p1 = [] \<or> p2 = []\<close> \<open>p1' = [] \<or> p2' = []\<close> have "C = set witness_p"
        using \<open>(connected_component G' u) = set p\<close> \<open>(connected_component G' v) = set p'\<close>
          \<open> C = connected_component G' u \<union> connected_component G' v\<close>
        by (fastforce simp: witness_p_def  split: if_splits)
      ultimately show ?case
        by auto
    qed (fastforce dest: IH intro: path_subset)
  qed (fastforce dest: IH intro: path_subset)
qed (auto simp: connected_components_empty intro!: exI[where x = "[]"])

corollary (in graph_abs) component_has_path_distinct:
  assumes
    "C \<in> connected_components G" and
    "\<And>v. v \<in> Vs G \<Longrightarrow> degree G v \<le> 2"
  shows "\<exists>p. path G p \<and> C = (set p) \<and> distinct p"
  using component_has_path_distinct[OF _ _ assms] graph
        finite_E
  by fastforce

definition component_path where
"component_path G C = (SOME p. path G p \<and> C = set p \<and> hd p \<noteq> last p)"

lemma component_path_works:
  assumes "finite C" "C \<in> connected_components G" "card C \<ge> 2"
  shows "path G (component_path G C) \<and> C = set (component_path G C)
          \<and> hd (component_path G C) \<noteq> last (component_path G C)"
  unfolding component_path_def
  apply(rule someI_ex)
  using component_has_path_no_cycle[OF assms] .

lemma component_walk_vertex_degress:
  assumes "\<And> x. x \<in> set p \<Longrightarrow> degree G x \<le> 2" "length p \<ge> 2" "distinct p"
    "walk_betw G u p v" "set p = connected_component G u" "graph_invar G"
  shows "\<And> x. x \<in> set p \<Longrightarrow> degree G x \<ge> 1"
    "\<And> x. \<lbrakk>x \<in> set p; x \<noteq> u; x \<noteq> v\<rbrakk> \<Longrightarrow> degree G x = 2"
    "degree G u = 1 \<longleftrightarrow> degree G v = 1"
proof-
  have dbltn_G: "dblton_graph G"
    by (simp add: assms(6))
  have obtain_e_with_x:"x \<in> set p \<Longrightarrow> \<exists> e. x \<in> e \<and> e \<in> set (edges_of_path p)" for x
    using path_vertex_has_edge[OF assms(2), of x] by auto
  define C where "C = component_edges G (connected_component G u)"
  have e_of_p_in_C: "set (edges_of_path p) \<subseteq> C" 
    using  assms(4,5) 
    by(auto simp add:  C_def dest: walk_between_nonempty_pathD(1) edges_path_subset_edges)
  have degree_p:"x \<in> set p \<Longrightarrow> degree C x \<ge> 1" for x
  proof(goal_cases)
    case 1
    then obtain e where "x \<in> e" "e \<in> set (edges_of_path p)"
      using obtain_e_with_x by auto
    moreover hence "e \<in> C" 
      using  assms(4) e_of_p_in_C path_ball_edges by(auto simp add: walk_betw_def)
    ultimately show ?case 
      by (simp add: degree_Vs vs_member_intro)
  qed
  have p_in_comp_u:"x \<in> set p \<Longrightarrow> x \<in> connected_component G u" for x
    by (simp add: assms(5))
  thus "x \<in> set p \<Longrightarrow> degree G x \<ge> 1" for x
    using p_in_comp_u degree_p  assms(4) degree_Vs in_connected_component_in_edges by fastforce
  have degree_in_p_leq_2: "x \<in> set p \<Longrightarrow> degree C x \<le> 2" for x
    using assms(1)[of x] degree_in_component_is_degree_two_verts[OF dbltn_G p_in_comp_u, of x] 
    by(auto simp add: C_def)
  have inner_verts_deg_2:"\<lbrakk>x \<in> set p; x \<noteq> u; x \<noteq> v\<rbrakk> \<Longrightarrow> degree C x = 2" for x
  proof(goal_cases)
    case 1
    obtain p1 p2 where "p =p1@[x]@p2" 
      using "1"(1) in_set_conv_decomp[of x p] by auto
    then obtain p1 p2 y z where p_split: "p = p1@[y,x,z]@p2"  
      using 1 assms(4)
      by(cases p2, all \<open>cases p1 rule: rev_cases\<close>)(auto simp add: walk_betw_def)
    hence all_different: "y\<noteq>x" "x \<noteq> z" "z\<noteq> y"
      using assms(3) by auto
    have "{y,x} \<in> set (edges_of_path p)" "{x, z} \<in> set (edges_of_path p)"
      using edges_of_path_append_subset by (fastforce simp add: p_split)+
    hence "{y, x} \<in> C" "{x, z} \<in> C" 
      using assms(4) path_ball_edges e_of_p_in_C by auto
    thus ?thesis
      using assms(3) degree_2[of y x C z] p_split assms(1)[of x] 
        degree_in_component_is_degree_two_verts[OF dbltn_G p_in_comp_u, of x]
      by(auto simp add: C_def)
  qed
  thus "\<lbrakk>x \<in> set p; x \<noteq> u; x \<noteq> v\<rbrakk> \<Longrightarrow> degree G x = 2" for x
    using degree_in_component_is_degree_two_verts[OF dbltn_G p_in_comp_u, of x] 
    by(auto simp add: C_def)
  have graph_invar_C:"graph_invar C" 
    using assms(6) component_edges_subset[of G ]  graph_abs_mono[of G C]
    by(auto simp add: graph_abs_def C_def)
  have uv_in_p: "u \<in> set p" "v \<in> set p" 
    using assms(4)
    by (auto simp add: walk_betw_def dest: last_in_set[of p] hd_in_set[of p])
  moreover hence u_neq_v:"u \<noteq> v" 
    using  assms(2,3,4) 
    by(cases p rule: list_cases_both_sides) (auto simp add: walk_betw_def)
  ultimately have Vs_C_is: "Vs C = set p" 
    unfolding C_def using assms(4,2,3) 
    by(subst Vs_of_component_edges_is_component[of v])(auto intro: has_path_in_connected_component simp add: dbltn_G assms(5))
  have length_p_minus_2:"length p -2 = card (set p - {u, v})" 
    using uv_in_p u_neq_v assms(3)
    by(subst card_Diff_insert[of u "set p" "{v}"]) (auto simp add: distinct_card)
  note handshakingC = bigraph_handshaking_lemma[OF graph_invar_C, simplified Vs_C_is]
  moreover have "sum (degree C) (set p) = sum (degree C) (set p - {u, v}) + degree C u + degree C v"
  proof(subst comm_monoid_add_class.sum.remove[of "set p" u "degree C"], goal_cases)
    case 3
    show ?case
    proof(subst comm_monoid_add_class.sum.remove[of "set p - {u}" v "degree C"], goal_cases)
      case 3
      moreover have "set p - {u} - {v} = set p - {u, v}"
        using u_neq_v uv_in_p by auto
      ultimately show ?case
        by(auto simp add: algebra_simps)
    qed (insert  u_neq_v uv_in_p(2), auto)
  qed (auto simp add: uv_in_p(1))
  moreover have "sum (degree C) (set p - {u, v}) = sum (\<lambda> x. 2) (set p - {u, v})"
    by(auto intro!: comm_monoid_add_class.sum.cong[OF refl] simp add: inner_verts_deg_2)
  moreover have "sum (\<lambda> x. 2) (set p - {u, v}) = 2 * (length p -2)"
    by(simp add: length_p_minus_2)
  ultimately have " enat (2 * card C) = 2 * (length p -2) + degree C u + degree C v "
    by (auto simp add: mult_2 mult_2_right of_nat_eq_enat)
  moreover have "degree C u = 1 \<or> degree C u = 2" 
  proof(cases "degree C u", goal_cases)
    case (1 nat)
    moreover have "enat nn + 1 + 1 + 1 \<le> 2  \<Longrightarrow> False" for nn
      by (metis enat_ord_simps(1) iless_Suc_eq le_add2 linorder_not_le one_add_one one_enat_def
          plus_1_eSuc(2) plus_enat_simps(1))
    ultimately show ?case 
      using degree_in_p_leq_2[OF uv_in_p(1)] degree_p[OF uv_in_p(1)] 
      by(cases nat rule: nat_cases_up_to_3 )
        (auto simp add: enat_0 numeral_2_eq_2  eSuc_plus_1 )
  next
    case 2
    then show ?case 
      using degree_in_p_leq_2[OF uv_in_p(1)] by simp
  qed
  moreover have "degree C v = 1 \<or> degree C v = 2" 
  proof(cases "degree C v", goal_cases)
    case (1 nat)
    moreover have "enat nn + 1 + 1 + 1 \<le> 2  \<Longrightarrow> False" for nn
      by (metis enat_ord_simps(1) iless_Suc_eq le_add2 linorder_not_le one_add_one one_enat_def
          plus_1_eSuc(2) plus_enat_simps(1))
    ultimately show ?case 
      using degree_in_p_leq_2[OF uv_in_p(2)] degree_p[OF uv_in_p(2)] 
      by(cases nat rule: nat_cases_up_to_3 )
        (auto simp add: enat_0 numeral_2_eq_2  eSuc_plus_1 )
  next
    case 2
    then show ?case 
      using degree_in_p_leq_2[OF uv_in_p(2)] by simp
  qed
  moreover have "enat (2 * (length p - 2)) + 1 + 2 =  enat (2* (length p -2) + 3)" 
    by (metis add.commute add_numeral_left mult_2 numeral_Bit1_eq_inc_double numeral_One numeral_plus_one
        of_nat_add of_nat_eq_enat one_add_one one_enat_def)
  moreover have "enat (2 * (length p - 2)) + 2 + 1 = enat (2* (length p -2) + 3)"
    by (metis add.assoc calculation(4) one_add_one)
  moreover have "(2 * card C) \<noteq> (2 * (length p - 2) + 3)" 
    by(cases "even (2 * card C)", all \<open>cases "even (2 * (length p - 2) + 3)"\<close>)
      (force+, auto)
  ultimately have "(degree C u = 1) = (degree C v = 1)"
    by auto
  thus "(degree G u = 1) = (degree G v = 1)"
    using degree_in_component_is_degree_two_verts[OF dbltn_G p_in_comp_u, OF uv_in_p(1)] 
      degree_in_component_is_degree_two_verts[OF dbltn_G p_in_comp_u, OF uv_in_p(2)] 
    by(auto simp add: C_def)
qed

subsection \<open>Connected Graphs\<close>

text \<open>Remove connectedness from topological spaces.\<close>
hide_const connected

definition "connected G = (\<forall> u\<in> Vs G. \<forall> v \<in> Vs G. reachable G u v)"

lemma connectedI: "(\<And> u v. \<lbrakk>u \<in> Vs G; v \<in> Vs G\<rbrakk> \<Longrightarrow> reachable G u v) \<Longrightarrow>connected G"
  by(auto simp add: connected_def)

lemma connectedE: "connected G \<Longrightarrow> 
           ((\<And> u v. \<lbrakk>u \<in> Vs G; v \<in> Vs G\<rbrakk> \<Longrightarrow> reachable G u v) \<Longrightarrow>P) \<Longrightarrow> P"
  by(auto simp add: connected_def)

lemma same_comp_connected: 
  "(\<And> u v. \<lbrakk>u \<in> Vs G; v \<in> Vs G\<rbrakk> \<Longrightarrow> connected_component G u = connected_component G v)
    \<Longrightarrow> connected G"
  apply(rule connectedI) 
  subgoal for u v
    apply(rule in_connected_componentE[of v G u])
      apply((insert in_own_connected_component[of v G])[1], blast) 
    by (auto intro: reachable_refl[of v G])
  done  

lemma connected_same_comp: 
  "\<lbrakk>connected G; u \<in> Vs G ; v \<in> Vs G\<rbrakk>
    \<Longrightarrow> connected_component G u = connected_component G v"
  using connected_components_member_eq in_connected_componentI
  by(unfold connected_def) fast

lemma connected_component_one_edge:
  assumes "r \<in> e"  "\<exists> u v. {u,v} = e \<and> u \<noteq> v" 
  shows   "Vs {e} = connected_component {e} r"
proof-
  obtain u v where e_split: "e = {u,v}" "u \<noteq> v"
    using assms(2) by auto
  hence "Vs {e} = {u,v}" 
    by (simp add: Vs_def)
  moreover have "connected_component {e} r = {u,v}"
    using assms(1) e_split(2)  calculation e_split(1) in_connected_component_in_edges
    by (fastforce simp add: e_split(1) in_own_connected_component in_con_comp_insert 
        connected_components_member_sym)
  ultimately show ?thesis by auto
qed

lemma connected_def_via_components:
  "connected G = ((\<forall> v \<in> Vs G. connected_component G v = Vs G))" 
proof(cases "G = {}")
  case True
  then show ?thesis 
    by (auto intro: connectedI vs_member_elim)
next
  case False
  note false = this
  show ?thesis
  proof(cases "G = {{}}")
    case True
    hence "connected G"
      by(auto intro:  connectedI simp add: Vs_def )
    moreover have "Vs G = {}"
      using True by(auto simp add: Vs_def)
    ultimately show ?thesis by auto
  next
    case False 
    then obtain e where "e \<in> G" "e \<noteq> {}"
      using false by blast
    then obtain v where "v \<in> Vs G" 
      by blast
    show ?thesis 
    proof(rule, goal_cases)
      case 1
      then show ?case using  in_connected_component_in_edges  
        by(fastforce elim!: connectedE intro: in_connected_componentI)
    next
      case 2
      then show ?case 
        using connectedE[OF same_comp_connected, of G] 
        by(auto intro!: connectedI)
    qed
  qed
qed
end