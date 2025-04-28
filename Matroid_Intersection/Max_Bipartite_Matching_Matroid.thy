theory Max_Bipartite_Matching_Matroid
  imports RANKING.More_Graph  Matroid_Intersection_Algorithm
 Compute_Path "HOL-Library.Product_Lexorder"
begin

locale max_bimatch_by_matroid_spec=
  fixes Edges :: "'b set"
    and to_dbltn :: "'b \<Rightarrow> 'a set"
    and X :: "'a set"
    and Y :: "'a set"
    and left_vertex :: "'b \<Rightarrow> 'a"
    and right_vertex :: "'b \<Rightarrow> 'a"

locale max_bimatch_by_matroid =
  max_bimatch_by_matroid_spec +
  assumes bipartite_G: "bipartite (to_dbltn `Edges) X Y"
    and     finite_G: "finite Edges"
    and left_vertex: "\<And> e. e \<in> Edges \<Longrightarrow> left_vertex e  \<in> X"
    and right_vertex: "\<And> e. e \<in> Edges \<Longrightarrow> right_vertex e \<in> Y"
    and to_dbltn_vertex: "\<And> e. e \<in> Edges \<Longrightarrow> to_dbltn e = {left_vertex e, right_vertex e}"
    and left_not_right: "\<And> e. e \<in> Edges \<Longrightarrow> left_vertex e \<noteq> right_vertex e "
    and to_dbltn_inj: "inj_on to_dbltn Edges"
    and finite_edges: "finite Edges"
begin

definition "indep1 E = (E \<subseteq> Edges \<and> (\<forall> x \<in> X. (\<forall> e \<in> E. \<forall> d \<in> E. x \<in> to_dbltn d \<longrightarrow> x \<in> to_dbltn e \<longrightarrow> e = d)))"

lemma indep1I: "E \<subseteq> Edges  \<Longrightarrow>
                   (\<And> x e d.  x \<in> X \<Longrightarrow> e \<in> E \<Longrightarrow> d \<in> E \<Longrightarrow> x \<in> to_dbltn d \<Longrightarrow> x \<in> to_dbltn e \<Longrightarrow> e = d) \<Longrightarrow> indep1 E"
  by(auto simp add: indep1_def)

lemma indep1E: "indep1 E \<Longrightarrow> 
                    (E \<subseteq> Edges  \<Longrightarrow>
                   (\<And> x e d.  x \<in> X \<Longrightarrow> e \<in> E \<Longrightarrow> d \<in> E \<Longrightarrow> x \<in> to_dbltn d \<Longrightarrow> x \<in> to_dbltn e \<Longrightarrow> e = d) \<Longrightarrow> P) \<Longrightarrow> P"
  by(auto simp add: indep1_def)

definition "indep2 E = (E \<subseteq> Edges \<and> (\<forall> x \<in> Y. (\<forall> e \<in> E. \<forall> d \<in> E. x \<in> to_dbltn d \<longrightarrow> x \<in> to_dbltn e \<longrightarrow> e = d)))"

lemma indep2I: "E \<subseteq> Edges  \<Longrightarrow>
                   (\<And> x e d.  x \<in> Y \<Longrightarrow> e \<in> E \<Longrightarrow> d \<in> E \<Longrightarrow> x \<in> to_dbltn d \<Longrightarrow> x \<in> to_dbltn e \<Longrightarrow> e = d) \<Longrightarrow> indep2 E"
  by(auto simp add: indep2_def)

lemma indep2E: "indep2 E \<Longrightarrow> 
                    (E \<subseteq> Edges  \<Longrightarrow>
                   (\<And> x e d.  x \<in> Y \<Longrightarrow> e \<in> E \<Longrightarrow> d \<in> E \<Longrightarrow> x \<in> to_dbltn d \<Longrightarrow> x \<in> to_dbltn e \<Longrightarrow> e = d) \<Longrightarrow> P) \<Longrightarrow> P"
  by(auto simp add: indep2_def)

lemma indep1_dbltn: "indep1 E \<Longrightarrow> e \<in> E \<Longrightarrow> d \<in> E \<Longrightarrow> e \<noteq> d \<Longrightarrow> to_dbltn e  \<noteq> to_dbltn d"
  using  left_vertex[of e] left_vertex[of d] to_dbltn_vertex[of e] to_dbltn_vertex[of d]
  by (auto simp add: indep1_def)

lemma indep_system1:"indep_system Edges indep1"
proof(rule indep_system.intro, goal_cases)
  case 1
  then show ?case by(simp add: finite_G)
next
  case (2 X)
  then show ?case 
    by(simp add: indep1_def)
next
  case 3
  then show ?case 
    by(auto intro!: exI[of _ "{}"] simp add: indep1_def)
next
  case (4 X Y)
  show ?case 
    apply(rule indep1E[OF 4(1)])
    using  4(2)by(fastforce intro!: indep1I )
qed

lemma indep_system2:"indep_system Edges indep2"
proof(rule indep_system.intro, goal_cases)
  case 1
  then show ?case by(simp add: finite_G)
next
  case (2 X)
  then show ?case 
    by(simp add: indep2_def)
next
  case 3
  then show ?case 
    by(auto intro!: exI[of _ "{}"] simp add: indep2_def)
next
  case (4 X Y)
  show ?case 
    apply(rule indep2E[OF 4(1)])
    using  4(2)by(fastforce intro!: indep2I)
qed

lemma left_prop:
  assumes "E \<subseteq> Edges" "e \<in> E"
  shows "left_vertex  e \<in> to_dbltn e" "left_vertex e \<in> X"
  using assms(1) assms(2) to_dbltn_vertex  left_vertex by auto

lemma right_prop:
  assumes "E \<subseteq> Edges" "e \<in> E"
  shows "right_vertex  e \<in> to_dbltn e" "right_vertex e \<in> Y"
  using assms(1) assms(2) to_dbltn_vertex  right_vertex by auto

lemma left_inj:
  assumes"indep1 E"
  shows "inj_on (left_vertex) E"
proof(rule inj_onI, goal_cases)
  case (1 e d)
  have EinG: "E \<subseteq> Edges"
    using assms indep1_def by blast
  have "left_vertex  e \<in> to_dbltn e" "left_vertex  e \<in> X"
    "left_vertex  d \<in> to_dbltn d" "left_vertex  d \<in> X"
    using left_prop[OF EinG 1(2)]  left_prop[OF EinG 1(1)]
    by auto
  then show ?case 
    using 1 assms by(auto elim!: indep1E)
qed

lemma x_is_left:"x \<in> to_dbltn e \<Longrightarrow> e \<in> E \<Longrightarrow> E \<subseteq> Edges \<Longrightarrow> x \<in> X \<Longrightarrow> left_vertex e = x" 
  by (meson bipartite_G bipartite_commute bipartite_eqI imageI in_mono max_bimatch_by_matroid.left_prop(1)
      max_bimatch_by_matroid.left_prop(2) max_bimatch_by_matroid_axioms)

lemma x_is_right:"x \<in> to_dbltn e \<Longrightarrow> e \<in> E \<Longrightarrow> E \<subseteq> Edges \<Longrightarrow> x \<in> Y \<Longrightarrow> right_vertex e = x" 
  by (meson bipartite_G bipartite_commute bipartite_eqI
      inj_on_image_mem_iff right_prop(1) right_vertex subset_iff to_dbltn_inj)

lemma right_inj:
  assumes"indep2 E"
  shows "inj_on (right_vertex) E"
proof(rule inj_onI, goal_cases)
  case (1 x y)
  then show ?case 
    using  right_prop(1,2)[of E x]  right_prop(1)[of E y] 
    by(auto intro:  indep2E[OF assms] )
qed

lemma matroid_axioms1: "matroid_axioms indep1"
proof(rule matroid_axioms.intro, goal_cases)
  case (1 E F)
  note one = this
  hence "card (left_vertex ` E) = Suc (card (left_vertex  ` F))"
    by(simp add: card_image[OF left_inj])
  then obtain x where x_prop:"x \<in> left_vertex ` E" "x \<notin> left_vertex  ` F" 
    using Suc_n_not_le_n[of "card (left_vertex  ` F)" ] card_mono[OF finite_imageI[OF indep_system.indep_finite[OF indep_system1  one(2)]]]
      subsetI[of "left_vertex ` E" "left_vertex  ` F" ] 
    by force
  then obtain ee where ee_prop:"ee \<in> E" "left_vertex  ee = x"
    by blast
  moreover hence "ee \<notin> F" 
    using  x_prop(2)
    by(auto simp add: image_iff)
  ultimately have ee_in:"ee \<in> E - F" by auto
  moreover have "indep1 ({ee} \<union> F)"
  proof(rule indep1I, goal_cases)
    case 1
    then show ?case 
      using \<open>ee \<in> E\<close> indep_system.indep_subset_carrier indep_system1 one(1) one(2) by blast
  next
    case (2 y e d)
    show ?case 
    proof(cases "ee = e")
      case True
      note true = this
      show ?thesis 
      proof(cases "ee = d")
        case True
        then show ?thesis 
          using true by simp
      next
        case False
        moreover have "y =x" 
          using "2"(1) "2"(5) ee_prop(1) ee_prop(2) indep1E[OF one(1)] true x_is_left
          by blast
        ultimately show ?thesis 
          using true 2  x_is_left x_prop(2)
          by(force intro: indep1E[OF one(2)] simp add: image_iff)
      qed
    next
      case False
      note false = this
      show ?thesis 
      proof(cases "ee = d")
        case True
        then show ?thesis  
          using false 2  x_is_left x_prop(2) ee_prop one 
          by (auto simp add: indep1_def)
      next
        case False
        thus ?thesis
          using 2 false indep1_def one(2) by force
      qed
    qed
  qed
  ultimately show ?case 
    by(auto intro: bexI[of _ x])
qed

lemma  max_bimatch_by_matroid_commuted:"max_bimatch_by_matroid Edges to_dbltn Y X right_vertex left_vertex" 
  using bipartite_G bipartite_commute  left_not_right 
  by(force intro!: max_bimatch_by_matroid.intro  right_vertex left_vertex
      simp add:  finite_edges to_dbltn_inj  to_dbltn_vertex)  


lemma matroid_axioms2: "matroid_axioms indep2"
  using max_bimatch_by_matroid.matroid_axioms1[OF max_bimatch_by_matroid_commuted]
  by(unfold max_bimatch_by_matroid.indep1_def[OF max_bimatch_by_matroid_commuted] indep2_def)

interpretation double_matroid_concrete: double_matroid Edges indep1 indep2
  by(auto intro!: double_matroid.intro matroid.intro indep_system1 indep_system2 matroid_axioms1 matroid_axioms2)

thm double_matroid_concrete.A1_def

term double_matroid_concrete.matroid1.the_circuit

lemma double_matroid_concrete: "double_matroid Edges indep1 indep2"
  by (simp add: double_matroid_concrete.double_matroid_axioms)

lemma in_dependent1_is: assumes "\<not> indep1 E"  "E \<subseteq> Edges"
  shows "\<exists> e d x. e \<in> E \<and> d \<in> E \<and> e \<noteq> d \<and> to_dbltn e \<inter> to_dbltn d \<inter> X = {x}"
proof(cases "inj_on left_vertex E")
  case True
  hence False
    using assms(1) x_is_left[OF _ _ assms(2)]
    by (simp add: assms(2) indep1_def inj_on_def )
  then show ?thesis by simp
next
  case False
  then obtain e d where ed: "e \<in> E" "d \<in> E" "left_vertex e = left_vertex d" "e \<noteq> d"
    by (meson inj_on_def)
  moreover hence "left_vertex e \<in> X"
    using left_prop[OF assms(2) ed(1)] left_prop[OF assms(2) ed(2)] by auto
  moreover hence "to_dbltn e \<inter> to_dbltn d \<inter> X = {left_vertex e}" 
  proof-
    have "left_vertex e \<in> to_dbltn e \<inter> to_dbltn d"
      using  left_prop[OF assms(2) ed(1)] left_prop[OF assms(2) ed(2)] ed(3) by simp
    moreover obtain e1 e2 where "to_dbltn e = {e1, e2}" "e1 \<noteq> e2" 
      using assms(2) ed(1) 
      by (simp add: left_not_right subset_eq to_dbltn_vertex)
    moreover obtain d1 d2 where "to_dbltn d = {d1, d2}" "d1 \<noteq> d2" 
      using assms(2) ed(2)
      by (simp add: left_not_right subset_eq to_dbltn_vertex)
    moreover have "right_vertex e \<notin> X" 
      using assms(2) calculation(2) calculation(3) 
        doubleton_eq_iff ed(1)   to_dbltn_vertex[of e] x_is_left[of e1] 
        x_is_left[of e2] by fast
    moreover have "to_dbltn e = {left_vertex e, right_vertex e}"
      using assms(2) ed(1) to_dbltn_vertex by auto
    moreover have "to_dbltn d = {left_vertex d, right_vertex d}"
      using assms(2) ed(2) to_dbltn_vertex by auto
    ultimately show ?thesis
    proof -
      have "to_dbltn e \<noteq> {left_vertex e, right_vertex e} \<or> to_dbltn e \<inter> (to_dbltn e \<inter> to_dbltn d) = {left_vertex e, right_vertex e} \<inter> (to_dbltn e \<inter> to_dbltn d)"
        by presburger
      thus ?thesis 
        using \<open>left_vertex e \<in> X\<close> 
          \<open>left_vertex e \<in> to_dbltn e \<inter> to_dbltn d\<close> \<open>right_vertex e \<notin> X\<close>
          \<open>to_dbltn e = {left_vertex e, right_vertex e}\<close> by blast
    qed
  qed
  thus ?thesis
    using ed(1) ed(2) ed(4) by blast
qed

lemma in_dependent2_is: assumes "\<not> indep2 E"  "E \<subseteq> Edges"
  shows "\<exists> e d x. e \<in> E \<and> d \<in> E \<and> e \<noteq> d \<and> to_dbltn e \<inter> to_dbltn d \<inter> Y = {x}"
  using assms(1) assms(2) max_bimatch_by_matroid.in_dependent1_is[OF max_bimatch_by_matroid_commuted]
  by(simp add: indep2_def  max_bimatch_by_matroid.indep1_def[OF max_bimatch_by_matroid_commuted])

lemma circuit1_is:
  assumes "double_matroid_concrete.matroid1.circuit E" 
  obtains x e d where "E = {e, d}"  "e \<noteq> d" "e \<in> Edges" "d \<in> Edges" "to_dbltn d \<inter> to_dbltn e \<inter> X = {x}" 
proof(goal_cases)
  case 1
  have a1: "\<not> indep1 E" "E \<subseteq> Edges"
    by (auto simp add: assms double_matroid_concrete.matroid1.circuit_dep
        double_matroid_concrete.matroid1.circuitD(1))
  obtain e d x where edx:"e \<in> E" "d \<in> E" "e \<noteq> d" "to_dbltn e \<inter> to_dbltn d \<inter> X = {x}"
    using in_dependent1_is[OF a1] by auto
  have "E = {e, d}"
  proof(rule ccontr)
    assume "E \<noteq> {e, d}"
    hence "{e, d} \<subset> E" 
      by (simp add: edx(1) edx(2) psubsetI)
    moreover then obtain f where "f \<in> E" "f \<notin> {e, d}" by auto
    ultimately have "{e, d} \<subseteq> E - {f}" by auto
    moreover have "\<not> indep1 {e, d}"
      using edx(3) edx(4) 
      by(auto simp add: indep1_def)
    ultimately have "\<not> indep1 (E - {f})"
      using double_matroid_concrete.matroid1.indep_subset by blast
    moreover have "indep1 (E - {f})" 
      using \<open>f \<in> E\<close> assms double_matroid_concrete.matroid1.circuit_in_def
        double_matroid_concrete.matroid1.circuit_min_dep by force
    ultimately show False by simp
  qed
  then show thesis
    using a1(2) edx
    by (intro 1[of e d x]) auto
qed

lemma circuit2_is:
  assumes "double_matroid_concrete.matroid2.circuit E" 
  obtains x e d where "E = {e, d}"  "e \<noteq> d" "e \<in> Edges" "d \<in> Edges" "to_dbltn d \<inter> to_dbltn e \<inter> Y = {x}" 
  using max_bimatch_by_matroid.circuit1_is[OF max_bimatch_by_matroid_commuted, of E thesis] assms
  by(unfold double_matroid_concrete.matroid2.circuit_def
      indep_system.circuit_def[OF max_bimatch_by_matroid.indep_system1[OF max_bimatch_by_matroid_commuted]]
      max_bimatch_by_matroid.indep1_def[OF max_bimatch_by_matroid_commuted]
      indep2_def) fast

lemma circuit1_card2:
  assumes "double_matroid_concrete.matroid1.circuit E" 
  shows "card E = 2"
proof(rule circuit1_is[OF assms], goal_cases)
  case (1 x e d)
  then show ?case by simp
qed

lemma circuit2_card2:
  assumes "double_matroid_concrete.matroid2.circuit E" 
  shows "card E = 2"
proof(rule circuit2_is[OF assms], goal_cases)
  case (1 x e d)
  then show ?case by simp
qed

lemma graph_matching_to_double_indep:
  assumes "graph_matching (to_dbltn ` Edges) M" 
  shows "\<exists> M_impl. M = to_dbltn ` M_impl  \<and> indep1 M_impl \<and> indep2 M_impl"
proof-
  have "M \<subseteq> to_dbltn ` Edges"
    by (simp add: assms)
  then obtain M_impl where M_impl_is: "M_impl \<subseteq> Edges" "to_dbltn ` M_impl  = M" 
    by(auto intro: subset_imageE)
  moreover have "indep1 M_impl"
    using M_impl_is assms
    by(auto intro!: indep1I  inj_onD[OF to_dbltn_inj]  simp add: matching_def  disjoint_iff)
  moreover have "indep2 M_impl"
    using M_impl_is assms
    by(auto intro!: indep2I  inj_onD[OF to_dbltn_inj]  simp add: matching_def  disjoint_iff)
  ultimately show ?thesis by auto
qed

lemma double_indep_to_graph_matching: 
  assumes "indep1 M" "indep2 M"
  shows   "graph_matching (to_dbltn ` Edges) (to_dbltn ` M)"
proof-
  have M_in_Edges:"M \<subseteq> Edges"
    using assms
    by(auto simp add: indep1_def indep2_def)
  hence "to_dbltn ` M \<subseteq> to_dbltn ` Edges" 
    using assms
    by(auto simp add: indep1_def indep2_def)
  moreover have "e1\<in>to_dbltn ` M \<Longrightarrow> e2\<in>to_dbltn ` M \<Longrightarrow> e1 \<noteq> e2 \<Longrightarrow> e1 \<inter> e2 = {}" for e1 e2
  proof(goal_cases)
    case 1
    then obtain e1_impl e2_impl where eds_impl:  "e1_impl \<in> M" "to_dbltn e1_impl = e1"
      "e2_impl \<in> M" "to_dbltn e2_impl = e2" by auto
    hence es_not_Eq:"e1_impl \<noteq> e2_impl" 
      using "1"(3) by fastforce
    have "{left_vertex e2_impl, right_vertex e2_impl} \<inter> 
                         {left_vertex e1_impl, right_vertex e1_impl} = {}"
      apply(rule indep1E[OF assms(1)])
      using  es_not_Eq eds_impl  left_prop(1,2)[OF M_in_Edges, of e1_impl] 
        right_prop(1)[OF M_in_Edges, of e2_impl] left_prop(1,2)[OF M_in_Edges, of e2_impl] 
        right_prop(1)[OF M_in_Edges, of e1_impl] 
      by(force dest:  inj_on_contraD[OF left_inj[OF assms(1)]]
          inj_on_contraD[OF right_inj[OF assms(2)]])+
    hence "to_dbltn e2_impl \<inter> to_dbltn e1_impl = {}"
      using M_in_Edges eds_impl(3,1)
      by(subst to_dbltn_vertex, auto simp add: to_dbltn_vertex)
    thus ?thesis
      by (simp add: Int_commute eds_impl(2) eds_impl(4))
  qed
  ultimately show?thesis 
    by(auto simp add: matching_def)
qed

thm double_matroid.maximum_characterisation[OF double_matroid_concrete]
end

datatype ('e, 'v) matching_set = MATCH 
  (edges: "('e \<times> color) tree")
  (on_left: "(('v \<times> ('e \<times> color) tree) \<times> color) tree")  
  (on_right: "(('v \<times> ('e \<times> color) tree) \<times> color) tree")

definition "map_empty' = (Leaf:: (('a \<times> ('b \<times> color) tree) \<times> color) tree)"

locale compute_max_bimatch_by_matroid_spec = 
  max_bimatch_by_matroid_spec
  where Edges = Edges and X = X and Y =Y and to_dbltn = to_dbltn
    and left_vertex = left_vertex and right_vertex = right_vertex

for Edges::"('e::linorder) set" and X::"('v::linorder) set" and Y::"'v set" 
  and to_dbltn::"'e \<Rightarrow> 'v set" and
  left_vertex::"'e \<Rightarrow> 'v" and right_vertex::"'e \<Rightarrow> 'v"
  + fixes Edges_impl::"('e \<times> color) tree"
begin

definition "the_edges mp v = (case (lookup mp v) of None \<Rightarrow> vset_empty | Some es \<Rightarrow> es)"

definition "empty_matching = MATCH vset_empty map_empty' map_empty'"
definition "insert_matching (e::'e) M= 
              (case M of (MATCH edgs lft rht) \<Rightarrow> 
              MATCH (vset_insert e edgs) 
                    (let x =  (left_vertex e) in
                      update x (vset_insert e (the_edges lft x)) lft) 
                    (let y =  (right_vertex e) in
                      update y (vset_insert e (the_edges rht y)) rht))"

definition "delete_matching (e::'e) M= 
              (case M of (MATCH edgs lft rht) \<Rightarrow> 
              MATCH (vset_delete e edgs) 
                    (let x =  (left_vertex e);
                         new_es = (vset_delete e (the_edges lft x)) in
                        (if new_es = vset_empty then delete x lft else
                          update x new_es lft)) 
                    (let y =  (right_vertex e) ;
                           new_es = (vset_delete e (the_edges rht y)) in
                          (if new_es = vset_empty then delete y rht else
                              update y new_es rht)))"
definition "set_matching M = t_set (edges M)"

definition "emap_lft_inv mp = (adj_inv mp \<and> 
       (\<forall> x. lookup mp x \<noteq> None \<longrightarrow> vset_inv (the (lookup mp x))) \<and>
       (\<forall> x e. (lookup mp x \<noteq> None \<and> e \<in> t_set (the (lookup mp x)))
                  \<longrightarrow> left_vertex e = x))"

definition "emap_rht_inv mp = (adj_inv mp \<and> 
       (\<forall> x. lookup mp x \<noteq> None \<longrightarrow> vset_inv (the (lookup mp x))) \<and>
       (\<forall> x e. (lookup mp x \<noteq> None \<and> e \<in> t_set (the (lookup mp x)))
                  \<longrightarrow> right_vertex e = x))"

fun invar_matching where
  "invar_matching (MATCH eds lft rht) = 
(vset_inv eds \<and> emap_lft_inv lft \<and> emap_rht_inv rht \<and>
 (\<exists> E. E = t_set eds \<and> E = {e | e. \<exists> x. lookup lft x \<noteq> None \<and> e \<in> t_set (the (lookup lft x))}
               \<and> E = {e | e. \<exists> x. lookup rht x \<noteq> None \<and> e \<in> t_set (the (lookup rht x))}))"

lemma invar_matching_alt_def:
  "invar_matching (MATCH eds lft rht) = 
(vset_inv eds \<and> emap_lft_inv lft \<and> emap_rht_inv rht 
 \<and> t_set eds = {e | e. \<exists> x. lookup rht x \<noteq> None \<and> e \<in> t_set (the (lookup rht x))}
\<and>  t_set eds = {e | e. \<exists> x. lookup lft x \<noteq> None \<and> e \<in> t_set (the (lookup lft x))})"
  by auto

lemma on_left_left_vertex: "invar_matching M \<Longrightarrow> e \<in> t_set (the_edges (on_left M) x) \<Longrightarrow> left_vertex e = x"
proof(induction M)
  case (MATCH x1a x2a x3a)
  then show ?case 
    by(cases "lookup x2a x")
      (auto simp add:  emap_lft_inv_def the_edges_def dfs.Graph.vset.set.set_empty)
qed

lemma on_right_right_vertex: "invar_matching M \<Longrightarrow> e \<in> t_set (the_edges (on_right M) x) \<Longrightarrow> right_vertex e = x"
proof(induction M)
  case (MATCH x1a x2a x3a)
  then show ?case 
    by(cases "lookup x3a x")
      (auto simp add:  emap_rht_inv_def the_edges_def dfs.Graph.vset.set.set_empty)
qed

lemma on_left_in_M: "invar_matching M \<Longrightarrow> e \<in> t_set (the_edges (on_left M) x) \<Longrightarrow> e \<in> set_matching M"
proof(induction M)
  case (MATCH x1a x2a x3a)
  then show ?case 
    by(cases "lookup x2a x")
      (auto simp add:  emap_lft_inv_def the_edges_def dfs.Graph.vset.set.set_empty set_matching_def)
qed

lemma on_right_in_M: "invar_matching M \<Longrightarrow> e \<in> t_set (the_edges (on_right M) x) \<Longrightarrow> e \<in> set_matching M"
proof(induction M)
  case (MATCH x1a x2a x3a)
  then show ?case 
    by(cases "lookup x3a x")
      (auto simp add:  emap_rht_inv_def the_edges_def dfs.Graph.vset.set.set_empty set_matching_def
        simp del: invar_matching.simps simp add: invar_matching_alt_def)

qed

lemma set_matching_empty: "invar_matching empty_matching"
  "set_matching empty_matching = {}"
  using M.map_specs(4) 
  by(auto simp add: empty_matching_def map_empty'_def emap_lft_inv_def emap_rht_inv_def
      RBT_Set.empty_def adj_inv_def set.invar_empty set_matching_def)

lemma set_matching_insert: assumes "invar_matching  M"
  shows "invar_matching (insert_matching x M)" (is ?thesis)
    and  "set_matching (insert_matching x M) = set_matching M \<union> {x}" (is ?thesis2)
  using assms
proof(induction M, unfold insert_matching_def matching_set.case invar_matching.simps, goal_cases)
  case (1 eds lft rht)
  hence from_invar: "vset_inv eds" "emap_lft_inv lft""emap_rht_inv rht"
    "\<And> e. e \<in>  t_set eds \<longleftrightarrow> (\<exists>x. lookup lft x \<noteq> None \<and> e \<in> t_set (the (lookup lft x)))"
    "\<And> e. e \<in>  t_set eds \<longleftrightarrow> (\<exists>x. lookup rht x \<noteq> None \<and> e \<in> t_set (the (lookup rht x)))"
    by(auto, force, force)
  hence minvar_lft:"M.invar lft" and minvar_rht:"M.invar rht"
    by (auto simp add: adj_inv_def emap_lft_inv_def emap_rht_inv_def)
  have goal1:"vset_inv (vset_insert x eds)"
    by (simp add: from_invar(1))
  have goal2:"emap_lft_inv (let xa = left_vertex x in update xa (vset_insert x (the_edges lft xa)) lft)"
    using from_invar(2) using RBT.set_tree_insert[of _  x] 
    by(force intro:  Map.invar_update[OF  M.Map_axioms] split: option.split 
        simp add: emap_lft_inv_def adj_inv_def the_edges_def Map.map_update[OF  M.Map_axioms]
        dfs.Graph.vset.set.invar_empty RBT_Set.empty_def vset_inv_def  RBT.inv_insert RBT.bst_insert)
  have goal3:"emap_rht_inv (let xa = right_vertex x in update xa (vset_insert x (the_edges rht xa)) rht)"
    using from_invar(3) using RBT.set_tree_insert[of _  x] 
    by(force intro:  Map.invar_update[OF  M.Map_axioms] split: option.split 
        simp add: emap_rht_inv_def adj_inv_def the_edges_def Map.map_update[OF  M.Map_axioms]
        dfs.Graph.vset.set.invar_empty RBT_Set.empty_def vset_inv_def  RBT.inv_insert RBT.bst_insert)
  have goal4:" e \<in> t_set (vset_insert x eds) \<longleftrightarrow>
         (\<exists>xa. lookup (let xa = left_vertex x in update xa (vset_insert x (the_edges lft xa)) lft) xa \<noteq>
                None \<and>
                e \<in> t_set
                      (the (lookup
                             (let xa = left_vertex x in update xa (vset_insert x (the_edges lft xa)) lft)
                             xa)))" for e
  proof-
    have g1:"lookup lft (left_vertex x) = None \<Longrightarrow>
    e \<in> t_set eds \<Longrightarrow>
    \<exists>xa. xa \<noteq> left_vertex x \<and>
         (xa \<noteq> left_vertex x \<longrightarrow> (\<exists>y. lookup lft xa = Some y) \<and> e \<in> t_set (the (lookup lft xa)))"
      using from_invar(4)[of e]  not_Some_eq[of " lookup lft _"] by metis
    have g2: "\<And>xa y.  e \<in> t_set y \<Longrightarrow> lookup lft xa = Some y \<Longrightarrow> e \<in> t_set eds"
      using from_invar(4) by auto
    have g3: "\<And>a. lookup lft (left_vertex x) = Some a \<Longrightarrow>
         \<exists>xa. (xa = left_vertex x \<longrightarrow> x \<in> t_set (vset_insert x a)) \<and>
              (xa \<noteq> left_vertex x \<longrightarrow> (\<exists>y. lookup lft xa = Some y) \<and> x \<in> t_set (the (lookup lft xa)))"
      using dfs.Graph.vset.set.set_insert  from_invar(2) 
      by(force simp add: emap_lft_inv_def )
    have g4: "\<And>a. lookup lft (left_vertex x) = Some a \<Longrightarrow>
         e \<in> t_set eds \<Longrightarrow>
         \<exists>xa. (xa = left_vertex x \<longrightarrow> e \<in> t_set (vset_insert x a)) \<and>
              (xa \<noteq> left_vertex x \<longrightarrow> (\<exists>y. lookup lft xa = Some y) \<and> e \<in> t_set (the (lookup lft xa)))"
      using Un_iff dfs.Graph.vset.set.set_insert 
        emap_lft_inv_def from_invar(2) from_invar(4) option.collapse option.sel
      by metis
    have g6: " \<And>a. lookup lft (left_vertex x) = Some a \<Longrightarrow>
         e \<noteq> x \<Longrightarrow> e \<in> t_set (vset_insert x a) \<Longrightarrow> e \<notin> t_set eds \<Longrightarrow> False" 
      by (metis RBT.set_tree_insert emap_lft_inv_def from_invar(2) from_invar(4)
          insert_iff insert_is_Un option.distinct(1) option.sel vset_inv_def)
    show ?thesis
      using g6 by (subst set.set_insert, all \<open>cases "lookup lft (left_vertex x)"\<close>, all \<open>cases "e = x"\<close>,
          auto simp add:  from_invar(1) the_edges_def M.map_update[OF minvar_lft] 
          set.set_insert[OF dfs.Graph.vset.set.invar_empty]
          dfs.Graph.vset.set.set_empty emap_lft_inv_def 
          intro: g1 g2 g3 g4 g6)
  qed
  have goal5:" e \<in> t_set (vset_insert x eds) \<longleftrightarrow>
         (\<exists>xa. lookup (let xa = right_vertex x in update xa (vset_insert x (the_edges rht xa)) rht) xa \<noteq>
                None \<and>
                e \<in> t_set
                      (the (lookup
                             (let xa = right_vertex x in update xa (vset_insert x (the_edges rht xa)) rht)
                             xa)))" for e
  proof-
    have g1:"lookup rht (right_vertex x) = None \<Longrightarrow>
    e \<in> t_set eds \<Longrightarrow>
    \<exists>xa. xa \<noteq> right_vertex x \<and>
         (xa \<noteq> right_vertex x \<longrightarrow> (\<exists>y. lookup rht xa = Some y) \<and> e \<in> t_set (the (lookup rht xa)))"
      using from_invar(5)[of e]  not_Some_eq[of " lookup rht _"] by metis
    have g2: "\<And>xa y.  e \<in> t_set y \<Longrightarrow> lookup rht xa = Some y \<Longrightarrow> e \<in> t_set eds"  
      using from_invar(5) by auto
    have g3: "\<And>a. lookup rht (right_vertex x) = Some a \<Longrightarrow>
         \<exists>xa. (xa = right_vertex x \<longrightarrow> x \<in> t_set (vset_insert x a)) \<and>
              (xa \<noteq> right_vertex x \<longrightarrow> (\<exists>y. lookup rht xa = Some y) \<and> x \<in> t_set (the (lookup rht xa)))"
      using dfs.Graph.vset.set.set_insert  from_invar(3) 
      by(force simp add: emap_rht_inv_def )
    have g4: "\<And>a. lookup rht (right_vertex x) = Some a \<Longrightarrow>
         e \<in> t_set eds \<Longrightarrow>
         \<exists>xa. (xa = right_vertex x \<longrightarrow> e \<in> t_set (vset_insert x a)) \<and>
              (xa \<noteq> right_vertex x \<longrightarrow> (\<exists>y. lookup rht xa = Some y) \<and> e \<in> t_set (the (lookup rht xa)))"
      using Un_iff dfs.Graph.vset.set.set_insert 
        emap_rht_inv_def from_invar(3) from_invar(5) option.collapse option.sel
      by metis
    have g6: " \<And>a. lookup rht (right_vertex x) = Some a \<Longrightarrow>
         e \<noteq> x \<Longrightarrow> e \<in> t_set (vset_insert x a) \<Longrightarrow> e \<notin> t_set eds \<Longrightarrow> False" 
      by (metis RBT.set_tree_insert emap_rht_inv_def from_invar(3) from_invar(5)
          insert_iff insert_is_Un option.distinct(1) option.sel vset_inv_def)
    show ?thesis
      using g6  by (subst set.set_insert, all \<open>cases "lookup rht (right_vertex x)"\<close>, all \<open>cases "e = x"\<close>,
          auto simp add:  from_invar(1) the_edges_def M.map_update[OF minvar_rht] 
          set.set_insert[OF dfs.Graph.vset.set.invar_empty]
          dfs.Graph.vset.set.set_empty emap_rht_inv_def 
          intro: g1 g2 g3 g4  g6)
  qed
  show ?case 
    using goal4 goal5 by (fastforce intro: goal3 goal2 goal1)
qed (simp add: set_matching_def)

lemma set_matching_delete: assumes "invar_matching  M"
  shows "invar_matching (delete_matching x M)" (is ?thesis)
    and  "set_matching (delete_matching x M) = set_matching M - {x}" (is ?thesis2)
  using assms
proof(induction M, unfold delete_matching_def matching_set.case invar_matching.simps, goal_cases)
  case (1 eds lft rht)
  hence from_invar: "vset_inv eds" "emap_lft_inv lft""emap_rht_inv rht"
    "\<And> e. e \<in>  t_set eds \<longleftrightarrow> (\<exists>x. lookup lft x \<noteq> None \<and> e \<in> t_set (the (lookup lft x)))"
    "\<And> e. e \<in>  t_set eds \<longleftrightarrow> (\<exists>x. lookup rht x \<noteq> None \<and> e \<in> t_set (the (lookup rht x)))"
    by(auto, force, force)
  hence minvar_lft:"M.invar lft" and minvar_rht:"M.invar rht"
    by (auto simp add: adj_inv_def emap_lft_inv_def emap_rht_inv_def)
  have goal1:"vset_inv (vset_delete x eds)"
    by (simp add: from_invar(1))
  have goal2:" emap_lft_inv
           (let xa = left_vertex x; new_es = vset_delete x (the_edges lft xa)
           in if new_es = vset_empty then RBT_Map.delete xa lft else update xa new_es lft)"
    using from_invar(2) 
    by(auto simp add: emap_lft_inv_def adj_inv_def minvar_lft  M.invar_delete[OF minvar_lft] 
        M.map_specs(3)[OF minvar_lft]  M.map_update[OF minvar_lft] the_edges_def  
        dfs.Graph.vset.set.invar_empty RBT_Set.empty_def option.case_eq_if
        intro: Map.invar_update[OF M.Map_axioms] minvar_lft  M.invar_delete[OF minvar_lft]
        option.exhaust[of "lookup lft (left_vertex x) "])
  have goal3:"emap_rht_inv
     (let y = right_vertex x; new_es = vset_delete x (the_edges rht y)
      in if new_es = vset_empty then RBT_Map.delete y rht else update y new_es rht)"
    using from_invar(3) 
    by(auto simp add: emap_rht_inv_def adj_inv_def minvar_rht  M.invar_delete[OF minvar_rht] 
        M.map_specs(3)[OF minvar_rht]  M.map_update[OF minvar_rht] the_edges_def  
        dfs.Graph.vset.set.invar_empty RBT_Set.empty_def option.case_eq_if
        intro: Map.invar_update[OF M.Map_axioms] minvar_lft  M.invar_delete[OF minvar_lft]
        option.exhaust[of "lookup lft (left_vertex x) "])
  have g1: "vset_delete x (the_edges lft (left_vertex x)) = vset_empty \<Longrightarrow>
          xa \<in> t_set (vset_delete x eds) \<Longrightarrow>
          \<exists>xb. (\<exists>y. lookup (RBT_Map.delete (left_vertex x) lft) xb = Some y) \<and>
               xa \<in> t_set (the (lookup (RBT_Map.delete (left_vertex x) lft) xb))" for xa
    unfolding the_edges_def
  proof(cases "lookup lft (left_vertex x)", goal_cases)
    case 1
    moreover then obtain x where x_prop:"lookup lft x \<noteq> None" "xa \<in> t_set (the (lookup lft x))"
      using from_invar(4)[of xa] by(auto simp add: set.set_delete[OF from_invar(1)])
    ultimately show ?case
      using M.map_delete[OF minvar_lft] from_invar(2)[simplified emap_lft_inv_def]        
      by (auto intro!:  exI[of _ x] simp add:  set.set_delete[OF from_invar(1)] M.map_delete[OF minvar_lft])
  next
    case (2 a)
    then obtain xx where x_prop:"lookup lft xx \<noteq> None" "xa \<in> t_set (the (lookup lft xx))"
      using from_invar(4)[of xa] by(auto simp add: set.set_delete[OF from_invar(1)])
    then obtain y where y_prop:" lookup lft xx = Some y" by auto
    hence aa:"vset_inv (the (lookup lft xx))"
      using  from_invar(2)[simplified emap_lft_inv_def]  x_prop(1) x_prop(2)
      by blast
    show ?case using 2 y_prop  Diff_insert0  dfs.Graph.vset.set.set_delete[of "the (lookup lft xx)", OF aa, of x]  x_prop(1) x_prop(2) 
      by(auto simp add: M.map_delete[OF minvar_lft, of "left_vertex x"] RBT_Set.empty_def 
          set.set_delete[OF from_invar(1)] intro!: exI[of _ xx])
  qed
  have g2:"vset_delete x (the_edges rht (right_vertex x)) = vset_empty \<Longrightarrow>
          xa \<in> t_set (vset_delete x eds) \<Longrightarrow>
          \<exists>xb. (\<exists>y. lookup (RBT_Map.delete (right_vertex x) rht) xb = Some y) \<and>
               xa \<in> t_set (the (lookup (RBT_Map.delete (right_vertex x) rht) xb))" for xa
    unfolding the_edges_def
  proof(cases "lookup rht (right_vertex x)", goal_cases)
    case 1
    moreover then obtain x where x_prop:"lookup rht x \<noteq> None" "xa \<in> t_set (the (lookup rht x))"
      using from_invar(5)[of xa] by(auto simp add: set.set_delete[OF from_invar(1)])
    ultimately show ?case
      using M.map_delete[OF minvar_rht] from_invar(3)[simplified emap_rht_inv_def]        
      by (auto intro!:  exI[of _ x] simp add:  set.set_delete[OF from_invar(1)] M.map_delete[OF minvar_lft])
  next
    case (2 a)
    then obtain xx where x_prop:"lookup rht xx \<noteq> None" "xa \<in> t_set (the (lookup rht xx))"
      using from_invar(5)[of xa] by(auto simp add: set.set_delete[OF from_invar(1)])
    then obtain y where y_prop:" lookup rht xx = Some y" by auto
    hence aa:"vset_inv (the (lookup rht xx))"
      using  from_invar(3)[simplified emap_rht_inv_def]  x_prop(1) x_prop(2)
      by blast
    show ?case using 2 y_prop  Diff_insert0  dfs.Graph.vset.set.set_delete[of "the (lookup rht xx)", OF aa, of x]  x_prop(1) x_prop(2) 
      by(auto simp add: M.map_delete[OF minvar_rht, of "right_vertex x"] RBT_Set.empty_def 
          set.set_delete[OF from_invar(1)] intro!: exI[of _ xx])
  qed
  have g3: "vset_delete x (the_edges lft (left_vertex x)) = vset_empty \<Longrightarrow>
       xa \<in> t_set y \<Longrightarrow>
       lookup (RBT_Map.delete (left_vertex x) lft) xaa = Some y \<Longrightarrow> xa \<in> t_set (vset_delete x eds)" for xa xaa y
    unfolding the_edges_def
  proof(cases "lookup lft (left_vertex x)", goal_cases)
    case 1
    moreover hence "lookup lft xaa \<noteq> None" "xa \<in> t_set (the (lookup lft xaa))" "left_vertex xa = xaa"
      using  from_invar(2)[simplified emap_lft_inv_def]  fun_upd_triv[of "lookup lft" "left_vertex x"] 
      by(unfold M.map_delete[OF minvar_lft, of "left_vertex x"]  1(4)) auto
    ultimately show ?thesis 
      by(auto simp add: dfs.Graph.vset.set.set_delete[OF from_invar(1)]
          M.map_delete[OF minvar_lft, of "left_vertex x"] from_invar(4)[of xa])
  next
    case (2 a)
    moreover hence "lookup lft xaa \<noteq> None" "xa \<in> t_set (the (lookup lft xaa))" "left_vertex xa = xaa"
      using  from_invar(2)[simplified emap_lft_inv_def] 
      by(unfold M.map_delete[OF minvar_lft, of "left_vertex x"], all \<open>cases "left_vertex x = xaa"\<close>) 
        auto
    ultimately show ?thesis 
      using  from_invar(4)
      by(auto simp add: dfs.Graph.vset.set.set_delete[OF from_invar(1)] M.map_delete[OF minvar_lft]) 
  qed
  have g4: "vset_delete x (the_edges rht (right_vertex x)) = vset_empty \<Longrightarrow>
       xa \<in> t_set y \<Longrightarrow>
       lookup (RBT_Map.delete (right_vertex x) rht) xaa = Some y \<Longrightarrow> xa \<in> t_set (vset_delete x eds)" for xa xaa y
    unfolding the_edges_def
  proof(cases "lookup rht (right_vertex x)", goal_cases)
    case 1
    moreover hence "lookup rht xaa \<noteq> None" "xa \<in> t_set (the (lookup rht xaa))" "right_vertex xa = xaa"
      using  from_invar(3)[simplified emap_rht_inv_def]  fun_upd_triv[of "lookup rht" "right_vertex x"] 
      by(unfold M.map_delete[OF minvar_rht, of "right_vertex x"]  1(4)) auto
    ultimately show ?thesis 
      by(auto simp add: dfs.Graph.vset.set.set_delete[OF from_invar(1)]
          M.map_delete[OF minvar_lft, of "right_vertex x"] from_invar(5)[of xa])
  next
    case (2 a)
    moreover hence "lookup rht xaa \<noteq> None" "xa \<in> t_set (the (lookup rht xaa))" "right_vertex xa = xaa"
      using  from_invar(3)[simplified emap_rht_inv_def] 
      by(unfold M.map_delete[OF minvar_rht, of "right_vertex x"], all \<open>cases "right_vertex x = xaa"\<close>) 
        auto
    ultimately show ?thesis 
      using  from_invar(5)
      by(auto simp add: dfs.Graph.vset.set.set_delete[OF from_invar(1)] M.map_delete[OF minvar_rht]) 
  qed
  have g5: "vset_delete x (the_edges rht (right_vertex x)) \<noteq> vset_empty \<Longrightarrow>
          xa \<in> t_set (vset_delete x eds) \<Longrightarrow>
          \<exists>xb. (\<exists>y. lookup (update (right_vertex x) (vset_delete x (the_edges rht (right_vertex x))) rht) xb =
                    Some y) \<and>
               xa \<in> t_set
                      (the (lookup
                             (update (right_vertex x) (vset_delete x (the_edges rht (right_vertex x))) rht)
                             xb))" for xa
    unfolding the_edges_def
  proof(cases "lookup rht (right_vertex x)", goal_cases)
    case 1
    then show ?case 
      using  Tree2.eq_set_tree_empty[symmetric]
        dfs.Graph.vset.set.set_delete[OF dfs.Graph.vset.set.invar_empty, of x]      
      by(auto simp add:  RBT_Set.empty_def)
  next
    case (2 a)
    hence a1:"xa \<noteq> x" "xa \<in> t_set eds" 
      by (simp add: from_invar(1))+
    moreover then obtain y where a2:"lookup rht y \<noteq> None" "xa \<in> t_set (the (lookup rht y))"
      using from_invar(5) by auto 
    ultimately show ?case using 2 from_invar(3)
      by(auto intro!: exI[of _ y] simp add:  M.map_update[OF minvar_rht] emap_rht_inv_def )
  qed
  have g6: "vset_delete x (the_edges lft (left_vertex x)) \<noteq> vset_empty \<Longrightarrow>
          xa \<in> t_set (vset_delete x eds) \<Longrightarrow>
          \<exists>xb. (\<exists>y. lookup (update (left_vertex x) (vset_delete x (the_edges lft (left_vertex x))) lft) xb =
                    Some y) \<and>
               xa \<in> t_set
                      (the (lookup
                             (update (left_vertex x) (vset_delete x (the_edges lft (left_vertex x))) lft)
                             xb))" for xa
    unfolding the_edges_def
  proof(cases "lookup lft (left_vertex x)", goal_cases)
    case 1
    then show ?case 
      using  Tree2.eq_set_tree_empty[symmetric]
        dfs.Graph.vset.set.set_delete[OF dfs.Graph.vset.set.invar_empty, of x]      
      by(auto simp add:  RBT_Set.empty_def)
  next
    case (2 a)
    hence a1:"xa \<noteq> x" "xa \<in> t_set eds" 
      by (simp add: from_invar(1))+
    moreover then obtain y where a2:"lookup lft y \<noteq> None" "xa \<in> t_set (the (lookup lft y))"
      using from_invar(4) by auto 
    ultimately show ?case using 2 from_invar(2)
      by(auto intro!: exI[of _ y] simp add:  M.map_update[OF minvar_lft] emap_lft_inv_def )
  qed
  have g7: "vset_delete x (the_edges rht (right_vertex x)) \<noteq> vset_empty \<Longrightarrow>
       xa \<in> t_set y \<Longrightarrow>
       lookup (update (right_vertex x) (vset_delete x (the_edges rht (right_vertex x))) rht) xaa = Some y \<Longrightarrow>
       xa \<in> t_set (vset_delete x eds)" for xa xaa y
    unfolding the_edges_def
  proof(cases "lookup rht (right_vertex x)", goal_cases)
    case 1
    then show ?case    
      by(auto simp add:  RBT_Set.empty_def)
  next
    case (2 a)
    then show ?case using from_invar(3,5)
      by(cases "xaa = right_vertex x")
        (auto simp add: M.map_update[OF minvar_rht] set.set_delete[OF  from_invar(1)]
          emap_rht_inv_def, force, fastforce)      
  qed
  have g8: "vset_delete x (the_edges lft (left_vertex x)) \<noteq> vset_empty \<Longrightarrow>
       xa \<in> t_set y \<Longrightarrow>
       lookup (update (left_vertex x) (vset_delete x (the_edges lft (left_vertex x))) lft) xaa = Some y \<Longrightarrow>
       xa \<in> t_set (vset_delete x eds)" for xa xaa y
    unfolding the_edges_def
  proof(cases "lookup lft (left_vertex x)", goal_cases)
    case 1
    then show ?case    
      by(auto simp add:  RBT_Set.empty_def)
  next
    case (2 a)
    then show ?case using from_invar(2,4)
      by(cases "xaa = left_vertex x")
        (auto simp add: M.map_update[OF minvar_lft] set.set_delete[OF  from_invar(1)]
          emap_lft_inv_def, force, fastforce)      
  qed
  show ?case 
    using goal1 goal2 goal3
    by (auto intro: g1 g2 g3 g4 g5 g6 g7 g8)
qed (simp add: set_matching_def)

fun weak_orcl1 where
  "weak_orcl1 e (MATCH eds lft rht) = 
(case (lookup lft (left_vertex e)) of Some es \<Rightarrow> (if es = vset_empty then True else False) |
                                      None \<Rightarrow> True)"

fun weak_orcl2 where
  "weak_orcl2 e (MATCH eds lft rht) = 
(case (lookup rht (right_vertex e)) of Some es \<Rightarrow> (if es = vset_empty then True else False) |
                                      None \<Rightarrow> True)"

fun circuit1 where
  "circuit1 e (MATCH eds lft rht) = (the_edges lft (left_vertex e))"

fun circuit2 where
  "circuit2 e (MATCH eds lft rht) = (the_edges rht (right_vertex e))"

fun complement_matching where
  "complement_matching (MATCH eds lft rht) = vset_diff Edges_impl eds"

fun inner_fold where "inner_fold (MATCH eds lft rht) f = fold_rbt f eds"

definition "outer_fold A f= fold_rbt f A"

definition "set_invar_red = vset_inv"
definition "to_set_red = t_set"
end

locale compute_max_bimatch_by_matroid =
  compute_max_bimatch_by_matroid_spec +
  max_bimatch_by_matroid+
  assumes Edges_impl_inv: "vset_inv Edges_impl"
    and    Edges_impl_are:  "t_set Edges_impl = Edges"
begin

lemma weak_orcl1_correct:"invar_matching M \<Longrightarrow>
           set_matching M \<subseteq> Edges \<Longrightarrow>
           x \<in> Edges \<Longrightarrow>
           x \<notin> set_matching M \<Longrightarrow>
           indep1 (set_matching M) \<Longrightarrow> weak_orcl1 x M = indep1 ({x} \<union> set_matching M)"
proof(induction M)
  case (MATCH eds lft rht)
  have P_of_ifI: "(b \<Longrightarrow> P left) \<Longrightarrow> (\<not> b \<Longrightarrow> P right) \<Longrightarrow> P (if b then left else right)"
    for b P left right by auto
  from MATCH show ?case 
  proof(cases "lookup lft (left_vertex x)")
    case None
    hence "\<not> (\<exists> e \<in> set_matching (MATCH eds lft rht). left_vertex e = left_vertex x)"
      using MATCH(1,4)
      by(fastforce simp add: set_matching_def emap_lft_inv_def )
    hence " indep1 ({x} \<union> set_matching (MATCH eds lft rht))"
      using MATCH(2,3,5) x_is_left by (auto simp add: indep1_def)
    moreover have  "weak_orcl1 x (MATCH eds lft rht)" using None by simp
    ultimately show ?thesis by simp
  next
    case (Some es)
    show ?thesis
    proof(subst weak_orcl1.simps, subst Some, subst option.case(2), rule P_of_ifI, goal_cases)
      case 1
      note one = this
      hence no_e: "\<not> (\<exists> e. e \<in> t_set (the (lookup lft (left_vertex x))))"
        using MATCH(1,4) Some dfs.Graph.vset.emptyD(1)[of es]
        by(auto simp add: set_matching_def emap_lft_inv_def )
      have e_contr:" e \<in> set_matching (MATCH eds lft rht) \<Longrightarrow> left_vertex e = left_vertex x \<Longrightarrow> False" for e
      proof(goal_cases)
        case 1
        then obtain y xa where "e \<in> t_set y" "lookup lft xa = Some y"
          using MATCH(1)
          by(auto simp add: set_matching_def emap_lft_inv_def )
        hence " e \<in> t_set (the (lookup lft (left_vertex x)))"
          using MATCH(1) 1 by(fastforce simp add:  emap_lft_inv_def )
        thus False
          using no_e by auto
      qed
      have "{x} \<union> set_matching (MATCH eds lft rht) \<subseteq> Edges"
        using MATCH.prems(2) MATCH.prems(3) by auto
      moreover have "(\<forall>xa\<in>X.
         \<forall>e\<in>{x} \<union> set_matching (MATCH eds lft rht).
            \<forall>d\<in>{x} \<union> set_matching (MATCH eds lft rht). xa \<in> to_dbltn d \<longrightarrow> xa \<in> to_dbltn e \<longrightarrow> e = d)"
        using e_contr  MATCH.prems(2) MATCH.prems(3)  x_is_left  calculation x_is_left MATCH.prems(5)
        by(fastforce simp add: indep1_def)
      ultimately show ?case
        by (auto simp add: indep1_def)
    next
      case 2
      then obtain e where  "e \<in> t_set (the (lookup lft (left_vertex x)))"
        using MATCH(1) Some dfs.Graph.vset.choose'[OF 2]
        by (fastforce simp add:  emap_lft_inv_def set_matching_def)
      hence  "e \<in> set_matching (MATCH eds lft rht)" "left_vertex e = left_vertex x" 
        using MATCH.prems(1) Some set_matching_def  Some \<open>e \<in> t_set (the (lookup lft (left_vertex x)))\<close>
        by(fastforce simp add: emap_lft_inv_def)+
      hence "\<not> indep1 ({x} \<union> set_matching (MATCH eds lft rht))"
        using left_prop MATCH(4)
        by(simp add: indep1_def set_matching_def)
          (fastforce intro!: bexI[of _ "left_vertex x"] bexI[of _ e])
      thus ?case by simp
    qed
  qed
qed

lemma weak_orcl2_correct:"invar_matching M \<Longrightarrow>
           set_matching M \<subseteq> Edges \<Longrightarrow>
           x \<in> Edges \<Longrightarrow>
           x \<notin> set_matching M \<Longrightarrow>
           indep2 (set_matching M) \<Longrightarrow> weak_orcl2 x M = indep2 ({x} \<union> set_matching M)"
proof(induction M)
  case (MATCH eds lft rht)
  have P_of_ifI: "(b \<Longrightarrow> P left) \<Longrightarrow> (\<not> b \<Longrightarrow> P right) \<Longrightarrow> P (if b then left else right)"
    for b P left right by auto
  from MATCH show ?case 
  proof(cases "lookup rht (right_vertex x)")
    case None
    hence "\<not> (\<exists> e \<in> set_matching (MATCH eds lft rht). right_vertex e = right_vertex x)"
      using MATCH(1,4)
      by(fastforce simp add: set_matching_def emap_rht_inv_def  invar_matching_alt_def 
          simp del: invar_matching.simps)     
    hence " indep2 ({x} \<union> set_matching (MATCH eds lft rht))"
      using MATCH(2,3,5) x_is_right by (auto simp add: indep2_def)
    moreover have  "weak_orcl2 x (MATCH eds lft rht)" using None by simp
    ultimately show ?thesis by simp
  next
    case (Some es)
    show ?thesis
    proof(subst weak_orcl2.simps, subst Some, subst option.case(2), rule P_of_ifI, goal_cases)
      case 1
      note one = this
      hence no_e: "\<not> (\<exists> e. e \<in> t_set (the (lookup rht (right_vertex x))))"
        using MATCH(1,4) Some dfs.Graph.vset.emptyD(1)[of es]
        by(auto simp add: set_matching_def emap_lft_inv_def )
      have e_contr:" e \<in> set_matching (MATCH eds lft rht) \<Longrightarrow> right_vertex e = right_vertex x \<Longrightarrow> False" for e
      proof(goal_cases)
        case 1
        then obtain y xa where "e \<in> t_set y" "lookup rht xa = Some y"
          using MATCH(1)
          by(auto simp add: set_matching_def emap_rht_inv_def invar_matching_alt_def
              simp del: invar_matching.simps)
        hence " e \<in> t_set (the (lookup rht (right_vertex x)))"
          using MATCH(1) 1 by(fastforce simp add:  emap_rht_inv_def)
        thus False
          using no_e by auto
      qed
      have "{x} \<union> set_matching (MATCH eds lft rht) \<subseteq> Edges"
        using MATCH.prems(2) MATCH.prems(3) by auto
      moreover have "(\<forall>xa\<in>Y.
         \<forall>e\<in>{x} \<union> set_matching (MATCH eds lft rht).
            \<forall>d\<in>{x} \<union> set_matching (MATCH eds lft rht). xa \<in> to_dbltn d \<longrightarrow> xa \<in> to_dbltn e \<longrightarrow> e = d)"
        using e_contr  MATCH.prems(2) MATCH.prems(3)  x_is_right  calculation MATCH.prems(5)
        by(fastforce simp add: indep2_def invar_matching_alt_def simp del: invar_matching.simps)
      ultimately show ?case
        by (auto simp add: indep2_def)
    next
      case 2
      then obtain e where  "e \<in> t_set (the (lookup rht (right_vertex x)))"
        using MATCH(1) Some dfs.Graph.vset.choose'[OF 2]
        by (fastforce simp add:  emap_lft_inv_def set_matching_def)
      hence  "e \<in> set_matching (MATCH eds lft rht)" "right_vertex e = right_vertex x" 
        using MATCH.prems(1) Some set_matching_def  Some \<open>e \<in> t_set (the (lookup rht (right_vertex x)))\<close>
        by(fastforce simp add: emap_rht_inv_def invar_matching_alt_def simp del: invar_matching.simps)+
      hence "\<not> indep2 ({x} \<union> set_matching (MATCH eds lft rht))"
        using right_prop MATCH(4)
        by(simp add: indep2_def set_matching_def)
          (fastforce intro!: bexI[of _ "right_vertex x"] bexI[of _ e])
      thus ?case by simp
    qed
  qed
qed

lemma  inner_fold_spec:"invar_matching M \<Longrightarrow> 
\<exists>xs. set xs = set_matching M \<and> inner_fold M f init = foldr f xs init"
proof(induction M)
  case (MATCH eds lft rht)
  show ?case 
    using preorder_witness[of eds f init]
    by(auto intro!: exI[of _ "map fst (preorder eds)"] simp add: set_matching_def)
qed

lemma outer_fold_spec: "set_invar_red M \<Longrightarrow>
 \<exists>xs. set xs = to_set_red M \<and> outer_fold M f acc = foldr f xs acc"
  using preorder_witness[of M f]
  by(auto intro!: exI[of _ "map fst (preorder M)"] 
      simp add: set_invar_red_def to_set_red_def outer_fold_def)

lemma set_invar_red_of_complement:"invar_matching  S  \<Longrightarrow> set_invar_red (complement_matching  S)"
  by(induction S)(auto simp add: set_invar_red_def intro!: dfs.set_ops.invar_diff Edges_impl_inv)

lemma complement_is:"invar_matching  S  \<Longrightarrow> to_set_red (complement_matching  S) = Edges - set_matching S"
  by(induction S)
    (auto simp add:Edges_impl_are  to_set_red_def Edges_impl_inv dfs.set_ops.set_diff set_matching_def)

interpretation double_matroid_concrete: double_matroid Edges indep1 indep2
  by(auto intro!: double_matroid.intro matroid.intro indep_system1 indep_system2 matroid_axioms1 matroid_axioms2)

lemma circuit1_correct:
  assumes "invar_matching M"
    "indep1 (set_matching M)"
    "set_matching M \<subseteq> Edges"
    "y \<in> Edges"
    "\<not> indep1 ({y} \<union> set_matching M)"
  shows " to_set_red (circuit1 y M) =
           double_matroid_concrete.matroid1.the_circuit ({y} \<union> set_matching M) - {y}"
proof-
  have a_circuit:"double_matroid_concrete.matroid1.circuit
 (double_matroid_concrete.matroid1.the_circuit ({y} \<union> set_matching M))"
    using assms(2) assms(3) assms(4) assms(5) double_matroid_concrete.matroid1.the_circuit_is_circuit(1) by auto
  then obtain e d x where edx:" double_matroid_concrete.matroid1.the_circuit ({y} \<union> set_matching M) = {e, d}"
    "e \<noteq> d" "e \<in> Edges" "d \<in> Edges" "to_dbltn d \<inter> to_dbltn e \<inter> X = {x}"
    by(auto intro:
        circuit1_is[of "double_matroid_concrete.matroid1.the_circuit ({y} \<union> set_matching M)"] )
  hence e_disj:"e = y \<or> d = y" 
    using a_circuit assms(2) assms(3) assms(4) assms(5) 
      double_matroid_concrete.matroid1.the_circuit_is_circuit(2)
      double_matroid_concrete.matroid1.min_dep_imp_supset_circuit
    by fastforce
  moreover have x_is_left:"left_vertex d = x" "left_vertex e = x"
    using edx(3,4) edx(5) x_is_left by auto
  ultimately have left_of_y: "left_vertex y = x" by auto
  show ?thesis
  proof(cases rule: disjE[OF e_disj])
    case 1
    note e_is_y=this
    hence circuit_is_d:"double_matroid_concrete.matroid1.the_circuit ({y} \<union> set_matching M) - {y} = {d}"
      using edx(1) edx(2) by auto
    have x_is_left:"left_vertex d = x"
      using edx(4) edx(5) x_is_left by fastforce
    moreover have "d \<in> set_matching M" 
      using "1" assms(2) assms(3) assms(4) assms(5)
        double_matroid_concrete.matroid1.the_circuit_is_circuit(2) edx(1) edx(2) by fastforce
    ultimately have "d \<in> t_set (the_edges (on_left M) x)"
      using assms(2,3,1)
      by(induction M)
        (fastforce simp add: the_edges_def set_matching_def indep1_def emap_lft_inv_def)
    moreover have "f \<in> t_set (the_edges (on_left M) x) \<Longrightarrow> f \<noteq> d \<Longrightarrow> False" for f
    proof(goal_cases)
      case 1
      hence "left_vertex f = left_vertex d"
        using assms(1) on_left_left_vertex x_is_left by blast
      moreover have "f \<in> set_matching M" 
        using "1"(1) assms(1) on_left_in_M by blast
      ultimately have "\<not> indep1 (set_matching M)"
        using "1"(2) \<open>d \<in> set_matching M\<close> inj_on_contraD[OF left_inj] by auto
      thus False 
        using assms(2) by blast
    qed
    ultimately have "t_set (the_edges (on_left M) x) = {d}" by auto
    moreover have "to_set_red (circuit1 y M) = t_set (the_edges (on_left M) x)"
      by(induction M)
        (auto simp add: to_set_red_def left_of_y) 
    ultimately show ?thesis
      using  circuit_is_d by argo
  next
    case 2
    note e_is_y=this
    hence circuit_is_d:"double_matroid_concrete.matroid1.the_circuit ({y} \<union> set_matching M) - {y} = {e}"
      using edx(1) edx(2) by auto
    have x_is_left:"left_vertex e = x"
      using edx(4) edx(5) x_is_left by fastforce
    moreover have "e \<in> set_matching M" 
      using "2" assms(2) assms(3) assms(4) assms(5)
        double_matroid_concrete.matroid1.the_circuit_is_circuit(2) edx(1) edx(2) by fastforce
    ultimately have "e \<in> t_set (the_edges (on_left M) x)"
      using assms(2,3,1)
      by(induction M)
        (fastforce simp add: the_edges_def set_matching_def indep1_def emap_lft_inv_def)
    moreover have "f \<in> t_set (the_edges (on_left M) x) \<Longrightarrow> f \<noteq> e \<Longrightarrow> False" for f
    proof(goal_cases)
      case 1
      hence "left_vertex f = left_vertex e"
        using assms(1) on_left_left_vertex x_is_left by blast
      moreover have "f \<in> set_matching M" 
        using "1"(1) assms(1) on_left_in_M by blast
      ultimately have "\<not> indep1 (set_matching M)"
        using "1"(2) \<open>e \<in> set_matching M\<close> inj_on_contraD[OF left_inj] by auto
      thus False 
        using assms(2) by blast
    qed
    ultimately have "t_set (the_edges (on_left M) x) = {e}" by auto
    moreover have "to_set_red (circuit1 y M) = t_set (the_edges (on_left M) x)"
      by(induction M)
        (auto simp add: to_set_red_def left_of_y) 
    ultimately show ?thesis
      using  circuit_is_d by argo
  qed
qed

lemma circuit1_invar: "invar_matching M \<Longrightarrow> set_invar_red (circuit1 y M)"
  by(induction M)
    (auto simp add: set_invar_red_def the_edges_def dfs.Graph.vset.set.invar_empty emap_lft_inv_def
      split: option.split)

lemma circuit2_correct:
  assumes "invar_matching M"
    "indep2 (set_matching M)"
    "set_matching M \<subseteq> Edges"
    "y \<in> Edges"
    "\<not> indep2 ({y} \<union> set_matching M)"
  shows " to_set_red (circuit2 y M) =
           double_matroid_concrete.matroid2.the_circuit ({y} \<union> set_matching M) - {y}"
proof-
  have a_circuit:"double_matroid_concrete.matroid2.circuit
 (double_matroid_concrete.matroid2.the_circuit ({y} \<union> set_matching M))"
    using assms(2) assms(3) assms(4) assms(5) double_matroid_concrete.matroid2.the_circuit_is_circuit(1) by auto
  then obtain e d x where edx:" double_matroid_concrete.matroid2.the_circuit ({y} \<union> set_matching M) = {e, d}"
    "e \<noteq> d" "e \<in> Edges" "d \<in> Edges" "to_dbltn d \<inter> to_dbltn e \<inter> Y = {x}"
    by(auto intro:
        circuit2_is[of "double_matroid_concrete.matroid2.the_circuit ({y} \<union> set_matching M)"] )
  hence e_disj:"e = y \<or> d = y" 
    using a_circuit assms(2) assms(3) assms(4) assms(5) 
      double_matroid_concrete.matroid2.the_circuit_is_circuit(2)
      double_matroid_concrete.matroid2.min_dep_imp_supset_circuit
    by fastforce
  moreover have x_is_right:"right_vertex d = x" "right_vertex e = x"
    using edx(3,4) edx(5) x_is_right by auto
  ultimately have right_of_y: "right_vertex y = x" by auto
  show ?thesis
  proof(cases rule: disjE[OF e_disj])
    case 1
    note e_is_y=this
    hence circuit_is_d:"double_matroid_concrete.matroid2.the_circuit ({y} \<union> set_matching M) - {y} = {d}"
      using edx(1) edx(2) by auto
    have x_is_right:"right_vertex d = x"
      using edx(4) edx(5) x_is_right by fastforce
    moreover have "d \<in> set_matching M" 
      using "1" assms(2) assms(3) assms(4) assms(5)
        double_matroid_concrete.matroid2.the_circuit_is_circuit(2) edx(1) edx(2) by fastforce
    ultimately have "d \<in> t_set (the_edges (on_right M) x)"
      using assms(2,3,1)
      by(induction M)
        (fastforce simp add: the_edges_def set_matching_def indep2_def emap_rht_inv_def invar_matching_alt_def
          simp del: invar_matching.simps)
    moreover have "f \<in> t_set (the_edges (on_right M) x) \<Longrightarrow> f \<noteq> d \<Longrightarrow> False" for f
    proof(goal_cases)
      case 1
      hence "right_vertex f = right_vertex d"
        using assms(1) on_right_right_vertex x_is_right by blast
      moreover have "f \<in> set_matching M" 
        using "1"(1) assms(1) on_right_in_M by blast
      ultimately have "\<not> indep2 (set_matching M)"
        using "1"(2) \<open>d \<in> set_matching M\<close> inj_on_contraD[OF right_inj] by auto
      thus False 
        using assms(2) by blast
    qed
    ultimately have "t_set (the_edges (on_right M) x) = {d}" by auto
    moreover have "to_set_red (circuit2 y M) = t_set (the_edges (on_right M) x)"
      by(induction M)
        (auto simp add: to_set_red_def right_of_y) 
    ultimately show ?thesis
      using  circuit_is_d by argo
  next
    case 2
    note e_is_y=this
    hence circuit_is_d:"double_matroid_concrete.matroid2.the_circuit ({y} \<union> set_matching M) - {y} = {e}"
      using edx(1) edx(2) by auto
    have x_is_left:"right_vertex e = x"
      using edx(4) edx(5) x_is_right by fastforce
    moreover have "e \<in> set_matching M" 
      using "2" assms(2) assms(3) assms(4) assms(5)
        double_matroid_concrete.matroid2.the_circuit_is_circuit(2) edx(1) edx(2) by fastforce
    ultimately have "e \<in> t_set (the_edges (on_right M) x)"
      using assms(2,3,1)
      by(induction M)
        (fastforce simp add: the_edges_def set_matching_def indep2_def emap_rht_inv_def invar_matching_alt_def
          simp del: invar_matching.simps)
    moreover have "f \<in> t_set (the_edges (on_right M) x) \<Longrightarrow> f \<noteq> e \<Longrightarrow> False" for f
    proof(goal_cases)
      case 1
      hence "right_vertex f = right_vertex e"
        using assms(1) on_right_right_vertex x_is_left by blast
      moreover have "f \<in> set_matching M" 
        using "1"(1) assms(1) on_right_in_M by blast
      ultimately have "\<not> indep2 (set_matching M)"
        using "1"(2) \<open>e \<in> set_matching M\<close> inj_on_contraD[OF right_inj] by auto
      thus False 
        using assms(2) by blast
    qed
    ultimately have "t_set (the_edges (on_right M) x) = {e}" by auto
    moreover have "to_set_red (circuit2 y M) = t_set (the_edges (on_right M) x)"
      by(induction M)
        (auto simp add: to_set_red_def right_of_y) 
    ultimately show ?thesis
      using  circuit_is_d by argo
  qed
qed

lemma circuit2_invar: "invar_matching M \<Longrightarrow> set_invar_red (circuit2 y M)"
  by(induction M)
    (auto simp add: set_invar_red_def the_edges_def dfs.Graph.vset.set.invar_empty emap_rht_inv_def
      split: option.split)

end

global_interpretation matching_basic_operations: compute_max_bimatch_by_matroid_spec
  where Edges =Edges and to_dbltn = to_dbltn and right_vertex= right_vertex
    and left_vertex = left_vertex
  for Edges to_dbltn left_vertex right_vertex Edges_impl
  defines the_edges=matching_basic_operations.the_edges
    and empty_matching=matching_basic_operations.empty_matching
    and insert_matching=matching_basic_operations.insert_matching
    and delete_matching=matching_basic_operations.delete_matching
    and set_matching=matching_basic_operations.set_matching
    and invar_matching=matching_basic_operations.invar_matching
    and weak_orcl1=matching_basic_operations.weak_orcl1
    and weak_orcl2=matching_basic_operations.weak_orcl2
    and circuit1=matching_basic_operations.circuit1
    and circuit2=matching_basic_operations.circuit2
    and complement_matching=matching_basic_operations.complement_matching
    and inner_fold=matching_basic_operations.inner_fold
    and outer_fold=matching_basic_operations.outer_fold
    and set_invar_red=matching_basic_operations.set_invar_red
    and to_set_red=matching_basic_operations.to_set_red
  done

global_interpretation matching_by_matroid: unweighted_intersection_spec
  where empty = RBT_Set.empty
    and delete= RBT_Map.delete
    and lookup=lookup
    and insert=insert_rbt
    and isin=isin
    and t_set=t_set
    and sel=sel
    and update=update
    and adjmap_inv =M.invar
    and vset_empty=Leaf
    and vset_delete= RBT.delete
    and vset_inv=vset_inv
    and to_set=set_matching
    and set_invar="invar_matching left_vertex right_vertex"
    and set_empty=empty_matching
    and inner_fold=inner_fold
    and outer_fold=outer_fold
    and inner_fold_circuit=outer_fold
    and set_insert="insert_matching left_vertex right_vertex"
    and set_delete="delete_matching left_vertex right_vertex"
    and weak_orcl1="weak_orcl1 left_vertex"
    and weak_orcl2="weak_orcl2 right_vertex"
    and circuit1="circuit1 left_vertex"
    and circuit2="circuit2 right_vertex"
    and find_path="\<lambda> S T G. find_path s t G S T "
    and complement="complement_matching Edges_impl"
  for  left_vertex right_vertex s t Edges_impl
  defines treat1=matching_by_matroid.treat1
    and     treat2=matching_by_matroid.treat2
    and     compute_graph=matching_by_matroid.compute_graph
    and     augment=matching_by_matroid.augment
    and     matroid_intersection_impl=matching_by_matroid.matroid_intersection_impl
    and     treat1_circuit=matching_by_matroid.treat1_circuit
    and     treat2_circuit=matching_by_matroid.treat2_circuit
    and     compute_graph_circuit=matching_by_matroid.compute_graph_circuit
    and     matroid_intersection_circuit_impl=matching_by_matroid.matroid_intersection_circuit_impl
    and     add_edge=G.add_edge
    and     initial_state=matching_by_matroid.initial_state
  by(auto intro!: unweighted_intersection_spec.intro simp add: G.Pair_Graph_Specs_axioms)

definition "es = [(1::nat,6::nat), (1, 8), (1, 10), (3,6),(3,10),  (9,8), (7,10)]"
definition "E_impl = a_edge_set es"

value "matroid_intersection_circuit_impl fst snd (0,0) (1,1) E_impl initial_state"
value "inorder (edges (sol 
(matroid_intersection_circuit_impl fst snd (0,0) (1,1) E_impl initial_state)))"

value "matroid_intersection_impl fst snd (0,0) (1,1) E_impl initial_state"
value "inorder (edges (sol (matroid_intersection_impl fst snd (0,0) (1,1) E_impl initial_state)))"

context 
  fixes left_vertex::"'e::linorder \<Rightarrow> 'v::linorder" 
    and right_vertex::"'e \<Rightarrow> 'v"
    and s::'e
    and t::'e
    and Edges_impl::"('e \<times> color) tree"
  assumes bipart:"\<not> (\<exists> e d. e \<in> t_set Edges_impl \<and> d \<in> t_set Edges_impl \<and>
                                 left_vertex e = right_vertex d)"
    and s_t: "s \<notin> t_set Edges_impl" "t \<notin> t_set Edges_impl" "s \<noteq> t"
    and Edges_impl_inv: "vset_inv Edges_impl"
    and left_not_right: "\<And> e. e \<in> Edges \<Longrightarrow> left_vertex e \<noteq> right_vertex e "
    and injectivity: "\<And> e e'. e \<in> Edges \<Longrightarrow> e' \<in> Edges \<Longrightarrow> left_vertex e = left_vertex e' \<Longrightarrow>
                                   right_vertex e= right_vertex e' \<Longrightarrow>e = e'"
begin

definition "to_dbltn e = {left_vertex e, right_vertex e}"
definition "Edges=t_set Edges_impl"
definition "X = left_vertex ` Edges"
definition "Y = right_vertex ` Edges"

lemma Edges_impl_is:"t_set Edges_impl =Edges"
  by(simp add: Edges_def)

lemma left_not_right: "e \<in> local.Edges \<Longrightarrow> \<exists>u v. {left_vertex e, right_vertex e} = {u, v} \<and> u \<noteq> v"
  using bipart by(auto simp add: Edges_def)

lemma bipartite: "bipartite (to_dbltn ` Edges) X Y"
  using bipart 
  by(auto simp add: Edges_def X_def Y_def bipartite_def to_dbltn_def)

lemma to_dbltn_inj: "inj_on to_dbltn Edges"
proof(rule inj_onI, goal_cases)
  case (1 x y)
  then show ?case 
    using injectivity [OF 1(1,2)] bipart 
    by(force simp add: to_dbltn_def Edges_def)
qed

lemma correct_side: "e \<in> Edges \<Longrightarrow> left_vertex e \<in> X"
  "e \<in> Edges \<Longrightarrow> right_vertex e \<in> Y"
  by(auto simp add: Edges_def X_def Y_def)

lemma finite_Edges: "finite Edges"
  by (simp add: Edges_def)

interpretation matching_as_matroid_intersection: max_bimatch_by_matroid
  where to_dbltn=to_dbltn and Edges=Edges and X = X and Y = Y and left_vertex = left_vertex 
    and right_vertex=right_vertex
  using bipartite bipart
  by(auto intro!: max_bimatch_by_matroid.intro 
      left_not_right bipartite correct_side finite_Edges
      simp add: to_dbltn_def to_dbltn_inj Edges_impl_is)

interpretation matching_as_matroid_intersection_proofs: compute_max_bimatch_by_matroid
  where to_dbltn=to_dbltn and Edges=Edges and X = X and Y = Y and left_vertex = left_vertex 
    and right_vertex=right_vertex
  by(auto simp add: compute_max_bimatch_by_matroid_def Edges_impl_inv Edges_impl_is
      matching_as_matroid_intersection.max_bimatch_by_matroid_axioms
      intro!: compute_max_bimatch_by_matroid_axioms.intro)

definition "indep1 = matching_as_matroid_intersection.indep1"
definition "indep2 = matching_as_matroid_intersection.indep2"

lemma double_matroid:"double_matroid Edges indep1 indep2"
  by(auto intro: matching_as_matroid_intersection.double_matroid_concrete simp add: indep1_def indep2_def)

lemma same_invar: "invar_matching left_vertex right_vertex= 
            matching_as_matroid_intersection_proofs.invar_matching"
  apply(rule ext)
  subgoal for M
    apply(cases M)
    apply (simp add: matching_basic_operations.emap_lft_inv_def
        matching_basic_operations.emap_rht_inv_def) 
    done
  done

interpretation matching_algorithm: unweighted_intersection
  where empty = RBT_Set.empty
    and delete= RBT_Map.delete
    and lookup=lookup
    and insert=insert_rbt
    and isin=isin
    and vset=t_set
    and sel=sel
    and update=update
    and adjmap_inv =M.invar
    and vset_empty=Leaf
    and vset_delete= RBT.delete
    and vset_inv=vset_inv
    and to_set=set_matching
    and set_invar="invar_matching left_vertex right_vertex"
    and set_empty=empty_matching
    and inner_fold=inner_fold
    and outer_fold=outer_fold
    and inner_fold_circuit=outer_fold
    and set_insert="insert_matching left_vertex right_vertex"
    and set_delete="delete_matching left_vertex right_vertex"
    and weak_orcl1="weak_orcl1 left_vertex"
    and weak_orcl2="weak_orcl2 right_vertex"
    and circuit1="circuit1 left_vertex"
    and circuit2="circuit2 right_vertex"
    and find_path="\<lambda> S T G. find_path s t G S T "
    and complement="complement_matching Edges_impl"
    and carrier=Edges
    and indep1=indep1
    and indep2=indep2
    and to_set_red=to_set_red
    and set_invar_red=set_invar_red
proof(rule unweighted_intersection.intro, goal_cases)
  case 1
  then show ?case 
    by (simp add: matching_by_matroid.unweighted_intersection_spec_axioms)
next
  case 2
  then show ?case 
    by(auto intro: double_matroid)
next
  case 3
  then show ?case 
  proof(rule unweighted_intersection_axioms.intro, goal_cases)
    case (1 S x)
    then show ?case 
      by (simp add: matching_basic_operations.set_matching_insert(1))
  next
    case (2 S x)
    then show ?case 
      by (simp add: matching_basic_operations.set_matching_insert(2))
  next
    case (3 S x)
    then show ?case 
      by (simp add: matching_basic_operations.set_matching_delete(1))
  next
    case (4 S x)
    then show ?case 
      by (simp add: matching_basic_operations.set_matching_delete(2))
  next
    case 5
    then show ?case 
      by (simp add: matching_basic_operations.set_matching_empty(1))
  next
    case 6
    then show ?case 
      by (simp add: matching_basic_operations.set_matching_empty(2))
  next
    case (7 X x)
    then show ?case 
      by (auto simp add:matching_as_matroid_intersection_proofs.weak_orcl1_correct 
          same_invar indep1_def weak_orcl1_def set_matching_def)
  next
    case (8 X x)
    then show ?case 
      by (auto simp add:matching_as_matroid_intersection_proofs.weak_orcl2_correct 
          same_invar indep2_def weak_orcl2_def set_matching_def)
  next
    case (9 X f G)
    then show ?case 
      by (auto intro: matching_as_matroid_intersection_proofs.inner_fold_spec 
          simp add:  same_invar indep2_def weak_orcl2_def set_matching_def inner_fold_def)
  next
    case (10 X f G)
    then show ?case 
      by(auto intro: matching_as_matroid_intersection_proofs.outer_fold_spec 
          simp add: same_invar indep2_def weak_orcl2_def set_matching_def
          outer_fold_def set_invar_red_def to_set_red_def)  
  next
    case (11 X f trip)
    then show ?case
      by(auto intro: matching_as_matroid_intersection_proofs.outer_fold_spec 
          simp add: same_invar indep2_def weak_orcl2_def set_matching_def
          outer_fold_def set_invar_red_def to_set_red_def)  
  next
    case (12 G S T)
    then show ?case 
      unfolding G_and_dfs_graph(1)
      using compute_path.find_path1[of s Edges t G S T]
      using Edges_def s_t(1,2,3) 
      by (auto intro: simp add: G_and_dfs_graph(1,2))
  next
    case (13 G S T p)
    then show ?case 
      unfolding G_and_dfs_graph(1)
      using compute_path.find_path_weak(2)[of s Edges t G S T p]s_t(1,2,3) 
      by (auto intro: simp add: G_and_dfs_graph(1,2) Edges_def)
  qed (auto intro: matching_as_matroid_intersection_proofs.set_invar_red_of_complement
      simp add: complement_matching_def invar_matching_def set_invar_red_def
      matching_as_matroid_intersection_proofs.complement_is  set_matching_def to_set_red_def
      matching_as_matroid_intersection_proofs.circuit1_correct
      circuit1_def indep1_def 
      matching_as_matroid_intersection_proofs.circuit1_invar
      matching_as_matroid_intersection_proofs.circuit2_correct
      circuit2_def indep2_def
      matching_as_matroid_intersection_proofs.circuit2_invar)
qed

lemma same_card_dbltn: "X \<subseteq> Edges \<Longrightarrow> card (to_dbltn ` X) = card X" for X
  using to_dbltn_inj
  by(auto intro!:  card_image inj_onI simp add: inj_on_def)

theorem solution:"graph_matching (to_dbltn ` Edges)
                  (to_dbltn ` (set_matching (sol (matroid_intersection_circuit_impl 
                                  left_vertex right_vertex s t Edges_impl initial_state))))"
  (is ?thesis1)
  and   "\<nexists> M. graph_matching (to_dbltn ` Edges) M \<and>
              card M > card  (set_matching (sol (matroid_intersection_circuit_impl 
                                 left_vertex right_vertex s t Edges_impl initial_state)))"
  (is ?thesis2)
proof-
  show ?thesis1
    using  matching_algorithm.indep_invar_def
             [of "matroid_intersection_circuit_impl left_vertex right_vertex s t Edges_impl initial_state"]
           matching_algorithm.is_max_def
             [of "_ (sol (matroid_intersection_circuit_impl left_vertex right_vertex s t Edges_impl initial_state))"]
            matching_algorithm.matroid_intersection_circuit_correctness(1)
    by( simp add: indep1_def indep2_def 
        matching_as_matroid_intersection.double_indep_to_graph_matching
        matroid_intersection_circuit_impl_def  initial_state_def matching_algorithm.same_results(2))
  show ?thesis2
  proof(rule ccontr, goal_cases)
    case 1
    then obtain M where M_prop:"graph_matching (local.to_dbltn ` local.Edges) M"
      "card
           (set_matching (sol
             (matroid_intersection_circuit_impl left_vertex right_vertex s t Edges_impl initial_state)))
          < card M" by auto
    then obtain M_impl where M_impl_prop:" M = local.to_dbltn ` M_impl"
      "matching_as_matroid_intersection.indep1 M_impl" "matching_as_matroid_intersection.indep2 M_impl"
      using matching_as_matroid_intersection.graph_matching_to_double_indep[OF M_prop(1)] by auto
    moreover have "card M = card M_impl" 
      using calculation(1) calculation(2) matching_algorithm.matroid1.indep_subset_carrier 
      by (simp add: indep1_def same_card_dbltn)
    moreover have "card
           (set_matching (sol 
             (matroid_intersection_circuit_impl left_vertex right_vertex s t
                     Edges_impl initial_state)))
          \<ge> card M_impl"
      using M_impl_prop(2,3)  matching_algorithm.indep_invar_def matching_algorithm.is_max_def
        matching_algorithm.matroid_intersection_circuit_correctness(1,2) 
      by(auto simp add: indep1_def indep2_def 
          matroid_intersection_circuit_impl_def matching_algorithm.same_results(2) initial_state_def)
    ultimately show ?case 
      using M_prop(2) by linarith
  qed
qed

end
end