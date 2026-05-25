theory Odd_Components
  imports Bipartite_Matchings_Existence Cardinality_Sums
begin

section \<open>Odd and Even Connected Components\<close>

definition odd_component where
  "odd_component G C = (\<exists> v \<in> Vs G. connected_component G v = C \<and> odd (card C))"

definition odd_components where
  "odd_components G = {C. odd_component G C}"

definition even_components where
  "even_components G = {C. \<exists> v \<in> Vs G. connected_component G v = C \<and> even (card C)}"

definition count_odd_components where
  "count_odd_components G = card (odd_components G)"

definition graph_diff where
  "graph_diff G X = {e. e \<in> G \<and> e \<inter> X = {}}"

(*TODO: those two definitions are the same

lemma "remove_vertices_graph = graph_diff"
  apply(rule HOL.ext)
  by (auto simp add: graph_diff_def remove_vertices_graph_def)*)

definition singl_in_diff where 
  "singl_in_diff G X = {a. \<exists> v. a = {v} \<and> v \<in> Vs G \<and> v \<notin> X \<and> v \<notin> Vs (graph_diff G X)}"

definition odd_comps_in_diff where
  "odd_comps_in_diff G X = (odd_components (graph_diff G X)) \<union> (singl_in_diff G X)"

definition count_odd_comps_in_diff where
  "count_odd_comps_in_diff G X = card (odd_comps_in_diff G X)"

definition barrier where
  "barrier G X = ( X \<noteq> {} \<and> card (odd_comps_in_diff G X) = card X)"

lemma graph_diff_member[iff?]: "e \<in> graph_diff G X \<longleftrightarrow>
   e \<in> G \<and> e \<inter> X = {}"
  unfolding graph_diff_def by simp

lemma graph_diffE:
  "e \<in> graph_diff G X \<Longrightarrow>
   (\<lbrakk>e \<in> G \<and> e \<inter> X = {}\<rbrakk> \<Longrightarrow> R)
   \<Longrightarrow> R"
  by (simp add: graph_diff_member)

lemma graph_diffI:
  assumes "e \<in> G"
  assumes "e \<inter> X = {}"
  shows "e \<in> graph_diff G X" 
  using assms graph_diff_def by auto

lemma graph_diff_subset: "graph_diff G X \<subseteq> G"
  by (simp add: graph_diff_def)

lemma connected_component_subset:
  assumes "v \<in> Vs G"
  shows "connected_component G v \<subseteq> Vs G"
  using assms by (metis in_connected_component_in_edges subsetI)

lemma diff_connected_component_subset:
  assumes "v \<in> Vs G"
  shows "connected_component (graph_diff G X) v \<subseteq> Vs G" 
  by (meson assms con_comp_subset connected_component_subset dual_order.trans graph_diff_subset)

lemma odd_component_member[iff?]: 
  "C \<in> odd_components G \<longleftrightarrow> odd_component G C"
  unfolding odd_components_def by simp

lemma odd_componentsE:
  "C \<in> odd_components G \<Longrightarrow>
   (\<lbrakk>odd_component G C\<rbrakk> \<Longrightarrow> R)
   \<Longrightarrow> R"
  by (simp add: odd_component_member)

lemma odd_componentsI:
  assumes "odd_component G C"
  shows "C \<in> odd_components G" 
  by (simp add: assms odd_components_def)

lemma odd_componentE:
  assumes major: "odd_component G C"
    and minor: "\<exists> v \<in> Vs G. connected_component G v = C \<and> odd (card C)  \<Longrightarrow> Q"
  shows "Q"
  using major minor odd_component_def by blast

lemma odd_componentOb:
  assumes "odd_component G C" 
  obtains v where "v \<in> Vs G" "connected_component G v = C" "odd (card C)"
  using assms unfolding odd_component_def  by blast

lemma odd_componentI:
  assumes "odd (card C)"
  assumes "v \<in> Vs G"
  assumes "connected_component G v = C"
  shows "odd_component G C" 
  using assms odd_component_def by auto

lemma even_component_member[iff?]: 
  "C \<in> even_components G \<longleftrightarrow>
   (\<exists>v \<in> Vs G. connected_component G v = C \<and> even (card C))"
  unfolding even_components_def by simp

lemma even_componentsE:
  assumes "C \<in> even_components G" 
  obtains v where "v \<in> Vs G" "connected_component G v = C" "even (card C)"
  using assms 
  by(auto simp: even_component_member)

lemma even_componentsI:
  assumes "even (card C)"
  assumes "v \<in> Vs G"
  assumes "connected_component G v = C"
  shows "C \<in> even_components G" 
  using assms even_components_def by auto

lemma singl_in_diff_member[iff?]: 
  "C \<in> singl_in_diff G  X \<longleftrightarrow> (\<exists> v. C = {v} \<and> v \<in> Vs G \<and> v \<notin> X \<and> v \<notin> Vs (graph_diff G X))"
  unfolding singl_in_diff_def by simp


lemma singl_in_diffE:
  assumes "C \<in> singl_in_diff G X" 
  obtains v where "v \<in> Vs G" "C = {v}" "v \<notin> X" "v \<notin> Vs (graph_diff G X)"
  using assms singl_in_diff_member[of C G X] 
  by(auto simp: singl_in_diff_member)


lemma singl_in_diffI:
  assumes "v \<in> Vs G"
  assumes "C = {v}"
  assumes "v \<notin> X"
  assumes "v \<notin> Vs (graph_diff G X)"
  shows "C \<in> singl_in_diff G X" 
  using  assms 
  by (simp add: singl_in_diff_member)

lemma odd_components_inter_singl_empty:
  shows "odd_components (graph_diff G X) \<inter> singl_in_diff G X = {}"
  apply(auto, elim odd_componentsE singl_in_diffE) 
  by (metis in_connected_component_in_edges odd_component_def singletonI)


lemma odd_components_sum_singletions_is_component:
  shows "(odd_components (graph_diff G X)) \<oplus> (singl_in_diff G X) = odd_comps_in_diff G X"
  using odd_components_inter_singl_empty 
  by (metis (no_types, lifting) Int_Un_eq(4) Un_Diff_Int Un_left_commute odd_comps_in_diff_def
      sup_bot_right symmetric_diff_def)


lemma odd_comps_in_diff_member[iff?]:
  "C \<in> odd_comps_in_diff G X \<longleftrightarrow> C \<in> odd_components (graph_diff G X) \<or> C \<in> singl_in_diff G X"
  by (simp add: odd_comps_in_diff_def)

lemma odd_comps_in_diffE:
  assumes major: "C \<in> odd_comps_in_diff G X"
    and minorP: "C \<in> odd_components (graph_diff G X) \<Longrightarrow> R"
    and minorQ: "C \<in> singl_in_diff G X \<Longrightarrow> R"
  shows R
  using major minorP minorQ odd_comps_in_diff_member by blast

lemma odd_comps_in_diffI1: "C \<in> odd_components (graph_diff G X) \<Longrightarrow> C \<in> odd_comps_in_diff G X"
  by (simp add: odd_comps_in_diff_member)

lemma odd_comps_in_diffI2: "C \<in> singl_in_diff G X \<Longrightarrow> C \<in> odd_comps_in_diff G X"
  by (simp add: odd_comps_in_diff_member)

lemma odd_comps_in_diffOR:
  assumes "C \<in> odd_components (graph_diff G X) \<or> C \<in> singl_in_diff G X"
  shows "C \<in> odd_comps_in_diff G X" 
  by (simp add: assms odd_comps_in_diff_member)

lemma edge_subset_component:
  assumes "graph_invar G"
  assumes "e \<in> G"
  assumes "v \<in> e"
  shows "e \<subseteq> connected_component G v"
  using assms connected_components_member_sym
  by (smt (verit, best) dblton_graphE in_con_comp_insert in_own_connected_component insert_Diff
          insert_iff singletonD subsetI)

lemma edge_in_E_card:
  assumes "graph_invar G"
  assumes "e \<in> G"
  shows "card e = 2" 
  using assms(1) assms(2) by auto

lemma component_is_finite:
  assumes "graph_invar G"
  shows "finite (connected_component G v)"
  by (metis assms connected_component_subset 
      connected_components_notE_singletons finite.simps finite_subset)

lemma connected_component_not_singleton:
  assumes "graph_invar G"
  assumes "v\<in> Vs G"
  shows "card (connected_component G v) > 1"
proof -
  obtain e where "e \<in> G" "v \<in> e" using assms(2) vs_member_elim by metis
  then have "e \<subseteq> (connected_component G v)"
    by (simp add: edge_subset_component assms(1) \<open>v\<in> Vs G\<close>)
  then have "card (connected_component G v) \<ge> 2"
    using edge_in_E_card[of G e] component_is_finite[of G v]  assms(1)
    by (metis \<open>e \<in> G\<close> card_mono)
  then show ?thesis  by linarith
qed

lemma odd_component_is_component:
  assumes "C \<in> odd_components G"
  assumes "x \<in> C"
  shows "connected_component G x = C"
  using assms
  apply(elim odd_componentsE odd_componentE)
  by (metis connected_components_member_eq)

lemma singl_in_diff_is_component:
  assumes "C \<in> singl_in_diff G X"
  assumes "x \<in> C"
  shows "connected_component (graph_diff G X) x = C"
  by (metis assms connected_components_notE_singletons singletonD singl_in_diff_member)

lemma odd_comps_in_diff_is_component:
  assumes "C \<in> (odd_comps_in_diff G X)"
  assumes "x \<in> C"
  shows "connected_component (graph_diff G X) x = C"
  using singl_in_diff_is_component
    odd_component_is_component 
  by (metis assms odd_comps_in_diff_member)

lemma odd_components_nonempty:
  assumes "C \<in> odd_comps_in_diff G X"
  shows "C \<noteq> {}" 
  using assms 
  apply (elim odd_comps_in_diffE odd_componentsE singl_in_diffE)
  unfolding odd_component_def
   apply (simp add: odd_card_imp_not_empty)
  by blast

lemma odd_component_in_E:
  assumes "odd_component G C"
  shows "C \<subseteq> Vs G" 
  by (metis assms connected_component_subset odd_component_def)

lemma odd_components_elem_in_E:
  assumes "C \<in> odd_components G"
  shows "C \<subseteq> Vs G" 
  by (meson assms odd_component_in_E odd_componentsE)

lemma singl_in_diff_in_E:
  assumes "C \<in> singl_in_diff G X"
  shows "C \<subseteq> Vs G"
  using assms 
  apply(elim singl_in_diffE) by blast

lemma component_in_E:
  assumes "C \<in> odd_comps_in_diff G X"
  shows "C \<subseteq> Vs G"
  using assms
  apply (elim odd_comps_in_diffE)
   apply (meson Vs_subset dual_order.trans graph_diff_subset odd_components_elem_in_E)
  by (simp add: singl_in_diff_in_E)

lemma component_of_el_in_E:
  assumes "connected_component G x \<in> (odd_comps_in_diff G X)"
  shows "x \<in> Vs G"
  using component_in_E 
  by (metis assms in_mono in_own_connected_component)

lemma odd_comps_in_diff_not_in_X:
  assumes "C \<in> odd_comps_in_diff G X"
  shows  "C \<inter> X = {}"
proof(rule ccontr)
  assume "C \<inter> X \<noteq> {}"
  show False 
  proof(cases "C \<in> odd_components (graph_diff G X)")
    case True
    have "C \<subseteq> Vs (graph_diff G X)"
      using True odd_components_elem_in_E by auto
    then show ?thesis 
      by (metis \<open>C \<inter> X \<noteq> {}\<close> disjoint_iff_not_equal graph_diffE subsetD vs_member_elim)
  next
    case False
    then have "C \<in> singl_in_diff G X" 
      by (meson assms odd_comps_in_diff_member)
    then show ?thesis 
      apply (elim singl_in_diffE)
      using \<open>C \<inter> X \<noteq> {}\<close> by blast
  qed
qed

lemma card_singl_in_diff_is_one:
  assumes "C \<in> singl_in_diff G X"
  shows "card C = 1" 
  using singl_in_diffE[OF assms]
  by (metis is_singleton_altdef is_singleton_def)

lemma diff_odd_compoenent_has_odd_card:
  assumes "C \<in> odd_comps_in_diff G X"
  shows "odd (card C)"
  using assms 
  apply(elim odd_comps_in_diffE odd_componentE)
   apply (meson odd_componentOb odd_componentsE)
  by (simp add: card_singl_in_diff_is_one)

lemma vs_graph_diff: "Vs (graph_diff G X) \<subseteq> Vs G - X"
  unfolding graph_diff_def Vs_def
  by blast

lemma odd_comps_in_diff_are_components:
  shows "odd_comps_in_diff G X = 
  {C. \<exists> v\<in>Vs G-X. connected_component (graph_diff G X) v = C \<and> odd (card C)}"
  unfolding odd_comps_in_diff_def
  apply safe
    apply(elim odd_componentsE odd_componentE )
    apply (meson subsetD vs_graph_diff) 
   apply (metis DiffI card_singl_in_diff_is_one odd_one singl_in_diffE 
      singl_in_diff_is_component singletonI)
  by (metis connected_components_notE_singletons odd_componentI 
      odd_componentsI singl_in_diffI)


lemma odd_comps_in_diff_are_componentsOb:
  assumes "C \<in> odd_comps_in_diff G X"
  obtains v where "v\<in>Vs G-X" 
    "connected_component (graph_diff G X) v = C"
    "odd (card C)"
  using odd_comps_in_diff_are_components[of G X] 
  using assms by fastforce

lemma odd_comps_in_diff_are_componentsI:
  assumes "odd (card C)"
  assumes "v\<in>Vs G-X"
  assumes "connected_component (graph_diff G X) v = C"
  shows "C \<in> odd_comps_in_diff G X"
  using odd_comps_in_diff_are_components[of G X] 
  using assms by fastforce

lemma odd_comps_in_diff_are_componentsI2:
  assumes "odd (card C)"
  assumes "C \<in> connected_components (graph_diff G X)"
  shows "C \<in> odd_comps_in_diff G X"
  by (metis assms(1) assms(2) connected_comp_has_vert odd_componentI
      odd_component_member odd_comps_in_diff_member)

lemma diff_component_disjoint:
  assumes "C1 \<in> (odd_comps_in_diff G X)"
  assumes "C2 \<in> (odd_comps_in_diff G X)"
  assumes "C1 \<noteq> C2"
  shows "C1 \<inter> C2 = {}"
  by (metis assms odd_comps_in_diff_is_component disjoint_iff_not_equal)


lemma components_is_union_even_and_odd:
  shows "connected_components G = odd_components G \<union> even_components G"
  unfolding connected_components_def odd_components_def even_components_def odd_component_def
  by safe blast+

lemma components_parity_is_odd_components_parity:
  assumes "graph_invar G"
  shows "even (sum card (connected_components G)) = even (card (odd_components G))"
proof -
  let ?Cs = " (connected_components G)"
  have "finite ?Cs"  
    by (simp add: assms finite_con_comps)
  then have "even (sum card (connected_components G)) = even (card {C \<in> ?Cs. odd (card C)})"
    using Parity.semiring_parity_class.even_sum_iff[of ?Cs card] by auto
  moreover have "{C \<in> ?Cs. odd (card C)} = odd_components G" 
    unfolding connected_components_def odd_components_def  odd_component_def by blast
  ultimately show ?thesis by presburger 
qed

lemma odd_components_eq_modulo_cardinality:
  assumes "graph_invar G"
  shows "even (card (odd_components G)) = even (card (Vs G))"
  using components_parity_is_odd_components_parity[OF assms] 
    sum_card_connected_components[OF assms] by auto

lemma diff_is_union_elements:
  assumes "graph_invar G"
  assumes "X \<subseteq> Vs G"
  shows "Vs (graph_diff G X) \<union> Vs (singl_in_diff G X) \<union> X = Vs G"
  apply safe
     apply (meson graph_diff_subset subset_iff vs_member)
    apply (metis insert_Diff insert_subset singl_in_diff_in_E vs_member)
  using assms(2) 
   apply blast
  by (meson singl_in_diffI singletonI vs_member_intro)

lemma el_vs_singleton_is_in_singleton:
  assumes "x \<in> Vs (singl_in_diff G X)"
  shows "{x} \<in> (singl_in_diff G X)"
  by (smt (verit, ccfv_SIG) CollectI assms singl_in_diff_member singletonD vs_member_elim)

lemma diff_disjoint_elements:
  assumes "graph_invar G"
  assumes "X \<subseteq> Vs G"
  shows "Vs (graph_diff G X) \<inter> Vs (singl_in_diff G X) = {}" 
    "Vs (graph_diff G X) \<inter> X = {}"
    "Vs (singl_in_diff G X) \<inter> X = {}"
    apply safe
    apply (metis connected_component_subset el_vs_singleton_is_in_singleton insert_subset 
      singl_in_diffE singl_in_diff_is_component singletonI)
   apply (metis IntI graph_diffE vs_member)
  using el_vs_singleton_is_in_singleton 
  by (metis Diff_eq_empty_iff Diff_subset assms(2) insert_subset singl_in_diffE)

lemma diff_card_is_sum_elements:
  assumes "graph_invar G"
  assumes "X \<subseteq> Vs G"
  shows "card (Vs (graph_diff G X)) + card (Vs (singl_in_diff G X)) + card X = card (Vs G)"
  using diff_is_union_elements[OF assms] diff_disjoint_elements[OF assms]
  by (metis Int_Un_distrib2 assms(1) card_Un_disjoint finite_Un sup_bot_right)

lemma singleton_set_card_eq_vertices:
  assumes "graph_invar G"
  assumes "X \<subseteq> Vs G"
  shows "card (Vs (singl_in_diff G X)) = card (singl_in_diff G X)"
proof -
  let ?A = "(singl_in_diff G X)"
  have "finite ?A" 
    by (metis Vs_def assms diff_is_union_elements finite_Un finite_UnionD)
  moreover have "\<forall>C \<in> ?A. finite C" 
    by(auto elim: singl_in_diffE)
  moreover have "\<forall> C1 \<in> ?A. \<forall> C2 \<in> ?A. C1 \<noteq> C2 \<longrightarrow> C1 \<inter> C2 = {}"   
    by(auto elim: singl_in_diffE)
  ultimately  have "sum card ?A = card (Vs ?A)" 
    using assms Vs_def card_Union_disjoint disjnt_def pairwise_def
    by (simp add: Vs_def card_Union_disjoint disjnt_def pairwise_def)
  also have "sum card ?A = card ?A" 
    by (metis card_eq_sum card_singl_in_diff_is_one sum.cong)
  finally show ?thesis 
    by presburger
qed

lemma finite_odd_components:
  assumes "graph_invar G"
  shows "finite (odd_components (graph_diff G X))" 
proof -
  have "finite (connected_components (graph_diff G X))" 
    by (meson Vs_subset assms finite_con_comps finite_subset graph_diff_subset)
  then show ?thesis 
    by (simp add: components_is_union_even_and_odd)
qed

lemma finite_odd_comps_in_diff:
  assumes "graph_invar G"
  assumes "X \<subseteq> Vs G" 
  shows "finite (odd_comps_in_diff G X)" 
  unfolding odd_comps_in_diff_def
  by (metis Vs_def assms diff_is_union_elements finite_Un 
      finite_UnionD finite_odd_components)

lemma graph_invar_diff:
  assumes "graph_invar G"
  shows "graph_invar (graph_diff G X)"
  by (meson assms graph_diff_subset graph_invar_subset)

lemma diff_odd_component_card_is_sum:
  assumes "graph_invar G"
  assumes "X \<subseteq> Vs G"
  shows "card (odd_comps_in_diff G X) = 
        card (odd_components (graph_diff G X)) + card (singl_in_diff G X)" 
  using finite_odd_comps_in_diff[of G X] 
  by (simp add: odd_components_inter_singl_empty 
      assms card_Un_disjoint odd_comps_in_diff_def)

lemma diff_odd_component_parity_sum:
  assumes "graph_invar G"
  assumes "X \<subseteq> Vs G"
  shows "even (card (odd_comps_in_diff G X) + card X ) = even (card (Vs G))"
proof -
  let ?odd = "(odd_components (graph_diff G X))"
  let ?singl = "(singl_in_diff G X)"
  let ?EwoX = "(graph_diff G X)"
  let ?allOdd = "odd_comps_in_diff G X"

  have "even (card ?allOdd + card X) =  even (card X + card ?odd + card ?singl)"
    using diff_odd_component_card_is_sum[of G X] assms 
    by presburger
  also have "\<dots> = even (card X + card (Vs ?EwoX) + card ?singl)" 
    using odd_components_eq_modulo_cardinality[of "?EwoX"] graph_invar_diff[of G X]
      assms(1)  by auto
  also have "\<dots> = even (card (Vs ?EwoX) + card (Vs ?singl) + card X)" 
    using singleton_set_card_eq_vertices[of G X] assms by presburger
  also have "\<dots>  = even (card (Vs G))"
    using diff_card_is_sum_elements[of G X] assms(1) assms(2) 
    by presburger
  finally show ?thesis by auto
qed

lemma diff_odd_component_parity':
  assumes "graph_invar G"
  assumes "X \<subseteq> Vs G"
  assumes  "card X \<le> card (odd_comps_in_diff G X)"
  shows "even (card (odd_comps_in_diff G X) - card X ) = even (card (Vs G))"
  using diff_odd_component_parity_sum[of G X] assms even_diff_nat not_less
  by force

lemma diff_odd_component_parity:
  assumes "graph_invar G"
  assumes "X \<subseteq> Vs G"
  assumes  "card X \<ge> card (odd_comps_in_diff G X)"
  shows "even (card X - card (odd_comps_in_diff G X)) = even (card (Vs G))"
  using diff_odd_component_parity_sum[of G X] assms even_diff_nat not_less
  by force

lemma path_in_comp:
  assumes "path G p"
  assumes "C \<in> connected_components G"
  assumes "last p \<in> C"
  shows "\<forall>x \<in> set p. x \<in> C" using assms(1) assms(3)
  by (metis assms(2) connected_components_closed' connected_components_member_eq empty_iff empty_set
      has_path_in_connected_component nonempty_path_walk_between path_subset_conn_comp subset_eq)

lemma exist_edge_in_component:
  assumes "graph_invar G"
  assumes "C \<in> connected_components G"
  assumes "x \<in> C" 
  obtains e where "e \<in> G" "x\<in> e" "e \<subseteq> C" 
proof - 
  have "C \<subseteq> Vs G" 
    by (simp add: assms(2) connected_component_subs_Vs)
  then obtain e where e: "e \<in> G" "x \<in> e" 
    by (meson assms(3) subsetD vs_member_elim)
  have "e \<subseteq> C" 
    by (metis assms connected_components_closed' e edge_subset_component)
  then show ?thesis 
    by (meson e that) 
qed  

lemma path_in_comp_edges:
  assumes "graph_invar G"
  assumes "path G p"
  assumes "C \<in> connected_components G"
  assumes "hd p \<in> C"
  assumes "(component_edges G C) \<noteq> {}" 
  shows "path (component_edges G C) p" using assms(2) assms(4) 
proof(induct p)
  case path0
  then show ?case 
    by simp
next
  case (path1 v)
  have "v \<in> C" 
    using path1.prems by auto
  then obtain e where  "e \<in> G \<and> v \<in> e \<and> e \<subseteq> C" 
    using exist_edge_in_component[of G C v]  assms(1) assms(3)
    by force
  then show ?case 
    using assms(1) edge_in_component_edges by auto
next
  case (path2 v v' vs)
  have "v \<in> C" 
    using path2.prems by auto
  have "v' \<in> C"
    by (metis \<open>v \<in> C\<close> assms(3) connected_components_eq' edge_in_component insert_subset path2.hyps(1))
  then have "{v, v'} \<subseteq> C" 
    by (simp add: \<open>v \<in> C\<close>)
  then have "{v, v'} \<in> (component_edges G C)"
    by (simp add: assms(1) edge_in_component_edges path2.hyps(1))
  then show "path (component_edges G C) (v # v' # vs)" 
    by (simp add: \<open>v' \<in> C\<close> path2.hyps(3))
qed

lemma graph_invar_union:
  assumes "finite A"
  assumes "\<forall>a \<in> A.  graph_invar a"
  assumes "\<forall>a \<in> A. finite (Vs a)"
  shows "graph_invar (\<Union>A)"
proof
  show "dblton_graph(\<Union> A)"
    using assms(2) by (fastforce simp: dblton_graph_def)
  then show "finite (Vs (\<Union> A))" 
    by (meson assms(1) assms(3) dblton_graph_finite_Vs finite_Union finite_Vs_then_finite)
qed

(*TODO: remove graph_invar from perfect matching, then we have the same definition.*)
(*
lemma "perfect_matching = More_Graph.perfect_matching"
*)

lemma perfect_matching_union:
  assumes "finite A"
  assumes "\<forall>a1 \<in>A.\<forall>a2\<in>A. a1 \<noteq> a2 \<longrightarrow> Vs a1 \<inter> Vs a2 = {}"
  assumes "\<forall>a \<in> A. \<exists>M. perfect_matching a M"
  assumes "\<forall> a \<in> A. {} \<notin> a" "\<forall>a \<in> A. finite (Vs a)"
  shows "\<exists>M. perfect_matching (\<Union>A) M"
proof -
  let ?Ms = "{Ms. \<exists>a \<in> A. Ms = {M. perfect_matching a M}}"
  (*have "\<forall>a \<in> A.  graph_invar a"
    using assms(3) perfect_matching_member
 
  then have "graph_invar (\<Union>A)" using graph_invar_union 
    by (simp add: graph_invar_union \<open>\<forall>a\<in>A. graph_invar a\<close> assms(1))*)
  (*have "\<forall>a \<in> A. finite (Vs a)" 
    by (simp add: \<open>\<forall>a\<in>A. graph_invar a\<close>)*)
  have disjoint_edges:"\<forall>a1 \<in>A.\<forall>a2\<in>A. a1 \<noteq> a2 \<longrightarrow> a1 \<inter> a2 = {}"
  proof(rule, rule, rule, rule ccontr, goal_cases)
    case (1 a1 a2)
    then obtain e where e: "e \<in> a1" "e \<in> a2" "e \<noteq> {}" 
      using assms(4) by auto
    hence "e \<subseteq> Vs a1" "e \<subseteq> Vs a2" "Vs a1 \<inter> Vs a2 \<noteq> {}"
      by auto
    thus False 
      by (simp add: "1"(1,2,3) assms(2))
  qed
  let ?f = "(\<lambda>a. {{M. perfect_matching a M}})"
  have "?Ms = (\<Union>a\<in>A. ?f a)" by blast

  then have "finite ?Ms" 
    using assms(1) by simp
  have "\<forall>a \<in> A. {M. perfect_matching a M} \<subseteq> {a1. a1 \<subseteq> a}" 
    by (simp add: Collect_mono perfect_matching_def)
  then have "\<forall>a \<in> A. finite {M. perfect_matching a M}"
    by (metis Vs_def \<open>\<forall>a\<in>A. finite (Vs a)\<close> finite_Collect_subsets finite_UnionD finite_subset)
  then have "finite (Vs ?Ms)"
    using assms(5)
    by (smt (verit) Vs_def \<open>finite ?Ms\<close> finite_Union mem_Collect_eq)
  have "\<forall>a1 \<in> A.\<forall>a2\<in>A. a1 \<noteq> a2 \<longrightarrow>
     {M. perfect_matching a1 M} \<inter> {M. perfect_matching a2 M} = {}" 
    apply (safe) 
    by (metis Int_absorb assms(2,4) ex_in_conv perfect_matching_def vs_member_intro)+
    (*by (met is assms(2) dblton_graph_def edges_are_Vs ex_in_conv inf.idem perfect_matching_member)+*)
    (*; metis Vs_subset assms(2) edges_are_Vs empty_iff le_iff_inf perfect_matchingE)+*)
  then have matchings_are_diff: "\<forall>a1 \<in> ?Ms.\<forall>a2\<in>?Ms. a1 \<noteq> a2 \<longrightarrow> a1 \<inter> a2 = {}" 
    by force
  have "\<forall>a\<in> ?Ms. \<exists>b\<in> Vs ?Ms. b \<in> a" 
    by (smt (z3) assms(3) mem_Collect_eq vs_member_intro)
  then obtain C where C_sub_Ms:"C\<subseteq> Vs ?Ms \<and> (\<forall>Ms\<in> ?Ms. \<exists>!M\<in>C. M \<in> Ms)"
    using ex_subset_same_elem_card[of ?Ms] matchings_are_diff \<open>finite (Vs ?Ms)\<close> \<open>finite ?Ms\<close> by presburger
  have "\<forall>c \<in> C. matching c"
  proof
    fix c
    assume "c \<in> C"
    then have "c \<in> Vs ?Ms" using C_sub_Ms by blast
    then have "\<exists>a\<in>A. perfect_matching a c" 
      by (smt (verit, best) mem_Collect_eq vs_member)
    then show "matching c"
      using perfect_matching_def by blast
  qed

  have "matching (\<Union>C)" 
    unfolding matching_def
  proof(safe)
    fix e1 X e2 Xa x xa
    {
      fix e1 X e2 Xa x xa
      assume assums:"e1 \<in> X" "X \<in> C" "e2 \<in> Xa" "Xa \<in> C" "x \<in> e1" "x \<notin> e2" "xa \<in> e1" "xa \<in> e2"
      show " xa \<in> {}"
      proof(cases "Xa = X")
        case True
        then show ?thesis using assums
          by (metis \<open>\<forall>c\<in>C. matching c\<close> matching_unique_match)
      next
        case False
        have "Xa \<in> Vs ?Ms" 
          using C_sub_Ms \<open>Xa \<in> C\<close> by blast
        then obtain a1 where a1_match:"a1 \<in> A \<and> perfect_matching a1 Xa"
          by (smt (verit) mem_Collect_eq vs_member)
        have "X \<in> Vs ?Ms" 
          using C_sub_Ms \<open>X \<in> C\<close> by blast
        then obtain a2 where a2_match:"a2 \<in> A \<and> perfect_matching a2 X"
          by (smt (verit) mem_Collect_eq vs_member)
        have "a1 \<noteq> a2" 
          using C_sub_Ms False \<open>X \<in> C\<close> \<open>Xa \<in> C\<close> a1_match a2_match by auto
        then have "a1 \<inter> a2 = {}" 
          by (simp add: a1_match a2_match disjoint_edges)

        then show ?thesis 
          using assums a1_match a2_match
          unfolding perfect_matching_def
          by (smt (verit, ccfv_threshold) IntI \<open>a1 \<noteq> a2\<close> assms(2) vs_member_intro)
      qed
    }
    then show "e1 \<in> X \<Longrightarrow> X \<in> C \<Longrightarrow> e2 \<in> Xa \<Longrightarrow> Xa \<in> C \<Longrightarrow> x \<in> e2 \<Longrightarrow>
       x \<notin> e1 \<Longrightarrow> xa \<in> e1 \<Longrightarrow> xa \<in> e2 \<Longrightarrow> xa \<in> {}"
      by blast
  qed   
  have "\<Union>C \<subseteq> \<Union>A"
  proof
    fix x
    assume "x \<in> \<Union>C"
    then obtain c where "c\<in>C \<and> x \<in> c" by auto
    then have "c \<in> Vs ?Ms" 
      using C_sub_Ms by blast
    then obtain a where "a\<in>A \<and> perfect_matching a c" 
      by (smt (verit, best) mem_Collect_eq vs_member)
    then show "x \<in> \<Union>A" 
      using \<open>a \<in> A \<and> perfect_matching a c\<close> \<open>c \<in> C \<and> x \<in> c\<close>
      by (meson UnionI perfect_matchingE subsetD)
  qed
  have "Vs (\<Union>C) = Vs (\<Union>A)"
  proof(safe)
    fix x 
    assume "x \<in> Vs (\<Union> A)" 
    then obtain e where "e \<in> (\<Union> A) \<and> x \<in> e"
      by (meson vs_member_elim)
    then obtain a where "a \<in> A \<and> e \<in> a" by auto
    then obtain c where "c \<in> C \<and> perfect_matching a c" 
      by (metis (mono_tags, lifting) C_sub_Ms mem_Collect_eq)
    then have "x \<in> Vs c" 
      using \<open>a \<in> A \<and> e \<in> a\<close> \<open>e \<in> \<Union> A \<and> x \<in> e\<close> 
      by (metis perfect_matchingE vs_member_intro)
    then show "x \<in> Vs (\<Union> C)" 
      by (metis Vs_def \<open>c \<in> C \<and> perfect_matching a c\<close> vs_member)
  qed (meson Vs_subset \<open>\<Union> C \<subseteq> \<Union> A\<close> subsetD)
  then have "perfect_matching (\<Union> A) (\<Union> C)" 
    by (simp add: \<open>\<Union> C \<subseteq> \<Union> A\<close>  \<open>matching (\<Union> C)\<close> perfect_matchingI)
  then show ?thesis by auto
qed

lemma vs_connected_component:
  assumes "graph_invar A"
  assumes "C \<in> connected_components A"
  shows "Vs (component_edges A C) = C"
proof(safe)
  {
    fix x
    assume "x \<in> Vs (component_edges A C)"
    then obtain e where "x \<in> e \<and> e \<in> (component_edges A C)" 
      by (meson vs_member_elim)
    then have "e \<subseteq> C" 
      by (smt (verit, best) component_edges_def mem_Collect_eq)
    then show "x \<in> C"
      by (meson \<open>x \<in> e \<and> e \<in> component_edges A C\<close> subsetD)
  }
  fix x
  assume "x \<in> C"
  then have "x \<in> Vs A" 
    by (meson assms connected_comp_verts_in_verts)
  then obtain e where "x \<in> e \<and> e \<in> A" 
    by (meson vs_member_elim)
  then obtain y where "e = {x, y}" 
    using assms(1) by fastforce
  then have "y \<in> C"
    by (metis \<open>x \<in> C\<close> \<open>x \<in> e \<and> e \<in> A\<close> assms(2) connected_components_closed' in_con_comp_insert insert_Diff)
  then have "e \<subseteq> C" 
    by (simp add: \<open>e = {x, y}\<close> \<open>x \<in> C\<close>)
  then have "e \<in> (component_edges A C)" 
    by (simp add: \<open>x \<in> e \<and> e \<in> A\<close> assms(1) edge_in_component_edges)
  then show "x \<in> Vs (component_edges A C)" 
    using \<open>x \<in> e \<and> e \<in> A\<close> by blast
qed

lemma components_edges_all:
  assumes "graph_invar A"
  shows "A = \<Union> (components_edges A)"
proof(safe)
  {
    fix e
    assume "e \<in> A"
    obtain C where "C \<in> connected_components A \<and> e \<subseteq> C"
      using edge_in_component
      by (metis \<open>e \<in> A\<close> assms dblton_graphE)
    then have "e \<in> component_edges A C" unfolding component_edges_def 
      using \<open>e \<in> A\<close> assms
      by blast
    then show "e \<in> \<Union> (components_edges A)" 
      by (simp add: \<open>e \<in> A\<close> assms graph_component_edges_partition)
  }

  fix e C'
  assume "C' \<in> (components_edges A)" "e \<in> C'"
  then show "e \<in> A"  
    using  assms graph_component_edges_partition by fastforce
qed


lemma perfect_matching_union_components:
  assumes "graph_invar A"
  assumes "\<forall>a \<in> connected_components A. \<exists>M. perfect_matching (component_edges A a) M"
  shows "\<exists>M. perfect_matching A M"
proof -
  have "finite (components_edges A)" 
    by (metis Vs_def assms(1) finite_UnionD graph_component_edges_partition)
  let ?E = "(components_edges A)" 
  have "\<forall>a \<in> ?E. \<exists>M. perfect_matching a M" using assms(2) unfolding components_edges_def
    by blast
  have " \<forall>a1\<in>?E. \<forall>a2\<in>?E. a1 \<noteq> a2 \<longrightarrow> Vs a1 \<inter> Vs a2 = {}"
  proof
    fix a1
    assume "a1 \<in> ?E"
    then obtain C1 where "C1 \<in> connected_components A \<and> a1 = component_edges A C1"
      by (smt (verit) components_edges_def mem_Collect_eq)
    then have "Vs a1 = C1" 
      by (simp add: assms(1) vs_connected_component)
    show "\<forall>a2\<in>?E. a1 \<noteq> a2 \<longrightarrow> Vs a1 \<inter> Vs a2 = {}" 
    proof
      fix a2
      assume "a2 \<in> ?E"
      then obtain C2 where "C2 \<in> connected_components A \<and> a2 = component_edges A C2"
        by (smt (verit) components_edges_def mem_Collect_eq)
      then have "Vs a2 = C2" 
        by (simp add: assms(1) vs_connected_component)
      have "C1 \<noteq> C2 \<longrightarrow> C1 \<inter> C2 = {}" 
        by (meson \<open>C1 \<in> connected_components A \<and> a1 = component_edges A C1\<close> \<open>C2 \<in> connected_components A \<and> a2 = component_edges A C2\<close> connected_components_disj)

      then show "a1 \<noteq> a2 \<longrightarrow> Vs a1 \<inter> Vs a2 = {}" 
        using \<open>C1 \<in> connected_components A \<and> a1 = component_edges A C1\<close> \<open>C2 \<in> connected_components A \<and> a2 = component_edges A C2\<close> \<open>Vs a1 = C1\<close> \<open>Vs a2 = C2\<close> 

        by force
    qed
  qed
  have A_is_component_edges_Union_A: "A = \<Union>?E" 
    using assms(1) components_edges_all by blast  
  then show "\<exists>M. perfect_matching A M"
    using perfect_matching_union[of ?E]
          `finite ?E` ` \<forall>a1\<in>?E. \<forall>a2\<in>?E. a1 \<noteq> a2 \<longrightarrow> Vs a1 \<inter> Vs a2 = {}` 
          `\<forall>a \<in> ?E. \<exists>M. perfect_matching a M`  assms(1)
         components_edges_image_Vs[of A] finite_UN[of "components_edges A" Vs] 
    by(subst A_is_component_edges_Union_A)
      (fastforce intro!:  perfect_matching_union[of ?E] simp add: graph_component_partition)
qed

lemma graph_diff_empty:
  shows "G = graph_diff G {}" 
  unfolding graph_diff_def by auto

lemma vertices_edges_in_same_component:
  assumes "{x, y} \<in> G"
  shows "y \<in> connected_component G x"
  by (meson assms(1) edges_are_walks has_path_in_connected_component)

lemma graph_diff_of_empty: 
  "graph_diff {} X = {}"
  using graph_diff_subset by auto

lemma empty_graph_odd_components:
  shows "odd_comps_in_diff {} X = {}" 
  unfolding odd_comps_in_diff_def
  apply safe
   apply(elim odd_componentsE odd_componentE )
   apply (metis empty_iff graph_diff_of_empty vs_member_elim)
  apply(elim singl_in_diffE)
  by (simp add: graph_diff_of_empty)

lemma component_edges_singleton_is_empty:
  assumes "graph_invar G" 
  shows "component_edges G {x} = {}"
  unfolding component_edges_def
  using assms by fastforce

lemma component_edges_subset:
  assumes "Y \<subseteq> C"
  shows "component_edges G Y \<subseteq> component_edges G C"
  unfolding component_edges_def
  by (smt (verit, ccfv_SIG) Collect_mono_iff assms(1) subset_trans)

lemma graph_diff_is_contained_in_set:
  assumes "Y \<subseteq> X"
  shows "graph_diff G X \<subseteq> graph_diff G Y"
  unfolding graph_diff_def 
  using assms by auto

lemma add_subset_change_odd_components:
  assumes "graph_invar G"
  assumes "X \<subseteq> Vs G"
  assumes "C \<in> (odd_comps_in_diff G X)"
  assumes "Y \<subseteq> C"
  assumes "Y \<noteq> {}"
  shows "odd_comps_in_diff G (X\<union>Y) = ((odd_comps_in_diff G X) - {C}) \<union>
    odd_comps_in_diff (component_edges (graph_diff G X) C) Y"
proof(cases "C \<in> singl_in_diff G X")
  case True
  then have "C = Y" unfolding singl_in_diff_def
    using assms(5) assms(4) by blast

  then obtain x where singl_x:"C = {x}" "x \<in> Vs G" "x \<notin> X" "x \<notin> Vs (graph_diff G X)"
    by (metis True singl_in_diffE)
  then have "Y = {x}" 
    by (simp add: \<open>C = Y\<close>)

  then have "(graph_diff G X) = (graph_diff G (X\<union>{x}))" 
    using `x \<notin> Vs (graph_diff G X)`
    unfolding graph_diff_def   
    by blast 

  then have "(odd_components (graph_diff G X)) = (odd_components (graph_diff G (X\<union>{x})))"
    by auto
  have "(singl_in_diff G X) - {{x}} = singl_in_diff G (X \<union> {x})"
    unfolding singl_in_diff_def
    using \<open>graph_diff G X = graph_diff G (X \<union> {x})\<close>         
    apply safe 
     apply (metis Un_iff singletonD)
    by metis
  have "{x} \<notin> (odd_components (graph_diff G X))" 
    using odd_components_elem_in_E singl_x(4) by blast
  then have "odd_comps_in_diff G (X\<union>{x}) = ((odd_comps_in_diff G X) - {{x}})"
    unfolding odd_comps_in_diff_def 
    by (simp add: Un_Diff \<open>graph_diff G X = graph_diff G (X \<union> {x})\<close> 
        \<open>singl_in_diff G X - {{x}} = singl_in_diff G (X \<union> {x})\<close>)


  have "(component_edges (graph_diff G X) C) = {}" 
    by (smt (verit, best) assms(1) component_edges_singleton_is_empty graph_invar_diff singl_x(1))
  then have "odd_comps_in_diff (component_edges (graph_diff G X) C) Y = {}" 
    by (simp add: empty_graph_odd_components)

  then show ?thesis unfolding odd_comps_in_diff_def  
    by (metis \<open>C = Y\<close> \<open>odd_comps_in_diff G (X \<union> {x}) = odd_comps_in_diff G X - {{x}}\<close> odd_comps_in_diff_def singl_x(1) sup_bot_right)
next
  case False
  then have "C \<in> odd_components (graph_diff G X)" 
    by (meson assms(3) odd_comps_in_diffE)
  then have odd_C: "odd_component (graph_diff G X) C" 
    using odd_componentsE by blast
  show "odd_comps_in_diff G (X\<union>Y) = ((odd_comps_in_diff G X) - {C}) \<union>
    odd_comps_in_diff (component_edges (graph_diff G X) C) Y" 
  proof 
    show " odd_comps_in_diff G (X \<union> Y) \<subseteq> odd_comps_in_diff G X - {C} \<union>
       odd_comps_in_diff (component_edges (graph_diff G X) C) Y"
    proof
      fix C'
      assume asmC':"C' \<in> odd_comps_in_diff G (X \<union> Y)"
      then have "C' \<noteq> {}" 
        using odd_components_nonempty by blast
      then obtain c where "c \<in> C'" by auto
      then have conn_compC':"connected_component (graph_diff G (X \<union> Y)) c = C'"
        using odd_comps_in_diff_is_component 
        by (metis asmC')

      show "C' \<in> odd_comps_in_diff G X - {C} \<union>
              odd_comps_in_diff (component_edges (graph_diff G X) C) Y"
      proof(cases "c \<in> C")
        case True
        then have conn_compC: "connected_component (graph_diff G X) c = C" 
          by (meson assms(3) odd_comps_in_diff_is_component)
        then have "c \<in> Vs (graph_diff G X)" 
          using True \<open>C \<in> odd_components (graph_diff G X)\<close> odd_components_elem_in_E by auto

        then obtain e where e: "e \<in> (graph_diff G X)" "c \<in> e"  
          by (meson vs_member_elim)
        then have "e \<subseteq> C"
          using edge_subset_component[of "(graph_diff G X)" e c]
          by (metis conn_compC assms(1) graph_invar_diff)
        have "C' = connected_component (graph_diff G (X\<union> Y)) c" 
          by (simp add: conn_compC')

        have "connected_component (graph_diff G (X \<union> Y)) c = 
      connected_component (graph_diff (component_edges (graph_diff G X) C) Y) c"
        proof(safe)
          {
            fix x
            assume asm:"x \<in> connected_component (graph_diff G (X\<union> Y)) c"
            show "x \<in> connected_component (graph_diff (component_edges (graph_diff G X) C) Y) c"
            proof(cases "x = c")
              case True
              then show ?thesis 
                by (simp add: in_own_connected_component)
            next
              case False
              then have "(\<exists>p. walk_betw (graph_diff G (X\<union> Y)) x p c)"
                unfolding connected_component_def 
                by (metis asm connected_components_member_sym in_con_comp_has_walk)
              then obtain p where p_walk:"walk_betw (graph_diff G (X\<union> Y)) x p c" 
                by auto
              then have "last p = c"
                by (simp add: walk_between_nonempty_pathD(4))
              then have "path (graph_diff G (X\<union> Y)) p" 
                using p_walk unfolding walk_betw_def  by auto
              then have "\<forall>z \<in> set p.  z \<in> C \<and>
                   z \<in> connected_component (graph_diff (component_edges (graph_diff G X) C) Y) c"
                using `last p = c`
              proof(induct p)
                case path0
                then show ?case 
                  by auto
              next
                case (path1 v)
                then show ?case 
                  by (simp add: True in_own_connected_component)
              next
                case (path2 v v' vs)
                have "v' \<in> C" 
                  by (metis last_ConsR list.set_intros(1) 
                      list.simps(3) path2.hyps(3) path2.prems)
                have "{v, v'} \<inter> (X\<union>Y) = {}" 
                  by (meson graph_diffE path2.hyps(1))
                then have "{v, v'} \<inter> X = {}" 
                  by (simp add: Int_Un_distrib)
                then have "{v, v'} \<in> (graph_diff G (X))"   
                  by (meson graph_diffE graph_diffI path2.hyps(1))
                then have "v \<in> C" 
                  by (metis \<open>v' \<in> C\<close> conn_compC connected_components_member_eq insert_commute 
                      vertices_edges_in_same_component)
                then have "{v, v'} \<in> (component_edges (graph_diff G X) C)"
                  using \<open>v' \<in> C\<close> \<open>{v, v'} \<in> graph_diff G X\<close> component_edges_def by blast     
                then have "{v, v'} \<in> (graph_diff (component_edges (graph_diff G X) C) Y)"
                  using \<open>{v, v'} \<inter> (X \<union> Y) = {}\<close> 
                  by (simp add: graph_diffI)       
                then have "v' \<in> connected_component 
                                (graph_diff (component_edges (graph_diff G X) C) Y) c" 
                  by (metis last_ConsR list.set_intros(1) list.simps(3) path2.hyps(3) 
                      path2.prems)
                then have "v \<in> connected_component 
                                (graph_diff (component_edges (graph_diff G X) C) Y) c"
                  by (metis \<open>{v, v'} \<in> graph_diff (component_edges (graph_diff G X) C) Y\<close> 
                      connected_components_member_eq insert_commute 
                      vertices_edges_in_same_component)
                then show ?case 
                  by (metis \<open>v \<in> C\<close> last_ConsR list.simps(3) path2.hyps(3) path2.prems set_ConsD)
              qed
              then show "x \<in> connected_component 
                          (graph_diff (component_edges (graph_diff G X) C) Y) c"
                by (metis list.set_sel(1) p_walk walk_betw_def)
            qed
          }
          fix x
          assume asm:"x \<in> connected_component (graph_diff (component_edges (graph_diff G X) C) Y) c" 
          show " x \<in> connected_component (graph_diff G (X \<union> Y)) c"
          proof(cases "x = c")
            case True
            then show ?thesis 
              by (simp add: in_own_connected_component)
          next
            case False
            then have "(\<exists>p. walk_betw  (graph_diff (component_edges (graph_diff G X) C) Y) x p c)"
              unfolding connected_component_def 
              by (metis asm connected_components_member_sym in_con_comp_has_walk)
            then obtain p where p_walk:
              "walk_betw  (graph_diff (component_edges (graph_diff G X) C) Y) x p c" 
              by auto
            then have "last p = c"
              by (simp add: walk_between_nonempty_pathD(4)) 
            then have "path  (graph_diff (component_edges (graph_diff G X) C) Y) p" 
              using p_walk unfolding walk_betw_def  by auto
            then have "\<forall>z \<in> set p. z \<in> connected_component (graph_diff G (X \<union> Y)) c"
              using `last p = c`
            proof(induct p) 
              case path0
              then show ?case 
                by auto
            next
              case (path1 v)
              then show ?case 
                using \<open>C' = connected_component (graph_diff G (X \<union> Y)) c\<close> \<open>c \<in> C'\<close> by auto

            next
              case (path2 v v' vs)
              have "last (v' # vs) = c" 
                using path2.prems 
                by auto
              have in_c: "\<forall>z\<in>set (v' # vs). z \<in> connected_component (graph_diff G (X \<union> Y)) c" 
                using \<open>last (v' # vs) = c\<close> path2.hyps(3) by blast
              have "{v, v'} \<in> (graph_diff (component_edges (graph_diff G X) C) Y)" 
                by (simp add: path2.hyps(1))
              then have "{v, v'} \<inter> Y = {}" 
                unfolding graph_diff_def 
                by fastforce
              have "{v, v'} \<in>  (component_edges (graph_diff G X) C)" 
                using graph_diff_subset path2.hyps(1) by blast
              then have "{v, v'} \<in> (graph_diff G X)" 
                using component_edges_subset  Connected_Components.component_edges_subset 
                      insert_Diff insert_subset
                by blast
              then have "{v, v'} \<inter> X = {}"
                unfolding graph_diff_def  
                by fastforce
              then have "{v, v'} \<in> (graph_diff G (X\<union>Y))"
                unfolding graph_diff_def 
                using `{v, v'} \<inter> Y = {}` \<open>{v, v'} \<in> graph_diff G X\<close> graph_diff_def by fastforce
              then have "v' \<in> connected_component (graph_diff G (X\<union>Y)) c" 
                by (simp add: in_c)
              then have "v \<in> connected_component (graph_diff G (X\<union>Y)) c"
                by (metis \<open>{v, v'} \<in> graph_diff G (X \<union> Y)\<close> connected_components_member_eq 
                    connected_components_member_sym vertices_edges_in_same_component)
              then show ?case 
                using in_c by fastforce
            qed 
            then show ?thesis 
              by (metis list.set_sel(1) p_walk walk_betw_def)
          qed
        qed
        then have c_in_diff:
          "connected_component (graph_diff (component_edges (graph_diff G X) C) Y) c = C'"
          using conn_compC' by presburger
        have "odd (card C')" 
          using asmC' diff_odd_compoenent_has_odd_card by auto
        have c_in_C: "c \<in> Vs (component_edges (graph_diff G X) C)" 
          by (smt (verit, ccfv_SIG) \<open>e \<subseteq> C\<close> assms(1) e edge_in_component_edges 
              graph_invar_diff vs_member)
        have "c \<notin> Y"
          by (meson \<open>c \<in> C'\<close> asmC' disjoint_iff_not_equal 
              odd_comps_in_diff_not_in_X subsetD sup_ge2)
        then have "c \<in> Vs (component_edges (graph_diff G X) C) - Y" 
          using c_in_C by blast
        then have "C' \<in> odd_comps_in_diff (component_edges (graph_diff G X) C) Y"
          using c_in_diff \<open>odd (card C')\<close>  by (meson odd_comps_in_diff_are_componentsI)
        then show "C' \<in> odd_comps_in_diff G X - {C} \<union>
                   odd_comps_in_diff (component_edges (graph_diff G X) C) Y" 
          by (simp add: odd_comps_in_diff_def)
      next
        case False
        then  have "c \<notin> C" by auto
        have "connected_component (graph_diff G X) c = connected_component (graph_diff G (X \<union> Y)) c"
        proof(safe)
          {
            fix x
            assume asmx:"x \<in> connected_component (graph_diff G X) c"
            show " x \<in> connected_component (graph_diff G (X \<union> Y)) c"
            proof(cases "x = c")
              case True
              then show ?thesis
                by (simp add: in_own_connected_component)
            next
              case False
              then have "\<exists>p. walk_betw (graph_diff G X) x p c"
                unfolding connected_component_def 
                by (metis asmx connected_components_member_sym in_con_comp_has_walk)
              then obtain p where p_walk:"walk_betw (graph_diff G X) x p c" by auto
              then have "last p = c"
                by (simp add: walk_between_nonempty_pathD(4))
              then have "path (graph_diff G X) p" 
                using p_walk unfolding walk_betw_def  by auto
              then have "\<forall>z \<in> set p. z \<in> C' \<and> z \<notin> C \<and> z \<in> connected_component (graph_diff G X) c"
                using `last p = c`
              proof(induct p) 
                case path0
                then show ?case 
                  by auto
              next
                case (path1 v)
                then show ?case 
                  using \<open>c \<in> C'\<close> \<open>c \<notin> C\<close> 
                  by (metis empty_iff empty_set in_own_connected_component last_ConsL set_ConsD)
              next
                case (path2 v v' vs)
                have "last (v' # vs) = c" 
                  using path2.prems 
                  by auto
                have zhyps: "\<forall>z\<in>set (v' # vs). z \<in> C' \<and> z \<notin> C \<and> 
                      z \<in> connected_component (graph_diff G X) c" 
                  using \<open>last (v' # vs) = c\<close> path2.hyps(3) by blast
                have "{v, v'} \<in> (graph_diff G X)" 
                  by (simp add: path2.hyps(1))
                then have "v' \<in> connected_component (graph_diff G X) c" 
                  by (simp add: zhyps)
                then have "v \<in> connected_component (graph_diff G X) v'"
                  by (meson connected_components_member_sym path2.hyps(1) 
                      vertices_edges_in_same_component)
                then have "v \<in> connected_component (graph_diff G X) c"
                  by (meson \<open>v' \<in> connected_component (graph_diff G X) c\<close> 
                      connected_components_member_trans)
                then have "v \<notin> C" 
                  by (metis assms(3) connected_components_member_eq list.set_intros(1)
                      odd_comps_in_diff_is_component zhyps)
                then have "v \<notin> Y" 
                  using assms(4) by blast
                have "v' \<notin> Y" 
                  by (meson zhyps assms(4) list.set_intros(1) subsetD)
                then have "{v, v'} \<inter> (Y) = {}" 
                  by (simp add: \<open>v \<notin> Y\<close>)
                have "{v, v'} \<inter> X = {}"
                  using `{v, v'} \<in> (graph_diff G X)`
                  unfolding graph_diff_def  
                  by fastforce
                then have "{v, v'} \<inter> (X\<union>Y) = {}" 
                  by (simp add: Int_Un_distrib \<open>{v, v'} \<inter> Y = {}\<close>)
                then have "{v, v'} \<in> (graph_diff G (X \<union> Y))" 
                  by (metis (mono_tags, lifting) graph_diff_def mem_Collect_eq path2.hyps(1))
                then have "v \<in> C'" 
                  by (metis conn_compC' connected_components_member_trans insert_commute
                      list.set_intros(1) vertices_edges_in_same_component zhyps)
                then show ?case 
                  using \<open>v \<in> connected_component (graph_diff G X) c\<close> \<open>v \<notin> C\<close> zhyps by auto
              qed
              then have "x \<in> C' \<and> x \<notin> C \<and> x \<in> connected_component (graph_diff G X) c" 
                by (metis list.set_sel(1) p_walk walk_betw_def)
              then show " x \<in> connected_component (graph_diff G (X \<union> Y)) c" 
                using conn_compC' by auto
            qed
          }
          fix x
          assume asmx:"x \<in> connected_component (graph_diff G (X \<union> Y)) c"
          show " x \<in> connected_component (graph_diff G X) c"
          proof(cases "x = c")
            case True
            then show ?thesis 
              by (simp add: in_own_connected_component)
          next
            case False
            then have "\<exists>p. walk_betw (graph_diff G (X \<union> Y)) x p c"
              unfolding connected_component_def
              by (metis asmx connected_components_member_sym in_con_comp_has_walk)
            then obtain p where p_walk:"walk_betw (graph_diff G (X \<union> Y)) x p c" 
              by auto
            then have "last p = c"
              by (simp add: walk_between_nonempty_pathD(4))
            then have "path (graph_diff G (X \<union> Y)) p" 
              using p_walk unfolding walk_betw_def by auto
            then have "\<forall>z \<in> set p. z \<in> connected_component (graph_diff G X) c"
              using `last p = c`
            proof(induct p) 
              case path0
              then show ?case 
                by auto
            next
              case (path1 v)
              then show ?case 
                using \<open>c \<in> C'\<close> \<open>c \<notin> C\<close> 
                by (metis empty_iff empty_set in_own_connected_component last_ConsL set_ConsD)
            next
              case (path2 v v' vs)
              have "last (v' # vs) = c" 
                using path2.prems 
                by auto
              have zhyps:"\<forall>z\<in>set (v' # vs). z \<in> connected_component (graph_diff G X) c" 
                using \<open>last (v' # vs) = c\<close> path2.hyps(3) by blast
              have "{v, v'} \<in> (graph_diff G (X \<union> Y))" 
                by (simp add: path2.hyps(1))
              then have "{v, v'} \<in> (graph_diff G (X))"
                unfolding graph_diff_def  
                by blast
              then have "v' \<in> connected_component (graph_diff G X) c" 
                by (simp add: zhyps)
              then show ?case 
                by (metis zhyps \<open>{v, v'} \<in> graph_diff G X\<close> connected_components_member_eq
                    insert_commute set_ConsD vertices_edges_in_same_component)
            qed
            then show " x \<in> connected_component (graph_diff G (X)) c" 
              by (metis list.set_sel(1) p_walk walk_betw_def)
          qed
        qed
        then have conn_compC: "connected_component (graph_diff G X) c = C'" 
          using conn_compC' by fastforce
        have "C' \<in> odd_comps_in_diff G X"
        proof(cases "C' \<in> singl_in_diff G (X \<union> Y)")
          case True
          then have "C' = {c}" 
            apply(elim singl_in_diffE)
            using \<open>c \<in> C'\<close> by fastforce
          have "connected_component (graph_diff G X) c = {c}" 
            by (simp add: \<open>C' = {c}\<close> conn_compC)
          have "c \<notin> Vs (graph_diff G X)"
          proof(rule ccontr)
            assume " \<not> c \<notin> Vs (graph_diff G X)"
            then have "\<exists> e. c \<in> e \<and> e \<in> (graph_diff G X)" 
              by (meson vs_member_elim)
            then obtain e where e: "c \<in> e \<and> e \<in> (graph_diff G X)" 
              by auto
            then have "e \<subseteq> connected_component (graph_diff G X) c" 
              by (metis assms(1) edge_subset_component graph_invar_diff)
            then show False
              using \<open>connected_component (graph_diff G X) c = {c}\<close> assms(1) e graph_invar_diff
              by fastforce
          qed
          then have "C' \<in> singl_in_diff G X" 
            unfolding singl_in_diff_def 
            using \<open>C' = {c}\<close> asmC' component_in_E odd_comps_in_diff_not_in_X True by fastforce
          then show ?thesis
            unfolding odd_comps_in_diff_def 
            by simp
        next
          case False
          then have "C' \<in> odd_components (graph_diff G (X\<union>Y))" 
            by (metis UnE asmC' odd_comps_in_diff_def)
          then have "odd (card C')" 
            by (simp add: odd_components_def odd_component_def)
          have "c\<in>Vs (graph_diff G X)"
          proof(rule ccontr)
            assume "c \<notin> Vs (graph_diff G X)"
            have c_notin_U:"c \<notin>  Vs (graph_diff G (X\<union>Y))"
            proof(rule ccontr)
              assume " \<not> c \<notin> Vs (graph_diff G (X \<union> Y))"
              then have "\<exists>e. c \<in> e \<and> e \<in> (graph_diff G (X \<union> Y))" 
                by (meson vs_member_elim)
              then obtain e where e:"c \<in> e \<and> e \<in> graph_diff G (X \<union> Y)"
                by auto
              then have "e \<inter> (X \<union> Y) = {}" 
                by (simp add: graph_diff_def)
              then have "e \<inter> X = {}"
                by auto
              then have "e \<in> graph_diff G X" 
                unfolding graph_diff_def 
                using e graph_diff_member by fastforce
              then have "c \<in> Vs (graph_diff G X)" 
                using \<open>c \<in> e \<and> e \<in> graph_diff G (X \<union> Y)\<close> 
                by blast
              then show False 
                using \<open>c \<notin> Vs (graph_diff G X)\<close> by blast
            qed
            have "c \<notin> X \<union> Y" 
              by (metis IntI \<open>c \<in> C'\<close> asmC' empty_iff odd_comps_in_diff_not_in_X)
            then have "{c} \<in> singl_in_diff G (X \<union> Y)" 
              unfolding singl_in_diff_def 
              using \<open>c \<in> C'\<close> c_notin_U asmC' component_in_E by fastforce
            then have "{c} \<in> odd_comps_in_diff G (X \<union> Y)" 
              by (simp add: odd_comps_in_diff_def)
            then have "connected_component (graph_diff G (X \<union> Y)) c = {c}" 
              by (simp add: c_notin_U connected_components_notE_singletons)
            then have "C' = {c}" 
              by (simp add: conn_compC')
            then have "C' \<in> singl_in_diff G (X \<union> Y)" 
              by (simp add: \<open>{c} \<in> singl_in_diff G (X\<union>Y)\<close>)
            then show False 
              by (simp add: False)
          qed
          then have "C' \<in> odd_components (graph_diff G X)"
            unfolding odd_components_def 
            by (simp add: \<open>odd (card C')\<close> conn_compC odd_componentI)
          then show ?thesis 
            by (simp add: odd_comps_in_diff_def)
        qed
        then show "C' \<in> odd_comps_in_diff G X - {C} \<union>
                   odd_comps_in_diff (component_edges (graph_diff G X) C) Y"
          using False \<open>c \<in> C'\<close> by blast
      qed
    qed
    show " odd_comps_in_diff G X - {C} \<union> odd_comps_in_diff
     (component_edges (graph_diff G X) C) Y \<subseteq> odd_comps_in_diff G (X \<union> Y)"
    proof
      fix C'
      assume asmC'odd:"C' \<in> odd_comps_in_diff G X - {C} \<union> odd_comps_in_diff
              (component_edges (graph_diff G X) C) Y"
      show "C' \<in> odd_comps_in_diff G (X \<union> Y)"
      proof(cases "C' \<in> odd_comps_in_diff G X - {C}")
        case True
        then have "C' \<noteq> C" 
          by blast
        then have "C' \<inter> C = {}"
          by (metis Diff_iff True assms(3) diff_component_disjoint)
        have C'_odd: "C' \<in> odd_comps_in_diff G X" 
          using True by auto
        have "C' \<noteq> {}" 
          using C'_odd odd_components_nonempty by blast
        then obtain c where "c \<in> C'" 
          by blast
        then have conn_C':"connected_component (graph_diff G X) c = C'" 
          by (simp add: C'_odd assms(1) assms(3) odd_comps_in_diff_is_component)
        have "c \<notin> C" 
          using \<open>C' \<inter> C = {}\<close> \<open>c \<in> C'\<close> by blast
        have conn_same: "connected_component (graph_diff G X) c = 
                         connected_component (graph_diff G (X \<union> Y)) c"
        proof(safe)
          {
            fix x
            assume asmx:"x \<in> connected_component (graph_diff G X) c"
            show "x \<in> connected_component (graph_diff G (X \<union> Y)) c"
            proof(cases "x = c")
              case True
              then show ?thesis 
                by (simp add: in_own_connected_component)
            next
              case False
              then have "\<exists>p. walk_betw (graph_diff G X) x p c"
                unfolding connected_component_def 
                by (metis asmx connected_components_member_sym in_con_comp_has_walk)
              then obtain p where p_walk:"walk_betw (graph_diff G X) x p c"
                by auto
              then have "last p = c"
                by (simp add: walk_between_nonempty_pathD(4))
              then have "path (graph_diff G X) p" 
                using p_walk unfolding walk_betw_def  by auto
              then have "\<forall>z \<in> set p. z \<in> C' \<and> z \<notin> C \<and> z \<in> connected_component (graph_diff G (X\<union>Y)) c"
                using `last p = c`
              proof(induct p) 
                case path0
                then show ?case 
                  by auto
              next
                case (path1 v)
                then show ?case 
                  by (metis \<open>c \<in> C'\<close> \<open>c \<notin> C\<close> empty_iff empty_set in_own_connected_component 
                      last_ConsL set_ConsD)
              next
                case (path2 v v' vs)
                have "last (v' # vs) = c" 
                  using path2.prems by auto
                have zhyp: "\<forall>z\<in>set (v' # vs). z \<in> C' \<and> z \<notin> C \<and>
                             z \<in> connected_component (graph_diff G (X \<union> Y)) c" 
                  using \<open>last (v' # vs) = c\<close> path2.hyps(3) by blast
                have "{v, v'} \<in> (graph_diff G X)" 
                  by (simp add: path2.hyps(1))
                then have "{v, v'} \<inter> X = {}" 
                  by (metis (mono_tags, lifting) graph_diff_def mem_Collect_eq)
                then have v'_conn:"v' \<in> connected_component (graph_diff G X) c" 
                  by (simp add: conn_C' zhyp)
                then have "v \<in> connected_component (graph_diff G X) v'"
                  by (meson connected_components_member_sym path2.hyps(1) 
                      vertices_edges_in_same_component)
                then have "v \<notin> C" 
                  by (metis \<open>C' \<inter> C = {}\<close> conn_C' 
                      connected_components_member_eq disjoint_iff_not_equal v'_conn)
                then have "v \<notin> Y" 
                  using assms(4) by blast
                have "v' \<notin> Y" 
                  using assms(4) zhyp by auto
                then have "{v, v'} \<inter> Y = {}" 
                  by (simp add: \<open>v \<notin> Y\<close>)
                have "{v, v'} \<inter> X = {}"
                  using `{v, v'} \<in> (graph_diff G X)` 
                  unfolding graph_diff_def  
                  by fastforce
                then have "{v, v'} \<inter> (X \<union> Y) = {}" 
                  by (simp add: Int_Un_distrib \<open>{v, v'} \<inter> Y = {}\<close>)
                then have "{v, v'} \<in> (graph_diff G (X \<union> Y))" 
                  by (metis (mono_tags, lifting) graph_diff_def mem_Collect_eq path2.hyps(1))
                then show ?case 
                  by (metis \<open>v \<in> connected_component (graph_diff G X) v'\<close> \<open>v \<notin> C\<close> conn_C' 
                      connected_components_member_eq connected_components_member_sym 
                      list.set_intros(1) set_ConsD vertices_edges_in_same_component zhyp)
              qed
              then show "x \<in> connected_component (graph_diff G (X \<union> Y)) c" 
                by (metis list.set_sel(1) p_walk walk_betw_def)
            qed
          }
          fix x
          assume asmx: "x \<in> connected_component (graph_diff G (X \<union> Y)) c"
          show "x \<in> connected_component (graph_diff G X) c"
          proof(cases "x = c")
            case True
            then show ?thesis 
              by (simp add: in_own_connected_component)
          next 
            case False
            then have "\<exists>p. walk_betw (graph_diff G (X \<union> Y)) x p c"
              unfolding connected_component_def 
              by (metis asmx connected_components_member_sym in_con_comp_has_walk)
            then obtain p where p_walk:"walk_betw (graph_diff G (X \<union> Y)) x p c"
              by auto
            then have "last p = c"
              by (simp add: walk_between_nonempty_pathD(4))
            then have "path (graph_diff G (X \<union> Y)) p" 
              using p_walk unfolding walk_betw_def  by auto
            then have "\<forall>z \<in> set p. z \<in> connected_component (graph_diff G X) c"
              using `last p = c`
            proof(induct p) 
              case path0
              then show ?case 
                by auto
            next
              case (path1 v)
              then show ?case 
                using \<open>c \<in> C'\<close> \<open>c \<notin> C\<close> 
                by (metis empty_iff empty_set in_own_connected_component last_ConsL set_ConsD)
            next
              case (path2 v v' vs)
              have "last (v' # vs) = c" 
                using path2.prems 
                by auto
              have zhyp: "\<forall>z\<in>set (v' # vs). z \<in> connected_component (graph_diff G X) c" 
                using \<open>last (v' # vs) = c\<close> path2.hyps(3) by blast
              have "{v, v'} \<in> graph_diff G (X \<union> Y)" 
                by (simp add: path2.hyps(1))
              then have "{v, v'} \<in> graph_diff G X" 
                unfolding graph_diff_def  
                by blast
              then have "v' \<in> connected_component (graph_diff G X) c" 
                by (simp add: zhyp)
              then show ?case 
                by (metis zhyp \<open>{v, v'} \<in> graph_diff G X\<close> connected_components_member_eq 
                    insert_commute set_ConsD vertices_edges_in_same_component)
            qed
            then show "x \<in> connected_component (graph_diff G (X)) c" 
              by (metis list.set_sel(1) p_walk walk_betw_def)
          qed
        qed
        then have conn_diff_C':"connected_component (graph_diff G (X \<union> Y)) c = C'" 
          using conn_C' by presburger
        show "C' \<in> odd_comps_in_diff G (X \<union> Y)"
        proof(cases "C' \<in> singl_in_diff G X")
          case True
          then have "C' = {c}" 
            apply(elim singl_in_diffE)
            using \<open>c \<in> C'\<close> by fastforce
          then have comp_singl:"connected_component (graph_diff G (X \<union> Y)) c = {c}" 
            using conn_diff_C' by auto
          then have "c \<notin>  Vs (graph_diff G X)" 
            using True
            apply(elim singl_in_diffE)
            using \<open>c \<in> C'\<close> by blast
          have c_notin_diff:"c \<notin> Vs (graph_diff G (X \<union> Y))"
          proof(rule ccontr)
            assume "\<not> c \<notin> Vs (graph_diff G (X \<union> Y))"   
            then obtain e where e:"c \<in> e \<and> e \<in> (graph_diff G (X \<union> Y))"
              by (meson vs_member_elim)
            then have "e \<subseteq> connected_component (graph_diff G (X \<union> Y)) c"
              by (simp add: assms(1) edge_subset_component graph_invar_diff)
            then show False
              using assms(1) comp_singl e graph_invar_diff
              by fastforce 
          qed
          have "c \<notin> X \<union> Y" 
            by (metis C'_odd IntI Un_iff \<open>c \<in> C'\<close> \<open>c \<notin> C\<close> assms(4) empty_iff 
                odd_comps_in_diff_not_in_X subsetD)
          then have "{c} \<in> singl_in_diff G (X \<union> Y)" 
            by (meson C'_odd \<open>c \<in> C'\<close> c_notin_diff component_in_E singl_in_diffI subsetD)
          then have "C' \<in> singl_in_diff G (X\<union>Y)" 
            by (simp add: \<open>C' = {c}\<close>)
          then show ?thesis 
            by (simp add: odd_comps_in_diff_def)
        next
          case False
          then have "C' \<in> odd_components (graph_diff G X)" 
            using C'_odd odd_comps_in_diffE by blast
          then have "odd (card C')" 
            by (simp add: odd_components_def odd_component_def)
          have "c \<notin> X \<union> Y" 
            by (metis C'_odd IntI Un_iff \<open>c \<in> C'\<close> \<open>c \<notin> C\<close> assms(4) empty_iff 
                odd_comps_in_diff_not_in_X subsetD)
          have "c \<in> Vs (graph_diff G X)"
            using \<open>C' \<in> odd_components (graph_diff G X)\<close> \<open>c \<in> C'\<close> odd_components_elem_in_E by auto
          then obtain e where e:"c \<in> e \<and> e \<in> graph_diff G X" 
            by (meson vs_member_elim)
          then have e_unfold:"c \<in> e \<and> e \<in> G \<and> e \<inter> X = {}" 
            by (simp add: graph_diff_def)
          have "e \<subseteq> C'" 
            by (metis assms(1) conn_C' e edge_subset_component graph_invar_diff)
          then have "e \<inter> Y = {}" 
            using \<open>C' \<inter> C = {}\<close> assms(4) by blast
          then have "e \<inter> (X \<union> Y) = {}" 
            by (simp add: Int_Un_distrib e_unfold)
          then have "e \<in> graph_diff G (X \<union> Y)" 
            by (simp add: e_unfold graph_diff_def)
          then have "c\<in>Vs (graph_diff G (X \<union> Y))" 
            using e by blast
          then have "C' \<in> odd_components (graph_diff G (X \<union> Y))"
            unfolding odd_components_def
            by (simp add: \<open>odd (card C')\<close> conn_diff_C' odd_componentI)
          then show ?thesis 
            by (simp add: odd_comps_in_diff_def)
        qed 
      next
        case False
        then have C'diffY:"C' \<in> odd_comps_in_diff (component_edges (graph_diff G X) C) Y"
          using asmC'odd by blast
        let ?C = "(component_edges (graph_diff G X) C)"
        have "graph_invar ?C"
          by (meson Connected_Components.component_edges_subset assms(1) graph_invar_diff graph_invar_subset)
        have "C' \<subseteq> Vs ?C" 
          by (meson C'diffY component_in_E)
        have "Vs ?C \<subseteq> C"
          unfolding component_edges_def 
          by (smt (verit, ccfv_SIG) mem_Collect_eq subset_eq vs_member)
        then have "C' \<subseteq> C" 
          using \<open>C' \<subseteq> Vs ?C\<close> by auto
        have "C' \<inter> Y = {}" 
          using C'diffY odd_comps_in_diff_not_in_X by blast
        then have "C' \<noteq> {}" 
          using odd_components_nonempty \<open>C' \<in> odd_comps_in_diff ?C Y\<close> `graph_invar ?C` by fastforce
        then obtain c where "c \<in> C'"
          by blast
        then have conn_diffY:"connected_component (graph_diff ?C Y) c = C'"
          by (simp add: C'diffY odd_comps_in_diff_is_component)
        have "connected_component (graph_diff G (X \<union> Y)) c = 
              connected_component (graph_diff ?C Y) c"
        proof(safe)
          {
            fix x
            assume asmx:"x \<in> connected_component (graph_diff G (X \<union> Y)) c"
            show "x \<in>  connected_component (graph_diff ?C Y) c"
            proof(cases "x = c")
              case True
              then show ?thesis 
                by (simp add: in_own_connected_component)
            next
              case False
              then have "\<exists>p. walk_betw (graph_diff G (X \<union> Y)) x p c"
                unfolding connected_component_def 
                by (metis asmx connected_components_member_sym in_con_comp_has_walk)
              then obtain p where p_walk:"walk_betw (graph_diff G (X \<union> Y)) x p c"
                by auto
              then have "last p = c" 
                by (simp add: walk_between_nonempty_pathD(4))
              then have "path (graph_diff G (X \<union> Y)) p" 
                using p_walk unfolding walk_betw_def  by auto
              then have "\<forall>z \<in> set p. z \<in> C'"
                using `last p = c`
              proof(induct p)
                case path0
                then show ?case 
                  by auto
              next
                case (path1 v)
                then show ?case  
                  using \<open>c \<in> C'\<close> by auto
              next
                case (path2 v v' vs)
                have "last (v' # vs) = c" 
                  using path2.prems 
                  by auto
                have "\<forall>z\<in>set (v' # vs). z \<in> C' " 
                  using \<open>last (v' # vs) = c\<close> path2.hyps(3)
                  by fastforce
                have "{v, v'} \<in> graph_diff G (X \<union> Y)" 
                  by (simp add: path2.hyps(1))
                then have "{v, v'} \<inter> (X \<union>Y) = {}" 
                  by (meson graph_diffE)
                then have "{v, v'} \<inter> Y = {}"
                  by blast
                then have "{v, v'} \<inter> X = {}"
                  using `{v, v'} \<inter> (X \<union>Y) = {}` by blast
                then have "{v, v'} \<in> graph_diff G X" 
                  unfolding graph_diff_def 
                  using graph_diff_subset path2.hyps(1) by auto
                have "v' \<in> C'"
                  by (simp add: \<open>\<forall>z\<in>set (v' # vs). z \<in> C'\<close>)
                then have "v' \<in> C"
                  using \<open>C' \<subseteq> C\<close> by blast
                then have "C = connected_component (graph_diff G X) c" 
                  by (metis \<open>C' \<subseteq> C\<close> \<open>c \<in> C'\<close> assms(3) in_mono odd_comps_in_diff_is_component)
                then have "v' \<in> connected_component (graph_diff G X) c"
                  using \<open>v' \<in> C\<close> by blast
                then have "v \<in> C" 
                  by (metis \<open>v' \<in> C\<close> \<open>{v, v'} \<in> graph_diff G X\<close> assms(3) 
                      connected_components_member_sym odd_comps_in_diff_is_component
                      vertices_edges_in_same_component)
                then have "{v, v'} \<subseteq> C" 
                  by (simp add: \<open>v' \<in> C\<close>)
                then have "{v, v'} \<in> ?C" 
                  using component_edges_def \<open>{v, v'} \<in> graph_diff G X\<close> by fastforce
                then have vv':"{v, v'} \<in> graph_diff ?C Y" 
                  unfolding graph_diff_def using `{v, v'} \<inter> Y = {}` by blast
                then have "v' \<in> connected_component (graph_diff ?C Y) c" 
                  using \<open>v' \<in> C'\<close> conn_diffY by blast
                then have "v \<in> connected_component (graph_diff ?C Y) c" 
                  by (metis vv' connected_components_member_eq insert_commute
                    vertices_edges_in_same_component)
                then have "v \<in> C'" 
                  using conn_diffY by auto
                then show ?case 
                  using \<open>\<forall>z\<in>set (v' # vs). z \<in> C'\<close> by fastforce
              qed
              then show "x \<in> connected_component (graph_diff 
                                                  (component_edges (graph_diff G X) C) Y) c"
                by (metis conn_diffY list.set_sel(1) p_walk walk_betw_def)
            qed
          }
          fix x
          assume asm:"x \<in> connected_component (graph_diff (component_edges (graph_diff G X) C) Y) c" 
          show " x \<in> connected_component (graph_diff G (X \<union> Y)) c"
          proof(cases "x = c")
            case True
            then show ?thesis 
              by (simp add: in_own_connected_component)

          next
            case False
            then have "\<exists>p. walk_betw  (graph_diff (component_edges (graph_diff G X) C) Y) x p c"
              unfolding connected_component_def 
              by (metis asm connected_components_member_sym in_con_comp_has_walk)
            then obtain p where p_walk:
                "walk_betw  (graph_diff (component_edges (graph_diff G X) C) Y) x p c" 
              by auto
            then have "last p = c"
              by (simp add: walk_between_nonempty_pathD(4))
            then have "path (graph_diff (component_edges (graph_diff G X) C) Y) p" 
              using p_walk unfolding walk_betw_def by auto
            then have "\<forall>z \<in> set p. z \<in> connected_component (graph_diff G (X \<union> Y)) c"
              using `last p = c`
            proof(induct p) 
              case path0
              then show ?case 
                by auto
            next
              case (path1 v)
              then show ?case 
                by (metis empty_iff empty_set in_own_connected_component last_ConsL set_ConsD)
            next
              case (path2 v v' vs)
              have "last (v' # vs) = c" 
                using path2.prems 
                by auto
              have zhyp:"\<forall>z\<in>set (v' # vs). z \<in> connected_component (graph_diff G (X \<union> Y)) c" 
                using \<open>last (v' # vs) = c\<close> path2.hyps(3) by blast
              have "{v, v'} \<in> (graph_diff (component_edges (graph_diff G X) C) Y)" 
                by (simp add: path2.hyps(1))
              then have "{v, v'} \<inter> Y = {}" unfolding graph_diff_def 
                by fastforce
              have "{v, v'} \<in> (component_edges (graph_diff G X) C)" 
                using graph_diff_subset path2.hyps(1) by blast
              then have "{v, v'} \<in> (graph_diff G X)" 
                using Connected_Components.component_edges_subset by fastforce
              then have "{v, v'} \<inter> X = {}"
                unfolding graph_diff_def by fastforce
              then have "{v, v'} \<in> (graph_diff G (X \<union> Y))" 
                unfolding graph_diff_def 
                using `{v, v'} \<inter> Y = {}` \<open>{v, v'} \<in> graph_diff G X\<close> graph_diff_def by fastforce
              then have "v' \<in> connected_component (graph_diff G (X \<union> Y)) c" 
                by (simp add: zhyp)
              then have "v \<in> connected_component (graph_diff G (X \<union> Y)) c"
                by (meson \<open>{v, v'} \<in> graph_diff G (X \<union> Y)\<close> connected_components_member_sym 
                    connected_components_member_trans vertices_edges_in_same_component)
              then show ?case 
                using zhyp by fastforce
            qed 
            then show ?thesis 
              by (metis list.set_sel(1) p_walk walk_betw_def)
          qed
        qed
        then have connC'XY:"connected_component (graph_diff G (X \<union> Y)) c = C'"
          using conn_diffY by fastforce
        show " C' \<in> odd_comps_in_diff  G (X \<union> Y)"
        proof(cases "C' \<in> singl_in_diff ?C Y")
          case True
          then have "\<exists>v. C' = {v} \<and> v \<in> Vs ?C \<and> v \<notin> Y \<and> v \<notin> Vs (graph_diff ?C Y)"
            unfolding singl_in_diff_def by blast
          then have "C' = {c}" 
            using \<open>c \<in> C'\<close> by force
          then have "connected_component (graph_diff G (X\<union>Y)) c = {c}" 
            using connC'XY by fastforce
          have "c \<notin> Vs (graph_diff G (X \<union> Y))" 
          proof(rule ccontr)
            assume " \<not> c \<notin> Vs (graph_diff G (X \<union> Y))"
            then obtain e where e:"c \<in> e \<and> e \<in> (graph_diff G (X \<union> Y))"
              by (meson vs_member_elim)
            then have "e \<subseteq> connected_component (graph_diff G (X\<union>Y)) c"
              by (simp add: assms(1) edge_subset_component graph_invar_diff)
            then show False 
              using \<open>connected_component (graph_diff G (X \<union> Y)) c = {c}\<close> 
                assms(1) e graph_invar_diff by fastforce
          qed
          have "c \<notin> X \<union> Y" 
          by (metis Un_iff \<open>C' \<inter> Y = {}\<close> \<open>C' \<subseteq> C\<close> \<open>c \<in> C'\<close> assms(3) 
              odd_comps_in_diff_not_in_X disjoint_iff_not_equal subset_eq)
        then have "{c} \<in> singl_in_diff G (X \<union> Y)" 
          by (meson \<open>C' \<subseteq> C\<close> \<open>c \<in> C'\<close> \<open>c \<notin> Vs (graph_diff G (X \<union> Y))\<close> assms(3) 
              component_in_E singl_in_diffI subsetD)
          then have "C' \<in> singl_in_diff G (X \<union> Y)" 
            by (simp add: \<open>C' = {c}\<close>)
          then show ?thesis 
            by (simp add: odd_comps_in_diff_def)
        next
          case False
          then have C'_odd_diff:"C' \<in> odd_components (graph_diff ?C Y)" 
            using C'diffY by (simp add: odd_comps_in_diff_def)
          then have "odd (card C')" 
            by (simp add: odd_components_def odd_component_def)
          have "c \<notin> X \<union> Y" 
            by (metis UnE \<open>C' \<inter> Y = {}\<close> \<open>C' \<subseteq> C\<close> \<open>c \<in> C'\<close> assms(3) disjoint_iff_not_equal
                odd_comps_in_diff_not_in_X subset_eq)
          have "c \<in> Vs (graph_diff ?C Y)" 
            using False \<open>C' \<subseteq> Vs ?C\<close> \<open>c \<notin> X \<union> Y\<close> conn_diffY 
              connected_components_notE_singletons singl_in_diffI by fastforce
            then obtain e where e:"c \<in> e \<and> e \<in> graph_diff ?C Y" 
              by (meson vs_member_elim)
          then have "c \<in> e \<and> e \<in> ?C \<and> e \<inter> Y = {}" 
            by (simp add: graph_diff_def)
          then have "e \<subseteq> C'"
            by (metis \<open>graph_invar (component_edges (graph_diff G X) C)\<close> conn_diffY e edge_subset_component graph_invar_diff)
          then have "e \<inter> (X \<union> Y) = {}" 
            by (smt (z3) Int_Un_distrib Int_Un_eq(4) Un_Int_assoc_eq Un_absorb Un_commute \<open>C' \<subseteq> C\<close>
                \<open>c \<in> e \<and> e \<in> ?C \<and> e \<inter> Y = {}\<close> assms(3) odd_comps_in_diff_not_in_X subset_trans)
          have "e \<in> G" 
            using `c \<in> e \<and> e \<in> ?C \<and> e \<inter> Y = {}` Connected_Components.component_edges_subset 
                  graph_diff_member 
            by blast
          then have "e \<in> (graph_diff G (X \<union> Y))" 
            by (simp add: \<open>e \<inter> (X \<union> Y) = {}\<close> graph_diff_def)
          then have "c\<in>Vs (graph_diff G (X \<union> Y))" 
            using e by blast
          then have "C' \<in> odd_components (graph_diff G (X \<union> Y))" 
            unfolding odd_components_def odd_component_def
            using \<open>odd (card C')\<close> connC'XY by blast
          then show ?thesis 
            by (simp add: odd_comps_in_diff_def)
        qed 
      qed
    qed
  qed
qed

lemma odd_comps_in_diff_same_inter_vertices:
  assumes "graph_invar G"
  shows "odd_comps_in_diff G (Y \<inter> Vs G) = odd_comps_in_diff G Y"
proof -
  have "graph_diff G (Y \<inter> Vs G) = graph_diff G Y" 
    unfolding graph_diff_def by blast
  then have "singl_in_diff G (Y \<inter> Vs G) = singl_in_diff G Y" 
    unfolding singl_in_diff_def
    by (safe;simp)
  then show ?thesis 
    by (simp add: \<open>graph_diff G (Y \<inter> Vs G) = graph_diff G Y\<close> odd_comps_in_diff_def)
qed

end
