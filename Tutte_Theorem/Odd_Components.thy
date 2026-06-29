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
proof
  fix u
  assume "u \<in> connected_component G v"
  then have "u \<in> Vs G \<or> v = u"
    by (rule in_connected_component_in_edges)
  with assms show "u \<in> Vs G"
    by fast
qed

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
proof (intro equals0I)
  fix C
  assume hboth: "C \<in> odd_components (graph_diff G X) \<inter> singl_in_diff G X"
  then have hOdd: "C \<in> odd_components (graph_diff G X)"
       and  hSingl: "C \<in> singl_in_diff G X"
    by auto
  from hSingl obtain v where
    hCv: "C = {v}" and hVs: "v \<notin> Vs (graph_diff G X)"
    by (auto simp: singl_in_diff_member)
  from hOdd have hOC: "odd_component (graph_diff G X) C"
    by (simp add: odd_component_member)
  obtain w where
    hw_Vs:   "w \<in> Vs (graph_diff G X)" and
    hw_comp: "connected_component (graph_diff G X) w = C"
    using odd_componentOb[OF hOC] by blast
  have "w \<in> connected_component (graph_diff G X) w"
    by (rule in_own_connected_component)
  with hw_comp hCv have "w \<in> {v}" by simp
  hence "w = v" by simp
  with hw_Vs hVs show False by simp
qed


lemma odd_components_sum_singletions_is_component:
  shows "(odd_components (graph_diff G X)) \<oplus> (singl_in_diff G X) = odd_comps_in_diff G X"
proof -
  have h_disj: "odd_components (graph_diff G X) \<inter> singl_in_diff G X = {}"
    using odd_components_inter_singl_empty .
  show ?thesis
    unfolding odd_comps_in_diff_def symmetric_diff_def
    using h_disj by blast
qed


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
proof -
  obtain u w where uw: "e = {u, w}" and neq: "u \<noteq> w"
    using assms(1) assms(2) dblton_graphE by blast
  from assms(3) uw have disj: "v = u \<or> v = w"
    by simp
  show ?thesis
  proof (cases "v = u")
    case True
    have mem_u: "u \<in> connected_component G u"
      by (rule in_own_connected_component)
    have "{u, w} \<in> G" 
      using assms(2) uw by simp
    have "reachable G u w"
      by (rule Paths.edges_reachable) fact
    have mem_w: "w \<in> connected_component G u"
      using \<open>reachable G u w\<close> by (simp add: Connected_Components.in_connected_componentI)
    with mem_u show ?thesis
      by (simp add: uw True)
  next
    case False
    then have veqw: "v = w" using disj by simp
    have mem_w: "w \<in> connected_component G w"
      by (rule in_own_connected_component)
    have "{u, w} \<in> G" 
      using assms(2) uw by simp
    have "reachable G u w"
      by (rule Paths.edges_reachable) fact
    have "reachable G w u"
      using \<open>reachable G u w\<close> by (simp add: Paths.reachable_sym)
    have mem_u: "u \<in> connected_component G w"
      using \<open>reachable G w u\<close> by (simp add: Connected_Components.in_connected_componentI)
    with mem_w show ?thesis
      by (simp add: uw veqw)
  qed
qed

lemma edge_in_E_card:
  assumes "graph_invar G"
  assumes "e \<in> G"
  shows "card e = 2" 
  using assms(1) assms(2) by auto

lemma component_is_finite:
  assumes "graph_invar G"
  shows "finite (connected_component G v)"
proof (cases "v \<in> Vs G")
  case True
  have sub: "connected_component G v \<subseteq> Vs G"
    by (rule connected_component_subset[OF True])
  moreover have "finite (Vs G)"
    using assms graph_invar_finite_Vs by blast
  ultimately show ?thesis
    by (rule finite_subset)
next
  case False
  then have "connected_component G v = {v}"
    by (rule connected_components_notE_singletons)
  then show ?thesis
    by simp
qed

lemma connected_component_not_singleton:
  assumes "graph_invar G"
  assumes "v\<in> Vs G"
  shows "card (connected_component G v) > 1"
proof -
  obtain e where "e \<in> G" "v \<in> e"
    using assms(2) by (rule vs_member_elim)
  then have "e \<subseteq> (connected_component G v)"
    by (simp add: edge_subset_component assms(1) \<open>v\<in> Vs G\<close>)
  then have "card (connected_component G v) \<ge> 2"
    using edge_in_E_card[of G e] component_is_finite[of G v]  assms(1)
  proof -
    have "card e \<le> card (connected_component G v)"
      using component_is_finite[OF assms(1)] \<open>e \<subseteq> connected_component G v\<close>
      by (rule card_mono)
    with edge_in_E_card[of G e] assms(1) \<open>e \<in> G\<close> show ?thesis
      by linarith
  qed
  then show ?thesis  by linarith
qed

lemma odd_component_is_component:
  assumes "C \<in> odd_components G"
  assumes "x \<in> C"
  shows "connected_component G x = C"
  using assms
  apply(elim odd_componentsE odd_componentE)
  by (auto simp: connected_components_member_eq)

lemma singl_in_diff_is_component:
  assumes "C \<in> singl_in_diff G X"
  assumes "x \<in> C"
  shows "connected_component (graph_diff G X) x = C"
proof -
  from assms(1) obtain v where hv_eq: "C = {v}"
    and hv_notin_Vs: "v \<notin> Vs (graph_diff G X)"
    using singl_in_diffE by blast
  have hx_eq: "x = v"
    using assms(2) hv_eq singletonD by blast
  have "connected_component (graph_diff G X) v = {v}"
    using hv_notin_Vs by (rule connected_components_notE_singletons)
  then show ?thesis
    using hx_eq hv_eq by simp
qed

lemma odd_comps_in_diff_is_component:
  assumes "C \<in> (odd_comps_in_diff G X)"
  assumes "x \<in> C"
  shows "connected_component (graph_diff G X) x = C"
proof -
  from assms(1) have "C \<in> odd_components (graph_diff G X) \<or> C \<in> singl_in_diff G X"
    by (simp add: odd_comps_in_diff_member)
  then show ?thesis
  proof
    assume "C \<in> odd_components (graph_diff G X)"
    then show ?thesis using assms(2) by (rule odd_component_is_component)
  next
    assume "C \<in> singl_in_diff G X"
    then show ?thesis using assms(2) by (rule singl_in_diff_is_component)
  qed
qed

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
  proof -
  obtain v where "v \<in> Vs G" and "connected_component G v = C"
    using assms unfolding odd_component_def by blast
  with connected_component_subset[OF `v \<in> Vs G`] show ?thesis by simp
qed

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
proof -
  have hx: "x \<in> connected_component G x"
    by (rule in_own_connected_component)
  have hsub: "connected_component G x \<subseteq> Vs G"
    using assms component_in_E by blast
  show "x \<in> Vs G"
    using hsub hx by blast
qed

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
    proof -
      note Csub = \<open>C \<subseteq> Vs (graph_diff G X)\<close>
      obtain v where vC: "v \<in> C" and vX: "v \<in> X"
        using \<open>C \<inter> X \<noteq> {}\<close> by blast
      have vVs: "v \<in> Vs (graph_diff G X)"
        using Csub vC by (rule subsetD)
      obtain e where eD: "e \<in> graph_diff G X" and ve: "v \<in> e"
        using vVs by (auto elim: vs_member_elim)
      have "v \<notin> X"
        using eD ve by (auto elim: graph_diffE)
      with vX show False by contradiction
    qed
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
  by (rule, simp)

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
  subgoal for x
  proof (elim singl_in_diffE)
    fix v
    assume h_vG: "v \<in> Vs G" and h_xv: "x = {v}" and h_vX: "v \<notin> X" and h_vVs: "v \<notin> Vs (graph_diff G X)"
    have h_singl: "x \<in> singl_in_diff G X"
      using singl_in_diffI[OF h_vG h_xv h_vX h_vVs] .
    show "\<exists>v\<in>Vs G - X. connected_component (graph_diff G X) v = x \<and> odd (card x)"
    proof (intro bexI[of _ v])
      show "connected_component (graph_diff G X) v = x \<and> odd (card x)"
      proof (intro conjI)
        show "connected_component (graph_diff G X) v = x"
          by (rule singl_in_diff_is_component[OF h_singl]) (simp add: h_xv)
      next
        show "odd (card x)"
          by (simp add: card_singl_in_diff_is_one[OF h_singl] odd_one)
      qed
    next
      show "v \<in> Vs G - X"
        by (intro DiffI h_vG h_vX)
    qed
  qed
proof -
  fix x v
  assume h1: "connected_component (graph_diff G X) v \<notin> singl_in_diff G X"
  assume h2: "v \<in> Vs G"
  assume h3: "v \<notin> X"
  assume h4: "odd (card (connected_component (graph_diff G X) v))"
  have v_in_Vs_diff: "v \<in> Vs (graph_diff G X)"
  proof (rule ccontr)
    assume v_notin: "v \<notin> Vs (graph_diff G X)"
    then have cc_is_singl: "connected_component (graph_diff G X) v = {v}"
      by (rule connected_components_notE_singletons)
    have "{v} \<in> singl_in_diff G X"
      using h2 h3 v_notin by (simp add: singl_in_diffI)
    with h1 show False using cc_is_singl by simp
  qed
  have odd_comp: "odd_component (graph_diff G X) (connected_component (graph_diff G X) v)"
    using h4 v_in_Vs_diff by (rule odd_componentI) simp
  from odd_comp show "connected_component (graph_diff G X) v \<in> odd_components (graph_diff G X)"
    by (simp add: odd_components_def)
qed


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
proof -
  from assms(2) obtain w where w_in_Vs: "w \<in> Vs (graph_diff G X)" and C_eq: "C = connected_component (graph_diff G X) w"
    by (rule connected_comp_has_vert)
  have w_in_diff: "w \<in> Vs G - X"
    using w_in_Vs vs_graph_diff[of G X] by auto
  show ?thesis
    using odd_comps_in_diff_are_componentsI assms(1) w_in_diff C_eq by fastforce
qed

lemma diff_component_disjoint:
  assumes "C1 \<in> (odd_comps_in_diff G X)"
  assumes "C2 \<in> (odd_comps_in_diff G X)"
  assumes "C1 \<noteq> C2"
  shows "C1 \<inter> C2 = {}"
proof (rule equals0I)
  fix x
  assume hx: "x \<in> C1 \<inter> C2"
  hence xC1: "x \<in> C1" and xC2: "x \<in> C2" by auto
  have comp_eq_C1: "connected_component (graph_diff G X) x = C1"
    using assms(1) xC1 by (rule odd_comps_in_diff_is_component)
  have comp_eq_C2: "connected_component (graph_diff G X) x = C2"
    using assms(2) xC2 by (rule odd_comps_in_diff_is_component)
  have "C1 = C2"
    using comp_eq_C1 comp_eq_C2 by auto
  with assms(3) show False by contradiction
qed


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
   subgoal for v
    by (blast dest: singl_in_diffE vs_member[THEN iffD1])
  using assms(2) 
   apply blast
  by (meson singl_in_diffI singletonI vs_member_intro)

lemma el_vs_singleton_is_in_singleton:
  assumes "x \<in> Vs (singl_in_diff G X)"
  shows "{x} \<in> (singl_in_diff G X)"
proof -
  obtain e where he: "e \<in> singl_in_diff G X" "x \<in> e"
    using assms by (auto elim: vs_member_elim)
  from he(1) obtain v where hv: "e = {v}"
    using singl_in_diffE by blast
  have "x = v"
    using he(2) hv singletonD by blast
  then show "{x} \<in> singl_in_diff G X"
    using he(1) hv by simp
qed

lemma diff_disjoint_elements:
  assumes "graph_invar G"
  assumes "X \<subseteq> Vs G"
  shows "Vs (graph_diff G X) \<inter> Vs (singl_in_diff G X) = {}" 
    "Vs (graph_diff G X) \<inter> X = {}"
    "Vs (singl_in_diff G X) \<inter> X = {}"
  proof safe
    fix x
    assume h1: "x \<in> Vs (graph_diff G X)" and h2: "x \<in> Vs (singl_in_diff G X)"
    have "{x} \<in> singl_in_diff G X"
      using h2 by (simp add: el_vs_singleton_is_in_singleton)
    then obtain v where hv: "v \<in> Vs G" "{x} = {v}" "v \<notin> X" "v \<notin> Vs (graph_diff G X)"
      using singl_in_diffE by blast
    have "x = v"
      using hv(2) singletonD by blast
    show "x \<in> {}"
      using h1 hv(4) \<open>x = v\<close> by simp
  next
    fix x
    assume "x \<in> Vs (graph_diff G X)" "x \<in> X"
    then show "x \<in> {}"
      unfolding Vs_def graph_diff_def by blast
  next
    fix x
    assume h1: "x \<in> Vs (singl_in_diff G X)" and h2: "x \<in> X"
    have "{x} \<in> singl_in_diff G X"
      using h1 by (simp add: el_vs_singleton_is_in_singleton)
    then obtain v where hv: "v \<in> Vs G" "{x} = {v}" "v \<notin> X" "v \<notin> Vs (graph_diff G X)"
      using singl_in_diffE by blast
    have "x = v"
      using hv(2) singletonD by blast
    then show "x \<in> {}"
      using h2 hv(3) by simp
  qed

lemma diff_card_is_sum_elements:
  assumes "graph_invar G"
  assumes "X \<subseteq> Vs G"
  shows "card (Vs (graph_diff G X)) + card (Vs (singl_in_diff G X)) + card X = card (Vs G)"
proof -
  (* Step 1: Name the two driver lemmas *)
  have union_eq: "Vs (graph_diff G X) \<union> Vs (singl_in_diff G X) \<union> X = Vs G"
    by (rule diff_is_union_elements[OF assms])
  (* Step 2: Obtain the pairwise disjointness facts *)
  have disj12: "Vs (graph_diff G X) \<inter> Vs (singl_in_diff G X) = {}"
    by (rule diff_disjoint_elements(1)[OF assms])
  have disj1X: "Vs (graph_diff G X) \<inter> X = {}"
    by (rule diff_disjoint_elements(2)[OF assms])
  have disj2X: "Vs (singl_in_diff G X) \<inter> X = {}"
    by (rule diff_disjoint_elements(3)[OF assms])
  (* Step 3: Finiteness — derive from graph_invar via graph_invar_finite_Vs *)
  have fin_G: "finite (Vs G)"
    by (rule graph_invar_finite_Vs[OF assms(1)])
  have fin1: "finite (Vs (graph_diff G X))"
    by (rule finite_subset[of _ "Vs G"]) (use union_eq fin_G in auto)
  have fin2: "finite (Vs (singl_in_diff G X))"
    by (rule finite_subset[of _ "Vs G"]) (use union_eq fin_G in auto)
  have fin3: "finite X"
    by (rule finite_subset[OF assms(2) fin_G])
  (* Step 4: Derive combined disjointness for the outer card_Un_disjoint call *)
  have disj_union_X: "(Vs (graph_diff G X) \<union> Vs (singl_in_diff G X)) \<inter> X = {}"
    by (simp add: Int_Un_distrib2 disj1X disj2X)
  (* Step 5: Inner card_Un_disjoint *)
  have card12: "card (Vs (graph_diff G X) \<union> Vs (singl_in_diff G X)) =
                card (Vs (graph_diff G X)) + card (Vs (singl_in_diff G X))"
    by (rule card_Un_disjoint[OF fin1 fin2 disj12])
  (* Step 6: Outer card_Un_disjoint *)
  have card_all: "card (Vs (graph_diff G X) \<union> Vs (singl_in_diff G X) \<union> X) =
                  card (Vs (graph_diff G X) \<union> Vs (singl_in_diff G X)) + card X"
    by (rule card_Un_disjoint[OF finite_UnI[OF fin1 fin2] fin3 disj_union_X])
  (* Step 7: Conclude by rewriting the union and arithmetic *)
  show ?thesis
    using union_eq card12 card_all by auto
qed

lemma singleton_set_card_eq_vertices:
  assumes "graph_invar G"
  assumes "X \<subseteq> Vs G"
  shows "card (Vs (singl_in_diff G X)) = card (singl_in_diff G X)"
proof -
  let ?A = "(singl_in_diff G X)"
  have "finite ?A"
  proof -
    have fin_Vs: "finite (Vs G)"
      using assms(1) by (rule graph_invar_finite_Vs)
    have Vs_singl_subset: "Vs (singl_in_diff G X) \<subseteq> Vs G"
      using assms diff_is_union_elements by blast
    have fin_Vs_singl: "finite (Vs (singl_in_diff G X))"
      using Vs_singl_subset fin_Vs by (rule finite_subset)
    show "finite ?A"
      using fin_Vs_singl unfolding Vs_def by (rule finite_UnionD)
  qed
  moreover have "\<forall>C \<in> ?A. finite C" 
    by(auto elim: singl_in_diffE)
  moreover have "\<forall> C1 \<in> ?A. \<forall> C2 \<in> ?A. C1 \<noteq> C2 \<longrightarrow> C1 \<inter> C2 = {}"   
    by(auto elim: singl_in_diffE)
  ultimately  have "sum card ?A = card (Vs ?A)" 
    using assms Vs_def card_Union_disjoint disjnt_def pairwise_def
    by (simp add: Vs_def card_Union_disjoint disjnt_def pairwise_def)
  also have "sum card ?A = card ?A"
  proof -
    have each_one: "\<forall>C \<in> ?A. card C = 1"
      using card_singl_in_diff_is_one by blast
    have "sum card ?A = sum (\<lambda>_. 1) ?A"
      by (rule sum.cong) (auto simp: each_one)
    also have "\<dots> = card ?A"
      by (simp add: card_eq_sum[symmetric])
    finally show ?thesis .
  qed
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
proof -
  have fin_odd: "finite (odd_components (graph_diff G X))"
    using assms(1) by (rule finite_odd_components)
  have fin_singl: "finite (singl_in_diff G X)"
  proof -
    have fin_Vs: "finite (Vs G)"
      using assms(1) by (rule graph_invar_finite_Vs)
    have Vs_singl_subset: "Vs (singl_in_diff G X) \<subseteq> Vs G"
      using assms diff_is_union_elements by blast
    have fin_Vs_singl: "finite (Vs (singl_in_diff G X))"
      using Vs_singl_subset fin_Vs by (rule finite_subset)
    show ?thesis
      using fin_Vs_singl unfolding Vs_def by (rule finite_UnionD)
  qed
  show "finite ((odd_components (graph_diff G X)) \<union> (singl_in_diff G X))"
    using fin_odd fin_singl by (simp add: finite_Un)
qed

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
  shows "\<forall>x \<in> set p. x \<in> C"
proof (cases "p = []")
  case True
  then show ?thesis by simp
next
  case False
  have set_subset: "set p \<subseteq> connected_component G (hd p)"
    using assms(1) by (simp add: path_subset_conn_comp)
  have last_in: "last p \<in> set p"
    using False by (simp add: last_in_set)
  have last_in_comp: "last p \<in> connected_component G (hd p)"
    using set_subset last_in by blast
  have comp_eq: "connected_component G (last p) = connected_component G (hd p)"
    using last_in_comp by (simp add: connected_components_member_eq)
  have C_eq: "C = connected_component G (last p)"
    using assms(2) assms(3) by (simp add: connected_components_closed')
  have "set p \<subseteq> C"
    using set_subset comp_eq C_eq by auto
  then show ?thesis by auto
qed

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
  proof -
    have "e \<subseteq> connected_component G x"
      by (rule edge_subset_component[OF assms(1) e(1) e(2)])
    moreover have "connected_component G x = C"
      using assms(2) assms(3) by (simp add: connected_components_closed'[symmetric])
    ultimately show ?thesis
      by simp
  qed
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
  proof -
    have edge_exists: "\<exists>C'. C' \<in> connected_components G \<and> {v, v'} \<subseteq> C'"
      using path2.hyps(1) by (rule edge_in_component)
    obtain C' where C'_comp: "C' \<in> connected_components G" and subset: "{v, v'} \<subseteq> C'"
      using edge_exists by blast
    have "v \<in> C'" using subset by auto
    with assms(3) C'_comp \<open>v \<in> C\<close> have "C = C'"
      using connected_components_eq' by fastforce
    then have "{v, v'} \<subseteq> C"
      using subset by auto
    then show "v' \<in> C"
      by auto
  qed
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
  proof -
    note pm_sub_bound = \<open>\<forall>a \<in> A. {M. perfect_matching a M} \<subseteq> {a1. a1 \<subseteq> a}\<close>
    show ?thesis
    proof (rule ballI)
      fix a
      assume ha: "a \<in> A"
      have hvsf: "finite (Vs a)"
        using \<open>\<forall>a \<in> A. finite (Vs a)\<close> ha by blast
      have ha_pow: "a \<subseteq> Pow (Vs a)"
      proof (rule subsetI)
        fix e
        assume "e \<in> a"
        then show "e \<in> Pow (Vs a)"
          unfolding Vs_def by blast
      qed
      have haf: "finite a"
        using ha_pow finite_subset hvsf finite_Pow_iff by blast
      have hpow: "finite {a1. a1 \<subseteq> a}"
        using haf finite_Collect_subsets by blast
      show "finite {M. perfect_matching a M}"
        using pm_sub_bound ha hpow finite_subset by blast
    qed
  qed
  then have hfin_pm: "\<forall>a \<in> A. finite {M. perfect_matching a M}" .
  have "finite (Vs ?Ms)"
  proof -
    have hfin_elems: "\<forall>x \<in> ?Ms. finite x"
    proof (rule ballI)
      fix x assume hx: "x \<in> ?Ms"
      then obtain a where ha: "a \<in> A" and hxa: "x = {M. perfect_matching a M}"
        by auto
      show "finite x"
        using hfin_pm ha hxa by simp
    qed
    have hfin_union: "finite (\<Union> ?Ms)"
      using \<open>finite ?Ms\<close> hfin_elems by (meson finite_Union)
    show "finite (Vs ?Ms)"
      unfolding Vs_def using hfin_union by simp
  qed
  have "\<forall>a1 \<in> A.\<forall>a2\<in>A. a1 \<noteq> a2 \<longrightarrow>
     {M. perfect_matching a1 M} \<inter> {M. perfect_matching a2 M} = {}" 
  proof (intro ballI impI)
    fix a1 a2
    assume ha1: "a1 \<in> A" and ha2: "a2 \<in> A" and hne: "a1 \<noteq> a2"
    show "{M. perfect_matching a1 M} \<inter> {M. perfect_matching a2 M} = {}"
    proof (rule equals0I)
      fix x
      assume hx: "x \<in> {M. perfect_matching a1 M} \<inter> {M. perfect_matching a2 M}"
      then have hpm1: "perfect_matching a1 x" and hpm2: "perfect_matching a2 x"
        by auto
      have hVs1: "Vs x = Vs a1"
        using hpm1 unfolding perfect_matching_def by auto
      have hVs2: "Vs x = Vs a2"
        using hpm2 unfolding perfect_matching_def by auto
      have hVs_eq: "Vs a1 = Vs a2"
        using hVs1 hVs2 by auto
      have hVs_disj: "Vs a1 \<inter> Vs a2 = {}"
        using assms(2) ha1 ha2 hne by auto
      have hVs_empty: "Vs a1 = {}"
        using hVs_eq hVs_disj by auto
      have ha1_empty: "a1 = {}"
      proof (rule ccontr)
        assume "a1 \<noteq> {}"
        then obtain e where he: "e \<in> a1" by blast
        have "e \<noteq> {}" using assms(4) ha1 he by auto
        then obtain v where hv: "v \<in> e" by blast
        have "v \<in> Vs a1" using vs_member_intro he hv by auto
        then show False using hVs_empty by auto
      qed
      have hVs2_empty: "Vs a2 = {}"
        using hVs_eq hVs_empty by auto
      have ha2_empty: "a2 = {}"
      proof (rule ccontr)
        assume "a2 \<noteq> {}"
        then obtain e where he: "e \<in> a2" by blast
        have "e \<noteq> {}" using assms(4) ha2 he by auto
        then obtain v where hv: "v \<in> e" by blast
        have "v \<in> Vs a2" using vs_member_intro he hv by auto
        then show False using hVs2_empty by auto
      qed
      show False using ha1_empty ha2_empty hne by auto
    qed
  qed

  then have matchings_are_diff: "\<forall>a1 \<in> ?Ms.\<forall>a2\<in>?Ms. a1 \<noteq> a2 \<longrightarrow> a1 \<inter> a2 = {}" 
    by force
  have "\<forall>a\<in> ?Ms. \<exists>b\<in> Vs ?Ms. b \<in> a" 
  proof (rule ballI)
    fix a
    assume ha: "a \<in> ?Ms"
    then obtain g where hg: "g \<in> A" and ha_eq: "a = {M. perfect_matching g M}"
      by auto
    obtain M where hM: "perfect_matching g M"
      using assms(3) hg by blast
    have hMa: "M \<in> a"
      using ha_eq hM by simp
    have hMVs: "M \<in> Vs ?Ms"
      using vs_member_intro ha hMa by blast
    show "\<exists>b\<in> Vs ?Ms. b \<in> a"
      using hMVs hMa by blast
  qed
  then obtain C where C_sub_Ms:"C\<subseteq> Vs ?Ms \<and> (\<forall>Ms\<in> ?Ms. \<exists>!M\<in>C. M \<in> Ms)"
    using ex_subset_same_elem_card[of ?Ms] matchings_are_diff \<open>finite (Vs ?Ms)\<close> \<open>finite ?Ms\<close> by presburger
  have "\<forall>c \<in> C. matching c"
  proof
    fix c
    assume "c \<in> C"
    then have "c \<in> Vs ?Ms" using C_sub_Ms by blast
    then have "\<exists>a\<in>A. perfect_matching a c"
    proof -
      assume hcVs: "c \<in> Vs ?Ms"
      obtain Ms where hMs: "Ms \<in> ?Ms" and hcMs: "c \<in> Ms"
        using hcVs by (auto simp: vs_member)
      obtain a where ha: "a \<in> A" and hMs_eq: "Ms = {M. perfect_matching a M}"
        using hMs by auto
      show "\<exists>a\<in>A. perfect_matching a c"
        using ha hcMs hMs_eq by auto
    qed
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
        then show ?thesis
        proof -
          have he2X: "e2 \<in> X"
            using assums(3) True by simp
          have hmatX: "matching X"
            using \<open>\<forall>c\<in>C. matching c\<close> assums(2) by blast
          from matching_unique_match[OF hmatX, of xa e1 e2] 
          have "e1 = e2"
            using assums(1) he2X assums(7) assums(8)
            by auto
          then show ?thesis
            using assums(5) assums(6) by simp
        qed
      next
        case False
        have "Xa \<in> Vs ?Ms" 
          using C_sub_Ms \<open>Xa \<in> C\<close> by blast
        then obtain a1 where a1_match:"a1 \<in> A \<and> perfect_matching a1 Xa"
          proof -
            assume hXaVs: "Xa \<in> Vs ?Ms"
            obtain Ms' where hMs'_in: "Ms' \<in> ?Ms" and hXa_in: "Xa \<in> Ms'"
              using hXaVs by (auto simp: vs_member)
            obtain a1 where ha1_A: "a1 \<in> A" and hMs'_eq: "Ms' = {M. perfect_matching a1 M}"
              using hMs'_in by auto
            have hpm: "perfect_matching a1 Xa"
              using hXa_in hMs'_eq by simp
            from ha1_A hpm have "a1 \<in> A \<and> perfect_matching a1 Xa"
              by blast
            then show ?thesis 
              by (rule that)
          qed
        have "X \<in> Vs ?Ms" 
          using C_sub_Ms \<open>X \<in> C\<close> by blast
        then obtain a2 where a2_match:"a2 \<in> A \<and> perfect_matching a2 X"
          by (auto simp: vs_member)
        have "a1 \<noteq> a2" 
          using C_sub_Ms False \<open>X \<in> C\<close> \<open>Xa \<in> C\<close> a1_match a2_match by auto
        then have "a1 \<inter> a2 = {}" 
          by (simp add: a1_match a2_match disjoint_edges)

        then show ?thesis 
          using assums a1_match a2_match
        proof -
          have hX_sub: "X \<subseteq> a2"       using a2_match by (auto simp: perfect_matching_def)
          have hXa_sub: "Xa \<subseteq> a1"     using a1_match by (auto simp: perfect_matching_def)
          have he1_a2: "e1 \<in> a2"      using assums(1) hX_sub by blast
          have he2_a1: "e2 \<in> a1"      using assums(3) hXa_sub by blast
          have hxa_Vs_a2: "xa \<in> Vs a2" using vs_member_intro he1_a2 assums(7) by blast
          have hxa_Vs_a1: "xa \<in> Vs a1" using vs_member_intro he2_a1 assums(8) by blast
          have hVs_disj: "Vs a1 \<inter> Vs a2 = {}"
            using assms(2) a1_match a2_match \<open>a1 \<noteq> a2\<close> by blast
          show ?thesis using hxa_Vs_a1 hxa_Vs_a2 hVs_disj by blast
        qed
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
    then obtain a where a_match: "a \<in> A \<and> perfect_matching a c"
    proof -
      assume hcVs: "c \<in> Vs ?Ms"
      obtain Ms' where hMs'_in: "Ms' \<in> ?Ms" and hc_in: "c \<in> Ms'"
        using hcVs by (auto simp: vs_member)
      obtain a where ha_A: "a \<in> A" and hMs'_eq: "Ms' = {M. perfect_matching a M}"
        using hMs'_in by auto
      have hpm: "perfect_matching a c"
        using hc_in hMs'_eq by simp
      from ha_A hpm have "a \<in> A \<and> perfect_matching a c"
        by blast
      then show ?thesis
        by (rule that)
    qed
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
    proof -
      have ha_Ms: "{M. perfect_matching a M} \<in> ?Ms"
        using \<open>a \<in> A \<and> e \<in> a\<close> by blast
      then have hex: "\<exists>!c \<in> C. c \<in> {M. perfect_matching a M}"
        using C_sub_Ms by blast
      then obtain c where "c \<in> C \<and> c \<in> {M. perfect_matching a M}"
        by blast
      then show thesis
        using that by blast
    qed
    then have "x \<in> Vs c"
    proof -
      have hpm: "perfect_matching a c"
        using \<open>c \<in> C \<and> perfect_matching a c\<close> by blast
      have he_a: "e \<in> a"
        using \<open>a \<in> A \<and> e \<in> a\<close> by blast
      have hx_e: "x \<in> e"
        using \<open>e \<in> \<Union> A \<and> x \<in> e\<close> by blast
      have hVs: "Vs c = Vs a"
        using hpm unfolding perfect_matching_def by blast
      have hx_Vs_a: "x \<in> Vs a"
        using vs_member_intro he_a hx_e by blast
      show "x \<in> Vs c"
        using hx_Vs_a hVs by blast
    qed
    then show "x \<in> Vs (\<Union> C)" 
      proof -
        have hc: "c \<in> C"
          using \<open>c \<in> C \<and> perfect_matching a c\<close> by blast
        show "x \<in> Vs (\<Union> C)"
          using \<open>x \<in> Vs c\<close> hc unfolding Vs_def by blast
      qed
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
      by (auto simp: component_edges_def)
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
  proof -
    have xy_A: "{x, y} \<in> A"
      using \<open>e = {x, y}\<close> \<open>x \<in> e \<and> e \<in> A\<close> by simp
    have eq: "A = insert {x, y} (A - {{x, y}})"
      using xy_A insert_Diff by blast
    have "y \<in> connected_component A x"
      by (subst eq) (rule in_con_comp_insert)
    moreover have "C = connected_component A x"
      using assms(2) \<open>x \<in> C\<close> by (simp add: connected_components_closed')
    ultimately show "y \<in> C" by simp
  qed
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
    proof -
      obtain u v where huv: "e = {u, v}" and "u \<noteq> v"
        using dblton_graphE assms \<open>e \<in> A\<close> by blast
      have "{u, v} \<in> A"
        using huv \<open>e \<in> A\<close> by auto
      from edge_in_component[OF this] obtain C' where 
        "C' \<in> connected_components A" and "{u, v} \<subseteq> C'"
        by blast
      have "e \<subseteq> C'"
        using huv \<open>{u, v} \<subseteq> C'\<close> by auto
      with \<open>C' \<in> connected_components A\<close> have "C' \<in> connected_components A \<and> e \<subseteq> C'"
        by auto
      then show ?thesis
        by (rule that)
    qed
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
  proof -
    have fin_A: "finite A"
      using assms(1) graph_invar_finite by blast
    have part: "\<Union>(components_edges A) = A"
      using graph_component_edges_partition assms(1) by blast
    have "finite (\<Union>(components_edges A))"
      using fin_A part by simp
    then show ?thesis
      by (rule finite_UnionD)
  qed
  let ?E = "(components_edges A)" 
  have "\<forall>a \<in> ?E. \<exists>M. perfect_matching a M" using assms(2) unfolding components_edges_def
    by blast
  have " \<forall>a1\<in>?E. \<forall>a2\<in>?E. a1 \<noteq> a2 \<longrightarrow> Vs a1 \<inter> Vs a2 = {}"
  proof
    fix a1
    assume "a1 \<in> ?E"
    then obtain C1 where "C1 \<in> connected_components A \<and> a1 = component_edges A C1"
      unfolding components_edges_def by blast
    then have "Vs a1 = C1" 
      by (simp add: assms(1) vs_connected_component)
    show "\<forall>a2\<in>?E. a1 \<noteq> a2 \<longrightarrow> Vs a1 \<inter> Vs a2 = {}" 
    proof
      fix a2
      assume "a2 \<in> ?E"
      then obtain C2 where "C2 \<in> connected_components A \<and> a2 = component_edges A C2"
        unfolding components_edges_def by blast
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
proof (rule equals0I)
  fix C
  assume "C \<in> odd_components (graph_diff {} X) \<union> singl_in_diff {} X"
  then show False
    by (simp add: graph_diff_of_empty vs_member_elim odd_components_def odd_component_def singl_in_diff_def)
qed

lemma component_edges_singleton_is_empty:
  assumes "graph_invar G" 
  shows "component_edges G {x} = {}"
  unfolding component_edges_def
  using assms by fastforce

lemma component_edges_subset:
  assumes "Y \<subseteq> C"
  shows "component_edges G Y \<subseteq> component_edges G C"
  unfolding component_edges_def
  by (auto dest: subsetD[OF assms(1)])

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
    using True unfolding singl_in_diff_def by blast
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
    by auto
  have "{x} \<notin> (odd_components (graph_diff G X))" 
    using odd_components_elem_in_E singl_x(4) by blast
  then have "odd_comps_in_diff G (X\<union>{x}) = ((odd_comps_in_diff G X) - {{x}})"
    unfolding odd_comps_in_diff_def 
    by (simp add: Un_Diff \<open>graph_diff G X = graph_diff G (X \<union> {x})\<close> 
        \<open>singl_in_diff G X - {{x}} = singl_in_diff G (X \<union> {x})\<close>)


  have "(component_edges (graph_diff G X) C) = {}"
  proof -
    have invar_diff: "graph_invar (graph_diff G X)"
      by (rule graph_invar_diff[OF assms(1)])
    have "component_edges (graph_diff G X) {x} = {}"
      by (rule component_edges_singleton_is_empty[OF invar_diff])
    then show ?thesis
      using singl_x(1) by simp
  qed
  then have "odd_comps_in_diff (component_edges (graph_diff G X) C) Y = {}" 
    by (simp add: empty_graph_odd_components)

  then show ?thesis
  proof -
    have empty_comp: "odd_comps_in_diff (component_edges (graph_diff G X) C) Y = {}"
      by fact
    have Y_eq: "Y = {x}"
      using \<open>C = Y\<close> singl_x(1) by simp
    have XY_eq: "X \<union> Y = X \<union> {x}"
      using Y_eq by simp
    have lhs_eq: "odd_comps_in_diff G (X \<union> Y) = odd_comps_in_diff G X - {C}"
    proof -
      have "odd_comps_in_diff G (X \<union> Y) = odd_comps_in_diff G (X \<union> {x})"
        using XY_eq by simp
      also have "\<dots> = odd_comps_in_diff G X - {{x}}"
        by (rule \<open>odd_comps_in_diff G (X \<union> {x}) = odd_comps_in_diff G X - {{x}}\<close>)
      also have "\<dots> = odd_comps_in_diff G X - {C}"
        using singl_x(1) by simp
      finally show ?thesis .
    qed
    then show ?thesis
      using empty_comp by simp
  qed
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
        by (rule odd_comps_in_diff_is_component[OF asmC'])

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
        proof -
          have invar_diff: "graph_invar (graph_diff G X)"
            by (rule graph_invar_diff[OF assms(1)])
          have "e \<subseteq> connected_component (graph_diff G X) c"
            using edge_subset_component[of "graph_diff G X" e c] invar_diff e(1) e(2)
            by blast
          then show ?thesis
            using conn_compC by simp
        qed
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
              proof -
                have "c \<in> connected_component (graph_diff G (X \<union> Y)) x"
                  using asm by (rule connected_components_member_sym)
                with \<open>x \<noteq> c\<close> show ?thesis
                  by (fastforce elim: in_con_comp_has_walk)
              qed
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
                proof -
                  have last_eq: "last (v' # vs) = c"
                    using \<open>last (v # v' # vs) = c\<close> by (simp add: last_ConsR)
                  then have "\<forall>z \<in> set (v' # vs). z \<in> C \<and>
                        z \<in> connected_component
                              (graph_diff (component_edges (graph_diff G X) C) Y) c"
                    using path2(3) by auto
                  moreover have "v' \<in> set (v' # vs)"
                    by simp
                  ultimately show ?thesis
                    by auto
                qed
                have "{v, v'} \<inter> (X\<union>Y) = {}" 
                  by (meson graph_diffE path2.hyps(1))
                then have "{v, v'} \<inter> X = {}" 
                  by (simp add: Int_Un_distrib)
                then have "{v, v'} \<in> (graph_diff G (X))"   
                  by (meson graph_diffE graph_diffI path2.hyps(1))
                then have "v \<in> C"
                proof -
                  have invar_diff_X: "graph_invar (graph_diff G X)"
                    by (rule graph_invar_diff[OF assms(1)])
                  have v'_in_comp: "v' \<in> connected_component (graph_diff G X) c"
                    using \<open>v' \<in> C\<close> conn_compC by simp
                  have comp_v'_eq: "connected_component (graph_diff G X) v' = C"
                    using connected_components_member_eq[OF v'_in_comp] conn_compC by simp
                  have edge_sub: "{v, v'} \<subseteq> connected_component (graph_diff G X) v'"
                    using edge_subset_component[OF invar_diff_X \<open>{v, v'} \<in> graph_diff G X\<close>]
                    by simp
                  then have "v \<in> connected_component (graph_diff G X) v'"
                    by blast
                  then show ?thesis
                    using comp_v'_eq by simp
                qed
                then have "{v, v'} \<in> (component_edges (graph_diff G X) C)"
                  using \<open>v' \<in> C\<close> \<open>{v, v'} \<in> graph_diff G X\<close> component_edges_def by blast     
                then have "{v, v'} \<in> (graph_diff (component_edges (graph_diff G X) C) Y)"
                  using \<open>{v, v'} \<inter> (X \<union> Y) = {}\<close> 
                  by (simp add: graph_diffI)       
                then have "v' \<in> connected_component 
                                (graph_diff (component_edges (graph_diff G X) C) Y) c"
                proof -
                  have "last (v' # vs) = c"
                    using path2.prems by (simp add: last_ConsR)
                  then have "\<forall>z \<in> set (v' # vs). z \<in> C \<and> 
                      z \<in> connected_component (graph_diff (component_edges (graph_diff G X) C) Y) c"
                    using path2.hyps(3) by blast
                  moreover have "v' \<in> set (v' # vs)"
                    by simp
                  ultimately show ?thesis
                    by blast
                qed
                then have "v \<in> connected_component 
                                (graph_diff (component_edges (graph_diff G X) C) Y) c"
                proof -
                  let ?H = "graph_diff (component_edges (graph_diff G X) C) Y"
                  note v'_in_comp = \<open>v' \<in> connected_component ?H c\<close>
                  note edge_in_H  = \<open>{v, v'} \<in> graph_diff (component_edges (graph_diff G X) C) Y\<close>
                  have comp_eq: "connected_component ?H v' = connected_component ?H c"
                    by (rule connected_components_member_eq[OF v'_in_comp])
                  have "v' \<in> connected_component ?H v"
                    by (rule vertices_edges_in_same_component[OF edge_in_H])
                  then have "v \<in> connected_component ?H v'"
                    by (rule connected_components_member_sym)
                  then show ?thesis
                    using comp_eq by simp
                qed
                note v_in_comp = this
                show ?case
                proof -
                  have last_vs: "last (v' # vs) = c"
                    using path2.prems by (simp add: last_ConsR)
                  with path2.hyps(3) have ih: "\<forall>z \<in> set (v' # vs). z \<in> C \<and>
                        z \<in> connected_component
                              (graph_diff (component_edges (graph_diff G X) C) Y) c"
                    by blast
                  show ?case
                  proof (rule ballI)
                    fix z
                    assume "z \<in> set (v # v' # vs)"
                    then consider (head) "z = v" | (tail) "z \<in> set (v' # vs)"
                      by auto
                    then show "z \<in> C \<and> z \<in> connected_component
                                          (graph_diff (component_edges (graph_diff G X) C) Y) c"
                    proof cases
                      case head
                      then show ?thesis using \<open>v \<in> C\<close> v_in_comp by simp
                    next
                      case tail
                      then show ?thesis using ih by blast
                    qed
                  qed
                qed
              qed
              then show "x \<in> connected_component 
                          (graph_diff (component_edges (graph_diff G X) C) Y) c"
              proof -
                note all_z =
                  \<open>\<forall>z\<in>set p. z \<in> C \<and>
                       z \<in> connected_component
                             (graph_diff (component_edges (graph_diff G X) C) Y) c\<close>
                have p_nonempty: "p \<noteq> []"
                  using p_walk unfolding walk_betw_def by simp
                have hd_x: "hd p = x"
                  using p_walk unfolding walk_betw_def by simp
                have "x \<in> set p"
                  using hd_in_set[OF p_nonempty] hd_x by simp
                with all_z show ?thesis by blast
              qed
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
