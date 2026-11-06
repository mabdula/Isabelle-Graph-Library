(*
  Author: Ralitsa Dordjonova
  Author: Mohammad Abdulaziz
*)

theory Odd_Components
  imports Bipartite_Matchings_Existence Cardinality_Sums
begin

provenance human

section \<open>Odd and Even Connected Components\<close>

definition odd_component where
  "odd_component G C = (\<exists> v \<in> Vs G. connected_component G v = C \<and> odd (card C))"

definition odd_components where
  "odd_components G = {C. odd_component G C}"

definition even_components where
  "even_components G = {C. \<exists> v \<in> Vs G. connected_component G v = C \<and> even (card C)}"

definition count_odd_components where
  "count_odd_components G = card (odd_components G)"
(*
definition graph_diff where
  "graph_diff G X = {e. e \<in> G \<and> e \<inter> X = {}}"
*)
(*TODO: those two definitions are the same

lemma "remove_vertices_graph = graph_diff"
  apply(rule HOL.ext)
  by (auto simp add: graph_diff_def remove_vertices_graph_def)*)

definition singl_in_diff where 
  "singl_in_diff G X = {a. \<exists> v. a = {v} \<and> v \<in> Vs G \<and> v \<notin> X \<and> v \<notin> Vs (G  \<setminus> X)}"

definition odd_comps_in_diff where
  "odd_comps_in_diff G X = (odd_components (G \<setminus> X)) \<union> (singl_in_diff G X)"

definition count_odd_comps_in_diff where
  "count_odd_comps_in_diff G X = card (odd_comps_in_diff G X)"

definition barrier where
  "barrier G X = ( X \<noteq> {} \<and> card (odd_comps_in_diff G X) = card X)"

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
  "C \<in> singl_in_diff G  X \<longleftrightarrow> (\<exists> v. C = {v} \<and> v \<in> Vs G \<and> v \<notin> X \<and> v \<notin> Vs (G  \<setminus> X))"
  unfolding singl_in_diff_def by simp

lemma singl_in_diffE:
  assumes "C \<in> singl_in_diff G X" 
  obtains v where "v \<in> Vs G" "C = {v}" "v \<notin> X" "v \<notin> Vs (G  \<setminus> X)"
  using assms singl_in_diff_member[of C G X] 
  by(auto simp: singl_in_diff_member)

lemma singl_in_diffI:
  assumes "v \<in> Vs G"
  assumes "C = {v}"
  assumes "v \<notin> X"
  assumes "v \<notin> Vs (G  \<setminus> X)"
  shows "C \<in> singl_in_diff G X" 
  using  assms 
  by (simp add: singl_in_diff_member)

lemma odd_components_inter_singl_empty:
  shows "odd_components (G \<setminus> X) \<inter> singl_in_diff G X = {}"
proof (intro equals0I)
  fix C
  assume hboth: "C \<in> odd_components (G \<setminus> X) \<inter> singl_in_diff G X"
  then have hOdd: "C \<in> odd_components (G \<setminus> X)"
       and  hSingl: "C \<in> singl_in_diff G X"
    by auto
  from hSingl obtain v where
    hCv: "C = {v}" and hVs: "v \<notin> Vs (G \<setminus> X)"
    by (auto simp: singl_in_diff_member)
  from hOdd have hOC: "odd_component (G \<setminus> X) C"
    by (simp add: odd_component_member)
  obtain w where
    hw_Vs:   "w \<in> Vs (G \<setminus> X)" and
    hw_comp: "connected_component (G \<setminus> X) w = C"
    using odd_componentOb[OF hOC] by blast
  have "w \<in> connected_component (G \<setminus> X) w"
    by (rule in_own_connected_component)
  with hw_comp hCv have "w \<in> {v}" by simp
  hence "w = v" by simp
  with hw_Vs hVs show False by simp
qed

lemma odd_components_sum_singletions_is_component:
  shows "(odd_components (G \<setminus> X)) \<oplus> (singl_in_diff G X) = odd_comps_in_diff G X"
proof -
  have h_disj: "odd_components (G \<setminus> X) \<inter> singl_in_diff G X = {}"
    using odd_components_inter_singl_empty .
  show ?thesis
    unfolding odd_comps_in_diff_def symmetric_diff_def
    using h_disj by blast
qed

lemma odd_comps_in_diff_member[iff?]:
  "C \<in> odd_comps_in_diff G X \<longleftrightarrow> C \<in> odd_components (G \<setminus> X) \<or> C \<in> singl_in_diff G X"
  by (simp add: odd_comps_in_diff_def)

lemma odd_comps_in_diffE:
  assumes major: "C \<in> odd_comps_in_diff G X"
    and minorP: "C \<in> odd_components (G \<setminus> X) \<Longrightarrow> R"
    and minorQ: "C \<in> singl_in_diff G X \<Longrightarrow> R"
  shows R
  using major minorP minorQ odd_comps_in_diff_member by blast

lemma odd_comps_in_diffI1: "C \<in> odd_components (G \<setminus> X) \<Longrightarrow> C \<in> odd_comps_in_diff G X"
  by (simp add: odd_comps_in_diff_member)

lemma odd_comps_in_diffI2: "C \<in> singl_in_diff G X \<Longrightarrow> C \<in> odd_comps_in_diff G X"
  by (simp add: odd_comps_in_diff_member)

lemma odd_comps_in_diffOR:
  assumes "C \<in> odd_components (G \<setminus> X) \<or> C \<in> singl_in_diff G X"
  shows "C \<in> odd_comps_in_diff G X" 
  by (simp add: assms odd_comps_in_diff_member)

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
  shows "connected_component (G \<setminus> X) x = C"
proof -
  from assms(1) obtain v where hv_eq: "C = {v}"
    and hv_notin_Vs: "v \<notin> Vs (G \<setminus> X)"
    using singl_in_diffE by blast
  have hx_eq: "x = v"
    using assms(2) hv_eq singletonD by blast
  have "connected_component (G \<setminus> X) v = {v}"
    using hv_notin_Vs by (rule connected_components_notE_singletons)
  then show ?thesis
    using hx_eq hv_eq by simp
qed

lemma odd_comps_in_diff_is_component:
  assumes "C \<in> (odd_comps_in_diff G X)"
  assumes "x \<in> C"
  shows "connected_component (G \<setminus> X) x = C"
proof -
  from assms(1) have "C \<in> odd_components (G \<setminus> X) \<or> C \<in> singl_in_diff G X"
    by (simp add: odd_comps_in_diff_member)
  then show ?thesis
  proof
    assume "C \<in> odd_components (G \<setminus> X)"
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
  proof(cases "C \<in> odd_components (G \<setminus> X)")
    case True
    have "C \<subseteq> Vs (G \<setminus> X)"
      using True odd_components_elem_in_E by auto
    then show ?thesis
    proof -
      note Csub = \<open>C \<subseteq> Vs (G \<setminus> X)\<close>
      obtain v where vC: "v \<in> C" and vX: "v \<in> X"
        using \<open>C \<inter> X \<noteq> {}\<close> by blast
      have vVs: "v \<in> Vs (G \<setminus> X)"
        using Csub vC by (rule subsetD)
      obtain e where eD: "e \<in> (G \<setminus> X)" and ve: "v \<in> e"
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

lemma odd_comps_in_diff_are_components:
  shows "odd_comps_in_diff G X = 
  {C. \<exists> v\<in>Vs G-X. connected_component (G \<setminus> X) v = C \<and> odd (card C)}"
  unfolding odd_comps_in_diff_def
  apply safe
    apply(elim odd_componentsE odd_componentE )
    apply (meson subsetD vs_graph_diff) 
  subgoal for x
  proof (elim singl_in_diffE)
    fix v
    assume h_vG: "v \<in> Vs G" and h_xv: "x = {v}" and h_vX: "v \<notin> X" and h_vVs: "v \<notin> Vs (G \<setminus> X)"
    have h_singl: "x \<in> singl_in_diff G X"
      using singl_in_diffI[OF h_vG h_xv h_vX h_vVs] .
    show "\<exists>v\<in>Vs G - X. connected_component (G \<setminus> X) v = x \<and> odd (card x)"
    proof (intro bexI[of _ v])
      show "connected_component (G \<setminus> X) v = x \<and> odd (card x)"
      proof (intro conjI)
        show "connected_component (G \<setminus> X) v = x"
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
  assume h1: "connected_component (G \<setminus> X) v \<notin> singl_in_diff G X"
  assume h2: "v \<in> Vs G"
  assume h3: "v \<notin> X"
  assume h4: "odd (card (connected_component (G \<setminus> X) v))"
  have v_in_Vs_diff: "v \<in> Vs (G \<setminus> X)"
  proof (rule ccontr)
    assume v_notin: "v \<notin> Vs (G \<setminus> X)"
    then have cc_is_singl: "connected_component (G \<setminus> X) v = {v}"
      by (rule connected_components_notE_singletons)
    have "{v} \<in> singl_in_diff G X"
      using h2 h3 v_notin by (simp add: singl_in_diffI)
    with h1 show False using cc_is_singl by simp
  qed
  have odd_comp: "odd_component (G \<setminus> X) (connected_component (G \<setminus> X) v)"
    using h4 v_in_Vs_diff by (rule odd_componentI) simp
  from odd_comp show "connected_component (G \<setminus> X) v \<in> odd_components (G \<setminus> X)"
    by (simp add: odd_components_def)
qed

lemma odd_comps_in_diff_are_componentsOb:
  assumes "C \<in> odd_comps_in_diff G X"
  obtains v where "v\<in>Vs G-X" 
    "connected_component (G \<setminus> X) v = C"
    "odd (card C)"
  using odd_comps_in_diff_are_components[of G X] 
  using assms by fastforce

lemma odd_comps_in_diff_are_componentsI:
  assumes "odd (card C)"
  assumes "v\<in>Vs G-X"
  assumes "connected_component (G \<setminus> X) v = C"
  shows "C \<in> odd_comps_in_diff G X"
  using odd_comps_in_diff_are_components[of G X] 
  using assms by fastforce

lemma odd_comps_in_diff_are_componentsI2:
  assumes "odd (card C)"
  assumes "C \<in> connected_components (G \<setminus> X)"
  shows "C \<in> odd_comps_in_diff G X"
proof -
  from assms(2) obtain w where w_in_Vs: "w \<in> Vs (G \<setminus> X)" and C_eq: "C = connected_component (G \<setminus> X) w"
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
  have comp_eq_C1: "connected_component (G \<setminus> X) x = C1"
    using assms(1) xC1 by (rule odd_comps_in_diff_is_component)
  have comp_eq_C2: "connected_component (G \<setminus> X) x = C2"
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
  shows "Vs (G \<setminus> X) \<union> Vs (singl_in_diff G X) \<union> X = Vs G"
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
  shows "Vs (G \<setminus> X) \<inter> Vs (singl_in_diff G X) = {}" 
    "Vs (G \<setminus> X) \<inter> X = {}"
    "Vs (singl_in_diff G X) \<inter> X = {}"
  proof safe
    fix x
    assume h1: "x \<in> Vs (G \<setminus> X)" and h2: "x \<in> Vs (singl_in_diff G X)"
    have "{x} \<in> singl_in_diff G X"
      using h2 by (simp add: el_vs_singleton_is_in_singleton)
    then obtain v where hv: "v \<in> Vs G" "{x} = {v}" "v \<notin> X" "v \<notin> Vs (G \<setminus> X)"
      using singl_in_diffE by blast
    have "x = v"
      using hv(2) singletonD by blast
    show "x \<in> {}"
      using h1 hv(4) \<open>x = v\<close> by simp
  next
    fix x
    assume "x \<in> Vs (G \<setminus> X)" "x \<in> X"
    then show "x \<in> {}"
      unfolding Vs_def graph_diff_def by blast
  next
    fix x
    assume h1: "x \<in> Vs (singl_in_diff G X)" and h2: "x \<in> X"
    have "{x} \<in> singl_in_diff G X"
      using h1 by (simp add: el_vs_singleton_is_in_singleton)
    then obtain v where hv: "v \<in> Vs G" "{x} = {v}" "v \<notin> X" "v \<notin> Vs (G \<setminus> X)"
      using singl_in_diffE by blast
    have "x = v"
      using hv(2) singletonD by blast
    then show "x \<in> {}"
      using h2 hv(3) by simp
  qed

lemma diff_card_is_sum_elements:
  assumes "graph_invar G"
  assumes "X \<subseteq> Vs G"
  shows "card (Vs (G \<setminus> X)) + card (Vs (singl_in_diff G X)) + card X = card (Vs G)"
proof -
  (* Step 1: Name the two driver lemmas *)
  have union_eq: "Vs (G \<setminus> X) \<union> Vs (singl_in_diff G X) \<union> X = Vs G"
    by (rule diff_is_union_elements[OF assms])
  (* Step 2: Obtain the pairwise disjointness facts *)
  have disj12: "Vs (G \<setminus> X) \<inter> Vs (singl_in_diff G X) = {}"
    by (rule diff_disjoint_elements(1)[OF assms])
  have disj1X: "Vs (G \<setminus> X) \<inter> X = {}"
    by (rule diff_disjoint_elements(2)[OF assms])
  have disj2X: "Vs (singl_in_diff G X) \<inter> X = {}"
    by (rule diff_disjoint_elements(3)[OF assms])
  (* Step 3: Finiteness — derive from graph_invar via graph_invar_finite_Vs *)
  have fin_G: "finite (Vs G)"
    by (rule graph_invar_finite_Vs[OF assms(1)])
  have fin1: "finite (Vs (G \<setminus> X))"
    by (rule finite_subset[of _ "Vs G"]) (use union_eq fin_G in auto)
  have fin2: "finite (Vs (singl_in_diff G X))"
    by (rule finite_subset[of _ "Vs G"]) (use union_eq fin_G in auto)
  have fin3: "finite X"
    by (rule finite_subset[OF assms(2) fin_G])
  (* Step 4: Derive combined disjointness for the outer card_Un_disjoint call *)
  have disj_union_X: "(Vs (G \<setminus> X) \<union> Vs (singl_in_diff G X)) \<inter> X = {}"
    by (simp add: Int_Un_distrib2 disj1X disj2X)
  (* Step 5: Inner card_Un_disjoint *)
  have card12: "card (Vs (G \<setminus> X) \<union> Vs (singl_in_diff G X)) =
                card (Vs (G \<setminus> X)) + card (Vs (singl_in_diff G X))"
    by (rule card_Un_disjoint[OF fin1 fin2 disj12])
  (* Step 6: Outer card_Un_disjoint *)
  have card_all: "card (Vs (G \<setminus> X) \<union> Vs (singl_in_diff G X) \<union> X) =
                  card (Vs (G \<setminus> X) \<union> Vs (singl_in_diff G X)) + card X"
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
  shows "finite (odd_components (G \<setminus> X))" 
proof -
  have "finite (connected_components (G \<setminus> X))" 
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
  have fin_odd: "finite (odd_components (G \<setminus> X))"
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
  show "finite ((odd_components (G \<setminus> X)) \<union> (singl_in_diff G X))"
    using fin_odd fin_singl by (simp add: finite_Un)
qed

lemma diff_odd_component_card_is_sum:
  assumes "graph_invar G"
  assumes "X \<subseteq> Vs G"
  shows "card (odd_comps_in_diff G X) = 
        card (odd_components (G \<setminus>X)) + card (singl_in_diff G X)" 
  using finite_odd_comps_in_diff[of G X] 
  by (simp add: odd_components_inter_singl_empty 
      assms card_Un_disjoint odd_comps_in_diff_def)

lemma diff_odd_component_parity_sum:
  assumes "graph_invar G"
  assumes "X \<subseteq> Vs G"
  shows "even (card (odd_comps_in_diff G X) + card X ) = even (card (Vs G))"
proof -
  let ?odd = "(odd_components (G \<setminus>X))"
  let ?singl = "(singl_in_diff G X)"
  let ?EwoX = "(G \<setminus>X)"
  let ?allOdd = "odd_comps_in_diff G X"

  have "even (card ?allOdd + card X) =  even (card X + card ?odd + card ?singl)"
    using diff_odd_component_card_is_sum[of G X] assms 
    by presburger
  also have "\<dots> = even (card X + card (Vs ?EwoX) + card ?singl)" 
    using odd_components_eq_modulo_cardinality[of "?EwoX"] graph_invar_remove_vertices[of G X]
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

lemma empty_graph_odd_components:
  shows "odd_comps_in_diff {} X = {}" 
  unfolding odd_comps_in_diff_def
proof (rule equals0I)
  fix C
  assume "C \<in> odd_components ({} \<setminus> X) \<union> singl_in_diff {} X"
  then show False
    by (simp add: graph_diff_of_empty vs_member_elim odd_components_def odd_component_def singl_in_diff_def)
qed

lemma add_subset_change_odd_components:
  assumes "graph_invar G"
  assumes "X \<subseteq> Vs G"
  assumes "C \<in> (odd_comps_in_diff G X)"
  assumes "Y \<subseteq> C"
  assumes "Y \<noteq> {}"
  shows "odd_comps_in_diff G (X\<union>Y) = ((odd_comps_in_diff G X) - {C}) \<union>
    odd_comps_in_diff (component_edges (G \<setminus> X) C) Y"
proof(cases "C \<in> singl_in_diff G X")
  case True
  then have "C = Y" unfolding singl_in_diff_def
    using assms(5) assms(4) by blast

  then obtain x where singl_x:"C = {x}" "x \<in> Vs G" "x \<notin> X" "x \<notin> Vs (G \<setminus> X)"
    using True unfolding singl_in_diff_def by blast
  then have "Y = {x}" 
    by (simp add: \<open>C = Y\<close>)

  then have "(G \<setminus> X) = (G \<setminus> (X\<union>{x}))" 
    using `x \<notin> Vs (G \<setminus> X)`
    unfolding graph_diff_def   
    by blast 

  then have "(odd_components (G \<setminus> X)) = (odd_components (G \<setminus> (X\<union>{x})))"
    by auto
  have "(singl_in_diff G X) - {{x}} = singl_in_diff G (X \<union> {x})"
    unfolding singl_in_diff_def
    using \<open>(G \<setminus> X) = (G \<setminus> (X \<union> {x}))\<close>         
    by auto
  have "{x} \<notin> (odd_components (G \<setminus> X))" 
    using odd_components_elem_in_E singl_x(4) by blast
  then have "odd_comps_in_diff G (X\<union>{x}) = ((odd_comps_in_diff G X) - {{x}})"
    unfolding odd_comps_in_diff_def 
    by (simp add: Un_Diff \<open>G \<setminus> X = G \<setminus> (X \<union> {x})\<close> 
        \<open>singl_in_diff G X - {{x}} = singl_in_diff G (X \<union> {x})\<close>)


  have "(component_edges (G \<setminus> X) C) = {}"
  proof -
    have invar_diff: "graph_invar (G \<setminus> X)"
      by (rule graph_invar_remove_vertices[OF assms(1)])
    have "component_edges (G \<setminus> X) {x} = {}"
      by (rule component_edges_singleton_is_empty[OF invar_diff])
    then show ?thesis
      using singl_x(1) by simp
  qed
  then have "odd_comps_in_diff (component_edges (G \<setminus> X) C) Y = {}" 
    by (simp add: empty_graph_odd_components)

  then show ?thesis
  proof -
    have empty_comp: "odd_comps_in_diff (component_edges (G \<setminus> X) C) Y = {}"
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
  then have "C \<in> odd_components (G \<setminus> X)" 
    by (meson assms(3) odd_comps_in_diffE)
  then have odd_C: "odd_component (G \<setminus> X) C" 
    using odd_componentsE by blast
  show "odd_comps_in_diff G (X\<union>Y) = ((odd_comps_in_diff G X) - {C}) \<union>
    odd_comps_in_diff (component_edges (G \<setminus> X) C) Y" 
  proof 
    show " odd_comps_in_diff G (X \<union> Y) \<subseteq> odd_comps_in_diff G X - {C} \<union>
       odd_comps_in_diff (component_edges (G \<setminus> X) C) Y"
    proof
      fix C'
      assume asmC':"C' \<in> odd_comps_in_diff G (X \<union> Y)"
      then have "C' \<noteq> {}" 
        using odd_components_nonempty by blast
      then obtain c where "c \<in> C'" by auto
      then have conn_compC':"connected_component (G \<setminus> (X \<union> Y)) c = C'"
        by (rule odd_comps_in_diff_is_component[OF asmC'])

      show "C' \<in> odd_comps_in_diff G X - {C} \<union>
              odd_comps_in_diff (component_edges (G \<setminus> X) C) Y"
      proof(cases "c \<in> C")
        case True
        then have conn_compC: "connected_component (G \<setminus> X) c = C" 
          by (meson assms(3) odd_comps_in_diff_is_component)
        then have "c \<in> Vs (G \<setminus> X)" 
          using True \<open>C \<in> odd_components (G \<setminus> X)\<close> odd_components_elem_in_E by auto

        then obtain e where e: "e \<in> (G \<setminus> X)" "c \<in> e"  
          by (meson vs_member_elim)
        then have "e \<subseteq> C"
        proof -
          have invar_diff: "graph_invar (G \<setminus> X)"
            by (rule graph_invar_remove_vertices[OF assms(1)])
          have "e \<subseteq> connected_component (G \<setminus> X) c"
            using edge_subset_component[of "(G \<setminus> X)" e c] invar_diff e(1) e(2)
            by blast
          then show ?thesis
            using conn_compC by simp
        qed
        have "C' = connected_component (G \<setminus> (X\<union> Y)) c" 
          by (simp add: conn_compC')

        have "connected_component (G \<setminus> (X \<union> Y)) c = 
      connected_component ((component_edges (G \<setminus> X) C) \<setminus> Y) c"
        proof(safe)
          {
            fix x
            assume asm:"x \<in> connected_component (G \<setminus> (X\<union> Y)) c"
            show "x \<in> connected_component ((component_edges (G \<setminus> X) C) \<setminus> Y) c"
            proof(cases "x = c")
              case True
              then show ?thesis 
                by (simp add: in_own_connected_component)
            next
              case False
              then have "(\<exists>p. walk_betw (G \<setminus> (X\<union> Y)) x p c)"
                unfolding connected_component_def 
              proof -
                have "c \<in> connected_component (G \<setminus> (X \<union> Y)) x"
                  using asm by (rule connected_components_member_sym)
                with \<open>x \<noteq> c\<close> show ?thesis
                  by (fastforce elim: in_con_comp_has_walk)
              qed
              then obtain p where p_walk:"walk_betw (G \<setminus> (X\<union> Y)) x p c" 
                by auto
              then have "last p = c"
                by (simp add: walk_between_nonempty_pathD(4))
              then have "path (G \<setminus> (X\<union> Y)) p" 
                using p_walk unfolding walk_betw_def  by auto
              then have "\<forall>z \<in> set p.  z \<in> C \<and>
                   z \<in> connected_component ((component_edges (G \<setminus> X) C) \<setminus> Y) c"
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
                              ((component_edges (G \<setminus> X) C) \<setminus> Y) c"
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
                then have "{v, v'} \<in> (G \<setminus> X)"   
                  by (meson graph_diffE graph_diffI path2.hyps(1))
                then have "v \<in> C"
                proof -
                  have invar_diff_X: "graph_invar (G \<setminus> X)"
                    by (rule graph_invar_remove_vertices[OF assms(1)])
                  have v'_in_comp: "v' \<in> connected_component (G \<setminus> X) c"
                    using \<open>v' \<in> C\<close> conn_compC by simp
                  have comp_v'_eq: "connected_component (G \<setminus> X) v' = C"
                    using connected_components_member_eq[OF v'_in_comp] conn_compC by simp
                  have edge_sub: "{v, v'} \<subseteq> connected_component (G \<setminus> X) v'"
                    using edge_subset_component[OF invar_diff_X \<open>{v, v'} \<in> (G \<setminus> X)\<close>]
                    by simp
                  then have "v \<in> connected_component (G \<setminus> X) v'"
                    by blast
                  then show ?thesis
                    using comp_v'_eq by simp
                qed
                then have "{v, v'} \<in> (component_edges (G \<setminus> X) C)"
                  using \<open>v' \<in> C\<close> \<open>{v, v'} \<in> (G \<setminus> X)\<close> component_edges_def by blast     
                then have "{v, v'} \<in> ((component_edges (G \<setminus> X) C) \<setminus> Y)"
                  using \<open>{v, v'} \<inter> (X \<union> Y) = {}\<close> 
                  by (simp add: graph_diffI)       
                then have "v' \<in> connected_component 
                                ((component_edges (G \<setminus> X) C) \<setminus> Y) c"
                proof -
                  have "last (v' # vs) = c"
                    using path2.prems by (simp add: last_ConsR)
                  then have "\<forall>z \<in> set (v' # vs). z \<in> C \<and> 
                      z \<in> connected_component ((component_edges (G \<setminus> X) C) \<setminus> Y) c"
                    using path2.hyps(3) by blast
                  moreover have "v' \<in> set (v' # vs)"
                    by simp
                  ultimately show ?thesis
                    by blast
                qed
                then have "v \<in> connected_component 
                                ((component_edges (G \<setminus> X) C) \<setminus> Y) c"
                proof -
                  let ?H = "((component_edges (G \<setminus> X) C) \<setminus> Y)"
                  note v'_in_comp = \<open>v' \<in> connected_component ?H c\<close>
                  note edge_in_H  = \<open>{v, v'} \<in> ((component_edges (G \<setminus> X) C) \<setminus> Y)\<close>
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
                              ((component_edges (G \<setminus> X) C) \<setminus> Y) c"
                    by blast
                  show ?case
                  proof (rule ballI)
                    fix z
                    assume "z \<in> set (v # v' # vs)"
                    then consider (head) "z = v" | (tail) "z \<in> set (v' # vs)"
                      by auto
                    then show "z \<in> C \<and> z \<in> connected_component
                                          ((component_edges (G \<setminus> X) C) \<setminus> Y) c"
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
                          ((component_edges (G \<setminus> X) C) \<setminus> Y) c"
              proof -
                note all_z =
                  \<open>\<forall>z\<in>set p. z \<in> C \<and>
                       z \<in> connected_component
                             ((component_edges (G \<setminus> X) C) \<setminus> Y) c\<close>
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
          assume asm:"x \<in> connected_component ((component_edges (G \<setminus> X) C) \<setminus> Y) c" 
          show " x \<in> connected_component (G \<setminus> (X \<union> Y)) c"
          proof(cases "x = c")
            case True
            then show ?thesis 
              by (simp add: in_own_connected_component)
          next
            case False
            then have "(\<exists>p. walk_betw  ((component_edges (G \<setminus> X) C) \<setminus> Y) x p c)"
              unfolding connected_component_def 
              proof -
                have "c \<in> connected_component ((component_edges (G \<setminus> X) C) \<setminus> Y) x"
                  using asm by (rule connected_components_member_sym)
                with \<open>x \<noteq> c\<close> show ?thesis
                  by (fastforce elim: in_con_comp_has_walk)
              qed
            then obtain p where p_walk:
              "walk_betw  ((component_edges (G \<setminus> X) C) \<setminus> Y) x p c" 
              by auto
            then have "last p = c"
              by (simp add: walk_between_nonempty_pathD(4)) 
            then have "path  ((component_edges (G \<setminus> X) C) \<setminus> Y) p" 
              using p_walk unfolding walk_betw_def  by auto
            then have "\<forall>z \<in> set p. z \<in> connected_component (G \<setminus> (X \<union> Y)) c"
              using `last p = c`
            proof(induct p) 
              case path0
              then show ?case 
                by auto
            next
              case (path1 v)
              then show ?case 
                using \<open>C' = connected_component (G \<setminus> (X \<union> Y)) c\<close> \<open>c \<in> C'\<close> by auto

            next
              case (path2 v v' vs)
              have "last (v' # vs) = c" 
                using path2.prems 
                by auto
              have in_c: "\<forall>z\<in>set (v' # vs). z \<in> connected_component (G \<setminus> (X \<union> Y)) c" 
                using \<open>last (v' # vs) = c\<close> path2.hyps(3) by blast
              have "{v, v'} \<in> ((component_edges (G \<setminus> X) C) \<setminus> Y)" 
                by (simp add: path2.hyps(1))
              then have "{v, v'} \<inter> Y = {}" 
                unfolding graph_diff_def 
                by fastforce
              have "{v, v'} \<in>  (component_edges (G \<setminus> X) C)" 
                using graph_diff_subset path2.hyps(1) by blast
              then have "{v, v'} \<in> (G \<setminus> X)" 
                using component_edges_subset  Connected_Components.component_edges_subset 
                      insert_Diff insert_subset
                by blast
              then have "{v, v'} \<inter> X = {}"
                unfolding graph_diff_def  
                by fastforce
              then have "{v, v'} \<in> (G \<setminus> (X\<union>Y))"
                unfolding graph_diff_def 
                using `{v, v'} \<inter> Y = {}` \<open>{v, v'} \<in> G \<setminus> X\<close> graph_diff_def by fastforce
              then have "v' \<in> connected_component (G \<setminus> (X\<union>Y)) c" 
                by (simp add: in_c)
              then have "v \<in> connected_component (G \<setminus> (X\<union>Y)) c"
              proof -
                have step1: "v' \<in> connected_component (G \<setminus> (X \<union> Y)) v"
                  by (rule vertices_edges_in_same_component[OF \<open>{v, v'} \<in> (G \<setminus> (X \<union> Y))\<close>])
                have step2: "v \<in> connected_component (G \<setminus> (X \<union> Y)) v'"
                  by (rule connected_components_member_sym[OF step1])
                have step3: "connected_component (G \<setminus> (X \<union> Y)) v' =
                             connected_component (G \<setminus> (X \<union> Y)) c"
                  by (rule connected_components_member_eq[OF \<open>v' \<in> connected_component (G \<setminus> (X\<union>Y)) c\<close>])
                show ?thesis
                  using step2 step3 by simp
              qed
              then show ?case 
                using in_c by fastforce
            qed 
            note all_in_comp = this
            show ?thesis
            proof -
              have p_nonempty: "p \<noteq> []"
                using p_walk unfolding walk_betw_def by simp
              have hd_x: "hd p = x"
                using p_walk unfolding walk_betw_def by simp
              have x_in_p: "x \<in> set p"
                using hd_in_set[OF p_nonempty] hd_x by simp
              show ?thesis
                using all_in_comp x_in_p by blast
            qed
          qed
        qed
        then have c_in_diff:
          "connected_component ((component_edges (G \<setminus> X) C) \<setminus> Y) c = C'"
          using conn_compC' by presburger
        have "odd (card C')" 
          using asmC' diff_odd_compoenent_has_odd_card by auto
        have c_in_C: "c \<in> Vs (component_edges (G \<setminus> X) C)"
        proof -
          from edge_in_component_edges[OF graph_invar_remove_vertices[OF assms(1)] e(1) \<open>e \<subseteq> C\<close>] 
          have e_in_comp: "e \<in> component_edges (G \<setminus> X) C" .
          show ?thesis
            using e(2) e_in_comp vs_member_intro by blast
        qed
        have "c \<notin> Y"
          by (meson \<open>c \<in> C'\<close> asmC' disjoint_iff_not_equal 
              odd_comps_in_diff_not_in_X subsetD sup_ge2)
        then have "c \<in> Vs (component_edges (G \<setminus> X) C) - Y" 
          using c_in_C by blast
        then have "C' \<in> odd_comps_in_diff (component_edges (G \<setminus> X) C) Y"
          using c_in_diff \<open>odd (card C')\<close>  by (meson odd_comps_in_diff_are_componentsI)
        then show "C' \<in> odd_comps_in_diff G X - {C} \<union>
                   odd_comps_in_diff (component_edges (G \<setminus> X) C) Y" 
          by (simp add: odd_comps_in_diff_def)
      next
        case False
        then  have "c \<notin> C" by auto
        have "connected_component (G \<setminus> X) c = connected_component (G \<setminus> (X \<union> Y)) c"
        proof(safe)
          {
            fix x
            assume asmx:"x \<in> connected_component (G \<setminus> X) c"
            show " x \<in> connected_component (G \<setminus> (X \<union> Y)) c"
            proof(cases "x = c")
              case True
              then show ?thesis
                by (simp add: in_own_connected_component)
            next
              case False
              then have "\<exists>p. walk_betw (G \<setminus> X) x p c"
                unfolding connected_component_def
              proof -
                have sym: "c \<in> connected_component (G \<setminus> X) x"
                  using asmx by (rule connected_components_member_sym)
                with \<open>x \<noteq> c\<close> show ?thesis
                  by (fastforce elim: in_con_comp_has_walk)
              qed
              then obtain p where p_walk:"walk_betw (G \<setminus> X) x p c" by auto
              then have "last p = c"
                by (simp add: walk_between_nonempty_pathD(4))
              then have "path (G \<setminus> X) p" 
                using p_walk unfolding walk_betw_def  by auto
              then have "\<forall>z \<in> set p. z \<in> C' \<and> z \<notin> C \<and> z \<in> connected_component (G \<setminus> X) c"
                using `last p = c`
              proof(induct p) 
                case path0
                then show ?case 
                  by auto
              next
                case (path1 v)
                then show ?case
                  using \<open>c \<in> C'\<close> \<open>c \<notin> C\<close>
                proof -
                  have v_eq_c: "v = c"
                    using path1.prems by simp
                  show ?thesis
                    using v_eq_c \<open>c \<in> C'\<close> \<open>c \<notin> C\<close> in_own_connected_component by auto
                qed
              next
                case (path2 v v' vs)
                have "last (v' # vs) = c" 
                  using path2.prems 
                  by auto
                have zhyps: "\<forall>z\<in>set (v' # vs). z \<in> C' \<and> z \<notin> C \<and> 
                      z \<in> connected_component (G \<setminus> X) c" 
                  using \<open>last (v' # vs) = c\<close> path2.hyps(3) by blast
                have "{v, v'} \<in> (G \<setminus> X)" 
                  by (simp add: path2.hyps(1))
                then have "v' \<in> connected_component (G \<setminus> X) c" 
                  by (simp add: zhyps)
                then have "v \<in> connected_component (G \<setminus> X) v'"
                  by (meson connected_components_member_sym path2.hyps(1) 
                      vertices_edges_in_same_component)
                then have "v \<in> connected_component (G \<setminus> X) c"
                  by (meson \<open>v' \<in> connected_component (G \<setminus> X) c\<close> 
                      connected_components_member_trans)
                then have "v \<notin> C" 
proof -
                    show ?thesis
                    proof (rule notI)
                      assume v_in_C: "v \<in> C"
                      have v'_not_C: "v' \<notin> C"
                        using zhyps list.set_intros(1) by auto
                      have comp_eq: "connected_component (G \<setminus> X) v = C"
                        by (rule odd_comps_in_diff_is_component[OF assms(3) v_in_C])
                      have "v' \<in> connected_component (G \<setminus> X) v"
                        by (rule vertices_edges_in_same_component[OF \<open>{v, v'} \<in> (G \<setminus> X)\<close>])
                      then have "v' \<in> C"
                        using comp_eq by simp
                      with v'_not_C show False by contradiction
                    qed
                  qed
                then have "v \<notin> Y" 
                  using assms(4) by blast
                have "v' \<notin> Y" 
                  by (meson zhyps assms(4) list.set_intros(1) subsetD)
                then have "{v, v'} \<inter> (Y) = {}" 
                  by (simp add: \<open>v \<notin> Y\<close>)
                have "{v, v'} \<inter> X = {}"
                  using `{v, v'} \<in> (G \<setminus> X)`
                  unfolding graph_diff_def  
                  by fastforce
                then have "{v, v'} \<inter> (X\<union>Y) = {}" 
                  by (simp add: Int_Un_distrib \<open>{v, v'} \<inter> Y = {}\<close>)
                then have "{v, v'} \<in> (G \<setminus> (X \<union> Y))" 
                  using path2.hyps(1)
                  unfolding graph_diff_def by blast
                then have "v \<in> C'"
                proof -
                  have v'_in_C': "v' \<in> C'"
                    using zhyps by simp
                  have v'_in_comp: "v' \<in> connected_component (G \<setminus> (X \<union> Y)) c"
                    using v'_in_C' conn_compC' by simp
                  have edge_comm: "{v', v} \<in> (G \<setminus> (X \<union> Y))"
                    using \<open>{v, v'} \<in> (G \<setminus> (X \<union> Y))\<close>
                    by (simp add: insert_commute)
                  have v_in_comp_v': "v \<in> connected_component (G \<setminus> (X \<union> Y)) v'"
                    by (rule vertices_edges_in_same_component[OF edge_comm])
                  have comp_eq: "connected_component (G \<setminus> (X \<union> Y)) v' =
                                 connected_component (G \<setminus> (X \<union> Y)) c"
                    by (rule connected_components_member_eq[OF v'_in_comp])
                  show ?thesis
                    using v_in_comp_v' comp_eq conn_compC' by simp
                qed
                then show ?case 
                  using \<open>v \<in> connected_component (G \<setminus> X) c\<close> \<open>v \<notin> C\<close> zhyps by auto
              qed
              note all_z = this
              have "x \<in> C' \<and> x \<notin> C \<and> x \<in> connected_component (G \<setminus> X) c"
              proof -
                have p_nonempty: "p \<noteq> []"
                  using p_walk unfolding walk_betw_def by simp
                have hd_x: "hd p = x"
                  using p_walk unfolding walk_betw_def by simp
                have x_in_p: "x \<in> set p"
                  using hd_in_set[OF p_nonempty] hd_x by simp
                show ?thesis
                  using all_z x_in_p by blast
              qed
              then show " x \<in> connected_component (G \<setminus> (X \<union> Y)) c" 
                using conn_compC' by auto
            qed
          }
          fix x
          assume asmx:"x \<in> connected_component (G \<setminus> (X \<union> Y)) c"
          show " x \<in> connected_component (G \<setminus> X) c"
          proof(cases "x = c")
            case True
            then show ?thesis 
              by (simp add: in_own_connected_component)
          next
            case False
            then have "\<exists>p. walk_betw (G \<setminus> (X \<union> Y)) x p c"
              proof -
                have "c \<in> connected_component (G \<setminus> (X \<union> Y)) x"
                  using asmx by (rule connected_components_member_sym)
                with \<open>x \<noteq> c\<close> show ?thesis
                  by (fastforce elim: in_con_comp_has_walk)
              qed
            then obtain p where p_walk:"walk_betw (G \<setminus> (X \<union> Y)) x p c" 
              by auto
            then have "last p = c"
              by (simp add: walk_between_nonempty_pathD(4))
            then have "path (G \<setminus> (X \<union> Y)) p" 
              using p_walk unfolding walk_betw_def by auto
            then have "\<forall>z \<in> set p. z \<in> connected_component (G \<setminus> X) c"
              using `last p = c`
            proof(induct p) 
              case path0
              then show ?case 
                by auto
            next
              case (path1 v)
              then have "v = c" by simp
              then show ?case by (simp add: in_own_connected_component)
            next
              case (path2 v v' vs)
              have "last (v' # vs) = c" 
                using path2.prems 
                by auto
              have zhyps:"\<forall>z\<in>set (v' # vs). z \<in> connected_component (G \<setminus> X) c" 
                using \<open>last (v' # vs) = c\<close> path2.hyps(3) by blast
              have "{v, v'} \<in> (G \<setminus> (X \<union> Y))" 
                by (simp add: path2.hyps(1))
              then have "{v, v'} \<in> (G \<setminus> (X))"
                unfolding graph_diff_def  
                by blast
              then have "v' \<in> connected_component (G \<setminus> X) c" 
                by (simp add: zhyps)
              then show ?case
              proof -
                have v'_in_comp: "v' \<in> connected_component (G \<setminus> X) c" by fact
                have v'_in_comp_v: "v' \<in> connected_component (G \<setminus> X) v"
                  by (rule vertices_edges_in_same_component[OF \<open>{v, v'} \<in> (G \<setminus> X)\<close>])
                have v_in_comp_v': "v \<in> connected_component (G \<setminus> X) v'"
                  by (rule connected_components_member_sym[OF v'_in_comp_v])
                have comp_v'_eq_c:
                  "connected_component (G \<setminus> X) v' = connected_component (G \<setminus> X) c"
                  by (rule connected_components_member_eq[OF v'_in_comp])
                have v_in_comp_c: "v \<in> connected_component (G \<setminus> X) c"
                  using v_in_comp_v' comp_v'_eq_c by simp
                show "\<forall>z\<in>set (v # v' # vs). z \<in> connected_component (G \<setminus> X) c"
                  using v_in_comp_c zhyps by auto
              qed
            qed
            show " x \<in> connected_component (G \<setminus> (X)) c" 
            proof -
              have all_in_p: "\<forall>z\<in>set p. z \<in> connected_component (G \<setminus> X) c"
                using \<open>\<forall>z\<in>set p. z \<in> connected_component (G \<setminus> X) c\<close> .
              have p_nonempty: "p \<noteq> []"
                using p_walk unfolding walk_betw_def by simp
              have hd_x: "hd p = x"
                using p_walk unfolding walk_betw_def by simp
              have x_in_p: "x \<in> set p"
                using hd_in_set[OF p_nonempty] hd_x by simp
              show ?thesis
                using all_in_p x_in_p by blast
            qed

          qed
        qed
        then have conn_compC: "connected_component (G \<setminus> X) c = C'" 
          using conn_compC' by fastforce
        have "C' \<in> odd_comps_in_diff G X"
        proof(cases "C' \<in> singl_in_diff G (X \<union> Y)")
          case True
          then have "C' = {c}" 
            apply(elim singl_in_diffE)
            using \<open>c \<in> C'\<close> by fastforce
          have "connected_component (G \<setminus> X) c = {c}" 
            by (simp add: \<open>C' = {c}\<close> conn_compC)
          have "c \<notin> Vs (G \<setminus> X)"
          proof(rule ccontr)
            assume " \<not> c \<notin> Vs (G \<setminus> X)"
            then have "\<exists> e. c \<in> e \<and> e \<in> (G \<setminus> X)" 
              by (meson vs_member_elim)
            then obtain e where e: "c \<in> e \<and> e \<in> (G \<setminus> X)" 
              by auto
            then have "e \<subseteq> connected_component (G \<setminus> X) c" 
            proof -
              have invar_diff: "graph_invar (G \<setminus> X)"
                by (rule graph_invar_remove_vertices[OF assms(1)])
              have c_in_e: "c \<in> e" using e by simp
              have e_in_diff: "e \<in> (G \<setminus> X)" using e by simp
              show "e \<subseteq> connected_component (G \<setminus> X) c"
                using edge_subset_component[of "(G \<setminus> X)" e c]
                      invar_diff e_in_diff c_in_e
                by blast
            qed
            then show False
              using \<open>connected_component (G \<setminus> X) c = {c}\<close> assms(1) e graph_invar_remove_vertices
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
          have "C' \<in> odd_components (G \<setminus> (X \<union> Y))" 
          proof -
            have "C' \<in> odd_components (G \<setminus> (X \<union> Y)) \<union> singl_in_diff G (X \<union> Y)"
              using asmC' unfolding odd_comps_in_diff_def .
            then show ?thesis
              using False by blast
          qed
          then have "odd (card C')" 
            by (simp add: odd_components_def odd_component_def)
          have "c\<in>Vs (G \<setminus> X)"
          proof(rule ccontr)
            assume "c \<notin> Vs (G \<setminus> X)"
            have c_notin_U:"c \<notin>  Vs (G \<setminus> (X\<union>Y))"
            proof(rule ccontr)
              assume " \<not> c \<notin> Vs (G \<setminus> (X \<union> Y))"
              then have "\<exists>e. c \<in> e \<and> e \<in> (G \<setminus> (X \<union> Y))" 
                by (meson vs_member_elim)
              then obtain e where e:"c \<in> e \<and> e \<in> G \<setminus> (X \<union> Y)"
                by auto
              then have "e \<inter> (X \<union> Y) = {}" 
                by (simp add: graph_diff_def)
              then have "e \<inter> X = {}"
                by auto
              then have "e \<in> G \<setminus> X" 
                unfolding graph_diff_def 
                using e graph_diff_member by fastforce
              then have "c \<in> Vs (G \<setminus> X)" 
                using \<open>c \<in> e \<and> e \<in> G \<setminus> (X \<union> Y)\<close> 
                by blast
              then show False 
                using \<open>c \<notin> Vs (G \<setminus> X)\<close> by blast
            qed
            have "c \<notin> X \<union> Y" 
            proof
              assume c_in_XY: "c \<in> X \<union> Y"
              have disj: "C' \<inter> (X \<union> Y) = {}"
                using odd_comps_in_diff_not_in_X asmC' by blast
              then show False
                using \<open>c \<in> C'\<close> c_in_XY by blast
            qed
            then have "{c} \<in> singl_in_diff G (X \<union> Y)" 
              unfolding singl_in_diff_def 
              using \<open>c \<in> C'\<close> c_notin_U asmC' component_in_E by fastforce
            then have "{c} \<in> odd_comps_in_diff G (X \<union> Y)" 
              by (simp add: odd_comps_in_diff_def)
            then have "connected_component (G \<setminus> (X \<union> Y)) c = {c}" 
              by (simp add: c_notin_U connected_components_notE_singletons)
            then have "C' = {c}" 
              by (simp add: conn_compC')
            then have "C' \<in> singl_in_diff G (X \<union> Y)" 
              by (simp add: \<open>{c} \<in> singl_in_diff G (X\<union>Y)\<close>)
            then show False 
              by (simp add: False)
          qed
          then have "C' \<in> odd_components (G \<setminus> X)"
            unfolding odd_components_def 
            by (simp add: \<open>odd (card C')\<close> conn_compC odd_componentI)
          then show ?thesis 
            by (simp add: odd_comps_in_diff_def)
        qed
        then show "C' \<in> odd_comps_in_diff G X - {C} \<union>
                   odd_comps_in_diff (component_edges (G \<setminus> X) C) Y"
          using False \<open>c \<in> C'\<close> by blast
      qed
    qed
    show " odd_comps_in_diff G X - {C} \<union> odd_comps_in_diff
     (component_edges (G \<setminus> X) C) Y \<subseteq> odd_comps_in_diff G (X \<union> Y)"
    proof
      fix C'
      assume asmC'odd:"C' \<in> odd_comps_in_diff G X - {C} \<union> odd_comps_in_diff
              (component_edges (G \<setminus> X) C) Y"
      show "C' \<in> odd_comps_in_diff G (X \<union> Y)"
      proof(cases "C' \<in> odd_comps_in_diff G X - {C}")
        case True
        then have "C' \<noteq> C" 
          by blast
        then have "C' \<inter> C = {}"
        proof -
          have C'_in: "C' \<in> odd_comps_in_diff G X"
            using True by blast
          show "C' \<inter> C = {}"
            using diff_component_disjoint[OF C'_in assms(3)] \<open>C' \<noteq> C\<close>
            by (simp add: Int_commute)
        qed
        have C'_odd: "C' \<in> odd_comps_in_diff G X" 
          using True by auto
        have "C' \<noteq> {}" 
          using C'_odd odd_components_nonempty by blast
        then obtain c where "c \<in> C'" 
          by blast
        then have conn_C':"connected_component (G \<setminus> X) c = C'" 
          by (simp add: C'_odd assms(1) assms(3) odd_comps_in_diff_is_component)
        have "c \<notin> C" 
          using \<open>C' \<inter> C = {}\<close> \<open>c \<in> C'\<close> by blast
        have conn_same: "connected_component (G \<setminus> X) c = 
                         connected_component (G \<setminus> (X \<union> Y)) c"
        proof(safe)
          {
            fix x
            assume asmx:"x \<in> connected_component (G \<setminus> X) c"
            show "x \<in> connected_component (G \<setminus> (X \<union> Y)) c"
            proof(cases "x = c")
              case True
              then show ?thesis 
                by (simp add: in_own_connected_component)
            next
              case False
              then have "\<exists>p. walk_betw (G \<setminus> X) x p c"
              proof -
                have sym: "c \<in> connected_component (G \<setminus> X) x"
                  using asmx by (rule connected_components_member_sym)
                with \<open>x \<noteq> c\<close> show ?thesis
                  by (fastforce elim: in_con_comp_has_walk)
              qed
              then obtain p where p_walk:"walk_betw (G \<setminus> X) x p c"
                by auto
              then have "last p = c"
                by (simp add: walk_between_nonempty_pathD(4))
              then have "path (G \<setminus> X) p" 
                using p_walk unfolding walk_betw_def  by auto
              then have "\<forall>z \<in> set p. z \<in> C' \<and> z \<notin> C \<and> z \<in> connected_component (G \<setminus> (X\<union>Y)) c"
                using `last p = c`
              proof(induct p) 
                case path0
                then show ?case 
                  by auto
              next
                case (path1 v)
                then have v_eq_c: "v = c" by simp
                show ?case
                  using v_eq_c \<open>c \<in> C'\<close> \<open>c \<notin> C\<close> in_own_connected_component by auto
              next
                case (path2 v v' vs)
                have "last (v' # vs) = c" 
                  using path2.prems by auto
                have zhyp: "\<forall>z\<in>set (v' # vs). z \<in> C' \<and> z \<notin> C \<and>
                             z \<in> connected_component (G \<setminus> (X \<union> Y)) c" 
                  using \<open>last (v' # vs) = c\<close> path2.hyps(3) by blast
                have "{v, v'} \<in> (G \<setminus> X)" 
                  by (simp add: path2.hyps(1))
                then have "{v, v'} \<inter> X = {}"
                  unfolding graph_diff_def by blast
                then have v'_conn:"v' \<in> connected_component (G \<setminus> X) c" 
                  by (simp add: conn_C' zhyp)
                then have "v \<in> connected_component (G \<setminus> X) v'"
                  by (meson connected_components_member_sym path2.hyps(1) 
                      vertices_edges_in_same_component)
                then have "v \<notin> C"
                proof -
                  have v_in_comp_v': "v \<in> connected_component (G \<setminus> X) v'"
                    by fact
                  have v'_in_C': "v' \<in> C'"
                    using zhyp by simp
                  have v'_in_comp_c: "v' \<in> connected_component (G \<setminus> X) c"
                    using conn_C' v'_in_C' by simp
                  have comp_v'_eq_C': "connected_component (G \<setminus> X) v' = C'"
                    using connected_components_member_eq[OF v'_in_comp_c] conn_C' by simp
                  have v_in_C': "v \<in> C'"
                    using v_in_comp_v' comp_v'_eq_C' by simp
                  show ?thesis
                    using v_in_C' \<open>C' \<inter> C = {}\<close> by blast
                qed
                then have "v \<notin> Y" 
                  using assms(4) by blast
                have "v' \<notin> Y" 
                  using assms(4) zhyp by auto
                then have "{v, v'} \<inter> Y = {}" 
                  by (simp add: \<open>v \<notin> Y\<close>)
                have "{v, v'} \<inter> X = {}"
                  using `{v, v'} \<in> (G \<setminus> X)` 
                  unfolding graph_diff_def  
                  by fastforce
                then have "{v, v'} \<inter> (X \<union> Y) = {}" 
                  by (simp add: Int_Un_distrib \<open>{v, v'} \<inter> Y = {}\<close>)
                then have "{v, v'} \<in> (G \<setminus> (X \<union> Y))"
                proof -
                  have in_G: "{v, v'} \<in> G"
                    using path2.hyps(1) graph_diff_subset by blast
                  show ?thesis
                    using in_G \<open>{v, v'} \<inter> (X \<union> Y) = {}\<close>
                    unfolding graph_diff_def by blast
                qed
                then show ?case 
                proof -
                  have edge_XY: "{v, v'} \<in> (G \<setminus> (X \<union> Y))" by fact
                  have v'_in_C': "v' \<in> C'"
                    using zhyp by simp
                  have v'_in_comp_c: "v' \<in> connected_component (G \<setminus> X) c"
                    using v'_in_C' conn_C' by simp
                  have comp_v'_eq_C': "connected_component (G \<setminus> X) v' = C'"
                    using connected_components_member_eq[OF v'_in_comp_c] conn_C' by simp
                  have v_in_C': "v \<in> C'"
                    using \<open>v \<in> connected_component (G \<setminus> X) v'\<close> comp_v'_eq_C' by simp
                  have v'_in_comp_XY: "v' \<in> connected_component (G \<setminus> (X \<union> Y)) c"
                    using zhyp by simp
                  have v'_in_comp_v: "v' \<in> connected_component (G \<setminus> (X \<union> Y)) v"
                    by (rule vertices_edges_in_same_component[OF edge_XY])
                  have v_in_comp_v': "v \<in> connected_component (G \<setminus> (X \<union> Y)) v'"
                    by (rule connected_components_member_sym[OF v'_in_comp_v])
                  have comp_v'_eq_c: "connected_component (G \<setminus> (X \<union> Y)) v' =
                                      connected_component (G \<setminus> (X \<union> Y)) c"
                    by (rule connected_components_member_eq[OF v'_in_comp_XY])
                  have v_in_comp_c: "v \<in> connected_component (G \<setminus> (X \<union> Y)) c"
                    using v_in_comp_v' comp_v'_eq_c by simp
                  show ?thesis
                    using v_in_C' \<open>v \<notin> C\<close> v_in_comp_c zhyp by auto
                qed
              qed
              then show "x \<in> connected_component (G \<setminus> (X \<union> Y)) c" 
                using p_walk walk_between_nonempty_pathD(3) by fastforce
            qed
          }
          fix x
          assume asmx: "x \<in> connected_component (G \<setminus> (X \<union> Y)) c"
          show "x \<in> connected_component (G \<setminus> X) c"
          proof(cases "x = c")
            case True
            then show ?thesis 
              by (simp add: in_own_connected_component)
          next 
            case False
            then have "\<exists>p. walk_betw (G \<setminus> (X \<union> Y)) x p c"
              proof -
                have "c \<in> connected_component (G \<setminus> (X \<union> Y)) x"
                  using asmx by (rule connected_components_member_sym)
                with \<open>x \<noteq> c\<close> show ?thesis
                  by (fastforce elim: in_con_comp_has_walk)
              qed
            then obtain p where p_walk:"walk_betw (G \<setminus> (X \<union> Y)) x p c"
              by auto
            then have "last p = c"
              by (simp add: walk_between_nonempty_pathD(4))
            then have "path (G \<setminus> (X \<union> Y)) p" 
              using p_walk unfolding walk_betw_def  by auto
            then have "\<forall>z \<in> set p. z \<in> connected_component (G \<setminus> X) c"
              using `last p = c`
            proof(induct p) 
              case path0
              then show ?case 
                by auto
            next  case (path1 v)
  then have "v = c" by simp
  then show ?case by (simp add: in_own_connected_component)
            next
              case (path2 v v' vs)
              have "last (v' # vs) = c" 
                using path2.prems 
                by auto
              have zhyp: "\<forall>z\<in>set (v' # vs). z \<in> connected_component (G \<setminus> X) c" 
                using \<open>last (v' # vs) = c\<close> path2.hyps(3) by blast
              have "{v, v'} \<in> G \<setminus> (X \<union> Y)" 
                by (simp add: path2.hyps(1))
              then have "{v, v'} \<in> G \<setminus> X" 
                unfolding graph_diff_def  
                by blast
              then have "v' \<in> connected_component (G \<setminus> X) c" 
                by (simp add: zhyp)
              then show ?case
              proof -
                have v'_in_comp_c: "v' \<in> connected_component (G \<setminus> X) c"
                  by fact
                have v'_in_comp_v: "v' \<in> connected_component (G \<setminus> X) v"
                  by (rule vertices_edges_in_same_component[OF \<open>{v, v'} \<in> (G \<setminus> X)\<close>])
                have v_in_comp_v': "v \<in> connected_component (G \<setminus> X) v'"
                  by (rule connected_components_member_sym[OF v'_in_comp_v])
                have comp_eq:
                  "connected_component (G \<setminus> X) v' = connected_component (G \<setminus> X) c"
                  by (rule connected_components_member_eq[OF v'_in_comp_c])
                have v_in_comp_c: "v \<in> connected_component (G \<setminus> X) c"
                  using v_in_comp_v' comp_eq by simp
                show "\<forall>z\<in>set (v # v' # vs). z \<in> connected_component (G \<setminus> X) c"
                  using v_in_comp_c zhyp by auto
              qed
            qed
            then show "x \<in> connected_component (G \<setminus> (X)) c" 
            proof -
              have p_nonempty: "p \<noteq> []"
                using p_walk unfolding walk_betw_def by simp
              have hd_x: "hd p = x"
                using p_walk unfolding walk_betw_def by simp
              have x_in_p: "x \<in> set p"
                using hd_in_set[OF p_nonempty] hd_x by simp
              with \<open>\<forall>z\<in>set p. z \<in> connected_component (G \<setminus> X) c\<close>
              show ?thesis by blast
            qed
          qed
        qed
        then have conn_diff_C':"connected_component (G \<setminus> (X \<union> Y)) c = C'" 
          using conn_C' by presburger
        show "C' \<in> odd_comps_in_diff G (X \<union> Y)"
        proof(cases "C' \<in> singl_in_diff G X")
          case True
          then have "C' = {c}" 
            apply(elim singl_in_diffE)
            using \<open>c \<in> C'\<close> by fastforce
          then have comp_singl:"connected_component (G \<setminus> (X \<union> Y)) c = {c}" 
            using conn_diff_C' by auto
          then have "c \<notin>  Vs (G \<setminus> X)" 
            using True
            apply(elim singl_in_diffE)
            using \<open>c \<in> C'\<close> by blast
          have c_notin_diff:"c \<notin> Vs (G \<setminus> (X \<union> Y))"
          proof(rule ccontr)
            assume "\<not> c \<notin> Vs (G \<setminus> (X \<union> Y))"   
            then obtain e where e:"c \<in> e \<and> e \<in> (G \<setminus> (X \<union> Y))"
              by (meson vs_member_elim)
            then have "e \<subseteq> connected_component (G \<setminus> (X \<union> Y)) c"
              by (simp add: assms(1) edge_subset_component graph_invar_remove_vertices)
            then show False
              using assms(1) comp_singl e graph_invar_remove_vertices
              by fastforce          qed
        have "c \<notin> X \<union> Y"
        proof (rule notI)
          assume h: "c \<in> X \<union> Y"
          have c_notin_X: "c \<notin> X"
          proof -
            have "C' \<inter> X = {}"
              using C'_odd odd_comps_in_diff_not_in_X by blast
            then show ?thesis
              using \<open>c \<in> C'\<close> by blast
          qed
          have c_notin_Y: "c \<notin> Y"
            using \<open>c \<notin> C\<close> assms(4) by blast
          show False
            using h c_notin_X c_notin_Y by blast
        qed
        then have "{c} \<in> singl_in_diff G (X \<union> Y)" 
            by (meson C'_odd \<open>c \<in> C'\<close> c_notin_diff component_in_E singl_in_diffI subsetD)
          then have "C' \<in> singl_in_diff G (X\<union>Y)" 
            by (simp add: \<open>C' = {c}\<close>)
          then show ?thesis 
            by (simp add: odd_comps_in_diff_def)
        next
          case False
          then have "C' \<in> odd_components (G \<setminus> X)" 
            using C'_odd odd_comps_in_diffE by blast
          then have "odd (card C')" 
            by (simp add: odd_components_def odd_component_def)
          have "c \<notin> X \<union> Y"
          proof -
            have "c \<notin> X"
            proof -
              have "C' \<inter> X = {}"
                using C'_odd odd_comps_in_diff_not_in_X by blast
              then show ?thesis
                using \<open>c \<in> C'\<close> by blast
            qed
            moreover have "c \<notin> Y"
              using \<open>c \<notin> C\<close> assms(4) by blast
            ultimately show ?thesis by blast
          qed
          have "c \<in> Vs (G \<setminus> X)"
            using \<open>C' \<in> odd_components (G \<setminus> X)\<close> \<open>c \<in> C'\<close> odd_components_elem_in_E by auto
          then obtain e where e:"c \<in> e \<and> e \<in> (G \<setminus> X)" 
            by (meson vs_member_elim)
          then have e_unfold:"c \<in> e \<and> e \<in> G \<and> e \<inter> X = {}" 
            by (simp add: graph_diff_def)
          have "e \<subseteq> C'"
          proof -
            have invar_diff: "graph_invar (G \<setminus> X)"
              by (rule graph_invar_remove_vertices[OF assms(1)])
            have c_in_e: "c \<in> e"
              using e by blast
            have e_in_diff: "e \<in> (G \<setminus> X)"
              using e by blast
            have e_sub_comp: "e \<subseteq> connected_component (G \<setminus> X) c"
              using edge_subset_component[of "(G \<setminus> X)" e c] invar_diff e_in_diff c_in_e
              by blast
            then show ?thesis
              using conn_C' by simp
          qed
          then have "e \<inter> Y = {}" 
            using \<open>C' \<inter> C = {}\<close> assms(4) by blast
          then have "e \<inter> (X \<union> Y) = {}" 
            by (simp add: Int_Un_distrib e_unfold)
          then have "e \<in> G \<setminus> (X \<union> Y)" 
            by (simp add: e_unfold graph_diff_def)
          then have "c\<in>Vs (G \<setminus> (X \<union> Y))" 
            using e by blast
          then have "C' \<in> odd_components (G \<setminus> (X \<union> Y))"
            unfolding odd_components_def
            by (simp add: \<open>odd (card C')\<close> conn_diff_C' odd_componentI)
          then show ?thesis 
            by (simp add: odd_comps_in_diff_def)
        qed 
      next
        case False
        then have C'diffY:"C' \<in> odd_comps_in_diff (component_edges (G \<setminus> X) C) Y"
          using asmC'odd by blast
        let ?C = "(component_edges (G \<setminus> X) C)"
        have "graph_invar ?C"
          by (meson Connected_Components.component_edges_subset assms(1) graph_invar_remove_vertices graph_invar_subset)
        have "C' \<subseteq> Vs ?C" 
          by (meson C'diffY component_in_E)
        have "Vs ?C \<subseteq> C"
          unfolding component_edges_def 
          by (auto simp: subset_iff vs_member)
        then have "C' \<subseteq> C" 
          using \<open>C' \<subseteq> Vs ?C\<close> by auto
        have "C' \<inter> Y = {}" 
          using C'diffY odd_comps_in_diff_not_in_X by blast
        then have "C' \<noteq> {}" 
          using odd_components_nonempty \<open>C' \<in> odd_comps_in_diff ?C Y\<close> `graph_invar ?C` by fastforce
        then obtain c where "c \<in> C'"
          by blast
        then have conn_diffY:"connected_component (?C \<setminus> Y) c = C'"
          by (simp add: C'diffY odd_comps_in_diff_is_component)
        have "connected_component (G \<setminus> (X \<union> Y)) c = 
              connected_component (?C \<setminus> Y) c"
        proof(safe)
          {
            fix x
            assume asmx:"x \<in> connected_component (G \<setminus> (X \<union> Y)) c"
            show "x \<in>  connected_component (?C \<setminus> Y) c"
            proof(cases "x = c")
              case True
              then show ?thesis 
                by (simp add: in_own_connected_component)
            next
              case False
              then have "\<exists>p. walk_betw (G \<setminus> (X \<union> Y)) x p c"
              proof -
                have "c \<in> connected_component (G \<setminus> (X \<union> Y)) x"
                  using asmx by (rule connected_components_member_sym)
                with \<open>x \<noteq> c\<close> show ?thesis
                  by (fastforce elim: in_con_comp_has_walk)
              qed
              then obtain p where p_walk:"walk_betw (G \<setminus> (X \<union> Y)) x p c"
                by auto
              then have "last p = c" 
                by (simp add: walk_between_nonempty_pathD(4))
              then have "path (G \<setminus> (X \<union> Y)) p" 
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
                have "{v, v'} \<in> G \<setminus> (X \<union> Y)" 
                  by (simp add: path2.hyps(1))
                then have "{v, v'} \<inter> (X \<union>Y) = {}" 
                  by (meson graph_diffE)
                then have "{v, v'} \<inter> Y = {}"
                  by blast
                then have "{v, v'} \<inter> X = {}"
                  using `{v, v'} \<inter> (X \<union>Y) = {}` by blast
                then have "{v, v'} \<in> G \<setminus> X" 
                  unfolding graph_diff_def 
                  using graph_diff_subset path2.hyps(1) by auto
                have "v' \<in> C'"
                  by (simp add: \<open>\<forall>z\<in>set (v' # vs). z \<in> C'\<close>)
                then have "v' \<in> C"
                  using \<open>C' \<subseteq> C\<close> by blast
                then have "C = connected_component (G \<setminus> X) c" 
                proof -
                  have c_in_C: "c \<in> C"
                    using \<open>c \<in> C'\<close> \<open>C' \<subseteq> C\<close> by blast
                  show ?thesis
                    using odd_comps_in_diff_is_component[OF assms(3) c_in_C] by simp
                qed
                then have "v' \<in> connected_component (G \<setminus> X) c"
                  using \<open>v' \<in> C\<close> by blast
                then have "v \<in> C"
                proof -
                  have v'_in_comp_v: "v' \<in> connected_component (G \<setminus> X) v"
                    by (rule vertices_edges_in_same_component[OF \<open>{v, v'} \<in> (G \<setminus> X)\<close>])
                  have v_in_comp_v': "v \<in> connected_component (G \<setminus> X) v'"
                    by (rule connected_components_member_sym[OF v'_in_comp_v])
                  have comp_eq: "connected_component (G \<setminus> X) v' =
                                 connected_component (G \<setminus> X) c"
                    by (rule connected_components_member_eq[OF
                          \<open>v' \<in> connected_component (G \<setminus> X) c\<close>])
                  show ?thesis
                    using v_in_comp_v' comp_eq \<open>C = connected_component (G \<setminus> X) c\<close>
                    by simp
                qed
                then have "{v, v'} \<subseteq> C" 
                  by (simp add: \<open>v' \<in> C\<close>)
                then have "{v, v'} \<in> ?C" 
                  using component_edges_def \<open>{v, v'} \<in> G \<setminus> X\<close> by fastforce
                then have vv':"{v, v'} \<in> ?C \<setminus> Y" 
                  unfolding graph_diff_def using `{v, v'} \<inter> Y = {}` by blast
                then have "v' \<in> connected_component (?C \<setminus> Y) c" 
                  using \<open>v' \<in> C'\<close> conn_diffY by blast
                then have "v \<in> connected_component (?C \<setminus> Y) c" 
                proof -
                  have vv'_comm: "{v', v} \<in> (?C \<setminus> Y)"
                    using vv' by (simp add: insert_commute)
                  have v_in_comp_v': "v \<in> connected_component (?C \<setminus> Y) v'"
                    by (rule vertices_edges_in_same_component[OF vv'_comm])
                  have comp_eq: "connected_component (?C \<setminus> Y) v' =
                                 connected_component (?C \<setminus> Y) c"
                    by (rule connected_components_member_eq[OF
                          \<open>v' \<in> connected_component (?C \<setminus> Y) c\<close>])
                  show ?thesis
                    using v_in_comp_v' comp_eq by simp
                qed
                then have "v \<in> C'" 
                  using conn_diffY by auto
                then show ?case 
                  using \<open>\<forall>z\<in>set (v' # vs). z \<in> C'\<close> by fastforce
              qed
              then show "x \<in> connected_component ((component_edges (G \<setminus> X) C) \<setminus> Y) c"
              proof -
                have all_z: "\<forall>z \<in> set p. z \<in> C'" by fact
                have p_nonempty: "p \<noteq> []"
                  using p_walk unfolding walk_betw_def by simp
                have hd_x: "hd p = x"
                  using p_walk unfolding walk_betw_def by simp
                have x_in_p: "x \<in> set p"
                  using hd_in_set[OF p_nonempty] hd_x by simp
                have x_in_C': "x \<in> C'"
                  using all_z x_in_p by blast
                show ?thesis
                  using x_in_C' conn_diffY by simp
              qed
            qed
          }
          fix x
          assume asm:"x \<in> connected_component ((component_edges (G \<setminus> X) C) \<setminus> Y) c" 
          show " x \<in> connected_component (G \<setminus> (X \<union> Y)) c"
          proof(cases "x = c")
            case True
            then show ?thesis 
              by (simp add: in_own_connected_component)

          next
            case False
            then have "\<exists>p. walk_betw  ((component_edges (G \<setminus> X) C) \<setminus> Y) x p c"
              proof -
                have sym: "c \<in> connected_component
                     ((component_edges (G \<setminus> X) C) \<setminus> Y) x"
                  using asm by (rule connected_components_member_sym)
                with \<open>x \<noteq> c\<close> show ?thesis
                  by (fastforce elim: in_con_comp_has_walk)
              qed
            then obtain p where p_walk:
                "walk_betw  ((component_edges (G \<setminus> X) C) \<setminus> Y) x p c" 
              by auto
            then have "last p = c"
              by (simp add: walk_between_nonempty_pathD(4))
            then have "path ((component_edges (G \<setminus> X) C) \<setminus> Y) p" 
              using p_walk unfolding walk_betw_def by auto
            then have "\<forall>z \<in> set p. z \<in> connected_component (G \<setminus> (X \<union> Y)) c"
              using `last p = c`
            proof(induct p) 
              case path0
              then show ?case 
                by auto
            next case (path1 v)
              then have v_eq_c: "v = c" by simp
              then show ?case by (simp add: in_own_connected_component)
            next
              case (path2 v v' vs)
              have "last (v' # vs) = c" 
                using path2.prems 
                by auto
              have zhyp:"\<forall>z\<in>set (v' # vs). z \<in> connected_component (G \<setminus> (X \<union> Y)) c" 
                using \<open>last (v' # vs) = c\<close> path2.hyps(3) by blast
              have "{v, v'} \<in> ((component_edges (G \<setminus> X) C) \<setminus> Y)" 
                by (simp add: path2.hyps(1))
              then have "{v, v'} \<inter> Y = {}" unfolding graph_diff_def 
                by fastforce
              have "{v, v'} \<in> (component_edges (G \<setminus> X) C)" 
                using graph_diff_subset path2.hyps(1) by blast
              then have "{v, v'} \<in> (G \<setminus> X)" 
                using Connected_Components.component_edges_subset by fastforce
              then have "{v, v'} \<inter> X = {}"
                unfolding graph_diff_def by fastforce
              then have "{v, v'} \<in> (G \<setminus> (X \<union> Y))" 
                unfolding graph_diff_def 
                using `{v, v'} \<inter> Y = {}` \<open>{v, v'} \<in> G \<setminus> X\<close> graph_diff_def by fastforce
              then have "v' \<in> connected_component (G \<setminus> (X \<union> Y)) c" 
                by (simp add: zhyp)
              then have "v \<in> connected_component (G \<setminus> (X \<union> Y)) c"
                by (meson \<open>{v, v'} \<in> G \<setminus> (X \<union> Y)\<close> connected_components_member_sym 
                    connected_components_member_trans vertices_edges_in_same_component)
              then show ?case 
                using zhyp by fastforce
            qed 
            then show ?thesis 
              by (metis list.set_sel(1) p_walk walk_betw_def)
          qed
        qed
        then have connC'XY:"connected_component (G \<setminus> (X \<union> Y)) c = C'"
          using conn_diffY by fastforce
        show " C' \<in> odd_comps_in_diff  G (X \<union> Y)"
        proof(cases "C' \<in> singl_in_diff ?C Y")
          case True
          then have "\<exists>v. C' = {v} \<and> v \<in> Vs ?C \<and> v \<notin> Y \<and> v \<notin> Vs (?C \<setminus> Y)"
            unfolding singl_in_diff_def by blast
          then have "C' = {c}" 
            using \<open>c \<in> C'\<close> by force
          then have "connected_component (G \<setminus> (X\<union>Y)) c = {c}" 
            using connC'XY by fastforce
          have "c \<notin> Vs (G \<setminus> (X \<union> Y))" 
          proof(rule ccontr)
            assume " \<not> c \<notin> Vs (G \<setminus> (X \<union> Y))"
            then obtain e where e:"c \<in> e \<and> e \<in> (G \<setminus> (X \<union> Y))"
              by (meson vs_member_elim)
            then have "e \<subseteq> connected_component (G \<setminus> (X\<union>Y)) c"
              by (simp add: assms(1) edge_subset_component graph_invar_remove_vertices)
            then show False 
              using \<open>connected_component (G \<setminus> (X \<union> Y)) c = {c}\<close> 
                assms(1) e graph_invar_remove_vertices by fastforce
          qed
          have "c \<notin> X \<union> Y"
          proof (rule notI)
            assume "c \<in> X \<union> Y"
            then consider (inX) "c \<in> X" | (inY) "c \<in> Y"
              by blast
            then show False
            proof cases
              case inX
              have c_in_C: "c \<in> C"
                using \<open>c \<in> C'\<close> \<open>C' \<subseteq> C\<close> by blast
              have "C \<inter> X = {}"
                using odd_comps_in_diff_not_in_X[OF assms(3)] .
              then show False
                using c_in_C inX by blast
            next
              case inY
              show False
                using \<open>c \<in> C'\<close> \<open>C' \<inter> Y = {}\<close> inY by blast
            qed
          qed
        then have "{c} \<in> singl_in_diff G (X \<union> Y)" 
          by (meson \<open>C' \<subseteq> C\<close> \<open>c \<in> C'\<close> \<open>c \<notin> Vs (G \<setminus> (X \<union> Y))\<close> assms(3) 
              component_in_E singl_in_diffI subsetD)
          then have "C' \<in> singl_in_diff G (X \<union> Y)" 
            by (simp add: \<open>C' = {c}\<close>)
          then show ?thesis 
            by (simp add: odd_comps_in_diff_def)
        next
          case False
          then have C'_odd_diff:"C' \<in> odd_components (?C \<setminus> Y)" 
            using C'diffY by (simp add: odd_comps_in_diff_def)
          then have "odd (card C')" 
            by (simp add: odd_components_def odd_component_def)
          have "c \<notin> X \<union> Y"
          proof -
            have c_notin_Y: "c \<notin> Y"
              using \<open>C' \<inter> Y = {}\<close> \<open>c \<in> C'\<close> by blast
            have c_notin_X: "c \<notin> X"
            proof -
              have "C \<inter> X = {}"
                using odd_comps_in_diff_not_in_X assms(3) by blast
              then show ?thesis
                using \<open>c \<in> C'\<close> \<open>C' \<subseteq> C\<close> by blast
            qed
            show ?thesis
              using c_notin_X c_notin_Y by blast
          qed
          have "c \<in> Vs (?C \<setminus> Y)" 
            using False \<open>C' \<subseteq> Vs ?C\<close> \<open>c \<notin> X \<union> Y\<close> conn_diffY 
              connected_components_notE_singletons singl_in_diffI by fastforce
            then obtain e where e:"c \<in> e \<and> e \<in> ?C \<setminus> Y" 
              by (meson vs_member_elim)
          then have "c \<in> e \<and> e \<in> ?C \<and> e \<inter> Y = {}" 
            by (simp add: graph_diff_def)
        then have "e \<subseteq> C'"
        proof -
          have invar_diff_CY: "graph_invar ((component_edges (G \<setminus> X) C) \<setminus> Y)"
            by (rule graph_invar_remove_vertices[OF \<open>graph_invar (component_edges (G \<setminus> X) C)\<close>])
          have e_in_CY: "e \<in> ((component_edges (G \<setminus> X) C) \<setminus> Y)"
            using e by blast
          have c_in_e: "c \<in> e"
            using e by blast
          have "e \<subseteq> connected_component ((component_edges (G \<setminus> X) C) \<setminus> Y) c"
            using edge_subset_component[OF invar_diff_CY e_in_CY c_in_e] by blast
          then show ?thesis
            using conn_diffY by simp
        qed
          then have "e \<inter> (X \<union> Y) = {}" 
          proof -
            have e_in_CE: "e \<in> component_edges (G \<setminus> X) C"
              using \<open>c \<in> e \<and> e \<in> ?C \<and> e \<inter> Y = {}\<close> by blast
            have e_in_diffX: "e \<in> (G \<setminus> X)"
              using Connected_Components.component_edges_subset e_in_CE by blast
            have e_inter_X: "e \<inter> X = {}"
              using e_in_diffX unfolding graph_diff_def by fastforce
            have e_inter_Y: "e \<inter> Y = {}"
              using \<open>c \<in> e \<and> e \<in> ?C \<and> e \<inter> Y = {}\<close> by blast
            show ?thesis
              using e_inter_X e_inter_Y by blast
          qed
          have "e \<in> G" 
            using `c \<in> e \<and> e \<in> ?C \<and> e \<inter> Y = {}` Connected_Components.component_edges_subset 
                  graph_diff_member 
            by blast
          then have "e \<in> (G \<setminus> (X \<union> Y))" 
            by (simp add: \<open>e \<inter> (X \<union> Y) = {}\<close> graph_diff_def)
          then have "c\<in>Vs (G \<setminus> (X \<union> Y))" 
            using e by blast
          then have "C' \<in> odd_components (G \<setminus> (X \<union> Y))" 
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
  have "G \<setminus> (Y \<inter> Vs G) = G \<setminus> Y" 
    unfolding graph_diff_def by blast
  then have "singl_in_diff G (Y \<inter> Vs G) = singl_in_diff G Y" 
    unfolding singl_in_diff_def
    by (safe;simp)
  then show ?thesis 
    by (simp add: \<open>G \<setminus> (Y \<inter> Vs G) = G \<setminus> Y\<close> odd_comps_in_diff_def)
qed

end
