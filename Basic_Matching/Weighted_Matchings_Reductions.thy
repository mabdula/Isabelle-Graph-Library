theory Weighted_Matchings_Reductions
  imports Matching
begin

section \<open>Variants of Weighted Matching\<close>

subsection \<open>Definitions\<close>

subsection \<open>Reductions\<close>
  (* For both the bipartite case and the general one,
     we perform the following reductions to the minimum weight perfect version.
     The outer arrow are trivial and of course bidirectional (see the following).
     The inner arrows are harder.
   max weight    max weight max card
     |                |
     v                v
   min weight   min weight max card
     |                |
     v                v
     min weight perfect <-- max weight perfect
*)
subsubsection \<open>Relationships between Weight Minimisation, Weight Maximisation 
               and Cardinality Maximisation\<close>

lemma min_and_max_matching:
  "min_weight_matching G w M \<longleftrightarrow> max_weight_matching G (- w) M"
  by(auto intro!: min_weight_matchingI max_weight_matchingI
      elim!:  min_weight_matchingE max_weight_matchingE
      simp add: sum_negf)

lemma min_perfect_and_max_perfect_matching:
  "min_weight_perfect_matching G w M \<longleftrightarrow> max_weight_perfect_matching G (- w) M"
  by(auto intro!: min_weight_perfect_matchingI max_weight_perfect_matchingI
      elim!:  min_weight_perfect_matchingE max_weight_perfect_matchingE
      simp add: sum_negf)

lemma min_max_card_and_max_max_card_matching:
  "min_weight_max_card_matching G w M \<longleftrightarrow> max_weight_max_card_matching G (- w) M"
  by(auto intro!: min_weight_max_card_matchingI max_weight_max_card_matchingI
      elim!:  min_weight_max_card_matchingE max_weight_max_card_matchingE
      simp add: sum_negf)

lemma max_unit_weight_max_card_matching:
  "max_weight_matching G (\<lambda> e. 1) M \<longleftrightarrow> max_card_matching G M"
  by(auto elim!: max_weight_matchingE max_card_matchingE
         intro!: max_weight_matchingI max_card_matchingI)

subsubsection \<open>Maximum Weight (Maximum Cardinality) to Minimum Weight Perfect (Bipartite)\<close>

datatype 'v bp_vertex_wrapper = 
  is_old_bp_vertex: old_vertex (the_vertex: 'v) | is_new_bp_vertex: new_vertex nat

definition "bp_perfected_G L R= 
  {{old_vertex u, old_vertex v} | u v. u \<in> L \<and> v \<in> R} \<union>
   {{new_vertex i, old_vertex v} | i v. i < card R - card L \<and> v \<in> R} \<union>
   {{old_vertex u, new_vertex i} | i u. i < card L - card R \<and> u \<in> L}"

definition "bp_perfected_L L R= 
  old_vertex ` L \<union> {new_vertex i | i . i < card R - card L }"

definition "bp_perfected_R L R= 
  old_vertex ` R \<union> {new_vertex i | i . i < card L - card R}"

lemma bp_perfected_G_def':
 "bp_perfected_G L R = {{u, v} | u v. u \<in> bp_perfected_L L R \<and> v \<in> bp_perfected_R L R}"
  by(auto simp add: Vs_def bp_perfected_G_def bp_perfected_L_def bp_perfected_R_def)

lemma no_new_vertex_old_vertex_new_vertex_inverse:
  assumes "(\<And> i. new_vertex i \<noteq> x)" 
  shows"old_vertex ( the_vertex  x) = x"
  using assms
  by(cases x) auto

lemma no_new_vertex_old_vertex_new_vertex_image_inverse:
  assumes "(\<And> i. new_vertex i \<notin> e)" 
  shows"old_vertex ` the_vertex ` e = e"
proof(rule, all \<open>rule\<close>, goal_cases)
  case (1 x)
  then obtain x' where x': "x' \<in> the_vertex ` e" "x = old_vertex x'" by blast
  moreover then obtain x'' where x'': "x'' \<in> e" "x' = the_vertex x''" by auto
  ultimately have "x = x''"
    using assms by(cases x'') auto
  then show ?case 
    using x'' by blast
next
  case (2 x)
  then obtain x' where "x = old_vertex x'" "the_vertex x = x'"
    using assms 
    by(cases x) auto
  then show ?case 
    using 2
    by (auto intro!: image_eqI)
qed

lemma old_vertex_of_the_vertex_contained:
  "\<lbrakk>\<And>i. new_vertex i \<notin> x; xc \<in> x\<rbrakk> \<Longrightarrow> old_vertex (the_vertex xc) \<in> x"
  using no_new_vertex_old_vertex_new_vertex_image_inverse by blast

lemma no_new_vertex_new_vertex_old_vertex_image_inverse:
  "the_vertex ` old_vertex ` e = e"
  by (auto intro!: image_eqI)

lemma bp_perfected_Vs_are:
  "\<lbrakk>L\<noteq>{}; R \<noteq> {}\<rbrakk> \<Longrightarrow> Vs (bp_perfected_G L R) = bp_perfected_L L R \<union> bp_perfected_R L R"
  unfolding bp_perfected_G_def'
  by(subst Vs_of_edges_connecting_two_sets)
    (auto simp add: bp_perfected_L_def bp_perfected_R_def)

lemma bp_perfected_Vs_subs:
  "Vs (bp_perfected_G L R) \<subseteq> bp_perfected_L L R \<union> bp_perfected_R L R"
  using Vs_of_edges_connecting_two_sets_subs
  unfolding bp_perfected_G_def' 
  by fast

lemma bipartite_Vs_of_complete_union_L_R:
 "\<lbrakk>bipartite G L R; L \<union> R  \<subseteq> Vs G\<rbrakk>
   \<Longrightarrow> Vs (bp_perfected_G L R) = bp_perfected_L L R \<union> bp_perfected_R L R"
proof(cases "L = {}", goal_cases)
  case 1
  thus ?case
    by(auto simp add: bp_perfected_G_def' bp_perfected_L_def bp_perfected_R_def
                      bipartite_empty_part_iff_empty)
next
  case 2
  thus ?case
  proof(cases "R = {}", goal_cases)
    case 1
    thus ?case
    by(auto simp add: bp_perfected_G_def' bp_perfected_L_def bp_perfected_R_def
                      bipartite_empty_part_iff_empty 
                dest: bipartite_commute)
  qed(rule bp_perfected_Vs_are)
qed

lemma perfected_vertices_empty_same:
  "\<lbrakk>finite L; finite R\<rbrakk> \<Longrightarrow> (bp_perfected_L L R) = {} \<longleftrightarrow>  (bp_perfected_R L R) = {}"
  using card_gt_0_iff by(force simp add: bp_perfected_L_def bp_perfected_R_def)

lemma balanced_complete_bipartite_perfected:
  assumes "bipartite G L R" "finite L" "finite R"
    shows "balanced_complete_bipartite (bp_perfected_G L R)
              (bp_perfected_L L R)  (bp_perfected_R L R)" (is ?th1)
      and balanced_complete_bipartite_perfected_side_cards:
          "card (bp_perfected_L L R) = max (card L) (card R)"
          "card (bp_perfected_R L R) = max (card L) (card R)"
proof-
  have card_hleper:  
    "card (old_vertex ` L \<union> {new_vertex i |i. i < card R - card L}) =
    card (old_vertex ` R \<union> {new_vertex i |i. i < card L - card R})"
    using assms(2,3)
    apply(subst card_Un_disjoint, simp, simp, force)
    apply(subst card_Un_disjoint)
    by(auto simp add: set_of_f_up_to_n_image card_image inj_on_def)
  show ?th1
    using assms
    by(auto intro!: balanced_complete_bipartiteI complete_bipartiteI 
        simp add: bp_perfected_G_def bp_perfected_R_def 
        bp_perfected_L_def bipartite_def card_hleper)+
  have "card L < card R 
    \<Longrightarrow> card (old_vertex ` L \<union> {new_vertex i |i. i < card R - card L}) = card R"
    using assms(2,3)
    by(subst card_Un_disjoint)
      (auto simp add: set_of_f_up_to_n_image card_image inj_on_def)
  thus  "card (bp_perfected_L L R) = max (card L) (card R)"
    by(cases "card L < card R")
      (auto simp add: bp_perfected_L_def bp_perfected_R_def inj_on_def intro!: card_image)
  have "\<not> card L < card R \<Longrightarrow> card (old_vertex ` R \<union> {new_vertex i |i. i < card L - card R}) = card L"
    using assms(2,3)
    by(subst card_Un_disjoint)
      (auto simp add: set_of_f_up_to_n_image card_image inj_on_def)
  thus   "card (bp_perfected_R L R) = max (card L) (card R)"
    by(cases "card L < card R")
      (auto simp add: bp_perfected_L_def bp_perfected_R_def inj_on_def intro!: card_image)
qed

lemma matching_on_old_vertices:
  "matching M \<longleftrightarrow> matching ((image old_vertex )` M)"
  by(auto intro!: matchingI elim!: matchingE) blast+

lemma old_vertex_rev_mono: 
  "(image old_vertex)` G \<subseteq> (image old_vertex)` G' \<Longrightarrow> G \<subseteq> G'"
  by(rule inj_image_rev_mono)
    (auto intro!: inj_on_image simp add: inj_def)

lemma graph_matching_on_old_vertices:
  "graph_matching G M \<longleftrightarrow> graph_matching ((image old_vertex )` G) ((image old_vertex )` M)"
  using matching_on_old_vertices 
  by (auto dest!: old_vertex_rev_mono)

definition "project_to_old G = {the_vertex ` e | e. e\<in> G \<and> (\<nexists> i. new_vertex i \<in> e)}"

lemma project_to_old_mono:
  "G \<subseteq> G' \<Longrightarrow> project_to_old G \<subseteq> project_to_old G'"
  by(auto simp add: project_to_old_def)

lemma matching_on_project_to_old:
  "matching M \<Longrightarrow> matching (project_to_old M)"
proof(rule matchingI, goal_cases)
  case (1 e1 e2)
  then obtain e1' e2' where e1e2:"e1 = the_vertex ` e1'" "e2 = the_vertex ` e2'"
    "e1' \<in> M" "e2' \<in> M" "(\<nexists> i. new_vertex i \<in> e1')" "(\<nexists> i. new_vertex i \<in> e2')"
    by(auto simp add: project_to_old_def)
  hence "e1' \<inter> e2' = {}" 
    using  "1"(1,4) 
    by(elim matchingE)blast
  moreover have "e1' = old_vertex ` e1" 
    using e1e2(1,5) no_new_vertex_old_vertex_new_vertex_image_inverse 
    by blast
  moreover have "e2' = old_vertex ` e2" 
    using e1e2(2,6) no_new_vertex_old_vertex_new_vertex_image_inverse 
    by blast
  ultimately show ?case
    by auto
qed

lemma graph_matching_on_project_to_old:
  "graph_matching G M \<Longrightarrow> graph_matching (project_to_old G) (project_to_old M)"
  using matching_on_project_to_old project_to_old_mono by auto

lemma the_vertex_inj:
  "\<lbrakk>\<nexists> i. x = new_vertex i; \<nexists> i. y = new_vertex i; the_vertex x = the_vertex y\<rbrakk> \<Longrightarrow> x = y"
  by(cases x, all \<open>cases y\<close>) auto

lemma the_vertex_image_inj:
  "\<lbrakk>\<nexists> i. new_vertex i \<in> x; \<nexists> i. new_vertex i \<in> y; the_vertex ` x = the_vertex ` y\<rbrakk> \<Longrightarrow> x = y"
  by (metis no_new_vertex_old_vertex_new_vertex_image_inverse)

definition "penalty G w = (card (Vs G) / 2) * Max (insert 0 { \<bar>w e \<bar> | e. e \<in> G}) + 1"

lemma penalty_cost_neagation:"penalty G (-w) = penalty G w"
  by(auto simp add: penalty_def)

lemma penalty_gtr_0: 
  assumes"finite G" 
  shows  "penalty G w > 0"
proof-
  have "0 \<le> Max ({0} \<union> { \<bar>w e\<bar> |e. e \<in> G})"
    using assms by(auto simp add: Max_ge_iff)
  hence "0 \<le> real (card (Vs G)) * Max ({0} \<union> { \<bar>w e\<bar> |e. e \<in> G}) / 2" 
    by auto
  then show ?thesis
    by(auto simp add: penalty_def)
qed

lemma edge_weight_less_thatn_penalty:
  assumes "graph_invar G" "e \<in> G"
    shows "w e < penalty G w" 
proof-
  have "w e \<le> Max (insert 0 { \<bar>w e \<bar> | e. e \<in> G})"
    using graph_invar_finite[OF assms(1)] assms(2)
    by(auto simp add: Max_ge_iff)
  moreover have "... \<le> (card (Vs G) / 2) * Max (insert 0 { \<bar>w e\<bar> | e. e \<in> G})"
    using assms graph_invar_finite[OF assms(1)]
    by(intro ordered_semiring_class.mult_right_mono[of 1 "(card (Vs G) / 2)", simplified mult_1])
      (auto simp add: less_eq_Suc_le[symmetric] card_gt_0_iff intro!: card_of_non_empty_graph_geq_2)
  moreover have "... < penalty G w"
    by(auto simp add: penalty_def)
  ultimately show  "w e < penalty G w" 
    by simp+
qed

lemma weight_of_matching_less_penalty:
  assumes "graph_invar G" "graph_matching G M"
  shows "sum w M < penalty G w"
proof-
  have zero_leq_Max: "0 \<le> Max ({0} \<union> { \<bar>w e\<bar> |e. e \<in> G})" and
    we_leq_Max: "e \<in> G \<Longrightarrow> w e \<le> Max ({0} \<union> { \<bar>w e\<bar> |e. e \<in> G})" for e
    using assms graph_invar_finite[OF assms(1)]
    by(auto simp add: Max_ge_iff)
  have "sum w M \<le> real (card M) * Max (insert 0 { \<bar>w e\<bar> | e. e \<in> G})"
    apply(subst semiring_1_class.sum_constant[of  "_::real", symmetric])
    apply(rule ordered_comm_monoid_add_class.sum_mono)
    using assms(2) we_leq_Max 
    by auto
  moreover have "... \<le> card (Vs G) / 2 * Max (insert 0 { \<bar>w e \<bar> | e. e \<in> G})"
    apply(rule ordered_semiring_class.mult_right_mono)
     apply(subst graph_abs.matching_card_vs')
    using assms(1,2) graph_abs.intro graph_abs_mono zero_leq_Max
    by (auto intro!: card_mono dest: subsetD[OF Vs_subset])
  moreover have "... < penalty G w"
    by(auto simp add: penalty_def)
  ultimately show ?thesis
    by simp
qed

lemma weight_of_matching_gtr_negated_penalty:
  assumes "graph_invar G" "graph_matching G M"
  shows "sum w M > -penalty G w"
proof-
  have "- sum w M < penalty G w"
    using weight_of_matching_less_penalty[OF assms, of "- w"]
    by(simp add: sum_negf[of w M, symmetric] penalty_cost_neagation[of G w, symmetric])
  thus ?thesis
    by simp
qed

lemma weight_of_matching_abs_less:
  assumes "graph_invar G" "graph_matching G M"
  shows "\<bar>sum w M\<bar> < penalty G w"
  using weight_of_matching_gtr_negated_penalty[OF assms, of w]
    weight_of_matching_less_penalty[OF assms, of w] 
  by(auto simp add: linordered_idom_class.abs_less_iff)

lemma weight_diff_of_matchings_less_than_2_penalties:
  assumes "graph_invar G" "graph_matching G M" "graph_matching G M'"
  shows "\<bar> sum w M - sum w M' \<bar> < 2*penalty G w"
  using weight_of_matching_abs_less[OF assms(1,2), of w]
    weight_of_matching_abs_less[OF assms(1,3), of w]
  by auto

definition "bp_min_costs_to_min_perfect_costs G (w::'a set \<Rightarrow> real) =
            (\<lambda> e. if \<exists> i. new_vertex i \<in> e then 0
                  else if (the_vertex ` e) \<notin> G then 0
                  else min 0 (w (the_vertex ` e)))"

definition "bp_min_max_card_costs_to_min_perfect_costs G (w::'a set \<Rightarrow> real) =
            (\<lambda> e. if \<exists> i. new_vertex i \<in> e then 2*penalty G w
                  else if (the_vertex ` e) \<notin> G then 2*penalty G w
                  else w (the_vertex ` e))"

lemma finite_G_finite_completion:
  "\<lbrakk>finite G; finite L; finite R\<rbrakk> \<Longrightarrow> finite (bp_perfected_G L R)"
proof(unfold bp_perfected_G_def, rule finite_UnI, rule finite_UnI, goal_cases)
  case 1
  thus ?case
    by (auto simp add: image_iff 
        intro!: finite_surj[of "L \<times> R" _  "\<lambda> x. {old_vertex (fst x), old_vertex (snd x)}"] 
        bexI)
next
  case 2
  thus ?case
    by (auto simp add: image_iff 
        intro!: finite_surj[of "R \<times> {0..< card R - card L}" _  
          "\<lambda> x. {old_vertex (fst x), new_vertex (snd x)}"] bexI)
next
  case 3
  thus ?case
    by (auto  intro!:  finite_surj[of "L \<times> {0..< card L - card R}" _  
          "\<lambda> x. {old_vertex (fst x), new_vertex (snd x)}"] bexI
        simp add: image_iff)
qed

lemma finite_L_finite_completion:
  "\<lbrakk>finite L\<rbrakk> \<Longrightarrow> finite (bp_perfected_L L R)"
  by(auto simp add: bp_perfected_L_def)

lemma finite_R_finite_completion:
  "\<lbrakk>finite R\<rbrakk> \<Longrightarrow> finite (bp_perfected_R L R)"
  by(auto simp add: bp_perfected_R_def)

lemma bp_perfected_L_R_disjnt:
  "R \<inter>  L = {} \<Longrightarrow> (bp_perfected_L L R) \<inter> (bp_perfected_R L R) = {}"
  by(auto simp add: bp_perfected_L_def bp_perfected_R_def)

context
  fixes G::"'a set set" and L R and w::"'a set \<Rightarrow> real"
  assumes bipartite_G: "bipartite G L R" 
    and finite_L: "finite L"
    and finite_R: "finite R"
begin

lemma finite_G: "finite G" 
  using bipartite_G finite_L finite_R finite_Vs_then_finite finite_parts_bipartite_graph_invar
  by auto

lemma graph_invarG: "graph_invar G"
  using bipartite_G finite_G finite_bipartite_graph_invar by auto

abbreviation "G' \<equiv> bp_perfected_G L R"
abbreviation "L' \<equiv> bp_perfected_L L R"
abbreviation "R' \<equiv> bp_perfected_R L R"
abbreviation "w' \<equiv> bp_min_costs_to_min_perfect_costs G w"

lemma old_vertex_of_G_in_G': "(image old_vertex) ` G \<subseteq> G'"
  using bipartite_G
  by(auto simp add: bp_perfected_G_def elim!: bipartite_edgeE)

lemma project_to_old_of_negs_two_ways:
  "project_to_old (E \<inter> {e | e. w' e < 0}) \<inter> G =  project_to_old E \<inter> {e | e. w e < 0} \<inter> G"
  by(auto simp add:  project_to_old_def bp_min_costs_to_min_perfect_costs_def)

lemma finite_G':"finite G'"
  by(auto intro!: finite_G_finite_completion
      simp add: finite_L finite_R finite_G)

lemma e_in_project_to_old_L_times_R:
  "e \<in> project_to_old G' \<Longrightarrow> e \<in> {{u, v} | u v. u \<in> L \<and> v \<in> R}"
  by(auto simp add: bp_perfected_G_def project_to_old_def)

lemma G'_bipartite: "bipartite G' L' R'"
  using balanced_complete_bipartiteD(1) balanced_complete_bipartite_perfected(1) bipartite_G
    complete_bipartiteD(1) finite_L finite_R by blast

lemma graph_abs_G': "graph_abs G'"
  by(auto intro!: bipartite_to_graph_abs G'_bipartite finite_G')

lemma complete_bipartite_G': "complete_bipartite G' L' R'"
  using balanced_complete_bipartiteD(1) balanced_complete_bipartite_perfected(1) bipartite_G finite_L
    finite_R by blast

lemma L'_R'_same_empty:"L' = {} \<longleftrightarrow> R' = {}"
  by (simp add: finite_L finite_R perfected_vertices_empty_same)

lemma finite_L': "finite L'"
  by (simp add: finite_L finite_L_finite_completion)

lemma finite_R': "finite R'"
  by (simp add: finite_R finite_R_finite_completion)

lemma L'_R'_disjoint: "L' \<inter> R' = {}"
  using G'_bipartite bipartite_disjointD by blast

lemma card_Vs_G': "card (Vs G') = 2* max (card L) (card R)"
  by (simp add: complete_bipartite_Vs[OF complete_bipartite_G' _ L'_R'_same_empty]
      graph_abs.dblton_E graph_abs_G' card_Un_disjoint finite_L' finite_R' 
      L'_R'_disjoint
      balanced_complete_bipartite_perfected_side_cards[OF bipartite_G finite_L finite_R])

lemma perfect_in_G'_max_L_R_edges:
  "perfect_matching G' M \<Longrightarrow> card M = max (card L) (card R)"
  by(auto simp add: perfect_matching_card'[OF _ graph_abs_G'] card_Vs_G')

lemma sum_on_new_is_sum_on_project_old:
  assumes "finite E"
  shows "sum w' E = sum w (project_to_old E \<inter> {e | e. w e < 0} \<inter> G)"
proof-
  have "sum w' E = sum w' {e | e. e \<in> E \<and> (\<nexists> i. new_vertex i \<in> e)} 
                + sum w' {e | e i. e \<in> E \<and> new_vertex i \<in> e}"
    using assms(1) 
    by (subst comm_monoid_add_class.sum.union_disjoint[symmetric]) 
      (auto intro!: arg_cong[of  _ _ "sum w'"])
  also have "... = sum w' {e | e. e \<in> E \<and> (\<nexists> i. new_vertex i \<in> e)}"
    by (auto simp add: bp_min_costs_to_min_perfect_costs_def)
  also have "... = sum w' {e | e. e \<in> E \<and> (\<nexists> i. new_vertex i \<in> e) \<and> w' e < 0} +
                   sum w' {e | e. e \<in> E \<and> (\<nexists> i. new_vertex i \<in> e) \<and> w' e \<ge> 0}"
    using assms(1)
    by (subst comm_monoid_add_class.sum.union_disjoint[symmetric]) 
      (auto intro!: arg_cong[of  _ _ "sum w'"])
  also have "... =  sum w' {e | e. e \<in> E \<and> (\<nexists> i. new_vertex i \<in> e) \<and> w' e < 0}"
    by(auto simp add: bp_min_costs_to_min_perfect_costs_def
        intro!: comm_monoid_add_class.sum.neutral)
  also have "... = sum w (project_to_old E \<inter> {e | e. w e < 0} \<inter> G)"
  proof-
    have pto_is:"project_to_old E \<inter> {e | e. w e < 0} \<inter> G = 
          (image the_vertex) ` {e |e. e \<in> E \<and> (\<nexists>i. new_vertex i \<in> e) \<and> local.w' e < 0}"
      by (auto simp add: project_to_old_def bp_min_costs_to_min_perfect_costs_def)
    have inj: "inj_on ((`) the_vertex) {e |e. e \<in> E \<and> (\<nexists>i. new_vertex i \<in> e) \<and> local.w' e < 0}"
      by(auto simp add: inj_on_def  the_vertex_image_inj)
    show ?thesis
      apply(subst pto_is)
      apply(subst comm_monoid_add_class.sum.reindex[OF inj])
      by (auto intro: comm_monoid_add_class.sum.cong 
          simp add: bp_min_costs_to_min_perfect_costs_def)
  qed
  finally show ?thesis
    by simp
qed

lemma min_weight_implies_min_weight_perfect:
  assumes "min_weight_matching G w M"
  obtains M' where "min_weight_perfect_matching G' w' M'"
                   "sum w' M' = sum w M" "((image old_vertex) ` M) \<subseteq> M'"
proof-
  note M_props = min_weight_matchingD[OF assms(1)]
  have "graph_matching G' ((image old_vertex) ` M)"
    apply(rule matching_graph_mono)
     apply(rule iffD1[OF graph_matching_on_old_vertices])
    using assms(1) old_vertex_of_G_in_G'
    by(auto elim!: min_weight_matchingE intro!: perfect_matchingD)
  hence "\<exists>M'. perfect_matching local.G' M' \<and> ((image old_vertex) ` M) \<subseteq> M'"
    by(auto intro!: extend_to_perfect_matching_in_balanced_complete_bipartite[
          OF balanced_complete_bipartite_perfected(1)[OF bipartite_G]]
        simp add: finite_L finite_R finite_G')
  then obtain M' where M': "perfect_matching local.G' M'" "((image old_vertex) ` M) \<subseteq> M'"
    by auto
  have finite_M': "finite M'" and matching_M': "matching M'" and M'_in_G': "M' \<subseteq> G'"
    using  M'(1) finite_G' 
    by(auto simp add: perfect_matching_def intro: rev_finite_subset) 
  have finite_M: "finite M" 
    using  M_props(1) finite_G rev_finite_subset by blast
  have M'_neg_olds_in_M: "project_to_old (M' \<inter> {e. local.w' e < 0}) \<inter> G \<subseteq> M"
  proof(rule ccontr, goal_cases)
    case 1
    then obtain e where e: "e \<in> project_to_old (M' \<inter> {e. local.w' e < 0})" "e \<notin> M" by auto
    hence "e \<in> {{u, v} | u v. u \<in> L \<and> v \<in> R}"
      using perfect_matchingD[OF M'(1)]  
      apply (intro e_in_project_to_old_L_times_R)
      apply(rule subsetD[OF project_to_old_mono])
      by auto
    hence e_props:"e \<in> G" "old_vertex ` e \<in> M'" "w' (old_vertex ` e) < 0" "w e < 0"
      using e
      by(auto simp add: project_to_old_def bp_min_costs_to_min_perfect_costs_def
          if_split[of "\<lambda> x. x < 0"] no_new_vertex_old_vertex_new_vertex_image_inverse)
    moreover have "matching (insert e M)"
      apply(subst matching_on_old_vertices)
      apply(rule matching_subgraph[OF matching_M'])
      using M'(2) e_props(2) by blast
    moreover have "insert e M \<subseteq> G"
      by (simp add: M_props(1) e_props(1))
    ultimately have "graph_matching G (insert e M)" 
      by simp
    moreover have "sum w (insert e M) < sum w M"
      by(simp add: comm_monoid_add_class.sum.insert[OF finite_M e(2)] e_props(4))
    ultimately show False
      using assms 
      by(auto dest: min_weight_matchingD)
  qed
  have in_M_but_not_in_project_zero_weight:
    "\<lbrakk>e\<in>M; e\<notin>  project_to_old (M' \<inter> {e. local.w' e < 0}) \<inter> G\<rbrakk> \<Longrightarrow> w e = 0" for e
  proof(goal_cases)
    case 1
    hence "old_vertex ` e \<in> M'"
      using M'(2) by blast
    moreover have e_in_G:"e \<in> G" 
      using "1"(1) M_props(1) by blast
    ultimately have "w' (old_vertex ` e) \<ge> 0"
      using 1(2)
      by(auto simp add: project_to_old_def bp_min_costs_to_min_perfect_costs_def
          if_split[of "\<lambda> x. x < 0"]) force
    hence "w e \<ge> 0" 
      by (simp add: e_in_G image_iff bp_min_costs_to_min_perfect_costs_def
          no_new_vertex_new_vertex_old_vertex_image_inverse)
    thus ?case
      using "1"(1) assms finite_M min_weight_matching_only_negs by fastforce
  qed
  have M'_M_same_costs:"sum w' M' = sum  w M"
  proof-
    have "sum w (project_to_old (M' \<inter> {e. w' e < 0}) \<inter> G) = sum w M"
      using in_M_but_not_in_project_zero_weight finite_M M'_neg_olds_in_M
      by(auto intro!: comm_monoid_add_class.sum.mono_neutral_left)
    thus ?thesis
      using M' project_to_old_of_negs_two_ways[of M']
      by(auto simp add: sum_on_new_is_sum_on_project_old[OF finite_M'] )
  qed
  have M'_opt:"min_weight_perfect_matching G' w' M'"
  proof(rule ccontr,goal_cases)
    case 1
    then obtain M'' where M'': "perfect_matching G' M''" "sum w' M'' < sum w' M'"
      using M'(1) by(auto simp add: min_weight_perfect_matching_def)
    hence "sum w' M'' < sum w M" 
      using M'_M_same_costs by linarith
    moreover have "sum w (project_to_old M'' \<inter> {e |e. w e < 0} \<inter> G) = sum w' M''" 
      using M''(1) finite_G' 
      by(subst sum_on_new_is_sum_on_project_old)
        (auto dest: perfect_matchingD(1) intro: rev_finite_subset)
    moreover have "graph_matching G (project_to_old M'' \<inter> {e |e. w e < 0} \<inter> G)"
      using M''(1) matching_subgraph[OF matching_on_project_to_old, of M'']
      by(auto dest: perfect_matchingD(2) simp add: inf.coboundedI1)
    ultimately have "\<not> min_weight_matching G w M" 
      by(auto simp add:  min_weight_matching_def)
    thus False
      using assms(1)
      by simp
  qed
  show thesis
    using M'_M_same_costs M'_opt that M'(2) by blast
qed

lemma min_weight_perfect_implies_min_weight:
  assumes "min_weight_perfect_matching G' w' M"
  shows "min_weight_matching G w (project_to_old M \<inter> {e |e. w e < 0} \<inter> G)"
    "sum w' M = sum w (project_to_old M \<inter> {e |e. w e < 0} \<inter> G)"
proof-
  show same_sum:"sum w' M = sum w (project_to_old M \<inter> {e |e. w e < 0} \<inter> G)"
    using assms finite_G' finite_subset
    by(intro sum_on_new_is_sum_on_project_old)
      (auto dest!: min_weight_perfect_matchingD(1) perfect_matchingD(1))
  have graph_match: "graph_matching G (project_to_old M \<inter> {e |e. w e < 0} \<inter> G)"
    using assms
    by(auto intro!: matching_subgraph[OF matching_on_project_to_old, of M]
        intro: perfect_matchingD
        elim!: min_weight_perfect_matchingE)
  show "min_weight_matching G w (project_to_old M \<inter> {e |e. w e < 0} \<inter> G)"
  proof(rule ccontr, goal_cases)
    case 1
    obtain M' where M': "min_weight_matching G w M'"
      using  min_matching_exists[OF finite_G] by blast
    hence M'_props: "graph_matching G M'" 
      "sum w M' < sum w (project_to_old M \<inter> {e |e. w e < 0} \<inter> G)"
      using 1 graph_match
      by (auto simp add: min_weight_matching_def)
    obtain M'' where "min_weight_perfect_matching G' w' M''" "sum w' M'' =  sum w M'"
      using M' min_weight_implies_min_weight_perfect by blast
    hence "perfect_matching G' M''" "sum w' M'' < sum w' M" 
      using min_weight_perfect_matchingD(1)  M'_props(2)  same_sum 
      by auto
    hence "\<not> min_weight_perfect_matching G' w' M" 
      using same_sum min_weight_perfect_matchingD(1)[OF assms] 
      by(auto simp add: min_weight_perfect_matching_def)
    thus False
      using assms(1) by simp
  qed
qed

abbreviation "w'' \<equiv> bp_min_max_card_costs_to_min_perfect_costs G w"

lemma sum_on_new_is_sum_on_project_old':
  assumes "finite E"
  shows "sum w'' E = sum w (project_to_old E \<inter> G) +
                       (real (card E) - real (card (project_to_old E \<inter> G))) * 2*penalty G w"
proof-
  define pnty where "pnty = 2*penalty G w"
  have "sum w'' E = sum w'' {e | e. e \<in> E \<and> (\<nexists> i. new_vertex i \<in> e)} 
                + sum w'' {e | e i. e \<in> E \<and> new_vertex i \<in> e}"
    using assms(1) 
    by (subst comm_monoid_add_class.sum.union_disjoint[symmetric]) 
      (auto intro!: arg_cong[of  _ _ "sum w''"])
  moreover have "... = sum w'' {e | e. e \<in> E \<and> (\<nexists> i. new_vertex i \<in> e)} +
                  card {e | e i. e \<in> E \<and> new_vertex i \<in> e} * pnty"
    by (auto simp add: bp_min_max_card_costs_to_min_perfect_costs_def pnty_def)
  moreover have "... = sum w'' {e | e. e \<in> E \<and> (\<nexists> i. new_vertex i \<in> e) \<and> the_vertex ` e \<in> G} +
                   sum w'' {e | e. e \<in> E \<and> (\<nexists> i. new_vertex i \<in> e) \<and> the_vertex ` e \<notin> G} +
                  card {e | e i. e \<in> E \<and> new_vertex i \<in> e} * pnty"
    using assms(1)
    by (subst comm_monoid_add_class.sum.union_disjoint[symmetric]) 
      (auto intro!: arg_cong[of  _ _ "sum w''"])
  moreover have "sum w'' {e | e. e \<in> E \<and> (\<nexists> i. new_vertex i \<in> e) \<and> the_vertex ` e \<in> G}
                  = sum w (project_to_old E \<inter> G)"
  proof-
    have pto_is:"project_to_old E  \<inter> G = 
          (image the_vertex) ` {e |e. e \<in> E \<and> (\<nexists>i. new_vertex i \<in> e) \<and> the_vertex ` e \<in> G}"
      by (auto simp add: project_to_old_def bp_min_costs_to_min_perfect_costs_def)
    have inj: "inj_on ((`) the_vertex) {e |e. e \<in> E \<and> (\<nexists>i. new_vertex i \<in> e) \<and> the_vertex ` e \<in> G}"
      by(auto simp add: inj_on_def  the_vertex_image_inj)
    show ?thesis
      apply(subst pto_is)
      apply(subst comm_monoid_add_class.sum.reindex[OF inj])
      by (auto intro: comm_monoid_add_class.sum.cong 
          simp add: bp_min_max_card_costs_to_min_perfect_costs_def)
  qed
  moreover have "sum w'' {e | e. e \<in> E \<and> (\<nexists> i. new_vertex i \<in> e) \<and> the_vertex ` e \<notin> G} +
                  card {e | e i. e \<in> E \<and> new_vertex i \<in> e} * pnty = 
                (real (card E) - real (card (project_to_old E \<inter> G))) * pnty"
  proof-
    have "sum w'' {e | e. e \<in> E \<and> (\<nexists> i. new_vertex i \<in> e) \<and> the_vertex ` e \<notin> G} =
          card {e | e. e \<in> E \<and> (\<nexists> i. new_vertex i \<in> e) \<and> the_vertex ` e \<notin> G} * pnty"
      by(auto intro!: same_sum_card_prod
          simp add: penalty_def bp_min_max_card_costs_to_min_perfect_costs_def pnty_def)
    moreover have "card {e | e i. e \<in> E \<and> new_vertex i \<in> e} +
            card {e | e. e \<in> E \<and> (\<nexists> i. new_vertex i \<in> e) \<and> the_vertex ` e \<notin> G}
           = real (card E) - card (project_to_old E \<inter> G)"
    proof(subst card_Un_disjoint[symmetric], goal_cases)
      case 4
      show ?case 
      proof(subst card_image[symmetric, of "image old_vertex" "_ \<inter> _"], goal_cases)
        case 1
        show ?case
          using inj_on_def by blast
      next
        case 2
        have "card E \<ge> card ((`) old_vertex ` (project_to_old E \<inter> G))"
          by(auto intro!: card_mono[OF assms(1)] simp add: project_to_old_def
              no_new_vertex_old_vertex_new_vertex_image_inverse)
        hence subst_help: "real (card E) - real (card ((`) old_vertex ` (project_to_old E \<inter> G)))
              = card E -card ((`) old_vertex ` (project_to_old E \<inter> G))"
          by simp
        show ?case     
        proof(subst subst_help, subst card_Diff_subset[symmetric], goal_cases)
          case 1
          show ?case
            using finite_G by blast
        next
          case 2
          show ?case
            by(auto simp add: project_to_old_def
                no_new_vertex_old_vertex_new_vertex_image_inverse)
        next
          case 3
          show ?case
            by (auto intro!: arg_cong[of _ _ card] old_vertex_of_the_vertex_contained
                simp add: project_to_old_def 
                no_new_vertex_old_vertex_new_vertex_image_inverse
                dest!: not_in_imageD)
        qed
      qed
    qed(insert assms, auto)
    ultimately show ?thesis 
      by(auto simp add: algebra_simps distrib_left[symmetric] simp del: distrib_left)
  qed
  ultimately show ?thesis
    by (auto simp add: pnty_def)
qed

lemma max_card_matching_in_perfect_matching:
  assumes "perfect_matching G' M'" "(image old_vertex) ` M \<subseteq> M'" "max_card_matching G M"
  shows "project_to_old M' \<inter> G = M"
proof-
  have M'_matching:"graph_matching G' M'" "matching M'"
    using assms(1) perfect_matchingD(1,2) by blast+
  have finite_M: "finite M" 
    using assms(3) finite_G 
    by(auto dest!: max_card_matchingD intro: rev_finite_subset) 
  show ?thesis
  proof(rule, rule ccontr, goal_cases)
    case 1
    then obtain e where e: "e \<in> project_to_old M'" "e \<notin> M" "e \<in> G" by auto
    hence "e \<in> {{u, v} | u v. u \<in> L \<and> v \<in> R}"
      using M'_matching(1)  
      apply (intro e_in_project_to_old_L_times_R)
      apply(rule subsetD[OF project_to_old_mono])
      by auto
    hence e_props:"e \<in> G" "old_vertex ` e \<in> M'" 
      using e
      by(auto simp add: project_to_old_def bp_min_costs_to_min_perfect_costs_def
          if_split[of "\<lambda> x. x < 0"] no_new_vertex_old_vertex_new_vertex_image_inverse)
    moreover have "matching (insert e M)"
      apply(subst matching_on_old_vertices)
      apply(rule matching_subgraph[OF M'_matching(2)])
      using assms(2) e_props(2) by blast
    moreover have "insert e M \<subseteq> G"
      by (simp add: assms(3) e_props(1) max_card_matchingD)
    ultimately have "graph_matching G (insert e M)" 
      by simp
    moreover have "card (insert e M) > card M"
      by (simp add: e(2) finite_M)
    ultimately show False 
      using linorder_not_le  max_card_matchingD[OF assms(3)]
      by blast
  next 
    case 2
    have "\<lbrakk>(`) old_vertex ` M \<subseteq> M'; M \<subseteq> G; x \<in> M\<rbrakk>
           \<Longrightarrow> \<exists>e. x = the_vertex ` e \<and> e \<in> M' \<and> (\<forall>i. new_vertex i \<notin> e)" for x
      by(rule  exI[of _ "(image old_vertex) _"], rule, 
            rule no_new_vertex_new_vertex_old_vertex_image_inverse[symmetric])
         auto
    thus ?case
      using assms(1,2) conjunct1[OF max_card_matchingD[OF assms(3)]]
      by(auto simp add: project_to_old_def)
  qed
qed

lemma min_weight_perfect_gives_min_weight_max_card_matching:
  assumes "min_weight_perfect_matching G' w'' M"
  shows  "min_weight_max_card_matching G w (project_to_old M \<inter> G)"
proof-
  note M_props = perfect_matchingD[OF min_weight_perfect_matchingD(1)[OF assms]]
    min_weight_perfect_matchingD[OF assms]
  have finite_M: "finite M"
    using M_props(1) finite_G' rev_finite_subset by blast
  have graph_matching_M:"graph_matching G (project_to_old M \<inter> G)" 
    using M_props(2) 
    by(auto intro: matching_subgraph[OF matching_on_project_to_old, of _ "_ \<inter> G"])
  have costs_of_M: "sum w'' M = sum w (project_to_old M \<inter> G)
           + (real (card M) - real (card (project_to_old M \<inter> G))) * 2*penalty G w"
    using sum_on_new_is_sum_on_project_old'[OF finite_M]  by simp
  have False
    if  "\<not> min_weight_max_card_matching G w (project_to_old M \<inter> G)"
  proof-
    have how_not_opt:
      "\<not> max_card_matching G (project_to_old M \<inter> G) \<or> 
           (max_card_matching G (project_to_old M \<inter> G) \<and>
            (\<exists> M'. max_card_matching G M' \<and> sum w M' < sum w (project_to_old M \<inter> G)))"
      using that 
      by(auto simp add: min_weight_max_card_matching_def)
    obtain M' where M': "min_weight_max_card_matching G w M'" 
      using finite_G min_weight_max_card_matching_exists by blast
    note M'_props = min_weight_max_card_matchingD[OF M']
    hence M_projected_non_opt_cases: "card M' > card (project_to_old M \<inter> G)
             \<or> (card M' = card  (project_to_old M \<inter> G) \<and> sum w M' < sum w (project_to_old M \<inter> G))"
    proof(cases rule: context_disjE[OF how_not_opt], goal_cases)
      case 1
      thus ?case 
        using graph_matching_M 
        by(auto dest!: min_weight_max_card_matchingD(1)
            simp add: max_card_matching_def order_less_le)
    next
      case 2
      then obtain M'' where "max_card_matching G M''" "sum w M'' < sum w (project_to_old M \<inter> G)"
        by auto
      moreover hence "sum w M'' \<ge> sum w M'"
        using M' min_weight_max_card_matching_def by blast
      moreover have "card M' =  card  (project_to_old M \<inter> G)" 
        using 2 M'_props(1)
        by(auto  intro: max_card_matchings_same_size)
      ultimately show ?case
        by simp
    qed
    have graph_matching_M': "graph_matching G M'"
      using M' max_card_matchingD min_weight_max_card_matchingD(1) by blast
    note that = graph_matching_M' M_projected_non_opt_cases
    have "\<exists>M''. perfect_matching G' M'' \<and> ((image old_vertex) ` M') \<subseteq> M''"
      using that(1) graph_matching_on_old_vertices old_vertex_of_G_in_G'
      by(auto intro!: extend_to_perfect_matching_in_balanced_complete_bipartite[
            OF balanced_complete_bipartite_perfected(1)[OF bipartite_G]]
          rev_image_eqI
          simp add: finite_L finite_R finite_G')
    then obtain M'' where M'': 
      "perfect_matching G' M''" "((image old_vertex) ` M') \<subseteq> M''" by auto
    have M''_props: "matching M''" "graph_matching G' M''" "finite M''"  
      using M''(1) finite_G' by(auto simp add: perfect_matching_def finite_subset)
    have M''_sum_is: "sum w'' M'' = sum w (project_to_old M'' \<inter> G) +
       (real (card M'') - real (card (project_to_old M'' \<inter> G))) * 2 * penalty G w"
      using sum_on_new_is_sum_on_project_old'[OF M''_props(3)] by simp
    have M''_costs_M: "sum w'' M'' \<ge> sum w'' M"
      using M''(1) M_props(5) by blast
    have M_M''_card:"card M'' = card M" 
      using  M''(1) M_props(4) graph_abs_G' 
      by(auto intro!: perfect_matchings_same_card)
    have project_M''_is: "project_to_old M'' \<inter> G = M'" 
      using  M''(1,2) M'_props(1)
      by(intro max_card_matching_in_perfect_matching) 
    have "sum w'' M > sum w'' M''"
    proof(cases rule: disjE[OF M_projected_non_opt_cases], goal_cases)
      case 1
      have "\<bar>sum w M' - sum w (project_to_old M \<inter> G)\<bar> < 2* penalty G w  "
        using graph_matching_M'  graph_matching_M
        by(auto intro!: weight_diff_of_matchings_less_than_2_penalties simp add: graph_invarG)
      moreover have "penalty G w * (real (card M') * 2) -
           penalty G w * (2 * real (card (project_to_old M \<inter> G))) \<ge> 2 * penalty G w"
        apply(subst right_diff_distrib[symmetric])
        apply(subst ab_semigroup_mult_class.mult.commute[of 2 "penalty G w"])
        apply(subst linordered_ring_strict_class.mult_le_cancel_left_pos)
        using 1 
        by (auto simp add: finite_G penalty_gtr_0 algebra_simps)
      ultimately show ?case
        by(auto simp add: costs_of_M M''_sum_is M_M''_card project_M''_is algebra_simps)
    next
      case 2
      thus ?case
        by(auto simp add: 2(1) costs_of_M M''_sum_is M_M''_card project_M''_is algebra_simps)
    qed
    thus False
      using M''_costs_M by argo
  qed
  thus ?thesis
    by auto
qed
end

hide_const G' L' R'

subsubsection \<open>Maximum Weight (Maximum Cardinality) 
                    to Minimum Weight Perfect (Potentially Non-Bipartite)\<close>

text \<open>Defining the two graphs and some properties\<close>

datatype 'v vertex_wrapper = is_fst: fst_cpy (the_vertex: 'v) | is_snd: snd_cpy (the_vertex: 'v)

lemma fst_cpy_inj_on: "inj_on fst_cpy X"
and snd_cpy_inj_on: "inj_on snd_cpy X"
and img_fst_cpy_inj_on: "inj_on (image fst_cpy) Y"
and img_snd_cpy_inj_on: "inj_on (image snd_cpy) Y"
  by(auto simp add: inj_on_def)

lemma crossing_edge_inj_on: "inj_on (\<lambda>x. {fst_cpy x, snd_cpy x}) X"
  by(auto simp add: inj_on_def)

definition "two_cpys_ptwise_connected G = 
   ((image fst_cpy) ` G \<union> (image snd_cpy) ` G) \<union> {{fst_cpy v, snd_cpy v} | v. v \<in> Vs G}"

lemma in_two_cpys_ptwise_connectedE:
  "\<lbrakk>e \<in> two_cpys_ptwise_connected G;
    \<And> e'. \<lbrakk>e = fst_cpy ` e'; e' \<in> G\<rbrakk> \<Longrightarrow> P;
    \<And> e'. \<lbrakk>e = snd_cpy ` e'; e' \<in> G\<rbrakk> \<Longrightarrow> P;
    \<And> v. \<lbrakk>e = {fst_cpy v, snd_cpy v}; v \<in> Vs G\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto simp add: two_cpys_ptwise_connected_def)

lemma snd_cpy_in_e_in_two_cpys_ptwise_connected_cases:
  "\<lbrakk>snd_cpy v\<in> e; e \<in> two_cpys_ptwise_connected G;
   (\<And> e'. \<lbrakk>e = snd_cpy ` e'; e' \<in> G\<rbrakk> \<Longrightarrow> P ); (e = {fst_cpy v, snd_cpy v} \<Longrightarrow> P)\<rbrakk>  \<Longrightarrow> P"
  by(auto simp add: two_cpys_ptwise_connected_def)

lemma fst_cpy_in_e_in_two_cpys_ptwise_connected_cases:
  "\<lbrakk>fst_cpy v\<in> e; e \<in> two_cpys_ptwise_connected G;
   (\<And> e'. \<lbrakk>e = fst_cpy ` e'; e' \<in> G\<rbrakk> \<Longrightarrow> P ); (e = {fst_cpy v, snd_cpy v} \<Longrightarrow> P)\<rbrakk> \<Longrightarrow> P"
  by(auto simp add: two_cpys_ptwise_connected_def)

definition "is_fst_cpy e = (\<forall> v \<in> e. is_fst v)"
definition "is_snd_cpy e = (\<forall> v \<in> e. is_snd v)"
definition "crossing e = ((\<exists> v \<in> e. is_fst v)\<and> (\<exists> v \<in> e. is_snd v))"

lemma not_crossing_fst_cpy: "\<not> crossing (fst_cpy ` e)" "crossing (fst_cpy ` e) \<Longrightarrow> False"
  and not_crossing_snd_cpy: "\<not> crossing (snd_cpy ` e)" "crossing (snd_cpy ` e) \<Longrightarrow> False"
  by(auto simp add: crossing_def )

lemma crossing_both_copies: "\<lbrakk>fst_cpy v \<in> e; snd_cpy v' \<in> e\<rbrakk> \<Longrightarrow> crossing e"
  by(force simp add: crossing_def intro: exI[of _ v]  exI[of _ v'])

lemma is_fst_cpy_def': "is_fst_cpy e \<longleftrightarrow> (\<exists> e'. e = fst_cpy ` e')"
  by(auto simp add: is_fst_cpy_def image_iff intro!: exI[of _ "the_vertex ` e"])

lemma is_snd_cpy_def': "is_snd_cpy e \<longleftrightarrow> (\<exists> e'. e = snd_cpy ` e')"
  by(auto simp add: is_snd_cpy_def image_iff intro!: exI[of _ "the_vertex ` e"])

lemma e_cpy_ptwise_connected_cases:
 "\<lbrakk>is_fst_cpy e \<Longrightarrow> P; is_snd_cpy e \<Longrightarrow> P; crossing e \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using vertex_wrapper.exhaust_disc
  by(auto simp add: is_fst_cpy_def is_snd_cpy_def crossing_def)

lemma crossing_and_fst_or_snd_cpy_exclusive:
  "\<lbrakk>is_fst_cpy e; crossing e\<rbrakk> \<Longrightarrow> False"
  "\<lbrakk>is_snd_cpy e; crossing e\<rbrakk> \<Longrightarrow> False"
  by (auto simp add: crossing_def is_fst_cpy_def is_snd_cpy_def vertex_wrapper.distinct_disc(1))

lemma fst_cpy_of_e_never_snd_cpy_of_e': "e \<noteq> {} \<or> e' \<noteq> {} \<Longrightarrow> fst_cpy ` e \<noteq> snd_cpy ` e'"
  by blast

lemma fst_and_snd_same_empty: 
  "fst_cpy ` e = snd_cpy ` e' \<Longrightarrow> e = {}"
  "fst_cpy ` e = snd_cpy ` e' \<Longrightarrow> e = e'"
  by blast+

lemma the_vertex_of_fst_cpy: "the_vertex ` fst_cpy ` e = e"
  by force

lemma the_vertex_of_snd_cpy: "the_vertex ` snd_cpy ` e = e"
  by force

lemma Vs_of_fst_cpy: "Vs ((`) fst_cpy ` G) = fst_cpy ` (Vs G)"
  and Vs_of_snd_cpy: "Vs ((`) snd_cpy ` G) = snd_cpy ` (Vs G)"
  by(auto simp add: Vs_def)

lemma Vs_of_mixed_edges:
 "Vs {{fst_cpy v, snd_cpy v} |v. P v}  = fst_cpy ` (Collect P) \<union> snd_cpy ` (Collect P)"
  by(auto simp add: Vs_def)

definition "get_fst_only G = { the_vertex ` e | e. e \<in> G \<and> is_fst_cpy e}"

lemma get_fst_only_finite: "finite G \<Longrightarrow> finite (get_fst_only G)"
  by(auto simp add: get_fst_only_def)

lemma get_fst_only_contains_empty: "{} \<in> get_fst_only G \<longleftrightarrow> {} \<in> G"
  by(auto simp add: get_fst_only_def is_fst_cpy_def')

definition "get_snd_only G = { the_vertex ` e | e. e \<in> G \<and> is_snd_cpy e}"

lemma get_snd_only_finite: "finite G \<Longrightarrow> finite (get_snd_only G)"
  by(auto simp add: get_snd_only_def)

lemma get_snd_only_contains_empty: "{} \<in> get_snd_only G \<longleftrightarrow> {} \<in> G"
  by(auto simp add: get_snd_only_def is_snd_cpy_def')

definition "get_crossing G = {e | e. e \<in> G \<and> crossing e}"

definition "get_crossing_projected G = {the_vertex ` e | e. e \<in> G \<and> crossing e}"

lemma get_crossing_get_crossing_projected:
  "(image the_vertex) ` get_crossing G = get_crossing_projected G"
  by(auto simp add: get_crossing_projected_def get_crossing_def)

lemma in_corssingI: "\<lbrakk>e \<in> G; crossing e\<rbrakk> \<Longrightarrow> e \<in> get_crossing G "
  and in_corssingE: "\<lbrakk>e \<in> get_crossing G; \<lbrakk>e \<in> G; crossing e\<rbrakk> \<Longrightarrow>P\<rbrakk> \<Longrightarrow> P "
  and in_corssingD:
   "e \<in> get_crossing G \<Longrightarrow>e \<in> G"
   "e \<in> get_crossing G \<Longrightarrow>crossing e"
  by(auto simp add: get_crossing_def)

definition "extend_matching G M = 
 ((image fst_cpy) ` M \<union> (image snd_cpy) ` M \<union> {{fst_cpy v, snd_cpy v} | v. v \<in> Vs G - Vs M})"

lemma exten_matching_in_extended_G:
  "M \<subseteq> G \<Longrightarrow> extend_matching G M \<subseteq> two_cpys_ptwise_connected G"
  by(auto simp add: extend_matching_def two_cpys_ptwise_connected_def)

lemma get_fst_only_of_extend_matching:
  "get_fst_only (extend_matching G M) =  M"
  by(auto simp add: extend_matching_def get_fst_only_def
                    the_vertex_of_fst_cpy the_vertex_of_snd_cpy is_fst_cpy_def'
            intro!: exI[of "\<lambda> x. _ = the_vertex ` x \<and> _ x" "fst_cpy ` _", OF
                    conjI[OF the_vertex_of_fst_cpy[symmetric]]])

lemma get_snd_only_of_extend_matching:
  "get_snd_only (extend_matching G M) =  M"
  by(auto simp add: extend_matching_def get_snd_only_def
                    the_vertex_of_fst_cpy the_vertex_of_snd_cpy is_snd_cpy_def'
            intro!: exI[of "\<lambda> x. _ = the_vertex ` x \<and> _ x" "snd_cpy ` _", OF
                    conjI[OF the_vertex_of_snd_cpy[symmetric]]])

lemma finite_extend_matching: "\<lbrakk>finite (Vs G); finite M\<rbrakk> \<Longrightarrow> finite (extend_matching G M)"
  by(auto simp add: extend_matching_def)

lemma empty_not_in_extend_matching: "{} \<notin> M \<Longrightarrow> {} \<notin> (extend_matching G M)"
  by(auto simp add: extend_matching_def)

lemma the_vertex_of_Vs_ptwsie_connected_is_Vs:
  "the_vertex ` (Vs (two_cpys_ptwise_connected G)) = Vs G"
  by(auto simp add: two_cpys_ptwise_connected_def vs_union Vs_of_fst_cpy
                     Vs_of_snd_cpy Vs_of_mixed_edges image_Un the_vertex_of_fst_cpy)

lemma graph_abs_two_copies: "graph_abs G \<Longrightarrow> graph_abs (two_cpys_ptwise_connected G)"
  by(auto simp add: two_cpys_ptwise_connected_def graph_abs_def vs_union
                    Vs_of_fst_cpy Vs_of_snd_cpy Vs_of_mixed_edges
            intro!: dblton_graph_union doublton_inj fst_cpy_inj_on snd_cpy_inj_on
             intro: dblton_graphI) 

lemma extend_matching_full_Vs:
  assumes "M \<subseteq> G" 
  shows "Vs (extend_matching G M) = Vs (two_cpys_ptwise_connected G)"
proof(rule, all \<open>rule\<close>, goal_cases)
  case (1 x)
  then obtain e where ex: "e \<in> extend_matching G M" "x \<in> e" 
    by (meson vs_member)
  hence "e \<in> two_cpys_ptwise_connected G" 
    using assms exten_matching_in_extended_G by blast
  then show ?case 
    using ex by blast
next
  case (2 x)
  hence the_vertex_x_in_G:"the_vertex x \<in> Vs G"
    using the_vertex_of_Vs_ptwsie_connected_is_Vs[of G] by blast 
  show ?case 
  proof(cases "the_vertex x \<in> Vs M")
    case True
    then obtain e where e: "e \<in> M" "the_vertex x \<in> e" 
      by (meson vs_member)
    hence "fst_cpy ` e \<in> extend_matching G M"  "snd_cpy ` e \<in> extend_matching G M"
      by(auto simp add: extend_matching_def)
    moreover have "x \<in> fst_cpy`  e \<or> x \<in> snd_cpy`  e"
      using e by(cases x) auto
    ultimately show ?thesis 
      using e by auto
  next
    case False
    hence a: "{fst_cpy (the_vertex x), snd_cpy (the_vertex x)} 
      \<in> {{fst_cpy v, snd_cpy v} | v. v \<in> Vs G - Vs M}"
      using the_vertex_x_in_G by auto
    have "x \<in> Vs {{fst_cpy v, snd_cpy v} | v. v \<in> Vs G - Vs M}"
      using a by(cases x) auto
    thus ?thesis
      by(unfold extend_matching_def vs_union) blast
  qed
qed

text \<open>Matchings in those Graphs.\<close>

lemma get_fst_only_of_two_cpys_ptwise_connected_subset:
  assumes "G' \<subseteq> two_cpys_ptwise_connected G"
  shows "get_fst_only G' \<subseteq> G"
proof(rule, goal_cases)
  case (1 e)
  then obtain e' where "e = the_vertex ` e'" "e' \<in> G'" "is_fst_cpy e'"
    by(auto simp add: get_fst_only_def)
  moreover hence "e' \<in> two_cpys_ptwise_connected G"
    using assms by auto
  ultimately show ?case
    by(auto simp add: two_cpys_ptwise_connected_def is_fst_cpy_def' is_snd_cpy_def'
                      the_vertex_of_fst_cpy the_vertex_of_snd_cpy)
qed

lemma get_fst_only_of_matching:
  assumes "matching M"
  shows "matching (get_fst_only M)"
proof(rule matchingI, rule ccontr, goal_cases)
  case (1 e1 e2)
    then obtain e1' where e1: "e1 = the_vertex ` e1'" "e1' \<in> M" "is_fst_cpy e1'"
      by(auto simp add: get_fst_only_def)
    from 1 obtain e2' where e2: "e2 = the_vertex ` e2'" "e2' \<in> M" "is_fst_cpy e2'"
      by(auto simp add: get_fst_only_def)
    have "e1' \<inter> e2' \<noteq> {}"
      using 1(4) e1(3) e2(3) 
      by (auto simp add: e1(1) e2(1) is_fst_cpy_def') 
    moreover have "e1' \<noteq> e2'"
      using 1(3) e1(1,3) e2(1,3) 
      by(force simp add: is_fst_cpy_def')
    ultimately show ?case 
      using assms e1(2) e2(2)
      by(auto elim!: matchingE)
  qed

lemma get_fst_only_of_graph_matching:
  assumes "graph_matching (two_cpys_ptwise_connected G) M"
  shows "graph_matching G (get_fst_only M)"
  using get_fst_only_of_two_cpys_ptwise_connected_subset[of M G]
        get_fst_only_of_matching[of M] assms
  by auto

lemma get_snd_only_of_two_cpys_ptwise_connected_subset:
  assumes "G' \<subseteq> two_cpys_ptwise_connected G"
  shows "get_snd_only G' \<subseteq> G"
proof(rule, goal_cases)
  case (1 e)
  then obtain e' where "e = the_vertex ` e'" "e' \<in> G'" "is_snd_cpy e'"
    by(auto simp add: get_snd_only_def)
  moreover hence "e' \<in> two_cpys_ptwise_connected G"
    using assms by auto
  ultimately show ?case
    by(auto simp add: two_cpys_ptwise_connected_def is_fst_cpy_def' is_snd_cpy_def'
                      the_vertex_of_fst_cpy the_vertex_of_snd_cpy)
qed

lemma get_snd_only_of_matching:
  assumes "matching M"
  shows "matching (get_snd_only M)"
proof(rule matchingI, rule ccontr, goal_cases)
  case (1 e1 e2)
    then obtain e1' where e1: "e1 = the_vertex ` e1'" "e1' \<in> M" "is_snd_cpy e1'"
      by(auto simp add: get_snd_only_def)
    from 1 obtain e2' where e2: "e2 = the_vertex ` e2'" "e2' \<in> M" "is_snd_cpy e2'"
      by(auto simp add: get_snd_only_def)
    have "e1' \<inter> e2' \<noteq> {}"
      using 1(4) e1(3) e2(3) 
      by (auto simp add: e1(1) e2(1) is_snd_cpy_def') 
    moreover have "e1' \<noteq> e2'"
      using 1(3) e1(1,3) e2(1,3) 
      by(force simp add: is_snd_cpy_def')
    ultimately show ?case 
      using assms e1(2) e2(2)
      by(auto elim!: matchingE)
  qed

lemma get_snd_only_of_graph_matching:
  assumes "graph_matching (two_cpys_ptwise_connected G) M"
  shows "graph_matching G (get_snd_only M)"
  using get_snd_only_of_two_cpys_ptwise_connected_subset[of M G]
        get_snd_only_of_matching[of M] assms
  by auto

lemma graph_matching_extend_matching:
  assumes "graph_matching G M"
  shows   "graph_matching (two_cpys_ptwise_connected G) (extend_matching G M)"
proof
  show "extend_matching G M \<subseteq> two_cpys_ptwise_connected G"
    using exten_matching_in_extended_G assms by blast
  show "matching (extend_matching G M)"
    unfolding extend_matching_def
  proof(rule matching_vertex_disj_union, goal_cases)
    case 1
    then show ?case 
      using assms
      by(auto intro!: matching_vertex_disj_union matching_image 
            simp add: fst_cpy_inj_on snd_cpy_inj_on Vs_of_fst_cpy Vs_of_snd_cpy)  
  next
    case 2
    then show ?case 
      by(auto intro!: matchingI)
  next
    case 3
    then show ?case 
      by(auto simp add: Vs_of_fst_cpy Vs_of_snd_cpy vs_union Vs_of_mixed_edges)
  qed
qed

text \<open>now add weights, too.\<close>

subsubsection \<open>Mincost to Mincost-Perfect (General)\<close>

definition "min_costs_to_min_perfect_costs G (w::'a set \<Rightarrow> real) =
            (\<lambda> e. if crossing e then 0 else w (the_vertex ` e))"

abbreviation "mpc \<equiv> min_costs_to_min_perfect_costs"

lemma weight_big_matching_split:
  assumes "finite M" "{} \<notin> M"
  shows  "sum (mpc G w) M = sum w (get_fst_only M) + sum w (get_snd_only M)"
proof-
  have "sum (mpc G w) {e | e. e\<in> M \<and> is_fst_cpy e } = sum w (get_fst_only M)"
    unfolding min_costs_to_min_perfect_costs_def
  proof(subst comm_monoid_add_class.sum.cong[OF refl if_not_P], goal_cases)
    case 2
    show ?case
     apply(subst sum_inner_function_to_image[of "image the_vertex" ])
      by(auto intro!: arg_cong[of _ _ "sum w"] 
          simp add: get_fst_only_def inj_on_def is_fst_cpy_def' the_vertex_of_fst_cpy)
  qed(auto intro: crossing_and_fst_or_snd_cpy_exclusive)
  moreover have "sum (mpc G w) {e | e. e\<in> M \<and> is_snd_cpy e } = sum w (get_snd_only M)"
    unfolding min_costs_to_min_perfect_costs_def
  proof(subst comm_monoid_add_class.sum.cong[OF refl if_not_P], goal_cases)
    case 2
    show ?case
     apply(subst sum_inner_function_to_image[of "image the_vertex" ])
      by(auto intro!: arg_cong[of _ _ "sum w"] 
          simp add: get_snd_only_def inj_on_def is_snd_cpy_def' the_vertex_of_snd_cpy)
  qed(auto intro: crossing_and_fst_or_snd_cpy_exclusive)
  moreover have "sum (mpc G w) {e | e. e\<in> M \<and> crossing e } = 0"
    by(auto simp add: min_costs_to_min_perfect_costs_def)
  moreover have "sum (mpc G w) M = 
      sum (mpc G w) {e |e. e \<in> M \<and> is_fst_cpy e} +
      sum (mpc G w) {e |e. e \<in> M \<and> is_snd_cpy e}+
      sum (mpc G w) {e |e. e \<in> M \<and> crossing e}"
  proof(subst comm_monoid_add_class.sum.union_disjoint[symmetric], goal_cases)
    case 3
    show ?case
      using assms 
      by(auto simp add: is_fst_cpy_def' is_snd_cpy_def' dest: fst_and_snd_same_empty(1))
  next
    case 4
    show ?case
    proof(subst comm_monoid_add_class.sum.union_disjoint[symmetric], goal_cases)
      case 4
      show ?case 
        by(auto intro!: arg_cong[of _ _ "sum (min_costs_to_min_perfect_costs G w)"]
                 intro: e_cpy_ptwise_connected_cases)
    qed (insert assms, auto  dest!: crossing_and_fst_or_snd_cpy_exclusive)
  qed (insert assms, auto)
  ultimately show ?thesis 
    by simp
qed

lemma weight_of_extend_matching:
  assumes "finite M" "finite (Vs G)" "{} \<notin> M"
  shows  "sum (mpc G w) (extend_matching G M)  = 2* sum w M"
  using assms
  by(auto simp add: weight_big_matching_split[of "extend_matching G M"] 
                    finite_extend_matching empty_not_in_extend_matching
                    get_fst_only_of_extend_matching get_snd_only_of_extend_matching)

lemma perfect_matching_extend_matching:
  assumes "graph_matching G M"
  shows   "perfect_matching (two_cpys_ptwise_connected G) (extend_matching G M)"
  using assms
  by (intro perfect_matchingI)
     (auto simp add: exten_matching_in_extended_G
                     graph_matching_extend_matching extend_matching_full_Vs)

text \<open>We show that for a minimum weight perfect matching in the old graph,
      the submatchings in the two copies of the old graph must have the same weight.
      We prove this by excluding one weight being strictly greater than the other by contradiction.
      There are two symmetric lemmas before the main statement.\<close>

lemma mwpm_in_two_cpys_ptwise_connected_fst_geq_snd:
  assumes "min_weight_perfect_matching (two_cpys_ptwise_connected G) (mpc G w) M"
          "sum w (get_fst_only M) < sum w (get_snd_only M)"
          "finite (Vs M)" "{} \<notin> M" "finite (Vs G)"
    shows False
proof-
  have finite_M: "finite M" 
    by (simp add: assms(3) finite_Vs_then_finite)
  have matching_fst_only: "graph_matching G (get_fst_only M)"
    using assms(1)
    by(intro get_fst_only_of_graph_matching)
      (auto elim!: min_weight_perfect_matchingE dest: perfect_matchingD)
  have "sum (mpc G w) M =  sum w (get_fst_only M) + sum w (get_snd_only M)"
    by(rule weight_big_matching_split[OF finite_M assms(4)])
  moreover have "sum w (get_fst_only M) + sum w (get_snd_only M) > 2*sum w (get_fst_only M)"
    using assms(2) by simp
  moreover have "2*sum w (get_fst_only M) = sum (mpc G w) (extend_matching G (get_fst_only M))"
    by(auto intro!: weight_of_extend_matching[symmetric]
          simp add: finite_M get_fst_only_finite assms(5,4) get_fst_only_contains_empty)
  moreover have "perfect_matching (two_cpys_ptwise_connected G)
                       (extend_matching G (get_fst_only M))"
    using matching_fst_only
    by(rule perfect_matching_extend_matching)
  ultimately show False
    using assms(1)
    by(auto simp add: min_weight_perfect_matching_def)
qed

lemma mwpm_in_two_cpys_ptwise_connected_fst_leq_snd:
  assumes "min_weight_perfect_matching (two_cpys_ptwise_connected G) (mpc G w) M"
          "sum w (get_fst_only M) > sum w (get_snd_only M)"
          "finite (Vs M)" "{} \<notin> M" "finite (Vs G)"
    shows False
proof-
  have finite_M: "finite M" 
    by (simp add: assms(3) finite_Vs_then_finite)
  have matching_snd_only: "graph_matching G (get_snd_only M)"
    using assms(1)
    by(intro get_snd_only_of_graph_matching)
      (auto elim!: min_weight_perfect_matchingE dest: perfect_matchingD)
  have "sum (mpc G w) M =  sum w (get_fst_only M) + sum w (get_snd_only M)"
    by(rule weight_big_matching_split[OF finite_M assms(4)])
  moreover have "sum w (get_fst_only M) + sum w (get_snd_only M) > 2*sum w (get_snd_only M)"
    using assms(2) by simp
  moreover have "2*sum w (get_snd_only M) = sum (mpc G w) (extend_matching G (get_snd_only M))"
    by(auto intro!: weight_of_extend_matching[symmetric]
          simp add: finite_M get_snd_only_finite assms(5,4) get_snd_only_contains_empty)
  moreover have "perfect_matching (two_cpys_ptwise_connected G)
                       (extend_matching G (get_snd_only M))"
    using matching_snd_only
    by(rule perfect_matching_extend_matching)
  ultimately show False
    using assms(1)
    by(auto simp add: min_weight_perfect_matching_def)
qed

lemma mwpm_in_two_cpys_ptwise_connected_fst_eq_snd:
  assumes "min_weight_perfect_matching (two_cpys_ptwise_connected G) (mpc G w) M"
          "finite (Vs M)" "{} \<notin> M" "finite (Vs G)"
   shows  "sum w (get_fst_only M) = sum w (get_snd_only M)"
  using mwpm_in_two_cpys_ptwise_connected_fst_leq_snd 
        mwpm_in_two_cpys_ptwise_connected_fst_geq_snd 
        assms
  by force

text \<open>Main reduction theorem:
     A minimum weight perfect matching in the new graph implies
     two (not necessarily distinct) minimum weight matchings in the old graph.
     These are obtained by looking at the first or second copy exclusively.\<close>

theorem min_weight_to_min_weight_perfect_general:
  assumes  "min_weight_perfect_matching (two_cpys_ptwise_connected G) (mpc G w) M"
           "finite (Vs M)" "{} \<notin> M" "finite (Vs G)" "{} \<notin> G"
  shows    "min_weight_matching G w (get_fst_only M)"
           "min_weight_matching G w (get_snd_only M)"
proof-
  have finite_M: "finite M" 
    by (simp add: assms(2) finite_Vs_then_finite)
  have sum_split: "sum (mpc G w) M = sum w (get_fst_only M) + sum w (get_snd_only M)"
    using finite_M assms(3) 
    by(rule weight_big_matching_split)
  have same_sum: "sum w (get_fst_only M) = sum w (get_snd_only M)"
    using assms 
    by(auto intro!: mwpm_in_two_cpys_ptwise_connected_fst_eq_snd)
  show  "min_weight_matching G w (get_fst_only M)"
  proof(rule ccontr, goal_cases)
    case 1
    have "graph_matching G (get_fst_only M)"
      using assms(1)
      by(intro get_fst_only_of_graph_matching)
        (auto elim!: min_weight_perfect_matchingE dest: perfect_matchingD)
    then obtain M' where M': "sum w M' < sum w (get_fst_only M)" "graph_matching G M'"
      using 1
      by(auto simp add: min_weight_matching_def linorder_not_le) 
    have M'_props: "finite M'" "{} \<notin> M'"
      using M'(2) assms(4,5) finite_Vs_then_finite finite_subset by blast+
    have "sum (mpc G w) (extend_matching G M') = 2*sum w M'"
      by(auto intro!: weight_of_extend_matching M'_props assms(4))
    moreover have "perfect_matching (two_cpys_ptwise_connected G) (extend_matching G M')"
      using M'(2)
      by(auto intro!: perfect_matching_extend_matching)
    ultimately have "\<not> min_weight_perfect_matching (two_cpys_ptwise_connected G) (mpc G w) M"
      using M'(1) sum_split same_sum
      by(auto simp add: min_weight_perfect_matching_def)
    thus False 
      using assms(1) 
      by simp
  qed
    show  "min_weight_matching G w (get_snd_only M)"
  proof(rule ccontr, goal_cases)
    case 1
    have "graph_matching G (get_snd_only M)"
      using assms(1)
      by(intro get_snd_only_of_graph_matching)
        (auto elim!: min_weight_perfect_matchingE dest: perfect_matchingD)
    then obtain M' where M': "sum w M' < sum w (get_snd_only M)" "graph_matching G M'"
      using 1
      by(auto simp add: min_weight_matching_def linorder_not_le) 
    have M'_props: "finite M'" "{} \<notin> M'"
      using M'(2) assms(4,5) finite_Vs_then_finite finite_subset by blast+
    have "sum (mpc G w) (extend_matching G M') = 2*sum w M'"
      by(auto intro!: weight_of_extend_matching M'_props assms(4))
    moreover have "perfect_matching (two_cpys_ptwise_connected G) (extend_matching G M')"
      using M'(2)
      by(auto intro!: perfect_matching_extend_matching)
    ultimately have "\<not> min_weight_perfect_matching (two_cpys_ptwise_connected G) (mpc G w) M"
      using M'(1) sum_split same_sum
      by(auto simp add: min_weight_perfect_matching_def)
    thus False 
      using assms(1) 
      by simp
  qed
qed

subsubsection \<open>Mincost-Maxcard to Mincost-Perfect (General)\<close>

text \<open>The same for min weight max card\<close>

definition "min_weight_max_card_costs_to_min_perfect_costs G (w::'a set \<Rightarrow> real) =
            (\<lambda> e. if crossing e then 4* penalty G w else w (the_vertex ` e))"

abbreviation "mwmcpc \<equiv> min_weight_max_card_costs_to_min_perfect_costs"

lemma weight_big_matching_split_max_card:
  assumes "finite M" "{} \<notin> M"
  shows  "sum (mwmcpc G w) M = 
     sum w (get_fst_only M) + sum w (get_snd_only M) + card (get_crossing M)*4*penalty G w "
proof-
  have "sum (mwmcpc G w) {e | e. e\<in> M \<and> is_fst_cpy e } = sum w (get_fst_only M)"
    unfolding min_weight_max_card_costs_to_min_perfect_costs_def
  proof(subst comm_monoid_add_class.sum.cong[OF refl if_not_P], goal_cases)
    case 2
    show ?case
     apply(subst sum_inner_function_to_image[of "image the_vertex" ])
      by(auto intro!: arg_cong[of _ _ "sum w"] 
          simp add: get_fst_only_def inj_on_def is_fst_cpy_def' the_vertex_of_fst_cpy)
  qed(auto intro: crossing_and_fst_or_snd_cpy_exclusive)
  moreover have "sum (mwmcpc G w) {e | e. e\<in> M \<and> is_snd_cpy e } = sum w (get_snd_only M)"
    unfolding min_weight_max_card_costs_to_min_perfect_costs_def
  proof(subst comm_monoid_add_class.sum.cong[OF refl if_not_P], goal_cases)
    case 2
    show ?case
     apply(subst sum_inner_function_to_image[of "image the_vertex" ])
      by(auto intro!: arg_cong[of _ _ "sum w"] 
          simp add: get_snd_only_def inj_on_def is_snd_cpy_def' the_vertex_of_snd_cpy)
  qed(auto intro: crossing_and_fst_or_snd_cpy_exclusive)
  moreover have "sum (mwmcpc G w) {e | e. e\<in> M \<and> crossing e } 
           = card (get_crossing M)*4*penalty G w "
    by(auto simp add:  min_weight_max_card_costs_to_min_perfect_costs_def 
                       get_crossing_def comm_monoid_add_class.sum.cong[OF refl if_P])
  moreover have "sum (mwmcpc G w) M = 
      sum (mwmcpc G w) {e |e. e \<in> M \<and> is_fst_cpy e} +
      sum (mwmcpc G w) {e |e. e \<in> M \<and> is_snd_cpy e}+
      sum (mwmcpc G w) {e |e. e \<in> M \<and> crossing e}"
  proof(subst comm_monoid_add_class.sum.union_disjoint[symmetric], goal_cases)
    case 3
    show ?case
      using assms 
      by(auto simp add: is_fst_cpy_def' is_snd_cpy_def' dest: fst_and_snd_same_empty(1))
  next
    case 4
    show ?case
    proof(subst comm_monoid_add_class.sum.union_disjoint[symmetric], goal_cases)
      case 4
      show ?case 
        by(auto intro!: arg_cong[of _ _ "sum (mwmcpc G w)"]
                 intro: e_cpy_ptwise_connected_cases)
    qed (insert assms, auto  dest!: crossing_and_fst_or_snd_cpy_exclusive)
  qed (insert assms, auto)
  ultimately show ?thesis 
    by simp
qed

lemma card_crossing_is_card_unmatched_fst:
  assumes "perfect_matching (two_cpys_ptwise_connected G) M"
  shows "card (get_crossing M) = card (Vs G - Vs (get_fst_only M))"
proof-
  note M_prop = perfect_matchingD[OF assms(1)]
  show ?thesis
proof(rule bij_betw_same_card[of "\<lambda> x. {fst_cpy x, snd_cpy x}", symmetric],
      unfold bij_betw_def, rule, goal_cases)
  case 1
  show ?case
    by(auto intro: inj_onI)
  case 2
  show ?case
  proof(rule, all \<open>rule\<close>, goal_cases)
    case (1 e)
    then obtain v where v: "v \<in> Vs G" "v \<notin> Vs (get_fst_only M)" "e = {fst_cpy v, snd_cpy v}" by auto
    hence "fst_cpy v \<in> Vs (two_cpys_ptwise_connected G)"
      by (simp add: Vs_of_fst_cpy two_cpys_ptwise_connected_def vs_union)
    then obtain e' where e': "fst_cpy v \<in> e'" "e' \<in> M" 
      using  M_prop(3)  vs_member[of "fst_cpy v"] by auto
    moreover have "e' = e"
      using M_prop(1) e'(1,2)  v 
       by(auto dest!: spec[of "\<lambda> x. _ x\<or> v \<notin> x" "the_vertex ` e'"]
            simp add:  get_fst_only_def is_fst_cpy_def' vs_member image_iff
           elim!: fst_cpy_in_e_in_two_cpys_ptwise_connected_cases[OF e'(1), of G])
     thus ?case 
       using v(3)  e'(2)
       by(auto intro!: in_corssingI crossing_both_copies e'(1,2))
  next
    case (2 e)
    then obtain x where e: "e = {fst_cpy x, snd_cpy x}" "e \<in> M" 
      using M_prop(1)
      by(auto elim!: in_corssingE 
              intro: in_two_cpys_ptwise_connectedE[of e G] 
               dest: not_crossing_snd_cpy(2) not_crossing_fst_cpy(2))
    moreover have  "x \<notin> Vs (get_fst_only M)"
    proof(rule ccontr, goal_cases)
      case 1
      then obtain e' where e': "x \<in> the_vertex ` e'" "e' \<in> M" "is_fst_cpy e'" 
        by(auto simp add: get_fst_only_def vs_member)
      hence "e \<noteq> e'" 
        using "2" crossing_and_fst_or_snd_cpy_exclusive(1) in_corssingD(2) by auto
      moreover have "fst_cpy x \<in> e \<inter> e'" 
        using e'(1,3) e(1) 
        by(auto simp add: is_fst_cpy_def')
      ultimately show False
        using M_prop(2) e'(2) e(2) 
        by(auto elim!: matchingE)
    qed
    moreover have "x \<in> Vs G" 
      by(auto intro!: imageI[of "fst_cpy x" _ the_vertex, simplified] 
            simp add: M_prop(3) edges_are_Vs[of "fst_cpy x" "snd_cpy x" M, 
                          simplified e(1)[symmetric], OF e(2)]
                      the_vertex_of_Vs_ptwsie_connected_is_Vs[of G, symmetric])
    ultimately show ?case
      by auto
  qed
qed
qed

lemma card_crossing_is_card_unmatched_snd:
  assumes "perfect_matching (two_cpys_ptwise_connected G) M"
    shows "card (get_crossing M) = card ( Vs G - Vs (get_snd_only M))"
proof-
  note M_prop = perfect_matchingD[OF assms(1)]
  show ?thesis
proof(rule bij_betw_same_card[of "\<lambda> x. {fst_cpy x, snd_cpy x}", symmetric],
      unfold bij_betw_def, rule, goal_cases)
  case 1
  show ?case
    by(auto intro: inj_onI)
  case 2
  show ?case
  proof(rule, all \<open>rule\<close>, goal_cases)
    case (1 e)
    then obtain v where v: "v \<in> Vs G" "v \<notin> Vs (get_snd_only M)" "e = {fst_cpy v, snd_cpy v}" by auto
    hence "snd_cpy v \<in> Vs (two_cpys_ptwise_connected G)"
      by (simp add: Vs_of_snd_cpy two_cpys_ptwise_connected_def vs_union)
    then obtain e' where e': "snd_cpy v \<in> e'" "e' \<in> M" 
      using  M_prop(3)  vs_member[of "snd_cpy v"] by auto
    moreover have "e' = e"
      using M_prop(1) e'(1,2)  v 
       by(auto dest!: spec[of "\<lambda> x. _ x\<or> v \<notin> x" "the_vertex ` e'"]
            simp add:  get_snd_only_def is_snd_cpy_def' vs_member image_iff
           elim!: snd_cpy_in_e_in_two_cpys_ptwise_connected_cases[OF e'(1), of G])
     thus ?case                   
       using v(3)  e'(2)
       by(auto intro!: in_corssingI crossing_both_copies e'(1,2))
  next
    case (2 e)
    then obtain x where e: "e = {fst_cpy x, snd_cpy x}" "e \<in> M" 
      using M_prop(1)
      by(auto elim!: in_corssingE 
              intro: in_two_cpys_ptwise_connectedE[of e G] 
               dest: not_crossing_snd_cpy(2) not_crossing_fst_cpy(2))
    moreover have  "x \<notin> Vs (get_snd_only M)"
    proof(rule ccontr, goal_cases)
      case 1
      then obtain e' where e': "x \<in> the_vertex ` e'" "e' \<in> M" "is_snd_cpy e'" 
        by(auto simp add: get_snd_only_def vs_member)
      hence "e \<noteq> e'" 
        using "2" crossing_and_fst_or_snd_cpy_exclusive(2) in_corssingD(2) by auto
      moreover have "snd_cpy x \<in> e \<inter> e'" 
        using e'(1,3) e(1) 
        by(auto simp add: is_snd_cpy_def')
      ultimately show False
        using M_prop(2) e'(2) e(2) 
        by(auto elim!: matchingE)
    qed
    moreover have "x \<in> Vs G" 
      by(auto intro!: imageI[of "snd_cpy x" _ the_vertex, simplified] 
            simp add: M_prop(3) edges_are_Vs_2[of "fst_cpy x" "snd_cpy x" M, 
                          simplified e(1)[symmetric], OF e(2)]
                      the_vertex_of_Vs_ptwsie_connected_is_Vs[of G, symmetric])
    ultimately show ?case
      by auto
  qed
qed
qed
  
lemma weight_of_extend_matching_max_card:
  assumes "finite M" "finite (Vs G)" "{} \<notin> M"
   shows  "sum (mwmcpc G w) (extend_matching G M) = 2* sum w M + (card (Vs G - Vs M))*4*penalty G w"
proof-
  have "sum (mwmcpc G w) (extend_matching G M) =
         2* sum w M + real (card (get_crossing (extend_matching G M))) * 4*penalty G w"
  using assms
   by(auto simp add: weight_big_matching_split_max_card[of "extend_matching G M", of G w] 
                    finite_extend_matching empty_not_in_extend_matching
                    get_fst_only_of_extend_matching get_snd_only_of_extend_matching)
  moreover have "card (get_crossing (extend_matching G M)) = card (Vs G - Vs M)"
    by(auto simp add: get_crossing_def extend_matching_def bij_betw_def crossing_edge_inj_on
             crossing_both_copies
            intro!: bij_betw_same_card[of "\<lambda> x. {fst_cpy x, snd_cpy x}", symmetric]
             dest!: not_crossing_fst_cpy(2) not_crossing_snd_cpy(2))
  ultimately show ?thesis 
    by simp
qed

lemma mwmcpc_in_two_cpys_ptwise_connected_fst_card_eq_snd_card:
  assumes "perfect_matching (two_cpys_ptwise_connected G) M" "graph_abs G"
    shows "card (get_fst_only M) = card (get_snd_only M)"  
proof-
  have "matching (get_fst_only M)"
    using assms(1) get_fst_only_of_matching perfect_matchingD(2) by auto
  moreover have "matching (get_snd_only M)"
    using assms(1) get_snd_only_of_matching perfect_matchingD(2) by auto
  moreover have "get_fst_only M \<subseteq> G" 
    by (simp add: assms(1) get_fst_only_of_two_cpys_ptwise_connected_subset perfect_matchingD(1))
  moreover have "get_snd_only M \<subseteq> G"
    by (simp add: assms(1) get_snd_only_of_two_cpys_ptwise_connected_subset perfect_matchingD(1))
  moreover have  "card (Vs G - Vs (get_fst_only M)) = card (Vs G - Vs (get_snd_only M))"
      using assms(1) card_crossing_is_card_unmatched_fst card_crossing_is_card_unmatched_snd
      by fastforce  
ultimately show ?thesis
  by(auto simp add: same_matching_card[of G] assms(2) )
qed

lemma  not_max_card_matching_not_min_weight_perfect:
  assumes "perfect_matching (two_cpys_ptwise_connected G) M"
          "graph_matching G M'" "card M' > card (get_fst_only M)" "graph_abs G"
    shows "sum (mwmcpc G w) (extend_matching G M') < sum (mwmcpc G w) M"
proof-
  note M_props = perfect_matchingD[OF assms(1)]
  have graph_abs_ext_G: "graph_abs (two_cpys_ptwise_connected G)"
    by (simp add: assms(4) graph_abs_two_copies)
  hence graph_abs_M:"graph_abs M" 
    using M_props(1) graph_abs_mono by auto
  have graph_invar_G: "graph_invar G"
    using assms(4) graph_abs_def by auto
  have finite_M: "finite M"
    using M_props(1) finite_subset graph_abs.finite_E graph_abs_ext_G by blast
  have empty_nin_M: "{} \<notin> M" 
    using graph_abs_M graph_abs_no_empty by auto
  have weight_split_M:
     "sum (mwmcpc G w) M = sum w (get_fst_only M) + sum w (get_snd_only M) +
          real (card (get_crossing M)) * 4*penalty G w"
    using weight_big_matching_split_max_card[of M]
    by(auto simp add: finite_M empty_nin_M)
  have matching_fst: "graph_matching G (get_fst_only M)"
     using M_props(1,2) get_fst_only_of_graph_matching by blast
  have matching_snd: "graph_matching G (get_snd_only M)"
    using M_props(1,2) get_snd_only_of_graph_matching by blast
  have weight_M_bounds:
     "sum (mwmcpc G w) M < real (card (get_crossing M)) * 4* penalty G w + 2*penalty G w"
      "sum (mwmcpc G w) M > real (card (get_crossing M)) * 4* penalty G w - 2*penalty G w"
    using weight_of_matching_abs_less[OF graph_invar_G matching_fst, of w]
          weight_of_matching_abs_less[OF graph_invar_G matching_snd, of w] 
    by(auto simp add: weight_split_M)
  have card_crossing_M: "card (get_crossing M) = card (Vs G - Vs (get_fst_only M))"
    using assms(1) by(auto intro!: card_crossing_is_card_unmatched_fst)
  have finite_M':"finite M'"
    using assms(3) linorder_not_less by fastforce
  have empty_nin_M: "{} \<notin> M'"
    using assms(2,4) graph_abs_no_empty(1) by auto
  have finite_Vs_M': "finite (Vs M')"
    using assms(2,4) graph_abs.finite_Vs graph_abs_mono by auto
  have weight_split_M': "sum (mwmcpc G w) (extend_matching G M') = 
          2 * sum w M' + card (Vs G - Vs M') *4* penalty G w"
    using assms(2) graph_invar_G empty_nin_M
    by(intro weight_of_extend_matching_max_card)
      (auto simp add: finite_M' graph_invar_G)
  have weight_M'_bounds:
     "sum (mwmcpc G w) (extend_matching G M') <
            card (Vs G - Vs M') * 4*penalty G w + 2*penalty G w"
      "sum (mwmcpc G w) (extend_matching G M') >
              card (Vs G - Vs M') * 4*penalty G w - 2*penalty G w"
    using weight_of_matching_abs_less[OF graph_invar_G assms(2), of w] 
    by(auto simp add: weight_split_M')
  have finite_Vs_fst_M: "finite (Vs (get_fst_only M))"
    using graph_invar_G graph_invar_subset matching_fst by auto
  have "graph_abs (get_fst_only M)"
    using assms(4) graph_abs_mono matching_fst by auto
  moreover have "graph_abs M'"
    using assms(2,4) graph_abs_mono by auto
  ultimately have "card (Vs (get_fst_only M)) < card (Vs M')"
    using assms(2,3)
    by(simp add: graph_abs.matching_card_vs[symmetric] matching_fst)
  moreover have "card (Vs M') \<le> card (Vs G)" 
    by (simp add: Vs_subset assms(2) card_mono graph_invar_G)
  ultimately have unmatched_diff: "card (Vs G - Vs M') < card (Vs G - Vs (get_fst_only M))"
    by (simp add: card_Vs_diff[OF _ finite_Vs_M'] assms(2) card_Vs_diff finite_Vs_fst_M  matching_fst)
  hence upper_bound_leq_lower_bound:
        "card (Vs G - Vs M') * 4*penalty G w + 4 * penalty G w \<le>
                card (get_crossing M) *4* penalty G w "
  proof-
    have "card (Vs G - Vs M') * 4*penalty G w + 4 * penalty G w = 
          Suc (card (Vs G - Vs M')) * 4*penalty G w " 
     by (auto simp add: algebra_simps)
   moreover have  "... \<le> card (Vs G - Vs (get_fst_only M)) * 4*penalty G w" 
     using graph_invar_G graph_invar_finite penalty_gtr_0 unmatched_diff by fastforce
   ultimately show ?thesis
     by(simp add: card_crossing_M)
 qed
  show ?thesis
    using weight_M'_bounds(1) weight_M_bounds(2) unmatched_diff upper_bound_leq_lower_bound
    by(auto simp add: algebra_simps)
qed

lemma mwmcpc_in_two_cpys_ptwise_connected_fst_geq_snd:
  assumes "perfect_matching (two_cpys_ptwise_connected G) M"
           "sum w (get_fst_only M) < sum w (get_snd_only M)"
           "graph_abs G"
    shows  "sum (mwmcpc G w) (extend_matching G (get_fst_only M)) < sum (mwmcpc G w) M" (is ?th1)
           "perfect_matching (two_cpys_ptwise_connected G) 
                   (extend_matching G (get_fst_only M))" (is ?th2)
proof-
  note M_props = perfect_matchingD[OF assms(1)]
  have graph_abs_ext_G: "graph_abs (two_cpys_ptwise_connected G)"
    by (simp add: assms(3) graph_abs_two_copies)
  hence graph_abs_M:"graph_abs M" 
    using M_props(1) graph_abs_mono by auto
  have graph_invar_G: "graph_invar G"
    using assms(3) graph_abs_def by auto
  have finite_M: "finite M"
    using M_props(1) finite_subset graph_abs.finite_E graph_abs_ext_G by blast
  have empty_nin_M: "{} \<notin> M" 
    using graph_abs_M graph_abs_no_empty by auto
  have weight_split_M:
     "sum (mwmcpc G w) M = sum w (get_fst_only M) + sum w (get_snd_only M) +
          real (card (get_crossing M)) * 4*penalty G w"
    using weight_big_matching_split_max_card[of M]
    by(auto simp add: finite_M empty_nin_M)
  have matching_fst: "graph_matching G (get_fst_only M)"
    using M_props(1,2) get_fst_only_of_graph_matching by blast
  have extended_fst_weight_split:
    "sum (mwmcpc G w) (extend_matching G (get_fst_only M)) =
      2 * sum w (get_fst_only M) + real (card (Vs G - Vs (get_fst_only M)) * 4) * penalty G w"
    by(rule weight_of_extend_matching_max_card[of "get_fst_only M" G w])
      (auto simp add: finite_M get_fst_only_finite  graph_invar_G
             empty_nin_M get_fst_only_contains_empty)
  moreover have "card (get_crossing M) = card (Vs G - Vs (get_fst_only M))"
    by(auto intro!: card_crossing_is_card_unmatched_fst assms(1))
  ultimately show ?th1
    by (auto simp add: algebra_simps assms(2) weight_split_M)
  show ?th2
    by (simp add: matching_fst perfect_matching_extend_matching)
qed

lemma mwmcpc_in_two_cpys_ptwise_connected_fst_leq_snd:
  assumes "perfect_matching (two_cpys_ptwise_connected G) M"
           "sum w (get_fst_only M) > sum w (get_snd_only M)"
           "graph_abs G"
    shows  "sum (mwmcpc G w) (extend_matching G (get_snd_only M)) < sum (mwmcpc G w) M" (is ?th1)
           "perfect_matching (two_cpys_ptwise_connected G) 
                   (extend_matching G (get_snd_only M))" (is ?th2)
proof-
  note M_props = perfect_matchingD[OF assms(1)]
  have graph_abs_ext_G: "graph_abs (two_cpys_ptwise_connected G)"
    by (simp add: assms(3) graph_abs_two_copies)
  hence graph_abs_M:"graph_abs M" 
    using M_props(1) graph_abs_mono by auto
  have graph_invar_G: "graph_invar G"
    using assms(3) graph_abs_def by auto
  have finite_M: "finite M"
    using M_props(1) finite_subset graph_abs.finite_E graph_abs_ext_G by blast
  have empty_nin_M: "{} \<notin> M" 
    using graph_abs_M graph_abs_no_empty by auto
  have weight_split_M:
     "sum (mwmcpc G w) M = sum w (get_fst_only M) + sum w (get_snd_only M) +
          real (card (get_crossing M)) * 4*penalty G w"
    using weight_big_matching_split_max_card[of M]
    by(auto simp add: finite_M empty_nin_M)
  have matching_snd: "graph_matching G (get_snd_only M)"
    using M_props(1,2) get_snd_only_of_graph_matching by blast
  have extended_snd_weight_split:
    "sum (mwmcpc G w) (extend_matching G (get_snd_only M)) =
      2 * sum w (get_snd_only M) + real (card (Vs G - Vs (get_snd_only M)) * 4) * penalty G w"
    by(rule weight_of_extend_matching_max_card[of "get_snd_only M" G w])
      (auto simp add: finite_M get_snd_only_finite  graph_invar_G
             empty_nin_M get_snd_only_contains_empty)
  moreover have "card (get_crossing M) = card (Vs G - Vs (get_snd_only M))"
    by(auto intro!: card_crossing_is_card_unmatched_snd assms(1))
  ultimately show ?th1
    by (auto simp add: algebra_simps assms(2) weight_split_M)
  show ?th2
    by (simp add: matching_snd perfect_matching_extend_matching)
qed

theorem min_weight_max_card_to_min_weight_perfect_general:
  assumes "graph_abs G" 
          "min_weight_perfect_matching (two_cpys_ptwise_connected G) (mwmcpc G w) M"
  shows   "min_weight_max_card_matching G w (get_fst_only M)"
          "min_weight_max_card_matching G w (get_snd_only M)"
proof-
  note M_props = min_weight_perfect_matchingD[OF assms(2)]
                 perfect_matchingD(1,2)[OF min_weight_perfect_matchingD(1)[OF assms(2)]]
  have graph_matching_fst: "graph_matching G (get_fst_only M)"
    using M_props(3,4) get_fst_only_of_graph_matching by blast
  have graph_matching_snd: "graph_matching G (get_snd_only M)"
    using M_props(3,4) get_snd_only_of_graph_matching by blast
  have finite_M: "finite M" 
    using M_props(3) assms(1) finite_subset graph_abs.finite_E graph_abs_two_copies by blast
  have empty_nin_M: "{} \<notin> M" 
    using M_props(3) assms(1) graph_abs_no_empty(2) graph_abs_two_copies by auto
  have max_card_matching_fst: "max_card_matching G (get_fst_only M)"
  proof(rule ccontr, goal_cases)
    case 1
    then obtain M' where M':"card M' > card (get_fst_only M)" "graph_matching G M'"
      using graph_matching_fst linorder_not_less 
      by(auto simp add: max_card_matching_def)
    have "sum (mwmcpc G w) (extend_matching G M') < sum (mwmcpc G w) M"
      by(auto intro!: not_max_card_matching_not_min_weight_perfect M_props(1) M'(2,1) assms(1))
    moreover have "perfect_matching  (two_cpys_ptwise_connected G) (extend_matching G M')"
      by (simp add: M'(2) perfect_matching_extend_matching)
    ultimately have 
      "\<not> min_weight_perfect_matching (two_cpys_ptwise_connected G) (mwmcpc G w) M"
      by(auto simp add: min_weight_perfect_matching_def)
    thus False
      using assms(2) 
      by simp
  qed
  moreover have same_cards: "card (get_fst_only M) = card (get_snd_only M)"
    by(auto intro!: mwmcpc_in_two_cpys_ptwise_connected_fst_card_eq_snd_card assms(1) M_props(1))
  ultimately have max_card_matching_snd: "max_card_matching G (get_snd_only M)"
    using graph_matching_snd max_card_matching_cardI by auto
  have fst_snd_same_weight: "sum w  (get_fst_only M) = sum w  (get_snd_only M)"
  proof(rule ccontr, goal_cases)
    case 1
    hence  "\<not> min_weight_perfect_matching (two_cpys_ptwise_connected G) (mwmcpc G w) M"
      using mwmcpc_in_two_cpys_ptwise_connected_fst_leq_snd[OF M_props(1) _ assms(1), of w]
            mwmcpc_in_two_cpys_ptwise_connected_fst_geq_snd[OF M_props(1) _ assms(1), of w]
            M_props(1)
      by(fastforce simp add:  min_weight_perfect_matching_def)
    thus False
      using assms(2) by simp
  qed
  show fst_min_weight_max_card: 
     "min_weight_max_card_matching G w (get_fst_only M)"
  proof(rule ccontr, goal_cases)
    case 1
    then obtain M' where M':"max_card_matching G M'" "sum w M' < sum w (get_fst_only M)"
      using max_card_matching_fst 
      by(auto simp add: min_weight_max_card_matching_def)
    note M'_props = max_card_matchingD[OF M'(1)]
    have M'_more_props: "finite M'" "finite (Vs G)" "{} \<notin> M'" 
      using M'_props assms(1) finite_subset graph_abs.finite_E graph_abs_mono[OF assms(1)]
      by (auto simp add: graph_abs.finite_Vs intro!: graph_abs_no_empty(2)[of M'])
    have "sum (mwmcpc G w) (extend_matching G M') = 
          2 * sum w M' + real (card (Vs G - Vs M') * 4) * penalty G w"
      by(intro weight_of_extend_matching_max_card[of M' G w] M'_more_props)
    moreover have "card (Vs G - Vs M') = card (Vs G - Vs (get_fst_only M))"
      by(auto intro!: max_card_matchings_same_number_unmatched
            simp add: max_card_matching_fst M'(1) assms(1))
     moreover have weight_split_M:
     "sum (mwmcpc G w) M = sum w (get_fst_only M) + sum w (get_snd_only M) +
          real (card (get_crossing M)) * 4*penalty G w"
        using weight_big_matching_split_max_card[of M]
        by(auto simp add: finite_M empty_nin_M)
      moreover have "card (get_crossing M) =  card (Vs G - Vs (get_fst_only M))" 
        using M_props(1) card_crossing_is_card_unmatched_fst by blast
      ultimately have "sum (mwmcpc G w) (extend_matching G M') < sum (mwmcpc G w) M"
        using M'(2)
        by(auto simp add: fst_snd_same_weight same_cards)
      moreover have "perfect_matching (two_cpys_ptwise_connected G)(extend_matching G M')" 
        by (simp add: M'_props perfect_matching_extend_matching)
      ultimately have "\<not> min_weight_perfect_matching (two_cpys_ptwise_connected G) (mwmcpc G w) M"
        by(auto simp add: min_weight_perfect_matching_def)
      thus False
        using assms(2)
        by simp
    qed
    thus "min_weight_max_card_matching G w (get_snd_only M)"
      by (simp add: fst_snd_same_weight max_card_matching_snd min_weight_max_card_matching_def)
  qed

end