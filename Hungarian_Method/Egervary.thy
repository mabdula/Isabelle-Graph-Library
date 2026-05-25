theory Egervary
  imports Matching_LPs.Matching_LP Tutte_Theorem.Bipartite_Matchings_Existence
begin

section \<open>Egerváry's Theorem\<close>

text \<open>This is a formalisation of Egerváry's Theorem which inspired Kuhn for his Hungarian Method.
      We follow the proof by Schrijver (Theorem 17.1 in his book).\<close>

lemma PD_adjustment_max_weight:
  assumes  "feasible_max_dual V G w \<pi>" "\<not> (\<exists> e \<in> G. e \<subseteq> S)"
   and NS_def: "NS = Neighbourhood (tight_subgraph G w \<pi>) S"
   and eps_props: 
          "\<And> u v. {u, v} \<in> Delta (G - (tight_subgraph G w \<pi>)) S \<Longrightarrow> \<epsilon> \<le> \<pi> u + \<pi> v - w {u, v}"
          "\<And> v. v \<in> S \<Longrightarrow> \<epsilon> \<le> \<pi> v"
          "\<epsilon> \<ge> 0"
   and \<pi>'_def: "\<pi>' = (\<lambda> v. if v \<in> NS then \<pi> v + \<epsilon>
                           else if v \<in> S then  \<pi> v - \<epsilon>
                           else \<pi> v)"
   shows "feasible_max_dual V G w \<pi>'"
         "S \<subseteq> V \<Longrightarrow> sum \<pi>' V = sum \<pi> V + \<epsilon> * (real (card NS) - real (card S))"
proof-

  note pi_props = feasible_max_dualD[OF assms(1)]

  show "feasible_max_dual V G w \<pi>'"
  proof(rule feasible_max_dualI, goal_cases)
    case (1 v)
    show ?case 
      using assms(5,6)  pi_props(1)[OF 1]
      by(auto simp add: \<pi>'_def)
  next
    case (2 e u v)
    text \<open>The graph is partitioned in three sets of vertices: $S$, $NS$ and all other vertices.\<close>
    text \<open>If $e$ is within one of the three sets of vertices\<close>
    have case_1: "e \<subseteq> S \<Longrightarrow> False"
      using "2"(1) assms(2,3) by fastforce
    moreover have case_2: "e \<subseteq> NS \<Longrightarrow> ?case"
      using pi_props(2)[OF 2] eps_props(3)
      by(auto simp add: 2(2) NS_def \<pi>'_def)
    moreover have case_3: "\<lbrakk>e \<inter> S = {}; e \<inter> NS = {}\<rbrakk>  \<Longrightarrow> ?case"
      using 2(1) pi_props(2)[OF 2]
      by(auto simp add: 2(2) \<pi>'_def)
    text \<open>If $e$ is between the sets of vertices\<close>
    moreover have case_4: "\<lbrakk>e \<inter> S \<noteq> {}; e \<inter> NS \<noteq> {}\<rbrakk> \<Longrightarrow> ?case"
      using 2(1) pi_props(2)[OF 2] eps_props(3)
      by(auto simp add: 2(2) \<pi>'_def)
    moreover have case_5: "\<lbrakk>e \<inter> S \<noteq> {}; e \<inter> NS = {}\<rbrakk> \<Longrightarrow> ?case"
    proof(goal_cases)
      case 1
      note one = this
      hence "e \<in> Delta (G - (tight_subgraph G w \<pi>)) S"
      proof(cases "u \<in> S")
        case True
        have "e \<notin> tight_subgraph G w \<pi>"
        proof(rule ccontr, goal_cases)
          case 1
          hence "v \<in> Neighbourhood (tight_subgraph G w \<pi>) S"
            using case_1
            by(auto intro!: in_NeighbourhoodI[of u] simp add: 2(2) True)
          thus False
            using  one(2)
            by(auto simp add: "2"(2) NS_def)
        qed
        moreover have "v \<notin> NS"
          using  one(2) 
          by (auto simp add: "2"(2))
        moreover have "v \<notin> S" 
          using  True case_1 
          by(auto simp add: "2"(2))
        ultimately show ?thesis 
          by(auto intro!: in_DeltaI[OF 2(2) _ True] 2(1))
      next
        case False
        moreover hence v_in_S:"v \<in> S"
          using one(1)
          by(auto simp add: "2"(2))
        moreover have "e \<notin> tight_subgraph G w \<pi>"
        proof(rule ccontr, goal_cases)
          case 1
          hence "u \<in> Neighbourhood (tight_subgraph G w \<pi>) S"
            using case_1
            by(auto intro!: in_NeighbourhoodI[of v] simp add: 2(2) v_in_S insert_commute)
          thus False
            using  one(2)
            by(auto simp add: "2"(2) NS_def)
        qed
        ultimately show ?thesis 
          using 2(2,1)
          by(auto intro!: in_DeltaI[OF _ _ v_in_S] simp add: insert_commute)
      qed
      then show ?thesis 
        using one case_1 eps_props(1)[of u v]
        by(auto simp add: 2(2) \<pi>'_def)
    qed
    moreover have case_6: "\<lbrakk>e \<inter> S = {}; e \<inter> NS \<noteq> {}\<rbrakk> \<Longrightarrow> ?case"
      using eps_props(3) pi_props(2)[OF 2]
      by(auto simp add: 2(2) \<pi>'_def)
    ultimately show ?case
      by auto
  qed (simp_all add: pi_props)
  show  "sum \<pi>' V = sum \<pi> V + \<epsilon> * (real (card NS) - real (card S))"
    if asm: "S \<subseteq> V"
  proof-
    have NS_in_V_without_S: "NS \<subseteq> V - S"
      using pi_props(3) asm  Neighbourhood_in_G Vs_subset[OF tight_subgraph_is_subgraph]
      by(force simp add: NS_def self_not_in_Neighbourhood)
    have x_in_S_not_in_NS: "x \<in> S \<Longrightarrow> x \<notin> NS" for x
      by (simp add: NS_def self_not_in_Neighbourhood)
    have split1: "sum p V = sum p (V - S) + sum p S" for p
      using asm pi_props(4)
      by(auto intro!: comm_monoid_add_class.sum.subset_diff)
    have split2: "sum p (V - S) = sum p (V - S - NS) + sum p NS" for p
      using NS_in_V_without_S pi_props(4)
      by(auto intro!: comm_monoid_add_class.sum.subset_diff)
    have "sum \<pi>' S = sum \<pi> S - \<epsilon> * real (card S) "
      using x_in_S_not_in_NS
      by(auto simp add: \<pi>'_def sum_subtractf)
    moreover have "sum \<pi>' NS = sum \<pi> NS + \<epsilon> * real (card NS) "
      by(auto simp add: \<pi>'_def sum.distrib)
    moreover have "sum \<pi>' (V - S - NS) = sum \<pi> (V - S - NS)"
      by(auto simp add: \<pi>'_def)
    ultimately show ?thesis
      by(unfold split1 split2) argo
  qed
qed

theorem egervary:
  assumes "bipartite G L R" "graph_invar G"
          "max_weight_matching G w M" "min_feasible_max_dual (L \<union> R) G w \<pi>"
    shows "sum w M = sum \<pi> (L \<union> R)"
proof-
  note M_props = max_weight_matchingD[OF assms(3)]
  note pi_props = min_feasible_max_dualD[OF assms(4)]
  note pi_props' = feasible_max_dualD[OF pi_props(1)]

  show ?thesis
  proof(cases "\<exists> M'. cover_matching (tight_subgraph G w \<pi>) M' (non_zero_vertices (L \<union> R) \<pi>)")
    case True
    then obtain M' where "cover_matching (tight_subgraph G w \<pi>) M' (non_zero_vertices (L \<union> R) \<pi>)"
      by auto
    hence M': "graph_matching (tight_subgraph G w \<pi>) M'" "non_zero_vertices (L \<union> R) \<pi> \<subseteq> Vs M'"
      by (auto elim!: cover_matchingE)
    hence "max_weight_matching G w M'" "sum w M' = sum \<pi> (L \<union> R)"
      using pi_props assms(2) tight_subgraph_is_subgraph[of G w \<pi>]
       by(auto intro!: max_weight_if_tight_matching_covers_bads)
     then show ?thesis 
       using M_props(1,2) nle_le[of "sum w M'" "sum w M"] 
       by(force elim!: max_weight_matchingE)
  next
    case False
    moreover have "non_zero_vertices (L \<union> R) \<pi> \<subseteq> L \<union> R"
      by(auto elim!: in_non_zero_verticesE)
    moreover have "graph_invar (tight_subgraph G w \<pi>)"
      using  assms(2)
      by(intro graph_invar_subgraph[OF _ tight_subgraph_is_subgraph]) auto
    moreover have "bipartite (tight_subgraph G w \<pi>) L R"
      using assms(1) bipartite_subgraph tight_subgraph_is_subgraph by blast
    ultimately obtain S where S:
       "S \<subseteq> L \<inter> non_zero_vertices (L \<union> R) \<pi> \<or> S \<subseteq> R \<inter> non_zero_vertices (L \<union> R) \<pi>"
       "card S > card (Neighbourhood (tight_subgraph G w \<pi>) S)"
      using linorder_not_le 
      by(auto simp add: schrijver_corollary_16_8a_standard_bipartite) 
    have finite_S:"finite S" and S_non_empty: "S \<noteq> {}"
      using S(2) card.infinite by force+
    define \<epsilon>  where 
      "\<epsilon> = Min ({ \<pi> u + \<pi> v - w {u, v} | u v. {u, v} \<in> Delta (G - tight_subgraph G w \<pi>) S}
             \<union> {\<pi> v | v. v \<in> S}) "
    define \<pi>' where "\<pi>' = (\<lambda>v. if v \<in> Neighbourhood (tight_subgraph G w \<pi>) S then \<pi> v + \<epsilon>
                               else if v \<in> S then \<pi> v - \<epsilon> else \<pi> v)"
    have "\<not> (\<exists>e\<in>G. e \<subseteq> S)"
    proof(rule ccontr, goal_cases)
      case 1
      then obtain e where "e \<in> G" "e \<subseteq> L \<or> e \<subseteq> R"
        using S by auto
      moreover then obtain u v where "e = {u, v}"
        using assms(2) by blast
      ultimately show False
        using bipartite_edgeD(1,4)[OF _ assms(1)]
        by auto
    qed
    moreover have eps_props:
      "{u, v} \<in> Delta (G - tight_subgraph G w \<pi>) S \<Longrightarrow> \<epsilon> \<le> \<pi> u + \<pi> v - w {u, v}"
      "v \<in> S \<Longrightarrow> \<epsilon> \<le> \<pi> v"
      "0 \<le> \<epsilon>" for u v
      using assms(2) finite_S S_non_empty S(1)
      by(auto intro!: linorder_class.Min.coboundedI finite_image_of_unordered_pairs Delta_finite
                      linorder_class.Min.boundedI pi_props'(1,2)
                elim: in_DeltaE
            simp add: \<epsilon>_def finite_Vs_then_finite doubleton_eq_iff)
    ultimately have adjustment: "feasible_max_dual (L \<union> R) G w \<pi>'"
       "sum \<pi>' (L \<union> R) = sum \<pi> (L \<union> R) 
           + \<epsilon> * (real (card (Neighbourhood (tight_subgraph G w \<pi>) S)) - real (card S))"
      using S(1)
       by(all \<open>intro PD_adjustment_max_weight[OF pi_props(1), of S, OF _ refl, of \<epsilon> \<pi>']\<close>)
         (auto simp add: \<pi>'_def)
     moreover have "0 < \<epsilon>"
       unfolding \<epsilon>_def
     proof(rule iffD2[OF linorder_class.Min_gr_iff, OF _ _ ballI], goal_cases)
       case 1
       then show ?case 
        by (auto intro!: finite_image_of_unordered_pairs Delta_finite
                 simp add: assms(2) finite_Vs_then_finite finite_S)
     next
       case 2
       then show ?case 
         using S_non_empty
         by (auto intro!: finite_image_of_unordered_pairs Delta_finite
               elim!: in_DeltaE in_non_zero_verticesE[OF  subsetD])
     next
       case (3 wpi)
       show ?case
       proof(cases rule: UnE[OF 3])
         case 1
         then obtain u v where uv:"wpi = \<pi> u + \<pi> v - w {u, v}"
                  "{u, v} \<in> Delta (G - tight_subgraph G w \<pi>) S"
           by auto
         then show ?thesis 
           using pi_props'(2)[OF _ refl, of u v]
           by (auto elim!: in_DeltaE simp add: doubleton_eq_iff tight_subgraph_def)+      
       next
         case 2
         then obtain v where "wpi = \<pi> v" "v \<in> S"
           by auto
         then show ?thesis 
           using S(1) pi_props'(1)[of v]
           by(auto elim!: in_non_zero_verticesE)
       qed
     qed
     ultimately have "sum \<pi>' (L \<union> R) <  sum \<pi> (L \<union> R)"
       by (auto simp add: S(2) mult_less_0_iff)
     hence False 
       using adjustment(1) pi_props(2) 
       by force
     then show ?thesis 
       by simp
  qed
qed

subsection \<open>König's Theorem\<close>

text \<open>We also formally prove the unweighted version, König's Theorem.\<close>

definition "vertex_cover G X = ((X \<subseteq> Vs G) \<and> (\<forall> e \<in> G. \<exists> x \<in> X. x \<in> e))"

lemma vertex_coverI: 
  "\<lbrakk>X \<subseteq> Vs G; \<And> e. e \<in> G \<Longrightarrow> \<exists> x \<in> X. x \<in> e\<rbrakk> \<Longrightarrow> vertex_cover G X"
and vertex_coverE: 
  "\<lbrakk>vertex_cover G X; \<lbrakk>X \<subseteq> Vs G; \<And> e. e \<in> G \<Longrightarrow> \<exists> x \<in> X. x \<in> e\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
and vertex_coverD: 
  "vertex_cover G X \<Longrightarrow> X \<subseteq> Vs G"
  "\<lbrakk>vertex_cover G X; e \<in> G\<rbrakk> \<Longrightarrow>  \<exists> x \<in> X. x \<in> e"
  by(auto simp add: vertex_cover_def)

definition "min_vertex_cover G X =
   (vertex_cover G X \<and> (\<forall> X'. vertex_cover G X' \<longrightarrow> card X' \<ge> card X))"

lemma min_vertex_coverI:
  "\<lbrakk>vertex_cover G X; \<And> X'. vertex_cover G X' \<Longrightarrow> card X' \<ge> card X\<rbrakk> \<Longrightarrow> min_vertex_cover G X"
and min_vertex_coverE:
  "\<lbrakk>min_vertex_cover G X; 
    \<lbrakk>vertex_cover G X; \<And> X'. vertex_cover G X' \<Longrightarrow> card X' \<ge> card X\<rbrakk> \<Longrightarrow>P\<rbrakk>\<Longrightarrow>P"
and min_vertex_coverD:
  "min_vertex_cover G X \<Longrightarrow> vertex_cover G X"
  "\<lbrakk>min_vertex_cover G X; vertex_cover G X'\<rbrakk> \<Longrightarrow> card X' \<ge> card X"
  by(auto simp add: min_vertex_cover_def)

lemma vertex_cover_full: "{} \<notin> G \<Longrightarrow> vertex_cover G (Vs G)"
proof(rule vertex_coverI, goal_cases)
  case (2 e)
  moreover then obtain x where "x \<in> e"
    by fastforce
  ultimately show ?case 
    by auto
qed simp

lemma finite_number_of_covers: "finite (Vs G) \<Longrightarrow> finite {X | X. vertex_cover G X}"
  by(auto intro!: finite_subset[of _ "Pow (Vs G)"] simp add: vertex_cover_def)

definition "\<tau> G = Min {card X | X. vertex_cover G X}"

lemmas tau_def = \<tau>_def

lemma min_cover_is_\<tau>: "\<lbrakk>finite (Vs G); min_vertex_cover G X\<rbrakk> \<Longrightarrow> card X = \<tau> G"
  unfolding tau_def
  by(subst linorder_class.eq_Min_iff)
    (auto simp add: image_Collect[symmetric] min_vertex_coverD(1,2)
            intro!: finite_imageI finite_number_of_covers[simplified] exI[of _ "X"]
              dest: min_vertex_coverD)

lemma min_vertex_cover_exists:
  assumes "finite (Vs G)" "{} \<notin> G"
  obtains X where "min_vertex_cover G X"
  apply(rule  minimiser_of_function_nempty_finite[of "Collect (vertex_cover G)" card])
  using finite_number_of_covers[OF assms(1)]  assms(2)
  by(auto intro!: vertex_cover_full simp add: min_vertex_cover_def)

corollary max_matching_min_cover_weak_duality:
  assumes  "graph_invar G" "graph_matching G M" "vertex_cover G X" "finite X"
   shows   "card M \<le> card X"
proof-
  have real_leq_cong: "(real n \<le> real m) = (n \<le> m)" for n m by auto
  have "(\<Sum>e\<in>M. (1::real)) \<le> (\<Sum>x\<in>Vs G. if x \<in> X then 1 else 0)"
    using assms(3,1) 
    by(intro max_matching_weak_duality[OF _ assms(2,1)])
      (auto intro!: feasible_max_dualI dest: vertex_coverD)
  also have "... = card (X \<inter> Vs G)"
    using assms(1)
    by(subst comm_monoid_add_class.sum.inter_filter[symmetric])
      (auto intro!: arg_cong[of  _ _ card])
  also have "... \<le> card X"
    by (simp add: assms(4) card_mono)
  finally show ?thesis
    by simp
qed

corollary max_matching_min_cover_duality_criterion:
  assumes  "graph_invar G" "graph_matching G M" "vertex_cover G X" "finite (Vs G)"
           "card M = card X"
     shows "max_card_matching G M" "min_vertex_cover G X"
  using assms  max_matching_min_cover_weak_duality[OF assms(1)]
        finite_subset[of X "Vs G"] vertex_coverD(1) rev_finite_subset
  by(fastforce intro!: max_card_matchingI' min_vertex_coverI
                dest!: max_matching_min_cover_weak_duality)+

theorem koenig:
  assumes "bipartite G L R" "graph_invar G"
  shows "\<nu> G = \<tau> G"
proof-

  obtain M where M: "max_card_matching G M"
    using assms(2) finite_Vs_then_finite max_card_matching_exists by auto
  obtain X where X: "min_vertex_cover G X" 
    using assms(2)
    by(auto intro: min_vertex_cover_exists[of G])

  note assms = assms M X

  note M_props = max_card_matchingDs[OF assms(3)]
  note X_props = min_vertex_coverD[OF assms(4)]
  note X_props' = vertex_coverD[OF X_props(1)]

  have X_in_G: "X \<subseteq> Vs G"
    by (simp add: X_props'(1))

  show ?thesis
  proof(cases "\<exists> M. cover_matching {e | e. e \<in> G \<and> (\<exists> x. e \<inter> X = {x})} M X")
    case True
    then obtain M' where M': "cover_matching {e | e. e \<in> G \<and> (\<exists> x. e \<inter> X = {x})} M' X"
      by auto
    note M'_props = cover_matchingD[OF M']
    define f where "f = (\<lambda> e. SOME x. e \<inter> X = {x})"
    have "card M' = card X"
    proof(rule bij_betw_same_card[of f], goal_cases)
      case 1
      have "inj_on f M'"
      proof(rule  inj_onI, goal_cases)
        case (1 e e')
        then obtain x x' where xx':  "e \<inter> X = {x}" "e' \<inter> X = {x'}"
          using M'_props(2) by force
        moreover have "f e = x" "f e' = x'"
          by (simp add: f_def xx')+
        ultimately have "x = x'" 
          using 1 by auto
        hence "e \<inter> e' \<noteq> {}"
          using xx' by auto
        thus ?case
          using "1"(1,2) M'_props(1)
          by(auto elim!: matchingE)
      qed
      moreover have "f ` M' = X"
      proof(rule, all \<open>rule\<close>, goal_cases)
        case (1 x)
        then obtain e where e: "e \<in> M'" "f e = x"
          by auto
        then obtain x' where x': "e \<inter> X = {x'}"
          using M'_props(2)  by auto
        moreover hence "f e = x'"
          by(auto simp add: f_def)
        ultimately show ?case 
          using e by auto
      next
        case (2 x)
        then obtain e where e: "e \<in> M'" "x \<in> e"
          using M'_props(3)  vs_member[of x M'] by auto
        moreover then obtain x' where "e \<inter> X = {x'}"
          using M'_props(2) 2 by auto
        ultimately have "e \<inter> X = {x}"
          using 2 by auto
        hence "f e = x"
          by(auto simp add: f_def)
        then show ?case 
          using e by auto
      qed
      ultimately show ?case 
        by(simp add: bij_betw_def)
    qed
    moreover hence "max_card_matching G M'"
      using assms(2) M'_props X_props X_in_G
      by(auto intro!: max_matching_min_cover_duality_criterion(1) intro: finite_subset)
    moreover hence "card M = card M'"
      using assms(3) max_card_matchings_same_size by auto
    ultimately show ?thesis 
      using  assms(2,4) finite_Vs_then_finite max_matching_is_\<nu>[of G] min_cover_is_\<tau>[of G]
      by force
  next
    case False
    moreover have "bipartite {e |e. e \<in> G \<and> (\<exists>x. e \<inter> X = {x})} L R"
      using assms(1) bipartite_subgraph by fastforce
    moreover have graph_inv_G':"graph_invar {e |e. e \<in> G \<and> (\<exists>x. e \<inter> X = {x})}"
      by(auto intro!: graph_invar_subgraph[OF  assms(2)])
    moreover have "X \<subseteq> L \<union> R"
      using X_in_G assms(1) bipartite_vs_subset by blast
    ultimately obtain S where S: "S \<subseteq> L \<inter> X \<or> S \<subseteq> R \<inter> X"
      "card S > card (Neighbourhood {e |e. e \<in> G \<and> (\<exists>x. e \<inter> X = {x})} S)"
      using schrijver_corollary_16_8a_standard_bipartite[of
          "{e |e. e \<in> G \<and> (\<exists>x. e \<inter> X = {x})}" L R X] 
      by force
    have "vertex_cover G (X - S \<union> Neighbourhood {e |e. e \<in> G \<and> (\<exists>x. e \<inter> X = {x})} S)"
    proof(rule vertex_coverI, goal_cases)
      case (2 e)
      then obtain x where x: "x \<in> X" "x \<in> e"
        using X_props' by blast
      show ?case 
      proof(cases "x \<in> S")
        case True
        obtain y where y: "e = {x, y}"
          using 2 assms(2) x(2) by blast
        have y_not_in_S: "y \<notin> S" 
          using 2 S(1) True assms(1) bipartite_edgeD(1,2) y by fastforce
        show ?thesis
        proof(cases "y \<in> X")
          case True
          moreover hence "y \<notin> Neighbourhood {e |e. e \<in> G \<and> (\<exists>x. e \<inter> X = {x})} S"
            using y S(1)
            by(auto elim!: in_NeighbourhoodE)
          ultimately show ?thesis 
            using y_not_in_S y by auto
        next
          case False
          hence "e \<inter> X = {x}"
            using y x by auto
          hence "y \<in> Neighbourhood {e |e. e \<in> G \<and> (\<exists>x. e \<inter> X = {x})} S"
            using 2 True S(1) y  y_not_in_S
            by(auto intro!: in_NeighbourhoodI[of x y _ S] exI[of _ x])
          then show ?thesis 
            using y by auto
        qed
      next
        case False
        then show ?thesis 
          using x by auto
      qed
    next
      case 1
      thus ?case
        using X_in_G
        by (auto elim!: in_NeighbourhoodE)
    qed
    moreover have  "card (X - S \<union> Neighbourhood {e |e. e \<in> G \<and> (\<exists>x. e \<inter> X = {x})} S) < card X"
    proof(subst card_Un_disjoint, goal_cases)
      case 1
      then show ?case 
        using  X_in_G assms(2)
        by (simp add: finite_subset)
    next
      case 2
      then show ?case 
        using Neighbourhood_in_G graph_inv_G' finite_subset
        by fastforce
    next
      case 3
      then show ?case 
        using S(1)
        by (auto elim!: in_NeighbourhoodE)
    next
      case 4
      then show ?case 
        using S card.infinite[] X_in_G infinite_super assms(2) card_mono [of X "S"]
        by(subst card_Diff_subset) fastforce+
    qed
    ultimately have False 
      using X_props(2) by force
    then show ?thesis 
      by simp
  qed
qed

end