theory Partition_Quotient_Graph
  imports Basic_Matching.Matching
begin

section \<open>Quotienting Graphs by a Partition\<close>

text \<open>We can partition a graph's vertices into equivalence classes.
      From that we can define a graph whose vertices are sets.
      This is similar to quotienting for the unweighted blossom algorithm, but:
      1. several vertices might be contracted at once 
      2. the vertices in the contracted graph have a new type.
      Since we here formalise the outline in Korte's and Vygen's book,
      we take a more abstract perspective.\<close>

subsection \<open>More about Partitions\<close>

definition "prepartition_on A P \<longleftrightarrow> \<Union>P \<supseteq> A \<and> disjoint P \<and> {} \<notin> P"

lemma prepartition_onI:
  "\<lbrakk>\<Union>P \<supseteq> A; \<And>p q. \<lbrakk>p \<in> P; q \<in> P; p \<noteq> q\<rbrakk> \<Longrightarrow> disjnt p q; {} \<notin> P\<rbrakk> \<Longrightarrow> prepartition_on A P"
  by (auto simp: prepartition_on_def pairwise_def)

lemma prepartition_onD1: "prepartition_on A P \<Longrightarrow> A \<subseteq> \<Union>P"
  by (auto simp: prepartition_on_def)

lemma prepartition_onD2: "prepartition_on A P \<Longrightarrow> disjoint P"
  by (auto simp: prepartition_on_def)

lemma prepartition_onD3: "prepartition_on A P \<Longrightarrow> {} \<notin> P"
  by (auto simp: prepartition_on_def)

lemma prepartition_on_eq_if_inter_nempty:
  "\<lbrakk>prepartition_on U \<P>; X \<in> \<P>; Y \<in> \<P>; X \<inter> Y \<noteq> {}\<rbrakk> \<Longrightarrow> X = Y"
  by(auto simp add: prepartition_on_def disjoint_def)

lemma partition_on_implies_prepartition_on:
 "partition_on U \<P> \<Longrightarrow> prepartition_on U \<P>"
  by(auto simp add: partition_on_def prepartition_on_def)

lemma partition_of_prepartition_is_prepartition:
  assumes "prepartition_on U \<P>" "X \<in> \<P>" "partition_on X \<P>'"
  shows "prepartition_on U (\<P> - {X} \<union> \<P>')"
proof(rule prepartition_onI, goal_cases)
  case 1
  then show ?case 
    using assms(1,2,3) by(auto simp add:  prepartition_on_def partition_on_def) 
next
  case (2 A B)
  then show ?case 
  proof(elim UnE, goal_cases)
    case 1
    then show ?case 
      using assms(1) 
      by(auto simp add: prepartition_on_def disjnt_def disjoint_def)
  next
    case 2
    show ?case
    proof(rule ccontr, goal_cases)
      case 1
      hence "\<not> disjnt A X"
        using "2"(3) assms(3) partition_onD1 by fastforce
      then show ?case
        using 2(2) assms(1,2) 
        by(auto simp add: prepartition_on_def disjoint_def disjnt_def)
    qed
  next
    case 3
    show ?case
    proof(rule ccontr, goal_cases)
      case 1
      hence " \<not> disjnt B X"
        using "3"(2) assms(3) disjnt_sym partition_onD1 by fastforce
      then show ?case
        using 3(3) assms(1,2) 
        by(auto simp add: partition_on_def disjoint_def disjnt_def prepartition_on_def)
    qed
  next
    case 4
    then show ?case 
      using assms(3) 
      by(auto simp add: partition_on_def disjnt_def disjoint_def)
  qed
next
  case 3
  then show ?case
   using assms(1,3) by(auto simp add:  partition_on_def prepartition_on_def)
qed

lemma partition_of_partition_is_partition:
  assumes "partition_on U \<P>" "X \<in> \<P>" "partition_on X \<P>'"
  shows "partition_on U (\<P> - {X} \<union> \<P>')"
proof(rule partition_onI, goal_cases)
  case 1
  then show ?case 
    using assms(1,2,3) by(auto simp add:  partition_on_def)
next
  case (2 A B)
  then show ?case 
  proof(elim UnE, goal_cases)
    case 1
    then show ?case 
      using assms(1) 
      by(auto simp add: partition_on_def disjnt_def disjoint_def)
  next
    case 2
    show ?case
    proof(rule ccontr, goal_cases)
      case 1
      hence " \<not> disjnt A X"
        using "2"(3) assms(3) partition_onD1 by fastforce
      then show ?case
        using 2(2) assms(1,2) 
        by(auto simp add: partition_on_def disjoint_def disjnt_def)
    qed
  next
    case 3
    show ?case
    proof(rule ccontr, goal_cases)
      case 1
      hence " \<not> disjnt B X"
        using "3"(2) assms(3) disjnt_sym partition_onD1 by fastforce
      then show ?case
        using 3(3) assms(1,2) 
        by(auto simp add: partition_on_def disjoint_def disjnt_def)
    qed
  next
    case 4
    then show ?case 
      using assms(3) 
      by(auto simp add: partition_on_def disjnt_def disjoint_def)
  qed
next
  case 3
  then show ?case
   using assms(1,3) by(auto simp add:  partition_on_def)
qed

lemma partition_on_eq_if_inter_nempty:
  "\<lbrakk>partition_on U \<P>; X \<in> \<P>; Y \<in> \<P>; X \<inter> Y \<noteq> {}\<rbrakk> \<Longrightarrow> X = Y"
  by(auto simp add: partition_on_def disjoint_def)

subsection \<open>The Graph\<close>

definition "partition_quotient_graph E \<P>= 
  {{X, Y} | X Y. X \<in> \<P> \<and> Y \<in> \<P> \<and> X \<noteq> Y \<and> (\<exists> e \<in> E. X \<inter> e \<noteq> {} \<and> Y \<inter> e \<noteq> {})}"

notation partition_quotient_graph ("_ \<sslash> _" 100)

lemma in_partition_quotient_graphE:
"\<lbrakk>e \<in> E \<sslash> \<P>;
  \<And> ee X Y. \<lbrakk>X \<in> \<P>; Y \<in> \<P>; X \<noteq> Y; ee \<in> E; X \<inter> ee \<noteq> {}; Y \<inter> ee \<noteq> {}; e= {X, Y}\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto simp add: partition_quotient_graph_def)

lemma partition_quotient_graphI: 
  "\<lbrakk>X \<in> \<P>; Y \<in> \<P>; X \<noteq> Y; e \<in> E; X \<inter> e \<noteq> {}; Y \<inter> e \<noteq> {}\<rbrakk> \<Longrightarrow> {X, Y} \<in> partition_quotient_graph E \<P>"
and partition_quotient_graphE:  
  "\<lbrakk>e' \<in> partition_quotient_graph E \<P>; 
    \<And>X Y e. \<lbrakk>e' = {X, Y}; X \<in> \<P>; Y \<in> \<P>; X \<noteq> Y; e \<in> E; X \<inter> e \<noteq> {}; Y \<inter> e \<noteq> {}\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
and  partition_quotient_graphD: 
  "e' \<in> partition_quotient_graph E \<P>\<Longrightarrow> 
     \<exists>X Y e. e' = {X, Y} \<and> X \<in> \<P> \<and> Y \<in> \<P> \<and> X \<noteq> Y \<and> e \<in> E \<and> X \<inter> e \<noteq> {} \<and> Y \<inter> e \<noteq> {}"  
  unfolding partition_quotient_graph_def by auto

lemma partition_quotient_graph_is_dblton:
  "dblton_graph (partition_quotient_graph E \<P>)"
  by(auto simp add: partition_quotient_graph_def dblton_graph_def)

lemma partition_quotient_graph_graph_invar:
  "\<lbrakk>finite X; partition_on X \<P>\<rbrakk> \<Longrightarrow> graph_invar (partition_quotient_graph E \<P>)"
  by(auto intro!: finite_dblton_finite_Vs  rev_finite_subset[OF finite_unordered_pairs, of \<P>]
           intro:  finite_elements
        simp add: partition_quotient_graph_def dblton_graph_def)

lemma Vs_partition_quotient_graph:"Vs (partition_quotient_graph E \<P>) \<subseteq> \<P>"
  by(auto simp add: partition_quotient_graph_def vs_member)

lemma prepartition_quotient_graph_verts_by_Delta:
  assumes "prepartition_on (Vs E) \<P>" "dblton_graph E"
  shows "Vs (partition_quotient_graph E \<P>) = {X | X e. X \<in> \<P> \<and> e \<in> Delta E X}"
proof(rule, all \<open>rule\<close>, goal_cases)
  case (1 X)
  then obtain e Y where eY: "X \<in> \<P>" "Y \<in> \<P>" "X \<noteq> Y" "e \<in> E" "X \<inter> e \<noteq> {}" "Y \<inter> e \<noteq> {}"
    by(auto simp add: partition_quotient_graph_def vs_member)
  moreover then obtain u v where uv: "e = {u, v}" "u \<noteq> v"
    using assms(2) by blast
  moreover have uXvX:"u \<in> X \<and> v \<notin> X \<or> v \<in> X \<and> u \<notin> X"
    using assms(1) eY(1,2,3,5,6)  uv(1) by(force simp add: prepartition_on_def disjoint_def)
  moreover hence "e \<in> Delta E X"
    using eY(4)
    by(auto intro: exI[of _ v]simp add: Delta_def uv doubleton_eq_iff insert_commute)
  ultimately show ?case
    by auto
next
  case (2 X)
  then obtain e where e: "X \<in> \<P>" "e \<in> Delta E X"
    by auto
  moreover then obtain u v where uv: "e = {u, v}" "u \<noteq> v" "e \<in> E"
    by (auto elim!: in_DeltaE)
  moreover then obtain u v where "e = {u, v}" "u \<noteq> v" "e \<in> E" "u \<in> X" "v \<notin> X"
    using e by(auto simp add: Delta_def)
  moreover then obtain Y where "Y \<in> \<P>" "v \<in> Y" 
    using assms(1)
    by(auto simp add: insert_commute prepartition_on_def vs_member) blast
  ultimately have "{X, Y} \<in> partition_quotient_graph E \<P>"
    by(auto intro!: partition_quotient_graphI[of X _ Y e])
  then show ?case 
    by auto
qed

lemmas partition_quotient_graph_verts_by_Delta=
  prepartition_quotient_graph_verts_by_Delta[OF partition_on_implies_prepartition_on]

lemma partition_quotient_graph_inter_Vs_commute:
  assumes "X \<subseteq> \<P>" "dblton_graph G" "disjoint \<P>"
  shows"(G \<sslash> \<P>) \<lbrakk>X\<rbrakk> = G \<lbrakk>\<Union> X\<rbrakk> \<sslash> X"
proof(rule, all \<open>rule\<close>, goal_cases)
  case (1 e)
  then obtain X1 X2 where X1X2:"{X1, X2} \<in> G \<sslash> \<P>" "e = {X1, X2}" "X1 \<in> X" "X2 \<in> X"
    using partition_quotient_graphD[of e G \<P>]
    by(auto  simp add: graph_inter_Vs_def)
  then obtain ee where ee: "X1 \<in> \<P>" "X2 \<in> \<P>" "X1 \<noteq> X2 " "ee \<in> G" "X1 \<inter> ee \<noteq> {}" "X2 \<inter> ee \<noteq> {}"
    by(auto simp add: partition_quotient_graph_def doubleton_eq_iff)
  then obtain x1 x2 where x1x2: "ee = {x1, x2}" "x1 \<noteq> x2"
    using assms(2) by(auto elim!: dblton_graphE)
  have "x1 \<in> X1 \<and> x2 \<in> X2 \<or> x1 \<in> X2 \<and> x2 \<in> X1"
    using ee(1,2,3,5,6) assms(3) x1x2(1)
    by(auto dest:  disjointD)
  hence "ee \<in> G \<lbrakk>\<Union> X\<rbrakk>"
    using ee(4-) X1X2(3-) x1x2
    by(auto simp add: graph_inter_Vs_def)
  then show ?case 
    using X1X2(2,3,4) ee(3,5,6)
    by(auto intro!: exI[of _ X1, OF exI[of _ X2]] bexI[of _ ee]
          simp add: partition_quotient_graph_def)
next
  case (2 x)
  then show ?case 
    using assms(1)
    by(auto simp add: partition_quotient_graph_def graph_inter_Vs_def)
qed

lemma edge_in_quot_remove_irrelevant_areas:
  assumes "\<And> YY. YY \<in> Y \<Longrightarrow> e \<inter> Y = {}"
  shows "e \<in> G \<sslash> (X -Y) \<longleftrightarrow> e \<in> G \<sslash> X"
  using assms
  by(auto simp add: partition_quotient_graph_def) blast+

lemma partition_quotient_graph_Vs_inter_intersection:
  "(G \<sslash> X) \<lbrakk>Y\<rbrakk> = G \<sslash> (X \<inter> Y)"
proof(rule, all \<open>rule\<close>, goal_cases)
  case (1 e)
  then show ?case
  proof(elim in_graph_inter_VsE in_partition_quotient_graphE, goal_cases)
    case (1 ee x y)
    then show ?case 
      by(auto intro!: exI[of _ x, OF exI[of _ y]] simp add: partition_quotient_graph_def)
  qed
next
  case (2 e)
  then show ?case
  proof(rule in_partition_quotient_graphE, goal_cases)
    case (1 ee X Y)
    note one = this
    then show ?case
      by(auto intro!:  in_graph_inter_VsI exI[of _ X, OF exI[of _ Y]] 
              simp add: partition_quotient_graph_def)
  qed
qed

lemma partition_quotient_matching_refine_factor_critical:
  assumes "dblton_graph E" "prepartition_on (Vs E) \<P>" "partition_on X \<P>\<^sub>X"
          "perfect_matching (partition_quotient_graph E \<P>) M"
          "{Y, X} \<in> M"  "X' \<in> \<P>\<^sub>X"
          "x \<in> X'" "y \<in> Y" "{x, y} \<in> E"
          "graph_matching (partition_quotient_graph (graph_inter_Vs E X) \<P>\<^sub>X  \<setminus> {X'}) M'"
          "Vs  M' = \<P>\<^sub>X - {X'}"
    shows "perfect_matching (partition_quotient_graph E (\<P> - {X} \<union> \<P>\<^sub>X)) 
                   (M - {{Y, X}} \<union> {{Y, X'}} \<union> M')"
proof-
  obtain e where e_def:"e = {x, y}"
    by auto
   have e: "e\<in>E" "X \<inter> e \<noteq> {}" "Y \<inter> e \<noteq> {}" "X \<in> \<P>" "Y \<in> \<P>" "X \<noteq> Y"
     using assms(3,4,5,6,7,8) Vs_partition_quotient_graph[of E \<P>]
            partition_quotient_graphD[of "{X, Y}" E \<P>]
     by (auto elim!: perfect_matchingE 
           simp add: assms(9) e_def partition_on_def edges_are_Vs_2  edges_are_Vs subsetD
              dest!: perfect_matching_subgraphD) 
   
  hence XY: "X \<inter> Y = {}" "X \<noteq> {}" "Y \<noteq> {}"
    using assms(2) by(auto simp add: prepartition_on_def disjoint_def)
  hence xy: "x \<in> X" "y\<in> Y" "{x, y} = e" "x \<noteq> y"
    using assms(1,3,6,7) partition_onD1 e(1) by (fastforce simp add: e_def assms(8))+
  have X': "X' \<in> \<P>\<^sub>X" "x \<in> X'" 
    by (auto simp add: assms(7,6))
  have y_not_in_X': "y \<notin> X'" 
    using X'(1) XY(1) assms(3) xy(2) by(auto simp add: partition_on_def)

  show ?thesis
    proof(rule perfect_matchingI, goal_cases)
      case 1
      then show ?case
      proof(rule, elim UnE, goal_cases)
        case (1 ee)
        hence "ee \<in> partition_quotient_graph E \<P>"
          using assms(4) by(auto elim!: perfect_matchingE)
        then show ?case 
          using 1
        proof(elim partition_quotient_graphE, goal_cases)
          case (1 XX YY ea)
          have "ee \<inter> {X, Y} = {}"
            using assms(4,5) 1(1)
            by (fastforce elim!: perfect_matchingE matchingE)
          then show ?case 
            using 1 unfolding 1
            by(intro partition_quotient_graphI) auto
        qed
      next
        case (2)
        then show ?case 
          using  e(1,3,5,6) X'(1,2) XY(1) xy 
          by(auto intro!: partition_quotient_graphI[where e = e])
      next
        case (3 ee)
        hence "ee \<in> partition_quotient_graph (graph_inter_Vs E X) \<P>\<^sub>X"
          using assms(10) remove_vertices_subgraph by blast
        then show ?case 
        proof(elim partition_quotient_graphE, goal_cases)
          case (1 XX YY ea)
          then show ?case 
            using e(1) graph_inter_Vs_subset(1)
            by(auto intro!: partition_quotient_graphI[where e = ea])
        qed
      qed
    next
      case 2
      then show ?case
      proof(rule matching_vertex_disj_union, goal_cases)
        case 1
        then show ?case
      proof(rule matching_vertex_disj_union, goal_cases)
        case 1
        then show ?case
          using assms(4) matching_delete perfect_matchingE by blast
      next
        case 2
        then show ?case
          using matching_singleton by auto
      next
        case 3
        then show ?case 
        proof(rule ccontr, goal_cases)
          case 1
          hence "Y \<in> Vs (M - {{Y, X}}) \<or> X' \<in> Vs (M - {{Y, X}})"
            by (auto simp add: Vs_of_edge)
          then show ?case 
          proof(elim disjE, goal_cases)
            case 1
            then show ?case 
              using  assms(3,4,5) X'(1)
             by (auto elim!: perfect_matchingE
                simp add: remove_matching_edge_Vs Vs_of_edge)
         next
           case 2
           then obtain eee where eee:"eee \<in> M" "eee \<in> M - {{Y, X}}" "X' \<in> eee"
             by (auto simp: vs_member)
           then obtain YY where YY:"eee = {X', YY}" "YY \<noteq> X'"
             by(elim dblton_graphE[OF partition_quotient_graph_is_dblton[of E],
                        OF  perfect_matching_subgraphD[OF assms(4), of eee]]) blast
           hence "X' = X"
             using X'(2) eee(1) assms(2,5) xy(1) e(4)
             by(elim partition_quotient_graphE[OF perfect_matching_subgraphD[OF assms(4)], of eee])
               (auto simp add: doubleton_eq_iff prepartition_on_def disjoint_def)
           hence "{X, Y} = {X', YY}" 
             using assms(4) YY(1) eee(1)
             by(intro matching_unique_match[of M X' "{X, Y}" "{X', YY}"])
               (auto elim!:  perfect_matchingE simp add: assms(5) edge_commute)
           thus False 
             using YY(1) eee(2) by auto
         qed
       qed
     qed
      next
        case 2
        then show ?case
          by (simp add: assms(10))
      next
        case 3
        then show ?case
        proof(rule ccontr, goal_cases)
          case 1
          then obtain Z where "Z \<in> Vs M'" "Z \<in> Vs M - {X} \<or> (Z = X' \<and> \<not> Z \<in> Vs M - {X})" 
            using assms(5,4) e(6) edges_are_Vs
            by (auto elim!: perfect_matchingE  simp add: vs_insert remove_matching_edge_Vs) (auto, blast+)
          then show ?case
          proof(elim disjE, goal_cases)
            case 1
            hence "Z \<in> \<P>\<^sub>X" 
              using  Vs_partition_quotient_graph[of \<P>\<^sub>X "graph_inter_Vs E X"] 
                    remove_vertices_subgraph_Vs[of Z "partition_quotient_graph \<P>\<^sub>X (graph_inter_Vs E X)" "{X'}"]
              by(auto elim!: perfect_matchingE simp add: assms(11))
            moreover have "Z \<in> \<P>"
             using assms(4) Vs_partition_quotient_graph[of E \<P>] 1
             by(auto elim!: perfect_matchingE)
           moreover have "Z \<subseteq> X" 
             using assms(3) calculation(1) partition_onD1 by blast
           ultimately have "Z = X"
             using assms(2,3) e(4)
             by(intro prepartition_on_eq_if_inter_nempty)
               (auto simp add: inf.absorb_iff1 partition_onD3)
           thus ?case
             using "1"(2) by fastforce
          next
            case 2
            then show ?case
              using assms(11)
              by(auto elim!: perfect_matchingE)
          qed
        qed
      qed
    next
      case 3
      then show ?case
      proof(subst prepartition_quotient_graph_verts_by_Delta, goal_cases)
        case 1
        then show ?case 
          by (simp add: assms(2,3) e(4) partition_of_prepartition_is_prepartition)
      next
        case 2
        then show ?case 
          using assms(1) by auto
      next
        case 3
        have rw1:"{Xa | Xa e. Xa \<in> \<P> - {X} \<union> \<P>\<^sub>X \<and> e \<in> Delta E Xa} =
              {Xa | Xa e. Xa \<in> \<P> - {X} \<and> e \<in> Delta E Xa} \<union>
              {Xa | Xa e. Xa \<in> \<P>\<^sub>X \<and> e \<in> Delta E Xa}"
          by auto
        have rw2:"Vs M - {Y, X} \<union> Vs {{Y, X'}} = Vs M - {X} \<union> {X'}"
          using  e(6) edges_are_Vs_2[of Y X M] edges_are_Vs_2[of X Y M] assms(5)
          by(auto simp add: Vs_of_edge insert_commute) 
        have rw3:"Vs (M - {{Y, X}} \<union> {{Y, X'}} \<union> M') = 
               Vs (M) - {X} \<union> ({X'} \<union> Vs M')"
          unfolding vs_union using assms(4)
          by (subst remove_matching_edge_Vs)(auto elim!: perfect_matchingE simp add: assms(5) rw2)
        show ?case
          unfolding rw1 rw3
          proof(rule arg_cong2[where f = Set.union], goal_cases)
            case 1
            have rw1:"{Xa | Xa e. Xa \<in> \<P> - {X} \<and> e \<in> Delta E Xa} = 
                 {Xa | Xa e. Xa \<in> \<P> \<and> e \<in> Delta E Xa} - {X}"
              by auto
            show ?case 
              unfolding rw1
            proof(rule arg_cong2[where f = minus, OF _ refl], 
                  subst prepartition_quotient_graph_verts_by_Delta[symmetric], goal_cases)
              case 1
              then show ?case 
                by (simp add: assms(2))
            next
              case 2
              then show ?case 
                by (simp add: assms(1))
            next
              case 3
              then show ?case
                by (simp add: assms(4) perfect_matchingD(3))
            qed
          next
            case 2
            have rw1:"{Xa | Xa e. Xa \<in> \<P>\<^sub>X \<and> e \<in> Delta E Xa} =
                    {X'} \<union> {Xa | Xa e. Xa \<in> \<P>\<^sub>X - {X'} \<and> e \<in> Delta E Xa}"
              using xy e(1) X'(1,2) y_not_in_X' 
              by(auto intro: exI[of _ e] in_DeltaI[of "{x, y}" x y E X'])
            show ?case
              unfolding rw1
            proof(rule arg_cong2[where f = Set.union, OF refl], goal_cases)
              case 1
              have rw1:"Vs M' = \<P>\<^sub>X - {X'}"
                using assms(11) by auto
              show ?case 
              proof(rule, all \<open>rule\<close>, goal_cases)
                case (1 x)
                then show ?case 
                 unfolding rw1 by auto
              next
                case (2 XX) 
                then obtain ee where ee: "ee \<in> M'" "XX \<in> ee"
                  by(auto simp add: vs_member)
                hence "ee \<in> partition_quotient_graph (graph_inter_Vs E X) \<P>\<^sub>X \<setminus> {X'}"
                  using assms(10) by blast
                hence ee_in_quot: "ee \<in> partition_quotient_graph (graph_inter_Vs E X) \<P>\<^sub>X"
                          "X' \<notin> ee"
                  using remove_vertices_subgraph'  ee(1) rw1 by auto
                obtain YY ea where YY_ea:" ee = {XX, YY}"
                     "XX \<in> \<P>\<^sub>X" "YY \<in> \<P>\<^sub>X" "XX \<noteq> YY" "ea \<in> graph_inter_Vs E X" "XX \<inter> ea \<noteq> {}" "YY \<inter> ea \<noteq> {}"
                  using ee(2) partition_quotient_graphD[OF ee_in_quot(1)] by auto
                obtain a b where "ea = {a, b}" "a \<noteq> b" "ea \<in> E"
                  using YY_ea(5) assms(1) 
                  by(auto dest: set_mp[OF graph_inter_Vs_subset(1)] elim!: dblton_graphE)
                then obtain a b where "ea = {a, b}" "a \<noteq> b" "a \<in> XX" "b \<notin> XX" "ea \<in> E"
                  using YY_ea(2,3,4,6,7) assms(3)
                  by(auto simp add:  partition_on_def doubleton_eq_iff disjoint_def)blast+
                hence "ea \<in> Delta E XX"
                  by(auto simp add: Delta_def)
                thus ?case using ee_in_quot(2) 
                 by (auto simp add: YY_ea )
              qed
            qed
          qed
        qed
      qed
    qed

lemma partition_quotient_matching_refine_factor_critical_selection:
  assumes "dblton_graph E" "partition_on (Vs E) \<P>" "partition_on X \<P>\<^sub>X"
          "perfect_matching (partition_quotient_graph E \<P>) M"
          "{Y, X} \<in> M"
          "\<P>' = \<P> - {X} \<union> \<P>\<^sub>X"
          "\<And> X'. X' \<in> \<P>\<^sub>X \<Longrightarrow> 
            graph_matching (partition_quotient_graph (graph_inter_Vs E X) \<P>\<^sub>X  \<setminus> {X'}) (f X') \<and>
            Vs  (f X') = \<P>\<^sub>X - {X'}"
    shows "\<exists> X' \<in>  \<P>\<^sub>X. perfect_matching (partition_quotient_graph E (\<P> - {X} \<union> \<P>\<^sub>X)) 
                   (M - {{Y, X}} \<union> {{Y, X'}} \<union> f X')"
proof-
  obtain e where e: "e\<in>E" "X \<inter> e \<noteq> {}" "Y \<inter> e \<noteq> {}" "X \<in> \<P>" "Y \<in> \<P>" "X \<noteq> Y"
    using assms(4,5) 
    by (auto elim!: perfect_matchingE dest!: set_mp 
          simp add: partition_quotient_graph_def doubleton_eq_iff)+
  hence XY: "X \<inter> Y = {}" "X \<noteq> {}" "Y \<noteq> {}" "X \<subseteq> Vs E" "Y \<subseteq> Vs E"
    using assms(2) by(auto simp add: partition_on_def disjoint_def)
  then obtain x y where xy: "x \<in> X" "y\<in> Y" "{x, y} = e" "x \<noteq> y"
    using assms(1) e by(auto elim!: dblton_graphE simp add:  doubleton_eq_iff)
  then obtain X' where X': "X' \<in> \<P>\<^sub>X" "x \<in> X'"
    using assms(3) by(auto simp add: partition_on_def)
  have y_not_in_X': "y \<notin> X'" 
    using X'(1) XY(1) assms(3) xy(2) by(auto simp add: partition_on_def)
  note match = assms(7)[OF X'(1)]

  show ?thesis
  proof(rule bexI[OF _ X'(1)], goal_cases)
    case 1
    then show ?case
      find_theorems prepartition_on partition_on
    proof(rule partition_quotient_matching_refine_factor_critical[OF assms(1) 
           partition_on_implies_prepartition_on[OF assms(2)]
                 assms(3,4,5) X' xy(2)], goal_cases)
      case 1
      then show ?case 
        by (simp add: e(1) xy(3))
    next
      case 2
      then show ?case 
        using match by blast
    next
      case 3
      then show ?case 
        using match by auto
    qed
  qed
qed

end