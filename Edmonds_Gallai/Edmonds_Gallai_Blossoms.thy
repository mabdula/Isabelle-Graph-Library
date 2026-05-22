theory Edmonds_Gallai_Blossoms
  imports Edmonds_Gallai_Preps
begin

subsection \<open>Properties of the Edmonds-Gallai Decomposition and Blossom Contraction\<close>

hide_const neighbourhood
hide_fact neighbourhood_def

text \<open>We define a predicate. We will later show that sets $\mathcal{D}$ and $A$ 
 which satisfy this predicate are the Edmonds-Gallai Decomposition.
 For now, we still work with a fixed maximum-cardinality matching.\<close>

definition "edmonds_gallai G M \<D> A= 
  (disjoint \<D> \<and> \<Union> \<D> \<subseteq> Vs G \<and> (\<forall> X \<in> \<D>. X \<noteq> {}) \<and> 
  A =  (Neighbourhood G (\<Union> \<D>)) \<and>
    (\<forall> X Y. X \<in> \<D> \<and> Y \<in> \<D> \<and> X \<noteq> Y \<longrightarrow> (X \<leftarrow>|\<rightarrow>\<^bsub>G\<^esub> Y)) \<and>
  (\<forall> X x. X \<in> \<D> \<and>  x \<in> X \<longrightarrow> (\<exists> M. graph_matching (G \<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x})) \<and>
  (\<forall> X \<in> \<D>. \<exists> x. x \<in> X \<and> Vs (M\<lbrakk>X\<rbrakk>) = X - {x}) \<and>
   (\<forall> v \<in> Vs G. even_vert G M v \<longleftrightarrow> v \<in> \<Union> \<D>) \<and>
   Delta M (\<Union> \<D> \<union> A) = {} \<and>
   (\<forall> D \<in> \<D>. card (Delta M D) \<le> 1) \<and>
    Vs G - (\<Union> \<D>) \<subseteq> Vs M \<and>
    M \<inter> (G \<lbrakk>A\<rbrakk>) = {})"

lemma edmonds_gallaiI:
  "\<lbrakk> disjoint \<D>; 
     \<Union> \<D> \<subseteq> Vs G; 
     (\<And>X. X \<in> \<D> \<Longrightarrow> X \<noteq> {}); 
     A = Neighbourhood G (\<Union> \<D>);
     (\<And>X Y. \<lbrakk>X \<in> \<D>; Y \<in> \<D>; X \<noteq> Y\<rbrakk> \<Longrightarrow> X \<leftarrow>|\<rightarrow>\<^bsub>G\<^esub> Y); 
     (\<And>X x. \<lbrakk>X \<in> \<D>; x \<in> X\<rbrakk> \<Longrightarrow> \<exists>M. graph_matching (G \<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x});
     (\<And>X. X \<in> \<D> \<Longrightarrow> \<exists>x. x \<in> X \<and> Vs (M\<lbrakk>X\<rbrakk>) = X - {x});
     (\<And>v. v \<in> Vs G \<Longrightarrow> even_vert G M v \<longleftrightarrow> v \<in> \<Union> \<D>);
     Delta M (\<Union> \<D> \<union> A) = {};
     (\<And>D. D \<in> \<D> \<Longrightarrow> card (Delta M D) \<le> 1);
     Vs G - (\<Union> \<D>) \<subseteq> Vs M;
     M \<inter> (G \<lbrakk>A\<rbrakk>) = {} \<rbrakk> 
  \<Longrightarrow> edmonds_gallai G M \<D> A"
  unfolding edmonds_gallai_def by auto

lemma edmonds_gallaiE:
  "\<lbrakk> edmonds_gallai G M \<D> A;
     \<lbrakk> disjoint \<D>; 
       \<Union> \<D> \<subseteq> Vs G; 
       (\<And>X. X \<in> \<D> \<Longrightarrow> X \<noteq> {}); 
       A = Neighbourhood G (\<Union> \<D>);
       (\<And>X Y. \<lbrakk>X \<in> \<D>; Y \<in> \<D>; X \<noteq> Y\<rbrakk> \<Longrightarrow> X \<leftarrow>|\<rightarrow>\<^bsub>G\<^esub> Y); 
       (\<And>X x. \<lbrakk>X \<in> \<D>; x \<in> X\<rbrakk> \<Longrightarrow> \<exists>M. graph_matching (G \<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x});
       (\<And>X. X \<in> \<D> \<Longrightarrow> \<exists>x. x \<in> X \<and> Vs (M\<lbrakk>X\<rbrakk>) = X - {x});
       (\<And>v. v \<in> Vs G \<Longrightarrow> even_vert G M v \<longleftrightarrow> v \<in> \<Union> \<D>);
       Delta M (\<Union> \<D> \<union> A) = {};
       (\<And>D. D \<in> \<D> \<Longrightarrow> card (Delta M D) \<le> 1);
       Vs G - (\<Union> \<D>) \<subseteq> Vs M;
       M \<inter> (G \<lbrakk>A\<rbrakk>) = {} \<rbrakk> \<Longrightarrow> P 
   \<rbrakk> \<Longrightarrow> P"
  unfolding edmonds_gallai_def by auto

lemma edmonds_gallaiD:
  "edmonds_gallai G M \<D> A \<Longrightarrow> disjoint \<D>"
  "edmonds_gallai G M \<D> A \<Longrightarrow> \<Union> \<D> \<subseteq> Vs G"   
  "\<lbrakk>edmonds_gallai G M \<D> A; X \<in> \<D>\<rbrakk> \<Longrightarrow> X \<noteq> {}"
  "edmonds_gallai G M \<D> A \<Longrightarrow> A = Neighbourhood G (\<Union> \<D>)"
  "\<lbrakk>edmonds_gallai G M \<D> A; X \<in> \<D>; Y \<in> \<D>; X \<noteq> Y\<rbrakk> \<Longrightarrow> X \<leftarrow>|\<rightarrow>\<^bsub>G\<^esub> Y"
  "\<lbrakk>edmonds_gallai G M \<D> A; X \<in> \<D>; x \<in> X\<rbrakk> \<Longrightarrow> \<exists>M. graph_matching (G \<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x}"
  "\<lbrakk>edmonds_gallai G M \<D> A; X \<in> \<D>\<rbrakk> \<Longrightarrow> \<exists>x. x \<in> X \<and> Vs (M\<lbrakk>X\<rbrakk>) = X - {x}"
  "\<lbrakk>edmonds_gallai G M \<D> A; v \<in> Vs G\<rbrakk> \<Longrightarrow> even_vert G M v \<longleftrightarrow> v \<in> \<Union> \<D>"
  "edmonds_gallai G M \<D> A \<Longrightarrow> Delta M (\<Union> \<D> \<union> A) = {}"
  "\<lbrakk>edmonds_gallai G M \<D> A; D \<in> \<D>\<rbrakk> \<Longrightarrow> card (Delta M D) \<le> 1"
  "edmonds_gallai G M \<D> A \<Longrightarrow> Vs G - (\<Union> \<D>) \<subseteq> Vs M"
  "edmonds_gallai G M \<D> A \<Longrightarrow> M \<inter> (G \<lbrakk>A\<rbrakk>) = {}"
  unfolding edmonds_gallai_def by auto

lemma edmonds_gallai_inj_carry_over:
  assumes "inj_on f (Vs (G \<union> M))"  "edmonds_gallai G M \<D> A" "graph_invar G" "dblton_graph M"
  shows "edmonds_gallai ((image f) ` G) ((image f) ` M) ((image f) ` \<D>) (f ` A)"
proof-
  note edmonds_gallaiD = edmonds_gallaiD[OF assms(2)]
  have goal1:"disjoint ((`) f ` \<D>)" 
    using edmonds_gallaiD(1,2) assms(1) vs_union[of G M]
      inj_on_subset[of f "Vs (G \<union> M)" "\<Union> \<D>"] disjoint_image[of f \<D>]
    by auto
  have goal2: "\<Union> ((`) f ` \<D>) \<subseteq> Vs ((`) f ` G)"
    unfolding Vs_of_imaged_graph Union_of_imaged 
    by (simp add: image_mono local.edmonds_gallaiD(2))
  have goal3: "X \<in> (`) f ` \<D> \<Longrightarrow> X \<noteq> {}" for X
    using local.edmonds_gallaiD(3) by fastforce
  have inj_on2:"inj_on f (Vs G \<union> \<Union> \<D>)"
    using assms(1) edmonds_gallaiD(2) vs_union[of G M] inj_on_Un[of f "Vs G" "Vs M"]
      Un_absorb2[of "\<Union> \<D>" "Vs G"]
    by auto
  have goal4: "f ` A = Neighbourhood ((`) f ` G) (\<Union> ((`) f ` \<D>))"
    using inj_on2 assms(3)
    unfolding Union_of_imaged 
    by(subst Neighbourhood_image)
      (simp_all add: local.edmonds_gallaiD(4))
  have goal5: "\<lbrakk>X \<in> (`) f ` \<D>; Y \<in> (`) f ` \<D>; X \<noteq> Y\<rbrakk> \<Longrightarrow> X \<leftarrow>|\<rightarrow>\<^bsub>(`) f ` G\<^esub> Y" for X Y
  proof(goal_cases)
    case 1
    then obtain XX YY where XX_YY:"XX \<in> \<D>" "X = f ` XX" "YY \<in> \<D>" "Y = f ` YY"
      by blast
    moreover hence "XX \<noteq> YY"
      using "1"(3) by fastforce
    moreover have "inj_on f (Vs G \<union> XX \<union> YY)"
      using calculation(1,3) inj_on2 edmonds_gallaiD(2) Union_upper[of XX \<D>]
        Union_upper[of YY \<D>] Un_absorb2[of XX "Vs G"] Un_absorb2[of YY "Vs G"]
        Un_absorb2[of "\<Union> \<D>" "Vs G"]
      by auto
    ultimately show ?case
      using assms(3) edmonds_gallaiD(5)
      by(simp add: connected_sets_of_vertices_image)
  qed
  have goal6: "\<lbrakk>X \<in> (`) f ` \<D>; x \<in> X\<rbrakk> \<Longrightarrow> \<exists>M. graph_matching ( (`) f ` G \<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x}"
    for X x
  proof(goal_cases)
    case 1
    then obtain XX xx where XX_xx: "XX \<in> \<D>" "X = f ` XX" "x = f xx" "xx \<in> XX"
      by auto
    obtain M where M: "matching M" "M \<subseteq> G \<lbrakk>XX\<rbrakk>" "Vs M = XX - {xx}"
      using XX_xx(1,4) local.edmonds_gallaiD(6) by force
    have inj_on3: "inj_on f (Vs M)" 
      using XX_xx(1) inj_on2 M(3) inj_on_Un[of f "Vs G" "\<Union> \<D>"]
        inj_on_subset[of f "\<Union> \<D>" XX] inj_on_subset[of f XX "Vs M"]
      by auto
    have inj_on4: "inj_on f (Vs G \<union> XX)"
      using edmonds_gallaiD(2) XX_xx(1)
      by(auto intro!: inj_on_subset[OF inj_on2])
    have " graph_matching ( ((`) f ` G) \<lbrakk>f ` XX\<rbrakk>) ((`) f ` M)"
      using inj_on3 unfolding graph_inter_Vs_image[OF inj_on4]
      by(intro graph_matching_image)(auto simp add: M(1,2)) 
    moreover have "Vs ((`) f ` M) = f ` XX - {f xx}" 
      unfolding Vs_of_imaged_graph M(3)
      using inj_on4 XX_xx edmonds_gallaiD(2) 
      by (subst inj_on_image_set_diff[of _ "Vs G"])(auto simp add: inj_on_Un)
    ultimately show ?case 
      unfolding XX_xx
      by(intro exI[of _ "(image f) ` M"]) auto
  qed
  have goal7: "X \<in> (`) f ` \<D> \<Longrightarrow> \<exists>x. x \<in> X \<and> Vs ( (`) f ` M \<lbrakk>X\<rbrakk>) = X - {x}" for X
  proof(goal_cases)
    case 1
    then obtain XX where XX_xx: "XX \<in> \<D>" "X = f ` XX" 
      by auto
    obtain x where x: "x \<in> XX" "Vs (M \<lbrakk>XX\<rbrakk>) = XX - {x}" 
      using XX_xx(1) edmonds_gallaiD(7) by force
    have inj_on5: "inj_on f (Vs M \<union> XX)" 
      using edmonds_gallaiD(2) XX_xx(1)
      by(auto intro!: inj_on_subset[OF assms(1)] simp add: vs_union)
    have "Vs ( (`) f ` M \<lbrakk>X\<rbrakk>) = X - {f x}"
      using inj_on2 XX_xx(1) edmonds_gallaiD(2) x(1)
      unfolding  XX_xx graph_inter_Vs_image[OF inj_on5] Vs_of_imaged_graph x(2)
      by(subst inj_on_image_set_diff[of _ "Vs G"])(auto simp add:  inj_on_Un)
    then show ?case 
      by(intro exI[of _ "f x"])(simp add: XX_xx(2) x(1))
  qed
  have goal8: 
    "v \<in> Vs ((`) f ` G) \<Longrightarrow> even_vert ((`) f ` G) ((`) f ` M) v = (v \<in> \<Union> ((`) f ` \<D>))" for v
  proof(goal_cases)
    case 1
    then obtain vv where vv: "vv \<in>Vs G" "v = f vv"
      using Vs_of_imaged_graph[of f G] by auto
    moreover hence "inj_on f (Vs G \<union> Vs M \<union> {vv})"
      using assms(1) vs_union[of G M] sup.absorb_iff1[of "{vv}" "Vs (G \<union> M)"] 
      by auto
    moreover have "f vv \<in> f ` \<Union> \<D> \<longleftrightarrow> vv \<in> \<Union> \<D>"
      using  vv(1) inj_on2 edmonds_gallaiD(2) sup.absorb1[of "\<Union> \<D>" "Vs G"]
        inj_on_image_mem_iff[of f "Vs G" vv "\<Union> \<D>"]
      by auto
    ultimately show ?case
      using 1 assms(3)
      by(simp add: vv even_vert_image[of f G M ]  edmonds_gallaiD(8)[of vv] image_Union)
  qed

  have f_union:"f ` X \<union> f ` Y = f ` (X \<union> Y)" for X Y
    by auto
  have inj1:"inj_on f (Vs M \<union> (\<Union> \<D> \<union> A))"
    using  edmonds_gallaiD(2,4) Neighbourhood_in_G[of G "\<Union> \<D>"] assms(1)
    by(intro inj_on_subset[of _ "Vs (G \<union> M)" "Vs M \<union> (\<Union> \<D> \<union> A)"])
      (auto simp add: vs_union)
  hence goal9: "Delta ((`) f ` M) (\<Union> ((`) f ` \<D>) \<union> f ` A) = {}"
    using assms(4) edmonds_gallaiD(9)
    unfolding Union_of_imaged f_union
    by(simp add: Delta_image)
  have goal10: "D \<in> (`) f ` \<D> \<Longrightarrow> card (Delta ((`) f ` M) D) \<le> 1" for D
  proof(goal_cases)
    case 1
    then obtain X where X: "X \<in> \<D>" "D = f ` X" 
      by auto
    moreover have "inj_on f (Vs M \<union> X)"
      using calculation(1) by(intro inj_on_subset[OF inj1]) auto
    moreover have "inj_on ((`) f) (Delta M X)"
      using  assms(1) inj_on_Un[of "(`) f" G M] inj_on_subset[of "(`) f" M "Delta M X"] 
        inj_on_image[of f "G \<union> M"] in_DeltaD(2)[of _ M X]
      by(auto simp add: Vs_def)
    ultimately show ?case
      using assms(4) edmonds_gallaiD(10)
      unfolding Union_of_imaged f_union X
      by(simp add: Delta_image card_image)
  qed
  have goal11: "Vs ((`) f ` G) - \<Union> ((`) f ` \<D>) \<subseteq> Vs ((`) f ` M)"
    unfolding Vs_of_imaged_graph Union_of_imaged
    using inj1 edmonds_gallaiD(11) inj_on_image_set_diff[of f "Vs M \<union> (\<Union> \<D> \<union> A)" "Vs G" "\<Union> \<D>"] 
    by force
  have inj_on6: "inj_on f (Vs G \<union> A)"
    using edmonds_gallaiD(2,4) inj_on2 Neighbourhood_in_G[of G "\<Union> \<D>"] 
      sup.absorb1[of "\<Union> \<D>" "Vs G"] sup.absorb1[of A "Vs G"]
    by auto
  have inj_on7: "inj_on ((`) f) (M \<union> (G \<lbrakk>A\<rbrakk>))"
    using assms(1) graph_inter_Vs_subset(1)[of G A] inj_on_subset[of "(`) f" "G \<union> M" "M \<union> G"]
      inj_on_subset[of "(`) f" "G \<union> M" "G \<union> M"] inj_on_subset[of "(`) f" "G \<union> M" "M \<union> (G \<lbrakk>A\<rbrakk>)"]
      inj_on_image[of f "G \<union> M"] 
    by (force simp add: Vs_def)
  have goal12: "(`) f ` M \<inter> (((`) f ` G) \<lbrakk>f ` A\<rbrakk>) = {}"
    using  inj_on6 inj_on7
    by(simp add: graph_inter_Vs_image inj_on_inter edmonds_gallaiD(12))

  show ?thesis
    by(intro edmonds_gallaiI goal1 goal2 goal3 goal4 goal5 goal6 goal7 goal8 goal9 goal10
        goal11 goal12|
        assumption)+
qed

text \<open>This predicate is invariant under blossom expansion.\<close>

context quot
begin

text \<open>We consider the case there the representative of the blossom does not disappear after 
      contraction. This is the case if there are edges leaving the set of vertices of the blossom.\<close>

lemma emonds_gallai_connected_blossom_obtain_D:
  assumes assumptions: "edmonds_gallai (quotG E) (quotG M) \<D> A"
    "Delta E (set C) \<noteq> {}"  "s = Vs E - set C" "blossom E M stem C"
    "max_card_matching E M" "u \<notin> Vs E" "u' \<notin> Vs E" "u' \<noteq> u"
  obtains D where "D \<in> \<D>" "u \<in> D"
proof(goal_cases)
  case 1
  note one = this

  obtain x where x: "x \<in> set C" 
    using assumptions(2) by(auto elim!: in_DeltaE)
  hence x_even: "even_vert E M x" and x_E: "x \<in> Vs E"
    using blossom_verts_are_even[OF assms(4)] 
    by(auto simp add: even_verts_def)
  have Delta_s_nempty:"Delta E s \<noteq> {}"
    unfolding Delta_s_Delta_compl_s_iff_empty
    using assumptions(2,3,4) subset_path_Vs[OF path_suff', of stem C]
    by (auto simp add: double_diff)
  have "P x = u"
    by (simp add: assumptions(3) x)
  hence "even_vert (quotG E) (quotG M) u"
    using even_vertex_blossom_contraction[OF assms(4) x_even x_E assms(5,3,6,7,8)]
    by auto
  moreover have "u \<in> Vs (quotG E)" 
    using assumptions(2) Delta_s_nempty
    by(auto dest!: s_not_in_quot_Delta_s_empty)
  ultimately obtain D where "D \<in> \<D>" "u \<in> D"
    using edmonds_gallaiD(8)[OF assms(1), of u] 
    by auto
  thus thesis
    using 1 by auto
qed

lemma empty_stem_u_not_in_quot_matching:
  assumes "match_blossom M stem C" "s = Vs E - set C" "stem = []" "M \<subseteq> E" 
          "set C \<subseteq> Vs E" "matching M"
  shows "u \<notin> Vs (quotG M)"
proof(rule ccontr, goal_cases)
  case 1
  then obtain e where "e \<in> quotG M" "u \<in> e"
    by (auto simp add: vs_member)
  then show ?case 
  proof(elim in_quotG_subset_E[OF _ assms(4)], goal_cases)
    case (1 ua va)
    then show ?case 
      using good_quot_map(1) by auto
  next
    case (2 va ua)
    have rev:"rev_alt_path M (rev (butlast C))" 
      using "1" assms(1,2,3,4,6) match_blossom_def not_in_quot_matching_not_in_matching_2 odd_cycleD(3)
      by fastforce
    have dbl: "dblton_graph M"
      using assms(4) dblton_E by blast
    show ?case
      using 2
    proof(cases rule: matching_edge_rev_alt_path_cases[OF rev 2(5) dbl assms(6)], goal_cases)
      case (1 a b i)
      hence "edges_of_path (rev (butlast C)) ! i \<in> set (edges_of_path (rev (butlast C)))"
        using edges_of_path_length[of "rev (butlast C)"] nth_mem[of i "edges_of_path (rev (butlast C))"]
        by auto
      hence "{ua, va} \<subseteq> set C" 
        using bulast_subset[of C] "1"(12)
          edges_of_path_subset_path[of "{ua, va}" "rev (butlast C)"]
        by auto
      then show ?case
        using "2"(3) assms(2) by blast
    next
      case (2 u v)
      hence "hd C \<in> Vs M" 
        using last_rev[of C]  tl_rev[of C]
          vs_member_intro[of u "{ua, va}" M] last_tl[of "rev C"]
        by auto
      then show ?case 
        using append_Nil assms(1,3) match_blossomD(4) by force  
    next
      case 3
      hence "ua \<in> Vs E" 
        using assms(4) edges_are_Vs[of ua va] by auto
      moreover have "set (rev (butlast C)) = set C" 
        using  match_blossomD(3)[OF assms(1)]
        by(cases C rule: list_cases_hd_and_last)(auto simp add: odd_cycle_def)
      ultimately have "ua \<in> s"
        using "3"(9) assms(2) by blast
      thus False
        by (simp add: "3"(4))
    qed
  qed
qed

lemma expand_odd_cycle_still_factor_critical:
  fixes D
  assumes  "s = Vs E - set C" "odd_cycle C" "u \<notin> Vs E" "u \<in> D" "path E C"
           "dblton_graph E" "D \<subseteq> Vs (quotG E)" "distinct (butlast C)"
  assumes critical: "\<And> x. x \<in> D \<Longrightarrow> \<exists>M. graph_matching ((quotG E) \<lbrakk>D\<rbrakk>) M \<and> Vs M = D - {x}"
  shows "x \<in> D - {u} \<union> set C \<Longrightarrow> 
          \<exists> M. graph_matching ( E \<lbrakk>D - {u} \<union> set C\<rbrakk>) M \<and> Vs M = D - {u} \<union> set C - {x}" 
        (is "?asm \<Longrightarrow> ?the")
proof-
  have C_props: "C \<noteq> []" "length C \<ge> 2" "length C \<ge> 3"  "length C \<ge> 1"
    using assms(2)
    by (auto dest!: match_blossomD(3) simp add: odd_cycle_def  odd_cycle_nempty )
  have dblton_quotE: "dblton_graph (quotG E)"
    using graph_invar_quotG by blast
  have Vs_without_s_is_C:"Vs E - s =  set C"
    by (simp add: assms(1,5) double_diff subset_path_Vs)
  have Vs_quotG_is: "Vs (quotG E) = insert u s"
    using Delta_wth_s_empty_quot_Vs Delta_wth_s_nonempty_quot_Vs assms(4,7) by auto
  have path_C: "path E C" 
    using assms(1-6) path_suff' by blast
  have more_C_props: "odd_cycle C" "set C = Vs ( E \<lbrakk>set C\<rbrakk>)" "path ( E \<lbrakk>set C\<rbrakk>) C"
    using match_blossomD(3) assms(1-6) C_props(2) path_C
    by(intro Vs_of_graph_inter_path[symmetric]  path_on_graph_inter_path | force)+
  hence distinct_C: "distinct (butlast C)"
    using assms by auto
  have C_inter_quot_empty: "set C \<inter> Vs  (quotG E) = {}"
    using Vs_quotG_is Vs_without_s_is_C assms(1-6) by auto
    show "?asm \<Longrightarrow> ?the"
   proof(elim UnE, goal_cases)
      case 1
      obtain Md where M: "graph_matching ((quotG E) \<lbrakk>D\<rbrakk>) Md" "Vs Md = D - {x}"
        using "1" critical by force
      have Md_matches_u: "u \<in> Vs Md" 
        using "1" M(2) assms(4) by auto
      have dblton_Md: "dblton_graph Md" 
        using M(1) dblton_quotE dblton_graph_Vs_inter by blast
      obtain up where up: "{u, up} \<in> Md" "u \<noteq> up"
        using dblton_Md Md_matches_u 
        by(auto elim!: Undirected_Set_Graphs.dblton_graphE 
            simp add: vs_member insert_commute)+
      have Md_without_u_edge_Vs_inter: "Md - {{u, up}} \<subseteq> (quotG E) \<lbrakk>D - {u}\<rbrakk>"
        using M(1) graph_inter_Vs_subset(1)  M(1,2) up(1)
          remove_matching_edge_Vs[of Md "{u, up}"]
        by (intro is_part_of_graph_inter_Vs) force+
      have quotG_D_without_u:"(quotG E) \<lbrakk>D - {u}\<rbrakk> = E \<lbrakk>D - {u}\<rbrakk>"
        using assms(3,7)
        by(intro u_not_in_subgraph_same_subgraph) auto
      have Md_without_matching: "graph_matching (E \<lbrakk>D - {u}\<rbrakk>) (Md - {{u, up}})"
        using M(1) Md_without_u_edge_Vs_inter matching_delete  quotG_D_without_u
        by blast
      have u_up_in_quot:"{u, up} \<in> quotG E"
        using M(1) in_graph_inter_VsE subset_eq up(1) by blast
      moreover have up_in_s:"up \<in> s" 
        using Vs_quotG_is edges_are_Vs_2 u_up_in_quot by blast
      ultimately obtain uc where uc: "{uc, up} \<in> E" "uc \<in> set C" 
        using edge_in_quotG_2'_doubleton[of up E] assms(1-6)
        by (auto simp add: insert_commute)
      have "\<exists>M. graph_matching ( E \<lbrakk>set C\<rbrakk>) M \<and> Vs M = Vs ( E \<lbrakk>set C\<rbrakk>) - {uc}"
        using more_C_props distinct_C uc(2) 
        by (intro odd_cycle_graph_factor_critical[of "E \<lbrakk>set C\<rbrakk>" "C" uc])
          (auto simp add: dblton_E dblton_graph_Vs_inter)
      then obtain Mc where Mc: "graph_matching ( E \<lbrakk>set C\<rbrakk>) Mc" "Vs Mc = set C - {uc}"
        using more_C_props(2) by auto
      have Vs_Md_witht_up_is:"Vs (Md - {{u, up}}) = Vs Md - {u, up}"
        by (simp add: M(1) remove_matching_edge_Vs up(1))
      have C_inter_D_empty:"set C \<inter> D = {}"
        using C_inter_quot_empty Vs_quotG_is assms(7) by auto
      have "matching (Md - {{u, up}} \<union> {{uc, up}} \<union> Mc)"
      proof(rule matching_vertex_disj_union, goal_cases)
        case 1
        then show ?case 
        proof(rule matching_vertex_disj_union, goal_cases)
          case 1
          then show ?case 
            using Md_without_matching by blast
        next
          case 2
          then show ?case 
            by (simp add: matching_singleton)
        next
          case 3
          then show ?case 
            using C_inter_D_empty uc(2)
            by(auto simp add: Vs_Md_witht_up_is Vs_of_edge M(2))
        qed
      next
        case 2
        then show ?case
          by (simp add: Mc(1))
      next
        case 3
        then show ?case
          using Vs_without_s_is_C up_in_s C_inter_D_empty 
          by(auto simp add: Vs_Md_witht_up_is M(2) vs_union vs_insert Mc(2))
      qed
      moreover have "Md - {{u, up}} \<union> {{uc, up}} \<union> Mc \<subseteq> E \<lbrakk>D - {u} \<union> set C\<rbrakk>"
      proof(rule is_part_of_graph_inter_Vs, goal_cases)
        case 1
        then show ?case 
          using Mc(1) Md_without_matching graph_inter_Vs_subset(1) uc(1) by fastforce
      next
        case 2
        thus ?case
          unfolding vs_union Mc(2) Vs_of_edge Vs_Md_witht_up_is M(2)
          using M(2) edges_are_Vs_2 up(1,2)  uc(2) 
          by fastforce
      qed
      ultimately have "graph_matching ( E \<lbrakk>D - {u} \<union> set C\<rbrakk>) (Md - {{u, up}} \<union> {{uc, up}} \<union> Mc)"
        by simp
      moreover have "Vs (Md - {{u, up}} \<union> {{uc, up}} \<union> Mc) = 
                   D - {u} \<union> set C - {x}"
        unfolding vs_union Mc(2) Vs_of_edge Vs_Md_witht_up_is M(2)
        using  uc(2) up(1,2) M(2) edges_are_Vs_2 "1" C_inter_D_empty 
        by fastforce
      ultimately show ?case 
        by auto
    next
      case 2
      obtain Md where M: "graph_matching ((quotG E) \<lbrakk>D\<rbrakk>) Md" "Vs Md = D - {u}"
        using assms(4) critical by force
      have dblton_Md: "dblton_graph Md" 
        using M(1) dblton_quotE dblton_graph_Vs_inter by blast
      have Md_without_u_edge_Vs_inter: "Md \<subseteq> (quotG E) \<lbrakk>D - {u}\<rbrakk>"
        using M(1) graph_inter_Vs_subset(1)  M(1,2)
        by (intro is_part_of_graph_inter_Vs) force+
      have quotG_D_without_u:"(quotG E) \<lbrakk>D - {u}\<rbrakk> = E \<lbrakk>D - {u}\<rbrakk>"
        using assms(7) by(intro u_not_in_subgraph_same_subgraph) auto
      have Md_without_matching: "graph_matching (E \<lbrakk>D - {u}\<rbrakk>) Md"
        using M(1) Md_without_u_edge_Vs_inter matching_delete quotG_D_without_u by blast
      have "\<exists>M. graph_matching ( E \<lbrakk>set C\<rbrakk>) M \<and> Vs M = Vs ( E \<lbrakk>set C\<rbrakk>) - {x}"
        using more_C_props distinct_C 2 
        by (intro odd_cycle_graph_factor_critical[of "E \<lbrakk>set C\<rbrakk>" "C" x])
          (auto simp add: dblton_E dblton_graph_Vs_inter)
      then obtain Mc where Mc: "graph_matching ( E \<lbrakk>set C\<rbrakk>) Mc" "Vs Mc = set C - {x}"
        using more_C_props(2) by auto
      have "matching (Md \<union> Mc)"
      proof(rule matching_vertex_disj_union, goal_cases)
        case 1
        then show ?case 
          by (simp add: M(1))
      next
        case 2
        then show ?case
          by (simp add: Mc(1))
      next
        case 3
        then show ?case
          using C_inter_quot_empty assms(7) 
          by (auto simp add: M(2) Mc(2))
      qed
      moreover have "Md \<union> Mc \<subseteq> E \<lbrakk>D - {u} \<union> set C\<rbrakk>"
      proof(rule is_part_of_graph_inter_Vs, goal_cases)
        case 1
        then show ?case
          using Mc(1) Md_without_matching graph_inter_Vs_subset(1) by blast
      next
        case 2
        thus ?case
          unfolding vs_union Mc(2) Vs_of_edge  M(2)
          using M(2) edges_are_Vs_2
          by fastforce
      qed
      ultimately have "graph_matching ( E \<lbrakk>D - {u} \<union> set C\<rbrakk>) (Md \<union> Mc)"
        by simp
      moreover have "Vs (Md  \<union> Mc) = 
                   D - {u} \<union> set C - {x}"
        using "2" C_inter_quot_empty assms(7)
        by (auto simp add: vs_union Mc(2) Vs_of_edge  M(2))
      ultimately show ?case 
        by auto
    qed
  qed

text \<open>It may also happen, that the blossom has no leaving edges, 
    which e.g. also means that the stem is empty. 
    The vertex would then disappear due to the graph format.
    This is why we need to consider this case separately.\<close>

lemma emonds_gallai_connected_blossom:
  fixes D
  assumes assumptions: "edmonds_gallai (quotG E) (quotG M) \<D> A"
    "Delta E (set C) \<noteq> {}"  "s = Vs E - set C" "blossom E M stem C"
    "max_card_matching E M" "u \<notin> Vs E" "u' \<notin> Vs E" "u' \<noteq> u"
    "D \<in> \<D>" "u \<in> D"
  shows "edmonds_gallai E M (\<D> - {D} \<union> {D - {u} \<union> set C}) A"
proof-
  note M_props = max_card_matchingDs[OF assms(5)]
  have C_props: "C \<noteq> []" "length C \<ge> 2" "length C \<ge> 3"  "length C \<ge> 1"
    using assumptions(4)
    by (auto dest!: match_blossomD(3) simp add: odd_cycle_def  odd_cycle_nempty )
  note blossomD = blossomD[OF assms(4)]
  note match_blossomD = match_blossomD[OF blossomD(2)]
  note edmonds_gallaiD = edmonds_gallaiD[OF assms(1)]
  have alt_path_C: "alt_path M C" 
    using local.blossomD(2) match_blossom_alt_cycle by auto
  have C_butlast_C_tl:"set (butlast C) = set (tl C)" 
    by (simp add: local.match_blossomD(3) odd_cycle_set_butlast_tl)
  have Vs_without_s_is_C:"Vs E - s =  set C" 
    using  assumptions(3,4) subset_path_Vs[OF path_suff', of stem C]
    by(auto simp add: double_diff)
  have Vs_quotG_is: "Vs (quotG E) = insert u s"
    using assms(2)
    by(intro Delta_wth_s_nonempty_quot_Vs)(auto simp add: Vs_without_s_is_C)
  have C_inter_quot_empty: "set C \<inter> Vs  (quotG E) = {}"
    using Vs_quotG_is Vs_without_s_is_C assumptions(6) by auto

  have goal1: "disjoint (\<D> - {D} \<union> {D - {u} \<union> set C})"
  proof(rule disjointI, elim UnE, goal_cases)
    case (1 a b)
    then show ?case 
      using edmonds_gallaiD(1) 
      by (auto simp add: disjoint_def)
  next
    case (2 X Y)
    hence "X \<inter> D = {}"
      using assumptions(9) edmonds_gallaiD(1)
      by(auto simp add: disjoint_def)
    then show ?case
      using "2"(2,3) edmonds_gallaiD(2) C_inter_quot_empty
      by auto
  next
    case (3 X Y)
    hence "Y \<inter> D = {}"
      using assumptions(9) edmonds_gallaiD(1)
      by(auto simp add: disjoint_def)
    then show ?case
      using "3"(2,3) edmonds_gallaiD(2) C_inter_quot_empty
      by auto
  qed simp

  have in_D_but_not_in_E_is_u:"\<lbrakk>x \<in> X; X \<in> \<D>; x \<notin> Vs E\<rbrakk> \<Longrightarrow> x = u" for x X
    using assumptions(3) edmonds_gallaiD(2) neq_u_notin_quotG by blast
  have in_X_has_u_is_D: "\<lbrakk>u \<in> X; X \<in> \<D>\<rbrakk> \<Longrightarrow> X = D" for X 
    using  assumptions(10,9) edmonds_gallaiD(1)
    by(auto simp add: disjoint_def)
  have in_d_but_not_in_E_is_u:"\<lbrakk>x \<in> D; x \<notin> Vs E\<rbrakk> \<Longrightarrow> x = u" for x
    by (simp add: assumptions(9) in_D_but_not_in_E_is_u)

  have goal2: "\<Union> (\<D> - {D} \<union> {D - {u} \<union> set C}) \<subseteq> Vs E"
    using in_D_but_not_in_E_is_u in_X_has_u_is_D 
    by(auto dest: in_d_but_not_in_E_is_u 
        simp add: Vs_without_s_is_C[symmetric])

  have goal3: "X \<in> \<D> - {D} \<union> {D - {u} \<union> set C} \<Longrightarrow> X \<noteq> {}" for X
    using C_props(1) edmonds_gallaiD(3) by auto

  have X_neq_D_in_s: "X \<in> \<D> - {D} \<Longrightarrow> X \<subseteq> s" for X
    using  in_X_has_u_is_D edmonds_gallaiD(2)
    by(auto simp add: Vs_quotG_is)

  have goal4: 
    "\<lbrakk>X \<in> \<D> - {D} \<union> {D - {u} \<union> set C}; Y \<in> \<D> - {D} \<union> {D - {u} \<union> set C}; X \<noteq> Y\<rbrakk> \<Longrightarrow> X \<leftarrow>|\<rightarrow>\<^bsub>E\<^esub> Y"
    for X Y
  proof(elim UnE, goal_cases)
    case 1
    then show ?case 
      using edmonds_gallaiD(5)[of X Y] X_neq_D_in_s 
      by (subst (asm) connected_set_of_vertices_quot_iff) auto
  next
    case 2
    hence "D \<leftarrow>|\<rightarrow>\<^bsub>quot_graph P E - {{u}}\<^esub> X" 
      using assumptions(9) edmonds_gallaiD(5) by force
    then show ?case 
      unfolding connected_sym[of X]
      using "2"(2,3) X_neq_D_in_s Vs_without_s_is_C 
      by(subst (asm) connected_set_of_vertices_quot_iff_u)
        (auto simp add: assumptions(10))
  next
    case 3
    hence "D \<leftarrow>|\<rightarrow>\<^bsub>quot_graph P E - {{u}}\<^esub> Y" 
      using assumptions(9) edmonds_gallaiD(5) by force
    then show ?case 
      using "3"(2,3) X_neq_D_in_s Vs_without_s_is_C 
      by(subst (asm) connected_set_of_vertices_quot_iff_u)
        (auto simp add: assumptions(10))
  qed simp
  have rw_Union: "\<Union> \<D> - {u} \<union> (Vs E - s) = \<Union> (\<D> - {D} \<union> {D - {u} \<union> set C})"
    using Vs_without_s_is_C in_X_has_u_is_D assumptions(3,6,9) 
    by auto
  have dblton_quotE:"dblton_graph (quotG E)"
    by (simp add: doubleton_quot)
  have path_C: "path E C" 
    using assumptions(4) path_suff' by blast
  have more_C_props: "odd_cycle C" "set C = Vs ( E \<lbrakk>set C\<rbrakk>)" "path ( E \<lbrakk>set C\<rbrakk>) C"
    using match_blossomD(3) assumptions(4) C_props(2) path_C
    by(intro Vs_of_graph_inter_path[symmetric]  path_on_graph_inter_path | force)+
  hence distinct_C: "distinct (butlast C)"
    using assumptions(4) match_blossomD(2) by force
  have goal6:
    "\<lbrakk>X \<in> \<D> - {D} \<union> {D - {u} \<union> set C}; x \<in> X\<rbrakk> 
       \<Longrightarrow> \<exists>M. graph_matching ( E \<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x}" for X x
  proof(elim UnE, goal_cases)
    case 1
    have quotG_X_rw: "(quot_graph P E - {{u}}) \<lbrakk>X\<rbrakk> =  E \<lbrakk>X\<rbrakk>"
      using "1"(2) X_neq_D_in_s good_quot_map(1) edmonds_gallaiD(2) 
      by (intro u_not_in_subgraph_same_subgraph[of X]) auto
    show ?case
      using edmonds_gallaiD(6)[of X x] 1
      by(auto simp add: quotG_X_rw)
  next
    case 2
    have X_is: "X = D - {u} \<union> set C" 
      using 2 by auto
    hence x_in:"x \<in> D - {u} \<union> set C"
      using 2 by auto
    then show ?case 
      using assumptions(3,6,10) more_C_props(1) path_C dblton_E edmonds_gallaiD(2)
            assms(9) distinct_C edmonds_gallaiD(6)[OF assumptions(9)]
      unfolding X_is
      by(intro expand_odd_cycle_still_factor_critical) auto
  qed

  have goal7: "\<lbrakk>v \<in> Vs E\<rbrakk> \<Longrightarrow>even_vert E M v \<longleftrightarrow> v \<in> \<Union> (\<D> - {D} \<union> {D - {u} \<union> set C})" for v
  proof(cases "v \<in> set C", goal_cases)
    case 2
    hence v_still_there:"P v = v"
      using assumptions(3) by auto
    from 2 show ?case
    proof(intro iffI, goal_cases)
      case 1
      hence "even_vert (quotG E) (quotG M) v"
        using even_vertex_blossom_contraction[OF assumptions(4) 1(3,1) assumptions(5,3,6-8)]
          v_still_there
        by simp
      moreover have v_inquotVs:"v \<in> Vs (quotG E)"
        using "2"(1) v_still_there assumptions(6) Vs_quotG_is by fastforce
      ultimately have v_in_DU: "v \<in> \<Union> \<D>"
        using edmonds_gallaiD(8) Vs_quotG_is by force
      then obtain X where X: "X \<in> \<D>" "v \<in> X"
        by auto
      show ?case
      proof(cases "X = D")
        case True
        hence "v \<noteq> u"
          using "2"(1) assumptions(6) by blast
        then show ?thesis 
          using X by auto
      next
        case False
        then show ?thesis
          using X by auto
      qed
    next
      case 2
      then obtain X where X: "X \<in> \<D> - {D} \<union> {D - {u} \<union> set C}" "v \<in> X"
        by auto
      hence "even_vert (quotG E) (quotG M) v"
        using "2"(1,2,3) Vs_quotG_is Diff_iff[of v "Vs E" s]  Vs_without_s_is_C
          rw_Union local.edmonds_gallaiD(8)[of v]
        by auto
      thus ?case
        using "2"(1) assumptions(3,5,6,7,8) even_vertex_blossom_contraction_reverse local.blossomD(1,2)
          v_still_there by auto
    qed
  next
    case 1
    thus ?case
      using  blossom_verts_even_alt_path[OF assms(4), of v]
      by (auto simp add: even_vert_even_alt_path)
  qed

  have M_in_E:"M \<subseteq> E" 
    by (simp add: assumptions(5) max_card_matchingDs(1))
  have even_length_C:"even (length C)" 
    using more_C_props(1) odd_cycle_even_verts by auto

  have goal3a: "A = Neighbourhood E (\<Union> (\<D> - {D} \<union> {D - {u} \<union> set C}))"
    unfolding edmonds_gallaiD(4) 
    using assumptions(10,9) rw_Union u_in_X_Neighbourhood_expanded[of "\<Union> \<D>"] 
    by auto

  have stem_in_s:"set stem \<subseteq> s"
  proof-
    have "set stem \<subseteq> Vs E"
      using local.blossomD(1) subset_path_Vs by fastforce
    moreover have "set stem \<inter> set C = {}"
      using more_C_props(1) C_props(3) match_blossomD(2)
      by(cases C rule: list_cases_hd_and_last)
        (auto simp add: odd_cycle_def)
    ultimately show ?thesis
      using Vs_without_s_is_C by auto
  qed

  have matching_quot_M: "matching (quotG M)"
    using M_in_E M_props(2) assumptions(3,4) matching_quotM by blast

  have goal4a:
    "X \<in> \<D> - {D} \<union> {D - {u} \<union> set C} \<Longrightarrow> \<exists>x. x \<in> X \<and> Vs ( M \<lbrakk>X\<rbrakk>) = X - {x}"
    for X 
  proof(elim UnE, goal_cases)
    case 1
    have quotM_X_rw: "(quot_graph P M - {{u}}) \<lbrakk>X\<rbrakk> =  M \<lbrakk>X\<rbrakk>" 
      using 1 X_neq_D_in_s good_quot_map(1) edmonds_gallaiD(2) 
        max_card_matching_subgraphD[OF assumptions(5)]
      by (intro u_not_in_subgraph_same_subgraph[of X]) auto
    show ?case
      using edmonds_gallaiD(7)[of X] 1
      by(auto simp add: quotM_X_rw)
  next
    case 2
    obtain x where x: "x \<in> D" "Vs ((quot_graph P M - {{u}}) \<lbrakk>D\<rbrakk>) = D - {x}"
      using assumptions(9) local.edmonds_gallaiD(7) by force
    have rw1:"D - {u} \<union> (Vs E - s) = X"
      using "2" Vs_without_s_is_C by force
    then show ?case 
    proof(cases "u = x")
      case True
      note u_is_ix=this
      show ?thesis 
      proof(rule exI[of _ "hd C"], goal_cases)
        case 1
        have "hd C \<in> X"
          using C_props(1) Vs_without_s_is_C rw1 subset_code(1) by auto
        moreover have "Vs ( M \<lbrakk>X\<rbrakk>) = X - {hd C}"
        proof(rule, all \<open>rule\<close>, goal_cases)
          case (1 x')
          then show ?case
          proof(elim vs_member_elim in_graph_inter_VsE, goal_cases)
            case (1 e)
            note one = this
            obtain y' where y': "e = {x', y'}" "x' \<noteq> y'" 
              using M_in_E one(1,2) by blast
            have "x' \<noteq> hd C"
            proof(rule ccontr, goal_cases)
              case 1
              hence "y' = last stem" "stem \<noteq> []"
                using assumptions(4) one(2) y'(1)  assumptions(5) max_card_matchingDs(2)
                  matched_blossom_vertex'_partner_last_in_stem[of M stem C x' y']
                by auto
              hence y'_in_stem: "y' \<in> set stem"
                by auto
              hence y'_not_in_C: "y' \<notin> set C" 
                using "1" y'(2) local.match_blossomD(2)  C_butlast_C_tl list.collapse[of C]
                  mk_disjoint_insert[of y' "set (butlast C)"] set_ConsD[of y' x' "tl C"]
                by fastforce
              hence "{y', u} \<in> quotG M" 
                using y'_in_stem assumptions(3) blossomD(1) mem_path_Vs "1" C_props(1)
                  edge_commute one(2) y'(1) M_in_E 
                by (intro subgraph_edge_in_graph_edge_in_quot[of y' x']) auto
              hence "{y', u} \<in> (quot_graph P M - {{u}}) \<lbrakk>D\<rbrakk>"
                using y'(1) assms(10) one(3) rw1 y'_not_in_C assumptions(3) 
                by(auto intro!: in_graph_inter_VsI)
              thus False 
                using x(2)  edges_are_Vs_2 u_is_ix by blast
            qed
            thus ?case
              using one(3) y'(1) by blast
          qed
        next
          case (2 x)
          note Two = this
          hence "x \<in> D - {u} \<or> x \<in> set C - {hd C, last C}"
            using more_C_props(1) Vs_without_s_is_C rw1 odd_cycleD(3)[of C]
            by auto
          then show ?case
          proof(elim disjE, goal_cases)
            case 1
            then obtain e where "e \<in> (quotG M) \<lbrakk>D\<rbrakk>" "x \<in> e"
              using u_is_ix vs_empty ex_in_conv[of bot] x(2) vs_transport[of x " (quotG M) \<lbrakk>D\<rbrakk>" "{}"]
              by auto
            then show ?case
              using 1
            proof(elim in_graph_inter_VsE, goal_cases)
              case 1
              then show ?case
              proof(elim in_quotG_subset_E[OF _ M_in_E], goal_cases)
                case (1 ua va)
                hence "e \<in> M \<lbrakk>X\<rbrakk>"
                  using Two  good_quot_map(1) rw1 
                  by (auto intro!: in_graph_inter_VsI)
                then show ?case
                  using "1"(1) by blast
              next
                case (2 va ua)
                hence "{ua, va} \<in> M \<lbrakk>X\<rbrakk>"
                  using Two  good_quot_map(1) rw1 M_in_E
                  by (auto intro!: in_graph_inter_VsI)
                then show ?case 
                  using 2 by auto
              qed
            qed
          next
            case 2
            hence "x \<in> set (butlast (tl C))" 
              by(cases C rule: list_cases_hd_and_last) auto
            then obtain i where "x \<in> edges_of_path C ! i" "i < length C - 1" "odd i"
              using verts_of_odd_edges[of C, symmetric] even_length_C 
              by (auto simp add: vs_member)
            moreover hence "edges_of_path C ! i \<in> set (edges_of_path C) \<inter> M"
              using verts_of_even_edges alt_path_intersected_with_matching[OF M_props(2) alt_path_C]
              by auto
            moreover have "edges_of_path C ! i \<subseteq> X"
              using Vs_without_s_is_C calculation rw1 
                edges_of_path_subset_path[of "edges_of_path C ! i" C]
              by auto
            ultimately show ?case
              by(auto intro!: vs_member_intro in_graph_inter_VsI)

          qed
        qed
        ultimately show ?case 
          by auto
      qed
    next
      case False
      then show ?thesis 
      proof(intro exI[of _ x], goal_cases)
        case 1
        have "x \<in> X"
          using False rw1 x(1) by blast
        moreover have "Vs ( M \<lbrakk>X\<rbrakk>) = X - {x}" 
        proof(rule, all \<open>rule\<close>, elim vs_member_elim in_graph_inter_VsE, goal_cases)
          case (1 x' e)
          note one = this
          then obtain y' where y': "e = {x', y'}"
            using M_in_E by blast
          hence x'_in_X: "x' \<in> X"
            using one(1,3) by blast
          moreover have "x' \<noteq> x"
          proof(rule ccontr, goal_cases)
            case 1
            then show ?case
            proof(cases "y' \<in> set C", goal_cases)
              case 1
              then show ?case 
              proof(cases "x' \<in> set C", goal_cases)
                case 1
                thus ?case
                  using C_inter_quot_empty assumptions(9) local.edmonds_gallaiD(2) x(1) by auto
              next
                case 2
                hence "{x', u} \<in> quotG M"
                  using False one M_in_E assumptions(3,9) edmonds_gallaiD(2)
                    subgraph_edge_in_graph_edge_in_quot y'
                  by blast
                moreover have "{x', u} \<subseteq> D"
                  using "2"(1) assumptions(10) x(1) by blast
                ultimately have "{x', u} \<in> (quotG M) \<lbrakk>D\<rbrakk>"
                  by (simp add: in_graph_inter_VsI)
                thus ?case
                  using "2"(1) edges_are_Vs x(2) by fastforce
              qed
            next
              case 2
              then show ?case
              proof(cases "x' \<in> set C", goal_cases)
                case 1
                hence "{y', u} \<in> quotG M" 
                  using "1"(1) False assumptions(9) x(1) "1"(3) edmonds_gallaiD(2) Vs_without_s_is_C
                    neq_u_notin_quotG[of x']
                  by auto
                then show ?thesis 
                  using "1" False  assumptions(3,9) local.edmonds_gallaiD(2) neq_u_notin_quotG x(1) by blast
              next
                case 2
                hence "{x', y'} \<in> quotG M" 
                  using False M_in_E assumptions(3) edge_in_s_in_quotG y' one by auto
                moreover have "{x', y'} \<subseteq> D"
                  using  "1" "2"(2) x(1) one(1,2,3) y' Vs_without_s_is_C rw1
                  by auto
                ultimately have "{x', y'} \<in> (quotG M) \<lbrakk>D\<rbrakk>"
                  by (auto intro!: in_graph_inter_VsI)
                then show ?thesis
                  using "1" edges_are_Vs x(2) by fastforce
              qed
            qed
          qed
          ultimately show ?case
            by auto
        next
          case (2 x')
          hence "x' \<in> D - {u, x} \<or> (x' \<in> (Vs E - s) - {x} \<and> \<not> x' \<in> D - {u, x})"
            using rw1 by auto
          thus ?case
          proof(elim disjE, goal_cases)
            case 1
            then obtain y' where "{x', y'} \<in>  (quotG M) \<lbrakk>D\<rbrakk>"
              using finite_E M_in_E "2" x(2) finite_quot[of M] doubleton_quot[of M]
                finite_dbl_finite_verts[of "(quotG M)"] rev_finite_subset[of E M] 
                graph_invar_graph_inter_Vs[of "(quotG M)" D]
                graph_invar_no_edge_no_vertex[of "(quotG M) \<lbrakk>D\<rbrakk>" x']
              by auto
            then show ?case
            proof(elim in_graph_inter_VsE in_quotG_subset_E[OF _ M_in_E], goal_cases)
              case (1 ua va)
              hence "{x', y'} \<in> M \<lbrakk>X\<rbrakk>" 
                using 2 assumptions(3,6) rw1 
                by(auto intro!: in_graph_inter_VsI simp add: doubleton_eq_iff)
              then show ?case 
                by auto
            next
              case (2 va ua)
              have x'_neq_y': "x' \<noteq> y'"
                using "2"(2,7) by auto
              hence "va = x'" 
                using 1 2 by(auto simp add: doubleton_eq_iff)
              hence "{x', ua} \<in> M \<lbrakk>X\<rbrakk>"
                using 1 2 M_in_E rw1 edges_are_Vs[of ua va E]
                by(auto intro!: in_graph_inter_VsI simp add: doubleton_eq_iff insert_commute)
              then show ?case 
                by auto
            qed
          next
            case 2
            note two = this
            hence x'_in_C:"x' \<in> set C" 
              using Vs_without_s_is_C by auto
            then show ?case 
            proof (cases "x' = hd C")
              case True
              have stem_nempty: "stem \<noteq> []" 
              proof(rule ccontr, goal_cases)
                case 1
                hence "u \<notin> Vs (quot_graph P M - {{u}})"
                  using empty_stem_u_not_in_quot_matching[OF blossomD(2) assms(3)]
                    M_in_E M_props(2) Vs_without_s_is_C by auto
                thus False
                  using False assumptions(10) x(1,2)
                    graph_inter_Vs_subset(1)[of "quot_graph P M - {{u}}" D]
                    Vs_subset[of "(quotG M) \<lbrakk>D\<rbrakk>" "quot_graph P M - {{u}}"]
                  by auto
              qed
              hence last_stem_x'_in_M:"{last stem, x'} \<in> M" 
                using  M_props(2) True insert_commute[of x' "last stem" "{}"] local.blossomD(2)
                  blossom_stem_nempty_bloss_base_parter[of M stem C]
                by simp
              hence last_stem_u_inquotM:"{last stem, u} \<in> quotG M" 
                using last_in_set stem_in_s stem_nempty x'_in_C assumptions(3) M_in_E
                by(intro subgraph_edge_in_graph_edge_in_quot[of "last stem" x'])
                  auto
              have "last stem \<in> D" 
              proof(rule ccontr, goal_cases)
                case 1
                hence not_in_quot_on_D: "{last stem, u} \<notin> (quotG M) \<lbrakk>D\<rbrakk>"
                  using in_graph_inter_VsD(2) by blast
                have "u \<notin> Vs ((quotG M) \<lbrakk>D\<rbrakk>)" 
                proof(rule ccontr, goal_cases)
                  case 1
                  then obtain e where "e \<in> (quotG M) \<lbrakk>D\<rbrakk>" "u \<in> e"
                    by(auto simp add: vs_member)
                  moreover hence "e = {last stem, u}"
                    using matching_quot_M  last_stem_u_inquotM
                      matching_unique_match[of "quotG M" u e "{last stem, u}"]
                      in_graph_inter_VsD(1)[of e "quotG M" D] 
                    by auto
                  ultimately show ?case
                    using not_in_quot_on_D by simp
                qed
                hence "u = x"
                  by (simp add: assumptions(10) x(2))
                thus False
                  using False by auto
              qed
              hence "{last stem, x'} \<in> M \<lbrakk>X\<rbrakk>" 
                using last_stem_x'_in_M  last_stem_u_inquotM rw1 two
                by(auto intro!: in_graph_inter_VsI)
              thus ?thesis
                by auto
            next
              case False
              hence "x' \<in> set (tl (butlast C))"
                using x'_in_C C_butlast_C_tl C_props(3)
                by(cases C rule: list_cases_hd_and_last) auto
              moreover have "set (tl (butlast C)) \<subseteq> Vs ( M \<lbrakk>set C\<rbrakk>)"
                using M_props(2) assumptions(4) blossom_matched_in_C by fastforce
              ultimately have "x' \<in> Vs ( M \<lbrakk>set C\<rbrakk>)" by auto
              thus ?thesis
                using graph_inter_Vs_subset(1,2)[of M "set C"]
                  Vs_without_s_is_C rw1 le_supI1[of "Vs ( M \<lbrakk>set C\<rbrakk>)" "set C" "D - {u}"]
                  Vs_subset[of " M \<lbrakk>set C\<rbrakk>" " M \<lbrakk>X\<rbrakk>"]
                  is_part_of_graph_inter_Vs[of " M \<lbrakk>set C\<rbrakk>" M X]
                by auto
            qed
          qed
        qed
        ultimately show ?case
          by auto
      qed
    qed
  qed

  have A_D_disj: "A \<inter> \<Union> \<D> = {}"
    by(auto elim!: in_NeighbourhoodE simp add: edmonds_gallaiD(4))

  have goal8: "Delta M (\<Union> (\<D> - {D} \<union> {D - {u} \<union> set C}) \<union> A) = {}"
    using edmonds_gallaiD(9)
  proof(subst (asm) quot_Delta_no_change[of M], goal_cases)
    case 1
    then show ?case 
      unfolding edmonds_gallaiD(4) Neighbourhood_neighbourhood_union_inter
    proof(rule, goal_cases)
      case (1 x)
      hence ux:"{u, x} \<in> quotG M" 
        by(auto simp add: neighbourhood_def insert_commute)
      hence ux:"{u, x} \<in> quotG E"
        using M_in_E quotG_mono by blast
      then show ?case 
      proof(cases "x \<in> \<Union> \<D>", goal_cases)
        case 1
        then obtain X where X: "X \<in> \<D>" "x \<in> X"
          by auto
        moreover have "X = D"
        proof(rule ccontr, goal_cases)
          case 1
          have "X \<inter> D = {}"
            using "1" X(1) assumptions(9) disjointD local.edmonds_gallaiD(1) by blast
          thus ?case
            using edmonds_gallaiD(5)[OF X(1) assms(9) 1] ux X(2) assms(10)
            by(auto simp add: connected_set_of_vertices_def insert_commute)
        qed
        ultimately show ?case by auto
      next
        case 2
        then show ?case 
          using 1 assms(9,10)
          by(auto intro!: bexI[of _ D] bexI[of _ u] 
              simp add: insert_commute neighbourhood_def)
      qed
    qed
  next
    case 2
    then show ?case 
      by (simp add: M_in_E)
  next
    case 3
    then show ?case 
      using assms(9,10) by auto
  next
    case 4
    have "\<Union> \<D> \<union> A - {u} \<union> (Vs E - s) = \<Union> (\<D> - {D} \<union> {D - {u} \<union> set C}) \<union> A"
      unfolding Vs_without_s_is_C
      using assumptions(9,10) in_X_has_u_is_D A_D_disj by blast
    then show ?case 
      using "4" by argo
  qed

  have goal9: "X \<in> \<D> - {D} \<union> {D - {u} \<union> set C} \<Longrightarrow> card (Delta M X) \<le> 1" for X
  proof(elim UnE, goal_cases)
    case 1
    note one = this
    hence "card (Delta (quotG M) X) \<le> 1"
      by(intro edmonds_gallaiD(10)) simp
    then show ?case
    proof(subst (asm) quot_Delta_no_change2, goal_cases)
      case 1
      then show ?case
        using in_X_has_u_is_D one by force
    next
      case 2
      then show ?case 
      proof(rule notI, elim in_NeighbourhoodE, goal_cases)
        case (1 x)
        hence "X \<longleftrightarrow>\<^bsub>quotG E\<^esub> D"
          using M_in_E quotG_mono assms(10)
          by(auto intro!:  exI[of _ x, OF exI[of _ u]] simp add: connected_set_of_vertices_def)
        thus False
          using assumptions(9) local.edmonds_gallaiD(5) one by auto
      qed
    next
      case 4
      then show ?case 
        using X_neq_D_in_s one by auto
    qed (auto simp add: M_in_E)
  next
    case 2
    hence 2: "X = D - {u} \<union> set C"
      by auto
    show ?case
      unfolding 2
    proof(rule ccontr, goal_cases)
      case 1
      then obtain e1 e2 where e1e2: "e1 \<in> Delta M (D - {u} \<union> set C)"
        "e2 \<in> Delta M (D - {u} \<union> set C)" "e1 \<noteq> e2"
        using card_ge_1_obtain_two_distinc_elems
        by (auto simp add: linorder_class.not_le)
      then obtain x1 x2 y1 y2 where ysxs: "e1 = {x1, y1}" "x1 \<noteq> y1"  "e2 = {x2, y2}" "x2 \<noteq> y2"
        "x1 \<in> D - {u} \<union> set C" "x2 \<in> D - {u} \<union> set C" "e1 \<in> M" "e2 \<in> M"
        "y1 \<notin> D - {u} \<union> set C" "y2 \<notin> D - {u} \<union> set C" 
        by(auto elim!: in_DeltaE simp add: doubleton_eq_iff)
      have more_distincts: "x1 \<noteq> x2" "y2 \<noteq> y1" "x1 \<noteq> y2" "x2 \<noteq> y1"
        using M_props(2) e1e2 ysxs
          matching_edges_not_eqD(1)[of M x1 y2 x1 y1] matching_edges_not_eqD(3)[of M y1 x2 x1 y1]
        by (auto simp add: doubleton_eq_iff insert_commute)
      have ys_in_s:"y1 \<in> s" "y2 \<in> s"
        using ysxs(1,3,7,8,9,10) M_in_E  assumptions(3)
          edges_are_Vs_2[of x1 y1 E] edges_are_Vs_2[of x2 y2 E]
        by auto
      have "{P x1, y1} \<in> quotG M" "{P x2, y2} \<in> quotG M"
        using M_in_E assumptions(3) edge_in_s_then_in_quotG_subgraph subgraph_edge_in_graph_edge_in_quot'
          ys_in_s ysxs(1,3,7,8) by auto
      moreover have in_Ds:"P x1 \<in> D"  "P x2 \<in> D" 
        using Vs_without_s_is_C assumptions(10) ysxs(5,6) by auto
      moreover have not_in_Ds: "y1 \<notin> D" "y2 \<notin> D"
        using good_quot_map(1) ys_in_s ysxs(9,10) by blast+
      ultimately have "{P x1, y1} \<in> Delta (quotG M) D"  "{P x2, y2} \<in> Delta (quotG M) D"
        by(auto intro: in_DeltaI[of _ "P x1" y1]  in_DeltaI[of _ "P x2" y2])
      moreover  have "{P x1, y1} \<noteq> {P x2, y2}"
        using in_Ds(1) insert_commute more_distincts(2) not_in_Ds(2) by fastforce
      moreover have "finite (Delta (quot_graph P M - {{u}}) D)"
        using finite_E M_in_E Delta_finite[of "quot_graph P M - {{u}}" D] finite_quot[of M]
          finite_subset[of M E] 
        by auto
      ultimately have "card (Delta (quotG M) D) > 1"
        by(intro at_least_two_in_card_ge_1[of "{P x1, y1}" _ "{P x2, y2}"]) simp+
      thus False
        using assumptions(9) local.edmonds_gallaiD(10) by force
    qed
  qed

  have goal10: "Vs E - \<Union> (\<D> - {D} \<union> {D - {u} \<union> set C}) \<subseteq> Vs M"
  proof(rule, goal_cases)
    case (1 x)
    then show ?case
      using M_in_E  good_quot_map(1) edmonds_gallaiD(11) vert_in_graph_iff_in_quot_diff_u[of x]
      unfolding rw_Union[symmetric] 
      by auto
  qed

  have goal11: "M \<inter> (E \<lbrakk>A\<rbrakk>) = {}"
  proof(rule ccontr, goal_cases)
    case 1
    then obtain e where e: "e \<in> M" "e \<in> E \<lbrakk>A\<rbrakk>"
      by auto
    thus ?case
      using 1
    proof(elim in_graph_inter_VsE, goal_cases)
      case 1
      have e_in_s:"e \<subseteq> s" 
        using assumptions(6) e(2) local.edmonds_gallaiD(4) Vs_quotG_is
          Neighbourhood_in_G[of "quot_graph P E - {{u}}" "\<Union> \<D>"]
          vs_member_intro[of u e E] in_graph_inter_VsD(1,2)[of e E A]
        by auto
      show ?case 
        using "1"(3,4) e(1) edge_in_s_in_quotG[OF e_in_s M_in_E] edge_in_s_then_in_quotG[OF e_in_s]
          in_graph_inter_VsI[of e "quotG E" A] edmonds_gallaiD(12) 
        by auto
    qed
  qed

  show ?thesis
    by(rule edmonds_gallaiI goal1 goal2 goal3 goal3a goal4 goal4a 
        goal6 goal7 goal8 goal9 goal10 goal11| 
        assumption)+
qed

lemma emonds_gallai_lonely_blossom:
  assumes assumptions: "edmonds_gallai (quotG E) (quotG M) \<D> A"
    "Delta E (set C) = {}"  "s = Vs E - set C" "blossom E M stem C"
    "max_card_matching E M" "u \<notin> Vs E" "u' \<notin> Vs E" "u' \<noteq> u"
  shows  "edmonds_gallai E M (insert (set C) \<D>) A"
proof-
  have assms:  "edmonds_gallai (quotG E) (quotG M) \<D> A"
    "Delta E (set C) = {}"  "distinct (butlast C)"  "odd_cycle C"
    "s = Vs E - set C" "path E C"
    using assms(1-4) distinct_append match_blossomD(2,3) path_suff' by auto
  have quot_Vs_are:"Vs (quot_graph P E - {{u}}) = s"
    using assms(2,5,6) subset_path_Vs[of E C] double_diff[of "set C" "Vs E" "Vs E"]
    by (intro Delta_wth_s_empty_quot_Vs) auto
  note edmonds_gallaiD = edmonds_gallaiD[OF assms(1), simplified quot_Vs_are]
  have p_in_E:"set C \<subseteq> Vs E"
    by (simp add: assms(6) subset_path_Vs)
  have goal1: "disjoint (insert (set C) \<D>)"
    using assms(5) edmonds_gallaiD(1,2) 
    by(auto intro!: disjointI simp add: disjoint_def)
  have goal2: "\<Union> (insert (set C) \<D>) \<subseteq> Vs E"
    using p_in_E good_quot_map(2) edmonds_gallaiD(2) by auto
  have goal3: "X \<in> insert (set C) \<D> \<Longrightarrow> X \<noteq> {}" for X
    using assms(4) edmonds_gallaiD(3) odd_cycle_nempty by auto

  have goal4_helper: "X \<leftarrow>|\<rightarrow>\<^bsub> E \<^esub> Y"
    if "X \<in> \<D>" "Y \<in> \<D>" "X \<noteq> Y" for X Y
    using edmonds_gallaiD(2,5) that 
    by (subst connected_set_of_vertices_quot_iff[symmetric]) auto
  have goal4: "\<lbrakk>X \<in> insert (set C) \<D>; Y \<in> insert (set C) \<D>\<rbrakk> \<Longrightarrow> X \<noteq> Y \<Longrightarrow> X \<leftarrow>|\<rightarrow>\<^bsub>E\<^esub> Y" for X Y
  proof(elim insertE, goal_cases)
    case 2
    then show ?case 
      using disjointD goal1 assms(2) 
      by (intro empty_Delta_disconnected) auto
  next
    case 3
    then show ?case 
      using disjointD goal1 assms(2) 
      by (subst connected_sym, intro empty_Delta_disconnected) auto
  next
    case 4
    then show ?case 
      using goal4_helper by simp
  qed simp

  have u_not_in_D:"u \<notin> \<Union> \<D>" 
    using good_quot_map(1) edmonds_gallaiD(2) by auto
  have finite_D: "finite \<D>" 
    using  graph goal2 finite_UnionD[of "insert (set C) \<D>"]
      infinite_super[of "\<Union> (insert (set C) \<D>)" "Vs E"]
    by auto
  have Vs_E_on_p_are_p:"Vs (E \<lbrakk>set C\<rbrakk>) = set C"
    using assms(4,6) 
    by(intro Vs_of_graph_inter_path)(auto simp add: odd_cycle_def)
  have length_p_geq_2: "2 \<le> length C"
    using assms(4) odd_cycle_length_verts_ge_4 by fastforce

  have "\<lbrakk>X \<in> \<D>; x \<in> X\<rbrakk> \<Longrightarrow> \<exists>M. graph_matching ( E \<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x}" for X x
    using edmonds_gallaiD(6)[of X x] u_not_in_D  edmonds_gallaiD(2) quot_Vs_are
    by(subst (asm) u_not_in_subgraph_same_subgraph) auto
  moreover have "x \<in> set C \<Longrightarrow> \<exists>M. graph_matching ( E \<lbrakk>set C\<rbrakk>) M \<and> Vs M = set C - {x}" for x
  proof(goal_cases)
    case 1
    have "\<exists>M. graph_matching (E \<lbrakk>set C\<rbrakk>) M \<and> Vs M = Vs (E \<lbrakk>set C\<rbrakk>) - {x}"
      using p_in_E 1 length_p_geq_2
      by (intro odd_cycle_graph_factor_critical[of "E \<lbrakk>set C\<rbrakk>" C x])
        (auto intro!: path_on_graph_inter_path
          simp add: dblton_E assms(3,4,6) graph graph_invar_graph_inter_Vs Vs_E_on_p_are_p)
    then show ?case 
      unfolding Vs_E_on_p_are_p by simp
  qed
  ultimately have goal6:
    "\<lbrakk>X \<in> insert (set C) \<D>; x \<in> X\<rbrakk> \<Longrightarrow> \<exists>M. graph_matching ( E \<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x}" for X x
    by auto

  have goal7: "\<lbrakk>v \<in> Vs E\<rbrakk> \<Longrightarrow> even_vert E M v \<longleftrightarrow> v \<in> \<Union> (insert (set C) \<D>)" for v
  proof(cases "v \<in> set C", goal_cases)
    case 1
    then show ?thesis
      using blossom_verts_even_alt_path[OF assumptions(4)]
      by(force simp add: even_vert_even_alt_path) 
  next
    case 2
    hence v_still_there:"P v = v"
      using assumptions(3) by auto
    have v_in_quot:"v \<in> Vs (quotG E)"
      using "2"(1) v_still_there assumptions(6) quot_Vs_are by presburger
    show ?case
    proof(insert 2, rule, goal_cases)
      case 1
      hence "even_vert (quotG E) (quotG M) v"
        using even_vertex_blossom_contraction[OF assumptions(4) 1(3,1) assumptions(5,3,6-8)]
          v_still_there
        by simp
      thus ?case
        using edmonds_gallaiD(8) quot_Vs_are v_in_quot by force
    next
      case 2
      thus ?case
        using assumptions(3,4,5,6,7,8) even_vertex_blossom_contraction_reverse edmonds_gallaiD(8)
        by auto
    qed
  qed

  have goal3a: "A = Neighbourhood E (\<Union> (insert (set C) \<D>))"
  proof-
    have rw1: "Neighbourhood (quotG E) (\<Union> \<D>) = 
           Neighbourhood (quotG E) (insert u (\<Union> \<D>))"
      using good_quot_map(1) quot_Vs_are 
      by (intro Neighbourhood_of_one_more_same_if_nin_Vs[symmetric]) blast
    have rw2: "... = Neighbourhood E (\<Union> (insert (set C) \<D>))"
      using u_not_in_D assms(5) p_in_E 
      by (subst u_in_X_Neighbourhood_expanded, 
          (intro insertI1 arg_cong[where f = "Neighbourhood E"])+)
        auto
    show ?thesis
      using edmonds_gallaiD(4) rw1 rw2 by argo
  qed

  have X_neq_D_in_s: "X \<in> \<D> \<Longrightarrow> X \<subseteq> s" for X
    using local.edmonds_gallaiD(2) by blast
  have stem_empty:"stem = []"
  proof(rule ccontr, goal_cases)
    case 1
    hence "{last stem, hd C} \<in> Delta M (set C)"
      using assumptions(4) assumptions(5) max_card_matchingDs(2)
      by(auto intro!: nempty_blossom_stem_last_stem_hd_C_in_C_Delta[of M stem C])
    hence "{last stem, hd C} \<in> Delta E (set C)"
      using Delta_set_mp assumptions(5) max_card_matching_def by blast
    thus False
      by (simp add: assumptions(2))
  qed


  have goal6a: "X \<in> insert (set C) \<D> \<Longrightarrow> \<exists>x. x \<in> X \<and> Vs ( M \<lbrakk>X\<rbrakk>) = X - {x}" for X
  proof(elim insertE, goal_cases)
    case 2
    have quotM_X_rw: "(quot_graph P M - {{u}}) \<lbrakk>X\<rbrakk> =  M \<lbrakk>X\<rbrakk>" 
      using 2 X_neq_D_in_s good_quot_map(1) edmonds_gallaiD(2) 
        max_card_matching_subgraphD[OF assumptions(5)] quot_Vs_are
      by (intro u_not_in_subgraph_same_subgraph[of X]) auto
    show ?case
      using edmonds_gallaiD(7)[of X] 2
      by(auto simp add: quotM_X_rw)
  next
    case 1
    show ?case
      unfolding 1
    proof(rule exI[of _ "hd C"], goal_cases)
      case 1
      have "hd C \<in> set C"
        by (simp add: assms(4) odd_cycle_nempty)
      moreover have "Vs ( M \<lbrakk>set C\<rbrakk>) = set C - {hd C}"
      proof(rule, all \<open>rule\<close>, goal_cases)
        case (1 x)
        then show ?case 
        proof(elim vs_member_elim in_graph_inter_VsE, goal_cases)
          case (1 e)
          then show ?case 
            using stem_empty assumptions(4) Diff_iff[of x "set C" "{hd C}"]
              in_mono[of e "set C" x] vs_member_intro[of x e M] 
              match_blossomD(4)[of M "[]" C]
            by auto
        qed
      next
        case (2 x)
        hence "x \<in> set (tl (butlast C))" 
          using assms(4) 
          by(cases C rule: list_cases_hd_and_last)(auto simp add: odd_cycle_def)
        then show ?case 
          using blossom_matched_in_C[of M stem C]
            assumptions(4,5) max_card_matchingDs(2) by blast
      qed
      ultimately show ?case
        by auto
    qed
  qed

  have M_in_E: "M \<subseteq> E"
    by (simp add: assumptions(5) max_card_matchingDs(1))

  have goal8: "Delta M (\<Union> (insert (set C) \<D>) \<union> A) = {}"
    using edmonds_gallaiD(9)
  proof(subst (asm) quot_Delta_no_change2[OF _ _ M_in_E], goal_cases)
    case 1
    then show ?case 
      using Neighbourhood_in_G good_quot_map(1) edmonds_gallaiD(2,4) quot_Vs_are by force
  next
    case 2
    then show ?case
    proof(rule notI, elim in_NeighbourhoodE, goal_cases)
      case (1 x)
      hence ux:"{u, x} \<in> quotG M" 
        by(auto simp add: neighbourhood_def insert_commute)
      hence ux:"{u, x} \<in> quotG E"
        using M_in_E quotG_mono by blast
      then obtain y where "y \<in> set C" "{y, x} \<in> quotG E" "x \<notin> set C"
        using good_quot_map(1) quot_Vs_are edges_are_Vs[of u x "quot_graph P E - {{u}}"]
        by auto
      hence False
        using good_quot_map(1) quot_Vs_are ux edges_are_Vs[of u x "quot_graph P E - {{u}}"] 
        by auto
      thus ?case
        by simp
    qed
  next
    case 3
    then show ?case 
      using edmonds_gallaiD(2,4) quot_Vs_are
        Neighbourhood_in_G[of "quot_graph P E - {{u}}" "\<Union> \<D>"] sup.boundedI[of "\<Union> \<D>" s A]
      by auto
  next
    case 4
    then show ?case 
      using Delta_union_bound[of M "set C" "\<Union> \<D>"] Delta_union_bound[of M "set C" "\<Union> \<D> \<union> A"]
        assumptions(2) Delta_set_mp[OF M_in_E] sup.assoc[of "set C" "\<Union> \<D>" A] 
      by force
  qed
  note max_card_matchingD = max_card_matchingD[OF assumptions(5)]
  have goal9: "X \<in> insert (set C) \<D> \<Longrightarrow> card (Delta M X) \<le> 1" for X
  proof(elim insertE, goal_cases)
    case 2
    note one = this
    hence "card (Delta (quotG M) X) \<le> 1"
      by(intro edmonds_gallaiD(10)) simp
    then show ?case
    proof(subst (asm) quot_Delta_no_change2[OF _ _ M_in_E], goal_cases)
      case 1
      then show ?case 
        using one u_not_in_D by force
    next
      case 2
      then show ?case 
        using stem_empty assms(6) assumptions(3,4,5) M_in_E 
          Neighbourhood_in_G[of "quot_graph P M - {{u}}" X]
          max_card_matchingDs(2)[of E M] subset_path_Vs[of E C]
          empty_stem_u_not_in_quot_matching[of M "[]" C]
        by auto
    qed (auto simp add: X_neq_D_in_s one)
  next
    case 1
    hence "Delta M X = {}" 
      using M_in_E all_not_in_conv[of "Delta M X"] assumptions(2) Delta_set_mp[of M E _ X]
      by auto
    thus ?case
      by simp
  qed

  have goal10: "Vs E - \<Union> (insert (set C) \<D>) \<subseteq> Vs M"
    using M_in_E assumptions(3) edmonds_gallaiD(11) vert_in_graph_iff_in_quot_diff_u by blast
  have goal11: "M \<inter> (E \<lbrakk>A\<rbrakk>) = {}"
  proof(rule ccontr, goal_cases)
    case 1
    then obtain e where e: "e \<in> M" "e \<in> E \<lbrakk>A\<rbrakk>"
      by auto
    thus ?case
      using 1
    proof(elim in_graph_inter_VsE, goal_cases)
      case 1
      have e_in_s:"e \<subseteq> s" 
        using assumptions(6) e(2) local.edmonds_gallaiD(4)  "1"(4) quot_Vs_are
          Neighbourhood_in_G[of "quot_graph P E - {{u}}" "\<Union> \<D>"]
          vs_member_intro[of u e E] in_graph_inter_VsD(1,2)[of e E A]
        by auto
      show ?case 
        using "1"(3,4) e(1) edge_in_s_in_quotG[OF e_in_s M_in_E] edge_in_s_then_in_quotG[OF e_in_s]
          in_graph_inter_VsI[of e "quotG E" A] edmonds_gallaiD(12) 
        by auto
    qed
  qed

  show ?thesis
    by(intro edmonds_gallaiI goal1 goal2 goal3 goal3a goal4 goal6 goal6a
        goal7 goal8 goal9 goal10 goal11| 
        assumption)+
qed
end
end