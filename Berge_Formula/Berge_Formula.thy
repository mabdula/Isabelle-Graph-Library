theory Berge_Formula
  imports Tutte_Theorem.Tutte_Theorem
begin

lemma sum_card_edges2:
  assumes "graph_invar G"
  shows "sum card G = (\<Sum>e\<in>G. 2)"
  by (smt (verit, del_insts) assms card_edge mem_Collect_eq subset_eq sum.cong)

lemma matching_vertices_double_size:
  assumes "graph_invar M"
  assumes "matching M"
  shows "2 * (card M) = card (Vs M)"
  by (simp add: assms(1,2) graph_abs.intro graph_abs.matching_card_vs)

lemma edge_same_comp:
  assumes "graph_invar G"
  assumes "e \<in> G"
  assumes "x \<in> e"
  assumes "y \<in> e"
  shows "x \<in> connected_component G y" 
  using assms(1,2,3,4) edge_subset_component in_mono 
  by force

lemma left_uncoverred_matching:
  assumes "graph_invar G"
  assumes "graph_matching G M"
  assumes "X \<subseteq> Vs G"
  shows " 2 * (card M) + card (odd_comps_in_diff G X) - card X \<le> card (Vs G)"
proof -
  have "finite (Vs M)" 
    by (meson Vs_subset assms(1) assms(2) finite_subset)
  have "matching M" 
    by (simp add: assms(2))
  have "M \<subseteq> G" 
    by (simp add: assms(2))
  let ?comp_out  = "\<lambda> C. {e. e \<in> M \<and> (\<exists> x y. e = {x,y} \<and> y \<in> C \<and> x \<in> X)}"
  let ?QX = "(odd_comps_in_diff G X)"
  have 2: "\<forall> e\<in> G. card e = 2" 
    using \<open>graph_invar G\<close> card_edge by blast
  have 4:"\<forall> C \<in> ?QX. (?comp_out C) \<subseteq> M"
    by blast
  have "\<forall> C \<in> ?QX. card (?comp_out C) * 2 = card (Vs (?comp_out C))"
  proof
    fix C
    assume "C \<in> ?QX"
    have "card (Vs (?comp_out C)) =  sum (\<lambda> e. card e) (?comp_out C)"
      using \<open>finite (Vs M)\<close> \<open>matching M\<close> matching_card_is_sum by fastforce
    also have "\<dots> =  sum (\<lambda> e. 2) (?comp_out C)" 
      by (smt (verit, ccfv_threshold) "2" \<open>M \<subseteq> G\<close> mem_Collect_eq subset_eq sum.cong)
    also have "\<dots> = card (?comp_out C) * 2" by simp  
    ultimately show "\<dots> = card (Vs (?comp_out C))" 
      by presburger
  qed
  have 3:"\<forall> C \<in> ?QX. card ((Vs (?comp_out C)) \<inter> X) = card (?comp_out C)" 
  proof
    fix C
    assume "C \<in> ?QX"
    have 5:"\<forall> e \<in> (?comp_out C). card (e \<inter> X) = 1"
      using Int_commute odd_comps_in_diff_not_in_X[of C G X]  \<open>C \<in> ?QX\<close> by force
    have "card ((Vs (?comp_out C)) \<inter> X) = sum (\<lambda> e. card (e \<inter> X)) (?comp_out C)"
      using matching_int_card_is_sum[of M "(?comp_out C)" X] `matching M` `finite (Vs M)` 
      by blast
    then show "card ((Vs (?comp_out C)) \<inter> X) =  card (?comp_out C)" using 5  
      by force   
  qed
  have 2:"(\<Union>C \<in>?QX. ((Vs (?comp_out C)) \<inter> X)) \<subseteq> X" 
    by blast
  let ?f = "(\<lambda> C. ((Vs (?comp_out C)) \<inter> X))"
  have 1:"\<forall>C \<in> ?QX. finite ((Vs (?comp_out C)) \<inter> X)" 
    by (meson assms(1) assms(3) finite_Int finite_subset)
  have "finite ?QX" 
    by (simp add: assms(1) diff_components_finite)
  have "\<forall> C1 \<in>?QX. \<forall> C2 \<in> ?QX.  C1 \<noteq> C2 \<longrightarrow> ((Vs (?comp_out C1))) \<inter> ((Vs (?comp_out C2))) = {}"
    by (smt (verit, del_insts) \<open>matching M\<close> diff_component_disjoint odd_comps_in_diff_not_in_X 
        disjoint_iff_not_equal doubleton_eq_iff matching_unique_match mem_Collect_eq vs_member)
  then have "\<forall> C1 \<in>?QX. \<forall> C2 \<in> ?QX. 
    C1 \<noteq> C2 \<longrightarrow> ((Vs (?comp_out C1)) \<inter> X) \<inter> ((Vs (?comp_out C2)) \<inter> X) = {}"   
    by blast
  then have "card (\<Union>C \<in>?QX. ((Vs (?comp_out C) \<inter> X))) = 
    sum (\<lambda> C. card (Vs (?comp_out C) \<inter> X)) ?QX"
    using union_card_is_sum[of "?QX" ?f] 1 `finite ?QX` by presburger
  then  have "sum (\<lambda> C. card ((Vs (?comp_out C)) \<inter> X)) ?QX \<le> card X" 
    by (metis (no_types, lifting) 2 assms(1) assms(3) card_mono finite_subset)
  then have 8:"sum (\<lambda> C. card (?comp_out C)) ?QX \<le> card X" 
    using 3 by auto
  then have 10: "\<forall> C \<in> ?QX. finite (?comp_out C)" 
    unfolding Vs_def 
    by (metis (no_types, lifting) "4" Vs_def \<open>M \<subseteq> G\<close> assms(1) finite_UnionD finite_subset)

  let ?comp_out_empty = "{C. C \<in> ?QX \<and> ?comp_out C = {}}"
  let ?comp_out_non = "{C. C \<in> ?QX \<and> ?comp_out C \<noteq> {}}"
  have 23:"card ?comp_out_empty \<ge> card ?QX - card X"
  proof(rule ccontr)
    assume "\<not> card ?comp_out_empty \<ge> card ?QX - card X"
    then have  11:"card ?comp_out_empty < card ?QX - card X" 
      using not_less by blast
    have 6:"?comp_out_non \<union> ?comp_out_empty = ?QX" 
      by blast
    have 5:"?comp_out_non \<inter> ?comp_out_empty = {}" 
      by blast
    have 7:"sum (\<lambda> C. card (?comp_out C)) ?comp_out_empty = 0" 
      by (smt (verit, del_insts) card.empty mem_Collect_eq sum.infinite sum_eq_0_iff)
    then have "sum (\<lambda> C. card (?comp_out C)) ?QX =
               sum (\<lambda> C. card (?comp_out C)) (?comp_out_non \<union> ?comp_out_empty)" 
      using 6 by auto
    have "sum (\<lambda> C. card (?comp_out C)) (?comp_out_non \<union> ?comp_out_empty) = 
          sum (\<lambda> C. card (?comp_out C)) (?comp_out_non) + 
          sum (\<lambda> C. card (?comp_out C)) (?comp_out_empty)"
      by (metis (no_types, lifting) \<open>finite ?QX\<close> 5 6 finite_Un sum.union_disjoint)
    then have "sum (\<lambda> C. card (?comp_out C)) ?comp_out_non = sum (\<lambda> C. card (?comp_out C)) ?QX"    
      using 7 6 by auto
    then have 9: "sum (\<lambda> C. card (?comp_out C)) ?comp_out_non \<le> card X" 
      using 8 by presburger
    then have "\<forall> C \<in> ?comp_out_non. card(?comp_out C) \<ge> 1"
      by (simp add: 10 card_gt_0_iff Suc_leI)  
    then have "sum (\<lambda> C. card (?comp_out C)) ?comp_out_non \<ge> card ?comp_out_non"
      using sum_mono 
      by (metis (no_types, lifting) card_eq_sum)
    then have 12: "card X \<ge> card ?comp_out_non" 
      using 9 order_trans by blast
    have "card ?QX = card ?comp_out_empty + card ?comp_out_non"
      by (metis (no_types, lifting) \<open>finite ?QX\<close> 5 6 add.commute card_Un_disjoint finite_Un)
    then have "card ?comp_out_empty < card ?comp_out_empty + card ?comp_out_non - card X"
      using 11 by presburger
    then have "card ?comp_out_non > card X" 
      by (meson less_diff_conv nat_add_left_cancel_less)
    then show False 
      using 12 not_less by blast
  qed
  have 13:"\<forall>C \<in> ?comp_out_empty. \<exists>v \<in> C. v \<notin> Vs M"
  proof
    fix C
    assume asmC: "C \<in> ?comp_out_empty" 
    have "C \<in> ?QX" 
      using asmC by force
    have "?comp_out C = {}" 
      using asmC by fastforce
    have e_in_C:"\<forall> e \<in> M. e \<inter> C = {} \<or> e \<inter> C = e"
    proof(safe)
      fix e x y
      assume assms_edge: "e \<in> M" "x \<in> e" "x \<notin> C" "y \<in> e" "y \<in> C" 
      then have "e \<inter> X = {}" 
        using Diff_disjoint \<open>C \<in> ?QX\<close> \<open>M \<subseteq> G\<close> \<open>graph_invar G\<close> \<open>?comp_out C = {}\<close>
        by (smt (verit, del_insts) "1" "10" "3" Int_insert_left_if1 asmC card_0_eq dblton_graphE
                dblton_graph_subset disjoint_insert(1) doubleton_eq_iff empty_iff inf_aci(1) insertE
                matching_unique_match mem_Collect_eq mk_disjoint_insert odd_comps_in_diff_not_in_X
                vs_empty)

      then have "e \<in> (graph_diff G X)" 
        using \<open>M \<subseteq> G\<close> \<open>e \<in> M\<close> 
        by (simp add: graph_diffI subsetD)
      then have "x \<in> C"
        by (smt (verit, ccfv_SIG) \<open>C \<in> odd_comps_in_diff G X\<close> assms(1) assms_edge(2) assms_edge(4)
                 assms_edge(5) edge_same_comp graph_invar_diff odd_comps_in_diff_is_component)
      then show "y \<in> {}"
        using \<open>x \<notin> C\<close> by auto
    qed
    show "\<exists>v \<in> C. v \<notin> Vs M" 
    proof(rule ccontr)
      assume "\<not> (\<exists>v\<in>C. v \<notin> Vs M)" 
      then have "\<forall>v \<in> C. v \<in> Vs M" by blast
      then have " ((Vs M) \<inter> C) = C" by auto
      have "card ((Vs M) \<inter> C) = sum (\<lambda> e. card (e \<inter> C)) M"
        using matching_int_card_is_sum[of M M C]  `matching M`  \<open>finite (Vs M)\<close> by blast
      then have "even (card C)" 
        using \<open>Vs M \<inter> C = C\<close>
        by (smt (verit, ccfv_threshold) \<open>M \<subseteq> G\<close> assms(1) card_edge dvd_sum e_in_C even_numeral 
            odd_card_imp_not_empty subset_eq)
      then show False 
        using diff_odd_compoenent_has_odd_card[of C G X] \<open>C \<in> ?QX\<close> by auto
    qed
  qed
  let ?not_in_M = "\<lambda> C. {v. v \<in> C \<and> v \<notin> Vs M}"
  have 14:"\<forall>C \<in> ?comp_out_empty. ?not_in_M C \<noteq> {}" 
    using 13 by auto
  have "\<forall>C \<in> ?comp_out_empty.  (?not_in_M C) \<subseteq> C"
    by blast
  then have 15:"\<forall>C \<in> ?comp_out_empty. finite (?not_in_M C)" 
    by (metis (no_types, lifting) assms(1) component_in_E finite_subset mem_Collect_eq)
  then have "\<forall>C \<in> ?comp_out_empty. card (?not_in_M C) \<ge> 1" 
    by (metis (no_types, lifting) One_nat_def Suc_leI 14 card_gt_0_iff)
  then have 20:"sum (\<lambda> C. card (?not_in_M C)) ?comp_out_empty \<ge> card ?comp_out_empty"
    by (metis (no_types, lifting) card_eq_sum sum_mono)
  have "finite ?comp_out_empty" 
    using \<open>finite (odd_comps_in_diff G X)\<close> by auto
  have 16:"\<forall>C \<in> ?comp_out_empty. finite (?not_in_M C)" 
    using 15 by blast
  have "\<forall> C1 \<in> ?comp_out_empty. \<forall> C2 \<in> ?comp_out_empty. C1 \<noteq> C2 \<longrightarrow> 
        ?not_in_M C1 \<inter> ?not_in_M C2 = {}"
    by (metis (no_types, lifting) diff_component_disjoint disjoint_iff_not_equal mem_Collect_eq)
  then have 18:"sum (\<lambda> C. card (?not_in_M C)) ?comp_out_empty = 
      card  (\<Union>C \<in> ?comp_out_empty. (?not_in_M C))"
    using union_card_is_sum[of ?comp_out_empty ?not_in_M] 
      16 \<open>finite ?comp_out_empty\<close> by blast
  have 19:"(\<Union>C \<in> ?comp_out_empty. (?not_in_M C)) = (?not_in_M (\<Union>C \<in> ?comp_out_empty. C))"
    by (safe;blast+)
  have "(\<Union>C \<in> ?comp_out_empty. C) \<subseteq> Vs G" 
    by (metis (mono_tags, lifting) SUP_least mem_Collect_eq component_in_E)
  then have 17:"?not_in_M (\<Union>C \<in> ?comp_out_empty. C) \<subseteq> ?not_in_M (Vs G)" 
    by auto
  have "?not_in_M (Vs G)\<subseteq> Vs G" 
    by blast
  then have "finite (?not_in_M (Vs G))" 
    by (meson assms(1) finite_subset)
  then have 22:"card (?not_in_M (\<Union>C \<in> ?comp_out_empty. C)) \<le> card (?not_in_M (Vs G))"
    using 17 card_mono by blast
  have 21:"card (?not_in_M (Vs G)) = card (Vs G - Vs M)" 
    by (metis set_diff_eq) 
  have "card (Vs G - Vs M) = card (Vs G) - card (Vs M)" 
    by (meson Vs_subset \<open>M \<subseteq> G\<close> \<open>finite (Vs M)\<close> card_Diff_subset)
  then have "card ?comp_out_empty + card (Vs M) \<le> card (Vs G)" 
    by (smt (verit) "18" "19" "20" "21" "22" Vs_subset \<open>M \<subseteq> G\<close> add_diff_cancel_right' assms(1) 
        card_mono dual_order.trans le_add2 le_diff_iff)
  then have "card (Vs M) + card ?QX - card X \<le> card (Vs G)" 
    using 23 by linarith
  then show " 2 * (card M) + card (odd_comps_in_diff G X) - card X \<le> card (Vs G)"
    by (metis \<open>finite (Vs M)\<close> assms(1) assms(2) dblton_graph_subset matching_vertices_double_size)
qed

lemma vertices_sum_in_components:
  shows "(\<Union>C \<in> (odd_comps_in_diff G X). C) \<subseteq> (Vs G - X)"
  apply safe
   apply (meson in_mono component_in_E)
  using odd_comps_in_diff_not_in_X by blast

lemma diff_odd_comps_card:
  assumes "graph_invar G"
  shows "card (odd_comps_in_diff G X) \<le> card (Vs G - X)"
proof -
  have "(\<Union>C \<in> (odd_comps_in_diff G X). C) \<subseteq> (Vs G - X)" 
    by (metis vertices_sum_in_components)
  then have "card (\<Union>C \<in> (odd_comps_in_diff G X). C) \<le> card (Vs G - X)" 
    by (simp add: assms card_mono)
  moreover have "card (\<Union>C \<in> (odd_comps_in_diff G X). C) = (\<Sum>C \<in> (odd_comps_in_diff G X). card C)" 
    by (smt (verit) assms card_eq_0_iff diff_component_disjoint diff_components_finite 
        diff_odd_compoenent_has_odd_card odd_card_imp_not_empty sum.cong union_card_is_sum)
  moreover have "\<forall>C \<in> (odd_comps_in_diff G X). card C \<ge> 1" 
    by (metis One_nat_def Suc_leI card_eq_0_iff card_gt_0_iff diff_odd_compoenent_has_odd_card 
        odd_card_imp_not_empty odd_components_nonempty)
  moreover then have "(\<Sum>C \<in> (odd_comps_in_diff G X). card C) \<ge> card (odd_comps_in_diff G X)"
    by (metis card_eq_sum sum_mono)
  ultimately show "card (odd_comps_in_diff G X) \<le> card (Vs G - X)" 
    by linarith
qed

lemma construct_perfect_matching_with_new_vertices:
  assumes "graph_invar G"
  assumes "X \<subseteq> Vs G"
  assumes "\<forall>Y \<subseteq> Vs G. card (odd_comps_in_diff G X) - card X \<ge> 
          card (odd_comps_in_diff G Y) - card Y"
  assumes "finite A" 
  assumes "card A = card (odd_comps_in_diff G X) - card X"
  assumes "A \<inter> Vs G = {}" 
  shows "\<exists>M. perfect_matching (G \<union> {{x, y}| x y. x \<in> Vs G \<and> y \<in> A}) M"  
proof(cases "G = {}")
  case True
  have "Vs G = {}" 
    by (simp add: Vs_def True)
  then show ?thesis 
    unfolding perfect_matching_def matching_def2
    using  True by force
next
  case False
  then have "G \<noteq> {}" by auto
  let ?H = "(G \<union> {{x, y}| x y. x \<in> Vs G \<and> y \<in> A})" 
  let ?k = "card (odd_comps_in_diff G X) - card X" 

  show "\<exists>M. perfect_matching (G \<union> {{x, y}| x y. x \<in> Vs G \<and> y \<in> A}) M"
  proof(cases "card (odd_comps_in_diff G X) - card X \<le> 0")
    case True
    then have "\<forall>Y \<subseteq> Vs G. card (odd_comps_in_diff G Y) - card Y \<le> 0" 
      by (metis assms(3) bot_nat_0.extremum_uniqueI) 
    then have "\<forall>Y \<subseteq> Vs G. card (odd_comps_in_diff G Y) \<le> card Y" 
      by auto
    then have "tutte_condition G" 
      unfolding tutte_condition_def by auto
    have "card A = 0" 
      using True assms(5) by force
    then have "A = {}" 
      using assms(4) card_0_eq by blast
    then show ?thesis using tutte 
      using \<open>tutte_condition G\<close> assms(1) by fastforce
  next
    case False
    assume "\<not> card (odd_comps_in_diff G X) - card X \<le> 0"
    then have 2:"card (odd_comps_in_diff G X) \<ge> card X" 
      by simp
    have 5:"Vs ?H = Vs G \<union> A"
    proof(safe)
      {
        fix x
        assume "x \<in> Vs (G \<union> {{x, y} |x y. x \<in> Vs G \<and> y \<in> A})"
        then have x:"x \<in> Vs G \<or> x \<in> Vs {{x, y} |x y. x \<in> Vs G \<and> y \<in> A}"
          by (simp add: Vs_def)
        assume "x \<notin> A"
        show "x \<in> Vs G"
        proof(cases "x \<in> Vs G")
          case True
          then show ?thesis by auto
        next
          case False
          have "x \<in> Vs {{x, y} |x y. x \<in> Vs G \<and> y \<in> A}" 
            using False x by blast
          then show ?thesis
            unfolding Vs_def using `x \<notin> A` by blast
        qed
      }
      fix x
      assume "x \<in> A"
      obtain y where y:"y \<in> Vs G" 
        unfolding Vs_def 
        using \<open>G \<noteq> {}\<close> assms(1)
        by blast
      then have "{x, y} \<in> {{x, y} |x y. x \<in> Vs G \<and> y \<in> A}" 
        using \<open>x \<in> A\<close> by blast
      then show "x \<in> Vs (G \<union> {{x, y} |x y. x \<in> Vs G \<and> y \<in> A})" 
        using insertCI by auto
    qed (simp add: Vs_def)
    then have "card (Vs ?H) = card (Vs G) + card A" 
      by (simp add: assms(1,4,6) card_Un_disjoint sup_commute)
    then have 3:"card (Vs ?H) = card (Vs G) + ?k" 
      using assms(5) by presburger
    have "finite (Vs ?H)" 
      using `Vs ?H = Vs G \<union> A`
      by (simp add: assms(1) assms(4))
    have 1: "graph_invar ?H"  
      using `finite (Vs ?H)`  assms(1) assms(6)
      by (smt (verit) Un_iff dblton_graph_def disjoint_iff_not_equal mem_Collect_eq)
    have "?k \<le> card (Vs G)" 
      by (metis (no_types, lifting) assms(1-2) card_Diff_subset diff_le_self 
          diff_odd_comps_card dual_order.trans finite_subset)
    show "\<exists>M. perfect_matching ?H M"
    proof(rule ccontr)
      assume "\<nexists>M. perfect_matching ?H M" 
      then have "\<not> tutte_condition ?H" 
        by (simp add: 1 tutte)
      then have "\<exists>Y \<subseteq> Vs ?H. card (odd_comps_in_diff ?H Y) > card Y"
        by (meson le_less_linear tutte_condition_def)
      then obtain Y where Y_subs:"Y \<subseteq> Vs ?H \<and> card (odd_comps_in_diff ?H Y) > card Y" 
        by auto
      have "even ?k = even (card (Vs G))" 
        using diff_odd_component_parity'[of G X] 2 assms(1-2) by blast
      then have 4:"even (card (Vs G) + ?k)"
        by auto
      then have "even (card (Vs ?H)) = even (card (Vs G) + ?k)"
        using 3 by presburger
      then have "even (card (Vs ?H))" 
        using 4 by blast
      have 7:"Vs ?H \<in> connected_components ?H"
      proof -
        have "Vs ?H \<noteq> {}" 
          using False \<open>Vs (G \<union> {{x, y} |x y. x \<in> Vs G \<and> y \<in> A}) = Vs G \<union> A\<close> assms(5) by force
        then obtain v where "v \<in> Vs G" 
          by fastforce
        have "A \<noteq> {}" 
          by (metis False assms(5) card.empty order_refl)
        then obtain a where "a \<in> A" by auto
        then have "{v, a} \<in> {{x, y} |x y. x \<in> Vs G \<and> y \<in> A}" 
          using \<open>v \<in> Vs G\<close> by blast
        then have "{v, a} \<in> ?H" 
          by blast
        have 6:"\<forall>x \<in> Vs ?H. x \<in> connected_component ?H v" 
        proof
          fix x
          assume "x \<in> Vs ?H"
          show "x \<in> connected_component ?H v" 
          proof(cases "x \<in> A")
            case True
            then have "{v, x} \<in> {{x, y} |x y. x \<in> Vs G \<and> y \<in> A}" 
              using \<open>v \<in> Vs G\<close> by blast
            then have "{v, x} \<in> ?H" 
              by blast
            then show ?thesis 
              by (meson vertices_edges_in_same_component)
          next
            case False
            have "x \<in> Vs G" 
              using False 5 \<open>x \<in> Vs ?H\<close> by fastforce
            then have "{a, x} \<in> {{x, y} |x y. x \<in> Vs G \<and> y \<in> A}" 
              using \<open>x \<in> Vs G\<close> `a \<in> A` by blast
            then have "{a, x} \<in> ?H" 
              by blast
            then show ?thesis 
              by (metis (no_types, lifting) \<open>{v, a} \<in> ?H\<close> connected_components_member_trans 
                  vertices_edges_in_same_component)
          qed
        qed
        have "Vs ?H = connected_component ?H v"
        proof(safe)
          {
            fix x 
            assume "x \<in> Vs ?H"
            then show "x \<in> connected_component ?H v" 
              using 6 by blast
          }
          fix x
          assume "x \<in> connected_component ?H v"
          then show "x \<in> Vs ?H" 
            using 5 \<open>v \<in> Vs G\<close> in_connected_component_in_edges by fastforce
        qed
        then show ?thesis 
          unfolding connected_components_def
          using in_own_connected_component by fastforce
      qed
      have "connected_components ?H = {Vs ?H}"
      proof 
        show "connected_components ?H \<subseteq> {Vs ?H}"
        proof
          fix C
          assume asmC:"C \<in> connected_components ?H"
          obtain c where "c \<in> C" 
            by (metis (no_types, lifting) asmC connected_comp_has_vert in_own_connected_component)
          then have "c \<in> Vs ?H" 
            by (metis (no_types, lifting) asmC connected_comp_verts_in_verts)
          then have "C = Vs ?H" 
            by (metis (no_types, lifting) 7 IntI \<open>c \<in> C\<close> asmC connected_components_disj empty_iff)
          then show "C \<in> {Vs ?H}"
            by blast
        qed
        show "{Vs ?H} \<subseteq> connected_components ?H" 
          using 7 by blast
      qed
      have 13:"odd_comps_in_diff ?H {} = {}" 
        by (smt (verit) Collect_empty_eq Diff_disjoint Diff_eq_empty_iff graph_diff_empty
            odd_comps_in_diff_are_components Un_Diff_Int Y_subs 7 \<open>even (card (Vs ?H))\<close>
            boolean_algebra_cancel.sup0 connected_comp_has_vert connected_components_member_eq)
      have "\<exists>y \<in> Vs G. y \<notin> Y"
      proof(rule ccontr)
        assume "\<not> (\<exists>y\<in>Vs G. y \<notin> Y)" 
        then have "\<forall>y\<in>Vs G. y \<in> Y" by auto
        then have "Vs G \<subseteq> Y" by auto
        then have "card (Vs G) \<le> card Y" 
          by (meson Y_subs 1 card_mono finite_subset)
        then have "card (odd_comps_in_diff ?H Y) > card (Vs G)" 
          using Y_subs by linarith 
        then show False 
          by (smt (verit, del_insts) Diff_disjoint Int_commute Nat.le_diff_conv2 Un_Diff_Int
              Un_Int_eq(1) Y_subs 5 1 \<open>card (Vs G) \<le> card Y\<close> \<open>?k \<le> card (Vs G)\<close>
              add_le_mono assms(1,4-6) card_Un_Int diff_add_inverse2 diff_le_self 
              diff_odd_comps_card finite_Diff finite_subset le_trans not_less subset_Un_eq)
      qed
      then obtain y where y:"y \<in> Vs G \<and> y \<notin> Y" 
        using `\<exists>y \<in> Vs G. y \<notin> Y` by auto
      have "A \<subseteq> Y"
      proof(rule ccontr)
        assume "\<not> A \<subseteq> Y"
        then obtain a where a:"a \<in> A \<and> a \<notin> Y"
          by blast
        have "a \<in> Vs ?H - Y" 
          by (simp add: 5 a)
        have "{y, a} \<in> {{x, y} |x y. x \<in> Vs G \<and> y \<in> A}" 
          using a y by blast
        then have "{y, a} \<in> ?H" 
          by auto
        then have "{y, a} \<in> graph_diff ?H Y" 
          by (simp add: a y graph_diffI)
        then have 10:"a \<in> Vs (graph_diff ?H Y)" 
          by auto
        have 9: "\<forall>x\<in>Vs ?H - Y. x \<in> connected_component (graph_diff ?H Y) a"
        proof
          fix x
          assume asmx:"x \<in> Vs ?H - Y"
          show "x \<in> connected_component (graph_diff ?H Y) a" 
          proof(cases "x \<in> Vs G")
            case True
            then have "{x, a} \<in> {{x, y} |x y. x \<in> Vs G \<and> y \<in> A}" 
              using a by blast
            then have "{x, a} \<in> ?H"
              by auto
            have "{x, a} \<inter> Y = {}" 
              using a asmx by blast
            then show ?thesis
              by (metis (no_types, lifting) \<open>{x, a} \<in> ?H\<close> graph_diffI insert_commute 
                  vertices_edges_in_same_component)
          next
            case False
            then have "x \<in> A" 
              using 5 asmx by auto
            then have "{x, y} \<in> ?H" 
              using y by blast
            then have "{x, y} \<in> graph_diff ?H Y" 
              using  asmx y  by (simp add: graph_diffI)
            then show ?thesis 
              by (metis (no_types, lifting) \<open>{y, a} \<in> graph_diff ?H Y\<close> 
                  connected_components_member_sym connected_components_member_trans 
                  vertices_edges_in_same_component)
          qed
        qed
        have 11:"connected_components (graph_diff ?H Y) = {connected_component (graph_diff ?H Y) a}"
        proof 
          show "connected_components (graph_diff (G \<union> {{x, y} |x y. x \<in> Vs G \<and> y \<in> A}) Y)
                \<subseteq> {connected_component (graph_diff (G \<union> {{x, y} |x y. x \<in> Vs G \<and> y \<in> A}) Y) a}"
          proof
            fix C
            assume "C \<in> connected_components (graph_diff ?H Y)"
            then obtain c where c: "C = connected_component (graph_diff ?H Y) c \<and> 
                                    c \<in> (Vs (graph_diff ?H Y))"
              by (meson connected_comp_has_vert)
            then have "c \<in> Vs ?H - Y" 
              by (meson subsetD vs_graph_diff)
            then have "C = connected_component (graph_diff ?H Y) a" 
              by (simp add: c 9 connected_components_member_eq)
            then show "C \<in> {connected_component (graph_diff ?H Y) a}"
              by auto
          qed
          then show "{connected_component (graph_diff ?H Y) a} \<subseteq> 
                connected_components (graph_diff ?H Y)" 
            by (metis (no_types, lifting) 10 empty_iff 
                own_connected_component_unique subset_singleton_iff)
        qed
        have 12:"(odd_components (graph_diff ?H Y)) \<subseteq> connected_components (graph_diff ?H Y)" 
          by (simp add: components_is_union_even_and_odd)
        have "singl_in_diff ?H Y = {}" 
        proof(rule ccontr)
          assume " singl_in_diff ?H Y \<noteq> {}"
          then obtain v where v: "{v} \<in> singl_in_diff ?H Y \<and> v \<in> Vs ?H \<and> v \<notin> Y \<and> 
                                  v \<notin> Vs (graph_diff ?H Y)"
            by (meson ex_in_conv singl_in_diff_member)
          then have "v \<in> connected_component (graph_diff ?H Y) a" 
            by (simp add: 9)
          then show False 
            using "10" in_connected_component_in_edges v by fastforce
        qed
        then have "(odd_components (graph_diff ?H Y)) = (odd_comps_in_diff ?H Y)" 
          by (simp add: odd_comps_in_diff_def)
        then have 14:"(odd_comps_in_diff ?H Y) \<subseteq> {connected_component (graph_diff ?H Y) a}" 
          using 11 12 by presburger
        then have "card (odd_comps_in_diff ?H Y) \<le> card {connected_component (graph_diff ?H Y) a}" 
          by (meson card_mono finite.emptyI finite.insertI)
        then have "card (odd_comps_in_diff ?H Y) \<le> 1" 
          by force
        show False
        proof(cases "card (odd_comps_in_diff ?H Y) = 1")
          case True
          then have "card Y = 0"  
            using Y_subs by linarith
          then have "Y = {}" 
            by (meson Y_subs 1 card_eq_0_iff rev_finite_subset)
          then have "(odd_comps_in_diff ?H Y) = {}"
            using 13 by fastforce
          then show ?thesis 
            using Y_subs by auto
        next
          case False
          then show ?thesis
            by (smt (z3) One_nat_def Y_subs 14 card.empty card.insert finite.emptyI insert_absorb
                le0 not_less subset_singleton_iff)
        qed
      qed
      then have 14:"graph_diff ?H Y = graph_diff G Y" 
        unfolding graph_diff_def by (safe;blast)
      then have "singl_in_diff ?H Y = singl_in_diff G Y" 
        unfolding singl_in_diff_def
        apply safe
        using "5" \<open>A \<subseteq> Y\<close> subsetD by fastforce+
      then have 15:"odd_comps_in_diff ?H Y = odd_comps_in_diff G Y" 
        by (simp add: 14 odd_comps_in_diff_def)
      have "odd_comps_in_diff G (Y \<inter> Vs G) = odd_comps_in_diff G Y" 
        by (simp add: odd_comps_in_diff_same_inter_vertices assms(1))
      then have "card (odd_comps_in_diff G (Y \<inter> Vs G)) > card Y" 
        using Y_subs 15 by auto
      have "Y = (Y \<inter> Vs G) \<union> A" 
        by (metis Un_Int_assoc_eq Y_subs \<open>A \<subseteq> Y\<close> 5 le_iff_inf)
      then have "card Y = card (Y \<inter> Vs G) + card A" 
        by (metis Int_commute Un_Int_eq(2) assms(1,4,6) card_Un_disjoint finite_Int inf_assoc)
      then have "card Y = card (Y \<inter> Vs G) + ?k" 
        using assms(5) by presburger
      then have "card (odd_comps_in_diff G (Y \<inter> Vs G)) > card (Y \<inter> Vs G) + ?k" 
        using \<open>card Y < card (odd_comps_in_diff G (Y \<inter> Vs G))\<close> by presburger
      then have "card (odd_comps_in_diff G (Y \<inter> Vs G)) - card (Y \<inter> Vs G) > ?k"
        by auto
      then show False 
        by (meson Int_lower2 assms(3) not_less)
    qed
  qed
qed

lemma  berge_formula2:
  assumes "graph_invar G"
  assumes "graph_matching G M"
  assumes "X \<subseteq> Vs G"
  assumes "\<forall>Y \<subseteq> Vs G. int (card (odd_comps_in_diff G X)) - int (card X) \<ge> 
          int (card (odd_comps_in_diff G Y)) - int (card Y)" 
  assumes "\<forall>M'. graph_matching G M' \<longrightarrow> card M \<ge> card M'"
  assumes "finite A" 
  assumes "card A = card (odd_comps_in_diff G X) - card X"
  assumes "A \<inter> Vs G = {}" 
  shows " 2 * (card M) + card (odd_comps_in_diff G X) - card X \<ge> card (Vs G)"
proof(cases "G={}")
  case True
  have "Vs G = {}" using True 
    by (simp add: Vs_def)
  then have "(G \<union> {{x, y}| x y. x \<in> Vs G \<and> y \<in> A}) = {}"
    using True by auto
  then show ?thesis 
    using \<open>Vs G = {}\<close> by auto
next
  case False
  then have "G \<noteq> {}" by auto
  let ?H = "(G \<union> {{x, y}| x y. x \<in> Vs G \<and> y \<in> A})" 
  let ?k = "card (odd_comps_in_diff G X) - card X"
  show ?thesis
  proof(cases "card (odd_comps_in_diff G X) \<le> card X")
    case True
    then have 1:"\<forall>Y \<subseteq> Vs G. card (odd_comps_in_diff G Y) \<le> card Y" 
      by (smt (verit, ccfv_threshold) assms(4) of_nat_le_iff)
    then have "tutte_condition G" 
      unfolding tutte_condition_def  by auto
    then obtain M' where M':"perfect_matching G M'" 
      using tutte assms(1) by auto
    then have "graph_matching G M'" 
      by (meson perfect_matchingE perfect_matchingE)
    then have "card M' \<le> card M" 
      by (simp add: assms(5))
    moreover have "graph_invar M'"
      using \<open>graph_matching G M'\<close> assms(1) graph_invar_subset by auto
    moreover have "graph_invar M"
      using assms(1,2) graph_invar_subset by auto
    ultimately have "card (Vs M') \<le> card (Vs M)" 
      using M' assms(1,2)
      by(auto elim!: perfect_matchingE 
           simp add: matching_vertices_double_size[symmetric]) 
    then have "card (Vs M) \<ge> card (Vs G)" 
      by (metis M' perfect_matchingE)
    have "Vs M \<subseteq> Vs G" 
      by (simp add: Vs_subset assms(2))
    then have "Vs M =  Vs G" 
      by (metis Diff_eq_empty_iff \<open>card (Vs G) \<le> card (Vs M)\<close> assms(1) card.empty card_Diff_subset 
          card_gt_0_iff diff_is_0_eq finite_Diff finite_subset subset_antisym)
    then have "perfect_matching G M" 
      by (simp add: assms(1-2) perfect_matchingI)
    have 2:"2 * card M = card (Vs G)"
      by (metis \<open>Vs M = Vs G\<close> assms(1) assms(2) dblton_graph_subset matching_vertices_double_size)
    have 3:"\<forall>x \<in> (Vs G). card {x} \<ge> card (odd_comps_in_diff G {x})"
      by (metis Int_lower2 1 assms(8) insert_subset)
    then  have "\<forall>x \<in> (Vs G). even (card {x} - card (odd_comps_in_diff G {x}))"
      by (metis Int_lower2 2 assms(1,8) diff_odd_component_parity dvd_triv_left insert_subset)
    then have "\<forall>x \<in> (Vs G).card (odd_comps_in_diff G {x}) = 1"
      by (metis One_nat_def Suc_leI 3 antisym_conv card.empty card.insert dvd_diffD empty_iff
          finite.emptyI not_less odd_card_imp_not_empty odd_one zero_order(2))
    then have "\<forall>x \<in> (Vs G). barrier G {x}"
      by (metis barrier_def insert_not_empty is_singleton_altdef is_singleton_def)
    then have "\<exists> X \<subseteq> Vs G. barrier G X"
      by (metis False assms(1) dblton_graphE empty_subsetI equals0I insert_subset vs_member_intro) 
    then obtain X' where X':"X' \<subseteq> Vs G \<and> card (odd_comps_in_diff G X') = card X'"
      by (meson Tutte_Theorem.barrier_def)
    have "card (odd_comps_in_diff G X) - card X = 0" 
      using True diff_is_0_eq' by blast 
    then show ?thesis 
      using \<open>2 * card M = card (Vs G)\<close> assms(4) by force
  next
    case False
    have 5:"card (odd_comps_in_diff G X) \<ge> card X" 
      by (meson False le_cases)
    have 4:"Vs ?H = Vs G \<union> A"
    proof(safe)
      {
        fix x
        assume "x \<in> Vs (G \<union> {{x, y} |x y. x \<in> Vs G \<and> y \<in> A})"
        then have x:"x \<in> Vs G \<or> x \<in> Vs {{x, y} |x y. x \<in> Vs G \<and> y \<in> A}"
          by (simp add: Vs_def)
        assume "x \<notin> A"
        show "x \<in> Vs G"
        proof(cases "x \<in> Vs G")
          case True
          then show ?thesis by auto
        next
          case False
          have "x \<in> Vs {{x, y} |x y. x \<in> Vs G \<and> y \<in> A}" 
            using False x by blast
          then obtain x' y' where " x' \<in> Vs G \<and> y' \<in> A \<and> x \<in> {x', y'}" 
            by (smt (verit, del_insts) Union_eq Vs_def mem_Collect_eq singleton_conv2)
          then show ?thesis 
            using `x \<notin> A` by blast
        qed
      }
      fix x
      assume " x \<in> A"
      obtain y where "y \<in> Vs G" 
        unfolding Vs_def using \<open>G \<noteq> {}\<close> assms(1)
        by blast
      then show "x \<in> Vs (G \<union> {{x, y} |x y. x \<in> Vs G \<and> y \<in> A})" 
        using  insertCI  \<open>x \<in> A\<close> by blast 
    qed (simp add: Vs_def)
    have 13:"card (Vs ?H) = card (Vs G) + card A" 
      by (simp add: 4 assms(1,6,8) card_Un_disjoint sup_commute)
    then have "card (Vs ?H) = card (Vs G) + ?k" 
      using assms(7) by presburger
    have "finite (Vs ?H)" using `Vs ?H = Vs G \<union> A` 
      by (simp add: assms(1) assms(6))
    have graph_invar_H:"graph_invar ?H" 
      using `finite (Vs ?H)` assms(1) assms(8)
      by (smt (verit) Un_iff dblton_graph_def disjoint_iff_not_equal mem_Collect_eq)
    obtain Mh where Mh:"perfect_matching ?H Mh" 
      using  construct_perfect_matching_with_new_vertices[of G X A] assms(1,3,4,6-8) 
      by (smt (verit, best) 5 diff_add_inverse le_Suc_ex le_diff_conv of_nat_add of_nat_le_iff)
    have "matching Mh" 
      using Mh perfect_matchingE by blast
    have 6: "Vs Mh = Vs ?H" 
      by (metis (no_types, lifting) Mh perfect_matchingE)
    then  have "\<forall>a \<in> Vs ?H. \<exists>! e \<in> Mh. a \<in> e"
      using \<open>matching Mh\<close> unfolding matching_def2 by argo
    then have "\<forall>a \<in> A.  \<exists>! e \<in> Mh. a \<in> e" 
      by (simp add: 4)

    let ?edges_A = " {e. e \<in> Mh \<and> e \<inter> A \<noteq> {}}"
    have "?edges_A \<subseteq> Mh" 
      by auto
    then have 8:"card ((Vs ?edges_A) \<inter> A) = sum (\<lambda> e. card (e \<inter> A)) (?edges_A)" 
      using matching_int_card_is_sum[of Mh ?edges_A] `matching Mh` 4 6 assms(1-6) by fastforce
    have 7:"((Vs ?edges_A) \<inter> A) = A"
    proof(safe)
      fix x
      assume "x \<in> A"
      then obtain e where e: "e\<in> Mh \<and> x \<in> e" 
        using `\<forall>a \<in> A. \<exists>! e \<in> Mh. a \<in> e` by blast
      then show "x \<in> (Vs ?edges_A)" 
        using \<open>x \<in> A\<close> by blast
    qed
    have "\<forall>e \<in> (?edges_A). card (e \<inter> A) = 1"
    proof
      fix e
      assume asme: "e \<in> ?edges_A"
      then have "(e \<inter> A)  \<noteq> {}" by auto
      then have "card (e \<inter> A) \<ge> 1" 
        by (simp add: Suc_leI assms(6) card_gt_0_iff)
      then have "e \<in> ?H" 
        using Mh asme perfect_matchingE by auto
      have "card (e \<inter> A) \<noteq> 2" 
      proof
        assume "card (e \<inter> A) = 2" 
        have "e \<notin> G"        
          using \<open>e \<inter> A \<noteq> {}\<close> assms(8) by blast
        have "e \<in>{{x, y} |x y. x \<in> Vs G \<and> y \<in> A}"       
          using \<open>e \<in> ?H\<close> \<open>e \<notin> G\<close> by blast
        then obtain x y where "e = {x, y} \<and> x \<in> Vs G \<and> y \<in> A"
          by blast
        then have "(e \<inter> A) = {y}" 
          by (metis Int_insert_left_if0 Int_insert_left_if1 assms(8) disjoint_iff inf_bot_right)
        then show False 
          using `card (e \<inter> A) = 2` by auto
      qed
      have "card e = 2" 
        using `graph_invar ?H` `e \<in> ?H` by (meson card_edge)
      then show "card (e \<inter> A) = 1" 
        using `card (e \<inter> A) \<ge> 1`
        by (metis Suc_1 \<open>card (e \<inter> A) \<noteq> 2\<close> card.infinite card_seteq inf_le1 nat.simps(3) nle_le
                  not_less_eq_eq)
    qed
    then have "sum (\<lambda> e. card (e \<inter> A)) (?edges_A) = card ?edges_A" 
      by auto
    then  have 11:"card {e. e \<in> Mh \<and> e \<inter> A \<noteq> {}} = card A" 
      using 7 8 by presburger
    have 10:"{e. e \<in> Mh \<and> e \<inter> A = {}} \<union> {e. e \<in> Mh \<and> e \<inter> A \<noteq> {}} = Mh" 
      by blast
    have 9:"{e. e \<in> Mh \<and> e \<inter> A = {}} \<inter> {e. e \<in> Mh \<and> e \<inter> A \<noteq> {}} = {}"
      by blast
    have "finite Mh"    
      by (metis (mono_tags, lifting) Vs_def 6 \<open>graph_invar ?H\<close> finite_UnionD)
    then have "card {e. e \<in> Mh \<and> e \<inter> A = {}} + card {e. e \<in> Mh \<and> e \<inter> A \<noteq> {}} = card Mh "  
      by (metis (no_types, lifting) 9 10 card_Un_disjoint finite_Un)
    then have "card {e. e \<in> Mh \<and> e \<inter> A = {}} = card Mh - card A" 
      using 11 by presburger
    then have 12:"card (graph_diff Mh A) = card Mh - card A" 
      unfolding graph_diff_def  by blast
    have "(graph_diff Mh A) \<subseteq> Mh" 
      by (simp add: graph_diff_subset)
    then have "matching (graph_diff Mh A)" 
      using \<open>matching Mh\<close> unfolding matching_def by (meson subset_eq)
    have "graph_diff Mh A \<subseteq> G " 
      unfolding graph_diff_def
    proof(safe)    
      fix e
      assume "e \<in> Mh" "e \<inter> A = {}" 
      have "e \<in> ?H" 
        using Mh \<open>e \<in> Mh\<close> perfect_matchingE by auto
      have "e \<notin> {{x, y} |x y. x \<in> Vs G \<and> y \<in> A}" 
        using \<open>e \<inter> A = {}\<close> by blast
      then show "e \<in> G" 
        using \<open>e \<in> ?H\<close> by blast
    qed
    then have "graph_matching G (graph_diff Mh A)" 
      by (simp add: \<open>matching (graph_diff Mh A)\<close>)
    then have "card M \<ge> card Mh - card A" 
      by (metis 12 assms(5))
    then have "card M + card M \<ge> card Mh + card Mh - card A - card A" 
      by auto
    then have "2* card M + card A\<ge> 2*card Mh - card A" 
      by (metis le_diff_conv mult_2)
    then have "2* card M + ?k \<ge> 2*card Mh - card A" 
      by (metis assms(7))
    also have "2*card Mh - card A = card (Vs Mh) - card A" 
      using Mh dblton_graph_subset matching_vertices_double_size graph_invar_H
      by(force elim!: perfect_matchingE simp add: matching_vertices_double_size[symmetric])
    also have "card (Vs Mh) - card A = card (Vs ?H) - card A" 
      using 6 by presburger
    also  have "card (Vs ?H) - card A = card(Vs G)" 
      using 13 by presburger
    also have "2 * card M + (card (odd_comps_in_diff G X) - card X) = 
      2 * card M +  card (odd_comps_in_diff G X) - card X"
      using 5 by simp
    finally  show "card (Vs G) \<le> 2 * card M + card (odd_comps_in_diff G X) - card X" 
      by blast
  qed
qed

locale add_vertices =
  fixes G :: "'a set set"
  fixes f :: "'a  \<Rightarrow> 'a " 
  assumes graph: "graph_invar G"
  assumes inj: "inj_on f (Vs G)" 
  assumes "\<forall>x \<in> Vs G. f x \<notin> Vs G"
begin

lemma  berge_formula2':
  assumes "graph_matching G M"
  assumes "X \<subseteq> Vs G"
  assumes "\<forall>Y \<subseteq> Vs G. int (card (odd_comps_in_diff G X)) - int (card X) \<ge> 
          int (card (odd_comps_in_diff G Y)) - int (card Y)" 
  assumes "\<forall>M'. graph_matching G M' \<longrightarrow> card M \<ge> card M'" 
  shows " 2 * (card M) + card (odd_comps_in_diff G X) - card X \<ge> card (Vs G)"
proof -
  obtain A' where A':"A' = (\<Union>x\<in>Vs G. {(f x)})" 
    by simp
  let ?f' = "(\<lambda> x. {f x})"
  have "\<forall>x1 \<in> Vs G. \<forall>x2 \<in> Vs G. x1 \<noteq> x2 \<longrightarrow> f x1 \<noteq> f x2" 
    by (meson inj inj_on_def)
  then have 1:"\<forall>x1 \<in> Vs G. \<forall>x2 \<in> Vs G. x1 \<noteq> x2 \<longrightarrow> ?f' x1 \<inter> ?f' x2 = {}"
    by blast
  have "finite (Vs G)"
    using graph by auto
  have "\<forall>x \<in> Vs G. finite (?f' x)"
    by auto
  have 2:"sum (\<lambda> x. card (?f' x)) (Vs G) = card (\<Union>x\<in>(Vs G). (?f' x))" 
    using union_card_is_sum[of "Vs G" ?f'] 1 \<open>finite (Vs G)\<close> by blast 
  have "sum (\<lambda> x. card (?f' x)) (Vs G) = sum (\<lambda> x. 1) (Vs G)"
    by (meson is_singleton_altdef is_singleton_def)
  then have "sum (\<lambda> x. card (?f' x)) (Vs G) = card (Vs G)" 
    by auto
  then have 3:"card A' = card (Vs G)" 
    using 2 A' by presburger
  have "A' \<inter> (Vs G) = {}"
  proof(rule ccontr)
    assume " A' \<inter> Vs G \<noteq> {}"
    then obtain a where a:"a \<in>  A' \<inter> Vs G" 
      by auto
    have "a \<in> (\<Union>x\<in>Vs G. {(f x)})"  
      using A' a by fastforce
    then obtain x where  "x \<in> Vs G \<and> f x = a" 
      by blast
    then show False 
      by (metis IntD2 a add_vertices_axioms add_vertices_def)
  qed
  have "card (odd_comps_in_diff G X)  \<le> card (Vs G)" 
    by (metis (no_types, lifting) assms(2) card_Diff_subset diff_le_self diff_odd_comps_card
        finite_subset graph order_trans)
  then have " card (odd_comps_in_diff G X) - card X  \<le> card (Vs G)" 
    by (meson diff_le_self dual_order.trans)
  then have 4:"card (odd_comps_in_diff G X) - card X  \<le> card A'" 
    using 3 by presburger
  have "finite A'" 
    using A' graph by blast
  then obtain A where "A \<subseteq> A' \<and> (card (odd_comps_in_diff G X) - card X = card A)" 
    by (metis 4 obtain_subset_with_card_n)
  then show " 2 * (card M) + card (odd_comps_in_diff G X) - card X \<ge> card (Vs G)"
    using berge_formula2[of G M X A] assms 
    by (smt (z3) \<open>A' \<inter> Vs G = {}\<close> \<open>finite A'\<close> disjoint_iff_not_equal finite_subset graph subsetD)
qed

lemma  berge_formula:
  assumes "graph_matching G M"
  assumes "X \<subseteq> Vs G"
  assumes "\<forall>Y \<subseteq> Vs G. int (card (odd_comps_in_diff G X)) - int (card X) \<ge> 
          int (card (odd_comps_in_diff G Y)) - int (card Y)" 
  assumes "\<forall>M'. graph_matching G M' \<longrightarrow> card M \<ge> card M'" 
  shows " 2 * (card M) + card (odd_comps_in_diff G X) - card X = card (Vs G)"
  using berge_formula2'[of M X] 
  by (simp add: assms graph le_antisym left_uncoverred_matching)

lemma  berge_formula':
  assumes "X \<subseteq> Vs G"
  assumes "\<forall>Y \<subseteq> Vs G. int (card (odd_comps_in_diff G X)) - int (card X) \<ge> 
          int (card (odd_comps_in_diff G Y)) - int (card Y)" 
  shows " 2 * \<nu> G + card (odd_comps_in_diff G X) - card X = card (Vs G)"
proof(rule obtain_max_card_matching_\<nu>[of G], goal_cases)
  case (2 M)
  thus ?case
    using assms berge_formula[OF 2(1) assms]
    by(auto elim: max_card_matchingE)
qed (simp add: dblton_graph_finite_Vs graph)
 
end
end