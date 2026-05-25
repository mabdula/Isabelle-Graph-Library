theory Tutte_Theorem
  imports Odd_Components Cardinality_Sums
begin

definition tutte_condition where
  "tutte_condition G = ( \<forall> X \<subseteq> Vs G. card (odd_comps_in_diff G X) \<le> card X)"

definition comp_out where 
  "comp_out G C X = {e. e \<in> G \<and> (\<exists> x y. e = {x,y} \<and> y \<in> C \<and> x \<in> X)}"

lemma tutte_condition_member[iff?]: "tutte_condition G \<longleftrightarrow>
  (\<forall> X \<subseteq> Vs G. card (odd_comps_in_diff G X) \<le> card X)"
  unfolding tutte_condition_def by simp

lemma tutte_conditionE:
  assumes "tutte_condition G"
  assumes "X \<subseteq> Vs G"
  shows "card (odd_comps_in_diff G X) \<le> card X"
  using assms 
  by(auto simp: tutte_condition_member)

lemma tutte_conditionI:
  assumes "\<forall>X \<subseteq> Vs G. card (odd_comps_in_diff G X) \<le> card X"
  shows "tutte_condition G" 
  using assms tutte_condition_member by auto

lemma comp_out_member[iff?]:
  "e \<in> comp_out G C X \<longleftrightarrow> e \<in> G \<and> (\<exists> x y. e = {x,y} \<and> y \<in> C \<and> x \<in> X)" 
  by (simp add: comp_out_def)

lemma comp_outE:
  assumes "e \<in> comp_out G C X"
  obtains x y where "e = {x,y}" "y \<in> C" "x \<in> X"  "e \<in> G"   
  by (meson assms comp_out_member)

lemma comp_outI:
  assumes "e = {x,y}" "y \<in> C" "x \<in> X"  "e \<in> G"
  shows "e \<in>  comp_out G C X"   
  using assms comp_out_member by blast

lemma odd_components_in_tutte_graph:
  assumes "graph_invar G"
  assumes "tutte_condition G"
  shows "(odd_comps_in_diff G {}) = {}"
proof -
  have "finite (odd_comps_in_diff G {})" 
    by (simp add: assms(1) finite_odd_comps_in_diff)
  have "{} \<subseteq> G" by auto
  then have "card (odd_comps_in_diff G {}) \<le> card {}" using assms(2) 
    by (metis card.empty empty_subsetI tutte_conditionE)
  then show ?thesis 
    using \<open>finite (odd_comps_in_diff G {})\<close> by auto
qed

lemma connected_comp_if_comp_out_empty:
  assumes "C \<in> odd_comps_in_diff G X"
  assumes "comp_out G C X = {}"
  shows "C \<in> connected_components G"
proof -
  obtain x where "x \<in> Vs G \<and> x \<in> C"
    using component_in_E[of C G X] 
    by (metis assms(1) disjoint_iff_not_equal le_iff_inf odd_components_nonempty)
  then have "connected_component (graph_diff G X) x = C"
    using odd_comps_in_diff_is_component[of C G X] 
    by (simp add: \<open>C \<in> odd_comps_in_diff G X\<close>)
  have " \<nexists>x y. x \<in> C \<and> y \<in> X \<and> {x, y} \<in> G" 
    by (metis assms(2) comp_outI insert_absorb insert_commute insert_not_empty)
  then have "\<forall>x y. {x, y} \<in> G \<and> x \<in> C \<longrightarrow> {x, y} \<in> graph_diff G X"   
    using assms(1) odd_comps_in_diff_not_in_X 
    by (metis Int_empty_left disjoint_iff_not_equal graph_diffI insert_disjoint(1))
  then have "\<forall>x y. {x, y} \<in> G \<and> x \<in> C \<longrightarrow> y \<in> C" 
    by (metis assms(1) odd_comps_in_diff_is_component vertices_edges_in_same_component)
  have "connected_component G x = C" 
  proof(safe)
    fix y
    assume "y \<in> connected_component G x"
    show "y \<in> C"
    proof(cases "x = y")
      case True
      then show ?thesis 
        using \<open>x \<in> Vs G \<and> x \<in> C\<close> by auto
    next
      case False
      then obtain p where p_walk:"walk_betw G x p y"
        using `y \<in> connected_component G x`
        by (metis  in_con_comp_has_walk )
      then have "hd p \<in> C" 
        by (simp add: \<open>x \<in> Vs G \<and> x \<in> C\<close> walk_between_nonempty_pathD(3))
      then have "path G p" 
        using p_walk unfolding walk_betw_def  by auto
      then have "\<forall>z \<in> set p. z \<in> C"  using `hd p \<in> C`
        apply (induct p)
          apply force
         apply auto[1]
        by (metis \<open>\<forall>x y. {x, y} \<in> G \<and> x \<in> C \<longrightarrow> y \<in> C\<close> list.sel(1) set_ConsD)
      then show "y \<in> C" 
        by (metis last_in_set p_walk walk_betw_def)
    qed   
  qed (metis \<open>connected_component (graph_diff G X) x = C\<close> 
      con_comp_subset graph_diff_subset insert_absorb insert_subset)
  then show ?thesis 
    by (metis \<open>x \<in> Vs G \<and> x \<in> C\<close> connected_components_closed' own_connected_component_unique)
qed

lemma comp_out_nonempty:
  assumes "graph_invar G"
  assumes "C \<in> odd_comps_in_diff G X"
  assumes "tutte_condition G"
  shows "comp_out G C X \<noteq> {}"
proof(rule ccontr)
  assume "\<not> comp_out G C X \<noteq> {}"
  then have "comp_out G C X = {}" by auto
  obtain x where "x \<in> Vs G \<and> x \<in> C"
    using component_in_E[of C G X] assms(2)
    by (metis odd_components_nonempty subset_empty subset_eq)
  then have "connected_component (graph_diff G X) x = C"
    using odd_comps_in_diff_is_component[of C G X] 
    by (simp add: \<open>C \<in> odd_comps_in_diff G X\<close>)
  have "C \<in> connected_components G" 
    by (meson \<open>comp_out G C X = {}\<close> assms(2) connected_comp_if_comp_out_empty)
  then have "C \<in> (odd_comps_in_diff G {})" 
    by (metis assms(2) diff_odd_compoenent_has_odd_card graph_diff_empty 
        odd_comps_in_diff_are_componentsI2)
  then show False using odd_components_in_tutte_graph[of G]
    by (simp add: assms  odd_components_in_tutte_graph)
qed

lemma tutte1:
  assumes "\<exists>M. perfect_matching G M" "graph_invar G"
  shows "tutte_condition G"
proof(rule ccontr)
  obtain M where "perfect_matching G M" using assms by auto
  assume "\<not> tutte_condition G"
  then obtain X where "X \<subseteq> Vs G \<and> card (odd_comps_in_diff G X) > card X"
    by (meson le_less_linear tutte_condition_def)
  then have "X \<subseteq> Vs M" "graph_invar G" "matching M" "M\<subseteq>G" "Vs M = Vs G"
    using \<open>perfect_matching G M\<close> perfect_matchingE assms(2)
    by metis+ 
  then have "finite (Vs M)" by simp
  have "finite M" 
    by (metis Vs_def \<open>Vs M = Vs G\<close> \<open>graph_invar G\<close> finite_UnionD)
  let ?comp_out  = "\<lambda> C. {e. e \<in> M \<and> (\<exists> x y. e = {x,y} \<and> y \<in> C \<and> x \<in> X)}"
  let ?QX = "(odd_comps_in_diff G X)"
  have 2: "\<forall> e\<in> G. card e = 2" 
    using \<open>graph_invar G\<close> card_edge by blast
  have "\<forall> C \<in> ?QX. (?comp_out C) \<subseteq> M"
    by blast
  have "\<forall> C \<in> ?QX. card (?comp_out C) * 2 = card ( Vs (?comp_out C))"
  proof
    fix C
    assume "C \<in> ?QX"
    have "card (Vs (?comp_out C)) =  sum (\<lambda> e. card e) (?comp_out C)"
      using \<open>finite (Vs M)\<close> \<open>matching M\<close> matching_card_is_sum by fastforce
    also have "\<dots> =  sum (\<lambda> e. 2) (?comp_out C)" 
      by (smt (verit, del_insts) \<open>M \<subseteq> G\<close> \<open>graph_invar G\<close> card_edge mem_Collect_eq subset_eq sum.cong)
    also have "\<dots> = card (?comp_out C) * 2" by simp  
    ultimately show "\<dots> = card (Vs (?comp_out C))" 
      by presburger
  qed
  have "\<forall> C \<in> ?QX. card ((Vs (?comp_out C)) \<inter> X) = card (?comp_out C)" 
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
  have "(\<Union>C \<in>?QX. ((Vs (?comp_out C)) \<inter> X)) \<subseteq> X" 
    by blast
  let ?f = "(\<lambda> C. ((Vs (?comp_out C)) \<inter> X))"
  have "\<forall>C \<in> ?QX. finite ((Vs (?comp_out C)) \<inter> X)" 
    by (meson \<open>X \<subseteq> Vs M\<close> \<open>finite (Vs M)\<close> finite_Int finite_subset)
  have "finite ?QX" 
    by (metis \<open>X \<subseteq> Vs G \<and> card X < card ?QX\<close> card_eq_0_iff card_gt_0_iff less_imp_triv)
  have "\<forall> C1 \<in>?QX. \<forall> C2 \<in> ?QX.  C1 \<noteq> C2 \<longrightarrow> ((Vs (?comp_out C1))) \<inter> ((Vs (?comp_out C2))) = {}"
    by (smt (verit, del_insts) \<open>matching M\<close> diff_component_disjoint odd_comps_in_diff_not_in_X 
        disjoint_iff_not_equal doubleton_eq_iff matching_unique_match mem_Collect_eq vs_member)
  then have "\<forall> C1 \<in>?QX. \<forall> C2 \<in> ?QX. 
    C1 \<noteq> C2 \<longrightarrow> ((Vs (?comp_out C1)) \<inter> X) \<inter> ((Vs (?comp_out C2)) \<inter> X) = {}"   
    by blast
  then have "card (\<Union>C \<in>?QX. ((Vs (?comp_out C) \<inter> X))) = 
    sum (\<lambda> C. card (Vs (?comp_out C) \<inter> X)) ?QX"
    using union_card_is_sum[of "?QX" ?f] `\<forall>C \<in> ?QX. finite ((Vs (?comp_out C)) \<inter> X)`
      `finite ?QX`  by presburger
  then  have "sum (\<lambda> C. card ((Vs (?comp_out C)) \<inter> X)) ?QX \<le> card X" 
    by (metis (no_types, lifting) \<open>(\<Union>C \<in>?QX. ((Vs (?comp_out C)) \<inter> X)) \<subseteq> X\<close> 
        \<open>X \<subseteq> Vs M\<close> \<open>finite (Vs M)\<close> card_mono finite_subset)
  then have "sum (\<lambda> C. card (?comp_out C)) ?QX \<le> card X" 
    using \<open>\<forall> C \<in> ?QX. card ((Vs (?comp_out C)) \<inter> X) = card (?comp_out C)\<close> by auto
  then have "\<forall> C \<in> ?QX. finite (?comp_out C)" 
    by (simp add: \<open>finite M\<close>) 
  have "\<forall> C \<in> ?QX. ?comp_out C \<noteq> {}" 
  proof
    fix C
    assume "C \<in> ?QX" 
    show "?comp_out C \<noteq> {}"
    proof(rule ccontr)
      assume "\<not> ?comp_out C \<noteq> {}" 
      then have "?comp_out C = {}" by auto
      have e_in_C:"\<forall> e \<in> M. e \<inter> C = {} \<or> e \<inter> C = e"
      proof(safe)
        fix e x y
        assume assms_edge: "e \<in> M" " x \<in> e" "x \<notin> C" "y \<in> e" "y \<in> C" 
        have "e = {x, y}" 
          using \<open>M \<subseteq> G\<close> \<open>graph_invar G\<close> assms_edge insert_eq_iff by auto
        then have "e \<inter> X = {}" 
          using \<open>C \<in> odd_comps_in_diff G X\<close> \<open>{e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} = {}\<close>
            assms_edge(1) assms_edge(5) odd_comps_in_diff_not_in_X by blast
        then have "e \<in> (graph_diff G X)" 
          using \<open>M \<subseteq> G\<close> \<open>e \<in> M\<close> 
          by (simp add: graph_diffI subsetD)
        then have "x \<in> C"
          by (metis \<open>C \<in> odd_comps_in_diff G X\<close> \<open>e = {x, y}\<close> assms_edge(5) 
                   connected_components_member_sym odd_comps_in_diff_is_component
                   vertices_edges_in_same_component)
        then show "y \<in> {}"  using \<open>x \<notin> C\<close> by auto
      qed
      have " ((Vs M) \<inter> C) = C" 
        by (metis Int_absorb1 \<open>C \<in> odd_comps_in_diff G X\<close> \<open>Vs M = Vs G\<close> component_in_E)
      have "card ((Vs M) \<inter> C) = sum (\<lambda> e. card (e \<inter> C)) M"
        using matching_int_card_is_sum[of M M C]  `matching M`  \<open>finite (Vs M)\<close> by blast
      then have "even (card C)" 
        using \<open>Vs M \<inter> C = C\<close>
        by (smt (verit) "2" \<open>M \<subseteq> G\<close> e_in_C dvd_sum even_numeral odd_card_imp_not_empty subset_eq)
      then show False 
        using diff_odd_compoenent_has_odd_card[of C G X] \<open>C \<in> ?QX\<close> by auto
    qed
  qed
  then have "\<forall> C \<in> ?QX. card(?comp_out C) \<ge> 1"
    by (simp add: \<open>\<forall>C\<in>odd_comps_in_diff G X. finite (?comp_out C)\<close> card_gt_0_iff Suc_leI)  
  then have "sum (\<lambda> C. card (?comp_out C)) ?QX \<ge> card ?QX"
    using sum_mono by fastforce
  then have "card X \<ge> card ?QX"  
    using \<open>sum (\<lambda> C. card (?comp_out C)) ?QX \<le> card X\<close> order_trans by blast
  then show False 
    using \<open>X \<subseteq> Vs G \<and> card X < card ?QX\<close> not_less by blast
qed

lemma odd_comps_in_diff_connected:
  assumes "graph_invar G"
  assumes "tutte_condition G"
  assumes "C \<in> (odd_comps_in_diff G X)" 
  shows "\<exists>x y. x \<in> C \<and> y \<in> X \<and> {x, y} \<in> G"
  using comp_out_nonempty[of G C X] 
  by (smt (verit, best) Collect_empty_eq assms(1) assms(2) assms(3) comp_out_def insert_commute)

definition barrier where
  "barrier G X = ( X \<noteq> {} \<and> card (odd_comps_in_diff G X) = card X)"

lemma diff_components_finite:
  assumes "graph_invar G"
  shows "finite (odd_comps_in_diff G X)" 
  unfolding odd_comps_in_diff_def
proof(safe)
  have "finite (connected_components (graph_diff G (X)))"
    by (meson Vs_subset assms finite_con_comps finite_subset graph_diff_subset)
  have "  (odd_components (graph_diff G X)) \<subseteq> connected_components (graph_diff G X)"
    unfolding odd_components_def connected_components_def 
    using odd_componentE by fastforce
  then show "finite  (odd_components (graph_diff G (X)))" 
    using \<open>finite (connected_components (graph_diff G (X)))\<close> finite_subset by blast
  have "finite (Vs G)"          
    by (simp add: assms)
  have "finite  {{v} |v. v \<in> Vs G}"
  proof -
    have "\<forall>x \<in>  {{v} |v. v \<in> Vs G}. \<exists>c \<in> Vs G. x = {c}"
      by blast
    let ?f = "(\<lambda>c. {{c}})"
    have "{{v} |v. v \<in> Vs G} = (\<Union>c\<in>(Vs G). (?f c))"
    proof(safe) 
      {
        fix x v
        assume "v \<in> Vs G"
        then show "{v} \<in> (\<Union>c\<in>Vs G. {{c}})" 
          by blast
      }
      fix x c
      assume "c \<in> Vs G"
      show "\<exists>v. {c} = {v} \<and> v \<in> Vs G" 
        using \<open>c \<in> Vs G\<close> by blast
    qed
    then show "finite {{v} |v. v \<in> Vs G}" 
      by (simp add: \<open>finite (Vs G)\<close>)
  qed
  have " singl_in_diff G (X) \<subseteq> {{v} |v. v \<in> Vs G}"
    unfolding singl_in_diff_def 
    by blast
  then show "finite ( singl_in_diff G (X))"
    using \<open>finite {{v} |v. v \<in> Vs G}\<close> 
      finite_subset[of "( singl_in_diff G (X))" "{{v} |v. v \<in> Vs G}"]
    by blast
qed

lemma new_components_subset_of_old_one:
  assumes "C' \<in> odd_comps_in_diff (component_edges (graph_diff G X) C) Y"
  shows "C' \<subseteq> Vs (component_edges (graph_diff G X) C)"
  using component_in_E[of C' "(component_edges (graph_diff G X) C)" "Y"]   
  using assms by blast

lemma new_components_in_old_one:
  assumes "graph_invar G"
  assumes "X \<subseteq> Vs G"
  assumes "C \<in> (odd_comps_in_diff G X)"
  shows " Vs  (component_edges (graph_diff G X) C) \<subseteq> C" 
proof
  fix x
  assume "x \<in> Vs (component_edges (graph_diff G X) C)"
  then have "\<exists>e. e \<in> (component_edges (graph_diff G X) C) \<and> x\<in>e"
    by (meson vs_member_elim)
  then obtain e where " e \<in> (component_edges (graph_diff G X) C) \<and> x\<in>e" by auto
  then have "e \<subseteq> C" unfolding component_edges_def  
    by auto
  then show "x\<in>C" 
    using \<open>e \<in> component_edges (graph_diff G X) C \<and> x \<in> e\<close> by auto
qed

lemma new_components_intersection_old_is_empty:
  assumes "graph_invar G"
  assumes "X \<subseteq> Vs G"
  assumes "C \<in> (odd_comps_in_diff G X)"
  assumes "Y \<subseteq> C"
  shows "(odd_comps_in_diff G X - {C}) \<inter> 
 odd_comps_in_diff (component_edges (graph_diff G X) C) Y= {}" 
proof(rule ccontr)
  assume "(odd_comps_in_diff G X - {C}) \<inter>
    odd_comps_in_diff (component_edges (graph_diff G X) C) Y \<noteq> {}"
  then obtain C' where C':"C' \<in> (odd_comps_in_diff G X - {C}) \<inter>
    odd_comps_in_diff (component_edges (graph_diff G X) C) Y"
    by (meson ex_in_conv)
  then have "C' \<subseteq> C" using new_components_in_old_one[of G X C]
      new_components_subset_of_old_one[of C' G X C Y] assms(1-3)
     by auto
  have "\<forall>C'\<in>odd_comps_in_diff G X - {C}. C' \<inter> C = {}" 
    by (metis DiffD2  assms(3) diff_component_disjoint insert_Diff insert_iff)
  have "C' \<inter> C = {}" 
    by (meson IntD1 C' \<open>\<forall>C'\<in>odd_comps_in_diff G X - {C}. C' \<inter> C = {}\<close>)
  then have "C' = {}" 
    using \<open>C' \<subseteq> C\<close> by auto
  have "C' \<noteq> {}"
    using C' assms(1) odd_components_nonempty by fastforce
  then show False 
    by (simp add: \<open>C' = {}\<close>)
qed

lemma max_barrier_add_vertex_empty_odd_components:
  assumes "graph_invar G"
  assumes "tutte_condition G"
  assumes "X \<subseteq> Vs G"
  assumes "barrier G X"
  assumes "\<forall> Y \<in> {Z. Z \<subseteq> Vs G \<and> barrier G Z}. Y \<noteq> X \<longrightarrow> \<not> (X \<subseteq> Y)"
  assumes "C \<in> (odd_comps_in_diff G X)"
  assumes "x \<in> C"
  shows "odd_comps_in_diff (component_edges (graph_diff G X) C) {x} = {}" (is "?docX = {}")
proof(rule ccontr)
  assume asm: "?docX \<noteq> {}"
  have "{x} \<noteq> {}" 
    by simp
  have odd_diffUn:"odd_comps_in_diff G (X \<union> {x}) =
 odd_comps_in_diff G X - {C} \<union> odd_comps_in_diff (component_edges (graph_diff G X) C) {x}"
    using add_subset_change_odd_components[of G X C "{x}"] assms by auto
  have "graph_invar (component_edges (graph_diff G X) C)" 
    by (smt (verit) Connected_Components.component_edges_subset assms(1) graph_diff_subset graph_invar_subset)
  have "finite ?docX" 
    using diff_components_finite[of "(component_edges (graph_diff G X) C)"]
    using \<open>graph_invar (component_edges (graph_diff G X) C)\<close> by blast
  then have "card ?docX \<ge> 1" 
    by (simp add: Suc_leI asm card_gt_0_iff)
  have "card (odd_comps_in_diff G (X\<union>{x})) \<le> card (X\<union>{x})"
    using assms(2) unfolding tutte_condition_def 
    by (metis Un_insert_right assms(3) assms(6) assms(7) boolean_algebra_cancel.sup0 component_in_E 
        insert_subset subsetD)
  then have "card (odd_comps_in_diff G (X\<union>{x}))\<le> card X +1" 
    by (metis One_nat_def Un_insert_right  add.right_neutral add_Suc_right assms(1) assms(3) 
        boolean_algebra_cancel.sup0 card.insert finite_subset insert_absorb trans_le_add1)
  have "card (odd_comps_in_diff G X) = card X" 
    using assms(4) barrier_def by blast
  have "card ((odd_comps_in_diff G X) - {C}) = card X - 1" 
    by (simp add: \<open>card (odd_comps_in_diff G X) = card X\<close> assms(6))
  then have "card (odd_comps_in_diff G (X\<union>{x})) \<le> (card X - 1) + 2" 
    using \<open>card (odd_comps_in_diff G (X \<union> {x})) \<le> card X + 1\<close> by linarith
  then have "card (odd_comps_in_diff G (X\<union>{x})) \<le> card ((odd_comps_in_diff G X) - {C}) + 2"
    using \<open>card (odd_comps_in_diff G X - {C}) = card X - 1\<close> by presburger
  then have card2: "card (odd_comps_in_diff G X - {C} \<union> 
             odd_comps_in_diff (component_edges (graph_diff G X) C) {x})
            \<le> card ((odd_comps_in_diff G X) - {C}) + 2" 
    using odd_diffUn by auto
  have "\<forall>C' \<in> (odd_comps_in_diff G X - {C}). C' \<inter> C = {}"
    by (metis DiffD1 DiffD2  assms(6) diff_component_disjoint insert_iff)
  then have "Vs (odd_comps_in_diff G X - {C}) \<inter> C = {}" 
    by (smt (verit, ccfv_SIG) Int_ac(3) Vs_def assms(1) assms(6)
        diff_component_disjoint disjoint_iff_not_equal insert_Diff insert_partition)
  then have "card ?docX \<le> 2" 
    by (smt (verit, ccfv_SIG) Int_lower2 Nat.le_diff_conv2 Un_upper1 
        card2 \<open>finite ?docX\<close> add.commute assms(1-4,6-7) card_Un_disjoint card_mono diff_add_inverse 
        diff_components_finite finite_Diff finite_Un insert_subset le_antisym nat_le_linear
        new_components_intersection_old_is_empty)
  show False
  proof(cases "card ?docX = 2")
    case True
    then have "card (odd_comps_in_diff G (X\<union>{x})) = card X + 1" 
      using  new_components_intersection_old_is_empty[of G X C "{x}"] 
      by (smt (verit, best) Int_lower2 Nat.add_diff_assoc Nat.add_diff_assoc2 One_nat_def Suc_leI 
          \<open>1 \<le> card (odd_comps_in_diff (component_edges (graph_diff G X) C) {x})\<close> 
          \<open>Vs (odd_comps_in_diff G X - {C}) \<inter> C = {}\<close> 
          \<open>card (odd_comps_in_diff G X - {C}) = card X - 1\<close> 
         odd_diffUn \<open>finite (odd_comps_in_diff (component_edges (graph_diff G X) C) {x})\<close> 
          assms(1) assms(2) assms(3) assms(4) assms(6) assms(7) barrier_def card_Un_disjoint
          card_gt_0_iff diff_add_inverse2 finite_Diff finite_subset insert_subsetI one_add_one)
    then have "card (odd_comps_in_diff G (X\<union>{x})) = card (X\<union>{x})" 
      by (metis One_nat_def Un_insert_right \<open>card (odd_comps_in_diff G X) = card X\<close> 
          add.right_neutral add_Suc_right assms(1) assms(3) card.insert finite_subset 
          insert_absorb sup_bot_right)
    then have "barrier G (X\<union>{x})"
      by (simp add: barrier_def)
    have "X \<subseteq> (X\<union>{x})" 
      by auto
    then show ?thesis using assms(5) `barrier G (X\<union>{x})`  
      by (metis (no_types, lifting) One_nat_def Un_subset_iff 
          \<open>card (odd_comps_in_diff G (X \<union> {x})) = card X + 1\<close> diff_is_0_eq'
          \<open>card (odd_comps_in_diff G (X \<union> {x})) \<le> card (X \<union> {x})\<close> assms(3,6-7) 
          component_in_E diff_add_inverse insert_Diff insert_is_Un mem_Collect_eq nat.simps(3))
  next
    case False
    then have " card (odd_comps_in_diff (component_edges(graph_diff G X) C) {x})  = 1" 
      using \<open>1 \<le> card (odd_comps_in_diff (component_edges (graph_diff G X) C) {x})\<close> 
            \<open>card (odd_comps_in_diff (component_edges (graph_diff G X) C) {x}) \<le> 2\<close> by linarith
    then have "\<exists>!C'. C' \<in> (odd_comps_in_diff (component_edges(graph_diff G X) C) {x})"
      by (metis card_1_singletonE empty_iff insert_iff)
    have "(odd_comps_in_diff G X - {C}) \<inter> 
          odd_comps_in_diff (component_edges (graph_diff G X) C) {x} = {}"
      using  new_components_intersection_old_is_empty[of G X C "{x}"] assms 
      by simp
    then have "Vs (component_edges(graph_diff G X) C) = C" 
      by (smt (verit, best) IntI Nat.add_diff_assoc2 One_nat_def Suc_leI Un_insert_right 
         \<open>card (odd_comps_in_diff (component_edges (graph_diff G X) C) {x}) = 1\<close>
         \<open>card (odd_comps_in_diff G X - {C}) = card X - 1\<close> \<open>card (odd_comps_in_diff G X) = card X\<close>
        odd_diffUn \<open>finite (odd_comps_in_diff (component_edges (graph_diff G X) C) {x})\<close> 
        add.right_neutral add_Suc_right assms(1) assms(3) assms(6) assms(7) 
        boolean_algebra_cancel.sup0 card.empty card.insert card_Un_disjoint card_gt_0_iff 
        component_in_E diff_add_inverse2 diff_components_finite diff_is_0_eq'
        diff_odd_component_parity odd_comps_in_diff_not_in_X empty_iff finite_Diff insert_subset
        nat_le_linear odd_card_imp_not_empty odd_one subsetD)
    then show ?thesis 
      by (smt (verit, ccfv_threshold) IntI Nat.add_diff_assoc2 One_nat_def Suc_leI Un_insert_right 
         \<open>(odd_comps_in_diff G X - {C}) \<inter> 
          odd_comps_in_diff (component_edges (graph_diff G X) C) {x} = {}\<close> 
          \<open>card (odd_comps_in_diff (component_edges (graph_diff G X) C) {x}) = 1\<close> 
          \<open>card (odd_comps_in_diff G X - {C}) = card X - 1\<close> \<open>card (odd_comps_in_diff G X) = card X\<close> 
          \<open>odd_comps_in_diff G (X \<union> {x}) = odd_comps_in_diff G X - {C} \<union> 
          odd_comps_in_diff (component_edges (graph_diff G X) C) {x}\<close>
          \<open>finite (odd_comps_in_diff (component_edges (graph_diff G X) C) {x})\<close> 
          add_Suc_right assms(1) assms(2) assms(3) assms(6) assms(7) boolean_algebra_cancel.sup0 
          card.empty card.insert card_Un_disjoint card_gt_0_iff component_in_E diff_add_inverse2 
          diff_components_finite diff_is_0_eq' diff_odd_component_parity odd_comps_in_diff_not_in_X 
          empty_iff finite_Diff insert_subset le_iff_add odd_card_imp_not_empty odd_one subsetD 
          tutte_condition_def)
  qed
qed

lemma max_barrier_add_vertex_doesnt_increase_odd_components:
  assumes "graph_invar G"
  assumes "tutte_condition G"
  assumes "X \<subseteq> Vs G"
  assumes "barrier G X"
  assumes "\<forall> Y \<in> {Z. Z \<subseteq> Vs G \<and> barrier G Z}. Y \<noteq> X \<longrightarrow> \<not> (X \<subseteq> Y)"
  assumes "C \<in> (odd_comps_in_diff G X)"
  assumes "x \<in> C"
  shows "odd_comps_in_diff G (X\<union>{x}) = (odd_comps_in_diff G X) - {C}"
proof -
  have "{x} \<noteq> {}" 
    by simp
  have 1: "odd_comps_in_diff G (X \<union> {x}) =
 odd_comps_in_diff G X - {C} \<union> odd_comps_in_diff (component_edges (graph_diff G X) C) {x}"
    using add_subset_change_odd_components[of G X C "{x}"] assms by auto
  let ?docX = "odd_comps_in_diff (component_edges (graph_diff G X) C) {x}"
  have "?docX = {}" 
    by (simp add: assms max_barrier_add_vertex_empty_odd_components)
  then show " odd_comps_in_diff G (X \<union> {x}) = odd_comps_in_diff G X - {C}"
    using 1 by auto
qed

lemma component_edges_same_in_diff:
  assumes "C \<in> odd_comps_in_diff G X"
  shows  "(component_edges (graph_diff G X) C) = (component_edges G C)"
proof - 
  have "\<forall>e \<subseteq> C. e \<in> G \<longrightarrow> e \<in> graph_diff G X"
  proof(safe)
    fix e
    assume "e \<subseteq> C" "e \<in> G"
    then have "e \<inter> X = {}" 
      using assms odd_comps_in_diff_not_in_X by blast
    then show "e \<in> graph_diff G X" unfolding graph_diff_def 
      by (simp add: \<open>e \<in> G\<close>)
  qed
  then show ?thesis      unfolding component_edges_def 
    by (meson graph_diff_subset subsetD)
qed

lemma graph_diff_trans:
  assumes "graph_invar G"
  shows "graph_diff G (X\<union>Y) = graph_diff (graph_diff G X) Y"
  unfolding graph_diff_def
  by (simp add: inf_sup_distrib1)

lemma vertices_of_edges_in_component_same:
  assumes "graph_invar G"
  assumes "X \<subseteq> Vs G"
  assumes "C \<in> odd_components (graph_diff G X)"
  shows " Vs (component_edges G C) = C"
proof(safe)
  {
    fix x
    assume "x \<in> Vs (component_edges G C)"
    then obtain e where " x \<in> e \<and> e \<in> (component_edges G C)" 
      by (meson vs_member_elim)
    have "C \<in> odd_comps_in_diff G X" 
      by (simp add: assms(3) odd_comps_in_diff_def)
    then have "e \<subseteq> C" using `x \<in> e \<and> e \<in> (component_edges G C)` 
      unfolding component_edges_def 
      by blast
    then show "x \<in> C" 
      using \<open>x \<in> e \<and> e \<in> component_edges G C\<close> by blast
  }
  fix x
  assume "x \<in> C"
  then have "x \<in> Vs (graph_diff G X) \<and> connected_component (graph_diff G X) x = C \<and> odd (card C)"
    by (meson assms(3) odd_component_def odd_component_is_component odd_componentsE 
        odd_components_elem_in_E subsetD)
  then obtain e where "x \<in> e \<and> e \<in> (graph_diff G X)" 
    by (meson vs_member_elim)
  have "graph_invar  (graph_diff G X)"
    by (simp add: assms(1) graph_invar_diff)
  then obtain x' y where  " e = {x', y}"
    using `x \<in> e \<and> e \<in> (graph_diff G X)`
    by blast
  then have "connected_component (graph_diff G X) x' = C" 
    by (metis \<open>x \<in> Vs (graph_diff G X) \<and> connected_component (graph_diff G X) x = C \<and> odd (card C)\<close> 
        \<open>x \<in> e \<and> e \<in> graph_diff G X\<close> connected_components_member_eq insert_iff singletonD 
        vertices_edges_in_same_component)
  then have "connected_component (graph_diff G X) y = C" using ` e = {x', y}`
    by (metis  \<open>x \<in> e \<and> e \<in> graph_diff G X\<close> connected_components_member_eq
        vertices_edges_in_same_component)
  then have "e \<subseteq> C" 
    by (metis \<open>connected_component (graph_diff G X) x' = C\<close> \<open>e = {x', y}\<close> 
        \<open>x \<in> e \<and> e \<in> graph_diff G X\<close> connected_components_member_sym insert_subset singletonD 
        subsetI vertices_edges_in_same_component)
  then have "e \<in> (component_edges G C)" unfolding component_edges_def 
    using \<open>e = {x', y}\<close> \<open>x \<in> e \<and> e \<in> graph_diff G X\<close> graph_diff_subset insert_Diff insert_subset 
    by fastforce
  then show "x \<in> Vs  (component_edges G C)" 
    using \<open>x \<in> e \<and> e \<in> graph_diff G X\<close> by blast
qed


lemma possible_connected_vertices_in_expanded_graph_intersection:
  assumes "graph_invar G"
  assumes "X \<subseteq> Vs G"
  assumes "C \<in> odd_comps_in_diff G X"
  assumes "x' \<in> C"
  assumes "{connected_component (graph_diff G X) x', {y'}} \<in> M'"
  assumes "matching M'" 
  assumes "y' \<in> X"
  shows " Vs {{c. \<exists>e. e \<in> G \<and> e = {c, y} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff G X) x}
     |x y. y\<in> X \<and> {connected_component (graph_diff G X) x, {y}} \<in> M'} \<inter> C =
    {c. \<exists>e. e \<in> G \<and> e = {c, y'} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff G X) x'}" 
    (is "Vs ?Z2 \<inter> C = ?C'")
proof
  have 1:"connected_component (graph_diff G X) x' = C" 
    by (simp add: assms(1) assms(3) assms(4) odd_comps_in_diff_is_component)
  show "Vs ?Z2 \<inter> C \<subseteq> ?C'"
  proof
    fix z
    assume asmz:"z\<in> Vs ?Z2 \<inter> C"
    then have "\<exists>C' \<in> ?Z2. z \<in> C'" 
      by (meson IntD1 vs_member_elim)
    then obtain C' where C':"C' \<in> ?Z2 \<and> z \<in> C'" by blast
    then have "\<exists>x1 y1. C' = {c . \<exists> e. e \<in> G \<and> e = {c, y1}  \<and> c \<notin> X
                     \<and> c \<in> connected_component (graph_diff G X) x1} \<and> y1 \<in> X
        \<and> {connected_component (graph_diff G X) x1, {y1}} \<in> M'" by auto
    then obtain x1 y1 where x1y1:"C' = {c . \<exists> e. e \<in> G \<and> e = {c, y1}  \<and> c \<notin> X
                     \<and> c \<in> connected_component (graph_diff G X) x1}  \<and> y1 \<in> X
        \<and> {connected_component (graph_diff G X) x1, {y1}} \<in> M'" by auto
    then have " z \<in> connected_component (graph_diff G X) x1"
      using C' by auto
    then have " connected_component (graph_diff G X) z = connected_component (graph_diff G X) x1"
      by (metis (no_types, lifting) connected_components_member_eq)
    then have 2:"C' = {c . \<exists> e. e \<in> G \<and> e = {c, y1}  \<and> c \<notin> X
                     \<and> c \<in> connected_component (graph_diff G X) z}  \<and> y1 \<in> X
        \<and> {connected_component (graph_diff G X) z, {y1}} \<in> M'" 
      using x1y1 by presburger
    have "connected_component (graph_diff G X) x' = C" 
      by (simp add: 1)
    then have 3:"connected_component (graph_diff G X) z = connected_component (graph_diff G X) x'"
      using asmz connected_components_member_eq by force
    then have 4:"{connected_component (graph_diff G X) z, {y1}} \<inter>
                    {connected_component (graph_diff G X) x', {y'}} \<noteq> {}"
      by simp
    have "matching M'" 
      using assms(6) by blast 
    then have "{connected_component (graph_diff G X) z, {y1}} = 
               {connected_component (graph_diff G X) x', {y'}}"
      by (meson 2 4 assms(5) matching_def)
    then have "y1 = y'" 
      by (metis (full_types) 3 doubleton_eq_iff)
    then have "C' = ?C'" 
      using 2 3 by presburger
    then show "z \<in> ?C'" 
      using C' by blast
  qed
  show "?C' \<subseteq> Vs ?Z2 \<inter> C" 
  proof
    fix z
    assume asmz:"z \<in> ?C'"
    then have ex1:"\<exists>e. e \<in> G \<and> e = {z, y'} \<and> z \<notin> X \<and> z \<in> connected_component (graph_diff G X) x'"
      by blast
    then have "z \<in> C"
      by (simp add: 1)
    then have "{connected_component (graph_diff G X) z, {y'}} \<in> M'" 
      using ex1 assms(5) connected_components_member_eq by force
    have "?C' \<in> ?Z2"
    proof(safe)
      have " {c. \<exists>e. e \<in> G \<and> e = {c, y'} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff G X) x'} =
          {c. \<exists>e. e \<in> G \<and> e = {c, y'} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff G X) x'}" 
        by blast
      then have "{c. \<exists>e. e \<in> G \<and> e = {c, y'} \<and> c \<notin> X \<and> 
            c \<in> connected_component (graph_diff G X) x'} =
          {c. \<exists>e. e \<in> G \<and> e = {c, y'} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff G X) x'} 
          \<and>  y' \<in> X \<and> {connected_component (graph_diff G X) x', {y'}} \<in> M'" 
        using assms(5) 
        using assms(7) by blast
      then show " \<exists>x y. {c. \<exists>e. e \<in> G \<and> e = {c, y'} \<and> c \<notin> X \<and> 
                  c \<in> connected_component (graph_diff G X) x'} =
          {c. \<exists>e. e \<in> G \<and> e = {c, y} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff G X) x}
           \<and> y \<in> X \<and> {connected_component (graph_diff G X) x, {y}} \<in> M'" 
        using Collect_cong by auto
    qed
    then show "z \<in> Vs ?Z2 \<inter> C" 
      by (metis (no_types, lifting) IntI \<open>z \<in> C\<close> asmz vs_member_intro)
  qed
qed

lemma subset_graph_finite:
  assumes "finite A"
  shows "finite {{X, Y}| X Y.  X \<subseteq> A \<and> Y \<subseteq> A}" (is "finite ?UA")
proof -
  have "finite {(X, Y) |X Y. X \<subseteq> A \<and> Y \<subseteq> A}"
    using assms by auto
  let ?f = "(\<lambda>(X, Y). {{X, Y}})" 
  have "{{X, Y}| X Y.  X \<subseteq> A \<and> Y \<subseteq> A} =  (\<Union>a\<in>{(X, Y) |X Y. X \<subseteq> A \<and> Y \<subseteq> A}. ?f a)"
  proof(safe)
  qed (auto)
  then show ?thesis 
    using \<open>finite {(X, Y) |X Y. X \<subseteq> A \<and> Y \<subseteq> A}\<close> by auto
qed

lemma union_of_set_finite:
  assumes "finite A"
  assumes "\<forall>a \<in> A. finite a"
  shows "finite (\<Union>A)" 
  using assms(1) assms(2) by blast

lemma new_component_subset_old:
  assumes "graph_invar G"
  assumes "Y \<subseteq> X"
  shows "connected_component (graph_diff G X) u \<subseteq> connected_component (graph_diff G Y) u"
  by (metis assms(1) assms(2) con_comp_subset graph_diff_subset graph_diff_trans subset_Un_eq)

lemma new_component_is_old:
  assumes "graph_invar G"
  assumes "Y \<subseteq> X"
  assumes "\<forall>y\<in>connected_component (graph_diff G Y) u. y \<notin> X"
  shows "connected_component (graph_diff G X) u = connected_component (graph_diff G Y) u"
proof
  show "connected_component (graph_diff G Y) u \<subseteq> connected_component (graph_diff G X) u"
  proof 
    fix y
    assume asmy:"y \<in> connected_component (graph_diff G Y) u" 
    then have "y \<notin> X" 
      using assms(3) by blast
    have "y = u \<or> (\<exists>p. walk_betw (graph_diff G Y) u p y)" 
      by (meson \<open>y \<in> connected_component (graph_diff G Y) u\<close> in_con_comp_has_walk)
    show "y \<in> connected_component (graph_diff G X) u"
    proof(cases "y = u")
      case True
      then show ?thesis 
        using \<open>y \<in> connected_component (graph_diff G Y) u\<close> assms(3) 
        by (simp add: in_own_connected_component)
    next
      case False
      then obtain p where p: "walk_betw (graph_diff G Y) y p u" 
        by (meson \<open>y = u \<or> (\<exists>p. walk_betw (graph_diff G Y) u p y)\<close> walk_symmetric)
      have 1:"set (edges_of_path p) \<subseteq> (graph_diff G Y)" 
        by (meson p path_edges_subset walk_between_nonempty_pathD(1))
      have "\<forall>x\<in>set p. x \<in>  connected_component (graph_diff G Y) u" 
        by (metis p asmy connected_components_member_eq path_subset_conn_comp subsetD 
            walk_between_nonempty_pathD)
      then have "\<forall>x\<in>set p. x \<notin> X" 
        using assms(3) by blast
      have "set (edges_of_path p) \<subseteq> (graph_diff G X)" 
      proof
        fix e
        assume asme:"e \<in> set (edges_of_path p)" 
        then have "e \<inter> X = {}" 
          by (meson Int_emptyI \<open>\<forall>x\<in>set p. x \<notin> X\<close> v_in_edge_in_path_gen)
        then show "e \<in>  (graph_diff G X)" 
          by (metis (mono_tags, lifting) asme 1 graph_diff_def mem_Collect_eq subsetD)
      qed
      then have "walk_betw (graph_diff G X) y p u" 
        by (smt (z3) False One_nat_def Suc_1 Suc_leI Suc_lessI p diff_is_0_eq'
            edges_of_path.simps(1) edges_of_path_Vs edges_of_path_length empty_iff
            empty_set in_edges_of_path last_in_set length_pos_if_in_set neq0_conv 
            path_edges_of_path_refl path_subset subset_empty walk_betw_def)
      then show ?thesis 
        by (meson connected_components_member_sym has_path_in_connected_component)
    qed
  qed
  show "connected_component (graph_diff G X) u \<subseteq> connected_component (graph_diff G Y) u" 
    by (simp add: assms(1) assms(2) new_component_subset_old)
qed

lemma every_el_in_barrier_connected:
  assumes "graph_invar G"
  assumes "tutte_condition G"
  assumes "X \<subseteq> Vs G"
  assumes "barrier G X"
  shows"\<forall>x \<in>X. \<exists>y \<in>Vs G - X. {x, y} \<in> G"
proof
  fix x
  assume "x \<in> X"
  show "\<exists>y \<in>Vs G - X. {x, y} \<in> G"
  proof(rule ccontr)
    assume "\<not> (\<exists>y\<in>Vs G - X.  {x, y} \<in> G)"
    then have "\<forall>e \<in> G. x \<in> e \<longrightarrow> e \<subseteq> X"
      by (smt (verit) Diff_iff \<open>x \<in> X\<close> assms(1) dblton_graphE insert_Diff insert_commute insert_iff
              subset_eq vs_member_intro)
    have diff_same:"(graph_diff G X) = (graph_diff G (X - {x}))"
      unfolding graph_diff_def 
      using \<open>\<forall>e\<in>G. x \<in> e \<longrightarrow> e \<subseteq> X\<close> assms(1) by fastforce
    then have "odd_components (graph_diff G X) = odd_components (graph_diff G (X - {x}))"
      by presburger
    have "(singl_in_diff G X) \<union> {{x}} = singl_in_diff G (X-{x})"
      unfolding singl_in_diff_def
      apply safe 
        apply (simp add: diff_same)+
       apply (metis Diff_iff diff_same \<open>x \<in> X\<close> assms(3) subsetD vs_graph_diff)
      using diff_same apply fastforce
      done
    then have "(odd_comps_in_diff G X) \<union> {{x}} = odd_comps_in_diff G (X-{x})" 
      unfolding odd_comps_in_diff_def using diff_same by auto
    then have 2:"card (odd_comps_in_diff G (X-{x})) = card ((odd_comps_in_diff G X) \<union> {{x}})" 
      by presburger
    have "(odd_comps_in_diff G X) \<inter> {{x}} = {}" 
      using \<open>x \<in> X\<close> odd_comps_in_diff_not_in_X by blast
    then have "card (odd_comps_in_diff G (X-{x})) = 
        card (odd_comps_in_diff G X) + card {{x}}" 
      by (metis 2 assms(1) card_Un_disjoint diff_components_finite finite.emptyI finite.insertI)
    then have 3:"card (odd_comps_in_diff G (X-{x})) = card X + 1" 
      by (metis One_nat_def assms(4) barrier_def card.empty card.insert finite.emptyI 
          insert_absorb insert_not_empty)
    have "card (odd_comps_in_diff G (X-{x})) \<le> card (X-{x})" 
      by (metis \<open>x \<in> X\<close> assms(2) assms(3) insert_Diff insert_subset tutte_condition_def)
    then show False 
      by (metis One_nat_def 3 card.empty card_Diff1_le card_gt_0_iff diff_add_inverse diff_is_0_eq' 
          le_trans zero_less_Suc)
  qed
qed

lemma singleton_set_is_union_singletons:
  assumes "finite X"
  shows "(\<Union>x\<in>X. {{x}}) = {{x} |x. x \<in> X}"
  by (safe;auto)

lemma card_singleton_set_same:
  assumes "finite X"
  assumes "A \<subseteq> {{x}|x. x \<in> X}"
  shows "card A = card {a. {a} \<in> A}" 
proof -
  let ?f = "(\<lambda>x. {{x}})" 
  have "A = (\<Union>x\<in>{a. {a} \<in> A}. ?f x)" 
  proof(safe)
    fix a
    assume "a \<in> A"
    then obtain x where "a = {x}" 
      using assms by blast
    then have "x \<in> {a. {a} \<in> A}"
      using \<open>a \<in> A\<close> by fastforce
    show "a \<in> (\<Union>x\<in>{a. {a} \<in> A}. {{x}})" 
      using \<open>a = {x}\<close> \<open>x \<in> {a. {a} \<in> A}\<close> by blast
  qed
  have "finite {{x}|x. x \<in> X}"
    using assms(1) by auto 
  then have "finite A" 
    using assms(2) finite_subset by blast
  then have 1:"finite {a. {a} \<in> A}" 
    using `A \<subseteq> {{x}|x. x \<in> X}`
  proof(induct A) 
    case empty
    then show ?case 
      by simp
  next
    case (insert x F)
    obtain a where "x = {a}" 
      using insert.prems by auto
    have "{a. {a} \<in> insert x F} =  {a. {a} \<in> F} \<union> {a}"
      using \<open>x = {a}\<close> by safe
    then show "finite {a. {a} \<in> insert x F}" 
      using insert.hyps(3) insert.prems by force
  qed
  have 2:"\<forall>C\<in>{a. {a} \<in> A}. finite {{C}}"
    by auto
  have " \<forall>C1\<in>{a. {a} \<in> A}. \<forall>C2\<in>{a. {a} \<in> A}. C1 \<noteq> C2 \<longrightarrow> {{C1}} \<inter> {{C2}} = {} " 
    by blast
  then have "card (\<Union>x\<in>{a. {a} \<in> A}. ?f x) =  sum (\<lambda>x. (card (?f x))) {a. {a} \<in> A}" 
    using union_card_is_sum[of "{a. {a} \<in> A}" ?f] 
    using 1 2 by presburger
  then have "card (\<Union>x\<in>{a. {a} \<in> A}. ?f x) = card {a. {a} \<in> A}" 
    by (metis (no_types, lifting) One_nat_def card.empty card.insert card_eq_sum empty_iff 
        finite.intros(1) sum.cong)
  then show "card A = card {a. {a} \<in> A}" 
    using \<open>A = (\<Union>x\<in>{a. {a} \<in> A}. {{x}})\<close> by simp
qed

lemma vertices_path_in_component:
  assumes "walk_betw G u p v"
  shows "\<forall>x\<in> set p. x \<in> connected_component G u"
  by (metis assms path_subset_conn_comp subsetD walk_between_nonempty_pathD(1,3))

lemma tutte2:
  assumes "graph_invar G"
  assumes "tutte_condition G"
  shows "\<exists>M. perfect_matching G M" 
  using assms
proof(induction "card (Vs G)" arbitrary: G rule: less_induct) 
  case less
  show "\<exists>M. perfect_matching G M"
  proof(cases "card (Vs G) \<le> 2")
    case True
    then show ?thesis
    proof(cases "card (Vs G) = 2")
      case True
      then obtain x y where "x \<in> Vs G \<and> y \<in> Vs G \<and> x \<noteq> y" 
        by (meson card_2_iff')
      then have "{x, y} =  Vs G" using True 
        by (smt (verit, best) card_2_iff doubleton_eq_iff insert_absorb insert_iff)
      have "\<forall> e \<in> G. e = {x, y}"
      proof
        fix e
        assume "e \<in> G"
        show "e = {x, y}"
        proof(rule ccontr)
          assume " e \<noteq> {x, y}"
          then obtain u where "u \<in> e \<and> (u \<noteq> x \<and> u \<noteq> y)"
            using \<open>e \<in> G\<close> less.prems(1)
            by blast
          then have "u \<in> Vs G"
            using \<open>e \<in> G\<close> by blast
          then show False 
            using \<open>u \<in> e \<and> u \<noteq> x \<and> u \<noteq> y\<close> \<open>{x, y} = Vs G\<close> by blast
        qed
      qed
      then have "G = {{x, y}}" 
        using \<open>x \<in> Vs G \<and> y \<in> Vs G \<and> x \<noteq> y\<close> vs_member by fastforce
      then have "matching G" 
        using matching_def by fastforce
      moreover have "G \<subseteq> G" by auto
      ultimately have "perfect_matching G G"
        unfolding perfect_matching_def
        using "less.prems"(1) by blast
      then show ?thesis by auto
    next
      case False
      then show ?thesis
      proof(cases "card (Vs G) = 1")
        case True
        then show ?thesis 
          apply(elim card_1_singletonE)
          by (metis edges_are_Vs graph_invar_edgeD graph_invar_vertex_edgeE' less.prems(1)
                    singleton_iff)
      next
        case False
        then have "card (Vs G) = 0" 
          using `card (Vs G) \<le> 2` `card (Vs G) \<noteq> 2` 
          by linarith
        then show ?thesis
          unfolding perfect_matching_def matching_def2
          using less.prems(1) by auto
      qed
    qed
  next
    case False
    have "even (card (Vs G))"
    proof(rule ccontr)
      assume "odd (card (Vs G))"
      have " {} \<subseteq> G" by auto
      then have "card (odd_comps_in_diff G {}) \<le> card {}" 
        by (metis "less.prems"(2) bot.extremum card.empty tutte_condition_def)
      then have card0:"card (odd_comps_in_diff G {}) = 0"
        by simp
      have "graph_diff G {} = G" 
        by (simp add: graph_diff_def)
      then have "(singl_in_diff G {}) = {}" 
        unfolding singl_in_diff_def 
        by simp
      then have "odd_comps_in_diff G {} = odd_components G"
        unfolding odd_comps_in_diff_def using `graph_diff G {} = G`
        by simp
      then have "card (odd_components G) \<ge> 1"
        using `odd (card (Vs G))`
        by (metis even_zero le_less_linear less.prems(1) less_one
            odd_components_eq_modulo_cardinality)
      then show False
        using card0 \<open>odd_comps_in_diff G {} = odd_components G\<close> by force
    qed
    have 1:"\<forall>x \<in> (Vs G). card {x} \<ge> card (odd_comps_in_diff G {x})"
      using "less.prems"(2) 
      by (meson bot.extremum insert_subsetI tutte_condition_def)
    then  have "\<forall>x \<in> (Vs G). even (card {x} - card (odd_comps_in_diff G {x}))" 
      using `even (card (Vs G))` diff_odd_component_parity
      by (metis "less.prems"(1) bot.extremum insert_subsetI)
    then have 21:"\<forall>x \<in> (Vs G).card (odd_comps_in_diff G {x}) = 1"
      by (metis One_nat_def Suc_leI 1 antisym_conv card.empty card.insert dvd_diffD empty_iff 
          finite.emptyI not_less odd_card_imp_not_empty odd_one zero_order(2))
    then have "\<forall>x \<in> (Vs G). barrier G {x}"
      by (metis barrier_def insert_not_empty is_singleton_altdef is_singleton_def)
    then have exBarr:"\<exists> X \<subseteq> Vs G. barrier G X" 
      by (metis "less.prems"(1) False Suc_leI card.empty finite.simps insertCI insert_is_Un 
          le_less_linear nat.simps(3) sup_ge1 zero_order(2))
    let ?B = "{X. X \<subseteq> Vs G \<and> barrier G X}"
    have "finite (Vs G)" 
      by (simp add: "less.prems"(1))
    then  have "finite ?B" by auto
    then  have "\<exists>X \<in> ?B. \<forall> Y \<in> ?B. Y \<noteq> X \<longrightarrow> \<not> (X \<subseteq> Y)" 
      by (metis (no_types, lifting) exBarr empty_iff finite_has_maximal mem_Collect_eq)
    then obtain X where X_max:"X \<in> ?B \<and> ( \<forall> Y \<in> ?B. Y \<noteq> X \<longrightarrow> \<not> (X \<subseteq> Y))"
      by meson
    then have X_barr:"X \<subseteq> Vs G \<and> barrier G X" 
      by auto
    then have "card (odd_comps_in_diff G X) = card X" 
      unfolding barrier_def by auto
    have "even_components (graph_diff G X) = {}"
    proof(rule ccontr)
      assume " even_components (graph_diff G X) \<noteq> {}"
      then obtain C where C:"C \<in>  even_components (graph_diff G X)" 
        by auto
      then have 2: "\<exists>v\<in>Vs (graph_diff G X). connected_component (graph_diff G X) v = C"
        by (simp add:  even_components_def)
      then obtain v where "v \<in> C"
        by (smt (verit) even_components_def in_own_connected_component mem_Collect_eq)
      then have comp_C:"connected_component (graph_diff G X) v = C"
        by (metis 2 connected_components_member_eq)
      have 6:"singl_in_diff G X \<subseteq> singl_in_diff G (X \<union> {v})"
      proof
        fix xs
        assume "xs \<in> singl_in_diff G X"
        then have "\<exists>x. xs = {x} \<and> x \<in> Vs G \<and> x \<notin> X \<and> x \<notin> Vs (graph_diff G X)" 
          unfolding singl_in_diff_def by auto
        then obtain x where x:"xs = {x} \<and> x \<in> Vs G \<and> x \<notin> X \<and> x \<notin> Vs (graph_diff G X)" 
          by presburger
        then have "x \<notin> X \<union> {v}" 
          by (metis UnE 2 \<open>v \<in> C\<close> in_connected_component_in_edges singletonD)
        have "x \<notin> Vs (graph_diff G X)" 
          by (simp add: x)
        then have "x \<notin> Vs (graph_diff G (X \<union> {v}))" 
          unfolding graph_diff_def
          by (simp add: vs_member)
        then have "{x} \<in> singl_in_diff G (X \<union> {v})" 
          unfolding singl_in_diff_def
          using \<open>x \<notin> X \<union> {v}\<close> x by blast
        then show "xs \<in> singl_in_diff G (X \<union> {v})" 
          by (simp add: x)
      qed
      have sub_diff:"graph_diff G (X\<union>{v}) \<subseteq> graph_diff G X"
        unfolding graph_diff_def
        by (simp add: Collect_mono)
      have "odd_components (graph_diff G X) \<subseteq> odd_components (graph_diff G (X \<union> {v}))"
      proof
        fix C'
        assume C':"C' \<in> odd_components (graph_diff G X)"
        then have "\<exists>x \<in> Vs (graph_diff G X).
                   connected_component (graph_diff G X) x = C' \<and> odd (card C')"
          unfolding odd_components_def odd_component_def by blast
        then  obtain x where odd_x:"x \<in> Vs (graph_diff G X) \<and> 
                                    connected_component (graph_diff G X) x = C' \<and> odd (card C')"
          by auto
        then have "x \<notin> C" 
          by (smt (verit) C connected_components_member_eq even_components_def mem_Collect_eq)
        then have "x \<noteq> v" 
          using \<open>v \<in> C\<close> by blast
        then have "\<exists>e \<in> (graph_diff G X). x \<in> e" 
          by (meson odd_x vs_member_elim)
        then obtain e where e: "e \<in> (graph_diff G X) \<and> x \<in> e" by auto
        then have "e \<subseteq> C'" 
          using edge_subset_component graph_invar_diff[OF less.prems(1)] less.prems(1) odd_x
          by (meson edge_subset_component)
        then have 3:"e \<in> component_edges (graph_diff G X) C'"
          unfolding component_edges_def 
          using e graph_diffE less.prems(1) 
          by blast
        have C'indiff:"\<forall>z \<in> C'. z \<in>  Vs (graph_diff G (X \<union> {v}))"
        proof
          fix z
          assume "z \<in> C'" 
          have "z \<noteq> v"
            by (metis \<open>x \<notin> C\<close> \<open>z \<in> C'\<close> comp_C connected_components_member_sym odd_x)
          then have "z \<notin> C" 
            by (metis 2 \<open>x \<notin> C\<close> \<open>z \<in> C'\<close> connected_components_member_eq 
                in_own_connected_component odd_x)
          have "\<exists>e \<in> G. e \<inter> X = {} \<and> z \<in> e" 
            by (smt (z3) odd_x  \<open>z \<in> C'\<close> graph_diff_def in_connected_component_in_edges
                mem_Collect_eq vs_member)
          then obtain e where e: "e\<in>G \<and>  e \<inter> X = {} \<and> z \<in> e" by auto
          have "v \<notin> e" 
          proof(rule ccontr)
            assume "\<not> v \<notin> e"
            then have "v \<in> e" 
              by auto
            then have "e = {z, v}"
              using `graph_invar G` `z \<noteq> v` e by fastforce
            then have "e \<in> (graph_diff G X)"
              using e graph_diff_def by auto
            then have "z \<in> connected_component (graph_diff G X) v"
              by (metis \<open>e = {z, v}\<close> in_con_comp_insert insert_Diff insert_commute)
            then have "z \<in> C" 
              by (simp add: comp_C)
            then show False 
              using \<open>z \<notin> C\<close> by auto
          qed
          then have "e \<in> G \<and> e \<inter> (X \<inter> {v}) = {} \<and> z \<in> e" 
            using e by blast
          then have "e \<in> graph_diff G (X\<union>{v})" unfolding graph_diff_def
            using e \<open>v \<notin> e\<close> by blast
          then show "z\<in> Vs (graph_diff G (X \<union> {v}))" 
            using e by blast
        qed
        have "\<forall>z \<in> C'. z \<in> connected_component (graph_diff G (X\<union>{v})) x"
        proof
          fix z
          assume "z\<in>C'"
          then have "\<exists>p. walk_betw (graph_diff G X) x p z"
            by (metis in_connected_component_has_walk odd_x) 
          then obtain p where p: "walk_betw (graph_diff G X) x p z"
            by auto
          have "walk_betw (graph_diff G (X\<union>{v})) x p z"
          proof(rule nonempty_path_walk_between)
            show "p \<noteq> []" 
              using p by auto
            show "hd p = x"
              using p
              by (simp add: walk_between_nonempty_pathD(3))
            show "last p = z"
              using p
              by (simp add: walk_between_nonempty_pathD(4))
            have "path (graph_diff G X) p" 
              by (meson p walk_betw_def)
            have 5:"graph_invar (graph_diff G X)" 
              using graph_invar_diff less.prems(1) by fastforce
            then have 4:"C' \<in> connected_components (graph_diff G X)" 
              by (simp add: C' components_is_union_even_and_odd)
            have "hd p \<in> C'" 
              by (metis \<open>hd p = x\<close> in_own_connected_component odd_x)
            have "(component_edges (graph_diff G X) C') \<noteq> {}" 
              using 3 by auto
            then have "path (component_edges (graph_diff G X) C')  p" 
              by (simp add: 4 5 \<open>hd p \<in> C'\<close> \<open>path (graph_diff G X) p\<close> path_in_comp_edges)
            have "component_edges (graph_diff G X) C' = 
                  component_edges (graph_diff G (X \<union> {v})) C'"
            proof(safe)
              { 
                fix e
                assume asme:"e \<in> component_edges (graph_diff G X) C'"
                then have "e \<subseteq> C'" 
                  unfolding component_edges_def
                  by blast
                then have "e \<in> graph_diff G X" 
                  using asme Connected_Components.component_edges_subset by blast
                have "v \<notin> e" 
                  by (metis \<open>e \<subseteq> C'\<close> \<open>x \<notin> C\<close> comp_C connected_components_member_sym odd_x subsetD)
                then have "e \<inter> (X \<union> {v}) = {}" 
                  by (metis Un_insert_right \<open>e \<in> graph_diff G X\<close> disjoint_insert(1) 
                      graph_diffE sup_bot.right_neutral)
                then have "e \<in> graph_diff G (X \<union> {v})" 
                  by (meson \<open>e \<in> graph_diff G X\<close> graph_diffE graph_diffI)
                then show "e \<in> (component_edges (graph_diff G (X\<union>{v})) C')" 
                  unfolding component_edges_def 
                  using \<open>e \<in> graph_diff G X\<close> \<open>e \<subseteq> C'\<close> \<open>graph_invar (graph_diff G X)\<close>
                  by blast
              }
              fix e
              assume asme:"e \<in> component_edges (graph_diff G (X \<union> {v})) C'"
              then have "e \<subseteq> C'" unfolding component_edges_def
                by blast
              then have "e \<in> (graph_diff G (X\<union>{v}))" 
                using asme Connected_Components.component_edges_subset by blast
              then have "e \<inter> X = {}" 
                unfolding graph_diff_def by blast
              then have "e \<in> (graph_diff G X)"
                unfolding graph_diff_def 
                using \<open>e \<in> graph_diff G (X \<union> {v})\<close> graph_diff_subset by blast
              then show "e \<in> component_edges (graph_diff G X) C'"
                unfolding component_edges_def  
                using \<open>e \<subseteq> C'\<close> \<open>graph_invar (graph_diff G X)\<close> by blast
            qed
            then show "path (graph_diff G (X \<union> {v})) p"
              using `path (component_edges (graph_diff G X) C')  p` 
              by (metis Connected_Components.component_edges_subset path_subset)
          qed
          then show "z \<in> connected_component (graph_diff G (X \<union> {v})) x" 
            by (simp add: has_path_in_connected_component)
        qed
        then have "C' \<subseteq> connected_component (graph_diff G (X \<union> {v})) x"
          by blast
        have "connected_component (graph_diff G (X \<union> {v})) x \<subseteq> C'"
        proof
          fix z
          assume "z \<in> connected_component (graph_diff G (X \<union> {v})) x"
          then have "\<exists>p. walk_betw (graph_diff G (X \<union> {v})) x p z" 
            by (meson C'indiff e \<open>e \<subseteq> C'\<close> in_connected_component_has_walk subsetD)
          then obtain p where p:"walk_betw (graph_diff G (X\<union>{v})) x p z"
            by auto
          then have "path (graph_diff G (X \<union> {v})) p" 
            by (meson walk_betw_def)
          then have "path (graph_diff G X) p" 
            using sub_diff path_subset by blast
          then have "walk_betw (graph_diff G X) x p z" 
            by (meson sub_diff p walk_subset)
          then show "z \<in> C'" 
            using odd_x
            by (meson has_path_in_connected_component)
        qed
        then have "C' = connected_component (graph_diff G (X \<union> {v})) x" 
          using \<open>C' \<subseteq> connected_component (graph_diff G (X \<union> {v})) x\<close> by blast
        then show "C' \<in> odd_components (graph_diff G (X \<union> {v}))"
          unfolding odd_components_def odd_component_def
          using C'indiff e \<open>e \<subseteq> C'\<close> odd_x by fastforce
      qed
      then have odd_sub:"odd_comps_in_diff G X \<subseteq> odd_comps_in_diff G (X \<union> {v})"
        by (metis 6 odd_comps_in_diff_def sup.mono)
      show False
      proof(cases "\<exists>x \<in> (C-{v}). x \<notin> Vs (graph_diff G (X \<union> {v}))")
        case True
        then  obtain x where x:"x \<in> (C-{v}) \<and> (x \<notin> Vs (graph_diff G (X \<union> {v})))"
          by auto
        then have "x \<in> Vs G"
          by (metis DiffD1 Diff_insert_absorb Vs_subset 2 connected_component_subset 
              graph_diff_subset subset_Diff_insert)
        then have "x \<notin> X \<and> x \<notin> Vs (graph_diff G (X\<union>{v}))" 
          by (metis "2" DiffD1 connected_component_subset insert_Diff subsetD 
              subset_Diff_insert vs_graph_diff x)
        then have "{x} \<in> singl_in_diff G (X \<union> {v})" 
          unfolding singl_in_diff_def
          using x \<open>x \<in> Vs G\<close> by auto
        have "x \<in> Vs (graph_diff G X)" 
          by (metis "2" Diff_iff in_connected_component_in_edges x)
        then have "{x} \<notin> singl_in_diff G (X)" 
          unfolding singl_in_diff_def by blast
        have "{x} \<notin> odd_components (graph_diff G X)" 
          using C unfolding odd_components_def odd_component_def even_components_def
          by (smt (verit, best) DiffD1 connected_components_member_eq insert_compr mem_Collect_eq x)
        then have "{x} \<notin> odd_comps_in_diff G X" 
          unfolding odd_comps_in_diff_def
          using \<open>{x} \<notin> singl_in_diff G X\<close> by force
        then have 9:"odd_comps_in_diff G X \<subset> odd_comps_in_diff G (X \<union> {v})" 
          unfolding odd_comps_in_diff_def 
          by (metis UnCI \<open>{x} \<in> singl_in_diff G (X \<union> {v})\<close> odd_comps_in_diff_def odd_sub psubsetI)
        have 7:"finite (connected_components (graph_diff G (X \<union> {v})))"
          by (meson "less.prems"(1) Vs_subset finite_con_comps finite_subset graph_diff_subset)
        have "odd_components (graph_diff G (X \<union> {v})) 
              \<subseteq> connected_components (graph_diff G (X \<union> {v}))"
          unfolding odd_components_def connected_components_def odd_component_def
          by blast
        then have 8:"finite (odd_components (graph_diff G (X \<union> {v})))" 
          using 7 finite_subset by blast
        have "finite ( singl_in_diff G (X \<union> {v}))" 
          by (metis diff_components_finite finite_Un less.prems(1) odd_comps_in_diff_def)
        then have "finite (odd_comps_in_diff G (X \<union> {v}))" 
          by (metis 8 odd_comps_in_diff_def finite_Un)
        then have 10:"card (odd_comps_in_diff G X) < card (odd_comps_in_diff G (X \<union> {v}))"
          by (meson 9 psubset_card_mono)
        then have "card(X) + 1 \<le> card (odd_comps_in_diff G (X \<union> {v}))" 
          by (simp add: \<open>card (odd_comps_in_diff G X) = card X\<close>)
        have "card (X \<union> {v}) = (card X) + 1"
          by (metis "less.prems"(1) IntI One_nat_def Un_insert_right X_barr 
              2 \<open>v \<in> C\<close> add.right_neutral add_Suc_right card.insert diff_disjoint_elements(2) 
              empty_iff finite_subset in_connected_component_in_edges sup_bot_right)
        have "card (odd_comps_in_diff G (X \<union> {v})) \<le> card (X \<union> {v})" 
          using assms(2)
          by (metis "2" Diff_insert0 Un_insert_right X_barr \<open>v \<in> C\<close> in_connected_component_in_edges
              insert_subset less.prems(2) subset_Diff_insert sup_bot.right_neutral tutte_conditionE 
              vs_graph_diff)
        then have "card (odd_comps_in_diff G (X \<union> {v})) \<le> (card X) + 1" 
          using \<open>card (X \<union> {v}) = card X + 1\<close> by presburger
        then have "barrier G (X \<union> {v})" 
          unfolding barrier_def
          using \<open>card (X \<union> {v}) = card X + 1\<close> \<open>card X + 1 \<le> card (odd_comps_in_diff G (X \<union> {v}))\<close> 
          by auto
        then have "X \<union> {v} \<in> ?B" 
          by (metis "2" Diff_insert0 Un_insert_right X_barr \<open>v \<in> C\<close> in_connected_component_in_edges 
              insert_subset mem_Collect_eq subset_Diff_insert sup_bot.right_neutral vs_graph_diff)
        then show ?thesis 
          by (metis X_max 10 sup.strict_order_iff sup_ge1)
      next
        case False
        let ?Cs = "connected_components (graph_diff G (X \<union> {v}))"
        assume "\<not> (\<exists>x\<in>C - {v}. x \<notin> Vs (graph_diff G (X \<union> {v})))"
        then have "\<forall>x\<in>C - {v}. x \<in> Vs (graph_diff G (X \<union> {v}))" 
          by auto
        have "\<exists> C' \<in> ?Cs.C' \<subseteq> (C-{v}) \<and> odd (card C')"
        proof(rule ccontr)
          assume asmNot:"\<not> (\<exists>C'\<in>?Cs. C' \<subseteq> (C-{v}) \<and> odd (card C'))"
          then have asm_pos:"\<forall> C' \<in> ?Cs. \<not> C' \<subseteq> (C-{v}) \<or> even (card C')"
            by blast
          then have "\<forall> C' \<in> ?Cs. C' \<subseteq> (C-{v}) \<longrightarrow> (card C') \<noteq> 1"
            by fastforce
          then have "\<forall> C' \<in> ?Cs. C' \<subseteq> (C-{v}) \<longrightarrow> (\<exists>x y. {x, y} \<subseteq> C')"
            by (metis connected_comp_nempty empty_subsetI equals0I insert_subset)
          have "\<forall> C' \<in> ?Cs. C' \<subseteq> (C-{v}) \<longrightarrow> component_edges (graph_diff G (X \<union> {v})) C' \<noteq> {}"
          proof
            fix C'
            assume asmC':"C' \<in> ?Cs"
            show " C' \<subseteq> (C-{v}) \<longrightarrow> component_edges (graph_diff G (X \<union> {v})) C' \<noteq> {}"
            proof
              assume "C' \<subseteq> C - {v}"
              have "(card C') \<noteq> 1" 
                using asmC' \<open>C' \<subseteq> C - {v}\<close> asm_pos by fastforce
              then have "(\<exists>x y. {x, y} \<subseteq> C' \<and> x \<noteq> y)" 
                by (metis asmC' connected_comp_nempty empty_subsetI insert_subset 
                    is_singletonI' is_singleton_altdef)
              then obtain x y where xy:"{x, y} \<subseteq> C' \<and> x \<noteq> y"
                  by auto
              then have "y \<in> connected_component (graph_diff G (X \<union> {v})) x" 
                by (metis asmC' connected_components_closed' insert_subset)
              then obtain p where p_walk: "walk_betw (graph_diff G (X \<union> {v})) x p y"
                by (metis in_con_comp_has_walk xy)
              then have "path (graph_diff G (X \<union> {v})) p"
                by (meson walk_betw_def)
              have "p \<noteq> []"
                using p_walk by auto
              have "hd p = x \<and> last p = y" 
                using p_walk
                by (simp add: walk_between_nonempty_pathD(3,4))
              then have "size p \<ge> 2" 
                by (metis One_nat_def Suc_1 Suc_leI \<open>p \<noteq> []\<close> antisym_conv1 append.simps(1) 
                    diff_add_inverse2 diff_less hd_Cons_tl last_snoc length_0_conv lessI 
                    less_Suc0 list.size(4) not_le xy)
              then have 11:"{x, hd (tl p)} \<in> (graph_diff G (X \<union> {v}))" 
                by (metis One_nat_def Suc_1 Suc_pred \<open>hd p = x \<and> last p = y\<close> \<open>p \<noteq> []\<close>
                    \<open>path (graph_diff G (X \<union> {v})) p\<close> hd_Cons_tl length_greater_0_conv length_tl 
                    lessI list.size(3) not_le path_2)
              then have "hd (tl p) \<in> C'"
                by (metis asmC' connected_components_closed' in_con_comp_insert insert_Diff insert_subset xy) 
              then have "{x, hd (tl p)} \<subseteq> C'" 
                using \<open>{x, y} \<subseteq> C' \<and> x \<noteq> y\<close> by blast
              then show "component_edges (graph_diff G (X \<union> {v})) C' \<noteq> {}" 
                by (smt (verit) 11 component_edges_def empty_Collect_eq)
            qed
          qed
          have 13:"(C-{v}) = \<Union>{C' \<in> ?Cs. C' \<subseteq> C - {v}}"
          proof
            show "C - {v} \<subseteq> \<Union> {C' \<in> ?Cs. C' \<subseteq> C - {v}}"
            proof
              fix x
              assume "x \<in> C - {v}"
              then have 12:"connected_component (graph_diff G X) x = C" 
                by (metis DiffD1 comp_C connected_components_member_eq)
              then have "\<exists> C'. C' = connected_component (graph_diff G (X \<union> {v})) x"
                by blast
              then obtain C' where C':"C' = connected_component (graph_diff G (X \<union> {v})) x" by auto
              then have "C' \<subseteq> C - {v}" 
                by (metis Diff_empty False Un_insert_right Un_upper1 12 \<open>x \<in> C - {v}\<close> 
                    connected_component_subset less.prems(1) new_component_subset_old subsetD 
                    subset_Diff_insert vs_graph_diff)
              then have "C' \<in> ?Cs"
                unfolding connected_components_def
                using C' False \<open>x \<in> C - {v}\<close> by fastforce
              then have "C' \<in> {C' \<in> ?Cs. C' \<subseteq> C - {v}}"
                using \<open>C' \<subseteq> C - {v}\<close> by blast
              then  show "x \<in> \<Union> {C' \<in> ?Cs. C' \<subseteq> C - {v}}"
                using UnionI C' in_own_connected_component by fastforce
            qed
            show "\<Union> {C' \<in> ?Cs. C' \<subseteq> C - {v}} \<subseteq> C - {v}"
              by blast
          qed
          let ?A = "{C' \<in>?Cs. C' \<subseteq> C - {v}}"
          have 15:"finite ?A"
            by (metis (no_types, lifting) "13" "2" Diff_empty Diff_insert0
                diff_connected_component_subset finite_Diff_insert finite_UnionD finite_subset 
                less.prems(1) subset_Diff_insert vs_graph_diff)
          have 14:"\<forall>C \<in> ?A. finite C" 
            by (metis (no_types, lifting) "less.prems"(1) Vs_subset connected_component_subs_Vs 
                finite_subset graph_diff_subset mem_Collect_eq)
          have "\<forall>C1\<in>?A. \<forall>C2 \<in>?A. C1 \<noteq> C2 \<longrightarrow> C1 \<inter> C2 = {}" 
            by (metis (no_types, lifting) connected_components_disj mem_Collect_eq)
          then have 16:"sum (\<lambda> C. card C) ?A = card (\<Union>C\<in>?A. C)" 
            using union_card_is_sum[of ?A "(\<lambda> C. C)"]
            using 14 15 by blast
          then have "even (sum (\<lambda> C. card C) ?A)" 
            by (metis (no_types, lifting) asmNot dvd_sum mem_Collect_eq)
          then have "even (card (C -{v}))" 
            using 13 16 by fastforce
          have "even (card C)" 
            using C even_components_def by fastforce
          have "odd (card (C - {v}))" 
            using `even (card C)` 
            by (smt (verit, ccfv_threshold) "less.prems"(1) Diff_empty Diff_insert_absorb 
                Diff_single_insert One_nat_def Vs_subset 2 \<open>v \<in> C\<close> card.empty card.insert 
                card_Diff_subset card_gt_0_iff card_le_sym_Diff connected_component_subset
                double_diff dvd_diffD1 empty_iff empty_subsetI finite_Diff finite_subset 
                graph_diff_subset insert_Diff nat_le_linear not_less odd_one)
          then show False 
            using \<open>even (card (C - {v}))\<close> by blast
        qed
        then obtain C' where C':"C'\<in>connected_components (graph_diff G (X \<union> {v})) \<and>
                                 C' \<subseteq> C - {v} \<and> odd (card C')" by auto
        then have 17:"C' \<in> odd_components (graph_diff G (X \<union> {v}))" 
          unfolding odd_components_def odd_component_def 
          by (smt (verit, del_insts) CollectI connected_comp_has_vert)
        have "C' \<notin> odd_components (graph_diff G X)" 
          using odd_comps_in_diffI1[OF 17] 
          unfolding singl_in_diff_def odd_comps_in_diff_def
          by (metis C' Diff_empty comp_C connected_comp_has_vert connected_components_member_eq
              in_own_connected_component odd_comps_in_diffI1 odd_comps_in_diff_is_component 
              subset_Diff_insert subset_iff)
        have "C' \<notin> singl_in_diff G X" 
          unfolding singl_in_diff_def 
          by (smt (verit, ccfv_threshold) Vs_subset C' sub_diff connected_component_subs_Vs 
              insert_subset mem_Collect_eq order_trans)
        then have "C' \<notin> odd_comps_in_diff G X"  
          unfolding odd_comps_in_diff_def
          using \<open>C' \<notin> odd_components (graph_diff G X)\<close> by force
        then have 20:"odd_comps_in_diff G X \<subset> odd_comps_in_diff G (X \<union> {v})" 
          unfolding odd_comps_in_diff_def 
          by (metis UnCI 17 odd_sub odd_comps_in_diff_def psubsetI)
        have 18:"finite (connected_components (graph_diff G (X \<union> {v})))"
          by (meson "less.prems"(1) Vs_subset finite_con_comps finite_subset graph_diff_subset)
        have "odd_components (graph_diff G (X \<union> {v}))
              \<subseteq> connected_components (graph_diff G (X \<union> {v}))"
          unfolding odd_components_def odd_component_def connected_components_def 
          by blast
        then have 19:"finite (odd_components (graph_diff G (X \<union> {v})))" 
          using 18 finite_subset by blast
        have "finite ( singl_in_diff G (X \<union> {v}))" 
          by (metis diff_components_finite finite_Un less.prems(1) odd_comps_in_diff_def)
        then have "finite (odd_comps_in_diff G (X \<union> {v}))" 
          by (metis 19 odd_comps_in_diff_def finite_Un)
        then have 21:"card (odd_comps_in_diff G X) < card (odd_comps_in_diff G (X \<union> {v}))"
          by (meson 20 psubset_card_mono)
        then have "card(X) + 1 \<le> card (odd_comps_in_diff G (X \<union> {v}))" 
          by (simp add: \<open>card (odd_comps_in_diff G X) = card X\<close>)
        have "card (X \<union> {v}) = (card X) + 1" 
          by (metis "2" IntI One_nat_def Un_insert_right X_barr \<open>v \<in> C\<close> add.right_neutral 
              add_Suc_right card.insert diff_disjoint_elements(2) empty_iff 
              finite_subset in_connected_component_in_edges less.prems(1) sup_bot.right_neutral)
        have "card (odd_comps_in_diff G (X \<union> {v})) \<le> card (X \<union> {v})" 
          using assms(2) 
          by (metis "2" Diff_insert0 Un_insert_right X_barr \<open>v \<in> C\<close> in_connected_component_in_edges
              insert_subset less.prems(2) subset_Diff_insert sup_bot.right_neutral tutte_conditionE 
              vs_graph_diff)
        then have "card (odd_comps_in_diff G (X \<union> {v})) \<le> (card X) + 1" 
          using \<open>card (X \<union> {v}) = card X + 1\<close> by presburger
        then have "barrier G (X \<union> {v})" 
          by (metis Un_empty X_barr \<open>card (X \<union> {v}) = card X + 1\<close> 
              \<open>card X + 1 \<le> card (odd_comps_in_diff G (X \<union> {v}))\<close> barrier_def le_antisym)
        then have " (X \<union> {v}) \<in> ?B" 
          by (metis Un_insert_right Vs_subset X_barr 2 \<open>v \<in> C\<close> connected_component_subset 
              graph_diff_subset insert_subsetI mem_Collect_eq subsetD sup_bot_right)
        then show ?thesis 
          by (metis X_max 21 sup.strict_order_iff sup_ge1)
      qed
    qed
    then have 22:"{C. \<exists>x \<in> Vs G - X. C =
                   connected_component (graph_diff G X) x \<and> even (card C)} = {}"
      unfolding even_components_def 
      by (smt (verit, ccfv_threshold) Collect_empty_eq One_nat_def card.empty card.insert
          connected_components_notE_singletons empty_iff finite.emptyI odd_one)
    have 84:"odd_comps_in_diff G X = 
          {C. \<exists>x \<in> Vs G - X. C = connected_component (graph_diff G X) x \<and> odd (card C)}" 
      using odd_comps_in_diff_are_components[of G X] Collect_cong less.prems(1) by auto
    then have 23:"odd_comps_in_diff G X = 
                {C. \<exists>x \<in> Vs G - X. C = connected_component (graph_diff G X) x}"
      using 22 by auto
    have "\<forall>x \<in>X. \<exists>y \<in>Vs G - X. {x, y} \<in> G" 
      by (simp add: X_barr every_el_in_barrier_connected less.prems(1) less.prems(2))
    let ?G' = "{e'. \<exists>x y. {x, y} \<in> G \<and> x \<notin> X \<and> y \<in> X \<and> e' = 
                {connected_component (graph_diff G X) x,{y}}}"
    have "\<forall>x \<in> X. {x} \<in> Vs ?G'" 
    proof
      fix x
      assume "x \<in> X"
      then obtain y where  "y \<in>Vs G - X \<and>  {x, y} \<in> G" 
        by (meson \<open>\<forall>x\<in>X. \<exists>y\<in>Vs G - X. {x, y} \<in> G\<close>)
      then have "{connected_component (graph_diff G X) y,{x}} \<in> ?G'"
        by (smt (z3) DiffD2 \<open>x \<in> X\<close> insert_commute mem_Collect_eq) 
      then show "{x} \<in> Vs ?G'" by auto
    qed
    let ?f = "(\<lambda>x. {{x}})"
    have 28:"Vs ?G' - (odd_comps_in_diff G X) = (\<Union>x\<in>X. ?f x)"
    proof(safe)
      {
        fix y
        assume "y \<in> Vs ?G'"
        assume "y \<notin> (odd_comps_in_diff G X)"
        then have noexcomp:"\<nexists>x. x\<in> Vs G - X \<and> y = connected_component (graph_diff G X) x"
          using 23 by blast
        obtain e' u v where e':"{u, v} \<in> G \<and> u \<notin> X \<and> v \<in> X \<and>
                                 e' = {connected_component (graph_diff G X) u, {v}} \<and> y \<in> e'"
          using `y \<in> Vs ?G'` 
          by (smt (verit, del_insts) mem_Collect_eq vs_member_elim)
        then have "\<exists>u. u \<in> X \<and> y = {u}" 
          by (metis Diff_iff noexcomp edges_are_Vs insert_iff singletonD)
        then show "y \<in> (\<Union>x\<in>X. ?f x)" 
          by blast
      }
      {
        fix y
        assume "y \<in> X" 
        then show "{y} \<in> Vs ?G'" 
          using \<open>\<forall>x \<in> X. {x} \<in> Vs ?G'\<close> by fastforce
      }
      fix y
      assume "y \<in> X" "{y} \<in> odd_comps_in_diff G X"
      then show False 
        by (metis IntI odd_comps_in_diff_not_in_X empty_iff insertCI)
    qed
    have "graph_invar ?G'"
    proof(safe, goal_cases)
      case 1
      then show ?case
        using in_own_connected_component singleton_iff in_connected_componentI2
        apply(simp add: dblton_graph_def)
        by (smt (verit, del_insts) in_connected_componentI2 singleton_iff)
    next
      case 2
      have "finite (Vs G)" 
        by (simp add: less.prems(1))
      then  have "finite {X.  X \<subseteq> Vs G}"  
        by force
      have "finite {{X, Y}| X Y.  X \<subseteq> Vs G \<and> Y \<subseteq> Vs G}" using `finite (Vs G)`
          subset_graph_finite[of "(Vs G)"] by auto
      then have "finite {{X, Y}| X Y.  X \<subseteq> Vs G \<and> Y \<subseteq> Vs G \<and> ( \<exists>x\<in>X.\<exists> y\<in>Y. {x, y} \<in> G)}" 
        by (smt (verit) Collect_mono rev_finite_subset)
      have "?G' \<subseteq> {{X, Y}| X Y.  X \<subseteq> Vs G \<and> Y \<subseteq> Vs G}"
      proof
        fix e
        assume "e \<in> ?G'"
        then obtain x y where edge_in_G':"{x, y} \<in> G \<and> x \<notin> X \<and> y \<in> X \<and> 
                                           e = {connected_component (graph_diff G X) x, {y}}"
          by auto
        have "connected_component (graph_diff G X) x \<subseteq> Vs G" 
          by (meson edge_in_G' diff_connected_component_subset edges_are_Vs)
        have "{y} \<subseteq> Vs G" 
          using edge_in_G' subsetD by blast
        then show "e \<in> {{X, Y}| X Y.  X \<subseteq> Vs G \<and> Y \<subseteq> Vs G}" 
          using \<open>connected_component (graph_diff G X) x \<subseteq> Vs G\<close> edge_in_G' by blast
      qed
      then have "finite ?G'" 
        using \<open>finite {{X, Y} |X Y. X \<subseteq> Vs G \<and> Y \<subseteq> Vs G}\<close> finite_subset by fastforce
      have "\<forall>C \<in> ?G'. finite C" 
        by blast
      then show "finite (Vs ?G')"
        by (simp add: union_of_set_finite Vs_def \<open>finite ?G'\<close>)
    qed
    have 25:"(odd_comps_in_diff G X) \<subseteq> Vs ?G'" 
    proof
      fix C
      assume asmC:"C \<in> (odd_comps_in_diff G X)"
      then obtain x y where xy:" {x, y} \<in> G \<and> x \<in> C \<and> y \<in> X" 
        by (metis less.prems(1) less.prems(2) odd_comps_in_diff_connected)
      then have 23:"{connected_component (graph_diff G X) x, {y}} \<in> ?G'" 
        using asmC odd_comps_in_diff_not_in_X 
        by (smt (verit) IntI empty_iff mem_Collect_eq) 
      have "C = connected_component (graph_diff G X) x" 
        by (metis asmC odd_comps_in_diff_is_component xy)
      then have "{C, {y}} \<in> ?G'" 
        using 23 by blast
      then show "C \<in> Vs ?G'" 
        by (meson edges_are_Vs)
    qed
    have "\<forall> e \<in> ?G'. \<exists> u v. e = {u, v} \<and> 
                     (u \<in> (odd_comps_in_diff G X) \<and> v \<in> Vs ?G' - (odd_comps_in_diff G X))"
    proof
      fix e
      assume "e \<in> ?G'"
      then obtain x y where xy:"{x, y} \<in> G \<and>  x \<notin> X \<and>  y \<in> X \<and> 
                                e = {connected_component (graph_diff G X) x, {y}}"
        by auto 
      then have 24:"connected_component (graph_diff G X) x \<in> (odd_comps_in_diff G X)"
        by (metis (mono_tags, lifting) "23" Diff_iff edges_are_Vs mem_Collect_eq)
      have "{y} \<in> Vs ?G'" 
        using xy by auto
      have "{y} \<notin> (odd_comps_in_diff G X)" 
        by (metis IntI xy odd_comps_in_diff_not_in_X empty_iff singletonI)
      then have "{y} \<in> Vs ?G' - (odd_comps_in_diff G X)" 
        by (simp add: \<open>{y} \<in> Vs ?G'\<close>)
      then show "\<exists> u v. e = {u, v}  \<and>
                       (u \<in> (odd_comps_in_diff G X) \<and> v \<in> Vs ?G' - (odd_comps_in_diff G X))"
        using 24 xy by blast
    qed
    then have "partitioned_bipartite ?G' (odd_comps_in_diff G X)"
      unfolding partitioned_bipartite_def
      by (metis (no_types, lifting) 25 \<open>graph_invar ?G'\<close>)
    have 29:"((card  (odd_comps_in_diff G X)) = card (Vs ?G' - (odd_comps_in_diff G X)))"
    proof - 
      have "card  (odd_comps_in_diff G X) = card X" 
        by (simp add: \<open>card (odd_comps_in_diff G X) = card X\<close>)
      have "finite X" 
        using X_barr less.prems(1) rev_finite_subset by auto
      have "\<forall>x \<in> X. finite (?f x)" 
        by blast
      have "\<forall> C1 \<in> X. \<forall> C2 \<in> X. C1 \<noteq> C2 \<longrightarrow> ?f C1 \<inter> ?f C2 = {}" by auto
      then have 26:"card (\<Union>x\<in>X. ?f x) = sum (\<lambda> C. card (?f C)) X" 
        using union_card_is_sum[of X ?f] 
        using \<open>\<forall>x\<in>X. finite {{x}}\<close> \<open>finite X\<close> by presburger
      have 27:"sum (\<lambda> C. card (?f C)) X =  sum (\<lambda> C. 1) X" 
        by simp
      have "sum (\<lambda> C. 1) X = card X" 
        by fastforce
      then have "card (\<Union>x\<in>X. ?f x) = card X" 
        using 26 27 by presburger
      then have " card (Vs ?G' - (odd_comps_in_diff G X)) = card X" 
        using 28 by presburger
      then show ?thesis 
        using \<open>card (odd_comps_in_diff G X) = card X\<close> by presburger
    qed
    have "\<exists>M. perfect_matching ?G' M"
    proof(rule ccontr)
      assume "\<nexists>M. perfect_matching ?G' M" 
      then have "\<not> (\<forall>A \<subseteq>  (odd_comps_in_diff G X). card (neighbours_of_Vs ?G' A) \<ge> card A \<and>
                   (card  (odd_comps_in_diff G X) = card (Vs ?G' - (odd_comps_in_diff G X))))"
        using frobenius_matching[of ?G' "(odd_comps_in_diff G X)" ] 
          `partitioned_bipartite ?G' (odd_comps_in_diff G X)` \<open>graph_invar ?G'\<close>
        by auto
      then have "\<exists> A \<subseteq> (odd_comps_in_diff G X). card (neighbours_of_Vs ?G' A) < card A \<or>
                   ((card  (odd_comps_in_diff G X)) \<noteq> card (Vs ?G' - (odd_comps_in_diff G X)))"
        using le_less_linear by blast
      then obtain A where A:"A \<subseteq> (odd_comps_in_diff G X) \<and> card (neighbours_of_Vs ?G' A) < card A" 
        using 29 by blast
      have 30:"neighbours_of_Vs ?G' (odd_comps_in_diff G X) = Vs ?G' - (odd_comps_in_diff G X)"
        using neighbours_of_Vs_bipartite[of ?G' "(odd_comps_in_diff G X)"]
          `partitioned_bipartite ?G' (odd_comps_in_diff G X)` 
        by fastforce
      have "(neighbours_of_Vs ?G' A) \<subseteq> (neighbours_of_Vs ?G' (odd_comps_in_diff G X))"
        using neighbours_of_Vs_subset[of A "(odd_comps_in_diff G X)"] A by blast
      then have "(neighbours_of_Vs ?G' A) \<subseteq> Vs ?G' - (odd_comps_in_diff G X)" 
        by (simp add: 30)
      then have 31:"(neighbours_of_Vs ?G' A) \<subseteq> (\<Union>x\<in>X. ?f x)" 
        by (simp add: 28)
      have "(\<Union>x\<in>X. ?f x) = {{x} |x. x \<in> X}" using  singleton_set_is_union_singletons[of X]
        by (meson X_barr less.prems(1) rev_finite_subset)
      then have 32:"(neighbours_of_Vs ?G' A) \<subseteq> {{x} |x. x \<in> X}" 
        using 31 by presburger
      let ?ReachA = "(\<lambda> A. {x. {x}\<in>(neighbours_of_Vs ?G' A)})"
      have "finite A" 
        using A diff_components_finite finite_subset less.prems(1) by auto
      have "finite X" 
        using X_barr \<open>finite (Vs G)\<close> rev_finite_subset by blast
      then have 38:"card (?ReachA A) = card (neighbours_of_Vs ?G' A)" 
        using card_singleton_set_same[of X "(neighbours_of_Vs ?G' A)"] 32 by presburger
      have "?ReachA A \<subseteq> X" 
        using `neighbours_of_Vs ?G' A \<subseteq> {{x} |x. x \<in> X}` by auto
      have "?ReachA A = {y'. \<exists>x'. {x', y'} \<in> G \<and>
                                   connected_component (graph_diff G X) x' \<in> A \<and> y' \<in> X}"
        unfolding neighbours_of_Vs_def 
        apply safe 
           apply blast+
        apply (metis IntI A odd_comps_in_diff_not_in_X empty_iff insertCI subsetD)
      proof -
        fix x x'
        assume asms:"{x', x} \<in> G" "connected_component (graph_diff G X) x' \<in> A" "x \<in> X"
        then have "{connected_component (graph_diff G X) x', {x}} \<in> ?G'"
          by (smt (verit, del_insts) IntI A odd_comps_in_diff_not_in_X empty_iff
              in_own_connected_component mem_Collect_eq subsetD)
        then   have "x \<in> ?ReachA A"  
          unfolding neighbours_of_Vs_def 
          by (smt (verit, best) A asms(2-3) odd_comps_in_diff_not_in_X disjoint_insert(2) 
              insertCI insert_Diff mem_Collect_eq subset_iff)
        then  show " \<exists>u\<in>A. \<exists>e\<in>?G'. {x} \<noteq> u \<and> u \<in> e \<and> {x} \<in> e" 
          unfolding neighbours_of_Vs_def by blast
      qed 
      have "A \<subseteq> odd_comps_in_diff G (?ReachA A)"
      proof
        fix C
        assume "C \<in> A" 
        then have 31:"C \<in> odd_comps_in_diff G X" 
          using A by blast
        then have "C \<noteq> {}" 
          using  less.prems(1) odd_components_nonempty by auto
        then obtain u where u:"u \<in> C" 
          by blast
        then have 33:"connected_component (graph_diff G X) u = C" 
          by (simp add: 31 odd_comps_in_diff_is_component less.prems(1))
        have 36:"\<forall>y\<in>connected_component (graph_diff G (?ReachA A)) u. y \<notin> X"
        proof
          fix y
          assume asmy:"y \<in> connected_component (graph_diff G (?ReachA A)) u" 
          show "y \<notin> X"
          proof(cases "y=u")
            case True
            then show ?thesis 
              using 31 u odd_comps_in_diff_not_in_X by blast
          next
            case False
            then obtain p where p:"walk_betw (graph_diff G (?ReachA A)) y p u"
              using asmy walk_symmetric 
              by (fastforce elim: in_con_comp_has_walk)
            then  have "\<forall>x\<in>set p. x \<in> connected_component (graph_diff G (?ReachA A)) u" 
              by (metis (no_types, lifting) asmy connected_components_member_eq 
                  vertices_path_in_component)
            have "u \<notin> X" 
              using 31 u odd_comps_in_diff_not_in_X by auto
            have "last p = u" 
              by (meson p walk_betw_def)
            then have "path (graph_diff G (?ReachA A)) p" 
              using p by (meson walk_betw_def)
            then have "\<forall>x \<in> set p. x \<notin> X \<and> x \<in> connected_component (graph_diff G X) u" 
              using `last p = u`
            proof(induct p)
              case path0
              then show ?case 
                by force
            next
              case (path1 v)
              then show ?case 
                using \<open>u \<notin> X\<close> in_own_connected_component by force
            next
              case (path2 v v' vs)
              have "{v, v'} \<in> (graph_diff G (?ReachA A))" 
                using path2.hyps(1) by blast
              then have "{v, v'} \<inter> (?ReachA A) = {}" 
                by (metis (mono_tags, lifting) graph_diff_def mem_Collect_eq)
              then have "{v} \<notin> neighbours_of_Vs ?G' A" 
                by blast
              then have "\<nexists>C. C\<in>A \<and> {C, {v}} \<in> ?G'"
                unfolding neighbours_of_Vs_def
                by (smt (verit, best) A doubleton_eq_iff in_mono insert_disjoint(2) insert_iff 
                                      mem_Collect_eq odd_comps_in_diff_not_in_X)  
              then have "{C, {v}} \<notin> ?G'" 
                using \<open>C \<in> A\<close> by presburger
              have 35:"v' \<in> connected_component (graph_diff G X) u" 
                using path2.hyps(3) path2.prems by fastforce
              then have 34:"{connected_component (graph_diff G X) v', {v}} \<notin> ?G'"
                by (metis (no_types, lifting) 33 \<open>{C, {v}} \<notin> ?G'\<close> connected_components_member_eq)
              have "\<forall>x\<in>set (v' # vs). x \<notin> X" 
                by (metis last_ConsR list.simps(3) path2.hyps(3) path2.prems)
              have "v \<notin> X"
              proof
                assume "v \<in> X"
                have " {v', v} \<in> G \<and> v' \<notin> X"
                  by (metis (no_types, lifting) \<open>\<forall>x\<in>set (v' # vs). x \<notin> X\<close> graph_diff_subset 
                      insert_commute list.set_intros(1) path2.hyps(1) subsetD)
                then have "{connected_component (graph_diff G X) v', {v}} \<in> ?G'" 
                  using \<open>v \<in> X\<close> by blast
                then show False 
                  using 34 by blast
              qed
              have "{v, v'} \<inter> X = {}" 
                by (simp add: \<open>\<forall>x\<in>set (v' # vs). x \<notin> X\<close> \<open>v \<notin> X\<close>)
              then have "{v, v'} \<in> (graph_diff G X)" 
                unfolding graph_diff_def  
                using graph_diff_subset path2.hyps(1) by auto
              then have "v \<in> connected_component (graph_diff G X) u" 
                by (metis 35 connected_components_member_eq insert_commute 
                    vertices_edges_in_same_component)
              then show ?case 
                by (metis \<open>v \<notin> X\<close> last_ConsR list.simps(3) path2.hyps(3) path2.prems set_ConsD)
            qed
            then show "y \<notin> X"
              by (metis (no_types, lifting) p list.set_sel(1) walk_betw_def)
          qed
        qed
        then have "connected_component (graph_diff G X) u = 
                   connected_component (graph_diff G (?ReachA A)) u"
          by (metis (no_types, lifting) \<open>?ReachA A \<subseteq> X\<close> less.prems(1) new_component_is_old)
        then have 37:"connected_component (graph_diff G (?ReachA A)) u = C" 
          using 33 by presburger
        then have "C \<in> {C. \<exists> v\<in>Vs G-X. connected_component (graph_diff G X) v = C \<and> odd (card C)}"
          using 31 odd_comps_in_diff_are_components less.prems(1) by metis
        then have "odd (card C)" 
          by auto
        then have "C \<in> {C. \<exists> v\<in>Vs G-X. connected_component (graph_diff G (?ReachA A)) v = C \<and> 
                                        odd (card C)}"
          using 31 36 37 u component_in_E insert_Diff insert_subset mem_Collect_eq
          by (smt (z3) DiffI) 
        then show "C \<in>  odd_comps_in_diff G (?ReachA A)" 
          using odd_comps_in_diff_are_components[of G " (?ReachA A)"] 
          by (smt (z3) DiffI 31 36 37 u \<open>?ReachA A \<subseteq> X\<close> component_in_E less.prems(1)
                mem_Collect_eq subsetD)
      qed
      then have 39:"card A \<le> card (odd_comps_in_diff G (?ReachA A))"
        by (simp add: card_mono diff_components_finite less.prems(1))
      have "card A > card (?ReachA A)" 
        using A 38 by presburger
      then have 40:"card (?ReachA A) < card (odd_comps_in_diff G (?ReachA A))"
        using 39 by linarith
      have "?ReachA A \<subseteq> Vs G" 
        using X_barr \<open>?ReachA A \<subseteq> X\<close> by blast
      then have "card (?ReachA A) \<ge> card (odd_comps_in_diff G (?ReachA A))"
        using assms(2) unfolding tutte_condition_def 
        by (meson less.prems(2) tutte_condition_def)
      then show False 
        using 40 not_less by blast
    qed
    then obtain M' where M':"perfect_matching ?G' M'" 
      by auto
    let ?Z2 = "{C. \<exists> x y. C = {c . \<exists> e. e \<in> G \<and> e = {c, y} \<and> c \<notin> X \<and> 
                          c \<in> connected_component (graph_diff G X) x} \<and>
                          y\<in> X  \<and> {connected_component (graph_diff G X) x, {y}} \<in> M'}"
    have "Vs ?Z2 \<inter> X = {}" 
    proof(safe)
      fix x
      assume "x \<in> Vs ?Z2" "x \<in> X"
      then obtain C x' y' where C:"(C = {c . \<exists> e. e \<in> G \<and> e = {c, y'} \<and> c \<notin> X \<and>
                                   c \<in> connected_component (graph_diff G X) x'} \<and>
                                   {connected_component (graph_diff G X) x', {y'}} \<in> M') \<and> x \<in> C"         
        using vs_member[of x ?Z2] by blast
      then have "x \<notin> X" 
        by blast
      then show "x \<in> {}" 
        using \<open>x \<in> X\<close> by blast
    qed
    have "Vs ?Z2 \<subseteq> Vs G"
    proof
      fix z
      assume "z \<in> Vs ?Z2" 
      then obtain C where "C \<in> ?Z2 \<and> z \<in> C" 
        by (meson vs_member_elim)
      then obtain x y where xy:"C = {c . \<exists> e. e \<in> G \<and> e = {c, y} \<and> c \<notin> X \<and> 
                                c \<in> connected_component (graph_diff G X) x} \<and>
                                {connected_component (graph_diff G X) x, {y}} \<in> M'"
        by blast 
      then have "C \<subseteq> Vs G"
        by (safe,auto)
      then show "z\<in> Vs G"
        using `C \<in> ?Z2 \<and> z \<in> C` by auto
    qed
    then have "finite (Vs ?Z2)" 
      by (simp add: finite_subset less.prems(1))
    have 41:"\<forall>a1 \<in>?Z2.\<forall>a2\<in>?Z2. a1 \<noteq> a2 \<longrightarrow> a1 \<inter> a2 = {}"
      apply safe
      using M' unfolding perfect_matching_def
      by (smt (verit, ccfv_SIG) connected_components_member_eq doubleton_eq_iff 
          insertCI matching_unique_match)+
    have "\<forall>C \<in> ?Z2. finite C"
    proof
      fix C
      assume "C \<in> ?Z2"
      then obtain x y where "C = {c . \<exists> e. e \<in> G \<and> e = {c, y} \<and> c \<notin> X \<and> 
                             c \<in> connected_component (graph_diff G X) x} \<and>
                             {connected_component (graph_diff G X) x, {y}} \<in> M'" 
        by blast 
      then have "C \<subseteq> Vs G"
        by (safe,auto)
      then show "finite C" 
        using \<open>finite (Vs G)\<close> finite_subset by auto
    qed
    have "finite ?Z2"
    proof(rule ccontr)
      assume "infinite ?Z2" 
      then have "infinite (\<Union>?Z2)" 
        using finite_UnionD by blast
      then have "infinite (Vs ?Z2)" 
        by (simp add: Vs_def)
      then show False 
        using \<open>finite (Vs ?Z2)\<close> by blast
    qed
    have "\<forall>a\<in>?Z2. a \<noteq> {}"
    proof
      fix a
      assume "a \<in> ?Z2"
      then obtain x y where xy:"{connected_component (graph_diff G X) x, {y}} \<in> M' \<and> y \<in> X \<and>
          a = {c. \<exists>e. e \<in> G \<and> e = {c, y} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff G X) x}"
        by blast
      then have "{connected_component (graph_diff G X) x, {y}} \<in> ?G'" 
        by (metis (no_types, lifting) M' perfect_matching_def subsetD)
      then obtain x' y' where x'y':"{x', y'} \<in> G \<and> x' \<notin> X \<and> y' \<in> X  \<and> 
                                    {connected_component (graph_diff G X) x, {y}} = 
                                    {connected_component (graph_diff G X) x', {y'}}" 
        by auto
      have "y = y'" 
        by (metis (no_types, lifting) doubleton_eq_iff empty_iff
            in_own_connected_component insert_iff x'y' xy)
      then have "x' \<in> a" 
        by (metis (no_types, lifting) CollectI doubleton_eq_iff in_own_connected_component x'y' xy)
      then show "a \<noteq> {}" by auto
    qed
    have "\<forall>a\<in>?Z2. \<exists>b\<in> Vs ?Z2. b \<in> a"
    proof
      fix a
      assume "a \<in> ?Z2" 
      then have "a \<noteq> {}" using `\<forall>a\<in>?Z2. a \<noteq> {}` by auto

      then obtain x where "x \<in> a" by blast
      then have "x \<in> Vs ?Z2" using `a \<in> ?Z2` 
        by (meson vs_member_intro)
      then show "\<exists>b\<in> Vs ?Z2. b \<in> a" 
        using \<open>x \<in> a\<close> by blast
    qed
    then  have "\<exists>Z' \<subseteq> Vs ?Z2. \<forall>C \<in> ?Z2. \<exists>!z \<in> Z'. z \<in> C"
      using ex_subset_same_elem_card[of ?Z2] `finite ?Z2` 41
        `finite (Vs ?Z2)`
      by presburger
    then obtain Z' where Z':"Z' \<subseteq> Vs ?Z2 \<and> ( \<forall>C \<in> ?Z2. \<exists>!z \<in> Z'. z \<in> C)" 
      by auto
    let ?M' = "{e. \<exists> x y. e = {x, y} \<and> e \<in> G \<and> 
                {connected_component (graph_diff G X) x, {y}} \<in> M' \<and> x \<in> Z'}"
    have 50:"\<forall>C \<in> odd_comps_in_diff G X. \<forall>z \<in> C.
             Vs (graph_diff (component_edges G C) {z}) = C - {z}"
    proof
      fix C 
      assume asmC:"C \<in> odd_comps_in_diff G X" 
      show "\<forall>z \<in> C. Vs (graph_diff (component_edges G C) {z}) = C - {z}"
      proof 
        fix z
        assume "z \<in> C"
        have 42:"odd_comps_in_diff (component_edges (graph_diff G X) C) {z} = {}"
          using max_barrier_add_vertex_empty_odd_components[of G X C z] 
                X_max asmC less.prems(1) less.prems(2) \<open>z \<in> C\<close> by fastforce
        show "Vs (graph_diff (component_edges G C) {z}) = C - {z}"
        proof
          show "Vs (graph_diff (component_edges G C) {z}) \<subseteq> C - {z}"
          proof
            fix x
            assume "x \<in> Vs (graph_diff (component_edges G C) {z})"
            then obtain e where e:"e \<in> (graph_diff (component_edges G C) {z}) \<and> x \<in> e"    
              by (meson vs_member_elim)
            then have "e \<in> (component_edges G C) \<and> e \<inter> {z} = {}" 
              by (simp add: graph_diff_def)
            then have "e \<subseteq> C" unfolding component_edges_def 
              by blast
            then show "x \<in> C - {z}" 
              using \<open>e \<in> component_edges G C \<and> e \<inter> {z} = {}\<close> e by blast
          qed
          show "C - {z} \<subseteq> Vs (graph_diff (component_edges G C) {z})"
          proof
            fix x
            assume asmx:"x \<in> C - {z}"
            have "singl_in_diff (component_edges (graph_diff G X) C) {z} = {}"
              using 42 odd_comps_in_diff_def by auto
            then have "singl_in_diff (component_edges G C) {z} = {}"
              by (simp add: asmC component_edges_same_in_diff)
            then have 44:"\<nexists> v.  v \<in> Vs (component_edges G C) \<and> 
              v \<notin> {z} \<and> v \<notin> Vs (graph_diff (component_edges G C) {z})"
              unfolding singl_in_diff_def by blast
            show "x \<in> Vs (graph_diff (component_edges G C) {z})"
            proof(cases "C \<in> odd_components (graph_diff G X)" )
              case True
              have "Vs (component_edges G C) = C" 
                by (meson True X_barr less.prems(1) vertices_of_edges_in_component_same)
              then have "x \<in> Vs (component_edges G C) \<and> x \<notin> {z}" 
                using asmx by blast
              then show "x \<in> Vs (graph_diff (component_edges G C) {z})"
                using "44" by blast
            next
              case False
              then have "C \<in> singl_in_diff G X" 
                by (metis UnE \<open>C \<in> odd_comps_in_diff G X\<close> odd_comps_in_diff_def)
              then have "C = {z}" unfolding singl_in_diff_def 
                using \<open>z \<in> C\<close> by fastforce
              then show ?thesis 
                using \<open>x \<in> C - {z}\<close> by blast
            qed
          qed
        qed
      qed
    qed
    have 78:"\<forall>C \<in> (odd_comps_in_diff G X). 
      \<exists>M. perfect_matching (graph_diff (component_edges G C) Z') M"
    proof
      fix C
      assume asmC: "C \<in> (odd_comps_in_diff G X)"
      have "\<exists>x y. x \<in> C \<and> y \<in> X \<and> {x, y} \<in> G" 
        using "less.prems"(2) "less.prems"(2) asmC X_barr Tutte_Theorem.odd_comps_in_diff_connected 
               less.prems(1) by metis 
      then obtain x y where xy:"x \<in> C \<and> y \<in> X \<and> {x, y} \<in> G"
        by auto
      then have "connected_component (graph_diff G X) x = C" 
        by (meson "less.prems"(1) asmC X_barr odd_comps_in_diff_is_component)
      then have "{C, {y}} \<in> ?G'" 
        using xy asmC odd_comps_in_diff_not_in_X[of C G X] by fastforce
      then have "C \<in> Vs ?G'" 
        by auto
      then have "C \<in> Vs M'" 
        using M' unfolding perfect_matching_def  by argo
      then obtain e where e:"C \<in> e \<and> e \<in> M'"
        by (meson vs_member_elim) 
      then have "\<exists>x y. {x, y} \<in> G \<and> y \<in> X \<and> e = {connected_component (graph_diff G X) x,{y}}"
        using M' unfolding perfect_matching_def by blast
      then obtain x' y' where x'y': "{x', y'} \<in> G \<and> y' \<in> X \<and> 
                                     e = {connected_component (graph_diff G X) x',{y'}}" 
        by auto
      then have 46:"connected_component (graph_diff G X) x' = C" 
        using asmC e odd_comps_in_diff_not_in_X[of C G X] by fastforce
      then have "x' \<in> C" 
        by (meson in_own_connected_component)
      let ?C' = "{c . \<exists> e. e \<in> G \<and> e = {c, y'} \<and> c \<notin> X \<and> 
                  c \<in> connected_component (graph_diff G X) x'}" 
      have "?C' \<subseteq> C"
        using 46 by force
      have 47:"{connected_component (graph_diff G X) x', {y'}} \<in> M'" 
        using e x'y' by blast
      then have "?C' = {c . \<exists> e. e \<in> G \<and> e = {c, y'}  \<and> c \<notin> X \<and>
                        c \<in> connected_component (graph_diff G X) x'} \<and> 
                        {connected_component (graph_diff G X) x', {y'}} \<in> M'" 
        by force
      have "\<exists>x' y'. ?C' = {c . \<exists> e. e \<in> G \<and> e = {c, y'}  \<and> c \<notin> X \<and> 
                          c \<in> connected_component (graph_diff G X) x'} \<and> y' \<in> X \<and> 
                          {connected_component (graph_diff G X) x', {y'}} \<in> M'"
        apply rule using 47 x'y' by blast
      then have "?C' \<in> ?Z2" 
        by blast
      have "\<forall>C \<in> ?Z2. \<exists>!z \<in> Z'. z \<in> C" 
        using Z' by linarith
      then have 48:" \<exists>!z \<in> Z'. z \<in> ?C'" 
        by (metis (no_types, lifting) \<open>?C' \<in> ?Z2\<close>)
      have "Z' \<subseteq> Vs ?Z2" 
        using Z' by linarith
      have "Vs ?Z2 \<inter> C = ?C'"
        using M' unfolding perfect_matching_def
        using possible_connected_vertices_in_expanded_graph_intersection[of G X C x' y' M']
        using "47" X_barr \<open>x' \<in> C\<close> asmC less.prems(1) x'y' by fastforce
      then have "\<exists>!z \<in> Z'. z \<in> C" 
        by (smt (verit) Int_iff \<open>Z' \<subseteq> Vs ?Z2\<close> 48 subset_eq)
      then obtain z where z:"z \<in> Z' \<and> z \<in> C" by auto
      have "C - Z' = C - {z}"
      proof
        show " C - Z' \<subseteq> C - {z}" 
          by (simp add: z subset_Diff_insert)
        show "C - {z} \<subseteq> C - Z'" 
          using \<open>\<exists>!z. z \<in> Z' \<and> z \<in> C\<close> z by blast
      qed
      have 68:"graph_diff (component_edges G C) Z' = graph_diff (component_edges G C) {z}"
        unfolding graph_diff_def
        apply safe 
        unfolding component_edges_def
        using z \<open>\<exists>!z. z \<in> Z' \<and> z \<in> C\<close> by blast+
      let ?Cz = "(graph_diff (component_edges G C) {z})"
      have "odd_comps_in_diff (component_edges (graph_diff G X) C) {z} = {}"
        using max_barrier_add_vertex_empty_odd_components[of G X C z] 
              X_max asmC z less.prems(1) less.prems(2) by fastforce
      then have "odd_comps_in_diff (component_edges G C) {z} = {}"
        by (simp add: asmC component_edges_same_in_diff) 
      have 51:"Vs (graph_diff (component_edges G C) {z}) = C - {z}"
        by (simp add: asmC z 50)
      have "(component_edges G C) \<subseteq> G" 
        unfolding component_edges_def 
        by force
      then have 58:"graph_invar (component_edges G C)"
        using graph_invar_subgraph less.prems(1)
        by auto
      have 67:"graph_diff (component_edges G C) {z} \<subseteq> G" 
        unfolding graph_diff_def component_edges_def
        by blast
      then have 52:"graph_invar (graph_diff (component_edges G C) {z})"
        by (simp add: "58" graph_invar_diff)
      have "card (Vs (graph_diff (component_edges G C) {z})) < card (Vs G)" 
        by (metis "51" \<open>finite (Vs G)\<close> asmC card_seteq component_in_E linorder_le_less_linear
            subset_Diff_insert subset_insertI2 subset_insert_iff z)
      then have 53:"tutte_condition ?Cz \<Longrightarrow> \<exists>M. (perfect_matching ?Cz) M" 
        using "less.hyps"(1) 52 by presburger
      have "\<exists>M. perfect_matching (graph_diff (component_edges G C) {z}) M" 
      proof(cases "C \<in> odd_components (graph_diff G X)")
        case True
        then have 54:"\<exists> c \<in> Vs (graph_diff G X).
              connected_component (graph_diff G X) c = C \<and> odd (card C)"
          unfolding odd_components_def odd_component_def
          by blast
        have 56:"Vs (component_edges G C) = C" 
          by (meson True X_barr less.prems(1) vertices_of_edges_in_component_same)
        show ?thesis 
        proof(rule ccontr)
          assume " \<nexists>M. perfect_matching
         (graph_diff (component_edges G C) {z}) M"
          then have "\<not> tutte_condition ?Cz" 
            using 53 by blast
          then obtain Y where Y:"Y\<subseteq> Vs ?Cz \<and> card (odd_comps_in_diff ?Cz Y) > card Y"
             by (meson le_less_linear tutte_condition_def)
          have "Vs ?Cz = C - {z}" 
            using \<open>Vs (graph_diff (component_edges G C) {z}) = C - {z}\<close> by auto
          have "odd (card C)" 
            using 54 by blast
          then have "even (card (C - {z}))"
            by (simp add: z)
          then have "even (card (odd_comps_in_diff ?Cz Y) - card Y)"
            by (metis "51" "52" Y diff_odd_component_parity' even_diff_nat linorder_le_less_linear)
          then have "card (odd_comps_in_diff ?Cz Y) - card Y \<ge> 2" 
            by (metis (no_types, lifting) One_nat_def Suc_leI Y add_0_right add_Suc_right 
                diff_diff_cancel diff_zero le_eq_less_or_eq nat_dvd_1_iff_1 nat_neq_iff 
                one_add_one zero_order(2))
          then have 63:"card (odd_comps_in_diff ?Cz Y) \<ge> card Y + 2" 
            by linarith
          have 55:"odd_comps_in_diff G (X \<union> (Y \<union> {z})) = odd_comps_in_diff G X - {C} \<union> 
                odd_comps_in_diff (component_edges (graph_diff G X) C) (Y \<union> {z})" 
            by (smt (verit, ccfv_threshold) "51" Diff_empty Un_empty Un_subset_iff X_barr Y 
                add_subset_change_odd_components asmC empty_not_insert insert_Diff 
                insert_Diff_single insert_is_Un less.prems(1) subset_Diff_insert subset_Un_eq z)
          have 62:"(odd_comps_in_diff G X - {C}) \<inter> 
                (odd_comps_in_diff (component_edges (graph_diff G X) C) (Y\<union>{z})) = {}"
            using new_components_intersection_old_is_empty[of G X C "(Y\<union>{z})"] 
                  "51" X_barr Y asmC less.prems(1) z
            by (simp add: subset_Diff_insert)
          then have 60:"card (odd_comps_in_diff G (X \<union> (Y \<union>{z}))) = 
                        card (odd_comps_in_diff G X - {C})
                      + card (odd_comps_in_diff (component_edges (graph_diff G X) C) (Y\<union>{z}))" 
            by (metis "55" card_Un_disjoint diff_components_finite finite_Un less.prems(1))
          have 60:"card (odd_comps_in_diff G X - {C}) = card (odd_comps_in_diff G X) - 1" 
            by (simp add: asmC diff_components_finite less.prems(1))
          then have 61:"card (odd_comps_in_diff G X - {C}) = card X - 1" 
            using \<open>card (odd_comps_in_diff G X) = card X\<close> by presburger
          have "odd_components (graph_diff (component_edges G C) (Y \<union> {z})) =
                odd_components (graph_diff ?Cz Y)" 
            using graph_diff_trans[of "(component_edges G C)" Y "{z}"]
                  58  by (metis graph_diff_trans sup_commute)
          have 59:"\<forall>v. v \<in> Vs (component_edges G C) \<and> v \<notin> Y \<union> {z} \<longleftrightarrow>
                 v \<in> Vs (graph_diff (component_edges G C) {z}) \<and>  v \<notin> Y "
              by (simp add: 56 `Vs ?Cz = C - {z}`)
          have 60:"graph_diff (component_edges G C) (Y \<union> {z}) =
                graph_diff (graph_diff (component_edges G C) {z}) Y"
            by (metis 58 graph_diff_trans sup_commute)
          then have "singl_in_diff (component_edges G C) (Y \<union> {z}) =
                     singl_in_diff (graph_diff (component_edges G C) {z}) Y"
            unfolding singl_in_diff_def using 59 by fastforce
          then have "odd_comps_in_diff (component_edges G C) (Y\<union>{z}) = odd_comps_in_diff ?Cz Y" 
            unfolding odd_comps_in_diff_def 
            using 60 by presburger
          then have "card (odd_comps_in_diff G (X \<union> (Y\<union>{z}))) = 
                     card X - 1 + card (odd_comps_in_diff ?Cz Y)"
            by (metis "52" "55" "61" "62" asmC card_Un_disjoint component_edges_same_in_diff 
                diff_components_finite finite_Diff less.prems(1))
          then have "card (odd_comps_in_diff G (X \<union> (Y\<union>{z}))) \<ge> card X - 1 + card Y + 2" 
            using 63 by linarith
          then have 66:"card (odd_comps_in_diff G (X \<union> (Y\<union>{z}))) \<ge> card X + card Y + 1" 
            by linarith
          have "X \<inter> (Y\<union>{z}) = {}"
            by (smt (verit, best) Un_insert_right Vs_subset X_barr Y asmC sup_bot.right_neutral z
                component_edges_same_in_diff disjoint_iff_not_equal graph_diff_subset insertE 
                less.prems(1) new_components_in_old_one odd_comps_in_diff_not_in_X subset_eq)
          then have 64:"card (X \<union> (Y\<union>{z})) = card X + card(Y\<union>{z})" 
            by (meson X_barr Y 52 card_Un_disjoint finite.emptyI finite.insertI finite_Un 
                finite_subset less.prems(1))
          have "Y \<inter> {z} = {}" 
            using \<open>Vs ?Cz = C - {z}\<close> Y by blast
          then have 65:"card (X \<union> (Y\<union>{z})) = card X + card Y + 1" 
            by (metis "52" "64" Int_Un_eq(3) One_nat_def Un_insert_right Y add.right_neutral 
                add_Suc_right card.insert disjoint_insert(1) rev_finite_subset)
          have "card (odd_comps_in_diff G (X \<union> (Y\<union>{z}))) \<le> card (X \<union> (Y\<union>{z}))" 
            using `tutte_condition G` 
            by (metis (no_types, lifting) "51" Un_subset_iff X_barr Y asmC component_in_E 
                insert_Diff insert_is_Un subset_Un_eq tutte_conditionE z)
          then have "card (odd_comps_in_diff G (X \<union> (Y \<union> {z}))) = card (X \<union> (Y \<union> {z}))" 
            using 65 66 le_antisym by presburger
          then have "barrier G (X \<union> (Y\<union>{z}))" 
            by (simp add: barrier_def)
          have "X \<subseteq> X \<union> (Y\<union>{z})" 
            by auto
          have "X \<union> (Y\<union>{z}) \<subseteq> Vs G" 
            by (metis Un_insert_right Un_least Vs_subset X_barr Y 67 asmC component_in_E 
                dual_order.trans insert_Diff insert_subset sup_bot.right_neutral z)
          then show False
            using X_max 
            by (metis (no_types, lifting) Int_absorb1 Un_empty \<open>X \<inter> (Y \<union> {z}) = {}\<close> 
                \<open>X \<subseteq> X \<union> (Y \<union> {z})\<close> \<open>barrier G (X \<union> (Y \<union> {z}))\<close> insert_not_empty mem_Collect_eq
                subset_Un_eq sup_commute)
        qed
      next
        case False
        then have "C \<in> singl_in_diff G X" 
          by (metis UnE \<open>C \<in> odd_comps_in_diff G X\<close> odd_comps_in_diff_def)
        then have 67:"\<exists> v. C = {v} \<and> v \<in> Vs G \<and> v \<notin> X \<and> v \<notin> Vs (graph_diff G X)"
          unfolding singl_in_diff_def 
          by blast
        then have "C = {z}" 
          using z by fastforce
        then have "\<forall>e\<subseteq>C. e \<in> G \<longrightarrow> e \<in> graph_diff G X" 
          using less.prems(1) by fastforce
        then have "component_edges G C = {}"
          unfolding component_edges_def
          using 67 by force
        then have "graph_diff (component_edges G C) {z} = {}" 
          by (metis bot.extremum_uniqueI graph_diff_subset)
        have "perfect_matching {} {}" 
          unfolding perfect_matching_def matching_def
          using graph_abs_empty
          by blast
        then show ?thesis 
          using \<open>graph_diff (component_edges G C) {z} = {}\<close> by auto
      qed
      then show "\<exists>M. perfect_matching (graph_diff (component_edges G C) Z') M"
        by (simp add: 68)
    qed
    have "M' \<subseteq> ?G'" 
      using M' unfolding perfect_matching_def by blast
    have "Z' \<inter> X = {}" 
      using \<open>Vs ?Z2 \<inter> X = {}\<close> Z' by blast
    let ?M2 = "{e. \<exists> x y. e = {x, y} \<and> x \<in> Z' \<and>
               {connected_component (graph_diff G X) x, {y}} \<in> M'}"
    have "Vs M' = Vs ?G'" 
      using M' unfolding perfect_matching_def by blast
    have "Vs ?M2 = Z' \<union> X"
    proof(safe)
      {
        fix x
        assume "x \<in> Vs ?M2" "x \<notin> X"
        then have "\<exists>e. x \<in> e \<and> ( \<exists> x y. e = {x, y} \<and> x \<in> Z' \<and> 
                      {connected_component (graph_diff G X) x, {y}} \<in> M')"
          by (smt (verit) mem_Collect_eq vs_member)
        then obtain e x' y' where e:
          "x \<in> e \<and> e = {x', y'} \<and> x' \<in> Z' \<and> {connected_component (graph_diff G X) x', {y'}} \<in> M'"
          by auto
        then have "x' \<notin> X" 
          using \<open>Vs ?Z2 \<inter> X = {}\<close> Z' empty_iff by auto
        have "{connected_component (graph_diff G X) x', {y'}} \<in> ?G'" 
          using \<open>M' \<subseteq> ?G'\<close> e by blast
        then  have "y' \<in> X" 
          by (smt (verit) \<open>x' \<notin> X\<close> doubleton_eq_iff in_own_connected_component mem_Collect_eq 
              singletonD)
        then show "x \<in> Z'" 
          using e \<open>x \<notin> X\<close> by blast
      }
      {
        fix x
        assume " x \<in> Z'"
        then have "x \<in>  Vs ?Z2" 
          using Z' by blast
        then obtain C x' y' where C: "C = {c. \<exists>e. e \<in> G \<and> e = {c, y'} \<and> 
                                      c \<notin> X \<and> c \<in> connected_component (graph_diff G X) x'} \<and> 
                                      {connected_component (graph_diff G X) x', {y'}} \<in> M' \<and> x \<in> C"
          by (smt (z3) mem_Collect_eq vs_member)
        then have "{connected_component (graph_diff G X) x, {y'}} \<in> M'" 
          using connected_components_member_eq by force
        then show "x \<in> Vs {{x, y} |x y. x \<in> Z' \<and>
                                        {connected_component (graph_diff G X) x, {y}} \<in> M'}"
          using \<open>x \<in> Z'\<close> by auto
      }
      fix x
      assume "x \<in> X" 
      then have "{x} \<in> Vs ?G'" 
        using \<open>\<forall>x \<in> X. {x} \<in> Vs ?G'\<close> by fastforce
      then have "{x} \<in> Vs M'" 
        using \<open>Vs M' = Vs ?G'\<close> by blast
      then obtain e' z' x' where e':"{x} \<in> e' \<and> e' \<in> M' \<and> {z', x'} \<in> G \<and> z' \<notin> X \<and> x' \<in> X \<and> e' =
                                     {connected_component (graph_diff G X) z', {x'}}"
        using \<open>M' \<subseteq> ?G'\<close>
        by (smt (verit, best) mem_Collect_eq subset_eq vs_member_elim)
      then have "x = x'" 
        using \<open>x \<in> X\<close> in_own_connected_component by force
      have 69:"\<exists>z \<in> connected_component (graph_diff G X) z'. z \<in> Z'"
        by (metis (mono_tags, lifting) Z' e' mem_Collect_eq)
      then obtain z where z:"z \<in> connected_component (graph_diff G X) z' \<and> z \<in> Z'"
        by auto
      then have "{connected_component (graph_diff G X) z, {x}} \<in> M'" 
        using \<open>x = x'\<close> e' connected_components_member_eq by force
      then show "x \<in> Vs {{x, y} |x y. x \<in> Z' \<and> {connected_component (graph_diff G X) x, {y}} \<in> M'}"
        using z by auto
    qed   
    have M2_in_G:"?M2 \<subseteq> G" 
    proof
      fix e
      assume "e \<in> ?M2"
      then obtain z x where edge_in_M': "e = {z, x} \<and> z \<in> Z' \<and> 
                                         {connected_component (graph_diff G X) z, {x}} \<in> M'" 
        by blast
      then have "z \<notin> X" 
        using \<open>Z' \<inter> X = {}\<close> by blast
      have "{connected_component (graph_diff G X) z, {x}} \<in> ?G'" 
        using `M' \<subseteq> ?G'` edge_in_M' by blast
      then have "x \<in> X" 
        by (smt (verit, ccfv_SIG) \<open>z \<notin> X\<close> doubleton_eq_iff in_own_connected_component
            mem_Collect_eq singletonD)
      let ?C' = "{c. \<exists>e. e \<in> G \<and> e = {c, x} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff G X) z}" 
      have "?C' \<in> ?Z2" 
        using edge_in_M' `x \<in> X` by blast
      then obtain C where C:"C \<in> ?Z2 \<and>  z \<in> C"  
        by (metis (no_types, lifting) Z' edge_in_M' subsetD vs_member_elim)
      obtain z' x' where z'x':"{connected_component (graph_diff G X) z', {x'}} \<in> M' \<and>
                               C = {c. \<exists>e. e \<in> G \<and> e = {c, x'} \<and> c \<notin> X \<and>
                               c \<in> connected_component (graph_diff G X) z'}"
        using \<open>C \<in>?Z2 \<and> z \<in> C\<close> by blast
      then have z_comp:"z \<in> connected_component (graph_diff G X) z'" 
        using \<open>C \<in>?Z2 \<and> z \<in> C\<close> by blast
      then have "connected_component (graph_diff G X) z \<in>
                 {connected_component (graph_diff G X) z, {x}}
                  \<inter> {connected_component (graph_diff G X) z', {x'}}"   
        by (metis Int_iff connected_components_member_eq insertCI)
      then have "{connected_component (graph_diff G X) z, {x}} =
         {connected_component (graph_diff G X) z', {x'}}" 
        using M' unfolding perfect_matching_def
        by (metis (no_types, lifting) edge_in_M' empty_iff matching_def z'x')
      then have "x = x'" 
        by (metis \<open>x \<in> X\<close> \<open>z \<notin> X\<close> emptyE insert_iff z_comp)
      then have "C = ?C'" 
        using connected_components_member_eq z'x' z_comp by force
      then have "z \<in> ?C'" using \<open>C \<in>?Z2 \<and> z \<in> C\<close> by auto
      then show "e \<in> G" 
        using edge_in_M' by fastforce
    qed
    have "perfect_matching ?M2 ?M2" 
      unfolding perfect_matching_def
    proof
      have "matching ?M2" 
        unfolding matching_def
      proof
        fix e1
        assume "e1 \<in> ?M2"
        then obtain z1 x1 where e1_in_M': "e1 = {z1, x1} \<and> z1 \<in> Z' \<and>
                                          {connected_component (graph_diff G X) z1, {x1}} \<in> M'"
          by blast
        then have "z1 \<notin> X" 
          using \<open>Z' \<inter> X = {}\<close> by blast
        have "{connected_component (graph_diff G X) z1, {x1}} \<in> ?G'" 
          using \<open>M' \<subseteq> ?G'\<close> e1_in_M' by blast
        then have "x1 \<in> X"    
          by (smt (verit) \<open>z1 \<notin> X\<close> doubleton_eq_iff in_own_connected_component mem_Collect_eq 
              singletonD)
        let ?C1 = "{c. \<exists>e. e \<in> G \<and> e = {c, x1} \<and> c \<notin> X \<and>
                           c \<in> connected_component (graph_diff G X) z1}"
        have "?C1 \<in> ?Z2"
          using e1_in_M'`x1 \<in> X` by blast
        then obtain C1 where C1:"C1 \<in> ?Z2 \<and> z1 \<in> C1 " 
          by (metis (no_types, lifting) Z' e1_in_M' subsetD vs_member_elim)
        obtain z1' x1' where z1x1:"{connected_component (graph_diff G X) z1', {x1'}} \<in> M' \<and>
                                   C1 = {c. \<exists>e. e \<in> G \<and> e = {c, x1'} \<and> c \<notin> X \<and>
                                   c \<in> connected_component (graph_diff G X) z1'}"
          using C1 by blast
        then have 70:"z1 \<in> connected_component (graph_diff G X) z1'" 
          using C1 by blast
        then have 76:"connected_component (graph_diff G X) z1 \<in>
                   {connected_component (graph_diff G X) z1, {x1}} 
                    \<inter> {connected_component (graph_diff G X) z1', {x1'}}"   
          by (metis Int_iff connected_components_member_eq insertCI)
        then have "{connected_component (graph_diff G X) z1, {x1}} =
                   {connected_component (graph_diff G X) z1', {x1'}}"
          using M' unfolding perfect_matching_def
          by (metis (no_types, lifting) e1_in_M' empty_iff matching_def z1x1)
        then have "x1 = x1'" 
          by (metis "70" \<open>x1 \<in> X\<close> \<open>z1 \<notin> X\<close> empty_iff insert_iff)
        then have "C1 = ?C1" 
          using "70" connected_components_member_eq z1x1 by fast
        then have "z1 \<in> ?C1" 
          using C1 by blast
        have 71:"{connected_component (graph_diff G X) z1, {x1}} \<in> ?G'" 
          using \<open>M' \<subseteq> ?G'\<close> e1_in_M' by blast
        then have "z1 \<notin> X" 
          using \<open>Vs ?Z2 \<inter> X = {}\<close> Z' e1_in_M' empty_iff subset_iff by auto
        then have "x1 \<in> X" 
          by (smt (z3) 71 doubleton_eq_iff in_own_connected_component mem_Collect_eq singletonD)
        show "\<forall>e2 \<in> ?M2.  e1 \<noteq> e2 \<longrightarrow> e1 \<inter> e2 = {}"
        proof
          fix e2
          assume "e2 \<in> ?M2"
          then obtain z2 x2 where e2_in_M': "e2 = {z2, x2} \<and> z2 \<in> Z' \<and> 
                                             {connected_component (graph_diff G X) z2, {x2}} \<in> M'" 
            by blast
          then have "z2 \<notin> X" 
            using \<open>Z' \<inter> X = {}\<close> by blast
          have "{connected_component (graph_diff G X) z2, {x2}} \<in> ?G'" 
            using \<open>M' \<subseteq> ?G'\<close> e2_in_M' by blast
          then have "x2 \<in> X"          
            by (smt (verit, ccfv_SIG) \<open>z2 \<notin> X\<close> doubleton_eq_iff in_own_connected_component 
                mem_Collect_eq singletonD)
          let ?C2 = "{c. \<exists>e. e \<in> G \<and> e = {c, x2} \<and> c \<notin> X \<and>
                             c \<in> connected_component (graph_diff G X) z2}"
          have "?C2 \<in> ?Z2" 
            using e2_in_M'`x2 \<in> X` by blast
          then obtain C2 where C2:"C2 \<in> ?Z2 \<and> z2 \<in> C2 "
            by (metis (no_types, lifting) Z' e2_in_M' subsetD vs_member_elim)
          obtain z2' x2' where z2x2: "{connected_component (graph_diff G X) z2', {x2'}} \<in> M' \<and> 
                                      C2 = {c. \<exists>e. e \<in> G \<and> e = {c, x2'} \<and> c \<notin> X \<and>
                                      c \<in> connected_component (graph_diff G X) z2'}"
            using C2 by blast
          then have 72:"z2 \<in> connected_component (graph_diff G X) z2'" 
            using C2 by blast
          then have "connected_component (graph_diff G X) z2 \<in>
                    {connected_component (graph_diff G X) z2, {x2}} 
                    \<inter> {connected_component (graph_diff G X) z2', {x2'}}"   
            by (metis Int_iff connected_components_member_eq insertCI)
          then have "{connected_component (graph_diff G X) z2, {x2}} =
                     {connected_component (graph_diff G X) z2', {x2'}}" 
            using M' unfolding perfect_matching_def matching_def
            by (metis (no_types, lifting) e2_in_M' empty_iff z2x2)
          then have "x2 = x2'" 
            by (metis (no_types, lifting) 72 connected_components_member_eq doubleton_eq_iff)
          then have "C2 = ?C2" 
            by (metis (no_types, lifting) Collect_cong 72 z2x2 connected_components_member_eq)
          then have "z2 \<in> ?C2" 
            using \<open>C2 \<in> ?Z2 \<and> z2 \<in> C2\<close> by blast
          have 73:"{connected_component (graph_diff G X) z2, {x2}} \<in> ?G'" 
            using \<open>M' \<subseteq> ?G'\<close> e2_in_M' by blast
          then have "z2 \<notin> X" 
            using \<open>Vs ?Z2 \<inter> X = {}\<close> Z' e2_in_M' empty_iff subset_iff by auto
          show " e1 \<noteq> e2 \<longrightarrow> e1 \<inter> e2 = {}"
          proof
            assume " e1 \<noteq> e2"
            have "x1 \<noteq> z2" 
              using \<open>x1 \<in> X\<close> \<open>z2 \<notin> X\<close> by blast
            then have "connected_component (graph_diff G X) z2 \<noteq> {x1}" 
              using in_own_connected_component by force
            have "x2 \<noteq> z1" 
              using \<open>x2 \<in> X\<close> \<open>z1 \<notin> X\<close> by blast
            then have 74:"connected_component (graph_diff G X) z1 \<noteq> {x2}" 
              using in_own_connected_component by force
            then have "x1 \<noteq> x2 \<or> z1 \<noteq> z2" 
              using e1_in_M' e2_in_M' `e1 \<noteq> e2` by fastforce
            have "matching M'" 
              using M' perfect_matching_def by blast
            have 75:"{connected_component (graph_diff G X) z1, {x1}} 
                   \<noteq> {connected_component (graph_diff G X) z2, {x2}}"
            proof
              assume asm:"{connected_component (graph_diff G X) z1, {x1}} =
                          {connected_component (graph_diff G X) z2, {x2}}" 
              then have "x1 = x2" 
                by (metis 74 doubleton_eq_iff)
              have "connected_component (graph_diff G X) z1 = 
                    connected_component (graph_diff G X) z2" 
                by (metis \<open>x1 = x2\<close> asm doubleton_eq_iff)
              then have "?C1 = ?C2" 
                using  \<open>x1 = x2\<close> by presburger
              then have "z1 = z2" 
                by (metis (no_types, lifting) \<open>C1 = ?C1\<close> C1 Z' \<open>z2 \<in> ?C2\<close> e1_in_M' e2_in_M')
              then show False 
                using \<open>x1 = x2\<close> \<open>x1 \<noteq> x2 \<or> z1 \<noteq> z2\<close> by blast
            qed
            have 77:"{connected_component (graph_diff G X) z1, {x1}}
                   \<inter> {connected_component (graph_diff G X) z2, {x2}} = {}"
              using \<open>matching M'\<close> unfolding matching_def 
              by (simp add: "75" e1_in_M' e2_in_M')
            then have "x1 \<noteq> x2" 
              by blast
            then have "z1 \<noteq> z2" 
              using 76 77 by force
            then have "{z1, x1} \<inter> {z2, x2} = {}" 
              using \<open>x1 \<noteq> x2\<close> \<open>x1 \<noteq> z2\<close> \<open>x2 \<in> X\<close> \<open>z1 \<notin> X\<close> by fastforce
            then show " e1 \<inter> e2 = {}" 
              using e1_in_M' e2_in_M' by fastforce
          qed
        qed
      qed
      have "?M2 \<subseteq> ?M2" by auto
      have "Vs ?M2 = Vs ?M2" by auto
      show "?M2 \<subseteq> ?M2" "matching ?M2 \<and> Vs ?M2 = Vs ?M2"
        using \<open>matching ?M2\<close> by blast+
    qed
    let ?ce = "(\<lambda> C. {(graph_diff (component_edges G C) Z')})"
    let ?CES = " {(graph_diff (component_edges G C) Z')| C. C \<in> (odd_comps_in_diff G X)}"
    let ?E' = "?CES \<union> {?M2}"
    have "\<forall>CE \<in> ?CES. \<exists>M. perfect_matching CE M" 
      using 78 by blast
    then have 83:"\<forall>CE \<in> ?E'. \<exists>M. perfect_matching CE M" 
      using \<open>perfect_matching ?M2 ?M2\<close> by blast
    have 79:"?CES  =  ( \<Union>C\<in>(odd_comps_in_diff G X). (?ce C))"
      by(safe;auto)
    have "finite ( \<Union>C\<in>(odd_comps_in_diff G X). (?ce C))" 
      by (meson 25 \<open>graph_invar ?G'\<close> finite.emptyI finite_UN_I finite_insert finite_subset)
    then  have "finite ?CES" 
      using 79 by presburger
    then have "finite ?E'" 
      by blast
    have disj:"\<forall>CE1 \<in> ?CES. \<forall>CE2 \<in> ?CES. CE1 \<noteq> CE2 \<longrightarrow> Vs CE1 \<inter> Vs CE2 = {}"
    proof(safe)
      fix C Ca x xa
      {
        fix  C Ca e xa
        assume asm: "C \<in> odd_comps_in_diff G X"
               "Ca \<in> odd_comps_in_diff G X"
               " e \<in> graph_diff (component_edges G C) Z'"
               " e \<notin> graph_diff (component_edges G Ca) Z'"
               " xa \<in> Vs (graph_diff (component_edges G C) Z')"
               "xa \<in> Vs (graph_diff (component_edges G Ca) Z')"
        have 81:"graph_diff (component_edges G C) Z' \<subseteq> (component_edges G C)"
          by (simp add: graph_diff_subset)
        then have "e \<in> (component_edges G C)" 
          by (simp add: asm(3) subset_eq)
        have "e \<inter> Z' = {}"  
          by (metis (mono_tags, lifting) asm(3) graph_diff_def mem_Collect_eq)
        have 80:"graph_diff (component_edges G Ca) Z' \<subseteq> (component_edges G Ca)"
          by (simp add: graph_diff_subset)
        then have "e \<notin>  (component_edges G Ca)" 
          using \<open>e \<inter> Z' = {}\<close> asm(4) graph_diff_def by blast
        then have "(component_edges G Ca) \<noteq> (component_edges G C)" 
          using \<open>e \<in> component_edges G C\<close> by blast
        then have "Ca \<noteq> C" unfolding component_edges_def 
          by blast
        then have "Ca \<inter> C = {}" 
          by (meson asm(1-2) diff_component_disjoint less.prems(1))
        have 82:"Vs (graph_diff (component_edges G C) Z') \<subseteq> Vs (component_edges G C)" 
          by (simp add: Vs_subset 81)
        have "Vs (graph_diff (component_edges G Ca) Z') \<subseteq> Vs (component_edges G Ca)" 
          by (simp add: Vs_subset 80)
        then have "Vs (graph_diff (component_edges G Ca) Z') \<inter> 
                   Vs (graph_diff (component_edges G C) Z') = {}" 
          by (smt (verit, ccfv_SIG) "82" X_barr \<open>Ca \<inter> C = {}\<close> asm(1-2) disjoint_iff_not_equal
              component_edges_same_in_diff less.prems(1) new_components_in_old_one subsetD)
        then show  "xa \<in> {}" 
          using asm(5-6) by blast
      }
      then show "C \<in> odd_comps_in_diff G X \<Longrightarrow> 
                Ca \<in> odd_comps_in_diff G X \<Longrightarrow>
                x \<in> graph_diff (component_edges G Ca) Z' \<Longrightarrow>
                x \<notin> graph_diff (component_edges G C) Z' \<Longrightarrow>
                xa \<in> Vs (graph_diff (component_edges G C) Z') \<Longrightarrow>
                xa \<in> Vs (graph_diff (component_edges G Ca) Z') \<Longrightarrow>
                xa \<in> {}" 
        by blast
    qed 
    have "\<forall>CE \<in> ?CES.  CE \<noteq> ?M2 \<longrightarrow> Vs CE \<inter> Vs ?M2 = {}" 
    proof 
      fix CE
      assume "CE \<in> ?CES"
      then obtain C where CE_in_diff: "C \<in> odd_comps_in_diff G X \<and> CE = graph_diff
          (component_edges G C) Z'" by auto
      have "Vs CE \<inter> Z' = {}"
        by (safe; metis CE_in_diff insert_Diff subset_Diff_insert vs_graph_diff)
      have "Vs CE \<subseteq> Vs (component_edges G C)" 
        by (simp add: CE_in_diff Vs_subset graph_diff_subset)
      have "Vs (component_edges G C) \<subseteq> C"
        unfolding component_edges_def 
        by (smt (verit) mem_Collect_eq subset_eq vs_member)
      then have "Vs CE \<inter> X = {}" 
        by (metis CE_in_diff \<open>Vs CE \<subseteq> Vs (component_edges G C)\<close> odd_comps_in_diff_not_in_X 
            disjoint_iff_not_equal subset_eq)
      then have "Vs CE \<inter> (X \<union> Z') = {}" 
        using \<open>Vs CE \<inter> Z' = {}\<close> by auto
      then
      show "CE \<noteq> ?M2 \<longrightarrow> Vs CE \<inter> Vs ?M2 = {}" 
        by (simp add: Un_commute \<open>Vs ?M2 = Z' \<union> X\<close>)
    qed
    then have "\<forall>CE1 \<in> ?E'. \<forall>CE2 \<in> ?E'. CE1 \<noteq> CE2 \<longrightarrow> Vs CE1 \<inter> Vs CE2 = {}" 
      by (simp add: Int_commute disj)
    moreover have "\<forall> a \<in> ?E'. {} \<notin> a" 
      by (auto simp add: component_edges_def graph_diff_def)
    moreover have "\<forall>a \<in> ?E'. finite (Vs a)"
    proof-
      have help1: 
        "C \<in> odd_comps_in_diff G X \<Longrightarrow> finite (Vs (graph_diff (component_edges G C) Z'))" for C
        using  Vs_subset[OF Connected_Components.component_edges_subset[of G]] 
               Vs_subset[OF graph_diff_subset[of "component_edges G _" Z']]
        by (force intro: finite_subset[of _ "Vs G"] 
               simp add: Vs_subset M2_in_G less.prems(1))+
      have  "Vs ({{x, y} | x y. (x \<in> Z' \<and> 
                   {connected_component (graph_diff G X) x, {y}} \<in> M')}) \<subseteq> Vs G"
        by (auto intro: simp add: Vs_subset M2_in_G less.prems(1))
      hence "finite (Vs ({{x, y} | x y. (x \<in> Z' \<and> 
                   {connected_component (graph_diff G X) x, {y}} \<in> M')}))"
        using finite_subset  \<open>finite (Vs G)\<close> by fastforce
      thus ?thesis
        by (auto intro: help1)
    qed
    ultimately have "\<exists>M. perfect_matching (\<Union>?E') M" 
      using perfect_matching_union[of ?E'] 83 \<open>finite ?E'\<close> by blast
    then obtain M where M:"perfect_matching (\<Union>?E') M" by auto
    have "\<Union>?E' \<subseteq> G" 
      apply safe
      using graph_diff_subset Connected_Components.component_edges_subset \<open>?M2 \<subseteq> G\<close> by blast+
    have 89:"Vs (odd_comps_in_diff G X) = Vs G - X" 
    proof(safe)
      {  fix x
        assume "x \<in> Vs (odd_comps_in_diff G X)" 
        then obtain C where C:"C \<in> (odd_comps_in_diff G X) \<and> x \<in> C" 
          by (meson vs_member_elim)
        have "C \<subseteq> Vs G" 
          by (meson C component_in_E)
        then show "x \<in> Vs G" 
          using C by blast
      }
      {
        fix x
        assume "x \<in> Vs (odd_comps_in_diff G X)" "x \<in> X"
        then show False 
          by (metis odd_comps_in_diff_not_in_X disjoint_insert(2) insert_Diff vs_member_elim)
      }
      fix x
      assume "x \<in> Vs G" "x\<notin>X" 
      then have "x \<in> connected_component (graph_diff G X) x"
        by (simp add: in_own_connected_component)
      then show "x \<in> Vs (odd_comps_in_diff G X)" 
        using 23 \<open>x \<in> Vs G\<close> \<open>x \<notin> X\<close> by auto
    qed
    have 86:"\<forall>C \<in> (odd_comps_in_diff G X). \<exists>!z \<in> Z'. z \<in> C"
    proof
      fix C
      assume asmC:"C \<in> odd_comps_in_diff G X" 
      then have "C \<in> Vs M'" 
        using "25" \<open>Vs M' = Vs ?G'\<close> by blast
      then obtain e where e:"C \<in> e \<and> e \<in> M'" 
        by (meson vs_member_elim)
      then have "e \<in> ?G'" 
        using \<open>M' \<subseteq> ?G'\<close> by blast
      obtain x where x: "connected_component (graph_diff G X) x = C" 
        using asmC 84 by auto
      then obtain y where y: "{connected_component (graph_diff G X) x, {y}} \<in> M' \<and> y \<in> X" 
        using asmC e \<open>e \<in> ?G'\<close> odd_comps_in_diff_not_in_X[of C G X] by fastforce
      let ?C' = "{c . \<exists> e. e \<in> G \<and> e = {c, y} \<and> c \<notin> X \<and> 
                           c \<in> connected_component (graph_diff G X) x}" 
      have "?C' \<in> ?Z2" 
        using y by blast
      then have "\<exists>!z \<in> Z'. z \<in> ?C'" 
        by (metis (no_types, lifting) Z')
      then obtain z where z:"z \<in> Z' \<and> z \<in> ?C'" by auto
      have "?C' \<subseteq> C"
        using x by blast
      have "\<forall>y \<in> Z' - {z}. y \<notin> C" 
      proof
        fix y'
        assume asmy':"y' \<in> Z' - {z}" 
        show "y' \<notin> C"
        proof
          assume "y' \<in> C"
          have "y' \<in> Vs ?Z2" 
            using Z' asmy' by blast
          then obtain Cy where Cy:"Cy \<in> ?Z2 \<and> y' \<in> Cy" 
            by (meson vs_member_elim)
          then have "y' \<notin> X" 
            using \<open>Z' \<inter> X = {}\<close> by auto
          then  obtain x' z' where x'z': "Cy = {c. \<exists>e. e \<in> G \<and> e = {c, x'} \<and> c \<notin> X \<and>
                                                c \<in> connected_component (graph_diff G X) z'} 
                                          \<and> {connected_component (graph_diff G X) z', {x'}} \<in> M'" 
            using Cy by blast
          then have "y' \<in> connected_component (graph_diff G X) z'" 
            using Cy by fastforce
          then have "connected_component (graph_diff G X) z' = C" 
            by (metis x \<open>y' \<in> C\<close> connected_components_member_eq)
          then have "y = x'" 
            using M' unfolding perfect_matching_def
            by (smt (verit, del_insts) x'z' x y doubleton_eq_iff insertCI matching_unique_match)
          then have "Cy = ?C'" 
            using x'z' x \<open>connected_component (graph_diff G X) z' = C\<close> by presburger
          then show False 
            using Cy \<open>\<exists>!z \<in> Z'. z \<in> ?C'\<close> asmy' z by blast
        qed
      qed
      then show "\<exists>!z. z \<in> Z' \<and> z \<in> C" 
        using x z by blast
    qed
    have "Vs (\<Union>?CES) = Vs (odd_comps_in_diff G X) - Z'" 
    proof(safe)
      {
        fix x
        assume "x \<in> Vs (\<Union>?CES)" 
        then obtain C where C:"C \<in> (odd_comps_in_diff G X) \<and> x \<in> Vs (graph_diff
                                                                     (component_edges G C) Z')" 
          unfolding Vs_def by blast
        then have "Vs (graph_diff (component_edges G C) Z') \<subseteq> C" 
          by (metis (no_types, lifting) Vs_subset X_barr component_edges_same_in_diff 
              graph_diff_subset less.prems(1) new_components_in_old_one order_subst2)
        then show "x \<in>  Vs (odd_comps_in_diff G X)" 
          using C by blast
      }
      {
        fix x
        assume "x \<in> Vs (\<Union>?CES)" "x \<in> Z'"
        then obtain C where "C \<in> (odd_comps_in_diff G X) \<and> x \<in> Vs (graph_diff
                                                                   (component_edges G C) Z')" 
          unfolding Vs_def by blast
        then show False 
          by (metis \<open>x \<in> Z'\<close> insert_Diff subset_Diff_insert vs_graph_diff)
      }
      fix x
      assume asmx: "x \<in> Vs (odd_comps_in_diff G X)" " x \<notin> Z'"
      then obtain C where C:"C \<in> (odd_comps_in_diff G X) \<and> x \<in> C"
        by (meson vs_member_elim)
      then have "\<exists>!z \<in> Z'. z \<in> C" 
        by (simp add: 86)
      then obtain z where z: "z \<in> Z' \<and> z \<in> C" 
        by auto
      have 87:"Vs (graph_diff (component_edges G C) {z}) =  C - {z}" 
        by (simp add: C 50 z)
      have 88:"graph_diff (component_edges G C) Z' = graph_diff (component_edges G C) {z}"
        unfolding graph_diff_def
        apply safe 
        using z apply blast
        unfolding component_edges_def
        using \<open>\<exists>!z. z \<in> Z' \<and> z \<in> C\<close> z by fastforce
      have "C - Z' = C - {z}" 
      proof
        show " C - Z' \<subseteq> C - {z}" 
          by (simp add: z subset_Diff_insert)
        show "C - {z} \<subseteq> C - Z'" 
          using \<open>\<exists>!z. z \<in> Z' \<and> z \<in> C\<close> z by blast
      qed
      then have "Vs (graph_diff (component_edges G C) Z') =  C - Z'" 
        using 87 88 by presburger
      then have "x \<in> Vs (graph_diff (component_edges G C) Z')" 
        using C asmx(2) by blast
      then show "x \<in> Vs (\<Union>?CES)" 
        unfolding Vs_def 
        using C by blast
    qed
    then have " Vs (\<Union>?CES) = (Vs G - Z') - X" 
      using 89 by auto 
    then have "Vs (\<Union>?CES) = Vs G - (Z' \<union> X)"
      by auto  
    then have "Vs (\<Union>?CES) = Vs G - (Vs ?M2)"
      using \<open>Vs ?M2 = Z' \<union> X\<close> by presburger
    then have "Vs (\<Union>?CES) \<union> Vs (?M2) = Vs G" 
      by (metis (no_types, lifting) Int_commute Un_Diff_Int Vs_subset \<open>?M2 \<subseteq> G\<close> le_iff_inf)
    then  have "Vs (\<Union>?E') = Vs G" 
      by (smt (verit, ccfv_SIG) Sup_empty Sup_insert Sup_union_distrib Vs_def sup_bot_right)
    have "perfect_matching G M" 
      unfolding perfect_matching_def
    proof
      have "matching M" 
        using M perfect_matching_def by blast
      have "M \<subseteq> (\<Union>?E')" 
        using M unfolding perfect_matching_def
        by blast
      then have "M \<subseteq> G"  using \<open>(\<Union>?E') \<subseteq> G\<close> 
        by (meson order_trans)
      have "Vs M = Vs (\<Union>?E')" 
        using M by(simp add: perfect_matching_def)
      then have "Vs M = Vs G" 
        using `Vs (\<Union>?E') = Vs G` by auto
      then show "M \<subseteq> G " "matching M \<and> Vs G = Vs M" 
        using \<open>matching M\<close> \<open>M \<subseteq> G\<close> by auto
    qed
    then show " \<exists>M. perfect_matching G M" by auto
  qed
qed

lemma tutte:
  assumes "graph_invar G"
  shows "tutte_condition G \<longleftrightarrow> (\<exists>M. perfect_matching G M)"
  using tutte1 tutte2 assms by auto

end