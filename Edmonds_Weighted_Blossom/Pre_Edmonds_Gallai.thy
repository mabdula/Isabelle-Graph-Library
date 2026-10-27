theory Pre_Edmonds_Gallai
  imports Blossom.Blossom_Algo_Search Edmonds_Gallai_Decomposition.Edmonds_Gallai_Blossoms
begin

section \<open>A Reduced Version of the Edmonds-Gallai Decomposition\<close>

text \<open>This is specifically tailored to the weighted matching algorithm 
  accoriding to Korte's and Vygen's outline.
  We give a variant of the blossom algorithm that either returns a perfect matching if there is one,
  of it returns sets of vertices by which can make dual updates.
  These sets happend to form the decomposition.
  Only a minority of the properties of the decomposition are relevant here, however.
  Factor-criticalitly of the sets in $\mathcal{D}$ is the most important.\<close>

subsection \<open>Blossoms and the Reduced Decomposition\<close>

definition "pre_edmonds_gallai G M \<D> = 
  (disjoint \<D> \<and> \<Union> \<D> \<subseteq> Vs G \<and> (\<forall> X \<in> \<D>. X \<noteq> {}) \<and> 
    (\<forall> X Y. X \<in> \<D> \<and> Y \<in> \<D> \<and> X \<noteq> Y \<longrightarrow> (X \<leftarrow>|\<rightarrow>\<^bsub>G\<^esub> Y)) \<and>
  card \<D> > card (Neighbourhood G (\<Union> \<D>)) \<and>
  (\<forall> X x. X \<in> \<D> \<and>  x \<in> X \<longrightarrow> (\<exists> M. graph_matching (G \<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x})) \<and>
   (\<forall> v \<in> Vs G. even_vert G M v \<longrightarrow> v \<in> \<Union> \<D>))"

lemma pre_edmonds_gallaiI:
  "\<lbrakk> disjoint \<D>; 
     \<Union> \<D> \<subseteq> Vs G; 
     (\<And>X. X \<in> \<D> \<Longrightarrow> X \<noteq> {}); 
     (\<And>X Y. \<lbrakk>X \<in> \<D>; Y \<in> \<D>; X \<noteq> Y\<rbrakk> \<Longrightarrow> X \<leftarrow>|\<rightarrow>\<^bsub>G\<^esub> Y); 
     card \<D> > card (Neighbourhood G (\<Union> \<D>));
     (\<And>X x. \<lbrakk>X \<in> \<D>; x \<in> X\<rbrakk> \<Longrightarrow> \<exists>M. graph_matching (G \<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x});
     (\<And>v. \<lbrakk>v \<in> Vs G; even_vert G M v\<rbrakk> \<Longrightarrow> v \<in> \<Union> \<D>) \<rbrakk> 
  \<Longrightarrow> pre_edmonds_gallai G M \<D>"
  unfolding pre_edmonds_gallai_def by auto

lemma pre_edmonds_gallaiE:
  "\<lbrakk>pre_edmonds_gallai G M \<D>;
    \<lbrakk> disjoint \<D>; 
     \<Union> \<D> \<subseteq> Vs G; 
     (\<And>X. X \<in> \<D> \<Longrightarrow> X \<noteq> {}); 
     (\<And>X Y. \<lbrakk>X \<in> \<D>; Y \<in> \<D>; X \<noteq> Y\<rbrakk> \<Longrightarrow> X \<leftarrow>|\<rightarrow>\<^bsub>G\<^esub> Y); 
     card \<D> > card (Neighbourhood G (\<Union> \<D>));
     (\<And>X x. \<lbrakk>X \<in> \<D>; x \<in> X\<rbrakk> \<Longrightarrow> \<exists>M. graph_matching (G \<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x});
     (\<And>v. \<lbrakk>v \<in> Vs G; even_vert G M v\<rbrakk> \<Longrightarrow> v \<in> \<Union> \<D>) \<rbrakk> \<Longrightarrow> P\<rbrakk>  
    \<Longrightarrow> P"
  unfolding pre_edmonds_gallai_def by auto

lemma pre_edmonds_gallaiD:
 "pre_edmonds_gallai G M \<D> \<Longrightarrow> disjoint \<D>"
 "pre_edmonds_gallai G M \<D> \<Longrightarrow> \<Union> \<D> \<subseteq> Vs G"    
 "\<lbrakk>pre_edmonds_gallai G M \<D>;  X \<in> \<D>\<rbrakk> \<Longrightarrow> X \<noteq> {}"
 "\<lbrakk>pre_edmonds_gallai G M \<D>; X \<in> \<D>; Y \<in> \<D>; X \<noteq> Y\<rbrakk> \<Longrightarrow> X \<leftarrow>|\<rightarrow>\<^bsub>G\<^esub> Y"
 "pre_edmonds_gallai G M \<D> \<Longrightarrow> card \<D> > card (Neighbourhood G (\<Union> \<D>))"
 "\<lbrakk>pre_edmonds_gallai G M \<D>; X \<in> \<D>; x \<in> X\<rbrakk> \<Longrightarrow> \<exists>M. graph_matching (G \<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x}"
 "\<lbrakk>pre_edmonds_gallai G M \<D>; v \<in> Vs G; even_vert G M v\<rbrakk> \<Longrightarrow> v \<in> \<Union> \<D>"
  unfolding pre_edmonds_gallai_def by auto

context quot
begin

lemma pre_emonds_gallai_lonely_blossom:
  assumes assumptions: "pre_edmonds_gallai (quotG E) (quotG M) \<D>"
          "Delta E (set C) = {}"  "s = Vs E - set C" "blossom E M stem C"
           "max_card_matching E M" "u \<notin> Vs E" "u' \<notin> Vs E" "u' \<noteq> u"
  shows  "pre_edmonds_gallai E M (insert (set C) \<D>)"
proof-
  have assms:  "pre_edmonds_gallai (quotG E) (quotG M) \<D>"
          "Delta E (set C) = {}"  "distinct (butlast C)"  "odd_cycle C"
          "s = Vs E - set C" "path E C"
    using assms(1-4) distinct_append match_blossomD(2,3) path_suff' by auto
  have quot_Vs_are:"Vs (quot_graph P E - {{u}}) = s"
    using assms(2,5,6) subset_path_Vs[of E C] double_diff[of "set C" "Vs E" "Vs E"]
    by (intro Delta_wth_s_empty_quot_Vs) auto
  note pre_edmonds_gallaiD = pre_edmonds_gallaiD[OF assms(1), simplified quot_Vs_are]
  have p_in_E:"set C \<subseteq> Vs E"
    by (simp add: assms(6) subset_path_Vs)
  have goal1: "disjoint (insert (set C) \<D>)"
    using assms(5) pre_edmonds_gallaiD(1,2) 
    by(auto intro!: disjointI simp add: disjoint_def)
  have goal2: "\<Union> (insert (set C) \<D>) \<subseteq> Vs E"
    using p_in_E good_quot_map(2) pre_edmonds_gallaiD(2) by auto
  have goal3: "X \<in> insert (set C) \<D> \<Longrightarrow> X \<noteq> {}" for X
    using assms(4) pre_edmonds_gallaiD(3) odd_cycle_nempty by auto

  have goal4_helper: "X \<leftarrow>|\<rightarrow>\<^bsub> E \<^esub> Y"
    if "X \<in> \<D>" "Y \<in> \<D>" "X \<noteq> Y" for X Y
    using local.pre_edmonds_gallaiD(2,4) that 
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
    using good_quot_map(1) pre_edmonds_gallaiD(2)
    by auto
  have finite_D: "finite \<D>" 
    using graph goal2 finite_UnionD[of "insert (set C) \<D>"]
      infinite_super[of "\<Union> (insert (set C) \<D>)" "Vs E"]
    by auto

  have goal5: "card (Neighbourhood E (\<Union> (insert (set C) \<D>))) < card (insert (set C) \<D>)"
  proof-

    have rw1: "Neighbourhood (quotG E) (\<Union> \<D>) = 
           Neighbourhood (quotG E) (insert u (\<Union> \<D>))"
      using good_quot_map(1) quot_Vs_are 
      by (intro Neighbourhood_of_one_more_same_if_nin_Vs[symmetric]) blast
    have rw2: "... = Neighbourhood E (\<Union> (insert (set C) \<D>))"
      using u_not_in_D assms(5) p_in_E 
      by (subst u_in_X_Neighbourhood_expanded,                    
          (intro insertI1  arg_cong[where f = "Neighbourhood E"])+) auto
   show ?thesis
     using pre_edmonds_gallaiD(5) finite_D  card_insert_le[of \<D> "set C"]
     unfolding rw1 rw2 
     by auto
 qed

  have Vs_E_on_p_are_p:"Vs (E \<lbrakk>set C\<rbrakk>) = set C"
    using assms(4,6) 
    by(intro Vs_of_graph_inter_path)(auto simp add: odd_cycle_def)
  have length_p_geq_2: "2 \<le> length C"
    using assms(4) odd_cycle_length_verts_ge_4 by fastforce

  have "\<lbrakk>X \<in> \<D>; x \<in> X\<rbrakk> \<Longrightarrow> \<exists>M. graph_matching ( E \<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x}" for X x
    using pre_edmonds_gallaiD(6)[of X x] u_not_in_D  local.pre_edmonds_gallaiD(2) quot_Vs_are
    by(subst (asm) u_not_in_subgraph_same_subgraph) auto
  moreover have "x \<in> set C \<Longrightarrow> \<exists>M. graph_matching ( E \<lbrakk>set C\<rbrakk>) M \<and> Vs M = set C - {x}" for x
  proof(goal_cases)
    case 1
    have "\<exists>M. graph_matching (E \<lbrakk>set C\<rbrakk>) M \<and> Vs M = Vs (E \<lbrakk>set C\<rbrakk>) - {x}"
      using p_in_E  1 length_p_geq_2
      by (intro odd_cycle_graph_factor_critical[of "E \<lbrakk>set C\<rbrakk>" C x])
         (auto intro!: path_on_graph_inter_path
             simp add: dblton_E assms(3,4,6) graph graph_invar_graph_inter_Vs Vs_E_on_p_are_p)
    then show ?case 
      unfolding Vs_E_on_p_are_p by simp
  qed
  ultimately have goal6:
    "\<lbrakk>X \<in> insert (set C) \<D>; x \<in> X\<rbrakk> \<Longrightarrow> \<exists>M. graph_matching ( E \<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x}" for X x
    by auto

  have goal7: "\<lbrakk>v \<in> Vs E; even_vert E M v\<rbrakk> \<Longrightarrow> v \<in> \<Union> (insert (set C) \<D>)" for v
  proof(cases "v \<in> set C", goal_cases)
    case 1
    then show ?thesis
      by auto
  next
    case 2
    hence v_still_there:"P v = v"
      using assumptions(3) by auto
    hence "even_vert (quotG E) (quotG M) v"
      using even_vertex_blossom_contraction[OF assumptions(4) 2(2,1) assumptions(5,3,6-8)]
      by simp
    moreover have "v \<in> Vs (quotG E)"
      using "2"(1) v_still_there assumptions(6) quot_Vs_are by presburger
    ultimately show ?thesis
      using pre_edmonds_gallaiD(7) quot_Vs_are by force
  qed
  
  show ?thesis
    by(intro pre_edmonds_gallaiI goal1 goal2 goal3 goal4 goal5 goal6 goal7) auto
qed

lemma pre_emonds_gallai_connected_blossom_obtain_D:
  assumes assumptions: "pre_edmonds_gallai (quotG E) (quotG M) \<D>"
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
    using pre_edmonds_gallaiD(7)[OF assms(1), of u] 
    by auto
  thus thesis
    using 1 by auto
qed

lemma pre_emonds_gallai_connected_blossom:
  fixes D
  assumes assumptions: "pre_edmonds_gallai (quotG E) (quotG M) \<D>"
          "Delta E (set C) \<noteq> {}"  "s = Vs E - set C" "blossom E M stem C"
          "max_card_matching E M" "u \<notin> Vs E" "u' \<notin> Vs E" "u' \<noteq> u"
          "D \<in> \<D>" "u \<in> D"
    shows "pre_edmonds_gallai E M (\<D> - {D} \<union> {D - {u} \<union> set C})"
proof-
  have C_props: "C \<noteq> []" "length C \<ge> 2" "length C \<ge> 3"  "length C \<ge> 1"
    using assumptions(4)
    by (auto dest!: match_blossomD(3) simp add: odd_cycle_def  odd_cycle_nempty )

  note pre_edmonds_gallaiD = pre_edmonds_gallaiD[OF assms(1)]
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
      using pre_edmonds_gallaiD(1) 
      by (auto simp add: disjoint_def)
  next
    case (2 X Y)
    hence "X \<inter> D = {}"
      using assumptions(9) pre_edmonds_gallaiD(1)
      by(auto simp add: disjoint_def)
    then show ?case
      using "2"(2,3) local.pre_edmonds_gallaiD(2) C_inter_quot_empty
      by auto
  next
    case (3 X Y)
    hence "Y \<inter> D = {}"
      using assumptions(9) pre_edmonds_gallaiD(1)
      by(auto simp add: disjoint_def)
    then show ?case
      using "3"(2,3) local.pre_edmonds_gallaiD(2) C_inter_quot_empty
      by auto
  qed simp

  have in_D_but_not_in_E_is_u:"\<lbrakk>x \<in> X; X \<in> \<D>; x \<notin> Vs E\<rbrakk> \<Longrightarrow> x = u" for x X
    using assumptions(3) local.pre_edmonds_gallaiD(2) neq_u_notin_quotG by blast
  have in_X_has_u_is_D: "\<lbrakk>u \<in> X; X \<in> \<D>\<rbrakk> \<Longrightarrow> X = D" for X 
    using  assumptions(10,9) local.pre_edmonds_gallaiD(1)
    by(auto simp add: disjoint_def)
  have in_d_but_not_in_E_is_u:"\<lbrakk>x \<in> D; x \<notin> Vs E\<rbrakk> \<Longrightarrow> x = u" for x
    by (simp add: assumptions(9) in_D_but_not_in_E_is_u)

  have goal2: "\<Union> (\<D> - {D} \<union> {D - {u} \<union> set C}) \<subseteq> Vs E"
    using pre_edmonds_gallaiD(2) in_D_but_not_in_E_is_u in_X_has_u_is_D 
    by(auto dest: in_d_but_not_in_E_is_u 
        simp add: Vs_without_s_is_C[symmetric])

  have goal3: "X \<in> \<D> - {D} \<union> {D - {u} \<union> set C} \<Longrightarrow> X \<noteq> {}" for X
    using C_props(1) pre_edmonds_gallaiD(3) by auto

  have X_neq_D_in_s: "X \<in> \<D> - {D} \<Longrightarrow> X \<subseteq> s" for X
    using  in_X_has_u_is_D pre_edmonds_gallaiD(2)
    by(auto simp add: Vs_quotG_is)

  have goal4: 
     "\<lbrakk>X \<in> \<D> - {D} \<union> {D - {u} \<union> set C}; Y \<in> \<D> - {D} \<union> {D - {u} \<union> set C}; X \<noteq> Y\<rbrakk> \<Longrightarrow> X \<leftarrow>|\<rightarrow>\<^bsub>E\<^esub> Y"
     for X Y
  proof(elim UnE, goal_cases)
    case 1
    then show ?case 
      using pre_edmonds_gallaiD(4)[of X Y] X_neq_D_in_s 
      by (subst (asm) connected_set_of_vertices_quot_iff) auto
  next
    case 2
    hence "D \<leftarrow>|\<rightarrow>\<^bsub>quot_graph P E - {{u}}\<^esub> X" 
      using assumptions(9) local.pre_edmonds_gallaiD(4) by force
    then show ?case 
      unfolding connected_sym[of X]
      using "2"(2,3) X_neq_D_in_s Vs_without_s_is_C 
      by(subst (asm) connected_set_of_vertices_quot_iff_u)
        (auto simp add: assumptions(10))
  next
    case 3
    hence "D \<leftarrow>|\<rightarrow>\<^bsub>quot_graph P E - {{u}}\<^esub> Y" 
      using assumptions(9) local.pre_edmonds_gallaiD(4) by force
    then show ?case 
      using "3"(2,3) X_neq_D_in_s Vs_without_s_is_C 
      by(subst (asm) connected_set_of_vertices_quot_iff_u)
        (auto simp add: assumptions(10))
  qed simp
  have rw_Union: "\<Union> \<D> - {u} \<union> (Vs E - s) = \<Union> (\<D> - {D} \<union> {D - {u} \<union> set C})"
    using Vs_without_s_is_C in_X_has_u_is_D assumptions(3,6,9) 
    by auto
  have rw_card: "card (\<D> - {D} \<union> {D - {u} \<union> set C}) = card \<D>"
    using X_neq_D_in_s assumptions(3,9) good_quot_map(2) 
    by (intro card_replace) auto
  have goal5: "card (Neighbourhood E (\<Union> (\<D> - {D} \<union> {D - {u} \<union> set C})))
              < card (\<D> - {D} \<union> {D - {u} \<union> set C})"
    using pre_edmonds_gallaiD(5) assumptions(10,9) rw_Union rw_card
    by (subst (asm) u_in_X_Neighbourhood_expanded) auto

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
      using "1"(2) X_neq_D_in_s good_quot_map(1) pre_edmonds_gallaiD(2) 
      by (intro u_not_in_subgraph_same_subgraph[of X]) auto
    show ?case
      using pre_edmonds_gallaiD(6)[of X x] 1
      by(auto simp add: quotG_X_rw)
  next
    case 2
    have X_is: "X = D - {u} \<union> set C" 
      using 2 by auto
    hence x_in:"x \<in> D - {u} \<union> set C"
      using 2 by auto
    then show ?case 
      using assumptions(3,6,10) more_C_props(1) path_C dblton_E pre_edmonds_gallaiD(2)
            assms(9) distinct_C pre_edmonds_gallaiD(6)[OF assumptions(9)]
      unfolding X_is
      by(intro expand_odd_cycle_still_factor_critical) auto
  qed

  have goal7: "\<lbrakk>v \<in> Vs E; even_vert E M v\<rbrakk> \<Longrightarrow> v \<in> \<Union> (\<D> - {D} \<union> {D - {u} \<union> set C})" for v
  proof(cases "v \<in> set C", goal_cases)
    case 2
    hence v_still_there:"P v = v"
      using assumptions(3) by auto
    hence "even_vert (quotG E) (quotG M) v"
      using even_vertex_blossom_contraction[OF assumptions(4) 2(2,1) assumptions(5,3,6-8)]
      by simp
    moreover have v_inquotVs:"v \<in> Vs (quotG E)"
      using "2"(1) v_still_there assumptions(6) Vs_quotG_is by fastforce
    ultimately have v_in_DU: "v \<in> \<Union> \<D>"
      using pre_edmonds_gallaiD(7) Vs_quotG_is by force
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
  qed simp

  show ?thesis
    by(intro pre_edmonds_gallaiI goal1 goal2 goal3 goal4 goal5 goal6 goal7) auto
qed

lemma pre_emonds_gallai_perfect_after_contraction:
  assumes assumptions: "s = Vs E - set C" "blossom E M stem C"
          "graph_matching E M" "Vs (quotG M) = Vs (quotG E)"
    shows "pre_edmonds_gallai E M {set C}"
proof-

  have goal1: "disjoint {set C}"
    by(auto simp add: disjoint_def)
  have goal2: "\<Union> {set C} \<subseteq> Vs E"
    using assumptions(2) subset_path_Vs by fastforce
  have goal3: "X \<in> {set C} \<Longrightarrow> X \<noteq> {}" for X
    using assumptions(2) match_blossomD(3) odd_cycle_nempty by blast
  have goal4: "\<lbrakk>X \<in> {set C}; Y \<in> {set C}; X \<noteq> Y\<rbrakk> \<Longrightarrow> X \<leftarrow>|\<rightarrow>\<^bsub>E\<^esub> Y" for X Y
    by auto
  have not_in_M_is_in_C:"\<lbrakk>v \<in> Vs E; v \<notin> Vs M\<rbrakk> \<Longrightarrow> v \<in> set C" for v
  proof(rule ccontr, goal_cases)
    case 1
    then obtain v' where "{v, v'} \<in> E"
      by(auto simp add: vs_member' insert_commute)
    then obtain v'' where "{v, v''} \<in> quotG E" 
      using "1"(1,2,3) quot_Vs_in_s assumptions(1,3,4)  vert_in_graph_iff_in_quot_diff_u[of v M]
      by auto
    hence v_inquotM:"v \<in> Vs (quotG M)"
      by (simp add: assumptions(4) edges_are_Vs)
    then obtain v2 where "{v, v2} \<in> quotG M"
      using assumptions(3,4) doubleton_quot[of M] graph_invar_quotG 
        graph_invar_no_edge_no_vertex[of "quot_graph P M - {{u}}" v]
      by auto
    then obtain v2' where "{v, v2'} \<in> M"
      using "1"(1,2,3) v_inquotM assumptions(1,3) vert_in_graph_iff_in_quot_diff_u
      by blast
    then show ?case 
      using 1 by auto
  qed

  have u_not_in_quotM: "u \<notin> Vs (quotG M)"
  proof(rule ccontr, goal_cases)
    case 1
    then obtain x where "{u, x} \<in> quotG M"
      using assumptions(3,4) graph_invar_quotG doubleton_quot[of M]
        graph_invar_no_edge_no_vertex[of "quot_graph P M - {{u}}" u]
      by auto
    hence stem_nempty: "stem \<noteq> []"
      using "1" assumptions(1,2,3) match_blossom_def not_in_quot_matching_not_in_matching_2 odd_cycleD(3)
      by fastforce
    hence length_stem: "length stem \<ge> 2"
      using stem_even[OF assms(2)]
      by(cases stem rule: list_cases3) auto
    have s0_not_in_C: "stem ! 0 \<notin> set C" 
      using match_blossomD(2,3)[of M stem C] assms(2) length_stem
      by(cases stem rule: list_cases3, all \<open>cases C rule: list_cases_hd_and_last\<close>)
        (auto simp add: odd_cycle_def)
    have s0_neq_u: "stem ! 0 \<noteq> u"
      using stem_nempty assumptions(1,2) good_quot_map(1) mem_path_Vs' s0_not_in_C by auto
    have "(stem ! 0) \<notin> Vs (quotG M)"
    proof(rule ccontr, goal_cases)
      case 1
      then obtain y where y: "{stem ! 0, y} \<in> quotG M"
        using assumptions(3,4) graph_invar_quotG doubleton_quot[of M]
          graph_invar_no_edge_no_vertex[of "quot_graph P M - {{u}}" "stem ! 0"]
        by auto
      have "\<exists> y'. {stem ! 0, y'} \<in> M"
      proof(cases "y = u")
        case True
        then show ?thesis
          using assumptions(3) y doubleton_eq_iff[of u "stem ! 0" "stem ! 0" u]
            in_quotG_neq_u[of "stem ! 0" M] edge_in_quotG_2'_doubleton[of "stem ! 0" M]
            edges_are_Vs_2[of u "stem ! 0" "quot_graph P M - {{u}}"]
          by auto
      next
        case False
        hence "{stem ! 0, y} \<in>  M"
         using s0_neq_u assumptions(3) y u_nin_edge_in_quot[of "{stem ! 0, y}" M]
            edge_in_quot_in_graph_1'[of "{stem ! 0, y}" M] 
         by auto
        then show ?thesis 
          by auto
      qed
      hence "stem ! 0 \<in> Vs M"
        by auto
      thus False
        using stem_nempty assumptions(2) 
         by(cases stem)(auto dest!: match_blossomD(4))
    qed
    moreover have "(stem ! 0) \<in> Vs (quotG E)"
      using assumptions(1,2) mem_path_Vs quot_Vs_in_s s0_not_in_C stem_nempty by fastforce
    ultimately show False
      using assumptions(4) by blast
  qed
  have Neihgbourhood_C_empty:"Neighbourhood E (\<Union> {set C}) = {}" 
    proof(rule ccontr, goal_cases)
      case 1
      then obtain x y where xy: "x \<in> set C" "y \<notin> set C" "{x, y} \<in> E"
        by(auto simp add: Neighbourhood_def)
      hence "{y, u} \<in> quotG E"
        using assumptions(1) 
        by(intro edge_in_graph_edge_in_quot)(auto simp add: insert_commute)
      hence u_in_quot: "u \<in> Vs (quotG E)"
        by auto
      hence "u \<in> Vs (quotG M)"
        using assumptions(4) by blast
      thus False
        using u_not_in_quotM by simp
    qed
    hence goal5: "card (Neighbourhood E (\<Union> {set C})) < card {set C}"
      by auto

  have lengthC: "length C \<ge> 2" 
    using assms(2)
    by(auto dest!: match_blossomD(3) simp add: odd_cycle_def)
  have pathC: "path E C" 
    using assumptions(2) path_suff by auto

  have goal6: "\<lbrakk>X \<in> {set C}; x \<in> X\<rbrakk> \<Longrightarrow> \<exists>M. graph_matching ( E \<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x}" for X x
  proof(goal_cases)
    case 1
    have Vs_E_non_C_rw:"Vs (E \<lbrakk>set C\<rbrakk>) = set C" 
      by (simp add: Vs_of_graph_inter_path lengthC pathC)
    have "\<exists>M. graph_matching ( E \<lbrakk>set C\<rbrakk>) M \<and> Vs M = Vs ( E \<lbrakk>set C\<rbrakk>) - {x}"
      using assumptions(2) 1
      by(intro odd_cycle_graph_factor_critical[of "E \<lbrakk>set C\<rbrakk>" C x])
        (auto dest: match_blossomD
          simp add: dblton_E dblton_graph_Vs_inter Vs_E_non_C_rw lengthC
                    pathC path_on_graph_inter_path)
    thus ?case 
      using 1 by (auto simp add: Vs_E_non_C_rw)
  qed

  have goal7: "\<lbrakk>v \<in> Vs E; even_vert E M v\<rbrakk> \<Longrightarrow> v \<in> \<Union> {set C}" for v
  proof(goal_cases)
    case 1
    then obtain p where "hd p \<notin> Vs M" "last p = v" "path E p \<or> length p = 1" "odd (length p)"
      by(auto simp add: even_vert_def)
    hence p: "hd p \<notin> Vs M" "last p = v" "path E p" "p \<noteq> []"
      using 1 by(all \<open>cases p rule: list_cases3\<close>) (auto simp add: path1)
    hence "hd p \<in> set C"
      using"1"(1)  mem_path_Vs[of E p "hd p"] not_in_M_is_in_C[of "hd p"]
      by auto
    hence "v \<in> set C" 
      using  Neihgbourhood_C_empty empty_Neighbourhood_path_contained[of p E "set C"]  p(2,3,4)
      by(cases p rule: rev_cases) auto
    then show ?case 
      by auto
  qed

  show ?thesis
    by(intro pre_edmonds_gallaiI goal1 goal2 goal3 goal4 goal5 goal6 goal7 | assumption)+
qed

subsection \<open>Computation with the Blossom Algorihtm\<close>
subsubsection \<open>Alternating Search\<close>
end

datatype 'v alt_search_res =  Two_Paths "'v list" "'v list" | PEDG "'v set set"

context compute_alt_path
begin


function (domintros) compute_alt_path_or_pedg:: "'F \<Rightarrow> 'a alt_search_res" where
  "compute_alt_path_or_pedg F = 
    (if if1_cond F then
       let
         (v1,v2,v3) = sel_if1 F;
          F' = extend_forest_even_unclassified F v1 v2 v3;
         return = compute_alt_path_or_pedg F'
       in
         return
     else if if2_cond F then
        let
          (v1,v2) = sel_if2 F; 
          return = Two_Paths (get_path F v1) (get_path F v2)
        in
          return
     else
       let
          return = PEDG {{v} | v. v \<in> vset_to_set (evens F)}
       in
         return)"
  by pat_completeness auto

lemma compute_alt_path_or_pedg_same_dom:
  shows "compute_alt_path_or_pedg_dom F \<longleftrightarrow> compute_alt_path_dom F"
proof(rule, goal_cases)
  case 1
  then show ?case 
    by(induction rule: compute_alt_path_or_pedg.pinduct)
      (auto intro: compute_alt_path.domintros)
next
  case 2
  then show ?case
    by(induction rule: compute_alt_path.pinduct)
      (auto intro: compute_alt_path_or_pedg.domintros)
qed

lemmas compute_alt_path_or_pedg_psimps' =
   compute_alt_path_or_pedg.psimps[simplified compute_alt_path_or_pedg_same_dom]

lemma compute_alt_path_or_pedg_same:
  assumes "compute_alt_path_dom F"
  shows "compute_alt_path_or_pedg F = Two_Paths p1 p2 \<longleftrightarrow> compute_alt_path F = Some (p1, p2)"
  using assms
proof(induction rule: compute_alt_path.pinduct, goal_cases)
  case (1 F)
  thus ?case
    by(auto simp add: compute_alt_path_or_pedg.psimps[of F] compute_alt_path.psimps[of F] 
                      compute_alt_path_or_pedg_same_dom 
               split: if_split prod.split)
qed

lemma compute_alt_path_or_pedg_same':
  assumes "compute_alt_path_dom F"
  shows "(\<exists> D. compute_alt_path_or_pedg F = PEDG D) \<longleftrightarrow> compute_alt_path F = None"
proof(cases "compute_alt_path F", goal_cases)
  case 1
  then show ?case 
    using compute_alt_path_or_pedg_same[OF assms]
    by (cases "compute_alt_path_or_pedg F") auto
next
  case (2 a)
  then show ?case
  proof(cases a, goal_cases)
    case (1 p1 p2)
    then show ?case 
      using compute_alt_path_or_pedg_same[OF assms, of p1 p2]
      by auto
  qed
qed

lemma compute_alt_path_or_pedg_if1:
  assumes "compute_alt_path_dom F" 
    "if1_cond F"
    "(v1, v2, v3) = sel_if1 F"
    "F' = extend_forest_even_unclassified F v1 v2 v3"
  shows "compute_alt_path_or_pedg F = compute_alt_path_or_pedg F'"
  using assms
  by (auto simp add: compute_alt_path_or_pedg.psimps compute_alt_path_or_pedg_same_dom
      Let_def split: if_splits prod.splits)

lemma what_if_search_fails_pedg:
  assumes "compute_alt_path_or_pedg F = PEDG \<D>"
   and     init: "finite \<lbrace>F\<rbrace>" "\<lbrace>F\<rbrace> \<subseteq> G" 
   and invars: "forest_invar M F" "aevens F \<subseteq> Vs G"
 shows "\<exists> F'. \<not> if1_cond F' \<and> \<not> if2_cond F' \<and> forest_invar M F' \<and> aroots F' = aroots F
               \<and> \<D> = {{v} | v. v \<in> vset_to_set (evens F')} \<and> aevens F' \<subseteq> Vs G \<and> \<lbrace> F' \<rbrace> \<subseteq> G"
  using assms(1) invars init(2)
proof(induction F arbitrary: \<D> rule: compute_alt_path_pinduct_2)
  case 1
  then show ?case
    by(intro compute_alt_path_dom init invars)
next
  case (2 F)
  note IH = this
  show ?case
  proof(cases "if1_cond F")
    case True
    obtain v1 v2 v3 where sel: "(v1,v2,v3) = sel_if1 F" "if1 F v1 v2 v3"
      using if1_cond_props''''[OF True] by auto
    hence  v1v2: "{v1, v2} \<in> G - \<lbrace>F\<rbrace>" "{v2, v3} \<in> M"  "v1 \<in> aevens F" "v2 \<notin> FVs F"
        using if1_props by auto
      then have v1_v2_P:"{v1, v2} \<in> G" "{v1, v2} \<notin> \<lbrace>F\<rbrace>"
        by simp+
      define F' where "F' = extend_forest_even_unclassified F v1 v2 v3"

      have precd:"forest_extension_precond F M v1 v2 v3"
        by (simp add: 2(4) \<open>if1 F v1 v2 v3\<close> if_1_forest_extension_precond)
      note F'_props = forest_extend[OF precd, folded F'_def]
      show ?thesis
        using IH(3,5,6) matching(2) v1v2(2) v1_v2_P(1)
        by(auto intro!: IH(2)[OF True sel(1) F'_def] 
              simp add: F'_props(5)[symmetric]
                        compute_alt_path_or_pedg_if1[OF IH(1) True sel(1) F'_def] F'_props(1-3))+
  next
    case False
    note false = this
    show ?thesis
    proof(cases "if2_cond F")
      case True
      hence False
        using IH(3) false
        by(subst (asm) compute_alt_path_or_pedg_psimps'[OF IH(1)], cases "sel_if2 F")
          (auto dest!:  if2_cond_props'''') 
      thus ?thesis
        by simp
  next
    case False
    thus ?thesis
      using false IH(1,3,4,5,6)
      by(auto intro!: exI[of _ F] exI[of _ F] simp add: compute_alt_path_or_pedg_psimps')
  qed
qed
qed

lemma termination_conditions_pedg:
  assumes "\<not> if1_cond F" "\<not> if2_cond F" "forest_invar M F" "Vs G - Vs M \<subseteq> aevens F" 
          "aevens F \<subseteq> Vs G" "\<lbrace> F \<rbrace> \<subseteq> G" "aroots F \<noteq> {}"
    shows "pre_edmonds_gallai G M {{v} |v. v \<in> aevens F}"
proof-               
  have goal1: "disjoint {{v} |v. v \<in> aevens F}"
    by(auto simp add: disjoint_def)
  have goal2: "\<Union> {{v} |v. v \<in> aevens F} \<subseteq> Vs G" 
    using assms(5) by blast
  have goal3: "X \<in> {{v} |v. v \<in> aevens F} \<Longrightarrow> X \<noteq> {}" for X by auto
  have goal5: "\<lbrakk>X \<in> {{v} |v. v \<in> aevens F}; Y \<in> {{v} |v. v \<in> aevens F}; X \<noteq> Y\<rbrakk>
                \<Longrightarrow> X \<leftarrow>|\<rightarrow>\<^bsub>G\<^esub> Y" for X Y
    using assms(2)
    by(auto simp add: connected_set_of_vertices_def if2_cond_def)
  have goal6: "card (Neighbourhood G (\<Union> {{v} |v. v \<in> aevens F})) < card {{v} |v. v \<in> aevens F}"
  proof-
    have rw1: "\<Union> {{v} |v. v \<in> aevens F} = aevens F" 
      by auto
    have rw2: "card {{v} |v. v \<in> aevens F} = card (aevens F)"
      by(subst card_image[of "\<lambda> v. {v}" "aevens F", symmetric])
        (auto intro!: inj_onI arg_cong[where f = card])
    show ?thesis
      unfolding rw1 rw2 finial_forest_evens'_Neighbourhood[OF assms(1,2,3,4,6)]
      using roots(2)[OF assms(3)] assms(5)
      by (subst higher_forest_properties(1)[OF assms(3)])
         (auto intro!:  finite_subset[of "aroots F" "Vs G"]  
             simp add: card_gt_0_iff assms(7) finite_Vs)
  qed
  have goal7: "\<lbrakk>X \<in> {{v} |v. v \<in> aevens F}; x \<in> X\<rbrakk>
        \<Longrightarrow> \<exists>M. graph_matching ( G \<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x}" for x X
    by(auto intro!: exI[of _ "{}"])
  have goal8: "\<lbrakk>v \<in> Vs G; even_vert G M v\<rbrakk> \<Longrightarrow> v \<in> \<Union> {{v} |v. v \<in> aevens F}" for v
  proof(goal_cases)
    case 1
    then obtain p where "odd (length p)"
     "alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path p)"
     "hd p \<notin> Vs M" "last p = v" "distinct p" "(path G p \<or> length p = 1)"
     by(elim even_vertE) auto
   hence p_props: "odd (length p)"
     "alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path p)"
     "hd p \<notin> Vs M" "last p = v" "distinct p" "path G p" "1 \<le> length p"
     using 1(1) by(all \<open>cases p rule: list_cases3\<close>) auto
   hence p_in_G:"set p \<subseteq> Vs G"
     by (simp add: subset_path_Vs)
   have edges_p_in_G: "set (edges_of_path p) \<subseteq> G"
     by (simp add: p_props(6) path_edges_subset)
   have alt_list_p:"alt_list (\<lambda>x. x \<in> aevens F) (\<lambda>x. x \<in> aodds F) p"
    using termination_conditions_alt_paths_alternating_labels[OF
               assms(1,2,3,4) p_props(2,7,3) refl p_in_G edges_p_in_G]
    by simp
  hence "last p \<in> aevens F"
    using last_odd_P2 p_props(1) by auto
  thus ?thesis
    using p_props(4) by blast
qed
 
  show ?thesis
    by(assumption | rule pre_edmonds_gallaiI  goal1 goal2 goal3 goal5 goal6 goal7 goal8)+
qed

lemma compute_alt_path_or_pedg_from_tree_2:
  assumes invars: "forest_invar M F" 
  and ret: "compute_alt_path_or_pedg F = PEDG \<D>"
  and init: "finite \<lbrace>F\<rbrace>" "\<lbrace>F\<rbrace> \<subseteq> G" "aevens F \<subseteq> Vs G"
  and unmatcheds_even: "Vs G - Vs M \<subseteq> aroots F" "Vs G - Vs M \<noteq> {}"
shows "\<nexists>p. matching_augmenting_path M p \<and> path G p \<and> distinct p" (is ?thesis1)
      "pre_edmonds_gallai G M \<D>" (is ?thesis2)
proof-
  have fun_dom: "compute_alt_path_dom F" 
    using compute_alt_path_dom init(1,2) invars by blast
  hence None:"compute_alt_path F = None"
    using ret by(auto simp add: compute_alt_path_or_pedg_same'[of F, symmetric])
  show ?thesis1
    by(intro compute_alt_path_from_tree_2 [OF assms(1) _ assms(3,4,6)] None)
  obtain F' where F': "\<not> if1_cond F'" "\<not> if2_cond F'" "forest_invar M F'" 
            "aroots F' = aroots F" "\<D> = {{v} |v. v \<in> aevens F'}" "aevens F' \<subseteq> Vs G" "\<lbrace> F' \<rbrace> \<subseteq> G"
    using what_if_search_fails_pedg[OF assms(2,3,4,1,5)] by auto
  have Vs_with_M_in_aevens:"Vs G - Vs M \<subseteq> aevens F'"
    using  F'(3,4) unmatcheds_even(1) roots(2)[of M F'] by auto
  have aroots_F': "aroots F' \<noteq> {}"
    using F'(4) unmatcheds_even(1,2) by force
  show ?thesis2           
    using termination_conditions_pedg[OF  F'(1,2,3) Vs_with_M_in_aevens F'(6,7) aroots_F'] F'(5)
    by simp
qed

definition "compute_pedg =
  (case compute_alt_path_or_pedg (empty_forest unmatcheds) of 
    PEDG \<D> \<Rightarrow> \<D>)"

lemma init_evens_in_G:"aevens (empty_forest unmatcheds) \<subseteq> Vs G"
  by (simp add: empty_forest(1) unmatcheds(2))

lemma initial_dom: "compute_alt_path_dom (empty_forest unmatcheds)"
  by (simp add: compute_alt_path_dom empty_forest(4) init_props(1))

lemma compute_pedg_correct:
  "\<lbrakk>compute_alt_path (empty_forest unmatcheds) = None; Vs G - Vs M \<noteq> {}\<rbrakk> \<Longrightarrow>
     pre_edmonds_gallai G M compute_pedg"
  by(rule compute_alt_path_or_pedg_from_tree_2(2)[OF 
            init_props(1) _ init_props(2,3)  init_evens_in_G init_props(4)])
    (auto simp add: compute_pedg_def compute_alt_path_or_pedg_same initial_dom 
             split: alt_search_res.split)

end

subsubsection \<open>Blossom Contraction and Reexpansion\<close>

locale find_aug_path_pedg =
find_aug_path where sel = sel
for sel::"'a set \<Rightarrow> 'a"+
fixes pedg_search::"'a set set \<Rightarrow> 'a set set \<Rightarrow> 'a set set"
and sel_from_sets::"('a set \<Rightarrow> bool) \<Rightarrow> 'a set set \<Rightarrow> 'a set"
assumes pedg_search_sound: 
 "\<lbrakk>graph_invar G; matching M; M \<subseteq> G; blos_search G M = None; Vs G - Vs M \<noteq> {}\<rbrakk>
     \<Longrightarrow> pre_edmonds_gallai G M (pedg_search G M)" 
assumes sel_from_sets:
  "\<And> \<D> P. \<lbrakk>finite \<D>; \<exists> D \<in> \<D>. P D\<rbrakk> \<Longrightarrow> sel_from_sets P \<D> \<in> \<D>"
  "\<And> \<D> P. \<lbrakk>finite \<D>; \<exists> D \<in> \<D>. P D\<rbrakk> \<Longrightarrow> P (sel_from_sets P \<D>)"
begin

function (domintros) find_pedg where
  "find_pedg G M = 
     (case blos_search G M of Some match_blossom_res \<Rightarrow>
        (case match_blossom_res of Blossom stem cyc \<Rightarrow>
            (let u = create_vert (Vs G);
                 s = Vs G - (set cyc);
                 quotG = quot.quotG s u
              in (if Vs (quotG G) = Vs (quotG M)
                 then {set cyc}
                 else 
                 (let \<D> = find_pedg (quotG G) (quotG M)
                 in if Delta G (set cyc) = {}
                    then insert  (set cyc) \<D>
                    else let D = sel_from_sets (\<lambda> D. u \<in> D) \<D>;
                             \<D>' = \<D> - {D} \<union> {D - {u} \<union>  (set cyc)}
                         in \<D>'))))
      | _ \<Rightarrow> pedg_search G M)"
  by pat_completeness auto

thm find_aug_path_dom
lemma find_pedg_dom:
  assumes  "matching M" "M \<subseteq> E" "graph_invar E" 
  shows "find_pedg_dom (E,M)"
  using assms
proof(induction "find_aug_path_meas E" arbitrary: E M rule: less_induct)
  case less
  have "find_pedg_dom
        (quot_graph (\<lambda>v. if v \<in> Vs E \<and> v \<notin> set cyc then v else create_vert (Vs E)) E -
         {{create_vert (Vs E)}},
         quot_graph (\<lambda>v. if v \<in> Vs E \<and> v \<notin> set cyc then v else create_vert (Vs E)) M -
         {{create_vert (Vs E)}})" 
    if "blos_search E M = Some (Blossom stem cyc)" for stem cyc
  proof- 
    note 1 = that
      let ?s = "(Vs E - (set cyc))"
      let ?u = "(create_vert (Vs E))"
      have "match_blossom M stem cyc"
        "path E (stem @ cyc)"
        using bloss_algo_sound(2) 1 less.prems(1,2,3) by auto
      then have "set cyc \<subseteq> Vs E"
        using path_suff subset_path_Vs by force
      then have "Vs E - ?s = set cyc"
        by auto
      moreover have "?s \<subseteq> Vs E"
        by auto
      moreover have "card (set cyc) \<ge> 2"
        using blossom_cycle_longer_2[OF \<open>match_blossom M stem cyc\<close>] .
      moreover have "finite (Vs E)"
        by (simp add: less.prems(3))
      ultimately have measure_less:"find_aug_path_meas (quot.quotG ?s ?u E) < find_aug_path_meas E"
        using 1 less.prems(3)           
        by(intro card_Vs_lt[of ?s E]) auto
      moreover have finite_quot:"finite (quot.quotG ?s ?u E)"
        by (simp add: \<open>finite (Vs E)\<close> quot_graph_finite')
      moreover have "((Vs E) - set cyc) \<subset> (Vs E)"
        using blossom_diff[OF \<open>graph_invar E\<close> \<open>match_blossom M stem cyc\<close> \<open>path E (stem@cyc)\<close>].  
      hence dblton_new: "dblton_graph (quot.quotG ?s ?u E)"
        using \<open>graph_invar E\<close> create_vert_works 
        by(intro doublton_quot[where E = E]) auto
      moreover have "matching (quot.quotG ?s ?u M)"
        using \<open>((Vs E) - set cyc) \<subset> (Vs E)\<close> \<open>graph_invar E\<close> \<open>match_blossom M stem cyc\<close> 
              less(2) less.prems(2)
        by (intro matching_quotM[where s = ?s and stem = stem and C=cyc and E=E]) auto
      moreover have "(quot.quotG ?s ?u M) \<subseteq> quot.quotG ?s ?u E"
        by (simp add: less.prems(2) Diff_mono graph_subset_quot_subset)
      moreover have "graph_invar (quot.quotG ?s ?u E)"
        using dblton_new finite_quot finite_dbl_finite_verts by auto
      ultimately show ?thesis
        using measure_less
        by(intro less(1)) auto
    qed
    thus ?case
      by(intro find_pedg.domintros) auto
  qed

context 
  fixes s::"'a set" and E::"'a set set"
  assumes quot_assms: "s \<subset> Vs E" "graph_invar E"
begin
interpretation quot: quot sel E s "(create_vert (Vs E))"
  using quot_assms create_vert_works 
  by unfold_locales auto

lemma card_Vs_lt:
  assumes "1 < card (Vs E - s)"
  shows "find_aug_path_meas (quot.quotG E) < find_aug_path_meas E"
  unfolding find_aug_path_meas_def
  using quot_assms assms
  by (intro quot.card_Vs_quotG) auto

lemmas matching_quotM=quot.matching_quotM

lemmas doublton_quot = quot.doubleton_quot

lemmas aug_path_works_in_contraction = quot.aug_path_works_in_contraction

lemmas finite_quot = quot.finite_quot

lemmas doubleton_quot = quot.doubleton_quot

lemmas refine = quot.refine

lemmas pre_emonds_gallai_lonely_blossom =quot.pre_emonds_gallai_lonely_blossom

lemmas graph_invar_quotG = quot.graph_invar_quotG

lemmas max_card_matching_equiv_blossom_contraction = 
     quot.max_card_matching_equiv_blossom_contraction

lemmas pre_emonds_gallai_perfect_after_contraction=
  quot.pre_emonds_gallai_perfect_after_contraction

lemmas pre_emonds_gallai_connected_blossom_obtain_D = 
  quot.pre_emonds_gallai_connected_blossom_obtain_D

lemmas pre_emonds_gallai_connected_blossom =
  quot.pre_emonds_gallai_connected_blossom
end

lemma find_pedg_correct:
  assumes  "graph_invar E" "max_card_matching E M" "Vs E - Vs M \<noteq> {}"
  shows "pre_edmonds_gallai E M (find_pedg E M)"
  using assms
proof(induction rule:  find_pedg.pinduct[OF find_pedg_dom, of M E], goal_cases)
  case 1
  then show ?case 
    using assms(2) max_card_matching_def by blast
next
  case 2
  then show ?case 
    by (simp add: assms(2) max_card_matchingDs(1))
next
  case 3
  then show ?case 
    by (simp add: assms(1))
next
  case (4 G M)
  note IH = this
  show ?case
    unfolding find_pedg.psimps[OF IH(1)]
  proof(cases "blos_search G M", goal_cases)
    case 1
    then show ?case
      using IH(4,5) max_card_matchingDs(2)
      by(auto intro!: pedg_search_sound simp add: IH(3) max_card_matching_subgraphD)
  next
    case (2 res)
    note two = this
    have matching_M: "matching M" and graph_matching_M: "graph_matching G M"
      using IH(4) max_card_matchingDs by auto
    have M_in_G: "M \<subseteq> G"
      by (simp add: IH(4) max_card_matchingDs(1))
    have no_p:"\<nexists> p. graph_augmenting_path G M p" 
      using IH(3) max_card_matchingD[OF IH(4)]  Berge[of M G] finite_Vs_then_finite[of G] 
            finite_subset[of M G]
      by auto
    obtain stem cyc where res_def: "res = Blossom stem cyc"
      using no_p bloss_algo_sound[OF IH(3) matching_M M_in_G] 2
      by(cases res) auto
    have a_blossom: "blossom G M stem cyc"
      by(intro bloss_algo_sound(2)[OF IH(3) matching_M M_in_G, of stem cyc])
        (simp add: "2" res_def)
    define u where "u = create_vert (Vs G)"
    define s where "s = Vs G - set cyc"
    define quotG where "quotG = (\<lambda>G. quot_graph (\<lambda>v. if v \<in> s then v else u) G - {{u}})"
have "set cyc \<subseteq> Vs G"
        using a_blossom path_suff[of G stem cyc] subset_path_Vs[of G cyc]
        by simp
    then have Vs_G_cyc:"Vs G - s = set cyc"
        by (auto simp add: s_def)
     moreover have "s \<subseteq> Vs G"
        by (auto simp add: s_def)
     moreover have "card (set cyc) \<ge> 2"
       using a_blossom blossom_cycle_longer_2 by blast
     ultimately have s_string_in_G:"s \<subset> Vs G" 
       by auto
     have quot_fold:
        "quot_graph (\<lambda>v. if v \<in> s then v else create_vert (Vs G)) GG - {{create_vert (Vs G)}} =
          quotG GG" for GG
       unfolding quotG_def u_def by simp
    show ?case
      unfolding 2 res_def option.case  match_blossom_res.case
    proof(cases "Vs (quotG G) = Vs (quotG M)", goal_cases)
      case 1
      then show ?case
        unfolding Let_def
      proof(subst (3) if_P, goal_cases)
        case 1
        then show ?case 
          unfolding quotG_def s_def u_def
          by simp
      next
        case 2
        thus ?case
          by(intro pre_emonds_gallai_perfect_after_contraction[OF 
                    s_string_in_G IH(3) s_def a_blossom graph_matching_M])
            (simp add: quot_fold)
      qed
    next
      case 2
      note not_perfect = this
      
    define \<D> where  "\<D> = find_pedg (quotG G) (quotG M)"

    define u' where "u' = create_vert (insert u (Vs G))"
    have u'_props: "create_vert (Vs G) \<notin> Vs G" "u' \<notin> Vs G" "u' \<noteq> create_vert (Vs G)"
      using IH(3) create_vert_works 
      by(auto simp add: u'_def u_def)
    have max_card_matching_quot: "max_card_matching (quotG G) (quotG M)"
      using max_card_matching_equiv_blossom_contraction[OF s_string_in_G IH(3) a_blossom
                graph_matching_M s_def u'_props(1), simplified quot_fold] IH(4)
      by simp
    hence Vs_quot_M_in_quot_Vs: "Vs (quotG G) \<supseteq> Vs (quotG M)"
      by (simp add: Vs_subset max_card_matchingDs(1))
     have IH_applied: "pre_edmonds_gallai (quotG G) (quotG M) \<D>"
       unfolding \<D>_def
     proof(rule IH(2)[OF two res_def u_def s_def], goal_cases)
       case 1
       then show ?case 
         using graph_invar_quotG IH(3) quotG_def s_string_in_G u_def 
         by presburger
     next
       case 4
       then show ?case 
         using IH(4)
         using max_card_matching_equiv_blossom_contraction[OF s_string_in_G IH(3) a_blossom
                 graph_matching_M s_def, simplified quot_fold]
         by (simp add: u'_props(1))
     next
       case 2
       then show ?case
         using  not_perfect by simp
     next
       case 3
       thus ?case
         using IH(3) graph_invar_quotG quotG_def s_string_in_G u_def by presburger
     next
       case 5
       thus ?case 
         using Vs_quot_M_in_quot_Vs not_perfect by blast
     qed 
     have grapn_invar_quot: "graph_invar (quotG G)"
       using IH(3) graph_invar_quotG quotG_def s_string_in_G u_def by presburger
    show ?case 
    proof(cases "Delta G (set cyc) = {}", goal_cases)
      case 1
      have "pre_edmonds_gallai G M (insert (set cyc) \<D>)"
        using IH_applied IH(4) u'_props 
        by (intro pre_emonds_gallai_lonely_blossom[OF s_string_in_G IH(3) _ 1 _ a_blossom],
            unfold  quot_fold)
            (auto simp add: s_def)
      thus ?case
        unfolding Let_def quot_fold[simplified s_def]
        by (simp add: "1" \<D>_def not_perfect)
    next
      case 2
      define D where "D = sel_from_sets ((\<in>) u) \<D>" 

      note obtainD1 =
           pre_emonds_gallai_connected_blossom_obtain_D[OF s_string_in_G IH(3) _ 2 _ a_blossom,
              simplified quot_fold[simplified s_def]]
      note obtainD2 =obtainD1[OF IH_applied s_def IH(4) u'_props]
      moreover have finite_\<D>: "finite \<D>" 
        using IH_applied
        by(auto dest!: pre_edmonds_gallaiD(2)
             simp add: finite_UnionD finite_subset grapn_invar_quot)
      ultimately have D_props: "D \<in> \<D>" "create_vert (Vs G) \<in> D"
        using sel_from_sets[of \<D> "(\<in>) u"]
        by(auto simp add: D_def u_def)
      note new_pedg1 =
           pre_emonds_gallai_connected_blossom[OF s_string_in_G IH(3) _ 2 _ a_blossom,
              simplified quot_fold[simplified s_def]]
      note new_pedg2 = new_pedg1[OF IH_applied s_def IH(4) u'_props D_props, folded u_def]
      thus ?case
        unfolding Let_def quot_fold[simplified s_def]
        by (simp add: "2" D_def \<D>_def not_perfect u_def)
    qed
  qed
qed
qed

end
end