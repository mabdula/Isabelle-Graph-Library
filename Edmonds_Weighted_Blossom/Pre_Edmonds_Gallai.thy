theory Pre_Edmonds_Gallai
  imports Blossom_Executable.Compute_Alt_Path Blossom_Executable.Find_Aug_Path
    Edmonds_Gallai_Decomposition.Edmonds_Gallai_Blossoms
begin

provenance human

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

datatype ('v, 'vset) alt_search_res = Two_Paths "'v list" "'v list" | PEDG 'vset

context compute_alt_path
begin

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

end

context Compute_Alt_Path
begin

function (domintros) compute_alt_path_or_pedg ::
  "('v, 'forest) Compute_Alt_Path_state \<Rightarrow> ('v, 'fset) alt_search_res" where
  "compute_alt_path_or_pedg state =
    (case unscanned state of
       (v, w) # rest \<Rightarrow>
         (if fset_isin (evens (search_forest state)) w then
            Two_Paths (get_path (search_forest state) v) (get_path (search_forest state) w)
          else if fset_isin (odds (search_forest state)) w then
            compute_alt_path_or_pedg (state \<lparr>unscanned := rest\<rparr>)
          else case mate_lookup M w of
             Some x \<Rightarrow> compute_alt_path_or_pedg
               (state \<lparr>queue := x # queue state, unscanned := rest,
                 search_forest := extend_forest_even_unclassified (search_forest state) v w x\<rparr>)
           | None \<Rightarrow> compute_alt_path_or_pedg (state \<lparr>unscanned := rest\<rparr>))
     | [] \<Rightarrow>
         (case queue state of
            v # q \<Rightarrow> compute_alt_path_or_pedg
              (state \<lparr>queue := q, unscanned := map (Pair v) (neighbour_list G v)\<rparr>)
          | [] \<Rightarrow> PEDG (evens (search_forest state))))"
  by pat_completeness auto

lemma compute_alt_path_or_pedg_same_dom:
  "compute_alt_path_or_pedg_dom state \<longleftrightarrow> Compute_Alt_Path_dom state"
proof
  assume "compute_alt_path_or_pedg_dom state"
  thus "Compute_Alt_Path_dom state"
    by (induction rule: compute_alt_path_or_pedg.pinduct)
       (auto intro: Compute_Alt_Path.domintros)
next
  assume "Compute_Alt_Path_dom state"
  thus "compute_alt_path_or_pedg_dom state"
    by (induction rule: Compute_Alt_Path.pinduct)
       (auto intro: compute_alt_path_or_pedg.domintros)
qed

lemmas compute_alt_path_or_pedg_psimps' =
  compute_alt_path_or_pedg.psimps[simplified compute_alt_path_or_pedg_same_dom]

lemma compute_alt_path_or_pedg_result:
  "Compute_Alt_Path_dom state \<Longrightarrow>
    compute_alt_path_or_pedg state =
      (case alternating_paths (Compute_Alt_Path state) of
         Some (p1, p2) \<Rightarrow> Two_Paths p1 p2
       | None \<Rightarrow> PEDG (evens (search_forest (Compute_Alt_Path state))))"
proof(induction rule: Compute_Alt_Path.pinduct)
  case (1 state)
  show ?case
  proof(cases "unscanned state")
    case Nil
    thus ?thesis
      using 1(2-)
      by (cases "queue state")
         (simp_all add: compute_alt_path_or_pedg_psimps'[OF 1(1)]
           Compute_Alt_Path.psimps[OF 1(1)] alternating_paths_def cong: option.case_cong)
  next
    case (Cons e rest)
    obtain v w where "e = (v, w)"
      by (cases e)
    with Cons show ?thesis
      using 1(2-)
      by (cases "fset_isin (evens (search_forest state)) w";
          cases "fset_isin (odds (search_forest state)) w"; cases "mate_lookup M w")
         (simp_all add: compute_alt_path_or_pedg_psimps'[OF 1(1)]
           Compute_Alt_Path.psimps[OF 1(1)] alternating_paths_def cong: option.case_cong)
  qed
qed

lemma compute_alt_path_or_pedg_same:
  "Compute_Alt_Path_dom state \<Longrightarrow>
    compute_alt_path_or_pedg state = Two_Paths p1 p2 \<longleftrightarrow>
    alternating_paths (Compute_Alt_Path state) = Some (p1, p2)"
  by (auto simp: compute_alt_path_or_pedg_result split: option.splits prod.splits)

lemma compute_alt_path_or_pedg_same':
  "Compute_Alt_Path_dom state \<Longrightarrow>
    (\<exists>D. compute_alt_path_or_pedg state = PEDG D) \<longleftrightarrow>
    alternating_paths (Compute_Alt_Path state) = None"
  by (auto simp: compute_alt_path_or_pedg_result split: option.splits prod.splits)

definition "compute_pedg =
  (case compute_alt_path_or_pedg initial_state of PEDG D \<Rightarrow> D)"

context
  assumes Compute_Alt_Path_axiom: Compute_Alt_Path_axiom
begin

interpretation abs_search: compute_alt_path
  where G = "ugraph_abs G" and M = "matching_abs M"
    and vset_invar = fset_invar and vset_to_set = fset_to_set
    and evens = evens and odds = odds and roots = roots
    and get_path = get_path and abstract_forest = abstract_forest
    and forest_invar = forest_invar
    and extend_forest_even_unclassified = extend_forest_even_unclassified
    and empty_forest = empty_forest and forest_univ = K and vset_empty = fset_empty
proof(rule compute_alt_path.intro)
  show "match (ugraph_abs G) (matching_abs M)"
    by unfold_locales
       (use ugraph_abs_graph_invar[OF graph_input_G[OF Compute_Alt_Path_axiom]]
         matching_invar_props[OF matching_invar_M[OF Compute_Alt_Path_axiom]] in auto)
  show "alternating_forest_ordinary_extension_spec fset_invar fset_to_set evens odds get_path
    abstract_forest forest_invar roots extend_forest_even_unclassified empty_forest K fset_empty"
    by (rule Forest.alternating_forest_ordinary_extension_spec_axioms)
qed

lemma termination_conditions_pedg:
  assumes "Compute_Alt_Path_ret_2_conds state" "invar_forest state" "invar_scanned state"
    "Vs (ugraph_abs G) - Vs (matching_abs M) \<noteq> {}"
  shows "pre_edmonds_gallai (ugraph_abs G) (matching_abs M)
    {{v} |v. v \<in> aevens state}"
proof-
  have closed: "\<And>v w. \<lbrakk>v \<in> aevens state; {v, w} \<in> ugraph_abs G\<rbrakk>
    \<Longrightarrow> w \<in> aodds state"
    using assms(1,3)
    by (auto simp: Compute_Alt_Path_ret_2_conds_def invar_scanned_def)
  have "\<not> abs_search.if1_cond (search_forest state)"
    using closed Forest.evens_and_odds_basis(4)[OF invar_forestD(1)[OF assms(2)]]
    by (auto simp: abs_search.if1_cond_def)
  moreover have "\<not> abs_search.if2_cond (search_forest state)"
    using closed Forest.evens_and_odds(4)[OF invar_forestD(1)[OF assms(2)]]
    by (auto simp: abs_search.if2_cond_def)
  moreover have "Vs (ugraph_abs G) - Vs (matching_abs M) \<subseteq> aevens state"
    using invar_forestD(3)[OF assms(2)] Forest.roots(2)[OF invar_forestD(1)[OF assms(2)]]
    by blast
  ultimately show ?thesis
    using abs_search.termination_conditions_pedg[of "search_forest state"]
      invar_forestD[OF assms(2)] aevens_subset_Vs[OF assms(2)] assms(4)
    by (auto simp: Union_of_singletons_in_set)
qed

lemma compute_alt_path_or_pedg_from_tree_2:
  assumes "invar_forest state" "invar_unscanned state" "invar_queue state" "invar_scanned state"
    "compute_alt_path_or_pedg state = PEDG D"
    "Vs (ugraph_abs G) - Vs (matching_abs M) \<noteq> {}"
  shows "\<not> graph_augmenting_path (ugraph_abs G) (matching_abs M) p"
    "pre_edmonds_gallai (ugraph_abs G) (matching_abs M)
      {{v} |v. v \<in> fset_to_set D}"
    "fset_invar D" "fset_to_set D \<subseteq> Vs (ugraph_abs G)"
proof-
  have dom: "Compute_Alt_Path_dom state"
    by (rule Compute_Alt_Path_terminates[OF Compute_Alt_Path_axiom assms(1-4)])
  have final: "invar_forest (Compute_Alt_Path state)" "invar_scanned (Compute_Alt_Path state)"
    using invars_holds[OF Compute_Alt_Path_axiom dom assms(1-4)] by auto
  have result: "alternating_paths (Compute_Alt_Path state) = None"
    "D = evens (search_forest (Compute_Alt_Path state))"
    using assms(5) compute_alt_path_or_pedg_result[OF dom]
    by (auto split: option.splits prod.splits)
  have ret: "Compute_Alt_Path_ret_2_conds (Compute_Alt_Path state)"
    using ret_holds[OF dom] result(1)
    by (auto simp: Compute_Alt_Path_ret_1_conds_def alternating_paths_def)
  show "\<not> graph_augmenting_path (ugraph_abs G) (matching_abs M) p"
    by (rule Compute_Alt_Path_correct_ret_2[OF Compute_Alt_Path_axiom ret final])
  show "pre_edmonds_gallai (ugraph_abs G) (matching_abs M)
      {{v} |v. v \<in> fset_to_set D}"
    using termination_conditions_pedg[OF ret final assms(6)] by (simp add: result(2))
  show "fset_invar D" "fset_to_set D \<subseteq> Vs (ugraph_abs G)"
    using forest_sets_invar(1)[OF final(1)] aevens_subset_Vs[OF final(1)]
    by (simp_all add: result(2))
qed

lemma compute_pedg_correct:
  assumes "alternating_paths (Compute_Alt_Path initial_state) = None"
    "Vs (ugraph_abs G) - Vs (matching_abs M) \<noteq> {}"
  shows "fset_invar compute_pedg" "fset_to_set compute_pedg \<subseteq> Vs (ugraph_abs G)"
    "pre_edmonds_gallai (ugraph_abs G) (matching_abs M)
      {{v} |v. v \<in> fset_to_set compute_pedg}"
proof-
  have "free_vertices \<noteq> []"
    using set_free_vertices[OF Compute_Alt_Path_axiom] assms(2) by auto
  moreover obtain D where "compute_alt_path_or_pedg initial_state = PEDG D"
    using compute_alt_path_or_pedg_same'[OF initial_state_dom[OF Compute_Alt_Path_axiom]] assms(1)
    by auto
  ultimately show "fset_invar compute_pedg" "fset_to_set compute_pedg \<subseteq> Vs (ugraph_abs G)"
    "pre_edmonds_gallai (ugraph_abs G) (matching_abs M)
      {{v} |v. v \<in> fset_to_set compute_pedg}"
    using compute_alt_path_or_pedg_from_tree_2(2-4)[
      OF initial_state_props[OF Compute_Alt_Path_axiom] _ assms(2)]
    by (auto simp: compute_pedg_def)
qed

end
end

subsubsection \<open>Blossom Contraction and Reexpansion\<close>

locale find_aug_path_pedg =
  Find_Aug_Path where lookup = lookup and mate_empty = mate_empty +
  Fset: fixed_univ_set K fset_invar fset_to_set fset_empty fset_insert fset_delete fset_isin
  for lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option" and mate_empty :: 'mate
    and fset_invar :: "'fset \<Rightarrow> bool" and fset_to_set :: "'fset \<Rightarrow> 'v set"
    and fset_empty :: 'fset and fset_insert :: "'v \<Rightarrow> 'fset \<Rightarrow> 'fset"
    and fset_delete :: "'v \<Rightarrow> 'fset \<Rightarrow> 'fset"
    and fset_isin :: "'fset \<Rightarrow> 'v \<Rightarrow> bool" +
  fixes pedg_search :: "'adjmap \<Rightarrow> 'v list \<Rightarrow> 'mate \<Rightarrow> 'fset"
  assumes create_vert_fresh: "\<And>vs'. create_vert vs' \<notin> set vs'"
  and create_vert_univ: "\<And>vs'. set vs' \<subseteq> K \<Longrightarrow> create_vert vs' \<in> K"
  and pedg_search_sound:
    "\<And>E vs' N. \<lbrakk>graph_input E vs'; matching_invar E N; blos_search E vs' N = None;
      Vs (ugraph_abs E) - Vs (matching_abs N) \<noteq> {}\<rbrakk>
      \<Longrightarrow> pre_edmonds_gallai (ugraph_abs E) (matching_abs N)
        {{v} |v. v \<in> fset_to_set (pedg_search E vs' N)}"
  and pedg_search_invar:
    "\<And>E vs' N. \<lbrakk>graph_input E vs'; matching_invar E N; blos_search E vs' N = None;
      Vs (ugraph_abs E) - Vs (matching_abs N) \<noteq> {}\<rbrakk>
      \<Longrightarrow> fset_invar (pedg_search E vs' N)"
begin

definition "pedg_singletons vs' D =
  List.map_filter (\<lambda>v. if fset_isin D v then Some (fset_insert v fset_empty) else None) vs'"

definition "pedg_insert_list C D = foldl (\<lambda>D v. fset_insert v D) D C"

definition "pedg_expand C u Ds =
  map (\<lambda>D. if fset_isin D u then pedg_insert_list C (fset_delete u D) else D) Ds"

definition "pedg_isolated E C S =
  list_all (\<lambda>v. list_all (fset_isin S) (neighbour_list E v)) C"

lemma pedg_singletons_props:
  assumes "fset_invar D" "fset_to_set D \<subseteq> set vs'" "set vs' \<subseteq> K"
  shows "list_all fset_invar (pedg_singletons vs' D)"
    "fset_to_set ` set (pedg_singletons vs' D) = {{v} |v. v \<in> fset_to_set D}"
  using assms
  by (auto intro!: image_eqI simp: pedg_singletons_def List.map_filter_map_filter[symmetric]
      list_all_iff image_image Fset.fixed_univ_set_isin
      Fset.fixed_univ_set_insert Fset.fixed_univ_set_empty)

lemma pedg_insert_list_props:
  assumes "fset_invar D" "set C \<subseteq> K"
  shows "fset_invar (pedg_insert_list C D) \<and>
    fset_to_set (pedg_insert_list C D) = fset_to_set D \<union> set C"
  using assms unfolding pedg_insert_list_def
  by (induction C arbitrary: D) (auto simp: Fset.fixed_univ_set_insert)

lemma pedg_isolated_iff:
  "\<lbrakk>graph_input E vs'; fset_invar S; fset_to_set S = set C\<rbrakk> \<Longrightarrow>
    pedg_isolated E C S \<longleftrightarrow> Delta (ugraph_abs E) (set C) = {}"
  by (auto simp: pedg_isolated_def list_all_iff Fset.fixed_univ_set_isin
      neighbour_list_ugraph_abs Delta_def)

lemma pedg_expand_invar:
  "\<lbrakk>list_all fset_invar Ds; set C \<subseteq> K\<rbrakk>
    \<Longrightarrow> list_all fset_invar (pedg_expand C u Ds)"
  by (auto simp: pedg_expand_def list_all_iff
      pedg_insert_list_props Fset.fixed_univ_set_delete split: if_splits)

lemma pedg_expand_abs:
  assumes "list_all fset_invar Ds" "set C \<subseteq> K"
    "disjoint (fset_to_set ` set Ds)" "D \<in> fset_to_set ` set Ds" "u \<in> D"
  shows "fset_to_set ` set (pedg_expand C u Ds) =
    (fset_to_set ` set Ds) - {D} \<union> {D - {u} \<union> set C}"
proof-
  have only: "u \<in> fset_to_set S \<longleftrightarrow> fset_to_set S = D"
    if "S \<in> set Ds" for S
    using assms(3-5) that by (auto simp: disjoint_def)
  have update: "fset_to_set (if fset_isin S u then pedg_insert_list C (fset_delete u S) else S) =
    (if fset_to_set S = D then D - {u} \<union> set C else fset_to_set S)"
    if "S \<in> set Ds" for S
    using assms(1,2) that only[OF that]
    by (auto simp: list_all_iff Fset.fixed_univ_set_isin
        pedg_insert_list_props Fset.fixed_univ_set_delete)
  have "fset_to_set ` set (pedg_expand C u Ds) =
    (\<lambda>S. if S = D then D - {u} \<union> set C else S) ` (fset_to_set ` set Ds)"
    unfolding pedg_expand_def set_map image_image
    by (rule image_cong[OF refl]) (rule update)
  also have "... = (fset_to_set ` set Ds) - {D} \<union> {D - {u} \<union> set C}"
    using assms(4) by (auto simp: image_iff split: if_splits)
  finally show ?thesis .
qed

text \<open>The vertex list can contain isolated vertices, including an isolated contracted
  blossom. Only vertices incident to an edge must have a matching partner.\<close>

definition "pedg_perfect E vs' N =
  list_all (\<lambda>v. neighbour_list E v = [] \<or> mate_lookup N v \<noteq> None) vs'"

lemma pedg_perfect_iff:
  assumes "graph_input E vs'" "matching_invar E N"
  shows "pedg_perfect E vs' N \<longleftrightarrow> Vs (ugraph_abs E) = Vs (matching_abs N)"
proof-
  have "neighbour_list E v = [] \<longleftrightarrow> v \<notin> Vs (ugraph_abs E)" for v
    using neighbour_list_nonempty_iff[OF assms(1), of v] by auto
  moreover have "mate_lookup N v = None \<longleftrightarrow> v \<notin> Vs (matching_abs N)" for v
    using Vs_matching_abs_iff[OF assms, of v] by auto
  ultimately show ?thesis
    using Vs_ugraph_abs_subset_vs[OF assms(1)] Vs_subset[OF matching_invar_props(3)[OF assms(2)]]
    by (auto simp: pedg_perfect_def list_all_iff)
qed

function (domintros) find_pedg where
  "find_pedg E vs' N =
    (case blos_search E vs' N of
       Some (Blossom stem C) \<Rightarrow>
         (let u = create_vert vs';
              E' = contract_graph E vs' C u;
              vs'' = contract_vertices vs' C u;
              N' = contract_matching N C u;
              S = pedg_insert_list C fset_empty
          in if pedg_perfect E' vs'' N' then [S]
             else let Ds = find_pedg E' vs'' N'
                  in if pedg_isolated E C S then S # Ds else pedg_expand C u Ds)
     | _ \<Rightarrow> pedg_singletons vs' (pedg_search E vs' N))"
  by pat_completeness auto

lemma find_pedg_dom:
  assumes "graph_input E vs'" "matching_invar E N"
  shows "find_pedg_dom (E, vs', N)"
  using assms
proof(induction "card (Vs (ugraph_abs E))" arbitrary: E vs' N rule: less_induct)
  case less
  have step: "find_pedg_dom (contract_graph E vs' C (create_vert vs'),
    contract_vertices vs' C (create_vert vs'), contract_matching N C (create_vert vs'))"
    if "blos_search E vs' N = Some (Blossom stem C)" for stem C
  proof-
    have contract: "graph_input E vs'" "matching_invar E N"
      "blossom (ugraph_abs E) (matching_abs N) stem C"
      "create_vert vs' \<notin> set vs' - set C" "create_vert vs' \<in> K"
      using less.prems blos_search(2)[OF less.prems that] create_vert_fresh create_vert_univ
      by (auto dest: graph_inputD(7))
    show ?thesis
      by (rule less.hyps[OF contract_card_Vs[OF contract]
            contract_graph_input[OF contract] contract_matching_invar[OF contract]])
  qed
  show ?case
    by (rule find_pedg.domintros) (auto intro: step)
qed

lemma find_pedg_correct:
  assumes "graph_input E vs'" "matching_invar E N"
    "max_card_matching (ugraph_abs E) (matching_abs N)"
    "Vs (ugraph_abs E) - Vs (matching_abs N) \<noteq> {}"
  shows "list_all fset_invar (find_pedg E vs' N)"
    "pre_edmonds_gallai (ugraph_abs E) (matching_abs N)
      (fset_to_set ` set (find_pedg E vs' N))"
proof-
  have "list_all fset_invar (find_pedg E vs' N) \<and>
    pre_edmonds_gallai (ugraph_abs E) (matching_abs N)
      (fset_to_set ` set (find_pedg E vs' N))"
    using assms
  proof(induction "card (Vs (ugraph_abs E))" arbitrary: E vs' N rule: less_induct)
    case less
    note dom = find_pedg_dom[OF less.prems(1,2)]
    show ?case
    proof(cases "blos_search E vs' N")
      case None
      have "fset_to_set (pedg_search E vs' N) \<subseteq> set vs'"
        using pre_edmonds_gallaiD(2)[OF pedg_search_sound[OF less.prems(1,2) None less.prems(4)]]
          Vs_ugraph_abs_subset_vs[OF less.prems(1)]
        by (auto simp: Union_of_singletons_in_set)
      from pedg_singletons_props[OF pedg_search_invar[OF less.prems(1,2) None less.prems(4)]
          this graph_inputD(7)[OF less.prems(1)]]
      show ?thesis
        using pedg_search_sound[OF less.prems(1,2) None less.prems(4)]
        by (simp add: find_pedg.psimps[OF dom] None)
    next
      case (Some r)
      have "\<not> graph_augmenting_path (ugraph_abs E) (matching_abs N) p" for p
        using Berge[OF matching_invar_props(4)[OF less.prems(2,1)]
          matching_invar_props(2,3)[OF less.prems(2)]
          conjunct1[OF ugraph_abs_graph_invar[OF less.prems(1)]]
          conjunct2[OF ugraph_abs_graph_invar[OF less.prems(1)]]]
          max_card_matchingD[OF less.prems(3)]
        by auto
      then obtain stem C where result: "blos_search E vs' N = Some (Blossom stem C)"
        using Some blos_search(1)[OF less.prems(1,2)]
        by (cases r) blast+
      let ?u = "create_vert vs'"
      have contract: "graph_input E vs'" "matching_invar E N"
        "blossom (ugraph_abs E) (matching_abs N) stem C" "?u \<notin> set vs' - set C" "?u \<in> K"
        using less.prems(1,2) blos_search(2)[OF less.prems(1,2) result]
          create_vert_fresh create_vert_univ[OF graph_inputD(7)[OF less.prems(1)]]
        by auto
      interpret Q: quot "ugraph_abs E" "Vs (ugraph_abs E) - set C" ?u
        by (rule quot_here[OF contract])
      note abs = contract_graph_abs[OF contract] contract_matching_abs[OF contract]
      have fresh: "?u \<notin> Vs (ugraph_abs E)"
        "create_vert (?u # vs') \<notin> Vs (ugraph_abs E)" "create_vert (?u # vs') \<noteq> ?u"
        using create_vert_fresh[of vs'] create_vert_fresh[of "?u # vs'"]
          Vs_ugraph_abs_subset_vs[OF less.prems(1)] by auto
      let ?E = "contract_graph E vs' C ?u"
      let ?vs = "contract_vertices vs' C ?u"
      let ?N = "contract_matching N C ?u"
      let ?Ds = "find_pedg ?E ?vs ?N"
      note input = contract_graph_input[OF contract] contract_matching_invar[OF contract]
      have matching: "graph_matching (ugraph_abs E) (matching_abs N)"
        using matching_invar_props(2,3)[OF less.prems(2)] by auto
      have C: "set C \<subseteq> K"
        using contraction_facts(2)[OF contract] Vs_ugraph_abs_subset_vs[OF less.prems(1)]
          graph_inputD(7)[OF less.prems(1)] by auto
      have cycle: "fset_invar (pedg_insert_list C fset_empty)"
        "fset_to_set (pedg_insert_list C fset_empty) = set C"
        using pedg_insert_list_props[OF Fset.fixed_univ_set_empty(1) C]
        by (auto simp: Fset.fixed_univ_set_empty(2))
      show ?thesis
      proof(cases "pedg_perfect ?E ?vs ?N")
        case True
        have "Vs (Q.quotG (matching_abs N)) = Vs (Q.quotG (ugraph_abs E))"
          using True pedg_perfect_iff[OF input] by (simp add: abs)
        from Q.pre_emonds_gallai_perfect_after_contraction[OF refl contract(3) matching this]
        show ?thesis
          using cycle by (simp add: find_pedg.psimps[OF dom] result Let_def True)
      next
        case False
        have nonperfect: "Vs (ugraph_abs ?E) - Vs (matching_abs ?N) \<noteq> {}"
          using False pedg_perfect_iff[OF input]
            Vs_subset[OF matching_invar_props(3)[OF input(2)]] by blast
        have max: "max_card_matching (ugraph_abs ?E) (matching_abs ?N)"
          using Q.max_card_matching_equiv_blossom_contraction[
            OF contract(3) matching refl fresh(1)] less.prems(3)
          by (simp add: abs)
        have IH: "list_all fset_invar ?Ds"
          "pre_edmonds_gallai (Q.quotG (ugraph_abs E)) (Q.quotG (matching_abs N))
            (fset_to_set ` set ?Ds)"
          using less.hyps[OF contract_card_Vs[OF contract] input max nonperfect]
          by (auto simp: abs)
        show ?thesis
        proof(cases "pedg_isolated E C (pedg_insert_list C fset_empty)")
          case True
          have "Delta (ugraph_abs E) (set C) = {}"
            using True pedg_isolated_iff[OF less.prems(1) cycle] by simp
          from Q.pre_emonds_gallai_lonely_blossom[
              OF IH(2) this refl contract(3) less.prems(3) fresh]
          show ?thesis
            using IH(1) cycle
            by (simp add: find_pedg.psimps[OF dom] result Let_def False True)
        next
          case connected: False
          have "Delta (ugraph_abs E) (set C) \<noteq> {}"
            using connected pedg_isolated_iff[OF less.prems(1) cycle] by simp
          then obtain D where D: "D \<in> fset_to_set ` set ?Ds" "?u \<in> D"
            by (rule Q.pre_emonds_gallai_connected_blossom_obtain_D[
                  OF IH(2) _ refl contract(3) less.prems(3) fresh])
          have "pre_edmonds_gallai (ugraph_abs E) (matching_abs N)
            ((fset_to_set ` set ?Ds) - {D} \<union> {D - {?u} \<union> set C})"
            by (rule Q.pre_emonds_gallai_connected_blossom[
                  OF IH(2) \<open>Delta (ugraph_abs E) (set C) \<noteq> {}\<close> refl contract(3) less.prems(3) fresh D])
          with pedg_expand_invar[OF IH(1) C]
            pedg_expand_abs[OF IH(1) C pre_edmonds_gallaiD(1)[OF IH(2)] D]
          show ?thesis
            by (simp add: find_pedg.psimps[OF dom] result Let_def False connected)
        qed
      qed
    qed
  qed
  thus "list_all fset_invar (find_pedg E vs' N)"
    "pre_edmonds_gallai (ugraph_abs E) (matching_abs N)
      (fset_to_set ` set (find_pedg E vs' N))"
    by auto
qed

end
end
