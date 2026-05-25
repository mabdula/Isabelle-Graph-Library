theory Arborescense
  imports Spanning_Trees Undirected_Set_Graphs.Undirected_Set_Graphs Greedoids.Greedoids
          Directed_Set_Graphs.More_Lists 
begin

section \<open>Arborescences\<close>

text \<open>Arborescences are trees around a certain vertex, the so-called root. 
For a fixed root, the arborescences form a greedoid, which satisfies the strong exchange property.\<close>

context graph_abs
begin

definition "arborescence r T = (has_no_cycle T \<and> (T \<noteq> {} \<longrightarrow> Vs T = connected_component T r))"

lemma arborescenceI:
 "\<lbrakk>has_no_cycle T; T \<noteq> {} \<Longrightarrow> Vs T = connected_component T r\<rbrakk> \<Longrightarrow> arborescence r T"
and arborescenceE:
 "\<lbrakk> arborescence r T; \<lbrakk>has_no_cycle T; T \<noteq> {} \<Longrightarrow> Vs T = connected_component T r\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
and arborescenceD:
 "arborescence r T \<Longrightarrow> has_no_cycle T"
 "\<lbrakk>arborescence r T; T \<noteq> {}\<rbrakk> \<Longrightarrow> Vs T = connected_component T r"
  by(auto simp add: arborescence_def)

lemma contains_empty: "arborescence r {}"
  using has_no_cycle_indep_ex has_no_cycle_indep_subset 
  by (fastforce simp add: arborescence_def)

lemma extension_property_one: 
  assumes "arborescence r S"
    "arborescence r T" "card T > card S" 
  shows "\<exists>x\<in>T - S. arborescence r (S \<union> {x})"
proof-
  have arborescense_unfold: "has_no_cycle T" "(T \<noteq> {} \<Longrightarrow> Vs T = connected_component T r)"
    "T \<subseteq> G"
    "has_no_cycle S" "(S \<noteq> {} \<Longrightarrow> Vs S = connected_component S r)"
    "S \<subseteq> G"
    using assms(1,2) by(auto simp add: has_no_cycle_def arborescence_def)
  show ?thesis
  proof(cases "S = {}")
    case True
    moreover hence "T \<noteq> {}"
      using assms(3) by force
    moreover then obtain e where e_prop:"r \<in> e" "e \<in> T" 
      using assms(2)  in_own_connected_component[of r T]
      by(auto elim:  vs_member_elim[of r T] simp add: arborescence_def)
    moreover have no_cyc:"has_no_cycle {e}" 
      using  calculation(4) indep_system.indep_subset[OF graph_indep_system arborescense_unfold(1)]  by blast
    moreover have e_good: " \<exists>u v. {u, v} = e \<and> u \<noteq> v"
      using arborescense_unfold(3) e_prop(2) by blast
    moreover hence  "Vs (S \<union> {e}) = connected_component (S \<union> {e}) r"
      using e_prop True by(simp add: connected_component_one_edge)
    ultimately have "e \<in> T -S" "arborescence r (S \<union> {e})"
      using True by(auto simp add: arborescence_def)
    thus ?thesis by auto
  next
    case False
    obtain e where e_prop: "e \<in> T - S" "has_no_cycle (insert e S)"
      using arborescense_unfold(1) arborescense_unfold(4) assms(3) 
        matroid.augment[OF graph_matroid] by blast
    then obtain x y where x_y_in_e:"x \<in> e" "y \<in> e" "x \<noteq> y" "e = {x,y}"
      using arborescense_unfold(3) by(auto dest: subset_edges_G)
    have xy_walk: "walk_betw (insert e S) x [x,y] y"
      by (simp add: edges_are_walks x_y_in_e(4))
    have "x \<in> Vs S \<Longrightarrow> y \<in> Vs S \<Longrightarrow> False"
      using False arborescense_unfold(5) connected_components_member_eq[of x S] e_prop(1) e_prop(2)
        has_no_cycle_ex_unique_path[of x y S] has_no_cycle_indep_subset_carrier[of "insert e S"]
        in_con_comp_has_walk[of y S x] x_y_in_e(3,4)
      by force
    then obtain x' y' where e_split':"e ={x', y'}" "x' \<noteq> y'" "x' \<notin> Vs S"
      using x_y_in_e(3) x_y_in_e(4) by blast
    have "x' \<in> connected_component T r"
      using arborescense_unfold(2) e_prop(1) e_split'(1) empty_Diff by blast 
    moreover have r_not_x:"r \<noteq> x'"
      using False arborescense_unfold(5) e_split'(3) in_own_connected_component by fastforce
    ultimately obtain p where p_walk:"walk_betw T r p x'"
      by (auto intro: in_con_comp_has_walk)
    hence hd_last_p:"hd p = r" "last p = x'" "p \<noteq> []"
      by (auto simp add: walk_between_nonempty_pathD)
    moreover have r_in_S:"r \<in> Vs S"
      by (simp add: False arborescense_unfold(5) in_own_connected_component)
    ultimately obtain ys zs z where ys_zs_z:"p = ys @ z # zs" "z \<notin> Vs S" "(\<forall>y\<in>set ys. \<not> y \<notin> Vs S)"
      using  iffD1[OF split_list_first_prop_iff[of p "\<lambda> x. x \<notin> Vs S"]]  e_split'(3)
      by fastforce
    hence "r \<in> set ys" 
      using  hd_in_set[OF hd_last_p(3)] hd_last_p(1)  r_in_S 
      by (auto simp add:  hd_append)
    hence ys_non_empty: "ys \<noteq> []" by auto
    hence "p = (butlast ys)@[last ys, z]@zs"
      using  append_butlast_last_id[of ys] by(fastforce simp add: ys_zs_z(1)) 
    hence new_edge_in_T: "{last ys, z} \<in> T" 
      using edge_mid_path[of T "butlast ys" "last ys" z zs] walk_between_nonempty_pathD(1)[OF p_walk ]
      by simp
    moreover have first_of_new_edge_in_S:"last ys \<in> Vs S" 
      using  last_in_set[OF ys_non_empty] ys_zs_z(3) by simp
    have no_cycle_after_insert:"has_no_cycle (insert {last ys, z} S)"
    proof(unfold has_no_cycle_def, rule ccontr, goal_cases)
      case 1
      moreover have inG:"insert {last ys, z} S \<subseteq> G"
        using arborescense_unfold(3) arborescense_unfold(6) new_edge_in_T by blast
      ultimately obtain u C where uC_prop: "decycle (insert {last ys, z} S) u C"  by auto
      hence inC:"{last ys, z} \<in> set C" 
        using arborescense_unfold(4) epath_edges_subset[of "insert {last ys, z} S" u C u] 
          epath_subset_other_set[of "insert {last ys, z} S" u C u S]
        by (fastforce simp add: decycle_def has_no_cycle_def)
      then obtain C1 C2 where C_split:"C = C1@[{last ys, z}]@C2"
        by(auto simp add: in_set_conv_decomp_first[of _ C])
      thus False
        using decycle_edge_path[OF inG uC_prop inC]  walk_endpoints(1) ys_zs_z(2)
        by auto
    qed
    moreover have Vs_and_comp:"Vs (insert {last ys, z} S) = connected_component (insert {last ys, z} S) r"
    proof-
      have "Vs (insert {last ys, z} S) = insert z (Vs S)" 
        using first_of_new_edge_in_S 
        by(auto simp add: Vs_def)
      also have "... = connected_component S z \<union>  connected_component S (last ys)"
        using arborescense_unfold(5)[OF False ] connected_components_member_eq[of "last ys" S r] 
          connected_components_notE_singletons[of z S] first_of_new_edge_in_S  ys_zs_z(2)
        by simp
      also have "... = connected_component (insert {last ys, z} S) (last ys)"
        using insert_edge_endpoints_same_component[OF reflexive] by fast
      also have "... = connected_component (insert {last ys, z} S) r"
        using calculation  in_Vs_insert[OF r_in_S]
          connected_components_member_eq[of r "insert {last ys, z} S" "last ys"] 
        by auto
      finally show ?thesis by auto
    qed
    ultimately have  "arborescence r (S \<union> {{last ys, z}})"
      by(simp add: arborescence_def)
    thus ?thesis
      using new_edge_in_T ys_zs_z(2) by auto
  qed
qed

lemma arborescence_extend_one_characterisation:
  assumes "arborescence r T" "{x, y} \<in> G""{x, y} \<notin> T"
  shows    "arborescence r (insert {x, y} T) \<longleftrightarrow>
           ((x \<in> insert r (Vs T) \<and> y \<notin> insert r (Vs T)) \<or> 
            (y \<in> insert r (Vs T) \<and> x \<notin> insert r (Vs T)))"
proof(rule , goal_cases)
  case 1
  hence arbor_unfolded: "has_no_cycle (insert {x, y} T)" 
    "Vs (insert {x, y} T) = connected_component (insert {x, y} T) r"
    "has_no_cycle T" "(T \<noteq> {} \<longrightarrow> Vs T = connected_component T r)"
    using assms(1) by(auto simp add:  arborescence_def)
  have x_not_y: "x \<noteq> y"
    using assms(2) by fastforce
  have " x \<in> insert r (Vs T) \<Longrightarrow> y \<in> insert r (Vs T) \<Longrightarrow> False"
  proof( goal_cases)
    case 1
    obtain pp where pp_prop:"walk_betw T x pp y"
      apply(rule  in_con_comp_has_walk[of y T x])
      using  "1"(1,2) arbor_unfolded(4) assms(2) connected_components_member_eq[of x T r]
        in_own_connected_component[of r T] vs_member[of _ T] 
      by auto
    then obtain p where p_prop:"walk_betw T x p y" "distinct p"
      using  walk_betw_different_verts_to_ditinct x_not_y by fast
    hence epath_p:"epath T x (edges_of_path p) y" 
      using dblton_E 
       by (auto intro!: walk_betw_imp_epath dblton_graph_subset[of G]  has_no_cycle_indep_subset_carrier 
         simp add: arbor_unfolded(3) graph_abs_subset  )
    have distinct_edges_p: "distinct (edges_of_path p)" 
      by (simp add: distinct_edges_of_vpath' p_prop(2))
    have xy_not_in_p: "{x, y} \<notin> set (edges_of_path p)"
      using assms(3) epath_edges_subset epath_p by fastforce
    have "length (edges_of_path p) \<ge> 2"
      using epath_p xy_not_in_p x_not_y
      by(cases "edges_of_path p" rule: vwalk_arcs.cases) auto
    hence "decycle (insert  {x, y} T)  x (edges_of_path p@[{x, y}])"
      using distinct_edges_p xy_not_in_p  epath_p x_not_y
      by(auto intro!: epath_append[of  _ _ _ y] intro: epath_subset simp add: decycle_def) 
    thus False
      using arbor_unfolded(1) by (auto simp add: has_no_cycle_def)
  qed
  moreover have " x \<notin> insert r (Vs T) \<Longrightarrow> y \<notin> insert r (Vs T) \<Longrightarrow> False"
    using  arbor_unfolded(2) edges_are_Vs[of x y "insert {x, y} T"] 
      in_connected_component_in_edges[of x T r] 
      in_connected_component_in_edges[of y T r]
      unite_disjoint_components_by_new_edge[of x T r y]  
    by auto
  ultimately show ?case by auto
next
  case 2
  note two = this
  have arbor_unfolded:  "has_no_cycle T" "(T \<noteq> {} \<longrightarrow> Vs T = connected_component T r)"
    using assms by(auto simp add: arborescence_def)
  have "has_no_cycle (insert {x, y} T)"
  proof(rule ccontr, goal_cases)
    case 1
    moreover have xyt_in_G: "insert {x, y} T \<subseteq> G"
      using  assms(1,2) has_no_cycle_indep_subset_carrier by (auto simp add: arborescence_def)
    ultimately obtain C u where uC: "decycle (insert {x, y} T) u C" 
      by(auto simp add: has_no_cycle_def)
    hence xy_in_C:"{x, y} \<in> set C" 
      using   assms(1)  new_edge_in_decycle
      by(force simp add: has_no_cycle_def arborescence_def)
    then obtain C1 C2  where C1C2: "C = C1@[{x,y}]@C2" 
      by (metis append_Cons append_Nil in_set_conv_decomp_first)
    hence xy_C1C2:"{x, y} \<notin> set C1 \<union> set C2" "set C1 \<union> set C2 \<noteq> {}"
      using uC unfolding decycle_def by auto
    hence "x \<in> Vs T" 
      using  decycle_edge_path[of x y T u C] uC walk_endpoints(2)[of T y _ x] xy_in_C xyt_in_G 
      by auto
    moreover have "y \<in> Vs T"
      using  decycle_edge_path[of x y T u C] uC walk_endpoints(2)[of T x _ y] xy_in_C xyt_in_G 
      by fastforce
    ultimately show False
      using "2" by blast
  qed
  moreover have "Vs (insert {x, y} T) = connected_component (insert {x, y} T) r"
  proof(rule, all \<open>rule\<close>, goal_cases)
    case (1 a)
    show ?case 
    proof(cases "a \<in> {x, y}")
      case True
      moreover have "x \<in> connected_component (insert {x, y} T) r"
      proof(rule disjE[OF 2], goal_cases)
        case 1
        then show ?case 
          using  assms(1)  connected_components_member_sym[of x T r]
            connected_components_member_sym[of y T r]
            connected_components_member_sym[of r "insert {x, y} T" x]
            insert_edge_endpoints_same_component[OF reflexive, of T x y] 
          by(auto simp add: Vs_def arborescence_def in_own_connected_component)
      next
        case 2
        then show ?case 
          using  assms(1)  connected_components_member_sym[of x T r]
            connected_components_member_sym[of y T r]
            connected_components_member_sym[of r "insert {x, y} T" x]
            insert_edge_endpoints_same_component[OF reflexive, of T x y] 
          by(auto simp add: Vs_def arborescence_def in_con_comp_insert insert_commute)
      qed
      moreover have "y \<in> connected_component (insert {x, y} T) r"
      proof(rule disjE[OF 2], goal_cases)
        case 1
        then show ?case 
          using  assms(1)  connected_components_member_sym[of x T r]
            connected_components_member_sym[of y T r]
            connected_components_member_sym[of r "insert {x, y} T" y]
            insert_edge_endpoints_same_component[OF reflexive, of T y x] 
          by(auto simp add: Vs_def arborescence_def in_con_comp_insert insert_commute)
      next
        case 2
        then show ?case 
          using  assms(1)  connected_components_member_sym[of x T r]
            connected_components_member_sym[of y T r]
            connected_components_member_sym[of r "insert {x, y} T" y]
            insert_edge_endpoints_same_component[OF reflexive, of T y x] 
          by(auto simp add: Vs_def arborescence_def insert_commute in_own_connected_component)
      qed
      ultimately show ?thesis by auto
    next
      case False
      then show ?thesis
        using  "1"  assms(1) connected_components_member_eq[of a T r] in_Vs_insertE[of a "{x, y}" T]
          in_own_connected_component[of a "insert {x, y} T"] 
          same_component_set_mono[of T "insert {x, y} T" r a]
        by(unfold Vs_def arborescence_def) blast
    qed
  next
    case (2 a)
    show ?case
    proof(cases " T = {}")
      case True
      then show ?thesis 
        using 2  in_connected_component_in_edges[of a "{{x, y}}" r] two 
        by(auto simp add: Vs_def)
    next
      case False
      hence "Vs T = connected_component T r"
        by (simp add: arbor_unfolded(2))
      then show ?thesis 
        using  "2" in_Vs_insert[of a T] in_connected_component_in_edges[of a "insert {x, y} T" r]
          in_own_connected_component[of r T ]
        by auto
    qed
  qed
  ultimately show ?case 
    by(auto simp add: arborescence_def)
qed

lemma basis_is: 
  assumes r_in_G: "r \<in> Vs G"
  shows "connected_component G r = connected_component T r \<and> has_no_cycle T \<and> connected T
                  \<longleftrightarrow> basis {T | T. arborescence r T} T"
proof(rule, goal_cases)
  case 1
  hence one: "connected_component G r = connected_component T r" "has_no_cycle T" "connected T" by auto
  hence T_in_G:"T \<subseteq> G" 
    by (simp add: has_no_cycle_indep_subset_carrier)
  obtain s where rs:"{r, s} \<in> G" "s \<noteq> r" 
    using Vs_eq_dVs dVs_member' edge_iff_edge_2 no_self_loops_2 r_in_G by auto
  hence "r \<in> Vs T" 
    using edges_are_walks[of r s G] has_path_in_connected_component2[of G r s] 
      in_connected_componentE[of s T r] one(1) by auto
  hence T_is_r_comp:"Vs T = connected_component T r" 
    using "1" \<open>r \<in> Vs T\<close> connected_component_set[of r T "Vs T"] reachable_in_Vs(2)[of T r]
    by(unfold connected_def) blast
  hence "arborescence r T"
    using  r_in_G  one(2) by (auto simp add: arborescence_def vs_member'[of r])
  moreover have "T \<subset> S \<Longrightarrow>  arborescence r S \<Longrightarrow> False" for S 
  proof(goal_cases)
    case 1
    then obtain e where e_pop: "e \<in> S - T" by auto
    hence e_in_G: "e \<in> G" 
      using "1"(2)  has_no_cycle_indep_subset_carrier by (fastforce simp add: arborescence_def)
    then obtain u v where uv: "e = {u, v}" "u \<noteq> v" by auto
    hence uv_in_S:"u \<in> Vs S" "v \<in> Vs S"
      using e_pop by auto
    hence "u \<in> connected_component S r"  "v \<in> connected_component S r"
      using "1"(1) "1"(2) by(auto simp add: arborescence_def)
    hence "u \<in> connected_component G r"  "v \<in> connected_component G r"
      using"1"(2) con_comp_subset[of S G]
      by(auto simp add: has_no_cycle_def arborescence_def) 
    hence "u \<in> connected_component T r"  "v \<in> connected_component T r"
      by (auto simp add: one(1))
    then obtain p where p:"walk_betw  T u p v"
      using connected_components_member_eq[of u T r]  uv(2)
      by(auto intro: in_con_comp_has_walk[of v T u])
    hence "epath T u (edges_of_path p) v" 
      using T_in_G by (auto intro!: walk_betw_imp_epath dblton_graph_subset[of G T] 
                          simp add:  graph_abs_subset  dblton_E)
    then obtain q where  q:"epath T u q v" "distinct q"
      by (auto dest: epath_distinct_epath)
    hence "epath S u q v" 
      using 1(1) by (auto intro: epath_subset)
    hence "epath S u (q @ [{u, v}]) u" 
      using uv(1,2) e_pop by(auto intro: epath_append)
    moreover have "distinct (q @ [{u, v}])" 
      using q(2)  e_pop epath_edges_subset[OF q(1)]  uv(1) by auto
    moreover have "length  (q @ [{u, v}]) \<ge> 2" 
      using uv(2) by(auto intro!: epath_non_empty[OF q(1), simplified])
    moreover have "length  (q @ [{u, v}]) = 2 \<Longrightarrow> False"
    proof(goal_cases)
      case 1
      hence "q = [{u, v}]" 
        using q(1) by(auto intro: list.exhaust[of q])
      hence "{u, v} \<in> T"
        using q(1) by auto
      then show ?case 
        using e_pop uv(1) by fastforce
    qed
    ultimately have"decycle S u (q @ [{u, v}])"
      by(force simp add: decycle_def) 
    thus False 
      using "1"(2)  by (auto simp add: arborescence_def has_no_cycle_def)
  qed
  ultimately  show ?case 
    by(auto simp add: basis_def)
next
  case 2
  hence arborT:"arborescence r T"
    by(auto simp add: basis_def)
  hence arbor_unfold:"has_no_cycle T" "T \<noteq> {} \<Longrightarrow> Vs T = connected_component T r"
    by(auto simp add: arborescence_def)
  have T_non_empt:"T \<noteq> {}"
  proof(rule ccontr, goal_cases)
    case 1
    obtain e where e_prop:"e \<in> G" "r \<in> e"
      using r_in_G vs_member' by auto
    hence "epath {e} u p u \<Longrightarrow> 2 < length p \<Longrightarrow> distinct p \<Longrightarrow> False" for u p
      by(auto intro: vwalk_arcs.cases[of p])
    hence "has_no_cycle {e}"
      using e_prop by(auto simp add: has_no_cycle_def decycle_def)
    moreover have "Vs {e} = connected_component {e} r"
      using e_prop connected_component_one_edge[of r e] 
      by(force elim: local.dblton_graphE[of e ])
    ultimately have "arborescence r {e}"
      by(simp add: arborescence_def)
    then show ?case 
      using 2 1 by(auto simp add: basis_def)
  qed
  have "connected_component G r = connected_component T r"
  proof-
    have "connected_component G r \<supseteq> connected_component T r"
      by (simp add: arbor_unfold(1) con_comp_subset has_no_cycle_indep_subset_carrier)
    moreover have "connected_component G r \<supset> connected_component T r \<Longrightarrow> False"
    proof(goal_cases)
      case 1
      then obtain x where x_prop:"x \<in> connected_component G r" "x \<notin> connected_component T r" by auto
      then obtain p where p_walk:"walk_betw G r p x"
        using in_connected_component_has_walk[of x G r]  r_in_G by auto
      moreover hence x_in_p:"x\<in>set p"
        using last_in_set by(auto simp add: walk_betw_def)
      moreover have r_in_T_comp:"r \<in> connected_component T r"
        by (simp add: in_connected_componentI2)
      ultimately obtain p1 z p2 where p_split: "p = p1@[z]@p2" "z \<notin> connected_component T r"
        "\<forall> x \<in> set p1. x \<in> connected_component T r " 
        using iffD1[OF split_list_first_prop_iff[of p "\<lambda> x. x \<notin> connected_component T r"]] x_prop(2)
        by auto
      have "r \<in> set p1" 
        using  hd_in_set[of p1]  p_walk r_in_T_comp walk_between_nonempty_path'(3)[of r p x] p_split(2)
        by(auto simp add: p_split(1) hd_append)
      hence new_in_G:"{last p1, z} \<in> G" 
        using p_split(1)  walk_between_nonempty_pathD(1)[OF p_walk] 
        by (force intro: edge_between_pref_suff[of p1 "[z]@p2", simplified] )
      have new_not_in_T:"{last p1, z} \<notin> T" 
        using arbor_unfold(2) edges_are_Vs_2 p_split(2) by blast
      have "has_no_cycle (insert {last p1, z} T)"
      proof(rule ccontr, goal_cases)
        case 1
        then obtain u C where uC_prop: "decycle (insert {last p1, z} T) u C"
          using arbor_unfold(1) has_no_cycle_def new_in_G by auto
        hence inC:"{last p1, z} \<in> set C" 
          using  epath_edges_subset[of "insert {last p1, z} T" u C u] 
            epath_subset_other_set[of "insert {last p1, z} T" u C u T]
            arbor_unfold(1) decycle_not_subset uC_prop
          by(force simp add:  decycle_def has_no_cycle_def)     
        then obtain C1 C2 where C_split:"C = C1@[{last p1, z}]@C2"
          by(auto simp add: in_set_conv_decomp_first[of _ C])
        thus False
          using decycle_edge_path[OF _ uC_prop inC]  walk_endpoints(1) arbor_unfold(2)[OF  T_non_empt]
            has_no_cycle_indep_subset_carrier[OF  arbor_unfold(1)] new_in_G p_split(2)
          by auto
      qed
      moreover have "Vs (insert {last p1, z} T) = connected_component (insert {last p1, z} T) r"
      proof-
        have "Vs (insert {last p1, z} T) = insert z (Vs T)" 
          using  \<open>r \<in> set p1\<close>  last_in_set[of p1] bspec[OF p_split(3)]
          by(unfold arbor_unfold(2)[OF T_non_empt, symmetric] Vs_def) fastforce
        also have "... = connected_component T z \<union>  connected_component T (last p1)"
          using  connected_components_member_eq[of "last p1" T r] 
            connected_components_notE_singletons[of z T] \<open>r \<in> set p1\<close> 
            arbor_unfold(2)[OF T_non_empt]  last_in_set[of p1] p_split(2) bspec[OF p_split(3)] 
          by fastforce
        also have "... = connected_component (insert {last p1, z} T) (last p1)"
          using insert_edge_endpoints_same_component[OF reflexive] by fast
        also have "... = connected_component (insert {last p1, z} T) r"
          using calculation  in_Vs_insert[of r T]  arbor_unfold(2)[OF T_non_empt] r_in_T_comp 
            connected_components_member_eq[of r "insert {last p1, z} T" "last p1"]  
          by force
        finally show ?thesis by auto
      qed  
      ultimately have "arborescence r (insert {last p1, z}  T)"
        by(auto simp add: arborescence_def)
      then show ?case 
        using 2 new_not_in_T by(auto simp add: basis_def) 
    qed
    ultimately show ?thesis by auto
  qed
  moreover have "connected T"
    using   arbor_unfold(2)[OF T_non_empt] connected_components_member_eq [of _ T r]
    by(auto intro: same_comp_connected) 
  ultimately show ?case
    by (simp add: arbor_unfold(1))
qed

lemma arborescense_connected: "arborescence  r T \<Longrightarrow> connected T "
  using connected_components_closed 
  by (fastforce intro!: same_comp_connected connected_components_member_eq 
                 elim!: arborescenceE)

lemma strong_exchange: assumes r_in_G: "r \<in> Vs G" 
  shows "strong_exchange_property G {T |T. arborescence r T}"
proof(rule strong_exchange_propertyI, goal_cases)
  case (1 A B e)
  note one = this
  hence one_unfolded:"has_no_cycle A" "(A \<noteq> {} \<Longrightarrow> Vs A = connected_component A r)"
    "has_no_cycle B" "(B \<noteq> {} \<Longrightarrow> Vs B = connected_component B r)"
    "has_no_cycle (insert e A)" "Vs (insert e A) = connected_component (insert e A) r"
    "A \<subseteq> G" "B \<subseteq> G" "insert e A \<subseteq> G"
    by(auto simp add: arborescence_def has_no_cycle_def)
  obtain x y where xy: "e ={x, y}" "x \<noteq> y"
    using one(5) by blast
  hence xy_inAe_component: "{x, y} \<subseteq> connected_component (insert e A) r"
    using one_unfolded(6) vs_member_intro by blast
  hence  "{x, y} \<subseteq> connected_component G r"
    using con_comp_subset[OF  one_unfolded(9)] by auto
  then obtain pp where pp_prop: "walk_betw B x pp y" 
    using basis_is[OF r_in_G, of B] one(4) in_connected_component_has_walk[of y B x] xy(2)
      connected_components_member_eq[of x B r] connected_components_notE_singletons[of x B]
    by force
  then obtain p where p_prop:"distinct p" "walk_betw B x p y" "set p \<subseteq> set pp"
    using walk_betw_different_verts_to_ditinct[OF pp_prop(1) xy(2) refl] by auto
  hence lenghtp: "length p \<ge> 2"
    using xy one(5) by(auto simp add: walk_betw_def intro: vwalk_arcs.cases[of p])
  have either_x_or_y_in_A: "(x \<in> insert r (Vs A) \<and> y \<notin> insert r (Vs A)) 
                            \<or> (y \<in> insert r (Vs A) \<and> x \<notin> insert r (Vs A))" 
  proof(cases "A = {}")
    case True
    then show ?thesis 
      using empty_iff in_connected_component_in_edges[of _ A r] in_mono insert_iff 
        unite_disjoint_components_by_new_edge[of x A r y] vs_member[of _ A] xy(1) xy(2) xy_inAe_component 
      by force
  next
    case False
    then show ?thesis
      using
        connected_component_in_components[of r A]  connected_components_closed''[of "Vs A" A  x]
        connected_components_closed''[of "Vs A" "insert e A"  r]
        has_no_cycle_ex_unique_path[of x y A]  in_connected_component_has_walk[of y A x]
        in_own_connected_component[of r A]  one(3) one_unfolded(2) one(5) one_unfolded(5) one_unfolded(9) 
        unchanged_connected_component[of x "Vs A" y A] xy(1) xy_inAe_component
      by (cases "\<nexists>p. walk_betw A x p y") auto
  qed
  have "x \<in> set p" "y \<in> set p"
    using last_in_set[of p] hd_in_set[of p] p_prop by(auto simp add: walk_betw_def)
  hence "\<exists>p1 p2 x' y'.
     p = p1 @ [x', y'] @ p2 \<and>
     (x' \<in> insert r (Vs A) \<and> y' \<notin> insert r (Vs A) \<or> y' \<in> insert r (Vs A) \<and> x' \<notin> insert r (Vs A))"
    using  list_P_switch[of x p "\<lambda> x. x \<in> insert r (Vs A)" y] 
      list_P_switch[of y p "\<lambda> x. x \<in> insert r (Vs A)" x] 
    by (cases rule: disjE[OF either_x_or_y_in_A]) auto
  then obtain u v p1 p2 where uvp1p2:"p = p1@[u, v]@p2" "(u \<in> insert r (Vs A) \<and> v \<notin> insert r (Vs A)) 
                            \<or> (v \<in> insert r (Vs A) \<and> u \<notin> insert r (Vs A))"
    by auto
  obtain u' v' where u'v':"u' \<in> insert r (Vs A)" "v' \<notin> (insert r (Vs A))"
    "{u', v'} \<in> set( edges_of_path p)"
    using edges_of_path_symmetric_split[of p1 u v p2] uvp1p2(1)
    by(cases rule: disjE[OF uvp1p2(2)]) auto
  hence u'v'B_without_A:"{u', v'} \<in> B - A" 
    using p_prop path_ball_edges[of B p] 
    by(unfold walk_betw_def) auto
  have u'v'_in_G:"{u', v'} \<in> G"
    using one_unfolded(8) u'v'B_without_A by fastforce
  have u'notv': "u' \<noteq> v'"
    using u'v'(1) u'v'(2) by blast
  have e_not_u'v': "e \<noteq> {u', v'}" 
    using one(5) u'v'B_without_A by blast
  have "arborescence r (insert {u', v'} A)"
  proof-
    have "has_no_cycle (insert {u', v'} A)"
      using  has_no_cycle_indep_subset[OF one_unfolded(3)] 
        one(3) one_unfolded(3) u'v'B_without_A by auto
    moreover have "Vs (insert {u', v'} A) = connected_component (insert {u', v'} A) r"
    proof(cases "A = {}")
      case True
      then show ?thesis 
        using  reachable_refl[of u' A]  u'v'(1) u'v'(2)
          connected_component_one_edge[of u' "{u', v'}"]  not_reachable_empt[of u' ]
        by auto
    next
      case False
      hence Vs_simpl:" insert r (Vs A) = Vs A"
        by (simp add: in_own_connected_component insert_absorb one_unfolded(2))
      show ?thesis 
      proof-
        have "Vs  (insert {u', v'} A) = insert v' (Vs A)" 
          using u'v'(1,2) Vs_simpl by(auto simp add: Vs_def)
        also have "... = connected_component A v' \<union>  connected_component A u'"
          using False Vs_simpl connected_components_member_eq[of u' A r] 
            connected_components_notE_singletons[of v' A] one_unfolded(2) u'v'(1) u'v'(2) 
          by auto
        also have "... = connected_component (insert {u', v'} A) u'"
          using insert_edge_endpoints_same_component[OF reflexive] by fast
        also have "... = connected_component (insert {u', v'} A) r"
          using calculation  in_Vs_insert[of r A "{u', v'}"]  
            connected_components_member_eq[of r "insert {u', v'} A" "u'"]   False Vs_simpl by auto
        finally show ?thesis by auto
      qed  
    qed
    ultimately show ?thesis
      by(simp add: arborescence_def)
  qed
  moreover have "arborescence r (B - {{u', v'}} \<union> {e})"
  proof-
    have Bu'v'e_inG: "B - {{u', v'}} \<union> {e} \<subseteq> G"
      using one_unfolded(8) one_unfolded(9) by auto
    have B_without_new_acycl:"has_no_cycle (B - {{u', v'}})"
      using graph_indep_system indep_system.indep_subset one_unfolded(3) by fastforce
    have "has_no_cycle (B - {{u', v'}} \<union> {e})"
    proof(rule ccontr, goal_cases)
      case 1
      then obtain C a where Ca:"decycle  (B - {{u', v'}} \<union> {e}) a C"
        by (meson Bu'v'e_inG has_no_cycle_def)
      hence e_in_C:"e \<in> set C" 
        using B_without_new_acycl Bu'v'e_inG 
          decycle_not_subset[of "(B - {{u', v'}} \<union> {e})" C "(B - {{u', v'}})"] 
          epath_edges_subset[of " (B - {{u', v'}} \<union> {e})" a C a] 
        by(unfold has_no_cycle_def  decycle_def ) blast
      have epathC: "epath (B - {{u', v'}} \<union> {e}) a C a" 
        by (meson Ca decycle_def)
      hence epathCG: "epath G a C a" 
        by (meson Bu'v'e_inG epath_subset)
      obtain C1 C2 where C1C2: "C = C1 @ [{x, y}] @ C2" 
        "(epath G a C1 x \<and> epath G y C2 a \<or> epath G a C1 y \<and> epath G x C2 a)"
        using  epath_one_split[OF epathCG, of x y]  e_in_C xy(1) xy(2) by blast
      hence epathC1C2:"( epath G y (C2@C1) x \<or> epath G x (C2@C1) y)"
        by (meson epath_append)
      moreover have "e \<notin> set (C2@C1)" 
        using C1C2(1) e_in_C Ca by(simp add: decycle_def xy(1))
      moreover have "set C \<subseteq>  (B - {{u', v'}} \<union> {e})"
        by (meson epathC epath_edges_subset)
      ultimately  have " set (C2@C1) \<subseteq>  (B - {{u', v'}}) " 
        unfolding xy(1) 
        by (simp add: C1C2(1) subset_insert)
      hence  epath_xy_B_without_new: 
        "(epath (B - {{u', v'}}) y (C2@C1) x \<or> epath (B - {{u', v'}}) x (C2@C1) y)"
        using epathC1C2  epath_subset_other_set by force
      hence epathBC1C2:"(epath (B) y (C2@C1) x \<or> epath (B ) x (C2@C1) y)"
        using  Diff_subset epath_subset by fast
      have epath_p: "epath B x (edges_of_path p) y" 
        using one_unfolded(8) 
        by (auto intro!: walk_betw_imp_epath dblton_graph_subset[of G B] 
               simp add:  graph_abs_subset  p_prop  dblton_E)
      obtain p1 p2 where p1p2:"edges_of_path p = p1 @ [{u', v'}] @ p2"
        "(epath B x p1 u' \<and> epath B v' p2 y \<or> epath B x p1 v' \<and> epath B u' p2 y)"
        using epath_one_split[OF epath_p u'v'(3) u'notv'] by auto
      have "\<exists> q. epath B u' q v' \<and> {u', v'} \<notin> set q"
      proof-
        have never_in: "{u', v'} \<notin> set p1"  "{u', v'} \<notin> set p2"  "{u', v'} \<notin> set C1" "{u', v'} \<notin> set C2"
          using \<open>set (C2 @ C1) \<subseteq> B - {{u', v'}}\<close> p1p2(1) distinct_edges_of_vpath[OF p_prop(1)] by auto
        show ?thesis 
        proof(cases rule: disjE[OF p1p2(2)], all \<open>cases rule: disjE[OF epathBC1C2]\<close>, goal_cases)
          case 1
          have "epath B u' (rev p1 @ rev C1 @ rev C2 @ rev p2) v'"
            using "1"(1) "1"(2) append_assoc epath_append epath_rev rev_append
            by metis
          thus ?case
            using never_in by auto
        next
          case 2
          hence "epath B u' (rev p1 @C2@C1 @ rev p2) v'" 
            using append_assoc epath_append epath_rev rev_append by metis
          then show ?case 
            using never_in by auto
        next
          case 3
          hence "epath B u' (p2 @  C2@C1 @ p1) v'" 
            using append_assoc epath_append epath_rev rev_append by metis
          then show ?case 
            using never_in by auto
        next
          case 4
          hence "epath B u' (p2 @  rev (C2@C1) @ p1) v'" 
            using append_assoc epath_append epath_rev rev_append by metis
          then show ?case 
            using never_in by auto
        qed
      qed
      then obtain q where q_prop:"epath B u' q v'" "{u', v'} \<notin> set q"
        by auto
      then obtain q' where q'_prop:"epath B u' q' v'" "set q' \<subseteq> set q" "distinct q'"
        using epath_distinct_epath[of B u' q v'] by auto
      have "length q' \<ge> 2"
        using q'_prop(1,2) u'notv' q_prop(2) by(cases q' rule: vwalk_arcs.cases) auto
      moreover have "distinct ({u', v'}#q')" 
        using q'_prop(2) q'_prop(3) q_prop(2) by auto
      moreover have "epath B v' ({u', v'}#q') v'"
        using q'_prop(1) u'notv' u'v'B_without_A by fastforce
      ultimately have "decycle B v'  ({u', v'}#q')" by(simp add: decycle_def)
      thus False 
        using  one_unfolded(3) by (auto simp add: has_no_cycle_def)
    qed
    moreover have "Vs (B - {{u', v'}} \<union> {e}) = connected_component (B - {{u', v'}} \<union> {e}) r"
    proof(rule, all \<open>rule\<close>, goal_cases)
      case (1 a)
      show ?case 
      proof(cases "a \<in> e")
        case True
        hence a1:"a \<in> connected_component (insert e A) r"
          using xy(1) xy_inAe_component by blast
        have a2:"insert e A \<subseteq>  (B - {{u', v'}} \<union> {e})" 
          using one(3) u'v'B_without_A by auto
        show ?thesis 
          using con_comp_subset[OF a2] a1 by auto
      next
        case False
        hence a_inB_without_new: "a \<in> Vs (B - {{u', v'}})" 
          using "1" by(auto elim: in_Vs_insertE)
        hence "a \<in> Vs B"
          by (meson Diff_iff vs_member)
        hence "a \<in> connected_component B r"
          using one_unfolded(4) u'v'B_without_A by blast
        then obtain qq where "walk_betw B r qq a"
          using  \<open>a \<in> Vs B\<close> in_con_comp_has_walk[of a B r] in_connected_component_has_walk[of a B r]
          by auto
        then obtain q where q_prop:"walk_betw B r q a" "distinct q" 
          using distinct_singleton[of a] walk_betw_different_verts_to_ditinct[of B r _ a, OF _  _ refl] walk_reflexive[of a B]
          by force     
        show ?thesis
        proof(cases "{u', v'}\<in> set (edges_of_path q)")
          case True
          have epath_q:"epath B r (edges_of_path q ) a" and epath_p:"epath B x (edges_of_path p) y"
            using  one_unfolded(8)
            by (auto intro!: walk_betw_imp_epath dblton_graph_subset[of G B]
                   simp add:  graph_abs_subset q_prop(1) p_prop(2) dblton_E)
          obtain q1 q2 where q1q2:"edges_of_path q = q1 @ [{u', v'}] @ q2" 
            "(epath B r q1 u' \<and> epath B v' q2 a \<or> epath B r q1 v' \<and> epath B u' q2 a)"
            using epath_one_split[OF epath_q True] u'notv' by blast
          obtain p1 p2 where p1p2:"edges_of_path p = p1 @ [{u', v'}] @ p2" 
            "(epath B x p1 u' \<and> epath B v' p2 y \<or> epath B x p1 v' \<and> epath B u' p2 y)"
            using epath_one_split[OF epath_p u'v'(3) u'notv'] by auto
          have u'v'_not_in: "{u', v'} \<notin> set p1 \<union> set p2 \<union> set q1 \<union> set q2" 
            using p1p2(1) q1q2(1) distinct_edges_of_vpath[OF q_prop(2)] 
              distinct_edges_of_vpath[OF p_prop(1)] by simp
          have  "\<exists> pra. epath (insert e B) r pra a \<and> {u', v'} \<notin> set pra \<and> length pra \<ge> 1"
          proof(cases rule: disjE[OF q1q2(2)], all \<open>cases rule: disjE[OF p1p2(2)]\<close>, goal_cases)
            case 1
            hence epaths: "epath (insert e B) r q1 u'" "epath (insert e B) v' q2 a" 
              "epath (insert e B) x p1 u'" "epath (insert e B) v' p2 y" 
              "epath (insert e B) x [e] y"  "epath (insert e B) y [e] x"
              using xy(1,2) by(auto intro: epath_subset)
            have "epath (insert e B) r (q1 @ rev p1@[e]@rev p2@q2) a"
              apply(rule epath_append[OF epaths(1)])
              apply(rule epath_append[OF epath_rev[OF epaths(3)]])
              apply(rule epath_append[OF epaths(5)])
              by(rule epath_append[OF epath_rev[OF epaths(4)] epaths(2)])
            thus ?case 
              using u'v'_not_in e_not_u'v' by auto
          next
            case 2
            hence epaths: "epath (insert e B) r q1 u'" "epath (insert e B) v' q2 a" 
              "epath (insert e B) x p1 v'" "epath (insert e B) u' p2 y" 
              "epath (insert e B) x [e] y"  "epath (insert e B) y [e] x"
              using xy(1,2) by(auto intro: epath_subset)
            have "epath (insert e B) r (q1 @ p2@[e]@p1@q2) a"
              apply(rule epath_append[OF epaths(1)])
              apply(rule epath_append[OF epaths(4)])
              apply(rule epath_append[OF epaths(6)])
              by(rule epath_append[OF epaths(3) epaths(2)])
            thus ?case 
              using u'v'_not_in e_not_u'v' by auto
          next
            case 3
            hence epaths: "epath (insert e B) r q1 v'" "epath (insert e B) u' q2 a" 
              "epath (insert e B) x p1 u'" "epath (insert e B) v' p2 y" 
              "epath (insert e B) x [e] y"  "epath (insert e B) y [e] x"
              using xy(1,2) by(auto intro: epath_subset)
            have "epath (insert e B) r (q1 @ p2@[e]@p1@q2) a"
              apply(rule epath_append[OF epaths(1)])
              apply(rule epath_append[OF epaths(4)])
              apply(rule epath_append[OF epaths(6)])
              by(rule epath_append[OF epaths(3) epaths(2)])
            thus ?case 
              using u'v'_not_in e_not_u'v' by auto
          next
            case 4
            hence epaths: "epath (insert e B) r q1 v'" "epath (insert e B) u' q2 a" 
              "epath (insert e B) x p1 v'" "epath (insert e B) u' p2 y" 
              "epath (insert e B) x [e] y"  "epath (insert e B) y [e] x"
              using xy(1,2) by(auto intro: epath_subset)
            have "epath (insert e B) r (q1 @ rev p1@[e]@rev p2@q2) a"
              apply(rule epath_append[OF epaths(1)])
              apply(rule epath_append[OF epath_rev[OF epaths(3)]])
              apply(rule epath_append[OF epaths(5)])
              by(rule epath_append[OF epath_rev[OF epaths(4)] epaths(2)])
            thus ?case 
              using u'v'_not_in e_not_u'v' by auto
          qed
          then obtain pra where pra_prop: "epath (insert e B) r pra a" "{u', v'} \<notin> set pra" "length pra \<ge> 1"
            by auto
          hence epath_without_u'v':"epath (insert e (B - {{u', v'}})) r pra a"
            using epath_edges_subset[OF pra_prop(1)] 
            by(auto intro!: epath_subset_other_set[OF pra_prop(1)])
          obtain prav where "walk_betw (insert e (B - {{u', v'}})) r prav a" "pra = edges_of_path prav"
            using epath_imp_walk_betw[OF epath_without_u'v' pra_prop(3)] by auto
          thus ?thesis
            by (simp add: has_path_in_connected_component)
        next
          case False
          note false = this
          show ?thesis
          proof(cases "a = r")
            case True
            then show ?thesis
              by (simp add: in_own_connected_component)
          next
            case False
            hence "set (edges_of_path q) \<subseteq> B - {{u', v'}}"
              using  false path_edges_subset q_prop(1)
              by(auto simp add:  walk_betw_def)
            moreover have  "walk_betw (set (edges_of_path q)) r q a"
              using  walk_betw_length[OF False[symmetric]  q_prop(1)] 
              by(auto intro: walk_in_edges_of_path[OF q_prop(1)])
            ultimately have "walk_betw (B - {{u', v'}}) r q a"
              by (auto intro: walk_subset)
            hence "walk_betw (insert e (B - {{u', v'}})) r q a" 
              by (auto intro: walk_subset)
            thus ?thesis
              by(auto intro!: has_path_in_connected_component2)
          qed
        qed
      qed
    next
      case (2 a)
      show ?case
      proof(cases "a = r")
        case True
        hence "a \<in> Vs B" 
          using  in_own_connected_component[of r B] not_reachable_empt one_unfolded(4) 
            reachableI[OF pp_prop] by force
        moreover have "insert e A \<subseteq> B - {{u', v'}} \<union> {e}"
          using one(3) u'v'B_without_A by auto
        then show ?thesis 
          using  True  Vs_subset[of "insert e A" "B - {{u', v'}} \<union> {e}"] 
            in_connected_componentI2[OF True] 
            one(3) one_unfolded(6) 
          by auto
      next
        case False
        then show ?thesis 
          using  in_connected_component_in_edges[OF 2] by auto
      qed
    qed
    ultimately show ?thesis 
      by(simp add: arborescence_def) 
  qed
  ultimately show ?case 
    using u'v'B_without_A 
    by auto
qed
end
end
