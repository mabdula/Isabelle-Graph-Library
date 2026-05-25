theory Spanning_Trees
  imports Undirected_Set_Graphs.Pair_Graph_Berge_Adaptor 
          Undirected_Set_Graphs.Pair_Graph_U_Specs
    Matroids_Greedy.Matroids_Theory
begin

section \<open>Spanning Trees\<close>

text \<open>We prove that in an undirected graph, the property of having no cycles forms a matroid
(the graphic/cycle matroid), with the carrier set being the set of edges of the graph and the
independence function being the function has_no_cycle.\<close>

text \<open>Matroid properties\<close>

context graph_abs
begin

lemma has_no_cycle_augment:
  "\<lbrakk>has_no_cycle X; has_no_cycle Y; card X = Suc (card Y)\<rbrakk>
     \<Longrightarrow> \<exists>x. x \<in> (X - Y) \<and> has_no_cycle (insert x Y)"
proof (rule ccontr, goal_cases)
  case 1
  then have "\<And> x. x \<in> X - Y \<Longrightarrow> \<not>has_no_cycle (insert x Y)" by blast
  moreover have "\<And> x. x \<in> X - Y \<Longrightarrow> (insert x Y) \<subseteq> G"
    using \<open>has_no_cycle X\<close> \<open>has_no_cycle Y\<close> unfolding has_no_cycle_def by auto
  ultimately have "\<And> x. x \<in> X - Y \<Longrightarrow> (\<exists>u c. decycle (insert x Y) u c)"
    unfolding has_no_cycle_def by simp

  from \<open>has_no_cycle X\<close> have "X \<subseteq> G" unfolding has_no_cycle_def by auto
  from \<open>has_no_cycle Y\<close> have "Y \<subseteq> G" unfolding has_no_cycle_def by auto
  from \<open>X \<subseteq> G\<close> finite_E have "finite X" by (simp add: finite_subset)
  from \<open>Y \<subseteq> G\<close> finite_E have "finite Y" by (simp add: finite_subset)
  from subset_edges_G[OF \<open>X \<subseteq> G\<close>] have "\<And> e. e \<in> X \<Longrightarrow> \<exists>u v. e = {u, v} \<and> u \<noteq> v" by simp
  then have "dblton_graph X" unfolding dblton_graph_def by blast
  from subset_edges_G[OF \<open>Y \<subseteq> G\<close>] have "\<And> e. e \<in> Y \<Longrightarrow> \<exists>u v. e = {u, v} \<and> u \<noteq> v" by simp
  then have "dblton_graph Y" unfolding dblton_graph_def by blast

  let ?V = "Vs G"
  have "finite ?V" using graph by blast
  have "Vs X \<subseteq> ?V" unfolding Vs_def using \<open>has_no_cycle X\<close> unfolding has_no_cycle_def by auto
  have "Vs Y \<subseteq> ?V" unfolding Vs_def using \<open>has_no_cycle Y\<close> unfolding has_no_cycle_def by auto

  from \<open>has_no_cycle Y\<close> have "(\<nexists>u c. decycle Y u c)"
    unfolding has_no_cycle_def by simp

(* Every CC of X is a subset of a CC of Y *)
  have ex_CC_subset:
    "\<And> C. C \<in> connected_components' ?V X \<Longrightarrow> \<exists>C' \<in> connected_components' ?V Y. C \<subseteq> C'"
  proof(goal_cases)
    case (1 C)
    note one = this
    then consider (a) "C \<in> connected_components X" | (b) "\<exists>v \<in> ?V - (Vs X). C = {v}"
      unfolding connected_components'_def by blast
    then show "\<exists>C' \<in> connected_components' ?V Y. C \<subseteq> C'"
    proof (cases)
      case a
      have "\<And> u v. \<lbrakk>u \<in> C; v \<in> C\<rbrakk> \<Longrightarrow> connected_component Y u = connected_component Y v \<and> u \<in> Vs Y"
      proof (goal_cases)
        case (1 u v)
        with \<open>C \<in> connected_components X\<close>
        have "\<exists>p. walk_betw X u p v" 
          by (meson same_con_comp_walk)
        then obtain p where "walk_betw X u p v" by blast
        from insert_edge_cycle_ex_walk_betw[OF \<open>X \<subseteq> G\<close> \<open>Y \<subseteq> G\<close> _
            \<open>(\<nexists>u c. decycle Y u c)\<close> this] 
        obtain q where "walk_betw Y u q v" 
          using \<open>\<And>x. x \<in> X - Y \<Longrightarrow> \<exists>u c. decycle (insert x Y) u c\<close> by blast
        then show "connected_component Y u = connected_component Y v \<and> u \<in> Vs Y"
          by (metis connected_components_member_eq in_connected_componentI reachableI walk_endpoints(1))
      qed
      then have "\<exists>w \<in> Vs Y. \<forall>u \<in> C. connected_component Y u = connected_component Y w"
        by (metis C_is_componentE a in_connected_componentI2)
      then have "\<exists>C' \<in> connected_components Y. \<forall>u \<in> C. u \<in> C'"
        by (metis connected_component_in_components in_own_connected_component)
      then show ?thesis unfolding connected_components'_def by blast 
    next
      case b
      then obtain v where "v \<in> ?V - (Vs X)" "C = {v}" by blast
      with union_connected_components'[OF \<open>dblton_graph Y\<close> \<open>Vs Y \<subseteq> ?V\<close>]
      show ?thesis by auto
    qed
  qed

(* Since CCs of Y are pairwise disjoint, every CC of X is a subset of exactly one CC of Y *)
  have ex_CC_subset_unique:
    "\<And> C. C \<in> connected_components' ?V X \<Longrightarrow> \<exists>!C' \<in> connected_components' ?V Y. C \<subseteq> C'"
  proof(goal_cases)
    case (1 C)
    with ex_CC_subset have
      "\<exists>C' \<in> connected_components' ?V Y. C \<subseteq> C'" by simp
    then obtain C' where "C' \<in> connected_components' ?V Y" "C \<subseteq> C'" by blast
    with connected_components'_disj connected_component'_nonempty
    have "(\<And>C''. C'' \<noteq> C' \<Longrightarrow> C'' \<in> connected_components' ?V Y \<Longrightarrow> \<not>C \<subseteq> C'')"
      by (metis Int_subset_iff \<open>C \<in> connected_components' (Vs G) X\<close> subset_empty)
    with \<open>C' \<in> connected_components' ?V Y\<close> \<open>C \<subseteq> C'\<close>
    show "\<exists>!C' \<in> connected_components' ?V Y. C \<subseteq> C'" by metis
  qed
  let ?f = "\<lambda>C. (THE C'. C' \<in> connected_components' ?V Y \<and> C \<subseteq> C')"
  from ex_CC_subset_unique theI'
  have "\<And> C. C \<in> connected_components' ?V X \<Longrightarrow> ?f C \<in> connected_components' ?V Y \<and> C \<subseteq> ?f C"
    by (metis (no_types, lifting))
  then have f_image_subset:
    "?f ` (connected_components' ?V X) \<subseteq> connected_components' ?V Y"
    by blast
  have "finite (connected_components' ?V X)" 
    by (metis "1"(1) Vs_subset finite_UnionD graph has_no_cycle_def union_connected_components'[OF \<open>dblton_graph X\<close>])

(* p \<ge> q *)
  have "card (connected_components' ?V X) \<ge> card (connected_components' ?V Y)"
  proof (rule ccontr, goal_cases)
    case 1
    then have "card (connected_components' ?V X) < card (connected_components' ?V Y)" by auto

    from reverse_pigeonhole[OF \<open>finite (connected_components' ?V X)\<close> f_image_subset this]
    have "\<exists>C' \<in> (connected_components' ?V Y). \<forall>C \<in> (connected_components' ?V X). C' \<noteq> ?f C"
      by auto
    then obtain C' where "C' \<in> (connected_components' ?V Y)"
             "\<And> C. C \<in> (connected_components' ?V X) \<Longrightarrow> C' \<noteq> ?f C"
      by blast
    with \<open>finite (connected_components' ?V X)\<close> ex_CC_subset_unique
    have "\<And> C. C \<in> (connected_components' ?V X) \<Longrightarrow> \<not>C \<subseteq> C'"
      by (metis (no_types, lifting) the_equality)
    from connected_component'_nonempty[OF \<open>C' \<in> (connected_components' ?V Y)\<close>]
    obtain v where "v \<in> C'" by blast
    have "v \<notin> \<Union> (connected_components' ?V X)"
    proof (rule ccontr, goal_cases)
      case 1
      then have "v \<in> \<Union> (connected_components' ?V X)" by blast
      then obtain C where "C \<in> (connected_components' ?V X)" "v \<in> C" by auto
      with ex_CC_subset_unique
      obtain C'' where "C'' \<in> connected_components' ?V Y" "C \<subseteq> C''" by blast
      with  \<open>C \<in> (connected_components' ?V X)\<close>
      have "C' \<noteq> C''"
        using \<open>\<And>Ca. Ca \<in> connected_components' (Vs G) X \<Longrightarrow> \<not> Ca \<subseteq> C'\<close> by blast
      from connected_components'_disj[OF this \<open>C' \<in> (connected_components' ?V Y)\<close>
          \<open>C'' \<in> connected_components' ?V Y\<close>] \<open>v \<in> C\<close> \<open>C \<subseteq> C''\<close> \<open>v \<in> C'\<close>
      show ?case by blast
    qed

    with union_connected_components'[OF \<open>dblton_graph X\<close> \<open>Vs X \<subseteq> ?V\<close>] have "v \<notin> ?V" by simp
    moreover have "v \<in> ?V"
      using union_connected_components'[OF \<open>dblton_graph Y\<close> \<open>Vs Y \<subseteq> ?V\<close>] \<open>v \<in> C'\<close> \<open>C' \<in> (connected_components' ?V Y)\<close>
      by auto
    ultimately show ?case by blast
  qed

  have "card ?V = card (Vs X) + card (?V - Vs X)"
    by (metis Diff_disjoint Diff_partition \<open>Vs X \<subseteq> Vs G\<close> card_Un_disjoint finite_Diff2 graph infinite_super)
  also have "... = card X + card (connected_components X) + card (?V - Vs X)"
    using connected_components_card \<open>has_no_cycle X\<close> 
    using \<open>\<And>e. e \<in> X \<Longrightarrow> \<exists>u v. e = {u, v} \<and> u \<noteq> v\<close> by presburger
  also have "... = card X + card (connected_components' ?V X)"
    using card_connected_components' \<open>X \<subseteq> G\<close> \<open>finite X\<close>
          \<open>finite ?V\<close> 
    using \<open>\<And>e. e \<in> X \<Longrightarrow> \<exists>u v. e = {u, v} \<and> u \<noteq> v\<close> by fastforce
  finally have card_V_1: "card ?V = card X + card (connected_components' ?V X)" .
  have "card ?V = card (Vs Y) + card (?V - Vs Y)"
    by (metis Diff_disjoint Diff_partition \<open>Vs Y \<subseteq> Vs G\<close> card_Un_disjoint finite_Diff2 graph infinite_super)
  also have "... = card Y + card (connected_components Y) + card (?V - Vs Y)"
    using connected_components_card \<open>has_no_cycle Y\<close>  \<open>\<And>e. e \<in> Y \<Longrightarrow> \<exists>u v. e = {u, v} \<and> u \<noteq> v\<close> by presburger
  also have "... = card Y + card (connected_components' ?V Y)"
    using card_connected_components'[OF \<open>Y \<subseteq> G\<close> \<open>finite Y\<close> _ \<open>finite ?V\<close>] 
          \<open>\<And>e. e \<in> Y \<Longrightarrow> \<exists>u v. e = {u, v} \<and> u \<noteq> v\<close> by presburger
  finally have card_V_2: "card ?V = card Y + card (connected_components' ?V Y)" .
  from card_V_1 card_V_2 \<open>card (connected_components' ?V X) \<ge> card (connected_components' ?V Y)\<close>
  have "card X \<le> card Y" by linarith
  with \<open>card X = Suc (card Y)\<close> show ?case by simp
qed

lemma graph_matroid:
  "matroid G has_no_cycle"
  apply standard
  using finite_E has_no_cycle_indep_subset_carrier has_no_cycle_indep_ex has_no_cycle_indep_subset 
    has_no_cycle_augment
  by blast+

lemma graph_indep_system:
  "indep_system G has_no_cycle"
  using matroid.axioms(1)[OF graph_matroid] .

definition "is_spanning_forest X = 
(has_no_cycle X \<and> (\<forall>v \<in> Vs G. \<forall>w \<in> Vs G. {v, w} \<in> G \<longrightarrow> reachable X v w))"

lemma spanning_forest_alternative:
  "is_spanning_forest X = (has_no_cycle X \<and> (\<forall>v \<in> Vs G. \<forall>w \<in> Vs G. reachable G v w \<longrightarrow> reachable X v w))"
proof(unfold is_spanning_forest_def, rule iffI, goal_cases)
  case 1
  hence prem: "\<lbrakk>v\<in>Vs G; w\<in>Vs G; {v, w} \<in> G\<rbrakk> \<Longrightarrow> reachable X v w" for v w by auto
  have "walk_betw G v p w \<Longrightarrow> reachable X v w" for v w p 
  proof(insert prem, induction  v p w rule: induct_walk_betw)
    case (path1 v)
    then obtain u where "{v, u} \<in> G" 
      by (metis insert_commute vs_member')
    moreover hence "u \<in> Vs G" 
      by auto
    ultimately have "reachable X v u"
      using path1 by blast
    moreover hence "reachable X u v" 
      by (simp add: reachable_sym)
    ultimately show ?case 
      by (simp add: reachable_refl reachable_in_Vs(2))
  next
    case (path2 v v' vs b)
    have "reachable X v' b"
      using path2(3,4) by blast
    moreover have "reachable X v v'"
      using path2(1,4) 
      by (simp add: edges_are_Vs edges_are_Vs_2)
    ultimately show ?case 
      by (auto intro: reachable_trans)
  qed
  then show ?case 
    using 1
    by (auto simp add: reachable_def)
next
  case 2
  then show ?case 
    by (auto simp add: edges_reachable)
qed

lemma spanning_forest_iff_basis:
  "is_spanning_forest X = indep_system.basis G has_no_cycle X"
  unfolding is_spanning_forest_def indep_system.basis_def[OF graph_indep_system]
proof (standard, goal_cases)
  case 1
  then have "X \<subseteq> G" unfolding has_no_cycle_def by blast
  have "(\<forall>x \<in> G - X. \<not> has_no_cycle (Set.insert x X))"
  proof (rule ballI)
    fix x
    assume "x \<in> G - X"
    then obtain v w where "x = {v, w}" "v \<noteq> w" by blast
    with \<open>x \<in> G - X\<close> have "v \<in> Vs G" "w \<in> Vs G" by auto+
    with \<open>x \<in> G - X\<close> \<open>x = {v, w}\<close> 1
    have "\<exists>p. walk_betw X v p w" unfolding reachable_def by blast
    have "Set.insert {v, w} X \<subseteq> G"
      using \<open>X \<subseteq> G\<close> \<open>x = {v, w}\<close> \<open>x \<in> G - X\<close> by auto
    have "{v, w} \<notin> X"
      using \<open>x = {v, w}\<close> \<open>x \<in> G - X\<close> by blast
    from has_no_cycle_ex_unique_path[OF \<open>Set.insert {v, w} X \<subseteq> G\<close>] this \<open>\<exists>q. walk_betw X v q w\<close> \<open>x = {v, w}\<close> 
    show "\<not> has_no_cycle (Set.insert x X)" by blast
  qed
  with 1 show ?case by blast
next
  case 2
  then have "X \<subseteq> G" "\<nexists>u c. decycle X u c" unfolding has_no_cycle_def by blast+
  have "\<And> v w. \<lbrakk>v \<in> Vs G; w \<in> Vs G; {v, w} \<in> G\<rbrakk> \<Longrightarrow> reachable X v w"
  proof (goal_cases)
    case (1 v w)
    show "reachable X v w"
    proof (cases "{v, w} \<in> X")
      case True
      then show ?thesis unfolding reachable_def
        by (meson edges_are_walks)
    next
      case False
      with 2 \<open>{v, w} \<in> G\<close> have "\<not> has_no_cycle (Set.insert {v, w} X)" by blast
      moreover have "Set.insert {v, w} X \<subseteq> G"
        using \<open>{v, w} \<in> G\<close> \<open>X \<subseteq> G\<close> by simp
      ultimately obtain u c where "decycle (Set.insert {v, w} X) u c"
        unfolding has_no_cycle_def by blast
      with decycle_not_subset \<open>\<nexists>u c. decycle X u c\<close>
      have "\<not> set c \<subseteq> X" by metis
      moreover have "set c \<subseteq> (Set.insert {v, w} X)" 
        using \<open>decycle (Set.insert {v, w} X) u c\<close> decycle_def epath_edges_subset by metis
      ultimately have "{v, w} \<in> set c" by blast

      have "\<exists>p. walk_betw X v p w"
        using decycle_edge_path[OF \<open>(Set.insert {v, w} X) \<subseteq> G\<close>
            \<open>decycle (Set.insert {v, w} X) u c\<close> \<open>{v, w} \<in> set c\<close>] walk_symmetric
        by fast
      then show ?thesis
        unfolding reachable_def by simp
    qed
  qed
  with 2 show ?case by blast
qed

end
end