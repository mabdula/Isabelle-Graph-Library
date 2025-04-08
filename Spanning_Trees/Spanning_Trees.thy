theory Spanning_Trees
  imports Undirected_Set_Graphs.Pair_Graph_Berge_Adaptor Directed_Set_Graphs.Pair_Graph_U_Specs
    Matroids_Greedy.Matroids_Theory
begin

context graph_abs
begin

definition "has_no_cycle X = ( X \<subseteq> G \<and> (\<nexists>u c. decycle X u c))"

text \<open>We prove that in an undirected graph, the property of having no cycles forms a matroid
(the graphic/cycle matroid), with the carrier set being the set of edges of the graph and the
independence function being the function has_no_cycle.\<close>

text \<open>Matroid properties\<close>

lemma has_no_cycle_indep_subset_carrier:
  "has_no_cycle X \<Longrightarrow> X \<subseteq> G"
  unfolding has_no_cycle_def by simp

lemma has_no_cycle_indep_ex:
  "\<exists>X. has_no_cycle X"
proof-
  have "{} \<subseteq> G" by simp
  moreover have "\<nexists>u c. decycle {} u c"
    unfolding decycle_def
    by (metis epath_empty(2) less_zeroE list.size(3))
  ultimately show "\<exists>X. has_no_cycle X"
    unfolding has_no_cycle_def by auto
qed

lemma has_no_cycle_indep_subset:
  "has_no_cycle X \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> has_no_cycle Y"
  apply (rule ccontr)
  using has_no_cycle_def decycle_subset
  by (metis dual_order.trans)



(* TODO later: maybe reorganise some of the following lemmas
(put into e.g. Undirected_Set_Graphs, put outside of graph_abs context or use subset_graph/subgraph locale *)

lemmas graph_abs_subset = graph_abs_mono[OF graph_abs_axioms]

lemma subset_edges_G:
  "X \<subseteq> G \<Longrightarrow> e \<in> X \<Longrightarrow> \<exists>u v. e = {u, v} \<and> u \<noteq> v"
  using graph by blast


lemma set_aux:
  "S1 = S2 \<union> S3 \<Longrightarrow> S2 \<inter> S3 = {} \<Longrightarrow>
    ({x, y} \<subseteq> S1 \<longleftrightarrow> ({x, y} \<subseteq> S2 \<or> {x, y} \<subseteq> S3 \<or> (x \<in> S2 \<and> y \<in> S3) \<or> (x \<in> S3 \<and> y \<in> S2)))"
  by auto


lemma walk_betw_imp_epath: (* TODO maybe also add this to adaptor code *)
  "walk_betw G u p v \<Longrightarrow> epath G u (edges_of_path p) v"
  apply (induction p arbitrary: u v)
  unfolding walk_betw_def apply simp
  by (smt (verit) epath.elims(3) edges_of_path.elims graph_abs.edge_iff_edge_1
      graph_abs_axioms last.simps list.distinct(1) list.sel(1) list.sel(3) no_self_loops_1 path.simps)

lemma epath_imp_walk_betw: (* TODO maybe also add this to adaptor code *)
  "epath G u p v \<Longrightarrow>length p \<ge> 1  \<Longrightarrow>\<exists> q. walk_betw G u q v \<and> p = edges_of_path q"
proof(induction p arbitrary: u v rule: edges_of_path.induct)
  case (3 e d l u v)
  then obtain a b where e_prop:"e = {a, b}" "a \<noteq> b" "a = u" "e \<in> G"
    by auto 
  hence epath:"epath G b (d # l) v" 
    using "3.prems"(1) doubleton_eq_iff by auto
  then obtain q where q_prop:"walk_betw G b q v"  "d # l = edges_of_path q"
    using 3(1)[OF epath] by auto
  moreover have "walk_betw G u [u, b] b" 
    using e_prop edges_are_walks by force
  moreover have "e#d#l = edges_of_path (u#q)" 
    using e_prop(1) e_prop(3) q_prop(2) walk_between_nonempty_pathD(3)[OF q_prop(1)] 
      walk_nonempty [OF q_prop(1)] by(cases q) auto

  ultimately show ?case 
    using e_prop walk_betw_cons 
    by (auto intro!: exI[of _ "u#q"], cases q)fastforce+
next
  case (2 e u v)
  hence "e \<in> G" "e = {u, v}" "u \<noteq> v" by auto
  thus ?case 
    by(auto intro: exI[of _ "[u, v]"] simp add: edges_are_walks)
qed simp

(* TODO later: Some of the following theorems before the augment property could maybe be in Undirected_Set_Graphs *)

lemma has_no_cycle_ex_unique_path:
  "(insert {u, v} X) \<subseteq> G \<Longrightarrow> has_no_cycle (insert {u, v} X) \<Longrightarrow> {u, v} \<notin> X \<Longrightarrow> \<nexists>p. walk_betw X u p v"
proof (rule ccontr, goal_cases)
  case 1
  then obtain p where "walk_betw X u p v" by blast

  from subset_edges_G[OF \<open>(insert {u, v} X) \<subseteq> G\<close>]
  have "u \<noteq> v" by blast

  from \<open>has_no_cycle (insert {u, v} X)\<close> has_no_cycle_def graph_abs_subset
  have "graph_abs (insert {u, v} X)" by auto
  from \<open>has_no_cycle (insert {u, v} X)\<close> has_no_cycle_def graph_abs_subset
  have "graph_abs X" by auto
  from graph_abs.walk_betw_iff_vwalk_bet[OF \<open>graph_abs X\<close>] \<open>walk_betw X u p v\<close> 
  have "vwalk_bet (graph_abs.D X) u p v" by blast
  from vwalk_imp_awalk[OF this]
  have "awalk (graph_abs.D X) u (edges_of_vwalk p) v" .

  from \<open>{u, v} \<notin> X\<close> have "(u, v) \<notin> (graph_abs.D X)"
    by (meson \<open>graph_abs X\<close> graph_abs.edge_iff_edge_1)

  have "(v, u) \<in> graph_abs.D (insert {u, v} X)"
    by (meson \<open>graph_abs (insert {u, v} X)\<close> graph_abs.edge_iff_edge_2 insertCI)

  from apath_awalk_to_apath[OF \<open>awalk (graph_abs.D X) u (edges_of_vwalk p) v\<close>] apath_def
  have "awalk (graph_abs.D X) u (awalk_to_apath (graph_abs.D X) (edges_of_vwalk p)) v"
    "distinct (awalk_verts u (awalk_to_apath (graph_abs.D X) (edges_of_vwalk p)))"
    by fast+
  moreover have "graph_abs.D X \<subseteq> graph_abs.D (insert {u, v} X)"
    by (meson \<open>graph_abs (insert {u, v} X)\<close> \<open>graph_abs X\<close> graph_abs.edge_iff_edge_2 insert_iff subrelI)
  ultimately have "awalk (graph_abs.D (insert {u, v} X)) u (awalk_to_apath (graph_abs.D X) (edges_of_vwalk p)) v"
    by (meson \<open>(v, u) \<in> graph_abs.D (insert {u, v} X)\<close> awalk_def dVsI(2) subset_trans)

  let ?c = "(v, u) # (awalk_to_apath (graph_abs.D X) (edges_of_vwalk p))"
  from \<open>awalk (graph_abs.D (insert {u, v} X)) u (awalk_to_apath (graph_abs.D X) (edges_of_vwalk p)) v\<close>
  have "awalk (graph_abs.D (insert {u, v} X)) v ?c v"
    using awalk_Cons_iff[of "(graph_abs.D (insert {u, v} X))" "v" "(v, u)" "(awalk_to_apath (graph_abs.D X)
    (edges_of_vwalk p))" "v"] \<open>(v, u) \<in> graph_abs.D (insert {u, v} X)\<close>
    by auto

  have "tl (awalk_verts v ?c) = 
    awalk_verts u (awalk_to_apath (graph_abs.D X) (edges_of_vwalk p))"
    by simp
  with \<open>distinct (awalk_verts u (awalk_to_apath (graph_abs.D X) (edges_of_vwalk p)))\<close>
  have "distinct (tl (awalk_verts v ?c))" by simp

  have list_decomp_1: "\<And>l. length l = 1 \<Longrightarrow> \<exists>a. l = [a]"
    by (metis One_nat_def length_0_conv length_Cons nat.inject neq_Nil_conv)

  have "length ?c > 2"
  proof (rule ccontr, goal_cases)
    case 1
    then have "length ?c \<le> 2" by simp
    with \<open>awalk (graph_abs.D (insert {u, v} X)) v ?c v\<close> \<open>u \<noteq> v\<close> have "length ?c = 2"
      by (smt (verit, best) One_nat_def Suc_1
          \<open>awalk (graph_abs.D (insert {u, v} X)) u (awalk_to_apath (graph_abs.D X) (edges_of_vwalk p)) v\<close>
          \<open>u \<noteq> v\<close> awalk_Nil_iff diff_Suc_Suc diff_is_0_eq' length_Cons length_tl list.exhaust_sel)
    then have "length (awalk_to_apath (graph_abs.D X) (edges_of_vwalk p)) = 1" by simp
    with \<open>awalk (graph_abs.D X) u (awalk_to_apath (graph_abs.D X) (edges_of_vwalk p)) v\<close>
    have "[(u, v)] = (awalk_to_apath (graph_abs.D X) (edges_of_vwalk p))"
      using list_decomp_1 by fastforce
    with awalk_to_apath_subset[OF \<open>awalk (graph_abs.D X) u (edges_of_vwalk p) v\<close>]
    have "(u, v) \<in> set (edges_of_vwalk p)"
      by (metis in_mono list.set_intros(1))
    moreover have "set (edges_of_vwalk p) \<subseteq> (graph_abs.D X)"
      using \<open>awalk (graph_abs.D X) u (edges_of_vwalk p) v\<close> by blast
    ultimately show ?case
      using \<open>(u, v) \<notin> (graph_abs.D X)\<close> by blast
  qed

  from \<open>awalk (graph_abs.D (insert {u, v} X)) v ?c v\<close> \<open>distinct (tl (awalk_verts v ?c))\<close> \<open>length ?c > 2\<close>
  have "cycle' (graph_abs.D (insert {u, v} X)) ?c"
    unfolding cycle'_def cycle_def by blast
  from graph_abs.cycle'_imp_decycle[OF \<open>graph_abs (insert {u, v} X)\<close> this]
  have "\<exists>x. decycle (insert {u, v} X) x (map undirected ?c)" by blast
  with \<open>has_no_cycle (insert {u, v} X)\<close> has_no_cycle_def show ?case by simp
qed


lemma has_no_cycle_connected_component_card:
  assumes "finite X" "\<And>e. e \<in> X \<Longrightarrow> \<exists>u v. e = {u, v} \<and> u \<noteq> v"
  shows "has_no_cycle X \<Longrightarrow> C \<in> connected_components X \<Longrightarrow> card C = card (component_edges X C) + 1"
  using assms
proof (induction "X" arbitrary: C)
  case empty
  then show ?case
    using connected_components_empty by blast
next
  case (insert e F)
  then have "has_no_cycle F" "(\<And>e. e \<in> F \<Longrightarrow> \<exists>u v. e = {u, v} \<and> u \<noteq> v)"
    using has_no_cycle_indep_subset[OF \<open>has_no_cycle (insert e F)\<close>] by blast+

  from \<open>has_no_cycle (insert e F)\<close> has_no_cycle_def graph_abs_subset
  have "graph_abs (insert e F)" by simp
  from \<open>has_no_cycle (insert e F)\<close> has_no_cycle_def graph_abs_subset
  have "graph_abs F" by simp
  from insert(6) have "dblton_graph F"
    unfolding dblton_graph_def by simp

  from insert(6) obtain u v where "e = {u, v}" "u \<noteq> v" by blast
  have "{u, v} \<notin> F" using \<open>e = {u, v}\<close> insert.hyps(2) by blast

  have "component_edges (insert e F) C =
    {{x, y} | x y. {x, y} \<subseteq> C \<and> {x, y} \<in> (insert e F)}"
    unfolding component_edges_def by blast
  also have "... = 
    {{x, y} | x y. {x, y} \<subseteq> C \<and> {x, y} \<in> F} \<union> {{x, y} | x y. {x, y} \<subseteq> C \<and> {x, y} = e}"
    using \<open>e \<notin> F\<close> by auto
  also have "... = 
    component_edges F C \<union> {{x, y} | x y. {x, y} \<subseteq> C \<and> {x, y} = e}"
    using component_edges_def by metis
  finally have edges_expr:
    "component_edges (insert e F) C = component_edges F C \<union> {{x, y} | x y. {x, y} \<subseteq> C \<and> {x, y} = e}" .

  have edges_disj: "component_edges F C \<inter> {{x, y} | x y. {x, y} \<subseteq> C \<and> {x, y} = e} = {}"
    unfolding component_edges_def using \<open>e \<notin> F\<close> by fastforce

  have IH: "\<And>C'. C' \<in> connected_components F \<Longrightarrow> card C' = card (component_edges F C') + 1"
    using insert(3) \<open>has_no_cycle F\<close> \<open>(\<And>e. e \<in> F \<Longrightarrow> \<exists>u v. e = {u, v} \<and> u \<noteq> v)\<close> by blast

  have in_CC_F: "C \<in> connected_components F \<Longrightarrow> card C = card (component_edges (insert e F) C) + 1"
  proof-
    assume "C \<in> connected_components F"
    have "\<not>{u, v} \<subseteq> C"
    proof (rule ccontr, goal_cases False)
      case False
      then have "{u, v} \<subseteq> C" by auto

      from \<open>{u, v} \<subseteq> C\<close> \<open>C \<in> connected_components F\<close>
      have "\<exists>p. walk_betw F u p v"
        by (meson reachable_def \<open>C \<in> connected_components F\<close> insert_subset same_con_comp_reachable) 
      then obtain p where "walk_betw F u p v" by blast

      have "has_no_cycle (component_edges (insert e F) C)"
        using component_edges_subset has_no_cycle_indep_subset insert(4) by metis

      from \<open>has_no_cycle (insert e F)\<close> \<open>e = {u, v}\<close> has_no_cycle_def
      have "(insert {u, v} F) \<subseteq> G" by simp
      from \<open>e = {u, v}\<close> has_no_cycle_ex_unique_path[OF this] \<open>has_no_cycle (insert e F)\<close> \<open>e \<notin> F\<close>
        \<open>walk_betw F u p v\<close>
      show ?case by blast
    qed

    with \<open>e = {u, v}\<close> edges_expr
    have "component_edges (insert e F) C = component_edges F C" by blast
    with IH[OF \<open>C \<in> connected_components F\<close>]
    show "card C = card (component_edges (insert e F) C) + 1" by auto
  qed

  from \<open>C \<in> connected_components (insert e F)\<close> \<open>e = {u, v}\<close>
  have "C \<in> connected_components (insert {u, v} F)" by auto
  then show ?case
  proof(elim in_insert_connected_componentE, goal_cases)
    case 1
    then show ?case
    proof (safe, goal_cases)
      case 1
      have "\<And>x y. {x, y} \<subseteq> C \<Longrightarrow> {x, y} \<notin> F"
        by (metis "1"(1) "1"(2) "1"(3) bot.extremum_uniqueI insert_not_empty subset_insert vs_member_intro)
      then have "component_edges F C = {}"
        unfolding component_edges_def by blast
      with edges_expr
      have "component_edges (insert e F) C = {{x, y} | x y. {x, y} \<subseteq> C \<and> {x, y} = e}"
        by simp
      with 1 \<open>e = {u, v}\<close>
      have "component_edges (insert e F) C = {{u, v}}" by auto
      with 1(3) show ?case
        using \<open>u \<noteq> v\<close> by auto
    qed (auto simp add: in_CC_F)
  next
    case (2 u' v')
    then consider (a) "C = insert v' (connected_component F u')" |
      (b) "C \<in> (connected_components F - {connected_component F u'})" by blast
    then show ?case
    proof (cases)
      case a
      with 2 \<open>e = {u, v}\<close> have "e = {u', v'}" by auto

      from \<open>u' \<in> Vs F\<close> have "(connected_component F u') \<in> connected_components F"
        by (simp add: connected_component_in_components)

      have "{u', v'} \<subseteq> (insert v' (connected_component F u'))" 
        by (simp add: in_own_connected_component)
      then have "{{x, y} | x y. {x, y} \<subseteq> C \<and> {x, y} = e} = {{u, v}}"
        using a \<open>e = {u, v}\<close> \<open>e = {u', v'}\<close> by auto

      with edges_expr
      have "component_edges (insert e F) C = insert {u, v} (component_edges F C)"
        by simp

      have "v' \<notin> (connected_component F u')"
        by (metis "2"(3) "2"(4) in_connected_component_in_edges)
      from edges_disj \<open>{{x, y} | x y. {x, y} \<subseteq> C \<and> {x, y} = e} = {{u, v}}\<close>
      have "{u, v} \<notin> component_edges F C"
        by simp

      from connected_component_finite[OF insert(1) \<open>dblton_graph F\<close>] insert(6) 
        \<open>(connected_component F u') \<in> connected_components F\<close>
      have "finite (connected_component F u')" by blast
      from insert
        \<open>C \<in> connected_components (insert e F)\<close>
      have "finite (component_edges F C)"
        by (meson component_edges_subset finite_subset)

      have "card (component_edges (insert e F) C) = card (insert {u, v} (component_edges F C))"
        using \<open>component_edges (insert e F) C = insert {u, v} (component_edges F C)\<close> by auto


      have "component_edges F C =
        {{x, y} |x y. {x, y} \<subseteq> (connected_component F u') \<and> {x, y} \<in> F} \<union>
        {{x, y} |x y. {x, y} \<subseteq> {v'} \<and> {x, y} \<in> F} \<union>
        {{x, y} |x y. x \<in> (connected_component F u') \<and> y = v' \<and> {x, y} \<in> F} \<union>
        {{x, y} |x y. x = v' \<and> y \<in> (connected_component F u') \<and> {x, y} \<in> F}"
        unfolding component_edges_def using a by auto
      also have "... =
        {{x, y} |x y. {x, y} \<subseteq> (connected_component F u') \<and> {x, y} \<in> F} \<union>
        {{x, y} |x y. x \<in> (connected_component F u') \<and> y = v' \<and> {x, y} \<in> F} \<union>
        {{x, y} |x y. x = v' \<and> y \<in> (connected_component F u') \<and> {x, y} \<in> F}"
        using \<open>(\<And>e. e \<in> F \<Longrightarrow> \<exists>u v. e = {u, v} \<and> u \<noteq> v)\<close>
        by fastforce
      finally have "component_edges F C =
        {{x, y} |x y. {x, y} \<subseteq> (connected_component F u') \<and> {x, y} \<in> F} \<union>
        {{x, y} |x y. x \<in> (connected_component F u') \<and> y = v' \<and> {x, y} \<in> F} \<union>
        {{x, y} |x y. x = v' \<and> y \<in> (connected_component F u') \<and> {x, y} \<in> F}" by blast
      moreover have "{{x, y} |x y. x \<in> (connected_component F u') \<and> y = v' \<and> {x, y} \<in> F} =
        {{x, y} |x y. x = v' \<and> y \<in> (connected_component F u') \<and> {x, y} \<in> F}"
        by (metis (no_types, opaque_lifting) doubleton_eq_iff)
      ultimately have "component_edges F C =
        {{x, y} |x y. {x, y} \<subseteq> (connected_component F u') \<and> {x, y} \<in> F} \<union>
        {{x, y} |x y. x \<in> (connected_component F u') \<and> y = v' \<and> {x, y} \<in> F}" by simp
      then have component_edges_expr: "component_edges F C = component_edges F (connected_component F u')"
        using \<open>v' \<notin> Vs F\<close> unfolding component_edges_def by auto

      have "card C = 1 + card (connected_component F u')"
        using a card_insert_disjoint[OF \<open>finite (connected_component F u')\<close> \<open>v' \<notin> (connected_component F u')\<close>]
        by auto
      also have "... = 1 + card (component_edges F (connected_component F u')) + 1"
        using IH[OF \<open>(connected_component F u') \<in> connected_components F\<close>] by simp
      also have "... = 1 + card (component_edges (insert e F) C)"
        using \<open>component_edges (insert e F) C = insert {u, v} (component_edges F C)\<close>
          card_insert_disjoint[OF \<open>finite (component_edges F C)\<close> \<open>{u, v} \<notin> component_edges F C\<close>]
          component_edges_expr
        by simp
      finally show ?thesis by auto
    qed (auto simp add: in_CC_F)
  next
    case 3
    then consider (a) "C = connected_component F u \<union> connected_component F v" |
      (b) "C \<in> (connected_components F - {connected_component F u, connected_component F v})" by blast
    then show ?case
    proof (cases)
      case a
      from \<open>connected_component F u \<noteq> connected_component F v\<close>
      have "v \<notin> connected_component F u" "u \<notin> connected_component F v"
        using connected_components_member_eq
        by (fastforce simp only:)+
      from \<open>connected_component F u \<noteq> connected_component F v\<close>
      have "connected_component F u \<inter> connected_component F v = {}"
        using connected_components_disj
        by(auto intro!: connected_component_in_components 3)

      from \<open>u \<in> Vs F\<close> \<open>v \<in> Vs F\<close>
      have "(connected_component F u) \<in> connected_components F"
        "(connected_component F v) \<in> connected_components F"
        by (simp add: connected_component_in_components)+

      from a in_own_connected_component
      have "{u, v} \<subseteq> C" by fast
      with \<open>e = {u, v}\<close>
      have "{{x, y} |x y. {x, y} \<subseteq> C \<and> {x, y} = e} = {{u, v}}" by auto

      have
        "component_edges F C =
          {{x, y} |x y. {x, y} \<subseteq> (connected_component F u) \<and> {x, y} \<in> F} \<union>
          {{x, y} |x y. {x, y} \<subseteq> (connected_component F v) \<and> {x, y} \<in> F} \<union>
          {{x, y} |x y. x \<in> (connected_component F u) \<and> y \<in> (connected_component F v) \<and> {x, y} \<in> F} \<union>
          {{x, y} |x y. x \<in> (connected_component F v) \<and> y \<in> (connected_component F u) \<and> {x, y} \<in> F}"
        unfolding component_edges_def using set_aux[OF a \<open>connected_component F u \<inter> connected_component F v = {}\<close>]
        by auto
      moreover have
        "{{x, y} |x y. x \<in> (connected_component F u) \<and> y \<in> (connected_component F v) \<and> {x, y} \<in> F} =
         {{x, y} |x y. x \<in> (connected_component F v) \<and> y \<in> (connected_component F u) \<and> {x, y} \<in> F}"
        by (metis (no_types, opaque_lifting) insert_commute)
      ultimately have "component_edges F C =
        {{x, y} |x y. {x, y} \<subseteq> (connected_component F u) \<and> {x, y} \<in> F} \<union>
        {{x, y} |x y. {x, y} \<subseteq> (connected_component F v) \<and> {x, y} \<in> F} \<union>
        {{x, y} |x y. x \<in> (connected_component F u) \<and> y \<in> (connected_component F v) \<and> {x, y} \<in> F}"
        by simp
      moreover have "\<And>x y. x \<in> (connected_component F u) \<and> y \<in> (connected_component F v) \<Longrightarrow> {x, y} \<notin> F"
        by (metis "3"(3) connected_components_member_eq in_con_comp_insert insert_absorb)
      ultimately have component_edges_expr: "component_edges F C =
        component_edges F (connected_component F u) \<union>
        component_edges F (connected_component F v)"
        unfolding component_edges_def by auto

      from edges_expr \<open>{{x, y} |x y. {x, y} \<subseteq> C \<and> {x, y} = e} = {{u, v}}\<close> component_edges_expr
      have "component_edges (insert e F) C = 
          (component_edges F (connected_component F u)) \<union>
          (component_edges F (connected_component F v)) \<union> {{u, v}}"
        by simp

      moreover have "{u, v} \<notin> (component_edges F (connected_component F u))"
        "{u, v} \<notin> (component_edges F (connected_component F v))"
        using \<open>{u, v} \<notin> F\<close> component_edges_subset by blast+

      ultimately have card_component_edges: "card (component_edges (insert e F) C) = 
        card (component_edges F (connected_component F u)) +
        card (component_edges F (connected_component F v)) + 1"
        (* TODO later: maybe simplify proof *)
        by (metis (no_types, lifting) "3"(3) One_nat_def \<open>connected_component F u \<in> connected_components F\<close>
            \<open>connected_component F v \<in> connected_components F\<close> \<open>{{x, y} |x y. {x, y} \<subseteq> C \<and> {x, y} = e} = {{u, v}}\<close>
            card.empty card.insert card_Un_disjoint component_edges_disj component_edges_expr component_edges_subset
            edges_disj empty_iff finite.emptyI finite.insertI finite_subset insert.hyps(1))


      from connected_component_finite[OF insert(1) \<open>dblton_graph F\<close>] insert(6) 
        \<open>(connected_component F u) \<in> connected_components F\<close>
      have "finite (connected_component F u)" by blast
      from connected_component_finite[OF insert(1) \<open>dblton_graph F\<close>] insert(6) 
        \<open>(connected_component F v) \<in> connected_components F\<close>
      have "finite (connected_component F v)" by blast

      have "card C = card (connected_component F u) + card (connected_component F v)"
        using card_Un_disjoint[OF \<open>finite (connected_component F u)\<close> \<open>finite (connected_component F v)\<close>
            \<open>connected_component F u \<inter> connected_component F v = {}\<close>] a by blast
      also have "... =
        card (component_edges F (connected_component F u)) + 1 + 
        card (component_edges F (connected_component F v)) + 1"
        using IH[OF \<open>(connected_component F u) \<in> connected_components F\<close>]
          IH[OF \<open>(connected_component F v) \<in> connected_components F\<close>] by auto
      also have "... =
        card (component_edges (insert e F) C) + 1"
        using card_component_edges by auto
      finally show ?thesis by blast
    qed (auto simp add: in_CC_F)
  next
    case 4
    then show ?case by (auto simp add: in_CC_F)
  qed
qed


lemma connected_components_card:
  "has_no_cycle X \<Longrightarrow> \<forall>e \<in> X. \<exists>u v. e = {u, v} \<and> u \<noteq> v \<Longrightarrow> card (Vs X) = card X + card (connected_components X)"
proof-
  assume "has_no_cycle X" "\<forall>e \<in> X. \<exists>u v. e = {u, v} \<and> u \<noteq> v"
  then have "finite X" "X \<subseteq> G" "dblton_graph X"
    unfolding has_no_cycle_def unfolding dblton_graph_def
    using finite_E rev_finite_subset by auto
  have "\<forall>C \<in> connected_components X. finite C"
    unfolding connected_components_def using \<open>finite X\<close> \<open>\<forall>e \<in> X. \<exists>u v. e = {u, v} \<and> u \<noteq> v\<close>
    by (metis Vs_def connected_component_subs_Vs connected_components_def finite.emptyI finite_Union finite_insert finite_subset)
  then have "\<forall>C \<in> connected_components X. finite (component_edges X C)"
    unfolding component_edges_def using \<open>finite X\<close>
    by (smt (verit, best) finite_subset mem_Collect_eq subset_eq)
  then have "\<forall>A \<in> (components_edges X). finite A"
    unfolding components_edges_def by auto

  have "finite (connected_components X)"
    unfolding connected_components_def
    by (metis Vs_def \<open>\<forall>e\<in>X. \<exists>u v. e = {u, v} \<and> u \<noteq> v\<close> \<open>finite X\<close> connected_components_def
        finite.emptyI finite_Union finite_con_comps finite_insert)
  then have "finite (components_edges X)"
    unfolding components_edges_def by auto

  from \<open>\<forall>A \<in> (components_edges X). finite A\<close>
  have "\<forall>A \<in> (components_edges X). finite (id A)"
    unfolding components_edges_def by auto
  have disj: "\<forall>C \<in> components_edges X. \<forall>C' \<in> components_edges X. C \<noteq> C' \<longrightarrow> id C \<inter> id C' = {}"
    unfolding components_edges_def using component_edges_disj by auto

  have component_edges_distinct:
    "\<forall>C \<in> connected_components X. \<forall>C' \<in> connected_components X. C \<noteq> C' \<longrightarrow> component_edges X C \<noteq> component_edges X C'"
    unfolding components_edges_def using component_edges_disj[where G = "X"] component_edges_nonempty[OF \<open>dblton_graph X\<close>]
    by fastforce

  have cards_geq_1:
    "\<forall>C \<in> connected_components X. card C \<ge> 1"
    using \<open>\<forall>C\<in>connected_components X. finite C\<close> connected_comp_nempty card_gt_0_iff less_eq_Suc_le by auto

  have "disjoint (connected_components X)"
    unfolding disjoint_def
    by (simp add: connected_components_disj)
  have card_Vs_X:
    "card (Vs X) = (\<Sum>C \<in> connected_components X. card C)"
    using Union_connected_components[OF \<open>dblton_graph X\<close>] card_Union_disjoint \<open>\<forall>C\<in>connected_components X. finite C\<close> \<open>disjoint (connected_components X)\<close>
    by metis

  from has_no_cycle_connected_component_card[OF \<open>finite X\<close>] \<open>\<forall>e \<in> X. \<exists>u v. e = {u, v} \<and> u \<noteq> v\<close>
    \<open>has_no_cycle X\<close>
  have "\<forall>C \<in> connected_components X. card C = card (component_edges X C) + 1" by blast
  then have cards_CCs: "\<forall>C \<in> connected_components X. card C - 1 = card (component_edges X C)"
    using cards_geq_1 by simp

  from \<open>dblton_graph X\<close> have "X = X \<inter> {{x, y} |x y. True}" by fast
  with component_edges_partition have "\<Union> (components_edges X) = X" by fastforce
  then have "card X = card (\<Union> (components_edges X))" by auto
  also have "... = (\<Sum>C \<in> components_edges X. card C)"
    using card_UN_disjoint[OF \<open>finite (components_edges X)\<close>
        \<open>\<forall>A \<in> (components_edges X). finite (id A)\<close> disj] by auto
  also have "... = (\<Sum>C \<in> connected_components X. card (component_edges X C))"
    unfolding components_edges_def using component_edges_distinct
    by (smt (verit, best) mem_Collect_eq sum.eq_general)
  also have "... = (\<Sum>C \<in> connected_components X. card C - 1)"
    using cards_CCs by auto
  also have "... = (\<Sum>C \<in> connected_components X. card C) - card (connected_components X)"
    using cards_geq_1 sum_subtractf_nat by fastforce
  also have "... = card (Vs X) - card (connected_components X)"
    using card_Vs_X by simp
  finally have "card X = card (Vs X) - card (connected_components X)" .

  with cards_geq_1
  have "(\<Sum>C \<in> connected_components X. card C) \<ge> card (connected_components X)"
    using sum_mono by fastforce
  then have "card (Vs X) \<ge> card (connected_components X)"
    using card_Vs_X by auto
  with \<open>card X = card (Vs X) - card (connected_components X)\<close>
  show "card (Vs X) = card X + card (connected_components X)" by auto
qed

lemma reverse_pigeonhole:
  "finite X \<Longrightarrow> (f ` X) \<subseteq> Y \<Longrightarrow> card X < card Y \<Longrightarrow> \<exists>y \<in> Y. \<forall>x \<in> X. y \<noteq> f x"
  by (metis imageI less_le_not_le subset_eq surj_card_le)

lemma decycle_edge_path: 
  "(insert {v, w} Y) \<subseteq> G \<Longrightarrow> decycle (insert {v, w} Y) u p \<Longrightarrow> {v, w} \<in> set p \<Longrightarrow> \<exists>q. walk_betw Y w q v"
proof-
  assume "(insert {v, w} Y) \<subseteq> G" "decycle (insert {v, w} Y) u p" "{v, w} \<in> set p"
  then have "epath (insert {v, w} Y) u p u" using decycle_def by metis
  from \<open>decycle (insert {v, w} Y) u p\<close> have "distinct p" using decycle_def by metis
  from \<open>decycle (insert {v, w} Y) u p\<close> have "length p > 2" using decycle_def by metis
  from \<open>epath (insert {v, w} Y) u p u\<close> have "u \<in> Vs (insert {v, w} Y)"
    by (metis epath.elims(2) \<open>2 < length p\<close> edges_are_Vs less_or_eq_imp_le
        linorder_not_less list.size(3) pos2)

  from graph_abs_subset[OF \<open>(insert {v, w} Y) \<subseteq> G\<close>]
  have "graph_abs (insert {v, w} Y)" by simp
  from graph_abs_subset \<open>(insert {v, w} Y) \<subseteq> G\<close>
  have "graph_abs Y" by simp
  from graph_abs.map_undirected_epath_to_awalk[OF \<open>graph_abs (insert {v, w} Y)\<close> \<open>epath (insert {v, w} Y) u p u\<close>]
  have "map undirected (epath_to_awalk u p) = p" by blast
      (* Note: Probably need to generalise E assumption (or use general statement from outside locale) *)
  from graph_abs.epath_imp_awalk[OF \<open>graph_abs (insert {v, w} Y)\<close> \<open>epath (insert {v, w} Y) u p u\<close>
      \<open>u \<in> Vs (insert {v, w} Y)\<close>]
  have "awalk (graph_abs.D (insert {v, w} Y)) u (epath_to_awalk u p) u" by blast
  then have "set (epath_to_awalk u p) \<subseteq> graph_abs.D (insert {v, w} Y)"
    unfolding awalk_def by blast

  have "length (epath_to_awalk u p) = length p"
    by (metis \<open>map undirected (epath_to_awalk u p) = p\<close> length_map)
  with \<open>length p > 2\<close>
  have "epath_to_awalk u p \<noteq> []" by auto

  from \<open>{v, w} \<in> set p\<close>
  have "\<exists>i. i < length p \<and> p ! i = {v, w}"
    by (simp add: in_set_conv_nth)
  then obtain i where "i < length p" "p ! i = {v, w}" by blast

  then have "p = take i p @ [{v, w}] @ drop (i + 1) p"
    by (metis Suc_eq_plus1 append.assoc append_take_drop_id hd_drop_conv_nth take_hd_drop)

  with \<open>distinct p\<close>
  have "{v, w} \<notin> set (take i p)"
    using not_distinct_conv_prefix by fastforce
  from \<open>p = take i p @ [{v, w}] @ drop (i + 1) p\<close> \<open>distinct p\<close>
  have "{v, w} \<notin> set (drop (i + 1) p)"
    by (metis append_Cons append_eq_append_conv2 distinct.simps(2) distinct_append self_append_conv)

  from \<open>map undirected (epath_to_awalk u p) = p\<close> \<open>i < length p\<close>
  have "undirected ((epath_to_awalk u p) ! i) = (p ! i)"
    by (metis list_update_id map_update nth_list_update_eq)
  with \<open>p ! i = {v, w}\<close> have "(epath_to_awalk u p) ! i = (v, w) \<or> (epath_to_awalk u p) ! i = (w, v)"
    using undirected_iff by auto


  with \<open>i < length p\<close> \<open>length (epath_to_awalk u p) = length p\<close>
  have "(epath_to_awalk u p) = take i (epath_to_awalk u p) @ [(epath_to_awalk u p) ! i] @ drop (i + 1) (epath_to_awalk u p)"
    by (metis add.commute append.assoc append_take_drop_id hd_drop_conv_nth plus_1_eq_Suc take_hd_drop)
  then obtain x y where
    awalk_decomp: "(epath_to_awalk u p) = take i (epath_to_awalk u p) @ [(x, y)] @ drop (i + 1) (epath_to_awalk u p)"
    by (metis rev_pair.cases)
  with \<open>(epath_to_awalk u p) = take i (epath_to_awalk u p) @ [(epath_to_awalk u p) ! i] @ drop (i + 1) (epath_to_awalk u p)\<close>
  have "(epath_to_awalk u p) ! i = (x, y)"
    by (metis append_same_eq list.inject same_append_eq)

  from awalk_decomp \<open>awalk (graph_abs.D (insert {v, w} Y)) u (epath_to_awalk u p) u\<close>
  have "awalk (graph_abs.D (insert {v, w} Y)) u (take i (epath_to_awalk u p)) x"
    by (metis awalk_Cons_iff awalk_append_iff fst_eqD)
  moreover have
    "awalk (graph_abs.D (insert {v, w} Y)) y (drop (i + 1) (epath_to_awalk u p)) u"
    using awalk_decomp \<open>awalk (graph_abs.D (insert {v, w} Y)) u (epath_to_awalk u p) u\<close>
    by (metis (mono_tags, lifting) append_Cons awalk_Cons_iff awalk_append_iff self_append_conv2 snd_conv)
  ultimately have
    "awalk (graph_abs.D (insert {v, w} Y)) y (drop (i + 1) (epath_to_awalk u p) @ take i (epath_to_awalk u p)) x"
    by auto

  have "map undirected (take i (epath_to_awalk u p)) = take i p"
    using take_map \<open>map undirected (epath_to_awalk u p) = p\<close> by metis
  then have "{v, w} \<notin> set (map undirected (take i (epath_to_awalk u p)))"
    using \<open>{v, w} \<notin> set (take i p)\<close> by auto
  moreover have "set (take i (epath_to_awalk u p)) \<subseteq> graph_abs.D (insert {v, w} Y)"
    using \<open>set (epath_to_awalk u p) \<subseteq> graph_abs.D (insert {v, w} Y)\<close>
    by (meson set_take_subset subset_trans)
  ultimately have "set (take i (epath_to_awalk u p)) \<subseteq> graph_abs.D Y"
    using \<open>graph_abs (insert {v, w} Y)\<close>
    by (smt (verit, best) graph_abs.edge_iff_edge_2 graph_abs_mono image_eqI insert_commute insert_iff
        list.set_map subrelI subset_iff subset_insertI undirected.simps)


  have "map undirected (drop (i + 1) (epath_to_awalk u p)) = drop (i + 1) p"
    using drop_map \<open>map undirected (epath_to_awalk u p) = p\<close> by metis
  then have "{v, w} \<notin> set (map undirected (drop (i + 1) (epath_to_awalk u p)))"
    using \<open>{v, w} \<notin> set (drop (i + 1) p)\<close> by auto
  moreover have "set (drop (i + 1) (epath_to_awalk u p)) \<subseteq> graph_abs.D (insert {v, w} Y)"
    using \<open>set (epath_to_awalk u p) \<subseteq> graph_abs.D (insert {v, w} Y)\<close>
    by (meson set_drop_subset subset_trans)
  ultimately have "set (drop (i + 1) (epath_to_awalk u p)) \<subseteq> graph_abs.D Y"
    using \<open>graph_abs (insert {v, w} Y)\<close>
    by (smt (verit, best) graph_abs.edge_iff_edge_2 graph_abs_mono image_eqI insert_commute insert_iff
        list.set_map subrelI subset_iff subset_insertI undirected.simps)

  from \<open>set (drop (i + 1) (epath_to_awalk u p)) \<subseteq> graph_abs.D Y\<close>
    \<open>set (take i (epath_to_awalk u p)) \<subseteq> graph_abs.D Y\<close>
  have "set (drop (i + 1) (epath_to_awalk u p) @ take i (epath_to_awalk u p)) \<subseteq> graph_abs.D Y"
    by auto

  have "set (map undirected (drop (i + 1) (epath_to_awalk u p) @ (take i (epath_to_awalk u p)))) \<subseteq>
    set (map undirected (drop (i + 1) (epath_to_awalk u p))) \<union> set (map undirected (take i (epath_to_awalk u p)))"
    by auto
  with \<open>{v, w} \<notin> set (map undirected (take i (epath_to_awalk u p)))\<close>
    \<open>{v, w} \<notin> set (map undirected (drop (i + 1) (epath_to_awalk u p)))\<close>
  have "{v, w} \<notin> set (map undirected (drop (i + 1) (epath_to_awalk u p) @ (take i (epath_to_awalk u p))))"
    by blast

  have "drop (i + 1) (epath_to_awalk u p) @ take i (epath_to_awalk u p) \<noteq> []"
    using \<open>length (epath_to_awalk u p) = length p\<close> \<open>length p > 2\<close> awalk_decomp
    by auto
  from awalk_hd_in_set[OF \<open>awalk (graph_abs.D (insert {v, w} Y)) y (drop (i + 1) (epath_to_awalk u p) @ take i (epath_to_awalk u p)) x\<close> this
      \<open>set (drop (i + 1) (epath_to_awalk u p) @ take i (epath_to_awalk u p)) \<subseteq> graph_abs.D Y\<close>]
  have "y \<in> dVs (graph_abs.D Y)" .

  with \<open>awalk (graph_abs.D (insert {v, w} Y)) y (drop (i + 1) (epath_to_awalk u p) @ take i (epath_to_awalk u p)) x\<close>
    \<open>set (drop (i + 1) (epath_to_awalk u p) @ take i (epath_to_awalk u p)) \<subseteq> graph_abs.D Y\<close>
  have "awalk (graph_abs.D Y) y (drop (i + 1) (epath_to_awalk u p) @ take i (epath_to_awalk u p)) x"
    unfolding awalk_def by blast
  from awalk_imp_vwalk[OF this]
  have "vwalk_bet (graph_abs.D Y) y (awalk_verts y (drop (i + 1) (epath_to_awalk u p) @ take i (epath_to_awalk u p))) x" .
  with graph_abs.walk_betw_iff_vwalk_bet[OF \<open>graph_abs Y\<close>]
  have "walk_betw Y y (awalk_verts y (drop (i + 1) (epath_to_awalk u p) @ take i (epath_to_awalk u p))) x"
    by blast
  moreover have "(x, y) = (v, w) \<or> (x, y) = (w, v)"
    using \<open>(epath_to_awalk u p) ! i = (x, y)\<close> \<open>(epath_to_awalk u p) ! i = (v, w) \<or> (epath_to_awalk u p) ! i = (w, v)\<close>
    by auto
  ultimately show "\<exists>q. walk_betw Y w q v"
    using walk_symmetric by fast
qed


lemma insert_edge_cycle_ex_walk_betw:
  assumes "X \<subseteq> G" "Y \<subseteq> G" "\<forall>x. x \<in> X - Y \<longrightarrow> (\<exists>u c. decycle (insert x Y) u c)" "\<nexists>u c. decycle Y u c"
  shows "walk_betw X u p v \<Longrightarrow> \<exists>q. walk_betw Y u q v"
proof (induction rule: induct_walk_betw)
  case (path1 v)
  from subset_edges_G[OF \<open>X \<subseteq> G\<close>]
  have "(\<forall>e \<in> X. \<exists>u v. e = {u, v} \<and> u \<noteq> v)" by simp
  with path1 have "\<exists>u. {u, v} \<in> X \<and> u \<noteq> v" unfolding Vs_def
    by (smt (verit) Union_iff empty_iff insert_commute insert_iff)
  then obtain u where "{u, v} \<in> X" "u \<noteq> v" by blast
  then consider (1) "{u, v} \<in> Y" | (2) "{u, v} \<in> X - Y" by blast
  then show ?case
  proof (cases)
    case 1
    then have "v \<in> Vs Y" by blast
    then show ?thesis by (meson walk_reflexive)
  next
    case 2
    with assms obtain w c where "decycle (insert {u, v} Y) w c" by blast
    with decycle_not_subset assms(4)
    have "\<not> set c \<subseteq> Y" by metis
    moreover have "set c \<subseteq> (insert {u, v} Y)" 
      using \<open>decycle (insert {u, v} Y) w c\<close> decycle_def epath_edges_subset by metis
    ultimately have "{u, v} \<in> set c" by blast
    have "(insert {u, v} Y) \<subseteq> G"
      using \<open>{u, v} \<in> X\<close> assms(1) assms(2) by blast
    from decycle_edge_path[OF this \<open>decycle (insert {u, v} Y) w c\<close> \<open>{u, v} \<in> set c\<close>]
    have "\<exists>q. walk_betw Y v q u" .
    then have "v \<in> Vs Y" by fastforce
    then show ?thesis
      by (meson walk_reflexive)
  qed
next
  case (path2 v v' vs b)
  then consider (1) "{v, v'} \<in> Y" | (2) "{v, v'} \<in> X - Y" by blast
  then show ?case
  proof (cases)
    case 1
    then have "walk_betw Y v [v, v'] v'"
      by (simp add: edges_are_walks)
    from walk_transitive[OF this] \<open>\<exists>q. walk_betw Y v' q b\<close>
    show ?thesis by auto
  next
    case 2
    with assms obtain w c where "decycle (insert {v, v'} Y) w c" by blast
    with decycle_not_subset assms(4)
    have "\<not> set c \<subseteq> Y" by metis
    moreover have "set c \<subseteq> (insert {v, v'} Y)" 
      using \<open>decycle (insert {v, v'} Y) w c\<close> decycle_def epath_edges_subset by metis
    ultimately have "{v, v'} \<in> set c" by blast
    have "(insert {v, v'} Y) \<subseteq> G"
      using assms(1) assms(2) path2.hyps(1) by blast
    have "\<exists>q. walk_betw Y v q v'"
      using decycle_edge_path[OF \<open>(insert {v, v'} Y) \<subseteq> G\<close>
          \<open>decycle (insert {v, v'} Y) w c\<close> \<open>{v, v'} \<in> set c\<close>] walk_symmetric
      by fast
    with path2(3) show ?thesis using walk_transitive by fast
  qed
qed

lemma card_connected_components':
  "X \<subseteq> G \<Longrightarrow> finite X \<Longrightarrow> \<forall>e\<in>X. \<exists>u v. e = {u, v} \<and> u \<noteq> v \<Longrightarrow> finite V \<Longrightarrow> 
    card (connected_components' V X) = card (connected_components X) + card (V - Vs X)"
proof-
  assume "X \<subseteq> G" "finite X" "\<forall>e\<in>X. \<exists>u v. e = {u, v} \<and> u \<noteq> v" "finite V"
  then have "dblton_graph X" unfolding dblton_graph_def by simp
  from Union_connected_components[OF this]
  have "connected_components X \<inter> ((\<lambda>v. {v}) ` (V - (Vs X))) = {}"
    by (smt (verit) DiffD2 UnionI disjoint_iff imageE singletonI)

  have "card ((\<lambda>v. {v}) ` (V - (Vs X))) = card (V - Vs X)"
    by (simp add: card_image)

  have "finite (connected_components X)"
    unfolding connected_components_def
    by (metis Vs_def \<open>\<forall>e\<in>X. \<exists>u v. e = {u, v} \<and> u \<noteq> v\<close> \<open>finite X\<close> connected_components_def finite.emptyI finite_Union finite_con_comps finite_insert)
  have "finite ((\<lambda>v. {v}) ` (V - (Vs X)))"
    using \<open>finite V\<close> by auto

  show "card (connected_components' V X) = card (connected_components X) + card (V - Vs X)"
    unfolding connected_components'_def using card_Un_disjoint[OF \<open>finite (connected_components X)\<close>
        \<open>finite ((\<lambda>v. {v}) ` (V - (Vs X)))\<close> \<open>connected_components X \<inter> ((\<lambda>v. {v}) ` (V - (Vs X))) = {}\<close>]
      \<open>card ((\<lambda>v. {v}) ` (V - (Vs X))) = card (V - Vs X)\<close> by simp
qed



lemma has_no_cycle_augment:
  "has_no_cycle X \<Longrightarrow> has_no_cycle Y \<Longrightarrow> card X = Suc (card Y) \<Longrightarrow> \<exists>x. x \<in> (X - Y) \<and> has_no_cycle (insert x Y)"
proof (rule ccontr, goal_cases)
  case 1
  then have "\<forall>x. x \<in> X - Y \<longrightarrow> \<not>has_no_cycle (insert x Y)" by blast
  moreover have "\<forall>x. x \<in> X - Y \<longrightarrow> (insert x Y) \<subseteq> G"
    using \<open>has_no_cycle X\<close> \<open>has_no_cycle Y\<close> unfolding has_no_cycle_def by auto
  ultimately have "\<forall>x. x \<in> X - Y \<longrightarrow> (\<exists>u c. decycle (insert x Y) u c)"
    unfolding has_no_cycle_def by simp

  from \<open>has_no_cycle X\<close> have "X \<subseteq> G" unfolding has_no_cycle_def by auto
  from \<open>has_no_cycle Y\<close> have "Y \<subseteq> G" unfolding has_no_cycle_def by auto
  from \<open>X \<subseteq> G\<close> finite_E have "finite X" by (simp add: finite_subset)
  from \<open>Y \<subseteq> G\<close> finite_E have "finite Y" by (simp add: finite_subset)
  from subset_edges_G[OF \<open>X \<subseteq> G\<close>] have "\<forall>e \<in> X. \<exists>u v. e = {u, v} \<and> u \<noteq> v" by simp
  then have "dblton_graph X" unfolding dblton_graph_def by blast
  from subset_edges_G[OF \<open>Y \<subseteq> G\<close>] have "\<forall>e \<in> Y. \<exists>u v. e = {u, v} \<and> u \<noteq> v" by simp
  then have "dblton_graph Y" unfolding dblton_graph_def by blast

  let ?V = "Vs G"
  have "finite ?V" using graph by blast
  have "Vs X \<subseteq> ?V" unfolding Vs_def using \<open>has_no_cycle X\<close> unfolding has_no_cycle_def by auto
  have "Vs Y \<subseteq> ?V" unfolding Vs_def using \<open>has_no_cycle Y\<close> unfolding has_no_cycle_def by auto

  from \<open>has_no_cycle Y\<close> have "(\<nexists>u c. decycle Y u c)"
    unfolding has_no_cycle_def by simp

(* Every CC of X is a subset of a CC of Y *)
  have ex_CC_subset:
    "\<forall>C \<in> connected_components' ?V X. \<exists>C' \<in> connected_components' ?V Y. C \<subseteq> C'"
  proof 
    fix C
    assume "C \<in> connected_components' ?V X"
    then consider (a) "C \<in> connected_components X" | (b) "\<exists>v \<in> ?V - (Vs X). C = {v}"
      unfolding connected_components'_def by blast
    then show "\<exists>C' \<in> connected_components' ?V Y. C \<subseteq> C'"
    proof (cases)
      case a
      have "\<forall>u \<in> C. \<forall>v \<in> C. connected_component Y u = connected_component Y v \<and> u \<in> Vs Y"
      proof (rule ballI, rule ballI)
        fix u v
        assume "u \<in> C" "v \<in> C"
        with \<open>C \<in> connected_components X\<close>
        have "\<exists>p. walk_betw X u p v" 
          by (meson same_con_comp_walk)
        then obtain p where "walk_betw X u p v" by blast
        from insert_edge_cycle_ex_walk_betw[OF \<open>X \<subseteq> G\<close> \<open>Y \<subseteq> G\<close> \<open>\<forall>x. x \<in> X - Y \<longrightarrow> (\<exists>u c. decycle (insert x Y) u c)\<close>
            \<open>(\<nexists>u c. decycle Y u c)\<close> this]
        obtain q where "walk_betw Y u q v" by blast
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
    "\<forall>C \<in> connected_components' ?V X. \<exists>!C' \<in> connected_components' ?V Y. C \<subseteq> C'"
  proof
    fix C
    assume "C \<in> connected_components' ?V X"
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
  have "\<forall>C \<in> connected_components' ?V X. ?f C \<in> connected_components' ?V Y \<and> C \<subseteq> ?f C"
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
    then obtain C' where "C' \<in> (connected_components' ?V Y)" "\<forall>C \<in> (connected_components' ?V X). C' \<noteq> ?f C"
      by blast
    with \<open>finite (connected_components' ?V X)\<close> ex_CC_subset_unique
    have "\<forall>C \<in> (connected_components' ?V X). \<not>C \<subseteq> C'"
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
      with \<open>\<forall>C \<in> (connected_components' ?V X). \<not>C \<subseteq> C'\<close> \<open>C \<in> (connected_components' ?V X)\<close>
      have "C' \<noteq> C''" by blast

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
    using connected_components_card[OF \<open>has_no_cycle X\<close> \<open>\<forall>e \<in> X. \<exists>u v. e = {u, v} \<and> u \<noteq> v\<close>] by auto
  also have "... = card X + card (connected_components' ?V X)"
    using card_connected_components'[OF \<open>X \<subseteq> G\<close> \<open>finite X\<close> \<open>\<forall>e \<in> X. \<exists>u v. e = {u, v} \<and> u \<noteq> v\<close> \<open>finite ?V\<close>] by auto
  finally have card_V_1: "card ?V = card X + card (connected_components' ?V X)" .

  have "card ?V = card (Vs Y) + card (?V - Vs Y)"
    by (metis Diff_disjoint Diff_partition \<open>Vs Y \<subseteq> Vs G\<close> card_Un_disjoint finite_Diff2 graph infinite_super)
  also have "... = card Y + card (connected_components Y) + card (?V - Vs Y)"
    using connected_components_card[OF \<open>has_no_cycle Y\<close> \<open>\<forall>e \<in> Y. \<exists>u v. e = {u, v} \<and> u \<noteq> v\<close>] by auto
  also have "... = card Y + card (connected_components' ?V Y)"
    using card_connected_components'[OF \<open>Y \<subseteq> G\<close> \<open>finite Y\<close> \<open>\<forall>e \<in> Y. \<exists>u v. e = {u, v} \<and> u \<noteq> v\<close> \<open>finite ?V\<close>] by auto
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
( has_no_cycle X \<and> (\<forall>v \<in> Vs G. \<forall>w \<in> Vs G. {v, w} \<in> G \<longrightarrow> reachable X v w))"

lemma spanning_forest_alternative:
  "is_spanning_forest X = (has_no_cycle X \<and> (\<forall>v \<in> Vs G. \<forall>w \<in> Vs G. reachable G v w \<longrightarrow> reachable X v w))"
proof(unfold is_spanning_forest_def, rule, goal_cases)
  case 1
  hence prem: "v\<in>Vs G \<Longrightarrow> w\<in>Vs G \<Longrightarrow> {v, w} \<in> G \<Longrightarrow> Undirected_Set_Graphs.reachable X v w" for v w by auto
  have "walk_betw G v p w \<Longrightarrow> Undirected_Set_Graphs.reachable X v w" for v w p 
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
      by (simp add: Undirected_Set_Graphs.reachable_refl reachable_in_Vs(2))
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
  have "(\<forall>v \<in> Vs G. \<forall>w \<in> Vs G. {v, w} \<in> G \<longrightarrow> reachable X v w)"
  proof (rule ballI, rule ballI, rule impI)
    fix v w
    assume "v \<in> Vs G " "w \<in> Vs G" "{v, w} \<in> G"
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



context Pair_Graph_U_Specs
begin

context
  fixes G::'adjmap
  assumes pair_graph_u_inv: "pair_graph_u_invar G"
begin


lemma ugraph_dblton_graph:
  "dblton_graph (ugraph_abs G)"
  unfolding ugraph_abs_def dblton_graph_def using graph_irreflexive[OF pair_graph_u_inv] by blast

lemma ugraph_finite:
  "finite (Vs (ugraph_abs G))"
  unfolding ugraph_abs_def Vs_def using invar_finite_vertices[OF pair_graph_u_inv] unfolding dVs_def digraph_abs_def
  by simp

lemma graph_abs_ugraph:
  "graph_abs (ugraph_abs G)"
  apply (simp add: graph_abs_def)
  using ugraph_dblton_graph ugraph_finite by force

(*
interpretation ugraph_abs_inst: graph_abs
  where E = "ugraph_abs G"
  apply (simp add: graph_abs_def)
  using ugraph_edges ugraph_finite by auto
*)




lemma ugraph_abs_digraph_abs: "graph_abs.D (ugraph_abs G) = digraph_abs G"
  unfolding graph_abs.D_def ugraph_abs_def digraph_abs_def
proof-
  have 1: "{u, v} \<in> {{u, v} |u v. v \<in>\<^sub>G \<N>\<^sub>G G u} \<longleftrightarrow> u \<in>\<^sub>G (\<N>\<^sub>G G v) \<or> v \<in>\<^sub>G (\<N>\<^sub>G G u)" for u v
    using  doubleton_eq_iff[of u v] by auto
      (*  using isin_neighborhood_set_edge[OF pair_graph_u_inv] set_edge_isin_neighborhood[OF pair_graph_u_inv] by auto
*)
  have "graph_abs.D {{u, v} |u v. v \<in>\<^sub>G \<N>\<^sub>G G u} = {(u, v) |u v. {u, v} \<in> {{u, v} |u v. v \<in>\<^sub>G \<N>\<^sub>G G u}}"
    using graph_abs.D_def[OF graph_abs_ugraph] ugraph_abs_def by simp
  also have "... = {(u, v) |u v. v \<in>\<^sub>G \<N>\<^sub>G G u} \<union> {(u, v) |u v. u \<in>\<^sub>G \<N>\<^sub>G G v}"
    using 1 by auto
  also have "... = {(u, v) |u v. v \<in>\<^sub>G \<N>\<^sub>G G u}"
    using graph_symmetric[OF pair_graph_u_inv] by blast
  finally show "graph_abs.D {{u, v} |u v. v \<in>\<^sub>G \<N>\<^sub>G G u} = {(u, v). v \<in>\<^sub>G \<N>\<^sub>G G u}" by simp
qed

lemma cycle_equivalence:
  "(\<exists>c. cycle' (digraph_abs G) c) = (\<exists>u c. decycle (ugraph_abs G) u c)"
  using graph_abs.cycle'_iff_decycle[OF graph_abs_ugraph] ugraph_abs_digraph_abs
  by simp


end
  (*
lemma ex_graph_impl_ugraph_abs:
  "graph_abs G \<Longrightarrow> \<exists>G_impl. pair_graph_u_invar G_impl \<and> ugraph_abs G_impl = G"
  sorry
*)
end

locale undirected_multigraph_spec =
  fixes to_dbltn::"'e \<Rightarrow> 'v set" and E::"'e set"
begin

definition "G = to_dbltn ` E"
definition decycle_multi :: "'e set \<Rightarrow> 'v \<Rightarrow> 'e list \<Rightarrow> bool" where
  "decycle_multi X u p = ((epath (to_dbltn ` X) u (map to_dbltn p) u 
                            \<and> set p \<subseteq> X \<and> length p \<ge> 2 \<and> distinct p))"

definition reachable_multi where   
  "reachable_multi X u v = (\<exists>p. walk_betw G u p v \<and> 
                (\<forall> e \<in> set (edges_of_path p). \<exists> e' \<in> X. to_dbltn e' = e))"

definition "has_no_cycle_multi X = ( X \<subseteq> E \<and> (\<nexists>u c. decycle_multi X u c))"

definition "is_spanning_forest_multi X = 
( has_no_cycle_multi X \<and> (\<forall>v w. reachable_multi E v w 
                \<longrightarrow> reachable_multi X v w))"

end

locale undirected_multigraph = undirected_multigraph_spec 
  where to_dbltn = to_dbltn and E = E for 
    to_dbltn::"'e \<Rightarrow> 'v set"  and E::"'e set" +
  assumes to_dbltn: "\<And> e. e \<in> E \<Longrightarrow> \<exists> u v.  to_dbltn e = {u, v} \<and> u \<noteq> v"
    and    finite_edges: "finite E"
begin

lemma edges_of_path_to_multigraph_path:"set (edges_of_path p) \<subseteq> to_dbltn ` X \<Longrightarrow> \<exists> p'. map to_dbltn p' = edges_of_path p \<and> set p' \<subseteq> X"
proof(induction p rule: edges_of_path.induct)
  case (3 v v' l)
  then obtain p' where "map to_dbltn p' = edges_of_path (v' # l)" "set p' \<subseteq> X" by auto
  moreover obtain e where "to_dbltn e = {v, v'}" "e \<in> X"using 3(2) by auto
  ultimately have  "map to_dbltn (e#p') = edges_of_path (v#v' # l)" "set (e#p') \<subseteq> X" by auto
  then show ?case by blast
qed auto

lemma  edges_to_path_split_by_edge: 
  assumes "to_dbltn e \<in> set (edges_of_path q)" "to_dbltn e = {a, b}" 
  shows "\<exists> q1 q2. q = q1@[a, b]@ q2 \<or> q = q1@[b, a]@ q2"
  using assms(1)
proof(induction q rule: edges_of_path.induct)
  case (3 x y rest)
  show ?case 
  proof(cases "to_dbltn e = {x, y}")
    case True
    hence "x # y # rest = Nil @ [a, b] @ rest \<or>
                 x # y # rest = Nil @ [b, a] @ rest"
      using assms(2) by fastforce
    thus ?thesis by auto
  next
    case False
    hence "to_dbltn e \<in> set (edges_of_path (y # rest))" 
      using 3(2) by simp
    then obtain q1 q2 where "y # rest = q1 @ [a, b] @ q2 \<or>
                       y # rest = q1 @ [b, a] @ q2" 
      using "3.IH" by blast
    hence  "\<exists> q2. x#y # rest = x#q1 @ [a, b] @ q2 \<or>
                       x#y # rest = x#q1 @ [b, a] @ q2" by auto
    then show ?thesis 
      by(auto intro!: exI[of "\<lambda> q1a. \<exists> q2a. _ q1a q2a" "x#q1"]) 
  qed
qed auto

lemma decycle_multi_split:

assumes "C = C1@[e]@C2"
  "decycle_multi X u C" 
  "to_dbltn e ={x, y}" 
shows "\<exists> d \<in> set C. x \<in> {x, y} \<inter> to_dbltn d  \<and> d \<noteq> e"
proof-
  have epath: "epath (to_dbltn ` X) u (map to_dbltn C) u" and distinctC:"distinct C"
    using assms(2) decycle_multi_def by blast+
  have "epath (to_dbltn ` X) u (map to_dbltn ((C1@[e]@C2)@(C1@[e]@C2)@(C1@[e]@C2))) u"
    apply(subst map_append)+
    apply(rule epath_append[OF epath[simplified assms(1) map_append]])+
    by(rule epath[simplified assms(1) map_append])
  hence big_epath:"epath (to_dbltn ` X) u (map to_dbltn (C1@[e]@C2@C1@[e]@C2@C1@[e]@C2)) u" by simp
  have middle_list_rewrite:"xs@[x, y, z]@ys = ((xs@[x])@[y] @(z#ys))" for xs ys x y z by auto
  have "\<exists>x y. to_dbltn e = {x, y} \<and>
      x \<noteq> y \<and>
      epath (to_dbltn ` X) u
       (butlast (map to_dbltn (C1 @ [e] @ C2 @ C1)) @ [last (map to_dbltn (C1 @ [e] @ C2 @ C1))]) x \<and>
      epath (to_dbltn ` X) y
       ([hd (map to_dbltn (C2 @ C1 @ [e] @ C2))] @ tl (map to_dbltn (C2 @ C1 @ [e] @ C2))) u \<and>
      x \<in> last (map to_dbltn (C1 @ [e] @ C2 @ C1)) \<inter> to_dbltn e \<and>
      y \<in> to_dbltn e \<inter> hd (map to_dbltn (C2 @ C1 @ [e] @ C2))"
    apply(rule epath_find_splitter_advanced)
    apply(subst middle_list_rewrite)
    apply(subst append_butlast_last_id)
    subgoal by simp
    apply(subst hd_Cons_tl)
    subgoal by simp
    using big_epath by auto
  then obtain x' y' where x'_y'_prop:"to_dbltn e = {x', y'}" "x' \<noteq> y'"
    "epath (to_dbltn ` X) u (map to_dbltn (C1 @ [e] @ C2 @ C1)) x'"
    "epath (to_dbltn ` X) y' (map to_dbltn (C2 @ C1 @ [e] @ C2)) u"
    "x' \<in> last (map to_dbltn (C1 @ [e] @ C2 @ C1)) \<inter> to_dbltn e"
    "y' \<in> to_dbltn e \<inter> hd (map to_dbltn (C2 @ C1 @ [e] @ C2))"
    apply(subst (asm) append_butlast_last_id) 
    subgoal by simp
    by force
  have x'_y'_are:"(x' = x \<and> y' = y)\<or> (y' = x \<and> x' = y)" 
    using assms(3) x'_y'_prop(1) by force
  have C_rest_not_empty: "C2 @ C1 \<noteq> []" 
    using assms(1) assms(2) decycle_multi_def by force
  have pred_e_not_e:"last (C1 @ [e] @ C2 @ C1) \<noteq> e" 
    using last_appendR[OF C_rest_not_empty] last_in_set[OF C_rest_not_empty] assms(1) distinctC 
    by (auto intro: eq_neq_eq_imp_neq[of _ "last ((C1 @ [e]) @ (C2 @ C1))", OF _ _ refl])
  have succ_e_not_e:"hd (C2 @ C1 @ [e] @ C2) \<noteq> e" 
    using hd_append2[OF C_rest_not_empty] hd_in_set[OF C_rest_not_empty] assms(1) distinctC 
    by (auto intro: eq_neq_eq_imp_neq[of _ "last ((C1 @ [e]) @ (C2 @ C1))", OF _ _ refl])
  show ?thesis
  proof(cases rule: disjE[OF x'_y'_are])
    case 1
    have "x \<in> {x, y} \<inter> to_dbltn (last (C1 @ [e] @ C2 @ C1))" 
      using "1"  last_map[of _ to_dbltn]  x'_y'_prop(5) by blast
    moreover have "last (C1 @ [e] @ C2 @ C1) \<in> set C" 
      using  Un_iff last_in_set[OF C_rest_not_empty] set_append 
      by (subst last_appendR)(auto simp add:  assms(1) last_appendR[OF  C_rest_not_empty])
    ultimately show ?thesis
      using pred_e_not_e
      by(auto intro!: bexI[of _ "last ( (C1 @ [e] @ C2 @ C1))"])
  next
    case 2
    have "x \<in> {x, y} \<inter> hd (map to_dbltn (C2 @ C1 @ [e] @ C2))" 
      using 2 last_map[of _ to_dbltn]  x'_y'_prop(6) by blast
    hence "x \<in>  to_dbltn (hd (C2 @ C1 @ [e] @ C2))"
      by(subst (asm) list.map_sel(1)) auto
    moreover have "hd (C2 @ C1 @ [e] @ C2) \<in> set C" 
      using  Un_iff last_in_set[OF C_rest_not_empty] set_append 
      by (simp add: assms(1) hd_append)
    ultimately show ?thesis
      using succ_e_not_e
      by(auto intro!: bexI[of _ "hd (C2 @ C1 @ [e] @ C2)"])
  qed
qed

interpretation graph_abs_interpretation: graph_abs where G = G
  using  finite_edges finite_imageI imageE to_dbltn
  by(auto intro!: to_dbltn 
      simp add: graph_abs_def dblton_graph_def dblton_graph_finite_Vs[symmetric] G_def)

lemma graph: "graph_invar G"
  by (simp add: local.graph_abs_interpretation.graph)

lemma decycle_multi_subset:
  "decycle_multi E' u p \<Longrightarrow> E' \<subseteq> G' \<Longrightarrow> decycle_multi G' u p"
  unfolding decycle_multi_def using epath_subset 
  by (metis image_mono subset_eq)

lemma has_no_cycle_multi_to_dbltn_inj: "has_no_cycle_multi X \<Longrightarrow>inj_on to_dbltn  X"
proof(unfold  has_no_cycle_multi_def 
    decycle_multi_def  inj_on_def, rule ccontr, goal_cases)
  case 1
  then obtain x y where xy_prop:"x \<in> X" "y \<in> X" "to_dbltn x = to_dbltn y" "x \<noteq> y"
    by auto
  then obtain u v where uv_prop:"to_dbltn x = {u, v}"  "u \<noteq> v"
    using  "1"(1)  to_dbltn[of x]by blast
  define p where "p = [x,y]"
  have " epath (to_dbltn ` X) u (map to_dbltn p) u"
    using xy_prop uv_prop by(auto simp add: p_def intro!:  exI[of _ v])
  moreover have " 2 \<le> length p "
    by(simp add: p_def)
  moreover have "distinct p"
    using xy_prop by(simp add: p_def)
  moreover have "set p \<subseteq> X" 
    by (simp add: p_def xy_prop(1) xy_prop(2))
  ultimately show ?case 
    using 1 by simp
qed

lemma has_no_cycle_multi_to_has_no_cycle:
  assumes "has_no_cycle_multi X" 
  shows "graph_abs_interpretation.has_no_cycle (to_dbltn ` X)"
  unfolding graph_abs_interpretation.has_no_cycle_def
proof(insert assms, unfold  has_no_cycle_multi_def decycle_def
    decycle_multi_def G_def, rule ccontr, goal_cases)
  case 1
  then obtain u p where up_prop:"epath (to_dbltn ` X) u p u" "2 < length p"
    "distinct p" by auto
  hence "set p \<subseteq> to_dbltn ` X"
    by (simp add: epath_edges_subset)
  hence "\<exists> q. p = map to_dbltn q \<and> set q \<subseteq> X"
  proof(induction p)
    case (Cons a p)
    then obtain q where "p = map to_dbltn q"  "set q \<subseteq> X" by auto
    moreover obtain aa where "a = to_dbltn aa" "aa \<in> X"
      using Cons by auto
    ultimately have "a # p = map to_dbltn (aa#q)" "set (aa # q) \<subseteq> X "
      by auto
    then show ?case 
      by(force intro: exI[of _ "aa#q"])
  qed auto
  then obtain q where pq_prop: "p = map to_dbltn q" "set q \<subseteq> X"by auto
  moreover  hence " epath (to_dbltn ` X) u (map to_dbltn q) u" 
    using up_prop  by auto
  moreover have "2 < length q"
    using pq_prop(1) up_prop(2) by auto
  moreover have " distinct q"
    using distinct_map pq_prop(1) up_prop(3) by blast
  ultimately show ?case 
    using 1(1) by auto
qed


lemma has_no_cycle_to_has_no_cycle_multi:
  "graph_abs_interpretation.has_no_cycle (to_dbltn ` X) \<Longrightarrow> 
inj_on to_dbltn X
\<Longrightarrow> X \<subseteq> E \<Longrightarrow>
 has_no_cycle_multi X"
  unfolding graph_abs_interpretation.has_no_cycle_def
proof(unfold  has_no_cycle_multi_def decycle_def
    decycle_multi_def G_def, rule ccontr, goal_cases)
  case 1
  note one = this
  then obtain u p where up_prop: " epath (to_dbltn ` X) u (map to_dbltn p) u"
    "2 \<le> length p" "distinct p" "set p \<subseteq> X"
    by auto
  moreover hence "distinct (map to_dbltn p)"
    using 1(2) epath_edges_subset[OF up_prop(1)] 
    by (simp add: subset_eq distinct_map inj_on_def) 
  moreover have "length p > 2"
  proof(rule ccontr, goal_cases)
    case 1
    hence "length p = 2" 
      using up_prop by simp
    then obtain e e' where pe:"p=[e, e']" 
      by (metis (no_types, opaque_lifting) One_nat_def Suc_1 Suc_length_conv length_0_conv)
    moreover then obtain a b  where "to_dbltn e= {a, b}" "a \<noteq> b" 
      using to_dbltn[of e] epath_edges_subset one(2)  up_prop(1) by fastforce
    moreover obtain c d where "to_dbltn e'= {c, d}" "c \<noteq> d" 
      using to_dbltn[of e'] epath_edges_subset one(2) pe up_prop(1) by fastforce
    ultimately have "to_dbltn e = to_dbltn e'"
      using up_prop(1) 
      by (clarsimp simp add: insert_commute)
    then show ?case 
      using one(2) pe up_prop(1)  \<open>distinct (map to_dbltn p)\<close> by auto
  qed
  ultimately show ?case 
    using 1 by auto
qed

lemma double_edge_is_cycle:
  assumes "e \<in> X" "e' \<in> X" "X \<subseteq> E" "to_dbltn e = to_dbltn e'" "e \<noteq> e'"
  shows"\<not> has_no_cycle_multi X"
proof-
  obtain u v where dbltn_e:"to_dbltn e = {u, v}" "u \<noteq> v"
    using to_dbltn[of e] assms by auto
  hence dbltn_e':"to_dbltn e' = {u, v}"
    using assms by simp
  define p where "p = [e,e']"
  hence epath_p:"epath (to_dbltn ` X) u (map to_dbltn p) u"
    apply (auto intro!: exI[of _ v])
    using dbltn_e dbltn_e' assms(1-3)
    by fastforce+
  moreover have "distinct p"
    using assms by(simp add: p_def)
  ultimately have " epath (to_dbltn ` X) u (map to_dbltn p) u
                    \<and> set p \<subseteq> X \<and> 2 \<le> length p \<and> distinct p"
    by(simp add: p_def assms(1,2))
  thus ?thesis
    by(auto simp add: has_no_cycle_multi_def decycle_multi_def)
qed

lemma has_no_cycle_to_has_no_cycle_multi_is:
  "(graph_abs_interpretation.has_no_cycle (to_dbltn ` X)\<and>  inj_on to_dbltn X \<and> X \<subseteq> E) =
 has_no_cycle_multi X"
  using has_no_cycle_multi_def has_no_cycle_multi_to_dbltn_inj
    has_no_cycle_multi_to_has_no_cycle has_no_cycle_to_has_no_cycle_multi 
  by auto


lemma has_no_cycle_multi_indep_subset_carrier:
  "has_no_cycle_multi X \<Longrightarrow> X \<subseteq> E"
  by (simp add: has_no_cycle_multi_def)

lemma empty_has_no_cycle_multi_indep:
  " has_no_cycle_multi {}" 
  by(auto simp add:has_no_cycle_multi_def decycle_multi_def)

lemma has_no_cycle_multi_indep_ex:
  "\<exists>X. has_no_cycle_multi X" 
  using empty_has_no_cycle_multi_indep by auto

lemma has_no_cycle_multi_indep_subset:
  "has_no_cycle_multi X \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> has_no_cycle_multi Y"
  using decycle_multi_subset
  by(unfold has_no_cycle_multi_def) blast

lemma has_no_cycle_multi_augment:
  assumes  "has_no_cycle_multi X" "has_no_cycle_multi Y"
    "card X = Suc (card Y)"
  shows "\<exists>x. x \<in> (X - Y) \<and> has_no_cycle_multi (insert x Y)"
proof-
  have nc_X:"graph_abs_interpretation.has_no_cycle (to_dbltn ` X)"
    using  has_no_cycle_multi_to_has_no_cycle assms(1) by simp
  moreover have nc_Y:"graph_abs_interpretation.has_no_cycle (to_dbltn ` Y)"
    using  has_no_cycle_multi_to_has_no_cycle assms(2) by simp
  moreover have "card (to_dbltn ` X) = Suc (card (to_dbltn ` Y))"
    using card_image[OF  has_no_cycle_multi_to_dbltn_inj] assms by simp
  ultimately obtain x where x_prop: "x \<in> (to_dbltn ` X) - (to_dbltn ` Y)" 
    "graph_abs_interpretation.has_no_cycle (insert x (to_dbltn ` Y))"
    using exE[OF graph_abs_interpretation.has_no_cycle_augment] by force
  then obtain e where e_prop:"e \<in> X - Y" "to_dbltn e = x" by auto
  moreover hence  "graph_abs_interpretation.has_no_cycle (to_dbltn ` (insert e Y))"
    using x_prop by simp
  moreover have "inj_on to_dbltn X"
    using has_no_cycle_multi_to_dbltn_inj assms(1) by simp
  moreover have "X \<subseteq> E"
    by (simp add: assms(1) has_no_cycle_multi_indep_subset_carrier)
  ultimately have  "has_no_cycle_multi (insert e Y)"
    using   assms(2) has_no_cycle_multi_indep_subset_carrier has_no_cycle_multi_to_dbltn_inj x_prop(1) 
    by (auto intro!: has_no_cycle_to_has_no_cycle_multi)
  then show ?thesis 
    using e_prop(1) by auto
qed

lemma graph_matroid_multi:
  "matroid E has_no_cycle_multi"
  apply standard
  using finite_edges has_no_cycle_multi_indep_subset_carrier has_no_cycle_multi_indep_ex 
    has_no_cycle_multi_indep_subset has_no_cycle_multi_augment
  by blast+

lemma graph_indep_system_multi:
  "indep_system E has_no_cycle_multi"
  using matroid.axioms(1)[OF graph_matroid_multi] .

lemma is_spanning_forest_multi_and_simple:"is_spanning_forest_multi X = 
(graph_abs_interpretation.is_spanning_forest (to_dbltn `X) \<and> inj_on to_dbltn X \<and> X \<subseteq> E)"
proof(rule, goal_cases)
  case 1
  note one = this
  hence "inj_on to_dbltn X" 
    by (simp add: has_no_cycle_multi_to_dbltn_inj is_spanning_forest_multi_def)
  moreover have "graph_abs_interpretation.is_spanning_forest (to_dbltn ` X)"
    unfolding graph_abs_interpretation.is_spanning_forest_def
  proof(rule, goal_cases)
    case 1
    then show ?case 
      using is_spanning_forest_multi_def one has_no_cycle_multi_to_has_no_cycle by blast
  next
    case 2
    then show ?case
    proof(rule, rule, rule, goal_cases)
      case (1 v w)
      then obtain e where "e \<in> E" "to_dbltn e = {v,w}"
        using G_def by auto
      hence "reachable_multi E v w" 
        by(force intro!: exI[of _  "[v, w]"] simp add: reachable_multi_def "1"(3) edges_are_walks)
      hence "reachable_multi X v w"
        using is_spanning_forest_multi_def one by blast
      then obtain p where p_rpop:"walk_betw G v p w"
        "(\<forall> e \<in> set (edges_of_path p). \<exists> e' \<in> X. to_dbltn e' = e)"
        using reachable_multi_def by auto
      moreover hence  "set (edges_of_path p) \<subseteq> to_dbltn ` X" by auto
      moreover have "walk_betw (set (edges_of_path p)) v p w"
      proof-
        have "v \<noteq> w" 
          using "1"(3) by fastforce
        hence "length p \<ge> 2"
          by (meson p_rpop(1) walk_betw_length)
        from  p_rpop(1)this show ?thesis 
          by (simp add: walk_in_edges_of_path)
      qed
      ultimately show ?case 
        by (meson reachableI walk_subset)
    qed
  qed
  moreover have "X \<subseteq> E"
    using has_no_cycle_multi_indep_subset_carrier one
    by (auto simp add:  is_spanning_forest_multi_def)
  ultimately show ?case by simp
next
  case 2
  have "has_no_cycle_multi X" 
    using 2 has_no_cycle_multi_indep_subset has_no_cycle_to_has_no_cycle_multi 
    by (force simp add:  graph_abs_interpretation.is_spanning_forest_def)
  moreover have "\<And> v w. reachable_multi E v w \<Longrightarrow> reachable_multi X v w"
  proof(goal_cases)
    case (1 v w)
    then obtain p where p_prop: " walk_betw G v p w" 
      "(\<forall>e\<in>set (edges_of_path p). \<exists>e'\<in>E. to_dbltn e' = e)"
      by(auto simp add: reachable_multi_def)
    moreover have "v \<in> Vs G"  "w \<in> Vs G" 
      using p_prop(1) by auto
    ultimately obtain q where  q_prop:"walk_betw (to_dbltn ` X) v q w"
      using 2
      by(unfold graph_abs_interpretation.spanning_forest_alternative, unfold reachable_def) blast 
    have X_in: "Vs (to_dbltn ` X) \<subseteq> Vs G" 
      by (simp add: "2" G_def Vs_subset image_mono)
    from q_prop show ?case 
      unfolding reachable_multi_def
    proof(induction _ v q w rule: induct_walk_betw)
      case (path1 v)
      then show ?case 
        using X_in graph_abs_interpretation.walk_reflexive' 
        by(auto intro!: exI[of _ "[v]"])
    next
      case (path2 v v' vs b)
      then obtain p where p_prop:
        "walk_betw G v' p b ""(\<forall>e\<in>set (edges_of_path p). \<exists>e'\<in>X. to_dbltn e' = e)"
        by auto
      hence "walk_betw G v (v#p) b" 
        apply(cases p)
        using p_prop(1) apply simp_all
        using "2"  graph_abs.walk_between_nonempty_path'(3)[OF  graph_abs_interpretation.graph_abs_axioms ]  path2.hyps(1) 
        by(subst walk_betw_cons)(fastforce intro:  edges_are_walks simp add: G_def)
      moreover have " (\<forall>e\<in>set (edges_of_path (v#p)). \<exists>e'\<in>X. to_dbltn e' = e)"
        using graph_abs_interpretation.walk_between_nonempty_path'(3)
          p_prop(1) p_prop(2) path2.hyps(1) by (cases p)fastforce+
      ultimately show ?case  by auto
    qed
  qed
  ultimately show ?case 
    unfolding is_spanning_forest_multi_def by auto
qed

lemma basis_imple_basis_multi:
  "(indep_system.basis G graph_abs_interpretation.has_no_cycle (to_dbltn ` X) \<and> inj_on to_dbltn X \<and> X \<subseteq> E)
 = indep_system.basis E has_no_cycle_multi X"
  unfolding indep_system.basis_def[OF graph_abs_interpretation.graph_indep_system]
    indep_system.basis_def[OF graph_indep_system_multi]
proof(rule, goal_cases)
  case 1
  hence all: "graph_abs_interpretation.has_no_cycle (to_dbltn ` X)"
    "(\<forall>x\<in>G - to_dbltn ` X. \<not> graph_abs_interpretation.has_no_cycle (insert x (to_dbltn ` X)))"
    "inj_on to_dbltn X" "X \<subseteq> E" by auto
  have "has_no_cycle_multi X" 
    using all has_no_cycle_to_has_no_cycle_multi by blast
  moreover have " (\<forall>x\<in>E - X. \<not> has_no_cycle_multi (insert x X))"
  proof(rule, goal_cases)
    case (1 e)
    show ?case
    proof(cases "to_dbltn e \<in> to_dbltn ` X")
      case True
      then show ?thesis 
        using 1  has_no_cycle_multi_to_dbltn_inj by auto
    next
      case False
      hence "to_dbltn e \<in> G - to_dbltn ` X"
        using 1 by (auto simp add: G_def)
      hence "\<not> graph_abs_interpretation.has_no_cycle (insert (to_dbltn e) (to_dbltn ` X))" 
        using all(2) by simp
      then show ?thesis 
        using has_no_cycle_multi_to_has_no_cycle by fastforce
    qed
  qed
  ultimately show ?case by simp
next
  case 2
  hence all: "has_no_cycle_multi X" 
    "(\<forall>x\<in>E - X. \<not> has_no_cycle_multi (insert x X))"
    by auto
  have "graph_abs_interpretation.has_no_cycle (to_dbltn ` X)"
    by (simp add: all(1) has_no_cycle_multi_to_has_no_cycle)
  moreover have "(\<forall>x\<in>G - to_dbltn ` X. \<not> graph_abs_interpretation.has_no_cycle (insert x (to_dbltn ` X)))"
  proof(rule, goal_cases)
    case (1 e)
    then obtain e' where "e' \<in> E" "to_dbltn e' = e" "e' \<notin> X"
      by (fastforce simp add: G_def)
    moreover hence "\<not> has_no_cycle_multi (insert e' X)" 
      by (simp add: all(2))
    ultimately show ?case 
      using "1"  all(1) has_no_cycle_multi_indep_subset_carrier 
        has_no_cycle_multi_to_dbltn_inj has_no_cycle_to_has_no_cycle_multi 
      by auto
  qed
  moreover have " inj_on to_dbltn X" 
    by (simp add: all(1) has_no_cycle_multi_to_dbltn_inj)
  moreover have " X \<subseteq> E"
    by (simp add: all(1) has_no_cycle_multi_indep_subset_carrier)
  ultimately show ?case 
    by simp
qed

term indep_system.basis 
term indep_system.basis_in

lemma spanning_forest_iff_basis_multi:
  "is_spanning_forest_multi X = indep_system.basis E has_no_cycle_multi X"
  by (simp add: basis_imple_basis_multi 
      is_spanning_forest_multi_and_simple graph_abs_interpretation.spanning_forest_iff_basis)

end
end