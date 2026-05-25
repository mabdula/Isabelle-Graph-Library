(*Authors: Mohammad Abdulaziz, Thomas Ammer, Adem Rimpapa,*)
theory Cycles
  imports Undirected_Set_Graphs Connected_Components
begin

section \<open>Cycles\<close>

definition decycle :: "'a set set \<Rightarrow> 'a \<Rightarrow> ('a set) list \<Rightarrow> bool" where
  "decycle G u p = (epath G u p u \<and> length p > 2 \<and> distinct p)"

lemma decycleE:
 "decycle G u p \<Longrightarrow> 
  (\<lbrakk>epath G u p u; length p > 2; distinct p\<rbrakk> \<Longrightarrow> P)
  \<Longrightarrow> P"
and decycleI:
  "\<lbrakk>epath G u p u; length p > 2; distinct p\<rbrakk> \<Longrightarrow> decycle G u p"
and decycleD:
   "decycle G u p \<Longrightarrow> epath G u p u"
   "decycle G u p \<Longrightarrow> length p > 2"
   "decycle G u p \<Longrightarrow> distinct p"
  by(auto simp add: decycle_def)

lemma decycle_subset:
  "\<lbrakk>decycle G u p; G \<subseteq> G'\<rbrakk> \<Longrightarrow> decycle G' u p"
  unfolding decycle_def using epath_subset by metis

lemma decycle_not_subset:
  "\<lbrakk>\<exists>u. decycle G u p; \<nexists>u. decycle G' u p\<rbrakk> \<Longrightarrow> \<not>set p \<subseteq> G'"
proof (rule ccontr, goal_cases)
  case 1
  then have "set p \<subseteq> G'" by blast
  from \<open>\<exists>u. decycle G u p\<close> decycle_def
    have "(\<exists>u. epath G u p u \<and> length p > 2 \<and> distinct p)"
    by metis
  then obtain u where "epath G u p u" "length p > 2" "distinct p"
    by blast

  with epath_subset_other_set[OF \<open>epath G u p u\<close> \<open>set p \<subseteq> G'\<close>] decycle_def
    have "decycle G' u p" by metis
  with \<open>\<nexists>u. decycle G' u p\<close> show ?case by blast
qed

lemma new_edge_in_decycle: "\<lbrakk>\<not> decycle T u C; decycle (insert e T) u C\<rbrakk> \<Longrightarrow> e \<in> set C" 
  using   epath_edges_subset epath_subset_other_set subset_insert
  by(fastforce simp add: decycle_def)

context graph_abs
begin

definition "has_no_cycle X = ( X \<subseteq> G \<and> (\<nexists>u c. decycle X u c))"

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
  "\<lbrakk>has_no_cycle X; Y \<subseteq> X\<rbrakk> \<Longrightarrow> has_no_cycle Y"
  apply (rule ccontr)
  using has_no_cycle_def decycle_subset
  by (metis dual_order.trans)

lemmas graph_abs_subset = graph_abs_mono[OF graph_abs_axioms]

lemma subset_edges_G:
  "\<lbrakk>X \<subseteq> G; e \<in> X\<rbrakk> \<Longrightarrow> \<exists>u v. e = {u, v} \<and> u \<noteq> v"
  using graph by blast

lemma set_aux:
  "S1 = S2 \<union> S3 \<Longrightarrow> S2 \<inter> S3 = {} \<Longrightarrow>
    ({x, y} \<subseteq> S1 \<longleftrightarrow> ({x, y} \<subseteq> S2 \<or> {x, y} \<subseteq> S3 \<or> (x \<in> S2 \<and> y \<in> S3) \<or> (x \<in> S3 \<and> y \<in> S2)))"
  by auto

lemma has_no_cycle_ex_unique_path:
  "\<lbrakk>(insert {u, v} X) \<subseteq> G; has_no_cycle (insert {u, v} X); {u, v} \<notin> X\<rbrakk> \<Longrightarrow> \<nexists>p. walk_betw X u p v"
proof (rule ccontr, goal_cases)
  case 1
  note one = this
  then obtain p where "walk_betw X u p v" by blast
  moreover have u_neq_v: "u \<noteq> v" 
     using "1"(1) by fastforce
  ultimately obtain q where q_prop: "walk_betw X u q v" "distinct q" "set q \<subseteq> set p"
    using walk_betw_different_verts_to_ditinct by force
  hence edges_q_in_X:"set (edges_of_path q) \<subseteq> X"
    by (simp add: path_edges_subset walk_between_nonempty_pathD(1))
  have length_q: "length q > 2"
  proof-
    have "length q \<ge> 2" 
      using  q_prop(1) u_neq_v 
      by (auto intro!: walk_betw_length)
    moreover have "length q = 2 \<Longrightarrow> False"
    proof(goal_cases)
      case 1
      hence "q = [u,v]" 
        by (auto intro!: q_prop(1) walk_betw_length_2_is)
      hence "{u, v} \<in> X" 
        using q_prop(1) walk_between_nonempty_pathD(1) by fastforce
      thus False 
        using one(3) by simp
    qed
    ultimately show ?thesis 
      by force
  qed
  obtain qq where q_split_first_off: "q=u#qq"
    using  q_prop(1) walk_betw_split_off_first by force
  have walk_betw_in_uv_X: "walk_betw (insert {u, v} X) u q v"
    by (auto intro: q_prop(1) subset_insertI walk_subset)
  hence walk_betw_v_v:"walk_betw (insert {u, v} X) v (v#q) v"
    by(auto intro!: walk_betw_Cons_first[of _ u])
  hence "epath (insert {u, v} X) v (edges_of_path (v # q)) v" 
    using "1"(1)  dblton_graph_subset graph 
    by(auto intro!: walk_betw_imp_epath)
  moreover have "2 < length (edges_of_path (v # q))"
    by(auto simp add: edges_of_path_length length_q)
  moreover have "distinct (edges_of_path (v # q))"
    using q_split_first_off edges_q_in_X  one(3) q_prop(2)
    by(auto intro!: distinct_edges_of_vpath simp add: insert_commute)
  ultimately have "decycle (insert {u, v} X) v (edges_of_path (v#q))"
    by(rule decycleI)
  thus False
    using has_no_cycle_def one(2) by fastforce
qed

lemma decycle_edge_path: 
  "\<lbrakk>(insert {v, w} Y) \<subseteq> G; decycle (insert {v, w} Y) u p; {v, w} \<in> set p\<rbrakk>
    \<Longrightarrow> \<exists>q. walk_betw Y w q v"
proof(goal_cases)
  case 1
  hence decycle_unfolded: "epath (insert {v, w} Y) u p u" "2 < length p" "distinct p"
    by(auto elim!: decycleE)
  have "v \<noteq> w"
    using "1"(1) by fastforce
  then obtain p1 p2 where p1p2: "p = p1 @ [{v, w}] @ p2"
   "(epath (insert {v, w} Y) u p1 v \<and> epath (insert {v, w} Y) w p2 u \<or>
    epath (insert {v, w} Y) u p1 w \<and> epath (insert {v, w} Y) v p2 u)"
    using epath_one_split[OF decycle_unfolded(1) 1(3)] by auto
  hence "\<exists> q. epath (insert {v, w} Y) w q v \<and> set q \<subseteq> set p - {{v, w}}" 
    using epath_append[of _ w p2 u p1 v]  decycle_unfolded(3)
          epath_append[of _ w "rev p1" u "rev p2" v] epath_rev 
    by fastforce
  then obtain q where "epath (insert {v, w} Y) w q v" "set q \<subseteq> set p - {{v, w}}" by auto
  moreover hence "set q \<subseteq> Y" 
    using epath_edges_subset by fast
  ultimately have "epath Y w q v"
    by (force intro: epath_subset_other_set)
  moreover hence "length q \<ge> 1" 
    using \<open>v \<noteq> w\<close> epath_non_empty by force
  ultimately obtain qv where "walk_betw Y w qv v" "q = edges_of_path qv"
    using epath_imp_walk_betw by force
  thus ?thesis 
    by auto
qed

lemma insert_edge_cycle_ex_walk_betw:
  assumes "X \<subseteq> G" "Y \<subseteq> G" "\<And> x. x \<in> X - Y  \<Longrightarrow> (\<exists>u c. decycle (insert x Y) u c)"
          "\<nexists>u c. decycle Y u c"
    shows "walk_betw X u p v \<Longrightarrow> \<exists>q. walk_betw Y u q v"
proof (induction rule: induct_walk_betw)
  case (path1 v)
  from subset_edges_G[OF \<open>X \<subseteq> G\<close>]
  have "\<And> e. e \<in> X \<Longrightarrow> \<exists>u v. e = {u, v} \<and> u \<noteq> v" by simp
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

subsection \<open>Cycles and Components\<close>

lemma has_no_cycle_connected_component_card:
  assumes "finite X" "\<And>e. e \<in> X \<Longrightarrow> \<exists>u v. e = {u, v} \<and> u \<noteq> v"
  shows "\<lbrakk>has_no_cycle X; C \<in> connected_components X\<rbrakk> \<Longrightarrow> card C = card (component_edges X C) + 1"
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
  "\<lbrakk>has_no_cycle X; \<And> e. e \<in> X \<Longrightarrow> \<exists>u v. e = {u, v} \<and> u \<noteq> v\<rbrakk>
    \<Longrightarrow> card (Vs X) = card X + card (connected_components X)"
proof(goal_cases)
  case 1
  then have "finite X" "X \<subseteq> G" "dblton_graph X"
    using finite_E rev_finite_subset 1(1)
    by (auto simp add: dblton_graph_def  has_no_cycle_def )
  have "\<And> C. C \<in> connected_components X \<Longrightarrow> finite C"
     using \<open>finite X\<close> 
    by (simp add: \<open>dblton_graph X\<close> connected_component_finite connected_components_def)
  then have "\<And> C. C \<in> connected_components X \<Longrightarrow> finite (component_edges X C)"
    unfolding component_edges_def using \<open>finite X\<close>
    by (smt (verit, best) finite_subset mem_Collect_eq subset_eq)
  then have "\<And> A. A \<in> (components_edges X) \<Longrightarrow> finite A"
    unfolding components_edges_def by auto
  have "finite (connected_components X)"
    by (simp add:  connected_components_def \<open>dblton_graph X\<close> \<open>finite X\<close> finite_dbl_finite_verts)
  then have "finite (components_edges X)"
    unfolding components_edges_def by auto
  have "\<And> A. A \<in> (components_edges X) \<Longrightarrow> finite (id A)" 
    using \<open>\<And>A. A \<in> components_edges X \<Longrightarrow> finite A\<close> by auto
  have disj: "\<And> C C'. \<lbrakk>C \<in> components_edges X; C' \<in> components_edges X; C \<noteq> C'\<rbrakk>
               \<Longrightarrow> id C \<inter> id C' = {}"
    using component_edges_disj by (auto simp add: components_edges_def)
  have component_edges_distinct:
    "\<And> C C'. \<lbrakk>C \<in> connected_components X; C' \<in> connected_components X; C \<noteq> C'\<rbrakk>
      \<Longrightarrow> component_edges X C \<noteq> component_edges X C'"
    using component_edges_disj[where G = "X"] component_edges_nonempty[OF \<open>dblton_graph X\<close>]
    by (fastforce simp add:  components_edges_def)
  have cards_geq_1:
    "\<And> C. C \<in> connected_components X \<Longrightarrow> card C \<ge> 1" 
    by (simp add: \<open>\<And>C. C \<in> connected_components X \<Longrightarrow> finite C\<close> connected_comp_nempty leI)
  have "disjoint (connected_components X)"
    by (simp add: connected_components_disj  disjoint_def)
  have card_Vs_X:
    "card (Vs X) = (\<Sum>C \<in> connected_components X. card C)"
    using Union_connected_components[OF \<open>dblton_graph X\<close>] card_Union_disjoint
          \<open>\<And>C. C \<in> connected_components X \<Longrightarrow> finite C\<close> \<open>disjoint (connected_components X)\<close>
    by fastforce
  from has_no_cycle_connected_component_card[OF \<open>finite X\<close>] \<open>has_no_cycle X\<close>
  have cards_CCs: "\<And> C. C \<in> connected_components X \<Longrightarrow> card C - 1 = card (component_edges X C)"
    using cards_geq_1 "1"(2) by simp
  from \<open>dblton_graph X\<close> have "X = X \<inter> {{x, y} |x y. True}" by fast
  with component_edges_partition have "\<Union> (components_edges X) = X" by fastforce
  then have "card X = card (\<Union> (components_edges X))" by auto
  also have "... = (\<Sum>C \<in> components_edges X. card C)"
    using  disj  \<open>\<And>A. A \<in> components_edges X \<Longrightarrow> finite A\<close>
    by(auto intro!: card_UN_disjoint[OF \<open>finite (components_edges X)\<close>, of id, simplified])
  also have "... = (\<Sum>C \<in> connected_components X. card (component_edges X C))"
    unfolding components_edges_def using component_edges_distinct
    by (smt (verit, best) mem_Collect_eq sum.eq_general)
  also have "... = (\<Sum>C \<in> connected_components X. card C - 1)"
    using cards_CCs by auto
  also have "... = (\<Sum>C \<in> connected_components X. card C) - card (connected_components X)"
    using cards_geq_1 sum_subtractf_nat by force
  also have "... = card (Vs X) - card (connected_components X)"
    using card_Vs_X by simp
  finally have "card X = card (Vs X) - card (connected_components X)" .
  with cards_geq_1
  have "(\<Sum>C \<in> connected_components X. card C) \<ge> card (connected_components X)"
    using sum_mono by force
  then have "card (Vs X) \<ge> card (connected_components X)"
    using card_Vs_X by auto
  with \<open>card X = card (Vs X) - card (connected_components X)\<close>
  show "card (Vs X) = card X + card (connected_components X)" by auto
qed

end
end