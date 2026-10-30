theory Spanning_Tree_Flow
  imports Flow_Theory.Cost_Optimality Spanning_Trees.Arborescense
begin

provenance human

context
cost_flow_network
begin


definition "spanning_tree_partition r T L U =
    (\<E> = T \<union> U \<union> L \<and> T \<inter> U = {} \<and> T \<inter> L = {} \<and> L \<inter> U = {} \<and>
      graph_abs.arborescence ((\<lambda> e. {fst e, snd e} ) ` T) r ((\<lambda> e. {fst e, snd e})  ` T)
      \<and>  graph_abs ((\<lambda> e. {fst e, snd e} ) ` T) \<and>
      (\<forall> e e'. {e, e'} \<subseteq> T \<and> {fst e, snd e} = {fst e', snd e'} \<longrightarrow> e = e') \<and>
      dVs (make_pair ` T) = \<V> )"

definition "flow_fits_spanning_tree_partition T L U f =
    ((\<forall> e \<in> L. f e = 0) \<and> (\<forall> e \<in> U. ereal (f e) = \<u> e))"

definition "potential_fits_spanning_tree_partition r T \<pi> =
       (\<pi> r = 0 \<and> (\<forall> e \<in> T. \<c> e + \<pi> (fst e) - \<pi> (snd e) = 0))"

text \<open>The flow on the tree edges is determined by the balance @{term b}. Otherwise the tree edges
      on which two such flows differ form a non-empty forest. A leaf @{term a} of it has a single
      such edge, and @{thm [source] excess_determines_edge} at @{term a} contradicts this.\<close>

lemma spanning_flow_unique:
  assumes "f is b flow" "f' is b flow" "spanning_tree_partition r T L U"
    "flow_fits_spanning_tree_partition T L U f" "flow_fits_spanning_tree_partition T L U f'"
    "e \<in> \<E>"
  shows "f e = f' e"
proof-
  define GT where "GT = (\<lambda>e. {fst e, snd e}) ` T"
  define D where "D = {e \<in> T. f e \<noteq> f' e}"
  have "\<And>x. \<lbrakk>x \<in> \<E>; x \<notin> T\<rbrakk> \<Longrightarrow> f x = f' x"
    using assms(3-5)
    by (auto simp: spanning_tree_partition_def flow_fits_spanning_tree_partition_def
             intro: ereal.inject[THEN iffD1, OF trans[OF _ sym]])
  moreover have "D = {}"
  proof(rule ccontr)
    assume "D \<noteq> {}"
    have "graph_abs GT" "graph_abs.arborescence GT r GT" "T \<subseteq> \<E>" "inj_on (\<lambda>e. {fst e, snd e}) T"
      using assms(3)
      by (auto simp: spanning_tree_partition_def GT_def inj_on_def)
    hence "graph_abs.has_no_cycle GT ((\<lambda>e. {fst e, snd e}) ` D)"
      by (intro graph_abs.has_no_cycle_indep_subset[OF _ graph_abs.arborescenceD(1)[of GT r GT]])
         (auto simp: GT_def D_def)
    then obtain a where "degree ((\<lambda>e. {fst e, snd e}) ` D) a = 1"
      using graph_abs.tree_has_leaf[OF \<open>graph_abs GT\<close>] \<open>D \<noteq> {}\<close>
      by blast
    then obtain ea where "ea \<in> D" "a \<in> {fst ea, snd ea}"
      "\<And>e. \<lbrakk>e \<in> D; a \<in> {fst e, snd e}\<rbrakk>
         \<Longrightarrow> {fst e, snd e} = {fst ea, snd ea}"
      by (auto dest!: degree_one_unique elim!: ex1E)
    hence "\<And>e. \<lbrakk>e \<in> D; a \<in> {fst e, snd e}\<rbrakk> \<Longrightarrow> e = ea"
      using inj_onD[OF \<open>inj_on (\<lambda>e. {fst e, snd e}) T\<close>]
      unfolding D_def
      by blast
    have "\<And>e. \<lbrakk>e \<in> \<E>; e \<noteq> ea; a \<in> {fst e, snd e}\<rbrakk> \<Longrightarrow> f e = f' e"
      using \<open>\<And>e. \<lbrakk>e \<in> D; a \<in> {fst e, snd e}\<rbrakk> \<Longrightarrow> e = ea\<close>
        \<open>\<And>x. \<lbrakk>x \<in> \<E>; x \<notin> T\<rbrakk> \<Longrightarrow> f x = f' x\<close>
      unfolding D_def
      by blast
    moreover have "fst ea \<noteq> snd ea" "ea \<in> \<E>"
      using graph_invar_edgeD[OF graph_abs.graph[OF \<open>graph_abs GT\<close>], of "fst ea" "snd ea"]
        \<open>ea \<in> D\<close> \<open>T \<subseteq> \<E>\<close>
      by (auto simp: GT_def D_def)
    moreover have "\<And>v. v \<in> \<V> \<Longrightarrow> ex f v = ex f' v"
      using assms(1,2)
      by (force simp: isbflow_def)
    moreover have "a \<in> \<V>"
      using \<open>a \<in> {fst ea, snd ea}\<close> \<open>ea \<in> \<E>\<close> fst_E_V snd_E_V
      by auto
    ultimately have "f ea = f' ea"
      using \<open>a \<in> {fst ea, snd ea}\<close>
      by (auto intro!: excess_determines_edge[of ea a f f'])
    thus False
      using \<open>ea \<in> D\<close>
      by (simp add: D_def)
  qed
  ultimately show ?thesis
    using assms(6)
    by (auto simp: D_def)
qed

text \<open>The potentials are unique, too. They agree at the root @{term r}. Along a tree edge the two
      reduced-cost equations show that agreement at one endpoint gives agreement at the other.
      Every vertex is joined to @{term r} by a walk in the tree.\<close>

lemma spanning_potential_unqiue:
  assumes "spanning_tree_partition r T L U" "potential_fits_spanning_tree_partition r T \<pi>"
    "potential_fits_spanning_tree_partition r T \<pi>'" "v \<in> \<V>"
  shows "\<pi> v = \<pi>' v"
proof-
  define GT where "GT = (\<lambda>e. {fst e, snd e}) ` T"
  have "Vs GT = dVs (make_pair ` T)"
    by (auto simp: GT_def Vs_def dVs_def make_pair_def)
  hence "Vs GT = \<V>" "graph_abs GT" "graph_abs.arborescence GT r GT"
    using assms(1)
    by (auto simp: spanning_tree_partition_def GT_def)
  moreover have "GT \<noteq> {}"
    using assms(4) \<open>Vs GT = \<V>\<close>
    by (auto simp: Vs_def)
  ultimately have "v \<in> connected_component GT r" "r \<in> Vs GT"
    using assms(4) graph_abs.arborescenceD(2)[of GT r GT] in_own_connected_component[of r GT]
    by auto
  then obtain p where "walk_betw GT r p v"
    by (rule in_connected_component_has_walk)
  moreover have "\<And>e. e \<in> T \<Longrightarrow> \<pi> (fst e) = \<pi>' (fst e) \<longleftrightarrow> \<pi> (snd e) = \<pi>' (snd e)"
    using assms(2,3)
    by (fastforce simp: potential_fits_spanning_tree_partition_def)
  hence "\<And>x y. \<lbrakk>{x, y} \<in> GT; \<pi> x = \<pi>' x\<rbrakk> \<Longrightarrow> \<pi> y = \<pi>' y"
    by (auto simp: GT_def doubleton_eq_iff)
  ultimately have "\<pi> r = \<pi>' r \<longrightarrow> \<pi> v = \<pi>' v"
    by (induction rule: induct_walk_betw) auto
  thus ?thesis
    using assms(2,3)
    by (simp add: potential_fits_spanning_tree_partition_def)
qed
end
end