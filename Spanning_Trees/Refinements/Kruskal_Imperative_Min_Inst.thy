theory Kruskal_Imperative_Min_Inst
  imports Kruskal_Imperative_Inst Spanning_Trees.Kruskal_Min
begin

provenance ai_human

section \<open>The Imperative Kruskal's Algorithm for Minimum Spanning Forests\<close>

text \<open>We obtain an imperative algorithm for minimum spanning forests by running the imperative
  (maximum) Kruskal's algorithm with negated costs. The negation is done on a copy of the cost
  array, so the input arrays are left unchanged. In the proof, the negated costs are related to
  the nonnegative shifted costs \<open>M - c\<close> (see \<open>Kruskal_Min\<close>). In contrast to the maximum version,
  there are no assumptions on the signs of the costs.\<close>

subsection \<open>The Imperative Locale\<close>

context Kruskal_Imperative
begin

theorem kruskal_imperative'_min_correct:
  assumes "\<And>e. e \<in> set order \<Longrightarrow> c e \<le> M"
    and "sort_desc (\<lambda>e. - c e) order = sort_desc (\<lambda>e. M - c e) order"
  shows
    "<cost_assn (\<lambda>e. - c e) c_impl * endpoints_assn endpoints ep_impl * edges_array \<mapsto>\<^sub>a order>
       kruskal_imperative' c_impl ep_impl edges_array
     <\<lambda>r. cost_assn (\<lambda>e. - c e) c_impl * endpoints_assn endpoints ep_impl * \<up>(
         set r \<subseteq> set order
       \<and> graph_abs.is_spanning_forest E (set_of_edge ` set r)
       \<and> (\<forall>X. X \<subseteq> set order \<and> graph_abs.is_spanning_forest E (set_of_edge ` X) \<longrightarrow>
            sum c (set r) \<le> sum c X)) * true>"
  by (rule ht_cons_post_prec[OF kruskal_imperative'_rule])
    (sep_auto simp: kruskal_min_weight[OF assms])

end

subsection \<open>Sorting by Shifted Keys\<close>

text \<open>Shifting all keys by the same amount does not change the result of \<open>sort_desc_qs\<close>.\<close>

lemma sort_desc_qs_shift:
  fixes c :: "nat \<Rightarrow> 'k::linordered_ab_group_add"
  shows "sort_desc_qs (\<lambda>e. a + c e) xs = sort_desc_qs c xs"
proof -
  have "sorted_wrt (\<lambda>x y. (c x, x) \<le> (c y, y)) (sort_key (\<lambda>e. (c e, e)) xs)"
    using sorted_sort_key[of "\<lambda>e. (c e, e)" xs] by (simp add: sorted_map)
  hence "sorted_wrt (\<lambda>x y. (c y, y) \<le> (c x, x)) (sort_desc_qs c xs)"
    by (simp add: sort_desc_qs_def sorted_wrt_rev)
  hence "sorted_wrt (\<lambda>x y. (a + c y, y) \<le> (a + c x, x)) (sort_desc_qs c xs)"
    by (rule sorted_wrt_mono_rel[rotated]) (auto simp: less_eq_prod_def)
  moreover have "inj (\<lambda>e. (a + c e, e))"
    by (auto simp: inj_def)
  moreover have "mset (sort_desc_qs c xs) = mset xs"
    by (simp add: sort_desc_qs_def)
  ultimately have "sort_desc_qs c xs = rev (sort_key (\<lambda>e. (a + c e, e)) xs)"
    using sorted_desc_unique[of "\<lambda>e. (a + c e, e)"] by blast
  thus ?thesis
    by (simp add: sort_desc_qs_def)
qed

subsection \<open>The Algorithm\<close>

text \<open>The cost array is copied and negated, and the imperative Kruskal's algorithm is run with
  the negated costs.\<close>

definition kruskal_imp_min ::
  "rat array \<Rightarrow> (nat \<times> nat) array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> nat list Heap"
  where "kruskal_imp_min costs eps edges n = do {
    cs \<leftarrow> Array.freeze costs;
    neg_costs \<leftarrow> Array.of_list (map uminus cs);
    kruskal_imp neg_costs eps edges n
  }"

subsection \<open>Correctness\<close>

subsubsection \<open>Correctness w.r.t. a Red-Black Tree Graph\<close>

lemma kruskal_imp_neg_correct_rbt_graph:
  fixes G :: "(nat \<times> (nat rbt)) rbt" and order :: "nat list"
    and eps :: "(nat \<times> nat) list" and cs :: "rat list"
  assumes "Pair_Graph_U_RBT_Inst.pair_graph_u_invar G"
    "(\<lambda>e. set_of_pair (eps ! e)) ` set order = Pair_Graph_U_RBT_Inst.ugraph_abs G"
    "inj_on (\<lambda>e. set_of_pair (eps ! e)) (set order)"
    "distinct order" "Pair_Graph_U_RBT_Inst.vertices G \<subseteq> {0..<n}"
    "\<forall>e \<in> set order. e < length eps \<and> e < length cs"
  shows
    "<neg_costs \<mapsto>\<^sub>a map uminus cs * eps_impl \<mapsto>\<^sub>a eps * edges \<mapsto>\<^sub>a order>
       kruskal_imp neg_costs eps_impl edges n
     <\<lambda>r. neg_costs \<mapsto>\<^sub>a map uminus cs * eps_impl \<mapsto>\<^sub>a eps * \<up>(set r \<subseteq> set order
       \<and> graph_abs.is_spanning_forest (Pair_Graph_U_RBT_Inst.ugraph_abs G)
           ((\<lambda>e. set_of_pair (eps ! e)) ` set r)
       \<and> (\<forall>X. X \<subseteq> set order \<and>
            graph_abs.is_spanning_forest (Pair_Graph_U_RBT_Inst.ugraph_abs G)
              ((\<lambda>e. set_of_pair (eps ! e)) ` X) \<longrightarrow>
            sum ((!) cs) (set r) \<le> sum ((!) cs) X)) * true>"
proof -
  let ?cs' = "map uminus cs"
  define M where "M = Max (Set.insert 0 ((!) cs ` set order))"
  have bound: "\<And>e. e \<in> set order \<Longrightarrow> - (?cs' ! e) \<le> M"
    using assms(6) by (auto simp: M_def intro!: Max_ge)
  have sort_eq: "sort_desc_qs (\<lambda>e. - (- (?cs' ! e))) order =
      sort_desc_qs (\<lambda>e. M - (- (?cs' ! e))) order"
    using sort_desc_qs_shift[of M "(!) ?cs'" order] by simp
  have sum_eq: "sum (\<lambda>e. - (?cs' ! e)) X = sum ((!) cs) X" if "X \<subseteq> set order" for X
    using that assms(6) by (intro sum.cong) auto
  note inst = Kruskal_Imperative_inst[OF assms(1-4) assms(5)[folded uf_universe_def], of ?cs']
  note rule = Kruskal_Imperative.kruskal_imperative'_min_correct[OF inst bound sort_eq,
      where c_impl = neg_costs and ep_impl = eps_impl and edges_array = edges]
  show ?thesis
    unfolding kruskal_imp_def
    by (rule ht_cons_prec[OF _ _ rule])
      (use assms(6) in \<open>sep_auto simp: cost_assn_arr_def endpoints_assn_arr_def sum_eq\<close>)+
qed

lemma kruskal_imp_min_correct_rbt_graph:
  fixes G :: "(nat \<times> (nat rbt)) rbt" and order :: "nat list"
    and eps :: "(nat \<times> nat) list" and cs :: "rat list"
  assumes "Pair_Graph_U_RBT_Inst.pair_graph_u_invar G"
    "(\<lambda>e. set_of_pair (eps ! e)) ` set order = Pair_Graph_U_RBT_Inst.ugraph_abs G"
    "inj_on (\<lambda>e. set_of_pair (eps ! e)) (set order)"
    "distinct order" "Pair_Graph_U_RBT_Inst.vertices G \<subseteq> {0..<n}"
    "\<forall>e \<in> set order. e < length eps \<and> e < length cs"
  shows
    "<costs \<mapsto>\<^sub>a cs * eps_impl \<mapsto>\<^sub>a eps * edges \<mapsto>\<^sub>a order>
       kruskal_imp_min costs eps_impl edges n
     <\<lambda>r. costs \<mapsto>\<^sub>a cs * eps_impl \<mapsto>\<^sub>a eps * \<up>(set r \<subseteq> set order
       \<and> graph_abs.is_spanning_forest (Pair_Graph_U_RBT_Inst.ugraph_abs G)
           ((\<lambda>e. set_of_pair (eps ! e)) ` set r)
       \<and> (\<forall>X. X \<subseteq> set order \<and>
            graph_abs.is_spanning_forest (Pair_Graph_U_RBT_Inst.ugraph_abs G)
              ((\<lambda>e. set_of_pair (eps ! e)) ` X) \<longrightarrow>
            sum ((!) cs) (set r) \<le> sum ((!) cs) X)) * true>"
  unfolding kruskal_imp_min_def
  by (sep_auto heap: kruskal_imp_neg_correct_rbt_graph[OF assms])

subsubsection \<open>Correctness w.r.t. the Arrays\<close>

text \<open>The final correctness theorem for minimum spanning forests. The assumptions are the same
  as for the maximum version (\<open>kruskal_imp_correct\<close>), except that the costs may be arbitrary.
  The result is compared with all spanning forests of the graph.\<close>

theorem kruskal_imp_min_correct:
  fixes order :: "nat list" and eps :: "(nat \<times> nat) list" and cs :: "rat list"
  assumes "distinct order"
    "\<forall>e \<in> set order. e < length eps \<and> e < length cs"
    "\<forall>e \<in> set order. fst (eps ! e) \<noteq> snd (eps ! e) \<and> fst (eps ! e) < n \<and> snd (eps ! e) < n"
    "inj_on (\<lambda>e. set_of_pair (eps ! e)) (set order)"
  shows
    "<costs \<mapsto>\<^sub>a cs * eps_impl \<mapsto>\<^sub>a eps * edges \<mapsto>\<^sub>a order>
       kruskal_imp_min costs eps_impl edges n
     <\<lambda>r. costs \<mapsto>\<^sub>a cs * eps_impl \<mapsto>\<^sub>a eps * \<up>(set r \<subseteq> set order
       \<and> graph_abs.is_spanning_forest ((\<lambda>e. set_of_pair (eps ! e)) ` set order)
           ((\<lambda>e. set_of_pair (eps ! e)) ` set r)
       \<and> (\<forall>X. X \<subseteq> set order \<and>
            graph_abs.is_spanning_forest ((\<lambda>e. set_of_pair (eps ! e)) ` set order)
              ((\<lambda>e. set_of_pair (eps ! e)) ` X) \<longrightarrow>
            sum ((!) cs) (set r) \<le> sum ((!) cs) X)) * true>"
proof -
  let ?es = "map ((!) eps) order"
  let ?G = "graph_of_edges ?es"
  have neq: "\<forall>(u, v) \<in> set ?es. u \<noteq> v"
    using assms(3) by auto
  note G = graph_of_edges_props[OF neq]
  have ugraph: "Pair_Graph_U_RBT_Inst.ugraph_abs ?G = (\<lambda>e. set_of_pair (eps ! e)) ` set order"
    by (simp add: G(3) image_comp)
  have bounded: "\<forall>(a, b) \<in> set ?es \<union> prod.swap ` set ?es. a < n \<and> b < n"
    using assms(3) by (auto simp: prod_eq_iff)
  have vertices: "Pair_Graph_U_RBT_Inst.vertices ?G \<subseteq> {0..<n}"
    unfolding Pair_Graph_U_RBT_Inst.vertices_equiv_dVs G(2)
    using bounded by (fastforce simp: dVs_def)
  show ?thesis
    using kruskal_imp_min_correct_rbt_graph[OF G(1) ugraph[symmetric] assms(4,1) vertices assms(2)]
    by (simp add: ugraph)
qed

subsection \<open>Code Generation\<close>

export_code kruskal_imp_min rat_of_int checking SML_imp

subsection \<open>Examples\<close>

text \<open>The examples of the maximum version (see \<open>Kruskal_Imperative_Inst\<close>), now for minimum
  spanning trees. For the first example, the minimum spanning tree consists of the edges
  1, 3, 2, 6 (in the order in which they are chosen) and has weight 12.\<close>

definition "kruskal_min_example = do {
  costs \<leftarrow> Array.of_list example_costs;
  eps \<leftarrow> Array.of_list example_endpoints;
  edges \<leftarrow> Array.of_list [0..<7];
  kruskal_imp_min costs eps edges 5
}"

ML_val \<open>@{code kruskal_min_example} ()\<close>

text \<open>The graph with 10 vertices and 20 edges: the minimum spanning tree consists of the edges
  12, 10, 1, 5, 4, 8, 11, 14, 16 (in the order in which they are chosen) and has weight 62.\<close>

definition "kruskal_min_example_20 = do {
  costs \<leftarrow> Array.of_list example_costs_20;
  eps \<leftarrow> Array.of_list example_endpoints_20;
  edges \<leftarrow> Array.of_list [0..<20];
  kruskal_imp_min costs eps edges 10
}"

ML_val \<open>@{code kruskal_min_example_20} ()\<close>

end
