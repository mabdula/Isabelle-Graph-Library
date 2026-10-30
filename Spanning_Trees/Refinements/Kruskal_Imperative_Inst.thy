theory Kruskal_Imperative_Inst
  imports Kruskal_Imperative Quicksort_Desc_Imperative
    Union_Find_Partial.Union_Find_Size_Int_Imp_Partial
    Graph_Algorithms_Dev.DFS_Example Graph_Algorithms_Dev.RBT_Map_Extension
    "HOL-Library.Code_Target_Numeral" Imperative.Code_Target_Machine_Int
begin

provenance ai_human

no_notation Ref.update (\<open>_ := _\<close> 62)

section \<open>Instantiation of the Imperative Kruskal's Algorithm\<close>

text \<open>We instantiate the imperative Kruskal's algorithm with
  \<^item> red-black trees for the graph (adjacency map) and for the (ghost) edge sets,
  \<^item> the union-find data structure with union by size and path compression from
    the Union-Find-Explain formalisation (\<open>CADE_artefact\<close>), where the sizes are encoded in a
    single integer array,
  \<^item> an in-place imperative quicksort (sorting by keys in descending order), and
  \<^item> a pure cost function.\<close>

subsection \<open>Union-Find\<close>

subsubsection \<open>The Abstraction of the Functional Union-Find Structure\<close>

lemma equiv_ufsi_\<alpha>: "equiv (Field (ufsi_\<alpha> u)) (ufsi_\<alpha> u)"
  including ufsi.lifting
  by transfer (simp add: ufs_\<alpha>_def equiv_Field_ufa_\<alpha>_ufa_\<alpha>)

lemma ufsi_\<alpha>_ufsi_init: "ufsi_\<alpha> (ufsi_init n) = {(x, x) |x. x < n}"
  including ufsi.lifting
  by transfer (simp add: ufs_\<alpha>_def ufa_of_ufs_ufs_init ufa_\<alpha>_ufa_init)

lemma Field_ufsi_\<alpha>_ufsi_init: "Field (ufsi_\<alpha> (ufsi_init n)) = {0..<n}"
  by (auto simp: ufsi_\<alpha>_ufsi_init Field_def)

lemma ufsi_\<alpha>_ufsi_union_size:
  "ufsi_\<alpha> (ufsi_union_size u x y) = per_union (ufsi_\<alpha> u) x y"
  including ufsi.lifting
  by transfer
    (auto simp: ufs_\<alpha>_def ufa_of_ufs_ufs_union_size ufa_union_size_def)

lemma ufsi_rep_of_eq_iff_in_ufsi_\<alpha>:
  assumes "x \<in> Field (ufsi_\<alpha> u)" "y \<in> Field (ufsi_\<alpha> u)"
  shows "ufsi_rep_of u x = ufsi_rep_of u y \<longleftrightarrow> (x, y) \<in> ufsi_\<alpha> u"
  using assms including ufsi.lifting
  by transfer (simp add: ufs_\<alpha>_def ufs_rep_of_def ufa_rep_of_eq_iff_in_ufa_\<alpha>)

subsubsection \<open>Partitions given by Equivalence Relations\<close>

text \<open>The equivalence classes of an equivalence relation after merging two classes.\<close>

lemma per_union_Image:
  assumes "equiv A Rel" "x \<in> A" "y \<in> A" "z \<in> A"
  shows "per_union Rel x y `` {z} = (if z \<in> Rel `` {x} \<union> Rel `` {y} then Rel `` {x} \<union> Rel `` {y} else Rel `` {z})"
proof -
  have sym: "(b, a) \<in> Rel" if "(a, b) \<in> Rel" for a b
    using assms(1) that by (auto simp: equiv_def sym_def)
  have Image: "per_union Rel x y `` {z} =
    Rel `` {z} \<union> (if (z, x) \<in> Rel then Rel `` {y} else {}) \<union>
      (if (z, y) \<in> Rel then Rel `` {x} else {})"
    by (auto simp: per_union_def intro: sym)
  show ?thesis
  proof (cases "z \<in> Rel `` {x} \<union> Rel `` {y}")
    case True
    then have "(z, x) \<in> Rel \<or> (z, y) \<in> Rel"
      using sym by auto
    then show ?thesis
      using True Image equiv_class_eq[OF assms(1), of z x] equiv_class_eq[OF assms(1), of z y]
      by auto
  next
    case False
    then have "(z, x) \<notin> Rel" "(z, y) \<notin> Rel"
      using sym by auto
    then show ?thesis
      using False Image by simp
  qed
qed

lemma quotient_per_union:
  assumes "equiv A Rel" "x \<in> A" "y \<in> A"
  shows "A // per_union Rel x y = (A // Rel - {Rel `` {x}, Rel `` {y}}) \<union> {Rel `` {x} \<union> Rel `` {y}}"
proof (rule set_eqI, rule iffI)
  fix C
  assume "C \<in> A // per_union Rel x y"
  then obtain z where z: "z \<in> A" "C = per_union Rel x y `` {z}"
    by (auto elim: quotientE)
  show "C \<in> (A // Rel - {Rel `` {x}, Rel `` {y}}) \<union> {Rel `` {x} \<union> Rel `` {y}}"
  proof (cases "z \<in> Rel `` {x} \<union> Rel `` {y}")
    case True
    thus ?thesis
      using z per_union_Image[OF assms z(1)] by simp
  next
    case False
    hence "Rel `` {z} \<noteq> Rel `` {x}" "Rel `` {z} \<noteq> Rel `` {y}"
      using assms(1) z(1) equiv_class_self by fastforce+
    thus ?thesis
      using False z per_union_Image[OF assms z(1)] by (auto intro: quotientI)
  qed
next
  fix C
  assume C: "C \<in> (A // Rel - {Rel `` {x}, Rel `` {y}}) \<union> {Rel `` {x} \<union> Rel `` {y}}"
  show "C \<in> A // per_union Rel x y"
  proof (cases "C = Rel `` {x} \<union> Rel `` {y}")
    case True
    have "x \<in> Rel `` {x}"
      using assms(1,2) equiv_class_self by fast
    hence "per_union Rel x y `` {x} = C"
      using True per_union_Image[OF assms assms(2)] by simp
    thus ?thesis
      using assms(2) by (auto intro: quotientI[of x A, where r = "per_union Rel x y", simplified])
  next
    case False
    with C have C': "C \<in> A // Rel" "C \<noteq> Rel `` {x}" "C \<noteq> Rel `` {y}"
      by auto
    then obtain z where "z \<in> A" "C = Rel `` {z}"
      by (auto elim: quotientE)
    with C' have z: "z \<in> A" "C = Rel `` {z}" "C \<noteq> Rel `` {x}" "C \<noteq> Rel `` {y}"
      by auto
    have "z \<notin> Rel `` {x} \<union> Rel `` {y}"
      using z assms(1) equiv_class_eq by fastforce
    hence "per_union Rel x y `` {z} = C"
      using z per_union_Image[OF assms z(1)] by simp
    thus ?thesis
      using z(1) by (auto intro: quotientI[of z A, where r = "per_union Rel x y", simplified])
  qed
qed

subsubsection \<open>Interpretation of the Union-Find Specification\<close>

text \<open>The universe is \<open>{0..<n}\<close>, and the sets are the equivalence classes of the abstraction.\<close>

definition "ufsi_uf_invar u n \<longleftrightarrow> Field (ufsi_\<alpha> u) = {0..<n}"

definition "ufsi_set_of_sets u = Field (ufsi_\<alpha> u) // ufsi_\<alpha> u"

definition "ufsi_in_same_set u x y \<longleftrightarrow> (x, y) \<in> ufsi_\<alpha> u"

definition "uf_universe (n::nat) = {0..<n}"

lemma ufsi_UnionFind_Specs:
  "UnionFind_Specs ufsi_uf_invar ufsi_set_of_sets ufsi_union_size ufsi_in_same_set ufsi_init uf_universe"
proof (unfold_locales, goal_cases)
  case (1 uf s)
  then show ?case
    using Union_quotient[OF equiv_ufsi_\<alpha>[of uf]]
    by (simp add: ufsi_uf_invar_def ufsi_set_of_sets_def uf_universe_def)
next
  case (2 uf s)
  then show ?case
    using quotient_disj[OF equiv_ufsi_\<alpha>]
    by (auto simp: ufsi_set_of_sets_def pairwise_def disjnt_def)
next
  case (3 uf s)
  then show ?case
    using in_quotient_imp_non_empty[OF equiv_ufsi_\<alpha>]
    by (auto simp: ufsi_set_of_sets_def)
next
  case (4 uf s x y)
  then have xy: "x \<in> Field (ufsi_\<alpha> uf)" "y \<in> Field (ufsi_\<alpha> uf)"
    by (simp_all add: ufsi_uf_invar_def uf_universe_def)
  show ?case
  proof
    assume "ufsi_in_same_set uf x y"
    then have "(x, y) \<in> ufsi_\<alpha> uf"
      by (simp add: ufsi_in_same_set_def)
    moreover have "ufsi_\<alpha> uf `` {x} \<in> ufsi_set_of_sets uf"
      using xy(1) by (simp add: ufsi_set_of_sets_def quotientI)
    moreover have "x \<in> ufsi_\<alpha> uf `` {x}"
      using equiv_class_self[OF equiv_ufsi_\<alpha> xy(1)] .
    ultimately show "\<exists>A \<in> ufsi_set_of_sets uf. x \<in> A \<and> y \<in> A"
      by blast
  next
    assume "\<exists>A \<in> ufsi_set_of_sets uf. x \<in> A \<and> y \<in> A"
    then obtain A where "A \<in> Field (ufsi_\<alpha> uf) // ufsi_\<alpha> uf" "x \<in> A" "y \<in> A"
      by (auto simp: ufsi_set_of_sets_def)
    then show "ufsi_in_same_set uf x y"
      using quotient_eq_iff[OF equiv_ufsi_\<alpha>[of uf], of A A x y]
      by (simp add: ufsi_in_same_set_def)
  qed
next
  case (5 uf s x y)
  then show ?case
    by (simp add: ufsi_uf_invar_def ufsi_\<alpha>_ufsi_union_size)
next
  case (6 uf s x A y B)
  have in_class: "C = ufsi_\<alpha> uf `` {z}" if "C \<in> Field (ufsi_\<alpha> uf) // ufsi_\<alpha> uf" "z \<in> C"
    for C z
    using that by (elim quotientE) (simp add: equiv_class_eq[OF equiv_ufsi_\<alpha>])
  have AB: "A = ufsi_\<alpha> uf `` {x}" "B = ufsi_\<alpha> uf `` {y}"
    "x \<in> Field (ufsi_\<alpha> uf)" "y \<in> Field (ufsi_\<alpha> uf)"
    using 6 in_class in_quotient_imp_subset[OF equiv_ufsi_\<alpha>[of uf]]
    by (auto simp: ufsi_set_of_sets_def)
  then show ?case
    using quotient_per_union[OF equiv_ufsi_\<alpha> AB(3,4)]
    by (simp add: ufsi_set_of_sets_def ufsi_\<alpha>_ufsi_union_size)
next
  case (7 s)
  then show ?case
    by (simp add: ufsi_uf_invar_def Field_ufsi_\<alpha>_ufsi_init)
next
  case (8 s)
  have "ufsi_\<alpha> (ufsi_init s) `` {a} = {a}" if "a < s" for a
    using that by (auto simp: ufsi_\<alpha>_ufsi_init)
  then show ?case
    by (auto simp: ufsi_set_of_sets_def Field_ufsi_\<alpha>_ufsi_init quotient_def uf_universe_def)
qed

subsubsection \<open>The Imperative Operations\<close>

text \<open>The Union-Find-Explain formalisation does not provide an operation for checking whether
  two elements are in the same set, so we add one.\<close>

definition "ufsi_imp_same_set ufsi_imp x y = do {
  rep_x \<leftarrow> ufsi_imp_rep_of_c ufsi_imp x;
  rep_y \<leftarrow> ufsi_imp_rep_of_c ufsi_imp y;
  Heap_Monad.return (rep_x = rep_y)
}"

lemma ufsi_imp_same_set_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufsi_\<alpha> u)" "y \<in> Field (ufsi_\<alpha> u)"
  shows "<is_ufsi_c u p> ufsi_imp_same_set p x y
    <\<lambda>r. is_ufsi_c u p * \<up>(r = ufsi_in_same_set u x y)>"
  using assms unfolding ufsi_imp_same_set_def ufsi_in_same_set_def
  by (sep_auto simp: ufsi_rep_of_eq_iff_in_ufsi_\<alpha>)

lemma ufsi_imp_init_is_ufsi_c_rule[sep_heap_rules]:
  "<emp> ufsi_imp_init n <is_ufsi_c (ufsi_init n)>"
  by (rule ht_cons_post_prec[OF ufsi_imp_init_rule is_ufsi_entails_is_ufsi_c])

subsection \<open>Graphs and Edge Sets\<close>

text \<open>The graph is given as an adjacency map (a red-black tree map from vertices to red-black
  tree sets of neighbours). The edge sets are red-black tree sets of pairs; they are only used
  in the proofs.\<close>

interpretation Pair_Graph_U_RBT_Inst: Pair_Graph_U_Specs
  where empty = empty and update = update and delete = delete and
    lookup = lookup and adjmap_inv = "M.invar" and vset_empty = "\<langle>\<rangle>" and
    insert = vset_insert and vset_delete = vset_delete and vset_inv = "vset_inv::(('v::linorder) rbt \<Rightarrow> bool)" and
    isin = isin and t_set = "Tree2.set_tree" and sel = sel
  by (simp add: Pair_Graph_U_Specs_def Pair_Graph_Specs_def Pair_Graph_U_Specs_Read_Only_def
      Pair_Graph_Specs_Read_Only_def M.Map_axioms S_C.Set_Choose_axioms)

lemmas rbt_size_correct' = rbt_size_correct[simplified
    vset_inv_def[simplified t_inv_def[symmetric], symmetric]]
lemmas rbt_nonempty_repr' = rbt_nonempty_repr[simplified
    vset_inv_def[simplified t_inv_def[symmetric], symmetric]]

interpretation Edge_Sets_RBT: Matroid_Specs
  where set_empty = "\<langle>\<rangle>" and set_insert = insert_rbt and set_delete = delete_rbt and
    set_inv = "vset_inv::(('e::linorder) rbt \<Rightarrow> bool)" and
    set_isin = isin and to_set = "Tree2.set_tree" and union = "RBT.union" and inter = "RBT.inter" and
    diff = "RBT.diff" and cardinality = size
  apply (subst Matroid_Specs_def, subst Indep_System_Specs_def, subst Card_Set2_def)
  apply (intro conjI)
  subgoal
    by (metis RBT_Set.empty_def dfs.set_ops.Set2_axioms)
  subgoal
    by (subst Card_Set2_axioms_def) (use rbt_nonempty_repr' rbt_size_correct' in blast)
  done

subsection \<open>Costs, Endpoints and Sorting\<close>

text \<open>Edges are natural numbers. The costs and the endpoints of the edges are stored in arrays
  on the heap, indexed by the edges. The functional cost and endpoints functions are thus
  \<open>(!) cs\<close> and \<open>(!) eps\<close>, where \<open>cs\<close> and \<open>eps\<close> are the contents of the arrays. The assertions
  also require all edges in \<open>es\<close> (which will be the list of edges of the graph) to be valid
  indices of the arrays.\<close>

instance rat :: heap ..

definition "cost_assn_arr es cs c c_impl =
  c_impl \<mapsto>\<^sub>a cs * \<up>(c = (!) cs \<and> (\<forall>e \<in> set es. e < length cs))"

definition "endpoints_assn_arr es eps ep ep_impl =
  ep_impl \<mapsto>\<^sub>a eps * \<up>(ep = (!) eps \<and> (\<forall>e \<in> set es. e < length eps))"

lemma qsort_desc_cost_rule:
  "set xs \<subseteq> set es \<Longrightarrow>
    <cost_assn_arr es cs c c_impl * a \<mapsto>\<^sub>a xs> qsort_desc c_impl a
    <\<lambda>r. cost_assn_arr es cs c c_impl * a \<mapsto>\<^sub>a sort_desc_qs c xs * \<up>(r = a)>"
  unfolding cost_assn_arr_def
  by (sep_auto heap: qsort_desc_rule)

lemma nth_endpoints_rule:
  "e \<in> set es \<Longrightarrow>
    <endpoints_assn_arr es eps ep ep_impl> Array.nth ep_impl e
    <\<lambda>r. endpoints_assn_arr es eps ep ep_impl * \<up>(r = ep e)>"
  unfolding endpoints_assn_arr_def by sep_auto

lemma sort_desc_axioms_sort_desc_qs: "sort_desc_axioms' sort_desc_qs"
  by (simp add: sort_desc_axioms_def sort_desc_qs_props)

subsection \<open>The Instantiation\<close>

lemma Kruskal_Imperative_inst:
  fixes G :: "(nat \<times> (nat rbt)) rbt" and order :: "nat list"
    and eps :: "(nat \<times> nat) list" and cs :: "rat list"
  assumes "Pair_Graph_U_RBT_Inst.pair_graph_u_invar G"
    "(\<lambda>e. set_of_pair (eps ! e)) ` set order = Pair_Graph_U_RBT_Inst.ugraph_abs G"
    "inj_on (\<lambda>e. set_of_pair (eps ! e)) (set order)"
    "distinct order" "Pair_Graph_U_RBT_Inst.vertices G \<subseteq> uf_universe n"
  shows "Kruskal_Imperative empty delete isin Tree2.set_tree sel update M.invar \<langle>\<rangle> vset_delete vset_inv
    delete_rbt isin vset_inv RBT.union RBT.inter RBT.diff size Tree2.set_tree
    ufsi_union_size ufsi_in_same_set ufsi_init vset_insert \<langle>\<rangle> insert_rbt ufsi_set_of_sets uf_universe
    G n ((!) eps) sort_desc_qs lookup ufsi_uf_invar order
    is_ufsi_c ufsi_imp_init ufsi_imp_union_size_c ufsi_imp_same_set
    (endpoints_assn_arr order eps) Array.nth (cost_assn_arr order cs) qsort_desc"
proof (intro Kruskal_Imperative.intro Kruskal.intro Kruskal_axioms.intro
    Kruskal_Imperative_axioms.intro, goal_cases)
  case 1
  then show ?case
    using Pair_Graph_U_RBT_Inst.Pair_Graph_U_Specs_axioms .
next
  case 2
  then show ?case
    using Edge_Sets_RBT.Matroid_Specs_axioms .
next
  case 3
  then show ?case
    using ufsi_UnionFind_Specs .
qed (auto simp: assms sort_desc_axioms_sort_desc_qs Indep_System_Specs.finite_sets_def
    ufsi_imp_init_is_ufsi_c_rule qsort_desc_cost_rule nth_endpoints_rule
    ufsi_uf_invar_def uf_universe_def
    intro: ufsi_imp_union_size_c_is_ufsi_c_rule ufsi_imp_same_set_rule
    dest: subsetD[OF assms(5)])

text \<open>The imperative Kruskal's algorithm. It takes an array holding the costs of the edges, an
  array holding the endpoints of the edges, an array holding the edges of the graph (which are
  indices into the other two arrays), and the number of vertices. It returns the list of chosen
  edges.\<close>

definition kruskal_imp ::
  "rat array \<Rightarrow> (nat \<times> nat) array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> nat list Heap"
  where "kruskal_imp costs eps edges n =
    Kruskal_Imperative.kruskal_imperative' n ufsi_imp_init ufsi_imp_union_size_c ufsi_imp_same_set
      Array.nth qsort_desc costs eps edges"

subsection \<open>Correctness\<close>

subsubsection \<open>Correctness w.r.t. a Red-Black Tree Graph\<close>

lemma kruskal_imp_correct_rbt_graph:
  fixes G :: "(nat \<times> (nat rbt)) rbt" and order :: "nat list"
    and eps :: "(nat \<times> nat) list" and cs :: "rat list"
  assumes "Pair_Graph_U_RBT_Inst.pair_graph_u_invar G"
    "(\<lambda>e. set_of_pair (eps ! e)) ` set order = Pair_Graph_U_RBT_Inst.ugraph_abs G"
    "inj_on (\<lambda>e. set_of_pair (eps ! e)) (set order)"
    "distinct order" "Pair_Graph_U_RBT_Inst.vertices G \<subseteq> {0..<n}"
    "\<forall>e \<in> set order. e < length eps \<and> e < length cs"
    and "\<forall>e \<in> set order. cs ! e \<ge> 0"
  shows
    "<costs \<mapsto>\<^sub>a cs * eps_impl \<mapsto>\<^sub>a eps * edges \<mapsto>\<^sub>a order>
       kruskal_imp costs eps_impl edges n
     <\<lambda>r. costs \<mapsto>\<^sub>a cs * eps_impl \<mapsto>\<^sub>a eps * \<up>(set r \<subseteq> set order
       \<and> graph_abs.is_spanning_forest (Pair_Graph_U_RBT_Inst.ugraph_abs G)
           ((\<lambda>e. set_of_pair (eps ! e)) ` set r)
       \<and> (\<forall>X. X \<subseteq> set order \<and>
            graph_abs.has_no_cycle (Pair_Graph_U_RBT_Inst.ugraph_abs G)
              ((\<lambda>e. set_of_pair (eps ! e)) ` X) \<longrightarrow>
            sum ((!) cs) X \<le> sum ((!) cs) (set r))) * true>"
proof -
  note inst = Kruskal_Imperative_inst[OF assms(1-4) assms(5)[folded uf_universe_def], of cs]
  show ?thesis
    unfolding kruskal_imp_def
    by (rule ht_cons_prec[OF _ _ Kruskal_Imperative.kruskal_imperative'_correct[OF inst,
            where c = "(!) cs" and c_impl = costs and ep_impl = eps_impl and edges_array = edges]])
      (use assms(6,7) in \<open>sep_auto simp: cost_assn_arr_def endpoints_assn_arr_def\<close>)+
qed

subsubsection \<open>Correctness w.r.t. the Arrays\<close>

text \<open>The graph is only used in the correctness statement. For given edges, we build the
  corresponding red-black tree graph (only in the proof), so that the final correctness theorem
  only talks about the arrays.\<close>

lemma pair_graph_u_invar_vset_empty:
  "Pair_Graph_U_RBT_Inst.pair_graph_u_invar (vset_empty :: (nat \<times> (nat rbt)) rbt)"
  unfolding Pair_Graph_U_RBT_Inst.pair_graph_u_invar_def
  apply (intro conjI Pair_Graph_RBT.G.graph_inv_empty Pair_Graph_RBT.G.finite_vsets_empty
      Pair_Graph_RBT.G.finite_graph_empty)
  apply (simp_all add: Pair_Graph_U_RBT_Inst.neighbourhood_def RBT_Set.empty_def)
  done

lemma digraph_abs_vset_empty:
  "Pair_Graph_U_RBT_Inst.digraph_abs (vset_empty :: (nat \<times> (nat rbt)) rbt) = {}"
  by (simp add: Pair_Graph_U_RBT_Inst.digraph_abs_def Pair_Graph_U_RBT_Inst.neighbourhood_def
      RBT_Set.empty_def)

definition graph_of_edges :: "(nat \<times> nat) list \<Rightarrow> (nat \<times> (nat rbt)) rbt" where
  "graph_of_edges es = foldr (\<lambda>(u, v) G. Pair_Graph_U_RBT_Inst.add_u_edge G u v) es vset_empty"

lemma graph_of_edges_props_conj:
  "\<forall>(u, v) \<in> set es. u \<noteq> v \<Longrightarrow>
    Pair_Graph_U_RBT_Inst.pair_graph_u_invar (graph_of_edges es) \<and>
    Pair_Graph_U_RBT_Inst.digraph_abs (graph_of_edges es) = set es \<union> prod.swap ` set es \<and>
    Pair_Graph_U_RBT_Inst.ugraph_abs (graph_of_edges es) = set_of_pair ` set es"
proof (induction es)
  case Nil
  have "Pair_Graph_U_RBT_Inst.digraph_abs (graph_of_edges []) = {}"
    by (simp add: graph_of_edges_def digraph_abs_vset_empty)
  then show ?case
    by (simp add: graph_of_edges_def pair_graph_u_invar_vset_empty
        Pair_Graph_U_RBT_Inst.ugraph_and_digraph_abs)
next
  case (Cons e es)
  obtain u v where e: "e = (u, v)" by fastforce
  have uv: "u \<noteq> v"
    using Cons.prems e by auto
  have IH: "Pair_Graph_U_RBT_Inst.pair_graph_u_invar (graph_of_edges es)"
    "Pair_Graph_U_RBT_Inst.digraph_abs (graph_of_edges es) = set es \<union> prod.swap ` set es"
    "Pair_Graph_U_RBT_Inst.ugraph_abs (graph_of_edges es) = set_of_pair ` set es"
    using Cons.IH Cons.prems by auto
  have G: "graph_of_edges ((u, v) # es) = Pair_Graph_U_RBT_Inst.add_u_edge (graph_of_edges es) u v"
    by (simp add: graph_of_edges_def)
  note add = Pair_Graph_U_RBT_Inst.pair_graph_u_invar_add_u_edge[OF IH(1) uv]
  show ?case
    unfolding e G
    using add(1,4,5) IH(2,3) by (auto simp: set_of_pair_def)
qed

lemma graph_of_edges_props:
  assumes "\<forall>(u, v) \<in> set es. u \<noteq> v"
  shows "Pair_Graph_U_RBT_Inst.pair_graph_u_invar (graph_of_edges es)"
    "Pair_Graph_U_RBT_Inst.digraph_abs (graph_of_edges es) = set es \<union> prod.swap ` set es"
    "Pair_Graph_U_RBT_Inst.ugraph_abs (graph_of_edges es) = set_of_pair ` set es"
  using graph_of_edges_props_conj[OF assms] by auto

text \<open>The final correctness theorem. The graph is given by the list of edges \<open>order\<close> and the
  endpoints \<open>eps ! e\<close> of each edge \<open>e\<close>. It has to be simple: edges have two different endpoints,
  and different edges have different sets of endpoints. For nonnegative costs \<open>cs ! e\<close>, Kruskal's
  algorithm computes a maximum-weight spanning forest of the graph. The arrays of costs and
  endpoints are only read.\<close>

theorem kruskal_imp_correct:
  fixes order :: "nat list" and eps :: "(nat \<times> nat) list" and cs :: "rat list"
  assumes "distinct order"
    "\<forall>e \<in> set order. e < length eps \<and> e < length cs"
    "\<forall>e \<in> set order. fst (eps ! e) \<noteq> snd (eps ! e) \<and> fst (eps ! e) < n \<and> snd (eps ! e) < n"
    "inj_on (\<lambda>e. set_of_pair (eps ! e)) (set order)"
    and "\<forall>e \<in> set order. cs ! e \<ge> 0"
  shows
    "<costs \<mapsto>\<^sub>a cs * eps_impl \<mapsto>\<^sub>a eps * edges \<mapsto>\<^sub>a order>
       kruskal_imp costs eps_impl edges n
     <\<lambda>r. costs \<mapsto>\<^sub>a cs * eps_impl \<mapsto>\<^sub>a eps * \<up>(set r \<subseteq> set order
       \<and> graph_abs.is_spanning_forest ((\<lambda>e. set_of_pair (eps ! e)) ` set order)
           ((\<lambda>e. set_of_pair (eps ! e)) ` set r)
       \<and> (\<forall>X. X \<subseteq> set order \<and>
            graph_abs.has_no_cycle ((\<lambda>e. set_of_pair (eps ! e)) ` set order)
              ((\<lambda>e. set_of_pair (eps ! e)) ` X) \<longrightarrow>
            sum ((!) cs) X \<le> sum ((!) cs) (set r))) * true>"
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
    using kruskal_imp_correct_rbt_graph[OF G(1) ugraph[symmetric] assms(4,1) vertices assms(2,5)]
    by (simp add: ugraph)
qed

subsection \<open>Machine Integers\<close>

text \<open>The generated code uses machine integers for natural numbers and integers (see
  \<open>Code_Target_Machine_Int\<close>), in SML as well as in Go and Scala.

  The union-find structure stores natural numbers (parents) and negated sizes in an array of
  integers, and converts between the two types with @{const nat} and @{const int}. Without the
  following printing, these conversions would be generated via @{typ integer}, whose code
  equations pattern-match on the representations of @{typ int} and @{typ nat}, which are printed
  as machine integers. Since both types are machine integers, @{const int} (in its code form
  @{const int_of_nat}) is the identity, and @{const nat} truncates negative numbers to \<open>0\<close>.\<close>

code_printing
  constant "nat :: int \<Rightarrow> nat" \<rightharpoonup> (SML) "Int.max/ ((0 : Int.int),/ (_))"
    and (Scala) "scala.math.max(0L,/ (_).asInstanceOf[Long])"
    and (Go) "!(func (k int64) int64 { if k < 0 { return 0 }; return k }((_)))"
| constant int_of_nat \<rightharpoonup> (SML) "_" and (Scala) "Machine.int((_))" and (Go) "_"

subsection \<open>Code Generation\<close>

text \<open>The defining equations of the constants of the locale \<open>Kruskal_Imperative\<close> are only
  available under the locale assumptions. Since these constants do not depend on the graph
  (which is only used in the correctness statement), we obtain unconditional equations from the
  instance for the empty graph.\<close>

lemma Kruskal_Imperative_empty_graph:
  "Kruskal_Imperative empty delete isin Tree2.set_tree sel update M.invar \<langle>\<rangle> vset_delete vset_inv
    delete_rbt isin vset_inv RBT.union RBT.inter RBT.diff size Tree2.set_tree
    ufsi_union_size ufsi_in_same_set ufsi_init vset_insert \<langle>\<rangle> insert_rbt ufsi_set_of_sets uf_universe
    (vset_empty :: (nat \<times> (nat rbt)) rbt) n ((!) []) sort_desc_qs lookup ufsi_uf_invar []
    is_ufsi_c ufsi_imp_init ufsi_imp_union_size_c ufsi_imp_same_set
    (endpoints_assn_arr [] []) Array.nth (cost_assn_arr [] []) qsort_desc"
  by (rule Kruskal_Imperative_inst)
    (simp_all add: pair_graph_u_invar_vset_empty digraph_abs_vset_empty
      Pair_Graph_U_RBT_Inst.vertices_equiv_dVs Pair_Graph_U_RBT_Inst.ugraph_and_digraph_abs)

definition kruskal_imp_init ::
  "rat array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> (nat, ufsi_imp) kruskal_state_imp Heap"
  where "kruskal_imp_init costs edges n =
  Kruskal_Imperative.kruskal_initial_state_impl n ufsi_imp_init qsort_desc costs edges"

definition kruskal_imp_loop ::
  "(nat \<times> nat) array \<Rightarrow> (nat, ufsi_imp) kruskal_state_imp \<Rightarrow> (nat, ufsi_imp) kruskal_state_imp Heap"
  where "kruskal_imp_loop =
  Kruskal_Imperative.kruskal_imperative ufsi_imp_union_size_c ufsi_imp_same_set Array.nth"

lemma kruskal_imp_init_code[code]:
  "kruskal_imp_init costs edges n = do {
     edge_array \<leftarrow> qsort_desc costs edges;
     uf \<leftarrow> ufsi_imp_init n;
     Heap_Monad.return \<lparr> edge_array = edge_array, edge_ptr = 0, result_list = [], uf_impl = uf \<rparr>
   }"
  unfolding kruskal_imp_init_def
  by (rule Kruskal_Imperative.kruskal_initial_state_impl_def[OF Kruskal_Imperative_empty_graph])

lemma kruskal_imp_loop_code[code]:
  "kruskal_imp_loop eps state = do {
     len \<leftarrow> Array.len (edge_array state);
     (if edge_ptr state < len then do {
        e \<leftarrow> Array.nth (edge_array state) (edge_ptr state);
        uv \<leftarrow> Array.nth eps e;
        b \<leftarrow> ufsi_imp_same_set (uf_impl state) (fst uv) (snd uv);
        (if \<not> b then do {
           uf \<leftarrow> ufsi_imp_union_size_c (uf_impl state) (fst uv) (snd uv);
           kruskal_imp_loop eps (state
             \<lparr>edge_ptr := edge_ptr state + 1, result_list := e # result_list state,
              uf_impl := uf\<rparr>)
         }
         else
           kruskal_imp_loop eps (state \<lparr>edge_ptr := edge_ptr state + 1\<rparr>))
      }
      else Heap_Monad.return state)
  }"
  unfolding kruskal_imp_loop_def
  by (rule Kruskal_Imperative.kruskal_imperative.simps[OF Kruskal_Imperative_empty_graph[of 0]])

lemma kruskal_imp_code[code]:
  "kruskal_imp costs eps edges n = do {
     state \<leftarrow> kruskal_imp_init costs edges n;
     state' \<leftarrow> kruskal_imp_loop eps state;
     Heap_Monad.return (result_list state')
   }"
  by (simp add: kruskal_imp_def kruskal_imp_init_def kruskal_imp_loop_def
      Kruskal_Imperative.kruskal_imperative'_def[OF Kruskal_Imperative_empty_graph])

lemmas [code] = ufsi_imp_same_set_def

text \<open>Programs that call the exported code need to construct the costs. Since @{const of_int} is a
  class operation, it is exported in the form of a constant specialised to @{typ rat}.\<close>

definition rat_of_int :: "int \<Rightarrow> rat" where
  "rat_of_int k = of_int k"

subsection \<open>Examples\<close>

text \<open>Edge \<open>e\<close> has the endpoints \<open>example_endpoints ! e\<close> and the cost \<open>example_costs ! e\<close>.\<close>

definition "example_endpoints = [(0::nat, 1::nat), (0, 2), (1, 2), (1, 3), (2, 3), (3, 4), (2, 4)]"

definition "example_costs = [4::rat, 1, 3, 2, 5, 7, 6]"

definition "kruskal_example = do {
  costs \<leftarrow> Array.of_list example_costs;
  eps \<leftarrow> Array.of_list example_endpoints;
  edges \<leftarrow> Array.of_list [0..<7];
  kruskal_imp costs eps edges 5
}"

ML_val \<open>@{code kruskal_example} ()\<close>

text \<open>A slightly larger example: a graph with 10 vertices and 20 edges. The costs are
  distinct, so the maximum-weight spanning tree is unique: it consists of the edges
  19, 18, 16, 9, 13, 2, 6, 11, 3 (in the order in which they are chosen) and has weight 128.\<close>

definition "example_endpoints_20 =
  [(0::nat, 1::nat), (0, 2), (0, 3), (1, 2), (1, 4), (2, 3), (2, 4), (2, 5), (3, 5), (3, 6),
   (4, 5), (4, 7), (5, 6), (5, 7), (5, 8), (6, 8), (6, 9), (7, 8), (7, 9), (8, 9)]"

definition "example_costs_20 =
  [7::rat, 3, 12, 9, 5, 4, 11, 8, 6, 15, 2, 10, 1, 14, 13, 16, 18, 17, 19, 20]"

definition "kruskal_example_20 = do {
  costs \<leftarrow> Array.of_list example_costs_20;
  eps \<leftarrow> Array.of_list example_endpoints_20;
  edges \<leftarrow> Array.of_list [0..<20];
  kruskal_imp costs eps edges 10
}"

ML_val \<open>@{code kruskal_example_20} ()\<close>

end
