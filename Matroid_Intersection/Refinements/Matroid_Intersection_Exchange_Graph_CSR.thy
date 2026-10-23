theory Matroid_Intersection_Exchange_Graph_CSR
  imports Matroid_Intersection_Exchange_Graph "Graph_Algorithms_Dev.BFS_Instantiation"
    Directed_Set_Graphs.CSR_Neighbour_Lists
begin

section \<open>The Exchange Graph Search on the CSR BFS\<close>

text \<open>Glue only. The graph is given by @{term nbrs_map}, the neighbour map of the grouped CSR of
  an edge list, and the BFS parameters are exactly those of @{locale BFS_lists_instance}, whose
  imperative refinement is the BFS of @{theory Graph_Algorithms_Dev.BFS_Refinement}. The sources
  are reversed. The matroids and their oracles stay abstract.\<close>

subsection \<open>The BFS on Built Graphs\<close>

definition "nh_bound es = Suc (Max (Set.insert 0 (dVs (set es))))"

lemma dVs_bound: "dVs (set es) \<subseteq> {..<nh_bound es}"
proof
  fix x assume x: "x \<in> dVs (set es)"
  have "x \<le> Max (Set.insert 0 (dVs (set es)))"
    by (rule Max_ge, simp add: finite_vertices_iff, rule insertI2[OF x])
  then show "x \<in> {..<nh_bound es}"
    unfolding nh_bound_def by simp
qed

text \<open>The graph of an edge list: the neighbour map of its CSR grouped by sources
  (@{locale csr_concat} of @{const nbrs}), with the bound @{const nh_bound}.\<close>

definition "nbrs_map es = csr_blocks.csr_map (nh_bound es)
  (map (csr_start (nbrs es)) [0..<Suc (nh_bound es)])
  (\<lambda>v. map (csr_start (nbrs es)) [0..<Suc (nh_bound es)] ! Suc v)
  (csr_entries (nbrs es) (nh_bound es))"

lemma mem_nbrs: "v \<in> set (nbrs es u) \<longleftrightarrow> (u, v) \<in> set es"
  unfolding nbrs_def by force

lemma case_nbrs_map: "(case nbrs_map es v of None \<Rightarrow> [] | Some vs \<Rightarrow> vs) = nbrs es v"
proof -
  interpret g: csr_concat "nbrs es" "nh_bound es" .
  show ?thesis
  proof (cases "v < nh_bound es")
    case True
    show ?thesis
      unfolding nbrs_map_def g.csr_map_def g.csr_list_blk[OF True] using True by (simp only: if_True option.case)
  next
    case False
    have "nbrs es v = []"
      unfolding nbrs_def map_is_Nil_conv filter_empty_conv
    proof (intro ballI notI)
      fix e
      assume e: "e \<in> set es" "fst e = v"
      have "v \<in> dVs (set es)"
        unfolding e(2)[symmetric] by (rule dVsI(1)[of "fst e" "snd e"]) (simp only: prod.collapse e(1))
      then show False
        using subsetD[OF dVs_bound[of es]] False by simp
    qed
    then show ?thesis
      unfolding nbrs_map_def g.csr_map_def if_not_P[OF False] option.case(1) by (rule sym)
  qed
qed

lemma nbrs_map_edge: "(\<exists>vs. nbrs_map es u = Some vs \<and> v \<in> set vs) \<longleftrightarrow> (u, v) \<in> set es"
  using case_nbrs_map[of es u] by (cases "nbrs_map es u") (auto simp: mem_nbrs[symmetric])

lemma nbrs_map_set: "set (case nbrs_map es u of None \<Rightarrow> [] | Some vs \<Rightarrow> vs) = {v. (u, v) \<in> set es}"
  unfolding case_nbrs_map mem_nbrs[symmetric] by simp

lemma finite_nbrs_map_dom: "finite (dom (nbrs_map es))"
proof -
  interpret g: csr_concat "nbrs es" "nh_bound es" .
  show ?thesis
  proof (rule finite_subset[OF subsetI finite_lessThan])
    fix x
    assume "x \<in> dom (nbrs_map es)"
    then show "x \<in> {..<nh_bound es}"
      unfolding dom_def mem_Collect_eq nbrs_map_def g.csr_map_def lessThan_iff
      by (cases "x < nh_bound es") (simp_all only: if_True if_False simp_thms option.distinct)
  qed
qed

lemma nbrs_map_edges: "{(u, v). v \<in> set (case nbrs_map es u of None \<Rightarrow> [] | Some vs \<Rightarrow> vs)} = set es"
  unfolding nbrs_map_set by (rule set_eqI) (simp only: mem_Collect_eq case_prod_beta prod.collapse)

text \<open>The graph of an edge list below \<open>N\<close> is a graph of the BFS of the library
  (@{locale bfs_iterator_arrays}), e.g.\ with an iterator that is never run. So its functional
  facts hold for it.\<close>

lemma nbrs_map_bfs:
  assumes "dVs (set es) \<subseteq> {..<N}"
  shows "bfs_iterator_arrays N (nbrs_map es) (\<lambda>_ _ _ acc. return acc) (\<lambda>_ :: unit. false)"
  by (rule bfs_iterator_arrays_graph) (unfold nbrs_map_edges, rule assms, rule finite_nbrs_map_dom)


subsection \<open>Code\<close>

locale unweighted_intersection_exchange_csr_spec =
  fixes set_insert :: "nat \<Rightarrow> 'mset \<Rightarrow> 'mset"
    and set_delete :: "nat \<Rightarrow> 'mset \<Rightarrow> 'mset"
    and to_set :: "'mset \<Rightarrow> nat set"
    and set_invar :: "'mset \<Rightarrow> bool"
    and set_empty :: "'mset"
    and set_memb :: "nat \<Rightarrow> 'mset \<Rightarrow> bool"
    and carrier_list :: "nat list"
    and orcl_prep1 :: "'mset \<Rightarrow> 'o1"
    and ins_orcl1 :: "'o1 \<Rightarrow> nat \<Rightarrow> bool"
    and exch_orcl1 :: "'o1 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
    and orcl_prep2 :: "'mset \<Rightarrow> 'o2"
    and ins_orcl2 :: "'o2 \<Rightarrow> nat \<Rightarrow> bool"
    and exch_orcl2 :: "'o2 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
begin

sublocale csr: unweighted_intersection_exchange_spec set_insert set_delete to_set set_invar 
  set_empty set_memb carrier_list orcl_prep1 ins_orcl1 exch_orcl1 orcl_prep2 ins_orcl2 exch_orcl2
  "[]" "\<lambda> xs x. x \<in> set xs" rev "id :: nat \<Rightarrow> nat" 
  "\<lambda> d S n. \<lambda> y. if y \<in> set S then n else d y" "\<lambda> d x. d x" parent_array.pa_init
  "parent_array.pa_get_path (length carrier_list)"
  "BFS_subprocedures_lists.next_frontier_current_parents parent_array.pa_extend" nbrs_map .

end

subsection \<open>Correctness\<close>

locale unweighted_intersection_exchange_csr =
  unweighted_intersection_exchange_csr_spec set_insert set_delete to_set set_invar set_empty set_memb
    carrier_list orcl_prep1 ins_orcl1 exch_orcl1 orcl_prep2 ins_orcl2 exch_orcl2 +
  unweighted_intersection_exchange_matroids carrier indep1 indep2 orcl_prep1 ins_orcl1 exch_orcl1
    orcl_prep2 ins_orcl2 exch_orcl2 to_set set_invar set_insert set_delete set_empty set_memb
    carrier_list
  for set_insert set_delete to_set set_invar set_empty set_memb carrier_list 
    orcl_prep1 ins_orcl1 exch_orcl1 orcl_prep2 ins_orcl2 exch_orcl2 carrier indep1 indep2 +
  assumes carrier_bound: "carrier \<subseteq> {..<length carrier_list}"
begin

sublocale csr: unweighted_intersection_exchange
  where set_insert = set_insert and set_delete = set_delete and to_set = to_set 
    and set_invar = set_invar and set_empty = set_empty and set_memb = set_memb 
    and carrier_list = carrier_list and orcl_prep1 = orcl_prep1 and ins_orcl1 = ins_orcl1 
    and exch_orcl1 = exch_orcl1 and orcl_prep2 = orcl_prep2 and ins_orcl2 = ins_orcl2
    and exch_orcl2 = exch_orcl2 and vset_empty = Nil and isin = "\<lambda> xs x. x \<in> set xs" 
    and vset_of_list = rev and some_dist = "id :: nat \<Rightarrow> nat"
    and set_all_dists_in_set = "\<lambda> d S n. \<lambda> y. if y \<in> set S then n else d y"
    and dist_lookup = "\<lambda> d x. d x" and parent_init = parent_array.pa_init
    and get_path = "parent_array.pa_get_path (length carrier_list)"
    and next_frontier_current_parents =
          "BFS_subprocedures_lists.next_frontier_current_parents parent_array.pa_extend"
    and build_graph = nbrs_map and carrier = carrier and indep1 = indep1 and indep2 = indep2
    and insert = Cons and t_set = set and sel = hd 
    and vset_delete = "\<lambda> x xs. filter (\<lambda> y. x \<noteq> y) xs" and vset_inv = "\<lambda> _. True"
    and union = append and inter = "\<lambda> xs ys. filter (\<lambda> y. y \<in> set ys) xs"
    and diff = "\<lambda> xs ys. filter (\<lambda> y. y \<notin> set ys) xs" and vset_inv2 = distinct
proof(intro unweighted_intersection_exchange.intro unweighted_intersection_exchange_axioms.intro)
  have b0: "bfs_iterator_arrays 0 (nbrs_map []) (\<lambda>_ _ _ acc. return acc) (\<lambda>_ :: unit. false)"
    by (rule nbrs_map_bfs) (simp only: list.set(1) dVs_empty empty_subsetI)
  interpret g: Pair_Graph_Specs "\<lambda> x. None" "\<lambda> x G. fun_upd G x None" "\<lambda> G x. G x" Cons
    "\<lambda> xs x. x \<in> set xs" set hd "\<lambda> x N G. fun_upd G x (Some N)" "\<lambda> G. True" "[]"
    "\<lambda> x xs. filter (\<lambda> y. (x::nat) \<noteq> y) xs" "\<lambda> _. True"
    unfolding fun_upd_def by (rule bfs_iterator_arrays.graph_specs[OF b0])
  show "unweighted_intersection_exchange_matroids carrier indep1 indep2 orcl_prep1 ins_orcl1 
          exch_orcl1 orcl_prep2 ins_orcl2 exch_orcl2 to_set set_invar set_insert set_delete set_empty 
          set_memb carrier_list"
    by (rule unweighted_intersection_exchange_matroids_axioms)
  show "Pair_Graph_Specs (\<lambda> x. None) (\<lambda> x G. fun_upd G x None) (\<lambda> G x. G x) Cons 
          (\<lambda> xs x. x \<in> set xs) set hd (\<lambda> x N G. fun_upd G x (Some N)) (\<lambda> G. True) [] 
          (\<lambda> x xs. filter (\<lambda> y. (x::nat) \<noteq> y) xs) (\<lambda> _. True)"
    by (rule g.Pair_Graph_Specs_axioms)
  show "Set2 [] (\<lambda> x xs. filter (\<lambda> y. (x::nat) \<noteq> y) xs) (\<lambda> xs x. x \<in> set xs) set (\<lambda> _. True) 
          Cons append (\<lambda> xs ys. filter (\<lambda> y. y \<in> set ys) xs) 
          (\<lambda> xs ys. filter (\<lambda> y. y \<notin> set ys) xs)"
    by (rule bfs_iterator_arrays.set_specs[OF b0])
  fix es
  show "g.graph_inv (nbrs_map es)"
    by (rule g.graph_invI) (rule TrueI)+
  show "g.finite_graph (nbrs_map es)"
    by (rule g.finite_graphI) (simp only: dom_def[symmetric] finite_nbrs_map_dom)
  show "g.finite_vsets (nbrs_map es)"
    by (rule g.finite_vsetsI) (rule finite_set)
  show "g.digraph_abs (nbrs_map es) = set es"
    unfolding g.digraph_abs_def g.neighbourhood_def by (rule nbrs_map_edges)
  show "set es \<subseteq> carrier \<times> carrier \<Longrightarrow>
     \<exists> exp_tree nfc dist_invar parent_abstract parent_invar par_U par_roots. 
     BFS_3.BFS_distance_parents (\<lambda> x. None) (\<lambda> x G. G(x := None)) Cons (\<lambda> xs x. x \<in> set xs) set hd
       (\<lambda> x N G. G(x := Some N)) (\<lambda> G. True) [] (\<lambda> x xs. filter (\<lambda> y. x \<noteq> y) xs) (\<lambda> _. True)
       append (\<lambda> xs ys. filter (\<lambda> y. y \<in> set ys) xs) (\<lambda> xs ys. filter (\<lambda> y. y \<notin> set ys) xs)
       (nbrs_map es) exp_tree nfc distinct id (\<lambda> d x. d x) dist_invar (\<lambda> G x. G x)
       (\<lambda> d S n. \<lambda> y. if y \<in> set S then n else d y) parent_abstract parent_invar par_U
       (parent_array.pa_get_path (length carrier_list)) par_roots parent_array.pa_init
       (BFS_subprocedures_lists.next_frontier_current_parents parent_array.pa_extend (nbrs_map es))"
  proof (rule bfs_iterator_arrays.distance_parents[OF nbrs_map_bfs])
    assume es: "set es \<subseteq> carrier \<times> carrier"
    have fs: "fst e \<in> carrier" "snd e \<in> carrier" if "e \<in> set es" for e
      using subsetD[OF es that] by (simp_all only: mem_Times_iff)
    have "dVs (set es) \<subseteq> carrier"
      unfolding dVs_eq by (intro Un_least image_subsetI fs)
    then show "dVs (set es) \<subseteq> {..<length carrier_list}"
      using carrier_bound by (rule order.trans)
  qed
  fix xs :: "nat list"
  assume "distinct xs"
  thus "distinct (rev xs)" "set (rev xs) = set xs"
    by (simp only: distinct_rev set_rev)+
qed

lemmas total_correctness = csr.total_correctness

end

end

