theory Matroid_Intersection_Exchange_Graph_CSR
  imports Matroid_Intersection_Exchange_Graph "Graph_Algorithms_Dev.BFS_Instantiation"
begin

section \<open>The Exchange Graph Search on the CSR BFS\<close>

text \<open>Glue only. The graph is given by @{const build_nhlists}, the neighbour map of the CSR
  arrays of an edge list, and the BFS parameters are exactly those of @{locale BFS_lists_instance},
  whose imperative refinement is the CSR BFS of @{theory Graph_Algorithms_Dev.BFS_Instantiation}.
  The sources are reversed as in @{locale bfs_csr}. The matroids and their oracles stay
  abstract.\<close>

subsection \<open>The BFS on Built Graphs\<close>

lemma build_nhlists_edge:
  "(\<exists> vs. build_nhlists es u = Some vs \<and> v \<in> set vs) \<longleftrightarrow> (u, v) \<in> set es"
  by (auto simp add: build_nhlists_def nbrs_def filter_empty_conv)

lemma finite_Vs_build_nhlists: "finite (BFS_subprocedures_lists.Vs (build_nhlists es))"
proof-
  have "BFS_subprocedures_lists.Vs (build_nhlists es) = dVs (set es)"
    unfolding BFS_subprocedures_lists.Vs_def[OF BFS_subprocedures_lists_bset] dVs_def 
    by (simp add: build_nhlists_edge)
  thus ?thesis
    by (simp add: finite_vertices_iff)
qed

definition "nh_bound es = Suc (Max (Set.insert 0 (BFS_subprocedures_lists.Vs (build_nhlists es))))"

lemma Vs_build_nhlists_bound: "BFS_subprocedures_lists.Vs (build_nhlists es) \<subseteq> {..<nh_bound es}"
proof
  fix x assume x: "x \<in> BFS_subprocedures_lists.Vs (build_nhlists es)"
  have "x \<le> Max (Set.insert 0 (BFS_subprocedures_lists.Vs (build_nhlists es)))"
    by (rule Max_ge, simp add: finite_Vs_build_nhlists, rule insertI2[OF x])
  then show "x \<in> {..<nh_bound es}"
    unfolding nh_bound_def by simp
qed

lemma bfs_build_nhlists:
  "\<exists> exp_tree nfc dist_invar parent_invar. 
     BFS_3.BFS_distance_parents (\<lambda> x. None) (\<lambda> x G. G(x := None)) Cons (\<lambda> xs x. x \<in> set xs) set hd
       (\<lambda> x N G. G(x := Some N)) (\<lambda> G. True) [] (\<lambda> x xs. filter (\<lambda> y. x \<noteq> y) xs) (\<lambda> _. True)
       append (\<lambda> xs ys. filter (\<lambda> y. y \<in> set ys) xs) (\<lambda> xs ys. filter (\<lambda> y. y \<notin> set ys) xs)
       (build_nhlists es) exp_tree nfc distinct id (\<lambda> d x. d x) dist_invar (\<lambda> G x. G x)
       (\<lambda> d S n. \<lambda> y. if y \<in> set S then n else d y)
       (BFS_subprocedures_lists.next_frontier_current_parents (build_nhlists es))
       (\<lambda> p x. p x) parent_invar id"
proof-
  interpret inst: BFS_lists_instance where is_visited_set = bset_assn
    and visited_memb = bset_memb and distinct_ins = bset_ins and iterate_neighbourhood = bfs_nbs
    and graph_assn = csr3_assn and G = "build_nhlists es" and Gi = Gi and srcs = "[]"
    and N = "nh_bound es" and Fr = Fr and Bf = Bf and Da = Da and Pa = Pa for Gi Fr Bf Da Pa
    using BFS_subprocedures_lists_bset Vs_build_nhlists_bound
    by (auto intro!: BFS_lists_instance.intro BFS_lists_instance_axioms.intro)
  show ?thesis
    using inst.imp_bfs.BFS_distance_parents_axioms unfolding fun_upd_def by blast
qed

lemma Pair_Graph_Specs_lists:
  "Pair_Graph_Specs (\<lambda> x. None) (\<lambda> x G. G(x := None)) (\<lambda> G x. G x) Cons 
          (\<lambda> xs x. x \<in> set xs) set hd (\<lambda> x N G. G(x := Some N)) (\<lambda> G. True) [] 
          (\<lambda> x xs. filter (\<lambda> y. (x::nat) \<noteq> y) xs) (\<lambda> _. True)"
proof-
  interpret inst: BFS_lists_instance where is_visited_set = bset_assn
    and visited_memb = bset_memb and distinct_ins = bset_ins and iterate_neighbourhood = bfs_nbs
    and graph_assn = csr3_assn and G = "build_nhlists []" and Gi = Gi and srcs = "[]"
    and N = "nh_bound []" and Fr = Fr and Bf = Bf and Da = Da and Pa = Pa for Gi Fr Bf Da Pa
    using BFS_subprocedures_lists_bset Vs_build_nhlists_bound
    by (auto intro!: BFS_lists_instance.intro BFS_lists_instance_axioms.intro)
  show ?thesis
    unfolding fun_upd_def by (rule inst.Graph.Pair_Graph_Specs_axioms)
qed

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
  "\<lambda> d S n. \<lambda> y. if y \<in> set S then n else d y" "\<lambda> d x. d x" "id :: nat \<Rightarrow> nat" "\<lambda> p x. p x"
  BFS_subprocedures_lists.next_frontier_current_parents build_nhlists .

end

subsection \<open>Correctness\<close>

locale unweighted_intersection_exchange_csr =
  unweighted_intersection_exchange_csr_spec set_insert set_delete to_set set_invar set_empty set_memb
    carrier_list orcl_prep1 ins_orcl1 exch_orcl1 orcl_prep2 ins_orcl2 exch_orcl2 +
  unweighted_intersection_exchange_matroids carrier indep1 indep2 orcl_prep1 ins_orcl1 exch_orcl1
    orcl_prep2 ins_orcl2 exch_orcl2 to_set set_invar set_insert set_delete set_empty set_memb
    carrier_list
  for set_insert set_delete to_set set_invar set_empty set_memb carrier_list 
    orcl_prep1 ins_orcl1 exch_orcl1 orcl_prep2 ins_orcl2 exch_orcl2 carrier indep1 indep2
begin

sublocale csr: unweighted_intersection_exchange
  where set_insert = set_insert and set_delete = set_delete and to_set = to_set 
    and set_invar = set_invar and set_empty = set_empty and set_memb = set_memb 
    and carrier_list = carrier_list and orcl_prep1 = orcl_prep1 and ins_orcl1 = ins_orcl1 
    and exch_orcl1 = exch_orcl1 and orcl_prep2 = orcl_prep2 and ins_orcl2 = ins_orcl2
    and exch_orcl2 = exch_orcl2 and vset_empty = Nil and isin = "\<lambda> xs x. x \<in> set xs" 
    and vset_of_list = rev and some_dist = "id :: nat \<Rightarrow> nat"
    and set_all_dists_in_set = "\<lambda> d S n. \<lambda> y. if y \<in> set S then n else d y"
    and dist_lookup = "\<lambda> d x. d x" and some_parent = "id :: nat \<Rightarrow> nat" 
    and parent_lookup = "\<lambda> p x. p x"
    and next_frontier_current_parents = BFS_subprocedures_lists.next_frontier_current_parents
    and build_graph = build_nhlists and carrier = carrier and indep1 = indep1 and indep2 = indep2
    and insert = Cons and t_set = set and sel = hd 
    and vset_delete = "\<lambda> x xs. filter (\<lambda> y. x \<noteq> y) xs" and vset_inv = "\<lambda> _. True"
    and union = append and inter = "\<lambda> xs ys. filter (\<lambda> y. y \<in> set ys) xs"
    and diff = "\<lambda> xs ys. filter (\<lambda> y. y \<notin> set ys) xs" and vset_inv2 = distinct
proof(intro unweighted_intersection_exchange.intro unweighted_intersection_exchange_axioms.intro)
  interpret inst: BFS_lists_instance where is_visited_set = bset_assn
    and visited_memb = bset_memb and distinct_ins = bset_ins and iterate_neighbourhood = bfs_nbs
    and graph_assn = csr3_assn and G = "build_nhlists []" and Gi = Gi and srcs = "[]"
    and N = "nh_bound []" and Fr = Fr and Bf = Bf and Da = Da and Pa = Pa for Gi Fr Bf Da Pa
    using BFS_subprocedures_lists_bset Vs_build_nhlists_bound
    by (auto intro!: BFS_lists_instance.intro BFS_lists_instance_axioms.intro)
  show "unweighted_intersection_exchange_matroids carrier indep1 indep2 orcl_prep1 ins_orcl1 
          exch_orcl1 orcl_prep2 ins_orcl2 exch_orcl2 to_set set_invar set_insert set_delete set_empty 
          set_memb carrier_list"
    by (rule unweighted_intersection_exchange_matroids_axioms)
  show "Pair_Graph_Specs (\<lambda> x. None) (\<lambda> x G. G(x := None)) (\<lambda> G x. G x) Cons 
          (\<lambda> xs x. x \<in> set xs) set hd (\<lambda> x N G. G(x := Some N)) (\<lambda> G. True) [] 
          (\<lambda> x xs. filter (\<lambda> y. (x::nat) \<noteq> y) xs) (\<lambda> _. True)"
    by (rule Pair_Graph_Specs_lists)
  show "Set2 [] (\<lambda> x xs. filter (\<lambda> y. (x::nat) \<noteq> y) xs) (\<lambda> xs x. x \<in> set xs) set (\<lambda> _. True) 
          Cons append (\<lambda> xs ys. filter (\<lambda> y. y \<in> set ys) xs) 
          (\<lambda> xs ys. filter (\<lambda> y. y \<notin> set ys) xs)"
    by (rule inst.set_ops.Set2_axioms)
  fix es
  show "inst.Graph.graph_inv (build_nhlists es)"
    by (rule inst.Graph.graph_invI) (rule TrueI)+
  have "{v. build_nhlists es v \<noteq> None} \<subseteq> fst ` set es"
    unfolding dom_def[symmetric] build_nhlists_dom nbrs_def map_is_Nil_conv filter_empty_conv
    by blast
  thus "inst.Graph.finite_graph (build_nhlists es)"
    by (intro inst.Graph.finite_graphI finite_subset[OF _ finite_imageI[OF finite_set]])
  show "inst.Graph.finite_vsets (build_nhlists es)"
    by (rule inst.Graph.finite_vsetsI) (rule finite_set)
  show "inst.Graph.digraph_abs (build_nhlists es) = set es"
  proof(rule set_eqI)
    fix e :: "nat \<times> nat"
    obtain u v where e: "e = (u, v)" 
      by (cases e)
    have "v \<in> set (case build_nhlists es u of None \<Rightarrow> [] | Some vs \<Rightarrow> vs) \<longleftrightarrow> 
          (\<exists> vs. build_nhlists es u = Some vs \<and> v \<in> set vs)"
    proof(cases "build_nhlists es u")
      case None
      show ?thesis
        unfolding None option.case(1) list.set(1) using option.distinct(1) by blast
    next
      case (Some vs)
      show ?thesis
        unfolding Some option.case(2) using option.inject by blast
    qed
    thus "e \<in> inst.Graph.digraph_abs (build_nhlists es) \<longleftrightarrow> e \<in> set es"
      unfolding e inst.Graph.digraph_abs_def inst.Graph.neighbourhood_def mem_Collect_eq 
                case_prod_conv build_nhlists_edge[symmetric] .
  qed
  show "\<exists> exp_tree nfc dist_invar parent_invar. 
     BFS_3.BFS_distance_parents (\<lambda> x. None) (\<lambda> x G. G(x := None)) Cons (\<lambda> xs x. x \<in> set xs) set hd
       (\<lambda> x N G. G(x := Some N)) (\<lambda> G. True) [] (\<lambda> x xs. filter (\<lambda> y. x \<noteq> y) xs) (\<lambda> _. True)
       append (\<lambda> xs ys. filter (\<lambda> y. y \<in> set ys) xs) (\<lambda> xs ys. filter (\<lambda> y. y \<notin> set ys) xs)
       (build_nhlists es) exp_tree nfc distinct id (\<lambda> d x. d x) dist_invar (\<lambda> G x. G x)
       (\<lambda> d S n. \<lambda> y. if y \<in> set S then n else d y)
       (BFS_subprocedures_lists.next_frontier_current_parents (build_nhlists es))
       (\<lambda> p x. p x) parent_invar id"
    by (rule bfs_build_nhlists)
  fix xs :: "nat list"
  assume "distinct xs"
  thus "distinct (rev xs)" "set (rev xs) = set xs"
    by (simp only: distinct_rev set_rev)+
qed

lemmas total_correctness = csr.total_correctness

end

end

