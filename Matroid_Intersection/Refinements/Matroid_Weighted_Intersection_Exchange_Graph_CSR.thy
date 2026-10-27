theory Matroid_Weighted_Intersection_Exchange_Graph_CSR
  imports Matroid_Weighted_Intersection_Exchange_Graph Matroid_Intersection_Exchange_Graph_CSR
begin

section \<open>The Weighted Exchange Graph Search on the CSR BFS\<close>

text \<open>Glue only, as @{theory Matroid_Intersection.Matroid_Intersection_Exchange_Graph_CSR}: the
  weighted exchange theory with the list BFS parameters of the unweighted CSR theory, and lists as
  reachable sets. The unweighted part of the correctness proof is taken from there.\<close>

subsection \<open>Code\<close>

locale weighted_intersection_exchange_csr_spec =
  unweighted_intersection_exchange_csr_spec set_insert set_delete to_set set_invar set_empty set_memb
    carrier_list orcl_prep1 ins_orcl1 exch_orcl1 orcl_prep2 ins_orcl2 exch_orcl2
  for set_insert :: "nat \<Rightarrow> 'mset \<Rightarrow> 'mset"
    and set_delete to_set set_invar set_empty set_memb carrier_list
      orcl_prep1 ins_orcl1 exch_orcl1 orcl_prep2 ins_orcl2 exch_orcl2 +
  fixes c_lookup :: "'cmap \<Rightarrow> nat \<Rightarrow> real"
    and c_shift :: "nat list \<Rightarrow> real \<Rightarrow> 'cmap \<Rightarrow> 'cmap"
    and c_zero :: "'cmap"
begin

sublocale csr: weighted_intersection_exchange_spec
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
    and build_graph = nbrs_map and c_lookup = c_lookup and c_shift = c_shift
    and c_zero = c_zero and vset_insert = Cons .

end

subsection \<open>Correctness\<close>

locale weighted_intersection_exchange_csr =
  weighted_intersection_exchange_csr_spec set_insert set_delete to_set set_invar set_empty set_memb
    carrier_list orcl_prep1 ins_orcl1 exch_orcl1 orcl_prep2 ins_orcl2 exch_orcl2
    c_lookup c_shift c_zero +
  unweighted_intersection_exchange_csr set_insert set_delete to_set set_invar set_empty set_memb
    carrier_list orcl_prep1 ins_orcl1 exch_orcl1 orcl_prep2 ins_orcl2 exch_orcl2 carrier indep1
    indep2
  for set_insert set_delete to_set set_invar set_empty set_memb carrier_list orcl_prep1 ins_orcl1
    exch_orcl1 orcl_prep2 ins_orcl2 exch_orcl2
    and c_lookup :: "'cmap \<Rightarrow> nat \<Rightarrow> real" and c_shift c_zero carrier indep1 indep2 +
  fixes c_invar :: "'cmap \<Rightarrow> bool"
  assumes c_zero: "c_invar c_zero" "c_lookup c_zero = (\<lambda> _. 0)"
  assumes c_shift:
    "\<And> R e c. c_invar c \<Longrightarrow> c_invar (c_shift R e c)"
    "\<And> R e c. c_invar c \<Longrightarrow>
       c_lookup (c_shift R e c) = (\<lambda> x. if x \<in> set R then c_lookup c x + e else c_lookup c x)"
begin

sublocale csr: weighted_intersection_exchange
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
    and build_graph = nbrs_map and c_lookup = c_lookup and c_shift = c_shift
    and c_zero = c_zero and vset_insert = Cons
    and carrier = carrier and indep1 = indep1 and indep2 = indep2
    and t_set = set and sel = hd and vset_delete = "\<lambda> x xs. filter (\<lambda> y. x \<noteq> y) xs"
    and vset_inv = "\<lambda> _. True" and union = append and inter = "\<lambda> xs ys. filter (\<lambda> y. y \<in> set ys) xs"
    and diff = "\<lambda> xs ys. filter (\<lambda> y. y \<notin> set ys) xs" and vset_inv2 = distinct
    and c_invar = c_invar
  by (unfold_locales; simp add: c_zero c_shift)

lemmas total_correctness = csr.total_correctness

end

end
