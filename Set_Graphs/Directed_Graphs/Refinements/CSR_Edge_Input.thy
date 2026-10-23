theory CSR_Edge_Input
  imports
    CSR_Graph
    Data_Structures.Fixed_Univ_Map_Specs_Imp
begin

section \<open>Arrays Indexed by Keys\<close>

text \<open>An array of size \<open>N\<close> represents a function on a key set @{term K}, whose keys are mapped
      injectively into \<open>{..<N}\<close> by @{term idx}; entries are read through @{term val}. The functional
      model is the function itself. With \<open>idx = id\<close> this is a map on the edges of the input, which
      are numbers, or on its vertices.\<close>

definition arr_lookup :: "('k \<Rightarrow> 'b) \<Rightarrow> 'k \<Rightarrow> 'b" where
  "arr_lookup f k = f k"

definition arr_upd :: "('k \<Rightarrow> 'b) \<Rightarrow> 'k \<Rightarrow> 'b \<Rightarrow> ('k \<Rightarrow> 'b)" where
  "arr_upd f k x = fun_upd f k x"

lemma arr_lookup_upd[simp]: "arr_lookup (arr_upd f k x) = fun_upd (arr_lookup f) k x"
  by (simp add: arr_lookup_def arr_upd_def fun_eq_iff)

definition arr_lookup_imp :: "('k \<Rightarrow> nat) \<Rightarrow> 'b::heap array \<Rightarrow> 'k \<Rightarrow> 'b Heap" where
  "arr_lookup_imp ix a k = Array.nth a (ix k)"

definition arr_upd_imp :: "('k \<Rightarrow> nat) \<Rightarrow> 'b::heap array \<Rightarrow> 'k \<Rightarrow> 'b \<Rightarrow> unit Heap" where
  "arr_upd_imp ix a k x = do { _ \<leftarrow> Array.upd (ix k) x a; return () }"

locale key_array =
  fixes N :: nat
    and idx :: "'k \<Rightarrow> nat"
    and K :: "'k set"
    and val :: "'bi::heap \<Rightarrow> 'b"
  assumes idx_inj: "inj_on idx K"
    and idx_bound: "k \<in> K \<Longrightarrow> idx k < N"
begin

definition arr_assn :: "('k \<Rightarrow> 'b) \<Rightarrow> 'bi array \<Rightarrow> assn" where
  "arr_assn f a = (\<exists>\<^sub>Al. a \<mapsto>\<^sub>a l * \<up>(length l = N \<and> (\<forall>k\<in>K. val (l ! idx k) = f k)))"

lemma arr_lookup_imp_rule:
  "k \<in> K \<Longrightarrow> <arr_assn f a> arr_lookup_imp idx a k <\<lambda>x. arr_assn f a * \<up>(val x = arr_lookup f k)>"
  unfolding arr_assn_def arr_lookup_imp_def arr_lookup_def
  by (sep_auto simp: idx_bound)

lemma arr_upd_imp_rule:
  "k \<in> K \<Longrightarrow> <arr_assn f a> arr_upd_imp idx a k x <\<lambda>_. arr_assn (arr_upd f k (val x)) a>"
  unfolding arr_assn_def arr_upd_imp_def arr_upd_def
  by (sep_auto simp: idx_bound nth_list_update inj_on_eq_iff[OF idx_inj])

lemma arr_new_rule:
  "<emp> Array.new N x <\<lambda>a. arr_assn (\<lambda>_. val x) a>"
  unfolding arr_assn_def by (sep_auto simp: idx_bound)

sublocale arr: fixed_univ_map_imp K "\<lambda>_. True" arr_upd arr_lookup val arr_assn "arr_upd_imp idx"
    "arr_lookup_imp idx"
  by unfold_locales (simp_all add: arr_lookup_imp_rule arr_upd_imp_rule)

end


section \<open>The Input Edges in CSR Form\<close>

text \<open>The CSR buildup of the input (theory \<open>CSR_Graph\<close>) groups the edges by their first
      endpoint. Grouping them by the second endpoint gives the ingoing edges; it is the same
      buildup with another key.\<close>

global_interpretation csr_code_tgt: imp_csr_buildup_code n edge_has_next edge_cur edge_adv tgt_imp
    edge_cur
  for n
  defines csr_build_edges_tgt = csr_code_tgt.csr_build_imp
    and csr_build_into_edges_tgt = csr_code_tgt.csr_build_into
    and csr_count_edges_tgt = csr_code_tgt.count_imp
    and csr_prefix_sums_tgt = csr_code_tgt.prefix_imp
    and csr_init_edges_tgt = csr_code_tgt.init_E_imp
    and csr_fill_edges_tgt = csr_code_tgt.fill_imp
  done

declare csr_code_tgt.count_imp.simps[code] csr_code_tgt.prefix_imp.simps[code]
  csr_code_tgt.fill_imp.simps[code]

text \<open>A search that only reads the neighbours stores the heads in the CSR instead of the edges:
      the same buildup, grouped by the first endpoint, with the second endpoint as value.\<close>

global_interpretation csr_code_heads: imp_csr_buildup_code n edge_has_next edge_cur edge_adv src_imp
    tgt_imp
  for n
  defines csr_build_heads = csr_code_heads.csr_build_imp
    and csr_count_heads = csr_code_heads.count_imp
    and csr_prefix_sums_heads = csr_code_heads.prefix_imp
    and csr_init_heads = csr_code_heads.init_E_imp
    and csr_fill_heads = csr_code_heads.fill_imp
  done

declare csr_code_heads.count_imp.simps[code] csr_code_heads.prefix_imp.simps[code]
  csr_code_heads.fill_imp.simps[code]

text \<open>The input of @{locale csr_edge_spec}, where the key is read from the endpoint arrays by
      @{term key_imp}.\<close>

locale csr_edge_input = csr_edge_spec n fs ts key
  for n fs ts key +
  fixes key_imp :: "nat array \<times> nat array \<Rightarrow> nat \<Rightarrow> nat Heap"
  assumes key_imp_rule:
      "\<And>i Ei. i < length fs \<Longrightarrow>
         <ends_assn fs ts Ei> key_imp Ei i <\<lambda>k. ends_assn fs ts Ei * \<up>(k = key i)>"
begin

lemma edge_key_array: "key_array (length fs) id (edges fs)"
  by unfold_locales auto

lemma vert_key_array: "key_array n id (verts fs ts)"
  by unfold_locales (use verts_bound in auto)

sublocale ci: imp_csr_buildup "edge_next fs" "edge_seq fs" "\<lambda>_. True" key n 0
    edge_has_next edge_cur edge_adv key_imp edge_cur id "\<lambda>s si. si = s" "ends_assn fs ts"
proof (unfold_locales, goal_cases)
  case (1 s si c)
  have "(edge_next fs s \<noteq> None) = (s < length fs)" by (simp add: edge_next_def)
  with 1 show ?case by (cases c) (sep_auto simp: edge_has_next_def ends_assn_def)
next
  case (2 s si e s' c) then show ?case
    by (sep_auto simp: edge_cur_def edge_next_def split: if_splits)
next
  case (3 s si e s' c) then show ?case
    by (sep_auto simp: edge_adv_def edge_next_def split: if_splits)
next
  case (4 e c) then show ?case
    by (sep_auto heap: key_imp_rule simp: edge_seq_def)
next
  case (5 e c) then show ?case
    by (sep_auto simp: edge_cur_def)
qed

sublocale graph: csr_graph_imp n "verts fs ts" inp.B_spec inp.E_spec
  by (rule csr_graph_imp.intro[OF graph.csr_graph_axioms])

lemma csr_build_rule:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts> ci.csr_build_imp (Fa, Ta) 0
   <\<lambda>(Ba, Ea). Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Ba \<mapsto>\<^sub>a inp.B_spec * Ea \<mapsto>\<^sub>a inp.E_spec>"
  using ci.csr_build_imp_rule[of "(Fa, Ta)" 0] by (simp add: ends_assn_def)

text \<open>The build into arrays allocated by the caller, one cell per edge.\<close>

lemma csr_build_into_rule:
  "length Es = length fs \<Longrightarrow>
   <Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Ba \<mapsto>\<^sub>a replicate (Suc n) 0 * Ea \<mapsto>\<^sub>a Es> ci.csr_build_into (Fa, Ta) 0 Ba Ea
   <\<lambda>_. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Ba \<mapsto>\<^sub>a inp.B_spec * Ea \<mapsto>\<^sub>a inp.E_spec>"
  using ci.csr_build_into_rule[of "(Fa, Ta)" Ba Ea Es 0]
  by (simp add: ends_assn_def inp.es_def edge_seq_def mult.assoc)

text \<open>The same buildup storing the second endpoints instead of the edges.\<close>

sublocale ch: imp_csr_buildup "edge_next fs" "edge_seq fs" "\<lambda>_. True" key n 0
    edge_has_next edge_cur edge_adv key_imp tgt_imp "e_tgt fs ts" "\<lambda>s si. si = s" "ends_assn fs ts"
proof (unfold_locales, goal_cases)
  case (1 s si c) then show ?case by (rule ci.has_next_rule)
next
  case (2 s si e s' c) then show ?case by (rule ci.cur_rule)
next
  case (3 s si e s' c) then show ?case by (rule ci.adv_rule)
next
  case (4 e c) then show ?case by (rule ci.key_rule)
next
  case (5 e c) then show ?case
    using ts_length by (intro tgt_imp_rule) (simp_all add: edge_seq_def)
qed

lemma csr_build_heads_rule:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts> ch.csr_build_imp (Fa, Ta) 0
   <\<lambda>(Ba, Ea). Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Ba \<mapsto>\<^sub>a inp.B_spec * Ea \<mapsto>\<^sub>a map (e_tgt fs ts) inp.E_spec>"
  using ch.csr_build_imp_rule[of "(Fa, Ta)" 0] by (simp add: ends_assn_def)

text \<open>The second endpoints grouped by the key are the blocks of a CSR. They need not be
      distinct.\<close>

sublocale heads: csr_graph_blocks_imp n "{..<n}" inp.B_spec "map (e_tgt fs ts) inp.E_spec"
  by unfold_locales (simp_all add: inp.length_B_spec graph.B_mono B_spec_bound)

end

text \<open>The two instances: grouped by the first endpoint, the code is @{const csr_build_edges},
      grouped by the second, @{const csr_build_edges_tgt}.\<close>

lemma csr_build_edges_src:
  "imp_csr_buildup_code.csr_build_imp n edge_has_next edge_cur edge_adv src_imp edge_cur =
   csr_build_edges n"
  by (simp add: csr_build_edges_def)

lemma csr_build_edges_tgt:
  "imp_csr_buildup_code.csr_build_imp n edge_has_next edge_cur edge_adv tgt_imp edge_cur =
   csr_build_edges_tgt n"
  by (simp add: csr_build_edges_tgt_def)

lemma csr_build_into_edges_src:
  "imp_csr_buildup_code.csr_build_into n edge_has_next edge_cur edge_adv src_imp edge_cur =
   csr_build_into_edges n"
  by (simp add: csr_build_into_edges_def)

lemma csr_build_into_edges_tgt:
  "imp_csr_buildup_code.csr_build_into n edge_has_next edge_cur edge_adv tgt_imp edge_cur =
   csr_build_into_edges_tgt n"
  by (simp add: csr_build_into_edges_tgt_def)

lemma csr_build_heads:
  "imp_csr_buildup_code.csr_build_imp n edge_has_next edge_cur edge_adv src_imp tgt_imp =
   csr_build_heads n"
  by (simp add: csr_build_heads_def)

end
