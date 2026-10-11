theory CSR_Edge_Input
  imports
    CSR_Graph
    Data_Structures.Fixed_Univ_Map_Specs_Imp
begin

section \<open>Arrays Indexed by Keys\<close>

text \<open>An array of size \<open>N\<close> represents a function on a key set @{term K}, whose keys are mapped
      injectively into \<open>{..<N}\<close> by @{term idx}; entries are read through @{term val}. The functional
      model is the function itself. With \<open>idx = e_id\<close> this is a map on the edges of the input,
      with \<open>idx = id\<close> a map on its vertices.\<close>

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

definition edge_key_tgt :: "nat array \<times> nat array \<Rightarrow> edge \<Rightarrow> nat Heap" where
  "edge_key_tgt _ e = return (e_tgt e)"

global_interpretation csr_code_tgt: imp_csr_buildup_code n edge_has_next edge_cur edge_adv edge_key_tgt
    edge_val
  for n
  defines csr_build_edges_tgt = csr_code_tgt.csr_build_imp
    and csr_count_edges_tgt = csr_code_tgt.count_imp
    and csr_prefix_sums_tgt = csr_code_tgt.prefix_imp
    and csr_init_edges_tgt = csr_code_tgt.init_E_imp
    and csr_fill_edges_tgt = csr_code_tgt.fill_imp
  done

declare csr_code_tgt.count_imp.simps[code] csr_code_tgt.prefix_imp.simps[code]
  csr_code_tgt.fill_imp.simps[code]

text \<open>The input: \<open>n\<close> bounds the vertices, @{term fs} and @{term ts} are the endpoint lists. The
      CSR form groups the edges by @{term key}, one of the two endpoints, computed by
      @{term key_imp}. The neighbourhoods are indexed by the vertices of the input.\<close>

locale csr_edge_input =
  fixes n :: nat
    and fs :: "nat list"
    and ts :: "nat list"
    and key :: "edge \<Rightarrow> nat"
    and key_imp :: "nat array \<times> nat array \<Rightarrow> edge \<Rightarrow> nat Heap"
  assumes ts_length: "length ts = length fs"
    and fs_bound: "\<And>u. u \<in> set fs \<Longrightarrow> u < n"
    and ts_bound: "\<And>v. v \<in> set ts \<Longrightarrow> v < n"
    and key_endpoint: "key = e_src \<or> key = e_tgt"
    and key_imp: "key_imp = (\<lambda>_ e. return (key e))"
begin

lemma edge_bound: "e \<in> edges fs ts \<Longrightarrow> e_src e < n \<and> e_tgt e < n"
  unfolding edges_iff using fs_bound[OF nth_mem] ts_bound[OF nth_mem] ts_length by auto

lemma verts_bound: "verts fs ts \<subseteq> {..<n}"
  using edge_bound by (auto simp: dVs_def multigraph_spec.make_pair_def)

lemma key_bound: "e \<in> edges fs ts \<Longrightarrow> key e < n"
  using key_endpoint edge_bound[of e] by (elim disjE) simp_all

lemma key_vert:
  assumes "e \<in> edges fs ts"
  shows "key e \<in> verts fs ts"
proof -
  have "multigraph_spec.make_pair e_src e_tgt e \<in> multigraph_spec.make_pair e_src e_tgt ` edges fs ts"
    using assms by (rule imageI)
  hence "{e_src e, e_tgt e} \<subseteq> verts fs ts"
    by (auto simp: dVs_def multigraph_spec.make_pair_def)
  thus ?thesis
    using key_endpoint by auto
qed

lemma e_id_key_array: "key_array (length fs) e_id (edges fs ts)"
  by unfold_locales (auto simp: inj_on_def edges_iff mk_edge_def e_id_def)

lemma vert_key_array: "key_array n id (verts fs ts)"
  by unfold_locales (use verts_bound in auto)

sublocale inp: csr_buildup "edge_next fs ts" "edge_seq fs ts" "\<lambda>_. True" key n 0
  by (rule csr_buildup.intro[OF edge_iterator])
     (unfold_locales, auto simp: edges_def[symmetric] key_bound)

sublocale ci: imp_csr_buildup "edge_next fs ts" "edge_seq fs ts" "\<lambda>_. True" key n 0
    edge_has_next edge_cur edge_adv key_imp edge_val id "\<lambda>s si. si = s"
    "\<lambda>(Fa, Ta). Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts"
proof (unfold_locales, goal_cases)
  case (1 s si c)
  have "(edge_next fs ts s \<noteq> None) = (s < length fs)" by (simp add: edge_next_def mk_edge_def)
  with 1 show ?case by (cases c) (sep_auto simp: edge_has_next_def)
next
  case (2 s si e s' c) then show ?case
    using ts_length
    by (cases c) (sep_auto simp: edge_cur_def edge_next_def mk_edge_def split: if_splits)
next
  case (3 s si e s' c) then show ?case
    by (cases c) (sep_auto simp: edge_adv_def edge_next_def split: if_splits)
next
  case (4 e c) then show ?case
    by (sep_auto simp: key_imp)
next
  case (5 e c) then show ?case
    by (sep_auto simp: edge_val_def)
qed

lemma es_edges: "set inp.es = edges fs ts"
  by (simp add: inp.es_def edges_def)

lemma E_spec_distinct: "distinct inp.E_spec"
proof -
  have "distinct (concat (map inp.blk [0..<k])) \<and> set (concat (map inp.blk [0..<k])) \<subseteq> {e. key e < k}"
    for k
  proof (induction k)
    case 0 show ?case by simp
  next
    case (Suc k) then show ?case
      using edge_seq_distinct[of fs ts 0] by (fastforce simp: inp.blk_def inp.es_def)
  qed
  then show ?thesis by (simp add: inp.E_spec_def)
qed

lemma E_spec_edges: "set inp.E_spec = edges fs ts"
  using inp.key_es by (auto simp: inp.E_spec_def inp.blk_def es_edges[symmetric])

lemma E_spec_ids_distinct: "distinct (map e_id inp.E_spec)"
  using E_spec_distinct inj_on_subset[OF key_array.idx_inj[OF e_id_key_array]]
  by (simp add: distinct_map E_spec_edges)

lemma E_spec_ids: "e \<in> set inp.E_spec \<Longrightarrow> e_id e < length fs"
  using key_array.idx_bound[OF e_id_key_array] by (simp add: E_spec_edges)

lemma verts_eq: "verts fs ts = set fs \<union> set ts"
proof
  show "verts fs ts \<subseteq> set fs \<union> set ts"
    using ts_length
    by (auto simp: dVs_def multigraph_spec.make_pair_def edges_iff mk_edge_def e_src_def e_tgt_def)
next
  show "set fs \<union> set ts \<subseteq> verts fs ts"
  proof
    fix v
    assume "v \<in> set fs \<union> set ts"
    then obtain i where i: "i < length fs" "v = fs ! i \<or> v = ts ! i"
      using ts_length by (auto simp: in_set_conv_nth)
    have "mk_edge fs ts i \<in> edges fs ts"
      using i(1) by (auto simp: edges_iff)
    hence "(fs ! i, ts ! i) \<in> multigraph_spec.make_pair e_src e_tgt ` edges fs ts"
      by (rule rev_image_eqI) (simp add: multigraph_spec.make_pair_def)
    thus "v \<in> verts fs ts"
      using i(2) unfolding dVs_def by blast
  qed
qed

sublocale graph: csr_graph n "verts fs ts" inp.B_spec inp.E_spec
proof (unfold_locales, goal_cases)
  case 1 show ?case by (rule verts_bound)
next
  case 2 show ?case by (rule inp.length_B_spec)
next
  case (3 v) then show ?case by (simp add: inp.B_spec_nth inp.start_mono)
next
  case (4 v) then show ?case
    using inp.start_mono[of "Suc v" n] by (simp add: inp.B_spec_nth inp.start_n inp.length_E_spec)
next
  case 5 show ?case by (rule E_spec_distinct)
qed

text \<open>The block of a vertex holds exactly the edges whose key is that vertex.\<close>

lemma csr_abstract_key:
  assumes "v \<in> verts fs ts"
  shows "graph.csr_abstract c v = {e \<in> edges fs ts. key e = v}"
proof -
  have vn: "v < n" using assms verts_bound by auto
  have "graph.csr_abstract c v = set (map ((!) inp.E_spec) [inp.B_spec ! v..<inp.B_spec ! Suc v])"
    by (simp add: graph.csr_abstract_def graph.seg_def)
  also have "\<dots> = set (take (inp.B_spec ! Suc v - inp.B_spec ! v) (drop (inp.B_spec ! v) inp.E_spec))"
    using graph.B_bound[OF vn] by (simp add: map_nth_upt_take_drop)
  also have "\<dots> = set (inp.blk v)"
    using inp.csr_block[OF vn] by simp
  also have "\<dots> = {e \<in> edges fs ts. key e = v}"
    by (auto simp: inp.blk_def es_edges[symmetric])
  finally show ?thesis .
qed

lemma csr_build_rule:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts> ci.csr_build_imp (Fa, Ta) 0
   <\<lambda>(Ba, Ea). Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Ba \<mapsto>\<^sub>a inp.B_spec * Ea \<mapsto>\<^sub>a inp.E_spec>"
  using ci.csr_build_imp_rule[of "(Fa, Ta)" 0] by simp

end

text \<open>The two instances: grouped by the first endpoint, the code is @{const csr_build_edges},
      grouped by the second, @{const csr_build_edges_tgt}.\<close>

lemma edge_key_src: "edge_key = (\<lambda>_ e. return (e_src e))"
  by (simp add: fun_eq_iff edge_key_def)

lemma edge_key_tgt: "edge_key_tgt = (\<lambda>_ e. return (e_tgt e))"
  by (simp add: fun_eq_iff edge_key_tgt_def)

lemma csr_build_edges_src:
  "imp_csr_buildup_code.csr_build_imp n edge_has_next edge_cur edge_adv edge_key edge_val =
   csr_build_edges n"
  by (simp add: csr_build_edges_def)

lemma csr_build_edges_tgt:
  "imp_csr_buildup_code.csr_build_imp n edge_has_next edge_cur edge_adv edge_key_tgt edge_val =
   csr_build_edges_tgt n"
  by (simp add: csr_build_edges_tgt_def)

end
