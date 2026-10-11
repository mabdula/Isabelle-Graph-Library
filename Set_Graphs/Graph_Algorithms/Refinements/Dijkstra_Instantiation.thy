theory Dijkstra_Instantiation
  imports Dijkstra_Refinement Data_Structures.Indexed_Heap_Imperative
    "Directed_Set_Graphs.CSR_Graph"
begin

section \<open>An Instantiation of the Imperative Dijkstra\<close>

text \<open>The locale @{locale dijkstra_impl_refine} is instantiated with purely imperative data
      structures of fixed size, allocated once:

        \<^item> distances, parents and the seen set are arrays over the vertices \<open>{..<n}\<close>,
        \<^item> the weights are an array indexed by edge identifiers,
        \<^item> the queue is the indexed heap of @{theory Data_Structures.Indexed_Heap_Imperative},
        \<^item> the sources are an array traversed by a cursor held in a reference, and
        \<^item> the graph is in compressed sparse row (CSR) form, built by
          @{theory Directed_Set_Graphs.CSR_Buildup_Imperative} and given in
          @{theory Directed_Set_Graphs.CSR_Graph}: an array \<open>B\<close> of block starts, an
          array \<open>E\<close> of edges sorted by source, and a cursor array \<open>C\<close>, initially a copy of the start
          indices. Advancing the iterator of a vertex increments its cursor; resetting it copies the
          start index back.

      Edges are triples \<open>(u, v, i)\<close> of source, target and identifier; the identifier makes parallel
      edges distinct and indexes the weight array.\<close>


subsection \<open>Arrays as functions\<close>

text \<open>An array of size \<open>N\<close> represents a function on a key set @{term K}, whose keys are mapped
      injectively into \<open>{..<N}\<close> by @{term idx}; entries are read through @{term val}. The functional
      model is the function itself.\<close>

definition arr_lookup :: "('k \<Rightarrow> 'b) \<Rightarrow> 'k \<Rightarrow> 'b" where
  "arr_lookup f k = f k"

definition arr_upd :: "('k \<Rightarrow> 'b) \<Rightarrow> 'k \<Rightarrow> 'b \<Rightarrow> ('k \<Rightarrow> 'b)" where
  "arr_upd f k x = f(k := x)"

lemma arr_lookup_upd[simp]: "arr_lookup (arr_upd f k x) = (arr_lookup f)(k := x)"
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


subsection \<open>The seen set as a Boolean array\<close>

definition bset_invar :: "'k set \<Rightarrow> 'k set \<Rightarrow> bool" where
  "bset_invar K S \<longleftrightarrow> S \<subseteq> K"

definition "bset_empty_imp N = Array.new N False"
definition "bset_insert_imp ix k a = arr_upd_imp ix a k True"
definition "bset_delete_imp ix k a = arr_upd_imp ix a k False"
definition "bset_isin_imp ix a k = arr_lookup_imp ix a k"

locale bool_set = key_array N idx K "id :: bool \<Rightarrow> bool"
  for N :: nat and idx :: "'k \<Rightarrow> nat" and K :: "'k set"
begin

definition bset_assn :: "'k set \<Rightarrow> bool array \<Rightarrow> assn" where
  "bset_assn S a = arr_assn (\<lambda>k. k \<in> S) a"

lemma bset_empty_rule: "<emp> bset_empty_imp N <\<lambda>a. bset_assn {} a>"
  using arr_new_rule[of False] unfolding bset_empty_imp_def bset_assn_def by simp

lemma bset_insert_rule: "x \<in> K \<Longrightarrow> <bset_assn S a> bset_insert_imp idx x a <\<lambda>_. bset_assn (insert x S) a>"
proof -
  assume x: "x \<in> K"
  have e: "arr_upd (\<lambda>k. k \<in> S) x (id True) = (\<lambda>k. k \<in> insert x S)"
    by (auto simp: arr_upd_def fun_eq_iff)
  show ?thesis
    unfolding bset_insert_imp_def bset_assn_def
    using arr_upd_imp_rule[OF x, of "\<lambda>k. k \<in> S" a True] e by (simp only: id_apply)
qed

lemma bset_delete_rule: "x \<in> K \<Longrightarrow> <bset_assn S a> bset_delete_imp idx x a <\<lambda>_. bset_assn (S - {x}) a>"
proof -
  assume x: "x \<in> K"
  have e: "arr_upd (\<lambda>k. k \<in> S) x (id False) = (\<lambda>k. k \<in> S - {x})"
    by (auto simp: arr_upd_def fun_eq_iff)
  show ?thesis
    unfolding bset_delete_imp_def bset_assn_def
    using arr_upd_imp_rule[OF x, of "\<lambda>k. k \<in> S" a False] e by (simp only: id_apply)
qed

lemma bset_isin_rule: "x \<in> K \<Longrightarrow> <bset_assn S a> bset_isin_imp idx a x <\<lambda>r. bset_assn S a * \<up>(r = (x \<in> S))>"
  unfolding bset_isin_imp_def bset_assn_def
  by (sep_auto heap: arr_lookup_imp_rule simp: arr_lookup_def)

sublocale bset: fixed_univ_set_imp K "bset_invar K" id "{}" insert "\<lambda>x S. S - {x}" "\<lambda>S x. x \<in> S"
    bset_assn "bset_empty_imp N" "bset_insert_imp idx" "bset_delete_imp idx" "bset_isin_imp idx"
  by unfold_locales
     (auto simp: bset_invar_def bset_empty_rule bset_insert_rule bset_delete_rule bset_isin_rule)

end


subsection \<open>The sources as an array with a cursor\<close>

text \<open>The functional model of the iterator is the cursor position into the fixed list @{term S}
      of distinct sources.\<close>

definition ait_current_imp :: "'a::heap array \<times> nat ref \<Rightarrow> 'a Heap" where
  "ait_current_imp = (\<lambda>(Sa, r). do { j \<leftarrow> !r; Array.nth Sa j })"

definition ait_has_imp :: "'a::heap array \<times> nat ref \<Rightarrow> bool Heap" where
  "ait_has_imp = (\<lambda>(Sa, r). do { j \<leftarrow> !r; l \<leftarrow> Array.len Sa; return (j < l) })"

definition ait_move_imp :: "'a::heap array \<times> nat ref \<Rightarrow> unit Heap" where
  "ait_move_imp = (\<lambda>(Sa, r). do { j \<leftarrow> !r; r := Suc j })"

locale array_iterator =
  fixes S :: "'a::heap list"
  assumes S_distinct: "distinct S"
begin

definition "ait_invar j \<longleftrightarrow> j \<le> length S"
definition "ait_abstract (j::nat) = set S"
definition "ait_current j = S ! j"
definition "ait_has j \<longleftrightarrow> j < length S"
definition "ait_iterated j = set (take j S)"
definition "ait_remaining j = set (drop j S)"
definition "ait_move j = Suc j"

lemma ait_remaining_ne: "ait_remaining j \<noteq> {} \<longleftrightarrow> j < length S"
  by (simp add: ait_remaining_def not_le)

sublocale ait: iterable_set ait_invar ait_abstract ait_current ait_has ait_iterated ait_remaining
    ait_move
proof (unfold_locales, goal_cases)
  case (1 j) show ?case
    using S_distinct set_take_disj_set_drop_if_distinct[of S j j]
    by (simp add: ait_iterated_def ait_remaining_def)
next
  case (2 j) show ?case
    by (simp add: ait_iterated_def ait_remaining_def ait_abstract_def flip: set_append)
next
  case (3 j) show ?case unfolding ait_has_def ait_remaining_def by auto
next
  case (4 j)
  then have j: "j < length S" by (simp add: ait_remaining_ne)
  show ?case
    unfolding ait_current_def ait_remaining_def using j by (metis Cons_nth_drop_Suc list.set_intros(1))
next
  case (5 j) show ?case by (simp add: ait_abstract_def)
next
  case (6 j)
  then have j: "j < length S" by (simp add: ait_remaining_ne)
  have "drop j S = S ! j # drop (Suc j) S" using j by (simp add: Cons_nth_drop_Suc)
  moreover have "S ! j \<notin> set (drop (Suc j) S)"
    using distinct_drop[OF S_distinct, of j] by (simp add: Cons_nth_drop_Suc[OF j, symmetric])
  ultimately show ?case
    by (simp add: ait_remaining_def ait_move_def ait_current_def)
next
  case (7 j)
  then have j: "j < length S" by (simp add: ait_remaining_ne)
  show ?case by (simp add: ait_iterated_def ait_move_def ait_current_def take_Suc_conv_app_nth j)
next
  case (8 j) then show ?case by (simp add: ait_invar_def ait_move_def ait_remaining_ne)
qed

definition ait_assn :: "nat \<Rightarrow> 'a array \<times> nat ref \<Rightarrow> assn" where
  "ait_assn j = (\<lambda>(Sa, r). Sa \<mapsto>\<^sub>a S * r \<mapsto>\<^sub>r j)"

lemma ait_move_imp_rule: "<ait_assn j (Sa, r)> ait_move_imp (Sa, r) <\<lambda>_. ait_assn (Suc j) (Sa, r)>"
  unfolding ait_assn_def ait_move_imp_def by sep_auto

sublocale ait_imp: iterable_set_imp ait_invar ait_abstract ait_current ait_has ait_iterated
    ait_remaining ait_move ait_assn ait_current_imp ait_has_imp ait_move_imp
proof (unfold_locales, goal_cases)
  case (1 j Si) then show ?case
    by (cases Si) (sep_auto simp: ait_assn_def ait_current_imp_def ait_current_def ait_remaining_ne)
next
  case (2 j Si) then show ?case
    by (cases Si) (sep_auto simp: ait_assn_def ait_has_imp_def ait_has_def)
next
  case (3 j Si) then show ?case
    by (cases Si) (simp add: ait_move_imp_rule ait_move_def)
qed

end


section \<open>The Code\<close>

text \<open>The global interpretation of the refined Dijkstra. The locale @{locale dijkstra_impl_spec}
      only fixes operations and has no assumptions. The CSR buildup for the input iterator is
      interpreted in @{theory Directed_Set_Graphs.CSR_Graph}.\<close>

global_interpretation dijkstra_code: dijkstra_impl_spec unreached "bset_isin_imp id" "\<lambda>Al. Al" early_stop
    "\<lambda>e. return (e_tgt e)" "arr_lookup_imp e_id" "arr_upd_imp id" "arr_lookup_imp id"
    "arr_upd_imp id" "bset_insert_imp id" "bset_isin_imp id"
    ait_current_imp ait_has_imp ait_move_imp
    csr_current_imp csr_has_imp csr_move_imp csr_reset_imp
    heap_extract_min_key_imp heap_decrease_key_imp heap_insert_imp
    "arr_lookup_imp id" "\<lambda>e. return (e_src e)"
  for unreached :: "'n::{linordered_ab_group_add, heap}" and early_stop :: bool
  defines dijkstra_relax_code = dijkstra_code.relax_edge_imp
    and dijkstra_source_code = dijkstra_code.insert_source_imp
    and dijkstra_target_test_code = dijkstra_code.target_test_imp
    and dijkstra_loop_code = dijkstra_code.dijkstra_loop_imp
    and dijkstra_imp_code = dijkstra_code.dijkstra_imp
    and dijkstra_path_rev_code = dijkstra_code.path_rev_imp
    and dijkstra_path_code = dijkstra_code.path_imp
  done

text \<open>The final program takes the arrays \<open>Fa\<close>, \<open>Ta\<close> of first and second endpoints, the weight
      array \<open>Wa\<close>, the source array \<open>Sa\<close>, the Boolean target array \<open>Tg\<close> and the edge test \<open>Al\<close>,
      builds the CSR representation, allocates and initialises all other data structures and runs
      the refined Dijkstra. It returns the final state and the target found.\<close>

definition dijkstra_csr_run where
  "dijkstra_csr_run n unreached early_stop Fa Ta Wa Sa Tg Al = do {
     (Ba, Ea) \<leftarrow> csr_build_edges n (Fa, Ta) 0;
     Ca \<leftarrow> csr_cursor_init n Ba;
     Da \<leftarrow> Array.new n unreached;
     Pa \<leftarrow> Array.new n None;
     Se \<leftarrow> bset_empty_imp n;
     Hq \<leftarrow> heap_empty_imp n 0;
     r \<leftarrow> ref 0;
     let si = \<lparr>dimp_dist = Da, dimp_seen = Se, dimp_parent = Pa, dimp_heap = Hq,
               dimp_graph = (Ba, Ea, Ca), dimp_srcs = (Sa, r), dimp_weight = Wa, dimp_target = Tg,
               dimp_allowed = Al\<rparr>;
     t \<leftarrow> dijkstra_imp_code unreached early_stop si;
     return (si, t) }"

text \<open>On the full graph, every edge is allowed. The program with the edge test that always
      succeeds is specialised by code equations: the test and its branch disappear from the
      relaxation, and the loop and the relaxation no longer read the test from the state.\<close>

definition all_edges_imp :: "nat \<Rightarrow> nat \<Rightarrow> edge \<Rightarrow> 'n \<Rightarrow> bool Heap" where
  "all_edges_imp u v e we = return True"

definition "dijkstra_csr_run_all n unreached early_stop Fa Ta Wa Sa Tg =
  dijkstra_csr_run n unreached early_stop Fa Ta Wa Sa Tg all_edges_imp"

definition "dijkstra_relax_all unreached s =
  dijkstra_relax_code unreached (s\<lparr>dimp_allowed := all_edges_imp\<rparr>)"

definition "dijkstra_loop_all unreached early_stop s =
  dijkstra_loop_code unreached early_stop (s\<lparr>dimp_allowed := all_edges_imp\<rparr>)"

lemma dimp_allowed_upd[simp]:
  "dijkstra_source_code (s\<lparr>dimp_allowed := Al\<rparr>) = dijkstra_source_code s"
  "dijkstra_target_test_code early_stop (s\<lparr>dimp_allowed := Al\<rparr>) = dijkstra_target_test_code early_stop s"
  by (simp_all add: fun_eq_iff dijkstra_code.insert_source_imp_def dijkstra_code.target_test_imp_def)

context notes all_edges_imp_def[simp] if_weak_cong[cong del] if_cong[cong]
  option.case_cong_weak[cong del] option.case_cong[cong]
begin
lemmas dijkstra_relax_all_code[code] =
  dijkstra_code.relax_edge_imp_def[of _ "s\<lparr>dimp_allowed := all_edges_imp\<rparr>" for s,
    folded dijkstra_relax_all_def, simplified]

lemmas dijkstra_loop_all_code[code] =
  dijkstra_code.dijkstra_loop_imp.simps[of _ _ "s\<lparr>dimp_allowed := all_edges_imp\<rparr>" for s,
    folded dijkstra_loop_all_def dijkstra_relax_all_def, simplified]
end


lemma dijkstra_csr_run_all_code[code]:
  "dijkstra_csr_run_all n unreached early_stop Fa Ta Wa Sa Tg = do {
     (Ba, Ea) \<leftarrow> csr_build_edges n (Fa, Ta) 0;
     Ca \<leftarrow> csr_cursor_init n Ba;
     Da \<leftarrow> Array.new n unreached;
     Pa \<leftarrow> Array.new n None;
     Se \<leftarrow> bset_empty_imp n;
     Hq \<leftarrow> heap_empty_imp n 0;
     r \<leftarrow> ref 0;
     let si = \<lparr>dimp_dist = Da, dimp_seen = Se, dimp_parent = Pa, dimp_heap = Hq,
               dimp_graph = (Ba, Ea, Ca), dimp_srcs = (Sa, r), dimp_weight = Wa, dimp_target = Tg,
               dimp_allowed = all_edges_imp\<rparr>;
     t \<leftarrow> dijkstra_loop_all unreached early_stop si None;
     return (si, t) }"
  unfolding dijkstra_csr_run_all_def dijkstra_csr_run_def dijkstra_loop_all_def
    dijkstra_code.dijkstra_imp_def Let_def
  by simp


section \<open>Correctness of the Code\<close>

subsection \<open>The data structures of the instance\<close>

text \<open>The proof locale fixes only functional values: the number \<open>n\<close> of vertices, the endpoint
      lists @{term fs} and @{term ts}, the weights @{term ws}, the distinct sources @{term sl}, and
      the embedding @{term h} of the weight type into the reals with its unreached marker.\<close>

locale dijkstra_csr = dist_embedding h unreached
  for h :: "'n::{linordered_ab_group_add, heap} \<Rightarrow> real" and unreached :: 'n +
  fixes n :: nat
    and fs :: "nat list"
    and ts :: "nat list"
    and ws :: "'n list"
    and sl :: "nat list"
  assumes fs_ne: "fs \<noteq> []"
    and ts_length: "length ts = length fs"
    and ws_length: "length ws = length fs"
    and fs_bound: "\<And>u. u \<in> set fs \<Longrightarrow> u < n"
    and ts_bound: "\<And>v. v \<in> set ts \<Longrightarrow> v < n"
    and ws_nonneg: "\<And>x. x \<in> set ws \<Longrightarrow> 0 \<le> x"
    and sl_distinct: "distinct sl"
    and sl_verts: "set sl \<subseteq> verts fs ts"
begin

definition wt :: "edge \<Rightarrow> real" where
  "wt e = h (ws ! e_id e)"

lemma edge_bound: "e \<in> edges fs ts \<Longrightarrow> e_src e < n \<and> e_tgt e < n"
  unfolding edges_iff using fs_bound[OF nth_mem] ts_bound[OF nth_mem] ts_length by auto

lemma verts_bound: "verts fs ts \<subseteq> {..<n}"
  using edge_bound by (auto simp: dVs_def multigraph_spec.make_pair_def)

text \<open>The multigraph of the input, which gives the notions of reachability and of shortest paths.\<close>

sublocale mg: multigraph e_src e_tgt "\<lambda>u v. (u, v, 0)" "edges fs ts"
  by unfold_locales (auto simp: e_src_def e_tgt_def edges_def edge_seq_def fs_ne)

sublocale inp: csr_buildup "edge_next fs ts" "edge_seq fs ts" "\<lambda>_. True" e_src n 0
  by (rule csr_buildup.intro[OF edge_iterator]) (unfold_locales, auto simp: edges_def[symmetric] edge_bound)

sublocale ci: imp_csr_buildup "edge_next fs ts" "edge_seq fs ts" "\<lambda>_. True" e_src n 0
    edge_has_next edge_cur edge_adv edge_key edge_val id "\<lambda>s si. si = s"
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
    by (sep_auto simp: edge_key_def)
next
  case (5 e c) then show ?case
    by (sep_auto simp: edge_val_def)
qed

lemma es_edges: "set inp.es = edges fs ts"
  by (simp add: inp.es_def edges_def)

lemma E_spec_distinct: "distinct inp.E_spec"
proof -
  have "distinct (concat (map inp.blk [0..<k])) \<and> set (concat (map inp.blk [0..<k])) \<subseteq> {e. e_src e < k}"
    for k
  proof (induction k)
    case 0 show ?case by simp
  next
    case (Suc k) then show ?case
      using edge_seq_distinct[of fs ts 0] by (fastforce simp: inp.blk_def inp.es_def)
  qed
  then show ?thesis by (simp add: inp.E_spec_def)
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

sublocale dist: key_array n id "verts fs ts" h
  by unfold_locales (use verts_bound in auto)

sublocale par: key_array n id "verts fs ts" "id :: edge option \<Rightarrow> edge option"
  by unfold_locales (use verts_bound in auto)

sublocale wgt: key_array "length fs" e_id "edges fs ts" h
  by unfold_locales (auto simp: inj_on_def edges_iff mk_edge_def e_id_def)

sublocale seen: bool_set n id "verts fs ts"
  by unfold_locales (use verts_bound in auto)

sublocale src: array_iterator sl
  by unfold_locales (rule sl_distinct)

sublocale hp: indexed_heap_imp n "verts fs ts" h 0
  by unfold_locales (simp_all add: verts_bound)

lemma csr_abstract_delta:
  assumes "v \<in> verts fs ts"
  shows "graph.csr_abstract c v = multigraph_spec.delta_plus (edges fs ts) e_src v"
proof -
  have vn: "v < n" using assms verts_bound by auto
  have "graph.csr_abstract c v = set (map ((!) inp.E_spec) [inp.B_spec ! v..<inp.B_spec ! Suc v])"
    by (simp add: graph.csr_abstract_def graph.seg_def)
  also have "\<dots> = set (take (inp.B_spec ! Suc v - inp.B_spec ! v) (drop (inp.B_spec ! v) inp.E_spec))"
    using graph.B_bound[OF vn] by (simp add: map_nth_upt_take_drop)
  also have "\<dots> = set (inp.blk v)"
    using inp.csr_block[OF vn] by simp
  also have "\<dots> = multigraph_spec.delta_plus (edges fs ts) e_src v"
    by (auto simp: inp.blk_def es_edges[symmetric] multigraph_spec.delta_plus_def)
  finally show ?thesis .
qed

lemma csr_build_edges_rule:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts> csr_build_edges n (Fa, Ta) 0
   <\<lambda>(Ba, Ea). Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Ba \<mapsto>\<^sub>a inp.B_spec * Ea \<mapsto>\<^sub>a inp.E_spec>"
  using ci.csr_build_imp_rule[of "(Fa, Ta)" 0] by (simp add: csr_build_edges_def)

end


subsection \<open>The instance of the refined Dijkstra\<close>

text \<open>Besides the target predicate, the instance fixes the edge predicate @{term allowed} and the
      heap representation @{term allowed_assn} of its imperative test. As in the refinement, the
      test @{term Al} is assumed to decide @{term allowed} on an edge given by its tail, head and
      weight, with its representation as a frame. The representation is determined by the
      caller.\<close>

locale dijkstra_csr_inst = dijkstra_csr +
  fixes target :: "nat \<Rightarrow> bool"
    and early_stop :: bool
    and allowed :: "nat \<Rightarrow> nat \<Rightarrow> edge \<Rightarrow> real \<Rightarrow> bool"
    and allowed_assn
  assumes allowed_imp_rule:
    "\<lbrakk>e \<in> edges fs ts; u = e_src e; v = e_tgt e; h we = wt e\<rbrakk> \<Longrightarrow>
     <allowed_assn Al> Al u v e we <\<lambda>b. allowed_assn Al * \<up>(b = allowed u v e (wt e))>"
begin

sublocale dij: dijkstra_impl_refine where
      fst = e_src and \<E> = "edges fs ts" and snd = e_tgt and create_edge = "\<lambda>u v. (u, v, 0)"
  and out_invar = graph.csr_invar and out_abstract = graph.csr_abstract
  and out_current = graph.csr_current and out_has = graph.csr_has
  and out_iterated = graph.csr_iterated and out_remaining = graph.csr_remaining
  and out_move = graph.csr_move and out_reset = graph.csr_reset
  and dist_invar = "\<lambda>_. True" and dist_upd = arr_upd and dist_lookup = arr_lookup
  and parent_invar = "\<lambda>_. True" and parent_upd = arr_upd and parent_lookup = arr_lookup
  and seen_invar = "bset_invar (verts fs ts)" and seen_abstract = id and seen_empty = "{}"
  and seen_insert = insert and seen_delete = "\<lambda>x S. S - {x}" and seen_isin = "\<lambda>S x. x \<in> S"
  and src_invar = src.ait_invar and src_abstract = src.ait_abstract
  and src_current = src.ait_current and src_has = src.ait_has
  and src_iterated = src.ait_iterated and src_remaining = src.ait_remaining
  and src_move = src.ait_move
  and queue_empty = heap_empty and queue_extract_min = heap_extract_min
  and queue_decrease_key = heap_decrease_key and queue_insert = heap_insert
  and queue_invar = "heap_invar (verts fs ts)" and queue_abstract = heap_abstract
  and og = "\<lambda>v. inp.B_spec ! v" and srcs = 0 and w = wt
  and target = target and allowed = allowed and early_stop = early_stop
  and dist_init = "\<lambda>_. -1" and parent_init = "\<lambda>_. None"
  and h = h and unreached = unreached
  and out_assn = graph.csr_assn and out_current_imp = csr_current_imp
  and out_has_imp = csr_has_imp and out_move_imp = csr_move_imp
  and out_reset_imp = csr_reset_imp
  and dist_assn = dist.arr_assn and dist_upd_imp = "arr_upd_imp id"
  and dist_lookup_imp = "arr_lookup_imp id"
  and parent_assn = par.arr_assn and parent_upd_imp = "arr_upd_imp id"
  and parent_lookup_imp = "arr_lookup_imp id"
  and weight_invar = "\<lambda>_. True" and weight_upd = arr_upd and weight_lookup = arr_lookup
  and weight_assn = wgt.arr_assn and weight_upd_imp = "arr_upd_imp e_id"
  and weight_lookup_imp = "arr_lookup_imp e_id"
  and seen_assn = seen.bset_assn and seen_empty_imp = "bset_empty_imp n"
  and seen_insert_imp = "bset_insert_imp id" and seen_delete_imp = "bset_delete_imp id"
  and seen_isin_imp = "bset_isin_imp id"
  and src_assn = src.ait_assn and src_current_imp = ait_current_imp
  and src_has_imp = ait_has_imp and src_move_imp = ait_move_imp
  and queue_assn = hp.heap_assn and queue_empty_imp = "heap_empty_imp n 0"
  and queue_extract_min_imp = heap_extract_min_key_imp
  and queue_decrease_key_imp = heap_decrease_key_imp
  and queue_insert_imp = heap_insert_imp
  and snd_imp = "\<lambda>e. return (e_tgt e)" and fst_imp = "\<lambda>e. return (e_src e)" and W = wt
  and target_imp = "bset_isin_imp id" and target_assn = "seen.bset_assn (Collect target)"
  and allowed_imp = "\<lambda>Al. Al" and allowed_assn = allowed_assn
  and queue_clear_imp = heap_clear_imp
  and queue_key_of_imp = heap_key_of_imp
proof (intro_locales, goal_cases)
  case 1 show ?case
  proof (unfold_locales, goal_cases)
    case 1
    have oi: "outgoing_edge_iterator (edges fs ts) e_tgt e_src graph.csr_invar graph.csr_abstract
        graph.csr_current graph.csr_has graph.csr_iterated graph.csr_remaining graph.csr_move
        graph.csr_reset"
      unfolding outgoing_edge_iterator_def by (rule graph.csr.indexed_iterable_set_axioms)
    show ?case
      unfolding outgoing_edge_iterator.out_graph_inv_def[OF oi]
      using graph.B_mono graph.K_less csr_abstract_delta by (auto simp: graph.csr_invar_def)
  next
    case 2 show ?case by (simp add: src.ait_invar_def)
  next
    case 3 show ?case using sl_verts by (simp add: src.ait_abstract_def)
  next
    case (4 e)
    then have "e_id e < length ws" using ws_length by (auto simp: edges_iff)
    then show ?case using ws_nonneg nth_mem by (auto simp: wt_def)
  next
    case (9 v) show ?case by (simp add: graph.csr_iterated_def graph.seg_def)
  qed (simp_all add: arr_lookup_def src.ait_remaining_def src.ait_abstract_def)
next
  case 2 show ?case
    by unfold_locales
       (simp_all add: arr_lookup_def allowed_imp_rule,
       (sep_auto heap: seen.bset_isin_rule)+)
qed

text \<open>The code part of this interpretation is the instance of @{locale dijkstra_impl_spec} that is
      globally interpreted, so the correctness of the refined algorithm holds for the global code.\<close>

theorem dijkstra_imp_code_correct:
  "<dij.state_assn (dij.initial_state :: (nat, _, _, _, _, _, _) dij_state) si>
     dijkstra_imp_code unreached early_stop si
   <\<lambda>r. dij.state_assn dij.dijkstra_compute si * \<up>(r = dij_target dij.dijkstra_compute)>"
  unfolding dijkstra_imp_code_def by (rule dij.dijkstra_imp_correct)

lemma dijkstra_imp_init:
  "<dist.arr_assn (\<lambda>_. -1) Da * seen.bset_assn {} Se * par.arr_assn (\<lambda>_. None) Pa *
    hp.heap_assn heap_empty Hq * graph.csr_assn ((!) inp.B_spec) (Ba, Ea, Ca) *
    Sa \<mapsto>\<^sub>a sl * r \<mapsto>\<^sub>r 0 * Wa \<mapsto>\<^sub>a ws * seen.bset_assn (Collect target) Tg * allowed_assn Al>
   dijkstra_imp_code unreached early_stop
     \<lparr>dimp_dist = Da, dimp_seen = Se, dimp_parent = Pa, dimp_heap = Hq,
      dimp_graph = (Ba, Ea, Ca), dimp_srcs = (Sa, r), dimp_weight = Wa, dimp_target = Tg,
      dimp_allowed = Al\<rparr>
   <\<lambda>t. dij.state_assn dij.dijkstra_compute
          \<lparr>dimp_dist = Da, dimp_seen = Se, dimp_parent = Pa, dimp_heap = Hq,
           dimp_graph = (Ba, Ea, Ca), dimp_srcs = (Sa, r), dimp_weight = Wa, dimp_target = Tg,
           dimp_allowed = Al\<rparr> *
        \<up>(t = dij_target dij.dijkstra_compute)>"
  (is "<?P> dijkstra_imp_code unreached early_stop ?si <?Q>")
proof (rule ht_cons_pre[OF _ dijkstra_imp_code_correct[of ?si]])
  show "?P \<Longrightarrow>\<^sub>A dij.state_assn dij.initial_state ?si"
    unfolding dij.state_assn_def dij.initial_state_def src.ait_assn_def wgt.arr_assn_def
    by (sep_auto simp: ws_length wt_def)
qed

text \<open>The target array is the target predicate tabulated over the vertex bound.\<close>

lemma target_array_assn:
  "Tg \<mapsto>\<^sub>a map target [0..<n] \<Longrightarrow>\<^sub>A seen.bset_assn (Collect target) Tg"
  unfolding seen.bset_assn_def seen.arr_assn_def using verts_bound by sep_auto

text \<open>The whole program computes @{const dij.dijkstra_compute}: the state returned refines it.\<close>

theorem dijkstra_csr_run_compute:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * Sa \<mapsto>\<^sub>a sl * Tg \<mapsto>\<^sub>a map target [0..<n] * allowed_assn Al>
     dijkstra_csr_run n unreached early_stop Fa Ta Wa Sa Tg Al
   <\<lambda>(si, t). dij.state_assn dij.dijkstra_compute si * \<up>(t = dij_target dij.dijkstra_compute)>"
  unfolding dijkstra_csr_run_def
  by (rule ht_cons_pre[OF ent_star_mono[OF ent_star_mono[OF ent_refl target_array_assn] ent_refl]])
    (sep_auto heap: csr_build_edges_rule graph.csr_cursor_init_rule dist.arr_new_rule
      par.arr_new_rule seen.bset_empty_rule hp.heap_empty_imp_rule dijkstra_imp_init)

text \<open>Without early stopping, every reached vertex is settled at the end.\<close>

lemma dijkstra_compute_reached_seen:
  assumes "\<not> early_stop" "arr_lookup (dij_dist dij.dijkstra_compute) v \<noteq> -1"
  shows "v \<in> dij_seen dij.dijkstra_compute"
  using dij.dijkstra_compute_reached_seen[OF dij.target_none_compute[OF assms(1)] assms(2)] by simp

text \<open>A distance list is correct if it marks exactly the vertices reachable from a source in the
      subgraph @{term dij.Ea} of allowed edges and holds their shortest-path distances.\<close>

definition shortest_dists where
  "shortest_dists dl \<longleftrightarrow> (\<forall>v \<in> verts fs ts.
     (dl ! v \<noteq> unreached \<longleftrightarrow> (\<exists>s \<in> set sl. dij.ag.reachable s v)) \<and>
     (dl ! v \<noteq> unreached \<longrightarrow> ereal (h (dl ! v)) = dij.ag.distance_set wt (set sl) v))"

text \<open>Without early stopping, the distance array of the final state holds the shortest
      distances.\<close>

lemma dist_assn_shortest:
  assumes "\<not> early_stop"
  shows "dist.arr_assn (dij_dist dij.dijkstra_compute) Da \<Longrightarrow>\<^sub>A
         (\<exists>\<^sub>Adl. Da \<mapsto>\<^sub>a dl * \<up>(length dl = n \<and> shortest_dists dl))"
proof -
  have compl: "arr_lookup (dij_dist dij.dijkstra_compute) v \<noteq> -1 \<longleftrightarrow> (\<exists>s \<in> set sl. dij.ag.reachable s v)"
    for v using dij.dijkstra_compute_complete[OF assms] by (simp add: src.ait_abstract_def)
  have opt: "arr_lookup (dij_dist dij.dijkstra_compute) v \<noteq> -1 \<Longrightarrow>
      ereal (arr_lookup (dij_dist dij.dijkstra_compute) v) = dij.ag.distance_set wt (set sl) v" for v
    using dij.dijkstra_compute_optimal dijkstra_compute_reached_seen[OF assms]
    by (simp add: src.ait_abstract_def)
  have P: "shortest_dists dl"
    if A: "\<forall>v \<in> verts fs ts. h (dl ! v) = arr_lookup (dij_dist dij.dijkstra_compute) v" for dl
    unfolding shortest_dists_def
  proof
    fix v assume v: "v \<in> verts fs ts"
    have e: "h (dl ! v) = arr_lookup (dij_dist dij.dijkstra_compute) v" using A v by blast
    have u: "dl ! v \<noteq> unreached \<longleftrightarrow> arr_lookup (dij_dist dij.dijkstra_compute) v \<noteq> -1"
      using e h_eq_neg1 by metis
    show "(dl ! v \<noteq> unreached \<longleftrightarrow> (\<exists>s \<in> set sl. dij.ag.reachable s v)) \<and>
          (dl ! v \<noteq> unreached \<longrightarrow> ereal (h (dl ! v)) = dij.ag.distance_set wt (set sl) v)"
      using u e compl opt by simp
  qed
  have P': "length dl = n \<and> shortest_dists dl"
    if a: "length dl = n \<and> (\<forall>k \<in> verts fs ts. h (dl ! id k) = dij_dist dij.dijkstra_compute k)" for dl
  proof -
    have "\<forall>v \<in> verts fs ts. h (dl ! v) = arr_lookup (dij_dist dij.dijkstra_compute) v"
      using a unfolding arr_lookup_def id_apply by blast
    then show ?thesis using a P by blast
  qed
  have mono: "(A \<Longrightarrow> B) \<Longrightarrow> X * \<up>A \<Longrightarrow>\<^sub>A X * \<up>B" for X A B
    by (cases A) simp_all
  show ?thesis
    unfolding dist.arr_assn_def
    by (rule ent_ex_preI, rule ent_ex_postI, rule mono, rule P')
qed

text \<open>The final correctness theorem for the distances: without early stopping, the program
      computes the shortest distances from the sources in the subgraph @{term dij.Ea}
      of allowed edges.\<close>

theorem dijkstra_csr_run_correct:
  assumes "\<not> early_stop"
  shows "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * Sa \<mapsto>\<^sub>a sl * Tg \<mapsto>\<^sub>a map target [0..<n] * allowed_assn Al>
           dijkstra_csr_run n unreached early_stop Fa Ta Wa Sa Tg Al
         <\<lambda>(si, t). \<exists>\<^sub>Adl. dimp_dist si \<mapsto>\<^sub>a dl * \<up>(length dl = n \<and> shortest_dists dl)>"
proof (rule ht_cons[OF ent_refl _ dijkstra_csr_run_compute], goal_cases)
  case (1 x)
  obtain si t where x: "x = (si, t)" by (cases x)
  have drop: "A * B * C * D * E * F * G * H * I * \<up>c \<Longrightarrow>\<^sub>A A * true" for A B C D E F G H I :: assn and c
    by sep_auto
  show ?case unfolding x prod.case dij.state_assn_def
    by (rule ent_trans[OF drop ent_star_mono[OF dist_assn_shortest[OF assms] ent_refl]])
qed

subsection \<open>Path reconstruction\<close>

text \<open>A path is a shortest path to \<open>v\<close> if it is a simple path from a source to \<open>v\<close> in the subgraph
      @{term dij.Ea} and its weight is the distance of \<open>v\<close> from the sources. It is then a shortest
      path between its source and \<open>v\<close>.\<close>

definition shortest_path :: "edge list \<Rightarrow> nat \<Rightarrow> bool" where
  "shortest_path p v \<longleftrightarrow> (\<exists>s \<in> set sl. dij.ag.path_bet p s v) \<and> distinct p \<and>
     ereal (mg.weight wt p) = dij.ag.distance_set wt (set sl) v"

lemma shortest_path_pairwise:
  "shortest_path p v \<Longrightarrow> \<exists>s \<in> set sl. dij.ag.path_bet p s v \<and> ereal (mg.weight wt p) = dij.ag.distance wt s v"
  unfolding shortest_path_def using dij.ag_distance_set_path_shortest by blast

lemma card_verts: "card (verts fs ts) \<le> n"
  using card_mono[OF finite_lessThan verts_bound] by simp

text \<open>The path reconstruction of the global code, @{const dijkstra_path_code}, on a state refining
      the final state of the functional Dijkstra: given an array of at least \<open>n\<close> cells, it writes
      the path to \<open>v\<close> reversed into the first \<open>k\<close> cells and returns \<open>k\<close>. If \<open>v\<close> is reachable from a
      source, this is a shortest path.\<close>

theorem dijkstra_path_code_correct:
  assumes "\<not> early_stop" "v \<in> verts fs ts" "n \<le> length r"
  shows "<dij.state_assn dij.dijkstra_compute si * Ra \<mapsto>\<^sub>a r>
           dijkstra_path_code si Ra v
         <\<lambda>k. dij.state_assn dij.dijkstra_compute si * (\<exists>\<^sub>Ap. Ra \<mapsto>\<^sub>a p * \<up>(length p = length r \<and>
            k \<le> n \<and> ((\<exists>s \<in> set sl. dij.ag.reachable s v) \<longrightarrow> shortest_path (rev (take k p)) v)))>"
proof -
  have c: "card (verts fs ts) \<le> length r" using card_verts assms(3) by linarith
  have imp: "length p = length r \<and> k \<le> n \<and>
      ((\<exists>s \<in> set sl. dij.ag.reachable s v) \<longrightarrow> shortest_path (rev (take k p)) v)"
    if a: "length p = length r \<and> k = length (dij.reconstruct_path dij.dijkstra_compute v) \<and>
      rev (take k p) = dij.reconstruct_path dij.dijkstra_compute v \<and>
      (arr_lookup (dij_dist dij.dijkstra_compute) v \<noteq> -1 \<longrightarrow>
        (\<exists>s \<in> src.ait_abstract 0. dij.ag.path_bet (rev (take k p)) s v \<and>
           mg.weight wt (rev (take k p)) = arr_lookup (dij_dist dij.dijkstra_compute) v))" for p k
  proof -
    have "k \<le> n" using a dij.reconstruct_path_compute_length[of v] card_verts by linarith
    moreover have "shortest_path (rev (take k p)) v" if re: "\<exists>s \<in> set sl. dij.ag.reachable s v"
    proof -
      have "v \<in> dij_seen dij.dijkstra_compute"
        using dijkstra_compute_reached_seen[OF assms(1)] dij.dijkstra_compute_complete[OF assms(1)] re
        by (simp add: src.ait_abstract_def)
      then show ?thesis
        using a dij.reconstruct_path_shortest[of v] unfolding shortest_path_def
        by (auto simp: src.ait_abstract_def simp del: distinct_rev)
    qed
    ultimately show ?thesis using a by blast
  qed
  have g: "(\<And>p. A p \<Longrightarrow> B p) \<Longrightarrow>
           X * (\<exists>\<^sub>Ap. Ra \<mapsto>\<^sub>a p * \<up>(A p)) \<Longrightarrow>\<^sub>A X * (\<exists>\<^sub>Ap. Ra \<mapsto>\<^sub>a p * \<up>(B p)) * true"
    for X and A B :: "edge list \<Rightarrow> bool"
    by sep_auto
  show ?thesis
    unfolding dijkstra_path_code_def
    by (rule ht_cons[OF ent_refl _ dij.path_imp_correct[OF assms(2) c]], rule g, erule imp)
qed

subsection \<open>The parent array\<close>

text \<open>A parent list is tight if the parent edge of every vertex \<open>v\<close> is an allowed edge into
      \<open>v\<close>, leaving a vertex reachable from a source, and the shortest distance of \<open>v\<close> is that
      of the vertex plus the weight of the edge.\<close>

definition tight_parent_array :: "edge option list \<Rightarrow> bool" where
  "tight_parent_array pl \<longleftrightarrow> (\<forall>v \<in> verts fs ts. \<forall>e. pl ! v = Some e \<longrightarrow>
     e \<in> dij.Ea \<and> e_tgt e = v \<and> (\<exists>s \<in> set sl. dij.ag.reachable s (e_src e)) \<and>
     dij.ag.distance_set wt (set sl) v = dij.ag.distance_set wt (set sl) (e_src e) + ereal (wt e))"

lemma parent_assn_tight:
  assumes "\<not> early_stop"
  shows "par.arr_assn (dij_parent dij.dijkstra_compute) Pa \<Longrightarrow>\<^sub>A
         (\<exists>\<^sub>Apl. Pa \<mapsto>\<^sub>a pl * \<up>(length pl = n \<and> tight_parent_array pl))"
proof -
  have P: "length pl = n \<and> tight_parent_array pl"
    if a: "length pl = n \<and> (\<forall>k \<in> verts fs ts. id (pl ! id k) = dij_parent dij.dijkstra_compute k)"
    for pl
    using a dij.dijkstra_compute_tight_parents[OF assms]
    unfolding tight_parent_array_def dij.tight_parents_def
    by (auto simp: arr_lookup_def src.ait_abstract_def)
  have mono: "(A \<Longrightarrow> B) \<Longrightarrow> X * \<up>A \<Longrightarrow>\<^sub>A X * \<up>B" for X A B
    by (cases A) simp_all
  show ?thesis
    unfolding par.arr_assn_def
    by (rule ent_ex_preI, rule ent_ex_postI, rule mono, rule P)
qed

text \<open>Without early stopping, the parent array of the final state is tight.\<close>

theorem dijkstra_csr_run_parents:
  assumes "\<not> early_stop"
  shows "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * Sa \<mapsto>\<^sub>a sl * Tg \<mapsto>\<^sub>a map target [0..<n] * allowed_assn Al>
           dijkstra_csr_run n unreached early_stop Fa Ta Wa Sa Tg Al
         <\<lambda>(si, t). \<exists>\<^sub>Apl. dimp_parent si \<mapsto>\<^sub>a pl * \<up>(length pl = n \<and> tight_parent_array pl)>"
proof (rule ht_cons[OF ent_refl _ dijkstra_csr_run_compute], goal_cases)
  case (1 x)
  obtain si t where x: "x = (si, t)" by (cases x)
  have drop: "A * B * C * D * E * F * G * H * I * \<up>c \<Longrightarrow>\<^sub>A C * true" for A B C D E F G H I :: assn and c
    by sep_auto
  show ?case unfolding x prod.case dij.state_assn_def
    by (rule ent_trans[OF drop ent_star_mono[OF parent_assn_tight[OF assms] ent_refl]])
qed

subsection \<open>Early stopping\<close>

text \<open>With early stopping, a target returned is a vertex reachable from a source, and no target is
      closer to the sources. If none is returned, no target is reachable from a source.\<close>

theorem dijkstra_csr_run_target:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * Sa \<mapsto>\<^sub>a sl * Tg \<mapsto>\<^sub>a map target [0..<n] * allowed_assn Al>
     dijkstra_csr_run n unreached early_stop Fa Ta Wa Sa Tg Al
   <\<lambda>(si, t). dij.state_assn dij.dijkstra_compute si * \<up>(t = dij_target dij.dijkstra_compute \<and>
      (\<forall>u. t = Some u \<longrightarrow> target u \<and> u \<in> verts fs ts \<and> (\<exists>s \<in> set sl. dij.ag.reachable s u) \<and>
         (\<forall>x. target x \<longrightarrow> dij.ag.distance_set wt (set sl) u \<le> dij.ag.distance_set wt (set sl) x)) \<and>
      (t = None \<longrightarrow> early_stop \<longrightarrow> (\<forall>v. target v \<longrightarrow> \<not> (\<exists>s \<in> set sl. dij.ag.reachable s v))))>"
proof (rule ht_cons[OF ent_refl _ dijkstra_csr_run_compute], goal_cases)
  case (1 x)
  obtain si t where x: "x = (si, t)" by (cases x)
  have tg: "target u \<and> u \<in> verts fs ts \<and> (\<exists>s \<in> set sl. dij.ag.reachable s u) \<and>
      (\<forall>x. target x \<longrightarrow> dij.ag.distance_set wt (set sl) u \<le> dij.ag.distance_set wt (set sl) x)"
    if "dij_target dij.dijkstra_compute = Some u" for u
  proof -
    have a: "target u" "u \<in> verts fs ts"
        "ereal (arr_lookup (dij_dist dij.dijkstra_compute) u) = dij.ag.distance_set wt (set sl) u"
        "\<forall>x. target x \<longrightarrow> dij.ag.distance_set wt (set sl) u \<le> dij.ag.distance_set wt (set sl) x"
      using dij.dijkstra_compute_target[OF that] by (auto simp: src.ait_abstract_def)
    have "dij.ag.distance_set wt (set sl) u \<noteq> \<infinity>" by (simp flip: a(3))
    then show ?thesis using a dij.ag_distance_set_infty_iff by blast
  qed
  have nt: "early_stop \<Longrightarrow> dij_target dij.dijkstra_compute = None \<Longrightarrow> target v \<Longrightarrow>
      \<not> (\<exists>s \<in> set sl. dij.ag.reachable s v)" for v
    using dij.dijkstra_compute_no_target by (auto simp: src.ait_abstract_def)
  have g: "P T \<Longrightarrow> X * \<up>(t = T) \<Longrightarrow>\<^sub>A X * \<up>(t = T \<and> P t) * true"
    for X and t T :: "nat option" and P
    by sep_auto
  show ?case unfolding x prod.case
    by (rule g) (use tg nt in blast)
qed

text \<open>For the target returned, the path reconstruction gives a shortest path from a source, and no
      simple path from a source to any target is shorter.\<close>

theorem dijkstra_path_code_target:
  assumes "dij_target dij.dijkstra_compute = Some u" "n \<le> length r"
  shows "<dij.state_assn dij.dijkstra_compute si * Ra \<mapsto>\<^sub>a r>
           dijkstra_path_code si Ra u
         <\<lambda>k. dij.state_assn dij.dijkstra_compute si * (\<exists>\<^sub>Ap. Ra \<mapsto>\<^sub>a p * \<up>(length p = length r \<and>
            k \<le> n \<and> target u \<and> shortest_path (rev (take k p)) u \<and>
            (\<forall>s \<in> set sl. \<forall>x q. target x \<longrightarrow> dij.ag.path_bet q s x \<longrightarrow> distinct q \<longrightarrow>
               mg.weight wt (rev (take k p)) \<le> mg.weight wt q)))>"
proof -
  have c: "card (verts fs ts) \<le> length r" using card_verts assms(2) by linarith
  have imp: "length p = length r \<and> k \<le> n \<and> target u \<and> shortest_path (rev (take k p)) u \<and>
      (\<forall>s \<in> set sl. \<forall>x q. target x \<longrightarrow> dij.ag.path_bet q s x \<longrightarrow> distinct q \<longrightarrow>
         mg.weight wt (rev (take k p)) \<le> mg.weight wt q)"
    if a: "length p = length r \<and> k = length (dij.reconstruct_path dij.dijkstra_compute u) \<and>
      target u \<and> (\<exists>s \<in> src.ait_abstract 0. dij.ag.path_bet (rev (take k p)) s u \<and>
        distinct (rev (take k p)) \<and>
        ereal (mg.weight wt (rev (take k p))) = dij.ag.distance_set wt (src.ait_abstract 0) u \<and>
        ereal (mg.weight wt (rev (take k p))) = dij.ag.distance wt s u) \<and>
      (\<forall>s \<in> src.ait_abstract 0. \<forall>x q. target x \<longrightarrow> dij.ag.path_bet q s x \<longrightarrow> distinct q \<longrightarrow>
         mg.weight wt (rev (take k p)) \<le> mg.weight wt q)"
    for p k
  proof -
    have "k \<le> n" using a dij.reconstruct_path_compute_length[of u] card_verts by linarith
    then show ?thesis using a unfolding shortest_path_def by (auto simp: src.ait_abstract_def)
  qed
  have g: "(\<And>p. A p \<Longrightarrow> B p) \<Longrightarrow>
           X * (\<exists>\<^sub>Ap. Ra \<mapsto>\<^sub>a p * \<up>(A p)) \<Longrightarrow>\<^sub>A X * (\<exists>\<^sub>Ap. Ra \<mapsto>\<^sub>a p * \<up>(B p)) * true"
    for X and A B :: "edge list \<Rightarrow> bool"
    by sep_auto
  show ?thesis
    unfolding dijkstra_path_code_def
    by (rule ht_cons[OF ent_refl _ dij.path_imp_target[OF assms(1) c]], rule g, erule imp)
qed

end

subsection \<open>The full graph\<close>

text \<open>With the edge test that always succeeds and the empty frame, every edge is allowed. The
      correctness theorems then hold for the input multigraph @{text mg} and the specialised
      program @{const dijkstra_csr_run_all}.\<close>

locale dijkstra_csr_all = dijkstra_csr +
  fixes target :: "nat \<Rightarrow> bool"
    and early_stop :: bool
begin

sublocale all: dijkstra_csr_inst where target = target and early_stop = early_stop
  and allowed = "\<lambda>_ _ _ _. True" and allowed_assn = "\<lambda>Al. \<up>(Al = all_edges_imp)"
  by unfold_locales (sep_auto simp: all_edges_imp_def)

lemma all_Ea: "all.dij.Ea = edges fs ts"
  by (simp add: all.dij.allowed_edge_def)

lemmas dijkstra_csr_run_all_correct =
    all.dijkstra_csr_run_correct[where Al = all_edges_imp, folded dijkstra_csr_run_all_def,
      unfolded all.shortest_dists_def all_Ea simp_thms(6) pure_true mult_1_right]
  and dijkstra_csr_run_all_parents =
    all.dijkstra_csr_run_parents[where Al = all_edges_imp, folded dijkstra_csr_run_all_def,
      unfolded all.tight_parent_array_def all_Ea simp_thms(6) pure_true mult_1_right]
  and dijkstra_csr_run_all_target =
    all.dijkstra_csr_run_target[where Al = all_edges_imp, folded dijkstra_csr_run_all_def,
      unfolded all_Ea simp_thms(6) pure_true mult_1_right]

end

section \<open>Running the Code\<close>

text \<open>The heap @{command partial_function}s do not register their equations for code generation.\<close>

declare dijkstra_code.dijkstra_loop_imp.simps[code]
  dijkstra_code.path_rev_imp.simps[code] sift_up_imp.simps[code] sift_down_imp.simps[code]

text \<open>A test harness. \<open>dijkstra_prepare\<close> copies the input lists into arrays, among them the target
      list \<open>tgs\<close> tabulating the target predicate, and runs the search on the full graph once.
      \<open>dijkstra_query\<close> asks the final state for the distance of a vertex and writes its path,
      reversed, into the array \<open>Ra\<close> the caller provides; it returns the distance and the path
      length. The \<open>code\<close> antiquotation compiles both into the running ML session; applying a
      @{typ "'a Heap"} computation to \<open>()\<close> runs it.\<close>

definition dijkstra_prepare where
  "dijkstra_prepare n fs ts (ws :: int list) sl early_stop tgs = do {
     Fa \<leftarrow> Array.of_list fs; Ta \<leftarrow> Array.of_list ts;
     Wa \<leftarrow> Array.of_list ws; Sa \<leftarrow> Array.of_list sl; Tg \<leftarrow> Array.of_list tgs;
     dijkstra_csr_run_all n (-1) early_stop Fa Ta Wa Sa Tg }"

definition dijkstra_query where
  "dijkstra_query si Ra v = do {
     d \<leftarrow> Array.nth (dimp_dist si) v;
     k \<leftarrow> dijkstra_path_code si Ra v;
     return (d :: int, k) }"

text \<open>Both runs below use the same graph, with the sources 0 and 5. A path is read from the first
      \<open>k\<close> entries of the path array and reversed, so it is printed from its source to the target,
      as triples (source, target, edge index). The path array is allocated once and reused for
      every query. Each \<open>ML_val\<close> block compiles its own copy of the code, so each one is
      self-contained.\<close>

text \<open>The run on the full graph. Without early stopping, the search runs once. Vertex 6 is
      unreachable: its distance is \<open>-1\<close> and its path is empty. With early stopping, the search for
      the targets 2 and 4 stops at the nearer target 4; the search for the unreachable target 6
      finds none.\<close>

ML_val \<open>
  let
    val nat = @{code nat_of_integer}
    val int = @{code int_of_integer}
    val i = @{code integer_of_nat}
    val n = 7
    (* the edges (source, target, weight); the edge index is the list position *)
    val es = [(0, 1, 1), (0, 2, 4), (1, 2, 1), (2, 3, 2), (1, 3, 5),
              (5, 4, 1), (4, 3, 1), (3, 4, 3), (6, 0, 1)]
    fun run early tgts =
      @{code dijkstra_prepare} (nat n)
        (map (fn (u, _, _) => nat u) es) (map (fn (_, v, _) => nat v) es)
        (map (fn (_, _, w) => int w) es) (map nat [0, 5]) early
        (List.tabulate (n, fn v => List.exists (fn x => x = v) tgts)) ()
    val ra = Array.array (n, (nat 0, (nat 0, nat 0)))
    fun query si v =
      let
        val (d, k) = @{code dijkstra_query} si ra (nat v) ()
        val path = rev (List.tabulate (i k, fn j => Array.sub (ra, j)))
      in
        (v, @{code integer_of_int} d, map (fn (u, (w, e)) => (i u, i w, i e)) path)
      end
    val (si, _) = run false []
    fun early tgts =
      (case run true tgts of (_, NONE) => NONE | (si, SOME u) => SOME (query si (i u)))
  in
    (map (query si) [2, 3, 4, 5, 6], early [2, 4], early [6])
  end
\<close>

text \<open>A run on a subgraph. The edge test allows exactly the edges with an even index; it is passed
      to the general program @{const dijkstra_csr_run}.\<close>

definition even_edges_imp :: "nat \<Rightarrow> nat \<Rightarrow> edge \<Rightarrow> 'n \<Rightarrow> bool Heap" where
  "even_edges_imp u v e we = return (even (e_id e))"

definition dijkstra_prepare_even where
  "dijkstra_prepare_even n fs ts (ws :: int list) sl early_stop tgs = do {
     Fa \<leftarrow> Array.of_list fs; Ta \<leftarrow> Array.of_list ts;
     Wa \<leftarrow> Array.of_list ws; Sa \<leftarrow> Array.of_list sl; Tg \<leftarrow> Array.of_list tgs;
     dijkstra_csr_run n (-1) early_stop Fa Ta Wa Sa Tg even_edges_imp }"

text \<open>On the even edges alone, vertex 3 is reached only by the edge 4 and vertex 4 not at all,
      since the edge 5 leaving the source 5 is odd.\<close>

ML_val \<open>
  let
    val nat = @{code nat_of_integer}
    val int = @{code int_of_integer}
    val i = @{code integer_of_nat}
    val n = 7
    (* the edges (source, target, weight); the edge index is the list position *)
    val es = [(0, 1, 1), (0, 2, 4), (1, 2, 1), (2, 3, 2), (1, 3, 5),
              (5, 4, 1), (4, 3, 1), (3, 4, 3), (6, 0, 1)]
    val (si, _) =
      @{code dijkstra_prepare_even} (nat n)
        (map (fn (u, _, _) => nat u) es) (map (fn (_, v, _) => nat v) es)
        (map (fn (_, _, w) => int w) es) (map nat [0, 5]) false
        (List.tabulate (n, fn _ => false)) ()
    val ra = Array.array (n, (nat 0, (nat 0, nat 0)))
    fun query v =
      let
        val (d, k) = @{code dijkstra_query} si ra (nat v) ()
        val path = rev (List.tabulate (i k, fn j => Array.sub (ra, j)))
      in
        (v, @{code integer_of_int} d, map (fn (u, (w, e)) => (i u, i w, i e)) path)
      end
  in
    map query [2, 3, 4, 5, 6]
  end
\<close>


section \<open>Top-Level Programs\<close>

text \<open>Two programs on the full graph, given by the arrays \<open>Fa\<close>, \<open>Ta\<close> of first and second endpoints
      and the weight array \<open>Wa\<close>, with the sources in the array \<open>Sa\<close>. A path is returned as a fresh
      array of edge indices, i.e.\ of positions in the input arrays, from its source to its end.

        \<^item> @{term dijkstra_shortest_path} is also given the targets in an array \<open>Tv\<close>. It searches
          with early stopping and returns a shortest path from a source to a nearest target, if any
          target is reachable.
        \<^item> @{term dijkstra_sp_compute} runs the search without early stopping and returns its final
          state together with an array for the path reconstruction. On this state,
          @{term dijkstra_sp_query} returns a shortest path from a source to a given vertex, if it
          is reachable. The state is not changed by a query, so it answers any number of them.

      All arrays except the returned paths are allocated before the search starts.\<close>

subsection \<open>The programs\<close>

text \<open>The target predicate tabulated over the vertex bound: the entries of the targets are set in
      an array of \<open>False\<close>.\<close>

partial_function (heap) dijkstra_mark_targets :: "nat array \<Rightarrow> bool array \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "dijkstra_mark_targets Tv Tg i = do {
     l \<leftarrow> Array.len Tv;
     if i < l then do {
       v \<leftarrow> Array.nth Tv i;
       _ \<leftarrow> Array.upd v True Tg;
       dijkstra_mark_targets Tv Tg (Suc i) }
     else return () }"

text \<open>The path reconstruction writes the edges of the path reversed into the first \<open>k\<close> cells of
      \<open>Ra\<close>. Their indices are copied into a fresh array of length \<open>k\<close>, in the order of the path.\<close>

partial_function (heap) dijkstra_edge_ids :: "edge array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "dijkstra_edge_ids Ra Pa k i =
     (if i < k then do {
        e \<leftarrow> Array.nth Ra (k - Suc i);
        _ \<leftarrow> Array.upd i (e_id e) Pa;
        dijkstra_edge_ids Ra Pa k (Suc i) }
      else return ())"

definition dijkstra_path_ids where
  "dijkstra_path_ids si Ra v = do {
     k \<leftarrow> dijkstra_path_code si Ra v;
     Pa \<leftarrow> Array.new k 0;
     dijkstra_edge_ids Ra Pa k 0;
     return Pa }"

definition dijkstra_shortest_path where
  "dijkstra_shortest_path n unreached Fa Ta Wa Sa Tv = do {
     Tg \<leftarrow> Array.new n False;
     Ra \<leftarrow> Array.new n (0, 0, 0);
     dijkstra_mark_targets Tv Tg 0;
     (si, t) \<leftarrow> dijkstra_csr_run_all n unreached True Fa Ta Wa Sa Tg;
     (case t of
        None \<Rightarrow> return None
      | Some u \<Rightarrow> do { Pa \<leftarrow> dijkstra_path_ids si Ra u; return (Some Pa) }) }"

definition dijkstra_sp_compute where
  "dijkstra_sp_compute n unreached Fa Ta Wa Sa = do {
     Tg \<leftarrow> Array.new n False;
     Ra \<leftarrow> Array.new n (0, 0, 0);
     (si, _) \<leftarrow> dijkstra_csr_run_all n unreached False Fa Ta Wa Sa Tg;
     return (si, Ra) }"

definition dijkstra_sp_query where
  "dijkstra_sp_query unreached th v = (case th of (si, Ra) \<Rightarrow> do {
     d \<leftarrow> Array.nth (dimp_dist si) v;
     if d = unreached then return None
     else do { Pa \<leftarrow> dijkstra_path_ids si Ra v; return (Some Pa) } })"

declare dijkstra_mark_targets.simps[code] dijkstra_edge_ids.simps[code]

subsection \<open>The loops\<close>

lemma dijkstra_mark_targets_rule:
  assumes "set gs \<subseteq> {..<length bs}" "i \<le> length gs"
  shows "<Tv \<mapsto>\<^sub>a gs * Tg \<mapsto>\<^sub>a bs> dijkstra_mark_targets Tv Tg i
         <\<lambda>_. Tv \<mapsto>\<^sub>a gs * Tg \<mapsto>\<^sub>a map (\<lambda>v. bs ! v \<or> v \<in> set (drop i gs)) [0..<length bs]>"
  using assms
proof (induction "length gs - i" arbitrary: i bs)
  case 0
  then show ?case by (subst dijkstra_mark_targets.simps) (sep_auto simp: map_nth)
next
  case (Suc k)
  have i: "i < length gs" using Suc.hyps(2) by simp
  have v: "gs ! i < length bs" using i Suc.prems(1) nth_mem by blast
  have e: "map (\<lambda>x. bs[gs ! i := True] ! x \<or> x \<in> set (drop (Suc i) gs)) [0..<length bs] =
           map (\<lambda>x. bs ! x \<or> x \<in> set (drop i gs)) [0..<length bs]"
    using i v by (auto simp: nth_list_update Cons_nth_drop_Suc[symmetric])
  have IH: "<Tv \<mapsto>\<^sub>a gs * Tg \<mapsto>\<^sub>a bs[gs ! i := True]> dijkstra_mark_targets Tv Tg (Suc i)
            <\<lambda>_. Tv \<mapsto>\<^sub>a gs * Tg \<mapsto>\<^sub>a map (\<lambda>x. bs ! x \<or> x \<in> set (drop i gs)) [0..<length bs]>"
    using Suc.hyps(1)[of "Suc i" "bs[gs ! i := True]"] Suc.hyps(2) Suc.prems(1) i e by simp
  show ?case using i v by (subst dijkstra_mark_targets.simps) (sep_auto heap: IH)
qed

lemma dijkstra_edge_ids_rule:
  assumes "k \<le> length r" "i \<le> k" "length xs = k"
  shows "<Ra \<mapsto>\<^sub>a r * Pa \<mapsto>\<^sub>a xs> dijkstra_edge_ids Ra Pa k i
         <\<lambda>_. Ra \<mapsto>\<^sub>a r * Pa \<mapsto>\<^sub>a (take i xs @ map (\<lambda>j. e_id (r ! (k - Suc j))) [i..<k])>"
  using assms(2,3)
proof (induction "k - i" arbitrary: i xs)
  case 0
  then have "i = k" by simp
  with 0 show ?case by (subst dijkstra_edge_ids.simps) sep_auto
next
  case (Suc d)
  have i: "i < k" using Suc.hyps(2) by simp
  have e: "take (Suc i) (xs[i := e_id (r ! (k - Suc i))]) @ map (\<lambda>j. e_id (r ! (k - Suc j))) [Suc i..<k] =
           take i xs @ map (\<lambda>j. e_id (r ! (k - Suc j))) [i..<k]"
    using i Suc.prems(2) by (simp add: take_Suc_conv_app_nth upt_conv_Cons list_update_append)
  have IH: "<Ra \<mapsto>\<^sub>a r * Pa \<mapsto>\<^sub>a xs[i := e_id (r ! (k - Suc i))]> dijkstra_edge_ids Ra Pa k (Suc i)
            <\<lambda>_. Ra \<mapsto>\<^sub>a r * Pa \<mapsto>\<^sub>a (take i xs @ map (\<lambda>j. e_id (r ! (k - Suc j))) [i..<k])>"
    using Suc.hyps(1)[of "Suc i" "xs[i := e_id (r ! (k - Suc i))]"] Suc.hyps(2) Suc.prems(2) i e
    by simp
  show ?case using i assms(1) Suc.prems(2) by (subst dijkstra_edge_ids.simps) (sep_auto heap: IH)
qed

text \<open>The indices of a path written by @{const dijkstra_path_code}, for any property @{term A}
      of the path length and the path array that the path reconstruction guarantees.\<close>

lemma dijkstra_path_ids_rule:
  assumes "<X * Ra \<mapsto>\<^sub>a r> dijkstra_path_code si Ra v <\<lambda>k. X * (\<exists>\<^sub>Ap. Ra \<mapsto>\<^sub>a p * \<up>(A k p))>"
    and "\<And>k p. A k p \<Longrightarrow> k \<le> length p"
  shows "<X * Ra \<mapsto>\<^sub>a r> dijkstra_path_ids si Ra v
         <\<lambda>Pa. X * (\<exists>\<^sub>Ap k. Ra \<mapsto>\<^sub>a p * Pa \<mapsto>\<^sub>a map e_id (rev (take k p)) * \<up>(A k p))>"
proof -
  have m: "map (\<lambda>j. e_id (p ! (k - Suc j))) [0..<k] = map e_id (rev (take k p))"
    if "A k p" for k p
    using assms(2)[OF that] by (intro nth_equalityI) (simp_all add: rev_nth)
  show ?thesis unfolding dijkstra_path_ids_def
    by (sep_auto heap: assms(1) dijkstra_edge_ids_rule dest: assms(2) simp: m)
qed

text \<open>An edge of the input is given by its index.\<close>

lemma map_mk_edge_e_id: "set p \<subseteq> edges fs ts \<Longrightarrow> map (mk_edge fs ts) (map e_id p) = p"
  by (induction p) (auto simp: edges_iff)

subsection \<open>Paths as edge indices\<close>

context dijkstra_csr_all
begin

lemma shortest_path_ids:
  assumes "all.shortest_path p v"
  shows "map (mk_edge fs ts) (map e_id p) = p" "\<exists>s \<in> set sl. mg.is_shortest_path wt p s v"
proof -
  obtain s where s: "s \<in> set sl" "mg.path_bet p s v" "ereal (mg.weight wt p) = mg.distance wt s v"
    using all.shortest_path_pairwise[OF assms] unfolding all_Ea by blast
  show "map (mk_edge fs ts) (map e_id p) = p"
    using s(2) map_mk_edge_e_id unfolding mg.path_bet_def by blast
  show "\<exists>s \<in> set sl. mg.is_shortest_path wt p s v"
    using s assms unfolding mg.is_shortest_path_def all.shortest_path_def by auto
qed

text \<open>The indices of the path to the target found.\<close>

lemma dijkstra_path_ids_target:
  assumes "dij_target all.dij.dijkstra_compute = Some u" "n \<le> length r"
  shows "<all.dij.state_assn all.dij.dijkstra_compute si * Ra \<mapsto>\<^sub>a r> dijkstra_path_ids si Ra u
         <\<lambda>Pa. all.dij.state_assn all.dij.dijkstra_compute si * (\<exists>\<^sub>Ar'. Ra \<mapsto>\<^sub>a r' * \<up>(length r' = length r)) *
            (\<exists>\<^sub>Aids. Pa \<mapsto>\<^sub>a ids * \<up>(target u \<and>
               (\<exists>s \<in> set sl. mg.is_shortest_path wt (map (mk_edge fs ts) ids) s u) \<and>
               (\<forall>s \<in> set sl. \<forall>x q. target x \<longrightarrow> mg.path_bet q s x \<longrightarrow> distinct q \<longrightarrow>
                  mg.weight wt (map (mk_edge fs ts) ids) \<le> mg.weight wt q)))>"
proof (rule ht_cons[OF ent_refl _ dijkstra_path_ids_rule[OF all.dijkstra_path_code_target[OF assms]]],
    goal_cases)
  case (1 Pa)
  show ?case using shortest_path_ids by (sep_auto simp: all_Ea)
next
  case (2 k p) then show ?case using assms(2) by simp
qed

text \<open>Without early stopping, the indices of a path to a reachable vertex.\<close>

lemma dijkstra_path_ids_reached:
  assumes "\<not> early_stop" "v \<in> verts fs ts" "n \<le> length r" "\<exists>s \<in> set sl. mg.reachable s v"
  shows "<all.dij.state_assn all.dij.dijkstra_compute si * Ra \<mapsto>\<^sub>a r> dijkstra_path_ids si Ra v
         <\<lambda>Pa. all.dij.state_assn all.dij.dijkstra_compute si * (\<exists>\<^sub>Ar'. Ra \<mapsto>\<^sub>a r' * \<up>(length r' = length r)) *
            (\<exists>\<^sub>Aids. Pa \<mapsto>\<^sub>a ids * \<up>(\<exists>s \<in> set sl. mg.is_shortest_path wt (map (mk_edge fs ts) ids) s v))>"
proof (rule ht_cons[OF ent_refl _ dijkstra_path_ids_rule[OF all.dijkstra_path_code_correct[OF assms(1-3)]]],
    goal_cases)
  case (1 Pa)
  show ?case using shortest_path_ids assms(4) by (sep_auto simp: all_Ea)
next
  case (2 k p) then show ?case using assms(3) by simp
qed

subsection \<open>Correctness of the top-level programs\<close>

text \<open>Weakening the pure parts of postconditions.\<close>

lemma pure_post_weaken:
  "(\<And>a b. P a b \<Longrightarrow> P' a b) \<Longrightarrow>
   (case x of (a, b) \<Rightarrow> Q a * \<up>(P a b)) \<Longrightarrow>\<^sub>A (case x of (a, b) \<Rightarrow> Q a * \<up>(P' a b)) * true"
  by (cases x) sep_auto

lemma ex_pure_post_weaken:
  "(\<And>y. P y \<Longrightarrow> P' y) \<Longrightarrow>
   X * Y * (\<exists>\<^sub>Ay. R y * \<up>(P y)) \<Longrightarrow>\<^sub>A X * (\<exists>\<^sub>Ay. R y * \<up>(P' y)) * true"
  by sep_auto

text \<open>With early stopping and the targets given by an array, @{const dijkstra_shortest_path}
      returns a shortest path from a source to a target, of weight at most that of any simple
      path from a source to a target, if any target is reachable.\<close>

theorem dijkstra_shortest_path_rule:
  assumes "early_stop" "set gs \<subseteq> {..<n}" "\<And>v. target v \<longleftrightarrow> v \<in> set gs"
  shows "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * Sa \<mapsto>\<^sub>a sl * Tv \<mapsto>\<^sub>a gs>
           dijkstra_shortest_path n unreached Fa Ta Wa Sa Tv
         <\<lambda>r. case r of
             None \<Rightarrow> \<up>(\<forall>s \<in> set sl. \<forall>t \<in> set gs. \<not> mg.reachable s t)
           | Some Pa \<Rightarrow> \<exists>\<^sub>Aids. Pa \<mapsto>\<^sub>a ids * \<up>(\<exists>t \<in> set gs.
               (\<exists>s \<in> set sl. mg.is_shortest_path wt (map (mk_edge fs ts) ids) s t) \<and>
               (\<forall>s \<in> set sl. \<forall>t' \<in> set gs. \<forall>q. mg.path_bet q s t' \<longrightarrow> distinct q \<longrightarrow>
                  mg.weight wt (map (mk_edge fs ts) ids) \<le> mg.weight wt q))>"
proof -
  have m: "map (\<lambda>v. replicate n False ! v \<or> v \<in> set (drop 0 gs)) [0..<length (replicate n False)] =
           map target [0..<n]"
    by (rule nth_equalityI) (simp_all add: assms(3))
  have mark: "<Tv \<mapsto>\<^sub>a gs * Tg \<mapsto>\<^sub>a replicate n False> dijkstra_mark_targets Tv Tg 0
              <\<lambda>_. Tv \<mapsto>\<^sub>a gs * Tg \<mapsto>\<^sub>a map target [0..<n]>" for Tg
    using dijkstra_mark_targets_rule[of gs "replicate n False" 0 Tv Tg, unfolded m] assms(2) by simp
  have es: "dijkstra_csr_run_all n unreached True = dijkstra_csr_run_all n unreached early_stop"
    using assms(1) by simp
  have run: "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * Sa \<mapsto>\<^sub>a sl * Tg \<mapsto>\<^sub>a map target [0..<n]>
               dijkstra_csr_run_all n unreached early_stop Fa Ta Wa Sa Tg
             <\<lambda>(si, t). all.dij.state_assn all.dij.dijkstra_compute si *
                \<up>(dij_target all.dij.dijkstra_compute = t \<and>
                  (t = None \<longrightarrow> (\<forall>s \<in> set sl. \<forall>x \<in> set gs. \<not> mg.reachable s x)))>" for Tg
    by (rule ht_cons[OF ent_refl pure_post_weaken dijkstra_csr_run_all_target])
      (use assms(1,3) in auto)
  have path: "<all.dij.state_assn all.dij.dijkstra_compute si * Ra \<mapsto>\<^sub>a r> dijkstra_path_ids si Ra u
              <\<lambda>Pa. all.dij.state_assn all.dij.dijkstra_compute si * (\<exists>\<^sub>Aids. Pa \<mapsto>\<^sub>a ids * \<up>(\<exists>t \<in> set gs.
                 (\<exists>s \<in> set sl. mg.is_shortest_path wt (map (mk_edge fs ts) ids) s t) \<and>
                 (\<forall>s \<in> set sl. \<forall>t' \<in> set gs. \<forall>q. mg.path_bet q s t' \<longrightarrow> distinct q \<longrightarrow>
                    mg.weight wt (map (mk_edge fs ts) ids) \<le> mg.weight wt q)))>"
    if "dij_target all.dij.dijkstra_compute = Some u" "n \<le> length r" for si Ra r u
    by (rule ht_cons[OF ent_refl ex_pure_post_weaken dijkstra_path_ids_target[OF that]])
      (use assms(3) in blast)
  show ?thesis unfolding dijkstra_shortest_path_def es
    by (sep_auto heap: mark run path)
qed

text \<open>The result of @{const dijkstra_sp_compute}: the final state of the search without early
      stopping and the array for the path reconstruction.\<close>

definition sp_assn where
  "sp_assn th = (case th of (si, Ra) \<Rightarrow>
     all.dij.state_assn all.dij.dijkstra_compute si * (\<exists>\<^sub>Ar. Ra \<mapsto>\<^sub>a r * \<up>(length r = n)))"

theorem dijkstra_sp_compute_rule:
  assumes "\<not> early_stop" "\<And>v. \<not> target v"
  shows "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * Sa \<mapsto>\<^sub>a sl>
           dijkstra_sp_compute n unreached Fa Ta Wa Sa <sp_assn>"
proof -
  have es: "dijkstra_csr_run_all n unreached False = dijkstra_csr_run_all n unreached early_stop"
    using assms(1) by simp
  have tg: "replicate n False = map target [0..<n]"
    by (rule nth_equalityI) (simp_all add: assms(2))
  have run: "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * Sa \<mapsto>\<^sub>a sl * Tg \<mapsto>\<^sub>a replicate n False>
               dijkstra_csr_run_all n unreached early_stop Fa Ta Wa Sa Tg
             <\<lambda>(si, t). all.dij.state_assn all.dij.dijkstra_compute si * \<up>True>" for Tg
    by (rule ht_cons[OF _ pure_post_weaken dijkstra_csr_run_all_target]) (simp_all add: tg)
  show ?thesis unfolding dijkstra_sp_compute_def sp_assn_def es
    by (sep_auto heap: run)
qed

text \<open>A query for a vertex of the graph returns a shortest path from a source to it if it is
      reachable, and nothing otherwise. The state is preserved.\<close>

theorem dijkstra_sp_query_rule:
  assumes "\<not> early_stop" "v \<in> verts fs ts"
  shows "<sp_assn th> dijkstra_sp_query unreached th v
         <\<lambda>r. sp_assn th * (case r of
             None \<Rightarrow> \<up>(\<forall>s \<in> set sl. \<not> mg.reachable s v)
           | Some Pa \<Rightarrow> \<exists>\<^sub>Aids. Pa \<mapsto>\<^sub>a ids *
               \<up>(\<exists>s \<in> set sl. mg.is_shortest_path wt (map (mk_edge fs ts) ids) s v))>"
proof -
  obtain si Ra where th: "th = (si, Ra)" by (cases th)
  have r: "arr_lookup (dij_dist all.dij.dijkstra_compute) v \<noteq> -1 \<longleftrightarrow> (\<exists>s \<in> set sl. mg.reachable s v)"
    using all.dij.dijkstra_compute_complete[OF assms(1), of v]
    by (simp add: src.ait_abstract_def all_Ea)
  have nth: "arr_lookup_imp id (dimp_dist si) v = Array.nth (dimp_dist si) v"
    by (simp add: arr_lookup_imp_def)
  note l = all.dij.dist_lookup_state[where u = v and si = si, OF TrueI assms(2), unfolded nth]
  have d: "<all.dij.state_assn all.dij.dijkstra_compute si> Array.nth (dimp_dist si) v
           <\<lambda>d. all.dij.state_assn all.dij.dijkstra_compute si *
              \<up>(d \<noteq> unreached \<longleftrightarrow> (\<exists>s \<in> set sl. mg.reachable s v))>"
    by (rule ht_cons[OF ent_refl _ l])
      (sep_auto simp: r[symmetric])
  show ?thesis unfolding th dijkstra_sp_query_def sp_assn_def prod.case
    using assms by (sep_auto heap: d dijkstra_path_ids_reached)
qed

end

subsection \<open>The programs on integers\<close>

text \<open>The programs with integer weights, whose correctness is stated without locales. The input
      is a nonempty graph with endpoints below \<open>n\<close> and nonnegative weights, with distinct
      sources among its vertices.\<close>

definition dijkstra_int_input :: "nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> int list \<Rightarrow> nat list \<Rightarrow> bool" where
  "dijkstra_int_input n fs ts ws sl \<longleftrightarrow> fs \<noteq> [] \<and> length ts = length fs \<and> length ws = length fs \<and>
     set fs \<subseteq> {..<n} \<and> set ts \<subseteq> {..<n} \<and> (\<forall>x \<in> set ws. 0 \<le> x) \<and>
     distinct sl \<and> set sl \<subseteq> verts fs ts"

text \<open>The executable instance: integers, embedded by @{const of_int}, with \<open>-1\<close> as the marker.\<close>

global_interpretation int_dist_embedding: dist_embedding "of_int :: int \<Rightarrow> real" "-1"
  by unfold_locales simp_all

lemma dijkstra_int_input_csr:
  "dijkstra_int_input n fs ts ws sl \<Longrightarrow> dijkstra_csr of_int (-1) n fs ts ws sl"
  unfolding dijkstra_int_input_def
  by (intro dijkstra_csr.intro int_dist_embedding.dist_embedding_axioms dijkstra_csr_axioms.intro) auto

text \<open>The weight function on the edges.\<close>

definition int_weight :: "int list \<Rightarrow> edge \<Rightarrow> real" where
  "int_weight ws e = of_int (ws ! e_id e)"

type_synonym dijkstra_sp_state =
  "(int array, bool array, edge option array, int heap_imp, nat array \<times> edge array \<times> nat array,
    nat array \<times> nat ref, int array, bool array, nat \<Rightarrow> nat \<Rightarrow> edge \<Rightarrow> int \<Rightarrow> bool Heap) dij_impl_state \<times>
   edge array"

definition dijkstra_shortest_path_int ::
  "nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> int array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat array option Heap" where
  "dijkstra_shortest_path_int n = dijkstra_shortest_path n (-1)"

definition dijkstra_sp_compute_int ::
  "nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> int array \<Rightarrow> nat array \<Rightarrow> dijkstra_sp_state Heap" where
  "dijkstra_sp_compute_int n = dijkstra_sp_compute n (-1)"

definition dijkstra_sp_query_int :: "dijkstra_sp_state \<Rightarrow> nat \<Rightarrow> nat array option Heap" where
  "dijkstra_sp_query_int = dijkstra_sp_query (-1)"

definition dijkstra_sp_int_assn :: "nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> int list \<Rightarrow> nat list \<Rightarrow> dijkstra_sp_state \<Rightarrow> assn" where
  "dijkstra_sp_int_assn n fs ts ws sl = dijkstra_csr_all.sp_assn of_int n fs ts ws sl (\<lambda>_. False) False"

theorem dijkstra_shortest_path_int_correct:
  assumes "dijkstra_int_input n fs ts ws sl" "set gs \<subseteq> {..<n}"
  shows "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * Sa \<mapsto>\<^sub>a sl * Tv \<mapsto>\<^sub>a gs>
           dijkstra_shortest_path_int n Fa Ta Wa Sa Tv
         <\<lambda>r. case r of
             None \<Rightarrow> \<up>(\<forall>s \<in> set sl. \<forall>t \<in> set gs. \<not> multigraph_spec.reachable (edges fs ts) e_src e_tgt s t)
           | Some Pa \<Rightarrow> \<exists>\<^sub>Aids. Pa \<mapsto>\<^sub>a ids * \<up>(\<exists>t \<in> set gs.
               (\<exists>s \<in> set sl. multigraph_spec.is_shortest_path (edges fs ts) e_src e_tgt (int_weight ws)
                  (map (mk_edge fs ts) ids) s t) \<and>
               (\<forall>s \<in> set sl. \<forall>t' \<in> set gs. \<forall>q. multigraph_spec.path_bet (edges fs ts) e_src e_tgt q s t' \<longrightarrow>
                  distinct q \<longrightarrow> multigraph_spec.weight (int_weight ws) (map (mk_edge fs ts) ids) \<le>
                    multigraph_spec.weight (int_weight ws) q))>"
proof -
  interpret dijkstra_csr_all of_int "-1" n fs ts ws sl "\<lambda>v. v \<in> set gs" True
    unfolding dijkstra_csr_all_def by (rule dijkstra_int_input_csr[OF assms(1)])
  have w: "wt = int_weight ws" by (simp add: fun_eq_iff wt_def int_weight_def)
  show ?thesis unfolding dijkstra_shortest_path_int_def
    by (rule dijkstra_shortest_path_rule[unfolded w]) (use assms(2) in simp_all)
qed

theorem dijkstra_sp_compute_int_correct:
  assumes "dijkstra_int_input n fs ts ws sl"
  shows "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * Sa \<mapsto>\<^sub>a sl>
           dijkstra_sp_compute_int n Fa Ta Wa Sa <dijkstra_sp_int_assn n fs ts ws sl>"
proof -
  interpret dijkstra_csr_all of_int "-1" n fs ts ws sl "\<lambda>_. False" False
    unfolding dijkstra_csr_all_def by (rule dijkstra_int_input_csr[OF assms(1)])
  show ?thesis unfolding dijkstra_sp_compute_int_def dijkstra_sp_int_assn_def
    by (rule dijkstra_sp_compute_rule) simp_all
qed

theorem dijkstra_sp_query_int_correct:
  assumes "dijkstra_int_input n fs ts ws sl" "v \<in> verts fs ts"
  shows "<dijkstra_sp_int_assn n fs ts ws sl th> dijkstra_sp_query_int th v
         <\<lambda>r. dijkstra_sp_int_assn n fs ts ws sl th * (case r of
             None \<Rightarrow> \<up>(\<forall>s \<in> set sl. \<not> multigraph_spec.reachable (edges fs ts) e_src e_tgt s v)
           | Some Pa \<Rightarrow> \<exists>\<^sub>Aids. Pa \<mapsto>\<^sub>a ids * \<up>(\<exists>s \<in> set sl.
               multigraph_spec.is_shortest_path (edges fs ts) e_src e_tgt (int_weight ws)
                 (map (mk_edge fs ts) ids) s v))>"
proof -
  interpret dijkstra_csr_all of_int "-1" n fs ts ws sl "\<lambda>_. False" False
    unfolding dijkstra_csr_all_def by (rule dijkstra_int_input_csr[OF assms(1)])
  have w: "wt = int_weight ws" by (simp add: fun_eq_iff wt_def int_weight_def)
  show ?thesis unfolding dijkstra_sp_query_int_def dijkstra_sp_int_assn_def
    by (rule dijkstra_sp_query_rule[unfolded w]) (use assms(2) in simp_all)
qed


text \<open>The programs on integers on the graph of the runs above, with the sources 0 and 5. A path is
      printed as its edge indices. For the targets 2 and 4, the nearest target is 4, reached by the
      edge 5 from the source 5; for the target 3 it is the path of the edges 5 and 6; the target 6
      is unreachable. The queries give the paths to all vertices; the sources get the empty path.\<close>

ML_val \<open>
  let
    val nat = @{code nat_of_integer}
    val int = @{code int_of_integer}
    val i = @{code integer_of_nat}
    val n = 7
    val es = [(0, 1, 1), (0, 2, 4), (1, 2, 1), (2, 3, 2), (1, 3, 5),
              (5, 4, 1), (4, 3, 1), (3, 4, 3), (6, 0, 1)]
    val fa = Array.fromList (map (fn (u, _, _) => nat u) es)
    val ta = Array.fromList (map (fn (_, v, _) => nat v) es)
    val wa = Array.fromList (map (fn (_, _, w) => int w) es)
    val sa = Array.fromList (map nat [0, 5])
    fun path NONE = NONE
      | path (SOME a) = SOME (map i (Array.foldr (op ::) [] a))
    fun nearest gs =
      path (@{code dijkstra_shortest_path_int} (nat n) fa ta wa sa (Array.fromList (map nat gs)) ())
    val st = @{code dijkstra_sp_compute_int} (nat n) fa ta wa sa ()
    fun query v = (v, path (@{code dijkstra_sp_query_int} st (nat v) ()))
  in
    (map nearest [[2, 4], [3], [6]], map query [0, 1, 2, 3, 4, 5, 6])
  end
\<close>

end
