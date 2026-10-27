theory Push_Relabel_Instantiation
  imports
    Push_Relabel_FIFO_Imperative
    Push_Relabel_RTF_Imperative
    Push_Relabel_HL_Imperative
    Push_Relabel_Label_Buckets_Imperative
    Directed_Set_Graphs.CSR_Edge_Input
    Directed_Set_Graphs.CSR_Graph_Reset_To
    Data_Structures.Imp_Array_Ring_Queue
    Data_Structures.Imp_Array_Move_To_Front_List
    Data_Structures.Imp_Array_Buckets
    Data_Structures.Imp_Bool_Set_Iterate
begin

section \<open>The Push-Relabel Algorithm on Arrays\<close>

text \<open>The input is a network with vertices below \<open>n\<close>, given by three arrays of length \<open>m\<close>: the
      first endpoints, the second endpoints and the capacities of the edges. The edges are the
      numbers \<open>i < m\<close>; the endpoints of \<open>i\<close> are read from the \<open>i\<close>-th entries of the first two
      arrays. All maps on the edges are arrays indexed by the edge number, all
      maps on the vertices arrays indexed by the vertex. The outgoing and the ingoing edges are
      two CSR collections with position arrays, so that the iterator of a vertex can be set to
      a given edge. The labels are kept with buckets of the vertices by label, the vertex set
      is a Boolean array, and the strategies use a ring buffer (FIFO), a move-to-front list
      (relabel-to-front) and buckets (highest label), all on arrays.

      Everything is allocated once, before the computation starts.\<close>

subsection \<open>The Programs\<close>

text \<open>The label map with buckets.\<close>

global_interpretation pr_lb: label_buckets_imp_code N "arr_lookup_imp id" "arr_upd_imp id"
    abk_insert_imp abk_remove_imp abk_pick_imp
  for N
  defines pr_lower = pr_lb.lower_imp
    and pr_lb_get = pr_lb.lb_get_imp
    and pr_lb_upd = pr_lb.lb_upd_imp
    and pr_drain = pr_lb.drain_imp
    and pr_gap_walk = pr_lb.gap_walk_imp
    and pr_lb_gap_fold = pr_lb.lb_gap_fold_imp
    and pr_lb_init = pr_lb.lb_init_imp
  done

declare pr_lb.lower_imp.simps[code] pr_lb.drain_imp.simps[code] pr_lb.gap_walk_imp.simps[code]

text \<open>The generic operations. The endpoints of an edge are read from the input arrays. The
      number of vertices is \<open>nv\<close>.\<close>

global_interpretation pr_ops: push_relabel_ops_imp_code src_imp tgt_imp s t nv
    "arr_lookup_imp id" "arr_upd_imp id" "arr_lookup_imp id" "arr_upd_imp id"
    pr_lb_get "pr_lb_upd nv" "arr_lookup_imp id" "arr_upd_imp id"
    csr_rt_current_imp csr_rt_has_imp csr_rt_move_imp csr_rt_reset_imp "csr_reset_to_imp id"
    csr_rt_current_imp csr_rt_has_imp csr_rt_move_imp csr_rt_reset_imp "csr_reset_to_imp id"
    pr_lb_gap_fold csr_rt_edges_fold_imp
  for s t nv
  defines pr_admissible_fwd = pr_ops.admissible_fwd_imp
    and pr_admissible_bwd = pr_ops.admissible_bwd_imp
    and pr_augment = pr_ops.augment_imp
    and pr_push_fwd = pr_ops.push_fwd_imp
    and pr_push_bwd = pr_ops.push_bwd_imp
    and pr_skip_scan = pr_ops.skip_scan_imp
    and pr_skip = pr_ops.skip_imp
    and pr_move = pr_ops.move_imp
    and pr_advance = pr_ops.advance_imp
    and pr_change_label = pr_ops.change_label_imp
    and pr_min_set = pr_ops.min_set_imp
    and pr_min_scan = pr_ops.min_scan_imp
    and pr_new_label = pr_ops.new_label_imp
    and pr_relabel = pr_ops.relabel_imp
    and pr_gap_step = pr_ops.gap_step_imp
    and pr_gap = pr_ops.gap_imp
    and pr_relabel_gap = pr_ops.relabel_gap_imp
    and pr_apply_op = pr_ops.apply_op_imp
    and pr_init_step = pr_ops.init_step_imp
    and pr_init = pr_ops.init_imp
    and pr_discharge_op = pr_ops.discharge_op_imp
  done

declare pr_ops.skip_scan_imp.simps[code] pr_ops.min_scan_imp.simps[code]
  pr_ops.apply_op_imp.simps[code]

text \<open>The strategies. The imperative vertex fold walks the Boolean array of the vertex set.\<close>

abbreviation "bool_array_set_fold_imp \<equiv> iter_set_fold_imp bool_array_set_it_init bool_array_set_it_has_next bool_array_set_it_next"

global_interpretation pr_fifo: push_relabel_fifo_imp_code src_imp tgt_imp s t nv
    "arr_lookup_imp id" "arr_upd_imp id" "arr_lookup_imp id" "arr_upd_imp id"
    pr_lb_get "pr_lb_upd nv" "arr_lookup_imp id" "arr_upd_imp id"
    csr_rt_current_imp csr_rt_has_imp csr_rt_move_imp csr_rt_reset_imp "csr_reset_to_imp id"
    csr_rt_current_imp csr_rt_has_imp csr_rt_move_imp csr_rt_reset_imp "csr_reset_to_imp id"
    pr_lb_gap_fold csr_rt_edges_fold_imp "arq_push_imp nv" "arq_pop_imp nv" arq_is_empty_imp
    bool_array_set_fold_imp
  for s t nv
  defines pr_fifo_after_push = pr_fifo.fifo_after_push_imp
    and pr_fifo_ctx_upd = pr_fifo.fifo_ctx_upd_imp
    and pr_fifo_discharge = pr_fifo.fifo_discharge_imp
    and pr_fifo_select = pr_fifo.fifo_select_imp
    and pr_fifo_init_step = pr_fifo.fifo_init_step_imp
    and pr_fifo_init_ctx = pr_fifo.fifo_init_ctx_imp
  done

global_interpretation pr_fifo_loop: push_relabel_imp_code src_imp tgt_imp s t nv
    "arr_lookup_imp id" "arr_upd_imp id" "arr_lookup_imp id" "arr_upd_imp id"
    pr_lb_get "pr_lb_upd nv" "arr_lookup_imp id" "arr_upd_imp id"
    csr_rt_current_imp csr_rt_has_imp csr_rt_move_imp csr_rt_reset_imp "csr_reset_to_imp id"
    csr_rt_current_imp csr_rt_has_imp csr_rt_move_imp csr_rt_reset_imp "csr_reset_to_imp id"
    pr_lb_gap_fold csr_rt_edges_fold_imp "pr_fifo_select s t nv" "pr_fifo_init_ctx s t nv"
  for s t nv
  defines pr_fifo_main_loop = pr_fifo_loop.push_relabel_loop_imp
    and pr_fifo_main = pr_fifo_loop.push_relabel_imp
  done

global_interpretation pr_rtf: push_relabel_rtf_imp_code src_imp tgt_imp s t nv
    "arr_lookup_imp id" "arr_upd_imp id" "arr_lookup_imp id" "arr_upd_imp id"
    pr_lb_get "pr_lb_upd nv" "arr_lookup_imp id" "arr_upd_imp id"
    csr_rt_current_imp csr_rt_has_imp csr_rt_move_imp csr_rt_reset_imp "csr_reset_to_imp id"
    csr_rt_current_imp csr_rt_has_imp csr_rt_move_imp csr_rt_reset_imp "csr_reset_to_imp id"
    pr_lb_gap_fold csr_rt_edges_fold_imp amtf_push_front_imp amtf_move_to_front_imp amtf_first_imp
    amtf_next_imp bool_array_set_fold_imp
  for s t nv
  defines pr_rtf_scan = pr_rtf.rtf_scan_imp
    and pr_rtf_discharge = pr_rtf.rtf_discharge_imp
    and pr_rtf_stop = pr_rtf.rtf_stop_imp
    and pr_rtf_next = pr_rtf.rtf_next_imp
    and pr_rtf_select = pr_rtf.rtf_select_imp
    and pr_rtf_init_step = pr_rtf.rtf_init_step_imp
    and pr_rtf_init_ctx = pr_rtf.rtf_init_ctx_imp
  done

global_interpretation pr_rtf_loop: push_relabel_imp_code src_imp tgt_imp s t nv
    "arr_lookup_imp id" "arr_upd_imp id" "arr_lookup_imp id" "arr_upd_imp id"
    pr_lb_get "pr_lb_upd nv" "arr_lookup_imp id" "arr_upd_imp id"
    csr_rt_current_imp csr_rt_has_imp csr_rt_move_imp csr_rt_reset_imp "csr_reset_to_imp id"
    csr_rt_current_imp csr_rt_has_imp csr_rt_move_imp csr_rt_reset_imp "csr_reset_to_imp id"
    pr_lb_gap_fold csr_rt_edges_fold_imp "pr_rtf_select nv" "pr_rtf_init_ctx s t"
  for s t nv
  defines pr_rtf_main_loop = pr_rtf_loop.push_relabel_loop_imp
    and pr_rtf_main = pr_rtf_loop.push_relabel_imp
  done

global_interpretation pr_hl: push_relabel_hl_imp_code src_imp tgt_imp s t nv
    "arr_lookup_imp id" "arr_upd_imp id" "arr_lookup_imp id" "arr_upd_imp id"
    pr_lb_get "pr_lb_upd nv" "arr_lookup_imp id" "arr_upd_imp id"
    csr_rt_current_imp csr_rt_has_imp csr_rt_move_imp csr_rt_reset_imp "csr_reset_to_imp id"
    csr_rt_current_imp csr_rt_has_imp csr_rt_move_imp csr_rt_reset_imp "csr_reset_to_imp id"
    pr_lb_gap_fold csr_rt_edges_fold_imp abk_insert_imp abk_remove_imp abk_pick_imp abk_move_imp
    bool_array_set_fold_imp
  for s t nv
  defines pr_hl_find = pr_hl.hl_find_imp
    and pr_hl_insert = pr_hl.hl_insert_imp
    and pr_hl_after_push = pr_hl.hl_after_push_imp
    and pr_hl_lift = pr_hl.hl_lift_imp
    and pr_hl_after_relabel = pr_hl.hl_after_relabel_imp
    and pr_hl_ctx_upd = pr_hl.hl_ctx_upd_imp
    and pr_hl_discharge = pr_hl.hl_discharge_imp
    and pr_hl_select = pr_hl.hl_select_imp
    and pr_hl_init_step = pr_hl.hl_init_step_imp
    and pr_hl_init_ctx = pr_hl.hl_init_ctx_imp
  done

global_interpretation pr_hl_loop: push_relabel_imp_code src_imp tgt_imp s t nv
    "arr_lookup_imp id" "arr_upd_imp id" "arr_lookup_imp id" "arr_upd_imp id"
    pr_lb_get "pr_lb_upd nv" "arr_lookup_imp id" "arr_upd_imp id"
    csr_rt_current_imp csr_rt_has_imp csr_rt_move_imp csr_rt_reset_imp "csr_reset_to_imp id"
    csr_rt_current_imp csr_rt_has_imp csr_rt_move_imp csr_rt_reset_imp "csr_reset_to_imp id"
    pr_lb_gap_fold csr_rt_edges_fold_imp "pr_hl_select s t nv" "pr_hl_init_ctx s t"
  for s t nv
  defines pr_hl_main_loop = pr_hl_loop.push_relabel_loop_imp
    and pr_hl_main = pr_hl_loop.push_relabel_imp
  done

declare pr_fifo_loop.push_relabel_loop_imp.simps[code] pr_rtf_loop.push_relabel_loop_imp.simps[code]
  pr_hl_loop.push_relabel_loop_imp.simps[code] pr_rtf.rtf_scan_imp.simps[code]
  pr_hl.hl_find_imp.simps[code] pr_hl.hl_lift_imp.simps[code]
  iter_fold.simps[code] bool_array_set_scan.simps[code] foldl_range_imp.simps[code]

subsection \<open>Allocation and Initialisation\<close>

text \<open>The vertex set, the endpoints of the edges, is collected in a Boolean array by one pass
      over the edges, which also counts the vertices.\<close>

definition pr_vertex_count_step :: "bool array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "pr_vertex_count_step Vi u c = do {
     b \<leftarrow> Array.nth Vi u;
     if b then return c else do { bool_array_set_insert_imp u Vi; return (Suc c) } }"

definition pr_vertex_set_imp :: "nat array \<Rightarrow> nat array \<Rightarrow> bool array \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "pr_vertex_set_imp Fa Ta Vi m =
     foldl_range_imp (\<lambda> i c. do {
       u \<leftarrow> Array.nth Fa i;
       v \<leftarrow> Array.nth Ta i;
       c' \<leftarrow> pr_vertex_count_step Vi u c;
       pr_vertex_count_step Vi v c' }) 0 m 0"

text \<open>A CSR collection with its position and cursor arrays, built by \<open>build\<close> from the edges.\<close>

definition pr_csr_setup :: "(nat \<Rightarrow> nat array \<times> nat array \<Rightarrow> nat \<Rightarrow> (nat array \<times> nat array) Heap) \<Rightarrow>
   nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> nat csr_rt_imp Heap" where
  "pr_csr_setup build n Fa Ta m = do {
     (Ba, Ea) \<leftarrow> build n (Fa, Ta) 0;
     Pa \<leftarrow> Array.new m 0;
     csr_pos_build_imp id Ea Pa m;
     Oa \<leftarrow> csr_cursor_init n Ba;
     return (Ba, Ea, Oa, Pa) }"

text \<open>Everything the three strategies share: the outgoing and the ingoing CSR collections with
      their position and cursor arrays, the vertex set and its size, the residual capacities, the
      excesses, the labels with their buckets (initialised), the counts and the references for
      the minimum of a relabelling scan. The capacity array of the input is used in place.\<close>

definition push_relabel_setup :: "nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> 'n::{linordered_idom, heap} array \<Rightarrow>
   (('n array, 'n array, nat array \<times> abki \<times> nat ref, nat array, nat csr_rt_imp,
     nat array \<times> nat array, nat) pr_imp \<times>
    bool array \<times> nat) Heap" where
  "push_relabel_setup n Fa Ta Ca = do {
     m \<leftarrow> Array.len Fa;
     Oi \<leftarrow> pr_csr_setup csr_build_edges n Fa Ta m;
     Ii \<leftarrow> pr_csr_setup csr_build_edges_tgt n Fa Ta m;
     Vi \<leftarrow> Array.new n False;
     nv \<leftarrow> pr_vertex_set_imp Fa Ta Vi m;
     Fw \<leftarrow> Array.new m 0;
     Bw \<leftarrow> Array.new m 0;
     Xa \<leftarrow> Array.new n 0;
     La \<leftarrow> Array.new n 0;
     Lb \<leftarrow> abk_empty_imp n nv;
     Dr \<leftarrow> ref 0;
     pr_lb_init (bool_array_set_fold_imp Vi) (La, Lb, Dr);
     Cn \<leftarrow> Array.new (2 * nv) 0;
     Mf \<leftarrow> ref False;
     Mk \<leftarrow> ref 0;
     Md \<leftarrow> ref 0;
     return (\<lparr>pi_fwd = Fw, pi_bwd = Bw, pi_caps = Ca, pi_ex = Xa, pi_lab = (La, Lb, Dr), pi_cnt = Cn,
              pi_out = Oi, pi_in = Ii, pi_ends = (Fa, Ta), pi_mf = Mf, pi_mk = Mk, pi_md = Md\<rparr>,
             Vi, nv) }"

text \<open>The three programs take the bound \<open>n\<close> on the vertices, the source \<open>s\<close>, the sink \<open>t\<close>,
      and the arrays of the first endpoints, the second endpoints and the capacities. They
      return the array of the flow by edge number.\<close>

definition push_relabel_fifo_run ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> 'n::{linordered_idom, heap} array \<Rightarrow> 'n array Heap" where
  "push_relabel_fifo_run n s t Fa Ta Ca = do {
     (Si, Vi, nv) \<leftarrow> push_relabel_setup n Fa Ta Ca;
     Qi \<leftarrow> arq_empty_imp nv 0;
     Cf \<leftarrow> ref False;
     Cu \<leftarrow> ref 0;
     pr_fifo_main s t nv (Qi, Cf, Cu, Vi) Si;
     return (pi_bwd Si) }"

definition push_relabel_rtf_run ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> 'n::{linordered_idom, heap} array \<Rightarrow> 'n array Heap" where
  "push_relabel_rtf_run n s t Fa Ta Ca = do {
     (Si, Vi, nv) \<leftarrow> push_relabel_setup n Fa Ta Ca;
     Ls \<leftarrow> amtf_empty_imp n;
     Cf \<leftarrow> ref False;
     Cu \<leftarrow> ref 0;
     Rr \<leftarrow> ref False;
     pr_rtf_main s t nv (Ls, Cf, Cu, Rr, Vi) Si;
     return (pi_bwd Si) }"

definition push_relabel_hl_run ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> 'n::{linordered_idom, heap} array \<Rightarrow> 'n array Heap" where
  "push_relabel_hl_run n s t Fa Ta Ca = do {
     (Si, Vi, nv) \<leftarrow> push_relabel_setup n Fa Ta Ca;
     Bi \<leftarrow> abk_empty_imp n (2 * nv);
     Br \<leftarrow> ref 0;
     Cf \<leftarrow> ref False;
     Cu \<leftarrow> ref 0;
     pr_hl_main s t nv (Bi, Br, Cf, Cu, Vi) Si;
     return (pi_bwd Si) }"

definition push_relabel_fifo_run_int :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> int array \<Rightarrow> int array Heap"
  where "push_relabel_fifo_run_int = push_relabel_fifo_run"
definition push_relabel_rtf_run_int :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> int array \<Rightarrow> int array Heap"
  where "push_relabel_rtf_run_int = push_relabel_rtf_run"
definition push_relabel_hl_run_int :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> int array \<Rightarrow> int array Heap"
  where "push_relabel_hl_run_int = push_relabel_hl_run"

text \<open>In the generated code, the loops contain no allocation. All allocations are in the run
      functions and @{const push_relabel_setup}, before the computation begins.\<close>


section \<open>Correctness\<close>

subsection \<open>The Input\<close>

text \<open>The endpoints are below \<open>n\<close>, the capacities are non-negative, and the source and the sink
      are two different vertices of the network, i.e. endpoints of edges.\<close>

locale push_relabel_input = real_embedding h
  for h :: "'n::{linordered_idom, heap} \<Rightarrow> real" +
  fixes n :: nat
    and fs ts :: "nat list"
    and cs :: "'n list"
    and s t :: nat
  assumes ts_length: "length ts = length fs"
    and cs_length: "length cs = length fs"
    and fs_bound: "\<And> u. u \<in> set fs \<Longrightarrow> u < n"
    and ts_bound: "\<And> v. v \<in> set ts \<Longrightarrow> v < n"
    and cs_nonneg: "\<And> c. c \<in> set cs \<Longrightarrow> 0 \<le> c"
    and s_vert: "s \<in> verts fs ts"
    and t_vert: "t \<in> verts fs ts"
    and s_neq_t: "s \<noteq> t"
begin

text \<open>The network: the edges of the input with their capacities.\<close>

definition "cap_of e = (if e \<in> edges fs then h (cs ! e) else 0)"

sublocale flow_network where \<E> = "edges fs" and fst = "e_src fs" and snd = "e_tgt fs ts"
    and create_edge = "e_new fs" and \<u> = "\<lambda> e. ereal (cap_of e)"
  using s_vert cs_nonneg cs_length
  by unfold_locales (auto simp: edges_def dVs_def cap_of_def)

text \<open>The edges grouped by their first and by their second endpoints, and the position arrays.\<close>

sublocale out: csr_edge_input n fs ts "e_src fs" src_imp
  by unfold_locales
     (use ts_length fs_bound ts_bound src_imp_rule[of _ fs ts] in auto)

sublocale inc: csr_edge_input n fs ts "e_tgt fs ts" tgt_imp
  by unfold_locales
     (use ts_length fs_bound ts_bound tgt_imp_rule[of _ fs ts] in auto)

definition "Po = csr_pos_list id out.inp.E_spec (replicate (length fs) 0)"
definition "Pin = csr_pos_list id inc.inp.E_spec (replicate (length fs) 0)"

sublocale out_rt: csr_graph_reset_to n "verts fs ts" out.inp.B_spec out.inp.E_spec id Po
  unfolding Po_def
  by (rule csr_graph_reset_to_pos_list)
     (simp_all add: out.graph.csr_graph_axioms out.E_spec_distinct out.E_spec_ids)

sublocale in_rt: csr_graph_reset_to n "verts fs ts" inc.inp.B_spec inc.inp.E_spec id Pin
  unfolding Pin_def
  by (rule csr_graph_reset_to_pos_list)
     (simp_all add: inc.graph.csr_graph_axioms inc.E_spec_distinct inc.E_spec_ids)

text \<open>The maps: on the edges by edge number, on the vertices by vertex.\<close>

sublocale ea: key_array "length fs" id "edges fs" h
  by (rule out.edge_key_array)

sublocale va: key_array n id "verts fs ts" h
  by (rule out.vert_key_array)

sublocale la: key_array n id "verts fs ts" "id :: nat \<Rightarrow> nat"
  by (rule out.vert_key_array)

sublocale ca: key_array "2 * card (verts fs ts)" id "{..<2 * card (verts fs ts)}" "id :: nat \<Rightarrow> nat"
  by unfold_locales simp_all

text \<open>The labels with their buckets: buckets over all vertices below \<open>n\<close>, restricted to the
      vertices of the network.\<close>

abbreviation "nV \<equiv> card (verts fs ts)"

abbreviation "vfold \<equiv> (\<lambda> g acc. foldl g acc (sorted_list_of_set (verts fs ts)))"

lemma vfold: "\<exists> vs. distinct vs \<and> set vs = verts fs ts \<and> vfold g acc = foldl g acc vs"
  by (intro exI[of _ "sorted_list_of_set (verts fs ts)"]) (simp add: \<V>_finite)

sublocale lbk: fixed_univ_buckets_imp "verts fs ts" "{..<nV}"
    "restr_buckets_invar (verts fs ts) (abk_invar n nV) (abk_abstract n nV)" "abk_abstract n nV"
    abk_empty abk_insert abk_remove abk_pick abk_move "abk_assn n nV" "abk_empty_imp n nV"
    abk_insert_imp abk_remove_imp abk_pick_imp abk_move_imp
  by (rule fixed_univ_buckets_imp.fixed_univ_buckets_imp_restrict[OF abk_fixed_univ_buckets_imp
        out.verts_bound])

sublocale lb: label_buckets_imp "verts fs ts" nV "\<lambda> _. True" arr_upd arr_lookup
    "restr_buckets_invar (verts fs ts) (abk_invar n nV) (abk_abstract n nV)" "abk_abstract n nV"
    abk_empty abk_insert abk_remove abk_pick abk_move "\<lambda> _. 0" vfold "arr_lookup_imp id"
    "arr_upd_imp id" abk_insert_imp abk_remove_imp abk_pick_imp la.arr_assn "abk_assn n nV"
    "abk_empty_imp n nV" abk_move_imp
  using V_non_empt
  by unfold_locales (simp_all add: \<V>_finite vfold arr_lookup_def[abs_def])

subsection \<open>The Generic Algorithm\<close>

lemma out_iterator: "outgoing_edge_iterator (edges fs) (e_tgt fs ts) (e_src fs) out.graph.csr_invar
    out.graph.csr_abstract out.graph.csr_current out.graph.csr_has out.graph.csr_iterated
    out.graph.csr_remaining out.graph.csr_move out.graph.csr_reset"
  unfolding outgoing_edge_iterator_def
  by (rule out.graph.csr.indexed_iterable_set_axioms)

lemma in_iterator: "ingoing_edge_iterator (edges fs) (e_tgt fs ts) (e_src fs) inc.graph.csr_invar
    inc.graph.csr_abstract inc.graph.csr_current inc.graph.csr_has inc.graph.csr_iterated
    inc.graph.csr_remaining inc.graph.csr_move inc.graph.csr_reset"
  unfolding ingoing_edge_iterator_def
  by (rule inc.graph.csr.indexed_iterable_set_axioms)

sublocale pr: push_relabel_ops_imp where \<E> = "edges fs" and fst = "e_src fs" and snd = "e_tgt fs ts"
    and create_edge = "e_new fs" and \<u> = "\<lambda> e. ereal (cap_of e)"
    and emap_invar = "\<lambda> _. True" and emap_upd = arr_upd and emap_get = arr_lookup
    and ex_invar = "\<lambda> _. True" and ex_upd = arr_upd and ex_get = arr_lookup
    and label_invar = lb.lb_invar and label_upd = lb.lb_upd and label_get = lb.lb_get
    and count_invar = "\<lambda> _. True" and count_upd = arr_upd and count_get = arr_lookup
    and out_invar = out.graph.csr_invar and out_abstract = out.graph.csr_abstract
    and out_current = out.graph.csr_current and out_has = out.graph.csr_has
    and out_iterated = out.graph.csr_iterated and out_remaining = out.graph.csr_remaining
    and out_move = out.graph.csr_move and out_reset = out.graph.csr_reset
    and in_invar = inc.graph.csr_invar and in_abstract = inc.graph.csr_abstract
    and in_current = inc.graph.csr_current and in_has = inc.graph.csr_has
    and in_iterated = inc.graph.csr_iterated and in_remaining = inc.graph.csr_remaining
    and in_move = inc.graph.csr_move and in_reset = inc.graph.csr_reset
    and out_reset_to = out_rt.csr_reset_to and in_reset_to = in_rt.csr_reset_to
    and caps = cap_of and num_verts = nV and gap_fold = lb.lb_gap_fold
    and edge_fold = "\<lambda> g acc. foldl g acc out.inp.E_spec"
    and emap_init = "\<lambda> _. h 0" and ex_init = "\<lambda> _. h 0" and label_init = lb.lb_init
    and count_init = "\<lambda> _. id 0" and out_init = "\<lambda> v. out.inp.B_spec ! v"
    and in_init = "\<lambda> v. inc.inp.B_spec ! v"
    and emap_get_imp = "arr_lookup_imp id" and emap_upd_imp = "arr_upd_imp id"
    and ex_get_imp = "arr_lookup_imp id" and ex_upd_imp = "arr_upd_imp id"
    and label_get_imp = pr_lb_get and label_upd_imp = "pr_lb_upd nV"
    and count_get_imp = "arr_lookup_imp id" and count_upd_imp = "arr_upd_imp id"
    and out_current_imp = csr_rt_current_imp and out_has_imp = csr_rt_has_imp
    and out_move_imp = csr_rt_move_imp and out_reset_imp = csr_rt_reset_imp
    and out_reset_to_imp = "csr_reset_to_imp id"
    and in_current_imp = csr_rt_current_imp and in_has_imp = csr_rt_has_imp
    and in_move_imp = csr_rt_move_imp and in_reset_imp = csr_rt_reset_imp
    and in_reset_to_imp = "csr_reset_to_imp id"
    and gap_fold_imp = pr_lb_gap_fold and edge_fold_imp = csr_rt_edges_fold_imp
    and emap_assn = ea.arr_assn and ex_assn = va.arr_assn and label_assn = lb.lb_assn
    and count_assn = ca.arr_assn and out_assn = out_rt.csr_rt_assn and in_assn = in_rt.csr_rt_assn
    and fst_imp = src_imp and snd_imp = tgt_imp and ends_assn = "ends_assn fs ts"
proof(unfold_locales, goal_cases)
  case (10 g acc)
  show ?case
    using out.E_spec_distinct out.E_spec_edges
    by blast
next
  case 15
  show ?case
    unfolding outgoing_edge_iterator.out_graph_inv_def[OF out_iterator]
    using out.graph.csr_init_invar
    by (auto simp: out.csr_abstract_key delta_plus_def)
next
  case 16
  show ?case
    unfolding ingoing_edge_iterator.in_graph_inv_def[OF in_iterator]
    using inc.graph.csr_init_invar
    by (auto simp: inc.csr_abstract_key delta_minus_def)
next
  case (17 A k Ai)
  thus ?case
    unfolding pr_lb_get_def
    by (rule lb.lb_get_imp_rule)
next
  case (18 A k Ai v)
  thus ?case
    unfolding pr_lb_upd_def
    by (rule lb.lb_upd_imp_rule)
next
  case (19 e Ei)
  thus ?case
    using src_imp_rule[of e fs ts Ei]
    by simp
next
  case (20 e Ei)
  thus ?case
    using tgt_imp_rule[of e fs ts Ei] ts_length
    by simp
next
  case (21 l k g g_imp R r Li)
  thus ?case
    unfolding pr_lb_gap_fold_def
    by (rule lb.lb_gap_fold_imp_rule)
next
  case (22 g g_imp P R acc og Oi)
  thus ?case
    using out.E_spec_edges
    by (intro out_rt.csr_rt_edges_fold_imp_rule[where I = P]) auto
qed (fact fixed_univ_map.fixed_univ_map_upd[OF lb.lb_fixed_univ_map] s_vert t_vert s_neq_t
          fixed_univ_map.fixed_univ_map_upd_invar[OF lb.lb_fixed_univ_map] lb.lb_gap_fold lb.lb_init_props
     | simp add: arr_lookup_def[abs_def])+

text \<open>The imperative vertex fold of the strategies walks the Boolean array of the vertex set.\<close>

lemma vset_fold:
  "set_fold_imp_rule (verts fs ts) (bool_array_set_assn n (verts fs ts) Vi) vfold (bool_array_set_fold_imp Vi)"
  using fixed_univ_set_iterate_imp.iter_set_fold_imp_rule[OF bool_array_set_fixed_univ_set_iterate_imp,
          of "verts fs ts"] out.verts_bound \<V>_finite
  by simp

subsection \<open>The Strategies\<close>

text \<open>FIFO: the queue is a ring buffer with one place per vertex.\<close>

sublocale fifo: push_relabel_fifo_imp where \<E> = "edges fs" and fst = "e_src fs" and snd = "e_tgt fs ts"
    and create_edge = "e_new fs" and \<u> = "\<lambda> e. ereal (cap_of e)"
    and emap_invar = "\<lambda> _. True" and emap_upd = arr_upd and emap_get = arr_lookup
    and ex_invar = "\<lambda> _. True" and ex_upd = arr_upd and ex_get = arr_lookup
    and label_invar = lb.lb_invar and label_upd = lb.lb_upd and label_get = lb.lb_get
    and count_invar = "\<lambda> _. True" and count_upd = arr_upd and count_get = arr_lookup
    and out_invar = out.graph.csr_invar and out_abstract = out.graph.csr_abstract
    and out_current = out.graph.csr_current and out_has = out.graph.csr_has
    and out_iterated = out.graph.csr_iterated and out_remaining = out.graph.csr_remaining
    and out_move = out.graph.csr_move and out_reset = out.graph.csr_reset
    and in_invar = inc.graph.csr_invar and in_abstract = inc.graph.csr_abstract
    and in_current = inc.graph.csr_current and in_has = inc.graph.csr_has
    and in_iterated = inc.graph.csr_iterated and in_remaining = inc.graph.csr_remaining
    and in_move = inc.graph.csr_move and in_reset = inc.graph.csr_reset
    and out_reset_to = out_rt.csr_reset_to and in_reset_to = in_rt.csr_reset_to
    and caps = cap_of and num_verts = nV and gap_fold = lb.lb_gap_fold
    and edge_fold = "\<lambda> g acc. foldl g acc out.inp.E_spec"
    and emap_init = "\<lambda> _. h 0" and ex_init = "\<lambda> _. h 0" and label_init = lb.lb_init
    and count_init = "\<lambda> _. id 0" and out_init = "\<lambda> v. out.inp.B_spec ! v"
    and in_init = "\<lambda> v. inc.inp.B_spec ! v"
    and emap_get_imp = "arr_lookup_imp id" and emap_upd_imp = "arr_upd_imp id"
    and ex_get_imp = "arr_lookup_imp id" and ex_upd_imp = "arr_upd_imp id"
    and label_get_imp = pr_lb_get and label_upd_imp = "pr_lb_upd nV"
    and count_get_imp = "arr_lookup_imp id" and count_upd_imp = "arr_upd_imp id"
    and out_current_imp = csr_rt_current_imp and out_has_imp = csr_rt_has_imp
    and out_move_imp = csr_rt_move_imp and out_reset_imp = csr_rt_reset_imp
    and out_reset_to_imp = "csr_reset_to_imp id"
    and in_current_imp = csr_rt_current_imp and in_has_imp = csr_rt_has_imp
    and in_move_imp = csr_rt_move_imp and in_reset_imp = csr_rt_reset_imp
    and in_reset_to_imp = "csr_reset_to_imp id"
    and gap_fold_imp = pr_lb_gap_fold and edge_fold_imp = csr_rt_edges_fold_imp
    and emap_assn = ea.arr_assn and ex_assn = va.arr_assn and label_assn = lb.lb_assn
    and count_assn = ca.arr_assn and out_assn = out_rt.csr_rt_assn and in_assn = in_rt.csr_rt_assn
    and fst_imp = src_imp and snd_imp = tgt_imp and ends_assn = "ends_assn fs ts"
    and qcap = nV and queue_invar = "arq_invar nV" and queue_abstract = "arq_abstract nV"
    and queue_empty = "arq_empty 0" and queue_push = "arq_push nV" and queue_pop = "arq_pop nV"
    and queue_is_empty = arq_is_empty and queue_vertex_fold = vfold
    and queue_push_imp = "arq_push_imp nV" and queue_pop_imp = "arq_pop_imp nV"
    and queue_is_empty_imp = arq_is_empty_imp and vertex_fold_imp = bool_array_set_fold_imp
    and queue_assn = "arq_assn nV" and queue_empty_imp = "arq_empty_imp nV 0"
    and vset_assn = "bool_array_set_assn n (verts fs ts)"
  by unfold_locales
     (fact bounded_queue.queue_capacity[OF arq_bounded_queue] bounded_queue.queue_empty[OF arq_bounded_queue]
           bounded_queue.queue_push[OF arq_bounded_queue] bounded_queue.queue_pop[OF arq_bounded_queue]
           bounded_queue.queue_is_empty[OF arq_bounded_queue] vfold vset_fold
           bounded_queue_imp.queue_empty_rule[OF arq_bounded_queue_imp]
           bounded_queue_imp.queue_push_rule[OF arq_bounded_queue_imp]
           bounded_queue_imp.queue_pop_rule[OF arq_bounded_queue_imp]
           bounded_queue_imp.queue_is_empty_rule[OF arq_bounded_queue_imp] | simp)+

text \<open>Relabel-to-front: the move-to-front list over all vertices below \<open>n\<close>, restricted to the
      vertices of the network.\<close>

sublocale vl: fixed_univ_list_imp "verts fs ts"
    "restr_list_invar (verts fs ts) (amtf_invar n) (amtf_abstract n)" "amtf_abstract n" amtf_empty
    amtf_push_front amtf_move_to_front amtf_first amtf_next "amtf_assn n" "amtf_empty_imp n"
    amtf_push_front_imp amtf_move_to_front_imp amtf_first_imp amtf_next_imp
  by (rule fixed_univ_list_imp.fixed_univ_list_imp_restrict[OF amtf_fixed_univ_list_imp
        out.verts_bound])

sublocale rtf: push_relabel_rtf_imp where \<E> = "edges fs" and fst = "e_src fs" and snd = "e_tgt fs ts"
    and create_edge = "e_new fs" and \<u> = "\<lambda> e. ereal (cap_of e)"
    and emap_invar = "\<lambda> _. True" and emap_upd = arr_upd and emap_get = arr_lookup
    and ex_invar = "\<lambda> _. True" and ex_upd = arr_upd and ex_get = arr_lookup
    and label_invar = lb.lb_invar and label_upd = lb.lb_upd and label_get = lb.lb_get
    and count_invar = "\<lambda> _. True" and count_upd = arr_upd and count_get = arr_lookup
    and out_invar = out.graph.csr_invar and out_abstract = out.graph.csr_abstract
    and out_current = out.graph.csr_current and out_has = out.graph.csr_has
    and out_iterated = out.graph.csr_iterated and out_remaining = out.graph.csr_remaining
    and out_move = out.graph.csr_move and out_reset = out.graph.csr_reset
    and in_invar = inc.graph.csr_invar and in_abstract = inc.graph.csr_abstract
    and in_current = inc.graph.csr_current and in_has = inc.graph.csr_has
    and in_iterated = inc.graph.csr_iterated and in_remaining = inc.graph.csr_remaining
    and in_move = inc.graph.csr_move and in_reset = inc.graph.csr_reset
    and out_reset_to = out_rt.csr_reset_to and in_reset_to = in_rt.csr_reset_to
    and caps = cap_of and num_verts = nV and gap_fold = lb.lb_gap_fold
    and edge_fold = "\<lambda> g acc. foldl g acc out.inp.E_spec"
    and emap_init = "\<lambda> _. h 0" and ex_init = "\<lambda> _. h 0" and label_init = lb.lb_init
    and count_init = "\<lambda> _. id 0" and out_init = "\<lambda> v. out.inp.B_spec ! v"
    and in_init = "\<lambda> v. inc.inp.B_spec ! v"
    and emap_get_imp = "arr_lookup_imp id" and emap_upd_imp = "arr_upd_imp id"
    and ex_get_imp = "arr_lookup_imp id" and ex_upd_imp = "arr_upd_imp id"
    and label_get_imp = pr_lb_get and label_upd_imp = "pr_lb_upd nV"
    and count_get_imp = "arr_lookup_imp id" and count_upd_imp = "arr_upd_imp id"
    and out_current_imp = csr_rt_current_imp and out_has_imp = csr_rt_has_imp
    and out_move_imp = csr_rt_move_imp and out_reset_imp = csr_rt_reset_imp
    and out_reset_to_imp = "csr_reset_to_imp id"
    and in_current_imp = csr_rt_current_imp and in_has_imp = csr_rt_has_imp
    and in_move_imp = csr_rt_move_imp and in_reset_imp = csr_rt_reset_imp
    and in_reset_to_imp = "csr_reset_to_imp id"
    and gap_fold_imp = pr_lb_gap_fold and edge_fold_imp = csr_rt_edges_fold_imp
    and emap_assn = ea.arr_assn and ex_assn = va.arr_assn and label_assn = lb.lb_assn
    and count_assn = ca.arr_assn and out_assn = out_rt.csr_rt_assn and in_assn = in_rt.csr_rt_assn
    and fst_imp = src_imp and snd_imp = tgt_imp and ends_assn = "ends_assn fs ts"
    and list_invar = "restr_list_invar (verts fs ts) (amtf_invar n) (amtf_abstract n)"
    and list_abstract = "amtf_abstract n" and list_empty = amtf_empty
    and list_push_front = amtf_push_front and list_move_to_front = amtf_move_to_front
    and list_first = amtf_first and list_next = amtf_next and list_vertex_fold = vfold
    and list_push_front_imp = amtf_push_front_imp and list_move_to_front_imp = amtf_move_to_front_imp
    and list_first_imp = amtf_first_imp and list_next_imp = amtf_next_imp
    and vertex_fold_imp = bool_array_set_fold_imp and list_assn = "amtf_assn n"
    and list_empty_imp = "amtf_empty_imp n" and vset_assn = "bool_array_set_assn n (verts fs ts)"
  by unfold_locales (fact vfold vset_fold)+

text \<open>Highest label: buckets over all vertices below \<open>n\<close> with \<open>2 * nV\<close> labels,
      restricted to the vertices of the network.\<close>

sublocale hbk: fixed_univ_buckets_imp "verts fs ts" "{..<2 * nV}"
    "restr_buckets_invar (verts fs ts) (abk_invar n (2 * nV)) (abk_abstract n (2 * nV))"
    "abk_abstract n (2 * nV)" abk_empty abk_insert abk_remove abk_pick abk_move
    "abk_assn n (2 * nV)" "abk_empty_imp n (2 * nV)" abk_insert_imp abk_remove_imp abk_pick_imp
    abk_move_imp
  by (rule fixed_univ_buckets_imp.fixed_univ_buckets_imp_restrict[OF abk_fixed_univ_buckets_imp
        out.verts_bound])

sublocale hl: push_relabel_hl_imp where \<E> = "edges fs" and fst = "e_src fs" and snd = "e_tgt fs ts"
    and create_edge = "e_new fs" and \<u> = "\<lambda> e. ereal (cap_of e)"
    and emap_invar = "\<lambda> _. True" and emap_upd = arr_upd and emap_get = arr_lookup
    and ex_invar = "\<lambda> _. True" and ex_upd = arr_upd and ex_get = arr_lookup
    and label_invar = lb.lb_invar and label_upd = lb.lb_upd and label_get = lb.lb_get
    and count_invar = "\<lambda> _. True" and count_upd = arr_upd and count_get = arr_lookup
    and out_invar = out.graph.csr_invar and out_abstract = out.graph.csr_abstract
    and out_current = out.graph.csr_current and out_has = out.graph.csr_has
    and out_iterated = out.graph.csr_iterated and out_remaining = out.graph.csr_remaining
    and out_move = out.graph.csr_move and out_reset = out.graph.csr_reset
    and in_invar = inc.graph.csr_invar and in_abstract = inc.graph.csr_abstract
    and in_current = inc.graph.csr_current and in_has = inc.graph.csr_has
    and in_iterated = inc.graph.csr_iterated and in_remaining = inc.graph.csr_remaining
    and in_move = inc.graph.csr_move and in_reset = inc.graph.csr_reset
    and out_reset_to = out_rt.csr_reset_to and in_reset_to = in_rt.csr_reset_to
    and caps = cap_of and num_verts = nV and gap_fold = lb.lb_gap_fold
    and edge_fold = "\<lambda> g acc. foldl g acc out.inp.E_spec"
    and emap_init = "\<lambda> _. h 0" and ex_init = "\<lambda> _. h 0" and label_init = lb.lb_init
    and count_init = "\<lambda> _. id 0" and out_init = "\<lambda> v. out.inp.B_spec ! v"
    and in_init = "\<lambda> v. inc.inp.B_spec ! v"
    and emap_get_imp = "arr_lookup_imp id" and emap_upd_imp = "arr_upd_imp id"
    and ex_get_imp = "arr_lookup_imp id" and ex_upd_imp = "arr_upd_imp id"
    and label_get_imp = pr_lb_get and label_upd_imp = "pr_lb_upd nV"
    and count_get_imp = "arr_lookup_imp id" and count_upd_imp = "arr_upd_imp id"
    and out_current_imp = csr_rt_current_imp and out_has_imp = csr_rt_has_imp
    and out_move_imp = csr_rt_move_imp and out_reset_imp = csr_rt_reset_imp
    and out_reset_to_imp = "csr_reset_to_imp id"
    and in_current_imp = csr_rt_current_imp and in_has_imp = csr_rt_has_imp
    and in_move_imp = csr_rt_move_imp and in_reset_imp = csr_rt_reset_imp
    and in_reset_to_imp = "csr_reset_to_imp id"
    and gap_fold_imp = pr_lb_gap_fold and edge_fold_imp = csr_rt_edges_fold_imp
    and emap_assn = ea.arr_assn and ex_assn = va.arr_assn and label_assn = lb.lb_assn
    and count_assn = ca.arr_assn and out_assn = out_rt.csr_rt_assn and in_assn = in_rt.csr_rt_assn
    and fst_imp = src_imp and snd_imp = tgt_imp and ends_assn = "ends_assn fs ts"
    and buckets_invar = "restr_buckets_invar (verts fs ts) (abk_invar n (2 * nV))
                           (abk_abstract n (2 * nV))"
    and buckets_abstract = "abk_abstract n (2 * nV)" and buckets_empty = abk_empty
    and buckets_insert = abk_insert and buckets_remove = abk_remove and buckets_pick = abk_pick
    and buckets_move = abk_move and bucket_vertex_fold = vfold
    and buckets_insert_imp = abk_insert_imp and buckets_remove_imp = abk_remove_imp
    and buckets_pick_imp = abk_pick_imp and buckets_move_imp = abk_move_imp
    and vertex_fold_imp = bool_array_set_fold_imp and buckets_assn = "abk_assn n (2 * nV)"
    and buckets_empty_imp = "abk_empty_imp n (2 * nV)" and vset_assn = "bool_array_set_assn n (verts fs ts)"
  by unfold_locales (fact vfold vset_fold)+

subsection \<open>The Setup\<close>

lemma E_spec_length: "length out.inp.E_spec = length fs" "length inc.inp.E_spec = length fs"
  using distinct_card[OF out.E_spec_distinct] distinct_card[OF inc.E_spec_distinct]
        out.E_spec_edges inc.E_spec_edges
  by (simp_all add: edges_def)

lemma out_setup_rule:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts> pr_csr_setup csr_build_edges n Fa Ta (length fs)
   <\<lambda> Oi. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts *
         out_rt.csr_rt_assn (\<lambda> v. out.inp.B_spec ! v) Oi>"
proof-
  have build: "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts> csr_build_edges n (Fa, Ta) 0
     <\<lambda>(Ba, Ea). Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Ba \<mapsto>\<^sub>a out.inp.B_spec *
                  Ea \<mapsto>\<^sub>a out.inp.E_spec>"
    unfolding csr_build_edges_src[symmetric]
    by (rule out.csr_build_rule)
  have pos: "<Ea \<mapsto>\<^sub>a out.inp.E_spec * Pa \<mapsto>\<^sub>a replicate (length fs) 0>
               csr_pos_build_imp id Ea Pa (length fs)
             <\<lambda>_. Ea \<mapsto>\<^sub>a out.inp.E_spec * Pa \<mapsto>\<^sub>a Po>" for Ea Pa
    using csr_pos_build_imp_rule[of out.inp.E_spec id "replicate (length fs) 0" Ea Pa]
          out.E_spec_ids
    by (simp add: E_spec_length Po_def)
  show ?thesis
    unfolding pr_csr_setup_def out_rt.csr_rt_assn_def
    by (sep_auto heap: build pos out.graph.csr_cursor_init_rule)
qed

lemma in_setup_rule:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts> pr_csr_setup csr_build_edges_tgt n Fa Ta (length fs)
   <\<lambda> Ii. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts *
         in_rt.csr_rt_assn (\<lambda> v. inc.inp.B_spec ! v) Ii>"
proof-
  have build: "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts> csr_build_edges_tgt n (Fa, Ta) 0
     <\<lambda>(Ba, Ea). Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Ba \<mapsto>\<^sub>a inc.inp.B_spec *
                  Ea \<mapsto>\<^sub>a inc.inp.E_spec>"
    unfolding csr_build_edges_tgt[symmetric]
    by (rule inc.csr_build_rule)
  have pos: "<Ea \<mapsto>\<^sub>a inc.inp.E_spec * Pa \<mapsto>\<^sub>a replicate (length fs) 0>
               csr_pos_build_imp id Ea Pa (length fs)
             <\<lambda>_. Ea \<mapsto>\<^sub>a inc.inp.E_spec * Pa \<mapsto>\<^sub>a Pin>" for Ea Pa
    using csr_pos_build_imp_rule[of inc.inp.E_spec id "replicate (length fs) 0" Ea Pa]
          inc.E_spec_ids
    by (simp add: E_spec_length Pin_def)
  show ?thesis
    unfolding pr_csr_setup_def in_rt.csr_rt_assn_def
    by (sep_auto heap: build pos inc.graph.csr_cursor_init_rule)
qed

lemma pr_vertex_count_step_rule:
  assumes "u < n" "finite W"
  shows "<bool_array_set_assn n W Vi> pr_vertex_count_step Vi u (card W)
         <\<lambda> r. bool_array_set_assn n (insert u W) Vi * \<up>(r = card (insert u W))>"
proof(cases "u \<in> W")
  case True
  then show ?thesis
    unfolding pr_vertex_count_step_def
    using assms(1)
    by (sep_auto heap: bool_array_set_memb_rule simp: insert_absorb)
next
  case False
  then show ?thesis
    unfolding pr_vertex_count_step_def bool_array_set_insert_imp_def
    using assms
    by (sep_auto heap: bool_array_set_memb_rule bool_array_set_upd_rule)
qed

lemma pr_vertex_set_imp_rule:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * bool_array_set_assn n {} Vi>
     pr_vertex_set_imp Fa Ta Vi (length fs)
   <\<lambda> r. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * bool_array_set_assn n (verts fs ts) Vi *
         \<up>(r = nV)>"
proof-
  define W where "W = (\<lambda> j. set (take j fs) \<union> set (take j ts))"
  let ?A = "\<lambda> j (_::unit) r. bool_array_set_assn n (W j) Vi * \<up>(r = card (W j))"
  have "<?A 0 () 0 * (Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts)> pr_vertex_set_imp Fa Ta Vi (length fs)
        <\<lambda> r. ?A (length fs) (foldl (\<lambda> a j. a) () [0..<length fs]) r *
              (Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts)>"
    unfolding pr_vertex_set_imp_def
  proof(rule foldl_range_imp_idx_rule[where A = ?A and g = "\<lambda> _ a. a"
          and F = "Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts"], goal_cases)
    case (1 j a r)
    have j: "j < length fs" "j < length ts" "fs ! j < n" "ts ! j < n"
      using 1 ts_length fs_bound ts_bound nth_mem
      by auto
    have W: "W (Suc j) = insert (ts ! j) (insert (fs ! j) (W j))"
      using j(1,2)
      by (auto simp: W_def take_Suc_conv_app_nth)
    have fin: "finite (W j)"
      by (simp add: W_def)
    show ?case
      using j fin
      by (sep_auto heap: pr_vertex_count_step_rule simp: W)
  qed simp
  moreover have "W 0 = {}" "W (length fs) = verts fs ts"
    using ts_length
    by (simp_all add: W_def out.verts_eq)
  ultimately show ?thesis
    by (simp add: ac_simps)
qed

lemma caps_assn: "Ca \<mapsto>\<^sub>a cs \<Longrightarrow>\<^sub>A ea.arr_assn cap_of Ca"
  unfolding ea.arr_assn_def using cs_length
  by (sep_auto simp: cap_of_def)

lemma la_new_rule: "<emp> Array.new n 0 <la.arr_assn (\<lambda> _. 0)>"
  using la.arr_new_rule[of 0]
  by simp

lemma pr_lb_init_rule:
  "<bool_array_set_assn n (verts fs ts) Vi *
    (la.arr_assn (\<lambda> _. 0) La * abk_assn n nV abk_empty Lb * Dr \<mapsto>\<^sub>r d0)>
     pr_lb_init (bool_array_set_fold_imp Vi) (La, Lb, Dr)
   <\<lambda>_. bool_array_set_assn n (verts fs ts) Vi * lb.lb_assn lb.lb_init (La, Lb, Dr)>"
  unfolding pr_lb_init_def
  by (intro lb.lb_init_imp_rule vset_fold)

text \<open>The initial state of all three strategies.\<close>

definition "setup_assn Si =
   ea.arr_assn (\<lambda> _. h 0) (pi_fwd Si) * ea.arr_assn (\<lambda> _. h 0) (pi_bwd Si) *
   ea.arr_assn cap_of (pi_caps Si) * va.arr_assn (\<lambda> _. h 0) (pi_ex Si) *
   lb.lb_assn lb.lb_init (pi_lab Si) * ca.arr_assn (\<lambda> _. id 0) (pi_cnt Si) *
   out_rt.csr_rt_assn (\<lambda> v. out.inp.B_spec ! v) (pi_out Si) *
   in_rt.csr_rt_assn (\<lambda> v. inc.inp.B_spec ! v) (pi_in Si) * ends_assn fs ts (pi_ends Si) *
   pr.min_scratch_assn Si"

lemma push_relabel_setup_rule:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Ca \<mapsto>\<^sub>a cs> push_relabel_setup n Fa Ta Ca
   <\<lambda>(Si, Vi, nv). setup_assn Si * bool_array_set_assn n (verts fs ts) Vi *
     \<up>(nv = nV \<and> pi_caps Si = Ca \<and> pi_ends Si = (Fa, Ta))>"
proof-
  have ht: "<ea.arr_assn cap_of Ca * (Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts)> push_relabel_setup n Fa Ta Ca
   <\<lambda>(Si, Vi, nv). setup_assn Si * bool_array_set_assn n (verts fs ts) Vi *
     \<up>(nv = nV \<and> pi_caps Si = Ca \<and> pi_ends Si = (Fa, Ta))>"
    unfolding push_relabel_setup_def setup_assn_def pr.min_scratch_assn_def pr.min_assn_def
      ends_assn_def
    by (sep_auto heap: out_setup_rule in_setup_rule bool_array_set_assn_new pr_vertex_set_imp_rule
          ea.arr_new_rule va.arr_new_rule la_new_rule abk_empty_rule pr_lb_init_rule
          ca.arr_new_rule)
  have ent: "Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Ca \<mapsto>\<^sub>a cs \<Longrightarrow>\<^sub>A
             ea.arr_assn cap_of Ca * (Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts)"
    using ent_star_mono[OF caps_assn ent_refl[of "Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts"]]
    by (simp add: ac_simps)
  show ?thesis
    by (rule ht_cons_prec[OF ent ent_refl ht])
qed

subsection \<open>Correctness of the Programs\<close>

text \<open>Each program leaves the input arrays and returns an array holding, by edge number, a
      maximum flow of the network.\<close>

text \<open>The part shared by the three proofs: running a strategy after the setup, and the result.\<close>

lemma setup_bind_rule:
  assumes "\<And> Si Vi. \<lbrakk>pi_caps Si = Ca; pi_ends Si = (Fa, Ta)\<rbrakk> \<Longrightarrow>
             <setup_assn Si * bool_array_set_assn n (verts fs ts) Vi> body Si Vi nV <Q>"
  shows "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Ca \<mapsto>\<^sub>a cs>
           push_relabel_setup n Fa Ta Ca \<bind> (\<lambda> (Si, Vi, nv). body Si Vi nv) <Q>"
proof(rule ht_bind[OF push_relabel_setup_rule], goal_cases)
  case (1 x)
  obtain Si Vi nv where x: "x = (Si, Vi, nv)"
    by (cases x)
  show ?case
    unfolding x prod.case
  proof(rule ht_extract_pre_pure(1), elim conjE)
    assume "nv = nV" "pi_caps Si = Ca" "pi_ends Si = (Fa, Ta)"
    then show "<setup_assn Si * bool_array_set_assn n (verts fs ts) Vi> body Si Vi nv <Q>"
      using assms[of Si Vi]
      by simp
  qed
qed

lemma result_ent:
  assumes "is_max_flow s t P"
  shows "Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * ea.arr_assn cap_of Ca * ea.arr_assn P Bw * true
         \<Longrightarrow>\<^sub>A
         Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * ea.arr_assn cap_of Ca *
         (\<exists>\<^sub>A f. ea.arr_assn f Bw * \<up>(is_max_flow s t f)) * true"
proof-
  have "ea.arr_assn P Bw \<Longrightarrow>\<^sub>A (\<exists>\<^sub>A f. ea.arr_assn f Bw * \<up>(is_max_flow s t f))"
    by (rule ent_ex_postI[of _ _ P]) (simp only: assms pure_true mult.right_neutral ent_refl)
  then show ?thesis
    by (rule ent_star_mono[OF ent_star_mono[OF ent_refl] ent_refl])
qed

lemma push_relabel_fifo_run_rule:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Ca \<mapsto>\<^sub>a cs> push_relabel_fifo_run n s t Fa Ta Ca
   <\<lambda> Bw. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * ea.arr_assn cap_of Ca *
         (\<exists>\<^sub>A f. ea.arr_assn f Bw * \<up>(is_max_flow s t f)) * true>"
proof-
  have main: "pr_fifo_main s t nV = fifo.fifo_imp.push_relabel_imp"
    unfolding pr_fifo_main_def pr_fifo_select_def pr_fifo_init_ctx_def ..
  have run: "<setup_assn Si * fifo.fifo_ctx_init_assn Ci> pr_fifo_main s t nV Ci Si
             <\<lambda>_. ends_assn fs ts (pi_ends Si) * ea.arr_assn cap_of (pi_caps Si) *
                  ea.arr_assn fifo.fifo.push_relabel (pi_bwd Si) * true>"
    for Si Ci
    using fifo.fifo_imp.push_relabel_imp_rule[of Si Ci]
    unfolding main fifo.fifo_imp.init_assn_def setup_assn_def .
  have ctx: "arq_assn nV (arq_empty 0) Qi * Cf \<mapsto>\<^sub>r False * Cu \<mapsto>\<^sub>r (0::nat) *
             bool_array_set_assn n (verts fs ts) Vi \<Longrightarrow>\<^sub>A fifo.fifo_ctx_init_assn (Qi, Cf, Cu, Vi)"
    for Qi Cf Cu Vi
    unfolding fifo.fifo_ctx_init_assn_def cur_assn_def
    by sep_auto
  have opt: "is_max_flow s t fifo.fifo.push_relabel"
    using fifo.fifo.push_relabel_correct
    by (simp add: arr_lookup_def[abs_def])
  show ?thesis
    unfolding push_relabel_fifo_run_def
  proof(rule setup_bind_rule, goal_cases)
    case (1 Si Vi)
    have main: "<setup_assn Si * (arq_assn nV (arq_empty 0) Qi * Cf \<mapsto>\<^sub>r False * Cu \<mapsto>\<^sub>r 0 *
                   bool_array_set_assn n (verts fs ts) Vi)> pr_fifo_main s t nV (Qi, Cf, Cu, Vi) Si
                <\<lambda>_. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * ea.arr_assn cap_of Ca *
                     ea.arr_assn fifo.fifo.push_relabel (pi_bwd Si) * true>"
      for Qi Cf Cu
      unfolding 1(1)[symmetric]
      by (rule ht_cons_prec[OF ent_star_mono[OF ent_refl ctx] ent_refl
                run[of Si, unfolded 1(2) ends_assn_def prod.case]])
    show ?case
      by (rule ht_cons_prec[OF ent_refl result_ent[OF opt]])
         (sep_auto heap: bounded_queue_imp.queue_empty_rule[OF arq_bounded_queue_imp] main)
  qed
qed

lemma push_relabel_rtf_run_rule:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Ca \<mapsto>\<^sub>a cs> push_relabel_rtf_run n s t Fa Ta Ca
   <\<lambda> Bw. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * ea.arr_assn cap_of Ca *
         (\<exists>\<^sub>A f. ea.arr_assn f Bw * \<up>(is_max_flow s t f)) * true>"
proof-
  have main: "pr_rtf_main s t nV = rtf.rtf_imp.push_relabel_imp"
    unfolding pr_rtf_main_def pr_rtf_select_def pr_rtf_init_ctx_def ..
  have run: "<setup_assn Si * rtf.rtf_ctx_init_assn Ci> pr_rtf_main s t nV Ci Si
             <\<lambda>_. ends_assn fs ts (pi_ends Si) * ea.arr_assn cap_of (pi_caps Si) *
                  ea.arr_assn rtf.rtf.push_relabel (pi_bwd Si) * true>"
    for Si Ci
    using rtf.rtf_imp.push_relabel_imp_rule[of Si Ci]
    unfolding main rtf.rtf_imp.init_assn_def setup_assn_def .
  have ctx: "amtf_assn n amtf_empty Ls * Cf \<mapsto>\<^sub>r False * Cu \<mapsto>\<^sub>r (0::nat) *
             Rr \<mapsto>\<^sub>r False * bool_array_set_assn n (verts fs ts) Vi
             \<Longrightarrow>\<^sub>A rtf.rtf_ctx_init_assn (Ls, Cf, Cu, Rr, Vi)"
    for Ls Cf Cu Rr Vi
    unfolding rtf.rtf_ctx_init_assn_def cur_assn_def
    by sep_auto
  have opt: "is_max_flow s t rtf.rtf.push_relabel"
    using rtf.rtf.push_relabel_correct
    by (simp add: arr_lookup_def[abs_def])
  show ?thesis
    unfolding push_relabel_rtf_run_def
  proof(rule setup_bind_rule, goal_cases)
    case (1 Si Vi)
    have main: "<setup_assn Si * (amtf_assn n amtf_empty Ls * Cf \<mapsto>\<^sub>r False * Cu \<mapsto>\<^sub>r 0 *
                   Rr \<mapsto>\<^sub>r False * bool_array_set_assn n (verts fs ts) Vi)>
                  pr_rtf_main s t nV (Ls, Cf, Cu, Rr, Vi) Si
                <\<lambda>_. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * ea.arr_assn cap_of Ca *
                     ea.arr_assn rtf.rtf.push_relabel (pi_bwd Si) * true>"
      for Ls Cf Cu Rr
      unfolding 1(1)[symmetric]
      by (rule ht_cons_prec[OF ent_star_mono[OF ent_refl ctx] ent_refl
                run[of Si, unfolded 1(2) ends_assn_def prod.case]])
    show ?case
      by (rule ht_cons_prec[OF ent_refl result_ent[OF opt]]) (sep_auto heap: amtf_empty_rule main)
  qed
qed

lemma push_relabel_hl_run_rule:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Ca \<mapsto>\<^sub>a cs> push_relabel_hl_run n s t Fa Ta Ca
   <\<lambda> Bw. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * ea.arr_assn cap_of Ca *
         (\<exists>\<^sub>A f. ea.arr_assn f Bw * \<up>(is_max_flow s t f)) * true>"
proof-
  have main: "pr_hl_main s t nV = hl.hl_imp.push_relabel_imp"
    unfolding pr_hl_main_def pr_hl_select_def pr_hl_init_ctx_def ..
  have run: "<setup_assn Si * hl.hl_ctx_init_assn Ci> pr_hl_main s t nV Ci Si
             <\<lambda>_. ends_assn fs ts (pi_ends Si) * ea.arr_assn cap_of (pi_caps Si) *
                  ea.arr_assn hl.hl.push_relabel (pi_bwd Si) * true>"
    for Si Ci
    using hl.hl_imp.push_relabel_imp_rule[of Si Ci]
    unfolding main hl.hl_imp.init_assn_def setup_assn_def .
  have ctx: "abk_assn n (2 * nV) abk_empty Bi * Br \<mapsto>\<^sub>r (0::nat) * Cf \<mapsto>\<^sub>r False *
             Cu \<mapsto>\<^sub>r (0::nat) * bool_array_set_assn n (verts fs ts) Vi
             \<Longrightarrow>\<^sub>A hl.hl_ctx_init_assn (Bi, Br, Cf, Cu, Vi)"
    for Bi Br Cf Cu Vi
    unfolding hl.hl_ctx_init_assn_def cur_assn_def
    by sep_auto
  have opt: "is_max_flow s t hl.hl.push_relabel"
    using hl.hl.push_relabel_correct
    by (simp add: arr_lookup_def[abs_def])
  show ?thesis
    unfolding push_relabel_hl_run_def
  proof(rule setup_bind_rule, goal_cases)
    case (1 Si Vi)
    have main: "<setup_assn Si * (abk_assn n (2 * nV) abk_empty Bi * Br \<mapsto>\<^sub>r 0 *
                   Cf \<mapsto>\<^sub>r False * Cu \<mapsto>\<^sub>r 0 * bool_array_set_assn n (verts fs ts) Vi)>
                  pr_hl_main s t nV (Bi, Br, Cf, Cu, Vi) Si
                <\<lambda>_. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * ea.arr_assn cap_of Ca *
                     ea.arr_assn hl.hl.push_relabel (pi_bwd Si) * true>"
      for Bi Br Cf Cu
      unfolding 1(1)[symmetric]
      by (rule ht_cons_prec[OF ent_star_mono[OF ent_refl ctx] ent_refl
                run[of Si, unfolded 1(2) ends_assn_def prod.case]])
    show ?case
      by (rule ht_cons_prec[OF ent_refl result_ent[OF opt]]) (sep_auto heap: abk_empty_rule main)
  qed
qed

end

end
