theory Hungarian_Method_CSR_Instantiation
  imports
    Directed_Set_Graphs.CSR_Edge_Input
    Data_Structures.Indexed_Heap
    Data_Structures.Set_Addons
    Data_Structures.Imp_Array_Fun
    Data_Structures.Imp_Bool_Set_Iterate
    Basic_Matching.Alternating_Forest_Imperative
    Basic_Matching.Matching_Augmentation_Imperative
    Primal_Dual_Path_Search_Imperative
    Init_Potential_Imperative
    Hungarian_Method_Top_Loop_Imperative
    Data_Structures.Indexed_Heap_Imperative
    Path_Search_Shortcut_Imperative
begin

provenance ai



section \<open>An Imperative Instantiation of the Hungarian Method\<close>

text \<open>The imperative modules of the Hungarian method are instantiated with data structures of
      fixed size, allocated once at the beginning:

        \<^item> the maps (best even neighbours, missed values, potential, parents, buddies) are arrays
          of size \<open>n\<close> that hold the values themselves (@{const array_fun_assn}); a vertex without best
          even neighbour, parent or buddy is mapped to the sentinel \<open>n\<close>,
        \<^item> the sets (left vertices, even and odd vertices) are Boolean arrays of size \<open>n\<close>
          (@{const bool_array_set_assn}), iterated in increasing order,
        \<^item> all of them are cleared in place,
        \<^item> the queue is the indexed binary heap of size \<open>n\<close>, and
        \<^item> the neighbourhoods are given in compressed sparse row (CSR) form: the CSR holds the
          targets of the edges, together with the weights in CSR order.

      The functional ADT types become the functional models that these data structures represent:
      total functions on the universe \<open>{..<n}\<close> and subsets of it, iterated in the order
      @{const sorted_list_of_set}. The functional models are not executed.\<close>

section \<open>The Code\<close>

text \<open>The global interpretations of the implementation modules (the forest and the augmentation),
      whose assumptions do not depend on the graph, and of the code locales of the algorithms.\<close>

subsection \<open>The Forest\<close>

global_interpretation forest_csr: forest_imp
  where K = "{..<n}" and parent_invar = "\<lambda>_. True" and parent_upd = array_fun_upd
    and parent_get = array_fun_lookup and origin_invar = "\<lambda>_. True" and origin_upd = array_fun_upd
    and origin_get = array_fun_lookup and vset_invar = "\<lambda>X. X \<subseteq> {..<n}" and vset_to_set = id
    and vset_empty = "{}" and vset_insert = insert and vset_delete = "\<lambda>x X. X - {x}"
    and vset_isin = "\<lambda>X x. x \<in> X" and vset_iterate = fset_iterate
    and parent_empty = "\<lambda>_. n" and origin_empty = "\<lambda>_. n" and nil = n
    and vset_assn = "bool_array_set_assn n" and vset_empty_imp = "Array.new n False"
    and vset_insert_imp = bool_array_set_insert_imp and vset_delete_imp = bool_array_set_delete_imp
    and vset_isin_imp = bool_array_set_isin_imp and lst = sorted_list_of_set and is_it = "bool_array_set_is_it n"
    and it_init = bool_array_set_it_init and it_has_next = bool_array_set_it_has_next and it_next = bool_array_set_it_next
    and parent_assn = "array_fun_assn n" and parent_upd_imp = array_fun_upd_imp
    and parent_get_imp = array_fun_lookup_imp
    and vset_clear_imp = "bool_array_set_clear_unit n" and parent_clear_imp = "array_fun_clear_unit n n"
    and parent_empty_imp = "Array.new n n"
  for n
  defines forest_csr_empty = forest_csr.forest_empty_imp
    and forest_csr_clear = forest_csr.forest_clear_imp
    and forest_csr_add_root = forest_csr.forest_add_root_imp
    and forest_csr_extend = forest_csr.forest_extend_imp
    and forest_csr_it_init = forest_csr.forest_it_init
    and forest_csr_get_path_loop = forest_csr.get_path_imp_loop
    and forest_csr_get_path = forest_csr.get_path_imp
  apply (rule forest_imp.intro)
     apply (rule forest_manipulation.intro)
      apply (rule forest_manipulation_spec.intro[OF array_fun_fixed_univ_map array_fun_fixed_univ_map
                                                   set_fixed_univ_set])
     apply (rule forest_manipulation_axioms.intro)
          apply simp
         apply simp
        apply (simp add: array_fun_lookup_def)
       apply simp
      apply (simp add: array_fun_lookup_def)
     apply (rule fset_iterate_below, assumption)
  by (rule bool_array_set_fixed_univ_set_imp bool_array_set_fixed_univ_set_iterate_imp
        array_fun_fixed_univ_map_imp bool_array_set_fixed_univ_set_clear_imp
        array_fun_fixed_univ_map_clear_imp array_fun_fixed_univ_map_init_imp)+

subsection \<open>The Augmentation\<close>

global_interpretation aug_csr: matching_augmentation_imp
  where K = "{..<n}" and buddy_invar = "\<lambda>_. True" and buddy_upd = array_fun_upd
    and buddy_get = array_fun_lookup and buddy_empty = "\<lambda>_. n" and nil = n
    and buddy_assn = "array_fun_assn n" and buddy_upd_imp = array_fun_upd_imp
    and buddy_get_imp = array_fun_lookup_imp
  for n
  defines augment_csr_loop = aug_csr.augment_loop
    and augment_csr = aug_csr.augment_imp
    and augment_counted_csr = aug_csr.augment_counted_imp
    and matching_card_csr = aug_csr.matching_card_imp
    and rematch_csr = aug_csr.rematch_imp
    and rematch_counted_csr = aug_csr.rematch_counted_imp
  by (intro matching_augmentation_imp.intro Matching_Augmentation_Specs.intro array_fun_fixed_univ_map
            array_fun_fixed_univ_map_imp)

subsection \<open>The Path Search\<close>

global_interpretation pds_csr: primal_dual_path_search_imp_code
  where nil = n and ben_get_imp = array_fun_lookup_imp and ben_upd_imp = array_fun_upd_imp
    and ben_clear_imp = "array_fun_clear_unit n n"
    and missed_get_imp = array_fun_lookup_imp and missed_upd_imp = array_fun_upd_imp
    and missed_clear_imp = "array_fun_clear_unit 0 n"
    and pot_get_imp = array_fun_lookup_imp and pot_upd_imp = array_fun_upd_imp
    and buddy_imp = array_fun_lookup_imp
    and left_it_init = bool_array_set_it_init and left_it_has_next = bool_array_set_it_has_next
    and left_it_next = bool_array_set_it_next
    and forest_clear_imp = "forest_csr_clear n" and forest_add_root_imp = forest_csr_add_root
    and forest_extend_imp = forest_csr_extend and forest_it_init = forest_csr_it_init
    and forest_it_has_next = bool_array_set_it_has_next and forest_it_next = bool_array_set_it_next
    and get_path_imp = "forest_csr_get_path n"
    and queue_clear_imp = heap_clear_imp and queue_extract_min_imp = heap_extract_min_key_imp
    and queue_key_of_imp = heap_key_of_imp and queue_decrease_key_imp = heap_decrease_key_imp
    and queue_insert_imp = heap_insert_imp
    and has_imp = wnb_has_imp and current_imp = "wnb_current_imp id"
    and current_cost_imp = wnb_current_cost_imp and move_imp = wnb_move_imp
    and reset_imp = wnb_reset_imp and reset_all_imp = "wnb_reset_all_imp n"
  for n
  defines pds_csr_relax_new = pds_csr.relax_new_imp
    and pds_csr_relax_old = pds_csr.relax_old_imp
    and pds_csr_relax = pds_csr.relax_imp
    and pds_csr_scan = pds_csr.scan_imp
    and pds_csr_update_ben = pds_csr.update_ben_imp
    and pds_csr_clear = pds_csr.clear_imp
    and pds_csr_init_step = pds_csr.init_step
    and pds_csr_init = pds_csr.init_imp
    and pds_csr_pot_step_even = pds_csr.pot_step_even
    and pds_csr_pot_step_odd = pds_csr.pot_step_odd
    and pds_csr_new_pot = pds_csr.new_pot_imp
    and pds_csr_loop = pds_csr.loop_imp
    and pds_csr_search = pds_csr.search_imp
  done

text \<open>The data structures of the path search form a single handle: the collection of
      neighbourhoods, the queue, the left vertices, the forest, the best even neighbours and the
      missed values. The potential is updated in place.\<close>

definition path_search_csr where
  "path_search_csr n = (\<lambda>(Ci, Qi, Li, Fi, Bi, Mi) Bdi Pti Ra. do {
     (res, Fi') \<leftarrow> pds_csr_search n Ci Qi Pti Bdi Li Ra Fi Bi Mi;
     return (res, Pti, (Ci, Qi, Li, Fi', Bi, Mi)) })"

subsection \<open>The Shortcut\<close>

text \<open>The shortcut works on the matching with its cardinality: it reads the buddy array and
      rematches without changing the cardinality.\<close>

global_interpretation sc_csr: path_search_shortcut_imp_code
  where nil = n and cap = cap and pot_get_imp = array_fun_lookup_imp and pot_upd_imp = array_fun_upd_imp
    and buddy_imp = "\<lambda>Mt. array_fun_lookup_imp (fst Mt)" and rematch_imp = "rematch_counted_csr n"
    and left_it_has_next = bool_array_set_it_has_next and left_it_next = bool_array_set_it_next
    and has_imp = wnb_has_imp and current_imp = "wnb_current_imp id"
    and current_cost_imp = wnb_current_cost_imp and move_imp = wnb_move_imp
    and reset_imp = wnb_reset_imp
  for n cap
  defines sc_csr_scan_best = sc_csr.bs.scan_best_imp
    and sc_csr_best_two = sc_csr.bs.best_two_imp
    and sc_csr_cur_red = sc_csr.cur_red_imp
    and sc_csr_pot_shift = sc_csr.pot_shift_imp
    and sc_csr_chain = sc_csr.chain_imp
    and sc_csr_row = sc_csr.sc_row_imp
    and sc_csr_loop = sc_csr.sc_loop_imp
    and sc_csr_shortcut = sc_csr.shortcut_imp
  done

text \<open>The full path search as the fallback of the shortcut. The cursors are reset by the path
      search before it starts and here after it ends; the iteration over the left vertices
      starts over.\<close>

definition fallback_csr where
  "fallback_csr n Di Mt Pti Ra = do {
     (res, Pti', Di') \<leftarrow> path_search_csr n Di (fst Mt) Pti Ra;
     (case Di' of (Ci, Qi, Li, Fi, Bi, Mi) \<Rightarrow> do {
        wnb_reset_all_imp n Ci;
        it \<leftarrow> bool_array_set_it_init Li;
        return (res, Mt, Pti', (Di', it)) }) }"

text \<open>The path search of the instantiation: while the matching has fewer than @{term theta}
      edges, the shortcut is tried first, with at most @{term cap} rematches per chain. Otherwise,
      or if it fails, the full path search is run. The matching carries its cardinality, hence
      the test takes constant time. The scratch state consists of the data structures of the
      full path search and the iterator over the left vertices still to be tried.\<close>

definition path_search_sc_csr where
  "path_search_sc_csr n theta cap = (\<lambda>Si Mt Pti Ra.
   case Si of (Di, it) \<Rightarrow> do {
     k \<leftarrow> matching_card_csr Mt;
     (if k < theta then do {
        (b, it') \<leftarrow> sc_csr_shortcut n cap (fst Di) Pti Mt Ra it;
        (if b then return (Imp_Path 2, Mt, Pti, (Di, it')) else fallback_csr n Di Mt Pti Ra) }
      else fallback_csr n Di Mt Pti Ra) })"

subsection \<open>The Initial Potential\<close>

global_interpretation ip_csr: init_potential_imp_code
  where has_imp = wnb_has_imp and current_cost_imp = wnb_current_cost_imp
    and move_imp = wnb_move_imp and reset_imp = wnb_reset_imp
    and pot_get_imp = array_fun_lookup_imp and pot_upd_imp = array_fun_upd_imp
    and left_it_init = bool_array_set_it_init and left_it_has_next = bool_array_set_it_has_next
    and left_it_next = bool_array_set_it_next
  defines init_pot_csr_upd_min = ip_csr.upd_min_imp
    and init_pot_csr_scan = ip_csr.scan_min_imp
    and init_pot_csr_step = ip_csr.init_pot_step
    and init_pot_csr = ip_csr.init_pot_imp
  done

subsection \<open>The Top Loop\<close>

global_interpretation hl_csr: hungarian_top_loop_imp_code "path_search_sc_csr n theta cap"
  augment_counted_csr
  for n theta cap
  defines hungarian_csr_main_loop = hl_csr.main_loop_imp
    and hungarian_csr = hl_csr.hungarian_imp
  done

subsection \<open>Initialisation\<close>

text \<open>The CSR is built over the edge indices. The search reads only the target and the weight of
      an edge, so one pass permutes the weights into CSR order and replaces every edge index by its
      target, in place. The weights and the targets of a neighbourhood are then read
      sequentially during the search.\<close>

partial_function (heap) perm_weights_targets_imp ::
  "nat array \<Rightarrow> nat array \<Rightarrow> 'n::heap array \<Rightarrow> 'n array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "perm_weights_targets_imp Ea Ta Wa Wc i m =
     (if i < m then do {
        e \<leftarrow> Array.nth Ea i;
        w \<leftarrow> Array.nth Wa e;
        v \<leftarrow> Array.nth Ta e;
        _ \<leftarrow> Array.upd i w Wc;
        _ \<leftarrow> Array.upd i v Ea;
        perm_weights_targets_imp Ea Ta Wa Wc (Suc i) m }
      else return ())"

text \<open>Inserting the elements of an array into a Boolean array, in place.\<close>

partial_function (heap) bool_array_set_insert_all :: "nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool array \<Rightarrow> unit Heap" where
  "bool_array_set_insert_all La i m s =
     (if i < m then do {
        v \<leftarrow> Array.nth La i;
        bool_array_set_insert_imp v s;
        bool_array_set_insert_all La (Suc i) m s }
      else return ())"

text \<open>The final program takes the number of vertices \<open>n\<close>, the threshold \<open>theta\<close> for the
      shortcut, the bound \<open>cap\<close> on the rematches of a chain, the arrays \<open>Fa\<close>, \<open>Ta\<close> of the left
      and the right endpoints of the edges, the weight array \<open>Wa\<close>, and the arrays \<open>La\<close>, \<open>Ra\<close> of
      the left and the right vertices. It builds the CSR representation, allocates all other data
      structures, computes the initial potential and runs the Hungarian method. It returns the
      result flag, the matching (as the array of buddies, with \<open>n\<close> for a free vertex) and the
      final potential. This is the only place with allocations. With \<open>theta = 0\<close>, the shortcut is
      never tried.\<close>

definition hungarian_csr_run ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> 'n::{linordered_idom, heap} array \<Rightarrow> nat array \<Rightarrow>
   nat array \<Rightarrow> (result \<times> nat array \<times> 'n array) Heap" where
  "hungarian_csr_run n theta cap Fa Ta Wa La Rv = do {
     (Ba, Ea) \<leftarrow> csr_build_edges n (Fa, Ta) 0;
     m \<leftarrow> Array.len Ea;
     Wc \<leftarrow> Array.new m 0;
     perm_weights_targets_imp Ea Ta Wa Wc 0 m;
     Ca \<leftarrow> csr_cursor_init n Ba;
     cL \<leftarrow> Array.len La;
     cR \<leftarrow> Array.len Rv;
     Li \<leftarrow> Array.new n False;
     bool_array_set_insert_all La 0 cL Li;
     Pti \<leftarrow> Array.new n 0;
     init_pot_csr ((Ba, Ea, Ca), Wc) Li Pti;
     wnb_reset_all_imp n ((Ba, Ea, Ca), Wc);
     it \<leftarrow> bool_array_set_it_init Li;
     Qi \<leftarrow> heap_empty_imp n 0;
     Fi \<leftarrow> forest_csr_empty n;
     Bi \<leftarrow> Array.new n n;
     Mi \<leftarrow> Array.new n 0;
     Mm \<leftarrow> Array.new n n;
     Ki \<leftarrow> ref 0;
     Ra \<leftarrow> Array.new n 0;
     (r, (Mm', _), Pti', _) \<leftarrow>
       hungarian_csr n theta cap cL cR ((((Ba, Ea, Ca), Wc), Qi, Li, Fi, Bi, Mi), it) (Mm, Ki) Pti
         Ra;
     return (r, Mm', Pti') }"

definition hungarian_csr_run_int ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> int array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow>
   (result \<times> nat array \<times> int array) Heap" where
  "hungarian_csr_run_int = hungarian_csr_run"

declare perm_weights_targets_imp.simps[code] bool_array_set_insert_all.simps[code] iter_fold.simps[code]
  forest_csr.get_path_imp_loop.simps[code] aug_csr.augment_loop.simps[code]
  pds_csr.scan_imp.simps[code] pds_csr.loop_imp.simps[code] ip_csr.scan_min_imp.simps[code]
  hl_csr.main_loop_imp.simps[code]
  bool_array_set_scan.simps[code] sc_csr.bs.scan_best_imp.simps[code] iter_find.simps[code]
  nb_best_scan_imp_code.best_upd_imp_def[code] nb_best_scan_imp_code.best2_upd_imp_def[code]
  nb_best_scan_imp_code.better_imp_def[code] sc_csr.chain_imp.simps[code]
  sc_csr.sc_loop_imp.simps[code] sift_down_imp.simps[code] sift_up_imp.simps[code]

export_code hungarian_csr_run_int checking SML_imp
text \<open>In the generated code, the computation of the initial potential and the main loop contain no
      allocation. All allocations are in @{const hungarian_csr_run} before the computation
      begins.\<close>



section \<open>Correctness\<close>

subsection \<open>The Input\<close>

text \<open>The input consists of the lists @{term fs}, @{term ts} of the left and the right endpoints of
      the edges, the weights @{term ws}, and the lists @{term ls}, @{term rs} of the left and the
      right vertices. Every vertex has an edge, the sides are disjoint, all vertices are below
      @{term n}, and there are no parallel edges. The threshold @{term theta} for the shortcut and
      the bound @{term cap} on the rematches of a chain are arbitrary.\<close>

locale hungarian_csr_input = real_embedding h
  for h :: "'n::{linordered_idom, heap} \<Rightarrow> real" +
  fixes n :: nat
    and fs :: "nat list"
    and ts :: "nat list"
    and ws :: "'n list"
    and ls :: "nat list"
    and rs :: "nat list"
    and theta :: nat
    and cap :: nat
  assumes ts_length: "length ts = length fs"
    and ws_length: "length ws = length fs"
    and ls_distinct: "distinct ls"
    and rs_distinct: "distinct rs"
    and fs_ls: "set fs = set ls"
    and ts_rs: "set ts = set rs"
    and sides_disjoint: "set ls \<inter> set rs = {}"
    and verts_below: "set ls \<union> set rs \<subseteq> {..<n}"
    and no_parallel: "distinct (zip fs ts)"
begin

abbreviation "L \<equiv> set ls"
abbreviation "R \<equiv> set rs"

definition "G = {{fs ! i, ts ! i} | i. i < length fs}"

definition "eidx u v = (THE i. i < length fs \<and> fs ! i = u \<and> ts ! i = v)"

definition "ecost u v = (if u \<in> L then h (ws ! eidx u v) else h (ws ! eidx v u))"

lemma fs_L: "i < length fs \<Longrightarrow> fs ! i \<in> L"
  using fs_ls nth_mem
  by blast

lemma ts_R: "i < length fs \<Longrightarrow> ts ! i \<in> R"
  using ts_rs ts_length nth_mem[of i ts]
  by (auto)

lemma L_less: "v \<in> L \<Longrightarrow> v < n" and R_less: "v \<in> R \<Longrightarrow> v < n"
  using verts_below
  by auto

lemma edge_unique:
  "\<lbrakk>i < length fs; j < length fs; fs ! i = fs ! j; ts ! i = ts ! j\<rbrakk> \<Longrightarrow> i = j"
  using ts_length nth_eq_iff_index_eq[OF no_parallel, of i j]
  by (simp)

lemma eidx_eq: "i < length fs \<Longrightarrow> eidx (fs ! i) (ts ! i) = i"
  unfolding eidx_def
  by (rule the_equality) (auto intro: edge_unique)

lemma ecost_edge: "i < length fs \<Longrightarrow> ecost (fs ! i) (ts ! i) = h (ws ! i)"
  by (simp add: ecost_def fs_L eidx_eq)

lemma ecost_edge_sym: "i < length fs \<Longrightarrow> ecost (ts ! i) (fs ! i) = h (ws ! i)"
  using ts_R fs_L sides_disjoint
  by (auto simp: ecost_def eidx_eq)

lemma G_edgeE:
  assumes "{u, v} \<in> G"
  obtains i where "i < length fs" "u = fs ! i" "v = ts ! i"
        | i where "i < length fs" "v = fs ! i" "u = ts ! i"
  using assms unfolding G_def
  by (auto simp: doubleton_eq_iff)

lemma ecost_sym: "{u, v} \<in> G \<Longrightarrow> ecost u v = ecost v u"
  by (erule G_edgeE) (simp_all add: ecost_edge ecost_edge_sym)

lemma bipartite_G: "bipartite G L R"
  unfolding bipartite_def G_def
  using fs_L ts_R sides_disjoint
  by (fastforce simp: doubleton_eq_iff)

lemma G_edge: "i < length fs \<Longrightarrow> {fs ! i, ts ! i} \<in> G"
  by (auto simp: G_def)

lemma Vs_G: "Vs G = L \<union> R"
proof
  show "Vs G \<subseteq> L \<union> R"
    using fs_L ts_R
    by (auto simp: Vs_def G_def)
  show "L \<union> R \<subseteq> Vs G"
    using ts_length
    by (auto simp: fs_ls[symmetric] ts_rs[symmetric] in_set_conv_nth
                         intro: G_edge[THEN edges_are_Vs] G_edge[THEN edges_are_Vs_2])
qed

lemma neighbours_G: "v \<in> L \<Longrightarrow> {u. {v, u} \<in> G} = {ts ! i | i. i < length fs \<and> fs ! i = v}"
  using fs_L ts_R sides_disjoint
  by (auto simp: G_def doubleton_eq_iff)

subsection \<open>The CSR Representation\<close>

sublocale ei: csr_edge_input n fs ts "e_src fs" src_imp
  by unfold_locales
     (use ts_length fs_ls ts_rs verts_below src_imp_rule[of _ fs ts] in auto)

text \<open>The block of a vertex holds the indices of its edges.\<close>

lemma block_edges:
  assumes "v < n"
  shows "(!) ei.inp.E_spec ` {ei.inp.B_spec ! v..<ei.inp.B_spec ! Suc v} =
         {i. i < length fs \<and> fs ! i = v}"
  using ei.block_key[OF assms]
  by (auto simp: edges_def e_src_def)

text \<open>The CSR holds the targets: the initialisation replaces every edge index by its target.\<close>

definition "Et = map ((!) ts) ei.inp.E_spec"

lemma Et_nth: "j < length ei.inp.E_spec \<Longrightarrow> Et ! j = ts ! (ei.inp.E_spec ! j)"
  by (simp add: Et_def)

text \<open>There are no parallel edges, so the targets are distinct within each block.\<close>

lemma Et_block_inj:
  assumes "v < n"
  shows "inj_on ((!) Et) {ei.inp.B_spec ! v..<ei.inp.B_spec ! Suc v}"
proof(rule inj_onI)
  fix j j'
  assume "j \<in> {ei.inp.B_spec ! v..<ei.inp.B_spec ! Suc v}" "j' \<in> {ei.inp.B_spec ! v..<ei.inp.B_spec ! Suc v}"
         "Et ! j = Et ! j'"
  moreover from this(1,2) have "ei.inp.E_spec ! j \<in> {i. i < length fs \<and> fs ! i = v}"
                               "ei.inp.E_spec ! j' \<in> {i. i < length fs \<and> fs ! i = v}"
    using block_edges[OF assms]
    by blast+
  ultimately show "j = j'"
    using ei.B_spec_bound[OF assms] ei.E_spec_distinct edge_unique[of "ei.inp.E_spec ! j" "ei.inp.E_spec ! j'"]
    by (auto simp: Et_nth nth_eq_iff_index_eq)
qed

text \<open>The neighbourhoods are indexed by the whole universe of the maps and sets, the vertices below
      \<open>n\<close>.
      Only the left vertices have neighbours.\<close>

sublocale graph: csr_graph_imp n "{..<n}" ei.inp.B_spec Et
proof(unfold_locales, goal_cases)
  case 1 show ?case by simp
next
  case 2 show ?case by (rule ei.inp.length_B_spec)
next
  case (3 v) then show ?case by (simp add: ei.inp.B_spec_nth ei.inp.start_mono)
next
  case (4 v) then show ?case by (simp add: Et_def ei.B_spec_bound)
next
  case (5 v) show ?case by (rule order.refl)
next
  case (6 v) then show ?case by (rule Et_block_inj)
qed

lemma csr_abstract_targets:
  assumes "v < n"
  shows "graph.csr_abstract c v = {ts ! i | i. i < length fs \<and> fs ! i = v}"
proof-
  have "graph.csr_abstract c v =
        (\<lambda>j. ts ! (ei.inp.E_spec ! j)) ` {ei.inp.B_spec ! v..<ei.inp.B_spec ! Suc v}"
    unfolding graph.csr_abstract_eq
    using ei.B_spec_bound[OF assms]
    by (intro image_cong refl) (simp add: Et_nth)
  also have "\<dots> = (!) ts ` (!) ei.inp.E_spec ` {ei.inp.B_spec ! v..<ei.inp.B_spec ! Suc v}"
    by (simp add: image_image)
  also have "\<dots> = (!) ts ` {i. i < length fs \<and> fs ! i = v}"
    by (simp only: block_edges[OF assms])
  finally show ?thesis
    by blast
qed

text \<open>The weights in CSR order.\<close>

definition "W = map ((!) ws) ei.inp.E_spec"

sublocale wcsr: weighted_csr n "{..<n}" ei.inp.B_spec Et id W ecost h
proof(unfold_locales, goal_cases)
  case (1 v) show ?case by simp
next
  case 2 show ?case by (simp add: W_def Et_def)
next
  case (3 v j)
  have v: "v < n" using 3(1) by simp
  have "ei.inp.E_spec ! j \<in> (!) ei.inp.E_spec ` {ei.inp.B_spec ! v..<ei.inp.B_spec ! Suc v}"
    using 3(2,3) by (intro imageI) simp
  then have "ei.inp.E_spec ! j \<in> {i. i < length fs \<and> fs ! i = v}"
    by (simp only: block_edges[OF v])
  then have i: "ei.inp.E_spec ! j < length fs" "fs ! (ei.inp.E_spec ! j) = v"
    by simp_all
  have "j < length ei.inp.E_spec" using 3(3) ei.B_spec_bound[OF v] by simp
  thus ?case using i ecost_edge[OF i(1)] by (simp add: W_def Et_nth)
qed

subsection \<open>The Queue\<close>

sublocale hp: indexed_heap_imp n "Vs G" h 0
  by unfold_locales (auto simp: Vs_G L_less R_less)

end

subsection \<open>The Neighbourhoods and the Initial Potential\<close>

context hungarian_csr_input
begin

abbreviation "nb_init \<equiv> (\<lambda>v. ei.inp.B_spec ! v)"

lemma L_below: "L \<subseteq> {..<n}"
  using L_less
  by auto

lemma L_lessThan: "i \<in> L \<Longrightarrow> i \<in> {..<n}"
  using L_less
  by simp

lemma wnb_abstract_init:
  "v \<in> L \<Longrightarrow> wcsr.wnb_abstract nb_init v = {u. {v, u} \<in> G}"
  using csr_abstract_targets[OF L_less]
  by (simp add: wcsr.wnb_abstract_eq graph.csr_abstract_eq neighbours_G)

lemma wnb_abstract_finite: "finite (wcsr.wnb_abstract C v)"
  by (simp add: wcsr.wnb_abstract_eq)

text \<open>The neighbourhoods do not depend on the cursors.\<close>

lemma wnb_abstract_cursor: "\<forall>i\<in>A. wcsr.wnb_abstract C i = wcsr.wnb_abstract C' i"
  by (simp add: wcsr.wnb_abstract_eq)

text \<open>The path search scans the neighbourhoods of the left vertices only.\<close>

lemma wnb_imp_L:
  "weighted_neighbourhoods_imp_spec graph.csr_invar wcsr.wnb_abstract wcsr.wnb_current
     graph.csr_has wcsr.wnb_iterated wcsr.wnb_remaining graph.csr_move graph.csr_reset L
     wcsr.wnb_assn (wnb_current_imp id) wnb_has_imp wnb_move_imp wnb_reset_imp ecost h nb_init
     wnb_current_cost_imp (wnb_reset_all_imp n)"
  apply (intro weighted_neighbourhoods_imp_spec.intro indexed_iterable_set_imp.intro
               indexed_set_cursor_imp.intro indexed_set_reset_imp.intro
               weighted_neighbourhoods_imp_spec_axioms.intro indexed_set_cursor_imp_axioms.intro
               indexed_set_reset_imp_axioms.intro
               wcsr.wnb.indexed_iterable_set_restrict
               indexed_iterable_set.axioms[OF wcsr.wnb.indexed_iterable_set_restrict] subsetI)
  apply (all \<open>(erule L_lessThan | rule wcsr.wnb_imp.nb_init_invar wcsr.wnb_imp.idx_has_rule
                    wcsr.wnb_imp.idx_current_rule wcsr.wnb_imp.current_cost_rule
                    wcsr.wnb_imp.idx_move_rule wcsr.wnb_imp.idx_reset_rule wcsr.wnb_imp.reset_all_rule;
               (assumption | erule L_lessThan | rule wnb_abstract_cursor)?)?\<close>)
  done

text \<open>The initial potential. The potential is an array of values that are read into the reals.\<close>

sublocale ipot: init_potential_imp
  where potential_upd = array_fun_upd and potential_get = array_fun_lookup
    and rnb_current = wcsr.wnb_current and rnb_has = graph.csr_has and rnb_move = graph.csr_move
    and rnb_reset = graph.csr_reset and cost = ecost and vset_iterate = fset_iterate
    and potential_invar = "\<lambda>_. True"
    and rnb_invar = graph.csr_invar and rnb_abstract = wcsr.wnb_abstract
    and rnb_iterated = wcsr.wnb_iterated and rnb_remaining = wcsr.wnb_remaining and K = "{..<n}"
    and potential_empty = "\<lambda>_. 0" and vset_to_set = id and vset_invar = "\<lambda>X. X \<subseteq> {..<n}"
    and lst = sorted_list_of_set
    and h = h and nb_init = nb_init and nb_assn = wcsr.wnb_assn and has_imp = wnb_has_imp
    and current_imp = "wnb_current_imp id" and current_cost_imp = wnb_current_cost_imp
    and move_imp = wnb_move_imp and reset_imp = wnb_reset_imp
    and reset_all_imp = "wnb_reset_all_imp n"
    and pot_assn = "array_fun_val_assn h n" and pot_upd_imp = array_fun_upd_imp
    and pot_get_imp = array_fun_lookup_imp
    and vset_assn = "bool_array_set_assn n"
    and left_is_it = "bool_array_set_is_it n" and left_it_init = bool_array_set_it_init
    and left_it_has_next = bool_array_set_it_has_next and left_it_next = bool_array_set_it_next
  apply (intro init_potential_imp.intro init_potential_coll.intro init_potential_coll_axioms.intro
               array_fun_fixed_univ_map wcsr.wnb.indexed_iterable_set_axioms real_embedding_axioms
               wcsr.wnb_imp.weighted_neighbourhoods_imp_spec_axioms
               wcsr.wnb_imp.indexed_iterable_set_imp_axioms array_fun_val_fixed_univ_map_imp
               bool_array_set_fixed_univ_set_iterate_imp)
  by (simp_all add: fset_iterate_def array_fun_lookup_def)

abbreviation "init_pot \<equiv> snd (ipot.init_potential_coll nb_init (\<lambda>_. 0) L)"

lemma init_pot_props:
  "\<And>u v. \<lbrakk>u \<in> L; v \<in> wcsr.wnb_abstract nb_init u\<rbrakk> \<Longrightarrow> array_fun_lookup init_pot u \<le> ecost u v"
  "\<And>u. u \<notin> L \<Longrightarrow> array_fun_lookup init_pot u = 0"
  "graph.csr_invar (fst (ipot.init_potential_coll nb_init (\<lambda>_. 0) L))"
  "wcsr.wnb_abstract (fst (ipot.init_potential_coll nb_init (\<lambda>_. 0) L)) = wcsr.wnb_abstract nb_init"
  using ipot.init_potential_coll_props[of nb_init L, OF graph.csr_init_invar L_below _ _
                                         wnb_abstract_finite]
  by (simp_all add: L_below)

subsection \<open>The Functional Models of the Matching and the Potential\<close>

text \<open>The matching is the total map of buddies on @{term "{..<n}"}, with @{term n} for a free
      vertex. The potential is a total function on the vertices.\<close>

abbreviation "wfun \<equiv> \<lambda>e. ecost (pick_one e) (pick_another e)"

lemma wfun_eq:
  assumes "{u, v} \<in> G"
  shows "wfun {u, v} = ecost u v"
proof-
  have "u \<noteq> v"
    by (rule bipartite_edgeE[OF assms bipartite_G]) (auto simp: doubleton_eq_iff)
  thus ?thesis
    using pick_one_and_another_props(3)[of "{u, v}", OF exI[of _ u]]
    by (auto simp: doubleton_eq_iff ecost_sym[OF assms])
qed

sublocale maug: matching_augmentation "{..<n}" "\<lambda>_. True" array_fun_upd array_fun_lookup "\<lambda>_. n" n
  by (intro matching_augmentation.intro matching_augmentation_axioms.intro
            Matching_Augmentation_Specs.intro array_fun_fixed_univ_map)
     (simp_all add: array_fun_lookup_def)

lemma Vs_G_below: "Vs G \<subseteq> {..<n}"
  using L_less R_less
  by (auto simp: Vs_G)

lemma buddy_lookup_rule:
  "v \<in> {..<n} \<Longrightarrow>
   <array_fun_assn n M Bdi> array_fun_lookup_imp Bdi v <\<lambda>r. array_fun_assn n M Bdi * \<up>(r = array_fun_lookup M v)>"
  by (sep_auto heap: array_fun_lookup_rule simp: array_fun_lookup_imp_def array_fun_lookup_def)

lemma buddy_edge:
  "\<lbrakk>aug_csr.invar_matching n G M; array_fun_lookup M v \<noteq> n\<rbrakk> \<Longrightarrow> {array_fun_lookup M v, v} \<in> aug_csr.\<M> n M"
  by (auto simp: aug_csr.\<M>_def' aug_csr.buddy_lookup_def insert_commute)

lemma buddy_free:
  assumes "aug_csr.invar_matching n G M"
  shows "array_fun_lookup M v = n \<longleftrightarrow> v \<notin> Vs (aug_csr.\<M> n M)"
proof-
  have "aug_csr.buddy_lookup n M v = None \<longleftrightarrow> v \<notin> Vs (aug_csr.\<M> n M)"
  proof(cases "aug_csr.buddy_lookup n M v")
    case None
    thus ?thesis
      by (auto simp: Vs_def aug_csr.\<M>_def'
                   dest: assms[THEN aug_csr.invar_matchingD(2), THEN aug_csr.symmetric_buddiesD, THEN iffD1])
  next
    case (Some w)
    hence "{v, w} \<in> aug_csr.\<M> n M"
      unfolding aug_csr.\<M>_def'
      by blast
    thus ?thesis
      using Some
      by (auto dest: edges_are_Vs)
  qed
  thus ?thesis
    by (simp add: aug_csr.buddy_lookup_def split: if_splits)
qed

abbreviation "csr_precond \<equiv>
  hungarian_loop_spec.path_search_precond array_fun_lookup (\<lambda>_. True) (aug_csr.invar_matching n G)
    (aug_csr.\<M> n) wfun G"

text \<open>The functional path search for the matching @{term M} and the potential @{term \<pi>}.\<close>

definition "fsearch M \<pi> =
  primal_dual_path_search_spec.search_path array_fun_upd array_fun_lookup array_fun_upd array_fun_lookup array_fun_upd
    array_fun_lookup ecost L wcsr.wnb_current graph.csr_has graph.csr_move graph.csr_reset nb_init
    (array_fun_lookup M) forest_csr.extend_forest_even_unclassified evens odds (forest_csr.get_path n)
    (forest_csr.empty_forest n) \<pi> heap_empty heap_extract_min heap_decrease_key heap_insert
    fset_iterate fset_iterate fset_filter fset_is_empty (\<lambda>_. n) (\<lambda>_. 0) n"

lemmas pds_spec = primal_dual_path_search_spec.intro[OF array_fun_fixed_univ_map array_fun_fixed_univ_map
                    array_fun_fixed_univ_map set_fixed_univ_set]

lemma pds_buddy_eq:
  "primal_dual_path_search_spec.buddy (array_fun_lookup M) n = aug_csr.buddy_lookup n M"
  by (rule ext)
     (simp add: primal_dual_path_search_spec.buddy_def[OF pds_spec] aug_csr.buddy_lookup_def)

lemma pds_M_eq: "primal_dual_path_search_spec.\<M> (array_fun_lookup M) n = aug_csr.\<M> n M"
  unfolding primal_dual_path_search_spec.\<M>_def[OF pds_spec] pds_buddy_eq aug_csr.\<M>_def'
  by (simp only: eq_commute[of "Some _"])

text \<open>The queue, the forest, the best even neighbours and the missed values of the path search,
      with arbitrary contents.\<close>

definition "pds_aux_assn Qi Fi Bi Mi =
   (\<exists>\<^sub>AH (F :: (nat set, nat set, nat set, nat \<Rightarrow> nat, nat \<Rightarrow> nat) alt_forest) B Ms.
      hp.heap_assn H Qi * forest_csr.forest_assn n F Fi * array_fun_assn n B Bi *
      array_fun_val_assn h n Ms Mi)"

text \<open>The data structures of the path search; the cursors are anywhere.\<close>

definition "csr_scratch_assn Di = (case Di of (Ci, Qi, Li, Fi, Bi, Mi) \<Rightarrow>
   (\<exists>\<^sub>AC. wcsr.wnb_assn C Ci * \<up>(graph.csr_invar C)) * pds_aux_assn Qi Fi Bi Mi *
   bool_array_set_assn n L Li)"

text \<open>The data structures of the path search with the shortcut, for the context of
      @{const path_search_shortcut_spec.path_search_sc}: the cursors represent the cursors of the
      context, and the iterator over the left vertices represents its left vertices.\<close>

definition "sc_scratch_assn ctx Si = (case ctx of (xs, C) \<Rightarrow> case Si of (Di, it) \<Rightarrow>
   case Di of (Ci, Qi, Li, Fi, Bi, Mi) \<Rightarrow>
     wcsr.wnb_assn C Ci * pds_aux_assn Qi Fi Bi Mi * bool_array_set_assn n L Li *
     bool_array_set_is_it n L Li xs it)"

end


subsection \<open>One Path Search\<close>

text \<open>For a matching @{term M} and a potential @{term \<pi>} that satisfy the precondition of the path
      search, the imperative path search of @{locale primal_dual_path_search_imp} is interpreted on
      the data structures of the instantiation.\<close>

locale hungarian_csr_search = hungarian_csr_input +
  fixes M :: "nat \<Rightarrow> nat" and \<pi> :: "nat \<Rightarrow> real"
  assumes precond: "csr_precond M \<pi>"
begin

lemmas pre = hungarian_loop_spec.path_search_precondD[OF precond]

lemma tight_M:
  assumes "{u, v} \<in> aug_csr.\<M> n M"
  shows "array_fun_lookup \<pi> u + array_fun_lookup \<pi> v = ecost u v"
proof-
  have "{u, v} \<in> tight_subgraph G wfun (array_fun_lookup \<pi>)"
    using pre(4) assms
    by blast
  hence "{u, v} \<in> G" "wfun {u, v} = array_fun_lookup \<pi> u + array_fun_lookup \<pi> v"
    by (auto simp: tight_subgraph_def doubleton_eq_iff add.commute insert_commute)
  thus ?thesis
    using wfun_eq
    by simp
qed
lemma missed_clear:
  "fixed_univ_map_clear_imp {..<n} (\<lambda>_. True) array_fun_lookup h (array_fun_val_assn h n)
     array_fun_lookup_imp (\<lambda>_. 0) (array_fun_clear_unit 0 n)"
  using array_fun_val_fixed_univ_map_clear_imp[of n h 0]
  by simp

sublocale ps: primal_dual_path_search_imp
  where K = "{..<n}" and ben_invar = "\<lambda>_. True" and ben_upd = array_fun_upd and ben_get = array_fun_lookup
    and missed_invar = "\<lambda>_. True" and missed_upd = array_fun_upd and missed_get = array_fun_lookup
    and potential_invar = "\<lambda>_. True" and potential_upd = array_fun_upd and potential_get = array_fun_lookup
    and vset_invar = "\<lambda>X. X \<subseteq> {..<n}" and vset_to_set = id and vset_empty = "{}"
    and vset_insert = insert and vset_delete = "\<lambda>x X. X - {x}" and vset_isin = "\<lambda>X x. x \<in> X"
    and G = G and edge_costs = ecost and edge_costs_code = ecost and left = L and right = R
    and in_G = "\<lambda>u v. {u, v} \<in> G"
    and rnb_invar = graph.csr_invar and rnb_abstract = wcsr.wnb_abstract
    and rnb_current = wcsr.wnb_current and rnb_has = graph.csr_has
    and rnb_iterated = wcsr.wnb_iterated and rnb_remaining = wcsr.wnb_remaining
    and rnb_move = graph.csr_move and rnb_reset = graph.csr_reset and rnb_init = nb_init
    and buddy_get = "array_fun_lookup M"
    and extend_forest_even_unclassified = forest_csr.extend_forest_even_unclassified
    and evens = evens and odds = odds and get_path = "forest_csr.get_path n"
    and abstract_forest = "forest_csr.abstract_forest n"
    and empty_forest = "forest_csr.empty_forest n" and forest_invar = "forest_csr.forest_invar n"
    and roots = roots and initial_pot = \<pi>
    and heap_empty = heap_empty and heap_extract_min = heap_extract_min
    and heap_decrease_key = heap_decrease_key and heap_insert = heap_insert
    and heap_invar = "heap_invar (Vs G)" and heap_abstract = heap_abstract
    and vset_iterate_ben = fset_iterate and vset_iterate_pot = fset_iterate
    and vset_filter = fset_filter and vset_is_empty = fset_is_empty
    and ben_empty = "\<lambda>_. n" and missed_empty = "\<lambda>_. 0" and nil = n
    and h = h
    and queue_assn = hp.heap_assn and queue_empty_imp = "heap_empty_imp n 0"
    and queue_clear_imp = heap_clear_imp and queue_extract_min_imp = heap_extract_min_key_imp
    and queue_key_of_imp = heap_key_of_imp and queue_decrease_key_imp = heap_decrease_key_imp
    and queue_insert_imp = heap_insert_imp
    and nb_assn = wcsr.wnb_assn and has_imp = wnb_has_imp and current_imp = "wnb_current_imp id"
    and current_cost_imp = wnb_current_cost_imp and move_imp = wnb_move_imp
    and reset_imp = wnb_reset_imp and reset_all_imp = "wnb_reset_all_imp n"
    and lst = sorted_list_of_set and forest_assn = "forest_csr.forest_assn n"
    and forest_empty_imp = "forest_csr_empty n" and forest_clear_imp = "forest_csr_clear n"
    and forest_add_root_imp = forest_csr_add_root and forest_extend_imp = forest_csr_extend
    and evens_memb_imp = forest_csr.evens_memb_imp and odds_memb_imp = forest_csr.odds_memb_imp
    and forest_is_it = "forest_csr.forest_is_it n" and forest_it_init = forest_csr_it_init
    and forest_it_has_next = bool_array_set_it_has_next and forest_it_next = bool_array_set_it_next
    and get_path_imp = "forest_csr_get_path n"
    and ben_assn = "array_fun_assn n" and ben_upd_imp = array_fun_upd_imp and ben_get_imp = array_fun_lookup_imp
    and missed_assn = "array_fun_val_assn h n" and missed_upd_imp = array_fun_upd_imp
    and missed_get_imp = array_fun_lookup_imp
    and pot_assn = "array_fun_val_assn h n" and pot_upd_imp = array_fun_upd_imp
    and pot_get_imp = array_fun_lookup_imp
    and vset_assn = "bool_array_set_assn n"
    and left_is_it = "bool_array_set_is_it n" and left_it_init = bool_array_set_it_init
    and left_it_has_next = bool_array_set_it_has_next and left_it_next = bool_array_set_it_next
    and buddy_assn = "array_fun_assn n M" and buddy_imp = array_fun_lookup_imp
    and ben_clear_imp = "array_fun_clear_unit n n" and missed_clear_imp = "array_fun_clear_unit 0 n"
  apply (intro primal_dual_path_search_imp.intro primal_dual_path_search_imp_axioms.intro
               primal_dual_path_search.intro primal_dual_path_search_axioms.intro pds_spec
               alternating_forest_imp_spec.axioms(1)[OF forest_csr.alternating_forest_imp_spec]
               hp.heap_key_value_queue_hungarian
               indexed_iterable_set_imp.axioms(1)[OF weighted_neighbourhoods_imp_spec.axioms(1)[OF wnb_imp_L]]
               real_embedding_axioms hp.hqueue.key_value_queue_imp_axioms wnb_imp_L
               forest_csr.alternating_forest_imp_spec
               array_fun_fixed_univ_map_imp array_fun_val_fixed_univ_map_imp bool_array_set_fixed_univ_set_iterate_imp
               buddy_lookup_rule array_fun_fixed_univ_map_clear_imp missed_clear)
  subgoal
    using indexed_iterable_set_imp.axioms(1)[OF weighted_neighbourhoods_imp_spec.axioms(1)[OF wnb_imp_L]]
    by simp
  subgoal by (simp add: bipartite_G)
  subgoal by (rule L_below)
  subgoal using R_less by auto
  subgoal by (rule graph.csr_init_invar)
  subgoal by (simp add: wnb_abstract_init)
  subgoal by (rule ecost_sym)
  subgoal premises p using feasible_min_perfect_dualD[OF pre(5) p refl] wfun_eq[OF p] by simp
  subgoal premises p
    unfolding pds_buddy_eq
    by (rule aug_csr.symmetric_buddiesD[OF aug_csr.invar_matchingD(2)[OF pre(1)], THEN iffD1,
                                        OF p[unfolded pds_buddy_eq]])
  subgoal using pre(3) unfolding pds_buddy_eq aug_csr.\<M>_def' .
  subgoal unfolding pds_M_eq by (rule tight_M)
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by (simp add: array_fun_lookup_def)
  subgoal by simp
  subgoal by (simp add: array_fun_lookup_def)
  subgoal for V f init using fset_iterate_below[of V n f init] by auto
  subgoal for V f init using fset_iterate_below[of V n f init] by auto
  subgoal by (auto simp: fset_filter_def)
  subgoal by (simp add: fset_filter_def)
  subgoal by (simp add: fset_is_empty_def)
  subgoal by (rule refl)
  subgoal using wnb_imp_L by simp
  subgoal by simp
  subgoal by (simp add: fset_iterate_def)
  subgoal by (simp add: fset_iterate_def)
  done

lemma fsearch_eq: "ps.search_path = fsearch M \<pi>"
  by (simp add: fsearch_def)

lemma scratch_eq:
  "csr_scratch_assn (Ci, Qi, Li, Fi, Bi, Mi) = ps.scratch_assn Ci Qi Fi Bi Mi * bool_array_set_assn n L Li"
  by (rule ent_iffI)
     (sep_auto simp: csr_scratch_assn_def pds_aux_assn_def ps.scratch_assn_def
                     wcsr.wnb_abstract_eq)+

lemma path_search_csr_rule:
  assumes "card (L \<union> R) \<le> length xs"
  shows "<csr_scratch_assn Di * array_fun_assn n M Bdi * array_fun_val_assn h n \<pi> Pti * Ra \<mapsto>\<^sub>a xs>
         path_search_csr n Di Bdi Pti Ra
         <\<lambda>(res, Pti', Di'). \<exists>\<^sub>Axs'. csr_scratch_assn Di' * array_fun_assn n M Bdi * Ra \<mapsto>\<^sub>a xs' *
            \<up>(length xs' = length xs) *
            (case fsearch M \<pi> of (r, \<pi>') \<Rightarrow> \<up>(imp_result_rel xs' res r) * array_fun_val_assn h n \<pi>' Pti')>"
proof(cases Di rule: prod_cases6)
  case (fields Ci Qi Li Fi Bi Mi)
  show ?thesis
    unfolding fields path_search_csr_def prod.case scratch_eq pds_csr_search_def
    by (sep_auto heap: ps.search_imp_rule[of xs] simp: assms ps.search_post_def fsearch_eq scratch_eq)
qed

lemmas fsearch_correct = ps.search_path_correct[unfolded fsearch_eq pds_M_eq]

end

subsection \<open>The Contract of the Full Path Search\<close>

context hungarian_csr_input
begin

lemma precond_instance:
  assumes "csr_precond M \<pi>"
  shows "hungarian_csr_search h n fs ts ws ls rs M \<pi>"
  by (intro hungarian_csr_search.intro hungarian_csr_input.intro hungarian_csr_search_axioms.intro
            real_embedding_axioms hungarian_csr_input_axioms assms)

lemma path_search_rule_csr:
  assumes "csr_precond M \<pi>" "card (L \<union> R) \<le> length xs"
  shows "<csr_scratch_assn Di * array_fun_assn n M Bdi * array_fun_val_assn h n \<pi> Pti * Ra \<mapsto>\<^sub>a xs>
         path_search_csr n Di Bdi Pti Ra
         <\<lambda>(res, Pti', Di'). \<exists>\<^sub>Axs'. csr_scratch_assn Di' * array_fun_assn n M Bdi * Ra \<mapsto>\<^sub>a xs' *
            \<up>(length xs' = length xs) *
            (case fsearch M \<pi> of (r, \<pi>') \<Rightarrow> \<up>(imp_result_rel xs' res r) * array_fun_val_assn h n \<pi>' Pti')>"
proof-
  interpret s: hungarian_csr_search h n fs ts ws ls rs theta cap M \<pi>
    using assms(1)
    by (rule precond_instance)
  show ?thesis
    by (rule s.path_search_csr_rule[OF assms(2)])
qed

abbreviation "csr_good_search \<equiv>
  hungarian_loop_spec.good_search array_fun_lookup (\<lambda>_. True) (aug_csr.invar_matching n G)
    (aug_csr.\<M> n) wfun G L R"

text \<open>The full path search satisfies the contract of a path search; it does not change the
      matching.\<close>

lemma feasible_ecost: "\<forall>u v. {u, v} \<in> G \<longrightarrow> q u + q v \<le> ecost u v \<Longrightarrow> feasible_min_perfect_dual G wfun q"
  using wfun_eq
  by (auto intro!: feasible_min_perfect_dualI)

lemma tight_ecost: "\<lbrakk>{u, v} \<in> G; ecost u v = q u + q v\<rbrakk> \<Longrightarrow> {u, v} \<in> tight_subgraph G wfun q"
  using wfun_eq
  by (auto intro: in_tight_subgraphI)

lemma fsearch_good_result:
  assumes "csr_precond M \<pi>" "fsearch M \<pi> = (Next_Iteration p, \<pi>')"
  shows "hungarian_loop_spec.good_search_result array_fun_lookup (\<lambda>_. True) (aug_csr.\<M> n) wfun G M \<pi>' p"
proof-
  interpret s: hungarian_csr_search h n fs ts ws ls rs theta cap M \<pi>
    using assms(1)
    by (rule precond_instance)
  note r = s.fsearch_correct(3-7)[OF assms(2)]
  show ?thesis
  proof(rule hungarian_loop_spec.good_search_resultI)
    show "aug_csr.\<M> n M \<subseteq> tight_subgraph G wfun (array_fun_lookup \<pi>')"
    proof
      fix e
      assume "e \<in> aug_csr.\<M> n M"
      moreover from this obtain u v where "e = {u, v}"
        by (auto simp: aug_csr.\<M>_def')
      ultimately show "e \<in> tight_subgraph G wfun (array_fun_lookup \<pi>')"
        using r(2) s.pre(3)
        by (auto intro!: tight_ecost)
    qed
    show "set (edges_of_path p) \<subseteq> tight_subgraph G wfun (array_fun_lookup \<pi>')"
    proof
      fix e
      assume "e \<in> set (edges_of_path p)"
      moreover from this have "e \<in> G"
        using path_edges_subset r(4)
        by (auto)
      moreover from this obtain u v where "e = {u, v}"
        by (auto elim: bipartite_edgeE[OF _ bipartite_G])
      ultimately show "e \<in> tight_subgraph G wfun (array_fun_lookup \<pi>')"
        using r(3)
        by (auto intro!: tight_ecost)
    qed
  qed (use r(1,4) feasible_ecost in auto)
qed

lemma fsearch_good:
  assumes "csr_precond M \<pi>" "fsearch M \<pi> = (r, \<pi>')"
  shows "csr_good_search M (r, M, \<pi>')"
proof-
  interpret s: hungarian_csr_search h n fs ts ws ls rs theta cap M \<pi>
    using assms(1)
    by (rule precond_instance)
  show ?thesis
  proof(rule hungarian_loop_spec.good_searchI)
    show "csr_precond M \<pi>'"
    proof(cases "\<exists>p. r = Next_Iteration p")
      case True
      thus ?thesis
        using hungarian_loop_spec.good_search_resultD[OF fsearch_good_result[OF assms(1)]] assms(2) s.pre(1,3)
        by (auto intro: hungarian_loop_spec.path_search_precondI)
    next
      case False
      thus ?thesis
        using assms s.ps.not_Next_Iteration_same_potential[unfolded s.fsearch_eq]
        by simp
    qed
    show "\<forall>B. \<exists>\<pi>''. feasible_min_perfect_dual G wfun \<pi>'' \<and> sum \<pi>'' (L \<union> R) > B"
      if "r = Dual_Unbounded"
    proof
      fix B
      obtain q where "\<forall>u v. {u, v} \<in> G \<longrightarrow> q u + q v \<le> ecost u v" "B + 1 \<le> sum q (L \<union> R)"
        using s.fsearch_correct(2)[of "B + 1"] assms(2) \<open>r = Dual_Unbounded\<close>
        by simp blast
      thus "\<exists>\<pi>''. feasible_min_perfect_dual G wfun \<pi>'' \<and> sum \<pi>'' (L \<union> R) > B"
        by (intro exI[of _ q]) (auto intro: feasible_ecost)
    qed
  qed (use s.fsearch_correct(1) assms(2) fsearch_good_result[OF assms(1)] in auto)
qed

subsection \<open>The Shortcut\<close>

text \<open>The full path search as the fallback of the shortcut. It leaves the matching as it is, and
      the cursors at the beginning of the neighbourhoods.\<close>

definition "ffallback C M \<pi> = (case fsearch M \<pi> of (r, \<pi>') \<Rightarrow> (r, M, \<pi>', nb_init))"

lemma ffallback_good:
  assumes "csr_precond M \<pi>" "graph.csr_invar C" "wcsr.wnb_abstract C = wcsr.wnb_abstract nb_init"
      and "ffallback C M \<pi> = (r, M', \<pi>', C')"
  shows "csr_good_search M (r, M', \<pi>') \<and> graph.csr_invar C' \<and>
         wcsr.wnb_abstract C' = wcsr.wnb_abstract nb_init"
  using fsearch_good[OF assms(1)] graph.csr_init_invar assms(4)
  by (auto simp: ffallback_def split: prod.splits)

lemma counted_buddy_rule:
  "v \<in> {..<n} \<Longrightarrow>
   <aug_csr.counted_assn n M Mt> array_fun_lookup_imp (fst Mt) v
   <\<lambda>r. aug_csr.counted_assn n M Mt * \<up>(r = array_fun_lookup M v)>"
  by (cases Mt) (sep_auto heap: buddy_lookup_rule simp: aug_csr.counted_assn_pair)

lemma rematch_counted_facts:
  assumes "aug_csr.invar_matching n G M" "{lq, r} \<in> aug_csr.\<M> n M" "l \<notin> Vs (aug_csr.\<M> n M)"
      "{l, r} \<in> G"
  shows "l \<in> {..<n}" "r \<in> {..<n}" "array_fun_lookup M r \<in> {..<n}"
        "card (aug_csr.\<M> n (aug_csr.rematch n M l r)) = card (aug_csr.\<M> n M)"
proof-
  have "array_fun_lookup M r \<noteq> n"
    using buddy_free[of M r] assms(1,2)
    by (auto intro: edges_are_Vs_2)
  hence "{array_fun_lookup M r, r} \<in> G"
    using buddy_edge[of M r] assms(1)
    by (auto simp: aug_csr.invar_matching_def)
  thus "l \<in> {..<n}" "r \<in> {..<n}" "array_fun_lookup M r \<in> {..<n}"
    using assms(4) Vs_G_below
    by (auto intro: edges_are_Vs edges_are_Vs_2)
  show "card (aug_csr.\<M> n (aug_csr.rematch n M l r)) = card (aug_csr.\<M> n M)"
    using maug.rematch_correct(2)[OF assms] card_swap[of "{lq, r}" "aug_csr.\<M> n M" "{l, r}"] assms(2,3)
          edges_are_Vs[of l r "aug_csr.\<M> n M"]
    by (auto simp: Vs_def)
qed

lemma rematch_counted_rule:
  assumes "aug_csr.invar_matching n G M" "{lq, r} \<in> aug_csr.\<M> n M" "l \<notin> Vs (aug_csr.\<M> n M)"
      "{l, r} \<in> G"
  shows "<aug_csr.counted_assn n M Mt> rematch_counted_csr n Mt l r
         <\<lambda>_. aug_csr.counted_assn n (aug_csr.rematch n M l r) Mt>"
  using aug_csr.rematch_counted_imp_rule[OF _ rematch_counted_facts[OF assms]]
  by (simp add: rematch_counted_csr_def)

sublocale sc: path_search_shortcut_imp
  where potential_abstract = array_fun_lookup
    and init_potential = init_pot and potential_invar = "\<lambda>_. True"
    and empty_matching = "\<lambda>_. n" and matching_invar = "aug_csr.invar_matching n G"
    and augment = aug_csr.augment_impl and matching_abstract = "aug_csr.\<M> n"
    and edge_costs = wfun and card_L = "length ls" and card_R = "length rs"
    and fallback = ffallback and G = G and left_order = "sorted_list_of_set L"
    and rnb_current = wcsr.wnb_current and rnb_has = graph.csr_has and rnb_move = graph.csr_move
    and rnb_reset = graph.csr_reset and buddy_get = array_fun_lookup and nil = n
    and rematch = "aug_csr.rematch n" and cap = cap
    and potential_get = array_fun_lookup and potential_upd = array_fun_upd and rnb_init = nb_init
    and edge_costs_code = ecost
    and rnb_invar = graph.csr_invar and rnb_abstract = wcsr.wnb_abstract
    and rnb_iterated = wcsr.wnb_iterated and rnb_remaining = wcsr.wnb_remaining and K = "{..<n}"
    and L = L and R = R and h = h
    and nb_assn = wcsr.wnb_assn and has_imp = wnb_has_imp and current_imp = "wnb_current_imp id"
    and current_cost_imp = wnb_current_cost_imp and move_imp = wnb_move_imp
    and reset_imp = wnb_reset_imp and reset_all_imp = "wnb_reset_all_imp n"
    and pot_assn = "array_fun_val_assn h n" and pot_upd_imp = array_fun_upd_imp
    and pot_get_imp = array_fun_lookup_imp
    and vset_invar = "\<lambda>X. X \<subseteq> {..<n}" and vset_to_set = id
    and vset_assn = "bool_array_set_assn n" and lst = sorted_list_of_set
    and left_is_it = "bool_array_set_is_it n" and left_it_init = bool_array_set_it_init
    and left_it_has_next = bool_array_set_it_has_next and left_it_next = bool_array_set_it_next
    and buddy_assn = "aug_csr.counted_assn n" and buddy_imp = "\<lambda>Mt. array_fun_lookup_imp (fst Mt)"
    and rematch_imp = "rematch_counted_csr n" and left = L
  apply (intro path_search_shortcut_imp.intro path_search_shortcut_imp_axioms.intro
               path_search_shortcut.intro path_search_shortcut_axioms.intro
               nb_best_scan_imp.intro nb_best_scan.intro array_fun_fixed_univ_map
               wcsr.wnb.indexed_iterable_set_axioms real_embedding_axioms
               wcsr.wnb_imp.weighted_neighbourhoods_imp_spec_axioms
               wcsr.wnb_imp.indexed_iterable_set_imp_axioms
               array_fun_val_fixed_univ_map_imp bool_array_set_fixed_univ_set_iterate_imp counted_buddy_rule
               rematch_counted_rule)
  subgoal by (rule bipartite_G)
  subgoal by simp
  subgoal by (rule L_below)
  subgoal by (rule Vs_G_below)
  subgoal by (rule graph.csr_init_invar)
  subgoal by (simp add: wnb_abstract_init)
  subgoal by (rule wnb_abstract_finite)
  subgoal by (simp add: wfun_eq)
  subgoal by (rule buddy_free)
  subgoal by (rule buddy_edge)
  subgoal by (simp add: aug_csr.invar_matching_def)
  subgoal by (rule maug.rematch_correct(1))
  subgoal by (rule maug.rematch_correct(2))
  subgoal by (rule refl)
  subgoal by (rule ffallback_good)
  subgoal by simp
  apply assumption+
  subgoal by (rule L_below)
  subgoal by simp
  subgoal by (rule refl)
  done

text \<open>The path search of the instantiation: the shortcut is tried while the matching has fewer
      than @{term theta} edges.\<close>

definition "fsearch_sc ctx M \<pi> = sc.path_search_sc (card (aug_csr.\<M> n M) < theta) ctx M \<pi>"

text \<open>The fallback runs the full path search, resets the cursors and starts the iteration over
      the left vertices over.\<close>

lemma sc_scratch_csr_scratch:
  assumes "graph.csr_invar C"
  shows "sc_scratch_assn (ys, C) (Di, it) \<Longrightarrow>\<^sub>A csr_scratch_assn Di"
proof(cases Di rule: prod_cases6)
  case (fields Ci Qi Li Fi Bi Mi)
  show ?thesis
    unfolding sc_scratch_assn_def csr_scratch_assn_def fields prod.case
    apply (rule ent_trans[OF _ ent_star_mono[OF _ bool_array_set_quit_iteration]])
     apply (simp only: mult.assoc[symmetric], rule ent_refl)
    using assms
    by (sep_auto)
qed

lemma fallback_csr_rule:
  assumes "csr_precond M \<pi>" "card (L \<union> R) \<le> length xs" "fsearch M \<pi> = (r, \<pi>')"
      and "graph.csr_invar C"
  shows "<sc_scratch_assn (ys, C) (Di, it) * aug_csr.counted_assn n M Mt *
          array_fun_val_assn h n \<pi> Pti * Ra \<mapsto>\<^sub>a xs>
         fallback_csr n Di Mt Pti Ra
         <\<lambda>(res, Mt', Pti', Si'). \<exists>\<^sub>Axs'. sc_scratch_assn (sorted_list_of_set L, nb_init) Si' *
            aug_csr.counted_assn n M Mt' * array_fun_val_assn h n \<pi>' Pti' * Ra \<mapsto>\<^sub>a xs' *
            \<up>(length xs' = length xs) * \<up>(imp_result_rel xs' res r)>"
proof(cases Mt)
  case (Pair Bdi Ki)
  show ?thesis
    apply (rule ht_cons_pre[OF ent_star_mono[OF ent_star_mono[OF ent_star_mono[OF
                 sc_scratch_csr_scratch[OF assms(4)]]]]])
       apply (rule ent_refl)+
    unfolding fallback_csr_def Pair aug_csr.counted_assn_pair fst_conv
    supply wcsr.wnb_imp.reset_all_rule[sep_heap_rules del] bool_array_set_it_init_rule[sep_heap_rules del]
    by (sep_auto heap: path_search_rule_csr[OF assms(1,2), of Di Bdi Pti Ra, unfolded assms(3) prod.case]
                       wcsr.wnb_imp.reset_all_rule[OF _ wnb_abstract_cursor]
                       bool_array_set_it_init_rule[OF L_below, unfolded id_apply]
                 simp: csr_scratch_assn_def sc_scratch_assn_def aug_csr.counted_assn_pair split: prod.splits)
qed

text \<open>The path search with the shortcut refines @{const fsearch_sc}.\<close>

lemma sc_ctx_props:
  assumes "sc.sc_ctx_invar (ys, C)"
  shows "set ys \<subseteq> L" "graph.csr_invar C" "wcsr.wnb_abstract C = wcsr.wnb_abstract nb_init"
  using assms
  by (simp_all add: sc.sc_ctx_invar_def)

lemma aug_path_length:
  "\<lbrakk>path G p; distinct p; matching_augmenting_path M p\<rbrakk> \<Longrightarrow> 2 \<le> length p \<and> length p \<le> card (L \<union> R)"
  using subset_path_Vs[of G p] card_mono[of "L \<union> R" "set p"] distinct_card[of p]
  by (auto simp: Vs_G matching_augmenting_path_def)

lemma sc_loop_csr_props:
  assumes "csr_precond M \<pi>" "sc.sc_ctx_invar (ys, C)" "sc.sc_loop (C, M, \<pi>) ys = ((C1, M1, \<pi>1), res, xs1)"
          "card (L \<union> R) \<le> length xs"
  shows "csr_precond M1 \<pi>1" "graph.csr_invar C1" "res \<noteq> None \<Longrightarrow> 2 \<le> length xs"
proof-
  have "sc.sc_inv M (C1, M1, \<pi>1) res"
    using sc.sc_loop_valid[of ys M "(C, M, \<pi>)", OF _ _ assms(3)] assms(1,2) sc_ctx_props[of ys C]
    by (simp add: sc.sc_inv_def)
  thus "csr_precond M1 \<pi>1" "graph.csr_invar C1"
    by (simp_all add: sc.sc_inv_def)
  show "2 \<le> length xs" if "res \<noteq> None"
  proof-
    obtain l p where "res = Some (l, p)"
      using \<open>res \<noteq> None\<close>
      by auto
    hence "graph_augmenting_path G (aug_csr.\<M> n M1) p"
      using \<open>sc.sc_inv M (C1, M1, \<pi>1) res\<close> sc.good_search_resultD(5)
      by (auto simp: sc.sc_inv_def)
    thus ?thesis
      using aug_path_length[of p "aug_csr.\<M> n M1"] assms(4)
      by (auto)
  qed
qed

lemma path_search_sc_rule_csr:
  assumes "csr_precond M \<pi>" "sc.sc_ctx_invar c" "fsearch_sc c M \<pi> = (r, M', \<pi>', c')"
      and "card (L \<union> R) \<le> length xs"
  shows "<sc_scratch_assn c Si * aug_csr.counted_assn n M Mt * array_fun_val_assn h n \<pi> Pti *
          Ra \<mapsto>\<^sub>a xs>
         path_search_sc_csr n theta cap Si Mt Pti Ra
         <\<lambda>(res, Mt', Pti', Si'). \<exists>\<^sub>Axs'. sc_scratch_assn c' Si' * aug_csr.counted_assn n M' Mt' *
            array_fun_val_assn h n \<pi>' Pti' * Ra \<mapsto>\<^sub>a xs' * \<up>(length xs' = length xs) *
            \<up>(imp_result_rel xs' res r)>"
proof-
  obtain ys C Di it where "c = (ys, C)" "Si = (Di, it)"
    by (cases c; cases Si) auto
  note cs = this
  note I = sc_ctx_props[OF assms(2)[unfolded cs(1)]]
  note mc = aug_csr.matching_card_imp_rule[where M = M and Mi = Mt]
  show ?thesis
  proof(cases "card (aug_csr.\<M> n M) < theta")
    case False
    obtain r0 \<pi>0 where "fsearch M \<pi> = (r0, \<pi>0)"
      by fastforce
    moreover from this have "r = r0" "M' = M" "\<pi>' = \<pi>0" "c' = (sorted_list_of_set L, nb_init)"
      using assms(3) False
      by (simp_all add: fsearch_sc_def sc.path_search_sc_def sc.sc_try_def cs(1) ffallback_def)
    ultimately show ?thesis
      unfolding path_search_sc_csr_def cs prod.case
      by (sep_auto heap: mc fallback_csr_rule[OF assms(1,4) \<open>fsearch M \<pi> = (r0, \<pi>0)\<close> I(2)]
                   simp: False)
  next
    case True
    obtain s res xs1 where "sc.sc_loop (C, M, \<pi>) ys = (s, res, xs1)"
      by (cases "sc.sc_loop (C, M, \<pi>) ys" rule: prod_cases3) auto
    moreover obtain C1 M1 \<pi>1 where "s = (C1, M1, \<pi>1)"
      by (cases s rule: prod_cases3) auto
    ultimately have "sc.sc_loop (C, M, \<pi>) ys = ((C1, M1, \<pi>1), res, xs1)"
      by simp
    note lp = this
    note S = sc_loop_csr_props[OF assms(1) assms(2)[unfolded cs(1)] lp assms(4)]
    note sh = sc.shortcut_imp_rule[OF assms(1) I lp S(3), unfolded id_apply[of L]]
    obtain Ci Qi Li Fi Bi Mi where "Di = (Ci, Qi, Li, Fi, Bi, Mi)"
      by (cases Di rule: prod_cases6)
    note Di = this
    show ?thesis
    proof(cases res)
      case None
      obtain r1 \<pi>1' where "fsearch M1 \<pi>1 = (r1, \<pi>1')"
        by fastforce
      moreover from this have "r = r1" "M' = M1" "\<pi>' = \<pi>1'" "c' = (sorted_list_of_set L, nb_init)"
        using assms(3) True
        by (simp_all add: fsearch_sc_def sc.path_search_sc_def sc.sc_try_def cs(1) lp None ffallback_def)
      ultimately show ?thesis
        using assms(4)
        unfolding path_search_sc_csr_def cs Di prod.case
        by (sep_auto heap: mc sh fallback_csr_rule[OF S(1) _ \<open>fsearch M1 \<pi>1 = (r1, \<pi>1')\<close> S(2),
                                       where Di = "(Ci, Qi, Li, Fi, Bi, Mi)", unfolded sc_scratch_assn_def prod.case]
                     simp: True None sc_csr_shortcut_def sc_scratch_assn_def)
    next
      case (Some a)
      then obtain l p where "res = Some (l, p)"
        by (cases a) auto
      moreover from this have "r = Next_Iteration p" "M' = M1" "\<pi>' = \<pi>1" "c' = (xs1, C1)"
        using assms(3) True
        by (simp_all add: fsearch_sc_def sc.path_search_sc_def sc.sc_try_def cs(1) lp)
      ultimately show ?thesis
        using S(3)
        unfolding path_search_sc_csr_def cs Di prod.case
        by (sep_auto heap: mc sh simp: True sc_csr_shortcut_def sc_scratch_assn_def)
    qed
  qed
qed

subsection \<open>The Top Loop\<close>

lemma ts_not_L: "i < length fs \<Longrightarrow> ts ! i \<notin> L"
  using ts_R sides_disjoint
  by blast

lemma init_pot_edge:
  "i < length fs \<Longrightarrow> array_fun_lookup init_pot (fs ! i) + array_fun_lookup init_pot (ts ! i) \<le> h (ws ! i)"
  using init_pot_props(1)[of "fs ! i" "ts ! i"] init_pot_props(2) ts_not_L[of i] wnb_abstract_init[of "fs ! i"]
        fs_L[of i] G_edge[of i] ecost_edge[of i]
  by (auto)

lemma feasible_init: "feasible_min_perfect_dual G wfun (array_fun_lookup init_pot)"
  using init_pot_edge ecost_edge ecost_edge_sym
  by (auto intro!: feasible_ecost elim!: G_edgeE simp: add.commute)

lemma augment_card:
  assumes "aug_csr.invar_matching n G M" "graph_augmenting_path G (aug_csr.\<M> n M) p"
  shows "card (aug_csr.\<M> n (aug_csr.augment_impl M p)) = Suc (card (aug_csr.\<M> n M))"
  using new_matching_plus_one[of "aug_csr.\<M> n M" p] maug.augmentation_correct(2)[OF assms] assms
  by (simp add: aug_csr.invar_matching_def)

sublocale hl: hungarian_top_loop_imp
  where potential_abstract = array_fun_lookup
    and init_potential = init_pot and potential_invar = "\<lambda>_. True"
    and empty_matching = "\<lambda>_. n" and matching_invar = "aug_csr.invar_matching n G"
    and augment = aug_csr.augment_impl and matching_abstract = "aug_csr.\<M> n"
    and edge_costs = wfun and card_L = "length ls" and card_R = "length rs"
    and path_search = fsearch_sc and ctx_invar = sc.sc_ctx_invar
    and init_ctx = "(sorted_list_of_set L, nb_init)" and G = G and L = L and R = R
    and path_search_imp = "path_search_sc_csr n theta cap" and augment_imp = augment_counted_csr
    and scratch_assn = sc_scratch_assn and matching_assn = "aug_csr.counted_assn n"
    and pot_assn = "array_fun_val_assn h n" and len_bound = "card (L \<union> R)"
proof(intro hungarian_top_loop_imp.intro hungarian_top_loop_imp_axioms.intro hungarian_loop.intro,
       goal_cases)
  case 1 show ?case by (rule bipartite_G)
next
  case 2 show ?case by (simp add: distinct_card[OF ls_distinct])
next
  case 3 show ?case by (simp add: distinct_card[OF rs_distinct])
next
  case 4 show ?case by simp
next
  case 5 show ?case by simp
next
  case 6 show ?case by (simp add: Vs_G)
next
  case 7 show ?case by simp
next
  case 8 show ?case by (rule feasible_init)
next
  case (9 M) thus ?case by (simp add: aug_csr.invar_matching_def)
next
  case 10 show ?case by (rule maug.empty_matching_props(1)[OF Vs_G_below])
next
  case 11 show ?case by (rule maug.empty_matching_props(2))
next
  case (12 M p) thus ?case by (rule maug.augmentation_correct(1))
next
  case (13 M p) thus ?case by (rule maug.augmentation_correct(2))
next
  case (14 c M \<pi> r M' \<pi>' c')
  thus ?case unfolding fsearch_sc_def by (rule sc.path_search_sc_correct(1))
next
  case (15 c M \<pi> r M' \<pi>' c')
  thus ?case unfolding fsearch_sc_def by (rule sc.path_search_sc_correct(2))
next
  case 16 show ?case by (simp add: sc.sc_ctx_invar_def graph.csr_init_invar)
next
  case 17 thus ?case by (rule path_search_sc_rule_csr)
next
  case (18 M p k xs Mi Ra)
  have sub: "set (take k xs) \<subseteq> {..<n}"
    using 18(2,4) subset_path_Vs[of G p] Vs_G_below by auto
  show ?case
    using aug_csr.augment_counted_imp_rule[where M = M and k = k and xs = xs and Mi = Mi and Ra = Ra,
                                           OF _ 18(3) sub] augment_card[OF 18(1,2)] 18(4)
    by simp
qed

end

subsection \<open>Initialisation\<close>

lemma perm_weights_targets_rule:
  assumes "i \<le> length es" "length xs = length es" "\<forall>e\<in>set es. e < length us \<and> e < length vs"
  shows "<Ea \<mapsto>\<^sub>a (map ((!) us) (take i es) @ drop i es) * Ta \<mapsto>\<^sub>a us * Wa \<mapsto>\<^sub>a vs * Wc \<mapsto>\<^sub>a xs>
         perm_weights_targets_imp Ea Ta Wa Wc i (length es)
         <\<lambda>_. Ea \<mapsto>\<^sub>a map ((!) us) es * Ta \<mapsto>\<^sub>a us * Wa \<mapsto>\<^sub>a vs *
              Wc \<mapsto>\<^sub>a (take i xs @ drop i (map ((!) vs) es))>"
  using assms(1,2)
proof(induction arbitrary: xs rule: inc_induct)
  case base
  thus ?case
    by (subst perm_weights_targets_imp.simps) (sep_auto)
next
  case (step i)
  show ?case
    using step.hyps(2) step.prems assms(3) perm_step_lists(1,2)[OF step.hyps(2) step.prems, where vs = vs]
          perm_step_lists(3,4)[OF step.hyps(2) step.prems, where us = us]
    by (subst perm_weights_targets_imp.simps)
       (sep_auto heap: step.IH[of "list_update xs i (vs ! (es ! i))"])
qed

lemma bool_array_set_insert_all_rule:
  assumes "i \<le> length xs" "set xs \<subseteq> {..<n}" "S \<subseteq> {..<n}"
  shows "<La \<mapsto>\<^sub>a xs * bool_array_set_assn n S s> bool_array_set_insert_all La i (length xs) s
         <\<lambda>_. La \<mapsto>\<^sub>a xs * bool_array_set_assn n (S \<union> set (drop i xs)) s>"
  using assms(1,3)
proof(induction arbitrary: S rule: inc_induct)
  case base
  show ?case
    by (subst bool_array_set_insert_all.simps) (sep_auto)
next
  case (step i)
  have "xs ! i \<in> {..<n}"
    using step.hyps(2) assms(2) nth_mem
    by blast
  thus ?case
    using step.hyps(2) step.prems
    by (subst bool_array_set_insert_all.simps)
       (sep_auto heap: fixed_univ_set_basic_imp.fixed_univ_set_insert_rule[OF
                         fixed_univ_set_imp.axioms(1)[OF bool_array_set_fixed_univ_set_imp]]
                       step.IH[of "insert (xs ! i) S"]
                 simp: Cons_nth_drop_Suc[symmetric])
qed

text \<open>Freshly allocated arrays as maps and sets.\<close>

lemma bool_array_set_insert_all_new:
  "set xs \<subseteq> {..<n} \<Longrightarrow>
   <La \<mapsto>\<^sub>a xs * s \<mapsto>\<^sub>a replicate n False> bool_array_set_insert_all La 0 (length xs) s
   <\<lambda>_. La \<mapsto>\<^sub>a xs * bool_array_set_assn n (set xs) s>"
  using bool_array_set_insert_all_rule[where i = 0 and xs = xs and n = n and S = "{}" and s = s and La = La]
  by (simp add: bool_array_set_assn_replicate)

context hungarian_csr_input
begin

lemma array_fun_val_zero: "Xi \<mapsto>\<^sub>a replicate n 0 \<Longrightarrow>\<^sub>A array_fun_val_assn h n (\<lambda>_. 0) Xi"
  unfolding array_fun_val_assn_def array_fun_assn_replicate[symmetric]
  by (rule ent_ex_postI[where x = "\<lambda>_. 0"]) simp

lemma init_pot_rule:
  "<graph.csr_assn nb_init (Ba, Ea, Ca) * Wc \<mapsto>\<^sub>a W *
    Pti \<mapsto>\<^sub>a replicate n 0 * bool_array_set_assn n L Li>
   init_pot_csr ((Ba, Ea, Ca), Wc) Li Pti
   <\<lambda>_. wcsr.wnb_assn (fst (ipot.init_potential_coll nb_init (\<lambda>_. 0) L)) ((Ba, Ea, Ca), Wc) *
         array_fun_val_assn h n init_pot Pti * bool_array_set_assn n L Li>"
  unfolding init_pot_csr_def
  apply(rule ht_cons_pre[OF _ ipot.init_pot_imp_rule[of nb_init L, OF graph.csr_init_invar L_below _
                                                    wnb_abstract_finite, simplified]])
  unfolding wcsr.wnb_assn_split array_fun_val_assn_def array_fun_assn_replicate[symmetric]
  by (sep_auto)

lemma card_LR: "card (L \<union> R) \<le> n"
  using card_mono[OF finite_lessThan verts_below]
  by simp

lemma hungarian_step:
  "<wcsr.wnb_assn nb_init Ci * hp.heap_assn heap_empty Qi *
    forest_csr.forest_assn n (forest_csr.empty_forest n {}) Fi *
    Bi \<mapsto>\<^sub>a replicate n n * Mi \<mapsto>\<^sub>a replicate n 0 * bool_array_set_assn n L Li *
    bool_array_set_is_it n L Li (sorted_list_of_set L) it *
    Mm \<mapsto>\<^sub>a replicate n n * Ki \<mapsto>\<^sub>r 0 * array_fun_val_assn h n init_pot Pti * Ra \<mapsto>\<^sub>a replicate n 0>
   hungarian_csr n theta cap (length ls) (length rs) ((Ci, Qi, Li, Fi, Bi, Mi), it) (Mm, Ki) Pti Ra
   <\<lambda>(r, (Mm', _), Pti', Si'). \<exists>\<^sub>AM \<pi>. array_fun_assn n M Mm' * array_fun_val_assn h n \<pi> Pti' * true *
      \<up>((r = result.success \<and> hl.hungarian = Some M) \<or> (r = result.failure \<and> hl.hungarian = None))>"
  unfolding hungarian_csr_def
  apply(rule ht_cons_pre[OF _ ht_cons_post[OF hl.hungarian_imp_rule[of "replicate n 0", simplified, OF card_LR]]])
  subgoal
    unfolding aug_csr.counted_assn_pair maug.empty_matching_props(2) sc_scratch_assn_def
              pds_aux_assn_def array_fun_val_assn_def array_fun_assn_replicate[symmetric]
    by (sep_auto)
  by (sep_auto simp: aug_csr.counted_assn_pair split: prod.splits)

lemma perm_csr_rule:
  "<Ea \<mapsto>\<^sub>a ei.inp.E_spec * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * Wc \<mapsto>\<^sub>a replicate (length ei.inp.E_spec) 0>
   perm_weights_targets_imp Ea Ta Wa Wc 0 (length ei.inp.E_spec)
   <\<lambda>_. Ea \<mapsto>\<^sub>a Et * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * Wc \<mapsto>\<^sub>a W>"
  using perm_weights_targets_rule[where i = 0 and es = ei.inp.E_spec and us = ts and vs = ws
                                    and xs = "replicate (length ei.inp.E_spec) 0"]
        ei.E_spec_ids ts_length ws_length
  by (simp add: Et_def W_def)

lemma csr_build_rule:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts> csr_build_edges n (Fa, Ta) 0
   <\<lambda>(Ba, Ea). Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Ba \<mapsto>\<^sub>a ei.inp.B_spec * Ea \<mapsto>\<^sub>a ei.inp.E_spec>"
  unfolding csr_build_edges_src[symmetric]
  by (rule ei.csr_build_rule)

text \<open>The imperative Hungarian method on the CSR representation computes the result of the
      functional @{term hl.hungarian}.\<close>

lemma hungarian_csr_run_rule:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs>
   hungarian_csr_run n theta cap Fa Ta Wa La Rv
   <\<lambda>(r, Mi, Pti). \<exists>\<^sub>AM \<pi>. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs *
      array_fun_assn n M Mi * array_fun_val_assn h n \<pi> Pti * true *
      \<up>((r = result.success \<and> hl.hungarian = Some M) \<or> (r = result.failure \<and> hl.hungarian = None))>"
proof-
  note rs = wcsr.wnb_imp.reset_all_rule[OF init_pot_props(3) wnb_abstract_cursor]
  note ii = bool_array_set_it_init_rule[OF L_below, unfolded id_apply]
  show ?thesis
    unfolding hungarian_csr_run_def
    supply wcsr.wnb_imp.reset_all_rule[sep_heap_rules del] bool_array_set_it_init_rule[sep_heap_rules del]
    by (sep_auto heap: csr_build_rule perm_csr_rule graph.csr_cursor_init_rule
                       bool_array_set_insert_all_new init_pot_rule rs ii hp.heap_empty_imp_rule
                       forest_csr.forest_empty_imp_rule hungarian_step
                 simp: L_below)
qed

text \<open>Together with the correctness of the functional Hungarian method: on success, the matching
      is a perfect matching of minimum weight; on failure, there is no perfect matching.\<close>

lemma hungarian_csr_run_correct:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs>
   hungarian_csr_run n theta cap Fa Ta Wa La Rv
   <\<lambda>(r, Mi, Pti). \<exists>\<^sub>AM \<pi>. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs *
      array_fun_assn n M Mi * array_fun_val_assn h n \<pi> Pti * true *
      \<up>((r = result.success \<and> min_weight_perfect_matching G wfun (aug_csr.\<M> n M)) \<or>
        (r = result.failure \<and> (\<nexists>M'. perfect_matching G M')))>"
  apply (rule ht_cons_post_prec[OF hungarian_csr_run_rule])
  apply (clarsimp split: prod.splits)
  apply (intro ent_ex_preI)
  apply (rule ent_ex_postI, rule ent_ex_postI)
  by (sep_auto simp: hl.hungarian_correctness(2) dest: hl.hungarian_correctness(1))

end

end
