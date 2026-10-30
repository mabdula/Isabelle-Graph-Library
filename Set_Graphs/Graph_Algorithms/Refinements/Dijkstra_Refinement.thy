theory Dijkstra_Refinement
  imports "Graph_Algorithms_Dev.Dijkstra" Data_Structures.Real_Embedding
   Data_Structures.Fixed_Univ_Set_Specs_Imp Data_Structures.Fixed_Univ_Map_Specs_Imp
   Data_Structures.Iterable_Set_Specs_Imp
   Data_Structures.Fixed_Univ_Key_Value_Queue_Specs_Imp
begin

provenance ai


section \<open>Refinement of Dijkstra's Algorithm to Imperative HOL\<close>

text \<open>The refinement follows the discipline of the network simplex refinement: a code locale
      @{text dijkstra_impl_spec} fixes the imperative operations (only their types) and defines the
      imperative program; a proof locale @{text dijkstra_impl_refine} combines the functional
      locale @{locale dijkstra} with the imperative ADT locales, which supply the Hoare triples.

      \<^emph>\<open>The program does not allocate.\<close> All data structures -- the distance, parent and weight
      arrays, the seen set, the queue, the graph and the source set -- are passed in as heap handles
      and mutated in place. Allocation (and resetting after a previous run) is left to the caller,
      so that the memory can be reused across several calls. Accordingly, the handles passed in must
      represent the components of the functional @{const dijkstra.initial_state}.

      Distances and weights are stored as values of a linearly ordered additive group @{typ 'n},
      read back into the reals by the embedding @{term h} of @{locale dist_embedding};
      @{term unreached} represents the functional marker \<open>-1\<close>. Distances/weights, vertices and
      edges are of sort @{class heap}, as the standard implementations store them in heap cells
      (e.g.\ the weight lookup is @{const Array.nth} on an array indexed by edges).\<close>


subsection \<open>The imperative state\<close>

text \<open>The heap handles of the program. They do not change during the computation, since all
      operations mutate in place. The vertex currently being scanned is passed as a separate argument
      of the loop and the target found is its result.\<close>

record ('di, 'si, 'pi, 'hi, 'gi, 'srci, 'wi, 'ei, 'ti, 'ai) dij_impl_state =
  dimp_dist    :: 'di
  dimp_seen    :: 'si
  dimp_parent  :: 'pi
  dimp_heap    :: 'hi
  dimp_graph   :: 'gi
  dimp_srcs    :: 'srci
  dimp_weight  :: 'wi
  dimp_ends    :: 'ei
  dimp_target  :: 'ti
  dimp_allowed :: 'ai


subsection \<open>The code locale\<close>

locale dijkstra_impl_spec =
  fixes unreached :: "'n::{linordered_ab_group_add, heap}"
    and target_imp :: "'ti \<Rightarrow> 'v::heap \<Rightarrow> bool Heap"
    and allowed_imp :: "'ai \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'e::heap \<Rightarrow> 'n \<Rightarrow> bool Heap"
    and early_stop :: bool
    and snd_imp :: "'ei \<Rightarrow> 'e::heap \<Rightarrow> 'v Heap"
    and weight_lookup_imp :: "'wi \<Rightarrow> 'e \<Rightarrow> 'n Heap"
    and dist_upd_imp :: "'di \<Rightarrow> 'v \<Rightarrow> 'n \<Rightarrow> unit Heap"
    and dist_lookup_imp :: "'di \<Rightarrow> 'v \<Rightarrow> 'n Heap"
    and parent_upd_imp :: "'pi \<Rightarrow> 'v \<Rightarrow> 'e option \<Rightarrow> unit Heap"
    and seen_insert_imp :: "'v \<Rightarrow> 'si \<Rightarrow> unit Heap"
    and seen_isin_imp :: "'si \<Rightarrow> 'v \<Rightarrow> bool Heap"
    and src_current_imp :: "'srci \<Rightarrow> 'v Heap"
    and src_has_imp :: "'srci \<Rightarrow> bool Heap"
    and src_move_imp :: "'srci \<Rightarrow> unit Heap"
    and out_current_imp :: "'gi \<Rightarrow> 'v \<Rightarrow> 'e Heap"
    and out_has_imp :: "'gi \<Rightarrow> 'v \<Rightarrow> bool Heap"
    and out_move_imp :: "'gi \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and out_reset_imp :: "'gi \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and queue_extract_min_imp :: "'hi \<Rightarrow> ('v \<times> 'n) option Heap"
    and queue_decrease_key_imp :: "'hi \<Rightarrow> 'v \<Rightarrow> 'n \<Rightarrow> unit Heap"
    and queue_insert_imp :: "'hi \<Rightarrow> 'v \<Rightarrow> 'n \<Rightarrow> unit Heap"
    and parent_lookup_imp :: "'pi \<Rightarrow> 'v \<Rightarrow> 'e option Heap"
    and fst_imp :: "'ei \<Rightarrow> 'e \<Rightarrow> 'v Heap"
begin

text \<open>Relax the edge @{term e} leaving the vertex @{term u} being scanned, whose distance is
      @{term du}. Mirrors @{const dijkstra.relax_edge}. The edge test @{term allowed_imp} is made
      after the seen test and sees the tail, the head, the edge and its weight.\<close>

definition relax_edge_imp ::
  "('di, 'si, 'pi, 'hi, 'gi, 'srci, 'wi, 'ei, 'ti, 'ai) dij_impl_state \<Rightarrow> 'v \<Rightarrow> 'n \<Rightarrow> 'e \<Rightarrow> unit Heap" where
  "relax_edge_imp s u du e =
     do { v \<leftarrow> snd_imp (dimp_ends s) e;
          sn \<leftarrow> seen_isin_imp (dimp_seen s) v;
          if sn then return ()
          else do {
            we \<leftarrow> weight_lookup_imp (dimp_weight s) e;
            a \<leftarrow> allowed_imp (dimp_allowed s) u v e we;
            if \<not> a then return ()
            else do {
              dv \<leftarrow> dist_lookup_imp (dimp_dist s) v;
              let nv = du + we;
              if dv = unreached then do {
                dist_upd_imp (dimp_dist s) v nv;
                parent_upd_imp (dimp_parent s) v (Some e);
                queue_insert_imp (dimp_heap s) v nv }
              else if nv < dv then do {
                dist_upd_imp (dimp_dist s) v nv;
                parent_upd_imp (dimp_parent s) v (Some e);
                queue_decrease_key_imp (dimp_heap s) v nv }
              else return () } } }"

text \<open>Register one source. Mirrors @{const dijkstra.insert_source}.\<close>

definition insert_source_imp ::
  "('di, 'si, 'pi, 'hi, 'gi, 'srci, 'wi, 'ei, 'ti, 'ai) dij_impl_state \<Rightarrow> 'v \<Rightarrow> unit Heap" where
  "insert_source_imp s v =
     do { dist_upd_imp (dimp_dist s) v 0;
          queue_insert_imp (dimp_heap s) v 0 }"

text \<open>The target test on a settled vertex. It is only made with early stopping.\<close>

definition target_test_imp ::
  "('di, 'si, 'pi, 'hi, 'gi, 'srci, 'wi, 'ei, 'ti, 'ai) dij_impl_state \<Rightarrow> 'v \<Rightarrow> bool Heap" where
  "target_test_imp s u = (if early_stop then target_imp (dimp_target s) u else return False)"

text \<open>The main loop, one step of the functional @{const dijkstra.dijkstra} per iteration. The
      argument @{term cur} is the vertex currently being scanned; the result is the target found
      (@{const None} if the queue ran empty).\<close>

partial_function (heap) dijkstra_loop_imp ::
  "('di, 'si, 'pi, 'hi, 'gi, 'srci, 'wi, 'ei, 'ti, 'ai) dij_impl_state \<Rightarrow> 'v option \<Rightarrow> 'v option Heap" where
  "dijkstra_loop_imp s cur =
     (case cur of
        Some u \<Rightarrow> do {
          b \<leftarrow> out_has_imp (dimp_graph s) u;
          if b then do {
            du \<leftarrow> dist_lookup_imp (dimp_dist s) u;
            e \<leftarrow> out_current_imp (dimp_graph s) u;
            out_move_imp (dimp_graph s) u;
            relax_edge_imp s u du e;
            dijkstra_loop_imp s (Some u) }
          else dijkstra_loop_imp s None }
      | None \<Rightarrow> do {
          b \<leftarrow> src_has_imp (dimp_srcs s);
          if b then do {
            v \<leftarrow> src_current_imp (dimp_srcs s);
            src_move_imp (dimp_srcs s);
            insert_source_imp s v;
            dijkstra_loop_imp s None }
          else do {
            (mo) \<leftarrow> queue_extract_min_imp (dimp_heap s);
            (case mo of
               None \<Rightarrow> return None
             | Some u \<Rightarrow> 
               case u of (u, k) \<Rightarrow>
               do {
                 sn \<leftarrow> seen_isin_imp (dimp_seen s) u;
                 if sn then dijkstra_loop_imp s None
                 else do {
                   seen_insert_imp u (dimp_seen s);
                   t \<leftarrow> target_test_imp s u;
                   if t then return (Some u)
                   else do {
                     out_reset_imp (dimp_graph s) u;
                     dijkstra_loop_imp s (Some u) } } }) } })"

text \<open>The entry point: no vertex is being scanned initially.\<close>

definition "dijkstra_imp s = dijkstra_loop_imp s None"

text \<open>Path reconstruction on the final state: going back from @{term v} along the parent edges to
      a source, the edges are written into the array @{term Ra} given by the caller, from position
      @{term k} on. The path thus ends up reversed in the array. The result is the position after
      the last edge written. Mirrors @{const dijkstra.build_path}.\<close>

partial_function (heap) path_rev_imp :: "'ei \<Rightarrow> 'pi \<Rightarrow> 'e array \<Rightarrow> 'v \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "path_rev_imp Ei Pa Ra v k =
     do { p \<leftarrow> parent_lookup_imp Pa v;
          (case p of
             None \<Rightarrow> return k
           | Some e \<Rightarrow> do {
               _ \<leftarrow> Array.upd k e Ra;
               u \<leftarrow> fst_imp Ei e;
               path_rev_imp Ei Pa Ra u (Suc k) }) }"

definition path_imp ::
  "('di, 'si, 'pi, 'hi, 'gi, 'srci, 'wi, 'ei, 'ti, 'ai) dij_impl_state \<Rightarrow> 'e array \<Rightarrow> 'v \<Rightarrow> nat Heap" where
  "path_imp s Ra v = path_rev_imp (dimp_ends s) (dimp_parent s) Ra v 0"

end


subsection \<open>The proof locale\<close>

text \<open>The proof locale combines

        \<^item> the functional locale @{locale dijkstra},
        \<^item> the distance embedding @{locale dist_embedding},
        \<^item> an imperative ADT locale for every data structure: the graph, the distance array
          (entries read through @{term h}), the parent array (identity), the weight array over the
          edge set (entries read through @{term h}), the seen set, the source set and the queue
          (keys read through @{term h}), and
        \<^item> the code locale @{locale dijkstra_impl_spec}.

      The weights are given by a functional array @{term W} over @{term \<E>} agreeing with
      @{term w}. The endpoint reads @{term snd_imp} and @{term fst_imp} only read a heap
      representation @{term ends_assn} of the endpoints. The
      target test @{term target_imp} decides the functional predicate @{term target} on a heap
      representation @{term target_assn}. Likewise, the edge test @{term allowed_imp} decides
      @{term allowed} for an edge given by its tail, head and weight on a heap representation
      @{term allowed_assn}. None of these representations is known to the refinement: each is
      fixed by the instantiation and carried as a frame through all Hoare triples.\<close>

locale dijkstra_impl_refine =
  dijkstra where fst = fst and target = target and allowed = allowed and early_stop = early_stop
      and dist_invar = dist_invar and dist_upd = dist_upd and dist_lookup = dist_lookup
      and parent_invar = parent_invar and parent_upd = parent_upd and parent_lookup = parent_lookup
      and queue_abstract = queue_abstract +
  dist_embedding where h = h and unreached = unreached +
  graph_imp: indexed_iterable_set_imp where
      idx_invar = out_invar and idx_abstract = out_abstract and idx_current = out_current
      and idx_has = out_has and idx_iterated = out_iterated and idx_remaining = out_remaining
      and idx_move = out_move and idx_reset = out_reset and K = \<V>
      and idx_assn = out_assn and idx_current_imp = out_current_imp
      and idx_has_imp = out_has_imp and idx_move_imp = out_move_imp
      and idx_reset_imp = out_reset_imp +
  dist_imp: fixed_univ_map_imp where K = \<V>
      and fixed_univ_map_invar = dist_invar
      and fixed_univ_map_upd = dist_upd
      and fixed_univ_map_lookup = dist_lookup
      and fixed_univ_map_val = h
      and fixed_univ_map_assn = dist_assn
      and fixed_univ_map_upd_imp = dist_upd_imp
      and fixed_univ_map_lookup_imp = dist_lookup_imp +
  parent_imp: fixed_univ_map_imp where K = \<V>
      and fixed_univ_map_invar = parent_invar
      and fixed_univ_map_upd = parent_upd
      and fixed_univ_map_lookup = parent_lookup
      and fixed_univ_map_val = id
      and fixed_univ_map_assn = parent_assn
      and fixed_univ_map_upd_imp = parent_upd_imp
      and fixed_univ_map_lookup_imp = parent_lookup_imp +
  weight_imp: fixed_univ_map_imp where K = \<E>
      and fixed_univ_map_invar = weight_invar
      and fixed_univ_map_upd = weight_upd
      and fixed_univ_map_lookup = weight_lookup
      and fixed_univ_map_val = h
      and fixed_univ_map_assn = weight_assn
      and fixed_univ_map_upd_imp = weight_upd_imp
      and fixed_univ_map_lookup_imp = weight_lookup_imp +
  seen_imp: fixed_univ_set_imp where U = \<V>
      and fixed_univ_set_invar = seen_invar and fixed_univ_set_abstract = seen_abstract
      and fixed_univ_set_empty = seen_empty and fixed_univ_set_insert = seen_insert
      and fixed_univ_set_delete = seen_delete and fixed_univ_set_isin = seen_isin
      and fixed_univ_set_assn = seen_assn and fixed_univ_set_empty_imp = seen_empty_imp
      and fixed_univ_set_insert_imp = seen_insert_imp and fixed_univ_set_delete_imp = seen_delete_imp
      and fixed_univ_set_isin_imp = seen_isin_imp +
  src_imp: iterable_set_imp where
      iterable_set_invar = src_invar and iterable_set_abstract = src_abstract
      and current_element = src_current and has_current = src_has
      and iterated = src_iterated and remaining = src_remaining and move_on = src_move
      and iterable_set_assn = src_assn and current_element_imp = src_current_imp
      and has_current_imp = src_has_imp and move_on_imp = src_move_imp +
  queue_imp: key_value_queue_imp where U = \<V> and queue_empty = queue_empty
      and queue_extract_min = queue_extract_min and queue_decrease_key = queue_decrease_key
      and queue_insert = queue_insert and queue_invar = queue_invar
      and queue_abstract = queue_abstract and queue_key = h +
  dijkstra_impl_spec where unreached = unreached and target_imp = target_imp
      and allowed_imp = allowed_imp and early_stop = early_stop
      and snd_imp = snd_imp and weight_lookup_imp = weight_lookup_imp
      and dist_upd_imp = dist_upd_imp and dist_lookup_imp = dist_lookup_imp
      and parent_upd_imp = parent_upd_imp
      and seen_insert_imp = seen_insert_imp and seen_isin_imp = seen_isin_imp
      and src_current_imp = src_current_imp and src_has_imp = src_has_imp
      and src_move_imp = src_move_imp
      and out_current_imp = out_current_imp
      and parent_lookup_imp = parent_lookup_imp and fst_imp = fst_imp
  for fst :: "'e::heap \<Rightarrow> 'v::heap"
    and target :: "'v \<Rightarrow> bool"
    and early_stop :: bool
    and dist_invar :: "'darr \<Rightarrow> bool"
    and dist_upd :: "'darr \<Rightarrow> 'v \<Rightarrow> real \<Rightarrow> 'darr"
    and dist_lookup :: "'darr \<Rightarrow> 'v \<Rightarrow> real"
    and parent_invar :: "'parr \<Rightarrow> bool"
    and parent_upd :: "'parr \<Rightarrow> 'v \<Rightarrow> 'e option \<Rightarrow> 'parr"
    and parent_lookup :: "'parr \<Rightarrow> 'v \<Rightarrow> 'e option"
    and queue_abstract :: "'queue \<Rightarrow> ('v \<times> real) set"
    and h :: "'n::{linordered_ab_group_add, heap} \<Rightarrow> real"
    and unreached :: 'n    and out_current_imp :: "'gi \<Rightarrow> 'v \<Rightarrow> 'e Heap"
    and out_assn
    and dist_assn
:: "'darr \<Rightarrow> 'di \<Rightarrow> assn"
    and dist_upd_imp :: "'di \<Rightarrow> 'v \<Rightarrow> 'n \<Rightarrow> unit Heap"
    and dist_lookup_imp :: "'di \<Rightarrow> 'v \<Rightarrow> 'n Heap"
    and parent_assn :: "'parr \<Rightarrow> 'pi \<Rightarrow> assn"
    and parent_upd_imp :: "'pi \<Rightarrow> 'v \<Rightarrow> 'e option \<Rightarrow> unit Heap"
    and parent_lookup_imp :: "'pi \<Rightarrow> 'v \<Rightarrow> 'e option Heap"
    and weight_invar :: "'warr \<Rightarrow> bool"
    and weight_upd :: "'warr \<Rightarrow> 'e \<Rightarrow> real \<Rightarrow> 'warr"
    and weight_lookup :: "'warr \<Rightarrow> 'e \<Rightarrow> real"
    and weight_assn :: "'warr \<Rightarrow> 'wi \<Rightarrow> assn"
    and weight_upd_imp :: "'wi \<Rightarrow> 'e \<Rightarrow> 'n \<Rightarrow> unit Heap"
    and weight_lookup_imp :: "'wi \<Rightarrow> 'e \<Rightarrow> 'n Heap"
    and seen_assn
    and seen_empty_imp :: "'si Heap"
    and seen_insert_imp :: "'v \<Rightarrow> 'si \<Rightarrow> unit Heap"
    and seen_delete_imp :: "'v \<Rightarrow> 'si \<Rightarrow> unit Heap"
    and seen_isin_imp :: "'si \<Rightarrow> 'v \<Rightarrow> bool Heap"
    and src_assn
    and src_current_imp :: "'srci \<Rightarrow> 'v Heap"
    and src_has_imp :: "'srci \<Rightarrow> bool Heap"
    and src_move_imp :: "'srci \<Rightarrow> unit Heap"
    and snd_imp :: "'ei \<Rightarrow> 'e \<Rightarrow> 'v Heap"
    and fst_imp :: "'ei \<Rightarrow> 'e \<Rightarrow> 'v Heap"
    and target_imp :: "'ti \<Rightarrow> 'v \<Rightarrow> bool Heap"
    and allowed :: "'v \<Rightarrow> 'v \<Rightarrow> 'e \<Rightarrow> real \<Rightarrow> bool"
    and allowed_imp :: "'ai \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'e \<Rightarrow> 'n \<Rightarrow> bool Heap" +
  fixes W :: 'warr
    and ends_assn :: "'ei \<Rightarrow> assn"
    and target_assn :: "'ti \<Rightarrow> assn"
    and allowed_assn :: "'ai \<Rightarrow> assn"
  assumes W_invar: "weight_invar W"
    and W_weights: "\<And>e. e \<in> \<E> \<Longrightarrow> weight_lookup W e = w e"
    and snd_imp_rule[sep_heap_rules]:
      "e \<in> \<E> \<Longrightarrow> <ends_assn Ei> snd_imp Ei e <\<lambda>v. ends_assn Ei * \<up>(v = snd e)>"
    and fst_imp_rule[sep_heap_rules]:
      "e \<in> \<E> \<Longrightarrow> <ends_assn Ei> fst_imp Ei e <\<lambda>u. ends_assn Ei * \<up>(u = fst e)>"
    and target_imp_rule[sep_heap_rules]:
      "v \<in> \<V> \<Longrightarrow> <target_assn Ti> target_imp Ti v <\<lambda>b. target_assn Ti * \<up>(b = target v)>"
    and allowed_imp_rule[sep_heap_rules]:
      "\<lbrakk>e \<in> \<E>; u = fst e; v = snd e; h we = w e\<rbrakk> \<Longrightarrow>
       <allowed_assn Ai> allowed_imp Ai u v e we <\<lambda>b. allowed_assn Ai * \<up>(b = allowed u v e (w e))>"
begin

text \<open>The functional state together with the weight array, the endpoints, the target test and
      the edge test is represented by the heap handles.\<close>

definition state_assn where
  "state_assn st si =
     dist_assn (dij_dist st) (dimp_dist si) *
     seen_assn (dij_seen st) (dimp_seen si) *
     parent_assn (dij_parent st) (dimp_parent si) *
     queue_assn (dij_heap st) (dimp_heap si) *
     out_assn (dij_graph st) (dimp_graph si) *
     src_assn (dij_srcs st) (dimp_srcs si) *
     weight_assn W (dimp_weight si) *
     ends_assn (dimp_ends si) *
     target_assn (dimp_target si) *
     allowed_assn (dimp_allowed si)"

text \<open>The scanned vertex and the found target are not stored in the heap, so they do not occur in
      the relation.\<close>

lemma state_assn_upd_curr[simp]: "state_assn (st\<lparr>dij_curr := c\<rparr>) si = state_assn st si"
  and state_assn_upd_target[simp]: "state_assn (st\<lparr>dij_target := t\<rparr>) si = state_assn st si"
  by (simp_all add: state_assn_def)


subsection \<open>Operations on the related state\<close>

text \<open>Following @{text DFS_Imperative}, we do not unfold the state assertion in the loop proof.
      Instead, every access of the loop to a component of the state is lifted to an operation on
      the related state: it preserves the relation, and a mutation moves the functional state to
      the one updated by the corresponding functional operation. Only these proofs unfold
      @{const state_assn}.\<close>

lemma weight_lookup_imp_rule:
  "e \<in> \<E> \<Longrightarrow> <weight_assn W Wi> weight_lookup_imp Wi e <\<lambda>x. weight_assn W Wi * \<up>(h x = w e)>"
  by (sep_auto simp: W_invar W_weights)

lemma snd_state[sep_heap_rules]:
  "e \<in> \<E> \<Longrightarrow>
   <state_assn st si> snd_imp (dimp_ends si) e <\<lambda>v. state_assn st si * \<up>(v = snd e)>"
  unfolding state_assn_def
  by sep_auto

lemma dist_lookup_state[sep_heap_rules]:
  "\<lbrakk>dist_invar (dij_dist st); u \<in> \<V>\<rbrakk> \<Longrightarrow>
   <state_assn st si> dist_lookup_imp (dimp_dist si) u
   <\<lambda>d. state_assn st si * \<up>(h d = dist_lookup (dij_dist st) u)>"
  unfolding state_assn_def
  by sep_auto

lemma out_has_state[sep_heap_rules]:
  "\<lbrakk>out_invar (dij_graph st); u \<in> \<V>\<rbrakk> \<Longrightarrow>
   <state_assn st si> out_has_imp (dimp_graph si) u
   <\<lambda>b. state_assn st si * \<up>(b = out_has (dij_graph st) u)>"
  unfolding state_assn_def
  by sep_auto

lemma out_current_state[sep_heap_rules]:
  "\<lbrakk>out_invar (dij_graph st); u \<in> \<V>; out_has (dij_graph st) u\<rbrakk> \<Longrightarrow>
   <state_assn st si> out_current_imp (dimp_graph si) u
   <\<lambda>e. state_assn st si * \<up>(e = out_current (dij_graph st) u)>"
  unfolding state_assn_def
  by (sep_auto simp: out_has_remaining)

lemma out_move_state[sep_heap_rules]:
  "\<lbrakk>out_invar (dij_graph st); u \<in> \<V>; out_has (dij_graph st) u\<rbrakk> \<Longrightarrow>
   <state_assn st si> out_move_imp (dimp_graph si) u
   <\<lambda>_. state_assn (st\<lparr>dij_graph := out_move (dij_graph st) u\<rparr>) si>"
  unfolding state_assn_def
  by (sep_auto simp: out_has_remaining)

lemma out_reset_state[sep_heap_rules]:
  "\<lbrakk>out_invar (dij_graph st); u \<in> \<V>\<rbrakk> \<Longrightarrow>
   <state_assn st si> out_reset_imp (dimp_graph si) u
   <\<lambda>_. state_assn (st\<lparr>dij_graph := out_reset (dij_graph st) u\<rparr>) si>"
  unfolding state_assn_def
  by sep_auto

lemma src_has_state[sep_heap_rules]:
  "src_invar (dij_srcs st) \<Longrightarrow>
   <state_assn st si> src_has_imp (dimp_srcs si)
   <\<lambda>b. state_assn st si * \<up>(b = src_has (dij_srcs st))>"
  unfolding state_assn_def
  by sep_auto

lemma src_current_state[sep_heap_rules]:
  "\<lbrakk>src_invar (dij_srcs st); src_has (dij_srcs st)\<rbrakk> \<Longrightarrow>
   <state_assn st si> src_current_imp (dimp_srcs si)
   <\<lambda>v. state_assn st si * \<up>(v = src_current (dij_srcs st))>"
  unfolding state_assn_def
  by (sep_auto simp: sources.has_current)

lemma src_move_state[sep_heap_rules]:
  "\<lbrakk>src_invar (dij_srcs st); src_has (dij_srcs st)\<rbrakk> \<Longrightarrow>
   <state_assn st si> src_move_imp (dimp_srcs si)
   <\<lambda>_. state_assn (st\<lparr>dij_srcs := src_move (dij_srcs st)\<rparr>) si>"
  unfolding state_assn_def
  by (sep_auto heap: src_imp.move_on_rule simp: sources.has_current[symmetric])

lemma extract_min_state[sep_heap_rules]:
  "queue_invar (dij_heap st) \<Longrightarrow>
   <state_assn st si> queue_extract_min_imp (dimp_heap si)
   <\<lambda>r. state_assn (st\<lparr>dij_heap := Product_Type.fst (queue_extract_min (dij_heap st))\<rparr>) si 
        * \<up>((case r of None \<Rightarrow> None | Some (v, k) \<Rightarrow> Some v) =
            prod.snd (queue_extract_min (dij_heap st)))>"
  unfolding state_assn_def
  by (sep_auto split: option.split)

lemma seen_isin_state[sep_heap_rules]:
  "\<lbrakk>seen_invar (dij_seen st); u \<in> \<V>\<rbrakk> \<Longrightarrow>
   <state_assn st si> seen_isin_imp (dimp_seen si) u
   <\<lambda>b. state_assn st si * \<up>(b = seen_isin (dij_seen st) u)>"
  unfolding state_assn_def
  by sep_auto

lemma seen_insert_state[sep_heap_rules]:
  "\<lbrakk>seen_invar (dij_seen st); u \<in> \<V>\<rbrakk> \<Longrightarrow>
   <state_assn st si> seen_insert_imp u (dimp_seen si)
   <\<lambda>_. state_assn (st\<lparr>dij_seen := seen_insert u (dij_seen st)\<rparr>) si>"
  unfolding state_assn_def
  by sep_auto

lemma target_test_state[sep_heap_rules]:
  "u \<in> \<V> \<Longrightarrow>
   <state_assn st si> target_test_imp si u <\<lambda>b. state_assn st si * \<up>(b = (early_stop \<and> target u))>"
  unfolding target_test_imp_def state_assn_def
  by sep_auto


subsection \<open>The single-edge operations\<close>

text \<open>Relaxing an edge preserves the relation. Its preconditions are those parts of the
      invariants that the Hoare triples of the accessed data structures demand; in particular the
      queue--distance coupling of @{const invar_2} decides between insertion and key decrease.\<close>

lemma relax_edge_imp_rule[sep_heap_rules]:
  assumes "dist_invar (dij_dist st)" "parent_invar (dij_parent st)" "invar_2 st" "e \<in> \<E>" "fst e = u"
  shows "<state_assn st si> relax_edge_imp si u du e
         <\<lambda>_. state_assn (relax_edge u (h du) e st) si>"
proof-
  have "queue_invar (dij_heap st)" "seen_invar (dij_seen st)" "snd e \<in> \<V>"
    "\<And>x k. (x, k) \<in> queue_abstract (dij_heap st) \<longleftrightarrow>
       x \<notin> seen_abstract (dij_seen st) \<and> dist_lookup (dij_dist st) x \<noteq> -1 \<and> k = dist_lookup (dij_dist st) x"
    using assms(3,4) snd_E_V
    by (auto elim!: invar_2_props)
  then show ?thesis
    using assms
    unfolding relax_edge_imp_def relax_edge_def state_assn_def Let_def allowed_edge_def
    by (sep_auto heap: weight_lookup_imp_rule dist_imp.fixed_univ_map_lookup_rule queue_imp.queue_decrease_key_rule
        simp: h_add h_less_iff[symmetric] seen_set.fixed_univ_set_isin)
qed

text \<open>Registering a source preserves the relation.\<close>

lemma insert_source_imp_rule[sep_heap_rules]:
  assumes "dist_invar (dij_dist st)" "invar_2 st" "v \<in> \<V>" "dist_lookup (dij_dist st) v = -1"
  shows "<state_assn st si> insert_source_imp si v
         <\<lambda>_. state_assn (insert_source v st) si>"
proof-
  have "queue_invar (dij_heap st)" "\<nexists>k. (v, k) \<in> queue_abstract (dij_heap st)"
    using assms(2,4)
    by (auto elim!: invar_2_props)
  then show ?thesis
    using assms
    unfolding insert_source_imp_def insert_source_def state_assn_def
    by sep_auto
qed



subsection \<open>The main loop\<close>

text \<open>The invariants of the functional algorithm that the loop needs: those guaranteeing the
      preconditions of all Hoare triples, and that no target has been found yet.\<close>

definition "dij_imp_invar st \<longleftrightarrow> invar_1 st \<and> invar_2 st \<and> invar_3 st \<and> invar_4 st \<and> invar_10 st"

lemma dij_imp_invar_step:
  "\<lbrakk>dij_imp_invar st; dijkstra_call_relax_conds st\<rbrakk> \<Longrightarrow> dij_imp_invar (dijkstra_upd_relax st)"
  "\<lbrakk>dij_imp_invar st; dijkstra_call_finish_conds st\<rbrakk> \<Longrightarrow> dij_imp_invar (dijkstra_upd_finish st)"
  "\<lbrakk>dij_imp_invar st; dijkstra_call_init_conds st\<rbrakk> \<Longrightarrow> dij_imp_invar (dijkstra_upd_init st)"
  "\<lbrakk>dij_imp_invar st; dijkstra_call_settle_conds st\<rbrakk> \<Longrightarrow> dij_imp_invar (dijkstra_upd_settle st)"
  unfolding dij_imp_invar_def
  by (auto intro: invar_holds_intros)

text \<open>One unfolding of the executable functional loop per branch.\<close>

lemma dijkstra_impl_step:
  "dijkstra_call_relax_conds st \<Longrightarrow> dijkstra_impl st = dijkstra_impl (dijkstra_upd_relax st)"
  "dijkstra_call_finish_conds st \<Longrightarrow> dijkstra_impl st = dijkstra_impl (dijkstra_upd_finish st)"
  "dijkstra_call_init_conds st \<Longrightarrow> dijkstra_impl st = dijkstra_impl (dijkstra_upd_init st)"
  "dijkstra_call_settle_conds st \<Longrightarrow> dijkstra_impl st = dijkstra_impl (dijkstra_upd_settle st)"
  "dijkstra_ret_done_conds st \<Longrightarrow> dijkstra_impl st = dijkstra_ret_done st"
  "dijkstra_ret_found_conds st \<Longrightarrow> dijkstra_impl st = dijkstra_ret_found st"
  by (subst dijkstra_impl.simps;
      auto simp: Let_def dijkstra_call_relax_conds_def dijkstra_upd_relax_def
                 dijkstra_call_finish_conds_def dijkstra_upd_finish_def
                 dijkstra_call_init_conds_def dijkstra_upd_init_def
                 dijkstra_call_settle_conds_def dijkstra_upd_settle_def
                 dijkstra_ret_done_conds_def dijkstra_ret_done_def
                 dijkstra_ret_found_conds_def dijkstra_ret_found_def
           split: option.splits prod.splits)+

text \<open>The imperative loop preserves the refinement relation: started on a state related to a
      functional state satisfying the invariants, it ends in a state related to the result of the
      executable functional loop @{const dijkstra_impl}, and returns its target. The proof is by
      fixpoint induction on the heap @{command partial_function}, as for the imperative DFS. Each
      branch of the functional loop is matched by the corresponding branch of the imperative one.\<close>

lemma dijkstra_loop_imp_rule:
  "dij_imp_invar st \<longrightarrow>
   <state_assn st si> dijkstra_loop_imp si (dij_curr st)
   <\<lambda>r. state_assn (dijkstra_impl st) si * \<up>(r = dij_target (dijkstra_impl st))>"
proof(induction arbitrary: st rule: dijkstra_loop_imp.fixp_induct)
  case (3 f)
  note IH = "3"[rule_format]
  let "?I \<longrightarrow> <?P> ?body <?Q>" = ?case
  show ?case
  proof(rule impI)
    assume I: "dij_imp_invar st"
    then have ds: "dist_invar (dij_dist st)" "parent_invar (dij_parent st)" "out_invar (dij_graph st)"
        "src_invar (dij_srcs st)" "queue_invar (dij_heap st)" "seen_invar (dij_seen st)"
        "dij_target st = None" "invar_2 (st\<lparr>dij_graph := g\<rparr>)" "invar_2 (st\<lparr>dij_srcs := x\<rparr>)"
        "dij_curr st = Some u \<Longrightarrow> u \<in> \<V>"
        "\<lbrakk>u \<in> \<V>; out_has (dij_graph st) u\<rbrakk> \<Longrightarrow>
           out_current (dij_graph st) u \<in> \<E> \<and> fst (out_current (dij_graph st) u) = u"
      for g x u
      by (auto simp: dij_imp_invar_def invar_2_def invar_10_def invar_1_ds out_current_edge out_current_fst)
    show "<?P> ?body <?Q>"
    proof(rule dijkstra_cases[of st])
      assume c: "dijkstra_call_relax_conds st"
      then obtain u where "dij_curr st = Some u" "out_has (dij_graph st) u"
        by (auto elim!: dijkstra_call_relax_condsE)
      moreover have IH': "<state_assn (relax_edge u (dist_lookup (dij_dist st) u) (out_current (dij_graph st) u)
                                (st\<lparr>dij_graph := out_move (dij_graph st) u\<rparr>)) si>
                 f si (Some u) <?Q>"
        using IH[OF dij_imp_invar_step(1)[OF I c]] calculation(1)
        unfolding dijkstra_impl_step(1)[OF c, symmetric]
        by (simp add: dijkstra_upd_relax_def)
      ultimately show ?thesis
        by (sep_auto heap: IH' simp: ds)
    next
      assume c: "dijkstra_call_finish_conds st"
      then obtain u where "dij_curr st = Some u" "\<not> out_has (dij_graph st) u"
        by (auto elim!: dijkstra_call_finish_condsE)
      moreover have IH': "<state_assn st si> f si None <?Q>"
        using IH[OF dij_imp_invar_step(2)[OF I c]]
        unfolding dijkstra_impl_step(2)[OF c, symmetric]
        by (simp add: dijkstra_upd_finish_def)
      ultimately show ?thesis
        by (sep_auto heap: IH' simp: ds)
    next
      assume c: "dijkstra_call_init_conds st"
      then have "dij_curr st = None" "src_has (dij_srcs st)"
          "src_current (dij_srcs st) \<in> src_remaining (dij_srcs st)"
        using ds(4) sources.has_current sources.current_element[OF ds(4)]
        by (auto elim!: dijkstra_call_init_condsE)
      moreover have "src_current (dij_srcs st) \<in> \<V>" "dist_lookup (dij_dist st) (src_current (dij_srcs st)) = -1"
        using I calculation(3) sources.iterable_set_abstract(2)[OF ds(4)]
        by (auto simp: dij_imp_invar_def elim!: invar_3_props)
      moreover have IH': "<state_assn (insert_source (src_current (dij_srcs st))
                                (st\<lparr>dij_srcs := src_move (dij_srcs st)\<rparr>)) si> f si None <?Q>"
        using IH[OF dij_imp_invar_step(3)[OF I c]] calculation(1)
        unfolding dijkstra_impl_step(3)[OF c, symmetric]
        by (simp add: dijkstra_upd_init_def)
      ultimately show ?thesis
        by (sep_auto heap: IH' simp: ds)
    next
      assume "dijkstra_call_skip_conds st"
      then show ?thesis
        using I
        by (auto simp: dij_imp_invar_def dest: skip_contra)
    next
      assume c: "dijkstra_call_settle_conds st"
      then obtain h2 u where "dij_curr st = None" "\<not> src_has (dij_srcs st)"
          "queue_extract_min (dij_heap st) = (h2, Some u)" "\<not> seen_isin (dij_seen st) u"
          "\<not> (early_stop \<and> target u)" "u \<in> \<V>"
        using heap.queue_extract_min_universe[OF ds(5)]
        by (auto elim!: dijkstra_call_settle_condsE)
      moreover have IH': "<state_assn (st\<lparr>dij_heap := h2, dij_seen := seen_insert u (dij_seen st),
                                  dij_graph := out_reset (dij_graph st) u\<rparr>) si> f si (Some u) <?Q>"
        using IH[OF dij_imp_invar_step(4)[OF I c]] calculation(3)
        unfolding dijkstra_impl_step(4)[OF c, symmetric]
        by (simp add: dijkstra_upd_settle_def state_assn_def)
      ultimately show ?thesis
        by (sep_auto heap: IH' simp: ds)
    next
      assume c: "dijkstra_ret_done_conds st"
      then obtain h2 where "dij_curr st = None" "\<not> src_has (dij_srcs st)"
          "queue_extract_min (dij_heap st) = (h2, None)"
        by (auto elim!: dijkstra_ret_done_condsE)
      then show ?thesis
        unfolding dijkstra_impl_step(5)[OF c] dijkstra_ret_done_def
        by (sep_auto simp: ds)
    next
      assume c: "dijkstra_ret_found_conds st"
      then obtain h2 u where found: "dij_curr st = None" "\<not> src_has (dij_srcs st)"
          "queue_extract_min (dij_heap st) = (h2, Some u)" "\<not> seen_isin (dij_seen st) u" early_stop
          "target u" "u \<in> \<V>"
        using heap.queue_extract_min_universe[OF ds(5)]
        by (auto elim!: dijkstra_ret_found_condsE)
      show ?thesis
        unfolding found(1) dijkstra_impl_step(6)[OF c] dijkstra_ret_found_def found(3) Let_def
        by (sep_auto simp: ds found)
    qed
  qed
qed simp_all


text \<open>Under the invariants the functional loop terminates, so the executable @{const dijkstra_impl}
      and the @{command function} @{const dijkstra}, about which the correctness theorems are
      stated, coincide.\<close>

lemma dijkstra_loop_imp_correct:
  assumes "dij_imp_invar st"
  shows "<state_assn st si> dijkstra_loop_imp si (dij_curr st)
         <\<lambda>r. state_assn (dijkstra st) si * \<up>(r = dij_target (dijkstra st))>"
  using dijkstra_loop_imp_rule[of st si] assms
  by (auto simp: dij_imp_invar_def dijkstra_impl_same dijkstra_terminates)

lemma dij_imp_invar_initial: "dij_imp_invar initial_state"
  using initial_state_props invar_10_initial
  by (simp add: dij_imp_invar_def)


subsection \<open>The whole algorithm\<close>

text \<open>Started on handles representing the initial state -- the distance array with all entries
      @{term unreached}, the empty seen set, the parent array with all entries @{const None}, the
      empty queue, the graph with all cursors at rest and the fresh source iterator -- the imperative
      program computes @{const dijkstra_compute}: afterwards the handles represent all its
      components. The result is the target found. The correctness theorems of @{locale dijkstra} about
      @{const dijkstra_compute} therefore carry over.\<close>

lemma dijkstra_imp_correct:
  "<state_assn (initial_state :: ('v, _, _, _, _, _, _) dij_state) si> dijkstra_imp si
   <\<lambda>r. state_assn dijkstra_compute si * \<up>(r = dij_target dijkstra_compute)>"
  using dijkstra_loop_imp_correct[OF dij_imp_invar_initial, of si]
  unfolding dijkstra_imp_def dijkstra_compute_def
  by (simp add: initial_state_def)

end


subsection \<open>Path reconstruction\<close>

text \<open>Going back from a vertex along the parent edges to a source, @{const dijkstra.reconstruct_path}
      reads off the path found. On the final state the targets of its edges are distinct, so it has
      at most @{term "card \<V>"} edges.\<close>


context dijkstra
begin

lemma parent_compute_induct[case_names root edge]:
  assumes "\<And>v. parent_lookup (dij_parent dijkstra_compute) v = None \<Longrightarrow> P v"
    "\<And>v e. \<lbrakk>parent_lookup (dij_parent dijkstra_compute) v = Some e; P (fst e)\<rbrakk> \<Longrightarrow> P v"
  shows "P v"
proof(induction v rule: wf_induct_rule[OF dijkstra_compute_parent_wf])
  case (1 v)
  then show ?case
    by (cases "parent_lookup (dij_parent dijkstra_compute) v") (auto simp: par_rel_def intro: assms)
qed

lemma build_path_compute_app:
  "build_path dijkstra_compute v acc = reconstruct_path dijkstra_compute v @ acc"
proof(induction v arbitrary: acc rule: parent_compute_induct)
  case (edge v e)
  show ?case
    using edge(1) edge(2)[of "e # acc"] edge(2)[of "[e]"]
    unfolding reconstruct_path_def
    by (subst (1 2) build_path.simps) simp
qed (simp add: reconstruct_path_def build_path.simps)

lemma reconstruct_path_compute_simps:
  "reconstruct_path dijkstra_compute v =
     (case parent_lookup (dij_parent dijkstra_compute) v of
        None \<Rightarrow> []
      | Some e \<Rightarrow> reconstruct_path dijkstra_compute (fst e) @ [e])"
  unfolding reconstruct_path_def
  by (subst build_path.simps)
    (simp add: build_path_compute_app[unfolded reconstruct_path_def, symmetric] split: option.split)

lemma reconstruct_path_compute_anc:
  "e' \<in> set (reconstruct_path dijkstra_compute v) \<Longrightarrow> (snd e', v) \<in> (par_rel dijkstra_compute)\<^sup>*"
proof(induction v rule: parent_compute_induct)
  case (edge v e)
  then show ?case
    using invar_tree_D[OF invar_tree_compute edge(1)] reconstruct_path_compute_simps[of v]
    by (auto simp: par_rel_def intro: rtrancl_into_rtrancl)
qed (simp add: reconstruct_path_compute_simps)

lemma reconstruct_path_compute_distinct:
  "distinct (map snd (reconstruct_path dijkstra_compute v))"
proof(induction v rule: parent_compute_induct)
  case (edge v e)
  have "(v, v) \<notin> (par_rel dijkstra_compute)\<^sup>+"
    using wf_acyclic[OF dijkstra_compute_parent_wf]
    by (simp add: acyclic_def)
  moreover have "(fst e, v) \<in> par_rel dijkstra_compute"
    using edge(1)
    by (auto simp: par_rel_def)
  ultimately have "v \<notin> snd ` set (reconstruct_path dijkstra_compute (fst e))"
    using reconstruct_path_compute_anc
    by (blast intro: rtrancl_into_trancl1)
  then show ?case
    using edge invar_tree_D[OF invar_tree_compute edge(1)] reconstruct_path_compute_simps[of v]
    by simp
qed (simp add: reconstruct_path_compute_simps)

lemma reconstruct_path_compute_edges: "set (reconstruct_path dijkstra_compute v) \<subseteq> \<E>"
proof(induction v rule: parent_compute_induct)
  case (edge v e)
  then show ?case
    using invar_tree_D[OF invar_tree_compute edge(1)] reconstruct_path_compute_simps[of v]
    by simp
qed (simp add: reconstruct_path_compute_simps)

lemma reconstruct_path_compute_length: "length (reconstruct_path dijkstra_compute v) \<le> card \<V>"
proof-
  have "snd ` set (reconstruct_path dijkstra_compute v) \<subseteq> \<V>"
    using reconstruct_path_compute_edges snd_E_V
    by fastforce
  then show ?thesis
    using distinct_card[OF reconstruct_path_compute_distinct[of v]]
    by (auto dest!: card_mono[OF \<V>_finite])
qed

text \<open>Without early stopping, no target is recorded. If none is recorded, the run ended with an
      empty queue, and every reached vertex and every vertex reachable from a source is settled.\<close>

lemma target_none_compute: assumes "\<not> early_stop" shows "dij_target dijkstra_compute = None"
  using target_none_run[OF initial_state_props(5) assms invar_10_initial, folded dijkstra_compute_def]
  by (auto elim!: invar_10_props)

lemma terminal_compute:
  assumes "dij_target dijkstra_compute = None"
  shows "queue_abstract (dij_heap dijkstra_compute) = {}" "dij_curr dijkstra_compute = None"
    "src_remaining (dij_srcs dijkstra_compute) = {}"
  using dijkstra_terminal[OF initial_state_props(5) initial_state_props(1-4), folded dijkstra_compute_def]
    assms
  by (auto simp: terminal_state_def)

lemma dijkstra_compute_reached_seen:
  assumes "dij_target dijkstra_compute = None" "dist_lookup (dij_dist dijkstra_compute) v \<noteq> -1"
  shows "v \<in> seen_abstract (dij_seen dijkstra_compute)"
  using invar_2_compute terminal_compute(1)[OF assms(1)] assms(2)
  by (auto elim!: invar_2_props)

lemma dijkstra_compute_reach_seen:
  assumes "dij_target dijkstra_compute = None" "s \<in> src_abstract srcs" "ag.reachable s v"
  shows "v \<in> seen_abstract (dij_seen dijkstra_compute)"
proof-
  have "dist_lookup (dij_dist dijkstra_compute) s = 0"
    using invar_9_compute assms(2) terminal_compute(3)[OF assms(1)]
    by (auto elim!: invar_9_props)
  then have "s \<in> seen_abstract (dij_seen dijkstra_compute)"
    using dijkstra_compute_reached_seen[OF assms(1)]
    by simp
  moreover obtain p where "ag.path_bet p s v"
    using assms(3) ag_reachable_iff_path
    by blast
  ultimately show ?thesis
    using reach_settled[OF terminal_compute(1,2)[OF assms(1)] assms(1) invar_1_compute
        invar_2_compute invar_7_compute invar_8_compute]
    by blast
qed 

subsection \<open>The shortest-path tree\<close>

text \<open>The edges of the parent map are tight: the parent edge of \<open>v\<close> is an allowed edge leaving a
      vertex reachable from a source, and the distance of \<open>v\<close> is the distance of that vertex plus
      the weight of the edge.\<close>

definition "tight_parents P \<longleftrightarrow> (\<forall>v e. parent_lookup P v = Some e \<longrightarrow>
   e \<in> Ea \<and> snd e = v \<and> (\<exists>s \<in> src_abstract srcs. ag.reachable s (fst e)) \<and>
   ag.distance_set w (src_abstract srcs) v = ag.distance_set w (src_abstract srcs) (fst e) + ereal (w e))"

lemma dijkstra_compute_tight_parents:
  assumes "\<not> early_stop"
  shows "tight_parents (dij_parent dijkstra_compute)"
  unfolding tight_parents_def
proof(intro allI impI)
  fix v e
  let ?d = "dist_lookup (dij_dist dijkstra_compute)"
  assume "parent_lookup (dij_parent dijkstra_compute) v = Some e"
  then have t: "fst e \<in> seen_abstract (dij_seen dijkstra_compute)" "snd e = v" "e \<in> Ea"
      "?d (fst e) \<noteq> -1" "?d v = ?d (fst e) + w e"
    using invar_tree_D[OF invar_tree_compute]
    by blast+
  have "0 \<le> ?d (fst e) + w e"
    using invar_3_compute t(3,4) w_nonneg
    by (auto elim!: invar_3_props intro!: add_nonneg_nonneg)
  then have "?d v \<noteq> -1"
    using t(5)
    by linarith
  then show "e \<in> Ea \<and> snd e = v \<and> (\<exists>s \<in> src_abstract srcs. ag.reachable s (fst e)) \<and>
      ag.distance_set w (src_abstract srcs) v = ag.distance_set w (src_abstract srcs) (fst e) + ereal (w e)"
    using t dijkstra_compute_optimal[symmetric] dijkstra_compute_complete[OF assms, THEN iffD1]
      dijkstra_compute_reached_seen[OF target_none_compute[OF assms]]
    by auto
qed

subsection \<open>The target found by early stopping\<close>

text \<open>A recorded target is a target, it is settled, and no target is closer to the sources. As long
      as early stopping has recorded no target, no settled vertex is a target.\<close>

definition "invar_tgt st \<longleftrightarrow> (case dij_target st of
     Some u \<Rightarrow> target u \<and> u \<in> seen_abstract (dij_seen st) \<and>
       (\<forall>x. target x \<longrightarrow> ag.distance_set w (src_abstract srcs) u \<le> ag.distance_set w (src_abstract srcs) x)
   | None \<Rightarrow> early_stop \<longrightarrow> (\<forall>x \<in> seen_abstract (dij_seen st). \<not> target x))"

lemma invar_tgt_steps:
  "\<lbrakk>dijkstra_call_relax_conds st; invar_tgt st\<rbrakk> \<Longrightarrow> invar_tgt (dijkstra_upd_relax st)"
  "\<lbrakk>dijkstra_call_finish_conds st; invar_tgt st\<rbrakk> \<Longrightarrow> invar_tgt (dijkstra_upd_finish st)"
  "\<lbrakk>dijkstra_call_init_conds st; invar_tgt st\<rbrakk> \<Longrightarrow> invar_tgt (dijkstra_upd_init st)"
  "\<lbrakk>dijkstra_call_skip_conds st; invar_tgt st\<rbrakk> \<Longrightarrow> invar_tgt (dijkstra_upd_skip st)"
  "\<lbrakk>dijkstra_ret_done_conds st; invar_tgt st\<rbrakk> \<Longrightarrow> invar_tgt (dijkstra_ret_done st)"
  by (auto simp: invar_tgt_def dijkstra_upd_relax_def dijkstra_upd_finish_def dijkstra_upd_init_def
      dijkstra_upd_skip_def dijkstra_ret_done_def Let_def split: prod.splits option.splits)

lemma invar_tgt_settle:
  "\<lbrakk>dijkstra_call_settle_conds st; invar_2 st; invar_tgt st\<rbrakk> \<Longrightarrow> invar_tgt (dijkstra_upd_settle st)"
  by (erule dijkstra_call_settle_condsE, frule popped_vertex)
     (auto simp: invar_tgt_def dijkstra_upd_settle_def dijkstra_ds_simps split: option.splits)

text \<open>When early stopping returns the extracted \<open>u\<close>, no settled vertex is a target, so every other
      target is unsettled, and by @{thm settle_opt_bound} it is not closer than \<open>u\<close>.\<close>

lemma invar_tgt_found:
  assumes "dijkstra_ret_found_conds st" "invar_1 st" "invar_2 st" "invar_5 st" "invar_7 st"
    "invar_8 st" "invar_9 st" "invar_10 st" "invar_opt st" "invar_tgt st"
  shows "invar_tgt (dijkstra_ret_found st)"
proof-
  obtain h2 u where hu: "dij_curr st = None" "\<not> src_has (dij_srcs st)"
      "queue_extract_min (dij_heap st) = (h2, Some u)" "early_stop" "target u"
    using assms(1)
    by (auto elim!: dijkstra_ret_found_condsE)
  have "\<forall>x \<in> seen_abstract (dij_seen st). \<not> target x"
    using assms(10)[unfolded invar_tgt_def] assms(8)[unfolded invar_10_def] hu(4)
    by simp
  moreover have "ag.distance_set w (src_abstract srcs) u \<le> ereal (dist_lookup (dij_dist st) u)"
    using assms(4) popped_vertex[OF hu(3) assms(3)]
    by (auto elim!: invar_5_props)
  ultimately have "ag.distance_set w (src_abstract srcs) u \<le> ag.distance_set w (src_abstract srcs) x"
    if "target x" for x
    using order_trans settle_opt_bound[OF hu(1-3) assms(2-9)] that
    by blast
  thus ?thesis
    using hu(3,5) popped_vertex[OF hu(3) assms(3)] assms(3)
    by (auto simp: invar_tgt_def dijkstra_ret_found_def dijkstra_ds_simps)
qed

lemma invar_tgt_holds:
  assumes "dijkstra_dom st" "invar_1 st" "invar_2 st" "invar_3 st" "invar_4 st" "invar_5 st"
    "invar_6 st" "invar_7 st" "invar_8 st" "invar_9 st" "invar_10 st" "invar_opt st" "invar_tgt st"
  shows "invar_tgt (dijkstra st)"
  using assms(2-)
proof(induction rule: dijkstra_induct[OF assms(1)])
  case IH: (1 st)
  show ?case
    apply(rule dijkstra_cases[where st = st])
    by (auto intro!: IH(2-) intro: invar_holds_intros invar_tgt_steps invar_tgt_settle invar_tgt_found
        simp: dijkstra_simps[OF IH(1)])
qed

lemma invar_tgt_compute: "invar_tgt dijkstra_compute"
  unfolding dijkstra_compute_def
  by (rule invar_tgt_holds[OF initial_state_props(5) initial_state_props(1) initial_state_props(2)
        initial_state_props(3) initial_state_props(4) invar_5_initial invar_6_initial invar_7_initial
        invar_8_initial invar_9_initial invar_10_initial invar_opt_initial])
    (simp add: invar_tgt_def initial_state_def seen_set.fixed_univ_set_empty(2))

text \<open>A target found by early stopping is a reached target, its distance is the shortest distance,
      and no target is closer to the sources.\<close>

lemma dijkstra_compute_target:
  assumes "dij_target dijkstra_compute = Some u"
  shows "target u \<and> u \<in> \<V> \<and> dist_lookup (dij_dist dijkstra_compute) u \<noteq> -1 \<and>
         ereal (dist_lookup (dij_dist dijkstra_compute) u) = ag.distance_set w (src_abstract srcs) u \<and>
         (\<forall>x. target x \<longrightarrow> ag.distance_set w (src_abstract srcs) u \<le> ag.distance_set w (src_abstract srcs) x)"
proof-
  have s: "target u" "u \<in> seen_abstract (dij_seen dijkstra_compute)"
      "\<forall>x. target x \<longrightarrow> ag.distance_set w (src_abstract srcs) u \<le> ag.distance_set w (src_abstract srcs) x"
    using invar_tgt_compute assms
    by (auto simp: invar_tgt_def)
  have "u \<in> \<V>"
    using invar_2_compute s(2)
    by (auto elim!: invar_2_props)
  moreover have "dist_lookup (dij_dist dijkstra_compute) u \<noteq> -1"
    using invar_8_compute s(2)
    by (auto elim!: invar_8_props)
  ultimately show ?thesis
    using s dijkstra_compute_optimal[OF s(2)]
    by blast
qed

text \<open>If early stopping finds no target, no target is reachable from a source.\<close>

lemma dijkstra_compute_no_target:
  assumes "early_stop" "dij_target dijkstra_compute = None" "target v"
  shows "\<forall>s \<in> src_abstract srcs. \<not> ag.reachable s v"
  using invar_tgt_compute[unfolded invar_tgt_def assms(2)] dijkstra_compute_reach_seen[OF assms(2)]
    assms(1,3)
  by auto

text \<open>The path reconstructed to a settled vertex is a simple shortest path from the sources, hence a
      shortest path between its source and the vertex.\<close>

lemma reconstruct_path_shortest:
  assumes "v \<in> seen_abstract (dij_seen dijkstra_compute)"
  shows "\<exists>s \<in> src_abstract srcs. ag.path_bet (reconstruct_path dijkstra_compute v) s v \<and>
     distinct (reconstruct_path dijkstra_compute v) \<and>
     ereal (weight w (reconstruct_path dijkstra_compute v)) = ag.distance_set w (src_abstract srcs) v \<and>
     ereal (weight w (reconstruct_path dijkstra_compute v)) = ag.distance w s v"
proof-
  have "dist_lookup (dij_dist dijkstra_compute) v \<noteq> -1"
    using invar_8_compute assms
    by (auto elim!: invar_8_props)
  then obtain s where s: "s \<in> src_abstract srcs" "ag.path_bet (reconstruct_path dijkstra_compute v) s v"
      "weight w (reconstruct_path dijkstra_compute v) = dist_lookup (dij_dist dijkstra_compute) v"
    using dijkstra_compute_path
    by blast
  have d: "distinct (reconstruct_path dijkstra_compute v)"
    using reconstruct_path_compute_distinct[of v]
    by (simp add: distinct_map)
  have e: "ereal (weight w (reconstruct_path dijkstra_compute v)) = ag.distance_set w (src_abstract srcs) v"
    using s(3) dijkstra_compute_optimal[OF assms]
    by simp
  show ?thesis
    using s d e ag_distance_set_path_shortest[OF s(1,2) d e]
    by blast
qed

text \<open>The path reconstructed to the target found by early stopping is no heavier than any simple
      path from a source to a target.\<close>

lemma reconstruct_path_target:
  assumes "dij_target dijkstra_compute = Some u" "s \<in> src_abstract srcs" "target x"
    "ag.path_bet q s x" "distinct q"
  shows "weight w (reconstruct_path dijkstra_compute u) \<le> weight w q"
proof-
  have "u \<in> seen_abstract (dij_seen dijkstra_compute)"
    using invar_tgt_compute assms(1)
    by (simp add: invar_tgt_def)
  then have "ereal (weight w (reconstruct_path dijkstra_compute u)) = ag.distance_set w (src_abstract srcs) u"
    using reconstruct_path_shortest
    by blast
  then show ?thesis
    by (intro ag_distance_set_path_le_targets[of "Collect target"])
      (use dijkstra_compute_target[OF assms(1)] assms in auto)
qed
end

text \<open>The imperative path reconstruction @{const dijkstra_impl_spec.path_imp} refines
      @{const dijkstra.reconstruct_path} on the final state. It only reads the parent array.\<close>

context dijkstra_impl_refine
begin

lemma parent_invar_compute: "parent_invar (dij_parent dijkstra_compute)"
  using invar_1_compute
  by (simp add: invar_1_def)

lemma path_rev_imp_rule:
  "\<lbrakk>v \<in> \<V>; k + length (reconstruct_path dijkstra_compute v) \<le> length r\<rbrakk> \<Longrightarrow>
   <ends_assn Ei * parent_assn (dij_parent dijkstra_compute) Pa * Ra \<mapsto>\<^sub>a r> path_rev_imp Ei Pa Ra v k
   <\<lambda>k'. ends_assn Ei * parent_assn (dij_parent dijkstra_compute) Pa *
        Ra \<mapsto>\<^sub>a (take k r @ rev (reconstruct_path dijkstra_compute v) @
                 drop (k + length (reconstruct_path dijkstra_compute v)) r) *
        \<up>(k' = k + length (reconstruct_path dijkstra_compute v))>"
proof(induction v arbitrary: k r rule: parent_compute_induct)
  case (root v)
  then show ?case
    by (subst path_rev_imp.simps) (sep_auto simp: parent_invar_compute reconstruct_path_compute_simps)
next
  case (edge v e)
  have "e \<in> \<E>" "reconstruct_path dijkstra_compute v = reconstruct_path dijkstra_compute (fst e) @ [e]"
    using edge(1) invar_tree_D[OF invar_tree_compute edge(1)] reconstruct_path_compute_simps[of v]
    by auto
  then show ?case
    using edge.prems
    by (subst path_rev_imp.simps)
      (sep_auto simp: edge(1) parent_invar_compute fst_E_V take_Suc_conv_app_nth
        list_update_append heap: edge(2))
qed

text \<open>Given the final state and an array of at least @{term "card \<V>"} cells,
      @{const dijkstra_impl_spec.path_imp} writes the reconstructed path to @{term v}, reversed,
      into the first cells of the array and returns its length. If @{term v} was reached, this is
      a path from a source whose weight is the distance computed.\<close>

lemma path_imp_correct:
  assumes "v \<in> \<V>" "card \<V> \<le> length r"
  shows "<state_assn dijkstra_compute si * Ra \<mapsto>\<^sub>a r> path_imp si Ra v
         <\<lambda>k. state_assn dijkstra_compute si * (\<exists>\<^sub>Ap. Ra \<mapsto>\<^sub>a p * \<up>(length p = length r \<and>
            k = length (reconstruct_path dijkstra_compute v) \<and>
            rev (take k p) = reconstruct_path dijkstra_compute v \<and>
            (dist_lookup (dij_dist dijkstra_compute) v \<noteq> -1 \<longrightarrow>
              (\<exists>s \<in> src_abstract srcs. ag.path_bet (rev (take k p)) s v \<and>
                 weight w (rev (take k p)) = dist_lookup (dij_dist dijkstra_compute) v))))>"
proof-
  have b: "length (reconstruct_path dijkstra_compute v) \<le> length r"
    using reconstruct_path_compute_length[of v] assms(2)
    by linarith
  have pth: "dist_lookup (dij_dist dijkstra_compute) v \<noteq> -1 \<longrightarrow>
      (\<exists>s \<in> src_abstract srcs. ag.path_bet (reconstruct_path dijkstra_compute v) s v \<and>
         weight w (reconstruct_path dijkstra_compute v) = dist_lookup (dij_dist dijkstra_compute) v)"
    using dijkstra_compute_path
    by blast
  have t: "<state_assn dijkstra_compute si * Ra \<mapsto>\<^sub>a r> path_imp si Ra v
           <\<lambda>k. state_assn dijkstra_compute si *
                Ra \<mapsto>\<^sub>a (rev (reconstruct_path dijkstra_compute v) @
                         drop (length (reconstruct_path dijkstra_compute v)) r) *
                \<up>(k = length (reconstruct_path dijkstra_compute v))>"
    unfolding path_imp_def state_assn_def
    using assms(1) b
    by (sep_auto heap: path_rev_imp_rule[where k = 0, simplified])
  have g: "P L m \<Longrightarrow> X * Ra \<mapsto>\<^sub>a L * \<up>(k = m) \<Longrightarrow>\<^sub>A X * (\<exists>\<^sub>Ap. Ra \<mapsto>\<^sub>a p * \<up>(P p k)) * true"
    for X L m k and P :: "'e list \<Rightarrow> nat \<Rightarrow> bool"
    by sep_auto
  show ?thesis
    by (rule ht_cons[OF ent_refl g t]) (use b pth in auto)
qed

text \<open>Without early stopping, the parent array of the final state is a tree of tight edges.\<close>

lemma dijkstra_imp_tight_parents:
  assumes "\<not> early_stop"
  shows "<state_assn (initial_state :: ('v, _, _, _, _, _, _) dij_state) si> dijkstra_imp si
         <\<lambda>_. state_assn dijkstra_compute si * \<up>(tight_parents (dij_parent dijkstra_compute))>"
proof-
  have g: "c \<Longrightarrow> X * \<up>(r = T) \<Longrightarrow>\<^sub>A X * \<up>c * true" for X c and r T :: "'v option"
    by sep_auto
  show ?thesis
    by (rule ht_cons[OF ent_refl g dijkstra_imp_correct]) (rule dijkstra_compute_tight_parents[OF assms])
qed

text \<open>A target returned by early stopping is a reached target with the shortest distance, and no
      target is closer to the sources. If early stopping returns none, no target is reachable.\<close>

lemma dijkstra_imp_target:
  "<state_assn (initial_state :: ('v, _, _, _, _, _, _) dij_state) si> dijkstra_imp si
   <\<lambda>r. state_assn dijkstra_compute si * \<up>(r = dij_target dijkstra_compute \<and>
      (\<forall>u. r = Some u \<longrightarrow> target u \<and> u \<in> \<V> \<and> dist_lookup (dij_dist dijkstra_compute) u \<noteq> -1 \<and>
         ereal (dist_lookup (dij_dist dijkstra_compute) u) = ag.distance_set w (src_abstract srcs) u \<and>
         (\<forall>x. target x \<longrightarrow> ag.distance_set w (src_abstract srcs) u \<le> ag.distance_set w (src_abstract srcs) x)) \<and>
      (r = None \<longrightarrow> early_stop \<longrightarrow> (\<forall>v. target v \<longrightarrow> (\<forall>s \<in> src_abstract srcs. \<not> ag.reachable s v))))>"
proof-
  have g: "P T \<Longrightarrow> X * \<up>(r = T) \<Longrightarrow>\<^sub>A X * \<up>(r = T \<and> P r) * true"
    for X and r T :: "'v option" and P
    by sep_auto
  show ?thesis
    by (rule ht_cons[OF ent_refl g dijkstra_imp_correct])
      (use dijkstra_compute_target dijkstra_compute_no_target in blast)
qed

text \<open>For the target found, @{const dijkstra_impl_spec.path_imp} gives a simple shortest path from
      the sources, which is a shortest path between its source and the target, and no simple path
      from a source to a target is shorter.\<close>

lemma path_imp_target:
  assumes "dij_target dijkstra_compute = Some u" "card \<V> \<le> length r"
  shows "<state_assn dijkstra_compute si * Ra \<mapsto>\<^sub>a r> path_imp si Ra u
         <\<lambda>k. state_assn dijkstra_compute si * (\<exists>\<^sub>Ap. Ra \<mapsto>\<^sub>a p * \<up>(length p = length r \<and>
            k = length (reconstruct_path dijkstra_compute u) \<and> target u \<and>
            (\<exists>s \<in> src_abstract srcs. ag.path_bet (rev (take k p)) s u \<and> distinct (rev (take k p)) \<and>
               ereal (weight w (rev (take k p))) = ag.distance_set w (src_abstract srcs) u \<and>
               ereal (weight w (rev (take k p))) = ag.distance w s u) \<and>
            (\<forall>s \<in> src_abstract srcs. \<forall>x q. target x \<longrightarrow> ag.path_bet q s x \<longrightarrow> distinct q \<longrightarrow>
               weight w (rev (take k p)) \<le> weight w q)))>"
proof-
  have tu: "target u" "u \<in> \<V>"
    using dijkstra_compute_target[OF assms(1)]
    by blast+
  have us: "u \<in> seen_abstract (dij_seen dijkstra_compute)"
    using invar_tgt_compute assms(1)
    by (simp add: invar_tgt_def)
  have g: "(\<And>p. A p \<Longrightarrow> B p) \<Longrightarrow>
           X * (\<exists>\<^sub>Ap. Ra \<mapsto>\<^sub>a p * \<up>(A p)) \<Longrightarrow>\<^sub>A X * (\<exists>\<^sub>Ap. Ra \<mapsto>\<^sub>a p * \<up>(B p)) * true"
    for X and A B :: "'e list \<Rightarrow> bool"
    by sep_auto
  show ?thesis
    by (rule ht_cons[OF ent_refl _ path_imp_correct[OF tu(2) assms(2)]], rule g)
      (use tu reconstruct_path_shortest[OF us] reconstruct_path_target[OF assms(1)] in
        \<open>auto simp del: distinct_rev\<close>)
qed

end
end


