theory Dijkstra
  imports Directed_Set_Graphs.Multigraph_Weighted_Paths
          Directed_Set_Graphs.Edge_Iterators
          Data_Structures.Fixed_Univ_Key_Value_Queue_Specs
          Data_Structures.Fixed_Univ_Map_Specs Data_Structures.Fixed_Univ_Set_Specs
begin

section \<open>Dijkstra's Shortest-Path Algorithm\<close>

section \<open>The Program State\<close>

text \<open>The mutable state carried through the computation: the tentative-distance array (a real per
      vertex, \<open>-1\<close> meaning \<open>\<infinity>\<close>), the settled (\<^emph>\<open>seen\<close>) set, the shortest-path-tree parent array
      (mapping each reached vertex to the edge by which it was reached), the priority queue, the
      graph collection (whose per-vertex edge cursor is advanced as neighbours are relaxed), the
      target found (if any), the vertex currently being scanned, and the remaining sources still to
      be loaded.\<close>

record ('v, 'g, 'darr, 'sset, 'parr, 'queue, 'src) dij_state =
  dij_dist   :: 'darr
  dij_seen   :: 'sset
  dij_parent :: 'parr
  dij_heap   :: 'queue
  dij_graph  :: 'g
  dij_target :: "'v option"
  dij_curr   :: "'v option"
  dij_srcs   :: 'src


subsection \<open>Setup for automation\<close>

named_theorems call_cond_elims
named_theorems call_cond_intros
named_theorems ret_holds_intros
named_theorems invar_props_intros
named_theorems invar_props_elims
named_theorems invar_holds_intros

subsection \<open>The Locale fixing the data structures\<close>

text \<open>The algorithm is parameterised over: the graph as an outgoing-edge iterator; three
      fixed-universe collections (distance array, parent array over \<open>\<V>\<close>, and the seen set); the
      source set as an @{locale iterable_set}; and the key--value priority queue. In addition it
      fixes the non-negative weight function @{term w}, the target predicate @{term target}, the
      edge predicate @{term allowed}, the early-stopping flag @{term early_stop}, and the initial
      (empty) distance and parent arrays (all distances \<open>-1\<close>, all parents @{term None}).\<close>

locale dijkstra =
  multigraph where fst = fst +
  outgoing_edge_iterator where fst = fst
      and out_invar = out_invar and out_abstract = out_abstract
      and out_current = out_current and out_has = out_has
      and out_iterated = out_iterated and out_remaining = out_remaining
      and out_move = out_move and out_reset = out_reset +
  dist_arr: fixed_univ_map where K = \<V>
      and fixed_univ_map_invar = dist_invar
      and fixed_univ_map_upd = dist_upd
      and fixed_univ_map_lookup = dist_lookup +
  parent_arr: fixed_univ_map where K = \<V>
      and fixed_univ_map_invar = parent_invar
      and fixed_univ_map_upd = parent_upd
      and fixed_univ_map_lookup = parent_lookup +
  seen_set: fixed_univ_set where U = \<V>
      and fixed_univ_set_invar = seen_invar and fixed_univ_set_abstract = seen_abstract
      and fixed_univ_set_empty = seen_empty and fixed_univ_set_insert = seen_insert
      and fixed_univ_set_delete = seen_delete and fixed_univ_set_isin = seen_isin +
  sources: iterable_set where
      iterable_set_invar = src_invar and iterable_set_abstract = src_abstract
      and current_element = src_current and has_current = src_has
      and iterated = src_iterated and remaining = src_remaining and move_on = src_move +
  heap: key_value_queue where U = \<V> and queue_empty = queue_empty
      and queue_extract_min = queue_extract_min and queue_decrease_key = queue_decrease_key
      and queue_insert = queue_insert and queue_invar = queue_invar
      and queue_abstract = queue_abstract
  for fst :: "'e \<Rightarrow> 'v"
  and out_invar :: "'g \<Rightarrow> bool" and out_abstract :: "'g \<Rightarrow> 'v \<Rightarrow> 'e set"
  and out_current :: "'g \<Rightarrow> 'v \<Rightarrow> 'e" and out_has :: "'g \<Rightarrow> 'v \<Rightarrow> bool"
  and out_iterated :: "'g \<Rightarrow> 'v \<Rightarrow> 'e set" and out_remaining :: "'g \<Rightarrow> 'v \<Rightarrow> 'e set"
  and out_move :: "'g \<Rightarrow> 'v \<Rightarrow> 'g" and out_reset :: "'g \<Rightarrow> 'v \<Rightarrow> 'g"
  and dist_invar :: "'darr \<Rightarrow> bool"
  and dist_upd :: "'darr \<Rightarrow> 'v \<Rightarrow> real \<Rightarrow> 'darr"
  and dist_lookup :: "'darr \<Rightarrow> 'v \<Rightarrow> real"
  and parent_invar :: "'parr \<Rightarrow> bool"
  and parent_upd :: "'parr \<Rightarrow> 'v \<Rightarrow> 'e option \<Rightarrow> 'parr"
  and parent_lookup :: "'parr \<Rightarrow> 'v \<Rightarrow> 'e option"
  and seen_invar :: "'sset \<Rightarrow> bool" and seen_abstract :: "'sset \<Rightarrow> 'v set"
  and seen_empty :: "'sset" and seen_insert :: "'v \<Rightarrow> 'sset \<Rightarrow> 'sset"
  and seen_delete :: "'v \<Rightarrow> 'sset \<Rightarrow> 'sset" and seen_isin :: "'sset \<Rightarrow> 'v \<Rightarrow> bool"
  and src_invar :: "'src \<Rightarrow> bool" and src_abstract :: "'src \<Rightarrow> 'v set"
  and src_current :: "'src \<Rightarrow> 'v" and src_has :: "'src \<Rightarrow> bool"
  and src_iterated :: "'src \<Rightarrow> 'v set" and src_remaining :: "'src \<Rightarrow> 'v set"
  and src_move :: "'src \<Rightarrow> 'src"
  and queue_empty :: "'queue"
  and queue_extract_min :: "'queue \<Rightarrow> ('queue \<times> 'v option)"
  and queue_decrease_key :: "'queue \<Rightarrow> 'v \<Rightarrow> real \<Rightarrow> 'queue"
  and queue_insert :: "'queue \<Rightarrow> 'v \<Rightarrow> real \<Rightarrow> 'queue"
  and queue_invar :: "'queue \<Rightarrow> bool"
  and queue_abstract :: "'queue \<Rightarrow> ('v \<times> real) set" +
  fixes og :: "'g"
    and srcs :: "'src"
    and w :: "'e \<Rightarrow> real"
    and target :: "'v \<Rightarrow> bool"
    and allowed :: "'v \<Rightarrow> 'v \<Rightarrow> 'e \<Rightarrow> real \<Rightarrow> bool"
    and early_stop :: "bool"
    and dist_init :: "'darr"
    and parent_init :: "'parr"
  assumes graph_inv: "out_graph_inv og"
    and srcs_invar: "src_invar srcs"
    and srcs_in_V: "src_abstract srcs \<subseteq> \<V>"
    and w_nonneg: "\<And>e. e \<in> \<E> \<Longrightarrow> 0 \<le> w e"
    and dist_init_invar: "dist_invar dist_init"
    and dist_init_inf: "\<And>v. dist_lookup dist_init v = -1"
    and parent_init_invar: "parent_invar parent_init"
    and parent_init_none: "\<And>v. parent_lookup parent_init v = None"
    and srcs_fresh: "src_remaining srcs = src_abstract srcs"
    and graph_fresh: "\<And>v. out_iterated og v = {}"
begin

text \<open>The predicate @{term allowed} sees the tail, head, edge and weight. The allowed edges form
      the subgraph @{term Ea}, to which all paths and distances refer.\<close>

definition "allowed_edge e \<longleftrightarrow> allowed (fst e) (snd e) e (w e)"

abbreviation "Ea \<equiv> {e \<in> \<E>. allowed_edge e}"

sublocale ag: multigraph_spec Ea fst snd create_edge .

lemma Ea_sub: "Ea \<subseteq> \<E>" by auto

lemmas ag_path_bet = sub_path_bet[OF Ea_sub]
  and ag_path_bet_ConsE = sub_path_bet_ConsE[OF Ea_sub]
  and ag_path_bet_snocI = sub_path_bet_snocI[OF Ea_sub]
  and ag_path_bet_edge_split = sub_path_bet_edge_split[OF Ea_sub]
  and ag_reachable_iff_path = sub_reachable_iff_path[OF Ea_sub]
  and ag_distance_set_le_path = sub_distance_set_le_path[OF Ea_sub]
  and ag_distance_set_infty_iff = sub_distance_set_infty_iff[OF Ea_sub]
  and ag_dist_set_less_infty_get_path = sub_dist_set_less_infty_get_path[OF Ea_sub]
  and ag_distance_set_path_shortest = sub_distance_set_path_shortest[OF Ea_sub]
  and ag_distance_set_path_le_targets = sub_distance_set_path_le_targets[OF Ea_sub]

lemma ag_path_bet_edges_subset: "ag.path_bet es u v \<Longrightarrow> set es \<subseteq> Ea"
  by (simp add: ag.path_bet_def)

lemma ag_path_bet_Nil[simp]: "ag.path_bet [] u v \<longleftrightarrow> u = v"
  by (simp add: ag.path_bet_def multigraph_path_def)

subsection \<open>The single-edge operations\<close>

text \<open>Relax a single outgoing edge @{term e} of the just-settled vertex @{term u}, whose final
      distance is @{term du}. If the head @{term "snd e"} is unsettled, the edge is allowed, and the
      new tentative distance @{term "du + w e"} improves on its current one (or the head is not yet
      reached, marked by distance \<open>-1\<close>), update the distance and parent and either insert the head
      into the queue (first time it is reached) or decrease its key.\<close>

definition relax_edge :: "'v \<Rightarrow> real \<Rightarrow> 'e \<Rightarrow>
    ('v,'g,'darr,'sset,'parr,'queue,'src) dij_state \<Rightarrow> ('v,'g,'darr,'sset,'parr,'queue,'src) dij_state" where
  "relax_edge u du e st =
     (let v = snd e; nv = du + w e in
      if seen_isin (dij_seen st) v \<or> \<not> allowed_edge e then st
      else if dist_lookup (dij_dist st) v = -1 then
        st \<lparr> dij_dist := dist_upd (dij_dist st) v nv,
             dij_parent := parent_upd (dij_parent st) v (Some e),
             dij_heap := queue_insert (dij_heap st) v nv \<rparr>
      else if nv < dist_lookup (dij_dist st) v then
        st \<lparr> dij_dist := dist_upd (dij_dist st) v nv,
             dij_parent := parent_upd (dij_parent st) v (Some e),
             dij_heap := queue_decrease_key (dij_heap st) v nv \<rparr>
      else st)"

text \<open>Register one source: its distance becomes \<open>0\<close> and it enters the queue at key \<open>0\<close>.\<close>

definition insert_source :: "'v \<Rightarrow>
    ('v,'g,'darr,'sset,'parr,'queue,'src) dij_state \<Rightarrow> ('v,'g,'darr,'sset,'parr,'queue,'src) dij_state" where
  "insert_source v st = st \<lparr> dij_dist := dist_upd (dij_dist st) v 0,
                             dij_heap := queue_insert (dij_heap st) v 0 \<rparr>"


subsection \<open>The main loop\<close>

text \<open>Each step advances by one element: relax one outgoing edge of the vertex currently being
      scanned; finish scanning it; load one source; skip a stale queue entry; or pop the next
      minimum and settle it. The loop ends when the queue is empty (whole reachable tree computed) or
      -- with @{term early_stop} -- when the popped vertex is a target.\<close>

function (domintros) dijkstra ::
  "('v,'g,'darr,'sset,'parr,'queue,'src) dij_state \<Rightarrow> ('v,'g,'darr,'sset,'parr,'queue,'src) dij_state" where
  "dijkstra st =
     (case dij_curr st of
        Some u \<Rightarrow>
          (if out_has (dij_graph st) u
           then dijkstra (relax_edge u (dist_lookup (dij_dist st) u) (out_current (dij_graph st) u)
                            (st \<lparr> dij_graph := out_move (dij_graph st) u \<rparr>))
           else dijkstra (st \<lparr> dij_curr := None \<rparr>))
      | None \<Rightarrow>
          (if src_has (dij_srcs st)
           then dijkstra (insert_source (src_current (dij_srcs st)) (st \<lparr> dij_srcs := src_move (dij_srcs st) \<rparr>))
           else (case queue_extract_min (dij_heap st) of
                   (h', None) \<Rightarrow> st \<lparr> dij_heap := h' \<rparr>
                 | (h', Some u) \<Rightarrow>
                     (if seen_isin (dij_seen st) u then dijkstra (st \<lparr> dij_heap := h' \<rparr>)
                      else if early_stop \<and> target u
                           then st \<lparr> dij_heap := h', dij_seen := seen_insert u (dij_seen st), dij_target := Some u \<rparr>
                           else dijkstra (st \<lparr> dij_heap := h', dij_seen := seen_insert u (dij_seen st),
                                               dij_curr := Some u, dij_graph := out_reset (dij_graph st) u \<rparr>)))))"
  by pat_completeness auto

definition "initial_state = \<lparr> dij_dist = dist_init, dij_seen = seen_empty, dij_parent = parent_init,
                     dij_heap = queue_empty, dij_graph = og, dij_target = None,
                     dij_curr = None, dij_srcs = srcs \<rparr>"

definition "dijkstra_compute = dijkstra initial_state"


subsection \<open>The branch conditions\<close>

definition "dijkstra_call_relax_conds st =
  (case dij_curr st of Some u \<Rightarrow> out_has (dij_graph st) u | None \<Rightarrow> False)"

definition "dijkstra_call_finish_conds st =
  (case dij_curr st of Some u \<Rightarrow> \<not> out_has (dij_graph st) u | None \<Rightarrow> False)"

definition "dijkstra_call_init_conds st =
  (case dij_curr st of Some u \<Rightarrow> False | None \<Rightarrow> src_has (dij_srcs st))"

definition "dijkstra_call_skip_conds st =
  (case dij_curr st of Some u \<Rightarrow> False | None \<Rightarrow>
     (\<not> src_has (dij_srcs st) \<and>
      (case queue_extract_min (dij_heap st) of (h', mo) \<Rightarrow>
         (case mo of Some u \<Rightarrow> seen_isin (dij_seen st) u | None \<Rightarrow> False))))"

definition "dijkstra_call_settle_conds st =
  (case dij_curr st of Some u \<Rightarrow> False | None \<Rightarrow>
     (\<not> src_has (dij_srcs st) \<and>
      (case queue_extract_min (dij_heap st) of (h', mo) \<Rightarrow>
         (case mo of Some u \<Rightarrow> \<not> seen_isin (dij_seen st) u \<and> \<not> (early_stop \<and> target u) | None \<Rightarrow> False))))"

definition "dijkstra_ret_done_conds st =
  (case dij_curr st of Some u \<Rightarrow> False | None \<Rightarrow>
     (\<not> src_has (dij_srcs st) \<and> (case queue_extract_min (dij_heap st) of (h', mo) \<Rightarrow> mo = None)))"

definition "dijkstra_ret_found_conds st =
  (case dij_curr st of Some u \<Rightarrow> False | None \<Rightarrow>
     (\<not> src_has (dij_srcs st) \<and>
      (case queue_extract_min (dij_heap st) of (h', mo) \<Rightarrow>
         (case mo of Some u \<Rightarrow> \<not> seen_isin (dij_seen st) u \<and> (early_stop \<and> target u) | None \<Rightarrow> False))))"


subsection \<open>The updates and returns\<close>

definition "dijkstra_upd_relax st =
  (let u = the (dij_curr st) in
     relax_edge u (dist_lookup (dij_dist st) u) (out_current (dij_graph st) u)
       (st \<lparr> dij_graph := out_move (dij_graph st) u \<rparr>))"

definition "dijkstra_upd_finish st = st \<lparr> dij_curr := None \<rparr>"

definition "dijkstra_upd_init st =
  insert_source (src_current (dij_srcs st)) (st \<lparr> dij_srcs := src_move (dij_srcs st) \<rparr>)"

definition "dijkstra_upd_skip st =
  (case queue_extract_min (dij_heap st) of (h', mo) \<Rightarrow> st \<lparr> dij_heap := h' \<rparr>)"

definition "dijkstra_upd_settle st =
  (case queue_extract_min (dij_heap st) of (h', mo) \<Rightarrow>
     (let u = the mo in
        st \<lparr> dij_heap := h', dij_seen := seen_insert u (dij_seen st),
             dij_curr := Some u, dij_graph := out_reset (dij_graph st) u \<rparr>))"

definition "dijkstra_ret_done st = st \<lparr> dij_heap := Product_Type.fst (queue_extract_min (dij_heap st)) \<rparr>"

definition "dijkstra_ret_found st =
  (case queue_extract_min (dij_heap st) of (h', mo) \<Rightarrow>
     (let u = the mo in
        st \<lparr> dij_heap := h', dij_seen := seen_insert u (dij_seen st), dij_target := Some u \<rparr>))"


subsection \<open>Condition eliminators, cases, simps, induction and domain rules\<close>

lemma dijkstra_call_relax_condsE[call_cond_elims]:
  "dijkstra_call_relax_conds st \<Longrightarrow>
   (\<And>u. \<lbrakk>dij_curr st = Some u; out_has (dij_graph st) u\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: dijkstra_call_relax_conds_def split: option.splits)

lemma dijkstra_call_finish_condsE[call_cond_elims]:
  "dijkstra_call_finish_conds st \<Longrightarrow>
   (\<And>u. \<lbrakk>dij_curr st = Some u; \<not> out_has (dij_graph st) u\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: dijkstra_call_finish_conds_def split: option.splits)

lemma dijkstra_call_init_condsE[call_cond_elims]:
  "dijkstra_call_init_conds st \<Longrightarrow>
   (\<lbrakk>dij_curr st = None; src_has (dij_srcs st)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: dijkstra_call_init_conds_def split: option.splits)

lemma dijkstra_call_skip_condsE[call_cond_elims]: "dijkstra_call_skip_conds st \<Longrightarrow> (\<And>h2 u. \<lbrakk>dij_curr st = None; \<not> src_has (dij_srcs st); queue_extract_min (dij_heap st) = (h2, Some u); seen_isin (dij_seen st) u\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: dijkstra_call_skip_conds_def split: option.splits prod.splits)

lemma dijkstra_call_settle_condsE[call_cond_elims]: "dijkstra_call_settle_conds st \<Longrightarrow> (\<And>h2 u. \<lbrakk>dij_curr st = None; \<not> src_has (dij_srcs st); queue_extract_min (dij_heap st) = (h2, Some u); \<not> seen_isin (dij_seen st) u; \<not> (early_stop \<and> target u)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: dijkstra_call_settle_conds_def split: option.splits prod.splits)

lemma dijkstra_ret_done_condsE[call_cond_elims]: "dijkstra_ret_done_conds st \<Longrightarrow> (\<And>h2. \<lbrakk>dij_curr st = None; \<not> src_has (dij_srcs st); queue_extract_min (dij_heap st) = (h2, None)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: dijkstra_ret_done_conds_def split: option.splits prod.splits)

lemma dijkstra_ret_found_condsE[call_cond_elims]: "dijkstra_ret_found_conds st \<Longrightarrow> (\<And>h2 u. \<lbrakk>dij_curr st = None; \<not> src_has (dij_srcs st); queue_extract_min (dij_heap st) = (h2, Some u); \<not> seen_isin (dij_seen st) u; early_stop; target u\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: dijkstra_ret_found_conds_def split: option.splits prod.splits)

lemma dijkstra_cases:
  assumes "dijkstra_call_relax_conds st \<Longrightarrow> P"
      and "dijkstra_call_finish_conds st \<Longrightarrow> P"
      and "dijkstra_call_init_conds st \<Longrightarrow> P"
      and "dijkstra_call_skip_conds st \<Longrightarrow> P"
      and "dijkstra_call_settle_conds st \<Longrightarrow> P"
      and "dijkstra_ret_done_conds st \<Longrightarrow> P"
      and "dijkstra_ret_found_conds st \<Longrightarrow> P"
    shows P
proof -
  have "dijkstra_call_relax_conds st \<or> dijkstra_call_finish_conds st \<or> dijkstra_call_init_conds st \<or>
        dijkstra_call_skip_conds st \<or> dijkstra_call_settle_conds st \<or> dijkstra_ret_done_conds st \<or>
        dijkstra_ret_found_conds st"
    by (auto simp: dijkstra_call_relax_conds_def dijkstra_call_finish_conds_def
                   dijkstra_call_init_conds_def dijkstra_call_skip_conds_def
                   dijkstra_call_settle_conds_def dijkstra_ret_done_conds_def
                   dijkstra_ret_found_conds_def
             split: option.split_asm prod.split_asm option.split prod.split)
  then show ?thesis using assms by auto
qed

lemma dijkstra_simps:
  assumes "dijkstra_dom st"
  shows "dijkstra_call_relax_conds st \<Longrightarrow> dijkstra st = dijkstra (dijkstra_upd_relax st)"
    and "dijkstra_call_finish_conds st \<Longrightarrow> dijkstra st = dijkstra (dijkstra_upd_finish st)"
    and "dijkstra_call_init_conds st \<Longrightarrow> dijkstra st = dijkstra (dijkstra_upd_init st)"
    and "dijkstra_call_skip_conds st \<Longrightarrow> dijkstra st = dijkstra (dijkstra_upd_skip st)"
    and "dijkstra_call_settle_conds st \<Longrightarrow> dijkstra st = dijkstra (dijkstra_upd_settle st)"
    and "dijkstra_ret_done_conds st \<Longrightarrow> dijkstra st = dijkstra_ret_done st"
    and "dijkstra_ret_found_conds st \<Longrightarrow> dijkstra st = dijkstra_ret_found st"
  by (auto simp add: dijkstra.psimps[OF assms] Let_def
             dijkstra_call_relax_conds_def dijkstra_upd_relax_def
             dijkstra_call_finish_conds_def dijkstra_upd_finish_def
             dijkstra_call_init_conds_def dijkstra_upd_init_def
             dijkstra_call_skip_conds_def dijkstra_upd_skip_def
             dijkstra_call_settle_conds_def dijkstra_upd_settle_def
             dijkstra_ret_done_conds_def dijkstra_ret_done_def
             dijkstra_ret_found_conds_def dijkstra_ret_found_def
           split: option.splits prod.splits)

lemma dijkstra_induct:
  assumes "dijkstra_dom st"
  assumes "\<And>st. \<lbrakk>dijkstra_dom st; dijkstra_call_relax_conds st \<Longrightarrow> P (dijkstra_upd_relax st); dijkstra_call_finish_conds st \<Longrightarrow> P (dijkstra_upd_finish st); dijkstra_call_init_conds st \<Longrightarrow> P (dijkstra_upd_init st); dijkstra_call_skip_conds st \<Longrightarrow> P (dijkstra_upd_skip st); dijkstra_call_settle_conds st \<Longrightarrow> P (dijkstra_upd_settle st)\<rbrakk> \<Longrightarrow> P st"
  shows "P st"
  apply(rule dijkstra.pinduct[OF assms(1)])
  apply(rule assms(2)[simplified dijkstra_call_relax_conds_def dijkstra_upd_relax_def dijkstra_call_finish_conds_def dijkstra_upd_finish_def dijkstra_call_init_conds_def dijkstra_upd_init_def dijkstra_call_skip_conds_def dijkstra_upd_skip_def dijkstra_call_settle_conds_def dijkstra_upd_settle_def])
  by (auto simp: Let_def split: option.splits prod.splits)

lemma dijkstra_domintros:
  assumes "dijkstra_call_relax_conds st \<Longrightarrow> dijkstra_dom (dijkstra_upd_relax st)"
      and "dijkstra_call_finish_conds st \<Longrightarrow> dijkstra_dom (dijkstra_upd_finish st)"
      and "dijkstra_call_init_conds st \<Longrightarrow> dijkstra_dom (dijkstra_upd_init st)"
      and "dijkstra_call_skip_conds st \<Longrightarrow> dijkstra_dom (dijkstra_upd_skip st)"
      and "dijkstra_call_settle_conds st \<Longrightarrow> dijkstra_dom (dijkstra_upd_settle st)"
    shows "dijkstra_dom st"
  apply(rule dijkstra.domintros)
  using assms(1)[simplified dijkstra_call_relax_conds_def dijkstra_upd_relax_def]
        assms(2)[simplified dijkstra_call_finish_conds_def dijkstra_upd_finish_def]
        assms(3)[simplified dijkstra_call_init_conds_def dijkstra_upd_init_def]
        assms(4)[simplified dijkstra_call_skip_conds_def dijkstra_upd_skip_def]
        assms(5)[simplified dijkstra_call_settle_conds_def dijkstra_upd_settle_def]
  by (force simp: Let_def split: option.splits prod.splits)+


subsection \<open>The graph cursor\<close>

text \<open>Advancing or rewinding a vertex's edge cursor never disturbs the graph's abstraction to the
      outgoing neighbourhoods, and the current edge is a genuine outgoing arc of the scanned vertex.\<close>

lemma out_has_remaining: "out_invar g \<Longrightarrow> u \<in> \<V> \<Longrightarrow> out_has g u \<Longrightarrow> out_remaining g u \<noteq> {}"
  using outg.idx_has by auto

lemma out_graph_inv_move: "out_graph_inv g \<Longrightarrow> u \<in> \<V> \<Longrightarrow> out_has g u \<Longrightarrow> out_graph_inv (out_move g u)"
  using outg.idx_move_invar outg.idx_move_abstract out_has_remaining by (auto simp: out_graph_inv_def)

lemma out_graph_inv_reset: "out_graph_inv g \<Longrightarrow> u \<in> \<V> \<Longrightarrow> out_graph_inv (out_reset g u)"
  using outg.idx_reset_invar outg.idx_reset_abstract by (auto simp: out_graph_inv_def)

lemma out_remaining_sub_abstract: "out_invar g \<Longrightarrow> u \<in> \<V> \<Longrightarrow> out_remaining g u \<subseteq> out_abstract g u"
  using outg.idx_partition_union by blast

lemma out_current_in_delta:
  assumes "out_graph_inv g" "u \<in> \<V>" "out_has g u"
  shows "out_current g u \<in> \<delta>\<^sup>+ u"
proof -
  have inv: "out_invar g" and abs: "out_abstract g u = \<delta>\<^sup>+ u"
    using assms by (auto simp: out_graph_inv_def)
  have "out_remaining g u \<noteq> {}" using inv assms out_has_remaining by auto
  then have "out_current g u \<in> out_remaining g u" using outg.idx_current inv assms(2) by auto
  moreover have "out_remaining g u \<subseteq> \<delta>\<^sup>+ u"
    using out_remaining_sub_abstract[OF inv assms(2)] abs by simp
  ultimately show ?thesis by blast
qed

lemma out_current_edge: "out_graph_inv g \<Longrightarrow> u \<in> \<V> \<Longrightarrow> out_has g u \<Longrightarrow> out_current g u \<in> \<E>"
  and out_current_fst: "out_graph_inv g \<Longrightarrow> u \<in> \<V> \<Longrightarrow> out_has g u \<Longrightarrow> fst (out_current g u) = u"
  using out_current_in_delta by (auto simp: delta_plus_def)

lemma finite_out_remaining:
  assumes "out_graph_inv g" "u \<in> \<V>" shows "finite (out_remaining g u)"
proof -
  have inv: "out_invar g" and abs: "out_abstract g u = \<delta>\<^sup>+ u"
    using assms by (auto simp: out_graph_inv_def)
  have "out_remaining g u \<subseteq> \<delta>\<^sup>+ u"
    using out_remaining_sub_abstract[OF inv assms(2)] abs by simp
  then show ?thesis using delta_plus_finite by (auto elim: finite_subset)
qed

text \<open>The single-edge operations touch only the distance, parent and heap; the other fields are
      untouched, and they preserve the array invariants.\<close>

lemma relax_edge_seen[simp]: "dij_seen (relax_edge u du e st) = dij_seen st"
  and relax_edge_graph[simp]: "dij_graph (relax_edge u du e st) = dij_graph st"
  and relax_edge_curr[simp]: "dij_curr (relax_edge u du e st) = dij_curr st"
  and relax_edge_srcs[simp]: "dij_srcs (relax_edge u du e st) = dij_srcs st"
  and relax_edge_target[simp]: "dij_target (relax_edge u du e st) = dij_target st"
  by (auto simp: relax_edge_def Let_def)

lemma relax_edge_dist_invar[simp]: "dist_invar (dij_dist st) \<Longrightarrow> snd e \<in> \<V> \<Longrightarrow> dist_invar (dij_dist (relax_edge u du e st))"
  and relax_edge_parent_invar[simp]: "parent_invar (dij_parent st) \<Longrightarrow> snd e \<in> \<V> \<Longrightarrow> parent_invar (dij_parent (relax_edge u du e st))"
  by (auto simp: relax_edge_def Let_def intro: dist_arr.fixed_univ_map_upd_invar parent_arr.fixed_univ_map_upd_invar)

lemma insert_source_seen[simp]: "dij_seen (insert_source v st) = dij_seen st"
  and insert_source_graph[simp]: "dij_graph (insert_source v st) = dij_graph st"
  and insert_source_parent[simp]: "dij_parent (insert_source v st) = dij_parent st"
  and insert_source_curr[simp]: "dij_curr (insert_source v st) = dij_curr st"
  and insert_source_target[simp]: "dij_target (insert_source v st) = dij_target st"
  and insert_source_srcs[simp]: "dij_srcs (insert_source v st) = dij_srcs st"
  and insert_source_dist_invar[simp]: "dist_invar (dij_dist st) \<Longrightarrow> v \<in> \<V> \<Longrightarrow> dist_invar (dij_dist (insert_source v st))"
  by (auto simp: insert_source_def intro: dist_arr.fixed_univ_map_upd_invar)


subsection \<open>Well-formedness invariant\<close>

text \<open>The abstract-datatype invariants of the distance / parent arrays, the graph collection and the
      source iterator are maintained throughout. (The settled-set invariant is coupled with the queue
      contents and is treated separately, since -- the seen set being fixed-universe -- its
      preservation needs that a popped vertex is a graph vertex.)\<close>

definition "invar_1 st \<longleftrightarrow> dist_invar (dij_dist st) \<and> parent_invar (dij_parent st) \<and>
  out_graph_inv (dij_graph st) \<and> src_invar (dij_srcs st)"

lemma invar_1_props[invar_props_elims]:
  "invar_1 st \<Longrightarrow> (\<lbrakk>dist_invar (dij_dist st); parent_invar (dij_parent st); out_graph_inv (dij_graph st); src_invar (dij_srcs st)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_1_def)

lemma invar_1_intro[invar_props_intros]:
  "\<lbrakk>dist_invar (dij_dist st); parent_invar (dij_parent st); out_graph_inv (dij_graph st); src_invar (dij_srcs st)\<rbrakk> \<Longrightarrow> invar_1 st"
  by (auto simp: invar_1_def)

subsection \<open>Queue--distance coupling invariant\<close>

text \<open>The heart of the correctness argument: the priority queue holds exactly the \<^emph>\<open>reached but not yet
      settled\<close> vertices, each keyed by its current tentative distance (a real \<open>\<noteq> -1\<close>). Alongside it
      we carry that the queue and seen set are well-formed, that settled and reached vertices are
      graph vertices, and that a vertex currently being scanned is a graph vertex. A consequence
      (used for the \<open>skip\<close> branch) is that a settled vertex is never in the queue, so a stale pop
      cannot occur.\<close>

definition "invar_2 st \<longleftrightarrow>
   queue_invar (dij_heap st) \<and>
   seen_invar (dij_seen st) \<and>
   seen_abstract (dij_seen st) \<subseteq> \<V> \<and>
   (\<forall>x. dist_lookup (dij_dist st) x \<noteq> -1 \<longrightarrow> x \<in> \<V>) \<and>
   (\<forall>u. dij_curr st = Some u \<longrightarrow> u \<in> \<V>) \<and>
   (\<forall>x k. ((x,k) \<in> queue_abstract (dij_heap st)) =
          (x \<notin> seen_abstract (dij_seen st) \<and> dist_lookup (dij_dist st) x \<noteq> -1 \<and> k = dist_lookup (dij_dist st) x))"

lemma invar_2_props[invar_props_elims]: "invar_2 st \<Longrightarrow> (\<lbrakk>queue_invar (dij_heap st); seen_invar (dij_seen st); seen_abstract (dij_seen st) \<subseteq> \<V>; \<forall>x. dist_lookup (dij_dist st) x \<noteq> -1 \<longrightarrow> x \<in> \<V>; \<forall>u. dij_curr st = Some u \<longrightarrow> u \<in> \<V>; \<forall>x k. ((x,k) \<in> queue_abstract (dij_heap st)) = (x \<notin> seen_abstract (dij_seen st) \<and> dist_lookup (dij_dist st) x \<noteq> -1 \<and> k = dist_lookup (dij_dist st) x)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_2_def)

lemma invar_2_intro[invar_props_intros]: "\<lbrakk>queue_invar (dij_heap st); seen_invar (dij_seen st); seen_abstract (dij_seen st) \<subseteq> \<V>; \<forall>x. dist_lookup (dij_dist st) x \<noteq> -1 \<longrightarrow> x \<in> \<V>; \<forall>u. dij_curr st = Some u \<longrightarrow> u \<in> \<V>; \<forall>x k. ((x,k) \<in> queue_abstract (dij_heap st)) = (x \<notin> seen_abstract (dij_seen st) \<and> dist_lookup (dij_dist st) x \<noteq> -1 \<and> k = dist_lookup (dij_dist st) x)\<rbrakk> \<Longrightarrow> invar_2 st"
  by (auto simp: invar_2_def)

lemma invar_2_holds_finish[invar_holds_intros]: "\<lbrakk>dijkstra_call_finish_conds st; invar_2 st\<rbrakk> \<Longrightarrow> invar_2 (dijkstra_upd_finish st)"
  by (auto simp: dijkstra_upd_finish_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_2_holds_done[invar_holds_intros]: "\<lbrakk>dijkstra_ret_done_conds st; invar_2 st\<rbrakk> \<Longrightarrow> invar_2 (dijkstra_ret_done st)"
proof -
  assume a: "dijkstra_ret_done_conds st" "invar_2 st"
  obtain h2 where ex: "queue_extract_min (dij_heap st) = (h2, None)"
    using a(1) by (auto elim!: dijkstra_ret_done_condsE)
  have qi: "queue_invar (dij_heap st)" using a(2) by (auto elim!: invar_2_props)
  have e1: "queue_abstract (dij_heap st) = {}" using heap.queue_extract_min(3)[OF qi] ex by simp
  have e2: "queue_abstract h2 = {}" using heap.queue_extract_min(5)[OF qi] ex by simp
  have q2: "queue_invar h2" using heap.queue_extract_min(1)[OF qi] ex by simp
  show ?thesis using a(2) e1 e2 q2 ex by (auto simp: invar_2_def dijkstra_ret_done_def)
qed

text \<open>The \<open>skip\<close> branch is unreachable: extracting a settled vertex would put it in the queue,
      contradicting the coupling.\<close>

lemma invar_2_holds_skip[invar_holds_intros]: "\<lbrakk>dijkstra_call_skip_conds st; invar_2 st\<rbrakk> \<Longrightarrow> invar_2 (dijkstra_upd_skip st)"
proof -
  assume a: "dijkstra_call_skip_conds st" "invar_2 st"
  obtain h2 u where hu: "queue_extract_min (dij_heap st) = (h2, Some u)" "seen_isin (dij_seen st) u"
    using a(1) by (auto elim!: dijkstra_call_skip_condsE)
  have qi: "queue_invar (dij_heap st)" and si: "seen_invar (dij_seen st)"
    and coup: "\<forall>x k. ((x,k) \<in> queue_abstract (dij_heap st)) = (x \<notin> seen_abstract (dij_seen st) \<and> dist_lookup (dij_dist st) x \<noteq> -1 \<and> k = dist_lookup (dij_dist st) x)"
    using a(2) by (auto elim!: invar_2_props)
  have "\<exists>k. (u,k) \<in> queue_abstract (dij_heap st)"
    using heap.queue_extract_min(2)[OF qi, of u] hu(1) by simp blast
  moreover have "u \<in> seen_abstract (dij_seen st)"
    using si hu(2) seen_set.fixed_univ_set_isin by auto
  ultimately show ?thesis using coup by blast
qed

text \<open>Settling a popped vertex: it is removed from the queue and added to the settled set; the popped
      vertex is reached, hence a graph vertex, and by key-uniqueness it occurred once in the queue.\<close>

lemma invar_2_holds_settle[invar_holds_intros]: "\<lbrakk>dijkstra_call_settle_conds st; invar_2 st\<rbrakk> \<Longrightarrow> invar_2 (dijkstra_upd_settle st)"
proof -
  assume a: "dijkstra_call_settle_conds st" "invar_2 st"
  obtain h2 u where hu: "queue_extract_min (dij_heap st) = (h2, Some u)" "\<not> seen_isin (dij_seen st) u"
    using a(1) by (auto elim!: dijkstra_call_settle_condsE)
  have qi: "queue_invar (dij_heap st)" and si: "seen_invar (dij_seen st)"
    and sV: "seen_abstract (dij_seen st) \<subseteq> \<V>"
    and reachV: "\<forall>x. dist_lookup (dij_dist st) x \<noteq> -1 \<longrightarrow> x \<in> \<V>"
    and coup: "\<forall>x k. ((x,k) \<in> queue_abstract (dij_heap st)) = (x \<notin> seen_abstract (dij_seen st) \<and> dist_lookup (dij_dist st) x \<noteq> -1 \<and> k = dist_lookup (dij_dist st) x)"
    using a(2) by (auto elim!: invar_2_props)
  obtain k where uk: "(u,k) \<in> queue_abstract (dij_heap st)"
    using heap.queue_extract_min(2)[OF qi, of u] hu(1) by simp blast
  have duk: "dist_lookup (dij_dist st) u \<noteq> -1" using coup uk by blast
  have uV: "u \<in> \<V>" using reachV duk by blast
  have h2q: "queue_abstract h2 = queue_abstract (dij_heap st) - {(u,k)}"
    using heap.queue_extract_min(4)[OF qi, of u k] hu(1) uk by simp
  have quniq: "\<And>k'. (u,k') \<in> queue_abstract (dij_heap st) \<Longrightarrow> k' = k"
    using heap.key_for_element_unique[OF qi] uk by blast
  have qih2: "queue_invar h2" using heap.queue_extract_min(1)[OF qi] hu(1) by simp
  show ?thesis
    unfolding dijkstra_upd_settle_def hu(1) prod.case Let_def option.sel
    apply (rule invar_2_intro)
    subgoal using qih2 by simp
    subgoal using seen_set.fixed_univ_set_insert(1)[OF si uV] by simp
    subgoal using seen_set.fixed_univ_set_insert(2)[OF si uV] sV uV by simp
    subgoal using reachV by simp
    subgoal using uV by simp
    subgoal using h2q coup quniq seen_set.fixed_univ_set_insert(2)[OF si uV] by auto
    done
qed

lemma invar_2_holds_found[invar_holds_intros]: "\<lbrakk>dijkstra_ret_found_conds st; invar_2 st\<rbrakk> \<Longrightarrow> invar_2 (dijkstra_ret_found st)"
proof -
  assume a: "dijkstra_ret_found_conds st" "invar_2 st"
  obtain h2 u where hu: "queue_extract_min (dij_heap st) = (h2, Some u)" "\<not> seen_isin (dij_seen st) u"
    using a(1) by (auto elim!: dijkstra_ret_found_condsE)
  have qi: "queue_invar (dij_heap st)" and si: "seen_invar (dij_seen st)"
    and sV: "seen_abstract (dij_seen st) \<subseteq> \<V>"
    and reachV: "\<forall>x. dist_lookup (dij_dist st) x \<noteq> -1 \<longrightarrow> x \<in> \<V>"
    and curV: "\<forall>u. dij_curr st = Some u \<longrightarrow> u \<in> \<V>"
    and coup: "\<forall>x k. ((x,k) \<in> queue_abstract (dij_heap st)) = (x \<notin> seen_abstract (dij_seen st) \<and> dist_lookup (dij_dist st) x \<noteq> -1 \<and> k = dist_lookup (dij_dist st) x)"
    using a(2) by (auto elim!: invar_2_props)
  obtain k where uk: "(u,k) \<in> queue_abstract (dij_heap st)"
    using heap.queue_extract_min(2)[OF qi, of u] hu(1) by simp blast
  have duk: "dist_lookup (dij_dist st) u \<noteq> -1" using coup uk by blast
  have uV: "u \<in> \<V>" using reachV duk by blast
  have h2q: "queue_abstract h2 = queue_abstract (dij_heap st) - {(u,k)}"
    using heap.queue_extract_min(4)[OF qi, of u k] hu(1) uk by simp
  have quniq: "\<And>k'. (u,k') \<in> queue_abstract (dij_heap st) \<Longrightarrow> k' = k"
    using heap.key_for_element_unique[OF qi] uk by blast
  have qih2: "queue_invar h2" using heap.queue_extract_min(1)[OF qi] hu(1) by simp
  show ?thesis
    unfolding dijkstra_ret_found_def hu(1) prod.case Let_def option.sel
    apply (rule invar_2_intro)
    subgoal using qih2 by simp
    subgoal using seen_set.fixed_univ_set_insert(1)[OF si uV] by simp
    subgoal using seen_set.fixed_univ_set_insert(2)[OF si uV] sV uV by simp
    subgoal using reachV by simp
    subgoal using curV by simp
    subgoal using h2q coup quniq seen_set.fixed_univ_set_insert(2)[OF si uV] by auto
    done
qed

text \<open>A closed form for the tentative distance after relaxing one edge.\<close>

lemma relax_edge_dist_at:
  assumes "dist_invar (dij_dist st)" "snd e \<in> \<V>"
  shows "dist_lookup (dij_dist (relax_edge u du e st)) x =
    (if x = snd e \<and> \<not> seen_isin (dij_seen st) (snd e) \<and> allowed_edge e \<and>
        (dist_lookup (dij_dist st) (snd e) = -1 \<or> du + w e < dist_lookup (dij_dist st) (snd e))
     then du + w e else dist_lookup (dij_dist st) x)"
  by (auto simp: relax_edge_def Let_def dist_arr.fixed_univ_map_upd[OF assms] split: if_splits)


subsection \<open>Auxiliary source-phase / non-negativity invariant\<close>

text \<open>Facts about the source-loading phase and non-negativity of tentative distances that the \<open>init\<close>
      and \<open>relax\<close> branches of the coupling invariant depend on: unprocessed sources are still
      unreached; a scanned vertex is settled, reached and never revised; and every reached vertex has
      a non-negative distance (as edge weights are non-negative).\<close>

definition "invar_3 st \<longleftrightarrow>
   src_abstract (dij_srcs st) \<subseteq> \<V> \<and>
   (\<forall>v. v \<in> src_remaining (dij_srcs st) \<longrightarrow> dist_lookup (dij_dist st) v = -1) \<and>
   (\<forall>u. dij_curr st = Some u \<longrightarrow> src_remaining (dij_srcs st) = {}) \<and>
   (\<forall>x. dist_lookup (dij_dist st) x \<noteq> -1 \<longrightarrow> 0 \<le> dist_lookup (dij_dist st) x) \<and>
   (\<forall>u. dij_curr st = Some u \<longrightarrow> dist_lookup (dij_dist st) u \<noteq> -1) \<and>
   (\<forall>u. dij_curr st = Some u \<longrightarrow> u \<in> seen_abstract (dij_seen st))"

lemma invar_3_props[invar_props_elims]: "invar_3 st \<Longrightarrow> (\<lbrakk>src_abstract (dij_srcs st) \<subseteq> \<V>; \<forall>v. v \<in> src_remaining (dij_srcs st) \<longrightarrow> dist_lookup (dij_dist st) v = -1; \<forall>u. dij_curr st = Some u \<longrightarrow> src_remaining (dij_srcs st) = {}; \<forall>x. dist_lookup (dij_dist st) x \<noteq> -1 \<longrightarrow> 0 \<le> dist_lookup (dij_dist st) x; \<forall>u. dij_curr st = Some u \<longrightarrow> dist_lookup (dij_dist st) u \<noteq> -1; \<forall>u. dij_curr st = Some u \<longrightarrow> u \<in> seen_abstract (dij_seen st)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_3_def)

lemma invar_3_intro[invar_props_intros]: "\<lbrakk>src_abstract (dij_srcs st) \<subseteq> \<V>; \<forall>v. v \<in> src_remaining (dij_srcs st) \<longrightarrow> dist_lookup (dij_dist st) v = -1; \<forall>u. dij_curr st = Some u \<longrightarrow> src_remaining (dij_srcs st) = {}; \<forall>x. dist_lookup (dij_dist st) x \<noteq> -1 \<longrightarrow> 0 \<le> dist_lookup (dij_dist st) x; \<forall>u. dij_curr st = Some u \<longrightarrow> dist_lookup (dij_dist st) u \<noteq> -1; \<forall>u. dij_curr st = Some u \<longrightarrow> u \<in> seen_abstract (dij_seen st)\<rbrakk> \<Longrightarrow> invar_3 st"
  by (auto simp: invar_3_def)

lemma invar_3_holds_finish[invar_holds_intros]: "\<lbrakk>dijkstra_call_finish_conds st; invar_3 st\<rbrakk> \<Longrightarrow> invar_3 (dijkstra_upd_finish st)"
  by (auto simp: dijkstra_upd_finish_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_3_holds_done[invar_holds_intros]: "\<lbrakk>dijkstra_ret_done_conds st; invar_3 st\<rbrakk> \<Longrightarrow> invar_3 (dijkstra_ret_done st)"
  by (simp add: dijkstra_ret_done_def invar_3_def)

lemma invar_3_holds_found[invar_holds_intros]: "\<lbrakk>dijkstra_ret_found_conds st; invar_3 st\<rbrakk> \<Longrightarrow> invar_3 (dijkstra_ret_found st)"
proof -
  assume a: "dijkstra_ret_found_conds st" "invar_3 st"
  obtain h2 u where hu: "dij_curr st = None" "queue_extract_min (dij_heap st) = (h2, Some u)"
    using a(1) by (auto elim!: dijkstra_ret_found_condsE)
  show ?thesis using a(2)
    by (auto simp: dijkstra_ret_found_def invar_3_def Let_def hu(1) hu(2))
qed

lemma invar_3_holds_skip[invar_holds_intros]: "\<lbrakk>dijkstra_call_skip_conds st; invar_2 st; invar_3 st\<rbrakk> \<Longrightarrow> invar_3 (dijkstra_upd_skip st)"
proof -
  assume a: "dijkstra_call_skip_conds st" "invar_2 st"
  obtain h2 u where hu: "queue_extract_min (dij_heap st) = (h2, Some u)" "seen_isin (dij_seen st) u"
    using a(1) by (auto elim!: dijkstra_call_skip_condsE)
  have qi: "queue_invar (dij_heap st)" and si: "seen_invar (dij_seen st)"
    and coup: "\<forall>x k. ((x,k) \<in> queue_abstract (dij_heap st)) = (x \<notin> seen_abstract (dij_seen st) \<and> dist_lookup (dij_dist st) x \<noteq> -1 \<and> k = dist_lookup (dij_dist st) x)"
    using a(2) by (auto elim!: invar_2_props)
  have "\<exists>k. (u,k) \<in> queue_abstract (dij_heap st)"
    using heap.queue_extract_min(2)[OF qi, of u] hu(1) by simp blast
  moreover have "u \<in> seen_abstract (dij_seen st)" using si hu(2) seen_set.fixed_univ_set_isin by auto
  ultimately show ?thesis using coup by blast
qed

lemma invar_3_holds_settle[invar_holds_intros]: "\<lbrakk>dijkstra_call_settle_conds st; invar_1 st; invar_2 st; invar_3 st\<rbrakk> \<Longrightarrow> invar_3 (dijkstra_upd_settle st)"
proof -
  assume a: "dijkstra_call_settle_conds st" "invar_1 st" "invar_2 st" "invar_3 st"
  obtain h2 u where hu: "\<not> src_has (dij_srcs st)" "queue_extract_min (dij_heap st) = (h2, Some u)" "\<not> seen_isin (dij_seen st) u"
    using a(1) by (auto elim!: dijkstra_call_settle_condsE)
  have sinv: "src_invar (dij_srcs st)" using a(2) by (auto elim!: invar_props_elims)
  have qi: "queue_invar (dij_heap st)"
    and reachV: "\<forall>x. dist_lookup (dij_dist st) x \<noteq> -1 \<longrightarrow> x \<in> \<V>"
    and si: "seen_invar (dij_seen st)"
    and coup: "\<forall>x k. ((x,k) \<in> queue_abstract (dij_heap st)) = (x \<notin> seen_abstract (dij_seen st) \<and> dist_lookup (dij_dist st) x \<noteq> -1 \<and> k = dist_lookup (dij_dist st) x)"
    using a(3) by (auto elim!: invar_2_props)
  obtain k where uk: "(u,k) \<in> queue_abstract (dij_heap st)"
    using heap.queue_extract_min(2)[OF qi, of u] hu(2) by simp blast
  have duk: "dist_lookup (dij_dist st) u \<noteq> -1" using coup uk by blast
  have uV: "u \<in> \<V>" using reachV duk by blast
  have rem0: "src_remaining (dij_srcs st) = {}" using hu(1) sinv sources.has_current by auto
  show ?thesis
    unfolding dijkstra_upd_settle_def hu(2) prod.case Let_def option.sel
    apply (rule invar_3_intro)
    subgoal using a(4) by (auto elim!: invar_props_elims)
    subgoal using a(4) by (auto elim!: invar_props_elims)
    subgoal using rem0 by simp
    subgoal using a(4) by (auto elim!: invar_props_elims)
    subgoal using duk by simp
    subgoal using seen_set.fixed_univ_set_insert(2)[OF si uV] by simp
    done
qed

lemma invar_3_holds_init[invar_holds_intros]: "\<lbrakk>dijkstra_call_init_conds st; invar_1 st; invar_3 st\<rbrakk> \<Longrightarrow> invar_3 (dijkstra_upd_init st)"
proof -
  assume a: "dijkstra_call_init_conds st" "invar_1 st" "invar_3 st"
  have cN: "dij_curr st = None" and srch: "src_has (dij_srcs st)"
    using a(1) by (auto elim!: dijkstra_call_init_condsE)
  have dinv: "dist_invar (dij_dist st)" and sinv: "src_invar (dij_srcs st)"
    using a(2) by (auto elim!: invar_props_elims)
  have rem: "src_remaining (dij_srcs st) \<noteq> {}" using srch sinv sources.has_current by auto
  have vV: "src_current (dij_srcs st) \<in> \<V>"
    using a(3) sources.current_element[OF sinv rem] sources.iterable_set_abstract(2)[OF sinv] by (auto elim!: invar_3_props)
  note upd = dist_arr.fixed_univ_map_upd[OF dinv vV]
  show ?thesis
    unfolding dijkstra_upd_init_def insert_source_def
    apply (rule invar_3_intro)
    subgoal using a(3) by (auto simp: sources.move_on(1)[OF sinv rem] elim!: invar_props_elims)
    subgoal using a(3) by (auto simp: sources.move_on(2)[OF sinv rem] upd elim!: invar_props_elims)
    subgoal using cN by simp
    subgoal using a(3) by (auto simp: upd elim!: invar_props_elims)
    subgoal using cN by simp
    subgoal using cN by simp
    done
qed

lemma invar_3_holds_relax[invar_holds_intros]: "\<lbrakk>dijkstra_call_relax_conds st; invar_1 st; invar_2 st; invar_3 st\<rbrakk> \<Longrightarrow> invar_3 (dijkstra_upd_relax st)"
proof -
  assume a: "dijkstra_call_relax_conds st" "invar_1 st" "invar_2 st" "invar_3 st"
  obtain u where cu: "dij_curr st = Some u" and oh: "out_has (dij_graph st) u"
    using a(1) by (auto elim!: dijkstra_call_relax_condsE)
  have gi: "out_graph_inv (dij_graph st)" and dinv: "dist_invar (dij_dist st)"
    using a(2) by (auto elim!: invar_props_elims)
  have si: "seen_invar (dij_seen st)" and curV: "\<forall>u. dij_curr st = Some u \<longrightarrow> u \<in> \<V>"
    using a(3) by (auto elim!: invar_props_elims)
  have uV: "u \<in> \<V>" using curV cu by blast
  have sabs: "src_abstract (dij_srcs st) \<subseteq> \<V>"
    and rem0: "src_remaining (dij_srcs st) = {}"
    and du_ne: "dist_lookup (dij_dist st) u \<noteq> -1"
    and useen: "u \<in> seen_abstract (dij_seen st)"
    and nn: "\<forall>x. dist_lookup (dij_dist st) x \<noteq> -1 \<longrightarrow> 0 \<le> dist_lookup (dij_dist st) x"
    using a(4) cu by (auto elim!: invar_props_elims)
  have eE: "out_current (dij_graph st) u \<in> \<E>" using out_current_edge[OF gi uV oh] .
  have we0: "0 \<le> w (out_current (dij_graph st) u)" using w_nonneg[OF eE] .
  have du0: "0 \<le> dist_lookup (dij_dist st) u" using nn du_ne by blast
  have vseen: "seen_isin (dij_seen st) u" using si useen seen_set.fixed_univ_set_isin by auto
  define st' where "st' = st \<lparr> dij_graph := out_move (dij_graph st) u \<rparr>"
  have dd[simp]: "dij_dist st' = dij_dist st" and ds[simp]: "dij_seen st' = dij_seen st"
    and dr[simp]: "dij_srcs st' = dij_srcs st" and dc[simp]: "dij_curr st' = dij_curr st"
    by (simp_all add: st'_def)
  have dinv': "dist_invar (dij_dist st')" using dinv by simp
  have upd_eq: "dijkstra_upd_relax st = relax_edge u (dist_lookup (dij_dist st) u) (out_current (dij_graph st) u) st'"
    by (simp add: dijkstra_upd_relax_def cu st'_def)
  have hV: "snd (out_current (dij_graph st) u) \<in> \<V>" using snd_E_V[OF eE] .
  note datx = relax_edge_dist_at[OF dinv' hV, of u "dist_lookup (dij_dist st) u", simplified]
  show ?thesis
    unfolding upd_eq
    apply (rule invar_3_intro)
    subgoal using sabs by simp
    subgoal using rem0 by simp
    subgoal using rem0 cu by simp
    subgoal using datx nn du0 we0 by (auto split: if_splits intro: add_nonneg_nonneg)
    subgoal using datx du_ne vseen cu by (auto split: if_splits)
    subgoal using useen cu by simp
    done
qed


subsection \<open>Auxiliary: sources unloaded implies nothing settled\<close>

definition "invar_4 st \<longleftrightarrow> (src_remaining (dij_srcs st) \<noteq> {} \<longrightarrow> seen_abstract (dij_seen st) = {})"

lemma invar_4_props[invar_props_elims]:
  "invar_4 st \<Longrightarrow> (\<lbrakk>src_remaining (dij_srcs st) \<noteq> {} \<longrightarrow> seen_abstract (dij_seen st) = {}\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_4_def)

lemma invar_4_intro[invar_props_intros]:
  "(src_remaining (dij_srcs st) \<noteq> {} \<longrightarrow> seen_abstract (dij_seen st) = {}) \<Longrightarrow> invar_4 st"
  by (auto simp: invar_4_def)

lemma invar_4_holds_finish[invar_holds_intros]: "\<lbrakk>dijkstra_call_finish_conds st; invar_4 st\<rbrakk> \<Longrightarrow> invar_4 (dijkstra_upd_finish st)"
  by (auto simp: dijkstra_upd_finish_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_4_holds_done[invar_holds_intros]: "\<lbrakk>dijkstra_ret_done_conds st; invar_4 st\<rbrakk> \<Longrightarrow> invar_4 (dijkstra_ret_done st)"
  by (simp add: dijkstra_ret_done_def invar_4_def)

lemma invar_4_holds_relax[invar_holds_intros]: "\<lbrakk>dijkstra_call_relax_conds st; invar_4 st\<rbrakk> \<Longrightarrow> invar_4 (dijkstra_upd_relax st)"
  by (auto simp: dijkstra_upd_relax_def Let_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_4_holds_init[invar_holds_intros]: "\<lbrakk>dijkstra_call_init_conds st; invar_1 st; invar_4 st\<rbrakk> \<Longrightarrow> invar_4 (dijkstra_upd_init st)"
proof -
  assume a: "dijkstra_call_init_conds st" "invar_1 st" "invar_4 st"
  have srch: "src_has (dij_srcs st)" using a(1) by (auto elim!: dijkstra_call_init_condsE)
  have sinv: "src_invar (dij_srcs st)" using a(2) by (auto elim!: invar_props_elims)
  have rem: "src_remaining (dij_srcs st) \<noteq> {}" using srch sinv sources.has_current by auto
  show ?thesis
    unfolding dijkstra_upd_init_def insert_source_def
    apply (rule invar_4_intro)
    using a(3) by (auto simp: sources.move_on(2)[OF sinv rem] elim!: invar_props_elims)
qed

lemma invar_4_holds_settle[invar_holds_intros]: "\<lbrakk>dijkstra_call_settle_conds st; invar_1 st; invar_4 st\<rbrakk> \<Longrightarrow> invar_4 (dijkstra_upd_settle st)"
proof -
  assume a: "dijkstra_call_settle_conds st" "invar_1 st" "invar_4 st"
  obtain h2 u where hu: "\<not> src_has (dij_srcs st)" "queue_extract_min (dij_heap st) = (h2, Some u)"
    using a(1) by (auto elim!: dijkstra_call_settle_condsE)
  have sinv: "src_invar (dij_srcs st)" using a(2) by (auto elim!: invar_props_elims)
  have rem0: "src_remaining (dij_srcs st) = {}" using hu(1) sinv sources.has_current by auto
  show ?thesis
    unfolding dijkstra_upd_settle_def hu(2) prod.case Let_def option.sel
    apply (rule invar_4_intro) using rem0 by simp
qed

lemma invar_4_holds_found[invar_holds_intros]: "\<lbrakk>dijkstra_ret_found_conds st; invar_1 st; invar_4 st\<rbrakk> \<Longrightarrow> invar_4 (dijkstra_ret_found st)"
proof -
  assume a: "dijkstra_ret_found_conds st" "invar_1 st" "invar_4 st"
  obtain h2 u where hu: "\<not> src_has (dij_srcs st)" "queue_extract_min (dij_heap st) = (h2, Some u)"
    using a(1) by (auto elim!: dijkstra_ret_found_condsE)
  have sinv: "src_invar (dij_srcs st)" using a(2) by (auto elim!: invar_props_elims)
  have rem0: "src_remaining (dij_srcs st) = {}" using hu(1) sinv sources.has_current by auto
  show ?thesis
    unfolding dijkstra_ret_found_def hu(2) prod.case Let_def option.sel
    apply (rule invar_4_intro) using rem0 by simp
qed

lemma invar_4_holds_skip[invar_holds_intros]: "\<lbrakk>dijkstra_call_skip_conds st; invar_2 st; invar_4 st\<rbrakk> \<Longrightarrow> invar_4 (dijkstra_upd_skip st)"
proof -
  assume a: "dijkstra_call_skip_conds st" "invar_2 st"
  obtain h2 u where hu: "queue_extract_min (dij_heap st) = (h2, Some u)" "seen_isin (dij_seen st) u"
    using a(1) by (auto elim!: dijkstra_call_skip_condsE)
  have qi: "queue_invar (dij_heap st)" and si: "seen_invar (dij_seen st)"
    and coup: "\<forall>x k. ((x,k) \<in> queue_abstract (dij_heap st)) = (x \<notin> seen_abstract (dij_seen st) \<and> dist_lookup (dij_dist st) x \<noteq> -1 \<and> k = dist_lookup (dij_dist st) x)"
    using a(2) by (auto elim!: invar_2_props)
  have "\<exists>k. (u,k) \<in> queue_abstract (dij_heap st)"
    using heap.queue_extract_min(2)[OF qi, of u] hu(1) by simp blast
  moreover have "u \<in> seen_abstract (dij_seen st)" using si hu(2) seen_set.fixed_univ_set_isin by auto
  ultimately show ?thesis using coup by blast
qed


subsection \<open>The coupling invariant on the source-loading branch\<close>

lemma invar_2_holds_init[invar_holds_intros]: "\<lbrakk>dijkstra_call_init_conds st; invar_1 st; invar_2 st; invar_3 st; invar_4 st\<rbrakk> \<Longrightarrow> invar_2 (dijkstra_upd_init st)"
proof -
  assume a: "dijkstra_call_init_conds st" "invar_1 st" "invar_2 st" "invar_3 st" "invar_4 st"
  have cN: "dij_curr st = None" and srch: "src_has (dij_srcs st)"
    using a(1) by (auto elim!: dijkstra_call_init_condsE)
  have dinv: "dist_invar (dij_dist st)" and sinv: "src_invar (dij_srcs st)"
    using a(2) by (auto elim!: invar_props_elims)
  have qi: "queue_invar (dij_heap st)" and si: "seen_invar (dij_seen st)"
    and sV: "seen_abstract (dij_seen st) \<subseteq> \<V>"
    and reachV: "\<forall>x. dist_lookup (dij_dist st) x \<noteq> -1 \<longrightarrow> x \<in> \<V>"
    and coup: "\<forall>x k. ((x,k) \<in> queue_abstract (dij_heap st)) = (x \<notin> seen_abstract (dij_seen st) \<and> dist_lookup (dij_dist st) x \<noteq> -1 \<and> k = dist_lookup (dij_dist st) x)"
    using a(3) by (auto elim!: invar_2_props)
  have sabs: "src_abstract (dij_srcs st) \<subseteq> \<V>"
    and remD: "\<forall>v. v \<in> src_remaining (dij_srcs st) \<longrightarrow> dist_lookup (dij_dist st) v = -1"
    using a(4) by (auto elim!: invar_props_elims)
  have rem: "src_remaining (dij_srcs st) \<noteq> {}" using srch sinv sources.has_current by auto
  have seenE: "seen_abstract (dij_seen st) = {}" using a(5) rem by (auto elim!: invar_props_elims)
  define v where "v = src_current (dij_srcs st)"
  have vrem: "v \<in> src_remaining (dij_srcs st)" using sources.current_element[OF sinv rem] by (simp add: v_def)
  have vV: "v \<in> \<V>" using vrem sources.iterable_set_abstract(2)[OF sinv] sabs by blast
  have dv: "dist_lookup (dij_dist st) v = -1" using remD vrem by blast
  have notin: "\<nexists>k. (v,k) \<in> queue_abstract (dij_heap st)" using coup dv by blast
  have qins: "queue_abstract (queue_insert (dij_heap st) v 0) = queue_abstract (dij_heap st) \<union> {(v,0)}"
    using heap.queue_insert(2)[OF qi vV notin] .
  have qinv: "queue_invar (queue_insert (dij_heap st) v 0)" using heap.queue_insert(1)[OF qi vV notin] .
  note upd = dist_arr.fixed_univ_map_upd[OF dinv vV[unfolded v_def]]
  show ?thesis
    unfolding dijkstra_upd_init_def insert_source_def
    apply (rule invar_2_intro)
    subgoal using qinv by (simp add: v_def)
    subgoal using si by simp
    subgoal using sV by simp
    subgoal using reachV vV by (auto simp: upd v_def)
    subgoal using cN by simp
    subgoal using qins coup seenE dv by (auto simp: upd v_def)
    done
qed

text \<open>The relaxation branch: a four-way case split (already-settled / not improving vs.\ first-reach
      insert vs.\ decrease-key). The new head keeps a non-negative, finite distance, and the coupling
      is re-established element-by-element from the queue axioms.\<close>

lemma invar_2_holds_relax[invar_holds_intros]: "\<lbrakk>dijkstra_call_relax_conds st; invar_1 st; invar_2 st; invar_3 st\<rbrakk> \<Longrightarrow> invar_2 (dijkstra_upd_relax st)"
proof -
  assume a: "dijkstra_call_relax_conds st" "invar_1 st" "invar_2 st" "invar_3 st"
  obtain u where cu: "dij_curr st = Some u" and oh: "out_has (dij_graph st) u"
    using a(1) by (auto elim!: dijkstra_call_relax_condsE)
  have gi: "out_graph_inv (dij_graph st)" and dinv: "dist_invar (dij_dist st)"
    using a(2) by (auto elim!: invar_1_props)
  have qi: "queue_invar (dij_heap st)" and si: "seen_invar (dij_seen st)"
    and sV: "seen_abstract (dij_seen st) \<subseteq> \<V>" and curV: "\<forall>u. dij_curr st = Some u \<longrightarrow> u \<in> \<V>"
    and reachV: "\<forall>x. dist_lookup (dij_dist st) x \<noteq> -1 \<longrightarrow> x \<in> \<V>"
    and coup: "\<forall>x k. ((x,k) \<in> queue_abstract (dij_heap st)) = (x \<notin> seen_abstract (dij_seen st) \<and> dist_lookup (dij_dist st) x \<noteq> -1 \<and> k = dist_lookup (dij_dist st) x)"
    using a(3) by (auto elim!: invar_2_props)
  have coupD: "\<And>x k. (x,k) \<in> queue_abstract (dij_heap st) \<Longrightarrow> x \<notin> seen_abstract (dij_seen st) \<and> dist_lookup (dij_dist st) x \<noteq> -1 \<and> k = dist_lookup (dij_dist st) x"
    using coup by blast
  have coupI: "\<And>x. x \<notin> seen_abstract (dij_seen st) \<Longrightarrow> dist_lookup (dij_dist st) x \<noteq> -1 \<Longrightarrow> (x, dist_lookup (dij_dist st) x) \<in> queue_abstract (dij_heap st)"
    using coup by blast
  have du_ne: "dist_lookup (dij_dist st) u \<noteq> -1"
    and nn: "\<forall>x. dist_lookup (dij_dist st) x \<noteq> -1 \<longrightarrow> 0 \<le> dist_lookup (dij_dist st) x"
    using a(4) cu by (auto elim!: invar_3_props)
  have uV: "u \<in> \<V>" using curV cu by blast
  have eE: "out_current (dij_graph st) u \<in> \<E>" using out_current_edge[OF gi uV oh] .
  define e where "e = out_current (dij_graph st) u"
  define hv where "hv = snd e"
  define nv where "nv = dist_lookup (dij_dist st) u + w e"
  have hvV: "hv \<in> \<V>" using snd_E_V eE by (simp add: hv_def e_def)
  have du0: "0 \<le> dist_lookup (dij_dist st) u" using nn du_ne by blast
  have nvne: "nv \<noteq> -1" unfolding nv_def e_def using du0 w_nonneg[OF eE] by linarith
  have isin: "\<And>x. seen_isin (dij_seen st) x = (x \<in> seen_abstract (dij_seen st))"
    using seen_set.fixed_univ_set_isin[OF si] by blast
  define st' where "st' = st \<lparr> dij_graph := out_move (dij_graph st) u \<rparr>"
  have dd: "dij_dist st' = dij_dist st" and ds: "dij_seen st' = dij_seen st"
    and dc: "dij_curr st' = dij_curr st" and dh: "dij_heap st' = dij_heap st"
    by (simp_all add: st'_def)
  have upd_eq: "dijkstra_upd_relax st = relax_edge u (dist_lookup (dij_dist st) u) e st'"
    by (simp add: dijkstra_upd_relax_def cu st'_def e_def)
  note upd = dist_arr.fixed_univ_map_upd[OF dinv hvV]
  have duf: "\<And>x. dist_lookup (dist_upd (dij_dist st) hv nv) x = (if x = hv then nv else dist_lookup (dij_dist st) x)"
    by (simp add: upd)
  have reach': "\<forall>x. dist_lookup (dist_upd (dij_dist st) hv nv) x \<noteq> -1 \<longrightarrow> x \<in> \<V>"
  proof (intro allI impI)
    fix x assume "dist_lookup (dist_upd (dij_dist st) hv nv) x \<noteq> -1"
    thus "x \<in> \<V>" using reachV hvV nvne unfolding duf by (auto split: if_splits)
  qed
  have curr': "\<forall>u'. dij_curr st' = Some u' \<longrightarrow> u' \<in> \<V>" using curV dc by simp
  let ?r = "relax_edge u (dist_lookup (dij_dist st) u) e st'"
  consider (skip) "seen_isin (dij_seen st) hv \<or> \<not> allowed_edge e \<or> (dist_lookup (dij_dist st) hv \<noteq> -1 \<and> \<not> nv < dist_lookup (dij_dist st) hv)"
    | (ins) "\<not> seen_isin (dij_seen st) hv \<and> allowed_edge e \<and> dist_lookup (dij_dist st) hv = -1"
    | (dec) "\<not> seen_isin (dij_seen st) hv \<and> allowed_edge e \<and> dist_lookup (dij_dist st) hv \<noteq> -1 \<and> nv < dist_lookup (dij_dist st) hv"
    by argo
  then show ?thesis
  proof cases
    case skip
    then have "?r = st'" by (auto simp: relax_edge_def Let_def hv_def[symmetric] nv_def[symmetric] st'_def)
    then show ?thesis unfolding upd_eq using a(3) by (simp add: invar_2_def st'_def)
  next
    case ins
    have hv_ns: "hv \<notin> seen_abstract (dij_seen st)" using ins isin by simp
    have notin': "\<nexists>k. (hv,k) \<in> queue_abstract (dij_heap st)" using coupD ins by blast
    have notinK: "\<And>k. (hv,k) \<notin> queue_abstract (dij_heap st)" using notin' by blast
    have rr: "?r = st' \<lparr> dij_dist := dist_upd (dij_dist st) hv nv, dij_parent := parent_upd (dij_parent st') hv (Some e), dij_heap := queue_insert (dij_heap st) hv nv \<rparr>"
      using ins by (simp add: relax_edge_def Let_def hv_def[symmetric] nv_def[symmetric] st'_def)
    have qins: "queue_abstract (queue_insert (dij_heap st) hv nv) = queue_abstract (dij_heap st) \<union> {(hv,nv)}"
      using heap.queue_insert(2)[OF qi hvV notin'] .
    have coup': "\<forall>x k. ((x,k) \<in> queue_abstract (queue_insert (dij_heap st) hv nv)) = (x \<notin> seen_abstract (dij_seen st) \<and> dist_lookup (dist_upd (dij_dist st) hv nv) x \<noteq> -1 \<and> k = dist_lookup (dist_upd (dij_dist st) hv nv) x)"
    proof (intro allI)
      fix x k
      show "((x,k) \<in> queue_abstract (queue_insert (dij_heap st) hv nv)) = (x \<notin> seen_abstract (dij_seen st) \<and> dist_lookup (dist_upd (dij_dist st) hv nv) x \<noteq> -1 \<and> k = dist_lookup (dist_upd (dij_dist st) hv nv) x)"
      proof (cases "x = hv")
        case True
        have mem: "((x,k) \<in> queue_abstract (queue_insert (dij_heap st) hv nv)) = (k = nv)"
          unfolding qins using notinK True by blast
        have dfx: "dist_lookup (dist_upd (dij_dist st) hv nv) x = nv" using True duf by simp
        show ?thesis unfolding mem dfx using True nvne hv_ns by blast
      next
        case False
        have mem: "((x,k) \<in> queue_abstract (queue_insert (dij_heap st) hv nv)) = ((x,k) \<in> queue_abstract (dij_heap st))"
          unfolding qins using False by blast
        have dfx: "dist_lookup (dist_upd (dij_dist st) hv nv) x = dist_lookup (dij_dist st) x" using False duf by simp
        show ?thesis unfolding mem dfx using coupD coupI by blast
      qed
    qed
    show ?thesis unfolding upd_eq rr
      apply (rule invar_2_intro)
      subgoal using heap.queue_insert(1)[OF qi hvV notin'] by simp
      subgoal using si ds by simp
      subgoal using sV ds by simp
      subgoal using reach' by simp
      subgoal using curr' by simp
      subgoal using coup' ds by simp
      done
  next
    case dec
    have hv_ns: "hv \<notin> seen_abstract (dij_seen st)" using dec isin by simp
    have vin: "(hv, dist_lookup (dij_dist st) hv) \<in> queue_abstract (dij_heap st)" using coupI hv_ns dec by blast
    have kd: "\<And>k'. (hv,k') \<in> queue_abstract (dij_heap st) \<Longrightarrow> k' = dist_lookup (dij_dist st) hv"
      using coupD by blast
    have rr: "?r = st' \<lparr> dij_dist := dist_upd (dij_dist st) hv nv, dij_parent := parent_upd (dij_parent st') hv (Some e), dij_heap := queue_decrease_key (dij_heap st) hv nv \<rparr>"
      using dec by (simp add: relax_edge_def Let_def hv_def[symmetric] nv_def[symmetric] st'_def)
    have qdec: "queue_abstract (queue_decrease_key (dij_heap st) hv nv) = queue_abstract (dij_heap st) - {(hv, dist_lookup (dij_dist st) hv)} \<union> {(hv, nv)}"
      using heap.queue_decrease_key(2)[OF qi hvV vin] dec by simp
    have coup': "\<forall>x k. ((x,k) \<in> queue_abstract (queue_decrease_key (dij_heap st) hv nv)) = (x \<notin> seen_abstract (dij_seen st) \<and> dist_lookup (dist_upd (dij_dist st) hv nv) x \<noteq> -1 \<and> k = dist_lookup (dist_upd (dij_dist st) hv nv) x)"
    proof (intro allI)
      fix x k
      show "((x,k) \<in> queue_abstract (queue_decrease_key (dij_heap st) hv nv)) = (x \<notin> seen_abstract (dij_seen st) \<and> dist_lookup (dist_upd (dij_dist st) hv nv) x \<noteq> -1 \<and> k = dist_lookup (dist_upd (dij_dist st) hv nv) x)"
      proof (cases "x = hv")
        case True
        have mem: "((x,k) \<in> queue_abstract (queue_decrease_key (dij_heap st) hv nv)) = (k = nv)"
          unfolding qdec using kd True by blast
        have dfx: "dist_lookup (dist_upd (dij_dist st) hv nv) x = nv" using True duf by simp
        show ?thesis unfolding mem dfx using True nvne hv_ns by blast
      next
        case False
        have mem: "((x,k) \<in> queue_abstract (queue_decrease_key (dij_heap st) hv nv)) = ((x,k) \<in> queue_abstract (dij_heap st))"
          unfolding qdec using False by blast
        have dfx: "dist_lookup (dist_upd (dij_dist st) hv nv) x = dist_lookup (dij_dist st) x" using False duf by simp
        show ?thesis unfolding mem dfx using coupD coupI by blast
      qed
    qed
    show ?thesis unfolding upd_eq rr
      apply (rule invar_2_intro)
      subgoal using heap.queue_decrease_key(1)[OF qi hvV vin] dec by simp
      subgoal using si ds by simp
      subgoal using sV ds by simp
      subgoal using reach' by simp
      subgoal using curr' by simp
      subgoal using coup' ds by simp
      done
  qed
qed


subsection \<open>Well-formedness is preserved\<close>

text \<open>The array, graph and source-iterator operations are specified only inside their universe
      \<open>\<V>\<close>, so preserving well-formedness needs that the vertex being scanned or settled, the head of
      the relaxed edge, and the loaded source are graph vertices. These facts come from the coupling
      invariant (a popped vertex lies in the queue's universe) and from the source-phase invariant.\<close>

lemma invar_1_holds_relax[invar_holds_intros]: "\<lbrakk>dijkstra_call_relax_conds st; invar_1 st; invar_2 st\<rbrakk> \<Longrightarrow> invar_1 (dijkstra_upd_relax st)"
proof -
  assume a: "dijkstra_call_relax_conds st" "invar_1 st" "invar_2 st"
  obtain u where cu: "dij_curr st = Some u" and oh: "out_has (dij_graph st) u"
    using a(1) by (auto elim!: dijkstra_call_relax_condsE)
  have gi: "out_graph_inv (dij_graph st)" using a(2) by (auto elim!: invar_1_props)
  have uV: "u \<in> \<V>" using a(3) cu by (auto elim!: invar_2_props)
  have hV: "snd (out_current (dij_graph st) u) \<in> \<V>" using snd_E_V[OF out_current_edge[OF gi uV oh]] .
  show ?thesis using a(2) gi uV oh hV
    by (auto simp: dijkstra_upd_relax_def cu elim!: invar_1_props intro!: invar_1_intro out_graph_inv_move)
qed

lemma invar_1_holds_finish[invar_holds_intros]: "\<lbrakk>dijkstra_call_finish_conds st; invar_1 st\<rbrakk> \<Longrightarrow> invar_1 (dijkstra_upd_finish st)"
  by (auto simp: dijkstra_upd_finish_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_1_holds_init[invar_holds_intros]: "\<lbrakk>dijkstra_call_init_conds st; invar_1 st; invar_3 st\<rbrakk> \<Longrightarrow> invar_1 (dijkstra_upd_init st)"
proof -
  assume a: "dijkstra_call_init_conds st" "invar_1 st" "invar_3 st"
  have srch: "src_has (dij_srcs st)" using a(1) by (auto elim!: dijkstra_call_init_condsE)
  have sinv: "src_invar (dij_srcs st)" using a(2) by (auto elim!: invar_1_props)
  have sabs: "src_abstract (dij_srcs st) \<subseteq> \<V>" using a(3) by (auto elim!: invar_3_props)
  have rem: "src_remaining (dij_srcs st) \<noteq> {}" using srch sinv sources.has_current by auto
  have vV: "src_current (dij_srcs st) \<in> \<V>"
    using sources.current_element[OF sinv rem] sources.iterable_set_abstract(2)[OF sinv] sabs by blast
  show ?thesis using a(2) vV sinv rem
    by (auto simp: dijkstra_upd_init_def elim!: invar_1_props intro!: invar_1_intro sources.move_on_invar)
qed

lemma invar_1_holds_skip[invar_holds_intros]: "\<lbrakk>dijkstra_call_skip_conds st; invar_1 st\<rbrakk> \<Longrightarrow> invar_1 (dijkstra_upd_skip st)"
  by (auto simp: dijkstra_upd_skip_def elim!: invar_props_elims intro!: invar_props_intros split: prod.splits)

lemma invar_1_holds_settle[invar_holds_intros]: "\<lbrakk>dijkstra_call_settle_conds st; invar_1 st; invar_2 st\<rbrakk> \<Longrightarrow> invar_1 (dijkstra_upd_settle st)"
proof -
  assume a: "dijkstra_call_settle_conds st" "invar_1 st" "invar_2 st"
  obtain h2 u where hu: "queue_extract_min (dij_heap st) = (h2, Some u)"
    using a(1) by (auto elim!: dijkstra_call_settle_condsE)
  have qi: "queue_invar (dij_heap st)" using a(3) by (auto elim!: invar_2_props)
  have uV: "u \<in> \<V>" using heap.queue_extract_min_universe[OF qi hu] .
  show ?thesis using a(2) uV
    by (auto simp: dijkstra_upd_settle_def hu Let_def elim!: invar_1_props intro!: invar_1_intro out_graph_inv_reset)
qed

lemma invar_1_holds_done[invar_holds_intros]: "\<lbrakk>dijkstra_ret_done_conds st; invar_1 st\<rbrakk> \<Longrightarrow> invar_1 (dijkstra_ret_done st)"
  by (auto simp: dijkstra_ret_done_def elim!: invar_props_elims intro!: invar_props_intros split: prod.splits)

lemma invar_1_holds_found[invar_holds_intros]: "\<lbrakk>dijkstra_ret_found_conds st; invar_1 st\<rbrakk> \<Longrightarrow> invar_1 (dijkstra_ret_found st)"
  by (simp add: dijkstra_ret_found_def invar_1_def Let_def split: prod.splits)


subsection \<open>The coupling invariant holds throughout, and initially\<close>

lemma invar_1_holds[invar_holds_intros]:
  assumes "dijkstra_dom st" "invar_1 st" "invar_2 st" "invar_3 st" "invar_4 st"
  shows "invar_1 (dijkstra st)"
  using assms(2-)
proof(induction rule: dijkstra_induct[OF assms(1)])
  case IH: (1 st)
  show ?case
    apply(rule dijkstra_cases[where st = st])
    by (auto intro!: IH(2-) intro: invar_holds_intros simp: dijkstra_simps[OF IH(1)])
qed

lemma invar_1_initial[invar_holds_intros]: "invar_1 initial_state"
  by (auto simp: initial_state_def invar_1_def graph_inv dist_init_invar parent_init_invar srcs_invar)

lemma invar_2_holds[invar_holds_intros]:
  assumes "dijkstra_dom st" "invar_1 st" "invar_2 st" "invar_3 st" "invar_4 st"
  shows "invar_2 (dijkstra st)"
  using assms(2-)
proof(induction rule: dijkstra_induct[OF assms(1)])
  case IH: (1 st)
  show ?case
    apply(rule dijkstra_cases[where st = st])
    by (auto intro!: IH(2-) intro: invar_holds_intros simp: dijkstra_simps[OF IH(1)])
qed

lemma invar_3_holds[invar_holds_intros]:
  assumes "dijkstra_dom st" "invar_1 st" "invar_2 st" "invar_3 st" "invar_4 st"
  shows "invar_3 (dijkstra st)"
  using assms(2-)
proof(induction rule: dijkstra_induct[OF assms(1)])
  case IH: (1 st)
  show ?case
    apply(rule dijkstra_cases[where st = st])
    by (auto intro!: IH(2-) intro: invar_holds_intros simp: dijkstra_simps[OF IH(1)])
qed

lemma invar_4_holds[invar_holds_intros]:
  assumes "dijkstra_dom st" "invar_1 st" "invar_2 st" "invar_3 st" "invar_4 st"
  shows "invar_4 (dijkstra st)"
  using assms(2-)
proof(induction rule: dijkstra_induct[OF assms(1)])
  case IH: (1 st)
  show ?case
    apply(rule dijkstra_cases[where st = st])
    by (auto intro!: IH(2-) intro: invar_holds_intros simp: dijkstra_simps[OF IH(1)])
qed

lemma invar_2_initial[invar_holds_intros]: "invar_2 initial_state"
  by (auto simp: initial_state_def invar_2_def heap.queue_empty seen_set.fixed_univ_set_empty dist_init_inf)

lemma invar_3_initial[invar_holds_intros]: "invar_3 initial_state"
  by (auto simp: initial_state_def invar_3_def srcs_in_V dist_init_inf)

lemma invar_4_initial[invar_holds_intros]: "invar_4 initial_state"
  by (auto simp: initial_state_def invar_4_def seen_set.fixed_univ_set_empty)

text \<open>The abstract-datatype well-formedness and the queue--distance coupling therefore hold of the
      computed state (given termination, established next): the settled set carries the tentative
      distances exactly.\<close>


subsection \<open>Termination\<close>

text \<open>The loop advances one element per step, so termination is by a lexicographic measure: the
      number of \<^emph>\<open>unsettled\<close> vertices decreases when a vertex is settled; the number of unprocessed
      \<^emph>\<open>sources\<close> decreases when one is loaded; and the size of the current vertex's \<^emph>\<open>edge cursor\<close>
      decreases while scanning (and drops to zero on finishing). The stale-\<open>skip\<close> branch never fires,
      by the coupling. This follows the \<open>DFS.thy\<close>/\<open>BFS_2.thy\<close> \<open><*mlex*>\<close> pattern.\<close>

named_theorems termination_intros

definition "m_unseen st = card (\<V> - seen_abstract (dij_seen st))"
definition "m_srcs st = card (src_remaining (dij_srcs st))"
definition "m_scan st = (case dij_curr st of Some u \<Rightarrow> card (out_remaining (dij_graph st) u) + 1 | None \<Rightarrow> 0)"
definition "dijkstra_term_rel = m_unseen <*mlex*> m_srcs <*mlex*> m_scan <*mlex*> {}"

lemma in_prod_relI[intro!,termination_intros]:
  "\<lbrakk>f1 a = f1 a'; (a, a') \<in> f2 <*mlex*> r\<rbrakk> \<Longrightarrow> (a,a') \<in> (f1 <*mlex*> f2 <*mlex*> r)"
   by (simp add: mlex_iff)+

lemma wf_term_rel: "wf dijkstra_term_rel"
  by (auto simp: wf_mlex dijkstra_term_rel_def)

lemma settle_terminates[termination_intros]:
  "\<lbrakk>dijkstra_call_settle_conds st; invar_1 st; invar_2 st\<rbrakk> \<Longrightarrow> (dijkstra_upd_settle st, st) \<in> m_unseen <*mlex*> r"
proof -
  assume a: "dijkstra_call_settle_conds st" "invar_1 st" "invar_2 st"
  obtain h2 u where hu: "queue_extract_min (dij_heap st) = (h2, Some u)" "\<not> seen_isin (dij_seen st) u"
    using a(1) by (auto elim!: dijkstra_call_settle_condsE)
  have qi: "queue_invar (dij_heap st)" and si: "seen_invar (dij_seen st)"
    and reachV: "\<forall>x. dist_lookup (dij_dist st) x \<noteq> -1 \<longrightarrow> x \<in> \<V>"
    and coup: "\<forall>x k. ((x,k) \<in> queue_abstract (dij_heap st)) = (x \<notin> seen_abstract (dij_seen st) \<and> dist_lookup (dij_dist st) x \<noteq> -1 \<and> k = dist_lookup (dij_dist st) x)"
    using a(3) by (auto elim!: invar_2_props)
  obtain k where uk: "(u,k) \<in> queue_abstract (dij_heap st)"
    using heap.queue_extract_min(2)[OF qi, of u] hu(1) by simp blast
  have uV: "u \<in> \<V>" using reachV coup uk by blast
  have uns: "u \<notin> seen_abstract (dij_seen st)" using hu(2) si seen_set.fixed_univ_set_isin by auto
  have sub: "(\<V> - insert u (seen_abstract (dij_seen st))) \<subset> (\<V> - seen_abstract (dij_seen st))"
    using uV uns by blast
  have "m_unseen (dijkstra_upd_settle st) < m_unseen st"
    unfolding dijkstra_upd_settle_def hu(1) prod.case Let_def option.sel m_unseen_def
    using seen_set.fixed_univ_set_insert(2)[OF si uV] psubset_card_mono[OF _ sub] \<V>_finite by simp
  thus ?thesis by (rule mlex_less)
qed

lemma m_unseen_init[termination_intros]: "m_unseen (dijkstra_upd_init st) = m_unseen st"
  by (simp add: dijkstra_upd_init_def insert_source_def m_unseen_def)

lemma m_unseen_relax[termination_intros]: "m_unseen (dijkstra_upd_relax st) = m_unseen st"
  by (simp add: dijkstra_upd_relax_def Let_def m_unseen_def)

lemma m_unseen_finish[termination_intros]: "m_unseen (dijkstra_upd_finish st) = m_unseen st"
  by (simp add: dijkstra_upd_finish_def m_unseen_def)

lemma m_srcs_relax[termination_intros]: "m_srcs (dijkstra_upd_relax st) = m_srcs st"
  by (simp add: dijkstra_upd_relax_def Let_def m_srcs_def)

lemma m_srcs_finish[termination_intros]: "m_srcs (dijkstra_upd_finish st) = m_srcs st"
  by (simp add: dijkstra_upd_finish_def m_srcs_def)

lemma init_terminates[termination_intros]:
  "\<lbrakk>dijkstra_call_init_conds st; invar_1 st; invar_3 st\<rbrakk> \<Longrightarrow> (dijkstra_upd_init st, st) \<in> m_srcs <*mlex*> r"
proof -
  assume a: "dijkstra_call_init_conds st" "invar_1 st" "invar_3 st"
  have srch: "src_has (dij_srcs st)" using a(1) by (auto elim!: dijkstra_call_init_condsE)
  have sinv: "src_invar (dij_srcs st)" using a(2) by (auto elim!: invar_props_elims)
  have sabs: "src_abstract (dij_srcs st) \<subseteq> \<V>" using a(3) by (auto elim!: invar_props_elims)
  have rem: "src_remaining (dij_srcs st) \<noteq> {}" using srch sinv sources.has_current by auto
  have vrem: "src_current (dij_srcs st) \<in> src_remaining (dij_srcs st)" using sources.current_element[OF sinv rem] .
  have "src_remaining (dij_srcs st) \<subseteq> \<V>" using sabs sources.iterable_set_abstract(2)[OF sinv] by blast
  then have fin: "finite (src_remaining (dij_srcs st))" using \<V>_finite by (rule finite_subset)
  have sub: "src_remaining (src_move (dij_srcs st)) \<subset> src_remaining (dij_srcs st)"
    using sources.move_on(2)[OF sinv rem] vrem by auto
  have "m_srcs (dijkstra_upd_init st) < m_srcs st"
    unfolding dijkstra_upd_init_def insert_source_def m_srcs_def
    using psubset_card_mono[OF fin sub] by simp
  thus ?thesis by (rule mlex_less)
qed

lemma relax_terminates[termination_intros]:
  "\<lbrakk>dijkstra_call_relax_conds st; invar_1 st; invar_2 st\<rbrakk> \<Longrightarrow> (dijkstra_upd_relax st, st) \<in> m_scan <*mlex*> r"
proof -
  assume a: "dijkstra_call_relax_conds st" "invar_1 st" "invar_2 st"
  obtain u where cu: "dij_curr st = Some u" and oh: "out_has (dij_graph st) u"
    using a(1) by (auto elim!: dijkstra_call_relax_condsE)
  have gi: "out_graph_inv (dij_graph st)" using a(2) by (auto elim!: invar_props_elims)
  have inv: "out_invar (dij_graph st)" using gi by (simp add: out_graph_inv_def)
  have uV: "u \<in> \<V>" using a(3) cu by (auto elim!: invar_2_props)
  have rem: "out_remaining (dij_graph st) u \<noteq> {}" using inv uV oh out_has_remaining by auto
  have vcur: "out_current (dij_graph st) u \<in> out_remaining (dij_graph st) u" using outg.idx_current[OF inv uV rem] .
  have fin: "finite (out_remaining (dij_graph st) u)" using finite_out_remaining[OF gi uV] .
  have sub: "out_remaining (out_move (dij_graph st) u) u \<subset> out_remaining (dij_graph st) u"
    using outg.idx_move_remaining[OF inv uV rem] vcur by auto
  have "m_scan (dijkstra_upd_relax st) < m_scan st"
    using psubset_card_mono[OF fin sub] cu by (simp add: dijkstra_upd_relax_def Let_def m_scan_def)
  thus ?thesis by (rule mlex_less)
qed

lemma finish_terminates[termination_intros]:
  "\<lbrakk>dijkstra_call_finish_conds st; invar_1 st; invar_2 st\<rbrakk> \<Longrightarrow> (dijkstra_upd_finish st, st) \<in> m_scan <*mlex*> r"
proof -
  assume a: "dijkstra_call_finish_conds st" "invar_1 st" "invar_2 st"
  obtain u where cu: "dij_curr st = Some u" and noh: "\<not> out_has (dij_graph st) u"
    using a(1) by (auto elim!: dijkstra_call_finish_condsE)
  have inv: "out_invar (dij_graph st)" using a(2) by (auto elim!: invar_1_props simp: out_graph_inv_def)
  have uV: "u \<in> \<V>" using a(3) cu by (auto elim!: invar_2_props)
  have rem0: "out_remaining (dij_graph st) u = {}" using noh inv uV outg.idx_has by auto
  have "m_scan (dijkstra_upd_finish st) < m_scan st"
    using rem0 cu by (simp add: dijkstra_upd_finish_def m_scan_def)
  thus ?thesis by (rule mlex_less)
qed

lemma in_dijkstra_term_rel'[termination_intros]:
  "\<lbrakk>dijkstra_call_settle_conds st; invar_1 st; invar_2 st\<rbrakk> \<Longrightarrow> (dijkstra_upd_settle st, st) \<in> dijkstra_term_rel"
  "\<lbrakk>dijkstra_call_init_conds st; invar_1 st; invar_3 st\<rbrakk> \<Longrightarrow> (dijkstra_upd_init st, st) \<in> dijkstra_term_rel"
  "\<lbrakk>dijkstra_call_relax_conds st; invar_1 st; invar_2 st\<rbrakk> \<Longrightarrow> (dijkstra_upd_relax st, st) \<in> dijkstra_term_rel"
  "\<lbrakk>dijkstra_call_finish_conds st; invar_1 st; invar_2 st\<rbrakk> \<Longrightarrow> (dijkstra_upd_finish st, st) \<in> dijkstra_term_rel"
  by (simp add: dijkstra_term_rel_def termination_intros)+

lemma skip_contra: "\<lbrakk>dijkstra_call_skip_conds st; invar_2 st\<rbrakk> \<Longrightarrow> False"
proof -
  assume a: "dijkstra_call_skip_conds st" "invar_2 st"
  obtain h2 u where hu: "queue_extract_min (dij_heap st) = (h2, Some u)" "seen_isin (dij_seen st) u"
    using a(1) by (auto elim!: dijkstra_call_skip_condsE)
  have qi: "queue_invar (dij_heap st)" and si: "seen_invar (dij_seen st)"
    and coup: "\<forall>x k. ((x,k) \<in> queue_abstract (dij_heap st)) = (x \<notin> seen_abstract (dij_seen st) \<and> dist_lookup (dij_dist st) x \<noteq> -1 \<and> k = dist_lookup (dij_dist st) x)"
    using a(2) by (auto elim!: invar_2_props)
  have "\<exists>k. (u,k) \<in> queue_abstract (dij_heap st)"
    using heap.queue_extract_min(2)[OF qi, of u] hu(1) by simp blast
  moreover have "u \<in> seen_abstract (dij_seen st)" using si hu(2) seen_set.fixed_univ_set_isin by auto
  ultimately show False using coup by blast
qed

lemma dijkstra_terminates[termination_intros]:
  assumes "invar_1 st" "invar_2 st" "invar_3 st" "invar_4 st"
  shows "dijkstra_dom st"
  using wf_term_rel assms
proof(induction rule: wf_induct_rule)
  case (less x)
  show ?case
    by (rule dijkstra_domintros)
       (auto intro!: invar_holds_intros less in_dijkstra_term_rel' dest: skip_contra)
qed

lemma initial_state_props[invar_holds_intros, termination_intros]:
  "invar_1 initial_state" "invar_2 initial_state" "invar_3 initial_state" "invar_4 initial_state"
  "dijkstra_dom initial_state"
  by (auto intro!: termination_intros invar_holds_intros)


subsection \<open>Soundness: computed distances are realised by paths\<close>

text \<open>Reusing the weighted-path development of \<open>Multigraph_Weighted_Paths\<close>: a distinct path of
      non-negative edges has non-negative weight, and relaxing an edge \<open>e\<close> out of a vertex whose
      distance is bounded by \<open>du\<close> bounds the head's distance by \<open>du + w e\<close> (splitting on whether the
      head already lies on the shortest path to the tail).\<close>

lemma weight_nonneg: "set p \<subseteq> Ea \<Longrightarrow> 0 \<le> weight w p"
  by (induction p) (auto simp: w_nonneg)

lemma distance_set_edge_bound:
  assumes "finite S" "e \<in> Ea" "ag.distance_set w S (fst e) \<le> ereal du"
  shows "ag.distance_set w S (snd e) \<le> ereal (du + w e)"
proof -
  have lt: "ag.distance_set w S (fst e) < \<infinity>" using assms(3) order_le_less_trans by fastforce
  obtain p s where sP: "s \<in> S" "ag.is_shortest_path w p s (fst e)" "ag.distance w s (fst e) = ag.distance_set w S (fst e)"
    by (rule ag_dist_set_less_infty_get_path[OF assms(1) lt])
  have pb: "ag.path_bet p s (fst e)" and dp: "distinct p" and wp: "ag.distance w s (fst e) = ereal (weight w p)"
    using sP(2) by (auto simp: ag.is_shortest_path_def)
  have wple: "weight w p \<le> du" using wp sP(3) assms(3) by simp
  have pE: "set p \<subseteq> Ea" using pb ag_path_bet_edges_subset by blast
  have we0: "0 \<le> w e" using assms(2) w_nonneg by blast
  show ?thesis
  proof (cases "e \<in> set p")
    case False
    have "ag.distance_set w S (snd e) \<le> ereal (weight w (p @ [e]))"
      using ag_distance_set_le_path[OF sP(1) ag_path_bet_snocI[OF pb assms(2)]] dp False by simp
    also have "... = ereal (weight w p + w e)" by (simp add: weight_snoc)
    also have "... \<le> ereal (du + w e)" using wple by simp
    finally show ?thesis .
  next
    case True
    obtain p1 p2 where dec: "p = p1 @ e # p2" and pb1: "ag.path_bet p1 s (fst e)"
      using ag_path_bet_edge_split[OF pb True] by blast
    have peq: "p = (p1 @ [e]) @ p2" using dec by simp
    have p2E: "set p2 \<subseteq> Ea" using pE dec by auto
    have "distinct (p1 @ [e])" using dp dec by auto
    then have "ag.distance_set w S (snd e) \<le> ereal (weight w (p1 @ [e]))"
      using ag_distance_set_le_path[OF sP(1) ag_path_bet_snocI[OF pb1 assms(2)]] by simp
    also have "weight w (p1 @ [e]) \<le> weight w p"
      using peq weight_nonneg[OF p2E] by simp
    also have "... \<le> du + w e" using wple we0 by simp
    finally show ?thesis by simp
  qed
qed


subsubsection \<open>The source set is constant, and distances stay unchanged on the non-updating branches\<close>

lemma dijkstra_upd_relax_srcs[simp]: "dij_srcs (dijkstra_upd_relax st) = dij_srcs st"
  by (simp add: dijkstra_upd_relax_def Let_def)
lemma dijkstra_upd_finish_srcs[simp]: "dij_srcs (dijkstra_upd_finish st) = dij_srcs st"
  by (simp add: dijkstra_upd_finish_def)
lemma dijkstra_upd_settle_srcs[simp]: "dij_srcs (dijkstra_upd_settle st) = dij_srcs st"
  by (simp add: dijkstra_upd_settle_def Let_def split: prod.splits)
lemma dijkstra_upd_skip_srcs[simp]: "dij_srcs (dijkstra_upd_skip st) = dij_srcs st"
  by (simp add: dijkstra_upd_skip_def split: prod.splits)
lemma dijkstra_ret_found_srcs[simp]: "dij_srcs (dijkstra_ret_found st) = dij_srcs st"
  by (simp add: dijkstra_ret_found_def Let_def split: prod.splits)
lemma dijkstra_ret_done_srcs[simp]: "dij_srcs (dijkstra_ret_done st) = dij_srcs st"
  by (simp add: dijkstra_ret_done_def)
lemma dijkstra_upd_init_srcs[simp]: "dij_srcs (dijkstra_upd_init st) = src_move (dij_srcs st)"
  by (simp add: dijkstra_upd_init_def insert_source_def)

lemma dijkstra_upd_finish_dist[simp]: "dij_dist (dijkstra_upd_finish st) = dij_dist st"
  by (simp add: dijkstra_upd_finish_def)
lemma dijkstra_upd_settle_dist[simp]: "dij_dist (dijkstra_upd_settle st) = dij_dist st"
  by (simp add: dijkstra_upd_settle_def Let_def split: prod.splits)
lemma dijkstra_upd_skip_dist[simp]: "dij_dist (dijkstra_upd_skip st) = dij_dist st"
  by (simp add: dijkstra_upd_skip_def split: prod.splits)
lemma dijkstra_ret_found_dist[simp]: "dij_dist (dijkstra_ret_found st) = dij_dist st"
  by (simp add: dijkstra_ret_found_def Let_def split: prod.splits)
lemma dijkstra_ret_done_dist[simp]: "dij_dist (dijkstra_ret_done st) = dij_dist st"
  by (simp add: dijkstra_ret_done_def)


subsubsection \<open>The abstract source set is invariant\<close>

definition "invar_6 st \<longleftrightarrow> src_abstract (dij_srcs st) = src_abstract srcs"

lemma invar_6_props[invar_props_elims]: "invar_6 st \<Longrightarrow> (src_abstract (dij_srcs st) = src_abstract srcs \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_6_def)
lemma invar_6_intro[invar_props_intros]: "src_abstract (dij_srcs st) = src_abstract srcs \<Longrightarrow> invar_6 st"
  by (auto simp: invar_6_def)

lemma invar_6_holds_relax[invar_holds_intros]: "\<lbrakk>dijkstra_call_relax_conds st; invar_6 st\<rbrakk> \<Longrightarrow> invar_6 (dijkstra_upd_relax st)"
  by (simp add: invar_6_def)
lemma invar_6_holds_finish[invar_holds_intros]: "\<lbrakk>dijkstra_call_finish_conds st; invar_6 st\<rbrakk> \<Longrightarrow> invar_6 (dijkstra_upd_finish st)"
  by (simp add: invar_6_def)
lemma invar_6_holds_done[invar_holds_intros]: "\<lbrakk>dijkstra_ret_done_conds st; invar_6 st\<rbrakk> \<Longrightarrow> invar_6 (dijkstra_ret_done st)"
  by (simp add: invar_6_def)
lemma invar_6_holds_skip[invar_holds_intros]: "\<lbrakk>dijkstra_call_skip_conds st; invar_6 st\<rbrakk> \<Longrightarrow> invar_6 (dijkstra_upd_skip st)"
  by (simp add: invar_6_def)
lemma invar_6_holds_settle[invar_holds_intros]: "\<lbrakk>dijkstra_call_settle_conds st; invar_6 st\<rbrakk> \<Longrightarrow> invar_6 (dijkstra_upd_settle st)"
  by (simp add: invar_6_def)
lemma invar_6_holds_found[invar_holds_intros]: "\<lbrakk>dijkstra_ret_found_conds st; invar_6 st\<rbrakk> \<Longrightarrow> invar_6 (dijkstra_ret_found st)"
  by (simp add: invar_6_def)

lemma invar_6_holds_init[invar_holds_intros]: "\<lbrakk>dijkstra_call_init_conds st; invar_1 st; invar_6 st\<rbrakk> \<Longrightarrow> invar_6 (dijkstra_upd_init st)"
proof -
  assume a: "dijkstra_call_init_conds st" "invar_1 st" "invar_6 st"
  have srch: "src_has (dij_srcs st)" using a(1) by (auto elim!: dijkstra_call_init_condsE)
  have sinv: "src_invar (dij_srcs st)" using a(2) by (auto elim!: invar_props_elims)
  have rem: "src_remaining (dij_srcs st) \<noteq> {}" using srch sinv sources.has_current by auto
  show ?thesis using a(3) by (simp add: invar_6_def sources.move_on(1)[OF sinv rem])
qed

lemma invar_6_holds[invar_holds_intros]:
  assumes "dijkstra_dom st" "invar_1 st" "invar_2 st" "invar_3 st" "invar_4 st" "invar_6 st"
  shows "invar_6 (dijkstra st)"
  using assms(2-)
proof(induction rule: dijkstra_induct[OF assms(1)])
  case IH: (1 st)
  show ?case
    apply(rule dijkstra_cases[where st = st])
    by (auto intro!: IH(2-) intro: invar_holds_intros simp: dijkstra_simps[OF IH(1)])
qed

lemma invar_6_initial[invar_holds_intros]: "invar_6 initial_state"
  by (auto simp: initial_state_def invar_6_def)


subsubsection \<open>The soundness invariant: reached vertices are over-approximated\<close>

definition "invar_5 st \<longleftrightarrow> (\<forall>v. dist_lookup (dij_dist st) v \<noteq> -1 \<longrightarrow> ag.distance_set w (src_abstract srcs) v \<le> ereal (dist_lookup (dij_dist st) v))"

lemma invar_5_props[invar_props_elims]: "invar_5 st \<Longrightarrow> (\<lbrakk>\<forall>v. dist_lookup (dij_dist st) v \<noteq> -1 \<longrightarrow> ag.distance_set w (src_abstract srcs) v \<le> ereal (dist_lookup (dij_dist st) v)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_5_def)
lemma invar_5_intro[invar_props_intros]: "\<forall>v. dist_lookup (dij_dist st) v \<noteq> -1 \<longrightarrow> ag.distance_set w (src_abstract srcs) v \<le> ereal (dist_lookup (dij_dist st) v) \<Longrightarrow> invar_5 st"
  by (auto simp: invar_5_def)

lemma invar_5_holds_finish[invar_holds_intros]: "\<lbrakk>dijkstra_call_finish_conds st; invar_5 st\<rbrakk> \<Longrightarrow> invar_5 (dijkstra_upd_finish st)"
  by (simp add: invar_5_def)
lemma invar_5_holds_settle[invar_holds_intros]: "\<lbrakk>dijkstra_call_settle_conds st; invar_5 st\<rbrakk> \<Longrightarrow> invar_5 (dijkstra_upd_settle st)"
  by (simp add: invar_5_def)
lemma invar_5_holds_skip[invar_holds_intros]: "\<lbrakk>dijkstra_call_skip_conds st; invar_5 st\<rbrakk> \<Longrightarrow> invar_5 (dijkstra_upd_skip st)"
  by (simp add: invar_5_def)
lemma invar_5_holds_done[invar_holds_intros]: "\<lbrakk>dijkstra_ret_done_conds st; invar_5 st\<rbrakk> \<Longrightarrow> invar_5 (dijkstra_ret_done st)"
  by (simp add: invar_5_def)
lemma invar_5_holds_found[invar_holds_intros]: "\<lbrakk>dijkstra_ret_found_conds st; invar_5 st\<rbrakk> \<Longrightarrow> invar_5 (dijkstra_ret_found st)"
  by (simp add: invar_5_def)

lemma invar_5_holds_init[invar_holds_intros]: "\<lbrakk>dijkstra_call_init_conds st; invar_1 st; invar_5 st; invar_6 st\<rbrakk> \<Longrightarrow> invar_5 (dijkstra_upd_init st)"
proof -
  assume a: "dijkstra_call_init_conds st" "invar_1 st" "invar_5 st" "invar_6 st"
  have srch: "src_has (dij_srcs st)" using a(1) by (auto elim!: dijkstra_call_init_condsE)
  have sinv: "src_invar (dij_srcs st)" and dinv: "dist_invar (dij_dist st)" using a(2) by (auto elim!: invar_props_elims)
  have I5: "\<forall>v. dist_lookup (dij_dist st) v \<noteq> -1 \<longrightarrow> ag.distance_set w (src_abstract srcs) v \<le> ereal (dist_lookup (dij_dist st) v)"
    using a(3) by (auto elim!: invar_props_elims)
  have sabs: "src_abstract (dij_srcs st) = src_abstract srcs" using a(4) by (auto elim!: invar_props_elims)
  have rem: "src_remaining (dij_srcs st) \<noteq> {}" using srch sinv sources.has_current by auto
  define v where "v = src_current (dij_srcs st)"
  have vrem: "v \<in> src_remaining (dij_srcs st)" using sources.current_element[OF sinv rem] by (simp add: v_def)
  have vS: "v \<in> src_abstract srcs" using vrem sources.iterable_set_abstract(2)[OF sinv] sabs by blast
  have v0: "ag.distance_set w (src_abstract srcs) v \<le> 0" using ag_distance_set_le_path[OF vS, of "[]" v w]
    by (simp add: ag.path_bet_def multigraph_path_def zero_ereal_def)
  have vV: "v \<in> \<V>" using vS srcs_in_V by blast
  show ?thesis
    unfolding invar_5_def
  proof (intro allI impI)
    fix x assume ne: "dist_lookup (dij_dist (dijkstra_upd_init st)) x \<noteq> -1"
    have dupd: "dist_lookup (dij_dist (dijkstra_upd_init st)) x = (if x = v then 0 else dist_lookup (dij_dist st) x)"
      by (simp add: dijkstra_upd_init_def insert_source_def v_def dist_arr.fixed_univ_map_upd[OF dinv vV[unfolded v_def]])
    show "ag.distance_set w (src_abstract srcs) x \<le> ereal (dist_lookup (dij_dist (dijkstra_upd_init st)) x)"
    proof (cases "x = v")
      case True thus ?thesis using v0 dupd by (simp add: zero_ereal_def)
    next
      case False thus ?thesis using I5 ne dupd by simp
    qed
  qed
qed

lemma invar_5_holds_relax[invar_holds_intros]:
  "\<lbrakk>dijkstra_call_relax_conds st; invar_1 st; invar_2 st; invar_3 st; invar_5 st\<rbrakk> \<Longrightarrow> invar_5 (dijkstra_upd_relax st)"
proof -
  assume a: "dijkstra_call_relax_conds st" "invar_1 st" "invar_2 st" "invar_3 st" "invar_5 st"
  obtain u where cu: "dij_curr st = Some u" and oh: "out_has (dij_graph st) u"
    using a(1) by (auto elim!: dijkstra_call_relax_condsE)
  have gi: "out_graph_inv (dij_graph st)" and dinv: "dist_invar (dij_dist st)"
    using a(2) by (auto elim!: invar_props_elims)
  have uV: "u \<in> \<V>" using a(3) cu by (auto elim!: invar_2_props)
  have du_ne: "dist_lookup (dij_dist st) u \<noteq> -1" using a(4) cu by (auto elim!: invar_3_props)
  have I5: "\<forall>v. dist_lookup (dij_dist st) v \<noteq> -1 \<longrightarrow> ag.distance_set w (src_abstract srcs) v \<le> ereal (dist_lookup (dij_dist st) v)"
    using a(5) by (auto elim!: invar_props_elims)
  have finS: "finite (src_abstract srcs)" using srcs_in_V \<V>_finite by (auto elim: finite_subset)
  define e where "e = out_current (dij_graph st) u"
  define du where "du = dist_lookup (dij_dist st) u"
  have eE: "e \<in> \<E>" using out_current_edge[OF gi uV oh] by (simp add: e_def)
  have efst: "fst e = u" using out_current_fst[OF gi uV oh] by (simp add: e_def)
  have dsfe: "ag.distance_set w (src_abstract srcs) (fst e) \<le> ereal du" using I5 du_ne efst by (simp add: du_def)
  have heV: "snd e \<in> \<V>" using snd_E_V[OF eE] .
  have edge_bound: "allowed_edge e \<Longrightarrow> ag.distance_set w (src_abstract srcs) (snd e) \<le> ereal (du + w e)"
    using distance_set_edge_bound[OF finS _ dsfe] eE by simp
  define st' where "st' = st \<lparr> dij_graph := out_move (dij_graph st) u \<rparr>"
  have dd[simp]: "dij_dist st' = dij_dist st" and ds[simp]: "dij_seen st' = dij_seen st"
    by (simp_all add: st'_def)
  have dinv': "dist_invar (dij_dist st')" using dinv by simp
  have upd_eq: "dijkstra_upd_relax st = relax_edge u du e st'"
    by (simp add: dijkstra_upd_relax_def cu du_def e_def st'_def)
  show ?thesis
    unfolding invar_5_def
  proof (intro allI impI)
    fix x assume ne: "dist_lookup (dij_dist (dijkstra_upd_relax st)) x \<noteq> -1"
    show "ag.distance_set w (src_abstract srcs) x \<le> ereal (dist_lookup (dij_dist (dijkstra_upd_relax st)) x)"
    proof (cases "x = snd e \<and> \<not> seen_isin (dij_seen st) (snd e) \<and> allowed_edge e \<and> (dist_lookup (dij_dist st) (snd e) = -1 \<or> du + w e < dist_lookup (dij_dist st) (snd e))")
      case True
      have "dist_lookup (dij_dist (dijkstra_upd_relax st)) x = du + w e"
        using True unfolding upd_eq by (subst relax_edge_dist_at[OF dinv' heV]) auto
      thus ?thesis using edge_bound True by simp
    next
      case False
      have "dist_lookup (dij_dist (dijkstra_upd_relax st)) x = dist_lookup (dij_dist st) x"
        using False unfolding upd_eq by (subst relax_edge_dist_at[OF dinv' heV]) auto
      thus ?thesis using I5 ne by simp
    qed
  qed
qed

lemma invar_5_holds[invar_holds_intros]:
  assumes "dijkstra_dom st" "invar_1 st" "invar_2 st" "invar_3 st" "invar_4 st" "invar_5 st" "invar_6 st"
  shows "invar_5 (dijkstra st)"
  using assms(2-)
proof(induction rule: dijkstra_induct[OF assms(1)])
  case IH: (1 st)
  show ?case
    apply(rule dijkstra_cases[where st = st])
    by (auto intro!: IH(2-) intro: invar_holds_intros simp: dijkstra_simps[OF IH(1)])
qed

lemma invar_5_initial[invar_holds_intros]: "invar_5 initial_state"
  by (auto simp: initial_state_def invar_5_def dist_init_inf)


subsubsection \<open>Soundness of the computed distances\<close>

lemma invar_5_compute: "invar_5 dijkstra_compute"
  unfolding dijkstra_compute_def
  by (rule invar_5_holds[OF initial_state_props(5) initial_state_props(1) initial_state_props(2)
        initial_state_props(3) initial_state_props(4) invar_5_initial invar_6_initial])

text \<open>Every distance the algorithm reports is the weight of an actual (source-to-\<open>v\<close>) path, hence an
      upper bound on the true set-distance. Equality for settled vertices (optimality) is the
      remaining part of the correctness argument.\<close>

theorem dijkstra_compute_upper_bound:
  assumes "dist_lookup (dij_dist dijkstra_compute) v \<noteq> -1"
  shows "ag.distance_set w (src_abstract srcs) v \<le> ereal (dist_lookup (dij_dist dijkstra_compute) v)"
  using invar_5_compute assms by (auto elim!: invar_5_props)


subsection \<open>Optimality: settled distances are shortest\<close>

text \<open>The remaining, harder direction: a settled vertex's recorded distance is not merely an upper
      bound (soundness, @{thm dijkstra_compute_upper_bound}) but the exact set-distance. The argument
      rests on three auxiliary invariants -- every loaded source keeps distance \<open>0\<close> (@{term invar_9}),
      settled vertices are fully scanned once the cursor rests (@{term invar_7}), and every scanned
      edge out of a settled vertex has already relaxed its head (@{term invar_8}, the \<^emph>\<open>frontier\<close>) --
      together with the min-extraction property of the queue.\<close>

subsubsection \<open>Loaded sources keep distance zero\<close>

definition "invar_9 st \<longleftrightarrow> (\<forall>v. v \<in> src_abstract srcs \<longrightarrow> v \<notin> src_remaining (dij_srcs st) \<longrightarrow> dist_lookup (dij_dist st) v = 0)"

lemma invar_9_props[invar_props_elims]: "invar_9 st \<Longrightarrow> (\<lbrakk>\<forall>v. v \<in> src_abstract srcs \<longrightarrow> v \<notin> src_remaining (dij_srcs st) \<longrightarrow> dist_lookup (dij_dist st) v = 0\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P" by (auto simp: invar_9_def)
lemma invar_9_intro[invar_props_intros]: "\<forall>v. v \<in> src_abstract srcs \<longrightarrow> v \<notin> src_remaining (dij_srcs st) \<longrightarrow> dist_lookup (dij_dist st) v = 0 \<Longrightarrow> invar_9 st" by (auto simp: invar_9_def)

lemma invar_9_holds_finish[invar_holds_intros]: "\<lbrakk>dijkstra_call_finish_conds st; invar_9 st\<rbrakk> \<Longrightarrow> invar_9 (dijkstra_upd_finish st)" by (simp add: invar_9_def)
lemma invar_9_holds_done[invar_holds_intros]: "\<lbrakk>dijkstra_ret_done_conds st; invar_9 st\<rbrakk> \<Longrightarrow> invar_9 (dijkstra_ret_done st)" by (simp add: invar_9_def)
lemma invar_9_holds_skip[invar_holds_intros]: "\<lbrakk>dijkstra_call_skip_conds st; invar_9 st\<rbrakk> \<Longrightarrow> invar_9 (dijkstra_upd_skip st)" by (simp add: invar_9_def)
lemma invar_9_holds_settle[invar_holds_intros]: "\<lbrakk>dijkstra_call_settle_conds st; invar_9 st\<rbrakk> \<Longrightarrow> invar_9 (dijkstra_upd_settle st)" by (simp add: invar_9_def)
lemma invar_9_holds_found[invar_holds_intros]: "\<lbrakk>dijkstra_ret_found_conds st; invar_9 st\<rbrakk> \<Longrightarrow> invar_9 (dijkstra_ret_found st)" by (simp add: invar_9_def)

lemma invar_9_holds_init[invar_holds_intros]: "\<lbrakk>dijkstra_call_init_conds st; invar_1 st; invar_3 st; invar_9 st\<rbrakk> \<Longrightarrow> invar_9 (dijkstra_upd_init st)"
proof -
  assume a: "dijkstra_call_init_conds st" "invar_1 st" "invar_3 st" "invar_9 st"
  have srch: "src_has (dij_srcs st)" using a(1) by (auto elim!: dijkstra_call_init_condsE)
  have sinv: "src_invar (dij_srcs st)" and dinv: "dist_invar (dij_dist st)" using a(2) by (auto elim!: invar_1_props)
  have rem: "src_remaining (dij_srcs st) \<noteq> {}" using srch sinv sources.has_current by auto
  define v where "v = src_current (dij_srcs st)"
  have vV: "v \<in> \<V>"
    using a(3) sources.current_element[OF sinv rem] sources.iterable_set_abstract(2)[OF sinv] by (auto simp: v_def elim!: invar_3_props)
  have remove: "src_remaining (src_move (dij_srcs st)) = src_remaining (dij_srcs st) - {v}"
    using sources.move_on(2)[OF sinv rem] by (simp add: v_def)
  have I9: "\<forall>s. s \<in> src_abstract srcs \<longrightarrow> s \<notin> src_remaining (dij_srcs st) \<longrightarrow> dist_lookup (dij_dist st) s = 0"
    using a(4) by (auto elim!: invar_9_props)
  show ?thesis
    unfolding invar_9_def
  proof (intro allI impI)
    fix s assume sS: "s \<in> src_abstract srcs" and snr: "s \<notin> src_remaining (dij_srcs (dijkstra_upd_init st))"
    have dupd: "dist_lookup (dij_dist (dijkstra_upd_init st)) s = (if s = v then 0 else dist_lookup (dij_dist st) s)"
      by (simp add: dijkstra_upd_init_def insert_source_def v_def dist_arr.fixed_univ_map_upd[OF dinv vV[unfolded v_def]])
    show "dist_lookup (dij_dist (dijkstra_upd_init st)) s = 0"
    proof (cases "s = v")
      case True thus ?thesis using dupd by simp
    next
      case False
      have "s \<notin> src_remaining (dij_srcs st)" using snr False by (simp add: dijkstra_upd_init_def remove)
      thus ?thesis using I9 sS dupd False by simp
    qed
  qed
qed

lemma invar_9_holds_relax[invar_holds_intros]: "\<lbrakk>dijkstra_call_relax_conds st; invar_1 st; invar_2 st; invar_3 st; invar_9 st\<rbrakk> \<Longrightarrow> invar_9 (dijkstra_upd_relax st)"
proof -
  assume a: "dijkstra_call_relax_conds st" "invar_1 st" "invar_2 st" "invar_3 st" "invar_9 st"
  obtain u where cu: "dij_curr st = Some u" and oh: "out_has (dij_graph st) u"
    using a(1) by (auto elim!: dijkstra_call_relax_condsE)
  have gi: "out_graph_inv (dij_graph st)" and dinv: "dist_invar (dij_dist st)"
    using a(2) by (auto elim!: invar_1_props)
  have uV: "u \<in> \<V>" using a(3) cu by (auto elim!: invar_2_props)
  have du_ne: "dist_lookup (dij_dist st) u \<noteq> -1" and reach0: "\<forall>x. dist_lookup (dij_dist st) x \<noteq> -1 \<longrightarrow> 0 \<le> dist_lookup (dij_dist st) x"
    using a(4) cu by (auto elim!: invar_3_props)
  have I9: "\<forall>s. s \<in> src_abstract srcs \<longrightarrow> s \<notin> src_remaining (dij_srcs st) \<longrightarrow> dist_lookup (dij_dist st) s = 0"
    using a(5) by (auto elim!: invar_9_props)
  define e where "e = out_current (dij_graph st) u"
  define du where "du = dist_lookup (dij_dist st) u"
  have eE: "e \<in> \<E>" using out_current_edge[OF gi uV oh] by (simp add: e_def)
  have du0: "0 \<le> du" using du_ne reach0 by (simp add: du_def)
  have we0: "0 \<le> w e" using eE w_nonneg by blast
  have heV: "snd e \<in> \<V>" using snd_E_V[OF eE] .
  define st' where "st' = st \<lparr> dij_graph := out_move (dij_graph st) u \<rparr>"
  have dd[simp]: "dij_dist st' = dij_dist st" and ds[simp]: "dij_seen st' = dij_seen st" and dsr[simp]: "dij_srcs st' = dij_srcs st"
    by (simp_all add: st'_def)
  have dinv': "dist_invar (dij_dist st')" using dinv by simp
  have upd_eq: "dijkstra_upd_relax st = relax_edge u du e st'"
    by (simp add: dijkstra_upd_relax_def cu du_def e_def st'_def)
  show ?thesis
    unfolding invar_9_def
  proof (intro allI impI)
    fix s assume sS: "s \<in> src_abstract srcs" and snr: "s \<notin> src_remaining (dij_srcs (dijkstra_upd_relax st))"
    have "s \<notin> src_remaining (dij_srcs st)" using snr by (simp add: upd_eq)
    hence ds0: "dist_lookup (dij_dist st) s = 0" using I9 sS by blast
    have "\<not> (du + w e < dist_lookup (dij_dist st) s)" using ds0 du0 we0 by simp
    hence "dist_lookup (dij_dist (dijkstra_upd_relax st)) s = dist_lookup (dij_dist st) s"
      using ds0 unfolding upd_eq by (subst relax_edge_dist_at[OF dinv' heV]) auto
    thus "dist_lookup (dij_dist (dijkstra_upd_relax st)) s = 0" using ds0 by simp
  qed
qed

lemma invar_9_holds[invar_holds_intros]:
  assumes "dijkstra_dom st" "invar_1 st" "invar_2 st" "invar_3 st" "invar_4 st" "invar_9 st"
  shows "invar_9 (dijkstra st)"
  using assms(2-)
proof(induction rule: dijkstra_induct[OF assms(1)])
  case IH: (1 st)
  show ?case
    apply(rule dijkstra_cases[where st = st])
    by (auto intro!: IH(2-) intro: invar_holds_intros simp: dijkstra_simps[OF IH(1)])
qed

lemma invar_9_initial[invar_holds_intros]: "invar_9 initial_state"
  using srcs_fresh by (auto simp: initial_state_def invar_9_def dist_init_inf)


subsubsection \<open>When the cursor rests, settled vertices are fully scanned\<close>

definition "invar_7 st \<longleftrightarrow> (dij_target st = None \<longrightarrow> (\<forall>x. x \<in> seen_abstract (dij_seen st) \<longrightarrow> dij_curr st = Some x \<or> out_remaining (dij_graph st) x = {}))"
lemma invar_7_props[invar_props_elims]: "invar_7 st \<Longrightarrow> (\<lbrakk>dij_target st = None \<Longrightarrow> \<forall>x. x \<in> seen_abstract (dij_seen st) \<longrightarrow> dij_curr st = Some x \<or> out_remaining (dij_graph st) x = {}\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P" by (auto simp: invar_7_def)
lemma invar_7_intro[invar_props_intros]: "(dij_target st = None \<Longrightarrow> \<forall>x. x \<in> seen_abstract (dij_seen st) \<longrightarrow> dij_curr st = Some x \<or> out_remaining (dij_graph st) x = {}) \<Longrightarrow> invar_7 st" by (auto simp: invar_7_def)

lemma invar_7_holds_done[invar_holds_intros]: "\<lbrakk>dijkstra_ret_done_conds st; invar_7 st\<rbrakk> \<Longrightarrow> invar_7 (dijkstra_ret_done st)" by (simp add: dijkstra_ret_done_def invar_7_def)
lemma invar_7_holds_skip[invar_holds_intros]: "\<lbrakk>dijkstra_call_skip_conds st; invar_7 st\<rbrakk> \<Longrightarrow> invar_7 (dijkstra_upd_skip st)" by (auto simp: invar_7_def dijkstra_upd_skip_def split: prod.splits)
lemma invar_7_holds_found[invar_holds_intros]: "\<lbrakk>dijkstra_ret_found_conds st; invar_7 st\<rbrakk> \<Longrightarrow> invar_7 (dijkstra_ret_found st)" by (auto simp: invar_7_def dijkstra_ret_found_def Let_def split: prod.splits)

lemma invar_7_holds_init[invar_holds_intros]: "\<lbrakk>dijkstra_call_init_conds st; invar_1 st; invar_4 st\<rbrakk> \<Longrightarrow> invar_7 (dijkstra_upd_init st)"
proof -
  assume a: "dijkstra_call_init_conds st" "invar_1 st" "invar_4 st"
  have srch: "src_has (dij_srcs st)" using a(1) by (auto elim!: dijkstra_call_init_condsE)
  have sinv: "src_invar (dij_srcs st)" using a(2) by (auto elim!: invar_1_props)
  have rem: "src_remaining (dij_srcs st) \<noteq> {}" using srch sinv sources.has_current by auto
  have seenE: "seen_abstract (dij_seen st) = {}" using a(3) rem by (auto elim!: invar_4_props)
  show ?thesis
    by (rule invar_7_intro) (simp add: dijkstra_upd_init_def seenE)
qed

lemma invar_7_holds_finish[invar_holds_intros]: "\<lbrakk>dijkstra_call_finish_conds st; invar_1 st; invar_2 st; invar_7 st\<rbrakk> \<Longrightarrow> invar_7 (dijkstra_upd_finish st)"
proof -
  assume a: "dijkstra_call_finish_conds st" "invar_1 st" "invar_2 st" "invar_7 st"
  obtain u where cu: "dij_curr st = Some u" and noh: "\<not> out_has (dij_graph st) u"
    using a(1) by (auto elim!: dijkstra_call_finish_condsE)
  have gi: "out_graph_inv (dij_graph st)" using a(2) by (auto elim!: invar_1_props)
  have oinv: "out_invar (dij_graph st)" using gi by (simp add: out_graph_inv_def)
  have uV: "u \<in> \<V>" using a(3) cu by (auto elim!: invar_2_props)
  have remu: "out_remaining (dij_graph st) u = {}" using noh oinv uV outg.idx_has by auto
  show ?thesis
  proof (rule invar_7_intro)
    assume tN: "dij_target (dijkstra_upd_finish st) = None"
    have tNst: "dij_target st = None" using tN by (simp add: dijkstra_upd_finish_def)
    have I7: "\<forall>x. x \<in> seen_abstract (dij_seen st) \<longrightarrow> dij_curr st = Some x \<or> out_remaining (dij_graph st) x = {}"
      using a(4) tNst by (auto elim!: invar_7_props)
    show "\<forall>x. x \<in> seen_abstract (dij_seen (dijkstra_upd_finish st)) \<longrightarrow> dij_curr (dijkstra_upd_finish st) = Some x \<or> out_remaining (dij_graph (dijkstra_upd_finish st)) x = {}"
    proof (intro allI impI)
      fix x assume xseen: "x \<in> seen_abstract (dij_seen (dijkstra_upd_finish st))"
      have xseen': "x \<in> seen_abstract (dij_seen st)" using xseen by (simp add: dijkstra_upd_finish_def)
      have "out_remaining (dij_graph st) x = {}"
      proof (cases "x = u")
        case True thus ?thesis using remu by simp
      next
        case False thus ?thesis using I7 xseen' cu by auto
      qed
      thus "dij_curr (dijkstra_upd_finish st) = Some x \<or> out_remaining (dij_graph (dijkstra_upd_finish st)) x = {}"
        by (simp add: dijkstra_upd_finish_def)
    qed
  qed
qed

lemma invar_7_holds_relax[invar_holds_intros]: "\<lbrakk>dijkstra_call_relax_conds st; invar_1 st; invar_2 st; invar_7 st\<rbrakk> \<Longrightarrow> invar_7 (dijkstra_upd_relax st)"
proof -
  assume a: "dijkstra_call_relax_conds st" "invar_1 st" "invar_2 st" "invar_7 st"
  obtain u where cu: "dij_curr st = Some u" and oh: "out_has (dij_graph st) u"
    using a(1) by (auto elim!: dijkstra_call_relax_condsE)
  have gi: "out_graph_inv (dij_graph st)" using a(2) by (auto elim!: invar_1_props)
  have oinv: "out_invar (dij_graph st)" using gi by (simp add: out_graph_inv_def)
  have uV: "u \<in> \<V>" using a(3) cu by (auto elim!: invar_2_props)
  have remne: "out_remaining (dij_graph st) u \<noteq> {}" using oh oinv uV outg.idx_has by auto
  have relgraph: "dij_graph (dijkstra_upd_relax st) = out_move (dij_graph st) u"
    and relcurr: "dij_curr (dijkstra_upd_relax st) = Some u"
    and relseen: "dij_seen (dijkstra_upd_relax st) = dij_seen st"
    and reltgt: "dij_target (dijkstra_upd_relax st) = dij_target st"
    by (simp_all add: dijkstra_upd_relax_def cu)
  show ?thesis
  proof (rule invar_7_intro)
    assume tN: "dij_target (dijkstra_upd_relax st) = None"
    have I7: "\<forall>x. x \<in> seen_abstract (dij_seen st) \<longrightarrow> dij_curr st = Some x \<or> out_remaining (dij_graph st) x = {}"
      using a(4) tN reltgt by (auto elim!: invar_7_props)
    show "\<forall>x. x \<in> seen_abstract (dij_seen (dijkstra_upd_relax st)) \<longrightarrow> dij_curr (dijkstra_upd_relax st) = Some x \<or> out_remaining (dij_graph (dijkstra_upd_relax st)) x = {}"
      unfolding relgraph relcurr relseen
    proof (intro allI impI)
      fix x assume xseen: "x \<in> seen_abstract (dij_seen st)"
      show "Some u = Some x \<or> out_remaining (out_move (dij_graph st) u) x = {}"
      proof (cases "x = u")
        case True thus ?thesis by simp
      next
        case False
        have "out_remaining (dij_graph st) x = {}" using I7 xseen cu False by auto
        thus ?thesis using outg.idx_move_remaining_other[OF oinv uV remne] False by simp
      qed
    qed
  qed
qed

lemma invar_7_holds_settle[invar_holds_intros]: "\<lbrakk>dijkstra_call_settle_conds st; invar_1 st; invar_2 st; invar_7 st\<rbrakk> \<Longrightarrow> invar_7 (dijkstra_upd_settle st)"
proof -
  assume a: "dijkstra_call_settle_conds st" "invar_1 st" "invar_2 st" "invar_7 st"
  obtain h2 u where hu: "dij_curr st = None" "queue_extract_min (dij_heap st) = (h2, Some u)" "\<not> seen_isin (dij_seen st) u"
    using a(1) by (auto elim!: dijkstra_call_settle_condsE)
  have gi: "out_graph_inv (dij_graph st)" using a(2) by (auto elim!: invar_1_props)
  have oinv: "out_invar (dij_graph st)" using gi by (simp add: out_graph_inv_def)
  have qi: "queue_invar (dij_heap st)" and si: "seen_invar (dij_seen st)" and reachV: "\<forall>x. dist_lookup (dij_dist st) x \<noteq> -1 \<longrightarrow> x \<in> \<V>"
    and coup: "\<forall>x k. ((x,k) \<in> queue_abstract (dij_heap st)) = (x \<notin> seen_abstract (dij_seen st) \<and> dist_lookup (dij_dist st) x \<noteq> -1 \<and> k = dist_lookup (dij_dist st) x)"
    using a(3) by (auto elim!: invar_2_props)
  have uabs: "\<exists>k. (u,k) \<in> queue_abstract (dij_heap st)" using heap.queue_extract_min(2)[OF qi, of u] hu(2) by simp blast
  then have uV: "u \<in> \<V>" using coup reachV by blast
  have seenins: "seen_abstract (dij_seen (dijkstra_upd_settle st)) = insert u (seen_abstract (dij_seen st))"
    by (simp add: dijkstra_upd_settle_def hu(2) Let_def seen_set.fixed_univ_set_insert(2)[OF si uV])
  have setgraph: "dij_graph (dijkstra_upd_settle st) = out_reset (dij_graph st) u"
    and setcurr: "dij_curr (dijkstra_upd_settle st) = Some u"
    and settgt: "dij_target (dijkstra_upd_settle st) = dij_target st"
    by (simp_all add: dijkstra_upd_settle_def hu(2) Let_def)
  show ?thesis
  proof (rule invar_7_intro)
    assume tN: "dij_target (dijkstra_upd_settle st) = None"
    have I7: "\<forall>x. x \<in> seen_abstract (dij_seen st) \<longrightarrow> dij_curr st = Some x \<or> out_remaining (dij_graph st) x = {}"
      using a(4) tN settgt by (auto elim!: invar_7_props)
    show "\<forall>x. x \<in> seen_abstract (dij_seen (dijkstra_upd_settle st)) \<longrightarrow> dij_curr (dijkstra_upd_settle st) = Some x \<or> out_remaining (dij_graph (dijkstra_upd_settle st)) x = {}"
      unfolding seenins setgraph setcurr
    proof (intro allI impI)
      fix x assume xin: "x \<in> insert u (seen_abstract (dij_seen st))"
      show "Some u = Some x \<or> out_remaining (out_reset (dij_graph st) u) x = {}"
      proof (cases "x = u")
        case True thus ?thesis by simp
      next
        case False
        hence xseen: "x \<in> seen_abstract (dij_seen st)" using xin by simp
        have "out_remaining (dij_graph st) x = {}" using I7 xseen hu(1) by auto
        thus ?thesis using outg.idx_reset_remaining_other[OF oinv uV] False by simp
      qed
    qed
  qed
qed

lemma invar_7_holds[invar_holds_intros]:
  assumes "dijkstra_dom st" "invar_1 st" "invar_2 st" "invar_3 st" "invar_4 st" "invar_7 st"
  shows "invar_7 (dijkstra st)"
  using assms(2-)
proof(induction rule: dijkstra_induct[OF assms(1)])
  case IH: (1 st)
  show ?case
    apply(rule dijkstra_cases[where st = st])
    by (auto intro!: IH(2-) intro: invar_holds_intros simp: dijkstra_simps[OF IH(1)])
qed

lemma invar_7_initial[invar_holds_intros]: "invar_7 initial_state"
  by (auto simp: initial_state_def invar_7_def seen_set.fixed_univ_set_empty(2))


subsubsection \<open>The frontier invariant: scanned allowed edges out of settled vertices are relaxed\<close>

definition "invar_8 st \<longleftrightarrow>
  (\<forall>x. x \<in> seen_abstract (dij_seen st) \<longrightarrow> dist_lookup (dij_dist st) x \<noteq> -1)
  \<and> (\<forall>x. x \<notin> seen_abstract (dij_seen st) \<longrightarrow> out_iterated (dij_graph st) x = {})
  \<and> (\<forall>x e. x \<in> seen_abstract (dij_seen st) \<longrightarrow> e \<in> out_iterated (dij_graph st) x \<longrightarrow> allowed_edge e \<longrightarrow>
        (snd e \<in> seen_abstract (dij_seen st) \<or>
         (dist_lookup (dij_dist st) (snd e) \<noteq> -1 \<and> dist_lookup (dij_dist st) (snd e) \<le> dist_lookup (dij_dist st) x + w e)))"

lemma invar_8_props[invar_props_elims]: "invar_8 st \<Longrightarrow> (\<lbrakk>\<forall>x. x \<in> seen_abstract (dij_seen st) \<longrightarrow> dist_lookup (dij_dist st) x \<noteq> -1; \<forall>x. x \<notin> seen_abstract (dij_seen st) \<longrightarrow> out_iterated (dij_graph st) x = {}; \<forall>x e. x \<in> seen_abstract (dij_seen st) \<longrightarrow> e \<in> out_iterated (dij_graph st) x \<longrightarrow> allowed_edge e \<longrightarrow> (snd e \<in> seen_abstract (dij_seen st) \<or> (dist_lookup (dij_dist st) (snd e) \<noteq> -1 \<and> dist_lookup (dij_dist st) (snd e) \<le> dist_lookup (dij_dist st) x + w e))\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P" by (auto simp: invar_8_def)
lemma invar_8_intro[invar_props_intros]: "\<lbrakk>\<forall>x. x \<in> seen_abstract (dij_seen st) \<longrightarrow> dist_lookup (dij_dist st) x \<noteq> -1; \<forall>x. x \<notin> seen_abstract (dij_seen st) \<longrightarrow> out_iterated (dij_graph st) x = {}; \<forall>x e. x \<in> seen_abstract (dij_seen st) \<longrightarrow> e \<in> out_iterated (dij_graph st) x \<longrightarrow> allowed_edge e \<longrightarrow> (snd e \<in> seen_abstract (dij_seen st) \<or> (dist_lookup (dij_dist st) (snd e) \<noteq> -1 \<and> dist_lookup (dij_dist st) (snd e) \<le> dist_lookup (dij_dist st) x + w e))\<rbrakk> \<Longrightarrow> invar_8 st" by (auto simp: invar_8_def)

lemma invar_8_holds_done[invar_holds_intros]: "\<lbrakk>dijkstra_ret_done_conds st; invar_8 st\<rbrakk> \<Longrightarrow> invar_8 (dijkstra_ret_done st)" by (simp add: dijkstra_ret_done_def invar_8_def)
lemma invar_8_holds_skip[invar_holds_intros]: "\<lbrakk>dijkstra_call_skip_conds st; invar_8 st\<rbrakk> \<Longrightarrow> invar_8 (dijkstra_upd_skip st)" by (auto simp: invar_8_def dijkstra_upd_skip_def split: prod.splits)
lemma invar_8_holds_finish[invar_holds_intros]: "\<lbrakk>dijkstra_call_finish_conds st; invar_8 st\<rbrakk> \<Longrightarrow> invar_8 (dijkstra_upd_finish st)" by (auto simp: invar_8_def dijkstra_upd_finish_def)

lemma invar_8_holds_init[invar_holds_intros]: "\<lbrakk>dijkstra_call_init_conds st; invar_1 st; invar_4 st; invar_8 st\<rbrakk> \<Longrightarrow> invar_8 (dijkstra_upd_init st)"
proof -
  assume a: "dijkstra_call_init_conds st" "invar_1 st" "invar_4 st" "invar_8 st"
  have srch: "src_has (dij_srcs st)" using a(1) by (auto elim!: dijkstra_call_init_condsE)
  have sinv: "src_invar (dij_srcs st)" using a(2) by (auto elim!: invar_1_props)
  have rem: "src_remaining (dij_srcs st) \<noteq> {}" using srch sinv sources.has_current by auto
  have seenE: "seen_abstract (dij_seen st) = {}" using a(3) rem by (auto elim!: invar_4_props)
  have I8b: "\<forall>x. x \<notin> seen_abstract (dij_seen st) \<longrightarrow> out_iterated (dij_graph st) x = {}" using a(4) by (auto elim!: invar_8_props)
  hence iterall: "\<forall>x. out_iterated (dij_graph st) x = {}" using seenE by simp
  have seenI: "dij_seen (dijkstra_upd_init st) = dij_seen st" and graphI: "dij_graph (dijkstra_upd_init st) = dij_graph st"
    by (simp_all add: dijkstra_upd_init_def insert_source_def)
  show ?thesis
    apply (rule invar_8_intro)
    subgoal by (simp add: seenI seenE)
    subgoal using iterall by (simp add: graphI)
    subgoal by (simp add: seenI seenE)
    done
qed

lemma invar_8_holds_found[invar_holds_intros]: "\<lbrakk>dijkstra_ret_found_conds st; invar_1 st; invar_2 st; invar_8 st\<rbrakk> \<Longrightarrow> invar_8 (dijkstra_ret_found st)"
proof -
  assume a: "dijkstra_ret_found_conds st" "invar_1 st" "invar_2 st" "invar_8 st"
  obtain h2 u where hu: "queue_extract_min (dij_heap st) = (h2, Some u)" "\<not> seen_isin (dij_seen st) u"
    using a(1) by (auto elim!: dijkstra_ret_found_condsE)
  have qi: "queue_invar (dij_heap st)" and reachV: "\<forall>x. dist_lookup (dij_dist st) x \<noteq> -1 \<longrightarrow> x \<in> \<V>" and si: "seen_invar (dij_seen st)"
    and coup: "\<forall>x k. ((x,k) \<in> queue_abstract (dij_heap st)) = (x \<notin> seen_abstract (dij_seen st) \<and> dist_lookup (dij_dist st) x \<noteq> -1 \<and> k = dist_lookup (dij_dist st) x)"
    using a(3) by (auto elim!: invar_2_props)
  obtain k where uk: "(u,k) \<in> queue_abstract (dij_heap st)" using heap.queue_extract_min(2)[OF qi, of u] hu(1) by simp blast
  have ureach: "dist_lookup (dij_dist st) u \<noteq> -1" and unseen: "u \<notin> seen_abstract (dij_seen st)" using uk coup by blast+
  have uV: "u \<in> \<V>" using ureach reachV by blast
  have seenins: "seen_abstract (dij_seen (dijkstra_ret_found st)) = insert u (seen_abstract (dij_seen st))"
    by (simp add: dijkstra_ret_found_def hu(1) Let_def seen_set.fixed_univ_set_insert(2)[OF si uV])
  have distF: "dij_dist (dijkstra_ret_found st) = dij_dist st" and graphF: "dij_graph (dijkstra_ret_found st) = dij_graph st"
    by (simp_all add: dijkstra_ret_found_def hu(1) Let_def)
  have I8a: "\<forall>x. x \<in> seen_abstract (dij_seen st) \<longrightarrow> dist_lookup (dij_dist st) x \<noteq> -1"
    and I8b: "\<forall>x. x \<notin> seen_abstract (dij_seen st) \<longrightarrow> out_iterated (dij_graph st) x = {}"
    and I8c: "\<forall>x e. x \<in> seen_abstract (dij_seen st) \<longrightarrow> e \<in> out_iterated (dij_graph st) x \<longrightarrow> allowed_edge e \<longrightarrow> (snd e \<in> seen_abstract (dij_seen st) \<or> (dist_lookup (dij_dist st) (snd e) \<noteq> -1 \<and> dist_lookup (dij_dist st) (snd e) \<le> dist_lookup (dij_dist st) x + w e))"
    using a(4) by (auto elim!: invar_8_props)
  show ?thesis
    unfolding invar_8_def seenins distF graphF
  proof (intro conjI allI impI)
    fix x assume "x \<in> insert u (seen_abstract (dij_seen st))"
    thus "dist_lookup (dij_dist st) x \<noteq> -1" using I8a ureach by auto
  next
    fix x assume "x \<notin> insert u (seen_abstract (dij_seen st))"
    thus "out_iterated (dij_graph st) x = {}" using I8b by auto
  next
    fix x e assume xin: "x \<in> insert u (seen_abstract (dij_seen st))" and ein: "e \<in> out_iterated (dij_graph st) x" and ea: "allowed_edge e"
    show "snd e \<in> insert u (seen_abstract (dij_seen st)) \<or> (dist_lookup (dij_dist st) (snd e) \<noteq> -1 \<and> dist_lookup (dij_dist st) (snd e) \<le> dist_lookup (dij_dist st) x + w e)"
    proof (cases "x = u")
      case True hence "out_iterated (dij_graph st) x = {}" using I8b unseen by simp
      thus ?thesis using ein by simp
    next
      case False hence xseen: "x \<in> seen_abstract (dij_seen st)" using xin by simp
      thus ?thesis using I8c ein ea by auto
    qed
  qed
qed

lemma invar_8_holds_settle[invar_holds_intros]: "\<lbrakk>dijkstra_call_settle_conds st; invar_1 st; invar_2 st; invar_8 st\<rbrakk> \<Longrightarrow> invar_8 (dijkstra_upd_settle st)"
proof -
  assume a: "dijkstra_call_settle_conds st" "invar_1 st" "invar_2 st" "invar_8 st"
  obtain h2 u where hu: "queue_extract_min (dij_heap st) = (h2, Some u)" "\<not> seen_isin (dij_seen st) u"
    using a(1) by (auto elim!: dijkstra_call_settle_condsE)
  have gi: "out_graph_inv (dij_graph st)" using a(2) by (auto elim!: invar_1_props)
  have oinv: "out_invar (dij_graph st)" using gi by (simp add: out_graph_inv_def)
  have qi: "queue_invar (dij_heap st)" and reachV: "\<forall>x. dist_lookup (dij_dist st) x \<noteq> -1 \<longrightarrow> x \<in> \<V>" and si: "seen_invar (dij_seen st)"
    and coup: "\<forall>x k. ((x,k) \<in> queue_abstract (dij_heap st)) = (x \<notin> seen_abstract (dij_seen st) \<and> dist_lookup (dij_dist st) x \<noteq> -1 \<and> k = dist_lookup (dij_dist st) x)"
    using a(3) by (auto elim!: invar_2_props)
  obtain k where uk: "(u,k) \<in> queue_abstract (dij_heap st)" using heap.queue_extract_min(2)[OF qi, of u] hu(1) by simp blast
  have ureach: "dist_lookup (dij_dist st) u \<noteq> -1" using uk coup by blast
  have uV: "u \<in> \<V>" using ureach reachV by blast
  have seenins: "seen_abstract (dij_seen (dijkstra_upd_settle st)) = insert u (seen_abstract (dij_seen st))"
    by (simp add: dijkstra_upd_settle_def hu(1) Let_def seen_set.fixed_univ_set_insert(2)[OF si uV])
  have distS: "dij_dist (dijkstra_upd_settle st) = dij_dist st" and graphS: "dij_graph (dijkstra_upd_settle st) = out_reset (dij_graph st) u"
    by (simp_all add: dijkstra_upd_settle_def hu(1) Let_def)
  have I8a: "\<forall>x. x \<in> seen_abstract (dij_seen st) \<longrightarrow> dist_lookup (dij_dist st) x \<noteq> -1"
    and I8b: "\<forall>x. x \<notin> seen_abstract (dij_seen st) \<longrightarrow> out_iterated (dij_graph st) x = {}"
    and I8c: "\<forall>x e. x \<in> seen_abstract (dij_seen st) \<longrightarrow> e \<in> out_iterated (dij_graph st) x \<longrightarrow> allowed_edge e \<longrightarrow> (snd e \<in> seen_abstract (dij_seen st) \<or> (dist_lookup (dij_dist st) (snd e) \<noteq> -1 \<and> dist_lookup (dij_dist st) (snd e) \<le> dist_lookup (dij_dist st) x + w e))"
    using a(4) by (auto elim!: invar_8_props)
  show ?thesis
    unfolding invar_8_def seenins distS graphS
  proof (intro conjI allI impI)
    fix x assume "x \<in> insert u (seen_abstract (dij_seen st))"
    thus "dist_lookup (dij_dist st) x \<noteq> -1" using I8a ureach by auto
  next
    fix x assume xni: "x \<notin> insert u (seen_abstract (dij_seen st))"
    hence xne: "x \<noteq> u" and xns: "x \<notin> seen_abstract (dij_seen st)" by auto
    have "out_iterated (out_reset (dij_graph st) u) x = out_iterated (dij_graph st) x" using outg.idx_reset_iterated_other[OF oinv uV] xne by simp
    thus "out_iterated (out_reset (dij_graph st) u) x = {}" using I8b xns by simp
  next
    fix x e assume xin: "x \<in> insert u (seen_abstract (dij_seen st))" and ein: "e \<in> out_iterated (out_reset (dij_graph st) u) x" and ea: "allowed_edge e"
    show "snd e \<in> insert u (seen_abstract (dij_seen st)) \<or> (dist_lookup (dij_dist st) (snd e) \<noteq> -1 \<and> dist_lookup (dij_dist st) (snd e) \<le> dist_lookup (dij_dist st) x + w e)"
    proof (cases "x = u")
      case True hence "out_iterated (out_reset (dij_graph st) u) x = {}" using outg.idx_reset_iterated[OF oinv uV] by simp
      thus ?thesis using ein by simp
    next
      case False hence xseen: "x \<in> seen_abstract (dij_seen st)" using xin by simp
      have "out_iterated (out_reset (dij_graph st) u) x = out_iterated (dij_graph st) x" using outg.idx_reset_iterated_other[OF oinv uV] False by simp
      hence "e \<in> out_iterated (dij_graph st) x" using ein by simp
      thus ?thesis using I8c xseen ea by auto
    qed
  qed
qed

lemma invar_8_holds_relax[invar_holds_intros]: "\<lbrakk>dijkstra_call_relax_conds st; invar_1 st; invar_2 st; invar_3 st; invar_8 st\<rbrakk> \<Longrightarrow> invar_8 (dijkstra_upd_relax st)"
proof -
  assume a: "dijkstra_call_relax_conds st" "invar_1 st" "invar_2 st" "invar_3 st" "invar_8 st"
  obtain u where cu: "dij_curr st = Some u" and oh: "out_has (dij_graph st) u"
    using a(1) by (auto elim!: dijkstra_call_relax_condsE)
  have gi: "out_graph_inv (dij_graph st)" and dinv: "dist_invar (dij_dist st)" using a(2) by (auto elim!: invar_1_props)
  have oinv: "out_invar (dij_graph st)" using gi by (simp add: out_graph_inv_def)
  have uV: "u \<in> \<V>" and si: "seen_invar (dij_seen st)" using a(3) cu by (auto elim!: invar_2_props)
  have useen: "u \<in> seen_abstract (dij_seen st)" and du_ne: "dist_lookup (dij_dist st) u \<noteq> -1"
    and reach0: "\<forall>x. dist_lookup (dij_dist st) x \<noteq> -1 \<longrightarrow> 0 \<le> dist_lookup (dij_dist st) x"
    using a(4) cu by (auto elim!: invar_3_props)
  have I8a: "\<forall>x. x \<in> seen_abstract (dij_seen st) \<longrightarrow> dist_lookup (dij_dist st) x \<noteq> -1"
    and I8b: "\<forall>x. x \<notin> seen_abstract (dij_seen st) \<longrightarrow> out_iterated (dij_graph st) x = {}"
    and I8c: "\<forall>x e. x \<in> seen_abstract (dij_seen st) \<longrightarrow> e \<in> out_iterated (dij_graph st) x \<longrightarrow> allowed_edge e \<longrightarrow> (snd e \<in> seen_abstract (dij_seen st) \<or> (dist_lookup (dij_dist st) (snd e) \<noteq> -1 \<and> dist_lookup (dij_dist st) (snd e) \<le> dist_lookup (dij_dist st) x + w e))"
    using a(5) by (auto elim!: invar_8_props)
  define e0 where "e0 = out_current (dij_graph st) u"
  define du where "du = dist_lookup (dij_dist st) u"
  define de where "de = snd e0"
  have eE: "e0 \<in> \<E>" using out_current_edge[OF gi uV oh] by (simp add: e0_def)
  have du0: "0 \<le> du" using du_ne reach0 by (simp add: du_def)
  have we0: "0 \<le> w e0" using eE w_nonneg by blast
  have dune1: "du + w e0 \<noteq> -1" using du0 we0 by simp
  have remne: "out_remaining (dij_graph st) u \<noteq> {}" using oh oinv uV outg.idx_has by auto
  have e0V: "snd e0 \<in> \<V>" using snd_E_V[OF eE] .
  define st' where "st' = st \<lparr> dij_graph := out_move (dij_graph st) u \<rparr>"
  have dd: "dij_dist st' = dij_dist st" and ds: "dij_seen st' = dij_seen st" by (simp_all add: st'_def)
  have dinv': "dist_invar (dij_dist st')" using dinv dd by simp
  have upd_eq: "dijkstra_upd_relax st = relax_edge u du e0 st'"
    by (simp add: dijkstra_upd_relax_def cu du_def e0_def st'_def)
  have seeneq: "dij_seen (dijkstra_upd_relax st) = dij_seen st" by (simp add: upd_eq ds)
  have grapheq: "dij_graph (dijkstra_upd_relax st) = out_move (dij_graph st) u" by (simp add: upd_eq st'_def)
  have distform: "\<And>y. dist_lookup (dij_dist (dijkstra_upd_relax st)) y = (if y = de \<and> \<not> seen_isin (dij_seen st) de \<and> allowed_edge e0 \<and> (dist_lookup (dij_dist st) de = -1 \<or> du + w e0 < dist_lookup (dij_dist st) de) then du + w e0 else dist_lookup (dij_dist st) y)"
    unfolding upd_eq de_def by (subst relax_edge_dist_at[OF dinv' e0V]) (auto simp: dd ds)
  have itu: "out_iterated (out_move (dij_graph st) u) u = out_iterated (dij_graph st) u \<union> {e0}"
    using outg.idx_move_iterated[OF oinv uV remne] by (simp add: e0_def)
  have ito: "\<And>x. x \<noteq> u \<Longrightarrow> out_iterated (out_move (dij_graph st) u) x = out_iterated (dij_graph st) x"
    using outg.idx_move_iterated_other[OF oinv uV remne] by simp
  have F1: "\<And>x. x \<in> seen_abstract (dij_seen st) \<Longrightarrow> dist_lookup (dij_dist (dijkstra_upd_relax st)) x = dist_lookup (dij_dist st) x"
  proof -
    fix x assume xseen: "x \<in> seen_abstract (dij_seen st)"
    have "x = de \<longrightarrow> seen_isin (dij_seen st) de" using xseen seen_set.fixed_univ_set_isin[OF si] by auto
    thus "dist_lookup (dij_dist (dijkstra_upd_relax st)) x = dist_lookup (dij_dist st) x" using distform[of x] by auto
  qed
  have F3: "\<And>y. dist_lookup (dij_dist st) y \<noteq> -1 \<Longrightarrow> dist_lookup (dij_dist (dijkstra_upd_relax st)) y \<le> dist_lookup (dij_dist st) y \<and> dist_lookup (dij_dist (dijkstra_upd_relax st)) y \<noteq> -1"
  proof -
    fix y assume yr: "dist_lookup (dij_dist st) y \<noteq> -1"
    show "dist_lookup (dij_dist (dijkstra_upd_relax st)) y \<le> dist_lookup (dij_dist st) y \<and> dist_lookup (dij_dist (dijkstra_upd_relax st)) y \<noteq> -1"
    proof (cases "y = de \<and> \<not> seen_isin (dij_seen st) de \<and> allowed_edge e0 \<and> (dist_lookup (dij_dist st) de = -1 \<or> du + w e0 < dist_lookup (dij_dist st) de)")
      case True
      hence dy: "dist_lookup (dij_dist (dijkstra_upd_relax st)) y = du + w e0" using distform[of y] by simp
      have "du + w e0 < dist_lookup (dij_dist st) y" using True yr by auto
      thus ?thesis using dy dune1 by auto
    next
      case False
      hence "dist_lookup (dij_dist (dijkstra_upd_relax st)) y = dist_lookup (dij_dist st) y" using distform[of y] by auto
      thus ?thesis using yr by auto
    qed
  qed
  have F2: "de \<in> seen_abstract (dij_seen st) \<or> (dist_lookup (dij_dist (dijkstra_upd_relax st)) de \<noteq> -1 \<and> dist_lookup (dij_dist (dijkstra_upd_relax st)) de \<le> du + w e0)" if "allowed_edge e0"
  proof (cases "de \<in> seen_abstract (dij_seen st)")
    case True thus ?thesis by simp
  next
    case False
    hence nsi: "\<not> seen_isin (dij_seen st) de" using seen_set.fixed_univ_set_isin[OF si] by auto
    show ?thesis
    proof (cases "dist_lookup (dij_dist st) de = -1 \<or> du + w e0 < dist_lookup (dij_dist st) de")
      case True
      hence "dist_lookup (dij_dist (dijkstra_upd_relax st)) de = du + w e0" using distform[of de] nsi that by simp
      thus ?thesis using dune1 by auto
    next
      case False
      hence "dist_lookup (dij_dist (dijkstra_upd_relax st)) de = dist_lookup (dij_dist st) de" using distform[of de] by auto
      thus ?thesis using False by auto
    qed
  qed
  show ?thesis
    unfolding invar_8_def seeneq grapheq
  proof (intro conjI allI impI)
    fix x assume "x \<in> seen_abstract (dij_seen st)"
    thus "dist_lookup (dij_dist (dijkstra_upd_relax st)) x \<noteq> -1" using F1 I8a by auto
  next
    fix x assume xns: "x \<notin> seen_abstract (dij_seen st)"
    hence xne: "x \<noteq> u" using useen by auto
    have "out_iterated (out_move (dij_graph st) u) x = out_iterated (dij_graph st) x" using ito xne by simp
    thus "out_iterated (out_move (dij_graph st) u) x = {}" using I8b xns by simp
  next
    fix x e assume xseen: "x \<in> seen_abstract (dij_seen st)" and ein: "e \<in> out_iterated (out_move (dij_graph st) u) x" and ea: "allowed_edge e"
    have dx: "dist_lookup (dij_dist (dijkstra_upd_relax st)) x = dist_lookup (dij_dist st) x" using F1 xseen by simp
    show "snd e \<in> seen_abstract (dij_seen st) \<or> (dist_lookup (dij_dist (dijkstra_upd_relax st)) (snd e) \<noteq> -1 \<and> dist_lookup (dij_dist (dijkstra_upd_relax st)) (snd e) \<le> dist_lookup (dij_dist (dijkstra_upd_relax st)) x + w e)"
    proof (cases "x = u")
      case True
      have "e \<in> out_iterated (dij_graph st) u \<union> {e0}" using ein itu True by simp
      thus ?thesis
      proof
        assume "e \<in> out_iterated (dij_graph st) u"
        hence "snd e \<in> seen_abstract (dij_seen st) \<or> (dist_lookup (dij_dist st) (snd e) \<noteq> -1 \<and> dist_lookup (dij_dist st) (snd e) \<le> dist_lookup (dij_dist st) u + w e)"
          using I8c useen ea by blast
        thus ?thesis using F3 dx True du_def by fastforce
      next
        assume "e \<in> {e0}"
        hence ee: "e = e0" by simp
        show ?thesis using F2 dx True ee ea by (auto simp: de_def du_def)
      qed
    next
      case False
      have "e \<in> out_iterated (dij_graph st) x" using ein ito False by simp
      hence "snd e \<in> seen_abstract (dij_seen st) \<or> (dist_lookup (dij_dist st) (snd e) \<noteq> -1 \<and> dist_lookup (dij_dist st) (snd e) \<le> dist_lookup (dij_dist st) x + w e)"
        using I8c xseen ea by blast
      thus ?thesis using F3 dx by fastforce
    qed
  qed
qed

lemma invar_8_holds[invar_holds_intros]:
  assumes "dijkstra_dom st" "invar_1 st" "invar_2 st" "invar_3 st" "invar_4 st" "invar_8 st"
  shows "invar_8 (dijkstra st)"
  using assms(2-)
proof(induction rule: dijkstra_induct[OF assms(1)])
  case IH: (1 st)
  show ?case
    apply(rule dijkstra_cases[where st = st])
    by (auto intro!: IH(2-) intro: invar_holds_intros simp: dijkstra_simps[OF IH(1)])
qed

lemma invar_8_initial[invar_holds_intros]: "invar_8 initial_state"
  by (auto simp: initial_state_def invar_8_def seen_set.fixed_univ_set_empty(2) graph_fresh)


subsubsection \<open>No target has been found yet (until the early-stop return)\<close>

definition "invar_10 st \<longleftrightarrow> dij_target st = None"
lemma invar_10_props[invar_props_elims]: "invar_10 st \<Longrightarrow> (dij_target st = None \<Longrightarrow> P) \<Longrightarrow> P" by (auto simp: invar_10_def)
lemma invar_10_intro[invar_props_intros]: "dij_target st = None \<Longrightarrow> invar_10 st" by (auto simp: invar_10_def)

lemma invar_10_holds_finish[invar_holds_intros]: "\<lbrakk>dijkstra_call_finish_conds st; invar_10 st\<rbrakk> \<Longrightarrow> invar_10 (dijkstra_upd_finish st)" by (simp add: invar_10_def dijkstra_upd_finish_def)
lemma invar_10_holds_skip[invar_holds_intros]: "\<lbrakk>dijkstra_call_skip_conds st; invar_10 st\<rbrakk> \<Longrightarrow> invar_10 (dijkstra_upd_skip st)" by (auto simp: invar_10_def dijkstra_upd_skip_def split: prod.splits)
lemma invar_10_holds_init[invar_holds_intros]: "\<lbrakk>dijkstra_call_init_conds st; invar_10 st\<rbrakk> \<Longrightarrow> invar_10 (dijkstra_upd_init st)" by (simp add: invar_10_def dijkstra_upd_init_def insert_source_def)
lemma invar_10_holds_relax[invar_holds_intros]: "\<lbrakk>dijkstra_call_relax_conds st; invar_10 st\<rbrakk> \<Longrightarrow> invar_10 (dijkstra_upd_relax st)" by (simp add: invar_10_def dijkstra_upd_relax_def Let_def)
lemma invar_10_holds_settle[invar_holds_intros]: "\<lbrakk>dijkstra_call_settle_conds st; invar_10 st\<rbrakk> \<Longrightarrow> invar_10 (dijkstra_upd_settle st)" by (auto simp: invar_10_def dijkstra_upd_settle_def Let_def split: prod.splits)
lemma invar_10_initial[invar_holds_intros]: "invar_10 initial_state" by (simp add: invar_10_def initial_state_def)


subsubsection \<open>The optimality invariant\<close>

definition "invar_opt st \<longleftrightarrow> (\<forall>v. v \<in> seen_abstract (dij_seen st) \<longrightarrow> ereal (dist_lookup (dij_dist st) v) \<le> ag.distance_set w (src_abstract srcs) v)"
lemma invar_opt_props[invar_props_elims]: "invar_opt st \<Longrightarrow> (\<lbrakk>\<forall>v. v \<in> seen_abstract (dij_seen st) \<longrightarrow> ereal (dist_lookup (dij_dist st) v) \<le> ag.distance_set w (src_abstract srcs) v\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P" by (auto simp: invar_opt_def)
lemma invar_opt_intro[invar_props_intros]: "\<forall>v. v \<in> seen_abstract (dij_seen st) \<longrightarrow> ereal (dist_lookup (dij_dist st) v) \<le> ag.distance_set w (src_abstract srcs) v \<Longrightarrow> invar_opt st" by (auto simp: invar_opt_def)

text \<open>The key path lemma: from any settled vertex \<open>x\<close>, following a distinct path \<open>p\<close> to an unsettled
      \<open>v\<close>, the frontier invariant and the recursive optimality of intermediate settled vertices produce
      a reached, unsettled vertex \<open>y\<close> whose distance is bounded by \<open>dist x + weight p\<close>.\<close>

lemma frontier_reach:
  assumes finS: "finite (src_abstract srcs)"
    and cN: "dij_curr st = None" and tN: "dij_target st = None"
    and I1: "invar_1 st" and I2: "invar_2 st" and I5: "invar_5 st"
    and I7: "invar_7 st" and I8: "invar_8 st" and Iopt: "invar_opt st"
  shows "ag.path_bet p x v \<Longrightarrow> distinct p \<Longrightarrow> x \<in> seen_abstract (dij_seen st) \<Longrightarrow> v \<notin> seen_abstract (dij_seen st)
    \<Longrightarrow> (\<exists>y. y \<notin> seen_abstract (dij_seen st) \<and> dist_lookup (dij_dist st) y \<noteq> -1 \<and> dist_lookup (dij_dist st) y \<le> dist_lookup (dij_dist st) x + weight w p)"
proof (induction p arbitrary: x)
  case Nil
  then show ?case by (auto simp: ag.path_bet_def)
next
  case (Cons e p')
  have gi: "out_graph_inv (dij_graph st)" using I1 by (auto elim!: invar_1_props)
  have oinv: "out_invar (dij_graph st)" using gi by (simp add: out_graph_inv_def)
  have sV: "seen_abstract (dij_seen st) \<subseteq> \<V>" using I2 by (auto elim!: invar_2_props)
  have I8a: "\<forall>z. z \<in> seen_abstract (dij_seen st) \<longrightarrow> dist_lookup (dij_dist st) z \<noteq> -1"
    and I8c: "\<forall>z e. z \<in> seen_abstract (dij_seen st) \<longrightarrow> e \<in> out_iterated (dij_graph st) z \<longrightarrow> allowed_edge e \<longrightarrow> (snd e \<in> seen_abstract (dij_seen st) \<or> (dist_lookup (dij_dist st) (snd e) \<noteq> -1 \<and> dist_lookup (dij_dist st) (snd e) \<le> dist_lookup (dij_dist st) z + w e))"
    using I8 by (auto elim!: invar_8_props)
  have I5all: "\<forall>z. dist_lookup (dij_dist st) z \<noteq> -1 \<longrightarrow> ag.distance_set w (src_abstract srcs) z \<le> ereal (dist_lookup (dij_dist st) z)"
    using I5 by (auto elim!: invar_5_props)
  have I7all: "\<forall>z. z \<in> seen_abstract (dij_seen st) \<longrightarrow> out_remaining (dij_graph st) z = {}"
    using I7 tN cN by (auto elim!: invar_7_props)
  have Ioptall: "\<forall>z. z \<in> seen_abstract (dij_seen st) \<longrightarrow> ereal (dist_lookup (dij_dist st) z) \<le> ag.distance_set w (src_abstract srcs) z"
    using Iopt by (auto elim!: invar_opt_props)
  have pb: "ag.path_bet (e # p') x v" and dis: "distinct (e # p')" and xseen: "x \<in> seen_abstract (dij_seen st)" and vns: "v \<notin> seen_abstract (dij_seen st)"
    using Cons.prems by auto
  have eE: "e \<in> Ea" and efst: "fst e = x" and pb': "ag.path_bet p' (snd e) v" using pb by (auto elim: ag_path_bet_ConsE)
  have dp': "distinct p'" using dis by auto
  have xV: "x \<in> \<V>" using xseen sV by blast
  have edelta: "e \<in> \<delta>\<^sup>+ x" using eE efst by (auto simp: delta_plus_def)
  have absx: "out_abstract (dij_graph st) x = \<delta>\<^sup>+ x" using gi xV by (auto simp: out_graph_inv_def)
  have remx: "out_remaining (dij_graph st) x = {}" using I7all xseen by blast
  have itx: "out_iterated (dij_graph st) x = \<delta>\<^sup>+ x" using outg.idx_partition_union[OF oinv xV] remx absx by simp
  have einit: "e \<in> out_iterated (dij_graph st) x" using edelta itx by simp
  have frontier: "snd e \<in> seen_abstract (dij_seen st) \<or> (dist_lookup (dij_dist st) (snd e) \<noteq> -1 \<and> dist_lookup (dij_dist st) (snd e) \<le> dist_lookup (dij_dist st) x + w e)"
    using I8c xseen einit eE by blast
  have wp'0: "0 \<le> weight w p'" using weight_nonneg[of p'] ag_path_bet_edges_subset[OF pb'] by simp
  have wcons: "weight w (e # p') = w e + weight w p'" by simp
  show ?case
  proof (cases "snd e \<in> seen_abstract (dij_seen st)")
    case False
    hence bound: "dist_lookup (dij_dist st) (snd e) \<noteq> -1 \<and> dist_lookup (dij_dist st) (snd e) \<le> dist_lookup (dij_dist st) x + w e" using frontier by simp
    have "dist_lookup (dij_dist st) (snd e) \<le> dist_lookup (dij_dist st) x + weight w (e # p')" using bound wp'0 wcons by simp
    thus ?thesis using False bound by blast
  next
    case True
    have dxne: "dist_lookup (dij_dist st) x \<noteq> -1" using I8a xseen by blast
    have dsfe: "ag.distance_set w (src_abstract srcs) (fst e) \<le> ereal (dist_lookup (dij_dist st) x)" using I5all dxne by (simp add: efst)
    have edgeb: "ag.distance_set w (src_abstract srcs) (snd e) \<le> ereal (dist_lookup (dij_dist st) x + w e)"
      using distance_set_edge_bound[OF finS eE dsfe] .
    have "ereal (dist_lookup (dij_dist st) (snd e)) \<le> ereal (dist_lookup (dij_dist st) x + w e)"
      using Ioptall True edgeb order_trans by blast
    hence dse: "dist_lookup (dij_dist st) (snd e) \<le> dist_lookup (dij_dist st) x + w e" by simp
    obtain y where y: "y \<notin> seen_abstract (dij_seen st)" "dist_lookup (dij_dist st) y \<noteq> -1" "dist_lookup (dij_dist st) y \<le> dist_lookup (dij_dist st) (snd e) + weight w p'"
      using Cons.IH[OF pb' dp' True vns] by blast
    have "dist_lookup (dij_dist st) y \<le> dist_lookup (dij_dist st) x + weight w (e # p')" using y(3) dse wcons by simp
    thus ?thesis using y(1) y(2) by blast
  qed
qed

text \<open>The heart of optimality: the recorded distance of the vertex extracted from the queue (whether
      settled or returned as the found target) is at most the true set-distance of every unsettled
      vertex, in particular of itself. The minimum-key extraction, the non-negativity of weights, and
      the frontier argument combine to show that no path to an unsettled vertex can beat it.\<close>

lemma settle_opt_bound:
  assumes cN: "dij_curr st = None" and nsh: "\<not> src_has (dij_srcs st)"
    and ext: "queue_extract_min (dij_heap st) = (h2, Some u)"
    and I1: "invar_1 st" and I2: "invar_2 st" and I5: "invar_5 st"
    and I7: "invar_7 st" and I8: "invar_8 st" and I9: "invar_9 st" and I10: "invar_10 st" and Iopt: "invar_opt st"
    and vns: "v \<notin> seen_abstract (dij_seen st)"
  shows "ereal (dist_lookup (dij_dist st) u) \<le> ag.distance_set w (src_abstract srcs) v"
proof (cases "ag.distance_set w (src_abstract srcs) v < \<infinity>")
  case infty: True
  have finS: "finite (src_abstract srcs)" using srcs_in_V \<V>_finite by (auto elim: finite_subset)
  have sinv: "src_invar (dij_srcs st)" using I1 by (auto elim!: invar_1_props)
  have qi: "queue_invar (dij_heap st)"
    and coup: "\<forall>x k. ((x,k) \<in> queue_abstract (dij_heap st)) = (x \<notin> seen_abstract (dij_seen st) \<and> dist_lookup (dij_dist st) x \<noteq> -1 \<and> k = dist_lookup (dij_dist st) x)"
    using I2 by (auto elim!: invar_2_props)
  have tN: "dij_target st = None" using I10 by (auto elim!: invar_10_props)
  have "\<exists>k. (u,k) \<in> queue_abstract (dij_heap st) \<and> (\<forall>x' k'. (x',k') \<in> queue_abstract (dij_heap st) \<longrightarrow> k \<le> k')"
    using heap.queue_extract_min(2)[OF qi, of u] ext by simp
  then obtain km where km: "(u,km) \<in> queue_abstract (dij_heap st)" "\<forall>x' k'. (x',k') \<in> queue_abstract (dij_heap st) \<longrightarrow> km \<le> k'" by blast
  have kmd: "km = dist_lookup (dij_dist st) u" using km(1) coup by blast
  have MIN: "\<And>y. y \<notin> seen_abstract (dij_seen st) \<Longrightarrow> dist_lookup (dij_dist st) y \<noteq> -1 \<Longrightarrow> dist_lookup (dij_dist st) u \<le> dist_lookup (dij_dist st) y"
  proof -
    fix y assume yns: "y \<notin> seen_abstract (dij_seen st)" and yr: "dist_lookup (dij_dist st) y \<noteq> -1"
    have "(y, dist_lookup (dij_dist st) y) \<in> queue_abstract (dij_heap st)" using coup yns yr by blast
    hence "km \<le> dist_lookup (dij_dist st) y" using km(2) by blast
    thus "dist_lookup (dij_dist st) u \<le> dist_lookup (dij_dist st) y" using kmd by simp
  qed
  have rem0: "src_remaining (dij_srcs st) = {}" using nsh sinv sources.has_current by auto
  have I9all: "\<forall>s. s \<in> src_abstract srcs \<longrightarrow> s \<notin> src_remaining (dij_srcs st) \<longrightarrow> dist_lookup (dij_dist st) s = 0" using I9 by (auto elim!: invar_9_props)
  have SRC0: "\<And>s. s \<in> src_abstract srcs \<Longrightarrow> dist_lookup (dij_dist st) s = 0" using I9all rem0 by simp
  obtain p s where sp: "s \<in> src_abstract srcs" "ag.is_shortest_path w p s v" "ag.distance w s v = ag.distance_set w (src_abstract srcs) v"
    using ag_dist_set_less_infty_get_path[OF finS infty] by blast
  have pb: "ag.path_bet p s v" and dp: "distinct p" and pd: "ag.distance w s v = ereal (weight w p)"
    using sp(2) by (auto simp: ag.is_shortest_path_def)
  have Deq: "ag.distance_set w (src_abstract srcs) v = ereal (weight w p)" using sp(3) pd by simp
  have ds0: "dist_lookup (dij_dist st) s = 0" using SRC0 sp(1) .
  have wp0: "0 \<le> weight w p" using weight_nonneg[of p] ag_path_bet_edges_subset[OF pb] by simp
  have "dist_lookup (dij_dist st) u \<le> weight w p"
  proof (cases "s \<in> seen_abstract (dij_seen st)")
    case True
    obtain y where y: "y \<notin> seen_abstract (dij_seen st)" "dist_lookup (dij_dist st) y \<noteq> -1" "dist_lookup (dij_dist st) y \<le> dist_lookup (dij_dist st) s + weight w p"
      using frontier_reach[OF finS cN tN I1 I2 I5 I7 I8 Iopt pb dp True vns] by blast
    have "dist_lookup (dij_dist st) u \<le> dist_lookup (dij_dist st) y" using MIN[OF y(1) y(2)] .
    thus ?thesis using y(3) ds0 by linarith
  next
    case False
    have dsne: "dist_lookup (dij_dist st) s \<noteq> -1" using ds0 by simp
    have "dist_lookup (dij_dist st) u \<le> dist_lookup (dij_dist st) s" using MIN[OF False dsne] .
    thus ?thesis using ds0 wp0 by linarith
  qed
  hence "ereal (dist_lookup (dij_dist st) u) \<le> ereal (weight w p)" by simp
  thus ?thesis using Deq by simp
qed (simp add: not_less)

text \<open>Preservation of the optimality invariant. The distance-changing branches (relax, init) never
      alter the distance of an already-settled vertex; settling (or returning) a new vertex adds it
      to the settled set with an optimal distance by @{thm settle_opt_bound}.\<close>

lemma invar_opt_holds_done[invar_holds_intros]: "\<lbrakk>dijkstra_ret_done_conds st; invar_opt st\<rbrakk> \<Longrightarrow> invar_opt (dijkstra_ret_done st)" by (simp add: dijkstra_ret_done_def invar_opt_def)
lemma invar_opt_holds_skip[invar_holds_intros]: "\<lbrakk>dijkstra_call_skip_conds st; invar_opt st\<rbrakk> \<Longrightarrow> invar_opt (dijkstra_upd_skip st)" by (auto simp: invar_opt_def dijkstra_upd_skip_def split: prod.splits)
lemma invar_opt_holds_finish[invar_holds_intros]: "\<lbrakk>dijkstra_call_finish_conds st; invar_opt st\<rbrakk> \<Longrightarrow> invar_opt (dijkstra_upd_finish st)" by (simp add: invar_opt_def dijkstra_upd_finish_def)

lemma invar_opt_holds_init[invar_holds_intros]: "\<lbrakk>dijkstra_call_init_conds st; invar_1 st; invar_4 st\<rbrakk> \<Longrightarrow> invar_opt (dijkstra_upd_init st)"
proof -
  assume a: "dijkstra_call_init_conds st" "invar_1 st" "invar_4 st"
  have srch: "src_has (dij_srcs st)" using a(1) by (auto elim!: dijkstra_call_init_condsE)
  have sinv: "src_invar (dij_srcs st)" using a(2) by (auto elim!: invar_1_props)
  have rem: "src_remaining (dij_srcs st) \<noteq> {}" using srch sinv sources.has_current by auto
  have seenE: "seen_abstract (dij_seen st) = {}" using a(3) rem by (auto elim!: invar_4_props)
  show ?thesis
    by (rule invar_opt_intro) (simp add: dijkstra_upd_init_def insert_source_def seenE)
qed

lemma invar_opt_holds_relax[invar_holds_intros]: "\<lbrakk>dijkstra_call_relax_conds st; invar_1 st; invar_2 st; invar_opt st\<rbrakk> \<Longrightarrow> invar_opt (dijkstra_upd_relax st)"
proof -
  assume a: "dijkstra_call_relax_conds st" "invar_1 st" "invar_2 st" "invar_opt st"
  obtain u where cu: "dij_curr st = Some u" and oh: "out_has (dij_graph st) u" using a(1) by (auto elim!: dijkstra_call_relax_condsE)
  have dinv: "dist_invar (dij_dist st)" using a(2) by (auto elim!: invar_1_props)
  have si: "seen_invar (dij_seen st)" using a(3) by (auto elim!: invar_2_props)
  have Iopt: "\<forall>v. v \<in> seen_abstract (dij_seen st) \<longrightarrow> ereal (dist_lookup (dij_dist st) v) \<le> ag.distance_set w (src_abstract srcs) v" using a(4) by (auto elim!: invar_opt_props)
  have gi: "out_graph_inv (dij_graph st)" using a(2) by (auto elim!: invar_1_props)
  have uV: "u \<in> \<V>" using a(3) cu by (auto elim!: invar_2_props)
  define e0 where "e0 = out_current (dij_graph st) u"
  have e0V: "snd e0 \<in> \<V>" using snd_E_V[OF out_current_edge[OF gi uV oh]] by (simp add: e0_def)
  define du where "du = dist_lookup (dij_dist st) u"
  define st' where "st' = st \<lparr> dij_graph := out_move (dij_graph st) u \<rparr>"
  have dd: "dij_dist st' = dij_dist st" and ds: "dij_seen st' = dij_seen st" by (simp_all add: st'_def)
  have dinv': "dist_invar (dij_dist st')" using dinv dd by simp
  have upd_eq: "dijkstra_upd_relax st = relax_edge u du e0 st'" by (simp add: dijkstra_upd_relax_def cu du_def e0_def st'_def)
  have seeneq: "dij_seen (dijkstra_upd_relax st) = dij_seen st" by (simp add: upd_eq ds)
  have F1: "\<And>v. v \<in> seen_abstract (dij_seen st) \<Longrightarrow> dist_lookup (dij_dist (dijkstra_upd_relax st)) v = dist_lookup (dij_dist st) v"
  proof -
    fix v assume vseen: "v \<in> seen_abstract (dij_seen st)"
    have "v = snd e0 \<longrightarrow> seen_isin (dij_seen st) (snd e0)" using vseen seen_set.fixed_univ_set_isin[OF si] by auto
    thus "dist_lookup (dij_dist (dijkstra_upd_relax st)) v = dist_lookup (dij_dist st) v"
      unfolding upd_eq by (subst relax_edge_dist_at[OF dinv' e0V]) (auto simp: dd ds)
  qed
  show ?thesis
    unfolding invar_opt_def seeneq
  proof (intro allI impI)
    fix v assume vseen: "v \<in> seen_abstract (dij_seen st)"
    have "ereal (dist_lookup (dij_dist (dijkstra_upd_relax st)) v) = ereal (dist_lookup (dij_dist st) v)" using F1 vseen by simp
    thus "ereal (dist_lookup (dij_dist (dijkstra_upd_relax st)) v) \<le> ag.distance_set w (src_abstract srcs) v" using Iopt vseen by simp
  qed
qed

lemma invar_opt_holds_settle[invar_holds_intros]: "\<lbrakk>dijkstra_call_settle_conds st; invar_1 st; invar_2 st; invar_5 st; invar_7 st; invar_8 st; invar_9 st; invar_10 st; invar_opt st\<rbrakk> \<Longrightarrow> invar_opt (dijkstra_upd_settle st)"
proof -
  assume a: "dijkstra_call_settle_conds st" "invar_1 st" "invar_2 st" "invar_5 st" "invar_7 st" "invar_8 st" "invar_9 st" "invar_10 st" "invar_opt st"
  obtain h2 u where hu: "dij_curr st = None" "\<not> src_has (dij_srcs st)" "queue_extract_min (dij_heap st) = (h2, Some u)" "\<not> seen_isin (dij_seen st) u"
    using a(1) by (auto elim!: dijkstra_call_settle_condsE)
  have qi: "queue_invar (dij_heap st)" and si: "seen_invar (dij_seen st)" and reachV: "\<forall>x. dist_lookup (dij_dist st) x \<noteq> -1 \<longrightarrow> x \<in> \<V>"
    and coup: "\<forall>x k. ((x,k) \<in> queue_abstract (dij_heap st)) = (x \<notin> seen_abstract (dij_seen st) \<and> dist_lookup (dij_dist st) x \<noteq> -1 \<and> k = dist_lookup (dij_dist st) x)"
    using a(3) by (auto elim!: invar_2_props)
  obtain k where uk: "(u,k) \<in> queue_abstract (dij_heap st)" using heap.queue_extract_min(2)[OF qi, of u] hu(3) by simp blast
  have ureach: "dist_lookup (dij_dist st) u \<noteq> -1" using uk coup by blast
  have uV: "u \<in> \<V>" using ureach reachV by blast
  have seenins: "seen_abstract (dij_seen (dijkstra_upd_settle st)) = insert u (seen_abstract (dij_seen st))"
    by (simp add: dijkstra_upd_settle_def hu(3) Let_def seen_set.fixed_univ_set_insert(2)[OF si uV])
  have distS: "dij_dist (dijkstra_upd_settle st) = dij_dist st" by (simp add: dijkstra_upd_settle_def hu(3) Let_def)
  have bound: "ereal (dist_lookup (dij_dist st) u) \<le> ag.distance_set w (src_abstract srcs) u"
    using settle_opt_bound[OF hu(1) hu(2) hu(3) a(2) a(3) a(4) a(5) a(6) a(7) a(8) a(9)] uk coup by blast
  have Iopt: "\<forall>v. v \<in> seen_abstract (dij_seen st) \<longrightarrow> ereal (dist_lookup (dij_dist st) v) \<le> ag.distance_set w (src_abstract srcs) v" using a(9) by (auto elim!: invar_opt_props)
  show ?thesis
    unfolding invar_opt_def seenins distS
  proof (intro allI impI)
    fix v assume "v \<in> insert u (seen_abstract (dij_seen st))"
    thus "ereal (dist_lookup (dij_dist st) v) \<le> ag.distance_set w (src_abstract srcs) v" using bound Iopt by auto
  qed
qed

lemma invar_opt_holds_found[invar_holds_intros]: "\<lbrakk>dijkstra_ret_found_conds st; invar_1 st; invar_2 st; invar_5 st; invar_7 st; invar_8 st; invar_9 st; invar_10 st; invar_opt st\<rbrakk> \<Longrightarrow> invar_opt (dijkstra_ret_found st)"
proof -
  assume a: "dijkstra_ret_found_conds st" "invar_1 st" "invar_2 st" "invar_5 st" "invar_7 st" "invar_8 st" "invar_9 st" "invar_10 st" "invar_opt st"
  obtain h2 u where hu: "dij_curr st = None" "\<not> src_has (dij_srcs st)" "queue_extract_min (dij_heap st) = (h2, Some u)" "\<not> seen_isin (dij_seen st) u"
    using a(1) by (auto elim!: dijkstra_ret_found_condsE)
  have qi: "queue_invar (dij_heap st)" and si: "seen_invar (dij_seen st)" and reachV: "\<forall>x. dist_lookup (dij_dist st) x \<noteq> -1 \<longrightarrow> x \<in> \<V>"
    and coup: "\<forall>x k. ((x,k) \<in> queue_abstract (dij_heap st)) = (x \<notin> seen_abstract (dij_seen st) \<and> dist_lookup (dij_dist st) x \<noteq> -1 \<and> k = dist_lookup (dij_dist st) x)"
    using a(3) by (auto elim!: invar_2_props)
  obtain k where uk: "(u,k) \<in> queue_abstract (dij_heap st)" using heap.queue_extract_min(2)[OF qi, of u] hu(3) by simp blast
  have ureach: "dist_lookup (dij_dist st) u \<noteq> -1" using uk coup by blast
  have uV: "u \<in> \<V>" using ureach reachV by blast
  have seenins: "seen_abstract (dij_seen (dijkstra_ret_found st)) = insert u (seen_abstract (dij_seen st))"
    by (simp add: dijkstra_ret_found_def hu(3) Let_def seen_set.fixed_univ_set_insert(2)[OF si uV])
  have distF: "dij_dist (dijkstra_ret_found st) = dij_dist st" by (simp add: dijkstra_ret_found_def hu(3) Let_def)
  have bound: "ereal (dist_lookup (dij_dist st) u) \<le> ag.distance_set w (src_abstract srcs) u"
    using settle_opt_bound[OF hu(1) hu(2) hu(3) a(2) a(3) a(4) a(5) a(6) a(7) a(8) a(9)] uk coup by blast
  have Iopt: "\<forall>v. v \<in> seen_abstract (dij_seen st) \<longrightarrow> ereal (dist_lookup (dij_dist st) v) \<le> ag.distance_set w (src_abstract srcs) v" using a(9) by (auto elim!: invar_opt_props)
  show ?thesis
    unfolding invar_opt_def seenins distF
  proof (intro allI impI)
    fix v assume "v \<in> insert u (seen_abstract (dij_seen st))"
    thus "ereal (dist_lookup (dij_dist st) v) \<le> ag.distance_set w (src_abstract srcs) v" using bound Iopt by auto
  qed
qed

lemma invar_opt_holds[invar_holds_intros]:
  assumes "dijkstra_dom st" "invar_1 st" "invar_2 st" "invar_3 st" "invar_4 st" "invar_5 st" "invar_6 st" "invar_7 st" "invar_8 st" "invar_9 st" "invar_10 st" "invar_opt st"
  shows "invar_opt (dijkstra st)"
  using assms(2-)
proof(induction rule: dijkstra_induct[OF assms(1)])
  case IH: (1 st)
  show ?case
    apply(rule dijkstra_cases[where st = st])
    by (auto intro!: IH(2-) intro: invar_holds_intros simp: dijkstra_simps[OF IH(1)])
qed

lemma invar_opt_initial[invar_holds_intros]: "invar_opt initial_state"
  by (auto simp: initial_state_def invar_opt_def seen_set.fixed_univ_set_empty(2))


subsubsection \<open>Exact-distance correctness of the computed result\<close>

lemma invar_8_compute: "invar_8 dijkstra_compute"
  unfolding dijkstra_compute_def
  by (rule invar_8_holds[OF initial_state_props(5) initial_state_props(1) initial_state_props(2) initial_state_props(3) initial_state_props(4) invar_8_initial])

lemma invar_opt_compute: "invar_opt dijkstra_compute"
  unfolding dijkstra_compute_def
  by (rule invar_opt_holds[OF initial_state_props(5) initial_state_props(1) initial_state_props(2) initial_state_props(3) initial_state_props(4) invar_5_initial invar_6_initial invar_7_initial invar_8_initial invar_9_initial invar_10_initial invar_opt_initial])

text \<open>The main correctness theorem: for every \<^emph>\<open>settled\<close> vertex the computed distance is exactly the
      shortest-path distance from the source set. Combined with @{thm dijkstra_compute_upper_bound}
      (soundness) this fully characterises the settled distances.\<close>

theorem dijkstra_compute_optimal:
  assumes "v \<in> seen_abstract (dij_seen dijkstra_compute)"
  shows "ereal (dist_lookup (dij_dist dijkstra_compute) v) = ag.distance_set w (src_abstract srcs) v"
proof -
  have opt: "ereal (dist_lookup (dij_dist dijkstra_compute) v) \<le> ag.distance_set w (src_abstract srcs) v"
    using invar_opt_compute assms by (auto elim!: invar_opt_props)
  have reached: "dist_lookup (dij_dist dijkstra_compute) v \<noteq> -1"
    using invar_8_compute assms by (auto elim!: invar_8_props)
  have sound: "ag.distance_set w (src_abstract srcs) v \<le> ereal (dist_lookup (dij_dist dijkstra_compute) v)"
    using invar_5_compute reached by (auto elim!: invar_5_props)
  show ?thesis using opt sound order.antisym by blast
qed


subsection \<open>Completeness: the reachable part is fully settled\<close>

text \<open>When @{term early_stop} is \<open>False\<close> the algorithm settles \<^emph>\<open>exactly\<close> the vertices reachable from
      the source set, so together with @{thm dijkstra_compute_optimal} the whole shortest-path tree of
      the reachable part is computed. The proof rests on three facts about the terminating
      configuration: no target has been found (so the run ended in the \<open>done\<close> branch), that branch
      leaves an empty queue with the cursor at rest, and the frontier invariant then makes the settled
      set closed under reachability.\<close>

subsubsection \<open>Without early stopping, no target is ever found\<close>

lemma invar_10_holds_done[invar_holds_intros]: "\<lbrakk>dijkstra_ret_done_conds st; invar_10 st\<rbrakk> \<Longrightarrow> invar_10 (dijkstra_ret_done st)" by (simp add: invar_10_def dijkstra_ret_done_def)
lemma invar_10_holds_found_ne[invar_holds_intros]: "\<lbrakk>dijkstra_ret_found_conds st; \<not> early_stop\<rbrakk> \<Longrightarrow> invar_10 (dijkstra_ret_found st)"
proof -
  assume a: "dijkstra_ret_found_conds st" "\<not> early_stop"
  have "early_stop" using a(1) by (auto elim!: dijkstra_ret_found_condsE)
  thus ?thesis using a(2) by simp
qed

lemma target_none_run:
  assumes "dijkstra_dom st" "\<not> early_stop" "invar_10 st"
  shows "invar_10 (dijkstra st)"
  using assms(2-)
proof (induction rule: dijkstra_induct[OF assms(1)])
  case IH: (1 st)
  show ?case
    apply (rule dijkstra_cases[where st = st])
    by (auto intro!: IH(2-) intro: invar_holds_intros simp: dijkstra_simps[OF IH(1)])
qed


subsubsection \<open>The terminating configuration\<close>

definition "terminal_state st \<longleftrightarrow> dij_curr st = None \<and> src_remaining (dij_srcs st) = {} \<and> (queue_abstract (dij_heap st) = {} \<or> dij_target st \<noteq> None)"

lemma terminal_ret_done[invar_holds_intros]: "\<lbrakk>dijkstra_ret_done_conds st; invar_1 st; invar_2 st\<rbrakk> \<Longrightarrow> terminal_state (dijkstra_ret_done st)"
proof -
  assume a: "dijkstra_ret_done_conds st" "invar_1 st" "invar_2 st"
  obtain h2 where hu: "dij_curr st = None" "\<not> src_has (dij_srcs st)" "queue_extract_min (dij_heap st) = (h2, None)" using a(1) by (auto elim!: dijkstra_ret_done_condsE)
  have sinv: "src_invar (dij_srcs st)" using a(2) by (auto elim!: invar_1_props)
  have qi: "queue_invar (dij_heap st)" using a(3) by (auto elim!: invar_2_props)
  have rem0: "src_remaining (dij_srcs st) = {}" using hu(2) sinv sources.has_current by auto
  have qe: "queue_abstract h2 = {}" using heap.queue_extract_min(5)[OF qi] hu(3) by simp
  show ?thesis using hu(1) hu(3) rem0 qe by (simp add: terminal_state_def dijkstra_ret_done_def)
qed

lemma terminal_ret_found[invar_holds_intros]: "\<lbrakk>dijkstra_ret_found_conds st; invar_1 st\<rbrakk> \<Longrightarrow> terminal_state (dijkstra_ret_found st)"
proof -
  assume a: "dijkstra_ret_found_conds st" "invar_1 st"
  obtain h2 u where hu: "dij_curr st = None" "\<not> src_has (dij_srcs st)" "queue_extract_min (dij_heap st) = (h2, Some u)" using a(1) by (auto elim!: dijkstra_ret_found_condsE)
  have sinv: "src_invar (dij_srcs st)" using a(2) by (auto elim!: invar_1_props)
  have rem0: "src_remaining (dij_srcs st) = {}" using hu(2) sinv sources.has_current by auto
  have curr: "dij_curr (dijkstra_ret_found st) = None" using hu(1) by (simp add: dijkstra_ret_found_def hu(3) Let_def)
  have tgt: "dij_target (dijkstra_ret_found st) = Some u" by (simp add: dijkstra_ret_found_def hu(3) Let_def)
  have srcs: "dij_srcs (dijkstra_ret_found st) = dij_srcs st" by (simp add: dijkstra_ret_found_def hu(3) Let_def)
  show ?thesis using curr rem0 tgt srcs by (simp add: terminal_state_def)
qed

lemma dijkstra_terminal:
  assumes "dijkstra_dom st" "invar_1 st" "invar_2 st" "invar_3 st" "invar_4 st"
  shows "terminal_state (dijkstra st)"
  using assms(2-)
proof (induction rule: dijkstra_induct[OF assms(1)])
  case IH: (1 st)
  show ?case
    apply (rule dijkstra_cases[where st = st])
    by (auto intro!: IH(2-) intro: invar_holds_intros simp: dijkstra_simps[OF IH(1)])
qed


subsubsection \<open>The settled set is closed under reachability\<close>

lemma reach_settled:
  assumes qe: "queue_abstract (dij_heap st) = {}" and cN: "dij_curr st = None" and tN: "dij_target st = None"
    and I1: "invar_1 st" and I2: "invar_2 st" and I7: "invar_7 st" and I8: "invar_8 st"
  shows "ag.path_bet p x v \<Longrightarrow> x \<in> seen_abstract (dij_seen st) \<Longrightarrow> v \<in> seen_abstract (dij_seen st)"
proof (induction p arbitrary: x)
  case Nil
  then show ?case by (auto simp: ag.path_bet_def)
next
  case (Cons e p')
  have gi: "out_graph_inv (dij_graph st)" using I1 by (auto elim!: invar_1_props)
  have oinv: "out_invar (dij_graph st)" using gi by (simp add: out_graph_inv_def)
  have sV: "seen_abstract (dij_seen st) \<subseteq> \<V>"
    and coup: "\<forall>x k. ((x,k) \<in> queue_abstract (dij_heap st)) = (x \<notin> seen_abstract (dij_seen st) \<and> dist_lookup (dij_dist st) x \<noteq> -1 \<and> k = dist_lookup (dij_dist st) x)"
    using I2 by (auto elim!: invar_2_props)
  have reached_seen: "\<And>z. dist_lookup (dij_dist st) z \<noteq> -1 \<Longrightarrow> z \<in> seen_abstract (dij_seen st)"
  proof -
    fix z assume zr: "dist_lookup (dij_dist st) z \<noteq> -1"
    show "z \<in> seen_abstract (dij_seen st)"
    proof (rule ccontr)
      assume "z \<notin> seen_abstract (dij_seen st)"
      hence "(z, dist_lookup (dij_dist st) z) \<in> queue_abstract (dij_heap st)" using coup zr by blast
      thus False using qe by simp
    qed
  qed
  have I7all: "\<forall>z. z \<in> seen_abstract (dij_seen st) \<longrightarrow> out_remaining (dij_graph st) z = {}" using I7 tN cN by (auto elim!: invar_7_props)
  have I8c: "\<forall>z e. z \<in> seen_abstract (dij_seen st) \<longrightarrow> e \<in> out_iterated (dij_graph st) z \<longrightarrow> allowed_edge e \<longrightarrow> (snd e \<in> seen_abstract (dij_seen st) \<or> (dist_lookup (dij_dist st) (snd e) \<noteq> -1 \<and> dist_lookup (dij_dist st) (snd e) \<le> dist_lookup (dij_dist st) z + w e))"
    using I8 by (auto elim!: invar_8_props)
  have pb: "ag.path_bet (e # p') x v" and xseen: "x \<in> seen_abstract (dij_seen st)" using Cons.prems by auto
  have eE: "e \<in> Ea" and efst: "fst e = x" and pb': "ag.path_bet p' (snd e) v" using pb by (auto elim: ag_path_bet_ConsE)
  have xV: "x \<in> \<V>" using xseen sV by blast
  have edelta: "e \<in> \<delta>\<^sup>+ x" using eE efst by (auto simp: delta_plus_def)
  have absx: "out_abstract (dij_graph st) x = \<delta>\<^sup>+ x" using gi xV by (auto simp: out_graph_inv_def)
  have remx: "out_remaining (dij_graph st) x = {}" using I7all xseen by blast
  have itx: "out_iterated (dij_graph st) x = \<delta>\<^sup>+ x" using outg.idx_partition_union[OF oinv xV] remx absx by simp
  have einit: "e \<in> out_iterated (dij_graph st) x" using edelta itx by simp
  have "snd e \<in> seen_abstract (dij_seen st) \<or> (dist_lookup (dij_dist st) (snd e) \<noteq> -1 \<and> dist_lookup (dij_dist st) (snd e) \<le> dist_lookup (dij_dist st) x + w e)"
    using I8c xseen einit eE by blast
  hence "snd e \<in> seen_abstract (dij_seen st)" using reached_seen by blast
  thus ?case using Cons.IH[OF pb'] by blast
qed


subsubsection \<open>Completeness of the computed distances\<close>

lemma invar_1_compute: "invar_1 dijkstra_compute" unfolding dijkstra_compute_def by (rule invar_1_holds[OF initial_state_props(5) initial_state_props(1) initial_state_props(2) initial_state_props(3) initial_state_props(4)])
lemma invar_2_compute: "invar_2 dijkstra_compute" unfolding dijkstra_compute_def by (rule invar_2_holds[OF initial_state_props(5) initial_state_props(1) initial_state_props(2) initial_state_props(3) initial_state_props(4)])
lemma invar_7_compute: "invar_7 dijkstra_compute" unfolding dijkstra_compute_def by (rule invar_7_holds[OF initial_state_props(5) initial_state_props(1) initial_state_props(2) initial_state_props(3) initial_state_props(4) invar_7_initial])
lemma invar_9_compute: "invar_9 dijkstra_compute" unfolding dijkstra_compute_def by (rule invar_9_holds[OF initial_state_props(5) initial_state_props(1) initial_state_props(2) initial_state_props(3) initial_state_props(4) invar_9_initial])

text \<open>With no early stopping, a vertex is reached (finite distance) if and only if it is reachable
      from some source. Combined with @{thm dijkstra_compute_optimal}, the recorded distance of every
      reachable vertex is its true shortest-path distance, and unreachable vertices keep the sentinel
      \<open>-1\<close>.\<close>

theorem dijkstra_compute_complete:
  assumes "\<not> early_stop"
  shows "dist_lookup (dij_dist dijkstra_compute) v \<noteq> -1 \<longleftrightarrow> (\<exists>s \<in> src_abstract srcs. ag.reachable s v)"
proof -
  have tstate: "terminal_state dijkstra_compute"
    unfolding dijkstra_compute_def by (rule dijkstra_terminal[OF initial_state_props(5) initial_state_props(1) initial_state_props(2) initial_state_props(3) initial_state_props(4)])
  have tN: "dij_target dijkstra_compute = None"
    unfolding dijkstra_compute_def using target_none_run[OF initial_state_props(5) assms invar_10_initial] by (auto elim!: invar_10_props)
  have qe: "queue_abstract (dij_heap dijkstra_compute) = {}" and cN: "dij_curr dijkstra_compute = None" and rem0: "src_remaining (dij_srcs dijkstra_compute) = {}"
    using tstate tN by (auto simp: terminal_state_def)
  have I8a: "\<forall>x. x \<in> seen_abstract (dij_seen dijkstra_compute) \<longrightarrow> dist_lookup (dij_dist dijkstra_compute) x \<noteq> -1"
    using invar_8_compute by (auto elim!: invar_8_props)
  have coup: "\<forall>x k. ((x,k) \<in> queue_abstract (dij_heap dijkstra_compute)) = (x \<notin> seen_abstract (dij_seen dijkstra_compute) \<and> dist_lookup (dij_dist dijkstra_compute) x \<noteq> -1 \<and> k = dist_lookup (dij_dist dijkstra_compute) x)"
    using invar_2_compute by (auto elim!: invar_2_props)
  have reached_seen: "\<And>z. dist_lookup (dij_dist dijkstra_compute) z \<noteq> -1 \<Longrightarrow> z \<in> seen_abstract (dij_seen dijkstra_compute)"
  proof -
    fix z assume zr: "dist_lookup (dij_dist dijkstra_compute) z \<noteq> -1"
    show "z \<in> seen_abstract (dij_seen dijkstra_compute)"
    proof (rule ccontr)
      assume "z \<notin> seen_abstract (dij_seen dijkstra_compute)"
      hence "(z, dist_lookup (dij_dist dijkstra_compute) z) \<in> queue_abstract (dij_heap dijkstra_compute)" using coup zr by blast
      thus False using qe by simp
    qed
  qed
  have I9all: "\<forall>s. s \<in> src_abstract srcs \<longrightarrow> s \<notin> src_remaining (dij_srcs dijkstra_compute) \<longrightarrow> dist_lookup (dij_dist dijkstra_compute) s = 0"
    using invar_9_compute by (auto elim!: invar_9_props)
  show ?thesis
  proof
    assume "dist_lookup (dij_dist dijkstra_compute) v \<noteq> -1"
    hence "ag.distance_set w (src_abstract srcs) v \<le> ereal (dist_lookup (dij_dist dijkstra_compute) v)" using invar_5_compute by (auto elim!: invar_5_props)
    hence "ag.distance_set w (src_abstract srcs) v \<noteq> \<infinity>" using order_le_less_trans by fastforce
    thus "\<exists>s \<in> src_abstract srcs. ag.reachable s v" using ag_distance_set_infty_iff by auto
  next
    assume "\<exists>s \<in> src_abstract srcs. ag.reachable s v"
    then obtain s where sS: "s \<in> src_abstract srcs" and reach: "ag.reachable s v" by blast
    have "s \<notin> src_remaining (dij_srcs dijkstra_compute)" using rem0 by simp
    hence "dist_lookup (dij_dist dijkstra_compute) s = 0" using I9all sS by blast
    hence sseen: "s \<in> seen_abstract (dij_seen dijkstra_compute)" using reached_seen by simp
    obtain p where pb: "ag.path_bet p s v" using reach ag_reachable_iff_path by blast
    have "v \<in> seen_abstract (dij_seen dijkstra_compute)"
      using reach_settled[OF qe cN tN invar_1_compute invar_2_compute invar_7_compute invar_8_compute pb sseen] .
    thus "dist_lookup (dij_dist dijkstra_compute) v \<noteq> -1" using I8a by blast
  qed
qed


subsection \<open>The shortest-path tree recorded in the parent map\<close>

text \<open>The parent array stores, for every reached vertex, the edge by which its current distance was
      achieved. We show these edges form a valid \<^emph>\<open>tight\<close> tree: the parent of \<open>v\<close> is an edge \<open>e\<close> into
      \<open>v\<close> whose tail is already settled and satisfies \<open>dist v = dist (fst e) + w e\<close>. This lets us read
      off, for any reached vertex, an actual shortest path back to a source.\<close>

lemma relax_edge_parent_at:
  assumes "parent_invar (dij_parent st)" "snd e \<in> \<V>"
  shows "parent_lookup (dij_parent (relax_edge u du e st)) x =
    (if x = snd e \<and> \<not> seen_isin (dij_seen st) (snd e) \<and> allowed_edge e \<and>
        (dist_lookup (dij_dist st) (snd e) = -1 \<or> du + w e < dist_lookup (dij_dist st) (snd e))
     then Some e else parent_lookup (dij_parent st) x)"
  by (auto simp: relax_edge_def Let_def parent_arr.fixed_univ_map_upd[OF assms] split: if_splits)

definition "invar_tree st \<longleftrightarrow> (\<forall>v e. parent_lookup (dij_parent st) v = Some e \<longrightarrow> fst e \<in> seen_abstract (dij_seen st) \<and> snd e = v \<and> e \<in> Ea \<and> dist_lookup (dij_dist st) (fst e) \<noteq> -1 \<and> dist_lookup (dij_dist st) v = dist_lookup (dij_dist st) (fst e) + w e)"
lemma invar_tree_props[invar_props_elims]: "invar_tree st \<Longrightarrow> (\<lbrakk>\<And>v e. parent_lookup (dij_parent st) v = Some e \<Longrightarrow> fst e \<in> seen_abstract (dij_seen st) \<and> snd e = v \<and> e \<in> Ea \<and> dist_lookup (dij_dist st) (fst e) \<noteq> -1 \<and> dist_lookup (dij_dist st) v = dist_lookup (dij_dist st) (fst e) + w e\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P" by (auto simp: invar_tree_def)
lemma invar_tree_intro[invar_props_intros]: "(\<And>v e. parent_lookup (dij_parent st) v = Some e \<Longrightarrow> fst e \<in> seen_abstract (dij_seen st) \<and> snd e = v \<and> e \<in> Ea \<and> dist_lookup (dij_dist st) (fst e) \<noteq> -1 \<and> dist_lookup (dij_dist st) v = dist_lookup (dij_dist st) (fst e) + w e) \<Longrightarrow> invar_tree st" by (auto simp: invar_tree_def)
lemma invar_tree_D: "invar_tree st \<Longrightarrow> parent_lookup (dij_parent st) v = Some e \<Longrightarrow> fst e \<in> seen_abstract (dij_seen st) \<and> snd e = v \<and> e \<in> Ea \<and> dist_lookup (dij_dist st) (fst e) \<noteq> -1 \<and> dist_lookup (dij_dist st) v = dist_lookup (dij_dist st) (fst e) + w e" by (auto simp: invar_tree_def)

lemma invar_tree_holds_done[invar_holds_intros]: "\<lbrakk>dijkstra_ret_done_conds st; invar_tree st\<rbrakk> \<Longrightarrow> invar_tree (dijkstra_ret_done st)" by (auto simp: dijkstra_ret_done_def elim!: invar_props_elims intro!: invar_props_intros)
lemma invar_tree_holds_skip[invar_holds_intros]: "\<lbrakk>dijkstra_call_skip_conds st; invar_tree st\<rbrakk> \<Longrightarrow> invar_tree (dijkstra_upd_skip st)" by (auto simp: dijkstra_upd_skip_def elim!: invar_props_elims intro!: invar_props_intros split: prod.splits)
lemma invar_tree_holds_finish[invar_holds_intros]: "\<lbrakk>dijkstra_call_finish_conds st; invar_tree st\<rbrakk> \<Longrightarrow> invar_tree (dijkstra_upd_finish st)" by (auto simp: dijkstra_upd_finish_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_tree_holds_settle[invar_holds_intros]: "\<lbrakk>dijkstra_call_settle_conds st; invar_1 st; invar_2 st; invar_tree st\<rbrakk> \<Longrightarrow> invar_tree (dijkstra_upd_settle st)"
proof -
  assume a: "dijkstra_call_settle_conds st" "invar_1 st" "invar_2 st" "invar_tree st"
  obtain h2 u where hu: "queue_extract_min (dij_heap st) = (h2, Some u)" using a(1) by (auto elim!: dijkstra_call_settle_condsE)
  have qi: "queue_invar (dij_heap st)" and si: "seen_invar (dij_seen st)" and reachV: "\<forall>x. dist_lookup (dij_dist st) x \<noteq> -1 \<longrightarrow> x \<in> \<V>"
    and coup: "\<forall>x k. ((x,k) \<in> queue_abstract (dij_heap st)) = (x \<notin> seen_abstract (dij_seen st) \<and> dist_lookup (dij_dist st) x \<noteq> -1 \<and> k = dist_lookup (dij_dist st) x)" using a(3) by (auto elim!: invar_2_props)
  obtain k where uk: "(u,k) \<in> queue_abstract (dij_heap st)" using heap.queue_extract_min(2)[OF qi, of u] hu by simp blast
  have uV: "u \<in> \<V>" using uk coup reachV by blast
  show ?thesis using a(4)
    by (auto simp: dijkstra_upd_settle_def Let_def hu seen_set.fixed_univ_set_insert(2)[OF si uV] elim!: invar_tree_props intro!: invar_tree_intro)
qed

lemma invar_tree_holds_found[invar_holds_intros]: "\<lbrakk>dijkstra_ret_found_conds st; invar_1 st; invar_2 st; invar_tree st\<rbrakk> \<Longrightarrow> invar_tree (dijkstra_ret_found st)"
proof -
  assume a: "dijkstra_ret_found_conds st" "invar_1 st" "invar_2 st" "invar_tree st"
  obtain h2 u where hu: "queue_extract_min (dij_heap st) = (h2, Some u)" using a(1) by (auto elim!: dijkstra_ret_found_condsE)
  have qi: "queue_invar (dij_heap st)" and si: "seen_invar (dij_seen st)" and reachV: "\<forall>x. dist_lookup (dij_dist st) x \<noteq> -1 \<longrightarrow> x \<in> \<V>"
    and coup: "\<forall>x k. ((x,k) \<in> queue_abstract (dij_heap st)) = (x \<notin> seen_abstract (dij_seen st) \<and> dist_lookup (dij_dist st) x \<noteq> -1 \<and> k = dist_lookup (dij_dist st) x)" using a(3) by (auto elim!: invar_2_props)
  obtain k where uk: "(u,k) \<in> queue_abstract (dij_heap st)" using heap.queue_extract_min(2)[OF qi, of u] hu by simp blast
  have uV: "u \<in> \<V>" using uk coup reachV by blast
  show ?thesis using a(4)
    by (auto simp: dijkstra_ret_found_def Let_def hu seen_set.fixed_univ_set_insert(2)[OF si uV] elim!: invar_tree_props intro!: invar_tree_intro)
qed

lemma invar_tree_holds_init[invar_holds_intros]: "\<lbrakk>dijkstra_call_init_conds st; invar_1 st; invar_4 st; invar_tree st\<rbrakk> \<Longrightarrow> invar_tree (dijkstra_upd_init st)"
proof -
  assume a: "dijkstra_call_init_conds st" "invar_1 st" "invar_4 st" "invar_tree st"
  have srch: "src_has (dij_srcs st)" using a(1) by (auto elim!: dijkstra_call_init_condsE)
  have sinv: "src_invar (dij_srcs st)" using a(2) by (auto elim!: invar_1_props)
  have rem: "src_remaining (dij_srcs st) \<noteq> {}" using srch sinv sources.has_current by auto
  have seenE: "seen_abstract (dij_seen st) = {}" using a(3) rem by (auto elim!: invar_4_props)
  show ?thesis using a(4) seenE
    by (auto simp: dijkstra_upd_init_def insert_source_def elim!: invar_tree_props intro!: invar_tree_intro)
qed

text \<open>The one substantial branch: relaxing the current edge either sets the head's parent to that
      edge (which is tight by construction) or leaves the map untouched; an already-recorded parent
      cannot point to the freshly-relaxed head, since that head is unsettled while all parents are
      settled.\<close>

lemma invar_tree_holds_relax[invar_holds_intros]: "\<lbrakk>dijkstra_call_relax_conds st; invar_1 st; invar_2 st; invar_3 st; invar_tree st\<rbrakk> \<Longrightarrow> invar_tree (dijkstra_upd_relax st)"
proof -
  assume a: "dijkstra_call_relax_conds st" "invar_1 st" "invar_2 st" "invar_3 st" "invar_tree st"
  obtain u where cu: "dij_curr st = Some u" and oh: "out_has (dij_graph st) u" using a(1) by (auto elim!: dijkstra_call_relax_condsE)
  have gi: "out_graph_inv (dij_graph st)" and dinv: "dist_invar (dij_dist st)" and pinv: "parent_invar (dij_parent st)" using a(2) by (auto elim!: invar_1_props)
  have uV: "u \<in> \<V>" and si: "seen_invar (dij_seen st)" using a(3) cu by (auto elim!: invar_2_props)
  have useen: "u \<in> seen_abstract (dij_seen st)" and du_ne: "dist_lookup (dij_dist st) u \<noteq> -1" using a(4) cu by (auto elim!: invar_3_props)
  have eE: "out_current (dij_graph st) u \<in> \<E>" and efst: "fst (out_current (dij_graph st) u) = u" using out_current_edge[OF gi uV oh] out_current_fst[OF gi uV oh] by auto
  define st' where "st' = st \<lparr> dij_graph := out_move (dij_graph st) u \<rparr>"
  have dd: "dij_dist st' = dij_dist st" "dij_seen st' = dij_seen st" "dij_parent st' = dij_parent st" by (simp_all add: st'_def)
  have dinv': "dist_invar (dij_dist st')" and pinv': "parent_invar (dij_parent st')" using dinv pinv dd by simp+
  have hV: "snd (out_current (dij_graph st) u) \<in> \<V>" using snd_E_V[OF eE] .
  have upd: "dijkstra_upd_relax st = relax_edge u (dist_lookup (dij_dist st) u) (out_current (dij_graph st) u) st'"
    by (simp add: dijkstra_upd_relax_def cu st'_def)
  note isin = seen_set.fixed_univ_set_isin[OF si]
  have seenF: "dij_seen (dijkstra_upd_relax st) = dij_seen st" by (simp add: upd dd)
  have parF: "\<And>x. parent_lookup (dij_parent (dijkstra_upd_relax st)) x = (if x = snd (out_current (dij_graph st) u) \<and> \<not> seen_isin (dij_seen st) (snd (out_current (dij_graph st) u)) \<and> allowed_edge (out_current (dij_graph st) u) \<and> (dist_lookup (dij_dist st) (snd (out_current (dij_graph st) u)) = -1 \<or> dist_lookup (dij_dist st) u + w (out_current (dij_graph st) u) < dist_lookup (dij_dist st) (snd (out_current (dij_graph st) u))) then Some (out_current (dij_graph st) u) else parent_lookup (dij_parent st) x)"
    unfolding upd by (subst relax_edge_parent_at[OF pinv' hV]) (auto simp: dd)
  have distF: "\<And>x. dist_lookup (dij_dist (dijkstra_upd_relax st)) x = (if x = snd (out_current (dij_graph st) u) \<and> \<not> seen_isin (dij_seen st) (snd (out_current (dij_graph st) u)) \<and> allowed_edge (out_current (dij_graph st) u) \<and> (dist_lookup (dij_dist st) (snd (out_current (dij_graph st) u)) = -1 \<or> dist_lookup (dij_dist st) u + w (out_current (dij_graph st) u) < dist_lookup (dij_dist st) (snd (out_current (dij_graph st) u))) then dist_lookup (dij_dist st) u + w (out_current (dij_graph st) u) else dist_lookup (dij_dist st) x)"
    unfolding upd by (subst relax_edge_dist_at[OF dinv' hV]) (auto simp: dd)
  show ?thesis
  proof (rule invar_tree_intro)
    fix v e assume p: "parent_lookup (dij_parent (dijkstra_upd_relax st)) v = Some e"
    show "fst e \<in> seen_abstract (dij_seen (dijkstra_upd_relax st)) \<and> snd e = v \<and> e \<in> Ea \<and> dist_lookup (dij_dist (dijkstra_upd_relax st)) (fst e) \<noteq> -1 \<and> dist_lookup (dij_dist (dijkstra_upd_relax st)) v = dist_lookup (dij_dist (dijkstra_upd_relax st)) (fst e) + w e"
    proof (cases "v = snd (out_current (dij_graph st) u) \<and> \<not> seen_isin (dij_seen st) (snd (out_current (dij_graph st) u)) \<and> allowed_edge (out_current (dij_graph st) u) \<and> (dist_lookup (dij_dist st) (snd (out_current (dij_graph st) u)) = -1 \<or> dist_lookup (dij_dist st) u + w (out_current (dij_graph st) u) < dist_lookup (dij_dist st) (snd (out_current (dij_graph st) u)))")
      case True
      thus ?thesis using p useen du_ne eE efst by (auto simp: parF distF seenF isin split: if_splits)
    next
      case False
      have pe: "parent_lookup (dij_parent st) v = Some e" using p by (simp add: parF if_not_P[OF False])
      show ?thesis using invar_tree_D[OF a(5) pe] False by (auto simp: parF distF seenF isin split: if_splits)
    qed
  qed
qed

lemma invar_tree_holds[invar_holds_intros]:
  assumes "dijkstra_dom st" "invar_1 st" "invar_2 st" "invar_3 st" "invar_4 st" "invar_tree st"
  shows "invar_tree (dijkstra st)"
  using assms(2-)
proof (induction rule: dijkstra_induct[OF assms(1)])
  case IH: (1 st)
  show ?case
    apply (rule dijkstra_cases[where st = st])
    by (auto intro!: IH(2-) intro: invar_holds_intros simp: dijkstra_simps[OF IH(1)])
qed

lemma invar_tree_initial[invar_holds_intros]: "invar_tree initial_state"
  by (auto simp: initial_state_def invar_tree_def parent_init_none)


subsubsection \<open>The tree is acyclic\<close>

text \<open>The parent pointers, viewed as the relation \<open>fst e \<rightarrow> v\<close> for \<open>parent v = Some e\<close>, are
      well-founded: relaxing an edge only ever adds a pointer \<^emph>\<open>into\<close> the freshly-relaxed head, which
      is still unsettled and therefore has no outgoing pointer, so no cycle can form.\<close>

definition "par_rel st = {(fst e, v) | v e. parent_lookup (dij_parent st) v = Some e}"
definition "invar_wf st \<longleftrightarrow> wf (par_rel st)"
lemma invar_wf_props[invar_props_elims]: "invar_wf st \<Longrightarrow> (wf (par_rel st) \<Longrightarrow> P) \<Longrightarrow> P" by (auto simp: invar_wf_def)
lemma invar_wf_intro[invar_props_intros]: "wf (par_rel st) \<Longrightarrow> invar_wf st" by (auto simp: invar_wf_def)

lemma invar_wf_holds_done[invar_holds_intros]: "\<lbrakk>dijkstra_ret_done_conds st; invar_wf st\<rbrakk> \<Longrightarrow> invar_wf (dijkstra_ret_done st)" by (simp add: invar_wf_def par_rel_def dijkstra_ret_done_def)
lemma invar_wf_holds_skip[invar_holds_intros]: "\<lbrakk>dijkstra_call_skip_conds st; invar_wf st\<rbrakk> \<Longrightarrow> invar_wf (dijkstra_upd_skip st)" by (simp add: invar_wf_def par_rel_def dijkstra_upd_skip_def split: prod.splits)
lemma invar_wf_holds_finish[invar_holds_intros]: "\<lbrakk>dijkstra_call_finish_conds st; invar_wf st\<rbrakk> \<Longrightarrow> invar_wf (dijkstra_upd_finish st)" by (simp add: invar_wf_def par_rel_def dijkstra_upd_finish_def)
lemma invar_wf_holds_settle[invar_holds_intros]: "\<lbrakk>dijkstra_call_settle_conds st; invar_wf st\<rbrakk> \<Longrightarrow> invar_wf (dijkstra_upd_settle st)" by (simp add: invar_wf_def par_rel_def dijkstra_upd_settle_def Let_def split: prod.splits)
lemma invar_wf_holds_found[invar_holds_intros]: "\<lbrakk>dijkstra_ret_found_conds st; invar_wf st\<rbrakk> \<Longrightarrow> invar_wf (dijkstra_ret_found st)" by (simp add: invar_wf_def par_rel_def dijkstra_ret_found_def Let_def split: prod.splits)
lemma invar_wf_holds_init[invar_holds_intros]: "\<lbrakk>dijkstra_call_init_conds st; invar_wf st\<rbrakk> \<Longrightarrow> invar_wf (dijkstra_upd_init st)" by (simp add: invar_wf_def par_rel_def dijkstra_upd_init_def insert_source_def)

lemma invar_wf_holds_relax[invar_holds_intros]: "\<lbrakk>dijkstra_call_relax_conds st; invar_1 st; invar_2 st; invar_3 st; invar_tree st; invar_wf st\<rbrakk> \<Longrightarrow> invar_wf (dijkstra_upd_relax st)"
proof -
  assume a: "dijkstra_call_relax_conds st" "invar_1 st" "invar_2 st" "invar_3 st" "invar_tree st" "invar_wf st"
  obtain u where cu: "dij_curr st = Some u" and oh: "out_has (dij_graph st) u" using a(1) by (auto elim!: dijkstra_call_relax_condsE)
  have gi: "out_graph_inv (dij_graph st)" and pinv: "parent_invar (dij_parent st)" using a(2) by (auto elim!: invar_1_props)
  have uV: "u \<in> \<V>" and si: "seen_invar (dij_seen st)" using a(3) cu by (auto elim!: invar_2_props)
  have useen: "u \<in> seen_abstract (dij_seen st)" using a(4) cu by (auto elim!: invar_3_props)
  have efst: "fst (out_current (dij_graph st) u) = u" using out_current_fst[OF gi uV oh] by simp
  have hV: "snd (out_current (dij_graph st) u) \<in> \<V>" using snd_E_V[OF out_current_edge[OF gi uV oh]] .
  have wfst: "wf (par_rel st)" using a(6) by (auto elim!: invar_wf_props)
  have dom: "Domain (par_rel st) \<subseteq> seen_abstract (dij_seen st)" using a(5) by (auto simp: par_rel_def dest: invar_tree_D)
  define st' where "st' = st \<lparr> dij_graph := out_move (dij_graph st) u \<rparr>"
  have dd: "dij_dist st' = dij_dist st" "dij_seen st' = dij_seen st" "dij_parent st' = dij_parent st" by (simp_all add: st'_def)
  have pinv': "parent_invar (dij_parent st')" using pinv dd by simp
  have upd: "dijkstra_upd_relax st = relax_edge u (dist_lookup (dij_dist st) u) (out_current (dij_graph st) u) st'"
    by (simp add: dijkstra_upd_relax_def cu st'_def)
  have parF: "\<And>x. parent_lookup (dij_parent (dijkstra_upd_relax st)) x = (if x = snd (out_current (dij_graph st) u) \<and> \<not> seen_isin (dij_seen st) (snd (out_current (dij_graph st) u)) \<and> allowed_edge (out_current (dij_graph st) u) \<and> (dist_lookup (dij_dist st) (snd (out_current (dij_graph st) u)) = -1 \<or> dist_lookup (dij_dist st) u + w (out_current (dij_graph st) u) < dist_lookup (dij_dist st) (snd (out_current (dij_graph st) u))) then Some (out_current (dij_graph st) u) else parent_lookup (dij_parent st) x)"
    unfolding upd by (subst relax_edge_parent_at[OF pinv' hV]) (auto simp: dd)
  have sub: "par_rel (dijkstra_upd_relax st) \<subseteq> insert (u, snd (out_current (dij_graph st) u)) (par_rel st)"
    by (auto simp: par_rel_def parF efst split: if_splits)
  show ?thesis
  proof (cases "seen_isin (dij_seen st) (snd (out_current (dij_graph st) u))")
    case True
    hence "par_rel (dijkstra_upd_relax st) = par_rel st" by (auto simp: par_rel_def parF)
    thus ?thesis using wfst by (simp add: invar_wf_def)
  next
    case False
    hence v0ns: "snd (out_current (dij_graph st) u) \<notin> seen_abstract (dij_seen st)" using si seen_set.fixed_univ_set_isin by auto
    have v0nd: "snd (out_current (dij_graph st) u) \<notin> Domain (par_rel st)" using dom v0ns by auto
    have une: "u \<noteq> snd (out_current (dij_graph st) u)" using useen v0ns by auto
    have noout: "\<And>y. (snd (out_current (dij_graph st) u), y) \<notin> par_rel st" using v0nd by (auto simp: Domain_iff)
    have "(snd (out_current (dij_graph st) u), u) \<notin> (par_rel st)\<^sup>*" using une noout by (metis converse_rtranclE)
    hence wfins: "wf (insert (u, snd (out_current (dij_graph st) u)) (par_rel st))" using wfst by simp
    show ?thesis unfolding invar_wf_def by (rule wf_subset[OF wfins sub])
  qed
qed

lemma invar_wf_holds[invar_holds_intros]:
  assumes "dijkstra_dom st" "invar_1 st" "invar_2 st" "invar_3 st" "invar_4 st" "invar_tree st" "invar_wf st"
  shows "invar_wf (dijkstra st)"
  using assms(2-)
proof (induction rule: dijkstra_induct[OF assms(1)])
  case IH: (1 st)
  show ?case
    apply (rule dijkstra_cases[where st = st])
    by (auto intro!: IH(2-) intro: invar_holds_intros simp: dijkstra_simps[OF IH(1)])
qed

lemma invar_wf_initial[invar_holds_intros]: "invar_wf initial_state"
  by (auto simp: initial_state_def invar_wf_def par_rel_def parent_init_none)


subsubsection \<open>A vertex reached with no parent is a source\<close>

definition "invar_root st \<longleftrightarrow> (\<forall>v. dist_lookup (dij_dist st) v \<noteq> -1 \<longrightarrow> parent_lookup (dij_parent st) v = None \<longrightarrow> v \<in> src_abstract srcs)"
lemma invar_root_props[invar_props_elims]: "invar_root st \<Longrightarrow> (\<lbrakk>\<And>v. dist_lookup (dij_dist st) v \<noteq> -1 \<Longrightarrow> parent_lookup (dij_parent st) v = None \<Longrightarrow> v \<in> src_abstract srcs\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P" by (auto simp: invar_root_def)
lemma invar_root_intro[invar_props_intros]: "(\<And>v. dist_lookup (dij_dist st) v \<noteq> -1 \<Longrightarrow> parent_lookup (dij_parent st) v = None \<Longrightarrow> v \<in> src_abstract srcs) \<Longrightarrow> invar_root st" by (auto simp: invar_root_def)

lemma invar_root_holds_done[invar_holds_intros]: "\<lbrakk>dijkstra_ret_done_conds st; invar_root st\<rbrakk> \<Longrightarrow> invar_root (dijkstra_ret_done st)" by (auto simp: invar_root_def dijkstra_ret_done_def elim!: invar_props_elims intro!: invar_props_intros)
lemma invar_root_holds_skip[invar_holds_intros]: "\<lbrakk>dijkstra_call_skip_conds st; invar_root st\<rbrakk> \<Longrightarrow> invar_root (dijkstra_upd_skip st)" by (auto simp: invar_root_def dijkstra_upd_skip_def elim!: invar_props_elims intro!: invar_props_intros split: prod.splits)
lemma invar_root_holds_finish[invar_holds_intros]: "\<lbrakk>dijkstra_call_finish_conds st; invar_root st\<rbrakk> \<Longrightarrow> invar_root (dijkstra_upd_finish st)" by (auto simp: invar_root_def dijkstra_upd_finish_def elim!: invar_props_elims intro!: invar_props_intros)
lemma invar_root_holds_settle[invar_holds_intros]: "\<lbrakk>dijkstra_call_settle_conds st; invar_root st\<rbrakk> \<Longrightarrow> invar_root (dijkstra_upd_settle st)" by (auto simp: invar_root_def dijkstra_upd_settle_def Let_def elim!: invar_props_elims intro!: invar_props_intros split: prod.splits)
lemma invar_root_holds_found[invar_holds_intros]: "\<lbrakk>dijkstra_ret_found_conds st; invar_root st\<rbrakk> \<Longrightarrow> invar_root (dijkstra_ret_found st)" by (auto simp: invar_root_def dijkstra_ret_found_def Let_def elim!: invar_props_elims intro!: invar_props_intros split: prod.splits)

lemma invar_root_holds_init[invar_holds_intros]: "\<lbrakk>dijkstra_call_init_conds st; invar_1 st; invar_6 st; invar_root st\<rbrakk> \<Longrightarrow> invar_root (dijkstra_upd_init st)"
proof -
  assume a: "dijkstra_call_init_conds st" "invar_1 st" "invar_6 st" "invar_root st"
  have srch: "src_has (dij_srcs st)" using a(1) by (auto elim!: dijkstra_call_init_condsE)
  have sinv: "src_invar (dij_srcs st)" and dinv: "dist_invar (dij_dist st)" using a(2) by (auto elim!: invar_1_props)
  have sabs: "src_abstract (dij_srcs st) = src_abstract srcs" using a(3) by (auto elim!: invar_props_elims)
  have rem: "src_remaining (dij_srcs st) \<noteq> {}" using srch sinv sources.has_current by auto
  define v0 where "v0 = src_current (dij_srcs st)"
  have v0S: "v0 \<in> src_abstract srcs" using sources.current_element[OF sinv rem] sources.iterable_set_abstract(2)[OF sinv] sabs by (auto simp: v0_def)
  have v0V: "v0 \<in> \<V>" using v0S srcs_in_V by blast
  have I: "\<forall>v. dist_lookup (dij_dist st) v \<noteq> -1 \<longrightarrow> parent_lookup (dij_parent st) v = None \<longrightarrow> v \<in> src_abstract srcs" using a(4) by (auto elim!: invar_root_props)
  show ?thesis
  proof (rule invar_root_intro)
    fix v assume r: "dist_lookup (dij_dist (dijkstra_upd_init st)) v \<noteq> -1" and pn: "parent_lookup (dij_parent (dijkstra_upd_init st)) v = None"
    have dupd: "dist_lookup (dij_dist (dijkstra_upd_init st)) v = (if v = v0 then 0 else dist_lookup (dij_dist st) v)"
      by (simp add: dijkstra_upd_init_def insert_source_def v0_def dist_arr.fixed_univ_map_upd[OF dinv v0V[unfolded v0_def]])
    show "v \<in> src_abstract srcs"
    proof (cases "v = v0")
      case True thus ?thesis using v0S by simp
    next
      case False
      hence "dist_lookup (dij_dist st) v \<noteq> -1" using r dupd by simp
      moreover have "parent_lookup (dij_parent st) v = None" using pn by (simp add: dijkstra_upd_init_def insert_source_def)
      ultimately show ?thesis using I by blast
    qed
  qed
qed

lemma invar_root_holds_relax[invar_holds_intros]: "\<lbrakk>dijkstra_call_relax_conds st; invar_1 st; invar_2 st; invar_root st\<rbrakk> \<Longrightarrow> invar_root (dijkstra_upd_relax st)"
proof -
  assume a: "dijkstra_call_relax_conds st" "invar_1 st" "invar_2 st" "invar_root st"
  obtain u where cu: "dij_curr st = Some u" and oh: "out_has (dij_graph st) u" using a(1) by (auto elim!: dijkstra_call_relax_condsE)
  have dinv: "dist_invar (dij_dist st)" and pinv: "parent_invar (dij_parent st)" and gi: "out_graph_inv (dij_graph st)" using a(2) by (auto elim!: invar_1_props)
  have uV: "u \<in> \<V>" using a(3) cu by (auto elim!: invar_2_props)
  have hV: "snd (out_current (dij_graph st) u) \<in> \<V>" using snd_E_V[OF out_current_edge[OF gi uV oh]] .
  have I: "\<forall>v. dist_lookup (dij_dist st) v \<noteq> -1 \<longrightarrow> parent_lookup (dij_parent st) v = None \<longrightarrow> v \<in> src_abstract srcs" using a(4) by (auto elim!: invar_root_props)
  define st' where "st' = st \<lparr> dij_graph := out_move (dij_graph st) u \<rparr>"
  have dd: "dij_dist st' = dij_dist st" "dij_seen st' = dij_seen st" "dij_parent st' = dij_parent st" by (simp_all add: st'_def)
  have dinv': "dist_invar (dij_dist st')" and pinv': "parent_invar (dij_parent st')" using dinv pinv dd by simp+
  have upd: "dijkstra_upd_relax st = relax_edge u (dist_lookup (dij_dist st) u) (out_current (dij_graph st) u) st'"
    by (simp add: dijkstra_upd_relax_def cu st'_def)
  have parF: "\<And>x. parent_lookup (dij_parent (dijkstra_upd_relax st)) x = (if x = snd (out_current (dij_graph st) u) \<and> \<not> seen_isin (dij_seen st) (snd (out_current (dij_graph st) u)) \<and> allowed_edge (out_current (dij_graph st) u) \<and> (dist_lookup (dij_dist st) (snd (out_current (dij_graph st) u)) = -1 \<or> dist_lookup (dij_dist st) u + w (out_current (dij_graph st) u) < dist_lookup (dij_dist st) (snd (out_current (dij_graph st) u))) then Some (out_current (dij_graph st) u) else parent_lookup (dij_parent st) x)"
    unfolding upd by (subst relax_edge_parent_at[OF pinv' hV]) (auto simp: dd)
  have distF: "\<And>x. dist_lookup (dij_dist (dijkstra_upd_relax st)) x = (if x = snd (out_current (dij_graph st) u) \<and> \<not> seen_isin (dij_seen st) (snd (out_current (dij_graph st) u)) \<and> allowed_edge (out_current (dij_graph st) u) \<and> (dist_lookup (dij_dist st) (snd (out_current (dij_graph st) u)) = -1 \<or> dist_lookup (dij_dist st) u + w (out_current (dij_graph st) u) < dist_lookup (dij_dist st) (snd (out_current (dij_graph st) u))) then dist_lookup (dij_dist st) u + w (out_current (dij_graph st) u) else dist_lookup (dij_dist st) x)"
    unfolding upd by (subst relax_edge_dist_at[OF dinv' hV]) (auto simp: dd)
  show ?thesis
  proof (rule invar_root_intro)
    fix v assume r: "dist_lookup (dij_dist (dijkstra_upd_relax st)) v \<noteq> -1" and pn: "parent_lookup (dij_parent (dijkstra_upd_relax st)) v = None"
    have ncond: "\<not> (v = snd (out_current (dij_graph st) u) \<and> \<not> seen_isin (dij_seen st) (snd (out_current (dij_graph st) u)) \<and> allowed_edge (out_current (dij_graph st) u) \<and> (dist_lookup (dij_dist st) (snd (out_current (dij_graph st) u)) = -1 \<or> dist_lookup (dij_dist st) u + w (out_current (dij_graph st) u) < dist_lookup (dij_dist st) (snd (out_current (dij_graph st) u))))"
      using pn parF by (auto split: if_splits)
    have "parent_lookup (dij_parent st) v = None" using pn by (simp add: parF if_not_P[OF ncond])
    moreover have "dist_lookup (dij_dist st) v \<noteq> -1" using r by (simp add: distF if_not_P[OF ncond])
    ultimately show "v \<in> src_abstract srcs" using I by blast
  qed
qed

lemma invar_root_holds[invar_holds_intros]:
  assumes "dijkstra_dom st" "invar_1 st" "invar_2 st" "invar_3 st" "invar_4 st" "invar_6 st" "invar_root st"
  shows "invar_root (dijkstra st)"
  using assms(2-)
proof (induction rule: dijkstra_induct[OF assms(1)])
  case IH: (1 st)
  show ?case
    apply (rule dijkstra_cases[where st = st])
    by (auto intro!: IH(2-) intro: invar_holds_intros simp: dijkstra_simps[OF IH(1)])
qed

lemma invar_root_initial[invar_holds_intros]: "invar_root initial_state"
  by (auto simp: initial_state_def invar_root_def dist_init_inf)


subsubsection \<open>Reconstructing the shortest path from the parent-edge map\<close>

text \<open>The parent array @{term dij_parent} stores, for each reached vertex \<open>v\<close>, the \<^emph>\<open>edge\<close> \<open>e\<close> by which
      it was reached (so @{term "snd e = v"} and the tail @{term "fst e"} is its predecessor).
      Following these edges back to a source reconstructs the shortest path itself. @{term build_path}
      does this with an accumulator and is a genuine (tail-recursive, executable) function; it
      terminates because the parent relation @{term par_rel} is well-founded (the acyclicity invariant
      @{term invar_wf}).\<close>

partial_function (tailrec) build_path where
  "build_path st v acc = (case parent_lookup (dij_parent st) v of None \<Rightarrow> acc | Some e \<Rightarrow> build_path st (fst e) (e # acc))"

definition "reconstruct_path st v = build_path st v []"

lemma build_path_acc:
  assumes wf: "invar_wf st" and I3: "invar_3 st" and I9: "invar_9 st" and Itree: "invar_tree st" and Iroot: "invar_root st"
  shows "dist_lookup (dij_dist st) v \<noteq> -1 \<Longrightarrow>
     (\<exists>s p. build_path st v acc = p @ acc \<and> ag.path_bet p s v \<and> s \<in> src_abstract srcs \<and> weight w p = dist_lookup (dij_dist st) v \<and> parent_lookup (dij_parent st) s = None)"
proof -
  have wfst: "wf (par_rel st)" using wf by (simp add: invar_wf_def)
  have "dist_lookup (dij_dist st) v \<noteq> -1 \<longrightarrow> (\<exists>s p. build_path st v acc = p @ acc \<and> ag.path_bet p s v \<and> s \<in> src_abstract srcs \<and> weight w p = dist_lookup (dij_dist st) v \<and> parent_lookup (dij_parent st) s = None)"
  proof (induction v arbitrary: acc rule: wf_induct_rule[OF wfst])
    case IH: (1 v)
    show ?case
    proof (rule impI)
      assume rv: "dist_lookup (dij_dist st) v \<noteq> -1"
      show "\<exists>s p. build_path st v acc = p @ acc \<and> ag.path_bet p s v \<and> s \<in> src_abstract srcs \<and> weight w p = dist_lookup (dij_dist st) v \<and> parent_lookup (dij_parent st) s = None"
      proof (cases "parent_lookup (dij_parent st) v")
        case None
        have vS: "v \<in> src_abstract srcs" using rv None Iroot by (auto elim!: invar_root_props)
        have vnr: "v \<notin> src_remaining (dij_srcs st)" using rv I3 by (auto elim!: invar_3_props)
        have dv0: "dist_lookup (dij_dist st) v = 0" using vS vnr I9 by (auto elim!: invar_9_props)
        have "build_path st v acc = [] @ acc" using None by (simp add: build_path.simps)
        thus ?thesis using vS dv0 None by (auto intro!: exI[of _ v] exI[of _ "[]"])
      next
        case (Some e)
        note D = invar_tree_D[OF Itree Some]
        have edge: "(fst e, v) \<in> par_rel st" using Some by (auto simp: par_rel_def)
        have du: "dist_lookup (dij_dist st) (fst e) \<noteq> -1" using D by simp
        obtain s p where p: "build_path st (fst e) (e # acc) = p @ (e # acc)" "ag.path_bet p s (fst e)" "s \<in> src_abstract srcs" "weight w p = dist_lookup (dij_dist st) (fst e)" "parent_lookup (dij_parent st) s = None"
          using IH[OF edge] du by blast
        have bp: "build_path st v acc = (p @ [e]) @ acc" using Some p(1) by (simp add: build_path.simps)
        have pv: "ag.path_bet (p @ [e]) s v" using ag_path_bet_snocI[OF p(2)] D by auto
        have wv: "weight w (p @ [e]) = dist_lookup (dij_dist st) v" using p(4) D by (simp add: weight_snoc)
        show ?thesis using bp pv p(3) p(5) wv by blast
      qed
    qed
  qed
  thus "dist_lookup (dij_dist st) v \<noteq> -1 \<Longrightarrow> (\<exists>s p. build_path st v acc = p @ acc \<and> ag.path_bet p s v \<and> s \<in> src_abstract srcs \<and> weight w p = dist_lookup (dij_dist st) v \<and> parent_lookup (dij_parent st) s = None)" by blast
qed

lemma reconstruct_path_correct:
  assumes wf: "invar_wf st" and I3: "invar_3 st" and I9: "invar_9 st" and Itree: "invar_tree st" and Iroot: "invar_root st"
    and rv: "dist_lookup (dij_dist st) v \<noteq> -1"
  shows "\<exists>s. ag.path_bet (reconstruct_path st v) s v \<and> s \<in> src_abstract srcs \<and> weight w (reconstruct_path st v) = dist_lookup (dij_dist st) v"
proof -
  have "\<exists>s p. build_path st v [] = p @ [] \<and> ag.path_bet p s v \<and> s \<in> src_abstract srcs \<and> weight w p = dist_lookup (dij_dist st) v \<and> parent_lookup (dij_parent st) s = None"
    using build_path_acc[OF wf I3 I9 Itree Iroot rv] by blast
  thus ?thesis by (auto simp: reconstruct_path_def)
qed

lemma invar_3_compute: "invar_3 dijkstra_compute" unfolding dijkstra_compute_def by (rule invar_3_holds[OF initial_state_props(5) initial_state_props(1) initial_state_props(2) initial_state_props(3) initial_state_props(4)])
lemma invar_tree_compute: "invar_tree dijkstra_compute" unfolding dijkstra_compute_def by (rule invar_tree_holds[OF initial_state_props(5) initial_state_props(1) initial_state_props(2) initial_state_props(3) initial_state_props(4) invar_tree_initial])
lemma invar_wf_compute: "invar_wf dijkstra_compute" unfolding dijkstra_compute_def by (rule invar_wf_holds[OF initial_state_props(5) initial_state_props(1) initial_state_props(2) initial_state_props(3) initial_state_props(4) invar_tree_initial invar_wf_initial])
lemma invar_root_compute: "invar_root dijkstra_compute" unfolding dijkstra_compute_def by (rule invar_root_holds[OF initial_state_props(5) initial_state_props(1) initial_state_props(2) initial_state_props(3) initial_state_props(4) invar_6_initial invar_root_initial])

text \<open>The parent-edge relation of the computed result is well-founded, and @{const reconstruct_path}
      -- a tail-recursive, executable function -- reads off from the parent-edge map, for every
      reached vertex, a concrete source-to-\<open>v\<close> path of weight @{term "dist_lookup (dij_dist
      dijkstra_compute) v"}; by @{thm dijkstra_compute_optimal} this is a genuine shortest path once
      \<open>v\<close> is settled.\<close>

theorem dijkstra_compute_parent_wf: "wf (par_rel dijkstra_compute)"
  using invar_wf_compute by (simp add: invar_wf_def)

theorem dijkstra_compute_path:
  assumes "dist_lookup (dij_dist dijkstra_compute) v \<noteq> -1"
  shows "\<exists>s. ag.path_bet (reconstruct_path dijkstra_compute v) s v \<and> s \<in> src_abstract srcs \<and> weight w (reconstruct_path dijkstra_compute v) = dist_lookup (dij_dist dijkstra_compute) v"
  using reconstruct_path_correct[OF invar_wf_compute invar_3_compute invar_9_compute invar_tree_compute invar_root_compute assms] .


subsection \<open>Executable version\<close>

partial_function (tailrec) dijkstra_impl where "dijkstra_impl st = (case dij_curr st of Some u \<Rightarrow> (if out_has (dij_graph st) u then dijkstra_impl (relax_edge u (dist_lookup (dij_dist st) u) (out_current (dij_graph st) u) (st \<lparr> dij_graph := out_move (dij_graph st) u \<rparr>)) else dijkstra_impl (st \<lparr> dij_curr := None \<rparr>)) | None \<Rightarrow> (if src_has (dij_srcs st) then dijkstra_impl (insert_source (src_current (dij_srcs st)) (st \<lparr> dij_srcs := src_move (dij_srcs st) \<rparr>)) else (case queue_extract_min (dij_heap st) of (h, None) \<Rightarrow> st \<lparr> dij_heap := h \<rparr> | (h, Some u) \<Rightarrow> (if seen_isin (dij_seen st) u then dijkstra_impl (st \<lparr> dij_heap := h \<rparr>) else if early_stop \<and> target u then st \<lparr> dij_heap := h, dij_seen := seen_insert u (dij_seen st), dij_target := Some u \<rparr> else dijkstra_impl (st \<lparr> dij_heap := h, dij_seen := seen_insert u (dij_seen st), dij_curr := Some u, dij_graph := out_reset (dij_graph st) u \<rparr>)))))"

lemma dijkstra_impl_same:
  assumes "dijkstra_dom st"
  shows "dijkstra_impl st = dijkstra st"
proof(induction rule: dijkstra.pinduct[OF assms])
  case (1 st)
  show ?case
    apply(subst dijkstra_impl.simps)
    apply(subst dijkstra.psimps[OF "1"(1)])
    using "1"(2-)
    by(auto split: option.splits prod.splits)
qed

thm dijkstra_compute_upper_bound
thm dijkstra_compute_optimal
thm dijkstra_compute_complete
thm dijkstra_compute_path

lemmas [code] = dijkstra_impl.simps initial_state_def

end

end