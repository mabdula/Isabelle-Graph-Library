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
  "\<lbrakk>dijkstra_call_relax_conds st;
   \<And>u. \<lbrakk>dij_curr st = Some u; out_has (dij_graph st) u\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: dijkstra_call_relax_conds_def split: option.splits)

lemma dijkstra_call_finish_condsE[call_cond_elims]:
  "\<lbrakk>dijkstra_call_finish_conds st;
   \<And>u. \<lbrakk>dij_curr st = Some u; \<not> out_has (dij_graph st) u\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: dijkstra_call_finish_conds_def split: option.splits)

lemma dijkstra_call_init_condsE[call_cond_elims]:
  "\<lbrakk>dijkstra_call_init_conds st;
   \<lbrakk>dij_curr st = None; src_has (dij_srcs st)\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: dijkstra_call_init_conds_def split: option.splits)

lemma dijkstra_call_skip_condsE[call_cond_elims]:
  "\<lbrakk>dijkstra_call_skip_conds st;
   \<And>h2 u. \<lbrakk>dij_curr st = None; \<not> src_has (dij_srcs st);
             queue_extract_min (dij_heap st) = (h2, Some u); seen_isin (dij_seen st) u\<rbrakk> \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by (auto simp: dijkstra_call_skip_conds_def split: option.splits prod.splits)

lemma dijkstra_call_settle_condsE[call_cond_elims]:
  "\<lbrakk>dijkstra_call_settle_conds st;
   \<And>h2 u. \<lbrakk>dij_curr st = None; \<not> src_has (dij_srcs st);
             queue_extract_min (dij_heap st) = (h2, Some u); \<not> seen_isin (dij_seen st) u;
             \<not> (early_stop \<and> target u)\<rbrakk> \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by (auto simp: dijkstra_call_settle_conds_def split: option.splits prod.splits)

lemma dijkstra_ret_done_condsE[call_cond_elims]:
  "\<lbrakk>dijkstra_ret_done_conds st;
   \<And>h2. \<lbrakk>dij_curr st = None; \<not> src_has (dij_srcs st);
           queue_extract_min (dij_heap st) = (h2, None)\<rbrakk> \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by (auto simp: dijkstra_ret_done_conds_def split: option.splits prod.splits)

lemma dijkstra_ret_found_condsE[call_cond_elims]:
  "\<lbrakk>dijkstra_ret_found_conds st;
   \<And>h2 u. \<lbrakk>dij_curr st = None; \<not> src_has (dij_srcs st);
             queue_extract_min (dij_heap st) = (h2, Some u); \<not> seen_isin (dij_seen st) u;
             early_stop; target u\<rbrakk> \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
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
proof-
  have "dijkstra_call_relax_conds st \<or> dijkstra_call_finish_conds st \<or> dijkstra_call_init_conds st \<or>
        dijkstra_call_skip_conds st \<or> dijkstra_call_settle_conds st \<or> dijkstra_ret_done_conds st \<or>
        dijkstra_ret_found_conds st"
    by (auto simp: dijkstra_call_relax_conds_def dijkstra_call_finish_conds_def
                   dijkstra_call_init_conds_def dijkstra_call_skip_conds_def
                   dijkstra_call_settle_conds_def dijkstra_ret_done_conds_def
                   dijkstra_ret_found_conds_def
             split: option.split_asm prod.split_asm option.split prod.split)
  then show ?thesis
    using assms
    by auto
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
    and "\<And>st. \<lbrakk>dijkstra_dom st;
                dijkstra_call_relax_conds st \<Longrightarrow> P (dijkstra_upd_relax st);
                dijkstra_call_finish_conds st \<Longrightarrow> P (dijkstra_upd_finish st);
                dijkstra_call_init_conds st \<Longrightarrow> P (dijkstra_upd_init st);
                dijkstra_call_skip_conds st \<Longrightarrow> P (dijkstra_upd_skip st);
                dijkstra_call_settle_conds st \<Longrightarrow> P (dijkstra_upd_settle st)\<rbrakk> \<Longrightarrow> P st"
  shows "P st"
  apply(rule dijkstra.pinduct[OF assms(1)])
  apply(rule assms(2)[simplified dijkstra_call_relax_conds_def dijkstra_upd_relax_def
                        dijkstra_call_finish_conds_def dijkstra_upd_finish_def
                        dijkstra_call_init_conds_def dijkstra_upd_init_def
                        dijkstra_call_skip_conds_def dijkstra_upd_skip_def
                        dijkstra_call_settle_conds_def dijkstra_upd_settle_def])
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

lemma out_has_remaining: "\<lbrakk>out_invar g; u \<in> \<V>; out_has g u\<rbrakk> \<Longrightarrow> out_remaining g u \<noteq> {}"
  using outg.idx_has
  by auto

lemma out_graph_inv_move: "\<lbrakk>out_graph_inv g; u \<in> \<V>; out_has g u\<rbrakk> \<Longrightarrow> out_graph_inv (out_move g u)"
  using outg.idx_move_invar outg.idx_move_abstract out_has_remaining
  by (auto simp: out_graph_inv_def)

lemma out_graph_inv_reset: "\<lbrakk>out_graph_inv g; u \<in> \<V>\<rbrakk> \<Longrightarrow> out_graph_inv (out_reset g u)"
  using outg.idx_reset_invar outg.idx_reset_abstract
  by (auto simp: out_graph_inv_def)

lemma out_remaining_sub_abstract: "\<lbrakk>out_invar g; u \<in> \<V>\<rbrakk> \<Longrightarrow> out_remaining g u \<subseteq> out_abstract g u"
  using outg.idx_partition_union
  by blast

lemma out_current_in_delta: "\<lbrakk>out_graph_inv g; u \<in> \<V>; out_has g u\<rbrakk> \<Longrightarrow> out_current g u \<in> \<delta>\<^sup>+ u"
  using outg.idx_current[of g u] out_has_remaining[of g u] out_remaining_sub_abstract[of g u]
  by (auto simp: out_graph_inv_def)

lemma out_current_edge: "\<lbrakk>out_graph_inv g; u \<in> \<V>; out_has g u\<rbrakk> \<Longrightarrow> out_current g u \<in> \<E>"
  and out_current_fst: "\<lbrakk>out_graph_inv g; u \<in> \<V>; out_has g u\<rbrakk> \<Longrightarrow> fst (out_current g u) = u"
  using out_current_in_delta
  by (auto simp: delta_plus_def)

lemma finite_out_remaining: "\<lbrakk>out_graph_inv g; u \<in> \<V>\<rbrakk> \<Longrightarrow> finite (out_remaining g u)"
  using out_remaining_sub_abstract[of g u] delta_plus_finite[of u]
  by (auto simp: out_graph_inv_def intro: finite_subset)

text \<open>The single-edge operations touch only the distance, parent and heap; the other fields are
      untouched, and they preserve the array invariants.\<close>

lemma relax_edge_seen[simp]: "dij_seen (relax_edge u du e st) = dij_seen st"
  and relax_edge_graph[simp]: "dij_graph (relax_edge u du e st) = dij_graph st"
  and relax_edge_curr[simp]: "dij_curr (relax_edge u du e st) = dij_curr st"
  and relax_edge_srcs[simp]: "dij_srcs (relax_edge u du e st) = dij_srcs st"
  and relax_edge_target[simp]: "dij_target (relax_edge u du e st) = dij_target st"
  by (auto simp: relax_edge_def Let_def)

lemma relax_edge_dist_invar[simp]:
  "\<lbrakk>dist_invar (dij_dist st); snd e \<in> \<V>\<rbrakk> \<Longrightarrow> dist_invar (dij_dist (relax_edge u du e st))"
  and relax_edge_parent_invar[simp]:
  "\<lbrakk>parent_invar (dij_parent st); snd e \<in> \<V>\<rbrakk> \<Longrightarrow> parent_invar (dij_parent (relax_edge u du e st))"
  by (auto simp: relax_edge_def Let_def
           intro: dist_arr.fixed_univ_map_upd_invar parent_arr.fixed_univ_map_upd_invar)

lemma insert_source_seen[simp]: "dij_seen (insert_source v st) = dij_seen st"
  and insert_source_graph[simp]: "dij_graph (insert_source v st) = dij_graph st"
  and insert_source_parent[simp]: "dij_parent (insert_source v st) = dij_parent st"
  and insert_source_curr[simp]: "dij_curr (insert_source v st) = dij_curr st"
  and insert_source_target[simp]: "dij_target (insert_source v st) = dij_target st"
  and insert_source_srcs[simp]: "dij_srcs (insert_source v st) = dij_srcs st"
  and insert_source_dist_invar[simp]:
    "\<lbrakk>dist_invar (dij_dist st); v \<in> \<V>\<rbrakk> \<Longrightarrow> dist_invar (dij_dist (insert_source v st))"
  by (auto simp: insert_source_def intro: dist_arr.fixed_univ_map_upd_invar)


subsection \<open>Well-formedness invariant\<close>

text \<open>The abstract-datatype invariants of the distance / parent arrays, the graph collection and the
      source iterator are maintained throughout. (The settled-set invariant is coupled with the queue
      contents and is treated separately, since -- the seen set being fixed-universe -- its
      preservation needs that a popped vertex is a graph vertex.)\<close>

definition "invar_1 st \<longleftrightarrow> dist_invar (dij_dist st) \<and> parent_invar (dij_parent st) \<and>
  out_graph_inv (dij_graph st) \<and> src_invar (dij_srcs st)"

lemma invar_1_props[invar_props_elims]:
  "\<lbrakk>invar_1 st;
   \<lbrakk>dist_invar (dij_dist st); parent_invar (dij_parent st); out_graph_inv (dij_graph st);
     src_invar (dij_srcs st)\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: invar_1_def)

lemma invar_1_intro[invar_props_intros]:
  "\<lbrakk>dist_invar (dij_dist st); parent_invar (dij_parent st); out_graph_inv (dij_graph st);
    src_invar (dij_srcs st)\<rbrakk> \<Longrightarrow> invar_1 st"
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

lemma invar_2_props[invar_props_elims]:
  "\<lbrakk>invar_2 st;
   \<lbrakk>queue_invar (dij_heap st); seen_invar (dij_seen st); seen_abstract (dij_seen st) \<subseteq> \<V>;
     \<forall>x. dist_lookup (dij_dist st) x \<noteq> -1 \<longrightarrow> x \<in> \<V>; \<forall>u. dij_curr st = Some u \<longrightarrow> u \<in> \<V>;
     \<forall>x k. ((x,k) \<in> queue_abstract (dij_heap st)) =
       (x \<notin> seen_abstract (dij_seen st) \<and> dist_lookup (dij_dist st) x \<noteq> -1 \<and> k = dist_lookup (dij_dist st) x)\<rbrakk>
    \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: invar_2_def)

lemma invar_2_intro[invar_props_intros]:
  "\<lbrakk>queue_invar (dij_heap st); seen_invar (dij_seen st); seen_abstract (dij_seen st) \<subseteq> \<V>;
    \<forall>x. dist_lookup (dij_dist st) x \<noteq> -1 \<longrightarrow> x \<in> \<V>; \<forall>u. dij_curr st = Some u \<longrightarrow> u \<in> \<V>;
    \<forall>x k. ((x,k) \<in> queue_abstract (dij_heap st)) =
      (x \<notin> seen_abstract (dij_seen st) \<and> dist_lookup (dij_dist st) x \<noteq> -1 \<and> k = dist_lookup (dij_dist st) x)\<rbrakk>
   \<Longrightarrow> invar_2 st"
  by (auto simp: invar_2_def)


subsection \<open>Setup for automation\<close>

text \<open>The invariant proofs use the data-structure specifications as rewrite rules, and read the
      data-structure invariants off @{term invar_1} and @{term invar_2}. These rules are switched on
      only for the proofs below (by \<open>context notes\<close>), not in the locale.\<close>

lemma invar_1_ds:
  "invar_1 st \<Longrightarrow> dist_invar (dij_dist st)" "invar_1 st \<Longrightarrow> parent_invar (dij_parent st)"
  "invar_1 st \<Longrightarrow> out_graph_inv (dij_graph st)" "invar_1 st \<Longrightarrow> out_invar (dij_graph st)"
  "invar_1 st \<Longrightarrow> src_invar (dij_srcs st)"
  by (auto simp: invar_1_def out_graph_inv_def)

lemma invar_2_ds:
  "invar_2 st \<Longrightarrow> queue_invar (dij_heap st)" "invar_2 st \<Longrightarrow> seen_invar (dij_seen st)"
  "invar_2 st \<Longrightarrow> (x, k) \<in> queue_abstract (dij_heap st) \<longleftrightarrow>
     x \<notin> seen_abstract (dij_seen st) \<and> dist_lookup (dij_dist st) x \<noteq> -1 \<and> k = dist_lookup (dij_dist st) x"
  by (auto elim!: invar_2_props)

lemma invar_2_in_V:
  "\<lbrakk>invar_2 st; x \<in> seen_abstract (dij_seen st)\<rbrakk> \<Longrightarrow> x \<in> \<V>"
  "\<lbrakk>invar_2 st; dist_lookup (dij_dist st) x \<noteq> -1\<rbrakk> \<Longrightarrow> x \<in> \<V>"
  "\<lbrakk>invar_2 st; dij_curr st = Some u\<rbrakk> \<Longrightarrow> u \<in> \<V>"
  by (auto elim!: invar_2_props)

lemma out_reset_cursor:
  "\<lbrakk>out_invar g; u \<in> \<V>\<rbrakk> \<Longrightarrow> out_iterated (out_reset g u) x = (if x = u then {} else out_iterated g x)"
  "\<lbrakk>out_invar g; u \<in> \<V>\<rbrakk> \<Longrightarrow>
     out_remaining (out_reset g u) x = (if x = u then out_abstract g u else out_remaining g x)"
  by (simp_all add: outg.idx_reset_iterated outg.idx_reset_iterated_other outg.idx_reset_remaining
                    outg.idx_reset_remaining_other)

lemmas dijkstra_ds_simps =
  invar_1_ds invar_2_ds out_reset_cursor
  seen_set.fixed_univ_set_empty seen_set.fixed_univ_set_insert seen_set.fixed_univ_set_isin
  dist_arr.fixed_univ_map_upd dist_arr.fixed_univ_map_upd_invar
  parent_arr.fixed_univ_map_upd parent_arr.fixed_univ_map_upd_invar
  sources.has_current outg.idx_has outg.idx_move_invar outg.idx_reset_invar outg.idx_reset_abstract

context
  notes dijkstra_ds_simps[simp]
begin

text \<open>A vertex popped from the queue is reached, unsettled, a graph vertex, and has the least key;
      the remaining queue is the old one without it. On the \<open>relax\<close> branch, the current edge is
      an outgoing edge of the scanned vertex, and its head is a graph vertex.\<close>

lemma popped_vertex:
  assumes "queue_extract_min (dij_heap st) = (h2, Some u)" "invar_2 st"
  shows "u \<in> \<V> \<and> u \<notin> seen_abstract (dij_seen st) \<and> dist_lookup (dij_dist st) u \<noteq> -1 \<and> queue_invar h2 \<and>
     queue_abstract h2 = queue_abstract (dij_heap st) - {(u, dist_lookup (dij_dist st) u)} \<and>
     (\<forall>x. x \<notin> seen_abstract (dij_seen st) \<longrightarrow> dist_lookup (dij_dist st) x \<noteq> -1 \<longrightarrow>
        dist_lookup (dij_dist st) u \<le> dist_lookup (dij_dist st) x)"
proof-
  obtain k where "(u, k) \<in> queue_abstract (dij_heap st)"
    "\<forall>x' k'. (x', k') \<in> queue_abstract (dij_heap st) \<longrightarrow> k \<le> k'"
    using assms heap.queue_extract_min(2)[of "dij_heap st" u]
    by auto
  thus ?thesis
    using assms heap.queue_extract_min(1,4)[where H = "dij_heap st"] invar_2_in_V(2)
    by auto
qed

lemma relax_edge_facts:
  assumes "dijkstra_call_relax_conds st" "invar_1 st" "invar_2 st"
  obtains u where "dij_curr st = Some u" "u \<in> \<V>" "out_remaining (dij_graph st) u \<noteq> {}"
    "out_current (dij_graph st) u \<in> out_remaining (dij_graph st) u" "out_current (dij_graph st) u \<in> \<E>"
    "fst (out_current (dij_graph st) u) = u" "snd (out_current (dij_graph st) u) \<in> \<V>"
    "0 \<le> w (out_current (dij_graph st) u)" "out_graph_inv (out_move (dij_graph st) u)"
    "\<forall>v. out_remaining (out_move (dij_graph st) u) v =
       (if v = u then out_remaining (dij_graph st) u - {out_current (dij_graph st) u} else out_remaining (dij_graph st) v)"
    "\<forall>v. out_iterated (out_move (dij_graph st) u) v =
       (if v = u then insert (out_current (dij_graph st) u) (out_iterated (dij_graph st) u) else out_iterated (dij_graph st) v)"
proof-
  obtain u where u: "dij_curr st = Some u" "out_has (dij_graph st) u"
    using assms(1)
    by (auto elim: dijkstra_call_relax_condsE)
  moreover have "u \<in> \<V>"
    using assms(3) u(1)
    by (rule invar_2_in_V(3))
  ultimately show thesis
    using that invar_1_ds[OF assms(2)] out_current_edge[of "dij_graph st" u]
          out_current_fst[of "dij_graph st" u] snd_E_V outg.idx_current[of "dij_graph st" u] w_nonneg
          out_graph_inv_move[of "dij_graph st" u] outg.idx_move_remaining[of "dij_graph st" u]
          outg.idx_move_iterated[of "dij_graph st" u] outg.idx_move_remaining_other[of "dij_graph st" u]
          outg.idx_move_iterated_other[of "dij_graph st" u]
    by auto
qed

lemma skip_contra: "\<lbrakk>dijkstra_call_skip_conds st; invar_2 st\<rbrakk> \<Longrightarrow> False"
  by (auto elim!: dijkstra_call_skip_condsE dest: popped_vertex)

lemma invar_2_holds_finish[invar_holds_intros]:
  "\<lbrakk>dijkstra_call_finish_conds st; invar_2 st\<rbrakk> \<Longrightarrow> invar_2 (dijkstra_upd_finish st)"
  unfolding dijkstra_upd_finish_def invar_2_def
  by simp

lemma invar_2_holds_done[invar_holds_intros]:
  "\<lbrakk>dijkstra_ret_done_conds st; invar_2 st\<rbrakk> \<Longrightarrow> invar_2 (dijkstra_ret_done st)"
  by (erule dijkstra_ret_done_condsE)
     (use heap.queue_extract_min(1,3,5)[where H = "dij_heap st"] in
       \<open>auto simp: dijkstra_ret_done_def elim!: invar_2_props intro!: invar_2_intro\<close>)

lemma invar_2_holds_skip[invar_holds_intros]:
  "\<lbrakk>dijkstra_call_skip_conds st; invar_2 st\<rbrakk> \<Longrightarrow> invar_2 (dijkstra_upd_skip st)"
  by (auto dest: skip_contra)

text \<open>Settling a popped vertex: it is removed from the queue and added to the settled set.\<close>

lemma invar_2_holds_settle[invar_holds_intros]:
  "\<lbrakk>dijkstra_call_settle_conds st; invar_2 st\<rbrakk> \<Longrightarrow> invar_2 (dijkstra_upd_settle st)"
  by (erule dijkstra_call_settle_condsE, frule popped_vertex)
     (auto simp: dijkstra_upd_settle_def elim!: invar_2_props intro!: invar_2_intro)

lemma invar_2_holds_found[invar_holds_intros]:
  "\<lbrakk>dijkstra_ret_found_conds st; invar_2 st\<rbrakk> \<Longrightarrow> invar_2 (dijkstra_ret_found st)"
  by (erule dijkstra_ret_found_condsE, frule popped_vertex)
     (auto simp: dijkstra_ret_found_def elim!: invar_2_props intro!: invar_2_intro)

text \<open>Closed forms for the fields after the \<open>relax\<close> branch.\<close>

lemma relax_edge_dist_at:
  assumes "dist_invar (dij_dist st)" "snd e \<in> \<V>"
  shows "dist_lookup (dij_dist (relax_edge u du e st)) x =
    (if x = snd e \<and> \<not> seen_isin (dij_seen st) (snd e) \<and> allowed_edge e \<and>
        (dist_lookup (dij_dist st) (snd e) = -1 \<or> du + w e < dist_lookup (dij_dist st) (snd e))
     then du + w e else dist_lookup (dij_dist st) x)"
  using assms
  by (auto simp: relax_edge_def Let_def)

lemma relax_edge_parent_at:
  assumes "parent_invar (dij_parent st)" "snd e \<in> \<V>"
  shows "parent_lookup (dij_parent (relax_edge u du e st)) x =
    (if x = snd e \<and> \<not> seen_isin (dij_seen st) (snd e) \<and> allowed_edge e \<and>
        (dist_lookup (dij_dist st) (snd e) = -1 \<or> du + w e < dist_lookup (dij_dist st) (snd e))
     then Some e else parent_lookup (dij_parent st) x)"
  using assms
  by (auto simp: relax_edge_def Let_def)

lemma dijkstra_upd_relax_fields[simp]:
  "dij_seen (dijkstra_upd_relax st) = dij_seen st"
  "dij_graph (dijkstra_upd_relax st) = out_move (dij_graph st) (the (dij_curr st))"
  "dij_curr (dijkstra_upd_relax st) = dij_curr st"
  "dij_srcs (dijkstra_upd_relax st) = dij_srcs st"
  "dij_target (dijkstra_upd_relax st) = dij_target st"
  by (simp_all add: dijkstra_upd_relax_def Let_def)

lemma dijkstra_upd_relax_dist:
  "\<lbrakk>dij_curr st = Some u; invar_1 st; snd (out_current (dij_graph st) u) \<in> \<V>\<rbrakk> \<Longrightarrow>
   dist_lookup (dij_dist (dijkstra_upd_relax st)) x =
     (if x = snd (out_current (dij_graph st) u) \<and> \<not> seen_isin (dij_seen st) (snd (out_current (dij_graph st) u)) \<and>
         allowed_edge (out_current (dij_graph st) u) \<and>
         (dist_lookup (dij_dist st) (snd (out_current (dij_graph st) u)) = -1 \<or>
          dist_lookup (dij_dist st) u + w (out_current (dij_graph st) u) <
            dist_lookup (dij_dist st) (snd (out_current (dij_graph st) u)))
      then dist_lookup (dij_dist st) u + w (out_current (dij_graph st) u) else dist_lookup (dij_dist st) x)"
  by (auto simp: dijkstra_upd_relax_def Let_def relax_edge_dist_at simp del: seen_set.fixed_univ_set_isin)

lemma dijkstra_upd_relax_parent:
  "\<lbrakk>dij_curr st = Some u; invar_1 st; snd (out_current (dij_graph st) u) \<in> \<V>\<rbrakk> \<Longrightarrow>
   parent_lookup (dij_parent (dijkstra_upd_relax st)) x =
     (if x = snd (out_current (dij_graph st) u) \<and> \<not> seen_isin (dij_seen st) (snd (out_current (dij_graph st) u)) \<and>
         allowed_edge (out_current (dij_graph st) u) \<and>
         (dist_lookup (dij_dist st) (snd (out_current (dij_graph st) u)) = -1 \<or>
          dist_lookup (dij_dist st) u + w (out_current (dij_graph st) u) <
            dist_lookup (dij_dist st) (snd (out_current (dij_graph st) u)))
      then Some (out_current (dij_graph st) u) else parent_lookup (dij_parent st) x)"
  by (auto simp: dijkstra_upd_relax_def Let_def relax_edge_parent_at simp del: seen_set.fixed_univ_set_isin)


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

lemma invar_3_props[invar_props_elims]:
  "\<lbrakk>invar_3 st;
   \<lbrakk>src_abstract (dij_srcs st) \<subseteq> \<V>; \<forall>v. v \<in> src_remaining (dij_srcs st) \<longrightarrow> dist_lookup (dij_dist st) v = -1;
     \<forall>u. dij_curr st = Some u \<longrightarrow> src_remaining (dij_srcs st) = {};
     \<forall>x. dist_lookup (dij_dist st) x \<noteq> -1 \<longrightarrow> 0 \<le> dist_lookup (dij_dist st) x;
     \<forall>u. dij_curr st = Some u \<longrightarrow> dist_lookup (dij_dist st) u \<noteq> -1;
     \<forall>u. dij_curr st = Some u \<longrightarrow> u \<in> seen_abstract (dij_seen st)\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: invar_3_def)

lemma invar_3_intro[invar_props_intros]:
  "\<lbrakk>src_abstract (dij_srcs st) \<subseteq> \<V>; \<forall>v. v \<in> src_remaining (dij_srcs st) \<longrightarrow> dist_lookup (dij_dist st) v = -1;
    \<forall>u. dij_curr st = Some u \<longrightarrow> src_remaining (dij_srcs st) = {};
    \<forall>x. dist_lookup (dij_dist st) x \<noteq> -1 \<longrightarrow> 0 \<le> dist_lookup (dij_dist st) x;
    \<forall>u. dij_curr st = Some u \<longrightarrow> dist_lookup (dij_dist st) u \<noteq> -1;
    \<forall>u. dij_curr st = Some u \<longrightarrow> u \<in> seen_abstract (dij_seen st)\<rbrakk> \<Longrightarrow> invar_3 st"
  by (auto simp: invar_3_def)

text \<open>On the \<open>init\<close> branch, the loaded source is a remaining source and a graph vertex.\<close>

lemma init_branch_facts:
  assumes "dijkstra_call_init_conds st" "invar_1 st" "invar_3 st"
  obtains "dij_curr st = None" "src_remaining (dij_srcs st) \<noteq> {}"
    "src_current (dij_srcs st) \<in> src_remaining (dij_srcs st)"
    "src_current (dij_srcs st) \<in> src_abstract (dij_srcs st)" "src_current (dij_srcs st) \<in> \<V>"
    "finite (src_remaining (dij_srcs st))" "src_invar (src_move (dij_srcs st))"
    "src_abstract (src_move (dij_srcs st)) = src_abstract (dij_srcs st)"
    "src_remaining (src_move (dij_srcs st)) = src_remaining (dij_srcs st) - {src_current (dij_srcs st)}"
proof-
  have "src_current (dij_srcs st) \<in> src_remaining (dij_srcs st)"
    "src_remaining (dij_srcs st) \<subseteq> src_abstract (dij_srcs st)" "src_abstract (dij_srcs st) \<subseteq> \<V>"
    using assms sources.current_element[of "dij_srcs st"] sources.iterable_set_abstract(2)[of "dij_srcs st"]
    by (auto elim!: dijkstra_call_init_condsE invar_3_props)
  moreover have "src_current (dij_srcs st) \<in> src_abstract (dij_srcs st)" "src_current (dij_srcs st) \<in> \<V>"
    "finite (src_remaining (dij_srcs st))"
    using calculation finite_subset[OF _ \<V>_finite]
    by blast+
  ultimately show thesis
    using that assms sources.move_on[of "dij_srcs st"] sources.move_on_invar[of "dij_srcs st"]
    by (auto elim!: dijkstra_call_init_condsE)
qed

lemma invar_3_holds_finish[invar_holds_intros]:
  "\<lbrakk>dijkstra_call_finish_conds st; invar_3 st\<rbrakk> \<Longrightarrow> invar_3 (dijkstra_upd_finish st)"
  by (auto simp: dijkstra_upd_finish_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_3_holds_done[invar_holds_intros]:
  "\<lbrakk>dijkstra_ret_done_conds st; invar_3 st\<rbrakk> \<Longrightarrow> invar_3 (dijkstra_ret_done st)"
  by (simp add: dijkstra_ret_done_def invar_3_def)

lemma invar_3_holds_found[invar_holds_intros]:
  "\<lbrakk>dijkstra_ret_found_conds st; invar_3 st\<rbrakk> \<Longrightarrow> invar_3 (dijkstra_ret_found st)"
  by (auto simp: dijkstra_ret_found_def elim!: dijkstra_ret_found_condsE invar_3_props intro!: invar_3_intro)

lemma invar_3_holds_skip[invar_holds_intros]:
  "\<lbrakk>dijkstra_call_skip_conds st; invar_2 st; invar_3 st\<rbrakk> \<Longrightarrow> invar_3 (dijkstra_upd_skip st)"
  by (auto dest: skip_contra)

lemma invar_3_holds_settle[invar_holds_intros]:
  "\<lbrakk>dijkstra_call_settle_conds st; invar_1 st; invar_2 st; invar_3 st\<rbrakk> \<Longrightarrow> invar_3 (dijkstra_upd_settle st)"
  by (erule dijkstra_call_settle_condsE, frule popped_vertex)
     (auto simp: dijkstra_upd_settle_def elim!: invar_3_props intro!: invar_3_intro)

lemma invar_3_holds_init[invar_holds_intros]:
  "\<lbrakk>dijkstra_call_init_conds st; invar_1 st; invar_3 st\<rbrakk> \<Longrightarrow> invar_3 (dijkstra_upd_init st)"
  by (erule init_branch_facts)
     (auto simp: dijkstra_upd_init_def insert_source_def elim!: invar_3_props intro!: invar_3_intro)

lemma invar_3_holds_relax[invar_holds_intros]:
  "\<lbrakk>dijkstra_call_relax_conds st; invar_1 st; invar_2 st; invar_3 st\<rbrakk> \<Longrightarrow> invar_3 (dijkstra_upd_relax st)"
  by (erule relax_edge_facts)
     (auto simp: dijkstra_upd_relax_dist elim!: invar_3_props intro!: invar_3_intro split: if_splits)


subsection \<open>Auxiliary: sources unloaded implies nothing settled\<close>

definition "invar_4 st \<longleftrightarrow> (src_remaining (dij_srcs st) \<noteq> {} \<longrightarrow> seen_abstract (dij_seen st) = {})"

lemma invar_4_props[invar_props_elims]:
  "\<lbrakk>invar_4 st; \<lbrakk>src_remaining (dij_srcs st) \<noteq> {} \<longrightarrow> seen_abstract (dij_seen st) = {}\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: invar_4_def)

lemma invar_4_intro[invar_props_intros]:
  "(src_remaining (dij_srcs st) \<noteq> {} \<longrightarrow> seen_abstract (dij_seen st) = {}) \<Longrightarrow> invar_4 st"
  by (auto simp: invar_4_def)

lemma invar_4_holds_finish[invar_holds_intros]:
  "\<lbrakk>dijkstra_call_finish_conds st; invar_4 st\<rbrakk> \<Longrightarrow> invar_4 (dijkstra_upd_finish st)"
  by (auto simp: dijkstra_upd_finish_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_4_holds_done[invar_holds_intros]:
  "\<lbrakk>dijkstra_ret_done_conds st; invar_4 st\<rbrakk> \<Longrightarrow> invar_4 (dijkstra_ret_done st)"
  by (simp add: dijkstra_ret_done_def invar_4_def)

lemma invar_4_holds_relax[invar_holds_intros]:
  "\<lbrakk>dijkstra_call_relax_conds st; invar_4 st\<rbrakk> \<Longrightarrow> invar_4 (dijkstra_upd_relax st)"
  by (auto elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_4_holds_init[invar_holds_intros]:
  "\<lbrakk>dijkstra_call_init_conds st; invar_1 st; invar_4 st\<rbrakk> \<Longrightarrow> invar_4 (dijkstra_upd_init st)"
  by (auto simp: dijkstra_upd_init_def elim!: dijkstra_call_init_condsE invar_props_elims intro!: invar_props_intros)

lemma invar_4_holds_settle[invar_holds_intros]:
  "\<lbrakk>dijkstra_call_settle_conds st; invar_1 st; invar_4 st\<rbrakk> \<Longrightarrow> invar_4 (dijkstra_upd_settle st)"
  by (auto simp: dijkstra_upd_settle_def elim!: dijkstra_call_settle_condsE invar_props_elims
           intro!: invar_props_intros)

lemma invar_4_holds_found[invar_holds_intros]:
  "\<lbrakk>dijkstra_ret_found_conds st; invar_1 st; invar_4 st\<rbrakk> \<Longrightarrow> invar_4 (dijkstra_ret_found st)"
  by (auto simp: dijkstra_ret_found_def elim!: dijkstra_ret_found_condsE invar_props_elims
           intro!: invar_props_intros)

lemma invar_4_holds_skip[invar_holds_intros]:
  "\<lbrakk>dijkstra_call_skip_conds st; invar_2 st; invar_4 st\<rbrakk> \<Longrightarrow> invar_4 (dijkstra_upd_skip st)"
  by (auto dest: skip_contra)


subsection \<open>The coupling invariant on the source-loading and relaxation branches\<close>

lemma invar_2_holds_init[invar_holds_intros]:
  assumes "dijkstra_call_init_conds st" "invar_1 st" "invar_2 st" "invar_3 st" "invar_4 st"
  shows "invar_2 (dijkstra_upd_init st)"
proof(rule init_branch_facts[OF assms(1,2,4)], goal_cases)
  case 1
  hence "dist_lookup (dij_dist st) (src_current (dij_srcs st)) = -1" "seen_abstract (dij_seen st) = {}"
    using assms(4,5)
    by (auto elim!: invar_3_props invar_4_props)
  thus ?case
    using 1 invar_1_ds[OF assms(2)] assms(3)[unfolded invar_2_def]
          heap.queue_insert[of "dij_heap st" "src_current (dij_srcs st)" 0]
    unfolding invar_2_def dijkstra_upd_init_def insert_source_def
    by auto
qed

text \<open>The relaxation branch: either the head of the edge is left alone, or it is inserted into the
      queue (first reach), or its key is decreased. The new distance is non-negative and finite.\<close>

lemma invar_2_holds_relax[invar_holds_intros]:
  assumes "dijkstra_call_relax_conds st" "invar_1 st" "invar_2 st" "invar_3 st"
  shows "invar_2 (dijkstra_upd_relax st)"
proof(rule relax_edge_facts[OF assms(1-3)], goal_cases)
  case (1 u)
  let ?v = "snd (out_current (dij_graph st) u)"
  let ?d = "dist_lookup (dij_dist st) u + w (out_current (dij_graph st) u)"
  have "0 \<le> ?d"
    using 1 assms(4)
    by (auto elim!: invar_3_props)
  hence "?d < dist_lookup (dij_dist st) ?v \<Longrightarrow> dist_lookup (dij_dist st) ?v \<noteq> -1"
    by linarith
  hence "\<lbrakk>?v \<notin> seen_abstract (dij_seen st); ?d < dist_lookup (dij_dist st) ?v\<rbrakk>
           \<Longrightarrow> queue_invar (queue_decrease_key (dij_heap st) ?v ?d)"
    using 1 assms(3)
    by (auto intro!: heap.queue_decrease_key(1)[where k' = "dist_lookup (dij_dist st) ?v"])
  thus ?case
    using 1 \<open>0 \<le> ?d\<close> invar_1_ds[OF assms(2)] assms(3)[unfolded invar_2_def]
          heap.queue_insert[of "dij_heap st" ?v ?d]
          heap.queue_decrease_key(2)[of "dij_heap st" ?v "dist_lookup (dij_dist st) ?v" ?d]
    unfolding invar_2_def dijkstra_upd_relax_def relax_edge_def Let_def
    by auto
qed


subsection \<open>Well-formedness is preserved\<close>

text \<open>The array, graph and source-iterator operations are specified only inside their universe
      \<open>\<V>\<close>, so preserving well-formedness needs that the vertex being scanned or settled, the head of
      the relaxed edge, and the loaded source are graph vertices. These facts come from the coupling
      invariant (a popped vertex lies in the queue's universe) and from the source-phase invariant.\<close>

lemma invar_1_holds_relax[invar_holds_intros]:
  "\<lbrakk>dijkstra_call_relax_conds st; invar_1 st; invar_2 st\<rbrakk> \<Longrightarrow> invar_1 (dijkstra_upd_relax st)"
  by (erule relax_edge_facts) (auto simp: dijkstra_upd_relax_def Let_def intro!: invar_1_intro)

lemma invar_1_holds_finish[invar_holds_intros]:
  "\<lbrakk>dijkstra_call_finish_conds st; invar_1 st\<rbrakk> \<Longrightarrow> invar_1 (dijkstra_upd_finish st)"
  by (auto simp: dijkstra_upd_finish_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_1_holds_init[invar_holds_intros]:
  "\<lbrakk>dijkstra_call_init_conds st; invar_1 st; invar_3 st\<rbrakk> \<Longrightarrow> invar_1 (dijkstra_upd_init st)"
  by (erule init_branch_facts) (auto simp: dijkstra_upd_init_def intro!: invar_1_intro)

lemma invar_1_holds_skip[invar_holds_intros]:
  "\<lbrakk>dijkstra_call_skip_conds st; invar_1 st\<rbrakk> \<Longrightarrow> invar_1 (dijkstra_upd_skip st)"
  by (auto simp: dijkstra_upd_skip_def elim!: invar_props_elims intro!: invar_props_intros split: prod.splits)

lemma invar_1_holds_settle[invar_holds_intros]:
  "\<lbrakk>dijkstra_call_settle_conds st; invar_1 st; invar_2 st\<rbrakk> \<Longrightarrow> invar_1 (dijkstra_upd_settle st)"
  by (erule dijkstra_call_settle_condsE, frule popped_vertex)
     (auto simp: dijkstra_upd_settle_def intro!: invar_1_intro out_graph_inv_reset)

lemma invar_1_holds_done[invar_holds_intros]:
  "\<lbrakk>dijkstra_ret_done_conds st; invar_1 st\<rbrakk> \<Longrightarrow> invar_1 (dijkstra_ret_done st)"
  by (auto simp: dijkstra_ret_done_def elim!: invar_props_elims intro!: invar_props_intros split: prod.splits)

lemma invar_1_holds_found[invar_holds_intros]:
  "\<lbrakk>dijkstra_ret_found_conds st; invar_1 st\<rbrakk> \<Longrightarrow> invar_1 (dijkstra_ret_found st)"
  by (auto simp: dijkstra_ret_found_def Let_def elim!: invar_1_props intro!: invar_1_intro split: prod.splits)


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

lemma invar_1_initial[invar_holds_intros]: "invar_1 initial_state"
  by (auto simp: initial_state_def invar_1_def graph_inv dist_init_invar parent_init_invar srcs_invar)

lemma invar_2_initial[invar_holds_intros]: "invar_2 initial_state"
  by (auto simp: initial_state_def invar_2_def heap.queue_empty dist_init_inf)

lemma invar_3_initial[invar_holds_intros]: "invar_3 initial_state"
  by (auto simp: initial_state_def invar_3_def srcs_in_V dist_init_inf)

lemma invar_4_initial[invar_holds_intros]: "invar_4 initial_state"
  by (auto simp: initial_state_def invar_4_def)


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
  by (erule dijkstra_call_settle_condsE, frule popped_vertex)
     (auto simp: dijkstra_upd_settle_def m_unseen_def \<V>_finite simp del: card_Diff_insert
           intro!: mlex_less psubset_card_mono)

lemma m_unseen_init[termination_intros]: "m_unseen (dijkstra_upd_init st) = m_unseen st"
  by (simp add: dijkstra_upd_init_def insert_source_def m_unseen_def)

lemma m_unseen_relax[termination_intros]: "m_unseen (dijkstra_upd_relax st) = m_unseen st"
  by (simp add: m_unseen_def)

lemma m_unseen_finish[termination_intros]: "m_unseen (dijkstra_upd_finish st) = m_unseen st"
  by (simp add: dijkstra_upd_finish_def m_unseen_def)

lemma m_srcs_relax[termination_intros]: "m_srcs (dijkstra_upd_relax st) = m_srcs st"
  by (simp add: m_srcs_def)

lemma m_srcs_finish[termination_intros]: "m_srcs (dijkstra_upd_finish st) = m_srcs st"
  by (simp add: dijkstra_upd_finish_def m_srcs_def)

lemma init_terminates[termination_intros]:
  "\<lbrakk>dijkstra_call_init_conds st; invar_1 st; invar_3 st\<rbrakk> \<Longrightarrow> (dijkstra_upd_init st, st) \<in> m_srcs <*mlex*> r"
  by (erule init_branch_facts)
     (auto simp: dijkstra_upd_init_def insert_source_def m_srcs_def card_gt_0_iff intro!: mlex_less diff_Suc_less)

lemma relax_terminates[termination_intros]:
  "\<lbrakk>dijkstra_call_relax_conds st; invar_1 st; invar_2 st\<rbrakk> \<Longrightarrow> (dijkstra_upd_relax st, st) \<in> m_scan <*mlex*> r"
  by (erule relax_edge_facts)
     (auto simp: m_scan_def card_gt_0_iff finite_out_remaining intro!: mlex_less diff_Suc_less)

lemma finish_terminates[termination_intros]:
  "\<lbrakk>dijkstra_call_finish_conds st; invar_1 st; invar_2 st\<rbrakk> \<Longrightarrow> (dijkstra_upd_finish st, st) \<in> m_scan <*mlex*> r"
  by (auto simp: dijkstra_upd_finish_def m_scan_def intro!: mlex_less elim!: call_cond_elims)

lemma in_dijkstra_term_rel'[termination_intros]:
  "\<lbrakk>dijkstra_call_settle_conds st; invar_1 st; invar_2 st\<rbrakk> \<Longrightarrow> (dijkstra_upd_settle st, st) \<in> dijkstra_term_rel"
  "\<lbrakk>dijkstra_call_init_conds st; invar_1 st; invar_3 st\<rbrakk> \<Longrightarrow> (dijkstra_upd_init st, st) \<in> dijkstra_term_rel"
  "\<lbrakk>dijkstra_call_relax_conds st; invar_1 st; invar_2 st\<rbrakk> \<Longrightarrow> (dijkstra_upd_relax st, st) \<in> dijkstra_term_rel"
  "\<lbrakk>dijkstra_call_finish_conds st; invar_1 st; invar_2 st\<rbrakk> \<Longrightarrow> (dijkstra_upd_finish st, st) \<in> dijkstra_term_rel"
  by (simp add: dijkstra_term_rel_def termination_intros)+

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
proof-
  obtain p s where p: "s \<in> S" "ag.path_bet p s (fst e)" "distinct p" "weight w p \<le> du"
    using ag_dist_set_less_infty_get_path[OF assms(1), of w "fst e"] assms(3)
    by (force simp: ag.is_shortest_path_def)
  moreover obtain p1 where "ag.path_bet p1 s (fst e)" "distinct (p1 @ [e])" "weight w p1 \<le> weight w p"
  proof(cases "e \<in> set p")
    case True
    then obtain p1 p2 where "p = p1 @ e # p2" "ag.path_bet p1 s (fst e)"
      using ag_path_bet_edge_split[OF p(2)]
      by blast
    thus thesis
      using that p(3) weight_nonneg[of p2] ag_path_bet_edges_subset[OF p(2)] assms(2) w_nonneg
      by auto
  qed (use p that in auto)
  ultimately have "ag.distance_set w S (snd e) \<le> ereal (weight w p1 + w e)" "weight w p1 + w e \<le> du + w e"
    using ag_distance_set_le_path[OF p(1) ag_path_bet_snocI[OF _ assms(2)]]
    by (auto simp: weight_snoc)
  thus ?thesis
    using order_trans ereal_less_eq(3)
    by blast
qed


subsubsection \<open>The source set is constant, and distances stay unchanged on the non-updating branches\<close>

lemma dijkstra_upd_srcs_dist[simp]:
  "dij_srcs (dijkstra_upd_finish st) = dij_srcs st" "dij_dist (dijkstra_upd_finish st) = dij_dist st"
  "dij_srcs (dijkstra_upd_settle st) = dij_srcs st" "dij_dist (dijkstra_upd_settle st) = dij_dist st"
  "dij_srcs (dijkstra_upd_skip st) = dij_srcs st" "dij_dist (dijkstra_upd_skip st) = dij_dist st"
  "dij_srcs (dijkstra_ret_found st) = dij_srcs st" "dij_dist (dijkstra_ret_found st) = dij_dist st"
  "dij_srcs (dijkstra_ret_done st) = dij_srcs st" "dij_dist (dijkstra_ret_done st) = dij_dist st"
  by (simp_all add: dijkstra_upd_finish_def dijkstra_upd_settle_def dijkstra_upd_skip_def
                    dijkstra_ret_found_def dijkstra_ret_done_def Let_def split: prod.splits)

lemma dijkstra_upd_init_srcs[simp]: "dij_srcs (dijkstra_upd_init st) = src_move (dij_srcs st)"
  by (simp add: dijkstra_upd_init_def)


subsubsection \<open>The abstract source set is invariant\<close>

definition "invar_6 st \<longleftrightarrow> src_abstract (dij_srcs st) = src_abstract srcs"

lemma invar_6_props[invar_props_elims]: "\<lbrakk>invar_6 st; src_abstract (dij_srcs st) = src_abstract srcs \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: invar_6_def)

lemma invar_6_intro[invar_props_intros]: "src_abstract (dij_srcs st) = src_abstract srcs \<Longrightarrow> invar_6 st"
  by (auto simp: invar_6_def)

lemma invar_6_holds_relax[invar_holds_intros]:
    "\<lbrakk>dijkstra_call_relax_conds st; invar_6 st\<rbrakk> \<Longrightarrow> invar_6 (dijkstra_upd_relax st)"
  and invar_6_holds_finish[invar_holds_intros]:
    "\<lbrakk>dijkstra_call_finish_conds st; invar_6 st\<rbrakk> \<Longrightarrow> invar_6 (dijkstra_upd_finish st)"
  and invar_6_holds_done[invar_holds_intros]:
    "\<lbrakk>dijkstra_ret_done_conds st; invar_6 st\<rbrakk> \<Longrightarrow> invar_6 (dijkstra_ret_done st)"
  and invar_6_holds_skip[invar_holds_intros]:
    "\<lbrakk>dijkstra_call_skip_conds st; invar_6 st\<rbrakk> \<Longrightarrow> invar_6 (dijkstra_upd_skip st)"
  and invar_6_holds_settle[invar_holds_intros]:
    "\<lbrakk>dijkstra_call_settle_conds st; invar_6 st\<rbrakk> \<Longrightarrow> invar_6 (dijkstra_upd_settle st)"
  and invar_6_holds_found[invar_holds_intros]:
    "\<lbrakk>dijkstra_ret_found_conds st; invar_6 st\<rbrakk> \<Longrightarrow> invar_6 (dijkstra_ret_found st)"
  by (simp_all add: invar_6_def)

lemma invar_6_holds_init[invar_holds_intros]:
  "\<lbrakk>dijkstra_call_init_conds st; invar_1 st; invar_3 st; invar_6 st\<rbrakk> \<Longrightarrow> invar_6 (dijkstra_upd_init st)"
  by (erule init_branch_facts) (auto simp: invar_6_def)

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

definition "invar_5 st \<longleftrightarrow> (\<forall>v. dist_lookup (dij_dist st) v \<noteq> -1 \<longrightarrow>
   ag.distance_set w (src_abstract srcs) v \<le> ereal (dist_lookup (dij_dist st) v))"

lemma invar_5_props[invar_props_elims]:
  "\<lbrakk>invar_5 st;
   \<lbrakk>\<forall>v. dist_lookup (dij_dist st) v \<noteq> -1 \<longrightarrow>
       ag.distance_set w (src_abstract srcs) v \<le> ereal (dist_lookup (dij_dist st) v)\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: invar_5_def)

lemma invar_5_intro[invar_props_intros]:
  "\<forall>v. dist_lookup (dij_dist st) v \<noteq> -1 \<longrightarrow> ag.distance_set w (src_abstract srcs) v \<le> ereal (dist_lookup (dij_dist st) v)
   \<Longrightarrow> invar_5 st"
  by (auto simp: invar_5_def)

lemma invar_5_holds_finish[invar_holds_intros]:
    "\<lbrakk>dijkstra_call_finish_conds st; invar_5 st\<rbrakk> \<Longrightarrow> invar_5 (dijkstra_upd_finish st)"
  and invar_5_holds_settle[invar_holds_intros]:
    "\<lbrakk>dijkstra_call_settle_conds st; invar_5 st\<rbrakk> \<Longrightarrow> invar_5 (dijkstra_upd_settle st)"
  and invar_5_holds_skip[invar_holds_intros]:
    "\<lbrakk>dijkstra_call_skip_conds st; invar_5 st\<rbrakk> \<Longrightarrow> invar_5 (dijkstra_upd_skip st)"
  and invar_5_holds_done[invar_holds_intros]:
    "\<lbrakk>dijkstra_ret_done_conds st; invar_5 st\<rbrakk> \<Longrightarrow> invar_5 (dijkstra_ret_done st)"
  and invar_5_holds_found[invar_holds_intros]:
    "\<lbrakk>dijkstra_ret_found_conds st; invar_5 st\<rbrakk> \<Longrightarrow> invar_5 (dijkstra_ret_found st)"
  by (auto simp: invar_5_def)

lemma distance_set_source: "s \<in> src_abstract srcs \<Longrightarrow> ag.distance_set w (src_abstract srcs) s \<le> ereal 0"
  using ag_distance_set_le_path[of s "src_abstract srcs" "[]" s w]
  by (simp add: zero_ereal_def)

lemma invar_5_holds_init[invar_holds_intros]:
  "\<lbrakk>dijkstra_call_init_conds st; invar_1 st; invar_3 st; invar_5 st; invar_6 st\<rbrakk> \<Longrightarrow> invar_5 (dijkstra_upd_init st)"
  by (erule init_branch_facts)
     (auto simp: invar_5_def invar_6_def dijkstra_upd_init_def insert_source_def intro: distance_set_source)

lemma invar_5_holds_relax[invar_holds_intros]:
  assumes "dijkstra_call_relax_conds st" "invar_1 st" "invar_2 st" "invar_3 st" "invar_5 st"
  shows "invar_5 (dijkstra_upd_relax st)"
proof(rule relax_edge_facts[OF assms(1-3)], goal_cases)
  case (1 u)
  hence "allowed_edge (out_current (dij_graph st) u) \<Longrightarrow>
         ag.distance_set w (src_abstract srcs) (snd (out_current (dij_graph st) u))
           \<le> ereal (dist_lookup (dij_dist st) u + w (out_current (dij_graph st) u))"
    using assms(4,5) finite_subset[OF srcs_in_V \<V>_finite]
    by (auto simp: invar_5_def intro!: distance_set_edge_bound elim!: invar_3_props)
  thus ?case
    using 1 assms(2,5)
    by (auto simp: invar_5_def dijkstra_upd_relax_dist split: if_splits)
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
  by (auto intro!: invar_holds_intros)

text \<open>Every distance the algorithm reports is the weight of an actual (source-to-\<open>v\<close>) path, hence an
      upper bound on the true set-distance. Equality for settled vertices (optimality) is the
      remaining part of the correctness argument.\<close>

lemma dijkstra_compute_upper_bound:
  "dist_lookup (dij_dist dijkstra_compute) v \<noteq> -1 \<Longrightarrow>
     ag.distance_set w (src_abstract srcs) v \<le> ereal (dist_lookup (dij_dist dijkstra_compute) v)"
  using invar_5_compute
  by (auto elim!: invar_5_props)


subsection \<open>Optimality: settled distances are shortest\<close>

text \<open>The remaining, harder direction: a settled vertex's recorded distance is not merely an upper
      bound (soundness, @{thm dijkstra_compute_upper_bound}) but the exact set-distance. The argument
      rests on three auxiliary invariants -- every loaded source keeps distance \<open>0\<close> (@{term invar_9}),
      settled vertices are fully scanned once the cursor rests (@{term invar_7}), and every scanned
      edge out of a settled vertex has already relaxed its head (@{term invar_8}, the \<^emph>\<open>frontier\<close>) --
      together with the min-extraction property of the queue.\<close>

subsubsection \<open>Loaded sources keep distance zero\<close>

definition "invar_9 st \<longleftrightarrow>
   (\<forall>v. v \<in> src_abstract srcs \<longrightarrow> v \<notin> src_remaining (dij_srcs st) \<longrightarrow> dist_lookup (dij_dist st) v = 0)"

lemma invar_9_props[invar_props_elims]:
  "\<lbrakk>invar_9 st;
   \<lbrakk>\<forall>v. v \<in> src_abstract srcs \<longrightarrow> v \<notin> src_remaining (dij_srcs st) \<longrightarrow> dist_lookup (dij_dist st) v = 0\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: invar_9_def)

lemma invar_9_intro[invar_props_intros]:
  "\<forall>v. v \<in> src_abstract srcs \<longrightarrow> v \<notin> src_remaining (dij_srcs st) \<longrightarrow> dist_lookup (dij_dist st) v = 0
   \<Longrightarrow> invar_9 st"
  by (auto simp: invar_9_def)

lemma invar_9_holds_finish[invar_holds_intros]:
    "\<lbrakk>dijkstra_call_finish_conds st; invar_9 st\<rbrakk> \<Longrightarrow> invar_9 (dijkstra_upd_finish st)"
  and invar_9_holds_done[invar_holds_intros]:
    "\<lbrakk>dijkstra_ret_done_conds st; invar_9 st\<rbrakk> \<Longrightarrow> invar_9 (dijkstra_ret_done st)"
  and invar_9_holds_skip[invar_holds_intros]:
    "\<lbrakk>dijkstra_call_skip_conds st; invar_9 st\<rbrakk> \<Longrightarrow> invar_9 (dijkstra_upd_skip st)"
  and invar_9_holds_settle[invar_holds_intros]:
    "\<lbrakk>dijkstra_call_settle_conds st; invar_9 st\<rbrakk> \<Longrightarrow> invar_9 (dijkstra_upd_settle st)"
  and invar_9_holds_found[invar_holds_intros]:
    "\<lbrakk>dijkstra_ret_found_conds st; invar_9 st\<rbrakk> \<Longrightarrow> invar_9 (dijkstra_ret_found st)"
  by (auto simp: invar_9_def)

lemma invar_9_holds_init[invar_holds_intros]:
  "\<lbrakk>dijkstra_call_init_conds st; invar_1 st; invar_3 st; invar_9 st\<rbrakk> \<Longrightarrow> invar_9 (dijkstra_upd_init st)"
  by (erule init_branch_facts) (auto simp: invar_9_def dijkstra_upd_init_def insert_source_def)

lemma invar_9_holds_relax[invar_holds_intros]:
  assumes "dijkstra_call_relax_conds st" "invar_1 st" "invar_2 st" "invar_3 st" "invar_9 st"
  shows "invar_9 (dijkstra_upd_relax st)"
proof(rule relax_edge_facts[OF assms(1-3)], goal_cases)
  case (1 u)
  hence "0 \<le> dist_lookup (dij_dist st) u + w (out_current (dij_graph st) u)"
    using assms(4)
    by (auto elim!: invar_3_props)
  thus ?case
    using 1 assms(2,5)
    by (auto simp: invar_9_def dijkstra_upd_relax_dist)
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
  using srcs_fresh
  by (auto simp: initial_state_def invar_9_def dist_init_inf)


subsubsection \<open>When the cursor rests, settled vertices are fully scanned\<close>

definition "invar_7 st \<longleftrightarrow> (dij_target st = None \<longrightarrow>
   (\<forall>x. x \<in> seen_abstract (dij_seen st) \<longrightarrow> dij_curr st = Some x \<or> out_remaining (dij_graph st) x = {}))"

lemma invar_7_props[invar_props_elims]:
  "\<lbrakk>invar_7 st;
   \<lbrakk>dij_target st = None \<Longrightarrow>
       \<forall>x. x \<in> seen_abstract (dij_seen st) \<longrightarrow> dij_curr st = Some x \<or> out_remaining (dij_graph st) x = {}\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: invar_7_def)

lemma invar_7_intro[invar_props_intros]:
  "(dij_target st = None \<Longrightarrow>
      \<forall>x. x \<in> seen_abstract (dij_seen st) \<longrightarrow> dij_curr st = Some x \<or> out_remaining (dij_graph st) x = {})
   \<Longrightarrow> invar_7 st"
  by (auto simp: invar_7_def)

lemma invar_7_holds_done[invar_holds_intros]:
    "\<lbrakk>dijkstra_ret_done_conds st; invar_7 st\<rbrakk> \<Longrightarrow> invar_7 (dijkstra_ret_done st)"
  and invar_7_holds_skip[invar_holds_intros]:
    "\<lbrakk>dijkstra_call_skip_conds st; invar_7 st\<rbrakk> \<Longrightarrow> invar_7 (dijkstra_upd_skip st)"
  and invar_7_holds_found[invar_holds_intros]:
    "\<lbrakk>dijkstra_ret_found_conds st; invar_7 st\<rbrakk> \<Longrightarrow> invar_7 (dijkstra_ret_found st)"
  by (auto simp: invar_7_def dijkstra_ret_done_def dijkstra_upd_skip_def dijkstra_ret_found_def Let_def
           split: prod.splits)

lemma invar_7_holds_init[invar_holds_intros]:
  "\<lbrakk>dijkstra_call_init_conds st; invar_1 st; invar_4 st\<rbrakk> \<Longrightarrow> invar_7 (dijkstra_upd_init st)"
  by (auto simp: invar_7_def dijkstra_upd_init_def elim!: dijkstra_call_init_condsE invar_props_elims)

lemma invar_7_holds_finish[invar_holds_intros]:
  "\<lbrakk>dijkstra_call_finish_conds st; invar_1 st; invar_2 st; invar_7 st\<rbrakk> \<Longrightarrow> invar_7 (dijkstra_upd_finish st)"
  by (erule dijkstra_call_finish_condsE, frule invar_2_in_V(3)) (auto simp: invar_7_def dijkstra_upd_finish_def)

lemma invar_7_holds_relax[invar_holds_intros]:
  "\<lbrakk>dijkstra_call_relax_conds st; invar_1 st; invar_2 st; invar_7 st\<rbrakk> \<Longrightarrow> invar_7 (dijkstra_upd_relax st)"
  by (erule relax_edge_facts) (auto simp: invar_7_def)

lemma invar_7_holds_settle[invar_holds_intros]:
  "\<lbrakk>dijkstra_call_settle_conds st; invar_1 st; invar_2 st; invar_7 st\<rbrakk> \<Longrightarrow> invar_7 (dijkstra_upd_settle st)"
  by (erule dijkstra_call_settle_condsE, frule popped_vertex) (auto simp: invar_7_def dijkstra_upd_settle_def)

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
  by (auto simp: initial_state_def invar_7_def)



subsubsection \<open>The frontier invariant: scanned allowed edges out of settled vertices are relaxed\<close>

subsubsection \<open>The frontier invariant: scanned allowed edges out of settled vertices are relaxed\<close>

definition "invar_8 st \<longleftrightarrow>
  (\<forall>x. x \<in> seen_abstract (dij_seen st) \<longrightarrow> dist_lookup (dij_dist st) x \<noteq> -1)
  \<and> (\<forall>x. x \<notin> seen_abstract (dij_seen st) \<longrightarrow> out_iterated (dij_graph st) x = {})
  \<and> (\<forall>x e. x \<in> seen_abstract (dij_seen st) \<longrightarrow> e \<in> out_iterated (dij_graph st) x \<longrightarrow> allowed_edge e \<longrightarrow>
        (snd e \<in> seen_abstract (dij_seen st) \<or>
         (dist_lookup (dij_dist st) (snd e) \<noteq> -1 \<and> dist_lookup (dij_dist st) (snd e) \<le> dist_lookup (dij_dist st) x + w e)))"

lemma invar_8_props[invar_props_elims]:
  "\<lbrakk>invar_8 st;
   \<lbrakk>\<forall>x. x \<in> seen_abstract (dij_seen st) \<longrightarrow> dist_lookup (dij_dist st) x \<noteq> -1;
     \<forall>x. x \<notin> seen_abstract (dij_seen st) \<longrightarrow> out_iterated (dij_graph st) x = {};
     \<forall>x e. x \<in> seen_abstract (dij_seen st) \<longrightarrow> e \<in> out_iterated (dij_graph st) x \<longrightarrow> allowed_edge e \<longrightarrow>
       (snd e \<in> seen_abstract (dij_seen st) \<or> (dist_lookup (dij_dist st) (snd e) \<noteq> -1 \<and>
          dist_lookup (dij_dist st) (snd e) \<le> dist_lookup (dij_dist st) x + w e))\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: invar_8_def)

lemma invar_8_intro[invar_props_intros]:
  "\<lbrakk>\<forall>x. x \<in> seen_abstract (dij_seen st) \<longrightarrow> dist_lookup (dij_dist st) x \<noteq> -1;
    \<forall>x. x \<notin> seen_abstract (dij_seen st) \<longrightarrow> out_iterated (dij_graph st) x = {};
    \<forall>x e. x \<in> seen_abstract (dij_seen st) \<longrightarrow> e \<in> out_iterated (dij_graph st) x \<longrightarrow> allowed_edge e \<longrightarrow>
      (snd e \<in> seen_abstract (dij_seen st) \<or> (dist_lookup (dij_dist st) (snd e) \<noteq> -1 \<and>
         dist_lookup (dij_dist st) (snd e) \<le> dist_lookup (dij_dist st) x + w e))\<rbrakk> \<Longrightarrow> invar_8 st"
  by (auto simp: invar_8_def)

lemma invar_8_frontier:
  "\<lbrakk>invar_8 st; x \<in> seen_abstract (dij_seen st); e \<in> out_iterated (dij_graph st) x; allowed_edge e\<rbrakk> \<Longrightarrow>
     snd e \<in> seen_abstract (dij_seen st) \<or>
     (dist_lookup (dij_dist st) (snd e) \<noteq> -1 \<and> dist_lookup (dij_dist st) (snd e) \<le> dist_lookup (dij_dist st) x + w e)"
  by (auto simp: invar_8_def)

lemma invar_8_holds_done[invar_holds_intros]:
    "\<lbrakk>dijkstra_ret_done_conds st; invar_8 st\<rbrakk> \<Longrightarrow> invar_8 (dijkstra_ret_done st)"
  and invar_8_holds_skip[invar_holds_intros]:
    "\<lbrakk>dijkstra_call_skip_conds st; invar_8 st\<rbrakk> \<Longrightarrow> invar_8 (dijkstra_upd_skip st)"
  and invar_8_holds_finish[invar_holds_intros]:
    "\<lbrakk>dijkstra_call_finish_conds st; invar_8 st\<rbrakk> \<Longrightarrow> invar_8 (dijkstra_upd_finish st)"
  by (auto simp: invar_8_def dijkstra_ret_done_def dijkstra_upd_skip_def dijkstra_upd_finish_def split: prod.splits)

lemma invar_8_holds_init[invar_holds_intros]:
  "\<lbrakk>dijkstra_call_init_conds st; invar_1 st; invar_4 st; invar_8 st\<rbrakk> \<Longrightarrow> invar_8 (dijkstra_upd_init st)"
  by (auto simp: invar_8_def dijkstra_upd_init_def elim!: dijkstra_call_init_condsE invar_1_props invar_4_props)

lemma invar_8_holds_found[invar_holds_intros]:
  "\<lbrakk>dijkstra_ret_found_conds st; invar_1 st; invar_2 st; invar_8 st\<rbrakk> \<Longrightarrow> invar_8 (dijkstra_ret_found st)"
  by (erule dijkstra_ret_found_condsE, frule popped_vertex) (auto simp: invar_8_def dijkstra_ret_found_def)

lemma invar_8_holds_settle[invar_holds_intros]:
  "\<lbrakk>dijkstra_call_settle_conds st; invar_1 st; invar_2 st; invar_8 st\<rbrakk> \<Longrightarrow> invar_8 (dijkstra_upd_settle st)"
  by (erule dijkstra_call_settle_condsE, frule popped_vertex) (auto simp: invar_8_def dijkstra_upd_settle_def)

text \<open>Relaxing changes only the distance of an unsettled head, never increases a distance, and
      leaves the head within \<open>du + w e\<close>; the new scanned edge is the relaxed one.\<close>

lemma invar_8_holds_relax[invar_holds_intros]:
  assumes "dijkstra_call_relax_conds st" "invar_1 st" "invar_2 st" "invar_3 st" "invar_8 st"
  shows "invar_8 (dijkstra_upd_relax st)"
proof(rule relax_edge_facts[OF assms(1-3)], goal_cases)
  case (1 u)
  let ?e = "out_current (dij_graph st) u" and ?d' = "dist_lookup (dij_dist (dijkstra_upd_relax st))"
  have "u \<in> seen_abstract (dij_seen st)" "dist_lookup (dij_dist st) u \<noteq> -1"
    "0 \<le> dist_lookup (dij_dist st) u + w ?e"
    using 1 assms(4)
    by (auto elim!: invar_3_props)
  hence "\<forall>x \<in> seen_abstract (dij_seen st). ?d' x = dist_lookup (dij_dist st) x"
    "\<forall>y. dist_lookup (dij_dist st) y \<noteq> -1 \<longrightarrow> ?d' y \<noteq> -1 \<and> ?d' y \<le> dist_lookup (dij_dist st) y"
    "allowed_edge ?e \<Longrightarrow> snd ?e \<in> seen_abstract (dij_seen st) \<or>
       (?d' (snd ?e) \<noteq> -1 \<and> ?d' (snd ?e) \<le> dist_lookup (dij_dist st) u + w ?e)"
    using 1 assms(2,3)
    by (auto simp: dijkstra_upd_relax_dist)
  thus ?case
    using 1 assms(5) \<open>u \<in> seen_abstract (dij_seen st)\<close>
    unfolding invar_8_def
    by (clarsimp, blast intro: order_trans)
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
  by (auto simp: initial_state_def invar_8_def graph_fresh)


subsubsection \<open>No target has been found yet (until the early-stop return)\<close>

definition "invar_10 st \<longleftrightarrow> dij_target st = None"

lemma invar_10_props[invar_props_elims]: "\<lbrakk>invar_10 st; dij_target st = None \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: invar_10_def)

lemma invar_10_intro[invar_props_intros]: "dij_target st = None \<Longrightarrow> invar_10 st"
  by (auto simp: invar_10_def)

lemma invar_10_holds_finish[invar_holds_intros]:
    "\<lbrakk>dijkstra_call_finish_conds st; invar_10 st\<rbrakk> \<Longrightarrow> invar_10 (dijkstra_upd_finish st)"
  and invar_10_holds_skip[invar_holds_intros]:
    "\<lbrakk>dijkstra_call_skip_conds st; invar_10 st\<rbrakk> \<Longrightarrow> invar_10 (dijkstra_upd_skip st)"
  and invar_10_holds_init[invar_holds_intros]:
    "\<lbrakk>dijkstra_call_init_conds st; invar_10 st\<rbrakk> \<Longrightarrow> invar_10 (dijkstra_upd_init st)"
  and invar_10_holds_relax[invar_holds_intros]:
    "\<lbrakk>dijkstra_call_relax_conds st; invar_10 st\<rbrakk> \<Longrightarrow> invar_10 (dijkstra_upd_relax st)"
  and invar_10_holds_settle[invar_holds_intros]:
    "\<lbrakk>dijkstra_call_settle_conds st; invar_10 st\<rbrakk> \<Longrightarrow> invar_10 (dijkstra_upd_settle st)"
  and invar_10_holds_done[invar_holds_intros]:
    "\<lbrakk>dijkstra_ret_done_conds st; invar_10 st\<rbrakk> \<Longrightarrow> invar_10 (dijkstra_ret_done st)"
  by (auto simp: invar_10_def dijkstra_upd_finish_def dijkstra_upd_skip_def dijkstra_upd_init_def
                 dijkstra_upd_settle_def dijkstra_ret_done_def Let_def split: prod.splits)

lemma invar_10_initial[invar_holds_intros]: "invar_10 initial_state"
  by (simp add: invar_10_def initial_state_def)


subsubsection \<open>The optimality invariant\<close>

definition "invar_opt st \<longleftrightarrow> (\<forall>v. v \<in> seen_abstract (dij_seen st) \<longrightarrow>
   ereal (dist_lookup (dij_dist st) v) \<le> ag.distance_set w (src_abstract srcs) v)"

lemma invar_opt_props[invar_props_elims]:
  "\<lbrakk>invar_opt st;
   \<lbrakk>\<forall>v. v \<in> seen_abstract (dij_seen st) \<longrightarrow> ereal (dist_lookup (dij_dist st) v) \<le> ag.distance_set w (src_abstract srcs) v\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: invar_opt_def)

lemma invar_opt_intro[invar_props_intros]:
  "\<forall>v. v \<in> seen_abstract (dij_seen st) \<longrightarrow> ereal (dist_lookup (dij_dist st) v) \<le> ag.distance_set w (src_abstract srcs) v
   \<Longrightarrow> invar_opt st"
  by (auto simp: invar_opt_def)

lemma finite_srcs: "finite (src_abstract srcs)"
  using srcs_in_V \<V>_finite
  by (rule finite_subset)

text \<open>When the cursor rests and no target was found, a settled vertex has scanned all its edges.\<close>

lemma settled_fully_scanned:
  "\<lbrakk>dij_curr st = None; dij_target st = None; invar_1 st; invar_2 st; invar_7 st; x \<in> seen_abstract (dij_seen st)\<rbrakk>
     \<Longrightarrow> out_iterated (dij_graph st) x = \<delta>\<^sup>+ x"
  using outg.idx_partition_union[of "dij_graph st" x] invar_2_in_V(1)[of st x]
  by (auto simp: out_graph_inv_def elim!: invar_7_props invar_1_props)

text \<open>The key path lemma: from any settled vertex \<open>x\<close>, following a distinct path \<open>p\<close> to an unsettled
      \<open>v\<close>, the frontier invariant and the recursive optimality of intermediate settled vertices produce
      a reached, unsettled vertex \<open>y\<close> whose distance is bounded by \<open>dist x + weight p\<close>.\<close>

lemma frontier_reach:
  "\<lbrakk>ag.path_bet p x v; distinct p; x \<in> seen_abstract (dij_seen st); v \<notin> seen_abstract (dij_seen st);
    dij_curr st = None; dij_target st = None; invar_1 st; invar_2 st; invar_5 st; invar_7 st; invar_8 st;
    invar_opt st\<rbrakk>
   \<Longrightarrow> \<exists>y. y \<notin> seen_abstract (dij_seen st) \<and> dist_lookup (dij_dist st) y \<noteq> -1 \<and>
          dist_lookup (dij_dist st) y \<le> dist_lookup (dij_dist st) x + weight w p"
proof(induction p arbitrary: x)
  case (Cons e p')
  hence e: "e \<in> Ea" "fst e = x" "ag.path_bet p' (snd e) v" "0 \<le> weight w p'"
    using weight_nonneg ag_path_bet_edges_subset
    by (auto elim: ag_path_bet_ConsE)
  hence "e \<in> out_iterated (dij_graph st) x"
    using Cons.prems settled_fully_scanned
    by (auto simp: delta_plus_def)
  hence front: "snd e \<in> seen_abstract (dij_seen st) \<or>
      (dist_lookup (dij_dist st) (snd e) \<noteq> -1 \<and> dist_lookup (dij_dist st) (snd e) \<le> dist_lookup (dij_dist st) x + w e)"
    using Cons.prems e
    by (auto elim!: invar_8_props)
  show ?case
  proof(cases "snd e \<in> seen_abstract (dij_seen st)")
    case True
    have "ag.distance_set w (src_abstract srcs) (fst e) \<le> ereal (dist_lookup (dij_dist st) x)"
      using Cons.prems e
      by (auto elim!: invar_5_props invar_8_props)
    hence "ag.distance_set w (src_abstract srcs) (snd e) \<le> ereal (dist_lookup (dij_dist st) x + w e)"
      by (rule distance_set_edge_bound[OF finite_srcs e(1)])
    moreover have "ereal (dist_lookup (dij_dist st) (snd e)) \<le> ag.distance_set w (src_abstract srcs) (snd e)"
      using Cons.prems True
      by (auto elim!: invar_opt_props)
    ultimately have "dist_lookup (dij_dist st) (snd e) \<le> dist_lookup (dij_dist st) x + w e"
      using order_trans ereal_less_eq(3)
      by blast
    moreover obtain y where "y \<notin> seen_abstract (dij_seen st)" "dist_lookup (dij_dist st) y \<noteq> -1"
      "dist_lookup (dij_dist st) y \<le> dist_lookup (dij_dist st) (snd e) + weight w p'"
      using Cons.IH[OF e(3) _ True] Cons.prems
      by auto
    ultimately show ?thesis
      by auto
  qed (use front e in force)
qed (auto simp: ag.path_bet_def)

text \<open>The heart of optimality: the recorded distance of the vertex extracted from the queue (whether
      settled or returned as the found target) is at most the true set-distance of every unsettled
      vertex, in particular of itself. The minimum-key extraction, the non-negativity of weights, and
      the frontier argument combine to show that no path to an unsettled vertex can beat it.\<close>

lemma settle_opt_bound:
  assumes "dij_curr st = None" "\<not> src_has (dij_srcs st)" "queue_extract_min (dij_heap st) = (h2, Some u)"
    "invar_1 st" "invar_2 st" "invar_5 st" "invar_7 st" "invar_8 st" "invar_9 st" "invar_10 st" "invar_opt st"
    "v \<notin> seen_abstract (dij_seen st)"
  shows "ereal (dist_lookup (dij_dist st) u) \<le> ag.distance_set w (src_abstract srcs) v"
proof(cases "ag.distance_set w (src_abstract srcs) v < \<infinity>")
  case True
  then obtain p s where "s \<in> src_abstract srcs" "ag.is_shortest_path w p s v"
      "ag.distance w s v = ag.distance_set w (src_abstract srcs) v"
    using ag_dist_set_less_infty_get_path[OF finite_srcs]
    by blast
  hence p: "ag.path_bet p s v" "distinct p" "ag.distance_set w (src_abstract srcs) v = ereal (weight w p)"
    "dist_lookup (dij_dist st) s = 0" "0 \<le> weight w p" "dij_target st = None"
    using assms(1,2,4,9,10) weight_nonneg ag_path_bet_edges_subset
    by (auto simp: ag.is_shortest_path_def invar_10_def elim!: invar_9_props)
  have min: "\<And>y. \<lbrakk>y \<notin> seen_abstract (dij_seen st); dist_lookup (dij_dist st) y \<noteq> -1\<rbrakk>
               \<Longrightarrow> dist_lookup (dij_dist st) u \<le> dist_lookup (dij_dist st) y"
    using popped_vertex[OF assms(3,5)]
    by blast
  have "dist_lookup (dij_dist st) u \<le> weight w p"
  proof(cases "s \<in> seen_abstract (dij_seen st)")
    case True
    thus ?thesis
      using frontier_reach[OF p(1,2) True assms(12,1) p(6) assms(4-8,11)] min p(4)
      by fastforce
  qed (use min p in force)
  thus ?thesis
    using p(3)
    by simp
qed (simp add: not_less)

text \<open>Preservation of the optimality invariant. The distance-changing branches (relax, init) never
      alter the distance of an already-settled vertex; settling (or returning) a new vertex adds it
      to the settled set with an optimal distance by @{thm settle_opt_bound}.\<close>

lemma invar_opt_holds_done[invar_holds_intros]:
    "\<lbrakk>dijkstra_ret_done_conds st; invar_opt st\<rbrakk> \<Longrightarrow> invar_opt (dijkstra_ret_done st)"
  and invar_opt_holds_skip[invar_holds_intros]:
    "\<lbrakk>dijkstra_call_skip_conds st; invar_opt st\<rbrakk> \<Longrightarrow> invar_opt (dijkstra_upd_skip st)"
  and invar_opt_holds_finish[invar_holds_intros]:
    "\<lbrakk>dijkstra_call_finish_conds st; invar_opt st\<rbrakk> \<Longrightarrow> invar_opt (dijkstra_upd_finish st)"
  by (auto simp: invar_opt_def dijkstra_ret_done_def dijkstra_upd_skip_def dijkstra_upd_finish_def
           split: prod.splits)

lemma invar_opt_holds_init[invar_holds_intros]:
  "\<lbrakk>dijkstra_call_init_conds st; invar_1 st; invar_4 st\<rbrakk> \<Longrightarrow> invar_opt (dijkstra_upd_init st)"
  by (auto simp: invar_opt_def dijkstra_upd_init_def elim!: dijkstra_call_init_condsE invar_1_props invar_4_props)

lemma invar_opt_holds_relax[invar_holds_intros]:
  "\<lbrakk>dijkstra_call_relax_conds st; invar_1 st; invar_2 st; invar_opt st\<rbrakk> \<Longrightarrow> invar_opt (dijkstra_upd_relax st)"
  by (erule relax_edge_facts) (auto simp: invar_opt_def dijkstra_upd_relax_dist)

lemma invar_opt_holds_settle[invar_holds_intros]:
  "\<lbrakk>dijkstra_call_settle_conds st; invar_1 st; invar_2 st; invar_5 st; invar_7 st; invar_8 st; invar_9 st;
    invar_10 st; invar_opt st\<rbrakk> \<Longrightarrow> invar_opt (dijkstra_upd_settle st)"
  by (erule dijkstra_call_settle_condsE, frule popped_vertex)
     (auto simp: invar_opt_def dijkstra_upd_settle_def intro: settle_opt_bound)

lemma invar_opt_holds_found[invar_holds_intros]:
  "\<lbrakk>dijkstra_ret_found_conds st; invar_1 st; invar_2 st; invar_5 st; invar_7 st; invar_8 st; invar_9 st;
    invar_10 st; invar_opt st\<rbrakk> \<Longrightarrow> invar_opt (dijkstra_ret_found st)"
  by (erule dijkstra_ret_found_condsE, frule popped_vertex)
     (auto simp: invar_opt_def dijkstra_ret_found_def intro: settle_opt_bound)

lemma invar_opt_holds[invar_holds_intros]:
  assumes "dijkstra_dom st" "invar_1 st" "invar_2 st" "invar_3 st" "invar_4 st" "invar_5 st" "invar_6 st"
    "invar_7 st" "invar_8 st" "invar_9 st" "invar_10 st" "invar_opt st"
  shows "invar_opt (dijkstra st)"
  using assms(2-)
proof(induction rule: dijkstra_induct[OF assms(1)])
  case IH: (1 st)
  show ?case
    apply(rule dijkstra_cases[where st = st])
    by (auto intro!: IH(2-) intro: invar_holds_intros simp: dijkstra_simps[OF IH(1)])
qed

lemma invar_opt_initial[invar_holds_intros]: "invar_opt initial_state"
  by (auto simp: initial_state_def invar_opt_def)


subsubsection \<open>Exact-distance correctness of the computed result\<close>

lemma invar_8_compute: "invar_8 dijkstra_compute"
  and invar_opt_compute: "invar_opt dijkstra_compute"
  unfolding dijkstra_compute_def
  by (auto intro!: invar_holds_intros)

text \<open>The main correctness theorem: for every \<^emph>\<open>settled\<close> vertex the computed distance is exactly the
      shortest-path distance from the source set. Combined with @{thm dijkstra_compute_upper_bound}
      (soundness) this fully characterises the settled distances.\<close>

lemma dijkstra_compute_optimal:
  "v \<in> seen_abstract (dij_seen dijkstra_compute) \<Longrightarrow>
     ereal (dist_lookup (dij_dist dijkstra_compute) v) = ag.distance_set w (src_abstract srcs) v"
  using invar_opt_compute invar_8_compute dijkstra_compute_upper_bound
  by (force elim!: invar_opt_props invar_8_props intro: order.antisym)



subsection \<open>Completeness: the reachable part is fully settled\<close>

text \<open>When @{term early_stop} is \<open>False\<close> the algorithm settles \<^emph>\<open>exactly\<close> the vertices reachable from
      the source set, so together with @{thm dijkstra_compute_optimal} the whole shortest-path tree of
      the reachable part is computed. The proof rests on three facts about the terminating
      configuration: no target has been found (so the run ended in the \<open>done\<close> branch), that branch
      leaves an empty queue with the cursor at rest, and the frontier invariant then makes the settled
      set closed under reachability.\<close>

subsubsection \<open>Without early stopping, no target is ever found\<close>

lemma invar_10_holds_found_ne[invar_holds_intros]:
  "\<lbrakk>dijkstra_ret_found_conds st; \<not> early_stop\<rbrakk> \<Longrightarrow> invar_10 (dijkstra_ret_found st)"
  by (erule dijkstra_ret_found_condsE) simp

lemma target_none_run:
  assumes "dijkstra_dom st" "\<not> early_stop" "invar_10 st"
  shows "invar_10 (dijkstra st)"
  using assms(2-)
proof(induction rule: dijkstra_induct[OF assms(1)])
  case IH: (1 st)
  show ?case
    apply(rule dijkstra_cases[where st = st])
    by (auto intro!: IH(2-) intro: invar_holds_intros simp: dijkstra_simps[OF IH(1)])
qed


subsubsection \<open>The terminating configuration\<close>

definition "terminal_state st \<longleftrightarrow> dij_curr st = None \<and> src_remaining (dij_srcs st) = {} \<and>
   (queue_abstract (dij_heap st) = {} \<or> dij_target st \<noteq> None)"

lemma terminal_ret_done[invar_holds_intros]:
  "\<lbrakk>dijkstra_ret_done_conds st; invar_1 st; invar_2 st\<rbrakk> \<Longrightarrow> terminal_state (dijkstra_ret_done st)"
  using heap.queue_extract_min(5)[of "dij_heap st"]
  by (auto simp: terminal_state_def dijkstra_ret_done_def elim!: dijkstra_ret_done_condsE)

lemma terminal_ret_found[invar_holds_intros]:
  "\<lbrakk>dijkstra_ret_found_conds st; invar_1 st\<rbrakk> \<Longrightarrow> terminal_state (dijkstra_ret_found st)"
  by (auto simp: terminal_state_def dijkstra_ret_found_def elim!: dijkstra_ret_found_condsE)

lemma dijkstra_terminal:
  assumes "dijkstra_dom st" "invar_1 st" "invar_2 st" "invar_3 st" "invar_4 st"
  shows "terminal_state (dijkstra st)"
  using assms(2-)
proof(induction rule: dijkstra_induct[OF assms(1)])
  case IH: (1 st)
  show ?case
    apply(rule dijkstra_cases[where st = st])
    by (auto intro!: IH(2-) intro: invar_holds_intros simp: dijkstra_simps[OF IH(1)])
qed


subsubsection \<open>The settled set is closed under reachability\<close>

lemma reached_settled: "\<lbrakk>queue_abstract (dij_heap st) = {}; invar_2 st; dist_lookup (dij_dist st) x \<noteq> -1\<rbrakk>
                          \<Longrightarrow> x \<in> seen_abstract (dij_seen st)"
  using invar_2_ds(3)[of st x "dist_lookup (dij_dist st) x"]
  by auto

lemma reach_settled:
  assumes "queue_abstract (dij_heap st) = {}" "dij_curr st = None" "dij_target st = None"
    "invar_1 st" "invar_2 st" "invar_7 st" "invar_8 st"
  shows "\<lbrakk>ag.path_bet p x v; x \<in> seen_abstract (dij_seen st)\<rbrakk> \<Longrightarrow> v \<in> seen_abstract (dij_seen st)"
proof(induction p arbitrary: x)
  case (Cons e p')
  hence e: "e \<in> Ea" "fst e = x" "ag.path_bet p' (snd e) v"
    by (auto elim: ag_path_bet_ConsE)
  hence "e \<in> out_iterated (dij_graph st) x"
    using settled_fully_scanned[OF assms(2-6) Cons.prems(2)]
    by (simp add: delta_plus_def)
  hence "snd e \<in> seen_abstract (dij_seen st)"
    using invar_8_frontier[OF assms(7) Cons.prems(2)] e(1) reached_settled[OF assms(1,5)]
    by auto
  thus ?case
    using Cons.IH[OF e(3)]
    by blast
qed (auto simp: ag.path_bet_def)


subsubsection \<open>Completeness of the computed distances\<close>

lemma invar_1_compute: "invar_1 dijkstra_compute"
  and invar_2_compute: "invar_2 dijkstra_compute"
  and invar_7_compute: "invar_7 dijkstra_compute"
  and invar_9_compute: "invar_9 dijkstra_compute"
  unfolding dijkstra_compute_def
  by (auto intro!: invar_holds_intros)

text \<open>With no early stopping, a vertex is reached (finite distance) if and only if it is reachable
      from some source. Combined with @{thm dijkstra_compute_optimal}, the recorded distance of every
      reachable vertex is its true shortest-path distance, and unreachable vertices keep the sentinel
      \<open>-1\<close>.\<close>

lemma dijkstra_compute_complete:
  assumes "\<not> early_stop"
  shows "dist_lookup (dij_dist dijkstra_compute) v \<noteq> -1 \<longleftrightarrow> (\<exists>s \<in> src_abstract srcs. ag.reachable s v)"
proof
  assume "dist_lookup (dij_dist dijkstra_compute) v \<noteq> -1"
  hence "ag.distance_set w (src_abstract srcs) v \<noteq> \<infinity>"
    using dijkstra_compute_upper_bound[of v]
    by auto
  thus "\<exists>s \<in> src_abstract srcs. ag.reachable s v"
    by (simp add: ag_distance_set_infty_iff)
next
  have state: "queue_abstract (dij_heap dijkstra_compute) = {}" "dij_curr dijkstra_compute = None"
      "src_remaining (dij_srcs dijkstra_compute) = {}" "dij_target dijkstra_compute = None"
    using dijkstra_terminal[OF initial_state_props(5,1-4)] target_none_run[OF initial_state_props(5) assms invar_10_initial]
    by (auto simp: terminal_state_def invar_10_def dijkstra_compute_def)
  assume "\<exists>s \<in> src_abstract srcs. ag.reachable s v"
  then obtain s p where "s \<in> src_abstract srcs" "ag.path_bet p s v"
    by (auto simp: ag_reachable_iff_path)
  moreover hence "s \<in> seen_abstract (dij_seen dijkstra_compute)"
    using state(3) invar_9_compute reached_settled[OF state(1) invar_2_compute]
    by (auto elim!: invar_9_props)
  ultimately show "dist_lookup (dij_dist dijkstra_compute) v \<noteq> -1"
    using reach_settled[OF state(1,2,4) invar_1_compute invar_2_compute invar_7_compute invar_8_compute]
          invar_8_compute
    by (auto elim!: invar_8_props)
qed


subsection \<open>The shortest-path tree recorded in the parent map\<close>

text \<open>The parent array stores, for every reached vertex, the edge by which its current distance was
      achieved. We show these edges form a valid \<^emph>\<open>tight\<close> tree: the parent of \<open>v\<close> is an edge \<open>e\<close> into
      \<open>v\<close> whose tail is already settled and satisfies \<open>dist v = dist (fst e) + w e\<close>. This lets us read
      off, for any reached vertex, an actual shortest path back to a source.\<close>

definition "invar_tree st \<longleftrightarrow> (\<forall>v e. parent_lookup (dij_parent st) v = Some e \<longrightarrow>
   fst e \<in> seen_abstract (dij_seen st) \<and> snd e = v \<and> e \<in> Ea \<and> dist_lookup (dij_dist st) (fst e) \<noteq> -1 \<and>
   dist_lookup (dij_dist st) v = dist_lookup (dij_dist st) (fst e) + w e)"

lemma invar_tree_props[invar_props_elims]:
  "\<lbrakk>invar_tree st;
   \<lbrakk>\<And>v e. parent_lookup (dij_parent st) v = Some e \<Longrightarrow>
       fst e \<in> seen_abstract (dij_seen st) \<and> snd e = v \<and> e \<in> Ea \<and> dist_lookup (dij_dist st) (fst e) \<noteq> -1 \<and>
       dist_lookup (dij_dist st) v = dist_lookup (dij_dist st) (fst e) + w e\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: invar_tree_def)

lemma invar_tree_intro[invar_props_intros]:
  "(\<And>v e. parent_lookup (dij_parent st) v = Some e \<Longrightarrow>
      fst e \<in> seen_abstract (dij_seen st) \<and> snd e = v \<and> e \<in> Ea \<and> dist_lookup (dij_dist st) (fst e) \<noteq> -1 \<and>
      dist_lookup (dij_dist st) v = dist_lookup (dij_dist st) (fst e) + w e) \<Longrightarrow> invar_tree st"
  by (auto simp: invar_tree_def)

lemma invar_tree_D:
  "\<lbrakk>invar_tree st; parent_lookup (dij_parent st) v = Some e\<rbrakk> \<Longrightarrow>
     fst e \<in> seen_abstract (dij_seen st) \<and> snd e = v \<and> e \<in> Ea \<and> dist_lookup (dij_dist st) (fst e) \<noteq> -1 \<and>
     dist_lookup (dij_dist st) v = dist_lookup (dij_dist st) (fst e) + w e"
  by (auto simp: invar_tree_def)

lemma invar_tree_holds_done[invar_holds_intros]:
    "\<lbrakk>dijkstra_ret_done_conds st; invar_tree st\<rbrakk> \<Longrightarrow> invar_tree (dijkstra_ret_done st)"
  and invar_tree_holds_skip[invar_holds_intros]:
    "\<lbrakk>dijkstra_call_skip_conds st; invar_tree st\<rbrakk> \<Longrightarrow> invar_tree (dijkstra_upd_skip st)"
  and invar_tree_holds_finish[invar_holds_intros]:
    "\<lbrakk>dijkstra_call_finish_conds st; invar_tree st\<rbrakk> \<Longrightarrow> invar_tree (dijkstra_upd_finish st)"
  by (auto simp: invar_tree_def dijkstra_ret_done_def dijkstra_upd_skip_def dijkstra_upd_finish_def
           split: prod.splits)

lemma invar_tree_holds_settle[invar_holds_intros]:
  "\<lbrakk>dijkstra_call_settle_conds st; invar_1 st; invar_2 st; invar_tree st\<rbrakk> \<Longrightarrow> invar_tree (dijkstra_upd_settle st)"
  by (erule dijkstra_call_settle_condsE, frule popped_vertex) (auto simp: invar_tree_def dijkstra_upd_settle_def)

lemma invar_tree_holds_found[invar_holds_intros]:
  "\<lbrakk>dijkstra_ret_found_conds st; invar_1 st; invar_2 st; invar_tree st\<rbrakk> \<Longrightarrow> invar_tree (dijkstra_ret_found st)"
  by (erule dijkstra_ret_found_condsE, frule popped_vertex) (auto simp: invar_tree_def dijkstra_ret_found_def)

lemma invar_tree_holds_init[invar_holds_intros]:
  "\<lbrakk>dijkstra_call_init_conds st; invar_1 st; invar_4 st; invar_tree st\<rbrakk> \<Longrightarrow> invar_tree (dijkstra_upd_init st)"
  by (auto simp: invar_tree_def dijkstra_upd_init_def elim!: dijkstra_call_init_condsE invar_1_props invar_4_props)

text \<open>Relaxing sets the head's parent to the relaxed edge, which is tight by construction; a recorded
      parent cannot point to the freshly-relaxed head, since that head is unsettled.\<close>

lemma invar_tree_holds_relax[invar_holds_intros]:
  assumes "dijkstra_call_relax_conds st" "invar_1 st" "invar_2 st" "invar_3 st" "invar_tree st"
  shows "invar_tree (dijkstra_upd_relax st)"
proof(rule relax_edge_facts[OF assms(1-3)], goal_cases)
  case (1 u)
  hence "u \<in> seen_abstract (dij_seen st)" "dist_lookup (dij_dist st) u \<noteq> -1"
    "0 \<le> dist_lookup (dij_dist st) u + w (out_current (dij_graph st) u)"
    using assms(4)
    by (auto elim!: invar_3_props)
  thus ?case
    using 1 assms(2,3)
    by (auto simp: invar_tree_def dijkstra_upd_relax_dist dijkstra_upd_relax_parent dest: invar_tree_D[OF assms(5)])
qed

lemma invar_tree_holds[invar_holds_intros]:
  assumes "dijkstra_dom st" "invar_1 st" "invar_2 st" "invar_3 st" "invar_4 st" "invar_tree st"
  shows "invar_tree (dijkstra st)"
  using assms(2-)
proof(induction rule: dijkstra_induct[OF assms(1)])
  case IH: (1 st)
  show ?case
    apply(rule dijkstra_cases[where st = st])
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

lemma invar_wf_props[invar_props_elims]: "\<lbrakk>invar_wf st; wf (par_rel st) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: invar_wf_def)

lemma invar_wf_intro[invar_props_intros]: "wf (par_rel st) \<Longrightarrow> invar_wf st"
  by (auto simp: invar_wf_def)

lemma invar_wf_holds_done[invar_holds_intros]:
    "\<lbrakk>dijkstra_ret_done_conds st; invar_wf st\<rbrakk> \<Longrightarrow> invar_wf (dijkstra_ret_done st)"
  and invar_wf_holds_skip[invar_holds_intros]:
    "\<lbrakk>dijkstra_call_skip_conds st; invar_wf st\<rbrakk> \<Longrightarrow> invar_wf (dijkstra_upd_skip st)"
  and invar_wf_holds_finish[invar_holds_intros]:
    "\<lbrakk>dijkstra_call_finish_conds st; invar_wf st\<rbrakk> \<Longrightarrow> invar_wf (dijkstra_upd_finish st)"
  and invar_wf_holds_settle[invar_holds_intros]:
    "\<lbrakk>dijkstra_call_settle_conds st; invar_wf st\<rbrakk> \<Longrightarrow> invar_wf (dijkstra_upd_settle st)"
  and invar_wf_holds_found[invar_holds_intros]:
    "\<lbrakk>dijkstra_ret_found_conds st; invar_wf st\<rbrakk> \<Longrightarrow> invar_wf (dijkstra_ret_found st)"
  and invar_wf_holds_init[invar_holds_intros]:
    "\<lbrakk>dijkstra_call_init_conds st; invar_wf st\<rbrakk> \<Longrightarrow> invar_wf (dijkstra_upd_init st)"
  by (simp_all add: invar_wf_def par_rel_def dijkstra_ret_done_def dijkstra_upd_skip_def dijkstra_upd_finish_def
                    dijkstra_upd_settle_def dijkstra_ret_found_def dijkstra_upd_init_def insert_source_def Let_def
               split: prod.splits)

lemma invar_wf_holds_relax[invar_holds_intros]:
  assumes "dijkstra_call_relax_conds st" "invar_1 st" "invar_2 st" "invar_3 st" "invar_tree st" "invar_wf st"
  shows "invar_wf (dijkstra_upd_relax st)"
proof(rule relax_edge_facts[OF assms(1-3)], goal_cases)
  case (1 u)
  let ?v = "snd (out_current (dij_graph st) u)"
  have "u \<in> seen_abstract (dij_seen st)"
    using 1 assms(4)
    by (auto elim!: invar_3_props)
  have "(?v, u) \<notin> (par_rel st)\<^sup>*" if "?v \<notin> seen_abstract (dij_seen st)"
  proof
    assume "(?v, u) \<in> (par_rel st)\<^sup>*"
    thus False
      using that \<open>u \<in> seen_abstract (dij_seen st)\<close>
      by (cases rule: converse_rtranclE) (auto simp: par_rel_def dest: invar_tree_D[OF assms(5)])
  qed
  moreover have "par_rel (dijkstra_upd_relax st) \<subseteq>
      (if ?v \<in> seen_abstract (dij_seen st) then par_rel st else insert (u, ?v) (par_rel st))"
    using 1 assms(2,3)
    by (auto simp: par_rel_def dijkstra_upd_relax_parent)
  ultimately show ?case
    using assms(6)
    by (auto simp: invar_wf_def intro: wf_subset split: if_splits)
qed

lemma invar_wf_holds[invar_holds_intros]:
  assumes "dijkstra_dom st" "invar_1 st" "invar_2 st" "invar_3 st" "invar_4 st" "invar_tree st" "invar_wf st"
  shows "invar_wf (dijkstra st)"
  using assms(2-)
proof(induction rule: dijkstra_induct[OF assms(1)])
  case IH: (1 st)
  show ?case
    apply(rule dijkstra_cases[where st = st])
    by (auto intro!: IH(2-) intro: invar_holds_intros simp: dijkstra_simps[OF IH(1)])
qed

lemma invar_wf_initial[invar_holds_intros]: "invar_wf initial_state"
  by (auto simp: initial_state_def invar_wf_def par_rel_def parent_init_none)


subsubsection \<open>A vertex reached with no parent is a source\<close>

definition "invar_root st \<longleftrightarrow> (\<forall>v. dist_lookup (dij_dist st) v \<noteq> -1 \<longrightarrow> parent_lookup (dij_parent st) v = None \<longrightarrow>
   v \<in> src_abstract srcs)"

lemma invar_root_props[invar_props_elims]:
  "\<lbrakk>invar_root st;
   \<lbrakk>\<And>v. \<lbrakk>dist_lookup (dij_dist st) v \<noteq> -1; parent_lookup (dij_parent st) v = None\<rbrakk> \<Longrightarrow> v \<in> src_abstract srcs\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: invar_root_def)

lemma invar_root_intro[invar_props_intros]:
  "(\<And>v. \<lbrakk>dist_lookup (dij_dist st) v \<noteq> -1; parent_lookup (dij_parent st) v = None\<rbrakk> \<Longrightarrow> v \<in> src_abstract srcs)
   \<Longrightarrow> invar_root st"
  by (auto simp: invar_root_def)

lemma invar_root_holds_done[invar_holds_intros]:
    "\<lbrakk>dijkstra_ret_done_conds st; invar_root st\<rbrakk> \<Longrightarrow> invar_root (dijkstra_ret_done st)"
  and invar_root_holds_skip[invar_holds_intros]:
    "\<lbrakk>dijkstra_call_skip_conds st; invar_root st\<rbrakk> \<Longrightarrow> invar_root (dijkstra_upd_skip st)"
  and invar_root_holds_finish[invar_holds_intros]:
    "\<lbrakk>dijkstra_call_finish_conds st; invar_root st\<rbrakk> \<Longrightarrow> invar_root (dijkstra_upd_finish st)"
  and invar_root_holds_settle[invar_holds_intros]:
    "\<lbrakk>dijkstra_call_settle_conds st; invar_root st\<rbrakk> \<Longrightarrow> invar_root (dijkstra_upd_settle st)"
  and invar_root_holds_found[invar_holds_intros]:
    "\<lbrakk>dijkstra_ret_found_conds st; invar_root st\<rbrakk> \<Longrightarrow> invar_root (dijkstra_ret_found st)"
  by (auto simp: invar_root_def dijkstra_ret_done_def dijkstra_upd_skip_def dijkstra_upd_finish_def
                 dijkstra_upd_settle_def dijkstra_ret_found_def Let_def split: prod.splits)

lemma invar_root_holds_init[invar_holds_intros]:
  "\<lbrakk>dijkstra_call_init_conds st; invar_1 st; invar_3 st; invar_6 st; invar_root st\<rbrakk> \<Longrightarrow> invar_root (dijkstra_upd_init st)"
  by (erule init_branch_facts) (auto simp: invar_root_def invar_6_def dijkstra_upd_init_def insert_source_def)

lemma invar_root_holds_relax[invar_holds_intros]:
  "\<lbrakk>dijkstra_call_relax_conds st; invar_1 st; invar_2 st; invar_root st\<rbrakk> \<Longrightarrow> invar_root (dijkstra_upd_relax st)"
  by (erule relax_edge_facts) (auto simp: invar_root_def dijkstra_upd_relax_dist dijkstra_upd_relax_parent)

lemma invar_root_holds[invar_holds_intros]:
  assumes "dijkstra_dom st" "invar_1 st" "invar_2 st" "invar_3 st" "invar_4 st" "invar_6 st" "invar_root st"
  shows "invar_root (dijkstra st)"
  using assms(2-)
proof(induction rule: dijkstra_induct[OF assms(1)])
  case IH: (1 st)
  show ?case
    apply(rule dijkstra_cases[where st = st])
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
  assumes "invar_wf st" "invar_3 st" "invar_9 st" "invar_tree st" "invar_root st"
  shows "dist_lookup (dij_dist st) v \<noteq> -1 \<Longrightarrow>
     \<exists>s p. build_path st v acc = p @ acc \<and> ag.path_bet p s v \<and> s \<in> src_abstract srcs \<and>
           weight w p = dist_lookup (dij_dist st) v \<and> parent_lookup (dij_parent st) s = None"
proof(induction v arbitrary: acc rule: wf_induct_rule[OF assms(1)[unfolded invar_wf_def]])
  case (1 v)
  show ?case
  proof(cases "parent_lookup (dij_parent st) v")
    case None
    thus ?thesis
      using 1(2) assms(2,3,5)
      by (auto simp: build_path.simps intro!: exI[of _ v] elim!: invar_3_props invar_9_props invar_root_props)
  next
    case (Some e)
    hence "(fst e, v) \<in> par_rel st" "snd e = v" "e \<in> Ea" "dist_lookup (dij_dist st) (fst e) \<noteq> -1"
      "dist_lookup (dij_dist st) v = dist_lookup (dij_dist st) (fst e) + w e"
      using invar_tree_D[OF assms(4)]
      by (auto simp: par_rel_def)
    thus ?thesis
      using 1(1)[of "fst e" "e # acc"] Some ag_path_bet_snocI
      by (fastforce simp: build_path.simps weight_snoc)
  qed
qed

lemma reconstruct_path_correct:
  "\<lbrakk>invar_wf st; invar_3 st; invar_9 st; invar_tree st; invar_root st; dist_lookup (dij_dist st) v \<noteq> -1\<rbrakk>
     \<Longrightarrow> \<exists>s. ag.path_bet (reconstruct_path st v) s v \<and> s \<in> src_abstract srcs \<and>
            weight w (reconstruct_path st v) = dist_lookup (dij_dist st) v"
  using build_path_acc[of st v "[]"]
  by (fastforce simp: reconstruct_path_def)

lemma invar_3_compute: "invar_3 dijkstra_compute"
  and invar_tree_compute: "invar_tree dijkstra_compute"
  and invar_wf_compute: "invar_wf dijkstra_compute"
  and invar_root_compute: "invar_root dijkstra_compute"
  unfolding dijkstra_compute_def
  by (auto intro!: invar_holds_intros)

text \<open>The parent-edge relation of the computed result is well-founded, and @{const reconstruct_path}
      -- a tail-recursive, executable function -- reads off from the parent-edge map, for every
      reached vertex, a concrete source-to-\<open>v\<close> path of weight @{term "dist_lookup (dij_dist
      dijkstra_compute) v"}; by @{thm dijkstra_compute_optimal} this is a genuine shortest path once
      \<open>v\<close> is settled.\<close>

lemma dijkstra_compute_parent_wf: "wf (par_rel dijkstra_compute)"
  using invar_wf_compute
  by (simp add: invar_wf_def)

lemma dijkstra_compute_path:
  "dist_lookup (dij_dist dijkstra_compute) v \<noteq> -1 \<Longrightarrow>
     \<exists>s. ag.path_bet (reconstruct_path dijkstra_compute v) s v \<and> s \<in> src_abstract srcs \<and>
         weight w (reconstruct_path dijkstra_compute v) = dist_lookup (dij_dist dijkstra_compute) v"
  using reconstruct_path_correct[OF invar_wf_compute invar_3_compute invar_9_compute invar_tree_compute
                                   invar_root_compute]
  by blast


end

subsection \<open>Executable version\<close>

partial_function (tailrec) dijkstra_impl where
  "dijkstra_impl st =
     (case dij_curr st of
        Some u \<Rightarrow>
          (if out_has (dij_graph st) u
           then dijkstra_impl (relax_edge u (dist_lookup (dij_dist st) u) (out_current (dij_graph st) u)
                                 (st \<lparr> dij_graph := out_move (dij_graph st) u \<rparr>))
           else dijkstra_impl (st \<lparr> dij_curr := None \<rparr>))
      | None \<Rightarrow>
          (if src_has (dij_srcs st)
           then dijkstra_impl (insert_source (src_current (dij_srcs st)) (st \<lparr> dij_srcs := src_move (dij_srcs st) \<rparr>))
           else (case queue_extract_min (dij_heap st) of
                   (h, None) \<Rightarrow> st \<lparr> dij_heap := h \<rparr>
                 | (h, Some u) \<Rightarrow>
                     (if seen_isin (dij_seen st) u then dijkstra_impl (st \<lparr> dij_heap := h \<rparr>)
                      else if early_stop \<and> target u
                           then st \<lparr> dij_heap := h, dij_seen := seen_insert u (dij_seen st), dij_target := Some u \<rparr>
                           else dijkstra_impl (st \<lparr> dij_heap := h, dij_seen := seen_insert u (dij_seen st),
                                                    dij_curr := Some u, dij_graph := out_reset (dij_graph st) u \<rparr>)))))"

lemma dijkstra_impl_same: "dijkstra_dom st \<Longrightarrow> dijkstra_impl st = dijkstra st"
proof(induction rule: dijkstra.pinduct)
  case (1 st)
  show ?case
    apply(subst dijkstra_impl.simps)
    apply(subst dijkstra.psimps[OF "1"(1)])
    using "1"(2-)
    by(auto split: option.splits prod.splits)
qed

lemmas [code] = dijkstra_impl.simps initial_state_def

end

end