theory Acyclic_Flow
  imports Flow_Theory.Cost_Optimality
       Directed_Set_Graphs.Edge_Iterators
       Data_Structures.Fixed_Univ_Map_Specs
       Data_Structures.Real_Embedding
begin

context
  cost_flow_network
begin

text \<open>A flow is acyclic when no residual cycle is augmenting in both directions.\<close>

definition "acyclic_flow f =
    (\<nexists> C. augpath f C \<and> augpath f (map erev (rev C)) \<and>
          distinct (map oedge C) \<and> fstv (hd C) = sndv (last C)
           \<and> set C \<subseteq> \<EE>)"

lemma acyclic_flowI[intro]:
  "(\<And> C. \<lbrakk>augpath f C; augpath f (map erev (rev C)); distinct (map oedge C);
                fstv (hd C) = sndv (last C); set C \<subseteq> \<EE>\<rbrakk> \<Longrightarrow> False)
                  \<Longrightarrow> acyclic_flow f"
  by (auto simp: acyclic_flow_def)

lemma acyclic_flowE[elim]:
  "\<lbrakk>acyclic_flow f; augpath f C; augpath f (map erev (rev C)); distinct (map oedge C); fstv (hd C) = sndv
    (last C); set C \<subseteq> \<EE>\<rbrakk> \<Longrightarrow> P"
  by (auto simp: acyclic_flow_def)

lemma acyclic_flowD[dest]:
  "\<lbrakk>acyclic_flow f; augpath f C; distinct (map oedge C); fstv (hd C) = sndv (last C); set C \<subseteq>
    \<EE>\<rbrakk> \<Longrightarrow> \<not> augpath f (map erev (rev C))"
  by (auto simp: acyclic_flow_def)

text \<open>Reversing a residual pre-path (edge-wise \<open>erev\<close>, then list reversal) yields a
      pre-path again.\<close>

lemma prepath_erev_rev: "prepath C \<Longrightarrow> prepath (map erev (rev C))"
  using awalk_UNIV_rev[of "fstv (hd C)" "map to_vertex_pair C" "sndv (last C)"]
        rev_prepath_fst_to_lst[of C] rev_prepath_lst_to_fst[of C]
  by (auto simp: prepath_def rev_map to_vertex_pair_erev_swap)

text \<open>General residual bridge: under an acyclic flow there is no closed pre-path all of
      whose arcs are residually free in both directions and whose underlying edges are
      distinct.  This is the abstract source of the free-edge forest property.\<close>

lemma acyclic_no_free_closed_prepath:
  "\<lbrakk>acyclic_flow f; prepath C; (\<And>e. e \<in> set C \<Longrightarrow> 0 < rcap f e); (\<And>e. e \<in> set
    C \<Longrightarrow> 0 < rcap f (erev e)); distinct (map oedge C); fstv (hd C) = sndv (last C); set C \<subseteq>
    \<EE>\<rbrakk> \<Longrightarrow> False"
  using prepath_erev_rev[of C]
  by (auto simp: prepath_def intro!: augpathI Rcap_strictI elim!: acyclic_flowE)

end

section \<open>The DFS-based acyclic-flow procedure\<close>

text \<open>State of the inner DFS-like procedure. Parallel stacks describe the current trail in the
      undirected multigraph of \emph{free} arcs: @{term af_vstack} holds the vertices and, one
      shorter, @{term af_estack} / @{term af_dstack} hold for each non-root vertex the arc it was
      entered by together with the direction that arc was traversed in (@{term True} = with the arc,
      from \<open>fst a\<close> to \<open>snd a\<close>; @{term False} = against it). @{term af_out_arr} / @{term
        af_in_arr}
      are the outgoing / ingoing edge arrays, mapping each vertex to its current edge iterator; the
      array entry of the scanned vertex is advanced in place (via @{term arr_upd}) as arcs are
      consumed, so a vertex resumes where it left off on backtrack.\<close>

text \<open>Three-valued vertex state, replacing the two seen / finished sets: a vertex is @{term Unseen}
      (never explored, or dropped by a truncation), @{term OnStack} (currently on the DFS stack), or
      @{term Finished} (fully explored). Kept in a single @{locale fixed_univ_map}, so classifying a
      neighbour is \emph{one} lookup instead of two set-membership probes.\<close>

datatype vertex_state = Unseen | OnStack | Finished

text \<open>@{term af_unbounded} flags detection of an \emph{unbounded} instance: an infinite-capacity free
      cycle whose only cost-non-increasing cancellation direction has no finite bottleneck (a negative
      infinite cycle). When set, both loops stop and the top-level answer reports unboundedness rather
      than an acyclic flow.\<close>

record ('v, 'e, 'farr, 'arr, 'sarr) AF_DFS_state =
  af_flow      :: "'farr"
  af_vstack    :: "'v list"
  af_estack    :: "'e list"
  af_dstack    :: "bool list"
  af_out_arr   :: "'arr"
  af_in_arr    :: "'arr"
  af_state     :: "'sarr"
  af_unbounded :: "bool"

text \<open>State of the outer loop: the flow being made acyclic, the vertex-state array, and an iterator
      handing out the vertices one by one; plus the unbounded flag.\<close>

record ('v, 'farr, 'sarr, 'vvit, 'arr) AF_state =
  aff_flow      :: "'farr"
  aff_state     :: "'sarr"
  aff_vit       :: "'vvit"
  aff_out_arr   :: "'arr"
  aff_in_arr    :: "'arr"
  aff_unbounded :: "bool"

subsection \<open>Setup for automation\<close>

text \<open>The proof follows the  \<^verbatim>\<open>Directed_Set_Graphs.Pair_Graph_Specs\<close>-based DFS template
      (@{file \<open>../Set_Graphs/Graph_Algorithms/DFS.thy\<close>} and
       @{file \<open>../Set_Graphs/Graph_Algorithms/DFS_Cycles_Aux.thy\<close>}): the recursion is split into
      branch-condition and update functions, invariants are stated with paired
      introduction / elimination rules, and preservation is discharged branch-by-branch through the
      named collections below.\<close>

named_theorems call_cond_elims
named_theorems call_cond_intros
named_theorems ret_holds_intros
named_theorems invar_props_intros
named_theorems invar_props_elims
named_theorems invar_holds_intros
named_theorems state_rel_intros
named_theorems state_rel_holds_intros
named_theorems termination_intros

text \<open>The executable specification locale: fixes the graph-iterator / array / vertex-iterator
      ADT operations and the program constants, with NO assumptions, and holds every executable
      definition of the acyclic-flow procedure.\<close>

locale acyclic_flow_impl_spec =
  fixes out_current   :: "'g \<Rightarrow> 'v \<Rightarrow> 'e" and out_has       :: "'g \<Rightarrow> 'v
    \<Rightarrow> bool"
    and out_move      :: "'g \<Rightarrow> 'v \<Rightarrow> 'g" and out_reset     :: "'g \<Rightarrow> 'v
      \<Rightarrow> 'g"
    and in_current    :: "'g \<Rightarrow> 'v \<Rightarrow> 'e" and in_has        :: "'g \<Rightarrow> 'v
      \<Rightarrow> bool"
    and in_move       :: "'g \<Rightarrow> 'v \<Rightarrow> 'g" and in_reset      :: "'g \<Rightarrow> 'v
      \<Rightarrow> 'g"
    and flow_upd :: "'farr \<Rightarrow> 'e \<Rightarrow> ('n :: linordered_idom) \<Rightarrow> 'farr"
    and flow_lookup :: "'farr \<Rightarrow> 'e \<Rightarrow> 'n"
    and st_upd :: "'sarr \<Rightarrow> 'v \<Rightarrow> vertex_state \<Rightarrow> 'sarr"
    and st_lookup :: "'sarr \<Rightarrow> 'v \<Rightarrow> vertex_state"
    and current_vertex :: "'vvit \<Rightarrow> 'v"
    and has_vertex :: "'vvit \<Rightarrow> bool"
    and move_on_vertex :: "'vvit \<Rightarrow> 'vvit"
    and out_arr in_arr :: "'g"
    and all_vertices :: "'vvit"
    and cap :: "'e \<Rightarrow> 'n"
    and cost :: "'e \<Rightarrow> 'n"
    and state_init :: "'sarr"
    and fst_exec :: "'e \<Rightarrow> 'v"
    and snd_exec :: "'e \<Rightarrow> 'v"
begin
end

text \<open>The proof locale: re-imposes the cost-flow network, the two edge iterators, the two arrays
      and the vertex iterator as genuine ADT contracts, plus the capacity/endpoint/initial-state
      assumptions. All invariants and correctness proofs live here.\<close>

locale acyclic_flow_impl =
  cost_flow_network where fst = "fst :: 'e \<Rightarrow> 'v" and snd = snd+
  real_embedding where h = "h :: 'n \<Rightarrow> real" +
  acyclic_flow_impl_spec where out_current = out_current and flow_lookup = flow_lookup
      and st_lookup = st_lookup and current_vertex = current_vertex +
  bidirectional_iterator where fst = fst and snd = snd
      and out_invar = out_invar and out_abstract = out_abstract
      and out_current = out_current and out_has = out_has
      and out_iterated = out_iterated and out_remaining = out_remaining
      and out_move = out_move and out_reset = out_reset
      and in_invar = in_invar and in_abstract = in_abstract
      and in_current = in_current and in_has = in_has
      and in_iterated = in_iterated and in_remaining = in_remaining
      and in_move = in_move and in_reset = in_reset +
  flow_array: fixed_univ_map where
      K = \<E> and fixed_univ_map_invar = flow_invar
      and fixed_univ_map_upd = flow_upd and fixed_univ_map_lookup = flow_lookup +
  state_arr: fixed_univ_map where
      K = \<V> and fixed_univ_map_invar = st_invar
      and fixed_univ_map_upd = st_upd and fixed_univ_map_lookup = st_lookup +
  vertex_iterator: iterable_set where
      iterable_set_invar = vit_invar and iterable_set_abstract = vit_abstract
      and current_element = current_vertex and has_current = has_vertex
      and iterated = vit_iterated and remaining = vit_remaining
      and move_on = move_on_vertex
    for fst and snd and
     out_current :: "'g \<Rightarrow> 'v \<Rightarrow> 'e" and flow_lookup :: "'farr \<Rightarrow> 'e \<Rightarrow>
       ('n :: linordered_idom)"
    and h :: "'n \<Rightarrow> real"
    and st_lookup :: "'sarr \<Rightarrow> 'v \<Rightarrow> vertex_state" and current_vertex :: "'vvit \<Rightarrow> 'v"
    and out_invar :: "'g \<Rightarrow> bool" and out_abstract :: "'g \<Rightarrow> 'v \<Rightarrow> 'e set"
    and out_iterated :: "'g \<Rightarrow> 'v \<Rightarrow> 'e set" and out_remaining :: "'g \<Rightarrow> 'v
      \<Rightarrow> 'e set"
    and in_invar :: "'g \<Rightarrow> bool" and in_abstract :: "'g \<Rightarrow> 'v \<Rightarrow> 'e set"
    and in_iterated :: "'g \<Rightarrow> 'v \<Rightarrow> 'e set" and in_remaining :: "'g \<Rightarrow> 'v
      \<Rightarrow> 'e set"
    and flow_invar :: "'farr \<Rightarrow> bool" and st_invar :: "'sarr \<Rightarrow> bool"
    and vit_invar :: "'vvit \<Rightarrow> bool" and vit_abstract :: "'vvit \<Rightarrow> 'v set"
    and vit_iterated :: "'vvit \<Rightarrow> 'v set" and vit_remaining :: "'vvit \<Rightarrow> 'v set" +
  assumes cap_encoding: "\<And>e. e \<in> \<E> \<Longrightarrow> (if \<u> e = \<infinity> then cap e = - 1 else \<u> e
    = ereal (h (cap e)))"
      and cost_encoding: "\<And>e. e \<in> \<E> \<Longrightarrow> \<c> e = h (cost e)"
      and state_init_invar: "st_invar state_init"
      and state_init_unseen: "\<And>v. v \<in> \<V> \<Longrightarrow> st_lookup state_init v = Unseen"
      and fst_exec_eq: "\<And>e. e \<in> \<E> \<Longrightarrow> fst_exec e = fst e"
      and snd_exec_eq: "\<And>e. e \<in> \<E> \<Longrightarrow> snd_exec e = snd e"
begin
end

context acyclic_flow_impl_spec begin
declare [[coercion_enabled = false]]

subsection \<open>Free arcs, rooms and costs\<close>

text \<open>The algorithm never inspects the (possibly infinite) capacity @{term \<open>\<u>\<close>} directly;
    instead it
      uses the real program capacity @{term cap}, where an infinite capacity is encoded as @{term \<open>- 1\<close>}
      (justified by \<open>cap_encoding\<close> below). Since @{term \<open>0 \<le> \<u> e\<close>}, a finite capacity
        is never
      @{term \<open>- 1\<close>}, so @{term \<open>- 1\<close>} unambiguously flags ``infinite''.

      An original arc is \emph{free} when its flow value is strictly positive and, if its capacity is
      finite, strictly below it; a free arc can be pushed in both directions.\<close>

definition af_arc_free :: "'farr \<Rightarrow> 'e \<Rightarrow> bool" where
  "af_arc_free fl a \<longleftrightarrow> (let f = flow_lookup fl a; c = cap a in 0 < f \<and> (c = - 1 \<or> f < c))"

text \<open>\emph{Both} directional rooms of an arc from a \emph{single} read of its flow and capacity,
      returned as a pair @{term \<open>(forward, backward)\<close>}: the forward room @{term \<open>cap a - f
        a\<close>} (or
      @{term \<open>- 1\<close>}, i.e.\ unbounded, when the capacity is infinite) and the backward room
      @{term \<open>f a\<close>}. Since a cancellation weighs an arc's room in both orientations, returning both at
      once avoids reading @{term flow_lookup} / @{term cap} twice per arc.\<close>

definition af_rooms :: "'farr \<Rightarrow> 'e \<Rightarrow> 'n \<times> 'n" where
  "af_rooms fl a = (let f = flow_lookup fl a; c = cap a in (if c = - 1 then - 1 else c - f, f))"

text \<open>Marginal cost of pushing one unit along an arc in a direction.\<close>

definition af_delta_cost :: "'e \<Rightarrow> bool \<Rightarrow> 'n" where
  "af_delta_cost a dir = (if dir then cost a else - cost a)"

text \<open>Minimum that treats @{term \<open>- 1\<close>} as ``no bound'' (unbounded room), so it is the neutral
    element.\<close>

definition af_min :: "'n \<Rightarrow> 'n \<Rightarrow> 'n" where
  "af_min x y = (if x = - 1 then y else if y = - 1 then x else min x y)"

text \<open>Push @{term \<gamma>} on one arc and return the updated flow \emph{paired with the new flow value}, so
      a caller can test saturation without reading the value back.\<close>

definition af_push_arc :: "'n \<Rightarrow> 'e \<Rightarrow> bool \<Rightarrow> 'farr \<Rightarrow> 'farr \<times> 'n"
    where
  "af_push_arc \<gamma> a dir fl = (let f = flow_lookup fl a + (if dir then \<gamma> else - \<gamma>) in (flow_upd fl
    a f, f))"

text \<open>Saturation test on an arc's \emph{already-computed} new flow value @{term f}: the negation of
      @{const af_arc_free}, but reading only @{term cap} (not the flow again). Used by the push pass
      to spot the bottleneck without re-reading the value it just wrote.\<close>

definition af_saturated :: "'n \<Rightarrow> 'e \<Rightarrow> bool" where
  "af_saturated f a = (let c = cap a in \<not> (0 < f \<and> (c = - 1 \<or> f < c)))"

text \<open>Fused first pass over the cancellation cycle -- \emph{scan-until-@{term x}}. Rather than take a
      precomputed length, the scan walks the vertex stack @{term vs} in lockstep with the arc / tag
      stacks @{term es} / @{term ds} and \emph{stops on reaching the reached ancestor @{term x}}, thus
      subsuming the old separate depth scan. In one traversal it accumulates (i) the total marginal
      cost along the tags, (ii) the bottleneck room as-is and (iii) flipped. @{const af_min} treats
      @{term \<open>- 1\<close>} as ``unbounded'' (the neutral element for the two room minima). The closing arc is
      folded into the seed by the caller.\<close>

fun af_scan :: "'farr \<Rightarrow> 'v \<Rightarrow> 'v list \<Rightarrow> 'e list \<Rightarrow> bool list
    \<Rightarrow> 'n \<times> 'n \<times> 'n \<Rightarrow> 'n \<times> 'n \<times> 'n" where
  "af_scan fl x (_ # v1 # vs) (a # es) (d # ds) (k, ra, rf) =
     (let (up, dn) = af_rooms fl a;
          acc = (k + af_delta_cost a d, af_min (if d then up else dn) ra, af_min (if d then dn else up) rf)
      in if v1 = x then acc else af_scan fl x (v1 # vs) es ds acc)"
| "af_scan fl x _ _ _ acc = acc"

text \<open>Fused second pass -- push @{term \<gamma>} around the same cycle \emph{and} locate the bottleneck. Each
      cycle arc is pushed once (negating the tag via @{term \<open>d \<noteq> flip\<close>} when flipped); right after
        the
      push the arc is tested for saturation, and the pass returns the flow paired with the \emph{drop
      count} @{term \<open>m'\<close>} = one more than the index of the \emph{deepest} arc that saturated, or
      @{term 0} if none did (only the closing arc). This subsumes the old separate bottleneck-locate
      scan.\<close>

fun af_push :: "'n \<Rightarrow> 'v \<Rightarrow> 'v list \<Rightarrow> 'e list \<Rightarrow> bool list \<Rightarrow>
    bool \<Rightarrow> 'farr \<Rightarrow> 'farr \<times> nat" where
  "af_push \<gamma> x (_ # v1 # vs) (a # es) (d # ds) flip fl =
     (let (fl1, f) = af_push_arc \<gamma> a (d \<noteq> flip) fl
      in if v1 = x then (fl1, if af_saturated f a then 1 else 0)
         else (let (fl2, r) = af_push \<gamma> x (v1 # vs) es ds flip fl1
               in (fl2, if r \<noteq> 0 then Suc r else (if af_saturated f a then 1 else 0))))"
| "af_push \<gamma> x _ _ _ flip fl = (fl, 0)"

text \<open>Cancel a tagged closed cycle of distinct free arcs -- the stack segment from the top down to the
      reached ancestor @{term x} (walked by @{const af_scan} / @{const af_push}, never materialised)
      closed by the arc @{term a} in direction @{term dir} -- returning the post-cancellation flow, the
      truncate-to-bottleneck drop count @{term \<open>m'\<close>}, and an \emph{unbounded} flag. @{const af_scan}
      accumulates the walk cost @{term k} and the two directional bottlenecks @{term ra} (as-is) /
      @{term rf} (flipped); we push in the non-positive-cost orientation (@{term \<open>flip = (0 < k)\<close>}).

      Capacity handling (the infinite-cycle cases). The chosen bottleneck @{term \<gamma>} is @{term \<open>- 1\<close>}
      exactly when that direction is \emph{unbounded} (all its rooms infinite). Then:
      \begin{itemize}
        \item if the walk cost is \emph{zero} and the \emph{other} direction is finite (@{term \<open>rf \<noteq> -
          1\<close>}),
              we cancel in that (equally cost-neutral) finite direction instead -- the flow is
              ``zeroed'' along the cycle;
        \item otherwise the only cost-non-increasing direction is unbounded and has \emph{negative}
              cost: the instance is unbounded, so we push nothing and raise the flag.
      \end{itemize}
      When @{term \<gamma>} is finite this reduces to the ordinary two-pass cancellation.\<close>

definition af_cancel_seg where
  "af_cancel_seg up dn x vs es ds a dir fl =
     (let (k, ra, rf) = af_scan fl x vs es ds
                          (af_delta_cost a dir, (if dir then up else dn), (if dir then dn else up));
          flip = 0 < k;
          \<gamma> = (if flip then rf else ra)
      in if \<gamma> \<noteq> - 1 then
           (let (fl', m') = af_push \<gamma> x vs es ds flip fl;
                (fl'', _) = af_push_arc \<gamma> a (dir \<noteq> flip) fl'
            in (fl'', m', False))
         else if k = 0 \<and> rf \<noteq> - 1 then
           (let (fl', m') = af_push rf x vs es ds True fl;
                (fl'', _) = af_push_arc rf a (dir \<noteq> True) fl'
            in (fl'', m', False))
         else (fl, 0, True))"

subsection \<open>The inner DFS-like procedure\<close>

text \<open>Process one incident free arc @{term a} of the current (top) vertex, already traversed in
      direction @{term dir}; the arc's iterator has already been advanced in @{term st}.
      A self-loop is a length-one defect cancelled on sight; the parent arc is skipped; an arc back
      to a vertex on the stack closes a distinct-arc cycle which is cancelled, the stack truncated
      to the reached vertex, and the iterators of the vertices leaving the stack -- \emph{together
      with the surviving reached vertex} -- are reset (\<open>truncate-and-reset\<close>); any other free arc leads
      to a fresh vertex, which is pushed.\<close>

text \<open>Reset one vertex's two edge iterators to their full, unconsumed state by copying the pristine
      iterators from the \emph{original} arrays @{term out_arr} / @{term in_arr} (never mutated by the
      run). Used on a back-edge cancellation for each \emph{dropped} vertex: it re-enters the
      unexplored world and must re-scan every incident free arc from scratch.\<close>

definition af_reset where
  "af_reset v st = st \<lparr> af_out_arr := out_reset (af_out_arr st) v,
                        af_in_arr  := in_reset (af_in_arr st) v \<rparr>"

text \<open>Fused truncation clean-up: over the first @{term n} (= @{term \<open>m'\<close>}) vertices of the stack --
    the
      ones dropped by truncate-to-bottleneck -- in \emph{one} walk both set the vertex back to
      @{term Unseen} (@{term st_upd}) and reset its iterators (@{const af_reset}). Merges what were two
      separate bounded folds. The surviving endpoint (at index @{term \<open>m'\<close>}) is not touched -- it
      resumes.\<close>

fun af_reset_unsee_seg where
  "af_reset_unsee_seg (Suc n) (v # vs) st =
     af_reset_unsee_seg n vs (af_reset v (st \<lparr> af_state := st_upd (af_state st) v Unseen \<rparr>))"
| "af_reset_unsee_seg _ _ st = st"

text \<open>Cost-directed normalisation of a self-loop arc @{term a} (@{term \<open>fst a = snd a\<close>}).  A
    self-loop
      carries no balance (its two endpoints coincide), so its flow may be driven to whichever bound its
      unit cost prefers without disturbing feasibility: a negative-cost loop is filled to its capacity
      @{term \<open>cap a\<close>} (a negative-cost loop of \emph{infinite} capacity certifies the instance unbounded),
      and \<^emph>\<open>every non-negative-cost loop is emptied\<close>, flow set to @{term 0}.  Emptying a zero-cost
        loop is
      cost-neutral and keeps the flow acyclic, so this needs no residual-room test --- the positive- and
      zero-cost cases coincide.  Unlike the old @{const af_cancel_seg} on-empty-segment treatment this
      fires on \emph{every} scanned self-loop, not only the free ones, so the final flow is
      self-loop-normalised (\<open>\<c> a \<ge> 0 \<Longrightarrow> flow 0\<close>, \<open>\<c> a < 0
        \<Longrightarrow> flow cap\<close>) regardless of the starting bound.\<close>

definition af_selfloop_handle where
  "af_selfloop_handle st a =
     (let fl = af_flow st in
      if cost a < 0 then
         (if cap a = - 1 then st \<lparr> af_unbounded := True \<rparr>
          else if flow_lookup fl a = cap a then st else st \<lparr> af_flow := flow_upd fl a (cap a) \<rparr>)
      else
         (if flow_lookup fl a = 0 then st else st \<lparr> af_flow := flow_upd fl a 0 \<rparr>))"

definition af_handle where
  "af_handle st a dir =
     (if fst_exec a = snd_exec a then af_selfloop_handle st a
      else
        (let (up, dn) = af_rooms (af_flow st) a in
         if \<not> (0 < dn \<and> (up = - 1 \<or> 0 < up)) then st
         else if af_estack st \<noteq> [] \<and> a = hd (af_estack st) then st
         else
           (let x = (if dir then snd_exec a else fst_exec a) in
            case st_lookup (af_state st) x of
              Finished \<Rightarrow> st
            | OnStack \<Rightarrow>
                (let (fl, m', ubd) = af_cancel_seg up dn x (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow
                  st)
                 in if ubd then st \<lparr> af_unbounded := True \<rparr>
                    else af_reset_unsee_seg m' (af_vstack st)
                           (st \<lparr> af_flow := fl,
                                 af_vstack := drop m' (af_vstack st),
                                 af_estack := drop m' (af_estack st),
                                 af_dstack := drop m' (af_dstack st) \<rparr>))
            | Unseen \<Rightarrow>
                st \<lparr> af_vstack := x # af_vstack st,
                     af_state := st_upd (af_state st) x OnStack,
                     af_estack := a # af_estack st,
                     af_dstack := dir # af_dstack st \<rparr>)))"

function (domintros) AF_DFS where
  "AF_DFS st =
     (if af_unbounded st then st else
      case af_vstack st of
        [] \<Rightarrow> st
      | v # vs \<Rightarrow>
         if out_has (af_out_arr st) v then
           AF_DFS (af_handle (st \<lparr> af_out_arr := out_move (af_out_arr st) v \<rparr>)
                             (out_current (af_out_arr st) v) True)
         else
           if in_has (af_in_arr st) v then
              AF_DFS (af_handle (st \<lparr> af_in_arr := in_move (af_in_arr st) v \<rparr>)
                                (in_current (af_in_arr st) v) False)
           else
              AF_DFS (st \<lparr> af_vstack := vs,
                           af_state := st_upd (af_state st) v Finished,
                           af_estack := tl (af_estack st),
                           af_dstack := tl (af_dstack st) \<rparr>))"
  by pat_completeness auto

partial_function (tailrec) AF_DFS_impl where
  "AF_DFS_impl st =
     (if af_unbounded st then st else
      case af_vstack st of
        [] \<Rightarrow> st
      | v # vs \<Rightarrow>
         if out_has (af_out_arr st) v then
           AF_DFS_impl (af_handle (st \<lparr> af_out_arr := out_move (af_out_arr st) v \<rparr>)
                                  (out_current (af_out_arr st) v) True)
         else
           if in_has (af_in_arr st) v then
              AF_DFS_impl (af_handle (st \<lparr> af_in_arr := in_move (af_in_arr st) v \<rparr>)
                                     (in_current (af_in_arr st) v) False)
           else
              AF_DFS_impl (st \<lparr> af_vstack := vs,
                                af_state := st_upd (af_state st) v Finished,
                                af_estack := tl (af_estack st),
                                af_dstack := tl (af_dstack st) \<rparr>))"

definition AF_DFS_initial where
  "AF_DFS_initial fl oa ia stt s =
     \<lparr> af_flow = fl,
       af_vstack = [s],
       af_estack = [],
       af_dstack = [],
       af_out_arr = oa,
       af_in_arr = ia,
       af_state = st_upd stt s OnStack,
       af_unbounded = False \<rparr>"

subsubsection \<open>Control-flow decomposition\<close>

text \<open>The inner recursion is split into three recursive branches -- advance along an outgoing free
      arc (\<open>T-out\<close>), advance along an ingoing one (\<open>T-in\<close>), or backtrack
        (\<open>T-pop\<close>) -- and one return
      branch (empty stack). The six-way dispatch inside @{const af_handle} lives entirely inside the
      update functions of the two advancing branches, exactly as neighbour selection lives inside
       \<^verbatim>\<open>DFS_upd1\<close> in the DFS template.\<close>

definition "AF_DFS_call_1_conds st =
   (\<not> af_unbounded st \<and>
    (case af_vstack st of v # vs \<Rightarrow> out_has (af_out_arr st) v | [] \<Rightarrow> False))"

definition "AF_DFS_upd1 st =
   (let v = hd (af_vstack st) in
    af_handle (st \<lparr> af_out_arr := out_move (af_out_arr st) v \<rparr>)
              (out_current (af_out_arr st) v) True)"

definition "AF_DFS_call_2_conds st =
   (\<not> af_unbounded st \<and>
    (case af_vstack st of
       v # vs \<Rightarrow> \<not> out_has (af_out_arr st) v \<and> in_has (af_in_arr st) v
     | [] \<Rightarrow> False))"

definition "AF_DFS_upd2 st =
   (let v = hd (af_vstack st) in
    af_handle (st \<lparr> af_in_arr := in_move (af_in_arr st) v \<rparr>)
              (in_current (af_in_arr st) v) False)"

definition "AF_DFS_call_3_conds st =
   (\<not> af_unbounded st \<and>
    (case af_vstack st of
       v # vs \<Rightarrow> \<not> out_has (af_out_arr st) v \<and> \<not> in_has (af_in_arr st) v
     | [] \<Rightarrow> False))"

definition "AF_DFS_upd3 st =
   st \<lparr> af_vstack := tl (af_vstack st),
        af_state := st_upd (af_state st) (hd (af_vstack st)) Finished,
        af_estack := tl (af_estack st),
        af_dstack := tl (af_dstack st) \<rparr>"

definition "AF_DFS_ret_conds st =
  (af_unbounded st \<or> (case af_vstack st of v # vs \<Rightarrow> False | [] \<Rightarrow> True))"

definition "AF_DFS_ret st = st"

subsection \<open>The outer loop over vertices\<close>

text \<open>Hand out the vertices one by one through the vertex iterator; whenever a vertex has not yet
      been explored, launch the inner DFS-like procedure from it, threading the (updated) flow and
      seen set on.\<close>

function (domintros) AF_outer where
  "AF_outer st =
     (if aff_unbounded st then st
      else if has_vertex (aff_vit st) then
        (let v = current_vertex (aff_vit st);
             st1 = st \<lparr> aff_vit := move_on_vertex (aff_vit st) \<rparr>
         in if st_lookup (aff_state st) v \<noteq> Unseen then AF_outer st1
            else (let res = AF_DFS (AF_DFS_initial (aff_flow st) (aff_out_arr st) (aff_in_arr st)
                                       (aff_state st) v)
                  in AF_outer (st1 \<lparr> aff_flow := af_flow res, aff_state := af_state res,
                                     aff_out_arr := af_out_arr res, aff_in_arr := af_in_arr res,
                                     aff_unbounded := af_unbounded res \<rparr>)))
      else st)"
  by pat_completeness auto

partial_function (tailrec) AF_outer_impl where
  "AF_outer_impl st =
     (if aff_unbounded st then st
      else if has_vertex (aff_vit st) then
        (let v = current_vertex (aff_vit st);
             st1 = st \<lparr> aff_vit := move_on_vertex (aff_vit st) \<rparr>
         in if st_lookup (aff_state st) v \<noteq> Unseen then AF_outer_impl st1
            else (let res = AF_DFS_impl (AF_DFS_initial (aff_flow st) (aff_out_arr st) (aff_in_arr st)
                                            (aff_state st) v)
                  in AF_outer_impl (st1 \<lparr> aff_flow := af_flow res, aff_state := af_state res,
                                          aff_out_arr := af_out_arr res, aff_in_arr := af_in_arr res,
                                          aff_unbounded := af_unbounded res \<rparr>)))
      else st)"

definition AF_outer_initial where
  "AF_outer_initial f0 =
     \<lparr> aff_flow = f0, aff_state = state_init, aff_vit = all_vertices,
       aff_out_arr = out_arr, aff_in_arr = in_arr, aff_unbounded = False \<rparr>"

subsubsection \<open>Control-flow decomposition of the outer loop\<close>

text \<open>Two recursive branches -- skip an already-explored vertex (\<open>call_1\<close>) or launch the inner DFS
      from an unseen one and thread its result back (\<open>call_2\<close>) -- and one return branch (iterator
      exhausted).\<close>

definition "AF_outer_call_1_conds st =
   (\<not> aff_unbounded st \<and> has_vertex (aff_vit st) \<and>
    st_lookup (aff_state st) (current_vertex (aff_vit st)) \<noteq> Unseen)"

definition "AF_outer_upd1 st = st \<lparr> aff_vit := move_on_vertex (aff_vit st) \<rparr>"

definition "AF_outer_call_2_conds st =
   (\<not> aff_unbounded st \<and> has_vertex (aff_vit st) \<and>
    st_lookup (aff_state st) (current_vertex (aff_vit st)) = Unseen)"

definition "AF_outer_upd2 st =
   (let v = current_vertex (aff_vit st);
        st1 = st \<lparr> aff_vit := move_on_vertex (aff_vit st) \<rparr>;
        res = AF_DFS (AF_DFS_initial (aff_flow st) (aff_out_arr st) (aff_in_arr st) (aff_state st) v)
    in st1 \<lparr> aff_flow := af_flow res, aff_state := af_state res,
             aff_out_arr := af_out_arr res, aff_in_arr := af_in_arr res,
             aff_unbounded := af_unbounded res \<rparr>)"

definition "AF_outer_ret_conds st = (aff_unbounded st \<or> \<not> has_vertex (aff_vit st))"

definition "AF_outer_ret st = st"

text \<open>Top-level entry point: make the flow @{term f0} acyclic.\<close>

text \<open>Top-level result as an @{type option}: @{term None} signals an \emph{unbounded} instance (a
      negative infinite-capacity free cycle was found), otherwise @{term \<open>Some f'\<close>} with @{term
        \<open>f'\<close>}
      the acyclic flow of no-greater cost.\<close>

definition make_acyclic :: "'farr \<Rightarrow> 'farr option" where
  "make_acyclic f0 =
     (let res = AF_outer (AF_outer_initial f0)
      in if aff_unbounded res then None else Some (aff_flow res))"

definition make_acyclic_impl :: "'farr \<Rightarrow> 'farr option" where
  "make_acyclic_impl f0 =
     (let res = AF_outer_impl (AF_outer_initial f0)
      in if aff_unbounded res then None else Some (aff_flow res))"

text \<open>The @{command partial_function} equations are not code equations by default (unlike @{command fun}
      / @{command definition}); register them so that, after a @{command global_interpretation} with
      executable data-structure operations, @{const make_acyclic_impl} is code-generatable.\<close>

lemmas [code] = AF_DFS_impl.simps AF_outer_impl.simps

end

context acyclic_flow_impl begin
declare [[coercion_enabled = false]]

text \<open>Bridges between the executable @{typ 'n}-valued program data (@{term cost}, @{term cap}) and the
      real specification data (@{term \<c>}, @{term \<u>}), via the embedding @{term h}. Because @{term h} is
      an order-embedding ring homomorphism, the sign tests the algorithm performs on @{term cost} agree
      with the sign tests the specification phrases on @{term \<c>}.\<close>

lemma cost_neg_bridge:  "a \<in> \<E> \<Longrightarrow> (cost a < 0) = (\<c> a < 0)"
  using cost_encoding
  by simp
lemma cost_nonneg_bridge: "a \<in> \<E> \<Longrightarrow> (0 \<le> cost a) = (0 \<le> \<c> a)"
  using cost_encoding
  by simp
lemma cost_pos_bridge:  "a \<in> \<E> \<Longrightarrow> (0 < cost a) = (0 < \<c> a)"
  using cost_encoding
  by simp
lemma cost_h: "a \<in> \<E> \<Longrightarrow> h (cost a) = \<c> a"
  using cost_encoding
  by simp

lemma cap_infinite_bridge: "a \<in> \<E> \<Longrightarrow> (cap a = - 1) = (\<u> a = \<infinity>)"
  using cap_encoding[of a] u_non_neg[of a]
  by (cases "\<u> a = \<infinity>") (auto simp: zero_ereal_def)
lemma cap_finite_h: "\<lbrakk>a \<in> \<E>; \<u> a \<noteq> \<infinity>\<rbrakk> \<Longrightarrow> ereal (h (cap a)) =
    \<u> a"
  using cap_encoding[of a]
  by (auto split: if_splits)

definition "multigraph_inv oa ia \<longleftrightarrow> out_graph_inv oa \<and> in_graph_inv ia"

lemma af_handle_real:
  "a \<in> \<E> \<Longrightarrow> af_handle st a dir =
     (if fst a = snd a then af_selfloop_handle st a
      else
        (let (up, dn) = af_rooms (af_flow st) a in
         if \<not> (0 < dn \<and> (up = - 1 \<or> 0 < up)) then st
         else if af_estack st \<noteq> [] \<and> a = hd (af_estack st) then st
         else
           (let x = (if dir then snd a else fst a) in
            case st_lookup (af_state st) x of
              Finished \<Rightarrow> st
            | OnStack \<Rightarrow>
                (let (fl, m', ubd) = af_cancel_seg up dn x (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow
                  st)
                 in if ubd then st \<lparr> af_unbounded := True \<rparr>
                    else af_reset_unsee_seg m' (af_vstack st)
                           (st \<lparr> af_flow := fl,
                                 af_vstack := drop m' (af_vstack st),
                                 af_estack := drop m' (af_estack st),
                                 af_dstack := drop m' (af_dstack st) \<rparr>))
            | Unseen \<Rightarrow>
                st \<lparr> af_vstack := x # af_vstack st,
                     af_state := st_upd (af_state st) x OnStack,
                     af_estack := a # af_estack st,
                     af_dstack := dir # af_dstack st \<rparr>)))"
  by (simp only: af_handle_def fst_exec_eq snd_exec_eq)

text \<open>The six outcomes of @{const af_handle}, as one case distinction.\<close>

lemma af_handle_cases_exec[case_names selfloop blocked parent finished push unbounded cancel]:
  obtains "fst_exec a = snd_exec a" "af_handle st a dir = af_selfloop_handle st a"
  | up dn where "fst_exec a \<noteq> snd_exec a" "af_rooms (af_flow st) a = (up, dn)"
      "\<not> (0 < dn \<and> (up = - 1 \<or> 0 < up))" "af_handle st a dir = st"
  | up dn where "fst_exec a \<noteq> snd_exec a" "af_rooms (af_flow st) a = (up, dn)"
      "0 < dn \<and> (up = - 1 \<or> 0 < up)" "af_estack st \<noteq> []" "a = hd (af_estack st)"
      "af_handle st a dir = st"
  | up dn where "fst_exec a \<noteq> snd_exec a" "af_rooms (af_flow st) a = (up, dn)"
      "0 < dn \<and> (up = - 1 \<or> 0 < up)" "\<not> (af_estack st \<noteq> [] \<and> a = hd (af_estack st))"
      "st_lookup (af_state st) (if dir then snd_exec a else fst_exec a) = Finished"
      "af_handle st a dir = st"
  | up dn where "fst_exec a \<noteq> snd_exec a" "af_rooms (af_flow st) a = (up, dn)"
      "0 < dn \<and> (up = - 1 \<or> 0 < up)" "\<not> (af_estack st \<noteq> [] \<and> a = hd (af_estack st))"
      "st_lookup (af_state st) (if dir then snd_exec a else fst_exec a) = Unseen"
      "af_handle st a dir =
         st\<lparr>af_vstack := (if dir then snd_exec a else fst_exec a) # af_vstack st,
            af_state := st_upd (af_state st) (if dir then snd_exec a else fst_exec a) OnStack,
            af_estack := a # af_estack st, af_dstack := dir # af_dstack st\<rparr>"
  | up dn fl m' where "fst_exec a \<noteq> snd_exec a" "af_rooms (af_flow st) a = (up, dn)"
      "0 < dn \<and> (up = - 1 \<or> 0 < up)" "\<not> (af_estack st \<noteq> [] \<and> a = hd (af_estack st))"
      "st_lookup (af_state st) (if dir then snd_exec a else fst_exec a) = OnStack"
      "af_cancel_seg up dn (if dir then snd_exec a else fst_exec a) (af_vstack st) (af_estack st)
         (af_dstack st) a dir (af_flow st) = (fl, m', True)"
      "af_handle st a dir = st\<lparr>af_unbounded := True\<rparr>"
  | up dn fl m' where "fst_exec a \<noteq> snd_exec a" "af_rooms (af_flow st) a = (up, dn)"
      "0 < dn \<and> (up = - 1 \<or> 0 < up)" "\<not> (af_estack st \<noteq> [] \<and> a = hd (af_estack st))"
      "st_lookup (af_state st) (if dir then snd_exec a else fst_exec a) = OnStack"
      "af_cancel_seg up dn (if dir then snd_exec a else fst_exec a) (af_vstack st) (af_estack st)
         (af_dstack st) a dir (af_flow st) = (fl, m', False)"
      "af_handle st a dir =
         af_reset_unsee_seg m' (af_vstack st)
           (st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st),
               af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>)"
proof-
  obtain up dn where r: "af_rooms (af_flow st) a = (up, dn)"
    by fastforce
  obtain fl m' ubd where c: "af_cancel_seg up dn (if dir then snd_exec a else fst_exec a)
      (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) = (fl, m', ubd)"
    by (rule prod_cases3)
  note h = af_handle_def[of st a dir]
  show thesis
  proof(cases "fst_exec a = snd_exec a")
    case True
    thus thesis
      using h
      by (intro that(1)) simp_all
  next
    case nl: False
    show thesis
    proof(cases "0 < dn \<and> (up = - 1 \<or> 0 < up)")
      case False
      thus thesis
        using nl r h
        by (intro that(2)[of up dn]) simp_all
    next
      case g: True
      show thesis
      proof(cases "af_estack st \<noteq> [] \<and> a = hd (af_estack st)")
        case True
        thus thesis
          using nl r g h
          by (intro that(3)[of up dn]) simp_all
      next
        case p: False
        show thesis
        proof(cases "st_lookup (af_state st) (if dir then snd_exec a else fst_exec a)")
          case Unseen
          thus thesis
            using nl r g p
            by (intro that(5)[of up dn]) (auto simp: h Let_def)
        next
          case OnStack
          show thesis
          proof(cases ubd)
            case True
            thus thesis
              using nl r g p c OnStack
              by (intro that(6)[of up dn fl m']) (auto simp: h Let_def)
          next
            case False
            thus thesis
              using nl r g p c OnStack
              by (intro that(7)[of up dn fl m']) (auto simp: h Let_def)
          qed
        next
          case Finished
          thus thesis
            using nl r g p
            by (intro that(4)[of up dn]) (auto simp: h Let_def)
        qed
      qed
    qed
  qed
qed

lemma af_handle_cases[consumes 1, case_names selfloop blocked parent finished push unbounded cancel]:
  assumes "a \<in> \<E>"
  obtains "fst a = snd a" "af_handle st a dir = af_selfloop_handle st a"
  | up dn where "fst a \<noteq> snd a" "af_rooms (af_flow st) a = (up, dn)"
      "\<not> (0 < dn \<and> (up = - 1 \<or> 0 < up))" "af_handle st a dir = st"
  | up dn where "fst a \<noteq> snd a" "af_rooms (af_flow st) a = (up, dn)"
      "0 < dn \<and> (up = - 1 \<or> 0 < up)" "af_estack st \<noteq> []" "a = hd (af_estack st)"
      "af_handle st a dir = st"
  | up dn where "fst a \<noteq> snd a" "af_rooms (af_flow st) a = (up, dn)"
      "0 < dn \<and> (up = - 1 \<or> 0 < up)" "\<not> (af_estack st \<noteq> [] \<and> a = hd (af_estack st))"
      "st_lookup (af_state st) (if dir then snd a else fst a) = Finished" "af_handle st a dir = st"
  | up dn where "fst a \<noteq> snd a" "af_rooms (af_flow st) a = (up, dn)"
      "0 < dn \<and> (up = - 1 \<or> 0 < up)" "\<not> (af_estack st \<noteq> [] \<and> a = hd (af_estack st))"
      "st_lookup (af_state st) (if dir then snd a else fst a) = Unseen"
      "af_handle st a dir =
         st\<lparr>af_vstack := (if dir then snd a else fst a) # af_vstack st,
            af_state := st_upd (af_state st) (if dir then snd a else fst a) OnStack,
            af_estack := a # af_estack st, af_dstack := dir # af_dstack st\<rparr>"
  | up dn fl m' where "fst a \<noteq> snd a" "af_rooms (af_flow st) a = (up, dn)"
      "0 < dn \<and> (up = - 1 \<or> 0 < up)" "\<not> (af_estack st \<noteq> [] \<and> a = hd (af_estack st))"
      "st_lookup (af_state st) (if dir then snd a else fst a) = OnStack"
      "af_cancel_seg up dn (if dir then snd a else fst a) (af_vstack st) (af_estack st)
         (af_dstack st) a dir (af_flow st) = (fl, m', True)"
      "af_handle st a dir = st\<lparr>af_unbounded := True\<rparr>"
  | up dn fl m' where "fst a \<noteq> snd a" "af_rooms (af_flow st) a = (up, dn)"
      "0 < dn \<and> (up = - 1 \<or> 0 < up)" "\<not> (af_estack st \<noteq> [] \<and> a = hd (af_estack st))"
      "st_lookup (af_state st) (if dir then snd a else fst a) = OnStack"
      "af_cancel_seg up dn (if dir then snd a else fst a) (af_vstack st) (af_estack st)
         (af_dstack st) a dir (af_flow st) = (fl, m', False)"
      "af_handle st a dir =
         af_reset_unsee_seg m' (af_vstack st)
           (st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st),
               af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>)"
  by (rule af_handle_cases_exec[of a st dir]; insert assms;
      simp only: fst_exec_eq snd_exec_eq; (blast intro: that))

lemma AF_DFS_call_1_conds[call_cond_elims]:
  "\<lbrakk>AF_DFS_call_1_conds st;
    \<lbrakk>\<not> af_unbounded st; \<exists>v vs. af_vstack st = v # vs;
     out_has (af_out_arr st) (hd (af_vstack st))\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: AF_DFS_call_1_conds_def split: list.splits)

lemma AF_DFS_call_2_conds[call_cond_elims]:
  "\<lbrakk>AF_DFS_call_2_conds st;
    \<lbrakk>\<not> af_unbounded st; \<exists>v vs. af_vstack st = v # vs;
     \<not> out_has (af_out_arr st) (hd (af_vstack st));
     in_has (af_in_arr st) (hd (af_vstack st))\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: AF_DFS_call_2_conds_def split: list.splits)

lemma AF_DFS_call_3_conds[call_cond_elims]:
  "\<lbrakk>AF_DFS_call_3_conds st;
    \<lbrakk>\<not> af_unbounded st; \<exists>v vs. af_vstack st = v # vs;
     \<not> out_has (af_out_arr st) (hd (af_vstack st));
     \<not> in_has (af_in_arr st) (hd (af_vstack st))\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: AF_DFS_call_3_conds_def split: list.splits)

lemma AF_DFS_ret_conds[call_cond_elims]:
  "\<lbrakk>AF_DFS_ret_conds st; af_unbounded st \<or> af_vstack st = [] \<Longrightarrow> P\<rbrakk>
    \<Longrightarrow> P"
  by (auto simp: AF_DFS_ret_conds_def split: list.splits)

lemma AF_DFS_ret_condsI[call_cond_intros]:
  "af_unbounded st \<or> af_vstack st = [] \<Longrightarrow> AF_DFS_ret_conds st"
  by (auto simp: AF_DFS_ret_conds_def split: list.splits)

lemma AF_DFS_cases:
  "\<lbrakk>(AF_DFS_call_1_conds st \<Longrightarrow> P); (AF_DFS_call_2_conds st \<Longrightarrow> P);
    (AF_DFS_call_3_conds st \<Longrightarrow> P); (AF_DFS_ret_conds st \<Longrightarrow> P)\<rbrakk> \<Longrightarrow>
    P"
  by (cases "af_vstack st"; (auto simp: AF_DFS_call_1_conds_def AF_DFS_call_2_conds_def
       AF_DFS_call_3_conds_def AF_DFS_ret_conds_def))

lemma AF_DFS_simps:
  assumes "AF_DFS_dom st"
  shows "AF_DFS_call_1_conds st \<Longrightarrow> AF_DFS st = AF_DFS (AF_DFS_upd1 st)"
        "AF_DFS_call_2_conds st \<Longrightarrow> AF_DFS st = AF_DFS (AF_DFS_upd2 st)"
        "AF_DFS_call_3_conds st \<Longrightarrow> AF_DFS st = AF_DFS (AF_DFS_upd3 st)"
        "AF_DFS_ret_conds st \<Longrightarrow> AF_DFS st = AF_DFS_ret st"
  by (auto simp add: AF_DFS.psimps[OF assms] Let_def
                     AF_DFS_call_1_conds_def AF_DFS_upd1_def
                     AF_DFS_call_2_conds_def AF_DFS_upd2_def
                     AF_DFS_call_3_conds_def AF_DFS_upd3_def
                     AF_DFS_ret_conds_def AF_DFS_ret_def
           split: list.splits if_splits)

lemma AF_DFS_induct:
  assumes "AF_DFS_dom st"
  assumes "\<And>st. \<lbrakk>AF_DFS_dom st;
                 AF_DFS_call_1_conds st \<Longrightarrow> P (AF_DFS_upd1 st);
                 AF_DFS_call_2_conds st \<Longrightarrow> P (AF_DFS_upd2 st);
                 AF_DFS_call_3_conds st \<Longrightarrow> P (AF_DFS_upd3 st)\<rbrakk> \<Longrightarrow> P st"
  shows "P st"
  apply(rule AF_DFS.pinduct[OF assms(1)])
  apply(rule assms(2)[simplified AF_DFS_call_1_conds_def AF_DFS_upd1_def
                                 AF_DFS_call_2_conds_def AF_DFS_upd2_def
                                 AF_DFS_call_3_conds_def AF_DFS_upd3_def])
  by (auto simp: Let_def split: list.splits if_splits)

lemma AF_DFS_domintros:
  assumes "AF_DFS_call_1_conds st \<Longrightarrow> AF_DFS_dom (AF_DFS_upd1 st)"
  assumes "AF_DFS_call_2_conds st \<Longrightarrow> AF_DFS_dom (AF_DFS_upd2 st)"
  assumes "AF_DFS_call_3_conds st \<Longrightarrow> AF_DFS_dom (AF_DFS_upd3 st)"
  shows "AF_DFS_dom st"
  apply(rule AF_DFS.domintros)
  using assms(1)[simplified AF_DFS_call_1_conds_def AF_DFS_upd1_def]
        assms(2)[simplified AF_DFS_call_2_conds_def AF_DFS_upd2_def]
        assms(3)[simplified AF_DFS_call_3_conds_def AF_DFS_upd3_def]
  by (force simp: Let_def split: list.splits if_splits)+

lemma AF_outer_call_1_conds[call_cond_elims]:
  "\<lbrakk>AF_outer_call_1_conds st;
    \<lbrakk>\<not> aff_unbounded st; has_vertex (aff_vit st);
     st_lookup (aff_state st) (current_vertex (aff_vit st)) \<noteq> Unseen\<rbrakk> \<Longrightarrow> P\<rbrakk>
       \<Longrightarrow> P"
  by (auto simp: AF_outer_call_1_conds_def)

lemma AF_outer_call_2_conds[call_cond_elims]:
  "\<lbrakk>AF_outer_call_2_conds st;
    \<lbrakk>\<not> aff_unbounded st; has_vertex (aff_vit st);
     st_lookup (aff_state st) (current_vertex (aff_vit st)) = Unseen\<rbrakk> \<Longrightarrow> P\<rbrakk>
       \<Longrightarrow> P"
  by (auto simp: AF_outer_call_2_conds_def)

lemma AF_outer_ret_conds[call_cond_elims]:
  "\<lbrakk>AF_outer_ret_conds st; aff_unbounded st \<or> \<not> has_vertex (aff_vit st) \<Longrightarrow> P\<rbrakk>
    \<Longrightarrow> P"
  by (auto simp: AF_outer_ret_conds_def)

lemma AF_outer_cases:
  "\<lbrakk>(AF_outer_call_1_conds st \<Longrightarrow> P); (AF_outer_call_2_conds st \<Longrightarrow> P);
    (AF_outer_ret_conds st \<Longrightarrow> P)\<rbrakk> \<Longrightarrow> P"
  by (auto simp: AF_outer_call_1_conds_def AF_outer_call_2_conds_def AF_outer_ret_conds_def)

lemma AF_outer_simps:
  assumes "AF_outer_dom st"
  shows "AF_outer_call_1_conds st \<Longrightarrow> AF_outer st = AF_outer (AF_outer_upd1 st)"
        "AF_outer_call_2_conds st \<Longrightarrow> AF_outer st = AF_outer (AF_outer_upd2 st)"
        "AF_outer_ret_conds st \<Longrightarrow> AF_outer st = AF_outer_ret st"
  by (auto simp add: AF_outer.psimps[OF assms] Let_def
                     AF_outer_call_1_conds_def AF_outer_upd1_def
                     AF_outer_call_2_conds_def AF_outer_upd2_def
                     AF_outer_ret_conds_def AF_outer_ret_def
           split: if_splits)

lemma AF_outer_induct:
  assumes "AF_outer_dom st"
  assumes "\<And>st. \<lbrakk>AF_outer_dom st;
                 AF_outer_call_1_conds st \<Longrightarrow> P (AF_outer_upd1 st);
                 AF_outer_call_2_conds st \<Longrightarrow> P (AF_outer_upd2 st)\<rbrakk> \<Longrightarrow> P st"
  shows "P st"
  apply(rule AF_outer.pinduct[OF assms(1)])
  apply(rule assms(2)[simplified AF_outer_call_1_conds_def AF_outer_upd1_def
                                 AF_outer_call_2_conds_def AF_outer_upd2_def])
  by (auto simp: Let_def split: if_splits)

lemma AF_outer_domintros:
  assumes "AF_outer_call_1_conds st \<Longrightarrow> AF_outer_dom (AF_outer_upd1 st)"
  assumes "AF_outer_call_2_conds st \<Longrightarrow> AF_outer_dom (AF_outer_upd2 st)"
  shows "AF_outer_dom st"
  apply(rule AF_outer.domintros)
  using assms(1)[simplified AF_outer_call_1_conds_def AF_outer_upd1_def]
        assms(2)[simplified AF_outer_call_2_conds_def AF_outer_upd2_def]
  by (force simp: Let_def split: if_splits)+

section \<open>Invariants and partial correctness\<close>

text \<open>Following the DFS template, the correctness argument is carried by a conjunction of invariants,
      each proved preserved branch-by-branch. We begin with Theme A --- data-structure
      well-formedness.\<close>

text \<open>Three bridge facts specialising the @{thm fixed_univ_map.fixed_univ_map_upd_invar} axiom to the
      flow, vertex-state and edge arrays of this locale.\<close>

lemma flow_upd_invar: "\<lbrakk>flow_invar A; k\<in> \<E>\<rbrakk>
 \<Longrightarrow> flow_invar (flow_upd A k v)"
  by (rule flow_array.fixed_univ_map_upd_invar)

subsection \<open>Properties of the self-loop normaliser\<close>

lemma af_selfloop_handle_proj[simp]:
  "af_out_arr (af_selfloop_handle st a) = af_out_arr st"
  "af_in_arr (af_selfloop_handle st a) = af_in_arr st"
  "af_vstack (af_selfloop_handle st a) = af_vstack st"
  "af_estack (af_selfloop_handle st a) = af_estack st"
  "af_dstack (af_selfloop_handle st a) = af_dstack st"
  "af_state (af_selfloop_handle st a) = af_state st"
  by (auto simp: af_selfloop_handle_def Let_def split: if_splits prod.splits)

lemma af_selfloop_handle_flow_cases:
  "af_flow (af_selfloop_handle st a) = af_flow st
   \<or> af_flow (af_selfloop_handle st a) = flow_upd (af_flow st) a 0
   \<or> af_flow (af_selfloop_handle st a) = flow_upd (af_flow st) a (cap a)"
  by (auto simp: af_selfloop_handle_def Let_def split: if_splits prod.splits)

lemma af_selfloop_handle_flow_invar:
  "\<lbrakk>a \<in> \<E>; flow_invar (af_flow st)\<rbrakk> \<Longrightarrow> flow_invar (af_flow (af_selfloop_handle
    st a))"
  using af_selfloop_handle_flow_cases[of st a]
  by (auto intro: flow_upd_invar)

lemma af_selfloop_handle_unbounded:
  "a \<in> \<E> \<Longrightarrow> af_unbounded (af_selfloop_handle st a) = (af_unbounded st \<or> (\<c> a < 0 \<and>
    cap a = - 1))"
  by (auto simp: af_selfloop_handle_def Let_def cost_neg_bridge split: if_splits prod.splits)

lemma af_selfloop_handle_flow_off:
  "\<lbrakk>a \<in> \<E>; flow_invar (af_flow st); b \<noteq> a\<rbrakk> \<Longrightarrow> flow_lookup (af_flow
    (af_selfloop_handle st a)) b = flow_lookup (af_flow st) b"
  using af_selfloop_handle_flow_cases[of st a]
  by (auto simp: flow_array.fixed_univ_map_upd)

lemma af_selfloop_handle_norm:
  "\<lbrakk>a \<in> \<E>; flow_invar (af_flow st); \<not> af_unbounded (af_selfloop_handle st a)\<rbrakk>
    \<Longrightarrow> (0 \<le> \<c> a \<longrightarrow> flow_lookup (af_flow (af_selfloop_handle st a)) a = 0)
       \<and> (\<c> a < 0 \<longrightarrow> cap a \<noteq> - 1 \<and> flow_lookup (af_flow (af_selfloop_handle st a))
         a = cap a)"
  using af_selfloop_handle_unbounded[of a st]
  by (auto simp: af_selfloop_handle_def Let_def cost_neg_bridge flow_array.fixed_univ_map_upd split: if_splits)

lemma af_selfloop_handle_notfree:
  "\<lbrakk>a \<in> \<E>; flow_invar (af_flow st); \<not> af_unbounded (af_selfloop_handle st a)\<rbrakk>
   \<Longrightarrow> \<not> af_arc_free (af_flow (af_selfloop_handle st a)) a"
  using af_selfloop_handle_norm[of a st]
  by (cases "\<c> a < 0") (auto simp: af_arc_free_def Let_def)

lemma af_selfloop_handle_free_imp_flow_id:
  "\<lbrakk>a \<in> \<E>; flow_invar (af_flow st); af_arc_free (af_flow (af_selfloop_handle st a)) a\<rbrakk>
   \<Longrightarrow> af_flow (af_selfloop_handle st a) = af_flow st"
  using af_selfloop_handle_flow_cases[of st a] flow_array.fixed_univ_map_upd[of "af_flow st" a]
  by (auto simp: af_arc_free_def Let_def)

lemma st_upd_invar:
"\<lbrakk>st_invar A; k \<in> \<V> \<rbrakk>
  \<Longrightarrow> st_invar (st_upd A k v)"
  by (rule state_arr.fixed_univ_map_upd_invar)

lemma out_move_invar:
  "\<lbrakk> out_invar A; v\<in> \<V>\<rbrakk>
    \<Longrightarrow> out_invar (out_move A v)"
  by (rule outg.idx_move_invar)

lemma out_reset_invar:
 "\<lbrakk> out_invar A; v\<in> \<V>\<rbrakk> \<Longrightarrow> out_invar (out_reset A v)"
  by (rule outg.idx_reset_invar)

lemma in_move_invar:
  "\<lbrakk> in_invar A; v\<in> \<V>\<rbrakk>
   \<Longrightarrow> in_invar (in_move A v)"
  by (rule ing.idx_move_invar)

lemma in_reset_invar:
  "\<lbrakk> in_invar A; v\<in> \<V>\<rbrakk> \<Longrightarrow> in_invar (in_reset A v)"
  by (rule ing.idx_reset_invar)

subsection \<open>Theme A --- data structures well-formed\<close>

definition "AF_invar_1 st \<longleftrightarrow>
   flow_invar (af_flow st) \<and> st_invar (af_state st) \<and>
   out_invar (af_out_arr st) \<and> in_invar (af_in_arr st)"

lemma AF_invar_1_props[invar_props_elims]:
  "\<lbrakk>AF_invar_1 st;
    \<lbrakk>flow_invar (af_flow st); st_invar (af_state st);
     out_invar (af_out_arr st); in_invar (af_in_arr st)\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: AF_invar_1_def)

lemma AF_invar_1_intro[invar_props_intros]:
  "\<lbrakk>flow_invar (af_flow st); st_invar (af_state st);
    out_invar (af_out_arr st); in_invar (af_in_arr st)\<rbrakk> \<Longrightarrow> AF_invar_1 st"
  by (auto simp: AF_invar_1_def)

text \<open>A cancellation only ever pushes flow (through @{const af_push} / @{const af_push_arc}), so it
      preserves @{term flow_invar}.\<close>

lemma af_push_arc_flow_invar:
  "\<lbrakk>a \<in> \<E>; af_push_arc \<gamma> a dir fl = (fl', f'); flow_invar fl\<rbrakk> \<Longrightarrow>
    flow_invar fl'"
  by (auto simp: af_push_arc_def Let_def flow_upd_invar)

lemma af_push_flow_invar:
  "\<lbrakk>set es \<subseteq> \<E>; af_push \<gamma> x vs es ds flip fl = (fl', m'); flow_invar fl\<rbrakk>
   \<Longrightarrow> flow_invar fl'"
  by (induction \<gamma> x vs es ds flip fl arbitrary: fl' m' rule: af_push.induct)
     (auto split: prod.splits if_splits dest: af_push_arc_flow_invar)

lemma af_cancel_seg_flow_invar:
  "\<lbrakk>set es \<subseteq> \<E>; a \<in> \<E>; af_cancel_seg up dn x vs es ds a dir fl = (fl'', m', ubd);
    flow_invar fl\<rbrakk> \<Longrightarrow> flow_invar fl''"
  by (auto simp: af_cancel_seg_def Let_def split: prod.splits if_splits
           dest: af_push_flow_invar af_push_arc_flow_invar)

text \<open>A reset copies pristine iterators via @{term arr_upd}, and the fused truncation clean-up also
      re-marks the dropped vertices @{term Unseen} via @{term st_upd}; both preserve the invariants.\<close>

lemma af_reset_state_upd_invar_1:
  "\<lbrakk>v \<in> \<V>; AF_invar_1 st\<rbrakk> \<Longrightarrow> AF_invar_1 (af_reset v (st \<lparr>af_state :=
    st_upd (af_state st) v Unseen\<rparr>))"
  by (auto simp: AF_invar_1_def af_reset_def st_upd_invar intro: out_reset_invar in_reset_invar)

lemma af_reset_unsee_seg_invar_1:
  "\<lbrakk>set vs \<subseteq> \<V>; AF_invar_1 st\<rbrakk> \<Longrightarrow> AF_invar_1 (af_reset_unsee_seg n vs st)"
  by (induction n vs st rule: af_reset_unsee_seg.induct) (auto intro: af_reset_state_upd_invar_1)

text \<open>Record-update helpers, one per shape of @{const af_handle} branch.\<close>

lemma AF_invar_1_out_advance:
  "\<lbrakk>v \<in> \<V>; AF_invar_1 st\<rbrakk> \<Longrightarrow> AF_invar_1 (st \<lparr>af_out_arr := out_move
    (af_out_arr st) v\<rparr>)"
  by (auto simp: AF_invar_1_def intro: out_move_invar)

lemma AF_invar_1_in_advance:
  "\<lbrakk>v \<in> \<V>; AF_invar_1 st\<rbrakk> \<Longrightarrow> AF_invar_1 (st \<lparr>af_in_arr := in_move
    (af_in_arr st) v\<rparr>)"
  by (auto simp: AF_invar_1_def intro: in_move_invar)

lemma af_handle_invar_1:
  assumes "AF_invar_1 st" "a \<in> \<E>" "set (af_estack st) \<subseteq> \<E>" "set (af_vstack st) \<subseteq> \<V>"
  shows "AF_invar_1 (af_handle st a dir)"
  using assms(2)
proof(cases rule: af_handle_cases[of a st dir])
  case selfloop
  thus ?thesis
    using assms(1) af_selfloop_handle_flow_invar assms(2)
    by (auto simp: AF_invar_1_def)
next
  case (push up dn)
  thus ?thesis
    using assms(1) fst_E_V assms(2) snd_E_V assms(2)
    by (cases dir) (auto simp: AF_invar_1_def st_upd_invar)
next
  case (cancel up dn fl m')
  have "flow_invar fl"
    using assms(1) af_cancel_seg_flow_invar assms(3,2) cancel(6)
    by (auto simp: AF_invar_1_def)
  thus ?thesis
    unfolding cancel(7)
    using assms(1,4)
    by (intro af_reset_unsee_seg_invar_1) (auto simp: AF_invar_1_def)
qed (auto simp: AF_invar_1_def assms(1)[unfolded AF_invar_1_def])

text \<open>The single-step preservation of Themes A and B now depends on the range invariants (an updated
      edge/vertex must lie in the edge/vertex set for the length-preserving arrays to register the write),
      so Themes A and B are preserved jointly. The combined single-step lemmas
        \<^verbatim>\<open>AF_invar_12_holds_1/2/3\<close>
      live below (after Theme E1 supplies the fact that the scanned arc lies in the edge set); the
      whole-loop lift is \<^verbatim>\<open>AF_inv_holds\<close>.\<close>

subsection \<open>Theme B --- stack bookkeeping\<close>

text \<open>The truncate clean-up @{const af_reset_unsee_seg} leaves the flow and the three stacks untouched
      and only re-marks the first @{term n} walked vertices @{term Unseen}; these structural facts
      drive every stack-invariant preservation step.\<close>

lemma af_reset_unsee_seg_vstack[simp]: "af_vstack (af_reset_unsee_seg n vs st) = af_vstack st"
  by (induction n vs st rule: af_reset_unsee_seg.induct) (auto simp: af_reset_def)

lemma af_reset_unsee_seg_estack[simp]: "af_estack (af_reset_unsee_seg n vs st) = af_estack st"
  by (induction n vs st rule: af_reset_unsee_seg.induct) (auto simp: af_reset_def)

lemma af_reset_unsee_seg_dstack[simp]: "af_dstack (af_reset_unsee_seg n vs st) = af_dstack st"
  by (induction n vs st rule: af_reset_unsee_seg.induct) (auto simp: af_reset_def)

lemma af_reset_unsee_seg_flow[simp]: "af_flow (af_reset_unsee_seg n vs st) = af_flow st"
  by (induction n vs st rule: af_reset_unsee_seg.induct) (auto simp: af_reset_def)

lemma af_reset_unsee_seg_state:
  "\<lbrakk>set vs \<subseteq> \<V>; st_invar (af_state st)\<rbrakk> \<Longrightarrow>
     st_lookup (af_state (af_reset_unsee_seg n vs st)) w =
       (if w \<in> set (take n vs) then Unseen else st_lookup (af_state st) w)"
  by (induction n vs st rule: af_reset_unsee_seg.induct)
     (auto simp: af_reset_def state_arr.fixed_univ_map_upd st_upd_invar)

text \<open>Truncate-to-bottleneck drops at most as many vertices as there are stack arcs, so it never
      empties the stack (the surviving reached endpoint stays on it).\<close>

lemma af_push_drop_bound: "af_push \<gamma> x vs es ds flip fl = (fl', m') \<Longrightarrow> m' \<le> length es"
  by (induction \<gamma> x vs es ds flip fl arbitrary: fl' m' rule: af_push.induct)
     (auto split: prod.splits if_splits)

lemma af_cancel_seg_drop_bound:
  "af_cancel_seg up dn x vs es ds a dir fl = (fl'', m', ubd) \<Longrightarrow> m' \<le> length es"
  by (auto simp: af_cancel_seg_def Let_def split: prod.splits if_splits dest: af_push_drop_bound)

text \<open>Theme B: the vertex stack is distinct, the arc/tag stacks are exactly one shorter (or all three
      are empty), and a vertex is @{term OnStack} iff it is on the vertex stack.\<close>

definition "AF_invar_2 st \<longleftrightarrow>
   distinct (af_vstack st) \<and>
   ((af_vstack st = [] \<and> af_estack st = [] \<and> af_dstack st = []) \<or>
    (Suc (length (af_estack st)) = length (af_vstack st) \<and>
     length (af_dstack st) = length (af_estack st))) \<and>
   (\<forall>v \<in> \<V>. (st_lookup (af_state st) v = OnStack) = (v \<in> set (af_vstack st)))"

lemma AF_invar_2E:
  "\<lbrakk>AF_invar_2 st;
     \<lbrakk>distinct (af_vstack st);
       (af_vstack st = [] \<and> af_estack st = [] \<and> af_dstack st = []) \<or>
       (Suc (length (af_estack st)) = length (af_vstack st) \<and>
        length (af_dstack st) = length (af_estack st));
       \<And>v. v \<in> \<V> \<Longrightarrow> (st_lookup (af_state st) v = OnStack) = (v \<in> set (af_vstack
         st))\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: AF_invar_2_def)

lemma AF_invar_2I:
  "\<lbrakk>distinct (af_vstack st);
    (af_vstack st = [] \<and> af_estack st = [] \<and> af_dstack st = []) \<or>
    (Suc (length (af_estack st)) = length (af_vstack st) \<and>
     length (af_dstack st) = length (af_estack st));
    \<And>v. v \<in> \<V> \<Longrightarrow> (st_lookup (af_state st) v = OnStack) = (v \<in> set (af_vstack
      st))\<rbrakk> \<Longrightarrow> AF_invar_2 st"
  by (auto simp: AF_invar_2_def)

text \<open>Push: the new leaf @{term x} was @{term Unseen}, hence not yet on the stack.\<close>

lemma AF_invar_2_push:
  "\<lbrakk>AF_invar_1 st; AF_invar_2 st; af_vstack st \<noteq> []; st_lookup (af_state st) x = Unseen; x \<in>
    \<V>\<rbrakk> \<Longrightarrow> AF_invar_2 (st\<lparr>af_vstack := x # af_vstack st, af_state := st_upd (af_state
    st) x OnStack,
                        af_estack := a # af_estack st, af_dstack := dir # af_dstack st\<rparr>)"
  by (auto simp: AF_invar_2_def AF_invar_1_def state_arr.fixed_univ_map_upd)

text \<open>Back-edge truncate-and-reset: drop @{term \<open>m'\<close>} vertices (bounded, so the stack stays
    non-empty)
      and re-mark exactly those @{term Unseen}. This is the load-bearing case; distinctness turns the
      @{term take}/@{term drop} split of the stack into the restored @{term OnStack} correspondence.\<close>

lemma AF_invar_2_backedge:
  assumes "AF_invar_1 st" "AF_invar_2 st" "af_vstack st \<noteq> []"
    "af_cancel_seg up dn x (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) = (fl, m', ubd)"
    and "set (af_vstack st) \<subseteq> \<V>"
  shows "AF_invar_2 (af_reset_unsee_seg m' (af_vstack st)
           (st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st),
               af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>))"
proof-
  have "m' \<le> length (af_estack st)"
       "set (af_vstack st) = set (take m' (af_vstack st)) \<union> set (drop m' (af_vstack st))"
       "set (take m' (af_vstack st)) \<inter> set (drop m' (af_vstack st)) = {}"
    using af_cancel_seg_drop_bound assms(4) assms(2)
          distinct_append[of "take m' (af_vstack st)" "drop m' (af_vstack st)"]
    by (auto simp: AF_invar_2_def set_append[symmetric] simp del: set_append)
  thus ?thesis
    using assms(1,2,3)
    by (auto simp: AF_invar_2_def AF_invar_1_def Suc_diff_le af_reset_unsee_seg_state[OF assms(5)]
             split: if_splits)
qed

lemma af_handle_invar_2:
  assumes "AF_invar_1 st" "AF_invar_2 st" "af_vstack st \<noteq> []"
    and "a \<in> \<E>" "set (af_vstack st) \<subseteq> \<V>"
  shows "AF_invar_2 (af_handle st a dir)"
  using assms(4)
proof(cases rule: af_handle_cases[of a st dir])
  case (push up dn)
  thus ?thesis
    using AF_invar_2_push[OF assms(1-3), of "if dir then snd a else fst a"]
          fst_E_V assms(4) snd_E_V assms(4)
    by (cases dir) auto
next
  case (cancel up dn fl m')
  thus ?thesis
    using AF_invar_2_backedge assms(1-3) cancel(6) assms(5)
    by (simp)
qed (insert assms(2), (auto simp: AF_invar_2_def))

lemma AF_invar_2_out_arr[simp]: "AF_invar_2 (st\<lparr>af_out_arr := X\<rparr>) = AF_invar_2 st"
  by (simp add: AF_invar_2_def)

lemma AF_invar_2_in_arr[simp]: "AF_invar_2 (st\<lparr>af_in_arr := X\<rparr>) = AF_invar_2 st"
  by (simp add: AF_invar_2_def)

text \<open>The single-step lifts of Theme B to the three DFS steps, together with those of Theme A, are the
      combined lemmas \<^verbatim>\<open>AF_invar_12_holds_1/2/3\<close> proved below (Theme E1 first supplies the
        fact that the
      scanned arc lies in the edge set).\<close>

subsection \<open>Theme D --- the flow (structural core)\<close>

text \<open>The three outcomes of @{const af_cancel_seg}: a finite cancellation in the cheaper direction,
      a cost-neutral cancellation in the finite direction, or the unbounded flag.\<close>

lemma af_cancel_seg_cases[consumes 1, case_names fin sw ubd]:
  assumes "af_cancel_seg up dn x vs es ds a dir fl = (fl'', m', ubd)"
  obtains k ra rf fl' f2
    where "af_scan fl x vs es ds (af_delta_cost a dir, if dir then up else dn, if dir then dn else up)
             = (k, ra, rf)"
      "(if 0 < k then rf else ra) \<noteq> - 1"
      "af_push (if 0 < k then rf else ra) x vs es ds (0 < k) fl = (fl', m')"
      "af_push_arc (if 0 < k then rf else ra) a (dir \<noteq> (0 < k)) fl' = (fl'', f2)" "\<not> ubd"
  | k ra rf fl' f2
    where "af_scan fl x vs es ds (af_delta_cost a dir, if dir then up else dn, if dir then dn else up)
             = (k, ra, rf)"
      "(if 0 < k then rf else ra) = - 1" "k = 0" "rf \<noteq> - 1"
      "af_push rf x vs es ds True fl = (fl', m')" "af_push_arc rf a (\<not> dir) fl' = (fl'', f2)" "\<not> ubd"
  | k ra rf
    where "af_scan fl x vs es ds (af_delta_cost a dir, if dir then up else dn, if dir then dn else up)
             = (k, ra, rf)"
      "(if 0 < k then rf else ra) = - 1" "\<not> (k = 0 \<and> rf \<noteq> - 1)" "fl'' = fl" "m' = 0" "ubd"
proof-
  obtain k ra rf where sc: "af_scan fl x vs es ds
      (af_delta_cost a dir, if dir then up else dn, if dir then dn else up) = (k, ra, rf)"
    by (rule prod_cases3)
  obtain fl1 r1 fl2 f2 where p: "af_push (if 0 < k then rf else ra) x vs es ds (0 < k) fl = (fl1, r1)"
      "af_push_arc (if 0 < k then rf else ra) a (dir \<noteq> (0 < k)) fl1 = (fl2, f2)"
    by fastforce
  obtain fl3 r3 fl4 f4 where q: "af_push rf x vs es ds True fl = (fl3, r3)"
      "af_push_arc rf a (\<not> dir) fl3 = (fl4, f4)"
    by fastforce
  show thesis
  proof(cases "(if 0 < k then rf else ra) \<noteq> - 1")
    case True
    thus thesis
      using assms sc p
      by (intro that(1)[of k ra rf fl1 f2]) (auto simp: af_cancel_seg_def Let_def)
  next
    case nf: False
    show thesis
    proof(cases "k = 0 \<and> rf \<noteq> - 1")
      case True
      thus thesis
        using assms sc q nf
        by (intro that(2)[of k ra rf fl3 f4]) (auto simp: af_cancel_seg_def Let_def)
    next
      case False
      thus thesis
        using assms sc nf
        by (intro that(3)[of k ra rf]) (auto simp: af_cancel_seg_def Let_def)
    qed
  qed
qed

text \<open>A cancellation touches the flow only on the arcs it pushes: the walk arcs @{term es} (through
      @{const af_push}) and the closing arc @{term a} (through @{const af_push_arc}). Every arc off the
      walk keeps its flow value, hence keeps its free/blocked status. This is the ``arcs off the walk
      are untouched'' half of D2 (the free set only shrinks).\<close>

lemma af_push_flow_off:
  "\<lbrakk>set es \<subseteq> \<E>; flow_invar fl; b \<notin> set es; af_push \<gamma> x vs es ds flip fl = (fl',
    m')\<rbrakk>
   \<Longrightarrow> flow_lookup fl' b = flow_lookup fl b"
  by (induction \<gamma> x vs es ds flip fl arbitrary: fl' m' rule: af_push.induct)
     (auto simp: af_push_arc_def Let_def flow_array.fixed_univ_map_upd flow_upd_invar split: prod.splits if_splits)

lemma af_push_arc_flow_off:
  "\<lbrakk>a \<in> \<E>; flow_invar fl; b \<noteq> a; af_push_arc \<gamma> a dir fl = (fl', f')\<rbrakk>
   \<Longrightarrow> flow_lookup fl' b = flow_lookup fl b"
  by (auto simp: af_push_arc_def Let_def flow_array.fixed_univ_map_upd)

lemma af_cancel_seg_flow_off:
  assumes "set es \<subseteq> \<E>" "a \<in> \<E>" "flow_invar fl" "b \<notin> set es" "b \<noteq> a"
    "af_cancel_seg up dn x vs es ds a dir fl = (fl'', m', ubd)"
  shows "flow_lookup fl'' b = flow_lookup fl b"
  using assms(6)
proof(cases rule: af_cancel_seg_cases)
  case (fin k ra rf fl' f2)
  thus ?thesis
    using af_push_flow_off assms(1,3,4) fin(3)
          af_push_arc_flow_off[OF assms(2) af_push_flow_invar[OF assms(1) fin(3) assms(3)] assms(5) fin(4)]
    by (simp)
next
  case (sw k ra rf fl' f2)
  thus ?thesis
    using af_push_flow_off assms(1,3,4) sw(5)
          af_push_arc_flow_off[OF assms(2) af_push_flow_invar[OF assms(1) sw(5) assms(3)] assms(5) sw(6)]
    by (simp)
qed (simp)

text \<open>Consequently an off-walk arc keeps its free/blocked status across a cancellation: the free set
      does not grow there.\<close>

lemma af_cancel_seg_arc_free_off:
  "\<lbrakk>set es \<subseteq> \<E>; a \<in> \<E>; flow_invar fl; b \<notin> set es; b \<noteq> a;
    af_cancel_seg up dn x vs es ds a dir fl = (fl'', m', ubd)\<rbrakk>
   \<Longrightarrow> af_arc_free fl'' b = af_arc_free fl b"
  by (simp add: af_arc_free_def af_cancel_seg_flow_off[of es a fl b up dn x vs ds dir fl'' m' ubd])

text \<open>Building blocks for the on-walk (feasibility / bottleneck) half of Theme D. One push shifts its
      arc's flow by exactly \<open>\<plusminus>\<gamma>\<close>; @{const af_min} is bounded above by any finite
        argument (it
      treats @{term \<open>- 1\<close>} as ``unbounded''), so the scanned bottleneck is @{text "\<le>"} every finite
        room.\<close>

lemma af_push_arc_at:
  "\<lbrakk>a \<in> \<E>; flow_invar fl; af_push_arc \<gamma> a dir fl = (fl', f')\<rbrakk>
   \<Longrightarrow> flow_lookup fl' a = f' \<and> f' = flow_lookup fl a + (if dir then \<gamma> else - \<gamma>)"
  by (auto simp: af_push_arc_def Let_def flow_array.fixed_univ_map_upd)

lemma af_min_le1: "x \<noteq> - 1 \<Longrightarrow> af_min x y \<le> x"
  by (auto simp: af_min_def)

text \<open>Feasibility of the flow (over the multigraph @{term \<E>}): every arc's value is between @{term 0}
      and its capacity (with @{term \<open>- 1\<close>} = infinite meaning ``no upper bound''). A single push keeps its
      arc feasible provided the push amount fits the room in the chosen direction --- the per-arc core
      of Theme D1.\<close>

definition "af_cap_feasible fl \<longleftrightarrow>
   (\<forall>a\<in>\<E>. 0 \<le> flow_lookup fl a \<and> (cap a = - 1 \<or> flow_lookup fl a \<le> cap a))"

text \<open>The executable capacity predicate is exactly the abstract @{const isuflow} on the flow's
      abstraction: @{term cap} encodes @{term \<open>\<u>\<close>} with the @{term \<open>- 1\<close>} sentinel for
        @{term \<open>\<infinity>\<close>}
      (@{thm cap_encoding}), and since @{term \<open>0 \<le> \<u> e\<close>} a finite room @{term \<open>f e \<le> cap
        e\<close>} matches
      @{term \<open>ereal (f e) \<le> \<u> e\<close>} while the sentinel matches the always-true infinite bound.\<close>

lemma af_cap_feasible_iff_isuflow: "af_cap_feasible fl \<longleftrightarrow> isuflow (h \<circ> flow_lookup fl)"
proof-
  have "(0 \<le> flow_lookup fl a \<and> (cap a = - 1 \<or> flow_lookup fl a \<le> cap a))
          \<longleftrightarrow> (ereal (h (flow_lookup fl a)) \<le> \<u> a \<and> 0 \<le> h (flow_lookup fl a))" if "a
            \<in> \<E>" for a
    using that cap_encoding[of a] cap_infinite_bridge[of a]
    by (cases "\<u> a = \<infinity>") auto
  thus ?thesis
    by (auto simp: af_cap_feasible_def isuflow_def)
qed

text \<open>Feasibility as a genuine @{term b}-flow of the flow's abstraction (Theme D1): capacity
      feasibility (@{const isuflow}, phrased over the abstract @{term \<open>\<u>\<close>}) \emph{together with} the
      balance/divergence condition @{term \<open>- ex\<^bsub>f\<^esub> v = b v\<close>} at every vertex. The executable
      capacity @{term cap} appears only inside the internal helper @{const af_cap_feasible}, which
      bridges to @{const isuflow} by @{thm af_cap_feasible_iff_isuflow}; the invariant itself is
      stated entirely over the abstract network.\<close>

definition "af_feasible b fl \<longleftrightarrow> (h \<circ> flow_lookup fl) is b flow"

lemma af_feasibleI:
  "\<lbrakk>af_cap_feasible fl; \<And>v. v \<in> \<V> \<Longrightarrow> - ex (h \<circ> flow_lookup fl) v = b
    v\<rbrakk> \<Longrightarrow> af_feasible b fl"
  by (auto simp: af_feasible_def af_cap_feasible_iff_isuflow intro: isbflowI)

lemma af_feasible_cap: "af_feasible b fl \<Longrightarrow> af_cap_feasible fl"
  by (auto simp: af_feasible_def af_cap_feasible_iff_isuflow elim: isbflowE)

lemma af_feasible_bal: "\<lbrakk>af_feasible b fl; v \<in> \<V>\<rbrakk> \<Longrightarrow> - ex (h \<circ> flow_lookup
    fl) v = b v"
  by (auto simp: af_feasible_def elim: isbflowE)

lemma af_push_arc_feasible:
  "\<lbrakk>a \<in> \<E>; 0 \<le> flow_lookup fl a; cap a = - 1 \<or> flow_lookup fl a \<le> cap a; 0 \<le> \<gamma>;
    if dir then (cap a = - 1 \<or> flow_lookup fl a + \<gamma> \<le> cap a) else \<gamma> \<le> flow_lookup fl a;
    flow_invar fl; af_push_arc \<gamma> a dir fl = (fl', f')\<rbrakk> \<Longrightarrow> 0 \<le> f' \<and> (cap a = - 1
    \<or> f' \<le> cap a)"
  by (cases dir; (fastforce dest: af_push_arc_at))

text \<open>@{const af_scan} reads each arc's room only through @{term flow_lookup} at arcs of @{term es};
      so two flows agreeing on @{term es} produce the same scan. This is what lets a \emph{sequential}
      push (which mutates the flow as it walks) still see the rooms @{const af_scan} precomputed on the
      \emph{original} flow --- the distinct walked arcs never interfere.\<close>

lemma af_scan_cong:
  "\<forall>b\<in>set es. flow_lookup fl b = flow_lookup fl' b
   \<Longrightarrow> af_scan fl x vs es ds acc = af_scan fl' x vs es ds acc"
  by (induction fl x vs es ds acc rule: af_scan.induct) (auto simp: af_rooms_def Let_def)

text \<open>Capacity-agnostic strengthenings of the scan room-bounds and walk-feasibility. Dropping the
      finite-capacity assumption: an infinite room shows up as the sentinel @{term \<open>- 1\<close>}, which
      @{const af_min} treats as ``no bound'' (neutral), so it never lowers a bottleneck; and pushing
      onto an infinite-capacity arc in its open direction is feasible for free (the @{term \<open>cap a = - 1\<close>}
      disjunct of @{const af_cap_feasible}).\<close>

lemma af_rooms_cap_feasible:
  "\<lbrakk>af_rooms fl a = (up, dn); af_cap_feasible fl; a \<in> \<E>\<rbrakk> \<Longrightarrow> 0 \<le> dn \<and>
    (up = - 1 \<or> 0 \<le> up)"
  by (auto simp: af_rooms_def af_cap_feasible_def Let_def split: if_splits)

lemma af_scan_accumulator_invariant:
  assumes "P acc"
    "\<And>a d k ra rf. \<lbrakk>a \<in> set es; P (k, ra, rf)\<rbrakk> \<Longrightarrow>
      P (k + af_delta_cost a d,
         af_min (if d then Product_Type.fst (af_rooms fl a) else Product_Type.snd (af_rooms fl a)) ra,
         af_min (if d then Product_Type.snd (af_rooms fl a) else Product_Type.fst (af_rooms fl a)) rf)"
  shows "P (af_scan fl x vs es ds acc)"
  using assms
proof(induction fl x vs es ds acc rule: af_scan.induct)
  case IH: (1 fl x u v vs a es d ds k ra rf)
  obtain up dn where rooms: "af_rooms fl a = (up, dn)"
    by fastforce
  have "P (k + af_delta_cost a d,
      af_min (if d then up else dn) ra, af_min (if d then dn else up) rf)"
    using IH.prems(2)[of a k ra rf d, simplified rooms] IH.prems(1)
    by auto
  thus ?case
    using IH.IH[OF rooms[symmetric] refl refl] IH.prems(2) rooms
    by (auto simp: Let_def)
qed auto

lemma af_scan_ra_mono_gen:
  assumes "af_cap_feasible fl" "set es \<subseteq> \<E>" "0 \<le> ra0" "af_scan fl x vs es ds (k0, ra0, rf0) = (k, ra,
    rf)"
  shows "ra \<le> ra0 \<and> 0 \<le> ra"
  by (rule af_scan_accumulator_invariant[where P="\<lambda>(_, r, _). r \<le> ra0 \<and> 0 \<le> r"
      and fl=fl and x=x and vs=vs and es=es and ds=ds and acc="(k0, ra0, rf0)",
      unfolded assms(4), simplified]; insert assms;
      (auto simp: af_min_def af_rooms_def af_cap_feasible_def Let_def split: if_splits))

lemma af_scan_rf_mono_gen:
  assumes "af_cap_feasible fl" "set es \<subseteq> \<E>" "0 \<le> rf0" "af_scan fl x vs es ds (k0, ra0, rf0) = (k, ra,
    rf)"
  shows "rf \<le> rf0 \<and> 0 \<le> rf"
  by (rule af_scan_accumulator_invariant[where P="\<lambda>(_, _, r). r \<le> rf0 \<and> 0 \<le> r"
      and fl=fl and x=x and vs=vs and es=es and ds=ds and acc="(k0, ra0, rf0)",
      unfolded assms(4), simplified]; insert assms;
      (auto simp: af_min_def af_rooms_def af_cap_feasible_def Let_def split: if_splits))

lemma af_scan_ra_valid:
  assumes "af_cap_feasible fl" "set es \<subseteq> \<E>" "ra0 = - 1 \<or> 0 \<le> ra0" "af_scan fl x vs es ds (k0,
    ra0, rf0) = (k, ra, rf)"
  shows "ra = - 1 \<or> 0 \<le> ra"
  by (rule af_scan_accumulator_invariant[where P="\<lambda>(_, r, _). r = - 1 \<or> 0 \<le> r"
      and fl=fl and x=x and vs=vs and es=es and ds=ds and acc="(k0, ra0, rf0)",
      unfolded assms(4), simplified]; insert assms;
      (auto simp: af_min_def af_rooms_def af_cap_feasible_def Let_def split: if_splits))

lemma af_scan_rf_valid:
  assumes "af_cap_feasible fl" "set es \<subseteq> \<E>" "rf0 = - 1 \<or> 0 \<le> rf0" "af_scan fl x vs es ds (k0,
    ra0, rf0) = (k, ra, rf)"
  shows "rf = - 1 \<or> 0 \<le> rf"
  by (rule af_scan_accumulator_invariant[where P="\<lambda>(_, _, r). r = - 1 \<or> 0 \<le> r"
      and fl=fl and x=x and vs=vs and es=es and ds=ds and acc="(k0, ra0, rf0)",
      unfolded assms(4), simplified]; insert assms;
      (auto simp: af_min_def af_rooms_def af_cap_feasible_def Let_def split: if_splits))

text \<open>A push amount bounded by the room of an arc in the pushed direction, whenever that room is finite,
      fits the arc.\<close>

lemma af_room_fits:
  "\<lbrakk>af_rooms fl a = (up, dn); af_cap_feasible fl; a \<in> \<E>;
    (if d then up else dn) \<noteq> - 1 \<Longrightarrow> g \<le> (if d then up else dn)\<rbrakk>
   \<Longrightarrow> if d then cap a = - 1 \<or> flow_lookup fl a + g \<le> cap a else g \<le> flow_lookup fl a"
  by (cases d) (auto simp: af_rooms_def af_cap_feasible_def Let_def split: if_splits)

text \<open>Whole-flow feasibility for a single push on the \emph{closing} arc, given it fits that arc's room.\<close>

lemma af_push_arc_af_cap_feasible:
  assumes "af_cap_feasible fl" "flow_invar fl" "a \<in> \<E>" "0 \<le> \<gamma>"
    "if dir then (cap a = - 1 \<or> flow_lookup fl a + \<gamma> \<le> cap a) else \<gamma> \<le> flow_lookup fl a"
    "af_push_arc \<gamma> a dir fl = (fl', f')"
  shows "af_cap_feasible fl'"
  unfolding af_cap_feasible_def
proof
  fix c
  assume "c \<in> \<E>"
  thus "0 \<le> flow_lookup fl' c \<and> (cap c = - 1 \<or> flow_lookup fl' c \<le> cap c)"
    using assms(1,3) af_push_arc_feasible[OF assms(3) _ _ assms(4,5,2,6)] af_push_arc_at assms(3,2,6)
          af_push_arc_flow_off[OF assms(3,2) _ assms(6), of c]
    by (cases "c = a") (auto simp: af_cap_feasible_def)
qed

text \<open>Relaxed to an infinite \emph{seed}: the closing arc of a cancellation seeds the walk-scan with its
      own room, which may be @{term \<open>- 1\<close>} (infinite). Since @{const af_min} neutralises @{term \<open>-
        1\<close>},
      the walked-arc feasibility still goes through --- the bottleneck bounds are derived only where the
      relevant room is finite.\<close>

lemma af_scan_push_feasible_gen2:
  "\<lbrakk>af_cap_feasible fl; flow_invar fl; distinct es; set es \<subseteq> \<E>;
    af_scan fl x vs es ds (k0, ra0, rf0) = (k, ra, rf); af_push \<gamma> x vs es ds flip fl = (fl', m');
    0 \<le> \<gamma>; ra0 = - 1 \<or> 0 \<le> ra0; rf0 = - 1 \<or> 0 \<le> rf0; if flip then \<gamma> \<le> rf else
      \<gamma> \<le> ra\<rbrakk>
   \<Longrightarrow> af_cap_feasible fl'"
proof(induction \<gamma> x vs es ds flip fl arbitrary: fl' m' k0 ra0 rf0 rule: af_push.induct)
  case (1 \<gamma> x u v1 vs a es d ds flip fl)
  obtain up dn where ud: "af_rooms fl a = (up, dn)"
    by (fastforce)
  obtain fl1 fv where p1: "af_push_arc \<gamma> a (d \<noteq> flip) fl = (fl1, fv)"
    by (fastforce)
  define Ra Rf where "Ra = af_min (if d then up else dn) ra0" and "Rf = af_min (if d then dn else up) rf0"
  have a: "a \<in> \<E>" "a \<notin> set es" "set es \<subseteq> \<E>" "distinct es"
    using 1(4,5)
    by (auto)
  have z: "0 \<le> dn" "up = - 1 \<or> 0 \<le> up"
    using af_rooms_cap_feasible[OF ud 1(2) a(1)]
    by (auto)
  have sc: "v1 \<noteq> x \<Longrightarrow> af_scan fl x (v1 # vs) es ds (k0 + af_delta_cost a d, Ra, Rf) = (k, ra, rf)"
    using 1(6) ud
    by (simp add: Let_def Ra_def Rf_def)
  have "(0 \<le> Ra \<longrightarrow> ra \<le> Ra) \<and> (0 \<le> Rf \<longrightarrow> rf \<le> Rf)"
  proof(cases "v1 = x")
    case True
    thus ?thesis
      using 1(6) ud
      by (simp add: Let_def Ra_def Rf_def)
  next
    case False
    thus ?thesis
      using af_scan_ra_mono_gen[OF 1(2) a(3) _ sc] af_scan_rf_mono_gen[OF 1(2) a(3) _ sc]
      by (blast)
  qed
  hence "(if d \<noteq> flip then up else dn) \<noteq> - 1 \<Longrightarrow> \<gamma> \<le> (if d \<noteq> flip then
    up else dn)"
    using z 1(9,10,11)
    by (cases d; cases flip) (auto simp: Ra_def Rf_def af_min_def split: if_splits)
  hence feas1: "af_cap_feasible fl1"
    using af_push_arc_af_cap_feasible[OF 1(2,3) a(1) 1(8) af_room_fits[OF ud 1(2) a(1)] p1]
    by (simp)
  show ?case
  proof(cases "v1 = x")
    case True
    thus ?thesis
      using 1(7) p1 feas1
      by (auto simp: Let_def)
  next
    case False
    obtain fl2 r where p2: "af_push \<gamma> x (v1 # vs) es ds flip fl1 = (fl2, r)"
      by (fastforce)
    have "\<forall>b\<in>set es. flow_lookup fl1 b = flow_lookup fl b"
      using a(2)
      by (auto intro: af_push_arc_flow_off[OF a(1) 1(3) _ p1])
    hence "af_scan fl1 x (v1 # vs) es ds (k0 + af_delta_cost a d, Ra, Rf) = (k, ra, rf)"
      using af_scan_cong[of es fl1 fl] sc False
      by (simp)
    moreover have "Ra = - 1 \<or> 0 \<le> Ra" "Rf = - 1 \<or> 0 \<le> Rf"
      using z 1(9,10)
      by (auto simp: Ra_def Rf_def af_min_def)
    ultimately show ?thesis
      using 1(1)[OF p1[symmetric] refl False feas1 af_push_arc_flow_invar[OF a(1) p1 1(3)] a(4,3) _ p2 1(8)]
            1(7,11) p1 p2 False
      by (auto simp: Let_def)
  qed
qed (auto)

text \<open>Feasibility of one finite cancellation: the walk is pushed by the bottleneck in the chosen
      direction, then the closing arc.\<close>

lemma af_cancel_push_feasible:
  assumes "af_cap_feasible fl" "flow_invar fl" "distinct (a # es)" "a \<in> \<E>" "set es \<subseteq> \<E>"
    "af_rooms fl a = (up, dn)"
    "af_scan fl x vs es ds (af_delta_cost a dir, if dir then up else dn, if dir then dn else up)
       = (k, ra, rf)"
    "g = (if flip then rf else ra)" "g \<noteq> - 1"
    "af_push g x vs es ds flip fl = (fl', m')" "af_push_arc g a (dir \<noteq> flip) fl' = (fl'', f2)"
  shows "af_cap_feasible fl''"
proof-
  have rooms: "0 \<le> dn" "up = - 1 \<or> 0 \<le> up"
    "(if dir then up else dn) = - 1 \<or> 0 \<le> (if dir then up else dn)"
    "(if dir then dn else up) = - 1 \<or> 0 \<le> (if dir then dn else up)"
    using assms(6,1,4)
    by (auto dest: af_rooms_cap_feasible)
  have g: "0 \<le> g"
    using assms(1,5,7-9) rooms(3,4)
    by (cases flip; (fastforce dest: af_scan_ra_valid af_scan_rf_valid))
  have "(if dir \<noteq> flip then up else dn) \<noteq> - 1 \<Longrightarrow> g \<le> (if dir \<noteq> flip then up
    else dn)"
    using assms(1,5,7,8) rooms(1,2)
    by (cases dir; cases flip; (fastforce dest: af_scan_ra_mono_gen af_scan_rf_mono_gen))
  moreover have "flow_lookup fl' a = flow_lookup fl a"
    using assms(2,3,5,10)
    by (auto dest: af_push_flow_off[where b=a])
  ultimately have "if dir \<noteq> flip then cap a = - 1 \<or> flow_lookup fl' a + g \<le> cap a
                   else g \<le> flow_lookup fl' a"
    using af_room_fits[of fl a up dn "dir \<noteq> flip" g] assms(1,4,6)
    by (simp)
  then show ?thesis
    using af_push_arc_af_cap_feasible[OF _ af_push_flow_invar[OF assms(5,10,2)] assms(4) g _ assms(11)]
          af_scan_push_feasible_gen2[OF assms(1,2) _ assms(5,7,10) g rooms(3,4)] assms(3,8)
    by (simp)
qed

text \<open>Capacity-agnostic feasibility of a whole cancellation: no finite-capacity assumption.\<close>

lemma af_cancel_seg_feasible_gen:
  assumes "af_cap_feasible fl" "flow_invar fl" "distinct (a # es)" "a \<in> \<E>" "set es \<subseteq> \<E>"
    "af_rooms fl a = (up, dn)" "af_cancel_seg up dn x vs es ds a dir fl = (fl'', m', ubd)"
  shows "af_cap_feasible fl''"
  using assms(7)
proof(cases rule: af_cancel_seg_cases)
  case (fin k ra rf fl' f2)
  thus ?thesis
    using af_cancel_push_feasible assms(1-6) fin(1) refl fin(2-4)
    by (simp)
next
  case (sw k ra rf fl' f2)
  hence "af_push_arc rf a (dir \<noteq> True) fl' = (fl'', f2)"
    by (simp)
  thus ?thesis
    using af_cancel_push_feasible[OF assms(1-6) sw(1) if_True[symmetric] sw(4,5)]
    by (simp)
qed (insert assms(1), (simp))

subsection \<open>Theme D3 --- cost is non-increasing\<close>

text \<open>Cost of a flow (over the multigraph): @{term \<open>\<C> f = (\<Sum>e\<in>\<E>. f e * \<c> e)\<close>}.
    One push on an arc
      shifts the total cost by exactly \<open>\<plusminus>\<gamma>\<close> times that arc's unit cost --- the sum over
        @{term \<E>}
      differs only at the pushed arc (finite @{term \<E>}).\<close>

lemma af_push_arc_cost:
  assumes "flow_invar fl" "a \<in> \<E>" "af_push_arc \<gamma> a dir fl = (fl', f')"
  shows "\<C> (h \<circ> flow_lookup fl') = \<C> (h \<circ> flow_lookup fl) + (if dir then h \<gamma> else - h
    \<gamma>) * \<c> a"
proof-
  have "\<C> (h \<circ> flow_lookup fl') - \<C> (h \<circ> flow_lookup fl)
        = (\<Sum>e\<in>\<E>. (h (flow_lookup fl' e) - h (flow_lookup fl e)) * \<c> e)"
    by (simp add: \<C>_def sum_subtractf left_diff_distrib comp_def)
  also have "\<dots> = (h (flow_lookup fl' a) - h (flow_lookup fl a)) * \<c> a"
    by (subst sum.remove[OF finite_E assms(2)])
       (auto intro!: sum.neutral simp: af_push_arc_flow_off[OF assms(2,1) _ assms(3)])
  also have "\<dots> = (if dir then h \<gamma> else - h \<gamma>) * \<c> a"
    using af_push_arc_at[of a fl \<gamma> dir fl' f'] assms(2,1,3)
    by (simp add: h_add)
  finally show ?thesis
    by (simp)
qed

text \<open>Coupled cost accounting for the walk: pushing @{term \<gamma>} along the scanned cycle changes the total
      cost by @{term \<gamma>} times the scan's accumulated walk cost @{term \<open>k - k0\<close>} (negated when
        flipped).\<close>

lemma af_scan_push_cost:
  "\<lbrakk>flow_invar fl; distinct es; set es \<subseteq> \<E>; af_scan fl x vs es ds (k0, ra0, rf0) = (k, ra, rf);
    af_push \<gamma> x vs es ds flip fl = (fl', m')\<rbrakk>
   \<Longrightarrow> \<C> (h \<circ> flow_lookup fl') = \<C> (h \<circ> flow_lookup fl) + h (\<gamma> * (if flip then
     k0 - k else k - k0))"
proof(induction \<gamma> x vs es ds flip fl arbitrary: fl' m' k0 ra0 rf0 rule: af_push.induct)
  case (1 \<gamma> x u v1 vs a es d ds flip fl)
  obtain up dn where ud: "af_rooms fl a = (up, dn)"
    by (fastforce)
  obtain fl1 fv where p1: "af_push_arc \<gamma> a (d \<noteq> flip) fl = (fl1, fv)"
    by (fastforce)
  have a: "a \<in> \<E>" "a \<notin> set es" "distinct es" "set es \<subseteq> \<E>"
    using 1(3,4)
    by (auto)
  have hc: "\<C> (h \<circ> flow_lookup fl1)
            = \<C> (h \<circ> flow_lookup fl) + h (\<gamma> * (if flip then - af_delta_cost a d else af_delta_cost a
              d))"
    using af_push_arc_cost[OF 1(2) a(1) p1]
    by (cases flip; cases d; (simp add: af_delta_cost_def algebra_simps h_mult cost_h[OF a(1)]))
  show ?case
  proof(cases "v1 = x")
    case True
    hence "k = k0 + af_delta_cost a d" "fl' = fl1"
      using 1(5,6) ud p1
      by (auto simp: Let_def)
    thus ?thesis
      using hc
      by (cases flip; (simp add: algebra_simps comp_def))
  next
    case False
    obtain fl2 r where p2: "af_push \<gamma> x (v1 # vs) es ds flip fl1 = (fl2, r)"
      by (fastforce)
    have "\<forall>b\<in>set es. flow_lookup fl1 b = flow_lookup fl b"
      using a(2)
      by (auto intro: af_push_arc_flow_off[OF a(1) 1(2) _ p1])
    hence "af_scan fl1 x (v1 # vs) es ds
             (k0 + af_delta_cost a d, af_min (if d then up else dn) ra0, af_min (if d then dn else up) rf0)
           = (k, ra, rf)"
      using af_scan_cong[of es fl1 fl] 1(5) ud False
      by (simp add: Let_def)
    then have "\<C> (h \<circ> flow_lookup fl2) = \<C> (h \<circ> flow_lookup fl1)
        + h (\<gamma> * (if flip then k0 + af_delta_cost a d - k else k - (k0 + af_delta_cost a d)))"
      using 1(1)[OF p1[symmetric] refl False af_push_arc_flow_invar[OF a(1) p1 1(2)] a(3,4) _ p2]
      by (blast)
    then show ?thesis
      using hc 1(6) p1 p2 False
      by (cases flip; (auto simp: Let_def algebra_simps h_add comp_def))
  qed
qed (auto)

text \<open>Theme D3, top level: a whole cancellation \emph{never increases} the cost. The walk push contributes
      @{term \<open>\<gamma> * (if flip then k0 - k else k - k0)\<close>} and the closing arc @{term \<open>\<gamma> *
        (if flip then - k0 else k0)\<close>}
      (@{term \<open>k0 = af_delta_cost a dir\<close>} is exactly the closing arc's tagged cost, the scan seed),
        summing to
      @{term \<open>\<gamma> * (if 0 < k then - k else k)\<close>} which is @{text \<le>} 0 since @{term \<open>0
        \<le> \<gamma>\<close>} and @{term \<open>flip = (0 < k)\<close>}
      picks the non-positive orientation; the zero-cost switch (@{term \<open>k = 0\<close>}) is cost-neutral, and the
        flag
      branch is cost-preserving.\<close>

lemma af_cancel_seg_cost_le_gen:
  assumes "af_cap_feasible fl" "flow_invar fl" "distinct (a # es)" "a \<in> \<E>" "set es \<subseteq> \<E>"
    "af_rooms fl a = (up, dn)" "af_cancel_seg up dn x vs es ds a dir fl = (fl'', m', ubd)"
  shows "\<C> (h \<circ> flow_lookup fl'') \<le> \<C> (h \<circ> flow_lookup fl)"
proof-
  have s: "(if dir then up else dn) = - 1 \<or> 0 \<le> (if dir then up else dn)"
          "(if dir then dn else up) = - 1 \<or> 0 \<le> (if dir then dn else up)"
    using assms(6,1,4)
    by (auto dest: af_rooms_cap_feasible)
  show ?thesis
    using assms(7)
  proof(cases rule: af_cancel_seg_cases)
    case (fin k ra rf fl' f2)
    have "0 \<le> (if 0 < k then rf else ra)"
      using assms(1,5) s fin(1,2)
      by (cases "0 < k"; (fastforce dest: af_scan_ra_valid af_scan_rf_valid))
    hence "(if 0 < k then rf else ra) * (if 0 < k then - k else k) \<le> 0"
      by (cases "0 < k") (auto intro: mult_nonneg_nonpos)
    moreover have "\<C> (h \<circ> flow_lookup fl'')
        = \<C> (h \<circ> flow_lookup fl) + h ((if 0 < k then rf else ra) * (if 0 < k then - k else k))"
      using assms(3) af_scan_push_cost[OF assms(2) _ assms(5) fin(1,3)]
            af_push_arc_cost[OF af_push_flow_invar[OF assms(5) fin(3) assms(2)] assms(4) fin(4)]
      by (cases "0 < k"; cases dir;
          (simp add: af_delta_cost_def algebra_simps h_add h_mult cost_h[OF assms(4), symmetric] distinct.simps))
    ultimately show ?thesis
      by (simp)
  next
    case (sw k ra rf fl' f2)
    have "\<C> (h \<circ> flow_lookup fl'') = \<C> (h \<circ> flow_lookup fl) + h (rf * (- k))"
      using assms(3) af_scan_push_cost[OF assms(2) _ assms(5) sw(1,5)]
            af_push_arc_cost[OF af_push_flow_invar[OF assms(5) sw(5) assms(2)] assms(4) sw(6)]
      by (cases dir; (simp add: af_delta_cost_def algebra_simps h_add h_mult cost_h[OF assms(4), symmetric]
        distinct.simps))
    thus ?thesis
      using sw(3)
      by (simp)
  qed (simp)
qed

subsection \<open>Theme E1 --- the iterator arrays implement the multigraph\<close>

text \<open>The two edge-iterator arrays held in the DFS state keep abstracting, at every vertex, to that
      vertex's outgoing/ingoing edges --- i.e.\ @{const multigraph_inv} of the \emph{current} arrays is an
      invariant. It only ever changes by (i) advancing one cell (@{term move_on_edges}, which preserves
      both @{term iset_abstract} and the iterator invariant) or (ii) resetting cells to the pristine
      originals (@{term out_arr} / @{term in_arr}, correct by the standing @{term \<open>multigraph_inv out_arr
        in_arr\<close>}).
      Consequently the arc the DFS scans at the top vertex is a genuine incident arc (E1 proper).\<close>

lemma af_current_out_incident:
  "\<lbrakk>multigraph_inv oa ia; v \<in> \<V>; out_has oa v\<rbrakk> \<Longrightarrow> out_current oa v \<in>
    \<delta>\<^sup>+ v"
  using outg.idx_current[of oa v] outg.idx_has[of oa v] outg.idx_partition_union[of oa v]
  by (fastforce simp: multigraph_inv_def out_graph_inv_def)

lemma af_current_in_incident:
  "\<lbrakk>multigraph_inv oa ia; v \<in> \<V>; in_has ia v\<rbrakk> \<Longrightarrow> in_current ia v \<in>
    \<delta>\<^sup>- v"
  using ing.idx_current[of ia v] ing.idx_has[of ia v] ing.idx_partition_union[of ia v]
  by (fastforce simp: multigraph_inv_def in_graph_inv_def)

lemma af_current_out_endpoint:
  "\<lbrakk>multigraph_inv oa ia; v \<in> \<V>; out_has oa v\<rbrakk> \<Longrightarrow> fst (out_current oa v) = v
    \<and> out_current oa v \<in> \<E>"
  by (fastforce simp: delta_plus_def dest: af_current_out_incident)

lemma af_current_in_endpoint:
  "\<lbrakk>multigraph_inv oa ia; v \<in> \<V>; in_has ia v\<rbrakk> \<Longrightarrow> snd (in_current ia v) = v
    \<and> in_current ia v \<in> \<E>"
  by (fastforce simp: delta_minus_def dest: af_current_in_incident)

lemma multigraph_inv_out_advance:
  "\<lbrakk>multigraph_inv oa ia; out_has oa v; v \<in> \<V>\<rbrakk> \<Longrightarrow> multigraph_inv (out_move oa v)
    ia"
  by (auto simp: multigraph_inv_def out_graph_inv_def outg.idx_has
      outg.idx_move_invar outg.idx_move_abstract)

lemma multigraph_inv_in_advance:
  "\<lbrakk>multigraph_inv oa ia; in_has ia v; v \<in> \<V>\<rbrakk> \<Longrightarrow> multigraph_inv oa (in_move ia v)"
  by (auto simp: multigraph_inv_def in_graph_inv_def ing.idx_has
      ing.idx_move_invar ing.idx_move_abstract)

lemma multigraph_inv_reset:
  "\<lbrakk>multigraph_inv out_arr in_arr; multigraph_inv oa ia; v \<in> \<V>\<rbrakk> \<Longrightarrow>
    multigraph_inv (out_reset oa v) (in_reset ia v)"
  by (auto simp: multigraph_inv_def out_graph_inv_def in_graph_inv_def
      outg.idx_reset_invar outg.idx_reset_abstract ing.idx_reset_invar ing.idx_reset_abstract)

text \<open>Every stack vertex is a vertex of the multigraph (a push only ever adds an endpoint of a scanned
      arc @{term \<open>a \<in> \<E>\<close>}); needed to invoke E1 at the top vertex.\<close>

definition "AF_invar_V st \<longleftrightarrow> set (af_vstack st) \<subseteq> \<V>"

definition "AF_invar_iter st \<longleftrightarrow> multigraph_inv (af_out_arr st) (af_in_arr st)"

lemma af_handle_invar_V:
  assumes "AF_invar_V st" "a \<in> \<E>"
  shows "AF_invar_V (af_handle st a dir)"
  by (rule af_handle_cases[of a st dir]; insert assms;
      (auto simp: AF_invar_V_def intro: fst_E_V snd_E_V dest: set_drop_subset[THEN subsetD]
        split: if_splits))

lemma AF_invar_V_out_arr[simp]: "AF_invar_V (st\<lparr>af_out_arr := X\<rparr>) = AF_invar_V st"
  by (simp add: AF_invar_V_def)

lemma AF_invar_V_in_arr[simp]: "AF_invar_V (st\<lparr>af_in_arr := X\<rparr>) = AF_invar_V st"
  by (simp add: AF_invar_V_def)

lemma AF_invar_V_holds_1[invar_holds_intros]:
  assumes "AF_DFS_call_1_conds st" "AF_invar_V st" "AF_invar_iter st"
  shows "AF_invar_V (AF_DFS_upd1 st)"
proof-
  have "hd (af_vstack st) \<in> \<V>" "out_has (af_out_arr st) (hd (af_vstack st))"
    using assms(1,2)
    by (auto elim!: call_cond_elims simp: AF_invar_V_def)
  thus ?thesis
    using af_current_out_endpoint[of "af_out_arr st" "af_in_arr st" "hd (af_vstack st)"] assms(2,3)
    by (auto simp: AF_DFS_upd1_def AF_invar_iter_def Let_def intro!: af_handle_invar_V)
qed

lemma AF_invar_V_holds_2[invar_holds_intros]:
  assumes "AF_DFS_call_2_conds st" "AF_invar_V st" "AF_invar_iter st"
  shows "AF_invar_V (AF_DFS_upd2 st)"
proof-
  have "hd (af_vstack st) \<in> \<V>" "in_has (af_in_arr st) (hd (af_vstack st))"
    using assms(1,2)
    by (auto elim!: call_cond_elims simp: AF_invar_V_def)
  thus ?thesis
    using af_current_in_endpoint[of "af_out_arr st" "af_in_arr st" "hd (af_vstack st)"] assms(2,3)
    by (auto simp: AF_DFS_upd2_def AF_invar_iter_def Let_def intro!: af_handle_invar_V)
qed

lemma AF_invar_V_holds_3[invar_holds_intros]:
  "\<lbrakk>AF_DFS_call_3_conds st; AF_invar_V st\<rbrakk> \<Longrightarrow> AF_invar_V (AF_DFS_upd3 st)"
  by (cases "af_vstack st") (auto simp: AF_DFS_upd3_def AF_invar_V_def)

lemma af_reset_state_upd_iter:
  "\<lbrakk>multigraph_inv out_arr in_arr; v \<in> \<V>; AF_invar_iter st\<rbrakk>
   \<Longrightarrow> AF_invar_iter (af_reset v (st \<lparr>af_state := st_upd (af_state st) v Unseen\<rparr>))"
  by (auto simp: AF_invar_iter_def af_reset_def intro: multigraph_inv_reset)

lemma af_reset_unsee_seg_iter:
  "\<lbrakk>set vs \<subseteq> \<V>; multigraph_inv out_arr in_arr; AF_invar_iter st\<rbrakk>
   \<Longrightarrow> AF_invar_iter (af_reset_unsee_seg n vs st)"
  by (induction n vs st rule: af_reset_unsee_seg.induct) (auto intro: af_reset_state_upd_iter)

lemma af_handle_iter:
  assumes "multigraph_inv out_arr in_arr" "AF_invar_iter st" "AF_invar_V st"
  shows "AF_invar_iter (af_handle st a dir)"
proof(cases rule: af_handle_cases_exec[of a st dir])
  case (cancel up dn fl m')
  show ?thesis
    unfolding cancel(7)
    using assms
    by (intro af_reset_unsee_seg_iter) (auto simp: AF_invar_iter_def AF_invar_V_def)
qed (auto simp: AF_invar_iter_def assms(2)[unfolded AF_invar_iter_def])

lemma AF_invar_iter_holds_1[invar_holds_intros]:
  assumes "multigraph_inv out_arr in_arr" "AF_DFS_call_1_conds st" "AF_invar_iter st" "AF_invar_V st"
  shows "AF_invar_iter (AF_DFS_upd1 st)"
proof-
  have "AF_invar_iter (st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack st))\<rparr>)"
    using assms(2-4)
    by (cases "af_vstack st")
       (auto simp: AF_invar_iter_def AF_DFS_call_1_conds_def AF_invar_V_def
             intro!: multigraph_inv_out_advance)
  thus ?thesis
    using assms(4)
    by (auto simp: AF_DFS_upd1_def Let_def intro!: af_handle_iter[OF assms(1)])
qed

lemma AF_invar_iter_holds_2[invar_holds_intros]:
  assumes "multigraph_inv out_arr in_arr" "AF_DFS_call_2_conds st" "AF_invar_iter st" "AF_invar_V st"
  shows "AF_invar_iter (AF_DFS_upd2 st)"
proof-
  have "AF_invar_iter (st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack st))\<rparr>)"
    using assms(2-4)
    by (cases "af_vstack st")
       (auto simp: AF_invar_iter_def AF_DFS_call_2_conds_def AF_invar_V_def
             intro!: multigraph_inv_in_advance)
  thus ?thesis
    using assms(4)
    by (auto simp: AF_DFS_upd2_def Let_def intro!: af_handle_iter[OF assms(1)])
qed

lemma AF_invar_iter_holds_3[invar_holds_intros]:
  "\<lbrakk>AF_DFS_call_3_conds st; AF_invar_iter st\<rbrakk> \<Longrightarrow> AF_invar_iter (AF_DFS_upd3 st)"
  by (auto simp: AF_DFS_upd3_def AF_invar_iter_def)

subsection \<open>Theme C --- the stack is a tagged (free) trail; and stack vertices are graph vertices\<close>

text \<open>The three stacks encode a walk in the graph: for each @{term i}, the arc @{term \<open>af_estack st !
    i\<close>}
      with tag @{term \<open>af_dstack st ! i\<close>} joins @{term \<open>af_vstack st ! i\<close>} (its head, the
        child) to
      @{term \<open>af_vstack st ! Suc i\<close>} (its tail, the parent). This is the flow-independent \emph{structure}
      of Theme C (the freeness of the arcs is a separate, D2-coupled clause); it survives every DFS step ---
      push extends the walk by the just-scanned incident arc (E1), truncate/pop keep a suffix.\<close>

definition "AF_invar_3 st \<longleftrightarrow>
  (\<forall>i < length (af_estack st).
     (if af_dstack st ! i then snd (af_estack st ! i) else fst (af_estack st ! i)) = af_vstack st ! i \<and>
     (if af_dstack st ! i then fst (af_estack st ! i) else snd (af_estack st ! i)) = af_vstack st ! Suc i)"

text \<open>A raw-list view of the trail, to reason about the @{text Cons} (push) case free of record clutter.\<close>

definition "af_trail P es ds \<longleftrightarrow>
  (\<forall>i<length es. (if ds!i then snd (es!i) else fst (es!i)) = P!i \<and> (if ds!i then fst (es!i) else snd
    (es!i)) = P!Suc i)"

lemma AF_invar_3_conv: "AF_invar_3 st = af_trail (af_vstack st) (af_estack st) (af_dstack st)"
  by (simp add: AF_invar_3_def af_trail_def)

lemma af_trail_Cons:
  "\<lbrakk>(if dir then fst a else snd a) = hd P; P \<noteq> []; af_trail P es ds\<rbrakk>
   \<Longrightarrow> af_trail ((if dir then snd a else fst a) # P) (a # es) (dir # ds)"
  by (auto simp: af_trail_def All_less_Suc2 hd_conv_nth)

text \<open>The tail of a trail is a trail (index shift), used to peel the first arc in the push induction.\<close>

lemma af_trail_tl: "af_trail (u # P) (a # es) (d # ds) \<Longrightarrow> af_trail P es ds"
  by (auto simp: af_trail_def All_less_Suc2)

text \<open>A suffix (drop the top @{term m} of all three stacks in lockstep) of a trail is a trail --- this covers
      both @{const AF_DFS_upd3} (pop, @{term \<open>m = 1\<close>}) and the back-edge truncation.\<close>

lemma af_trail_drop:
  "\<lbrakk>af_trail P es ds; length ds = length es; Suc (length es) = length P\<rbrakk>
   \<Longrightarrow> af_trail (drop m P) (drop m es) (drop m ds)"
proof(induction m arbitrary: P es ds)
  case (Suc m)
  show ?case
  proof(cases es)
    case Nil
    thus ?thesis
      by (simp add: af_trail_def)
  next
    case (Cons a es')
    then obtain u P' d ds' where "P = u # P'" "ds = d # ds'"
      using Suc.prems
      by (cases P; cases ds) auto
    thus ?thesis
      using Suc.IH af_trail_tl Suc.prems Cons
      by (auto)
  qed
qed (simp)

lemma AF_invar_3_drop:
  "\<lbrakk>AF_invar_3 st; Suc (length (af_estack st)) = length (af_vstack st);
    length (af_dstack st) = length (af_estack st)\<rbrakk>
   \<Longrightarrow> AF_invar_3 (st\<lparr>af_vstack := drop m (af_vstack st), af_estack := drop m (af_estack st),
                       af_dstack := drop m (af_dstack st)\<rparr>)"
  by (simp add: AF_invar_3_conv af_trail_drop)

lemma AF_invar_3_push:
  "\<lbrakk>AF_invar_3 st; (if dir then fst a else snd a) = hd (af_vstack st); af_vstack st \<noteq> []\<rbrakk>
   \<Longrightarrow> AF_invar_3 (st\<lparr>af_vstack := (if dir then snd a else fst a) # af_vstack st,
                       af_estack := a # af_estack st, af_dstack := dir # af_dstack st\<rparr>)"
  by (simp add: AF_invar_3_conv af_trail_Cons)

lemma af_reset_unsee_seg_invar_3: "AF_invar_3 (af_reset_unsee_seg n vs st) = AF_invar_3 st"
  by (simp add: AF_invar_3_def)

subsection \<open>Cancellation preserves excess (balance/divergence)\<close>

text \<open>Pushing @{term \<gamma>} around the cancellation cycle changes no vertex excess (Theme D1's
      divergence half). The argument needs \emph{no} arc-distinctness: each single-arc push shifts the
      excess of its two endpoints by @{term \<gamma>} (up to sign), and along the trail these boundary
      terms telescope, the closing arc cancelling the two remaining ends. First, a pointwise sum
      update.\<close>

lemma sum_fun_upd_delta:
  assumes "finite S"
  shows "sum (g(a := g a + (\<delta>::real))) S = sum g S + (if a \<in> S then \<delta> else 0)"
proof(cases "a \<in> S")
  case True
  have "sum (g(a := g a + \<delta>)) (S - {a}) = sum g (S - {a})"
    by (intro sum.cong) auto
  thus ?thesis
    using True
    by (simp add: sum.remove[OF assms True])
qed (auto intro: sum.cong)

text \<open>A single arc push shifts the excess of its head vertex and its tail vertex by opposite signed
      amounts @{term \<gamma>} (or its negation, per the push direction); a self-loop leaves the excess
      unchanged.\<close>

lemma af_push_arc_ex:
  assumes "flow_invar fl" "a \<in> \<E>" "af_push_arc \<gamma> a dir fl = (fl', f')"
  shows "ex (h \<circ> flow_lookup fl') v = ex (h \<circ> flow_lookup fl) v
           + (if dir then h \<gamma> else - h \<gamma>) * ((if snd a = v then 1 else 0) - (if fst a = v then 1 else 0))"
proof-
  have f: "(\<lambda>e. h (flow_lookup fl' e))
        = (\<lambda>e. h (flow_lookup fl e))(a := h (flow_lookup fl a) + (if dir then h \<gamma> else - h \<gamma>))"
    using assms
    by (auto simp: af_push_arc_def Let_def flow_array.fixed_univ_map_upd h_add)
  have "(\<Sum>e\<in>\<delta>\<^sup>- v. h (flow_lookup fl' e))
        = (\<Sum>e\<in>\<delta>\<^sup>- v. h (flow_lookup fl e)) + (if a \<in> \<delta>\<^sup>- v then (if dir then h
          \<gamma> else - h \<gamma>) else 0)"
    unfolding f
    by (rule sum_fun_upd_delta[OF delta_minus_finite])
  moreover have "(\<Sum>e\<in>\<delta>\<^sup>+ v. h (flow_lookup fl' e))
        = (\<Sum>e\<in>\<delta>\<^sup>+ v. h (flow_lookup fl e)) + (if a \<in> \<delta>\<^sup>+ v then (if dir then h
          \<gamma> else - h \<gamma>) else 0)"
    unfolding f
    by (rule sum_fun_upd_delta[OF delta_plus_finite])
  moreover have "(a \<in> \<delta>\<^sup>- v) = (snd a = v)" "(a \<in> \<delta>\<^sup>+ v) = (fst a = v)"
    using assms(2)
    by (auto simp: delta_minus_def delta_plus_def)
  ultimately show ?thesis
    by (simp add: ex_def algebra_simps)
qed

subsection \<open>Self-loop normaliser: excess, cost and feasibility\<close>

lemma flow_upd_as_push: "af_push_arc (v - flow_lookup fl a) a True fl = (flow_upd fl a v, v)"
  by (simp add: af_push_arc_def Let_def)

lemma ex_flow_upd_selfloop:
  "\<lbrakk>a \<in> \<E>; fst a = snd a; flow_invar fl\<rbrakk>
   \<Longrightarrow> ex (h \<circ> flow_lookup (flow_upd fl a v)) w = ex (h \<circ> flow_lookup fl) w"
  using af_push_arc_ex[OF _ _ flow_upd_as_push]
  by simp

lemma cost_flow_upd:
  "\<lbrakk>a \<in> \<E>; flow_invar fl\<rbrakk>
   \<Longrightarrow> \<C> (h \<circ> flow_lookup (flow_upd fl a v)) = \<C> (h \<circ> flow_lookup fl) + h (v -
     flow_lookup fl a) * \<c> a"
  using af_push_arc_cost[OF _ _ flow_upd_as_push]
  by simp

lemma af_selfloop_handle_ex:
  "\<lbrakk>a \<in> \<E>; fst a = snd a; flow_invar (af_flow st)\<rbrakk>
   \<Longrightarrow> ex (h \<circ> flow_lookup (af_flow (af_selfloop_handle st a))) v = ex (h \<circ> flow_lookup
     (af_flow st)) v"
  using af_selfloop_handle_flow_cases[of st a] ex_flow_upd_selfloop
  by auto

lemma cap_nonneg: "\<lbrakk>a \<in> \<E>; cap a \<noteq> - 1\<rbrakk> \<Longrightarrow> 0 \<le> cap a"
  using cap_encoding[of a] u_non_neg[of a]
  by (auto simp: zero_ereal_def split: if_splits)

lemma af_selfloop_handle_flow_scases:
  "a \<in> \<E> \<Longrightarrow> af_flow (af_selfloop_handle st a) = af_flow st
   \<or> (af_flow (af_selfloop_handle st a) = flow_upd (af_flow st) a 0 \<and> \<not> \<c> a < 0)
   \<or> (af_flow (af_selfloop_handle st a) = flow_upd (af_flow st) a (cap a) \<and> \<c> a < 0 \<and> cap a \<noteq>
     - 1)"
  by (auto simp: af_selfloop_handle_def Let_def cost_neg_bridge split: if_splits)

lemma af_selfloop_handle_feasible:
  "\<lbrakk>a \<in> \<E>; flow_invar (af_flow st); af_cap_feasible (af_flow st)\<rbrakk> \<Longrightarrow>
    af_cap_feasible (af_flow (af_selfloop_handle st a))"
  using af_selfloop_handle_flow_scases[of a st] cap_nonneg[of a]
  by (auto simp: af_cap_feasible_def flow_array.fixed_univ_map_upd split: if_splits)

lemma af_selfloop_handle_cost_le:
  assumes "a \<in> \<E>" "flow_invar (af_flow st)" "af_cap_feasible (af_flow st)"
  shows "\<C> (h \<circ> flow_lookup (af_flow (af_selfloop_handle st a))) \<le> \<C> (h \<circ> flow_lookup (af_flow
    st))"
proof-
  have "0 \<le> flow_lookup (af_flow st) a" "cap a = - 1 \<or> flow_lookup (af_flow st) a \<le> cap a"
    using assms(1,3)
    by (auto simp: af_cap_feasible_def)
  thus ?thesis
    using af_selfloop_handle_flow_scases[OF assms(1), of st] cost_flow_upd[OF assms(1,2), of 0]
          cost_flow_upd[OF assms(1,2), of "cap a"]
          mult_nonneg_nonpos[of "h (cap a) - h (flow_lookup (af_flow st) a)" "\<c> a"]
    by (auto intro: mult_nonpos_nonneg simp: not_less)
qed

text \<open>Pushing @{term \<gamma>} along the trail prefix that reaches @{term x}: the excess of every vertex is
      unchanged except the two ends of the sub-walk --- the start @{term \<open>hd vs\<close>} and the reached
      @{term x} --- which shift by @{term \<gamma>} up to sign. Proved by induction on the fused push,
      telescoping the per-arc boundary shifts; the coupling @{term \<open>Suc (length es) = length vs\<close>}
      rules out running off the stack before reaching @{term x}.\<close>

lemma af_push_ex:
  "\<lbrakk>flow_invar fl; af_trail vs es ds; set es \<subseteq> \<E>; Suc (length es) = length vs; length ds = length
    es;
    x \<in> set (tl vs); af_push \<gamma> x vs es ds flip fl = (fl', m')\<rbrakk>
   \<Longrightarrow> ex (h \<circ> flow_lookup fl') v
       = ex (h \<circ> flow_lookup fl) v
         + (if flip then - h \<gamma> else h \<gamma>) * ((if hd vs = v then 1 else 0) - (if x = v then 1 else 0))"
proof(induction \<gamma> x vs es ds flip fl arbitrary: fl' m' rule: af_push.induct)
  case (1 \<gamma> x u v1 vs a es d ds flip fl)
  obtain fl1 fv where p1: "af_push_arc \<gamma> a (d \<noteq> flip) fl = (fl1, fv)"
    by fastforce
  have a: "a \<in> \<E>" "set es \<subseteq> \<E>"
    using 1(4)
    by auto
  have "(if d then snd a else fst a) = u \<and> (if d then fst a else snd a) = v1"
    using 1(3)
    by (fastforce simp: af_trail_def)
  hence step: "ex (h \<circ> flow_lookup fl1) v = ex (h \<circ> flow_lookup fl) v
                + (if flip then - h \<gamma> else h \<gamma>) * ((if u = v then 1 else 0) - (if v1 = v then 1 else 0))"
    using af_push_arc_ex[OF 1(2) a(1) p1]
    by (cases d; cases flip; auto simp: algebra_simps)
  show ?case
  proof(cases "v1 = x")
    case True
    thus ?thesis
      using 1(8) p1 step
      by (auto simp: comp_def)
  next
    case False
    obtain fl2 r where p2: "af_push \<gamma> x (v1 # vs) es ds flip fl1 = (fl2, r)"
      by fastforce
    have "Suc (length es) = length (v1 # vs)" "length ds = length es" "x \<in> set (tl (v1 # vs))"
      using 1(5-7) False
      by auto
    moreover have "fl' = fl2"
      using 1(8) p1 p2 False
      by auto
    ultimately show ?thesis
      using 1(1)[OF p1[symmetric] refl False af_push_arc_flow_invar[OF a(1) p1 1(2)]
                    af_trail_tl[OF 1(3)] a(2) _ _ _ p2] step
      by (auto simp: algebra_simps comp_def)
  qed
qed (auto simp: Suc_length_conv comp_def)

text \<open>A back-edge cancellation preserves every vertex's excess: the push around the trail prefix
      shifts the two ends (@{term \<open>hd vs\<close>} and @{term x}), and the closing arc @{term a} --- which
      connects exactly those two vertices --- cancels both shifts. Holds in all three cancellation
      branches (finite bottleneck, the cost-neutral finite ``switch'', and the unbounded no-op).\<close>

lemma af_cancel_seg_ex_pres:
  assumes "flow_invar fl" "af_trail vs es ds" "set es \<subseteq> \<E>" "a \<in> \<E>"
    "Suc (length es) = length vs" "length ds = length es" "x \<in> set (tl vs)"
    "(if dir then fst a else snd a) = hd vs" "(if dir then snd a else fst a) = x"
    "af_cancel_seg up dn x vs es ds a dir fl = (fl'', m', ubd)"
  shows "ex (h \<circ> flow_lookup fl'') v = ex (h \<circ> flow_lookup fl) v"
  using assms(10)
proof(cases rule: af_cancel_seg_cases)
  case (fin k ra rf fl' f2)
  thus ?thesis
    using af_push_ex[OF assms(1-3,5-7) fin(3)] assms(8,9)
          af_push_arc_ex[OF af_push_flow_invar[OF assms(3) fin(3) assms(1)] assms(4) fin(4)]
    by (cases dir; cases "0 < k"; auto simp: algebra_simps comp_def)
next
  case (sw k ra rf fl' f2)
  thus ?thesis
    using af_push_ex[OF assms(1-3,5-7) sw(5)] assms(8,9)
          af_push_arc_ex[OF af_push_flow_invar[OF assms(3) sw(5) assms(1)] assms(4) sw(6)]
    by (cases dir; auto simp: algebra_simps comp_def)
qed simp

text \<open>The self-loop cancellation (empty stack, closing arc @{term a} a genuine loop @{term \<open>fst a = snd
    a\<close>})
      trivially preserves excess: the push is over the empty trail and the closing loop-arc shifts its
      head and tail --- the same vertex --- by cancelling amounts.\<close>

lemma af_cancel_seg_ex_pres_selfloop:
  "\<lbrakk>flow_invar fl; a \<in> \<E>; fst a = snd a; af_cancel_seg up dn x [] [] [] a dir fl = (fl'', m',
    ubd)\<rbrakk> \<Longrightarrow> ex (h \<circ> flow_lookup fl'') v = ex (h \<circ> flow_lookup fl) v"
  by (auto simp: af_cancel_seg_def af_push_arc_def Let_def ex_flow_upd_selfloop
      split: prod.splits if_splits)

text \<open>Preservation of the trail structure across @{const af_handle}, given the \emph{incidence} precondition
      (the arc @{term a} leaves the current top vertex in direction @{term dir}) --- which the DFS discharges
      by E1. Push uses @{thm [source] AF_invar_3_push}; the back-edge branch uses @{thm [source] AF_invar_3_drop}
      (the reached ancestor's segment survives); all other branches leave the three stacks untouched.\<close>

lemma af_handle_invar_3:
  assumes "AF_invar_1 st" "AF_invar_2 st" "AF_invar_3 st"
    "(if dir then fst a else snd a) = hd (af_vstack st)" "af_vstack st \<noteq> []" "a \<in> \<E>"
  shows "AF_invar_3 (af_handle st a dir)"
  using assms(6)
proof(cases rule: af_handle_cases[of a st dir])
  case (push up dn)
  thus ?thesis
    using AF_invar_3_push[OF assms(3-5)]
    by (simp add: AF_invar_3_conv)
next
  case (cancel up dn fl m')
  have cpl: "Suc (length (af_estack st)) = length (af_vstack st)" "length (af_dstack st) = length (af_estack st)"
    using assms(2,5)
    by (auto simp: AF_invar_2_def)
  show ?thesis
    using cancel(7) AF_invar_3_drop[OF assms(3) cpl, of m']
    by (simp add: AF_invar_3_conv af_reset_unsee_seg_invar_3)
qed (insert assms(3), simp_all add: AF_invar_3_conv)

text \<open>Lifting the trail structure and @{const AF_invar_V} to the whole inner DFS. The out/in edge-array
      advances leave both invariants (they touch neither the stacks nor the flow); the push branch discharges
      \<open>af_handle_invar_3\<close>'s incidence precondition (and \<open>af_handle_invar_V\<close>'s @{term
        \<open>a \<in> \<E>\<close>})
      through E1 at the top vertex.\<close>

lemma AF_invar_3_out_arr[simp]: "AF_invar_3 (st\<lparr>af_out_arr := X\<rparr>) = AF_invar_3 st"
  by (simp add: AF_invar_3_def)

lemma AF_invar_3_in_arr[simp]: "AF_invar_3 (st\<lparr>af_in_arr := X\<rparr>) = AF_invar_3 st"
  by (simp add: AF_invar_3_def)

lemma AF_invar_3_holds_1[invar_holds_intros]:
  assumes "AF_DFS_call_1_conds st" "AF_invar_1 st" "AF_invar_2 st" "AF_invar_3 st" "AF_invar_iter st"
    "AF_invar_V st"
  shows "AF_invar_3 (AF_DFS_upd1 st)"
proof-
  have "af_vstack st \<noteq> []" "out_has (af_out_arr st) (hd (af_vstack st))" "hd (af_vstack st) \<in> \<V>"
    using assms(1,6)
    by (auto elim!: call_cond_elims simp: AF_invar_V_def)
  thus ?thesis
    using af_current_out_endpoint[of "af_out_arr st" "af_in_arr st" "hd (af_vstack st)"] assms(2-5)
    by (auto simp: AF_DFS_upd1_def Let_def AF_invar_iter_def
             intro!: af_handle_invar_3 AF_invar_1_out_advance)
qed

lemma AF_invar_3_holds_2[invar_holds_intros]:
  assumes "AF_DFS_call_2_conds st" "AF_invar_1 st" "AF_invar_2 st" "AF_invar_3 st" "AF_invar_iter st"
    "AF_invar_V st"
  shows "AF_invar_3 (AF_DFS_upd2 st)"
proof-
  have "af_vstack st \<noteq> []" "in_has (af_in_arr st) (hd (af_vstack st))" "hd (af_vstack st) \<in> \<V>"
    using assms(1,6)
    by (auto elim!: call_cond_elims simp: AF_invar_V_def)
  thus ?thesis
    using af_current_in_endpoint[of "af_out_arr st" "af_in_arr st" "hd (af_vstack st)"] assms(2-5)
    by (auto simp: AF_DFS_upd2_def Let_def AF_invar_iter_def
             intro!: af_handle_invar_3 AF_invar_1_in_advance)
qed

lemma AF_invar_3_holds_3[invar_holds_intros]:
  assumes "AF_DFS_call_3_conds st" "AF_invar_2 st" "AF_invar_3 st"
  shows "AF_invar_3 (AF_DFS_upd3 st)"
proof-
  have "Suc (length (af_estack st)) = length (af_vstack st)" "length (af_dstack st) = length (af_estack st)"
    using assms(1,2)
    by (auto elim!: call_cond_elims simp: AF_invar_2_def)
  thus ?thesis
    using AF_invar_3_drop[OF assms(3), of "Suc 0"]
    by (simp add: AF_DFS_upd3_def AF_invar_3_conv drop_Suc)
qed

subsection \<open>Theme D2 --- the free set shrinks: survivors of a cancellation stay free\<close>

text \<open>The free-arc guard the algorithm actually tests (@{term \<open>0 < dn \<and> (up = - 1 \<or> 0 <
    up)\<close>} on the rooms)
      coincides with @{const af_arc_free} on a feasible flow.\<close>

lemma af_guard_free:
  "\<lbrakk>af_rooms fl a = (up, dn); cap a = - 1 \<or> flow_lookup fl a \<le> cap a\<rbrakk>
   \<Longrightarrow> (0 < dn \<and> (up = - 1 \<or> 0 < up)) = af_arc_free fl a"
  by (auto simp: af_rooms_def af_arc_free_def Let_def split: if_splits)

text \<open>A push leaves its arc free exactly when the fused saturation test (on the value it wrote) says so.\<close>

lemma af_saturated_free:
  "\<lbrakk>a \<in> \<E>; flow_invar fl; af_push_arc \<gamma> a dir fl = (fl', f'); \<not> af_saturated f' a\<rbrakk>
   \<Longrightarrow> af_arc_free fl' a"
  using af_push_arc_at[of a fl \<gamma> dir fl' f']
  by (auto simp: af_saturated_def af_arc_free_def Let_def)

lemma af_saturated_notfree:
  "\<lbrakk>a \<in> \<E>; flow_invar fl; af_push_arc \<gamma> a dir fl = (fl', f'); af_saturated f' a\<rbrakk>
   \<Longrightarrow> \<not> af_arc_free fl' a"
  by (auto simp: af_saturated_def af_arc_free_def Let_def dest: af_push_arc_at)

text \<open>The crux of D2. The push pass returns the truncate count @{term \<open>m'\<close>} = one past the
    \emph{deepest}
      arc that saturated (or @{term 0} if none), so every arc from index @{term \<open>m'\<close>} onward stays free ---
      the surviving suffix of the cancellation is entirely free. This is purely combinatorial in the
      saturation flags (no room bound needed): distinctness keeps each arc's written value its own.\<close>

lemma af_push_survivor:
  "\<lbrakk>flow_invar fl; distinct es; \<forall>b\<in>set es. af_arc_free fl b;
    af_push \<gamma> x vs es ds flip fl = (fl', m'); set es \<subseteq> \<E>\<rbrakk>
   \<Longrightarrow> \<forall>i. i < length es \<longrightarrow> m' \<le> i \<longrightarrow> af_arc_free fl' (es ! i)"
proof(induction \<gamma> x vs es ds flip fl arbitrary: fl' m' rule: af_push.induct)
  case (1 \<gamma> x u v1 vs a es d ds flip fl)
  obtain fl1 f where p1: "af_push_arc \<gamma> a (d \<noteq> flip) fl = (fl1, f)"
    by (fastforce)
  have a: "a \<in> \<E>" "set es \<subseteq> \<E>" "a \<notin> set es" "distinct es"
    using 1(3,6)
    by (auto)
  have fl1: "flow_invar fl1" "\<not> af_saturated f a \<Longrightarrow> af_arc_free fl1 a"
    using af_push_arc_flow_invar[OF a(1) p1 1(2)] af_saturated_free[OF a(1) 1(2) p1]
    by (auto)
  have "\<forall>b\<in>set es. flow_lookup fl1 b = flow_lookup fl b"
    using a(3)
    by (auto intro: af_push_arc_flow_off[OF a(1) 1(2) _ p1])
  hence free: "\<forall>b\<in>set es. af_arc_free fl1 b"
    using 1(4)
    by (simp add: af_arc_free_def)
  show ?case
  proof(cases "v1 = x")
    case True
    thus ?thesis
      using 1(5) p1 fl1(2) free
      by (auto simp: Let_def All_less_Suc2 split: if_splits)
  next
    case False
    obtain fl2 r where p2: "af_push \<gamma> x (v1 # vs) es ds flip fl1 = (fl2, r)"
      by (fastforce)
    have "\<not> af_saturated f a \<Longrightarrow> af_arc_free fl2 a"
      using fl1(2) af_push_flow_off a(2) fl1(1) a(3) p2
      by (simp add: af_arc_free_def)
    thus ?thesis
      using 1(1)[OF p1[symmetric] refl False fl1(1) a(4) free p2 a(2)]
            1(5) p1 p2 False
      by (auto simp: Let_def All_less_Suc2 split: if_splits)
  qed
qed (auto)

text \<open>Lifted to a whole cancellation: since the closing arc is off the walk (@{term \<open>a \<notin> set
    es\<close>}) it
      does not disturb the surviving arcs. Every arc of @{term es} from index @{term \<open>m'\<close>} onward is free
      in the post-cancellation flow (the unbounded-flag branch leaves the flow, hence freeness, untouched).\<close>

lemma af_cancel_seg_survivor_free:
  assumes "flow_invar fl" "distinct es" "\<forall>b\<in>set es. af_arc_free fl b" "a \<notin> set es" "set es
    \<subseteq> \<E>"
    "a \<in> \<E>" "af_cancel_seg up dn x vs es ds a dir fl = (fl'', m', ubd)" "i < length es" "m' \<le> i"
  shows "af_arc_free fl'' (es ! i)"
proof-
  have ne: "es ! i \<noteq> a"
    using assms(4) nth_mem assms(8)
    by (auto)
  show ?thesis
    using assms(7)
  proof(cases rule: af_cancel_seg_cases)
    case (fin k ra rf fl' f2)
    thus ?thesis
      using af_push_survivor assms(1-3) fin(3) assms(5) assms(8,9)
            af_push_arc_flow_off[OF assms(6) af_push_flow_invar[OF assms(5) fin(3) assms(1)] ne fin(4)]
      by (auto simp: af_arc_free_def)
  next
    case (sw k ra rf fl' f2)
    thus ?thesis
      using af_push_survivor assms(1-3) sw(5) assms(5) assms(8,9)
            af_push_arc_flow_off[OF assms(6) af_push_flow_invar[OF assms(5) sw(5) assms(1)] ne sw(6)]
      by (auto simp: af_arc_free_def)
  qed (insert assms(3) nth_mem[OF assms(8)], (auto))
qed

subsection \<open>Theme C (freeness) --- the stack arcs stay free, and the closing arc is off the stack\<close>

text \<open>The two endpoints of a stack arc are exactly its two trail vertices; hence a stack arc joins
      \emph{distinct} vertices, so no self-loop (and no arc incident to the top from a non-parent) can be
      a stack arc, and (from distinct @{term \<open>af_vstack st\<close>}) the arc list itself is distinct.\<close>

lemma trail_endpoints:
  "\<lbrakk>AF_invar_3 st; i < length (af_estack st)\<rbrakk>
   \<Longrightarrow> {fst (af_estack st ! i), snd (af_estack st ! i)} = {af_vstack st ! i, af_vstack st ! Suc i}"
  by (auto simp: AF_invar_3_def split: if_splits)

lemma estack_distinct:
  assumes "AF_invar_2 st" "AF_invar_3 st"
  shows "distinct (af_estack st)"
proof(cases "af_estack st = []")
  case False
  hence d: "distinct (af_vstack st)" "Suc (length (af_estack st)) = length (af_vstack st)"
    using assms(1)
    by (auto simp: AF_invar_2_def)
  show ?thesis
  proof(subst distinct_conv_nth, intro allI impI notI)
    fix i j
    assume ij: "i < length (af_estack st)" "j < length (af_estack st)" "i \<noteq> j"
      "af_estack st ! i = af_estack st ! j"
    hence "{af_vstack st ! i, af_vstack st ! Suc i} = {af_vstack st ! j, af_vstack st ! Suc j}"
      using trail_endpoints[of st i] assms(2) ij(1) trail_endpoints[of st j] assms(2) ij(2)
      by (simp)
    thus False
      using ij d nth_eq_iff_index_eq[of "af_vstack st"] d(1)
      by (auto simp: doubleton_eq_iff)
  qed
qed (simp)

lemma a_notin_estack_selfloop:
  assumes "AF_invar_2 st" "AF_invar_3 st" "fst a = snd a"
  shows "a \<notin> set (af_estack st)"
proof
  assume "a \<in> set (af_estack st)"
  then obtain i where i: "i < length (af_estack st)" "af_estack st ! i = a"
    by (auto simp: in_set_conv_nth)
  moreover have "distinct (af_vstack st)" "Suc (length (af_estack st)) = length (af_vstack st)"
    using assms(1) i(1)
    by (auto simp: AF_invar_2_def)
  ultimately show False
    using trail_endpoints[of st i] assms(2) i(1) assms(3) nth_eq_iff_index_eq[of "af_vstack st" i "Suc i"]
    by (auto simp: doubleton_eq_iff)
qed

lemma a_notin_estack_incident:
  assumes "AF_invar_2 st" "AF_invar_3 st" "hd (af_vstack st) \<in> {fst a, snd a}" "af_vstack st \<noteq> []"
    "\<not> (af_estack st \<noteq> [] \<and> a = hd (af_estack st))"
  shows "a \<notin> set (af_estack st)"
proof
  assume "a \<in> set (af_estack st)"
  then obtain j where j: "j < length (af_estack st)" "af_estack st ! j = a"
    by (auto simp: in_set_conv_nth)
  moreover have "distinct (af_vstack st)" "Suc (length (af_estack st)) = length (af_vstack st)"
    using assms(1) j(1)
    by (auto simp: AF_invar_2_def)
  moreover have "j \<noteq> 0"
    using j assms(5) hd_conv_nth[of "af_estack st"]
    by (cases j) auto
  ultimately show False
    using trail_endpoints[of st j] assms(2) j(1) assms(3,4) nth_eq_iff_index_eq[of "af_vstack st" 0 j]
          nth_eq_iff_index_eq[of "af_vstack st" 0 "Suc j"]
    by (auto simp: hd_conv_nth doubleton_eq_iff)
qed

text \<open>State-level flow invariants: the stack arcs are edges, the flow is feasible, and every stack arc is
      free. Feasibility uses D1; freeness uses D2
      (@{thm [source] af_cancel_seg_survivor_free}) for the surviving cancelled segment and the
        guard\<open>\<Leftrightarrow>\<close>free
      equivalence for the push. All three are preserved across @{const af_handle} given the E1 incidence
      (@{term \<open>a \<in> \<E>\<close>} and @{term \<open>(if dir then fst a else snd a) = hd (af_vstack
        st)\<close>}).\<close>

definition "AF_invar_estE st \<longleftrightarrow> set (af_estack st) \<subseteq> \<E>"

lemma af_handle_invar_estE:
  assumes "AF_invar_estE st" "a \<in> \<E>"
  shows "AF_invar_estE (af_handle st a dir)"
  using assms(2)
proof(cases rule: af_handle_cases[of a st dir])
  case (cancel up dn fl m')
  thus ?thesis
    using assms(1) set_drop_subset[of m' "af_estack st"]
    by (auto simp: AF_invar_estE_def)
qed (insert assms, auto simp: AF_invar_estE_def)

definition "AF_invar_feas st \<longleftrightarrow> af_cap_feasible (af_flow st)"

lemma af_handle_invar_feas:
  assumes "AF_invar_1 st" "AF_invar_2 st" "AF_invar_3 st" "AF_invar_feas st" "AF_invar_estE st" "a \<in> \<E>"
    "(if dir then fst a else snd a) = hd (af_vstack st)" "af_vstack st \<noteq> []"
  shows "AF_invar_feas (af_handle st a dir)"
  using assms(6)
proof(cases rule: af_handle_cases[of a st dir])
  case selfloop
  thus ?thesis
    using af_selfloop_handle_feasible assms(6) assms(1,4)
    by (auto simp: AF_invar_feas_def AF_invar_1_def)
next
  case (cancel up dn fl m')
  have "hd (af_vstack st) \<in> {fst a, snd a}"
    using assms(7)
    by (cases dir) auto
  hence "distinct (a # af_estack st)"
    using a_notin_estack_incident[OF assms(2,3) _ assms(8) cancel(4)] estack_distinct assms(2,3)
    by (simp)
  thus ?thesis
    using af_cancel_seg_feasible_gen[OF _ _ _ assms(6) _ cancel(2,6)] assms(1,4,5) cancel(7)
    by (auto simp: AF_invar_feas_def AF_invar_1_def AF_invar_estE_def)
qed (insert assms(4), (auto simp: AF_invar_feas_def))

definition "AF_invar_free st \<longleftrightarrow> (\<forall>b\<in>set (af_estack st). af_arc_free (af_flow st) b)"

lemma af_handle_invar_free:
  assumes "AF_invar_1 st" "AF_invar_2 st" "AF_invar_3 st" "AF_invar_feas st" "AF_invar_free st"
    "AF_invar_estE st" "a \<in> \<E>" "(if dir then fst a else snd a) = hd (af_vstack st)" "af_vstack st \<noteq> []"
  shows "AF_invar_free (af_handle st a dir)"
proof-
  have f: "flow_invar (af_flow st)" "\<forall>b\<in>set (af_estack st). af_arc_free (af_flow st) b"
    "set (af_estack st) \<subseteq> \<E>"
    using assms(1,5,6)
    by (auto simp: AF_invar_1_def AF_invar_free_def AF_invar_estE_def)
  show ?thesis
    using assms(7)
  proof(cases rule: af_handle_cases[of a st dir])
    case selfloop
    have "\<forall>b\<in>set (af_estack st). flow_lookup (af_flow (af_selfloop_handle st a)) b = flow_lookup (af_flow
      st) b"
      using a_notin_estack_selfloop assms(2,3) selfloop(1)
      by (auto intro: af_selfloop_handle_flow_off[OF assms(7) f(1)])
    thus ?thesis
      using selfloop(2) f(2)
      by (simp add: AF_invar_free_def af_arc_free_def)
  next
    case (push up dn)
    have "af_arc_free (af_flow st) a"
      using af_guard_free push(2) push(3) assms(4,7)
      by (auto simp: AF_invar_feas_def af_cap_feasible_def)
    thus ?thesis
      using push(6) f(2)
      by (simp add: AF_invar_free_def)
  next
    case (cancel up dn fl m')
    have "hd (af_vstack st) \<in> {fst a, snd a}"
      using assms(8)
      by (cases dir) auto
    hence "a \<notin> set (af_estack st)"
      using a_notin_estack_incident[OF assms(2,3) _ assms(9) cancel(4)]
      by (simp)
    then have "af_arc_free fl (af_estack st ! i)" if "i < length (af_estack st)" "m' \<le> i" for i
      using af_cancel_seg_survivor_free[OF f(1) estack_distinct[OF assms(2,3)] f(2) _ f(3) assms(7)
                                             cancel(6) that]
      by (blast)
    thus ?thesis
      using cancel(7)
      by (auto simp: AF_invar_free_def in_set_conv_nth)
  qed (insert assms(5), (auto simp: AF_invar_free_def))
qed

text \<open>Dual of the survivor lemma (towards the free-set \emph{strictly} shrinking): when the drop count is
      positive, the deepest dropped arc (index @{term \<open>m' - 1\<close>}) is the one that saturated, hence is no
      longer free. Together with @{thm [source] af_push_survivor} this pinpoints the boundary at @{term
        \<open>m'\<close>}.\<close>

lemma af_push_bottleneck_sat:
  assumes "flow_invar fl" "distinct es"
    and "af_push \<gamma> x vs es ds flip fl = (fl', m')" "0 < m'" "set es \<subseteq> \<E>"
  shows "af_saturated (flow_lookup fl' (es ! (m' - 1))) (es ! (m' - 1))"
  using assms
proof(induction \<gamma> x vs es ds flip fl arbitrary: fl' m' rule: af_push.induct)
  case (1 \<gamma> x uu v1 vs a es d ds flip fl)
  obtain fl1 fv where pa: "af_push_arc \<gamma> a (d \<noteq> flip) fl = (fl1, fv)"
  by fastforce
  obtain fl2 r where rec: "af_push \<gamma> x (v1 # vs) es ds flip fl1 = (fl2, r)"
  by fastforce
  have fi1: "flow_invar fl1" "flow_lookup fl1 a = fv"
    using af_push_arc_flow_invar[OF _ pa 1(2)] af_push_arc_at[OF _ 1(2) pa] 1(6)
    by auto
  moreover have "flow_lookup fl2 a = flow_lookup fl1 a"
    using af_push_flow_off[OF _ fi1(1) _ rec] 1(3,6)
    by auto
  ultimately show ?case
    using 1(1)[OF pa[symmetric] refl _ fi1(1) _ rec] 1(3-6) pa rec
    by (auto simp: nth_Cons' split: if_splits)
qed simp_all

lemma af_push_saturated_at:
  "\<lbrakk>set es \<subseteq> \<E>; flow_invar fl; distinct es; af_push \<gamma> x vs es ds flip fl = (fl', m'); 0 <
    m'\<rbrakk>
   \<Longrightarrow> \<not> af_arc_free fl' (es ! (m' - 1))"
  using af_push_bottleneck_sat[of fl es \<gamma> x vs ds flip fl' m']
  by (auto simp: af_saturated_def af_arc_free_def Let_def)

subsection \<open>Towards termination --- the free-set key of the DFS measure\<close>

text \<open>@{const af_handle} either leaves the flow untouched (the push / skip / flag branches --- so the free
      set is unchanged and the iterator-progress key of the measure will strictly drop) or performs a real
      cancellation, which strictly shrinks the free set. This
      dichotomy is exactly the first (well-founded) key of the inner-DFS termination measure.\<close>

definition "af_freeset st = {b\<in>\<E>. af_arc_free (af_flow st) b}"

subsection \<open>Inner DFS termination\<close>

text \<open>The measure is lexicographic: (i) the number of free arcs (@{const af_freeset}), which strictly drops
      on every cancellation (D2) and is unchanged otherwise; (ii) the total number of un-scanned iterator
      edges \<open>af_iterrem\<close>, which strictly drops on every advance (push / skip) and is unchanged by a
      non-cancelling @{const af_handle}; (iii) the stack length, which drops on a pop. Each is a natural
      number (the remaining sets are finite under the iterator invariant), giving a well-founded order.\<close>

lemma remaining_out_finite: "\<lbrakk>multigraph_inv oa ia; v \<in> \<V>\<rbrakk> \<Longrightarrow> finite
    (out_remaining oa v)"
  using outg.idx_partition_union[of oa v] delta_plus_finite[of v]
  by (auto simp: multigraph_inv_def out_graph_inv_def intro: finite_subset)

lemma remaining_in_finite: "\<lbrakk>multigraph_inv oa ia; v \<in> \<V>\<rbrakk> \<Longrightarrow> finite
    (in_remaining ia v)"
  using ing.idx_partition_union[of ia v] delta_minus_finite[of v]
  by (auto simp: multigraph_inv_def in_graph_inv_def intro: finite_subset)

lemma out_move_card:
  "\<lbrakk>out_invar C; out_remaining C v \<noteq> {}; finite (out_remaining C v); v \<in> \<V>\<rbrakk>
   \<Longrightarrow> card (out_remaining (out_move C v) v) = card (out_remaining C v) - 1"
  by (simp add: outg.idx_move_remaining outg.idx_current card_Diff_singleton)

lemma in_move_card:
  "\<lbrakk>in_invar C; in_remaining C v \<noteq> {}; finite (in_remaining C v); v \<in> \<V>\<rbrakk>
   \<Longrightarrow> card (in_remaining (in_move C v) v) = card (in_remaining C v) - 1"
  by (simp add: ing.idx_move_remaining ing.idx_current card_Diff_singleton)

definition "af_iterrem st =
  (\<Sum>v\<in>\<V>. card (out_remaining (af_out_arr st) v)
           + card (in_remaining (af_in_arr st) v))"

lemma sum_drop_one:
  assumes "finite A" "v \<in> A" "g' v + 1 = g v" "\<And>w. \<lbrakk>w \<in> A; w \<noteq> v\<rbrakk>
    \<Longrightarrow> g' w = (g w :: nat)"
  shows "sum g' A + 1 = sum g A"
proof-
  have "sum g' (A - {v}) = sum g (A - {v})"
    using assms(4)
    by (intro sum.cong) auto
  thus ?thesis
    using assms(3)
    by (simp add: sum.remove[OF assms(1,2)])
qed

lemma af_iterrem_out_advance:
  assumes "multigraph_inv (af_out_arr st) (af_in_arr st)" "v \<in> \<V>" "out_has (af_out_arr st) v"
  shows "af_iterrem (st\<lparr>af_out_arr := out_move (af_out_arr st) v\<rparr>) + 1 = af_iterrem st"
  using assms remaining_out_finite[of "af_out_arr st" "af_in_arr st" v]
    outg.idx_has[of "af_out_arr st" v] out_move_card[of "af_out_arr st" v]
    outg.idx_move_remaining_other[of "af_out_arr st" v]
  unfolding af_iterrem_def
  by (intro sum_drop_one[OF \<V>_finite assms(2)])
     (auto simp: af_iterrem_def multigraph_inv_def out_graph_inv_def card_gt_0_iff)

lemma af_iterrem_in_advance:
  assumes "multigraph_inv (af_out_arr st) (af_in_arr st)" "v \<in> \<V>" "in_has (af_in_arr st) v"
  shows "af_iterrem (st\<lparr>af_in_arr := in_move (af_in_arr st) v\<rparr>) + 1 = af_iterrem st"
  using assms remaining_in_finite[of "af_out_arr st" "af_in_arr st" v]
    ing.idx_has[of "af_in_arr st" v] in_move_card[of "af_in_arr st" v]
    ing.idx_move_remaining_other[of "af_in_arr st" v]
  unfolding af_iterrem_def
  by (intro sum_drop_one[OF \<V>_finite assms(2)])
     (auto simp: af_iterrem_def multigraph_inv_def in_graph_inv_def card_gt_0_iff)

lemma AF_invar_feas_out_arr[simp]: "AF_invar_feas (st\<lparr>af_out_arr := X\<rparr>) = AF_invar_feas st"
  by (simp add: AF_invar_feas_def)

lemma AF_invar_feas_in_arr[simp]: "AF_invar_feas (st\<lparr>af_in_arr := X\<rparr>) = AF_invar_feas st"
  by (simp add: AF_invar_feas_def)

lemma AF_invar_free_out_arr[simp]: "AF_invar_free (st\<lparr>af_out_arr := X\<rparr>) = AF_invar_free st"
  by (simp add: AF_invar_free_def)

lemma AF_invar_free_in_arr[simp]: "AF_invar_free (st\<lparr>af_in_arr := X\<rparr>) = AF_invar_free st"
  by (simp add: AF_invar_free_def)

lemma AF_invar_estE_out_arr[simp]: "AF_invar_estE (st\<lparr>af_out_arr := X\<rparr>) = AF_invar_estE st"
  by (simp add: AF_invar_estE_def)

lemma AF_invar_estE_in_arr[simp]: "AF_invar_estE (st\<lparr>af_in_arr := X\<rparr>) = AF_invar_estE st"
  by (simp add: AF_invar_estE_def)

text \<open>The two advancing DFS steps hand the scanned arc to @{const af_handle}; by E1 it is an edge
      incident to the top vertex.\<close>

lemma AF_DFS_upd1_scan:
  assumes "AF_DFS_call_1_conds st" "AF_invar_iter st" "AF_invar_V st"
  obtains a where
    "AF_DFS_upd1 st = af_handle (st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack st))\<rparr>) a True"
    "a \<in> \<E>" "fst a = hd (af_vstack st)" "af_vstack st \<noteq> []" "hd (af_vstack st) \<in> \<V>"
proof-
  have "af_vstack st \<noteq> []" "out_has (af_out_arr st) (hd (af_vstack st))" "hd (af_vstack st) \<in> \<V>"
    using assms(1,3)
    by (auto elim!: call_cond_elims simp: AF_invar_V_def)
  thus thesis
    using that af_current_out_endpoint[of "af_out_arr st" "af_in_arr st" "hd (af_vstack st)"] assms(2)
    by (auto simp: AF_DFS_upd1_def Let_def AF_invar_iter_def)
qed

lemma AF_DFS_upd2_scan:
  assumes "AF_DFS_call_2_conds st" "AF_invar_iter st" "AF_invar_V st"
  obtains a where
    "AF_DFS_upd2 st = af_handle (st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack st))\<rparr>) a False"
    "a \<in> \<E>" "snd a = hd (af_vstack st)" "af_vstack st \<noteq> []" "hd (af_vstack st) \<in> \<V>"
proof-
  have "af_vstack st \<noteq> []" "in_has (af_in_arr st) (hd (af_vstack st))" "hd (af_vstack st) \<in> \<V>"
    using assms(1,3)
    by (auto elim!: call_cond_elims simp: AF_invar_V_def)
  thus thesis
    using that af_current_in_endpoint[of "af_out_arr st" "af_in_arr st" "hd (af_vstack st)"] assms(2)
    by (auto simp: AF_DFS_upd2_def Let_def AF_invar_iter_def)
qed

lemma AF_invar_estE_holds_1[invar_holds_intros]:
  "\<lbrakk>AF_DFS_call_1_conds st; AF_invar_estE st; AF_invar_iter st; AF_invar_V st\<rbrakk>
   \<Longrightarrow> AF_invar_estE (AF_DFS_upd1 st)"
  by (erule AF_DFS_upd1_scan) (auto intro: af_handle_invar_estE)

lemma AF_invar_estE_holds_2[invar_holds_intros]:
  "\<lbrakk>AF_DFS_call_2_conds st; AF_invar_estE st; AF_invar_iter st; AF_invar_V st\<rbrakk>
   \<Longrightarrow> AF_invar_estE (AF_DFS_upd2 st)"
  by (erule AF_DFS_upd2_scan) (auto intro: af_handle_invar_estE)

lemma AF_invar_estE_holds_3[invar_holds_intros]:
  "\<lbrakk>AF_DFS_call_3_conds st; AF_invar_estE st\<rbrakk> \<Longrightarrow> AF_invar_estE (AF_DFS_upd3 st)"
  by (cases "af_estack st") (auto simp: AF_DFS_upd3_def AF_invar_estE_def)

lemma AF_invar_feas_holds_1[invar_holds_intros]:
  "\<lbrakk>AF_DFS_call_1_conds st; AF_invar_1 st; AF_invar_2 st; AF_invar_3 st; AF_invar_feas st;
    AF_invar_estE st; AF_invar_iter st; AF_invar_V st\<rbrakk> \<Longrightarrow> AF_invar_feas (AF_DFS_upd1 st)"
  by (erule AF_DFS_upd1_scan) (auto intro!: af_handle_invar_feas AF_invar_1_out_advance)

lemma AF_invar_feas_holds_2[invar_holds_intros]:
  "\<lbrakk>AF_DFS_call_2_conds st; AF_invar_1 st; AF_invar_2 st; AF_invar_3 st; AF_invar_feas st;
    AF_invar_estE st; AF_invar_iter st; AF_invar_V st\<rbrakk> \<Longrightarrow> AF_invar_feas (AF_DFS_upd2 st)"
  by (erule AF_DFS_upd2_scan) (auto intro!: af_handle_invar_feas AF_invar_1_in_advance)

lemma AF_invar_feas_holds_3[invar_holds_intros]:
  "\<lbrakk>AF_DFS_call_3_conds st; AF_invar_feas st\<rbrakk> \<Longrightarrow> AF_invar_feas (AF_DFS_upd3 st)"
  by (simp add: AF_DFS_upd3_def AF_invar_feas_def)

lemma AF_invar_free_holds_1[invar_holds_intros]:
  "\<lbrakk>AF_DFS_call_1_conds st; AF_invar_1 st; AF_invar_2 st; AF_invar_3 st; AF_invar_feas st;
    AF_invar_free st; AF_invar_iter st; AF_invar_V st; AF_invar_estE st\<rbrakk>
   \<Longrightarrow> AF_invar_free (AF_DFS_upd1 st)"
  by (erule AF_DFS_upd1_scan) (auto intro!: af_handle_invar_free AF_invar_1_out_advance)

lemma AF_invar_free_holds_2[invar_holds_intros]:
  "\<lbrakk>AF_DFS_call_2_conds st; AF_invar_1 st; AF_invar_2 st; AF_invar_3 st; AF_invar_feas st;
    AF_invar_free st; AF_invar_iter st; AF_invar_V st; AF_invar_estE st\<rbrakk>
   \<Longrightarrow> AF_invar_free (AF_DFS_upd2 st)"
  by (erule AF_DFS_upd2_scan) (auto intro!: af_handle_invar_free AF_invar_1_in_advance)

lemma AF_invar_free_holds_3[invar_holds_intros]:
  "\<lbrakk>AF_DFS_call_3_conds st; AF_invar_2 st; AF_invar_3 st; AF_invar_free st\<rbrakk>
   \<Longrightarrow> AF_invar_free (AF_DFS_upd3 st)"
  by (cases "af_estack st") (auto simp: AF_DFS_upd3_def AF_invar_free_def)

text \<open>Combined single-step preservation of Themes A and B: @{const AF_invar_1}'s per-step preservation
      needs the range facts that Theme E1 supplies for the scanned arc.\<close>

lemma AF_invar_12_holds_1[invar_holds_intros]:
  "\<lbrakk>AF_DFS_call_1_conds st; AF_invar_1 st; AF_invar_2 st; AF_invar_iter st; AF_invar_V st;
    AF_invar_estE st\<rbrakk> \<Longrightarrow> AF_invar_1 (AF_DFS_upd1 st) \<and> AF_invar_2 (AF_DFS_upd1 st)"
  by (erule AF_DFS_upd1_scan; (auto intro!: af_handle_invar_1 af_handle_invar_2 AF_invar_1_out_advance
           simp: AF_invar_V_def AF_invar_estE_def))

lemma AF_invar_12_holds_2[invar_holds_intros]:
  "\<lbrakk>AF_DFS_call_2_conds st; AF_invar_1 st; AF_invar_2 st; AF_invar_iter st; AF_invar_V st;
    AF_invar_estE st\<rbrakk> \<Longrightarrow> AF_invar_1 (AF_DFS_upd2 st) \<and> AF_invar_2 (AF_DFS_upd2 st)"
  by (erule AF_DFS_upd2_scan; (auto intro!: af_handle_invar_1 af_handle_invar_2 AF_invar_1_in_advance
           simp: AF_invar_V_def AF_invar_estE_def))

lemma AF_invar_12_holds_3[invar_holds_intros]:
  assumes "AF_DFS_call_3_conds st" "AF_invar_1 st" "AF_invar_2 st" "AF_invar_V st"
  shows "AF_invar_1 (AF_DFS_upd3 st) \<and> AF_invar_2 (AF_DFS_upd3 st)"
proof-
  obtain v vs where "af_vstack st = v # vs"
    using assms(1)
    by (auto elim!: call_cond_elims)
  thus ?thesis
    using assms(2-4) state_arr.fixed_univ_map_upd[of "af_state st" v]
    by (cases "af_estack st"; cases "af_dstack st")
       (auto simp: AF_DFS_upd3_def AF_invar_1_def AF_invar_2_def AF_invar_V_def st_upd_invar)
qed

definition "AF_inv st \<longleftrightarrow> AF_invar_1 st \<and> AF_invar_2 st \<and> AF_invar_3 st \<and>
    AF_invar_iter st \<and>
  AF_invar_V st \<and> AF_invar_estE st \<and> AF_invar_feas st \<and> AF_invar_free st"

lemma AF_inv_holds_1:
  "\<lbrakk>multigraph_inv out_arr in_arr; AF_DFS_call_1_conds st; AF_inv st\<rbrakk> \<Longrightarrow> AF_inv
    (AF_DFS_upd1 st)"
  by (simp add: AF_inv_def invar_holds_intros)

lemma AF_inv_holds_2:
  "\<lbrakk>multigraph_inv out_arr in_arr; AF_DFS_call_2_conds st; AF_inv st\<rbrakk> \<Longrightarrow> AF_inv
    (AF_DFS_upd2 st)"
  by (simp add: AF_inv_def invar_holds_intros)

lemma AF_inv_holds_3: "\<lbrakk>AF_DFS_call_3_conds st; AF_inv st\<rbrakk> \<Longrightarrow> AF_inv (AF_DFS_upd3 st)"
  by (simp add: AF_inv_def invar_holds_intros)

lemma af_freeset_upd[simp]:
  "af_freeset (st\<lparr>af_out_arr := X\<rparr>) = af_freeset st" "af_freeset (st\<lparr>af_in_arr := X\<rparr>) =
    af_freeset st"
  "af_freeset (st\<lparr>af_vstack := Y\<rparr>) = af_freeset st" "af_freeset (st\<lparr>af_state := Z\<rparr>) =
    af_freeset st"
  "af_freeset (st\<lparr>af_estack := E\<rparr>) = af_freeset st" "af_freeset (st\<lparr>af_dstack := D\<rparr>) =
    af_freeset st"
  "af_freeset (st\<lparr>af_unbounded := U\<rparr>) = af_freeset st"
  by (simp_all add: af_freeset_def)

subsection \<open>Capacity-agnostic cancellation saturation (dropping the finite-capacity assumption)\<close>

text \<open>The following are @{term \<open>\<forall>a. cap a \<noteq> - 1\<close>}-free strengthenings of the
    cancellation saturation
      lemmas. The observation: a \emph{bounded} cancellation (@{term \<open>\<not> ubd\<close>}, chosen room @{term
        \<open>\<gamma> \<noteq> - 1\<close>})
      still saturates an arc regardless of the other arcs' capacities --- a backward push drives the flow to
      @{term 0} with no capacity bound, and a forward push with a finite room forces the capacity to be
      finite. These feed a capacity-agnostic termination argument (the free set strictly drops, or the
      iterator advances even on the unbounded-flag step).\<close>

lemma af_push_arc_room_notfree_gen:
  "\<lbrakk>flow_invar fl; a \<in> \<E>; af_rooms fl a = (up, dn); (if dir then up else dn) \<noteq> - 1;
    af_push_arc (if dir then up else dn) a dir fl = (fl', f')\<rbrakk> \<Longrightarrow> \<not> af_arc_free fl' a"
  using af_push_arc_at[of a fl "if dir then up else dn" dir fl' f']
  by (cases dir) (auto simp: af_rooms_def af_arc_free_def Let_def split: if_splits)

lemma af_scan_push_seed_gen:
  "\<lbrakk>flow_invar fl; distinct es; \<gamma> \<noteq> - 1; set es \<subseteq> \<E>; af_scan fl x vs es ds (k0,
    ra0, rf0) = (k, ra, rf);
    af_push \<gamma> x vs es ds flip fl = (fl', 0); \<gamma> = (if flip then rf else ra)\<rbrakk>
   \<Longrightarrow> (if flip then rf else ra) = (if flip then rf0 else ra0)"
proof(induction \<gamma> x vs es ds flip fl arbitrary: fl' k0 ra0 rf0 k ra rf rule: af_push.induct)
  case (1 \<gamma> x u v1 vs a es d ds flip fl)
  obtain up dn where ud: "af_rooms fl a = (up, dn)"
    by fastforce
  obtain fl1 fv where pa: "af_push_arc \<gamma> a (d \<noteq> flip) fl = (fl1, fv)"
    by fastforce
  have a: "a \<in> \<E>" "a \<notin> set es" "distinct es" "set es \<subseteq> \<E>"
    using 1(3,5)
    by auto
  have sat: "\<gamma> = (if flip then (if d then dn else up) else (if d then up else dn)) \<Longrightarrow>
    af_saturated fv a"
    using af_push_arc_at[OF a(1) 1(2) pa] ud 1(4)
    by (cases flip; cases d) (auto simp: af_rooms_def af_saturated_def Let_def split: if_splits)
  show ?case
  proof(cases "v1 = x")
    case True
    hence "ra = af_min (if d then up else dn) ra0" "rf = af_min (if d then dn else up) rf0"
          "\<not> af_saturated fv a"
      using 1(6,7) ud pa
      by (auto simp: Let_def split: if_splits)
    thus ?thesis
      using sat 1(8)
      by (cases flip; cases d) (auto simp: af_min_def min_def split: if_splits)
  next
    case False
    obtain fl2 r where p2: "af_push \<gamma> x (v1 # vs) es ds flip fl1 = (fl2, r)"
      by fastforce
    have r: "r = 0" "\<not> af_saturated fv a"
      using 1(7) ud pa p2 False
      by (auto simp: Let_def split: if_splits)
    have "\<forall>b\<in>set es. flow_lookup fl1 b = flow_lookup fl b"
      using a(2)
      by (auto intro: af_push_arc_flow_off[OF a(1) 1(2) _ pa])
    hence "af_scan fl1 x (v1 # vs) es ds
                  (k0 + af_delta_cost a d, af_min (if d then up else dn) ra0, af_min (if d then dn else up) rf0)
                = (k, ra, rf)"
      using af_scan_cong[of es fl1 fl] 1(6) ud False
      by (simp add: Let_def)
    then have "(if flip then rf else ra)
          = (if flip then af_min (if d then dn else up) rf0 else af_min (if d then up else dn) ra0)"
      using 1(1)[OF pa[symmetric] refl False af_push_arc_flow_invar[OF a(1) pa 1(2)] a(3) 1(4) a(4) _
                    p2[unfolded r(1)] 1(8)]
      by (blast)
    thus ?thesis
      using sat r(2) 1(8)
      by (cases flip; cases d) (auto simp: af_min_def min_def split: if_splits)
  qed
qed auto

lemma af_cancel_seg_closing_sat_gen:
  assumes "flow_invar fl" "distinct es" "set es \<subseteq> \<E>" "a \<in> \<E>" "a \<notin> set es" "af_rooms fl a =
    (up, dn)"
    "af_cancel_seg up dn x vs es ds a dir fl = (fl', 0, False)"
  shows "\<not> af_arc_free fl' a"
proof-
  have closesat: "\<not> af_arc_free fl2 a"
    if "af_scan fl x vs es ds (af_delta_cost a dir, if dir then up else dn, if dir then dn else up)
          = (k, ra, rf)"
       "g = (if flip then rf else ra)" "g \<noteq> - 1" "af_push g x vs es ds flip fl = (fl1, 0)"
       "af_push_arc g a (dir \<noteq> flip) fl1 = (fl2, f2)"
    for k ra rf g flip fl1 fl2 f2
  proof-
    have "g = (if dir \<noteq> flip then up else dn)"
      using af_scan_push_seed_gen[OF assms(1,2) that(3) assms(3) that(1,4,2)] that(2)
      by (cases flip; cases dir) auto
    moreover have "af_rooms fl1 a = (up, dn)"
      using af_push_flow_off[OF assms(3,1,5) that(4)] assms(6)
      by (auto simp: af_rooms_def Let_def split: if_splits)
    ultimately show ?thesis
      using af_push_arc_room_notfree_gen[OF af_push_flow_invar[OF assms(3) that(4) assms(1)] assms(4),
                                         of up dn "dir \<noteq> flip" fl2 f2] that(3,5)
      by simp
  qed
  show ?thesis
    using assms(7)
  proof(cases rule: af_cancel_seg_cases)
    case (fin k ra rf fl1 f2)
    thus ?thesis
      using closesat[OF fin(1) refl fin(2-4)]
      by simp
  next
    case (sw k ra rf fl1 f2)
    hence "af_push_arc rf a (dir \<noteq> True) fl1 = (fl', f2)"
      by simp
    thus ?thesis
      using closesat[OF sw(1) if_True[symmetric] sw(4,5)]
      by simp
  qed simp
qed

lemma af_cancel_seg_bottleneck_sat:
  assumes "flow_invar fl" "distinct es" "a \<notin> set es" "set es \<subseteq> \<E>" "a \<in> \<E>"
    "af_cancel_seg up dn x vs es ds a dir fl = (fl'', m', ubd)" "0 < m'"
  shows "af_saturated (flow_lookup fl'' (es ! (m' - 1))) (es ! (m' - 1))"
proof-
  obtain \<gamma> flip fl' f where p: "af_push \<gamma> x vs es ds flip fl = (fl', m')"
    and pa: "af_push_arc \<gamma> a (dir \<noteq> flip) fl' = (fl'', f)"
    using assms(6,7)
    by (auto simp: af_cancel_seg_def Let_def split: prod.splits if_splits)
  have "es ! (m' - 1) \<noteq> a"
    using assms(3,7) af_cancel_seg_drop_bound[of up dn x vs es ds a dir fl fl'' m' ubd] assms(6) nth_mem[of "m' - 1" es]
    by (auto)
  then show ?thesis
    using af_push_bottleneck_sat[of fl es \<gamma> x vs ds flip fl' m'] assms(1,2) p assms(7,4)
          af_push_arc_flow_off[OF assms(5) af_push_flow_invar[OF assms(4) p assms(1)] _ pa]
    by (simp)
qed

lemma af_cancel_seg_free_witnessE_gen:
  assumes "af_cap_feasible fl" "flow_invar fl" "distinct es" "a \<in> \<E>" "set es \<subseteq> \<E>"
    "af_rooms fl a = (up, dn)" "af_arc_free fl a" "\<forall>b\<in>set es. af_arc_free fl b" "a \<notin> set es"
    "af_cancel_seg up dn x vs es ds a dir fl = (fl'', m', ubd)" "\<not> ubd"
  shows "\<exists>b\<in>\<E>. af_arc_free fl b \<and> \<not> af_arc_free fl'' b"
proof(cases "m'=0")
  case True
  have "\<not> af_arc_free fl'' a"
    using assms True af_cancel_seg_closing_sat_gen[of fl es a up dn x vs ds dir fl'']
    by auto
  then show ?thesis
    using assms(4,7)
    by blast
next
  case False
  have "es ! (m'-1) \<in> set es"
    using assms(10) False af_cancel_seg_drop_bound[of up dn x vs es ds a dir fl fl'' m' ubd]
    by auto
  moreover have "\<not> af_arc_free fl'' (es ! (m'-1))"
    using assms False af_cancel_seg_bottleneck_sat[of fl es a up dn x vs ds dir fl'' m' ubd]
    by (auto simp: af_saturated_def af_arc_free_def Let_def)
  ultimately show ?thesis
  using assms(5,8)
  by blast
qed

lemma af_cancel_seg_free_card_gen:
  assumes "af_cap_feasible fl" "flow_invar fl" "distinct es" "a \<in> \<E>" "set es \<subseteq> \<E>"
    "af_rooms fl a = (up, dn)" "af_arc_free fl a" "\<forall>b\<in>set es. af_arc_free fl b" "a \<notin> set es"
    "af_cancel_seg up dn x vs es ds a dir fl = (fl'', m', ubd)" "\<not> ubd"
  shows "card {b\<in>\<E>. af_arc_free fl'' b} < card {b\<in>\<E>. af_arc_free fl b}"
proof-
  have "af_arc_free fl b" if "b \<in> \<E>" "af_arc_free fl'' b" for b
    using that assms(7,8) af_cancel_seg_arc_free_off[OF assms(5,4,2) _ _ assms(10), of b]
    by (cases "b \<in> set es \<or> b = a") auto
  moreover obtain w where "w \<in> \<E>" "af_arc_free fl w" "\<not> af_arc_free fl'' w"
    using af_cancel_seg_free_witnessE_gen assms
    by (blast)
  ultimately have "{b\<in>\<E>. af_arc_free fl'' b} \<subset> {b\<in>\<E>. af_arc_free fl b}"
    by (blast)
  thus ?thesis
    using finite_E
    by (intro psubset_card_mono) auto
qed

text \<open>@{const af_handle} either keeps the free set and the iterator arrays, or strictly shrinks the
      free set.\<close>

lemma af_handle_noncancel_or_free_gen:
  assumes "AF_invar_1 st" "AF_invar_2 st" "AF_invar_3 st" "AF_invar_feas st" "AF_invar_free st"
    "AF_invar_estE st" "a \<in> \<E>" "(if dir then fst a else snd a) = hd (af_vstack st)" "af_vstack st \<noteq> []"
  shows "(card (af_freeset (af_handle st a dir)) = card (af_freeset st) \<and>
          af_iterrem (af_handle st a dir) = af_iterrem st) \<or>
         card (af_freeset (af_handle st a dir)) < card (af_freeset st)"
proof-
  have f: "flow_invar (af_flow st)" "af_cap_feasible (af_flow st)"
    "\<forall>b\<in>set (af_estack st). af_arc_free (af_flow st) b" "set (af_estack st) \<subseteq> \<E>"
    using assms(1,4-6)
    by (auto simp: AF_invar_1_def AF_invar_feas_def AF_invar_free_def AF_invar_estE_def)
  show ?thesis
    using assms(7)
  proof(cases rule: af_handle_cases[of a st dir])
    case selfloop
    show ?thesis
    proof(cases "af_arc_free (af_flow (af_selfloop_handle st a)) a")
      case True
      thus ?thesis
        using selfloop(2) af_selfloop_handle_free_imp_flow_id[of a st] assms(7) f(1) True
        by (simp add: af_freeset_def af_iterrem_def)
    next
      case False
      have "\<forall>b. b \<noteq> a \<longrightarrow> af_arc_free (af_flow (af_selfloop_handle st a)) b = af_arc_free
        (af_flow st) b"
        using af_selfloop_handle_flow_off[of a st] assms(7) f(1)
        by (simp add: af_arc_free_def)
      then have "af_freeset (af_selfloop_handle st a) = af_freeset st - {a}"
        using False
        by (auto simp: af_freeset_def)
      moreover have "af_iterrem (af_selfloop_handle st a) = af_iterrem st"
        by (simp add: af_iterrem_def)
      moreover have "finite (af_freeset st)"
        using finite_E
        by (auto simp: af_freeset_def)
      ultimately show ?thesis
        using selfloop(2) psubset_card_mono[of "af_freeset st" "af_freeset st - {a}"]
        by (cases "a \<in> af_freeset st") auto
    qed
  next
    case (cancel up dn fl m')
    have "hd (af_vstack st) \<in> {fst a, snd a}"
      using assms(8)
      by (cases dir) auto
    hence "a \<notin> set (af_estack st)"
      using a_notin_estack_incident[OF assms(2,3) _ assms(9) cancel(4)]
      by (simp)
    moreover have "af_arc_free (af_flow st) a"
      using af_guard_free[where fl="af_flow st" and a=a and up=up and dn=dn] cancel(2) cancel(3) f(2) assms(7)
      by (auto simp: af_cap_feasible_def)
    ultimately have "card {b\<in>\<E>. af_arc_free fl b} < card {b\<in>\<E>. af_arc_free (af_flow st) b}"
      using af_cancel_seg_free_card_gen[OF f(2,1) estack_distinct[OF assms(2,3)] assms(7) f(4) cancel(2)
                                           _ f(3) _ cancel(6)]
      by (simp)
    thus ?thesis
      using cancel(7)
      by (simp add: af_freeset_def)
  qed (simp_all add: af_iterrem_def)
qed

lemma af_meas_upd1_in[termination_intros]:
  assumes "multigraph_inv out_arr in_arr" "AF_DFS_call_1_conds st" "AF_inv st"
  shows "(AF_DFS_upd1 st, st) \<in> measures [\<lambda>s. card (af_freeset s), \<lambda>s. af_iterrem s, \<lambda>s.
    length (af_vstack s)]"
proof-
  have i: "AF_invar_1 st" "AF_invar_2 st" "AF_invar_3 st" "AF_invar_iter st" "AF_invar_V st"
    "AF_invar_estE st" "AF_invar_feas st" "AF_invar_free st"
    using assms(3)
    by (auto simp: AF_inv_def)
  obtain a where a: "AF_DFS_upd1 st
      = af_handle (st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack st))\<rparr>) a True"
    "a \<in> \<E>" "fst a = hd (af_vstack st)" "af_vstack st \<noteq> []" "hd (af_vstack st) \<in> \<V>"
    by (rule AF_DFS_upd1_scan[OF assms(2) i(4,5)])
  let ?st' = "st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack st))\<rparr>"
  have "out_has (af_out_arr st) (hd (af_vstack st))"
    using assms(2)
    by (auto elim!: call_cond_elims)
  hence "af_iterrem ?st' + 1 = af_iterrem st"
    using af_iterrem_out_advance[OF _ a(5)] i(4)
    by (simp add: AF_invar_iter_def)
  moreover have "(card (af_freeset (af_handle ?st' a True)) = card (af_freeset ?st') \<and>
                  af_iterrem (af_handle ?st' a True) = af_iterrem ?st') \<or>
                 card (af_freeset (af_handle ?st' a True)) < card (af_freeset ?st')"
    by (rule af_handle_noncancel_or_free_gen) (insert i a(2-5), auto intro: AF_invar_1_out_advance)
  ultimately show ?thesis
    using a(1)
    by (auto simp: in_measures)
qed

lemma af_meas_upd2_in[termination_intros]:
  assumes "multigraph_inv out_arr in_arr" "AF_DFS_call_2_conds st" "AF_inv st"
  shows "(AF_DFS_upd2 st, st) \<in> measures [\<lambda>s. card (af_freeset s), \<lambda>s. af_iterrem s, \<lambda>s.
    length (af_vstack s)]"
proof-
  have i: "AF_invar_1 st" "AF_invar_2 st" "AF_invar_3 st" "AF_invar_iter st" "AF_invar_V st"
    "AF_invar_estE st" "AF_invar_feas st" "AF_invar_free st"
    using assms(3)
    by (auto simp: AF_inv_def)
  obtain a where a: "AF_DFS_upd2 st
      = af_handle (st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack st))\<rparr>) a False"
    "a \<in> \<E>" "snd a = hd (af_vstack st)" "af_vstack st \<noteq> []" "hd (af_vstack st) \<in> \<V>"
    by (rule AF_DFS_upd2_scan[OF assms(2) i(4,5)])
  let ?st' = "st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack st))\<rparr>"
  have "in_has (af_in_arr st) (hd (af_vstack st))"
    using assms(2)
    by (auto elim!: call_cond_elims)
  hence "af_iterrem ?st' + 1 = af_iterrem st"
    using af_iterrem_in_advance[OF _ a(5)] i(4)
    by (simp add: AF_invar_iter_def)
  moreover have "(card (af_freeset (af_handle ?st' a False)) = card (af_freeset ?st') \<and>
                  af_iterrem (af_handle ?st' a False) = af_iterrem ?st') \<or>
                 card (af_freeset (af_handle ?st' a False)) < card (af_freeset ?st')"
    by (rule af_handle_noncancel_or_free_gen) (insert i a(2-5), auto intro: AF_invar_1_in_advance)
  ultimately show ?thesis
    using a(1)
    by (auto simp: in_measures)
qed

lemma af_meas_upd3_in[termination_intros]:
  "AF_DFS_call_3_conds st
   \<Longrightarrow> (AF_DFS_upd3 st, st) \<in> measures [\<lambda>s. card (af_freeset s), \<lambda>s. af_iterrem s,
     \<lambda>s. length (af_vstack s)]"
  by (auto elim!: call_cond_elims simp: in_measures AF_DFS_upd3_def af_freeset_def af_iterrem_def)

text \<open>Inner DFS termination: under the full invariant @{const AF_inv} (established at launch from the
      standing @{term \<open>multigraph_inv out_arr in_arr\<close>} and finite capacities), the DFS is total.\<close>

lemma AF_DFS_dom[termination_intros]:
  assumes "multigraph_inv out_arr in_arr" "AF_inv st"
  shows "AF_DFS_dom st"
  using assms
  by (induction st rule: wf_induct_rule[OF wf_measures[of
      "[\<lambda>s. card (af_freeset s), \<lambda>s. af_iterrem s, \<lambda>s. length (af_vstack s)]"]])
     (blast intro: AF_DFS_domintros termination_intros
       AF_inv_holds_1 AF_inv_holds_2 AF_inv_holds_3)

subsection \<open>Outer loop termination --- the whole procedure is total\<close>

text \<open>The full invariant holds at each DFS launch (established from the standing @{term \<open>multigraph_inv
    out_arr in_arr\<close>},
      finite capacities, feasible input flow, and a vertex iterator covering @{term \<V>}), so every launched DFS is
      total; the outer loop's own measure is the number of vertices yet to be visited, which drops on every
        step.\<close>

lemma AF_inv_initial:
  "\<lbrakk>flow_invar fl; st_invar stt; out_invar oa; in_invar ia; multigraph_inv oa ia; v \<in> \<V>;
    af_cap_feasible fl; \<forall>w\<in>\<V>. st_lookup stt w \<noteq> OnStack\<rbrakk> \<Longrightarrow> AF_inv
    (AF_DFS_initial fl oa ia stt v)"
  by (auto simp: AF_inv_def AF_DFS_initial_def AF_invar_1_def AF_invar_2_def AF_invar_3_def
                 AF_invar_iter_def AF_invar_V_def AF_invar_estE_def AF_invar_feas_def AF_invar_free_def
                 st_upd_invar state_arr.fixed_univ_map_upd)

lemma AF_inv_holds:
  assumes "AF_DFS_dom st" "multigraph_inv out_arr in_arr" "AF_inv st"
  shows "AF_inv (AF_DFS st)"
  using assms(3)
proof(induction rule: AF_DFS_induct[OF assms(1)])
  case IH: (1 st)
  show ?case
    by (rule AF_DFS_cases[where st = st])
       (auto intro!: IH(2-5) AF_inv_holds_1[OF assms(2)] AF_inv_holds_2[OF assms(2)] AF_inv_holds_3
             simp: AF_DFS_simps[OF IH(1)] AF_DFS_ret_def)
qed

lemma AF_DFS_ret_vstack:
  assumes "AF_DFS_dom st"
  shows "\<not> af_unbounded (AF_DFS st) \<longrightarrow> af_vstack (AF_DFS st) = []"
proof(induction rule: AF_DFS_induct[OF assms])
  case IH: (1 st)
  show ?case
    by (rule AF_DFS_cases[where st = st])
       (insert IH, auto simp: AF_DFS_simps[OF IH(1)] AF_DFS_ret_def elim!: call_cond_elims)
qed

definition "AFF_inv st \<longleftrightarrow>
  flow_invar (aff_flow st) \<and> st_invar (aff_state st) \<and>
  out_invar (aff_out_arr st) \<and> in_invar (aff_in_arr st) \<and>
  multigraph_inv (aff_out_arr st) (aff_in_arr st) \<and>
  af_cap_feasible (aff_flow st) \<and>
  (\<not> aff_unbounded st \<longrightarrow> (\<forall>w\<in>\<V>. st_lookup (aff_state st) w \<noteq> OnStack)) \<and>
  vit_invar (aff_vit st) \<and> vit_abstract (aff_vit st) \<subseteq> \<V>"

text \<open>The DFS launched by the outer loop from its current vertex.\<close>

abbreviation "af_launch st \<equiv>
  AF_DFS_initial (aff_flow st) (aff_out_arr st) (aff_in_arr st) (aff_state st) (current_vertex (aff_vit st))"

lemma AFF_inv_initial:
  "\<lbrakk>multigraph_inv out_arr in_arr; flow_invar f0; af_cap_feasible f0; vit_invar all_vertices;
    vit_abstract all_vertices \<subseteq> \<V>\<rbrakk> \<Longrightarrow> AFF_inv (AF_outer_initial f0)"
  using state_init_invar state_init_unseen
  by (auto simp: AFF_inv_def AF_outer_initial_def multigraph_inv_def out_graph_inv_def in_graph_inv_def)

lemma vit_current_V:
  "\<lbrakk>AFF_inv st; has_vertex (aff_vit st)\<rbrakk> \<Longrightarrow> current_vertex (aff_vit st) \<in> \<V>"
  using vertex_iterator.has_current[of "aff_vit st"]
    vertex_iterator.current_element[of "aff_vit st"]
    vertex_iterator.iterable_set_abstract(2)[of "aff_vit st"]
  by (auto simp: AFF_inv_def)

lemma vit_rem_finite:
  assumes "AFF_inv st"
  shows "finite (vit_remaining (aff_vit st))"
  by (rule finite_subset[where B="\<V>"]; insert assms \<V>_finite
      vertex_iterator.iterable_set_abstract(2)[of "aff_vit st"];
      auto simp: AFF_inv_def)

lemma vit_move_on:
  "\<lbrakk>AFF_inv st; has_vertex (aff_vit st)\<rbrakk> \<Longrightarrow> vit_invar (move_on_vertex (aff_vit st))"
    "\<lbrakk>AFF_inv st; has_vertex (aff_vit st)\<rbrakk> \<Longrightarrow> vit_abstract (move_on_vertex (aff_vit
      st)) \<subseteq> \<V>"
    "\<lbrakk>AFF_inv st; has_vertex (aff_vit st)\<rbrakk> \<Longrightarrow> card (vit_remaining (move_on_vertex
      (aff_vit st))) < card (vit_remaining (aff_vit st))"
    "\<lbrakk>AFF_inv st; has_vertex (aff_vit st)\<rbrakk> \<Longrightarrow> vit_iterated (move_on_vertex (aff_vit
      st)) = vit_iterated (aff_vit st) \<union> {current_vertex (aff_vit st)}"
    "\<lbrakk>AFF_inv st; has_vertex (aff_vit st)\<rbrakk> \<Longrightarrow> vit_abstract (move_on_vertex (aff_vit
      st)) = vit_abstract (aff_vit st)"
  using vit_rem_finite[of st] vertex_iterator.current_element[of "aff_vit st"]
    vertex_iterator.move_on_invar[of "aff_vit st"] vertex_iterator.move_on[of "aff_vit st"]
  by (auto simp: AFF_inv_def vertex_iterator.has_current intro: card_Diff1_less simp del: card_Diff_insert)

lemma AFF_inv_holds_1: "\<lbrakk>AF_outer_call_1_conds st; AFF_inv st\<rbrakk> \<Longrightarrow> AFF_inv
    (AF_outer_upd1 st)"
  using vit_move_on[of st]
  by (auto simp: AFF_inv_def AF_outer_upd1_def AF_outer_call_1_conds_def)

lemma AF_outer_launch:
  "\<lbrakk>multigraph_inv out_arr in_arr; AF_outer_call_2_conds st; AFF_inv st\<rbrakk> \<Longrightarrow> AF_inv
    (af_launch st)"
    "\<lbrakk>multigraph_inv out_arr in_arr; AF_outer_call_2_conds st; AFF_inv st\<rbrakk> \<Longrightarrow>
      AF_DFS_dom (af_launch st)"
  using vit_current_V[of st]
  by (auto simp: AF_outer_call_2_conds_def AFF_inv_def intro!: AF_inv_initial intro: AF_DFS_dom)

lemma AFF_inv_holds_2:
  assumes "multigraph_inv out_arr in_arr" "AF_outer_call_2_conds st" "AFF_inv st"
  shows "AFF_inv (AF_outer_upd2 st)"
proof-
  have "AF_inv (AF_DFS (af_launch st))"
       "\<not> af_unbounded (AF_DFS (af_launch st)) \<longrightarrow> af_vstack (AF_DFS (af_launch st)) = []"
    using AF_outer_launch[of st] assms AF_inv_holds[OF _ assms(1)] AF_DFS_ret_vstack
    by (auto)
  thus ?thesis
    using vit_move_on[of st] assms(3) assms(2)
    by (auto simp: AFF_inv_def AF_outer_upd2_def AF_outer_call_2_conds_def Let_def AF_inv_def
                   AF_invar_1_def AF_invar_2_def AF_invar_iter_def AF_invar_feas_def)
qed

text \<open>Outer-loop (hence whole-procedure) termination.\<close>

lemma AF_outer_call_terminates[termination_intros]:
  "\<lbrakk>AFF_inv st; AF_outer_call_1_conds st\<rbrakk> \<Longrightarrow>
    (AF_outer_upd1 st, st) \<in> measure (\<lambda>s. card (vit_remaining (aff_vit s)))"
  "\<lbrakk>AFF_inv st; AF_outer_call_2_conds st\<rbrakk> \<Longrightarrow>
    (AF_outer_upd2 st, st) \<in> measure (\<lambda>s. card (vit_remaining (aff_vit s)))"
  using vit_move_on(3)[of st]
  by (auto simp: AF_outer_upd1_def AF_outer_call_1_conds_def AF_outer_upd2_def AF_outer_call_2_conds_def Let_def)

lemma AF_outer_dom[termination_intros]:
  assumes "multigraph_inv out_arr in_arr" "AFF_inv st"
  shows "AF_outer_dom st"
  using assms
  by (induction st rule: wf_induct_rule[OF wf_measure[of "\<lambda>s. card (vit_remaining (aff_vit s))"]])
     (blast intro: AF_outer_domintros AF_outer_call_terminates AFF_inv_holds_1 AFF_inv_holds_2)

subsection \<open>Graph-array projection preservation: the acyclifier only moves cursors\<close>

text \<open>The outer loop, the inner DFS and the segment handler all touch @{const af_out_arr} /
      @{const af_in_arr} exclusively through @{term out_move}/@{term out_reset} (resp.
      @{term in_move}/@{term in_reset}).  Hence any projection @{term proj} that those two graph
      operations leave unchanged is preserved by the whole procedure.  Instantiated downstream (in the
      CSR setting) with the edge / lower-bound / upper-bound selectors, which the concrete cursor
      operations preserve, this shows the acyclifier returns the graph arrays with their static CSR
      structure intact --- only the cursor moves.\<close>

lemma af_reset_unsee_seg_out_proj:
  assumes "\<And>G v. proj (out_reset G v) = proj G"
  shows "proj (af_out_arr (af_reset_unsee_seg n vs st)) = proj (af_out_arr st)"
  by (induction n vs st rule: af_reset_unsee_seg.induct) (auto simp: af_reset_def assms)

lemma af_reset_unsee_seg_in_proj:
  assumes "\<And>G v. proj (in_reset G v) = proj G"
  shows "proj (af_in_arr (af_reset_unsee_seg n vs st)) = proj (af_in_arr st)"
  by (induction n vs st rule: af_reset_unsee_seg.induct) (auto simp: af_reset_def assms)

lemma af_handle_out_proj:
  assumes "\<And>G v. proj (out_reset G v) = proj G"
  shows "proj (af_out_arr (af_handle st a dir)) = proj (af_out_arr st)"
  by (cases rule: af_handle_cases_exec[of a st dir])
     (simp_all add: af_reset_unsee_seg_out_proj assms)

lemma af_handle_in_proj:
  assumes "\<And>G v. proj (in_reset G v) = proj G"
  shows "proj (af_in_arr (af_handle st a dir)) = proj (af_in_arr st)"
  by (cases rule: af_handle_cases_exec[of a st dir])
     (simp_all add: af_reset_unsee_seg_in_proj assms)

lemma AF_DFS_rel:
  assumes "AF_DFS_dom st" "multigraph_inv out_arr in_arr" "AF_inv st"
    "\<And>s. \<lbrakk>AF_DFS_call_1_conds s; AF_inv s\<rbrakk> \<Longrightarrow> R (AF_DFS_upd1 s) s"
    "\<And>s. \<lbrakk>AF_DFS_call_2_conds s; AF_inv s\<rbrakk> \<Longrightarrow> R (AF_DFS_upd2 s) s"
    "\<And>s. \<lbrakk>AF_DFS_call_3_conds s; AF_inv s\<rbrakk> \<Longrightarrow> R (AF_DFS_upd3 s) s"
    "\<And>s. R s s" "\<And>x y z. \<lbrakk>R x y; R y z\<rbrakk> \<Longrightarrow> R x z"
  shows "R (AF_DFS st) st"
  using assms(1,3)
proof(induction rule: AF_DFS_induct[consumes 1])
  case IH: (1 st)
  show ?case
    by (rule AF_DFS_cases[where st=st]; insert IH assms(2);
        simp only: AF_DFS_simps[OF IH(1)] AF_DFS_ret_def;
        (blast intro: assms(4-8) AF_inv_holds_1 AF_inv_holds_2 AF_inv_holds_3))
qed

lemma AF_outer_rel:
  assumes "multigraph_inv out_arr in_arr" "AF_outer_dom st" "AFF_inv st"
    "\<And>s. \<lbrakk>AF_outer_call_2_conds s; AFF_inv s\<rbrakk> \<Longrightarrow> R (AF_outer_upd2 s) s"
    "\<And>s. \<lbrakk>AF_outer_call_1_conds s; AFF_inv s\<rbrakk> \<Longrightarrow> R (AF_outer_upd1 s) s"
    "\<And>s. R s s" "\<And>x y z. \<lbrakk>R x y; R y z\<rbrakk> \<Longrightarrow> R x z"
  shows "R (AF_outer st) st"
  using assms(2,3)
proof(induction rule: AF_outer_induct[consumes 1])
  case IH: (1 st)
  show ?case
    by (rule AF_outer_cases[where st=st]; insert IH assms(1);
        simp only: AF_outer_simps[OF IH(1)] AF_outer_ret_def;
        (blast intro: assms(4-7) AFF_inv_holds_1 AFF_inv_holds_2))
qed

lemma AF_DFS_out_proj:
  assumes "\<And>G v. proj (out_move G v) = proj G" "\<And>G v. proj (out_reset G v) = proj G" "AF_DFS_dom st"
  shows "proj (af_out_arr (AF_DFS st)) = proj (af_out_arr st)"
  using assms(3)
proof(induction rule: AF_DFS_induct[consumes 1])
  case IH: (1 st)
  show ?case
    by (rule AF_DFS_cases[where st=st])
       (insert IH, (auto simp: AF_DFS_simps AF_DFS_upd1_def AF_DFS_upd2_def
         AF_DFS_upd3_def AF_DFS_ret_def Let_def af_handle_out_proj assms(1,2)))
qed

lemma AF_DFS_in_proj:
  assumes "\<And>G v. proj (in_move G v) = proj G" "\<And>G v. proj (in_reset G v) = proj G" "AF_DFS_dom st"
  shows "proj (af_in_arr (AF_DFS st)) = proj (af_in_arr st)"
  using assms(3)
proof(induction rule: AF_DFS_induct[consumes 1])
  case IH: (1 st)
  show ?case
    by (rule AF_DFS_cases[where st=st])
       (insert IH, (auto simp: AF_DFS_simps AF_DFS_upd1_def AF_DFS_upd2_def
         AF_DFS_upd3_def AF_DFS_ret_def Let_def af_handle_in_proj assms(1,2)))
qed

lemma AF_outer_out_proj:
  assumes "\<And>G v. proj (out_move G v) = proj G" "\<And>G v. proj (out_reset G v) = proj G"
    "multigraph_inv out_arr in_arr" "AFF_inv st"
  shows "proj (aff_out_arr (AF_outer st)) = proj (aff_out_arr st)"
  by (rule AF_outer_rel[where R="\<lambda>x y. proj (aff_out_arr x) = proj (aff_out_arr y)"];
      insert assms;
      (auto simp: AF_outer_upd1_def AF_outer_upd2_def Let_def
        AF_DFS_out_proj AF_outer_launch(2) intro: AF_outer_dom);
      simp add: AF_DFS_initial_def)

lemma AF_outer_in_proj:
  assumes "\<And>G v. proj (in_move G v) = proj G" "\<And>G v. proj (in_reset G v) = proj G"
    "multigraph_inv out_arr in_arr" "AFF_inv st"
  shows "proj (aff_in_arr (AF_outer st)) = proj (aff_in_arr st)"
  by (rule AF_outer_rel[where R="\<lambda>x y. proj (aff_in_arr x) = proj (aff_in_arr y)"];
      insert assms;
      (auto simp: AF_outer_upd1_def AF_outer_upd2_def Let_def
        AF_DFS_in_proj AF_outer_launch(2) intro: AF_outer_dom);
      simp add: AF_DFS_initial_def)

subsection \<open>Top level: the result is a feasible flow of no-greater cost\<close>

text \<open>Combining totality with the invariants: the outer loop preserves @{const AFF_inv} (so the returned
      flow is feasible) and never increases the cost (D3 lifted through @{const af_handle}, @{const AF_DFS}
      and @{const AF_outer}). Hence when @{const make_acyclic} returns @{term \<open>Some f'\<close>}, @{term f'} is a
      feasible flow with @{term \<open>\<C> (h \<circ> flow_lookup f') \<le> \<C> (h \<circ> flow_lookup f0)\<close>}.
        (The remaining conjunct of the
      correctness theorem, acyclicity of @{term f'}, is Theme F.)\<close>

lemma AFF_inv_holds:
  assumes "AF_outer_dom st" "multigraph_inv out_arr in_arr" "AFF_inv st"
  shows "AFF_inv (AF_outer st)"
  using assms(3)
proof(induction rule: AF_outer_induct[OF assms(1)])
  case IH: (1 st)
  show ?case
    by (rule AF_outer_cases[where st = st])
       (auto intro!: IH(2-4) AFF_inv_holds_1 AFF_inv_holds_2[OF assms(2)]
             simp: AF_outer_simps[OF IH(1)] AF_outer_ret_def)
qed

text \<open>The run from the initial state, when it returns a flow.\<close>

lemma make_acyclic_Some:
  "\<lbrakk>multigraph_inv out_arr in_arr; flow_invar f0; af_cap_feasible f0; vit_invar all_vertices; vit_abstract
    all_vertices \<subseteq> \<V>; make_acyclic f0 = Some f'\<rbrakk> \<Longrightarrow> AF_outer_dom (AF_outer_initial
    f0)"
    "\<lbrakk>multigraph_inv out_arr in_arr; flow_invar f0; af_cap_feasible f0; vit_invar all_vertices; vit_abstract
      all_vertices \<subseteq> \<V>; make_acyclic f0 = Some f'\<rbrakk> \<Longrightarrow> AFF_inv (AF_outer_initial f0)"
    "\<lbrakk>multigraph_inv out_arr in_arr; flow_invar f0; af_cap_feasible f0; vit_invar all_vertices; vit_abstract
      all_vertices \<subseteq> \<V>; make_acyclic f0 = Some f'\<rbrakk> \<Longrightarrow> f' = aff_flow (AF_outer
      (AF_outer_initial f0))"
    "\<lbrakk>multigraph_inv out_arr in_arr; flow_invar f0; af_cap_feasible f0; vit_invar all_vertices; vit_abstract
      all_vertices \<subseteq> \<V>; make_acyclic f0 = Some f'\<rbrakk> \<Longrightarrow> \<not> aff_unbounded
      (AF_outer (AF_outer_initial f0))"
  by (auto simp: make_acyclic_def Let_def split: if_splits intro!: AF_outer_dom AFF_inv_initial)

lemma make_acyclic_feasible:
  "\<lbrakk>multigraph_inv out_arr in_arr; flow_invar f0; af_cap_feasible f0; vit_invar all_vertices; vit_abstract
    all_vertices \<subseteq> \<V>; make_acyclic f0 = Some f'\<rbrakk> \<Longrightarrow> af_cap_feasible f'"
  using make_acyclic_Some[of f0 f'] AFF_inv_holds[of "AF_outer_initial f0"]
  by (auto simp: AFF_inv_def)

text \<open>Relations between a state and its successor, lifted through the inner DFS and the outer loop.\<close>

text \<open>A flow relation established by every @{const af_handle} carries over to the two advancing
      DFS steps.\<close>

lemma AF_DFS_upd_flow:
  fixes st :: "('v, 'e, 'farr, 'g, 'sarr, 'z) AF_DFS_state_scheme"
  assumes "\<And>(s :: ('v, 'e, 'farr, 'g, 'sarr, 'z) AF_DFS_state_scheme) a dir. \<lbrakk>AF_invar_1 s; AF_invar_2 s;
    AF_invar_3 s; AF_invar_feas s; AF_invar_estE s; a \<in> \<E>;
             (if dir then fst a else snd a) = hd (af_vstack s); af_vstack s \<noteq> []\<rbrakk>
             \<Longrightarrow> Q (af_flow (af_handle s a dir)) (af_flow s)"
    "AF_inv st"
  shows "AF_DFS_call_1_conds st \<Longrightarrow> Q (af_flow (AF_DFS_upd1 st)) (af_flow st)"
    "AF_DFS_call_2_conds st \<Longrightarrow> Q (af_flow (AF_DFS_upd2 st)) (af_flow st)"
proof-
  have i: "AF_invar_1 st" "AF_invar_2 st" "AF_invar_3 st" "AF_invar_feas st" "AF_invar_estE st"
    "AF_invar_iter st" "AF_invar_V st"
    using assms(2)
    by (auto simp: AF_inv_def)
  show "Q (af_flow (AF_DFS_upd1 st)) (af_flow st)" if "AF_DFS_call_1_conds st"
  proof(rule AF_DFS_upd1_scan[OF that i(6,7)])
    fix a
    assume a: "AF_DFS_upd1 st = af_handle (st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack
      st))\<rparr>) a True"
      "a \<in> \<E>" "fst a = hd (af_vstack st)" "af_vstack st \<noteq> []" "hd (af_vstack st) \<in> \<V>"
    have "Q (af_flow (af_handle (st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack st))\<rparr>) a True))
            (af_flow (st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack st))\<rparr>))"
      by (rule assms(1)) (insert i a, auto intro: AF_invar_1_out_advance)
    thus ?thesis
      using a(1)
      by simp
  qed
  show "Q (af_flow (AF_DFS_upd2 st)) (af_flow st)" if "AF_DFS_call_2_conds st"
  proof(rule AF_DFS_upd2_scan[OF that i(6,7)])
    fix a
    assume a: "AF_DFS_upd2 st = af_handle (st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack st))\<rparr>)
      a False"
      "a \<in> \<E>" "snd a = hd (af_vstack st)" "af_vstack st \<noteq> []" "hd (af_vstack st) \<in> \<V>"
    have "Q (af_flow (af_handle (st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack st))\<rparr>) a False))
            (af_flow (st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack st))\<rparr>))"
      by (rule assms(1)) (insert i a, auto intro: AF_invar_1_in_advance)
    thus ?thesis
      using a(1)
      by simp
  qed
qed

lemma af_handle_cost_le:
  assumes "AF_invar_1 st" "AF_invar_2 st" "AF_invar_3 st" "AF_invar_feas st" "AF_invar_estE st" "a \<in> \<E>"
    "(if dir then fst a else snd a) = hd (af_vstack st)" "af_vstack st \<noteq> []"
  shows "\<C> (h \<circ> flow_lookup (af_flow (af_handle st a dir))) \<le> \<C> (h \<circ> flow_lookup (af_flow st))"
  using assms(6)
proof(cases rule: af_handle_cases[of a st dir])
  case selfloop
  thus ?thesis
    using af_selfloop_handle_cost_le[OF assms(6), of st] assms(1,4)
    by (simp add: AF_invar_1_def AF_invar_feas_def)
next
  case (cancel up dn fl m')
  have "hd (af_vstack st) \<in> {fst a, snd a}"
    using assms(7)
    by (cases dir) auto
  hence "distinct (a # af_estack st)"
    using a_notin_estack_incident[OF assms(2,3) _ assms(8) cancel(4)] estack_distinct assms(2,3)
    by (simp)
  thus ?thesis
    using af_cancel_seg_cost_le_gen[OF _ _ _ assms(6) _ cancel(2,6)] assms(1,4,5) cancel(7)
    by (simp add: AF_invar_feas_def AF_invar_1_def AF_invar_estE_def)
qed (simp_all)

lemma AF_DFS_cost_le:
  "\<lbrakk>AF_DFS_dom st; multigraph_inv out_arr in_arr; AF_inv st\<rbrakk>
   \<Longrightarrow> \<C> (h \<circ> flow_lookup (af_flow (AF_DFS st))) \<le> \<C> (h \<circ> flow_lookup (af_flow st))"
  by (rule AF_DFS_rel[where R = "\<lambda>x y. \<C> (h \<circ> flow_lookup (af_flow x)) \<le> \<C> (h \<circ>
    flow_lookup (af_flow y))"])
     (auto simp: AF_DFS_upd3_def intro: order_trans
           AF_DFS_upd_flow[where Q = "\<lambda>f g. \<C> (h \<circ> flow_lookup f) \<le> \<C> (h \<circ> flow_lookup
             g)", OF af_handle_cost_le])

lemma AF_outer_cost_le:
  assumes "AF_outer_dom st" "multigraph_inv out_arr in_arr" "AFF_inv st"
  shows "\<C> (h \<circ> flow_lookup (aff_flow (AF_outer st))) \<le> \<C> (h \<circ> flow_lookup (aff_flow st))"
proof(rule AF_outer_rel[where R="\<lambda>x y. \<C> (h \<circ> flow_lookup (aff_flow x)) \<le> \<C> (h \<circ>
    flow_lookup (aff_flow y))"])
  fix s
  assume "AF_outer_call_2_conds s" "AFF_inv s"
  then have "AF_DFS_dom (af_launch s)" "AF_inv (af_launch s)"
    using assms(2) AF_outer_launch[of s]
    by auto
  then show "\<C> (h \<circ> flow_lookup (aff_flow (AF_outer_upd2 s))) \<le> \<C> (h \<circ> flow_lookup (aff_flow s))"
    using assms(2) AF_DFS_cost_le[of "af_launch s"]
    by (simp add: AF_outer_upd2_def Let_def AF_DFS_initial_def)
qed (insert assms, auto simp: AF_outer_upd1_def)

lemma make_acyclic_cost_le:
  "\<lbrakk>multigraph_inv out_arr in_arr; flow_invar f0; af_cap_feasible f0; vit_invar all_vertices; vit_abstract
    all_vertices \<subseteq> \<V>; make_acyclic f0 = Some f'\<rbrakk> \<Longrightarrow> \<C> (h \<circ> flow_lookup
    f') \<le> \<C> (h \<circ> flow_lookup f0)"
  using make_acyclic_Some[of f0 f'] AF_outer_cost_le[of "AF_outer_initial f0"]
  by (auto simp: AF_outer_initial_def)

subsection \<open>Cancellation preserves the balance through the whole run\<close>

text \<open>The divergence half of Theme D1, lifted to @{const make_acyclic}: every @{const af_handle} step
      leaves every vertex's excess unchanged (a step either does not touch the flow, or cancels a
      cycle, which by @{thm af_cancel_seg_ex_pres} preserves excess), hence so does the whole DFS and
      the outer loop. This threads exactly like the cost bound, but as an \emph{equality}.\<close>

lemma af_handle_ex:
  assumes "AF_invar_1 st" "AF_invar_2 st" "AF_invar_3 st" "AF_invar_feas st" "AF_invar_estE st" "a \<in> \<E>"
    "(if dir then fst a else snd a) = hd (af_vstack st)" "af_vstack st \<noteq> []"
  shows "ex (h \<circ> flow_lookup (af_flow (af_handle st a dir))) v = ex (h \<circ> flow_lookup (af_flow st)) v"
  using assms(6)
proof(cases rule: af_handle_cases[of a st dir])
  case selfloop
  thus ?thesis
    using af_selfloop_handle_ex[OF assms(6) selfloop(1), of st v] assms(1)
    by (simp add: AF_invar_1_def)
next
  case (cancel up dn fl m')
  have "(if dir then snd a else fst a) \<in> set (tl (af_vstack st))"
    using cancel(1,5) assms(2,7,8) fst_E_V assms(6) snd_E_V assms(6)
    by (cases "af_vstack st"; cases dir) (auto simp: AF_invar_2_def)
  moreover have "Suc (length (af_estack st)) = length (af_vstack st)" "length (af_dstack st) = length (af_estack st)"
    using assms(2,8)
    by (auto simp: AF_invar_2_def)
  ultimately show ?thesis
    using af_cancel_seg_ex_pres[OF _ _ _ assms(6) _ _ _ assms(7) refl cancel(6)] assms(1,3,5) cancel(7)
    by (simp add: AF_invar_1_def AF_invar_3_conv AF_invar_estE_def)
qed (simp_all)

lemma AF_DFS_ex:
  "\<lbrakk>AF_DFS_dom st; multigraph_inv out_arr in_arr; AF_inv st\<rbrakk>
   \<Longrightarrow> ex (h \<circ> flow_lookup (af_flow (AF_DFS st))) v = ex (h \<circ> flow_lookup (af_flow st)) v"
  by (rule AF_DFS_rel[where R = "\<lambda>x y. ex (h \<circ> flow_lookup (af_flow x)) v = ex (h \<circ> flow_lookup
    (af_flow y)) v"])
     (auto simp: AF_DFS_upd3_def
           intro: AF_DFS_upd_flow[where Q = "\<lambda>f g. ex (h \<circ> flow_lookup f) v = ex (h \<circ> flow_lookup
             g) v",
                                  OF af_handle_ex])

lemma AF_outer_ex:
  assumes "AF_outer_dom st" "multigraph_inv out_arr in_arr" "AFF_inv st"
  shows "ex (h \<circ> flow_lookup (aff_flow (AF_outer st))) v = ex (h \<circ> flow_lookup (aff_flow st)) v"
proof(rule AF_outer_rel[where R="\<lambda>x y. ex (h \<circ> flow_lookup (aff_flow x)) v = ex (h \<circ> flow_lookup
    (aff_flow y)) v"])
  fix s
  assume "AF_outer_call_2_conds s" "AFF_inv s"
  then have "AF_DFS_dom (af_launch s)" "AF_inv (af_launch s)"
    using assms(2) AF_outer_launch[of s]
    by auto
  then show "ex (h \<circ> flow_lookup (aff_flow (AF_outer_upd2 s))) v = ex (h \<circ> flow_lookup (aff_flow s)) v"
    using assms(2) AF_DFS_ex[of "af_launch s"]
    by (simp add: AF_outer_upd2_def Let_def AF_DFS_initial_def)
qed (insert assms, auto simp: AF_outer_upd1_def)

lemma make_acyclic_ex:
  "\<lbrakk>multigraph_inv out_arr in_arr; flow_invar f0; af_cap_feasible f0; vit_invar all_vertices; vit_abstract
    all_vertices \<subseteq> \<V>; make_acyclic f0 = Some f'\<rbrakk> \<Longrightarrow> ex (h \<circ> flow_lookup f')
    v = ex (h \<circ> flow_lookup f0) v"
  using make_acyclic_Some[of f0 f'] AF_outer_ex[of "AF_outer_initial f0"]
  by (auto simp: AF_outer_initial_def)

text \<open>Feasibility as a genuine @{term b}-flow is preserved: the output keeps capacity feasibility
      (@{thm make_acyclic_feasible}) and, since every vertex's excess is unchanged
      (@{thm make_acyclic_ex}), the same balance @{term b} as the input.\<close>

lemma make_acyclic_feasible_bal:
  "\<lbrakk>multigraph_inv out_arr in_arr; flow_invar f0; af_feasible b f0; vit_invar all_vertices; vit_abstract
    all_vertices \<subseteq> \<V>; make_acyclic f0 = Some f'\<rbrakk> \<Longrightarrow> af_feasible b f'"
  using make_acyclic_feasible[of f0 f'] make_acyclic_ex[of f0 f']
    af_feasible_cap[of b f0] af_feasible_bal[of b f0]
  by (auto intro!: af_feasibleI)

subsection \<open>Theme F, part 1: reducing acyclicity to the absence of a free cycle\<close>

text \<open>The residual definition of @{const acyclic_flow} (no residual closed walk augmenting in both
      directions) is equivalent, on the underlying arcs, to the absence of a closed walk of distinct
      \emph{free} arcs (@{const af_arc_free}). We eliminate the residual layer here: an arc that admits
      positive residual capacity in \emph{both} directions is exactly a free arc, because the forward
      residual capacity of an arc is its capacity minus its flow and the backward residual capacity is
      the flow itself. Hence @{const acyclic_flow} follows from the purely combinatorial statement that
      the returned flow carries no closed trail of distinct free arcs --- the goal the DFS exploration
      engine (Theme F, part 2) discharges.\<close>

lemma residual_both_ways_free:
  assumes "0 < \<uu>\<^bsub>h \<circ> flow_lookup f'\<^esub> e" "0 < \<uu>\<^bsub>h \<circ> flow_lookup f'\<^esub>
    (erev e)" "e \<in> \<EE>"
  shows "af_arc_free f' (oedge e)"
proof-
  have "0 < flow_lookup f' (oedge e)" "ereal (h (flow_lookup f' (oedge e))) < \<u> (oedge e)"
    using assms(1,2) u_non_neg[of "oedge e"]
    by (cases e; cases "\<u> (oedge e)"; auto)+
  thus ?thesis
    using cap_encoding[of "oedge e"] assms(3)
    by (auto simp: af_arc_free_def \<EE>_def split: if_splits)
qed

lemma acyclic_witness_arcs_free:
  assumes "augpath (h \<circ> flow_lookup f') C" "augpath (h \<circ> flow_lookup f') (map erev (rev C))"
    "e \<in> set C" "e \<in> \<EE>"
  shows "af_arc_free f' (oedge e)"
proof(rule residual_both_ways_free[OF _ _ assms(4)])
  show "0 < \<uu>\<^bsub>h \<circ> flow_lookup f'\<^esub> e"
    using assms(1,3)
    by (auto simp: augpath_def intro: rcap_extr_non_zero[where es = C and ES = "set C"])
  show "0 < \<uu>\<^bsub>h \<circ> flow_lookup f'\<^esub> (erev e)"
    using assms(2,3)
    by (auto simp: augpath_def
             intro: rcap_extr_non_zero[where es = "map erev (rev C)" and ES = "set (map erev (rev C))"])
qed

lemma acyclic_flow_from_no_free_cycle:
  "\<nexists>C. prepath C \<and> (\<forall>e\<in>set C. af_arc_free f' (oedge e)) \<and> distinct (map oedge C)
              \<and> fstv (hd C) = sndv (last C) \<and> set C \<subseteq> \<EE> \<Longrightarrow> acyclic_flow (h
                \<circ> flow_lookup f')"
  by (fastforce simp: augpath_def dest: acyclic_witness_arcs_free)

text \<open>The converse bridge, used when consuming acyclicity: a \emph{free} arc admits strictly positive
      residual capacity in both directions (forward @{term \<open>\<u> a - f a\<close>} --- positive because either the
      capacity is infinite or the flow is below it --- and backward @{term \<open>f a\<close>} --- positive because the
      flow is strictly positive). Hence a closed pre-path of free arcs is augmenting in both directions,
      which an @{const acyclic_flow} forbids.\<close>

lemma free_arc_both_ways:
  assumes "af_arc_free f' (oedge e)" "e \<in> \<EE>"
  shows "0 < rcap (h \<circ> flow_lookup f') e \<and> 0 < rcap (h \<circ> flow_lookup f') (erev e)"
proof-
  have "0 < \<u> (oedge e) - ereal (h (flow_lookup f' (oedge e)))" "0 < flow_lookup f' (oedge e)"
    using assms cap_encoding[of "oedge e"] u_non_neg[of "oedge e"]
    by (auto simp: af_arc_free_def Let_def \<EE>_def zero_ereal_def split: if_splits)
  thus ?thesis
    by (cases e) (simp_all add: comp_def)
qed

text \<open>Consuming acyclicity: an @{const acyclic_flow} has \emph{no} closed pre-path of pairwise
      distinct free arcs. This is the exact converse of @{thm acyclic_flow_from_no_free_cycle} and is
      what the initial-basis construction uses to prove the free edges form a forest (every free edge
      is a tree edge).\<close>

lemma acyclic_flow_no_free_cycle:
  "acyclic_flow (h \<circ> flow_lookup f') \<Longrightarrow> \<nexists>C. prepath C \<and> (\<forall>e\<in>set C.
    af_arc_free f' (oedge e)) \<and> distinct (map oedge C)
              \<and> fstv (hd C) = sndv (last C) \<and> set C \<subseteq> \<EE>"
  using free_arc_both_ways
  by (blast dest: acyclic_no_free_closed_prepath)

subsection \<open>Theme F, part 2: the exploration engine\<close>

text \<open>A predicate that every @{const af_handle} preserves, and that ignores the iterator arrays, is
      preserved by the advancing DFS steps, and, given the pop step, by the whole DFS.\<close>

lemma AF_inv_out_advance:
  "\<lbrakk>AF_inv st; AF_DFS_call_1_conds st\<rbrakk>
   \<Longrightarrow> AF_inv (st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack st))\<rparr>)"
  by (auto elim!: call_cond_elims simp: AF_inv_def AF_invar_iter_def AF_invar_V_def
           intro: AF_invar_1_out_advance multigraph_inv_out_advance)

lemma AF_inv_in_advance:
  "\<lbrakk>AF_inv st; AF_DFS_call_2_conds st\<rbrakk>
   \<Longrightarrow> AF_inv (st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack st))\<rparr>)"
  by (auto elim!: call_cond_elims simp: AF_inv_def AF_invar_iter_def AF_invar_V_def
           intro: AF_invar_1_in_advance multigraph_inv_in_advance)

lemma AF_DFS_upd_pred:
  assumes "\<And>s a dir. \<lbrakk>AF_inv s; a \<in> \<E>; (if dir then fst a else snd a) = hd (af_vstack s);
                       af_vstack s \<noteq> []; P s\<rbrakk> \<Longrightarrow> P (af_handle s a dir)"
    "\<And>s X. P (s\<lparr>af_out_arr := X\<rparr>) = P s" "\<And>s X. P (s\<lparr>af_in_arr := X\<rparr>) = P s"
      "AF_inv st" "P st"
  shows "AF_DFS_call_1_conds st \<Longrightarrow> P (AF_DFS_upd1 st)" "AF_DFS_call_2_conds st \<Longrightarrow> P
    (AF_DFS_upd2 st)"
proof-
  show "P (AF_DFS_upd1 st)" if "AF_DFS_call_1_conds st"
    by (rule AF_DFS_upd1_scan[where st=st]; insert assms that AF_inv_out_advance[of st];
        (auto simp: AF_inv_def intro: assms(1) AF_inv_out_advance))
  show "P (AF_DFS_upd2 st)" if "AF_DFS_call_2_conds st"
    by (rule AF_DFS_upd2_scan[where st=st]; insert assms that AF_inv_in_advance[of st];
        (auto simp: AF_inv_def intro: assms(1) AF_inv_in_advance))
qed

lemma AF_DFS_pred:
  assumes "AF_DFS_dom st" "multigraph_inv out_arr in_arr" "AF_inv st" "P st"
    "\<And>s a dir. \<lbrakk>AF_inv s; a \<in> \<E>; (if dir then fst a else snd a) = hd (af_vstack s);
                 af_vstack s \<noteq> []; P s\<rbrakk> \<Longrightarrow> P (af_handle s a dir)"
    "\<And>s X. P (s\<lparr>af_out_arr := X\<rparr>) = P s" "\<And>s X. P (s\<lparr>af_in_arr := X\<rparr>) = P s"
    "\<And>s. \<lbrakk>AF_DFS_call_3_conds s; AF_inv s; P s\<rbrakk> \<Longrightarrow> P (AF_DFS_upd3 s)"
  shows "P (AF_DFS st)"
  by (rule AF_DFS_rel[where R="\<lambda>x y. P y \<longrightarrow> P x", THEN mp]; insert assms;
      (auto intro: AF_DFS_upd_pred))

text \<open>A first load-bearing building block: \emph{finished vertices stay finished}. No @{const af_handle}
      branch ever un-finishes a vertex --- a push touches only a fresh (@{term Unseen}) vertex, a
      cancellation's reset un-sees only \emph{stack} vertices (which are @{term OnStack}, never
      @{term Finished}), and the flow-only branches leave @{const af_state} untouched.\<close>

lemma af_finished_off_stack:
  "\<lbrakk>AF_invar_2 st; AF_invar_V st; st_lookup (af_state st) w = Finished\<rbrakk> \<Longrightarrow> w \<notin>
    set (af_vstack st)"
  by (fastforce simp: AF_invar_2_def AF_invar_V_def)

lemma af_handle_finished_mono:
  assumes "AF_invar_1 st" "AF_invar_2 st" "a \<in> \<E>" "AF_invar_V st" "st_lookup (af_state st) w = Finished"
  shows "st_lookup (af_state (af_handle st a dir)) w = Finished"
  using assms(3)
  by (cases rule: af_handle_cases[of a st dir]; insert assms af_finished_off_stack[of st w] fst_E_V[of a] snd_E_V[of a];
      (auto simp: AF_invar_1_def AF_invar_V_def state_arr.fixed_univ_map_upd
        af_reset_unsee_seg_state dest: in_set_takeD split: if_splits))

lemma af_finished_mono_upd3:
  "\<lbrakk>AF_DFS_call_3_conds st; AF_inv st; st_lookup (af_state st) w = Finished\<rbrakk>
   \<Longrightarrow> st_lookup (af_state (AF_DFS_upd3 st)) w = Finished"
  by (auto elim!: call_cond_elims
           simp: AF_inv_def AF_invar_1_def AF_invar_V_def AF_DFS_upd3_def state_arr.fixed_univ_map_upd)

lemma AF_DFS_finished_mono:
  "\<lbrakk>AF_DFS_dom st; multigraph_inv out_arr in_arr\<rbrakk>
   \<Longrightarrow> AF_inv st \<longrightarrow> st_lookup (af_state st) w = Finished \<longrightarrow> st_lookup
     (af_state (AF_DFS st)) w = Finished"
  by (auto intro!: AF_DFS_pred[where P = "\<lambda>s. st_lookup (af_state s) w = Finished"] af_finished_mono_upd3
           intro: af_handle_finished_mono simp: AF_inv_def)

text \<open>Second building block: \emph{vertex coverage}. The DFS root stays at the bottom of the stack
      (@{const af_handle} and the pop keep @{term \<open>last (af_vstack st)\<close>} fixed, since the back-edge
      truncation drops at most @{term \<open>length (af_estack st)\<close>} vertices, one fewer than the stack), so
      when the DFS returns without flagging unboundedness (empty stack) the root has been finished. An
      outer-loop invariant then propagates this: every vertex the vertex iterator has already passed is
      finished. At outer termination the iterator is exhausted, so --- assuming it enumerates all of
      @{term \<V>} --- every vertex is finished.\<close>

lemma af_handle_vstack_last:
  assumes "AF_invar_2 st" "af_vstack st \<noteq> []" "last (af_vstack st) = v"
  shows "af_vstack (af_handle st a dir) \<noteq> [] \<and> last (af_vstack (af_handle st a dir)) = v"
  by (rule af_handle_cases_exec[of a st dir]; insert assms;
      (auto simp: AF_invar_2_def last_drop drop_eq_Nil dest: af_cancel_seg_drop_bound))

definition "af_root_ok v st \<longleftrightarrow>
  (af_vstack st \<noteq> [] \<and> last (af_vstack st) = v) \<or> st_lookup (af_state st) v = Finished"

lemma af_handle_root_ok:
  "\<lbrakk>AF_invar_1 st; AF_invar_2 st; a \<in> \<E>; AF_invar_V st; af_root_ok v st\<rbrakk>
   \<Longrightarrow> af_root_ok v (af_handle st a dir)"
  using af_handle_finished_mono[of st a v dir] af_handle_vstack_last[of st v a dir]
  by (auto simp: af_root_ok_def)

lemma af_root_ok_upd3:
  assumes "AF_DFS_call_3_conds st" "AF_inv st" "af_root_ok v st"
  shows "af_root_ok v (AF_DFS_upd3 st)"
proof-
  obtain u us where vv: "af_vstack st = u # us"
    using assms(1)
    by (auto elim!: call_cond_elims)
  hence "st_invar (af_state st)" "u \<in> \<V>"
    using assms(2)
    by (auto simp: AF_inv_def AF_invar_1_def AF_invar_V_def)
  thus ?thesis
    using vv assms(3)
    by (cases us) (auto simp: af_root_ok_def AF_DFS_upd3_def state_arr.fixed_univ_map_upd)
qed

lemma AF_DFS_root_ok:
  "\<lbrakk>AF_DFS_dom st; multigraph_inv out_arr in_arr\<rbrakk>
   \<Longrightarrow> AF_inv st \<longrightarrow> af_root_ok v st \<longrightarrow> af_root_ok v (AF_DFS st)"
  by (intro impI AF_DFS_pred[where P = "af_root_ok v"] af_root_ok_upd3 af_handle_root_ok)
     (auto simp: AF_inv_def af_root_ok_def)

lemma AF_DFS_root_finished:
  "\<lbrakk>AF_DFS_dom st; multigraph_inv out_arr in_arr; AF_inv st; af_root_ok v st; \<not> af_unbounded (AF_DFS
    st)\<rbrakk>
   \<Longrightarrow> st_lookup (af_state (AF_DFS st)) v = Finished"
  using AF_DFS_root_ok[of st v] AF_DFS_ret_vstack[of st]
  by (auto simp: af_root_ok_def)

text \<open>A predicate that every outer step preserves holds of the result.\<close>

lemma AF_outer_pred:
  assumes "multigraph_inv out_arr in_arr" "AF_outer_dom st" "AFF_inv st" "P st"
    "\<And>s. \<lbrakk>AF_outer_call_2_conds s; AFF_inv s; P s\<rbrakk> \<Longrightarrow> P (AF_outer_upd2 s)"
    "\<And>s. \<lbrakk>AF_outer_call_1_conds s; AFF_inv s; P s\<rbrakk> \<Longrightarrow> P (AF_outer_upd1 s)"
  shows "P (AF_outer st)"
  by (rule AF_outer_rel[where R="\<lambda>x y. P y \<longrightarrow> P x", THEN mp]; insert assms;
      (auto))

definition "AFF_cov st \<longleftrightarrow>
  (\<not> aff_unbounded st \<longrightarrow> (\<forall>v \<in> vit_iterated (aff_vit st). st_lookup (aff_state st) v =
    Finished))"

lemma AFF_cov_holds_1:
  assumes "AF_outer_call_1_conds st" "AFF_inv st" "AFF_cov st"
  shows "AFF_cov (AF_outer_upd1 st)"
proof-
  have c: "\<not> aff_unbounded st" "has_vertex (aff_vit st)"
    "st_lookup (aff_state st) (current_vertex (aff_vit st)) \<noteq> Unseen"
    using assms(1)
    by (auto simp: AF_outer_call_1_conds_def)
  hence "st_lookup (aff_state st) (current_vertex (aff_vit st)) = Finished"
    using assms(2) vit_current_V[of st] assms(2) c(2)
    by (cases "st_lookup (aff_state st) (current_vertex (aff_vit st))") (auto simp: AFF_inv_def)
  thus ?thesis
    using assms(3) c vit_move_on(4)[of st] assms(2) c(2)
    by (auto simp: AFF_cov_def AF_outer_upd1_def)
qed

lemma AFF_cov_holds_2:
  assumes "multigraph_inv out_arr in_arr" "AF_outer_call_2_conds st" "AFF_inv st" "AFF_cov st"
  shows "AFF_cov (AF_outer_upd2 st)"
proof-
  have c: "\<not> aff_unbounded st" "has_vertex (aff_vit st)"
    "st_lookup (aff_state st) (current_vertex (aff_vit st)) = Unseen"
    using assms(2)
    by (auto simp: AF_outer_call_2_conds_def)
  have l: "AF_inv (af_launch st)" "AF_DFS_dom (af_launch st)"
    using AF_outer_launch[of st] assms(1-3)
    by (auto)
  have "st_lookup (af_state (af_launch st)) w = Finished" if "w \<in> vit_iterated (aff_vit st)" for w
    using that assms(3,4) c vit_current_V[of st] assms(3) c(2)
    by (auto simp: AFF_cov_def AFF_inv_def AF_DFS_initial_def state_arr.fixed_univ_map_upd)
  hence "st_lookup (af_state (AF_DFS (af_launch st))) w = Finished" if "w \<in> vit_iterated (aff_vit st)" for w
    using that AF_DFS_finished_mono[where st="af_launch st"] l(2) assms(1) l(1)
    by (blast)
  moreover have "\<not> af_unbounded (AF_DFS (af_launch st))
                 \<longrightarrow> st_lookup (af_state (AF_DFS (af_launch st))) (current_vertex (aff_vit st)) =
                   Finished"
    using AF_DFS_root_finished[where st="af_launch st"] l(2) assms(1) l(1)
    by (auto simp: af_root_ok_def AF_DFS_initial_def)
  ultimately show ?thesis
    using vit_move_on(4)[of st] assms(3) c(2)
    by (auto simp: AFF_cov_def AF_outer_upd2_def Let_def)
qed

lemma AF_outer_inv_cov:
  "\<lbrakk>AF_outer_dom st; multigraph_inv out_arr in_arr\<rbrakk>
   \<Longrightarrow> AFF_inv st \<and> AFF_cov st \<longrightarrow> AFF_inv (AF_outer st) \<and> AFF_cov (AF_outer st)"
  using AFF_inv_holds[of st]
  by (auto intro!: AF_outer_pred[where P = AFF_cov] intro: AFF_cov_holds_1 AFF_cov_holds_2)

lemma AF_outer_ret_reached:
  assumes "AF_outer_dom st"
  shows "\<not> aff_unbounded (AF_outer st) \<longrightarrow> \<not> has_vertex (aff_vit (AF_outer st))"
  using assms
proof(induction rule: AF_outer_induct[consumes 1])
  case IH: (1 st)
  show ?case
    by (rule AF_outer_cases[where st=st]; insert IH;
        auto simp: AF_outer_simps[OF IH(1)] AF_outer_ret_def elim!: call_cond_elims)
qed

lemma AF_outer_abstract:
  "\<lbrakk>AF_outer_dom st; multigraph_inv out_arr in_arr\<rbrakk>
   \<Longrightarrow> AFF_inv st \<longrightarrow> vit_abstract (aff_vit (AF_outer st)) = vit_abstract (aff_vit st)"
  by (intro impI AF_outer_rel[where R = "\<lambda>x y. vit_abstract (aff_vit x) = vit_abstract (aff_vit y)"])
     (auto simp: AF_outer_upd1_def AF_outer_upd2_def Let_def vit_move_on(5) elim!: call_cond_elims)

lemma AF_outer_cov_terminal:
  "\<lbrakk>AF_outer_dom st; multigraph_inv out_arr in_arr; AFF_inv st; AFF_cov st; \<not> aff_unbounded (AF_outer
    st)\<rbrakk> \<Longrightarrow> \<forall>v \<in> vit_abstract (aff_vit (AF_outer st)). st_lookup (aff_state
    (AF_outer st)) v = Finished"
  using AF_outer_inv_cov[of st] AF_outer_ret_reached[of st]
    vertex_iterator.has_current[of "aff_vit (AF_outer st)"]
    vertex_iterator.iterable_set_abstract(2)[of "aff_vit (AF_outer st)"]
  by (auto simp: AFF_cov_def AFF_inv_def)

text \<open>The acyclifier returns a well-formed flow array: @{const AFF_inv} carries @{term flow_invar}
      through the whole outer loop, so it holds of the returned @{term \<open>aff_flow\<close>}.  With a
      length-pinned @{term flow_invar} at the list instantiation this is exactly length preservation,
      which is what the augmented-array glue downstream needs.\<close>

lemma make_acyclic_flow_invar:
  "\<lbrakk>multigraph_inv out_arr in_arr; flow_invar f0; af_cap_feasible f0; vit_invar all_vertices; vit_abstract
    all_vertices \<subseteq> \<V>; vit_iterated all_vertices = {}; make_acyclic f0 = Some f'\<rbrakk>
    \<Longrightarrow> flow_invar f'"
  using make_acyclic_Some[of f0 f'] AFF_inv_holds[of "AF_outer_initial f0"]
  by (auto simp: AFF_inv_def)

lemma make_acyclic_all_finished:
  "\<lbrakk>multigraph_inv out_arr in_arr; flow_invar f0; af_cap_feasible f0; vit_invar all_vertices; vit_abstract
    all_vertices = \<V>; vit_iterated all_vertices = {}; make_acyclic f0 = Some f'\<rbrakk> \<Longrightarrow>
    \<forall>v \<in> \<V>. st_lookup (aff_state (AF_outer (AF_outer_initial f0))) v = Finished"
  using make_acyclic_Some[of f0 f'] AF_outer_cov_terminal[of "AF_outer_initial f0"]
    AF_outer_abstract[of "AF_outer_initial f0"]
  by (auto simp: AFF_cov_def AF_outer_initial_def)

text \<open>Third building block: \emph{edge exhaustion}. A finished vertex has consumed both its edge
      iterators (their remaining-edge sets are empty), because a vertex is finished exactly at the pop, whose
      guard @{const AF_DFS_call_3_conds} says both iterators have no current edge; and thereafter its
      array entries are frozen --- the per-step advance only touches the top vertex and the back-edge
      reset only touches dropped (on-stack) vertices, never a finished one. So at termination every
      vertex --- being finished (coverage) --- has scanned \emph{all} its incident edges.\<close>

lemma af_reset_unsee_seg_out_lookup:
  "\<lbrakk>out_invar (af_out_arr st); w \<notin> set (take n vs); set vs \<subseteq> \<V>\<rbrakk>
   \<Longrightarrow> out_remaining (af_out_arr (af_reset_unsee_seg n vs st)) w = out_remaining (af_out_arr st) w
     \<and> out_iterated (af_out_arr (af_reset_unsee_seg n vs st)) w = out_iterated (af_out_arr st) w"
  by (induction n vs st rule: af_reset_unsee_seg.induct)
     (auto simp: af_reset_def out_reset_invar outg.idx_reset_remaining_other outg.idx_reset_iterated_other)

lemma af_reset_unsee_seg_in_lookup:
  "\<lbrakk>in_invar (af_in_arr st); w \<notin> set (take n vs); set vs \<subseteq> \<V>\<rbrakk>
   \<Longrightarrow> in_remaining (af_in_arr (af_reset_unsee_seg n vs st)) w = in_remaining (af_in_arr st) w
     \<and> in_iterated (af_in_arr (af_reset_unsee_seg n vs st)) w = in_iterated (af_in_arr st) w"
  by (induction n vs st rule: af_reset_unsee_seg.induct)
     (auto simp: af_reset_def in_reset_invar ing.idx_reset_remaining_other ing.idx_reset_iterated_other)

definition "AF_invar_exh st \<longleftrightarrow>
  (\<forall>v\<in>\<V>. st_lookup (af_state st) v = Finished \<longrightarrow>
        out_remaining (af_out_arr st) v = {} \<and> in_remaining (af_in_arr st) v = {})"

lemma af_handle_arr_off:
  assumes "AF_invar_1 st" "AF_invar_2 st" "AF_invar_V st" "st_lookup (af_state st) v = Finished"
  shows "out_remaining (af_out_arr (af_handle st a dir)) v = out_remaining (af_out_arr st) v
       \<and> out_iterated (af_out_arr (af_handle st a dir)) v = out_iterated (af_out_arr st) v
       \<and> in_remaining (af_in_arr (af_handle st a dir)) v = in_remaining (af_in_arr st) v
       \<and> in_iterated (af_in_arr (af_handle st a dir)) v = in_iterated (af_in_arr st) v"
proof(cases rule: af_handle_cases_exec[of a st dir])
  case (cancel up dn fl m')
  have "v \<notin> set (take m' (af_vstack st))"
    using af_finished_off_stack[of st v] assms(2-4)
    by (auto dest: in_set_takeD)
  then show ?thesis
    using assms(1,3) unfolding cancel(7) AF_invar_1_def AF_invar_V_def
    by (simp add: af_reset_unsee_seg_out_lookup af_reset_unsee_seg_in_lookup)
qed (simp_all)

lemma af_handle_finished_back:
  assumes "AF_invar_1 st" "AF_invar_2 st" "a \<in> \<E>" "AF_invar_V st"
    "st_lookup (af_state (af_handle st a dir)) v = Finished"
  shows "st_lookup (af_state st) v = Finished"
  by (rule af_handle_cases[of a st dir]; insert assms fst_E_V[of a] snd_E_V[of a];
      (auto simp: AF_invar_1_def AF_invar_V_def state_arr.fixed_univ_map_upd
        af_reset_unsee_seg_state split: if_splits))

lemma af_handle_exh:
  "\<lbrakk>AF_invar_1 st; AF_invar_2 st; a \<in> \<E>; AF_invar_V st; AF_invar_exh st\<rbrakk> \<Longrightarrow>
    AF_invar_exh (af_handle st a dir)"
  using af_handle_arr_off[where st=st and a=a and dir=dir] af_handle_finished_back[of st a dir]
  by (auto simp: AF_invar_exh_def)

lemma af_exh_upd1:
  assumes "AF_DFS_call_1_conds st" "AF_inv st" "AF_invar_exh st"
  shows "AF_invar_exh (AF_DFS_upd1 st)"
proof-
  have "AF_invar_iter st" "AF_invar_V st"
    using assms(2)
    by (auto simp: AF_inv_def)
  then obtain a where a: "AF_DFS_upd1 st = af_handle (st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack
    st))\<rparr>) a True"
    "a \<in> \<E>" "fst a = hd (af_vstack st)" "af_vstack st \<noteq> []" "hd (af_vstack st) \<in> \<V>"
    by (rule AF_DFS_upd1_scan[OF assms(1)])
  have i: "out_invar (af_out_arr st)" "out_remaining (af_out_arr st) (hd (af_vstack st)) \<noteq> {}"
    using assms(1,2) a(5) outg.idx_has
    by (auto elim!: call_cond_elims simp: AF_inv_def AF_invar_1_def)
  have "\<forall>v. st_lookup (af_state st) v = Finished \<longrightarrow> v \<noteq> hd (af_vstack st)"
    using af_finished_off_stack[of st "hd (af_vstack st)"] hd_in_set a(4) assms(2)
    by (auto simp: AF_inv_def)
  hence "AF_invar_exh (st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack st))\<rparr>)"
    using assms(3) outg.idx_move_remaining_other[of "af_out_arr st" "hd (af_vstack st)"] i(1) a(5) i(2)
    by (auto simp: AF_invar_exh_def)
  thus ?thesis
    using AF_inv_out_advance[of st] assms(2,1) a(1,2)
    by (auto simp: AF_inv_def intro: af_handle_exh)
qed

lemma af_exh_upd2:
  assumes "AF_DFS_call_2_conds st" "AF_inv st" "AF_invar_exh st"
  shows "AF_invar_exh (AF_DFS_upd2 st)"
proof-
  have "AF_invar_iter st" "AF_invar_V st"
    using assms(2)
    by (auto simp: AF_inv_def)
  then obtain a where a: "AF_DFS_upd2 st = af_handle (st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack
    st))\<rparr>) a False"
    "a \<in> \<E>" "snd a = hd (af_vstack st)" "af_vstack st \<noteq> []" "hd (af_vstack st) \<in> \<V>"
    by (rule AF_DFS_upd2_scan[OF assms(1)])
  have i: "in_invar (af_in_arr st)" "in_remaining (af_in_arr st) (hd (af_vstack st)) \<noteq> {}"
    using assms(1,2) a(5) ing.idx_has
    by (auto elim!: call_cond_elims simp: AF_inv_def AF_invar_1_def)
  have "\<forall>v. st_lookup (af_state st) v = Finished \<longrightarrow> v \<noteq> hd (af_vstack st)"
    using af_finished_off_stack[of st "hd (af_vstack st)"] hd_in_set a(4) assms(2)
    by (auto simp: AF_inv_def)
  hence "AF_invar_exh (st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack st))\<rparr>)"
    using assms(3) ing.idx_move_remaining_other[of "af_in_arr st" "hd (af_vstack st)"] i(1) a(5) i(2)
    by (auto simp: AF_invar_exh_def)
  thus ?thesis
    using AF_inv_in_advance[of st] assms(2,1) a(1,2)
    by (auto simp: AF_inv_def intro: af_handle_exh)
qed

lemma af_exh_upd3:
  assumes "AF_DFS_call_3_conds st" "AF_inv st" "AF_invar_exh st"
  shows "AF_invar_exh (AF_DFS_upd3 st)"
proof-
  obtain u us where vv: "af_vstack st = u # us"
    using assms(1)
    by (auto elim!: call_cond_elims)
  hence "st_invar (af_state st)" "u \<in> \<V>" "out_invar (af_out_arr st)" "in_invar (af_in_arr st)"
    using assms(2)
    by (auto simp: AF_inv_def AF_invar_1_def AF_invar_V_def)
  thus ?thesis
    using vv assms(1,3) outg.idx_has[of "af_out_arr st" u] ing.idx_has[of "af_in_arr st" u]
    by (auto elim!: call_cond_elims simp: AF_invar_exh_def AF_DFS_upd3_def state_arr.fixed_univ_map_upd)
qed

lemma AF_DFS_exh:
  "\<lbrakk>AF_DFS_dom st; multigraph_inv out_arr in_arr\<rbrakk> \<Longrightarrow> AF_inv st \<longrightarrow>
    AF_invar_exh st \<longrightarrow> AF_invar_exh (AF_DFS st)"
  by (intro impI AF_DFS_rel[where R = "\<lambda>x y. AF_invar_exh y \<longrightarrow> AF_invar_exh x", THEN mp])
     (auto intro: af_exh_upd1 af_exh_upd2 af_exh_upd3)

definition "AFF_exh st \<longleftrightarrow>
  (\<forall>v\<in>\<V>. st_lookup (aff_state st) v = Finished \<longrightarrow>
        out_remaining (aff_out_arr st) v = {} \<and> in_remaining (aff_in_arr st) v = {})"

lemma AFF_exh_holds_1: "AFF_exh st \<Longrightarrow> AFF_exh (AF_outer_upd1 st)"
  by (simp add: AFF_exh_def AF_outer_upd1_def)

lemma AFF_exh_holds_2:
  assumes "multigraph_inv out_arr in_arr" "AF_outer_call_2_conds st" "AFF_inv st" "AFF_exh st"
  shows "AFF_exh (AF_outer_upd2 st)"
proof-
  have "AF_invar_exh (af_launch st)"
    using assms(2-4) vit_current_V[of st] assms(3)
    by (auto simp: AF_outer_call_2_conds_def AFF_inv_def AFF_exh_def AF_invar_exh_def AF_DFS_initial_def
                   state_arr.fixed_univ_map_upd)
  hence "AF_invar_exh (AF_DFS (af_launch st))"
    using AF_DFS_exh[where st="af_launch st"] AF_outer_launch[of st] assms(1-3)
    by (blast)
  thus ?thesis
    by (simp add: AFF_exh_def AF_invar_exh_def AF_outer_upd2_def Let_def)
qed

lemma AF_outer_inv_exh:
  "\<lbrakk>AF_outer_dom st; multigraph_inv out_arr in_arr\<rbrakk>
   \<Longrightarrow> AFF_inv st \<and> AFF_exh st \<longrightarrow> AFF_inv (AF_outer st) \<and> AFF_exh (AF_outer st)"
  using AFF_inv_holds[of st]
  by (auto intro!: AF_outer_pred[where P = AFF_exh] intro: AFF_exh_holds_1 AFF_exh_holds_2)

lemma make_acyclic_all_edges_scanned:
  "\<lbrakk>multigraph_inv out_arr in_arr; flow_invar f0; af_cap_feasible f0; vit_invar all_vertices; vit_abstract
    all_vertices = \<V>; vit_iterated all_vertices = {}; make_acyclic f0 = Some f'\<rbrakk> \<Longrightarrow>
    \<forall>v \<in> \<V>. out_remaining (aff_out_arr (AF_outer (AF_outer_initial f0))) v = {}
              \<and> in_remaining (aff_in_arr (AF_outer (AF_outer_initial f0))) v = {}"
  using make_acyclic_Some[of f0 f'] AF_outer_inv_exh[of "AF_outer_initial f0"]
    make_acyclic_all_finished[of f0 f'] state_init_unseen
  by (auto simp: AFF_exh_def AF_outer_initial_def)

text \<open>Fourth building block: \emph{free-arc monotonicity} (MONO). Each cancellation pushes flow around a
      closed trail of \emph{free} arcs, moving every arc on the trail toward a capacity boundary and
      leaving arcs off the trail untouched; so no arc ever \emph{becomes} free --- the free set only
      shrinks. Consequently an arc that is free in the final flow was free throughout the run, in
      particular at the moment it was scanned. Lifting the single-step fact through @{const af_handle},
      @{const AF_DFS} and @{const AF_outer} gives that @{const af_arc_free} of the returned flow implies
      @{const af_arc_free} of the input --- and, applied at intermediate states, of every flow in
      between.\<close>

lemma af_handle_free_mono:
  assumes "AF_invar_1 st" "AF_invar_feas st" "AF_invar_free st" "a \<in> \<E>" "AF_invar_estE st"
    "af_arc_free (af_flow (af_handle st a dir)) b"
  shows "af_arc_free (af_flow st) b"
  using assms(4)
proof(cases rule: af_handle_cases[of a st dir])
  case selfloop
  thus ?thesis
    using assms(1,4,6) af_selfloop_handle_free_imp_flow_id[of a st] af_selfloop_handle_flow_off[of a st b]
    by (cases "b = a") (auto simp: AF_invar_1_def af_arc_free_def)
next
  case (cancel up dn fl m')
  have "af_arc_free (af_flow st) a"
    using af_guard_free cancel(2) cancel(3) assms(2,4)
    by (auto simp: AF_invar_feas_def af_cap_feasible_def)
  thus ?thesis
    using cancel(7) assms(1,3,5,6) af_cancel_seg_arc_free_off[OF _ assms(4) _ _ _ cancel(6), of b]
    by (cases "b \<in> set (af_estack st) \<or> b = a") (auto simp: AF_invar_1_def AF_invar_free_def AF_invar_estE_def)
qed (insert assms(6), (simp_all))

text \<open>A scanned self-loop's flow value is untouched by @{const af_handle} at any \emph{other} edge: it
      is never on the cancelled walk (@{thm [source] a_notin_estack_selfloop}), so every branch --- the
      self-loop normaliser (which touches only the current edge), the push/skip/flag branches (no flow
      change), and a real cancellation (off-walk arcs preserved, @{thm [source] af_cancel_seg_flow_off})
      --- leaves it fixed. This is the value-level analogue of @{thm [source] af_handle_free_mono}.\<close>

lemma af_handle_flow_selfloop_off:
  assumes "AF_invar_1 st" "AF_invar_2 st" "AF_invar_3 st" "AF_invar_estE st" "a \<in> \<E>" "fst e = snd e" "e
    \<noteq> a"
  shows "flow_lookup (af_flow (af_handle st a dir)) e = flow_lookup (af_flow st) e"
  using assms(5)
proof(cases rule: af_handle_cases[of a st dir])
  case selfloop
  thus ?thesis
    using assms(1) af_selfloop_handle_flow_off[OF assms(5) _ assms(7)]
    by (auto simp: AF_invar_1_def)
next
  case (cancel up dn fl m')
  thus ?thesis
    using assms(1,4) af_cancel_seg_flow_off[OF _ assms(5) _ a_notin_estack_selfloop[OF assms(2,3,6)] assms(7) cancel(6)]
    by (auto simp: AF_invar_1_def AF_invar_estE_def)
qed simp_all

lemma af_free_mono_upd1:
  assumes "AF_inv st" "AF_DFS_call_1_conds st" "af_arc_free (af_flow (AF_DFS_upd1 st)) b"
  shows "af_arc_free (af_flow st) b"
proof-
  have "AF_invar_iter st" "AF_invar_V st"
    using assms(1)
    by (auto simp: AF_inv_def)
  then obtain a where "AF_DFS_upd1 st = af_handle (st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack
    st))\<rparr>) a True"
    "a \<in> \<E>" "fst a = hd (af_vstack st)" "af_vstack st \<noteq> []" "hd (af_vstack st) \<in> \<V>"
    by (rule AF_DFS_upd1_scan[OF assms(2)])
  thus ?thesis
    using AF_inv_out_advance[of st] assms(1,2) assms(3)
          af_handle_free_mono[of "st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack st))\<rparr>" a True
            b]
    by (auto simp: AF_inv_def)
qed

lemma af_free_mono_upd2:
  assumes "AF_inv st" "AF_DFS_call_2_conds st" "af_arc_free (af_flow (AF_DFS_upd2 st)) b"
  shows "af_arc_free (af_flow st) b"
proof-
  have "AF_invar_iter st" "AF_invar_V st"
    using assms(1)
    by (auto simp: AF_inv_def)
  then obtain a where "AF_DFS_upd2 st = af_handle (st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack
    st))\<rparr>) a False"
    "a \<in> \<E>" "snd a = hd (af_vstack st)" "af_vstack st \<noteq> []" "hd (af_vstack st) \<in> \<V>"
    by (rule AF_DFS_upd2_scan[OF assms(2)])
  thus ?thesis
    using AF_inv_in_advance[of st] assms(1,2) assms(3)
          af_handle_free_mono[of "st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack st))\<rparr>" a False b]
    by (auto simp: AF_inv_def)
qed

subsection \<open>Theme F, part 3: the running forest invariant\<close>

text \<open>The load-bearing invariant of the acyclicity engine: the \emph{scanned} free arcs form a forest,
      i.e.\ carry no closed trail of distinct arcs. An arc is \emph{scanned} once one of its endpoints
      has advanced its iterator past it. The invariant is stated as the absence of a closed residual
      walk all of whose underlying arcs are simultaneously free and scanned. Two consequences are
      immediate and proved here: (i) at termination every free arc is scanned (edge exhaustion), so the
      invariant collapses to @{term \<open>nfc\<close>} --- the terminal bridge; (ii) it holds initially, when no
      edge has been scanned yet. What remains (Theme F, part 4) is preservation across @{const af_handle}
      --- in particular the truncate-and-reset branch --- lifted through @{const AF_DFS} and
      @{const AF_outer}.\<close>

definition "AFF_scanned st a \<longleftrightarrow>
  a \<in> out_iterated (aff_out_arr st) (fst a) \<or> a \<in> in_iterated (aff_in_arr st) (snd a)"

definition "AFF_forest st \<longleftrightarrow>
  \<not> (\<exists>C. prepath C \<and> (\<forall>e\<in>set C. af_arc_free (aff_flow st) (oedge e) \<and> AFF_scanned
    st (oedge e))
        \<and> distinct (map oedge C) \<and> fstv (hd C) = sndv (last C) \<and> set C \<subseteq> \<EE>)"

lemma AFF_scanned_of_exhausted:
  assumes "multigraph_inv (aff_out_arr st) (aff_in_arr st)" "out_remaining (aff_out_arr st) (fst a) = {}" "a \<in> \<E>"
  shows "AFF_scanned st a"
proof-
  have "out_invar (aff_out_arr st)" "out_abstract (aff_out_arr st) (fst a) = \<delta>\<^sup>+ (fst a)" "fst a \<in>
    \<V>"
    using assms(1) fst_E_V assms(3)
    by (auto simp: multigraph_inv_def out_graph_inv_def)
  thus ?thesis
    using outg.idx_partition_union[of "aff_out_arr st" "fst a"] assms(2,3)
    by (auto simp: AFF_scanned_def delta_plus_def)
qed

lemma make_acyclic_forest_nfc:
  assumes "multigraph_inv out_arr in_arr" "flow_invar f0" "af_cap_feasible f0" "vit_invar all_vertices"
    "vit_abstract all_vertices = \<V>" "vit_iterated all_vertices = {}" "make_acyclic f0 = Some f'"
    "AFF_forest (AF_outer (AF_outer_initial f0))"
  shows "\<nexists>C. prepath C \<and> (\<forall>e\<in>set C. af_arc_free f' (oedge e)) \<and> distinct (map oedge C)
             \<and> fstv (hd C) = sndv (last C) \<and> set C \<subseteq> \<EE>"
proof-
  note r = make_acyclic_Some[OF assms(1-4) equalityD1[OF assms(5)] assms(7)]
  have "multigraph_inv (aff_out_arr (AF_outer (AF_outer_initial f0))) (aff_in_arr (AF_outer (AF_outer_initial f0)))"
    using AFF_inv_holds[of "AF_outer_initial f0"] r(1) assms(1) r(2)
    by (simp add: AFF_inv_def)
  hence "\<forall>e\<in>\<EE>. AFF_scanned (AF_outer (AF_outer_initial f0)) (oedge e)"
    using AFF_scanned_of_exhausted make_acyclic_all_edges_scanned[of f0 f'] assms(1-7) fst_E_V o_edge_res
    by (blast)
  thus ?thesis
    using assms(8) unfolding r(3) AFF_forest_def
    by (blast)
qed

lemma make_acyclic_acyclic_from_forest:
  "\<lbrakk>multigraph_inv out_arr in_arr; flow_invar f0; af_cap_feasible f0; vit_invar all_vertices;
    vit_abstract all_vertices = \<V>; vit_iterated all_vertices = {}; make_acyclic f0 = Some f';
    AFF_forest (AF_outer (AF_outer_initial f0))\<rbrakk>
   \<Longrightarrow> acyclic_flow (h \<circ> flow_lookup f')"
  by (intro acyclic_flow_from_no_free_cycle make_acyclic_forest_nfc)

text \<open>Preservation, outer loop. The skip step changes neither the flow, the iterators, nor the seen
      set, so it trivially preserves the forest invariant. The launch step runs a whole inner DFS and
      is the substantial obligation --- it is where the \<open>DFS_Cycles_Aux\<close>-style
        \<open>invar_cycle_false\<close>
      argument (ported to the flow-mutating, truncate-and-reset procedure, with the invariant stated at
      quiescent configurations and a self-healing lemma for the back-edge transient) must be discharged.\<close>

text \<open>DFS-level forest invariant and the reduction of the launch step to it. \<open>AF_forest\<close> is the
      inner-DFS analogue of @{const AFF_forest}; the launch feeds the outer flow/iterators/seen set into
      a fresh inner state, so @{const AFF_forest} of the launched configuration equals \<open>AF_forest\<close>
      of the inner initial state, and @{const AFF_forest} after the launch equals \<open>AF_forest\<close> of
      the inner result. Hence \<open>AFF_forest_holds_2\<close> reduces exactly to \emph{@{const AF_DFS}
      preserves \<open>AF_forest\<close>} --- the ported \<open>invar_cycle_false\<close> obligation.\<close>

definition "af_scanned st a \<longleftrightarrow>
  a \<in> out_iterated (af_out_arr st) (fst a) \<or> a \<in> in_iterated (af_in_arr st) (snd a)"

definition "AF_forest st \<longleftrightarrow>
  \<not> (\<exists>C. prepath C \<and> (\<forall>e\<in>set C. af_arc_free (af_flow st) (oedge e) \<and> af_scanned st
    (oedge e))
        \<and> distinct (map oedge C) \<and> fstv (hd C) = sndv (last C) \<and> set C \<subseteq> \<EE>)"

text \<open>The @{term scan_sub} ingredient of the forest step: advancing an iterator adds only the
      current edge to the scanned set. An arc scanned after the advance, other than the current one, was
      already scanned before.\<close>

lemma af_out_advance_scan_sub:
  assumes "AF_invar_1 st" "AF_invar_iter st" "AF_invar_V st" "af_vstack st \<noteq> []"
    "out_has (af_out_arr st) (hd (af_vstack st))" "b \<noteq> out_current (af_out_arr st) (hd (af_vstack st))"
    "af_scanned (st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack st))\<rparr>) b"
  shows "af_scanned st b"
proof-
  have "hd (af_vstack st) \<in> \<V>"
    using assms(3,4)
    by (cases "af_vstack st") (auto simp: AF_invar_V_def)
  then show ?thesis
    using assms outg.idx_has[of "af_out_arr st" "hd (af_vstack st)"]
      outg.idx_move_iterated[of "af_out_arr st" "hd (af_vstack st)"]
      outg.idx_move_iterated_other[of "af_out_arr st" "hd (af_vstack st)"]
    by (cases "fst b = hd (af_vstack st)") (auto simp: AF_invar_1_def af_scanned_def)
qed

lemma af_in_advance_scan_sub:
  assumes "AF_invar_1 st" "AF_invar_iter st" "AF_invar_V st" "af_vstack st \<noteq> []"
    "in_has (af_in_arr st) (hd (af_vstack st))" "b \<noteq> in_current (af_in_arr st) (hd (af_vstack st))"
    "af_scanned (st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack st))\<rparr>) b"
  shows "af_scanned st b"
proof-
  have "hd (af_vstack st) \<in> \<V>"
    using assms(3,4)
    by (cases "af_vstack st") (auto simp: AF_invar_V_def)
  then show ?thesis
    using assms ing.idx_has[of "af_in_arr st" "hd (af_vstack st)"]
      ing.idx_move_iterated[of "af_in_arr st" "hd (af_vstack st)"]
      ing.idx_move_iterated_other[of "af_in_arr st" "hd (af_vstack st)"]
    by (cases "snd b = hd (af_vstack st)") (auto simp: AF_invar_1_def af_scanned_def)
qed

subsection \<open>Theme F, part 4: an instrumented DFS carrying a finish clock (proof only)\<close>

text \<open>A ghost \emph{finish clock}: \<open>AF_DFS_i\<close> runs exactly like the executable @{const AF_DFS}
      but additionally threads a pure rank function @{typ \<open>'v \<Rightarrow> nat\<close>} and a counter, stamping
        each
      vertex with the counter value at the moment it is popped (finished). The clock steers no branch,
      so it never enters the executable algorithm; it exists solely to express the finish order for the
      acyclicity argument (a finished vertex has at most one free arc to a later-finished vertex). Being
      monotone, a recorded rank is never disturbed by the truncate-and-reset --- which is precisely why
      it succeeds where the seen/tree structure fails. The base component of \<open>AF_DFS_i\<close> coincides
      with @{const AF_DFS}, so results about the rank transfer to the real run.\<close>

function (domintros) AF_DFS_i where
  "AF_DFS_i st rk c =
     (if af_unbounded st then (st, rk, c) else
      case af_vstack st of
        [] \<Rightarrow> (st, rk, c)
      | v # vs \<Rightarrow>
         if out_has (af_out_arr st) v then
           AF_DFS_i (af_handle (st \<lparr> af_out_arr := out_move (af_out_arr st) v \<rparr>)
                             (out_current (af_out_arr st) v) True) rk c
         else
           if in_has (af_in_arr st) v then
              AF_DFS_i (af_handle (st \<lparr> af_in_arr := in_move (af_in_arr st) v \<rparr>)
                                (in_current (af_in_arr st) v) False) rk c
           else
              AF_DFS_i (st \<lparr> af_vstack := vs,
                           af_state := st_upd (af_state st) v Finished,
                           af_estack := tl (af_estack st),
                           af_dstack := tl (af_dstack st) \<rparr>) (rk(v := c)) (Suc c))"
  by pat_completeness auto

lemma AF_DFS_i_dom_all:
  assumes "AF_DFS_dom st"
  shows "\<forall>rk c. AF_DFS_i_dom (st, rk, c)"
proof(induction rule: AF_DFS_induct[OF assms])
  case IH: (1 st)
  show ?case
  proof(cases "af_vstack st")
    case (Cons v vs)
    show ?thesis
      by (intro allI, rule AF_DFS_i.domintros)
         (insert IH(2-4), simp_all add: Cons AF_DFS_call_1_conds_def AF_DFS_call_2_conds_def
                            AF_DFS_call_3_conds_def AF_DFS_upd1_def AF_DFS_upd2_def AF_DFS_upd3_def)
  qed (intro allI, rule AF_DFS_i.domintros, simp_all)
qed

text \<open>The finish-order invariant J' (\<open>af_rankok\<close>): every finished vertex has at most one free
      arc to a strictly-later-finished (higher-rank) vertex --- its DFS-tree parent edge. A vertex
      counts as ``later'' if it is not yet finished (\<open>af_hgt\<close>), so the invariant makes sense at
      every step. Terminally (all finished) it says every finished vertex has $\leq 1$ free arc to a
      higher-rank vertex, which is the certificate that the free graph is a forest.

      A first ingredient: a cancellation only ever removes free arcs (MONO), so it preserves J' --- with
      fewer free arcs the uniqueness of the higher arc is only easier. The delicate step is establishing
      J' for a vertex \emph{at its pop}: exhaustion means it scanned every arc in the incarnation that
      pops, MONO makes those arcs free already at scan time, and a free back-edge to an ancestor would
      have truncated (dropped) the reader --- contradicting that this is the incarnation that pops. So
      every free-at-pop arc is a tree/parent edge, giving $\leq 1$ to a higher rank, with no self-healing.\<close>

definition "af_hgt st rk v a \<longleftrightarrow>
  (st_lookup (af_state st) (if fst a = v then snd a else fst a) \<noteq> Finished
   \<or> rk (if fst a = v then snd a else fst a) > rk v)"

definition "af_rankok st rk \<longleftrightarrow>
  (\<forall>v\<in>\<V>. st_lookup (af_state st) v = Finished \<longrightarrow>
     (\<forall>a1 a2. a1 \<in> \<E> \<longrightarrow> af_arc_free (af_flow st) a1 \<longrightarrow> v \<in> {fst a1,
       snd a1} \<longrightarrow> af_hgt st rk v a1 \<longrightarrow>
              a2 \<in> \<E> \<longrightarrow> af_arc_free (af_flow st) a2 \<longrightarrow> v \<in> {fst a2, snd a2}
                \<longrightarrow> af_hgt st rk v a2 \<longrightarrow>
              a1 = a2))"

text \<open>The pop case of J' (the crux). Assume every free arc incident to the popping vertex @{term v}
      whose far endpoint is not yet finished is @{term v}'s parent arc (@{term \<open>hd (af_estack st)\<close>}) ---
      the fact the running scan-resolution invariant will supply, following from exhaustion, MONO, and
      the truncation behaviour. Then stamping @{term v} with the current clock preserves @{const af_rankok}:
      for @{term v} itself all higher-rank free arcs coincide with the parent arc (so $\leq 1$), and for a
      previously-finished vertex the ``higher'' status of each of its arcs is unchanged (a neighbour that
      was on the stack, hence counted as later, becomes finished with strictly larger rank).\<close>

lemma af_rankok_pop:
  assumes "af_rankok st rk" "st_invar (af_state st)" "v \<in> \<V>" "st_lookup (af_state st) v \<noteq> Finished"
    "\<And>u. \<lbrakk>u \<in> \<V>; st_lookup (af_state st) u = Finished\<rbrakk> \<Longrightarrow> rk u < (c :: nat)"
    "\<And>a. \<lbrakk>a \<in> \<E>; af_arc_free (af_flow st) a; v \<in> {fst a, snd a};
          st_lookup (af_state st) (if fst a = v then snd a else fst a) \<noteq> Finished\<rbrakk>
         \<Longrightarrow> af_estack st \<noteq> [] \<and> a = hd (af_estack st)"
  shows "af_rankok (st\<lparr>af_vstack := vs, af_state := st_upd (af_state st) v Finished,
                       af_estack := tl (af_estack st), af_dstack := tl (af_dstack st)\<rparr>) (rk(v := c))"
proof(unfold af_rankok_def, intro ballI allI impI)
  let ?st' = "st\<lparr>af_vstack := vs, af_state := st_upd (af_state st) v Finished,
                 af_estack := tl (af_estack st), af_dstack := tl (af_dstack st)\<rparr>"
  fix u a1 a2
  assume u: "u \<in> \<V>" "st_lookup (af_state ?st') u = Finished"
    and a1: "a1 \<in> \<E>" "af_arc_free (af_flow ?st') a1" "u \<in> {fst a1, snd a1}" "af_hgt ?st' (rk(v := c)) u a1"
    and a2: "a2 \<in> \<E>" "af_arc_free (af_flow ?st') a2" "u \<in> {fst a2, snd a2}" "af_hgt ?st' (rk(v := c)) u a2"
  have lk: "st_lookup (af_state ?st') w = (if w = v then Finished else st_lookup (af_state st) w)" for w
    using assms(2,3)
    by (simp add: state_arr.fixed_univ_map_upd)
  show "a1 = a2"
  proof(cases "u = v")
    case True
    have h: "af_estack st \<noteq> [] \<and> a = hd (af_estack st)"
      if "a \<in> \<E>" "af_arc_free (af_flow ?st') a" "u \<in> {fst a, snd a}" "af_hgt ?st' (rk(v := c)) u a" for a
    proof(rule assms(6)[OF that(1)])
      have "(if fst a = v then snd a else fst a) \<in> \<V>"
        using fst_E_V[of a] that(1) snd_E_V[of a] that(1)
        by (auto)
      thus "st_lookup (af_state st) (if fst a = v then snd a else fst a) \<noteq> Finished"
        using that(4) True assms(2-4) assms(5)[of "if fst a = v then snd a else fst a"]
        by (cases "(if fst a = v then snd a else fst a) = v")
           (auto simp: af_hgt_def state_arr.fixed_univ_map_upd)
    qed (insert that True, (simp_all))
    show ?thesis
      using h[of a1] a1 h[of a2] a2
      by (simp)
  next
    case False
    hence "st_lookup (af_state st) u = Finished" "rk u < c"
      using u lk assms(5)
      by (auto)
    moreover have "af_hgt ?st' (rk(v := c)) u a = af_hgt st rk u a" for a
      using calculation False lk assms(4)
      by (auto simp: af_hgt_def)
    ultimately show ?thesis
      using assms(1) u(1) a1 a2
      by (auto simp: af_rankok_def)
  qed
qed

text \<open>The advance branches preserve J'. @{const af_handle} never finishes a vertex and, by MONO, a
      free arc of the result was already free before, so the uniqueness of the higher arc transfers.
      The advance itself only moves an iterator, so it leaves @{const af_rankok} unchanged.\<close>

lemma af_handle_finished_iff:
  "\<lbrakk>AF_inv st; a \<in> \<E>\<rbrakk>
   \<Longrightarrow> st_lookup (af_state (af_handle st a dir)) w = Finished \<longleftrightarrow> st_lookup (af_state
     st) w = Finished"
  using af_handle_finished_mono[of st a w dir] af_handle_finished_back[of st a dir w]
  by (auto simp: AF_inv_def)

lemma af_handle_af_rankok:
  assumes "AF_inv st" "a \<in> \<E>" "af_rankok st rk"
  shows "af_rankok (af_handle st a dir) rk"
proof-
  have "af_arc_free (af_flow (af_handle st a dir)) b \<Longrightarrow> af_arc_free (af_flow st) b" for b
    using assms(1,2) af_handle_free_mono[of st a dir b]
    by (auto simp: AF_inv_def)
  then show ?thesis
    using assms(3) unfolding af_rankok_def af_hgt_def af_handle_finished_iff[OF assms(1,2)]
    by blast
qed

lemma af_rankok_upd:
  assumes "AF_inv st" "af_rankok st rk"
  shows "AF_DFS_call_1_conds st \<Longrightarrow> af_rankok (AF_DFS_upd1 st) rk"
    "AF_DFS_call_2_conds st \<Longrightarrow> af_rankok (AF_DFS_upd2 st) rk"
  by (intro AF_DFS_upd_pred[where P = "\<lambda>s. af_rankok s rk"] assms af_handle_af_rankok;
      simp add: af_rankok_def af_hgt_def)+

text \<open>Fact 1 (truncate-to-bottleneck). The arc @{term \<open>es ! (m' - 1)\<close>} joining the truncation
      survivor to its dropped child --- which @{const af_push} returns as the deepest saturated arc ---
      is saturated (not free) in the post-cancellation flow, and by MONO it stays dead.\<close>

text \<open>Fact 1 lifted through a full segment cancellation: the extra @{const af_push_arc} on the
      closing arc @{term a} does not touch the boundary edge, which lies on the walk @{term es}.\<close>

definition "af_scanres st \<longleftrightarrow>
  (\<forall>v\<in>\<V>. \<forall>a. st_lookup (af_state st) v = OnStack \<longrightarrow> a \<in> \<E>
    \<longrightarrow> af_scanned st a \<longrightarrow>
         v \<in> {fst a, snd a} \<longrightarrow> af_arc_free (af_flow st) a \<longrightarrow>
         st_lookup (af_state st) (if fst a = v then snd a else fst a) \<noteq> Finished \<longrightarrow>
         a \<in> set (af_estack st))"

text \<open>The running scan-resolution invariant K (@{const af_scanres}) that will discharge the @{term res}
      hypothesis of @{thm [source] af_rankok_pop}: every scanned free arc incident to an \emph{on-stack}
      vertex, whose far endpoint is not finished, is a stack (trail) edge. Stated over on-stack vertices
      it has no reset transient --- the dangling edge left by a truncation runs from a finished vertex to
      an unseen one. With exhaustion at the pop, K forces such an arc of the top vertex to be its parent edge.\<close>

lemma af_estack_incident_hd:
  assumes "AF_invar_2 st" "AF_invar_3 st" "a \<in> set (af_estack st)" "af_vstack st \<noteq> []"
    "hd (af_vstack st) \<in> {fst a, snd a}"
  shows "a = hd (af_estack st)"
proof-
  obtain j where j: "j < length (af_estack st)" "a = af_estack st ! j"
    using assms(3)
    by (auto simp: in_set_conv_nth)
  have d: "distinct (af_vstack st)" "Suc (length (af_estack st)) = length (af_vstack st)"
    using assms(1,4)
    by (auto simp: AF_invar_2_def)
  have "{fst a, snd a} = {af_vstack st ! j, af_vstack st ! Suc j}"
    using assms(2) j
    by (auto simp: AF_invar_3_def split: if_splits)
  then have "af_vstack st ! 0 \<in> {af_vstack st ! j, af_vstack st ! Suc j}"
    using assms(5) hd_conv_nth[of "af_vstack st"] assms(4)
    by (simp)
  then have "j = 0"
    using assms(4) d j nth_eq_iff_index_eq[OF d(1), of 0 j] nth_eq_iff_index_eq[OF d(1), of 0 "Suc j"]
    by (simp)
  then show ?thesis
    using j
    by (cases "af_estack st") simp_all
qed

text \<open>The closing arc handled at the top vertex is off the trail: were it a stack arc it would be the
      parent (@{thm [source] af_estack_incident_hd}), which the back-edge branch excludes.\<close>

lemma af_closing_arc_not_on_trail:
  "\<lbrakk>AF_invar_2 st; AF_invar_3 st; af_vstack st \<noteq> []; hd (af_vstack st) \<in> {fst a, snd a}; af_estack
    st = [] \<or> a \<noteq> hd (af_estack st)\<rbrakk> \<Longrightarrow> a \<notin> set (af_estack st)"
  by (fastforce dest: af_estack_incident_hd)

text \<open>Fact 1 at the @{const af_handle} back-edge branch: the boundary trail arc
      @{term \<open>af_estack st ! (m' - 1)\<close>} is saturated in the cancelled flow, hence no longer free.\<close>

lemma af_backedge_boundary_dead:
  "\<lbrakk>flow_invar (af_flow st); AF_invar_2 st; AF_invar_3 st; AF_invar_estE st; a \<in> \<E>; af_vstack st
    \<noteq> []; hd (af_vstack st) \<in> {fst a, snd a}; af_estack st = [] \<or> a \<noteq> hd (af_estack st);
    af_cancel_seg up dn x (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) = (fl, m', ubd); 0 <
    m'\<rbrakk> \<Longrightarrow> \<not> af_arc_free fl (af_estack st ! (m' - 1))"
  using af_cancel_seg_bottleneck_sat[of "af_flow st" "af_estack st" a up dn x
      "af_vstack st" "af_dstack st" dir fl m' ubd]
    estack_distinct[of st] af_closing_arc_not_on_trail[of st a]
  by (auto simp: AF_invar_estE_def af_saturated_def af_arc_free_def Let_def)

text \<open>Exhaustion of a vertex's iterators means every incident edge has been scanned.\<close>

lemma af_scanned_of_exhausted:
  "\<lbrakk>multigraph_inv (af_out_arr st) (af_in_arr st); a \<in> \<E>; v \<in> {fst a, snd a}; \<not> out_has
    (af_out_arr st) v; \<not> in_has (af_in_arr st) v\<rbrakk> \<Longrightarrow> af_scanned st a"
  using fst_E_V[of a] snd_E_V[of a]
    outg.idx_partition_union[of "af_out_arr st" "fst a"] outg.idx_has[of "af_out_arr st" "fst a"]
    ing.idx_partition_union[of "af_in_arr st" "snd a"] ing.idx_has[of "af_in_arr st" "snd a"]
  by (auto simp: multigraph_inv_def out_graph_inv_def in_graph_inv_def
      af_scanned_def delta_plus_def delta_minus_def)

text \<open>At the pop the @{term res} hypothesis of @{thm [source] af_rankok_pop} follows: the top's arcs are
      all scanned, so a free one with a not-finished far end lies on the trail by @{const af_scanres}
      and is pinned to @{term \<open>hd (af_estack st)\<close>} by @{thm [source] af_estack_incident_hd}.\<close>

lemma af_scanres_res:
  assumes "af_scanres st" "AF_DFS_call_3_conds st" "multigraph_inv (af_out_arr st) (af_in_arr st)"
    "AF_invar_2 st" "AF_invar_3 st" "a \<in> \<E>" "af_arc_free (af_flow st) a" "hd (af_vstack st) \<in> {fst a, snd a}"
    "st_lookup (af_state st) (if fst a = hd (af_vstack st) then snd a else fst a) \<noteq> Finished"
  shows "af_estack st \<noteq> [] \<and> a = hd (af_estack st)"
proof-
  have ne: "af_vstack st \<noteq> []" "\<not> out_has (af_out_arr st) (hd (af_vstack st))"
    "\<not> in_has (af_in_arr st) (hd (af_vstack st))"
    using assms(2)
    by (auto elim!: call_cond_elims)
  have "hd (af_vstack st) \<in> \<V>"
    using assms(6,8) fst_E_V[of a] snd_E_V[of a]
    by auto
  then have "st_lookup (af_state st) (hd (af_vstack st)) = OnStack"
    using assms(4) ne(1)
    by (auto simp: AF_invar_2_def)
  moreover have "af_scanned st a"
    using assms ne af_scanned_of_exhausted[of st a "hd (af_vstack st)"]
    by auto
  ultimately have "a \<in> set (af_estack st)"
    using assms(1)[unfolded af_scanres_def, rule_format, of "hd (af_vstack st)" a]
      assms(6-9) fst_E_V[of a] snd_E_V[of a]
    by auto
  then show ?thesis
    using assms ne af_estack_incident_hd[of st a]
    by auto
qed

text \<open>Hence the pop preserves J', stamping the finished vertex with the current clock.\<close>

lemma af_rankok_upd3:
  assumes "AF_inv st" "AF_DFS_call_3_conds st" "af_rankok st rk" "af_scanres st"
    "\<And>u. \<lbrakk>u \<in> \<V>; st_lookup (af_state st) u = Finished\<rbrakk> \<Longrightarrow> rk u < (c :: nat)"
  shows "af_rankok (AF_DFS_upd3 st) (rk(hd (af_vstack st) := c))"
proof-
  have i: "st_invar (af_state st)" "AF_invar_2 st" "AF_invar_3 st"
    "multigraph_inv (af_out_arr st) (af_in_arr st)" "AF_invar_V st"
    using assms(1)
    by (auto simp: AF_inv_def AF_invar_1_def AF_invar_iter_def)
  then have "hd (af_vstack st) \<in> \<V>" "st_lookup (af_state st) (hd (af_vstack st)) = OnStack"
    using assms(2) hd_in_set
    by (auto elim!: call_cond_elims simp: AF_invar_2_def AF_invar_V_def)
  then show ?thesis
    unfolding AF_DFS_upd3_def
    using af_rankok_pop[OF assms(3) i(1) _ _ assms(5) af_scanres_res[OF assms(4,2) i(4,2,3)]]
    by simp
qed

text \<open>Preservation of K (@{const af_scanres}) by the pop: the popped vertex's parent edge leaves the
      trail, but a surviving scanned free arc of another on-stack vertex with a not-finished far end
      cannot be that edge (its far end would be the just-finished vertex).\<close>

lemma af_hd_estack_incident_hd_vstack:
  assumes "AF_invar_2 st" "AF_invar_3 st" "af_estack st \<noteq> []"
  shows "hd (af_vstack st) \<in> {fst (hd (af_estack st)), snd (hd (af_estack st))}"
  using assms(2)[unfolded AF_invar_3_def, rule_format, of 0] assms(1,3)
  by (cases "af_vstack st") (auto simp: AF_invar_2_def hd_conv_nth split: if_splits)

lemma af_scanres_upd3:
  assumes "AF_inv st" "AF_DFS_call_3_conds st" "af_scanres st"
  shows "af_scanres (AF_DFS_upd3 st)"
proof(unfold af_scanres_def, intro ballI allI impI)
  fix v a
  have i: "AF_invar_2 st" "AF_invar_3 st" "st_invar (af_state st)" "hd (af_vstack st) \<in> \<V>"
    using assms(1,2) hd_in_set
    by (auto elim!: call_cond_elims simp: AF_inv_def AF_invar_1_def AF_invar_V_def)
  assume "v \<in> \<V>" "st_lookup (af_state (AF_DFS_upd3 st)) v = OnStack" "a \<in> \<E>" "af_scanned (AF_DFS_upd3
    st) a"
    "v \<in> {fst a, snd a}" "af_arc_free (af_flow (AF_DFS_upd3 st)) a"
    "st_lookup (af_state (AF_DFS_upd3 st)) (if fst a = v then snd a else fst a) \<noteq> Finished"
  then have "v \<in> {fst a, snd a}" "a \<in> set (af_estack st)" "v \<noteq> hd (af_vstack st)"
    "(if fst a = v then snd a else fst a) \<noteq> hd (af_vstack st)"
    using assms(3) i(3,4)
    by (auto simp: af_scanres_def AF_DFS_upd3_def af_scanned_def state_arr.fixed_univ_map_upd split: if_splits)
  moreover have "a = hd (af_estack st) \<Longrightarrow> hd (af_vstack st) \<in> {fst a, snd a}"
    using af_hd_estack_incident_hd_vstack[of st] i(1,2) calculation(2)
    by (cases "af_estack st") auto
  ultimately show "a \<in> set (af_estack (AF_DFS_upd3 st))"
    by (cases "af_estack st") (auto simp: AF_DFS_upd3_def split: if_splits)
qed

subsection \<open>Pristine (unseen) vertices carry no scanned arc\<close>

text \<open>A vertex only leaves the @{term Unseen} state by being pushed, and only re-enters it through a
      reset that simultaneously restores its pristine iterators (@{const af_reset}); the running top,
      whose iterator advances, is always @{term OnStack}. Hence every @{term Unseen} vertex has an
      empty iterated set, so a scanned arc always has at least one endpoint that is not unseen.\<close>

definition "af_pristine1 st \<longleftrightarrow>
  (\<forall>v\<in>\<V>. st_lookup (af_state st) v = Unseen \<longrightarrow>
       out_iterated (af_out_arr st) v = {} \<and>
       in_iterated (af_in_arr st) v = {})"

text \<open>The full pristine invariant adds: no \emph{free scanned} arc is a self-loop, and a scanned
      self-loop sits at its cost-preferred bound. A self-loop is saturated the instant it is scanned,
      and freeness is anti-monotone, so old ones stay dead. This lets the forest argument exclude a
      self-loop cycle edge at the minimum-rank vertex.\<close>

definition "af_pristine st \<longleftrightarrow>
  af_pristine1 st \<and>
  (\<forall>a. af_scanned st a \<longrightarrow> af_arc_free (af_flow st) a \<longrightarrow> fst a \<noteq> snd a)
    \<and>
  (\<forall>a. af_scanned st a \<longrightarrow> fst a = snd a \<longrightarrow>
       (0 \<le> \<c> a \<longrightarrow> flow_lookup (af_flow st) a = 0)
     \<and> (\<c> a < 0 \<longrightarrow> flow_lookup (af_flow st) a = cap a))"

lemma af_pristine_imp1: "af_pristine st \<Longrightarrow> af_pristine1 st"
  by (simp add: af_pristine_def)

lemma af_pristine1_scanned_seen:
  "\<lbrakk>af_pristine1 st; af_scanned st a; a \<in> \<E>\<rbrakk>
   \<Longrightarrow> st_lookup (af_state st) (fst a) \<noteq> Unseen \<or> st_lookup (af_state st) (snd a) \<noteq>
     Unseen"
  by (auto simp: af_scanned_def af_pristine1_def dest: fst_E_V snd_E_V)

text \<open>A truncation reset restores the two edge iterators of each \emph{dropped} vertex to their
      pristine state, so its iterated set becomes empty.\<close>

lemma af_reset_unsee_seg_out_pristine:
  "\<lbrakk>out_invar (af_out_arr st); distinct vs; w \<in> set (take n vs); set vs \<subseteq> \<V>\<rbrakk>
   \<Longrightarrow> out_iterated (af_out_arr (af_reset_unsee_seg n vs st)) w = {}"
proof(induction n vs st rule: af_reset_unsee_seg.induct)
  case (1 n v vs st)
  have i: "out_invar (af_out_arr (af_reset v (st\<lparr>af_state := st_upd (af_state st) v Unseen\<rparr>)))"
    using 1(2,5)
    by (simp add: af_reset_def out_reset_invar)
  then show ?case
    using 1(1)[OF i] 1(3-5) af_reset_unsee_seg_out_lookup[OF i, of v n vs]
    by (cases "w = v") (auto simp: af_reset_def outg.idx_reset_iterated[OF 1(2)] dest: in_set_takeD)
qed simp_all

lemma af_reset_unsee_seg_in_pristine:
  "\<lbrakk>in_invar (af_in_arr st); distinct vs; w \<in> set (take n vs); set vs \<subseteq> \<V>\<rbrakk>
   \<Longrightarrow> in_iterated (af_in_arr (af_reset_unsee_seg n vs st)) w = {}"
proof(induction n vs st rule: af_reset_unsee_seg.induct)
  case (1 n v vs st)
  have i: "in_invar (af_in_arr (af_reset v (st\<lparr>af_state := st_upd (af_state st) v Unseen\<rparr>)))"
    using 1(2,5)
    by (simp add: af_reset_def in_reset_invar)
  then show ?case
    using 1(1)[OF i] 1(3-5) af_reset_unsee_seg_in_lookup[OF i, of v n vs]
    by (cases "w = v") (auto simp: af_reset_def ing.idx_reset_iterated[OF 1(2)] dest: in_set_takeD)
qed simp_all

text \<open>The pop leaves the iterators untouched and only finishes a vertex.\<close>

lemma af_pristine1_upd3:
  "\<lbrakk>AF_inv st; AF_DFS_call_3_conds st; af_pristine1 st\<rbrakk> \<Longrightarrow> af_pristine1 (AF_DFS_upd3 st)"
  using hd_in_set
  by (auto elim!: call_cond_elims split: if_splits
           simp: AF_inv_def AF_invar_1_def AF_invar_V_def af_pristine1_def AF_DFS_upd3_def
                 state_arr.fixed_univ_map_upd)

text \<open>@{const af_handle} preserves @{const af_pristine1}: every branch either leaves the iterators
      intact, or --- on a back-edge cancellation --- resets the dropped vertices exactly as they are
      re-marked @{term Unseen}.\<close>

lemma af_handle_pristine1:
  assumes "AF_invar_1 st" "AF_invar_2 st" "a \<in> \<E>" "AF_invar_V st" "af_pristine1 st"
  shows "af_pristine1 (af_handle st a dir)"
proof-
  have i: "out_invar (af_out_arr st)" "in_invar (af_in_arr st)" "st_invar (af_state st)"
    "distinct (af_vstack st)" "set (af_vstack st) \<subseteq> \<V>"
    using assms(1,2,4)
    by (auto simp: AF_invar_1_def AF_invar_2_def AF_invar_V_def)
  from assms(3) show ?thesis
  proof(cases rule: af_handle_cases[of a st dir])
    case (push up dn)
    then show ?thesis
      using assms(5) i(3) fst_E_V assms(3) snd_E_V assms(3)
      by (cases dir) (auto simp: af_pristine1_def state_arr.fixed_univ_map_upd split: if_splits)
  next
    case (cancel up dn fl m')
    show ?thesis
      using assms(5) i unfolding af_pristine1_def cancel(7)
      by (auto simp: af_reset_unsee_seg_state af_reset_unsee_seg_out_pristine af_reset_unsee_seg_in_pristine
                     af_reset_unsee_seg_out_lookup af_reset_unsee_seg_in_lookup split: if_splits)
  qed (insert assms(5), (simp_all add: af_pristine1_def))
qed

text \<open>Hence the two advancing update branches preserve @{const af_pristine1}: an advance touches only
      the on-stack top's iterator.\<close>

lemma af_pristine1_out_advance:
  "\<lbrakk>AF_inv st; AF_DFS_call_1_conds st; af_pristine1 st\<rbrakk> \<Longrightarrow> af_pristine1
    (st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack st))\<rparr>)"
  using hd_in_set
    outg.idx_has[of "af_out_arr st" "hd (af_vstack st)"]
    outg.idx_move_iterated_other[of "af_out_arr st" "hd (af_vstack st)"]
  by (auto elim!: call_cond_elims
        simp: af_pristine1_def AF_inv_def AF_invar_1_def AF_invar_2_def AF_invar_V_def)

lemma af_pristine1_in_advance:
  "\<lbrakk>AF_inv st; AF_DFS_call_2_conds st; af_pristine1 st\<rbrakk> \<Longrightarrow> af_pristine1
    (st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack st))\<rparr>)"
  using hd_in_set
    ing.idx_has[of "af_in_arr st" "hd (af_vstack st)"]
    ing.idx_move_iterated_other[of "af_in_arr st" "hd (af_vstack st)"]
  by (auto elim!: call_cond_elims
        simp: af_pristine1_def AF_inv_def AF_invar_1_def AF_invar_2_def AF_invar_V_def)

lemma af_pristine1_upd:
  assumes "AF_inv st" "af_pristine1 st"
  shows "AF_DFS_call_1_conds st \<Longrightarrow> af_pristine1 (AF_DFS_upd1 st)"
    "AF_DFS_call_2_conds st \<Longrightarrow> af_pristine1 (AF_DFS_upd2 st)"
proof-
  have i: "AF_invar_iter st" "AF_invar_V st"
    using assms(1)
    by (auto simp: AF_inv_def)
  show "af_pristine1 (AF_DFS_upd1 st)" if "AF_DFS_call_1_conds st"
    by (rule AF_DFS_upd1_scan[where st=st])
       (insert assms that i AF_inv_out_advance[of st] af_pristine1_out_advance[of st], auto simp: AF_inv_def
         af_handle_pristine1)
  show "af_pristine1 (AF_DFS_upd2 st)" if "AF_DFS_call_2_conds st"
    by (rule AF_DFS_upd2_scan[where st=st])
       (insert assms that i AF_inv_in_advance[of st] af_pristine1_in_advance[of st], auto simp: AF_inv_def
         af_handle_pristine1)
qed

subsection \<open>A length-one (self-loop) cancellation saturates its arc\<close>

text \<open>A self-loop is cancelled on sight with an empty segment: @{const af_scan} and @{const af_push}
      hit their base equations, leaving a single @{const af_push_arc} that drives the arc's flow to
      @{term 0} or to its capacity --- either way the arc is no longer free.\<close>

lemma af_cancel_seg_selfloop_notfree:
  assumes "flow_invar fl" "a \<in> \<E>" "af_rooms fl a = (up, dn)"
    "af_cancel_seg up dn (fst a) [] [] [] a True fl = (fl', m', ubd)" "\<not> ubd"
  shows "\<not> af_arc_free fl' a"
proof-
  obtain \<gamma> d f where p: "af_push_arc \<gamma> a d fl = (fl', f)"
    and "\<gamma> = (if 0 < af_delta_cost a True then dn else up) \<and> \<gamma> \<noteq> - 1 \<and> d = (\<not> 0 <
      af_delta_cost a True)
     \<or> \<gamma> = dn \<and> d = False"
    using assms(4,5)
    by (auto simp: af_cancel_seg_def Let_def split: prod.splits if_splits)
  moreover have "flow_lookup fl a = dn" "up = (if cap a = - 1 then - 1 else cap a - dn)"
    using assms(3)
    by (auto simp: af_rooms_def Let_def)
  ultimately show ?thesis
    using af_saturated_notfree[of a fl "\<gamma>" d fl' f] assms(2,1) p af_push_arc_at[of a fl "\<gamma>" d fl' f]
      assms(2,1) p
    by (auto simp: af_saturated_def split: if_splits)
qed

text \<open>A truncation reset and hence @{const af_handle} only ever \emph{remove} scanned arcs: a dropped
      vertex's iterators become pristine, every other branch leaves both edge arrays untouched.\<close>

lemma af_reset_unsee_seg_scanned_sub:
  assumes "out_invar (af_out_arr st)" "in_invar (af_in_arr st)" "distinct vs" "set vs \<subseteq> \<V>"
    "af_scanned (af_reset_unsee_seg n vs st) b"
  shows "af_scanned st b"
  using assms(5)
  by (cases "fst b \<in> set (take n vs)"; cases "snd b \<in> set (take n vs)")
     (insert assms(1-4), auto simp: af_scanned_def af_reset_unsee_seg_out_pristine af_reset_unsee_seg_in_pristine
                                    af_reset_unsee_seg_out_lookup af_reset_unsee_seg_in_lookup)

lemma af_handle_scanned_sub:
  assumes "AF_invar_1 st" "AF_invar_2 st" "AF_invar_V st" "af_scanned (af_handle st a dir) b"
  shows "af_scanned st b"
proof(cases rule: af_handle_cases_exec[of a st dir])
  case (cancel up dn fl m')
  then show ?thesis
    using assms af_reset_unsee_seg_scanned_sub[of "st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st),
            af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>" "af_vstack st" m' b]
    by (auto simp: AF_invar_1_def AF_invar_2_def AF_invar_V_def af_scanned_def)
qed (insert assms(4), auto simp: af_scanned_def)

text \<open>The scan-resolution invariant @{const af_scanres} is preserved by @{const af_handle} on the
      advanced state. The last two hypotheses model the state after the current arc @{term a} has been
      scanned: @{const af_scanres} for every arc other than @{term a}, and the pre-scan resolution of
      @{term a} itself (on a back-edge truncation the just-scanned arc is un-scanned by the reset of its
      dropped near endpoint).\<close>

lemma af_handle_af_scanres:
  assumes "AF_inv st" "af_pristine1 st" "a \<in> \<E>" "hd (af_vstack st) = (if dir then fst a else snd a)"
    "af_vstack st \<noteq> []" "\<not> af_unbounded (af_handle st a dir)"
    "\<And>u c. \<lbrakk>u \<in> \<V>; st_lookup (af_state st) u = OnStack; c \<in> \<E>; c \<noteq> a; af_scanned st c;
            u \<in> {fst c, snd c}; af_arc_free (af_flow st) c;
            st_lookup (af_state st) (if fst c = u then snd c else fst c) \<noteq> Finished\<rbrakk>
           \<Longrightarrow> c \<in> set (af_estack st)"
    "\<lbrakk>st_lookup (af_state st) (if dir then snd a else fst a) = OnStack; af_arc_free (af_flow st) a;
      a \<notin> set (af_estack st)\<rbrakk>
     \<Longrightarrow> if dir then a \<notin> in_iterated (af_in_arr st) (snd a) else a \<notin> out_iterated
       (af_out_arr st) (fst a)"
  shows "af_scanres (af_handle st a dir)"
proof(unfold af_scanres_def, intro ballI allI impI)
  fix v b
  assume v: "v \<in> \<V>" "st_lookup (af_state (af_handle st a dir)) v = OnStack"
    and b: "b \<in> \<E>" "af_scanned (af_handle st a dir) b" "v \<in> {fst b, snd b}"
      "af_arc_free (af_flow (af_handle st a dir)) b"
      "st_lookup (af_state (af_handle st a dir)) (if fst b = v then snd b else fst b) \<noteq> Finished"
  have i: "AF_invar_1 st" "AF_invar_2 st" "AF_invar_3 st" "AF_invar_feas st" "AF_invar_free st"
    "AF_invar_estE st" "AF_invar_V st"
    using assms(1)
    by (auto simp: AF_inv_def)
  have j: "flow_invar (af_flow st)" "st_invar (af_state st)" "out_invar (af_out_arr st)"
    "in_invar (af_in_arr st)" "distinct (af_vstack st)" "set (af_vstack st) \<subseteq> \<V>"
    "cap a = - 1 \<or> flow_lookup (af_flow st) a \<le> cap a"
    using i assms(3)
    by (auto simp: AF_invar_1_def AF_invar_2_def AF_invar_V_def AF_invar_feas_def af_cap_feasible_def)
  have s: "af_scanned st b" "af_arc_free (af_flow st) b"
    "st_lookup (af_state st) (if fst b = v then snd b else fst b) \<noteq> Finished"
    using af_handle_scanned_sub i(1,2,7) b(2) af_handle_free_mono i(1,4,5) assms(3) i(6) b(4) b(5)
          af_handle_finished_iff[OF assms(1,3), of dir "if fst b = v then snd b else fst b"]
    by (auto)
  have r: "\<lbrakk>b \<noteq> a; st_lookup (af_state st) v = OnStack\<rbrakk> \<Longrightarrow> b \<in> set
    (af_estack st)"
    using assms(7)[OF v(1) _ b(1) _ s(1) b(3) s(2,3)]
    by (blast)
  have inc: "hd (af_vstack st) \<in> {fst a, snd a}"
    using assms(4)
    by (auto)
  from assms(3) show "b \<in> set (af_estack (af_handle st a dir))"
  proof(cases rule: af_handle_cases[of a st dir])
    case selfloop
    then show ?thesis
      using r v(2) b(4) assms(6) af_selfloop_handle_notfree assms(3) j(1)
      by (cases "b = a") auto
  next
    case (blocked up dn)
    then show ?thesis
      using r v(2) b(4) af_guard_free blocked(2) j(7)
      by (cases "b = a") auto
  next
    case (parent up dn)
    then show ?thesis
      using r v(2)
      by (cases "b = a") auto
  next
    case (finished up dn)
    then show ?thesis
      using r v(2) b(3,5)
      by (cases "b = a"; cases dir) (auto split: if_splits)
  next
    case (push up dn)
    show ?thesis
    proof(cases "b \<noteq> a \<and> v = (if dir then snd a else fst a)")
      case True
      let ?w = "if fst b = v then snd b else fst b"
      have "st_lookup (af_state st) ?w = OnStack"
        using af_pristine1_scanned_seen assms(2) s(1) b(1) s(3) b(3) True push(5)
        by (cases "st_lookup (af_state st) ?w") (auto split: if_splits)
      then show ?thesis
        using assms(7)[of ?w b] True push(5,6) b(1,3) s(1,2) fst_E_V b(1) snd_E_V b(1)
        by (auto split: if_splits)
    next
      case False
      then show ?thesis
        using r v(2) push(6) j(2) fst_E_V assms(3) snd_E_V assms(3)
        by (cases dir) (auto simp: state_arr.fixed_univ_map_upd split: if_splits)
    qed
  next
    case (unbounded up dn fl m')
    then show ?thesis
      using assms(6)
      by (simp)
  next
    case (cancel up dn fl m')
    have vd: "v \<notin> set (take m' (af_vstack st))" "st_lookup (af_state st) v = OnStack"
      using v(2) j(2,6)
      by (auto simp: cancel(7) af_reset_unsee_seg_state split: if_splits)
    have np: "af_estack st = [] \<or> a \<noteq> hd (af_estack st)"
      using cancel(4)
      by (auto)
    have ane: "a \<notin> set (af_estack st)"
      using af_closing_arc_not_on_trail[OF i(2,3) assms(5) inc np] .
    have len: "m' \<le> length (af_estack st)" "Suc (length (af_estack st)) = length (af_vstack st)"
      using af_cancel_seg_drop_bound cancel(6) i(2) assms(5)
      by (auto simp: AF_invar_2_def)
    show ?thesis
    proof(cases "b = a")
      case False
      have "b \<notin> set (take m' (af_estack st))"
      proof
        assume "b \<in> set (take m' (af_estack st))"
        then obtain k where k: "k < m'" "k < length (af_estack st)" "b = af_estack st ! k"
          by (auto simp: in_set_conv_nth)
        then have "{fst b, snd b} = {af_vstack st ! k, af_vstack st ! Suc k}"
          "af_vstack st ! k \<in> set (take m' (af_vstack st))"
          using trail_endpoints[of st k] i(3) k(2) len nth_mem[of k "take m' (af_vstack st)"]
          by (auto)
        then have "Suc k = m'"
          using vd(1) b(3) k(1) len nth_mem[of "Suc k" "take m' (af_vstack st)"]
          by (cases "Suc k < m'") auto
        then show False
          using af_backedge_boundary_dead[of st a up dn "if dir then snd a else fst a" dir fl m' False] j(1) i(2,3,6)
            assms(3,5) inc np cancel(6) b(4) k(3) cancel(7)
          by (auto)
      qed
      then show ?thesis
        using r False vd(2) set_append[of "take m' (af_estack st)" "drop m' (af_estack st)"] cancel(7)
        by (auto)
    next
      case current: True
      have afree: "af_arc_free (af_flow st) a"
        using af_guard_free[where fl="af_flow st" and a=a and up=up and dn=dn] cancel(2) j(7) cancel(3)
        by (simp)
      show ?thesis
      proof(cases "m' = 0")
        case True
        then show ?thesis
          using af_cancel_seg_closing_sat_gen[OF j(1) estack_distinct[OF i(2,3)] i(6)[unfolded AF_invar_estE_def]
                  assms(3) ane cancel(2) cancel(6)[unfolded True]] b(4) cancel(7) current
          by (simp)
      next
        case False
        then have "hd (af_vstack st) \<in> set (take m' (af_vstack st))"
          using assms(5)
          by (cases "af_vstack st"; cases m') auto
        then show ?thesis
          using b(2,3) vd(1) current assms(4) cancel(7) assms(8) cancel(5) afree ane j(3-6)
          by (cases dir) (auto simp: af_scanned_def af_reset_unsee_seg_out_pristine af_reset_unsee_seg_in_pristine
                                    af_reset_unsee_seg_out_lookup af_reset_unsee_seg_in_lookup)
      qed
    qed
  qed
qed

text \<open>The two advancing update branches preserve @{const af_scanres}: the advance scans the current
      arc and leaves every other scan intact (@{thm [source] af_out_advance_scan_sub}), so the side
      conditions of @{thm [source] af_handle_af_scanres} follow from the pre-step @{const af_scanres}.\<close>

lemma af_scanres_upd1:
  assumes "AF_inv st" "AF_DFS_call_1_conds st" "af_pristine1 st" "af_scanres st"
    "\<not> af_unbounded (AF_DFS_upd1 st)"
  shows "af_scanres (AF_DFS_upd1 st)"
proof-
  let ?a = "out_current (af_out_arr st) (hd (af_vstack st))"
  have i: "AF_invar_1 st" "AF_invar_iter st" "AF_invar_V st" "af_vstack st \<noteq> []"
    "out_has (af_out_arr st) (hd (af_vstack st))" "st_lookup (af_state st) (hd (af_vstack st)) = OnStack"
    "hd (af_vstack st) \<in> \<V>"
    using assms(1,2) hd_in_set
    by (auto elim!: call_cond_elims simp: AF_inv_def AF_invar_2_def AF_invar_V_def)
  have a: "fst ?a = hd (af_vstack st)" "?a \<in> \<E>"
    using af_current_out_endpoint[OF _ i(7,5)] i(2)
    by (auto simp: AF_invar_iter_def)
  have "?a \<notin> in_iterated (af_in_arr st) (snd ?a)"
    if "af_arc_free (af_flow st) ?a" "?a \<notin> set (af_estack st)" "st_lookup (af_state st) (snd ?a) = OnStack"
    using assms(4) that i(6) a snd_E_V a(2)
    by (auto simp: af_scanres_def af_scanned_def)
  then have "af_scanres (af_handle (st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack st))\<rparr>) ?a
    True)"
    by (intro af_handle_af_scanres[OF AF_inv_out_advance[OF assms(1,2)] af_pristine1_out_advance[OF assms(1-3)] a(2)])
       (insert assms(4,5) i(4) a af_out_advance_scan_sub[OF i(1-5)], (auto simp: af_scanres_def AF_DFS_upd1_def
         Let_def))
  then show ?thesis
    by (simp add: AF_DFS_upd1_def Let_def)
qed

lemma af_scanres_upd2:
  assumes "AF_inv st" "AF_DFS_call_2_conds st" "af_pristine1 st" "af_scanres st"
    "\<not> af_unbounded (AF_DFS_upd2 st)"
  shows "af_scanres (AF_DFS_upd2 st)"
proof-
  let ?a = "in_current (af_in_arr st) (hd (af_vstack st))"
  have i: "AF_invar_1 st" "AF_invar_iter st" "AF_invar_V st" "af_vstack st \<noteq> []"
    "in_has (af_in_arr st) (hd (af_vstack st))" "st_lookup (af_state st) (hd (af_vstack st)) = OnStack"
    "hd (af_vstack st) \<in> \<V>"
    using assms(1,2) hd_in_set
    by (auto elim!: call_cond_elims simp: AF_inv_def AF_invar_2_def AF_invar_V_def)
  have a: "snd ?a = hd (af_vstack st)" "?a \<in> \<E>"
    using af_current_in_endpoint[OF _ i(7,5)] i(2)
    by (auto simp: AF_invar_iter_def)
  have "?a \<notin> out_iterated (af_out_arr st) (fst ?a)"
    if "af_arc_free (af_flow st) ?a" "?a \<notin> set (af_estack st)" "st_lookup (af_state st) (fst ?a) = OnStack"
    using assms(4) that i(6) a fst_E_V a(2)
    by (auto simp: af_scanres_def af_scanned_def)
  then have "af_scanres (af_handle (st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack st))\<rparr>) ?a
    False)"
    by (intro af_handle_af_scanres[OF AF_inv_in_advance[OF assms(1,2)] af_pristine1_in_advance[OF assms(1-3)] a(2)])
       (insert assms(4,5) i(4) a af_in_advance_scan_sub[OF i(1-5)], (auto simp: af_scanres_def AF_DFS_upd2_def Let_def))
  then show ?thesis
    by (simp add: AF_DFS_upd2_def Let_def)
qed

text \<open>The combined @{const af_pristine} is preserved by every @{const AF_DFS} step: an old
      free-scanned arc keeps @{term \<open>fst \<noteq> snd\<close>} by anti-monotone freeness and scan-subsumption; a
      newly scanned self-loop is the just-advanced current edge, which @{const af_handle} saturates.\<close>

lemma af_pristine_handle:
  assumes "AF_inv st'" "a \<in> \<E>" "\<not> af_unbounded (af_handle st' a dir)" "af_pristine1 (af_handle st' a dir)"
    "af_flow st' = af_flow st" "\<And>b. \<lbrakk>b \<noteq> a; af_scanned st' b\<rbrakk> \<Longrightarrow> af_scanned
      st b" "af_pristine st"
  shows "af_pristine (af_handle st' a dir)"
proof-
  have i: "AF_invar_1 st'" "AF_invar_2 st'" "AF_invar_3 st'" "AF_invar_feas st'" "AF_invar_free st'"
    "AF_invar_estE st'" "AF_invar_V st'" "flow_invar (af_flow st')"
    using assms(1)
    by (auto simp: AF_inv_def AF_invar_1_def)
  have s: "\<lbrakk>af_scanned (af_handle st' a dir) b; b \<noteq> a\<rbrakk> \<Longrightarrow> af_scanned st b" for b
    using af_handle_scanned_sub i(1,2,7) assms(6)
    by (blast)
  have h: "fst a = snd a \<Longrightarrow> af_handle st' a dir = af_selfloop_handle st' a"
    by (simp add: af_handle_real[OF assms(2)])
  show ?thesis
    unfolding af_pristine_def
  proof(intro conjI assms(4); intro allI impI)
    fix b assume "af_scanned (af_handle st' a dir) b" "af_arc_free (af_flow (af_handle st' a dir)) b"
    then show "fst b \<noteq> snd b"
      using s assms(3,5,7) h af_handle_free_mono[OF i(1,4,5) assms(2) i(6), of dir b]
            af_selfloop_handle_notfree[of a st'] assms(2) i(8)
      by (cases "b = a") (auto simp: af_pristine_def)
  next
    fix b assume "af_scanned (af_handle st' a dir) b" "fst b = snd b"
    then show "(0 \<le> \<c> b \<longrightarrow> flow_lookup (af_flow (af_handle st' a dir)) b = 0)
             \<and> (\<c> b < 0 \<longrightarrow> flow_lookup (af_flow (af_handle st' a dir)) b = cap b)"
      using s assms(3,5,7) h af_handle_flow_selfloop_off[OF i(1,2,3,6) assms(2), of b dir]
            af_selfloop_handle_norm[of a st'] assms(2) i(8)
      by (cases "b = a") (auto simp: af_pristine_def)
  qed
qed

lemma af_pristine_upd:
  assumes "AF_inv st" "af_pristine st"
  shows "\<lbrakk>AF_DFS_call_1_conds st; \<not> af_unbounded (AF_DFS_upd1 st)\<rbrakk> \<Longrightarrow> af_pristine
    (AF_DFS_upd1 st)"
    "\<lbrakk>AF_DFS_call_2_conds st; \<not> af_unbounded (AF_DFS_upd2 st)\<rbrakk> \<Longrightarrow> af_pristine
      (AF_DFS_upd2 st)"
    "AF_DFS_call_3_conds st \<Longrightarrow> af_pristine (AF_DFS_upd3 st)"
proof-
  have p: "af_pristine1 st"
    using assms(2)
    by (simp add: af_pristine_def)
  have i: "AF_invar_1 st" "AF_invar_iter st" "AF_invar_V st"
    using assms(1)
    by (auto simp: AF_inv_def)
  show "af_pristine (AF_DFS_upd1 st)" if "AF_DFS_call_1_conds st" "\<not> af_unbounded (AF_DFS_upd1 st)"
  proof-
    have j: "af_vstack st \<noteq> []" "out_has (af_out_arr st) (hd (af_vstack st))" "hd (af_vstack st) \<in> \<V>"
      using that(1) i(3) hd_in_set[of "af_vstack st"]
      by (auto elim!: call_cond_elims simp: AF_invar_V_def)
    then have "out_current (af_out_arr st) (hd (af_vstack st)) \<in> \<E>"
      using af_current_out_endpoint[OF _ j(3,2)] i(2)
      by (auto simp: AF_invar_iter_def)
    then show ?thesis
      using af_pristine_handle[OF AF_inv_out_advance[OF assms(1) that(1)] _ _ _ _
              af_out_advance_scan_sub[OF i j(1,2)] assms(2)]
            that(2) af_pristine1_upd(1)[of st] assms(1) p that(1)
      by (simp add: AF_DFS_upd1_def Let_def)
  qed
  show "af_pristine (AF_DFS_upd2 st)" if "AF_DFS_call_2_conds st" "\<not> af_unbounded (AF_DFS_upd2 st)"
  proof-
    have j: "af_vstack st \<noteq> []" "in_has (af_in_arr st) (hd (af_vstack st))" "hd (af_vstack st) \<in> \<V>"
      using that(1) i(3) hd_in_set[of "af_vstack st"]
      by (auto elim!: call_cond_elims simp: AF_invar_V_def)
    then have "in_current (af_in_arr st) (hd (af_vstack st)) \<in> \<E>"
      using af_current_in_endpoint[OF _ j(3,2)] i(2)
      by (auto simp: AF_invar_iter_def)
    then show ?thesis
      using af_pristine_handle[OF AF_inv_in_advance[OF assms(1) that(1)] _ _ _ _
              af_in_advance_scan_sub[OF i j(1,2)] assms(2)]
            that(2) af_pristine1_upd(2)[of st] assms(1) p that(1)
      by (simp add: AF_DFS_upd2_def Let_def)
  qed
  show "af_pristine (AF_DFS_upd3 st)" if "AF_DFS_call_3_conds st"
    using assms(2) af_pristine1_upd3[of st] assms(1) that p
    by (simp add: af_pristine_def af_scanned_def AF_DFS_upd3_def) blast
qed

subsection \<open>Lifting the finish-order invariant through the instrumented DFS\<close>

text \<open>The finish clock never decreases: a vertex is stamped @{term c} when it is finished and the clock
      then advances, so every finished vertex's rank stays below the current clock; the ranking is
      injective on finished vertices, which lets the forest argument pick a strict minimum on a cycle.\<close>

definition "af_vrank st rk c \<longleftrightarrow>
  (\<forall>u\<in>\<V>. st_lookup (af_state st) u = Finished \<longrightarrow> rk u < (c :: nat)) \<and>
  inj_on rk {v\<in>\<V>. st_lookup (af_state st) v = Finished}"

lemma af_vrank_upd:
  assumes "AF_inv st" "af_vrank st rk c"
  shows "AF_DFS_call_1_conds st \<Longrightarrow> af_vrank (AF_DFS_upd1 st) rk c"
    "AF_DFS_call_2_conds st \<Longrightarrow> af_vrank (AF_DFS_upd2 st) rk c"
    "AF_DFS_call_3_conds st \<Longrightarrow> af_vrank (AF_DFS_upd3 st) (rk(hd (af_vstack st) := c)) (Suc c)"
proof-
  show "AF_DFS_call_1_conds st \<Longrightarrow> af_vrank (AF_DFS_upd1 st) rk c"
    "AF_DFS_call_2_conds st \<Longrightarrow> af_vrank (AF_DFS_upd2 st) rk c"
    by (intro AF_DFS_upd_pred[where P = "\<lambda>s. af_vrank s rk c"] assms;
        simp add: af_vrank_def af_handle_finished_iff)+
  show "af_vrank (AF_DFS_upd3 st) (rk(hd (af_vstack st) := c)) (Suc c)" if "AF_DFS_call_3_conds st"
  proof-
    have "hd (af_vstack st) \<in> \<V>" "st_lookup (af_state st) (hd (af_vstack st)) = OnStack"
      "st_invar (af_state st)"
      using assms(1) that hd_in_set
      by (auto elim!: call_cond_elims simp: AF_inv_def AF_invar_1_def AF_invar_2_def AF_invar_V_def)
    then show ?thesis
      using assms(2) unfolding af_vrank_def AF_DFS_upd3_def
      by (auto simp: state_arr.fixed_univ_map_upd inj_on_def split: if_splits)
  qed
qed

text \<open>The four running invariants of the finish-order argument, vacuous on an unbounded state. With
      @{const AF_inv} they are preserved by every update, so they hold of the whole-run result, with
      respect to the finish ranks accumulated by @{const AF_DFS_i}.\<close>

definition "af_fin st rk c \<longleftrightarrow>
  (\<not> af_unbounded st \<longrightarrow> af_pristine st \<and> af_scanres st \<and> af_rankok st rk \<and> af_vrank
    st rk c)"

lemma AF_DFS_call_bounded:
  "AF_DFS_call_1_conds st \<Longrightarrow> \<not> af_unbounded st"
  "AF_DFS_call_2_conds st \<Longrightarrow> \<not> af_unbounded st"
  "AF_DFS_call_3_conds st \<Longrightarrow> \<not> af_unbounded st"
  by (auto elim!: call_cond_elims)

lemma af_fin_upd:
  assumes "AF_inv st" "af_fin st rk c"
  shows "AF_DFS_call_1_conds st \<Longrightarrow> af_fin (AF_DFS_upd1 st) rk c"
    "AF_DFS_call_2_conds st \<Longrightarrow> af_fin (AF_DFS_upd2 st) rk c"
    "AF_DFS_call_3_conds st \<Longrightarrow> af_fin (AF_DFS_upd3 st) (rk(hd (af_vstack st) := c)) (Suc c)"
proof-
  have "af_pristine st" "af_pristine1 st" "af_scanres st" "af_rankok st rk" "af_vrank st rk c"
    "\<And>u. \<lbrakk>u \<in> \<V>; st_lookup (af_state st) u = Finished\<rbrakk> \<Longrightarrow> rk u < c"
    if "\<not> af_unbounded st"
    using assms(2) that
    by (auto simp: af_fin_def af_pristine_def af_vrank_def)
  then show "AF_DFS_call_1_conds st \<Longrightarrow> af_fin (AF_DFS_upd1 st) rk c"
    "AF_DFS_call_2_conds st \<Longrightarrow> af_fin (AF_DFS_upd2 st) rk c"
    "AF_DFS_call_3_conds st \<Longrightarrow> af_fin (AF_DFS_upd3 st) (rk(hd (af_vstack st) := c)) (Suc c)"
    using assms(1)
    by (auto simp: af_fin_def dest: AF_DFS_call_bounded
          intro: af_pristine_upd af_scanres_upd1 af_scanres_upd2 af_scanres_upd3
          af_rankok_upd af_rankok_upd3 af_vrank_upd)
qed

lemma AF_DFS_i_simps:
  "\<lbrakk>AF_DFS_dom st; AF_DFS_call_1_conds st\<rbrakk> \<Longrightarrow> AF_DFS_i st rk c = AF_DFS_i (AF_DFS_upd1
    st) rk c"
    "\<lbrakk>AF_DFS_dom st; AF_DFS_call_2_conds st\<rbrakk> \<Longrightarrow> AF_DFS_i st rk c = AF_DFS_i
      (AF_DFS_upd2 st) rk c"
    "\<lbrakk>AF_DFS_dom st; AF_DFS_call_3_conds st\<rbrakk> \<Longrightarrow> AF_DFS_i st rk c = AF_DFS_i
      (AF_DFS_upd3 st) (rk(hd (af_vstack st) := c)) (Suc c)"
    "\<lbrakk>AF_DFS_dom st; AF_DFS_ret_conds st\<rbrakk> \<Longrightarrow> AF_DFS_i st rk c = (st, rk, c)"
  using AF_DFS_i_dom_all[of st]
  by (auto simp: AF_DFS_i.psimps AF_DFS_upd1_def AF_DFS_upd2_def AF_DFS_upd3_def
        AF_DFS_ret_conds_def Let_def elim!: call_cond_elims split: list.splits)

lemma AF_DFS_i_fin:
  assumes "AF_DFS_dom st" "multigraph_inv out_arr in_arr"
  shows "\<lbrakk>AF_inv st; af_fin st rk c\<rbrakk> \<Longrightarrow> \<exists>r cc. AF_DFS_i st rk c = (AF_DFS st,
    r, cc) \<and> af_fin (AF_DFS st) r cc"
  using assms(1)
proof(induction arbitrary: rk c rule: AF_DFS_induct[consumes 1])
  case IH: (1 st)
  show ?case
    by (rule AF_DFS_cases[of st]; insert IH assms(2);
        simp only: AF_DFS_i_simps[OF IH(1)] AF_DFS_simps[OF IH(1)] AF_DFS_ret_def;
        (blast intro: AF_inv_holds_1 AF_inv_holds_2 AF_inv_holds_3 af_fin_upd))
qed

subsection \<open>The four running invariants at a launch's initial state\<close>

text \<open>Launching the inner DFS from a fresh vertex @{term s} marks @{term s} on-stack and clears the
      three stacks; the flow and iterators are inherited. Hence the running invariants of the launched
      configuration reduce to conditions on the inherited data.\<close>

lemma af_pristine_initial:
  "\<lbrakk>st_invar stt; s \<in> \<V>; (\<And>v. \<lbrakk>v \<in> \<V>; st_lookup stt v = Unseen\<rbrakk>
    \<Longrightarrow> out_iterated oa v = {} \<and> in_iterated ia v = {}); (\<And>a. \<lbrakk>a \<in> out_iterated oa
    (fst a) \<or> a \<in> in_iterated ia (snd a); af_arc_free fl a\<rbrakk> \<Longrightarrow> fst a \<noteq> snd a);
    (\<And>a. \<lbrakk>a \<in> out_iterated oa (fst a) \<or> a \<in> in_iterated ia (snd a); fst a = snd a\<rbrakk>
         \<Longrightarrow> (0 \<le> \<c> a \<longrightarrow> flow_lookup fl a = 0) \<and> (\<c> a < 0
           \<longrightarrow> flow_lookup fl a = cap a))\<rbrakk> \<Longrightarrow> af_pristine (AF_DFS_initial fl oa
           ia stt s)"
  by (auto simp: af_pristine_def af_pristine1_def af_scanned_def AF_DFS_initial_def
                 state_arr.fixed_univ_map_upd split: if_splits)

lemma af_vrank_initial:
  "\<lbrakk>st_invar stt; s \<in> \<V>; (\<And>u. \<lbrakk>u \<in> \<V>; st_lookup stt u = Finished\<rbrakk>
    \<Longrightarrow> rk u < (c :: nat)); inj_on rk {v\<in>\<V>. st_lookup stt v = Finished}\<rbrakk>
    \<Longrightarrow> af_vrank (AF_DFS_initial fl oa ia stt s) rk c"
  by (auto simp: af_vrank_def AF_DFS_initial_def state_arr.fixed_univ_map_upd split: if_splits
           intro: inj_on_subset)

lemma af_rankok_initial:
  assumes "st_invar stt" "s \<in> \<V>" "st_lookup stt s = Unseen"
    "af_rankok st0 rk" "af_flow st0 = fl" "af_state st0 = stt"
  shows "af_rankok (AF_DFS_initial fl oa ia stt s) rk"
proof-
  have "st_lookup (af_state (AF_DFS_initial fl oa ia stt s)) w = Finished \<longleftrightarrow> st_lookup (af_state
    st0) w = Finished"
    for w
    using assms(1-3,6)
    by (auto simp: AF_DFS_initial_def state_arr.fixed_univ_map_upd)
  then show ?thesis
    using assms(4,5) unfolding af_rankok_def af_hgt_def
    by (simp add: AF_DFS_initial_def)
qed

lemma af_scanres_initial:
  assumes "st_invar stt" "s \<in> \<V>" "\<And>w. w \<in> \<V> \<Longrightarrow> st_lookup stt w \<noteq> OnStack"
    "\<And>v. \<lbrakk>v \<in> \<V>; st_lookup stt v = Unseen\<rbrakk> \<Longrightarrow> out_iterated oa v = {} \<and>
      in_iterated ia v = {}"
    "st_lookup stt s = Unseen"
  shows "af_scanres (AF_DFS_initial fl oa ia stt s)"
proof-
  have "\<lbrakk>x \<in> out_iterated oa w; w \<in> \<V>\<rbrakk> \<Longrightarrow> st_lookup stt w = Finished"
    "\<lbrakk>x \<in> in_iterated ia w; w \<in> \<V>\<rbrakk> \<Longrightarrow> st_lookup stt w = Finished" for w x
    using assms(3,4)[of w]
    by (cases "st_lookup stt w"; (auto))+
  then show ?thesis
    using assms(1-3,5)
    by (auto simp: af_scanres_def af_scanned_def AF_DFS_initial_def state_arr.fixed_univ_map_upd fst_E_V snd_E_V
             split: if_splits)
qed

subsection \<open>The forest keystone: the finish-order invariant forbids a free scanned cycle\<close>

text \<open>The endpoints of a residual arc are exactly the endpoints of its underlying arc, and (for a
      non-self-loop) the @{const af_hgt} ``other endpoint'' picks out the arc's far residual endpoint.\<close>

lemma fstv_sndv_oedge: "{fstv e, sndv e} = {fst (oedge e), snd (oedge e)}"
  by (cases e) auto

lemma af_hgt_other_fstv:
  "\<lbrakk>fst (oedge e) \<noteq> snd (oedge e); v = fstv e\<rbrakk> \<Longrightarrow> (if fst (oedge e) = v then snd
    (oedge e) else fst (oedge e)) = sndv e"
  by (cases e) auto

lemma af_hgt_other_sndv:
  "\<lbrakk>fst (oedge e) \<noteq> snd (oedge e); v = sndv e\<rbrakk> \<Longrightarrow> (if fst (oedge e) = v then snd
    (oedge e) else fst (oedge e)) = fstv e"
  by (cases e) auto

text \<open>Consecutive residual arcs of a @{const prepath} share a vertex.\<close>

lemma prepath_consec:
  assumes "prepath C" "Suc i < length C"
  shows "sndv (C ! i) = fstv (C ! Suc i)"
proof-
  have "C \<noteq> []" "cas (fstv (hd C)) (map to_vertex_pair C) (sndv (last C))"
    using assms(1)
    by (auto simp: prepath_def awalk_def)
  then have "map prod.fst (map to_vertex_pair C) @ [prod.snd (last (map to_vertex_pair C))]
             = prod.fst (hd (map to_vertex_pair C)) # map prod.snd (map to_vertex_pair C)"
    using awalk_verts_conv'[of "fstv (hd C)" "map to_vertex_pair C"]
    by (simp add: awalk_verts_conv)
  then have "(map prod.fst (map to_vertex_pair C) @ [prod.snd (last (map to_vertex_pair C))]) ! Suc i
             = (prod.fst (hd (map to_vertex_pair C)) # map prod.snd (map to_vertex_pair C)) ! Suc i"
    by (rule arg_cong)
  then show ?thesis
    using assms(2)
    by (simp add: nth_append to_vertex_pair_fst_snd)
qed

text \<open>The keystone. Given a closed @{const prepath} of distinct-underlying, free, non-self-loop residual
      arcs over finished vertices, the minimum-rank vertex carries two distinct incident free arcs whose
      far endpoints both outrank it --- contradicting @{const af_rankok}.\<close>

lemma AF_forest_from_cycle:
  assumes "af_rankok st rk" "inj_on (rk :: 'v \<Rightarrow> nat) {v\<in>\<V>. st_lookup (af_state st) v = Finished}"
    "\<And>v. v \<in> \<V> \<Longrightarrow> st_lookup (af_state st) v = Finished"
    "\<And>e. e \<in> set C \<Longrightarrow> fst (oedge e) \<noteq> snd (oedge e) \<and> af_arc_free (af_flow st)
      (oedge e)"
    "prepath C" "distinct (map oedge C)" "fstv (hd C) = sndv (last C)" "set C \<subseteq> \<EE>"
  shows False
proof-
  let ?n = "length C"
  have ne: "C \<noteq> []"
    using assms(5)
    by (simp add: prepath_def)
  have V: "oedge e \<in> \<E>" "fstv e \<in> \<V>" "sndv e \<in> \<V>" "fstv e \<noteq> sndv e" if "e \<in> set C" for e
  proof-
    have "oedge e \<in> \<E>" "fst (oedge e) \<noteq> snd (oedge e)"
      using that assms(4,8)
      by (auto simp: o_edge_res)
    then show "oedge e \<in> \<E>" "fstv e \<in> \<V>" "sndv e \<in> \<V>" "fstv e \<noteq> sndv e"
      using fst_E_V[of "oedge e"] snd_E_V[of "oedge e"]
      by (cases e; (simp))+
  qed
  obtain i0 where i0: "i0 < ?n" "\<And>i. i < ?n \<Longrightarrow> rk (fstv (C ! i0)) \<le> rk (fstv (C ! i))"
    using arg_min_nat_lemma[of "\<lambda>i. i < ?n" 0 "\<lambda>i. rk (fstv (C ! i))"] ne
    by (auto)
  define i1 where "i1 = (if i0 = 0 then ?n - 1 else i0 - 1)"
  define k where "k = (if Suc i0 < ?n then Suc i0 else 0)"
  have "2 \<le> ?n"
  proof(rule ccontr)
    assume "\<not> 2 \<le> ?n"
    then obtain x where "C = [x]"
      using ne
      by (cases C; cases "tl C") auto
    then show False
      using V(4)[of x] assms(7)
      by (simp)
  qed
  then have j: "i1 < ?n" "k < ?n" "i1 \<noteq> i0"
    using i0(1)
    by (auto simp: i1_def k_def)
  have j4: "sndv (C ! i1) = fstv (C ! i0)"
  proof(cases "i0 = 0")
    case True
    then show ?thesis
      using assms(7) ne
      by (simp add: i1_def last_conv_nth hd_conv_nth)
  next
    case False
    then show ?thesis
      using prepath_consec[OF assms(5), of i1] i0(1)
      by (simp add: i1_def)
  qed
  have j5: "sndv (C ! i0) = fstv (C ! k)"
  proof(cases "Suc i0 < ?n")
    case True
    then show ?thesis
      using prepath_consec[OF assms(5), of i0]
      by (simp add: k_def)
  next
    case False
    then have "i0 = ?n - 1"
      using i0(1)
      by (simp)
    then show ?thesis
      using assms(7) ne
      by (simp add: k_def last_conv_nth hd_conv_nth)
  qed
  have m: "C ! i0 \<in> set C" "C ! i1 \<in> set C"
    using i0(1) j(1)
    by (simp_all)
  have "fstv (C ! i0) \<in> {v\<in>\<V>. st_lookup (af_state st) v = Finished}"
    "sndv (C ! i0) \<in> {v\<in>\<V>. st_lookup (af_state st) v = Finished}"
    "fstv (C ! i1) \<in> {v\<in>\<V>. st_lookup (af_state st) v = Finished}"
    using V m(1) V m(2) assms(3)
    by (simp_all)
  then have "rk (fstv (C ! i0)) < rk (sndv (C ! i0))" "rk (fstv (C ! i0)) < rk (fstv (C ! i1))"
    using i0(2)[of k] j(2) i0(2)[of i1] j(1) j4 j5 V(4)[of "C ! i0"] m(1) V(4)[of "C ! i1"] m(2)
          assms(2)
    by (auto simp: le_less dest: inj_onD)
  then have "af_hgt st rk (fstv (C ! i0)) (oedge (C ! i0))" "af_hgt st rk (fstv (C ! i0)) (oedge (C ! i1))"
    using af_hgt_other_fstv[OF conjunct1[OF assms(4)[OF m(1)]] refl]
          af_hgt_other_sndv[OF conjunct1[OF assms(4)[OF m(2)]] j4[symmetric]]
    by (simp_all add: af_hgt_def)
  moreover have "fstv (C ! i0) \<in> {fst (oedge (C ! i0)), snd (oedge (C ! i0))}"
    "fstv (C ! i0) \<in> {fst (oedge (C ! i1)), snd (oedge (C ! i1))}"
    using j4
    by (simp_all add: fstv_sndv_oedge[symmetric])
  ultimately have "oedge (C ! i0) = oedge (C ! i1)"
    using assms(1)[unfolded af_rankok_def, rule_format, of "fstv (C ! i0)" "oedge (C ! i0)" "oedge (C ! i1)"]
          assms(3) V(1,2)[of "C ! i0"] m(1) V(1)[of "C ! i1"] m(2) assms(4)[of "C ! i0"] assms(4)[of "C ! i1"]
    by (simp)
  then show False
    using assms(6) i0(1) j(1,3) nth_eq_iff_index_eq[of "map oedge C" i0 i1]
    by (simp)
qed

text \<open>Packaged as @{const AF_forest}: with the finish-order invariants and every graph vertex finished,
      no free scanned closed trail exists (@{const af_pristine} excludes free scanned self-loops).\<close>

lemma AF_forest_from_rankok:
  assumes "af_rankok st rk" "af_vrank st rk c" "\<And>v. v \<in> \<V> \<Longrightarrow> st_lookup (af_state st) v =
    Finished"
    "af_pristine st"
  shows "AF_forest st"
  unfolding AF_forest_def
proof(intro notI, elim exE conjE)
  fix C
  assume C: "prepath C" "\<forall>e\<in>set C. af_arc_free (af_flow st) (oedge e) \<and> af_scanned st (oedge e)"
    "distinct (map oedge C)" "fstv (hd C) = sndv (last C)" "set C \<subseteq> \<EE>"
  show False
    by (rule AF_forest_from_cycle[where st=st and rk=rk and C=C]; insert assms C;
        auto simp: af_pristine_def af_vrank_def)
qed

lemma af_fin_cong:
  "\<lbrakk>af_flow s = af_flow t; af_state s = af_state t; af_out_arr s = af_out_arr t; af_in_arr s = af_in_arr
    t\<rbrakk>
   \<Longrightarrow> af_pristine s = af_pristine t \<and> af_rankok s rk = af_rankok t rk \<and> af_vrank s rk c =
     af_vrank t rk c"
  by (simp add: af_pristine_def af_pristine1_def af_scanned_def af_rankok_def af_hgt_def af_vrank_def)

subsection \<open>Threading the finish-order invariant through the outer loop and closing acyclicity\<close>

text \<open>The outer state carries the flow, vertex states and iterators of an inner state with empty
      stacks; the finish-order invariants of the outer loop are read off that projection.\<close>

definition aff_af :: "('v, 'farr, 'sarr, 'vvit, 'g, 'z) AF_state_scheme \<Rightarrow> ('v, 'e, 'farr, 'g, 'sarr)
    AF_DFS_state"
  where "aff_af st = \<lparr>af_flow = aff_flow st, af_vstack = [], af_estack = [], af_dstack = [],
  af_out_arr = aff_out_arr st, af_in_arr = aff_in_arr st, af_state = aff_state st, af_unbounded = False\<rparr>"

definition "AFF_fin2 st rk c \<longleftrightarrow>
  (\<not> aff_unbounded st \<longrightarrow> af_pristine (aff_af st) \<and> af_rankok (aff_af st) rk \<and> af_vrank
    (aff_af st) rk c)"

lemma AFF_fin2_holds_1: "AFF_fin2 st rk c \<Longrightarrow> AFF_fin2 (AF_outer_upd1 st) rk c"
  by (simp add: AFF_fin2_def aff_af_def AF_outer_upd1_def)

lemma AFF_fin2_initial:
  "\<forall>u. out_iterated out_arr u = {} \<and> in_iterated in_arr u = {} \<Longrightarrow> AFF_fin2
    (AF_outer_initial f0) (\<lambda>_. 0) 0"
  using state_init_unseen
  by (auto simp: AFF_fin2_def aff_af_def AF_outer_initial_def af_pristine_def af_pristine1_def af_scanned_def
                 af_rankok_def af_vrank_def inj_on_def)

text \<open>The launch reconstructs the ranking from the inner DFS via @{thm [source] AF_DFS_i_fin} and the
      launch's @{const AF_DFS_initial} lemmas.\<close>

lemma AFF_fin2_holds_2:
  assumes "multigraph_inv out_arr in_arr" "AF_outer_call_2_conds st" "AFF_inv st" "AFF_fin2 st rk c"
  shows "\<exists>rk' c'. AFF_fin2 (AF_outer_upd2 st) rk' c'"
proof-
  let ?v = "current_vertex (aff_vit st)"
  let ?init = "af_launch st :: ('v, 'e, 'farr, 'g, 'sarr) AF_DFS_state"
  have i: "st_invar (aff_state st)" "?v \<in> \<V>" "\<forall>w\<in>\<V>. st_lookup (aff_state st) w \<noteq> OnStack"
    "st_lookup (aff_state st) ?v = Unseen" "\<not> aff_unbounded st"
    using assms(2,3) vit_current_V assms(3)
    by (auto simp: AFF_inv_def AF_outer_call_2_conds_def)
  have p: "af_pristine (aff_af st)" "af_rankok (aff_af st) rk" "af_vrank (aff_af st) rk c"
    using assms(4) i(5)
    by (auto simp: AFF_fin2_def)
  note inv = AF_outer_launch[OF assms(1-3)]
  have "af_pristine ?init"
    by (rule af_pristine_initial[OF i(1,2)])
       (insert p(1), (auto simp: aff_af_def af_pristine_def af_pristine1_def af_scanned_def))
  moreover have "af_scanres ?init"
    by (rule af_scanres_initial[OF i(1,2) _ _ i(4)])
       (insert i(3) p(1), (auto simp: aff_af_def af_pristine_def af_pristine1_def))
  moreover have "af_rankok ?init rk"
    by (rule af_rankok_initial[OF i(1,2,4) p(2)]) (simp_all add: aff_af_def)
  moreover have "af_vrank ?init rk c"
    by (rule af_vrank_initial[OF i(1,2)]) (insert p(3), (auto simp: aff_af_def af_vrank_def))
  ultimately have "af_fin ?init rk c"
  by (simp add: af_fin_def)
  then obtain r cc where "af_fin (AF_DFS ?init) r cc"
    using AF_DFS_i_fin inv(2) assms(1) inv(1)
    by (blast)
  then have "AFF_fin2 (AF_outer_upd2 st) r cc"
    using af_fin_cong[of "aff_af (AF_outer_upd2 st)" "AF_DFS ?init" r cc]
    by (simp add: AFF_fin2_def af_fin_def aff_af_def AF_outer_upd2_def Let_def)
  then show ?thesis
    by (blast)
qed

lemma AF_outer_fin:
  assumes "multigraph_inv out_arr in_arr" "AF_outer_dom st" "AFF_inv st" "AFF_fin2 st rk c"
  shows "\<exists>rk c. AFF_fin2 (AF_outer st) rk c"
  by (rule AF_outer_pred[where P="\<lambda>s. \<exists>rk c. AFF_fin2 s rk c"]; insert assms;
      (blast intro: AFF_fin2_holds_1 AFF_fin2_holds_2))

text \<open>Assembling: at @{const make_acyclic}'s bounded return, the finish-order invariants and full
      vertex coverage meet, so the returned flow has no free scanned closed trail, and every scanned
      self-loop sits at its cost-preferred bound.\<close>

lemma make_acyclic_fin:
  assumes "multigraph_inv out_arr in_arr" "flow_invar f0" "af_cap_feasible f0" "vit_invar all_vertices"
    "vit_abstract all_vertices = \<V>" "vit_iterated all_vertices = {}" "make_acyclic f0 = Some f'"
    "\<forall>u. out_iterated out_arr u = {} \<and> in_iterated in_arr u = {}"
  shows "AFF_forest (AF_outer (AF_outer_initial f0))" "af_pristine (aff_af (AF_outer (AF_outer_initial f0)))"
proof-
  note r = make_acyclic_Some[OF assms(1-4) equalityD1[OF assms(5)] assms(7)]
  obtain rk c where "af_pristine (aff_af (AF_outer (AF_outer_initial f0)))"
    "af_rankok (aff_af (AF_outer (AF_outer_initial f0))) rk" "af_vrank (aff_af (AF_outer (AF_outer_initial f0))) rk c"
    using AF_outer_fin[OF assms(1) r(1,2) AFF_fin2_initial[OF assms(8)]] r(4)
    by (auto simp: AFF_fin2_def)
  then show "af_pristine (aff_af (AF_outer (AF_outer_initial f0)))" "AFF_forest (AF_outer (AF_outer_initial f0))"
    using AF_forest_from_rankok[of "aff_af (AF_outer (AF_outer_initial f0))" rk c]
          make_acyclic_all_finished[of f0 f'] assms(1-7)
    by (auto simp: AF_forest_def AFF_forest_def af_scanned_def AFF_scanned_def aff_af_def)
qed

lemma make_acyclic_selfloop:
  assumes "multigraph_inv out_arr in_arr" "flow_invar f0" "af_cap_feasible f0" "vit_invar all_vertices"
    "vit_abstract all_vertices = \<V>" "vit_iterated all_vertices = {}" "make_acyclic f0 = Some f'"
    "\<forall>u. out_iterated out_arr u = {} \<and> in_iterated in_arr u = {}" "e \<in> \<E>" "fst e = snd e"
  shows "(0 \<le> \<c> e \<longrightarrow> flow_lookup f' e = 0) \<and> (\<c> e < 0 \<longrightarrow> flow_lookup f' e
    = cap e)"
proof-
  note r = make_acyclic_Some[OF assms(1-4) equalityD1[OF assms(5)] assms(7)]
  have "multigraph_inv (aff_out_arr (AF_outer (AF_outer_initial f0))) (aff_in_arr (AF_outer (AF_outer_initial f0)))"
    using AFF_inv_holds[of "AF_outer_initial f0"] r(1) assms(1) r(2)
    by (simp add: AFF_inv_def)
  then have "AFF_scanned (AF_outer (AF_outer_initial f0)) e"
    using AFF_scanned_of_exhausted make_acyclic_all_edges_scanned[of f0 f'] assms(1-7) fst_E_V assms(9) assms(9)
    by (blast)
  then show ?thesis
    using make_acyclic_fin(2)[of f0 f'] assms(1-8) r(3) assms(10)
    by (auto simp: af_pristine_def af_scanned_def AFF_scanned_def aff_af_def)
qed

text \<open>The top-level correctness theorem, now \emph{unconditional}: the no-free-cycle obligation
      is discharged by the forest engine.\<close>

lemma make_acyclic_correct_unconditional:
  "\<lbrakk>multigraph_inv out_arr in_arr; flow_invar f0; af_cap_feasible f0; vit_invar all_vertices; vit_abstract
    all_vertices = \<V>; vit_iterated all_vertices = {}; \<forall>u. out_iterated out_arr u = {} \<and> in_iterated
    in_arr u = {}; make_acyclic f0 = Some f'\<rbrakk> \<Longrightarrow> af_cap_feasible f' \<and> \<C> (h \<circ>
    flow_lookup f') \<le> \<C> (h \<circ> flow_lookup f0) \<and> acyclic_flow (h \<circ> flow_lookup f')"
  using make_acyclic_feasible[of f0 f'] make_acyclic_cost_le[of f0 f']
    make_acyclic_fin(1)[of f0 f'] make_acyclic_acyclic_from_forest[of f0 f']
  by auto

text \<open>The user-facing correctness theorem strengthened to a genuine @{term b}-flow: from a feasible
      @{term b}-flow input the algorithm returns a feasible @{term b}-flow of no greater cost, and acyclic.\<close>

lemma make_acyclic_correct_unconditional_bflow:
  "\<lbrakk>multigraph_inv out_arr in_arr; flow_invar f0; af_feasible b f0; vit_invar all_vertices; vit_abstract
    all_vertices = \<V>; vit_iterated all_vertices = {}; \<forall>u. out_iterated out_arr u = {} \<and> in_iterated
    in_arr u = {}; make_acyclic f0 = Some f'\<rbrakk> \<Longrightarrow> af_feasible b f' \<and> \<C> (h \<circ>
    flow_lookup f') \<le> \<C> (h \<circ> flow_lookup f0) \<and> acyclic_flow (h \<circ> flow_lookup f')"
  using make_acyclic_feasible_bal[of f0 b f'] make_acyclic_correct_unconditional[of f0 f']
  by (auto dest: af_feasible_cap)

subsection \<open>The unbounded case: a negative infinite-capacity cycle witness\<close>

text \<open>When the top-level answer is @{term None}, the instance is genuinely unbounded: there is a
      directed cycle of original arcs, every one of infinite capacity, whose total cost is negative.
      Circulating flow around such a cycle drives the cost to @{term \<open>- \<infinity>\<close>}, so no cost-minimal
        (or
      even cost-bounded acyclic) flow of the same divergence exists. This section constructs that
      witness from the state at the moment the @{const af_unbounded} flag is raised.\<close>
text \<open>The witness we produce is exactly the library predicate @{const has_neg_infty_cycle}: a closed walk
      of original arcs, all of infinite capacity, of negative total cost. We abbreviate it at the locale's
      graph parameters.\<close>

abbreviation neg_inf_cycle :: bool where
  "neg_inf_cycle \<equiv> has_neg_infty_cycle make_pair \<E> \<c> \<u>"
text \<open>@{const af_min} yields the unbounded sentinel @{term \<open>- 1\<close>} only when \emph{both} arguments are
      unbounded --- so an unbounded directional bottleneck forces \emph{every} arc on the cycle to be
      unbounded in that direction.\<close>

lemma af_min_eq_neg1: "af_min x y = - 1 \<longleftrightarrow> x = - 1 \<and> y = - 1"
  by (auto simp: af_min_def split: if_splits)

text \<open>The as-is room of an arc traversed in direction @{term d}: the room read from a \emph{single} flow
      lookup, exactly the value @{const af_scan} folds. The flipped room is @{term \<open>asis_room fl a (\<not>
        d)\<close>}.\<close>

definition asis_room :: "'farr \<Rightarrow> 'e \<Rightarrow> bool \<Rightarrow> 'n" where
  "asis_room fl a d = (let (up, dn) = af_rooms fl a in if d then up else dn)"

text \<open>A free arc has a strictly positive backward (draining) room, hence its as-is room is the sentinel
      @{term \<open>- 1\<close>} only when it is traversed \emph{forward} and its capacity is infinite.\<close>

lemma asis_room_pos_free: "af_arc_free fl a \<Longrightarrow> 0 < asis_room fl a False"
  by (auto simp: asis_room_def af_rooms_def af_arc_free_def Let_def)

lemma asis_room_neg1_free: "\<lbrakk>af_arc_free fl a; asis_room fl a d = - 1\<rbrakk> \<Longrightarrow> d \<and> cap
    a = - 1"
  using asis_room_pos_free[of fl a]
  by (cases d) (auto simp: asis_room_def af_rooms_def af_arc_free_def Let_def split: if_splits)

lemma tl_len2: "x \<in> set (tl xs) \<Longrightarrow> 2 \<le> length xs"
  by (cases xs) (auto simp: Suc_le_eq length_greater_0_conv)

text \<open>The scan reaches the ancestor @{term x}: it stops at the first stack position @{term p} carrying
      @{term x}, having accumulated the walk cost as a prefix sum, and --- crucially --- if the chosen
      directional bottleneck comes back unbounded (@{term \<open>- 1\<close>}) then \emph{every} walked arc is
      unbounded in that direction (and so is the seed).\<close>

lemma af_scan_reach:
  "\<lbrakk>af_scan fl x vs es ds (k0, ra0, rf0) = (k, ra, rf); x \<in> set (tl vs); length vs \<le> Suc (length es);
    length vs \<le> Suc (length ds)\<rbrakk> \<Longrightarrow> (\<exists>p. 1 \<le> p \<and> p \<le> length es \<and>
    Suc p \<le> length vs \<and> vs ! p = x \<and>
        k = k0 + (\<Sum>i<p. af_delta_cost (es!i) (ds!i)) \<and>
        (ra = - 1 \<longrightarrow> ra0 = - 1 \<and> (\<forall>i<p. asis_room fl (es!i) (ds!i) = - 1)) \<and>
        (rf = - 1 \<longrightarrow> rf0 = - 1 \<and> (\<forall>i<p. asis_room fl (es!i) (\<not> ds!i) = - 1)))"
proof(induction fl x vs es ds "(k0, ra0, rf0)" arbitrary: k0 ra0 rf0 k ra rf rule: af_scan.induct)
  case (1 fl x u v1 vs a es d ds k0 ra0 rf0)
  obtain up dn where ud: "af_rooms fl a = (up, dn)"
    by (fastforce)
  have rooms: "asis_room fl a d = (if d then up else dn)"
    "asis_room fl a (\<not> d) = (if d then dn else up)"
    by (auto simp: asis_room_def ud)
  let ?acc = "(k0 + af_delta_cost a d, af_min (if d then up else dn) ra0, af_min (if d then dn else up) rf0)"
  show ?case
  proof(cases "v1 = x")
    case True
    then show ?thesis
      using 1(2) ud rooms
      by (intro exI[of _ 1]) (auto simp: Let_def af_min_eq_neg1)
  next
    case False
    have "af_scan fl x (v1#vs) es ds ?acc = (k, ra, rf)"
      using 1(2) ud False
      by (simp add: Let_def)
    then obtain p where p: "1 \<le> p" "p \<le> length es" "Suc p \<le> length (v1#vs)" "(v1#vs)!p = x"
      "k = (k0 + af_delta_cost a d) + (\<Sum>i<p. af_delta_cost (es!i) (ds!i))"
      "ra = - 1 \<longrightarrow> af_min (if d then up else dn) ra0 = - 1 \<and> (\<forall>i<p. asis_room fl (es!i)
        (ds!i) = - 1)"
      "rf = - 1 \<longrightarrow> af_min (if d then dn else up) rf0 = - 1 \<and> (\<forall>i<p. asis_room fl (es!i)
        (\<not> ds!i) = - 1)"
      using 1(1)[OF ud[symmetric] refl refl False] 1(3-5) False
      by (fastforce)
    show ?thesis
      by (intro exI[of _ "Suc p"])
         (insert p rooms, (auto simp: af_min_eq_neg1 nth_Cons' less_Suc_eq_0_disj
           sum.lessThan_Suc_shift simp del: sum.lessThan_Suc))
  qed
qed (auto dest: tl_len2)

text \<open>Bridge the executable @{term \<open>- 1\<close>} sentinel back to the genuine infinite capacity @{term
    \<open>\<u> a = \<infinity>\<close>}.\<close>

lemma cap_neg1_infty:
  "\<lbrakk>a \<in> \<E>; cap a = - 1\<rbrakk> \<Longrightarrow> \<u> a = \<infinity>"
  by (simp add: cap_infinite_bridge)

text \<open>A closed directed walk of arcs -- each arc's head vertex being the next arc's tail, cyclically --
      yields the @{const closed_w} required by @{const has_neg_infty_cycle}.\<close>

lemma cas_chain:
  "\<lbrakk>\<forall>i. Suc i < length C \<longrightarrow> snd (C ! i) = fst (C ! Suc i); C \<noteq> []\<rbrakk>
    \<Longrightarrow> cas (fst (hd C)) (map make_pair C) (snd (last C))"
proof(induction C)
  case (Cons a C)
  have "\<forall>i. Suc i < length C \<longrightarrow> snd (C ! i) = fst (C ! Suc i)"
    using Cons.prems(1)
    by auto
  then have "C \<noteq> [] \<Longrightarrow> cas (fst (hd C)) (map make_pair C) (snd (last C))"
    using Cons.IH
    by simp
  then show ?case
    using Cons.prems(1)[rule_format, of 0]
    unfolding make_pair_def
    by (cases C) auto
qed simp

lemma neg_inf_cycleI:
  assumes "C \<noteq> []" and "set C \<subseteq> \<E>" and "\<forall>a\<in>set C. cap a = - 1"
    and "sum_list (map \<c> C) < 0"
    and "\<forall>i<length C. snd (C!i) = fst (C!(Suc i mod length C))"
  shows neg_inf_cycle
proof(rule has_neg_infty_cycleI[where D=C])
  have "\<forall>i. Suc i < length C \<longrightarrow> snd (C!i) = fst (C!Suc i)"
    using assms(5)
    by auto
  then have "cas (fst (hd C)) (map make_pair C) (snd (last C))"
    using assms(1) cas_chain[of C]
    by blast
  moreover have "snd (last C) = fst (hd C)"
    using assms(1) assms(5)[rule_format, of "length C-1"]
    by (simp add: last_conv_nth hd_conv_nth)
  moreover have "fst (hd C) \<in> dVs (make_pair ` \<E>)"
  proof-
    have "make_pair (hd C) \<in> make_pair ` \<E>"
      by (rule imageI; rule subsetD[where A="set C"]; insert assms(1,2); auto)
    then show ?thesis
      by (auto simp: make_pair_def dVs_def)
  qed
  ultimately show "closed_w (make_pair ` \<E>) (map make_pair C)"
    using assms(1,2)
    by (auto simp: closed_w_def awalk_def)
  show "foldr (\<lambda>e. (+) (\<c> e)) C 0 < 0"
    using assms(4)
    by (simp add: sum_list.eq_foldr foldr_map o_def)
  show "set C \<subseteq> \<E>"
    by (rule assms(2))
  show "\<And>e. e \<in> set C \<Longrightarrow> \<u> e = PInfty"
    using assms(2,3) cap_neg1_infty
    by auto
qed

text \<open>Assemble the witness cycle from the stack trail. In the \<open>as-is\<close> orientation (chosen when the
    walk
      cost is non-positive) every trail arc is traversed forward and the cycle is
      @{term \<open>a # rev (take p es)\<close>}: the closing arc from the top down to the reached ancestor, then the
      trail arcs back up.\<close>

lemma trail_cycle_asis:
  assumes "af_trail vs es ds"
    and "p \<le> length es" and "1 \<le> p" and "Suc p \<le> length vs"
    and "vs ! p = x" and "hd vs = fst a" and "snd a = x"
    and "\<forall>i<p. ds ! i"
    and "\<forall>i<p. cap (es!i) = - 1" and "cap a = - 1"
    and "a \<in> \<E>" and "set es \<subseteq> \<E>"
    and "\<c> a + (\<Sum>i<p. \<c> (es!i)) < 0"
    and "vs \<noteq> []"
  shows neg_inf_cycle
proof-
  define C where "C = a # rev (take p es)"
  have lenC: "length C = Suc p"
    using assms(2)
    by (simp add: C_def)
  have Cnth: "C ! j = (if j = 0 then a else es ! (p-j))" if "j \<le> p" for j
    using that assms(2)
    by (cases j) (auto simp: C_def rev_nth)
  have trail: "snd (es!j) = vs!j \<and> fst (es!j) = vs!Suc j" if "j < p" for j
    using that assms(2,8) assms(1)[unfolded af_trail_def, rule_format, of j]
    by auto
  have closed: "\<forall>i<length C. snd (C!i) = fst (C!(Suc i mod length C))"
  proof(intro allI impI)
    fix i assume "i < length C"
    then have "i \<le> p"
      by (simp add: lenC)
    then show "snd (C!i) = fst (C!(Suc i mod length C))"
      using assms(3,5-7,14) trail[of 0] trail[of "p-1"] trail[of "p-i"] trail[of "p-Suc i"]
      by (cases "i=p"; cases "i=0";
          (auto simp: lenC Cnth hd_conv_nth Suc_diff_Suc))
  qed
  have "sum_list (map \<c> (take p es)) = (\<Sum>i<p. \<c> (es!i))"
    using assms(2)
    by (simp add: sum_list_sum_nth min_absorb2 lessThan_atLeast0)
  then have "sum_list (map \<c> C) < 0"
    using assms(13)
    by (simp add: C_def rev_map[symmetric] sum_list_rev add.commute)
  then show ?thesis
    by (intro neg_inf_cycleI[where C=C]; insert assms closed;
        auto simp: C_def dest: in_set_takeD;
        auto simp: in_set_conv_nth)
qed

text \<open>The \<open>flipped\<close> orientation (chosen when the walk cost is positive, so the reversal is negative):
      every trail arc is traversed forward down the stack and the cycle is @{term \<open>take p es @
        [a]\<close>}.\<close>

lemma trail_cycle_flip:
  assumes "af_trail vs es ds"
    and "p \<le> length es" and "1 \<le> p" and "Suc p \<le> length vs"
    and "vs ! p = x" and "hd vs = snd a" and "fst a = x"
    and "\<forall>i<p. \<not> ds ! i"
    and "\<forall>i<p. cap (es!i) = - 1" and "cap a = - 1"
    and "a \<in> \<E>" and "set es \<subseteq> \<E>"
    and "\<c> a + (\<Sum>i<p. \<c> (es!i)) < 0"
    and "vs \<noteq> []"
  shows neg_inf_cycle
proof-
  define C where "C = take p es @ [a]"
  have lenC: "length C = Suc p"
    using assms(2)
    by (simp add: C_def)
  have Cnth: "C ! j = (if j = p then a else es ! j)" if "j \<le> p" for j
    using that assms(2)
    by (auto simp: C_def nth_append)
  have trail: "fst (es!j) = vs!j \<and> snd (es!j) = vs!Suc j" if "j < p" for j
    using that assms(2,8) assms(1)[unfolded af_trail_def, rule_format, of j]
    by auto
  have closed: "\<forall>i<length C. snd (C!i) = fst (C!(Suc i mod length C))"
  proof(intro allI impI)
    fix i assume "i < length C"
    then have "i \<le> p"
      by (simp add: lenC)
    then show "snd (C!i) = fst (C!(Suc i mod length C))"
      using assms(3,5-7,14) trail[of 0] trail[of i] trail[of "Suc i"]
      by (cases "i=p"; cases "Suc i=p";
          (auto simp: lenC Cnth hd_conv_nth))
  qed
  have "sum_list (map \<c> (take p es)) = (\<Sum>i<p. \<c> (es!i))"
    using assms(2)
    by (simp add: sum_list_sum_nth min_absorb2 lessThan_atLeast0)
  then have "sum_list (map \<c> C) < 0"
    using assms(13)
    by (simp add: C_def rev_map[symmetric] sum_list_rev add.commute)
  then show ?thesis
    by (intro neg_inf_cycleI[where C=C]; insert assms closed;
        auto simp: C_def dest: in_set_takeD;
        auto simp: in_set_conv_nth)
qed

text \<open>The local witness: whenever @{const af_cancel_seg} raises the unbounded flag on the (distinct,
      free) trail closed by @{term a}, a negative infinite-capacity cycle exists. The chosen
      non-positive-cost push direction has an unbounded bottleneck, forcing every arc on the cycle to
      be forward-oriented and of infinite capacity, with strictly negative total cost.\<close>

lemma af_cancel_seg_ubd_witness:
  assumes "af_trail vs es ds" "length vs \<le> Suc (length es)" "length vs \<le> Suc (length ds)"
    "\<forall>b\<in>set es. af_arc_free fl b" "af_arc_free fl a" "set es \<subseteq> \<E>" "a \<in> \<E>" "x \<in> set
      (tl vs)"
    "hd vs = (if dir then fst a else snd a)" "x = (if dir then snd a else fst a)" "af_rooms fl a = (up, dn)"
    "af_cancel_seg up dn x vs es ds a dir fl = (fl', m', True)" "vs \<noteq> []"
  shows neg_inf_cycle
proof-
  obtain k ra rf where sc:
    "af_scan fl x vs es ds (af_delta_cost a dir, if dir then up else dn, if dir then dn else up) = (k, ra, rf)"
    by (rule prod_cases3)
  have g: "(if 0 < k then rf else ra) = - 1" "\<not> (k = 0 \<and> rf \<noteq> - 1)"
    using assms(12)
    by (auto simp: af_cancel_seg_def sc Let_def split: if_splits prod.splits)
  obtain p where p: "1 \<le> p" "p \<le> length es" "Suc p \<le> length vs" "vs ! p = x"
    "k = af_delta_cost a dir + (\<Sum>i<p. af_delta_cost (es!i) (ds!i))"
    "ra = - 1 \<longrightarrow> (if dir then up else dn) = - 1 \<and> (\<forall>i<p. asis_room fl (es!i) (ds!i) = - 1)"
    "rf = - 1 \<longrightarrow> (if dir then dn else up) = - 1 \<and> (\<forall>i<p. asis_room fl (es!i) (\<not> ds!i)
      = - 1)"
    using af_scan_reach sc assms(8,2,3)
    by (blast)
  have r: "(if dir then up else dn) = asis_room fl a dir" "(if dir then dn else up) = asis_room fl a (\<not> dir)"
    by (auto simp: asis_room_def assms(11))
  have E: "af_arc_free fl (es!i)" "es!i \<in> \<E>" if "i < p" for i
    using assms(4,6) p(2) that
    by (auto)
  have hc: "\<c> a + (\<Sum>i<p. \<c> (es!i)) = h (cost a + (\<Sum>i<p. cost (es!i)))"
    by (simp add: h_add h_sum cost_h[OF assms(7)]) (auto intro!: sum.cong simp: cost_h E(2))
  have ks: "k = (if dir then 1 else - 1) * (cost a + (\<Sum>i<p. cost (es!i)))" if "\<forall>i<p. ds ! i = dir"
    using p(5) that
    by (cases dir) (auto simp: af_delta_cost_def sum_negf[symmetric] intro!: sum.cong)
  show ?thesis
  proof(cases "0 < k")
    case True
    then have "\<not> dir" "cap a = - 1" "\<forall>i<p. \<not> ds ! i \<and> cap (es!i) = - 1"
      using g(1) p(7) r(2) assms(5) E(1)
      by (auto dest: asis_room_neg1_free)
    then show ?thesis
      by (intro trail_cycle_flip[OF assms(1) p(2,1,3,4)])
         (insert True ks hc assms(6,7,9,10,13), (auto simp: h_less_iff[of _ 0, simplified]))
  next
    case False
    then have "dir" "cap a = - 1" "\<forall>i<p. ds ! i \<and> cap (es!i) = - 1"
      using g(1) p(6) r(1) assms(5) E(1)
      by (auto dest: asis_room_neg1_free)
    moreover have "k \<noteq> 0"
      using g(2) p(7) r(2) asis_room_neg1_free[OF assms(5), of "\<not> dir"] calculation(1)
      by (auto)
    ultimately show ?thesis
      by (intro trail_cycle_asis[OF assms(1) p(2,1,3,4)])
         (insert False ks hc assms(6,7,9,10,13), (auto simp: h_less_iff[of _ 0, simplified]))
  qed
qed

text \<open>@{const af_reset_unsee_seg} leaves the unbounded flag untouched.\<close>

lemma af_reset_unsee_seg_unbounded[simp]: "af_unbounded (af_reset_unsee_seg n vs st) = af_unbounded st"
  by (induction n vs st rule: af_reset_unsee_seg.induct) (auto simp: af_reset_def)

text \<open>The running witness: once the unbounded flag is raised, a negative infinite-capacity cycle
      exists. The cycle is a flow-independent property of the graph, so the only work is at the step
      that first raises the flag --- a self-loop normalisation or a cycle cancellation.\<close>

lemma af_handle_ubd_wit:
  assumes "AF_inv st" "a \<in> \<E>" "(if dir then fst a else snd a) = hd (af_vstack st)" "af_vstack st \<noteq> []"
    "af_unbounded st \<longrightarrow> neg_inf_cycle" "af_unbounded (af_handle st a dir)"
  shows neg_inf_cycle
  using assms(2)
proof(cases rule: af_handle_cases[of a st dir])
  case selfloop
  then show ?thesis
    using assms(5,6) neg_inf_cycleI[of "[a]"] assms(2)
    by (auto simp: af_selfloop_handle_unbounded[OF assms(2)])
next
  case (unbounded up dn fl m')
  have i: "af_cap_feasible (af_flow st)" "\<forall>b\<in>set (af_estack st). af_arc_free (af_flow st) b"
    "set (af_estack st) \<subseteq> \<E>" "af_trail (af_vstack st) (af_estack st) (af_dstack st)"
    "Suc (length (af_estack st)) = length (af_vstack st)" "length (af_dstack st) = length (af_estack st)"
    "\<forall>v\<in>\<V>. (st_lookup (af_state st) v = OnStack) = (v \<in> set (af_vstack st))"
    using assms(1,4)
    by (auto simp: AF_inv_def AF_invar_feas_def AF_invar_free_def AF_invar_estE_def AF_invar_3_conv AF_invar_2_def)
  have "af_arc_free (af_flow st) a"
    using af_guard_free unbounded(2) unbounded(3) i(1) assms(2)
    by (auto simp: af_cap_feasible_def)
  moreover have "(if dir then snd a else fst a) \<in> set (tl (af_vstack st))"
    using unbounded(1,5) i(7) assms(3,4) fst_E_V assms(2) snd_E_V assms(2)
    by (cases dir; cases "af_vstack st") auto
  ultimately show ?thesis
    by (intro af_cancel_seg_ubd_witness[OF i(4) _ _ i(2) _ i(3) assms(2) _ _ refl unbounded(2,6) assms(4)])
       (insert i(5,6) assms(3), (auto))
qed (insert assms(5,6), (auto))

lemma AF_DFS_ubd_wit:
  "\<lbrakk>AF_DFS_dom st; multigraph_inv out_arr in_arr; AF_inv st; af_unbounded st \<longrightarrow>
    neg_inf_cycle\<rbrakk>
   \<Longrightarrow> af_unbounded (AF_DFS st) \<longrightarrow> neg_inf_cycle"
  by (rule AF_DFS_pred; (auto simp: AF_DFS_upd3_def intro: af_handle_ubd_wit))

text \<open>Outer-loop level: each launch inherits the witness from the inner DFS; a skip leaves the flag
      untouched.\<close>

lemma AF_outer_ubd_wit:
  assumes "multigraph_inv out_arr in_arr" "AF_outer_dom st" "AFF_inv st" "aff_unbounded st \<longrightarrow>
    neg_inf_cycle"
  shows "aff_unbounded (AF_outer st) \<longrightarrow> neg_inf_cycle"
proof(rule AF_outer_pred[where P = "\<lambda>s. aff_unbounded s \<longrightarrow> neg_inf_cycle", OF assms])
  show "aff_unbounded (AF_outer_upd2 s) \<longrightarrow> neg_inf_cycle" if "AF_outer_call_2_conds s" "AFF_inv s" for s
    using AF_DFS_ubd_wit[OF AF_outer_launch(2)[OF assms(1) that] assms(1) AF_outer_launch(1)[OF assms(1) that]]
    by (simp add: AF_outer_upd2_def Let_def AF_DFS_initial_def)
qed (simp add: AF_outer_upd1_def)

text \<open>The unbounded top-level answer is sound: @{term None} exactly certifies a negative
      infinite-capacity directed cycle of original arcs, along which the objective is unbounded below.\<close>

lemma make_acyclic_none_unbounded:
  "\<lbrakk>multigraph_inv out_arr in_arr; flow_invar f0; af_feasible b f0; vit_invar all_vertices; vit_abstract
    all_vertices \<subseteq> \<V>; make_acyclic f0 = None\<rbrakk> \<Longrightarrow> neg_inf_cycle"
  using AFF_inv_initial[of f0] af_feasible_cap[of b f0]
    AF_outer_dom[of "AF_outer_initial f0"] AF_outer_ubd_wit[of "AF_outer_initial f0"]
  by (auto simp: AF_outer_initial_def make_acyclic_def Let_def split: if_splits)

end

end
