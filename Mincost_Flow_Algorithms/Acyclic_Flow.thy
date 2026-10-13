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
  assumes "\<And> C. augpath f C \<Longrightarrow> augpath f (map erev (rev C)) \<Longrightarrow>
                distinct (map oedge C) \<Longrightarrow> fstv (hd C) = sndv (last C) \<Longrightarrow>
                set C \<subseteq> \<EE> \<Longrightarrow> False"
  shows "acyclic_flow f"
  using assms by (auto simp: acyclic_flow_def)

lemma acyclic_flowE[elim]:
  assumes "acyclic_flow f"
          "augpath f C" "augpath f (map erev (rev C))"
          "distinct (map oedge C)" "fstv (hd C) = sndv (last C)"
          "set C \<subseteq> \<EE>"
  shows P
  using assms by (auto simp: acyclic_flow_def)

lemma acyclic_flowD[dest]:
  assumes "acyclic_flow f"
          "augpath f C" "distinct (map oedge C)"
          "fstv (hd C) = sndv (last C)" "set C \<subseteq> \<EE>"
  shows "\<not> augpath f (map erev (rev C))"
  using assms by (auto simp: acyclic_flow_def)

text \<open>Reversing a residual pre-path (edge-wise \<open>erev\<close>, then list reversal) yields a
      pre-path again.\<close>

lemma prepath_erev_rev: "prepath C \<Longrightarrow> prepath (map erev (rev C))"
proof -
  assume pp: "prepath C"
  hence ne: "C \<noteq> []"
    and aw: "awalk UNIV (fstv (hd C)) (map to_vertex_pair C) (sndv (last C))"
    by(auto simp add: prepath_def)
  have rev1: "awalk UNIV (sndv (last C)) (map prod.swap (rev (map to_vertex_pair C))) (fstv (hd C))"
    by(rule awalk_UNIV_rev[OF aw])
  have mapeq: "map prod.swap (rev (map to_vertex_pair C)) = map to_vertex_pair (map erev (rev C))"
    by(simp add: rev_map to_vertex_pair_erev_swap)
  have f1: "fstv (hd (map erev (rev C))) = sndv (last C)"
    by(rule rev_prepath_fst_to_lst[OF ne])
  have f2: "sndv (last (map erev (rev C))) = fstv (hd C)"
    by(rule rev_prepath_lst_to_fst[OF ne])
  have ne2: "map erev (rev C) \<noteq> []" using ne by simp
  have "awalk UNIV (fstv (hd (map erev (rev C)))) (map to_vertex_pair (map erev (rev C)))
          (sndv (last (map erev (rev C))))"
    unfolding f1 f2 mapeq[symmetric] by(rule rev1)
  thus "prepath (map erev (rev C))"
    by(rule prepathI[OF _ ne2])
qed

text \<open>General residual bridge: under an acyclic flow there is no closed pre-path all of
      whose arcs are residually free in both directions and whose underlying edges are
      distinct.  This is the abstract source of the free-edge forest property.\<close>

lemma acyclic_no_free_closed_prepath:
  assumes acyc: "acyclic_flow f"
      and pp:   "prepath C"
      and fwd:  "\<And>e. e \<in> set C \<Longrightarrow> 0 < rcap f e"
      and bwd:  "\<And>e. e \<in> set C \<Longrightarrow> 0 < rcap f (erev e)"
      and dist: "distinct (map oedge C)"
      and clsd: "fstv (hd C) = sndv (last C)"
      and sub:  "set C \<subseteq> \<EE>"
  shows False
proof -
  have ne: "C \<noteq> []" using pp by(auto simp add: prepath_def)
  have fin: "finite (set C)" by simp
  have neS: "set C \<noteq> {}" using ne by simp
  have rc1: "0 < Rcap f (set C)" by(rule Rcap_strictI[OF fin neS fwd])
  have aug1: "augpath f C" by(rule augpathI[OF pp rc1])
  have pp2: "prepath (map erev (rev C))" by(rule prepath_erev_rev[OF pp])
  have finR: "finite (set (map erev (rev C)))" by simp
  have neR: "set (map erev (rev C)) \<noteq> {}" using ne by simp
  have rcR: "\<And>x. x \<in> set (map erev (rev C)) \<Longrightarrow> 0 < rcap f x"
  proof -
    fix x assume "x \<in> set (map erev (rev C))"
    then obtain e where "e \<in> set C" "x = erev e" by auto
    thus "0 < rcap f x" using bwd by simp
  qed
  have rc2: "0 < Rcap f (set (map erev (rev C)))" by(rule Rcap_strictI[OF finR neR rcR])
  have aug2: "augpath f (map erev (rev C))" by(rule augpathI[OF pp2 rc2])
  show False by(rule acyclic_flowE[OF acyc aug1 aug2 dist clsd sub])
qed

end





section \<open>The DFS-based acyclic-flow procedure\<close>

text \<open>State of the inner DFS-like procedure. Parallel stacks describe the current trail in the
      undirected multigraph of \emph{free} arcs: @{term af_vstack} holds the vertices and, one
      shorter, @{term af_estack} / @{term af_dstack} hold for each non-root vertex the arc it was
      entered by together with the direction that arc was traversed in (@{term True} = with the arc,
      from \<open>fst a\<close> to \<open>snd a\<close>; @{term False} = against it). @{term af_out_arr} / @{term af_in_arr}
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



text \<open>The executable specification locale: fixes the graph-iterator / array / vertex-iterator
      ADT operations and the program constants, with NO assumptions, and holds every executable
      definition of the acyclic-flow procedure.\<close>

locale acyclic_flow_impl_spec =
  fixes out_current   :: "'g \<Rightarrow> 'v \<Rightarrow> 'e" and out_has       :: "'g \<Rightarrow> 'v \<Rightarrow> bool"
    and out_move      :: "'g \<Rightarrow> 'v \<Rightarrow> 'g" and out_reset     :: "'g \<Rightarrow> 'v \<Rightarrow> 'g"
    and in_current    :: "'g \<Rightarrow> 'v \<Rightarrow> 'e" and in_has        :: "'g \<Rightarrow> 'v \<Rightarrow> bool"
    and in_move       :: "'g \<Rightarrow> 'v \<Rightarrow> 'g" and in_reset      :: "'g \<Rightarrow> 'v \<Rightarrow> 'g"
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
     out_current :: "'g \<Rightarrow> 'v \<Rightarrow> 'e" and flow_lookup :: "'farr \<Rightarrow> 'e \<Rightarrow> ('n :: linordered_idom)"
    and h :: "'n \<Rightarrow> real"
    and st_lookup :: "'sarr \<Rightarrow> 'v \<Rightarrow> vertex_state" and current_vertex :: "'vvit \<Rightarrow> 'v"
    and out_invar :: "'g \<Rightarrow> bool" and out_abstract :: "'g \<Rightarrow> 'v \<Rightarrow> 'e set"
    and out_iterated :: "'g \<Rightarrow> 'v \<Rightarrow> 'e set" and out_remaining :: "'g \<Rightarrow> 'v \<Rightarrow> 'e set"
    and in_invar :: "'g \<Rightarrow> bool" and in_abstract :: "'g \<Rightarrow> 'v \<Rightarrow> 'e set"
    and in_iterated :: "'g \<Rightarrow> 'v \<Rightarrow> 'e set" and in_remaining :: "'g \<Rightarrow> 'v \<Rightarrow> 'e set"
    and flow_invar :: "'farr \<Rightarrow> bool" and st_invar :: "'sarr \<Rightarrow> bool"
    and vit_invar :: "'vvit \<Rightarrow> bool" and vit_abstract :: "'vvit \<Rightarrow> 'v set"
    and vit_iterated :: "'vvit \<Rightarrow> 'v set" and vit_remaining :: "'vvit \<Rightarrow> 'v set" +
  assumes cap_encoding: "\<And>e. e \<in> \<E> \<Longrightarrow> (if \<u> e = \<infinity> then cap e = - 1 else \<u> e = ereal (h (cap e)))"
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

text \<open>The algorithm never inspects the (possibly infinite) capacity @{term \<open>\<u>\<close>} directly; instead it
      uses the real program capacity @{term cap}, where an infinite capacity is encoded as @{term \<open>- 1\<close>}
      (justified by \<open>cap_encoding\<close> below). Since @{term \<open>0 \<le> \<u> e\<close>}, a finite capacity is never
      @{term \<open>- 1\<close>}, so @{term \<open>- 1\<close>} unambiguously flags ``infinite''.

      An original arc is \emph{free} when its flow value is strictly positive and, if its capacity is
      finite, strictly below it; a free arc can be pushed in both directions.\<close>

definition af_arc_free :: "'farr \<Rightarrow> 'e \<Rightarrow> bool" where
  "af_arc_free fl a \<longleftrightarrow> (let f = flow_lookup fl a; c = cap a in 0 < f \<and> (c = - 1 \<or> f < c))"

text \<open>\emph{Both} directional rooms of an arc from a \emph{single} read of its flow and capacity,
      returned as a pair @{term \<open>(forward, backward)\<close>}: the forward room @{term \<open>cap a - f a\<close>} (or
      @{term \<open>- 1\<close>}, i.e.\ unbounded, when the capacity is infinite) and the backward room
      @{term \<open>f a\<close>}. Since a cancellation weighs an arc's room in both orientations, returning both at
      once avoids reading @{term flow_lookup} / @{term cap} twice per arc.\<close>

definition af_rooms :: "'farr \<Rightarrow> 'e \<Rightarrow> 'n \<times> 'n" where
  "af_rooms fl a = (let f = flow_lookup fl a; c = cap a in (if c = - 1 then - 1 else c - f, f))"

text \<open>Marginal cost of pushing one unit along an arc in a direction.\<close>

definition af_delta_cost :: "'e \<Rightarrow> bool \<Rightarrow> 'n" where
  "af_delta_cost a dir = (if dir then cost a else - cost a)"

text \<open>Minimum that treats @{term \<open>- 1\<close>} as ``no bound'' (unbounded room), so it is the neutral element.\<close>

definition af_min :: "'n \<Rightarrow> 'n \<Rightarrow> 'n" where
  "af_min x y = (if x = - 1 then y else if y = - 1 then x else min x y)"

text \<open>Push @{term \<gamma>} on one arc and return the updated flow \emph{paired with the new flow value}, so
      a caller can test saturation without reading the value back.\<close>

definition af_push_arc :: "'n \<Rightarrow> 'e \<Rightarrow> bool \<Rightarrow> 'farr \<Rightarrow> 'farr \<times> 'n" where
  "af_push_arc \<gamma> a dir fl = (let f = flow_lookup fl a + (if dir then \<gamma> else - \<gamma>) in (flow_upd fl a f, f))"

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

fun af_scan :: "'farr \<Rightarrow> 'v \<Rightarrow> 'v list \<Rightarrow> 'e list \<Rightarrow> bool list \<Rightarrow> 'n \<times> 'n \<times> 'n \<Rightarrow> 'n \<times> 'n \<times> 'n" where
  "af_scan fl x (_ # v1 # vs) (a # es) (d # ds) (k, ra, rf) =
     (let (up, dn) = af_rooms fl a;
          acc = (k + af_delta_cost a d, af_min (if d then up else dn) ra, af_min (if d then dn else up) rf)
      in if v1 = x then acc else af_scan fl x (v1 # vs) es ds acc)"
| "af_scan fl x _ _ _ acc = acc"

text \<open>Fused second pass -- push @{term \<gamma>} around the same cycle \emph{and} locate the bottleneck. Each
      cycle arc is pushed once (negating the tag via @{term \<open>d \<noteq> flip\<close>} when flipped); right after the
      push the arc is tested for saturation, and the pass returns the flow paired with the \emph{drop
      count} @{term \<open>m'\<close>} = one more than the index of the \emph{deepest} arc that saturated, or
      @{term 0} if none did (only the closing arc). This subsumes the old separate bottleneck-locate
      scan.\<close>

fun af_push :: "'n \<Rightarrow> 'v \<Rightarrow> 'v list \<Rightarrow> 'e list \<Rightarrow> bool list \<Rightarrow> bool \<Rightarrow> 'farr \<Rightarrow> 'farr \<times> nat" where
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
        \item if the walk cost is \emph{zero} and the \emph{other} direction is finite (@{term \<open>rf \<noteq> - 1\<close>}),
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

text \<open>Fused truncation clean-up: over the first @{term n} (= @{term \<open>m'\<close>}) vertices of the stack -- the
      ones dropped by truncate-to-bottleneck -- in \emph{one} walk both set the vertex back to
      @{term Unseen} (@{term st_upd}) and reset its iterators (@{const af_reset}). Merges what were two
      separate bounded folds. The surviving endpoint (at index @{term \<open>m'\<close>}) is not touched -- it
      resumes.\<close>

fun af_reset_unsee_seg where
  "af_reset_unsee_seg (Suc n) (v # vs) st =
     af_reset_unsee_seg n vs (af_reset v (st \<lparr> af_state := st_upd (af_state st) v Unseen \<rparr>))"
| "af_reset_unsee_seg _ _ st = st"

text \<open>Cost-directed normalisation of a self-loop arc @{term a} (@{term \<open>fst a = snd a\<close>}).  A self-loop
      carries no balance (its two endpoints coincide), so its flow may be driven to whichever bound its
      unit cost prefers without disturbing feasibility: a negative-cost loop is filled to its capacity
      @{term \<open>cap a\<close>} (a negative-cost loop of \emph{infinite} capacity certifies the instance unbounded),
      and \<^emph>\<open>every non-negative-cost loop is emptied\<close>, flow set to @{term 0}.  Emptying a zero-cost loop is
      cost-neutral and keeps the flow acyclic, so this needs no residual-room test --- the positive- and
      zero-cost cases coincide.  Unlike the old @{const af_cancel_seg} on-empty-segment treatment this
      fires on \emph{every} scanned self-loop, not only the free ones, so the final flow is
      self-loop-normalised (\<open>\<c> a \<ge> 0 \<Longrightarrow> flow 0\<close>, \<open>\<c> a < 0 \<Longrightarrow> flow cap\<close>) regardless of the starting bound.\<close>

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
                (let (fl, m', ubd) = af_cancel_seg up dn x (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st)
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
      arc (\<open>T-out\<close>), advance along an ingoing one (\<open>T-in\<close>), or backtrack (\<open>T-pop\<close>) -- and one return
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
      negative infinite-capacity free cycle was found), otherwise @{term \<open>Some f'\<close>} with @{term \<open>f'\<close>}
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

lemma cost_neg_bridge:  "a \<in> \<E> \<Longrightarrow> (cost a < 0) = (\<c> a < 0)" using cost_encoding by simp
lemma cost_nonneg_bridge: "a \<in> \<E> \<Longrightarrow> (0 \<le> cost a) = (0 \<le> \<c> a)" using cost_encoding by simp
lemma cost_pos_bridge:  "a \<in> \<E> \<Longrightarrow> (0 < cost a) = (0 < \<c> a)" using cost_encoding by simp
lemma cost_h: "a \<in> \<E> \<Longrightarrow> h (cost a) = \<c> a" using cost_encoding by simp

lemma cap_infinite_bridge: "a \<in> \<E> \<Longrightarrow> (cap a = - 1) = (\<u> a = \<infinity>)"
proof -
  assume a: "a \<in> \<E>"
  show ?thesis
  proof (cases "\<u> a = \<infinity>")
    case True thus ?thesis using cap_encoding[OF a] by simp
  next
    case False
    hence "\<u> a = ereal (h (cap a))" using cap_encoding[OF a] by simp
    hence "0 \<le> h (cap a)" using u_non_neg[of a] by (simp add: zero_ereal_def)
    hence "cap a \<noteq> - 1" by simp
    thus ?thesis using False by simp
  qed
qed
lemma cap_finite_h: "\<lbrakk>a \<in> \<E>; \<u> a \<noteq> \<infinity>\<rbrakk> \<Longrightarrow> ereal (h (cap a)) = \<u> a"
  using cap_encoding[of a] by (auto split: if_splits)

definition "multigraph_inv oa ia \<longleftrightarrow> out_graph_inv oa \<and> in_graph_inv ia"

lemma af_handle_real:
  assumes "a \<in> \<E>"
  shows "af_handle st a dir =
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
                (let (fl, m', ubd) = af_cancel_seg up dn x (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st)
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
  by (simp only: af_handle_def fst_exec_eq[OF assms] snd_exec_eq[OF assms])


lemma AF_DFS_call_1_conds[call_cond_elims]:
  "AF_DFS_call_1_conds st \<Longrightarrow>
   \<lbrakk>\<lbrakk>\<not> af_unbounded st; \<exists>v vs. af_vstack st = v # vs;
     out_has (af_out_arr st) (hd (af_vstack st))\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: AF_DFS_call_1_conds_def split: list.splits)

lemma AF_DFS_call_2_conds[call_cond_elims]:
  "AF_DFS_call_2_conds st \<Longrightarrow>
   \<lbrakk>\<lbrakk>\<not> af_unbounded st; \<exists>v vs. af_vstack st = v # vs;
     \<not> out_has (af_out_arr st) (hd (af_vstack st));
     in_has (af_in_arr st) (hd (af_vstack st))\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: AF_DFS_call_2_conds_def split: list.splits)

lemma AF_DFS_call_3_conds[call_cond_elims]:
  "AF_DFS_call_3_conds st \<Longrightarrow>
   \<lbrakk>\<lbrakk>\<not> af_unbounded st; \<exists>v vs. af_vstack st = v # vs;
     \<not> out_has (af_out_arr st) (hd (af_vstack st));
     \<not> in_has (af_in_arr st) (hd (af_vstack st))\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: AF_DFS_call_3_conds_def split: list.splits)

lemma AF_DFS_ret_conds[call_cond_elims]:
  "AF_DFS_ret_conds st \<Longrightarrow> \<lbrakk>\<lbrakk>af_unbounded st \<or> af_vstack st = []\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: AF_DFS_ret_conds_def split: list.splits)

lemma AF_DFS_ret_condsI[call_cond_intros]:
  "\<lbrakk>af_unbounded st \<or> af_vstack st = []\<rbrakk> \<Longrightarrow> AF_DFS_ret_conds st"
  by (auto simp: AF_DFS_ret_conds_def split: list.splits)

lemma AF_DFS_cases:
  assumes "AF_DFS_call_1_conds st \<Longrightarrow> P"
      and "AF_DFS_call_2_conds st \<Longrightarrow> P"
      and "AF_DFS_call_3_conds st \<Longrightarrow> P"
      and "AF_DFS_ret_conds st \<Longrightarrow> P"
  shows "P"
proof-
  have "AF_DFS_call_1_conds st \<or> AF_DFS_call_2_conds st \<or>
        AF_DFS_call_3_conds st \<or> AF_DFS_ret_conds st"
    by (auto simp add: AF_DFS_call_1_conds_def AF_DFS_call_2_conds_def
                       AF_DFS_call_3_conds_def AF_DFS_ret_conds_def
             split: list.split_asm)
  then show ?thesis using assms by auto
qed

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
  "AF_outer_call_1_conds st \<Longrightarrow>
   \<lbrakk>\<lbrakk>\<not> aff_unbounded st; has_vertex (aff_vit st);
     st_lookup (aff_state st) (current_vertex (aff_vit st)) \<noteq> Unseen\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: AF_outer_call_1_conds_def)

lemma AF_outer_call_2_conds[call_cond_elims]:
  "AF_outer_call_2_conds st \<Longrightarrow>
   \<lbrakk>\<lbrakk>\<not> aff_unbounded st; has_vertex (aff_vit st);
     st_lookup (aff_state st) (current_vertex (aff_vit st)) = Unseen\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: AF_outer_call_2_conds_def)

lemma AF_outer_ret_conds[call_cond_elims]:
  "AF_outer_ret_conds st \<Longrightarrow> \<lbrakk>\<lbrakk>aff_unbounded st \<or> \<not> has_vertex (aff_vit st)\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: AF_outer_ret_conds_def)

lemma AF_outer_cases:
  assumes "AF_outer_call_1_conds st \<Longrightarrow> P"
      and "AF_outer_call_2_conds st \<Longrightarrow> P"
      and "AF_outer_ret_conds st \<Longrightarrow> P"
  shows "P"
proof-
  have "AF_outer_call_1_conds st \<or> AF_outer_call_2_conds st \<or> AF_outer_ret_conds st"
    by (auto simp add: AF_outer_call_1_conds_def AF_outer_call_2_conds_def AF_outer_ret_conds_def)
  then show ?thesis using assms by auto
qed

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
  assumes ae: "a \<in> \<E>" and fi: "flow_invar (af_flow st)"
  shows "flow_invar (af_flow (af_selfloop_handle st a))"
  using af_selfloop_handle_flow_cases[of st a] fi flow_upd_invar[OF fi ae] by auto

lemma af_selfloop_handle_unbounded:
  assumes ae: "a \<in> \<E>"
  shows "af_unbounded (af_selfloop_handle st a) = (af_unbounded st \<or> (\<c> a < 0 \<and> cap a = - 1))"
  by (auto simp: af_selfloop_handle_def Let_def cost_neg_bridge[OF ae] split: if_splits prod.splits)

lemma af_selfloop_handle_flow_off:
  assumes ae: "a \<in> \<E>" and fi: "flow_invar (af_flow st)" and ne: "b \<noteq> a"
  shows "flow_lookup (af_flow (af_selfloop_handle st a)) b = flow_lookup (af_flow st) b"
  using af_selfloop_handle_flow_cases[of st a] ne
        flow_array.fixed_univ_map_upd[OF fi ae] by auto

lemma af_selfloop_handle_notfree:
  assumes ae: "a \<in> \<E>" and fi: "flow_invar (af_flow st)" and nub: "\<not> af_unbounded (af_selfloop_handle st a)"
  shows "\<not> af_arc_free (af_flow (af_selfloop_handle st a)) a"
proof (cases "\<c> a < 0")
  case True
  hence cne: "cap a \<noteq> - 1" using nub by (simp add: af_selfloop_handle_unbounded[OF ae])
  have "flow_lookup (af_flow (af_selfloop_handle st a)) a = cap a"
    using True cne ae
    by (auto simp: af_selfloop_handle_def Let_def cost_neg_bridge[OF ae] flow_array.fixed_univ_map_upd[OF fi ae] split: if_splits)
  thus ?thesis by (simp add: af_arc_free_def Let_def)
next
  case False
  hence "flow_lookup (af_flow (af_selfloop_handle st a)) a = 0"
    using ae by (auto simp: af_selfloop_handle_def Let_def cost_neg_bridge[OF ae] flow_array.fixed_univ_map_upd[OF fi ae] split: if_splits)
  thus ?thesis by (simp add: af_arc_free_def Let_def)
qed

lemma af_selfloop_handle_norm:
  assumes ae: "a \<in> \<E>" and fi: "flow_invar (af_flow st)" and nub: "\<not> af_unbounded (af_selfloop_handle st a)"
  shows "(0 \<le> \<c> a \<longrightarrow> flow_lookup (af_flow (af_selfloop_handle st a)) a = 0)
       \<and> (\<c> a < 0 \<longrightarrow> cap a \<noteq> - 1 \<and> flow_lookup (af_flow (af_selfloop_handle st a)) a = cap a)"
proof (rule conjI; rule impI)
  assume "0 \<le> \<c> a"
  thus "flow_lookup (af_flow (af_selfloop_handle st a)) a = 0"
    using ae by (auto simp: af_selfloop_handle_def Let_def cost_neg_bridge[OF ae] flow_array.fixed_univ_map_upd[OF fi ae] split: if_splits)
next
  assume neg: "\<c> a < 0"
  have cne: "cap a \<noteq> - 1" using neg nub by (simp add: af_selfloop_handle_unbounded[OF ae])
  have "flow_lookup (af_flow (af_selfloop_handle st a)) a = cap a"
    using neg cne ae by (auto simp: af_selfloop_handle_def Let_def cost_neg_bridge[OF ae] flow_array.fixed_univ_map_upd[OF fi ae] split: if_splits)
  thus "cap a \<noteq> - 1 \<and> flow_lookup (af_flow (af_selfloop_handle st a)) a = cap a" using cne by simp
qed

lemma af_selfloop_handle_free_imp_flow_id:
  assumes ae: "a \<in> \<E>" and fi: "flow_invar (af_flow st)"
    and fr: "af_arc_free (af_flow (af_selfloop_handle st a)) a"
  shows "af_flow (af_selfloop_handle st a) = af_flow st"
proof -
  have n0: "\<not> af_arc_free (flow_upd (af_flow st) a 0) a"
    using flow_array.fixed_univ_map_upd[OF fi ae] by (simp add: af_arc_free_def Let_def)
  have ncap: "\<not> af_arc_free (flow_upd (af_flow st) a (cap a)) a"
    using flow_array.fixed_univ_map_upd[OF fi ae] by (simp add: af_arc_free_def Let_def)
  show ?thesis using fr n0 ncap af_selfloop_handle_flow_cases[of st a] by auto
qed

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
  "AF_invar_1 st \<Longrightarrow>
     (\<lbrakk>flow_invar (af_flow st); st_invar (af_state st);
       out_invar (af_out_arr st); in_invar (af_in_arr st)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: AF_invar_1_def)

lemma AF_invar_1_intro[invar_props_intros]:
  "\<lbrakk>flow_invar (af_flow st); st_invar (af_state st);
    out_invar (af_out_arr st); in_invar (af_in_arr st)\<rbrakk> \<Longrightarrow> AF_invar_1 st"
  by (auto simp: AF_invar_1_def)

text \<open>A cancellation only ever pushes flow (through @{const af_push} / @{const af_push_arc}), so it
      preserves @{term flow_invar}.\<close>

lemma af_push_arc_flow_invar:
  "a \<in> \<E> \<Longrightarrow> 
  af_push_arc \<gamma> a dir fl = (fl', f') \<Longrightarrow> flow_invar fl \<Longrightarrow> flow_invar fl'"
  by (auto simp: af_push_arc_def Let_def flow_upd_invar)

lemma af_push_flow_invar:
  "set es \<subseteq> \<E> \<Longrightarrow> 
   af_push \<gamma> x vs es ds flip fl = (fl', m') \<Longrightarrow> flow_invar fl \<Longrightarrow> flow_invar fl'"
  by (induction \<gamma> x vs es ds flip fl arbitrary: fl' m' rule: af_push.induct)
     (auto split: prod.splits if_splits dest: af_push_arc_flow_invar)

lemma af_cancel_seg_flow_invar:
  "\<lbrakk>set es \<subseteq> \<E>; a \<in> \<E>\<rbrakk> \<Longrightarrow> 
   af_cancel_seg up dn x vs es ds a dir fl = (fl'', m', ubd) \<Longrightarrow> flow_invar fl \<Longrightarrow> flow_invar fl''"
  by (auto simp: af_cancel_seg_def Let_def split: prod.splits if_splits
           dest: af_push_flow_invar af_push_arc_flow_invar)

text \<open>A reset copies pristine iterators via @{term arr_upd}, and the fused truncation clean-up also
      re-marks the dropped vertices @{term Unseen} via @{term st_upd}; both preserve the invariants.\<close>

lemma af_reset_state_upd_invar_1:
  "v \<in> \<V> \<Longrightarrow> AF_invar_1 st \<Longrightarrow> AF_invar_1 (af_reset v (st \<lparr>af_state := st_upd (af_state st) v Unseen\<rparr>))"
  by (auto simp: AF_invar_1_def af_reset_def st_upd_invar intro: out_reset_invar in_reset_invar)

lemma af_reset_unsee_seg_invar_1:
  "set vs \<subseteq> \<V> \<Longrightarrow> AF_invar_1 st \<Longrightarrow> AF_invar_1 (af_reset_unsee_seg n vs st)"
  by (induction n vs st rule: af_reset_unsee_seg.induct) (auto intro: af_reset_state_upd_invar_1)

text \<open>Record-update helpers, one per shape of @{const af_handle} branch.\<close>

lemma AF_invar_1_out_advance:
  "v \<in> \<V> \<Longrightarrow> AF_invar_1 st \<Longrightarrow> AF_invar_1 (st \<lparr>af_out_arr := out_move (af_out_arr st) v\<rparr>)"
  by (auto simp: AF_invar_1_def intro: out_move_invar)

lemma AF_invar_1_in_advance:
  "v \<in> \<V> \<Longrightarrow> AF_invar_1 st \<Longrightarrow> AF_invar_1 (st \<lparr>af_in_arr := in_move (af_in_arr st) v\<rparr>)"
  by (auto simp: AF_invar_1_def intro: in_move_invar)

lemma af_handle_invar_1:
  assumes "AF_invar_1 st" and ae: "a \<in> \<E>"
    and estE: "set (af_estack st) \<subseteq> \<E>" and aV: "set (af_vstack st) \<subseteq> \<V>"
  shows "AF_invar_1 (af_handle st a dir)"
proof -
  show ?thesis
  proof (cases "fst_exec a = snd_exec a")
    case selfl: True
    have fi: "flow_invar (af_flow st)" using assms(1) by (simp add: AF_invar_1_def)
    have "af_handle st a dir = af_selfloop_handle st a" using selfl by (simp add: af_handle_def)
    thus ?thesis using assms(1) af_selfloop_handle_flow_invar[OF ae fi] by (auto simp: AF_invar_1_def)
  next
    case selfloop: False
    obtain up dn where updn: "af_rooms (af_flow st) a = (up, dn)"
      by (cases "af_rooms (af_flow st) a") auto
    show ?thesis
    proof (cases "0 < dn \<and> (up = - 1 \<or> 0 < up)")
      case False thus ?thesis using assms(1) updn selfloop by (simp add: af_handle_def Let_def)
    next
      case guard: True
      show ?thesis
      proof (cases "af_estack st \<noteq> [] \<and> a = hd (af_estack st)")
        case True thus ?thesis using assms(1) updn guard selfloop by (simp add: af_handle_def Let_def)
      next
        case parent: False
        show ?thesis
        proof (cases "st_lookup (af_state st) (if dir then snd_exec a else fst_exec a)")
          case Unseen
          have wV: "(if dir then snd_exec a else fst_exec a) \<in> \<V>"
            using ae fst_E_V[OF ae] snd_E_V[OF ae] by (cases dir) (auto simp: snd_exec_eq[OF ae] fst_exec_eq[OF ae])
          have "af_handle st a dir = st\<lparr>af_vstack := (if dir then snd_exec a else fst_exec a) # af_vstack st,
              af_state := st_upd (af_state st) (if dir then snd_exec a else fst_exec a) OnStack,
              af_estack := a # af_estack st, af_dstack := dir # af_dstack st\<rparr>"
            using updn guard selfloop parent Unseen by (auto simp: af_handle_def Let_def)
          thus ?thesis using assms(1) wV by (auto simp: AF_invar_1_def st_upd_invar)
        next
          case OnStack
          obtain fl m' ubd where c: "af_cancel_seg up dn (if dir then snd_exec a else fst_exec a)
              (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) = (fl, m', ubd)"
            by (metis prod_cases3)
          have fi: "flow_invar fl" using af_cancel_seg_flow_invar[OF estE ae c] assms(1) by (auto simp: AF_invar_1_def)
          show ?thesis
          proof (cases ubd)
            case True
            have "af_handle st a dir = st\<lparr>af_unbounded := True\<rparr>"
              using updn guard selfloop parent OnStack c True by (auto simp: af_handle_def Let_def)
            thus ?thesis using assms by (simp add: AF_invar_1_def)
          next
            case False
            have red: "af_handle st a dir = af_reset_unsee_seg m' (af_vstack st)
                (st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st),
                    af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>)"
              using updn guard selfloop parent OnStack c False by (auto simp: af_handle_def Let_def)
            have "AF_invar_1 (st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st),
                    af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>)"
              using assms fi by (auto simp: AF_invar_1_def)
            hence "AF_invar_1 (af_reset_unsee_seg m' (af_vstack st)
                (st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st),
                    af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>))"
              by (rule af_reset_unsee_seg_invar_1[OF aV])
            thus ?thesis using red by simp
          qed
        next
          case Finished
          thus ?thesis using assms updn guard selfloop parent by (auto simp: af_handle_def Let_def)
        qed
      qed
    qed
  qed
qed

text \<open>The single-step preservation of Themes A and B now depends on the range invariants (an updated
      edge/vertex must lie in the edge/vertex set for the length-preserving arrays to register the write),
      so Themes A and B are preserved jointly. The combined single-step lemmas \<^verbatim>\<open>AF_invar_12_holds_1/2/3\<close>
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
  "AF_invar_2 st \<Longrightarrow>
     (\<lbrakk>distinct (af_vstack st);
       (af_vstack st = [] \<and> af_estack st = [] \<and> af_dstack st = []) \<or>
       (Suc (length (af_estack st)) = length (af_vstack st) \<and>
        length (af_dstack st) = length (af_estack st));
       \<And>v. v \<in> \<V> \<Longrightarrow> (st_lookup (af_state st) v = OnStack) = (v \<in> set (af_vstack st))\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: AF_invar_2_def)

lemma AF_invar_2I:
  "\<lbrakk>distinct (af_vstack st);
    (af_vstack st = [] \<and> af_estack st = [] \<and> af_dstack st = []) \<or>
    (Suc (length (af_estack st)) = length (af_vstack st) \<and>
     length (af_dstack st) = length (af_estack st));
    \<And>v. v \<in> \<V> \<Longrightarrow> (st_lookup (af_state st) v = OnStack) = (v \<in> set (af_vstack st))\<rbrakk> \<Longrightarrow> AF_invar_2 st"
  by (auto simp: AF_invar_2_def)

text \<open>Push: the new leaf @{term x} was @{term Unseen}, hence not yet on the stack.\<close>

lemma AF_invar_2_push:
  assumes "AF_invar_1 st" "AF_invar_2 st" "af_vstack st \<noteq> []" "st_lookup (af_state st) x = Unseen"
    and xV: "x \<in> \<V>"
  shows "AF_invar_2 (st\<lparr>af_vstack := x # af_vstack st, af_state := st_upd (af_state st) x OnStack,
                        af_estack := a # af_estack st, af_dstack := dir # af_dstack st\<rparr>)"
proof -
  from assms(1) have si: "st_invar (af_state st)" by (auto simp: AF_invar_1_def)
  from assms(2) xV have "(st_lookup (af_state st) x = OnStack) = (x \<in> set (af_vstack st))"
    by (auto simp: AF_invar_2_def)
  with assms(4) have xni: "x \<notin> set (af_vstack st)" by auto
  from assms(2,3) xni show ?thesis
    by (auto simp: AF_invar_2_def state_arr.fixed_univ_map_upd[OF si xV])
qed

text \<open>Back-edge truncate-and-reset: drop @{term \<open>m'\<close>} vertices (bounded, so the stack stays non-empty)
      and re-mark exactly those @{term Unseen}. This is the load-bearing case; distinctness turns the
      @{term take}/@{term drop} split of the stack into the restored @{term OnStack} correspondence.\<close>

lemma AF_invar_2_backedge:
  assumes "AF_invar_1 st" "AF_invar_2 st" "af_vstack st \<noteq> []"
    "af_cancel_seg up dn x (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) = (fl, m', ubd)"
    and vV: "set (af_vstack st) \<subseteq> \<V>"
  shows "AF_invar_2 (af_reset_unsee_seg m' (af_vstack st)
           (st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st),
               af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>))"
proof -
  from assms(1) have si: "st_invar (af_state st)" by (auto simp: AF_invar_1_def)
  from assms(2,3) have d: "distinct (af_vstack st)"
    and cpl: "\<And>w. w \<in> \<V> \<Longrightarrow> (st_lookup (af_state st) w = OnStack) = (w \<in> set (af_vstack st))"
    and le: "Suc (length (af_estack st)) = length (af_vstack st)"
            "length (af_dstack st) = length (af_estack st)"
    by (auto simp: AF_invar_2_def)
  from assms(4) have mle: "m' \<le> length (af_estack st)" by (rule af_cancel_seg_drop_bound)
  define inner where "inner = st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st),
      af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>"
  have si_inner: "st_invar (af_state inner)" using si by (simp add: inner_def)
  have est: "af_estack (af_reset_unsee_seg m' (af_vstack st) inner) = drop m' (af_estack st)"
    by (simp add: inner_def)
  have dst: "af_dstack (af_reset_unsee_seg m' (af_vstack st) inner) = drop m' (af_dstack st)"
    by (simp add: inner_def)
  have vst: "af_vstack (af_reset_unsee_seg m' (af_vstack st) inner) = drop m' (af_vstack st)"
    by (simp add: inner_def)
  have stt: "\<And>w. st_lookup (af_state (af_reset_unsee_seg m' (af_vstack st) inner)) w =
                 (if w \<in> set (take m' (af_vstack st)) then Unseen else st_lookup (af_state st) w)"
    using af_reset_unsee_seg_state[OF vV si_inner] by (simp add: inner_def)
  have setd: "set (af_vstack st) = set (take m' (af_vstack st)) \<union> set (drop m' (af_vstack st))"
    by (metis append_take_drop_id set_append)
  have disj: "set (take m' (af_vstack st)) \<inter> set (drop m' (af_vstack st)) = {}"
    using d by (metis append_take_drop_id distinct_append)
  have "AF_invar_2 (af_reset_unsee_seg m' (af_vstack st) inner)"
    apply (rule AF_invar_2I)
    subgoal using d by (simp add: inner_def)
    subgoal using vst est dst le mle by (auto simp: Suc_diff_le)
    subgoal for w using stt cpl setd disj vst by (auto split: if_splits)
    done
  thus ?thesis by (simp only: inner_def)
qed

lemma af_handle_invar_2:
  assumes "AF_invar_1 st" "AF_invar_2 st" "af_vstack st \<noteq> []"
    and ae: "a \<in> \<E>" and aV: "set (af_vstack st) \<subseteq> \<V>"
  shows "AF_invar_2 (af_handle st a dir)"
proof -
  show ?thesis
  proof (cases "fst_exec a = snd_exec a")
    case True
    have "af_handle st a dir = af_selfloop_handle st a" using True by (simp add: af_handle_def)
    thus ?thesis using assms(2) by (simp add: AF_invar_2_def)
  next
    case selfloop: False
    obtain up dn where updn: "af_rooms (af_flow st) a = (up, dn)"
      by (cases "af_rooms (af_flow st) a") auto
    show ?thesis
    proof (cases "0 < dn \<and> (up = - 1 \<or> 0 < up)")
      case False thus ?thesis using assms(2) updn selfloop by (simp add: af_handle_def Let_def)
    next
      case guard: True
      show ?thesis
      proof (cases "af_estack st \<noteq> [] \<and> a = hd (af_estack st)")
        case True thus ?thesis using assms(2) updn guard selfloop by (simp add: af_handle_def Let_def)
      next
        case parent: False
        show ?thesis
        proof (cases "st_lookup (af_state st) (if dir then snd_exec a else fst_exec a)")
          case Unseen
          have wV: "(if dir then snd_exec a else fst_exec a) \<in> \<V>"
            using ae fst_E_V[OF ae] snd_E_V[OF ae] by (cases dir) (auto simp: snd_exec_eq[OF ae] fst_exec_eq[OF ae])
          have push: "AF_invar_2 (st\<lparr>af_vstack := (if dir then snd_exec a else fst_exec a) # af_vstack st,
              af_state := st_upd (af_state st) (if dir then snd_exec a else fst_exec a) OnStack,
              af_estack := a # af_estack st, af_dstack := dir # af_dstack st\<rparr>)"
            using assms(1,2,3) Unseen wV by (rule AF_invar_2_push)
          from updn guard selfloop parent Unseen push show ?thesis
            by (auto simp: af_handle_def Let_def)
        next
          case OnStack
          obtain fl m' ubd where c: "af_cancel_seg up dn (if dir then snd_exec a else fst_exec a)
              (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) = (fl, m', ubd)"
            by (metis prod_cases3)
          show ?thesis
          proof (cases ubd)
            case True
            have "af_handle st a dir = st\<lparr>af_unbounded := True\<rparr>"
              using updn guard selfloop parent OnStack c True by (auto simp: af_handle_def Let_def)
            thus ?thesis using assms(2) by (simp add: AF_invar_2_def)
          next
            case False
            have be: "AF_invar_2 (af_reset_unsee_seg m' (af_vstack st)
                (st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st),
                    af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>))"
              using assms(1,2,3) c aV by (rule AF_invar_2_backedge)
            have red: "af_handle st a dir = af_reset_unsee_seg m' (af_vstack st)
                (st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st),
                    af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>)"
              using updn guard selfloop parent OnStack c False by (auto simp: af_handle_def Let_def)
            from red be show ?thesis by simp
          qed
        next
          case Finished
          thus ?thesis using assms(2) updn guard selfloop parent
            by (auto simp: af_handle_def Let_def)
        qed
      qed
    qed
  qed
qed

lemma AF_invar_2_out_arr[simp]: "AF_invar_2 (st\<lparr>af_out_arr := X\<rparr>) = AF_invar_2 st"
  by (simp add: AF_invar_2_def)

lemma AF_invar_2_in_arr[simp]: "AF_invar_2 (st\<lparr>af_in_arr := X\<rparr>) = AF_invar_2 st"
  by (simp add: AF_invar_2_def)

text \<open>The single-step lifts of Theme B to the three DFS steps, together with those of Theme A, are the
      combined lemmas \<^verbatim>\<open>AF_invar_12_holds_1/2/3\<close> proved below (Theme E1 first supplies the fact that the
      scanned arc lies in the edge set).\<close>


subsection \<open>Theme D --- the flow (structural core)\<close>

text \<open>A cancellation touches the flow only on the arcs it pushes: the walk arcs @{term es} (through
      @{const af_push}) and the closing arc @{term a} (through @{const af_push_arc}). Every arc off the
      walk keeps its flow value, hence keeps its free/blocked status. This is the ``arcs off the walk
      are untouched'' half of D2 (the free set only shrinks).\<close>

lemma af_push_flow_off:
  "set es \<subseteq> \<E> \<Longrightarrow> flow_invar fl \<Longrightarrow> b \<notin> set es \<Longrightarrow> af_push \<gamma> x vs es ds flip fl = (fl', m') \<Longrightarrow>
     flow_lookup fl' b = flow_lookup fl b"
  by (induction \<gamma> x vs es ds flip fl arbitrary: fl' m' rule: af_push.induct)
     (auto simp: af_push_arc_def Let_def flow_array.fixed_univ_map_upd flow_upd_invar
           split: prod.splits if_splits)

lemma af_push_arc_flow_off:
  "a \<in> \<E> \<Longrightarrow> flow_invar fl \<Longrightarrow> b \<noteq> a \<Longrightarrow> af_push_arc \<gamma> a dir fl = (fl', f') \<Longrightarrow>
     flow_lookup fl' b = flow_lookup fl b"
  by (auto simp: af_push_arc_def Let_def flow_array.fixed_univ_map_upd)

lemma af_cancel_seg_flow_off:
  assumes esE: "set es \<subseteq> \<E>" and ae: "a \<in> \<E>"
    and a1: "flow_invar fl" and a2: "b \<notin> set es" and a3: "b \<noteq> a"
    and a4: "af_cancel_seg up dn x vs es ds a dir fl = (fl'', m', ubd)"
  shows "flow_lookup fl'' b = flow_lookup fl b"
proof -
  obtain k ra rf where sc: "af_scan fl x vs es ds
      (af_delta_cost a dir, if dir then up else dn, if dir then dn else up) = (k, ra, rf)"
    by (metis prod_cases3)
  consider (fin) "(if 0 < k then rf else ra) \<noteq> - 1"
    | (sw) "\<not> (if 0 < k then rf else ra) \<noteq> - 1" "k = 0 \<and> rf \<noteq> - 1"
    | (ubd) "\<not> (if 0 < k then rf else ra) \<noteq> - 1" "\<not> (k = 0 \<and> rf \<noteq> - 1)"
    by blast
  then show ?thesis
  proof cases
    case fin
    obtain fl' r where p: "af_push (if 0 < k then rf else ra) x vs es ds (0 < k) fl = (fl', r)"
      by fastforce
    obtain fl2 f2 where pa: "af_push_arc (if 0 < k then rf else ra) a (dir \<noteq> (0 < k)) fl' = (fl2, f2)"
      by fastforce
    from a4 sc fin have e: "fl'' = fl2" using p pa by (auto simp: af_cancel_seg_def Let_def)
    have fi': "flow_invar fl'" by (rule af_push_flow_invar[OF esE p a1])
    have "flow_lookup fl' b = flow_lookup fl b" by (rule af_push_flow_off[OF esE a1 a2 p])
    moreover have "flow_lookup fl2 b = flow_lookup fl' b" by (rule af_push_arc_flow_off[OF ae fi' a3 pa])
    ultimately show ?thesis using e by simp
  next
    case sw
    obtain fl' r where p: "af_push rf x vs es ds True fl = (fl', r)" by fastforce
    obtain fl2 f2 where pa: "af_push_arc rf a (dir \<noteq> True) fl' = (fl2, f2)" by fastforce
    from a4 sc sw have e: "fl'' = fl2" using p pa by (auto simp: af_cancel_seg_def Let_def)
    have fi': "flow_invar fl'" by (rule af_push_flow_invar[OF esE p a1])
    have "flow_lookup fl' b = flow_lookup fl b" by (rule af_push_flow_off[OF esE a1 a2 p])
    moreover have "flow_lookup fl2 b = flow_lookup fl' b" by (rule af_push_arc_flow_off[OF ae fi' a3 pa])
    ultimately show ?thesis using e by simp
  next
    case ubd
    from a4 sc ubd have "fl'' = fl" by (auto simp: af_cancel_seg_def Let_def)
    thus ?thesis by simp
  qed
qed

text \<open>Consequently an off-walk arc keeps its free/blocked status across a cancellation: the free set
      does not grow there.\<close>

lemma af_cancel_seg_arc_free_off:
  "set es \<subseteq> \<E> \<Longrightarrow> a \<in> \<E> \<Longrightarrow> flow_invar fl \<Longrightarrow> b \<notin> set es \<Longrightarrow> b \<noteq> a \<Longrightarrow>
     af_cancel_seg up dn x vs es ds a dir fl = (fl'', m', ubd) \<Longrightarrow>
     af_arc_free fl'' b = af_arc_free fl b"
  by (auto simp: af_arc_free_def dest: af_cancel_seg_flow_off)

text \<open>Building blocks for the on-walk (feasibility / bottleneck) half of Theme D. One push shifts its
      arc's flow by exactly \<open>\<plusminus>\<gamma>\<close>; @{const af_min} is bounded above by any finite argument (it
      treats @{term \<open>- 1\<close>} as ``unbounded''), so the scanned bottleneck is @{text "\<le>"} every finite room.\<close>

lemma af_push_arc_at:
  "a \<in> \<E> \<Longrightarrow> flow_invar fl \<Longrightarrow> af_push_arc \<gamma> a dir fl = (fl', f') \<Longrightarrow>
     flow_lookup fl' a = f' \<and> f' = flow_lookup fl a + (if dir then \<gamma> else - \<gamma>)"
  by (auto simp: af_push_arc_def Let_def flow_array.fixed_univ_map_upd)

lemma af_min_le1: "x \<noteq> - 1 \<Longrightarrow> af_min x y \<le> x" by (auto simp: af_min_def)

text \<open>Feasibility of the flow (over the multigraph @{term \<E>}): every arc's value is between @{term 0}
      and its capacity (with @{term \<open>- 1\<close>} = infinite meaning ``no upper bound''). A single push keeps its
      arc feasible provided the push amount fits the room in the chosen direction --- the per-arc core
      of Theme D1. (The full walk-level statement additionally needs @{const af_scan}'s bottleneck to
      lower-bound every room, whose sentinel @{term \<open>- 1\<close>} is only reachable for infinite-capacity
      arcs; see the finite-capacity discussion in the design notes.)\<close>

definition "af_cap_feasible fl \<longleftrightarrow>
   (\<forall>a\<in>\<E>. 0 \<le> flow_lookup fl a \<and> (cap a = - 1 \<or> flow_lookup fl a \<le> cap a))"

text \<open>The executable capacity predicate is exactly the abstract @{const isuflow} on the flow's
      abstraction: @{term cap} encodes @{term \<open>\<u>\<close>} with the @{term \<open>- 1\<close>} sentinel for @{term \<open>\<infinity>\<close>}
      (@{thm cap_encoding}), and since @{term \<open>0 \<le> \<u> e\<close>} a finite room @{term \<open>f e \<le> cap e\<close>} matches
      @{term \<open>ereal (f e) \<le> \<u> e\<close>} while the sentinel matches the always-true infinite bound.\<close>

lemma af_cap_feasible_iff_isuflow:
 "af_cap_feasible fl \<longleftrightarrow> isuflow (h \<circ> flow_lookup fl)"
proof-
  have "(0 \<le> flow_lookup fl a \<and> (cap a = - 1 \<or> flow_lookup fl a \<le> cap a))
          \<longleftrightarrow> (ereal (h (flow_lookup fl a)) \<le> \<u> a \<and> 0 \<le> h (flow_lookup fl a))"
    if ae: "a \<in> \<E>" for a
  proof (cases "\<u> a = \<infinity>")
    case True
    hence c: "cap a = - 1" using cap_encoding[OF ae] by simp
    have "ereal (h (flow_lookup fl a)) \<le> \<u> a" using True by simp
    thus ?thesis using c by simp
  next
    case False
    hence ua: "\<u> a = ereal (h (cap a))" using cap_encoding[OF ae] by simp
    have "cap a \<noteq> - 1" using ua u_non_neg[of a] by (auto simp: zero_ereal_def)
    thus ?thesis using ua by auto
  qed
  thus ?thesis by (auto simp: af_cap_feasible_def isuflow_def)
qed

text \<open>Feasibility as a genuine @{term b}-flow of the flow's abstraction (Theme D1): capacity
      feasibility (@{const isuflow}, phrased over the abstract @{term \<open>\<u>\<close>}) \emph{together with} the
      balance/divergence condition @{term \<open>- ex\<^bsub>f\<^esub> v = b v\<close>} at every vertex. The executable
      capacity @{term cap} appears only inside the internal helper @{const af_cap_feasible}, which
      bridges to @{const isuflow} by @{thm af_cap_feasible_iff_isuflow}; the invariant itself is
      stated entirely over the abstract network.\<close>

definition "af_feasible b fl \<longleftrightarrow> (h \<circ> flow_lookup fl) is b flow"

lemma af_feasibleI:
  "af_cap_feasible fl \<Longrightarrow> (\<And>v. v \<in> \<V> \<Longrightarrow> - ex (h \<circ> flow_lookup fl) v = b v) \<Longrightarrow> af_feasible b fl"
  by (auto simp: af_feasible_def af_cap_feasible_iff_isuflow intro: isbflowI)

lemma af_feasible_cap: "af_feasible b fl \<Longrightarrow> af_cap_feasible fl"
  by (auto simp: af_feasible_def af_cap_feasible_iff_isuflow elim: isbflowE)

lemma af_feasible_bal: "af_feasible b fl \<Longrightarrow> v \<in> \<V> \<Longrightarrow> - ex (h \<circ> flow_lookup fl) v = b v"
  by (auto simp: af_feasible_def elim: isbflowE)

lemma af_push_arc_feasible:
  assumes ae: "a \<in> \<E>" and "0 \<le> flow_lookup fl a" "cap a = - 1 \<or> flow_lookup fl a \<le> cap a" "0 \<le> \<gamma>"
    "if dir then (cap a = - 1 \<or> flow_lookup fl a + \<gamma> \<le> cap a) else \<gamma> \<le> flow_lookup fl a"
    "flow_invar fl" "af_push_arc \<gamma> a dir fl = (fl', f')"
  shows "0 \<le> f' \<and> (cap a = - 1 \<or> f' \<le> cap a)"
  using assms af_push_arc_at[OF ae assms(6) assms(7)] by (cases dir) auto

text \<open>@{const af_scan} reads each arc's room only through @{term flow_lookup} at arcs of @{term es};
      so two flows agreeing on @{term es} produce the same scan. This is what lets a \emph{sequential}
      push (which mutates the flow as it walks) still see the rooms @{const af_scan} precomputed on the
      \emph{original} flow --- the distinct walked arcs never interfere.\<close>

lemma af_scan_cong:
  "(\<forall>b\<in>set es. flow_lookup fl b = flow_lookup fl' b) \<Longrightarrow>
   af_scan fl x vs es ds acc = af_scan fl' x vs es ds acc"
proof (induction fl x vs es ds acc rule: af_scan.induct)
  case (1 fl x u v1 vs a es d ds acc)
  have ar: "af_rooms fl a = af_rooms fl' a" using 1(2) by (simp add: af_rooms_def)
  obtain up dn where ud: "af_rooms fl a = (up, dn)" by fastforce
  have tail: "\<forall>b\<in>set es. flow_lookup fl b = flow_lookup fl' b" using 1(2) by simp
  show ?case
  proof (cases "v1 = x")
    case True thus ?thesis using ud ar by (simp add: Let_def)
  next
    case False
    show ?thesis using ud ar 1(1)[OF ud[symmetric] refl refl False tail] False by (simp add: Let_def)
  qed
qed simp_all

text \<open>Capacity-agnostic strengthenings of the scan room-bounds and walk-feasibility. Dropping the
      finite-capacity assumption: an infinite room shows up as the sentinel @{term \<open>- 1\<close>}, which
      @{const af_min} treats as ``no bound'' (neutral), so it never lowers a bottleneck; and pushing
      onto an infinite-capacity arc in its open direction is feasible for free (the @{term \<open>cap a = - 1\<close>}
      disjunct of @{const af_cap_feasible}).\<close>

lemma af_scan_ra_mono_gen:
  "af_cap_feasible fl \<Longrightarrow> set es \<subseteq> \<E> \<Longrightarrow> 0 \<le> ra0 \<Longrightarrow>
     af_scan fl x vs es ds (k0, ra0, rf0) = (k, ra, rf) \<Longrightarrow> ra \<le> ra0 \<and> 0 \<le> ra"
proof (induction fl x vs es ds "(k0, ra0, rf0)" arbitrary: k0 ra0 rf0 k ra rf rule: af_scan.induct)
  case (1 fl x u v1 vs a es d ds k0 ra0 rf0)
  obtain up dn where ud: "af_rooms fl a = (up, dn)" by fastforce
  have ain: "a \<in> \<E>" using 1(3) by auto
  have es3: "set es \<subseteq> \<E>" using 1(3) by auto
  have z0: "0 \<le> dn" "up = - 1 \<or> 0 \<le> up"
    using ud 1(2) ain by (auto simp: af_rooms_def af_cap_feasible_def Let_def split: if_splits)
  have m2: "af_min (if d then up else dn) ra0 \<le> ra0" "0 \<le> af_min (if d then up else dn) ra0"
    using z0 1(4) by (auto simp: af_min_def split: if_splits)
  show ?case
  proof (cases "v1 = x")
    case True
    thus ?thesis using 1(5) ud m2 by (auto simp: Let_def)
  next
    case False
    have rec: "af_scan fl x (v1 # vs) es ds
        (k0 + af_delta_cost a d, af_min (if d then up else dn) ra0, af_min (if d then dn else up) rf0)
        = (k, ra, rf)"
      using 1(5) ud False by (simp add: Let_def)
    have "ra \<le> af_min (if d then up else dn) ra0 \<and> 0 \<le> ra"
      using 1(1)[OF ud[symmetric] refl refl False 1(2) es3 m2(2) rec] by auto
    thus ?thesis using m2 by auto
  qed
qed auto

lemma af_scan_rf_mono_gen:
  "af_cap_feasible fl \<Longrightarrow> set es \<subseteq> \<E> \<Longrightarrow> 0 \<le> rf0 \<Longrightarrow>
     af_scan fl x vs es ds (k0, ra0, rf0) = (k, ra, rf) \<Longrightarrow> rf \<le> rf0 \<and> 0 \<le> rf"
proof (induction fl x vs es ds "(k0, ra0, rf0)" arbitrary: k0 ra0 rf0 k ra rf rule: af_scan.induct)
  case (1 fl x u v1 vs a es d ds k0 ra0 rf0)
  obtain up dn where ud: "af_rooms fl a = (up, dn)" by fastforce
  have ain: "a \<in> \<E>" using 1(3) by auto
  have es3: "set es \<subseteq> \<E>" using 1(3) by auto
  have z0: "0 \<le> dn" "up = - 1 \<or> 0 \<le> up"
    using ud 1(2) ain by (auto simp: af_rooms_def af_cap_feasible_def Let_def split: if_splits)
  have m2: "af_min (if d then dn else up) rf0 \<le> rf0" "0 \<le> af_min (if d then dn else up) rf0"
    using z0 1(4) by (auto simp: af_min_def split: if_splits)
  show ?case
  proof (cases "v1 = x")
    case True
    thus ?thesis using 1(5) ud m2 by (auto simp: Let_def)
  next
    case False
    have rec: "af_scan fl x (v1 # vs) es ds
        (k0 + af_delta_cost a d, af_min (if d then up else dn) ra0, af_min (if d then dn else up) rf0)
        = (k, ra, rf)"
      using 1(5) ud False by (simp add: Let_def)
    have "rf \<le> af_min (if d then dn else up) rf0 \<and> 0 \<le> rf"
      using 1(1)[OF ud[symmetric] refl refl False 1(2) es3 m2(2) rec] by auto
    thus ?thesis using m2 by auto
  qed
qed auto

lemma af_scan_ra_valid:
  "af_cap_feasible fl \<Longrightarrow> set es \<subseteq> \<E> \<Longrightarrow> (ra0 = - 1 \<or> 0 \<le> ra0) \<Longrightarrow>
     af_scan fl x vs es ds (k0, ra0, rf0) = (k, ra, rf) \<Longrightarrow> ra = - 1 \<or> 0 \<le> ra"
proof (induction fl x vs es ds "(k0, ra0, rf0)" arbitrary: k0 ra0 rf0 k ra rf rule: af_scan.induct)
  case (1 fl x u v1 vs a es d ds k0 ra0 rf0)
  obtain up dn where ud: "af_rooms fl a = (up, dn)" by fastforce
  have ain: "a \<in> \<E>" using 1(3) by auto
  have es3: "set es \<subseteq> \<E>" using 1(3) by auto
  have z0: "0 \<le> dn" "up = - 1 \<or> 0 \<le> up"
    using ud 1(2) ain by (auto simp: af_rooms_def af_cap_feasible_def Let_def split: if_splits)
  have m2: "af_min (if d then up else dn) ra0 = - 1 \<or> 0 \<le> af_min (if d then up else dn) ra0"
    using z0 1(4) by (auto simp: af_min_def split: if_splits)
  show ?case
  proof (cases "v1 = x")
    case True
    thus ?thesis using 1(5) ud m2 by (auto simp: Let_def)
  next
    case False
    have rec: "af_scan fl x (v1 # vs) es ds
        (k0 + af_delta_cost a d, af_min (if d then up else dn) ra0, af_min (if d then dn else up) rf0)
        = (k, ra, rf)"
      using 1(5) ud False by (simp add: Let_def)
    show ?thesis using 1(1)[OF ud[symmetric] refl refl False 1(2) es3 m2 rec] .
  qed
qed auto

lemma af_scan_rf_valid:
  "af_cap_feasible fl \<Longrightarrow> set es \<subseteq> \<E> \<Longrightarrow> (rf0 = - 1 \<or> 0 \<le> rf0) \<Longrightarrow>
     af_scan fl x vs es ds (k0, ra0, rf0) = (k, ra, rf) \<Longrightarrow> rf = - 1 \<or> 0 \<le> rf"
proof (induction fl x vs es ds "(k0, ra0, rf0)" arbitrary: k0 ra0 rf0 k ra rf rule: af_scan.induct)
  case (1 fl x u v1 vs a es d ds k0 ra0 rf0)
  obtain up dn where ud: "af_rooms fl a = (up, dn)" by fastforce
  have ain: "a \<in> \<E>" using 1(3) by auto
  have es3: "set es \<subseteq> \<E>" using 1(3) by auto
  have z0: "0 \<le> dn" "up = - 1 \<or> 0 \<le> up"
    using ud 1(2) ain by (auto simp: af_rooms_def af_cap_feasible_def Let_def split: if_splits)
  have m2: "af_min (if d then dn else up) rf0 = - 1 \<or> 0 \<le> af_min (if d then dn else up) rf0"
    using z0 1(4) by (auto simp: af_min_def split: if_splits)
  show ?case
  proof (cases "v1 = x")
    case True
    thus ?thesis using 1(5) ud m2 by (auto simp: Let_def)
  next
    case False
    have rec: "af_scan fl x (v1 # vs) es ds
        (k0 + af_delta_cost a d, af_min (if d then up else dn) ra0, af_min (if d then dn else up) rf0)
        = (k, ra, rf)"
      using 1(5) ud False by (simp add: Let_def)
    show ?thesis using 1(1)[OF ud[symmetric] refl refl False 1(2) es3 m2 rec] .
  qed
qed auto

text \<open>Relaxed to an infinite \emph{seed}: the closing arc of a cancellation seeds the walk-scan with its
      own room, which may be @{term \<open>- 1\<close>} (infinite). Since @{const af_min} neutralises @{term \<open>- 1\<close>},
      the walked-arc feasibility still goes through --- the bottleneck bounds are derived only where the
      relevant room is finite.\<close>

lemma af_scan_push_feasible_gen2:
  "af_cap_feasible fl \<Longrightarrow> flow_invar fl \<Longrightarrow> distinct es \<Longrightarrow> set es \<subseteq> \<E> \<Longrightarrow>
   af_scan fl x vs es ds (k0, ra0, rf0) = (k, ra, rf) \<Longrightarrow>
   af_push \<gamma> x vs es ds flip fl = (fl', m') \<Longrightarrow>
   0 \<le> \<gamma> \<Longrightarrow> (ra0 = - 1 \<or> 0 \<le> ra0) \<Longrightarrow> (rf0 = - 1 \<or> 0 \<le> rf0) \<Longrightarrow> (if flip then \<gamma> \<le> rf else \<gamma> \<le> ra) \<Longrightarrow>
   af_cap_feasible fl'"
proof (induction \<gamma> x vs es ds flip fl arbitrary: fl' m' k0 ra0 rf0 rule: af_push.induct)
  case (1 \<gamma> x u v1 vs a es d ds flip fl)
  have ain: "a \<in> \<E>" using 1(5) by auto
  have adist: "a \<notin> set es" using 1(4) by auto
  have es3: "set es \<subseteq> \<E>" using 1(5) by auto
  obtain up dn where ud: "af_rooms fl a = (up, dn)" by fastforce
  have dnv: "dn = flow_lookup fl a" using ud by (auto simp: af_rooms_def Let_def)
  have upv: "up = (if cap a = - 1 then - 1 else cap a - flow_lookup fl a)" using ud by (auto simp: af_rooms_def Let_def)
  have base: "0 \<le> flow_lookup fl a" "cap a = - 1 \<or> flow_lookup fl a \<le> cap a"
    using 1(2) ain by (auto simp: af_cap_feasible_def)
  have z0dn: "0 \<le> dn" using dnv base by simp
  have z0up: "up = - 1 \<or> 0 \<le> up" using upv base by auto
  obtain fl1 fv where p1: "af_push_arc \<gamma> a (d \<noteq> flip) fl = (fl1, fv)" by fastforce
  have fi1: "flow_invar fl1" using 1(3) af_push_arc_flow_invar[OF ain p1] by blast
  define Ra where "Ra = af_min (if d then up else dn) ra0"
  define Rf where "Rf = af_min (if d then dn else up) rf0"
  have z1: "Ra = - 1 \<or> 0 \<le> Ra" using z0dn z0up 1(9) by (auto simp: Ra_def af_min_def split: if_splits)
  have z1': "Rf = - 1 \<or> 0 \<le> Rf" using z0dn z0up 1(10) by (auto simp: Rf_def af_min_def split: if_splits)
  have raRa: "0 \<le> Ra \<Longrightarrow> ra \<le> Ra"
  proof -
    assume zRa: "0 \<le> Ra"
    show "ra \<le> Ra"
    proof (cases "v1 = x")
      case True thus ?thesis using 1(6) ud by (simp add: Let_def Ra_def)
    next
      case False
      have rec: "af_scan fl x (v1 # vs) es ds (k0 + af_delta_cost a d, Ra, Rf) = (k, ra, rf)"
        using 1(6) ud False by (simp add: Let_def Ra_def Rf_def)
      show ?thesis using af_scan_ra_mono_gen[OF 1(2) es3 zRa rec] by auto
    qed
  qed
  have rfRf: "0 \<le> Rf \<Longrightarrow> rf \<le> Rf"
  proof -
    assume zRf: "0 \<le> Rf"
    show "rf \<le> Rf"
    proof (cases "v1 = x")
      case True thus ?thesis using 1(6) ud by (simp add: Let_def Rf_def)
    next
      case False
      have rec: "af_scan fl x (v1 # vs) es ds (k0 + af_delta_cost a d, Ra, Rf) = (k, ra, rf)"
        using 1(6) ud False by (simp add: Let_def Ra_def Rf_def)
      show ?thesis using af_scan_rf_mono_gen[OF 1(2) es3 zRf rec] by auto
    qed
  qed
  have gle: "(if (d \<noteq> flip) then up else dn) \<noteq> - 1 \<Longrightarrow> \<gamma> \<le> (if (d \<noteq> flip) then up else dn)"
  proof -
    assume rne: "(if (d \<noteq> flip) then up else dn) \<noteq> - 1"
    show "\<gamma> \<le> (if (d \<noteq> flip) then up else dn)"
    proof (cases flip)
      case Tf: True
      have g: "\<gamma> \<le> rf" using 1(11) Tf by simp
      have rne': "(if d then dn else up) \<noteq> - 1" using rne Tf by (cases d) auto
      have zRf: "0 \<le> Rf" using rne' z0dn z0up 1(10) by (auto simp: Rf_def af_min_def split: if_splits)
      have "rf \<le> (if d then dn else up)" using rfRf[OF zRf] af_min_le1[OF rne', of rf0] unfolding Rf_def by linarith
      thus ?thesis using g Tf by (cases d) auto
    next
      case Ff: False
      have g: "\<gamma> \<le> ra" using 1(11) Ff by simp
      have rne': "(if d then up else dn) \<noteq> - 1" using rne Ff by (cases d) auto
      have zRa: "0 \<le> Ra" using rne' z0dn z0up 1(9) by (auto simp: Ra_def af_min_def split: if_splits)
      have "ra \<le> (if d then up else dn)" using raRa[OF zRa] af_min_le1[OF rne', of ra0] unfolding Ra_def by linarith
      thus ?thesis using g Ff by (cases d) auto
    qed
  qed
  have room': "if (d \<noteq> flip) then (cap a = - 1 \<or> flow_lookup fl a + \<gamma> \<le> cap a) else \<gamma> \<le> flow_lookup fl a"
  proof (cases "d \<noteq> flip")
    case fwd: True
    show ?thesis
    proof (cases "cap a = - 1")
      case True thus ?thesis using fwd by simp
    next
      case capf: False
      have fle: "flow_lookup fl a \<le> cap a" using base(2) capf by simp
      have upeq: "up = cap a - flow_lookup fl a" using upv capf by simp
      have up0: "0 \<le> up" using upeq fle by linarith
      have "(if (d \<noteq> flip) then up else dn) \<noteq> - 1" using fwd up0 by simp
      hence "\<gamma> \<le> (if (d \<noteq> flip) then up else dn)" using gle by simp
      hence "\<gamma> \<le> up" using fwd by simp
      hence "flow_lookup fl a + \<gamma> \<le> cap a" using upeq by simp
      thus ?thesis using fwd by simp
    qed
  next
    case bwd: False
    have "(if (d \<noteq> flip) then up else dn) \<noteq> - 1" using bwd z0dn by simp
    hence "\<gamma> \<le> (if (d \<noteq> flip) then up else dn)" using gle by simp
    hence "\<gamma> \<le> dn" using bwd by simp
    thus ?thesis using bwd dnv by simp
  qed
  have feas1: "af_cap_feasible fl1"
    unfolding af_cap_feasible_def
  proof
    fix c assume c: "c \<in> \<E>"
    show "0 \<le> flow_lookup fl1 c \<and> (cap c = - 1 \<or> flow_lookup fl1 c \<le> cap c)"
    proof (cases "c = a")
      case True
      show ?thesis
        using True af_push_arc_feasible[OF ain base(1) base(2) 1(8) room' 1(3) p1] af_push_arc_at[OF ain 1(3) p1]
        by auto
    next
      case False
      have "flow_lookup fl1 c = flow_lookup fl c" using af_push_arc_flow_off[OF ain 1(3) False p1] by simp
      thus ?thesis using c 1(2) by (auto simp: af_cap_feasible_def)
    qed
  qed
  show ?case
  proof (cases "v1 = x")
    case True
    hence "fl' = fl1" using 1(7) p1 by (auto simp: Let_def)
    thus ?thesis using feas1 by simp
  next
    case False
    obtain fl2 r where p2: "af_push \<gamma> x (v1 # vs) es ds flip fl1 = (fl2, r)" by fastforce
    have des: "distinct es" using 1(4) by simp
    have fleq: "fl' = fl2" using 1(7) p1 p2 False by (auto simp: Let_def)
    have agree: "\<forall>b\<in>set es. flow_lookup fl1 b = flow_lookup fl b"
    proof
      fix b assume "b \<in> set es"
      hence "b \<noteq> a" using adist by auto
      thus "flow_lookup fl1 b = flow_lookup fl b" using af_push_arc_flow_off[OF ain 1(3) _ p1] by blast
    qed
    have rec: "af_scan fl x (v1 # vs) es ds (k0 + af_delta_cost a d, Ra, Rf) = (k, ra, rf)"
      using 1(6) ud False by (simp add: Let_def Ra_def Rf_def)
    have rec1: "af_scan fl1 x (v1 # vs) es ds (k0 + af_delta_cost a d, Ra, Rf) = (k, ra, rf)"
      using af_scan_cong[OF agree] rec by simp
    have bott: "if flip then \<gamma> \<le> rf else \<gamma> \<le> ra" using 1(11) .
    have "af_cap_feasible fl2"
      by (rule 1(1)[OF p1[symmetric] refl False feas1 fi1 des es3 rec1 p2 1(8) z1 z1' bott])
    thus ?thesis using fleq by simp
  qed
qed auto

text \<open>Whole-flow feasibility for a single push on the \emph{closing} arc, given it fits that arc's room.\<close>

lemma af_push_arc_af_cap_feasible:
  assumes A1: "af_cap_feasible fl" and A2: "flow_invar fl" and A3: "a \<in> \<E>" and A4: "0 \<le> \<gamma>"
    and A5: "if dir then (cap a = - 1 \<or> flow_lookup fl a + \<gamma> \<le> cap a) else \<gamma> \<le> flow_lookup fl a"
    and A6: "af_push_arc \<gamma> a dir fl = (fl', f')"
  shows "af_cap_feasible fl'"
  unfolding af_cap_feasible_def
proof (rule ballI)
  fix c assume c: "c \<in> \<E>"
  have base: "0 \<le> flow_lookup fl a" "cap a = - 1 \<or> flow_lookup fl a \<le> cap a"
    using A1 A3 by (auto simp: af_cap_feasible_def)
  show "0 \<le> flow_lookup fl' c \<and> (cap c = - 1 \<or> flow_lookup fl' c \<le> cap c)"
  proof (cases "c = a")
    case True
    show ?thesis
      using True af_push_arc_feasible[OF A3 base(1) base(2) A4 A5 A2 A6] af_push_arc_at[OF A3 A2 A6]
      by auto
  next
    case False
    have "flow_lookup fl' c = flow_lookup fl c" using af_push_arc_flow_off[OF A3 A2 False A6] by simp
    thus ?thesis using c A1 by (auto simp: af_cap_feasible_def)
  qed
qed

text \<open>Capacity-agnostic feasibility of a whole cancellation: no finite-capacity assumption. The walked
      arcs stay feasible by @{thm [source] af_scan_push_feasible_gen2} (an infinite closing-arc seed is
      tolerated), the free-set positivity of the chosen room by the scan-validity lemmas, and the closing
      arc by @{thm [source] af_push_arc_af_cap_feasible} (which handles @{term \<open>cap a = - 1\<close>} directly).\<close>

lemma af_cancel_seg_feasible_gen:
  assumes A1: "af_cap_feasible fl" and A3: "flow_invar fl"
    and A4: "distinct (a # es)" and A5: "a \<in> \<E>" and A6: "set es \<subseteq> \<E>"
    and A7: "af_rooms fl a = (up, dn)"
    and A8: "af_cancel_seg up dn x vs es ds a dir fl = (fl'', m', ubd)"
  shows "af_cap_feasible fl''"
proof -
  have des: "distinct es" using A4 by simp
  have adist: "a \<notin> set es" using A4 by simp
  have dnv: "dn = flow_lookup fl a" using A7 by (auto simp: af_rooms_def Let_def)
  have upv: "up = (if cap a = - 1 then - 1 else cap a - flow_lookup fl a)" using A7 by (auto simp: af_rooms_def Let_def)
  have base: "0 \<le> flow_lookup fl a" "cap a = - 1 \<or> flow_lookup fl a \<le> cap a" using A1 A5 by (auto simp: af_cap_feasible_def)
  have z0dn: "0 \<le> dn" using dnv base by simp
  have z0up: "up = - 1 \<or> 0 \<le> up" using upv base by auto
  have s1: "(if dir then up else dn) = - 1 \<or> 0 \<le> (if dir then up else dn)" using z0dn z0up by (cases dir) auto
  have s2: "(if dir then dn else up) = - 1 \<or> 0 \<le> (if dir then dn else up)" using z0dn z0up by (cases dir) auto
  obtain k ra rf where sc: "af_scan fl x vs es ds
      (af_delta_cost a dir, if dir then up else dn, if dir then dn else up) = (k, ra, rf)" by (metis prod_cases3)
  have rav: "ra = - 1 \<or> 0 \<le> ra" using af_scan_ra_valid[OF A1 A6 s1 sc] .
  have rfv: "rf = - 1 \<or> 0 \<le> rf" using af_scan_rf_valid[OF A1 A6 s2 sc] .
  show ?thesis
  proof (cases "(if 0 < k then rf else ra) \<noteq> - 1")
    case fin: True
    let ?flip = "0 < k"
    let ?g = "if ?flip then rf else ra"
    obtain fl' r where p: "af_push ?g x vs es ds ?flip fl = (fl', r)" by fastforce
    obtain fl2 f2 where pa: "af_push_arc ?g a (dir \<noteq> ?flip) fl' = (fl2, f2)" by fastforce
    have e: "fl'' = fl2" using A8 sc fin p pa by (auto simp: af_cancel_seg_def Let_def)
    have gpos: "0 \<le> ?g" using rav rfv fin by (cases ?flip) auto
    have gbott: "if ?flip then ?g \<le> rf else ?g \<le> ra" by (cases ?flip) auto
    have feas': "af_cap_feasible fl'"
      by (rule af_scan_push_feasible_gen2[OF A1 A3 des A6 sc p gpos s1 s2 gbott])
    have fi': "flow_invar fl'" by (rule af_push_flow_invar[OF A6 p A3])
    have fla: "flow_lookup fl' a = flow_lookup fl a" 
      using af_push_flow_off A3 adist p  A6 by blast
    have cle: "(if (dir \<noteq> ?flip) then up else dn) \<noteq> - 1 \<Longrightarrow> ?g \<le> (if (dir \<noteq> ?flip) then up else dn)"
    proof -
      assume rne: "(if (dir \<noteq> ?flip) then up else dn) \<noteq> - 1"
      show "?g \<le> (if (dir \<noteq> ?flip) then up else dn)"
      proof (cases ?flip)
        case True
        have g: "?g = rf" using True by simp
        have req: "(if (dir \<noteq> ?flip) then up else dn) = (if dir then dn else up)" using True by (cases dir) auto
        have rne': "(if dir then dn else up) \<noteq> - 1" using rne req by simp
        have s0: "0 \<le> (if dir then dn else up)" using rne' z0dn z0up by (cases dir) auto
        have "rf \<le> (if dir then dn else up)" using af_scan_rf_mono_gen[OF A1 A6 s0 sc] by simp
        thus ?thesis using g req by simp
      next
        case False
        have g: "?g = ra" using False by simp
        have req: "(if (dir \<noteq> ?flip) then up else dn) = (if dir then up else dn)" using False by (cases dir) auto
        have rne': "(if dir then up else dn) \<noteq> - 1" using rne req by simp
        have s0: "0 \<le> (if dir then up else dn)" using rne' z0dn z0up by (cases dir) auto
        have "ra \<le> (if dir then up else dn)" using af_scan_ra_mono_gen[OF A1 A6 s0 sc] by simp
        thus ?thesis using g req by simp
      qed
    qed
    have gle: "if (dir \<noteq> ?flip) then (cap a = - 1 \<or> flow_lookup fl' a + ?g \<le> cap a) else ?g \<le> flow_lookup fl' a"
    proof (cases "dir \<noteq> ?flip")
      case fwd: True
      show ?thesis
      proof (cases "cap a = - 1")
        case True thus ?thesis using fwd by simp
      next
        case capf: False
        have fle: "flow_lookup fl a \<le> cap a" using base(2) capf by simp
        have upeq: "up = cap a - flow_lookup fl a" using upv capf by simp
        have up0: "0 \<le> up" using upeq fle by linarith
        have "(if (dir \<noteq> ?flip) then up else dn) \<noteq> - 1" using fwd up0 by simp
        hence "?g \<le> (if (dir \<noteq> ?flip) then up else dn)" using cle by simp
        hence "?g \<le> up" using fwd by simp
        hence "flow_lookup fl a + ?g \<le> cap a" using upeq by simp
        thus ?thesis using fwd fla by simp
      qed
    next
      case bwd: False
      have "(if (dir \<noteq> ?flip) then up else dn) \<noteq> - 1" using bwd z0dn by simp
      hence "?g \<le> (if (dir \<noteq> ?flip) then up else dn)" using cle by simp
      hence "?g \<le> dn" using bwd by simp
      thus ?thesis using bwd fla dnv by simp
    qed
    show ?thesis using e af_push_arc_af_cap_feasible[OF feas' fi' A5 gpos gle pa] by simp
  next
    case notfin: False
    show ?thesis
    proof (cases "k = 0 \<and> rf \<noteq> - 1")
      case sw: True
      obtain fl' r where p: "af_push rf x vs es ds True fl = (fl', r)" by fastforce
      obtain fl2 f2 where pa: "af_push_arc rf a (dir \<noteq> True) fl' = (fl2, f2)" by fastforce
      have e: "fl'' = fl2" using A8 sc notfin sw p pa by (auto simp: af_cancel_seg_def Let_def)
      have gpos: "0 \<le> rf" using rfv sw by auto
      have gbott: "if True then rf \<le> rf else rf \<le> ra" by simp
      have feas': "af_cap_feasible fl'"
        by (rule af_scan_push_feasible_gen2[OF A1 A3 des A6 sc p gpos s1 s2 gbott])
      have fi': "flow_invar fl'" by (rule af_push_flow_invar[OF A6 p A3])
      have fla: "flow_lookup fl' a = flow_lookup fl a" by (rule af_push_flow_off[OF A6 A3 adist p])
      have cle: "(if (dir \<noteq> True) then up else dn) \<noteq> - 1 \<Longrightarrow> rf \<le> (if (dir \<noteq> True) then up else dn)"
      proof -
        assume rne: "(if (dir \<noteq> True) then up else dn) \<noteq> - 1"
        have req: "(if (dir \<noteq> True) then up else dn) = (if dir then dn else up)" by (cases dir) auto
        have rne': "(if dir then dn else up) \<noteq> - 1" using rne req by simp
        have s0: "0 \<le> (if dir then dn else up)" using rne' z0dn z0up by (cases dir) auto
        have "rf \<le> (if dir then dn else up)" using af_scan_rf_mono_gen[OF A1 A6 s0 sc] by simp
        thus "rf \<le> (if (dir \<noteq> True) then up else dn)" using req by simp
      qed
      have gle: "if (dir \<noteq> True) then (cap a = - 1 \<or> flow_lookup fl' a + rf \<le> cap a) else rf \<le> flow_lookup fl' a"
      proof (cases "dir \<noteq> True")
        case fwd: True
        show ?thesis
        proof (cases "cap a = - 1")
          case True thus ?thesis using fwd by simp
        next
          case capf: False
          have fle: "flow_lookup fl a \<le> cap a" using base(2) capf by simp
          have upeq: "up = cap a - flow_lookup fl a" using upv capf by simp
          have up0: "0 \<le> up" using upeq fle by linarith
          have "(if (dir \<noteq> True) then up else dn) \<noteq> - 1" using fwd up0 by simp
          hence "rf \<le> (if (dir \<noteq> True) then up else dn)" using cle by simp
          hence "rf \<le> up" using fwd by simp
          hence "flow_lookup fl a + rf \<le> cap a" using upeq by simp
          thus ?thesis using fwd fla by simp
        qed
      next
        case bwd: False
        have "(if (dir \<noteq> True) then up else dn) \<noteq> - 1" using bwd z0dn by simp
        hence "rf \<le> (if (dir \<noteq> True) then up else dn)" using cle by simp
        hence "rf \<le> dn" using bwd by simp
        thus ?thesis using bwd fla dnv by simp
      qed
      show ?thesis using e af_push_arc_af_cap_feasible[OF feas' fi' A5 gpos gle pa] by simp
    next
      case ub: False
      from A8 sc notfin ub have "fl'' = fl" by (auto simp: af_cancel_seg_def Let_def)
      thus ?thesis using A1 by simp
    qed
  qed
qed

subsection \<open>Theme D3 --- cost is non-increasing\<close>

text \<open>Cost of a flow (over the multigraph): @{term \<open>\<C> f = (\<Sum>e\<in>\<E>. f e * \<c> e)\<close>}. One push on an arc
      shifts the total cost by exactly \<open>\<plusminus>\<gamma>\<close> times that arc's unit cost --- the sum over @{term \<E>}
      differs only at the pushed arc (finite @{term \<E>}).\<close>

lemma af_push_arc_cost:
  assumes fi: "flow_invar fl" and ain: "a \<in> \<E>"
    and p: "af_push_arc \<gamma> a dir fl = (fl', f')"
  shows "\<C> (h \<circ> flow_lookup fl') = \<C> (h \<circ> flow_lookup fl) + (if dir then h \<gamma> else - h \<gamma>) * \<c> a"
proof -
  have off: "\<And>e. e \<noteq> a \<Longrightarrow> flow_lookup fl' e = flow_lookup fl e"
    using af_push_arc_flow_off[OF ain fi _ p] by blast
  have at: "flow_lookup fl' a = flow_lookup fl a + (if dir then \<gamma> else - \<gamma>)"
    using af_push_arc_at[OF ain fi p] by simp
  have g0: "\<And>e. e \<in> \<E> \<Longrightarrow> e \<noteq> a \<Longrightarrow> (h (flow_lookup fl' e) - h (flow_lookup fl e)) * \<c> e = 0"
    using off by simp
  have "\<C> (h \<circ> flow_lookup fl') - \<C> (h \<circ> flow_lookup fl)
        = (\<Sum>e\<in>\<E>. (h (flow_lookup fl' e) - h (flow_lookup fl e)) * \<c> e)"
    by (simp add: \<C>_def sum_subtractf left_diff_distrib comp_def)
  also have "\<dots> = (h (flow_lookup fl' a) - h (flow_lookup fl a)) * \<c> a"
  proof -
    have "(\<Sum>e\<in>\<E>. (h (flow_lookup fl' e) - h (flow_lookup fl e)) * \<c> e)
          = (h (flow_lookup fl' a) - h (flow_lookup fl a)) * \<c> a
            + (\<Sum>e\<in>\<E>-{a}. (h (flow_lookup fl' e) - h (flow_lookup fl e)) * \<c> e)"
      by (rule sum.remove[OF finite_E ain])
    moreover have "(\<Sum>e\<in>\<E>-{a}. (h (flow_lookup fl' e) - h (flow_lookup fl e)) * \<c> e) = 0"
      by (rule sum.neutral) (auto simp: g0)
    ultimately show ?thesis by simp
  qed
  also have "\<dots> = (if dir then h \<gamma> else - h \<gamma>) * \<c> a" using at by (simp add: h_add)
  finally show ?thesis by simp
qed

text \<open>Coupled cost accounting for the walk: pushing @{term \<gamma>} along the scanned cycle changes the total
      cost by @{term \<gamma>} times the scan's accumulated walk cost @{term \<open>k - k0\<close>} (negated when flipped). The
      per-arc shifts of @{thm [source] af_push_arc_cost} telescope into @{const af_scan}'s @{term k}, with
      @{thm [source] af_scan_cong} transporting the (original-flow) cost tags across the sequential push.\<close>

lemma af_scan_push_cost:
  "flow_invar fl \<Longrightarrow> distinct es \<Longrightarrow> set es \<subseteq> \<E> \<Longrightarrow>
   af_scan fl x vs es ds (k0, ra0, rf0) = (k, ra, rf) \<Longrightarrow>
   af_push \<gamma> x vs es ds flip fl = (fl', m') \<Longrightarrow>
   \<C> (h \<circ> flow_lookup fl') = \<C> (h \<circ> flow_lookup fl) + h (\<gamma> * (if flip then k0 - k else k - k0))"
proof (induction \<gamma> x vs es ds flip fl arbitrary: fl' m' k0 ra0 rf0 rule: af_push.induct)
  case (1 \<gamma> x u v1 vs a es d ds flip fl)
  have ain: "a \<in> \<E>" using 1(4) by auto
  have adist: "a \<notin> set es" using 1(3) by auto
  obtain up dn where ud: "af_rooms fl a = (up, dn)" by fastforce
  obtain fl1 fv where p1: "af_push_arc \<gamma> a (d \<noteq> flip) fl = (fl1, fv)" by fastforce
  have fi1: "flow_invar fl1" 
    using 1(2) af_push_arc_flow_invar p1 ain by auto
  have hc: "\<C> (h \<circ> flow_lookup fl1) = \<C> (h \<circ> flow_lookup fl) + h (\<gamma> * (if flip then - af_delta_cost a d else af_delta_cost a d))"
    using af_push_arc_cost[OF 1(2) ain p1]
    by (cases flip; cases d; simp add: af_delta_cost_def algebra_simps h_mult cost_h[OF ain])
  have kacc: "af_scan fl x (u # v1 # vs) (a # es) (d # ds) (k0, ra0, rf0)
             = (let acc = (k0 + af_delta_cost a d, af_min (if d then up else dn) ra0, af_min (if d then dn else up) rf0)
                in if v1 = x then acc else af_scan fl x (v1 # vs) es ds acc)"
    using ud by (simp add: Let_def)
  show ?case
  proof (cases "v1 = x")
    case True
    have kv: "k = k0 + af_delta_cost a d" using 1(5) kacc True by (simp add: Let_def)
    have "fl' = fl1" using 1(6) p1 True by (auto simp: Let_def)
    thus ?thesis using hc kv by (cases flip; simp add: algebra_simps comp_def)
  next
    case False
    obtain fl2 r where p2: "af_push \<gamma> x (v1 # vs) es ds flip fl1 = (fl2, r)" by fastforce
    have fleq: "fl' = fl2" using 1(6) p1 p2 False by (auto simp: Let_def)
    have des: "distinct es" using 1(3) by simp
    have ses: "set es \<subseteq> \<E>" using 1(4) by simp
    have agree: "\<forall>b\<in>set es. flow_lookup fl1 b = flow_lookup fl b"
    proof
      fix b assume "b \<in> set es"
      hence "b \<noteq> a" using adist by auto
      thus "flow_lookup fl1 b = flow_lookup fl b" using af_push_arc_flow_off[OF ain 1(2) _ p1] by blast
    qed
    have rec: "af_scan fl x (v1 # vs) es ds (k0 + af_delta_cost a d, af_min (if d then up else dn) ra0, af_min (if d then dn else up) rf0) = (k, ra, rf)"
      using 1(5) kacc False by (simp add: Let_def)
    have rec1: "af_scan fl1 x (v1 # vs) es ds (k0 + af_delta_cost a d, af_min (if d then up else dn) ra0, af_min (if d then dn else up) rf0) = (k, ra, rf)"
      using af_scan_cong[OF agree] rec by simp
    have IH: "\<C> (h \<circ> flow_lookup fl2) = \<C> (h \<circ> flow_lookup fl1) + h (\<gamma> * (if flip then (k0 + af_delta_cost a d) - k else k - (k0 + af_delta_cost a d)))"
      by (rule 1(1)[OF p1[symmetric] refl False fi1 des ses rec1 p2])
    show ?thesis using fleq hc IH
      by (cases flip; simp add: algebra_simps h_add comp_def)
  qed
qed auto

text \<open>Theme D3, top level: a whole cancellation \emph{never increases} the cost. The walk push contributes
      @{term \<open>\<gamma> * (if flip then k0 - k else k - k0)\<close>} and the closing arc @{term \<open>\<gamma> * (if flip then - k0 else k0)\<close>}
      (@{term \<open>k0 = af_delta_cost a dir\<close>} is exactly the closing arc's tagged cost, the scan seed), summing to
      @{term \<open>\<gamma> * (if 0 < k then - k else k)\<close>} which is @{text \<le>} 0 since @{term \<open>0 \<le> \<gamma>\<close>} and @{term \<open>flip = (0 < k)\<close>}
      picks the non-positive orientation; the zero-cost switch (@{term \<open>k = 0\<close>}) is cost-neutral, and the flag
      branch is cost-preserving.\<close>

text \<open>Capacity-agnostic cost non-increase of a cancellation: the walk cost identity and closing-arc cost
      are capacity-free, and the only use of finite capacity was to bound @{term \<gamma>} below by @{term 0} ---
      which the scan-validity lemmas provide unconditionally.\<close>

lemma af_cancel_seg_cost_le_gen:
  assumes A1: "af_cap_feasible fl" and A3: "flow_invar fl"
    and A4: "distinct (a # es)" and A5: "a \<in> \<E>" and A6: "set es \<subseteq> \<E>"
    and A7: "af_rooms fl a = (up, dn)"
    and A8: "af_cancel_seg up dn x vs es ds a dir fl = (fl'', m', ubd)"
  shows "\<C> (h \<circ> flow_lookup fl'') \<le> \<C> (h \<circ> flow_lookup fl)"
proof -
  have des: "distinct es" using A4 by simp
  have adist: "a \<notin> set es" using A4 by simp
  have dnv: "dn = flow_lookup fl a" using A7 by (auto simp: af_rooms_def Let_def)
  have upv: "up = (if cap a = - 1 then - 1 else cap a - flow_lookup fl a)" using A7 by (auto simp: af_rooms_def Let_def)
  have base: "0 \<le> flow_lookup fl a" "cap a = - 1 \<or> flow_lookup fl a \<le> cap a" using A1 A5 by (auto simp: af_cap_feasible_def)
  have z0dn: "0 \<le> dn" using dnv base by simp
  have z0up: "up = - 1 \<or> 0 \<le> up" using upv base by auto
  have s1: "(if dir then up else dn) = - 1 \<or> 0 \<le> (if dir then up else dn)" using z0dn z0up by (cases dir) auto
  have s2: "(if dir then dn else up) = - 1 \<or> 0 \<le> (if dir then dn else up)" using z0dn z0up by (cases dir) auto
  obtain k ra rf where sc: "af_scan fl x vs es ds
      (af_delta_cost a dir, if dir then up else dn, if dir then dn else up) = (k, ra, rf)" by (metis prod_cases3)
  have rav: "ra = - 1 \<or> 0 \<le> ra" using af_scan_ra_valid[OF A1 A6 s1 sc] .
  have rfv: "rf = - 1 \<or> 0 \<le> rf" using af_scan_rf_valid[OF A1 A6 s2 sc] .
  consider (fin) "(if 0 < k then rf else ra) \<noteq> - 1"
    | (sw) "\<not> (if 0 < k then rf else ra) \<noteq> - 1" "k = 0 \<and> rf \<noteq> - 1"
    | (ubd) "\<not> (if 0 < k then rf else ra) \<noteq> - 1" "\<not> (k = 0 \<and> rf \<noteq> - 1)" by blast
  then show ?thesis
  proof cases
    case fin
    obtain fl' r where p: "af_push (if 0 < k then rf else ra) x vs es ds (0 < k) fl = (fl', r)" by fastforce
    obtain fl2 f2 where pa: "af_push_arc (if 0 < k then rf else ra) a (dir \<noteq> (0 < k)) fl' = (fl2, f2)" by fastforce
    from A8 sc fin have e: "fl'' = fl2" using p pa by (auto simp: af_cancel_seg_def Let_def)
    have gpos: "0 \<le> (if 0 < k then rf else ra)" using rav rfv fin by (cases "0 < k") auto
    have fi': "flow_invar fl'" by (rule af_push_flow_invar[OF A6 p A3])
    have walk: "\<C> (h \<circ> flow_lookup fl') = \<C> (h \<circ> flow_lookup fl)
        + h ((if 0 < k then rf else ra) * (if (0 < k) then af_delta_cost a dir - k else k - af_delta_cost a dir))"
      by (rule af_scan_push_cost[OF A3 des A6 sc p])
    have close: "\<C> (h \<circ> flow_lookup fl2) = \<C> (h \<circ> flow_lookup fl')
        + (if (dir \<noteq> (0 < k)) then h (if 0 < k then rf else ra) else - h (if 0 < k then rf else ra)) * \<c> a"
      by (rule af_push_arc_cost[OF fi' A5 pa])
    have costeq: "\<C> (h \<circ> flow_lookup fl2) = \<C> (h \<circ> flow_lookup fl) + h ((if 0 < k then rf else ra) * (if 0 < k then - k else k))"
      using walk close by (cases "0 < k"; cases dir; simp add: af_delta_cost_def algebra_simps h_add h_mult cost_h[OF A5, symmetric])
    have le: "(if 0 < k then rf else ra) * (if 0 < k then - k else k) \<le> 0"
      using gpos by (cases "0 < k") (auto intro: mult_nonneg_nonpos)
    show ?thesis using e costeq le by simp
  next
    case sw
    obtain fl' r where p: "af_push rf x vs es ds True fl = (fl', r)" by fastforce
    obtain fl2 f2 where pa: "af_push_arc rf a (dir \<noteq> True) fl' = (fl2, f2)" by fastforce
    from A8 sc sw have e: "fl'' = fl2" using p pa by (auto simp: af_cancel_seg_def Let_def)
    have fi': "flow_invar fl'" by (rule af_push_flow_invar[OF A6 p A3])
    have walk: "\<C> (h \<circ> flow_lookup fl') = \<C> (h \<circ> flow_lookup fl) + h (rf * (if True then af_delta_cost a dir - k else k - af_delta_cost a dir))"
      by (rule af_scan_push_cost[OF A3 des A6 sc p])
    have close: "\<C> (h \<circ> flow_lookup fl2) = \<C> (h \<circ> flow_lookup fl') + (if (dir \<noteq> True) then h rf else - h rf) * \<c> a"
      by (rule af_push_arc_cost[OF fi' A5 pa])
    have costeq: "\<C> (h \<circ> flow_lookup fl2) = \<C> (h \<circ> flow_lookup fl) + h (rf * (- k))"
      using walk close by (cases dir; simp add: af_delta_cost_def algebra_simps h_add h_mult cost_h[OF A5, symmetric])
    have "k = 0" using sw by simp
    then show ?thesis using e costeq by simp
  next
    case ubd
    from A8 sc ubd have "fl'' = fl" by (auto simp: af_cancel_seg_def Let_def)
    thus ?thesis by simp
  qed
qed

subsection \<open>Theme E1 --- the iterator arrays implement the multigraph\<close>

text \<open>The two edge-iterator arrays held in the DFS state keep abstracting, at every vertex, to that
      vertex's outgoing/ingoing edges --- i.e.\ @{const multigraph_inv} of the \emph{current} arrays is an
      invariant. It only ever changes by (i) advancing one cell (@{term move_on_edges}, which preserves
      both @{term iset_abstract} and the iterator invariant) or (ii) resetting cells to the pristine
      originals (@{term out_arr} / @{term in_arr}, correct by the standing @{term \<open>multigraph_inv out_arr in_arr\<close>}).
      Consequently the arc the DFS scans at the top vertex is a genuine incident arc (E1 proper).\<close>

lemma af_current_out_incident:
  assumes mi: "multigraph_inv oa ia" and v: "v \<in> \<V>" and hc: "out_has oa v"
  shows "out_current oa v \<in> \<delta>\<^sup>+ v"
proof -
  have oi: "out_invar oa" and ab: "out_abstract oa v = \<delta>\<^sup>+ v"
    using mi v by (auto simp: multigraph_inv_def out_graph_inv_def)
  have ne: "out_remaining oa v \<noteq> {}" using hc 
    using outg.idx_has[OF oi v] hc by auto
  have "out_current oa v \<in> out_remaining oa v" 
    using outg.idx_current[OF oi v ne] .
  moreover have "out_remaining oa v \<subseteq> out_abstract oa v"
    using outg.idx_partition_union[OF oi v] by blast
  ultimately show ?thesis using ab by blast
qed

lemma af_current_in_incident:
  assumes mi: "multigraph_inv oa ia" and v: "v \<in> \<V>" and hc: "in_has ia v"
  shows "in_current ia v \<in> \<delta>\<^sup>- v"
proof -
  have ii: "in_invar ia" and ab: "in_abstract ia v = \<delta>\<^sup>- v"
    using mi v by (auto simp: multigraph_inv_def in_graph_inv_def)
  have ne: "in_remaining ia v \<noteq> {}" using hc 
    by (simp add: ing.idx_has[OF ii v])
  have "in_current ia v \<in> in_remaining ia v" 
    using ing.idx_current[OF ii v ne ] .
  moreover have "in_remaining ia v \<subseteq> in_abstract ia v"
    using ing.idx_partition_union[OF ii v] by blast
  ultimately show ?thesis using ab by blast
qed

lemma af_current_out_endpoint:
  assumes "multigraph_inv oa ia" "v \<in> \<V>" "out_has oa v"
  shows "fst (out_current oa v) = v \<and> out_current oa v \<in> \<E>"
  using af_current_out_incident[OF assms] by (auto simp: delta_plus_def)

lemma af_current_in_endpoint:
  assumes "multigraph_inv oa ia" "v \<in> \<V>" "in_has ia v"
  shows "snd (in_current ia v) = v \<and> in_current ia v \<in> \<E>"
  using af_current_in_incident[OF assms] by (auto simp: delta_minus_def)

lemma multigraph_inv_out_advance:
  assumes mi: "multigraph_inv oa ia" and hc: "out_has oa v"
  and v: "v \<in> \<V>"
  shows "multigraph_inv (out_move oa v) ia"
proof -
  have oi: "out_invar oa" and oab: "\<forall>w\<in>\<V>. out_abstract oa w = \<delta>\<^sup>+ w"
    using mi by (auto simp: multigraph_inv_def out_graph_inv_def)
  have ig: "in_graph_inv ia" using mi by (simp add: multigraph_inv_def)
  have ne: "out_remaining oa v \<noteq> {}" using hc 
    by (simp add: outg.idx_has[OF oi v])
  have "out_graph_inv (out_move oa v)"
    using outg.idx_move_invar[OF oi v] 
     outg.idx_move_abstract[OF oi v ne] oab
    by (auto simp: out_graph_inv_def)
  thus ?thesis using ig by (simp add: multigraph_inv_def)
qed

lemma multigraph_inv_in_advance:
  assumes mi: "multigraph_inv oa ia" and hc: "in_has ia v"
   and v: "v \<in> \<V>"
  shows "multigraph_inv oa (in_move ia v)"
proof -
  have ii: "in_invar ia" and iab: "\<forall>w\<in>\<V>. in_abstract ia w = \<delta>\<^sup>- w"
    using mi by (auto simp: multigraph_inv_def in_graph_inv_def)
  have og: "out_graph_inv oa" using mi by (simp add: multigraph_inv_def)
  have ne: "in_remaining ia v \<noteq> {}" using hc 
    by (simp add: ing.idx_has[OF ii v])
  have "in_graph_inv (in_move ia v)"
    using ing.idx_move_invar[OF ii v] ing.idx_move_abstract[OF ii v ne] iab
    by (auto simp: in_graph_inv_def)
  thus ?thesis using og by (simp add: multigraph_inv_def)
qed

lemma multigraph_inv_reset:
  assumes pri: "multigraph_inv out_arr in_arr" 
     and mi: "multigraph_inv oa ia" and v: "v \<in> \<V>"
  shows "multigraph_inv (out_reset oa v) (in_reset ia v)"
proof -
  have oi: "out_invar oa" and oab: "\<forall>w\<in>\<V>. out_abstract oa w = \<delta>\<^sup>+ w"
    using mi by (auto simp: multigraph_inv_def out_graph_inv_def)
  have ii: "in_invar ia" and iab: "\<forall>w\<in>\<V>. in_abstract ia w = \<delta>\<^sup>- w"
    using mi by (auto simp: multigraph_inv_def in_graph_inv_def)
  have "out_graph_inv (out_reset oa v)"
    using outg.idx_reset_invar[OF oi v] 
          outg.idx_reset_abstract[OF oi v] oab
    by (auto simp: out_graph_inv_def)
  moreover have "in_graph_inv (in_reset ia v)"
    using ing.idx_reset_invar[OF ii] v ing.idx_reset_abstract[OF ii] iab
    by (auto simp: in_graph_inv_def)
  ultimately show ?thesis by (simp add: multigraph_inv_def)
qed

text \<open>Every stack vertex is a vertex of the multigraph (a push only ever adds an endpoint of a scanned
      arc @{term \<open>a \<in> \<E>\<close>}); needed to invoke E1 at the top vertex.\<close>

definition "AF_invar_V st \<longleftrightarrow> set (af_vstack st) \<subseteq> \<V>"

definition "AF_invar_iter st \<longleftrightarrow> multigraph_inv (af_out_arr st) (af_in_arr st)"


lemma af_handle_invar_V:
  assumes AV: "AF_invar_V st" and ae: "a \<in> \<E>"
  shows "AF_invar_V (af_handle st a dir)"
proof -
  obtain up dn where updn: "af_rooms (af_flow st) a = (up, dn)"
    by (cases "af_rooms (af_flow st) a") auto
  have xV: "(if dir then snd a else fst a) \<in> \<V>" using ae fst_E_V snd_E_V by (cases dir) auto
  show ?thesis
  proof (cases "fst a = snd a")
    case selfl: True
    have "af_handle st a dir = af_selfloop_handle st a" using selfl by (simp add: af_handle_real[OF ae])
    thus ?thesis using AV by (simp add: AF_invar_V_def)
  next
    case selfloop: False
    show ?thesis
    proof (cases "0 < dn \<and> (up = - 1 \<or> 0 < up)")
      case False thus ?thesis using AV updn selfloop by (simp add: af_handle_real[OF ae] Let_def)
    next
      case guard: True
      show ?thesis
      proof (cases "af_estack st \<noteq> [] \<and> a = hd (af_estack st)")
        case True
        have "af_handle st a dir = st"
          unfolding af_handle_real[OF ae]
          using updn guard selfloop True by (simp add: Let_def)
        thus ?thesis using AV by (simp add: AF_invar_V_def)
      next
        case parent: False
        show ?thesis
        proof (cases "st_lookup (af_state st) (if dir then snd a else fst a)")
          case Unseen
          have "af_handle st a dir = st\<lparr>af_vstack := (if dir then snd a else fst a) # af_vstack st,
              af_state := st_upd (af_state st) (if dir then snd a else fst a) OnStack,
              af_estack := a # af_estack st, af_dstack := dir # af_dstack st\<rparr>"
            using updn guard selfloop parent Unseen by (auto simp: af_handle_real[OF ae] Let_def)
          thus ?thesis using AV xV by (simp add: AF_invar_V_def)
        next
          case OnStack
          obtain fl m' ubd where c: "af_cancel_seg up dn (if dir then snd a else fst a)
              (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) = (fl, m', ubd)"
            by (metis prod_cases3)
          show ?thesis
          proof (cases ubd)
            case True
            have "af_handle st a dir = st\<lparr>af_unbounded := True\<rparr>"
              using updn guard selfloop parent OnStack c True by (auto simp: af_handle_real[OF ae] Let_def)
            thus ?thesis using AV by (simp add: AF_invar_V_def)
          next
            case False
            have red: "af_handle st a dir = af_reset_unsee_seg m' (af_vstack st)
                (st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st),
                    af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>)"
              using updn guard selfloop parent OnStack c False by (auto simp: af_handle_real[OF ae] Let_def)
            have "set (drop m' (af_vstack st)) \<subseteq> \<V>"
              using AV set_drop_subset[of m' "af_vstack st"] by (auto simp: AF_invar_V_def)
            thus ?thesis using red by (simp add: AF_invar_V_def)
          qed
        next
          case Finished
          thus ?thesis using AV updn guard selfloop parent by (auto simp: af_handle_real[OF ae] Let_def)
        qed
      qed
    qed
  qed
qed

lemma AF_invar_V_out_arr[simp]: "AF_invar_V (st\<lparr>af_out_arr := X\<rparr>) = AF_invar_V st"
  by (simp add: AF_invar_V_def)
lemma AF_invar_V_in_arr[simp]: "AF_invar_V (st\<lparr>af_in_arr := X\<rparr>) = AF_invar_V st"
  by (simp add: AF_invar_V_def)

lemma AF_invar_V_holds_1:
  assumes conds: "AF_DFS_call_1_conds st" and AV: "AF_invar_V st" and Aiter: "AF_invar_iter st"
  shows "AF_invar_V (AF_DFS_upd1 st)"
proof -
  from conds have ne: "af_vstack st \<noteq> []" and he: "out_has (af_out_arr st) (hd (af_vstack st))"
    by (auto elim!: call_cond_elims)
  have vV: "hd (af_vstack st) \<in> \<V>" using AV ne hd_in_set by (auto simp: AF_invar_V_def)
  have ae: "out_current (af_out_arr st) (hd (af_vstack st)) \<in> \<E>"
    using af_current_out_endpoint[OF _ vV he] Aiter by (auto simp: AF_invar_iter_def)
  have AV': "AF_invar_V (st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack st))\<rparr>)"
    using AV by simp
  show ?thesis unfolding AF_DFS_upd1_def Let_def by (rule af_handle_invar_V[OF AV' ae])
qed

lemma AF_invar_V_holds_2:
  assumes conds: "AF_DFS_call_2_conds st" and AV: "AF_invar_V st" and Aiter: "AF_invar_iter st"
  shows "AF_invar_V (AF_DFS_upd2 st)"
proof -
  from conds have ne: "af_vstack st \<noteq> []" and he: "in_has (af_in_arr st) (hd (af_vstack st))"
    by (auto elim!: call_cond_elims)
  have vV: "hd (af_vstack st) \<in> \<V>" using AV ne hd_in_set by (auto simp: AF_invar_V_def)
  have ae: "in_current (af_in_arr st) (hd (af_vstack st)) \<in> \<E>"
    using af_current_in_endpoint[OF _ vV he] Aiter by (auto simp: AF_invar_iter_def)
  have AV': "AF_invar_V (st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack st))\<rparr>)"
    using AV by simp
  show ?thesis unfolding AF_DFS_upd2_def Let_def by (rule af_handle_invar_V[OF AV' ae])
qed

lemma AF_invar_V_holds_3:
  "AF_DFS_call_3_conds st \<Longrightarrow> AF_invar_V st \<Longrightarrow> AF_invar_V (AF_DFS_upd3 st)"
  by (cases "af_vstack st") (auto simp: AF_DFS_upd3_def AF_invar_V_def)

lemma af_reset_state_upd_iter:
  "\<lbrakk>multigraph_inv out_arr in_arr; v \<in> \<V>\<rbrakk>
    \<Longrightarrow> AF_invar_iter st \<Longrightarrow>
     AF_invar_iter (af_reset v (st \<lparr>af_state := st_upd (af_state st) v Unseen\<rparr>))"
  by (auto simp: AF_invar_iter_def af_reset_def intro: multigraph_inv_reset)

lemma af_reset_unsee_seg_iter:
  "set vs \<subseteq> \<V> \<Longrightarrow> 
  multigraph_inv out_arr in_arr \<Longrightarrow> AF_invar_iter st \<Longrightarrow> AF_invar_iter (af_reset_unsee_seg n vs st)"
  by (induction n vs st rule: af_reset_unsee_seg.induct) (auto intro: af_reset_state_upd_iter)

lemma af_handle_iter:
  assumes mi0: "multigraph_inv out_arr in_arr"
   and inv: "AF_invar_iter st" and inv2: "AF_invar_V st"
  shows "AF_invar_iter (af_handle st a dir)"
proof -
  show ?thesis
  proof (cases "fst_exec a = snd_exec a")
    case True
    have "af_handle st a dir = af_selfloop_handle st a" using True by (simp add: af_handle_def)
    thus ?thesis using inv by (simp add: AF_invar_iter_def)
  next
    case selfloop: False
    obtain up dn where updn: "af_rooms (af_flow st) a = (up, dn)"
      by (cases "af_rooms (af_flow st) a") auto
    show ?thesis
    proof (cases "0 < dn \<and> (up = - 1 \<or> 0 < up)")
      case False thus ?thesis using inv updn selfloop by (simp add: af_handle_def Let_def)
    next
      case guard: True
      show ?thesis
      proof (cases "af_estack st \<noteq> [] \<and> a = hd (af_estack st)")
        case True thus ?thesis using inv updn guard selfloop by (simp add: af_handle_def Let_def)
      next
        case parent: False
        show ?thesis
        proof (cases "st_lookup (af_state st) (if dir then snd_exec a else fst_exec a)")
          case Unseen
          have "af_handle st a dir = st\<lparr>af_vstack := (if dir then snd_exec a else fst_exec a) # af_vstack st,
              af_state := st_upd (af_state st) (if dir then snd_exec a else fst_exec a) OnStack,
              af_estack := a # af_estack st, af_dstack := dir # af_dstack st\<rparr>"
            using updn guard selfloop parent Unseen by (auto simp: af_handle_def Let_def)
          thus ?thesis using inv by (auto simp: AF_invar_iter_def)
        next
          case OnStack
          obtain fl m' ubd where c: "af_cancel_seg up dn (if dir then snd_exec a else fst_exec a)
              (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) = (fl, m', ubd)"
            by (metis prod_cases3)
          show ?thesis
          proof (cases ubd)
            case True
            have "af_handle st a dir = st\<lparr>af_unbounded := True\<rparr>"
              using updn guard selfloop parent OnStack c True by (auto simp: af_handle_def Let_def)
            thus ?thesis using inv by (simp add: AF_invar_iter_def)
          next
            case False
            have red: "af_handle st a dir = af_reset_unsee_seg m' (af_vstack st)
                (st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st),
                    af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>)"
              using updn guard selfloop parent OnStack c False by (auto simp: af_handle_def Let_def)
            have "AF_invar_iter (st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st),
                    af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>)"
              using inv by (simp add: AF_invar_iter_def)
            hence "AF_invar_iter (af_reset_unsee_seg m' (af_vstack st)
                (st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st),
                    af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>))"
              using af_reset_unsee_seg_iter mi0 
              using AF_invar_V_def inv2 by blast
            thus ?thesis using red by simp
          qed
        next
          case Finished
          thus ?thesis using inv updn guard selfloop parent by (auto simp: af_handle_def Let_def)
        qed
      qed
    qed
  qed
qed

lemma AF_invar_iter_holds_1:
  assumes mi0: "multigraph_inv out_arr in_arr" 
  and conds: "AF_DFS_call_1_conds st" and inv: "AF_invar_iter st"
  and invV: "AF_invar_V st"
  shows "AF_invar_iter (AF_DFS_upd1 st)"
proof -
  from conds have he: "out_has (af_out_arr st) (hd (af_vstack st))"
    by (auto elim!: call_cond_elims)
  have adv: "AF_invar_iter (st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack st))\<rparr>)"
    using inv he invV conds 
    by (cases "af_vstack st")
       (auto simp add: AF_invar_iter_def 
                       AF_DFS_call_1_conds_def AF_invar_V_def
           intro!: multigraph_inv_out_advance)
  show ?thesis
    using invV
    unfolding AF_DFS_upd1_def Let_def
    by (auto intro!: af_handle_iter[OF mi0 adv])
qed

lemma AF_invar_iter_holds_2:
  assumes mi0: "multigraph_inv out_arr in_arr"
   and conds: "AF_DFS_call_2_conds st" and inv: "AF_invar_iter st"
   and invV: "AF_invar_V st"
  shows "AF_invar_iter (AF_DFS_upd2 st)"
proof -
  from conds have he: "in_has (af_in_arr st) (hd (af_vstack st))"
    by (auto elim!: call_cond_elims)
  have adv: "AF_invar_iter (st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack st))\<rparr>)"
    using inv he conds invV
    by(cases "af_vstack st")
      (auto simp add: AF_invar_iter_def AF_DFS_call_2_conds_def  AF_invar_V_def
         intro!: multigraph_inv_in_advance)
  show ?thesis 
    using AF_invar_V_holds_2 conds inv invV
    by(auto intro!: af_handle_iter[OF mi0 adv] simp add: AF_DFS_upd2_def Let_def )
qed

lemma AF_invar_iter_holds_3:
  "AF_DFS_call_3_conds st \<Longrightarrow> AF_invar_iter st \<Longrightarrow> AF_invar_iter (AF_DFS_upd3 st)"
  by (auto simp: AF_DFS_upd3_def AF_invar_iter_def)

subsection \<open>Theme C --- the stack is a tagged (free) trail; and stack vertices are graph vertices\<close>

text \<open>The three stacks encode a walk in the graph: for each @{term i}, the arc @{term \<open>af_estack st ! i\<close>}
      with tag @{term \<open>af_dstack st ! i\<close>} joins @{term \<open>af_vstack st ! i\<close>} (its head, the child) to
      @{term \<open>af_vstack st ! Suc i\<close>} (its tail, the parent). This is the flow-independent \emph{structure}
      of Theme C (the freeness of the arcs is a separate, D2-coupled clause); it survives every DFS step ---
      push extends the walk by the just-scanned incident arc (E1), truncate/pop keep a suffix.\<close>

definition "AF_invar_3 st \<longleftrightarrow>
  (\<forall>i < length (af_estack st).
     (if af_dstack st ! i then snd (af_estack st ! i) else fst (af_estack st ! i)) = af_vstack st ! i \<and>
     (if af_dstack st ! i then fst (af_estack st ! i) else snd (af_estack st ! i)) = af_vstack st ! Suc i)"

text \<open>A suffix (drop the top @{term m} of all three stacks in lockstep) of a trail is a trail --- this covers
      both @{const AF_DFS_upd3} (pop, @{term \<open>m = 1\<close>}) and the back-edge truncation.\<close>

lemma AF_invar_3_drop:
  assumes A3: "AF_invar_3 st"
    and cpl: "Suc (length (af_estack st)) = length (af_vstack st)" "length (af_dstack st) = length (af_estack st)"
  shows "AF_invar_3 (st\<lparr>af_vstack := drop m (af_vstack st), af_estack := drop m (af_estack st), af_dstack := drop m (af_dstack st)\<rparr>)"
proof (unfold AF_invar_3_def, intro allI impI)
  fix i assume i: "i < length (af_estack (st\<lparr>af_vstack := drop m (af_vstack st), af_estack := drop m (af_estack st), af_dstack := drop m (af_dstack st)\<rparr>))"
  hence i2: "m + i < length (af_estack st)" by simp
  have "(if af_dstack st ! (m+i) then snd (af_estack st ! (m+i)) else fst (af_estack st ! (m+i))) = af_vstack st ! (m+i) \<and>
        (if af_dstack st ! (m+i) then fst (af_estack st ! (m+i)) else snd (af_estack st ! (m+i))) = af_vstack st ! Suc (m+i)"
    using A3 i2 by (auto simp: AF_invar_3_def)
  thus "(if af_dstack (st\<lparr>af_vstack := drop m (af_vstack st), af_estack := drop m (af_estack st), af_dstack := drop m (af_dstack st)\<rparr>) ! i
          then snd (af_estack (st\<lparr>af_vstack := drop m (af_vstack st), af_estack := drop m (af_estack st), af_dstack := drop m (af_dstack st)\<rparr>) ! i)
          else fst (af_estack (st\<lparr>af_vstack := drop m (af_vstack st), af_estack := drop m (af_estack st), af_dstack := drop m (af_dstack st)\<rparr>) ! i))
         = af_vstack (st\<lparr>af_vstack := drop m (af_vstack st), af_estack := drop m (af_estack st), af_dstack := drop m (af_dstack st)\<rparr>) ! i \<and>
        (if af_dstack (st\<lparr>af_vstack := drop m (af_vstack st), af_estack := drop m (af_estack st), af_dstack := drop m (af_dstack st)\<rparr>) ! i
          then fst (af_estack (st\<lparr>af_vstack := drop m (af_vstack st), af_estack := drop m (af_estack st), af_dstack := drop m (af_dstack st)\<rparr>) ! i)
          else snd (af_estack (st\<lparr>af_vstack := drop m (af_vstack st), af_estack := drop m (af_estack st), af_dstack := drop m (af_dstack st)\<rparr>) ! i))
         = af_vstack (st\<lparr>af_vstack := drop m (af_vstack st), af_estack := drop m (af_estack st), af_dstack := drop m (af_dstack st)\<rparr>) ! Suc i"
    using i2 cpl by (auto split: if_splits)
qed

text \<open>A raw-list view of the trail, to reason about the @{text Cons} (push) case free of record clutter.\<close>

definition "af_trail P es ds \<longleftrightarrow>
  (\<forall>i<length es. (if ds!i then snd (es!i) else fst (es!i)) = P!i \<and> (if ds!i then fst (es!i) else snd (es!i)) = P!Suc i)"

lemma AF_invar_3_conv: "AF_invar_3 st = af_trail (af_vstack st) (af_estack st) (af_dstack st)"
  by (simp add: AF_invar_3_def af_trail_def)

lemma af_trail_Cons:
  assumes inc: "(if dir then fst a else snd a) = hd P" and ne: "P \<noteq> []" and tr: "af_trail P es ds"
  shows "af_trail ((if dir then snd a else fst a) # P) (a # es) (dir # ds)"
proof (unfold af_trail_def, intro allI impI)
  fix i assume "i < length (a # es)"
  hence i: "i < Suc (length es)" by simp
  show "(if (dir # ds) ! i then snd ((a # es) ! i) else fst ((a # es) ! i)) = ((if dir then snd a else fst a) # P) ! i \<and>
        (if (dir # ds) ! i then fst ((a # es) ! i) else snd ((a # es) ! i)) = ((if dir then snd a else fst a) # P) ! Suc i"
  proof (cases "i = 0")
    case True
    thus ?thesis using inc ne by (auto simp: hd_conv_nth)
  next
    case False
    then obtain j where j: "i = Suc j" using not0_implies_Suc by blast
    hence jl: "j < length es" using i by simp
    have "(if ds!j then snd (es!j) else fst (es!j)) = P!j \<and> (if ds!j then fst (es!j) else snd (es!j)) = P!Suc j"
      using tr jl by (auto simp: af_trail_def)
    thus ?thesis using j by (auto split: if_splits)
  qed
qed

lemma AF_invar_3_push:
  assumes A3: "AF_invar_3 st"
    and inc: "(if dir then fst a else snd a) = hd (af_vstack st)"
    and ne: "af_vstack st \<noteq> []"
  shows "AF_invar_3 (st\<lparr>af_vstack := (if dir then snd a else fst a) # af_vstack st,
                        af_estack := a # af_estack st, af_dstack := dir # af_dstack st\<rparr>)"
proof -
  have "af_trail (af_vstack st) (af_estack st) (af_dstack st)" using A3 by (simp add: AF_invar_3_conv)
  from af_trail_Cons[OF inc ne this]
  have "af_trail ((if dir then snd a else fst a) # af_vstack st) (a # af_estack st) (dir # af_dstack st)" .
  thus ?thesis by (simp add: AF_invar_3_conv)
qed

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
proof (cases "a \<in> S")
  case True
  have "sum (g(a := g a + \<delta>)) S = (g a + \<delta>) + sum (g(a := g a + \<delta>)) (S - {a})"
    by (simp add: sum.remove[OF assms True])
  moreover have "sum (g(a := g a + \<delta>)) (S - {a}) = sum g (S - {a})"
    by (intro sum.cong) auto
  moreover have "sum g (S - {a}) = sum g S - g a"
    by (simp add: sum.remove[OF assms True])
  ultimately show ?thesis using True by simp
next
  case False
  hence "sum (g(a := g a + \<delta>)) S = sum g S" by (intro sum.cong) (auto simp: False)
  thus ?thesis using False by simp
qed

text \<open>The tail of a trail is a trail (index shift), used to peel the first arc in the push induction.\<close>

lemma af_trail_tl:
  assumes "af_trail (u # P) (a # es) (d # ds)"
  shows "af_trail P es ds"
proof (unfold af_trail_def, intro allI impI)
  fix j assume "j < length es"
  hence "Suc j < length (a # es)" by simp
  thus "(if ds ! j then snd (es ! j) else fst (es ! j)) = P ! j \<and>
        (if ds ! j then fst (es ! j) else snd (es ! j)) = P ! Suc j"
    using assms by (fastforce simp: af_trail_def)
qed

text \<open>A single arc push shifts the excess of its head vertex and its tail vertex by opposite signed
      amounts @{term \<gamma>} (or its negation, per the push direction); a self-loop leaves the excess
      unchanged.\<close>

lemma af_push_arc_ex:
  assumes fi: "flow_invar fl" and ae: "a \<in> \<E>"
    and p: "af_push_arc \<gamma> a dir fl = (fl', f')"
  shows "ex (h \<circ> flow_lookup fl') v = ex (h \<circ> flow_lookup fl) v
           + (if dir then h \<gamma> else - h \<gamma>) * ((if snd a = v then 1 else 0) - (if fst a = v then 1 else 0))"
proof -
  have fl'_eq: "flow_lookup fl' = (flow_lookup fl)(a := flow_lookup fl a + (if dir then \<gamma> else - \<gamma>))"
    using p fi ae by (auto simp: af_push_arc_def Let_def flow_array.fixed_univ_map_upd)
  have happ: "(\<lambda>e. h (flow_lookup fl' e)) = (\<lambda>e. h (flow_lookup fl e))(a := h (flow_lookup fl a) + (if dir then h \<gamma> else - h \<gamma>))"
    by (rule ext) (simp add: fl'_eq h_add)
  have din2: "(\<Sum>e\<in>\<delta>\<^sup>- v. h (flow_lookup fl' e))
             = (\<Sum>e\<in>\<delta>\<^sup>- v. h (flow_lookup fl e)) + (if a \<in> \<delta>\<^sup>- v then (if dir then h \<gamma> else - h \<gamma>) else 0)"
    unfolding happ by (rule sum_fun_upd_delta[OF delta_minus_finite])
  have dout2: "(\<Sum>e\<in>\<delta>\<^sup>+ v. h (flow_lookup fl' e))
             = (\<Sum>e\<in>\<delta>\<^sup>+ v. h (flow_lookup fl e)) + (if a \<in> \<delta>\<^sup>+ v then (if dir then h \<gamma> else - h \<gamma>) else 0)"
    unfolding happ by (rule sum_fun_upd_delta[OF delta_plus_finite])
  have inm: "(a \<in> \<delta>\<^sup>- v) = (snd a = v)" using ae by (auto simp: delta_minus_def)
  have inp: "(a \<in> \<delta>\<^sup>+ v) = (fst a = v)" using ae by (auto simp: delta_plus_def)
  show ?thesis by (simp add: ex_def din2 dout2 inm inp algebra_simps)
qed

subsection \<open>Self-loop normaliser: excess, cost and feasibility\<close>

lemma flow_upd_as_push: "af_push_arc (v - flow_lookup fl a) a True fl = (flow_upd fl a v, v)"
  by (simp add: af_push_arc_def Let_def)

lemma ex_flow_upd_selfloop:
  assumes ae: "a \<in> \<E>" and sl: "fst a = snd a" and fi: "flow_invar fl"
  shows "ex ( h o (flow_lookup (flow_upd fl a v))) w = 
       ex (h o (flow_lookup fl)) w"
  using af_push_arc_ex[OF fi ae flow_upd_as_push] sl by simp

lemma cost_flow_upd:
  assumes ae: "a \<in> \<E>" and fi: "flow_invar fl"
  shows "\<C> (h \<circ> flow_lookup (flow_upd fl a v)) = \<C> (h \<circ> flow_lookup fl) + h (v - flow_lookup fl a) * \<c> a"
  using af_push_arc_cost[OF fi ae flow_upd_as_push] by simp

lemma af_selfloop_handle_ex:
  assumes ae: "a \<in> \<E>" and sl: "fst a = snd a" and fi: "flow_invar (af_flow st)"
  shows "ex (h \<circ> flow_lookup (af_flow (af_selfloop_handle st a))) v = ex (h \<circ> flow_lookup (af_flow st)) v"
  using af_selfloop_handle_flow_cases[of st a] ex_flow_upd_selfloop[OF ae sl fi] by auto

lemma cap_nonneg: "a \<in> \<E> \<Longrightarrow> cap a \<noteq> - 1 \<Longrightarrow> 0 \<le> cap a"
proof -
  assume a: "a \<in> \<E>" and cne: "cap a \<noteq> - 1"
  have "\<u> a \<noteq> \<infinity>" using cap_encoding[OF a] cne by (auto split: if_splits)
  hence "\<u> a = ereal (h (cap a))" using cap_encoding[OF a] by simp
  hence "0 \<le> ereal (h (cap a))" using u_non_neg[of a] by simp
  thus "0 \<le> cap a" by (simp add: zero_ereal_def)
qed

lemma af_selfloop_handle_flow_scases:
  assumes ae: "a \<in> \<E>"
  shows "af_flow (af_selfloop_handle st a) = af_flow st
   \<or> (af_flow (af_selfloop_handle st a) = flow_upd (af_flow st) a 0 \<and> \<not> \<c> a < 0)
   \<or> (af_flow (af_selfloop_handle st a) = flow_upd (af_flow st) a (cap a) \<and> \<c> a < 0 \<and> cap a \<noteq> - 1)"
proof (cases "0 < \<c> a")
  case True thus ?thesis by (auto simp: af_selfloop_handle_def Let_def cost_neg_bridge[OF ae] split: if_splits)
next
  case notpos: False
  show ?thesis
  proof (cases "\<c> a < 0")
    case neg: True
    show ?thesis
    proof (cases "cap a = - 1")
      case True thus ?thesis using neg notpos by (auto simp: af_selfloop_handle_def Let_def cost_neg_bridge[OF ae])
    next
      case False thus ?thesis using neg notpos by (auto simp: af_selfloop_handle_def Let_def cost_neg_bridge[OF ae] split: if_splits)
    qed
  next
    case False
    hence "\<c> a = 0" using notpos by simp
    thus ?thesis by (auto simp: af_selfloop_handle_def Let_def cost_neg_bridge[OF ae] split: if_splits prod.splits)
  qed
qed

lemma af_selfloop_handle_feasible:
  assumes ae: "a \<in> \<E>" and fi: "flow_invar (af_flow st)" and feas: "af_cap_feasible (af_flow st)"
  shows "af_cap_feasible (af_flow (af_selfloop_handle st a))"
proof -
  have upd_feas: "\<And>v. 0 \<le> v \<Longrightarrow> (cap a = - 1 \<or> v \<le> cap a) \<Longrightarrow> af_cap_feasible (flow_upd (af_flow st) a v)"
    using feas flow_array.fixed_univ_map_upd[OF fi ae] by (auto simp: af_cap_feasible_def)
  from af_selfloop_handle_flow_scases[OF ae, of st] show ?thesis
  proof (elim disjE conjE)
    assume "af_flow (af_selfloop_handle st a) = af_flow st" thus ?thesis using feas by simp
  next
    assume z: "af_flow (af_selfloop_handle st a) = flow_upd (af_flow st) a 0" and "\<not> \<c> a < 0"
    show ?thesis using z upd_feas[of 0] cap_nonneg[OF ae] by (cases "cap a = - 1") auto
  next
    assume s: "af_flow (af_selfloop_handle st a) = flow_upd (af_flow st) a (cap a)"
      and "\<c> a < 0" and cne: "cap a \<noteq> - 1"
    show ?thesis using s upd_feas[of "cap a"] cap_nonneg[OF ae cne] by simp
  qed
qed

lemma af_selfloop_handle_cost_le:
  assumes ae: "a \<in> \<E>" and fi: "flow_invar (af_flow st)" and feas: "af_cap_feasible (af_flow st)"
  shows "\<C> (h \<circ> flow_lookup (af_flow (af_selfloop_handle st a))) \<le> \<C> (h \<circ> flow_lookup (af_flow st))"
proof -
  have base: "0 \<le> flow_lookup (af_flow st) a" "cap a = - 1 \<or> flow_lookup (af_flow st) a \<le> cap a"
    using feas ae by (auto simp: af_cap_feasible_def)
  from af_selfloop_handle_flow_scases[OF ae, of st] show ?thesis
  proof (elim disjE conjE)
    assume "af_flow (af_selfloop_handle st a) = af_flow st" thus ?thesis by simp
  next
    assume z: "af_flow (af_selfloop_handle st a) = flow_upd (af_flow st) a 0" and nn: "\<not> \<c> a < 0"
    have "\<C> (h \<circ> flow_lookup (flow_upd (af_flow st) a 0)) = \<C> (h \<circ> flow_lookup (af_flow st)) + h (0 - flow_lookup (af_flow st) a) * \<c> a"
      using cost_flow_upd[OF ae fi, of 0] by simp
    moreover have "h (0 - flow_lookup (af_flow st) a) * \<c> a \<le> 0"
      using base(1) nn by (auto intro: mult_nonpos_nonneg simp: not_less)
    ultimately show ?thesis using z by simp
  next
    assume s: "af_flow (af_selfloop_handle st a) = flow_upd (af_flow st) a (cap a)"
      and neg: "\<c> a < 0" and cne: "cap a \<noteq> - 1"
    have "\<C> (h \<circ> flow_lookup (flow_upd (af_flow st) a (cap a))) = \<C> (h \<circ> flow_lookup (af_flow st)) + h (cap a - flow_lookup (af_flow st) a) * \<c> a"
      using cost_flow_upd[OF ae fi, of "cap a"] by simp
    moreover have "h (cap a - flow_lookup (af_flow st) a) * \<c> a \<le> 0"
      using base(2) neg cne by (auto intro: mult_nonneg_nonpos)
    ultimately show ?thesis using s by simp
  qed
qed

text \<open>Pushing @{term \<gamma>} along the trail prefix that reaches @{term x}: the excess of every vertex is
      unchanged except the two ends of the sub-walk --- the start @{term \<open>hd vs\<close>} and the reached
      @{term x} --- which shift by @{term \<gamma>} up to sign. Proved by induction on the fused push,
      telescoping the per-arc boundary shifts; the coupling @{term \<open>Suc (length es) = length vs\<close>}
      rules out running off the stack before reaching @{term x}.\<close>

lemma af_push_ex:
  "flow_invar fl
    \<Longrightarrow> af_trail vs es ds \<Longrightarrow> set es \<subseteq> \<E> \<Longrightarrow>
   Suc (length es) = length vs \<Longrightarrow> length ds = length es \<Longrightarrow> x \<in> set (tl vs) \<Longrightarrow>
   af_push \<gamma> x vs es ds flip fl = (fl', m') \<Longrightarrow>
   ex (h \<circ> flow_lookup fl') v
     = ex (h \<circ> flow_lookup fl) v
       + (if flip then - h \<gamma> else h \<gamma>) * ((if hd vs = v then 1 else 0) - (if x = v then 1 else 0))"
proof (induction \<gamma> x vs es ds flip fl arbitrary: fl' m' rule: af_push.induct)
  case (1 \<gamma> x u v1 vs a es d ds flip fl)
  obtain fl1 fv where p1: "af_push_arc \<gamma> a (d \<noteq> flip) fl = (fl1, fv)" by fastforce
  have ain: "a \<in> \<E>" using 1 by auto
  have fi1: "flow_invar fl1" using 1(2) 
     af_push_arc_flow_invar[OF ain p1] by blast
  have trh: "(if d then snd a else fst a) = u \<and> (if d then fst a else snd a) = v1"
    using 1(3) by (fastforce simp: af_trail_def)
  have step_v1: "ex (h \<circ> flow_lookup fl1) v
                  = ex (h \<circ> flow_lookup fl) v
                    + (if flip then - h \<gamma> else h \<gamma>) * ((if u = v then 1 else 0) - (if v1 = v then 1 else 0))"
  proof -
    have "ex (h \<circ> flow_lookup fl1) v = ex (h \<circ> flow_lookup fl) v
            + (if (d \<noteq> flip) then h \<gamma> else - h \<gamma>) * ((if snd a = v then 1 else 0) - (if fst a = v then 1 else 0))"
      by (rule af_push_arc_ex[OF 1(2) ain p1])
    thus ?thesis using trh by (cases d; cases flip; auto simp: algebra_simps)
  qed
  show ?case
  proof (cases "v1 = x")
    case True
    hence "fl' = fl1" using 1(8) p1 by auto
    thus ?thesis using step_v1 True by (simp add: comp_def)
  next
    case False
    obtain fl2 r where p2: "af_push \<gamma> x (v1 # vs) es ds flip fl1 = (fl2, r)" by fastforce
    have tr1: "af_trail (v1 # vs) es ds" using af_trail_tl[OF 1(3)] .
    have es1: "set es \<subseteq> \<E>" using 1(4) by simp
    have cpl1a: "Suc (length es) = length (v1 # vs)" using 1(5) by simp
    have cpl1b: "length ds = length es" using 1(6) by simp
    have xin1: "x \<in> set (tl (v1 # vs))" using False 1(7) by auto
    have "fl' = fl2" using 1(8) p1 p2 False by auto
    moreover have "ex (h \<circ> flow_lookup fl2) v
                    = ex (h \<circ> flow_lookup fl1) v
                      + (if flip then - h \<gamma> else h \<gamma>) * ((if hd (v1 # vs) = v then 1 else 0) - (if x = v then 1 else 0))"
      by (rule 1(1)[OF p1[symmetric] refl False fi1 tr1 es1 cpl1a cpl1b xin1 p2])
    ultimately show ?thesis using step_v1 by (simp add: algebra_simps comp_def)
  qed
qed (auto simp: Suc_length_conv comp_def)

text \<open>A back-edge cancellation preserves every vertex's excess: the push around the trail prefix
      shifts the two ends (@{term \<open>hd vs\<close>} and @{term x}), and the closing arc @{term a} --- which
      connects exactly those two vertices --- cancels both shifts. Holds in all three cancellation
      branches (finite bottleneck, the cost-neutral finite ``switch'', and the unbounded no-op).\<close>

lemma af_cancel_seg_ex_pres:
  assumes fi: "flow_invar fl"
    and tr: "af_trail vs es ds"
    and esE: "set es \<subseteq> \<E>" and aE: "a \<in> \<E>"
    and cpl1: "Suc (length es) = length vs" and cpl2: "length ds = length es"
    and reach: "x \<in> set (tl vs)"
    and clt: "(if dir then fst a else snd a) = hd vs"
    and clh: "(if dir then snd a else fst a) = x"
    and res: "af_cancel_seg up dn x vs es ds a dir fl = (fl'', m', ubd)"
  shows "ex (h \<circ> flow_lookup fl'') v = ex (h \<circ> flow_lookup fl) v"
proof -
  obtain k ra rf where sc: "af_scan fl x vs es ds
      (af_delta_cost a dir, if dir then up else dn, if dir then dn else up) = (k, ra, rf)"
    by (metis prod_cases3)
  consider (fin) "(if 0 < k then rf else ra) \<noteq> - 1"
    | (sw) "\<not> (if 0 < k then rf else ra) \<noteq> - 1" "k = 0 \<and> rf \<noteq> - 1"
    | (ubd) "\<not> (if 0 < k then rf else ra) \<noteq> - 1" "\<not> (k = 0 \<and> rf \<noteq> - 1)"
    by blast
  then show ?thesis
  proof cases
    case fin
    obtain fl' r where p: "af_push (if 0 < k then rf else ra) x vs es ds (0 < k) fl = (fl', r)" by fastforce
    obtain fl2 f2 where pa: "af_push_arc (if 0 < k then rf else ra) a (dir \<noteq> (0 < k)) fl' = (fl2, f2)" 
      by fastforce
    from res sc fin have e: "fl'' = fl2" using p pa by (auto simp: af_cancel_seg_def Let_def)
    have fi': "flow_invar fl'" using af_push_flow_invar p fi esE by auto
    have e1: "ex (h \<circ> flow_lookup fl') v = ex (h \<circ> flow_lookup fl) v
               + (if (0 < k) then - h (if 0 < k then rf else ra) else h (if 0 < k then rf else ra))
                 * ((if hd vs = v then 1 else 0) - (if x = v then 1 else 0))"
      using af_push_ex[OF fi tr esE cpl1 cpl2 reach p] .
    have e2: "ex (h \<circ> flow_lookup fl2) v = ex (h \<circ> flow_lookup fl') v
               + (if (dir \<noteq> (0 < k)) then h (if 0 < k then rf else ra) else - h (if 0 < k then rf else ra))
                 * ((if snd a = v then 1 else 0) - (if fst a = v then 1 else 0))"
      using af_push_arc_ex[OF fi' aE pa] .
    show ?thesis unfolding e using e1 e2 clt clh by (cases dir; cases "0 < k"; auto simp: algebra_simps comp_def)
  next
    case sw
    obtain fl' r where p: "af_push rf x vs es ds True fl = (fl', r)" by fastforce
    obtain fl2 f2 where pa: "af_push_arc rf a (dir \<noteq> True) fl' = (fl2, f2)" by fastforce
    from res sc sw have e: "fl'' = fl2" using p pa by (auto simp: af_cancel_seg_def Let_def)
    have fi': "flow_invar fl'" using af_push_flow_invar p fi esE by auto
    have e1: "ex (h \<circ> flow_lookup fl') v = ex (h \<circ> flow_lookup fl) v
               + (if True then - h rf else h rf) * ((if hd vs = v then 1 else 0) - (if x = v then 1 else 0))"
      using af_push_ex[OF fi tr esE cpl1 cpl2 reach p] .
    have e2: "ex (h \<circ> flow_lookup fl2) v = ex (h \<circ> flow_lookup fl') v
               + (if (dir \<noteq> True) then h rf else - h rf) * ((if snd a = v then 1 else 0) - (if fst a = v then 1 else 0))"
      using af_push_arc_ex[OF fi' aE pa] .
    show ?thesis unfolding e using e1 e2 clt clh by (cases dir; auto simp: algebra_simps comp_def)
  next
    case ubd
    from res sc ubd have "fl'' = fl" by (auto simp: af_cancel_seg_def Let_def)
    thus ?thesis by simp
  qed
qed

text \<open>The self-loop cancellation (empty stack, closing arc @{term a} a genuine loop @{term \<open>fst a = snd a\<close>})
      trivially preserves excess: the push is over the empty trail and the closing loop-arc shifts its
      head and tail --- the same vertex --- by cancelling amounts.\<close>

lemma af_cancel_seg_ex_pres_selfloop:
  assumes fi: "flow_invar fl" and aE: "a \<in> \<E>" and sl: "fst a = snd a"
    and res: "af_cancel_seg up dn x [] [] [] a dir fl = (fl'', m', ubd)"
  shows "ex (h \<circ> flow_lookup fl'') v = ex (h \<circ> flow_lookup fl) v"
proof -
  obtain k ra rf where sc: "af_scan fl x [] [] []
      (af_delta_cost a dir, if dir then up else dn, if dir then dn else up) = (k, ra, rf)"
    by (metis prod_cases3)
  consider (fin) "(if 0 < k then rf else ra) \<noteq> - 1"
    | (sw) "\<not> (if 0 < k then rf else ra) \<noteq> - 1" "k = 0 \<and> rf \<noteq> - 1"
    | (ubd) "\<not> (if 0 < k then rf else ra) \<noteq> - 1" "\<not> (k = 0 \<and> rf \<noteq> - 1)"
    by blast
  then show ?thesis
  proof cases
    case fin
    obtain fl2 f2 where pa: "af_push_arc (if 0 < k then rf else ra) a (dir \<noteq> (0 < k)) fl = (fl2, f2)" by fastforce
    from res sc fin have e: "fl'' = fl2" using pa by (auto simp: af_cancel_seg_def Let_def)
    have "ex (h \<circ> flow_lookup fl2) v = ex (h \<circ> flow_lookup fl) v
           + (if (dir \<noteq> (0 < k)) then h (if 0 < k then rf else ra) else - h (if 0 < k then rf else ra))
             * ((if snd a = v then 1 else 0) - (if fst a = v then 1 else 0))"
      using af_push_arc_ex[OF fi aE pa] .
    thus ?thesis unfolding e using sl by simp
  next
    case sw
    obtain fl2 f2 where pa: "af_push_arc rf a (dir \<noteq> True) fl = (fl2, f2)" by fastforce
    from res sc sw have e: "fl'' = fl2" using pa by (auto simp: af_cancel_seg_def Let_def)
    have "ex (h \<circ> flow_lookup fl2) v = ex (h \<circ> flow_lookup fl) v
           + (if (dir \<noteq> True) then h rf else - h rf) * ((if snd a = v then 1 else 0) - (if fst a = v then 1 else 0))"
      using af_push_arc_ex[OF fi aE pa] .
    thus ?thesis unfolding e using sl by simp
  next
    case ubd
    from res sc ubd have "fl'' = fl" by (auto simp: af_cancel_seg_def Let_def)
    thus ?thesis by simp
  qed
qed

text \<open>Preservation of the trail structure across @{const af_handle}, given the \emph{incidence} precondition
      (the arc @{term a} leaves the current top vertex in direction @{term dir}) --- which the DFS discharges
      by E1. Push uses @{thm [source] AF_invar_3_push}; the back-edge branch uses @{thm [source] AF_invar_3_drop}
      (the reached ancestor's segment survives); all other branches leave the three stacks untouched.\<close>

lemma af_handle_invar_3:
  assumes A1: "AF_invar_1 st" and A2: "AF_invar_2 st" and A3: "AF_invar_3 st"
    and inc: "(if dir then fst a else snd a) = hd (af_vstack st)" and ne: "af_vstack st \<noteq> []" and ae: "a \<in> \<E>"
  shows "AF_invar_3 (af_handle st a dir)"
proof -
  have cpl: "Suc (length (af_estack st)) = length (af_vstack st)" "length (af_dstack st) = length (af_estack st)"
    using A2 ne by (auto simp: AF_invar_2_def)
  obtain up dn where updn: "af_rooms (af_flow st) a = (up, dn)"
    by (cases "af_rooms (af_flow st) a") auto
  have "a \<in> \<E>"
    using ae by fastforce
  hence [simp]: "fst_exec a = fst a" "snd_exec a = snd a"
    using ae fst_exec_eq snd_exec_eq by fastforce+
  show ?thesis
  proof (cases "fst a = snd a")
    case selfl: True
    have "af_handle st a dir = af_selfloop_handle st a" using selfl by (simp add: af_handle_real[OF ae])
    thus ?thesis using A3 by (simp add: AF_invar_3_conv)
  next
    case selfloop: False
    show ?thesis
    proof (cases "0 < dn \<and> (up = - 1 \<or> 0 < up)")
      case False thus ?thesis using A3 updn selfloop by (simp add: af_handle_real[OF ae] Let_def)
    next
      case guard: True
      show ?thesis
      proof (cases "af_estack st \<noteq> [] \<and> a = hd (af_estack st)")
        case True
        have "af_handle st a dir = st"
          unfolding af_handle_real[OF ae]
          using updn guard selfloop True by (simp add: Let_def)
        thus ?thesis using A3 by simp
      next
        case parent: False
        show ?thesis
        proof (cases "st_lookup (af_state st) (if dir then snd a else fst a)")
          case Unseen
          have "af_handle st a dir = st\<lparr>af_vstack := (if dir then snd a else fst a) # af_vstack st,
              af_state := st_upd (af_state st) (if dir then snd a else fst a) OnStack,
              af_estack := a # af_estack st, af_dstack := dir # af_dstack st\<rparr>"
            using updn guard selfloop parent Unseen by (auto simp: af_handle_real[OF ae] Let_def)
          moreover have "AF_invar_3 (st\<lparr>af_vstack := (if dir then snd a else fst a) # af_vstack st,
              af_estack := a # af_estack st, af_dstack := dir # af_dstack st\<rparr>)"
            using AF_invar_3_push[OF A3 inc ne] .
          ultimately show ?thesis by (simp add: AF_invar_3_conv)
        next
          case OnStack
          obtain fl m' ubd where c: "af_cancel_seg up dn (if dir then snd a else fst a)
              (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) = (fl, m', ubd)"
            by (metis prod_cases3)
          show ?thesis
          proof (cases ubd)
            case True
            have "af_handle st a dir = st\<lparr>af_unbounded := True\<rparr>"
              using updn guard selfloop parent OnStack c True by (auto simp: af_handle_real[OF ae] Let_def)
            thus ?thesis using A3 by (simp add: AF_invar_3_conv)
          next
            case False
            have red: "af_handle st a dir = af_reset_unsee_seg m' (af_vstack st)
                (st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st),
                    af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>)"
              using updn guard selfloop parent OnStack c False by (auto simp: af_handle_real[OF ae] Let_def)
            have "AF_invar_3 (st\<lparr>af_vstack := drop m' (af_vstack st),
                    af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>)"
              using AF_invar_3_drop[OF A3 cpl] .
            hence "AF_invar_3 (st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st),
                    af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>)"
              by (simp add: AF_invar_3_conv)
            thus ?thesis using red by (simp add: af_reset_unsee_seg_invar_3)
          qed
        next
          case Finished
          thus ?thesis using A3 updn guard selfloop parent by (auto simp: af_handle_real[OF ae] Let_def)
        qed
      qed
    qed
  qed
qed

text \<open>Lifting the trail structure and @{const AF_invar_V} to the whole inner DFS. The out/in edge-array
      advances leave both invariants (they touch neither the stacks nor the flow); the push branch discharges
      \<open>af_handle_invar_3\<close>'s incidence precondition (and \<open>af_handle_invar_V\<close>'s @{term \<open>a \<in> \<E>\<close>})
      through E1 at the top vertex.\<close>

lemma AF_invar_3_out_arr[simp]: "AF_invar_3 (st\<lparr>af_out_arr := X\<rparr>) = AF_invar_3 st"
  by (simp add: AF_invar_3_def)
lemma AF_invar_3_in_arr[simp]: "AF_invar_3 (st\<lparr>af_in_arr := X\<rparr>) = AF_invar_3 st"
  by (simp add: AF_invar_3_def)

lemma AF_invar_3_holds_1:
  assumes conds: "AF_DFS_call_1_conds st" and A1: "AF_invar_1 st" and A2: "AF_invar_2 st"
    and A3: "AF_invar_3 st" and Aiter: "AF_invar_iter st" and AV: "AF_invar_V st"
  shows "AF_invar_3 (AF_DFS_upd1 st)"
proof -
  from conds have ne: "af_vstack st \<noteq> []" and he: "out_has (af_out_arr st) (hd (af_vstack st))"
    by (auto elim!: call_cond_elims)
  have vV: "hd (af_vstack st) \<in> \<V>" using AV ne hd_in_set by (auto simp: AF_invar_V_def)
  have fstv: "fst (out_current (af_out_arr st) (hd (af_vstack st))) = hd (af_vstack st)"
    using af_current_out_endpoint[OF _ vV he] Aiter by (auto simp: AF_invar_iter_def)
  have ae: "out_current (af_out_arr st) (hd (af_vstack st)) \<in> \<E>"
    using af_current_out_endpoint[OF _ vV he] Aiter 
    by (auto simp: AF_invar_iter_def)
  have A1': "AF_invar_1 (st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack st))\<rparr>)"
    using vV  AF_invar_1_out_advance A1 by auto
  have inc: "(if True then fst (out_current (af_out_arr st) (hd (af_vstack st)))
             else snd (out_current (af_out_arr st) (hd (af_vstack st))))
           = hd (af_vstack (st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack st))\<rparr>))"
    using fstv by simp
  show ?thesis unfolding AF_DFS_upd1_def Let_def
    by (rule af_handle_invar_3[OF A1' _ _ inc _ ae]) (use A2 A3 ne in simp)+
qed

lemma AF_invar_3_holds_2:
  assumes conds: "AF_DFS_call_2_conds st" and A1: "AF_invar_1 st" and A2: "AF_invar_2 st"
    and A3: "AF_invar_3 st" and Aiter: "AF_invar_iter st" and AV: "AF_invar_V st"
  shows "AF_invar_3 (AF_DFS_upd2 st)"
proof -
  from conds have ne: "af_vstack st \<noteq> []" and he: "in_has (af_in_arr st) (hd (af_vstack st))"
    by (auto elim!: call_cond_elims)
  have vV: "hd (af_vstack st) \<in> \<V>" using AV ne hd_in_set by (auto simp: AF_invar_V_def)
  have sndv: "snd (in_current (af_in_arr st) (hd (af_vstack st))) = hd (af_vstack st)"
    using af_current_in_endpoint[OF _ vV he] Aiter by (auto simp: AF_invar_iter_def)
  have ae: "in_current (af_in_arr st) (hd (af_vstack st)) \<in> \<E>"
    using af_current_in_endpoint[OF _ vV he] Aiter by (auto simp: AF_invar_iter_def)
  have A1': "AF_invar_1 (st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack st))\<rparr>)"
    by (rule AF_invar_1_in_advance[OF vV A1])
  have inc: "(if False then fst (in_current (af_in_arr st) (hd (af_vstack st)))
             else snd (in_current (af_in_arr st) (hd (af_vstack st))))
           = hd (af_vstack (st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack st))\<rparr>))"
    using sndv by simp
  show ?thesis unfolding AF_DFS_upd2_def Let_def
    by (rule af_handle_invar_3[OF A1' _ _ inc _ ae]) (use A2 A3 ne in simp)+
qed

lemma AF_invar_3_holds_3:
  assumes conds: "AF_DFS_call_3_conds st" and A2: "AF_invar_2 st" and A3: "AF_invar_3 st"
  shows "AF_invar_3 (AF_DFS_upd3 st)"
proof -
  from conds have ne: "af_vstack st \<noteq> []" by (auto elim!: call_cond_elims)
  have cpl: "Suc (length (af_estack st)) = length (af_vstack st)" "length (af_dstack st) = length (af_estack st)"
    using A2 ne by (auto simp: AF_invar_2_def)
  have "AF_invar_3 (st\<lparr>af_vstack := drop (Suc 0) (af_vstack st), af_estack := drop (Suc 0) (af_estack st), af_dstack := drop (Suc 0) (af_dstack st)\<rparr>)"
    using AF_invar_3_drop[OF A3 cpl] .
  thus ?thesis by (simp add: AF_DFS_upd3_def AF_invar_3_conv drop_Suc)
qed

text \<open>The combined lift: Themes A, B, C-structure, E1 and @{const AF_invar_V} are jointly preserved by the
      inner DFS (a single induction, since the trail/vertex invariants depend on the iterator invariant).\<close>

subsection \<open>Theme D2 --- the free set shrinks: survivors of a cancellation stay free\<close>

text \<open>The free-arc guard the algorithm actually tests (@{term \<open>0 < dn \<and> (up = - 1 \<or> 0 < up)\<close>} on the rooms)
      coincides with @{const af_arc_free} on a feasible flow.\<close>

lemma af_guard_free:
  assumes "af_rooms fl a = (up, dn)" "cap a = - 1 \<or> flow_lookup fl a \<le> cap a"
  shows "(0 < dn \<and> (up = - 1 \<or> 0 < up)) = af_arc_free fl a"
  using assms by (auto simp: af_rooms_def af_arc_free_def Let_def split: if_splits)

text \<open>A push leaves its arc free exactly when the fused saturation test (on the value it wrote) says so.\<close>

lemma af_saturated_free:
  "a \<in> \<E> \<Longrightarrow> flow_invar fl \<Longrightarrow> af_push_arc \<gamma> a dir fl = (fl', f') \<Longrightarrow> \<not> af_saturated f' a \<Longrightarrow> af_arc_free fl' a"
  using af_push_arc_at[of a fl \<gamma> dir fl' f'] by (auto simp: af_saturated_def af_arc_free_def Let_def)

lemma af_saturated_notfree:
  "a \<in> \<E> \<Longrightarrow> flow_invar fl \<Longrightarrow> af_push_arc \<gamma> a dir fl = (fl', f') \<Longrightarrow> af_saturated f' a \<Longrightarrow> \<not> af_arc_free fl' a"
  using af_push_arc_at[of a fl \<gamma> dir fl' f'] by (auto simp: af_saturated_def af_arc_free_def Let_def)

text \<open>The crux of D2. The push pass returns the truncate count @{term \<open>m'\<close>} = one past the \emph{deepest}
      arc that saturated (or @{term 0} if none), so every arc from index @{term \<open>m'\<close>} onward stays free ---
      the surviving suffix of the cancellation is entirely free. This is purely combinatorial in the
      saturation flags (no room bound needed): distinctness keeps each arc's written value its own.\<close>

lemma af_push_survivor:
  "flow_invar fl \<Longrightarrow> distinct es \<Longrightarrow> (\<forall>b\<in>set es. af_arc_free fl b) \<Longrightarrow>
   af_push \<gamma> x vs es ds flip fl = (fl', m') \<Longrightarrow> set es \<subseteq> \<E> \<Longrightarrow>
   \<forall>i. i < length es \<longrightarrow> m' \<le> i \<longrightarrow> af_arc_free fl' (es ! i)"
proof (induction \<gamma> x vs es ds flip fl arbitrary: fl' m' rule: af_push.induct)
  case (1 \<gamma> x u v1 vs a es d ds flip fl)
  have ain: "a \<in> \<E>" using 1(6) by auto
  have estl: "set es \<subseteq> \<E>" using 1(6) by auto
  obtain fl1 f where p1: "af_push_arc \<gamma> a (d \<noteq> flip) fl = (fl1, f)" by fastforce
  have adist: "a \<notin> set es" using 1(3) by auto
  have fi1: "flow_invar fl1" using 1(2) af_push_arc_flow_invar[OF ain p1] by blast
  have tailfree: "\<forall>b\<in>set es. af_arc_free fl1 b"
  proof
    fix b assume b: "b \<in> set es"
    hence "b \<noteq> a" using adist by auto
    hence "flow_lookup fl1 b = flow_lookup fl b" using af_push_arc_flow_off[OF ain 1(2) _ p1] by blast
    thus "af_arc_free fl1 b" using b 1(4) by (auto simp: af_arc_free_def)
  qed
  show ?case
  proof (cases "v1 = x")
    case True
    from True 1(5) p1 have fl'eq: "fl' = fl1" and m'eq: "m' = (if af_saturated f a then 1 else 0)"
      by (auto simp: Let_def)
    show ?thesis
    proof (intro allI impI)
      fix i assume i: "i < length (a # es)" and mi: "m' \<le> i"
      show "af_arc_free fl' ((a # es) ! i)"
      proof (cases i)
        case 0
        have "\<not> af_saturated f a" using mi m'eq 0 by (auto split: if_splits)
        thus ?thesis using 0 fl'eq af_saturated_free[OF ain 1(2) p1] by simp
      next
        case (Suc j)
        hence jl: "j < length es" using i by simp
        have "af_arc_free fl1 (es ! j)" using tailfree jl nth_mem by blast
        thus ?thesis using Suc fl'eq by simp
      qed
    qed
  next
    case False
    obtain fl2 r where p2: "af_push \<gamma> x (v1 # vs) es ds flip fl1 = (fl2, r)" by fastforce
    from False 1(5) p1 p2 have fl'eq: "fl' = fl2"
      and m'eq: "m' = (if r \<noteq> 0 then Suc r else (if af_saturated f a then 1 else 0))"
      by (auto simp: Let_def)
    have des: "distinct es" using 1(3) by simp
    have IH: "\<forall>i. i < length es \<longrightarrow> r \<le> i \<longrightarrow> af_arc_free fl2 (es ! i)"
      using 1(1)[OF p1[symmetric] refl False fi1 des tailfree p2 estl] .
    show ?thesis
    proof (intro allI impI)
      fix i assume i: "i < length (a # es)" and mi: "m' \<le> i"
      show "af_arc_free fl' ((a # es) ! i)"
      proof (cases i)
        case 0
        have m0: "m' = 0" using mi 0 by simp
        hence r0: "r = 0" and nsat: "\<not> af_saturated f a" using m'eq by (auto split: if_splits)
        have "af_arc_free fl1 a" using af_saturated_free[OF ain 1(2) p1] nsat by simp
        moreover have "flow_lookup fl2 a = flow_lookup fl1 a"
          using af_push_flow_off[OF estl fi1 adist p2] by simp
        ultimately have "af_arc_free fl2 a" by (auto simp: af_arc_free_def)
        thus ?thesis using 0 fl'eq by simp
      next
        case (Suc j)
        hence jl: "j < length es" using i by simp
        have "r \<le> j"
        proof (cases "r = 0")
          case True thus ?thesis by simp
        next
          case False hence "m' = Suc r" using m'eq by simp
          thus ?thesis using mi Suc by simp
        qed
        hence "af_arc_free fl2 (es ! j)" using IH jl by blast
        thus ?thesis using Suc fl'eq by simp
      qed
    qed
  qed
qed auto

text \<open>Lifted to a whole cancellation: since the closing arc is off the walk (@{term \<open>a \<notin> set es\<close>}) it
      does not disturb the surviving arcs. Every arc of @{term es} from index @{term \<open>m'\<close>} onward is free
      in the post-cancellation flow (the unbounded-flag branch leaves the flow, hence freeness, untouched).\<close>

lemma af_cancel_seg_survivor_free:
  assumes fi: "flow_invar fl" and des: "distinct es" and free: "\<forall>b\<in>set es. af_arc_free fl b"
    and ane: "a \<notin> set es" and esE: "set es \<subseteq> \<E>" and ae: "a \<in> \<E>"
    and cs: "af_cancel_seg up dn x vs es ds a dir fl = (fl'', m', ubd)"
    and i: "i < length es" and mi: "m' \<le> i"
  shows "af_arc_free fl'' (es ! i)"
proof -
  obtain k ra rf where sc: "af_scan fl x vs es ds
      (af_delta_cost a dir, if dir then up else dn, if dir then dn else up) = (k, ra, rf)"
    by (metis prod_cases3)
  have imem: "es ! i \<in> set es" using i nth_mem by blast
  hence ine: "es ! i \<noteq> a" using ane by auto
  consider (fin) "(if 0 < k then rf else ra) \<noteq> - 1"
    | (sw) "\<not> (if 0 < k then rf else ra) \<noteq> - 1" "k = 0 \<and> rf \<noteq> - 1"
    | (ubd) "\<not> (if 0 < k then rf else ra) \<noteq> - 1" "\<not> (k = 0 \<and> rf \<noteq> - 1)"
    by blast
  then show ?thesis
  proof cases
    case fin
    obtain fl' r where p: "af_push (if 0 < k then rf else ra) x vs es ds (0 < k) fl = (fl', r)" by fastforce
    obtain fl2 f2 where pa: "af_push_arc (if 0 < k then rf else ra) a (dir \<noteq> (0 < k)) fl' = (fl2, f2)" by fastforce
    from cs sc fin have e: "fl'' = fl2" and meq: "m' = r" using p pa by (auto simp: af_cancel_seg_def Let_def)
    have "af_arc_free fl' (es ! i)" using af_push_survivor[OF fi des free p esE] i mi meq by auto
    moreover have fi': "flow_invar fl'" using af_push_flow_invar[OF esE p fi] .
    moreover have "flow_lookup fl2 (es ! i) = flow_lookup fl' (es ! i)"
      using af_push_arc_flow_off[OF ae fi' ine pa] by simp
    ultimately show ?thesis using e by (auto simp: af_arc_free_def)
  next
    case sw
    obtain fl' r where p: "af_push rf x vs es ds True fl = (fl', r)" by fastforce
    obtain fl2 f2 where pa: "af_push_arc rf a (dir \<noteq> True) fl' = (fl2, f2)" by fastforce
    from cs sc sw have e: "fl'' = fl2" and meq: "m' = r" using p pa by (auto simp: af_cancel_seg_def Let_def)
    have "af_arc_free fl' (es ! i)" using af_push_survivor[OF fi des free p esE] i mi meq by auto
    moreover have fi': "flow_invar fl'" using af_push_flow_invar[OF esE p fi] .
    moreover have "flow_lookup fl2 (es ! i) = flow_lookup fl' (es ! i)"
      using af_push_arc_flow_off[OF ae fi' ine pa] by simp
    ultimately show ?thesis using e by (auto simp: af_arc_free_def)
  next
    case ubd
    from cs sc ubd have "fl'' = fl" by (auto simp: af_cancel_seg_def Let_def)
    thus ?thesis using free imem by auto
  qed
qed

subsection \<open>Theme C (freeness) --- the stack arcs stay free, and the closing arc is off the stack\<close>

text \<open>The two endpoints of a stack arc are exactly its two trail vertices; hence a stack arc joins
      \emph{distinct} vertices, so no self-loop (and no arc incident to the top from a non-parent) can be
      a stack arc, and (from distinct @{term \<open>af_vstack st\<close>}) the arc list itself is distinct.\<close>

lemma trail_endpoints:
  "AF_invar_3 st \<Longrightarrow> i < length (af_estack st) \<Longrightarrow>
     {fst (af_estack st ! i), snd (af_estack st ! i)} = {af_vstack st ! i, af_vstack st ! Suc i}"
  by (auto simp: AF_invar_3_def split: if_splits)

lemma estack_distinct:
  assumes A2: "AF_invar_2 st" and A3: "AF_invar_3 st"
  shows "distinct (af_estack st)"
proof (cases "af_estack st = []")
  case True thus ?thesis by simp
next
  case False
  from A2 False have dP: "distinct (af_vstack st)"
    and cpl: "Suc (length (af_estack st)) = length (af_vstack st)"
    by (auto simp: AF_invar_2_def)
  show ?thesis
  proof (subst distinct_conv_nth, intro allI impI)
    fix i j assume i: "i < length (af_estack st)" and j: "j < length (af_estack st)" and ne: "i \<noteq> j"
    show "af_estack st ! i \<noteq> af_estack st ! j"
    proof
      assume eq: "af_estack st ! i = af_estack st ! j"
      have si: "{af_vstack st ! i, af_vstack st ! Suc i} = {af_vstack st ! j, af_vstack st ! Suc j}"
        using trail_endpoints[OF A3 i] trail_endpoints[OF A3 j] eq by simp
      have il: "i < length (af_vstack st)" "Suc i < length (af_vstack st)" using i cpl by auto
      have jl: "j < length (af_vstack st)" "Suc j < length (af_vstack st)" using j cpl by auto
      have "(af_vstack st ! i = af_vstack st ! j \<and> af_vstack st ! Suc i = af_vstack st ! Suc j) \<or>
            (af_vstack st ! i = af_vstack st ! Suc j \<and> af_vstack st ! Suc i = af_vstack st ! j)"
        using si by (auto simp: doubleton_eq_iff)
      thus False
      proof
        assume "af_vstack st ! i = af_vstack st ! j \<and> af_vstack st ! Suc i = af_vstack st ! Suc j"
        hence "i = j" using il jl dP nth_eq_iff_index_eq by blast
        thus False using ne by simp
      next
        assume "af_vstack st ! i = af_vstack st ! Suc j \<and> af_vstack st ! Suc i = af_vstack st ! j"
        hence "i = Suc j" and "Suc i = j" using il jl dP nth_eq_iff_index_eq by blast+
        thus False by simp
      qed
    qed
  qed
qed

lemma a_notin_estack_selfloop:
  assumes A2: "AF_invar_2 st" and A3: "AF_invar_3 st" and loop: "fst a = snd a"
  shows "a \<notin> set (af_estack st)"
proof
  assume "a \<in> set (af_estack st)"
  then obtain i where i: "i < length (af_estack st)" and ai: "af_estack st ! i = a"
    by (metis in_set_conv_nth)
  have "{fst a, snd a} = {af_vstack st ! i, af_vstack st ! Suc i}"
    using trail_endpoints[OF A3 i] ai by simp
  hence eqv: "af_vstack st ! i = af_vstack st ! Suc i" using loop by auto
  have dP: "distinct (af_vstack st)" and cpl: "Suc (length (af_estack st)) = length (af_vstack st)"
    using A2 i by (auto simp: AF_invar_2_def)
  have "i < length (af_vstack st)" "Suc i < length (af_vstack st)" using i cpl by auto
  hence "i = Suc i" using eqv dP nth_eq_iff_index_eq by blast
  thus False by simp
qed

lemma a_notin_estack_incident:
  assumes A2: "AF_invar_2 st" and A3: "AF_invar_3 st"
    and inc: "hd (af_vstack st) \<in> {fst a, snd a}"
    and ne: "af_vstack st \<noteq> []"
    and notparent: "\<not> (af_estack st \<noteq> [] \<and> a = hd (af_estack st))"
  shows "a \<notin> set (af_estack st)"
proof
  assume "a \<in> set (af_estack st)"
  then obtain j where j: "j < length (af_estack st)" and aj: "af_estack st ! j = a"
    by (metis in_set_conv_nth)
  have es_ne: "af_estack st \<noteq> []" using j by auto
  have dP: "distinct (af_vstack st)" and cpl: "Suc (length (af_estack st)) = length (af_vstack st)"
    using A2 j by (auto simp: AF_invar_2_def)
  have j1: "j \<noteq> 0"
  proof
    assume "j = 0"
    hence "a = hd (af_estack st)" using aj es_ne by (simp add: hd_conv_nth)
    thus False using notparent es_ne by simp
  qed
  have sj: "{fst a, snd a} = {af_vstack st ! j, af_vstack st ! Suc j}"
    using trail_endpoints[OF A3 j] aj by simp
  have "hd (af_vstack st) = af_vstack st ! 0" using ne by (simp add: hd_conv_nth)
  with inc sj have "af_vstack st ! 0 = af_vstack st ! j \<or> af_vstack st ! 0 = af_vstack st ! Suc j" by auto
  moreover have "0 < length (af_vstack st)" "j < length (af_vstack st)" "Suc j < length (af_vstack st)"
    using ne j cpl by auto
  ultimately have "0 = j \<or> 0 = Suc j" using dP nth_eq_iff_index_eq by blast
  thus False using j1 by simp
qed

text \<open>State-level flow invariants: the stack arcs are edges, the flow is feasible, and every stack arc is
      free. Feasibility uses D1; freeness uses D2
      (@{thm [source] af_cancel_seg_survivor_free}) for the surviving cancelled segment and the guard\<open>\<Leftrightarrow>\<close>free
      equivalence for the push. All three are preserved across @{const af_handle} given the E1 incidence
      (@{term \<open>a \<in> \<E>\<close>} and @{term \<open>(if dir then fst a else snd a) = hd (af_vstack st)\<close>}).\<close>

definition "AF_invar_estE st \<longleftrightarrow> set (af_estack st) \<subseteq> \<E>"

lemma af_handle_invar_estE:
  assumes AE: "AF_invar_estE st" and ae: "a \<in> \<E>"
  shows "AF_invar_estE (af_handle st a dir)"
proof -
  obtain up dn where updn: "af_rooms (af_flow st) a = (up, dn)"
    by (cases "af_rooms (af_flow st) a") auto
  show ?thesis
  proof (cases "fst a = snd a")
    case selfl: True
    have "af_handle st a dir = af_selfloop_handle st a" using selfl by (simp add: af_handle_real[OF ae])
    thus ?thesis using AE by (simp add: AF_invar_estE_def)
  next
    case selfloop: False
    show ?thesis
    proof (cases "0 < dn \<and> (up = - 1 \<or> 0 < up)")
      case False thus ?thesis using AE updn selfloop by (simp add: af_handle_real[OF ae] Let_def)
    next
      case guard: True
      show ?thesis
      proof (cases "af_estack st \<noteq> [] \<and> a = hd (af_estack st)")
        case True
        have "af_handle st a dir = st"
          unfolding af_handle_real[OF ae]
          using updn guard selfloop True by (simp add: Let_def)
        thus ?thesis using AE by (simp add: AF_invar_estE_def)
      next
        case parent: False
        show ?thesis
        proof (cases "st_lookup (af_state st) (if dir then snd a else fst a)")
          case Unseen
          have "af_handle st a dir = st\<lparr>af_vstack := (if dir then snd a else fst a) # af_vstack st,
              af_state := st_upd (af_state st) (if dir then snd a else fst a) OnStack,
              af_estack := a # af_estack st, af_dstack := dir # af_dstack st\<rparr>"
            using updn guard selfloop parent Unseen by (auto simp: af_handle_real[OF ae] Let_def)
          thus ?thesis using AE ae by (simp add: AF_invar_estE_def)
        next
          case OnStack
          obtain fl m' ubd where c: "af_cancel_seg up dn (if dir then snd a else fst a)
              (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) = (fl, m', ubd)"
            by (metis prod_cases3)
          show ?thesis
          proof (cases ubd)
            case True
            have "af_handle st a dir = st\<lparr>af_unbounded := True\<rparr>"
              using updn guard selfloop parent OnStack c True by (auto simp: af_handle_real[OF ae] Let_def)
            thus ?thesis using AE by (simp add: AF_invar_estE_def)
          next
            case False
            have red: "af_handle st a dir = af_reset_unsee_seg m' (af_vstack st)
                (st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st),
                    af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>)"
              using updn guard selfloop parent OnStack c False by (auto simp: af_handle_real[OF ae] Let_def)
            have "set (drop m' (af_estack st)) \<subseteq> \<E>"
              using AE set_drop_subset[of m' "af_estack st"] by (auto simp: AF_invar_estE_def)
            thus ?thesis using red by (simp add: AF_invar_estE_def)
          qed
        next
          case Finished
          thus ?thesis using AE updn guard selfloop parent by (auto simp: af_handle_real[OF ae] Let_def)
        qed
      qed
    qed
  qed
qed

definition "AF_invar_feas st \<longleftrightarrow> af_cap_feasible (af_flow st)"

lemma af_handle_invar_feas:
  assumes A1: "AF_invar_1 st" and A2: "AF_invar_2 st" and A3: "AF_invar_3 st"
    and Afe: "AF_invar_feas st" and AE: "AF_invar_estE st"
    and ae: "a \<in> \<E>"
    and inc: "(if dir then fst a else snd a) = hd (af_vstack st)" and ne: "af_vstack st \<noteq> []"
  shows "AF_invar_feas (af_handle st a dir)"
proof -
  have fi: "flow_invar (af_flow st)" using A1 by (auto simp: AF_invar_1_def)
  have feas: "af_cap_feasible (af_flow st)" using Afe by (simp add: AF_invar_feas_def)
  have estE: "set (af_estack st) \<subseteq> \<E>" using AE by (simp add: AF_invar_estE_def)
  have inc': "hd (af_vstack st) \<in> {fst a, snd a}" using inc by (cases dir) auto
  obtain up dn where updn: "af_rooms (af_flow st) a = (up, dn)"
    by (cases "af_rooms (af_flow st) a") auto
  show ?thesis
  proof (cases "fst a = snd a")
    case selfl: True
    have "af_handle st a dir = af_selfloop_handle st a" using selfl by (simp add: af_handle_real[OF ae])
    thus ?thesis using af_selfloop_handle_feasible[OF ae fi feas] by (simp add: AF_invar_feas_def)
  next
    case selfloop: False
    show ?thesis
    proof (cases "0 < dn \<and> (up = - 1 \<or> 0 < up)")
      case False thus ?thesis using Afe updn selfloop by (simp add: af_handle_real[OF ae] AF_invar_feas_def Let_def)
    next
      case guard: True
      show ?thesis
      proof (cases "af_estack st \<noteq> [] \<and> a = hd (af_estack st)")
        case True
        have "af_handle st a dir = st"
          unfolding af_handle_real[OF ae]
          using updn guard selfloop True by (simp add: Let_def)
        thus ?thesis using Afe by (simp add: AF_invar_feas_def)
      next
        case parent: False
        show ?thesis
        proof (cases "st_lookup (af_state st) (if dir then snd a else fst a)")
          case Unseen
          have "af_handle st a dir = st\<lparr>af_vstack := (if dir then snd a else fst a) # af_vstack st,
              af_state := st_upd (af_state st) (if dir then snd a else fst a) OnStack,
              af_estack := a # af_estack st, af_dstack := dir # af_dstack st\<rparr>"
            using updn guard selfloop parent Unseen by (auto simp: af_handle_real[OF ae] Let_def)
          thus ?thesis using feas by (simp add: AF_invar_feas_def)
        next
          case OnStack
          obtain fl m' ubd where c: "af_cancel_seg up dn (if dir then snd a else fst a)
              (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) = (fl, m', ubd)"
            by (metis prod_cases3)
          have dist: "distinct (a # af_estack st)"
            using a_notin_estack_incident[OF A2 A3 inc' ne parent] estack_distinct[OF A2 A3] by simp
          have "af_cap_feasible fl"
            using af_cancel_seg_feasible_gen[OF feas fi dist ae estE updn c] .
          then show ?thesis
          proof (cases ubd)
            case True
            have "af_handle st a dir = st\<lparr>af_unbounded := True\<rparr>"
              using updn guard selfloop parent OnStack c True by (auto simp: af_handle_real[OF ae] Let_def)
            thus ?thesis using feas by (simp add: AF_invar_feas_def)
          next
            case False
            have red: "af_handle st a dir = af_reset_unsee_seg m' (af_vstack st)
                (st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st),
                    af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>)"
              using updn guard selfloop parent OnStack c False by (auto simp: af_handle_real[OF ae] Let_def)
            thus ?thesis using \<open>af_cap_feasible fl\<close> by (simp add: AF_invar_feas_def)
          qed
        next
          case Finished
          thus ?thesis using Afe updn guard selfloop parent by (auto simp: af_handle_real[OF ae] Let_def AF_invar_feas_def)
        qed
      qed
    qed
  qed
qed

definition "AF_invar_free st \<longleftrightarrow> (\<forall>b\<in>set (af_estack st). af_arc_free (af_flow st) b)"

lemma af_handle_invar_free:
  assumes A1: "AF_invar_1 st" and A2: "AF_invar_2 st" and A3: "AF_invar_3 st"
    and Afe: "AF_invar_feas st" and Afr: "AF_invar_free st" and AinE: "AF_invar_estE st"
    and ae: "a \<in> \<E>"
    and inc: "(if dir then fst a else snd a) = hd (af_vstack st)" and ne: "af_vstack st \<noteq> []"
  shows "AF_invar_free (af_handle st a dir)"
proof -
  have fi: "flow_invar (af_flow st)" using A1 by (auto simp: AF_invar_1_def)
  have feas: "af_cap_feasible (af_flow st)" using Afe by (simp add: AF_invar_feas_def)
  have fr: "\<forall>b\<in>set (af_estack st). af_arc_free (af_flow st) b" using Afr by (simp add: AF_invar_free_def)
  have distES: "distinct (af_estack st)" using estack_distinct[OF A2 A3] .
  have inc': "hd (af_vstack st) \<in> {fst a, snd a}" using inc by (cases dir) auto
  obtain up dn where updn: "af_rooms (af_flow st) a = (up, dn)"
    by (cases "af_rooms (af_flow st) a") auto
  show ?thesis
  proof (cases "fst a = snd a")
    case selfl: True
    have ane: "a \<notin> set (af_estack st)" using a_notin_estack_selfloop[OF A2 A3 selfl] .
    have ha: "af_handle st a dir = af_selfloop_handle st a" using selfl by (simp add: af_handle_real[OF ae])
    have "\<forall>b\<in>set (af_estack st). af_arc_free (af_flow (af_selfloop_handle st a)) b"
    proof
      fix b assume b: "b \<in> set (af_estack st)"
      hence bne: "b \<noteq> a" using ane by auto
      have "flow_lookup (af_flow (af_selfloop_handle st a)) b = flow_lookup (af_flow st) b"
        using af_selfloop_handle_flow_off[OF ae fi bne] .
      thus "af_arc_free (af_flow (af_selfloop_handle st a)) b" using b fr by (auto simp: af_arc_free_def)
    qed
    thus ?thesis using ha by (simp add: AF_invar_free_def)
  next
    case selfloop: False
    show ?thesis
    proof (cases "0 < dn \<and> (up = - 1 \<or> 0 < up)")
      case False thus ?thesis using Afr updn selfloop by (simp add: af_handle_real[OF ae] AF_invar_free_def Let_def)
    next
      case guard: True
      have afree: "af_arc_free (af_flow st) a"
      proof -
        have "cap a = - 1 \<or> flow_lookup (af_flow st) a \<le> cap a" using feas ae by (auto simp: af_cap_feasible_def)
        thus ?thesis using af_guard_free[OF updn] guard by simp
      qed
      show ?thesis
      proof (cases "af_estack st \<noteq> [] \<and> a = hd (af_estack st)")
        case True
        have "af_handle st a dir = st"
          unfolding af_handle_real[OF ae]
          using updn guard selfloop True by (simp add: Let_def)
        thus ?thesis using Afr by (simp add: AF_invar_free_def)
      next
        case parent: False
        have ane: "a \<notin> set (af_estack st)" using a_notin_estack_incident[OF A2 A3 inc' ne parent] .
        show ?thesis
        proof (cases "st_lookup (af_state st) (if dir then snd a else fst a)")
          case Unseen
          have "af_handle st a dir = st\<lparr>af_vstack := (if dir then snd a else fst a) # af_vstack st,
              af_state := st_upd (af_state st) (if dir then snd a else fst a) OnStack,
              af_estack := a # af_estack st, af_dstack := dir # af_dstack st\<rparr>"
            using updn guard selfloop parent Unseen by (auto simp: af_handle_real[OF ae] Let_def)
          thus ?thesis using afree fr by (simp add: AF_invar_free_def)
        next
          case OnStack
          obtain fl m' ubd where c: "af_cancel_seg up dn (if dir then snd a else fst a)
              (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) = (fl, m', ubd)"
            by (metis prod_cases3)
          have survfree: "\<forall>b\<in>set (drop m' (af_estack st)). af_arc_free fl b"
          proof
            fix b assume "b \<in> set (drop m' (af_estack st))"
            then obtain i where "i < length (drop m' (af_estack st))" and bi: "drop m' (af_estack st) ! i = b"
              by (metis in_set_conv_nth)
            hence jl: "m' + i < length (af_estack st)" and beq: "b = af_estack st ! (m' + i)"
              by auto
            show "af_arc_free fl b"
              using af_cancel_seg_survivor_free 
                    fi distES fr ane c jl beq  AF_invar_estE_def AinE ae le_add1 
              by(auto simp add: AF_invar_estE_def)
          qed
          show ?thesis
          proof (cases ubd)
            case True
            have "af_handle st a dir = st\<lparr>af_unbounded := True\<rparr>"
              using updn guard selfloop parent OnStack c True by (auto simp: af_handle_real[OF ae] Let_def)
            thus ?thesis using Afr by (simp add: AF_invar_free_def)
          next
            case False
            have red: "af_handle st a dir = af_reset_unsee_seg m' (af_vstack st)
                (st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st),
                    af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>)"
              using updn guard selfloop parent OnStack c False by (auto simp: af_handle_real[OF ae] Let_def)
            thus ?thesis using survfree by (simp add: AF_invar_free_def)
          qed
        next
          case Finished
          thus ?thesis using Afr updn guard selfloop parent by (auto simp: af_handle_real[OF ae] Let_def AF_invar_free_def)
        qed
      qed
    qed
  qed
qed

text \<open>Dual of the survivor lemma (towards the free-set \emph{strictly} shrinking): when the drop count is
      positive, the deepest dropped arc (index @{term \<open>m' - 1\<close>}) is the one that saturated, hence is no
      longer free. Together with @{thm [source] af_push_survivor} this pinpoints the boundary at @{term \<open>m'\<close>}.\<close>

lemma af_push_saturated_at:
  "set es \<subseteq> \<E> \<Longrightarrow> flow_invar fl \<Longrightarrow> distinct es \<Longrightarrow>
   af_push \<gamma> x vs es ds flip fl = (fl', m') \<Longrightarrow> 0 < m' \<Longrightarrow>
   \<not> af_arc_free fl' (es ! (m' - 1))"
proof (induction \<gamma> x vs es ds flip fl arbitrary: fl' m' rule: af_push.induct)
  case (1 \<gamma> x u v1 vs a es d ds flip fl)
  obtain fl1 f where p1: "af_push_arc \<gamma> a (d \<noteq> flip) fl = (fl1, f)" by fastforce
  have adist: "a \<notin> set es" using 1 by auto
  have fi1: "flow_invar fl1" using 1(2,3) af_push_arc_flow_invar[OF _ p1]
    by simp
  show ?case
  proof (cases "v1 = x")
    case True
    from True 1(4,3,5) p1 have fl'eq: "fl' = fl1" and m'eq: "m' = (if af_saturated f a then 1 else 0)"
      by (auto simp: Let_def) 
    have "af_saturated f a" using 1(5,6) m'eq by (auto split: if_splits) 
    hence "m' = 1" using m'eq by simp
    thus ?thesis using fl'eq \<open>af_saturated f a\<close> af_saturated_notfree 1 p1 by simp
  next
    case False
    obtain fl2 r where p2: "af_push \<gamma> x (v1 # vs) es ds flip fl1 = (fl2, r)" by fastforce
    from False 1 p1 p2 have fl'eq: "fl' = fl2"
      and m'eq: "m' = (if r \<noteq> 0 then Suc r else (if af_saturated f a then 1 else 0))"
      by (auto simp: Let_def)
    have des: "distinct es" using 1 by simp
    show ?thesis
    proof (cases "r = 0")
      case True
      hence msat: "m' = (if af_saturated f a then 1 else 0)" using m'eq by simp
      have "af_saturated f a" using 1 msat by (auto split: if_splits)
      hence m1: "m' = 1" using msat by simp
      have "flow_lookup fl2 a = flow_lookup fl1 a" 
        using af_push_flow_off fi1 adist p2 "1.prems"(1) by auto
      hence "\<not> af_arc_free fl2 a"
        using af_saturated_notfree 1 p1 \<open>af_saturated f a\<close> by (auto simp: af_arc_free_def)
      thus ?thesis using m1 fl'eq by simp
    next
      case False
      hence m'eq2: "m' = Suc r" using m'eq by simp
      hence rpos: "0 < r" using False by simp
      have IH: "\<not> af_arc_free fl2 (es ! (r - 1))"
        using 1 p1[symmetric]  refl \<open>v1 \<noteq> x\<close> fi1 des p2 rpos  by auto
      have "(a # es) ! (m' - 1) = es ! (r - 1)" using m'eq2 rpos by (cases r) auto
      thus ?thesis using IH fl'eq by simp
    qed
  qed
qed auto

text \<open>The scanned bottleneck @{term ra} is \emph{achieved}: it is either the seed @{term ra0} (the closing
      arc's room) or the as-is room of some walked arc (@{const af_min} always returns one of its arguments).
      With @{thm [source] af_push_survivor} (when @{term \<open>m' = 0\<close>} every walked arc stays free, so none had
      room @{term ra}) this forces @{term \<open>ra = ra0\<close>} in the @{term \<open>m' = 0\<close>} branch --- i.e.\ the closing
      arc is the bottleneck and saturates, so a cancellation always removes at least one free arc.\<close>

text \<open>When the drop count is @{term 0} the bottleneck equals the closing arc's seed room (no walked arc
      is tighter, else it would have saturated and raised @{term \<open>m'\<close>}); so pushing @{term \<gamma>} onto the
      closing arc pushes it by exactly its own room and saturates it.\<close>

text \<open>Theme D2, top level: a (non-flag) cancellation removes at least one free arc and never creates one,
      so the free set strictly shrinks --- the well-founded key for termination.\<close>

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

lemma remaining_out_finite:
  assumes mi: "multigraph_inv oa ia" and v: "v \<in> \<V>"
  shows "finite (out_remaining oa v)"
proof -
  have oi: "out_invar oa" and ab: "out_abstract oa v = \<delta>\<^sup>+ v"
    using mi v by (auto simp: multigraph_inv_def out_graph_inv_def)
  have "out_remaining oa v \<subseteq> out_abstract oa v" using outg.idx_partition_union[OF oi v] by blast
  thus ?thesis using ab delta_plus_finite by (auto intro: finite_subset)
qed

lemma remaining_in_finite:
  assumes mi: "multigraph_inv oa ia" and v: "v \<in> \<V>"
  shows "finite (in_remaining ia v)"
proof -
  have ii: "in_invar ia" and ab: "in_abstract ia v = \<delta>\<^sup>- v"
    using mi v by (auto simp: multigraph_inv_def in_graph_inv_def)
  have "in_remaining ia v \<subseteq> in_abstract ia v" using ing.idx_partition_union[OF ii v] by blast
  thus ?thesis using ab delta_minus_finite by (auto intro: finite_subset)
qed

lemma out_move_card:
  assumes oi: "out_invar C" and ne: "out_remaining C v \<noteq> {}" 
  and fin: "finite (out_remaining C v)" and v: "v \<in> \<V>"
  shows "card (out_remaining (out_move C v) v) = card (out_remaining C v) - 1"
  using outg.idx_move_remaining[OF oi v ne] oi ne outg.idx_current[OF oi v ne] fin
  by (simp add: card_Diff_singleton)

lemma in_move_card:
  assumes ii: "in_invar C" and ne: "in_remaining C v \<noteq> {}" 
   and fin: "finite (in_remaining C v)" and v: "v \<in> \<V>"
  shows "card (in_remaining (in_move C v) v) = card (in_remaining C v) - 1"
  using ing.idx_move_remaining[OF ii v ne] ing.idx_current[OF ii v ne] fin
  by (simp add: card_Diff_singleton)

definition "af_iterrem st =
  (\<Sum>v\<in>\<V>. card (out_remaining (af_out_arr st) v)
           + card (in_remaining (af_in_arr st) v))"

lemma af_iterrem_out_advance:
  assumes mi: "multigraph_inv (af_out_arr st) (af_in_arr st)" and v: "v \<in> \<V>"
    and he: "out_has (af_out_arr st) v"
  shows "af_iterrem (st\<lparr>af_out_arr := out_move (af_out_arr st) v\<rparr>) + 1 = af_iterrem st"
proof -
  define oa where "oa = af_out_arr st"
  define ia where "ia = af_in_arr st"
  have ao: "out_invar oa" using mi by (auto simp: multigraph_inv_def out_graph_inv_def oa_def)
  have hev: "out_has oa v" using he by (simp add: oa_def)
  have ne: "out_remaining oa v \<noteq> {}" using hev by (simp add: outg.idx_has[OF ao v])
  have finrem: "finite (out_remaining oa v)" using remaining_out_finite[OF mi v] by (simp add: oa_def)
  have cardpos: "0 < card (out_remaining oa v)" using ne finrem by (simp add: card_gt_0_iff)
  let ?oa' = "out_move oa v"
  let ?f = "\<lambda>w. card (out_remaining oa w) + card (in_remaining ia w)"
  let ?f' = "\<lambda>w. card (out_remaining ?oa' w) + card (in_remaining ia w)"
  have fv': "?f' v + 1 = ?f v"
    using out_move_card[OF ao ne finrem v] cardpos by simp
  have cong: "(\<Sum>w\<in>\<V>-{v}. ?f' w) = (\<Sum>w\<in>\<V>-{v}. ?f w)"
    by (rule sum.cong[OF refl]) (simp add: outg.idx_move_remaining_other[OF ao v ne])
  have "af_iterrem (st\<lparr>af_out_arr := ?oa'\<rparr>) + 1 = (\<Sum>w\<in>\<V>. ?f' w) + 1"
    by (simp add: af_iterrem_def oa_def ia_def)
  also have "\<dots> = (?f' v + (\<Sum>w\<in>\<V>-{v}. ?f' w)) + 1" by (subst sum.remove[OF \<V>_finite v]) simp
  also have "\<dots> = (?f' v + 1) + (\<Sum>w\<in>\<V>-{v}. ?f w)" using cong by simp
  also have "\<dots> = ?f v + (\<Sum>w\<in>\<V>-{v}. ?f w)" using fv' by simp
  also have "\<dots> = (\<Sum>w\<in>\<V>. ?f w)" by (subst sum.remove[OF \<V>_finite v]) simp
  also have "\<dots> = af_iterrem st" by (simp add: af_iterrem_def oa_def ia_def)
  finally show ?thesis by (simp add: oa_def)
qed

lemma af_iterrem_in_advance:
  assumes mi: "multigraph_inv (af_out_arr st) (af_in_arr st)" and v: "v \<in> \<V>"
    and he: "in_has (af_in_arr st) v"
  shows "af_iterrem (st\<lparr>af_in_arr := in_move (af_in_arr st) v\<rparr>) + 1 = af_iterrem st"
proof -
  define oa where "oa = af_out_arr st"
  define ia where "ia = af_in_arr st"
  have ai: "in_invar ia" using mi by (auto simp: multigraph_inv_def in_graph_inv_def ia_def)
  have hev: "in_has ia v" using he by (simp add: ia_def)
  have ne: "in_remaining ia v \<noteq> {}" using hev by (simp add: ing.idx_has[OF ai v])
  have finrem: "finite (in_remaining ia v)" using remaining_in_finite[OF mi v] by (simp add: ia_def)
  have cardpos: "0 < card (in_remaining ia v)" using ne finrem by (simp add: card_gt_0_iff)
  let ?ia' = "in_move ia v"
  let ?f = "\<lambda>w. card (out_remaining oa w) + card (in_remaining ia w)"
  let ?f' = "\<lambda>w. card (out_remaining oa w) + card (in_remaining ?ia' w)"
  have fv': "?f' v + 1 = ?f v"
    using in_move_card[OF ai ne finrem v] cardpos by simp
  have cong: "(\<Sum>w\<in>\<V>-{v}. ?f' w) = (\<Sum>w\<in>\<V>-{v}. ?f w)"
    by (rule sum.cong[OF refl]) (simp add: ing.idx_move_remaining_other[OF ai v ne])
  have "af_iterrem (st\<lparr>af_in_arr := ?ia'\<rparr>) + 1 = (\<Sum>w\<in>\<V>. ?f' w) + 1"
    by (simp add: af_iterrem_def oa_def ia_def)
  also have "\<dots> = (?f' v + (\<Sum>w\<in>\<V>-{v}. ?f' w)) + 1" by (subst sum.remove[OF \<V>_finite v]) simp
  also have "\<dots> = (?f' v + 1) + (\<Sum>w\<in>\<V>-{v}. ?f w)" using cong by simp
  also have "\<dots> = ?f v + (\<Sum>w\<in>\<V>-{v}. ?f w)" using fv' by simp
  also have "\<dots> = (\<Sum>w\<in>\<V>. ?f w)" by (subst sum.remove[OF \<V>_finite v]) simp
  also have "\<dots> = af_iterrem st" by (simp add: af_iterrem_def oa_def ia_def)
  finally show ?thesis by (simp add: ia_def)
qed

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

lemma AF_invar_estE_holds_1:
  assumes conds: "AF_DFS_call_1_conds st" and AE: "AF_invar_estE st"
    and Aiter: "AF_invar_iter st" and AV: "AF_invar_V st"
  shows "AF_invar_estE (AF_DFS_upd1 st)"
proof -
  from conds have ne: "af_vstack st \<noteq> []" and he: "out_has (af_out_arr st) (hd (af_vstack st))"
    by (auto elim!: call_cond_elims)
  have vV: "hd (af_vstack st) \<in> \<V>" using AV ne hd_in_set by (auto simp: AF_invar_V_def)
  have ae: "out_current (af_out_arr st) (hd (af_vstack st)) \<in> \<E>"
    using af_current_out_endpoint[OF _ vV he] Aiter by (auto simp: AF_invar_iter_def)
  have AE': "AF_invar_estE (st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack st))\<rparr>)" using AE by simp
  show ?thesis unfolding AF_DFS_upd1_def Let_def by (rule af_handle_invar_estE[OF AE' ae])
qed

lemma AF_invar_estE_holds_2:
  assumes conds: "AF_DFS_call_2_conds st" and AE: "AF_invar_estE st"
    and Aiter: "AF_invar_iter st" and AV: "AF_invar_V st"
  shows "AF_invar_estE (AF_DFS_upd2 st)"
proof -
  from conds have ne: "af_vstack st \<noteq> []" and he: "in_has (af_in_arr st) (hd (af_vstack st))"
    by (auto elim!: call_cond_elims)
  have vV: "hd (af_vstack st) \<in> \<V>" using AV ne hd_in_set by (auto simp: AF_invar_V_def)
  have ae: "in_current (af_in_arr st) (hd (af_vstack st)) \<in> \<E>"
    using af_current_in_endpoint[OF _ vV he] Aiter by (auto simp: AF_invar_iter_def)
  have AE': "AF_invar_estE (st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack st))\<rparr>)" using AE by simp
  show ?thesis unfolding AF_DFS_upd2_def Let_def by (rule af_handle_invar_estE[OF AE' ae])
qed

lemma AF_invar_estE_holds_3:
  "AF_DFS_call_3_conds st \<Longrightarrow> AF_invar_estE st \<Longrightarrow> AF_invar_estE (AF_DFS_upd3 st)"
  by (cases "af_estack st") (auto simp: AF_DFS_upd3_def AF_invar_estE_def)

lemma AF_invar_feas_holds_1:
  assumes conds: "AF_DFS_call_1_conds st"
    and A1: "AF_invar_1 st" and A2: "AF_invar_2 st" and A3: "AF_invar_3 st"
    and Afe: "AF_invar_feas st" and AE: "AF_invar_estE st" and Aiter: "AF_invar_iter st" and AV: "AF_invar_V st"
  shows "AF_invar_feas (AF_DFS_upd1 st)"
proof -
  from conds have ne: "af_vstack st \<noteq> []" and he: "out_has (af_out_arr st) (hd (af_vstack st))"
    by (auto elim!: call_cond_elims)
  have vV: "hd (af_vstack st) \<in> \<V>" using AV ne hd_in_set by (auto simp: AF_invar_V_def)
  have endp: "fst (out_current (af_out_arr st) (hd (af_vstack st))) = hd (af_vstack st) \<and>
              out_current (af_out_arr st) (hd (af_vstack st)) \<in> \<E>"
    using af_current_out_endpoint[OF _ vV he] Aiter by (auto simp: AF_invar_iter_def)
  let ?st' = "st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack st))\<rparr>"
  have A1': "AF_invar_1 ?st'" using vV by (rule AF_invar_1_out_advance[OF _ A1])
  have inc: "(if True then fst (out_current (af_out_arr st) (hd (af_vstack st)))
             else snd (out_current (af_out_arr st) (hd (af_vstack st)))) = hd (af_vstack ?st')"
    using endp by simp
  show ?thesis unfolding AF_DFS_upd1_def Let_def
    by (rule af_handle_invar_feas[OF A1' _ _ _ _ _ inc _]) (use A2 A3 Afe AE endp ne in simp_all)
qed

lemma AF_invar_feas_holds_2:
  assumes conds: "AF_DFS_call_2_conds st"
    and A1: "AF_invar_1 st" and A2: "AF_invar_2 st" and A3: "AF_invar_3 st"
    and Afe: "AF_invar_feas st" and AE: "AF_invar_estE st" and Aiter: "AF_invar_iter st" and AV: "AF_invar_V st"
  shows "AF_invar_feas (AF_DFS_upd2 st)"
proof -
  from conds have ne: "af_vstack st \<noteq> []" and he: "in_has (af_in_arr st) (hd (af_vstack st))"
    by (auto elim!: call_cond_elims)
  have vV: "hd (af_vstack st) \<in> \<V>" using AV ne hd_in_set by (auto simp: AF_invar_V_def)
  have endp: "snd (in_current (af_in_arr st) (hd (af_vstack st))) = hd (af_vstack st) \<and>
              in_current (af_in_arr st) (hd (af_vstack st)) \<in> \<E>"
    using af_current_in_endpoint[OF _ vV he] Aiter by (auto simp: AF_invar_iter_def)
  let ?st' = "st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack st))\<rparr>"
  have A1': "AF_invar_1 ?st'" using vV by (rule AF_invar_1_in_advance[OF _ A1])
  have inc: "(if False then fst (in_current (af_in_arr st) (hd (af_vstack st)))
             else snd (in_current (af_in_arr st) (hd (af_vstack st)))) = hd (af_vstack ?st')"
    using endp by simp
  show ?thesis unfolding AF_DFS_upd2_def Let_def
    by (rule af_handle_invar_feas[OF A1' _ _ _ _ _ inc _]) (use A2 A3 Afe AE endp ne in simp_all)
qed

lemma AF_invar_feas_holds_3:
  assumes conds: "AF_DFS_call_3_conds st" and Afe: "AF_invar_feas st"
  shows "AF_invar_feas (AF_DFS_upd3 st)"
  using Afe by (simp add: AF_DFS_upd3_def AF_invar_feas_def)

lemma AF_invar_free_holds_1:
  assumes conds: "AF_DFS_call_1_conds st"
    and A1: "AF_invar_1 st" and A2: "AF_invar_2 st" and A3: "AF_invar_3 st"
    and Afe: "AF_invar_feas st" and Afr: "AF_invar_free st" and Aiter: "AF_invar_iter st" 
    and AV: "AF_invar_V st" and AE: "AF_invar_estE st"
  shows "AF_invar_free (AF_DFS_upd1 st)"
proof -
  from conds have ne: "af_vstack st \<noteq> []" and he: "out_has (af_out_arr st) (hd (af_vstack st))"
    by (auto elim!: call_cond_elims)
  have vV: "hd (af_vstack st) \<in> \<V>" using AV ne hd_in_set by (auto simp: AF_invar_V_def)
  have endp: "fst (out_current (af_out_arr st) (hd (af_vstack st))) = hd (af_vstack st) \<and>
              out_current (af_out_arr st) (hd (af_vstack st)) \<in> \<E>"
    using af_current_out_endpoint[OF _ vV he] Aiter by (auto simp: AF_invar_iter_def)
  let ?st' = "st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack st))\<rparr>"
  have A1': "AF_invar_1 ?st'" using vV by (rule AF_invar_1_out_advance[OF _ A1])
  have inc: "(if True then fst (out_current (af_out_arr st) (hd (af_vstack st)))
             else snd (out_current (af_out_arr st) (hd (af_vstack st)))) = hd (af_vstack ?st')"
    using endp by simp
  show ?thesis 
    using AE A2 A3 Afe Afr endp ne
    unfolding AF_DFS_upd1_def Let_def
    by (auto intro!: af_handle_invar_free[OF A1' _ _ _ _ _ _ inc _])
qed

lemma AF_invar_free_holds_2:
  assumes conds: "AF_DFS_call_2_conds st"
    and A1: "AF_invar_1 st" and A2: "AF_invar_2 st" and A3: "AF_invar_3 st"
    and Afe: "AF_invar_feas st" and Afr: "AF_invar_free st" and Aiter: "AF_invar_iter st" 
    and AV: "AF_invar_V st" and AE: "AF_invar_estE st"
  shows "AF_invar_free (AF_DFS_upd2 st)"
proof -
  from conds have ne: "af_vstack st \<noteq> []" and he: "in_has (af_in_arr st) (hd (af_vstack st))"
    by (auto elim!: call_cond_elims)
  have vV: "hd (af_vstack st) \<in> \<V>" using AV ne hd_in_set by (auto simp: AF_invar_V_def)
  have endp: "snd (in_current (af_in_arr st) (hd (af_vstack st))) = hd (af_vstack st) \<and>
              in_current (af_in_arr st) (hd (af_vstack st)) \<in> \<E>"
    using af_current_in_endpoint[OF _ vV he] Aiter by (auto simp: AF_invar_iter_def)
  let ?st' = "st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack st))\<rparr>"
  have A1': "AF_invar_1 ?st'" using vV by (rule AF_invar_1_in_advance[OF _ A1])
  have inc: "(if False then fst (in_current (af_in_arr st) (hd (af_vstack st)))
             else snd (in_current (af_in_arr st) (hd (af_vstack st)))) = hd (af_vstack ?st')"
    using endp by simp
  show ?thesis 
    using  A2 A3 Afe Afr endp ne AE
    by(auto simp add: AF_DFS_upd2_def Let_def
          intro!: af_handle_invar_free[OF A1' _ _ _ _ _ _ inc _]) 
qed

lemma AF_invar_free_holds_3:
  assumes conds: "AF_DFS_call_3_conds st" and A2: "AF_invar_2 st" and A3: "AF_invar_3 st" and Afr: "AF_invar_free st"
  shows "AF_invar_free (AF_DFS_upd3 st)"
proof -
  have "\<forall>b\<in>set (tl (af_estack st)). af_arc_free (af_flow st) b"
    using Afr by (cases "af_estack st") (auto simp: AF_invar_free_def)
  thus ?thesis by (simp add: AF_DFS_upd3_def AF_invar_free_def)
qed

text \<open>Combined single-step preservation of Themes A and B. Since @{const AF_invar_1}'s per-step
      preservation now needs the range facts that Theme E1 supplies for the scanned arc (and both
      themes share the same @{const af_handle} obligations), they are lifted jointly here, replacing the
      old per-invariant @{text AF_invar_1_holds_k}/@{text AF_invar_2_holds_k}.\<close>

lemma AF_invar_12_holds_1:
  assumes conds: "AF_DFS_call_1_conds st" and i1: "AF_invar_1 st" and i2: "AF_invar_2 st"
    and iit: "AF_invar_iter st" and iV: "AF_invar_V st" and iE: "AF_invar_estE st"
  shows "AF_invar_1 (AF_DFS_upd1 st) \<and> AF_invar_2 (AF_DFS_upd1 st)"
proof -
  from conds have ne: "af_vstack st \<noteq> []" and he: "out_has (af_out_arr st) (hd (af_vstack st))"
    by (auto elim!: call_cond_elims)
  have vV: "hd (af_vstack st) \<in> \<V>" using iV ne hd_in_set by (auto simp: AF_invar_V_def)
  have ae: "out_current (af_out_arr st) (hd (af_vstack st)) \<in> \<E>"
    using af_current_out_endpoint[OF _ vV he] iit by (auto simp: AF_invar_iter_def)
  let ?st1 = "st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack st))\<rparr>"
  have i1': "AF_invar_1 ?st1" using AF_invar_1_out_advance[OF vV i1] .
  have i2': "AF_invar_2 ?st1" using i2 by simp
  have vV': "set (af_vstack ?st1) \<subseteq> \<V>" using iV by (simp add: AF_invar_V_def)
  have eE': "set (af_estack ?st1) \<subseteq> \<E>" using iE by (simp add: AF_invar_estE_def)
  have ne': "af_vstack ?st1 \<noteq> []" using ne by simp
  have h1: "AF_invar_1 (af_handle ?st1 (out_current (af_out_arr st) (hd (af_vstack st))) True)"
    by (rule af_handle_invar_1[OF i1' ae eE' vV'])
  have h2: "AF_invar_2 (af_handle ?st1 (out_current (af_out_arr st) (hd (af_vstack st))) True)"
    by (rule af_handle_invar_2[OF i1' i2' ne' ae vV'])
  show ?thesis unfolding AF_DFS_upd1_def Let_def using h1 h2 by simp
qed

lemma AF_invar_12_holds_2:
  assumes conds: "AF_DFS_call_2_conds st" and i1: "AF_invar_1 st" and i2: "AF_invar_2 st"
    and iit: "AF_invar_iter st" and iV: "AF_invar_V st" and iE: "AF_invar_estE st"
  shows "AF_invar_1 (AF_DFS_upd2 st) \<and> AF_invar_2 (AF_DFS_upd2 st)"
proof -
  from conds have ne: "af_vstack st \<noteq> []" and he: "in_has (af_in_arr st) (hd (af_vstack st))"
    by (auto elim!: call_cond_elims)
  have vV: "hd (af_vstack st) \<in> \<V>" using iV ne hd_in_set by (auto simp: AF_invar_V_def)
  have ae: "in_current (af_in_arr st) (hd (af_vstack st)) \<in> \<E>"
    using af_current_in_endpoint[OF _ vV he] iit by (auto simp: AF_invar_iter_def)
  let ?st1 = "st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack st))\<rparr>"
  have i1': "AF_invar_1 ?st1" using AF_invar_1_in_advance[OF vV i1] .
  have i2': "AF_invar_2 ?st1" using i2 by simp
  have vV': "set (af_vstack ?st1) \<subseteq> \<V>" using iV by (simp add: AF_invar_V_def)
  have eE': "set (af_estack ?st1) \<subseteq> \<E>" using iE by (simp add: AF_invar_estE_def)
  have ne': "af_vstack ?st1 \<noteq> []" using ne by simp
  have h1: "AF_invar_1 (af_handle ?st1 (in_current (af_in_arr st) (hd (af_vstack st))) False)"
    by (rule af_handle_invar_1[OF i1' ae eE' vV'])
  have h2: "AF_invar_2 (af_handle ?st1 (in_current (af_in_arr st) (hd (af_vstack st))) False)"
    by (rule af_handle_invar_2[OF i1' i2' ne' ae vV'])
  show ?thesis unfolding AF_DFS_upd2_def Let_def using h1 h2 by simp
qed

lemma AF_invar_12_holds_3:
  assumes conds: "AF_DFS_call_3_conds st" and i1: "AF_invar_1 st" and i2: "AF_invar_2 st"
    and iV: "AF_invar_V st"
  shows "AF_invar_1 (AF_DFS_upd3 st) \<and> AF_invar_2 (AF_DFS_upd3 st)"
proof -
  from i1 have si: "st_invar (af_state st)" by (auto simp: AF_invar_1_def)
  from conds obtain v vs where vv: "af_vstack st = v # vs" by (auto elim!: call_cond_elims)
  have vV: "v \<in> \<V>" using iV vv by (auto simp: AF_invar_V_def)
  have inv1: "AF_invar_1 (AF_DFS_upd3 st)"
    using i1 vV vv by (auto simp: AF_DFS_upd3_def AF_invar_1_def st_upd_invar)
  from i2 vv have d: "distinct vs" and vni: "v \<notin> set vs"
    and cpl: "\<And>w. w \<in> \<V> \<Longrightarrow> (st_lookup (af_state st) w = OnStack) = (w \<in> set (v # vs))"
    and le: "length (af_estack st) = length vs" "length (af_dstack st) = length vs"
    by (auto simp: AF_invar_2_def)
  have inv2: "AF_invar_2 (AF_DFS_upd3 st)"
    unfolding AF_DFS_upd3_def
    apply (rule AF_invar_2I)
    subgoal using vv d by simp
    subgoal using vv le by (cases "af_estack st"; cases "af_dstack st"; cases vs; auto)
    subgoal for w using vv cpl vni si by (auto simp: state_arr.fixed_univ_map_upd[OF si vV])
    done
  show ?thesis using inv1 inv2 by simp
qed

definition "AF_inv st \<longleftrightarrow> AF_invar_1 st \<and> AF_invar_2 st \<and> AF_invar_3 st \<and> AF_invar_iter st \<and>
  AF_invar_V st \<and> AF_invar_estE st \<and> AF_invar_feas st \<and> AF_invar_free st"

lemma AF_inv_holds_1:
  assumes mi0: "multigraph_inv out_arr in_arr"
    and conds: "AF_DFS_call_1_conds st" and inv: "AF_inv st"
  shows "AF_inv (AF_DFS_upd1 st)"
proof -
  from inv have i1: "AF_invar_1 st" and i2: "AF_invar_2 st" and i3: "AF_invar_3 st"
    and iit: "AF_invar_iter st" and iV: "AF_invar_V st" and iE: "AF_invar_estE st"
    and ife: "AF_invar_feas st" and ifr: "AF_invar_free st" by (auto simp: AF_inv_def)
  show ?thesis unfolding AF_inv_def
    using AF_invar_12_holds_1[OF conds i1 i2 iit iV iE]
          AF_invar_3_holds_1[OF conds i1 i2 i3 iit iV] AF_invar_iter_holds_1[OF mi0 conds iit iV]
          AF_invar_V_holds_1[OF conds iV iit] AF_invar_estE_holds_1[OF conds iE iit iV]
          AF_invar_feas_holds_1[OF conds i1 i2 i3 ife iE iit iV]
          AF_invar_free_holds_1[OF conds i1 i2 i3 ife ifr iit iV iE]
    by blast
qed

lemma AF_inv_holds_2:
  assumes mi0: "multigraph_inv out_arr in_arr"
    and conds: "AF_DFS_call_2_conds st" and inv: "AF_inv st"
  shows "AF_inv (AF_DFS_upd2 st)"
proof -
  from inv have i1: "AF_invar_1 st" and i2: "AF_invar_2 st" and i3: "AF_invar_3 st"
    and iit: "AF_invar_iter st" and iV: "AF_invar_V st" and iE: "AF_invar_estE st"
    and ife: "AF_invar_feas st" and ifr: "AF_invar_free st" by (auto simp: AF_inv_def)
  show ?thesis unfolding AF_inv_def
    using AF_invar_12_holds_2[OF conds i1 i2 iit iV iE]
          AF_invar_3_holds_2[OF conds i1 i2 i3 iit iV] AF_invar_iter_holds_2[OF mi0 conds iit iV]
          AF_invar_V_holds_2[OF conds iV iit] AF_invar_estE_holds_2[OF conds iE iit iV]
          AF_invar_feas_holds_2[OF conds i1 i2 i3 ife iE iit iV]
          AF_invar_free_holds_2[OF conds i1 i2 i3 ife ifr iit iV iE]
    by blast
qed

lemma AF_inv_holds_3:
  assumes conds: "AF_DFS_call_3_conds st" and inv: "AF_inv st"
  shows "AF_inv (AF_DFS_upd3 st)"
proof -
  from inv have i1: "AF_invar_1 st" and i2: "AF_invar_2 st" and i3: "AF_invar_3 st"
    and iit: "AF_invar_iter st" and iV: "AF_invar_V st" and iE: "AF_invar_estE st"
    and ife: "AF_invar_feas st" and ifr: "AF_invar_free st" by (auto simp: AF_inv_def)
  show ?thesis unfolding AF_inv_def
    using AF_invar_12_holds_3[OF conds i1 i2 iV]
          AF_invar_3_holds_3[OF conds i2 i3] AF_invar_iter_holds_3[OF conds iit]
          AF_invar_V_holds_3[OF conds iV] AF_invar_estE_holds_3[OF conds iE]
          AF_invar_feas_holds_3[OF conds ife] AF_invar_free_holds_3[OF conds i2 i3 ifr]
    by blast
qed

lemma af_freeset_out_arr[simp]: "af_freeset (st\<lparr>af_out_arr := X\<rparr>) = af_freeset st"
  by (simp add: af_freeset_def)
lemma af_freeset_in_arr[simp]: "af_freeset (st\<lparr>af_in_arr := X\<rparr>) = af_freeset st"
  by (simp add: af_freeset_def)
lemma af_freeset_vstack[simp]: "af_freeset (st\<lparr>af_vstack := X\<rparr>) = af_freeset st"
  by (simp add: af_freeset_def)
lemma af_freeset_state[simp]: "af_freeset (st\<lparr>af_state := X\<rparr>) = af_freeset st"
  by (simp add: af_freeset_def)
lemma af_freeset_estack[simp]: "af_freeset (st\<lparr>af_estack := X\<rparr>) = af_freeset st"
  by (simp add: af_freeset_def)
lemma af_freeset_dstack[simp]: "af_freeset (st\<lparr>af_dstack := X\<rparr>) = af_freeset st"
  by (simp add: af_freeset_def)
lemma af_freeset_unbounded[simp]: "af_freeset (st\<lparr>af_unbounded := X\<rparr>) = af_freeset st"
  by (simp add: af_freeset_def)

subsection \<open>Capacity-agnostic cancellation saturation (dropping the finite-capacity assumption)\<close>

text \<open>The following are @{term \<open>\<forall>a. cap a \<noteq> - 1\<close>}-free strengthenings of the cancellation saturation
      lemmas. The observation: a \emph{bounded} cancellation (@{term \<open>\<not> ubd\<close>}, chosen room @{term \<open>\<gamma> \<noteq> - 1\<close>})
      still saturates an arc regardless of the other arcs' capacities --- a backward push drives the flow to
      @{term 0} with no capacity bound, and a forward push with a finite room forces the capacity to be
      finite. These feed a capacity-agnostic termination argument (the free set strictly drops, or the
      iterator advances even on the unbounded-flag step).\<close>

lemma af_push_arc_room_notfree_gen:
  assumes fi: "flow_invar fl" and ae: "a \<in> \<E>" and ar: "af_rooms fl a = (up, dn)"
    and room_fin: "(if dir then up else dn) \<noteq> - 1"
    and pa: "af_push_arc (if dir then up else dn) a dir fl = (fl', f')"
  shows "\<not> af_arc_free fl' a"
proof -
  have dnv: "dn = flow_lookup fl a" using ar by (auto simp: af_rooms_def Let_def)
  have upv: "up = (if cap a = - 1 then - 1 else cap a - flow_lookup fl a)" using ar by (auto simp: af_rooms_def Let_def)
  have flf': "flow_lookup fl' a = f'"
    and f'v: "f' = flow_lookup fl a + (if dir then (if dir then up else dn) else - (if dir then up else dn))"
    using af_push_arc_at[OF ae fi pa] by auto
  show ?thesis
  proof (cases dir)
    case True
    hence capne: "cap a \<noteq> - 1" using room_fin upv by (auto split: if_splits)
    hence "up = cap a - flow_lookup fl a" using upv by simp
    hence "flow_lookup fl' a = cap a" using f'v flf' True by simp
    thus ?thesis using capne by (simp add: af_arc_free_def)
  next
    case False
    hence "flow_lookup fl' a = flow_lookup fl a - dn" using f'v flf' by simp
    hence "flow_lookup fl' a = 0" using dnv by simp
    thus ?thesis by (simp add: af_arc_free_def)
  qed
qed

lemma af_scan_push_seed_gen:
  "flow_invar fl \<Longrightarrow> distinct es \<Longrightarrow> \<gamma> \<noteq> - 1 \<Longrightarrow> set es \<subseteq> \<E> \<Longrightarrow>
   af_scan fl x vs es ds (k0, ra0, rf0) = (k, ra, rf) \<Longrightarrow>
   af_push \<gamma> x vs es ds flip fl = (fl', 0) \<Longrightarrow>
   \<gamma> = (if flip then rf else ra) \<Longrightarrow>
   (if flip then rf else ra) = (if flip then rf0 else ra0)"
proof (induction \<gamma> x vs es ds flip fl arbitrary: fl' k0 ra0 rf0 k ra rf rule: af_push.induct)
  case (1 \<gamma> x u v1 vs a es d ds flip fl)
  have ain: "a \<in> \<E>" using 1(5) by auto
  have adist: "a \<notin> set es" using 1(3) by simp
  obtain up dn where ud: "af_rooms fl a = (up, dn)" by fastforce
  have dnv: "dn = flow_lookup fl a" using ud by (auto simp: af_rooms_def Let_def)
  have upv: "up = (if cap a = - 1 then - 1 else cap a - flow_lookup fl a)" using ud by (auto simp: af_rooms_def Let_def)
  let ?pd = "d \<noteq> flip"
  let ?tag = "if flip then (if d then dn else up) else (if d then up else dn)"
  let ?cseed = "if flip then rf0 else ra0"
  obtain fl1 fv where pa: "af_push_arc \<gamma> a ?pd fl = (fl1, fv)" by fastforce
  have fvv: "fv = flow_lookup fl a + (if ?pd then \<gamma> else - \<gamma>)" using af_push_arc_at[OF ain 1(2) pa] by simp
  have tag_pd: "?tag = (if ?pd then up else dn)" by (cases flip; cases d; simp)
  have sat_if: "\<gamma> = ?tag \<Longrightarrow> af_saturated fv a"
  proof -
    assume g: "\<gamma> = ?tag"
    show "af_saturated fv a"
    proof (cases ?pd)
      case True
      hence gup: "\<gamma> = up" using g tag_pd by simp
      hence capne: "cap a \<noteq> - 1" using 1(4) upv by (auto split: if_splits)
      hence "up = cap a - flow_lookup fl a" using upv by simp
      hence "fv = cap a" using fvv gup True by simp
      thus ?thesis by (simp add: af_saturated_def)
    next
      case False
      hence "fv = flow_lookup fl a - dn" using fvv g tag_pd by simp
      hence "fv = 0" using dnv by simp
      thus ?thesis by (simp add: af_saturated_def)
    qed
  qed
  let ?ra1 = "af_min (if d then up else dn) ra0"
  let ?rf1 = "af_min (if d then dn else up) rf0"
  have accchosen: "(if flip then ?rf1 else ?ra1) = af_min ?tag ?cseed" by (cases flip; simp)
  have chosen_min: "(if flip then rf else ra) = af_min ?tag ?cseed"
  proof (cases "v1 = x")
    case True
    hence "af_scan fl x (u # v1 # vs) (a # es) (d # ds) (k0, ra0, rf0) = (k0 + af_delta_cost a d, ?ra1, ?rf1)"
      using ud by (simp add: Let_def)
    hence "ra = ?ra1 \<and> rf = ?rf1" using 1(6) by auto
    thus ?thesis using accchosen by simp
  next
    case False
    obtain fl2 r where p2: "af_push \<gamma> x (v1 # vs) es ds flip fl1 = (fl2, r)" by fastforce
    have m0: "(if r \<noteq> 0 then Suc r else (if af_saturated fv a then 1 else 0)) = 0"
      using 1(7) ud pa p2 False by (auto simp: Let_def)
    hence r0: "r = 0" by (auto split: if_splits)
    have rec_scan: "af_scan fl x (v1 # vs) es ds (k0 + af_delta_cost a d, ?ra1, ?rf1) = (k, ra, rf)"
      using 1(6) ud False by (simp add: Let_def)
    have fi1: "flow_invar fl1" using af_push_arc_flow_invar[OF ain pa 1(2)] .
    have des: "distinct es" using 1(3) by simp
    have esE: "set es \<subseteq> \<E>" using 1(5) by auto
    have agree: "\<forall>b\<in>set es. flow_lookup fl1 b = flow_lookup fl b"
    proof
      fix b assume b: "b \<in> set es"
      hence "b \<noteq> a" using adist by auto
      thus "flow_lookup fl1 b = flow_lookup fl b" using af_push_arc_flow_off[OF ain 1(2) _ pa] by blast
    qed
    have rec_scan1: "af_scan fl1 x (v1 # vs) es ds (k0 + af_delta_cost a d, ?ra1, ?rf1) = (k, ra, rf)"
      using af_scan_cong[OF agree] rec_scan by simp
    have p2': "af_push \<gamma> x (v1 # vs) es ds flip fl1 = (fl2, 0)" using p2 r0 by simp
    have "(if flip then rf else ra) = (if flip then ?rf1 else ?ra1)"
      using 1(1)[OF pa[symmetric] refl False fi1 des 1(4) esE rec_scan1 p2' 1(8)] .
    thus ?thesis using accchosen by simp
  qed
  have nsat: "\<not> af_saturated fv a"
  proof (cases "v1 = x")
    case True thus ?thesis using 1(7) ud pa by (auto simp: Let_def split: if_splits)
  next
    case False
    obtain fl2 r where p2: "af_push \<gamma> x (v1 # vs) es ds flip fl1 = (fl2, r)" by fastforce
    have "(if r \<noteq> 0 then Suc r else (if af_saturated fv a then 1 else 0)) = 0"
      using 1(7) ud pa p2 False by (auto simp: Let_def)
    thus ?thesis by (auto split: if_splits)
  qed
  have gnetag: "\<gamma> \<noteq> ?tag" using nsat sat_if by blast
  have "(if flip then rf else ra) \<noteq> ?tag" using gnetag 1(8) by simp
  thus ?case using chosen_min by (auto simp: af_min_def split: if_splits)
qed auto

lemma af_cancel_seg_free_witnessE_gen:
  assumes feas: "af_cap_feasible fl" and fi: "flow_invar fl"
    and des: "distinct es" and ain: "a \<in> \<E>" and ses: "set es \<subseteq> \<E>"
    and ar: "af_rooms fl a = (up, dn)" and afree: "af_arc_free fl a"
    and sfree: "\<forall>b\<in>set es. af_arc_free fl b" and ane: "a \<notin> set es"
    and cs: "af_cancel_seg up dn x vs es ds a dir fl = (fl'', m', ubd)" and nubd: "\<not> ubd"
  shows "\<exists>b\<in>\<E>. af_arc_free fl b \<and> \<not> af_arc_free fl'' b"
proof -
  obtain k ra rf where sc: "af_scan fl x vs es ds
      (af_delta_cost a dir, if dir then up else dn, if dir then dn else up) = (k, ra, rf)" by (metis prod_cases3)
  have stacksat: "\<And>fl' fl2 f2 r flip.
      af_push (if flip then rf else ra) x vs es ds flip fl = (fl', r) \<Longrightarrow>
      af_push_arc (if flip then rf else ra) a (dir \<noteq> flip) fl' = (fl2, f2) \<Longrightarrow>
      0 < r \<Longrightarrow> \<exists>b\<in>\<E>. af_arc_free fl b \<and> \<not> af_arc_free fl2 b"
  proof -
    fix fl' fl2 f2 r flip
    assume p: "af_push (if flip then rf else ra) x vs es ds flip fl = (fl', r)"
      and pa: "af_push_arc (if flip then rf else ra) a (dir \<noteq> flip) fl' = (fl2, f2)" and rpos: "0 < r"
    have fi': "flow_invar fl'" using af_push_flow_invar[OF ses p fi] .
    have rl: "r - 1 < length es" using af_push_drop_bound[OF p] rpos by simp
    have bmem: "es ! (r-1) \<in> set es" using rl nth_mem by blast
    have bne: "es ! (r-1) \<noteq> a" using bmem ane by auto
    have "\<not> af_arc_free fl' (es ! (r-1))" using af_push_saturated_at[OF ses fi des p rpos] .
    moreover have "flow_lookup fl2 (es ! (r-1)) = flow_lookup fl' (es ! (r-1))"
      using af_push_arc_flow_off[OF ain fi' bne pa] by simp
    ultimately have "\<not> af_arc_free fl2 (es ! (r-1))" by (auto simp: af_arc_free_def)
    moreover have "af_arc_free fl (es ! (r-1))" using sfree bmem by blast
    ultimately show "\<exists>b\<in>\<E>. af_arc_free fl b \<and> \<not> af_arc_free fl2 b" using bmem ses by blast
  qed
  consider (fin) "(if 0 < k then rf else ra) \<noteq> - 1"
    | (sw) "\<not> (if 0 < k then rf else ra) \<noteq> - 1" "k = 0 \<and> rf \<noteq> - 1"
    | (ubd) "\<not> (if 0 < k then rf else ra) \<noteq> - 1" "\<not> (k = 0 \<and> rf \<noteq> - 1)"
    by blast
  then show ?thesis
  proof cases
    case fin
    obtain fl' r where p: "af_push (if 0 < k then rf else ra) x vs es ds (0 < k) fl = (fl', r)" by fastforce
    obtain fl2 f2 where pa: "af_push_arc (if 0 < k then rf else ra) a (dir \<noteq> (0 < k)) fl' = (fl2, f2)" by fastforce
    from cs sc fin have e: "fl'' = fl2" and meq: "m' = r" using p pa by (auto simp: af_cancel_seg_def Let_def)
    have fi': "flow_invar fl'" using af_push_flow_invar[OF ses p fi] .
    have fla': "flow_lookup fl' a = flow_lookup fl a" using af_push_flow_off[OF ses fi ane p] .
    have arfl': "af_rooms fl' a = (up, dn)"
    proof -
      have "af_rooms fl' a = af_rooms fl a" by (simp add: af_rooms_def Let_def fla')
      thus ?thesis using ar by simp
    qed
    show ?thesis
    proof (cases "r = 0")
      case False
      thus ?thesis using stacksat[OF p pa] e by auto
    next
      case r0: True
      show ?thesis
      proof (cases "0 < k")
        case Tk: True
        have rfne: "rf \<noteq> - 1" using fin Tk by simp
        have pT: "af_push rf x vs es ds True fl = (fl', 0)" using p Tk r0 by simp
        have rfeq: "rf = (if dir then dn else up)" using af_scan_push_seed_gen[OF fi des rfne ses sc pT] by simp
        have paT: "af_push_arc (if (dir \<noteq> True) then up else dn) a (dir \<noteq> True) fl' = (fl2, f2)"
          using pa Tk rfeq by (cases dir) auto
        have rmfin: "(if (dir \<noteq> True) then up else dn) \<noteq> - 1" using rfeq rfne by (cases dir) auto
        have "\<not> af_arc_free fl2 a" using af_push_arc_room_notfree_gen[OF fi' ain arfl' rmfin paT] .
        thus ?thesis using afree e ain by blast
      next
        case Fk: False
        have rane: "ra \<noteq> - 1" using fin Fk by simp
        have pF: "af_push ra x vs es ds False fl = (fl', 0)" using p Fk r0 by simp
        have raeq: "ra = (if dir then up else dn)" using af_scan_push_seed_gen[OF fi des rane ses sc pF] by simp
        have paF: "af_push_arc (if (dir \<noteq> False) then up else dn) a (dir \<noteq> False) fl' = (fl2, f2)"
          using pa Fk raeq by (cases dir) auto
        have rmfin: "(if (dir \<noteq> False) then up else dn) \<noteq> - 1" using raeq rane by (cases dir) auto
        have "\<not> af_arc_free fl2 a" using af_push_arc_room_notfree_gen[OF fi' ain arfl' rmfin paF] .
        thus ?thesis using afree e ain by blast
      qed
    qed
  next
    case sw
    obtain fl' r where p: "af_push rf x vs es ds True fl = (fl', r)" by fastforce
    obtain fl2 f2 where pa: "af_push_arc rf a (dir \<noteq> True) fl' = (fl2, f2)" by fastforce
    from cs sc sw have e: "fl'' = fl2" and meq: "m' = r" using p pa by (auto simp: af_cancel_seg_def Let_def)
    have fi': "flow_invar fl'" using af_push_flow_invar[OF ses p fi] .
    have fla': "flow_lookup fl' a = flow_lookup fl a" using af_push_flow_off[OF ses fi ane p] .
    have arfl': "af_rooms fl' a = (up, dn)"
    proof -
      have "af_rooms fl' a = af_rooms fl a" by (simp add: af_rooms_def Let_def fla')
      thus ?thesis using ar by simp
    qed
    have rfne: "rf \<noteq> - 1" using sw by simp
    show ?thesis
    proof (cases "r = 0")
      case False
      have p': "af_push (if True then rf else ra) x vs es ds True fl = (fl', r)" using p by simp
      have pa': "af_push_arc (if True then rf else ra) a (dir \<noteq> True) fl' = (fl2, f2)" using pa by simp
      thus ?thesis using stacksat[OF p' pa'] False e by auto
    next
      case r0: True
      have pT: "af_push rf x vs es ds True fl = (fl', 0)" using p r0 by simp
      have rfeq: "rf = (if dir then dn else up)" using af_scan_push_seed_gen[OF fi des rfne ses sc pT] by simp
      have paT: "af_push_arc (if (dir \<noteq> True) then up else dn) a (dir \<noteq> True) fl' = (fl2, f2)"
        using pa rfeq by (cases dir) auto
      have rmfin: "(if (dir \<noteq> True) then up else dn) \<noteq> - 1" using rfeq rfne by (cases dir) auto
      have "\<not> af_arc_free fl2 a" using af_push_arc_room_notfree_gen[OF fi' ain arfl' rmfin paT] .
      thus ?thesis using afree e ain by blast
    qed
  next
    case ubd
    from cs sc ubd nubd show ?thesis by (auto simp: af_cancel_seg_def Let_def)
  qed
qed

lemma af_cancel_seg_free_card_gen:
  assumes feas: "af_cap_feasible fl" and fi: "flow_invar fl"
    and des: "distinct es" and ain: "a \<in> \<E>" and ses: "set es \<subseteq> \<E>"
    and ar: "af_rooms fl a = (up, dn)" and afree: "af_arc_free fl a"
    and sfree: "\<forall>b\<in>set es. af_arc_free fl b" and ane: "a \<notin> set es"
    and cs: "af_cancel_seg up dn x vs es ds a dir fl = (fl'', m', ubd)" and nubd: "\<not> ubd"
  shows "card {b\<in>\<E>. af_arc_free fl'' b} < card {b\<in>\<E>. af_arc_free fl b}"
proof -
  have finF: "finite {b\<in>\<E>. af_arc_free fl b}" using finite_E by auto
  have sub: "{b\<in>\<E>. af_arc_free fl'' b} \<subseteq> {b\<in>\<E>. af_arc_free fl b}"
  proof
    fix b assume "b \<in> {b\<in>\<E>. af_arc_free fl'' b}"
    hence bE: "b \<in> \<E>" and bf'': "af_arc_free fl'' b" by auto
    have "af_arc_free fl b"
    proof (cases "b \<in> set es")
      case True thus ?thesis using sfree by blast
    next
      case bni: False
      show ?thesis
      proof (cases "b = a")
        case True thus ?thesis using afree by simp
      next
        case bnea: False
        have "flow_lookup fl'' b = flow_lookup fl b"
          using af_cancel_seg_flow_off fi bni bnea cs  ain ses by blast
        thus ?thesis using bf'' by (auto simp: af_arc_free_def)
      qed
    qed
    thus "b \<in> {b\<in>\<E>. af_arc_free fl b}" using bE by auto
  qed
  obtain w where w: "w \<in> \<E>" "af_arc_free fl w" "\<not> af_arc_free fl'' w"
    using af_cancel_seg_free_witnessE_gen[OF feas fi des ain ses ar afree sfree ane cs nubd] by blast
  have "w \<in> {b\<in>\<E>. af_arc_free fl b}" and "w \<notin> {b\<in>\<E>. af_arc_free fl'' b}" using w by auto
  hence "{b\<in>\<E>. af_arc_free fl'' b} \<subset> {b\<in>\<E>. af_arc_free fl b}" using sub by blast
  thus ?thesis using psubset_card_mono[OF finF] by blast
qed

lemma af_cancel_seg_closing_sat_gen:
  assumes fi: "flow_invar fl" and des: "distinct es"
    and esE: "set es \<subseteq> \<E>" and ain: "a \<in> \<E>" and ane: "a \<notin> set es"
    and updn: "af_rooms fl a = (up, dn)"
    and cs: "af_cancel_seg up dn x vs es ds a dir fl = (fl', 0, False)"
  shows "\<not> af_arc_free fl' a"
proof -
  obtain k ra rf where sc: "af_scan fl x vs es ds
      (af_delta_cost a dir, if dir then up else dn, if dir then dn else up) = (k, ra, rf)" by (metis prod_cases3)
  consider (fin) "(if 0 < k then rf else ra) \<noteq> - 1"
    | (sw) "\<not> (if 0 < k then rf else ra) \<noteq> - 1" "k = 0 \<and> rf \<noteq> - 1"
    | (ub) "\<not> (if 0 < k then rf else ra) \<noteq> - 1" "\<not> (k = 0 \<and> rf \<noteq> - 1)" by blast
  then show ?thesis
  proof cases
    case fin
    let ?flip = "0 < k"
    let ?g = "if ?flip then rf else ra"
    have gne: "?g \<noteq> - 1" using fin by simp
    obtain fl1 m1 where p: "af_push ?g x vs es ds ?flip fl = (fl1, m1)" by fastforce
    obtain fl2 f2 where pa: "af_push_arc ?g a (dir \<noteq> ?flip) fl1 = (fl2, f2)" by fastforce
    have fl'eq: "fl' = fl2" and m0: "m1 = 0" using cs sc fin p pa by (auto simp: af_cancel_seg_def Let_def)
    have p0: "af_push ?g x vs es ds ?flip fl = (fl1, 0)" using p m0 by simp
    have seed: "?g = (if ?flip then (if dir then dn else up) else (if dir then up else dn))"
      using af_scan_push_seed_gen[OF fi des gne esE sc p0] by simp
    have fi1: "flow_invar fl1" using af_push_flow_invar[OF esE p fi] .
    have fl1a: "flow_lookup fl1 a = flow_lookup fl a" using af_push_flow_off[OF esE fi ane p] .
    have arfl1: "af_rooms fl1 a = (up, dn)"
    proof -
      have "af_rooms fl1 a = af_rooms fl a" by (simp add: af_rooms_def Let_def fl1a)
      thus ?thesis using updn by simp
    qed
    have gtag: "?g = (if (dir \<noteq> ?flip) then up else dn)" using seed by (cases ?flip; cases dir; simp)
    have pa': "af_push_arc (if (dir \<noteq> ?flip) then up else dn) a (dir \<noteq> ?flip) fl1 = (fl2, f2)" using pa gtag by simp
    have rmfin: "(if (dir \<noteq> ?flip) then up else dn) \<noteq> - 1" using gtag gne by simp
    have "\<not> af_arc_free fl2 a" using af_push_arc_room_notfree_gen[OF fi1 ain arfl1 rmfin pa'] .
    thus ?thesis using fl'eq by simp
  next
    case sw
    have gne: "rf \<noteq> - 1" using sw by simp
    obtain fl1 m1 where p: "af_push rf x vs es ds True fl = (fl1, m1)" by fastforce
    obtain fl2 f2 where pa: "af_push_arc rf a (dir \<noteq> True) fl1 = (fl2, f2)" by fastforce
    have fl'eq: "fl' = fl2" and m0: "m1 = 0" using cs sc sw p pa by (auto simp: af_cancel_seg_def Let_def)
    have p0: "af_push rf x vs es ds True fl = (fl1, 0)" using p m0 by simp
    have seed: "(if True then rf else ra) = (if True then (if dir then dn else up) else (if dir then up else dn))"
      using af_scan_push_seed_gen[OF fi des gne esE sc p0] by simp
    hence rfseed: "rf = (if dir then dn else up)" by simp
    have fi1: "flow_invar fl1" using af_push_flow_invar[OF esE p fi] .
    have fl1a: "flow_lookup fl1 a = flow_lookup fl a" using af_push_flow_off[OF esE fi ane p] .
    have arfl1: "af_rooms fl1 a = (up, dn)"
    proof -
      have "af_rooms fl1 a = af_rooms fl a" by (simp add: af_rooms_def Let_def fl1a)
      thus ?thesis using updn by simp
    qed
    have gtag: "rf = (if (dir \<noteq> True) then up else dn)" using rfseed by (cases dir; simp)
    have pa': "af_push_arc (if (dir \<noteq> True) then up else dn) a (dir \<noteq> True) fl1 = (fl2, f2)" using pa gtag by simp
    have rmfin: "(if (dir \<noteq> True) then up else dn) \<noteq> - 1" using gtag gne by simp
    have "\<not> af_arc_free fl2 a" using af_push_arc_room_notfree_gen[OF fi1 ain arfl1 rmfin pa'] .
    thus ?thesis using fl'eq by simp
  next
    case ub
    from cs sc ub have False by (auto simp: af_cancel_seg_def Let_def)
    thus ?thesis by simp
  qed
qed

lemma af_handle_noncancel_or_free_gen:
  assumes A1: "AF_invar_1 st" and A2: "AF_invar_2 st" and A3: "AF_invar_3 st"
    and Afe: "AF_invar_feas st" and Afr: "AF_invar_free st" and AE: "AF_invar_estE st"
    and ae: "a \<in> \<E>"
    and inc: "(if dir then fst a else snd a) = hd (af_vstack st)" and ne: "af_vstack st \<noteq> []"
  shows "(af_out_arr (af_handle st a dir) = af_out_arr st \<and>
          af_in_arr (af_handle st a dir) = af_in_arr st \<and>
          af_freeset (af_handle st a dir) = af_freeset st) \<or>
         card (af_freeset (af_handle st a dir)) < card (af_freeset st)"
proof -
  have fi: "flow_invar (af_flow st)" using A1 by (auto simp: AF_invar_1_def)
  have feas: "af_cap_feasible (af_flow st)" using Afe by (simp add: AF_invar_feas_def)
  have fr: "\<forall>b\<in>set (af_estack st). af_arc_free (af_flow st) b" using Afr by (simp add: AF_invar_free_def)
  have estE: "set (af_estack st) \<subseteq> \<E>" using AE by (simp add: AF_invar_estE_def)
  have distES: "distinct (af_estack st)" using estack_distinct[OF A2 A3] .
  have inc': "hd (af_vstack st) \<in> {fst a, snd a}" using inc by (cases dir) auto
  have finfs: "finite (af_freeset st)" using finite_E by (auto simp: af_freeset_def intro: finite_subset)
  show ?thesis
  proof (cases "fst a = snd a")
    case selfl: True
    have ha: "af_handle st a dir = af_selfloop_handle st a" using selfl by (simp add: af_handle_real[OF ae])
    have fs_off: "\<And>b. b \<noteq> a \<Longrightarrow> af_arc_free (af_flow (af_selfloop_handle st a)) b = af_arc_free (af_flow st) b"
      using af_selfloop_handle_flow_off[OF ae fi] by (simp add: af_arc_free_def)
    show ?thesis
    proof (cases "af_arc_free (af_flow (af_selfloop_handle st a)) a")
      case True
      have "af_flow (af_selfloop_handle st a) = af_flow st"
        using af_selfloop_handle_free_imp_flow_id[OF ae fi True] .
      hence "af_freeset (af_handle st a dir) = af_freeset st" using ha by (simp add: af_freeset_def)
      thus ?thesis using ha by simp
    next
      case nf: False
      have fsetnew: "af_freeset (af_selfloop_handle st a) = af_freeset st - {a}"
      proof (rule set_eqI)
        fix b
        show "(b \<in> af_freeset (af_selfloop_handle st a)) = (b \<in> af_freeset st - {a})"
        proof (cases "b = a")
          case True thus ?thesis using nf by (simp add: af_freeset_def)
        next
          case False thus ?thesis using fs_off[OF False] by (simp add: af_freeset_def)
        qed
      qed
      show ?thesis
      proof (cases "a \<in> af_freeset st")
        case True
        hence "af_freeset (af_selfloop_handle st a) \<subset> af_freeset st" using fsetnew by auto
        hence "card (af_freeset (af_selfloop_handle st a)) < card (af_freeset st)"
          using psubset_card_mono[OF finfs] by simp
        thus ?thesis using ha by simp
      next
        case False
        have "af_freeset st - {a} = af_freeset st" using False by auto
        thus ?thesis using fsetnew ha by simp
      qed
    qed
  next
    case selfloop: False
    obtain up dn where updn: "af_rooms (af_flow st) a = (up, dn)"
      by (cases "af_rooms (af_flow st) a") auto
    show ?thesis
    proof (cases "0 < dn \<and> (up = - 1 \<or> 0 < up)")
      case False thus ?thesis using updn selfloop by (simp add: af_handle_real[OF ae] Let_def)
    next
      case guard: True
      have afree: "af_arc_free (af_flow st) a"
      proof -
        have "cap a = - 1 \<or> flow_lookup (af_flow st) a \<le> cap a" using feas ae by (auto simp: af_cap_feasible_def)
        thus ?thesis using af_guard_free[OF updn] guard by simp
      qed
      show ?thesis
      proof (cases "af_estack st \<noteq> [] \<and> a = hd (af_estack st)")
        case True
        have "af_handle st a dir = st"
          unfolding af_handle_real[OF ae]
          using updn guard selfloop True by (simp add: Let_def)
        thus ?thesis by simp
      next
        case parent: False
        have ane: "a \<notin> set (af_estack st)" using a_notin_estack_incident[OF A2 A3 inc' ne parent] .
        show ?thesis
        proof (cases "st_lookup (af_state st) (if dir then snd a else fst a)")
          case Unseen
          have "af_handle st a dir = st\<lparr>af_vstack := (if dir then snd a else fst a) # af_vstack st,
              af_state := st_upd (af_state st) (if dir then snd a else fst a) OnStack,
              af_estack := a # af_estack st, af_dstack := dir # af_dstack st\<rparr>"
            using updn guard selfloop parent Unseen by (auto simp: af_handle_real[OF ae] Let_def)
          thus ?thesis by simp
        next
          case OnStack
          obtain fl m' ubd where c: "af_cancel_seg up dn (if dir then snd a else fst a)
              (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) = (fl, m', ubd)"
            by (metis prod_cases3)
          show ?thesis
          proof (cases ubd)
            case True
            have "af_handle st a dir = st\<lparr>af_unbounded := True\<rparr>"
              using updn guard selfloop parent OnStack c True by (auto simp: af_handle_real[OF ae] Let_def)
            thus ?thesis by simp
          next
            case False
            have hd: "af_handle st a dir = af_reset_unsee_seg m' (af_vstack st)
                (st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st),
                    af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>)"
              using updn guard selfloop parent OnStack c False by (auto simp: af_handle_real[OF ae] Let_def)
            have "card {b\<in>\<E>. af_arc_free fl b} < card {b\<in>\<E>. af_arc_free (af_flow st) b}"
              by (rule af_cancel_seg_free_card_gen[OF feas fi distES ae estE updn afree fr ane c False])
            thus ?thesis using hd by (simp add: af_freeset_def)
          qed
        next
          case Finished
          thus ?thesis using updn guard selfloop parent by (auto simp: af_handle_real[OF ae] Let_def)
        qed
      qed
    qed
  qed
qed



lemma af_meas_upd1_in:
  assumes mi0: "multigraph_inv out_arr in_arr"
    and conds: "AF_DFS_call_1_conds st" and inv: "AF_inv st"
  shows "(AF_DFS_upd1 st, st) \<in> measures [\<lambda>s. card (af_freeset s), \<lambda>s. af_iterrem s, \<lambda>s. length (af_vstack s)]"
proof -
  from inv have i1: "AF_invar_1 st" and i2: "AF_invar_2 st" and i3: "AF_invar_3 st"
    and iit: "AF_invar_iter st" and iV: "AF_invar_V st" and iE: "AF_invar_estE st"
    and ife: "AF_invar_feas st" and ifr: "AF_invar_free st" by (auto simp: AF_inv_def)
  from conds have ne: "af_vstack st \<noteq> []" and he: "out_has (af_out_arr st) (hd (af_vstack st))"
    by (auto elim!: call_cond_elims)
  have mi': "multigraph_inv (af_out_arr st) (af_in_arr st)" using iit by (simp add: AF_invar_iter_def)
  have vV: "hd (af_vstack st) \<in> \<V>" using iV ne hd_in_set by (auto simp: AF_invar_V_def)
  have endp: "fst (out_current (af_out_arr st) (hd (af_vstack st))) = hd (af_vstack st) \<and>
              out_current (af_out_arr st) (hd (af_vstack st)) \<in> \<E>"
    using af_current_out_endpoint[OF mi' vV he] by simp
  let ?st' = "st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack st))\<rparr>"
  let ?a = "out_current (af_out_arr st) (hd (af_vstack st))"
  have upd1: "AF_DFS_upd1 st = af_handle ?st' ?a True" by (simp add: AF_DFS_upd1_def Let_def)
  have A1': "AF_invar_1 ?st'"using AF_invar_1_out_advance i1 vV by auto
  have inc: "(if True then fst ?a else snd ?a) = hd (af_vstack ?st')" using endp by simp
  have dich: "(af_out_arr (af_handle ?st' ?a True) = af_out_arr ?st' \<and>
               af_in_arr (af_handle ?st' ?a True) = af_in_arr ?st' \<and>
               af_freeset (af_handle ?st' ?a True) = af_freeset ?st') \<or>
              card (af_freeset (af_handle ?st' ?a True)) < card (af_freeset ?st')"
    by (rule af_handle_noncancel_or_free_gen[OF A1' _ _ _ _ _ _ inc _])
       (use i2 i3 ife ifr iE endp ne in simp_all)
  have iterdec: "af_iterrem ?st' + 1 = af_iterrem st" by (rule af_iterrem_out_advance[OF mi' vV he])
  from dich show ?thesis
  proof
    assume L: "af_out_arr (af_handle ?st' ?a True) = af_out_arr ?st' \<and>
               af_in_arr (af_handle ?st' ?a True) = af_in_arr ?st' \<and>
               af_freeset (af_handle ?st' ?a True) = af_freeset ?st'"
    have fc: "card (af_freeset (AF_DFS_upd1 st)) = card (af_freeset st)"
      using L upd1 by simp
    have "af_iterrem (AF_DFS_upd1 st) = af_iterrem ?st'"
      using L upd1 by (simp add: af_iterrem_def)
    hence "af_iterrem (AF_DFS_upd1 st) < af_iterrem st" using iterdec by simp
    thus ?thesis using fc by (simp add: in_measures)
  next
    assume R: "card (af_freeset (af_handle ?st' ?a True)) < card (af_freeset ?st')"
    hence "card (af_freeset (AF_DFS_upd1 st)) < card (af_freeset st)" using upd1 by simp
    thus ?thesis by (simp add: in_measures)
  qed
qed

lemma af_meas_upd2_in:
  assumes mi0: "multigraph_inv out_arr in_arr"
    and conds: "AF_DFS_call_2_conds st" and inv: "AF_inv st"
  shows "(AF_DFS_upd2 st, st) \<in> measures [\<lambda>s. card (af_freeset s), \<lambda>s. af_iterrem s, \<lambda>s. length (af_vstack s)]"
proof -
  from inv have i1: "AF_invar_1 st" and i2: "AF_invar_2 st" and i3: "AF_invar_3 st"
    and iit: "AF_invar_iter st" and iV: "AF_invar_V st" and iE: "AF_invar_estE st"
    and ife: "AF_invar_feas st" and ifr: "AF_invar_free st" by (auto simp: AF_inv_def)
  from conds have ne: "af_vstack st \<noteq> []" and he: "in_has (af_in_arr st) (hd (af_vstack st))"
    by (auto elim!: call_cond_elims)
  have mi': "multigraph_inv (af_out_arr st) (af_in_arr st)" using iit by (simp add: AF_invar_iter_def)
  have vV: "hd (af_vstack st) \<in> \<V>" using iV ne hd_in_set by (auto simp: AF_invar_V_def)
  have endp: "snd (in_current (af_in_arr st) (hd (af_vstack st))) = hd (af_vstack st) \<and>
              in_current (af_in_arr st) (hd (af_vstack st)) \<in> \<E>"
    using af_current_in_endpoint[OF mi' vV he] by simp
  let ?st' = "st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack st))\<rparr>"
  let ?a = "in_current (af_in_arr st) (hd (af_vstack st))"
  have upd2: "AF_DFS_upd2 st = af_handle ?st' ?a False" by (simp add: AF_DFS_upd2_def Let_def)
  have A1': "AF_invar_1 ?st'" using AF_invar_1_in_advance i1 vV by auto
  have inc: "(if False then fst ?a else snd ?a) = hd (af_vstack ?st')" using endp by simp
  have dich: "(af_out_arr (af_handle ?st' ?a False) = af_out_arr ?st' \<and>
               af_in_arr (af_handle ?st' ?a False) = af_in_arr ?st' \<and>
               af_freeset (af_handle ?st' ?a False) = af_freeset ?st') \<or>
              card (af_freeset (af_handle ?st' ?a False)) < card (af_freeset ?st')"
    by (rule af_handle_noncancel_or_free_gen[OF A1' _ _ _ _ _ _ inc _])
       (use i2 i3 ife ifr iE endp ne in simp_all)
  have iterdec: "af_iterrem ?st' + 1 = af_iterrem st" by (rule af_iterrem_in_advance[OF mi' vV he])
  from dich show ?thesis
  proof
    assume L: "af_out_arr (af_handle ?st' ?a False) = af_out_arr ?st' \<and>
               af_in_arr (af_handle ?st' ?a False) = af_in_arr ?st' \<and>
               af_freeset (af_handle ?st' ?a False) = af_freeset ?st'"
    have fc: "card (af_freeset (AF_DFS_upd2 st)) = card (af_freeset st)"
      using L upd2 by simp
    have "af_iterrem (AF_DFS_upd2 st) = af_iterrem ?st'"
      using L upd2 by (simp add: af_iterrem_def)
    hence "af_iterrem (AF_DFS_upd2 st) < af_iterrem st" using iterdec by simp
    thus ?thesis using fc by (simp add: in_measures)
  next
    assume R: "card (af_freeset (af_handle ?st' ?a False)) < card (af_freeset ?st')"
    hence "card (af_freeset (AF_DFS_upd2 st)) < card (af_freeset st)" using upd2 by simp
    thus ?thesis by (simp add: in_measures)
  qed
qed

lemma af_meas_upd3_in:
  assumes conds: "AF_DFS_call_3_conds st"
  shows "(AF_DFS_upd3 st, st) \<in> measures [\<lambda>s. card (af_freeset s), \<lambda>s. af_iterrem s, \<lambda>s. length (af_vstack s)]"
proof -
  from conds have ne: "af_vstack st \<noteq> []" by (auto elim!: call_cond_elims)
  have fc: "af_freeset (AF_DFS_upd3 st) = af_freeset st" by (simp add: AF_DFS_upd3_def af_freeset_def)
  have it: "af_iterrem (AF_DFS_upd3 st) = af_iterrem st" by (simp add: AF_DFS_upd3_def af_iterrem_def)
  have "length (af_vstack (AF_DFS_upd3 st)) < length (af_vstack st)"
    using ne by (simp add: AF_DFS_upd3_def)
  thus ?thesis using fc it by (simp add: in_measures)
qed

text \<open>Inner DFS termination: under the full invariant @{const AF_inv} (established at launch from the
      standing @{term \<open>multigraph_inv out_arr in_arr\<close>} and finite capacities), the DFS is total.\<close>

lemma AF_DFS_dom:
  assumes mi0: "multigraph_inv out_arr in_arr" and inv: "AF_inv st"
  shows "AF_DFS_dom st"
proof -
  let ?r = "measures [\<lambda>s. card (af_freeset s), \<lambda>s. af_iterrem s, \<lambda>s. length (af_vstack s)]"
  have wf: "wf ?r" by simp
  have "AF_inv st \<longrightarrow> AF_DFS_dom st"
    using wf
  proof (induction st rule: wf_induct_rule)
    case (less st)
    show ?case
    proof
      assume inv: "AF_inv st"
      show "AF_DFS_dom st"
      proof (rule AF_DFS_domintros)
        assume c: "AF_DFS_call_1_conds st"
        have "(AF_DFS_upd1 st, st) \<in> ?r" using af_meas_upd1_in[OF mi0 c inv] .
        moreover have "AF_inv (AF_DFS_upd1 st)" using AF_inv_holds_1[OF mi0 c inv] .
        ultimately show "AF_DFS_dom (AF_DFS_upd1 st)" using less by blast
      next
        assume c: "AF_DFS_call_2_conds st"
        have "(AF_DFS_upd2 st, st) \<in> ?r" using af_meas_upd2_in[OF mi0 c inv] .
        moreover have "AF_inv (AF_DFS_upd2 st)" using AF_inv_holds_2[OF mi0 c inv] .
        ultimately show "AF_DFS_dom (AF_DFS_upd2 st)" using less by blast
      next
        assume c: "AF_DFS_call_3_conds st"
        have "(AF_DFS_upd3 st, st) \<in> ?r" using af_meas_upd3_in[OF c] .
        moreover have "AF_inv (AF_DFS_upd3 st)" using AF_inv_holds_3[OF c inv] .
        ultimately show "AF_DFS_dom (AF_DFS_upd3 st)" using less by blast
      qed
    qed
  qed
  thus ?thesis using inv by blast
qed

subsection \<open>Outer loop termination --- the whole procedure is total\<close>

text \<open>The full invariant holds at each DFS launch (established from the standing @{term \<open>multigraph_inv out_arr in_arr\<close>},
      finite capacities, feasible input flow, and a vertex iterator covering @{term \<V>}), so every launched DFS is
      total; the outer loop's own measure is the number of vertices yet to be visited, which drops on every step.\<close>

lemma AF_inv_initial:
  assumes fi: "flow_invar fl" and si: "st_invar stt" and ao: "out_invar oa" and ai: "in_invar ia"
    and mi: "multigraph_inv oa ia" and vV: "v \<in> \<V>" and feas: "af_cap_feasible fl"
    and noos: "\<forall>w\<in>\<V>. st_lookup stt w \<noteq> OnStack"
  shows "AF_inv (AF_DFS_initial fl oa ia stt v)"
proof -
  have si': "st_invar (st_upd stt v OnStack)" using st_upd_invar[OF si vV] .
  have lk: "\<And>w. st_lookup (st_upd stt v OnStack) w = (if w = v then OnStack else st_lookup stt w)"
    using state_arr.fixed_univ_map_upd[OF si vV] by simp
  have "AF_invar_1 (AF_DFS_initial fl oa ia stt v)"
    using fi si' ao ai by (simp add: AF_DFS_initial_def AF_invar_1_def)
  moreover have "AF_invar_2 (AF_DFS_initial fl oa ia stt v)"
    using lk noos by (auto simp: AF_DFS_initial_def AF_invar_2_def)
  moreover have "AF_invar_3 (AF_DFS_initial fl oa ia stt v)"
    by (simp add: AF_DFS_initial_def AF_invar_3_def)
  moreover have "AF_invar_iter (AF_DFS_initial fl oa ia stt v)"
    using mi by (simp add: AF_DFS_initial_def AF_invar_iter_def)
  moreover have "AF_invar_V (AF_DFS_initial fl oa ia stt v)"
    using vV by (simp add: AF_DFS_initial_def AF_invar_V_def)
  moreover have "AF_invar_estE (AF_DFS_initial fl oa ia stt v)"
    by (simp add: AF_DFS_initial_def AF_invar_estE_def)
  moreover have "AF_invar_feas (AF_DFS_initial fl oa ia stt v)"
    using feas by (simp add: AF_DFS_initial_def AF_invar_feas_def)
  moreover have "AF_invar_free (AF_DFS_initial fl oa ia stt v)"
    by (simp add: AF_DFS_initial_def AF_invar_free_def)
  ultimately show ?thesis by (simp add: AF_inv_def)
qed

lemma AF_inv_holds:
  assumes dom: "AF_DFS_dom st" and mi0: "multigraph_inv out_arr in_arr"
    and inv: "AF_inv st"
  shows "AF_inv (AF_DFS st)"
  using inv proof (induction rule: AF_DFS_induct[OF dom])
  case IH: (1 st)
  show ?case
    apply (rule AF_DFS_cases[where st = st])
    by (auto intro!: IH(2-5) AF_inv_holds_1[OF mi0] AF_inv_holds_2[OF mi0] AF_inv_holds_3
             simp: AF_DFS_simps[OF IH(1)] AF_DFS_ret_def)
qed

lemma AF_DFS_ret_vstack:
  assumes dom: "AF_DFS_dom st"
  shows "\<not> af_unbounded (AF_DFS st) \<longrightarrow> af_vstack (AF_DFS st) = []"
proof (induction rule: AF_DFS_induct[OF dom])
  case IH: (1 st)
  show ?case
    apply (rule AF_DFS_cases[where st = st])
    subgoal using IH(2) by (simp add: AF_DFS_simps[OF IH(1)])
    subgoal using IH(3) by (simp add: AF_DFS_simps[OF IH(1)])
    subgoal using IH(4) by (simp add: AF_DFS_simps[OF IH(1)])
    subgoal by (auto simp: AF_DFS_simps[OF IH(1)] AF_DFS_ret_def elim!: call_cond_elims)
    done
qed

definition "AFF_inv st \<longleftrightarrow>
  flow_invar (aff_flow st) \<and> st_invar (aff_state st) \<and>
  out_invar (aff_out_arr st) \<and> in_invar (aff_in_arr st) \<and>
  multigraph_inv (aff_out_arr st) (aff_in_arr st) \<and>
  af_cap_feasible (aff_flow st) \<and>
  (\<not> aff_unbounded st \<longrightarrow> (\<forall>w\<in>\<V>. st_lookup (aff_state st) w \<noteq> OnStack)) \<and>
  vit_invar (aff_vit st) \<and> vit_abstract (aff_vit st) \<subseteq> \<V>"

lemma AFF_inv_initial:
  assumes mi0: "multigraph_inv out_arr in_arr" and ff: "flow_invar f0" and feas: "af_cap_feasible f0"
    and vv: "vit_invar all_vertices" and vab: "vit_abstract all_vertices \<subseteq> \<V>"
  shows "AFF_inv (AF_outer_initial f0)"
proof -
  have "out_invar out_arr" "in_invar in_arr" using mi0 by (auto simp: multigraph_inv_def out_graph_inv_def in_graph_inv_def)
  thus ?thesis
    using mi0 ff feas vv vab state_init_invar state_init_unseen
    by (auto simp: AFF_inv_def AF_outer_initial_def)
qed

lemma vit_current_V:
  assumes inv: "AFF_inv st" and hv: "has_vertex (aff_vit st)"
  shows "current_vertex (aff_vit st) \<in> \<V>"
proof -
  have iv: "vit_invar (aff_vit st)" and vab: "vit_abstract (aff_vit st) \<subseteq> \<V>" using inv by (auto simp: AFF_inv_def)
  have ne: "vit_remaining (aff_vit st) \<noteq> {}" using hv iv vertex_iterator.has_current by auto
  have "current_vertex (aff_vit st) \<in> vit_remaining (aff_vit st)" using iv ne vertex_iterator.current_element by auto
  moreover have "vit_remaining (aff_vit st) \<subseteq> vit_abstract (aff_vit st)"
    using vertex_iterator.iterable_set_abstract(2)[OF iv] by auto
  ultimately show ?thesis using vab by auto
qed

lemma vit_rem_finite:
  assumes inv: "AFF_inv st" shows "finite (vit_remaining (aff_vit st))"
proof -
  have iv: "vit_invar (aff_vit st)" and vab: "vit_abstract (aff_vit st) \<subseteq> \<V>" using inv by (auto simp: AFF_inv_def)
  have "vit_remaining (aff_vit st) \<subseteq> vit_abstract (aff_vit st)"
    using vertex_iterator.iterable_set_abstract(2)[OF iv] by auto
  thus ?thesis using vab \<V>_finite by (auto intro: finite_subset)
qed

lemma AFF_inv_holds_1:
  assumes conds: "AF_outer_call_1_conds st" and inv: "AFF_inv st"
  shows "AFF_inv (AF_outer_upd1 st)"
proof -
  have iv: "vit_invar (aff_vit st)" and vab: "vit_abstract (aff_vit st) \<subseteq> \<V>" using inv by (auto simp: AFF_inv_def)
  have hv: "has_vertex (aff_vit st)" using conds by (auto simp: AF_outer_call_1_conds_def)
  have ne: "vit_remaining (aff_vit st) \<noteq> {}" using hv iv vertex_iterator.has_current by auto
  have iv': "vit_invar (move_on_vertex (aff_vit st))" using vertex_iterator.move_on_invar[OF iv ne] .
  have vab': "vit_abstract (move_on_vertex (aff_vit st)) \<subseteq> \<V>"
    using vertex_iterator.move_on(1)[OF iv ne] vab by simp
  show ?thesis using inv iv' vab' by (simp add: AFF_inv_def AF_outer_upd1_def)
qed

lemma AFF_inv_holds_2:
  assumes mi0: "multigraph_inv out_arr in_arr"
    and conds: "AF_outer_call_2_conds st" and inv: "AFF_inv st"
  shows "AFF_inv (AF_outer_upd2 st)"
proof -
  from inv have ff: "flow_invar (aff_flow st)" and sti: "st_invar (aff_state st)"
    and aoi: "out_invar (aff_out_arr st)" and aii: "in_invar (aff_in_arr st)"
    and mii: "multigraph_inv (aff_out_arr st) (aff_in_arr st)" and feas: "af_cap_feasible (aff_flow st)"
    and noos: "\<not> aff_unbounded st \<longrightarrow> (\<forall>w\<in>\<V>. st_lookup (aff_state st) w \<noteq> OnStack)"
    and iv: "vit_invar (aff_vit st)" and vab: "vit_abstract (aff_vit st) \<subseteq> \<V>" by (auto simp: AFF_inv_def)
  from conds have nu: "\<not> aff_unbounded st" and hv: "has_vertex (aff_vit st)" by (auto simp: AF_outer_call_2_conds_def)
  let ?v = "current_vertex (aff_vit st)"
  have vV: "?v \<in> \<V>" using vit_current_V[OF inv hv] .
  have noos': "\<forall>w\<in>\<V>. st_lookup (aff_state st) w \<noteq> OnStack" using noos nu by simp
  let ?init = "AF_DFS_initial (aff_flow st) (aff_out_arr st) (aff_in_arr st) (aff_state st) ?v"
  have dom: "AF_DFS_dom ?init" using AF_DFS_dom[OF mi0 AF_inv_initial[OF ff sti aoi aii mii vV feas noos']] .
  have inv_res: "AF_inv (AF_DFS ?init)"
    using AF_inv_holds[OF dom mi0 AF_inv_initial[OF ff sti aoi aii mii vV feas noos']] .
  from inv_res have r1: "AF_invar_1 (AF_DFS ?init)" and r2: "AF_invar_2 (AF_DFS ?init)"
    and rit: "AF_invar_iter (AF_DFS ?init)" and rfe: "AF_invar_feas (AF_DFS ?init)" by (auto simp: AF_inv_def)
  have c1: "flow_invar (af_flow (AF_DFS ?init))" and c2: "st_invar (af_state (AF_DFS ?init))"
    and c3: "out_invar (af_out_arr (AF_DFS ?init))" and c4: "in_invar (af_in_arr (AF_DFS ?init))"
    using r1 by (auto simp: AF_invar_1_def)
  have c5: "multigraph_inv (af_out_arr (AF_DFS ?init)) (af_in_arr (AF_DFS ?init))"
    using rit by (simp add: AF_invar_iter_def)
  have c6: "af_cap_feasible (af_flow (AF_DFS ?init))" using rfe by (simp add: AF_invar_feas_def)
  have c7: "\<not> af_unbounded (AF_DFS ?init) \<longrightarrow> (\<forall>w\<in>\<V>. st_lookup (af_state (AF_DFS ?init)) w \<noteq> OnStack)"
  proof
    assume "\<not> af_unbounded (AF_DFS ?init)"
    hence "af_vstack (AF_DFS ?init) = []" using AF_DFS_ret_vstack[OF dom] by simp
    thus "\<forall>w\<in>\<V>. st_lookup (af_state (AF_DFS ?init)) w \<noteq> OnStack" using r2 by (auto simp: AF_invar_2_def)
  qed
  have ne: "vit_remaining (aff_vit st) \<noteq> {}" using hv iv vertex_iterator.has_current by auto
  have iv': "vit_invar (move_on_vertex (aff_vit st))" using vertex_iterator.move_on_invar[OF iv ne] .
  have vab': "vit_abstract (move_on_vertex (aff_vit st)) \<subseteq> \<V>"
    using vertex_iterator.move_on(1)[OF iv ne] vab by simp
  show ?thesis using c1 c2 c3 c4 c5 c6 c7 iv' vab'
    by (simp add: AFF_inv_def AF_outer_upd2_def Let_def)
qed

lemma vit_move_on_card:
  assumes inv: "AFF_inv st" and hv: "has_vertex (aff_vit st)"
  shows "card (vit_remaining (move_on_vertex (aff_vit st))) < card (vit_remaining (aff_vit st))"
proof -
  have iv: "vit_invar (aff_vit st)" using inv by (simp add: AFF_inv_def)
  have ne: "vit_remaining (aff_vit st) \<noteq> {}" using hv iv vertex_iterator.has_current by auto
  have fin: "finite (vit_remaining (aff_vit st))" using vit_rem_finite[OF inv] .
  have cur: "current_vertex (aff_vit st) \<in> vit_remaining (aff_vit st)"
    using iv ne vertex_iterator.current_element by auto
  have pos: "0 < card (vit_remaining (aff_vit st))" using fin ne by (simp add: card_gt_0_iff)
  have "vit_remaining (move_on_vertex (aff_vit st)) = vit_remaining (aff_vit st) - {current_vertex (aff_vit st)}"
    using vertex_iterator.move_on(2)[OF iv ne] .
  hence "card (vit_remaining (move_on_vertex (aff_vit st))) = card (vit_remaining (aff_vit st)) - 1"
    using cur fin by (simp add: card_Diff_singleton)
  thus ?thesis using pos by simp
qed

text \<open>Outer-loop (hence whole-procedure) termination.\<close>

lemma AF_outer_dom:
  assumes mi0: "multigraph_inv out_arr in_arr" and inv: "AFF_inv st"
  shows "AF_outer_dom st"
proof -
  let ?r = "measure (\<lambda>s. card (vit_remaining (aff_vit s)))"
  have wfr: "wf ?r" by simp
  have "AFF_inv st \<longrightarrow> AF_outer_dom st"
    using wfr
  proof (induction st rule: wf_induct_rule)
    case (less st)
    show ?case
    proof
      assume inv: "AFF_inv st"
      show "AF_outer_dom st"
      proof (rule AF_outer_domintros)
        assume c: "AF_outer_call_1_conds st"
        have hv: "has_vertex (aff_vit st)" using c by (auto simp: AF_outer_call_1_conds_def)
        have "(AF_outer_upd1 st, st) \<in> ?r" using vit_move_on_card[OF inv hv] by (simp add: AF_outer_upd1_def)
        moreover have "AFF_inv (AF_outer_upd1 st)" using AFF_inv_holds_1[OF c inv] .
        ultimately show "AF_outer_dom (AF_outer_upd1 st)" using less by blast
      next
        assume c: "AF_outer_call_2_conds st"
        have hv: "has_vertex (aff_vit st)" using c by (auto simp: AF_outer_call_2_conds_def)
        have "(AF_outer_upd2 st, st) \<in> ?r" using vit_move_on_card[OF inv hv] by (simp add: AF_outer_upd2_def Let_def)
        moreover have "AFF_inv (AF_outer_upd2 st)" using AFF_inv_holds_2[OF mi0 c inv] .
        ultimately show "AF_outer_dom (AF_outer_upd2 st)" using less by blast
      qed
    qed
  qed
  thus ?thesis using inv by blast
qed

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
  assumes A: "\<And>G v. proj (out_reset G v) = proj G"
  shows "proj (af_out_arr (af_handle st a dir)) = proj (af_out_arr st)"
proof (cases "fst_exec a = snd_exec a")
  case True
  then show ?thesis by (simp add: af_handle_def)
next
  case sl: False
  obtain up dn where updn: "af_rooms (af_flow st) a = (up, dn)" by (cases "af_rooms (af_flow st) a")
  show ?thesis
  proof (cases "0 < dn \<and> (up = - 1 \<or> 0 < up)")
    case False
    then show ?thesis using sl updn by (simp add: af_handle_def Let_def)
  next
    case guard: True
    show ?thesis
    proof (cases "af_estack st \<noteq> [] \<and> a = hd (af_estack st)")
      case True
      then show ?thesis using sl updn guard by (simp add: af_handle_def Let_def)
    next
      case eshd: False
      show ?thesis
      proof (cases "st_lookup (af_state st) (if dir then snd_exec a else fst_exec a)")
        case Finished
        then show ?thesis using sl updn guard eshd by (simp add: af_handle_def Let_def)
      next
        case OnStack
        obtain fl m' ubd where cs: "af_cancel_seg up dn (if dir then snd_exec a else fst_exec a) (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) = (fl, m', ubd)"
          by (cases "af_cancel_seg up dn (if dir then snd_exec a else fst_exec a) (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st)") auto
        show ?thesis
        proof (cases ubd)
          case True
          then show ?thesis using sl updn guard eshd OnStack cs by (simp add: af_handle_def Let_def)
        next
          case False
          then show ?thesis using sl updn guard eshd OnStack cs
            by (simp add: af_handle_def Let_def af_reset_unsee_seg_out_proj[OF A])
        qed
      next
        case Unseen
        then show ?thesis using sl updn guard eshd by (simp add: af_handle_def Let_def)
      qed
    qed
  qed
qed

lemma af_handle_in_proj:
  assumes A: "\<And>G v. proj (in_reset G v) = proj G"
  shows "proj (af_in_arr (af_handle st a dir)) = proj (af_in_arr st)"
proof (cases "fst_exec a = snd_exec a")
  case True
  then show ?thesis by (simp add: af_handle_def)
next
  case sl: False
  obtain up dn where updn: "af_rooms (af_flow st) a = (up, dn)" by (cases "af_rooms (af_flow st) a")
  show ?thesis
  proof (cases "0 < dn \<and> (up = - 1 \<or> 0 < up)")
    case False
    then show ?thesis using sl updn by (simp add: af_handle_def Let_def)
  next
    case guard: True
    show ?thesis
    proof (cases "af_estack st \<noteq> [] \<and> a = hd (af_estack st)")
      case True
      then show ?thesis using sl updn guard by (simp add: af_handle_def Let_def)
    next
      case eshd: False
      show ?thesis
      proof (cases "st_lookup (af_state st) (if dir then snd_exec a else fst_exec a)")
        case Finished
        then show ?thesis using sl updn guard eshd by (simp add: af_handle_def Let_def)
      next
        case OnStack
        obtain fl m' ubd where cs: "af_cancel_seg up dn (if dir then snd_exec a else fst_exec a) (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) = (fl, m', ubd)"
          by (cases "af_cancel_seg up dn (if dir then snd_exec a else fst_exec a) (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st)") auto
        show ?thesis
        proof (cases ubd)
          case True
          then show ?thesis using sl updn guard eshd OnStack cs by (simp add: af_handle_def Let_def)
        next
          case False
          then show ?thesis using sl updn guard eshd OnStack cs
            by (simp add: af_handle_def Let_def af_reset_unsee_seg_in_proj[OF A])
        qed
      next
        case Unseen
        then show ?thesis using sl updn guard eshd by (simp add: af_handle_def Let_def)
      qed
    qed
  qed
qed

lemma AF_DFS_out_proj:
  assumes om: "\<And>G v. proj (out_move G v) = proj G" and orst: "\<And>G v. proj (out_reset G v) = proj G"
    and dom: "AF_DFS_dom st"
  shows "proj (af_out_arr (AF_DFS st)) = proj (af_out_arr st)"
proof (induction rule: AF_DFS_induct[OF dom])
  case (1 st)
  consider (c1) "AF_DFS_call_1_conds st" | (c2) "AF_DFS_call_2_conds st"
    | (c3) "AF_DFS_call_3_conds st" | (r) "AF_DFS_ret_conds st"
    by (cases "af_vstack st") (auto simp: AF_DFS_call_1_conds_def AF_DFS_call_2_conds_def AF_DFS_call_3_conds_def AF_DFS_ret_conds_def)
  then show ?case
  proof cases
    case c1
    thus ?thesis using 1(2)[OF c1] AF_DFS_simps(1)[OF 1(1) c1]
      by (simp add: AF_DFS_upd1_def Let_def af_handle_out_proj[OF orst] om)
  next
    case c2
    thus ?thesis using 1(3)[OF c2] AF_DFS_simps(2)[OF 1(1) c2]
      by (simp add: AF_DFS_upd2_def Let_def af_handle_out_proj[OF orst])
  next
    case c3
    thus ?thesis using 1(4)[OF c3] AF_DFS_simps(3)[OF 1(1) c3]
      by (simp add: AF_DFS_upd3_def)
  next
    case r
    thus ?thesis using AF_DFS_simps(4)[OF 1(1) r] by (simp add: AF_DFS_ret_def)
  qed
qed

lemma AF_DFS_in_proj:
  assumes im: "\<And>G v. proj (in_move G v) = proj G" and irst: "\<And>G v. proj (in_reset G v) = proj G"
    and dom: "AF_DFS_dom st"
  shows "proj (af_in_arr (AF_DFS st)) = proj (af_in_arr st)"
proof (induction rule: AF_DFS_induct[OF dom])
  case (1 st)
  consider (c1) "AF_DFS_call_1_conds st" | (c2) "AF_DFS_call_2_conds st"
    | (c3) "AF_DFS_call_3_conds st" | (r) "AF_DFS_ret_conds st"
    by (cases "af_vstack st") (auto simp: AF_DFS_call_1_conds_def AF_DFS_call_2_conds_def AF_DFS_call_3_conds_def AF_DFS_ret_conds_def)
  then show ?case
  proof cases
    case c1
    thus ?thesis using 1(2)[OF c1] AF_DFS_simps(1)[OF 1(1) c1]
      by (simp add: AF_DFS_upd1_def Let_def af_handle_in_proj[OF irst])
  next
    case c2
    thus ?thesis using 1(3)[OF c2] AF_DFS_simps(2)[OF 1(1) c2]
      by (simp add: AF_DFS_upd2_def Let_def af_handle_in_proj[OF irst] im)
  next
    case c3
    thus ?thesis using 1(4)[OF c3] AF_DFS_simps(3)[OF 1(1) c3]
      by (simp add: AF_DFS_upd3_def)
  next
    case r
    thus ?thesis using AF_DFS_simps(4)[OF 1(1) r] by (simp add: AF_DFS_ret_def)
  qed
qed

lemma AF_outer_out_proj:
  assumes om: "\<And>G v. proj (out_move G v) = proj G" and orst: "\<And>G v. proj (out_reset G v) = proj G"
    and mi0: "multigraph_inv out_arr in_arr" and inv: "AFF_inv st"
  shows "proj (aff_out_arr (AF_outer st)) = proj (aff_out_arr st)"
proof -
  have "AFF_inv st \<longrightarrow> proj (aff_out_arr (AF_outer st)) = proj (aff_out_arr st)"
  proof (induction rule: AF_outer_induct[OF AF_outer_dom[OF mi0 inv]])
    case (1 st)
    show ?case
    proof
      assume invst: "AFF_inv st"
      consider (c1) "AF_outer_call_1_conds st" | (c2) "AF_outer_call_2_conds st" | (r) "AF_outer_ret_conds st"
        by (auto simp: AF_outer_call_1_conds_def AF_outer_call_2_conds_def AF_outer_ret_conds_def)
      then show "proj (aff_out_arr (AF_outer st)) = proj (aff_out_arr st)"
      proof cases
        case c1
        have ih: "proj (aff_out_arr (AF_outer (AF_outer_upd1 st))) = proj (aff_out_arr (AF_outer_upd1 st))"
          using 1(2)[OF c1] AFF_inv_holds_1[OF c1 invst] by simp
        show ?thesis using ih AF_outer_simps(1)[OF 1(1) c1] by (simp add: AF_outer_upd1_def)
      next
        case c2
        have ih: "proj (aff_out_arr (AF_outer (AF_outer_upd2 st))) = proj (aff_out_arr (AF_outer_upd2 st))"
          using 1(3)[OF c2] AFF_inv_holds_2[OF mi0 c2 invst] by simp
        from invst have ff: "flow_invar (aff_flow st)" and sti: "st_invar (aff_state st)"
          and aoi: "out_invar (aff_out_arr st)" and aii: "in_invar (aff_in_arr st)"
          and mii: "multigraph_inv (aff_out_arr st) (aff_in_arr st)" and feas: "af_cap_feasible (aff_flow st)"
          and noos: "\<not> aff_unbounded st \<longrightarrow> (\<forall>w\<in>\<V>. st_lookup (aff_state st) w \<noteq> OnStack)"
          by (auto simp: AFF_inv_def)
        from c2 have nu: "\<not> aff_unbounded st" and hv: "has_vertex (aff_vit st)" by (auto simp: AF_outer_call_2_conds_def)
        have vV: "current_vertex (aff_vit st) \<in> \<V>" using vit_current_V[OF invst hv] .
        have noos': "\<forall>w\<in>\<V>. st_lookup (aff_state st) w \<noteq> OnStack" using noos nu by simp
        have dom: "AF_DFS_dom (AF_DFS_initial (aff_flow st) (aff_out_arr st) (aff_in_arr st) (aff_state st) (current_vertex (aff_vit st)))"
          using AF_DFS_dom[OF mi0 AF_inv_initial[OF ff sti aoi aii mii vV feas noos']] .
        have pres: "proj (aff_out_arr (AF_outer_upd2 st)) = proj (aff_out_arr st)"
          using AF_DFS_out_proj[OF om orst dom] by (simp add: AF_outer_upd2_def Let_def AF_DFS_initial_def)
        show ?thesis using ih pres AF_outer_simps(2)[OF 1(1) c2] by simp
      next
        case r
        thus ?thesis using AF_outer_simps(3)[OF 1(1) r] by (simp add: AF_outer_ret_def)
      qed
    qed
  qed
  thus ?thesis using inv by simp
qed

lemma AF_outer_in_proj:
  assumes im: "\<And>G v. proj (in_move G v) = proj G" and irst: "\<And>G v. proj (in_reset G v) = proj G"
    and mi0: "multigraph_inv out_arr in_arr" and inv: "AFF_inv st"
  shows "proj (aff_in_arr (AF_outer st)) = proj (aff_in_arr st)"
proof -
  have "AFF_inv st \<longrightarrow> proj (aff_in_arr (AF_outer st)) = proj (aff_in_arr st)"
  proof (induction rule: AF_outer_induct[OF AF_outer_dom[OF mi0 inv]])
    case (1 st)
    show ?case
    proof
      assume invst: "AFF_inv st"
      consider (c1) "AF_outer_call_1_conds st" | (c2) "AF_outer_call_2_conds st" | (r) "AF_outer_ret_conds st"
        by (auto simp: AF_outer_call_1_conds_def AF_outer_call_2_conds_def AF_outer_ret_conds_def)
      then show "proj (aff_in_arr (AF_outer st)) = proj (aff_in_arr st)"
      proof cases
        case c1
        have ih: "proj (aff_in_arr (AF_outer (AF_outer_upd1 st))) = proj (aff_in_arr (AF_outer_upd1 st))"
          using 1(2)[OF c1] AFF_inv_holds_1[OF c1 invst] by simp
        show ?thesis using ih AF_outer_simps(1)[OF 1(1) c1] by (simp add: AF_outer_upd1_def)
      next
        case c2
        have ih: "proj (aff_in_arr (AF_outer (AF_outer_upd2 st))) = proj (aff_in_arr (AF_outer_upd2 st))"
          using 1(3)[OF c2] AFF_inv_holds_2[OF mi0 c2 invst] by simp
        from invst have ff: "flow_invar (aff_flow st)" and sti: "st_invar (aff_state st)"
          and aoi: "out_invar (aff_out_arr st)" and aii: "in_invar (aff_in_arr st)"
          and mii: "multigraph_inv (aff_out_arr st) (aff_in_arr st)" and feas: "af_cap_feasible (aff_flow st)"
          and noos: "\<not> aff_unbounded st \<longrightarrow> (\<forall>w\<in>\<V>. st_lookup (aff_state st) w \<noteq> OnStack)"
          by (auto simp: AFF_inv_def)
        from c2 have nu: "\<not> aff_unbounded st" and hv: "has_vertex (aff_vit st)" by (auto simp: AF_outer_call_2_conds_def)
        have vV: "current_vertex (aff_vit st) \<in> \<V>" using vit_current_V[OF invst hv] .
        have noos': "\<forall>w\<in>\<V>. st_lookup (aff_state st) w \<noteq> OnStack" using noos nu by simp
        have dom: "AF_DFS_dom (AF_DFS_initial (aff_flow st) (aff_out_arr st) (aff_in_arr st) (aff_state st) (current_vertex (aff_vit st)))"
          using AF_DFS_dom[OF mi0 AF_inv_initial[OF ff sti aoi aii mii vV feas noos']] .
        have pres: "proj (aff_in_arr (AF_outer_upd2 st)) = proj (aff_in_arr st)"
          using AF_DFS_in_proj[OF im irst dom] by (simp add: AF_outer_upd2_def Let_def AF_DFS_initial_def)
        show ?thesis using ih pres AF_outer_simps(2)[OF 1(1) c2] by simp
      next
        case r
        thus ?thesis using AF_outer_simps(3)[OF 1(1) r] by (simp add: AF_outer_ret_def)
      qed
    qed
  qed
  thus ?thesis using inv by simp
qed

subsection \<open>Top level: the result is a feasible flow of no-greater cost\<close>

text \<open>Combining totality with the invariants: the outer loop preserves @{const AFF_inv} (so the returned
      flow is feasible) and never increases the cost (D3 lifted through @{const af_handle}, @{const AF_DFS}
      and @{const AF_outer}). Hence when @{const make_acyclic} returns @{term \<open>Some f'\<close>}, @{term f'} is a
      feasible flow with @{term \<open>\<C> (h \<circ> flow_lookup f') \<le> \<C> (h \<circ> flow_lookup f0)\<close>}. (The remaining conjunct of the
      correctness theorem, acyclicity of @{term f'}, is Theme F.)\<close>

lemma AFF_inv_holds:
  assumes dom: "AF_outer_dom st" and mi0: "multigraph_inv out_arr in_arr"
    and inv: "AFF_inv st"
  shows "AFF_inv (AF_outer st)"
  using inv proof (induction rule: AF_outer_induct[OF dom])
  case IH: (1 st)
  show ?case
    apply (rule AF_outer_cases[where st = st])
    by (auto intro!: IH(2-4) AFF_inv_holds_1 AFF_inv_holds_2[OF mi0]
             simp: AF_outer_simps[OF IH(1)] AF_outer_ret_def)
qed

lemma make_acyclic_feasible:
  assumes mi0: "multigraph_inv out_arr in_arr"
    and ff: "flow_invar f0" and feas: "af_cap_feasible f0"
    and vv: "vit_invar all_vertices" and vab: "vit_abstract all_vertices \<subseteq> \<V>"
    and res: "make_acyclic f0 = Some f'"
  shows "af_cap_feasible f'"
proof -
  have dom: "AF_outer_dom (AF_outer_initial f0)"
    using AF_outer_dom[OF mi0 AFF_inv_initial[OF mi0 ff feas vv vab]] .
  have "AFF_inv (AF_outer (AF_outer_initial f0))"
    using AFF_inv_holds[OF dom mi0 AFF_inv_initial[OF mi0 ff feas vv vab]] .
  moreover have "f' = aff_flow (AF_outer (AF_outer_initial f0))"
    using res by (auto simp: make_acyclic_def Let_def split: if_splits)
  ultimately show ?thesis by (simp add: AFF_inv_def)
qed

lemma af_handle_cost_le:
  assumes A1: "AF_invar_1 st" and A2: "AF_invar_2 st" and A3: "AF_invar_3 st"
    and Afe: "AF_invar_feas st" and AE: "AF_invar_estE st"
    and ae: "a \<in> \<E>"
    and inc: "(if dir then fst a else snd a) = hd (af_vstack st)" and ne: "af_vstack st \<noteq> []"
  shows "\<C> (h \<circ> flow_lookup (af_flow (af_handle st a dir))) \<le> \<C> (h \<circ> flow_lookup (af_flow st))"
proof -
  have fi: "flow_invar (af_flow st)" using A1 by (auto simp: AF_invar_1_def)
  have feas: "af_cap_feasible (af_flow st)" using Afe by (simp add: AF_invar_feas_def)
  have estE: "set (af_estack st) \<subseteq> \<E>" using AE by (simp add: AF_invar_estE_def)
  have distES: "distinct (af_estack st)" using estack_distinct[OF A2 A3] .
  have inc': "hd (af_vstack st) \<in> {fst a, snd a}" using inc by (cases dir) auto
  obtain up dn where updn: "af_rooms (af_flow st) a = (up, dn)"
    by (cases "af_rooms (af_flow st) a") auto
  show ?thesis
  proof (cases "fst a = snd a")
    case selfl: True
    have "af_handle st a dir = af_selfloop_handle st a" using selfl by (simp add: af_handle_real[OF ae])
    thus ?thesis using af_selfloop_handle_cost_le[OF ae fi feas] by simp
  next
    case selfloop: False
    show ?thesis
    proof (cases "0 < dn \<and> (up = - 1 \<or> 0 < up)")
      case False thus ?thesis using updn selfloop by (simp add: af_handle_real[OF ae] Let_def)
    next
      case guard: True
      show ?thesis
      proof (cases "af_estack st \<noteq> [] \<and> a = hd (af_estack st)")
        case True
        have "af_handle st a dir = st"
          unfolding af_handle_real[OF ae]
          using updn guard selfloop True by (simp add: Let_def)
        thus ?thesis by simp
      next
        case parent: False
        show ?thesis
        proof (cases "st_lookup (af_state st) (if dir then snd a else fst a)")
          case Unseen
          have "af_handle st a dir = st\<lparr>af_vstack := (if dir then snd a else fst a) # af_vstack st,
              af_state := st_upd (af_state st) (if dir then snd a else fst a) OnStack,
              af_estack := a # af_estack st, af_dstack := dir # af_dstack st\<rparr>"
            using updn guard selfloop parent Unseen by (auto simp: af_handle_real[OF ae] Let_def)
          thus ?thesis by simp
        next
          case OnStack
          obtain fl m' ubd where c: "af_cancel_seg up dn (if dir then snd a else fst a)
              (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) = (fl, m', ubd)"
            by (metis prod_cases3)
          have dist: "distinct (a # af_estack st)"
            using a_notin_estack_incident[OF A2 A3 inc' ne parent] distES by simp
          have cle: "\<C> (h \<circ> flow_lookup fl) \<le> \<C> (h \<circ> flow_lookup (af_flow st))"
            using af_cancel_seg_cost_le_gen[OF feas fi dist ae estE updn c] .
          show ?thesis
          proof (cases ubd)
            case True
            have "af_handle st a dir = st\<lparr>af_unbounded := True\<rparr>"
              using updn guard selfloop parent OnStack c True by (auto simp: af_handle_real[OF ae] Let_def)
            thus ?thesis by simp
          next
            case False
            have "af_handle st a dir = af_reset_unsee_seg m' (af_vstack st)
                (st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st),
                    af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>)"
              using updn guard selfloop parent OnStack c False by (auto simp: af_handle_real[OF ae] Let_def)
            thus ?thesis using cle by simp
          qed
        next
          case Finished
          thus ?thesis using updn guard selfloop parent by (auto simp: af_handle_real[OF ae] Let_def)
        qed
      qed
    qed
  qed
qed

lemma af_cost_le_upd1:
  assumes conds: "AF_DFS_call_1_conds st" and inv: "AF_inv st"
  shows "\<C> (h \<circ> flow_lookup (af_flow (AF_DFS_upd1 st))) \<le> \<C> (h \<circ> flow_lookup (af_flow st))"
proof -
  from inv have i1: "AF_invar_1 st" and i2: "AF_invar_2 st" and i3: "AF_invar_3 st"
    and iit: "AF_invar_iter st" and iV: "AF_invar_V st" and iE: "AF_invar_estE st"
    and ife: "AF_invar_feas st" by (auto simp: AF_inv_def)
  from conds have ne: "af_vstack st \<noteq> []" and he: "out_has (af_out_arr st) (hd (af_vstack st))"
    by (auto elim!: call_cond_elims)
  have mi': "multigraph_inv (af_out_arr st) (af_in_arr st)" using iit by (simp add: AF_invar_iter_def)
  have vV: "hd (af_vstack st) \<in> \<V>" using iV ne hd_in_set by (auto simp: AF_invar_V_def)
  have endp: "fst (out_current (af_out_arr st) (hd (af_vstack st))) = hd (af_vstack st) \<and>
              out_current (af_out_arr st) (hd (af_vstack st)) \<in> \<E>"
    using af_current_out_endpoint[OF mi' vV he] by simp
  let ?st' = "st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack st))\<rparr>"
  let ?a = "out_current (af_out_arr st) (hd (af_vstack st))"
  have A1': "AF_invar_1 ?st'" by (rule AF_invar_1_out_advance[OF vV i1])
  have inc: "(if True then fst ?a else snd ?a) = hd (af_vstack ?st')" using endp by simp
  have "\<C> (h \<circ> flow_lookup (af_flow (af_handle ?st' ?a True))) \<le> \<C> (h \<circ> flow_lookup (af_flow ?st'))"
    by (rule af_handle_cost_le[OF A1' _ _ _ _ _ inc _]) (use i2 i3 ife iE endp ne in simp_all)
  thus ?thesis unfolding AF_DFS_upd1_def Let_def by (simp add: comp_def)
qed

lemma af_cost_le_upd2:
  assumes conds: "AF_DFS_call_2_conds st" and inv: "AF_inv st"
  shows "\<C> (h \<circ> flow_lookup (af_flow (AF_DFS_upd2 st))) \<le> \<C> (h \<circ> flow_lookup (af_flow st))"
proof -
  from inv have i1: "AF_invar_1 st" and i2: "AF_invar_2 st" and i3: "AF_invar_3 st"
    and iit: "AF_invar_iter st" and iV: "AF_invar_V st" and iE: "AF_invar_estE st"
    and ife: "AF_invar_feas st" by (auto simp: AF_inv_def)
  from conds have ne: "af_vstack st \<noteq> []" and he: "in_has (af_in_arr st) (hd (af_vstack st))"
    by (auto elim!: call_cond_elims)
  have mi': "multigraph_inv (af_out_arr st) (af_in_arr st)" using iit by (simp add: AF_invar_iter_def)
  have vV: "hd (af_vstack st) \<in> \<V>" using iV ne hd_in_set by (auto simp: AF_invar_V_def)
  have endp: "snd (in_current (af_in_arr st) (hd (af_vstack st))) = hd (af_vstack st) \<and>
              in_current (af_in_arr st) (hd (af_vstack st)) \<in> \<E>"
    using af_current_in_endpoint[OF mi' vV he] by simp
  let ?st' = "st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack st))\<rparr>"
  let ?a = "in_current (af_in_arr st) (hd (af_vstack st))"
  have A1': "AF_invar_1 ?st'" by (rule AF_invar_1_in_advance[OF vV i1])
  have inc: "(if False then fst ?a else snd ?a) = hd (af_vstack ?st')" using endp by simp
  have "\<C> (h \<circ> flow_lookup (af_flow (af_handle ?st' ?a False))) \<le> \<C> (h \<circ> flow_lookup (af_flow ?st'))"
    by (rule af_handle_cost_le[OF A1' _ _ _ _ _ inc _]) (use i2 i3 ife iE endp ne in simp_all)
  thus ?thesis unfolding AF_DFS_upd2_def Let_def by (simp add: comp_def)
qed

lemma af_cost_le_upd3:
  "\<C> (h \<circ> flow_lookup (af_flow (AF_DFS_upd3 st))) \<le> \<C> (h \<circ> flow_lookup (af_flow st))"
  by (simp add: AF_DFS_upd3_def)

lemma AF_DFS_cost_le:
  assumes dom: "AF_DFS_dom st" and mi0: "multigraph_inv out_arr in_arr"
  shows "AF_inv st \<longrightarrow> \<C> (h \<circ> flow_lookup (af_flow (AF_DFS st))) \<le> \<C> (h \<circ> flow_lookup (af_flow st))"
proof (induction rule: AF_DFS_induct[OF dom])
  case IH: (1 st)
  show ?case
  proof
    assume inv: "AF_inv st"
    show "\<C> (h \<circ> flow_lookup (af_flow (AF_DFS st))) \<le> \<C> (h \<circ> flow_lookup (af_flow st))"
    proof (rule AF_DFS_cases[where st = st])
      assume c: "AF_DFS_call_1_conds st"
      have "\<C> (h \<circ> flow_lookup (af_flow (AF_DFS (AF_DFS_upd1 st)))) \<le> \<C> (h \<circ> flow_lookup (af_flow (AF_DFS_upd1 st)))"
        using IH(2)[OF c] AF_inv_holds_1[OF mi0 c inv] by (simp add: comp_def)
      also have "\<dots> \<le> \<C> (h \<circ> flow_lookup (af_flow st))" using af_cost_le_upd1[OF c inv] .
      finally show ?thesis using c by (simp add: AF_DFS_simps[OF IH(1)] comp_def)
    next
      assume c: "AF_DFS_call_2_conds st"
      have "\<C> (h \<circ> flow_lookup (af_flow (AF_DFS (AF_DFS_upd2 st)))) \<le> \<C> (h \<circ> flow_lookup (af_flow (AF_DFS_upd2 st)))"
        using IH(3)[OF c] AF_inv_holds_2[OF mi0 c inv] by (simp add: comp_def)
      also have "\<dots> \<le> \<C> (h \<circ> flow_lookup (af_flow st))" using af_cost_le_upd2[OF c inv] .
      finally show ?thesis using c by (simp add: AF_DFS_simps[OF IH(1)] comp_def)
    next
      assume c: "AF_DFS_call_3_conds st"
      have "\<C> (h \<circ> flow_lookup (af_flow (AF_DFS (AF_DFS_upd3 st)))) \<le> \<C> (h \<circ> flow_lookup (af_flow (AF_DFS_upd3 st)))"
        using IH(4)[OF c] AF_inv_holds_3[OF c inv] by (simp add: comp_def)
      also have "\<dots> \<le> \<C> (h \<circ> flow_lookup (af_flow st))" using af_cost_le_upd3 .
      finally show ?thesis using c by (simp add: AF_DFS_simps[OF IH(1)] comp_def)
    next
      assume c: "AF_DFS_ret_conds st"
      thus ?thesis by (simp add: AF_DFS_simps[OF IH(1)] AF_DFS_ret_def)
    qed
  qed
qed

lemma AF_outer_cost_le:
  assumes dom: "AF_outer_dom st" and mi0: "multigraph_inv out_arr in_arr"
  shows "AFF_inv st \<longrightarrow> \<C> (h \<circ> flow_lookup (aff_flow (AF_outer st))) \<le> \<C> (h \<circ> flow_lookup (aff_flow st))"
proof (induction rule: AF_outer_induct[OF dom])
  case IH: (1 st)
  show ?case
  proof
    assume inv: "AFF_inv st"
    show "\<C> (h \<circ> flow_lookup (aff_flow (AF_outer st))) \<le> \<C> (h \<circ> flow_lookup (aff_flow st))"
    proof (rule AF_outer_cases[where st = st])
      assume c: "AF_outer_call_1_conds st"
      have "\<C> (h \<circ> flow_lookup (aff_flow (AF_outer (AF_outer_upd1 st)))) \<le> \<C> (h \<circ> flow_lookup (aff_flow (AF_outer_upd1 st)))"
        using IH(2)[OF c] AFF_inv_holds_1[OF c inv] by (simp add: comp_def)
      also have "\<C> (h \<circ> flow_lookup (aff_flow (AF_outer_upd1 st))) = \<C> (h \<circ> flow_lookup (aff_flow st))"
        by (simp add: AF_outer_upd1_def)
      finally show ?thesis using c by (simp add: AF_outer_simps[OF IH(1)] comp_def)
    next
      assume c: "AF_outer_call_2_conds st"
      from inv have ff: "flow_invar (aff_flow st)" and sti: "st_invar (aff_state st)"
        and aoi: "out_invar (aff_out_arr st)" and aii: "in_invar (aff_in_arr st)"
        and mii: "multigraph_inv (aff_out_arr st) (aff_in_arr st)" and feas: "af_cap_feasible (aff_flow st)"
        and noos: "\<not> aff_unbounded st \<longrightarrow> (\<forall>w\<in>\<V>. st_lookup (aff_state st) w \<noteq> OnStack)" by (auto simp: AFF_inv_def)
      from c have nu: "\<not> aff_unbounded st" and hv: "has_vertex (aff_vit st)" by (auto simp: AF_outer_call_2_conds_def)
      let ?v = "current_vertex (aff_vit st)"
      have vV: "?v \<in> \<V>" using vit_current_V[OF inv hv] .
      have noos': "\<forall>w\<in>\<V>. st_lookup (aff_state st) w \<noteq> OnStack" using noos nu by simp
      let ?init = "AF_DFS_initial (aff_flow st) (aff_out_arr st) (aff_in_arr st) (aff_state st) ?v"
      have invi: "AF_inv ?init" using AF_inv_initial[OF ff sti aoi aii mii vV feas noos'] .
      have domi: "AF_DFS_dom ?init" using AF_DFS_dom[OF mi0 invi] .
      have dcost: "\<C> (h \<circ> flow_lookup (af_flow (AF_DFS ?init))) \<le> \<C> (h \<circ> flow_lookup (aff_flow st))"
        using AF_DFS_cost_le[OF domi mi0] invi by (simp add: AF_DFS_initial_def comp_def)
      have "\<C> (h \<circ> flow_lookup (aff_flow (AF_outer (AF_outer_upd2 st)))) \<le> \<C> (h \<circ> flow_lookup (aff_flow (AF_outer_upd2 st)))"
        using IH(3)[OF c] AFF_inv_holds_2[OF mi0 c inv] by (simp add: comp_def)
      also have "\<C> (h \<circ> flow_lookup (aff_flow (AF_outer_upd2 st))) \<le> \<C> (h \<circ> flow_lookup (aff_flow st))"
        using dcost by (simp add: AF_outer_upd2_def Let_def comp_def)
      finally show ?thesis using c by (simp add: AF_outer_simps[OF IH(1)] comp_def)
    next
      assume c: "AF_outer_ret_conds st"
      thus ?thesis by (simp add: AF_outer_simps[OF IH(1)] AF_outer_ret_def)
    qed
  qed
qed

lemma make_acyclic_cost_le:
  assumes mi0: "multigraph_inv out_arr in_arr"
    and ff: "flow_invar f0" and feas: "af_cap_feasible f0"
    and vv: "vit_invar all_vertices" and vab: "vit_abstract all_vertices \<subseteq> \<V>"
    and res: "make_acyclic f0 = Some f'"
  shows "\<C> (h \<circ> flow_lookup f') \<le> \<C> (h \<circ> flow_lookup f0)"
proof -
  have dom: "AF_outer_dom (AF_outer_initial f0)"
    using AF_outer_dom[OF mi0 AFF_inv_initial[OF mi0 ff feas vv vab]] .
  have "\<C> (h \<circ> flow_lookup (aff_flow (AF_outer (AF_outer_initial f0)))) \<le> \<C> (h \<circ> flow_lookup (aff_flow (AF_outer_initial f0)))"
    using AF_outer_cost_le[OF dom mi0] AFF_inv_initial[OF mi0 ff feas vv vab] by (simp add: comp_def)
  moreover have "aff_flow (AF_outer_initial f0) = f0" by (simp add: AF_outer_initial_def)
  moreover have "f' = aff_flow (AF_outer (AF_outer_initial f0))"
    using res by (auto simp: make_acyclic_def Let_def split: if_splits)
  ultimately show ?thesis by simp
qed

subsection \<open>Cancellation preserves the balance through the whole run\<close>

text \<open>The divergence half of Theme D1, lifted to @{const make_acyclic}: every @{const af_handle} step
      leaves every vertex's excess unchanged (a step either does not touch the flow, or cancels a
      cycle, which by @{thm af_cancel_seg_ex_pres} preserves excess), hence so does the whole DFS and
      the outer loop. This threads exactly like the cost bound, but as an \emph{equality}.\<close>

lemma af_handle_ex:
  assumes A1: "AF_invar_1 st" and A2: "AF_invar_2 st" and A3: "AF_invar_3 st"
    and AE: "AF_invar_estE st" and ae: "a \<in> \<E>"
    and inc: "(if dir then fst a else snd a) = hd (af_vstack st)" and ne: "af_vstack st \<noteq> []"
  shows "ex (h \<circ> flow_lookup (af_flow (af_handle st a dir))) v = ex (h \<circ> flow_lookup (af_flow st)) v"
proof -
  have fi: "flow_invar (af_flow st)" using A1 by (auto simp: AF_invar_1_def)
  have estE: "set (af_estack st) \<subseteq> \<E>" using AE by (simp add: AF_invar_estE_def)
  have tr: "af_trail (af_vstack st) (af_estack st) (af_dstack st)" using A3 by (simp add: AF_invar_3_conv)
  have inc': "hd (af_vstack st) \<in> {fst a, snd a}" using inc by (cases dir) auto
  have cpl: "Suc (length (af_estack st)) = length (af_vstack st)"
            "length (af_dstack st) = length (af_estack st)"
    using A2 ne by (auto simp: AF_invar_2_def)
  obtain up dn where updn: "af_rooms (af_flow st) a = (up, dn)"
    by (cases "af_rooms (af_flow st) a") auto
  show ?thesis
  proof (cases "fst a = snd a")
    case selfl: True
    have "af_handle st a dir = af_selfloop_handle st a" using selfl by (simp add: af_handle_real[OF ae])
    thus ?thesis using af_selfloop_handle_ex[OF ae selfl fi] by simp
  next
    case selfloop: False
    show ?thesis
    proof (cases "0 < dn \<and> (up = - 1 \<or> 0 < up)")
      case False thus ?thesis using updn selfloop by (simp add: af_handle_real[OF ae] Let_def)
    next
      case guard: True
      show ?thesis
      proof (cases "af_estack st \<noteq> [] \<and> a = hd (af_estack st)")
        case True
        have "af_handle st a dir = st"
          unfolding af_handle_real[OF ae]
          using updn guard selfloop True by (simp add: Let_def)
        thus ?thesis by simp
      next
        case parent: False
        show ?thesis
        proof (cases "st_lookup (af_state st) (if dir then snd a else fst a)")
          case Unseen
          have "af_handle st a dir = st\<lparr>af_vstack := (if dir then snd a else fst a) # af_vstack st,
              af_state := st_upd (af_state st) (if dir then snd a else fst a) OnStack,
              af_estack := a # af_estack st, af_dstack := dir # af_dstack st\<rparr>"
            using updn guard selfloop parent Unseen by (auto simp: af_handle_real[OF ae] Let_def)
          thus ?thesis by simp
        next
          case OnStack
          obtain fl m' ubd where c: "af_cancel_seg up dn (if dir then snd a else fst a)
              (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) = (fl, m', ubd)"
            by (metis prod_cases3)
          have xV: "(if dir then snd a else fst a) \<in> \<V>"
            using fst_E_V[OF ae] snd_E_V[OF ae] by (cases dir) auto
          have xstack: "(if dir then snd a else fst a) \<in> set (af_vstack st)"
            using OnStack A2 xV by (auto simp: AF_invar_2_def)
          have xnhd: "(if dir then snd a else fst a) \<noteq> hd (af_vstack st)"
            using inc selfloop by (cases dir) auto
          have reach: "(if dir then snd a else fst a) \<in> set (tl (af_vstack st))"
            using xstack xnhd ne by (cases "af_vstack st") auto
          have exfl: "ex (h \<circ> flow_lookup fl) v = ex (h \<circ> flow_lookup (af_flow st)) v"
            using af_cancel_seg_ex_pres[OF fi tr estE ae cpl(1) cpl(2) reach inc refl c] .
          show ?thesis
          proof (cases ubd)
            case True
            have "af_handle st a dir = st\<lparr>af_unbounded := True\<rparr>"
              using updn guard selfloop parent OnStack c True by (auto simp: af_handle_real[OF ae] Let_def)
            thus ?thesis by simp
          next
            case False
            have "af_handle st a dir = af_reset_unsee_seg m' (af_vstack st)
                (st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st),
                    af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>)"
              using updn guard selfloop parent OnStack c False by (auto simp: af_handle_real[OF ae] Let_def)
            thus ?thesis using exfl by simp
          qed
        next
          case Finished
          thus ?thesis using updn guard selfloop parent by (auto simp: af_handle_real[OF ae] Let_def)
        qed
      qed
    qed
  qed
qed

text \<open>The excess-preservation of one DFS step, lifted through the recursion (mirrors the cost bound).\<close>

lemma af_ex_upd1:
  assumes conds: "AF_DFS_call_1_conds st" and inv: "AF_inv st"
  shows "ex (h \<circ> flow_lookup (af_flow (AF_DFS_upd1 st))) v = ex (h \<circ> flow_lookup (af_flow st)) v"
proof -
  from inv have i1: "AF_invar_1 st" and i2: "AF_invar_2 st" and i3: "AF_invar_3 st"
    and iit: "AF_invar_iter st" and iV: "AF_invar_V st" and iE: "AF_invar_estE st" by (auto simp: AF_inv_def)
  from conds have ne: "af_vstack st \<noteq> []" and he: "out_has (af_out_arr st) (hd (af_vstack st))"
    by (auto elim!: call_cond_elims)
  have mi': "multigraph_inv (af_out_arr st) (af_in_arr st)" using iit by (simp add: AF_invar_iter_def)
  have vV: "hd (af_vstack st) \<in> \<V>" using iV ne hd_in_set by (auto simp: AF_invar_V_def)
  have endp: "fst (out_current (af_out_arr st) (hd (af_vstack st))) = hd (af_vstack st) \<and>
              out_current (af_out_arr st) (hd (af_vstack st)) \<in> \<E>"
    using af_current_out_endpoint[OF mi' vV he] by simp
  let ?st' = "st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack st))\<rparr>"
  let ?a = "out_current (af_out_arr st) (hd (af_vstack st))"
  have A1': "AF_invar_1 ?st'" by (rule AF_invar_1_out_advance[OF vV i1])
  have inc: "(if True then fst ?a else snd ?a) = hd (af_vstack ?st')" using endp by simp
  have "ex (h \<circ> flow_lookup (af_flow (af_handle ?st' ?a True))) v = ex (h \<circ> flow_lookup (af_flow ?st')) v"
    by (rule af_handle_ex[OF A1' _ _ _ _ inc _]) (use i2 i3 iE endp ne in simp_all)
  thus ?thesis unfolding AF_DFS_upd1_def Let_def by (simp add: comp_def)
qed

lemma af_ex_upd2:
  assumes conds: "AF_DFS_call_2_conds st" and inv: "AF_inv st"
  shows "ex (h \<circ> flow_lookup (af_flow (AF_DFS_upd2 st))) v = ex (h \<circ> flow_lookup (af_flow st)) v"
proof -
  from inv have i1: "AF_invar_1 st" and i2: "AF_invar_2 st" and i3: "AF_invar_3 st"
    and iit: "AF_invar_iter st" and iV: "AF_invar_V st" and iE: "AF_invar_estE st" by (auto simp: AF_inv_def)
  from conds have ne: "af_vstack st \<noteq> []" and he: "in_has (af_in_arr st) (hd (af_vstack st))"
    by (auto elim!: call_cond_elims)
  have mi': "multigraph_inv (af_out_arr st) (af_in_arr st)" using iit by (simp add: AF_invar_iter_def)
  have vV: "hd (af_vstack st) \<in> \<V>" using iV ne hd_in_set by (auto simp: AF_invar_V_def)
  have endp: "snd (in_current (af_in_arr st) (hd (af_vstack st))) = hd (af_vstack st) \<and>
              in_current (af_in_arr st) (hd (af_vstack st)) \<in> \<E>"
    using af_current_in_endpoint[OF mi' vV he] by simp
  let ?st' = "st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack st))\<rparr>"
  let ?a = "in_current (af_in_arr st) (hd (af_vstack st))"
  have A1': "AF_invar_1 ?st'" by (rule AF_invar_1_in_advance[OF vV i1])
  have inc: "(if False then fst ?a else snd ?a) = hd (af_vstack ?st')" using endp by simp
  have "ex (h \<circ> flow_lookup (af_flow (af_handle ?st' ?a False))) v = ex (h \<circ> flow_lookup (af_flow ?st')) v"
    by (rule af_handle_ex[OF A1' _ _ _ _ inc _]) (use i2 i3 iE endp ne in simp_all)
  thus ?thesis unfolding AF_DFS_upd2_def Let_def by (simp add: comp_def)
qed

lemma af_ex_upd3:
  "ex (h \<circ> flow_lookup (af_flow (AF_DFS_upd3 st))) v = ex (h \<circ> flow_lookup (af_flow st)) v"
  by (simp add: AF_DFS_upd3_def)

lemma AF_DFS_ex:
  assumes dom: "AF_DFS_dom st" and mi0: "multigraph_inv out_arr in_arr"
  shows "AF_inv st \<longrightarrow> ex (h \<circ> flow_lookup (af_flow (AF_DFS st))) v = ex (h \<circ> flow_lookup (af_flow st)) v"
proof (induction rule: AF_DFS_induct[OF dom])
  case IH: (1 st)
  show ?case
  proof
    assume inv: "AF_inv st"
    show "ex (h \<circ> flow_lookup (af_flow (AF_DFS st))) v = ex (h \<circ> flow_lookup (af_flow st)) v"
    proof (rule AF_DFS_cases[where st = st])
      assume c: "AF_DFS_call_1_conds st"
      have "ex (h \<circ> flow_lookup (af_flow (AF_DFS (AF_DFS_upd1 st)))) v = ex (h \<circ> flow_lookup (af_flow (AF_DFS_upd1 st))) v"
        using IH(2)[OF c] AF_inv_holds_1[OF mi0 c inv] by (simp add: comp_def)
      also have "\<dots> = ex (h \<circ> flow_lookup (af_flow st)) v" using af_ex_upd1[OF c inv] .
      finally show ?thesis using c by (simp add: AF_DFS_simps[OF IH(1)] comp_def)
    next
      assume c: "AF_DFS_call_2_conds st"
      have "ex (h \<circ> flow_lookup (af_flow (AF_DFS (AF_DFS_upd2 st)))) v = ex (h \<circ> flow_lookup (af_flow (AF_DFS_upd2 st))) v"
        using IH(3)[OF c] AF_inv_holds_2[OF mi0 c inv] by (simp add: comp_def)
      also have "\<dots> = ex (h \<circ> flow_lookup (af_flow st)) v" using af_ex_upd2[OF c inv] .
      finally show ?thesis using c by (simp add: AF_DFS_simps[OF IH(1)] comp_def)
    next
      assume c: "AF_DFS_call_3_conds st"
      have "ex (h \<circ> flow_lookup (af_flow (AF_DFS (AF_DFS_upd3 st)))) v = ex (h \<circ> flow_lookup (af_flow (AF_DFS_upd3 st))) v"
        using IH(4)[OF c] AF_inv_holds_3[OF c inv] by (simp add: comp_def)
      also have "\<dots> = ex (h \<circ> flow_lookup (af_flow st)) v" using af_ex_upd3 .
      finally show ?thesis using c by (simp add: AF_DFS_simps[OF IH(1)] comp_def)
    next
      assume c: "AF_DFS_ret_conds st"
      thus ?thesis by (simp add: AF_DFS_simps[OF IH(1)] AF_DFS_ret_def)
    qed
  qed
qed

lemma AF_outer_ex:
  assumes dom: "AF_outer_dom st" and mi0: "multigraph_inv out_arr in_arr"
  shows "AFF_inv st \<longrightarrow> ex (h \<circ> flow_lookup (aff_flow (AF_outer st))) v = ex (h \<circ> flow_lookup (aff_flow st)) v"
proof (induction rule: AF_outer_induct[OF dom])
  case IH: (1 st)
  show ?case
  proof
    assume inv: "AFF_inv st"
    show "ex (h \<circ> flow_lookup (aff_flow (AF_outer st))) v = ex (h \<circ> flow_lookup (aff_flow st)) v"
    proof (rule AF_outer_cases[where st = st])
      assume c: "AF_outer_call_1_conds st"
      have "ex (h \<circ> flow_lookup (aff_flow (AF_outer (AF_outer_upd1 st)))) v = ex (h \<circ> flow_lookup (aff_flow (AF_outer_upd1 st))) v"
        using IH(2)[OF c] AFF_inv_holds_1[OF c inv] by (simp add: comp_def)
      also have "ex (h \<circ> flow_lookup (aff_flow (AF_outer_upd1 st))) v = ex (h \<circ> flow_lookup (aff_flow st)) v"
        by (simp add: AF_outer_upd1_def)
      finally show ?thesis using c by (simp add: AF_outer_simps[OF IH(1)] comp_def)
    next
      assume c: "AF_outer_call_2_conds st"
      from inv have ff: "flow_invar (aff_flow st)" and sti: "st_invar (aff_state st)"
        and aoi: "out_invar (aff_out_arr st)" and aii: "in_invar (aff_in_arr st)"
        and mii: "multigraph_inv (aff_out_arr st) (aff_in_arr st)" and feas: "af_cap_feasible (aff_flow st)"
        and noos: "\<not> aff_unbounded st \<longrightarrow> (\<forall>w\<in>\<V>. st_lookup (aff_state st) w \<noteq> OnStack)" by (auto simp: AFF_inv_def)
      from c have nu: "\<not> aff_unbounded st" and hv: "has_vertex (aff_vit st)" by (auto simp: AF_outer_call_2_conds_def)
      let ?v = "current_vertex (aff_vit st)"
      have vV: "?v \<in> \<V>" using vit_current_V[OF inv hv] .
      have noos': "\<forall>w\<in>\<V>. st_lookup (aff_state st) w \<noteq> OnStack" using noos nu by simp
      let ?init = "AF_DFS_initial (aff_flow st) (aff_out_arr st) (aff_in_arr st) (aff_state st) ?v"
      have invi: "AF_inv ?init" using AF_inv_initial[OF ff sti aoi aii mii vV feas noos'] .
      have domi: "AF_DFS_dom ?init" using AF_DFS_dom[OF mi0 invi] .
      have dex: "ex (h \<circ> flow_lookup (af_flow (AF_DFS ?init))) v = ex (h \<circ> flow_lookup (aff_flow st)) v"
        using AF_DFS_ex[OF domi mi0] invi by (simp add: AF_DFS_initial_def comp_def)
      have "ex (h \<circ> flow_lookup (aff_flow (AF_outer (AF_outer_upd2 st)))) v = ex (h \<circ> flow_lookup (aff_flow (AF_outer_upd2 st))) v"
        using IH(3)[OF c] AFF_inv_holds_2[OF mi0 c inv] by (simp add: comp_def)
      also have "ex (h \<circ> flow_lookup (aff_flow (AF_outer_upd2 st))) v = ex (h \<circ> flow_lookup (aff_flow st)) v"
        using dex by (simp add: AF_outer_upd2_def Let_def comp_def)
      finally show ?thesis using c by (simp add: AF_outer_simps[OF IH(1)] comp_def)
    next
      assume c: "AF_outer_ret_conds st"
      thus ?thesis by (simp add: AF_outer_simps[OF IH(1)] AF_outer_ret_def)
    qed
  qed
qed

lemma make_acyclic_ex:
  assumes mi0: "multigraph_inv out_arr in_arr"
    and ff: "flow_invar f0" and feas: "af_cap_feasible f0"
    and vv: "vit_invar all_vertices" and vab: "vit_abstract all_vertices \<subseteq> \<V>"
    and res: "make_acyclic f0 = Some f'"
  shows "ex (h \<circ> flow_lookup f') v = ex (h \<circ> flow_lookup f0) v"
proof -
  have dom: "AF_outer_dom (AF_outer_initial f0)"
    using AF_outer_dom[OF mi0 AFF_inv_initial[OF mi0 ff feas vv vab]] .
  have "ex (h \<circ> flow_lookup (aff_flow (AF_outer (AF_outer_initial f0)))) v = ex (h \<circ> flow_lookup (aff_flow (AF_outer_initial f0))) v"
    using AF_outer_ex[OF dom mi0] AFF_inv_initial[OF mi0 ff feas vv vab] by (simp add: comp_def)
  moreover have "aff_flow (AF_outer_initial f0) = f0" by (simp add: AF_outer_initial_def)
  moreover have "f' = aff_flow (AF_outer (AF_outer_initial f0))"
    using res by (auto simp: make_acyclic_def Let_def split: if_splits)
  ultimately show ?thesis by simp
qed

text \<open>Feasibility as a genuine @{term b}-flow is preserved: the output keeps capacity feasibility
      (@{thm make_acyclic_feasible}) and, since every vertex's excess is unchanged
      (@{thm make_acyclic_ex}), the same balance @{term b} as the input.\<close>

lemma make_acyclic_feasible_bal:
  assumes mi0: "multigraph_inv out_arr in_arr"
    and ff: "flow_invar f0" and feas: "af_feasible b f0"
    and vv: "vit_invar all_vertices" and vab: "vit_abstract all_vertices \<subseteq> \<V>"
    and res: "make_acyclic f0 = Some f'"
  shows "af_feasible b f'"
proof -
  have capf0: "af_cap_feasible f0" using feas by (rule af_feasible_cap)
  have capf': "af_cap_feasible f'" using make_acyclic_feasible[OF mi0 ff capf0 vv vab res] .
  show ?thesis
  proof (rule af_feasibleI[OF capf'])
    fix v assume vV: "v \<in> \<V>"
    have b0: "- ex (h \<circ> flow_lookup f0) v = b v" using af_feasible_bal[OF feas vV] .
    have exeq: "ex (h \<circ> flow_lookup f') v = ex (h \<circ> flow_lookup f0) v"
      using make_acyclic_ex[OF mi0 ff capf0 vv vab res] .
    show "- ex (h \<circ> flow_lookup f') v = b v" using b0 exeq by simp
  qed
qed

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
  assumes p1: "0 < \<uu>\<^bsub>h \<circ> flow_lookup f'\<^esub> e"
      and p2: "0 < \<uu>\<^bsub>h \<circ> flow_lookup f'\<^esub> (erev e)"
      and e_in_E: "e \<in> \<EE>"
  shows "af_arc_free f' (oedge e)"
proof -
  have key: "0 < flow_lookup f' (oedge e) \<and> ereal (h (flow_lookup f' (oedge e))) < \<u> (oedge e)"
  proof (cases e)
    case (F a)
    show ?thesis using p1 p2 u_non_neg[of a] F by (cases "\<u> a") auto
  next
    case (B a)
    show ?thesis using p1 p2 u_non_neg[of a] B by (cases "\<u> a") auto
  qed
  have pos: "0 < flow_lookup f' (oedge e)" using key by simp
  have oE: "oedge e \<in> \<E>" using e_in_E by (auto simp: \<EE>_def)
  have "cap (oedge e) = - 1 \<or> flow_lookup f' (oedge e) < cap (oedge e)"
  proof (cases "\<u> (oedge e) = \<infinity>")
    case True
    hence "cap (oedge e) = - 1" using cap_encoding[OF oE] by simp
    thus ?thesis by simp
  next
    case False
    hence ueq: "\<u> (oedge e) = ereal (h (cap (oedge e)))" using cap_encoding[OF oE] by simp
    have "flow_lookup f' (oedge e) < cap (oedge e)" using key ueq by simp
    thus ?thesis by simp
  qed
  thus ?thesis using pos by (simp add: af_arc_free_def)
qed

lemma acyclic_witness_arcs_free:
  assumes ap: "augpath (h \<circ> flow_lookup f') C" and apr: "augpath (h \<circ> flow_lookup f') (map erev (rev C))"
    and e: "e \<in> set C" and e_in_E:"e \<in> \<EE>"
  shows "af_arc_free f' (oedge e)"
proof -
  have "0 < \<uu>\<^bsub>h \<circ> flow_lookup f'\<^esub> e"
    using ap e by (auto simp: augpath_def intro: rcap_extr_non_zero[where es = C and ES = "set C"])
  moreover have "erev e \<in> set (map erev (rev C))" using e by auto
  hence "0 < \<uu>\<^bsub>h \<circ> flow_lookup f'\<^esub> (erev e)"
    using apr by (auto simp: augpath_def
                      intro: rcap_extr_non_zero[where es = "map erev (rev C)" and ES = "set (map erev (rev C))"])
  ultimately show ?thesis
    using e_in_E
    by (rule residual_both_ways_free)
qed

lemma acyclic_flow_from_no_free_cycle:
  assumes "\<nexists>C. prepath C \<and> (\<forall>e\<in>set C. af_arc_free f' (oedge e)) \<and> distinct (map oedge C)
              \<and> fstv (hd C) = sndv (last C) \<and> set C \<subseteq> \<EE>"
  shows "acyclic_flow (h \<circ> flow_lookup f')"
proof (rule acyclic_flowI)
  fix C
  assume a: "augpath (h \<circ> flow_lookup f') C" "augpath (h \<circ> flow_lookup f') (map erev (rev C))"
    "distinct (map oedge C)" "fstv (hd C) = sndv (last C)" "set C \<subseteq> \<EE>"
  have "prepath C" using a(1) by (simp add: augpath_def)
  moreover have "\<forall>e\<in>set C. af_arc_free f' (oedge e)"
    using acyclic_witness_arcs_free[OF a(1) a(2)] a(5) by blast
  ultimately show False using assms a(3-5) by blast
qed

text \<open>The converse bridge, used when consuming acyclicity: a \emph{free} arc admits strictly positive
      residual capacity in both directions (forward @{term \<open>\<u> a - f a\<close>} --- positive because either the
      capacity is infinite or the flow is below it --- and backward @{term \<open>f a\<close>} --- positive because the
      flow is strictly positive). Hence a closed pre-path of free arcs is augmenting in both directions,
      which an @{const acyclic_flow} forbids.\<close>

lemma free_arc_both_ways:
  assumes free: "af_arc_free f' (oedge e)" and e_in_E: "e \<in> \<EE>"
  shows "0 < rcap (h \<circ> flow_lookup f') e \<and> 0 < rcap (h \<circ> flow_lookup f') (erev e)"
proof -
  from e_in_E have oE: "oedge e \<in> \<E>" by (auto simp: \<EE>_def)
  from free have fpos: "0 < flow_lookup f' (oedge e)"
    and cc: "cap (oedge e) = - 1 \<or> flow_lookup f' (oedge e) < cap (oedge e)"
    by (auto simp: af_arc_free_def Let_def)
  have unn: "\<u> (oedge e) \<ge> 0" by (rule u_non_neg)
  have room: "0 < \<u> (oedge e) - ereal (h (flow_lookup f' (oedge e)))"
  proof (cases "\<u> (oedge e) = \<infinity>")
    case True thus ?thesis by simp
  next
    case False
    hence ueq: "\<u> (oedge e) = ereal (h (cap (oedge e)))" using cap_encoding[OF oE] by simp
    have cne: "cap (oedge e) \<noteq> - 1" using ueq unn by (auto simp: zero_ereal_def)
    hence flt: "flow_lookup f' (oedge e) < cap (oedge e)" using cc by simp
    show ?thesis using flt ueq by simp
  qed
  show ?thesis
  proof (cases e)
    case (F d) show ?thesis using F room fpos by (simp add: comp_def)
  next
    case (B d) show ?thesis using B room fpos by (simp add: comp_def)
  qed
qed

text \<open>Consuming acyclicity: an @{const acyclic_flow} has \emph{no} closed pre-path of pairwise
      distinct free arcs. This is the exact converse of @{thm acyclic_flow_from_no_free_cycle} and is
      what the initial-basis construction uses to prove the free edges form a forest (every free edge
      is a tree edge).\<close>

lemma acyclic_flow_no_free_cycle:
  assumes acyc: "acyclic_flow (h \<circ> flow_lookup f')"
  shows "\<nexists>C. prepath C \<and> (\<forall>e\<in>set C. af_arc_free f' (oedge e)) \<and> distinct (map oedge C)
              \<and> fstv (hd C) = sndv (last C) \<and> set C \<subseteq> \<EE>"
proof (rule notI, elim exE conjE)
  fix C
  assume pp: "prepath C" and fr: "\<forall>e\<in>set C. af_arc_free f' (oedge e)"
    and dist: "distinct (map oedge C)" and clsd: "fstv (hd C) = sndv (last C)"
    and sub: "set C \<subseteq> \<EE>"
  have both: "\<And>e. e \<in> set C \<Longrightarrow>
                0 < rcap (h \<circ> flow_lookup f') e \<and> 0 < rcap (h \<circ> flow_lookup f') (erev e)"
  proof -
    fix e assume eC: "e \<in> set C"
    have "af_arc_free f' (oedge e)" using fr eC by blast
    moreover have "e \<in> \<EE>" using sub eC by blast
    ultimately show "0 < rcap (h \<circ> flow_lookup f') e \<and> 0 < rcap (h \<circ> flow_lookup f') (erev e)"
      by (rule free_arc_both_ways)
  qed
  have fwd: "\<And>e. e \<in> set C \<Longrightarrow> 0 < rcap (h \<circ> flow_lookup f') e" using both by blast
  have bwd: "\<And>e. e \<in> set C \<Longrightarrow> 0 < rcap (h \<circ> flow_lookup f') (erev e)" using both by blast
  show False by (rule acyclic_no_free_closed_prepath[OF acyc pp fwd bwd dist clsd sub])
qed

text \<open>The full Some-case correctness statement. Feasibility and non-increasing cost are proved
      outright; acyclicity is reduced (via @{thm acyclic_flow_from_no_free_cycle}) to the single
      combinatorial obligation that the returned flow carries no closed trail of distinct free arcs.
      Discharging that obligation from the DFS exploration is Theme F, part 2 (the forest engine).\<close>

subsection \<open>Theme F, part 2 (in progress): the exploration engine\<close>

text \<open>Towards discharging the no-free-cycle obligation. A first load-bearing building block:
      \emph{finished vertices stay finished}. No @{const af_handle} branch ever un-finishes a vertex
      --- a push touches only a fresh (@{term Unseen}) vertex, a cancellation's reset un-sees only
      \emph{stack} vertices (which are @{term OnStack}, never @{term Finished}), and the flow-only
      branches leave @{const af_state} untouched. Lifting through the three step operators and the whole
      @{const AF_DFS} recursion gives that a vertex finished at any point remains finished at the end of
      the DFS. (Combined with vertex coverage and the forest invariant --- still to come --- this yields
      the terminal ``all incident free arcs of a finished vertex are already resolved'' needed for the
      no-free-cycle claim.)\<close>

lemma af_handle_finished_mono:
  assumes A1: "AF_invar_1 st" and A2: "AF_invar_2 st" and ae: "a \<in> \<E>" and AV: "AF_invar_V st"
    and Fin: "st_lookup (af_state st) w = Finished"
  shows "st_lookup (af_state (af_handle st a dir)) w = Finished"
proof -
  have si: "st_invar (af_state st)" using A1 by (simp add: AF_invar_1_def)
  have wnv: "w \<notin> set (af_vstack st)"
  proof
    assume win: "w \<in> set (af_vstack st)"
    hence wV: "w \<in> \<V>" using AV by (auto simp: AF_invar_V_def)
    from win wV have "st_lookup (af_state st) w = OnStack" using A2 by (auto simp: AF_invar_2_def)
    with Fin show False by simp
  qed
  obtain up dn where updn: "af_rooms (af_flow st) a = (up, dn)" by (cases "af_rooms (af_flow st) a") auto
  show ?thesis
  proof (cases "fst_exec a = snd_exec a")
    case True
    have "af_handle st a dir = af_selfloop_handle st a" using True by (simp add: af_handle_def)
    thus ?thesis using Fin by simp
  next
    case selfloop: False
    show ?thesis
    proof (cases "0 < dn \<and> (up = - 1 \<or> 0 < up)")
      case False thus ?thesis using updn selfloop Fin by (simp add: af_handle_def Let_def)
    next
      case guard: True
      show ?thesis
      proof (cases "af_estack st \<noteq> [] \<and> a = hd (af_estack st)")
        case True thus ?thesis using updn guard selfloop Fin by (simp add: af_handle_def Let_def)
      next
        case parent: False
        show ?thesis
        proof (cases "st_lookup (af_state st) (if dir then snd_exec a else fst_exec a)")
          case Unseen
          have xne: "(if dir then snd_exec a else fst_exec a) \<noteq> w" using Unseen Fin by auto
          have cV: "(if dir then snd_exec a else fst_exec a) \<in> \<V>"
            using ae fst_E_V[OF ae] snd_E_V[OF ae] by (cases dir) (auto simp: snd_exec_eq[OF ae] fst_exec_eq[OF ae])
          show ?thesis using updn guard selfloop parent Unseen Fin xne
            by (auto simp: af_handle_def Let_def state_arr.fixed_univ_map_upd[OF si cV])
          next
          case OnStack
          obtain fl m' ubd where c: "af_cancel_seg up dn (if dir then snd_exec a else fst_exec a)
              (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) = (fl, m', ubd)"
            by (metis prod_cases3)
          show ?thesis
          proof (cases ubd)
            case True
            thus ?thesis using updn guard selfloop parent OnStack c Fin by (auto simp: af_handle_def Let_def)
          next
            case False
            let ?dst = "st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st),
                    af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>"
            have red: "af_handle st a dir = af_reset_unsee_seg m' (af_vstack st) ?dst"
              using updn guard selfloop parent OnStack c False by (auto simp: af_handle_def Let_def)
            have wnv': "w \<notin> set (take m' (af_vstack st))" using wnv by (meson in_set_takeD)
            have sid: "st_invar (af_state ?dst)" using si by simp
            have vsV: "set (af_vstack st) \<subseteq> \<V>" using AV by (simp add: AF_invar_V_def)
            show ?thesis using red af_reset_unsee_seg_state[OF vsV sid, of m' w] wnv' Fin by simp
          qed
        next
          case Finished
          thus ?thesis using updn guard selfloop parent Fin by (simp add: af_handle_def Let_def)
        qed
      qed
    qed
  qed
qed

lemma af_finished_mono_upd1:
  assumes inv: "AF_inv st" and conds: "AF_DFS_call_1_conds st" and Fin: "st_lookup (af_state st) w = Finished"
  shows "st_lookup (af_state (AF_DFS_upd1 st)) w = Finished"
proof -
  from inv have i1: "AF_invar_1 st" and i2: "AF_invar_2 st" and iit: "AF_invar_iter st"
    and iV: "AF_invar_V st" by (auto simp: AF_inv_def)
  from conds have ne: "af_vstack st \<noteq> []" and he: "out_has (af_out_arr st) (hd (af_vstack st))"
    by (auto elim!: call_cond_elims)
  have mi': "multigraph_inv (af_out_arr st) (af_in_arr st)" using iit by (simp add: AF_invar_iter_def)
  have vV: "hd (af_vstack st) \<in> \<V>" using iV ne hd_in_set by (auto simp: AF_invar_V_def)
  have ae: "out_current (af_out_arr st) (hd (af_vstack st)) \<in> \<E>"
    using af_current_out_endpoint[OF mi' vV he] by simp
  let ?st' = "st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack st))\<rparr>"
  have "st_lookup (af_state (af_handle ?st'
          (out_current (af_out_arr st) (hd (af_vstack st))) True)) w = Finished"
    by (rule af_handle_finished_mono[OF AF_invar_1_out_advance[OF vV i1]])
       (use i2 ae iV Fin in \<open>simp_all add: AF_invar_2_def AF_invar_V_def\<close>)
  thus ?thesis by (simp add: AF_DFS_upd1_def Let_def)
qed

lemma af_finished_mono_upd2:
  assumes inv: "AF_inv st" and conds: "AF_DFS_call_2_conds st" and Fin: "st_lookup (af_state st) w = Finished"
  shows "st_lookup (af_state (AF_DFS_upd2 st)) w = Finished"
proof -
  from inv have i1: "AF_invar_1 st" and i2: "AF_invar_2 st" and iit: "AF_invar_iter st"
    and iV: "AF_invar_V st" by (auto simp: AF_inv_def)
  from conds have ne: "af_vstack st \<noteq> []" and he: "in_has (af_in_arr st) (hd (af_vstack st))"
    by (auto elim!: call_cond_elims)
  have mi': "multigraph_inv (af_out_arr st) (af_in_arr st)" using iit by (simp add: AF_invar_iter_def)
  have vV: "hd (af_vstack st) \<in> \<V>" using iV ne hd_in_set by (auto simp: AF_invar_V_def)
  have ae: "in_current (af_in_arr st) (hd (af_vstack st)) \<in> \<E>"
    using af_current_in_endpoint[OF mi' vV he] by simp
  let ?st' = "st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack st))\<rparr>"
  have "st_lookup (af_state (af_handle ?st'
          (in_current (af_in_arr st) (hd (af_vstack st))) False)) w = Finished"
    by (rule af_handle_finished_mono[OF AF_invar_1_in_advance[OF vV i1]])
       (use i2 ae iV Fin in \<open>simp_all add: AF_invar_2_def AF_invar_V_def\<close>)
  thus ?thesis by (simp add: AF_DFS_upd2_def Let_def)
qed

lemma af_finished_mono_upd3:
  assumes inv: "AF_inv st" and conds: "AF_DFS_call_3_conds st" and Fin: "st_lookup (af_state st) w = Finished"
  shows "st_lookup (af_state (AF_DFS_upd3 st)) w = Finished"
proof -
  from inv have i1: "AF_invar_1 st" and iV: "AF_invar_V st" by (auto simp: AF_inv_def)
  have si: "st_invar (af_state st)" using i1 by (simp add: AF_invar_1_def)
  from conds obtain v vs where vv: "af_vstack st = v # vs" by (auto elim!: call_cond_elims)
  have vV: "v \<in> \<V>" using iV vv by (auto simp: AF_invar_V_def)
  show ?thesis using Fin si vv by (simp add: AF_DFS_upd3_def state_arr.fixed_univ_map_upd[OF si vV])
qed

lemma AF_DFS_finished_mono:
  assumes dom: "AF_DFS_dom st" and mi0: "multigraph_inv out_arr in_arr"
  shows "AF_inv st \<longrightarrow> st_lookup (af_state st) w = Finished \<longrightarrow> st_lookup (af_state (AF_DFS st)) w = Finished"
proof (induction rule: AF_DFS_induct[OF dom])
  case IH: (1 st)
  show ?case
  proof (intro impI)
    assume inv: "AF_inv st" and Fin: "st_lookup (af_state st) w = Finished"
    from inv have i1: "AF_invar_1 st" and i2: "AF_invar_2 st" by (auto simp: AF_inv_def)
    show "st_lookup (af_state (AF_DFS st)) w = Finished"
    proof (rule AF_DFS_cases[where st = st])
      assume c: "AF_DFS_call_1_conds st"
      have "st_lookup (af_state (AF_DFS_upd1 st)) w = Finished" using af_finished_mono_upd1[OF inv c Fin] .
      thus ?thesis using IH(2)[OF c] AF_inv_holds_1[OF mi0 c inv] c
        by (auto simp: AF_DFS_simps[OF IH(1)])
    next
      assume c: "AF_DFS_call_2_conds st"
      have "st_lookup (af_state (AF_DFS_upd2 st)) w = Finished" using af_finished_mono_upd2[OF inv c Fin] .
      thus ?thesis using IH(3)[OF c] AF_inv_holds_2[OF mi0 c inv] c
        by (auto simp: AF_DFS_simps[OF IH(1)])
    next
      assume c: "AF_DFS_call_3_conds st"
      have "st_lookup (af_state (AF_DFS_upd3 st)) w = Finished" using af_finished_mono_upd3[OF inv c Fin] .
      thus ?thesis using IH(4)[OF c] AF_inv_holds_3[OF c inv] c
        by (auto simp: AF_DFS_simps[OF IH(1)])
    next
      assume c: "AF_DFS_ret_conds st"
      thus ?thesis using Fin by (simp add: AF_DFS_simps[OF IH(1)] AF_DFS_ret_def)
    qed
  qed
qed

text \<open>Second building block: \emph{vertex coverage}. The DFS root stays at the bottom of the stack
      (@{const af_handle} and the pop keep @{term \<open>last (af_vstack st)\<close>} fixed, since the back-edge
      truncation drops at most @{term \<open>length (af_estack st)\<close>} vertices, one fewer than the stack), so
      when the DFS returns without flagging unboundedness (empty stack) the root has been finished. An
      outer-loop invariant then propagates this: every vertex the vertex iterator has already passed is
      finished. At outer termination the iterator is exhausted, so --- assuming it enumerates all of
      @{term \<V>} --- every vertex is finished.\<close>

lemma af_handle_vstack_last:
  assumes A2: "AF_invar_2 st" and ne: "af_vstack st \<noteq> []" and la: "last (af_vstack st) = v"
  shows "af_vstack (af_handle st a dir) \<noteq> [] \<and> last (af_vstack (af_handle st a dir)) = v"
proof -
  obtain up dn where updn: "af_rooms (af_flow st) a = (up, dn)" by (cases "af_rooms (af_flow st) a") auto
  show ?thesis
  proof (cases "fst_exec a = snd_exec a")
    case True
    have "af_handle st a dir = af_selfloop_handle st a" using True by (simp add: af_handle_def)
    thus ?thesis using ne la by simp
  next
    case selfloop: False
    show ?thesis
    proof (cases "0 < dn \<and> (up = - 1 \<or> 0 < up)")
      case False thus ?thesis using updn selfloop ne la by (simp add: af_handle_def Let_def)
    next
      case guard: True
      show ?thesis
      proof (cases "af_estack st \<noteq> [] \<and> a = hd (af_estack st)")
        case True thus ?thesis using updn guard selfloop ne la by (simp add: af_handle_def Let_def)
      next
        case parent: False
        show ?thesis
        proof (cases "st_lookup (af_state st) (if dir then snd_exec a else fst_exec a)")
          case Unseen
          have "af_vstack (af_handle st a dir) = (if dir then snd_exec a else fst_exec a) # af_vstack st"
            using updn guard selfloop parent Unseen by (auto simp: af_handle_def Let_def)
          thus ?thesis using ne la by simp
        next
          case OnStack
          obtain fl m' ubd where c: "af_cancel_seg up dn (if dir then snd_exec a else fst_exec a)
              (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) = (fl, m', ubd)"
            by (metis prod_cases3)
          have mle: "m' \<le> length (af_estack st)" using af_cancel_seg_drop_bound[OF c] .
          have "length (af_estack st) < length (af_vstack st)" using A2 ne by (auto simp: AF_invar_2_def)
          hence mlt: "m' < length (af_vstack st)" using mle by simp
          show ?thesis
          proof (cases ubd)
            case True thus ?thesis using updn guard selfloop parent OnStack c ne la by (auto simp: af_handle_def Let_def)
          next
            case False
            have red: "af_vstack (af_handle st a dir) = drop m' (af_vstack st)"
              using updn guard selfloop parent OnStack c False by (auto simp: af_handle_def Let_def)
            have "drop m' (af_vstack st) \<noteq> []" using mlt by (auto simp: drop_eq_Nil)
            moreover have "last (drop m' (af_vstack st)) = v" using mlt la by (simp add: last_drop)
            ultimately show ?thesis using red by simp
          qed
        next
          case Finished
          thus ?thesis using updn guard selfloop parent ne la by (simp add: af_handle_def Let_def)
        qed
      qed
    qed
  qed
qed

definition "af_root_ok v st \<longleftrightarrow>
  (af_vstack st \<noteq> [] \<and> last (af_vstack st) = v) \<or> st_lookup (af_state st) v = Finished"

lemma af_handle_root_ok:
  assumes A1: "AF_invar_1 st" and A2: "AF_invar_2 st" and ae: "a \<in> \<E>" and AV: "AF_invar_V st" and R: "af_root_ok v st"
  shows "af_root_ok v (af_handle st a dir)"
proof (cases "st_lookup (af_state st) v = Finished")
  case True
  hence "st_lookup (af_state (af_handle st a dir)) v = Finished" by (rule af_handle_finished_mono[OF A1 A2 ae AV])
  thus ?thesis by (simp add: af_root_ok_def)
next
  case False
  hence "af_vstack st \<noteq> [] \<and> last (af_vstack st) = v" using R by (simp add: af_root_ok_def)
  hence "af_vstack (af_handle st a dir) \<noteq> [] \<and> last (af_vstack (af_handle st a dir)) = v"
    using af_handle_vstack_last[OF A2] by auto
  thus ?thesis by (simp add: af_root_ok_def)
qed

lemma af_root_ok_upd1:
  assumes inv: "AF_inv st" and conds: "AF_DFS_call_1_conds st" and R: "af_root_ok v st"
  shows "af_root_ok v (AF_DFS_upd1 st)"
proof -
  from inv have i1: "AF_invar_1 st" and i2: "AF_invar_2 st" and iit: "AF_invar_iter st"
    and iV: "AF_invar_V st" by (auto simp: AF_inv_def)
  from conds have ne: "af_vstack st \<noteq> []" and he: "out_has (af_out_arr st) (hd (af_vstack st))"
    by (auto elim!: call_cond_elims)
  have mi': "multigraph_inv (af_out_arr st) (af_in_arr st)" using iit by (simp add: AF_invar_iter_def)
  have vV: "hd (af_vstack st) \<in> \<V>" using iV ne hd_in_set by (auto simp: AF_invar_V_def)
  have ae: "out_current (af_out_arr st) (hd (af_vstack st)) \<in> \<E>"
    using af_current_out_endpoint[OF mi' vV he] by simp
  let ?st' = "st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack st))\<rparr>"
  have "af_root_ok v (af_handle ?st'
          (out_current (af_out_arr st) (hd (af_vstack st))) True)"
    by (rule af_handle_root_ok[OF AF_invar_1_out_advance[OF vV i1]])
       (use i2 ae iV R in \<open>simp_all add: AF_invar_2_def af_root_ok_def AF_invar_V_def\<close>)
  thus ?thesis by (simp add: AF_DFS_upd1_def Let_def)
qed

lemma af_root_ok_upd2:
  assumes inv: "AF_inv st" and conds: "AF_DFS_call_2_conds st" and R: "af_root_ok v st"
  shows "af_root_ok v (AF_DFS_upd2 st)"
proof -
  from inv have i1: "AF_invar_1 st" and i2: "AF_invar_2 st" and iit: "AF_invar_iter st"
    and iV: "AF_invar_V st" by (auto simp: AF_inv_def)
  from conds have ne: "af_vstack st \<noteq> []" and he: "in_has (af_in_arr st) (hd (af_vstack st))"
    by (auto elim!: call_cond_elims)
  have mi': "multigraph_inv (af_out_arr st) (af_in_arr st)" using iit by (simp add: AF_invar_iter_def)
  have vV: "hd (af_vstack st) \<in> \<V>" using iV ne hd_in_set by (auto simp: AF_invar_V_def)
  have ae: "in_current (af_in_arr st) (hd (af_vstack st)) \<in> \<E>"
    using af_current_in_endpoint[OF mi' vV he] by simp
  let ?st' = "st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack st))\<rparr>"
  have "af_root_ok v (af_handle ?st'
          (in_current (af_in_arr st) (hd (af_vstack st))) False)"
    by (rule af_handle_root_ok[OF AF_invar_1_in_advance[OF vV i1]])
       (use i2 ae iV R in \<open>simp_all add: AF_invar_2_def af_root_ok_def AF_invar_V_def\<close>)
  thus ?thesis by (simp add: AF_DFS_upd2_def Let_def)
qed

lemma af_root_ok_upd3:
  assumes inv: "AF_inv st" and conds: "AF_DFS_call_3_conds st" and R: "af_root_ok v st"
  shows "af_root_ok v (AF_DFS_upd3 st)"
proof -
  from inv have i1: "AF_invar_1 st" and iV: "AF_invar_V st" by (auto simp: AF_inv_def)
  have si: "st_invar (af_state st)" using i1 by (simp add: AF_invar_1_def)
  from conds obtain u us where vv: "af_vstack st = u # us" by (auto elim!: call_cond_elims)
  have uV: "u \<in> \<V>" using iV vv by (auto simp: AF_invar_V_def)
  show ?thesis
  proof (cases "st_lookup (af_state st) v = Finished")
    case True
    hence "st_lookup (af_state (AF_DFS_upd3 st)) v = Finished"
      using si vv by (simp add: AF_DFS_upd3_def vv state_arr.fixed_univ_map_upd[OF si uV])
    thus ?thesis by (simp add: af_root_ok_def)
  next
    case notfin: False
    hence L: "af_vstack st \<noteq> [] \<and> last (af_vstack st) = v" using R by (simp add: af_root_ok_def)
    show ?thesis
    proof (cases "tl (af_vstack st) = []")
      case True
      hence hv: "hd (af_vstack st) = v" using L by (metis hd_Cons_tl last_ConsL)
      have "st_lookup (af_state (AF_DFS_upd3 st)) (hd (af_vstack st)) = Finished"
        using vv by (simp add: AF_DFS_upd3_def state_arr.fixed_univ_map_upd[OF si uV])
      hence "st_lookup (af_state (AF_DFS_upd3 st)) v = Finished" using hv by simp
      thus ?thesis by (simp add: af_root_ok_def)
    next
      case False
      have "last (tl (af_vstack st)) = v" using L False by (metis hd_Cons_tl last_ConsR)
      thus ?thesis using False by (simp add: af_root_ok_def AF_DFS_upd3_def)
    qed
  qed
qed

lemma AF_DFS_root_ok:
  assumes dom: "AF_DFS_dom st" and mi0: "multigraph_inv out_arr in_arr"
  shows "AF_inv st \<longrightarrow> af_root_ok v st \<longrightarrow> af_root_ok v (AF_DFS st)"
proof (induction rule: AF_DFS_induct[OF dom])
  case IH: (1 st)
  show ?case
  proof (intro impI)
    assume inv: "AF_inv st" and R: "af_root_ok v st"
    from inv have i1: "AF_invar_1 st" and i2: "AF_invar_2 st" by (auto simp: AF_inv_def)
    show "af_root_ok v (AF_DFS st)"
    proof (rule AF_DFS_cases[where st = st])
      assume c: "AF_DFS_call_1_conds st"
      have "af_root_ok v (AF_DFS_upd1 st)" using af_root_ok_upd1[OF inv c R] .
      thus ?thesis using IH(2)[OF c] AF_inv_holds_1[OF mi0 c inv] c by (auto simp: AF_DFS_simps[OF IH(1)])
    next
      assume c: "AF_DFS_call_2_conds st"
      have "af_root_ok v (AF_DFS_upd2 st)" using af_root_ok_upd2[OF inv c R] .
      thus ?thesis using IH(3)[OF c] AF_inv_holds_2[OF mi0 c inv] c by (auto simp: AF_DFS_simps[OF IH(1)])
    next
      assume c: "AF_DFS_call_3_conds st"
      have "af_root_ok v (AF_DFS_upd3 st)" using af_root_ok_upd3[OF inv c R] .
      thus ?thesis using IH(4)[OF c] AF_inv_holds_3[OF c inv] c by (auto simp: AF_DFS_simps[OF IH(1)])
    next
      assume c: "AF_DFS_ret_conds st"
      thus ?thesis using R by (simp add: AF_DFS_simps[OF IH(1)] AF_DFS_ret_def)
    qed
  qed
qed

lemma AF_DFS_root_finished:
  assumes dom: "AF_DFS_dom st" and mi0: "multigraph_inv out_arr in_arr"
    and inv: "AF_inv st" and R: "af_root_ok v st" and nu: "\<not> af_unbounded (AF_DFS st)"
  shows "st_lookup (af_state (AF_DFS st)) v = Finished"
proof -
  have "af_root_ok v (AF_DFS st)" using AF_DFS_root_ok[OF dom mi0] inv R by simp
  moreover have "af_vstack (AF_DFS st) = []" using AF_DFS_ret_vstack[OF dom] nu by simp
  ultimately show ?thesis by (simp add: af_root_ok_def)
qed

definition "AFF_cov st \<longleftrightarrow>
  (\<not> aff_unbounded st \<longrightarrow> (\<forall>v \<in> vit_iterated (aff_vit st). st_lookup (aff_state st) v = Finished))"

lemma AFF_cov_holds_1:
  assumes conds: "AF_outer_call_1_conds st" and inv: "AFF_inv st" and cov: "AFF_cov st"
  shows "AFF_cov (AF_outer_upd1 st)"
proof (unfold AFF_cov_def, intro impI ballI)
  fix w assume w: "w \<in> vit_iterated (aff_vit (AF_outer_upd1 st))"
  have iv: "vit_invar (aff_vit st)" using inv by (simp add: AFF_inv_def)
  have hv: "has_vertex (aff_vit st)" and uns: "st_lookup (aff_state st) (current_vertex (aff_vit st)) \<noteq> Unseen"
       and nu0: "\<not> aff_unbounded st"
    using conds by (auto simp: AF_outer_call_1_conds_def)
  have ne: "vit_remaining (aff_vit st) \<noteq> {}" using hv iv vertex_iterator.has_current by auto
  have "vit_iterated (aff_vit (AF_outer_upd1 st)) = vit_iterated (aff_vit st) \<union> {current_vertex (aff_vit st)}"
    using vertex_iterator.move_on(3)[OF iv ne] by (simp add: AF_outer_upd1_def)
  hence "w \<in> vit_iterated (aff_vit st) \<or> w = current_vertex (aff_vit st)" using w by auto
  thus "st_lookup (aff_state (AF_outer_upd1 st)) w = Finished"
  proof
    assume "w \<in> vit_iterated (aff_vit st)"
    thus ?thesis using cov nu0 by (auto simp: AFF_cov_def AF_outer_upd1_def)
  next
    assume wc: "w = current_vertex (aff_vit st)"
    have "st_lookup (aff_state st) (current_vertex (aff_vit st)) = Finished"
    proof (cases "st_lookup (aff_state st) (current_vertex (aff_vit st))")
      case Unseen thus ?thesis using uns by simp
    next
      case OnStack thus ?thesis using inv nu0 vit_current_V[OF inv hv] by (auto simp: AFF_inv_def)
    next
      case Finished thus ?thesis by simp
    qed
    thus ?thesis using wc by (simp add: AF_outer_upd1_def)
  qed
qed

lemma AFF_cov_holds_2:
  assumes mi0: "multigraph_inv out_arr in_arr"
    and conds: "AF_outer_call_2_conds st" and inv: "AFF_inv st" and cov: "AFF_cov st"
  shows "AFF_cov (AF_outer_upd2 st)"
proof (unfold AFF_cov_def, intro impI ballI)
  fix w assume nu: "\<not> aff_unbounded (AF_outer_upd2 st)"
    and w: "w \<in> vit_iterated (aff_vit (AF_outer_upd2 st))"
  from inv have ff: "flow_invar (aff_flow st)" and sti: "st_invar (aff_state st)"
    and aoi: "out_invar (aff_out_arr st)" and aii: "in_invar (aff_in_arr st)"
    and mii: "multigraph_inv (aff_out_arr st) (aff_in_arr st)" and feas: "af_cap_feasible (aff_flow st)"
    and noos: "\<not> aff_unbounded st \<longrightarrow> (\<forall>w\<in>\<V>. st_lookup (aff_state st) w \<noteq> OnStack)"
    and iv: "vit_invar (aff_vit st)" by (auto simp: AFF_inv_def)
  from conds have nu0: "\<not> aff_unbounded st" and hv: "has_vertex (aff_vit st)"
    and vuns: "st_lookup (aff_state st) (current_vertex (aff_vit st)) = Unseen"
    by (auto simp: AF_outer_call_2_conds_def)
  let ?v = "current_vertex (aff_vit st)"
  have vV: "?v \<in> \<V>" using vit_current_V[OF inv hv] .
  have noos': "\<forall>w\<in>\<V>. st_lookup (aff_state st) w \<noteq> OnStack" using noos nu0 by simp
  let ?init = "AF_DFS_initial (aff_flow st) (aff_out_arr st) (aff_in_arr st) (aff_state st) ?v"
  have invi: "AF_inv ?init" using AF_inv_initial[OF ff sti aoi aii mii vV feas noos'] .
  have domi: "AF_DFS_dom ?init" using AF_DFS_dom[OF mi0 invi] .
  have nures: "\<not> af_unbounded (AF_DFS ?init)" using nu by (simp add: AF_outer_upd2_def Let_def)
  have ne: "vit_remaining (aff_vit st) \<noteq> {}" using hv iv vertex_iterator.has_current by auto
  have iter_eq: "vit_iterated (aff_vit (AF_outer_upd2 st)) = vit_iterated (aff_vit st) \<union> {?v}"
    using vertex_iterator.move_on(3)[OF iv ne] by (simp add: AF_outer_upd2_def Let_def)
  have state_res: "aff_state (AF_outer_upd2 st) = af_state (AF_DFS ?init)" by (simp add: AF_outer_upd2_def Let_def)
  from w iter_eq have "w \<in> vit_iterated (aff_vit st) \<or> w = ?v" by auto
  thus "st_lookup (aff_state (AF_outer_upd2 st)) w = Finished"
  proof
    assume wc: "w = ?v"
    have rok: "af_root_ok ?v ?init" by (simp add: af_root_ok_def AF_DFS_initial_def)
    have "st_lookup (af_state (AF_DFS ?init)) ?v = Finished"
      using AF_DFS_root_finished[OF domi mi0 invi rok nures] .
    thus ?thesis using state_res wc by simp
  next
    assume wi: "w \<in> vit_iterated (aff_vit st)"
    have wfin: "st_lookup (aff_state st) w = Finished" using cov nu0 wi by (auto simp: AFF_cov_def)
    have wne: "w \<noteq> ?v" using wfin vuns by auto
    have p: "st_lookup (af_state ?init) w = Finished"
      using wfin wne sti by (simp add: AF_DFS_initial_def state_arr.fixed_univ_map_upd[OF sti vV])
    have "st_lookup (af_state (AF_DFS ?init)) w = Finished"
      using AF_DFS_finished_mono[OF domi mi0, of w] invi p by blast
    thus ?thesis using state_res by simp
  qed
qed

lemma AF_outer_inv_cov:
  assumes dom: "AF_outer_dom st" and mi0: "multigraph_inv out_arr in_arr"
  shows "AFF_inv st \<and> AFF_cov st \<longrightarrow> AFF_inv (AF_outer st) \<and> AFF_cov (AF_outer st)"
proof (induction rule: AF_outer_induct[OF dom])
  case IH: (1 st)
  show ?case
  proof
    assume ic: "AFF_inv st \<and> AFF_cov st"
    hence inv: "AFF_inv st" and cov: "AFF_cov st" by auto
    show "AFF_inv (AF_outer st) \<and> AFF_cov (AF_outer st)"
    proof (rule AF_outer_cases[where st = st])
      assume c: "AF_outer_call_1_conds st"
      have step: "AFF_inv (AF_outer_upd1 st) \<and> AFF_cov (AF_outer_upd1 st)"
        using AFF_inv_holds_1[OF c inv] AFF_cov_holds_1[OF c inv cov] by simp
      have "AFF_inv (AF_outer (AF_outer_upd1 st)) \<and> AFF_cov (AF_outer (AF_outer_upd1 st))"
        using IH(2)[OF c] step by blast
      thus ?thesis using c by (simp add: AF_outer_simps[OF IH(1)])
    next
      assume c: "AF_outer_call_2_conds st"
      have step: "AFF_inv (AF_outer_upd2 st) \<and> AFF_cov (AF_outer_upd2 st)"
        using AFF_inv_holds_2[OF mi0 c inv] AFF_cov_holds_2[OF mi0 c inv cov] by simp
      have "AFF_inv (AF_outer (AF_outer_upd2 st)) \<and> AFF_cov (AF_outer (AF_outer_upd2 st))"
        using IH(3)[OF c] step by blast
      thus ?thesis using c by (simp add: AF_outer_simps[OF IH(1)])
    next
      assume c: "AF_outer_ret_conds st"
      thus ?thesis using ic by (simp add: AF_outer_simps[OF IH(1)] AF_outer_ret_def)
    qed
  qed
qed

lemma AF_outer_ret_reached:
  assumes dom: "AF_outer_dom st"
  shows "\<not> aff_unbounded (AF_outer st) \<longrightarrow> \<not> has_vertex (aff_vit (AF_outer st))"
proof (induction rule: AF_outer_induct[OF dom])
  case IH: (1 st)
  show ?case
    apply (rule AF_outer_cases[where st = st])
    subgoal using IH(2) by (simp add: AF_outer_simps[OF IH(1)])
    subgoal using IH(3) by (simp add: AF_outer_simps[OF IH(1)])
    subgoal by (auto simp: AF_outer_simps[OF IH(1)] AF_outer_ret_def AF_outer_ret_conds_def elim!: call_cond_elims)
    done
qed

lemma AF_outer_abstract:
  assumes dom: "AF_outer_dom st" and mi0: "multigraph_inv out_arr in_arr"
  shows "AFF_inv st \<longrightarrow> vit_abstract (aff_vit (AF_outer st)) = vit_abstract (aff_vit st)"
proof (induction rule: AF_outer_induct[OF dom])
  case IH: (1 st)
  show ?case
  proof
    assume inv: "AFF_inv st"
    have iv: "vit_invar (aff_vit st)" using inv by (simp add: AFF_inv_def)
    show "vit_abstract (aff_vit (AF_outer st)) = vit_abstract (aff_vit st)"
    proof (rule AF_outer_cases[where st = st])
      assume c: "AF_outer_call_1_conds st"
      have hv: "has_vertex (aff_vit st)" using c by (auto simp: AF_outer_call_1_conds_def)
      have ne: "vit_remaining (aff_vit st) \<noteq> {}" using hv iv vertex_iterator.has_current by auto
      have ab: "vit_abstract (aff_vit (AF_outer_upd1 st)) = vit_abstract (aff_vit st)"
        using vertex_iterator.move_on(1)[OF iv ne] by (simp add: AF_outer_upd1_def)
      have "vit_abstract (aff_vit (AF_outer (AF_outer_upd1 st))) = vit_abstract (aff_vit (AF_outer_upd1 st))"
        using IH(2)[OF c] AFF_inv_holds_1[OF c inv] by blast
      thus ?thesis using ab c by (simp add: AF_outer_simps[OF IH(1)])
    next
      assume c: "AF_outer_call_2_conds st"
      have hv: "has_vertex (aff_vit st)" using c by (auto simp: AF_outer_call_2_conds_def)
      have ne: "vit_remaining (aff_vit st) \<noteq> {}" using hv iv vertex_iterator.has_current by auto
      have ab: "vit_abstract (aff_vit (AF_outer_upd2 st)) = vit_abstract (aff_vit st)"
        using vertex_iterator.move_on(1)[OF iv ne] by (simp add: AF_outer_upd2_def Let_def)
      have "vit_abstract (aff_vit (AF_outer (AF_outer_upd2 st))) = vit_abstract (aff_vit (AF_outer_upd2 st))"
        using IH(3)[OF c] AFF_inv_holds_2[OF mi0 c inv] by blast
      thus ?thesis using ab c by (simp add: AF_outer_simps[OF IH(1)])
    next
      assume c: "AF_outer_ret_conds st"
      thus ?thesis by (simp add: AF_outer_simps[OF IH(1)] AF_outer_ret_def)
    qed
  qed
qed

lemma AF_outer_cov_terminal:
  assumes dom: "AF_outer_dom st" and mi0: "multigraph_inv out_arr in_arr"
    and inv: "AFF_inv st" and cov: "AFF_cov st" and nu: "\<not> aff_unbounded (AF_outer st)"
  shows "\<forall>v \<in> vit_abstract (aff_vit (AF_outer st)). st_lookup (aff_state (AF_outer st)) v = Finished"
proof -
  have ic: "AFF_inv (AF_outer st) \<and> AFF_cov (AF_outer st)"
    using AF_outer_inv_cov[OF dom mi0] inv cov by blast
  have iv': "vit_invar (aff_vit (AF_outer st))" using ic by (simp add: AFF_inv_def)
  have "\<not> has_vertex (aff_vit (AF_outer st))" using AF_outer_ret_reached[OF dom] nu by simp
  hence "vit_remaining (aff_vit (AF_outer st)) = {}" using iv' vertex_iterator.has_current by auto
  hence "vit_iterated (aff_vit (AF_outer st)) = vit_abstract (aff_vit (AF_outer st))"
    using vertex_iterator.iterable_set_abstract(2)[OF iv'] by auto
  moreover have "\<forall>v \<in> vit_iterated (aff_vit (AF_outer st)). st_lookup (aff_state (AF_outer st)) v = Finished"
    using ic nu by (simp add: AFF_cov_def)
  ultimately show ?thesis by simp
qed


text \<open>The acyclifier returns a well-formed flow array: @{const AFF_inv} carries @{term flow_invar}
      through the whole outer loop, so it holds of the returned @{term \<open>aff_flow\<close>}.  With a
      length-pinned @{term flow_invar} at the list instantiation this is exactly length preservation,
      which is what the augmented-array glue downstream needs.\<close>

lemma make_acyclic_flow_invar:
  assumes mi0: "multigraph_inv out_arr in_arr"
    and ff: "flow_invar f0" and feas: "af_cap_feasible f0"
    and vv: "vit_invar all_vertices" and vab: "vit_abstract all_vertices \<subseteq> \<V>"
    and vit0: "vit_iterated all_vertices = {}"
    and res: "make_acyclic f0 = Some f'"
  shows "flow_invar f'"
proof -
  have inv0: "AFF_inv (AF_outer_initial f0)" using AFF_inv_initial[OF mi0 ff feas vv vab] .
  have cov0: "AFF_cov (AF_outer_initial f0)" using vit0 by (simp add: AFF_cov_def AF_outer_initial_def)
  have dom: "AF_outer_dom (AF_outer_initial f0)" using AF_outer_dom[OF mi0 inv0] .
  have ic: "AFF_inv (AF_outer (AF_outer_initial f0))"
    using AF_outer_inv_cov[OF dom mi0] inv0 cov0 by blast
  have ff': "f' = aff_flow (AF_outer (AF_outer_initial f0))"
    using res by (auto simp: make_acyclic_def Let_def split: if_splits)
  show ?thesis using ic by (simp add: ff' AFF_inv_def)
qed

lemma make_acyclic_all_finished:
  assumes mi0: "multigraph_inv out_arr in_arr"
    and ff: "flow_invar f0" and feas: "af_cap_feasible f0"
    and vv: "vit_invar all_vertices" and vabsV: "vit_abstract all_vertices = \<V>"
    and vit0: "vit_iterated all_vertices = {}"
    and res: "make_acyclic f0 = Some f'"
  shows "\<forall>v \<in> \<V>. st_lookup (aff_state (AF_outer (AF_outer_initial f0))) v = Finished"
proof -
  have vab: "vit_abstract all_vertices \<subseteq> \<V>" using vabsV by simp
  have inv0: "AFF_inv (AF_outer_initial f0)" using AFF_inv_initial[OF mi0 ff feas vv vab] .
  have cov0: "AFF_cov (AF_outer_initial f0)" using vit0 by (simp add: AFF_cov_def AF_outer_initial_def)
  have dom: "AF_outer_dom (AF_outer_initial f0)" using AF_outer_dom[OF mi0 inv0] .
  have nu: "\<not> aff_unbounded (AF_outer (AF_outer_initial f0))"
    using res by (auto simp: make_acyclic_def Let_def split: if_splits)
  have "\<forall>v \<in> vit_abstract (aff_vit (AF_outer (AF_outer_initial f0))).
          st_lookup (aff_state (AF_outer (AF_outer_initial f0))) v = Finished"
    using AF_outer_cov_terminal[OF dom mi0 inv0 cov0 nu] .
  moreover have "vit_abstract (aff_vit (AF_outer (AF_outer_initial f0))) = \<V>"
    using AF_outer_abstract[OF dom mi0] inv0 vabsV by (simp add: AF_outer_initial_def)
  ultimately show ?thesis by simp
qed

text \<open>Third building block: \emph{edge exhaustion}. A finished vertex has consumed both its edge
      iterators (their remaining-edge sets are empty), because a vertex is finished exactly at the pop, whose
      guard @{const AF_DFS_call_3_conds} says both iterators have no current edge; and thereafter its
      array entries are frozen --- the per-step advance only touches the top vertex and the back-edge
      reset only touches dropped (on-stack) vertices, never a finished one. So at termination every
      vertex --- being finished (coverage) --- has scanned \emph{all} its incident edges.\<close>

lemma af_reset_unsee_seg_out_lookup:
  assumes "out_invar (af_out_arr st)" and "w \<notin> set (take n vs)" and "set vs \<subseteq> \<V>"
  shows "out_remaining (af_out_arr (af_reset_unsee_seg n vs st)) w = out_remaining (af_out_arr st) w
       \<and> out_iterated (af_out_arr (af_reset_unsee_seg n vs st)) w = out_iterated (af_out_arr st) w"
  using assms
proof (induction n vs st rule: af_reset_unsee_seg.induct)
  case (1 n v vs st)
  let ?st1 = "af_reset v (st\<lparr>af_state := st_upd (af_state st) v Unseen\<rparr>)"
  have vw: "w \<noteq> v" and wn: "w \<notin> set (take n vs)" using 1(3) by auto
  have vV: "v \<in> \<V>" and vsV: "set vs \<subseteq> \<V>" using 1(4) by auto
  have ai1: "out_invar (af_out_arr ?st1)" using 1(2) vV by (simp add: af_reset_def out_reset_invar)
  have look: "out_remaining (af_out_arr ?st1) w = out_remaining (af_out_arr st) w
            \<and> out_iterated (af_out_arr ?st1) w = out_iterated (af_out_arr st) w"
    using vw vV by (simp add: af_reset_def outg.idx_reset_remaining_other[OF 1(2)]
                                        outg.idx_reset_iterated_other[OF 1(2)])
  show ?case using 1(1)[OF ai1 wn vsV] look by simp
qed simp_all

lemma af_reset_unsee_seg_in_lookup:
  assumes "in_invar (af_in_arr st)" and "w \<notin> set (take n vs)" and "set vs \<subseteq> \<V>"
  shows "in_remaining (af_in_arr (af_reset_unsee_seg n vs st)) w = in_remaining (af_in_arr st) w
       \<and> in_iterated (af_in_arr (af_reset_unsee_seg n vs st)) w = in_iterated (af_in_arr st) w"
  using assms
proof (induction n vs st rule: af_reset_unsee_seg.induct)
  case (1 n v vs st)
  let ?st1 = "af_reset v (st\<lparr>af_state := st_upd (af_state st) v Unseen\<rparr>)"
  have vw: "w \<noteq> v" and wn: "w \<notin> set (take n vs)" using 1(3) by auto
  have vV: "v \<in> \<V>" and vsV: "set vs \<subseteq> \<V>" using 1(4) by auto
  have ai1: "in_invar (af_in_arr ?st1)" using 1(2) vV by (simp add: af_reset_def in_reset_invar)
  have look: "in_remaining (af_in_arr ?st1) w = in_remaining (af_in_arr st) w
            \<and> in_iterated (af_in_arr ?st1) w = in_iterated (af_in_arr st) w"
    using vw vV by (simp add: af_reset_def ing.idx_reset_remaining_other[OF 1(2)]
                                        ing.idx_reset_iterated_other[OF 1(2)])
  show ?case using 1(1)[OF ai1 wn vsV] look by simp
qed simp_all

definition "AF_invar_exh st \<longleftrightarrow>
  (\<forall>v\<in>\<V>. st_lookup (af_state st) v = Finished \<longrightarrow>
        out_remaining (af_out_arr st) v = {} \<and>
        in_remaining (af_in_arr st) v = {})"

lemma af_handle_arr_off:
  assumes A1: "AF_invar_1 st" and A2: "AF_invar_2 st" and AV: "AF_invar_V st" and F: "st_lookup (af_state st) v = Finished"
  shows "out_remaining (af_out_arr (af_handle st a dir)) v = out_remaining (af_out_arr st) v
       \<and> out_iterated (af_out_arr (af_handle st a dir)) v = out_iterated (af_out_arr st) v
       \<and> in_remaining (af_in_arr (af_handle st a dir)) v = in_remaining (af_in_arr st) v
       \<and> in_iterated (af_in_arr (af_handle st a dir)) v = in_iterated (af_in_arr st) v"
proof -
  have aio: "out_invar (af_out_arr st)" and aii: "in_invar (af_in_arr st)" using A1 by (auto simp: AF_invar_1_def)
  have wnv: "v \<notin> set (af_vstack st)"
  proof
    assume vin: "v \<in> set (af_vstack st)"
    hence vV: "v \<in> \<V>" using AV by (auto simp: AF_invar_V_def)
    from vin vV have "st_lookup (af_state st) v = OnStack" using A2 by (auto simp: AF_invar_2_def)
    with F show False by simp
  qed
  have vsV: "set (af_vstack st) \<subseteq> \<V>" using AV by (simp add: AF_invar_V_def)
  obtain up dn where updn: "af_rooms (af_flow st) a = (up, dn)" by (cases "af_rooms (af_flow st) a") auto
  show ?thesis
  proof (cases "fst_exec a = snd_exec a")
    case True
    have "af_handle st a dir = af_selfloop_handle st a" using True by (simp add: af_handle_def)
    thus ?thesis by simp
  next
    case selfloop: False
    show ?thesis
    proof (cases "0 < dn \<and> (up = - 1 \<or> 0 < up)")
      case False thus ?thesis using updn selfloop by (simp add: af_handle_def Let_def)
    next
      case guard: True
      show ?thesis
      proof (cases "af_estack st \<noteq> [] \<and> a = hd (af_estack st)")
        case True thus ?thesis using updn guard selfloop by (simp add: af_handle_def Let_def)
      next
        case parent: False
        show ?thesis
        proof (cases "st_lookup (af_state st) (if dir then snd_exec a else fst_exec a)")
          case Unseen
          thus ?thesis using updn guard selfloop parent by (auto simp: af_handle_def Let_def)
        next
          case OnStack
          obtain fl m' ubd where c: "af_cancel_seg up dn (if dir then snd_exec a else fst_exec a)
              (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) = (fl, m', ubd)"
            by (metis prod_cases3)
          show ?thesis
          proof (cases ubd)
            case True thus ?thesis using updn guard selfloop parent OnStack c by (auto simp: af_handle_def Let_def)
          next
            case False
            let ?dst = "st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st),
                    af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>"
            have red: "af_handle st a dir = af_reset_unsee_seg m' (af_vstack st) ?dst"
              using updn guard selfloop parent OnStack c False by (auto simp: af_handle_def Let_def)
            have wnv': "v \<notin> set (take m' (af_vstack st))" using wnv by (meson in_set_takeD)
            have o: "out_remaining (af_out_arr (af_reset_unsee_seg m' (af_vstack st) ?dst)) v = out_remaining (af_out_arr st) v
                   \<and> out_iterated (af_out_arr (af_reset_unsee_seg m' (af_vstack st) ?dst)) v = out_iterated (af_out_arr st) v"
              using af_reset_unsee_seg_out_lookup[of ?dst v m' "af_vstack st"] aio wnv' vsV by simp
            have i: "in_remaining (af_in_arr (af_reset_unsee_seg m' (af_vstack st) ?dst)) v = in_remaining (af_in_arr st) v
                   \<and> in_iterated (af_in_arr (af_reset_unsee_seg m' (af_vstack st) ?dst)) v = in_iterated (af_in_arr st) v"
              using af_reset_unsee_seg_in_lookup[of ?dst v m' "af_vstack st"] aii wnv' vsV by simp
            show ?thesis using red o i by simp
          qed
        next
          case Finished
          thus ?thesis using updn guard selfloop parent by (auto simp: af_handle_def Let_def)
        qed
      qed
    qed
  qed
qed

lemma af_handle_finished_back:
  assumes A1: "AF_invar_1 st" and A2: "AF_invar_2 st" and ae: "a \<in> \<E>" and AV: "AF_invar_V st"
    and F: "st_lookup (af_state (af_handle st a dir)) v = Finished"
  shows "st_lookup (af_state st) v = Finished"
proof -
  have si: "st_invar (af_state st)" using A1 by (simp add: AF_invar_1_def)
  obtain up dn where updn: "af_rooms (af_flow st) a = (up, dn)" by (cases "af_rooms (af_flow st) a") auto
  show ?thesis
  proof (cases "fst_exec a = snd_exec a")
    case True
    have "af_handle st a dir = af_selfloop_handle st a" using True by (simp add: af_handle_def)
    thus ?thesis using F by simp
  next
    case selfloop: False
    show ?thesis
    proof (cases "0 < dn \<and> (up = - 1 \<or> 0 < up)")
      case False
      have "af_handle st a dir = st" using updn selfloop False by (auto simp: af_handle_def Let_def)
      thus ?thesis using F by simp
    next
      case guard: True
      show ?thesis
      proof (cases "af_estack st \<noteq> [] \<and> a = hd (af_estack st)")
        case True
        have "af_handle st a dir = st" using updn selfloop True by (auto simp: af_handle_def Let_def)
        thus ?thesis using F by simp
      next
        case parent: False
        show ?thesis
        proof (cases "st_lookup (af_state st) (if dir then snd_exec a else fst_exec a)")
          case Unseen
          have cV: "(if dir then snd_exec a else fst_exec a) \<in> \<V>"
            using ae fst_E_V[OF ae] snd_E_V[OF ae] by (cases dir) (auto simp: snd_exec_eq[OF ae] fst_exec_eq[OF ae])
          have h: "af_handle st a dir = st\<lparr>af_vstack := (if dir then snd_exec a else fst_exec a) # af_vstack st,
                     af_state := st_upd (af_state st) (if dir then snd_exec a else fst_exec a) OnStack,
                     af_estack := a # af_estack st, af_dstack := dir # af_dstack st\<rparr>"
            using updn guard selfloop parent Unseen by (auto simp: af_handle_def Let_def)
          have "st_lookup (af_state (af_handle st a dir)) v =
                  (if v = (if dir then snd_exec a else fst_exec a) then OnStack else st_lookup (af_state st) v)"
            using h si by (simp add: state_arr.fixed_univ_map_upd[OF si cV])
          thus ?thesis using F by (auto split: if_splits)
        next
          case OnStack
          obtain fl m' ubd where c: "af_cancel_seg up dn (if dir then snd_exec a else fst_exec a)
              (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) = (fl, m', ubd)"
            by (cases "af_cancel_seg up dn (if dir then snd_exec a else fst_exec a)
                        (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st)") auto
          show ?thesis
          proof (cases ubd)
            case True thus ?thesis using updn guard selfloop parent OnStack c F by (auto simp: af_handle_def Let_def)
          next
            case False
            let ?dst = "st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st),
                    af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>"
            have red: "af_handle st a dir = af_reset_unsee_seg m' (af_vstack st) ?dst"
              using updn guard selfloop parent OnStack c False by (auto simp: af_handle_def Let_def)
            have sid: "st_invar (af_state ?dst)" using si by simp
            have vsV: "set (af_vstack st) \<subseteq> \<V>" using AV by (simp add: AF_invar_V_def)
            have "st_lookup (af_state (af_handle st a dir)) v =
                    (if v \<in> set (take m' (af_vstack st)) then Unseen else st_lookup (af_state st) v)"
              using red af_reset_unsee_seg_state[OF vsV sid, of m' v] by simp
            thus ?thesis using F by (auto split: if_splits)
          qed
        next
          case Finished
          have "af_handle st a dir = st" using updn selfloop parent Finished by (auto simp: af_handle_def Let_def)
          thus ?thesis using F by simp
        qed
      qed
    qed
  qed
qed

lemma af_handle_exh:
  assumes A1: "AF_invar_1 st" and A2: "AF_invar_2 st" and ae: "a \<in> \<E>" and AV: "AF_invar_V st" and E: "AF_invar_exh st"
  shows "AF_invar_exh (af_handle st a dir)"
proof (unfold AF_invar_exh_def, intro ballI impI)
  fix v assume vV': "v \<in> \<V>" and F: "st_lookup (af_state (af_handle st a dir)) v = Finished"
  have Fst: "st_lookup (af_state st) v = Finished" using af_handle_finished_back[OF A1 A2 ae AV F] .
  have "out_remaining (af_out_arr st) v = {} \<and> in_remaining (af_in_arr st) v = {}"
    using E Fst vV' by (simp add: AF_invar_exh_def)
  moreover have "out_remaining (af_out_arr (af_handle st a dir)) v = out_remaining (af_out_arr st) v
              \<and> in_remaining (af_in_arr (af_handle st a dir)) v = in_remaining (af_in_arr st) v"
    using af_handle_arr_off[OF A1 A2 AV Fst] by simp
  ultimately show "out_remaining (af_out_arr (af_handle st a dir)) v = {}
                 \<and> in_remaining (af_in_arr (af_handle st a dir)) v = {}" by simp
qed

lemma af_exh_upd1:
  assumes A1: "AF_invar_1 st" and A2: "AF_invar_2 st" and iter: "AF_invar_iter st" and iV: "AF_invar_V st"
    and E: "AF_invar_exh st" and c: "AF_DFS_call_1_conds st"
  shows "AF_invar_exh (AF_DFS_upd1 st)"
proof -
  have ne: "af_vstack st \<noteq> []" using c by (auto elim!: call_cond_elims)
  have aio: "out_invar (af_out_arr st)" using A1 by (simp add: AF_invar_1_def)
  have mi': "multigraph_inv (af_out_arr st) (af_in_arr st)" using iter by (simp add: AF_invar_iter_def)
  have vV: "hd (af_vstack st) \<in> \<V>" using iV ne hd_in_set by (auto simp: AF_invar_V_def)
  have hae: "out_has (af_out_arr st) (hd (af_vstack st))" using c by (auto elim!: call_cond_elims)
  have ae: "out_current (af_out_arr st) (hd (af_vstack st)) \<in> \<E>"
    using af_current_out_endpoint[OF mi' vV hae] by simp
  let ?st' = "st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack st))\<rparr>"
  have exh': "AF_invar_exh ?st'"
  proof (unfold AF_invar_exh_def, intro ballI impI)
    fix v assume vV': "v \<in> \<V>" and F: "st_lookup (af_state ?st') v = Finished"
    hence Fv: "st_lookup (af_state st) v = Finished" by simp
    have vnv: "v \<notin> set (af_vstack st)"
    proof
      assume "v \<in> set (af_vstack st)"
      hence "st_lookup (af_state st) v = OnStack" using A2 vV' by (auto simp: AF_invar_2_def)
      with Fv show False by simp
    qed
    hence vh: "v \<noteq> hd (af_vstack st)" using ne by auto
    have he: "out_has (af_out_arr st) (hd (af_vstack st))" using c by (auto elim!: call_cond_elims)
    have nehd: "out_remaining (af_out_arr st) (hd (af_vstack st)) \<noteq> {}" using he by (simp add: outg.idx_has[OF aio vV])
    have "out_remaining (af_out_arr ?st') v = out_remaining (af_out_arr st) v"
      using outg.idx_move_remaining_other[OF aio vV nehd vh] by simp
    thus "out_remaining (af_out_arr ?st') v = {} \<and> in_remaining (af_in_arr ?st') v = {}"
      using E Fv vV' by (simp add: AF_invar_exh_def)
  qed
  have "AF_invar_exh (af_handle ?st' (out_current (af_out_arr st) (hd (af_vstack st))) True)"
    by (rule af_handle_exh[OF AF_invar_1_out_advance[OF vV A1] _ ae _ exh'])
       (use A2 iV in \<open>simp_all add: AF_invar_2_def AF_invar_V_def\<close>)
  thus ?thesis by (simp add: AF_DFS_upd1_def Let_def)
qed

lemma af_exh_upd2:
  assumes A1: "AF_invar_1 st" and A2: "AF_invar_2 st" and iter: "AF_invar_iter st" and iV: "AF_invar_V st"
    and E: "AF_invar_exh st" and c: "AF_DFS_call_2_conds st"
  shows "AF_invar_exh (AF_DFS_upd2 st)"
proof -
  have ne: "af_vstack st \<noteq> []" using c by (auto elim!: call_cond_elims)
  have aii: "in_invar (af_in_arr st)" using A1 by (simp add: AF_invar_1_def)
  have mi': "multigraph_inv (af_out_arr st) (af_in_arr st)" using iter by (simp add: AF_invar_iter_def)
  have vV: "hd (af_vstack st) \<in> \<V>" using iV ne hd_in_set by (auto simp: AF_invar_V_def)
  have hae: "in_has (af_in_arr st) (hd (af_vstack st))" using c by (auto elim!: call_cond_elims)
  have ae: "in_current (af_in_arr st) (hd (af_vstack st)) \<in> \<E>"
    using af_current_in_endpoint[OF mi' vV hae] by simp
  let ?st' = "st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack st))\<rparr>"
  have exh': "AF_invar_exh ?st'"
  proof (unfold AF_invar_exh_def, intro ballI impI)
    fix v assume vV': "v \<in> \<V>" and F: "st_lookup (af_state ?st') v = Finished"
    hence Fv: "st_lookup (af_state st) v = Finished" by simp
    have vnv: "v \<notin> set (af_vstack st)"
    proof
      assume "v \<in> set (af_vstack st)"
      hence "st_lookup (af_state st) v = OnStack" using A2 vV' by (auto simp: AF_invar_2_def)
      with Fv show False by simp
    qed
    hence vh: "v \<noteq> hd (af_vstack st)" using ne by auto
    have he: "in_has (af_in_arr st) (hd (af_vstack st))" using c by (auto elim!: call_cond_elims)
    have nehd: "in_remaining (af_in_arr st) (hd (af_vstack st)) \<noteq> {}" using he by (simp add: ing.idx_has[OF aii vV])
    have "in_remaining (af_in_arr ?st') v = in_remaining (af_in_arr st) v"
      using ing.idx_move_remaining_other[OF aii vV nehd vh] by simp
    thus "out_remaining (af_out_arr ?st') v = {} \<and> in_remaining (af_in_arr ?st') v = {}"
      using E Fv vV' by (simp add: AF_invar_exh_def)
  qed
  have "AF_invar_exh (af_handle ?st' (in_current (af_in_arr st) (hd (af_vstack st))) False)"
    by (rule af_handle_exh[OF AF_invar_1_in_advance[OF vV A1] _ ae _ exh'])
       (use A2 iV in \<open>simp_all add: AF_invar_2_def AF_invar_V_def\<close>)
  thus ?thesis by (simp add: AF_DFS_upd2_def Let_def)
qed

lemma af_exh_upd3:
  assumes A1: "AF_invar_1 st" and iter: "AF_invar_iter st" and iV: "AF_invar_V st"
    and E: "AF_invar_exh st" and c: "AF_DFS_call_3_conds st"
  shows "AF_invar_exh (AF_DFS_upd3 st)"
proof (unfold AF_invar_exh_def, intro ballI impI)
  fix v assume vV': "v \<in> \<V>" and F: "st_lookup (af_state (AF_DFS_upd3 st)) v = Finished"
  have si: "st_invar (af_state st)" using A1 by (simp add: AF_invar_1_def)
  have ne: "af_vstack st \<noteq> []"
    and nho: "\<not> out_has (af_out_arr st) (hd (af_vstack st))"
    and nhi: "\<not> in_has (af_in_arr st) (hd (af_vstack st))"
    using c by (auto elim!: call_cond_elims)
  have mi': "multigraph_inv (af_out_arr st) (af_in_arr st)" using iter by (simp add: AF_invar_iter_def)
  have vV: "hd (af_vstack st) \<in> \<V>" using iV ne hd_in_set by (auto simp: AF_invar_V_def)
  have aio: "out_invar (af_out_arr st)" and aii: "in_invar (af_in_arr st)"
    using mi' by (auto simp: multigraph_inv_def out_graph_inv_def in_graph_inv_def)
  have rho: "out_remaining (af_out_arr st) (hd (af_vstack st)) = {}" using nho by (simp add: outg.idx_has[OF aio vV])
  have rhi: "in_remaining (af_in_arr st) (hd (af_vstack st)) = {}" using nhi by (simp add: ing.idx_has[OF aii vV])
  have lk: "st_lookup (af_state (AF_DFS_upd3 st)) v =
              (if v = hd (af_vstack st) then Finished else st_lookup (af_state st) v)"
    using si by (simp add: AF_DFS_upd3_def state_arr.fixed_univ_map_upd[OF si vV])
  show "out_remaining (af_out_arr (AF_DFS_upd3 st)) v = {}
      \<and> in_remaining (af_in_arr (AF_DFS_upd3 st)) v = {}"
  proof (cases "v = hd (af_vstack st)")
    case True
    thus ?thesis using rho rhi by (simp add: AF_DFS_upd3_def)
  next
    case False
    hence "st_lookup (af_state st) v = Finished" using F lk by simp
    thus ?thesis using E vV' by (simp add: AF_invar_exh_def AF_DFS_upd3_def)
  qed
qed

lemma AF_DFS_exh:
  assumes dom: "AF_DFS_dom st" and mi0: "multigraph_inv out_arr in_arr"
  shows "AF_inv st \<longrightarrow> AF_invar_exh st \<longrightarrow> AF_invar_exh (AF_DFS st)"
proof (induction rule: AF_DFS_induct[OF dom])
  case IH: (1 st)
  show ?case
  proof (intro impI)
    assume inv: "AF_inv st" and E: "AF_invar_exh st"
    from inv have i1: "AF_invar_1 st" and i2: "AF_invar_2 st" and iter: "AF_invar_iter st" and iV: "AF_invar_V st"
      by (auto simp: AF_inv_def)
    show "AF_invar_exh (AF_DFS st)"
    proof (rule AF_DFS_cases[where st = st])
      assume c: "AF_DFS_call_1_conds st"
      have "AF_invar_exh (AF_DFS_upd1 st)" using af_exh_upd1[OF i1 i2 iter iV E c] .
      thus ?thesis using IH(2)[OF c] AF_inv_holds_1[OF mi0 c inv] c by (auto simp: AF_DFS_simps[OF IH(1)])
    next
      assume c: "AF_DFS_call_2_conds st"
      have "AF_invar_exh (AF_DFS_upd2 st)" using af_exh_upd2[OF i1 i2 iter iV E c] .
      thus ?thesis using IH(3)[OF c] AF_inv_holds_2[OF mi0 c inv] c by (auto simp: AF_DFS_simps[OF IH(1)])
    next
      assume c: "AF_DFS_call_3_conds st"
      have "AF_invar_exh (AF_DFS_upd3 st)" using af_exh_upd3[OF i1 iter iV E c] .
      thus ?thesis using IH(4)[OF c] AF_inv_holds_3[OF c inv] c by (auto simp: AF_DFS_simps[OF IH(1)])
    next
      assume c: "AF_DFS_ret_conds st"
      thus ?thesis using E by (simp add: AF_DFS_simps[OF IH(1)] AF_DFS_ret_def)
    qed
  qed
qed

definition "AFF_exh st \<longleftrightarrow>
  (\<forall>v\<in>\<V>. st_lookup (aff_state st) v = Finished \<longrightarrow>
        out_remaining (aff_out_arr st) v = {} \<and>
        in_remaining (aff_in_arr st) v = {})"

lemma AFF_exh_holds_1:
  assumes conds: "AF_outer_call_1_conds st" and E: "AFF_exh st"
  shows "AFF_exh (AF_outer_upd1 st)"
  using E by (simp add: AFF_exh_def AF_outer_upd1_def)

lemma AFF_exh_holds_2:
  assumes mi0: "multigraph_inv out_arr in_arr"
    and conds: "AF_outer_call_2_conds st" and inv: "AFF_inv st" and E: "AFF_exh st"
  shows "AFF_exh (AF_outer_upd2 st)"
proof -
  from inv have ff: "flow_invar (aff_flow st)" and sti: "st_invar (aff_state st)"
    and aoi: "out_invar (aff_out_arr st)" and aii: "in_invar (aff_in_arr st)"
    and mii: "multigraph_inv (aff_out_arr st) (aff_in_arr st)" and feas: "af_cap_feasible (aff_flow st)"
    and noos: "\<not> aff_unbounded st \<longrightarrow> (\<forall>w\<in>\<V>. st_lookup (aff_state st) w \<noteq> OnStack)" by (auto simp: AFF_inv_def)
  from conds have nu0: "\<not> aff_unbounded st" and hv: "has_vertex (aff_vit st)"
    and vuns: "st_lookup (aff_state st) (current_vertex (aff_vit st)) = Unseen" by (auto simp: AF_outer_call_2_conds_def)
  let ?v = "current_vertex (aff_vit st)"
  have vV: "?v \<in> \<V>" using vit_current_V[OF inv hv] .
  have noos': "\<forall>w\<in>\<V>. st_lookup (aff_state st) w \<noteq> OnStack" using noos nu0 by simp
  let ?init = "AF_DFS_initial (aff_flow st) (aff_out_arr st) (aff_in_arr st) (aff_state st) ?v"
  have invi: "AF_inv ?init" using AF_inv_initial[OF ff sti aoi aii mii vV feas noos'] .
  have domi: "AF_DFS_dom ?init" using AF_DFS_dom[OF mi0 invi] .
  have exhi: "AF_invar_exh ?init"
  proof (unfold AF_invar_exh_def, intro ballI impI)
    fix w assume wV: "w \<in> \<V>" and "st_lookup (af_state ?init) w = Finished"
    hence "st_lookup (st_upd (aff_state st) ?v OnStack) w = Finished" by (simp add: AF_DFS_initial_def)
    hence "st_lookup (aff_state st) w = Finished"
      using sti by (auto simp: state_arr.fixed_univ_map_upd[OF sti vV] split: if_splits)
    thus "out_remaining (af_out_arr ?init) w = {} \<and> in_remaining (af_in_arr ?init) w = {}"
      using E wV by (simp add: AFF_exh_def AF_DFS_initial_def)
  qed
  have "AF_invar_exh (AF_DFS ?init)" using AF_DFS_exh[OF domi mi0] invi exhi by blast
  thus ?thesis by (simp add: AFF_exh_def AF_invar_exh_def AF_outer_upd2_def Let_def)
qed

lemma AF_outer_inv_exh:
  assumes dom: "AF_outer_dom st" and mi0: "multigraph_inv out_arr in_arr"
  shows "AFF_inv st \<and> AFF_exh st \<longrightarrow> AFF_inv (AF_outer st) \<and> AFF_exh (AF_outer st)"
proof (induction rule: AF_outer_induct[OF dom])
  case IH: (1 st)
  show ?case
  proof
    assume ie: "AFF_inv st \<and> AFF_exh st"
    hence inv: "AFF_inv st" and E: "AFF_exh st" by auto
    show "AFF_inv (AF_outer st) \<and> AFF_exh (AF_outer st)"
    proof (rule AF_outer_cases[where st = st])
      assume c: "AF_outer_call_1_conds st"
      have step: "AFF_inv (AF_outer_upd1 st) \<and> AFF_exh (AF_outer_upd1 st)"
        using AFF_inv_holds_1[OF c inv] AFF_exh_holds_1[OF c E] by simp
      have "AFF_inv (AF_outer (AF_outer_upd1 st)) \<and> AFF_exh (AF_outer (AF_outer_upd1 st))"
        using IH(2)[OF c] step by blast
      thus ?thesis using c by (simp add: AF_outer_simps[OF IH(1)])
    next
      assume c: "AF_outer_call_2_conds st"
      have step: "AFF_inv (AF_outer_upd2 st) \<and> AFF_exh (AF_outer_upd2 st)"
        using AFF_inv_holds_2[OF mi0 c inv] AFF_exh_holds_2[OF mi0 c inv E] by simp
      have "AFF_inv (AF_outer (AF_outer_upd2 st)) \<and> AFF_exh (AF_outer (AF_outer_upd2 st))"
        using IH(3)[OF c] step by blast
      thus ?thesis using c by (simp add: AF_outer_simps[OF IH(1)])
    next
      assume c: "AF_outer_ret_conds st"
      thus ?thesis using ie by (simp add: AF_outer_simps[OF IH(1)] AF_outer_ret_def)
    qed
  qed
qed

lemma make_acyclic_all_edges_scanned:
  assumes mi0: "multigraph_inv out_arr in_arr"
    and ff: "flow_invar f0" and feas: "af_cap_feasible f0"
    and vv: "vit_invar all_vertices" and vabsV: "vit_abstract all_vertices = \<V>"
    and vit0: "vit_iterated all_vertices = {}" and res: "make_acyclic f0 = Some f'"
  shows "\<forall>v \<in> \<V>. out_remaining (aff_out_arr (AF_outer (AF_outer_initial f0))) v = {}
              \<and> in_remaining (aff_in_arr (AF_outer (AF_outer_initial f0))) v = {}"
proof -
  have vab: "vit_abstract all_vertices \<subseteq> \<V>" using vabsV by simp
  have inv0: "AFF_inv (AF_outer_initial f0)" using AFF_inv_initial[OF mi0 ff feas vv vab] .
  have exh0: "AFF_exh (AF_outer_initial f0)" using state_init_unseen by (auto simp: AFF_exh_def AF_outer_initial_def)
  have dom: "AF_outer_dom (AF_outer_initial f0)" using AF_outer_dom[OF mi0 inv0] .
  have exhR: "AFF_exh (AF_outer (AF_outer_initial f0))"
    using AF_outer_inv_exh[OF dom mi0] inv0 exh0 by blast
  have covR: "\<forall>v \<in> \<V>. st_lookup (aff_state (AF_outer (AF_outer_initial f0))) v = Finished"
    using make_acyclic_all_finished[OF mi0 ff feas vv vabsV vit0 res] .
  show ?thesis using exhR covR by (auto simp: AFF_exh_def)
qed

text \<open>Fourth building block: \emph{free-arc monotonicity} (MONO). Each cancellation pushes flow around a
      closed trail of \emph{free} arcs, moving every arc on the trail toward a capacity boundary and
      leaving arcs off the trail untouched; so no arc ever \emph{becomes} free --- the free set only
      shrinks. Consequently an arc that is free in the final flow was free throughout the run, in
      particular at the moment it was scanned. Lifting the single-step fact through @{const af_handle},
      @{const AF_DFS} and @{const AF_outer} gives that @{const af_arc_free} of the returned flow implies
      @{const af_arc_free} of the input --- and, applied at intermediate states, of every flow in
      between.\<close>

lemma af_handle_free_mono:
  assumes A1: "AF_invar_1 st" and Afe: "AF_invar_feas st" and Afr: "AF_invar_free st" and ae: "a \<in> \<E>"
    and estE: "AF_invar_estE st"
    and F: "af_arc_free (af_flow (af_handle st a dir)) b"
  shows "af_arc_free (af_flow st) b"
proof -
  have fi: "flow_invar (af_flow st)" using A1 by (simp add: AF_invar_1_def)
  have esE: "set (af_estack st) \<subseteq> \<E>" using estE by (simp add: AF_invar_estE_def)
  have feas_a: "cap a = - 1 \<or> flow_lookup (af_flow st) a \<le> cap a"
    using Afe ae by (auto simp: AF_invar_feas_def af_cap_feasible_def)
  have frees: "\<forall>c\<in>set (af_estack st). af_arc_free (af_flow st) c" using Afr by (simp add: AF_invar_free_def)
  obtain up dn where updn: "af_rooms (af_flow st) a = (up, dn)" by (cases "af_rooms (af_flow st) a") auto
  have gfree: "(0 < dn \<and> (up = - 1 \<or> 0 < up)) = af_arc_free (af_flow st) a"
    using af_guard_free[OF updn feas_a] .
  show ?thesis
  proof (cases "fst_exec a = snd_exec a")
    case sl: True
    have ha: "af_handle st a dir = af_selfloop_handle st a" using sl by (simp add: af_handle_def)
    show ?thesis
    proof (cases "b = a")
      case True
      have fr': "af_arc_free (af_flow (af_selfloop_handle st a)) a" using F ha True by simp
      have "af_flow (af_selfloop_handle st a) = af_flow st"
        using af_selfloop_handle_free_imp_flow_id[OF ae fi fr'] .
      thus ?thesis using fr' True by simp
    next
      case False
      have "af_arc_free (af_flow (af_selfloop_handle st a)) b = af_arc_free (af_flow st) b"
        using af_selfloop_handle_flow_off[OF ae fi False] by (simp add: af_arc_free_def)
      thus ?thesis using F ha by simp
    qed
  next
    case selfloop: False
    show ?thesis
    proof (cases "0 < dn \<and> (up = - 1 \<or> 0 < up)")
      case False thus ?thesis using updn F selfloop by (simp add: af_handle_def Let_def)
    next
      case guard: True
      have afreea: "af_arc_free (af_flow st) a" using gfree guard by simp
      show ?thesis
      proof (cases "af_estack st \<noteq> [] \<and> a = hd (af_estack st)")
        case True
        have "af_handle st a dir = st" using updn selfloop True by (auto simp: af_handle_def Let_def)
        thus ?thesis using F by simp
      next
        case parent: False
        show ?thesis
        proof (cases "st_lookup (af_state st) (if dir then snd_exec a else fst_exec a)")
          case Unseen thus ?thesis using updn guard selfloop parent F by (auto simp: af_handle_def Let_def)
        next
          case OnStack
          obtain fl m' ubd where c: "af_cancel_seg up dn (if dir then snd_exec a else fst_exec a)
              (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) = (fl, m', ubd)"
            by (metis prod_cases3)
          show ?thesis
          proof (cases ubd)
            case True thus ?thesis using updn guard selfloop parent OnStack c F by (auto simp: af_handle_def Let_def)
          next
            case False
            have fl_eq: "af_flow (af_handle st a dir) = fl"
              using updn guard selfloop parent OnStack c False by (auto simp: af_handle_def Let_def)
            show ?thesis
            proof (cases "b \<in> set (af_estack st) \<or> b = a")
              case True thus ?thesis using afreea frees by auto
            next
              case False
              hence bni: "b \<notin> set (af_estack st)" and bna: "b \<noteq> a" by auto
              have "af_arc_free fl b = af_arc_free (af_flow st) b"
                using af_cancel_seg_arc_free_off[OF esE ae fi bni bna c] by simp
              thus ?thesis using F fl_eq by simp
            qed
          qed
        next
          case Finished
          have "af_handle st a dir = st" using updn selfloop parent Finished by (auto simp: af_handle_def Let_def)
          thus ?thesis using F by simp
        qed
      qed
    qed
  qed
qed

text \<open>A scanned self-loop's flow value is untouched by @{const af_handle} at any \emph{other} edge: it
      is never on the cancelled walk (@{thm [source] a_notin_estack_selfloop}), so every branch --- the
      self-loop normaliser (which touches only the current edge), the push/skip/flag branches (no flow
      change), and a real cancellation (off-walk arcs preserved, @{thm [source] af_cancel_seg_flow_off})
      --- leaves it fixed. This is the value-level analogue of @{thm [source] af_handle_free_mono}.\<close>

lemma af_handle_flow_selfloop_off:
  assumes A1: "AF_invar_1 st" and A2: "AF_invar_2 st" and A3: "AF_invar_3 st"
    and estE: "AF_invar_estE st"
    and ae: "a \<in> \<E>" and esl: "fst e = snd e" and ene: "e \<noteq> a"
  shows "flow_lookup (af_flow (af_handle st a dir)) e = flow_lookup (af_flow st) e"
proof -
  have fi: "flow_invar (af_flow st)" using A1 by (simp add: AF_invar_1_def)
  have esE: "set (af_estack st) \<subseteq> \<E>" using estE by (simp add: AF_invar_estE_def)
  have eni: "e \<notin> set (af_estack st)" using a_notin_estack_selfloop[OF A2 A3 esl] .
  obtain up dn where updn: "af_rooms (af_flow st) a = (up, dn)" by (cases "af_rooms (af_flow st) a") auto
  show ?thesis
  proof (cases "fst_exec a = snd_exec a")
    case sl: True
    have ha: "af_handle st a dir = af_selfloop_handle st a" using sl by (simp add: af_handle_def)
    show ?thesis using af_selfloop_handle_flow_off[OF ae fi ene] ha by simp
  next
    case selfloop: False
    show ?thesis
    proof (cases "0 < dn \<and> (up = - 1 \<or> 0 < up)")
      case False thus ?thesis using updn selfloop by (simp add: af_handle_def Let_def)
    next
      case guard: True
      show ?thesis
      proof (cases "af_estack st \<noteq> [] \<and> a = hd (af_estack st)")
        case True
        have "af_handle st a dir = st" using updn selfloop True by (auto simp: af_handle_def Let_def)
        thus ?thesis by simp
      next
        case parent: False
        show ?thesis
        proof (cases "st_lookup (af_state st) (if dir then snd_exec a else fst_exec a)")
          case Unseen thus ?thesis using updn guard selfloop parent by (auto simp: af_handle_def Let_def)
        next
          case OnStack
          obtain fl m' ubd where c: "af_cancel_seg up dn (if dir then snd_exec a else fst_exec a)
              (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) = (fl, m', ubd)"
            by (metis prod_cases3)
          show ?thesis
          proof (cases ubd)
            case True thus ?thesis using updn guard selfloop parent OnStack c by (auto simp: af_handle_def Let_def)
          next
            case False
            have fl_eq: "af_flow (af_handle st a dir) = fl"
              using updn guard selfloop parent OnStack c False by (auto simp: af_handle_def Let_def)
            have "flow_lookup fl e = flow_lookup (af_flow st) e"
              using af_cancel_seg_flow_off[OF esE ae fi eni ene c] by simp
            thus ?thesis using fl_eq by simp
          qed
        next
          case Finished
          have "af_handle st a dir = st" using updn selfloop parent Finished by (auto simp: af_handle_def Let_def)
          thus ?thesis by simp
        qed
      qed
    qed
  qed
qed

lemma af_free_mono_upd1:
  assumes inv: "AF_inv st" and c: "AF_DFS_call_1_conds st" and F: "af_arc_free (af_flow (AF_DFS_upd1 st)) b"
  shows "af_arc_free (af_flow st) b"
proof -
  from inv have i1: "AF_invar_1 st" and iit: "AF_invar_iter st" and iV: "AF_invar_V st"
    and ife: "AF_invar_feas st" and ifr: "AF_invar_free st" and iestE: "AF_invar_estE st" by (auto simp: AF_inv_def)
  from c have ne: "af_vstack st \<noteq> []" and he: "out_has (af_out_arr st) (hd (af_vstack st))"
    by (auto elim!: call_cond_elims)
  have mi': "multigraph_inv (af_out_arr st) (af_in_arr st)" using iit by (simp add: AF_invar_iter_def)
  have vV: "hd (af_vstack st) \<in> \<V>" using iV ne hd_in_set by (auto simp: AF_invar_V_def)
  have ae: "out_current (af_out_arr st) (hd (af_vstack st)) \<in> \<E>"
    using af_current_out_endpoint[OF mi' vV he] by simp
  let ?st' = "st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack st))\<rparr>"
  have "af_arc_free (af_flow ?st') b"
    by (rule af_handle_free_mono[OF AF_invar_1_out_advance[OF vV i1] _ _ ae])
       (use ife ifr iestE F in \<open>simp_all add: AF_invar_feas_def AF_invar_free_def AF_invar_estE_def AF_DFS_upd1_def Let_def\<close>)
  thus ?thesis by simp
qed

lemma af_free_mono_upd2:
  assumes inv: "AF_inv st" and c: "AF_DFS_call_2_conds st" and F: "af_arc_free (af_flow (AF_DFS_upd2 st)) b"
  shows "af_arc_free (af_flow st) b"
proof -
  from inv have i1: "AF_invar_1 st" and iit: "AF_invar_iter st" and iV: "AF_invar_V st"
    and ife: "AF_invar_feas st" and ifr: "AF_invar_free st" and iestE: "AF_invar_estE st" by (auto simp: AF_inv_def)
  from c have ne: "af_vstack st \<noteq> []" and he: "in_has (af_in_arr st) (hd (af_vstack st))"
    by (auto elim!: call_cond_elims)
  have mi': "multigraph_inv (af_out_arr st) (af_in_arr st)" using iit by (simp add: AF_invar_iter_def)
  have vV: "hd (af_vstack st) \<in> \<V>" using iV ne hd_in_set by (auto simp: AF_invar_V_def)
  have ae: "in_current (af_in_arr st) (hd (af_vstack st)) \<in> \<E>"
    using af_current_in_endpoint[OF mi' vV he] by simp
  let ?st' = "st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack st))\<rparr>"
  have "af_arc_free (af_flow ?st') b"
    by (rule af_handle_free_mono[OF AF_invar_1_in_advance[OF vV i1] _ _ ae])
       (use ife ifr iestE F in \<open>simp_all add: AF_invar_feas_def AF_invar_free_def AF_invar_estE_def AF_DFS_upd2_def Let_def\<close>)
  thus ?thesis by simp
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
  a \<in> out_iterated (aff_out_arr st) (fst a) \<or>
  a \<in> in_iterated (aff_in_arr st) (snd a)"

definition "AFF_forest st \<longleftrightarrow>
  \<not> (\<exists>C. prepath C \<and> (\<forall>e\<in>set C. af_arc_free (aff_flow st) (oedge e) \<and> AFF_scanned st (oedge e))
        \<and> distinct (map oedge C) \<and> fstv (hd C) = sndv (last C) \<and> set C \<subseteq> \<EE>)"

lemma AFF_scanned_of_exhausted:
  assumes mii: "multigraph_inv (aff_out_arr st) (aff_in_arr st)"
    and exh: "out_remaining (aff_out_arr st) (fst a) = {}"
    and a: "a \<in> \<E>"
  shows "AFF_scanned st a"
proof -
  have vV: "fst a \<in> \<V>" using fst_E_V[OF a] .
  have oi: "out_invar (aff_out_arr st)" and ab: "out_abstract (aff_out_arr st) (fst a) = \<delta>\<^sup>+ (fst a)"
    using mii vV by (auto simp: multigraph_inv_def out_graph_inv_def)
  have "out_iterated (aff_out_arr st) (fst a) = out_abstract (aff_out_arr st) (fst a)"
    using outg.idx_partition_union[OF oi vV] exh by auto
  also have "\<dots> = \<delta>\<^sup>+ (fst a)" using ab .
  finally have "a \<in> out_iterated (aff_out_arr st) (fst a)"
    using a by (auto simp: delta_plus_def)
  thus ?thesis by (simp add: AFF_scanned_def)
qed

lemma make_acyclic_forest_nfc:
  assumes mi0: "multigraph_inv out_arr in_arr"
    and ff: "flow_invar f0" and feas: "af_cap_feasible f0"
    and vv: "vit_invar all_vertices" and vabsV: "vit_abstract all_vertices = \<V>"
    and vit0: "vit_iterated all_vertices = {}" and res: "make_acyclic f0 = Some f'"
    and forest: "AFF_forest (AF_outer (AF_outer_initial f0))"
  shows "\<nexists>C. prepath C \<and> (\<forall>e\<in>set C. af_arc_free f' (oedge e)) \<and> distinct (map oedge C)
             \<and> fstv (hd C) = sndv (last C) \<and> set C \<subseteq> \<EE>"
proof (rule notI, elim exE conjE)
  fix C
  assume C: "prepath C" "\<forall>e\<in>set C. af_arc_free f' (oedge e)" "distinct (map oedge C)"
    "fstv (hd C) = sndv (last C)" "set C \<subseteq> \<EE>"
  let ?st' = "AF_outer (AF_outer_initial f0)"
  have ff': "f' = aff_flow ?st'" using res by (auto simp: make_acyclic_def Let_def split: if_splits)
  have vab: "vit_abstract all_vertices \<subseteq> \<V>" using vabsV by simp
  have inv0: "AFF_inv (AF_outer_initial f0)" using AFF_inv_initial[OF mi0 ff feas vv vab] .
  have dom: "AF_outer_dom (AF_outer_initial f0)" using AF_outer_dom[OF mi0 inv0] .
  have miR: "multigraph_inv (aff_out_arr ?st') (aff_in_arr ?st')"
    using AFF_inv_holds[OF dom mi0 inv0] by (simp add: AFF_inv_def)
  have scan: "\<forall>v \<in> \<V>. out_remaining (aff_out_arr ?st') v = {}
                    \<and> in_remaining (aff_in_arr ?st') v = {}"
    using make_acyclic_all_edges_scanned[OF mi0 ff feas vv vabsV vit0 res] .
  have "\<forall>e\<in>set C. af_arc_free (aff_flow ?st') (oedge e) \<and> AFF_scanned ?st' (oedge e)"
  proof
    fix e assume e: "e \<in> set C"
    have oe: "oedge e \<in> \<E>" using C(5) e o_edge_res by auto
    have free: "af_arc_free (aff_flow ?st') (oedge e)" using C(2) e ff' by auto
    have "fst (oedge e) \<in> \<V>" using fst_E_V[OF oe] .
    hence "out_remaining (aff_out_arr ?st') (fst (oedge e)) = {}" using scan by auto
    hence "AFF_scanned ?st' (oedge e)" using AFF_scanned_of_exhausted[OF miR _ oe] by simp
    thus "af_arc_free (aff_flow ?st') (oedge e) \<and> AFF_scanned ?st' (oedge e)" using free by simp
  qed
  hence "\<exists>C. prepath C \<and> (\<forall>e\<in>set C. af_arc_free (aff_flow ?st') (oedge e) \<and> AFF_scanned ?st' (oedge e))
          \<and> distinct (map oedge C) \<and> fstv (hd C) = sndv (last C) \<and> set C \<subseteq> \<EE>"
    using C(1,3,4,5) by blast
  thus False using forest by (simp add: AFF_forest_def)
qed

lemma make_acyclic_acyclic_from_forest:
  assumes mi0: "multigraph_inv out_arr in_arr"
    and ff: "flow_invar f0" and feas: "af_cap_feasible f0"
    and vv: "vit_invar all_vertices" and vabsV: "vit_abstract all_vertices = \<V>"
    and vit0: "vit_iterated all_vertices = {}" and res: "make_acyclic f0 = Some f'"
    and forest: "AFF_forest (AF_outer (AF_outer_initial f0))"
  shows "acyclic_flow (h \<circ> flow_lookup f')"
  using acyclic_flow_from_no_free_cycle[OF make_acyclic_forest_nfc[OF mi0 ff feas vv vabsV vit0 res forest]] .

text \<open>Preservation, outer loop. The skip step changes neither the flow, the iterators, nor the seen
      set, so it trivially preserves the forest invariant. The launch step runs a whole inner DFS and
      is the substantial obligation --- it is where the \<open>DFS_Cycles_Aux\<close>-style \<open>invar_cycle_false\<close>
      argument (ported to the flow-mutating, truncate-and-reset procedure, with the invariant stated at
      quiescent configurations and a self-healing lemma for the back-edge transient) must be discharged.\<close>

text \<open>DFS-level forest invariant and the reduction of the launch step to it. \<open>AF_forest\<close> is the
      inner-DFS analogue of @{const AFF_forest}; the launch feeds the outer flow/iterators/seen set into
      a fresh inner state, so @{const AFF_forest} of the launched configuration equals \<open>AF_forest\<close>
      of the inner initial state, and @{const AFF_forest} after the launch equals \<open>AF_forest\<close> of
      the inner result. Hence \<open>AFF_forest_holds_2\<close> reduces exactly to \emph{@{const AF_DFS}
      preserves \<open>AF_forest\<close>} --- the ported \<open>invar_cycle_false\<close> obligation.\<close>

definition "af_scanned st a \<longleftrightarrow>
  a \<in> out_iterated (af_out_arr st) (fst a) \<or>
  a \<in> in_iterated (af_in_arr st) (snd a)"

definition "AF_forest st \<longleftrightarrow>
  \<not> (\<exists>C. prepath C \<and> (\<forall>e\<in>set C. af_arc_free (af_flow st) (oedge e) \<and> af_scanned st (oedge e))
        \<and> distinct (map oedge C) \<and> fstv (hd C) = sndv (last C) \<and> set C \<subseteq> \<EE>)"

text \<open>The easy half of a step: a witness cycle that avoids the newly-scanned arc @{term a} is already a
      witness in the pre-state, given that freeness is monotone (Theme F/MONO) and no arc other than
      @{term a} gains scanned status. The remaining (hard) half is a witness \emph{through} @{term a},
      handled per @{const af_handle} branch --- the back-edge cancellation breaking the fundamental
      cycle and the push/finished-skip cases via the quiescent exploration invariants (E2/E4) and the
      self-healing lemma.\<close>

text \<open>The @{term scan_sub} ingredient of the forest step: advancing an iterator adds only the
      current edge to the scanned set. An arc scanned after the advance, other than the current one, was
      already scanned before.\<close>

lemma af_out_advance_scan_sub:
  assumes A1: "AF_invar_1 st" and iter: "AF_invar_iter st" and iV: "AF_invar_V st"
    and ne: "af_vstack st \<noteq> []" and he: "out_has (af_out_arr st) (hd (af_vstack st))"
    and bne: "b \<noteq> out_current (af_out_arr st) (hd (af_vstack st))"
    and F: "af_scanned (st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack st))\<rparr>) b"
  shows "af_scanned st b"
proof -
  let ?top = "hd (af_vstack st)"
  let ?st' = "st\<lparr>af_out_arr := out_move (af_out_arr st) ?top\<rparr>"
  have aio: "out_invar (af_out_arr st)" using A1 by (simp add: AF_invar_1_def)
  have topV: "?top \<in> \<V>" using iV ne hd_in_set by (auto simp: AF_invar_V_def)
  have rem: "out_remaining (af_out_arr st) ?top \<noteq> {}" using he by (simp add: outg.idx_has[OF aio topV])
  from F have "b \<in> out_iterated (af_out_arr ?st') (fst b) \<or> b \<in> in_iterated (af_in_arr st) (snd b)"
    by (simp add: af_scanned_def)
  thus "af_scanned st b"
  proof
    assume out: "b \<in> out_iterated (af_out_arr ?st') (fst b)"
    show ?thesis
    proof (cases "fst b = ?top")
      case True
      have "out_iterated (af_out_arr ?st') (fst b)
              = out_iterated (af_out_arr st) ?top \<union> {out_current (af_out_arr st) ?top}"
        using True outg.idx_move_iterated[OF aio topV rem] by simp
      hence "b \<in> out_iterated (af_out_arr st) ?top" using out bne by simp
      thus ?thesis using True by (simp add: af_scanned_def)
    next
      case False
      hence "b \<in> out_iterated (af_out_arr st) (fst b)"
        using out outg.idx_move_iterated_other[OF aio topV rem] by simp
      thus ?thesis by (simp add: af_scanned_def)
    qed
  next
    assume "b \<in> in_iterated (af_in_arr st) (snd b)"
    thus ?thesis by (simp add: af_scanned_def)
  qed
qed

lemma af_in_advance_scan_sub:
  assumes A1: "AF_invar_1 st" and iter: "AF_invar_iter st" and iV: "AF_invar_V st"
    and ne: "af_vstack st \<noteq> []" and he: "in_has (af_in_arr st) (hd (af_vstack st))"
    and bne: "b \<noteq> in_current (af_in_arr st) (hd (af_vstack st))"
    and F: "af_scanned (st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack st))\<rparr>) b"
  shows "af_scanned st b"
proof -
  let ?top = "hd (af_vstack st)"
  let ?st' = "st\<lparr>af_in_arr := in_move (af_in_arr st) ?top\<rparr>"
  have aii: "in_invar (af_in_arr st)" using A1 by (simp add: AF_invar_1_def)
  have topV: "?top \<in> \<V>" using iV ne hd_in_set by (auto simp: AF_invar_V_def)
  have rem: "in_remaining (af_in_arr st) ?top \<noteq> {}" using he by (simp add: ing.idx_has[OF aii topV])
  from F have "b \<in> out_iterated (af_out_arr st) (fst b) \<or> b \<in> in_iterated (af_in_arr ?st') (snd b)"
    by (simp add: af_scanned_def)
  thus "af_scanned st b"
  proof
    assume "b \<in> out_iterated (af_out_arr st) (fst b)"
    thus ?thesis by (simp add: af_scanned_def)
  next
    assume inn: "b \<in> in_iterated (af_in_arr ?st') (snd b)"
    show ?thesis
    proof (cases "snd b = ?top")
      case True
      have "in_iterated (af_in_arr ?st') (snd b)
              = in_iterated (af_in_arr st) ?top \<union> {in_current (af_in_arr st) ?top}"
        using True ing.idx_move_iterated[OF aii topV rem] by simp
      hence "b \<in> in_iterated (af_in_arr st) ?top" using inn bne by simp
      thus ?thesis using True by (simp add: af_scanned_def)
    next
      case False
      hence "b \<in> in_iterated (af_in_arr st) (snd b)"
        using inn ing.idx_move_iterated_other[OF aii topV rem] by simp
      thus ?thesis by (simp add: af_scanned_def)
    qed
  qed
qed

subsection \<open>Theme F, part 4: exploration bookkeeping (towards the ported cycle invariant)\<close>

text \<open>The seen and finished vertex sets and their relation to the stack --- the analogue of
      \<open>DFS_Cycles_Aux.invar_seen_stack_finished\<close>. The finished set is exactly the seen set minus
      the stack; the stack is a subset of the seen set; finished and stack are disjoint.\<close>

definition "af_seen st = {v. st_lookup (af_state st) v \<noteq> Unseen}"
definition "af_fin st = {v. st_lookup (af_state st) v = Finished}"

subsection \<open>Theme F, part 4: an instrumented DFS carrying a finish clock (proof only)\<close>

text \<open>A ghost \emph{finish clock}: \<open>AF_DFS_i\<close> runs exactly like the executable @{const AF_DFS}
      but additionally threads a pure rank function @{typ \<open>'v \<Rightarrow> nat\<close>} and a counter, stamping each
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
  assumes dom: "AF_DFS_dom st"
  shows "\<forall>rk c. AF_DFS_i_dom (st, rk, c)"
proof (induction rule: AF_DFS_induct[OF dom])
  case (1 st)
  show ?case
  proof (intro allI)
    fix rk c
    show "AF_DFS_i_dom (st, rk, c)"
    proof (rule AF_DFS_i.domintros)
      fix x21 x22
      assume a: "\<not> af_unbounded st" "af_vstack st = x21 # x22" "out_has (af_out_arr st) x21"
      have c1: "AF_DFS_call_1_conds st" using a by (auto simp: AF_DFS_call_1_conds_def)
      have eq: "af_handle (st\<lparr>af_out_arr := out_move (af_out_arr st) x21\<rparr>)
                  (out_current (af_out_arr st) x21) True = AF_DFS_upd1 st"
        using a(2) by (simp add: AF_DFS_upd1_def Let_def)
      show "AF_DFS_i_dom (af_handle (st\<lparr>af_out_arr := out_move (af_out_arr st) x21\<rparr>)
                  (out_current (af_out_arr st) x21) True, rk, c)"
        using 1(2)[OF c1] eq by simp
    next
      fix x21 x22
      assume a: "\<not> af_unbounded st" "af_vstack st = x21 # x22" "\<not> out_has (af_out_arr st) x21"
        "in_has (af_in_arr st) x21"
      have c2: "AF_DFS_call_2_conds st" using a by (auto simp: AF_DFS_call_2_conds_def)
      have eq: "af_handle (st\<lparr>af_in_arr := in_move (af_in_arr st) x21\<rparr>)
                  (in_current (af_in_arr st) x21) False = AF_DFS_upd2 st"
        using a(2) by (simp add: AF_DFS_upd2_def Let_def)
      show "AF_DFS_i_dom (af_handle (st\<lparr>af_in_arr := in_move (af_in_arr st) x21\<rparr>)
                  (in_current (af_in_arr st) x21) False, rk, c)"
        using 1(3)[OF c2] eq by simp
    next
      fix x21 x22
      assume a: "\<not> af_unbounded st" "af_vstack st = x21 # x22" "\<not> out_has (af_out_arr st) x21"
        "\<not> in_has (af_in_arr st) x21"
      have c3: "AF_DFS_call_3_conds st" using a by (auto simp: AF_DFS_call_3_conds_def)
      have eq: "st\<lparr>af_vstack := x22, af_state := st_upd (af_state st) x21 Finished,
                   af_estack := tl (af_estack st), af_dstack := tl (af_dstack st)\<rparr> = AF_DFS_upd3 st"
        using a(2) by (simp add: AF_DFS_upd3_def)
      show "AF_DFS_i_dom (st\<lparr>af_vstack := x22, af_state := st_upd (af_state st) x21 Finished,
                   af_estack := tl (af_estack st), af_dstack := tl (af_dstack st)\<rparr>, rk(x21 := c), Suc c)"
        using 1(4)[OF c3] eq by simp
    qed
  qed
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
     (\<forall>a1 a2. a1 \<in> \<E> \<longrightarrow> af_arc_free (af_flow st) a1 \<longrightarrow> v \<in> {fst a1, snd a1} \<longrightarrow> af_hgt st rk v a1 \<longrightarrow>
              a2 \<in> \<E> \<longrightarrow> af_arc_free (af_flow st) a2 \<longrightarrow> v \<in> {fst a2, snd a2} \<longrightarrow> af_hgt st rk v a2 \<longrightarrow>
              a1 = a2))"

text \<open>The pop case of J' (the crux). Assume every free arc incident to the popping vertex @{term v}
      whose far endpoint is not yet finished is @{term v}'s parent arc (@{term \<open>hd (af_estack st)\<close>}) ---
      the fact the running scan-resolution invariant will supply, following from exhaustion, MONO, and
      the truncation behaviour. Then stamping @{term v} with the current clock preserves @{const af_rankok}:
      for @{term v} itself all higher-rank free arcs coincide with the parent arc (so $\leq 1$), and for a
      previously-finished vertex the ``higher'' status of each of its arcs is unchanged (a neighbour that
      was on the stack, hence counted as later, becomes finished with strictly larger rank).\<close>

lemma af_rankok_pop:
  assumes ok: "af_rankok st rk"
    and si: "st_invar (af_state st)" and vV: "v \<in> \<V>"
    and vfin: "st_lookup (af_state st) v \<noteq> Finished"
    and vrank: "\<And>u. u \<in> \<V> \<Longrightarrow> st_lookup (af_state st) u = Finished \<Longrightarrow> rk u < (c :: nat)"
    and res: "\<And>a. a \<in> \<E> \<Longrightarrow> af_arc_free (af_flow st) a \<Longrightarrow> v \<in> {fst a, snd a}
               \<Longrightarrow> st_lookup (af_state st) (if fst a = v then snd a else fst a) \<noteq> Finished
               \<Longrightarrow> af_estack st \<noteq> [] \<and> a = hd (af_estack st)"
  shows "af_rankok (st\<lparr>af_vstack := vs, af_state := st_upd (af_state st) v Finished,
                       af_estack := tl (af_estack st), af_dstack := tl (af_dstack st)\<rparr>) (rk(v := c))"
proof (unfold af_rankok_def, intro ballI allI impI)
  let ?st' = "st\<lparr>af_vstack := vs, af_state := st_upd (af_state st) v Finished,
                 af_estack := tl (af_estack st), af_dstack := tl (af_dstack st)\<rparr>"
  fix u a1 a2
  assume uV: "u \<in> \<V>" and uf: "st_lookup (af_state ?st') u = Finished"
    and a1: "a1 \<in> \<E>" "af_arc_free (af_flow ?st') a1" "u \<in> {fst a1, snd a1}" "af_hgt ?st' (rk(v := c)) u a1"
    and a2: "a2 \<in> \<E>" "af_arc_free (af_flow ?st') a2" "u \<in> {fst a2, snd a2}" "af_hgt ?st' (rk(v := c)) u a2"
  have flow: "af_flow ?st' = af_flow st" by simp
  have lk: "\<And>w. st_lookup (af_state ?st') w = (if w = v then Finished else st_lookup (af_state st) w)"
    using si by (simp add: state_arr.fixed_univ_map_upd[OF si vV])
  have hgt_v: "\<And>a. a \<in> \<E> \<Longrightarrow> af_hgt ?st' (rk(v := c)) v a
                 \<Longrightarrow> st_lookup (af_state st) (if fst a = v then snd a else fst a) \<noteq> Finished"
  proof -
    fix a assume aE: "a \<in> \<E>" and A: "af_hgt ?st' (rk(v := c)) v a"
    define w where "w = (if fst a = v then snd a else fst a)"
    have wV: "w \<in> \<V>" using fst_E_V[OF aE] snd_E_V[OF aE] by (auto simp: w_def)
    from A have H: "st_lookup (af_state ?st') w \<noteq> Finished \<or> (rk(v := c)) w > (rk(v := c)) v"
      by (simp add: af_hgt_def w_def)
    show "st_lookup (af_state st) w \<noteq> Finished"
    proof
      assume F: "st_lookup (af_state st) w = Finished"
      have wnv: "w \<noteq> v" using F vfin by auto
      have "st_lookup (af_state ?st') w = Finished" using F wnv lk by simp
      moreover have "\<not> (rk(v := c)) w > (rk(v := c)) v"
        using vrank[OF wV F] wnv by (simp add: not_less)
      ultimately show False using H by simp
    qed
  qed
  show "a1 = a2"
  proof (cases "u = v")
    case True
    have e1: "af_estack st \<noteq> [] \<and> a1 = hd (af_estack st)"
      using res[OF a1(1)] a1(2,3,4) hgt_v[OF a1(1)] True flow by auto
    have e2: "af_estack st \<noteq> [] \<and> a2 = hd (af_estack st)"
      using res[OF a2(1)] a2(2,3,4) hgt_v[OF a2(1)] True flow by auto
    show ?thesis using e1 e2 by simp
  next
    case notv: False
    hence ust: "st_lookup (af_state st) u = Finished" using uf lk by simp
    hence ultc: "rk u < c" using vrank uV by simp
    have hgt_eq: "\<And>a. af_hgt ?st' (rk(v := c)) u a = af_hgt st rk u a"
    proof -
      fix a
      define w where "w = (if fst a = u then snd a else fst a)"
      show "af_hgt ?st' (rk(v := c)) u a = af_hgt st rk u a"
      proof (cases "w = v")
        case True
        have "st_lookup (af_state ?st') w = Finished" using True lk by simp
        moreover have "(rk(v := c)) w > (rk(v := c)) u" using True ultc notv by simp
        moreover have "st_lookup (af_state st) w \<noteq> Finished" using True vfin by simp
        ultimately show ?thesis by (simp add: af_hgt_def w_def)
      next
        case Fw: False
        have "st_lookup (af_state ?st') w = st_lookup (af_state st) w" using Fw lk by simp
        moreover have "(rk(v := c)) w = rk w" using Fw by simp
        moreover have "(rk(v := c)) u = rk u" using notv by simp
        ultimately show ?thesis by (simp add: af_hgt_def w_def)
      qed
    qed
    have af1: "af_arc_free (af_flow st) a1" using a1(2) flow by simp
    have af2: "af_arc_free (af_flow st) a2" using a2(2) flow by simp
    have h1: "af_hgt st rk u a1" using a1(4) hgt_eq[of a1] by simp
    have h2: "af_hgt st rk u a2" using a2(4) hgt_eq[of a2] by simp
    show ?thesis using ok ust uV a1(1,3) af1 h1 a2(1,3) af2 h2 by (auto simp: af_rankok_def)
  qed
qed

text \<open>The advance branches preserve J'. @{const af_handle} never finishes a vertex and, by MONO, a
      free arc of the result was already free before, so the uniqueness of the higher arc transfers
      (no freeze reasoning needed). The advance itself only moves an iterator, touching neither the flow
      nor the seen set, so it leaves @{const af_rankok} unchanged.\<close>

lemma af_handle_af_rankok:
  assumes A1: "AF_invar_1 st" and A2: "AF_invar_2 st" and Afe: "AF_invar_feas st"
    and Afr: "AF_invar_free st" and ae: "a \<in> \<E>" and AV: "AF_invar_V st" and Est: "AF_invar_estE st"
    and ok: "af_rankok st rk"
  shows "af_rankok (af_handle st a dir) rk"
proof (unfold af_rankok_def, intro ballI allI impI)
  fix u a1 a2
  assume uV: "u \<in> \<V>" and uf: "st_lookup (af_state (af_handle st a dir)) u = Finished"
    and a1: "a1 \<in> \<E>" "af_arc_free (af_flow (af_handle st a dir)) a1" "u \<in> {fst a1, snd a1}"
            "af_hgt (af_handle st a dir) rk u a1"
    and a2: "a2 \<in> \<E>" "af_arc_free (af_flow (af_handle st a dir)) a2" "u \<in> {fst a2, snd a2}"
            "af_hgt (af_handle st a dir) rk u a2"
  have fineq: "\<And>w. (st_lookup (af_state (af_handle st a dir)) w = Finished) = (st_lookup (af_state st) w = Finished)"
    using af_handle_finished_mono[OF A1 A2 ae AV] af_handle_finished_back[OF A1 A2 ae AV] by blast
  have hgt: "\<And>b. af_hgt (af_handle st a dir) rk u b = af_hgt st rk u b"
    by (simp add: af_hgt_def fineq)
  have ufst: "st_lookup (af_state st) u = Finished" using uf fineq by simp
  have af1: "af_arc_free (af_flow st) a1" using af_handle_free_mono[OF A1 Afe Afr ae Est a1(2)] .
  have af2: "af_arc_free (af_flow st) a2" using af_handle_free_mono[OF A1 Afe Afr ae Est a2(2)] .
  show "a1 = a2"
    using ok ufst uV a1(1,3) af1 a1(4) a2(1,3) af2 a2(4) hgt by (auto simp: af_rankok_def)
qed

lemma af_rankok_upd1:
  assumes inv: "AF_inv st" and c: "AF_DFS_call_1_conds st" and ok: "af_rankok st rk"
  shows "af_rankok (AF_DFS_upd1 st) rk"
proof -
  from inv have i1: "AF_invar_1 st" and i2: "AF_invar_2 st" and iit: "AF_invar_iter st"
    and iV: "AF_invar_V st" and ife: "AF_invar_feas st" and ifr: "AF_invar_free st"
    and iestE: "AF_invar_estE st" by (auto simp: AF_inv_def)
  from c have ne: "af_vstack st \<noteq> []" and he: "out_has (af_out_arr st) (hd (af_vstack st))"
    by (auto elim!: call_cond_elims)
  have mi': "multigraph_inv (af_out_arr st) (af_in_arr st)" using iit by (simp add: AF_invar_iter_def)
  have vV: "hd (af_vstack st) \<in> \<V>" using iV ne hd_in_set by (auto simp: AF_invar_V_def)
  have ae: "out_current (af_out_arr st) (hd (af_vstack st)) \<in> \<E>"
    using af_current_out_endpoint[OF mi' vV he] by simp
  let ?st' = "st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack st))\<rparr>"
  have ok': "af_rankok ?st' rk" using ok by (simp add: af_rankok_def af_hgt_def)
  have "af_rankok (af_handle ?st' (out_current (af_out_arr st) (hd (af_vstack st))) True) rk"
    by (rule af_handle_af_rankok[OF AF_invar_1_out_advance[OF vV i1] _ _ _ ae _ _ ok'])
       (use i2 ife ifr iV iestE in \<open>simp_all add: AF_invar_2_def AF_invar_feas_def AF_invar_free_def AF_invar_V_def AF_invar_estE_def\<close>)
  thus ?thesis by (simp add: AF_DFS_upd1_def Let_def)
qed

lemma af_rankok_upd2:
  assumes inv: "AF_inv st" and c: "AF_DFS_call_2_conds st" and ok: "af_rankok st rk"
  shows "af_rankok (AF_DFS_upd2 st) rk"
proof -
  from inv have i1: "AF_invar_1 st" and i2: "AF_invar_2 st" and iit: "AF_invar_iter st"
    and iV: "AF_invar_V st" and ife: "AF_invar_feas st" and ifr: "AF_invar_free st"
    and iestE: "AF_invar_estE st" by (auto simp: AF_inv_def)
  from c have ne: "af_vstack st \<noteq> []" and he: "in_has (af_in_arr st) (hd (af_vstack st))"
    by (auto elim!: call_cond_elims)
  have mi': "multigraph_inv (af_out_arr st) (af_in_arr st)" using iit by (simp add: AF_invar_iter_def)
  have vV: "hd (af_vstack st) \<in> \<V>" using iV ne hd_in_set by (auto simp: AF_invar_V_def)
  have ae: "in_current (af_in_arr st) (hd (af_vstack st)) \<in> \<E>"
    using af_current_in_endpoint[OF mi' vV he] by simp
  let ?st' = "st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack st))\<rparr>"
  have ok': "af_rankok ?st' rk" using ok by (simp add: af_rankok_def af_hgt_def)
  have "af_rankok (af_handle ?st' (in_current (af_in_arr st) (hd (af_vstack st))) False) rk"
    by (rule af_handle_af_rankok[OF AF_invar_1_in_advance[OF vV i1] _ _ _ ae _ _ ok'])
       (use i2 ife ifr iV iestE in \<open>simp_all add: AF_invar_2_def AF_invar_feas_def AF_invar_free_def AF_invar_V_def AF_invar_estE_def\<close>)
  thus ?thesis by (simp add: AF_DFS_upd2_def Let_def)
qed

text \<open>Fact 1 (truncate-to-bottleneck). The arc @{term \<open>es ! (m' - 1)\<close>} joining the truncation
      survivor to its dropped child --- which @{const af_push} returns as the deepest saturated arc, so
      that @{term \<open>m'\<close>} is one more than its index --- is saturated (not free) in the post-cancellation
      flow. This is the load-bearing fact that makes the back-edge branch leave no dangling free edge:
      the survivor's boundary edge is dead, and by MONO it stays dead.\<close>

lemma af_push_bottleneck_sat:
  assumes "flow_invar fl" "distinct es"
    and "af_push \<gamma> x vs es ds flip fl = (fl', m')" "0 < m'" "set es \<subseteq> \<E>"
  shows "af_saturated (flow_lookup fl' (es ! (m' - 1))) (es ! (m' - 1))"
  using assms
proof (induction \<gamma> x vs es ds flip fl arbitrary: fl' m' rule: af_push.induct)
  case (1 \<gamma> x uu v1 vs a es d ds flip fl)
  have ain: "a \<in> \<E>" using 1(6) by auto
  have estl: "set es \<subseteq> \<E>" using 1(6) by auto
  obtain fl1 fv where pa: "af_push_arc \<gamma> a (d \<noteq> flip) fl = (fl1, fv)" by fastforce
  have fi1: "flow_invar fl1" using af_push_arc_flow_invar[OF ain pa 1(2)] .
  have lka: "flow_lookup fl1 a = fv" using af_push_arc_at[OF ain 1(2) pa] by simp
  show ?case
  proof (cases "v1 = x")
    case True
    have ev: "af_push \<gamma> x (uu # v1 # vs) (a # es) (d # ds) flip fl = (fl1, if af_saturated fv a then 1 else 0)"
      using True pa by simp
    have m': "m' = (if af_saturated fv a then 1 else 0)" and fl'eq: "fl' = fl1"
      using ev 1(4) by auto
    have sat: "af_saturated fv a" using m' 1(5) by (auto split: if_splits)
    hence m'1: "m' = 1" using m' by simp
    show ?thesis using sat lka fl'eq m'1 by simp
  next
    case False
    obtain fl2 r where rec: "af_push \<gamma> x (v1 # vs) es ds flip fl1 = (fl2, r)" by fastforce
    have ev: "af_push \<gamma> x (uu # v1 # vs) (a # es) (d # ds) flip fl =
                (fl2, if r \<noteq> 0 then Suc r else (if af_saturated fv a then 1 else 0))"
      using False pa rec by simp
    have fl'eq: "fl' = fl2"
      and m'eq: "m' = (if r \<noteq> 0 then Suc r else (if af_saturated fv a then 1 else 0))"
      using ev 1(4) by auto
    have diste: "distinct es" using 1(3) by simp
    have anotin: "a \<notin> set es" using 1(3) by simp
    have vnx: "v1 \<noteq> x" using False .
    show ?thesis
    proof (cases "r = 0")
      case True
      have m'1: "m' = (if af_saturated fv a then 1 else 0)" using m'eq True by simp
      have sat: "af_saturated fv a" using m'1 1(5) by (auto split: if_splits)
      have m'e1: "m' = 1" using m'1 sat by simp
      have "flow_lookup fl2 a = flow_lookup fl1 a"
        using af_push_flow_off[OF estl fi1 anotin rec] .
      hence "flow_lookup fl' a = fv" using fl'eq lka by simp
      thus ?thesis using sat m'e1 fl'eq by simp
    next
      case False
      have rpos: "0 < r" using False by simp
      have m'sr: "m' = Suc r" using m'eq False by simp
      have ih: "af_saturated (flow_lookup fl2 (es ! (r - 1))) (es ! (r - 1))"
        using 1(1)[OF pa[symmetric] refl vnx fi1 diste rec rpos estl] .
      have idx: "(a # es) ! (m' - 1) = es ! (r - 1)" using m'sr rpos by (simp add: nth_Cons')
      show ?thesis using ih idx fl'eq by simp
    qed
  qed
next
  case "2_1" then show ?case by simp
next
  case "2_2" then show ?case by simp
next
  case "2_3" then show ?case by simp
next
  case "2_4" then show ?case by simp
qed

text \<open>Fact 1 lifted through a full segment cancellation. The extra @{const af_push_arc} on the
      closing arc @{term a} does not touch the boundary edge @{term \<open>es ! (m' - 1)\<close>} (it lies on the
      walk @{term es}, disjoint from @{term a}), so the boundary arc stays saturated in the
      returned flow @{term fl''}.\<close>

lemma af_cancel_seg_bottleneck_sat:
  assumes fi: "flow_invar fl" and dist: "distinct es" and anotin: "a \<notin> set es"
    and esE: "set es \<subseteq> \<E>" and ae: "a \<in> \<E>"
    and cs: "af_cancel_seg up dn x vs es ds a dir fl = (fl'', m', ubd)" and mpos: "0 < m'"
  shows "af_saturated (flow_lookup fl'' (es ! (m' - 1))) (es ! (m' - 1))"
proof -
  have mle: "m' \<le> length es" using af_cancel_seg_drop_bound[OF cs] .
  have idx_lt: "m' - 1 < length es" using mle mpos by simp
  hence ene: "es ! (m' - 1) \<in> set es" by simp
  hence bne: "es ! (m' - 1) \<noteq> a" using anotin by blast
  obtain k ra rf where sc: "af_scan fl x vs es ds
      (af_delta_cost a dir, if dir then up else dn, if dir then dn else up) = (k, ra, rf)"
    by (metis prod_cases3)
  consider (fin) "(if 0 < k then rf else ra) \<noteq> - 1"
    | (sw) "\<not> (if 0 < k then rf else ra) \<noteq> - 1" "k = 0 \<and> rf \<noteq> - 1"
    | (ubdc) "\<not> (if 0 < k then rf else ra) \<noteq> - 1" "\<not> (k = 0 \<and> rf \<noteq> - 1)"
    by blast
  then show ?thesis
  proof cases
    case fin
    obtain fl' r where p: "af_push (if 0 < k then rf else ra) x vs es ds (0 < k) fl = (fl', r)"
      by fastforce
    obtain fl2 f2 where pa: "af_push_arc (if 0 < k then rf else ra) a (dir \<noteq> (0 < k)) fl' = (fl2, f2)"
      by fastforce
    from cs sc fin have e: "fl'' = fl2" and mr: "m' = r"
      using p pa by (auto simp: af_cancel_seg_def Let_def)
    have fi': "flow_invar fl'" by (rule af_push_flow_invar[OF esE p fi])
    have rpos: "0 < r" using mpos mr by simp
    have sat: "af_saturated (flow_lookup fl' (es ! (r - 1))) (es ! (r - 1))"
      by (rule af_push_bottleneck_sat[OF fi dist p rpos esE])
    have bne': "es ! (r - 1) \<noteq> a" using bne mr by simp
    have "flow_lookup fl2 (es ! (r - 1)) = flow_lookup fl' (es ! (r - 1))"
      by (rule af_push_arc_flow_off[OF ae fi' bne' pa])
    thus ?thesis using sat e mr by simp
  next
    case sw
    obtain fl' r where p: "af_push rf x vs es ds True fl = (fl', r)" by fastforce
    obtain fl2 f2 where pa: "af_push_arc rf a (dir \<noteq> True) fl' = (fl2, f2)" by fastforce
    from cs sc sw have e: "fl'' = fl2" and mr: "m' = r"
      using p pa by (auto simp: af_cancel_seg_def Let_def)
    have fi': "flow_invar fl'" by (rule af_push_flow_invar[OF esE p fi])
    have rpos: "0 < r" using mpos mr by simp
    have sat: "af_saturated (flow_lookup fl' (es ! (r - 1))) (es ! (r - 1))"
      by (rule af_push_bottleneck_sat[OF fi dist p rpos esE])
    have bne': "es ! (r - 1) \<noteq> a" using bne mr by simp
    have "flow_lookup fl2 (es ! (r - 1)) = flow_lookup fl' (es ! (r - 1))"
      by (rule af_push_arc_flow_off[OF ae fi' bne' pa])
    thus ?thesis using sat e mr by simp
  next
    case ubdc
    from cs sc ubdc have "m' = 0" by (auto simp: af_cancel_seg_def Let_def)
    thus ?thesis using mpos by simp
  qed
qed

definition "af_scanres st \<longleftrightarrow>
  (\<forall>v\<in>\<V>. \<forall>a. st_lookup (af_state st) v = OnStack \<longrightarrow> a \<in> \<E> \<longrightarrow> af_scanned st a \<longrightarrow>
         v \<in> {fst a, snd a} \<longrightarrow> af_arc_free (af_flow st) a \<longrightarrow>
         st_lookup (af_state st) (if fst a = v then snd a else fst a) \<noteq> Finished \<longrightarrow>
         a \<in> set (af_estack st))"

text \<open>The running scan-resolution invariant K (@{const af_scanres}) that will discharge the @{term res}
      hypothesis of @{thm [source] af_rankok_pop}: every scanned free arc incident to an \emph{on-stack}
      vertex, whose far endpoint is not finished, is a stack (trail) edge. Stated over on-stack vertices
      it has no reset transient --- the dangling edge left by a truncation runs from a finished vertex to
      an unseen one, so it is not incident to any on-stack vertex. Combined with the trail structure below
      and exhaustion at the pop, K forces such an arc of the top vertex to be exactly its parent edge.\<close>

lemma af_estack_incident_hd:
  assumes A2: "AF_invar_2 st" and A3: "AF_invar_3 st"
    and amem: "a \<in> set (af_estack st)" and ne: "af_vstack st \<noteq> []"
    and inc: "hd (af_vstack st) \<in> {fst a, snd a}"
  shows "a = hd (af_estack st)"
proof -
  from amem obtain j where j: "j < length (af_estack st)" and aj: "a = af_estack st ! j"
    by (metis in_set_conv_nth)
  have estne: "af_estack st \<noteq> []" using amem by auto
  have dist: "distinct (af_vstack st)" using A2 by (simp add: AF_invar_2_def)
  have len: "Suc (length (af_estack st)) = length (af_vstack st)"
    using A2 ne by (auto simp: AF_invar_2_def)
  have jl: "j < length (af_vstack st)" using j len by simp
  have sjl: "Suc j < length (af_vstack st)" using j len by simp
  have z: "0 < length (af_vstack st)" using ne by simp
  have ends: "{fst a, snd a} = {af_vstack st ! j, af_vstack st ! Suc j}"
    using A3 j aj by (auto simp: AF_invar_3_def split: if_splits)
  have hd0: "hd (af_vstack st) = af_vstack st ! 0" using hd_conv_nth[OF ne] .
  have inc0: "af_vstack st ! 0 \<in> {af_vstack st ! j, af_vstack st ! Suc j}"
    using inc unfolding hd0 ends .
  have "0 = j \<or> 0 = Suc j"
    using inc0 nth_eq_iff_index_eq[OF dist z jl] nth_eq_iff_index_eq[OF dist z sjl] by auto
  hence j0: "j = 0" by auto
  show ?thesis using aj hd_conv_nth[OF estne] j0 by simp
qed

text \<open>The closing arc handled at the top vertex is off the trail. It is incident to
      @{term \<open>hd (af_vstack st)\<close>}, so were it a stack arc it would have to be the parent
      @{term \<open>hd (af_estack st)\<close>} (by @{thm [source] af_estack_incident_hd}) --- but the back-edge
      branch is only entered when the arc is \emph{not} the parent. Hence @{const af_cancel_seg}'s
      @{term \<open>a \<notin> set es\<close>} side-condition holds for the real @{term \<open>af_estack st\<close>} segment.\<close>

lemma af_closing_arc_not_on_trail:
  assumes A2: "AF_invar_2 st" and A3: "AF_invar_3 st"
    and vne: "af_vstack st \<noteq> []" and inc: "hd (af_vstack st) \<in> {fst a, snd a}"
    and notpar: "af_estack st = [] \<or> a \<noteq> hd (af_estack st)"
  shows "a \<notin> set (af_estack st)"
proof
  assume amem: "a \<in> set (af_estack st)"
  hence estne: "af_estack st \<noteq> []" by auto
  have "a = hd (af_estack st)" using af_estack_incident_hd[OF A2 A3 amem vne inc] .
  thus False using notpar estne by simp
qed

text \<open>Fact 1 at the @{const af_handle} back-edge branch: the boundary trail arc
      @{term \<open>af_estack st ! (m' - 1)\<close>} joining the survivor @{term \<open>af_vstack st ! m'\<close>} to the deepest
      dropped vertex @{term \<open>af_vstack st ! (m' - 1)\<close>} (see @{thm [source] trail_endpoints}) is
      \emph{saturated} in the cancelled flow, hence no longer free. This is what kills the would-be
      dangling free edge from the surviving on-stack vertex to a dropped (now unseen) vertex.\<close>

lemma af_backedge_boundary_dead:
  assumes A1: "flow_invar (af_flow st)" and A2: "AF_invar_2 st" and A3: "AF_invar_3 st"
    and Est: "AF_invar_estE st" and ae: "a \<in> \<E>"
    and vne: "af_vstack st \<noteq> []" and inc: "hd (af_vstack st) \<in> {fst a, snd a}"
    and notpar: "af_estack st = [] \<or> a \<noteq> hd (af_estack st)"
    and cs: "af_cancel_seg up dn x (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st)
               = (fl, m', ubd)"
    and mpos: "0 < m'"
  shows "\<not> af_arc_free fl (af_estack st ! (m' - 1))"
proof -
  have esE: "set (af_estack st) \<subseteq> \<E>" using Est by (simp add: AF_invar_estE_def)
  have anotin: "a \<notin> set (af_estack st)"
    using af_closing_arc_not_on_trail[OF A2 A3 vne inc notpar] .
  have dist: "distinct (af_estack st)" using estack_distinct[OF A2 A3] .
  have "af_saturated (flow_lookup fl (af_estack st ! (m' - 1))) (af_estack st ! (m' - 1))"
    by (rule af_cancel_seg_bottleneck_sat[OF A1 dist anotin esE ae cs mpos])
  thus ?thesis by (simp add: af_saturated_def af_arc_free_def Let_def)
qed

text \<open>Exhaustion of a vertex's iterators means every incident edge has been scanned: an out-edge lands
      in the (now fully enumerated) out-iterator, an in-edge in the in-iterator.\<close>

lemma af_scanned_of_exhausted:
  assumes mii: "multigraph_inv (af_out_arr st) (af_in_arr st)"
    and a: "a \<in> \<E>" and v: "v \<in> {fst a, snd a}"
    and nho: "\<not> out_has (af_out_arr st) v"
    and nhi: "\<not> in_has (af_in_arr st) v"
  shows "af_scanned st a"
proof -
  from v consider (out) "v = fst a" | (inn) "v = snd a" by auto
  thus ?thesis
  proof cases
    case out
    have vV: "fst a \<in> \<V>" using fst_E_V[OF a] .
    have oi: "out_invar (af_out_arr st)" and ab: "out_abstract (af_out_arr st) (fst a) = \<delta>\<^sup>+ (fst a)"
      using mii vV by (auto simp: multigraph_inv_def out_graph_inv_def)
    have exh: "out_remaining (af_out_arr st) (fst a) = {}"
      using nho out by (simp add: outg.idx_has[OF oi vV])
    have "out_iterated (af_out_arr st) (fst a) = out_abstract (af_out_arr st) (fst a)"
      using outg.idx_partition_union[OF oi vV] exh by auto
    also have "\<dots> = \<delta>\<^sup>+ (fst a)" using ab .
    finally have "a \<in> out_iterated (af_out_arr st) (fst a)"
      using a by (auto simp: delta_plus_def)
    thus ?thesis by (simp add: af_scanned_def)
  next
    case inn
    have vV: "snd a \<in> \<V>" using snd_E_V[OF a] .
    have ii: "in_invar (af_in_arr st)" and ab: "in_abstract (af_in_arr st) (snd a) = \<delta>\<^sup>- (snd a)"
      using mii vV by (auto simp: multigraph_inv_def in_graph_inv_def)
    have exh: "in_remaining (af_in_arr st) (snd a) = {}"
      using nhi inn by (simp add: ing.idx_has[OF ii vV])
    have "in_iterated (af_in_arr st) (snd a) = in_abstract (af_in_arr st) (snd a)"
      using ing.idx_partition_union[OF ii vV] exh by auto
    also have "\<dots> = \<delta>\<^sup>- (snd a)" using ab .
    finally have "a \<in> in_iterated (af_in_arr st) (snd a)"
      using a by (auto simp: delta_minus_def)
    thus ?thesis by (simp add: af_scanned_def)
  qed
qed

text \<open>At the pop the @{term res} hypothesis of @{thm [source] af_rankok_pop} follows: the top's arcs are
      all scanned (exhaustion), so a free one with a not-finished far end lands in @{const af_estack} by
      @{const af_scanres} and is pinned to @{term \<open>hd (af_estack st)\<close>} by @{thm [source] af_estack_incident_hd}.\<close>

lemma af_scanres_res:
  assumes sr: "af_scanres st" and conds: "AF_DFS_call_3_conds st"
    and mii: "multigraph_inv (af_out_arr st) (af_in_arr st)"
    and A2: "AF_invar_2 st" and A3: "AF_invar_3 st"
    and a: "a \<in> \<E>" and free: "af_arc_free (af_flow st) a"
    and inc: "hd (af_vstack st) \<in> {fst a, snd a}"
    and farnf: "st_lookup (af_state st) (if fst a = hd (af_vstack st) then snd a else fst a) \<noteq> Finished"
  shows "af_estack st \<noteq> [] \<and> a = hd (af_estack st)"
proof -
  let ?v = "hd (af_vstack st)"
  from conds have ne: "af_vstack st \<noteq> []"
    and nho: "\<not> out_has (af_out_arr st) ?v"
    and nhi: "\<not> in_has (af_in_arr st) ?v"
    by (auto elim!: call_cond_elims)
  have vV: "?v \<in> \<V>" using inc fst_E_V[OF a] snd_E_V[OF a] by auto
  have vos: "st_lookup (af_state st) ?v = OnStack"
    using A2 ne hd_in_set vV by (auto simp: AF_invar_2_def)
  have scan: "af_scanned st a" using af_scanned_of_exhausted[OF mii a inc nho nhi] .
  have amem: "a \<in> set (af_estack st)"
    using sr vos vV a scan inc free farnf by (auto simp: af_scanres_def)
  have "a = hd (af_estack st)" using af_estack_incident_hd[OF A2 A3 amem ne inc] .
  moreover have "af_estack st \<noteq> []" using amem by auto
  ultimately show ?thesis by simp
qed

text \<open>Hence the pop preserves J', stamping the finished vertex with the current clock.\<close>

lemma af_rankok_upd3:
  assumes inv: "AF_inv st" and conds: "AF_DFS_call_3_conds st"
    and ok: "af_rankok st rk" and sr: "af_scanres st"
    and vrank: "\<And>u. u \<in> \<V> \<Longrightarrow> st_lookup (af_state st) u = Finished \<Longrightarrow> rk u < (c :: nat)"
  shows "af_rankok (AF_DFS_upd3 st) (rk(hd (af_vstack st) := c))"
proof -
  let ?v = "hd (af_vstack st)"
  from inv have i1: "AF_invar_1 st" and i2: "AF_invar_2 st" and i3: "AF_invar_3 st"
    and iit: "AF_invar_iter st" by (auto simp: AF_inv_def)
  have si: "st_invar (af_state st)" using i1 by (simp add: AF_invar_1_def)
  have mii: "multigraph_inv (af_out_arr st) (af_in_arr st)" using iit by (simp add: AF_invar_iter_def)
  from conds have ne: "af_vstack st \<noteq> []" by (auto elim!: call_cond_elims)
  have vin: "?v \<in> set (af_vstack st)" using hd_in_set[OF ne] .
  have vV: "?v \<in> \<V>" using inv vin by (auto simp: AF_inv_def AF_invar_V_def)
  have vos: "st_lookup (af_state st) ?v = OnStack" using i2 vin vV by (auto simp: AF_invar_2_def)
  have vfin: "st_lookup (af_state st) ?v \<noteq> Finished" using vos by simp
  have res: "\<And>a. a \<in> \<E> \<Longrightarrow> af_arc_free (af_flow st) a \<Longrightarrow> ?v \<in> {fst a, snd a}
               \<Longrightarrow> st_lookup (af_state st) (if fst a = ?v then snd a else fst a) \<noteq> Finished
               \<Longrightarrow> af_estack st \<noteq> [] \<and> a = hd (af_estack st)"
    using af_scanres_res[OF sr conds mii i2 i3] by blast
  show ?thesis
    unfolding AF_DFS_upd3_def
    using af_rankok_pop[OF ok si vV vfin vrank res] .
qed

text \<open>Preservation of the scan-resolution invariant K (@{const af_scanres}). The pop is the tractable
      case: the popped vertex's edge @{term \<open>hd (af_estack st)\<close>} (incident to it) leaves the trail, but any
      surviving scanned free arc of another on-stack vertex whose far end is not finished cannot be that
      edge (its far end would be the just-finished vertex), so it lies in the tail of the trail.\<close>

lemma af_hd_estack_incident_hd_vstack:
  assumes A2: "AF_invar_2 st" and A3: "AF_invar_3 st" and estne: "af_estack st \<noteq> []"
  shows "hd (af_vstack st) \<in> {fst (hd (af_estack st)), snd (hd (af_estack st))}"
proof -
  have vne: "af_vstack st \<noteq> []" using A2 estne by (auto simp: AF_invar_2_def)
  have z: "0 < length (af_estack st)" using estne by simp
  have "(if af_dstack st ! 0 then snd (af_estack st ! 0) else fst (af_estack st ! 0)) = af_vstack st ! 0"
    using A3 z by (auto simp: AF_invar_3_def)
  hence "af_vstack st ! 0 \<in> {fst (af_estack st ! 0), snd (af_estack st ! 0)}"
    by (auto split: if_splits)
  thus ?thesis using hd_conv_nth[OF vne] hd_conv_nth[OF estne] by simp
qed

lemma af_scanres_upd3:
  assumes inv: "AF_inv st" and conds: "AF_DFS_call_3_conds st" and sr: "af_scanres st"
  shows "af_scanres (AF_DFS_upd3 st)"
proof (unfold af_scanres_def, intro ballI allI impI)
  let ?v0 = "hd (af_vstack st)"
  fix v a
  assume vV: "v \<in> \<V>" and vos': "st_lookup (af_state (AF_DFS_upd3 st)) v = OnStack"
    and a: "a \<in> \<E>" and scan': "af_scanned (AF_DFS_upd3 st) a"
    and inc: "v \<in> {fst a, snd a}" and free': "af_arc_free (af_flow (AF_DFS_upd3 st)) a"
    and farnf': "st_lookup (af_state (AF_DFS_upd3 st)) (if fst a = v then snd a else fst a) \<noteq> Finished"
  from inv have i1: "AF_invar_1 st" and i2: "AF_invar_2 st" and i3: "AF_invar_3 st"
    and iV: "AF_invar_V st" by (auto simp: AF_inv_def)
  have si: "st_invar (af_state st)" using i1 by (simp add: AF_invar_1_def)
  have ne: "af_vstack st \<noteq> []" using conds by (auto elim!: call_cond_elims)
  have hV: "?v0 \<in> \<V>" using iV ne hd_in_set by (auto simp: AF_invar_V_def)
  have lk: "\<And>w. st_lookup (af_state (AF_DFS_upd3 st)) w = (if w = ?v0 then Finished else st_lookup (af_state st) w)"
    using si by (simp add: AF_DFS_upd3_def state_arr.fixed_univ_map_upd[OF si hV])
  have vnv0: "v \<noteq> ?v0" and vos: "st_lookup (af_state st) v = OnStack" using vos' lk by (auto split: if_splits)
  have scan: "af_scanned st a" using scan' by (simp add: AF_DFS_upd3_def af_scanned_def)
  have free: "af_arc_free (af_flow st) a" using free' by (simp add: AF_DFS_upd3_def)
  let ?far = "if fst a = v then snd a else fst a"
  have farnv0: "?far \<noteq> ?v0" and farnf: "st_lookup (af_state st) ?far \<noteq> Finished"
    using farnf' lk by (auto split: if_splits)
  have amem: "a \<in> set (af_estack st)" using sr vos vV a scan inc free farnf by (auto simp: af_scanres_def)
  have estne: "af_estack st \<noteq> []" using amem by auto
  have ah_ne: "a \<noteq> hd (af_estack st)"
  proof
    assume ah: "a = hd (af_estack st)"
    have "?v0 \<in> {fst a, snd a}" using af_hd_estack_incident_hd_vstack[OF i2 i3 estne] ah by simp
    hence "?far = ?v0" using inc vnv0 by (auto split: if_splits)
    thus False using farnv0 by simp
  qed
  have "a \<in> set (tl (af_estack st))"
  proof (cases "af_estack st")
    case Nil thus ?thesis using estne by simp
  next
    case (Cons x xs) thus ?thesis using amem ah_ne by auto
  qed
  thus "a \<in> set (af_estack (AF_DFS_upd3 st))" by (simp add: AF_DFS_upd3_def)
qed

subsection \<open>Pristine (unseen) vertices carry no scanned arc\<close>

text \<open>A vertex only leaves the @{term Unseen} state by being pushed, and only re-enters it through a
      reset that simultaneously restores its pristine iterators (@{const af_reset}); the running top,
      whose iterator advances, is always @{term OnStack}. Hence every @{term Unseen} vertex has an
      empty iterated set --- no incident arc has yet been scanned through it. Consequently a scanned
      arc always has at least one endpoint that is \emph{not} unseen, which rules out the otherwise
      problematic case of a freshly pushed vertex acquiring a scanned free arc to a still-unseen one.\<close>

definition "af_pristine1 st \<longleftrightarrow>
  (\<forall>v\<in>\<V>. st_lookup (af_state st) v = Unseen \<longrightarrow>
       out_iterated (af_out_arr st) v = {} \<and>
       in_iterated (af_in_arr st) v = {})"

text \<open>The full pristine invariant folds in a second clause: no \emph{free scanned} arc is a self-loop.
      A self-loop is cancelled (saturated) the instant it is scanned (@{const af_handle}'s self-loop
      branch), so it never survives as a free scanned arc; freeness is anti-monotone
      (@{thm [source] af_free_mono_upd1}) so old ones stay dead. This is what lets the forest argument
      exclude a self-loop cycle edge at the minimum-rank vertex. Its preservation needs the
      scan-subsumption lemmas below, so the combined invariant and its preservation lemmas are stated
      later; @{const af_pristine1} carries the transient-free first clause used by the scan machinery.\<close>

definition "af_pristine st \<longleftrightarrow>
  af_pristine1 st \<and>
  (\<forall>a. af_scanned st a \<longrightarrow> af_arc_free (af_flow st) a \<longrightarrow> fst a \<noteq> snd a) \<and>
  (\<forall>a. af_scanned st a \<longrightarrow> fst a = snd a \<longrightarrow>
       (0 \<le> \<c> a \<longrightarrow> flow_lookup (af_flow st) a = 0)
     \<and> (\<c> a < 0 \<longrightarrow> flow_lookup (af_flow st) a = cap a))"

lemma af_pristine_imp1: "af_pristine st \<Longrightarrow> af_pristine1 st"
  by (simp add: af_pristine_def)

lemma af_pristine1_scanned_seen:
  assumes pr: "af_pristine1 st" and sc: "af_scanned st a" and aE: "a \<in> \<E>"
  shows "st_lookup (af_state st) (fst a) \<noteq> Unseen \<or> st_lookup (af_state st) (snd a) \<noteq> Unseen"
proof -
  have fV: "fst a \<in> \<V>" using fst_E_V[OF aE] .
  have sV: "snd a \<in> \<V>" using snd_E_V[OF aE] .
  from sc have "a \<in> out_iterated (af_out_arr st) (fst a) \<or>
                a \<in> in_iterated (af_in_arr st) (snd a)"
    by (simp add: af_scanned_def)
  thus ?thesis
  proof
    assume "a \<in> out_iterated (af_out_arr st) (fst a)"
    hence "out_iterated (af_out_arr st) (fst a) \<noteq> {}" by auto
    thus ?thesis using pr fV by (auto simp: af_pristine1_def)
  next
    assume "a \<in> in_iterated (af_in_arr st) (snd a)"
    hence "in_iterated (af_in_arr st) (snd a) \<noteq> {}" by auto
    thus ?thesis using pr sV by (auto simp: af_pristine1_def)
  qed
qed

text \<open>A truncation reset restores the two edge iterators of each \emph{dropped} vertex to their
      pristine (global) state, so its iterated set becomes empty (via @{term fresh}).\<close>

lemma af_reset_unsee_seg_out_pristine:
  assumes "out_invar (af_out_arr st)" and "distinct vs" and "w \<in> set (take n vs)" and "set vs \<subseteq> \<V>"
  shows "out_iterated (af_out_arr (af_reset_unsee_seg n vs st)) w = {}"
  using assms
proof (induction n vs st rule: af_reset_unsee_seg.induct)
  case (1 n v vs st)
  let ?st1 = "af_reset v (st\<lparr>af_state := st_upd (af_state st) v Unseen\<rparr>)"
  have vV: "v \<in> \<V>" and vsV: "set vs \<subseteq> \<V>" using 1(5) by auto
  have ai1: "out_invar (af_out_arr ?st1)" using 1(2) vV by (simp add: af_reset_def out_reset_invar)
  show ?case
  proof (cases "w = v")
    case True
    have vnvs: "v \<notin> set (take n vs)" using 1(3) by (meson distinct.simps(2) in_set_takeD)
    have z: "out_iterated (af_out_arr ?st1) v = {}"
      using vV by (simp add: af_reset_def outg.idx_reset_iterated[OF 1(2)])
    have "out_iterated (af_out_arr (af_reset_unsee_seg n vs ?st1)) v = out_iterated (af_out_arr ?st1) v"
      using af_reset_unsee_seg_out_lookup[OF ai1 vnvs vsV] by simp
    thus ?thesis using z True by simp
  next
    case False
    have wtake: "w \<in> set (take n vs)" using 1(4) False by (simp add: take_Suc_Cons)
    have dvs: "distinct vs" using 1(3) by simp
    show ?thesis using 1(1)[OF ai1 dvs wtake vsV] by simp
  qed
qed simp_all

lemma af_reset_unsee_seg_in_pristine:
  assumes "in_invar (af_in_arr st)" and "distinct vs" and "w \<in> set (take n vs)" and "set vs \<subseteq> \<V>"
  shows "in_iterated (af_in_arr (af_reset_unsee_seg n vs st)) w = {}"
  using assms
proof (induction n vs st rule: af_reset_unsee_seg.induct)
  case (1 n v vs st)
  let ?st1 = "af_reset v (st\<lparr>af_state := st_upd (af_state st) v Unseen\<rparr>)"
  have vV: "v \<in> \<V>" and vsV: "set vs \<subseteq> \<V>" using 1(5) by auto
  have ai1: "in_invar (af_in_arr ?st1)" using 1(2) vV by (simp add: af_reset_def in_reset_invar)
  show ?case
  proof (cases "w = v")
    case True
    have vnvs: "v \<notin> set (take n vs)" using 1(3) by (meson distinct.simps(2) in_set_takeD)
    have z: "in_iterated (af_in_arr ?st1) v = {}"
      using vV by (simp add: af_reset_def ing.idx_reset_iterated[OF 1(2)])
    have "in_iterated (af_in_arr (af_reset_unsee_seg n vs ?st1)) v = in_iterated (af_in_arr ?st1) v"
      using af_reset_unsee_seg_in_lookup[OF ai1 vnvs vsV] by simp
    thus ?thesis using z True by simp
  next
    case False
    have wtake: "w \<in> set (take n vs)" using 1(4) False by (simp add: take_Suc_Cons)
    have dvs: "distinct vs" using 1(3) by simp
    show ?thesis using 1(1)[OF ai1 dvs wtake vsV] by simp
  qed
qed simp_all

text \<open>The pop leaves the iterators untouched and only finishes a vertex, so it preserves
      @{const af_pristine} outright.\<close>

lemma af_pristine1_upd3:
  assumes inv: "AF_inv st" and conds: "AF_DFS_call_3_conds st" and pr: "af_pristine1 st"
  shows "af_pristine1 (AF_DFS_upd3 st)"
proof (unfold af_pristine1_def, intro ballI impI)
  fix v assume vV: "v \<in> \<V>" and un: "st_lookup (af_state (AF_DFS_upd3 st)) v = Unseen"
  from inv have i1: "AF_invar_1 st" and iV: "AF_invar_V st" by (auto simp: AF_inv_def)
  have si: "st_invar (af_state st)" using i1 by (simp add: AF_invar_1_def)
  have ne: "af_vstack st \<noteq> []" using conds by (auto elim!: call_cond_elims)
  have hV: "hd (af_vstack st) \<in> \<V>" using iV ne hd_in_set by (auto simp: AF_invar_V_def)
  have lk: "st_lookup (af_state (AF_DFS_upd3 st)) v =
              (if v = hd (af_vstack st) then Finished else st_lookup (af_state st) v)"
    using si by (simp add: AF_DFS_upd3_def state_arr.fixed_univ_map_upd[OF si hV])
  have "st_lookup (af_state st) v = Unseen" using un lk by (auto split: if_splits)
  hence "out_iterated (af_out_arr st) v = {} \<and>
         in_iterated (af_in_arr st) v = {}"
    using pr vV by (simp add: af_pristine1_def)
  thus "out_iterated (af_out_arr (AF_DFS_upd3 st)) v = {} \<and>
        in_iterated (af_in_arr (AF_DFS_upd3 st)) v = {}"
    by (simp add: AF_DFS_upd3_def)
qed

text \<open>@{const af_handle} preserves @{const af_pristine}. Every branch either leaves the iterators
      intact while only advancing the state (blocked, self-loop, skips, push), or --- on a back-edge
      cancellation --- resets the dropped vertices, whose iterators become pristine (empty iterated,
      via @{term fresh}) exactly as they are re-marked @{term Unseen}.\<close>

lemma af_handle_pristine1:
  assumes A1: "AF_invar_1 st" and A2: "AF_invar_2 st" and ae: "a \<in> \<E>" and AV: "AF_invar_V st"
    and fresh: "\<forall>u. out_iterated out_arr u = {} \<and> in_iterated in_arr u = {}"
    and pr: "af_pristine1 st"
  shows "af_pristine1 (af_handle st a dir)"
proof (unfold af_pristine1_def, intro ballI impI)
  fix v assume vV: "v \<in> \<V>" and un: "st_lookup (af_state (af_handle st a dir)) v = Unseen"
  have si: "st_invar (af_state st)" using A1 by (simp add: AF_invar_1_def)
  have aio: "out_invar (af_out_arr st)" using A1 by (simp add: AF_invar_1_def)
  have aii: "in_invar (af_in_arr st)" using A1 by (simp add: AF_invar_1_def)
  have dvs: "distinct (af_vstack st)" using A2 by (simp add: AF_invar_2_def)
  obtain up dn where updn: "af_rooms (af_flow st) a = (up, dn)" by (cases "af_rooms (af_flow st) a") auto
  show "out_iterated (af_out_arr (af_handle st a dir)) v = {} \<and>
        in_iterated (af_in_arr (af_handle st a dir)) v = {}"
  proof (cases "fst_exec a = snd_exec a")
    case True
    have "af_handle st a dir = af_selfloop_handle st a" using True by (simp add: af_handle_def)
    thus ?thesis using un pr vV by (simp add: af_pristine1_def)
  next
    case selfloop: False
    show ?thesis
    proof (cases "0 < dn \<and> (up = - 1 \<or> 0 < up)")
      case False
      hence "af_handle st a dir = st" using updn selfloop by (simp add: af_handle_def Let_def)
      thus ?thesis using un pr vV by (simp add: af_pristine1_def)
    next
      case guard: True
      show ?thesis
      proof (cases "af_estack st \<noteq> [] \<and> a = hd (af_estack st)")
        case True
        hence "af_handle st a dir = st" using updn guard selfloop by (simp add: af_handle_def Let_def)
        thus ?thesis using un pr vV by (simp add: af_pristine1_def)
      next
        case parent: False
        show ?thesis
        proof (cases "st_lookup (af_state st) (if dir then snd_exec a else fst_exec a)")
          case Unseen
          have cV: "(if dir then snd_exec a else fst_exec a) \<in> \<V>"
            using ae fst_E_V[OF ae] snd_E_V[OF ae] by (cases dir) (auto simp: snd_exec_eq[OF ae] fst_exec_eq[OF ae])
          have h: "af_handle st a dir = st\<lparr>af_vstack := (if dir then snd_exec a else fst_exec a) # af_vstack st,
                     af_state := st_upd (af_state st) (if dir then snd_exec a else fst_exec a) OnStack,
                     af_estack := a # af_estack st, af_dstack := dir # af_dstack st\<rparr>"
            using updn guard selfloop parent Unseen by (auto simp: af_handle_def Let_def)
          have io: "af_out_arr (af_handle st a dir) = af_out_arr st \<and> af_in_arr (af_handle st a dir) = af_in_arr st"
            using h by simp
          have "st_lookup (af_state (af_handle st a dir)) v =
                  (if v = (if dir then snd_exec a else fst_exec a) then OnStack else st_lookup (af_state st) v)"
            using h si by (simp add: state_arr.fixed_univ_map_upd[OF si cV])
          hence "st_lookup (af_state st) v = Unseen" using un by (auto split: if_splits)
          thus ?thesis using io pr vV by (auto simp: af_pristine1_def)
        next
          case OnStack
          obtain fl m' ubd where c: "af_cancel_seg up dn (if dir then snd_exec a else fst_exec a)
              (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) = (fl, m', ubd)"
            by (cases "af_cancel_seg up dn (if dir then snd_exec a else fst_exec a) (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st)") auto
          show ?thesis
          proof (cases ubd)
            case True
            hence "af_handle st a dir = st\<lparr>af_unbounded := True\<rparr>"
              using updn guard selfloop parent OnStack c by (auto simp: af_handle_def Let_def)
            thus ?thesis using un pr vV by (simp add: af_pristine1_def)
          next
            case ubdF: False
            let ?dst = "st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st),
                    af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>"
            have red: "af_handle st a dir = af_reset_unsee_seg m' (af_vstack st) ?dst"
              using updn guard selfloop parent OnStack c ubdF by (auto simp: af_handle_def Let_def)
            have sid: "st_invar (af_state ?dst)" using si by simp
            have aiod: "out_invar (af_out_arr ?dst)" using aio by simp
            have aiid: "in_invar (af_in_arr ?dst)" using aii by simp
            have vsV: "set (af_vstack st) \<subseteq> \<V>" using AV by (simp add: AF_invar_V_def)
            have stlk: "st_lookup (af_state (af_handle st a dir)) v =
                          (if v \<in> set (take m' (af_vstack st)) then Unseen else st_lookup (af_state st) v)"
              using red af_reset_unsee_seg_state[OF vsV sid, of m' v] by simp
            show ?thesis
            proof (cases "v \<in> set (take m' (af_vstack st))")
              case invv: True
              have "out_iterated (af_out_arr (af_handle st a dir)) v = {}"
                using red af_reset_unsee_seg_out_pristine[OF aiod dvs invv vsV] by simp
              moreover have "in_iterated (af_in_arr (af_handle st a dir)) v = {}"
                using red af_reset_unsee_seg_in_pristine[OF aiid dvs invv vsV] by simp
              ultimately show ?thesis by simp
            next
              case notin: False
              have vun: "st_lookup (af_state st) v = Unseen" using un stlk notin by simp
              have "out_iterated (af_out_arr (af_handle st a dir)) v = out_iterated (af_out_arr st) v"
                using red af_reset_unsee_seg_out_lookup[OF aiod notin vsV] by simp
              moreover have "in_iterated (af_in_arr (af_handle st a dir)) v = in_iterated (af_in_arr st) v"
                using red af_reset_unsee_seg_in_lookup[OF aiid notin vsV] by simp
              ultimately show ?thesis using vun pr vV by (simp add: af_pristine1_def)
            qed
          qed
        next
          case Finished
          hence "af_handle st a dir = st" using updn guard selfloop parent by (simp add: af_handle_def Let_def)
          thus ?thesis using un pr vV by (simp add: af_pristine1_def)
        qed
      qed
    qed
  qed
qed

text \<open>Hence the two advancing update branches preserve @{const af_pristine1}: an advance touches only
      the on-stack top's iterator, and @{const af_handle} preserves it by the lemma above.\<close>

lemma af_pristine1_upd1:
  assumes inv: "AF_inv st" and c: "AF_DFS_call_1_conds st"
    and fresh: "\<forall>u. out_iterated out_arr u = {} \<and> in_iterated in_arr u = {}"
    and pr: "af_pristine1 st"
  shows "af_pristine1 (AF_DFS_upd1 st)"
proof -
  from inv have i1: "AF_invar_1 st" and i2: "AF_invar_2 st" by (auto simp: AF_inv_def)
  from c have ne: "af_vstack st \<noteq> []" by (auto elim!: call_cond_elims)
  let ?top = "hd (af_vstack st)"
  let ?st' = "st\<lparr>af_out_arr := out_move (af_out_arr st) ?top\<rparr>"
  have aio: "out_invar (af_out_arr st)" using i1 by (simp add: AF_invar_1_def)
  have topV: "?top \<in> \<V>" using inv ne hd_in_set by (auto simp: AF_inv_def AF_invar_V_def)
  have topos: "st_lookup (af_state st) ?top = OnStack" using i2 ne hd_in_set topV by (auto simp: AF_invar_2_def)
  have he: "out_has (af_out_arr st) ?top" using c by (auto elim!: call_cond_elims)
  have rem: "out_remaining (af_out_arr st) ?top \<noteq> {}" using he by (simp add: outg.idx_has[OF aio topV])
  have pr': "af_pristine1 ?st'"
  proof (unfold af_pristine1_def, intro ballI impI)
    fix v assume vV: "v \<in> \<V>" and "st_lookup (af_state ?st') v = Unseen"
    hence vun: "st_lookup (af_state st) v = Unseen" by simp
    hence vnt: "v \<noteq> ?top" using topos by auto
    have "out_iterated (af_out_arr ?st') v = out_iterated (af_out_arr st) v"
      using outg.idx_move_iterated_other[OF aio topV rem vnt] by simp
    thus "out_iterated (af_out_arr ?st') v = {} \<and>
          in_iterated (af_in_arr ?st') v = {}"
      using vun pr vV by (simp add: af_pristine1_def)
  qed
  have vtop: "?top \<in> \<V>" using inv ne hd_in_set by (auto simp: AF_inv_def AF_invar_V_def)
  have mi': "multigraph_inv (af_out_arr st) (af_in_arr st)" using inv by (simp add: AF_inv_def AF_invar_iter_def)
  have ae: "out_current (af_out_arr st) ?top \<in> \<E>" using af_current_out_endpoint[OF mi' vtop he] by simp
  have AV': "AF_invar_V ?st'" using inv by (simp add: AF_inv_def AF_invar_V_def)
  have i1': "AF_invar_1 ?st'" using AF_invar_1_out_advance[OF vtop i1] .
  have i2': "AF_invar_2 ?st'" using i2 by (simp add: AF_invar_2_def)
  have "af_pristine1 (af_handle ?st' (out_current (af_out_arr st) ?top) True)"
    using af_handle_pristine1[OF i1' i2' ae AV' fresh pr'] .
  thus ?thesis by (simp add: AF_DFS_upd1_def Let_def)
qed

lemma af_pristine1_upd2:
  assumes inv: "AF_inv st" and c: "AF_DFS_call_2_conds st"
    and fresh: "\<forall>u. out_iterated out_arr u = {} \<and> in_iterated in_arr u = {}"
    and pr: "af_pristine1 st"
  shows "af_pristine1 (AF_DFS_upd2 st)"
proof -
  from inv have i1: "AF_invar_1 st" and i2: "AF_invar_2 st" by (auto simp: AF_inv_def)
  from c have ne: "af_vstack st \<noteq> []" by (auto elim!: call_cond_elims)
  let ?top = "hd (af_vstack st)"
  let ?st' = "st\<lparr>af_in_arr := in_move (af_in_arr st) ?top\<rparr>"
  have aii: "in_invar (af_in_arr st)" using i1 by (simp add: AF_invar_1_def)
  have topV: "?top \<in> \<V>" using inv ne hd_in_set by (auto simp: AF_inv_def AF_invar_V_def)
  have topos: "st_lookup (af_state st) ?top = OnStack" using i2 ne hd_in_set topV by (auto simp: AF_invar_2_def)
  have he: "in_has (af_in_arr st) ?top" using c by (auto elim!: call_cond_elims)
  have rem: "in_remaining (af_in_arr st) ?top \<noteq> {}" using he by (simp add: ing.idx_has[OF aii topV])
  have pr': "af_pristine1 ?st'"
  proof (unfold af_pristine1_def, intro ballI impI)
    fix v assume vV: "v \<in> \<V>" and "st_lookup (af_state ?st') v = Unseen"
    hence vun: "st_lookup (af_state st) v = Unseen" by simp
    hence vnt: "v \<noteq> ?top" using topos by auto
    have "in_iterated (af_in_arr ?st') v = in_iterated (af_in_arr st) v"
      using ing.idx_move_iterated_other[OF aii topV rem vnt] by simp
    thus "out_iterated (af_out_arr ?st') v = {} \<and>
          in_iterated (af_in_arr ?st') v = {}"
      using vun pr vV by (simp add: af_pristine1_def)
  qed
  have vtop: "?top \<in> \<V>" using inv ne hd_in_set by (auto simp: AF_inv_def AF_invar_V_def)
  have mi': "multigraph_inv (af_out_arr st) (af_in_arr st)" using inv by (simp add: AF_inv_def AF_invar_iter_def)
  have ae: "in_current (af_in_arr st) ?top \<in> \<E>" using af_current_in_endpoint[OF mi' vtop he] by simp
  have AV': "AF_invar_V ?st'" using inv by (simp add: AF_inv_def AF_invar_V_def)
  have i1': "AF_invar_1 ?st'" using AF_invar_1_in_advance[OF vtop i1] .
  have i2': "AF_invar_2 ?st'" using i2 by (simp add: AF_invar_2_def)
  have "af_pristine1 (af_handle ?st' (in_current (af_in_arr st) ?top) False)"
    using af_handle_pristine1[OF i1' i2' ae AV' fresh pr'] .
  thus ?thesis by (simp add: AF_DFS_upd2_def Let_def)
qed

subsection \<open>A length-one (self-loop) cancellation saturates its arc\<close>

text \<open>A self-loop is cancelled on sight with an empty segment: @{const af_scan} and @{const af_push}
      both hit their base equations, leaving a single @{const af_push_arc} that drives the arc's flow to
      @{term 0} (draining the defect) or to its capacity (filling it) --- either way the arc is no longer
      free. This kills the would-be free scanned self-loop incident to the top vertex (a self-loop is
      never a trail arc).\<close>

lemma af_cancel_seg_selfloop_notfree:
  assumes fi: "flow_invar fl" and ain: "a \<in> \<E>"
    and updn: "af_rooms fl a = (up, dn)"
    and cs: "af_cancel_seg up dn (fst a) [] [] [] a True fl = (fl', m', ubd)"
    and nub: "\<not> ubd"
  shows "\<not> af_arc_free fl' a"
proof -
  have f: "flow_lookup fl a = dn" and up_val: "up = (if cap a = - 1 then - 1 else cap a - dn)"
    using updn by (auto simp: af_rooms_def Let_def)
  let ?k = "af_delta_cost a True"
  let ?flip = "0 < ?k"
  let ?ga = "if ?flip then dn else up"
  consider (fin) "?ga \<noteq> - 1" | (sw) "\<not> ?ga \<noteq> - 1" "?k = 0 \<and> dn \<noteq> - 1"
    | (ub) "\<not> ?ga \<noteq> - 1" "\<not> (?k = 0 \<and> dn \<noteq> - 1)" by blast
  then show ?thesis
  proof cases
    case fin
    obtain fl2 f2 where pa: "af_push_arc ?ga a (True \<noteq> ?flip) fl = (fl2, f2)" by fastforce
    have fl'eq: "fl' = fl2" using cs updn fin pa by (auto simp: af_cancel_seg_def Let_def)
    have f2v: "f2 = dn + (if True \<noteq> ?flip then ?ga else - ?ga)"
      using af_push_arc_at[OF ain fi pa] f by simp
    have "af_saturated f2 a"
    proof (cases ?flip)
      case True
      hence "f2 = 0" using f2v by simp
      thus ?thesis by (simp add: af_saturated_def)
    next
      case False
      hence "?ga = up" by simp
      hence "cap a \<noteq> - 1" using fin up_val by (auto split: if_splits)
      hence "f2 = cap a" using f2v False up_val by simp
      thus ?thesis by (simp add: af_saturated_def)
    qed
    thus ?thesis using af_saturated_notfree[OF ain fi pa] fl'eq by simp
  next
    case sw
    obtain fl2 f2 where pa: "af_push_arc dn a (True \<noteq> True) fl = (fl2, f2)" by fastforce
    have fl'eq: "fl' = fl2" using cs updn sw pa by (auto simp: af_cancel_seg_def Let_def)
    have "f2 = 0" using af_push_arc_at[OF ain fi pa] f by simp
    hence "af_saturated f2 a" by (simp add: af_saturated_def)
    thus ?thesis using af_saturated_notfree[OF ain fi pa] fl'eq by simp
  next
    case ub
    have "ubd" using cs updn ub by (auto simp: af_cancel_seg_def Let_def)
    thus ?thesis using nub by simp
  qed
qed

subsection \<open>A bottleneck-only cancellation saturates its closing arc\<close>

text \<open>Seed preservation: when a cancellation truncates \emph{no} walked arc (@{term \<open>m' = 0\<close>}), the
      chosen bottleneck @{term \<gamma>} coincides with its scan \emph{seed} --- no walked arc tightened it.
      The step: @{term \<open>m' = 0\<close>} forces the first walked arc \emph{not} to saturate, i.e.\ @{term \<gamma>}
      differs from that arc's push-room, so the @{const af_min} against it keeps the seed. (@{const af_min}
      always returns one of its two arguments, so this is unconditional.)\<close>

text \<open>Hence a bottleneck-only cancellation (@{term \<open>m' = 0\<close>}, no truncation) saturates its closing
      arc: the pushed amount equals that arc's push-room, driving its flow to a boundary.\<close>

text \<open>A truncation reset only \emph{removes} scanned arcs: a dropped vertex's iterators become pristine
      (empty iterated, via @{term fresh}), so any arc scanned after the reset was already scanned before.
      This is the @{const af_scanned} monotonicity the back-edge case of the scan-resolution invariant
      needs for arcs other than the closing one.\<close>

lemma af_reset_unsee_seg_scanned_sub:
  assumes ao: "out_invar (af_out_arr st)" and ai: "in_invar (af_in_arr st)"
    and dvs: "distinct vs" and vsV: "set vs \<subseteq> \<V>"
    and fresh: "\<forall>u. out_iterated out_arr u = {} \<and> in_iterated in_arr u = {}"
    and sc: "af_scanned (af_reset_unsee_seg n vs st) b"
  shows "af_scanned st b"
proof -
  from sc consider (out) "b \<in> out_iterated (af_out_arr (af_reset_unsee_seg n vs st)) (fst b)"
    | (inn) "b \<in> in_iterated (af_in_arr (af_reset_unsee_seg n vs st)) (snd b)"
    by (auto simp: af_scanned_def)
  thus ?thesis
  proof cases
    case out
    show ?thesis
    proof (cases "fst b \<in> set (take n vs)")
      case True
      have "out_iterated (af_out_arr (af_reset_unsee_seg n vs st)) (fst b) = {}"
        using af_reset_unsee_seg_out_pristine[OF ao dvs True vsV] .
      thus ?thesis using out by simp
    next
      case False
      have "out_iterated (af_out_arr (af_reset_unsee_seg n vs st)) (fst b) = out_iterated (af_out_arr st) (fst b)"
        using af_reset_unsee_seg_out_lookup[OF ao False vsV] by simp
      thus ?thesis using out by (simp add: af_scanned_def)
    qed
  next
    case inn
    show ?thesis
    proof (cases "snd b \<in> set (take n vs)")
      case True
      have "in_iterated (af_in_arr (af_reset_unsee_seg n vs st)) (snd b) = {}"
        using af_reset_unsee_seg_in_pristine[OF ai dvs True vsV] .
      thus ?thesis using inn by simp
    next
      case False
      have "in_iterated (af_in_arr (af_reset_unsee_seg n vs st)) (snd b) = in_iterated (af_in_arr st) (snd b)"
        using af_reset_unsee_seg_in_lookup[OF ai False vsV] by simp
      thus ?thesis using inn by (simp add: af_scanned_def)
    qed
  qed
qed

text \<open>@{const af_handle} only ever \emph{removes} scanned arcs: every branch bar the truncation reset
      leaves both edge arrays untouched, and the reset makes the dropped vertices pristine.\<close>

lemma af_handle_scanned_sub:
  assumes A1: "AF_invar_1 st" and A2: "AF_invar_2 st" and AV: "AF_invar_V st"
    and fresh: "\<forall>u. out_iterated out_arr u = {} \<and> in_iterated in_arr u = {}"
    and sc: "af_scanned (af_handle st a dir) b"
  shows "af_scanned st b"
proof -
  have si: "st_invar (af_state st)" using A1 by (simp add: AF_invar_1_def)
  have aio: "out_invar (af_out_arr st)" using A1 by (simp add: AF_invar_1_def)
  have aii: "in_invar (af_in_arr st)" using A1 by (simp add: AF_invar_1_def)
  have dvs: "distinct (af_vstack st)" using A2 by (simp add: AF_invar_2_def)
  have vsV: "set (af_vstack st) \<subseteq> \<V>" using AV by (simp add: AF_invar_V_def)
  obtain up dn where updn: "af_rooms (af_flow st) a = (up, dn)" by (cases "af_rooms (af_flow st) a") auto
  show ?thesis
  proof (cases "fst_exec a = snd_exec a")
    case True
    have "af_handle st a dir = af_selfloop_handle st a" using True by (simp add: af_handle_def)
    thus ?thesis using sc by (simp add: af_scanned_def)
  next
    case selfloop: False
    show ?thesis
    proof (cases "0 < dn \<and> (up = - 1 \<or> 0 < up)")
      case False
      hence "af_handle st a dir = st" using updn selfloop by (simp add: af_handle_def Let_def)
      thus ?thesis using sc by simp
    next
      case guard: True
      show ?thesis
      proof (cases "af_estack st \<noteq> [] \<and> a = hd (af_estack st)")
        case True
        hence "af_handle st a dir = st" using updn guard selfloop by (simp add: af_handle_def Let_def)
        thus ?thesis using sc by simp
      next
        case parent: False
        show ?thesis
        proof (cases "st_lookup (af_state st) (if dir then snd_exec a else fst_exec a)")
          case Unseen
          have io: "af_out_arr (af_handle st a dir) = af_out_arr st \<and> af_in_arr (af_handle st a dir) = af_in_arr st"
            using updn guard selfloop parent Unseen by (auto simp: af_handle_def Let_def)
          thus ?thesis using sc by (simp add: af_scanned_def)
        next
          case OnStack
          obtain fl m' ubd where c: "af_cancel_seg up dn (if dir then snd_exec a else fst_exec a)
              (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) = (fl, m', ubd)"
            by (metis prod_cases3)
          show ?thesis
          proof (cases ubd)
            case True
            have io: "af_out_arr (af_handle st a dir) = af_out_arr st \<and> af_in_arr (af_handle st a dir) = af_in_arr st"
              using updn guard selfloop parent OnStack c True by (auto simp: af_handle_def Let_def)
            thus ?thesis using sc by (simp add: af_scanned_def)
          next
            case ubdF: False
            let ?dst = "st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st),
                    af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>"
            have red: "af_handle st a dir = af_reset_unsee_seg m' (af_vstack st) ?dst"
              using updn guard selfloop parent OnStack c ubdF by (auto simp: af_handle_def Let_def)
            have aiod: "out_invar (af_out_arr ?dst)" using aio by simp
            have aiid: "in_invar (af_in_arr ?dst)" using aii by simp
            have "af_scanned (af_reset_unsee_seg m' (af_vstack st) ?dst) b" using sc red by simp
            hence "af_scanned ?dst b" using af_reset_unsee_seg_scanned_sub[OF aiod aiid dvs vsV fresh] by blast
            thus ?thesis by (simp add: af_scanned_def)
          qed
        next
          case Finished
          hence "af_handle st a dir = st" using updn guard selfloop parent by (simp add: af_handle_def Let_def)
          thus ?thesis using sc by simp
        qed
      qed
    qed
  qed
qed

text \<open>The scan-resolution invariant @{const af_scanres} is preserved by @{const af_handle} on the
      advanced state. The hypotheses model the state after the current arc @{term a} has been scanned:
      @{term srx} is @{const af_scanres} for every arc \emph{other} than @{term a}, and @{term sra} is
      the pre-scan resolution for @{term a} itself (used only to show that on a back-edge truncation the
      just-scanned arc is un-scanned by the reset of its near, dropped, endpoint). Every branch is
      discharged from the freeness/finished monotonicities, @{thm [source] af_pristine1_scanned_seen}
      (push into a fresh vertex), @{thm [source] af_backedge_boundary_dead}, and
      @{thm [source] af_handle_scanned_sub}.\<close>

lemma af_handle_af_scanres:
  assumes inv: "AF_inv st" and fresh: "\<forall>u. out_iterated out_arr u = {} \<and> in_iterated in_arr u = {}"
    and pr: "af_pristine1 st" and ae: "a \<in> \<E>"
    and near: "hd (af_vstack st) = (if dir then fst a else snd a)" and vne: "af_vstack st \<noteq> []"
    and nub: "\<not> af_unbounded (af_handle st a dir)"
    and srx: "\<And>u c. u \<in> \<V> \<Longrightarrow> st_lookup (af_state st) u = OnStack \<Longrightarrow> c \<in> \<E> \<Longrightarrow> c \<noteq> a \<Longrightarrow> af_scanned st c \<Longrightarrow>
                u \<in> {fst c, snd c} \<Longrightarrow> af_arc_free (af_flow st) c \<Longrightarrow>
                st_lookup (af_state st) (if fst c = u then snd c else fst c) \<noteq> Finished \<Longrightarrow> c \<in> set (af_estack st)"
    and sra: "st_lookup (af_state st) (if dir then snd a else fst a) = OnStack \<Longrightarrow> af_arc_free (af_flow st) a \<Longrightarrow>
              a \<notin> set (af_estack st) \<Longrightarrow>
              (if dir then a \<notin> in_iterated (af_in_arr st) (snd a)
               else a \<notin> out_iterated (af_out_arr st) (fst a))"
  shows "af_scanres (af_handle st a dir)"
proof (unfold af_scanres_def, intro ballI allI impI)
  fix v b
  assume vV: "v \<in> \<V>" and vos: "st_lookup (af_state (af_handle st a dir)) v = OnStack" and bE: "b \<in> \<E>"
    and bscan: "af_scanned (af_handle st a dir) b" and binc: "v \<in> {fst b, snd b}"
    and bfree: "af_arc_free (af_flow (af_handle st a dir)) b"
    and bfarnf: "st_lookup (af_state (af_handle st a dir)) (if fst b = v then snd b else fst b) \<noteq> Finished"
  from inv have i1: "AF_invar_1 st" and i2: "AF_invar_2 st" and i3: "AF_invar_3 st"
    and ife: "AF_invar_feas st" and ifr: "AF_invar_free st" and iestE: "AF_invar_estE st"
    and iV: "AF_invar_V st"
    by (auto simp: AF_inv_def)
  have vsV: "set (af_vstack st) \<subseteq> \<V>" using iV by (simp add: AF_invar_V_def)
  have fi: "flow_invar (af_flow st)" using i1 by (simp add: AF_invar_1_def)
  have si: "st_invar (af_state st)" using i1 by (simp add: AF_invar_1_def)
  have aio: "out_invar (af_out_arr st)" using i1 by (simp add: AF_invar_1_def)
  have aii: "in_invar (af_in_arr st)" using i1 by (simp add: AF_invar_1_def)
  have dvs: "distinct (af_vstack st)" using i2 by (simp add: AF_invar_2_def)
  have inc_a: "hd (af_vstack st) \<in> {fst a, snd a}" using near by (auto split: if_splits)
  obtain up dn where updn: "af_rooms (af_flow st) a = (up, dn)" by (cases "af_rooms (af_flow st) a") auto
  have feas_a: "cap a = - 1 \<or> flow_lookup (af_flow st) a \<le> cap a" using ife ae by (auto simp: AF_invar_feas_def af_cap_feasible_def)
  have gfree: "(0 < dn \<and> (up = - 1 \<or> 0 < up)) = af_arc_free (af_flow st) a" using af_guard_free[OF updn feas_a] .
  let ?far = "if fst b = v then snd b else fst b"
  have farst: "st_lookup (af_state st) ?far \<noteq> Finished" using af_handle_finished_mono[OF i1 i2 ae iV] bfarnf by metis
  show "b \<in> set (af_estack (af_handle st a dir))"
  proof (cases "b = a")
    case bna: False
    have scanst: "af_scanned st b" using af_handle_scanned_sub[OF i1 i2 iV fresh bscan] .
    have freest: "af_arc_free (af_flow st) b" using af_handle_free_mono[OF i1 ife ifr ae iestE bfree] .
    show ?thesis
    proof (cases "fst a = snd a")
      case selfl: True
      have h: "af_handle st a dir = af_selfloop_handle st a" using selfl by (simp add: af_handle_real[OF ae])
      have vst: "st_lookup (af_state st) v = OnStack" using vos h by simp
      have "b \<in> set (af_estack st)" using srx[OF vV vst bE bna scanst binc freest farst] .
      thus ?thesis using h by simp
    next
      case selfloop: False
      show ?thesis
      proof (cases "0 < dn \<and> (up = - 1 \<or> 0 < up)")
        case guardF: False
        hence h: "af_handle st a dir = st" using updn selfloop by (simp add: af_handle_real[OF ae] Let_def)
        have "b \<in> set (af_estack st)" using srx[OF vV _ bE bna scanst binc freest] vos farst h by auto
        thus ?thesis using h by simp
      next
        case guard: True
        show ?thesis
        proof (cases "af_estack st \<noteq> [] \<and> a = hd (af_estack st)")
          case parentT: True
          hence h: "af_handle st a dir = st"
            unfolding af_handle_real[OF ae] using updn guard selfloop by (simp add: Let_def)
          have "b \<in> set (af_estack st)" using srx[OF vV _ bE bna scanst binc freest] vos farst h by auto
          thus ?thesis using h by simp
        next
          case parent: False
          hence notpar: "af_estack st = [] \<or> a \<noteq> hd (af_estack st)" by auto
          let ?x = "if dir then snd a else fst a"
          show ?thesis
          proof (cases "st_lookup (af_state st) ?x")
            case Unseen
            have h: "af_handle st a dir = st\<lparr>af_vstack := ?x # af_vstack st, af_state := st_upd (af_state st) ?x OnStack,
                       af_estack := a # af_estack st, af_dstack := dir # af_dstack st\<rparr>"
              using updn guard selfloop parent Unseen by (auto simp: af_handle_real[OF ae] Let_def)
            have esh: "af_estack (af_handle st a dir) = a # af_estack st" using h by simp
            have xV: "?x \<in> \<V>" using ae fst_E_V[OF ae] snd_E_V[OF ae] by (cases dir) auto
            have vlk: "st_lookup (af_state (af_handle st a dir)) v = (if v = ?x then OnStack else st_lookup (af_state st) v)"
              using h si by (simp add: state_arr.fixed_univ_map_upd[OF si xV])
            show ?thesis
            proof (cases "v = ?x")
              case vx: True
              have vun: "st_lookup (af_state st) v = Unseen" using vx Unseen by simp
              have farnu: "st_lookup (af_state st) ?far \<noteq> Unseen"
                using af_pristine1_scanned_seen[OF pr scanst bE] binc vun by (auto split: if_splits)
              have ufar: "st_lookup (af_state st) ?far = OnStack" using farnu farst by (cases "st_lookup (af_state st) ?far") auto
              have farin: "?far \<in> {fst b, snd b}" using binc by (auto split: if_splits)
              have farv: "(if fst b = ?far then snd b else fst b) = v" using binc vx by (auto split: if_splits)
              have farV: "?far \<in> \<V>" using fst_E_V[OF bE] snd_E_V[OF bE] by (auto split: if_splits)
              have "b \<in> set (af_estack st)" using srx[OF farV ufar bE bna scanst farin freest] farv vun by simp
              thus ?thesis using esh by simp
            next
              case vnx: False
              have vst: "st_lookup (af_state st) v = OnStack" using vos vlk vnx by simp
              have "b \<in> set (af_estack st)" using srx[OF vV vst bE bna scanst binc freest farst] .
              thus ?thesis using esh by simp
            qed
          next
            case Finished
            hence h: "af_handle st a dir = st" using updn guard selfloop parent by (simp add: af_handle_real[OF ae] Let_def)
            have "b \<in> set (af_estack st)" using srx[OF vV _ bE bna scanst binc freest] vos farst h by auto
            thus ?thesis using h by simp
          next
            case OnStack
            obtain fl m' ub where c: "af_cancel_seg up dn ?x (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) = (fl, m', ub)"
              by (metis prod_cases3)
            have ubF: "\<not> ub" using nub updn guard selfloop parent OnStack c by (auto simp: af_handle_real[OF ae] Let_def)
            let ?dst = "st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st),
                    af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>"
            have h: "af_handle st a dir = af_reset_unsee_seg m' (af_vstack st) ?dst"
              using updn guard selfloop parent OnStack c ubF by (auto simp: af_handle_real[OF ae] Let_def)
            have flh: "af_flow (af_handle st a dir) = fl" using h by simp
            have esh: "af_estack (af_handle st a dir) = drop m' (af_estack st)" using h by simp
            have sid: "st_invar (af_state ?dst)" using si by simp
            have vlk: "st_lookup (af_state (af_handle st a dir)) v =
                        (if v \<in> set (take m' (af_vstack st)) then Unseen else st_lookup (af_state st) v)"
              using h af_reset_unsee_seg_state[OF vsV sid, of m' v] by simp
            have vnd: "v \<notin> set (take m' (af_vstack st))" and vst: "st_lookup (af_state st) v = OnStack"
              using vos vlk by (auto split: if_splits)
            have bmem: "b \<in> set (af_estack st)" using srx[OF vV vst bE bna scanst binc freest farst] .
            show ?thesis
            proof (cases "m' = 0")
              case True thus ?thesis using bmem esh by simp
            next
              case False
              hence mpos: "0 < m'" by simp
              have mle: "m' \<le> length (af_estack st)" using af_cancel_seg_drop_bound[OF c] .
              have len: "Suc (length (af_estack st)) = length (af_vstack st)" using i2 vne by (auto simp: AF_invar_2_def)
              have ltk: "length (take m' (af_vstack st)) = m'" using mle len by (simp add: min.absorb2)
              have ane: "a \<notin> set (af_estack st)" using af_closing_arc_not_on_trail[OF i2 i3 vne inc_a notpar] .
              have bnottake: "b \<notin> set (take m' (af_estack st))"
              proof
                assume "b \<in> set (take m' (af_estack st))"
                then obtain j where jl: "j < length (take m' (af_estack st))" and bj: "take m' (af_estack st) ! j = b"
                  by (meson in_set_conv_nth)
                have jm: "j < m'" using jl by simp
                have jle: "j < length (af_estack st)" using jl by simp
                have bej: "b = af_estack st ! j" using bj jm by (simp add: nth_take)
                have ends: "{fst b, snd b} = {af_vstack st ! j, af_vstack st ! Suc j}"
                  using trail_endpoints[OF i3 jle] bej by simp
                have jtake: "af_vstack st ! j \<in> set (take m' (af_vstack st))"
                  using jm ltk nth_take[of j m' "af_vstack st"] nth_mem[of j "take m' (af_vstack st)"] by simp
                have vsj: "v = af_vstack st ! Suc j" using binc ends vnd jtake by auto
                have sucm: "Suc j = m'"
                proof (rule ccontr)
                  assume "Suc j \<noteq> m'"
                  hence sm: "Suc j < m'" using jm by simp
                  hence "af_vstack st ! Suc j \<in> set (take m' (af_vstack st))"
                    using ltk nth_take[of "Suc j" m' "af_vstack st"] nth_mem[of "Suc j" "take m' (af_vstack st)"] by simp
                  thus False using vsj vnd by simp
                qed
                hence bnd: "b = af_estack st ! (m' - 1)" using bej by (metis diff_Suc_1)
                have "\<not> af_arc_free fl (af_estack st ! (m' - 1))"
                  using af_backedge_boundary_dead[OF fi i2 i3 iestE ae vne inc_a notpar c mpos] .
                thus False using bfree flh bnd by simp
              qed
              have "b \<in> set (drop m' (af_estack st))" using bmem bnottake
                by (metis append_take_drop_id set_append Un_iff)
              thus ?thesis using esh by simp
            qed
          qed
        qed
      qed
    qed
  next
    case ba: True
    show ?thesis
    proof (cases "fst a = snd a")
      case selfl: True
      have h: "af_handle st a dir = af_selfloop_handle st a" using selfl by (simp add: af_handle_real[OF ae])
      have "\<not> af_unbounded (af_selfloop_handle st a)" using nub h by simp
      hence "\<not> af_arc_free (af_flow (af_selfloop_handle st a)) a" using af_selfloop_handle_notfree[OF ae fi] by simp
      thus ?thesis using bfree ba h by simp
    next
      case selfloop: False
      show ?thesis
      proof (cases "0 < dn \<and> (up = - 1 \<or> 0 < up)")
        case guardF: False
        hence "\<not> af_arc_free (af_flow st) a" using gfree by simp
        moreover have "af_handle st a dir = st" using guardF updn selfloop by (simp add: af_handle_real[OF ae] Let_def)
        ultimately show ?thesis using bfree ba by simp
      next
        case guard: True
        show ?thesis
        proof (cases "af_estack st \<noteq> [] \<and> a = hd (af_estack st)")
          case parentT: True
          have amem: "a \<in> set (af_estack st)" using parentT by (metis hd_in_set)
          have h: "af_handle st a dir = st"
            unfolding af_handle_real[OF ae] using updn guard selfloop parentT by (simp add: Let_def)
          thus ?thesis using ba amem by simp
        next
          case parent: False
          hence notpar: "af_estack st = [] \<or> a \<noteq> hd (af_estack st)" by auto
          let ?x = "if dir then snd a else fst a"
          show ?thesis
          proof (cases "st_lookup (af_state st) ?x")
            case Unseen
            have "af_estack (af_handle st a dir) = a # af_estack st"
              using updn guard selfloop parent Unseen by (auto simp: af_handle_real[OF ae] Let_def)
            thus ?thesis using ba by simp
          next
            case Finished
            hence h: "af_handle st a dir = st" using updn guard selfloop parent by (simp add: af_handle_real[OF ae] Let_def)
            show ?thesis
            proof (cases "v = ?x")
              case True thus ?thesis using vos h Finished by simp
            next
              case vnx: False
              have "?far = ?x" using ba binc near vnx by (cases dir; auto split: if_splits)
              thus ?thesis using bfarnf h Finished by simp
            qed
          next
            case OnStack
            obtain fl m' ub where c: "af_cancel_seg up dn ?x (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) = (fl, m', ub)"
              by (metis prod_cases3)
            have ubF: "\<not> ub" using nub updn guard selfloop parent OnStack c by (auto simp: af_handle_real[OF ae] Let_def)
            let ?dst = "st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st),
                    af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>"
            have h: "af_handle st a dir = af_reset_unsee_seg m' (af_vstack st) ?dst"
              using updn guard selfloop parent OnStack c ubF by (auto simp: af_handle_real[OF ae] Let_def)
            have sid: "st_invar (af_state ?dst)" using si by simp
            have des: "distinct (af_estack st)" using estack_distinct[OF i2 i3] .
            have esE: "set (af_estack st) \<subseteq> \<E>" using iestE by (simp add: AF_invar_estE_def)
            have ane: "a \<notin> set (af_estack st)" using af_closing_arc_not_on_trail[OF i2 i3 vne inc_a notpar] .
            have afree: "af_arc_free (af_flow st) a" using guard gfree by simp
            have apre: "if dir then a \<notin> in_iterated (af_in_arr st) (snd a)
                        else a \<notin> out_iterated (af_out_arr st) (fst a)"
              using sra[OF OnStack afree ane] .
            have aio': "out_invar (af_out_arr ?dst)" using aio by simp
            have aii': "in_invar (af_in_arr ?dst)" using aii by simp
            have vlk: "st_lookup (af_state (af_handle st a dir)) v =
                        (if v \<in> set (take m' (af_vstack st)) then Unseen else st_lookup (af_state st) v)"
              using h af_reset_unsee_seg_state[OF vsV sid, of m' v] by simp
            have vnd: "v \<notin> set (take m' (af_vstack st))" using vos vlk by (auto split: if_splits)
            show ?thesis
            proof (cases "m' = 0")
              case True
              have c0: "af_cancel_seg up dn ?x (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) = (fl, 0, False)"
                using c True ubF by simp
              have "\<not> af_arc_free fl a" using af_cancel_seg_closing_sat_gen[OF fi des esE ae ane updn c0] .
              thus ?thesis using bfree ba h by simp
            next
              case False
              hence mpos: "0 < m'" by simp
              have mle: "m' \<le> length (af_estack st)" using af_cancel_seg_drop_bound[OF c] .
              have len: "Suc (length (af_estack st)) = length (af_vstack st)" using i2 vne by (auto simp: AF_invar_2_def)
              have ltk: "length (take m' (af_vstack st)) = m'" using mle len by (simp add: min.absorb2)
              have topdrop: "hd (af_vstack st) \<in> set (take m' (af_vstack st))"
              proof -
                have "af_vstack st ! 0 \<in> set (take m' (af_vstack st))"
                  using mpos ltk nth_take[of 0 m' "af_vstack st"] nth_mem[of 0 "take m' (af_vstack st)"] by simp
                thus ?thesis using hd_conv_nth[OF vne] by simp
              qed
              have vsurv: "v = ?x"
              proof -
                have "v \<noteq> hd (af_vstack st)" using vnd topdrop by auto
                thus ?thesis using ba binc near by (cases dir; auto)
              qed
              have notscan: "\<not> af_scanned (af_handle st a dir) a"
              proof
                assume "af_scanned (af_handle st a dir) a"
                hence sca: "af_scanned (af_reset_unsee_seg m' (af_vstack st) ?dst) a" using h by simp
                show False
                proof (cases dir)
                  case dT: True
                  have fstdrop: "fst a \<in> set (take m' (af_vstack st))" using near dT topdrop by simp
                  have noout: "a \<notin> out_iterated (af_out_arr (af_reset_unsee_seg m' (af_vstack st) ?dst)) (fst a)"
                    using af_reset_unsee_seg_out_pristine[OF aio' dvs fstdrop vsV] by simp
                  have sndnd: "snd a \<notin> set (take m' (af_vstack st))" using vsurv vnd dT by simp
                  have "in_iterated (af_in_arr (af_reset_unsee_seg m' (af_vstack st) ?dst)) (snd a) = in_iterated (af_in_arr st) (snd a)"
                    using af_reset_unsee_seg_in_lookup[OF aii' sndnd vsV] by simp
                  hence "a \<in> in_iterated (af_in_arr st) (snd a)" using sca noout by (auto simp: af_scanned_def)
                  thus False using apre dT by simp
                next
                  case dF: False
                  have snddrop: "snd a \<in> set (take m' (af_vstack st))" using near dF topdrop by simp
                  have noin: "a \<notin> in_iterated (af_in_arr (af_reset_unsee_seg m' (af_vstack st) ?dst)) (snd a)"
                    using af_reset_unsee_seg_in_pristine[OF aii' dvs snddrop vsV] by simp
                  have fstnd: "fst a \<notin> set (take m' (af_vstack st))" using vsurv vnd dF by simp
                  have "out_iterated (af_out_arr (af_reset_unsee_seg m' (af_vstack st) ?dst)) (fst a) = out_iterated (af_out_arr st) (fst a)"
                    using af_reset_unsee_seg_out_lookup[OF aio' fstnd vsV] by simp
                  hence "a \<in> out_iterated (af_out_arr st) (fst a)" using sca noin by (auto simp: af_scanned_def)
                  thus False using apre dF by simp
                qed
              qed
              thus ?thesis using bscan ba by simp
            qed
          qed
        qed
      qed
    qed
  qed
qed

text \<open>The two advancing update branches preserve @{const af_scanres}: the advance scans the current
      arc (leaving every other scan intact, @{thm [source] af_out_advance_scan_sub}), and
      @{const af_handle} then restores the invariant via @{thm [source] af_handle_af_scanres}. The
      side-conditions of that lemma are discharged from the pre-step @{const af_scanres} (@{term srx}
      and @{term sra}) and the advance-preservation of the well-formedness invariants and
      @{const af_pristine1}.\<close>

lemma af_scanres_upd1:
  assumes inv: "AF_inv st" and c: "AF_DFS_call_1_conds st"
    and fresh: "\<forall>u. out_iterated out_arr u = {} \<and> in_iterated in_arr u = {}"
    and pr: "af_pristine1 st" and sr: "af_scanres st"
    and nub: "\<not> af_unbounded (AF_DFS_upd1 st)"
  shows "af_scanres (AF_DFS_upd1 st)"
proof -
  from inv have i1: "AF_invar_1 st" and i2: "AF_invar_2 st" and i3: "AF_invar_3 st"
    and iit: "AF_invar_iter st" and iV: "AF_invar_V st" and iestE: "AF_invar_estE st"
    and ife: "AF_invar_feas st" and ifr: "AF_invar_free st" by (auto simp: AF_inv_def)
  from c have ne: "af_vstack st \<noteq> []" and he: "out_has (af_out_arr st) (hd (af_vstack st))"
    by (auto elim!: call_cond_elims)
  have mi': "multigraph_inv (af_out_arr st) (af_in_arr st)" using iit by (simp add: AF_invar_iter_def)
  have vV: "hd (af_vstack st) \<in> \<V>" using iV ne hd_in_set by (auto simp: AF_invar_V_def)
  have aio: "out_invar (af_out_arr st)" using i1 by (simp add: AF_invar_1_def)
  have topos: "st_lookup (af_state st) (hd (af_vstack st)) = OnStack" using i2 ne hd_in_set vV by (auto simp: AF_invar_2_def)
  let ?top = "hd (af_vstack st)"
  let ?a = "out_current (af_out_arr st) ?top"
  let ?st' = "st\<lparr>af_out_arr := out_move (af_out_arr st) ?top\<rparr>"
  have endp: "fst ?a = ?top \<and> ?a \<in> \<E>" using af_current_out_endpoint[OF mi' vV he] .
  have ae: "?a \<in> \<E>" using endp by simp
  have near: "hd (af_vstack ?st') = (if True then fst ?a else snd ?a)" using endp by simp
  have vne: "af_vstack ?st' \<noteq> []" using ne by simp
  have inv': "AF_inv ?st'"
  proof (unfold AF_inv_def, intro conjI)
    show "AF_invar_1 ?st'" using AF_invar_1_out_advance[OF vV i1] .
    show "AF_invar_2 ?st'" using i2 by (simp add: AF_invar_2_def)
    show "AF_invar_3 ?st'" using i3 by (auto simp: AF_invar_3_def split: if_splits)
    show "AF_invar_iter ?st'" using iit he vV by (auto simp: AF_invar_iter_def intro: multigraph_inv_out_advance)
    show "AF_invar_V ?st'" using iV by (simp add: AF_invar_V_def)
    show "AF_invar_estE ?st'" using iestE by (simp add: AF_invar_estE_def)
    show "AF_invar_feas ?st'" using ife by (simp add: AF_invar_feas_def)
    show "AF_invar_free ?st'" using ifr by (simp add: AF_invar_free_def)
  qed
  have pr': "af_pristine1 ?st'"
  proof (unfold af_pristine1_def, intro ballI impI)
    fix w assume wV: "w \<in> \<V>" and "st_lookup (af_state ?st') w = Unseen"
    hence wun: "st_lookup (af_state st) w = Unseen" by simp
    hence wnt: "w \<noteq> ?top" using topos by auto
    have rem: "out_remaining (af_out_arr st) ?top \<noteq> {}" using he by (simp add: outg.idx_has[OF aio vV])
    have "out_iterated (af_out_arr ?st') w = out_iterated (af_out_arr st) w"
      using outg.idx_move_iterated_other[OF aio vV rem wnt] by simp
    thus "out_iterated (af_out_arr ?st') w = {} \<and> in_iterated (af_in_arr ?st') w = {}"
      using wun pr wV by (simp add: af_pristine1_def)
  qed
  have nub': "\<not> af_unbounded (af_handle ?st' ?a True)" using nub by (simp add: AF_DFS_upd1_def Let_def)
  have srx: "\<And>u cc. u \<in> \<V> \<Longrightarrow> st_lookup (af_state ?st') u = OnStack \<Longrightarrow> cc \<in> \<E> \<Longrightarrow> cc \<noteq> ?a \<Longrightarrow> af_scanned ?st' cc \<Longrightarrow>
                u \<in> {fst cc, snd cc} \<Longrightarrow> af_arc_free (af_flow ?st') cc \<Longrightarrow>
                st_lookup (af_state ?st') (if fst cc = u then snd cc else fst cc) \<noteq> Finished \<Longrightarrow> cc \<in> set (af_estack ?st')"
  proof -
    fix u cc
    assume uV: "u \<in> \<V>" and uos: "st_lookup (af_state ?st') u = OnStack" and ccE: "cc \<in> \<E>" and ccna: "cc \<noteq> ?a"
      and ccsc: "af_scanned ?st' cc" and ccinc: "u \<in> {fst cc, snd cc}"
      and ccfree: "af_arc_free (af_flow ?st') cc"
      and ccfar: "st_lookup (af_state ?st') (if fst cc = u then snd cc else fst cc) \<noteq> Finished"
    have sccst: "af_scanned st cc" using af_out_advance_scan_sub[OF i1 iit iV ne he ccna] ccsc by simp
    have "cc \<in> set (af_estack st)" using sr uos uV ccE sccst ccinc ccfree ccfar by (auto simp: af_scanres_def)
    thus "cc \<in> set (af_estack ?st')" by simp
  qed
  have sra: "st_lookup (af_state ?st') (if True then snd ?a else fst ?a) = OnStack \<Longrightarrow> af_arc_free (af_flow ?st') ?a \<Longrightarrow>
             ?a \<notin> set (af_estack ?st') \<Longrightarrow>
             (if True then ?a \<notin> in_iterated (af_in_arr ?st') (snd ?a)
              else ?a \<notin> out_iterated (af_out_arr ?st') (fst ?a))"
  proof -
    assume sndos: "st_lookup (af_state ?st') (if True then snd ?a else fst ?a) = OnStack"
      and afree: "af_arc_free (af_flow ?st') ?a" and anotin: "?a \<notin> set (af_estack ?st')"
    have sndos': "st_lookup (af_state st) (snd ?a) = OnStack" using sndos by simp
    have afree': "af_arc_free (af_flow st) ?a" using afree by simp
    have anotin': "?a \<notin> set (af_estack st)" using anotin by simp
    have "?a \<notin> in_iterated (af_in_arr st) (snd ?a)"
    proof
      assume "?a \<in> in_iterated (af_in_arr st) (snd ?a)"
      hence sca: "af_scanned st ?a" by (simp add: af_scanned_def)
      have farne: "st_lookup (af_state st) (if fst ?a = snd ?a then snd ?a else fst ?a) \<noteq> Finished"
        using endp topos sndos' by (auto split: if_splits)
      have "?a \<in> set (af_estack st)" using sr sndos' snd_E_V[OF ae] ae sca afree' farne by (auto simp: af_scanres_def)
      thus False using anotin' by simp
    qed
    thus "if True then ?a \<notin> in_iterated (af_in_arr ?st') (snd ?a)
          else ?a \<notin> out_iterated (af_out_arr ?st') (fst ?a)" by simp
  qed
  have "af_scanres (af_handle ?st' ?a True)"
    using af_handle_af_scanres[OF inv' fresh pr' ae near vne nub' srx sra] .
  thus ?thesis by (simp add: AF_DFS_upd1_def Let_def)
qed

lemma af_scanres_upd2:
  assumes inv: "AF_inv st" and c: "AF_DFS_call_2_conds st"
    and fresh: "\<forall>u. out_iterated out_arr u = {} \<and> in_iterated in_arr u = {}"
    and pr: "af_pristine1 st" and sr: "af_scanres st"
    and nub: "\<not> af_unbounded (AF_DFS_upd2 st)"
  shows "af_scanres (AF_DFS_upd2 st)"
proof -
  from inv have i1: "AF_invar_1 st" and i2: "AF_invar_2 st" and i3: "AF_invar_3 st"
    and iit: "AF_invar_iter st" and iV: "AF_invar_V st" and iestE: "AF_invar_estE st"
    and ife: "AF_invar_feas st" and ifr: "AF_invar_free st" by (auto simp: AF_inv_def)
  from c have ne: "af_vstack st \<noteq> []" and he: "in_has (af_in_arr st) (hd (af_vstack st))"
    by (auto elim!: call_cond_elims)
  have mi': "multigraph_inv (af_out_arr st) (af_in_arr st)" using iit by (simp add: AF_invar_iter_def)
  have vV: "hd (af_vstack st) \<in> \<V>" using iV ne hd_in_set by (auto simp: AF_invar_V_def)
  have aii: "in_invar (af_in_arr st)" using i1 by (simp add: AF_invar_1_def)
  have topos: "st_lookup (af_state st) (hd (af_vstack st)) = OnStack" using i2 ne hd_in_set vV by (auto simp: AF_invar_2_def)
  let ?top = "hd (af_vstack st)"
  let ?a = "in_current (af_in_arr st) ?top"
  let ?st' = "st\<lparr>af_in_arr := in_move (af_in_arr st) ?top\<rparr>"
  have endp: "snd ?a = ?top \<and> ?a \<in> \<E>" using af_current_in_endpoint[OF mi' vV he] .
  have ae: "?a \<in> \<E>" using endp by simp
  have near: "hd (af_vstack ?st') = (if False then fst ?a else snd ?a)" using endp by simp
  have vne: "af_vstack ?st' \<noteq> []" using ne by simp
  have inv': "AF_inv ?st'"
  proof (unfold AF_inv_def, intro conjI)
    show "AF_invar_1 ?st'" using AF_invar_1_in_advance[OF vV i1] .
    show "AF_invar_2 ?st'" using i2 by (simp add: AF_invar_2_def)
    show "AF_invar_3 ?st'" using i3 by (auto simp: AF_invar_3_def split: if_splits)
    show "AF_invar_iter ?st'" using iit he vV by (auto simp: AF_invar_iter_def intro: multigraph_inv_in_advance)
    show "AF_invar_V ?st'" using iV by (simp add: AF_invar_V_def)
    show "AF_invar_estE ?st'" using iestE by (simp add: AF_invar_estE_def)
    show "AF_invar_feas ?st'" using ife by (simp add: AF_invar_feas_def)
    show "AF_invar_free ?st'" using ifr by (simp add: AF_invar_free_def)
  qed
  have pr': "af_pristine1 ?st'"
  proof (unfold af_pristine1_def, intro ballI impI)
    fix w assume wV: "w \<in> \<V>" and "st_lookup (af_state ?st') w = Unseen"
    hence wun: "st_lookup (af_state st) w = Unseen" by simp
    hence wnt: "w \<noteq> ?top" using topos by auto
    have rem: "in_remaining (af_in_arr st) ?top \<noteq> {}" using he by (simp add: ing.idx_has[OF aii vV])
    have "in_iterated (af_in_arr ?st') w = in_iterated (af_in_arr st) w"
      using ing.idx_move_iterated_other[OF aii vV rem wnt] by simp
    thus "out_iterated (af_out_arr ?st') w = {} \<and> in_iterated (af_in_arr ?st') w = {}"
      using wun pr wV by (simp add: af_pristine1_def)
  qed
  have nub': "\<not> af_unbounded (af_handle ?st' ?a False)" using nub by (simp add: AF_DFS_upd2_def Let_def)
  have srx: "\<And>u cc. u \<in> \<V> \<Longrightarrow> st_lookup (af_state ?st') u = OnStack \<Longrightarrow> cc \<in> \<E> \<Longrightarrow> cc \<noteq> ?a \<Longrightarrow> af_scanned ?st' cc \<Longrightarrow>
                u \<in> {fst cc, snd cc} \<Longrightarrow> af_arc_free (af_flow ?st') cc \<Longrightarrow>
                st_lookup (af_state ?st') (if fst cc = u then snd cc else fst cc) \<noteq> Finished \<Longrightarrow> cc \<in> set (af_estack ?st')"
  proof -
    fix u cc
    assume uV: "u \<in> \<V>" and uos: "st_lookup (af_state ?st') u = OnStack" and ccE: "cc \<in> \<E>" and ccna: "cc \<noteq> ?a"
      and ccsc: "af_scanned ?st' cc" and ccinc: "u \<in> {fst cc, snd cc}"
      and ccfree: "af_arc_free (af_flow ?st') cc"
      and ccfar: "st_lookup (af_state ?st') (if fst cc = u then snd cc else fst cc) \<noteq> Finished"
    have sccst: "af_scanned st cc" using af_in_advance_scan_sub[OF i1 iit iV ne he ccna] ccsc by simp
    have "cc \<in> set (af_estack st)" using sr uos uV ccE sccst ccinc ccfree ccfar by (auto simp: af_scanres_def)
    thus "cc \<in> set (af_estack ?st')" by simp
  qed
  have sra: "st_lookup (af_state ?st') (if False then snd ?a else fst ?a) = OnStack \<Longrightarrow> af_arc_free (af_flow ?st') ?a \<Longrightarrow>
             ?a \<notin> set (af_estack ?st') \<Longrightarrow>
             (if False then ?a \<notin> in_iterated (af_in_arr ?st') (snd ?a)
              else ?a \<notin> out_iterated (af_out_arr ?st') (fst ?a))"
  proof -
    assume fstos: "st_lookup (af_state ?st') (if False then snd ?a else fst ?a) = OnStack"
      and afree: "af_arc_free (af_flow ?st') ?a" and anotin: "?a \<notin> set (af_estack ?st')"
    have fstos': "st_lookup (af_state st) (fst ?a) = OnStack" using fstos by simp
    have afree': "af_arc_free (af_flow st) ?a" using afree by simp
    have anotin': "?a \<notin> set (af_estack st)" using anotin by simp
    have "?a \<notin> out_iterated (af_out_arr st) (fst ?a)"
    proof
      assume "?a \<in> out_iterated (af_out_arr st) (fst ?a)"
      hence sca: "af_scanned st ?a" by (simp add: af_scanned_def)
      have farne: "st_lookup (af_state st) (if fst ?a = fst ?a then snd ?a else fst ?a) \<noteq> Finished"
        using endp topos by simp
      have "?a \<in> set (af_estack st)" using sr fstos' fst_E_V[OF ae] ae sca afree' farne by (auto simp: af_scanres_def)
      thus False using anotin' by simp
    qed
    thus "if False then ?a \<notin> in_iterated (af_in_arr ?st') (snd ?a)
          else ?a \<notin> out_iterated (af_out_arr ?st') (fst ?a)" by simp
  qed
  have "af_scanres (af_handle ?st' ?a False)"
    using af_handle_af_scanres[OF inv' fresh pr' ae near vne nub' srx sra] .
  thus ?thesis by (simp add: AF_DFS_upd2_def Let_def)
qed

text \<open>The combined @{const af_pristine} (first clause + no free-scanned self-loop) is preserved by every
      @{const AF_DFS} step. The first clause rides on @{const af_pristine1}'s preservation; the self-loop
      clause is discharged per step: an old free-scanned arc keeps @{term \<open>fst \<noteq> snd\<close>} by anti-monotone
      freeness (@{thm [source] af_free_mono_upd1}) and scan-subsumption
      (@{thm [source] af_out_advance_scan_sub}, @{thm [source] af_handle_scanned_sub}); a \emph{newly}
      scanned self-loop is the just-advanced current edge, which @{const af_handle} cancels and saturates
      (@{thm [source] af_cancel_seg_selfloop_notfree}) --- so it is no longer free.\<close>

lemma af_pristine_upd3:
  assumes inv: "AF_inv st" and conds: "AF_DFS_call_3_conds st" and pr: "af_pristine st"
  shows "af_pristine (AF_DFS_upd3 st)"
proof (unfold af_pristine_def, intro conjI)
  show "af_pristine1 (AF_DFS_upd3 st)" using af_pristine1_upd3[OF inv conds af_pristine_imp1[OF pr]] .
  show "\<forall>a. af_scanned (AF_DFS_upd3 st) a \<longrightarrow> af_arc_free (af_flow (AF_DFS_upd3 st)) a \<longrightarrow> fst a \<noteq> snd a"
  proof (intro allI impI)
    fix b assume "af_scanned (AF_DFS_upd3 st) b" and "af_arc_free (af_flow (AF_DFS_upd3 st)) b"
    hence "af_scanned st b" and "af_arc_free (af_flow st) b"
      by (simp_all add: af_scanned_def AF_DFS_upd3_def)
    thus "fst b \<noteq> snd b" using pr by (auto simp: af_pristine_def)
  qed
  show "\<forall>a. af_scanned (AF_DFS_upd3 st) a \<longrightarrow> fst a = snd a \<longrightarrow>
            (0 \<le> \<c> a \<longrightarrow> flow_lookup (af_flow (AF_DFS_upd3 st)) a = 0)
          \<and> (\<c> a < 0 \<longrightarrow> flow_lookup (af_flow (AF_DFS_upd3 st)) a = cap a)"
  proof (intro allI impI)
    fix b assume sc: "af_scanned (AF_DFS_upd3 st) b" and sl: "fst b = snd b"
    have "af_scanned st b" using sc by (simp add: af_scanned_def AF_DFS_upd3_def)
    moreover have "af_flow (AF_DFS_upd3 st) = af_flow st" by (simp add: AF_DFS_upd3_def)
    ultimately show "(0 \<le> \<c> b \<longrightarrow> flow_lookup (af_flow (AF_DFS_upd3 st)) b = 0)
                   \<and> (\<c> b < 0 \<longrightarrow> flow_lookup (af_flow (AF_DFS_upd3 st)) b = cap b)"
      using pr sl by (auto simp: af_pristine_def)
  qed
qed

lemma af_pristine_upd1:
  assumes inv: "AF_inv st" and c: "AF_DFS_call_1_conds st"
    and fresh: "\<forall>u. out_iterated out_arr u = {} \<and> in_iterated in_arr u = {}"
    and nub: "\<not> af_unbounded (AF_DFS_upd1 st)"
    and pr: "af_pristine st"
  shows "af_pristine (AF_DFS_upd1 st)"
proof (unfold af_pristine_def, intro conjI)
  from inv have i1: "AF_invar_1 st" and i2: "AF_invar_2 st" and iit: "AF_invar_iter st" and iV: "AF_invar_V st"
    and i3: "AF_invar_3 st" and iestE: "AF_invar_estE st"
    by (auto simp: AF_inv_def)
  from c have ne: "af_vstack st \<noteq> []" and he: "out_has (af_out_arr st) (hd (af_vstack st))"
    by (auto elim!: call_cond_elims)
  have pr1: "af_pristine1 st" using af_pristine_imp1[OF pr] .
  show "af_pristine1 (AF_DFS_upd1 st)" using af_pristine1_upd1[OF inv c fresh pr1] .
  show "\<forall>a. af_scanned (AF_DFS_upd1 st) a \<longrightarrow> af_arc_free (af_flow (AF_DFS_upd1 st)) a \<longrightarrow> fst a \<noteq> snd a"
  proof (intro allI impI)
    fix b assume bscan: "af_scanned (AF_DFS_upd1 st) b" and bfree: "af_arc_free (af_flow (AF_DFS_upd1 st)) b"
    have cl2: "\<And>d. af_scanned st d \<Longrightarrow> af_arc_free (af_flow st) d \<Longrightarrow> fst d \<noteq> snd d" using pr by (auto simp: af_pristine_def)
    let ?top = "hd (af_vstack st)"
    let ?a = "out_current (af_out_arr st) ?top"
    let ?st' = "st\<lparr>af_out_arr := out_move (af_out_arr st) ?top\<rparr>"
    have mi': "multigraph_inv (af_out_arr st) (af_in_arr st)" using iit by (simp add: AF_invar_iter_def)
    have vV: "?top \<in> \<V>" using iV ne hd_in_set by (auto simp: AF_invar_V_def)
    have ae: "?a \<in> \<E>" using af_current_out_endpoint[OF mi' vV he] by simp
    have i1': "AF_invar_1 ?st'" using AF_invar_1_out_advance[OF vV i1] .
    have i2': "AF_invar_2 ?st'" using i2 by (simp add: AF_invar_2_def)
    have AV': "AF_invar_V ?st'" using iV by (simp add: AF_invar_V_def)
    have hd1: "AF_DFS_upd1 st = af_handle ?st' ?a True" by (simp add: AF_DFS_upd1_def Let_def)
    have bscan': "af_scanned ?st' b" using af_handle_scanned_sub[OF i1' i2' AV' fresh] bscan hd1 by simp
    have bfree_st: "af_arc_free (af_flow st) b" using af_free_mono_upd1[OF inv c] bfree by simp
    show "fst b \<noteq> snd b"
    proof (cases "b = ?a")
      case bne: False
      have "af_scanned st b" using af_out_advance_scan_sub[OF i1 iit iV ne he bne] bscan' by simp
      thus ?thesis using cl2 bfree_st by blast
    next
      case bA: True
      show ?thesis
      proof (rule ccontr)
        assume sln: "\<not> fst b \<noteq> snd b"
        hence selfl: "fst ?a = snd ?a" using bA by simp
        have slx: "fst_exec ?a = snd_exec ?a" using selfl fst_exec_eq[OF ae] snd_exec_eq[OF ae] by simp
        have h: "af_handle ?st' ?a True = af_selfloop_handle ?st' ?a" using slx by (simp add: af_handle_def)
        have fi: "flow_invar (af_flow ?st')" using i1' by (simp add: AF_invar_1_def)
        have nub': "\<not> af_unbounded (af_selfloop_handle ?st' ?a)" using nub hd1 h by simp
        have "\<not> af_arc_free (af_flow (af_selfloop_handle ?st' ?a)) ?a"
          using af_selfloop_handle_notfree[OF ae fi nub'] .
        thus False using bfree bA hd1 h by simp
      qed
    qed
  qed
  show "\<forall>a. af_scanned (AF_DFS_upd1 st) a \<longrightarrow> fst a = snd a \<longrightarrow>
            (0 \<le> \<c> a \<longrightarrow> flow_lookup (af_flow (AF_DFS_upd1 st)) a = 0)
          \<and> (\<c> a < 0 \<longrightarrow> flow_lookup (af_flow (AF_DFS_upd1 st)) a = cap a)"
  proof (intro allI impI)
    fix b assume bscan: "af_scanned (AF_DFS_upd1 st) b" and bsl: "fst b = snd b"
    have cl3: "\<And>d. af_scanned st d \<Longrightarrow> fst d = snd d \<Longrightarrow>
                 (0 \<le> \<c> d \<longrightarrow> flow_lookup (af_flow st) d = 0) \<and> (\<c> d < 0 \<longrightarrow> flow_lookup (af_flow st) d = cap d)"
      using pr by (auto simp: af_pristine_def)
    let ?top = "hd (af_vstack st)"
    let ?a = "out_current (af_out_arr st) ?top"
    let ?st' = "st\<lparr>af_out_arr := out_move (af_out_arr st) ?top\<rparr>"
    have mi': "multigraph_inv (af_out_arr st) (af_in_arr st)" using iit by (simp add: AF_invar_iter_def)
    have vV: "?top \<in> \<V>" using iV ne hd_in_set by (auto simp: AF_invar_V_def)
    have ae: "?a \<in> \<E>" using af_current_out_endpoint[OF mi' vV he] by simp
    have i1': "AF_invar_1 ?st'" using AF_invar_1_out_advance[OF vV i1] .
    have i2': "AF_invar_2 ?st'" using i2 by (simp add: AF_invar_2_def)
    have es_eq: "af_estack ?st' = af_estack st" and ds_eq: "af_dstack ?st' = af_dstack st"
      and vs_eq: "af_vstack ?st' = af_vstack st" by simp_all
    have i3': "AF_invar_3 ?st'" using i3 by (simp only: AF_invar_3_def es_eq ds_eq vs_eq)
    have estE': "AF_invar_estE ?st'" using iestE by (simp only: AF_invar_estE_def es_eq)
    have AV': "AF_invar_V ?st'" using iV by (simp add: AF_invar_V_def)
    have hd1: "AF_DFS_upd1 st = af_handle ?st' ?a True" by (simp add: AF_DFS_upd1_def Let_def)
    have bscan': "af_scanned ?st' b" using af_handle_scanned_sub[OF i1' i2' AV' fresh] bscan hd1 by simp
    show "(0 \<le> \<c> b \<longrightarrow> flow_lookup (af_flow (AF_DFS_upd1 st)) b = 0)
        \<and> (\<c> b < 0 \<longrightarrow> flow_lookup (af_flow (AF_DFS_upd1 st)) b = cap b)"
    proof (cases "b = ?a")
      case bA: True
      have slx: "fst_exec ?a = snd_exec ?a" using bsl bA fst_exec_eq[OF ae] snd_exec_eq[OF ae] by simp
      have h: "af_handle ?st' ?a True = af_selfloop_handle ?st' ?a" using slx by (simp add: af_handle_def)
      have fi: "flow_invar (af_flow ?st')" using i1' by (simp add: AF_invar_1_def)
      have nub': "\<not> af_unbounded (af_selfloop_handle ?st' ?a)" using nub hd1 h by simp
      have "(0 \<le> \<c> ?a \<longrightarrow> flow_lookup (af_flow (af_selfloop_handle ?st' ?a)) ?a = 0)
          \<and> (\<c> ?a < 0 \<longrightarrow> cap ?a \<noteq> - 1 \<and> flow_lookup (af_flow (af_selfloop_handle ?st' ?a)) ?a = cap ?a)"
        using af_selfloop_handle_norm[OF ae fi nub'] .
      thus ?thesis using bA hd1 h by simp
    next
      case bne: False
      have off: "flow_lookup (af_flow (af_handle ?st' ?a True)) b = flow_lookup (af_flow ?st') b"
        using af_handle_flow_selfloop_off[OF i1' i2' i3' estE' ae bsl bne] .
      have "af_scanned st b" using af_out_advance_scan_sub[OF i1 iit iV ne he bne] bscan' by simp
      thus ?thesis using cl3[OF _ bsl] off hd1 by simp
    qed
  qed
qed

lemma af_pristine_upd2:
  assumes inv: "AF_inv st" and c: "AF_DFS_call_2_conds st"
    and fresh: "\<forall>u. out_iterated out_arr u = {} \<and> in_iterated in_arr u = {}"
    and nub: "\<not> af_unbounded (AF_DFS_upd2 st)"
    and pr: "af_pristine st"
  shows "af_pristine (AF_DFS_upd2 st)"
proof (unfold af_pristine_def, intro conjI)
  from inv have i1: "AF_invar_1 st" and i2: "AF_invar_2 st" and iit: "AF_invar_iter st" and iV: "AF_invar_V st"
    and i3: "AF_invar_3 st" and iestE: "AF_invar_estE st"
    by (auto simp: AF_inv_def)
  from c have ne: "af_vstack st \<noteq> []" and he: "in_has (af_in_arr st) (hd (af_vstack st))"
    by (auto elim!: call_cond_elims)
  have pr1: "af_pristine1 st" using af_pristine_imp1[OF pr] .
  show "af_pristine1 (AF_DFS_upd2 st)" using af_pristine1_upd2[OF inv c fresh pr1] .
  show "\<forall>a. af_scanned (AF_DFS_upd2 st) a \<longrightarrow> af_arc_free (af_flow (AF_DFS_upd2 st)) a \<longrightarrow> fst a \<noteq> snd a"
  proof (intro allI impI)
    fix b assume bscan: "af_scanned (AF_DFS_upd2 st) b" and bfree: "af_arc_free (af_flow (AF_DFS_upd2 st)) b"
    have cl2: "\<And>d. af_scanned st d \<Longrightarrow> af_arc_free (af_flow st) d \<Longrightarrow> fst d \<noteq> snd d" using pr by (auto simp: af_pristine_def)
    let ?top = "hd (af_vstack st)"
    let ?a = "in_current (af_in_arr st) ?top"
    let ?st' = "st\<lparr>af_in_arr := in_move (af_in_arr st) ?top\<rparr>"
    have mi': "multigraph_inv (af_out_arr st) (af_in_arr st)" using iit by (simp add: AF_invar_iter_def)
    have vV: "?top \<in> \<V>" using iV ne hd_in_set by (auto simp: AF_invar_V_def)
    have ae: "?a \<in> \<E>" using af_current_in_endpoint[OF mi' vV he] by simp
    have i1': "AF_invar_1 ?st'" using AF_invar_1_in_advance[OF vV i1] .
    have i2': "AF_invar_2 ?st'" using i2 by (simp add: AF_invar_2_def)
    have AV': "AF_invar_V ?st'" using iV by (simp add: AF_invar_V_def)
    have hd2: "AF_DFS_upd2 st = af_handle ?st' ?a False" by (simp add: AF_DFS_upd2_def Let_def)
    have bscan': "af_scanned ?st' b" using af_handle_scanned_sub[OF i1' i2' AV' fresh] bscan hd2 by simp
    have bfree_st: "af_arc_free (af_flow st) b" using af_free_mono_upd2[OF inv c] bfree by simp
    show "fst b \<noteq> snd b"
    proof (cases "b = ?a")
      case bne: False
      have "af_scanned st b" using af_in_advance_scan_sub[OF i1 iit iV ne he bne] bscan' by simp
      thus ?thesis using cl2 bfree_st by blast
    next
      case bA: True
      show ?thesis
      proof (rule ccontr)
        assume sln: "\<not> fst b \<noteq> snd b"
        hence selfl: "fst ?a = snd ?a" using bA by simp
        have slx: "fst_exec ?a = snd_exec ?a" using selfl fst_exec_eq[OF ae] snd_exec_eq[OF ae] by simp
        have h: "af_handle ?st' ?a False = af_selfloop_handle ?st' ?a" using slx by (simp add: af_handle_def)
        have fi: "flow_invar (af_flow ?st')" using i1' by (simp add: AF_invar_1_def)
        have nub': "\<not> af_unbounded (af_selfloop_handle ?st' ?a)" using nub hd2 h by simp
        have "\<not> af_arc_free (af_flow (af_selfloop_handle ?st' ?a)) ?a"
          using af_selfloop_handle_notfree[OF ae fi nub'] .
        thus False using bfree bA hd2 h by simp
      qed
    qed
  qed
  show "\<forall>a. af_scanned (AF_DFS_upd2 st) a \<longrightarrow> fst a = snd a \<longrightarrow>
            (0 \<le> \<c> a \<longrightarrow> flow_lookup (af_flow (AF_DFS_upd2 st)) a = 0)
          \<and> (\<c> a < 0 \<longrightarrow> flow_lookup (af_flow (AF_DFS_upd2 st)) a = cap a)"
  proof (intro allI impI)
    fix b assume bscan: "af_scanned (AF_DFS_upd2 st) b" and bsl: "fst b = snd b"
    have cl3: "\<And>d. af_scanned st d \<Longrightarrow> fst d = snd d \<Longrightarrow>
                 (0 \<le> \<c> d \<longrightarrow> flow_lookup (af_flow st) d = 0) \<and> (\<c> d < 0 \<longrightarrow> flow_lookup (af_flow st) d = cap d)"
      using pr by (auto simp: af_pristine_def)
    let ?top = "hd (af_vstack st)"
    let ?a = "in_current (af_in_arr st) ?top"
    let ?st' = "st\<lparr>af_in_arr := in_move (af_in_arr st) ?top\<rparr>"
    have mi': "multigraph_inv (af_out_arr st) (af_in_arr st)" using iit by (simp add: AF_invar_iter_def)
    have vV: "?top \<in> \<V>" using iV ne hd_in_set by (auto simp: AF_invar_V_def)
    have ae: "?a \<in> \<E>" using af_current_in_endpoint[OF mi' vV he] by simp
    have i1': "AF_invar_1 ?st'" using AF_invar_1_in_advance[OF vV i1] .
    have i2': "AF_invar_2 ?st'" using i2 by (simp add: AF_invar_2_def)
    have es_eq: "af_estack ?st' = af_estack st" and ds_eq: "af_dstack ?st' = af_dstack st"
      and vs_eq: "af_vstack ?st' = af_vstack st" by simp_all
    have i3': "AF_invar_3 ?st'" using i3 by (simp only: AF_invar_3_def es_eq ds_eq vs_eq)
    have estE': "AF_invar_estE ?st'" using iestE by (simp only: AF_invar_estE_def es_eq)
    have AV': "AF_invar_V ?st'" using iV by (simp add: AF_invar_V_def)
    have hd2: "AF_DFS_upd2 st = af_handle ?st' ?a False" by (simp add: AF_DFS_upd2_def Let_def)
    have bscan': "af_scanned ?st' b" using af_handle_scanned_sub[OF i1' i2' AV' fresh] bscan hd2 by simp
    show "(0 \<le> \<c> b \<longrightarrow> flow_lookup (af_flow (AF_DFS_upd2 st)) b = 0)
        \<and> (\<c> b < 0 \<longrightarrow> flow_lookup (af_flow (AF_DFS_upd2 st)) b = cap b)"
    proof (cases "b = ?a")
      case bA: True
      have slx: "fst_exec ?a = snd_exec ?a" using bsl bA fst_exec_eq[OF ae] snd_exec_eq[OF ae] by simp
      have h: "af_handle ?st' ?a False = af_selfloop_handle ?st' ?a" using slx by (simp add: af_handle_def)
      have fi: "flow_invar (af_flow ?st')" using i1' by (simp add: AF_invar_1_def)
      have nub': "\<not> af_unbounded (af_selfloop_handle ?st' ?a)" using nub hd2 h by simp
      have "(0 \<le> \<c> ?a \<longrightarrow> flow_lookup (af_flow (af_selfloop_handle ?st' ?a)) ?a = 0)
          \<and> (\<c> ?a < 0 \<longrightarrow> cap ?a \<noteq> - 1 \<and> flow_lookup (af_flow (af_selfloop_handle ?st' ?a)) ?a = cap ?a)"
        using af_selfloop_handle_norm[OF ae fi nub'] .
      thus ?thesis using bA hd2 h by simp
    next
      case bne: False
      have off: "flow_lookup (af_flow (af_handle ?st' ?a False)) b = flow_lookup (af_flow ?st') b"
        using af_handle_flow_selfloop_off[OF i1' i2' i3' estE' ae bsl bne] .
      have "af_scanned st b" using af_in_advance_scan_sub[OF i1 iit iV ne he bne] bscan' by simp
      thus ?thesis using cl3[OF _ bsl] off hd2 by simp
    qed
  qed
qed

subsection \<open>Lifting the finish-order invariant through the instrumented DFS\<close>

text \<open>The finish clock never decreases: a vertex is stamped @{term c} when it is finished and the clock
      then advances to @{term \<open>Suc c\<close>}, so every finished vertex's rank stays below the current clock.
      The advancing steps finish nobody, hence leave the clock invariant intact.\<close>

definition "af_vrank st rk c \<longleftrightarrow>
  (\<forall>u\<in>\<V>. st_lookup (af_state st) u = Finished \<longrightarrow> rk u < (c :: nat)) \<and>
  inj_on rk {v\<in>\<V>. st_lookup (af_state st) v = Finished}"

text \<open>@{const af_vrank} now folds in the finish-clock discipline \emph{and} injectivity of the ranking
      on finished vertices: each pop stamps the current clock @{term c}, which the bound clause
      guarantees is strictly above every already-finished rank, so the new rank is fresh. Injectivity of
      the terminal ranking is what lets the forest argument pick a strict minimum on a cycle.\<close>

lemma af_vrank_upd3:
  assumes inv: "AF_inv st" and conds: "AF_DFS_call_3_conds st" and vr: "af_vrank st rk c"
  shows "af_vrank (AF_DFS_upd3 st) (rk(hd (af_vstack st) := c)) (Suc c)"
proof -
  from inv have i1: "AF_invar_1 st" and A2: "AF_invar_2 st" and iV: "AF_invar_V st" by (auto simp: AF_inv_def)
  have si: "st_invar (af_state st)" using i1 by (simp add: AF_invar_1_def)
  have ne: "af_vstack st \<noteq> []" using conds by (auto elim!: call_cond_elims)
  let ?v = "hd (af_vstack st)"
  have vV: "?v \<in> \<V>" using iV ne hd_in_set by (auto simp: AF_invar_V_def)
  have vos: "st_lookup (af_state st) ?v = OnStack" using A2 ne hd_in_set vV by (auto simp: AF_invar_2_def)
  have bound: "\<forall>u\<in>\<V>. st_lookup (af_state st) u = Finished \<longrightarrow> rk u < c"
    and injh: "inj_on rk {v\<in>\<V>. st_lookup (af_state st) v = Finished}" using vr by (auto simp: af_vrank_def)
  have lk: "\<And>u. st_lookup (af_state (AF_DFS_upd3 st)) u = (if u = ?v then Finished else st_lookup (af_state st) u)"
    using si by (simp add: AF_DFS_upd3_def state_arr.fixed_univ_map_upd[OF si vV])
  show ?thesis
  proof (unfold af_vrank_def, intro conjI ballI impI)
    fix u assume uV: "u \<in> \<V>" and un: "st_lookup (af_state (AF_DFS_upd3 st)) u = Finished"
    show "(rk(?v := c)) u < Suc c"
    proof (cases "u = ?v")
      case True thus ?thesis by simp
    next
      case False
      hence "st_lookup (af_state st) u = Finished" using un lk by simp
      hence "rk u < c" using bound uV by simp
      thus ?thesis using False by simp
    qed
  next
    have setEq: "{v\<in>\<V>. st_lookup (af_state (AF_DFS_upd3 st)) v = Finished} = insert ?v {v\<in>\<V>. st_lookup (af_state st) v = Finished}"
      using lk vos vV by auto
    show "inj_on (rk(?v := c)) {v\<in>\<V>. st_lookup (af_state (AF_DFS_upd3 st)) v = Finished}"
    proof (unfold setEq, rule inj_on_insert[THEN iffD2], intro conjI)
      show "inj_on (rk(?v := c)) {v\<in>\<V>. st_lookup (af_state st) v = Finished}"
        using injh vos by (auto simp: inj_on_def)
      show "(rk(?v := c)) ?v \<notin> (rk(?v := c)) ` ({v\<in>\<V>. st_lookup (af_state st) v = Finished} - {?v})"
        using bound vos by (auto simp: image_iff)
    qed
  qed
qed

lemma af_vrank_upd1:
  assumes inv: "AF_inv st" and conds: "AF_DFS_call_1_conds st" and vr: "af_vrank st rk c"
  shows "af_vrank (AF_DFS_upd1 st) rk c"
proof -
  from inv have i1: "AF_invar_1 st" and i2: "AF_invar_2 st" and iit: "AF_invar_iter st"
    and iV: "AF_invar_V st" by (auto simp: AF_inv_def)
  from conds have ne: "af_vstack st \<noteq> []" and he: "out_has (af_out_arr st) (hd (af_vstack st))"
    by (auto elim!: call_cond_elims)
  have mi': "multigraph_inv (af_out_arr st) (af_in_arr st)" using iit by (simp add: AF_invar_iter_def)
  have vV: "hd (af_vstack st) \<in> \<V>" using iV ne hd_in_set by (auto simp: AF_invar_V_def)
  have ae: "out_current (af_out_arr st) (hd (af_vstack st)) \<in> \<E>"
    using af_current_out_endpoint[OF mi' vV he] by simp
  have bound: "\<forall>u\<in>\<V>. st_lookup (af_state st) u = Finished \<longrightarrow> rk u < c"
    and injh: "inj_on rk {v\<in>\<V>. st_lookup (af_state st) v = Finished}" using vr by (auto simp: af_vrank_def)
  let ?st' = "st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack st))\<rparr>"
  have i1': "AF_invar_1 ?st'" using AF_invar_1_out_advance[OF vV i1] .
  have i2': "AF_invar_2 ?st'" using i2 by (simp add: AF_invar_2_def)
  have AV': "AF_invar_V ?st'" using iV by (simp add: AF_invar_V_def)
  have fback: "\<And>u. st_lookup (af_state (AF_DFS_upd1 st)) u = Finished \<Longrightarrow> st_lookup (af_state st) u = Finished"
  proof -
    fix u assume "st_lookup (af_state (AF_DFS_upd1 st)) u = Finished"
    hence "st_lookup (af_state (af_handle ?st' (out_current (af_out_arr st) (hd (af_vstack st))) True)) u = Finished"
      by (simp add: AF_DFS_upd1_def Let_def)
    hence "st_lookup (af_state ?st') u = Finished" using af_handle_finished_back[OF i1' i2' ae AV'] by blast
    thus "st_lookup (af_state st) u = Finished" by simp
  qed
  show ?thesis
  proof (unfold af_vrank_def, intro conjI ballI impI)
    fix u assume uV: "u \<in> \<V>" and "st_lookup (af_state (AF_DFS_upd1 st)) u = Finished"
    thus "rk u < c" using fback bound uV by simp
  next
    have sub: "{v\<in>\<V>. st_lookup (af_state (AF_DFS_upd1 st)) v = Finished} \<subseteq> {v\<in>\<V>. st_lookup (af_state st) v = Finished}"
      using fback by auto
    show "inj_on rk {v\<in>\<V>. st_lookup (af_state (AF_DFS_upd1 st)) v = Finished}"
      using inj_on_subset[OF injh sub] .
  qed
qed

lemma af_vrank_upd2:
  assumes inv: "AF_inv st" and conds: "AF_DFS_call_2_conds st" and vr: "af_vrank st rk c"
  shows "af_vrank (AF_DFS_upd2 st) rk c"
proof -
  from inv have i1: "AF_invar_1 st" and i2: "AF_invar_2 st" and iit: "AF_invar_iter st"
    and iV: "AF_invar_V st" by (auto simp: AF_inv_def)
  from conds have ne: "af_vstack st \<noteq> []" and he: "in_has (af_in_arr st) (hd (af_vstack st))"
    by (auto elim!: call_cond_elims)
  have mi': "multigraph_inv (af_out_arr st) (af_in_arr st)" using iit by (simp add: AF_invar_iter_def)
  have vV: "hd (af_vstack st) \<in> \<V>" using iV ne hd_in_set by (auto simp: AF_invar_V_def)
  have ae: "in_current (af_in_arr st) (hd (af_vstack st)) \<in> \<E>"
    using af_current_in_endpoint[OF mi' vV he] by simp
  have bound: "\<forall>u\<in>\<V>. st_lookup (af_state st) u = Finished \<longrightarrow> rk u < c"
    and injh: "inj_on rk {v\<in>\<V>. st_lookup (af_state st) v = Finished}" using vr by (auto simp: af_vrank_def)
  let ?st' = "st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack st))\<rparr>"
  have i1': "AF_invar_1 ?st'" using AF_invar_1_in_advance[OF vV i1] .
  have i2': "AF_invar_2 ?st'" using i2 by (simp add: AF_invar_2_def)
  have AV': "AF_invar_V ?st'" using iV by (simp add: AF_invar_V_def)
  have fback: "\<And>u. st_lookup (af_state (AF_DFS_upd2 st)) u = Finished \<Longrightarrow> st_lookup (af_state st) u = Finished"
  proof -
    fix u assume "st_lookup (af_state (AF_DFS_upd2 st)) u = Finished"
    hence "st_lookup (af_state (af_handle ?st' (in_current (af_in_arr st) (hd (af_vstack st))) False)) u = Finished"
      by (simp add: AF_DFS_upd2_def Let_def)
    hence "st_lookup (af_state ?st') u = Finished" using af_handle_finished_back[OF i1' i2' ae AV'] by blast
    thus "st_lookup (af_state st) u = Finished" by simp
  qed
  show ?thesis
  proof (unfold af_vrank_def, intro conjI ballI impI)
    fix u assume uV: "u \<in> \<V>" and "st_lookup (af_state (AF_DFS_upd2 st)) u = Finished"
    thus "rk u < c" using fback bound uV by simp
  next
    have sub: "{v\<in>\<V>. st_lookup (af_state (AF_DFS_upd2 st)) v = Finished} \<subseteq> {v\<in>\<V>. st_lookup (af_state st) v = Finished}"
      using fback by auto
    show "inj_on rk {v\<in>\<V>. st_lookup (af_state (AF_DFS_upd2 st)) v = Finished}"
      using inj_on_subset[OF injh sub] .
  qed
qed

text \<open>Domain of the recursive calls (downward closure of the accessibility relation) and the fact that
      an already-unbounded state is returned unchanged; together they let a not-@{const af_unbounded}
      result be pushed back one single step, which is what @{thm [source] af_scanres_upd1} needs.\<close>

lemma AF_DFS_dom_upd1:
  assumes dom: "AF_DFS_dom st" and ca: "AF_DFS_call_1_conds st" shows "AF_DFS_dom (AF_DFS_upd1 st)"
proof -
  have "AF_DFS_rel (AF_DFS_upd1 st) st"
    using ca by (subst AF_DFS_rel.simps) (auto simp: AF_DFS_call_1_conds_def AF_DFS_upd1_def Let_def split: list.splits)
  thus ?thesis using dom by (rule accp_downward[rotated])
qed

lemma AF_DFS_dom_upd2:
  assumes dom: "AF_DFS_dom st" and ca: "AF_DFS_call_2_conds st" shows "AF_DFS_dom (AF_DFS_upd2 st)"
proof -
  have "AF_DFS_rel (AF_DFS_upd2 st) st"
    using ca by (subst AF_DFS_rel.simps) (auto simp: AF_DFS_call_2_conds_def AF_DFS_upd2_def Let_def split: list.splits)
  thus ?thesis using dom by (rule accp_downward[rotated])
qed

lemma AF_DFS_unbounded_id:
  assumes dom: "AF_DFS_dom st" and ub: "af_unbounded st" shows "AF_DFS st = st"
  using ub by (simp add: AF_DFS.psimps[OF dom])

lemma nub_step1:
  assumes dom: "AF_DFS_dom st" and ca: "AF_DFS_call_1_conds st" and nu: "\<not> af_unbounded (AF_DFS st)"
  shows "\<not> af_unbounded (AF_DFS_upd1 st)"
proof
  assume ub: "af_unbounded (AF_DFS_upd1 st)"
  have "AF_DFS (AF_DFS_upd1 st) = AF_DFS_upd1 st" using AF_DFS_unbounded_id[OF AF_DFS_dom_upd1[OF dom ca] ub] .
  hence "af_unbounded (AF_DFS st)" using ub ca by (simp add: AF_DFS_simps[OF dom])
  thus False using nu by simp
qed

lemma nub_step2:
  assumes dom: "AF_DFS_dom st" and ca: "AF_DFS_call_2_conds st" and nu: "\<not> af_unbounded (AF_DFS st)"
  shows "\<not> af_unbounded (AF_DFS_upd2 st)"
proof
  assume ub: "af_unbounded (AF_DFS_upd2 st)"
  have "AF_DFS (AF_DFS_upd2 st) = AF_DFS_upd2 st" using AF_DFS_unbounded_id[OF AF_DFS_dom_upd2[OF dom ca] ub] .
  hence "af_unbounded (AF_DFS st)" using ub ca by (simp add: AF_DFS_simps[OF dom])
  thus False using nu by simp
qed

text \<open>The lift: with all four running invariants (@{const AF_inv}, @{const af_pristine},
      @{const af_scanres}, @{const af_rankok}) and the finish-clock discipline (@{const af_vrank})
      preserved by every update, the finish-order invariant @{const af_rankok} holds of the whole-run
      result, with respect to the finish ranks accumulated by @{const AF_DFS_i}. The base component of
      @{const AF_DFS_i} is the executable @{const AF_DFS}.\<close>

lemma af_rankok_AF_DFS_i:
  assumes dom: "AF_DFS_dom st" and mi0: "multigraph_inv out_arr in_arr"
    and fresh: "\<forall>u. out_iterated out_arr u = {} \<and> in_iterated in_arr u = {}"
  shows "\<forall>rk c. AF_inv st \<longrightarrow> af_pristine st \<longrightarrow> af_scanres st \<longrightarrow> af_rankok st rk \<longrightarrow> af_vrank st rk c \<longrightarrow>
         \<not> af_unbounded (AF_DFS st) \<longrightarrow>
         (\<exists>r cc. AF_DFS_i st rk c = (AF_DFS st, r, cc) \<and> af_rankok (AF_DFS st) r)"
proof (induction rule: AF_DFS_induct[OF dom])
  case (1 st)
  show ?case
  proof (intro allI impI)
    fix rk c
    assume inv: "AF_inv st" and pr: "af_pristine st" and sr: "af_scanres st"
      and ok: "af_rankok st rk" and vr: "af_vrank st rk c" and nub: "\<not> af_unbounded (AF_DFS st)"
    from inv have i1: "AF_invar_1 st" and i2: "AF_invar_2 st" by (auto simp: AF_inv_def)
    have si: "st_invar (af_state st)" using i1 by (simp add: AF_invar_1_def)
    have di: "AF_DFS_i_dom (st, rk, c)" using AF_DFS_i_dom_all[OF 1(1)] by blast
    show "\<exists>r cc. AF_DFS_i st rk c = (AF_DFS st, r, cc) \<and> af_rankok (AF_DFS st) r"
    proof (rule AF_DFS_cases[where st = st])
      assume ca: "AF_DFS_call_1_conds st"
      have eq: "AF_DFS_i st rk c = AF_DFS_i (AF_DFS_upd1 st) rk c"
        using ca by (auto simp: AF_DFS_i.psimps[OF di] AF_DFS_upd1_def Let_def elim!: call_cond_elims)
      have dfeq: "AF_DFS (AF_DFS_upd1 st) = AF_DFS st" using ca by (simp add: AF_DFS_simps[OF 1(1)])
      have nub1: "\<not> af_unbounded (AF_DFS_upd1 st)" using nub_step1[OF 1(1) ca nub] .
      have nub': "\<not> af_unbounded (AF_DFS (AF_DFS_upd1 st))" using nub dfeq by simp
      have "\<exists>r cc. AF_DFS_i (AF_DFS_upd1 st) rk c = (AF_DFS (AF_DFS_upd1 st), r, cc) \<and> af_rankok (AF_DFS (AF_DFS_upd1 st)) r"
        using 1(2)[OF ca] AF_inv_holds_1[OF mi0 ca inv] af_pristine_upd1[OF inv ca fresh nub1 pr]
              af_scanres_upd1[OF inv ca fresh af_pristine_imp1[OF pr] sr nub1] af_rankok_upd1[OF inv ca ok]
              af_vrank_upd1[OF inv ca vr] nub' by blast
      then obtain r cc where "AF_DFS_i (AF_DFS_upd1 st) rk c = (AF_DFS (AF_DFS_upd1 st), r, cc)"
        and rok: "af_rankok (AF_DFS (AF_DFS_upd1 st)) r" by blast
      thus "\<exists>r cc. AF_DFS_i st rk c = (AF_DFS st, r, cc) \<and> af_rankok (AF_DFS st) r" using eq dfeq by auto
    next
      assume ca: "AF_DFS_call_2_conds st"
      have eq: "AF_DFS_i st rk c = AF_DFS_i (AF_DFS_upd2 st) rk c"
        using ca by (auto simp: AF_DFS_i.psimps[OF di] AF_DFS_upd2_def Let_def elim!: call_cond_elims)
      have dfeq: "AF_DFS (AF_DFS_upd2 st) = AF_DFS st" using ca by (simp add: AF_DFS_simps[OF 1(1)])
      have nub1: "\<not> af_unbounded (AF_DFS_upd2 st)" using nub_step2[OF 1(1) ca nub] .
      have nub': "\<not> af_unbounded (AF_DFS (AF_DFS_upd2 st))" using nub dfeq by simp
      have "\<exists>r cc. AF_DFS_i (AF_DFS_upd2 st) rk c = (AF_DFS (AF_DFS_upd2 st), r, cc) \<and> af_rankok (AF_DFS (AF_DFS_upd2 st)) r"
        using 1(3)[OF ca] AF_inv_holds_2[OF mi0 ca inv] af_pristine_upd2[OF inv ca fresh nub1 pr]
              af_scanres_upd2[OF inv ca fresh af_pristine_imp1[OF pr] sr nub1] af_rankok_upd2[OF inv ca ok]
              af_vrank_upd2[OF inv ca vr] nub' by blast
      then obtain r cc where "AF_DFS_i (AF_DFS_upd2 st) rk c = (AF_DFS (AF_DFS_upd2 st), r, cc)"
        and rok: "af_rankok (AF_DFS (AF_DFS_upd2 st)) r" by blast
      thus "\<exists>r cc. AF_DFS_i st rk c = (AF_DFS st, r, cc) \<and> af_rankok (AF_DFS st) r" using eq dfeq by auto
    next
      assume ca: "AF_DFS_call_3_conds st"
      have eq: "AF_DFS_i st rk c = AF_DFS_i (AF_DFS_upd3 st) (rk(hd (af_vstack st) := c)) (Suc c)"
        using ca by (auto simp: AF_DFS_i.psimps[OF di] AF_DFS_upd3_def elim!: call_cond_elims)
      have dfeq: "AF_DFS (AF_DFS_upd3 st) = AF_DFS st" using ca
        by (simp add: AF_DFS_simps[OF 1(1)])
      have ne: "af_vstack st \<noteq> []" using ca by (auto elim!: call_cond_elims)
      have vrank': "\<And>u. u \<in> \<V> \<Longrightarrow> st_lookup (af_state st) u = Finished \<Longrightarrow> rk u < c" using vr by (auto simp: af_vrank_def)
      have nub': "\<not> af_unbounded (AF_DFS (AF_DFS_upd3 st))" using nub dfeq by simp
      have "\<exists>r cc. AF_DFS_i (AF_DFS_upd3 st) (rk(hd (af_vstack st) := c)) (Suc c) = (AF_DFS (AF_DFS_upd3 st), r, cc)
              \<and> af_rankok (AF_DFS (AF_DFS_upd3 st)) r"
        using 1(4)[OF ca] AF_inv_holds_3[OF ca inv] af_pristine_upd3[OF inv ca pr]
              af_scanres_upd3[OF inv ca sr] af_rankok_upd3[OF inv ca ok sr vrank']
              af_vrank_upd3[OF inv ca vr] nub' by blast
      then obtain r cc where "AF_DFS_i (AF_DFS_upd3 st) (rk(hd (af_vstack st) := c)) (Suc c) = (AF_DFS (AF_DFS_upd3 st), r, cc)"
        and rok: "af_rankok (AF_DFS (AF_DFS_upd3 st)) r" by blast
      thus "\<exists>r cc. AF_DFS_i st rk c = (AF_DFS st, r, cc) \<and> af_rankok (AF_DFS st) r" using eq dfeq by auto
    next
      assume ca: "AF_DFS_ret_conds st"
      hence eq: "AF_DFS_i st rk c = (st, rk, c)"
        by (auto simp: AF_DFS_i.psimps[OF di] AF_DFS_ret_conds_def split: list.splits)
      have "AF_DFS st = st"
        using AF_DFS_simps(4)[OF 1(1) ca] by (simp add: AF_DFS_ret_def)
      thus "\<exists>r cc. AF_DFS_i st rk c = (AF_DFS st, r, cc) \<and> af_rankok (AF_DFS st) r" using eq ok by auto
    qed
  qed
qed

subsection \<open>The four running invariants at a launch's initial state\<close>

text \<open>Launching the inner DFS from a fresh vertex @{term s} marks @{term s} on-stack and clears the
      three stacks; the flow and iterators are inherited. Hence @{const af_pristine}, @{const af_vrank},
      @{const af_rankok} and @{const af_scanres} of the launched configuration reduce to conditions on
      the inherited data: unseen vertices carry no scanned edge (@{term prin}), the finish clock still
      dominates the finished ranks (@{term vrin}), the finish-order invariant held before the launch
      (@{term rk0}), and (for @{const af_scanres}) the pre-launch state has no on-stack vertex
      (@{term noos}) and @{term s} is unseen --- so its pristine iterators leave the (empty) trail
      vacuously scan-resolved.\<close>

lemma af_pristine1_initial:
  assumes si: "st_invar stt" and sV: "s \<in> \<V>"
    and prin: "\<And>v. v \<in> \<V> \<Longrightarrow> st_lookup stt v = Unseen \<Longrightarrow> out_iterated oa v = {} \<and> in_iterated ia v = {}"
  shows "af_pristine1 (AF_DFS_initial fl oa ia stt s)"
proof (unfold af_pristine1_def, intro ballI impI)
  fix v assume vV: "v \<in> \<V>" and "st_lookup (af_state (AF_DFS_initial fl oa ia stt s)) v = Unseen"
  hence "st_lookup (st_upd stt s OnStack) v = Unseen" by (simp add: AF_DFS_initial_def)
  hence vun: "st_lookup stt v = Unseen" using si by (auto simp: state_arr.fixed_univ_map_upd[OF si sV] split: if_splits)
  thus "out_iterated (af_out_arr (AF_DFS_initial fl oa ia stt s)) v = {} \<and>
        in_iterated (af_in_arr (AF_DFS_initial fl oa ia stt s)) v = {}"
    using prin vV by (simp add: AF_DFS_initial_def)
qed

text \<open>The combined @{const af_pristine} at a launch's initial state: the first clause reduces to the
      inherited unseen-iterators condition (@{thm [source] af_pristine1_initial}); the self-loop clause
      is inherited from the pre-launch iterators/flow (@{term prsl}), since a launch copies the flow and
      iterator arrays verbatim.\<close>

lemma af_pristine_initial:
  assumes si: "st_invar stt" and sV: "s \<in> \<V>"
    and prin: "\<And>v. v \<in> \<V> \<Longrightarrow> st_lookup stt v = Unseen \<Longrightarrow> out_iterated oa v = {} \<and> in_iterated ia v = {}"
    and prsl: "\<And>a. a \<in> out_iterated oa (fst a) \<or> a \<in> in_iterated ia (snd a) \<Longrightarrow>
                    af_arc_free fl a \<Longrightarrow> fst a \<noteq> snd a"
    and prsl3: "\<And>a. a \<in> out_iterated oa (fst a) \<or> a \<in> in_iterated ia (snd a) \<Longrightarrow> fst a = snd a \<Longrightarrow>
                    (0 \<le> \<c> a \<longrightarrow> flow_lookup fl a = 0) \<and> (\<c> a < 0 \<longrightarrow> flow_lookup fl a = cap a)"
  shows "af_pristine (AF_DFS_initial fl oa ia stt s)"
proof (unfold af_pristine_def, intro conjI)
  show "af_pristine1 (AF_DFS_initial fl oa ia stt s)" using af_pristine1_initial[OF si sV prin] .
  show "\<forall>a. af_scanned (AF_DFS_initial fl oa ia stt s) a \<longrightarrow> af_arc_free (af_flow (AF_DFS_initial fl oa ia stt s)) a \<longrightarrow> fst a \<noteq> snd a"
  proof (intro allI impI)
    fix a assume "af_scanned (AF_DFS_initial fl oa ia stt s) a"
      and "af_arc_free (af_flow (AF_DFS_initial fl oa ia stt s)) a"
    hence "a \<in> out_iterated oa (fst a) \<or> a \<in> in_iterated ia (snd a)"
      and "af_arc_free fl a" by (simp_all add: af_scanned_def AF_DFS_initial_def)
    thus "fst a \<noteq> snd a" using prsl by blast
  qed
  show "\<forall>a. af_scanned (AF_DFS_initial fl oa ia stt s) a \<longrightarrow> fst a = snd a \<longrightarrow>
            (0 \<le> \<c> a \<longrightarrow> flow_lookup (af_flow (AF_DFS_initial fl oa ia stt s)) a = 0)
          \<and> (\<c> a < 0 \<longrightarrow> flow_lookup (af_flow (AF_DFS_initial fl oa ia stt s)) a = cap a)"
  proof (intro allI impI)
    fix a assume "af_scanned (AF_DFS_initial fl oa ia stt s) a" and sl: "fst a = snd a"
    hence it: "a \<in> out_iterated oa (fst a) \<or> a \<in> in_iterated ia (snd a)"
      by (simp add: af_scanned_def AF_DFS_initial_def)
    have fleq: "af_flow (AF_DFS_initial fl oa ia stt s) = fl" by (simp add: AF_DFS_initial_def)
    show "(0 \<le> \<c> a \<longrightarrow> flow_lookup (af_flow (AF_DFS_initial fl oa ia stt s)) a = 0)
        \<and> (\<c> a < 0 \<longrightarrow> flow_lookup (af_flow (AF_DFS_initial fl oa ia stt s)) a = cap a)"
      unfolding fleq using prsl3[OF it sl] by simp
  qed
qed

lemma af_vrank_initial:
  assumes si: "st_invar stt" and sV: "s \<in> \<V>"
    and vrin: "\<And>u. u \<in> \<V> \<Longrightarrow> st_lookup stt u = Finished \<Longrightarrow> rk u < (c :: nat)"
    and vinj: "inj_on rk {v\<in>\<V>. st_lookup stt v = Finished}"
  shows "af_vrank (AF_DFS_initial fl oa ia stt s) rk c"
proof -
  have fin: "\<And>u. st_lookup (af_state (AF_DFS_initial fl oa ia stt s)) u = Finished \<Longrightarrow> st_lookup stt u = Finished"
  proof -
    fix u assume "st_lookup (af_state (AF_DFS_initial fl oa ia stt s)) u = Finished"
    hence "st_lookup (st_upd stt s OnStack) u = Finished" by (simp add: AF_DFS_initial_def)
    thus "st_lookup stt u = Finished" using si by (auto simp: state_arr.fixed_univ_map_upd[OF si sV] split: if_splits)
  qed
  show ?thesis
  proof (unfold af_vrank_def, intro conjI ballI impI)
    fix u assume uV: "u \<in> \<V>" and "st_lookup (af_state (AF_DFS_initial fl oa ia stt s)) u = Finished"
    thus "rk u < c" using fin vrin uV by blast
  next
    have sub: "{v\<in>\<V>. st_lookup (af_state (AF_DFS_initial fl oa ia stt s)) v = Finished} \<subseteq> {v\<in>\<V>. st_lookup stt v = Finished}"
      using fin by auto
    show "inj_on rk {v\<in>\<V>. st_lookup (af_state (AF_DFS_initial fl oa ia stt s)) v = Finished}"
      using inj_on_subset[OF vinj sub] .
  qed
qed

lemma af_rankok_initial:
  assumes si: "st_invar stt" and sV: "s \<in> \<V>" and s_un: "st_lookup stt s = Unseen"
    and rk0: "af_rankok st0 rk" and fl_eq: "af_flow st0 = fl" and st_eq: "af_state st0 = stt"
  shows "af_rankok (AF_DFS_initial fl oa ia stt s) rk"
proof (unfold af_rankok_def, intro ballI allI impI)
  let ?ini = "AF_DFS_initial fl oa ia stt s"
  fix v a1 a2
  assume vV: "v \<in> \<V>"
    and vf: "st_lookup (af_state ?ini) v = Finished"
    and a1: "a1 \<in> \<E>" "af_arc_free (af_flow ?ini) a1" "v \<in> {fst a1, snd a1}" "af_hgt ?ini rk v a1"
    and a2: "a2 \<in> \<E>" "af_arc_free (af_flow ?ini) a2" "v \<in> {fst a2, snd a2}" "af_hgt ?ini rk v a2"
  have stlk: "st_lookup (af_state ?ini) = (\<lambda>w. if w = s then OnStack else st_lookup (af_state st0) w)"
    using si st_eq by (auto simp: AF_DFS_initial_def state_arr.fixed_univ_map_upd[OF si sV] st_eq)
  have vf0: "st_lookup (af_state st0) v = Finished" using vf by (simp add: stlk split: if_split_asm)
  have hgt: "\<And>a. af_hgt ?ini rk v a = af_hgt st0 rk v a"
    using s_un st_eq by (auto simp: af_hgt_def stlk)
  have free: "\<And>a. af_arc_free (af_flow ?ini) a = af_arc_free (af_flow st0) a"
    using fl_eq by (simp add: AF_DFS_initial_def)
  show "a1 = a2" using rk0 vf0 a1 a2 hgt free vV unfolding af_rankok_def Ball_def by metis
qed

lemma af_scanres_initial:
  assumes si: "st_invar stt" and sV: "s \<in> \<V>"
    and noos: "\<And>w. w \<in> \<V> \<Longrightarrow> st_lookup stt w \<noteq> OnStack"
    and prin: "\<And>v. v \<in> \<V> \<Longrightarrow> st_lookup stt v = Unseen \<Longrightarrow> out_iterated oa v = {} \<and> in_iterated ia v = {}"
    and s_un: "st_lookup stt s = Unseen"
  shows "af_scanres (AF_DFS_initial fl oa ia stt s)"
proof (unfold af_scanres_def, intro ballI allI impI)
  let ?ini = "AF_DFS_initial fl oa ia stt s"
  fix v a
  assume vV: "v \<in> \<V>"
    and vos: "st_lookup (af_state ?ini) v = OnStack" and aE: "a \<in> \<E>"
    and scan: "af_scanned ?ini a" and inc: "v \<in> {fst a, snd a}"
    and free: "af_arc_free (af_flow ?ini) a"
    and farnf: "st_lookup (af_state ?ini) (if fst a = v then snd a else fst a) \<noteq> Finished"
  have stlk: "st_lookup (af_state ?ini) = (\<lambda>w. if w = s then OnStack else st_lookup stt w)"
    using si by (auto simp: AF_DFS_initial_def state_arr.fixed_univ_map_upd[OF si sV])
  have vs: "v = s" using vos noos vV by (auto simp: stlk split: if_split_asm)
  let ?far = "if fst a = v then snd a else fst a"
  have farnf': "st_lookup stt ?far \<noteq> Finished" using farnf s_un by (auto simp: stlk split: if_split_asm)
  have pris: "\<And>e. e \<in> {fst a, snd a} \<Longrightarrow> out_iterated oa e = {} \<and> in_iterated ia e = {}"
  proof -
    fix e assume e: "e \<in> {fst a, snd a}"
    have eV: "e \<in> \<V>" using e fst_E_V[OF aE] snd_E_V[OF aE] by auto
    have "st_lookup stt e = Unseen"
    proof (cases "e = s")
      case True thus ?thesis using s_un by simp
    next
      case False
      have "e = ?far" using e vs False inc by (auto split: if_splits)
      hence "st_lookup stt e \<noteq> Finished" using farnf' by simp
      thus ?thesis using noos eV by (cases "st_lookup stt e") auto
    qed
    thus "out_iterated oa e = {} \<and> in_iterated ia e = {}" using prin eV by simp
  qed
  have "\<not> af_scanned ?ini a" using pris by (auto simp: af_scanned_def AF_DFS_initial_def)
  thus "a \<in> set (af_estack ?ini)" using scan by blast
qed

subsection \<open>The forest keystone: the finish-order invariant forbids a free scanned cycle\<close>

text \<open>The endpoints of a residual arc are exactly the endpoints of its underlying arc, and (for a
      non-self-loop) the @{const af_hgt} ``other endpoint'' picks out the arc's far residual endpoint.\<close>

lemma fstv_sndv_oedge: "{fstv e, sndv e} = {fst (oedge e), snd (oedge e)}"
  by (cases e) auto

lemma af_hgt_other_fstv:
  assumes "fst (oedge e) \<noteq> snd (oedge e)" and "v = fstv e"
  shows "(if fst (oedge e) = v then snd (oedge e) else fst (oedge e)) = sndv e"
  using assms by (cases e) auto

lemma af_hgt_other_sndv:
  assumes "fst (oedge e) \<noteq> snd (oedge e)" and "v = sndv e"
  shows "(if fst (oedge e) = v then snd (oedge e) else fst (oedge e)) = fstv e"
  using assms by (cases e) auto

text \<open>Consecutive residual arcs of a @{const prepath} share a vertex: the head of arc @{term i} is the
      tail of arc @{term \<open>Suc i\<close>}. Extracted from the two shapes of @{const awalk_verts}.\<close>

lemma prepath_consec:
  assumes pp: "prepath C" and i: "Suc i < length C"
  shows "sndv (C ! i) = fstv (C ! Suc i)"
proof -
  let ?p = "map to_vertex_pair C"
  have ne: "C \<noteq> []" using pp by (simp add: prepath_def)
  have cas: "cas (fstv (hd C)) ?p (sndv (last C))" using pp by (auto simp: prepath_def awalk_def)
  have iv: "Suc i < length ?p" using i by simp
  have v1: "awalk_verts (fstv (hd C)) ?p = map prod.fst ?p @ [prod.snd (last ?p)]"
    using ne by (simp add: awalk_verts_conv)
  have v2: "awalk_verts (fstv (hd C)) ?p = prod.fst (hd ?p) # map prod.snd ?p"
    using awalk_verts_conv'[OF cas] ne by simp
  have A: "awalk_verts (fstv (hd C)) ?p ! Suc i = fstv (C ! Suc i)"
    using v1 iv i by (simp add: nth_append to_vertex_pair_fst_snd)
  have B: "awalk_verts (fstv (hd C)) ?p ! Suc i = sndv (C ! i)"
    using v2 iv i by (simp add: to_vertex_pair_fst_snd)
  show ?thesis using A B by simp
qed

text \<open>The keystone. Given a closed @{const prepath} of distinct-underlying, free residual arcs, all of
      whose vertices are @{term Finished} and none of whose underlying arcs is a self-loop, the
      minimum-rank vertex carries two \emph{distinct} incident free arcs (its cyclic
      predecessor and successor) whose far endpoints both outrank it (@{const af_hgt}) --- contradicting
      @{const af_rankok}, which allows a finished vertex at most one such arc.\<close>

lemma AF_forest_from_cycle:
  assumes ok: "af_rankok st rk"
    and inj: "inj_on rk {v\<in>\<V>. st_lookup (af_state st) v = Finished}"
    and allfin: "\<And>e. e \<in> set C \<Longrightarrow> st_lookup (af_state st) (fstv e) = Finished \<and> st_lookup (af_state st) (sndv e) = Finished"
    and nsl: "\<And>e. e \<in> set C \<Longrightarrow> fst (oedge e) \<noteq> snd (oedge e)"
    and pp: "prepath C" and freeC: "\<And>e. e \<in> set C \<Longrightarrow> af_arc_free (af_flow st) (oedge e)"
    and dist: "distinct (map oedge C)" and clo: "fstv (hd C) = sndv (last C)" and sub: "set C \<subseteq> \<EE>"
    and rknat: "\<And>v. (rk v :: nat) = rk v"
  shows False
proof -
  let ?n = "length C"
  have ne: "C \<noteq> []" using pp by (simp add: prepath_def)
  have npos: "0 < ?n" using ne by simp
  define f where "f i = rk (fstv (C ! i))" for i
  define m where "m = Min (f ` {0..<?n})"
  have "m \<in> f ` {0..<?n}" unfolding m_def using npos by (intro Min_in) auto
  then obtain i0 where i0n: "i0 < ?n" and fi0: "f i0 = m" by auto
  have i0min: "\<And>i. i < ?n \<Longrightarrow> m \<le> f i" unfolding m_def by (intro Min_le) auto
  let ?v0 = "fstv (C ! i0)"
  have eoutmem: "C ! i0 \<in> set C" using i0n by simp
  have cycV: "\<And>e. e \<in> set C \<Longrightarrow> fstv e \<in> \<V> \<and> sndv e \<in> \<V>"
  proof -
    fix e assume e: "e \<in> set C"
    have oeE: "oedge e \<in> \<E>" using sub e o_edge_res by auto
    thus "fstv e \<in> \<V> \<and> sndv e \<in> \<V>" using fst_E_V[OF oeE] snd_E_V[OF oeE] by (cases e) auto
  qed
  have n2: "2 \<le> ?n"
  proof (rule ccontr)
    assume a: "\<not> 2 \<le> ?n"
    hence len1: "?n = 1" using npos by linarith
    have "\<exists>x. C = [x]" using len1 by (cases C) auto
    then obtain x where cx: "C = [x]" by blast
    have "fstv x = sndv x" using clo cx by simp
    hence "fst (oedge x) = snd (oedge x)" using fstv_sndv_oedge[of x] by (cases x) auto
    moreover have "x \<in> set C" using cx by simp
    ultimately show False using nsl by simp
  qed
  define i1 where "i1 = (if i0 = 0 then ?n - 1 else i0 - 1)"
  have i1n: "i1 < ?n" using npos i0n by (auto simp: i1_def)
  have i1ne: "i1 \<noteq> i0" using n2 i0n by (auto simp: i1_def)
  have einmem: "C ! i1 \<in> set C" using i1n by simp
  have sin: "sndv (C ! i1) = ?v0"
  proof (cases "i0 = 0")
    case True
    hence i1e: "i1 = ?n - 1" by (simp add: i1_def)
    hence "sndv (C ! i1) = sndv (last C)" using npos by (simp add: last_conv_nth ne)
    also have "\<dots> = fstv (hd C)" using clo by simp
    also have "\<dots> = ?v0" using True by (simp add: hd_conv_nth ne)
    finally show ?thesis .
  next
    case False
    hence si1: "Suc i1 = i0" by (auto simp: i1_def)
    thus ?thesis using prepath_consec[OF pp, of i1] i0n by simp
  qed
  define k where "k = (if Suc i0 < ?n then Suc i0 else 0)"
  have kn: "k < ?n" using npos i0n by (auto simp: k_def)
  have sout: "sndv (C ! i0) = fstv (C ! k)"
  proof (cases "Suc i0 < ?n")
    case True thus ?thesis using prepath_consec[OF pp, of i0] by (simp add: k_def)
  next
    case False
    hence i0e: "i0 = ?n - 1" using i0n by linarith
    have "sndv (C ! i0) = sndv (last C)" using i0e npos by (simp add: last_conv_nth ne)
    also have "\<dots> = fstv (hd C)" using clo by simp
    also have "\<dots> = fstv (C ! k)" using False i0n by (simp add: hd_conv_nth ne k_def)
    finally show ?thesis .
  qed
  have v0fin: "st_lookup (af_state st) ?v0 = Finished" using allfin[OF eoutmem] by simp
  have soutfin: "st_lookup (af_state st) (sndv (C ! i0)) = Finished" using allfin[OF eoutmem] by simp
  have finfin: "st_lookup (af_state st) (fstv (C ! i1)) = Finished" using allfin[OF einmem] by simp
  have out_ne: "sndv (C ! i0) \<noteq> ?v0" using nsl[OF eoutmem] fstv_sndv_oedge[of "C ! i0"] by (cases "C ! i0") auto
  have "rk (sndv (C ! i0)) = f k" using sout by (simp add: f_def)
  moreover have "f i0 \<le> f k" using i0min[OF kn] fi0 by simp
  ultimately have "rk ?v0 \<le> rk (sndv (C ! i0))" by (simp add: f_def)
  moreover have "rk ?v0 \<noteq> rk (sndv (C ! i0))"
    using inj v0fin soutfin out_ne cycV[OF eoutmem] by (auto simp: inj_on_def)
  ultimately have out_gt: "rk ?v0 < rk (sndv (C ! i0))" by simp
  have in_ne: "fstv (C ! i1) \<noteq> ?v0" using nsl[OF einmem] fstv_sndv_oedge[of "C ! i1"] sin by (cases "C ! i1") auto
  have "rk ?v0 \<le> rk (fstv (C ! i1))" using i0min[OF i1n] fi0 by (simp add: f_def)
  moreover have "rk ?v0 \<noteq> rk (fstv (C ! i1))"
    using inj v0fin finfin in_ne cycV[OF eoutmem] cycV[OF einmem] by (auto simp: inj_on_def)
  ultimately have in_gt: "rk ?v0 < rk (fstv (C ! i1))" by simp
  have hgt_out: "af_hgt st rk ?v0 (oedge (C ! i0))"
    using out_gt af_hgt_other_fstv[OF nsl[OF eoutmem] refl] by (simp add: af_hgt_def)
  have hgt_in: "af_hgt st rk ?v0 (oedge (C ! i1))"
    using in_gt af_hgt_other_sndv[OF nsl[OF einmem] sin[symmetric]] by (simp add: af_hgt_def)
  have oe_out: "oedge (C ! i0) \<in> \<E>" using sub eoutmem o_edge_res by auto
  have oe_in: "oedge (C ! i1) \<in> \<E>" using sub einmem o_edge_res by auto
  have inc_out: "?v0 \<in> {fst (oedge (C ! i0)), snd (oedge (C ! i0))}"
    using fstv_sndv_oedge[of "C ! i0"] by auto
  have inc_in: "?v0 \<in> {fst (oedge (C ! i1)), snd (oedge (C ! i1))}"
    using fstv_sndv_oedge[of "C ! i1"] sin by auto
  have v0V: "?v0 \<in> \<V>" using inc_out fst_E_V[OF oe_out] snd_E_V[OF oe_out] by auto
  have "oedge (C ! i0) = oedge (C ! i1)"
    using ok v0fin v0V oe_out freeC[OF eoutmem] inc_out hgt_out oe_in freeC[OF einmem] inc_in hgt_in
    unfolding af_rankok_def Ball_def by blast
  moreover have "oedge (C ! i0) \<noteq> oedge (C ! i1)"
  proof
    assume "oedge (C ! i0) = oedge (C ! i1)"
    hence "map oedge C ! i0 = map oedge C ! i1" using i0n i1n by simp
    hence "i0 = i1" using dist i0n i1n by (metis length_map nth_eq_iff_index_eq)
    thus False using i1ne by simp
  qed
  ultimately show False by simp
qed

text \<open>Packaged as @{const AF_forest}: with the finish-order invariant @{const af_rankok}, injective
      ranking on finished vertices, @{const af_pristine} (no free scanned self-loop) and \emph{every}
      graph vertex finished, no free scanned closed trail exists. The all-finished premise is what the
      outer loop supplies at @{const make_acyclic}'s end.\<close>

lemma AF_forest_from_cycle_rankok:
  assumes ok: "af_rankok st rk"
    and inj: "inj_on rk {v\<in>\<V>. st_lookup (af_state st) v = Finished}"
    and allfin: "\<And>v. v \<in> \<V> \<Longrightarrow> st_lookup (af_state st) v = Finished"
    and pr: "af_pristine st"
    and rknat: "\<And>v. (rk v :: nat) = rk v"
  shows "AF_forest st"
proof (unfold AF_forest_def, rule notI, elim exE conjE)
  fix C
  assume pp: "prepath C"
    and sc: "\<forall>e\<in>set C. af_arc_free (af_flow st) (oedge e) \<and> af_scanned st (oedge e)"
    and dist: "distinct (map oedge C)" and clo: "fstv (hd C) = sndv (last C)" and sub: "set C \<subseteq> \<EE>"
  have freeC: "\<And>e. e \<in> set C \<Longrightarrow> af_arc_free (af_flow st) (oedge e)" using sc by auto
  have scanC: "\<And>e. e \<in> set C \<Longrightarrow> af_scanned st (oedge e)" using sc by auto
  have nsl: "\<And>e. e \<in> set C \<Longrightarrow> fst (oedge e) \<noteq> snd (oedge e)"
    using pr freeC scanC by (auto simp: af_pristine_def)
  have allfinC: "\<And>e. e \<in> set C \<Longrightarrow> st_lookup (af_state st) (fstv e) = Finished \<and> st_lookup (af_state st) (sndv e) = Finished"
  proof -
    fix e assume e: "e \<in> set C"
    have oeE: "oedge e \<in> \<E>" using sub e o_edge_res by auto
    have "fstv e \<in> \<V> \<and> sndv e \<in> \<V>" using fst_E_V[OF oeE] snd_E_V[OF oeE] by (cases e) auto
    thus "st_lookup (af_state st) (fstv e) = Finished \<and> st_lookup (af_state st) (sndv e) = Finished"
      using allfin by simp
  qed
  show False using AF_forest_from_cycle[OF ok inj allfinC nsl pp freeC dist clo sub rknat] .
qed

lemma AF_forest_from_rankok:
  assumes ok: "af_rankok st rk"
    and vr: "af_vrank st rk c"
    and allfin: "\<And>v. v \<in> \<V> \<Longrightarrow> st_lookup (af_state st) v = Finished"
    and pr: "af_pristine st"
  shows "AF_forest st"
proof -
  have inj: "inj_on rk {v\<in>\<V>. st_lookup (af_state st) v = Finished}" using vr by (simp add: af_vrank_def)
  have rknat: "\<And>v. (rk v :: nat) = rk v" by simp
  show ?thesis using AF_forest_from_cycle_rankok[OF ok inj allfin pr rknat] .
qed

subsection \<open>Threading the finish-order invariant through the outer loop and closing acyclicity\<close>

text \<open>@{const af_pristine} is preserved by a whole (bounded) inner DFS, and --- alongside the
      finish-clock evolution tracked by @{const AF_DFS_i} --- so is @{const af_vrank}. These lift the
      per-step preservation lemmas to the DFS return.\<close>

lemma AF_DFS_pristine:
  assumes dom: "AF_DFS_dom st" and mi0: "multigraph_inv out_arr in_arr"
    and fresh: "\<forall>u. out_iterated out_arr u = {} \<and> in_iterated in_arr u = {}"
  shows "AF_inv st \<longrightarrow> af_pristine st \<longrightarrow> \<not> af_unbounded (AF_DFS st) \<longrightarrow> af_pristine (AF_DFS st)"
proof (induction rule: AF_DFS_induct[OF dom])
  case IH: (1 st)
  show ?case
  proof (intro impI)
    assume inv: "AF_inv st" and pr: "af_pristine st" and nu: "\<not> af_unbounded (AF_DFS st)"
    from inv have i1: "AF_invar_1 st" and i2: "AF_invar_2 st" by (auto simp: AF_inv_def)
    have si: "st_invar (af_state st)" using i1 by (simp add: AF_invar_1_def)
    show "af_pristine (AF_DFS st)"
    proof (rule AF_DFS_cases[where st = st])
      assume c: "AF_DFS_call_1_conds st"
      have dfeq: "AF_DFS (AF_DFS_upd1 st) = AF_DFS st" using c by (simp add: AF_DFS_simps[OF IH(1)])
      have nu1: "\<not> af_unbounded (AF_DFS_upd1 st)" using nub_step1[OF IH(1) c nu] .
      have "af_pristine (AF_DFS_upd1 st)" using af_pristine_upd1[OF inv c fresh nu1 pr] .
      moreover have "AF_inv (AF_DFS_upd1 st)" using AF_inv_holds_1[OF mi0 c inv] .
      moreover have "\<not> af_unbounded (AF_DFS (AF_DFS_upd1 st))" using nu dfeq by simp
      ultimately show ?thesis using IH(2)[OF c] dfeq by auto
    next
      assume c: "AF_DFS_call_2_conds st"
      have dfeq: "AF_DFS (AF_DFS_upd2 st) = AF_DFS st" using c 
        by (simp add: AF_DFS_simps[OF IH(1)])
      have nu1: "\<not> af_unbounded (AF_DFS_upd2 st)" using nub_step2[OF IH(1) c nu] .
      have "af_pristine (AF_DFS_upd2 st)" using af_pristine_upd2[OF inv c fresh nu1 pr] .
      moreover have "AF_inv (AF_DFS_upd2 st)" using AF_inv_holds_2[OF mi0 c inv] .
      moreover have "\<not> af_unbounded (AF_DFS (AF_DFS_upd2 st))" using nu dfeq by simp
      ultimately show ?thesis using IH(3)[OF c] dfeq by auto
    next
      assume c: "AF_DFS_call_3_conds st"
      have dfeq: "AF_DFS (AF_DFS_upd3 st) = AF_DFS st" using c 
        by (simp add: AF_DFS_simps[OF IH(1)])
      have "af_pristine (AF_DFS_upd3 st)" using af_pristine_upd3[OF inv c pr] .
      moreover have "AF_inv (AF_DFS_upd3 st)" using AF_inv_holds_3[OF c inv] .
      moreover have "\<not> af_unbounded (AF_DFS (AF_DFS_upd3 st))" using nu dfeq by simp
      ultimately show ?thesis using IH(4)[OF c] dfeq by auto
    next
      assume c: "AF_DFS_ret_conds st"
      thus ?thesis using pr 
        by (simp add: AF_DFS_simps[OF IH(1)] AF_DFS_ret_def)
    qed
  qed
qed

lemma af_vrank_AF_DFS_i:
  assumes dom: "AF_DFS_dom st" and mi0: "multigraph_inv out_arr in_arr"
    and fresh: "\<forall>u. out_iterated out_arr u = {} \<and> in_iterated in_arr u = {}"
  shows "\<forall>rk c. AF_inv st \<longrightarrow> af_pristine st \<longrightarrow> af_scanres st \<longrightarrow> af_rankok st rk \<longrightarrow> af_vrank st rk c \<longrightarrow>
         \<not> af_unbounded (AF_DFS st) \<longrightarrow>
         (\<exists>r cc. AF_DFS_i st rk c = (AF_DFS st, r, cc) \<and> af_vrank (AF_DFS st) r cc)"
proof (induction rule: AF_DFS_induct[OF dom])
  case (1 st)
  show ?case
  proof (intro allI impI)
    fix rk c
    assume inv: "AF_inv st" and pr: "af_pristine st" and sr: "af_scanres st"
      and ok: "af_rankok st rk" and vr: "af_vrank st rk c" and nub: "\<not> af_unbounded (AF_DFS st)"
    from inv have i1: "AF_invar_1 st" and i2: "AF_invar_2 st" by (auto simp: AF_inv_def)
    have si: "st_invar (af_state st)" using i1 by (simp add: AF_invar_1_def)
    have di: "AF_DFS_i_dom (st, rk, c)" using AF_DFS_i_dom_all[OF 1(1)] by blast
    show "\<exists>r cc. AF_DFS_i st rk c = (AF_DFS st, r, cc) \<and> af_vrank (AF_DFS st) r cc"
    proof (rule AF_DFS_cases[where st = st])
      assume ca: "AF_DFS_call_1_conds st"
      have eq: "AF_DFS_i st rk c = AF_DFS_i (AF_DFS_upd1 st) rk c"
        using ca by (auto simp: AF_DFS_i.psimps[OF di] AF_DFS_upd1_def Let_def elim!: call_cond_elims)
      have dfeq: "AF_DFS (AF_DFS_upd1 st) = AF_DFS st" using ca by (simp add: AF_DFS_simps[OF 1(1)])
      have nub1: "\<not> af_unbounded (AF_DFS_upd1 st)" using nub_step1[OF 1(1) ca nub] .
      have nub': "\<not> af_unbounded (AF_DFS (AF_DFS_upd1 st))" using nub dfeq by simp
      have "\<exists>r cc. AF_DFS_i (AF_DFS_upd1 st) rk c = (AF_DFS (AF_DFS_upd1 st), r, cc) \<and> af_vrank (AF_DFS (AF_DFS_upd1 st)) r cc"
        using 1(2)[OF ca] AF_inv_holds_1[OF mi0 ca inv] af_pristine_upd1[OF inv ca fresh nub1 pr]
              af_scanres_upd1[OF inv ca fresh af_pristine_imp1[OF pr] sr nub1] af_rankok_upd1[OF inv ca ok]
              af_vrank_upd1[OF inv ca vr] nub' by blast
      then obtain r cc where "AF_DFS_i (AF_DFS_upd1 st) rk c = (AF_DFS (AF_DFS_upd1 st), r, cc)"
        and vrk: "af_vrank (AF_DFS (AF_DFS_upd1 st)) r cc" by blast
      thus "\<exists>r cc. AF_DFS_i st rk c = (AF_DFS st, r, cc) \<and> af_vrank (AF_DFS st) r cc" using eq dfeq by auto
    next
      assume ca: "AF_DFS_call_2_conds st"
      have eq: "AF_DFS_i st rk c = AF_DFS_i (AF_DFS_upd2 st) rk c"
        using ca by (auto simp: AF_DFS_i.psimps[OF di] AF_DFS_upd2_def Let_def elim!: call_cond_elims)
      have dfeq: "AF_DFS (AF_DFS_upd2 st) = AF_DFS st" using ca by (simp add: AF_DFS_simps[OF 1(1)])
      have nub1: "\<not> af_unbounded (AF_DFS_upd2 st)" using nub_step2[OF 1(1) ca nub] .
      have nub': "\<not> af_unbounded (AF_DFS (AF_DFS_upd2 st))" using nub dfeq by simp
      have "\<exists>r cc. AF_DFS_i (AF_DFS_upd2 st) rk c = (AF_DFS (AF_DFS_upd2 st), r, cc) \<and> af_vrank (AF_DFS (AF_DFS_upd2 st)) r cc"
        using 1(3)[OF ca] AF_inv_holds_2[OF mi0 ca inv] af_pristine_upd2[OF inv ca fresh nub1 pr]
              af_scanres_upd2[OF inv ca fresh af_pristine_imp1[OF pr] sr nub1] af_rankok_upd2[OF inv ca ok]
              af_vrank_upd2[OF inv ca vr] nub' by blast
      then obtain r cc where "AF_DFS_i (AF_DFS_upd2 st) rk c = (AF_DFS (AF_DFS_upd2 st), r, cc)"
        and vrk: "af_vrank (AF_DFS (AF_DFS_upd2 st)) r cc" by blast
      thus "\<exists>r cc. AF_DFS_i st rk c = (AF_DFS st, r, cc) \<and> af_vrank (AF_DFS st) r cc" using eq dfeq by auto
    next
      assume ca: "AF_DFS_call_3_conds st"
      have eq: "AF_DFS_i st rk c = AF_DFS_i (AF_DFS_upd3 st) (rk(hd (af_vstack st) := c)) (Suc c)"
        using ca by (auto simp: AF_DFS_i.psimps[OF di] AF_DFS_upd3_def elim!: call_cond_elims)
      have dfeq: "AF_DFS (AF_DFS_upd3 st) = AF_DFS st" using ca
        by (simp add: AF_DFS_simps[OF 1(1)])
      have ne: "af_vstack st \<noteq> []" using ca by (auto elim!: call_cond_elims)
      have vrank': "\<And>u. u \<in> \<V> \<Longrightarrow> st_lookup (af_state st) u = Finished \<Longrightarrow> rk u < c" using vr by (auto simp: af_vrank_def)
      have nub': "\<not> af_unbounded (AF_DFS (AF_DFS_upd3 st))" using nub dfeq by simp
      have "\<exists>r cc. AF_DFS_i (AF_DFS_upd3 st) (rk(hd (af_vstack st) := c)) (Suc c) = (AF_DFS (AF_DFS_upd3 st), r, cc)
              \<and> af_vrank (AF_DFS (AF_DFS_upd3 st)) r cc"
        using 1(4)[OF ca] AF_inv_holds_3[OF ca inv] af_pristine_upd3[OF inv ca pr]
              af_scanres_upd3[OF inv ca sr] af_rankok_upd3[OF inv ca ok sr vrank']
              af_vrank_upd3[OF inv ca vr] nub' by blast
      then obtain r cc where "AF_DFS_i (AF_DFS_upd3 st) (rk(hd (af_vstack st) := c)) (Suc c) = (AF_DFS (AF_DFS_upd3 st), r, cc)"
        and vrk: "af_vrank (AF_DFS (AF_DFS_upd3 st)) r cc" by blast
      thus "\<exists>r cc. AF_DFS_i st rk c = (AF_DFS st, r, cc) \<and> af_vrank (AF_DFS st) r cc" using eq dfeq by auto
    next
      assume ca: "AF_DFS_ret_conds st"
      hence eq: "AF_DFS_i st rk c = (st, rk, c)"
        by (auto simp: AF_DFS_i.psimps[OF di] AF_DFS_ret_conds_def split: list.splits)
      have "AF_DFS st = st" using ca 
        by (simp add: AF_DFS_simps[OF 1(1)] AF_DFS_ret_def)
      thus "\<exists>r cc. AF_DFS_i st rk c = (AF_DFS st, r, cc) \<and> af_vrank (AF_DFS st) r cc" using eq vr by auto
    qed
  qed
qed

text \<open>Outer-loop shadows of the finish-order invariants, read off the accumulated flow / vertex-state /
      iterator arrays of the @{typ \<open>(_,_,_,_,_) AF_state\<close>}. They agree with their \<open>AF_DFS_state\<close>
      counterparts whenever the four carried components coincide (bridge lemmas below), which is what the
      launch step establishes.\<close>

definition "AFF_pristine st \<longleftrightarrow>
  (\<forall>v\<in>\<V>. st_lookup (aff_state st) v = Unseen \<longrightarrow>
       out_iterated (aff_out_arr st) v = {} \<and> in_iterated (aff_in_arr st) v = {}) \<and>
  (\<forall>a. (a \<in> out_iterated (aff_out_arr st) (fst a) \<or> a \<in> in_iterated (aff_in_arr st) (snd a)) \<longrightarrow>
       af_arc_free (aff_flow st) a \<longrightarrow> fst a \<noteq> snd a) \<and>
  (\<forall>a. (a \<in> out_iterated (aff_out_arr st) (fst a) \<or> a \<in> in_iterated (aff_in_arr st) (snd a)) \<longrightarrow>
       fst a = snd a \<longrightarrow>
       (0 \<le> \<c> a \<longrightarrow> flow_lookup (aff_flow st) a = 0)
     \<and> (\<c> a < 0 \<longrightarrow> flow_lookup (aff_flow st) a = cap a))"

definition "AFF_hgt st rk v a \<longleftrightarrow>
  (st_lookup (aff_state st) (if fst a = v then snd a else fst a) \<noteq> Finished
   \<or> rk (if fst a = v then snd a else fst a) > rk v)"

definition "AFF_rankok st rk \<longleftrightarrow>
  (\<forall>v\<in>\<V>. st_lookup (aff_state st) v = Finished \<longrightarrow>
     (\<forall>a1 a2. a1 \<in> \<E> \<longrightarrow> af_arc_free (aff_flow st) a1 \<longrightarrow> v \<in> {fst a1, snd a1} \<longrightarrow> AFF_hgt st rk v a1 \<longrightarrow>
              a2 \<in> \<E> \<longrightarrow> af_arc_free (aff_flow st) a2 \<longrightarrow> v \<in> {fst a2, snd a2} \<longrightarrow> AFF_hgt st rk v a2 \<longrightarrow> a1 = a2))"

definition "AFF_vrank st rk c \<longleftrightarrow>
  (\<forall>u\<in>\<V>. st_lookup (aff_state st) u = Finished \<longrightarrow> rk u < (c::nat)) \<and>
  inj_on rk {v\<in>\<V>. st_lookup (aff_state st) v = Finished}"

definition "AFF_fin2 st rk c \<longleftrightarrow> (\<not> aff_unbounded st \<longrightarrow> AFF_pristine st \<and> AFF_rankok st rk \<and> AFF_vrank st rk c)"

lemma af_AFF_rankok: "af_flow ast = aff_flow st \<Longrightarrow> af_state ast = aff_state st \<Longrightarrow> af_rankok ast rk = AFF_rankok st rk"
  by (simp add: af_rankok_def AFF_rankok_def af_hgt_def AFF_hgt_def)

lemma af_AFF_vrank: "af_state ast = aff_state st \<Longrightarrow> af_vrank ast rk c = AFF_vrank st rk c"
  by (simp add: af_vrank_def AFF_vrank_def)

lemma af_AFF_pristine:
  "af_flow ast = aff_flow st \<Longrightarrow> af_state ast = aff_state st \<Longrightarrow> af_out_arr ast = aff_out_arr st \<Longrightarrow> af_in_arr ast = aff_in_arr st
   \<Longrightarrow> af_pristine ast = AFF_pristine st"
  by (simp add: af_pristine_def af_pristine1_def af_scanned_def AFF_pristine_def)

lemma af_AFF_forest:
  "af_flow ast = aff_flow st \<Longrightarrow> af_out_arr ast = aff_out_arr st \<Longrightarrow> af_in_arr ast = aff_in_arr st
   \<Longrightarrow> AF_forest ast = AFF_forest st"
  by (simp add: AF_forest_def AFF_forest_def af_scanned_def AFF_scanned_def)

text \<open>The outer-level forest keystone: at a state where the finish-order invariants hold and every graph
      vertex is finished, no free scanned closed trail exists. Obtained from @{thm [source] AF_forest_from_rankok}
      on a witness \<open>AF_DFS_state\<close> sharing the four carried components.\<close>

lemma AFF_forest_from_rankok:
  assumes ok: "AFF_rankok st rk" and vr: "AFF_vrank st rk c"
    and allfin: "\<And>v. v \<in> \<V> \<Longrightarrow> st_lookup (aff_state st) v = Finished"
    and pr: "AFF_pristine st"
  shows "AFF_forest st"
proof -
  let ?ast = "\<lparr> af_flow = aff_flow st, af_vstack = [], af_estack = [], af_dstack = [],
     af_out_arr = aff_out_arr st, af_in_arr = aff_in_arr st, af_state = aff_state st, af_unbounded = aff_unbounded st \<rparr>"
  have e1: "af_flow ?ast = aff_flow st" and e2: "af_state ?ast = aff_state st"
    and e3: "af_out_arr ?ast = aff_out_arr st" and e4: "af_in_arr ?ast = aff_in_arr st" by simp_all
  have r: "af_rankok ?ast rk" using ok e1 e2 af_AFF_rankok by blast
  have v: "af_vrank ?ast rk c" using vr e2 af_AFF_vrank by blast
  have p: "af_pristine ?ast" using pr e1 e2 e3 e4 af_AFF_pristine by blast
  have af: "\<And>v. v \<in> \<V> \<Longrightarrow> st_lookup (af_state ?ast) v = Finished" using allfin e2 by simp
  have "AF_forest ?ast" using AF_forest_from_rankok[OF r v af p] .
  moreover have "AF_forest ?ast = AFF_forest st" using af_AFF_forest[OF e1 e3 e4] .
  ultimately show ?thesis by blast
qed

text \<open>Establishing and preserving @{const AFF_fin2} (finish-order structure with an unspecified ranking)
      through the outer loop. Skip preserves it verbatim; the launch reconstructs the ranking from the
      inner DFS via @{thm [source] af_rankok_AF_DFS_i}, @{thm [source] af_vrank_AF_DFS_i},
      @{thm [source] AF_DFS_pristine} and the launch's @{const AF_DFS_initial} lemmas.\<close>

lemma AFF_fin2_cong:
  "aff_flow st' = aff_flow st \<Longrightarrow> aff_state st' = aff_state st \<Longrightarrow> aff_out_arr st' = aff_out_arr st \<Longrightarrow>
   aff_in_arr st' = aff_in_arr st \<Longrightarrow> aff_unbounded st' = aff_unbounded st \<Longrightarrow> AFF_fin2 st' rk c = AFF_fin2 st rk c"
  by (simp add: AFF_fin2_def AFF_pristine_def AFF_rankok_def AFF_vrank_def AFF_hgt_def)

lemma AFF_fin2_holds_1: "AFF_fin2 st rk c \<Longrightarrow> AFF_fin2 (AF_outer_upd1 st) rk c"
  using AFF_fin2_cong[of "AF_outer_upd1 st" st rk c] by (simp add: AF_outer_upd1_def)

lemma AFF_fin2_initial:
  assumes fresh: "\<forall>u. out_iterated out_arr u = {} \<and> in_iterated in_arr u = {}"
  shows "AFF_fin2 (AF_outer_initial f0) (\<lambda>_. 0) 0"
proof (unfold AFF_fin2_def, intro impI conjI)
  have unseen: "\<And>v. v \<in> \<V> \<Longrightarrow> st_lookup (aff_state (AF_outer_initial f0)) v = Unseen"
    by (simp add: AF_outer_initial_def state_init_unseen)
  show "AFF_pristine (AF_outer_initial f0)"
    using unseen fresh by (auto simp: AFF_pristine_def AF_outer_initial_def)
  show "AFF_rankok (AF_outer_initial f0) (\<lambda>_. 0)"
    using unseen by (auto simp: AFF_rankok_def)
  show "AFF_vrank (AF_outer_initial f0) (\<lambda>_. 0) 0"
    using unseen by (auto simp: AFF_vrank_def inj_on_def)
qed

lemma AFF_fin2_holds_2:
  assumes mi0: "multigraph_inv out_arr in_arr"
    and fresh: "\<forall>u. out_iterated out_arr u = {} \<and> in_iterated in_arr u = {}"
    and conds: "AF_outer_call_2_conds st" and inv: "AFF_inv st" and fin: "AFF_fin2 st rk c"
  shows "\<exists>rk' c'. AFF_fin2 (AF_outer_upd2 st) rk' c'"
proof (cases "aff_unbounded (AF_outer_upd2 st)")
  case True
  thus ?thesis by (auto simp: AFF_fin2_def)
next
  case nu: False
  from inv have ff: "flow_invar (aff_flow st)" and sti: "st_invar (aff_state st)"
    and aoi: "out_invar (aff_out_arr st)" and aii: "in_invar (aff_in_arr st)"
    and mii: "multigraph_inv (aff_out_arr st) (aff_in_arr st)" and feas: "af_cap_feasible (aff_flow st)"
    and noos: "\<not> aff_unbounded st \<longrightarrow> (\<forall>w\<in>\<V>. st_lookup (aff_state st) w \<noteq> OnStack)" by (auto simp: AFF_inv_def)
  from conds have nu0: "\<not> aff_unbounded st" and hv: "has_vertex (aff_vit st)"
    and vuns: "st_lookup (aff_state st) (current_vertex (aff_vit st)) = Unseen" by (auto simp: AF_outer_call_2_conds_def)
  let ?v = "current_vertex (aff_vit st)"
  have vV: "?v \<in> \<V>" using vit_current_V[OF inv hv] .
  have noos_all: "\<forall>w\<in>\<V>. st_lookup (aff_state st) w \<noteq> OnStack" using noos nu0 by simp
  have noos_w: "\<And>w. w \<in> \<V> \<Longrightarrow> st_lookup (aff_state st) w \<noteq> OnStack" using noos_all by blast
  have finp: "AFF_pristine st" and finr: "AFF_rankok st rk" and finv: "AFF_vrank st rk c"
    using fin nu0 by (auto simp: AFF_fin2_def)
  let ?init = "AF_DFS_initial (aff_flow st) (aff_out_arr st) (aff_in_arr st) (aff_state st) ?v"
  have invi: "AF_inv ?init" using AF_inv_initial[OF ff sti aoi aii mii vV feas noos_all] .
  have domi: "AF_DFS_dom ?init" using AF_DFS_dom[OF mi0 invi] .
  have nures: "\<not> af_unbounded (AF_DFS ?init)" using nu by (simp add: AF_outer_upd2_def Let_def)
  let ?w = "\<lparr> af_flow = aff_flow st, af_vstack = [], af_estack = [], af_dstack = [],
     af_out_arr = aff_out_arr st, af_in_arr = aff_in_arr st, af_state = aff_state st, af_unbounded = aff_unbounded st \<rparr>"
  have we1: "af_flow ?w = aff_flow st" and we2: "af_state ?w = aff_state st"
    and we3: "af_out_arr ?w = aff_out_arr st" and we4: "af_in_arr ?w = aff_in_arr st" by simp_all
  have rw: "af_rankok ?w rk" using finr af_AFF_rankok[OF we1 we2] by metis
  have vw: "af_vrank ?w rk c" using finv af_AFF_vrank[OF we2] by metis
  have rinit: "af_rankok ?init rk" using af_rankok_initial[OF sti vV vuns rw we1 we2] .
  have vrin: "\<And>u. u \<in> \<V> \<Longrightarrow> st_lookup (aff_state st) u = Finished \<Longrightarrow> rk u < c" using vw we2 by (auto simp: af_vrank_def)
  have vinj: "inj_on rk {v\<in>\<V>. st_lookup (aff_state st) v = Finished}" using vw we2 by (auto simp: af_vrank_def)
  have vinit: "af_vrank ?init rk c" using af_vrank_initial[OF sti vV vrin vinj] .
  have prin: "\<And>v. v \<in> \<V> \<Longrightarrow> st_lookup (aff_state st) v = Unseen \<Longrightarrow> out_iterated (aff_out_arr st) v = {} \<and> in_iterated (aff_in_arr st) v = {}"
    using finp by (auto simp: AFF_pristine_def)
  have prsl: "\<And>a. a \<in> out_iterated (aff_out_arr st) (fst a) \<or> a \<in> in_iterated (aff_in_arr st) (snd a) \<Longrightarrow> af_arc_free (aff_flow st) a \<Longrightarrow> fst a \<noteq> snd a"
    using finp by (auto simp: AFF_pristine_def)
  have prsl3: "\<And>a. a \<in> out_iterated (aff_out_arr st) (fst a) \<or> a \<in> in_iterated (aff_in_arr st) (snd a) \<Longrightarrow> fst a = snd a \<Longrightarrow>
                    (0 \<le> \<c> a \<longrightarrow> flow_lookup (aff_flow st) a = 0) \<and> (\<c> a < 0 \<longrightarrow> flow_lookup (aff_flow st) a = cap a)"
    using finp by (auto simp: AFF_pristine_def)
  have pinit: "af_pristine ?init" using af_pristine_initial[OF sti vV prin prsl prsl3] .
  have sinit: "af_scanres ?init" using af_scanres_initial[OF sti vV noos_w prin vuns] .
  obtain r cc where dieq: "AF_DFS_i ?init rk c = (AF_DFS ?init, r, cc)" and rok: "af_rankok (AF_DFS ?init) r"
    using af_rankok_AF_DFS_i[OF domi mi0 fresh] invi pinit sinit rinit vinit nures by blast
  obtain r' cc' where die2: "AF_DFS_i ?init rk c = (AF_DFS ?init, r', cc')" and vres': "af_vrank (AF_DFS ?init) r' cc'"
    using af_vrank_AF_DFS_i[OF domi mi0 fresh] invi pinit sinit rinit vinit nures by blast
  have vres: "af_vrank (AF_DFS ?init) r cc" using vres' dieq die2 by simp
  have pres: "af_pristine (AF_DFS ?init)" using AF_DFS_pristine[OF domi mi0 fresh] invi pinit nures by blast
  have su1: "aff_flow (AF_outer_upd2 st) = af_flow (AF_DFS ?init)" and su2: "aff_state (AF_outer_upd2 st) = af_state (AF_DFS ?init)"
    and su3: "aff_out_arr (AF_outer_upd2 st) = af_out_arr (AF_DFS ?init)" and su4: "aff_in_arr (AF_outer_upd2 st) = af_in_arr (AF_DFS ?init)"
    by (simp_all add: AF_outer_upd2_def Let_def)
  have "AFF_fin2 (AF_outer_upd2 st) r cc"
  proof (unfold AFF_fin2_def, intro impI conjI)
    show "AFF_pristine (AF_outer_upd2 st)"
      using pres af_AFF_pristine[OF su1[symmetric] su2[symmetric] su3[symmetric] su4[symmetric]] by metis
    show "AFF_rankok (AF_outer_upd2 st) r" using rok af_AFF_rankok[OF su1[symmetric] su2[symmetric]] by metis
    show "AFF_vrank (AF_outer_upd2 st) r cc" using vres af_AFF_vrank[OF su2[symmetric]] by metis
  qed
  thus ?thesis by blast
qed

lemma AF_outer_fin:
  assumes dom: "AF_outer_dom st" and mi0: "multigraph_inv out_arr in_arr"
    and fresh: "\<forall>u. out_iterated out_arr u = {} \<and> in_iterated in_arr u = {}"
  shows "AFF_inv st \<longrightarrow> (\<exists>rk c. AFF_fin2 st rk c) \<longrightarrow> (\<exists>rk c. AFF_fin2 (AF_outer st) rk c)"
proof (induction rule: AF_outer_induct[OF dom])
  case IH: (1 st)
  show ?case
  proof (intro impI)
    assume inv: "AFF_inv st" and fin: "\<exists>rk c. AFF_fin2 st rk c"
    show "\<exists>rk c. AFF_fin2 (AF_outer st) rk c"
    proof (rule AF_outer_cases[where st = st])
      assume c: "AF_outer_call_1_conds st"
      obtain rk cc where "AFF_fin2 st rk cc" using fin by blast
      hence f1: "\<exists>rk c. AFF_fin2 (AF_outer_upd1 st) rk c" using AFF_fin2_holds_1 by blast
      have "\<exists>rk c. AFF_fin2 (AF_outer (AF_outer_upd1 st)) rk c" using IH(2)[OF c] AFF_inv_holds_1[OF c inv] f1 by blast
      thus ?thesis using c by (simp add: AF_outer_simps[OF IH(1)])
    next
      assume c: "AF_outer_call_2_conds st"
      obtain rk cc where fin2: "AFF_fin2 st rk cc" using fin by blast
      have f2: "\<exists>rk c. AFF_fin2 (AF_outer_upd2 st) rk c" using AFF_fin2_holds_2[OF mi0 fresh c inv fin2] .
      have "\<exists>rk c. AFF_fin2 (AF_outer (AF_outer_upd2 st)) rk c" using IH(3)[OF c] AFF_inv_holds_2[OF mi0 c inv] f2 by blast
      thus ?thesis using c by (simp add: AF_outer_simps[OF IH(1)])
    next
      assume c: "AF_outer_ret_conds st"
      thus ?thesis using fin by (simp add: AF_outer_simps[OF IH(1)] AF_outer_ret_def)
    qed
  qed
qed

text \<open>Assembling: at @{const make_acyclic}'s bounded return, the finish-order invariants and full vertex
      coverage (@{thm [source] make_acyclic_all_finished}) meet, so the returned flow has no free scanned
      closed trail --- i.e.\ @{const AFF_forest} holds.\<close>

lemma make_acyclic_forest_fin:
  assumes mi0: "multigraph_inv out_arr in_arr"
    and ff: "flow_invar f0" and feas: "af_cap_feasible f0"
    and vv: "vit_invar all_vertices" and vabsV: "vit_abstract all_vertices = \<V>"
    and vit0: "vit_iterated all_vertices = {}" and res: "make_acyclic f0 = Some f'"
    and fresh: "\<forall>u. out_iterated out_arr u = {} \<and> in_iterated in_arr u = {}"
  shows "AFF_forest (AF_outer (AF_outer_initial f0))"
proof -
  let ?fin = "AF_outer (AF_outer_initial f0)"
  have vab: "vit_abstract all_vertices \<subseteq> \<V>" using vabsV by simp
  have inv0: "AFF_inv (AF_outer_initial f0)" using AFF_inv_initial[OF mi0 ff feas vv vab] .
  have dom: "AF_outer_dom (AF_outer_initial f0)" using AF_outer_dom[OF mi0 inv0] .
  have fin0: "\<exists>rk c. AFF_fin2 (AF_outer_initial f0) rk c" using AFF_fin2_initial[OF fresh] by blast
  have "\<exists>rk c. AFF_fin2 ?fin rk c" using AF_outer_fin[OF dom mi0 fresh] inv0 fin0 by blast
  then obtain rk c where fin: "AFF_fin2 ?fin rk c" by blast
  have nu: "\<not> aff_unbounded ?fin" using res by (auto simp: make_acyclic_def Let_def split: if_splits)
  have finp: "AFF_pristine ?fin" and finr: "AFF_rankok ?fin rk" and finv: "AFF_vrank ?fin rk c"
    using fin nu by (auto simp: AFF_fin2_def)
  have allfin: "\<And>v. v \<in> \<V> \<Longrightarrow> st_lookup (aff_state ?fin) v = Finished"
    using make_acyclic_all_finished[OF mi0 ff feas vv vabsV vit0 res] by blast
  show ?thesis using AFF_forest_from_rankok[OF finr finv allfin finp] .
qed

text \<open>The terminal state is @{const AFF_pristine}: in particular its third clause pins every scanned
      self-loop to the cost-appropriate bound. Since at termination every edge is scanned
      (@{thm [source] make_acyclic_all_edges_scanned}, @{thm [source] AFF_scanned_of_exhausted}), this
      lifts to a guarantee about the returned flow.\<close>

lemma make_acyclic_pristine_fin:
  assumes mi0: "multigraph_inv out_arr in_arr"
    and ff: "flow_invar f0" and feas: "af_cap_feasible f0"
    and vv: "vit_invar all_vertices" and vabsV: "vit_abstract all_vertices = \<V>"
    and vit0: "vit_iterated all_vertices = {}" and res: "make_acyclic f0 = Some f'"
    and fresh: "\<forall>u. out_iterated out_arr u = {} \<and> in_iterated in_arr u = {}"
  shows "AFF_pristine (AF_outer (AF_outer_initial f0))"
proof -
  let ?fin = "AF_outer (AF_outer_initial f0)"
  have vab: "vit_abstract all_vertices \<subseteq> \<V>" using vabsV by simp
  have inv0: "AFF_inv (AF_outer_initial f0)" using AFF_inv_initial[OF mi0 ff feas vv vab] .
  have dom: "AF_outer_dom (AF_outer_initial f0)" using AF_outer_dom[OF mi0 inv0] .
  have fin0: "\<exists>rk c. AFF_fin2 (AF_outer_initial f0) rk c" using AFF_fin2_initial[OF fresh] by blast
  have "\<exists>rk c. AFF_fin2 ?fin rk c" using AF_outer_fin[OF dom mi0 fresh] inv0 fin0 by blast
  then obtain rk c where fin: "AFF_fin2 ?fin rk c" by blast
  have nu: "\<not> aff_unbounded ?fin" using res by (auto simp: make_acyclic_def Let_def split: if_splits)
  show "AFF_pristine ?fin" using fin nu by (auto simp: AFF_fin2_def)
qed

theorem make_acyclic_selfloop:
  assumes mi0: "multigraph_inv out_arr in_arr"
    and ff: "flow_invar f0" and feas: "af_cap_feasible f0"
    and vv: "vit_invar all_vertices" and vabsV: "vit_abstract all_vertices = \<V>"
    and vit0: "vit_iterated all_vertices = {}" and res: "make_acyclic f0 = Some f'"
    and fresh: "\<forall>u. out_iterated out_arr u = {} \<and> in_iterated in_arr u = {}"
    and ee: "e \<in> \<E>" and esl: "fst e = snd e"
  shows "(0 \<le> \<c> e \<longrightarrow> flow_lookup f' e = 0) \<and> (\<c> e < 0 \<longrightarrow> flow_lookup f' e = cap e)"
proof -
  let ?fin = "AF_outer (AF_outer_initial f0)"
  have ff': "f' = aff_flow ?fin" using res by (auto simp: make_acyclic_def Let_def split: if_splits)
  have vab: "vit_abstract all_vertices \<subseteq> \<V>" using vabsV by simp
  have inv0: "AFF_inv (AF_outer_initial f0)" using AFF_inv_initial[OF mi0 ff feas vv vab] .
  have dom: "AF_outer_dom (AF_outer_initial f0)" using AF_outer_dom[OF mi0 inv0] .
  have miR: "multigraph_inv (aff_out_arr ?fin) (aff_in_arr ?fin)"
    using AFF_inv_holds[OF dom mi0 inv0] by (simp add: AFF_inv_def)
  have scan: "\<forall>v \<in> \<V>. out_remaining (aff_out_arr ?fin) v = {} \<and> in_remaining (aff_in_arr ?fin) v = {}"
    using make_acyclic_all_edges_scanned[OF mi0 ff feas vv vabsV vit0 res] .
  have "out_remaining (aff_out_arr ?fin) (fst e) = {}" using scan fst_E_V[OF ee] by auto
  hence sc: "AFF_scanned ?fin e" using AFF_scanned_of_exhausted[OF miR _ ee] by simp
  have pr: "AFF_pristine ?fin" using make_acyclic_pristine_fin[OF mi0 ff feas vv vabsV vit0 res fresh] .
  have "(0 \<le> \<c> e \<longrightarrow> flow_lookup (aff_flow ?fin) e = 0) \<and> (\<c> e < 0 \<longrightarrow> flow_lookup (aff_flow ?fin) e = cap e)"
    using pr sc esl by (auto simp: AFF_pristine_def AFF_scanned_def)
  thus ?thesis using ff' by simp
qed

text \<open>The top-level correctness theorem, now \emph{unconditional}: the no-free-cycle obligation
      is discharged by the forest engine.\<close>

theorem make_acyclic_correct_unconditional:
  assumes mi0: "multigraph_inv out_arr in_arr"
    and ff: "flow_invar f0" and feas: "af_cap_feasible f0"
    and vv: "vit_invar all_vertices" and vabsV: "vit_abstract all_vertices = \<V>"
    and vit0: "vit_iterated all_vertices = {}"
    and fresh: "\<forall>u. out_iterated out_arr u = {} \<and> in_iterated in_arr u = {}"
    and res: "make_acyclic f0 = Some f'"
  shows "af_cap_feasible f' \<and> \<C> (h \<circ> flow_lookup f') \<le> \<C> (h \<circ> flow_lookup f0) \<and> acyclic_flow (h \<circ> flow_lookup f')"
proof -
  have vab: "vit_abstract all_vertices \<subseteq> \<V>" using vabsV by simp
  have forest: "AFF_forest (AF_outer (AF_outer_initial f0))"
    using make_acyclic_forest_fin[OF mi0 ff feas vv vabsV vit0 res fresh] .
  show ?thesis
    using make_acyclic_feasible[OF mi0 ff feas vv vab res]
          make_acyclic_cost_le[OF mi0 ff feas vv vab res]
          make_acyclic_acyclic_from_forest[OF mi0 ff feas vv vabsV vit0 res forest]
    by blast
qed

text \<open>The user-facing correctness theorem strengthened to a genuine @{term b}-flow: from a feasible
      @{term b}-flow input the algorithm returns a feasible @{term b}-flow (same capacities \emph{and}
      same divergence @{term b} at every vertex, by @{thm make_acyclic_feasible_bal}), of no greater
      cost, and acyclic.\<close>

theorem make_acyclic_correct_unconditional_bflow:
  assumes mi0: "multigraph_inv out_arr in_arr"
    and ff: "flow_invar f0" and feas: "af_feasible b f0"
    and vv: "vit_invar all_vertices" and vabsV: "vit_abstract all_vertices = \<V>"
    and vit0: "vit_iterated all_vertices = {}"
    and fresh: "\<forall>u. out_iterated out_arr u = {} \<and> in_iterated in_arr u = {}"
    and res: "make_acyclic f0 = Some f'"
  shows "af_feasible b f' \<and> \<C> (h \<circ> flow_lookup f') \<le> \<C> (h \<circ> flow_lookup f0) \<and> acyclic_flow (h \<circ> flow_lookup f')"
proof -
  have capf0: "af_cap_feasible f0" using feas by (rule af_feasible_cap)
  have vab: "vit_abstract all_vertices \<subseteq> \<V>" using vabsV by simp
  show ?thesis
    using make_acyclic_feasible_bal[OF mi0 ff feas vv vab res]
          make_acyclic_correct_unconditional[OF mi0 ff capf0 vv vabsV vit0 fresh res]
    by blast
qed


subsection \<open>The unbounded case: a negative infinite-capacity cycle witness\<close>

text \<open>When the top-level answer is @{term None}, the instance is genuinely unbounded: there is a
      directed cycle of original arcs, every one of infinite capacity, whose total cost is negative.
      Circulating flow around such a cycle drives the cost to @{term \<open>- \<infinity>\<close>}, so no cost-minimal (or
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
      lookup, exactly the value @{const af_scan} folds. The flipped room is @{term \<open>asis_room fl a (\<not> d)\<close>}.\<close>

definition asis_room :: "'farr \<Rightarrow> 'e \<Rightarrow> bool \<Rightarrow> 'n" where
  "asis_room fl a d = (let (up, dn) = af_rooms fl a in if d then up else dn)"

text \<open>A free arc has a strictly positive backward (draining) room, hence its as-is room is the sentinel
      @{term \<open>- 1\<close>} only when it is traversed \emph{forward} and its capacity is infinite.\<close>

lemma asis_room_pos_free: "af_arc_free fl a \<Longrightarrow> 0 < asis_room fl a False"
  by (auto simp: asis_room_def af_rooms_def af_arc_free_def Let_def)

lemma asis_room_neg1_free: "af_arc_free fl a \<Longrightarrow> asis_room fl a d = - 1 \<Longrightarrow> d \<and> cap a = - 1"
  using asis_room_pos_free[of fl a]
  by (cases d) (auto simp: asis_room_def af_rooms_def af_arc_free_def Let_def split: if_splits)

lemma tl_len2: "x \<in> set (tl xs) \<Longrightarrow> 2 \<le> length xs"
  by (cases xs) (auto simp: Suc_le_eq length_greater_0_conv)

text \<open>The scan reaches the ancestor @{term x}: it stops at the first stack position @{term p} carrying
      @{term x}, having accumulated the walk cost as a prefix sum, and --- crucially --- if the chosen
      directional bottleneck comes back unbounded (@{term \<open>- 1\<close>}) then \emph{every} walked arc is
      unbounded in that direction (and so is the seed).\<close>

lemma af_scan_reach:
  "af_scan fl x vs es ds (k0, ra0, rf0) = (k, ra, rf) \<Longrightarrow>
   x \<in> set (tl vs) \<Longrightarrow> length vs \<le> Suc (length es) \<Longrightarrow> length vs \<le> Suc (length ds) \<Longrightarrow>
   (\<exists>p. 1 \<le> p \<and> p \<le> length es \<and> Suc p \<le> length vs \<and> vs ! p = x \<and>
        k = k0 + (\<Sum>i<p. af_delta_cost (es!i) (ds!i)) \<and>
        (ra = - 1 \<longrightarrow> ra0 = - 1 \<and> (\<forall>i<p. asis_room fl (es!i) (ds!i) = - 1)) \<and>
        (rf = - 1 \<longrightarrow> rf0 = - 1 \<and> (\<forall>i<p. asis_room fl (es!i) (\<not> ds!i) = - 1)))"
proof (induction fl x vs es ds "(k0, ra0, rf0)" arbitrary: k0 ra0 rf0 k ra rf rule: af_scan.induct)
  case (1 fl x u v1 vs a es d ds k0 ra0 rf0)
  obtain up dn where ud: "af_rooms fl a = (up, dn)" by fastforce
  have rda: "asis_room fl a d = (if d then up else dn)" and fda: "asis_room fl a (\<not> d) = (if d then dn else up)"
    by (auto simp: asis_room_def ud)
  let ?acc = "(k0 + af_delta_cost a d, af_min (if d then up else dn) ra0, af_min (if d then dn else up) rf0)"
  show ?case
  proof (cases "v1 = x")
    case True
    hence res: "(k, ra, rf) = ?acc"
      using 1(2) ud True by (simp add: Let_def)
    have "(1::nat) \<le> 1 \<and> 1 \<le> length (a#es) \<and> Suc 1 \<le> length (u#v1#vs) \<and> (u#v1#vs)!1 = x \<and>
          k = k0 + (\<Sum>i<1. af_delta_cost ((a#es)!i) ((d#ds)!i)) \<and>
          (ra = - 1 \<longrightarrow> ra0 = - 1 \<and> (\<forall>i<1. asis_room fl ((a#es)!i) ((d#ds)!i) = - 1)) \<and>
          (rf = - 1 \<longrightarrow> rf0 = - 1 \<and> (\<forall>i<1. asis_room fl ((a#es)!i) (\<not> (d#ds)!i) = - 1))"
      using res True rda fda by (auto simp: af_min_eq_neg1)
    thus ?thesis by blast
  next
    case False
    have rec: "af_scan fl x (v1#vs) es ds ?acc = (k, ra, rf)"
      using 1(2) ud False by (simp add: Let_def)
    have xtl: "x \<in> set (tl (v1#vs))" using 1(3) False by auto
    have le1: "length (v1#vs) \<le> Suc (length es)" using 1(4) by simp
    have le2: "length (v1#vs) \<le> Suc (length ds)" using 1(5) by simp
    obtain p where p: "1 \<le> p" "p \<le> length es" "Suc p \<le> length (v1#vs)" "(v1#vs)!p = x"
       "k = (k0 + af_delta_cost a d) + (\<Sum>i<p. af_delta_cost (es!i) (ds!i))"
       "(ra = - 1 \<longrightarrow> af_min (if d then up else dn) ra0 = - 1 \<and> (\<forall>i<p. asis_room fl (es!i) (ds!i) = - 1))"
       "(rf = - 1 \<longrightarrow> af_min (if d then dn else up) rf0 = - 1 \<and> (\<forall>i<p. asis_room fl (es!i) (\<not> ds!i) = - 1))"
      using 1(1)[OF ud[symmetric] refl refl False rec xtl le1 le2] by auto
    show ?thesis
    proof (intro exI[of _ "Suc p"] conjI)
      show "k = k0 + (\<Sum>i<Suc p. af_delta_cost ((a#es)!i) ((d#ds)!i))"
        using p(5) by (simp add: sum.lessThan_Suc_shift del: sum.lessThan_Suc)
      show "ra = - 1 \<longrightarrow> ra0 = - 1 \<and> (\<forall>i<Suc p. asis_room fl ((a#es)!i) ((d#ds)!i) = - 1)"
      proof
        assume "ra = - 1"
        hence "af_min (if d then up else dn) ra0 = - 1 \<and> (\<forall>i<p. asis_room fl (es!i) (ds!i) = - 1)" using p(6) by simp
        thus "ra0 = - 1 \<and> (\<forall>i<Suc p. asis_room fl ((a#es)!i) ((d#ds)!i) = - 1)"
          using rda by (auto simp: af_min_eq_neg1 nth_Cons' less_Suc_eq_0_disj)
      qed
      show "rf = - 1 \<longrightarrow> rf0 = - 1 \<and> (\<forall>i<Suc p. asis_room fl ((a#es)!i) (\<not> (d#ds)!i) = - 1)"
      proof
        assume "rf = - 1"
        hence "af_min (if d then dn else up) rf0 = - 1 \<and> (\<forall>i<p. asis_room fl (es!i) (\<not> ds!i) = - 1)" using p(7) by simp
        thus "rf0 = - 1 \<and> (\<forall>i<Suc p. asis_room fl ((a#es)!i) (\<not> (d#ds)!i) = - 1)"
          using fda by (auto simp: af_min_eq_neg1 nth_Cons' less_Suc_eq_0_disj)
      qed
    qed (use p in \<open>auto simp: nth_Cons'\<close>)
  qed
qed (auto dest: tl_len2)

text \<open>Bridge the executable @{term \<open>- 1\<close>} sentinel back to the genuine infinite capacity @{term \<open>\<u> a = \<infinity>\<close>}.\<close>

lemma cap_neg1_infty: 
  assumes "a \<in> \<E>"
  shows "cap a = - 1 \<Longrightarrow> \<u> a = \<infinity>"
  using cap_infinite_bridge[OF assms] by simp

text \<open>A closed directed walk of arcs -- each arc's head vertex being the next arc's tail, cyclically --
      yields the @{const closed_w} required by @{const has_neg_infty_cycle}.\<close>

lemma cas_chain:
  "\<forall>i. Suc i < length C \<longrightarrow> snd (C ! i) = fst (C ! Suc i) \<Longrightarrow> C \<noteq> [] \<Longrightarrow>
   cas (fst (hd C)) (map make_pair C) (snd (last C))"
proof (induction C)
  case (Cons a C)
  show ?case
  proof (cases "C = []")
    case True thus ?thesis by (simp add: make_pair_def)
  next
    case False
    have hd: "snd a = fst (hd C)"
      using Cons.prems(1)[rule_format, of 0] False by (simp add: hd_conv_nth)
    have "\<forall>i. Suc i < length C \<longrightarrow> snd (C ! i) = fst (C ! Suc i)" using Cons.prems(1) by auto
    hence ih: "cas (fst (hd C)) (map make_pair C) (snd (last C))" using Cons.IH False by simp
    have mp: "make_pair a = (fst a, snd a)" by (simp add: make_pair_def)
    have "cas (fst a) (map make_pair (a # C)) (snd (last (a # C)))" using ih hd mp False by simp
    thus ?thesis by simp
  qed
qed simp

lemma neg_inf_cycleI:
  assumes ne: "C \<noteq> []" and sub: "set C \<subseteq> \<E>" and cp: "\<forall>a\<in>set C. cap a = - 1"
    and cost: "sum_list (map \<c> C) < 0"
    and clos: "\<forall>i<length C. snd (C!i) = fst (C!(Suc i mod length C))"
  shows neg_inf_cycle
proof (rule has_neg_infty_cycleI[where D = C])
  have chain: "\<forall>i. Suc i < length C \<longrightarrow> snd (C ! i) = fst (C ! Suc i)"
    using clos by (auto simp: mod_less)
  have wrap: "snd (C ! (length C - 1)) = fst (hd C)"
    using clos ne by (auto simp: hd_conv_nth)
  have "cas (fst (hd C)) (map make_pair C) (snd (last C))" using cas_chain[OF chain ne] .
  moreover have "snd (last C) = fst (hd C)" using wrap ne by (simp add: last_conv_nth)
  ultimately have casc: "cas (fst (hd C)) (map make_pair C) (fst (hd C))" by simp
  have u_dvs: "fst (hd C) \<in> dVs (make_pair ` \<E>)"
  proof -
    have "make_pair (hd C) \<in> make_pair ` \<E>" using hd_in_set[OF ne] sub by auto
    thus ?thesis by (auto simp: make_pair_def dVs_def)
  qed
  show "closed_w (make_pair ` \<E>) (map make_pair C)"
    unfolding closed_w_def awalk_def using casc u_dvs sub ne by auto
  show "foldr (\<lambda>e. (+) (\<c> e)) C 0 < 0"
    using cost by (simp add: sum_list.eq_foldr foldr_map o_def)
  show "set C \<subseteq> \<E>" by (rule sub)
  show "\<And>e. e \<in> set C \<Longrightarrow> \<u> e = PInfty"  
    using sub cp cap_neg1_infty by auto
qed

text \<open>Assemble the witness cycle from the stack trail. In the \<open>as-is\<close> orientation (chosen when the walk
      cost is non-positive) every trail arc is traversed forward and the cycle is
      @{term \<open>a # rev (take p es)\<close>}: the closing arc from the top down to the reached ancestor, then the
      trail arcs back up.\<close>

lemma trail_cycle_asis:
  assumes tr: "af_trail vs es ds"
    and ple: "p \<le> length es" and p1: "1 \<le> p" and pv: "Suc p \<le> length vs"
    and vp: "vs ! p = x" and hda: "hd vs = fst a" and xa: "snd a = x"
    and dstrue: "\<forall>i<p. ds ! i"
    and capes: "\<forall>i<p. cap (es!i) = - 1" and capa: "cap a = - 1"
    and ain: "a \<in> \<E>" and esin: "set es \<subseteq> \<E>"
    and cost: "\<c> a + (\<Sum>i<p. \<c> (es!i)) < 0"
    and vne: "vs \<noteq> []"
  shows neg_inf_cycle
proof -
  define C where "C = a # rev (take p es)"
  have lenC: "length C = Suc p" using ple by (simp add: C_def)
  have Cnth: "\<And>j. j \<le> p \<Longrightarrow> C ! j = (if j = 0 then a else es ! (p - j))"
  proof -
    fix j assume jp: "j \<le> p"
    show "C ! j = (if j = 0 then a else es ! (p - j))"
    proof (cases "j = 0")
      case True thus ?thesis by (simp add: C_def)
    next
      case False
      then obtain j' where j': "j = Suc j'" using not0_implies_Suc by blast
      have "C ! j = rev (take p es) ! j'" by (simp add: C_def j')
      also have "\<dots> = take p es ! (p - Suc j')" using j' jp ple by (simp add: rev_nth)
      also have "\<dots> = es ! (p - Suc j')" using j' jp ple by (simp add: nth_take)
      finally show ?thesis using j' by simp
    qed
  qed
  have trj: "\<And>j. j < p \<Longrightarrow> snd (es!j) = vs!j \<and> fst (es!j) = vs!Suc j"
  proof -
    fix j assume jp: "j < p"
    have "j < length es" using jp ple by simp
    hence "(if ds!j then snd (es!j) else fst (es!j)) = vs!j \<and> (if ds!j then fst (es!j) else snd (es!j)) = vs!Suc j"
      using tr by (simp add: af_trail_def)
    thus "snd (es!j) = vs!j \<and> fst (es!j) = vs!Suc j" using dstrue jp by simp
  qed
  have hdv: "vs ! 0 = fst a" using hda vne by (simp add: hd_conv_nth)
  show ?thesis
  proof (rule neg_inf_cycleI)
    show "C \<noteq> []" by (simp add: C_def)
    show "set C \<subseteq> \<E>" using ain esin by (auto simp: C_def dest: in_set_takeD)
    show "\<forall>b\<in>set C. cap b = - 1"
    proof
      fix b assume "b \<in> set C"
      then consider "b = a" | "b \<in> set (take p es)" by (auto simp: C_def)
      thus "cap b = - 1"
      proof cases
        case 2
        then obtain j where "j < p" "b = es ! j"
          using ple by (auto simp: in_set_conv_nth min_absorb2)
        thus ?thesis using capes by simp
      qed (simp add: capa)
    qed
    show "sum_list (map \<c> C) < 0"
    proof -
      have "sum_list (map \<c> C) = \<c> a + sum_list (map \<c> (take p es))"
        by (simp add: C_def rev_map[symmetric] sum_list_rev)
      also have "sum_list (map \<c> (take p es)) = (\<Sum>i<p. \<c> (es!i))"
        using ple by (simp add: sum_list_sum_nth min_absorb2 lessThan_atLeast0)
      finally show ?thesis using cost by simp
    qed
    show "\<forall>i<length C. snd (C!i) = fst (C!(Suc i mod length C))"
    proof (intro allI impI)
      fix i assume "i < length C"
      hence ip: "i \<le> p" using lenC by simp
      show "snd (C!i) = fst (C!(Suc i mod length C))"
      proof (cases "i = p")
        case True
        have "snd (C!i) = snd (es!0)" using Cnth[of p] p1 True by simp
        also have "\<dots> = vs!0" using trj p1 by simp
        also have "\<dots> = fst a" by (rule hdv)
        also have "\<dots> = fst (C!(Suc i mod length C))"
          using True lenC by (simp add: Cnth)
        finally show ?thesis .
      next
        case False
        hence iltp: "i < p" using ip by simp
        have smod: "Suc i mod length C = Suc i" using iltp lenC by simp
        show ?thesis
        proof (cases "i = 0")
          case True
          have "snd (C!i) = snd a" using True by (simp add: C_def)
          also have "\<dots> = x" by (rule xa)
          also have "\<dots> = vs!p" using vp by simp
          also have "\<dots> = fst (es!(p-1))" using trj p1 by simp
          also have "\<dots> = fst (C!1)" using Cnth[of 1] p1 by simp
          finally show ?thesis using True smod by simp
        next
          case False
          hence i0: "0 < i" by simp
          have "snd (C!i) = snd (es!(p-i))" using Cnth[of i] ip i0 by simp
          also have "\<dots> = vs!(p-i)" using trj iltp i0 by simp
          also have "\<dots> = fst (es!(p - Suc i))"
            using trj iltp i0 by (simp add: Suc_diff_Suc)
          also have "\<dots> = fst (C!(Suc i))" using Cnth[of "Suc i"] iltp by simp
          finally show ?thesis using smod by simp
        qed
      qed
    qed
  qed
qed

text \<open>The \<open>flipped\<close> orientation (chosen when the walk cost is positive, so the reversal is negative):
      every trail arc is traversed forward down the stack and the cycle is @{term \<open>take p es @ [a]\<close>}.\<close>

lemma trail_cycle_flip:
  assumes tr: "af_trail vs es ds"
    and ple: "p \<le> length es" and p1: "1 \<le> p" and pv: "Suc p \<le> length vs"
    and vp: "vs ! p = x" and hda: "hd vs = snd a" and xa: "fst a = x"
    and dsfalse: "\<forall>i<p. \<not> ds ! i"
    and capes: "\<forall>i<p. cap (es!i) = - 1" and capa: "cap a = - 1"
    and ain: "a \<in> \<E>" and esin: "set es \<subseteq> \<E>"
    and cost: "\<c> a + (\<Sum>i<p. \<c> (es!i)) < 0"
    and vne: "vs \<noteq> []"
  shows neg_inf_cycle
proof -
  define C where "C = take p es @ [a]"
  have lenC: "length C = Suc p" using ple by (simp add: C_def)
  have Cnth: "\<And>j. j \<le> p \<Longrightarrow> C ! j = (if j = p then a else es ! j)"
  proof -
    fix j assume jp: "j \<le> p"
    show "C ! j = (if j = p then a else es ! j)"
    proof (cases "j = p")
      case True thus ?thesis using ple by (simp add: C_def nth_append)
    next
      case False
      hence "j < p" using jp by simp
      thus ?thesis using ple by (simp add: C_def nth_append nth_take)
    qed
  qed
  have trj: "\<And>j. j < p \<Longrightarrow> fst (es!j) = vs!j \<and> snd (es!j) = vs!Suc j"
  proof -
    fix j assume jp: "j < p"
    have "j < length es" using jp ple by simp
    hence "(if ds!j then snd (es!j) else fst (es!j)) = vs!j \<and> (if ds!j then fst (es!j) else snd (es!j)) = vs!Suc j"
      using tr by (simp add: af_trail_def)
    thus "fst (es!j) = vs!j \<and> snd (es!j) = vs!Suc j" using dsfalse jp by simp
  qed
  have hdv: "vs ! 0 = snd a" using hda vne by (simp add: hd_conv_nth)
  show ?thesis
  proof (rule neg_inf_cycleI)
    show "C \<noteq> []" by (simp add: C_def)
    show "set C \<subseteq> \<E>" using ain esin by (auto simp: C_def dest: in_set_takeD)
    show "\<forall>b\<in>set C. cap b = - 1"
    proof
      fix b assume "b \<in> set C"
      then consider "b = a" | "b \<in> set (take p es)" by (auto simp: C_def)
      thus "cap b = - 1"
      proof cases
        case 2
        then obtain j where "j < p" "b = es ! j"
          using ple by (auto simp: in_set_conv_nth min_absorb2)
        thus ?thesis using capes by simp
      qed (simp add: capa)
    qed
    show "sum_list (map \<c> C) < 0"
    proof -
      have "sum_list (map \<c> C) = sum_list (map \<c> (take p es)) + \<c> a"
        by (simp add: C_def)
      also have "sum_list (map \<c> (take p es)) = (\<Sum>i<p. \<c> (es!i))"
        using ple by (simp add: sum_list_sum_nth min_absorb2 lessThan_atLeast0)
      finally show ?thesis using cost by simp
    qed
    show "\<forall>i<length C. snd (C!i) = fst (C!(Suc i mod length C))"
    proof (intro allI impI)
      fix i assume "i < length C"
      hence ip: "i \<le> p" using lenC by simp
      show "snd (C!i) = fst (C!(Suc i mod length C))"
      proof (cases "i = p")
        case True
        have "snd (C!i) = snd a" using Cnth[of p] True by simp
        also have "\<dots> = vs!0" using hdv by simp
        also have "\<dots> = fst (es!0)" using trj p1 by simp
        also have "\<dots> = fst (C!(Suc i mod length C))"
          using True lenC Cnth[of 0] p1 by simp
        finally show ?thesis .
      next
        case False
        hence iltp: "i < p" using ip by simp
        have smod: "Suc i mod length C = Suc i" using iltp lenC by simp
        have "snd (C!i) = snd (es!i)" using Cnth[of i] iltp by simp
        also have "\<dots> = vs!Suc i" using trj iltp by simp
        also have "\<dots> = fst (C!(Suc i))"
        proof (cases "Suc i = p")
          case True
          thus ?thesis using Cnth[of "Suc i"] vp xa by simp
        next
          case False
          hence "Suc i < p" using iltp by simp
          thus ?thesis using Cnth[of "Suc i"] trj by simp
        qed
        finally show ?thesis using smod by simp
      qed
    qed
  qed
qed

text \<open>The local witness: whenever @{const af_cancel_seg} raises the unbounded flag on the (distinct,
      free) trail closed by @{term a}, a negative infinite-capacity cycle exists. The chosen
      non-positive-cost push direction has an unbounded bottleneck, forcing every arc on the cycle to
      be forward-oriented and of infinite capacity, with strictly negative total cost.\<close>

lemma af_cancel_seg_ubd_witness:
  assumes tr: "af_trail vs es ds"
    and cpl1: "length vs \<le> Suc (length es)" and cpl2: "length vs \<le> Suc (length ds)"
    and free: "\<forall>b\<in>set es. af_arc_free fl b" and afree: "af_arc_free fl a"
    and esin: "set es \<subseteq> \<E>" and ain: "a \<in> \<E>"
    and xtl: "x \<in> set (tl vs)"
    and near: "hd vs = (if dir then fst a else snd a)"
    and xdef: "x = (if dir then snd a else fst a)"
    and rooms: "af_rooms fl a = (up, dn)"
    and cancel: "af_cancel_seg up dn x vs es ds a dir fl = (fl', m', True)"
    and vne: "vs \<noteq> []"
  shows neg_inf_cycle
proof -
  obtain k ra rf where scaneq:
    "af_scan fl x vs es ds (af_delta_cost a dir, if dir then up else dn, if dir then dn else up) = (k, ra, rf)"
    by (metis prod_cases3)
  have gam: "(if 0 < k then rf else ra) = - 1" and notsw: "\<not> (k = 0 \<and> rf \<noteq> - 1)"
    using cancel by (auto simp: af_cancel_seg_def scaneq Let_def split: if_splits prod.splits)
  obtain p where p: "1 \<le> p" "p \<le> length es" "Suc p \<le> length vs" "vs ! p = x"
    "k = af_delta_cost a dir + (\<Sum>i<p. af_delta_cost (es!i) (ds!i))"
    "(ra = - 1 \<longrightarrow> (if dir then up else dn) = - 1 \<and> (\<forall>i<p. asis_room fl (es!i) (ds!i) = - 1))"
    "(rf = - 1 \<longrightarrow> (if dir then dn else up) = - 1 \<and> (\<forall>i<p. asis_room fl (es!i) (\<not> ds!i) = - 1))"
    using af_scan_reach[OF scaneq xtl cpl1 cpl2] by blast
  have ra0: "(if dir then up else dn) = asis_room fl a dir" and rf0: "(if dir then dn else up) = asis_room fl a (\<not> dir)"
    by (auto simp: asis_room_def rooms)
  have esfree: "\<And>i. i < p \<Longrightarrow> af_arc_free fl (es!i)" using free p(2) by (simp add: nth_mem)
  show ?thesis
  proof (cases "0 < k")
    case True
    hence rfm: "rf = - 1" using gam by simp
    have rf0m: "asis_room fl a (\<not> dir) = - 1" and allrf: "\<forall>i<p. asis_room fl (es!i) (\<not> ds!i) = - 1"
      using p(7) rfm rf0 by auto
    have ndir: "\<not> dir" and capa: "cap a = - 1" using asis_room_neg1_free[OF afree rf0m] by auto
    have dsfalse: "\<forall>i<p. \<not> ds ! i" and capes: "\<forall>i<p. cap (es!i) = - 1"
      using allrf asis_room_neg1_free[OF esfree] by auto
    have cost: "\<c> a + (\<Sum>i<p. \<c> (es!i)) < 0"
    proof -
      have esE: "\<And>i. i < p \<Longrightarrow> es!i \<in> \<E>" using esin p(2) by (meson less_le_trans nth_mem subsetD)
      have sumeq: "(\<Sum>i<p. af_delta_cost (es!i) (ds!i)) = (\<Sum>i<p. - cost (es!i))"
        by (rule sum.cong[OF refl]) (auto simp: af_delta_cost_def dsfalse lessThan_iff)
      have kn: "k = - (cost a + (\<Sum>i<p. cost (es!i)))"
        using p(5) ndir sumeq by (simp add: af_delta_cost_def sum_negf)
      have sc: "(\<Sum>i<p. h (cost (es!i))) = (\<Sum>i<p. \<c> (es!i))"
        by (rule sum.cong[OF refl]) (auto simp: cost_h esE)
      have ceq: "\<c> a + (\<Sum>i<p. \<c> (es!i)) = h (cost a + (\<Sum>i<p. cost (es!i)))"
        using sc cost_h[OF ain] by (simp add: h_add h_sum)
      show ?thesis using kn True by (simp add: ceq)
    qed
    have hda: "hd vs = snd a" using near ndir by simp
    have xa: "fst a = x" using xdef ndir by simp
    show ?thesis
      by (rule trail_cycle_flip[OF tr p(2) p(1) p(3) p(4) hda xa dsfalse capes capa ain esin cost vne])
  next
    case False
    hence kle: "k \<le> 0" by simp
    have ram: "ra = - 1" using gam False by simp
    have ra0m: "asis_room fl a dir = - 1" and allra: "\<forall>i<p. asis_room fl (es!i) (ds!i) = - 1"
      using p(6) ram ra0 by auto
    have dir: "dir" and capa: "cap a = - 1" using asis_room_neg1_free[OF afree ra0m] by auto
    have dstrue: "\<forall>i<p. ds ! i" and capes: "\<forall>i<p. cap (es!i) = - 1"
      using allra asis_room_neg1_free[OF esfree] by auto
    have knz: "k \<noteq> 0"
    proof
      assume "k = 0"
      hence "rf = - 1" using notsw by simp
      hence "(if dir then dn else up) = - 1" using p(7) by simp
      hence "asis_room fl a (\<not> dir) = - 1" using rf0 by simp
      thus False using asis_room_pos_free[OF afree] dir by simp
    qed
    have cost: "\<c> a + (\<Sum>i<p. \<c> (es!i)) < 0"
    proof -
      have esE: "\<And>i. i < p \<Longrightarrow> es!i \<in> \<E>" using esin p(2) by (meson less_le_trans nth_mem subsetD)
      have sumeq: "(\<Sum>i<p. af_delta_cost (es!i) (ds!i)) = (\<Sum>i<p. cost (es!i))"
        by (rule sum.cong[OF refl]) (auto simp: af_delta_cost_def dstrue lessThan_iff)
      have kn: "k = cost a + (\<Sum>i<p. cost (es!i))"
        using p(5) dir sumeq by (simp add: af_delta_cost_def)
      have sc: "(\<Sum>i<p. h (cost (es!i))) = (\<Sum>i<p. \<c> (es!i))"
        by (rule sum.cong[OF refl]) (auto simp: cost_h esE)
      have ceq: "\<c> a + (\<Sum>i<p. \<c> (es!i)) = h (cost a + (\<Sum>i<p. cost (es!i)))"
        using sc cost_h[OF ain] by (simp add: h_add h_sum)
      show ?thesis using kn kle knz by (simp add: ceq)
    qed
    have hda: "hd vs = fst a" using near dir by simp
    have xa: "snd a = x" using xdef dir by simp
    show ?thesis
      by (rule trail_cycle_asis[OF tr p(2) p(1) p(3) p(4) hda xa dstrue capes capa ain esin cost vne])
  qed
qed

text \<open>The self-loop unbounded case: a single infinite-capacity arc of negative cost.\<close>

lemma af_cancel_seg_selfloop_ubd_witness:
  assumes afree: "af_arc_free fl a" and ain: "a \<in> \<E>" and loop: "fst a = snd a"
    and rooms: "af_rooms fl a = (up, dn)"
    and cancel: "af_cancel_seg up dn (fst a) [] [] [] a True fl = (fl', m', True)"
  shows neg_inf_cycle
proof -
  have gam: "(if 0 < af_delta_cost a True then dn else up) = - 1" and notsw: "\<not> (af_delta_cost a True = 0 \<and> dn \<noteq> - 1)"
    using cancel by (auto simp: af_cancel_seg_def Let_def split: if_splits prod.splits)
  have dnpos: "0 < dn" using afree rooms by (auto simp: af_arc_free_def af_rooms_def Let_def split: if_splits)
  have kle: "\<not> 0 < af_delta_cost a True"
  proof
    assume "0 < af_delta_cost a True"
    hence "dn = - 1" using gam by simp
    thus False using dnpos by simp
  qed
  hence upm: "up = - 1" using gam by simp
  have capa: "cap a = - 1" using asis_room_neg1_free[OF afree, of True] upm rooms by (simp add: asis_room_def)
  have cneg: "\<c> a < 0"
  proof -
    have "af_delta_cost a True \<noteq> 0" using notsw dnpos by auto
    hence "cost a < 0" using kle by (auto simp: af_delta_cost_def)
    thus ?thesis by (simp add: cost_h[OF ain, symmetric])
  qed
  show ?thesis
  proof (rule neg_inf_cycleI[of "[a]"])
    show "\<forall>i<length [a]. snd ([a]!i) = fst ([a]!(Suc i mod length [a]))" using loop by simp
  qed (auto simp: ain capa cneg)
qed

text \<open>The self-loop normaliser raises the unbounded flag exactly for a negative infinite-capacity
      self-loop, which is itself a negative infinite-capacity cycle.\<close>

lemma af_selfloop_handle_ubd_wit:
  assumes ain: "a \<in> \<E>" and loop: "fst a = snd a"
    and raised: "af_unbounded (af_selfloop_handle st a)" and nub0: "\<not> af_unbounded st"
  shows neg_inf_cycle
proof -
  have "\<c> a < 0 \<and> cap a = - 1" using raised nub0 by (simp add: af_selfloop_handle_unbounded[OF ain])
  hence cneg: "\<c> a < 0" and capa: "cap a = - 1" by auto
  show ?thesis
  proof (rule neg_inf_cycleI[of "[a]"])
    show "\<forall>i<length [a]. snd ([a]!i) = fst ([a]!(Suc i mod length [a]))" using loop by simp
  qed (auto simp: ain capa cneg)
qed

text \<open>@{const af_reset_unsee_seg} leaves the flag untouched.\<close>

lemma af_reset_unsee_seg_unbounded[simp]: "af_unbounded (af_reset_unsee_seg n vs st) = af_unbounded st"
  by (induction n vs st rule: af_reset_unsee_seg.induct) (auto simp: af_reset_def)

text \<open>The running witness invariant: once the unbounded flag is set, a negative infinite-capacity cycle
      exists. Since the cycle is a flow-independent property of the graph, the implication survives every
      subsequent step trivially; the only work is at the step that first raises the flag.\<close>

definition "AF_ubd_wit st \<longleftrightarrow> (af_unbounded st \<longrightarrow> neg_inf_cycle)"

lemma af_handle_ubd_wit:
  assumes A1: "AF_invar_1 st" and A2: "AF_invar_2 st" and A3: "AF_invar_3 st"
    and Afe: "AF_invar_feas st" and Afr: "AF_invar_free st" and AE: "AF_invar_estE st"
    and ae: "a \<in> \<E>"
    and inc: "(if dir then fst a else snd a) = hd (af_vstack st)" and ne: "af_vstack st \<noteq> []"
    and wit: "AF_ubd_wit st"
  shows "AF_ubd_wit (af_handle st a dir)"
proof -
  have feas: "af_cap_feasible (af_flow st)" using Afe by (simp add: AF_invar_feas_def)
  have fr: "\<forall>b\<in>set (af_estack st). af_arc_free (af_flow st) b" using Afr by (simp add: AF_invar_free_def)
  have esin: "set (af_estack st) \<subseteq> \<E>" using AE by (simp add: AF_invar_estE_def)
  have tr: "af_trail (af_vstack st) (af_estack st) (af_dstack st)" using A3 by (simp add: AF_invar_3_conv)
  have cpl: "Suc (length (af_estack st)) = length (af_vstack st) \<and> length (af_dstack st) = length (af_estack st)"
    using A2 ne by (auto simp: AF_invar_2_def)
  have onstack: "\<And>v. v \<in> \<V> \<Longrightarrow> (st_lookup (af_state st) v = OnStack) = (v \<in> set (af_vstack st))"
    using A2 by (simp add: AF_invar_2_def)
  have inc': "hd (af_vstack st) \<in> {fst a, snd a}" using inc by (cases dir) auto
  obtain up dn where updn: "af_rooms (af_flow st) a = (up, dn)"
    by (cases "af_rooms (af_flow st) a") auto
  show ?thesis
  proof (cases "fst a = snd a")
    case selfl: True
    have h: "af_handle st a dir = af_selfloop_handle st a" using selfl by (simp add: af_handle_real[OF ae])
    have "af_unbounded (af_selfloop_handle st a) \<longrightarrow> neg_inf_cycle"
    proof
      assume ub: "af_unbounded (af_selfloop_handle st a)"
      show neg_inf_cycle
      proof (cases "af_unbounded st")
        case True thus ?thesis using wit by (simp add: AF_ubd_wit_def)
      next
        case False thus ?thesis using af_selfloop_handle_ubd_wit[OF ae selfl ub] by blast
      qed
    qed
    thus ?thesis using h by (simp add: AF_ubd_wit_def)
  next
    case selfloop: False
    show ?thesis
    proof (cases "0 < dn \<and> (up = - 1 \<or> 0 < up)")
      case False thus ?thesis using wit updn selfloop unfolding af_handle_real[OF ae] by (simp add: AF_ubd_wit_def Let_def)
    next
      case guard: True
      have afree: "af_arc_free (af_flow st) a"
      proof -
        have "cap a = - 1 \<or> flow_lookup (af_flow st) a \<le> cap a" using feas ae by (auto simp: af_cap_feasible_def)
        thus ?thesis using af_guard_free[OF updn] guard by simp
      qed
      show ?thesis
      proof (cases "af_estack st \<noteq> [] \<and> a = hd (af_estack st)")
        case True
        have "af_handle st a dir = st"
          unfolding af_handle_real[OF ae] using updn guard selfloop True by (simp add: Let_def)
        thus ?thesis using wit by (simp add: AF_ubd_wit_def)
      next
        case parent: False
        show ?thesis
        proof (cases "st_lookup (af_state st) (if dir then snd a else fst a)")
          case Unseen
          have "af_handle st a dir = st\<lparr>af_vstack := (if dir then snd a else fst a) # af_vstack st,
              af_state := st_upd (af_state st) (if dir then snd a else fst a) OnStack,
              af_estack := a # af_estack st, af_dstack := dir # af_dstack st\<rparr>"
            unfolding af_handle_real[OF ae] using updn guard selfloop parent Unseen by (auto simp: Let_def)
          thus ?thesis using wit by (simp add: AF_ubd_wit_def)
        next
          case OnStack
          let ?x = "if dir then snd a else fst a"
          obtain fl m' ubd where c: "af_cancel_seg up dn ?x
              (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) = (fl, m', ubd)"
            by (metis prod_cases3)
          show ?thesis
          proof (cases ubd)
            case True
            have "af_handle st a dir = st\<lparr>af_unbounded := True\<rparr>"
              unfolding af_handle_real[OF ae] using updn guard selfloop parent OnStack c True by (auto simp: Let_def)
            moreover have neg_inf_cycle
            proof -
              have xV: "?x \<in> \<V>" using fst_E_V[OF ae] snd_E_V[OF ae] by (cases dir) auto
              have xin: "?x \<in> set (af_vstack st)" using OnStack onstack[OF xV] by simp
              have xnhd: "?x \<noteq> hd (af_vstack st)" using inc selfloop by (cases dir) auto
              have xtl: "?x \<in> set (tl (af_vstack st))" using xin xnhd ne by (cases "af_vstack st") auto
              show ?thesis
                by (rule af_cancel_seg_ubd_witness[OF tr _ _ fr afree esin ae xtl _ refl updn _ ne])
                   (use cpl inc c True in \<open>auto\<close>)
            qed
            ultimately show ?thesis by (simp add: AF_ubd_wit_def)
          next
            case False
            have red: "af_handle st a dir = af_reset_unsee_seg m' (af_vstack st)
                (st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st),
                    af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>)"
              unfolding af_handle_real[OF ae] using updn guard selfloop parent OnStack c False by (auto simp: Let_def)
            thus ?thesis using wit by (simp add: AF_ubd_wit_def)
          qed
        next
          case Finished
          thus ?thesis using wit updn guard selfloop parent unfolding af_handle_real[OF ae] by (auto simp: Let_def AF_ubd_wit_def)
        qed
      qed
    qed
  qed
qed

lemma AF_ubd_wit_out_arr[simp]: "AF_ubd_wit (st\<lparr>af_out_arr := X\<rparr>) = AF_ubd_wit st" by (simp add: AF_ubd_wit_def)
lemma AF_ubd_wit_in_arr[simp]: "AF_ubd_wit (st\<lparr>af_in_arr := X\<rparr>) = AF_ubd_wit st" by (simp add: AF_ubd_wit_def)

lemma AF_ubd_wit_holds_1:
  assumes conds: "AF_DFS_call_1_conds st"
    and A1: "AF_invar_1 st" and A2: "AF_invar_2 st" and A3: "AF_invar_3 st"
    and Afe: "AF_invar_feas st" and Afr: "AF_invar_free st" and AE: "AF_invar_estE st"
    and Aiter: "AF_invar_iter st" and AV: "AF_invar_V st" and wit: "AF_ubd_wit st"
  shows "AF_ubd_wit (AF_DFS_upd1 st)"
proof -
  from conds have ne: "af_vstack st \<noteq> []" and he: "out_has (af_out_arr st) (hd (af_vstack st))"
    by (auto elim!: call_cond_elims)
  have vV: "hd (af_vstack st) \<in> \<V>" using AV ne hd_in_set by (auto simp: AF_invar_V_def)
  have endp: "fst (out_current (af_out_arr st) (hd (af_vstack st))) = hd (af_vstack st) \<and>
              out_current (af_out_arr st) (hd (af_vstack st)) \<in> \<E>"
    using af_current_out_endpoint[OF _ vV he] Aiter by (auto simp: AF_invar_iter_def)
  let ?st' = "st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack st))\<rparr>"
  have A1': "AF_invar_1 ?st'" by (rule AF_invar_1_out_advance[OF vV A1])
  have inc: "(if True then fst (out_current (af_out_arr st) (hd (af_vstack st)))
             else snd (out_current (af_out_arr st) (hd (af_vstack st)))) = hd (af_vstack ?st')"
    using endp by simp
  show ?thesis unfolding AF_DFS_upd1_def Let_def
    by (rule af_handle_ubd_wit[OF A1' _ _ _ _ _ _ inc _ _]) (use A2 A3 Afe Afr AE endp ne wit in simp_all)
qed

lemma AF_ubd_wit_holds_2:
  assumes conds: "AF_DFS_call_2_conds st"
    and A1: "AF_invar_1 st" and A2: "AF_invar_2 st" and A3: "AF_invar_3 st"
    and Afe: "AF_invar_feas st" and Afr: "AF_invar_free st" and AE: "AF_invar_estE st"
    and Aiter: "AF_invar_iter st" and AV: "AF_invar_V st" and wit: "AF_ubd_wit st"
  shows "AF_ubd_wit (AF_DFS_upd2 st)"
proof -
  from conds have ne: "af_vstack st \<noteq> []" and he: "in_has (af_in_arr st) (hd (af_vstack st))"
    by (auto elim!: call_cond_elims)
  have vV: "hd (af_vstack st) \<in> \<V>" using AV ne hd_in_set by (auto simp: AF_invar_V_def)
  have endp: "snd (in_current (af_in_arr st) (hd (af_vstack st))) = hd (af_vstack st) \<and>
              in_current (af_in_arr st) (hd (af_vstack st)) \<in> \<E>"
    using af_current_in_endpoint[OF _ vV he] Aiter by (auto simp: AF_invar_iter_def)
  let ?st' = "st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack st))\<rparr>"
  have A1': "AF_invar_1 ?st'" by (rule AF_invar_1_in_advance[OF vV A1])
  have inc: "(if False then fst (in_current (af_in_arr st) (hd (af_vstack st)))
             else snd (in_current (af_in_arr st) (hd (af_vstack st)))) = hd (af_vstack ?st')"
    using endp by simp
  show ?thesis unfolding AF_DFS_upd2_def Let_def
    by (rule af_handle_ubd_wit[OF A1' _ _ _ _ _ _ inc _ _]) (use A2 A3 Afe Afr AE endp ne wit in simp_all)
qed

lemma AF_ubd_wit_holds_3:
  "AF_DFS_call_3_conds st \<Longrightarrow> AF_ubd_wit st \<Longrightarrow> AF_ubd_wit (AF_DFS_upd3 st)"
  by (simp add: AF_DFS_upd3_def AF_ubd_wit_def)

text \<open>The witness invariant is preserved through the whole inner DFS.\<close>

lemma AF_DFS_ubd_wit:
  assumes dom: "AF_DFS_dom st" and mi0: "multigraph_inv out_arr in_arr"
  shows "AF_inv st \<longrightarrow> AF_ubd_wit st \<longrightarrow> AF_ubd_wit (AF_DFS st)"
proof (induction rule: AF_DFS_induct[OF dom])
  case IH: (1 st)
  show ?case
  proof (intro impI)
    assume inv: "AF_inv st" and wit: "AF_ubd_wit st"
    from inv have i1: "AF_invar_1 st" and i2: "AF_invar_2 st" and i3: "AF_invar_3 st"
      and iit: "AF_invar_iter st" and iV: "AF_invar_V st" and iE: "AF_invar_estE st"
      and ife: "AF_invar_feas st" and ifr: "AF_invar_free st" by (auto simp: AF_inv_def)
    show "AF_ubd_wit (AF_DFS st)"
    proof (rule AF_DFS_cases[where st = st])
      assume c: "AF_DFS_call_1_conds st"
      have "AF_ubd_wit (AF_DFS_upd1 st)" using AF_ubd_wit_holds_1[OF c i1 i2 i3 ife ifr iE iit iV wit] .
      thus ?thesis using IH(2)[OF c] AF_inv_holds_1[OF mi0 c inv] c
        by (auto simp: AF_DFS_simps[OF IH(1)])
    next
      assume c: "AF_DFS_call_2_conds st"
      have "AF_ubd_wit (AF_DFS_upd2 st)" using AF_ubd_wit_holds_2[OF c i1 i2 i3 ife ifr iE iit iV wit] .
      thus ?thesis using IH(3)[OF c] AF_inv_holds_2[OF mi0 c inv] c
        by (auto simp: AF_DFS_simps[OF IH(1)])
    next
      assume c: "AF_DFS_call_3_conds st"
      have "AF_ubd_wit (AF_DFS_upd3 st)" using AF_ubd_wit_holds_3[OF c wit] .
      thus ?thesis using IH(4)[OF c] AF_inv_holds_3[OF c inv] c
        by (auto simp: AF_DFS_simps[OF IH(1)])
    next
      assume c: "AF_DFS_ret_conds st"
      thus ?thesis using wit by (simp add: AF_DFS_simps[OF IH(1)] AF_DFS_ret_def)
    qed
  qed
qed

text \<open>Outer-loop level: the flag on the outer state likewise certifies a negative infinite-capacity cycle.
      Each launch inherits the property from the inner DFS (@{thm [source] AF_DFS_ubd_wit}); a skip leaves
      the flag untouched.\<close>

definition "AFF_ubd_wit st \<longleftrightarrow> (aff_unbounded st \<longrightarrow> neg_inf_cycle)"

lemma AFF_ubd_wit_holds_1:
  "AF_outer_call_1_conds st \<Longrightarrow> AFF_ubd_wit st \<Longrightarrow> AFF_ubd_wit (AF_outer_upd1 st)"
  by (simp add: AF_outer_upd1_def AFF_ubd_wit_def)

lemma AFF_ubd_wit_holds_2:
  assumes mi0: "multigraph_inv out_arr in_arr"
    and conds: "AF_outer_call_2_conds st" and inv: "AFF_inv st" and wit: "AFF_ubd_wit st"
  shows "AFF_ubd_wit (AF_outer_upd2 st)"
proof -
  from inv have ff: "flow_invar (aff_flow st)" and sti: "st_invar (aff_state st)"
    and aoi: "out_invar (aff_out_arr st)" and aii: "in_invar (aff_in_arr st)"
    and mii: "multigraph_inv (aff_out_arr st) (aff_in_arr st)" and feas: "af_cap_feasible (aff_flow st)"
    and noos: "\<not> aff_unbounded st \<longrightarrow> (\<forall>w\<in>\<V>. st_lookup (aff_state st) w \<noteq> OnStack)" by (auto simp: AFF_inv_def)
  from conds have nu: "\<not> aff_unbounded st" and hv: "has_vertex (aff_vit st)" by (auto simp: AF_outer_call_2_conds_def)
  let ?v = "current_vertex (aff_vit st)"
  have vV: "?v \<in> \<V>" using vit_current_V[OF inv hv] .
  have noos': "\<forall>w\<in>\<V>. st_lookup (aff_state st) w \<noteq> OnStack" using noos nu by simp
  let ?init = "AF_DFS_initial (aff_flow st) (aff_out_arr st) (aff_in_arr st) (aff_state st) ?v"
  have dom: "AF_DFS_dom ?init" using AF_DFS_dom[OF mi0 AF_inv_initial[OF ff sti aoi aii mii vV feas noos']] .
  have inv_init: "AF_inv ?init" using AF_inv_initial[OF ff sti aoi aii mii vV feas noos'] .
  have wit_init: "AF_ubd_wit ?init" by (simp add: AF_ubd_wit_def AF_DFS_initial_def)
  have "AF_ubd_wit (AF_DFS ?init)" using AF_DFS_ubd_wit[OF dom mi0] inv_init wit_init by blast
  hence "af_unbounded (AF_DFS ?init) \<longrightarrow> neg_inf_cycle" by (simp add: AF_ubd_wit_def)
  thus ?thesis by (simp add: AFF_ubd_wit_def AF_outer_upd2_def Let_def)
qed

lemma AF_outer_ubd_wit:
  assumes dom: "AF_outer_dom st" and mi0: "multigraph_inv out_arr in_arr"
    and inv: "AFF_inv st" and wit: "AFF_ubd_wit st"
  shows "AFF_ubd_wit (AF_outer st)"
  using inv wit proof (induction rule: AF_outer_induct[OF dom])
  case IH: (1 st)
  show ?case
    apply (rule AF_outer_cases[where st = st])
    subgoal
      using IH(2) AFF_inv_holds_1 AFF_ubd_wit_holds_1 IH(4,5)
      by (auto simp: AF_outer_simps[OF IH(1)])
    subgoal
      using IH(3) AFF_inv_holds_2[OF mi0] AFF_ubd_wit_holds_2[OF mi0] IH(4,5)
      by (auto simp: AF_outer_simps[OF IH(1)])
    subgoal using IH(5) by (auto simp: AF_outer_simps[OF IH(1)] AF_outer_ret_def)
    done
qed

text \<open>The unbounded top-level answer is sound: @{term None} exactly certifies a negative
      infinite-capacity directed cycle of original arcs --- a circulation of unbounded capacity and
      negative cost, along which the objective is unbounded below.\<close>

theorem make_acyclic_none_unbounded:
  assumes mi0: "multigraph_inv out_arr in_arr"
    and ff: "flow_invar f0" and feas: "af_feasible b f0"
    and vv: "vit_invar all_vertices" and vab: "vit_abstract all_vertices \<subseteq> \<V>"
    and res: "make_acyclic f0 = None"
  shows neg_inf_cycle
proof -
  have capf0: "af_cap_feasible f0" using feas
    by (rule af_feasible_cap)
  
  have dom: "AF_outer_dom (AF_outer_initial f0)" 
    using AF_outer_dom[OF mi0 AFF_inv_initial[OF mi0 ff capf0 vv vab]] .
  have wit0: "AFF_ubd_wit (AF_outer_initial f0)" by (simp add: AFF_ubd_wit_def AF_outer_initial_def)
  have "AFF_ubd_wit (AF_outer (AF_outer_initial f0))"
    using AF_outer_ubd_wit[OF dom mi0 AFF_inv_initial[OF mi0 ff capf0 vv vab] wit0] .
  moreover have "aff_unbounded (AF_outer (AF_outer_initial f0))"
    using res by (auto simp: make_acyclic_def Let_def split: if_splits)
  ultimately show ?thesis by (simp add: AFF_ubd_wit_def)
qed

end

end
