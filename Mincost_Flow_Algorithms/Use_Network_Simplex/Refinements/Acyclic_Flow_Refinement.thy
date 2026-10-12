theory Acyclic_Flow_Refinement
  imports Mincost_Flow_Algorithms.Acyclic_Flow 
          Separation_Logic_Imperative_HOL_Partial.Array_Blit
begin

section \<open>Imperative refinement of the acyclic-flow procedure\<close>

text \<open>This theory mirrors the functional specification locale @{locale acyclic_flow_impl_spec}, but
      every store the algorithm mutates --- the flow, the three-valued vertex-state map, the two
      per-vertex edge iterators, the vertex iterator of the outer loop and the three parallel DFS
      stacks --- is now a \<^emph>\<open>mutable heap object\<close>, and every operation is lifted into the @{typ \<open>_ Heap\<close>}
      monad. Every fixed operation and every derived constant carries an @{text \<open>_imp\<close>} suffix so that
      this locale can later be combined with the functional locales without name clashes.

      The refinement discipline is the standard Imperative-HOL one:
      \<^item> a functional operation that \<^emph>\<open>changes\<close> a data structure (a flow update, a vertex-state write,
        advancing / resetting an iterator) becomes an in-place mutation with result type
        @{typ \<open>unit Heap\<close>} --- the structure is changed but \<^emph>\<open>not returned\<close>;
      \<^item> a functional operation that \<^emph>\<open>changes a container and also returns a proper value\<close> drops the
        container from the returned tuple --- it is mutated in place --- and returns only the value(s) in
        the @{typ \<open>_ Heap\<close>} monad (e.g.\ the cancellation returns just its drop count and unbounded
        flag, the flow having been augmented in place);
      \<^item> a functional operation that \<^emph>\<open>computes a value\<close> (a lookup, an endpoint projection, a room /
        cost combination) returns that value in the @{typ \<open>_ Heap\<close>} monad;
      \<^item> pure arithmetic on values already read out of the heap stays pure.

      The three functional DFS stacks @{term af_vstack} / @{term af_estack} / @{term af_dstack} become
      three \<^emph>\<open>mutable arrays\<close> @{term ivstack} / @{term iestack} / @{term idstack} together with a
      \<^emph>\<open>stack pointer\<close> @{term sp} that is threaded as an ordinary @{typ nat} argument (a value on the
      heap), rather than a boxed length. The intended (never here assumed --- this belongs to the proof
      locale) layout is: @{term ivstack} holds the trail vertices in indices \<open>[0..<sp]\<close> with the
      top at \<open>sp - 1\<close>; for \<open>1 \<le> i < sp\<close> the entries \<open>iestack ! i\<close> /
      \<open>idstack ! i\<close> hold the arc / direction by which \<open>ivstack ! i\<close> was entered from its
      parent \<open>ivstack ! (i - 1)\<close>. Index \<open>0\<close> of the arc / direction stacks (the DFS root)
      is unused.

      The @{term af_unbounded} flag is not stored: exactly as the network-simplex loop returns a
      status value, the loops here \<^emph>\<open>return a boolean\<close> --- @{term True} meaning an unbounded
      instance (a negative infinite-capacity free cycle) was detected --- and leave the mutated flow store
      in place for the caller to read.

      This locale fixes only the imperative operations; it states \<^emph>\<open>no assumptions\<close>. Every text below
      describes how a fixed imperative function is meant to be used, it is not an axiom.\<close>

subsection \<open>The imperative program state\<close>

text \<open>The mutable program state. The flow, vertex-state, edge-iterator and vertex-iterator stores of
      the two functional program states become handles to heap objects (mutated in place, so the
      handles are threaded unchanged), plus the three DFS-stack arrays.\<close>

record ('farr, 'sarr, 'g, 'vvit, 'v, 'e) af_impl_state =
  iflow   :: 'farr        \<comment> \<open>current flow store\<close>
  istate  :: 'sarr        \<comment> \<open>three-valued vertex-state store\<close>
  iout    :: 'g           \<comment> \<open>outgoing edge-iterator store\<close>
  iin     :: 'g           \<comment> \<open>ingoing edge-iterator store\<close>
  ivit    :: 'vvit        \<comment> \<open>outer-loop vertex iterator\<close>
  ivstack :: "'v array"   \<comment> \<open>DFS vertex stack\<close>
  iestack :: "'e array"   \<comment> \<open>DFS entering-arc stack\<close>
  idstack :: "bool array" \<comment> \<open>DFS entering-direction stack\<close>

subsection \<open>The specification locale of the imperative operations\<close>

text \<open>The two edge iterators are per-vertex: @{term out_current_imp} / @{term in_current_imp} \<^emph>\<open>read\<close>
      the current outgoing / ingoing arc of a vertex, @{term out_has_imp} / @{term in_has_imp} report
      whether one is left, @{term out_move_imp} / @{term in_move_imp} advance the iterator \<^emph>\<open>in place\<close>,
      and @{term out_reset_imp} / @{term in_reset_imp} reset it to its full unconsumed state (copied
      from the pristine originals) \<^emph>\<open>in place\<close>. @{term flow_upd_imp} / @{term st_upd_imp} write, and
      @{term flow_lookup_imp} / @{term st_lookup_imp} read, the flow and vertex-state stores. The
      vertex iterator @{term current_vertex_imp} / @{term has_vertex_imp} / @{term move_on_vertex_imp}
      hands out the vertices of the outer loop, advancing in place. @{term cap_imp} reads an edge
      capacity (@{term \<open>- 1\<close>} = {\isasyminfinity}), @{term cost_imp} its unit cost, and @{term fst_exec_imp} /
      @{term snd_exec_imp} its two endpoints.\<close>

locale acyclic_flow_impl_refine =
  fixes out_current_imp   :: "'g \<Rightarrow> 'v::heap \<Rightarrow> 'e::heap Heap"
    and out_has_imp       :: "'g \<Rightarrow> 'v \<Rightarrow> bool Heap"
    and out_move_imp      :: "'g \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and out_reset_imp     :: "'g \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and in_current_imp    :: "'g \<Rightarrow> 'v \<Rightarrow> 'e Heap"
    and in_has_imp        :: "'g \<Rightarrow> 'v \<Rightarrow> bool Heap"
    and in_move_imp       :: "'g \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and in_reset_imp      :: "'g \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and flow_upd_imp      :: "'farr \<Rightarrow> 'e \<Rightarrow> ('n :: linordered_idom) \<Rightarrow> unit Heap"
    and flow_lookup_imp   :: "'farr \<Rightarrow> 'e \<Rightarrow> 'n Heap"
    and st_upd_imp        :: "'sarr \<Rightarrow> 'v \<Rightarrow> vertex_state \<Rightarrow> unit Heap"
    and st_lookup_imp     :: "'sarr \<Rightarrow> 'v \<Rightarrow> vertex_state Heap"
    and current_vertex_imp :: "'vvit \<Rightarrow> 'v Heap"
    and has_vertex_imp     :: "'vvit \<Rightarrow> bool Heap"
    and move_on_vertex_imp :: "'vvit \<Rightarrow> unit Heap"
    and cap_imp   :: "'e \<Rightarrow> 'n Heap"
    and cost_imp  :: "'e \<Rightarrow> 'n Heap"
    and fst_exec_imp :: "'e \<Rightarrow> 'v Heap"
    and snd_exec_imp :: "'e \<Rightarrow> 'v Heap"
begin

subsection \<open>Free arcs, rooms and costs\<close>

text \<open>Both directional rooms of an arc from a \<^emph>\<open>single\<close> read of its flow and capacity, as a pair
      @{term \<open>(forward, backward)\<close>}: forward @{term \<open>cap a - f a\<close>} (or @{term \<open>- 1\<close>}, i.e.\ unbounded,
      for an infinite capacity) and backward @{term \<open>f a\<close>}.\<close>
definition "af_rooms_imp s a =
  do { f \<leftarrow> flow_lookup_imp (iflow s) a; c \<leftarrow> cap_imp a;
       (let fwd = (if c = - 1 then - 1 else c - f) in return (fwd, f)) }"

text \<open>Marginal cost of pushing one unit along an arc in a direction.\<close>
definition "af_delta_cost_imp a dir = do { c \<leftarrow> cost_imp a; (let dc = (if dir then c else - c) in return dc) }"

text \<open>Minimum treating @{term \<open>- 1\<close>} as ``no bound'' --- pure, on values already read.\<close>
definition "af_min_imp x y = (if x = - 1 then y else if y = - 1 then x else min x y)"

text \<open>Push @{term \<gamma>} on one arc in place and \<^emph>\<open>return the new flow value\<close>, so a caller can test
      saturation without reading the value back.\<close>
definition "af_push_arc_imp \<gamma> a dir s =
  do { f0 \<leftarrow> flow_lookup_imp (iflow s) a;
       (let \<delta> = (if dir then \<gamma> else - \<gamma>); f = f0 + \<delta> in
        do { _ \<leftarrow> flow_upd_imp (iflow s) a f; return f }) }"

text \<open>Saturation test on an arc's \<^emph>\<open>already-computed\<close> new flow value @{term f} --- reads only
      @{term cap_imp}, not the flow again.\<close>
definition "af_saturated_imp f a = do { c \<leftarrow> cap_imp a; return (\<not> (0 < f \<and> (c = - 1 \<or> f < c))) }"

subsection \<open>The two cancellation passes over the stack segment\<close>

text \<open>First pass --- \<^emph>\<open>scan-until-@{term x}\<close>. Walk the DFS stack from the top \<open>sp - 1\<close> downward,
      at each index @{term i} reading the entering arc \<open>iestack ! i\<close> (tagged \<open>idstack ! i\<close>)
      and stopping once the \<^emph>\<open>parent\<close> vertex \<open>ivstack ! (i - 1)\<close> is the reached ancestor
      @{term x}. It accumulates the total marginal cost @{term k}, the as-is bottleneck room @{term ra}
      and the flipped bottleneck room @{term rf}; @{const af_min_imp} treats @{term \<open>- 1\<close>} as the
      neutral (unbounded) element. No intermediate list is built.\<close>
text \<open>The accumulator is threaded as \<^emph>\<open>three flat arguments\<close> @{term k} / @{term ra} / @{term rf}
      (rather than a boxed triple) so that the recursive call sits directly under a monadic bind, as in
      the network-simplex scan primitives; the collected triple is only assembled at the leaf.\<close>
partial_function (heap) af_scan_imp ::
  "('farr, 'sarr, 'g, 'vvit, 'v, 'e) af_impl_state \<Rightarrow> 'v \<Rightarrow> nat \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> ('n \<times> 'n \<times> 'n) Heap"
  where
  "af_scan_imp s x i k ra rf =
     do { a \<leftarrow> Array.nth (iestack s) i;
          d \<leftarrow> Array.nth (idstack s) i;
          updn \<leftarrow> af_rooms_imp s a;
          dc \<leftarrow> af_delta_cost_imp a d;
          p \<leftarrow> Array.nth (ivstack s) (i - 1);
          (let up = fst updn; dn = snd updn;
               ru = (if d then up else dn);
               rd = (if d then dn else up);
               k'  = k + dc;
               ra' = af_min_imp ru ra;
               rf' = af_min_imp rd rf
           in if p = x then return (k', ra', rf') else af_scan_imp s x (i - 1) k' ra' rf') }"

text \<open>Second pass --- push @{term \<gamma>} around the same cycle \<^emph>\<open>and\<close> locate the bottleneck. Each cycle arc
      is pushed once (negating its tag via @{term \<open>d \<noteq> flip\<close>}); right after the push the arc is tested
      for saturation. The pass returns the \<^emph>\<open>drop count\<close> \<open>m'\<close> = one more than the index of the
      \<^emph>\<open>deepest\<close> arc that saturated, or @{term 0} if none but the closing arc did.

      To keep the pass in \<^emph>\<open>constant stack space\<close> it is written \<^emph>\<open>tail-recursively\<close>: rather than
      combine a result read back from the recursive call, it threads two flat @{typ nat} arguments ---
      the running depth @{term dep} (@{term 1} at the top) and the deepest saturated depth @{term best}
      seen so far (@{term 0} = none). Because the walk descends towards @{term x}, a later (deeper) hit
      simply overwrites @{term best}, so at the leaf @{term best} already \<^emph>\<open>is\<close> @{term \<open>m'\<close>}. The flow
      is mutated in place.\<close>
partial_function (heap) af_push_imp ::
  "('farr, 'sarr, 'g, 'vvit, 'v, 'e) af_impl_state \<Rightarrow> 'n \<Rightarrow> 'v \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap"
  where
  "af_push_imp s \<gamma> x i flip dep best =
     do { a \<leftarrow> Array.nth (iestack s) i;
          d \<leftarrow> Array.nth (idstack s) i;
          f \<leftarrow> af_push_arc_imp \<gamma> a (d \<noteq> flip) s;
          sat \<leftarrow> af_saturated_imp f a;
          p \<leftarrow> Array.nth (ivstack s) (i - 1);
          (let best' = (if sat then dep else best)
           in if p = x then return best' else af_push_imp s \<gamma> x (i - 1) flip (dep + 1) best') }"

text \<open>Cancel the tagged closed cycle --- the stack segment from the top down to the reached ancestor
      @{term x} (walked by @{const af_scan_imp} / @{const af_push_imp}, never materialised) closed by the
      arc @{term a} in direction @{term dir}, whose two rooms @{term up} / @{term dn} the caller already
      read. Returns only the \<^emph>\<open>drop count\<close> \<open>m'\<close> and the \<^emph>\<open>unbounded\<close> flag; the flow is augmented
      in place. Cost-neutral infinite-cycle handling matches the functional \<open>af_cancel_seg\<close>: push in the
      non-positive-cost orientation, and when that direction is unbounded either flip to the finite
      cost-neutral one or, failing that, report unboundedness.\<close>
definition "af_cancel_seg_imp s up dn x a dir sp =
  (let ra0 = (if dir then up else dn); rf0 = (if dir then dn else up) in
   do { dc0 \<leftarrow> af_delta_cost_imp a dir;
        kraf \<leftarrow> af_scan_imp s x (sp - 1) dc0 ra0 rf0;
        (case kraf of (k, ra, rf) \<Rightarrow>
           (let flip = 0 < k; \<gamma> = (if flip then rf else ra) in
            if \<gamma> \<noteq> - 1 then
              do { m' \<leftarrow> af_push_imp s \<gamma> x (sp - 1) flip 1 0;
                   _ \<leftarrow> af_push_arc_imp \<gamma> a (dir \<noteq> flip) s;
                   return (m', False) }
            else if k = 0 \<and> rf \<noteq> - 1 then
              do { m' \<leftarrow> af_push_imp s rf x (sp - 1) True 1 0;
                   _ \<leftarrow> af_push_arc_imp rf a (dir \<noteq> True) s;
                   return (m', False) }
            else return (0, True))) })"

subsection \<open>Truncation clean-up and self-loops\<close>

text \<open>Reset one vertex's two edge iterators to their pristine unconsumed state, in place.\<close>
definition "af_reset_imp s v = do { _ \<leftarrow> out_reset_imp (iout s) v; in_reset_imp (iin s) v }"

text \<open>Fused truncation clean-up: over the top @{term n} (= \<open>m'\<close>) stack vertices --- indices
      @{term i}, @{term \<open>i - 1\<close>}, {\isasymdots} --- in \<^emph>\<open>one\<close> walk set each back to @{term Unseen} and reset its
      iterators. The surviving endpoint just below is not touched.\<close>
partial_function (heap) af_reset_unsee_seg_imp ::
  "('farr, 'sarr, 'g, 'vvit, 'v, 'e) af_impl_state \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap"
  where
  "af_reset_unsee_seg_imp s n i =
     (if n = 0 then return ()
      else do { v \<leftarrow> Array.nth (ivstack s) i;
                _ \<leftarrow> st_upd_imp (istate s) v Unseen;
                _ \<leftarrow> af_reset_imp s v;
                af_reset_unsee_seg_imp s (n - 1) (i - 1) })"

text \<open>Cost-directed normalisation of a self-loop @{term a} (\<open>fst a = snd a\<close>): a negative-cost
      loop is filled to its capacity (an \<^emph>\<open>infinite\<close>-capacity one certifies unboundedness), every
      non-negative-cost loop is emptied. Mutates the flow in place; returns the unbounded flag.\<close>
definition "af_selfloop_handle_imp s a =
  do { co \<leftarrow> cost_imp a;
       (if co < 0
        then do { c \<leftarrow> cap_imp a;
                  (if c = - 1 then return True
                   else do { f \<leftarrow> flow_lookup_imp (iflow s) a;
                             (if f = c then return False
                              else do { _ \<leftarrow> flow_upd_imp (iflow s) a c; return False }) }) }
        else do { f \<leftarrow> flow_lookup_imp (iflow s) a;
                  (if f = 0 then return False
                   else do { _ \<leftarrow> flow_upd_imp (iflow s) a 0; return False }) }) }"

subsection \<open>Processing one incident free arc\<close>

text \<open>Process one incident arc @{term a} of the current top vertex, traversed in direction @{term dir},
      given the current stack pointer @{term sp}. All mutation is in place; the returned pair is the
      \<^emph>\<open>new stack pointer\<close> and the \<^emph>\<open>unbounded\<close> flag. A self-loop is normalised on sight; a
      non-free arc, the parent arc, and an arc to a @{term Finished} vertex are no-ops (@{term sp}
      unchanged); an arc to an @{term OnStack} vertex closes a cycle --- cancelled, the stack truncated by
      the drop count and the dropped vertices reset --- and an arc to an @{term Unseen} vertex pushes it.\<close>
text \<open>Cycle-closing case (an @{term OnStack} target): cancel the cycle in place, then either report
      unboundedness or truncate the stack by the drop count @{term \<open>m'\<close>} and reset the dropped vertices.\<close>
definition "af_close_cycle_imp s up dn x a dir sp =
  do { mubd \<leftarrow> af_cancel_seg_imp s up dn x a dir sp;
       (case mubd of (m', ubd) \<Rightarrow>
          if ubd then return (sp, True)
          else do { _ \<leftarrow> af_reset_unsee_seg_imp s m' (sp - 1);
                    return (sp - m', False) }) }"

text \<open>Fresh-vertex case (an @{term Unseen} target): push @{term x}, entered by arc @{term a} in
      direction @{term dir}, onto the top of the three stacks and mark it @{term OnStack}.\<close>
definition "af_push_vertex_imp s x a dir sp =
  do { _ \<leftarrow> Array.upd sp x (ivstack s);
       _ \<leftarrow> Array.upd sp a (iestack s);
       _ \<leftarrow> Array.upd sp dir (idstack s);
       _ \<leftarrow> st_upd_imp (istate s) x OnStack;
       return (sp + 1, False) }"

text \<open>Process one incident arc @{term a} of the current top vertex, traversed in direction @{term dir},
      given the current stack pointer @{term sp}. All mutation is in place; the returned pair is the
      \<^emph>\<open>new stack pointer\<close> and the \<^emph>\<open>unbounded\<close> flag. A self-loop is normalised on sight; a
      non-free arc, the parent arc, and an arc to a @{term Finished} vertex are no-ops (@{term sp}
      unchanged); an arc to an @{term OnStack} vertex closes a cycle and an arc to an @{term Unseen}
      vertex pushes it.\<close>
definition "af_handle_imp s a dir sp =
  do { fe \<leftarrow> fst_exec_imp a;
       se \<leftarrow> snd_exec_imp a;
       (if fe = se then do { ubd \<leftarrow> af_selfloop_handle_imp s a; return (sp, ubd) }
        else do {
          updn \<leftarrow> af_rooms_imp s a;
          (if \<not> (0 < snd updn \<and> (fst updn = - 1 \<or> 0 < fst updn)) then return (sp, False)
           else do {
             is_parent \<leftarrow> (if 2 \<le> sp
                          then do { top_e \<leftarrow> Array.nth (iestack s) (sp - 1); return (a = top_e) }
                          else return False);
             (if is_parent then return (sp, False)
              else (let x = (if dir then se else fe) in
                do { stx \<leftarrow> st_lookup_imp (istate s) x;
                     (case stx of
                        Finished \<Rightarrow> return (sp, False)
                      | OnStack \<Rightarrow> af_close_cycle_imp s (fst updn) (snd updn) x a dir sp
                      | Unseen \<Rightarrow> af_push_vertex_imp s x a dir sp) })) }) }) }"

subsection \<open>The inner DFS-like procedure\<close>

text \<open>The inner loop, threading the stack pointer @{term sp}. An empty stack (@{term \<open>sp = 0\<close>}) returns
      ``bounded''. Otherwise the top vertex is scanned: an outgoing free arc first (the current arc is
      read, the iterator advanced in place, then @{const af_handle_imp} run), then an ingoing one, then
      backtrack --- mark the top @{term Finished} and pop (@{term \<open>sp - 1\<close>}). As soon as
      @{const af_handle_imp} reports unboundedness the loop returns @{term True}.\<close>
partial_function (heap) AF_DFS_imp ::
  "('farr, 'sarr, 'g, 'vvit, 'v, 'e) af_impl_state \<Rightarrow> nat \<Rightarrow> bool Heap"
  where
  "AF_DFS_imp s sp =
     (if sp = 0 then return False
      else do {
        v \<leftarrow> Array.nth (ivstack s) (sp - 1);
        oh \<leftarrow> out_has_imp (iout s) v;
        (if oh
         then do { a \<leftarrow> out_current_imp (iout s) v;
                   _ \<leftarrow> out_move_imp (iout s) v;
                   (sp', ubd) \<leftarrow> af_handle_imp s a True sp;
                   if ubd then return True else AF_DFS_imp s sp' }
         else do {
           ih \<leftarrow> in_has_imp (iin s) v;
           (if ih
            then do { a \<leftarrow> in_current_imp (iin s) v;
                      _ \<leftarrow> in_move_imp (iin s) v;
                      (sp', ubd) \<leftarrow> af_handle_imp s a False sp;
                      if ubd then return True else AF_DFS_imp s sp' }
            else do { _ \<leftarrow> st_upd_imp (istate s) v Finished;
                      AF_DFS_imp s (sp - 1) }) }) })"

text \<open>Launch the inner DFS from an unseen vertex @{term v}: seed the stack with @{term v} at index
      @{term 0} (so @{term \<open>sp = 1\<close>}), mark it @{term OnStack}, and run. Returns the unbounded flag.\<close>
definition "af_dfs_start_imp s v =
  do { _ \<leftarrow> Array.upd 0 v (ivstack s);
       _ \<leftarrow> st_upd_imp (istate s) v OnStack;
       AF_DFS_imp s 1 }"

subsection \<open>The outer loop over vertices\<close>

text \<open>Hand out the vertices one by one through the vertex iterator (advanced in place); whenever a
      vertex is still @{term Unseen}, launch the inner DFS from it and thread on. Returns @{term True}
      as soon as an unbounded instance is detected, else @{term False} when the iterator is exhausted;
      the acyclic flow is left in @{term \<open>iflow s\<close>}.\<close>
partial_function (heap) AF_outer_imp ::
  "('farr, 'sarr, 'g, 'vvit, 'v, 'e) af_impl_state \<Rightarrow> bool Heap"
  where
  "AF_outer_imp s =
     do { hv \<leftarrow> has_vertex_imp (ivit s);
          (if \<not> hv then return False
           else do {
             v \<leftarrow> current_vertex_imp (ivit s);
             _ \<leftarrow> move_on_vertex_imp (ivit s);
             stv \<leftarrow> st_lookup_imp (istate s) v;
             (if stv \<noteq> Unseen then AF_outer_imp s
              else do { ubd \<leftarrow> af_dfs_start_imp s v;
                        if ubd then return True else AF_outer_imp s }) }) }"

text \<open>The initial imperative state is \<^emph>\<open>assembled from externally supplied handles and arrays\<close>: the
      flow store @{term fl}, the vertex-state store @{term stt}, the two edge-iterator stores
      @{term oa} / @{term ia}, the vertex iterator @{term vit}, and --- crucially --- the three DFS-stack
      arrays @{term vst} / @{term est} / @{term dst}. \<^emph>\<open>Every non-constant amount of memory therefore
      originates outside this locale\<close>: the caller allocates the stores and the three size-@{text \<open>\<ge> |V|\<close>}
      stack arrays and hands them in; the assembly below is a constant-size record of handles and the
      whole procedure adds only O(1) working memory on top. This mirrors the functional
      @{term AF_outer_initial}, except that there the stores are fixed locale constants
      (@{term state_init}, @{term all_vertices}, @{term out_arr}, @{term in_arr}) whereas here they are
      inputs (mutable heap objects the caller owns), and the stacks are explicit arrays rather than
      lists grown on the heap.

      The contract the caller must establish (used, never assumed here): @{term stt} maps every vertex
      to @{term Unseen}, @{term oa} / @{term ia} are the pristine full iterators, @{term vit} is at the
      start of the vertex order, and @{term vst} / @{term est} / @{term dst} have length at least the
      number of vertices.\<close>
definition af_impl_state_init ::
  "'farr \<Rightarrow> 'sarr \<Rightarrow> 'g \<Rightarrow> 'g \<Rightarrow> 'vvit \<Rightarrow> 'v array \<Rightarrow> 'e array \<Rightarrow> bool array \<Rightarrow>
     ('farr, 'sarr, 'g, 'vvit, 'v, 'e) af_impl_state" where
  "af_impl_state_init fl stt oa ia vit vst est dst =
     \<lparr> iflow = fl, istate = stt, iout = oa, iin = ia, ivit = vit,
       ivstack = vst, iestack = est, idstack = dst \<rparr>"

text \<open>Top-level entry point: assemble the state from the externally supplied stores and stack arrays,
      then make the flow acyclic \<^emph>\<open>in place\<close>. The returned boolean is @{term True} for an \<^emph>\<open>unbounded\<close>
      instance (the functional @{term None}) and @{term False} otherwise, with the resulting acyclic
      flow readable from the supplied flow store @{term fl} (the functional @{term \<open>Some (aff_flow res)\<close>}).\<close>
definition "make_acyclic_imp fl stt oa ia vit vst est dst =
   AF_outer_imp (af_impl_state_init fl stt oa ia vit vst est dst)"

end

section \<open>The refinement proof locale\<close>

text \<open>The proof locale combines the functional proof locale @{locale acyclic_flow_impl} --- which
      supplies the cost-flow network (hence the vertex set @{term \<V>} and edge set @{term \<E>}), the
      functional ADT operations and \<^emph>\<open>all their assumed laws\<close>, and the correctness of the functional
      \<open>make_acyclic\<close> --- with the imperative code locale @{locale acyclic_flow_impl_refine}.

      For each mutable store it fixes a \<^emph>\<open>representation assertion\<close> relating a functional store value to
      its imperative heap handle (@{typ assn} is the separation-logic heap predicate): @{term flow_assn}
      for the flow, @{term state_assn} for the vertex-state map, @{term out_assn} and @{term in_assn} for the
      outgoing and the ingoing edge-iterator collection (at @{term iout} and @{term iin}), and @{term vit_assn} for
      the vertex iterator.

      It then \<^emph>\<open>assumes one Hoare triple per imperative operation\<close>. The discipline is:
      \<^item> a mutating operation (result @{typ \<open>unit Heap\<close>}) turns the pre-representation of the store into
        the representation of the \<^emph>\<open>functionally updated\<close> store, with no returned value;
      \<^item> a reading operation returns the value the \<^emph>\<open>functional\<close> operation computes, keeping the
        representation unchanged;
      \<^item> the pure endpoint / capacity / cost reads have an empty footprint.

      Crucially, the \<^emph>\<open>pure logical preconditions of each triple are exactly the hypotheses of the
      corresponding functional ADT law(s)\<close> --- the refinement assertion alone does not guarantee that the
      \<^emph>\<open>inputs have the right structure\<close> (the ADT invariant, the key-set membership, a non-empty
      remainder), so those hypotheses must \<^emph>\<open>still be assumed\<close>. For the flow store that is
      @{term \<open>flow_invar Fl\<close>} together with the key-set membership @{term \<open>e \<in> \<E>\<close>} (mirroring the law
      \<open>fixed_univ_map.fixed_univ_map_upd\<close>); for the vertex-state store @{term \<open>st_invar St\<close>} and
      @{term \<open>v \<in> \<V>\<close>}; for the two indexed edge iterators @{term \<open>out_invar G\<close>} resp.\ @{term \<open>in_invar G\<close>},
      @{term \<open>v \<in> \<V>\<close>}, and --- for the \<open>current\<close>/\<open>move\<close> steps --- the extra @{term \<open>out_remaining G v \<noteq> {}\<close>}
      / @{term \<open>in_remaining G v \<noteq> {}\<close>} (mirroring \<open>indexed_iterable_set.idx_current\<close> and
      \<open>indexed_iterable_set.idx_move_invar\<close>); and for the vertex iterator @{term \<open>vit_invar Vit\<close>} plus,
      for \<open>current\<close>/\<open>move_on\<close>, @{term \<open>vit_remaining Vit \<noteq> {}\<close>} (mirroring \<open>iterable_set.has_current\<close>
      and \<open>iterable_set.current_element\<close>).\<close>

locale acyclic_flow_impl_refine_proof =
  acyclic_flow_impl where flow_lookup = flow_lookup and st_lookup = st_lookup
      and out_current = out_current and current_vertex = current_vertex +
  acyclic_flow_impl_refine where flow_lookup_imp = flow_lookup_imp and st_lookup_imp = st_lookup_imp
      and out_current_imp = out_current_imp and current_vertex_imp = current_vertex_imp
  for flow_lookup       :: "'farr \<Rightarrow> 'e::heap \<Rightarrow> ('n::linordered_idom)"
    and flow_lookup_imp   :: "'farri \<Rightarrow> 'e \<Rightarrow> 'n Heap"
    and st_lookup         :: "'sarr \<Rightarrow> 'v::heap \<Rightarrow> vertex_state"
    and st_lookup_imp     :: "'sarri \<Rightarrow> 'v \<Rightarrow> vertex_state Heap"
    and out_current       :: "'g \<Rightarrow> 'v \<Rightarrow> 'e"
    and out_current_imp   :: "'gi \<Rightarrow> 'v \<Rightarrow> 'e Heap"
    and current_vertex    :: "'vvit \<Rightarrow> 'v"
    and current_vertex_imp :: "'vviti \<Rightarrow> 'v Heap" +
  fixes flow_assn  :: "'farr \<Rightarrow> 'farri \<Rightarrow> assn"
    and state_assn :: "'sarr \<Rightarrow> 'sarri \<Rightarrow> assn"
    and out_assn :: "'g \<Rightarrow> 'gi \<Rightarrow> assn"
    and in_assn :: "'g \<Rightarrow> 'gi \<Rightarrow> assn"
    and vit_assn   :: "'vvit \<Rightarrow> 'vviti \<Rightarrow> assn"
    and rd         :: assn  \<comment> \<open>footprint of the (read-only) per-edge cap / cost / endpoint stores\<close>
    and Lvst :: nat and Lest :: nat and Ldst :: nat
      \<comment> \<open>the (fixed) physical lengths of the three caller-supplied DFS stack arrays.  Imperative-HOL
         arrays never change length, but a purely existential postcondition forgets that, and the
         caller (which reuses these arrays afterwards) needs it back.  The acyclifier's own
         requirement stays the lower bound in terms of the vertex count, kept alongside.\<close>
  assumes
    \<comment> \<open>flow store --- an @{locale fixed_univ_map} with key set @{term \<E>}\<close>
    flow_lookup_rule:
      "\<lbrakk>flow_invar Fl; e \<in> \<E>\<rbrakk> \<Longrightarrow> <flow_assn Fl fh> flow_lookup_imp fh e
                 <\<lambda>r. flow_assn Fl fh * \<up>(r = flow_lookup Fl e)>"
    and flow_upd_rule:
      "\<lbrakk>flow_invar Fl; e \<in> \<E>\<rbrakk> \<Longrightarrow> <flow_assn Fl fh> flow_upd_imp fh e w
                 <\<lambda>_. flow_assn (flow_upd Fl e w) fh>"
    \<comment> \<open>vertex-state store --- an @{locale fixed_univ_map} with key set @{term \<V>}\<close>
    and st_lookup_rule:
      "\<lbrakk>st_invar St; v \<in> \<V>\<rbrakk> \<Longrightarrow> <state_assn St sh> st_lookup_imp sh v
                 <\<lambda>r. state_assn St sh * \<up>(r = st_lookup St v)>"
    and st_upd_rule:
      "\<lbrakk>st_invar St; v \<in> \<V>\<rbrakk> \<Longrightarrow> <state_assn St sh> st_upd_imp sh v q
                 <\<lambda>_. state_assn (st_upd St v q) sh>"
    \<comment> \<open>outgoing edge iterator --- an @{locale indexed_iterable_set} with key set @{term \<V>}\<close>
    and out_has_rule:
      "\<lbrakk>out_invar G; v \<in> \<V>\<rbrakk> \<Longrightarrow> <out_assn G gh> out_has_imp gh v
                 <\<lambda>r. out_assn G gh * \<up>(r = out_has G v)>"
    and out_current_rule:
      "\<lbrakk>out_invar G; v \<in> \<V>; out_remaining G v \<noteq> {}\<rbrakk> \<Longrightarrow> <out_assn G gh> out_current_imp gh v
                 <\<lambda>r. out_assn G gh * \<up>(r = out_current G v)>"
    and out_move_rule:
      "\<lbrakk>out_invar G; v \<in> \<V>; out_remaining G v \<noteq> {}\<rbrakk> \<Longrightarrow> <out_assn G gh> out_move_imp gh v
                 <\<lambda>_. out_assn (out_move G v) gh>"
    and out_reset_rule:
      "\<lbrakk>out_invar G; v \<in> \<V>\<rbrakk> \<Longrightarrow> <out_assn G gh> out_reset_imp gh v
                 <\<lambda>_. out_assn (out_reset G v) gh>"
    \<comment> \<open>ingoing edge iterator --- an @{locale indexed_iterable_set} with key set @{term \<V>}\<close>
    and in_has_rule:
      "\<lbrakk>in_invar G; v \<in> \<V>\<rbrakk> \<Longrightarrow> <in_assn G gh> in_has_imp gh v
                 <\<lambda>r. in_assn G gh * \<up>(r = in_has G v)>"
    and in_current_rule:
      "\<lbrakk>in_invar G; v \<in> \<V>; in_remaining G v \<noteq> {}\<rbrakk> \<Longrightarrow> <in_assn G gh> in_current_imp gh v
                 <\<lambda>r. in_assn G gh * \<up>(r = in_current G v)>"
    and in_move_rule:
      "\<lbrakk>in_invar G; v \<in> \<V>; in_remaining G v \<noteq> {}\<rbrakk> \<Longrightarrow> <in_assn G gh> in_move_imp gh v
                 <\<lambda>_. in_assn (in_move G v) gh>"
    and in_reset_rule:
      "\<lbrakk>in_invar G; v \<in> \<V>\<rbrakk> \<Longrightarrow> <in_assn G gh> in_reset_imp gh v
                 <\<lambda>_. in_assn (in_reset G v) gh>"
    \<comment> \<open>vertex iterator --- an @{locale iterable_set}\<close>
    and has_vertex_rule:
      "vit_invar Vit \<Longrightarrow> <vit_assn Vit vh> has_vertex_imp vh
                 <\<lambda>r. vit_assn Vit vh * \<up>(r = has_vertex Vit)>"
    and current_vertex_rule:
      "\<lbrakk>vit_invar Vit; vit_remaining Vit \<noteq> {}\<rbrakk> \<Longrightarrow> <vit_assn Vit vh> current_vertex_imp vh
                 <\<lambda>r. vit_assn Vit vh * \<up>(r = current_vertex Vit)>"
    and move_on_vertex_rule:
      "\<lbrakk>vit_invar Vit; vit_remaining Vit \<noteq> {}\<rbrakk> \<Longrightarrow> <vit_assn Vit vh> move_on_vertex_imp vh
                 <\<lambda>_. vit_assn (move_on_vertex Vit) vh>"
    \<comment> \<open>pure per-edge reads --- empty heap footprint; the same @{term \<open>e \<in> \<E>\<close>} the functional encoding
        axioms (\<open>cap_encoding\<close>, \<open>cost_encoding\<close>, \<open>fst_exec_eq\<close>, \<open>snd_exec_eq\<close>) assume, so a bounded
        (e.g.\ @{term \<E>}-indexed) implementation is provable and all that knowledge is available\<close>
    and cap_rule:      "e \<in> \<E> \<Longrightarrow> <rd> cap_imp e      <\<lambda>r. rd * \<up>(r = cap e)>"
    and cost_rule:     "e \<in> \<E> \<Longrightarrow> <rd> cost_imp e     <\<lambda>r. rd * \<up>(r = cost e)>"
    and fst_exec_rule: "e \<in> \<E> \<Longrightarrow> <rd> fst_exec_imp e <\<lambda>r. rd * \<up>(r = fst_exec e)>"
    and snd_exec_rule: "e \<in> \<E> \<Longrightarrow> <rd> snd_exec_imp e <\<lambda>r. rd * \<up>(r = snd_exec e)>"
begin

subsection \<open>Refinement of the derived leaf operations\<close>

text \<open>The assumed per-operation Hoare triples are registered for @{method sep_auto}; each derived read
      / write then refines its functional counterpart by a one-line separation-logic proof.\<close>
lemmas [sep_heap_rules] =
  flow_lookup_rule flow_upd_rule st_lookup_rule st_upd_rule
  out_has_rule out_current_rule out_move_rule out_reset_rule
  in_has_rule in_current_rule in_move_rule in_reset_rule
  has_vertex_rule current_vertex_rule move_on_vertex_rule
  cap_rule cost_rule fst_exec_rule snd_exec_rule

text \<open>The @{term \<open>- 1\<close>}-as-{\isasyminfinity} minimum is purely functional and identical to @{const af_min}.\<close>
lemma af_min_imp_eq: "af_min_imp x y = af_min x y"
  by (simp add: af_min_imp_def af_min_def)

text \<open>Both directional rooms of an arc, from one read of flow and capacity.\<close>
lemma af_rooms_imp_rule [sep_heap_rules]:
  "\<lbrakk>flow_invar Fl; a \<in> \<E>\<rbrakk> \<Longrightarrow>
   <flow_assn Fl (iflow s) * rd> af_rooms_imp s a
   <\<lambda>r. flow_assn Fl (iflow s) * rd * \<up>(r = af_rooms Fl a)>"
  unfolding af_rooms_imp_def af_rooms_def by (sep_auto simp: Let_def)

text \<open>Marginal cost of pushing one unit along an arc.\<close>
lemma af_delta_cost_imp_rule [sep_heap_rules]:
  "a \<in> \<E> \<Longrightarrow> <rd> af_delta_cost_imp a dir <\<lambda>r. rd * \<up>(r = af_delta_cost a dir)>"
  unfolding af_delta_cost_imp_def af_delta_cost_def by (sep_auto simp: Let_def)

text \<open>Saturation test on an already-computed flow value.\<close>
lemma af_saturated_imp_rule [sep_heap_rules]:
  "a \<in> \<E> \<Longrightarrow> <rd> af_saturated_imp f a <\<lambda>r. rd * \<up>(r = af_saturated f a)>"
  unfolding af_saturated_imp_def af_saturated_def by (sep_auto simp: Let_def)

text \<open>Push @{term \<gamma>} on one arc in place, returning the new flow value --- the imperative counterpart of
      @{const af_push_arc} with the flow store mutated in place.\<close>
lemma af_push_arc_imp_rule [sep_heap_rules]:
  "\<lbrakk>flow_invar Fl; a \<in> \<E>\<rbrakk> \<Longrightarrow>
   <flow_assn Fl (iflow s)> af_push_arc_imp \<gamma> a dir s
   <\<lambda>r. flow_assn (flow_upd Fl a (flow_lookup Fl a + (if dir then \<gamma> else - \<gamma>))) (iflow s)
        * \<up>(r = flow_lookup Fl a + (if dir then \<gamma> else - \<gamma>))>"
  unfolding af_push_arc_imp_def Let_def by sep_auto

subsection \<open>Refinement relations for the DFS state and the outer state\<close>

text \<open>@{term dfs_rel} ties an \<open>AF_DFS_state\<close> to an imperative \<open>af_impl_state\<close> and a stack
      pointer @{term sp}: the four stores relate through their assertions, and the three stack \<^emph>\<open>arrays\<close>
      (existentially quantified, allocated with room @{term \<open>card \<V>\<close>}) carry the functional stacks
      through @{term \<open>af_vstack st = rev (take sp vl)\<close>} (top at index @{term \<open>sp - 1\<close>}) and the shifted
      arc/direction correspondences (index @{term 0} unused). @{term outer_rel} is the analogue for the
      outer loop, additionally relating the vertex iterator.\<close>

definition dfs_rel :: "('v,'e,'farr,'g,'sarr) AF_DFS_state \<Rightarrow> ('farri,'sarri,'gi,'vviti,'v,'e) af_impl_state \<Rightarrow> nat \<Rightarrow> assn" where
  "dfs_rel st s sp = rd *
     flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) *
     out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) *
     (\<exists>\<^sub>A vl el dl. ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl *
        \<up>( card \<V> \<le> length vl \<and> card \<V> \<le> length el \<and> card \<V> \<le> length dl \<and> sp \<le> card \<V> \<and>
           af_vstack st = rev (take sp vl) \<and>
           af_estack st = rev (drop (Suc 0) (take sp el)) \<and>
           af_dstack st = rev (drop (Suc 0) (take sp dl)) \<and>
           length vl = Lvst \<and> length el = Lest \<and> length dl = Ldst))"

definition outer_rel :: "('v,'farr,'sarr,'vvit,'g) AF_state \<Rightarrow> ('farri,'sarri,'gi,'vviti,'v,'e) af_impl_state \<Rightarrow> assn" where
  "outer_rel st s = rd *
     flow_assn (aff_flow st) (iflow s) * state_assn (aff_state st) (istate s) *
     out_assn (aff_out_arr st) (iout s) * in_assn (aff_in_arr st) (iin s) *
     vit_assn (aff_vit st) (ivit s) *
     (\<exists>\<^sub>A vl el dl. ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl *
        \<up>( card \<V> \<le> length vl \<and> card \<V> \<le> length el \<and> card \<V> \<le> length dl \<and>
           length vl = Lvst \<and> length el = Lest \<and> length dl = Ldst))"

subsection \<open>Sorried refinement lemmas, one per remaining operation --- filled top to bottom\<close>

text \<open>\<^emph>\<open>Scaffold.\<close> One Hoare-triple refinement obligation per imperative function of the program,
      each stating that the operation refines its functional counterpart. They are stated first and
      discharged from the top (leaf recursions) downwards to the top-level @{const make_acyclic_imp}.
      @{command declare} @{text quick_and_dirty} enables the placeholder @{command sorry} proofs and is
      removed once every obligation below is closed.\<close>
declare [[quick_and_dirty = true]]

text \<open>First cancellation pass: @{const af_scan_imp} walking the stack arrays from index @{term i}
      downwards refines @{const af_scan} on the corresponding stack sub-lists.\<close>
lemma af_scan_imp_rule:
  "\<lbrakk>flow_invar Fl; i < length vl; i < length el; i < length dl;
    set (drop (Suc 0) (take (Suc i) el)) \<subseteq> \<E>; x \<in> set (take i vl)\<rbrakk> \<Longrightarrow>
   <flow_assn Fl (iflow s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd>
     af_scan_imp s x i k ra rf
   <\<lambda>r. flow_assn Fl (iflow s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd *
        \<up>(r = af_scan Fl x (rev (take (Suc i) vl)) (rev (drop (Suc 0) (take (Suc i) el)))
                          (rev (drop (Suc 0) (take (Suc i) dl))) (k, ra, rf))>"
proof (induction i arbitrary: k ra rf)
  case 0 then show ?case by simp
next
  case (Suc i)
  have D: "rev (take (Suc i) vl) = vl ! i # rev (take i vl)"
    using Suc.prems(2) by (simp add: take_Suc_conv_app_nth Suc_lessD)
  have Dvl: "rev (take (Suc (Suc i)) vl) = vl ! Suc i # vl ! i # rev (take i vl)"
    using Suc.prems(2) D by (simp add: take_Suc_conv_app_nth)
  have Del: "rev (drop (Suc 0) (take (Suc (Suc i)) el)) = el ! Suc i # rev (drop (Suc 0) (take (Suc i) el))"
    using take_Suc_conv_app_nth[OF Suc.prems(3)] Suc.prems(3) by (simp add: drop_append)
  have Ddl: "rev (drop (Suc 0) (take (Suc (Suc i)) dl)) = dl ! Suc i # rev (drop (Suc 0) (take (Suc i) dl))"
    using take_Suc_conv_app_nth[OF Suc.prems(4)] Suc.prems(4) by (simp add: drop_append)
  have ael: "el ! Suc i \<in> \<E>" using Del Suc.prems(5) by auto
  have F: "af_scan Fl x (rev (take (Suc (Suc i)) vl)) (rev (drop (Suc 0) (take (Suc (Suc i)) el)))
              (rev (drop (Suc 0) (take (Suc (Suc i)) dl))) (k, ra, rf) =
           af_scan Fl x (rev (take (Suc i) vl)) (rev (drop (Suc 0) (take (Suc i) el)))
              (rev (drop (Suc 0) (take (Suc i) dl)))
              (k + af_delta_cost (el ! Suc i) (dl ! Suc i),
               af_min (if dl ! Suc i then prod.fst (af_rooms Fl (el ! Suc i)) else prod.snd (af_rooms Fl (el ! Suc i))) ra,
               af_min (if dl ! Suc i then prod.snd (af_rooms Fl (el ! Suc i)) else prod.fst (af_rooms Fl (el ! Suc i))) rf)"
    if "vl ! i \<noteq> x" for k ra rf
    using that
    apply (simp only: Dvl Del Ddl)
    apply (subst af_scan.simps(1))
    apply (simp add: case_prod_beta D[symmetric])
    done
  have G: "af_scan Fl x (rev (take (Suc (Suc i)) vl)) (rev (drop (Suc 0) (take (Suc (Suc i)) el)))
              (rev (drop (Suc 0) (take (Suc (Suc i)) dl))) (k, ra, rf) =
           (k + af_delta_cost (el ! Suc i) (dl ! Suc i),
            af_min (if dl ! Suc i then prod.fst (af_rooms Fl (el ! Suc i)) else prod.snd (af_rooms Fl (el ! Suc i))) ra,
            af_min (if dl ! Suc i then prod.snd (af_rooms Fl (el ! Suc i)) else prod.fst (af_rooms Fl (el ! Suc i))) rf)"
    if "vl ! i = x" for k ra rf
    using that unfolding Dvl Del Ddl by (subst af_scan.simps(1)) (simp add: case_prod_beta)
  have xcase: "vl ! i = x \<or> x \<in> set (take i vl)"
    using Suc.prems(2,6) by (auto simp: take_Suc_conv_app_nth Suc_lessD)
  have iel: "i < length el" using Suc.prems(3) by simp
  have idl: "i < length dl" using Suc.prems(4) by simp
  have ivl: "i < length vl" using Suc.prems(2) by simp
  have esub: "set (drop (Suc 0) (take (Suc i) el)) \<subseteq> \<E>" using Del Suc.prems(5) by auto
  show ?case
    apply (subst af_scan_imp.simps)
    apply (sep_auto simp: af_min_imp_eq ael F G case_prod_beta Suc.prems Suc_lessD
                    heap: Suc.IH[OF Suc.prems(1) ivl iel idl esub])
    subgoal using xcase by auto
    subgoal by sep_auto
    subgoal apply (sep_auto heap: Suc.IH[OF Suc.prems(1) ivl iel idl esub])
      subgoal using xcase by auto
      subgoal by sep_auto
      done
    done
qed

text \<open>Second cancellation pass: @{const af_push_imp} (tail-recursive, seeded @{term \<open>dep = 1\<close>},
      @{term \<open>best = 0\<close>}) refines @{const af_push}, mutating the flow in place and returning the drop
      count.\<close>
text \<open>General induction over the walked prefix: seeded with arbitrary @{term dep} / @{term best}, the
      imperative pass mirrors @{const af_push} on @{term \<open>rev (take (Suc i) vl)\<close>}, mutating the flow in
      place and returning @{term best} when nothing is saturated, else @{term \<open>dep\<close>} offset by the
      functional drop count.\<close>
lemma af_push_imp_gen:
  "\<lbrakk>flow_invar Fl; Suc 0 \<le> i; i < length vl; i < length el; i < length dl;
    set (drop (Suc 0) (take (Suc i) el)) \<subseteq> \<E>; x \<in> set (take i vl)\<rbrakk> \<Longrightarrow>
   <flow_assn Fl (iflow s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd>
     af_push_imp s \<gamma> x i flip dep best
   <\<lambda>r. flow_assn (prod.fst (af_push \<gamma> x (rev (take (Suc i) vl)) (rev (drop (Suc 0) (take (Suc i) el)))
                             (rev (drop (Suc 0) (take (Suc i) dl))) flip Fl)) (iflow s)
        * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd
        * \<up>(r = (if prod.snd (af_push \<gamma> x (rev (take (Suc i) vl)) (rev (drop (Suc 0) (take (Suc i) el)))
                            (rev (drop (Suc 0) (take (Suc i) dl))) flip Fl) = 0 then best
                 else dep + prod.snd (af_push \<gamma> x (rev (take (Suc i) vl)) (rev (drop (Suc 0) (take (Suc i) el)))
                            (rev (drop (Suc 0) (take (Suc i) dl))) flip Fl) - 1))>"
proof (induction i arbitrary: Fl dep best)
  case 0 then show ?case by simp
next
  case (Suc i)
  have D: "rev (take (Suc i) vl) = vl ! i # rev (take i vl)"
    using Suc.prems(3) by (simp add: take_Suc_conv_app_nth Suc_lessD)
  have Dvl: "rev (take (Suc (Suc i)) vl) = vl ! Suc i # vl ! i # rev (take i vl)"
    using Suc.prems(3) D by (simp add: take_Suc_conv_app_nth)
  have Del: "rev (drop (Suc 0) (take (Suc (Suc i)) el)) = el ! Suc i # rev (drop (Suc 0) (take (Suc i) el))"
    using take_Suc_conv_app_nth[OF Suc.prems(4)] Suc.prems(4) by (simp add: drop_append)
  have Ddl: "rev (drop (Suc 0) (take (Suc (Suc i)) dl)) = dl ! Suc i # rev (drop (Suc 0) (take (Suc i) dl))"
    using take_Suc_conv_app_nth[OF Suc.prems(5)] Suc.prems(5) by (simp add: drop_append)
  have ael: "el ! Suc i \<in> \<E>" using Del Suc.prems(6) by auto
  have xcase: "vl ! i = x \<or> x \<in> set (take i vl)"
    using Suc.prems(3,7) by (auto simp: take_Suc_conv_app_nth Suc_lessD)
  have flinv: "flow_invar (flow_upd Fl (el ! Suc i) (flow_lookup Fl (el ! Suc i) + (if dl ! Suc i \<noteq> flip then \<gamma> else - \<gamma>)))"
    using Suc.prems(1) ael by (rule flow_array.fixed_univ_map_upd_invar)
  have iel: "i < length el" using Suc.prems(4) by simp
  have idl: "i < length dl" using Suc.prems(5) by simp
  have ivl: "i < length vl" using Suc.prems(3) by simp
  have esub: "set (drop (Suc 0) (take (Suc i) el)) \<subseteq> \<E>" using Del Suc.prems(6) by auto
  have si: "Suc 0 \<le> i" if "vl ! i \<noteq> x" using xcase that by (cases i) auto
  have veq: "(if (if r0 \<noteq> 0 then Suc r0 else (if s0 then 1 else 0)) = 0 then best
              else dep + (if r0 \<noteq> 0 then Suc r0 else (if s0 then 1 else 0)) - 1)
             = (if r0 = 0 then (if s0 then dep else best) else Suc dep + r0 - 1)" for r0 s0
    by (cases "r0 = 0"; cases s0) auto
  have G: "af_push \<gamma> x (rev (take (Suc (Suc i)) vl)) (rev (drop (Suc 0) (take (Suc (Suc i)) el)))
             (rev (drop (Suc 0) (take (Suc (Suc i)) dl))) flip Fl
           = (flow_upd Fl (el ! Suc i) (flow_lookup Fl (el ! Suc i) + (if dl ! Suc i \<noteq> flip then \<gamma> else - \<gamma>)),
              if af_saturated (flow_lookup Fl (el ! Suc i) + (if dl ! Suc i \<noteq> flip then \<gamma> else - \<gamma>)) (el ! Suc i) then 1 else 0)"
    if "vl ! i = x"
    using that unfolding Dvl Del Ddl by (subst af_push.simps(1)) (simp add: af_push_arc_def Let_def case_prod_beta)
  have F: "af_push \<gamma> x (rev (take (Suc (Suc i)) vl)) (rev (drop (Suc 0) (take (Suc (Suc i)) el)))
             (rev (drop (Suc 0) (take (Suc (Suc i)) dl))) flip Fl
           = (case af_push \<gamma> x (rev (take (Suc i) vl)) (rev (drop (Suc 0) (take (Suc i) el)))
                (rev (drop (Suc 0) (take (Suc i) dl))) flip
                (flow_upd Fl (el ! Suc i) (flow_lookup Fl (el ! Suc i) + (if dl ! Suc i \<noteq> flip then \<gamma> else - \<gamma>)))
              of (fl2, r) \<Rightarrow>
                (fl2, if r \<noteq> 0 then Suc r
                      else (if af_saturated (flow_lookup Fl (el ! Suc i) + (if dl ! Suc i \<noteq> flip then \<gamma> else - \<gamma>)) (el ! Suc i) then 1 else 0)))"
    if "vl ! i \<noteq> x"
    using that unfolding Dvl Del Ddl by (subst af_push.simps(1)) (simp add: af_push_arc_def Let_def case_prod_beta D[symmetric])
  show ?case
  proof (cases "vl ! i = x")
    case True
    have rd_e: "<flow_assn Fl (iflow s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd>
                  Array.nth (iestack s) (Suc i)
                <\<lambda>a. flow_assn Fl (iflow s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd * \<up>(a = el ! Suc i)>"
      by (sep_auto simp: Suc.prems(4))
    have rd_d: "<flow_assn Fl (iflow s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd>
                  Array.nth (idstack s) (Suc i)
                <\<lambda>d. flow_assn Fl (iflow s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd * \<up>(d = dl ! Suc i)>"
      by (sep_auto simp: Suc.prems(5))
    have op_arc: "<flow_assn Fl (iflow s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd>
                    af_push_arc_imp \<gamma> (el ! Suc i) (dl ! Suc i \<noteq> flip) s
                  <\<lambda>f. flow_assn (flow_upd Fl (el ! Suc i) (flow_lookup Fl (el ! Suc i) + (if dl ! Suc i \<noteq> flip then \<gamma> else - \<gamma>))) (iflow s)
                       * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd
                       * \<up>(f = flow_lookup Fl (el ! Suc i) + (if dl ! Suc i \<noteq> flip then \<gamma> else - \<gamma>))>"
      by (sep_auto simp: Suc.prems(1) ael)
    have op_sat: "\<And>fl'. <flow_assn fl' (iflow s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd>
                    af_saturated_imp (flow_lookup Fl (el ! Suc i) + (if dl ! Suc i \<noteq> flip then \<gamma> else - \<gamma>)) (el ! Suc i)
                  <\<lambda>sat. flow_assn fl' (iflow s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd
                         * \<up>(sat = af_saturated (flow_lookup Fl (el ! Suc i) + (if dl ! Suc i \<noteq> flip then \<gamma> else - \<gamma>)) (el ! Suc i))>"
      by (sep_auto simp: ael)
    have rd_v: "\<And>fl'. <flow_assn fl' (iflow s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd>
                    Array.nth (ivstack s) i
                  <\<lambda>p. flow_assn fl' (iflow s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd * \<up>(p = vl ! i)>"
      by (sep_auto simp: ivl)
    have Gfst: "prod.fst (af_push \<gamma> x (rev (take (Suc (Suc i)) vl)) (rev (drop (Suc 0) (take (Suc (Suc i)) el)))
                       (rev (drop (Suc 0) (take (Suc (Suc i)) dl))) flip Fl)
                = flow_upd Fl (el ! Suc i) (flow_lookup Fl (el ! Suc i) + (if dl ! Suc i \<noteq> flip then \<gamma> else - \<gamma>))"
      by (simp add: G[OF True])
    have veqT: "(if prod.snd (af_push \<gamma> x (rev (take (Suc (Suc i)) vl)) (rev (drop (Suc 0) (take (Suc (Suc i)) el)))
                       (rev (drop (Suc 0) (take (Suc (Suc i)) dl))) flip Fl) = 0 then best
                 else dep + prod.snd (af_push \<gamma> x (rev (take (Suc (Suc i)) vl)) (rev (drop (Suc 0) (take (Suc (Suc i)) el)))
                       (rev (drop (Suc 0) (take (Suc (Suc i)) dl))) flip Fl) - 1)
                = (if af_saturated (flow_lookup Fl (el ! Suc i) + (if dl ! Suc i \<noteq> flip then \<gamma> else - \<gamma>)) (el ! Suc i) then dep else best)"
      by (simp add: G[OF True])
    show ?thesis
      apply (subst af_push_imp.simps)
      apply (simp only: Gfst veqT diff_Suc_1)
      apply (rule ht_bind[OF rd_e])
      apply (rule ht_extract_pre_pure(1))
      apply hypsubst
      apply (rule ht_bind[OF rd_d])
      apply (rule ht_extract_pre_pure(1))
      apply hypsubst
      apply (rule ht_bind[OF op_arc])
      apply (rule ht_extract_pre_pure(1))
      apply hypsubst
      apply (rule ht_bind[OF op_sat])
      apply (rule ht_extract_pre_pure(1))
      apply hypsubst
      apply (rule ht_bind[OF rd_v])
      apply (rule ht_extract_pre_pure(1))
      apply hypsubst
      apply (simp only: Let_def if_P[OF True])
      apply (sep_auto simp: mod_star_trueI)
      done
  next
    case False
    have xset: "x \<in> set (take i vl)" using xcase False by simp
    note IHi = Suc.IH[OF flinv si[OF False] ivl iel idl esub xset]
    have Ffst: "prod.fst (af_push \<gamma> x (rev (take (Suc (Suc i)) vl)) (rev (drop (Suc 0) (take (Suc (Suc i)) el)))
                  (rev (drop (Suc 0) (take (Suc (Suc i)) dl))) flip Fl)
                = prod.fst (af_push \<gamma> x (rev (take (Suc i) vl)) (rev (drop (Suc 0) (take (Suc i) el)))
                  (rev (drop (Suc 0) (take (Suc i) dl))) flip
                  (flow_upd Fl (el ! Suc i) (flow_lookup Fl (el ! Suc i) + (if dl ! Suc i \<noteq> flip then \<gamma> else - \<gamma>))))"
      unfolding F[OF False] by (simp add: case_prod_beta)
    have veqf: "(if prod.snd (af_push \<gamma> x (rev (take (Suc (Suc i)) vl)) (rev (drop (Suc 0) (take (Suc (Suc i)) el)))
                     (rev (drop (Suc 0) (take (Suc (Suc i)) dl))) flip Fl) = 0 then best
                 else dep + prod.snd (af_push \<gamma> x (rev (take (Suc (Suc i)) vl)) (rev (drop (Suc 0) (take (Suc (Suc i)) el)))
                     (rev (drop (Suc 0) (take (Suc (Suc i)) dl))) flip Fl) - 1)
                = (if prod.snd (af_push \<gamma> x (rev (take (Suc i) vl)) (rev (drop (Suc 0) (take (Suc i) el)))
                     (rev (drop (Suc 0) (take (Suc i) dl))) flip
                     (flow_upd Fl (el ! Suc i) (flow_lookup Fl (el ! Suc i) + (if dl ! Suc i \<noteq> flip then \<gamma> else - \<gamma>)))) = 0
                   then (if af_saturated (flow_lookup Fl (el ! Suc i) + (if dl ! Suc i \<noteq> flip then \<gamma> else - \<gamma>)) (el ! Suc i) then dep else best)
                   else Suc dep + prod.snd (af_push \<gamma> x (rev (take (Suc i) vl)) (rev (drop (Suc 0) (take (Suc i) el)))
                     (rev (drop (Suc 0) (take (Suc i) dl))) flip
                     (flow_upd Fl (el ! Suc i) (flow_lookup Fl (el ! Suc i) + (if dl ! Suc i \<noteq> flip then \<gamma> else - \<gamma>)))) - 1)"
      unfolding F[OF False] using veq by (simp add: case_prod_beta)
    have rd_e: "<flow_assn Fl (iflow s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd>
                  Array.nth (iestack s) (Suc i)
                <\<lambda>a. flow_assn Fl (iflow s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd * \<up>(a = el ! Suc i)>"
      by (sep_auto simp: Suc.prems(4))
    have rd_d: "<flow_assn Fl (iflow s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd>
                  Array.nth (idstack s) (Suc i)
                <\<lambda>d. flow_assn Fl (iflow s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd * \<up>(d = dl ! Suc i)>"
      by (sep_auto simp: Suc.prems(5))
    have op_arc: "<flow_assn Fl (iflow s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd>
                    af_push_arc_imp \<gamma> (el ! Suc i) (dl ! Suc i \<noteq> flip) s
                  <\<lambda>f. flow_assn (flow_upd Fl (el ! Suc i) (flow_lookup Fl (el ! Suc i) + (if dl ! Suc i \<noteq> flip then \<gamma> else - \<gamma>))) (iflow s)
                       * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd
                       * \<up>(f = flow_lookup Fl (el ! Suc i) + (if dl ! Suc i \<noteq> flip then \<gamma> else - \<gamma>))>"
      by (sep_auto simp: Suc.prems(1) ael)
    have op_sat: "\<And>fl'. <flow_assn fl' (iflow s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd>
                    af_saturated_imp (flow_lookup Fl (el ! Suc i) + (if dl ! Suc i \<noteq> flip then \<gamma> else - \<gamma>)) (el ! Suc i)
                  <\<lambda>sat. flow_assn fl' (iflow s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd
                         * \<up>(sat = af_saturated (flow_lookup Fl (el ! Suc i) + (if dl ! Suc i \<noteq> flip then \<gamma> else - \<gamma>)) (el ! Suc i))>"
      by (sep_auto simp: ael)
    have rd_v: "\<And>fl'. <flow_assn fl' (iflow s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd>
                    Array.nth (ivstack s) i
                  <\<lambda>p. flow_assn fl' (iflow s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd * \<up>(p = vl ! i)>"
      by (sep_auto simp: ivl)
    show ?thesis
      apply (subst af_push_imp.simps)
      apply (simp only: Ffst veqf diff_Suc_1)
      apply (rule ht_bind[OF rd_e])
      apply (rule ht_extract_pre_pure(1))
      apply hypsubst
      apply (rule ht_bind[OF rd_d])
      apply (rule ht_extract_pre_pure(1))
      apply hypsubst
      apply (rule ht_bind[OF op_arc])
      apply (rule ht_extract_pre_pure(1))
      apply hypsubst
      apply (rule ht_bind[OF op_sat])
      apply (rule ht_extract_pre_pure(1))
      apply hypsubst
      apply (rule ht_bind[OF rd_v])
      apply (rule ht_extract_pre_pure(1))
      apply hypsubst
      apply (simp only: Let_def if_not_P[OF False])
      apply (rule ht_cons_post_prec[OF IHi])
      apply sep_auto
      done
  qed
qed

lemma af_push_imp_rule:
  "\<lbrakk>flow_invar Fl; Suc 0 \<le> i; i < length vl; i < length el; i < length dl;
    set (drop (Suc 0) (take (Suc i) el)) \<subseteq> \<E>; x \<in> set (take i vl)\<rbrakk> \<Longrightarrow>
   <flow_assn Fl (iflow s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd>
     af_push_imp s \<gamma> x i flip (Suc 0) 0
   <\<lambda>r. case af_push \<gamma> x (rev (take (Suc i) vl)) (rev (drop (Suc 0) (take (Suc i) el)))
                          (rev (drop (Suc 0) (take (Suc i) dl))) flip Fl of (fl', m') \<Rightarrow>
          flow_assn fl' (iflow s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd * \<up>(r = m')>"
  apply (rule ht_cons_post_prec[OF af_push_imp_gen])
  apply assumption+
  apply (sep_auto simp: case_prod_beta)
  done

text \<open>Whole tagged-cycle cancellation, mutating the flow and returning drop count + unbounded flag.\<close>
lemma af_cancel_seg_imp_rule:
  assumes "flow_invar Fl" "a \<in> \<E>" "Suc 0 \<le> sp" "sp \<le> length vl" "sp \<le> length el" "sp \<le> length dl"
          "set (drop (Suc 0) (take sp el)) \<subseteq> \<E>" "x \<in> set (take (sp - Suc 0) vl)"
  shows
   "<flow_assn Fl (iflow s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd>
     af_cancel_seg_imp s up dn x a dir sp
   <\<lambda>r. case af_cancel_seg up dn x (rev (take sp vl)) (rev (drop (Suc 0) (take sp el)))
                          (rev (drop (Suc 0) (take sp dl))) a dir Fl of (fl'', m', ubd) \<Rightarrow>
          flow_assn fl'' (iflow s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd *
          \<up>(r = (m', ubd))>"
proof -
  have ssp: "Suc (sp - Suc 0) = sp" using assms(3) by simp
  have ivl: "sp - Suc 0 < length vl" using assms(3,4) by simp
  have iel: "sp - Suc 0 < length el" using assms(3,5) by simp
  have idl: "sp - Suc 0 < length dl" using assms(3,6) by simp
  have esub: "set (drop (Suc 0) (take (Suc (sp - Suc 0)) el)) \<subseteq> \<E>" using assms(7) ssp by simp
  have i1: "Suc 0 \<le> sp - Suc 0" using assms(8) by (cases "sp - Suc 0") auto
  have eses: "set (rev (drop (Suc 0) (take sp el))) \<subseteq> \<E>" using assms(7) by simp
  have pinv: "flow_invar (prod.fst (af_push g x (rev (take sp vl)) (rev (drop (Suc 0) (take sp el)))
                (rev (drop (Suc 0) (take sp dl))) fp Fl))" for g fp
    using af_push_flow_invar[OF eses] assms(1) by (metis prod.collapse)
  note SR = af_scan_imp_rule[OF assms(1) ivl iel idl esub assms(8), unfolded ssp]
  note PR = af_push_imp_rule[OF assms(1) i1 ivl iel idl esub assms(8), unfolded ssp]
  have dcr: "<flow_assn Fl (iflow s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd>
               af_delta_cost_imp a dir
             <\<lambda>dc0. flow_assn Fl (iflow s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd
                    * \<up>(dc0 = af_delta_cost a dir)>"
    by (sep_auto simp: assms(2))
  have branch: "<flow_assn Fl (iflow s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd>
                  do { m' \<leftarrow> af_push_imp s g x (sp - Suc 0) fp (Suc 0) 0;
                       _ \<leftarrow> af_push_arc_imp g a (dir \<noteq> fp) s; return (m', False) }
                <\<lambda>r. case af_push g x (rev (take sp vl)) (rev (drop (Suc 0) (take sp el)))
                              (rev (drop (Suc 0) (take sp dl))) fp Fl of (fl', m') \<Rightarrow>
                       case af_push_arc g a (dir \<noteq> fp) fl' of (fl'', uu_) \<Rightarrow>
                         flow_assn fl'' (iflow s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd
                         * \<up>(r = (m', False))>" for g fp
  proof -
    obtain fl' m' where pe: "af_push g x (rev (take sp vl)) (rev (drop (Suc 0) (take sp el)))
                               (rev (drop (Suc 0) (take sp dl))) fp Fl = (fl', m')"
      by (cases "af_push g x (rev (take sp vl)) (rev (drop (Suc 0) (take sp el)))
                   (rev (drop (Suc 0) (take sp dl))) fp Fl") auto
    have fi': "flow_invar fl'" using pinv[of g fp] by (simp add: pe)
    note PRe = PR[of s g fp, unfolded pe prod.case]
    show ?thesis
      unfolding pe prod.case
      apply (rule ht_bind[OF PRe])
      apply (rule ht_extract_pre_pure(1))
      apply hypsubst
      apply (sep_auto simp: af_push_arc_def Let_def fi' assms(2))
      done
  qed
  obtain k ra rf where sc: "af_scan Fl x (rev (take sp vl)) (rev (drop (Suc 0) (take sp el)))
                              (rev (drop (Suc 0) (take sp dl)))
                              (af_delta_cost a dir, (if dir then up else dn), (if dir then dn else up))
                            = (k, ra, rf)"
    by (cases "af_scan Fl x (rev (take sp vl)) (rev (drop (Suc 0) (take sp el)))
                 (rev (drop (Suc 0) (take sp dl)))
                 (af_delta_cost a dir, (if dir then up else dn), (if dir then dn else up))") auto
  show ?thesis
  proof (cases "(if 0 < k then rf else ra) \<noteq> - 1")
    case True
    show ?thesis
      unfolding af_cancel_seg_imp_def af_cancel_seg_def Let_def One_nat_def
      apply (rule ht_bind[OF dcr]) apply (rule ht_extract_pre_pure(1)) apply hypsubst
      apply (rule ht_bind[OF SR]) apply (rule ht_extract_pre_pure(1)) apply hypsubst
      apply (simp only: sc prod.case if_P[OF True])
      apply (rule ht_cons_post_prec[OF branch])
      apply (sep_auto split: prod.splits)
      done
  next
    case False
    show ?thesis
    proof (cases "k = 0 \<and> rf \<noteq> - 1")
      case True
      show ?thesis
        unfolding af_cancel_seg_imp_def af_cancel_seg_def Let_def One_nat_def
        apply (rule ht_bind[OF dcr]) apply (rule ht_extract_pre_pure(1)) apply hypsubst
        apply (rule ht_bind[OF SR]) apply (rule ht_extract_pre_pure(1)) apply hypsubst
        apply (simp only: sc prod.case if_not_P[OF False] if_P[OF True])
        apply (rule ht_cons_post_prec[OF branch])
        apply (sep_auto split: prod.splits)
        done
    next
      case FF: False
      show ?thesis
        unfolding af_cancel_seg_imp_def af_cancel_seg_def Let_def One_nat_def
        apply (rule ht_bind[OF dcr]) apply (rule ht_extract_pre_pure(1)) apply hypsubst
        apply (rule ht_bind[OF SR]) apply (rule ht_extract_pre_pure(1)) apply hypsubst
        apply (simp only: sc prod.case if_not_P[OF False] if_not_P[OF FF])
        apply sep_auto
        done
    qed
  qed
qed

text \<open>Reset one vertex's two edge iterators in place.\<close>
lemma af_reset_imp_rule:
  "\<lbrakk>out_invar OG; in_invar IG; v \<in> \<V>\<rbrakk> \<Longrightarrow>
   <out_assn OG (iout s) * in_assn IG (iin s)> af_reset_imp s v
   <\<lambda>_. out_assn (out_reset OG v) (iout s) * in_assn (in_reset IG v) (iin s)>"
  unfolding af_reset_imp_def by sep_auto

text \<open>Generalised fused truncation clean-up over the top @{term n} stack vertices, the walked list
      given directly as @{term \<open>rev (take sp vl)\<close>} so the induction on @{term n} can rethread the state.\<close>
lemma af_reset_unsee_seg_imp_gen:
  "\<lbrakk>st_invar (af_state st); out_invar (af_out_arr st); in_invar (af_in_arr st);
    n \<le> sp; sp \<le> length vl; set (take sp vl) \<subseteq> \<V>\<rbrakk> \<Longrightarrow>
   <state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) *
    in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl>
     af_reset_unsee_seg_imp s n (sp - Suc 0)
   <\<lambda>_. state_assn (af_state (af_reset_unsee_seg n (rev (take sp vl)) st)) (istate s) *
        out_assn (af_out_arr (af_reset_unsee_seg n (rev (take sp vl)) st)) (iout s) *
        in_assn (af_in_arr (af_reset_unsee_seg n (rev (take sp vl)) st)) (iin s) * ivstack s \<mapsto>\<^sub>a vl>"
proof (induction n arbitrary: st sp)
  case 0 then show ?case by (subst af_reset_unsee_seg_imp.simps) sep_auto
next
  case (Suc n)
  have sp1: "Suc 0 \<le> sp" using Suc.prems(4) by simp
  have ssp: "Suc (sp - Suc 0) = sp" using sp1 by simp
  have spvl: "sp - Suc 0 < length vl" using sp1 Suc.prems(5) by simp
  have t: "take sp vl = take (sp - Suc 0) vl @ [vl ! (sp - Suc 0)]"
    using take_Suc_conv_app_nth[OF spvl] by (simp add: ssp)
  have hd: "rev (take sp vl) = vl ! (sp - Suc 0) # rev (take (sp - Suc 0) vl)" using t by simp
  have vmem: "vl ! (sp - Suc 0) \<in> set (take sp vl)" using t by simp
  have vV: "vl ! (sp - Suc 0) \<in> \<V>" using vmem Suc.prems(6) by blast
  have nle: "n \<le> sp - Suc 0" using Suc.prems(4) by simp
  have svl: "sp - Suc 0 \<le> length vl" using Suc.prems(5) by simp
  have ssub: "set (take (sp - Suc 0) vl) \<subseteq> \<V>" using Suc.prems(6) t by auto
  have feq: "af_reset_unsee_seg (Suc n) (rev (take sp vl)) st =
             af_reset_unsee_seg n (rev (take (sp - Suc 0) vl))
               (af_reset (vl ! (sp - Suc 0)) (st\<lparr>af_state := st_upd (af_state st) (vl ! (sp - Suc 0)) Unseen\<rparr>))"
    by (subst hd) simp
  have sti: "st_invar (af_state (af_reset (vl ! (sp - Suc 0)) (st\<lparr>af_state := st_upd (af_state st) (vl ! (sp - Suc 0)) Unseen\<rparr>)))"
    using st_upd_invar[OF Suc.prems(1) vV] by (simp add: af_reset_def)
  have oti: "out_invar (af_out_arr (af_reset (vl ! (sp - Suc 0)) (st\<lparr>af_state := st_upd (af_state st) (vl ! (sp - Suc 0)) Unseen\<rparr>)))"
    using out_reset_invar[OF Suc.prems(2) vV] by (simp add: af_reset_def)
  have iti: "in_invar (af_in_arr (af_reset (vl ! (sp - Suc 0)) (st\<lparr>af_state := st_upd (af_state st) (vl ! (sp - Suc 0)) Unseen\<rparr>)))"
    using in_reset_invar[OF Suc.prems(3) vV] by (simp add: af_reset_def)
  note IH = Suc.IH[OF sti oti iti nle svl ssub]
  have rd: "<state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl>
              Array.nth (ivstack s) (sp - Suc 0)
            <\<lambda>r. state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl
                 * \<up>(r = vl ! (sp - Suc 0))>"
    by (sep_auto simp: spvl)
  have su: "<state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl>
              st_upd_imp (istate s) (vl ! (sp - Suc 0)) Unseen
            <\<lambda>_. state_assn (st_upd (af_state st) (vl ! (sp - Suc 0)) Unseen) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl>"
    by (sep_auto simp: Suc.prems(1) vV)
  have ar: "<state_assn (st_upd (af_state st) (vl ! (sp - Suc 0)) Unseen) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl>
              af_reset_imp s (vl ! (sp - Suc 0))
            <\<lambda>_. state_assn (af_state (af_reset (vl ! (sp - Suc 0)) (st\<lparr>af_state := st_upd (af_state st) (vl ! (sp - Suc 0)) Unseen\<rparr>))) (istate s)
                 * out_assn (af_out_arr (af_reset (vl ! (sp - Suc 0)) (st\<lparr>af_state := st_upd (af_state st) (vl ! (sp - Suc 0)) Unseen\<rparr>))) (iout s)
                 * in_assn (af_in_arr (af_reset (vl ! (sp - Suc 0)) (st\<lparr>af_state := st_upd (af_state st) (vl ! (sp - Suc 0)) Unseen\<rparr>))) (iin s) * ivstack s \<mapsto>\<^sub>a vl>"
    by (sep_auto heap: af_reset_imp_rule simp: Suc.prems(2) Suc.prems(3) vV af_reset_def)
  have prog: "af_reset_unsee_seg_imp s (Suc n) (sp - Suc 0) =
              do { v \<leftarrow> Array.nth (ivstack s) (sp - Suc 0); _ \<leftarrow> st_upd_imp (istate s) v Unseen;
                   _ \<leftarrow> af_reset_imp s v; af_reset_unsee_seg_imp s n (sp - Suc 0 - Suc 0) }"
    by (subst af_reset_unsee_seg_imp.simps) simp
  show ?case
    unfolding prog
    apply (simp only: feq)
    apply (rule ht_bind[OF rd]) apply (rule ht_extract_pre_pure(1)) apply hypsubst
    apply (rule ht_bind[OF su])
    apply (rule ht_bind[OF ar])
    apply (rule IH)
    done
qed

text \<open>Fused truncation clean-up over the top @{term n} stack vertices.\<close>
lemma af_reset_unsee_seg_imp_rule:
  "\<lbrakk>st_invar (af_state st); out_invar (af_out_arr st); in_invar (af_in_arr st);
    n \<le> sp; sp \<le> length vl; set (take sp vl) \<subseteq> \<V>; af_vstack st = rev (take sp vl)\<rbrakk> \<Longrightarrow>
   <state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) *
    in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl>
     af_reset_unsee_seg_imp s n (sp - Suc 0)
   <\<lambda>_. state_assn (af_state (af_reset_unsee_seg n (af_vstack st) st)) (istate s) *
        out_assn (af_out_arr (af_reset_unsee_seg n (af_vstack st) st)) (iout s) *
        in_assn (af_in_arr (af_reset_unsee_seg n (af_vstack st) st)) (iin s) * ivstack s \<mapsto>\<^sub>a vl>"
  by (simp add: af_reset_unsee_seg_imp_gen)

text \<open>Self-loop normalisation, mutating the flow and returning the unbounded flag.\<close>
lemma af_selfloop_handle_imp_rule:
  "\<lbrakk>flow_invar (af_flow st); a \<in> \<E>; \<not> af_unbounded st\<rbrakk> \<Longrightarrow>
   <flow_assn (af_flow st) (iflow s) * rd> af_selfloop_handle_imp s a
   <\<lambda>r. flow_assn (af_flow (af_selfloop_handle st a)) (iflow s) * rd *
        \<up>(r = af_unbounded (af_selfloop_handle st a))>"
  unfolding af_selfloop_handle_imp_def af_selfloop_handle_def Let_def
  by (sep_auto split: if_splits)

text \<open>Truncation encodings: dropping @{term cm} off the reversed stack / trail-edge lists shrinks the
      @{term sp} bound by @{term cm}. Used to re-establish @{const dfs_rel} after the stack is cut.\<close>
lemma tr_v: "sp \<le> length vl \<Longrightarrow> drop cm (rev (take sp vl)) = rev (take (sp - cm) vl)"
  by (simp add: drop_rev take_take min_def)

lemma tr_e: "cm \<le> sp - Suc 0 \<Longrightarrow> sp \<le> length el \<Longrightarrow> drop cm (rev (drop (Suc 0) (take sp el))) = rev (drop (Suc 0) (take (sp - cm) el))"
  by (simp add: drop_take tr_v)

text \<open>From the @{const OnStack} guard: an OnStack, in-{\isasymV}, non-top vertex sits strictly below the stack
      top, i.e.\ in the pre-top prefix --- exactly @{const af_cancel_seg}'s @{term \<open>x \<in> set (take (sp-1) vl)\<close>}.\<close>
lemma xmem_below_top:
  assumes "AF_invar_2 st" "st_lookup (af_state st) x = OnStack" "x \<in> \<V>" "x \<noteq> hd (af_vstack st)"
          "Suc 0 \<le> sp" "af_vstack st = rev (take sp vl)" "sp \<le> length vl"
  shows "x \<in> set (take (sp - Suc 0) vl)"
proof -
  have onmem: "x \<in> set (af_vstack st)" using assms(1,2,3) by (auto elim!: AF_invar_2E)
  have spvl: "sp - Suc 0 < length vl" using assms(5,7) by simp
  have hdc: "af_vstack st = vl ! (sp - Suc 0) # rev (take (sp - Suc 0) vl)"
    using assms(6) take_Suc_conv_app_nth[OF spvl] assms(5) by simp
  show ?thesis using onmem assms(4) hdc by simp
qed

text \<open>OnStack cycle-closing case of @{const af_handle}: cancel the tagged cycle (mutating the flow),
      then truncate the stacks to the bottleneck and unmark the popped segment. Bundled premise
      @{term \<open>AF_inv st\<close>} supplies the distinctness / trail invariants; the extra pure postcondition
      exposes the new pointer @{term sp'} and the unbounded flag for @{const af_handle}'s caller.\<close>
lemma af_close_cycle_imp_rule:
  assumes I: "AF_inv st" "a \<in> \<E>" "\<not> af_unbounded st" "st_lookup (af_state st) x = OnStack"
             "x \<in> \<V>" "x \<noteq> hd (af_vstack st)" "Suc 0 \<le> sp"
  shows
   "<dfs_rel st s sp> af_close_cycle_imp s up dn x a dir sp
   <\<lambda>r. case r of (sp', ubd) \<Rightarrow>
          dfs_rel (case af_cancel_seg up dn x (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st)
                    of (fl, m', ub) \<Rightarrow>
                      if ub then st\<lparr>af_unbounded := True\<rparr>
                      else af_reset_unsee_seg m' (af_vstack st)
                             (st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st),
                                  af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>))
                  s sp' *
          \<up>(sp' = length (af_vstack (case af_cancel_seg up dn x (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st)
                    of (fl, m', ub) \<Rightarrow>
                      if ub then st\<lparr>af_unbounded := True\<rparr>
                      else af_reset_unsee_seg m' (af_vstack st)
                             (st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st),
                                  af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>))) \<and>
             ubd = af_unbounded (case af_cancel_seg up dn x (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st)
                    of (fl, m', ub) \<Rightarrow>
                      if ub then st\<lparr>af_unbounded := True\<rparr>
                      else af_reset_unsee_seg m' (af_vstack st)
                             (st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st),
                                  af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>)))>"
proof -
  have inv1: "AF_invar_1 st" and inv2: "AF_invar_2 st" and invE: "AF_invar_estE st" and invV: "AF_invar_V st" using I(1) unfolding AF_inv_def by auto
  have fi: "flow_invar (af_flow st)" and sti: "st_invar (af_state st)" and oti: "out_invar (af_out_arr st)" and iti: "in_invar (af_in_arr st)" using inv1 by (auto elim: AF_invar_1_props)
  have esub: "set (af_estack st) \<subseteq> \<E>" using invE by (simp add: AF_invar_estE_def)
  have vsub: "set (af_vstack st) \<subseteq> \<V>" using invV by (simp add: AF_invar_V_def)
  obtain fl'' cm ub where cs: "af_cancel_seg up dn x (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) = (fl'', cm, ub)" by (cases "af_cancel_seg up dn x (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st)") auto
  have mles: "cm \<le> length (af_estack st)" using af_cancel_seg_drop_bound[OF cs] .
  have ubflow: "ub \<Longrightarrow> fl'' = af_flow st" using cs by (auto simp: af_cancel_seg_def Let_def split: prod.splits if_splits)
  have body: "<flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd> af_close_cycle_imp s up dn x a dir sp <\<lambda>r. case r of (sp', ubd) \<Rightarrow> dfs_rel (case af_cancel_seg up dn x (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) of (fl, m', ub) \<Rightarrow> if ub then st\<lparr>af_unbounded := True\<rparr> else af_reset_unsee_seg m' (af_vstack st) (st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st), af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>)) s sp' * \<up>(sp' = length (af_vstack (case af_cancel_seg up dn x (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) of (fl, m', ub) \<Rightarrow> if ub then st\<lparr>af_unbounded := True\<rparr> else af_reset_unsee_seg m' (af_vstack st) (st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st), af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>))) \<and> ubd = af_unbounded (case af_cancel_seg up dn x (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) of (fl, m', ub) \<Rightarrow> if ub then st\<lparr>af_unbounded := True\<rparr> else af_reset_unsee_seg m' (af_vstack st) (st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st), af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>)))>"
    if T: "card \<V> \<le> length vl" "card \<V> \<le> length el" "card \<V> \<le> length dl" "sp \<le> card \<V>" "af_vstack st = rev (take sp vl)" "af_estack st = rev (drop (Suc 0) (take sp el))" "af_dstack st = rev (drop (Suc 0) (take sp dl))" "length vl = Lvst" "length el = Lest" "length dl = Ldst" for vl el dl
  proof -
    have svl: "sp \<le> length vl" using T(1,4) by simp
    have sel: "sp \<le> length el" using T(2,4) by simp
    have sdl: "sp \<le> length dl" using T(3,4) by simp
    \<comment> \<open>the stack-length equalities, pushed through the facts the folds below need: as simp rules the
        equalities rewrite \<open>length vl\<close> away, so the consequences are recorded up front\<close>
    have cLv: "card \<V> \<le> Lvst" using T(1) T(8) by simp
    have cLe: "card \<V> \<le> Lest" using T(2) T(9) by simp
    have cLd: "card \<V> \<le> Ldst" using T(3) T(10) by simp
    have spLv: "sp \<le> Lvst" using svl T(8) by simp
    have lvst: "length (af_vstack st) = sp" using T(5) svl by simp
    have xmem: "x \<in> set (take (sp - Suc 0) vl)" using xmem_below_top[OF inv2 I(4) I(5) I(6) I(7) T(5) svl] .
    have esub': "set (drop (Suc 0) (take sp el)) \<subseteq> \<E>" using esub T(6) by simp
    have cmle: "cm \<le> sp - Suc 0" using mles by (simp add: T(6) sel)
    have cmsp: "cm \<le> sp" using cmle by simp
    have cr: "<flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd> af_cancel_seg_imp s up dn x a dir sp <\<lambda>r. flow_assn fl'' (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd * \<up>(r = (cm, ub))>"
      by (sep_auto heap: af_cancel_seg_imp_rule[OF fi I(2) I(7) svl sel sdl esub' xmem] simp: T(5)[symmetric] T(6)[symmetric] T(7)[symmetric] cs)
    have vsub': "set (take sp vl) \<subseteq> \<V>" using vsub T(5) by simp
    have scc: "sp - cm \<le> card \<V>" using T(4) by (meson diff_le_self le_trans)
    have scl: "sp - cm \<le> length vl" using svl by (meson diff_le_self le_trans)
    have stiI: "st_invar (af_state (st\<lparr>af_flow := fl'', af_vstack := drop cm (af_vstack st), af_estack := drop cm (af_estack st), af_dstack := drop cm (af_dstack st)\<rparr>))" using sti by simp
    have otiI: "out_invar (af_out_arr (st\<lparr>af_flow := fl'', af_vstack := drop cm (af_vstack st), af_estack := drop cm (af_estack st), af_dstack := drop cm (af_dstack st)\<rparr>))" using oti by simp
    have itiI: "in_invar (af_in_arr (st\<lparr>af_flow := fl'', af_vstack := drop cm (af_vstack st), af_estack := drop cm (af_estack st), af_dstack := drop cm (af_dstack st)\<rparr>))" using iti by simp
    note gg = af_reset_unsee_seg_imp_gen[OF stiI otiI itiI cmsp svl vsub', simplified]
    have rst: "<flow_assn fl'' (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd> af_reset_unsee_seg_imp s cm (sp - 1) <\<lambda>_. flow_assn fl'' (iflow s) * state_assn (af_state (af_reset_unsee_seg cm (rev (take sp vl)) (st\<lparr>af_flow := fl'', af_vstack := drop cm (af_vstack st), af_estack := drop cm (af_estack st), af_dstack := drop cm (af_dstack st)\<rparr>))) (istate s) * out_assn (af_out_arr (af_reset_unsee_seg cm (rev (take sp vl)) (st\<lparr>af_flow := fl'', af_vstack := drop cm (af_vstack st), af_estack := drop cm (af_estack st), af_dstack := drop cm (af_dstack st)\<rparr>))) (iout s) * in_assn (af_in_arr (af_reset_unsee_seg cm (rev (take sp vl)) (st\<lparr>af_flow := fl'', af_vstack := drop cm (af_vstack st), af_estack := drop cm (af_estack st), af_dstack := drop cm (af_dstack st)\<rparr>))) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd>"
      by (sep_auto heap: gg simp: One_nat_def)
    have entF_m: "flow_assn fl'' (iflow s) * state_assn (af_state (af_reset_unsee_seg cm (af_vstack st) (st\<lparr>af_flow := fl'', af_vstack := drop cm (af_vstack st), af_estack := drop cm (af_estack st), af_dstack := drop cm (af_dstack st)\<rparr>))) (istate s) * out_assn (af_out_arr (af_reset_unsee_seg cm (af_vstack st) (st\<lparr>af_flow := fl'', af_vstack := drop cm (af_vstack st), af_estack := drop cm (af_estack st), af_dstack := drop cm (af_dstack st)\<rparr>))) (iout s) * in_assn (af_in_arr (af_reset_unsee_seg cm (af_vstack st) (st\<lparr>af_flow := fl'', af_vstack := drop cm (af_vstack st), af_estack := drop cm (af_estack st), af_dstack := drop cm (af_dstack st)\<rparr>))) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd \<Longrightarrow>\<^sub>A dfs_rel (af_reset_unsee_seg cm (af_vstack st) (st\<lparr>af_flow := fl'', af_vstack := drop cm (af_vstack st), af_estack := drop cm (af_estack st), af_dstack := drop cm (af_dstack st)\<rparr>)) s (sp - cm) * true * \<up>(sp - cm = length (af_vstack st) - cm \<and> \<not> af_unbounded st)"
      unfolding dfs_rel_def
      apply (simp only: ex_assn_move_out)
      apply (rule ent_ex_postI[where x=vl])
      apply (rule ent_ex_postI[where x=el])
      apply (rule ent_ex_postI[where x=dl])
      apply (sep_auto simp: T(1) T(2) T(3) T(5) T(6) T(7) T(8) T(9) T(10) cLv cLe cLd tr_v[OF svl] tr_e[OF cmle sel] tr_e[OF cmle sdl] lvst I(3) scc)
      by (simp add: min.absorb2 spLv)
    have entT_m: "fl'' = af_flow st \<Longrightarrow> flow_assn fl'' (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd \<Longrightarrow>\<^sub>A dfs_rel (st\<lparr>af_unbounded := True\<rparr>) s sp * true * \<up>(sp = length (af_vstack st))"
      unfolding dfs_rel_def
      apply (simp only: ex_assn_move_out)
      apply (rule ent_ex_postI[where x=vl])
      apply (rule ent_ex_postI[where x=el])
      apply (rule ent_ex_postI[where x=dl])
      apply (sep_auto simp: T(1) T(2) T(3) T(4) T(5) T(6) T(7) T(8) T(9) T(10) cLv cLe cLd lvst)
      by (simp add: min.absorb2 spLv)
    have step2: "<flow_assn fl'' (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd> (if ub then return (sp, True) else do { _ \<leftarrow> af_reset_unsee_seg_imp s cm (sp - 1); return (sp - cm, False) }) <\<lambda>r. case r of (sp', ubd) \<Rightarrow> dfs_rel (if ub then st\<lparr>af_unbounded := True\<rparr> else af_reset_unsee_seg cm (af_vstack st) (st\<lparr>af_flow := fl'', af_vstack := drop cm (af_vstack st), af_estack := drop cm (af_estack st), af_dstack := drop cm (af_dstack st)\<rparr>)) s sp' * \<up>(sp' = length (af_vstack (if ub then st\<lparr>af_unbounded := True\<rparr> else af_reset_unsee_seg cm (af_vstack st) (st\<lparr>af_flow := fl'', af_vstack := drop cm (af_vstack st), af_estack := drop cm (af_estack st), af_dstack := drop cm (af_dstack st)\<rparr>))) \<and> ubd = af_unbounded (if ub then st\<lparr>af_unbounded := True\<rparr> else af_reset_unsee_seg cm (af_vstack st) (st\<lparr>af_flow := fl'', af_vstack := drop cm (af_vstack st), af_estack := drop cm (af_estack st), af_dstack := drop cm (af_dstack st)\<rparr>)))>"
    proof (cases ub)
      case True
      show ?thesis
        apply (simp only: True if_True)
        apply (sep_auto)
        apply (rule entailsD[OF entT_m[OF ubflow[OF True]]])
        apply assumption
        done
    next
      case False
      show ?thesis
        apply (simp only: False if_False)
        apply (rule ht_bind[OF rst[folded T(5)]])
        apply (sep_auto)
        apply (rule entailsD[OF entF_m])
        apply assumption
        done
    qed
    show ?thesis
      unfolding af_close_cycle_imp_def
      apply (rule ht_bind[OF cr])
      apply (rule ht_extract_pre_pure(1))
      apply hypsubst
      apply (simp only: prod.case cs)
      apply (rule step2)
      done
  qed
  show ?thesis
    apply (subst dfs_rel_def)
    apply (simp only: ex_assn_move_out)
    apply (rule ht_exEI)+
    apply (simp only: mult.assoc[symmetric])
    apply (rule ht_extract_pre_pure(1))
    apply (erule conjE)+
    apply (rule ht_cons_pre[OF _ body]; (assumption | sep_auto))
    done
qed

text \<open>Two list-encoding rewrites: writing @{term x} at index @{term sp} then taking @{term \<open>Suc sp\<close>}
      appends @{term x} to the reversed stack (the estack/dstack variant needs @{term \<open>Suc 0 \<le> sp\<close>}).\<close>
lemma penc_v: "sp < length vl \<Longrightarrow> rev ((take (Suc sp) vl)[sp := x]) = x # rev (take sp vl)"
  by (simp add: take_Suc_conv_app_nth list_update_append)

lemma penc_e: "Suc 0 \<le> sp \<Longrightarrow> sp < length el \<Longrightarrow> rev (drop (Suc 0) ((take (Suc sp) el)[sp := a])) = a # rev (drop (Suc 0) (take sp el))"
  by (simp add: take_Suc_conv_app_nth list_update_append drop_append)

text \<open>Fresh-vertex case of @{const af_handle}: push the new vertex. Needs @{term \<open>Suc 0 \<le> sp\<close>} (the DFS
      stack is non-empty --- the root is always on it) so the estack / dstack encoding shifts correctly;
      that premise is discharged at the call site from the @{const AF_DFS} loop condition.\<close>
lemma af_push_vertex_imp_rule:
  assumes A: "st_invar (af_state st)" "x \<in> \<V>" "sp < card \<V>" "Suc 0 \<le> sp"
  shows "<dfs_rel st s sp> af_push_vertex_imp s x a dir sp
   <\<lambda>r. case r of (sp', ubd) \<Rightarrow>
          dfs_rel (st\<lparr>af_vstack := x # af_vstack st, af_state := st_upd (af_state st) x OnStack,
                      af_estack := a # af_estack st, af_dstack := dir # af_dstack st\<rparr>) s sp' *
          \<up>(sp' = Suc sp \<and> \<not> ubd)>"
proof -
  have ent: "flow_assn (af_flow st) (iflow s) * state_assn (st_upd (af_state st) x OnStack) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl[sp := x] * iestack s \<mapsto>\<^sub>a el[sp := a] * idstack s \<mapsto>\<^sub>a dl[sp := dir] * rd \<Longrightarrow>\<^sub>A dfs_rel (st\<lparr>af_vstack := x # af_vstack st, af_state := st_upd (af_state st) x OnStack, af_estack := a # af_estack st, af_dstack := dir # af_dstack st\<rparr>) s (Suc sp)"
    if T: "card \<V> \<le> length vl" "card \<V> \<le> length el" "card \<V> \<le> length dl" "sp \<le> card \<V>" "af_vstack st = rev (take sp vl)" "af_estack st = rev (drop (Suc 0) (take sp el))" "af_dstack st = rev (drop (Suc 0) (take sp dl))" "length vl = Lvst" "length el = Lest" "length dl = Ldst" for vl el dl
  proof -
    have svl: "sp < length vl" using A(3) T(1) by (rule less_le_trans)
    have sel: "sp < length el" using A(3) T(2) by (rule less_le_trans)
    have sdl: "sp < length dl" using A(3) T(3) by (rule less_le_trans)
    have cLv: "card \<V> \<le> Lvst" using T(1) T(8) by simp
    have cLe: "card \<V> \<le> Lest" using T(2) T(9) by simp
    have cLd: "card \<V> \<le> Ldst" using T(3) T(10) by simp
    show ?thesis
      unfolding dfs_rel_def
      apply (simp only: ex_assn_move_out)
      apply (rule ent_ex_postI[where x="vl[sp := x]"])
      apply (rule ent_ex_postI[where x="el[sp := a]"])
      apply (rule ent_ex_postI[where x="dl[sp := dir]"])
      by (sep_auto simp: penc_v[OF svl] penc_e[OF A(4) sel] penc_e[OF A(4) sdl] T cLv cLe cLd A(3) Suc_le_eq)
  qed 
  show ?thesis
    unfolding af_push_vertex_imp_def
    apply (subst dfs_rel_def)
    apply (sep_auto simp: A(1-3) ent assms(1) ex_assn_move_out)
    subgoal premises p
      using entailsD[OF ent_star_mono[OF ent[OF p(5) p(6) p(7) p(8) p(9) p(10) p(11) p(12)[symmetric] p(13)[symmetric] p(14)[symmetric], simplified p(9) p(10) p(11) p(12) p(13) p(14)] ent_refl]] p(4)
      by (simp add: ac_simps)
    done
qed

text \<open>Processing one incident arc: refines @{const af_handle}, threading the new stack pointer and the
      unbounded flag. Premises (agreed design): the bundled DFS invariant @{term \<open>AF_inv st\<close>}, a valid
      free arc @{term \<open>a \<in> \<E>\<close>}, boundedness so far, a non-empty stack, and the \<^emph>\<open>orientation\<close> fact that
      the arc's near endpoint (tail if @{term dir}, head otherwise) is the current stack top --- all
      discharged at the @{const AF_DFS} call site (@{thm af_current_out_endpoint} / the @{text \<open>v # vs\<close>}
      pattern), so none weakens the final \<open>make_acyclic_imp_rule\<close>.\<close>
lemma af_handle_imp_rule:
  assumes I: "AF_inv st" "a \<in> \<E>" "\<not> af_unbounded st" "af_vstack st \<noteq> []"
             "(if dir then fst_exec a else snd_exec a) = hd (af_vstack st)"
  shows "<dfs_rel st s sp> af_handle_imp s a dir sp
   <\<lambda>r. case r of (sp', ubd) \<Rightarrow>
          dfs_rel (af_handle st a dir) s sp' *
          \<up>(sp' = length (af_vstack (af_handle st a dir)) \<and> ubd = af_unbounded (af_handle st a dir))>"
proof -
  have inv1: "AF_invar_1 st" and inv2: "AF_invar_2 st" and invE: "AF_invar_estE st" and invV: "AF_invar_V st" using I(1) unfolding AF_inv_def by auto
  have fi: "flow_invar (af_flow st)" and sti: "st_invar (af_state st)" and oti: "out_invar (af_out_arr st)" and iti: "in_invar (af_in_arr st)" using inv1 by (auto elim: AF_invar_1_props)
  have dvst: "distinct (af_vstack st)" using inv2 by (auto elim: AF_invar_2E)
  have onmem: "\<And>v. v \<in> \<V> \<Longrightarrow> (st_lookup (af_state st) v = OnStack) = (v \<in> set (af_vstack st))" using inv2 by (auto elim: AF_invar_2E)
  have xV: "(if dir then snd_exec a else fst_exec a) \<in> \<V>" using I(2) fst_E_V[OF I(2)] snd_E_V[OF I(2)] by (cases dir) (auto simp: snd_exec_eq[OF I(2)] fst_exec_eq[OF I(2)])
  have body: "<flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd> af_handle_imp s a dir sp <\<lambda>r. case r of (sp', ubd) \<Rightarrow> dfs_rel (af_handle st a dir) s sp' * \<up>(sp' = length (af_vstack (af_handle st a dir)) \<and> ubd = af_unbounded (af_handle st a dir))>"
    if T: "card \<V> \<le> length vl" "card \<V> \<le> length el" "card \<V> \<le> length dl" "sp \<le> card \<V>" "af_vstack st = rev (take sp vl)" "af_estack st = rev (drop (Suc 0) (take sp el))" "af_dstack st = rev (drop (Suc 0) (take sp dl))" "length vl = Lvst" "length el = Lest" "length dl = Ldst" for vl el dl
  proof -
    have svl: "sp \<le> length vl" using T(1,4) by simp
    have sel: "sp \<le> length el" using T(2,4) by simp
    have sdl: "sp \<le> length dl" using T(3,4) by simp
    have cLv: "card \<V> \<le> Lvst" using T(1) T(8) by simp
    have cLe: "card \<V> \<le> Lest" using T(2) T(9) by simp
    have cLd: "card \<V> \<le> Ldst" using T(3) T(10) by simp
    have spLv: "sp \<le> Lvst" using svl T(8) by simp
    have lvst: "length (af_vstack st) = sp" using T(5) svl by simp
    have sp1: "Suc 0 \<le> sp" using I(4) lvst by (cases "af_vstack st") auto
    have foldflat: "flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd \<Longrightarrow>\<^sub>A dfs_rel st s sp"
      unfolding dfs_rel_def
      apply (simp only: ex_assn_move_out)
      apply (rule ent_ex_postI[where x=vl], rule ent_ex_postI[where x=el], rule ent_ex_postI[where x=dl])
      by (sep_auto simp: T cLv cLe cLd)
    have pfe: "<flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd> fst_exec_imp a <\<lambda>r. flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd * \<up>(r = fst_exec a)>"
      by (sep_auto simp: I(2))
    have pse: "<flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd> snd_exec_imp a <\<lambda>r. flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd * \<up>(r = snd_exec a)>"
      by (sep_auto simp: I(2))
    have prooms: "<flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd> af_rooms_imp s a <\<lambda>r. flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd * \<up>(r = af_rooms (af_flow st) a)>"
      by (sep_auto heap: af_rooms_imp_rule[OF fi I(2)])
    have pnth: "<flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd> Array.nth (iestack s) (sp - 1) <\<lambda>r. flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd * \<up>(r = el ! (sp - 1))>"
      using sp1 sel by (sep_auto)
    have pstlook: "<flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd> st_lookup_imp (istate s) (if dir then snd_exec a else fst_exec a) <\<lambda>r. flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd * \<up>(r = st_lookup (af_state st) (if dir then snd_exec a else fst_exec a))>"
      by (sep_auto heap: st_lookup_rule[OF sti xV])
    have ret_ent: "flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd \<Longrightarrow>\<^sub>A dfs_rel st s sp * true * \<up>(sp = length (af_vstack st) \<and> \<not> af_unbounded st)"
      unfolding dfs_rel_def
      apply (simp only: ex_assn_move_out)
      apply (rule ent_ex_postI[where x=vl], rule ent_ex_postI[where x=el], rule ent_ex_postI[where x=dl])
      apply (sep_auto simp: T cLv cLe cLd lvst I(3))
      by (simp add: min.absorb2 spLv)
    have selfl_ent: "flow_assn (af_flow (af_selfloop_handle st a)) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd \<Longrightarrow>\<^sub>A dfs_rel (af_selfloop_handle st a) s sp * true * \<up>(sp = length (af_vstack st))"
      unfolding dfs_rel_def
      apply (simp only: ex_assn_move_out af_selfloop_handle_proj)
      apply (rule ent_ex_postI[where x=vl], rule ent_ex_postI[where x=el], rule ent_ex_postI[where x=dl])
      apply (sep_auto simp: T cLv cLe cLd lvst)
      by (simp add: min.absorb2 spLv)
    have laest: "length (af_estack st) = sp - Suc 0" using T(6) sel by simp
    have neest: "(af_estack st \<noteq> []) = (2 \<le> sp)" using laest sp1 by (cases sp) auto
    have hdest: "2 \<le> sp \<Longrightarrow> hd (af_estack st) = el ! (sp - 1)"
      using T(6) sel sp1 by (simp add: hd_rev last_drop last_conv_nth take_Suc_conv_app_nth)
    have vsub: "set (af_vstack st) \<subseteq> \<V>" using invV by (simp add: AF_invar_V_def)
    have xhd: "fst_exec a \<noteq> snd_exec a \<Longrightarrow> (if dir then snd_exec a else fst_exec a) \<noteq> hd (af_vstack st)"
      using I(5) by (cases dir) auto
    have spcard: "st_lookup (af_state st) (if dir then snd_exec a else fst_exec a) = Unseen \<Longrightarrow> sp < card \<V>"
    proof -
      assume un: "st_lookup (af_state st) (if dir then snd_exec a else fst_exec a) = Unseen"
      have xnmem: "(if dir then snd_exec a else fst_exec a) \<notin> set (af_vstack st)" using un onmem[OF xV] by auto
      have cardv: "card (set (af_vstack st)) = sp" using dvst lvst by (simp add: distinct_card)
      have sub: "set (af_vstack st) \<subset> \<V>" using vsub xV xnmem by blast
      show ?thesis using psubset_card_mono[OF \<V>_finite sub] cardv by simp
    qed
    have slh: "<flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd> af_selfloop_handle_imp s a <\<lambda>r. flow_assn (af_flow (af_selfloop_handle st a)) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd * \<up>(r = af_unbounded (af_selfloop_handle st a))>"
      by (sep_auto heap: af_selfloop_handle_imp_rule[OF fi I(2) I(3)])
    have tr_sl: "<flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd> af_selfloop_handle_imp s a \<bind> (\<lambda>ubd. return (sp, ubd)) <\<lambda>r. case r of (sp', ubd) \<Rightarrow> dfs_rel (af_selfloop_handle st a) s sp' * \<up>(sp' = length (af_vstack (af_selfloop_handle st a)) \<and> ubd = af_unbounded (af_selfloop_handle st a))>"
      apply (rule ht_bind[OF slh]) apply (rule ht_extract_pre_pure(1)) apply hypsubst
      apply (sep_auto)
      apply (rule entailsD[OF selfl_ent]) apply assumption
      done
    have tr_ret: "<flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd> return (sp, False) <\<lambda>r. case r of (sp', ubd) \<Rightarrow> dfs_rel st s sp' * \<up>(sp' = length (af_vstack st) \<and> ubd = af_unbounded st)>"
      apply (sep_auto)
      apply (rule entailsD[OF ret_ent]) apply assumption
      done
    have tr_on: "<flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd> af_close_cycle_imp s up1 dn1 (if dir then snd_exec a else fst_exec a) a dir sp <\<lambda>r. case r of (sp', ubd) \<Rightarrow> dfs_rel (case af_cancel_seg up1 dn1 (if dir then snd_exec a else fst_exec a) (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) of (fl, m', ub) \<Rightarrow> if ub then st\<lparr>af_unbounded := True\<rparr> else af_reset_unsee_seg m' (af_vstack st) (st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st), af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>)) s sp' * \<up>(sp' = length (af_vstack (case af_cancel_seg up1 dn1 (if dir then snd_exec a else fst_exec a) (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) of (fl, m', ub) \<Rightarrow> if ub then st\<lparr>af_unbounded := True\<rparr> else af_reset_unsee_seg m' (af_vstack st) (st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st), af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>))) \<and> ubd = af_unbounded (case af_cancel_seg up1 dn1 (if dir then snd_exec a else fst_exec a) (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) of (fl, m', ub) \<Rightarrow> if ub then st\<lparr>af_unbounded := True\<rparr> else af_reset_unsee_seg m' (af_vstack st) (st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st), af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>)))>"
      if nsl: "fst_exec a \<noteq> snd_exec a" and onst: "st_lookup (af_state st) (if dir then snd_exec a else fst_exec a) = OnStack" for up1 dn1
      by (rule ht_cons_pre[OF foldflat af_close_cycle_imp_rule[OF I(1) I(2) I(3) onst xV xhd[OF nsl] sp1]])
    have tr_un: "<flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd> af_push_vertex_imp s (if dir then snd_exec a else fst_exec a) a dir sp <\<lambda>r. case r of (sp', ubd) \<Rightarrow> dfs_rel (st\<lparr>af_vstack := (if dir then snd_exec a else fst_exec a) # af_vstack st, af_state := st_upd (af_state st) (if dir then snd_exec a else fst_exec a) OnStack, af_estack := a # af_estack st, af_dstack := dir # af_dstack st\<rparr>) s sp' * \<up>(sp' = length (af_vstack (st\<lparr>af_vstack := (if dir then snd_exec a else fst_exec a) # af_vstack st, af_state := st_upd (af_state st) (if dir then snd_exec a else fst_exec a) OnStack, af_estack := a # af_estack st, af_dstack := dir # af_dstack st\<rparr>)) \<and> ubd = af_unbounded (st\<lparr>af_vstack := (if dir then snd_exec a else fst_exec a) # af_vstack st, af_state := st_upd (af_state st) (if dir then snd_exec a else fst_exec a) OnStack, af_estack := a # af_estack st, af_dstack := dir # af_dstack st\<rparr>))>"
      if un: "st_lookup (af_state st) (if dir then snd_exec a else fst_exec a) = Unseen"
      apply (rule ht_cons_post_prec[OF ht_cons_pre[OF foldflat af_push_vertex_imp_rule[OF sti xV spcard[OF un] sp1]]])
      apply (sep_auto simp: lvst I(3) split: prod.splits)
      done
    have pparent: "<flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd> (if 2 \<le> sp then Array.nth (iestack s) (sp - 1) \<bind> (\<lambda>top_e. return (a = top_e)) else return False) <\<lambda>r. flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd * \<up>(r = (af_estack st \<noteq> [] \<and> a = hd (af_estack st)))>"
    proof (cases "2 \<le> sp")
      case True
      show ?thesis
        apply (simp only: if_P[OF True])
        apply (rule ht_bind[OF pnth]) apply (rule ht_extract_pre_pure(1)) apply hypsubst
        apply (sep_auto simp: neest hdest[OF True] True)
        done
    next
      case False
      show ?thesis
        apply (simp only: if_not_P[OF False])
        apply (sep_auto simp: neest False)
        done
    qed
    have mainif: "<flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd> (if fst_exec a = snd_exec a then af_selfloop_handle_imp s a \<bind> (\<lambda>ubd. return (sp, ubd)) else af_rooms_imp s a \<bind> (\<lambda>updn. if \<not> (0 < prod.snd updn \<and> (prod.fst updn = - 1 \<or> 0 < prod.fst updn)) then return (sp, False) else (if 2 \<le> sp then Array.nth (iestack s) (sp - 1) \<bind> (\<lambda>top_e. return (a = top_e)) else return False) \<bind> (\<lambda>is_parent. if is_parent then return (sp, False) else let x = if dir then snd_exec a else fst_exec a in st_lookup_imp (istate s) x \<bind> case_vertex_state (af_push_vertex_imp s x a dir sp) (af_close_cycle_imp s (prod.fst updn) (prod.snd updn) x a dir sp) (return (sp, False))))) <\<lambda>r. case r of (sp', ubd) \<Rightarrow> dfs_rel (af_handle st a dir) s sp' * \<up>(sp' = length (af_vstack (af_handle st a dir)) \<and> ubd = af_unbounded (af_handle st a dir))>"
    proof (cases "fst_exec a = snd_exec a")
      case True
      have afh: "af_handle st a dir = af_selfloop_handle st a" using True by (simp add: af_handle_def)
      show ?thesis by (simp only: if_P[OF True] afh) (rule tr_sl)
    next
      case nsl: False
      obtain up dn where updn: "af_rooms (af_flow st) a = (up, dn)" by (cases "af_rooms (af_flow st) a") auto
      show ?thesis
      proof (cases "0 < dn \<and> (up = - 1 \<or> 0 < up)")
        case gf: False
        have afh: "af_handle st a dir = st" using nsl updn gf by (simp add: af_handle_def)
        show ?thesis
          apply (simp only: if_not_P[OF nsl] afh)
          apply (rule ht_bind[OF prooms], rule ht_extract_pre_pure(1), hypsubst)
          apply (simp only: updn prod.sel if_P[OF gf])
          apply (rule tr_ret)
          done
      next
        case gt: True
        have gtn: "\<not> \<not> (0 < dn \<and> (up = - 1 \<or> 0 < up))" using gt by simp
        show ?thesis
        proof (cases "af_estack st \<noteq> [] \<and> a = hd (af_estack st)")
          case par: True
          have afh: "af_handle st a dir = st" using nsl updn gt par by (simp add: af_handle_def)
          show ?thesis
            apply (simp only: if_not_P[OF nsl] afh)
            apply (rule ht_bind[OF prooms], rule ht_extract_pre_pure(1), hypsubst)
            apply (simp only: updn prod.sel if_not_P[OF gtn])
            apply (rule ht_bind[OF pparent], rule ht_extract_pre_pure(1), hypsubst)
            apply (simp only: if_P[OF par])
            apply (rule tr_ret)
            done
        next
          case np: False
          show ?thesis
          proof (cases "st_lookup (af_state st) (if dir then snd_exec a else fst_exec a)")
            case Finished
            have afh: "af_handle st a dir = st" by (simp only: af_handle_def if_not_P[OF nsl] updn prod.case if_not_P[OF gtn] if_not_P[OF np] Let_def Finished vertex_state.case)
            show ?thesis
              apply (simp only: if_not_P[OF nsl] afh)
              apply (rule ht_bind[OF prooms], rule ht_extract_pre_pure(1), hypsubst)
              apply (simp only: updn prod.sel if_not_P[OF gtn])
              apply (rule ht_bind[OF pparent], rule ht_extract_pre_pure(1), hypsubst)
              apply (simp only: if_not_P[OF np] Let_def)
              apply (rule ht_bind[OF pstlook], rule ht_extract_pre_pure(1), hypsubst)
              apply (simp only: Finished vertex_state.case)
              apply (rule tr_ret)
              done
          next
            case OnStack
            have afh: "af_handle st a dir = (case af_cancel_seg up dn (if dir then snd_exec a else fst_exec a) (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) of (fl, m', ub) \<Rightarrow> if ub then st\<lparr>af_unbounded := True\<rparr> else af_reset_unsee_seg m' (af_vstack st) (st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st), af_estack := drop m' (af_estack st), af_dstack := drop m' (af_dstack st)\<rparr>))" by (simp only: af_handle_def if_not_P[OF nsl] updn prod.case if_not_P[OF gtn] if_not_P[OF np] Let_def OnStack vertex_state.case)
            show ?thesis
              apply (simp only: if_not_P[OF nsl] afh)
              apply (rule ht_bind[OF prooms], rule ht_extract_pre_pure(1), hypsubst)
              apply (simp only: updn prod.sel if_not_P[OF gtn])
              apply (rule ht_bind[OF pparent], rule ht_extract_pre_pure(1), hypsubst)
              apply (simp only: if_not_P[OF np] Let_def)
              apply (rule ht_bind[OF pstlook], rule ht_extract_pre_pure(1), hypsubst)
              apply (simp only: OnStack vertex_state.case)
              apply (rule tr_on[OF nsl OnStack])
              done
          next
            case Unseen
            have afh: "af_handle st a dir = (st\<lparr>af_vstack := (if dir then snd_exec a else fst_exec a) # af_vstack st, af_state := st_upd (af_state st) (if dir then snd_exec a else fst_exec a) OnStack, af_estack := a # af_estack st, af_dstack := dir # af_dstack st\<rparr>)" by (simp only: af_handle_def if_not_P[OF nsl] updn prod.case if_not_P[OF gtn] if_not_P[OF np] Let_def Unseen vertex_state.case)
            show ?thesis
              apply (simp only: if_not_P[OF nsl] afh)
              apply (rule ht_bind[OF prooms], rule ht_extract_pre_pure(1), hypsubst)
              apply (simp only: updn prod.sel if_not_P[OF gtn])
              apply (rule ht_bind[OF pparent], rule ht_extract_pre_pure(1), hypsubst)
              apply (simp only: if_not_P[OF np] Let_def)
              apply (rule ht_bind[OF pstlook], rule ht_extract_pre_pure(1), hypsubst)
              apply (simp only: Unseen vertex_state.case)
              apply (rule tr_un[OF Unseen])
              done
          qed
        qed
      qed
    qed
    show ?thesis
      unfolding af_handle_imp_def
      apply (rule ht_bind[OF pfe], rule ht_extract_pre_pure(1), hypsubst)
      apply (rule ht_bind[OF pse], rule ht_extract_pre_pure(1), hypsubst)
      apply (rule mainif)
      done
  qed
  show ?thesis
    apply (subst dfs_rel_def)
    apply (simp only: ex_assn_move_out)
    apply (rule ht_exEI)+
    apply (simp only: mult.assoc[symmetric])
    apply (rule ht_extract_pre_pure(1))
    apply (erule conjE)+
    apply (rule ht_cons_pre[OF _ body]; (assumption | sep_auto))
    done
qed

text \<open>The inner DFS loop refines @{const AF_DFS_impl}, by \<^emph>\<open>fixpoint induction\<close> on the heap
      @{command partial_function}. The added premise @{term \<open>multigraph_inv out_arr in_arr\<close>} is the
      standing correctness precondition of the whole acyclic-flow development (the input graph arrays
      genuinely represent the graph); it is what @{thm AF_inv_holds_1} etc. require and is threaded to
      the top. The functional side varies over @{term st} / @{term sp}; the imperative state @{term s}
      is threaded unchanged, matching the in-place recursion @{term \<open>f s sp'\<close>}.\<close>
lemma AF_DFS_imp_rule:
  assumes mi0: "multigraph_inv out_arr in_arr" and A: "AF_inv st" "\<not> af_unbounded st" "sp = length (af_vstack st)"
  shows "<dfs_rel st s sp> AF_DFS_imp s sp <\<lambda>r. (\<exists>\<^sub>A sp'. dfs_rel (AF_DFS_impl st) s sp') * \<up>(r = af_unbounded (AF_DFS_impl st))>"
proof -
  have "AF_inv st \<longrightarrow> \<not> af_unbounded st \<longrightarrow> sp = length (af_vstack st) \<longrightarrow> <dfs_rel st s sp> AF_DFS_imp s sp <\<lambda>r. (\<exists>\<^sub>A sp'. dfs_rel (AF_DFS_impl st) s sp') * \<up>(r = af_unbounded (AF_DFS_impl st))>"
  proof (induction arbitrary: st sp rule: AF_DFS_imp.fixp_induct)
    case 1 show ?case by simp
  next
    case 2 show ?case by simp
  next
    case (3 f)
    note IH = "3.IH"
    show ?case
    proof (intro impI, goal_cases)
      case 1
      note I = 1
      show ?case
      proof (cases "sp = 0")
        case sp0: True
        have vst: "af_vstack st = []" using I(3) sp0 by simp
        have impl: "AF_DFS_impl st = st" by (subst AF_DFS_impl.simps) (simp add: I(2) vst)
        show ?thesis by (simp only: if_P[OF sp0] impl) (sep_auto simp: I(2))
      next
        case spn: False
        have sp1: "Suc 0 \<le> sp" using spn by simp
        have inv1: "AF_invar_1 st" and invit: "AF_invar_iter st" and invV: "AF_invar_V st" using I(1) unfolding AF_inv_def by auto
        have fi: "flow_invar (af_flow st)" and sti: "st_invar (af_state st)" and oti: "out_invar (af_out_arr st)" and iti: "in_invar (af_in_arr st)" using inv1 by (auto elim: AF_invar_1_props)
        have mi_cur: "multigraph_inv (af_out_arr st) (af_in_arr st)" using invit by (simp add: AF_invar_iter_def)
        have ane: "af_vstack st \<noteq> []" using I(3) sp1 by (cases "af_vstack st") auto
        have vV: "hd (af_vstack st) \<in> \<V>" using invV ane by (auto simp: AF_invar_V_def hd_in_set)
        have body: "<flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd> Array.nth (ivstack s) (sp - 1) \<bind> (\<lambda>v. out_has_imp (iout s) v \<bind> (\<lambda>oh. if oh then out_current_imp (iout s) v \<bind> (\<lambda>a. out_move_imp (iout s) v \<bind> (\<lambda>_. af_handle_imp s a True sp \<bind> (\<lambda>a. case a of (sp', ubd) \<Rightarrow> if ubd then return True else f s sp'))) else in_has_imp (iin s) v \<bind> (\<lambda>ih. if ih then in_current_imp (iin s) v \<bind> (\<lambda>a. in_move_imp (iin s) v \<bind> (\<lambda>_. af_handle_imp s a False sp \<bind> (\<lambda>a. case a of (sp', ubd) \<Rightarrow> if ubd then return True else f s sp'))) else st_upd_imp (istate s) v Finished \<bind> (\<lambda>_. f s (sp - 1))))) <\<lambda>r. (\<exists>\<^sub>A sp'. dfs_rel (AF_DFS_impl st) s sp') * \<up>(r = af_unbounded (AF_DFS_impl st))>"
          if T: "card \<V> \<le> length vl" "card \<V> \<le> length el" "card \<V> \<le> length dl" "sp \<le> card \<V>" "af_vstack st = rev (take sp vl)" "af_estack st = rev (drop (Suc 0) (take sp el))" "af_dstack st = rev (drop (Suc 0) (take sp dl))" "length vl = Lvst" "length el = Lest" "length dl = Ldst" for vl el dl
        proof -
          have svl: "sp \<le> length vl" using T(1,4) by simp
          have sel: "sp \<le> length el" using T(2,4) by simp
          have sdl: "sp \<le> length dl" using T(3,4) by simp
          have cLv: "card \<V> \<le> Lvst" using T(1) T(8) by simp
          have cLe: "card \<V> \<le> Lest" using T(2) T(9) by simp
          have cLd: "card \<V> \<le> Ldst" using T(3) T(10) by simp
          have spLv: "sp \<le> Lvst" using svl T(8) by simp
          have lvst: "length (af_vstack st) = sp" using T(5) svl by simp
          have vhd: "vl ! (sp - 1) = hd (af_vstack st)"
          proof -
            have s1: "sp - 1 < length vl" using svl sp1 by simp
            have "take sp vl = take (Suc (sp - 1)) vl" using sp1 by simp
            also have "... = take (sp - 1) vl @ [vl ! (sp - 1)]" using s1 by (rule take_Suc_conv_app_nth)
            finally have "af_vstack st = rev (take (sp - 1) vl @ [vl ! (sp - 1)])" using T(5) by simp
            thus ?thesis by simp
          qed
          have vVn: "vl ! (sp - 1) \<in> \<V>" using vhd vV by simp
          have foldflat: "flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd \<Longrightarrow>\<^sub>A dfs_rel st s sp"
            unfolding dfs_rel_def
            apply (simp only: ex_assn_move_out)
            apply (rule ent_ex_postI[where x=vl], rule ent_ex_postI[where x=el], rule ent_ex_postI[where x=dl])
            by (sep_auto simp: T cLv cLe cLd)
          have svn: "sp - 1 < length vl" using svl sp1 by simp
          have pv: "<flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd> Array.nth (ivstack s) (sp - 1) <\<lambda>r. flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd * \<up>(r = vl ! (sp - 1))>"
            using svn by sep_auto
          have phas_out: "<flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd> out_has_imp (iout s) (vl ! (sp - 1)) <\<lambda>r. flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd * \<up>(r = out_has (af_out_arr st) (vl ! (sp - 1)))>"
            by (sep_auto heap: out_has_rule[OF oti vVn])
          have phas_in: "<flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd> in_has_imp (iin s) (vl ! (sp - 1)) <\<lambda>r. flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd * \<up>(r = in_has (af_in_arr st) (vl ! (sp - 1)))>"
            by (sep_auto heap: in_has_rule[OF iti vVn])
          have disp: "<flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd> (if out_has (af_out_arr st) (vl ! (sp - 1)) then out_current_imp (iout s) (vl ! (sp - 1)) \<bind> (\<lambda>a. out_move_imp (iout s) (vl ! (sp - 1)) \<bind> (\<lambda>_. af_handle_imp s a True sp \<bind> (\<lambda>a. case a of (sp', ubd) \<Rightarrow> if ubd then return True else f s sp'))) else in_has_imp (iin s) (vl ! (sp - 1)) \<bind> (\<lambda>ih. if ih then in_current_imp (iin s) (vl ! (sp - 1)) \<bind> (\<lambda>a. in_move_imp (iin s) (vl ! (sp - 1)) \<bind> (\<lambda>_. af_handle_imp s a False sp \<bind> (\<lambda>a. case a of (sp', ubd) \<Rightarrow> if ubd then return True else f s sp'))) else st_upd_imp (istate s) (vl ! (sp - 1)) Finished \<bind> (\<lambda>_. f s (sp - 1)))) <\<lambda>r. (\<exists>\<^sub>A sp'. dfs_rel (AF_DFS_impl st) s sp') * \<up>(r = af_unbounded (AF_DFS_impl st))>"
          proof (cases "out_has (af_out_arr st) (vl ! (sp - 1))")
            case oh: True
            have he: "out_has (af_out_arr st) (hd (af_vstack st))" using oh vhd by simp
            have ne_out: "out_remaining (af_out_arr st) (hd (af_vstack st)) \<noteq> {}" using outg.idx_has[OF oti vV] he by simp
            have aeo: "out_current (af_out_arr st) (hd (af_vstack st)) \<in> \<E>" using af_current_out_endpoint[OF mi_cur vV he] by simp
            have fsto: "fst_exec (out_current (af_out_arr st) (hd (af_vstack st))) = hd (af_vstack st)" using af_current_out_endpoint[OF mi_cur vV he] fst_exec_eq[OF aeo] by simp
            have call1: "AF_DFS_call_1_conds st" using I(2) ane he by (auto simp: AF_DFS_call_1_conds_def split: list.splits)
            have inv_moved: "AF_inv (st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack st))\<rparr>)" using I(1) AF_invar_1_out_advance[OF vV inv1] multigraph_inv_out_advance[OF mi_cur he] vV by (auto simp: AF_inv_def AF_invar_iter_def)
            have pcur_out: "<flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd> out_current_imp (iout s) (hd (af_vstack st)) <\<lambda>r. flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd * \<up>(r = out_current (af_out_arr st) (hd (af_vstack st)))>" by (sep_auto heap: out_current_rule[OF oti vV ne_out])
            have pmove_out: "<flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd> out_move_imp (iout s) (hd (af_vstack st)) <\<lambda>_. flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (out_move (af_out_arr st) (hd (af_vstack st))) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd>" by (sep_auto heap: out_move_rule[OF oti vV ne_out])
            have foldflat_moved: "flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (out_move (af_out_arr st) (hd (af_vstack st))) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd \<Longrightarrow>\<^sub>A dfs_rel (st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack st))\<rparr>) s sp"
              unfolding dfs_rel_def apply (simp only: ex_assn_move_out) apply (rule ent_ex_postI[where x=vl], rule ent_ex_postI[where x=el], rule ent_ex_postI[where x=dl]) by (sep_auto simp: T cLv cLe cLd)
            have upd1eq: "AF_DFS_upd1 st = af_handle (st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack st))\<rparr>) (out_current (af_out_arr st) (hd (af_vstack st))) True" by (simp add: AF_DFS_upd1_def Let_def)
            have impl_out: "AF_DFS_impl st = AF_DFS_impl (AF_DFS_upd1 st)"
            proof (cases "af_vstack st")
              case Nil thus ?thesis using ane by simp next
              case (Cons v vs) hence hv: "hd (af_vstack st) = v" by simp
              show ?thesis apply (subst AF_DFS_impl.simps) using I(2) he by (simp add: Cons hv AF_DFS_upd1_def Let_def)
            qed
            have ubd_impl: "af_unbounded (AF_DFS_upd1 st) \<Longrightarrow> AF_DFS_impl (AF_DFS_upd1 st) = AF_DFS_upd1 st" by (subst AF_DFS_impl.simps) simp
            have nub_m: "\<not> af_unbounded (st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack st))\<rparr>)" using I(2) by simp
            have ane_m: "af_vstack (st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack st))\<rparr>) \<noteq> []" using ane by simp
            have ori_m: "(if True then fst_exec (out_current (af_out_arr st) (hd (af_vstack st))) else snd_exec (out_current (af_out_arr st) (hd (af_vstack st)))) = hd (af_vstack (st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack st))\<rparr>))" using fsto by simp
            have ah: "<dfs_rel (st\<lparr>af_out_arr := out_move (af_out_arr st) (hd (af_vstack st))\<rparr>) s sp> af_handle_imp s (out_current (af_out_arr st) (hd (af_vstack st))) True sp <\<lambda>r. case r of (sp', ubd) \<Rightarrow> dfs_rel (AF_DFS_upd1 st) s sp' * \<up>(sp' = length (af_vstack (AF_DFS_upd1 st)) \<and> ubd = af_unbounded (AF_DFS_upd1 st))>"
              using af_handle_imp_rule[OF inv_moved aeo nub_m ane_m ori_m] by (simp only: upd1eq[symmetric])
            have tail: "<case r of (sp', ubd) \<Rightarrow> dfs_rel (AF_DFS_upd1 st) s sp' * \<up>(sp' = length (af_vstack (AF_DFS_upd1 st)) \<and> ubd = af_unbounded (AF_DFS_upd1 st))> (case r of (sp', ubd) \<Rightarrow> if ubd then return True else f s sp') <\<lambda>r'. (\<exists>\<^sub>A sp''. dfs_rel (AF_DFS_impl st) s sp'') * \<up>(r' = af_unbounded (AF_DFS_impl st))>" for r
            proof (cases r)
              case (Pair sp' ubd)
              have "<dfs_rel (AF_DFS_upd1 st) s sp' * \<up>(sp' = length (af_vstack (AF_DFS_upd1 st)) \<and> ubd = af_unbounded (AF_DFS_upd1 st))> (if ubd then return True else f s sp') <\<lambda>r'. (\<exists>\<^sub>A sp''. dfs_rel (AF_DFS_impl st) s sp'') * \<up>(r' = af_unbounded (AF_DFS_impl st))>"
              proof (cases ubd)
                case True
                show ?thesis proof (rule ht_extract_pre_pure(1), goal_cases)
                  case 1
                  have ubd_eq: "af_unbounded (AF_DFS_upd1 st) = True" using 1 True by simp
                  have impl_eq: "AF_DFS_impl st = AF_DFS_upd1 st" using impl_out ubd_impl ubd_eq by simp
                  show ?case by (simp only: True if_True impl_eq) (sep_auto simp: ubd_eq)
                qed
              next
                case False
                show ?thesis proof (rule ht_extract_pre_pure(1), goal_cases)
                  case 1
                  have sp_eq: "sp' = length (af_vstack (AF_DFS_upd1 st))" using 1 by simp
                  have nub: "\<not> af_unbounded (AF_DFS_upd1 st)" using 1 False by simp
                  have inv1u: "AF_inv (AF_DFS_upd1 st)" using AF_inv_holds_1[OF mi0 call1 I(1)] .
                  have IHu: "<dfs_rel (AF_DFS_upd1 st) s sp'> f s sp' <\<lambda>r'. (\<exists>\<^sub>A sp''. dfs_rel (AF_DFS_impl (AF_DFS_upd1 st)) s sp'') * \<up>(r' = af_unbounded (AF_DFS_impl (AF_DFS_upd1 st)))>" using IH[of "AF_DFS_upd1 st" sp'] inv1u nub sp_eq by simp
                  show ?case by (simp only: False if_False impl_out) (rule IHu)
                qed
              qed
              thus ?thesis by (simp only: Pair prod.case)
            qed
            show ?thesis
              apply (simp only: vhd if_P[OF he])
              apply (rule ht_bind[OF pcur_out], rule ht_extract_pre_pure(1), hypsubst)
              apply (rule ht_bind[OF pmove_out])
              apply (rule ht_bind[OF ht_cons_pre[OF foldflat_moved ah]])
              apply (rule tail)
              done
          next
            case onoh: False
            have heno: "\<not> out_has (af_out_arr st) (hd (af_vstack st))" using onoh vhd by simp
            have disp2: "<flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd> (if in_has (af_in_arr st) (vl ! (sp - 1)) then in_current_imp (iin s) (vl ! (sp - 1)) \<bind> (\<lambda>a. in_move_imp (iin s) (vl ! (sp - 1)) \<bind> (\<lambda>_. af_handle_imp s a False sp \<bind> (\<lambda>a. case a of (sp', ubd) \<Rightarrow> if ubd then return True else f s sp'))) else st_upd_imp (istate s) (vl ! (sp - 1)) Finished \<bind> (\<lambda>_. f s (sp - 1))) <\<lambda>r. (\<exists>\<^sub>A sp'. dfs_rel (AF_DFS_impl st) s sp') * \<up>(r = af_unbounded (AF_DFS_impl st))>"
            proof (cases "in_has (af_in_arr st) (vl ! (sp - 1))")
              case ih: True
              have hi: "in_has (af_in_arr st) (hd (af_vstack st))" using ih vhd by simp
              have ne_in: "in_remaining (af_in_arr st) (hd (af_vstack st)) \<noteq> {}" using ing.idx_has[OF iti vV] hi by simp
              have aei: "in_current (af_in_arr st) (hd (af_vstack st)) \<in> \<E>" using af_current_in_endpoint[OF mi_cur vV hi] by simp
              have fsti: "snd_exec (in_current (af_in_arr st) (hd (af_vstack st))) = hd (af_vstack st)" using af_current_in_endpoint[OF mi_cur vV hi] snd_exec_eq[OF aei] by simp
              have call2: "AF_DFS_call_2_conds st" using I(2) ane heno hi by (auto simp: AF_DFS_call_2_conds_def split: list.splits)
              have inv_moved: "AF_inv (st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack st))\<rparr>)" using I(1) AF_invar_1_in_advance[OF vV inv1] multigraph_inv_in_advance[OF mi_cur hi] vV by (auto simp: AF_inv_def AF_invar_iter_def)
              have pcur_in: "<flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd> in_current_imp (iin s) (hd (af_vstack st)) <\<lambda>r. flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd * \<up>(r = in_current (af_in_arr st) (hd (af_vstack st)))>" by (sep_auto heap: in_current_rule[OF iti vV ne_in])
              have pmove_in: "<flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd> in_move_imp (iin s) (hd (af_vstack st)) <\<lambda>_. flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (in_move (af_in_arr st) (hd (af_vstack st))) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd>" by (sep_auto heap: in_move_rule[OF iti vV ne_in])
              have foldflat_moved: "flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (in_move (af_in_arr st) (hd (af_vstack st))) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd \<Longrightarrow>\<^sub>A dfs_rel (st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack st))\<rparr>) s sp"
                unfolding dfs_rel_def apply (simp only: ex_assn_move_out) apply (rule ent_ex_postI[where x=vl], rule ent_ex_postI[where x=el], rule ent_ex_postI[where x=dl]) by (sep_auto simp: T cLv cLe cLd)
              have upd2eq: "AF_DFS_upd2 st = af_handle (st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack st))\<rparr>) (in_current (af_in_arr st) (hd (af_vstack st))) False" by (simp add: AF_DFS_upd2_def Let_def)
              have impl_in: "AF_DFS_impl st = AF_DFS_impl (AF_DFS_upd2 st)"
              proof (cases "af_vstack st")
                case Nil thus ?thesis using ane by simp next
                case (Cons v vs) hence hv: "hd (af_vstack st) = v" by simp
                show ?thesis apply (subst AF_DFS_impl.simps) using I(2) heno hi by (simp add: Cons hv AF_DFS_upd2_def Let_def)
              qed
              have ubd_impl2: "af_unbounded (AF_DFS_upd2 st) \<Longrightarrow> AF_DFS_impl (AF_DFS_upd2 st) = AF_DFS_upd2 st" by (subst AF_DFS_impl.simps) simp
              have nub_m2: "\<not> af_unbounded (st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack st))\<rparr>)" using I(2) by simp
              have ane_m2: "af_vstack (st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack st))\<rparr>) \<noteq> []" using ane by simp
              have ori_m2: "(if False then fst_exec (in_current (af_in_arr st) (hd (af_vstack st))) else snd_exec (in_current (af_in_arr st) (hd (af_vstack st)))) = hd (af_vstack (st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack st))\<rparr>))" using fsti by simp
              have ah2: "<dfs_rel (st\<lparr>af_in_arr := in_move (af_in_arr st) (hd (af_vstack st))\<rparr>) s sp> af_handle_imp s (in_current (af_in_arr st) (hd (af_vstack st))) False sp <\<lambda>r. case r of (sp', ubd) \<Rightarrow> dfs_rel (AF_DFS_upd2 st) s sp' * \<up>(sp' = length (af_vstack (AF_DFS_upd2 st)) \<and> ubd = af_unbounded (AF_DFS_upd2 st))>"
                using af_handle_imp_rule[OF inv_moved aei nub_m2 ane_m2 ori_m2] by (simp only: upd2eq[symmetric])
              have tail2: "<case r of (sp', ubd) \<Rightarrow> dfs_rel (AF_DFS_upd2 st) s sp' * \<up>(sp' = length (af_vstack (AF_DFS_upd2 st)) \<and> ubd = af_unbounded (AF_DFS_upd2 st))> (case r of (sp', ubd) \<Rightarrow> if ubd then return True else f s sp') <\<lambda>r'. (\<exists>\<^sub>A sp''. dfs_rel (AF_DFS_impl st) s sp'') * \<up>(r' = af_unbounded (AF_DFS_impl st))>" for r
              proof (cases r)
                case (Pair sp' ubd)
                have "<dfs_rel (AF_DFS_upd2 st) s sp' * \<up>(sp' = length (af_vstack (AF_DFS_upd2 st)) \<and> ubd = af_unbounded (AF_DFS_upd2 st))> (if ubd then return True else f s sp') <\<lambda>r'. (\<exists>\<^sub>A sp''. dfs_rel (AF_DFS_impl st) s sp'') * \<up>(r' = af_unbounded (AF_DFS_impl st))>"
                proof (cases ubd)
                  case True
                  show ?thesis proof (rule ht_extract_pre_pure(1), goal_cases)
                    case 1
                    have ubd_eq: "af_unbounded (AF_DFS_upd2 st) = True" using 1 True by simp
                    have impl_eq: "AF_DFS_impl st = AF_DFS_upd2 st" using impl_in ubd_impl2 ubd_eq by simp
                    show ?case by (simp only: True if_True impl_eq) (sep_auto simp: ubd_eq)
                  qed
                next
                  case False
                  show ?thesis proof (rule ht_extract_pre_pure(1), goal_cases)
                    case 1
                    have sp_eq: "sp' = length (af_vstack (AF_DFS_upd2 st))" using 1 by simp
                    have nub: "\<not> af_unbounded (AF_DFS_upd2 st)" using 1 False by simp
                    have inv2u: "AF_inv (AF_DFS_upd2 st)" using AF_inv_holds_2[OF mi0 call2 I(1)] .
                    have IHu: "<dfs_rel (AF_DFS_upd2 st) s sp'> f s sp' <\<lambda>r'. (\<exists>\<^sub>A sp''. dfs_rel (AF_DFS_impl (AF_DFS_upd2 st)) s sp'') * \<up>(r' = af_unbounded (AF_DFS_impl (AF_DFS_upd2 st)))>" using IH[of "AF_DFS_upd2 st" sp'] inv2u nub sp_eq by simp
                    show ?case by (simp only: False if_False impl_in) (rule IHu)
                  qed
                qed
                thus ?thesis by (simp only: Pair prod.case)
              qed
              show ?thesis
                apply (simp only: vhd if_P[OF hi])
                apply (rule ht_bind[OF pcur_in], rule ht_extract_pre_pure(1), hypsubst)
                apply (rule ht_bind[OF pmove_in])
                apply (rule ht_bind[OF ht_cons_pre[OF foldflat_moved ah2]])
                apply (rule tail2)
                done
            next
              case ihno: False
              have hino: "\<not> in_has (af_in_arr st) (hd (af_vstack st))" using ihno vhd by simp
              have tlv: "tl (af_vstack st) = rev (take (sp - 1) vl)" using T(5) svl by (simp add: tl_rev butlast_take)
              have tle: "tl (af_estack st) = rev (drop (Suc 0) (take (sp - 1) el))" using T(6) sel by (simp add: tl_rev butlast_take butlast_drop drop_take)
              have tld: "tl (af_dstack st) = rev (drop (Suc 0) (take (sp - 1) dl))" using T(7) sdl by (simp add: tl_rev butlast_take butlast_drop drop_take)
              have spcm: "sp - Suc 0 \<le> card \<V>" using T(4) by (meson diff_le_self le_trans)
              have foldflat_pop: "flow_assn (af_flow st) (iflow s) * state_assn (st_upd (af_state st) (hd (af_vstack st)) Finished) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd \<Longrightarrow>\<^sub>A dfs_rel (AF_DFS_upd3 st) s (sp - 1)"
                unfolding dfs_rel_def AF_DFS_upd3_def apply (simp only: ex_assn_move_out) apply (rule ent_ex_postI[where x=vl], rule ent_ex_postI[where x=el], rule ent_ex_postI[where x=dl]) by (sep_auto simp: T(1) T(2) T(3) spcm tlv tle tld T(8) T(9) T(10) cLv cLe cLd)
              have pupd: "<flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd> st_upd_imp (istate s) (hd (af_vstack st)) Finished <\<lambda>_. flow_assn (af_flow st) (iflow s) * state_assn (st_upd (af_state st) (hd (af_vstack st)) Finished) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd>" by (sep_auto heap: st_upd_rule[OF sti vV])
              have call3: "AF_DFS_call_3_conds st" using I(2) ane heno hino by (auto simp: AF_DFS_call_3_conds_def split: list.splits)
              have inv3u: "AF_inv (AF_DFS_upd3 st)" using AF_inv_holds_3[OF call3 I(1)] .
              have impl_pop: "AF_DFS_impl st = AF_DFS_impl (AF_DFS_upd3 st)"
              proof (cases "af_vstack st")
                case Nil thus ?thesis using ane by simp next
                case (Cons v vs) hence hv: "hd (af_vstack st) = v" by simp
                show ?thesis apply (subst AF_DFS_impl.simps) using I(2) heno hino by (simp add: Cons hv AF_DFS_upd3_def Let_def)
              qed
              have vstpop: "sp - 1 = length (af_vstack (AF_DFS_upd3 st))" using lvst by (simp add: AF_DFS_upd3_def)
              have nub3: "\<not> af_unbounded (AF_DFS_upd3 st)" using I(2) by (simp add: AF_DFS_upd3_def)
              have IHu: "<dfs_rel (AF_DFS_upd3 st) s (sp - 1)> f s (sp - 1) <\<lambda>r'. (\<exists>\<^sub>A sp''. dfs_rel (AF_DFS_impl (AF_DFS_upd3 st)) s sp'') * \<up>(r' = af_unbounded (AF_DFS_impl (AF_DFS_upd3 st)))>" using IH[of "AF_DFS_upd3 st" "sp - 1"] inv3u nub3 vstpop by simp
              show ?thesis
                apply (simp only: vhd if_not_P[OF hino])
                apply (rule ht_bind[OF pupd])
                apply (simp only: impl_pop)
                apply (rule ht_cons_pre[OF foldflat_pop IHu])
                done
            qed
            show ?thesis
              apply (simp only: if_not_P[OF onoh])
              apply (rule ht_bind[OF phas_in], rule ht_extract_pre_pure(1), hypsubst)
              apply (rule disp2)
              done
          qed
          show ?thesis
            apply (rule ht_bind[OF pv], rule ht_extract_pre_pure(1), hypsubst)
            apply (rule ht_bind[OF phas_out], rule ht_extract_pre_pure(1), hypsubst)
            apply (rule disp)
            done
        qed
        show ?thesis
          apply (simp only: if_not_P[OF spn])
          apply (subst dfs_rel_def)
          apply (simp only: ex_assn_move_out)
          apply (rule ht_exEI)+
          apply (simp only: mult.assoc[symmetric])
          apply (rule ht_extract_pre_pure(1))
          apply (erule conjE)+
          apply (rule ht_cons_pre[OF _ body[simplified ex_assn_move_out]]; (assumption | sep_auto))
          done
      qed
    qed
  qed
  thus ?thesis using A by simp
qed

text \<open>Launching the inner DFS from a fresh vertex. Beyond the store invariants, the caller supplies the
      standing @{term \<open>multigraph_inv out_arr in_arr\<close>} (reset target of @{const AF_DFS_imp}), the launch
      graph's @{term \<open>multigraph_inv OG IG\<close>}, capacity-feasibility of the seed flow, and that no vertex is
      @{const OnStack} in the seed state --- exactly the      \<open>AF_inv_initial\<close> hypotheses, all maintained
      by the outer loop's @{const AFF_inv}.\<close>
lemma af_dfs_start_imp_rule:
  assumes fi: "flow_invar Fl" and si: "st_invar St" and ao: "out_invar OG" and ai: "in_invar IG" and vV: "v \<in> \<V>"
    and mi0: "multigraph_inv out_arr in_arr" and miOG: "multigraph_inv OG IG" and feas: "af_cap_feasible Fl"
    and noos: "\<forall>w\<in>\<V>. st_lookup St w \<noteq> OnStack"
    and cvl: "card \<V> \<le> length vl" and cel: "card \<V> \<le> length el" and cdl: "card \<V> \<le> length dl"
    and lvl: "length vl = Lvst" and lel: "length el = Lest" and ldl: "length dl = Ldst"
  shows "<flow_assn Fl (iflow s) * state_assn St (istate s) * out_assn OG (iout s) * in_assn IG (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd> af_dfs_start_imp s v <\<lambda>r. (\<exists>\<^sub>A sp'. dfs_rel (AF_DFS_impl (AF_DFS_initial Fl OG IG St v)) s sp') * \<up>(r = af_unbounded (AF_DFS_impl (AF_DFS_initial Fl OG IG St v)))>"
proof -
  have AF_inv_init: "AF_inv (AF_DFS_initial Fl OG IG St v)" using AF_inv_initial[OF fi si ao ai miOG vV feas noos] .
  have nub_init: "\<not> af_unbounded (AF_DFS_initial Fl OG IG St v)" by (simp add: AF_DFS_initial_def)
  have len_init: "(1::nat) = length (af_vstack (AF_DFS_initial Fl OG IG St v))" by (simp add: AF_DFS_initial_def)
  have cV: "0 < card \<V>" using vV \<V>_finite by (auto simp: card_gt_0_iff)
  have vlne: "vl \<noteq> []" using cV cvl by (metis length_greater_0_conv less_le_trans)
  have cardpos: "0 < length vl" using vlne by simp
  have suc1: "Suc 0 \<le> card \<V>" using cV by simp
  have vst: "(take (Suc 0) vl)[0 := v] = [v]" using vlne by (cases vl) auto
  have foldinit: "flow_assn Fl (iflow s) * state_assn (st_upd St v OnStack) (istate s) * out_assn OG (iout s) * in_assn IG (iin s) * ivstack s \<mapsto>\<^sub>a (vl[0 := v]) * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd \<Longrightarrow>\<^sub>A dfs_rel (AF_DFS_initial Fl OG IG St v) s 1"
    unfolding dfs_rel_def AF_DFS_initial_def
    apply (simp only: ex_assn_move_out)
    apply (rule ent_ex_postI[where x="vl[0 := v]"], rule ent_ex_postI[where x=el], rule ent_ex_postI[where x=dl])
    by (sep_auto simp: cvl cel cdl lvl lel ldl cvl[unfolded lvl] cel[unfolded lel] cdl[unfolded ldl] suc1 vlne vst)
  have pupd: "<flow_assn Fl (iflow s) * state_assn St (istate s) * out_assn OG (iout s) * in_assn IG (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd> Array.upd 0 v (ivstack s) <\<lambda>r. flow_assn Fl (iflow s) * state_assn St (istate s) * out_assn OG (iout s) * in_assn IG (iin s) * ivstack s \<mapsto>\<^sub>a (vl[0 := v]) * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd>"
    by (sep_auto simp: cardpos vlne)
  have pstupd: "<flow_assn Fl (iflow s) * state_assn St (istate s) * out_assn OG (iout s) * in_assn IG (iin s) * ivstack s \<mapsto>\<^sub>a (vl[0 := v]) * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd> st_upd_imp (istate s) v OnStack <\<lambda>_. flow_assn Fl (iflow s) * state_assn (st_upd St v OnStack) (istate s) * out_assn OG (iout s) * in_assn IG (iin s) * ivstack s \<mapsto>\<^sub>a (vl[0 := v]) * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd>"
    by (sep_auto heap: st_upd_rule[OF si vV])
  show ?thesis
    unfolding af_dfs_start_imp_def
    apply (rule ht_bind[OF pupd])
    apply (rule ht_bind[OF pstupd])
    apply (rule ht_cons_pre[OF foldinit AF_DFS_imp_rule[OF mi0 AF_inv_init nub_init len_init]])
    done
qed

text \<open>\<^emph>\<open>partial\_function = domintro bridges.\<close> The executable @{const AF_DFS_impl} / @{const AF_outer_impl}
      (the @{command partial_function} fixpoints, registered as code equations) coincide with the
      totally-defined domintro functions @{const AF_DFS} / @{const AF_outer} on their domains. These are
      what connect the imperative refinement (which mirrors the \<open>_impl\<close> recursion) to the functional
      correctness development (stated for the domintro versions, e.g.\ \<open>AFF_inv_holds_2\<close>).\<close>


lemma AF_DFS_impl_simps:
  shows "AF_DFS_call_1_conds st \<Longrightarrow> AF_DFS_impl st = AF_DFS_impl (AF_DFS_upd1 st)"
    and "AF_DFS_call_2_conds st \<Longrightarrow> AF_DFS_impl st = AF_DFS_impl (AF_DFS_upd2 st)"
    and "AF_DFS_call_3_conds st \<Longrightarrow> AF_DFS_impl st = AF_DFS_impl (AF_DFS_upd3 st)"
    and "AF_DFS_ret_conds st \<Longrightarrow> AF_DFS_impl st = st"
  by (subst AF_DFS_impl.simps, auto simp: AF_DFS_call_1_conds_def AF_DFS_upd1_def AF_DFS_call_2_conds_def AF_DFS_upd2_def AF_DFS_call_3_conds_def AF_DFS_upd3_def AF_DFS_ret_conds_def Let_def split: list.splits if_splits)+

lemma AF_DFS_impl_eq:
  assumes mi0: "multigraph_inv out_arr in_arr" and inv: "AF_inv st"
  shows "AF_DFS_impl st = AF_DFS st"
proof -
  have dom: "AF_DFS_dom st" using AF_DFS_dom[OF mi0 inv] .
  have gen: "AF_DFS_impl st0 = AF_DFS st0" if d: "AF_DFS_dom st0" for st0
    using d
  proof (induction st0 rule: AF_DFS.pinduct)
    case (1 st0)
    show ?case
    proof (rule AF_DFS_cases[where st=st0])
      assume c: "AF_DFS_call_1_conds st0"
      then obtain x21 x22 where cc: "\<not> af_unbounded st0" "af_vstack st0 = x21 # x22" "out_has (af_out_arr st0) x21"
        by (auto simp: AF_DFS_call_1_conds_def split: list.splits)
      have ih: "AF_DFS_impl (AF_DFS_upd1 st0) = AF_DFS (AF_DFS_upd1 st0)"
        using 1(2)[OF cc(1) cc(2) cc(3)] cc(2) by (simp add: AF_DFS_upd1_def)
      show ?thesis using AF_DFS_impl_simps(1)[OF c] ih AF_DFS_simps(1)[OF 1(1) c] by simp
    next
      assume c: "AF_DFS_call_2_conds st0"
      then obtain x21 x22 where cc: "\<not> af_unbounded st0" "af_vstack st0 = x21 # x22" "\<not> out_has (af_out_arr st0) x21" "in_has (af_in_arr st0) x21"
        by (auto simp: AF_DFS_call_2_conds_def split: list.splits)
      have ih: "AF_DFS_impl (AF_DFS_upd2 st0) = AF_DFS (AF_DFS_upd2 st0)"
        using 1(3)[OF cc(1) cc(2) cc(3) cc(4)] cc(2) by (simp add: AF_DFS_upd2_def)
      show ?thesis using AF_DFS_impl_simps(2)[OF c] ih AF_DFS_simps(2)[OF 1(1) c] by simp
    next
      assume c: "AF_DFS_call_3_conds st0"
      then obtain x21 x22 where cc: "\<not> af_unbounded st0" "af_vstack st0 = x21 # x22" "\<not> out_has (af_out_arr st0) x21" "\<not> in_has (af_in_arr st0) x21"
        by (auto simp: AF_DFS_call_3_conds_def split: list.splits)
      have ih: "AF_DFS_impl (AF_DFS_upd3 st0) = AF_DFS (AF_DFS_upd3 st0)"
        using 1(4)[OF cc(1) cc(2) cc(3) cc(4)] cc(2) by (simp add: AF_DFS_upd3_def)
      show ?thesis using AF_DFS_impl_simps(3)[OF c] ih AF_DFS_simps(3)[OF 1(1) c] by simp
    next
      assume c: "AF_DFS_ret_conds st0"
      show ?thesis using AF_DFS_impl_simps(4)[OF c] AF_DFS_simps(4)[OF 1(1) c] by (simp add: AF_DFS_ret_def)
    qed
  qed
  show ?thesis using gen[OF dom] .
qed

lemma AF_outer_impl_simps1: "AF_outer_call_1_conds st \<Longrightarrow> AF_outer_impl st = AF_outer_impl (AF_outer_upd1 st)"
  by (subst AF_outer_impl.simps) (auto simp: AF_outer_call_1_conds_def AF_outer_upd1_def Let_def)

lemma AF_outer_impl_simps_ret: "AF_outer_ret_conds st \<Longrightarrow> AF_outer_impl st = st"
  by (subst AF_outer_impl.simps) (auto simp: AF_outer_ret_conds_def Let_def split: if_splits)

lemma AF_outer_impl_eq:
  assumes mi0: "multigraph_inv out_arr in_arr" and inv: "AFF_inv st"
  shows "AF_outer_impl st = AF_outer st"
proof -
  have dom: "AF_outer_dom st" using AF_outer_dom[OF mi0 inv] .
  have gen: "AF_outer_dom st0 \<Longrightarrow> AFF_inv st0 \<longrightarrow> AF_outer_impl st0 = AF_outer st0" for st0
  proof (induction st0 rule: AF_outer.pinduct)
    case (1 st0)
    show ?case
    proof (intro impI)
      assume aff: "AFF_inv st0"
      show "AF_outer_impl st0 = AF_outer st0"
      proof (rule AF_outer_cases[where st=st0])
        assume c: "AF_outer_call_1_conds st0"
        have affinv1: "AFF_inv (AF_outer_upd1 st0)" using AFF_inv_holds_1[OF c aff] .
        have ih1: "AF_outer_impl (AF_outer_upd1 st0) = AF_outer (AF_outer_upd1 st0)"
          using 1(2) c affinv1 by (auto simp: AF_outer_call_1_conds_def AF_outer_upd1_def)
        show ?thesis using AF_outer_impl_simps1[OF c] ih1 AF_outer_simps(1)[OF 1(1) c] by simp
      next
        assume c: "AF_outer_call_2_conds st0"
        from c have cc: "\<not> aff_unbounded st0" "has_vertex (aff_vit st0)" "st_lookup (aff_state st0) (current_vertex (aff_vit st0)) = Unseen" by (auto simp: AF_outer_call_2_conds_def)
        have ff: "flow_invar (aff_flow st0)" and sti: "st_invar (aff_state st0)" and aoi: "out_invar (aff_out_arr st0)" and aii: "in_invar (aff_in_arr st0)" and mii: "multigraph_inv (aff_out_arr st0) (aff_in_arr st0)" and feas: "af_cap_feasible (aff_flow st0)" and noos0: "\<not> aff_unbounded st0 \<longrightarrow> (\<forall>w\<in>\<V>. st_lookup (aff_state st0) w \<noteq> OnStack)" using aff by (auto simp: AFF_inv_def)
        have vV: "current_vertex (aff_vit st0) \<in> \<V>" using vit_current_V[OF aff cc(2)] .
        have noos': "\<forall>w\<in>\<V>. st_lookup (aff_state st0) w \<noteq> OnStack" using noos0 cc(1) by simp
        have inv_init: "AF_inv (AF_DFS_initial (aff_flow st0) (aff_out_arr st0) (aff_in_arr st0) (aff_state st0) (current_vertex (aff_vit st0)))" using AF_inv_initial[OF ff sti aoi aii mii vV feas noos'] .
        have bridge: "AF_DFS_impl (AF_DFS_initial (aff_flow st0) (aff_out_arr st0) (aff_in_arr st0) (aff_state st0) (current_vertex (aff_vit st0))) = AF_DFS (AF_DFS_initial (aff_flow st0) (aff_out_arr st0) (aff_in_arr st0) (aff_state st0) (current_vertex (aff_vit st0)))" using AF_DFS_impl_eq[OF mi0 inv_init] .
        have affinv2: "AFF_inv (AF_outer_upd2 st0)" using AFF_inv_holds_2[OF mi0 c aff] .
        have impl2: "AF_outer_impl st0 = AF_outer_impl (AF_outer_upd2 st0)"
          apply (subst AF_outer_impl.simps) using cc bridge by (auto simp: AF_outer_upd2_def Let_def)
        have ih2: "AF_outer_impl (AF_outer_upd2 st0) = AF_outer (AF_outer_upd2 st0)"
        proof -
          have "AFF_inv (AF_outer_upd2 st0) \<longrightarrow> AF_outer_impl (AF_outer_upd2 st0) = AF_outer (AF_outer_upd2 st0)"
            using 1(3)[of "current_vertex (aff_vit st0)" "st0\<lparr>aff_vit := move_on_vertex (aff_vit st0)\<rparr>" "AF_DFS (AF_DFS_initial (aff_flow st0) (aff_out_arr st0) (aff_in_arr st0) (aff_state st0) (current_vertex (aff_vit st0)))"] cc
            by (simp add: AF_outer_upd2_def Let_def)
          thus ?thesis using affinv2 by simp
        qed
        show ?thesis using impl2 ih2 AF_outer_simps(2)[OF 1(1) c] by simp
      next
        assume c: "AF_outer_ret_conds st0"
        show ?thesis using AF_outer_impl_simps_ret[OF c] AF_outer_simps(3)[OF 1(1) c] by (simp add: AF_outer_ret_def)
      qed
    qed
  qed
  show ?thesis using gen[OF dom] inv by simp
qed

text \<open>The outer loop over vertices refines @{const AF_outer_impl}. The added premise
      @{term \<open>multigraph_inv out_arr in_arr\<close>} is the standing correctness precondition threaded from the
      top (as for @{thm AF_DFS_imp_rule}); it is exactly what @{thm AFF_inv_holds_1} / @{thm AFF_inv_holds_2}
      require and is discharged at @{const make_acyclic_imp} via @{thm AFF_inv_initial}.\<close>
lemma AF_outer_imp_rule:
  assumes mi0: "multigraph_inv out_arr in_arr" and A: "AFF_inv st" "\<not> aff_unbounded st"
  shows "<outer_rel st s> AF_outer_imp s <\<lambda>r. outer_rel (AF_outer_impl st) s * \<up>(r = aff_unbounded (AF_outer_impl st))>"
proof -
  have "AFF_inv st \<longrightarrow> \<not> aff_unbounded st \<longrightarrow> <outer_rel st s> AF_outer_imp s <\<lambda>r. outer_rel (AF_outer_impl st) s * \<up>(r = aff_unbounded (AF_outer_impl st))>"
  proof (induction arbitrary: st rule: AF_outer_imp.fixp_induct)
    case 1 show ?case by simp
  next
    case 2 show ?case by simp
  next
    case (3 f)
    note IH = "3.IH"
    show ?case
    proof (intro impI, goal_cases)
      case 1
      note I = 1
      have vinv: "vit_invar (aff_vit st)" and vsub: "vit_abstract (aff_vit st) \<subseteq> \<V>" and ffi: "flow_invar (aff_flow st)" and sti: "st_invar (aff_state st)" and aoi: "out_invar (aff_out_arr st)" and aii: "in_invar (aff_in_arr st)" and mii: "multigraph_inv (aff_out_arr st) (aff_in_arr st)" and feas: "af_cap_feasible (aff_flow st)" and noos0: "\<not> aff_unbounded st \<longrightarrow> (\<forall>w\<in>\<V>. st_lookup (aff_state st) w \<noteq> OnStack)" using I(1) by (auto simp: AFF_inv_def)
      have noos: "\<forall>w\<in>\<V>. st_lookup (aff_state st) w \<noteq> OnStack" using noos0 I(2) by simp
      have body: "<flow_assn (aff_flow st) (iflow s) * state_assn (aff_state st) (istate s) * out_assn (aff_out_arr st) (iout s) * in_assn (aff_in_arr st) (iin s) * vit_assn (aff_vit st) (ivit s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd> has_vertex_imp (ivit s) \<bind> (\<lambda>hv. if \<not> hv then return False else current_vertex_imp (ivit s) \<bind> (\<lambda>v. move_on_vertex_imp (ivit s) \<bind> (\<lambda>_. st_lookup_imp (istate s) v \<bind> (\<lambda>stv. if stv \<noteq> Unseen then f s else af_dfs_start_imp s v \<bind> (\<lambda>ubd. if ubd then return True else f s))))) <\<lambda>r. outer_rel (AF_outer_impl st) s * \<up>(r = aff_unbounded (AF_outer_impl st))>"
        if T: "card \<V> \<le> length vl" "card \<V> \<le> length el" "card \<V> \<le> length dl" "length vl = Lvst" "length el = Lest" "length dl = Ldst" for vl el dl
      proof -
        have foldouter: "flow_assn (aff_flow st) (iflow s) * state_assn (aff_state st) (istate s) * out_assn (aff_out_arr st) (iout s) * in_assn (aff_in_arr st) (iin s) * vit_assn (aff_vit st) (ivit s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd \<Longrightarrow>\<^sub>A outer_rel st s"
          unfolding outer_rel_def
          apply (simp only: ex_assn_move_out)
          apply (rule ent_ex_postI[where x=vl], rule ent_ex_postI[where x=el], rule ent_ex_postI[where x=dl])
          by (sep_auto simp: T T(1)[unfolded T(4)] T(2)[unfolded T(5)] T(3)[unfolded T(6)])
        have phv: "<flow_assn (aff_flow st) (iflow s) * state_assn (aff_state st) (istate s) * out_assn (aff_out_arr st) (iout s) * in_assn (aff_in_arr st) (iin s) * vit_assn (aff_vit st) (ivit s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd> has_vertex_imp (ivit s) <\<lambda>r. flow_assn (aff_flow st) (iflow s) * state_assn (aff_state st) (istate s) * out_assn (aff_out_arr st) (iout s) * in_assn (aff_in_arr st) (iin s) * vit_assn (aff_vit st) (ivit s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd * \<up>(r = has_vertex (aff_vit st))>"
          by (sep_auto heap: has_vertex_rule[OF vinv])
        show ?thesis
        proof (cases "has_vertex (aff_vit st)")
          case hvF: False
          have cond: "\<not> has_vertex (aff_vit st)" using hvF by simp
          have retc: "AF_outer_ret_conds st" using hvF by (simp add: AF_outer_ret_conds_def)
          have impl: "AF_outer_impl st = st" using AF_outer_impl_simps_ret[OF retc] .
          have rf2: "<outer_rel st s> return False <\<lambda>r. outer_rel st s * \<up>(r = aff_unbounded st)>" by (sep_auto simp: I(2))
          show ?thesis
            apply (rule ht_bind[OF phv], rule ht_extract_pre_pure(1), hypsubst)
            apply (simp only: if_P[OF cond] impl)
            apply (rule ht_cons_pre[OF foldouter rf2])
            done
        next
          case hvT: True
          have ne: "vit_remaining (aff_vit st) \<noteq> {}" using hvT vinv vertex_iterator.has_current by auto
          have ncond: "\<not> \<not> has_vertex (aff_vit st)" using hvT by simp
          have vV: "current_vertex (aff_vit st) \<in> \<V>" using vit_current_V[OF I(1) hvT] .
          have pcur: "<flow_assn (aff_flow st) (iflow s) * state_assn (aff_state st) (istate s) * out_assn (aff_out_arr st) (iout s) * in_assn (aff_in_arr st) (iin s) * vit_assn (aff_vit st) (ivit s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd> current_vertex_imp (ivit s) <\<lambda>r. flow_assn (aff_flow st) (iflow s) * state_assn (aff_state st) (istate s) * out_assn (aff_out_arr st) (iout s) * in_assn (aff_in_arr st) (iin s) * vit_assn (aff_vit st) (ivit s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd * \<up>(r = current_vertex (aff_vit st))>"
            by (sep_auto heap: current_vertex_rule[OF vinv ne])
          have pmove: "<flow_assn (aff_flow st) (iflow s) * state_assn (aff_state st) (istate s) * out_assn (aff_out_arr st) (iout s) * in_assn (aff_in_arr st) (iin s) * vit_assn (aff_vit st) (ivit s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd> move_on_vertex_imp (ivit s) <\<lambda>_. flow_assn (aff_flow st) (iflow s) * state_assn (aff_state st) (istate s) * out_assn (aff_out_arr st) (iout s) * in_assn (aff_in_arr st) (iin s) * vit_assn (move_on_vertex (aff_vit st)) (ivit s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd>"
            by (sep_auto heap: move_on_vertex_rule[OF vinv ne])
          have pstlook: "<flow_assn (aff_flow st) (iflow s) * state_assn (aff_state st) (istate s) * out_assn (aff_out_arr st) (iout s) * in_assn (aff_in_arr st) (iin s) * vit_assn (move_on_vertex (aff_vit st)) (ivit s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd> st_lookup_imp (istate s) (current_vertex (aff_vit st)) <\<lambda>r. flow_assn (aff_flow st) (iflow s) * state_assn (aff_state st) (istate s) * out_assn (aff_out_arr st) (iout s) * in_assn (aff_in_arr st) (iin s) * vit_assn (move_on_vertex (aff_vit st)) (ivit s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd * \<up>(r = st_lookup (aff_state st) (current_vertex (aff_vit st)))>"
            by (sep_auto heap: st_lookup_rule[OF sti vV])
          have foldmoved: "flow_assn (aff_flow st) (iflow s) * state_assn (aff_state st) (istate s) * out_assn (aff_out_arr st) (iout s) * in_assn (aff_in_arr st) (iin s) * vit_assn (move_on_vertex (aff_vit st)) (ivit s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd \<Longrightarrow>\<^sub>A outer_rel (AF_outer_upd1 st) s"
            unfolding outer_rel_def AF_outer_upd1_def
            apply simp
            apply (rule ent_ex_postI[where x=vl], rule ent_ex_postI[where x=el], rule ent_ex_postI[where x=dl])
            by (sep_auto simp: T T(1)[unfolded T(4)] T(2)[unfolded T(5)] T(3)[unfolded T(6)])
          show ?thesis
          proof (cases "st_lookup (aff_state st) (current_vertex (aff_vit st)) = Unseen")
            case unseenT: True
            have nseq: "\<not> (st_lookup (aff_state st) (current_vertex (aff_vit st)) \<noteq> Unseen)" using unseenT by simp
            have call2: "AF_outer_call_2_conds st" using I(2) hvT unseenT by (auto simp: AF_outer_call_2_conds_def)
            define res where "res = AF_DFS_impl (AF_DFS_initial (aff_flow st) (aff_out_arr st) (aff_in_arr st) (aff_state st) (current_vertex (aff_vit st)))"
            define st2 where "st2 = st\<lparr>aff_vit := move_on_vertex (aff_vit st), aff_flow := af_flow res, aff_state := af_state res, aff_out_arr := af_out_arr res, aff_in_arr := af_in_arr res, aff_unbounded := af_unbounded res\<rparr>"
            have inv_init: "AF_inv (AF_DFS_initial (aff_flow st) (aff_out_arr st) (aff_in_arr st) (aff_state st) (current_vertex (aff_vit st)))" using AF_inv_initial[OF ffi sti aoi aii mii vV feas noos] .
            have bridge: "res = AF_DFS (AF_DFS_initial (aff_flow st) (aff_out_arr st) (aff_in_arr st) (aff_state st) (current_vertex (aff_vit st)))" unfolding res_def using AF_DFS_impl_eq[OF mi0 inv_init] .
            have st2_upd2: "st2 = AF_outer_upd2 st" unfolding st2_def AF_outer_upd2_def Let_def using bridge by simp
            have impl: "AF_outer_impl st = AF_outer_impl st2" unfolding st2_def res_def by (subst AF_outer_impl.simps) (simp add: I(2) hvT unseenT Let_def)
            have dfs_base: "<flow_assn (aff_flow st) (iflow s) * state_assn (aff_state st) (istate s) * out_assn (aff_out_arr st) (iout s) * in_assn (aff_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd> af_dfs_start_imp s (current_vertex (aff_vit st)) <\<lambda>r. (\<exists>\<^sub>A sp'. dfs_rel res s sp') * \<up>(r = af_unbounded res)>"
              unfolding res_def using af_dfs_start_imp_rule[OF ffi sti aoi aii vV mi0 mii feas noos T(1) T(2) T(3) T(4) T(5) T(6)] .
            have reorder: "flow_assn (aff_flow st) (iflow s) * state_assn (aff_state st) (istate s) * out_assn (aff_out_arr st) (iout s) * in_assn (aff_in_arr st) (iin s) * vit_assn (move_on_vertex (aff_vit st)) (ivit s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd \<Longrightarrow>\<^sub>A (flow_assn (aff_flow st) (iflow s) * state_assn (aff_state st) (istate s) * out_assn (aff_out_arr st) (iout s) * in_assn (aff_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd) * vit_assn (move_on_vertex (aff_vit st)) (ivit s)"
              by sep_auto
            have fold_dfs: "(\<exists>\<^sub>A sp'. dfs_rel res s sp' * vit_assn (move_on_vertex (aff_vit st)) (ivit s)) \<Longrightarrow>\<^sub>A outer_rel st2 s"
              unfolding dfs_rel_def outer_rel_def st2_def by sep_auto
            have tail: "<((\<exists>\<^sub>A sp'. dfs_rel res s sp') * \<up>(ubd = af_unbounded res)) * vit_assn (move_on_vertex (aff_vit st)) (ivit s)> (if ubd then return True else f s) <\<lambda>r. outer_rel (AF_outer_impl st) s * \<up>(r = aff_unbounded (AF_outer_impl st))>" for ubd
            proof -
              have reshape: "((\<exists>\<^sub>A sp'. dfs_rel res s sp') * \<up>(ubd = af_unbounded res)) * vit_assn (move_on_vertex (aff_vit st)) (ivit s) \<Longrightarrow>\<^sub>A (\<exists>\<^sub>A sp'. dfs_rel res s sp' * vit_assn (move_on_vertex (aff_vit st)) (ivit s)) * \<up>(ubd = af_unbounded res)"
                by sep_auto
              show ?thesis
                apply (rule ht_cons_pre[OF reshape])
                apply (rule ht_extract_pre_pure(1))
              proof (goal_cases)
                case 1
                show ?case
                proof (cases ubd)
                  case ubT: True
                  have afub: "af_unbounded res = True" using 1 ubT by simp
                  have st2ub: "aff_unbounded st2 = True" unfolding st2_def using afub by simp
                  have retc2: "AF_outer_ret_conds st2" using st2ub by (simp add: AF_outer_ret_conds_def)
                  have implst: "AF_outer_impl st = st2" using impl AF_outer_impl_simps_ret[OF retc2] by simp
                  show ?thesis
                    apply (simp only: ubT if_True implst)
                    apply (rule ht_cons_pre[OF fold_dfs])
                    apply (sep_auto simp: st2ub)
                    done
                next
                  case ubF: False
                  have afub: "af_unbounded res = False" using 1 ubF by simp
                  have nub2: "\<not> aff_unbounded st2" unfolding st2_def using afub by simp
                  have inv2: "AFF_inv st2" using AFF_inv_holds_2[OF mi0 call2 I(1)] by (simp add: st2_upd2)
                  have IHu2: "<outer_rel st2 s> f s <\<lambda>r. outer_rel (AF_outer_impl st2) s * \<up>(r = aff_unbounded (AF_outer_impl st2))>" using IH[of st2] inv2 nub2 by simp
                  show ?thesis
                    apply (simp only: ubF if_False impl)
                    apply (rule ht_cons_pre[OF fold_dfs IHu2])
                    done
                qed
              qed
            qed
            show ?thesis
              apply (rule ht_bind[OF phv], rule ht_extract_pre_pure(1), hypsubst)
              apply (simp only: if_not_P[OF ncond])
              apply (rule ht_bind[OF pcur], rule ht_extract_pre_pure(1), hypsubst)
              apply (rule ht_bind[OF pmove])
              apply (rule ht_bind[OF pstlook], rule ht_extract_pre_pure(1), hypsubst)
              apply (simp only: if_not_P[OF nseq])
              apply (rule ht_bind[OF ht_cons_pre[OF reorder ht_frame[OF dfs_base]]])
              apply (rule tail)
              done
          next
            case unseenF: False
            have condu: "st_lookup (aff_state st) (current_vertex (aff_vit st)) \<noteq> Unseen" using unseenF by simp
            have call1: "AF_outer_call_1_conds st" using I(2) hvT unseenF by (auto simp: AF_outer_call_1_conds_def)
            have impl: "AF_outer_impl st = AF_outer_impl (AF_outer_upd1 st)" using AF_outer_impl_simps1[OF call1] .
            have inv1: "AFF_inv (AF_outer_upd1 st)" using AFF_inv_holds_1[OF call1 I(1)] .
            have nub1: "\<not> aff_unbounded (AF_outer_upd1 st)" using I(2) by (simp add: AF_outer_upd1_def)
            have IHu: "<outer_rel (AF_outer_upd1 st) s> f s <\<lambda>r. outer_rel (AF_outer_impl (AF_outer_upd1 st)) s * \<up>(r = aff_unbounded (AF_outer_impl (AF_outer_upd1 st)))>" using IH[of "AF_outer_upd1 st"] inv1 nub1 by simp
            show ?thesis
              apply (rule ht_bind[OF phv], rule ht_extract_pre_pure(1), hypsubst)
              apply (simp only: if_not_P[OF ncond])
              apply (rule ht_bind[OF pcur], rule ht_extract_pre_pure(1), hypsubst)
              apply (rule ht_bind[OF pmove])
              apply (rule ht_bind[OF pstlook], rule ht_extract_pre_pure(1), hypsubst)
              apply (simp only: if_P[OF condu] impl)
              apply (rule ht_cons_pre[OF foldmoved IHu])
              done
          qed
        qed
      qed
      show ?case
        apply (subst outer_rel_def)
        apply (simp only: ex_assn_move_out)
        apply (rule ht_exEI)+
        apply (simp only: mult.assoc[symmetric])
        apply (rule ht_extract_pre_pure(1))
        apply (erule conjE)+
        apply (rule ht_cons_pre[OF _ body]; (assumption | sep_auto))
        done
    qed
  qed
  thus ?thesis using A by simp
qed

text \<open>\<^emph>\<open>Target theorem.\<close> If the eight input handles / arrays refine the functional input stores, then
      @{const make_acyclic_imp} leaves the flow store representing the functional @{const make_acyclic}
      result and returns @{term True} exactly for the unbounded (@{term None}) verdict --- i.e.\ the final
      imperative structures refine the final functional ones.\<close>
theorem make_acyclic_imp_rule:
  assumes mi0: "multigraph_inv out_arr in_arr" and ff: "flow_invar f0" and feas: "af_cap_feasible f0"
    and vv: "vit_invar all_vertices" and vab: "vit_abstract all_vertices \<subseteq> \<V>"
    and cvs: "card \<V> \<le> length vs0" and ces: "card \<V> \<le> length es0" and cds: "card \<V> \<le> length ds0"
    and lvs: "length vs0 = Lvst" and les: "length es0 = Lest" and lds: "length ds0 = Ldst"
  shows "<flow_assn f0 fh * state_assn state_init sh * out_assn out_arr oh * in_assn in_arr ih *
    vit_assn all_vertices vih * rd * vst \<mapsto>\<^sub>a vs0 * est \<mapsto>\<^sub>a es0 * dst \<mapsto>\<^sub>a ds0>
     make_acyclic_imp fh sh oh ih vih vst est dst
   <\<lambda>r. \<exists>\<^sub>A f'. flow_assn f' fh *
        out_assn (aff_out_arr (AF_outer (AF_outer_initial f0))) oh *
        in_assn (aff_in_arr (AF_outer (AF_outer_initial f0))) ih *
        (\<exists>\<^sub>A vl el dl. vst \<mapsto>\<^sub>a vl * est \<mapsto>\<^sub>a el * dst \<mapsto>\<^sub>a dl *
           \<up>(card \<V> \<le> length vl \<and> card \<V> \<le> length el \<and> card \<V> \<le> length dl \<and>
             length vl = Lvst \<and> length el = Lest \<and> length dl = Ldst)) *
        rd * true *
        \<up>((r \<longleftrightarrow> make_acyclic f0 = None) \<and> (make_acyclic f0 = None \<or> make_acyclic f0 = Some f'))>"
proof -
  have affinv: "AFF_inv (AF_outer_initial f0)" using AFF_inv_initial[OF mi0 ff feas vv vab] .
  have nub: "\<not> aff_unbounded (AF_outer_initial f0)" by (simp add: AF_outer_initial_def)
  define resO where "resO = AF_outer_impl (AF_outer_initial f0)"
  have resO_eq: "resO = AF_outer (AF_outer_initial f0)" unfolding resO_def using AF_outer_impl_eq[OF mi0 affinv] .
  have mkac: "make_acyclic f0 = (if aff_unbounded resO then None else Some (aff_flow resO))"
    by (simp add: make_acyclic_def resO_eq[symmetric] Let_def)
  have foldinit: "flow_assn f0 fh * state_assn state_init sh * out_assn out_arr oh * in_assn in_arr ih * vit_assn all_vertices vih * rd * vst \<mapsto>\<^sub>a vs0 * est \<mapsto>\<^sub>a es0 * dst \<mapsto>\<^sub>a ds0 \<Longrightarrow>\<^sub>A outer_rel (AF_outer_initial f0) (af_impl_state_init fh sh oh ih vih vst est dst)"
    unfolding outer_rel_def AF_outer_initial_def af_impl_state_init_def
    apply simp
    apply (rule ent_ex_postI[where x=vs0], rule ent_ex_postI[where x=es0], rule ent_ex_postI[where x=ds0])
    by (sep_auto simp: cvs ces cds lvs les lds cvs[unfolded lvs] ces[unfolded les] cds[unfolded lds])
  have run: "<outer_rel (AF_outer_initial f0) (af_impl_state_init fh sh oh ih vih vst est dst)> AF_outer_imp (af_impl_state_init fh sh oh ih vih vst est dst) <\<lambda>r. outer_rel resO (af_impl_state_init fh sh oh ih vih vst est dst) * \<up>(r = aff_unbounded resO)>"
    using AF_outer_imp_rule[OF mi0 affinv nub] unfolding resO_def .
  have foldout: "outer_rel resO (af_impl_state_init fh sh oh ih vih vst est dst) * \<up>(r = aff_unbounded resO) \<Longrightarrow>\<^sub>A (\<exists>\<^sub>A f'. flow_assn f' fh * out_assn (aff_out_arr (AF_outer (AF_outer_initial f0))) oh * in_assn (aff_in_arr (AF_outer (AF_outer_initial f0))) ih * (\<exists>\<^sub>A vl el dl. vst \<mapsto>\<^sub>a vl * est \<mapsto>\<^sub>a el * dst \<mapsto>\<^sub>a dl * \<up>(card \<V> \<le> length vl \<and> card \<V> \<le> length el \<and> card \<V> \<le> length dl \<and> length vl = Lvst \<and> length el = Lest \<and> length dl = Ldst)) * rd * true * \<up>((r \<longleftrightarrow> make_acyclic f0 = None) \<and> (make_acyclic f0 = None \<or> make_acyclic f0 = Some f')))" for r
    unfolding outer_rel_def af_impl_state_init_def resO_eq[symmetric]
    apply (rule ent_ex_postI[where x="aff_flow resO"])
    by (sep_auto simp: mkac cvs ces cds lvs les lds cvs[unfolded lvs] ces[unfolded les] cds[unfolded lds])
  show ?thesis
    unfolding make_acyclic_imp_def
    apply (rule ht_cons_pre[OF foldinit])
    apply (rule ht_cons_post_prec[OF run foldout])
    done
qed

end

end