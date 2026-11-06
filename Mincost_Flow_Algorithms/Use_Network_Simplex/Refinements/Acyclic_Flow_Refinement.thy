theory Acyclic_Flow_Refinement
  imports Mincost_Flow_Algorithms.Acyclic_Flow
          Separation_Logic_Imperative_HOL_Partial.Array_Blit
          Data_Structures.Iterable_Set_Specs_Imp Data_Structures.Fixed_Univ_Map_Specs_Imp
begin

section \<open>Imperative refinement of the acyclic-flow procedure\<close>

text \<open>This theory mirrors the functional specification locale @{locale acyclic_flow_impl_spec}, but every
      store the algorithm mutates --- the flow, the three-valued vertex-state map, the two per-vertex edge
      iterators, the vertex iterator of the outer loop and the three parallel DFS stacks --- is now a
      \<^emph>\<open>mutable heap object\<close>, and every operation is lifted into the
      @{typ \<open>_ Heap\<close>} monad. Every fixed operation and every derived constant carries an
      @{text \<open>_imp\<close>} suffix so that this locale can later be combined with the functional locales
      without name clashes.

      The refinement discipline is the standard Imperative-HOL one:
      \<^item> a functional operation that \<^emph>\<open>changes\<close> a data structure (a flow update, a
        vertex-state write, advancing / resetting an iterator) becomes an in-place mutation with result type
        @{typ \<open>unit Heap\<close>} --- the structure is changed but \<^emph>\<open>not returned\<close>;
      \<^item> a functional operation that
        \<^emph>\<open>changes a container and also returns a proper value\<close> drops the container from the
        returned tuple --- it is mutated in place --- and returns only the value(s) in the
        @{typ \<open>_ Heap\<close>} monad (e.g.\ the cancellation returns just its drop count and unbounded flag,
        the flow having been augmented in place);
      \<^item> a functional operation that \<^emph>\<open>computes a value\<close> (a lookup, an endpoint
        projection, a room / cost combination) returns that value in the @{typ \<open>_ Heap\<close>} monad;
      \<^item> pure arithmetic on values already read out of the heap stays pure.

      The three functional DFS stacks @{term af_vstack} / @{term af_estack} / @{term af_dstack} become three
      \<^emph>\<open>mutable arrays\<close> @{term ivstack} / @{term iestack} / @{term idstack} together with a
      \<^emph>\<open>stack pointer\<close> @{term sp} that is threaded as an ordinary @{typ nat} argument (a value
      on the heap), rather than a boxed length. The intended (never here assumed --- this belongs to the proof
      locale) layout is: @{term ivstack} holds the trail vertices in indices \<open>[0..<sp]\<close> with the top
      at \<open>sp - 1\<close>; for \<open>1 \<le> i < sp\<close> the entries \<open>iestack ! i\<close> /
      \<open>idstack ! i\<close> hold the arc / direction by which \<open>ivstack ! i\<close> was entered from its
      parent \<open>ivstack ! (i - 1)\<close>. Index \<open>0\<close> of the arc / direction stacks (the DFS root)
      is unused.

      The @{term af_unbounded} flag is not stored: exactly as the network-simplex loop returns a
      status value, the loops here \<^emph>\<open>return a boolean\<close> --- @{term True} meaning an unbounded
      instance (a negative infinite-capacity free cycle) was detected --- and leave the mutated flow store
      in place for the caller to read.

      This locale fixes only the imperative operations; it states \<^emph>\<open>no assumptions\<close>. Every text
      below describes how a fixed imperative function is meant to be used, it is not an axiom.\<close>

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

text \<open>The two edge iterators are per-vertex: @{term out_current_imp} / @{term in_current_imp}
      \<^emph>\<open>read\<close> the current outgoing / ingoing arc of a vertex, @{term out_has_imp} /
      @{term in_has_imp} report whether one is left, @{term out_move_imp} / @{term in_move_imp} advance the
      iterator \<^emph>\<open>in place\<close>, and @{term out_reset_imp} / @{term in_reset_imp} reset it to its
      full unconsumed state (copied from the pristine originals) \<^emph>\<open>in place\<close>.
      @{term flow_upd_imp} / @{term st_upd_imp} write, and @{term flow_lookup_imp} / @{term st_lookup_imp} read,
      the flow and vertex-state stores. The vertex iterator @{term current_vertex_imp} / @{term has_vertex_imp} /
      @{term move_on_vertex_imp} hands out the vertices of the outer loop, advancing in place. @{term cap_imp}
      reads an edge capacity (@{term \<open>- 1\<close>} = {\isasyminfinity}), @{term cost_imp} its unit cost, and
      @{term fst_exec_imp} / @{term snd_exec_imp} its two endpoints.\<close>

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

text \<open>Both directional rooms of an arc from a \<^emph>\<open>single\<close> read of its flow and capacity, as
      a pair @{term \<open>(forward, backward)\<close>}: forward @{term \<open>cap a - f a\<close>} (or
      @{term \<open>- 1\<close>}, i.e.\ unbounded, for an infinite capacity) and backward
      @{term \<open>f a\<close>}.\<close>
definition "af_rooms_imp s a =
  do { f \<leftarrow> flow_lookup_imp (iflow s) a; c \<leftarrow> cap_imp a;
       (let fwd = (if c = - 1 then - 1 else c - f) in return (fwd, f)) }"

text \<open>Marginal cost of pushing one unit along an arc in a direction.\<close>
definition "af_delta_cost_imp a dir
              = do { c \<leftarrow> cost_imp a; (let dc = (if dir then c else - c) in return dc) }"

text \<open>Minimum treating @{term \<open>- 1\<close>} as ``no bound'' --- pure, on values already read.\<close>
definition "af_min_imp x y = (if x = - 1 then y else if y = - 1 then x else min x y)"

text \<open>Push @{term \<gamma>} on one arc in place and \<^emph>\<open>return the new flow value\<close>, so a
      caller can test saturation without reading the value back.\<close>
definition "af_push_arc_imp \<gamma> a dir s =
  do { f0 \<leftarrow> flow_lookup_imp (iflow s) a;
       (let \<delta> = (if dir then \<gamma> else - \<gamma>); f = f0 + \<delta> in
        do { _ \<leftarrow> flow_upd_imp (iflow s) a f; return f }) }"

text \<open>Saturation test on an arc's \<^emph>\<open>already-computed\<close> new flow value @{term f} --- reads only
      @{term cap_imp}, not the flow again.\<close>
definition "af_saturated_imp f a
              = do { c \<leftarrow> cap_imp a; return (\<not> (0 < f \<and> (c = - 1 \<or> f < c))) }"

subsection \<open>The two cancellation passes over the stack segment\<close>

text \<open>First pass --- \<^emph>\<open>scan-until-@{term x}\<close>. Walk the DFS stack from the top
      \<open>sp - 1\<close> downward, at each index @{term i} reading the entering arc \<open>iestack ! i\<close>
      (tagged \<open>idstack ! i\<close>) and stopping once the \<^emph>\<open>parent\<close> vertex
      \<open>ivstack ! (i - 1)\<close> is the reached ancestor @{term x}. It accumulates the total marginal cost
      @{term k}, the as-is bottleneck room @{term ra} and the flipped bottleneck room @{term rf};
      @{const af_min_imp} treats @{term \<open>- 1\<close>} as the neutral (unbounded) element. No intermediate
      list is built.\<close>
text \<open>The accumulator is threaded as \<^emph>\<open>three flat arguments\<close> @{term k} / @{term ra} /
      @{term rf} (rather than a boxed triple) so that the recursive call sits directly under a monadic bind, as in
      the network-simplex scan primitives; the collected triple is only assembled at the leaf.\<close>
partial_function (heap) af_scan_imp ::
  "('farr, 'sarr, 'g, 'vvit, 'v, 'e) af_impl_state \<Rightarrow> 'v \<Rightarrow> nat \<Rightarrow> 'n \<Rightarrow> 'n
     \<Rightarrow> 'n \<Rightarrow> ('n \<times> 'n \<times> 'n) Heap"
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

text \<open>Second pass --- push @{term \<gamma>} around the same cycle \<^emph>\<open>and\<close> locate the
      bottleneck. Each cycle arc is pushed once (negating its tag via @{term \<open>d \<noteq> flip\<close>});
      right after the push the arc is tested for saturation. The pass returns the \<^emph>\<open>drop count\<close>
      \<open>m'\<close> = one more than the index of the \<^emph>\<open>deepest\<close> arc that saturated, or
      @{term 0} if none but the closing arc did.

      To keep the pass in \<^emph>\<open>constant stack space\<close> it is written
      \<^emph>\<open>tail-recursively\<close>: rather than combine a result read back from the recursive call, it
      threads two flat @{typ nat} arguments --- the running depth @{term dep} (@{term 1} at the top) and the
      deepest saturated depth @{term best} seen so far (@{term 0} = none). Because the walk descends towards
      @{term x}, a later (deeper) hit simply overwrites @{term best}, so at the leaf @{term best} already
      \<^emph>\<open>is\<close> @{term \<open>m'\<close>}. The flow is mutated in place.\<close>
partial_function (heap) af_push_imp ::
  "('farr, 'sarr, 'g, 'vvit, 'v, 'e) af_impl_state \<Rightarrow> 'n \<Rightarrow> 'v \<Rightarrow> nat
     \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap"
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
      @{term x} (walked by @{const af_scan_imp} / @{const af_push_imp}, never materialised) closed by the arc
      @{term a} in direction @{term dir}, whose two rooms @{term up} / @{term dn} the caller already read. Returns
      only the \<^emph>\<open>drop count\<close> \<open>m'\<close> and the \<^emph>\<open>unbounded\<close> flag;
      the flow is augmented in place. Cost-neutral infinite-cycle handling matches the functional
      \<open>af_cancel_seg\<close>: push in the non-positive-cost orientation, and when that direction is unbounded
      either flip to the finite cost-neutral one or, failing that, report unboundedness.\<close>
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
      @{term i}, @{term \<open>i - 1\<close>}, {\isasymdots} --- in \<^emph>\<open>one\<close> walk set each back
      to @{term Unseen} and reset its iterators. The surviving endpoint just below is not touched.\<close>
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

text \<open>Process one incident arc @{term a} of the current top vertex, traversed in direction @{term dir}, given
      the current stack pointer @{term sp}. All mutation is in place; the returned pair is the
      \<^emph>\<open>new stack pointer\<close> and the \<^emph>\<open>unbounded\<close> flag. A self-loop is
      normalised on sight; a non-free arc, the parent arc, and an arc to a @{term Finished} vertex are no-ops
      (@{term sp} unchanged); an arc to an @{term OnStack} vertex closes a cycle --- cancelled, the stack truncated
      by the drop count and the dropped vertices reset --- and an arc to an @{term Unseen} vertex pushes
      it.\<close>
text \<open>Cycle-closing case (an @{term OnStack} target): cancel the cycle in place, then either report
      unboundedness or truncate the stack by the drop count @{term \<open>m'\<close>} and reset the dropped
      vertices.\<close>
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

text \<open>Process one incident arc @{term a} of the current top vertex, traversed in direction @{term dir}, given
      the current stack pointer @{term sp}. All mutation is in place; the returned pair is the
      \<^emph>\<open>new stack pointer\<close> and the \<^emph>\<open>unbounded\<close> flag. A self-loop is
      normalised on sight; a non-free arc, the parent arc, and an arc to a @{term Finished} vertex are no-ops
      (@{term sp} unchanged); an arc to an @{term OnStack} vertex closes a cycle and an arc to an @{term Unseen}
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

text \<open>The inner loop, threading the stack pointer @{term sp}. An empty stack (@{term \<open>sp = 0\<close>})
      returns ``bounded''. Otherwise the top vertex is scanned: an outgoing free arc first (the current arc is
      read, the iterator advanced in place, then @{const af_handle_imp} run), then an ingoing one, then backtrack
      --- mark the top @{term Finished} and pop (@{term \<open>sp - 1\<close>}). As soon as @{const af_handle_imp}
      reports unboundedness the loop returns @{term True}.\<close>
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

text \<open>Launch the inner DFS from an unseen vertex @{term v}: seed the stack with @{term v} at index @{term 0}
      (so @{term \<open>sp = 1\<close>}), mark it @{term OnStack}, and run. Returns the unbounded flag.\<close>
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

text \<open>The initial imperative state is
      \<^emph>\<open>assembled from externally supplied handles and arrays\<close>: the flow store @{term fl}, the
      vertex-state store @{term stt}, the two edge-iterator stores @{term oa} / @{term ia}, the vertex iterator
      @{term vit}, and --- crucially --- the three DFS-stack arrays @{term vst} / @{term est} / @{term dst}.
      \<^emph>\<open>Every non-constant amount of memory therefore originates outside this locale\<close>: the
      caller allocates the stores and the three size-@{text \<open>\<ge> |V|\<close>} stack arrays and hands them
      in; the assembly below is a constant-size record of handles and the whole procedure adds only O(1) working
      memory on top. This mirrors the functional @{term AF_outer_initial}, except that there the stores are fixed
      locale constants (@{term state_init}, @{term all_vertices}, @{term out_arr}, @{term in_arr}) whereas here
      they are inputs (mutable heap objects the caller owns), and the stacks are explicit arrays rather than lists
      grown on the heap.

      The contract the caller must establish (used, never assumed here): @{term stt} maps every vertex
      to @{term Unseen}, @{term oa} / @{term ia} are the pristine full iterators, @{term vit} is at the
      start of the vertex order, and @{term vst} / @{term est} / @{term dst} have length at least the
      number of vertices.\<close>
definition af_impl_state_init ::
  "'farr \<Rightarrow> 'sarr \<Rightarrow> 'g \<Rightarrow> 'g \<Rightarrow> 'vvit \<Rightarrow> 'v array
     \<Rightarrow> 'e array \<Rightarrow> bool array \<Rightarrow>
     ('farr, 'sarr, 'g, 'vvit, 'v, 'e) af_impl_state" where
  "af_impl_state_init fl stt oa ia vit vst est dst =
     \<lparr> iflow = fl, istate = stt, iout = oa, iin = ia, ivit = vit,
       ivstack = vst, iestack = est, idstack = dst \<rparr>"

text \<open>Top-level entry point: assemble the state from the externally supplied stores and stack arrays, then
      make the flow acyclic \<^emph>\<open>in place\<close>. The returned boolean is @{term True} for an
      \<^emph>\<open>unbounded\<close> instance (the functional @{term None}) and @{term False} otherwise, with the
      resulting acyclic flow readable from the supplied flow store @{term fl} (the functional
      @{term \<open>Some (aff_flow res)\<close>}).\<close>
definition "make_acyclic_imp fl stt oa ia vit vst est dst =
   AF_outer_imp (af_impl_state_init fl stt oa ia vit vst est dst)"

end

section \<open>The refinement proof locale\<close>

text \<open>The proof locale combines the functional proof locale @{locale acyclic_flow_impl} --- which supplies
      the cost-flow network (hence the vertex set @{term \<V>} and edge set @{term \<E>}), the functional ADT
      operations and \<^emph>\<open>all their assumed laws\<close>, and the correctness of the functional
      \<open>make_acyclic\<close> --- with the imperative code locale @{locale acyclic_flow_impl_refine}.

      For each mutable store it fixes a \<^emph>\<open>representation assertion\<close> relating a functional store
      value to its imperative heap handle (@{typ assn} is the separation-logic heap predicate): @{term flow_assn}
      for the flow, @{term state_assn} for the vertex-state map, @{term out_assn} and @{term in_assn} for the
      outgoing and the ingoing edge-iterator collection (at @{term iout} and @{term iin}), and @{term vit_assn} for
      the vertex iterator. The two edge-iterator collections are library instances @{text out_imp} and
      @{text in_imp} of @{locale indexed_iterable_set_imp} over @{term \<V>}, which supply their triples.

      For the other stores it \<^emph>\<open>assumes one Hoare triple per imperative operation\<close>. The discipline
      is:
      \<^item> a mutating operation (result @{typ \<open>unit Heap\<close>}) turns the pre-representation of the
        store into the representation of the \<^emph>\<open>functionally updated\<close> store, with no returned
        value;
      \<^item> a reading operation returns the value the \<^emph>\<open>functional\<close> operation computes,
        keeping the representation unchanged;
      \<^item> the pure endpoint / capacity / cost reads have an empty footprint.

      Crucially, the \<^emph>\<open>pure logical preconditions\<close> of each triple are exactly the hypotheses of
      the corresponding functional ADT law(s) --- the refinement assertion alone does not guarantee that the
      \<^emph>\<open>inputs have the right structure\<close> (the ADT invariant, the key-set membership, a
      non-empty remainder), so those hypotheses must \<^emph>\<open>still be assumed\<close>. For the flow store
      that is @{term \<open>flow_invar Fl\<close>} together with the key-set membership
      @{term \<open>e \<in> \<E>\<close>} (mirroring the law \<open>fixed_univ_map.fixed_univ_map_upd\<close>); for
      the vertex-state store @{term \<open>st_invar St\<close>} and @{term \<open>v \<in> \<V>\<close>}; and for
      the vertex iterator @{term \<open>vit_invar Vit\<close>} plus, for
      \<open>current\<close>/\<open>move_on\<close>, @{term \<open>vit_remaining Vit \<noteq> {}\<close>}
      (mirroring \<open>iterable_set.has_current\<close> and \<open>iterable_set.current_element\<close>).\<close>

text \<open>The vertex states are stored in arrays.\<close>

instance vertex_state :: countable by countable_datatype
instance vertex_state :: heap ..

locale acyclic_flow_impl_refine_proof =
  acyclic_flow_impl where flow_lookup = flow_lookup and st_lookup = st_lookup
      and out_current = out_current and current_vertex = current_vertex +
  acyclic_flow_impl_refine where flow_lookup_imp = flow_lookup_imp and st_lookup_imp = st_lookup_imp
      and out_current_imp = out_current_imp and current_vertex_imp = current_vertex_imp +
  out_imp: indexed_iterable_set_imp where
      idx_invar = out_invar and idx_abstract = out_abstract and idx_current = out_current
      and idx_has = out_has and idx_iterated = out_iterated and idx_remaining = out_remaining
      and idx_move = out_move and idx_reset = out_reset and K = \<V>
      and idx_assn = out_assn and idx_current_imp = out_current_imp
      and idx_has_imp = out_has_imp and idx_move_imp = out_move_imp
      and idx_reset_imp = out_reset_imp +
  in_imp: indexed_iterable_set_imp where
      idx_invar = in_invar and idx_abstract = in_abstract and idx_current = in_current
      and idx_has = in_has and idx_iterated = in_iterated and idx_remaining = in_remaining
      and idx_move = in_move and idx_reset = in_reset and K = \<V>
      and idx_assn = in_assn and idx_current_imp = in_current_imp
      and idx_has_imp = in_has_imp and idx_move_imp = in_move_imp
      and idx_reset_imp = in_reset_imp +
  flow_imp: fixed_univ_map_imp where K = \<E> and fixed_univ_map_invar = flow_invar
      and fixed_univ_map_upd = flow_upd and fixed_univ_map_lookup = flow_lookup
      and fixed_univ_map_val = id and fixed_univ_map_assn = flow_assn
      and fixed_univ_map_upd_imp = flow_upd_imp and fixed_univ_map_lookup_imp = flow_lookup_imp +
  st_imp: fixed_univ_map_imp where K = \<V> and fixed_univ_map_invar = st_invar
      and fixed_univ_map_upd = st_upd and fixed_univ_map_lookup = st_lookup
      and fixed_univ_map_val = id and fixed_univ_map_assn = state_assn
      and fixed_univ_map_upd_imp = st_upd_imp and fixed_univ_map_lookup_imp = st_lookup_imp
  for flow_lookup       :: "'farr \<Rightarrow> 'e::heap \<Rightarrow> ('n::{linordered_idom, heap})"
    and flow_lookup_imp   :: "'farri \<Rightarrow> 'e \<Rightarrow> 'n Heap"
    and st_lookup         :: "'sarr \<Rightarrow> 'v::heap \<Rightarrow> vertex_state"
    and st_lookup_imp     :: "'sarri \<Rightarrow> 'v \<Rightarrow> vertex_state Heap"
    and out_current       :: "'g \<Rightarrow> 'v \<Rightarrow> 'e"
    and out_current_imp   :: "'gi \<Rightarrow> 'v \<Rightarrow> 'e Heap"
    and current_vertex    :: "'vvit \<Rightarrow> 'v"
    and current_vertex_imp :: "'vviti \<Rightarrow> 'v Heap"
    and out_assn :: "'g \<Rightarrow> 'gi \<Rightarrow> assn"
    and in_assn :: "'g \<Rightarrow> 'gi \<Rightarrow> assn"
    and flow_assn  :: "'farr \<Rightarrow> 'farri \<Rightarrow> assn"
    and state_assn :: "'sarr \<Rightarrow> 'sarri \<Rightarrow> assn" +
  fixes vit_assn   :: "'vvit \<Rightarrow> 'vviti \<Rightarrow> assn"
    and rd         :: assn  \<comment>
      \<open>footprint of the (read-only) per-edge cap / cost / endpoint stores\<close>
    and Lvst :: nat and Lest :: nat and Ldst :: nat
      \<comment> \<open>the (fixed) physical lengths of the three caller-supplied DFS stack arrays.  Imperative-HOL
         arrays never change length, but a purely existential postcondition forgets that, and the
         caller (which reuses these arrays afterwards) needs it back.  The acyclifier's own
         requirement stays the lower bound in terms of the vertex count, kept alongside.\<close>
  assumes

    \<comment> \<open>vertex iterator --- an @{locale iterable_set}\<close>
    has_vertex_rule:
      "vit_invar Vit \<Longrightarrow> <vit_assn Vit vh> has_vertex_imp vh
                 <\<lambda>r. vit_assn Vit vh * \<up>(r = has_vertex Vit)>"
    and current_vertex_rule:
      "\<lbrakk>vit_invar Vit; vit_remaining Vit \<noteq> {}\<rbrakk>
         \<Longrightarrow> <vit_assn Vit vh> current_vertex_imp vh
                 <\<lambda>r. vit_assn Vit vh * \<up>(r = current_vertex Vit)>"
    and move_on_vertex_rule:
      "\<lbrakk>vit_invar Vit; vit_remaining Vit \<noteq> {}\<rbrakk>
         \<Longrightarrow> <vit_assn Vit vh> move_on_vertex_imp vh
                 <\<lambda>_. vit_assn (move_on_vertex Vit) vh>"
    \<comment> \<open>pure per-edge reads --- empty heap footprint;
                      the same @{term \<open>e \<in> \<E>\<close>} the functional encoding
        axioms (\<open>cap_encoding\<close>, \<open>cost_encoding\<close>, \<open>fst_exec_eq\<close>,
                \<open>snd_exec_eq\<close>) assume, so a bounded
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

  has_vertex_rule current_vertex_rule move_on_vertex_rule
  cap_rule cost_rule fst_exec_rule snd_exec_rule

text \<open>The @{term \<open>- 1\<close>}-as-{\isasyminfinity} minimum is purely functional and identical to
      @{const af_min}.\<close>
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
   <\<lambda>r. flow_assn (prod.fst (af_push_arc \<gamma> a dir Fl)) (iflow s)
     * \<up>(r = prod.snd (af_push_arc \<gamma> a dir Fl))>"
  unfolding af_push_arc_imp_def af_push_arc_def Let_def by sep_auto


subsection \<open>Refinement relations for the DFS state and the outer state\<close>

text \<open>@{term dfs_rel} ties an \<open>AF_DFS_state\<close> to an imperative \<open>af_impl_state\<close> and a
      stack pointer @{term sp}: the four stores relate through their assertions, and the three stack
      \<^emph>\<open>arrays\<close> (existentially quantified, allocated with room
      @{term \<open>card \<V>\<close>}) carry the functional stacks through
      @{term \<open>af_vstack st = rev (take sp vl)\<close>} (top at index @{term \<open>sp - 1\<close>}) and the
      shifted arc/direction correspondences (index @{term 0} unused). @{term outer_rel} is the analogue for the
      outer loop, additionally relating the vertex iterator.\<close>

definition dfs_rel :: "('v,'e,'farr,'g,'sarr) AF_DFS_state \<Rightarrow> ('farri,'sarri,'gi,'vviti,'v,'e) af_impl_state
                         \<Rightarrow> nat \<Rightarrow> assn" where
  "dfs_rel st s sp = rd *
     flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s) *
     out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) *
     (\<exists>\<^sub>A vl el dl. ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el
      * idstack s \<mapsto>\<^sub>a dl *
        \<up>( card \<V> \<le> length vl \<and> card \<V> \<le> length el \<and> card \<V> \<le> length dl
              \<and> sp \<le> card \<V> \<and>
           af_vstack st = rev (take sp vl) \<and>
           af_estack st = rev (drop (Suc 0) (take sp el)) \<and>
           af_dstack st = rev (drop (Suc 0) (take sp dl)) \<and>
           length vl = Lvst \<and> length el = Lest \<and> length dl = Ldst))"

definition outer_rel :: "('v,'farr,'sarr,'vvit,'g) AF_state
                           \<Rightarrow> ('farri,'sarri,'gi,'vviti,'v,'e) af_impl_state \<Rightarrow> assn" where
  "outer_rel st s = rd *
     flow_assn (aff_flow st) (iflow s) * state_assn (aff_state st) (istate s) *
     out_assn (aff_out_arr st) (iout s) * in_assn (aff_in_arr st) (iin s) *
     vit_assn (aff_vit st) (ivit s) *
     (\<exists>\<^sub>A vl el dl. ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el
      * idstack s \<mapsto>\<^sub>a dl *
        \<up>( card \<V> \<le> length vl \<and> card \<V> \<le> length el \<and> card \<V> \<le> length dl \<and>
           length vl = Lvst \<and> length el = Lest \<and> length dl = Ldst))"

text \<open>Opening @{const dfs_rel} in a precondition: a triple on the four stores and the three concrete
      stack arrays, under the pure facts of the relation, gives the triple on the relation.\<close>
lemma dfs_rel_ht:
  assumes "\<And>vl el dl. \<lbrakk>card \<V> \<le> length vl; card \<V> \<le> length el;
                                    card \<V> \<le> length dl; sp \<le> card \<V>;
             af_vstack st = rev (take sp vl); af_estack st = rev (drop (Suc 0) (take sp el));
             af_dstack st = rev (drop (Suc 0) (take sp dl)); length vl = Lvst; length el = Lest;
               length dl = Ldst\<rbrakk>
           \<Longrightarrow> <flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s)
             * out_assn (af_out_arr st) (iout s) *
                in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el
                  * idstack s \<mapsto>\<^sub>a dl * rd> c <Q>"
  shows "<dfs_rel st s sp> c <Q>"
  unfolding dfs_rel_def
  by (simp only: ex_assn_move_out, intro ht_exEI, simp only: mult.assoc[symmetric],
      rule ht_extract_pre_pure(1), elim conjE)
     (rule ht_cons_pre[OF _ assms]; (assumption | sep_auto))

lemma outer_rel_ht:
  assumes "\<And>vl el dl. \<lbrakk>card \<V> \<le> length vl; card \<V> \<le> length el; card \<V> \<le> length dl;
             length vl = Lvst; length el = Lest; length dl = Ldst\<rbrakk>
           \<Longrightarrow> <flow_assn (aff_flow st) (iflow s) * state_assn (aff_state st) (istate s)
             * out_assn (aff_out_arr st) (iout s) *
                in_assn (aff_in_arr st) (iin s) * vit_assn (aff_vit st) (ivit s) * ivstack s \<mapsto>\<^sub>a vl
                  * iestack s \<mapsto>\<^sub>a el *
                idstack s \<mapsto>\<^sub>a dl * rd> c <Q>"
  shows "<outer_rel st s> c <Q>"
  unfolding outer_rel_def
  by (simp only: ex_assn_move_out, intro ht_exEI, simp only: mult.assoc[symmetric],
      rule ht_extract_pre_pure(1), elim conjE)
     (rule ht_cons_pre[OF _ assms]; (assumption | sep_auto))

subsection \<open>Refinement lemmas, one per operation, from the leaf recursions upwards\<close>


text \<open>Stack-array encodings: the functional stacks are reversed prefixes of the arrays, so the entry at
      index @{term i} heads the reversed prefix of length @{term \<open>Suc i\<close>}.\<close>
lemma rev_take_Suc: "i < length xs \<Longrightarrow> rev (take (Suc i) xs) = xs ! i # rev (take i xs)"
  by (simp add: take_Suc_conv_app_nth)

lemma rev_drop_take_Suc:
  "\<lbrakk>Suc 0 \<le> i; i < length xs\<rbrakk> \<Longrightarrow>
   rev (drop (Suc 0) (take (Suc i) xs)) = xs ! i # rev (drop (Suc 0) (take i xs))"
  by (simp add: take_Suc_conv_app_nth)

text \<open>First cancellation pass: @{const af_scan_imp} walking the stack arrays from index @{term i}
      downwards refines @{const af_scan} on the corresponding stack sub-lists.\<close>
lemma af_scan_imp_rule:
  "\<lbrakk>flow_invar Fl; i < length vl; i < length el; i < length dl;
    set (drop (Suc 0) (take (Suc i) el)) \<subseteq> \<E>; x \<in> set (take i vl)\<rbrakk> \<Longrightarrow>
   <flow_assn Fl (iflow s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el
     * idstack s \<mapsto>\<^sub>a dl * rd>
     af_scan_imp s x i k ra rf
   <\<lambda>r. flow_assn Fl (iflow s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el
     * idstack s \<mapsto>\<^sub>a dl * rd *
        \<up>(r = af_scan Fl x (rev (take (Suc i) vl)) (rev (drop (Suc 0) (take (Suc i) el)))
                          (rev (drop (Suc 0) (take (Suc i) dl))) (k, ra, rf))>"
proof(induction i arbitrary: k ra rf)
  case (Suc i)
  have "el ! Suc i \<in> \<E>" "set (drop (Suc 0) (take (Suc i) el)) \<subseteq> \<E>"
    using Suc.prems(3,5) by (auto simp: take_Suc_conv_app_nth[of "Suc i"])
  moreover have "vl ! i \<noteq> x \<Longrightarrow> x \<in> set (take i vl)"
    using Suc.prems(2,6) by (auto simp: take_Suc_conv_app_nth[of i])
  ultimately show ?case
    using Suc.prems by (subst af_scan_imp.simps)
      (sep_auto simp: rev_take_Suc rev_drop_take_Suc af_min_imp_eq case_prod_beta heap: Suc.IH)
qed simp

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
   <flow_assn Fl (iflow s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el
     * idstack s \<mapsto>\<^sub>a dl * rd>
     af_push_imp s \<gamma> x i flip dep best
   <\<lambda>r. flow_assn (prod.fst (af_push \<gamma> x (rev (take (Suc i) vl)) (rev (drop (Suc 0) (take (Suc i) el)))
                             (rev (drop (Suc 0) (take (Suc i) dl))) flip Fl)) (iflow s)
        * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd
        * \<up>(r = (if prod.snd (af_push \<gamma> x (rev (take (Suc i) vl)) (rev (drop (Suc 0) (take (Suc i) el)))
                            (rev (drop (Suc 0) (take (Suc i) dl))) flip Fl) = 0 then best
                 else dep + prod.snd (af_push \<gamma> x (rev (take (Suc i) vl)) (rev (drop (Suc 0) (take (Suc i) el)))
                            (rev (drop (Suc 0) (take (Suc i) dl))) flip Fl) - 1))>"
proof(induction i arbitrary: Fl dep best)
  case (Suc i)
  have "el ! Suc i \<in> \<E>" "set (drop (Suc 0) (take (Suc i) el)) \<subseteq> \<E>"
    using Suc.prems(4,6) by (auto simp: take_Suc_conv_app_nth[of "Suc i"])
  note IH = Suc.IH[OF _ _ _ _ _ this(2)]
  have "vl ! i \<noteq> x \<Longrightarrow> Suc 0 \<le> i"
    "vl ! i \<noteq> x \<Longrightarrow> x \<in> set (take i vl)"
    using Suc.prems(3,7) by (auto simp: take_Suc_conv_app_nth[of i] Suc_le_eq intro!: gr0I)
  note IH = IH[OF _ this(1) _ _ _ this(2)]
  obtain fl1 f where "af_push_arc \<gamma> (el ! Suc i) (dl ! Suc i = (\<not> flip)) Fl = (fl1, f)" "flow_invar fl1"
    using af_push_arc_flow_invar[OF \<open>el ! Suc i \<in> \<E>\<close> _ Suc.prems(1)] by fastforce
  moreover obtain fl2 r where "af_push \<gamma> x (rev (take (Suc i) vl)) (rev (drop (Suc 0) (take (Suc i) el)))
                                (rev (drop (Suc 0) (take (Suc i) dl))) flip fl1 = (fl2, r)"
    by fastforce
  moreover have "af_push \<gamma> x (rev (take (Suc (Suc i)) vl)) (rev (drop (Suc 0) (take (Suc (Suc i)) el)))
                   (rev (drop (Suc 0) (take (Suc (Suc i)) dl))) flip Fl
                 = (if vl ! i = x then (fl1, if af_saturated f (el ! Suc i) then 1 else 0)
                    else (fl2, if r \<noteq> 0 then Suc r else if af_saturated f (el ! Suc i) then 1 else 0))"
    using calculation Suc.prems(3-5) by (simp add: rev_take_Suc rev_drop_take_Suc)
  note eqs = calculation(1,3) this
  show ?case
    using Suc.prems(1,3-5) \<open>el ! Suc i \<in> \<E>\<close> \<open>flow_invar fl1\<close>
    by (cases "vl ! i = x"; subst af_push_imp.simps, simp only: diff_Suc_1)
       (sep_auto simp: eqs, sep_auto simp: eqs heap: IH)
qed simp

lemma af_push_imp_rule:
  "\<lbrakk>flow_invar Fl; Suc 0 \<le> i; i < length vl; i < length el; i < length dl;
    set (drop (Suc 0) (take (Suc i) el)) \<subseteq> \<E>; x \<in> set (take i vl)\<rbrakk> \<Longrightarrow>
   <flow_assn Fl (iflow s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el
     * idstack s \<mapsto>\<^sub>a dl * rd>
     af_push_imp s \<gamma> x i flip (Suc 0) 0
   <\<lambda>r. case af_push \<gamma> x (rev (take (Suc i) vl)) (rev (drop (Suc 0) (take (Suc i) el)))
                          (rev (drop (Suc 0) (take (Suc i) dl))) flip Fl of (fl', m') \<Rightarrow>
          flow_assn fl' (iflow s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el
            * idstack s \<mapsto>\<^sub>a dl * rd * \<up>(r = m')>"
  by (rule ht_cons_post_prec[OF af_push_imp_gen]; (assumption | sep_auto simp: case_prod_beta))

text \<open>Whole tagged-cycle cancellation, mutating the flow and returning drop count + unbounded flag.\<close>
lemma af_cancel_seg_imp_rule:
  assumes "flow_invar Fl" "a \<in> \<E>" "Suc 0 \<le> sp" "sp \<le> length vl" "sp \<le> length el"
          "sp \<le> length dl" "set (drop (Suc 0) (take sp el)) \<subseteq> \<E>" "x \<in> set (take (sp - Suc 0) vl)"
  shows
   "<flow_assn Fl (iflow s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el
      * idstack s \<mapsto>\<^sub>a dl * rd>
     af_cancel_seg_imp s up dn x a dir sp
   <\<lambda>r. case af_cancel_seg up dn x (rev (take sp vl)) (rev (drop (Suc 0) (take sp el)))
                          (rev (drop (Suc 0) (take sp dl))) a dir Fl of (fl'', m', ubd) \<Rightarrow>
          flow_assn fl'' (iflow s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el *
          idstack s \<mapsto>\<^sub>a dl * rd * \<up>(r = (m', ubd))>"
proof -
  have "sp - Suc 0 < length vl" "sp - Suc 0 < length el" "sp - Suc 0 < length dl"
       "set (drop (Suc 0) (take (Suc (sp - Suc 0)) el)) \<subseteq> \<E>" "Suc 0 \<le> sp - Suc 0"
         "Suc (sp - Suc 0) = sp"
    using assms(3-8) by (auto simp: Suc_le_eq intro!: Suc_lessI)
  note SR = af_scan_imp_rule[OF assms(1) this(1-4) assms(8), unfolded this(6)]
    and PR = af_push_imp_rule[OF assms(1) this(5,1-4) assms(8), unfolded this(6)]
  let ?vs = "rev (take sp vl)" and ?es = "rev (drop (Suc 0) (take sp el))" and ?ds = "rev (drop (Suc 0) (take sp dl))"
  have "set ?es \<subseteq> \<E>"
    using assms(7) by simp
  obtain ra0 rf0 where "(if dir then up else dn) = ra0" "(if dir then dn else up) = rf0"
    by blast
  note dirs = this
  obtain k ra rf where "af_scan Fl x ?vs ?es ?ds (af_delta_cost a dir, ra0, rf0) = (k, ra, rf)"
    by (rule prod_cases3)
  moreover obtain fl1 m1 where "af_push ra x ?vs ?es ?ds False Fl = (fl1, m1)"
    by (rule prod.exhaust)
  moreover note af_push_flow_invar[OF \<open>set ?es \<subseteq> \<E>\<close> this assms(1)]
  moreover obtain fl2 m2 where "af_push rf x ?vs ?es ?ds True Fl = (fl2, m2)"
    by (rule prod.exhaust)
  moreover note af_push_flow_invar[OF \<open>set ?es \<subseteq> \<E>\<close> this assms(1)]
  note eqs = calculation this
  show ?thesis
    using assms(1-3)
    unfolding af_cancel_seg_imp_def af_cancel_seg_def One_nat_def Let_def dirs
    by (sep_auto heap: SR PR simp: eqs case_prod_beta)
qed

text \<open>Reset one vertex's two edge iterators in place.\<close>
lemma af_reset_imp_rule:
  "\<lbrakk>out_invar OG; in_invar IG; v \<in> \<V>\<rbrakk> \<Longrightarrow>
   <out_assn OG (iout s) * in_assn IG (iin s)> af_reset_imp s v
   <\<lambda>_. out_assn (out_reset OG v) (iout s) * in_assn (in_reset IG v) (iin s)>"
  unfolding af_reset_imp_def by sep_auto

text \<open>Generalised fused truncation clean-up over the top @{term n} stack vertices, the walked list given
      directly as @{term \<open>rev (take sp vl)\<close>} so the induction on @{term n} can rethread the
      state.\<close>
lemma af_reset_unsee_seg_imp_gen:
  "\<lbrakk>st_invar (af_state st); out_invar (af_out_arr st); in_invar (af_in_arr st);
    n \<le> sp; sp \<le> length vl; set (take sp vl) \<subseteq> \<V>\<rbrakk> \<Longrightarrow>
   <state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) *
    in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl>
     af_reset_unsee_seg_imp s n (sp - Suc 0)
   <\<lambda>_. state_assn (af_state (af_reset_unsee_seg n (rev (take sp vl)) st)) (istate s) *
        out_assn (af_out_arr (af_reset_unsee_seg n (rev (take sp vl)) st)) (iout s) *
        in_assn (af_in_arr (af_reset_unsee_seg n (rev (take sp vl)) st)) (iin s) * ivstack s \<mapsto>\<^sub>a vl>"
proof(induction n arbitrary: st sp)
  case (Suc n)
  then obtain j where "sp = Suc j"
    by (cases sp) auto
  moreover have "rev (take sp vl) = vl ! j # rev (take j vl)" "vl ! j \<in> \<V>" "set (take j vl) \<subseteq> \<V>"
    using Suc.prems(5,6) calculation by (auto simp: take_Suc_conv_app_nth)
  ultimately show ?case
    using Suc.prems(1-4) by (subst af_reset_unsee_seg_imp.simps)
      (sep_auto heap: af_reset_imp_rule
         Suc.IH[of "af_reset (vl ! j) (st\<lparr>af_state := st_upd (af_state st) (vl ! j) Unseen\<rparr>)" j,
                unfolded af_reset_def, simplified]
         simp: af_reset_def st_upd_invar out_reset_invar in_reset_invar)
qed (subst af_reset_unsee_seg_imp.simps, sep_auto)

text \<open>Fused truncation clean-up over the top @{term n} stack vertices.\<close>
lemma af_reset_unsee_seg_imp_rule:
  "\<lbrakk>st_invar (af_state st); out_invar (af_out_arr st); in_invar (af_in_arr st);
    n \<le> sp; sp \<le> length vl; set (take sp vl) \<subseteq> \<V>;
      af_vstack st = rev (take sp vl)\<rbrakk> \<Longrightarrow>
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
  by (simp add: drop_rev min_def)

lemma tr_e:
  "cm \<le> sp - Suc 0 \<Longrightarrow> sp \<le> length el
     \<Longrightarrow> drop cm (rev (drop (Suc 0) (take sp el))) = rev (drop (Suc 0) (take (sp - cm) el))"
  by (simp add: drop_take tr_v)

text \<open>From the @{const OnStack} guard: an OnStack, in-{\isasymV}, non-top vertex sits strictly below the
      stack top, i.e.\ in the pre-top prefix --- exactly @{const af_cancel_seg}'s
      @{term \<open>x \<in> set (take (sp-1) vl)\<close>}.\<close>
lemma xmem_below_top:
  "\<lbrakk>AF_invar_2 st; st_lookup (af_state st) x = OnStack; x \<in> \<V>;
            x \<noteq> hd (af_vstack st); Suc 0 \<le> sp;
    af_vstack st = rev (take sp vl); sp \<le> length vl\<rbrakk> \<Longrightarrow> x \<in> set (take (sp - Suc 0) vl)"
  by (cases sp) (auto elim!: AF_invar_2E simp: rev_take_Suc)

text \<open>OnStack cycle-closing case of @{const af_handle}: cancel the tagged cycle (mutating the flow),
      then truncate the stacks to the bottleneck and unmark the popped segment. Bundled premise
      @{term \<open>AF_inv st\<close>} supplies the distinctness / trail invariants; the extra pure postcondition
      exposes the new pointer @{term sp'} and the unbounded flag for @{const af_handle}'s caller.\<close>
lemma af_close_cycle_imp_rule:
  assumes "AF_inv st" "a \<in> \<E>" "\<not> af_unbounded st" "st_lookup (af_state st) x = OnStack"
             "x \<in> \<V>" "x \<noteq> hd (af_vstack st)" "Suc 0 \<le> sp"
  shows
   "<dfs_rel st s sp> af_close_cycle_imp s up dn x a dir sp
   <\<lambda>r. case r of (sp', ubd) \<Rightarrow>
          dfs_rel
            (case af_cancel_seg up dn x (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) of
               (fl, m', ub) \<Rightarrow> if ub then st\<lparr>af_unbounded := True\<rparr>
                              else af_reset_unsee_seg m' (af_vstack st)
                                     (st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st),
                                          af_estack := drop m' (af_estack st),
                                            af_dstack := drop m' (af_dstack st)\<rparr>))
            s sp' *
          \<up>(sp' = length (af_vstack
            (case af_cancel_seg up dn x (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) of
               (fl, m', ub) \<Rightarrow> if ub then st\<lparr>af_unbounded := True\<rparr>
                              else af_reset_unsee_seg m' (af_vstack st)
                                     (st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st),
                                          af_estack := drop m' (af_estack st),
                                            af_dstack := drop m' (af_dstack st)\<rparr>))
             ) \<and>
             ubd = af_unbounded
            (case af_cancel_seg up dn x (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) of
               (fl, m', ub) \<Rightarrow> if ub then st\<lparr>af_unbounded := True\<rparr>
                              else af_reset_unsee_seg m' (af_vstack st)
                                     (st\<lparr>af_flow := fl, af_vstack := drop m' (af_vstack st),
                                          af_estack := drop m' (af_estack st),
                                            af_dstack := drop m' (af_dstack st)\<rparr>))
          )>"
proof -
  have inv1: "AF_invar_1 st" and inv2: "AF_invar_2 st" and invE: "AF_invar_estE st" and invV: "AF_invar_V st"
    using assms(1) unfolding AF_inv_def by auto
  have fi: "flow_invar (af_flow st)" and sti: "st_invar (af_state st)" and oti: "out_invar (af_out_arr st)"
   and iti: "in_invar (af_in_arr st)"
    using inv1 by (auto elim: AF_invar_1_props)
  have esub: "set (af_estack st) \<subseteq> \<E>" using invE by (simp add: AF_invar_estE_def)
  have vsub: "set (af_vstack st) \<subseteq> \<V>" using invV by (simp add: AF_invar_V_def)
  obtain fl'' cm ub
    where cs: "af_cancel_seg up dn x (af_vstack st) (af_estack st) (af_dstack st) a dir (af_flow st) = (fl'', cm, ub)"
    by (rule prod_cases3)
  have mles: "cm \<le> length (af_estack st)" using af_cancel_seg_drop_bound[OF cs] .
  have ubflow: "ub \<Longrightarrow> fl'' = af_flow st"
    using cs by (auto simp: af_cancel_seg_def Let_def split: prod.splits if_splits)
  let ?st' = "st\<lparr>af_flow := fl'', af_vstack := drop cm (af_vstack st), af_estack := drop cm (af_estack st),
                  af_dstack := drop cm (af_dstack st)\<rparr>"
  show ?thesis
  proof(rule dfs_rel_ht, goal_cases)
    case (1 vl el dl)
    note T = 1
    have svl: "sp \<le> length vl" and sel: "sp \<le> length el" and sdl: "sp \<le> length dl" using T(1-4) by simp_all
    have cLv: "card \<V> \<le> Lvst" and cLe: "card \<V> \<le> Lest" and cLd: "card \<V> \<le> Ldst"
      using T(1-3,8-10) by simp_all
    have spLv: "sp \<le> Lvst" using svl T(8) by simp
    have lvst: "length (af_vstack st) = sp" using T(5) svl by simp
    have xmem: "x \<in> set (take (sp - Suc 0) vl)" using xmem_below_top[OF inv2 assms(4-7) T(5) svl] .
    have esub': "set (drop (Suc 0) (take sp el)) \<subseteq> \<E>" using esub T(6) by simp
    have cmle: "cm \<le> sp - Suc 0" using mles by (simp add: T(6) sel)
    have cmsp: "cm \<le> sp" using cmle by simp
    have cr: "<flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s)
                * out_assn (af_out_arr st) (iout s) *
               in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el
                 * idstack s \<mapsto>\<^sub>a dl * rd>
                af_cancel_seg_imp s up dn x a dir sp
              <\<lambda>r. flow_assn
                fl'' (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) *
                   in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el
                     * idstack s \<mapsto>\<^sub>a dl * rd *
                   \<up>(r = (cm, ub))>"
      by (sep_auto heap: af_cancel_seg_imp_rule[OF fi assms(2,7) svl sel sdl esub' xmem]
                   simp: T(5)[symmetric] T(6)[symmetric] T(7)[symmetric] cs)
    have vsub': "set (take sp vl) \<subseteq> \<V>" using vsub T(5) by simp
    have scc: "sp - cm \<le> card \<V>" using T(4) by arith
    have stiI: "st_invar (af_state ?st')" and otiI: "out_invar (af_out_arr ?st')" and itiI: "in_invar (af_in_arr ?st')"
      using sti oti iti by simp_all
    note gg = af_reset_unsee_seg_imp_gen[OF stiI otiI itiI cmsp svl vsub', simplified]
    have rst: "<flow_assn fl'' (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) *
                in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el
                  * idstack s \<mapsto>\<^sub>a dl * rd>
                 af_reset_unsee_seg_imp s cm (sp - 1)
               <\<lambda>_. flow_assn
                 fl'' (iflow s) * state_assn (af_state (af_reset_unsee_seg cm (rev (take sp vl)) ?st')) (istate s) *
                    out_assn (af_out_arr (af_reset_unsee_seg cm (rev (take sp vl)) ?st')) (iout s) *
                    in_assn (af_in_arr (af_reset_unsee_seg cm (rev (take sp vl)) ?st')) (iin s) *
                    ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el
                      * idstack s \<mapsto>\<^sub>a dl * rd>"
      by (sep_auto heap: gg)
    have entF_m:
        "flow_assn fl'' (iflow s) * state_assn (af_state (af_reset_unsee_seg cm (af_vstack st) ?st')) (istate s) *
                  out_assn (af_out_arr (af_reset_unsee_seg cm (af_vstack st) ?st')) (iout s) *
                  in_assn (af_in_arr (af_reset_unsee_seg cm (af_vstack st) ?st')) (iin s) *
                  ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd
                  \<Longrightarrow>\<^sub>A dfs_rel (af_reset_unsee_seg cm (af_vstack st) ?st') s (sp - cm) * true *
                      \<up>(sp - cm = length (af_vstack st) - cm \<and> \<not> af_unbounded st)"
      unfolding dfs_rel_def
      by (sep_auto simp: T cLv cLe cLd tr_v[OF svl] tr_e[OF cmle sel] tr_e[OF cmle sdl] lvst assms(3) scc spLv)
    have entT_m: "fl'' = af_flow st \<Longrightarrow>
                  flow_assn fl'' (iflow s) * state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) *
                  in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el
                    * idstack s \<mapsto>\<^sub>a dl * rd
                  \<Longrightarrow>\<^sub>A dfs_rel (st\<lparr>af_unbounded := True\<rparr>) s sp * true
                    * \<up>(sp = length (af_vstack st))"
      unfolding dfs_rel_def by (sep_auto simp: T cLv cLe cLd lvst spLv)
    show ?case
    proof(cases ub)
      case True
      show ?thesis
        unfolding af_close_cycle_imp_def
        by (rule ht_bind[OF cr], rule ht_extract_pre_pure(1), hypsubst, simp only: prod.case cs True if_True)
           (sep_auto, erule entailsD[OF entT_m[OF ubflow[OF True]]])
    next
      case False
      show ?thesis
        unfolding af_close_cycle_imp_def
        by (rule ht_bind[OF cr], rule ht_extract_pre_pure(1), hypsubst, simp only: prod.case cs False if_False)
           (rule ht_bind[OF rst[folded T(5)]], sep_auto, erule entailsD[OF entF_m])
    qed
  qed
qed

text \<open>Two list-encoding rewrites: writing @{term x} at index @{term sp} then taking
      @{term \<open>Suc sp\<close>} appends @{term x} to the reversed stack (the estack/dstack variant needs
      @{term \<open>Suc 0 \<le> sp\<close>}).\<close>
lemma penc_v: "sp < length vl \<Longrightarrow> rev (list_update (take (Suc sp) vl) sp x) = x # rev (take sp vl)"
  by (simp add: take_Suc_conv_app_nth list_update_append)

lemma penc_e:
  "\<lbrakk>Suc 0 \<le> sp; sp < length el\<rbrakk> \<Longrightarrow>
   rev (drop (Suc 0) (list_update (take (Suc sp) el) sp a)) = a # rev (drop (Suc 0) (take sp el))"
  by (simp add: take_Suc_conv_app_nth list_update_append)

text \<open>Fresh-vertex case of @{const af_handle}: push the new vertex. Needs
      @{term \<open>Suc 0 \<le> sp\<close>} (the DFS stack is non-empty --- the root is always on it) so the estack
      / dstack encoding shifts correctly; that premise is discharged at the call site from the @{const AF_DFS} loop
      condition.\<close>
lemma af_push_vertex_imp_rule:
  assumes "st_invar (af_state st)" "x \<in> \<V>" "sp < card \<V>" "Suc 0 \<le> sp"
  shows "<dfs_rel st s sp> af_push_vertex_imp s x a dir sp
   <\<lambda>r. case r of (sp', ubd) \<Rightarrow>
          dfs_rel (st\<lparr>af_vstack := x # af_vstack st, af_state := st_upd (af_state st) x OnStack,
                      af_estack := a # af_estack st, af_dstack := dir # af_dstack st\<rparr>) s sp' *
          \<up>(sp' = Suc sp \<and> \<not> ubd)>"
proof(rule dfs_rel_ht, goal_cases)
  case (1 vl el dl)
  note T = 1
  have svl: "sp < length vl" and sel: "sp < length el" and sdl: "sp < length dl"
    using assms(3) T(1-3) by linarith+
  have cL: "card \<V> \<le> Lvst" "card \<V> \<le> Lest" "card \<V> \<le> Ldst" using T(1-3,8-10) by simp_all
  show ?case
    unfolding af_push_vertex_imp_def dfs_rel_def
    by (sep_auto simp: assms(1-3) penc_v[OF svl] penc_e[OF assms(4) sel] penc_e[OF assms(4) sdl] T cL Suc_le_eq)
qed

text \<open>An @{const Unseen} vertex is off the (distinct) DFS stack,
      so the stack is shorter than @{term \<V>}.\<close>
lemma af_unseen_stack_card:
  "\<lbrakk>AF_invar_2 st; set (af_vstack st) \<subseteq> \<V>; x \<in> \<V>;
    st_lookup (af_state st) x = Unseen\<rbrakk>
   \<Longrightarrow> length (af_vstack st) < card \<V>"
  by (erule AF_invar_2E) (auto simp: distinct_card[symmetric] intro!: psubset_card_mono[OF \<V>_finite])

text \<open>Processing one incident arc: refines @{const af_handle}, threading the new stack pointer and the
      unbounded flag. Premises (agreed design): the bundled DFS invariant @{term \<open>AF_inv st\<close>}, a valid
      free arc @{term \<open>a \<in> \<E>\<close>}, boundedness so far, a non-empty stack, and the
      \<^emph>\<open>orientation\<close> fact that the arc's near endpoint (tail if @{term dir}, head otherwise) is
      the current stack top --- all discharged at the @{const AF_DFS} call site (@{thm af_current_out_endpoint} /
      the @{text \<open>v # vs\<close>} pattern), so none weakens the final
      \<open>make_acyclic_imp_rule\<close>.\<close>
lemma af_handle_imp_rule:
  assumes "AF_inv st" "a \<in> \<E>" "\<not> af_unbounded st" "af_vstack st \<noteq> []"
             "(if dir then fst_exec a else snd_exec a) = hd (af_vstack st)"
  shows "<dfs_rel st s sp> af_handle_imp s a dir sp
   <\<lambda>r. case r of (sp', ubd) \<Rightarrow>
          dfs_rel (af_handle st a dir) s sp' *
          \<up>(sp' = length (af_vstack (af_handle st a dir)) \<and> ubd = af_unbounded (af_handle st a dir))>"
proof(rule dfs_rel_ht, goal_cases)
  case (1 vl el dl)
  note T = 1
  let ?x = "if dir then snd_exec a else fst_exec a"
  have inv1: "AF_invar_1 st" and inv2: "AF_invar_2 st" and vsub: "set (af_vstack st) \<subseteq> \<V>"
    using assms(1) unfolding AF_inv_def by (auto simp: AF_invar_V_def)
  have fi: "flow_invar (af_flow st)" and sti: "st_invar (af_state st)" using inv1 by (auto elim: AF_invar_1_props)
  have xV: "?x \<in> \<V>" using fst_E_V[OF assms(2)] snd_E_V[OF assms(2)]
    by (cases dir) (auto simp: snd_exec_eq[OF assms(2)] fst_exec_eq[OF assms(2)])
  have svl: "sp \<le> length vl" and sel: "sp \<le> length el" using T(1,2,4) by simp_all
  have cL: "card \<V> \<le> Lvst" "card \<V> \<le> Lest" "card \<V> \<le> Ldst" using T(1-3,8-10) by simp_all
  have spLv: "sp \<le> Lvst" using svl T(8) by simp
  have lvst: "length (af_vstack st) = sp" using T(5) svl by simp
  have sp1: "Suc 0 \<le> sp" using assms(4) lvst by (cases "af_vstack st") auto
  have neest: "(af_estack st \<noteq> []) = (2 \<le> sp)" using T(6) sel sp1 by (cases sp) auto
  have hdest: "2 \<le> sp \<Longrightarrow> hd (af_estack st) = el ! (sp - 1)"
    using T(6) sel sp1 by (simp add: hd_rev last_conv_nth take_Suc_conv_app_nth)
  have xhd: "fst_exec a \<noteq> snd_exec a \<Longrightarrow> ?x \<noteq> hd (af_vstack st)"
    using assms(5) by (cases dir) auto
  have spcard: "sp < card \<V>" if "st_lookup (af_state st) ?x = Unseen"
    using af_unseen_stack_card[OF inv2 vsub xV that] lvst by simp
  have fold: "flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s)
                * out_assn (af_out_arr st) (iout s) *
      in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el
        * idstack s \<mapsto>\<^sub>a dl * rd \<Longrightarrow>\<^sub>A dfs_rel st s sp"
    unfolding dfs_rel_def by (sep_auto simp: T cL)
  have ret: "flow_assn (af_flow st') (iflow s) * state_assn (af_state st) (istate s)
               * out_assn (af_out_arr st) (iout s) *
      in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el
        * idstack s \<mapsto>\<^sub>a dl * rd * true \<Longrightarrow>\<^sub>A dfs_rel st' s sp * true"
    if "af_state st' = af_state st" "af_out_arr st' = af_out_arr st" "af_in_arr st' = af_in_arr st"
       "af_vstack st' = af_vstack st" "af_estack st' = af_estack st" "af_dstack st' = af_dstack st" for st'
    unfolding dfs_rel_def by (sep_auto simp: that T cL spLv)
  let ?P = "flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s)
              * out_assn (af_out_arr st) (iout s) *
      in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el
        * idstack s \<mapsto>\<^sub>a dl * rd"
  have F: "<?P> fst_exec_imp a <\<lambda>r. ?P * \<up>(r = fst_exec a)>"
    "<?P> snd_exec_imp a <\<lambda>r. ?P * \<up>(r = snd_exec a)>"
    "<?P> af_rooms_imp s a <\<lambda>r. ?P * \<up>(r = af_rooms (af_flow st) a)>"
    "<?P> st_lookup_imp (istate s) ?x <\<lambda>r. ?P * \<up>(r = st_lookup (af_state st) ?x)>"
    by (sep_auto simp: assms(2) heap: af_rooms_imp_rule[OF fi assms(2)] st_imp.fixed_univ_map_lookup_rule[OF sti xV])+
  have PAR: "<?P> (if 2 \<le> sp then Array.nth (iestack s) (sp - 1) \<bind>
                   (\<lambda>top_e. return (a = top_e)) else return False)
      <\<lambda>r. ?P * \<up>(r = (af_estack st \<noteq> [] \<and> a = hd (af_estack st)))>"
    by (cases "2 \<le> sp") (sep_auto simp: neest hdest sel)+
  have RET: "<?P> return (sp, False)
      <\<lambda>r. case r of (sp', ubd)
        \<Rightarrow> dfs_rel st s sp' * \<up>(sp' = length (af_vstack st) \<and> ubd = af_unbounded st)>"
    by (sep_auto simp: lvst assms(3)) (erule entailsD[rotated], (rule ent_trans[OF _ ret]; sep_auto))
  note PV = ht_cons_pre[OF fold af_push_vertex_imp_rule[OF sti xV spcard sp1]]
  note CC = ht_cons_pre[OF fold af_close_cycle_imp_rule[OF assms(1-3) _ xV xhd sp1]]
  note S = if_True if_False simp_thms prod.sel Let_def vertex_state.case
  note B = ht_bind[OF F(1)] ht_bind[OF F(2)] ht_bind[OF F(3)] ht_bind[OF PAR] ht_bind[OF F(4)] ht_extract_pre_pure(1)
  show ?case
  proof(cases rule: af_handle_cases_exec[where a=a and st=st and dir=dir])
    case blocked
    show ?thesis
      unfolding af_handle_imp_def by ((rule B | hypsubst | simp only: S blocked)+, rule RET)
  next
    case parent
    show ?thesis
      unfolding af_handle_imp_def
      by ((rule B | hypsubst | simp only: S parent(1,2,6) eqTrueI[OF parent(3)] eqTrueI[OF conjI[OF parent(4,5)]])+,
          rule RET)
  next
    case finished
    show ?thesis
      unfolding af_handle_imp_def
      by ((rule B | hypsubst | simp only: S finished(1,2,4-6) eqTrueI[OF finished(3)])+, rule RET)
  next
    case push
    show ?thesis
      unfolding af_handle_imp_def
      by ((rule B | hypsubst | simp only: S push(1,2,4-6) eqTrueI[OF push(3)])+,
          rule ht_cons_post_prec[OF PV[OF push(5)]], sep_auto simp: lvst assms(3))
  next
    case unbounded
    show ?thesis
      unfolding af_handle_imp_def
      by ((rule B | hypsubst | simp only: S unbounded(1,2,4,5,7) eqTrueI[OF unbounded(3)])+)
         (rule ht_cons_post_prec[OF CC[OF unbounded(5)]]; (rule unbounded(1) | sep_auto simp: unbounded(6)))
  next
    case cancel
    show ?thesis
      unfolding af_handle_imp_def
      by ((rule B | hypsubst | simp only: S cancel(1,2,4,5,7) eqTrueI[OF cancel(3)])+)
         (rule ht_cons_post_prec[OF CC[OF cancel(5)]]; (rule cancel(1) | sep_auto simp: cancel(6)))
  next
    case selfloop
    have "<?P> af_selfloop_handle_imp s a <\<lambda>r. flow_assn (af_flow (af_selfloop_handle st a)) (iflow s) *
        state_assn (af_state st) (istate s) * out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) *
        ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd
          * \<up>(r = af_unbounded (af_selfloop_handle st a))>"
      by (sep_auto heap: af_selfloop_handle_imp_rule[OF fi assms(2,3)])
    note SL = ht_bind[OF this]
    show ?thesis
      unfolding af_handle_imp_def
      by ((rule B SL | hypsubst | simp only: S selfloop)+, sep_auto simp: lvst)
         (erule entailsD[rotated], (rule ent_trans[OF _ ret]; sep_auto))


  qed
qed


lemma AF_DFS_impl_simps:
  shows "AF_DFS_call_1_conds st \<Longrightarrow> AF_DFS_impl st = AF_DFS_impl (AF_DFS_upd1 st)"
    and "AF_DFS_call_2_conds st \<Longrightarrow> AF_DFS_impl st = AF_DFS_impl (AF_DFS_upd2 st)"
    and "AF_DFS_call_3_conds st \<Longrightarrow> AF_DFS_impl st = AF_DFS_impl (AF_DFS_upd3 st)"
    and "AF_DFS_ret_conds st \<Longrightarrow> AF_DFS_impl st = st"
  by (subst AF_DFS_impl.simps, auto simp: AF_DFS_call_1_conds_def AF_DFS_upd1_def AF_DFS_call_2_conds_def
      AF_DFS_upd2_def AF_DFS_call_3_conds_def AF_DFS_upd3_def AF_DFS_ret_conds_def Let_def split:
    list.splits if_splits)+

text \<open>The inner DFS loop refines @{const AF_DFS_impl}, by \<^emph>\<open>fixpoint induction\<close> on the heap
      @{command partial_function}. The added premise @{term \<open>multigraph_inv out_arr in_arr\<close>} is the
      standing correctness precondition of the whole acyclic-flow development (the input graph arrays
      genuinely represent the graph); it is what @{thm AF_inv_holds_1} etc. require and is threaded to
      the top. The functional side varies over @{term st} / @{term sp}; the imperative state @{term s}
      is threaded unchanged, matching the in-place recursion @{term \<open>f s sp'\<close>}.\<close>
lemma AF_DFS_imp_rule:
  assumes "multigraph_inv out_arr in_arr" and "AF_inv st" "\<not> af_unbounded st" "sp = length (af_vstack st)"
  shows "<dfs_rel st s sp> AF_DFS_imp s sp <\<lambda>r. (\<exists>\<^sub>A sp'. dfs_rel (AF_DFS_impl st) s sp')
           * \<up>(r = af_unbounded (AF_DFS_impl st))>"
proof -
  have "AF_inv st \<longrightarrow> \<not> af_unbounded st \<longrightarrow> sp = length (af_vstack st)
          \<longrightarrow> <dfs_rel st s sp> AF_DFS_imp s sp <\<lambda>r.
    (\<exists>\<^sub>A sp'. dfs_rel (AF_DFS_impl st) s sp') * \<up>(r = af_unbounded (AF_DFS_impl st))>"
  proof(induction arbitrary: st sp rule: AF_DFS_imp.fixp_induct)
    case (3 f)
    have TAIL: "<dfs_rel st' s (length (af_vstack st'))>
        (if af_unbounded st' then return True else f s (length (af_vstack st')))
        <\<lambda>r. (\<exists>\<^sub>A sp'. dfs_rel (AF_DFS_impl st') s sp')
          * \<up>(r = af_unbounded (AF_DFS_impl st'))>"
      if "AF_inv st'" for st'
    proof(cases "af_unbounded st'")
      case True
      show ?thesis
        by (simp only: True if_True AF_DFS_impl_simps(4)[OF AF_DFS_ret_condsI[OF disjI1[OF True]]]) sep_auto
    qed (simp only: if_False, rule "3.IH"[rule_format, OF that _ refl])
    show ?case
    proof(intro impI, goal_cases)
      case 1
      note I = 1
      show ?case
      proof(cases "sp = 0")
        case sp0: True
        have "AF_DFS_impl st = st" using I(3) sp0 by (simp add: AF_DFS_impl_simps(4)[OF AF_DFS_ret_condsI])
        then show ?thesis by (simp add: sp0) (sep_auto simp: I(2))
      next
        case False
        let ?v = "hd (af_vstack st)"
        have ane: "af_vstack st \<noteq> []" using I(3) False by auto
        have inv1: "AF_invar_1 st" and mi: "multigraph_inv (af_out_arr st) (af_in_arr st)" and vV: "?v \<in> \<V>"
          using I(1) ane unfolding AF_inv_def by (auto simp: AF_invar_iter_def AF_invar_V_def)
        have oti: "out_invar (af_out_arr st)" and iti: "in_invar (af_in_arr st)" and sti: "st_invar (af_state st)"
          using inv1 by (auto elim: AF_invar_1_props)
        show ?thesis
        proof(simp only: if_not_P[OF False], rule dfs_rel_ht, goal_cases)
          case (1 vl el dl)
          note T = 1
          have svl: "sp \<le> length vl" and sel: "sp \<le> length el" and sdl: "sp \<le> length dl"
            using T(1-4) by simp_all
          have cL: "card \<V> \<le> Lvst" "card \<V> \<le> Lest" "card \<V> \<le> Ldst" using T(1-3,8-10) by simp_all
          have vhd: "vl ! (sp - 1) = ?v" using T(5) svl False by (cases sp) (simp_all add: take_Suc_conv_app_nth)
          let ?P = "flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s)
                      * out_assn (af_out_arr st) (iout s) *
            in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el
              * idstack s \<mapsto>\<^sub>a dl * rd"
          have fold: "flow_assn (af_flow st) (iflow s) * state_assn (af_state st) (istate s)
                        * out_assn (af_out_arr st') (iout s) *
              in_assn (af_in_arr st') (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el
                * idstack s \<mapsto>\<^sub>a dl * rd \<Longrightarrow>\<^sub>A dfs_rel st' s sp"
            if "af_flow st' = af_flow st" "af_state st' = af_state st" "af_vstack st' = af_vstack st"
               "af_estack st' = af_estack st" "af_dstack st' = af_dstack st" for st'
            unfolding dfs_rel_def by (sep_auto simp: that T cL)
          have H: "<?P> Array.nth (ivstack s) (sp - 1) <\<lambda>r. ?P * \<up>(r = ?v)>"
            "<?P> out_has_imp (iout s) ?v <\<lambda>r. ?P * \<up>(r = out_has (af_out_arr st) ?v)>"
            "<?P> in_has_imp (iin s) ?v <\<lambda>r. ?P * \<up>(r = in_has (af_in_arr st) ?v)>"
            using svl False vhd by (sep_auto heap: out_imp.idx_has_rule[OF oti vV] in_imp.idx_has_rule[OF iti vV])+
          note B = ht_bind[OF H(1)] ht_bind[OF H(2)] ht_bind[OF H(3)] ht_extract_pre_pure(1)
          show ?case
          proof(cases "out_has (af_out_arr st) ?v")
            case oh: True
            let ?a = "out_current (af_out_arr st) ?v"
              and ?so = "st\<lparr>af_out_arr := out_move (af_out_arr st) ?v\<rparr>"
            have ne: "out_remaining (af_out_arr st) ?v \<noteq> {}" using outg.idx_has[OF oti vV] oh by simp
            have call: "AF_DFS_call_1_conds st" using I(2) ane oh
              by (cases "af_vstack st") (auto simp: AF_DFS_call_1_conds_def)
            have aE: "?a \<in> \<E>" and ori: "(if True then fst_exec ?a else snd_exec ?a) = hd (af_vstack ?so)"
              using af_current_out_endpoint[OF mi vV oh] fst_exec_eq by auto
            have "AF_inv ?so" "\<not> af_unbounded ?so" "af_vstack ?so \<noteq> []"
              using I(1,2) ane AF_invar_1_out_advance[OF vV inv1] multigraph_inv_out_advance[OF mi oh vV] vV
              by (auto simp: AF_inv_def AF_invar_iter_def)
            note AH = ht_cons_pre[OF fold[of ?so, simplified] af_handle_imp_rule[OF this(1) aE this(2,3) ori]]
            have C: "<?P> out_current_imp (iout s) ?v <\<lambda>r. ?P * \<up>(r = ?a)>"
              "<?P> out_move_imp (iout s) ?v <\<lambda>_. flow_assn (af_flow st) (iflow s)
                 * state_assn (af_state st) (istate s) *
                 out_assn (out_move (af_out_arr st) ?v) (iout s) * in_assn (af_in_arr st) (iin s) *
                 ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el
                   * idstack s \<mapsto>\<^sub>a dl * rd>"
              by (sep_auto heap: out_imp.idx_current_rule[OF oti vV ne] out_imp.idx_move_rule[OF oti vV ne])+
            show ?thesis
              by (simp only: AF_DFS_impl_simps(1)[OF call] AF_DFS_upd1_def Let_def)
                 ((rule B ht_bind[OF C(1)] ht_bind[OF C(2)] ht_bind[OF AH] | erule conjE | hypsubst
                  | simp only: oh if_True split_paired_all prod.case)+,
                  rule TAIL[OF AF_inv_holds_1[OF assms(1) call I(1)], unfolded AF_DFS_upd1_def Let_def])
          next
            case noh: False
            show ?thesis
            proof(cases "in_has (af_in_arr st) ?v")
              case ih: True
              let ?a = "in_current (af_in_arr st) ?v"
                and ?si = "st\<lparr>af_in_arr := in_move (af_in_arr st) ?v\<rparr>"
              have ne: "in_remaining (af_in_arr st) ?v \<noteq> {}" using ing.idx_has[OF iti vV] ih by simp
              have call: "AF_DFS_call_2_conds st" using I(2) ane noh ih
                by (cases "af_vstack st") (auto simp: AF_DFS_call_2_conds_def)
              have aE: "?a \<in> \<E>" and ori: "(if False then fst_exec ?a else snd_exec ?a) = hd (af_vstack ?si)"
                using af_current_in_endpoint[OF mi vV ih] snd_exec_eq by auto
              have "AF_inv ?si" "\<not> af_unbounded ?si" "af_vstack ?si \<noteq> []"
                using I(1,2) ane AF_invar_1_in_advance[OF vV inv1] multigraph_inv_in_advance[OF mi ih] vV
                by (auto simp: AF_inv_def AF_invar_iter_def)
              note AH = ht_cons_pre[OF fold[of ?si, simplified] af_handle_imp_rule[OF this(1) aE this(2,3) ori]]
              have C: "<?P> in_current_imp (iin s) ?v <\<lambda>r. ?P * \<up>(r = ?a)>"
                "<?P> in_move_imp (iin s) ?v <\<lambda>_. flow_assn (af_flow st) (iflow s)
                   * state_assn (af_state st) (istate s) *
                   out_assn (af_out_arr st) (iout s) * in_assn (in_move (af_in_arr st) ?v) (iin s) *
                   ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el
                     * idstack s \<mapsto>\<^sub>a dl * rd>"
                by (sep_auto heap: in_imp.idx_current_rule[OF iti vV ne] in_imp.idx_move_rule[OF iti vV ne])+
              show ?thesis
                by (simp only: AF_DFS_impl_simps(2)[OF call] AF_DFS_upd2_def Let_def)
                   ((rule B ht_bind[OF C(1)] ht_bind[OF C(2)] ht_bind[OF AH] | erule conjE | hypsubst
                    | simp only: noh ih if_True if_False split_paired_all prod.case)+,
                    rule TAIL[OF AF_inv_holds_2[OF assms(1) call I(1)], unfolded AF_DFS_upd2_def Let_def])
            next
              case nih: False
              have call: "AF_DFS_call_3_conds st" using I(2) ane noh nih
                by (cases "af_vstack st") (auto simp: AF_DFS_call_3_conds_def)
              have "sp - Suc 0 \<le> card \<V>" using T(4) by arith
              moreover have "tl (af_vstack st) = rev (take (sp - 1) vl)"
                "tl (af_estack st) = rev (drop (Suc 0) (take (sp - 1) el))"
                "tl (af_dstack st) = rev (drop (Suc 0) (take (sp - 1) dl))"
                using T(5-7) svl sel sdl by (simp_all add: tl_rev butlast_take butlast_drop drop_take)
              ultimately have pop: "flow_assn (af_flow st) (iflow s)
                                      * state_assn (st_upd (af_state st) ?v Finished) (istate s) *
                  out_assn (af_out_arr st) (iout s) * in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl
                    * iestack s \<mapsto>\<^sub>a el *
                  idstack s \<mapsto>\<^sub>a dl * rd \<Longrightarrow>\<^sub>A dfs_rel (AF_DFS_upd3 st) s (sp - 1)"
                unfolding dfs_rel_def AF_DFS_upd3_def by (sep_auto simp: T(1-3,8-10) cL)
              have U: "<?P> st_upd_imp (istate s) ?v Finished <\<lambda>_. flow_assn (af_flow st) (iflow s) *
                  state_assn (st_upd (af_state st) ?v Finished) (istate s) * out_assn (af_out_arr st) (iout s) *
                  in_assn (af_in_arr st) (iin s) * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el
                    * idstack s \<mapsto>\<^sub>a dl * rd>"
                by (sep_auto heap: st_imp.fixed_univ_map_upd_rule[OF sti vV])
              have "\<not> af_unbounded (AF_DFS_upd3 st)" "sp - 1 = length (af_vstack (AF_DFS_upd3 st))"
                using I(2,3) unfolding AF_DFS_upd3_def by simp_all
              note IH = "3.IH"[rule_format, OF AF_inv_holds_3[OF call I(1)] this]
              show ?thesis
                by (simp only: AF_DFS_impl_simps(3)[OF call])
                   ((rule B ht_bind[OF U] | hypsubst | simp only: noh nih if_False)+, rule ht_cons_pre[OF pop IH])
            qed
          qed
        qed
      qed
    qed
  qed simp_all
  from this[rule_format, OF assms(2-4)] show ?thesis .
qed

text \<open>Launching the inner DFS from a fresh vertex. Beyond the store invariants, the caller supplies the
      standing @{term \<open>multigraph_inv out_arr in_arr\<close>} (reset target of @{const AF_DFS_imp}), the launch
      graph's @{term \<open>multigraph_inv OG IG\<close>}, capacity-feasibility of the seed flow, and that no vertex is
      @{const OnStack} in the seed state --- exactly the \<open>AF_inv_initial\<close> hypotheses, all maintained
      by the outer loop's @{const AFF_inv}.\<close>
lemma af_dfs_start_imp_rule:
  assumes "flow_invar Fl" and "st_invar St" and "out_invar OG" and "in_invar IG" and "v \<in> \<V>"
    and "multigraph_inv out_arr in_arr" and "multigraph_inv OG IG" and "af_cap_feasible Fl"
    and "\<forall>w\<in>\<V>. st_lookup St w \<noteq> OnStack"
    and "card \<V> \<le> length vl" and "card \<V> \<le> length el" and "card \<V> \<le> length dl"
    and "length vl = Lvst" and "length el = Lest" and "length dl = Ldst"
  shows "<flow_assn Fl (iflow s) * state_assn St (istate s) * out_assn OG (iout s) * in_assn IG (iin s)
           * ivstack s \<mapsto>\<^sub>a vl * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl
    * rd> af_dfs_start_imp s v <\<lambda>r.
    (\<exists>\<^sub>A sp'. dfs_rel (AF_DFS_impl (AF_DFS_initial Fl OG IG St v)) s sp')
    * \<up>(r = af_unbounded (AF_DFS_impl (AF_DFS_initial Fl OG IG St v)))>"
proof -
  have "\<not> af_unbounded (AF_DFS_initial Fl OG IG St v)" "1 = length (af_vstack (AF_DFS_initial Fl OG IG St v))"
    by (simp_all add: AF_DFS_initial_def)
  note R = AF_DFS_imp_rule[OF assms(6) AF_inv_initial[OF assms(1-4,7,5,8,9)] this]
  have "0 < card \<V>" using assms(5) \<V>_finite by (auto simp: card_gt_0_iff)
  then have vlne: "vl \<noteq> []" and "Suc 0 \<le> card \<V>"
    and "list_update (take (Suc 0) vl) 0 v = [v]" using assms(10)
    by (cases vl; auto)+
  then have "flow_assn Fl (iflow s) * state_assn (st_upd St v OnStack) (istate s) * out_assn OG (iout s)
               * in_assn IG (iin s) *
      ivstack s \<mapsto>\<^sub>a list_update vl 0 v * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl
        * rd \<Longrightarrow>\<^sub>A dfs_rel (AF_DFS_initial Fl OG IG St v) s 1"
    unfolding dfs_rel_def AF_DFS_initial_def
      by (sep_auto simp: assms(10-15) assms(10)[unfolded assms(13)] assms(11)[unfolded assms(14)]
          assms(12)[unfolded assms(15)])
  from ht_cons_pre[OF this R] show ?thesis
    unfolding af_dfs_start_imp_def by (sep_auto heap: st_imp.fixed_univ_map_upd_rule[OF assms(2,5)] simp: vlne)
qed

text \<open>\<^emph>\<open>partial\_function = domintro bridges.\<close> The executable @{const AF_DFS_impl} /
      @{const AF_outer_impl} (the @{command partial_function} fixpoints, registered as code equations) coincide
      with the totally-defined domintro functions @{const AF_DFS} / @{const AF_outer} on their domains. These are
      what connect the imperative refinement (which mirrors the \<open>_impl\<close> recursion) to the functional
      correctness development (stated for the domintro versions, e.g.\ \<open>AFF_inv_holds_2\<close>).\<close>
lemma AF_DFS_impl_eq:
  "\<lbrakk>multigraph_inv out_arr in_arr; AF_inv st\<rbrakk> \<Longrightarrow> AF_DFS_impl st = AF_DFS st"
proof(rule AF_DFS_induct[where P = "\<lambda>st. AF_DFS_impl st = AF_DFS st", OF AF_DFS_dom], assumption+, goal_cases)
  case (1 st)
  then show ?case by (cases rule: AF_DFS_cases[of st]) (simp_all add: AF_DFS_impl_simps AF_DFS_simps AF_DFS_ret_def)
qed

lemma AF_outer_impl_simps1:
  "AF_outer_call_1_conds st \<Longrightarrow> AF_outer_impl st = AF_outer_impl (AF_outer_upd1 st)"
  by (subst AF_outer_impl.simps) (auto simp: AF_outer_call_1_conds_def AF_outer_upd1_def Let_def)

lemma AF_outer_impl_simps2:
  "\<lbrakk>multigraph_inv out_arr in_arr; AF_outer_call_2_conds st; AFF_inv st\<rbrakk>
   \<Longrightarrow> AF_outer_impl st = AF_outer_impl (AF_outer_upd2 st)"
  by (subst AF_outer_impl.simps)
     (auto simp: AF_DFS_impl_eq[OF _ AF_outer_launch(1)] AF_outer_call_2_conds_def AF_outer_upd2_def Let_def)

lemma AF_outer_impl_simps_ret: "AF_outer_ret_conds st \<Longrightarrow> AF_outer_impl st = st"
  by (subst AF_outer_impl.simps) (auto simp: AF_outer_ret_conds_def Let_def split: if_splits)

lemma AF_outer_impl_eq:
  assumes "multigraph_inv out_arr in_arr" and "AFF_inv st"
  shows "AF_outer_impl st = AF_outer st"
  using assms(2)
proof(induction rule: AF_outer_induct[OF AF_outer_dom[OF assms]])
  case (1 st)
  show ?case
    by (rule AF_outer_cases[of st]; simp only: 1 assms(1) AF_outer_impl_simps1 AF_outer_impl_simps2
          AF_outer_impl_simps_ret AF_outer_simps AF_outer_ret_def AFF_inv_holds_1 AFF_inv_holds_2 simp_thms)
qed

text \<open>The outer loop over vertices refines @{const AF_outer_impl}. The added premise
      @{term \<open>multigraph_inv out_arr in_arr\<close>} is the standing correctness precondition threaded from the
      top (as for @{thm AF_DFS_imp_rule}); it is exactly what @{thm AFF_inv_holds_1} / @{thm AFF_inv_holds_2}
      require and is discharged at @{const make_acyclic_imp} via @{thm AFF_inv_initial}.\<close>
lemma AF_outer_imp_rule:
  assumes "multigraph_inv out_arr in_arr" and "AFF_inv st" "\<not> aff_unbounded st"
  shows "<outer_rel st s> AF_outer_imp s <\<lambda>r. outer_rel (AF_outer_impl st) s
           * \<up>(r = aff_unbounded (AF_outer_impl st))>"
proof -
  have "AFF_inv st \<longrightarrow> \<not> aff_unbounded st
          \<longrightarrow> <outer_rel st s> AF_outer_imp s <\<lambda>r. outer_rel (AF_outer_impl st) s
    * \<up>(r = aff_unbounded (AF_outer_impl st))>"
  proof(induction arbitrary: st rule: AF_outer_imp.fixp_induct)
    case (3 f)
    show ?case
    proof(intro impI, goal_cases)
      case 1
      note I = 1
      have vinv: "vit_invar (aff_vit st)" and ffi: "flow_invar (aff_flow st)" and sti: "st_invar (aff_state st)"
        and aoi: "out_invar (aff_out_arr st)" and aii: "in_invar (aff_in_arr st)"
          and feas: "af_cap_feasible (aff_flow st)"
        and mii: "multigraph_inv (aff_out_arr st) (aff_in_arr st)"
          and noos: "\<forall>w\<in>\<V>. st_lookup (aff_state st) w \<noteq> OnStack"
        using I by (auto simp: AFF_inv_def)
      show ?case
      proof(rule outer_rel_ht, goal_cases)
        case (1 vl el dl)
        note T = 1 1(1)[unfolded 1(4)] 1(2)[unfolded 1(5)] 1(3)[unfolded 1(6)]
        let ?P = "flow_assn (aff_flow st) (iflow s) * state_assn (aff_state st) (istate s)
                    * out_assn (aff_out_arr st) (iout s) *
          in_assn (aff_in_arr st) (iin s) * vit_assn (aff_vit st) (ivit s) * ivstack s \<mapsto>\<^sub>a vl
            * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd"
        have HV: "<?P> has_vertex_imp (ivit s) <\<lambda>r. ?P * \<up>(r = has_vertex (aff_vit st))>"
          by (sep_auto heap: has_vertex_rule[OF vinv])
        note S = simp_thms if_True if_False
        show ?case
        proof(cases "has_vertex (aff_vit st)")
          case False
          have impl: "AF_outer_impl st = st" using False by (simp add: AF_outer_impl_simps_ret AF_outer_ret_conds_def)
          have fold: "?P \<Longrightarrow>\<^sub>A outer_rel st s" unfolding outer_rel_def by (sep_auto simp: T)
          show ?thesis
            by (simp only: impl) ((rule ht_bind[OF HV] ht_extract_pre_pure(1) | hypsubst | simp only: S False)+,
                rule ht_cons_pre[OF fold], sep_auto simp: I(2))
        next
          case hv: True
          let ?v = "current_vertex (aff_vit st)" and ?mv = "move_on_vertex (aff_vit st)"
          have ne: "vit_remaining (aff_vit st) \<noteq> {}" using hv vinv vertex_iterator.has_current by auto
          have vV: "?v \<in> \<V>" using vit_current_V[OF I(1) hv] .
          let ?P1 = "flow_assn (aff_flow st) (iflow s) * state_assn (aff_state st) (istate s)
                       * out_assn (aff_out_arr st) (iout s) *
            in_assn (aff_in_arr st) (iin s) * vit_assn ?mv (ivit s) * ivstack s \<mapsto>\<^sub>a vl
              * iestack s \<mapsto>\<^sub>a el * idstack s \<mapsto>\<^sub>a dl * rd"
          have C: "<?P> current_vertex_imp (ivit s) <\<lambda>r. ?P * \<up>(r = ?v)>"
            "<?P> move_on_vertex_imp (ivit s) <\<lambda>_. ?P1>"
            "<?P1> st_lookup_imp (istate s) ?v <\<lambda>r. ?P1 * \<up>(r = st_lookup (aff_state st) ?v)>"
            by (sep_auto heap: current_vertex_rule[OF vinv ne] move_on_vertex_rule[OF vinv ne]
                               st_imp.fixed_univ_map_lookup_rule[OF sti vV])+
          note B = ht_bind[OF HV] ht_bind[OF C(1)] ht_bind[OF C(2)] ht_bind[OF C(3)] ht_extract_pre_pure(1)
          show ?thesis
          proof(cases "st_lookup (aff_state st) ?v = Unseen")
            case False
            have call: "AF_outer_call_1_conds st" using I(2) hv False by (simp add: AF_outer_call_1_conds_def)
            have "\<not> aff_unbounded (AF_outer_upd1 st)" using I(2) by (simp add: AF_outer_upd1_def)
            note IH = "3.IH"[rule_format, OF AFF_inv_holds_1[OF call I(1)] this]
            show ?thesis
              by (simp only: AF_outer_impl_simps1[OF call])
                 ((rule B | hypsubst | simp only: S hv False)+, rule ht_cons_pre[OF _ IH],
                  unfold outer_rel_def AF_outer_upd1_def, sep_auto simp: T)
          next
            case True
            have call: "AF_outer_call_2_conds st" using I(2) hv True by (simp add: AF_outer_call_2_conds_def)
            let ?res = "AF_DFS_impl (AF_DFS_initial (aff_flow st) (aff_out_arr st) (aff_in_arr st) (aff_state st) ?v)"
            have st2: "AF_outer_upd2 st = st\<lparr>aff_vit := ?mv, aff_flow := af_flow ?res,
                         aff_state := af_state ?res,
                aff_out_arr := af_out_arr ?res, aff_in_arr := af_in_arr ?res,
                  aff_unbounded := af_unbounded ?res\<rparr>"
              using AF_DFS_impl_eq[OF assms(1) AF_outer_launch(1)[OF assms(1) call I(1)]]
                by (simp add: AF_outer_upd2_def Let_def)
            have FD: "(\<exists>\<^sub>A sp'. dfs_rel ?res s sp')
                        * vit_assn ?mv (ivit s) \<Longrightarrow>\<^sub>A outer_rel (AF_outer_upd2 st) s"
              unfolding dfs_rel_def outer_rel_def st2 by sep_auto
            have D: "<?P1> af_dfs_start_imp s ?v <\<lambda>r. (\<exists>\<^sub>A sp'. dfs_rel ?res s sp')
                       * vit_assn ?mv (ivit s) * \<up>(r = af_unbounded ?res)>"
              by (rule ht_cons_prec[OF _ _ ht_frame[OF
                  af_dfs_start_imp_rule[OF ffi sti aoi aii vV assms(1) mii feas noos T(1-6)], where R
                = "vit_assn ?mv (ivit s)"]])
                 sep_auto+
            have TL: "<(\<exists>\<^sub>A sp'. dfs_rel ?res s sp')
                        * vit_assn ?mv (ivit s)> (if af_unbounded ?res then return True else f s)
                <\<lambda>r. outer_rel (AF_outer_impl (AF_outer_upd2 st)) s
                  * \<up>(r = aff_unbounded (AF_outer_impl (AF_outer_upd2 st)))>"
            proof(cases "af_unbounded ?res")
              case ub: True
              have impl: "AF_outer_impl (AF_outer_upd2 st) = AF_outer_upd2 st"
                using ub by (simp add: AF_outer_impl_simps_ret AF_outer_ret_conds_def st2)
              show ?thesis by (simp only: ub if_True impl) (rule ht_cons_pre[OF FD], sep_auto simp: st2 ub)
            next
              case ub: False
              have nub: "\<not> aff_unbounded (AF_outer_upd2 st)" using ub by (simp add: st2)
              show ?thesis
                by (simp only: ub if_False) (rule
                    ht_cons_pre[OF FD "3.IH"[rule_format, OF AFF_inv_holds_2[OF assms(1) call I(1)] nub]])
            qed
            show ?thesis
              by (simp only: AF_outer_impl_simps2[OF assms(1) call I(1)])
                 ((rule B ht_bind[OF D] | hypsubst | simp only: S hv True)+, rule TL)
          qed
        qed
      qed
    qed
  qed simp_all
  thus ?thesis using assms(2-3) by simp
qed

text \<open>\<^emph>\<open>Target theorem.\<close> If the eight input handles / arrays refine the functional input
      stores, then @{const make_acyclic_imp} leaves the flow store representing the functional
      @{const make_acyclic} result and returns @{term True} exactly for the unbounded (@{term None}) verdict ---
      i.e.\ the final imperative structures refine the final functional ones.\<close>
lemma make_acyclic_imp_rule:
  assumes "multigraph_inv out_arr in_arr" and "flow_invar f0" and "af_cap_feasible f0"
    and "vit_invar all_vertices" and "vit_abstract all_vertices \<subseteq> \<V>"
    and "card \<V> \<le> length vs0" and "card \<V> \<le> length es0" and "card \<V> \<le> length ds0"
    and "length vs0 = Lvst" and "length es0 = Lest" and "length ds0 = Ldst"
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
        \<up>((r \<longleftrightarrow> make_acyclic f0 = None)
              \<and> (make_acyclic f0 = None \<or> make_acyclic f0 = Some f'))>"
proof -
  have I: "AFF_inv (AF_outer_initial f0)" "\<not> aff_unbounded (AF_outer_initial f0)"
    using AFF_inv_initial[OF assms(1-5)] by (simp_all add: AF_outer_initial_def)
  note E = AF_outer_impl_eq[OF assms(1) I(1), symmetric]
  have mk: "make_acyclic f0 = (if aff_unbounded (AF_outer_impl (AF_outer_initial f0)) then None
      else Some (aff_flow (AF_outer_impl (AF_outer_initial f0))))"
    by (simp add: make_acyclic_def E Let_def)
  have fold: "flow_assn f0 fh * state_assn state_init sh * out_assn out_arr oh * in_assn in_arr ih
                * vit_assn all_vertices vih * rd *
      vst \<mapsto>\<^sub>a vs0 * est \<mapsto>\<^sub>a es0
        * dst \<mapsto>\<^sub>a ds0 \<Longrightarrow>\<^sub>A outer_rel (AF_outer_initial f0)
        (af_impl_state_init fh sh oh ih vih vst est dst)"
    unfolding outer_rel_def AF_outer_initial_def af_impl_state_init_def
    by (sep_auto simp: assms(6-11) assms(6)[unfolded assms(9)] assms(7)[unfolded assms(10)]
        assms(8)[unfolded assms(11)])
  show ?thesis
    unfolding make_acyclic_imp_def
    by (rule ht_cons_prec[OF fold _ AF_outer_imp_rule[OF assms(1) I]], unfold E outer_rel_def af_impl_state_init_def,
        rule ent_ex_postI[where x = "aff_flow (AF_outer_impl (AF_outer_initial f0))"])
       (sep_auto simp: mk assms(6-11) assms(6)[unfolded assms(9)] assms(7)[unfolded assms(10)]
        assms(8)[unfolded assms(11)])
qed

end

end
