theory Network_Simplex_Refinement
  imports Mincost_Flow_Algorithms.Network_Simplex_Final Data_Structures.Fixed_Univ_Map_Specs_Imp
          Separation_Logic_Imperative_HOL_Partial.Array_Blit
begin

section \<open>Imperative refinement of the network simplex loop\<close>

text \<open>This theory mirrors the functional specification locale @{locale network_simplex_spec}, but
      every store, tree, selector and descriptor is now a \<^emph>\<open>mutable heap object\<close>: edges, vertices,
      booleans, the numeric flow/residual values and the two real descriptors (potential @{typ 'p},
      reduced cost @{typ 'r}) are all @{class heap} data living in mutable arrays / references, and
      every operation is lifted into the @{typ \<open>_ Heap\<close>} monad. Every fixed operation and every
      derived constant carries an @{text \<open>_imp\<close>} suffix, so that this locale can later be combined with
      the functional locales without name clashes.

      The refinement discipline is the standard Imperative-HOL one:
      \<^item> a functional operation that \<^emph>\<open>changes and returns\<close> a data structure (an array update, a tree
        swap) becomes an in-place mutation whose result type is @{typ \<open>unit Heap\<close>} --- the structure is
        changed but \<^emph>\<open>not returned\<close>;
      \<^item> a functional operation that returns \<^emph>\<open>both a proper value and a changed container\<close> (the
        selector) drops the container from the returned tuple --- it is mutated in place --- and returns
        only the value(s) in the @{typ \<open>_ Heap\<close>} monad;
      \<^item> a functional operation that \<^emph>\<open>computes a value\<close> (a lookup, an endpoint projection, a
        descriptor combination) returns that value in the @{typ \<open>_ Heap\<close>} monad;
      \<^item> pure arithmetic on values already read out of the heap stays pure.

      The program state gains \<^emph>\<open>two extra variables\<close> @{term ipath1}, @{term ipath2}: mutable arrays
      into which the fundamental-circuit path search writes its two vertex paths. The path search
      therefore no longer returns two lists but two natural-number \<^emph>\<open>pointers\<close> @{term \<open>(ptr1, ptr2)\<close>};
      the intended contract (used, never assumed here --- the properties belong to the proof locale) is
      that the first @{term ptr1} / @{term ptr2} entries of @{term ipath1} / @{term ipath2} hold the
      vertices of the functional lists @{term p1} / @{term p2}.

      This locale fixes only the imperative operations; it states \<^emph>\<open>no assumptions\<close>. Every text below
      is a description of how the fixed imperative function is meant to be used, not an axiom.\<close>

subsection \<open>The imperative program state\<close>

text \<open>The mutable program state. The seven stores of the functional program state become handles to
      heap objects (mutated in place, so the handles are threaded unchanged), plus the two path arrays
      @{term ipath1}, @{term ipath2}. The termination flag is not stored: the loop simply \<^emph>\<open>returns\<close> a
      @{typ return} value.\<close>

record ('farr, 'parr, 'arbor, 'pearr, 'darr, 'earr, 'sel, 'a::heap) ns_impl_state =
  iflow    :: 'farr      \<comment> \<open>current flow store\<close>
  ipot     :: 'parr      \<comment> \<open>vertex-potential store\<close>
  itree    :: 'arbor     \<comment> \<open>spanning-tree structure\<close>
  iparent  :: 'pearr     \<comment> \<open>parent-edge store (over @{term \<open>V - {r}\<close>})\<close>
  idir     :: 'darr      \<comment> \<open>parent-edge orientation store\<close>
  iestate  :: 'earr      \<comment> \<open>edge-tag store (InTree / InL / InU)\<close>
  isel     :: 'sel       \<comment> \<open>entering-edge selector\<close>
  ipath1   :: "'a array" \<comment> \<open>path buffer 1\<close>
  ipath2   :: "'a array" \<comment> \<open>path buffer 2\<close>

subsection \<open>The specification locale of the imperative operations\<close>

text \<open>@{term sel_select_imp} runs the selector on the current potentials and edge tags: it mutates
      the selector in place (so the functional @{term sel'} is dropped from the returned tuple) and
      returns @{term None} (optimal) or @{term \<open>Some (e, in_U, \<gamma>)\<close>} --- an entering edge, its
      @{term U}/@{term L} flag and its reduced cost descriptor.

      @{term shift_pot_imp} shifts every potential in the subtree opposed to the root at @{term v} by
      the reduced-cost descriptor @{term \<gamma>} --- added when the flag holds, else subtracted --- in place on
      the potential store. It is a \<^emph>\<open>dedicated first-order traversal\<close>: the subtree walk, the
      descriptor arithmetic and the per-vertex potential read/write are fused into this one primitive,
      so \<^emph>\<open>nothing higher-order (no callback / closure) is applied per vertex\<close>. This is why the
      potential descriptor @{typ 'p} and the separate @{text \<open>pot_*_imp\<close>} / @{text \<open>pot_value_*_imp\<close>}
      operations no longer appear --- they are now internal to the concrete shift.

      @{term get_path_pair_imp} searches the two tree paths of the fundamental circuit of
      @{term \<open>(u, v)\<close>}, writing the vertex paths into the two supplied arrays and returning the two
      fill pointers.

      @{term swap_edge_imp} swaps a tree edge in place. The @{text \<open>_upd_imp\<close>} stores mutate in place;
      the @{text \<open>_lookup_imp\<close>} stores read a value. @{term cap_imp} reads an edge capacity
      (@{term \<open>- 1\<close>} = {\isasyminfinity}). @{term fst_exec_imp} / @{term snd_exec_imp} read the endpoints of an edge.\<close>

locale network_simplex_impl_spec =
  fixes r :: "'a::heap"
    and sel_select_imp :: "'sel \<Rightarrow> 'parr \<Rightarrow> 'earr \<Rightarrow> ('edge \<times> bool \<times> 'r) option Heap"
    and shift_pot_imp :: "'arbor \<Rightarrow> 'a \<Rightarrow> 'parr \<Rightarrow> 'r \<Rightarrow> bool \<Rightarrow> unit Heap"
    and get_path_pair_imp :: "'arbor \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a array \<Rightarrow> 'a array \<Rightarrow> (nat \<times> nat) Heap"
    and swap_edge_imp :: "'arbor \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> unit Heap"
    and flow_upd_imp :: "'farr \<Rightarrow> 'edge \<Rightarrow> 'n::linordered_idom \<Rightarrow> unit Heap"
    and flow_lookup_imp :: "'farr \<Rightarrow> 'edge \<Rightarrow> 'n Heap"
    and parent_upd_imp :: "'pearr \<Rightarrow> 'a \<Rightarrow> 'edge \<Rightarrow> unit Heap"
    and parent_lookup_imp :: "'pearr \<Rightarrow> 'a \<Rightarrow> 'edge Heap"
    and dir_upd_imp :: "'darr \<Rightarrow> 'a \<Rightarrow> bool \<Rightarrow> unit Heap"
    and dir_lookup_imp :: "'darr \<Rightarrow> 'a \<Rightarrow> bool Heap"
    and es_upd_imp :: "'earr \<Rightarrow> 'edge \<Rightarrow> edge_tag \<Rightarrow> unit Heap"
    and es_lookup_imp :: "'earr \<Rightarrow> 'edge \<Rightarrow> edge_tag Heap"
    and cap_imp :: "'edge \<Rightarrow> 'n Heap"
    and fst_exec_imp :: "'edge \<Rightarrow> 'a Heap"
    and snd_exec_imp :: "'edge \<Rightarrow> 'a Heap"
begin

subsection \<open>Reading the state and residual capacities\<close>

text \<open>Run the entering-edge selector on the current potentials and edge tags.\<close>
definition "ns_select_imp s = sel_select_imp (isel s) (ipot s) (iestate s)"

text \<open>Forward residual (remaining capacity) and backward residual (current flow) of a graph edge,
      as reals with @{term \<open>- 1\<close>} standing for {\isasyminfinity} (only the forward residual can be infinite).\<close>
definition "res_fwd_imp s a =
  do { c \<leftarrow> cap_imp a;
       if c = - 1 then return (- 1)
       else do { f \<leftarrow> flow_lookup_imp (iflow s) a; return (c - f) } }"
definition "res_bwd_imp s a = flow_lookup_imp (iflow s) a"

subsection \<open>Parent edges and their residuals\<close>

definition "par_edge_imp s v = parent_lookup_imp (iparent s) v"
definition "par_up_imp s v = dir_lookup_imp (idir s) v"

text \<open>Residual of @{term v}'s parent edge, traversed upward (@{term res_up_imp}) resp. downward
      (@{term res_down_imp}). Upward traversal is forward exactly when the edge natively points to the
      parent.\<close>
definition "res_up_imp s v =
  do { up \<leftarrow> par_up_imp s v; e \<leftarrow> par_edge_imp s v; if up then res_fwd_imp s e else res_bwd_imp s e }"
definition "res_down_imp s v =
  do { up \<leftarrow> par_up_imp s v; e \<leftarrow> par_edge_imp s v; if up then res_bwd_imp s e else res_fwd_imp s e }"

subsection \<open>Bottleneck (in-place, over the two path arrays)\<close>

text \<open>Minimum of two residuals under the @{term \<open>- 1\<close>} = {\isasyminfinity} convention --- pure, on values already read.\<close>
definition "mininf_imp (x::'n) y =
  (if x = - 1 then y else if y = - 1 then x else min x y)"

text \<open>Scan a path-array prefix @{term \<open>[0..<ptr]\<close>} bottom-up. @{term scan_up_loop_imp} keeps the
      \<^emph>\<open>last\<close> minimiser (via @{text \<open>\<le>\<close>}), @{term scan_down_loop_imp} the \<^emph>\<open>first\<close> (via @{text \<open><\<close>}).
      The running minimum @{term m} and its child vertex @{term best} are threaded as \<^emph>\<open>two flat
      arguments\<close> --- no option, no per-step pair --- with @{term \<open>m = - 1\<close>} as the ``nothing seen yet''
      sentinel (so @{term best}, seeded with the dummy @{term r}, is meaningful only once
      @{term \<open>m \<noteq> - 1\<close>}). No intermediate list is built.\<close>
partial_function (heap) scan_up_loop_imp ::
  "('farr, 'parr, 'arbor, 'pearr, 'darr, 'earr, 'sel, 'a) ns_impl_state
     \<Rightarrow> 'a array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'n \<Rightarrow> 'a \<Rightarrow> ('n \<times> 'a) Heap" where
  "scan_up_loop_imp s pa i ptr m best =
     (if ptr \<le> i then return (m, best)
      else do {
        v \<leftarrow> Array.nth pa i;
        rr \<leftarrow> res_up_imp s v;
        (if rr = - 1 then scan_up_loop_imp s pa (i + 1) ptr m best
         else if m = - 1 then scan_up_loop_imp s pa (i + 1) ptr rr v
         else if rr \<le> m then scan_up_loop_imp s pa (i + 1) ptr rr v
         else scan_up_loop_imp s pa (i + 1) ptr m best)
      })"

partial_function (heap) scan_down_loop_imp ::
  "('farr, 'parr, 'arbor, 'pearr, 'darr, 'earr, 'sel, 'a) ns_impl_state
     \<Rightarrow> 'a array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'n \<Rightarrow> 'a \<Rightarrow> ('n \<times> 'a) Heap" where
  "scan_down_loop_imp s pa i ptr m best =
     (if ptr \<le> i then return (m, best)
      else do {
        v \<leftarrow> Array.nth pa i;
        rr \<leftarrow> res_down_imp s v;
        (if rr = - 1 then scan_down_loop_imp s pa (i + 1) ptr m best
         else if m = - 1 then scan_down_loop_imp s pa (i + 1) ptr rr v
         else if rr < m then scan_down_loop_imp s pa (i + 1) ptr rr v
         else scan_down_loop_imp s pa (i + 1) ptr m best)
      })"

definition "scan_up_imp s pa ptr = scan_up_loop_imp s pa 0 ptr (- 1) r"
definition "scan_down_imp s pa ptr = scan_down_loop_imp s pa 0 ptr (- 1) r"

text \<open>The bottleneck of the fundamental circuit of the entering edge @{term e}, over the two path
      arrays (their prefixes @{term ptr1}, @{term ptr2}). For an edge in @{term L} (@{term \<open>\<not> in_U\<close>})
      the @{term \<open>snd e\<close>} side is the up-path; for @{term U} the roles swap. Returns a flat tuple
      @{term \<open>(\<delta>, is_flip, v, e0fwd, up_side)\<close>} (no options): @{term \<open>\<delta> = - 1\<close>} signals an
      all-infinite circuit (unbounded); otherwise @{term is_flip} tells a flip (the entering edge is
      itself the bottleneck --- @{term v}, @{term e0fwd}, @{term up_side} are then dummies) from a full
      pivot with leaving-edge child @{term v}. The peak tie-break prefers the up-path, then the
      entering edge, then the down-path.\<close>
definition "bottleneck_imp s e in_U ptr1 ptr2 =
  (let (up_pa, up_ptr, down_pa, down_ptr) =
         (if in_U then (ipath1 s, ptr1, ipath2 s, ptr2)
                  else (ipath2 s, ptr2, ipath1 s, ptr1))
   in do {
     r_e \<leftarrow> (if in_U then res_bwd_imp s e else res_fwd_imp s e);
     muvu \<leftarrow> scan_up_imp   s up_pa up_ptr;
     mdvd \<leftarrow> scan_down_imp s down_pa down_ptr;
     (case muvu of (mu, vu) \<Rightarrow> case mdvd of (md, vd) \<Rightarrow>
        (let d = mininf_imp r_e (mininf_imp mu md) in
         if d = - 1 then return (- 1, True, r, False, False)
         else if mu \<noteq> - 1 \<and> mu = d
           then do { up \<leftarrow> par_up_imp s vu; return (d, False, vu, up, True) }
         else if r_e = d then return (d, True, r, False, False)
         else do { up \<leftarrow> par_up_imp s vd; return (d, False, vd, \<not> up, False) }))
   })"

subsection \<open>State updates\<close>

text \<open>Augment the flow by @{term \<delta>} along the fundamental circuit, in place. A degenerate pivot
      (@{term \<open>\<delta> \<le> 0\<close>}) leaves the flow untouched. @{term aug_loop_imp} folds the parent-edge updates
      over a path-array prefix; rather than take a sign \<^emph>\<open>closure\<close> (a per-vertex indirect call) it takes
      the value @{term \<delta>} and a flag @{term on_up} (whether this is the up-path pass) and computes the
      per-vertex sign inline as @{term \<open>if up = on_up then \<delta> else - \<delta>\<close>}.\<close>
partial_function (heap) aug_loop_imp ::
  "('farr, 'parr, 'arbor, 'pearr, 'darr, 'earr, 'sel, 'a) ns_impl_state
     \<Rightarrow> 'a array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'n \<Rightarrow> bool \<Rightarrow> unit Heap" where
  "aug_loop_imp s pa i ptr \<delta> on_up =
     (if ptr \<le> i then return ()
      else do {
        v \<leftarrow> Array.nth pa i;
        a \<leftarrow> par_edge_imp s v;
        up \<leftarrow> par_up_imp s v;
        fa \<leftarrow> flow_lookup_imp (iflow s) a;
        _ \<leftarrow> flow_upd_imp (iflow s) a (fa + (if up = on_up then \<delta> else - \<delta>));
        aug_loop_imp s pa (i + 1) ptr \<delta> on_up
      })"

definition "augment_flow_imp s e in_U \<delta> ptr1 ptr2 =
  (if \<delta> \<le> 0 then return ()
   else (let (up_pa, up_ptr, down_pa, down_ptr) =
               (if in_U then (ipath1 s, ptr1, ipath2 s, ptr2)
                        else (ipath2 s, ptr2, ipath1 s, ptr1))
         in do {
           fe \<leftarrow> flow_lookup_imp (iflow s) e;
           _ \<leftarrow> flow_upd_imp (iflow s) e (fe + (if in_U then - \<delta> else \<delta>));
           _ \<leftarrow> aug_loop_imp s up_pa 0 up_ptr \<delta> True;
           aug_loop_imp s down_pa 0 down_ptr \<delta> False
         }))"

text \<open>Degenerate pivot (the entering edge is its own bottleneck): the tree and potentials are
      unchanged and @{term e} flips between @{term L} and @{term U}, but the flow is still augmented by
      @{term \<delta>} along the whole circuit. The selector was already advanced in place by
      @{term sel_select_imp}, so there is no @{term sel'} to store.\<close>
definition "ns_flip_imp s e in_U \<delta> ptr1 ptr2 =
  do { _ \<leftarrow> augment_flow_imp s e in_U \<delta> ptr1 ptr2;
       es_upd_imp (iestate s) e (if in_U then InL else InU) }"

text \<open>Re-parenting after a swap, walking a path-array prefix from @{term \<open>hd P\<close>} up to @{term v} and
      no further, reversing parent pointers in place. To avoid a read-after-write the walk carries the
      \<^emph>\<open>old\<close> parent edge @{term pe} and orientation @{term pup} of the previous spine vertex --- captured
      into @{term \<open>(olde, oldup)\<close>} before the current vertex is overwritten --- rather than re-reading
      them; the @{term first} flag marks the initial step (where @{term pe}, @{term pup} are unused
      dummies), replacing what was an option.\<close>
partial_function (heap) reparent_walk_imp ::
  "('farr, 'parr, 'arbor, 'pearr, 'darr, 'earr, 'sel, 'a) ns_impl_state
     \<Rightarrow> 'edge \<Rightarrow> 'a \<Rightarrow> bool \<Rightarrow> 'edge \<Rightarrow> bool \<Rightarrow> 'a array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "reparent_walk_imp s e v first pe pup pa i ptr =
     (if ptr \<le> i then return ()
      else do {
        w \<leftarrow> Array.nth pa i;
        olde \<leftarrow> par_edge_imp s w;
        oldup \<leftarrow> par_up_imp s w;
        _ \<leftarrow> (if first
             then do { fe \<leftarrow> fst_exec_imp e;
                       _ \<leftarrow> parent_upd_imp (iparent s) w e;
                       dir_upd_imp (idir s) w (w = fe) }
             else do { _ \<leftarrow> parent_upd_imp (iparent s) w pe;
                       dir_upd_imp (idir s) w (\<not> pup) });
        (if w = v then return ()
         else reparent_walk_imp s e v False olde oldup pa (i + 1) ptr)
      })"

definition "reparent_imp s e pa ptr v = reparent_walk_imp s e v True e False pa 0 ptr"

text \<open>Full pivot: augment the flow, shift the potentials over the far side rooted at @{term v}, swap
      the tree edge, re-parent the parent/direction arrays along the spine @{term P}, and move
      @{term e} into the tree and the leaving edge @{term e0} into @{term U} (if saturated) or
      @{term L}. The leaving edge @{term e0} is read \<^emph>\<open>before\<close> @{const reparent_imp} overwrites
      @{term v}'s parent; the flow augmentation reads the parent arrays before @{const reparent_imp}
      mutates them.\<close>
definition "ns_pivot_imp s e eu ev in_U \<gamma> \<delta> v e0fwd up_side ptr1 ptr2 =
  (let updir = (in_U = up_side)
   in do {
     e0 \<leftarrow> par_edge_imp s v;
     _ \<leftarrow> augment_flow_imp s e in_U \<delta> ptr1 ptr2;
     _ \<leftarrow> shift_pot_imp (itree s) v (ipot s) \<gamma> (\<not> updir);
     _ \<leftarrow> reparent_imp s e (if updir then ipath1 s else ipath2 s)
                      (if updir then ptr1 else ptr2) v;
     _ \<leftarrow> swap_edge_imp (itree s) v (if updir then eu else ev) (if updir then ev else eu);
     _ \<leftarrow> es_upd_imp (iestate s) e InTree;
     es_upd_imp (iestate s) e0 (if e0fwd then InU else InL)
   })"

subsection \<open>The loop\<close>

text \<open>One iteration: select an entering edge (@{const None} {\isasymLongrightarrow} optimal, return @{const success});
      otherwise search the paths, compute the bottleneck (@{const None} {\isasymLongrightarrow} unbounded, return
      @{const unbounded}); otherwise flip or pivot in place and recurse. The state handles are threaded
      unchanged --- all changes are in-place mutations --- so the loop is genuinely tail-recursive and
      MLton compiles it to an in-place loop.\<close>
partial_function (heap) ns_loop_imp ::
  "('farr, 'parr, 'arbor, 'pearr, 'darr, 'earr, 'sel, 'a) ns_impl_state \<Rightarrow> return Heap" where
  "ns_loop_imp s =
     do {
       sel \<leftarrow> ns_select_imp s;
       (case sel of
          None \<Rightarrow> return Network_Simplex.success
        | Some (e, in_U, \<gamma>) \<Rightarrow>
            do {
              u \<leftarrow> fst_exec_imp e;
              v \<leftarrow> snd_exec_imp e;
              (ptr1, ptr2) \<leftarrow> get_path_pair_imp (itree s) u v (ipath1 s) (ipath2 s);
              bn \<leftarrow> bottleneck_imp s e in_U ptr1 ptr2;
              (case bn of (\<delta>, is_flip, vv, e0fwd, up_side) \<Rightarrow>
                 if \<delta> = - 1 then return Network_Simplex.unbounded
                 else if is_flip
                   then do { _ \<leftarrow> ns_flip_imp s e in_U \<delta> ptr1 ptr2; ns_loop_imp s }
                   else do { _ \<leftarrow> ns_pivot_imp s e u v in_U \<gamma> \<delta> vv e0fwd up_side ptr1 ptr2; ns_loop_imp s })
            })
     }"

end

section \<open>The refinement proof locale\<close>

text \<open>The proof locale combines the functional proof locale @{locale network_simplex} --- which
      supplies the cost-flow network (hence the vertex set @{term \<V>}, the edge set @{term \<E>} and the
      root @{term r}), the spanning-tree ADT, the five array stores, the selector and \<^emph>\<open>all their
      assumed laws\<close> --- with the imperative code locale @{locale network_simplex_impl_spec}. The two
      locales share only the root @{term r}; every imperative operation carries an @{text \<open>_imp\<close>}
      suffix, so no other parameter is accidentally identified.

      For each mutable store it fixes a \<^emph>\<open>representation assertion\<close> relating a functional store value
      to its imperative heap handle (@{typ assn} is the separation-logic heap predicate):
      @{term flow_assn}, @{term pot_assn}, @{term tree_assn}, @{term parent_assn}, @{term dir_assn},
      @{term es_assn} and @{term sel_assn}. The two path buffers are plain arrays and use the standard
      @{term \<open>(\<mapsto>\<^sub>a)\<close>} array assertion directly.

      It then \<^emph>\<open>assumes one Hoare triple per imperative operation\<close>. The discipline is:
      \<^item> a mutating operation (result @{typ \<open>unit Heap\<close>}) turns the pre-representation of the store into
        the representation of the \<^emph>\<open>functionally updated\<close> store, with no returned value;
      \<^item> a reading operation returns the value the \<^emph>\<open>functional\<close> operation computes, keeping the
        representation unchanged;
      \<^item> the selector mutates its own store in place and returns the value part of the functional result
        (the functional @{term sel'} is dropped from the tuple);
      \<^item> the path search mutates the two buffers in place and returns the two fill pointers, the buffer
        prefixes then holding the functional vertex lists;
      \<^item> the pure endpoint / capacity reads have an empty footprint.

      Crucially, the \<^emph>\<open>pure logical preconditions of each triple are exactly the hypotheses of the
      corresponding functional law(s)\<close>. The refinement assertion alone captures only the low-level
      structural correspondence between a functional value and its heap handle; it does \<^emph>\<open>not\<close> by
      itself guarantee that the inputs have the well-formed structure (the store invariant, the
      key-set membership, the arborescence invariant, the non-self-loop / distinct-endpoint condition)
      under which the assumed imperative function is meant to run and terminate. Those hypotheses must
      therefore \<^emph>\<open>still be assumed\<close>: for the flow / edge-state stores that is @{term flow_invar} /
      @{term es_invar} with @{term \<open>e \<in> \<E>\<close>} (mirroring @{locale fixed_univ_map} at key set
      @{term \<E>}); for the potential store @{term pot_invar} at key set @{term \<V>}; for the
      parent-edge / direction stores @{term parent_invar} / @{term dir_invar} with
      @{term \<open>v \<in> \<V> - {r}\<close>}; for the tree the @{term arborescense_invar} together with the exact
      @{term get_path_pair} / @{term swap_edge} hypotheses of the @{locale arborescense_adt} axioms;
      and for the selector @{term sel_invar}, @{term pot_invar}, @{term es_invar}.\<close>

text \<open>The edge-state tags are stored in arrays.\<close>

instance edge_tag :: countable by countable_datatype
instance edge_tag :: heap ..

locale network_simplex_impl_refine =
  network_simplex where flow_lookup = flow_lookup and pot_lookup = pot_lookup
      and get_path_pair = get_path_pair and parent_lookup = parent_lookup
      and dir_lookup = dir_lookup and es_lookup = es_lookup and sel_select = sel_select +
  network_simplex_impl_spec where flow_lookup_imp = flow_lookup_imp
      and shift_pot_imp = shift_pot_imp and parent_lookup_imp = parent_lookup_imp
      and dir_lookup_imp = dir_lookup_imp and es_lookup_imp = es_lookup_imp
      and sel_select_imp = sel_select_imp +
  flow_imp: fixed_univ_map_imp where K = \<E> and fixed_univ_map_invar = flow_invar
      and fixed_univ_map_upd = flow_upd and fixed_univ_map_lookup = flow_lookup
      and fixed_univ_map_val = id and fixed_univ_map_assn = flow_assn
      and fixed_univ_map_upd_imp = flow_upd_imp and fixed_univ_map_lookup_imp = flow_lookup_imp +
  es_imp: fixed_univ_map_imp where K = \<E> and fixed_univ_map_invar = es_invar
      and fixed_univ_map_upd = es_upd and fixed_univ_map_lookup = es_lookup
      and fixed_univ_map_val = id and fixed_univ_map_assn = es_assn
      and fixed_univ_map_upd_imp = es_upd_imp and fixed_univ_map_lookup_imp = es_lookup_imp +
  parent_imp: fixed_univ_map_imp where K = "\<V> - {r}" and fixed_univ_map_invar = parent_invar
      and fixed_univ_map_upd = parent_upd and fixed_univ_map_lookup = parent_lookup
      and fixed_univ_map_val = id and fixed_univ_map_assn = parent_assn
      and fixed_univ_map_upd_imp = parent_upd_imp and fixed_univ_map_lookup_imp = parent_lookup_imp +
  dir_imp: fixed_univ_map_imp where K = "\<V> - {r}" and fixed_univ_map_invar = dir_invar
      and fixed_univ_map_upd = dir_upd and fixed_univ_map_lookup = dir_lookup
      and fixed_univ_map_val = id and fixed_univ_map_assn = dir_assn
      and fixed_univ_map_upd_imp = dir_upd_imp and fixed_univ_map_lookup_imp = dir_lookup_imp
  for flow_lookup       :: "'farr \<Rightarrow> 'edge::heap \<Rightarrow> 'n::{linordered_idom, heap}"
    and flow_lookup_imp   :: "'farri \<Rightarrow> 'edge \<Rightarrow> 'n Heap"
    and pot_lookup        :: "'parr \<Rightarrow> 'a::heap \<Rightarrow> 'p"
    and get_path_pair     :: "'arbor \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a list \<times> 'a list"
    and shift_pot_imp     :: "'arbori \<Rightarrow> 'a \<Rightarrow> 'parri \<Rightarrow> 'r \<Rightarrow> bool \<Rightarrow> unit Heap"
    and parent_lookup     :: "'pearr \<Rightarrow> 'a \<Rightarrow> 'edge"
    and parent_lookup_imp :: "'pearri \<Rightarrow> 'a \<Rightarrow> 'edge Heap"
    and dir_lookup        :: "'darr \<Rightarrow> 'a \<Rightarrow> bool"
    and dir_lookup_imp    :: "'darri \<Rightarrow> 'a \<Rightarrow> bool Heap"
    and es_lookup         :: "'earr \<Rightarrow> 'edge \<Rightarrow> edge_tag"
    and es_lookup_imp     :: "'earri \<Rightarrow> 'edge \<Rightarrow> edge_tag Heap"
    and sel_select        :: "'selector \<Rightarrow> 'parr \<Rightarrow> 'earr \<Rightarrow> ('edge \<times> bool \<times> 'r \<times> 'selector) option"
    and sel_select_imp    :: "'seli \<Rightarrow> 'parri \<Rightarrow> 'earri \<Rightarrow> ('edge \<times> bool \<times> 'r) option Heap"
    and flow_assn   :: "'farr \<Rightarrow> 'farri \<Rightarrow> assn"
    and parent_assn :: "'pearr \<Rightarrow> 'pearri \<Rightarrow> assn"
    and dir_assn    :: "'darr \<Rightarrow> 'darri \<Rightarrow> assn"
    and es_assn     :: "'earr \<Rightarrow> 'earri \<Rightarrow> assn" +
  fixes pot_assn    :: "'parr \<Rightarrow> 'parri \<Rightarrow> assn"
    and tree_assn   :: "'arbor \<Rightarrow> 'arbori \<Rightarrow> assn"
    and sel_assn    :: "'selector \<Rightarrow> 'seli \<Rightarrow> assn"
    and rd          :: assn  \<comment> \<open>footprint of the read-only per-edge cap / endpoint stores\<close>
  assumes

    \<comment> \<open>potential shift --- the first-order subtree traversal refining the functional \<open>shift_pot\<close>; it
        reads the tree and mutates the potential store, whose functional value becomes
        \<open>shift_pot T v pa g up\<close>. Its precondition is exactly that of the functional law \<open>shift_pot_spec\<close>.\<close>
    shift_pot_rule:
      "\<lbrakk>arborescense_invar T; v \<in> \<V>; pot_invar pa; \<And>u. u \<in> \<V> \<Longrightarrow> pot_value_invar (pot_lookup pa u)\<rbrakk> \<Longrightarrow>
       <tree_assn T th * pot_assn pa poth> shift_pot_imp th v poth g up
                 <\<lambda>_. tree_assn T th * pot_assn (shift_pot T v pa g up) poth>"
    \<comment> \<open>entering-edge selection --- reads potentials and edge tags, mutates the selector in place and
        returns the value part of the functional result (the functional @{term sel'} is dropped).\<close>
    and sel_select_rule:
      "\<lbrakk>sel_invar Sel; pot_invar \<pi>; es_invar Es\<rbrakk> \<Longrightarrow>
       <sel_assn Sel selh * pot_assn \<pi> poth * es_assn Es esh * rd> sel_select_imp selh poth esh
                 <\<lambda>res. pot_assn \<pi> poth * es_assn Es esh * rd *
                    (case sel_select Sel \<pi> Es of
                       None \<Rightarrow> (\<exists>\<^sub>A ss. sel_assn ss selh) * \<up>(res = None)
                     | Some (e, in_U, \<gamma>, sel') \<Rightarrow> sel_assn sel' selh * \<up>(res = Some (e, in_U, \<gamma>)))>"
    \<comment> \<open>fundamental-circuit path search --- writes the two functional vertex paths into the two buffers
        and returns their fill pointers; the buffer prefixes then hold @{term p1} / @{term p2}. The
        buffers must be at least as long as a longest tree path (@{term \<open>card \<V>\<close>} bounds it). Its
        precondition is exactly that of the @{locale arborescense_adt} axiom @{text get_path_pair}.\<close>
    and get_path_pair_rule:
      "\<lbrakk>arborescense_invar T; u \<noteq> v; u \<in> \<V>; v \<in> \<V>; card \<V> - 1 \<le> length l1; card \<V> - 1 \<le> length l2\<rbrakk> \<Longrightarrow>
       <tree_assn T th * a1 \<mapsto>\<^sub>a l1 * a2 \<mapsto>\<^sub>a l2> get_path_pair_imp th u v a1 a2
                 <\<lambda>(ptr1, ptr2). \<exists>\<^sub>A l1' l2'. tree_assn T th * a1 \<mapsto>\<^sub>a l1' * a2 \<mapsto>\<^sub>a l2' *
                    \<up>(length l1' = length l1 \<and> length l2' = length l2 \<and>
                      ptr1 \<le> length l1' \<and> ptr2 \<le> length l2' \<and>
                      (take ptr1 l1', take ptr2 l2') = get_path_pair T u v)>"
    \<comment> \<open>tree-edge swap --- mutates the tree structure, whose functional value becomes
        @{term \<open>swap_edge T x u v\<close>}. Its precondition is exactly that of the @{locale arborescense_adt}
        axiom @{text swap_edge}.\<close>
    and swap_edge_rule:
      "\<lbrakk>arborescense_invar T; get_path_pair T u v = (p1, p2); u \<noteq> v;
        walk_betw (abstract_arborescense T) u (p1 @ a # p3) r; distinct (p1 @ a # p3);
        (x, y) \<in> set (edges_of_vwalk (p1 @ [a])); u \<in> \<V>; v \<in> \<V>\<rbrakk> \<Longrightarrow>
       <tree_assn T th> swap_edge_imp th x u v <\<lambda>_. tree_assn (swap_edge T x u v) th>"
    \<comment> \<open>pure per-edge reads --- empty heap footprint, the same @{term \<open>e \<in> \<E>\<close>} the functional encoding
        axioms (\<open>cap_infinite\<close> / \<open>cap_finite\<close>, \<open>fst_exec_coincide\<close>, \<open>snd_exec_coincide\<close>) assume.\<close>
    and cap_rule:      "e \<in> \<E> \<Longrightarrow> <rd> cap_imp e      <\<lambda>x. rd * \<up>(x = cap e)>"
    and fst_exec_rule: "e \<in> \<E> \<Longrightarrow> <rd> fst_exec_imp e <\<lambda>x. rd * \<up>(x = fst_exec e)>"
    and snd_exec_rule: "e \<in> \<E> \<Longrightarrow> <rd> snd_exec_imp e <\<lambda>x. rd * \<up>(x = snd_exec e)>"
begin

text \<open>The assumed per-operation Hoare triples are registered for @{method sep_auto}; each derived
      read / write and, ultimately, the whole loop then refines its functional counterpart.\<close>
lemmas [sep_heap_rules] =

  shift_pot_rule sel_select_rule get_path_pair_rule swap_edge_rule
  cap_rule fst_exec_rule snd_exec_rule

subsection \<open>Refinement of the derived leaf operations\<close>

text \<open>The @{term \<open>- 1\<close>}-as-{\isasyminfinity} minimum is purely functional and identical to @{const mininf}.\<close>
lemma mininf_imp_eq: "mininf_imp x y = mininf x y"
  by (simp add: mininf_imp_def mininf_def)

text \<open>Forward residual of a graph edge --- one read of capacity and, if finite, of flow.\<close>
lemma res_fwd_imp_rule [sep_heap_rules]:
  "\<lbrakk>flow_invar (current_flow s); a \<in> \<E>\<rbrakk> \<Longrightarrow>
   <flow_assn (current_flow s) (iflow si) * rd> res_fwd_imp si a
   <\<lambda>x. flow_assn (current_flow s) (iflow si) * rd * \<up>(x = res_fwd s a)>"
  unfolding res_fwd_imp_def res_fwd_def by (sep_auto simp: Let_def)

text \<open>Backward residual --- the current flow on the edge.\<close>
lemma res_bwd_imp_rule [sep_heap_rules]:
  "\<lbrakk>flow_invar (current_flow s); a \<in> \<E>\<rbrakk> \<Longrightarrow>
   <flow_assn (current_flow s) (iflow si)> res_bwd_imp si a
   <\<lambda>x. flow_assn (current_flow s) (iflow si) * \<up>(x = res_bwd s a)>"
  unfolding res_bwd_imp_def res_bwd_def by sep_auto

text \<open>The parent graph edge of a non-root vertex.\<close>
lemma par_edge_imp_rule [sep_heap_rules]:
  "\<lbrakk>parent_invar (parent_edge s); v \<in> \<V> - {r}\<rbrakk> \<Longrightarrow>
   <parent_assn (parent_edge s) (iparent si)> par_edge_imp si v
   <\<lambda>x. parent_assn (parent_edge s) (iparent si) * \<up>(x = par_edge s v)>"
  unfolding par_edge_imp_def par_edge_def by sep_auto

text \<open>The orientation flag of a non-root vertex's parent edge.\<close>
lemma par_up_imp_rule [sep_heap_rules]:
  "\<lbrakk>dir_invar (edge_dir s); v \<in> \<V> - {r}\<rbrakk> \<Longrightarrow>
   <dir_assn (edge_dir s) (idir si)> par_up_imp si v
   <\<lambda>x. dir_assn (edge_dir s) (idir si) * \<up>(x = par_up s v)>"
  unfolding par_up_imp_def par_up_def by sep_auto

text \<open>Residual of a vertex's parent edge traversed upward --- reads direction, parent edge and flow.\<close>
lemma res_up_imp_rule [sep_heap_rules]:
  "\<lbrakk>flow_invar (current_flow s); parent_invar (parent_edge s); dir_invar (edge_dir s);
    v \<in> \<V> - {r}; par_edge s v \<in> \<E>\<rbrakk> \<Longrightarrow>
   <flow_assn (current_flow s) (iflow si) * parent_assn (parent_edge s) (iparent si)
      * dir_assn (edge_dir s) (idir si) * rd>
     res_up_imp si v
   <\<lambda>x. flow_assn (current_flow s) (iflow si) * parent_assn (parent_edge s) (iparent si)
      * dir_assn (edge_dir s) (idir si) * rd * \<up>(x = res_up s v)>"
  unfolding res_up_imp_def res_up_def by sep_auto

text \<open>Residual of a vertex's parent edge traversed downward.\<close>
lemma res_down_imp_rule [sep_heap_rules]:
  "\<lbrakk>flow_invar (current_flow s); parent_invar (parent_edge s); dir_invar (edge_dir s);
    v \<in> \<V> - {r}; par_edge s v \<in> \<E>\<rbrakk> \<Longrightarrow>
   <flow_assn (current_flow s) (iflow si) * parent_assn (parent_edge s) (iparent si)
      * dir_assn (edge_dir s) (idir si) * rd>
     res_down_imp si v
   <\<lambda>x. flow_assn (current_flow s) (iflow si) * parent_assn (parent_edge s) (iparent si)
      * dir_assn (edge_dir s) (idir si) * rd * \<up>(x = res_down s v)>"
  unfolding res_down_imp_def res_down_def by sep_auto

text \<open>Run the entering-edge selector --- reads potentials and edge tags, mutates the selector in place
      and returns the value part of @{const ns_select} (the functional @{term sel'} is dropped).\<close>
lemma ns_select_imp_rule:
  "\<lbrakk>sel_invar (edge_sel s); pot_invar (potentials s); es_invar (edge_state s)\<rbrakk> \<Longrightarrow>
   <sel_assn (edge_sel s) (isel si) * pot_assn (potentials s) (ipot si)
      * es_assn (edge_state s) (iestate si) * rd>
     ns_select_imp si
   <\<lambda>res. pot_assn (potentials s) (ipot si) * es_assn (edge_state s) (iestate si) * rd *
      (case ns_select s of None \<Rightarrow> (\<exists>\<^sub>A ss. sel_assn ss (isel si)) * \<up>(res = None)
       | Some (e, in_U, \<gamma>, sel') \<Rightarrow> sel_assn sel' (isel si) * \<up>(res = Some (e, in_U, \<gamma>)))>"
  unfolding ns_select_imp_def ns_select_def by (sep_auto heap: sel_select_rule)

subsection \<open>The state refinement relation\<close>

text \<open>@{term ns_rel} ties a functional \<open>network_simplex_state\<close> to an imperative
      \<open>ns_impl_state\<close>: the seven functional stores relate to their imperative handles through
      the seven representation assertions, and the two path buffers @{term ipath1}, @{term ipath2}
      are \<^emph>\<open>existentially quantified\<close> arrays with room for a longest tree path (@{term \<open>card \<V> - 1\<close>}
      entries). The buffers carry \<^emph>\<open>no semantic content between iterations\<close> --- they are scratch space,
      meaningful only \<^emph>\<open>during\<close> an iteration --- so all @{term ns_rel} asserts is that each refines
      \<^emph>\<open>some\<close> list of length at least @{term \<open>card \<V> - 1\<close>}; at the loop granularity they are hidden
      behind the
      existential; the operations that inspect them (\<open>get_path_pair_imp\<close>, \<open>bottleneck_imp\<close>,
      \<open>augment_flow_imp\<close>) expose them explicitly instead. The termination flag is not stored
      imperatively, so it has no counterpart here.\<close>

definition ns_rel ::
  "('farr, 'parr, 'arbor, 'pearr, 'darr, 'earr, 'selector) network_simplex_state
     \<Rightarrow> ('farri, 'parri, 'arbori, 'pearri, 'darri, 'earri, 'seli, 'a) ns_impl_state \<Rightarrow> assn" where
  "ns_rel s si =
     rd *
     flow_assn   (current_flow s)  (iflow si)   *
     pot_assn    (potentials s)    (ipot si)     *
     tree_assn   (spanning_tree s) (itree si)    *
     parent_assn (parent_edge s)   (iparent si)  *
     dir_assn    (edge_dir s)      (idir si)     *
     es_assn     (edge_state s)    (iestate si)  *
     sel_assn    (edge_sel s)      (isel si)     *
     (\<exists>\<^sub>A l1 l2. ipath1 si \<mapsto>\<^sub>a l1 * ipath2 si \<mapsto>\<^sub>a l2 *
        \<up>(card \<V> - 1 \<le> length l1 \<and> card \<V> - 1 \<le> length l2))"

text \<open>A \<^emph>\<open>weaker\<close> relation for the loop's \<^emph>\<open>result\<close>: the selector store carries pricing state \<^emph>\<open>between\<close>
      iterations, so the loop's precondition must pin it (\<open>ns_rel\<close>); but at the loop's terminal states it
      is dead. The imperative @{const ns_select_imp} advances the selector store to @{term sel'} whenever
      it returns @{term \<open>Some \<close>}, whereas the functional @{const ns_unbounded_upd} keeps the old
      @{term \<open>edge_sel s\<close>} (only @{const ns_flip} / @{const ns_pivot} thread @{term sel'}). So on the
      unbounded terminal branch the two selector stores legitimately diverge; the result relation therefore
      leaves the selector store \<^emph>\<open>existential\<close>, asserting only that it represents \<^emph>\<open>some\<close> functional
      selector. Every other store still relates exactly.\<close>
definition ns_rel_weak ::
  "('farr, 'parr, 'arbor, 'pearr, 'darr, 'earr, 'selector) network_simplex_state
     \<Rightarrow> ('farri, 'parri, 'arbori, 'pearri, 'darri, 'earri, 'seli, 'a) ns_impl_state \<Rightarrow> assn" where
  "ns_rel_weak s si =
     rd *
     flow_assn   (current_flow s)  (iflow si)   *
     pot_assn    (potentials s)    (ipot si)     *
     tree_assn   (spanning_tree s) (itree si)    *
     parent_assn (parent_edge s)   (iparent si)  *
     dir_assn    (edge_dir s)      (idir si)     *
     es_assn     (edge_state s)    (iestate si)  *
     (\<exists>\<^sub>A ss. sel_assn ss (isel si)) *
     (\<exists>\<^sub>A l1 l2. ipath1 si \<mapsto>\<^sub>a l1 * ipath2 si \<mapsto>\<^sub>a l2 *
        \<up>(card \<V> - 1 \<le> length l1 \<and> card \<V> - 1 \<le> length l2))"


subsection \<open>Refinement of the bottleneck scan\<close>

text \<open>@{const scan_up_loop_imp} walking the path-array prefix @{term \<open>[i..<ptr]\<close>} upward refines the
      @{const fold} of the @{const scan_up} step over the corresponding vertex sub-list
      @{term \<open>drop i (take ptr l)\<close>} (where @{term l} is the buffer content). Each scanned vertex must
      be a non-root vertex whose parent edge lies in @{term \<E>} (so @{const res_up_imp} is specified).\<close>
lemma scan_up_loop_imp_rule:
  "\<lbrakk>flow_invar (current_flow s); parent_invar (parent_edge s); dir_invar (edge_dir s);
    ptr \<le> length l; \<forall>v \<in> set (drop i (take ptr l)).
      v \<in> \<V> - {r} \<and> par_edge s v \<in> \<E>\<rbrakk> \<Longrightarrow>
   <flow_assn (current_flow s) (iflow si) * parent_assn (parent_edge s) (iparent si)
      * dir_assn (edge_dir s) (idir si) * pa \<mapsto>\<^sub>a l * rd>
     scan_up_loop_imp si pa i ptr m0 best0
   <\<lambda>res. flow_assn (current_flow s) (iflow si) * parent_assn (parent_edge s) (iparent si)
      * dir_assn (edge_dir s) (idir si) * pa \<mapsto>\<^sub>a l * rd
      * \<up>(res = fold (\<lambda> v acc. case acc of (m, best) \<Rightarrow>
               (let rr = res_up s v in
                if rr = - 1 then (m, best) else if m = - 1 then (rr, v)
                else if rr \<le> m then (rr, v) else (m, best)))
             (drop i (take ptr l)) (m0, best0))>"
proof(induction "ptr - i" arbitrary: i m0 best0)
  case (Suc k)
  have k: "k = ptr - Suc i" "\<not> ptr \<le> i" "i < length l"
    "drop i (take ptr l) = l ! i # drop (Suc i) (take ptr l)"
    "l ! i \<in> \<V>" "l ! i \<noteq> r" "par_edge s (l ! i) \<in> \<E>"
    "\<forall>v \<in> set (drop (Suc i) (take ptr l)). v \<in> \<V> - {r} \<and> par_edge s v \<in> \<E>"
    using Suc.hyps(2) Suc.prems(4,5)
    by (auto simp: Cons_nth_drop_Suc[symmetric])
  show ?case
    by (sep_auto simp: scan_up_loop_imp.simps[of si pa i] k(2-7) Suc.prems(1-3)
      split: if_splits heap: Suc.hyps(1)[OF k(1) Suc.prems(1-4) k(8)])
qed (subst scan_up_loop_imp.simps, sep_auto simp: drop_take)

text \<open>The downward scan is the mirror image, using @{const res_down} and a \<^emph>\<open>strict\<close>
      comparison.\<close>
lemma scan_down_loop_imp_rule:
  "\<lbrakk>flow_invar (current_flow s); parent_invar (parent_edge s); dir_invar (edge_dir s);
    ptr \<le> length l; \<forall>v \<in> set (drop i (take ptr l)).
      v \<in> \<V> - {r} \<and> par_edge s v \<in> \<E>\<rbrakk> \<Longrightarrow>
   <flow_assn (current_flow s) (iflow si) * parent_assn (parent_edge s) (iparent si)
      * dir_assn (edge_dir s) (idir si) * pa \<mapsto>\<^sub>a l * rd>
     scan_down_loop_imp si pa i ptr m0 best0
   <\<lambda>res. flow_assn (current_flow s) (iflow si) * parent_assn (parent_edge s) (iparent si)
      * dir_assn (edge_dir s) (idir si) * pa \<mapsto>\<^sub>a l * rd
      * \<up>(res = fold (\<lambda> v acc. case acc of (m, best) \<Rightarrow>
               (let rr = res_down s v in
                if rr = - 1 then (m, best) else if m = - 1 then (rr, v)
                else if rr < m then (rr, v) else (m, best)))
             (drop i (take ptr l)) (m0, best0))>"
proof(induction "ptr - i" arbitrary: i m0 best0)
  case (Suc k)
  have k: "k = ptr - Suc i" "\<not> ptr \<le> i" "i < length l"
    "drop i (take ptr l) = l ! i # drop (Suc i) (take ptr l)"
    "l ! i \<in> \<V>" "l ! i \<noteq> r" "par_edge s (l ! i) \<in> \<E>"
    "\<forall>v \<in> set (drop (Suc i) (take ptr l)). v \<in> \<V> - {r} \<and> par_edge s v \<in> \<E>"
    using Suc.hyps(2) Suc.prems(4,5)
    by (auto simp: Cons_nth_drop_Suc[symmetric])
  show ?case
    by (sep_auto simp: scan_down_loop_imp.simps[of si pa i] k(2-7) Suc.prems(1-3)
      split: if_splits heap: Suc.hyps(1)[OF k(1) Suc.prems(1-4) k(8)])
qed (subst scan_down_loop_imp.simps, sep_auto simp: drop_take)

text \<open>Seeded at index @{term 0} with @{term \<open>(- 1, r)\<close>}, the loops refine the top-level
      @{const scan_up} / @{const scan_down} on the buffer prefix @{term \<open>take ptr l\<close>}.\<close>
lemma scan_up_imp_rule:
  "\<lbrakk>flow_invar (current_flow s); parent_invar (parent_edge s); dir_invar (edge_dir s);
    ptr \<le> length l; \<forall>v \<in> set (take ptr l).
      v \<in> \<V> - {r} \<and> par_edge s v \<in> \<E>\<rbrakk> \<Longrightarrow>
   <flow_assn (current_flow s) (iflow si) * parent_assn (parent_edge s) (iparent si)
      * dir_assn (edge_dir s) (idir si) * pa \<mapsto>\<^sub>a l * rd>
     scan_up_imp si pa ptr
   <\<lambda>res. flow_assn (current_flow s) (iflow si) * parent_assn (parent_edge s) (iparent si)
      * dir_assn (edge_dir s) (idir si) * pa \<mapsto>\<^sub>a l * rd * \<up>(res = scan_up s (take ptr l))>"
  unfolding scan_up_imp_def scan_up_def
  by (sep_auto heap: scan_up_loop_imp_rule[where i = 0])

lemma scan_down_imp_rule:
  "\<lbrakk>flow_invar (current_flow s); parent_invar (parent_edge s); dir_invar (edge_dir s);
    ptr \<le> length l; \<forall>v \<in> set (take ptr l).
      v \<in> \<V> - {r} \<and> par_edge s v \<in> \<E>\<rbrakk> \<Longrightarrow>
   <flow_assn (current_flow s) (iflow si) * parent_assn (parent_edge s) (iparent si)
      * dir_assn (edge_dir s) (idir si) * pa \<mapsto>\<^sub>a l * rd>
     scan_down_imp si pa ptr
   <\<lambda>res. flow_assn (current_flow s) (iflow si) * parent_assn (parent_edge s) (iparent si)
      * dir_assn (edge_dir s) (idir si) * pa \<mapsto>\<^sub>a l * rd * \<up>(res = scan_down s (take ptr l))>"
  unfolding scan_down_imp_def scan_down_def
  by (sep_auto heap: scan_down_loop_imp_rule[where i = 0])
text \<open>If the circuit bottleneck is finite but is attained neither at the entering edge nor on the
      up-path, then the down-path minimum is itself finite --- so its minimiser is a real vertex.\<close>
lemma bottleneck_down_finite:
  "\<lbrakk>mininf r_e (mininf mu md) \<noteq> - 1; r_e \<noteq> mininf r_e (mininf mu md);
    \<not> (mu \<noteq> - 1 \<and> mu = mininf r_e (mininf mu md))\<rbrakk> \<Longrightarrow> md \<noteq> - 1"
  by (auto simp: mininf_def split: if_splits)

lemma scan_snd_in_V:
  "\<lbrakk>scan_up s p = (m, w); m \<noteq> - 1;
    \<forall>v \<in> set p. v \<in> \<V> - {r} \<and> par_edge s v \<in> \<E>\<rbrakk> \<Longrightarrow> w \<in> \<V> - {r}"
  "\<lbrakk>scan_down s p = (m, w); m \<noteq> - 1;
    \<forall>v \<in> set p. v \<in> \<V> - {r} \<and> par_edge s v \<in> \<E>\<rbrakk> \<Longrightarrow> w \<in> \<V> - {r}"
  using scan_up_snd_mem[of s p m w] scan_down_snd_mem[of s p m w]
  by auto

text \<open>The whole bottleneck computation refines @{const bottleneck}. It reads the entering edge's
      residual, runs the two scans over the two buffer prefixes (the functional paths
      @{term \<open>take ptr1 l1\<close>} / @{term \<open>take ptr2 l2\<close>}), and --- when a tree edge
      leaves --- reads the leaving vertex's orientation. The scans' minimisers are genuine path vertices (by
      @{thm scan_up_snd_mem} / @{thm scan_down_snd_mem}), hence non-root, so @{const par_up_imp} is specified
      there.\<close>
lemma bottleneck_imp_rule:
  assumes "flow_invar (current_flow s)" "parent_invar (parent_edge s)" "dir_invar (edge_dir s)"
    "e \<in> \<E>" "ptr1 \<le> length l1" "ptr2 \<le> length l2"
    "\<forall>v \<in> set (take ptr1 l1). v \<in> \<V> - {r} \<and> par_edge s v \<in> \<E>"
    "\<forall>v \<in> set (take ptr2 l2). v \<in> \<V> - {r} \<and> par_edge s v \<in> \<E>"
  shows "<flow_assn (current_flow s) (iflow si) * parent_assn (parent_edge s) (iparent si)
      * dir_assn (edge_dir s) (idir si) * ipath1 si \<mapsto>\<^sub>a l1 * ipath2 si \<mapsto>\<^sub>a l2 * rd>
     bottleneck_imp si e in_U ptr1 ptr2
   <\<lambda>res. flow_assn (current_flow s) (iflow si) * parent_assn (parent_edge s) (iparent si)
      * dir_assn (edge_dir s) (idir si) * ipath1 si \<mapsto>\<^sub>a l1 * ipath2 si \<mapsto>\<^sub>a l2 * rd
      * \<up>(res = bottleneck s e in_U (take ptr1 l1) (take ptr2 l2))>"
  unfolding bottleneck_imp_def bottleneck_def
  by (cases in_U; sep_auto simp: Let_def mininf_imp_eq assms(1-4)
    dest: scan_snd_in_V[OF _ _ assms(7)] scan_snd_in_V[OF _ _ assms(8)] bottleneck_down_finite
    heap: scan_up_imp_rule[OF assms(1-3,5,7)] scan_up_imp_rule[OF assms(1-3,6,8)]
      scan_down_imp_rule[OF assms(1-3,5,7)] scan_down_imp_rule[OF assms(1-3,6,8)])

subsection \<open>Refinement of the flow augmentation\<close>

text \<open>@{const aug_loop_imp} folds the parent-edge flow updates over a path-array prefix in place. Since
      @{const augment_flow_imp} always calls it with a \<^emph>\<open>literal\<close> pass flag, we prove the
      two instances separately (avoiding a spurious flag/sign case split): with
      @{term \<open>on_up = True\<close>} (the up-path, sign
      @{term \<open>if par_up s v then \<delta> else - \<delta>\<close>}) and with
      @{term \<open>on_up = False\<close>} (the down-path, opposite sign). The flow value is threaded through
      the induction; @{thm flow_arr.fixed_univ_map_upd_invar} keeps @{term flow_invar} across each update.\<close>
lemma aug_loop_imp_up_rule:
  "\<lbrakk>flow_invar Fl; parent_invar (parent_edge s); dir_invar (edge_dir s);
    ptr \<le> length l; \<forall>v \<in> set (drop i (take ptr l)).
      v \<in> \<V> - {r} \<and> par_edge s v \<in> \<E>\<rbrakk> \<Longrightarrow>
   <flow_assn Fl (iflow si) * parent_assn (parent_edge s) (iparent si)
      * dir_assn (edge_dir s) (idir si) * pa \<mapsto>\<^sub>a l>
     aug_loop_imp si pa i ptr \<delta> True
   <\<lambda>_. flow_assn (fold (\<lambda> v f. let a = par_edge s v in
                     flow_upd f a (flow_lookup f a + (if par_up s v then \<delta> else - \<delta>)))
                   (drop i (take ptr l)) Fl) (iflow si)
      * parent_assn (parent_edge s) (iparent si) * dir_assn (edge_dir s) (idir si) * pa \<mapsto>\<^sub>a l>"
proof(induction "ptr - i" arbitrary: i Fl)
  case (Suc k)
  have k: "k = ptr - Suc i" "\<not> ptr \<le> i" "i < length l"
    "drop i (take ptr l) = l ! i # drop (Suc i) (take ptr l)"
    "l ! i \<in> \<V>" "l ! i \<noteq> r" "par_edge s (l ! i) \<in> \<E>"
    "\<forall>v \<in> set (drop (Suc i) (take ptr l)). v \<in> \<V> - {r} \<and> par_edge s v \<in> \<E>"
    using Suc.hyps(2) Suc.prems(4,5)
    by (auto simp: Cons_nth_drop_Suc[symmetric])
  show ?case
    by (sep_auto simp: aug_loop_imp.simps[of si pa i] k(2-7) Suc.prems(1-3) Let_def
      flow_arr.fixed_univ_map_upd_invar[OF Suc.prems(1) k(7)] heap: Suc.hyps(1)[OF k(1) _ Suc.prems(2-4) k(8)])
qed (subst aug_loop_imp.simps, sep_auto simp: drop_take)

lemma aug_loop_imp_down_rule:
  "\<lbrakk>flow_invar Fl; parent_invar (parent_edge s); dir_invar (edge_dir s);
    ptr \<le> length l; \<forall>v \<in> set (drop i (take ptr l)).
      v \<in> \<V> - {r} \<and> par_edge s v \<in> \<E>\<rbrakk> \<Longrightarrow>
   <flow_assn Fl (iflow si) * parent_assn (parent_edge s) (iparent si)
      * dir_assn (edge_dir s) (idir si) * pa \<mapsto>\<^sub>a l>
     aug_loop_imp si pa i ptr \<delta> False
   <\<lambda>_. flow_assn (fold (\<lambda> v f. let a = par_edge s v in
                     flow_upd f a (flow_lookup f a + (if par_up s v then - \<delta> else \<delta>)))
                   (drop i (take ptr l)) Fl) (iflow si)
      * parent_assn (parent_edge s) (iparent si) * dir_assn (edge_dir s) (idir si) * pa \<mapsto>\<^sub>a l>"
proof(induction "ptr - i" arbitrary: i Fl)
  case (Suc k)
  have k: "k = ptr - Suc i" "\<not> ptr \<le> i" "i < length l"
    "drop i (take ptr l) = l ! i # drop (Suc i) (take ptr l)"
    "l ! i \<in> \<V>" "l ! i \<noteq> r" "par_edge s (l ! i) \<in> \<E>"
    "\<forall>v \<in> set (drop (Suc i) (take ptr l)). v \<in> \<V> - {r} \<and> par_edge s v \<in> \<E>"
    using Suc.hyps(2) Suc.prems(4,5)
    by (auto simp: Cons_nth_drop_Suc[symmetric])
  show ?case
    by (sep_auto simp: aug_loop_imp.simps[of si pa i] k(2-7) Suc.prems(1-3) Let_def
      flow_arr.fixed_univ_map_upd_invar[OF Suc.prems(1) k(7)] heap: Suc.hyps(1)[OF k(1) _ Suc.prems(2-4) k(8)])
qed (subst aug_loop_imp.simps, sep_auto simp: drop_take)

text \<open>Folding parent-edge flow updates preserves @{term flow_invar} (each update is on an edge of
      @{term \<E>}).\<close>
lemma fold_flow_invar:
  "\<lbrakk>flow_invar Fl; \<forall>v \<in> set p. par_edge s v \<in> \<E>\<rbrakk> \<Longrightarrow>
   flow_invar (fold (\<lambda>v f. flow_upd f (par_edge s v) (g f v)) p Fl)"
  by (induction p arbitrary: Fl) (simp_all add: flow_arr.fixed_univ_map_upd_invar)

text \<open>The whole flow augmentation refines @{const augment_flow}: a degenerate pivot leaves the flow
      untouched; otherwise the entering edge is updated and the flow is pushed along the two circuit
      branches in place, the up-branch (@{term True}) before the down-branch (@{term False}).\<close>
lemma augment_flow_imp_rule:
  assumes "flow_invar (current_flow s)" "parent_invar (parent_edge s)" "dir_invar (edge_dir s)"
    "e \<in> \<E>" "ptr1 \<le> length l1" "ptr2 \<le> length l2"
    "\<forall>v \<in> set (take ptr1 l1). v \<in> \<V> - {r} \<and> par_edge s v \<in> \<E>"
    "\<forall>v \<in> set (take ptr2 l2). v \<in> \<V> - {r} \<and> par_edge s v \<in> \<E>"
  shows "<flow_assn (current_flow s) (iflow si) * parent_assn (parent_edge s) (iparent si)
      * dir_assn (edge_dir s) (idir si) * ipath1 si \<mapsto>\<^sub>a l1 * ipath2 si \<mapsto>\<^sub>a l2>
     augment_flow_imp si e in_U \<delta> ptr1 ptr2
   <\<lambda>_. flow_assn (augment_flow s e in_U \<delta> (take ptr1 l1) (take ptr2 l2)) (iflow si)
      * parent_assn (parent_edge s) (iparent si) * dir_assn (edge_dir s) (idir si)
      * ipath1 si \<mapsto>\<^sub>a l1 * ipath2 si \<mapsto>\<^sub>a l2>"
  unfolding augment_flow_imp_def augment_flow_def
  by (cases in_U; sep_auto simp: Let_def assms(1,4,7,8) flow_arr.fixed_univ_map_upd_invar[OF assms(1,4)]
      fold_flow_invar[OF flow_arr.fixed_univ_map_upd_invar[OF assms(1,4)]]
    heap: aug_loop_imp_up_rule[where i = 0, unfolded drop_0, OF _ assms(2,3,5,7)]
      aug_loop_imp_up_rule[where i = 0, unfolded drop_0, OF _ assms(2,3,6,8)]
      aug_loop_imp_down_rule[where i = 0, unfolded drop_0, OF _ assms(2,3,5,7)]
      aug_loop_imp_down_rule[where i = 0, unfolded drop_0, OF _ assms(2,3,6,8)])

subsection \<open>Refinement of the degenerate pivot (flip)\<close>

text \<open>@{const ns_flip_imp} augments the flow along the circuit and then relabels the entering edge
      between @{term InL} and @{term InU} in place; it refines @{const ns_flip} on the flow and
      edge-state stores (the selector was already advanced by @{const ns_select_imp}).\<close>
lemma ns_flip_imp_rule:
  assumes "flow_invar (current_flow s)" "parent_invar (parent_edge s)" "dir_invar (edge_dir s)"
    "es_invar (edge_state s)" "e \<in> \<E>" "ptr1 \<le> length l1" "ptr2 \<le> length l2"
    "\<forall>v \<in> set (take ptr1 l1). v \<in> \<V> - {r} \<and> par_edge s v \<in> \<E>"
    "\<forall>v \<in> set (take ptr2 l2). v \<in> \<V> - {r} \<and> par_edge s v \<in> \<E>"
  shows "<flow_assn (current_flow s) (iflow si) * parent_assn (parent_edge s) (iparent si)
      * dir_assn (edge_dir s) (idir si) * es_assn (edge_state s) (iestate si)
      * ipath1 si \<mapsto>\<^sub>a l1 * ipath2 si \<mapsto>\<^sub>a l2>
     ns_flip_imp si e in_U \<delta> ptr1 ptr2
   <\<lambda>_. flow_assn (augment_flow s e in_U \<delta> (take ptr1 l1) (take ptr2 l2)) (iflow si)
      * parent_assn (parent_edge s) (iparent si) * dir_assn (edge_dir s) (idir si)
      * es_assn (es_upd (edge_state s) e (if in_U then InL else InU)) (iestate si)
      * ipath1 si \<mapsto>\<^sub>a l1 * ipath2 si \<mapsto>\<^sub>a l2>"
  unfolding ns_flip_imp_def
  by (sep_auto simp: assms(4,5) heap: augment_flow_imp_rule[OF assms(1-3,5-9)])

subsection \<open>Refinement of the re-parenting walk\<close>

text \<open>@{const reparent_walk_imp} reverses the parent pointers along the spine in place. It both
      \<^emph>\<open>reads and mutates\<close> the parent-edge / direction stores, so its refinement carries a
      \<^emph>\<open>store agreement invariant\<close>: on the still-unvisited suffix of the spine the mutable
      stores @{term Pe}, @{term D} still agree with the frozen functional state @{term s} --- maintained
      because the spine is @{term distinct}, so each visited vertex leaves the suffix untouched. The reads
      therefore see the original @{term \<open>par_edge s\<close>} / @{term \<open>par_up s\<close>} that
      @{const reparent_walk} threads.\<close>
lemma reparent_walk_imp_rule:
  "\<lbrakk>parent_invar Pe; dir_invar D; ptr \<le> length l; e \<in> \<E>;
    distinct (drop i (take ptr l));
    \<forall>w \<in> set (drop i (take ptr l)). w \<in> \<V> - {r};
    \<forall>w \<in> set (drop i (take ptr l)).
      parent_lookup Pe w = par_edge s w \<and> dir_lookup D w = par_up s w\<rbrakk> \<Longrightarrow>
   <rd * parent_assn Pe (iparent si) * dir_assn D (idir si) * pa \<mapsto>\<^sub>a l>
     reparent_walk_imp si e v first pe pup pa i ptr
   <\<lambda>_. rd * (case reparent_walk s e v first pe pup (drop i (take ptr l)) (Pe, D) of (Pe', D') \<Rightarrow>
          parent_assn Pe' (iparent si) * dir_assn D' (idir si) * pa \<mapsto>\<^sub>a l)>"
proof(induction "ptr - i" arbitrary: i Pe D first pe pup)
  case (Suc k)
  have k: "k = ptr - Suc i" "\<not> ptr \<le> i" "i < length l"
    "drop i (take ptr l) = l ! i # drop (Suc i) (take ptr l)"
    using Suc.hyps(2) Suc.prems(3)
    by (simp_all add: Cons_nth_drop_Suc[symmetric])
  have v: "l ! i \<in> \<V> - {r}" "l ! i \<in> \<V>" "l ! i \<noteq> r"
    "parent_lookup Pe (l ! i) = par_edge s (l ! i)"
    "dir_lookup D (l ! i) = par_up s (l ! i)" "distinct (drop (Suc i) (take ptr l))"
    "\<forall>w \<in> set (drop (Suc i) (take ptr l)). w \<in> \<V> - {r}"
    "\<forall>w \<in> set (drop (Suc i) (take ptr l)). parent_lookup (parent_upd Pe (l ! i) x) w = par_edge s w
       \<and> dir_lookup (dir_upd D (l ! i) y) w = par_up s w" for x y
    using Suc.prems(5-7) k(4)
    by (auto simp: parent_arr.fixed_univ_map_upd[OF Suc.prems(1)] dir_arr.fixed_univ_map_upd[OF Suc.prems(2)])
  note IH = Suc.hyps(1)[OF k(1) parent_arr.fixed_univ_map_upd_invar[OF Suc.prems(1) v(1)]
      dir_arr.fixed_univ_map_upd_invar[OF Suc.prems(2) v(1)] Suc.prems(3,4) v(6,7)]
  show ?case
    by (subst reparent_walk_imp.simps; sep_auto simp: par_edge_imp_def par_up_imp_def k(2-4) v(2-5,8)
      Suc.prems(1,2,4) parent_arr.fixed_univ_map_upd_invar[OF Suc.prems(1) v(1)]
      dir_arr.fixed_univ_map_upd_invar[OF Suc.prems(2) v(1)] heap: IH IH[simplified])
qed (subst reparent_walk_imp.simps, sep_auto simp: drop_take)

text \<open>At the top level (@{term \<open>i = 0\<close>}) the stores are the frozen originals, so the agreement
      invariant holds by definition of @{const par_edge} / @{const par_up}.\<close>
lemma reparent_imp_rule:
  "\<lbrakk>parent_invar (parent_edge s); dir_invar (edge_dir s); ptr \<le> length l; e \<in> \<E>;
    distinct (take ptr l); \<forall>w \<in> set (take ptr l). w \<in> \<V> - {r}\<rbrakk> \<Longrightarrow>
   <rd * parent_assn (parent_edge s) (iparent si) * dir_assn (edge_dir s) (idir si) * pa \<mapsto>\<^sub>a l>
     reparent_imp si e pa ptr v
   <\<lambda>_. rd * (case reparent s e (take ptr l) v of (Pe', D') \<Rightarrow>
          parent_assn Pe' (iparent si) * dir_assn D' (idir si) * pa \<mapsto>\<^sub>a l)>"
  unfolding reparent_imp_def reparent_def
  by (rule reparent_walk_imp_rule[where i = 0, unfolded drop_0]) (simp_all add: par_edge_def par_up_def)

subsection \<open>Refinement of the full pivot\<close>

text \<open>@{const ns_pivot_imp} performs the whole pivot in place: it reads the leaving edge @{term e0}
      \<^emph>\<open>before\<close> re-parenting overwrites it, augments the flow, shifts the potentials over
      the far side (reading the \<^emph>\<open>old\<close> tree before the swap), re-parents the spine, swaps
      the tree edge, and moves @{term e} into the tree and @{term e0} into @{term U}/@{term L}. It refines
      @{const ns_pivot} on the six mutated stores. The assumptions are the union of the sub-operations'
      preconditions, including the @{locale arborescense_adt} @{text swap_edge} witnesses (spine @{term psw1},
      join arc @{term a}, tail @{term p3}, leaving arc @{term \<open>(v, y)\<close>}).\<close>
lemma ns_pivot_imp_rule:
  assumes "flow_invar (current_flow s)" "pot_invar (potentials s)"
    "\<And>u. u \<in> \<V> \<Longrightarrow> pot_value_invar (pot_lookup (potentials s) u)"
    "arborescense_invar (spanning_tree s)"
    "parent_invar (parent_edge s)" "dir_invar (edge_dir s)" "es_invar (edge_state s)"
    "e \<in> \<E>" "par_edge s v \<in> \<E>" "v \<in> \<V> - {r}" "eu = fst_exec e" "ev = snd_exec e"
    "ptr1 \<le> length l1" "ptr2 \<le> length l2"
    "\<forall>w \<in> set (take ptr1 l1). w \<in> \<V> - {r} \<and> par_edge s w \<in> \<E>"
    "\<forall>w \<in> set (take ptr2 l2). w \<in> \<V> - {r} \<and> par_edge s w \<in> \<E>"
    "distinct (take ptr1 l1)" "distinct (take ptr2 l2)"
    "get_path_pair (spanning_tree s) (if in_U = up_side then eu else ev)
        (if in_U = up_side then ev else eu) = (psw1, psw2)"
    "eu \<noteq> ev"
    "walk_betw (abstract_arborescense (spanning_tree s)) (if in_U = up_side then eu else ev)
        (psw1 @ a # p3) r"
    "distinct (psw1 @ a # p3)" "(v, y) \<in> set (edges_of_vwalk (psw1 @ [a]))"
    "eu \<in> \<V>" "ev \<in> \<V>"
  shows "<rd * flow_assn (current_flow s) (iflow si) * pot_assn (potentials s) (ipot si)
      * tree_assn (spanning_tree s) (itree si) * parent_assn (parent_edge s) (iparent si)
      * dir_assn (edge_dir s) (idir si) * es_assn (edge_state s) (iestate si)
      * ipath1 si \<mapsto>\<^sub>a l1 * ipath2 si \<mapsto>\<^sub>a l2>
     ns_pivot_imp si e eu ev in_U \<gamma> \<delta> v e0fwd up_side ptr1 ptr2
   <\<lambda>_. rd * flow_assn (augment_flow s e in_U \<delta> (take ptr1 l1) (take ptr2 l2)) (iflow si)
      * pot_assn (shift_pot (spanning_tree s) v (potentials s) \<gamma> (in_U \<noteq> up_side)) (ipot si)
      * tree_assn (swap_edge (spanning_tree s) v (if in_U = up_side then eu else ev)
                     (if in_U = up_side then ev else eu)) (itree si)
      * (case reparent s e (if in_U = up_side then take ptr1 l1 else take ptr2 l2) v of (Pe', D') \<Rightarrow>
           parent_assn Pe' (iparent si) * dir_assn D' (idir si))
      * es_assn (es_upd (es_upd (edge_state s) e InTree) (par_edge s v)
                   (if e0fwd then InU else InL)) (iestate si)
      * ipath1 si \<mapsto>\<^sub>a l1 * ipath2 si \<mapsto>\<^sub>a l2>"
proof(cases "in_U = up_side")
  case True
  obtain Pe D where "reparent s e (take ptr1 l1) v = (Pe, D)"
    by fastforce
  then show ?thesis
    unfolding ns_pivot_imp_def Let_def
    by (sep_auto simp: True assms(5-9,17) assms(10,15,16)[simplified]
      es_arr.fixed_univ_map_upd_invar[OF assms(7,8)]
    heap: augment_flow_imp_rule[OF assms(1,5,6,8,13-16)] shift_pot_rule[OF assms(4) _ assms(2,3)]
      reparent_imp_rule[OF assms(5,6,13,8,17)] swap_edge_rule[OF assms(4) assms(19)[unfolded if_P[OF True]]
      assms(20) assms(21)[unfolded if_P[OF True]] assms(22-25)])
next
  case False
  obtain Pe D where "reparent s e (take ptr2 l2) v = (Pe, D)"
    by fastforce
  then show ?thesis
    unfolding ns_pivot_imp_def Let_def
    by (sep_auto simp: False assms(5-9,18) assms(10,15,16)[simplified]
      es_arr.fixed_univ_map_upd_invar[OF assms(7,8)]
    heap: augment_flow_imp_rule[OF assms(1,5,6,8,13-16)] shift_pot_rule[OF assms(4) _ assms(2,3)]
      reparent_imp_rule[OF assms(5,6,14,8,18)] swap_edge_rule[OF assms(4) assms(19)[unfolded if_not_P[OF False]]
      assms(20)[symmetric] assms(21)[unfolded if_not_P[OF False]] assms(22,23,25,24)])
qed

subsection \<open>Refinement of the whole loop\<close>

text \<open>A triple from @{const ns_rel} also holds with the two path buffers opened, for any concrete
      buffers that are long enough.\<close>
lemma ns_rel_cont:
  "\<lbrakk><ns_rel t si> c <Q>; card \<V> - 1 \<le> length l1; card \<V> - 1 \<le> length l2\<rbrakk>
   \<Longrightarrow> <rd * flow_assn (current_flow t) (iflow si) * pot_assn (potentials t) (ipot si)
      * tree_assn (spanning_tree t) (itree si) * parent_assn (parent_edge t) (iparent si)
      * dir_assn (edge_dir t) (idir si) * es_assn (edge_state t) (iestate si)
      * sel_assn (edge_sel t) (isel si) * ipath1 si \<mapsto>\<^sub>a l1 * ipath2 si \<mapsto>\<^sub>a l2> c <Q>"
  unfolding ns_rel_def
  by (erule ht_cons_pre[rotated], simp only: ex_assn_move_out)
    (rule ent_ex_postI[where x = l1], rule ent_ex_postI[where x = l2], sep_auto)

text \<open>One loop iteration from a state satisfying @{const ns_invar}: the store invariants, the
      fundamental-circuit well-formedness and the step-preservation facts all follow from
      \<open>Network_Simplex_Preservation\<close>. On the \<^emph>\<open>pivot\<close> branch the spine also
      carries the leaving edge @{term \<open>par_edge s vv\<close>} as one of its @{const edges_of_vwalk} arcs
      --- the well-formedness the \<open>swap_edge\<close> refinement axiom needs
      (\<open>loop_step_swap\<close>).\<close>

context
  fixes s :: "('farr, 'parr, 'arbor, 'pearr, 'darr, 'earr, 'selector) network_simplex_state"
    and e in_U \<gamma> sel' p1 p2
  assumes inv: "ns_invar s" and sel: "ns_select s = Some (e, in_U, \<gamma>, sel')"
    and gpp: "get_path_pair (spanning_tree s) (fst_exec e) (snd_exec e) = (p1, p2)"
begin

lemma loop_step_entering:
  "e \<in> \<E>" "get_path_pair (spanning_tree s) (fst e) (snd e) = (p1, p2)" "fst_exec e = fst e" "snd_exec e = snd e"
  using ns_select_SomeD(2)[OF inv sel] gpp
  by simp_all

lemma loop_step_facts:
  "sel_invar (edge_sel s)" "pot_invar (potentials s)" "es_invar (edge_state s)"
  "flow_invar (current_flow s)" "parent_invar (parent_edge s)" "dir_invar (edge_dir s)"
  "arborescense_invar (spanning_tree s)" "u \<in> \<V> \<Longrightarrow> pot_value_invar (pot_lookup (potentials s) u)"
  "fst e \<noteq> snd e" "fst e \<in> \<V>" "snd e \<in> \<V>"
  "\<forall>w \<in> set p1. w \<in> \<V> - {r} \<and> par_edge s w \<in> \<E>"
  "\<forall>w \<in> set p2. w \<in> \<V> - {r} \<and> par_edge s w \<in> \<E>"
  using ns_invar_implD[OF ns_invarD(1)[OF inv]] step_entering(3,8,9)[OF inv sel loop_step_entering(2)]
    select_path_verts[OF inv sel loop_step_entering(2)] step_path_edges(1,2)[OF inv sel loop_step_entering(2)]
  unfolding pot_valid_def
  by blast+

lemma loop_step_distinct: "distinct p1" "distinct p2"
  using step_paths(3,4)[OF inv sel loop_step_entering(2)]
  by (cases in_U; simp)+

lemma loop_step_flip:
  "\<lbrakk>bottleneck s e in_U p1 p2 = (\<delta>, True, vv, e0fwd, up_side); \<delta> \<noteq> - 1\<rbrakk>
   \<Longrightarrow> ns_invar (ns_flip s e in_U \<gamma> sel' \<delta> p1 p2)"
  using ns_flip_preservation(1)[OF inv] sel gpp
  by (simp add: ns_flip_cond_def ns_flip_upd_def)

lemma loop_step_pivot:
  "\<lbrakk>bottleneck s e in_U p1 p2 = (\<delta>, False, vv, e0fwd, up_side); \<delta> \<noteq> - 1\<rbrakk>
   \<Longrightarrow> vv \<in> \<V> - {r} \<and> par_edge s vv \<in> \<E>
     \<and> ns_invar (ns_pivot s e in_U \<gamma> sel' \<delta> vv e0fwd up_side p1 p2)"
  using pivot_facts(1)[OF inv sel loop_step_entering(2)] ns_invar_tree_edgeD[OF ns_invarD(7)[OF inv]]
    ns_pivot_preservation(1)[OF inv] sel gpp
  by (simp add: ns_pivot_cond_def ns_pivot_upd_def)

lemma loop_step_swap:
  assumes "bottleneck s e in_U p1 p2 = (\<delta>, False, vv, e0fwd, up_side)" "\<delta> \<noteq> - 1"
  obtains a p3 y where
    "get_path_pair (spanning_tree s) (if in_U = up_side then fst e else snd e)
       (if in_U = up_side then snd e else fst e)
      = (if in_U = up_side then p1 else p2, if in_U = up_side then p2 else p1)"
    "walk_betw (abstract_arborescense (spanning_tree s)) (if in_U = up_side then fst e else snd e)
       ((if in_U = up_side then p1 else p2) @ a # p3) r"
    "distinct ((if in_U = up_side then p1 else p2) @ a # p3)"
    "(vv, y) \<in> set (edges_of_vwalk ((if in_U = up_side then p1 else p2) @ [a]))"
proof-
  let ?P = "if in_U = up_side then p1 else p2"
  obtain a p3 where w: "walk_betw (abstract_arborescense (spanning_tree s)) (if in_U = up_side then fst e else snd e)
      (?P @ a # p3) r" "distinct (?P @ a # p3)"
    using step_walks(1)[OF inv sel loop_step_entering(2)]
    by (cases "in_U = up_side") auto
  obtain j where j: "j < length ?P" "?P ! j = vv"
    using pivot_facts(5)[OF inv sel loop_step_entering(2) assms]
    by (auto simp: in_set_conv_nth)
  then have "(?P @ [a]) ! Suc j = par_vx s vv"
    using walk_succ_is_par_vx[OF inv w, of j] pivot_facts(1)[OF inv sel loop_step_entering(2) assms]
    by (cases "Suc j = length ?P") (simp_all add: nth_append)
  then have "(vv, par_vx s vv) \<in> set (edges_of_vwalk (?P @ [a]))"
    using edges_of_vwalk_index[of j "?P @ [a]"] nth_mem[of j "edges_of_vwalk (?P @ [a])"] j
    by (simp add: edges_of_vwalk_length nth_append)
  then show ?thesis
    using that[of a p3] w loop_step_entering(2) get_path_pair(2)[OF loop_step_facts(7) loop_step_entering(2)]
      loop_step_facts(9-11)
    by (cases "in_U = up_side") auto
qed

text \<open>The rest of an iteration once the two paths sit in the buffers: run the bottleneck scan and
      take the unbounded, flip or pivot branch, handing the new state to the continuation @{term c}.\<close>
lemma loop_step_tail:
  assumes "ptr1 \<le> length l1" "ptr2 \<le> length l2" "take ptr1 l1 = p1" "take ptr2 l2 = p2"
    "card \<V> - 1 \<le> length l1" "card \<V> - 1 \<le> length l2" "u = fst e" "v = snd e"
    "\<And>t. ns_invar t \<Longrightarrow> <ns_rel t si> c
       <\<lambda>res. ns_rel_weak (ns_loop_impl t) si * \<up>(res = network_simplex_state.return (ns_loop_impl t))>"
  shows "<rd * flow_assn (current_flow s) (iflow si) * pot_assn (potentials s) (ipot si)
      * tree_assn (spanning_tree s) (itree si) * parent_assn (parent_edge s) (iparent si)
      * dir_assn (edge_dir s) (idir si) * es_assn (edge_state s) (iestate si) * sel_assn sel' (isel si)
      * ipath1 si \<mapsto>\<^sub>a l1 * ipath2 si \<mapsto>\<^sub>a l2>
     do {
       bn \<leftarrow> bottleneck_imp si e in_U ptr1 ptr2;
       (case bn of (\<delta>, is_flip, vv, e0fwd, up_side) \<Rightarrow>
          if \<delta> = - 1 then Heap_Monad.return Network_Simplex.unbounded
          else if is_flip then do { _ \<leftarrow> ns_flip_imp si e in_U \<delta> ptr1 ptr2; c }
          else do { _ \<leftarrow> ns_pivot_imp si e u v in_U \<gamma> \<delta> vv e0fwd up_side ptr1 ptr2; c })
     }
   <\<lambda>res. ns_rel_weak (ns_loop_impl s) si * \<up>(res = network_simplex_state.return (ns_loop_impl s))>"
proof-
  obtain \<delta> is_flip vv e0fwd up_side
    where bn: "bottleneck s e in_U p1 p2 = (\<delta>, is_flip, vv, e0fwd, up_side)"
    by (cases "bottleneck s e in_U p1 p2") auto
  note B = bottleneck_imp_rule[OF loop_step_facts(4-6) loop_step_entering(1) assms(1,2)
      loop_step_facts(12,13)[folded assms(3,4)], where in_U = in_U, unfolded assms(3,4) bn]
  note F = loop_step_facts loop_step_distinct loop_step_entering bn assms(1-4,7,8)
    assms(5,6)[unfolded One_nat_def]
  show ?thesis
  proof(cases "\<delta> = - 1")
    case True
    have "ns_loop_impl s = ns_unbounded_upd s"
      using sel gpp bn True
      by (simp add: ns_loop_impl_simps(2) ns_unbounded_cond_def)
    then show ?thesis
      unfolding ns_rel_weak_def
      by (sep_auto simp: True F ns_unbounded_upd_def heap: B)
  next
    case False
    show ?thesis
    proof(cases is_flip)
      case True
      have "ns_loop_impl s = ns_loop_impl (ns_flip s e in_U \<gamma> sel' \<delta> p1 p2)"
        using sel gpp bn True \<open>\<delta> \<noteq> - 1\<close>
        by (simp add: ns_loop_impl_simps(3) ns_flip_cond_def ns_flip_upd_def)
      moreover obtain st where st: "(if in_U then InL else InU) = st"
        by simp
      ultimately show ?thesis
        unfolding ns_flip_def st
        by (sep_auto simp: True \<open>\<delta> \<noteq> - 1\<close> F heap: B
          ns_flip_imp_rule[OF loop_step_facts(4-6,3) loop_step_entering(1) assms(1,2)
            loop_step_facts(12,13)[folded assms(3,4)], where in_U = in_U, unfolded assms(3,4) st]
          ns_rel_cont[OF assms(9)[OF loop_step_flip[OF bn[simplified True] \<open>\<delta> \<noteq> - 1\<close>]]
            assms(5,6),
            unfolded ns_flip_def st, simplified])
    next
      case False
      obtain Pe D where rp: "reparent s e (if in_U = up_side then p1 else p2) vv = (Pe, D)"
        by fastforce
      obtain a1 b1 st where fo: "(if in_U = up_side then fst e else snd e) = a1"
        "(if in_U = up_side then snd e else fst e) = b1" "(if e0fwd then InU else InL) = st"
        by simp
      note P = loop_step_pivot[OF bn[simplified False] \<open>\<delta> \<noteq> - 1\<close>]
      have L: "ns_loop_impl s = ns_loop_impl (ns_pivot s e in_U \<gamma> sel' \<delta> vv e0fwd up_side p1 p2)"
        using sel gpp bn False \<open>\<delta> \<noteq> - 1\<close>
        by (simp add: ns_loop_impl_simps(4) ns_pivot_cond_def ns_pivot_upd_def)
      show ?thesis
        unfolding L ns_pivot_def Let_def rp prod.case loop_step_entering(3,4) fo
      proof(rule loop_step_swap[OF bn[simplified False] \<open>\<delta> \<noteq> - 1\<close>], goal_cases)
        case (1 a p3 y)
        show ?case
          by (sep_auto simp: False \<open>\<delta> \<noteq> - 1\<close> F heap: B
            ns_pivot_imp_rule[OF loop_step_facts(4,2,8,7,5,6,3) loop_step_entering(1) conjunct1[OF conjunct2[OF P]]
              conjunct1[OF P] loop_step_entering(3,4)[symmetric] assms(1,2) loop_step_facts(12,13)[folded assms(3,4)]
              loop_step_distinct[folded assms(3,4)] 1(1) loop_step_facts(9) 1(2-4) loop_step_facts(10,11),
              where e0fwd = e0fwd, unfolded assms(3,4) rp prod.case fo]
            ns_rel_cont[OF assms(9)[OF conjunct2[OF conjunct2[OF P]]] assms(5,6),
              unfolded ns_pivot_def Let_def rp prod.case loop_step_entering(3,4) fo, simplified])
      qed
    qed
  qed
qed

end

text \<open>One iteration of @{const ns_loop_imp}, with the recursive call abstracted to @{term c}: if
      @{term c} refines @{const ns_loop_impl} on every invariant state, so does the loop body.\<close>
lemma ns_loop_step:
  assumes "ns_invar s"
    "\<And>t. ns_invar t \<Longrightarrow> <ns_rel t si> c
       <\<lambda>res. ns_rel_weak (ns_loop_impl t) si * \<up>(res = network_simplex_state.return (ns_loop_impl t))>"
  shows "<ns_rel s si>
     do {
       sel \<leftarrow> ns_select_imp si;
       (case sel of
          None \<Rightarrow> Heap_Monad.return Network_Simplex.success
        | Some (e, in_U, \<gamma>) \<Rightarrow>
            do {
              u \<leftarrow> fst_exec_imp e;
              v \<leftarrow> snd_exec_imp e;
              (ptr1, ptr2) \<leftarrow> get_path_pair_imp (itree si) u v (ipath1 si) (ipath2 si);
              bn \<leftarrow> bottleneck_imp si e in_U ptr1 ptr2;
              (case bn of (\<delta>, is_flip, vv, e0fwd, up_side) \<Rightarrow>
                 if \<delta> = - 1 then Heap_Monad.return Network_Simplex.unbounded
                 else if is_flip then do { _ \<leftarrow> ns_flip_imp si e in_U \<delta> ptr1 ptr2; c }
                 else do { _ \<leftarrow> ns_pivot_imp si e u v in_U \<gamma> \<delta> vv e0fwd up_side ptr1 ptr2; c })
            })
     }
   <\<lambda>res. ns_rel_weak (ns_loop_impl s) si * \<up>(res = network_simplex_state.return (ns_loop_impl s))>"
proof(cases "ns_select s")
  case None
  then show ?thesis
    unfolding ns_rel_def ns_rel_weak_def
    by (sep_auto simp: None ns_loop_impl.simps ns_optimal_def
      ns_invar_implD(2,5,6)[OF ns_invarD(1)[OF assms(1)], unfolded pot_valid_def]
      heap: ns_select_imp_rule[of s, unfolded None option.case])
next
  case (Some x)
  obtain e in_U \<gamma> sel' where sel: "ns_select s = Some (e, in_U, \<gamma>, sel')"
    using Some
    by (cases x) auto
  obtain p1 p2 where gpp: "get_path_pair (spanning_tree s) (fst_exec e) (snd_exec e) = (p1, p2)"
    by fastforce
  note E = loop_step_entering[OF assms(1) sel gpp]
  obtain T where T: "\<And>e in_U \<gamma> u v ptr1 ptr2. do {
       bn \<leftarrow> bottleneck_imp si e in_U ptr1 ptr2;
       (case bn of (\<delta>, is_flip, vv, e0fwd, up_side) \<Rightarrow>
          if \<delta> = - 1 then Heap_Monad.return Network_Simplex.unbounded
          else if is_flip then do { _ \<leftarrow> ns_flip_imp si e in_U \<delta> ptr1 ptr2; c }
          else do { _ \<leftarrow> ns_pivot_imp si e u v in_U \<gamma> \<delta> vv e0fwd up_side ptr1 ptr2; c })
     } = T e in_U \<gamma> u v ptr1 ptr2"
    by (rule that, rule refl)
  show ?thesis
    unfolding ns_rel_def T
    by (sep_auto simp: E loop_step_facts(7,9-11)[OF assms(1) sel gpp]
      heap: ns_select_imp_rule[OF loop_step_facts(1-3)[OF assms(1) sel gpp], unfolded sel option.case prod.case]
      loop_step_tail[OF assms(1) sel gpp _ _ _ _ _ _ _ _ assms(2), unfolded T])
qed

text \<open>The imperative loop @{const ns_loop_imp} refines the functional @{const ns_loop_impl} under the
      single, natural precondition @{term \<open>ns_invar s\<close>}, by
      \<^emph>\<open>fixpoint induction\<close> on the heap @{command partial_function}. The six interface
      lemmas above supply everything each iteration needs; here we only assemble them. Under partial
      correctness a diverging run makes the triple hold vacuously, so no termination argument is needed.\<close>

lemma ns_loop_imp_rule:
  "ns_invar s \<longrightarrow> <ns_rel s si> ns_loop_imp si
     <\<lambda>res. ns_rel_weak (ns_loop_impl s) si * \<up>(res = network_simplex_state.return (ns_loop_impl s))>"
proof(induction arbitrary: s rule: ns_loop_imp.fixp_induct)
  case (3 f s)
  show ?case
    using ns_loop_step[of s si "f si"] "3.IH"
    by blast
qed simp_all

text \<open>The refinement above is stated against the heap @{command partial_function}
      @{const ns_loop_impl}, but the functional correctness theorems live on the @{command function}
      @{const ns_loop}. Under @{term \<open>ns_invar s\<close>} the loop terminates (@{text ns_loop_dom_of_invar}),
      so the two agree (@{text ns_loop_dom_impl_same}); transferring along that equality lands the
      imperative result on the \<^emph>\<open>final functional state\<close> @{term \<open>ns_loop s\<close>}.\<close>

lemma ns_loop_imp_correct:
  assumes "ns_invar s"
  shows "<ns_rel s si> ns_loop_imp si
           <\<lambda>res. ns_rel_weak (ns_loop s) si * \<up>(res = network_simplex_state.return (ns_loop s))>"
  using assms ns_loop_imp_rule[of s si]
  by (simp add: ns_loop_dom_impl_same ns_loop_dom_of_invar)
end


section \<open>Correctness against the functional loop and the initial basis\<close>

text \<open>Merging the initial-basis proof locale @{locale network_simplex_init} with the imperative
      refinement locale @{locale network_simplex_impl_refine}: the loop-refinement corollary
      \<open>ns_loop_imp_correct\<close> (which already talks about the terminating function \<open>ns_loop\<close>)
      specialises to the constructed initial state.\<close>

locale network_simplex_init_impl_refine =
  network_simplex_impl_refine + network_simplex_init
begin

text \<open>Specialised to the initial basis built by @{locale network_simplex_init}: since
      @{text init_state_invar} gives @{term \<open>ns_invar init_state\<close>}, the imperative loop started
      from any heap refining \<open>init_state\<close> refines the functional run
      @{term \<open>ns_loop init_state\<close>} --- the state on which @{text network_simplex_correct} states
      optimality / unboundedness.\<close>

lemma ns_loop_imp_init:
  "<ns_rel init_state si> ns_loop_imp si
     <\<lambda>res. ns_rel_weak (ns_loop init_state) si
              * \<up>(res = network_simplex_state.return (ns_loop init_state))>"
  using init_state_invar
  by (rule ns_loop_imp_correct)

end

end

