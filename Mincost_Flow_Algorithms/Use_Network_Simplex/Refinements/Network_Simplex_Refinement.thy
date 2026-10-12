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
    ptr \<le> length l; \<forall>v \<in> set (drop i (take ptr l)). v \<in> \<V> - {r} \<and> par_edge s v \<in> \<E>\<rbrakk> \<Longrightarrow>
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
proof (induction "ptr - i" arbitrary: i m0 best0)
  case 0
  hence le: "ptr \<le> i" by simp
  show ?case
    by (subst scan_up_loop_imp.simps) (sep_auto simp: le drop_take)
next
  case (Suc k)
  from Suc.hyps(2) have iltptr: "i < ptr" by simp
  hence niltptr: "\<not> ptr \<le> i" by simp
  have iltl: "i < length l" using iltptr Suc.prems(4) by simp
  have lt: "i < length (take ptr l)" using iltptr Suc.prems(4) by simp
  have dec: "drop i (take ptr l) = l ! i # drop (Suc i) (take ptr l)"
    using lt iltptr by (simp add: Cons_nth_drop_Suc[symmetric] nth_take)
  have kval: "k = ptr - Suc i" using Suc.hyps(2) iltptr by simp
  have vin: "l ! i \<in> \<V> - {r}" "par_edge s (l ! i) \<in> \<E>" using Suc.prems(5) dec by auto
  have subprem: "\<forall>v \<in> set (drop (Suc i) (take ptr l)). v \<in> \<V> - {r} \<and> par_edge s v \<in> \<E>"
    using Suc.prems(5) dec by auto
  note IH = Suc.hyps(1)[OF kval Suc.prems(1) Suc.prems(2) Suc.prems(3) Suc.prems(4) subprem]
  have vinV: "l ! i \<in> \<V>" and vinr: "l ! i \<noteq> r" using vin(1) by auto
  show ?case
    by (subst scan_up_loop_imp.simps)
       (sep_auto simp: niltptr dec iltl vinV vinr vin(2)
                       Suc.prems(1) Suc.prems(2) Suc.prems(3)
                 split: if_splits heap: IH)
qed

text \<open>The downward scan is the mirror image, using @{const res_down} and a \<^emph>\<open>strict\<close> comparison.\<close>
lemma scan_down_loop_imp_rule:
  "\<lbrakk>flow_invar (current_flow s); parent_invar (parent_edge s); dir_invar (edge_dir s);
    ptr \<le> length l; \<forall>v \<in> set (drop i (take ptr l)). v \<in> \<V> - {r} \<and> par_edge s v \<in> \<E>\<rbrakk> \<Longrightarrow>
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
proof (induction "ptr - i" arbitrary: i m0 best0)
  case 0
  hence le: "ptr \<le> i" by simp
  show ?case
    by (subst scan_down_loop_imp.simps) (sep_auto simp: le drop_take)
next
  case (Suc k)
  from Suc.hyps(2) have iltptr: "i < ptr" by simp
  hence niltptr: "\<not> ptr \<le> i" by simp
  have iltl: "i < length l" using iltptr Suc.prems(4) by simp
  have lt: "i < length (take ptr l)" using iltptr Suc.prems(4) by simp
  have dec: "drop i (take ptr l) = l ! i # drop (Suc i) (take ptr l)"
    using lt iltptr by (simp add: Cons_nth_drop_Suc[symmetric] nth_take)
  have kval: "k = ptr - Suc i" using Suc.hyps(2) iltptr by simp
  have vin: "l ! i \<in> \<V> - {r}" "par_edge s (l ! i) \<in> \<E>" using Suc.prems(5) dec by auto
  have subprem: "\<forall>v \<in> set (drop (Suc i) (take ptr l)). v \<in> \<V> - {r} \<and> par_edge s v \<in> \<E>"
    using Suc.prems(5) dec by auto
  note IH = Suc.hyps(1)[OF kval Suc.prems(1) Suc.prems(2) Suc.prems(3) Suc.prems(4) subprem]
  have vinV: "l ! i \<in> \<V>" and vinr: "l ! i \<noteq> r" using vin(1) by auto
  show ?case
    by (subst scan_down_loop_imp.simps)
       (sep_auto simp: niltptr dec iltl vinV vinr vin(2)
                       Suc.prems(1) Suc.prems(2) Suc.prems(3)
                 split: if_splits heap: IH)
qed

text \<open>Snoc recurrences of the two scans (left @{const fold}), and the consequence used below: when a
      scan reports a finite minimum (first component not the \<open>- 1\<close> sentinel) its minimiser is a genuine
      element of the scanned path --- hence, under the path precondition, a non-root vertex on which
      @{const par_up_imp} is specified.\<close>
lemma scan_up_snoc:
  "scan_up s (xs @ [x]) =
     (case scan_up s xs of (m, best) \<Rightarrow>
        (let rr = res_up s x in
         if rr = - 1 then (m, best) else if m = - 1 then (rr, x)
         else if rr \<le> m then (rr, x) else (m, best)))"
  by (simp add: scan_up_def)

lemma scan_down_snoc:
  "scan_down s (xs @ [x]) =
     (case scan_down s xs of (m, best) \<Rightarrow>
        (let rr = res_down s x in
         if rr = - 1 then (m, best) else if m = - 1 then (rr, x)
         else if rr < m then (rr, x) else (m, best)))"
  by (simp add: scan_down_def)

lemma scan_up_snd_mem:
  "scan_up s p = (m, best) \<Longrightarrow> m \<noteq> - 1 \<Longrightarrow> best \<in> set p"
proof (induction p arbitrary: m best rule: rev_induct)
  case Nil thus ?case by (simp add: scan_up_def)
next
  case (snoc x xs)
  obtain m' best' where mb: "scan_up s xs = (m', best')" by fastforce
  show ?case
    using snoc.prems snoc.IH[OF mb] mb
    by (auto simp: scan_up_snoc Let_def split: if_splits)
qed

lemma scan_down_snd_mem:
  "scan_down s p = (m, best) \<Longrightarrow> m \<noteq> - 1 \<Longrightarrow> best \<in> set p"
proof (induction p arbitrary: m best rule: rev_induct)
  case Nil thus ?case by (simp add: scan_down_def)
next
  case (snoc x xs)
  obtain m' best' where mb: "scan_down s xs = (m', best')" by fastforce
  show ?case
    using snoc.prems snoc.IH[OF mb] mb
    by (auto simp: scan_down_snoc Let_def split: if_splits)
qed

text \<open>Seeded at index @{term 0} with @{term \<open>(- 1, r)\<close>}, the loops refine the top-level
      @{const scan_up} / @{const scan_down} on the buffer prefix @{term \<open>take ptr l\<close>}.\<close>
lemma scan_up_imp_rule:
  assumes "flow_invar (current_flow s)" "parent_invar (parent_edge s)" "dir_invar (edge_dir s)"
    "ptr \<le> length l" "\<forall>v \<in> set (take ptr l). v \<in> \<V> - {r} \<and> par_edge s v \<in> \<E>"
  shows "<flow_assn (current_flow s) (iflow si) * parent_assn (parent_edge s) (iparent si)
      * dir_assn (edge_dir s) (idir si) * pa \<mapsto>\<^sub>a l * rd>
     scan_up_imp si pa ptr
   <\<lambda>res. flow_assn (current_flow s) (iflow si) * parent_assn (parent_edge s) (iparent si)
      * dir_assn (edge_dir s) (idir si) * pa \<mapsto>\<^sub>a l * rd * \<up>(res = scan_up s (take ptr l))>"
proof -
  have P5: "\<forall>v \<in> set (drop 0 (take ptr l)). v \<in> \<V> - {r} \<and> par_edge s v \<in> \<E>"
    using assms(5) by simp
  show ?thesis
    unfolding scan_up_imp_def
    by (rule ht_cons_post[OF scan_up_loop_imp_rule[OF assms(1) assms(2) assms(3) assms(4) P5]])
       (sep_auto simp: scan_up_def)
qed

lemma scan_down_imp_rule:
  assumes "flow_invar (current_flow s)" "parent_invar (parent_edge s)" "dir_invar (edge_dir s)"
    "ptr \<le> length l" "\<forall>v \<in> set (take ptr l). v \<in> \<V> - {r} \<and> par_edge s v \<in> \<E>"
  shows "<flow_assn (current_flow s) (iflow si) * parent_assn (parent_edge s) (iparent si)
      * dir_assn (edge_dir s) (idir si) * pa \<mapsto>\<^sub>a l * rd>
     scan_down_imp si pa ptr
   <\<lambda>res. flow_assn (current_flow s) (iflow si) * parent_assn (parent_edge s) (iparent si)
      * dir_assn (edge_dir s) (idir si) * pa \<mapsto>\<^sub>a l * rd * \<up>(res = scan_down s (take ptr l))>"
proof -
  have P5: "\<forall>v \<in> set (drop 0 (take ptr l)). v \<in> \<V> - {r} \<and> par_edge s v \<in> \<E>"
    using assms(5) by simp
  show ?thesis
    unfolding scan_down_imp_def
    by (rule ht_cons_post[OF scan_down_loop_imp_rule[OF assms(1) assms(2) assms(3) assms(4) P5]])
       (sep_auto simp: scan_down_def)
qed


text \<open>If the circuit bottleneck is finite but is attained neither at the entering edge nor on the
      up-path, then the down-path minimum is itself finite --- so its minimiser is a real vertex.\<close>
lemma bottleneck_down_finite:
  "mininf r_e (mininf mu md) \<noteq> - 1 \<Longrightarrow> r_e \<noteq> mininf r_e (mininf mu md)
     \<Longrightarrow> \<not> (mu \<noteq> - 1 \<and> mu = mininf r_e (mininf mu md)) \<Longrightarrow> md \<noteq> - 1"
  by (auto simp: mininf_def split: if_splits)

text \<open>The whole bottleneck computation refines @{const bottleneck}. It reads the entering edge's
      residual, runs the two scans over the two buffer prefixes (the functional paths
      @{term \<open>take ptr1 l1\<close>} / @{term \<open>take ptr2 l2\<close>}), and --- when a tree edge leaves --- reads the
      leaving vertex's orientation. The scans' minimisers are genuine path vertices (by
      @{thm scan_up_snd_mem} / @{thm scan_down_snd_mem}), hence non-root, so @{const par_up_imp} is
      specified there.\<close>
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
proof -
  have vmem1: "\<And>m best. scan_up s (take ptr1 l1) = (m, best) \<Longrightarrow> m \<noteq> - 1 \<Longrightarrow> best \<in> \<V> - {r}"
    using assms(7) by (fastforce dest: scan_up_snd_mem)
  have vmem1': "\<And>m best. scan_down s (take ptr1 l1) = (m, best) \<Longrightarrow> m \<noteq> - 1 \<Longrightarrow> best \<in> \<V> - {r}"
    using assms(7) by (fastforce dest: scan_down_snd_mem)
  have vmem2: "\<And>m best. scan_up s (take ptr2 l2) = (m, best) \<Longrightarrow> m \<noteq> - 1 \<Longrightarrow> best \<in> \<V> - {r}"
    using assms(8) by (fastforce dest: scan_up_snd_mem)
  have vmem2': "\<And>m best. scan_down s (take ptr2 l2) = (m, best) \<Longrightarrow> m \<noteq> - 1 \<Longrightarrow> best \<in> \<V> - {r}"
    using assms(8) by (fastforce dest: scan_down_snd_mem)
  show ?thesis
  proof (cases in_U)
    case True
    show ?thesis
      unfolding bottleneck_imp_def bottleneck_def
      by (sep_auto simp: True if_P[OF True] Let_def mininf_imp_eq
                         assms(1) assms(2) assms(3) assms(4)
                 dest: vmem1 vmem2' bottleneck_down_finite
                 heap: scan_up_imp_rule[OF assms(1) assms(2) assms(3) assms(5) assms(7)]
                       scan_down_imp_rule[OF assms(1) assms(2) assms(3) assms(6) assms(8)])
  next
    case False
    show ?thesis
      unfolding bottleneck_imp_def bottleneck_def
      by (sep_auto simp: False if_not_P[OF False] Let_def mininf_imp_eq
                         assms(1) assms(2) assms(3) assms(4)
                 dest: vmem2 vmem1' bottleneck_down_finite
                 heap: scan_up_imp_rule[OF assms(1) assms(2) assms(3) assms(6) assms(8)]
                       scan_down_imp_rule[OF assms(1) assms(2) assms(3) assms(5) assms(7)])
  qed
qed

subsection \<open>Refinement of the flow augmentation\<close>

text \<open>@{const aug_loop_imp} folds the parent-edge flow updates over a path-array prefix in place. Since
      @{const augment_flow_imp} always calls it with a \<^emph>\<open>literal\<close> pass flag, we prove the two instances
      separately (avoiding a spurious flag/sign case split): with @{term \<open>on_up = True\<close>} (the up-path,
      sign @{term \<open>if par_up s v then \<delta> else - \<delta>\<close>}) and with @{term \<open>on_up = False\<close>} (the down-path,
      opposite sign). The flow value is threaded through the induction;
      @{thm flow_arr.fixed_univ_map_upd_invar} keeps @{term flow_invar} across each update.\<close>
lemma aug_loop_imp_up_rule:
  "\<lbrakk>flow_invar Fl; parent_invar (parent_edge s); dir_invar (edge_dir s);
    ptr \<le> length l; \<forall>v \<in> set (drop i (take ptr l)). v \<in> \<V> - {r} \<and> par_edge s v \<in> \<E>\<rbrakk> \<Longrightarrow>
   <flow_assn Fl (iflow si) * parent_assn (parent_edge s) (iparent si)
      * dir_assn (edge_dir s) (idir si) * pa \<mapsto>\<^sub>a l>
     aug_loop_imp si pa i ptr \<delta> True
   <\<lambda>_. flow_assn (fold (\<lambda> v f. let a = par_edge s v in
                     flow_upd f a (flow_lookup f a + (if par_up s v then \<delta> else - \<delta>)))
                   (drop i (take ptr l)) Fl) (iflow si)
      * parent_assn (parent_edge s) (iparent si) * dir_assn (edge_dir s) (idir si) * pa \<mapsto>\<^sub>a l>"
proof (induction "ptr - i" arbitrary: i Fl)
  case 0
  hence le: "ptr \<le> i" by simp
  show ?case
    by (subst aug_loop_imp.simps) (sep_auto simp: le drop_take)
next
  case (Suc k)
  from Suc.hyps(2) have iltptr: "i < ptr" by simp
  hence niltptr: "\<not> ptr \<le> i" by simp
  have iltl: "i < length l" using iltptr Suc.prems(4) by simp
  have lt: "i < length (take ptr l)" using iltptr Suc.prems(4) by simp
  have dec: "drop i (take ptr l) = l ! i # drop (Suc i) (take ptr l)"
    using lt iltptr by (simp add: Cons_nth_drop_Suc[symmetric] nth_take)
  have kval: "k = ptr - Suc i" using Suc.hyps(2) iltptr by simp
  have vin: "l ! i \<in> \<V> - {r}" "par_edge s (l ! i) \<in> \<E>" using Suc.prems(5) dec by auto
  have vinV: "l ! i \<in> \<V>" and vinr: "l ! i \<noteq> r" using vin(1) by auto
  have subprem: "\<forall>v \<in> set (drop (Suc i) (take ptr l)). v \<in> \<V> - {r} \<and> par_edge s v \<in> \<E>"
    using Suc.prems(5) dec by auto
  from subprem have subV: "\<And>v. v \<in> set (drop (Suc i) (take ptr l)) \<Longrightarrow> v \<in> \<V>"
    and subr: "\<And>v. v \<in> set (drop (Suc i) (take ptr l)) \<Longrightarrow> v \<noteq> r" by auto
  have finvw: "flow_invar (flow_upd Fl (par_edge s (l ! i)) w)" for w
    by (rule flow_arr.fixed_univ_map_upd_invar[OF Suc.prems(1) vin(2)])
  note IH = Suc.hyps(1)[OF kval]
  show ?case
    by (subst aug_loop_imp.simps)
       (sep_auto simp: niltptr dec vin vinV vinr iltl finvw subprem subV subr Let_def
                       Suc.prems(1) Suc.prems(2) Suc.prems(3) Suc.prems(4) heap: IH)
qed

lemma aug_loop_imp_down_rule:
  "\<lbrakk>flow_invar Fl; parent_invar (parent_edge s); dir_invar (edge_dir s);
    ptr \<le> length l; \<forall>v \<in> set (drop i (take ptr l)). v \<in> \<V> - {r} \<and> par_edge s v \<in> \<E>\<rbrakk> \<Longrightarrow>
   <flow_assn Fl (iflow si) * parent_assn (parent_edge s) (iparent si)
      * dir_assn (edge_dir s) (idir si) * pa \<mapsto>\<^sub>a l>
     aug_loop_imp si pa i ptr \<delta> False
   <\<lambda>_. flow_assn (fold (\<lambda> v f. let a = par_edge s v in
                     flow_upd f a (flow_lookup f a + (if par_up s v then - \<delta> else \<delta>)))
                   (drop i (take ptr l)) Fl) (iflow si)
      * parent_assn (parent_edge s) (iparent si) * dir_assn (edge_dir s) (idir si) * pa \<mapsto>\<^sub>a l>"
proof (induction "ptr - i" arbitrary: i Fl)
  case 0
  hence le: "ptr \<le> i" by simp
  show ?case
    by (subst aug_loop_imp.simps) (sep_auto simp: le drop_take)
next
  case (Suc k)
  from Suc.hyps(2) have iltptr: "i < ptr" by simp
  hence niltptr: "\<not> ptr \<le> i" by simp
  have iltl: "i < length l" using iltptr Suc.prems(4) by simp
  have lt: "i < length (take ptr l)" using iltptr Suc.prems(4) by simp
  have dec: "drop i (take ptr l) = l ! i # drop (Suc i) (take ptr l)"
    using lt iltptr by (simp add: Cons_nth_drop_Suc[symmetric] nth_take)
  have kval: "k = ptr - Suc i" using Suc.hyps(2) iltptr by simp
  have vin: "l ! i \<in> \<V> - {r}" "par_edge s (l ! i) \<in> \<E>" using Suc.prems(5) dec by auto
  have vinV: "l ! i \<in> \<V>" and vinr: "l ! i \<noteq> r" using vin(1) by auto
  have subprem: "\<forall>v \<in> set (drop (Suc i) (take ptr l)). v \<in> \<V> - {r} \<and> par_edge s v \<in> \<E>"
    using Suc.prems(5) dec by auto
  from subprem have subV: "\<And>v. v \<in> set (drop (Suc i) (take ptr l)) \<Longrightarrow> v \<in> \<V>"
    and subr: "\<And>v. v \<in> set (drop (Suc i) (take ptr l)) \<Longrightarrow> v \<noteq> r" by auto
  have finvw: "flow_invar (flow_upd Fl (par_edge s (l ! i)) w)" for w
    by (rule flow_arr.fixed_univ_map_upd_invar[OF Suc.prems(1) vin(2)])
  note IH = Suc.hyps(1)[OF kval]
  show ?case
    by (subst aug_loop_imp.simps)
       (sep_auto simp: niltptr dec vin vinV vinr iltl finvw subprem subV subr Let_def
                       Suc.prems(1) Suc.prems(2) Suc.prems(3) Suc.prems(4) heap: IH)
qed

text \<open>Specialisations at @{term \<open>i = 0\<close>} (the way @{const augment_flow_imp} calls them), with the
      @{term \<open>drop 0\<close>} reduced to the whole buffer prefix.\<close>
lemmas aug_loop_imp_up_rule0 = aug_loop_imp_up_rule[where i = 0, simplified]
lemmas aug_loop_imp_down_rule0 = aug_loop_imp_down_rule[where i = 0, simplified]
text \<open>Folding parent-edge flow updates preserves @{term flow_invar} (each update is on an edge of
      @{term \<E>}).\<close>
lemma fold_flow_invar:
  "flow_invar Fl \<Longrightarrow> \<forall>v \<in> set p. par_edge s v \<in> \<E> \<Longrightarrow>
   flow_invar (fold (\<lambda> v f. let a = par_edge s v in
                 flow_upd f a (flow_lookup f a + sg (par_up s v))) p Fl)"
proof (induction p arbitrary: Fl)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  have "flow_invar (flow_upd Fl (par_edge s x) (flow_lookup Fl (par_edge s x) + sg (par_up s x)))"
    by (rule flow_arr.fixed_univ_map_upd_invar[OF Cons.prems(1)]) (use Cons.prems(2) in simp)
  thus ?case using Cons.prems(2) Cons.IH by (simp add: Let_def)
qed

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
proof (cases "\<delta> \<le> 0")
  case True
  show ?thesis
    unfolding augment_flow_imp_def augment_flow_def by (sep_auto simp: True)
next
  case False
  have f0inv: "flow_invar (flow_upd (current_flow s) e
                  (flow_lookup (current_flow s) e + (if in_U then - \<delta> else \<delta>)))"
    by (rule flow_arr.fixed_univ_map_upd_invar[OF assms(1) assms(4)])
  from assms(7) have a7V: "\<And>v. v \<in> set (take ptr1 l1) \<Longrightarrow> v \<in> \<V>"
    and a7r: "\<And>v. v \<in> set (take ptr1 l1) \<Longrightarrow> v \<noteq> r" by auto
  from assms(8) have a8V: "\<And>v. v \<in> set (take ptr2 l2) \<Longrightarrow> v \<in> \<V>"
    and a8r: "\<And>v. v \<in> set (take ptr2 l2) \<Longrightarrow> v \<noteq> r" by auto
  show ?thesis
  proof (cases in_U)
    case True note inU = this
    have f0T: "flow_invar (flow_upd (current_flow s) e (flow_lookup (current_flow s) e - \<delta>))"
      using f0inv inU by simp
    have f1inv: "flow_invar (fold (\<lambda> v f. let a = par_edge s v in
                    flow_upd f a (flow_lookup f a + (if par_up s v then \<delta> else - \<delta>)))
                  (take ptr1 l1)
                  (flow_upd (current_flow s) e (flow_lookup (current_flow s) e - \<delta>)))"
      by (rule fold_flow_invar[where sg = "\<lambda> b. if b then \<delta> else - \<delta>", OF f0T]) (use assms(7) in auto)
    show ?thesis
      unfolding augment_flow_imp_def augment_flow_def
      by (sep_auto simp: inU if_P[OF inU] Let_def assms(1) assms(4) assms(7) assms(8)
                         a7V a7r a8V a8r
                 heap: aug_loop_imp_up_rule0[OF f0T assms(2) assms(3) assms(5)]
                       aug_loop_imp_down_rule0[OF f1inv assms(2) assms(3) assms(6)])
  next
    case False note ninU = this
    have f0F: "flow_invar (flow_upd (current_flow s) e (flow_lookup (current_flow s) e + \<delta>))"
      using f0inv ninU by simp
    have f1inv: "flow_invar (fold (\<lambda> v f. let a = par_edge s v in
                    flow_upd f a (flow_lookup f a + (if par_up s v then \<delta> else - \<delta>)))
                  (take ptr2 l2)
                  (flow_upd (current_flow s) e (flow_lookup (current_flow s) e + \<delta>)))"
      by (rule fold_flow_invar[where sg = "\<lambda> b. if b then \<delta> else - \<delta>", OF f0F]) (use assms(8) in auto)
    show ?thesis
      unfolding augment_flow_imp_def augment_flow_def
      by (sep_auto simp: ninU if_not_P[OF ninU] Let_def assms(1) assms(4) assms(7) assms(8)
                         a7V a7r a8V a8r
                 heap: aug_loop_imp_up_rule0[OF f0F assms(2) assms(3) assms(6)]
                       aug_loop_imp_down_rule0[OF f1inv assms(2) assms(3) assms(5)])
  qed
qed

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
  by (sep_auto simp: assms(4) assms(5)
             heap: augment_flow_imp_rule[OF assms(1) assms(2) assms(3) assms(5)
                     assms(6) assms(7) assms(8) assms(9)])

subsection \<open>Refinement of the re-parenting walk\<close>

text \<open>@{const reparent_walk_imp} reverses the parent pointers along the spine in place. It both
      \<^emph>\<open>reads and mutates\<close> the parent-edge / direction stores, so its refinement carries a \<^emph>\<open>store
      agreement invariant\<close>: on the still-unvisited suffix of the spine the mutable stores @{term Pe},
      @{term D} still agree with the frozen functional state @{term s} --- maintained because the spine
      is @{term distinct}, so each visited vertex leaves the suffix untouched. The reads therefore see
      the original @{term \<open>par_edge s\<close>} / @{term \<open>par_up s\<close>} that @{const reparent_walk} threads.\<close>
lemma reparent_walk_imp_rule:
  "\<lbrakk>parent_invar Pe; dir_invar D; ptr \<le> length l; e \<in> \<E>;
    distinct (drop i (take ptr l));
    \<forall>w \<in> set (drop i (take ptr l)). w \<in> \<V> - {r};
    \<forall>w \<in> set (drop i (take ptr l)). parent_lookup Pe w = par_edge s w \<and> dir_lookup D w = par_up s w\<rbrakk> \<Longrightarrow>
   <rd * parent_assn Pe (iparent si) * dir_assn D (idir si) * pa \<mapsto>\<^sub>a l>
     reparent_walk_imp si e v first pe pup pa i ptr
   <\<lambda>_. rd * (case reparent_walk s e v first pe pup (drop i (take ptr l)) (Pe, D) of (Pe', D') \<Rightarrow>
          parent_assn Pe' (iparent si) * dir_assn D' (idir si) * pa \<mapsto>\<^sub>a l)>"
proof (induction "ptr - i" arbitrary: i Pe D first pe pup)
  case 0
  hence le: "ptr \<le> i" by simp
  show ?case
    by (subst reparent_walk_imp.simps) (sep_auto simp: le drop_take)
next
  case (Suc k)
  from Suc.hyps(2) have iltptr: "i < ptr" by simp
  hence niltptr: "\<not> ptr \<le> i" by simp
  have iltl: "i < length l" using iltptr Suc.prems(3) by simp
  have lt: "i < length (take ptr l)" using iltptr Suc.prems(3) by simp
  have dec: "drop i (take ptr l) = l ! i # drop (Suc i) (take ptr l)"
    using lt iltptr by (simp add: Cons_nth_drop_Suc[symmetric] nth_take)
  have kval: "k = ptr - Suc i" using Suc.hyps(2) iltptr by simp
  have wV: "l ! i \<in> \<V> - {r}" using Suc.prems(6) dec by auto
  have wVv: "l ! i \<in> \<V>" and wr: "l ! i \<noteq> r" using wV by auto
  have agrp: "parent_lookup Pe (l ! i) = par_edge s (l ! i)"
    and agrd: "dir_lookup D (l ! i) = par_up s (l ! i)" using Suc.prems(7) dec by auto
  have distl: "distinct (drop (Suc i) (take ptr l))"
    and lni: "l ! i \<notin> set (drop (Suc i) (take ptr l))" using Suc.prems(5) dec by auto
  have subV: "\<forall>w \<in> set (drop (Suc i) (take ptr l)). w \<in> \<V> - {r}" using Suc.prems(6) dec by auto
  have pinvw: "parent_invar (parent_upd Pe (l ! i) w')" for w'
    by (rule parent_arr.fixed_univ_map_upd_invar[OF Suc.prems(1) wV])
  have dinvw: "dir_invar (dir_upd D (l ! i) w')" for w'
    by (rule dir_arr.fixed_univ_map_upd_invar[OF Suc.prems(2) wV])
  have agrec: "\<forall>w \<in> set (drop (Suc i) (take ptr l)).
      parent_lookup (parent_upd Pe (l ! i) v') w = par_edge s w
      \<and> dir_lookup (dir_upd D (l ! i) d') w = par_up s w" for v' d'
  proof (intro ballI conjI)
    fix w assume w: "w \<in> set (drop (Suc i) (take ptr l))"
    have wne: "w \<noteq> l ! i" using w lni by auto
    have win: "w \<in> set (drop i (take ptr l))" using w dec by auto
    show "parent_lookup (parent_upd Pe (l ! i) v') w = par_edge s w"
      using parent_arr.fixed_univ_map_upd[OF Suc.prems(1) wV] wne Suc.prems(7) win by simp
    show "dir_lookup (dir_upd D (l ! i) d') w = par_up s w"
      using dir_arr.fixed_univ_map_upd[OF Suc.prems(2) wV] wne Suc.prems(7) win by simp
  qed
  note IH = Suc.hyps(1)[OF kval _ _ Suc.prems(3) Suc.prems(4) distl subV]
  show ?case
    apply (subst reparent_walk_imp.simps)
    unfolding par_edge_imp_def par_up_imp_def
    by (sep_auto simp: niltptr dec agrp agrd wVv wr iltl reparent_walk.simps
                       Suc.prems(1) Suc.prems(2) Suc.prems(4) pinvw dinvw agrec
                 heap: IH[OF pinvw dinvw] IH[OF pinvw dinvw, simplified])
qed

text \<open>At the top level (@{term \<open>i = 0\<close>}) the stores are the frozen originals, so the agreement
      invariant holds by definition of @{const par_edge} / @{const par_up}.\<close>
lemmas reparent_walk_imp_rule0 = reparent_walk_imp_rule[where i = 0, simplified]

lemma reparent_imp_rule:
  assumes "parent_invar (parent_edge s)" "dir_invar (edge_dir s)" "ptr \<le> length l" "e \<in> \<E>"
    "distinct (take ptr l)" "\<forall>w \<in> set (take ptr l). w \<in> \<V> - {r}"
  shows "<rd * parent_assn (parent_edge s) (iparent si) * dir_assn (edge_dir s) (idir si) * pa \<mapsto>\<^sub>a l>
     reparent_imp si e pa ptr v
   <\<lambda>_. rd * (case reparent s e (take ptr l) v of (Pe', D') \<Rightarrow>
          parent_assn Pe' (iparent si) * dir_assn D' (idir si) * pa \<mapsto>\<^sub>a l)>"
proof -
  have agr0: "\<forall>w \<in> set (take ptr l).
      parent_lookup (parent_edge s) w = par_edge s w \<and> dir_lookup (edge_dir s) w = par_up s w"
    by (simp add: par_edge_def par_up_def)
  have m0: "\<forall>w \<in> set (take ptr l). w \<in> \<V> \<and> w \<noteq> r" using assms(6) by auto
  show ?thesis
    unfolding reparent_imp_def reparent_def
    by (rule reparent_walk_imp_rule0[OF assms(1) assms(2) assms(3) assms(4) assms(5) m0 agr0])
qed

subsection \<open>Refinement of the full pivot\<close>

text \<open>@{const ns_pivot_imp} performs the whole pivot in place: it reads the leaving edge @{term e0}
      \<^emph>\<open>before\<close> re-parenting overwrites it, augments the flow, shifts the potentials over the far
      side (reading the \<^emph>\<open>old\<close> tree before the swap), re-parents the spine, swaps the tree edge, and
      moves @{term e} into the tree and @{term e0} into @{term U}/@{term L}. It refines
      @{const ns_pivot} on the six mutated stores. The assumptions are the union of the sub-operations'
      preconditions, including the @{locale arborescense_adt} @{text swap_edge} witnesses (spine
      @{term psw1}, join arc @{term a}, tail @{term p3}, leaving arc @{term \<open>(v, y)\<close>}).\<close>
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
proof -
  have vV: "v \<in> \<V>" and vr: "v \<noteq> r" using assms(10) by auto
  have esinv2: "es_invar (es_upd (edge_state s) e InTree)"
    by (rule es_arr.fixed_univ_map_upd_invar[OF assms(7) assms(8)])
  have m1: "\<forall>w \<in> set (take ptr1 l1). w \<in> \<V> - {r}" using assms(15) by auto
  have m2: "\<forall>w \<in> set (take ptr2 l2). w \<in> \<V> - {r}" using assms(16) by auto
  have eveu: "ev \<noteq> eu" using assms(20) by simp
  note shiftR = shift_pot_rule[OF assms(4) vV assms(2) assms(3)]
  note augR = augment_flow_imp_rule[OF assms(1) assms(5) assms(6) assms(8) assms(13) assms(14)
                assms(15) assms(16)]
  show ?thesis
  proof (cases "in_U = up_side")
    case True note inU = this
    have gpp: "get_path_pair (spanning_tree s) eu ev = (psw1, psw2)" using assms(19) inU by simp
    have wlk: "walk_betw (abstract_arborescense (spanning_tree s)) eu (psw1 @ a # p3) r"
      using assms(21) inU by simp
    obtain Pe1 D1 where rep1: "reparent s e (take ptr1 l1) v = (Pe1, D1)" by fastforce
    show ?thesis
      unfolding ns_pivot_imp_def Let_def
      by (sep_auto simp: inU assms(5) assms(6) assms(7) assms(8) assms(9) vV vr
                         assms(15) assms(17) esinv2 rep1
                 heap: augR shiftR
                       reparent_imp_rule[OF assms(5) assms(6) assms(13) assms(8) assms(17) m1]
                       swap_edge_rule[OF assms(4) gpp assms(20) wlk assms(22) assms(23)
                         assms(24) assms(25)])
  next
    case False note ninU = this
    have gpp: "get_path_pair (spanning_tree s) ev eu = (psw1, psw2)" using assms(19) ninU by simp
    have wlk: "walk_betw (abstract_arborescense (spanning_tree s)) ev (psw1 @ a # p3) r"
      using assms(21) ninU by simp
    obtain Pe2 D2 where rep2: "reparent s e (take ptr2 l2) v = (Pe2, D2)" by fastforce
    show ?thesis
      unfolding ns_pivot_imp_def Let_def
      by (sep_auto simp: ninU assms(5) assms(6) assms(7) assms(8) assms(9) vV vr
                         assms(16) assms(18) esinv2 rep2
                 heap: augR shiftR
                       reparent_imp_rule[OF assms(5) assms(6) assms(14) assms(8) assms(18) m2]
                       swap_edge_rule[OF assms(4) gpp eveu wlk assms(22) assms(23)
                         assms(25) assms(24)])
  qed
qed

subsection \<open>Refinement of the whole loop\<close>

text \<open>The fundamental-circuit spine on the \<^emph>\<open>up\<close> side carries the leaving edge @{term \<open>par_edge s v\<close>}
      as one of its @{const edges_of_vwalk} arcs --- the well-formedness the \<open>swap_edge\<close> refinement axiom
      needs. This reconstructs the witness that the preservation proof @{text swap_edge_pivot} builds
      internally.\<close>

lemma pivot_swap_witness:
  assumes inv: "ns_invar s"
    and sel: "ns_select s = Some (e, in_U, \<gamma>, sel')"
    and pp:  "get_path_pair (spanning_tree s) (fst e) (snd e) = (p1, p2)"
    and bn:  "bottleneck s e in_U p1 p2 = (\<delta>, False, v, e0fwd, up_side)"
  shows "\<exists>psw1 psw2 aa p3 y.
           get_path_pair (spanning_tree s)
              (if in_U = up_side then fst e else snd e)
              (if in_U = up_side then snd e else fst e) = (psw1, psw2)
           \<and> walk_betw (abstract_arborescense (spanning_tree s))
               (if in_U = up_side then fst e else snd e) (psw1 @ aa # p3) r
           \<and> distinct (psw1 @ aa # p3)
           \<and> (v, y) \<in> set (edges_of_vwalk (psw1 @ [aa]))"
proof -
  let ?absT = "abstract_arborescense (spanning_tree s)"
  let ?u = "if in_U = up_side then fst e else snd e"
  let ?vax = "if in_U = up_side then snd e else fst e"
  let ?P = "if in_U = up_side then p1 else p2"
  have eE: "e \<in> \<E>" using ns_select_SomeD(2)[OF inv sel] .
  have arb: "arborescense_invar (spanning_tree s)"
    using ns_invar_implD(7)[OF ns_invarD(1)[OF inv]] .
  have neq: "fst e \<noteq> snd e" using entering_not_selfloop[OF inv sel] .
  have fV: "fst e \<in> \<V>" using fst_E_V[OF eE] .
  have sV: "snd e \<in> \<V>" using snd_E_V[OF eE] .
  obtain a p3 where
    w1: "walk_betw ?absT (fst e) (p1 @ a # p3) r" and
    w2: "walk_betw ?absT (snd e) (p2 @ a # p3) r" and
    d1: "distinct (p1 @ a # p3)" and d2: "distinct (p2 @ a # p3)"
    using get_path_pair(1)[OF arb pp neq fV sV] by blast
  have vP: "v \<in> set ?P" using bottleneck_pivot_facts(1)[OF inv sel pp bn] .
  have vVr: "v \<in> \<V> - {r}" using bottleneck_pivot_facts(2)[OF inv sel pp bn] .
  have wP: "walk_betw ?absT ?u (?P @ a # p3) r" using w1 w2 by (cases "in_U = up_side") simp_all
  have dP: "distinct (?P @ a # p3)" using d1 d2 by (cases "in_U = up_side") simp_all
  obtain j where jlen: "j < length ?P" and Pj: "?P ! j = v"
    using vP by (metis in_set_conv_nth)
  have SjW: "Suc j < length (?P @ a # p3)" using jlen by simp
  have Wj: "(?P @ a # p3) ! j = v" using jlen Pj by (simp add: nth_append)
  have Wjr: "(?P @ a # p3) ! j \<in> \<V> - {r}" using Wj vVr by simp
  have pv_succ: "par_vx s v = (?P @ a # p3) ! Suc j"
    using walk_succ_is_par_vx[OF inv wP dP SjW Wjr] Wj by simp
  have qlen: "Suc j < length (?P @ [a])" using jlen by simp
  have qj: "(?P @ [a]) ! j = v" using jlen Pj by (simp add: nth_append)
  have qcat: "?P @ a # p3 = (?P @ [a]) @ p3" by simp
  have qsucc: "(?P @ [a]) ! Suc j = par_vx s v"
    using pv_succ qlen by (metis nth_append qcat)
  have eidx: "edges_of_vwalk (?P @ [a]) ! j = (v, par_vx s v)"
    using edges_of_vwalk_index[OF qlen] qj qsucc by simp
  have jelen: "j < length (edges_of_vwalk (?P @ [a]))"
    using jlen by (simp add: edges_of_vwalk_length)
  have edgemem: "(v, par_vx s v) \<in> set (edges_of_vwalk (?P @ [a]))"
    using nth_mem[OF jelen] eidx by simp
  have GP: "get_path_pair (spanning_tree s) ?u ?vax = (?P, if in_U = up_side then p2 else p1)"
    using pp get_path_pair(2)[OF arb pp neq fV sV] by (cases "in_U = up_side") simp_all
  show ?thesis using GP wP dP edgemem by blast
qed

text \<open>The store invariants, the fundamental-circuit well-formedness, and the step-preservation facts
      that the loop refinement needs are all consequences of the concrete network-simplex invariant
      @{const ns_invar} --- its data-structure part and the \<open>Network_Simplex_Preservation\<close> development.
      We package them as six interface lemmas so the loop refinement reads cleanly.\<close>

lemma inv_sel:
  assumes "ns_invar t"
  shows "sel_invar (edge_sel t) \<and> pot_invar (potentials t) \<and> es_invar (edge_state t)"
  using ns_invar_implD[OF ns_invarD(1)[OF assms]] by (auto simp: pot_valid_def)

lemma inv_stores:
  assumes "ns_invar t"
  shows "flow_invar (current_flow t) \<and> parent_invar (parent_edge t)
           \<and> dir_invar (edge_dir t) \<and> arborescense_invar (spanning_tree t)"
  using ns_invar_implD[OF ns_invarD(1)[OF assms]] by auto

lemma inv_gpp:
  assumes "ns_invar t" "ns_select t = Some (e, in_U, \<gamma>, sel')"
  shows "e \<in> \<E> \<and> fst_exec e \<noteq> snd_exec e \<and> fst_exec e \<in> \<V> \<and> snd_exec e \<in> \<V>"
proof -
  have eE: "e \<in> \<E>" using ns_select_SomeD(2)[OF assms] .
  show ?thesis
    using eE entering_not_selfloop[OF assms] fst_E_V[OF eE] snd_E_V[OF eE]
    by (simp add: fst_exec_coincide[OF eE] snd_exec_coincide[OF eE])
qed

lemma inv_paths:
  assumes "ns_invar t" "ns_select t = Some (e, in_U, \<gamma>, sel')"
    "get_path_pair (spanning_tree t) (fst_exec e) (snd_exec e) = (p1, p2)"
  shows "(\<forall>w \<in> set p1. w \<in> \<V> - {r} \<and> par_edge t w \<in> \<E>)
         \<and> (\<forall>w \<in> set p2. w \<in> \<V> - {r} \<and> par_edge t w \<in> \<E>) \<and> distinct p1 \<and> distinct p2"
proof -
  have eE: "e \<in> \<E>" using ns_select_SomeD(2)[OF assms(1,2)] .
  have neq: "fst e \<noteq> snd e" using entering_not_selfloop[OF assms(1,2)] .
  have pp': "get_path_pair (spanning_tree t) (fst e) (snd e) = (p1, p2)"
    using assms(3) by (simp add: fst_exec_coincide[OF eE] snd_exec_coincide[OF eE])
  have v1: "set p1 \<subseteq> \<V> - {r}" and v2: "set p2 \<subseteq> \<V> - {r}"
    using get_path_pair_verts[OF assms(1) eE neq pp'] by auto
  have arb: "arborescense_invar (spanning_tree t)"
    using ns_invar_implD(7)[OF ns_invarD(1)[OF assms(1)]] .
  obtain a p3 where d1: "distinct (p1 @ a # p3)" and d2: "distinct (p2 @ a # p3)"
    using get_path_pair(1)[OF arb pp' neq fst_E_V[OF eE] snd_E_V[OF eE]] by blast
  have tree: "ns_invar_tree t" using ns_invarD(7)[OF assms(1)] .
  show ?thesis using v1 v2 d1 d2 ns_invar_tree_edgeD[OF tree] by auto
qed

lemma inv_flip:
  assumes "ns_invar t" "ns_select t = Some (e, in_U, \<gamma>, sel')"
    "get_path_pair (spanning_tree t) (fst_exec e) (snd_exec e) = (p1, p2)"
    "bottleneck t e in_U p1 p2 = (\<delta>, True, vv, e0fwd, up_side)" "\<delta> \<noteq> - 1"
  shows "ns_invar (ns_flip t e in_U \<gamma> sel' \<delta> p1 p2)"
proof -
  have cond: "ns_flip_cond t" using assms(2,3,4,5) by (simp add: ns_flip_cond_def)
  have upd: "ns_flip_upd t = ns_flip t e in_U \<gamma> sel' \<delta> p1 p2"
    using assms(2,3,4) by (simp add: ns_flip_upd_def)
  show ?thesis using ns_flip_preservation[OF assms(1) cond] upd by simp
qed

lemma inv_pivot:
  assumes "ns_invar t" "ns_select t = Some (e, in_U, \<gamma>, sel')"
    "get_path_pair (spanning_tree t) (fst_exec e) (snd_exec e) = (p1, p2)"
    "bottleneck t e in_U p1 p2 = (\<delta>, False, vv, e0fwd, up_side)" "\<delta> \<noteq> - 1"
  shows "(\<forall>u \<in> \<V>. pot_value_invar (pot_lookup (potentials t) u)) \<and> par_edge t vv \<in> \<E>
         \<and> vv \<in> \<V> - {r}
         \<and> (\<exists>psw1 psw2 aa p3 y.
              get_path_pair (spanning_tree t) (if in_U = up_side then fst_exec e else snd_exec e)
                 (if in_U = up_side then snd_exec e else fst_exec e) = (psw1, psw2)
              \<and> walk_betw (abstract_arborescense (spanning_tree t))
                  (if in_U = up_side then fst_exec e else snd_exec e) (psw1 @ aa # p3) r
              \<and> distinct (psw1 @ aa # p3) \<and> (vv, y) \<in> set (edges_of_vwalk (psw1 @ [aa])))
         \<and> ns_invar (ns_pivot t e in_U \<gamma> sel' \<delta> vv e0fwd up_side p1 p2)"
proof -
  have eE: "e \<in> \<E>" using ns_select_SomeD(2)[OF assms(1,2)] .
  have pp': "get_path_pair (spanning_tree t) (fst e) (snd e) = (p1, p2)"
    using assms(3) by (simp add: fst_exec_coincide[OF eE] snd_exec_coincide[OF eE])
  have pv: "\<forall>u \<in> \<V>. pot_value_invar (pot_lookup (potentials t) u)"
    using ns_invar_implD(2)[OF ns_invarD(1)[OF assms(1)]] by (simp add: pot_valid_def)
  have vVr: "vv \<in> \<V> - {r}" using bottleneck_pivot_facts(2)[OF assms(1,2) pp' assms(4)] .
  have peE: "par_edge t vv \<in> \<E>" using ns_invar_tree_edgeD[OF ns_invarD(7)[OF assms(1)] vVr] .
  have cond: "ns_pivot_cond t" using assms(2,3,4,5) by (simp add: ns_pivot_cond_def)
  have upd: "ns_pivot_upd t = ns_pivot t e in_U \<gamma> sel' \<delta> vv e0fwd up_side p1 p2"
    using assms(2,3,4) by (simp add: ns_pivot_upd_def)
  have presv: "ns_invar (ns_pivot t e in_U \<gamma> sel' \<delta> vv e0fwd up_side p1 p2)"
    using ns_pivot_preservation[OF assms(1) cond] upd by simp
  show ?thesis
    unfolding fst_exec_coincide[OF eE] snd_exec_coincide[OF eE]
    using pv peE vVr pivot_swap_witness[OF assms(1,2) pp' assms(4)] presv by blast
qed

text \<open>The imperative loop @{const ns_loop_imp} refines the functional @{const ns_loop_impl} under the
      single, natural precondition @{term \<open>ns_invar s\<close>}, by \<^emph>\<open>fixpoint induction\<close> on the heap
      @{command partial_function}. The six interface lemmas above supply everything each iteration
      needs; here we only assemble them. Under partial correctness a diverging run makes the triple
      hold vacuously, so no termination argument is needed.\<close>

lemma ns_loop_imp_rule:
  shows "ns_invar s \<longrightarrow> <ns_rel s si> ns_loop_imp si
           <\<lambda>res. ns_rel_weak (ns_loop_impl s) si * \<up>(res = network_simplex_state.return (ns_loop_impl s))>"
proof (induction arbitrary: s rule: ns_loop_imp.fixp_induct)
  case 1 show ?case by simp
next
  case 2 show ?case by simp
next
  case (3 f s)
  note IH = "3.IH"
  show ?case
  proof (intro impI)
    assume I: "ns_invar s"
    show "<ns_rel s si> ns_select_imp si \<bind>
            (\<lambda>sel. case sel of None \<Rightarrow> Heap_Monad.return Network_Simplex.success
                   | Some (e, in_U, \<gamma>) \<Rightarrow>
                       fst_exec_imp e \<bind> (\<lambda>u. snd_exec_imp e \<bind> (\<lambda>v.
                        get_path_pair_imp (itree si) u v (ipath1 si) (ipath2 si) \<bind> (\<lambda>(ptr1, ptr2).
                        bottleneck_imp si e in_U ptr1 ptr2 \<bind> (\<lambda>bn.
                        case bn of (\<delta>, is_flip, vv, e0fwd, up_side) \<Rightarrow>
                          if \<delta> = - 1 then Heap_Monad.return Network_Simplex.unbounded
                          else if is_flip
                            then ns_flip_imp si e in_U \<delta> ptr1 ptr2 \<bind> (\<lambda>_. f si)
                            else ns_pivot_imp si e u v in_U \<gamma> \<delta> vv e0fwd up_side ptr1 ptr2 \<bind> (\<lambda>_. f si))))))
           <\<lambda>res. ns_rel_weak (ns_loop_impl s) si * \<up>(res = network_simplex_state.return (ns_loop_impl s))>"
    proof (cases "ns_select s")
      case None note nsel = this
      have pre: "sel_invar (edge_sel s)" "pot_invar (potentials s)" "es_invar (edge_state s)"
        using inv_sel[OF I] by auto
      have lu: "ns_loop_impl s = ns_optimal s" by (simp add: ns_loop_impl.simps nsel)
      have selNone: "<sel_assn (edge_sel s) (isel si) * pot_assn (potentials s) (ipot si)
                       * es_assn (edge_state s) (iestate si) * rd>
                     ns_select_imp si
                     <\<lambda>res. (\<exists>\<^sub>A ss. sel_assn ss (isel si)) * pot_assn (potentials s) (ipot si)
                       * es_assn (edge_state s) (iestate si) * rd * \<up>(res = None)>"
        by (rule ht_cons_post[OF ns_select_imp_rule[OF pre(1) pre(2) pre(3)]]) (sep_auto simp: nsel)
      show ?thesis
        unfolding ns_rel_def ns_rel_weak_def
        by (sep_auto simp: lu ns_optimal_def heap: selNone)
    next
      case (Some res0)
      obtain e in_U \<gamma> sel' where sel: "ns_select s = Some (e, in_U, \<gamma>, sel')"
        using Some by (cases res0) auto
      have pre: "sel_invar (edge_sel s)" "pot_invar (potentials s)" "es_invar (edge_state s)"
        using inv_sel[OF I] by auto
      have st: "flow_invar (current_flow s)" "parent_invar (parent_edge s)"
        "dir_invar (edge_dir s)" "arborescense_invar (spanning_tree s)"
        using inv_stores[OF I] by auto
      have gp: "e \<in> \<E>" "fst_exec e \<noteq> snd_exec e" "fst_exec e \<in> \<V>" "snd_exec e \<in> \<V>"
        using inv_gpp[OF I sel] by auto
      obtain p1 p2 where gpp: "get_path_pair (spanning_tree s) (fst_exec e) (snd_exec e) = (p1, p2)"
        by fastforce
      have paths: "\<forall>w \<in> set p1. w \<in> \<V> - {r} \<and> par_edge s w \<in> \<E>"
        "\<forall>w \<in> set p2. w \<in> \<V> - {r} \<and> par_edge s w \<in> \<E>" "distinct p1" "distinct p2"
        using inv_paths[OF I sel gpp] by auto
      \<comment> \<open>@{thm fst_exec_eq} / @{thm snd_exec_eq} rewrite the endpoint reads to \<open>fst e\<close> /
          \<open>snd e\<close>; the bridged \<open>gppb\<close> keeps \<open>get_path_pair\<close> matching after that.\<close>
      have gppb: "get_path_pair (spanning_tree s) (fst e) (snd e) = (p1, p2)"
        using gpp by (simp add: fst_exec_eq[OF gp(1)] snd_exec_eq[OF gp(1)])
      have gpb: "fst e \<in> \<V>" "snd e \<in> \<V>" "fst e \<noteq> snd e"
        using gp by (simp_all add: fst_exec_eq[OF gp(1)] snd_exec_eq[OF gp(1)])
      obtain \<delta> is_flip vv e0fwd up_side
        where bn: "bottleneck s e in_U p1 p2 = (\<delta>, is_flip, vv, e0fwd, up_side)"
        by (metis prod_cases5)
      have lu: "ns_loop_impl s =
          (if \<delta> = - 1 then ns_unbounded_upd s
           else if is_flip then ns_loop_impl (ns_flip s e in_U \<gamma> sel' \<delta> p1 p2)
           else ns_loop_impl (ns_pivot s e in_U \<gamma> sel' \<delta> vv e0fwd up_side p1 p2))"
        by (simp add: ns_loop_impl.simps sel gpp bn)
      \<comment> \<open>Remaining: thread the buffers through \<open>get_path_pair_imp\<close>, run @{const bottleneck_imp},
          and case-split on @{term \<delta>} / @{term is_flip}, applying @{thm ns_flip_imp_rule} /
          @{thm ns_pivot_imp_rule} with the invariant facts and the fixpoint IH for the tail. The
          store invariants (\<open>pre\<close>/\<open>st\<close>), the fundamental-circuit well-formedness (\<open>gp\<close>/\<open>paths\<close>) and
          the preservation facts (\<open>inv_flip\<close>/\<open>inv_pivot\<close>) are exactly what those rules and the IH need.\<close>
      note IHr = IH[rule_format]
      have selSome: "<sel_assn (edge_sel s) (isel si) * pot_assn (potentials s) (ipot si)
                       * es_assn (edge_state s) (iestate si) * rd>
                     ns_select_imp si
                     <\<lambda>res. sel_assn sel' (isel si) * pot_assn (potentials s) (ipot si)
                       * es_assn (edge_state s) (iestate si) * rd * \<up>(res = Some (e, in_U, \<gamma>))>"
        by (rule ht_cons_post[OF ns_select_imp_rule[OF pre(1) pre(2) pre(3)]]) (sep_auto simp: sel)
      \<comment> \<open>Frame the select refinement onto the whole state, landing a \<^emph>\<open>concrete\<close> @{term \<open>Some (e, in_U, \<gamma>)\<close>}.\<close>
      have selF: "<rd * flow_assn (current_flow s) (iflow si) * pot_assn (potentials s) (ipot si)
          * tree_assn (spanning_tree s) (itree si) * parent_assn (parent_edge s) (iparent si)
          * dir_assn (edge_dir s) (idir si) * es_assn (edge_state s) (iestate si)
          * sel_assn (edge_sel s) (isel si)
          * (\<exists>\<^sub>A l1 l2. ipath1 si \<mapsto>\<^sub>a l1 * ipath2 si \<mapsto>\<^sub>a l2
               * \<up>(card \<V> - 1 \<le> length l1 \<and> card \<V> - 1 \<le> length l2))>
         ns_select_imp si
        <\<lambda>res. rd * flow_assn (current_flow s) (iflow si) * pot_assn (potentials s) (ipot si)
          * tree_assn (spanning_tree s) (itree si) * parent_assn (parent_edge s) (iparent si)
          * dir_assn (edge_dir s) (idir si) * es_assn (edge_state s) (iestate si)
          * sel_assn sel' (isel si)
          * (\<exists>\<^sub>A l1 l2. ipath1 si \<mapsto>\<^sub>a l1 * ipath2 si \<mapsto>\<^sub>a l2
               * \<up>(card \<V> - 1 \<le> length l1 \<and> card \<V> - 1 \<le> length l2))
          * \<up>(res = Some (e, in_U, \<gamma>))>"
        by (sep_auto heap: selSome)
      \<comment> \<open>The Some-branch body with a \<^emph>\<open>concrete\<close> entering edge --- no option-case-split, so the endpoint
          reads and the path/bottleneck refinements thread cleanly.\<close>
      have contBody: "<rd * flow_assn (current_flow s) (iflow si) * pot_assn (potentials s) (ipot si)
          * tree_assn (spanning_tree s) (itree si) * parent_assn (parent_edge s) (iparent si)
          * dir_assn (edge_dir s) (idir si) * es_assn (edge_state s) (iestate si)
          * sel_assn sel' (isel si)
          * (\<exists>\<^sub>A l1 l2. ipath1 si \<mapsto>\<^sub>a l1 * ipath2 si \<mapsto>\<^sub>a l2
               * \<up>(card \<V> - 1 \<le> length l1 \<and> card \<V> - 1 \<le> length l2))>
         fst_exec_imp e \<bind> (\<lambda>u. snd_exec_imp e \<bind> (\<lambda>v.
           get_path_pair_imp (itree si) u v (ipath1 si) (ipath2 si) \<bind> (\<lambda>(ptr1, ptr2).
           bottleneck_imp si e in_U ptr1 ptr2 \<bind> (\<lambda>bn.
           case bn of (\<delta>, is_flip, vv, e0fwd, up_side) \<Rightarrow>
             if \<delta> = - 1 then Heap_Monad.return Network_Simplex.unbounded
             else if is_flip then ns_flip_imp si e in_U \<delta> ptr1 ptr2 \<bind> (\<lambda>_. f si)
             else ns_pivot_imp si e u v in_U \<gamma> \<delta> vv e0fwd up_side ptr1 ptr2 \<bind> (\<lambda>_. f si)))))
        <\<lambda>res. ns_rel_weak (ns_loop_impl s) si * \<up>(res = network_simplex_state.return (ns_loop_impl s))>"
      proof -
        \<comment> \<open>Peel the two endpoint reads and the path search with @{thm ht_bind}; each peeled step turns
            its guarantee into a \<^emph>\<open>top-level\<close> precondition pure, so the fill pointers arrive with the
            clean facts @{term \<open>take ptr1 l1' = p1\<close>} / @{term \<open>take ptr2 l2' = p2\<close>} that the bottleneck /
            augmentation refinements need --- a single \<open>sep_auto\<close> never re-normalises them mid-monad.\<close>
        have fstF: "<rd * flow_assn (current_flow s) (iflow si) * pot_assn (potentials s) (ipot si)
            * tree_assn (spanning_tree s) (itree si) * parent_assn (parent_edge s) (iparent si)
            * dir_assn (edge_dir s) (idir si) * es_assn (edge_state s) (iestate si)
            * sel_assn sel' (isel si)
            * (\<exists>\<^sub>A l1 l2. ipath1 si \<mapsto>\<^sub>a l1 * ipath2 si \<mapsto>\<^sub>a l2
                 * \<up>(card \<V> - 1 \<le> length l1 \<and> card \<V> - 1 \<le> length l2))>
           fst_exec_imp e
          <\<lambda>u. rd * flow_assn (current_flow s) (iflow si) * pot_assn (potentials s) (ipot si)
            * tree_assn (spanning_tree s) (itree si) * parent_assn (parent_edge s) (iparent si)
            * dir_assn (edge_dir s) (idir si) * es_assn (edge_state s) (iestate si)
            * sel_assn sel' (isel si)
            * (\<exists>\<^sub>A l1 l2. ipath1 si \<mapsto>\<^sub>a l1 * ipath2 si \<mapsto>\<^sub>a l2
                 * \<up>(card \<V> - 1 \<le> length l1 \<and> card \<V> - 1 \<le> length l2)) * \<up>(u = fst_exec e)>"
          by (sep_auto heap: fst_exec_rule[OF gp(1)])
        have sndF: "\<And>u. <rd * flow_assn (current_flow s) (iflow si) * pot_assn (potentials s) (ipot si)
            * tree_assn (spanning_tree s) (itree si) * parent_assn (parent_edge s) (iparent si)
            * dir_assn (edge_dir s) (idir si) * es_assn (edge_state s) (iestate si)
            * sel_assn sel' (isel si)
            * (\<exists>\<^sub>A l1 l2. ipath1 si \<mapsto>\<^sub>a l1 * ipath2 si \<mapsto>\<^sub>a l2
                 * \<up>(card \<V> - 1 \<le> length l1 \<and> card \<V> - 1 \<le> length l2)) * \<up>(u = fst_exec e)>
           snd_exec_imp e
          <\<lambda>v. rd * flow_assn (current_flow s) (iflow si) * pot_assn (potentials s) (ipot si)
            * tree_assn (spanning_tree s) (itree si) * parent_assn (parent_edge s) (iparent si)
            * dir_assn (edge_dir s) (idir si) * es_assn (edge_state s) (iestate si)
            * sel_assn sel' (isel si)
            * (\<exists>\<^sub>A l1 l2. ipath1 si \<mapsto>\<^sub>a l1 * ipath2 si \<mapsto>\<^sub>a l2
                 * \<up>(card \<V> - 1 \<le> length l1 \<and> card \<V> - 1 \<le> length l2))
            * \<up>(u = fst_exec e) * \<up>(v = snd_exec e)>"
          by (sep_auto heap: snd_exec_rule[OF gp(1)])
        have gppF: "\<And>u v. <rd * flow_assn (current_flow s) (iflow si) * pot_assn (potentials s) (ipot si)
            * tree_assn (spanning_tree s) (itree si) * parent_assn (parent_edge s) (iparent si)
            * dir_assn (edge_dir s) (idir si) * es_assn (edge_state s) (iestate si)
            * sel_assn sel' (isel si)
            * (\<exists>\<^sub>A l1 l2. ipath1 si \<mapsto>\<^sub>a l1 * ipath2 si \<mapsto>\<^sub>a l2
                 * \<up>(card \<V> - 1 \<le> length l1 \<and> card \<V> - 1 \<le> length l2))
            * \<up>(u = fst_exec e) * \<up>(v = snd_exec e)>
           get_path_pair_imp (itree si) u v (ipath1 si) (ipath2 si)
          <\<lambda>(ptr1, ptr2). (\<exists>\<^sub>A l1' l2'.
             rd * flow_assn (current_flow s) (iflow si) * pot_assn (potentials s) (ipot si)
             * tree_assn (spanning_tree s) (itree si) * parent_assn (parent_edge s) (iparent si)
             * dir_assn (edge_dir s) (idir si) * es_assn (edge_state s) (iestate si)
             * sel_assn sel' (isel si) * ipath1 si \<mapsto>\<^sub>a l1' * ipath2 si \<mapsto>\<^sub>a l2'
             * \<up>(card \<V> - 1 \<le> length l1' \<and> card \<V> - 1 \<le> length l2'
                 \<and> ptr1 \<le> length l1' \<and> ptr2 \<le> length l2'
                 \<and> take ptr1 l1' = p1 \<and> take ptr2 l2' = p2)
             * \<up>(u = fst_exec e) * \<up>(v = snd_exec e))>"
          by (sep_auto simp: gpp gppb gp gpb st(4) heap: get_path_pair_rule)
        \<comment> \<open>The bottleneck / augmentation tail, with the fill pointers' guarantees as clean hypotheses.
            The branch well-formedness and the bottleneck value are derived here by \<^emph>\<open>controlled\<close>
            rewriting with the path facts --- never a blind \<open>sep_auto\<close> search.\<close>
        have tailP: "\<lbrakk>u = fst_exec e; v = snd_exec e;
            card \<V> - 1 \<le> length l1' \<and> card \<V> - 1 \<le> length l2'
              \<and> ptr1 \<le> length l1' \<and> ptr2 \<le> length l2'
              \<and> take ptr1 l1' = p1 \<and> take ptr2 l2' = p2\<rbrakk> \<Longrightarrow>
           <rd * flow_assn (current_flow s) (iflow si) * pot_assn (potentials s) (ipot si)
            * tree_assn (spanning_tree s) (itree si) * parent_assn (parent_edge s) (iparent si)
            * dir_assn (edge_dir s) (idir si) * es_assn (edge_state s) (iestate si)
            * sel_assn sel' (isel si) * ipath1 si \<mapsto>\<^sub>a l1' * ipath2 si \<mapsto>\<^sub>a l2'>
           bottleneck_imp si e in_U ptr1 ptr2 \<bind> (\<lambda>bn.
             case bn of (\<delta>, is_flip, vv, e0fwd, up_side) \<Rightarrow>
               if \<delta> = - 1 then Heap_Monad.return Network_Simplex.unbounded
               else if is_flip then ns_flip_imp si e in_U \<delta> ptr1 ptr2 \<bind> (\<lambda>_. f si)
               else ns_pivot_imp si e u v in_U \<gamma> \<delta> vv e0fwd up_side ptr1 ptr2 \<bind> (\<lambda>_. f si))
          <\<lambda>res. ns_rel_weak (ns_loop_impl s) si * \<up>(res = network_simplex_state.return (ns_loop_impl s))>"
          for u v ptr1 ptr2 l1' l2'
        proof -
          assume uv: "u = fst_exec e" "v = snd_exec e"
            and Cc: "card \<V> - 1 \<le> length l1' \<and> card \<V> - 1 \<le> length l2'
                     \<and> ptr1 \<le> length l1' \<and> ptr2 \<le> length l2'
                     \<and> take ptr1 l1' = p1 \<and> take ptr2 l2' = p2"
          from Cc have A5: "ptr1 \<le> length l1'" and A6: "ptr2 \<le> length l2'"
            and TA1: "take ptr1 l1' = p1" and TA2: "take ptr2 l2' = p2"
            and cardL1: "card \<V> - 1 \<le> length l1'" and cardL2: "card \<V> - 1 \<le> length l2'" by auto
          have af1: "\<forall>w\<in>set (take ptr1 l1'). w \<in> \<V> - {r} \<and> par_edge s w \<in> \<E>"
            using paths(1) by (simp add: TA1)
          have af2: "\<forall>w\<in>set (take ptr2 l2'). w \<in> \<V> - {r} \<and> par_edge s w \<in> \<E>"
            using paths(2) by (simp add: TA2)
          have d1: "distinct (take ptr1 l1')" using paths(3) by (simp add: TA1)
          have d2: "distinct (take ptr2 l2')" using paths(4) by (simp add: TA2)
          have bv: "bottleneck s e in_U (take ptr1 l1') (take ptr2 l2') = (\<delta>, is_flip, vv, e0fwd, up_side)"
            using bn by (simp add: TA1 TA2)
          note bottR = bottleneck_imp_rule[OF st(1) st(2) st(3) gp(1) A5 A6 af1 af2]
          note bottR2 = bottR[unfolded bv]
          \<comment> \<open>Peel the bottleneck read on its own --- a straight-line \<open>sep_auto\<close> with no \<open>case\<close> / \<open>if\<close>
              tail, so the self-referential @{thm fst_exec_eq} never fires on the (un-taken) pivot
              branch.  Its result is the \<^emph>\<open>concrete\<close> bottleneck tuple.\<close>
          have bottF2: "<rd * flow_assn (current_flow s) (iflow si) * pot_assn (potentials s) (ipot si)
              * tree_assn (spanning_tree s) (itree si) * parent_assn (parent_edge s) (iparent si)
              * dir_assn (edge_dir s) (idir si) * es_assn (edge_state s) (iestate si)
              * sel_assn sel' (isel si) * ipath1 si \<mapsto>\<^sub>a l1' * ipath2 si \<mapsto>\<^sub>a l2'>
             bottleneck_imp si e in_U ptr1 ptr2
            <\<lambda>res. rd * flow_assn (current_flow s) (iflow si) * pot_assn (potentials s) (ipot si)
              * tree_assn (spanning_tree s) (itree si) * parent_assn (parent_edge s) (iparent si)
              * dir_assn (edge_dir s) (idir si) * es_assn (edge_state s) (iestate si)
              * sel_assn sel' (isel si) * ipath1 si \<mapsto>\<^sub>a l1' * ipath2 si \<mapsto>\<^sub>a l2'
              * \<up>(res = (\<delta>, is_flip, vv, e0fwd, up_side))>"
            by (sep_auto simp: bv heap: bottR)
          show "<rd * flow_assn (current_flow s) (iflow si) * pot_assn (potentials s) (ipot si)
              * tree_assn (spanning_tree s) (itree si) * parent_assn (parent_edge s) (iparent si)
              * dir_assn (edge_dir s) (idir si) * es_assn (edge_state s) (iestate si)
              * sel_assn sel' (isel si) * ipath1 si \<mapsto>\<^sub>a l1' * ipath2 si \<mapsto>\<^sub>a l2'>
             bottleneck_imp si e in_U ptr1 ptr2 \<bind> (\<lambda>bn.
               case bn of (\<delta>, is_flip, vv, e0fwd, up_side) \<Rightarrow>
                 if \<delta> = - 1 then Heap_Monad.return Network_Simplex.unbounded
                 else if is_flip then ns_flip_imp si e in_U \<delta> ptr1 ptr2 \<bind> (\<lambda>_. f si)
                 else ns_pivot_imp si e u v in_U \<gamma> \<delta> vv e0fwd up_side ptr1 ptr2 \<bind> (\<lambda>_. f si))
            <\<lambda>res. ns_rel_weak (ns_loop_impl s) si
                     * \<up>(res = network_simplex_state.return (ns_loop_impl s))>"
          proof (cases "\<delta> = - 1")
            case True note dne = this
            have luU: "ns_loop_impl s = ns_unbounded_upd s" using lu dne by simp
            show ?thesis
              unfolding ns_rel_weak_def luU ns_unbounded_upd_def
              apply (rule ht_bind[OF bottF2])
              apply (rule ht_extract_pre_pure, hypsubst)
              apply (simp only: prod.case if_P[OF dne])
              apply (rule ht_cons_post[OF ht_return_sp])
              apply (simp only: ex_assn_move_out)
              apply (rule ent_ex_postI[where x = l1'])
              apply (rule ent_ex_postI[where x = l2'])
              apply (rule ent_ex_postI[where x = sel'])
              apply (sep_auto simp: cardL1 cardL2)
              apply (simp add: cardL1[unfolded One_nat_def])
              apply (simp add: cardL2[unfolded One_nat_def])
              apply (simp add: mod_pure_star_dist)
              done
          next
            case False note dne = this
            show ?thesis
            proof (cases "is_flip")
              case True note isf = this
              have bfl: "bottleneck s e in_U p1 p2 = (\<delta>, True, vv, e0fwd, up_side)"
                using bn isf by simp
              have invf: "ns_invar (ns_flip s e in_U \<gamma> sel' \<delta> p1 p2)"
                using inv_flip[OF I sel gpp bfl dne] .
              have luF: "ns_loop_impl s = ns_loop_impl (ns_flip s e in_U \<gamma> sel' \<delta> p1 p2)"
                using lu dne isf by simp
              have flipF: "<rd * flow_assn (current_flow s) (iflow si) * pot_assn (potentials s) (ipot si)
                  * tree_assn (spanning_tree s) (itree si) * parent_assn (parent_edge s) (iparent si)
                  * dir_assn (edge_dir s) (idir si) * es_assn (edge_state s) (iestate si)
                  * sel_assn sel' (isel si) * ipath1 si \<mapsto>\<^sub>a l1' * ipath2 si \<mapsto>\<^sub>a l2'>
                 ns_flip_imp si e in_U \<delta> ptr1 ptr2
                <\<lambda>_. rd * flow_assn (augment_flow s e in_U \<delta> p1 p2) (iflow si)
                  * pot_assn (potentials s) (ipot si) * tree_assn (spanning_tree s) (itree si)
                  * parent_assn (parent_edge s) (iparent si) * dir_assn (edge_dir s) (idir si)
                  * es_assn (es_upd (edge_state s) e (if in_U then InL else InU)) (iestate si)
                  * sel_assn sel' (isel si) * ipath1 si \<mapsto>\<^sub>a l1' * ipath2 si \<mapsto>\<^sub>a l2'>"
                by (sep_auto simp: TA1 TA2
                         heap: ns_flip_imp_rule[OF st(1) st(2) st(3) pre(3) gp(1) A5 A6 af1 af2])
              have entP: "rd * flow_assn (augment_flow s e in_U \<delta> p1 p2) (iflow si)
                  * pot_assn (potentials s) (ipot si) * tree_assn (spanning_tree s) (itree si)
                  * parent_assn (parent_edge s) (iparent si) * dir_assn (edge_dir s) (idir si)
                  * es_assn (es_upd (edge_state s) e (if in_U then InL else InU)) (iestate si)
                  * sel_assn sel' (isel si) * ipath1 si \<mapsto>\<^sub>a l1' * ipath2 si \<mapsto>\<^sub>a l2'
                 \<Longrightarrow>\<^sub>A ns_rel (ns_flip s e in_U \<gamma> sel' \<delta> p1 p2) si"
                unfolding ns_rel_def ns_flip_def
                apply (simp only: ex_assn_move_out)
                apply (rule ent_ex_postI[where x = l1'])
                apply (rule ent_ex_postI[where x = l2'])
                apply (sep_auto simp: cardL1 cardL2)
                apply (simp_all add: cardL1[unfolded One_nat_def] cardL2[unfolded One_nat_def])
                done
              show ?thesis
                unfolding luF
                apply (rule ht_bind[OF bottF2])
                apply (rule ht_extract_pre_pure, hypsubst)
                apply (simp only: prod.case if_not_P[OF dne] if_P[OF isf])
                apply (rule ht_bind[OF flipF])
                apply (rule ht_cons_pre[OF entP IHr[OF invf]])
                done
            next
              case False note isf = this
              have bnp: "bottleneck s e in_U p1 p2 = (\<delta>, False, vv, e0fwd, up_side)"
                using bn isf by simp
              obtain psw1 psw2 aa p3 y where piv:
                "\<forall>u \<in> \<V>. pot_value_invar (pot_lookup (potentials s) u)"
                "par_edge s vv \<in> \<E>" "vv \<in> \<V> - {r}"
                "get_path_pair (spanning_tree s)
                    (if in_U = up_side then fst_exec e else snd_exec e)
                    (if in_U = up_side then snd_exec e else fst_exec e) = (psw1, psw2)"
                "walk_betw (abstract_arborescense (spanning_tree s))
                    (if in_U = up_side then fst_exec e else snd_exec e) (psw1 @ aa # p3) r"
                "distinct (psw1 @ aa # p3)" "(vv, y) \<in> set (edges_of_vwalk (psw1 @ [aa]))"
                and invp: "ns_invar (ns_pivot s e in_U \<gamma> sel' \<delta> vv e0fwd up_side p1 p2)"
                using inv_pivot[OF I sel gpp bnp dne] by blast
              obtain Pe1 D1 where rep1:
                "reparent s e p1 vv = (Pe1, D1)" by fastforce
              obtain Pe2 D2 where rep2:
                "reparent s e p2 vv = (Pe2, D2)" by fastforce
              have luP: "ns_loop_impl s = ns_loop_impl (ns_pivot s e in_U \<gamma> sel' \<delta> vv e0fwd up_side p1 p2)"
                using lu dne isf by simp
              have pivF: "<rd * flow_assn (current_flow s) (iflow si) * pot_assn (potentials s) (ipot si)
                  * tree_assn (spanning_tree s) (itree si) * parent_assn (parent_edge s) (iparent si)
                  * dir_assn (edge_dir s) (idir si) * es_assn (edge_state s) (iestate si)
                  * sel_assn sel' (isel si) * ipath1 si \<mapsto>\<^sub>a l1' * ipath2 si \<mapsto>\<^sub>a l2'>
                 ns_pivot_imp si e u v in_U \<gamma> \<delta> vv e0fwd up_side ptr1 ptr2
                <\<lambda>_. rd * flow_assn (augment_flow s e in_U \<delta> (take ptr1 l1') (take ptr2 l2')) (iflow si)
                  * pot_assn (shift_pot (spanning_tree s) vv (potentials s) \<gamma> (in_U \<noteq> up_side)) (ipot si)
                  * tree_assn (swap_edge (spanning_tree s) vv (if in_U = up_side then fst_exec e else snd_exec e)
                                 (if in_U = up_side then snd_exec e else fst_exec e)) (itree si)
                  * (case reparent s e (if in_U = up_side then take ptr1 l1' else take ptr2 l2') vv of (Pe', D') \<Rightarrow>
                       parent_assn Pe' (iparent si) * dir_assn D' (idir si))
                  * es_assn (es_upd (es_upd (edge_state s) e InTree) (par_edge s vv)
                               (if e0fwd then InU else InL)) (iestate si)
                  * sel_assn sel' (isel si) * ipath1 si \<mapsto>\<^sub>a l1' * ipath2 si \<mapsto>\<^sub>a l2'>"
                unfolding uv(1) uv(2)
                by (sep_auto heap: ns_pivot_imp_rule[OF st(1) pre(2) piv(1)[rule_format] st(4) st(2) st(3) pre(3)
                                 gp(1) piv(2) piv(3) refl refl A5 A6 af1 af2 d1 d2 piv(4) gp(2)
                                 piv(5) piv(6) piv(7) gp(3) gp(4)])
              have entP: "rd * flow_assn (augment_flow s e in_U \<delta> (take ptr1 l1') (take ptr2 l2')) (iflow si)
                  * pot_assn (shift_pot (spanning_tree s) vv (potentials s) \<gamma> (in_U \<noteq> up_side)) (ipot si)
                  * tree_assn (swap_edge (spanning_tree s) vv (if in_U = up_side then fst_exec e else snd_exec e)
                                 (if in_U = up_side then snd_exec e else fst_exec e)) (itree si)
                  * (case reparent s e (if in_U = up_side then take ptr1 l1' else take ptr2 l2') vv of (Pe', D') \<Rightarrow>
                       parent_assn Pe' (iparent si) * dir_assn D' (idir si))
                  * es_assn (es_upd (es_upd (edge_state s) e InTree) (par_edge s vv)
                               (if e0fwd then InU else InL)) (iestate si)
                  * sel_assn sel' (isel si) * ipath1 si \<mapsto>\<^sub>a l1' * ipath2 si \<mapsto>\<^sub>a l2'
                 \<Longrightarrow>\<^sub>A ns_rel (ns_pivot s e in_U \<gamma> sel' \<delta> vv e0fwd up_side p1 p2) si"
                unfolding ns_rel_def
                apply (simp only: ex_assn_move_out)
                apply (rule ent_ex_postI[where x = l1'])
                apply (rule ent_ex_postI[where x = l2'])
                apply (sep_auto simp: rep1 rep2 cardL1 cardL2 ns_pivot_def Let_def TA1 TA2)
                apply (simp_all add: mult.assoc cardL1[unfolded One_nat_def] cardL2[unfolded One_nat_def])
                done
              show ?thesis
                unfolding luP
                apply (rule ht_bind[OF bottF2])
                apply (rule ht_extract_pre_pure, hypsubst)
                apply (simp only: prod.case if_not_P[OF dne] if_not_P[OF isf])
                apply (rule ht_bind[OF pivF])
                apply (rule ht_cons_pre[OF entP IHr[OF invp]])
                done
            qed
          qed
        qed
        show ?thesis
          apply (rule ht_bind[OF fstF], rule ht_bind[OF sndF], rule ht_bind[OF gppF])
          apply (simp only: split_paired_all prod.case)
          apply (rule ht_exEI)+
          apply (rule ht_extract_pre_pure)+
          apply (rule tailP)
          apply assumption+
          done
      qed
      show ?thesis
        unfolding ns_rel_def
        apply (rule ht_bind[OF selF])
        apply (rule ht_extract_pre_pure, hypsubst)
        apply (simp only: option.case prod.case)
        apply (rule contBody)
        done
    qed
  qed
qed

text \<open>The refinement above is stated against the heap @{command partial_function}
      @{const ns_loop_impl}, but the functional correctness theorems live on the @{command function}
      @{const ns_loop}. Under @{term \<open>ns_invar s\<close>} the loop terminates (@{text ns_loop_dom_of_invar}),
      so the two agree (@{text ns_loop_dom_impl_same}); transferring along that equality lands the
      imperative result on the \<^emph>\<open>final functional state\<close> @{term \<open>ns_loop s\<close>}.\<close>

lemma ns_loop_imp_correct:
  assumes "ns_invar s"
  shows "<ns_rel s si> ns_loop_imp si
           <\<lambda>res. ns_rel_weak (ns_loop s) si * \<up>(res = network_simplex_state.return (ns_loop s))>"
proof -
  have eq: "ns_loop_impl s = ns_loop s"
    using ns_loop_dom_impl_same[OF ns_loop_dom_of_invar[OF assms]] .
  show ?thesis using ns_loop_imp_rule[THEN mp, OF assms] unfolding eq .
qed
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
      @{text init_state_invar} gives @{term \<open>ns_invar init_state\<close>}, the imperative loop started from
      any heap refining \<open>init_state\<close> refines the functional run @{term \<open>ns_loop init_state\<close>} --- the
      state on which @{text network_simplex_correct} states optimality / unboundedness.\<close>

corollary ns_loop_imp_init:
  "<ns_rel init_state si> ns_loop_imp si
     <\<lambda>res. ns_rel_weak (ns_loop init_state) si
              * \<up>(res = network_simplex_state.return (ns_loop init_state))>"
  using ns_loop_imp_correct[OF init_state_invar] .

end

end

