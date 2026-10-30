theory Network_Simplex
  imports Flow_Theory.Spanning_Tree_Flow
      Flow_Theory.Cost_Optimality
      Data_Structures.Fixed_Univ_Set_Specs
      Data_Structures.Fixed_Univ_Map_Specs
      Data_Structures.Real_Embedding
begin

provenance ai


text \<open>Tagged variant. Instead of the two edge sets @{term L} and @{term U} being stored as two
      separate @{locale fixed_univ_set} values, this development keeps a single
      @{locale fixed_univ_map} @{term edge_state} that maps every edge to a \<^emph>\<open>tag\<close> recording its
      current r\^ole in the spanning-tree structure: @{term InTree} (a tree edge), @{term InL} (at its
      lower bound, i.e. in the former set @{term L}) or @{term InU} (saturated, i.e. in the former set
      @{term U}). The abstract views @{term ns_L_of} / @{term ns_U_of} still denote the very same edge
      sets --- now carved out of @{term \<open>\<E>\<close>} by the tag --- so the structural reasoning is unchanged.\<close>

datatype edge_tag = InTree | InL | InU

locale \<^marker>\<open>provenance ai_human\<close> arborescense_adt =
  fixes V::"'a set"
   and r::"'a"
   and arborescense_invar::"'arbor \<Rightarrow> bool"
   and abstract_arborescense::"'arbor \<Rightarrow> 'a set set"
   and get_path_pair::"'arbor \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a list \<times> 'a list)"
   and swap_edge::"'arbor \<Rightarrow> 'a \<Rightarrow>'a \<Rightarrow>'a \<Rightarrow> 'arbor"
 assumes
   general:
    "r \<in> V"
    "\<And> T. arborescense_invar T \<Longrightarrow> graph_invar (abstract_arborescense T)"
    "\<And> T x y. \<lbrakk>arborescense_invar T; x \<in> V; y \<in> V\<rbrakk>  \<Longrightarrow> 
          \<exists>! p. (walk_betw (abstract_arborescense T) y p x)
                \<and> distinct p"
    "\<And> T. arborescense_invar T \<Longrightarrow> Vs (abstract_arborescense T) = V"
   and get_path_pair:
     "\<And> T p1 p2 u v. \<lbrakk>arborescense_invar T; get_path_pair T u v = (p1,p2); u \<noteq> v; u\<in> V; v \<in> V\<rbrakk> \<Longrightarrow>
          \<exists> a p3. walk_betw (abstract_arborescense T) u (p1 @ a # p3) r \<and>
                walk_betw (abstract_arborescense T) v (p2 @ a # p3) r \<and>
                distinct (p1 @ a # p3) \<and> distinct (p2 @ a # p3) \<and>
                set p1 \<inter> set p2 = {}"
     "\<And> T p1 p2 u v. \<lbrakk>arborescense_invar T; get_path_pair T u v = (p1,p2) ; u \<noteq> v; u\<in> V; v \<in> V\<rbrakk> \<Longrightarrow>
          get_path_pair T v u = (p2,p1)"
  and swap_edge:
      "\<And> T p1 p2 p3 a u v x y. \<lbrakk>arborescense_invar T; get_path_pair T u v = (p1,p2); u \<noteq> v;
                           walk_betw (abstract_arborescense T) u (p1 @ a # p3) r; distinct (p1 @ a # p3);
                           (x, y) \<in> set (edges_of_vwalk (p1 @ [a])); u\<in> V; v \<in> V\<rbrakk> \<Longrightarrow>
                           arborescense_invar (swap_edge T x u v)"
      "\<And> T p1 p2 p3 a u v x y. \<lbrakk>arborescense_invar T; get_path_pair T u v = (p1,p2); u \<noteq> v;
                           walk_betw (abstract_arborescense T) u (p1 @ a # p3) r; distinct (p1 @ a # p3);
                           (x, y) \<in> set (edges_of_vwalk (p1 @ [a])); u\<in> V; v \<in> V\<rbrakk> \<Longrightarrow>
                           abstract_arborescense (swap_edge T x u v) =
                           (abstract_arborescense T - {{x, y}} \<union> {{u, v}})"

section \<open>Abstract data types for the algorithm\<close>

text \<open>Vertex potentials and edge reduced costs are not stored as plain reals. We use two abstract
      \emph{real descriptors}, each abstracted to @{typ real} by a verification-only function that is
      never executed:
      \<^item> a \<^emph>\<open>potential descriptor\<close> @{typ 'p} for the vertex potentials held in the potential array ---
        with invariant \<open>pot_value_invar\<close>, abstraction \<open>pot_value_abstract\<close>, and the two \<^emph>\<open>mixed\<close>
        operations \<open>pot_value_plus, pot_value_minus :: 'p \<Rightarrow> 'r \<Rightarrow> 'p\<close> that shift a potential by a
        reduced cost;
      \<^item> a \<^emph>\<open>reduced-cost descriptor\<close> @{typ 'r} for the value \<open>\<gamma>\<close> the selector returns --- with invariant
        \<open>rcost_invar\<close> and abstraction \<open>rcost_abstract\<close>; it carries no arithmetic of its own (reduced
        costs are never combined with one another).
      The two mixed operations are specified only \<^emph>\<open>conditionally\<close> (axioms \<open>pot_value_plus_spec\<close> /
      \<open>pot_value_minus_spec\<close>): their abstraction law and invariant preservation are guaranteed only
      when the resulting real value is admissible --- a signed edge-cost sum in which \<^emph>\<open>at most one\<close> edge
      touches the root \<open>r\<close> (the predicate \<open>good_pot_val\<close> below). Every potential the algorithm
      maintains is a tree-path cost sum reaching \<open>r\<close> exactly once, so the guard always holds where the
      operations are used. This split and its guard are exactly what later let us realise the
      ``big-M'' method with a pair representation \<open>(m, o)\<close> (an M-coefficient and an ordinary part)
      without numerical-stability issues: the \<open>\<le> 1\<close> root-edge bound keeps \<open>\<bar>m\<bar> \<le> 1\<close> and the
      edge-cost-sum bound keeps the ordinary part from overflowing, so componentwise add/subtract stay
      exact and the constant \<open>M\<close> --- occurring only inside the abstraction --- is chosen once and never
      explicitly computed.\<close>

text \<open>The entering-edge (pivot) rule is abstracted as a small stateful ADT: an invariant
      @{term sel_invar} and a selection function @{term sel_select}. Given the current potentials
      and the two sets @{term L} and @{term U}, the selector returns either @{term None} (no eligible
      edge --- the optimality stopping condition) or @{term "Some (e, in_U, \<gamma>, sel')"}: an entering
      edge @{term e}, a flag telling whether it came from @{term U} (@{term True}) or @{term L}
      (@{term False}), a descriptor @{term \<gamma>} of its reduced cost in the abstract real type, and an
      updated selector. The behavioural specification (invariant preservation and eligibility of the
      returned edge) is added in the proof locale.\<close>

locale \<^marker>\<open>provenance ai_human\<close> edge_selector =
  fixes sel_invar :: "'selector \<Rightarrow> bool"
    and sel_select ::
      "'selector \<Rightarrow> 'parr \<Rightarrow> 'earr
         \<Rightarrow> ('edge \<times> bool \<times> 'r \<times> 'selector) option"

section \<open>Specification locale for the network simplex algorithm\<close>

text \<open>The specification locale conjoins the cost-flow network (@{locale cost_flow_network}, source
      of the costs @{term \<open>\<c>\<close>} and the extended-real capacities @{term \<open>\<u>\<close>}), the spanning-tree ADT
      (@{locale arborescense_adt}), and the array-/set-like stores realising the program state:
      \<^item> @{term flow_lookup} --- an @{locale fixed_univ_map} mapping every edge to its current flow (a
        @{typ real});
      \<^item> @{term pot_lookup} --- an @{locale fixed_univ_map} mapping every vertex to its potential,
        represented in the abstract potential-descriptor type @{typ 'p} (reduced costs use the
        separate descriptor type @{typ 'r}; see the two real-descriptor families above);
      \<^item> @{term parent_lookup} --- an @{locale fixed_univ_map} over the vertices @{term \<open>V - {r}\<close>}
        giving, for each vertex, the graph edge to its predecessor on the path to the root, and
      \<^item> @{term dir_lookup} --- a boolean @{locale fixed_univ_map} over @{term \<open>V - {r}\<close>} recording the
        orientation of that parent edge;
      \<^item> @{term es_lookup} --- an @{locale fixed_univ_map} mapping every edge to its @{typ edge_tag}
        state: @{term InTree} (in the spanning tree), @{term InL} (zero-flow, the former @{term L}) or
        @{term InU} (saturated, the former @{term U}). The zero-flow and saturated edge sets are the
        verification-only views \<open>ns_L_of\<close> / \<open>ns_U_of\<close> carved out of @{term \<open>\<E>\<close>} by the tag.
      In addition we fix the balances @{term b} (the cost-flow network has none) and an executable
      capacity @{term cap} on the reals in which @{term \<open>- 1\<close>} plays the role of infinity, linked to
      the abstract @{term \<open>\<u>\<close>} by the assumptions \<open>cap_infinite\<close> and \<open>cap_finite\<close>. We assume the
      graph has no self-loops (\<open>no_self_loop\<close>), so every entering edge has two distinct endpoints and
      hence a well-defined fundamental circuit (@{term get_path_pair} is specified only for @{term \<open>u \<noteq> v\<close>}).
      The assumptions
      \<open>sel_select_Some\<close> and \<open>sel_select_None\<close> specify the behaviour of the entering-edge selection;
      the repackaged rules \<open>sel_select_SomeD\<close> / \<open>sel_select_NoneD\<close> in the body are the interface the
      loop uses.\<close>

locale \<^marker>\<open>provenance ai_human\<close> network_simplex_spec =
  fixes r :: "'a"
    and sel_select :: "'selector \<Rightarrow> 'parr \<Rightarrow> 'earr \<Rightarrow> ('edge \<times> bool \<times> 'r \<times> 'selector) option"
    and shift_pot :: "'arbor \<Rightarrow> 'a \<Rightarrow> 'parr \<Rightarrow> 'r \<Rightarrow> bool \<Rightarrow> 'parr"
    and get_path_pair :: "'arbor \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a list \<times> 'a list)"
    and swap_edge :: "'arbor \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'arbor"
    and flow_upd :: "'farr \<Rightarrow> 'edge \<Rightarrow> ('n::linordered_idom) \<Rightarrow> 'farr"
    and flow_lookup :: "'farr \<Rightarrow> 'edge \<Rightarrow> 'n"
    and pot_upd :: "'parr \<Rightarrow> 'a \<Rightarrow> 'p \<Rightarrow> 'parr"
    and pot_lookup :: "'parr \<Rightarrow> 'a \<Rightarrow> 'p"
    and parent_upd :: "'pearr \<Rightarrow> 'a \<Rightarrow> 'edge \<Rightarrow> 'pearr"
    and parent_lookup :: "'pearr \<Rightarrow> 'a \<Rightarrow> 'edge"
    and dir_upd :: "'darr \<Rightarrow> 'a \<Rightarrow> bool \<Rightarrow> 'darr"
    and dir_lookup :: "'darr \<Rightarrow> 'a \<Rightarrow> bool"
    and es_upd :: "'earr \<Rightarrow> 'edge \<Rightarrow> edge_tag \<Rightarrow> 'earr"
    and es_lookup :: "'earr \<Rightarrow> 'edge \<Rightarrow> edge_tag"
    and cap :: "'edge \<Rightarrow> 'n"
    and pot_value_plus     :: "'p \<Rightarrow> 'r \<Rightarrow> 'p"
    and pot_value_minus    :: "'p \<Rightarrow> 'r \<Rightarrow> 'p"
    and fst_exec           :: "'edge \<Rightarrow> 'a"
    and snd_exec           :: "'edge \<Rightarrow> 'a"
begin
end

section \<open>Program state\<close>

text \<open>The termination flag of the loop. @{term notyetterm} means the algorithm is still running,
      @{term success} that an optimum spanning tree structure has been reached, and @{term unbounded}
      that step 4 exposed an all-infinite-capacity circuit with @{term \<open>\<gamma> \<noteq> 0\<close>}, i.e. the instance is
      unbounded. (An @{term infeasible} value for the Big-M initialisation will be added later.)\<close>

datatype return = notyetterm | success | unbounded
text \<open>The mutable program state of the network simplex loop. It bundles the current flow and the
      vertex potentials (as array stores), the spanning tree structure --- represented both abstractly
      (@{term spanning_tree}) and concretely through the @{term parent_edge} / @{term edge_dir}
      arrays that, for every non-root vertex, record the graph edge to its predecessor on the path to
      the root and that edge's orientation --- the edge-state array @{term edge_state} tagging every edge
      as @{term InTree}, @{term InL} (zero-flow, i.e. L) or @{term InU} (saturated, i.e. U), the
      (stateful) entering-edge selector, and the termination flag.\<close>

record ('farr, 'parr, 'tree, 'pearr, 'darr, 'earr, 'sel) network_simplex_state =
  current_flow  :: 'farr
  potentials    :: 'parr
  spanning_tree :: 'tree
  parent_edge   :: 'pearr
  edge_dir      :: 'darr
  edge_state    :: 'earr
  edge_sel      :: 'sel
  return        :: return

section \<open>The network simplex loop\<close>

text \<open>We assemble the loop over the program state, following steps 2--6 of the algorithm. Its body
      branches on the four criteria: (i) whether the selector finds an entering edge at all
      (@{term None} --- the structure is optimal); (ii) whether that edge comes from @{term L} or
      @{term U} (the @{term in_U} flag, which fixes the orientation of the fundamental circuit);
      (iii) whether the circuit's bottleneck is infinite (an unbounded negative cycle); and (iv)
      whether the entering edge is itself the bottleneck --- then it merely flips between @{term L} and
      @{term U} with no tree change (@{term ns_flip}) --- or a genuine tree edge leaves and a full pivot
      is performed (@{term ns_pivot}).

      Residual capacities are handled on the reals with @{term \<open>- 1\<close>} as the infinity sentinel
      (matching @{term cap}), and the fundamental circuit is never materialised --- the bottleneck and
      the flow augmentation fold in place over the two vertex paths @{term get_path_pair} returns ---
      so every operation is executable. The @{term parent_edge} / @{term edge_dir} arrays are
      re-parented in place after each swap (@{term reparent}). The orientation conventions --- the
      first/last bottleneck tie-break, the per-side residual directions, the flow-augmentation signs,
      the leaving-edge @{term L}/@{term U} assignment, and the potential-shift sign
      @{term \<open>in_U \<noteq> up_side\<close>} --- have all been cross-checked against LEMON's reference
      implementation; their formal verification awaits the correctness proof.\<close>

context network_simplex_spec
begin

subsection \<open>Reading the state and residual capacities\<close>

text \<open>Run the entering-edge selector on the current potentials and the two edge sets.\<close>
definition "ns_select s = sel_select (edge_sel s) (potentials s) (edge_state s)"

text \<open>Forward residual (remaining capacity) and backward residual (current flow) of a graph edge,
      as reals with @{term \<open>- 1\<close>} standing for $\infty$ (only the forward residual can be infinite).\<close>
definition "res_fwd s a =
  (let c = cap a in if c = - 1 then - 1 else c - flow_lookup (current_flow s) a)"
definition "res_bwd s a = flow_lookup (current_flow s) a"

subsection \<open>Parent edges and their residuals\<close>

text \<open>For a non-root vertex @{term v}: its parent graph edge, and the orientation flag. By
      convention @{term \<open>par_up s v\<close>} is @{const True} iff that edge points \emph{from} @{term v}
      \emph{to} its parent.\<close>
definition "par_edge s v = parent_lookup (parent_edge s) v"
definition "par_up s v = dir_lookup (edge_dir s) v"

text \<open>Residual of @{term v}'s parent edge when the fundamental circuit traverses it upward (child to
      parent, @{term res_up}) resp. downward (parent to child, @{term res_down}). Upward traversal is
      \emph{forward} exactly when the edge natively points to the parent.\<close>
definition "res_up s v =
  (if par_up s v then res_fwd s (par_edge s v) else res_bwd s (par_edge s v))"
definition "res_down s v =
  (if par_up s v then res_bwd s (par_edge s v) else res_fwd s (par_edge s v))"

subsection \<open>Bottleneck (in-place, over the two tree paths)\<close>

text \<open>Minimum of two residuals under the @{term \<open>- 1\<close>} = $\infty$ convention.\<close>
definition "mininf (x::'n) (y::'n) =
  (if x = - 1 then y else if y = - 1 then x else min x y)"

text \<open>Scan a tree path bottom-up (leaf towards the ancestor), returning the smallest residual seen
      (@{term \<open>- 1\<close>} if the path is empty or all-infinite) together with the child vertex of the
      attaining edge. @{term scan_up} is used on the \<open>edge \<rightarrow> ancestor\<close> side and keeps the \emph{last}
      minimiser (nearest the peak, via \<open>\<le>\<close>); @{term scan_down} is used on the \<open>ancestor \<rightarrow> edge\<close> side
      and keeps the \emph{first} minimiser (via \<open><\<close>). No intermediate list is built.\<close>
definition "scan_up s p =
  fold (\<lambda> v acc.
          case acc of (m, best) \<Rightarrow>
            (let rr = res_up s v in
             if rr = - 1 then (m, best)
             else if m = - 1 then (rr, v)
             else if rr \<le> m then (rr, v)
             else (m, best)))
       p ((- 1)::'n, r)"
definition "scan_down s p =
  fold (\<lambda> v acc.
          case acc of (m, best) \<Rightarrow>
            (let rr = res_down s v in
             if rr = - 1 then (m, best)
             else if m = - 1 then (rr, v)
             else if rr < m then (rr, v)
             else (m, best)))
       p ((- 1)::'n, r)"

text \<open>The bottleneck of the fundamental circuit of the entering edge @{term e}, computed in place
      over the two vertex paths @{term p1}, @{term p2} (from @{term get_path_pair}, hoisted into
      @{term ns_loop} and passed in; no circuit list is materialised).
      For an edge in @{term L} (@{term \<open>\<not> in_U\<close>}) flow is pushed forward and the \<open>snd e\<close> side is the
      up-path; for @{term U} the roles swap. The result is @{const None} when every arc is infinite
      (unbounded negative cycle), otherwise @{term \<open>Some (\<delta>, leaving)\<close>} where @{term \<delta>} is the minimum
      residual and @{term leaving} is @{const None} when the entering edge itself is the bottleneck
      (a flip), or @{term \<open>Some (v, e0fwd, up_side)\<close>} giving the leaving edge's child vertex
      @{term v}, whether its arc is forward (saturated) and whether it lies on the up-side of the
      circuit. The peak-based tie-break is realised by preferring the up-path (last), then the
      entering edge, then the down-path (first).\<close>
definition "bottleneck s e in_U p1 p2 =
  (let up_path = (if in_U then p1 else p2);
       down_path = (if in_U then p2 else p1);
       r_e = (if in_U then res_bwd s e else res_fwd s e)
   in case scan_up s up_path of (mu, vu) \<Rightarrow>
      case scan_down s down_path of (md, vd) \<Rightarrow>
        (let d = mininf r_e (mininf mu md) in
         if d = - 1 then (- 1, True, r, False, False)
         else if mu \<noteq> - 1 \<and> mu = d then (d, False, vu, par_up s vu, True)
         else if r_e = d then (d, True, r, False, False)
         else (d, False, vd, \<not> par_up s vd, False)))"

subsection \<open>State updates\<close>

text \<open>Augment the flow by @{term \<delta>} along the fundamental circuit, in place: the entering edge, then
      the up-path (forward when its edges point to the parent), then the down-path (the opposite).
      A degenerate pivot (@{term \<open>\<delta> = 0\<close>}, common under strong feasibility) leaves the flow untouched
      and returns it directly --- no circuit rewrite --- mirroring LEMON's @{text \<open>if (delta > 0)\<close>} guard
      in @{text changeFlow}. (The tree swap, potential shift and re-parenting still happen: only the
      flow update is skippable.)\<close>
definition "augment_flow s e in_U \<delta> p1 p2 =
  (if \<delta> \<le> 0 then current_flow s else
   (let up_path = (if in_U then p1 else p2);
       down_path = (if in_U then p2 else p1);
       f0 = flow_upd (current_flow s) e
              (flow_lookup (current_flow s) e + (if in_U then - \<delta> else \<delta>));
       f1 = fold (\<lambda> v f. let a = par_edge s v in
                    flow_upd f a (flow_lookup f a + (if par_up s v then \<delta> else - \<delta>)))
                 up_path f0
   in fold (\<lambda> v f. let a = par_edge s v in
              flow_upd f a (flow_lookup f a + (if par_up s v then - \<delta> else \<delta>)))
           down_path f1))"

text \<open>Shift the potentials by @{term \<gamma>} (added if @{term up}, else subtracted) over the far side of
      the cut, rooted at @{term v}. This is now a \<^emph>\<open>first-order primitive\<close> @{term shift_pot} of the
      spec locale --- @{term \<open>shift_pot T v pa \<gamma> up\<close>} returns the potential store obtained from
      @{term pa} by shifting every potential in the subtree opposed to the root at @{term v} --- so it
      mirrors the imperative @{term shift_pot_imp} exactly (no higher-order tree-iteration callback).
      Its behaviour is characterised in the proof locale by the assumption @{text shift_pot_spec}.\<close>

text \<open>Terminal states: optimum reached, and unbounded negative cycle found.\<close>
definition "ns_optimal s = s \<lparr> return := success \<rparr>"
definition "ns_unbounded_upd s = s \<lparr> return := unbounded \<rparr>"

text \<open>Degenerate pivot (the entering edge is its own bottleneck, @{term \<open>e = e0\<close>}): the tree and
      potentials are unchanged and @{term e} flips between @{term L} and @{term U}, but the flow is
      still augmented by @{term \<delta>} along the \<^emph>\<open>whole fundamental circuit\<close> via @{const augment_flow}
      (which folds over the pre-computed paths @{term p1}, @{term p2} --- no new list is built) --- not
      merely on @{term e}. This mirrors KV step (6), which augments @{term f} by @{term \<delta>} along
      @{term C} even when @{term \<open>e = e0\<close>} (only @{term T} and @{term \<pi>} stay fixed), and LEMON's
      @{text changeFlow}, which pushes @{term \<delta>} around the cycle regardless of whether the tree
      changes. Updating @{term e} alone would break flow conservation whenever \<open>\<delta> = u e\<close> is nonzero.
      The @{term \<open>\<delta> \<le> 0\<close>} guard inside @{const augment_flow} makes the truly degenerate
      @{term \<open>\<delta> = 0\<close>} case a pure @{term L}/@{term U} relabelling.\<close>
definition "ns_flip s e in_U \<gamma> sel' \<delta> p1 p2 =
  s \<lparr> current_flow := augment_flow s e in_U \<delta> p1 p2,
      edge_state := es_upd (edge_state s) e (if in_U then InL else InU),
      edge_sel := sel' \<rparr>"

text \<open>Re-parenting after a swap. When the entering edge @{term e} replaces the leaving edge (child
      vertex @{term v}), the subtree hanging below @{term v} is re-attached to the rest of the tree
      through @{term e}. Concretely, the spine @{term P} from the far endpoint @{term \<open>hd P\<close>} up to
      @{term v} has its parent pointers \emph{reversed}: the far endpoint gets @{term e} as its new
      parent edge (pointing to the other endpoint of @{term e}, so its direction flag is
      @{term \<open>hd P = fst e\<close>}); every higher spine vertex inherits the \emph{old} parent edge of its
      predecessor, with the orientation flipped. Vertices above @{term v}, and all subtrees hanging
      off the spine, are untouched. Walked in place from @{term \<open>hd P\<close>} up to @{term v} and \emph{no
      further} --- the tail of @{term P} from @{term v} towards the peak is never visited, matching
      LEMON, which walks only the stem @{text \<open>u_out \<dots> u_in\<close>}. The @{term prev} argument carries the
      previous spine vertex (whose \emph{old} orientation, read from @{term s}, is inherited), so
      there is no read-after-write.\<close>
fun \<^marker>\<open>provenance ai_human\<close> reparent_walk where
  "reparent_walk s e v first pe pup [] pd = pd"
| "reparent_walk s e v first pe pup (w # ws) pd =
     (case pd of (parr, darr) \<Rightarrow>
      (let pd' = (if first
                  then (parent_upd parr w e, dir_upd darr w (w = fst_exec e))
                  else (parent_upd parr w pe, dir_upd darr w (\<not> pup)))
       in if w = v then pd'
          else reparent_walk s e v False (par_edge s w) (par_up s w) ws pd'))"

definition "reparent s e P v = reparent_walk s e v True e False P (parent_edge s, edge_dir s)"

text \<open>Full pivot: the entering edge @{term e} enters the tree in place of the leaving edge
      @{term \<open>e0 = par_edge s v\<close>} (child vertex @{term v}). Augment the flow along the circuit, shift
      the potentials over the far side rooted at @{term v} --- the sign is derived from the processing
      direction @{term in_U} and the side @{term up_side} of the leaving edge --- swap the tree edge,
      re-parent the @{term parent_edge} / @{term edge_dir} arrays along the spine @{term P} (the path
      @{term v} lies on), and move @{term e} out of its set and @{term e0} into @{term U} (if
      saturated, @{term e0fwd}) or @{term L}. The shift magnitude @{term \<gamma>} is the entering edge's
      reduced cost and the sign @{term \<open>in_U \<noteq> up_side\<close>} follows LEMON's @{text updatePotential}
      (@{text \<open>\<sigma> = -pred_dir[u_in]\<sqdot>c\<^sub>\<pi>(e)\<close>}), positive exactly when the moved subtree contains the
      head @{term \<open>snd e\<close>}.\<close>
definition "ns_pivot s e in_U \<gamma> sel' \<delta> v e0fwd up_side p1 p2 =
  (let e0 = par_edge s v;
       P = (if in_U = up_side then p1 else p2);
       (parr, darr) = reparent s e P v
   in s \<lparr> current_flow := augment_flow s e in_U \<delta> p1 p2,
          potentials := shift_pot (spanning_tree s) v (potentials s) \<gamma> (in_U \<noteq> up_side),
          spanning_tree := swap_edge (spanning_tree s) v
                             (if in_U = up_side then fst_exec e else snd_exec e)
                             (if in_U = up_side then snd_exec e else fst_exec e),
          parent_edge := parr,
          edge_dir := darr,
          edge_state := es_upd (es_upd (edge_state s) e InTree) e0 (if e0fwd then InU else InL),
          edge_sel := sel' \<rparr>)"

subsection \<open>The loop\<close>

text \<open>One iteration: select an entering edge; if there is none the structure is optimal; otherwise
      compute the bottleneck; if it is infinite the instance is unbounded; otherwise pivot --- a flip
      when the entering edge is the bottleneck (@{term \<open>leaving = None\<close>}), a full swap otherwise ---
      and recurse. Termination is not proven here (@{command function}~@{text \<open>(domintros)\<close>}); the
      executable @{command partial_function} twin will be added later.\<close>
function \<^marker>\<open>provenance ai_human\<close> (domintros) ns_loop where
"ns_loop s =
  (case ns_select s of None \<Rightarrow> ns_optimal s
     | Some (e, in_U, \<gamma>, sel') \<Rightarrow>
       (let (p1, p2) = get_path_pair (spanning_tree s) (fst_exec e) (snd_exec e) in
       (case bottleneck s e in_U p1 p2 of (\<delta>, is_flip, v, e0fwd, up_side) \<Rightarrow>
         if \<delta> = - 1 then ns_unbounded_upd s
         else if is_flip then ns_loop (ns_flip s e in_U \<gamma> sel' \<delta> p1 p2)
         else ns_loop (ns_pivot s e in_U \<gamma> sel' \<delta> v e0fwd up_side p1 p2))))"
  by pat_completeness auto

text \<open>The executable twin: the same body with the recursive calls redirected to itself, defined as a
      @{command partial_function}~@{text \<open>(tailrec)\<close>} so that code equations are produced. It agrees
      with @{const ns_loop} on the domain (see the agreement lemma below).\<close>

partial_function \<^marker>\<open>provenance ai_human\<close> (tailrec) ns_loop_impl where
"ns_loop_impl s =
  (case ns_select s of None \<Rightarrow> ns_optimal s
     | Some (e, in_U, \<gamma>, sel') \<Rightarrow>
       (let (p1, p2) = get_path_pair (spanning_tree s) (fst_exec e) (snd_exec e) in
       (case bottleneck s e in_U p1 p2 of (\<delta>, is_flip, v, e0fwd, up_side) \<Rightarrow>
         if \<delta> = - 1 then ns_unbounded_upd s
         else if is_flip then ns_loop_impl (ns_flip s e in_U \<gamma> sel' \<delta> p1 p2)
         else ns_loop_impl (ns_pivot s e in_U \<gamma> sel' \<delta> v e0fwd up_side p1 p2))))"

lemmas [code] = ns_loop_impl.simps

subsection \<open>Branch state-transformers and guards\<close>

text \<open>The state transformer of each recursive branch, re-deriving from @{term s} alone the values the
      loop body destructures. The two terminal branches reuse @{const ns_optimal} and
      @{const ns_unbounded_upd}.\<close>

definition "ns_flip_upd s =
  (let (e, in_U, \<gamma>, sel') = the (ns_select s);
       (p1, p2) = get_path_pair (spanning_tree s) (fst_exec e) (snd_exec e);
       (\<delta>, is_flip, v, e0fwd, up_side) = bottleneck s e in_U p1 p2
   in ns_flip s e in_U \<gamma> sel' \<delta> p1 p2)"

definition "ns_pivot_upd s =
  (let (e, in_U, \<gamma>, sel') = the (ns_select s);
       (p1, p2) = get_path_pair (spanning_tree s) (fst_exec e) (snd_exec e);
       (\<delta>, is_flip, v, e0fwd, up_side) = bottleneck s e in_U p1 p2
   in ns_pivot s e in_U \<gamma> sel' \<delta> v e0fwd up_side p1 p2)"

text \<open>The four mutually-exclusive, exhaustive branch guards.\<close>

definition "ns_success_cond s =
  (case ns_select s of None \<Rightarrow> True | Some _ \<Rightarrow> False)"

definition "ns_unbounded_cond s =
  (case ns_select s of None \<Rightarrow> False
   | Some (e, in_U, \<gamma>, sel') \<Rightarrow>
       (let (p1, p2) = get_path_pair (spanning_tree s) (fst_exec e) (snd_exec e)
        in (case bottleneck s e in_U p1 p2 of (\<delta>, is_flip, v, e0fwd, up_side) \<Rightarrow> \<delta> = - 1)))"

definition "ns_flip_cond s =
  (case ns_select s of None \<Rightarrow> False
   | Some (e, in_U, \<gamma>, sel') \<Rightarrow>
       (let (p1, p2) = get_path_pair (spanning_tree s) (fst_exec e) (snd_exec e)
        in (case bottleneck s e in_U p1 p2 of (\<delta>, is_flip, v, e0fwd, up_side) \<Rightarrow> \<delta> \<noteq> - 1 \<and> is_flip)))"

definition "ns_pivot_cond s =
  (case ns_select s of None \<Rightarrow> False
   | Some (e, in_U, \<gamma>, sel') \<Rightarrow>
       (let (p1, p2) = get_path_pair (spanning_tree s) (fst_exec e) (snd_exec e)
        in (case bottleneck s e in_U p1 p2 of (\<delta>, is_flip, v, e0fwd, up_side) \<Rightarrow> \<delta> \<noteq> - 1 \<and> \<not> is_flip)))"

end

section \<open>Correctness locale for the network simplex loop\<close>

text \<open>The proof locale extends the executable specification @{locale network_simplex_spec} by
      re-imposing the cost-flow network, the spanning-tree ADT and the five array/selector
      contracts as genuine assumptions, together with the capacity encoding, the selector
      behaviour and the potential-descriptor arithmetic. All correctness reasoning lives here.\<close>

locale \<^marker>\<open>provenance ai_human\<close> network_simplex =
  cost_flow_network where fst = "fst :: 'edge \<Rightarrow> 'a"  and snd = snd+
  real_embedding where h = "h :: 'n \<Rightarrow> real" +
  network_simplex_spec where sel_select = sel_select and flow_upd = flow_upd
      and pot_upd = pot_upd and parent_upd = parent_upd and dir_upd = dir_upd
      and es_upd = es_upd +
  selector: edge_selector where sel_invar = sel_invar and sel_select = sel_select +
  arborescense_adt where V = "\<V> :: 'a set" and r = "r :: 'a"
      and get_path_pair = get_path_pair
      and swap_edge = swap_edge +
  flow_arr: fixed_univ_map where K = "\<E> :: 'edge set" and
      fixed_univ_map_invar = flow_invar and fixed_univ_map_upd = flow_upd and
      fixed_univ_map_lookup = flow_lookup +
  pot_arr: fixed_univ_map where K = "\<V> :: 'a set" and
      fixed_univ_map_invar = pot_invar and fixed_univ_map_upd = pot_upd and
      fixed_univ_map_lookup = pot_lookup +
  parent_arr: fixed_univ_map where K = "\<V> - {r} :: 'a set" and
      fixed_univ_map_invar = parent_invar and fixed_univ_map_upd = parent_upd and
      fixed_univ_map_lookup = parent_lookup +
  dir_arr: fixed_univ_map where K = "\<V> - {r} :: 'a set" and
      fixed_univ_map_invar = dir_invar and fixed_univ_map_upd = dir_upd and
      fixed_univ_map_lookup = dir_lookup +
  es_arr: fixed_univ_map where K = "\<E> :: 'edge set" and
      fixed_univ_map_invar = es_invar and fixed_univ_map_upd = es_upd and
      fixed_univ_map_lookup = es_lookup
    for fst and snd and 
        flow_invar :: "'farr \<Rightarrow> bool" and pot_invar :: "'parr \<Rightarrow> bool"
    and parent_invar :: "'pearr \<Rightarrow> bool" and dir_invar :: "'darr \<Rightarrow> bool"
    and es_invar :: "'earr \<Rightarrow> bool" and sel_invar :: "'selector \<Rightarrow> bool"
    and sel_select :: "'selector \<Rightarrow> 'parr \<Rightarrow> 'earr
                         \<Rightarrow> ('edge \<times> bool \<times> 'r \<times> 'selector) option"
    and flow_upd :: "'farr \<Rightarrow> 'edge \<Rightarrow> ('n::linordered_idom) \<Rightarrow> 'farr"
    and h :: "'n \<Rightarrow> real"
    and pot_upd :: "'parr \<Rightarrow> 'a \<Rightarrow> 'p \<Rightarrow> 'parr"
    and parent_upd :: "'pearr \<Rightarrow> 'a \<Rightarrow> 'edge \<Rightarrow> 'pearr"
    and dir_upd :: "'darr \<Rightarrow> 'a \<Rightarrow> bool \<Rightarrow> 'darr"
    and es_upd :: "'earr \<Rightarrow> 'edge \<Rightarrow> edge_tag \<Rightarrow> 'earr"    and pot_value_invar :: "'p \<Rightarrow> bool" and rcost_invar :: "'r \<Rightarrow> bool"
    and pot_value_abstract :: "'p \<Rightarrow> real" and rcost_abstract :: "'r \<Rightarrow> real" +
  fixes b :: "'a \<Rightarrow> real"
  assumes fst_exec_coincide:
      "\<And> e. e \<in> \<E> \<Longrightarrow> fst_exec e = fst e"
    and snd_exec_coincide:
      "\<And> e. e \<in> \<E> \<Longrightarrow> snd_exec e = snd e"
    and cap_infinite:
      "\<And> e. e \<in> \<E> \<Longrightarrow> (cap e = - 1) \<longleftrightarrow> \<u> e = \<infinity>"
    and cap_finite:
      "\<And> e. \<lbrakk>e \<in> \<E>; cap e \<ge> 0\<rbrakk> \<Longrightarrow> \<u> e = ereal (h (cap e))"
    and cap_nonneg:
      "\<And> e. e \<in> \<E> \<Longrightarrow> 0 \<le> cap e \<or> cap e = - 1"
    and sel_select_Some:
      "\<And> sel \<pi> es e in_U \<gamma> sel'.
         \<lbrakk>sel_invar sel; pot_invar \<pi>; \<forall> v \<in> \<V>. pot_value_invar (pot_lookup \<pi> v);
           pot_value_abstract (pot_lookup \<pi> r) = 0;
           es_invar es; sel_select sel \<pi> es = Some (e, in_U, \<gamma>, sel')\<rbrakk> \<Longrightarrow>
           sel_invar sel' \<and> rcost_invar \<gamma> \<and>
           rcost_abstract \<gamma>
             = \<c> e + pot_value_abstract (pot_lookup \<pi> (fst e))
                   - pot_value_abstract (pot_lookup \<pi> (snd e)) \<and>
           (if in_U then e \<in> \<E> \<and> fst e \<noteq> snd e \<and> es_lookup es e = InU \<and> rcost_abstract \<gamma> > 0
                    else e \<in> \<E> \<and> fst e \<noteq> snd e \<and> es_lookup es e = InL \<and> rcost_abstract \<gamma> < 0)"
    and sel_select_None:
      "\<And> sel \<pi> es.
         \<lbrakk>sel_invar sel; pot_invar \<pi>; \<forall> v \<in> \<V>. pot_value_invar (pot_lookup \<pi> v);
           pot_value_abstract (pot_lookup \<pi> r) = 0;
           es_invar es; sel_select sel \<pi> es = None\<rbrakk> \<Longrightarrow>
           (\<forall> e \<in> \<E>. fst e \<noteq> snd e \<longrightarrow> es_lookup es e = InL \<longrightarrow> \<c> e + pot_value_abstract (pot_lookup \<pi> (fst e))
                                      - pot_value_abstract (pot_lookup \<pi> (snd e)) \<ge> 0) \<and>
           (\<forall> e \<in> \<E>. fst e \<noteq> snd e \<longrightarrow> es_lookup es e = InU \<longrightarrow> \<c> e + pot_value_abstract (pot_lookup \<pi> (fst e))
                                      - pot_value_abstract (pot_lookup \<pi> (snd e)) \<le> 0)"
    and pot_value_plus_spec:
      "\<And> p g. \<lbrakk>pot_value_invar p; rcost_invar g;
           \<exists> A D. A \<subseteq> \<E> \<and> D \<subseteq> \<E> \<and>
                  card {e \<in> A \<union> D. fst e = r \<or> snd e = r} \<le> 1 \<and>
                  pot_value_abstract p + rcost_abstract g = (\<Sum> e \<in> A. \<c> e) - (\<Sum> e \<in> D. \<c> e)\<rbrakk> \<Longrightarrow>
           pot_value_abstract (pot_value_plus p g) = pot_value_abstract p + rcost_abstract g \<and>
           pot_value_invar (pot_value_plus p g)"
    and pot_value_minus_spec:
      "\<And> p g. \<lbrakk>pot_value_invar p; rcost_invar g;
           \<exists> A D. A \<subseteq> \<E> \<and> D \<subseteq> \<E> \<and>
                  card {e \<in> A \<union> D. fst e = r \<or> snd e = r} \<le> 1 \<and>
                  pot_value_abstract p - rcost_abstract g = (\<Sum> e \<in> A. \<c> e) - (\<Sum> e \<in> D. \<c> e)\<rbrakk> \<Longrightarrow>
           pot_value_abstract (pot_value_minus p g) = pot_value_abstract p - rcost_abstract g \<and>
           pot_value_invar (pot_value_minus p g)"
    and shift_pot_spec:
      "\<And> T v pa g up.
         \<lbrakk>arborescense_invar T; v \<in> \<V>; pot_invar pa;
           \<And>u. u \<in> \<V> \<Longrightarrow> pot_value_invar (pot_lookup pa u)\<rbrakk> \<Longrightarrow>
         \<exists> xs. set xs = {x. \<exists>p. walk_betw (abstract_arborescense T) x p r \<and> distinct p \<and> v \<in> set p}
               \<and> distinct xs
               \<and> shift_pot T v pa g up
                   = foldr (\<lambda> x acc. pot_upd acc x
                        ((if up then pot_value_plus else pot_value_minus) (pot_lookup acc x) g)) xs pa"
begin

text \<open>The executable endpoint functions @{term fst_exec} / @{term snd_exec} coincide with the
      abstract @{term fst} / @{term snd} on the edge set @{term \<E>}. Every edge the loop ever handles
      lies in @{term \<E>}, so once @{term \<open>e \<in> \<E>\<close>} is known these rewrite the executable projections
      back to the abstract ones, letting the existing proofs go through unchanged.\<close>

lemmas fst_exec_eq[simp] = fst_exec_coincide
lemmas snd_exec_eq[simp] = snd_exec_coincide


text \<open>Abstract (verification-only) view of the potentials, and the reduced cost
      @{term \<open>c\<pi> e = \<c> e + \<pi> (fst e) - \<pi> (snd e)\<close>} of an edge under a potential array.\<close>

abbreviation "abstract_pot \<pi> v \<equiv> pot_value_abstract (pot_lookup \<pi> v)"

definition "reduced_cost \<pi> e = \<c> e + abstract_pot \<pi> (fst e) - abstract_pot \<pi> (snd e)"

text \<open>The guard under which the potential-descriptor arithmetic (@{term pot_value_plus} /
      @{term pot_value_minus}) is specified: a real @{term x} is \emph{admissible} when it is a signed
      sum of edge costs in which \<^emph>\<open>at most one\<close> edge touches the root @{term r}. Every potential the
      algorithm maintains is a tree-path cost sum reaching @{term r} exactly once, so this holds for
      every value fed to the descriptor operations --- and it is exactly what a ``big-M'' pair
      representation \<open>(m, o)\<close> needs (the \<open>\<le> 1\<close> root edge bounds the M-coefficient \<open>\<bar>m\<bar> \<le> 1\<close>, and being
      a genuine edge-cost sum bounds the ordinary part \<open>o\<close>).\<close>

definition "good_pot_val x \<equiv>
  (\<exists> A D. A \<subseteq> \<E> \<and> D \<subseteq> \<E> \<and>
          card {e \<in> A \<union> D. fst e = r \<or> snd e = r} \<le> 1 \<and>
          x = (\<Sum> e \<in> A. \<c> e) - (\<Sum> e \<in> D. \<c> e))"

text \<open>A potential store is \emph{valid} when its array invariant holds and every stored vertex
      potential is a well-formed element of the abstract real type.\<close>

definition "pot_valid \<pi> \<equiv> pot_invar \<pi> \<and> (\<forall> v \<in> \<V>. pot_value_invar (pot_lookup \<pi> v))"

text \<open>The precondition under which the edge selection is specified: the selector, the potentials
      and both edge sets are well-formed.\<close>

definition "selection_precond sel \<pi> es \<equiv>
  sel_invar sel \<and> pot_valid \<pi> \<and> es_invar es \<and> pot_value_abstract (pot_lookup \<pi> r) = 0"

text \<open>@{term \<open>entering_edge \<pi> L U e in_U\<close>} states that @{term e} is an eligible entering edge with the
      given membership flag: taken from @{term U} with strictly positive reduced cost, or from
      @{term L} with strictly negative reduced cost. @{term \<open>no_entering_edge \<pi> L U\<close>} is the negation
      over all of @{term L} and @{term U} --- the optimality (stopping) condition.\<close>

definition "entering_edge \<pi> es e in_U \<equiv>
  (if in_U then e \<in> \<E> \<and> fst e \<noteq> snd e \<and> es_lookup es e = InU \<and> reduced_cost \<pi> e > 0
           else e \<in> \<E> \<and> fst e \<noteq> snd e \<and> es_lookup es e = InL \<and> reduced_cost \<pi> e < 0)"

definition "no_entering_edge \<pi> es \<equiv>
  (\<forall> e \<in> \<E>. fst e \<noteq> snd e \<longrightarrow> es_lookup es e = InL \<longrightarrow> reduced_cost \<pi> e \<ge> 0) \<and>
  (\<forall> e \<in> \<E>. fst e \<noteq> snd e \<longrightarrow> es_lookup es e = InU \<longrightarrow> reduced_cost \<pi> e \<le> 0)"

text \<open>The two selection assumptions above are stated on unfolded expressions (a locale cannot refer
      to its own body definitions). The following two rules repackage them in terms of the
      predicates just introduced --- this is the interface the loop and its correctness proof use.
      Whenever the selection precondition holds: a @{term \<open>Some (e, in_U, \<gamma>, sel')\<close>} result yields an
      updated selector satisfying its invariant, a well-formed descriptor @{term \<gamma>} whose value is
      exactly the reduced cost of @{term e}, and an eligible entering edge with flag @{term in_U}; a
      @{term None} result means no entering edge exists, i.e. the structure is optimal.\<close>

lemma sel_select_SomeD:
  assumes "selection_precond sel \<pi> es" "sel_select sel \<pi> es = Some (e, in_U, \<gamma>, sel')"
  shows "sel_invar sel'" and "rcost_invar \<gamma>"
    and "rcost_abstract \<gamma> = reduced_cost \<pi> e" and "entering_edge \<pi> es e in_U"
  using sel_select_Some[of sel \<pi> es e in_U \<gamma> sel'] assms
  by (auto simp: selection_precond_def pot_valid_def reduced_cost_def entering_edge_def)

lemma sel_select_NoneD:
  assumes "selection_precond sel \<pi> es" "sel_select sel \<pi> es = None"
  shows "no_entering_edge \<pi> es"
  using sel_select_None[of sel \<pi> es] assms
  by (auto simp: selection_precond_def pot_valid_def no_entering_edge_def reduced_cost_def)

subsection \<open>Introduction / elimination rules for the guards\<close>

lemma ns_success_condE:
  assumes "ns_success_cond s" "ns_select s = None \<Longrightarrow> Q"
  shows Q
  using assms by (auto simp: ns_success_cond_def split: option.splits)

lemma ns_success_condI: "ns_select s = None \<Longrightarrow> ns_success_cond s"
  by (auto simp: ns_success_cond_def)

lemma ns_unbounded_condE:
  assumes "ns_unbounded_cond s"
    "\<And> e in_U \<gamma> sel' p1 p2 is_flip v e0fwd up_side.
       \<lbrakk>ns_select s = Some (e, in_U, \<gamma>, sel');
        get_path_pair (spanning_tree s) (fst_exec e) (snd_exec e) = (p1, p2);
        bottleneck s e in_U p1 p2 = (- 1, is_flip, v, e0fwd, up_side)\<rbrakk> \<Longrightarrow> Q"
  shows Q
  using assms by (auto simp: ns_unbounded_cond_def Let_def split: option.splits prod.splits)

lemma ns_unbounded_condI:
  "\<lbrakk>ns_select s = Some (e, in_U, \<gamma>, sel');
    get_path_pair (spanning_tree s) (fst_exec e) (snd_exec e) = (p1, p2);
    bottleneck s e in_U p1 p2 = (- 1, is_flip, v, e0fwd, up_side)\<rbrakk> \<Longrightarrow> ns_unbounded_cond s"
  by (auto simp: ns_unbounded_cond_def Let_def)

lemma ns_flip_condE:
  assumes "ns_flip_cond s"
    "\<And> e in_U \<gamma> sel' p1 p2 \<delta> v e0fwd up_side.
       \<lbrakk>ns_select s = Some (e, in_U, \<gamma>, sel');
        get_path_pair (spanning_tree s) (fst_exec e) (snd_exec e) = (p1, p2);
        bottleneck s e in_U p1 p2 = (\<delta>, True, v, e0fwd, up_side); \<delta> \<noteq> - 1\<rbrakk> \<Longrightarrow> Q"
  shows Q
  using assms by (auto simp: ns_flip_cond_def Let_def split: option.splits prod.splits)

lemma ns_flip_condI:
  "\<lbrakk>ns_select s = Some (e, in_U, \<gamma>, sel');
    get_path_pair (spanning_tree s) (fst_exec e) (snd_exec e) = (p1, p2);
    bottleneck s e in_U p1 p2 = (\<delta>, True, v, e0fwd, up_side); \<delta> \<noteq> - 1\<rbrakk> \<Longrightarrow> ns_flip_cond s"
  by (auto simp: ns_flip_cond_def Let_def)

lemma ns_pivot_condE:
  assumes "ns_pivot_cond s"
    "\<And> e in_U \<gamma> sel' p1 p2 \<delta> v e0fwd up_side.
       \<lbrakk>ns_select s = Some (e, in_U, \<gamma>, sel');
        get_path_pair (spanning_tree s) (fst_exec e) (snd_exec e) = (p1, p2);
        bottleneck s e in_U p1 p2 = (\<delta>, False, v, e0fwd, up_side); \<delta> \<noteq> - 1\<rbrakk> \<Longrightarrow> Q"
  shows Q
  using assms by (auto simp: ns_pivot_cond_def Let_def split: option.splits prod.splits)

lemma ns_pivot_condI:
  "\<lbrakk>ns_select s = Some (e, in_U, \<gamma>, sel');
    get_path_pair (spanning_tree s) (fst_exec e) (snd_exec e) = (p1, p2);
    bottleneck s e in_U p1 p2 = (\<delta>, False, v, e0fwd, up_side); \<delta> \<noteq> - 1\<rbrakk> \<Longrightarrow> ns_pivot_cond s"
  by (auto simp: ns_pivot_cond_def Let_def)

lemma ns_loop_cases:
  assumes "ns_success_cond s \<Longrightarrow> P"
          "ns_unbounded_cond s \<Longrightarrow> P"
          "ns_flip_cond s \<Longrightarrow> P"
          "ns_pivot_cond s \<Longrightarrow> P"
  shows P
proof -
  have "ns_success_cond s \<or> ns_unbounded_cond s \<or> ns_flip_cond s \<or> ns_pivot_cond s"
    by (auto simp: ns_success_cond_def ns_unbounded_cond_def ns_flip_cond_def ns_pivot_cond_def
             Let_def split: option.splits prod.splits)
  then show P using assms by blast
qed

subsection \<open>One-step unfolding and tailored induction\<close>

lemma ns_loop_simps:
  assumes "ns_loop_dom s"
  shows "ns_success_cond s \<Longrightarrow> ns_loop s = ns_optimal s"
        "ns_unbounded_cond s \<Longrightarrow> ns_loop s = ns_unbounded_upd s"
        "ns_flip_cond s \<Longrightarrow> ns_loop s = ns_loop (ns_flip_upd s)"
        "ns_pivot_cond s \<Longrightarrow> ns_loop s = ns_loop (ns_pivot_upd s)"
  by (auto elim!: ns_success_condE ns_unbounded_condE ns_flip_condE ns_pivot_condE
           simp: ns_loop.psimps[OF assms] ns_flip_upd_def ns_pivot_upd_def Let_def)

lemma ns_loop_impl_simps:
  shows "ns_success_cond s \<Longrightarrow> ns_loop_impl s = ns_optimal s"
        "ns_unbounded_cond s \<Longrightarrow> ns_loop_impl s = ns_unbounded_upd s"
        "ns_flip_cond s \<Longrightarrow> ns_loop_impl s = ns_loop_impl (ns_flip_upd s)"
        "ns_pivot_cond s \<Longrightarrow> ns_loop_impl s = ns_loop_impl (ns_pivot_upd s)"
  by (subst ns_loop_impl.simps,
      auto elim!: ns_success_condE ns_unbounded_condE ns_flip_condE ns_pivot_condE
           simp: ns_flip_upd_def ns_pivot_upd_def Let_def)+

lemma ns_loop_induct:
  assumes "ns_loop_dom s"
    "\<And> s. \<lbrakk>ns_loop_dom s;
            ns_flip_cond s \<Longrightarrow> P (ns_flip_upd s);
            ns_pivot_cond s \<Longrightarrow> P (ns_pivot_upd s)\<rbrakk> \<Longrightarrow> P s"
  shows "P s"
  by (rule ns_loop.pinduct[OF assms(1)], rule assms(2))
     (auto elim!: ns_flip_condE ns_pivot_condE simp: ns_flip_upd_def ns_pivot_upd_def Let_def)

subsection \<open>Agreement of the executable twin with the specification loop\<close>

lemma ns_loop_dom_impl_same:
  assumes "ns_loop_dom s"
  shows "ns_loop_impl s = ns_loop s"
proof (induction rule: ns_loop_induct[OF assms])
  case (1 s)
  then show ?case by (cases rule: ns_loop_cases[of s]) (simp_all add: ns_loop_impl_simps ns_loop_simps)
qed

lemma ns_loop_dom_impl_cong:
  assumes "ns_loop_dom s'" "s = s'"
  shows "ns_loop_impl s = ns_loop s'"
  using ns_loop_dom_impl_same assms by auto

subsection \<open>Domain introduction rules\<close>

lemma ns_loop_dom_success: "ns_success_cond s \<Longrightarrow> ns_loop_dom s"
  by (auto elim!: ns_success_condE intro: ns_loop.domintros)

lemma ns_loop_dom_unbounded: "ns_unbounded_cond s \<Longrightarrow> ns_loop_dom s"
  by (auto elim!: ns_unbounded_condE intro: ns_loop.domintros)

lemma ns_loop_dom_flip:
  "\<lbrakk>ns_flip_cond s; ns_loop_dom (ns_flip_upd s)\<rbrakk> \<Longrightarrow> ns_loop_dom s"
  by (auto intro: ns_loop.domintros simp: ns_flip_upd_def Let_def elim!: ns_flip_condE)

lemma ns_loop_dom_pivot:
  "\<lbrakk>ns_pivot_cond s; ns_loop_dom (ns_pivot_upd s)\<rbrakk> \<Longrightarrow> ns_loop_dom s"
  by (auto intro: ns_loop.domintros simp: ns_pivot_upd_def Let_def elim!: ns_pivot_condE)

lemma ns_loop_simps_without_dom:
  shows "ns_success_cond s \<Longrightarrow> ns_loop s = ns_optimal s"
        "ns_unbounded_cond s \<Longrightarrow> ns_loop s = ns_unbounded_upd s"
  using ns_loop_dom_success ns_loop_dom_unbounded ns_loop_simps by auto

section \<open>Invariants of the loop state\<close>

text \<open>Abstract (verification-only) views of a program state @{term s}: the current flow as a plain
      real-valued function on edges, the potential as a real-valued function on vertices, the tree
      edge set @{term T} as the image of the parent-edge array over the non-root vertices, and the
      two edge sets @{term L} (zero-flow) and @{term U} (saturated).\<close>

abbreviation "ns_flow_of s \<equiv> h \<circ> flow_lookup (current_flow s)"
abbreviation "ns_pot_of s \<equiv> abstract_pot (potentials s)"
abbreviation "ns_tree_edges s \<equiv> parent_lookup (parent_edge s) ` (\<V> - {r})"

text \<open>The zero-flow (@{term L}) and saturated (@{term U}) edge sets, carved out of @{term \<open>\<E>\<close>} by the
      @{term edge_state} tag. These are kept as \<^emph>\<open>definitions\<close> (not abbreviations) so that they behave
      as opaque sets in the downstream cardinality/finiteness reasoning --- exactly like the former
      \<open>set_abstract\<close>-based views; unfold \<open>ns_L_of_def\<close> / \<open>ns_U_of_def\<close> when the tag is actually needed.\<close>

definition "ns_L_of s = {e \<in> \<E>. fst e \<noteq> snd e \<and> es_lookup (edge_state s) e = InL}"
definition "ns_U_of s = {e \<in> \<E>. fst e \<noteq> snd e \<and> es_lookup (edge_state s) e = InU}"

text \<open>Self-loops are not classified by the tag array; for the spanning-tree partition they are folded
      back into @{term L} / @{term U} by cost: a non-negative-cost self-loop (which carries zero flow)
      sits in @{term L}, a negative-cost one (saturated) in @{term U}. These sets depend only on the
      static cost and edge set, so they are the same in every state.\<close>

definition "ns_selfloops_L = {e \<in> \<E>. fst e = snd e \<and> 0 \<le> \<c> e}"
definition "ns_selfloops_U = {e \<in> \<E>. fst e = snd e \<and> \<c> e < 0}"

text \<open>\<^bold>\<open>(1) Data-structure invariant.\<close> Every store of the state is well-formed: the flow, parent-edge
      and direction arrays satisfy their array invariants, the potential store is @{term pot_valid}
      (array invariant plus well-formed abstract reals at every vertex), both edge sets and the
      selector satisfy their invariants, and the abstract spanning tree is a valid arborescence. As
      the array lookups are total and the key sets are fixed statically, no domain conditions are
      needed (unlike \<open>implementation_invar\<close> for Orlin's algorithm).\<close>

definition "ns_invar_impl s \<equiv>
  flow_invar (current_flow s) \<and>
  pot_valid (potentials s) \<and>
  parent_invar (parent_edge s) \<and>
  dir_invar (edge_dir s) \<and>
  es_invar (edge_state s) \<and>
  sel_invar (edge_sel s) \<and>
  arborescense_invar (spanning_tree s)"

text \<open>\<^bold>\<open>(A) b-flow.\<close> The current flow is a feasible @{term b}-flow: it respects the capacity bounds
      (@{term isuflow}, i.e. \<open>0 \<le> f e \<le> \<u> e\<close> on \<^emph>\<open>every\<close> edge) and conserves the balances @{term b}
      at every vertex. This is the invariant that was missing from the informal list; reusing the
      library's \<open>_ is _ flow\<close> predicate rather than \<open>isuflow\<close> supplies flow conservation on top of
      global feasibility.\<close>

definition "ns_invar_bflow s \<equiv> (ns_flow_of s) is b flow"

text \<open>\<^bold>\<open>(2) Spanning tree structure.\<close> @{term \<open>(r, T, L, U)\<close>} is a spanning tree structure: the edge
      universe @{term \<open>\<E>\<close>} splits disjointly into the tree edges, @{term L} and @{term U}, and the
      tree edges form a spanning arborescence rooted at @{term r}.\<close>

definition "ns_invar_partition s \<equiv>
  spanning_tree_partition r (ns_tree_edges s)
    (ns_L_of s \<union> ns_selfloops_L) (ns_U_of s \<union> ns_selfloops_U)"

text \<open>\<^bold>\<open>(5) Flow fits the structure.\<close> Edges in @{term L} carry zero flow and edges in @{term U} are
      saturated.\<close>

definition "ns_invar_flow_fits s \<equiv>
  flow_fits_spanning_tree_partition (ns_tree_edges s) (ns_L_of s) (ns_U_of s) (ns_flow_of s)"

text \<open>\<^bold>\<open>(4) Potential fits the structure.\<close> The root has potential @{term 0} and every tree edge has
      zero reduced cost --- the library's @{const potential_fits_spanning_tree_partition}, whose
      per-edge condition \<open>\<c> e + \<pi> (fst e) - \<pi> (snd e) = 0\<close> is exactly \<open>reduced_cost \<pi> e = 0\<close>. This
      KV-standard convention matches the selector (@{term sel_select}) and the library's optimality
      certificate in .\<close>

definition "ns_invar_pot_fits s \<equiv>
  potential_fits_spanning_tree_partition r (ns_tree_edges s) (ns_pot_of s)"

text \<open>\<^bold>\<open>(3) Strict feasibility on the tree.\<close> The strict half that, together with the capacity bounds
      already supplied by @{term ns_invar_bflow}, upgrades feasibility to \<^emph>\<open>strong\<close> feasibility: an
      upward parent edge (pointing from the vertex to its parent, @{term \<open>par_up s v\<close>}) has flow
      strictly below its capacity, and a downward parent edge has strictly positive flow.\<close>

definition "ns_invar_strict s \<equiv>
  (\<forall> v \<in> \<V> - {r}.
     if par_up s v
     then ereal (h (flow_lookup (current_flow s) (par_edge s v))) < \<u> (par_edge s v)
     else flow_lookup (current_flow s) (par_edge s v) > 0)"

text \<open>The parent vertex of a non-root vertex @{term v}: the endpoint of its parent edge other than
      @{term v}, read off through the stored orientation. By convention \<open>par_up s v\<close> holds iff the
      parent edge points from @{term v} to its parent, so the parent is \<open>snd (par_edge s v)\<close> when
      \<open>par_up s v\<close> and \<open>fst (par_edge s v)\<close> otherwise.\<close>

definition "par_vx s v = (if par_up s v then snd (par_edge s v) else fst (par_edge s v))"

text \<open>\<^bold>\<open>(C) Edge $\leftrightarrow$ tree-edge correspondence.\<close> The bridge tying the concrete @{term parent_edge} and
      @{term edge_dir} arrays to the abstract spanning tree. For every non-root vertex @{term v}:
      \<^item> its parent edge is a genuine graph edge, \<open>par_edge s v \<in> \<E>\<close>;
      \<^item> the direction flag agrees with @{term fst}/@{term snd}: @{term v} is the tail
        (\<open>fst (par_edge s v) = v\<close>) exactly when \<open>par_up s v\<close>, i.e. the edge is oriented from @{term v}
        towards its parent iff the flag says so --- this is what \<^emph>\<open>brings @{term par_up}, @{term edge_dir}
        and the tree together\<close>;
      \<^item> the other endpoint \<open>par_vx s v\<close> is really @{term v}'s predecessor towards the root: the unique
        simple walk from @{term v} to @{term r} in the tree starts \<open>v # par_vx s v # \<dots>\<close>.
      The final conjunct states that the undirected projection of the parent edges is exactly the
      abstract arborescence, so the array view @{term \<open>ns_tree_edges s\<close>} and @{term \<open>spanning_tree s\<close>}
      denote the same tree.\<close>

definition "ns_invar_tree s \<equiv>
  (\<forall> v \<in> \<V> - {r}.
     par_edge s v \<in> \<E>
   \<and> (if par_up s v then fst (par_edge s v) = v else snd (par_edge s v) = v)
   \<and> (\<exists> q. distinct (v # par_vx s v # q)
           \<and> walk_betw (abstract_arborescense (spanning_tree s)) v (v # par_vx s v # q) r))
  \<and> (\<lambda> e. {fst e, snd e}) ` (ns_tree_edges s) = abstract_arborescense (spanning_tree s)"

text \<open>Self-loops are outside the L/U/T tag classification (the array only classifies non-self-loops);
      they are folded into the partition's @{term L} / @{term U} sets by cost. This invariant fixes their
      \<^emph>\<open>flow\<close>: a non-negative-cost self-loop carries zero flow (so it belongs, at flow 0, in the
      partition's @{term L}) and a negative-cost one is saturated (so it belongs, at flow @{term \<open>\<u> e\<close>},
      in @{term U}). A self-loop has reduced cost equal to its plain cost (the potentials cancel) and,
      since @{const entering_edge} now requires @{term \<open>fst e \<noteq> snd e\<close>}, a self-loop is never entering and
      never a tree edge, so its flow never changes and the classification is trivially preserved. This is
      what the pivot ever needed the old \<open>no_self_loop\<close> axiom for, and it supplies the complementary
      slackness of self-loops to the optimality certificate.\<close>

definition "ns_invar_selfloop s \<equiv>
  (\<forall> e \<in> \<E>. fst e = snd e \<longrightarrow>
       (0 \<le> \<c> e \<longrightarrow> ns_flow_of s e = 0)
     \<and> (\<c> e < 0 \<longrightarrow> ereal (ns_flow_of s e) = \<u> e))"

text \<open>The overall loop invariant is the conjunction of the eight predicates above.\<close>

definition "ns_invar s \<equiv>
  ns_invar_impl s \<and> ns_invar_bflow s \<and> ns_invar_partition s \<and>
  ns_invar_flow_fits s \<and> ns_invar_pot_fits s \<and> ns_invar_strict s \<and> ns_invar_tree s
  \<and> ns_invar_selfloop s"

subsection \<open>Introduction, elimination and destruction rules\<close>

text \<open>\<^bold>\<open>(1) Data-structure invariant.\<close>\<close>

lemma ns_invar_implI:
  "\<lbrakk>flow_invar (current_flow s); pot_valid (potentials s); parent_invar (parent_edge s);
    dir_invar (edge_dir s); es_invar (edge_state s);
    sel_invar (edge_sel s); arborescense_invar (spanning_tree s)\<rbrakk>
   \<Longrightarrow> ns_invar_impl s"
  by (simp add: ns_invar_impl_def)

lemma ns_invar_implE:
  "ns_invar_impl s \<Longrightarrow>
     (\<lbrakk>flow_invar (current_flow s); pot_valid (potentials s); parent_invar (parent_edge s);
        dir_invar (edge_dir s); es_invar (edge_state s);
        sel_invar (edge_sel s); arborescense_invar (spanning_tree s)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (simp add: ns_invar_impl_def)

lemma ns_invar_implD:
  "ns_invar_impl s \<Longrightarrow> flow_invar (current_flow s)"
  "ns_invar_impl s \<Longrightarrow> pot_valid (potentials s)"
  "ns_invar_impl s \<Longrightarrow> parent_invar (parent_edge s)"
  "ns_invar_impl s \<Longrightarrow> dir_invar (edge_dir s)"
  "ns_invar_impl s \<Longrightarrow> es_invar (edge_state s)"
  "ns_invar_impl s \<Longrightarrow> sel_invar (edge_sel s)"
  "ns_invar_impl s \<Longrightarrow> arborescense_invar (spanning_tree s)"
  by (simp_all add: ns_invar_impl_def)

text \<open>\<^bold>\<open>(A) b-flow.\<close>\<close>

lemma ns_invar_bflowI: "(ns_flow_of s) is b flow \<Longrightarrow> ns_invar_bflow s"
  by (simp add: ns_invar_bflow_def)

lemma ns_invar_bflowE: "ns_invar_bflow s \<Longrightarrow> ((ns_flow_of s) is b flow \<Longrightarrow> P) \<Longrightarrow> P"
  by (simp add: ns_invar_bflow_def)

lemma ns_invar_bflowD: "ns_invar_bflow s \<Longrightarrow> (ns_flow_of s) is b flow"
  by (simp add: ns_invar_bflow_def)

text \<open>\<^bold>\<open>(2) Spanning tree structure.\<close>\<close>

lemma ns_invar_partitionI:
  "spanning_tree_partition r (ns_tree_edges s)
     (ns_L_of s \<union> ns_selfloops_L) (ns_U_of s \<union> ns_selfloops_U) \<Longrightarrow> ns_invar_partition s"
  by (simp add: ns_invar_partition_def)

lemma ns_invar_partitionE:
  "ns_invar_partition s \<Longrightarrow>
     (spanning_tree_partition r (ns_tree_edges s)
        (ns_L_of s \<union> ns_selfloops_L) (ns_U_of s \<union> ns_selfloops_U) \<Longrightarrow> P) \<Longrightarrow> P"
  by (simp add: ns_invar_partition_def)

lemma ns_invar_partitionD:
  "ns_invar_partition s \<Longrightarrow> spanning_tree_partition r (ns_tree_edges s)
     (ns_L_of s \<union> ns_selfloops_L) (ns_U_of s \<union> ns_selfloops_U)"
  by (simp add: ns_invar_partition_def)

text \<open>\<^bold>\<open>(5) Flow fits the structure.\<close>\<close>

lemma ns_invar_flow_fitsI:
  "flow_fits_spanning_tree_partition (ns_tree_edges s) (ns_L_of s) (ns_U_of s) (ns_flow_of s)
     \<Longrightarrow> ns_invar_flow_fits s"
  by (simp add: ns_invar_flow_fits_def)

lemma ns_invar_flow_fitsE:
  "ns_invar_flow_fits s \<Longrightarrow>
     (flow_fits_spanning_tree_partition (ns_tree_edges s) (ns_L_of s) (ns_U_of s) (ns_flow_of s)
        \<Longrightarrow> P) \<Longrightarrow> P"
  by (simp add: ns_invar_flow_fits_def)

lemma ns_invar_flow_fitsD:
  "ns_invar_flow_fits s
     \<Longrightarrow> flow_fits_spanning_tree_partition (ns_tree_edges s) (ns_L_of s) (ns_U_of s) (ns_flow_of s)"
  by (simp add: ns_invar_flow_fits_def)

text \<open>\<^bold>\<open>(4) Potential fits the structure.\<close>\<close>

lemma ns_invar_pot_fitsI:
  "potential_fits_spanning_tree_partition r (ns_tree_edges s) (ns_pot_of s) \<Longrightarrow> ns_invar_pot_fits s"
  by (simp add: ns_invar_pot_fits_def)

lemma ns_invar_pot_fitsE:
  "ns_invar_pot_fits s \<Longrightarrow>
     (potential_fits_spanning_tree_partition r (ns_tree_edges s) (ns_pot_of s) \<Longrightarrow> P) \<Longrightarrow> P"
  by (simp add: ns_invar_pot_fits_def)

lemma ns_invar_pot_fitsD:
  "ns_invar_pot_fits s \<Longrightarrow> potential_fits_spanning_tree_partition r (ns_tree_edges s) (ns_pot_of s)"
  by (simp add: ns_invar_pot_fits_def)

text \<open>\<^bold>\<open>(3) Strict feasibility on the tree.\<close> The per-vertex destruction rule yields the @{term If}
      condition; @{term ns_invar_strict_upD} / @{term ns_invar_strict_downD} project onto the two
      orientations.\<close>

lemma ns_invar_strictI:
  assumes "\<And>v. v \<in> \<V> - {r} \<Longrightarrow>
              (if par_up s v
               then ereal (h (flow_lookup (current_flow s) (par_edge s v))) < \<u> (par_edge s v)
               else flow_lookup (current_flow s) (par_edge s v) > 0)"
  shows "ns_invar_strict s"
  using assms by (auto simp add: ns_invar_strict_def)

lemma ns_invar_strictE:
  assumes "ns_invar_strict s"
    and "(\<And>v. v \<in> \<V> - {r} \<Longrightarrow>
             (if par_up s v
              then ereal (h (flow_lookup (current_flow s) (par_edge s v))) < \<u> (par_edge s v)
              else flow_lookup (current_flow s) (par_edge s v) > 0)) \<Longrightarrow> P"
  shows P
  using assms by (auto simp add: ns_invar_strict_def)

lemma ns_invar_strictD:
  assumes "ns_invar_strict s" "v \<in> \<V> - {r}"
  shows "if par_up s v
         then ereal (h (flow_lookup (current_flow s) (par_edge s v))) < \<u> (par_edge s v)
         else flow_lookup (current_flow s) (par_edge s v) > 0"
  using assms by (auto simp add: ns_invar_strict_def)

lemma ns_invar_strict_upD:
  assumes "ns_invar_strict s" "v \<in> \<V> - {r}" "par_up s v"
  shows "ereal (h (flow_lookup (current_flow s) (par_edge s v))) < \<u> (par_edge s v)"
  using ns_invar_strictD[OF assms(1,2)] assms(3) by simp

lemma ns_invar_strict_downD:
  assumes "ns_invar_strict s" "v \<in> \<V> - {r}" "\<not> par_up s v"
  shows "flow_lookup (current_flow s) (par_edge s v) > 0"
  using ns_invar_strictD[OF assms(1,2)] assms(3) by simp

text \<open>\<^bold>\<open>(C) Edge $\leftrightarrow$ tree-edge correspondence.\<close> @{term ns_invar_tree_vertexD} gives the per-vertex
      conjunction, @{term ns_invar_tree_edgesD} the tree-set equality; the remaining destruction
      rules project the per-vertex conjunction onto its three components.\<close>

lemma ns_invar_treeI:
  assumes "\<And>v. v \<in> \<V> - {r} \<Longrightarrow>
              par_edge s v \<in> \<E>
            \<and> (if par_up s v then fst (par_edge s v) = v else snd (par_edge s v) = v)
            \<and> (\<exists>q. distinct (v # par_vx s v # q)
                   \<and> walk_betw (abstract_arborescense (spanning_tree s)) v (v # par_vx s v # q) r)"
    and "(\<lambda>e. {fst e, snd e}) ` (ns_tree_edges s) = abstract_arborescense (spanning_tree s)"
  shows "ns_invar_tree s"
  using assms by (auto simp add: ns_invar_tree_def)

lemma ns_invar_treeE:
  assumes "ns_invar_tree s"
    and "(\<lbrakk>\<And>v. v \<in> \<V> - {r} \<Longrightarrow>
              par_edge s v \<in> \<E>
            \<and> (if par_up s v then fst (par_edge s v) = v else snd (par_edge s v) = v)
            \<and> (\<exists>q. distinct (v # par_vx s v # q)
                   \<and> walk_betw (abstract_arborescense (spanning_tree s)) v (v # par_vx s v # q) r);
          (\<lambda>e. {fst e, snd e}) ` (ns_tree_edges s) = abstract_arborescense (spanning_tree s)\<rbrakk> \<Longrightarrow> P)"
  shows P
  using assms by (auto simp add: ns_invar_tree_def)

lemma ns_invar_tree_vertexD:
  assumes "ns_invar_tree s" "v \<in> \<V> - {r}"
  shows "par_edge s v \<in> \<E>
       \<and> (if par_up s v then fst (par_edge s v) = v else snd (par_edge s v) = v)
       \<and> (\<exists>q. distinct (v # par_vx s v # q)
              \<and> walk_betw (abstract_arborescense (spanning_tree s)) v (v # par_vx s v # q) r)"
  using assms by (auto simp add: ns_invar_tree_def)

lemma ns_invar_tree_edgesD:
  "ns_invar_tree s
     \<Longrightarrow> (\<lambda>e. {fst e, snd e}) ` (ns_tree_edges s) = abstract_arborescense (spanning_tree s)"
  by (simp add: ns_invar_tree_def)

lemma ns_invar_tree_edgeD:
  "\<lbrakk>ns_invar_tree s; v \<in> \<V> - {r}\<rbrakk> \<Longrightarrow> par_edge s v \<in> \<E>"
  using ns_invar_tree_vertexD by blast

lemma ns_invar_tree_dirD:
  "\<lbrakk>ns_invar_tree s; v \<in> \<V> - {r}\<rbrakk>
     \<Longrightarrow> (if par_up s v then fst (par_edge s v) = v else snd (par_edge s v) = v)"
  using ns_invar_tree_vertexD by blast

lemma ns_invar_tree_walkD:
  "\<lbrakk>ns_invar_tree s; v \<in> \<V> - {r}\<rbrakk>
     \<Longrightarrow> (\<exists>q. distinct (v # par_vx s v # q)
             \<and> walk_betw (abstract_arborescense (spanning_tree s)) v (v # par_vx s v # q) r)"
  using ns_invar_tree_vertexD by blast

text \<open>\<^bold>\<open>The overall loop invariant.\<close>\<close>

lemma ns_invarI:
  "\<lbrakk>ns_invar_impl s; ns_invar_bflow s; ns_invar_partition s; ns_invar_flow_fits s;
    ns_invar_pot_fits s; ns_invar_strict s; ns_invar_tree s; ns_invar_selfloop s\<rbrakk> \<Longrightarrow> ns_invar s"
  by (simp add: ns_invar_def)

lemma ns_invarE:
  "ns_invar s \<Longrightarrow>
     (\<lbrakk>ns_invar_impl s; ns_invar_bflow s; ns_invar_partition s; ns_invar_flow_fits s;
        ns_invar_pot_fits s; ns_invar_strict s; ns_invar_tree s; ns_invar_selfloop s\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (simp add: ns_invar_def)

lemma ns_invarD:
  "ns_invar s \<Longrightarrow> ns_invar_impl s"
  "ns_invar s \<Longrightarrow> ns_invar_bflow s"
  "ns_invar s \<Longrightarrow> ns_invar_partition s"
  "ns_invar s \<Longrightarrow> ns_invar_flow_fits s"
  "ns_invar s \<Longrightarrow> ns_invar_pot_fits s"
  "ns_invar s \<Longrightarrow> ns_invar_strict s"
  "ns_invar s \<Longrightarrow> ns_invar_tree s"
  "ns_invar s \<Longrightarrow> ns_invar_selfloop s"
  by (simp_all add: ns_invar_def)

end

end
