theory Network_Simplex_Initial_Basis_Code
  imports Mincost_Flow_Algorithms.Network_Simplex_Final
          Mincost_Flow_Algorithms.Acyclic_Flow
          Directed_Set_Graphs.CSR_Graph_Spec
          Use_Network_Simplex.Rooted_Arborescense
          Data_Structures.List_Cursor
begin

text \<open>This is the single \<^emph>\<open>code\<close> theory of the initial-basis construction: it
      collects every executable definition (the CSR builds, Pass A, the free-edge DFS builder, the
      augmented-network arrays, the arborescence swap, and the whole M-free entering-edge selector) into one
      assumption-free specification locale \<open>initial_basis_code_spec\<close>. The four downstream theories
      import it and add only assumptions and proofs.\<close>

section \<open>Efficient list-backed arrays and a vertex iterator\<close>

text \<open>The acyclic-flow procedure is stated over abstract data types: two @{locale fixed_univ_map}s (the
      flow and the three-valued vertex state) and one @{locale iterable_set} (the vertices to scan). We give
      the cheapest faithful models, meant to be read as arrays: a flow / state array is a plain list, looked
      up with @{const nth} and written with @{const list_update} --- both \<open>O(1)\<close> once the list is
      a genuine array --- and the vertex iterator is the list cursor @{typ \<open>'v list_cursor\<close>}, a
      vertex list together with a single moving cursor, so @{term current}, @{term has} and @{term move} are a
      read, a length-compare and an increment. The set-valued fields (@{term abstract}, @{term iterated},
      @{term remaining}) are ghosts used only in the proofs and vanish at code generation.\<close>

section \<open>Array-mimicking input lists for the initial basis\<close>

text \<open>The initial-basis construction is driven by a handful of parallel lists that stand in for the
      arrays a real implementation would be handed.
      \<^emph>\<open>Edges are identified by their index\<close>: the four edge lists all have the same
      length, and the ith edge has capacity @{term \<open>capacity_list ! i\<close>}, cost
      @{term \<open>cost_list ! i\<close>}, tail @{term \<open>fst_list ! i\<close>}, head
      @{term \<open>snd_list ! i\<close>} and carries flow @{term \<open>flow_list ! i\<close>} (the acyclic
      flow to be turned into the initial basis). The number of edges is @{term m}, the common length of the
      edge lists, so the edges are exactly the indices @{term \<open>{0..<m}\<close>}. Capacities are
      non-negative except that @{term \<open>- 1\<close>} encodes an infinite capacity: it is the only
      negative value a capacity may take. The vertices are described by two further lists of equal length: the
      ith vertex has \<^emph>\<open>name\<close> @{term \<open>vs_list ! i\<close>} and balance
      @{term \<open>b_list ! i\<close>}. Vertex names are naturals; we reserve @{term \<open>0::nat\<close>}
      as a non-name (there is no node @{term \<open>0\<close>}), which later lets us use it for the artificial
      root. The only structural consistency we demand here is that the endpoints mentioned by the edge lists
      are exactly the vertices: the union of the tails and heads is the vertex-name set.\<close>

section \<open>Big-M as a tagged pair, and the DFS builder state\<close>

text \<open>Design notes {\isasymsection}2: a potential / reduced-cost value is a pair of a
      \<^emph>\<open>tag\<close> --- an integer coefficient of the symbolic big constant \<open>M\<close>,
      drawn from \<open>{-2..2}\<close> and stored as a five-valued datatype --- and an ordinary real
      \<open>offset\<close>. The abstraction sends a pair \<open>(t, o)\<close> to
      \<open>of_mtag t * M + o\<close>; with \<open>M\<close> large enough
      (\<open>> 6 \<sqdot> \<Sigma>|c|\<close>, chosen in the locale) the tag is recoverable from the abstract
      value, which is what discharges the conditional \<open>pot_value_*_spec\<close> axioms.\<close>

datatype mtag = M_m2 | M_m1 | M_0 | M_p1 | M_p2

primrec of_mtag :: "mtag \<Rightarrow> int" where
  "of_mtag M_m2 = - 2" | "of_mtag M_m1 = - 1" | "of_mtag M_0 = 0"
| "of_mtag M_p1 = 1"   | "of_mtag M_p2 = 2"

text \<open>Reconstruct a tag from an integer coefficient, clamping anything off the range
      @{term \<open>{- 2..2}\<close>} (the clamped cases never arise for admissible values, but keep the
      operations total).\<close>

definition mtag_of :: "int \<Rightarrow> mtag" where
  "mtag_of i = (if i \<le> - 2 then M_m2 else if i = - 1 then M_m1 else if i = 0 then M_0
                else if i = 1 then M_p1 else M_p2)"

definition tag_add :: "mtag \<Rightarrow> mtag \<Rightarrow> mtag" where
  "tag_add a b = mtag_of (of_mtag a + of_mtag b)"

definition tag_sub :: "mtag \<Rightarrow> mtag \<Rightarrow> mtag" where
  "tag_sub a b = mtag_of (of_mtag a - of_mtag b)"
(*
definition pval_abstract :: 
"'n \<Rightarrow> mtag \<times> ('n::linordered_idom) \<Rightarrow> real" where
  "pval_abstract M p = real_of_int (of_mtag (fst p)) * M + snd p"
*)
definition pval_plus :: "mtag \<times> ('n::linordered_idom) \<Rightarrow>
 mtag \<times> ('n::linordered_idom) \<Rightarrow> mtag \<times> ('n::linordered_idom)" where
  "pval_plus a b = (tag_add (fst a) (fst b), snd a + snd b)"

definition pval_minus :: "mtag \<times> ('n::linordered_idom)
 \<Rightarrow> mtag \<times> ('n::linordered_idom) \<Rightarrow> mtag \<times> ('n::linordered_idom)" where
  "pval_minus a b = (tag_sub (fst a) (fst b), snd a - snd b)"

definition pval_zero :: "mtag \<times> ('n::linordered_idom)" where "pval_zero = (M_0, 0)"
definition pval_M    ::  "mtag \<times> ('n::linordered_idom)" where "pval_M    = (M_p1, 0)"
definition pval_negM ::  "mtag \<times> ('n::linordered_idom)" where "pval_negM = (M_m1, 0)"

subsection \<open>A dedicated potential-shift iterator over the thread\<close>

text \<open>The potential shift is realised by its \<^emph>\<open>own\<close> tail-recursive walk down the
      thread block of the pivot vertex, mirroring the imperative @{term shift_pot_imp}: at each visited node
      the potential is read, shifted by @{term g} and written back --- a single fused read/arith/write, with
      no higher-order per-node callback. The walk stops once the last successor @{const lsuc} of the start
      node has been processed (that node is the rightmost leaf of the subtree in thread order).

      To keep the \<^emph>\<open>inner\<close> loop branch-free, the @{term up} flag is tested
      \<^emph>\<open>once\<close>, up front: there are two separate loops, one that always adds
      (\<open>shift_pot_up_loop\<close>) and one that always subtracts (\<open>shift_pot_down_loop\<close>);
      \<open>shift_pot_impl\<close> picks the loop and never re-checks the flag while iterating. These are
      fresh implementations, not the generic @{const iterate_root_opposed_impl}; each is proved equivalent to
      a @{const subtree_fold} below, which is all the correctness argument needs.\<close>

partial_function (tailrec) shift_pot_up_loop ::
  "nat ndtree \<Rightarrow> nat \<Rightarrow> mtag \<times> ('n::linordered_idom) \<Rightarrow> nat \<Rightarrow> (mtag \<times> 'n) list \<Rightarrow> (mtag \<times> 'n) list"
  where
  "shift_pot_up_loop S stop g u pa =
     (let pa' = pa[u := pval_plus (pa ! u) g]
      in (if u = stop then pa' else shift_pot_up_loop S stop g (the (thrd S u)) pa'))"

partial_function (tailrec) shift_pot_down_loop ::
  "nat ndtree \<Rightarrow> nat \<Rightarrow> mtag \<times> ('n::linordered_idom) \<Rightarrow> nat \<Rightarrow> (mtag \<times> 'n) list \<Rightarrow> (mtag \<times> 'n) list"
  where
  "shift_pot_down_loop S stop g u pa =
     (let pa' = pa[u := pval_minus (pa ! u) g]
      in (if u = stop then pa' else shift_pot_down_loop S stop g (the (thrd S u)) pa'))"

definition shift_pot_impl ::
  "nat ndtree \<Rightarrow> nat \<Rightarrow> (mtag \<times> ('n::linordered_idom)) list \<Rightarrow> mtag \<times> 'n \<Rightarrow> bool \<Rightarrow> (mtag \<times> 'n) list"
  where
  "shift_pot_impl S v pa g up =
     (if up then shift_pot_up_loop   S (lsuc S v) g v pa
            else shift_pot_down_loop S (lsuc S v) g v pa)"

text \<open>Each branch-free walk agrees with a @{const subtree_fold} over the same thread block whose
      per-node step is its read/shift/write.  Proved by induction on the block prefix, unfolding both
      tail-recursions in lockstep --- exactly the shape of @{thm [source] subtree_fold_follow}.\<close>
lemma shift_pot_up_loop_subtree_fold:
  "\<lbrakk>parent_spec (thrd S); follow (thrd S) u = bl @ stp # rest; stp \<notin> set bl\<rbrakk>
   \<Longrightarrow> shift_pot_up_loop S stp g u pa
       = subtree_fold S stp u (\<lambda>x acc. acc[x := pval_plus (acc ! x) g]) pa"
proof(induction bl arbitrary: u pa)
  case Nil
  then show ?case
    using follow_hd_ps[of "thrd S" u]
    by (subst shift_pot_up_loop.simps, subst subtree_fold.simps) (simp add: Let_def)
next
  case (Cons b bs)
  then obtain w where "u \<noteq> stp" "thrd S u = Some w" "follow (thrd S) w = bs @ stp # rest"
    using follow_hd_ps[of "thrd S" u] follow_ps_simps[of "thrd S" u]
    by (cases "thrd S u") auto
  with Cons show ?case
    by (subst shift_pot_up_loop.simps, subst subtree_fold.simps) (simp add: Let_def)
qed

lemma shift_pot_down_loop_subtree_fold:
  "\<lbrakk>parent_spec (thrd S); follow (thrd S) u = bl @ stp # rest; stp \<notin> set bl\<rbrakk>
   \<Longrightarrow> shift_pot_down_loop S stp g u pa
       = subtree_fold S stp u (\<lambda>x acc. acc[x := pval_minus (acc ! x) g]) pa"
proof(induction bl arbitrary: u pa)
  case Nil
  then show ?case
    using follow_hd_ps[of "thrd S" u]
    by (subst shift_pot_down_loop.simps, subst subtree_fold.simps) (simp add: Let_def)
next
  case (Cons b bs)
  then obtain w where "u \<noteq> stp" "thrd S u = Some w" "follow (thrd S) w = bs @ stp # rest"
    using follow_hd_ps[of "thrd S" u] follow_ps_simps[of "thrd S" u]
    by (cases "thrd S u") auto
  with Cons show ?case
    by (subst shift_pot_down_loop.simps, subst subtree_fold.simps) (simp add: Let_def)
qed

text \<open>The mutable state carried by the free-edge DFS builder (design notes
      {\isasymsection}4/{\isasymsection}6.1). Every field is an array read with @{const nth} and written with
      @{const list_update}; the option-valued pointer maps @{term prnt}/@{term thrd}/@{term rvth} use
      @{term \<open>0::nat\<close>} as the null sentinel (there is no node \<open>0\<close>). The stack
      @{term ds_stk} of active vertices makes the recursion explicit, so the later array refinement has
      exactly the same (while-loop) shape. The iterators over the free outgoing and ingoing ranges of the
      vertices are the cursor functions @{term ds_oc} and @{term ds_ic} (@{locale csr_ranges}); a vertex's
      cursors are reset when it is pushed.\<close>

record 'n dfs_state =
  ds_seen :: "bool list"                   \<comment> \<open>visited flag (= in tree)\<close>
  ds_prnt :: "nat list"                    \<comment> \<open>ndtree parent vertex (0 = none)\<close>
  ds_par  :: "nat list"                    \<comment> \<open>parent edge id\<close>
  ds_dir  :: "bool list"                   \<comment> \<open>orientation: True {\isasymRightarrow} edge points v {\isasymrightarrow} parent (up)\<close>
  ds_pot  :: "(mtag \<times> ('n::linordered_idom)) list"                   \<comment> \<open>potential\<close>
  ds_thrd :: "nat list"                    \<comment> \<open>thread successor (0 = none)\<close>
  ds_rvth :: "nat list"                    \<comment> \<open>thread predecessor (0 = none)\<close>
  ds_lsuc :: "nat list"                    \<comment> \<open>last successor (rightmost descendant in thread)\<close>
  ds_snum :: "nat list"                    \<comment> \<open>subtree size\<close>
  ds_prev :: "nat"                         \<comment> \<open>last vertex emitted in preorder\<close>
  ds_stk  :: "nat list"                    \<comment> \<open>DFS stack of active vertices\<close>
  ds_oc   :: "nat \<Rightarrow> nat"                 \<comment> \<open>cursors into the free outgoing ranges\<close>
  ds_ic   :: "nat \<Rightarrow> nat"                 \<comment> \<open>cursors into the free ingoing ranges\<close>
  ds_afst :: "nat list"                    \<comment> \<open>artificial-edge tails (fst / snd / capacity / flow / tag),
                                                each pre-sized to the \<open>K \<le> length vs_list\<close> bound and
                                                filled at cursor @{term ds_nxt} --- an array push, no growth\<close>
  ds_asnd :: "nat list"
  ds_acap :: "'n list"
  ds_aflw :: "'n list"
  ds_aest :: "edge_tag list"
  ds_nxt  :: "nat"                         \<comment> \<open>next artificial-edge offset; its id is \<open>m + ds_nxt\<close>\<close>

subsection \<open>The selector record and the assumed tuning parameters\<close>

text \<open>The candidate shortlist is modelled as a
      \<^emph>\<open>fixed-capacity array with a length pointer\<close>, to mirror the eventual imperative
      store exactly: @{term sel_arr} is a backing list of constant length (the capacity
      @{term max_candidates}), @{term sel_len} is the live-prefix pointer, and the meaningful candidates are
      the first @{term sel_len} entries of @{term sel_arr} --- the array
      \<^emph>\<open>up to the pointer\<close>. Everything past the pointer is stale. Insertion writes at the
      pointer and bumps it; deletion is swap-with-last; both are @{const list_update} plus pointer arithmetic,
      so the backing list never changes length and no array is ever allocated after initialisation.\<close>

record ns_sel =
  sel_cur :: nat             \<comment> \<open>block-search bookmark into the augmented arc set\<close>
  sel_arr :: "nat list"      \<comment> \<open>fixed-capacity backing array of candidate edge ids\<close>
  sel_len :: nat             \<comment> \<open>live-prefix pointer: candidates are the first @{term sel_len} of @{term sel_arr}\<close>

subsection \<open>M-free sign and violation tests on descriptors\<close>

text \<open>The executable path must never evaluate the symbolic constant @{term bigM}: doing so would
      reintroduce exactly the floating-point cancellation the tagged-pair descriptor exists to avoid. These
      three tests work purely on the descriptor --- the integer big-M coefficient
      @{term \<open>of_mtag (fst p)\<close>} and the ordinary part @{term \<open>snd p\<close>} --- and
      mention no @{term M} at all. \<open>pval_neg\<close> / \<open>pval_pos\<close> give the sign, and
      \<open>viol_gt\<close> compares violation magnitude (bigger coefficient first, then bigger ordinary
      part). Their agreement with the abstraction @{term \<open>pval_abstract bigM\<close>} is a
      \<^emph>\<open>proof-time\<close> fact (see @{text pval_neg_abstract} / @{text pval_pos_abstract}),
      needing only the reduced-cost bound; that is the sole place the actual size of @{term bigM} ever
      matters.\<close>

definition pval_neg :: "mtag \<times> ('n::linordered_idom) \<Rightarrow> bool" where
  "pval_neg p \<longleftrightarrow> of_mtag (fst p) < 0 \<or> (of_mtag (fst p) = 0 \<and> snd p < 0)"

definition pval_pos :: "mtag \<times> ('n::linordered_idom) \<Rightarrow> bool" where
  "pval_pos p \<longleftrightarrow> 0 < of_mtag (fst p) \<or> (of_mtag (fst p) = 0 \<and> 0 < snd p)"

definition viol_gt :: "mtag \<times> ('n::linordered_idom)
 \<Rightarrow> mtag \<times> ('n::linordered_idom) \<Rightarrow> bool" where
  "viol_gt g1 g2 \<longleftrightarrow>
     \<bar>of_mtag (fst g1)\<bar> > \<bar>of_mtag (fst g2)\<bar>
     \<or> (\<bar>of_mtag (fst g1)\<bar> = \<bar>of_mtag (fst g2)\<bar> \<and> \<bar>snd g1\<bar> > \<bar>snd g2\<bar>)"

text \<open>The running best is carried \<^emph>\<open>without an option\<close> through the loops, as a flat
      tuple: a \<^emph>\<open>found\<close> flag followed by the edge, its @{term in_U} flag, and its reduced-cost
      descriptor. This is what lets \<open>scan_cache\<close> / \<open>scan\<close> thread the accumulator as
      four plain loop variables --- no @{term Some} is allocated per update --- the option surviving only at
      the once-per-pivot boundary of the selector, as the ADT demands. The sentinel \<open>no_best\<close>
      (\<^emph>\<open>found\<close> = @{term False}) starts each scan; its edge fields are dummies never read
      while the flag is unset.\<close>

type_synonym 'n best_cand = "bool \<times> nat \<times> bool \<times> mtag \<times> 'n"

definition no_best :: "('n::linordered_idom) best_cand" where
  "no_best = (False, 0, False, pval_zero)"

text \<open>The three possible verdicts of the whole min-cost-flow solve.
      \<^item> @{term \<open>Optimum f\<close>} --- a minimum-cost @{term b}-flow on the \<^emph>\<open>original\<close> edges, extracted
        from the augmented optimum after every artificial edge has been driven to zero.
      \<^item> @{term Infeasible} --- the augmented network is optimal but still routes flow on an
        artificial edge, witnessing that no @{term b}-flow of the original network exists.
      \<^item> @{term Neg_inf_cycle} --- a negative infinite-capacity cycle was found (by the acyclifier
        or by the loop), so the instance is unbounded (or, with the artificial edges, infeasible);
        in either case the original problem is malformed.\<close>

datatype 'n ns_outcome =
    Optimum "'n list"
  | Infeasible
  | Neg_inf_cycle


locale initial_basis_code_spec =
  fixes capacity_list :: "('n::linordered_idom) list"
    and cost_list     :: "'n list"
    and fst_list      :: "nat list"
    and snd_list      :: "nat list"
    and flow_list     :: "'n list"
    and m             :: "nat"
    and n             :: "nat"
    and b_list        :: "'n list"
   (* and h             :: "'n \<Rightarrow> real"*)
    and block_size     :: nat
    and min_candidates :: nat
    and max_candidates :: nat
begin

text \<open>The vertices are the dense range @{term \<open>{Suc 0..n}\<close>}: every name between
      @{term \<open>1::nat\<close>} and @{term n} is a vertex, @{term \<open>0::nat\<close>} is reserved as
      the null sentinel, and @{term \<open>Suc n\<close>} (\<open>vcount\<close>) is the artificial root added
      by the initial basis. @{term vs_list} is no longer an input; it is this range, materialised once.
      Vertices that carry no edge are allowed (their balance is assumed @{term 0} in the proof locale); the
      lonely-vertex guard keeps them out of the spanning tree.\<close>

definition vs_list :: "nat list" where "vs_list = [Suc 0..<Suc n]"

lemma set_vs_list: "set vs_list = {Suc 0..n}"
  by (simp only: vs_list_def set_upt atLeastLessThanSuc_atLeastAtMost)
lemma length_vs_list: "length vs_list = n" by (simp add: vs_list_def)
lemma distinct_vs_list_code: "distinct vs_list" by (simp add: vs_list_def)
lemma zero_notin_vs_list: "0 \<notin> set vs_list" by (simp add: vs_list_def)

text \<open>The lists are read as a cost-flow specification (assumption-free): the same instantiation as the
      network reading in the proof locale, but only the executable structure is fixed and no multigraph axiom
      is discharged, so the vertex set and the edge data become available for the definitions below.\<close>


text \<open>@{term vcount} is one past the largest vertex name --- the common length of every vertex-indexed
      array. The vertex-max is a \<^emph>\<open>left\<close> fold: \<open>fold\<close> is tail-recursive,
      where the \<open>foldr\<close> it replaces would build a call chain as deep as @{term vs_list}. The two
      agree because @{term max} is left-commutative, so \<open>vcount_foldr\<close> below still presents the
      \<open>foldr\<close> view to the proofs. The max is computed in this one place and reused by the balance
      array \<open>b_arr\<close> and the CSR builds.\<close>

definition vcount :: nat where
  "vcount = Suc (fold max vs_list 0)"

lemma vcount_eq: "vcount = Suc n"
  unfolding vcount_def vs_list_def by (induction n) simp_all

lemma vcount_foldr: "vcount = Suc (foldr max vs_list 0)"
  unfolding vcount_def by (simp add: foldr_fold fun_eq_iff max.left_commute)

text \<open>A list used as an array to fetch a balance by the \<^emph>\<open>name\<close> of a vertex. We
      start from an all-zero array of length \<open>Suc vcount\<close> and scatter each pair
      @{term \<open>(vs_list ! i, b_list ! i)\<close>} into it. Position @{term v} then holds the balance of
      the vertex named @{term v} (slot @{term \<open>0::nat\<close>} stays a dummy, as there is no node
      @{term \<open>0\<close>}).

      The array is one longer than the vertex names it stores. The extra slot is the artificial root
      @{term vcount}, which the augmented network of the initial basis adds and which the scatter never
      touches, since every name in @{term vs_list} is smaller than @{term vcount}. So its balance reads back
      as @{term \<open>0::real\<close>}, which is the value the root must have: the balances sum to zero
      (\<open>balance_sum_zero\<close>), hence so do the imbalances, and the artificial edges carry as much
      flow into the root as out of it. With the shorter array the read would run off the end and the root's
      balance would be unspecified, leaving the augmented \<open>b\<close>-flow obligation unprovable.\<close>

definition b_arr :: "'n list" where
  "b_arr = foldl (\<lambda> arr (v, x). arr[v := x])
                 (replicate (Suc vcount) 0)
                 (zip vs_list b_list)"

definition b_lookup :: "nat \<Rightarrow> 'n" where
  "b_lookup v = b_arr ! v"

subsection \<open>The graph as two CSRs and the acyclic-flow procedure\<close>

text \<open>Both adjacency structures are the CSR of the edge list built by the counting sort
      @{locale csr_buildup}, with the edges @{term \<open>[0..<length fst_list]\<close>} as elements: the
      outgoing one keys each edge on its tail (@{term \<open>e_src fst_list\<close>}), the ingoing one on its
      head (@{term \<open>e_tgt fst_list snd_list\<close>}). The blocks are indexed by vertex
      \<^emph>\<open>name\<close>, so the array of block starts \<open>B\<close> has
      @{term \<open>Suc vcount\<close>} entries, one past the largest name (exactly as @{const b_arr}); names
      that are not vertices index empty blocks. The acyclic-flow instance uses the two CSRs as its edge
      iterators (@{locale csr_graph}, the iterator state being the cursor function), and the initial-basis
      construction reuses their block starts and overwrites their edge arrays in place with the free edges
      ({\isasymsection}4, no rebuild, no new allocation).\<close>

section \<open>Initial-basis construction: the strongly-feasible spanning tree\<close>

subsection \<open>Pass A: one fused sweep --- status, excess, and the free-edge CSRs\<close>

text \<open>Realising the notes' single pass: one fold over the edges records, per edge, its status
      (\<open>edge_state\<close>), accumulates the excess (\<open>excess\<close>), and --- for a
      \<^emph>\<open>free\<close> (tree) edge --- appends it to the range of its tail in the outgoing CSR and
      to the range of its head in the ingoing CSR (@{const csr_append}), in place. Each range starts empty at
      the start of its block (\<open>out_lo\<close> / \<open>in_lo\<close>), so each vertex's free edges
      occupy the front of its block (@{locale csr_ranges}). No list is materialised beyond the ones the notes
      name.\<close>

definition out_lo :: "nat list" where
  "out_lo = butlast (csr_buildup.B_spec (edge_seq fst_list) (e_src fst_list) vcount 0)"

definition in_lo :: "nat list" where
  "in_lo = butlast (csr_buildup.B_spec (edge_seq fst_list) (e_tgt fst_list snd_list) vcount 0)"

text \<open>A vertex whose blocks are empty in \<^emph>\<open>both\<close> CSRs
      (@{const csr_blocks.csr_empty}) is an endpoint of no edge --- a \<^emph>\<open>lonely\<close> vertex.
      The test is two O(1) reads per CSR, so it introduces no extra sweep.\<close>

definition is_lonely :: "nat \<Rightarrow> bool" where
  "is_lonely v \<longleftrightarrow>
     csr_blocks.csr_empty (csr_buildup.B_spec (edge_seq fst_list) (e_src fst_list) vcount 0) v \<and>
     csr_blocks.csr_empty (csr_buildup.B_spec (edge_seq fst_list) (e_tgt fst_list snd_list) vcount 0) v"

text \<open>The edged vertices: the dense range with the edge-less (lonely) names removed.  This is the
      vertex set actually fed to the acyclifier, so its abstraction stays exactly the graph vertex
      set @{term \<open>set fst_list \<union> set snd_list\<close>}, and the lonely names --- whose balance the proof
      locale assumes @{term 0} --- are skipped there just as the lonely guard skips them in the
      spanning tree.\<close>

definition edged_vs_list :: "nat list" where
  "edged_vs_list = filter (\<lambda>v. \<not> is_lonely v) vs_list"

text \<open>The fused step for edge @{term e}. The state is the status list, the excess, and the outgoing
      and ingoing free ranges, each a pair of the range ends and the edge array. A self-loop cancels
      in the excess (the head update is read back by the tail update).\<close>

definition passA_step ::
  "'n list \<Rightarrow> nat \<Rightarrow> edge_tag list \<times> 'n list \<times> (nat list \<times> nat list) \<times> (nat list \<times> nat list)
       \<Rightarrow> edge_tag list \<times> 'n list \<times> (nat list \<times> nat list) \<times> (nat list \<times> nat list)" where
  "passA_step fl e = (\<lambda>(est, exc, fo, fi).
     let x = fst_list ! e; y = snd_list ! e; f = fl ! e; u = capacity_list ! e;
         st = (if f = 0 then InL else if u \<noteq> - 1 \<and> f = u then InU else InTree);
         exc' = (let a = exc[y := exc ! y + f] in a[x := a ! x - f])
     in if st = InTree
        then (est[e := st], exc', csr_append x e fo, csr_append y e fi)
        else (est[e := st], exc', fo, fi))"

definition passA ::
  "'n list \<Rightarrow> edge_tag list \<times> 'n list \<times> (nat list \<times> nat list) \<times> (nat list \<times> nat list)" where
  "passA fl = fold (passA_step fl) [0..<m]
     (replicate m InL, replicate (Suc vcount) (0::'n),
      (out_lo, csr_buildup.E_spec (edge_seq fst_list) (e_src fst_list) vcount 0),
      (in_lo, csr_buildup.E_spec (edge_seq fst_list) (e_tgt fst_list snd_list) vcount 0))"

definition edge_state :: "'n list \<Rightarrow> edge_tag list" where
  "edge_state fl = (let (est, _, _, _) = passA fl in est)"

definition excess :: "'n list" where
  "excess = (let (_, exc, _, _) = passA flow_list in exc)"

definition free_out :: "'n list \<Rightarrow> nat list \<times> nat list" where
  "free_out fl = (let (_, _, fo, _) = passA fl in fo)"

definition free_in :: "'n list \<Rightarrow> nat list \<times> nat list" where
  "free_in fl = (let (_, _, _, fi) = passA fl in fi)"

subsection \<open>Derived views: status and imbalance\<close>

text \<open>Vertex v's free outgoing edges are its range in @{term \<open>free_out fl\<close>}, its free ingoing edges
      its range in @{term \<open>free_in fl\<close>} (@{locale csr_ranges}, with the block starts of the full CSRs).
      The DFS iterates over these ranges, so no per-vertex edge list is materialised.\<close>

text \<open>The imbalance @{term \<open>imbalance ! v\<close>} = achieved - target balance = the signed amount
      @{term v}'s artificial edge must ship toward the root (surplus positive); the root carries none. It is
      the @{const excess} array transformed \<^emph>\<open>in place\<close> (@{const excess} is spent here)
      --- no new array.\<close>

definition imbalance :: "'n list" where
  "imbalance = fold (\<lambda>v arr. arr[v := arr ! v + b_lookup v]) [0..<vcount] excess"

subsection \<open>Artificial-edge orientation and the augmented endpoints\<close>

text \<open>Each vertex @{term v} owns at most one artificial edge. It is oriented
      \<open>v \<rightarrow> root\<close> (up) iff @{term v} is a surplus/balanced vertex, else
      \<open>root \<rightarrow> v\<close> (down); it carries @{term \<open>\<bar>imbalance ! v\<bar>\<close>}.
      A \<^emph>\<open>tree\<close> artificial edge gets a slack \<open>+ 1\<close> toward the root when it
      points up (strong feasibility); a down one is saturated but legal (\<open>f > 0\<close>). The three
      functions below are the \<^emph>\<open>build-time formulas\<close>: Phases 1 and 2 evaluate them once
      per artificial edge to fill the artificial tail of the unified augmented edge arrays (design notes
      {\isasymsection}1/{\isasymsection}5).\<close>

definition art_dir :: "nat \<Rightarrow> bool" where
  "art_dir v \<longleftrightarrow> 0 \<le> imbalance ! v"

definition art_flow :: "nat \<Rightarrow> 'n" where
  "art_flow v = \<bar>imbalance ! v\<bar>"

definition art_tree_cap :: "nat \<Rightarrow> 'n" where
  "art_tree_cap v = (if art_dir v then art_flow v + 1 else art_flow v)"

text \<open>The augmented network's endpoints, capacity and flow are \<^emph>\<open>single\<close>
      length-\<open>m + K\<close> arrays --- the real part followed by the artificial tail the phases append
      --- so the simplex loop reads \<open>fst_all ! e\<close>, \<open>cap_all ! e\<close> etc.\ with no
      \<open>e < m\<close> comparison on the executable path. These arrays are defined once the phase
      construction is in place; the earlier per-edge endpoint functions \<open>fst_aug\<close> /
      \<open>snd_aug\<close> (which branched on \<open>e < m\<close>) are therefore dropped.\<close>

text \<open>Design notes {\isasymsection}4/{\isasymsection}6.1. A single depth-first traversal of the
      free-edge CSRs (built by Pass A) grows the rooted arborescence toward @{term vcount}. The traversal is a
      genuine recursive function stepping an explicit stack of vertices --- the same shape the later array
      refinement will have --- iterating over the free outgoing and then the free ingoing range of the top
      vertex with the iterators @{term ds_oc} / @{term ds_ic} of @{locale csr_ranges}.\<close>

text \<open>The initial builder state: nothing visited, the root @{term vcount} seeded (its subtree size
      starts at \<open>1\<close> and the thread predecessor of the first emitted vertex will be the root). The
      cursors are arbitrary; each vertex's cursors are reset when it is pushed.\<close>

definition dfs_init :: "'n dfs_state" where
  "dfs_init =
     \<lparr> ds_seen = replicate (Suc vcount) False,
       ds_prnt = replicate (Suc vcount) 0,
       ds_par  = replicate (Suc vcount) 0,
       ds_dir  = replicate (Suc vcount) False,
       ds_pot  = replicate (Suc vcount) pval_zero,
       ds_thrd = replicate (Suc vcount) 0,
       ds_rvth = replicate (Suc vcount) 0,
       ds_lsuc = replicate (Suc vcount) 0,
       ds_snum = (replicate (Suc vcount) 0)[vcount := 1],
       ds_prev = vcount,
       ds_stk  = [],
       ds_oc   = (\<lambda>_. 0),
       ds_ic   = (\<lambda>_. 0),
       ds_afst = replicate (length vs_list) 0, ds_asnd = replicate (length vs_list) 0,
       ds_acap = replicate (length vs_list) 0, ds_aflw = replicate (length vs_list) 0,
       ds_aest = replicate (length vs_list) InL,
       ds_nxt  = 0 \<rparr>"

text \<open>Pushing vertex @{term w}: reset both its iterators and put it on the stack.\<close>

definition dfs_push :: "'n dfs_state \<Rightarrow> nat \<Rightarrow> 'n dfs_state" where
  "dfs_push s w =
     s\<lparr> ds_stk := w # ds_stk s,
        ds_oc := csr_blocks.csr_reset (csr_buildup.B_spec (edge_seq fst_list) (e_src fst_list) vcount 0)
                   (ds_oc s) w,
        ds_ic := csr_blocks.csr_reset (csr_buildup.B_spec (edge_seq fst_list) (e_tgt fst_list snd_list) vcount 0)
                   (ds_ic s) w \<rparr>"

text \<open>Discovering a fresh vertex @{term w} from stack-top @{term v} across the free real edge
      @{term e}: finalise @{term w}'s tree fields, link it into the thread after the last emitted
      vertex @{term \<open>ds_prev s\<close>}, seed its potential to give @{term e} zero reduced cost
      (\<open>\<plusminus> cost_list ! e\<close> by whether @{term v} is @{term e}'s tail), and push @{term w}.
      The orientation flag is \<open>True\<close> iff @{term e} points \<open>w \<rightarrow> v\<close> (up toward the
      parent).\<close>

definition dfs_discover :: "'n dfs_state \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'n dfs_state" where
  "dfs_discover s v w e =
     (let sgn = (if v = fst_list ! e then (cost_list ! e) else - (cost_list ! e));
          pw  = pval_plus (ds_pot s ! v) (M_0, sgn);
          pv  = ds_prev s
      in dfs_push
           (s\<lparr> ds_seen := (ds_seen s)[w := True],
               ds_prnt := (ds_prnt s)[w := v],
               ds_par  := (ds_par s)[w := e],
               ds_dir  := (ds_dir s)[w := (fst_list ! e = w)],
               ds_pot  := (ds_pot s)[w := pw],
               ds_thrd := (ds_thrd s)[pv := w],
               ds_rvth := (ds_rvth s)[w := pv],
               ds_snum := (ds_snum s)[w := 1],
               ds_prev := w \<rparr>) w)"

text \<open>Finishing (post-order) stack-top @{term v}: the last vertex emitted so far is the rightmost
      descendant of @{term v}'s subtree, so it is @{term v}'s \<open>lsuc\<close>; add @{term v}'s completed
      subtree size to its parent's running count and pop @{term v}.\<close>

definition dfs_finish :: "'n dfs_state \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> 'n dfs_state" where
  "dfs_finish s v rest =
     (let p = ds_prnt s ! v
      in s\<lparr> ds_lsuc := (ds_lsuc s)[v := ds_prev s],
            ds_snum := (ds_snum s)[p := ds_snum s ! p + ds_snum s ! v],
            ds_stk  := rest \<rparr>)"

text \<open>The traversal itself: at the stack top iterate over the free outgoing range, then the free
      ingoing range, recursing into each unseen neighbour; when both are exhausted, finish the
      vertex. Termination (each real recursion either marks a fresh vertex or advances an iterator)
      is deferred to a separate measure lemma, as for \<open>AF_DFS\<close>.\<close>

text \<open>The recursion takes the two free ranges of Pass A --- @{term fo} / @{term fi}, each the pair of
      range ends and edge array --- rather than the flow. This is what keeps the traversal linear:
      @{const free_out} / @{const free_in} re-run the \<^emph>\<open>whole\<close> of @{const passA}, a fold
      over all @{term m} edges, so a flow-indexed recursion would redo Pass A at every single DFS step. Taking
      the ranges as arguments --- they are fixed for the entire traversal --- runs @{const passA} once, in
      \<open>build_dfs\<close> just below, and shares it across the whole descent.\<close>

function (domintros) build_dfs_a ::
  "nat list \<times> nat list \<Rightarrow> nat list \<times> nat list \<Rightarrow> 'n dfs_state \<Rightarrow> 'n dfs_state" where
  "build_dfs_a fo fi s =
     (case ds_stk s of
        [] \<Rightarrow> s
      | v # rest \<Rightarrow>
         if csr_blocks.csr_has ((!) (fst fo)) (ds_oc s) v then
           (let e = csr_blocks.csr_current (snd fo) (ds_oc s) v; w = snd_list ! e;
                s1 = s\<lparr> ds_oc := csr_blocks.csr_move ((!) (fst fo)) (ds_oc s) v \<rparr>
            in build_dfs_a fo fi (if ds_seen s ! w then s1 else dfs_discover s1 v w e))
         else if csr_blocks.csr_has ((!) (fst fi)) (ds_ic s) v then
           (let e = csr_blocks.csr_current (snd fi) (ds_ic s) v; w = fst_list ! e;
                s1 = s\<lparr> ds_ic := csr_blocks.csr_move ((!) (fst fi)) (ds_ic s) v \<rparr>
            in build_dfs_a fo fi (if ds_seen s ! w then s1 else dfs_discover s1 v w e))
         else
           build_dfs_a fo fi (dfs_finish s v rest))"
  by pat_completeness auto

text \<open>The flow-indexed traversal: \<^emph>\<open>one\<close> @{const passA}, its two free ranges handed to the
      recursion. The domain predicate and the unfolding rule of the flow-indexed recursion are
      recovered by \<open>build_dfs_dom\<close> and \<open>build_dfs_psimps\<close>.\<close>

definition build_dfs :: "'n list \<Rightarrow> 'n dfs_state \<Rightarrow> 'n dfs_state" where
  "build_dfs fl s = (let (_, _, fo, fi) = passA fl in build_dfs_a fo fi s)"

definition build_dfs_dom :: "'n list \<times> 'n dfs_state \<Rightarrow> bool" where
  "build_dfs_dom p \<longleftrightarrow> build_dfs_a_dom (free_out (fst p), free_in (fst p), snd p)"

lemma build_dfs_unfold: "build_dfs fl s = build_dfs_a (free_out fl) (free_in fl) s"
  by (simp add: build_dfs_def free_out_def free_in_def split: prod.splits)

lemma build_dfs_dom_iff:
  "build_dfs_dom (fl, s) \<longleftrightarrow> build_dfs_a_dom (free_out fl, free_in fl, s)"
  by (simp add: build_dfs_dom_def)

text \<open>The flow-indexed unfolding rule, recovered from the range-indexed recursion.\<close>

lemma build_dfs_psimps:
  "build_dfs_dom (fl, s) \<Longrightarrow> build_dfs fl s =
    (case ds_stk s of
       [] \<Rightarrow> s
     | v # rest \<Rightarrow>
        if csr_blocks.csr_has ((!) (fst (free_out fl))) (ds_oc s) v then
          (let e = csr_blocks.csr_current (snd (free_out fl)) (ds_oc s) v; w = snd_list ! e;
               s1 = s\<lparr> ds_oc := csr_blocks.csr_move ((!) (fst (free_out fl))) (ds_oc s) v \<rparr>
           in build_dfs fl (if ds_seen s ! w then s1 else dfs_discover s1 v w e))
        else if csr_blocks.csr_has ((!) (fst (free_in fl))) (ds_ic s) v then
          (let e = csr_blocks.csr_current (snd (free_in fl)) (ds_ic s) v; w = fst_list ! e;
               s1 = s\<lparr> ds_ic := csr_blocks.csr_move ((!) (fst (free_in fl))) (ds_ic s) v \<rparr>
           in build_dfs fl (if ds_seen s ! w then s1 else dfs_discover s1 v w e))
        else
          build_dfs fl (dfs_finish s v rest))"
  unfolding build_dfs_unfold build_dfs_dom_iff by (rule build_dfs_a.psimps)

text \<open>Opening a tree component at an unseen vertex @{term c}: emit @{term c}'s
      \<^emph>\<open>tree\<close> artificial edge (write its endpoints / capacity / flow into the pre-sized
      artificial tails at cursor @{term \<open>ds_nxt s\<close>}, tag @{const InTree}), finalise @{term c} as
      a child of the root @{term vcount}, seed its potential to \<open>\<plusminus> M\<close> (a down edge
      \<open>r \<rightarrow> c\<close> gives \<open>+ M\<close>, an up edge \<open>- M\<close>), thread-link
      it, push it on the empty stack, then drain its subtree by @{const build_dfs}. Orientation / flow /
      capacity are computed inline from a \<^emph>\<open>single\<close> @{term \<open>imbalance ! c\<close>}
      read (the build-time formulas @{const art_dir} / @{const art_flow} / @{const art_tree_cap}, unfolded to
      avoid re-reading @{const imbalance}).\<close>

definition open_tree_component :: "'n list \<Rightarrow> 'n dfs_state \<Rightarrow> nat \<Rightarrow> 'n dfs_state" where
  "open_tree_component fl s c =
     (let imb = imbalance ! c; up = 0 \<le> imb; af = \<bar>imb\<bar>; cp = (if up then af + 1 else af);
          pv = ds_prev s
      in build_dfs fl
           (dfs_push
             (s\<lparr> ds_afst := (ds_afst s)[ds_nxt s := (if up then c else vcount)],
                 ds_asnd := (ds_asnd s)[ds_nxt s := (if up then vcount else c)],
                 ds_acap := (ds_acap s)[ds_nxt s := cp],
                 ds_aflw := (ds_aflw s)[ds_nxt s := af],
                 ds_aest := (ds_aest s)[ds_nxt s := InTree],
                 ds_nxt  := Suc (ds_nxt s),
                 ds_seen := (ds_seen s)[c := True],
                 ds_prnt := (ds_prnt s)[c := vcount],
                 ds_par  := (ds_par s)[c := m + ds_nxt s],
                 ds_dir  := (ds_dir s)[c := up],
                 ds_pot  := (ds_pot s)[c := (if up then pval_negM else pval_M)],
                 ds_thrd := (ds_thrd s)[pv := c],
                 ds_rvth := (ds_rvth s)[c := pv],
                 ds_snum := (ds_snum s)[c := 1],
                 ds_prev := c,
                 ds_stk  := [] \<rparr>) c))"

text \<open>Emitting a \<^emph>\<open>saturated\<close> @{term U} artificial edge for an already-seen
      imbalanced vertex @{term v} (design notes {\isasymsection}4, last table row): it carries
      @{term \<open>art_flow v\<close>} at its bound (capacity = flow), so it is tagged @{const InU} and
      touches no tree field.\<close>

definition emit_U_edge :: "'n dfs_state \<Rightarrow> nat \<Rightarrow> 'n dfs_state" where
  "emit_U_edge s v =
     (let imb = imbalance ! v; up = 0 \<le> imb; fl = \<bar>imb\<bar>
      in s\<lparr> ds_afst := (ds_afst s)[ds_nxt s := (if up then v else vcount)],
            ds_asnd := (ds_asnd s)[ds_nxt s := (if up then vcount else v)],
            ds_acap := (ds_acap s)[ds_nxt s := fl],
            ds_aflw := (ds_aflw s)[ds_nxt s := fl],
            ds_aest := (ds_aest s)[ds_nxt s := InU],
            ds_nxt  := Suc (ds_nxt s) \<rparr>)"

text \<open>Phase 1 --- one scan of the vertices, imbalanced first: an imbalanced unseen vertex opens its
      tree component; an imbalanced already-seen vertex emits a saturated @{term U} edge; balanced
      vertices are skipped.\<close>

definition phase1_step :: "'n list \<Rightarrow> nat \<Rightarrow> 'n dfs_state \<Rightarrow> 'n dfs_state" where
  "phase1_step fl v s =
     (if imbalance ! v = 0 then s
      else if \<not> ds_seen s ! v then open_tree_component fl s v
      else emit_U_edge s v)"

definition phase1 :: "'n list \<Rightarrow> 'n dfs_state \<Rightarrow> 'n dfs_state" where
  "phase1 fl s = fold (phase1_step fl) vs_list s"

text \<open>Phase 2 --- a second vertex scan opening every still-unseen (necessarily balanced) vertex as a
      flow-0 tree component. Afterwards every vertex is seen, so the thread and parent map span the
      augmented vertex set, rooted at @{term vcount}.\<close>

definition phase2_step :: "'n list \<Rightarrow> nat \<Rightarrow> 'n dfs_state \<Rightarrow> 'n dfs_state" where
  "phase2_step fl v s = (if ds_seen s ! v \<or> is_lonely v then s else open_tree_component fl s v)"

definition phase2 :: "'n list \<Rightarrow> 'n dfs_state \<Rightarrow> 'n dfs_state" where
  "phase2 fl s = fold (phase2_step fl) vs_list s"

text \<open>The finished builder: run both phases, then the one \<^emph>\<open>root finalisation\<close> the
      traversal cannot do per-frame --- the root @{term vcount} is never pushed, so it is never popped and its
      @{term ds_lsuc} slot is never written. Its last successor (rightmost descendant of the whole tree) is
      the last vertex emitted, i.e.\ the final @{term ds_prev}. This is the ndtree clause
      @{term \<open>lsuc S r = last P\<close>} (I7 at @{term r}); every non-root
      \<open>lsuc\<close>/\<open>snum\<close> was already produced at its pop inside @{const build_dfs}, with
      no extra pass.\<close>

definition build_tree :: "'n list \<Rightarrow> 'n dfs_state" where
  "build_tree fl = (let s = phase2 fl (phase1 fl dfs_init) in s\<lparr> ds_lsuc := (ds_lsuc s)[vcount := ds_prev s] \<rparr>)"


text \<open>The acyclic-flow procedure is available here as an assumption-free specification instance: the two
      counting-sort CSRs are its edge iterators, the flow and vertex-state arrays are lists, and fst-exec /
      snd-exec are the constant-time endpoint reads. Interpreting the acyclic-flow specification locale
      exports the executable acyclifier into this specification locale, so the acyclifier can be executed
      without discharging any ADT law.\<close>

sublocale acyclic_flow_impl_spec
  where out_current = "csr_blocks.csr_current (csr_buildup.E_spec (edge_seq fst_list) (e_src fst_list) vcount 0)"
    and out_has = "csr_blocks.csr_has (\<lambda>v. csr_buildup.B_spec (edge_seq fst_list) (e_src fst_list) vcount 0 ! Suc v)"
    and out_move = "csr_blocks.csr_move (\<lambda>v. csr_buildup.B_spec (edge_seq fst_list) (e_src fst_list) vcount 0 ! Suc v)"
    and out_reset = "csr_blocks.csr_reset (csr_buildup.B_spec (edge_seq fst_list) (e_src fst_list) vcount 0)"
    and in_current = "csr_blocks.csr_current (csr_buildup.E_spec (edge_seq fst_list) (e_tgt fst_list snd_list) vcount 0)"
    and in_has = "csr_blocks.csr_has (\<lambda>v. csr_buildup.B_spec (edge_seq fst_list) (e_tgt fst_list snd_list) vcount 0 ! Suc v)"
    and in_move = "csr_blocks.csr_move (\<lambda>v. csr_buildup.B_spec (edge_seq fst_list) (e_tgt fst_list snd_list) vcount 0 ! Suc v)"
    and in_reset = "csr_blocks.csr_reset (csr_buildup.B_spec (edge_seq fst_list) (e_tgt fst_list snd_list) vcount 0)"
    and flow_upd = list_update and flow_lookup = nth
    and st_upd = list_update and st_lookup = nth
    and current_vertex = lc_current and has_vertex = lc_has
    and move_on_vertex = lc_move
    and out_arr = "(!) (csr_buildup.B_spec (edge_seq fst_list) (e_src fst_list) vcount 0)"
    and in_arr = "(!) (csr_buildup.B_spec (edge_seq fst_list) (e_tgt fst_list snd_list) vcount 0)"
    and all_vertices = "\<lparr> lc_list = edged_vs_list, lc_pos = 0 \<rparr>"
    and cap = "\<lambda> e.  capacity_list ! e "
    and cost = "\<lambda> e. cost_list ! e"
    and state_init = "replicate vcount Unseen"
    and fst_exec = "\<lambda> e. fst_list ! e"
    and snd_exec = "\<lambda> e. snd_list ! e"
  by unfold_locales


subsection \<open>The acyclified flow the tree is built from\<close>

text \<open>The candidate @{term flow_list} is only capacity-complying; the strongly-feasible tree is built
      from its \<^emph>\<open>acyclified\<close> form. @{const make_acyclic} either returns @{term None} --- a
      negative infinite-capacity free cycle, i.e.\ the instance is unbounded/infeasible and no tree is built
      --- or @{term \<open>Some f'\<close>} with @{term \<open>f'\<close>} acyclic, capacity-complying and of
      the same excesses. @{term acyc_flow} is that output, defaulting to @{term flow_list} on the (guarded)
      @{term None} branch so every downstream array stays total; the orchestrator \<open>solve\<close> below
      never uses it on that branch.\<close>

definition acyc_flow_opt :: "'n list option" where
  "acyc_flow_opt = make_acyclic flow_list"

definition acyc_flow :: "'n list" where
  "acyc_flow = (case acyc_flow_opt of Some f' \<Rightarrow> f' | None \<Rightarrow> flow_list)"

subsection \<open>The abstract arborescence read off the builder arrays\<close>

text \<open>The spanning-tree ADT operations act on an @{typ \<open>nat ndtree\<close>};
      \<open>tree_st\<close> reads it off the \<^emph>\<open>finished builder state\<close> (parent / thread /
      reverse-thread / last-successor / subtree-size), with the option-pointer maps sending the null sentinel
      @{term \<open>0::nat\<close>} and the unseen vertices to @{term None}. @{term \<open>vseen_st s\<close>}
      are the discovered real vertices, @{term \<open>varb_st s\<close>} adds the root @{term vcount}.\<close>

text \<open>The reader is indexed by the builder \<^emph>\<open>state\<close>, not by the flow, and this is
      what makes it cheap: the five pointer maps of \<open>tree_st\<close> are closures, so had each captured
      a flow @{term fl} and called @{term \<open>build_tree fl\<close>} itself,
      \<^emph>\<open>every single pointer lookup\<close> during the simplex would re-run the whole builder.
      Taking the finished state as the argument means @{const build_tree} is run once and all five fields
      share that one result. The flow-indexed \<open>tree_of\<close> below is just the composition, used to
      state the initial tree.\<close>

definition vseen_st :: "'n dfs_state \<Rightarrow> nat set" where
  "vseen_st s = {y. y < vcount \<and> ds_seen s ! y}"

definition varb_st :: "'n dfs_state \<Rightarrow> nat set" where
  "varb_st s = insert vcount (vseen_st s)"

definition sprnt_st :: "'n dfs_state \<Rightarrow> nat \<Rightarrow> nat option" where
  "sprnt_st s v = (if v \<in> vseen_st s then Some (ds_prnt s ! v) else None)"

definition sthrd_st :: "'n dfs_state \<Rightarrow> nat \<Rightarrow> nat option" where
  "sthrd_st s v = (if v \<in> varb_st s \<and> ds_thrd s ! v \<noteq> 0 then Some (ds_thrd s ! v) else None)"

definition srvth_st :: "'n dfs_state \<Rightarrow> nat \<Rightarrow> nat option" where
  "srvth_st s v = (if v \<in> varb_st s \<and> ds_rvth s ! v \<noteq> 0 then Some (ds_rvth s ! v) else None)"

definition tree_st :: "'n dfs_state \<Rightarrow> nat ndtree" where
  "tree_st s = \<lparr> prnt = sprnt_st s, thrd = sthrd_st s, rvth = srvth_st s,
                 lsuc = (\<lambda>v. ds_lsuc s ! v), snum = (\<lambda>v. ds_snum s ! v) \<rparr>"

text \<open>The flow-indexed views: each is its state-indexed counterpart at the finished builder. The
      equations \<open>vseen_of_eq\<close> {\isasymdots} \<open>tree_of_eq\<close> below recover the original
      one-step definitions, so the correctness statements are unchanged.\<close>

definition vseen_of :: "'n list \<Rightarrow> nat set" where
  "vseen_of fl = vseen_st (build_tree fl)"

definition varb_of :: "'n list \<Rightarrow> nat set" where
  "varb_of fl = varb_st (build_tree fl)"

definition sprnt_of :: "'n list \<Rightarrow> nat \<Rightarrow> nat option" where
  "sprnt_of fl = sprnt_st (build_tree fl)"

definition sthrd_of :: "'n list \<Rightarrow> nat \<Rightarrow> nat option" where
  "sthrd_of fl = sthrd_st (build_tree fl)"

definition srvth_of :: "'n list \<Rightarrow> nat \<Rightarrow> nat option" where
  "srvth_of fl = srvth_st (build_tree fl)"

definition tree_of :: "'n list \<Rightarrow> nat ndtree" where
  "tree_of fl = tree_st (build_tree fl)"

lemma vseen_of_eq: "vseen_of fl = {y. y < vcount \<and> ds_seen (build_tree fl) ! y}"
  by (simp add: vseen_of_def vseen_st_def)

lemma varb_of_eq: "varb_of fl = insert vcount (vseen_of fl)"
  by (simp add: varb_of_def vseen_of_def varb_st_def)

lemma sprnt_of_eq:
  "sprnt_of fl v = (if v \<in> vseen_of fl then Some (ds_prnt (build_tree fl) ! v) else None)"
  by (simp add: sprnt_of_def vseen_of_def sprnt_st_def)

lemma sthrd_of_eq:
  "sthrd_of fl v = (if v \<in> varb_of fl \<and> ds_thrd (build_tree fl) ! v \<noteq> 0
                    then Some (ds_thrd (build_tree fl) ! v) else None)"
  by (simp add: sthrd_of_def varb_of_def sthrd_st_def)

lemma srvth_of_eq:
  "srvth_of fl v = (if v \<in> varb_of fl \<and> ds_rvth (build_tree fl) ! v \<noteq> 0
                    then Some (ds_rvth (build_tree fl) ! v) else None)"
  by (simp add: srvth_of_def varb_of_def srvth_st_def)

lemma tree_of_eq:
  "tree_of fl = \<lparr> prnt = sprnt_of fl, thrd = sthrd_of fl, rvth = srvth_of fl,
                  lsuc = (\<lambda>v. ds_lsuc (build_tree fl) ! v),
                  snum = (\<lambda>v. ds_snum (build_tree fl) ! v) \<rparr>"
  by (simp add: tree_of_def tree_st_def sprnt_of_def sthrd_of_def srvth_of_def)


subsection \<open>Augmented-network arrays and the arborescence swap\<close>

text \<open>Executable augmented-network arrays and the arborescence swap operation, built directly on
      build-tree of the acyclified flow; they need no correctness hypothesis, so they live in the
      assumption-free code-side locale. The augmented cost array cost-all is not here: its cost uses
      the symbolic Big-M and is therefore proof-only.\<close>

text \<open>\<open>art_tree\<close> names the \<^emph>\<open>finished builder\<close> of the acyclified flow.
      Every consumer below reads it --- the artificial-edge count \<open>Kart\<close> and the five augmented
      arrays, and further down the initial potential / parent / direction arrays and the initial tree handed
      to the interpreted simplex. Binding it \<^emph>\<open>once\<close> here means the builder runs once
      rather than once per consumer. Its unfolding is a simp rule, so every proof still sees
      @{term \<open>build_tree acyc_flow\<close>} exactly as before.\<close>

definition art_tree :: "'n dfs_state" where "art_tree = build_tree acyc_flow"

declare art_tree_def[simp]

definition Kart :: nat where "Kart = ds_nxt art_tree"
definition fst_all :: "nat list" where "fst_all = fst_list @ take Kart (ds_afst art_tree)"
definition snd_all :: "nat list" where "snd_all = snd_list @ take Kart (ds_asnd art_tree)"
definition cap_all :: "'n list" where "cap_all = capacity_list @ take Kart (ds_acap art_tree)"
definition flow_all :: "'n list" where "flow_all = acyc_flow @ take Kart (ds_aflw art_tree)"
definition state_all :: "edge_tag list" where "state_all = edge_state acyc_flow @ take Kart (ds_aest art_tree)"

definition swap_edge_impl :: "'a ndtree \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a ndtree" where
  "swap_edge_impl S x u v = update_tree S u v x (join_of (prnt S) u v)"

subsection \<open>The executable entering-edge selector\<close>

definition marc :: nat where "marc = m + Kart"

definition cost_pval :: "nat \<Rightarrow>  (mtag \<times> 'n)" where
  "cost_pval e = (if e < m then (M_0, cost_list ! e) else pval_M)"

definition red_cost :: " (mtag \<times> 'n) list \<Rightarrow> nat \<Rightarrow>  (mtag \<times> 'n)" where
  "red_cost \<pi> e =
     pval_plus (cost_pval e)
       (pval_minus (nth \<pi> (fst_all ! e))
                   (nth \<pi> (snd_all ! e)))"

definition eligible :: "edge_tag list \<Rightarrow> (mtag \<times> 'n) list \<Rightarrow> nat \<Rightarrow> bool" where
  "eligible es \<pi> e =
     (fst_all ! e \<noteq> snd_all ! e \<and>
      (case nth es e of
        InTree \<Rightarrow> False
      | InL    \<Rightarrow> pval_neg (red_cost \<pi> e)
      | InU    \<Rightarrow> pval_pos (red_cost \<pi> e)))"

definition ent_in_U :: "edge_tag list \<Rightarrow> nat \<Rightarrow> bool" where
  "ent_in_U es e = (nth es e = InU)"

definition evaluate :: "edge_tag list \<Rightarrow> 
 (mtag \<times> 'n) list \<Rightarrow> nat \<Rightarrow> bool \<times> bool \<times>  (mtag \<times> 'n)" where
  "evaluate es \<pi> e =
     (let a = fst_all ! e; d = snd_all ! e
      in if a = d
         then (False, nth es e = InU, pval_zero)
         else let t = nth es e;
                  g = pval_plus (cost_pval e) (pval_minus (\<pi> ! a) (\<pi> ! d))
              in ((case t of InTree \<Rightarrow> False | InL \<Rightarrow> pval_neg g | InU \<Rightarrow> pval_pos g), t = InU, g))"

fun better :: "'n best_cand \<Rightarrow> nat \<times> bool \<times>  (mtag \<times> 'n) 
       \<Rightarrow> 'n best_cand" where
  "better (found, be, bu, bg) (e', u', g') =
     (if \<not> found \<or> viol_gt g' bg then (True, e', u', g') else (found, be, bu, bg))"

definition bok :: "edge_tag list \<Rightarrow>  (mtag \<times> 'n) list \<Rightarrow> 'n best_cand \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool" where
  "bok es pt best a len =
     (case best of (f,e,u,g) \<Rightarrow>
        f \<longrightarrow> (eligible es pt e \<and> u = ent_in_U es e \<and> g = red_cost pt e \<and> e \<in> set (take len a)))"

function scan_cache ::
    "edge_tag list \<Rightarrow>  (mtag \<times> 'n) list \<Rightarrow> nat 
\<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> 'n best_cand
       \<Rightarrow> nat list \<times> nat \<times> 'n best_cand" where
  "scan_cache es \<pi> i a len best =
     (if len \<le> i then (a, len, best)
      else
        (let e = a ! i;
             (elig, u, g) = evaluate es \<pi> e
         in if elig
            then scan_cache es \<pi> (Suc i) a len (better best (e, u, g))
            else scan_cache es \<pi> i (a[i := a ! (len - 1)]) (len - 1) best))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(es, \<pi>, i, a, len, best). len - i)") auto

function scan ::
    "edge_tag list \<Rightarrow>  (mtag \<times> 'n) list \<Rightarrow> nat 
\<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> 'n best_cand
       \<Rightarrow> nat \<times> nat list \<times> nat \<times> 'n best_cand" where
  "scan es \<pi> mc fuel bpos cur a len best =
     (if fuel = 0 then (cur, a, len, best)
      else if max_candidates \<le> len then (cur, a, len, best)
      else if bpos = 0 \<and> min_candidates \<le> len then (cur, a, len, best)
      else
        (let bpos1 = (if bpos = 0 then block_size else bpos);
             (elig, u, g) = evaluate es \<pi> cur;
             a1    = (if elig then a[len := cur] else a);
             len1  = (if elig then Suc len else len);
             best1 = (if elig then better best (cur, u, g) else best);
             cur1  = (if cur + 1 = mc then 0 else cur + 1)
         in scan es \<pi> mc (fuel - 1) (bpos1 - 1) cur1 a1 len1 best1))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(es, \<pi>, mc, fuel, bpos, cur, a, len, best). fuel)") auto

definition sel_select_impl ::
    "ns_sel \<Rightarrow>  (mtag \<times> 'n) list \<Rightarrow> edge_tag list 
     \<Rightarrow> (nat \<times> bool \<times>  (mtag \<times> 'n) \<times> ns_sel) option" where
  "sel_select_impl sel \<pi> es =
     (case scan_cache es \<pi> 0 (sel_arr sel) (sel_len sel) no_best of
        (a1, len1, (found1, e, u, g)) \<Rightarrow>
          if found1
          then Some (e, u, g, sel\<lparr> sel_arr := a1, sel_len := len1 \<rparr>)
          else
            \<comment> \<open>first @{term marc} = the fixed arc count @{term mc}; second = the initial @{term fuel}\<close>
            (case scan es \<pi> marc marc block_size (sel_cur sel) a1 len1 no_best of
               (cur', a2, len2, (found2, e2, u2, g2)) \<Rightarrow>
                 if found2
                 then Some (e2, u2, g2, \<lparr> sel_cur = cur', sel_arr = a2, sel_len = len2 \<rparr>)
                 else None))"

definition sel_invar_impl :: "ns_sel \<Rightarrow> bool" where
  "sel_invar_impl sel \<longleftrightarrow>
     length (sel_arr sel) = max_candidates
     \<and> sel_len sel \<le> max_candidates
     \<and> (0 < marc \<longrightarrow> sel_cur sel < marc)
     \<and> set (take (sel_len sel) (sel_arr sel)) \<subseteq> {0..<marc}"

definition init_sel :: ns_sel where
  "init_sel = \<lparr> sel_cur = 0, sel_arr = replicate max_candidates 0, sel_len = 0 \<rparr>"


subsection \<open>The network-simplex loop on the augmented network\<close>

text \<open>The executable network-simplex specification, interpreted for the augmented network with only
      \<^emph>\<open>executable\<close> operations supplied: the endpoints / capacities are the augmented arrays, the
      spanning-tree operations are @{const get_path_pair_impl} / @{const swap_edge_impl} /
      @{const iterate_root_opposed_impl}, the entering-edge selector is @{const sel_select_impl}, and
      the potential arithmetic is @{const pval_plus} / @{const pval_minus}.  The verification-only
      parameters --- the real cost @{term \<c>}, the descriptor abstractions and the store/descriptor
      invariants --- are never evaluated by @{const network_simplex_spec.ns_loop_impl}, so they are given
      trivial placeholders here; their real form appears only in the proof interpretation.\<close>

interpretation NSc: network_simplex_init_spec
  where r = vcount
    and shift_pot = shift_pot_impl
    and get_path_pair = get_path_pair_impl
    and swap_edge = swap_edge_impl
    and flow_upd = list_update and flow_lookup = nth
    and pot_upd = list_update and pot_lookup = nth
    and parent_upd = list_update and parent_lookup = nth
    and dir_upd = list_update and dir_lookup = nth
    and es_upd = list_update and es_lookup = nth
    and sel_select = sel_select_impl
    and cap = "\<lambda> e. cap_all ! e"
    and pot_value_plus = pval_plus
    and pot_value_minus = pval_minus
    and fst_exec = "\<lambda> e. fst_all ! e"
    and snd_exec = "\<lambda> e. snd_all ! e"
    and init_flow = flow_all
    and init_pot = "ds_pot art_tree"
    and init_tree = "tree_st art_tree"
    and init_parent = "ds_par art_tree"
    and init_dir = "ds_dir art_tree"
    and init_edge_state = state_all
    and init_sel = init_sel
  by unfold_locales

text \<open>The starting state @{const NSc.init_state} --- the augmented flow / edge-state, the potentials, the
      abstract arborescence and the parent / direction arrays read off the builder of the acyclified
      flow, and the fresh entering-edge selector --- is provided by the interpreted @{locale
      network_simplex_init_spec}, not redefined here.\<close>

text \<open>The orchestrator. First acyclify @{term flow_list}: a @{term None} answer is a negative
      infinite-capacity cycle, reported as @{const Neg_inf_cycle}. Otherwise build the strongly-feasible
      spanning tree and run the network-simplex loop from @{const NSc.init_state}. Its @{const return} flag
      distinguishes an @{const unbounded} circuit (again @{const Neg_inf_cycle}) from @{const success} (an
      optimum of the \<^emph>\<open>augmented\<close> network). On success we inspect the artificial edges
      @{term \<open>[m..<m+Kart]\<close>}: if they all carry zero flow the original network is feasible and
      the minimum-cost @{term b}-flow is the augmented flow
      \<^emph>\<open>restricted to the original edges\<close> (@{term \<open>take m\<close>}); if any
      artificial edge still carries flow, no @{term b}-flow exists and the verdict is @{const Infeasible}.\<close>

definition solve :: "'n ns_outcome" where
  "solve =
     (let ao = acyc_flow_opt
      in case ao of
           None \<Rightarrow> Neg_inf_cycle
         | Some _ \<Rightarrow>
             (let s = NSc.ns_loop_impl NSc.init_state; f = current_flow s
              in if return s = unbounded then Neg_inf_cycle
                 else if list_all (\<lambda>k. f ! k = 0) [m..<m+Kart]
                      then Optimum (take m f )
                      else Infeasible))"


end

end


