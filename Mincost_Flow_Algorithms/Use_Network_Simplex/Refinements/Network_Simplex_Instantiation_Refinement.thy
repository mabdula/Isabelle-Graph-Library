
theory Network_Simplex_Instantiation_Refinement
  imports Use_Network_Simplex.Network_Simplex_Initial_Basis_Selector
          Network_Simplex_Refinement
          Acyclic_Flow_Refinement
          Directed_Set_Graphs.CSR_Edge_Input
          Data_Structures.List_Cursor_Imperative
          Data_Structures.Imp_Array_Fun
          Use_Network_Simplex.Rooted_Arborescense_Refinement
begin

section \<open>Imperative refinement of the orchestrator @{const initial_basis_code_spec.solve}\<close>

text \<open>This theory assembles the imperative counterpart of the top-level functional orchestrator
      @{const initial_basis_code_spec.solve}.  The functional program

      \<^item> acyclifies the input flow (@{const initial_basis_code_spec.acyc_flow_opt}); a @{term None}
        answer is a negative infinite-capacity cycle;
      \<^item> otherwise builds the strongly-feasible spanning tree, runs the network-simplex loop
        (\<open>NSc.ns_loop_impl\<close> from \<open>NSc.init_state\<close>) and, on a bounded optimum of the augmented
        network, reads the verdict off the artificial edges @{term \<open>[m..<m + Kart]\<close>}.

      The imperative version reuses the two big already-verified refinements --- \<open>make_acyclic_imp\<close>
      (see \<open>make_acyclic_imp_rule\<close>) and \<open>ns_loop_imp\<close> (see \<open>ns_loop_imp_rule\<close>) --- and glues them with a
      materialisation step and a final artificial-edge scan.  All stores are @{class heap} arrays;
      arrays are reused across phases (the acyclifier's DFS stacks and CSR blocks are handed on as
      the network-simplex path buffers and spanning-tree scaffold once the acyclifier no longer
      needs them).\<close>

subsection \<open>The three-valued solution flag\<close>

text \<open>The imperative orchestrator returns only a status flag; the optimum flow --- when one exists ---
      is left in the first @{term m} cells of the flow array.  The flag mirrors the three shapes of
      the functional @{typ \<open>'n ns_outcome\<close>}: @{const Optimum} {\isasymmapsto} @{term OptimalF},
      @{const Infeasible} {\isasymmapsto} @{term InfeasibleF}, @{const Neg_inf_cycle} {\isasymmapsto} @{term NegInfCycleF}.\<close>

datatype solve_status = OptimalF | InfeasibleF | NegInfCycleF

text \<open>Abstraction from a functional outcome to the flag it corresponds to.\<close>
fun status_of :: "'n ns_outcome \<Rightarrow> solve_status" where
  "status_of (Optimum _)   = OptimalF"
| "status_of Infeasible    = InfeasibleF"
| "status_of Neg_inf_cycle = NegInfCycleF"

subsection \<open>The artificial-edge scan\<close>

text \<open>The concrete counterpart of @{term \<open>list_all (\<lambda>k. f ! k = 0) [m..<m + Kart]\<close>}: walk the flow
      array over the artificial index range @{term \<open>[i..<hi]\<close>} and report whether every artificial
      edge carries zero flow.  Purely a read loop over one array; no allocation.\<close>

partial_function (heap) scan_art_imp ::
  "('n::{heap,zero}) array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool Heap"
  where
  "scan_art_imp fa i hi =
     (if hi \<le> i then return True
      else do { v \<leftarrow> Array.nth fa i;
                if v = 0 then scan_art_imp fa (Suc i) hi else return False })"

text \<open>@{const scan_art_imp} computes exactly the functional test
      @{term \<open>list_all (\<lambda>k. xs ! k = 0) [i..<hi]\<close>} on the array contents, leaving the array
      untouched.  By induction on the remaining length @{term \<open>hi - i\<close>}, unfolding the fixpoint one
      step per iteration.\<close>

lemma scan_art_imp_rule:
  "hi \<le> length xs \<Longrightarrow>
   <fa \<mapsto>\<^sub>a xs> scan_art_imp fa i hi
   <\<lambda>b. fa \<mapsto>\<^sub>a xs * \<up>(b = list_all (\<lambda>k. xs ! k = 0) [i..<hi])>"
proof (induction "hi - i" arbitrary: i)
  case 0
  hence "hi \<le> i" by simp
  thus ?case by (subst scan_art_imp.simps) sep_auto
next
  case (Suc d)
  from Suc.hyps(2) have il: "i < hi" by simp
  hence il2: "i < length xs" using Suc.prems by simp
  have du: "d = hi - Suc i" using Suc.hyps(2) by simp
  have IH: "<fa \<mapsto>\<^sub>a xs> scan_art_imp fa (Suc i) hi
             <\<lambda>b. fa \<mapsto>\<^sub>a xs * \<up>(b = list_all (\<lambda>k. xs ! k = 0) [Suc i..<hi])>"
    using Suc.hyps(1)[OF du Suc.prems] .
  have split: "list_all (\<lambda>k. xs ! k = 0) [i..<hi]
             = (xs ! i = 0 \<and> list_all (\<lambda>k. xs ! k = 0) [Suc i..<hi])"
    using il by (simp add: upt_conv_Cons)
  show ?case
    by (subst scan_art_imp.simps)
       (sep_auto simp: split il2 heap: IH)
qed

section \<open>Concrete imperative data structures\<close>

text \<open>The functional program models every store as a \<^emph>\<open>list read as an array\<close> and every iterator by
      a record with a moving cursor.  Here we give the genuine mutable-array counterparts, each a
      plain top-level Heap program that \<^emph>\<open>exactly refines\<close> its functional operation, so that the two
      abstract refinement locales (the acyclifier and the network-simplex loop) can be instantiated
      at them.  Nothing here lives in a locale; the refinement obligations are discharged later in
      the proof locale of @{const initial_basis_code_spec.solve}.\<close>

subsection \<open>Flow / vertex-state stores --- plain arrays\<close>

text \<open>The abstract-array model uses @{const nth} for lookup and @{const list_update} for update; the
      mutable counterparts are @{const Array.nth} and @{term \<open>\<lambda>a i x. Array.upd i x a\<close>}, with the
      store assertion the standard @{term \<open>(\<mapsto>\<^sub>a)\<close>}.  No wrapper is needed: the array primitives are
      used directly when instantiating.\<close>



section \<open>Heap instances for the datatypes stored in arrays\<close>

text \<open>The potential tags are held in mutable arrays, so they must be @{class heap} (i.e.
      @{class countable} and @{class typerep}); the vertex states and the edge tags are made instances
      in the refinement theories of the acyclifier and of the loop.\<close>


instance mtag :: countable by countable_datatype
instance mtag :: heap ..

section \<open>Instantiating the imperative acyclifier\<close>

text \<open>The imperative acyclifier is defined in the assumption-free specification locale
      @{locale acyclic_flow_impl_refine}, which fixes only the manipulating \<^emph>\<open>functions\<close> --- no
      assumptions and no fixed arrays.  We turn it into \<^emph>\<open>actual code\<close> by a @{command
      global_interpretation}: the store / iterator functions are the concrete array-manipulating
      programs built above, and the four per-edge reads are array look-ups closing over the \<^emph>\<open>four
      graph arrays\<close>, which the \<open>for\<close> clause makes \<^emph>\<open>parameters\<close> of the generated constant.
      The interpretation is provable outright (no assumptions), and @{term make_acyclic_prog} is the
      resulting executable, taking @{term cap_arr}, @{term cost_arr}, @{term fst_arr}, @{term snd_arr}
      (via \<open>for\<close>) and the eight store handles as arguments --- every array handed in.\<close>

global_interpretation acyc: acyclic_flow_impl_refine
  where out_current_imp = csr_current_imp and out_has_imp = csr_has_imp
    and out_move_imp = csr_move_imp and out_reset_imp = csr_reset_imp
    and in_current_imp = csr_current_imp and in_has_imp = csr_has_imp
    and in_move_imp = csr_move_imp and in_reset_imp = csr_reset_imp
    and flow_upd_imp = array_fun_upd_imp and flow_lookup_imp = Array.nth
    and st_upd_imp = array_fun_upd_imp and st_lookup_imp = Array.nth
    and current_vertex_imp = lc_current_imp and has_vertex_imp = lc_has_imp
    and move_on_vertex_imp = lc_move_imp
    and cap_imp  = "\<lambda>e. Array.nth cap_arr  e" and cost_imp = "\<lambda>e. Array.nth cost_arr e"
    and fst_exec_imp = "\<lambda>e. Array.nth fst_arr e" and snd_exec_imp = "\<lambda>e. Array.nth snd_arr e"
  for cap_arr cost_arr fst_arr snd_arr
  defines make_acyclic_prog = acyc.make_acyclic_imp
  by unfold_locales

text \<open>Register the recursive Heap sub-programs' fixpoint equations as code equations (the
      @{command partial_function} @{text simps}), so the acyclifier is code-generatable --- the same
      discipline as \<open>DFS_imperative.simps\<close> in the imperative-DFS template.\<close>
lemmas [code] =
  acyclic_flow_impl_refine.af_rooms_imp_def
  acyclic_flow_impl_refine.af_delta_cost_imp_def
  acyclic_flow_impl_refine.af_min_imp_def
  acyclic_flow_impl_refine.af_push_arc_imp_def
  acyclic_flow_impl_refine.af_saturated_imp_def
  acyclic_flow_impl_refine.af_cancel_seg_imp_def
  acyclic_flow_impl_refine.af_reset_imp_def
  acyclic_flow_impl_refine.af_selfloop_handle_imp_def
  acyclic_flow_impl_refine.af_close_cycle_imp_def
  acyclic_flow_impl_refine.af_push_vertex_imp_def
  acyclic_flow_impl_refine.af_handle_imp_def
  acyclic_flow_impl_refine.af_dfs_start_imp_def
  acyclic_flow_impl_refine.af_impl_state_init_def
  acyclic_flow_impl_refine.af_scan_imp.simps
  acyclic_flow_impl_refine.af_push_imp.simps
  acyclic_flow_impl_refine.af_reset_unsee_seg_imp.simps
  acyclic_flow_impl_refine.AF_DFS_imp.simps
  acyclic_flow_impl_refine.AF_outer_imp.simps

export_code make_acyclic_prog checking SML_imp
export_code make_acyclic_prog in SML module_name Acyclifier

section \<open>Instantiating the imperative network-simplex loop\<close>

text \<open>The imperative loop \<open>ns_loop_imp\<close> is defined in the assumption-free specification locale
      @{locale network_simplex_impl_spec}, which fixes the manipulating \<^emph>\<open>functions\<close>: the
      entering-edge selector, the three spanning-tree operations (subtree potential-shift,
      fundamental-circuit path search, tree-edge swap) and the flow / potential / parent / direction /
      edge-state store reads and writes.  We build the concrete functions here and turn the loop into
      \<^emph>\<open>actual code\<close> by a @{command global_interpretation}, as for the acyclifier.  The spanning-tree
      primitives are the already-verified imperative ports @{const update_tree_imp},
      @{const get_path_pair_imp}, @{const iterate_root_opposed_imp} of \<open>Rooted_Arborescense_Refinement\<close>;
      the network-simplex operations are thin compositions of them.  No arrays are allocated --- every
      store is a fixed function and the graph arrays / tuning constants remain
      @{command global_interpretation} parameters, allocated only in the final orchestrator.\<close>

subsection \<open>The three spanning-tree operations, on @{typ ndtree_impl}\<close>

text \<open>The join (apex / LCA) of @{term u} and @{term v}: the two pointers converge upward, the one with
      the smaller subtree size (@{const snum_impl}) climbing to its parent, until they meet --- the
      imperative counterpart of @{const join_of}.  This mirrors the convergence of
      @{const join_paths_loop_imp} but keeps only the meeting vertex.\<close>
partial_function (heap) join_of_imp :: "ndtree_impl \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "join_of_imp Ti u v =
     (if u = v then return u
      else do { snu \<leftarrow> Array.nth (snum_impl Ti) u;
                snv \<leftarrow> Array.nth (snum_impl Ti) v;
                (if snu \<le> snv
                 then do { pu \<leftarrow> Array.nth (prnt_impl Ti) u; join_of_imp Ti pu v }
                 else do { pv \<leftarrow> Array.nth (prnt_impl Ti) v; join_of_imp Ti u pv }) })"

text \<open>The snum-driven climb refines the functional @{const join_of}: for any common ancestor @{term j}
      of @{term cu} and @{term cv} whose strictly-below prefixes are disjoint, @{const join_of_imp}
      returns @{term j}.  Proved by strong induction on the combined remaining root-path length, the
      exact skeleton of @{thm join_paths_loop_imp_rule} but tracking only the meeting vertex.\<close>
lemma join_of_imp_rule:
  assumes inv: "arb_invar r V S"
  shows "cu \<in> V \<Longrightarrow> cv \<in> V \<Longrightarrow> j \<in> set (follow (prnt S) cu) \<Longrightarrow> j \<in> set (follow (prnt S) cv) \<Longrightarrow>
    set (takeWhile (\<lambda>x. x \<noteq> j) (follow (prnt S) cu)) \<inter> set (takeWhile (\<lambda>x. x \<noteq> j) (follow (prnt S) cv)) = {} \<Longrightarrow>
    <ndtree_assn V S Ti> join_of_imp Ti cu cv <\<lambda>res. ndtree_assn V S Ti * \<up>(res = j)>"
proof -
  have rinv: "rooted_arborescense_invar r V (prnt S)" using inv unfolding arb_invar_def by simp
  have ps: "parent_spec (prnt S)" by (rule rooted_arborescense_invar_parent_spec[OF rinv])
  define W where "W = (\<lambda>x. takeWhile (\<lambda>y. y \<noteq> j) (follow (prnt S) x))"
  { fix N cu cv
    have "length (follow (prnt S) cu) + length (follow (prnt S) cv) = N \<Longrightarrow> cu \<in> V \<Longrightarrow> cv \<in> V \<Longrightarrow>
          j \<in> set (follow (prnt S) cu) \<Longrightarrow> j \<in> set (follow (prnt S) cv) \<Longrightarrow> set (W cu) \<inter> set (W cv) = {} \<Longrightarrow>
          <ndtree_assn V S Ti> join_of_imp Ti cu cv <\<lambda>res. ndtree_assn V S Ti * \<up>(res = j)>"
    proof (induct N arbitrary: cu cv rule: less_induct)
      case (less N cu cv)
      note eqN = less.prems(1) and cuV = less.prems(2) and cvV = less.prems(3) and jcu = less.prems(4)
        and jcv = less.prems(5) and disj = less.prems(6)
      have jV: "j \<in> V" using follow_subset_V[OF rinv cuV] jcu by auto
      show ?case
      proof (cases "cu = cv")
        case True
        note eqcc = True
        have cuj: "cu = j"
        proof (rule ccontr)
          assume cune: "cu \<noteq> j"
          have "cu \<in> set (W cu)"
          proof -
            have ne: "follow (prnt S) cu \<noteq> []" by (rule follow_ne_ps[OF ps])
            have hd: "hd (follow (prnt S) cu) = cu" by (rule follow_hd_ps[OF ps])
            show ?thesis using ne hd cune by (cases "follow (prnt S) cu") (auto simp: W_def)
          qed
          moreover have "cu \<in> set (W cv)" using eqcc calculation by simp
          ultimately show False using disj by auto
        qed
        show ?thesis using eqcc cuj by (subst join_of_imp.simps) sep_auto
      next
        case False
        note cune_cv = False
        show ?thesis
        proof (cases "snum S cu \<le> snum S cv")
          case True
          note le = True
          have cune: "cu \<noteq> j"
          proof (rule ccontr)
            assume "\<not> cu \<noteq> j" hence cj: "cu = j" by simp
            have cvne: "cv \<noteq> j" using cune_cv cj by auto
            have "snum S cv < snum S j" using snum_proper_anc_lt[OF inv jV jcv] cvne by simp
            thus False using le cj by simp
          qed
          obtain w where Pw: "prnt S cu = Some w" and fcu: "follow (prnt S) cu = cu # follow (prnt S) w"
            and jcw: "j \<in> set (follow (prnt S) w)" using follow_cons_of_anc[OF ps jcu cune] by auto
          have Wcu: "W cu = cu # W w" using fcu cune by (simp add: W_def)
          have wmem: "w \<in> set (follow (prnt S) cu)" using fcu follow_hd_ps[OF ps, of w] follow_ne_ps[OF ps, of w]
            by (metis hd_in_set list.set_intros(2))
          have wV: "w \<in> V" using follow_subset_V[OF rinv cuV] wmem by auto
          have disj': "set (W w) \<inter> set (W cv) = {}" using disj Wcu by auto
          have lenlt: "length (follow (prnt S) w) + length (follow (prnt S) cv) < N" using eqN fcu by simp
          note IH2 = less.hyps[OF lenlt refl wV cvV jcw jcv disj']
          have poeq: "nat_of_opt (prnt S cu) = w" using Pw by simp
          show ?thesis
            apply (subst join_of_imp.simps)
            apply (sep_auto simp: cune_cv le cuV cvV poeq heap: IH2)
            done
        next
          case False
          note notle = False
          have cvne: "cv \<noteq> j"
          proof (rule ccontr)
            assume "\<not> cv \<noteq> j" hence cj: "cv = j" by simp
            have cune: "cu \<noteq> j" using cune_cv cj by auto
            have "snum S cu < snum S j" using snum_proper_anc_lt[OF inv jV jcu] cune by simp
            thus False using notle cj by simp
          qed
          obtain w where Pw: "prnt S cv = Some w" and fcv: "follow (prnt S) cv = cv # follow (prnt S) w"
            and jcw: "j \<in> set (follow (prnt S) w)" using follow_cons_of_anc[OF ps jcv cvne] by auto
          have Wcv: "W cv = cv # W w" using fcv cvne by (simp add: W_def)
          have wmem: "w \<in> set (follow (prnt S) cv)" using fcv follow_hd_ps[OF ps, of w] follow_ne_ps[OF ps, of w]
            by (metis hd_in_set list.set_intros(2))
          have wV: "w \<in> V" using follow_subset_V[OF rinv cvV] wmem by auto
          have disj': "set (W cu) \<inter> set (W w) = {}" using disj Wcv by auto
          have lenlt: "length (follow (prnt S) cu) + length (follow (prnt S) w) < N" using eqN fcv by simp
          note IH2 = less.hyps[OF lenlt refl cuV wV jcu jcw disj']
          have poeq: "nat_of_opt (prnt S cv) = w" using Pw by simp
          show ?thesis
            apply (subst join_of_imp.simps)
            apply (sep_auto simp: cune_cv notle cuV cvV poeq heap: IH2)
            done
        qed
      qed
    qed }
  note gen = this[unfolded W_def]
  show "cu \<in> V \<Longrightarrow> cv \<in> V \<Longrightarrow> j \<in> set (follow (prnt S) cu) \<Longrightarrow> j \<in> set (follow (prnt S) cv) \<Longrightarrow>
    set (takeWhile (\<lambda>x. x \<noteq> j) (follow (prnt S) cu)) \<inter> set (takeWhile (\<lambda>x. x \<noteq> j) (follow (prnt S) cv)) = {} \<Longrightarrow>
    <ndtree_assn V S Ti> join_of_imp Ti cu cv <\<lambda>res. ndtree_assn V S Ti * \<up>(res = j)>"
    by (rule gen[OF refl])
qed

text \<open>Specialised to the deepest common ancestor: @{const join_of_imp} returns exactly
      @{term \<open>join_of (prnt S) u v\<close>}.  The common-ancestor side conditions of @{thm join_of_imp_rule}
      are the @{thm join_of_mem} membership and @{thm join_takeWhile_disjoint} disjointness at the join.\<close>
lemma join_of_imp_correct:
  assumes inv: "arb_invar r V S" and uV: "u \<in> V" and vV: "v \<in> V"
  shows "<ndtree_assn V S Ti> join_of_imp Ti u v
           <\<lambda>res. ndtree_assn V S Ti * \<up>(res = join_of (prnt S) u v)>"
proof -
  have rinv: "rooted_arborescense_invar r V (prnt S)" using inv unfolding arb_invar_def by simp
  have ps: "parent_spec (prnt S)" by (rule rooted_arborescense_invar_parent_spec[OF rinv])
  have lst: "last (follow (prnt S) u) = last (follow (prnt S) v)"
    using follow_last_root[OF inv uV] follow_last_root[OF inv vV] by simp
  have ju: "join_of (prnt S) u v \<in> set (follow (prnt S) u)" using join_of_mem(1)[OF ps lst] .
  have jv: "join_of (prnt S) u v \<in> set (follow (prnt S) v)" using join_of_mem(2)[OF ps lst] .
  have disjj: "set (takeWhile (\<lambda>x. x \<noteq> join_of (prnt S) u v) (follow (prnt S) u))
              \<inter> set (takeWhile (\<lambda>x. x \<noteq> join_of (prnt S) u v) (follow (prnt S) v)) = {}"
    using join_takeWhile_disjoint[OF inv uV vV refl] .
  show ?thesis by (rule join_of_imp_rule[OF inv uV vV ju jv disjj])
qed
text \<open>The functional \<open>swap_edge_impl S x u v = update_tree S u v x (join_of (prnt S) u v)\<close>,
      imperatively: compute the join of the entering edge's endpoints and hand it to
      @{const update_tree_imp}.\<close>
definition ns_swap_edge_imp :: "ndtree_impl \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "ns_swap_edge_imp Ti x u v = do { j \<leftarrow> join_of_imp Ti u v; update_tree_imp Ti u v x j }"

text \<open>The functional \<open>get_path_pair_impl\<close>, imperatively: the verified @{const get_path_pair_imp} with
      the two caller path arrays moved after the endpoints, to match the fixed operation's argument
      order.\<close>
definition ns_get_path_pair_imp ::
  "ndtree_impl \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> (nat \<times> nat) Heap" where
  "ns_get_path_pair_imp Ti u v a1 a2 = get_path_pair_imp Ti a1 a2 u v"

text \<open>The functional \<open>shift_pot_impl\<close>, imperatively: fold the read/shift/write of the potential cell
      over the subtree of @{term v} opposed to the root, via the verified
      @{const iterate_root_opposed_imp}.  The sign of the shift is chosen by @{term up} (add on the
      up-side, subtract on the down-side).  The accumulator is the unused unit --- the potential array is
      mutated in place.\<close>
definition ns_shift_pot_imp ::
  "ndtree_impl \<Rightarrow> nat \<Rightarrow> (mtag \<times> 'n::{heap,linordered_idom}) array \<Rightarrow> (mtag \<times> 'n) \<Rightarrow> bool \<Rightarrow> unit Heap" where
  "ns_shift_pot_imp Ti v pa g up =
     iterate_root_opposed_imp Ti v
       (\<lambda>x (_::unit). do { p \<leftarrow> Array.nth pa x;
                           _ \<leftarrow> Array.upd x (if up then pval_plus p g else pval_minus p g) pa;
                           return () }) ()"

subsection \<open>The entering-edge selector, imperatively\<close>

text \<open>The M-free block-search selector, ported to the Heap monad.  The candidate cache becomes a
      @{typ \<open>nat array\<close>}, and the bookmark / live-length become @{typ \<open>nat ref\<close>}s; the running best is
      carried as the pure flat @{typ \<open>'n best_cand\<close>}.  Everything else (the reduced-cost descriptor
      arithmetic, the eligibility and violation tests) is the same M-free pure code as the functional
      selector --- the pure @{const initial_basis_code_spec.better} is reused directly --- so the
      executable counterparts of \<open>cost_pval\<close> / \<open>evaluate\<close> / \<open>scan_cache\<close> / \<open>scan\<close> differ only in
      reading their inputs from arrays.  The tuning constants (@{term m}, the arc count, the block
      size, the min / max candidate counts) and the three graph arrays (endpoints, cost) stay
      parameters, fixed only in the orchestrator.\<close>

type_synonym ns_sel_imp = "nat array \<times> nat ref \<times> nat ref"

text \<open>The functional \<open>cost_pval\<close>: the plain cost of an original edge (tag @{term M_0}), or the
      artificial cost @{const pval_M} for an artificial edge @{term \<open>e \<ge> m\<close>}.\<close>
definition cost_pval_imp :: "nat \<Rightarrow> 'n::{heap,linordered_idom} array \<Rightarrow> nat \<Rightarrow> (mtag \<times> 'n) Heap" where
  "cost_pval_imp m cost_arr e =
     (if e < m then do { c \<leftarrow> Array.nth cost_arr e; return (M_0, c) } else return pval_M)"

text \<open>The functional \<open>evaluate\<close>: read the edge tag and endpoints once; a self-loop is ineligible
      without pricing; otherwise assemble the reduced-cost descriptor once and test its sign M-free.\<close>
definition evaluate_imp ::
  "nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> 'n::{heap,linordered_idom} array \<Rightarrow> edge_tag array
   \<Rightarrow> (mtag \<times> 'n) array \<Rightarrow> nat \<Rightarrow> (bool \<times> bool \<times> (mtag \<times> 'n)) Heap" where
  "evaluate_imp m fst_arr snd_arr cost_arr es pt e =
     do { a \<leftarrow> Array.nth fst_arr e; d \<leftarrow> Array.nth snd_arr e; t \<leftarrow> Array.nth es e;
          if a = d then return (False, t = InU, pval_zero)
          else do { cp \<leftarrow> cost_pval_imp m cost_arr e;
                    pa \<leftarrow> Array.nth pt a; pd \<leftarrow> Array.nth pt d;
                    (let g = pval_plus cp (pval_minus pa pd)
                     in return ((case t of InTree \<Rightarrow> False | InL \<Rightarrow> pval_neg g | InU \<Rightarrow> pval_pos g),
                                t = InU, g)) } }"

text \<open>Minor iteration (the functional \<open>scan_cache\<close>): one pass over the live prefix @{term \<open>[0..<len]\<close>}
      of the cache array; a still-eligible entry is priced once and offered to the running best (index
      advances), a dud is deleted by swap-with-last (write @{term \<open>sarr ! (len-1)\<close>} into slot @{term i},
      drop the length, do not advance).  Returns the shrunk length and the best; the array is mutated in
      place.\<close>
partial_function (heap) scan_cache_imp ::
  "nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> 'n::{heap,linordered_idom} array \<Rightarrow> edge_tag array
   \<Rightarrow> (mtag \<times> 'n) array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'n best_cand \<Rightarrow> (nat \<times> 'n best_cand) Heap" where
  "scan_cache_imp m fst_arr snd_arr cost_arr es pt sarr i len best =
     (if len \<le> i then return (len, best)
      else do {
        e \<leftarrow> Array.nth sarr i;
        (elig, u, g) \<leftarrow> evaluate_imp m fst_arr snd_arr cost_arr es pt e;
        (if elig
         then scan_cache_imp m fst_arr snd_arr cost_arr es pt sarr (Suc i) len
                (initial_basis_code_spec.better best (e, u, g))
         else do { lst \<leftarrow> Array.nth sarr (len - 1);
                   _ \<leftarrow> array_fun_upd_imp sarr i lst;
                   scan_cache_imp m fst_arr snd_arr cost_arr es pt sarr i (len - 1) best }) })"

text \<open>Major iteration (the functional \<open>scan\<close>): the wrap-around block sweep from the bookmark
      @{term cur}, at most @{term fuel} arcs, stopping when the cache reaches the max candidate count or
      a whole block has been scanned and at least the min candidate count is held.  An eligible arc is
      pushed at the length pointer.  Returns the advanced bookmark, the new length and the best; the
      cache array is mutated in place.\<close>
partial_function (heap) scan_imp ::
  "nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> 'n::{heap,linordered_idom} array
   \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> edge_tag array \<Rightarrow> (mtag \<times> 'n) array \<Rightarrow> nat array
   \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'n best_cand \<Rightarrow> (nat \<times> nat \<times> 'n best_cand) Heap" where
  "scan_imp m fst_arr snd_arr cost_arr min_c max_c block_size mc es pt sarr fuel bpos cur len best =
     (if fuel = 0 then return (cur, len, best)
      else if max_c \<le> len then return (cur, len, best)
      else if bpos = 0 \<and> min_c \<le> len then return (cur, len, best)
      else do {
        (elig, u, g) \<leftarrow> evaluate_imp m fst_arr snd_arr cost_arr es pt cur;
        _ \<leftarrow> (if elig then array_fun_upd_imp sarr len cur else return ());
        (let bpos1 = (if bpos = 0 then block_size else bpos);
             len1  = (if elig then Suc len else len);
             best1 = (if elig then initial_basis_code_spec.better best (cur, u, g) else best);
             cur1  = (if cur + 1 = mc then 0 else cur + 1)
         in scan_imp m fst_arr snd_arr cost_arr min_c max_c block_size mc es pt sarr
                     (fuel - 1) (bpos1 - 1) cur1 len1 best1) })"

text \<open>The functional \<open>sel_select_impl\<close>, imperatively: minor iteration first; if it finds an entering
      edge, commit the shrunk length and return it; otherwise a major iteration, committing bookmark and
      length on success, @{term None} (optimal) otherwise.  The state triple is mutated in place, so the
      returned tuple drops the selector --- exactly the \<^emph>\<open>\_imp\<close> discipline.\<close>
definition ns_sel_select_imp ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> 'n::{heap,linordered_idom} array
   \<Rightarrow> ns_sel_imp \<Rightarrow> (mtag \<times> 'n) array \<Rightarrow> edge_tag array
   \<Rightarrow> (nat \<times> bool \<times> (mtag \<times> 'n)) option Heap" where
  "ns_sel_select_imp m mc block_size min_c max_c fst_arr snd_arr cost_arr sel pt es =
     (let sarr = fst sel; cref = fst (snd sel); lref = snd (snd sel)
      in do {
        len0 \<leftarrow> Ref.lookup lref;
        (len1, b1) \<leftarrow> scan_cache_imp m fst_arr snd_arr cost_arr es pt sarr 0 len0 no_best;
        (case b1 of (found1, e1, u1, g1) \<Rightarrow>
           if found1 then do { _ \<leftarrow> Ref.update lref len1; return (Some (e1, u1, g1)) }
           else do {
             cur0 \<leftarrow> Ref.lookup cref;
             (cur2, len2, b2) \<leftarrow> scan_imp m fst_arr snd_arr cost_arr min_c max_c block_size mc
                                          es pt sarr mc block_size cur0 len1 no_best;
             (case b2 of (found2, e2, u2, g2) \<Rightarrow>
                if found2 then do { _ \<leftarrow> Ref.update cref cur2; _ \<leftarrow> Ref.update lref len2;
                                    return (Some (e2, u2, g2)) }
                else return None) }) })"

subsection \<open>The @{command global_interpretation}\<close>

text \<open>The store reads are @{const Array.nth}, the store writes @{const array_fun_upd_imp}; the two path buffers
      are plain @{typ \<open>nat array\<close>}s.  The selector, the three tree operations and the endpoint /
      capacity reads are the concrete functions above.  The graph arrays and the selector's tuning
      constants become parameters via \<open>for\<close>; @{term ns_loop_prog} is the resulting executable loop.\<close>

global_interpretation ns: network_simplex_impl_spec
  where r = r
    and sel_select_imp =
          "ns_sel_select_imp m marc_c block_c minc_c maxc_c fst_arr snd_arr cost_arr"
    and shift_pot_imp = ns_shift_pot_imp
    and get_path_pair_imp = ns_get_path_pair_imp
    and swap_edge_imp = ns_swap_edge_imp
    and flow_upd_imp = array_fun_upd_imp and flow_lookup_imp = Array.nth
    and parent_upd_imp = array_fun_upd_imp and parent_lookup_imp = Array.nth
    and dir_upd_imp = array_fun_upd_imp and dir_lookup_imp = Array.nth
    and es_upd_imp = array_fun_upd_imp and es_lookup_imp = Array.nth
    and cap_imp = "Array.nth cap_arr"
    and fst_exec_imp = "Array.nth fst_arr"
    and snd_exec_imp = "Array.nth snd_arr"
  for r m marc_c block_c minc_c maxc_c fst_arr snd_arr cost_arr cap_arr
  defines ns_loop_prog = ns.ns_loop_imp
  by unfold_locales

section \<open>Materialising the strongly-feasible initial basis\<close>

text \<open>The imperative port of the functional builder \<open>build_tree\<close> / \<open>art_tree\<close> of
      \<open>Network_Simplex_Initial_Basis_Code\<close>: a genuine array program that, from the acyclified flow left
      in the flow array, fills the augmented edge arrays (the artificial tail @{term \<open>[m..<m+Kart]\<close>})
      and the strongly-feasible spanning tree --- the very @{typ ndtree_impl}, parent / direction /
      potential arrays and edge-state array the network-simplex loop then mutates.  Following the
      functional code, \<^emph>\<open>arrays are reused, not reallocated\<close>: the edge arrays of the two CSRs of the
      input become the free ranges in place (Pass A appends the free edges of each vertex to an
      initially empty range at the start of its block, @{const csr_append_imp}), the excess
      accumulator is transformed in place into the imbalance, and the DFS stack reuses a stack array
      of the acyclifier.\<close>

subsection \<open>Pass A: the free ranges, in place\<close>

text \<open>The functional \<open>passA_step\<close> as a Heap loop over the edge range @{term \<open>[e..<hi]\<close>}.  For each edge
      it writes the edge tag into the (augmented) edge-state array, accumulates the excess (head then
      tail, so a self-loop cancels), and appends a \<^emph>\<open>free\<close> edge (tag @{const InTree}) to the free
      outgoing range of its tail and the free ingoing range of its head.  The edge arrays
      @{term oe_arr} / @{term ie_arr} are those of the two CSRs, the range ends @{term oh_arr} /
      @{term ih_arr} start at the block starts.\<close>
partial_function (heap) passA_imp ::
  "'n::{heap,linordered_idom} array \<Rightarrow> 'n array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> edge_tag array \<Rightarrow> 'n array
   \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "passA_imp fl cap_arr fst_arr snd_arr es_arr exc_arr oe_arr oh_arr ie_arr ih_arr e hi =
     (if hi \<le> e then return ()
      else do {
        x \<leftarrow> Array.nth fst_arr e; y \<leftarrow> Array.nth snd_arr e;
        f \<leftarrow> Array.nth fl e; u \<leftarrow> Array.nth cap_arr e;
        (let st = (if f = 0 then InL else if u \<noteq> - 1 \<and> f = u then InU else InTree)
         in do {
           _ \<leftarrow> array_fun_upd_imp es_arr e st;
           ey \<leftarrow> Array.nth exc_arr y; _ \<leftarrow> array_fun_upd_imp exc_arr y (ey + f);
           ex \<leftarrow> Array.nth exc_arr x; _ \<leftarrow> array_fun_upd_imp exc_arr x (ex - f);
           _ \<leftarrow> (if st = InTree
                then do { _ \<leftarrow> csr_append_imp oe_arr oh_arr x e; csr_append_imp ie_arr ih_arr y e }
                else return ());
           passA_imp fl cap_arr fst_arr snd_arr es_arr exc_arr oe_arr oh_arr ie_arr ih_arr (Suc e) hi }) })"

subsection \<open>Imbalance: the excess transformed in place\<close>

text \<open>The functional \<open>imbalance = fold (\<lambda>v arr. arr[v := arr ! v + b_lookup v]) [0..<vcount] excess\<close>:
      add each vertex's target balance to its achieved excess, in place on the (reused) excess array.\<close>
partial_function (heap) imbalance_imp ::
  "'n::{heap,linordered_idom} array \<Rightarrow> 'n array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "imbalance_imp exc_arr b_arr v vcount =
     (if vcount \<le> v then return ()
      else do { e \<leftarrow> Array.nth exc_arr v; bb \<leftarrow> Array.nth b_arr v;
                _ \<leftarrow> array_fun_upd_imp exc_arr v (e + bb);
                imbalance_imp exc_arr b_arr (Suc v) vcount })"

subsection \<open>The imperative builder state\<close>

text \<open>The mutable counterpart of the functional @{typ \<open>'n dfs_state\<close>}: a bundle of the array / reference
      handles the DFS builder mutates.  The five spanning-tree maps live in the @{typ ndtree_impl}
      @{term di_tree} (whose arrays \<^emph>\<open>are\<close> the network-simplex loop's tree, filled here); the parent /
      direction / potential / edge-state arrays are likewise the loop's own stores.  The artificial
      edges are written \<^emph>\<open>directly into the augmented endpoint / capacity / flow / edge-state arrays\<close>
      at index @{term \<open>m + k\<close>} (no separate artificial arrays), so @{term di_fst} {\isasymdots} @{term di_es} are
      the length-\<open>m + K\<close> augmented arrays.  The free outgoing ranges are the block starts
      @{term di_ob}, the edges @{term di_oe} and the range ends @{term di_oh} of Pass A, iterated with
      the cursors @{term di_oc} (likewise for the ingoing ones); the DFS stack of vertices is the array
      @{term di_stk} with the fill pointer @{term di_sp}.\<close>

record 'n dfs_imp =
  di_seen :: "bool array"          \<comment> \<open>visited flag\<close>
  di_tree :: "ndtree_impl"         \<comment> \<open>prnt / thrd / rvth / lsuc / snum (the loop's tree)\<close>
  di_par  :: "nat array"           \<comment> \<open>parent edge id\<close>
  di_dir  :: "bool array"          \<comment> \<open>parent-edge orientation\<close>
  di_pot  :: "(mtag \<times> 'n) array"   \<comment> \<open>potential\<close>
  di_fst  :: "nat array"           \<comment> \<open>augmented edge tails (fst); artificial writes at \<open>m + k\<close>\<close>
  di_snd  :: "nat array"           \<comment> \<open>augmented edge heads (snd)\<close>
  di_cap  :: "'n array"            \<comment> \<open>augmented capacities\<close>
  di_cost :: "'n array"            \<comment> \<open>edge costs (original block; the {\isasymplusminus} cost seed)\<close>
  di_flow :: "'n array"            \<comment> \<open>augmented flow\<close>
  di_es   :: "edge_tag array"      \<comment> \<open>augmented edge-state tags\<close>
  di_ob   :: "nat array"           \<comment> \<open>block starts of the outgoing CSR\<close>
  di_oe   :: "nat array"           \<comment> \<open>free outgoing ranges: edges\<close>
  di_oh   :: "nat array"           \<comment> \<open>free outgoing ranges: ends\<close>
  di_oc   :: "nat array"           \<comment> \<open>cursors into the free outgoing ranges\<close>
  di_ib   :: "nat array"           \<comment> \<open>block starts of the ingoing CSR\<close>
  di_ie   :: "nat array"           \<comment> \<open>free ingoing ranges: edges\<close>
  di_ih   :: "nat array"           \<comment> \<open>free ingoing ranges: ends\<close>
  di_ic   :: "nat array"           \<comment> \<open>cursors into the free ingoing ranges\<close>
  di_stk  :: "nat array"           \<comment> \<open>DFS stack of vertices\<close>
  di_sp   :: "nat ref"             \<comment> \<open>DFS stack fill pointer\<close>
  di_prev :: "nat ref"             \<comment> \<open>last vertex emitted in preorder\<close>
  di_nxt  :: "nat ref"             \<comment> \<open>next artificial-edge offset (id = \<open>m + di_nxt\<close>)\<close>

subsection \<open>Discovering and finishing a vertex\<close>

text \<open>Linking a vertex @{term w} into the tree: its parent @{term p}, parent edge @{term e}, orientation
      @{term d} and potential @{term pw}, and the thread after the last emitted vertex, whose successor
      @{term w} becomes.  Shared by discovering a vertex and opening a tree component.\<close>
definition tree_link_imp ::
  "'n::{heap,linordered_idom} dfs_imp \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> mtag \<times> 'n \<Rightarrow> unit Heap" where
  "tree_link_imp st w p e d pw =
     do {
       _ \<leftarrow> array_fun_upd_imp (di_seen st) w True;
       _ \<leftarrow> array_fun_upd_imp (prnt_impl (di_tree st)) w p;
       _ \<leftarrow> array_fun_upd_imp (di_par st) w e;
       _ \<leftarrow> array_fun_upd_imp (di_dir st) w d;
       _ \<leftarrow> array_fun_upd_imp (di_pot st) w pw;
       pv \<leftarrow> Ref.lookup (di_prev st);
       _ \<leftarrow> array_fun_upd_imp (thrd_impl (di_tree st)) pv w;
       _ \<leftarrow> array_fun_upd_imp (rvth_impl (di_tree st)) w pv;
       _ \<leftarrow> array_fun_upd_imp (snum_impl (di_tree st)) w 1;
       Ref.update (di_prev st) w }"

text \<open>The functional @{term dfs_discover}: finalise the fresh child @{term w} reached from @{term v}
      across free real edge @{term e} --- seed its tree fields, thread-link it after the last emitted
      vertex, give @{term e} zero reduced cost (\<open>\<plusminus> cost\<close> by whether @{term v} is @{term e}'s tail), and
      push it, resetting its two cursors.\<close>
definition dfs_discover_imp :: "'n::{heap,linordered_idom} dfs_imp \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "dfs_discover_imp st v w e =
     do {
       fe \<leftarrow> Array.nth (di_fst st) e;
       ce \<leftarrow> Array.nth (di_cost st) e;
       potv \<leftarrow> Array.nth (di_pot st) v;
       _ \<leftarrow> tree_link_imp st w v e (fe = w) (pval_plus potv (M_0, if v = fe then ce else - ce));
       sp \<leftarrow> Ref.lookup (di_sp st);
       _ \<leftarrow> array_fun_upd_imp (di_stk st) sp w;
       _ \<leftarrow> Ref.update (di_sp st) (Suc sp);
       _ \<leftarrow> csr_reset_imp (di_ob st, di_oe st, di_oc st) w;
       csr_reset_imp (di_ib st, di_ie st, di_ic st) w }"

text \<open>The functional @{term dfs_finish}: on popping @{term v} (post-order) the last vertex emitted is
      its rightmost descendant, so it is @{term v}'s \<open>lsuc\<close>; add @{term v}'s completed subtree size to
      its parent's and pop it.\<close>
definition dfs_finish_imp :: "'n::{heap,linordered_idom} dfs_imp \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "dfs_finish_imp st v =
     do { p \<leftarrow> Array.nth (prnt_impl (di_tree st)) v;
          pv \<leftarrow> Ref.lookup (di_prev st);
          _ \<leftarrow> array_fun_upd_imp (lsuc_impl (di_tree st)) v pv;
          snp \<leftarrow> Array.nth (snum_impl (di_tree st)) p;
          snv \<leftarrow> Array.nth (snum_impl (di_tree st)) v;
          _ \<leftarrow> array_fun_upd_imp (snum_impl (di_tree st)) p (snp + snv);
          sp \<leftarrow> Ref.lookup (di_sp st);
          Ref.update (di_sp st) (sp - 1) }"

subsection \<open>The depth-first traversal\<close>

text \<open>The functional @{term build_dfs_a}: at the stack top @{term v} take one step of the iterator over
      the free outgoing range, else of the iterator over the free ingoing range
      (@{const csr_step_upto_imp}), recursing after discovering an unseen neighbour; when both ranges
      are exhausted, finish the vertex.  The neighbour across an outgoing edge @{term e} is
      @{term \<open>snd_list ! e\<close>}, across an ingoing edge @{term \<open>fst_list ! e\<close>}.\<close>
partial_function (heap) build_dfs_a_imp ::
  "'n::{heap,linordered_idom} dfs_imp \<Rightarrow> unit Heap" where
  "build_dfs_a_imp st =
     do {
       sp \<leftarrow> Ref.lookup (di_sp st);
       (if sp = 0 then return ()
        else do {
          v \<leftarrow> Array.nth (di_stk st) (sp - 1);
          csr_step_upto_imp (di_ob st, di_oe st, di_oc st) (di_oh st) v
            (\<lambda>e. do {
               w \<leftarrow> Array.nth (di_snd st) e;
               sw \<leftarrow> Array.nth (di_seen st) w;
               _ \<leftarrow> (if sw then return () else dfs_discover_imp st v w e);
               build_dfs_a_imp st })
            (csr_step_upto_imp (di_ib st, di_ie st, di_ic st) (di_ih st) v
               (\<lambda>e. do {
                  w \<leftarrow> Array.nth (di_fst st) e;
                  sw \<leftarrow> Array.nth (di_seen st) w;
                  _ \<leftarrow> (if sw then return () else dfs_discover_imp st v w e);
                  build_dfs_a_imp st })
               (do { _ \<leftarrow> dfs_finish_imp st v; build_dfs_a_imp st })) }) }"

subsection \<open>Opening tree components and emitting artificial edges\<close>

text \<open>Writing an artificial edge --- tail, head, capacity, flow and tag --- at index @{term aidx} of
      the augmented arrays.  Shared by opening a tree component and emitting a @{term U} edge.\<close>
definition art_edge_imp ::
  "'n::{heap,linordered_idom} dfs_imp \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> edge_tag \<Rightarrow> unit Heap" where
  "art_edge_imp st aidx x y u f tag =
     do {
       _ \<leftarrow> array_fun_upd_imp (di_fst st) aidx x;
       _ \<leftarrow> array_fun_upd_imp (di_snd st) aidx y;
       _ \<leftarrow> array_fun_upd_imp (di_cap st) aidx u;
       _ \<leftarrow> array_fun_upd_imp (di_flow st) aidx f;
       array_fun_upd_imp (di_es st) aidx tag }"

text \<open>The functional @{term open_tree_component}: open an unseen imbalanced (Phase 1) or balanced
      (Phase 2) vertex @{term c} as a child of the root.  Emit @{term c}'s \<^emph>\<open>tree\<close> artificial edge ---
      written directly into the augmented arrays at index @{term \<open>m + k\<close>} and tagged @{const InTree} ---
      finalise @{term c}'s tree fields, seed its potential to \<open>\<plusminus> M\<close>, thread-link it, push it on the
      empty stack, then drain its subtree with @{const build_dfs_a_imp}.  Orientation / flow / capacity
      come from the one @{term \<open>imb_arr ! c\<close>} read (the imbalance array): up (\<open>c \<rightarrow> root\<close>) iff
      @{term \<open>0 \<le> imb\<close>}, flow @{term \<open>\<bar>imb\<bar>\<close>}, a tree edge getting a \<open>+ 1\<close> slack toward the root when it
      points up.\<close>
definition open_tree_component_imp ::
  "'n::{heap,linordered_idom} dfs_imp \<Rightarrow> 'n array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "open_tree_component_imp st imb_arr m vcount c =
     do {
       imb \<leftarrow> Array.nth imb_arr c;
       nxt \<leftarrow> Ref.lookup (di_nxt st);
       (let up = 0 \<le> imb; af = \<bar>imb\<bar>; aidx = m + nxt
        in do {
          _ \<leftarrow> art_edge_imp st aidx (if up then c else vcount) (if up then vcount else c)
                 (if up then af + 1 else af) af InTree;
          _ \<leftarrow> Ref.update (di_nxt st) (Suc nxt);
          _ \<leftarrow> tree_link_imp st c vcount aidx up (if up then pval_negM else pval_M);
          _ \<leftarrow> array_fun_upd_imp (di_stk st) 0 c;
          _ \<leftarrow> Ref.update (di_sp st) 1;
          _ \<leftarrow> csr_reset_imp (di_ob st, di_oe st, di_oc st) c;
          _ \<leftarrow> csr_reset_imp (di_ib st, di_ie st, di_ic st) c;
          build_dfs_a_imp st }) }"

text \<open>The functional @{term emit_U_edge}: a \<^emph>\<open>saturated\<close> @{term U} artificial edge for an already-seen
      imbalanced vertex @{term v} --- capacity equal to its flow @{term \<open>\<bar>imb\<bar>\<close>}, tagged @{const InU},
      touching no tree field.\<close>
definition emit_U_edge_imp ::
  "'n::{heap,linordered_idom} dfs_imp \<Rightarrow> 'n array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "emit_U_edge_imp st imb_arr m vcount v =
     do {
       imb \<leftarrow> Array.nth imb_arr v;
       nxt \<leftarrow> Ref.lookup (di_nxt st);
       (let up = 0 \<le> imb; fl = \<bar>imb\<bar>
        in do {
          _ \<leftarrow> art_edge_imp st (m + nxt) (if up then v else vcount) (if up then vcount else v) fl fl InU;
          Ref.update (di_nxt st) (Suc nxt) }) }"

subsection \<open>The two vertex scans\<close>

text \<open>The functional @{term phase1_step}: an imbalanced unseen vertex opens its tree component, an
      imbalanced already-seen vertex emits a saturated @{term U} edge, a balanced vertex is skipped.\<close>
definition phase1_step_imp ::
  "'n::{heap,linordered_idom} dfs_imp \<Rightarrow> 'n array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "phase1_step_imp st imb_arr m vcount v =
     do { imb \<leftarrow> Array.nth imb_arr v;
          (if imb = 0 then return ()
           else do { sv \<leftarrow> Array.nth (di_seen st) v;
                     (if sv then emit_U_edge_imp st imb_arr m vcount v
                      else open_tree_component_imp st imb_arr m vcount v) }) }"

text \<open>@{term phase1}: the fused first scan of the vertices @{term \<open>vs_list = [1..n]\<close>}.\<close>
partial_function (heap) phase1_imp ::
  "'n::{heap,linordered_idom} dfs_imp \<Rightarrow> 'n array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "phase1_imp st imb_arr m vcount v n =
     (if n < v then return ()
      else do { _ \<leftarrow> phase1_step_imp st imb_arr m vcount v;
                phase1_imp st imb_arr m vcount (Suc v) n })"

text \<open>The functional @{term phase2_step}: open every still-unseen, \<^emph>\<open>non-lonely\<close> (hence balanced)
      vertex as a flow-0 tree component.  A vertex is lonely when it is an endpoint of no edge --- its
      blocks in both CSRs are empty (@{const csr_empty_imp}).\<close>
definition phase2_step_imp ::
  "'n::{heap,linordered_idom} dfs_imp \<Rightarrow> 'n array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "phase2_step_imp st imb_arr m vcount v =
     do { sv \<leftarrow> Array.nth (di_seen st) v;
          (if sv then return ()
           else do { eo \<leftarrow> csr_empty_imp (di_ob st) v; ei \<leftarrow> csr_empty_imp (di_ib st) v;
                     (if eo \<and> ei then return ()
                      else open_tree_component_imp st imb_arr m vcount v) }) }"

text \<open>@{term phase2}: the second scan opening every remaining balanced vertex.\<close>
partial_function (heap) phase2_imp ::
  "'n::{heap,linordered_idom} dfs_imp \<Rightarrow> 'n array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "phase2_imp st imb_arr m vcount v n =
     (if n < v then return ()
      else do { _ \<leftarrow> phase2_step_imp st imb_arr m vcount v;
                phase2_imp st imb_arr m vcount (Suc v) n })"

subsection \<open>The finished builder\<close>

text \<open>The functional @{term build_tree}: seed the root (subtree size @{term 1}, last-emitted vertex the
      root @{term vcount}, empty stack, no artificial edges yet), run both phases, then the one root
      finalisation the traversal cannot do per-frame --- the root is never popped, so its \<open>lsuc\<close>
      (rightmost descendant of the whole tree) is the final last-emitted vertex.  The vertex-indexed
      arrays are assumed freshly zeroed by the orchestrator (parents / edges / thread pointers @{term 0},
      directions @{term False}, potentials @{const pval_zero}, sizes @{term 0}); this seeds only the
      root-specific cells and the three references.\<close>
definition build_tree_imp ::
  "'n::{heap,linordered_idom} dfs_imp \<Rightarrow> 'n array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "build_tree_imp st imb_arr m vcount n =
     do {
       _ \<leftarrow> array_fun_upd_imp (snum_impl (di_tree st)) vcount 1;
       _ \<leftarrow> Ref.update (di_prev st) vcount;
       _ \<leftarrow> Ref.update (di_nxt st) 0;
       _ \<leftarrow> Ref.update (di_sp st) 0;
       _ \<leftarrow> phase1_imp st imb_arr m vcount 1 n;
       _ \<leftarrow> phase2_imp st imb_arr m vcount 1 n;
       pv \<leftarrow> Ref.lookup (di_prev st);
       array_fun_upd_imp (lsuc_impl (di_tree st)) vcount pv }"

section \<open>Generic array loops\<close>

text \<open>Fill a prefix of an array with a constant (used to clear the seen array before reuse).\<close>
partial_function (heap) arr_fill_imp :: "'a::heap array \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "arr_fill_imp a x v nn =
     (if nn \<le> v then return () else do { _ \<leftarrow> array_fun_upd_imp a v x; arr_fill_imp a x (Suc v) nn })"

text \<open>Copy a prefix of one array into another (used to reset the cursor array to the block starts).\<close>
partial_function (heap) arr_copy_imp :: "'a::heap array \<Rightarrow> 'a array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "arr_copy_imp src dst v nn =
     (if nn \<le> v then return ()
      else do { x \<leftarrow> Array.nth src v; _ \<leftarrow> array_fun_upd_imp dst v x; arr_copy_imp src dst (Suc v) nn })"

subsection \<open>Refinement rules for the generic array loops\<close>

text \<open>A single in-place write refines a list update; @{const arr_fill_imp} and @{const arr_copy_imp}
      then refine the corresponding range operations on the abstract list.\<close>

lemma array_fun_upd_imp_list_rule [sep_heap_rules]:
  "i < length xs \<Longrightarrow> <a \<mapsto>\<^sub>a xs> array_fun_upd_imp a i x <\<lambda>_. a \<mapsto>\<^sub>a list_update xs i x>"
  unfolding array_fun_upd_imp_def by sep_auto

lemma arr_fill_imp_rule:
  "v \<le> nn \<Longrightarrow> nn \<le> length xs \<Longrightarrow>
   <a \<mapsto>\<^sub>a xs> arr_fill_imp a x v nn
   <\<lambda>_. a \<mapsto>\<^sub>a (take v xs @ replicate (nn - v) x @ drop nn xs)>"
proof (induction "nn - v" arbitrary: v xs)
  case 0
  then have "nn = v" by simp
  then show ?case by (subst arr_fill_imp.simps) sep_auto
next
  case (Suc d)
  from Suc.hyps(2) Suc.prems have vn: "v < nn" by simp
  have d': "d = nn - Suc v" using Suc.hyps(2) by simp
  have len': "nn \<le> length (list_update xs v x)" using Suc.prems by simp
  have step: "<a \<mapsto>\<^sub>a list_update xs v x> arr_fill_imp a x (Suc v) nn
              <\<lambda>_. a \<mapsto>\<^sub>a (take (Suc v) (list_update xs v x) @ replicate (nn - Suc v) x @ drop nn (list_update xs v x))>"
    using Suc.hyps(1)[OF d' _ len'] vn by simp
  have eq: "(take (Suc v) xs)[v := x] @ replicate (nn - Suc v) x @ drop nn xs
            = take v xs @ replicate (nn - v) x @ drop nn xs"
  proof -
    have a: "(take (Suc v) xs)[v := x] = take v xs @ [x]"
      using vn Suc.prems(2) by (simp add: take_Suc_conv_app_nth list_update_append)
    have c: "replicate (nn - v) x = x # replicate (nn - Suc v) x"
      by (simp add: Suc_diff_Suc[OF vn, symmetric])
    show ?thesis by (simp only: a c append.assoc append_Cons append_Nil)
  qed
  show ?case
    using vn Suc.prems(2)
    apply (subst arr_fill_imp.simps)
    by (sep_auto heap: step simp: eq)
qed

lemma arr_copy_imp_rule:
  "v \<le> nn \<Longrightarrow> nn \<le> length xs \<Longrightarrow> nn \<le> length ys \<Longrightarrow>
   <src \<mapsto>\<^sub>a xs * dst \<mapsto>\<^sub>a ys> arr_copy_imp src dst v nn
   <\<lambda>_. src \<mapsto>\<^sub>a xs * dst \<mapsto>\<^sub>a (take v ys @ take (nn - v) (drop v xs) @ drop nn ys)>"
proof (induction "nn - v" arbitrary: v ys)
  case 0
  then have "nn = v" by simp
  then show ?case by (subst arr_copy_imp.simps) sep_auto
next
  case (Suc d)
  from Suc.hyps(2) Suc.prems have vn: "v < nn" by simp
  have vx: "v < length xs" using vn Suc.prems(2) by simp
  have d': "d = nn - Suc v" using Suc.hyps(2) by simp
  have lenys': "nn \<le> length (list_update ys v (xs ! v))" using Suc.prems(3) by simp
  have step: "<src \<mapsto>\<^sub>a xs * dst \<mapsto>\<^sub>a list_update ys v (xs ! v)> arr_copy_imp src dst (Suc v) nn
              <\<lambda>_. src \<mapsto>\<^sub>a xs * dst \<mapsto>\<^sub>a (take (Suc v) (list_update ys v (xs ! v))
                        @ take (nn - Suc v) (drop (Suc v) xs) @ drop nn (list_update ys v (xs ! v)))>"
    using Suc.hyps(1)[OF d' _ Suc.prems(2) lenys'] vn by simp
  have eq: "(take (Suc v) ys)[v := xs ! v] @ take (nn - Suc v) (drop (Suc v) xs) @ drop nn ys
            = take v ys @ take (nn - v) (drop v xs) @ drop nn ys"
  proof -
    have a: "(take (Suc v) ys)[v := xs ! v] = take v ys @ [xs ! v]"
      using vn Suc.prems(3) by (simp add: take_Suc_conv_app_nth list_update_append)
    have c: "take (nn - v) (drop v xs) = xs ! v # take (nn - Suc v) (drop (Suc v) xs)"
      by (simp only: Cons_nth_drop_Suc[OF vx, symmetric] Suc_diff_Suc[OF vn, symmetric] take_Suc_Cons)
    show ?thesis by (simp only: a c append.assoc append_Cons append_Nil)
  qed
  show ?case
    using vn Suc.prems(2,3)
    apply (subst arr_copy_imp.simps)
    by (sep_auto heap: step simp: eq)
qed

section \<open>The edged vertices\<close>

text \<open>The imperative counterpart of the functional @{const initial_basis_code_spec.edged_vs_list}: the
      dense vertex range @{term \<open>[1..n]\<close>} with the \<^emph>\<open>lonely\<close> names (endpoints of no edge --- both
      blocks empty, @{const csr_empty_imp}) removed.  The acyclifier iterates exactly these.  We count
      them, then fill an exactly-sized array (so the iterator's length matches the abstraction).\<close>
partial_function (heap) count_edged_imp :: "nat array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "count_edged_imp ob ib v n acc =
     (if n < v then return acc
      else do { eo \<leftarrow> csr_empty_imp ob v; ei \<leftarrow> csr_empty_imp ib v;
                count_edged_imp ob ib (Suc v) n (if eo \<and> ei then acc else Suc acc) })"

partial_function (heap) fill_edged_imp ::
  "nat array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "fill_edged_imp vl ob ib v n j =
     (if n < v then return ()
      else do { eo \<leftarrow> csr_empty_imp ob v; ei \<leftarrow> csr_empty_imp ib v;
                (if eo \<and> ei then fill_edged_imp vl ob ib (Suc v) n j
                 else do { _ \<leftarrow> array_fun_upd_imp vl j v; fill_edged_imp vl ob ib (Suc v) n (Suc j) }) })"

section \<open>The orchestrator\<close>

text \<open>The imperative refinement of the functional orchestrator @{const initial_basis_code_spec.solve}.
      All working arrays are allocated \<^emph>\<open>once\<close> here and threaded through the phases, reusing memory
      wherever the functional code does: the two CSRs of the input are built once by the shared
      builder (@{const csr_build_into_edges}, @{const csr_build_into_edges_tgt}); the acyclifier
      iterates them with the cursor arrays @{term o_h} / @{term i_h}, which then become the ends of
      the free ranges that Pass A appends to the edge arrays in place; the acyclifier's DFS stacks
      @{term vst} / @{term est} are handed on as the tree-builder's stack and then as the
      network-simplex path buffers.  The augmented endpoint / capacity / flow / edge-state arrays
      have length @{term \<open>m + n\<close>} (the artificial-edge count @{term Kart} is at most @{term n});
      their first @{term m} cells are copied from the input.

      The phases: build the CSRs; acyclify the flow (an @{term unbounded} answer is a negative
      infinite-capacity cycle, @{term NegInfCycleF}); reset the range ends and run Pass A + the
      imbalance transform; build the strongly-feasible spanning tree; run the network-simplex loop
      (an @{term unbounded} verdict is again @{term NegInfCycleF}); on a bounded optimum inspect the
      artificial edges @{term \<open>[m..<m + Kart]\<close>} --- all-zero means the minimum-cost @{term b}-flow is
      left in the first @{term m} flow cells (@{term OptimalF}), otherwise the instance is infeasible
      (@{term InfeasibleF}).\<close>
definition solve_imp ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat
   \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> 'n::{heap,linordered_idom} array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array
   \<Rightarrow> solve_status Heap" where
  "solve_imp n m block_size min_cand max_cand in_fst in_snd in_cap in_cost in_flow in_b =
     (let vcount = Suc n; V = Suc vcount; mn = m + n
      in do {
        fst_arr  \<leftarrow> Array.new mn 0;   _ \<leftarrow> arr_copy_imp in_fst  fst_arr  0 m;
        snd_arr  \<leftarrow> Array.new mn 0;   _ \<leftarrow> arr_copy_imp in_snd  snd_arr  0 m;
        cap_arr  \<leftarrow> Array.new mn 0;   _ \<leftarrow> arr_copy_imp in_cap  cap_arr  0 m;
        flow_arr \<leftarrow> Array.new mn 0;   _ \<leftarrow> arr_copy_imp in_flow flow_arr 0 m;
        es_arr   \<leftarrow> Array.new mn InL;
        pot_arr \<leftarrow> Array.new V pval_zero;
        prnt \<leftarrow> Array.new V 0; thrd \<leftarrow> Array.new V 0; rvth \<leftarrow> Array.new V 0;
        lsuc \<leftarrow> Array.new V 0; snum \<leftarrow> Array.new V 0; aux \<leftarrow> Array.new V 0;
        par \<leftarrow> Array.new V 0; dir \<leftarrow> Array.new V False;
        state_arr \<leftarrow> Array.new V Unseen; exc_arr \<leftarrow> Array.new V 0;
        o_b \<leftarrow> Array.new V 0; o_e \<leftarrow> Array.new m 0; o_h \<leftarrow> Array.new vcount 0; o_c \<leftarrow> Array.new vcount 0;
        i_b \<leftarrow> Array.new V 0; i_e \<leftarrow> Array.new m 0; i_h \<leftarrow> Array.new vcount 0; i_c \<leftarrow> Array.new vcount 0;
        vst \<leftarrow> Array.new V 0; est \<leftarrow> Array.new V 0; dst \<leftarrow> Array.new V False;
        _ \<leftarrow> csr_build_into_edges vcount (in_fst, in_snd) 0 o_b o_e;
        _ \<leftarrow> csr_build_into_edges_tgt vcount (in_fst, in_snd) 0 i_b i_e;
        _ \<leftarrow> csr_copy_imp vcount o_b o_h 0;
        _ \<leftarrow> csr_copy_imp vcount i_b i_h 0;
        k \<leftarrow> count_edged_imp o_b i_b 1 n 0;
        vl \<leftarrow> Array.new k 0;
        _ \<leftarrow> fill_edged_imp vl o_b i_b 1 n 0;
        pr \<leftarrow> ref 0;
        ubd \<leftarrow> make_acyclic_prog cap_arr in_cost fst_arr snd_arr flow_arr state_arr
                (o_b, o_e, o_h) (i_b, i_e, i_h) (vl, pr) vst est dst;
        (if ubd then return NegInfCycleF
         else do {
           _ \<leftarrow> csr_copy_imp vcount o_b o_h 0;
           _ \<leftarrow> csr_copy_imp vcount i_b i_h 0;
           _ \<leftarrow> passA_imp flow_arr cap_arr fst_arr snd_arr es_arr exc_arr o_e o_h i_e i_h 0 m;
           _ \<leftarrow> imbalance_imp exc_arr in_b 0 vcount;
           \<comment> \<open>Reuse the acyclifier's (now dead) DFS stack @{term dst} as the tree-builder's ``seen''
              array; it must be all-@{term False} for the build.\<close>
           _ \<leftarrow> arr_fill_imp dst False 0 V;
           sp_ref \<leftarrow> ref 0; prev_ref \<leftarrow> ref 0; nxt_ref \<leftarrow> ref 0;
           (let tree = \<lparr> prnt_impl = prnt, thrd_impl = thrd, rvth_impl = rvth,
                         lsuc_impl = lsuc, snum_impl = snum, aux_impl = aux \<rparr>;
                st = \<lparr> di_seen = dst, di_tree = tree, di_par = par, di_dir = dir, di_pot = pot_arr,
                      di_fst = fst_arr, di_snd = snd_arr, di_cap = cap_arr, di_cost = in_cost,
                      di_flow = flow_arr, di_es = es_arr,
                      di_ob = o_b, di_oe = o_e, di_oh = o_h, di_oc = o_c,
                      di_ib = i_b, di_ie = i_e, di_ih = i_h, di_ic = i_c,
                      di_stk = vst, di_sp = sp_ref, di_prev = prev_ref, di_nxt = nxt_ref \<rparr>
            in do {
              _ \<leftarrow> build_tree_imp st exc_arr m vcount n;
              Kart \<leftarrow> Ref.lookup nxt_ref;
              (let marc = m + Kart
               in do {
                 sel_arr \<leftarrow> Array.new max_cand 0; scur \<leftarrow> ref 0; slen \<leftarrow> ref 0;
                 (let state = ns_impl_state.make flow_arr pot_arr tree par dir es_arr
                                (sel_arr, scur, slen) vst est
                  in do {
                    res \<leftarrow> ns_loop_prog vcount m marc block_size min_cand max_cand
                                        fst_arr snd_arr in_cost cap_arr state;
                    (if res = Network_Simplex.unbounded then return NegInfCycleF
                     else do {
                       allz \<leftarrow> scan_art_imp flow_arr m marc;
                       (if allz
                        then do { _ \<leftarrow> arr_copy_imp flow_arr in_flow 0 m; return OptimalF }
                        else return InfeasibleF) }) }) }) }) }) })"

section \<open>Code generation for the whole solver\<close>

text \<open>Register the fixpoint equations of every recursive Heap sub-program the solver reaches: the
      materialisation loops of this theory, the abstract network-simplex loop of
      @{locale network_simplex_impl_spec}, and the arborescence-refinement loops.  The acyclifier's
      equations were registered above, the CSR builder's in the library.  With these,
      @{const solve_imp} generates as self-contained imperative SML.\<close>

lemmas [code] =
  ns_loop_prog_def
  scan_art_imp.simps join_of_imp.simps scan_cache_imp.simps scan_imp.simps
  passA_imp.simps imbalance_imp.simps build_dfs_a_imp.simps phase1_imp.simps phase2_imp.simps
  arr_fill_imp.simps arr_copy_imp.simps count_edged_imp.simps fill_edged_imp.simps
  initial_basis_code_spec.better.simps
  network_simplex_impl_spec.ns_select_imp_def network_simplex_impl_spec.res_fwd_imp_def
  network_simplex_impl_spec.res_bwd_imp_def network_simplex_impl_spec.par_edge_imp_def
  network_simplex_impl_spec.par_up_imp_def network_simplex_impl_spec.res_up_imp_def
  network_simplex_impl_spec.res_down_imp_def network_simplex_impl_spec.mininf_imp_def
  network_simplex_impl_spec.scan_up_loop_imp.simps network_simplex_impl_spec.scan_down_loop_imp.simps
  network_simplex_impl_spec.scan_up_imp_def network_simplex_impl_spec.scan_down_imp_def
  network_simplex_impl_spec.bottleneck_imp_def network_simplex_impl_spec.aug_loop_imp.simps
  network_simplex_impl_spec.augment_flow_imp_def network_simplex_impl_spec.ns_flip_imp_def
  network_simplex_impl_spec.reparent_walk_imp.simps network_simplex_impl_spec.reparent_imp_def
  network_simplex_impl_spec.ns_pivot_imp_def network_simplex_impl_spec.ns_loop_imp.simps
  stem_loop_imp.simps dirty_pass_imp.simps stem_num_loop_imp.simps
  fused_vin_loop_imp.simps fused_vout_loop_imp.simps join_paths_loop_imp.simps subtree_fold_imp.simps

export_code solve_imp checking SML_imp

section \<open>Correctness of the imperative orchestrator\<close>

text \<open>The functional selector locale @{locale initial_basis_selector} fixes its value type only as
      @{class linordered_idom}, but the imperative @{const solve_imp} stores those values in
      @{typ \<open>'n array\<close>}s, which additionally requires @{class heap}.  A locale's fixed type parameter
      cannot be re-sorted after the fact, so we introduce the thin extension
      \<open>initial_basis_selector_heap\<close>: it \<^emph>\<open>is\<close> @{locale initial_basis_selector} --- inheriting
      \<open>solve\<close>, @{thm [source] initial_basis_selector.solve_correct} and all the input lists ---
      but re-declares @{typ 'n} at the stronger sort @{class heap} {\isasyminter} @{class linordered_idom}.  All of
      this lives in the present theory; the functional development is untouched.

      Inside it the final refinement statement is a single Hoare triple: run on six input arrays
      holding the locale-fixed input lists, @{const solve_imp} returns the same verdict as the
      functional \<open>solve\<close> (under @{const status_of}), leaves the five read-only input arrays
      untouched, and --- on @{const OptimalF} --- leaves the minimum-cost @{term b}-flow in the first
      @{term m} cells of the flow array.  Composed with @{thm [source] initial_basis_selector.solve_correct}
      it certifies the executable solver end-to-end.\<close>

locale initial_basis_selector_heap =
  initial_basis_selector where capacity_list = capacity_list and h = h
  for capacity_list :: "('n :: {heap, linordered_idom}) list" and h :: "'n \<Rightarrow> real"
begin

text \<open>The two CSRs of the input as imperative collections (@{locale csr_edge_input}): the keys are
      read from the endpoint arrays.\<close>

sublocale outI: csr_edge_input vcount fst_list snd_list "e_src fst_list" src_imp
  by (intro csr_edge_input.intro out.csr_edge_spec_axioms csr_edge_input_axioms.intro)
     (use src_imp_rule[of _ fst_list snd_list] in auto)

sublocale incI: csr_edge_input vcount fst_list snd_list "e_tgt fst_list snd_list" tgt_imp
  by (intro csr_edge_input.intro inc.csr_edge_spec_axioms csr_edge_input_axioms.intro)
     (use tgt_imp_rule[of _ fst_list snd_list] length_snd length_fst in auto)

subsection \<open>Layer (c): the imperative acyclifier refines @{const make_acyclic}\<close>

text \<open>The concrete assertions relating the functional stores to their imperative arrays.  The flow and
      vertex-state arrays are over-allocated (the flow array carries @{term n} spare artificial-edge
      cells, the state array one spare root cell), so the assertions pad the abstract list with an
      existential remainder.  The two edge iterators are the library CSR collections.\<close>

definition flow_assn_m :: "'n list \<Rightarrow> 'n array \<Rightarrow> assn" where
  "flow_assn_m fl ha = (\<exists>\<^sub>A r. ha \<mapsto>\<^sub>a (fl @ r) * \<up>(length r = n))"

definition state_assn_v :: "vertex_state list \<Rightarrow> vertex_state array \<Rightarrow> assn" where
  "state_assn_v st ha = (\<exists>\<^sub>A r. ha \<mapsto>\<^sub>a (st @ r) * \<up>(length r = Suc 0))"

text \<open>The per-operation Hoare triples of the stores, for the concrete arrays; the edge iterators
      and the vertex iterator are discharged by the library rules.\<close>

lemma flow_lookup_rule_c:
  "\<lbrakk>length Fl = m; e \<in> {0..<m}\<rbrakk> \<Longrightarrow>
   <flow_assn_m Fl fh> Array.nth fh e <\<lambda>r. flow_assn_m Fl fh * \<up>(r = Fl ! e)>"
  unfolding flow_assn_m_def by (sep_auto simp: nth_append)

lemma flow_upd_rule_c:
  "\<lbrakk>length Fl = m; e \<in> {0..<m}\<rbrakk> \<Longrightarrow>
   <flow_assn_m Fl fh> array_fun_upd_imp fh e w <\<lambda>_. flow_assn_m (Fl[e := w]) fh>"
  unfolding flow_assn_m_def array_fun_upd_imp_def by (sep_auto simp: list_update_append)

lemma state_lookup_rule_c:
  "\<lbrakk>\<forall>v\<in>original_network.\<V>. v < length St; v \<in> original_network.\<V>\<rbrakk> \<Longrightarrow>
   <state_assn_v St sh> Array.nth sh v <\<lambda>r. state_assn_v St sh * \<up>(r = St ! v)>"
  unfolding state_assn_v_def by (sep_auto simp: nth_append)

lemma state_upd_rule_c:
  "\<lbrakk>\<forall>v\<in>original_network.\<V>. v < length St; v \<in> original_network.\<V>\<rbrakk> \<Longrightarrow>
   <state_assn_v St sh> array_fun_upd_imp sh v q <\<lambda>_. state_assn_v (St[v := q]) sh>"
  unfolding state_assn_v_def array_fun_upd_imp_def by (sep_auto simp: list_update_append)


text \<open>\<^emph>\<open>Layer (c) target.\<close>  Interpreting the acyclifier refinement proof locale at the concrete
      operations turns @{thm [source] acyclic_flow_impl_refine_proof.make_acyclic_imp_rule} into a
      Hoare triple for the executable @{const make_acyclic_prog}: it leaves the flow array holding
      the functional @{const make_acyclic} result and returns @{term True} exactly on the unbounded
      (@{term None}) verdict; the two CSR collections are returned with some cursors.\<close>
lemma make_acyclic_prog_rule:
  fixes cap_arr cost_arr :: "'n array" and fst_arr snd_arr :: "nat array"
    and fh :: "'n array" and sh :: "vertex_state array"
    and oh ih :: "nat array \<times> nat array \<times> nat array"
    and vih :: "nat list_cursor_imp" and vst est :: "nat array" and dst :: "bool array"
    and cl co :: "'n list" and fla sla :: "nat list" and f0 :: "'n list"
    and vs0 es0 :: "nat list" and ds0 :: "bool list"
  assumes cl_len: "m \<le> length cl" and cl_eq: "\<And>e. e < m \<Longrightarrow> cl ! e = capacity_list ! e"
      and co_len: "m \<le> length co" and co_eq: "\<And>e. e < m \<Longrightarrow> co ! e = cost_list ! e"
      and fla_len: "m \<le> length fla" and fla_eq: "\<And>e. e < m \<Longrightarrow> fla ! e = fst_list ! e"
      and sla_len: "m \<le> length sla" and sla_eq: "\<And>e. e < m \<Longrightarrow> sla ! e = snd_list ! e"
      and ff: "length f0 = m" and feas: "af_cap_feasible f0"
      and cvs: "card original_network.\<V> \<le> length vs0"
      and ces: "card original_network.\<V> \<le> length es0"
      and cds: "card original_network.\<V> \<le> length ds0"
  shows "<flow_assn_m f0 fh * state_assn_v (replicate vcount Unseen) sh *
          outI.graph.csr_assn ((!) out.inp.B_spec) oh * incI.graph.csr_assn ((!) inc.inp.B_spec) ih *
          lc_assn \<lparr>lc_list = edged_vs_list, lc_pos = 0\<rparr> vih *
          (cap_arr \<mapsto>\<^sub>a cl * cost_arr \<mapsto>\<^sub>a co * fst_arr \<mapsto>\<^sub>a fla * snd_arr \<mapsto>\<^sub>a sla) *
          vst \<mapsto>\<^sub>a vs0 * est \<mapsto>\<^sub>a es0 * dst \<mapsto>\<^sub>a ds0>
         make_acyclic_prog cap_arr cost_arr fst_arr snd_arr fh sh oh ih vih vst est dst
        <\<lambda>r. \<exists>\<^sub>A f' c_o c_i. flow_assn_m f' fh *
             outI.graph.csr_assn c_o oh * incI.graph.csr_assn c_i ih *
             (cap_arr \<mapsto>\<^sub>a cl * cost_arr \<mapsto>\<^sub>a co * fst_arr \<mapsto>\<^sub>a fla * snd_arr \<mapsto>\<^sub>a sla) *
             (\<exists>\<^sub>A vl el dl. vst \<mapsto>\<^sub>a vl * est \<mapsto>\<^sub>a el * dst \<mapsto>\<^sub>a dl *
                \<up>(card original_network.\<V> \<le> length vl \<and> card original_network.\<V> \<le> length el \<and> card original_network.\<V> \<le> length dl \<and>
                  length vl = length vs0 \<and> length el = length es0 \<and> length dl = length ds0)) *
             true *
             \<up>((r \<longleftrightarrow> make_acyclic f0 = None) \<and> (make_acyclic f0 = None \<or> make_acyclic f0 = Some f'))>"
proof -
  have capr: "e \<in> {0..<m} \<Longrightarrow> <cap_arr \<mapsto>\<^sub>a cl * cost_arr \<mapsto>\<^sub>a co * fst_arr \<mapsto>\<^sub>a fla * snd_arr \<mapsto>\<^sub>a sla>
      Array.nth cap_arr e
    <\<lambda>r. (cap_arr \<mapsto>\<^sub>a cl * cost_arr \<mapsto>\<^sub>a co * fst_arr \<mapsto>\<^sub>a fla * snd_arr \<mapsto>\<^sub>a sla) * \<up>(r = capacity_list ! e)>" for e
    using cl_len cl_eq by sep_auto
  have costr: "e \<in> {0..<m} \<Longrightarrow> <cap_arr \<mapsto>\<^sub>a cl * cost_arr \<mapsto>\<^sub>a co * fst_arr \<mapsto>\<^sub>a fla * snd_arr \<mapsto>\<^sub>a sla>
      Array.nth cost_arr e
    <\<lambda>r. (cap_arr \<mapsto>\<^sub>a cl * cost_arr \<mapsto>\<^sub>a co * fst_arr \<mapsto>\<^sub>a fla * snd_arr \<mapsto>\<^sub>a sla) * \<up>(r = cost_list ! e)>" for e
    using co_len co_eq by sep_auto
  have fstr: "e \<in> {0..<m} \<Longrightarrow> <cap_arr \<mapsto>\<^sub>a cl * cost_arr \<mapsto>\<^sub>a co * fst_arr \<mapsto>\<^sub>a fla * snd_arr \<mapsto>\<^sub>a sla>
      Array.nth fst_arr e
    <\<lambda>r. (cap_arr \<mapsto>\<^sub>a cl * cost_arr \<mapsto>\<^sub>a co * fst_arr \<mapsto>\<^sub>a fla * snd_arr \<mapsto>\<^sub>a sla) * \<up>(r = fst_list ! e)>" for e
    using fla_len fla_eq by sep_auto
  have sndr: "e \<in> {0..<m} \<Longrightarrow> <cap_arr \<mapsto>\<^sub>a cl * cost_arr \<mapsto>\<^sub>a co * fst_arr \<mapsto>\<^sub>a fla * snd_arr \<mapsto>\<^sub>a sla>
      Array.nth snd_arr e
    <\<lambda>r. (cap_arr \<mapsto>\<^sub>a cl * cost_arr \<mapsto>\<^sub>a co * fst_arr \<mapsto>\<^sub>a fla * snd_arr \<mapsto>\<^sub>a sla) * \<up>(r = snd_list ! e)>" for e
    using sla_len sla_eq by sep_auto
  interpret acycR: acyclic_flow_impl_refine_proof
    where fst = "\<lambda>e. if e < m then fst_list ! e else Product_Type.fst (prod_decode (e - m))"
      and snd = "\<lambda>e. if e < m then snd_list ! e else Product_Type.snd (prod_decode (e - m))"
      and \<E> = "{0..<m}"
      and create_edge = "\<lambda>u v. m + prod_encode (u, v)"
      and \<u> = "\<lambda>e. if e < m then (if capacity_list ! e = - 1 then \<infinity> else ereal (h (capacity_list ! e))) else \<infinity>"
      and \<c> = "\<lambda>e. h (cost_list ! e)"
      and out_invar = out.graph.csr_invar and out_abstract = out.graph.csr_abstract
      and out_current = out.graph.csr_current and out_has = out.graph.csr_has
      and out_iterated = out.graph.csr_iterated and out_remaining = out.graph.csr_remaining
      and out_move = out.graph.csr_move and out_reset = out.graph.csr_reset
      and in_invar = inc.graph.csr_invar and in_abstract = inc.graph.csr_abstract
      and in_current = inc.graph.csr_current and in_has = inc.graph.csr_has
      and in_iterated = inc.graph.csr_iterated and in_remaining = inc.graph.csr_remaining
      and in_move = inc.graph.csr_move and in_reset = inc.graph.csr_reset
      and flow_invar = "\<lambda>xs. length xs = m" and flow_upd = list_update and flow_lookup = nth
      and st_invar = "\<lambda>xs. \<forall>v\<in>original_network.\<V>. v < length xs" and st_upd = list_update and st_lookup = nth
      and vit_invar = lc_invar and vit_abstract = lc_abstract and current_vertex = lc_current
      and has_vertex = lc_has and vit_iterated = lc_iterated and vit_remaining = lc_remaining
      and move_on_vertex = lc_move
      and out_arr = "(!) out.inp.B_spec" and in_arr = "(!) inc.inp.B_spec"
      and all_vertices = "\<lparr> lc_list = edged_vs_list, lc_pos = 0 \<rparr>"
      and cap = "\<lambda>e. capacity_list ! e" and cost = "\<lambda>e. cost_list ! e" and h = "h :: 'n \<Rightarrow> real"
      and state_init = "replicate vcount Unseen"
      and fst_exec = "\<lambda>e. fst_list ! e" and snd_exec = "\<lambda>e. snd_list ! e"
      and out_current_imp = csr_current_imp and out_has_imp = csr_has_imp
      and out_move_imp = csr_move_imp and out_reset_imp = csr_reset_imp
      and in_current_imp = csr_current_imp and in_has_imp = csr_has_imp
      and in_move_imp = csr_move_imp and in_reset_imp = csr_reset_imp
      and flow_upd_imp = array_fun_upd_imp and flow_lookup_imp = Array.nth
      and st_upd_imp = array_fun_upd_imp and st_lookup_imp = Array.nth
      and current_vertex_imp = lc_current_imp and has_vertex_imp = lc_has_imp
      and move_on_vertex_imp = lc_move_imp
      and cap_imp = "\<lambda>e. Array.nth cap_arr e" and cost_imp = "\<lambda>e. Array.nth cost_arr e"
      and fst_exec_imp = "\<lambda>e. Array.nth fst_arr e" and snd_exec_imp = "\<lambda>e. Array.nth snd_arr e"
      and flow_assn = flow_assn_m and state_assn = state_assn_v
      and out_assn = outI.graph.csr_assn and in_assn = incI.graph.csr_assn and vit_assn = lc_assn
      and rd = "cap_arr \<mapsto>\<^sub>a cl * cost_arr \<mapsto>\<^sub>a co * fst_arr \<mapsto>\<^sub>a fla * snd_arr \<mapsto>\<^sub>a sla"
      and Lvst = "length vs0" and Lest = "length es0" and Ldst = "length ds0"
    apply intro_locales
    apply (insert indexed_iterable_set_imp.axioms(2)[OF outI.graph.csr_imp.indexed_iterable_set_imp_axioms], simp add: verts_V)
    apply (insert indexed_iterable_set_imp.axioms(2)[OF incI.graph.csr_imp.indexed_iterable_set_imp_axioms], simp add: verts_V)
    apply (rule fixed_univ_map_basic_imp.intro; unfold id_apply; rule flow_lookup_rule_c; assumption)
    apply (rule fixed_univ_map_imp_axioms.intro; unfold id_apply; rule flow_upd_rule_c; assumption)
    apply (rule fixed_univ_map_basic_imp.intro; unfold id_apply; rule state_lookup_rule_c; assumption)
    apply (rule fixed_univ_map_imp_axioms.intro; unfold id_apply; rule state_upd_rule_c; assumption)
    apply (rule acyclic_flow_impl_refine_proof_axioms.intro)

    apply (rule lc.has_current_rule; assumption)
    apply (rule lc.current_element_rule; assumption)
    apply (rule lc.move_on_rule; assumption)
    apply (rule capr; assumption)
    apply (rule costr; assumption)
    apply (rule fstr; assumption)
    apply (rule sndr; assumption)
    done
  have vv: "lc_invar \<lparr>lc_list = edged_vs_list, lc_pos = 0\<rparr>"
    by (simp add: lc_invar_def distinct_edged_vs_list)
  have vab: "lc_abstract \<lparr>lc_list = edged_vs_list, lc_pos = 0\<rparr> \<subseteq> original_network.\<V>"
    by (simp add: lc_abstract_def V_orig_eq_edged)
  show ?thesis
    unfolding make_acyclic_prog_def
    by (rule ht_cons_post_prec[OF acycR.make_acyclic_imp_rule[OF multigraph_inv_csr ff feas vv vab cvs ces cds refl refl refl]])
       sep_auto
qed

subsection \<open>Layer (d): Pass A and the in-place imbalance transform\<close>

text \<open>Running @{const imbalance_imp} over \<open>[v..<vcount]\<close> adds each vertex's balance-array entry to its
      excess cell, exactly the functional @{const imbalance} fold.  The balance array is a parameter
      here (@{term bl}); at the call site it holds the vertex-indexed balances and the agreement
      \<open>bl ! w = b_arr ! w\<close> is supplied then.\<close>
lemma imbalance_imp_rule:
  "\<lbrakk>v \<le> vcount; vcount \<le> length exc0; \<forall>w<vcount. w < length bl\<rbrakk> \<Longrightarrow>
   <exc_arr \<mapsto>\<^sub>a exc0 * ba \<mapsto>\<^sub>a bl>
    imbalance_imp exc_arr ba v vcount
   <\<lambda>_. exc_arr \<mapsto>\<^sub>a (fold (\<lambda>w a. a[w := a ! w + bl ! w]) [v..<vcount] exc0) * ba \<mapsto>\<^sub>a bl>"
proof (induction "vcount - v" arbitrary: v exc0)
  case 0
  thus ?case by (subst imbalance_imp.simps) sep_auto
next
  case (Suc k)
  have vlt: "v < vcount" using Suc.hyps(2) by simp
  have kv: "k = vcount - Suc v" using Suc.hyps(2) by simp
  have nvcv: "\<not> vcount \<le> v" using vlt by simp
  have vex: "v < length exc0" using Suc.prems(2) vlt by simp
  have vbl: "v < length bl" using Suc.prems(3) vlt by simp
  have suc_le: "Suc v \<le> vcount" using vlt by simp
  have vc_le: "vcount \<le> length (exc0[v := exc0 ! v + bl ! v])" using Suc.prems(2) by simp
  note ih = Suc.hyps(1)[OF kv suc_le vc_le Suc.prems(3)]
  have foldeq: "fold (\<lambda>w a. a[w := a ! w + bl ! w]) [v..<vcount] exc0
              = fold (\<lambda>w a. a[w := a ! w + bl ! w]) [Suc v..<vcount] (exc0[v := exc0 ! v + bl ! v])"
    by (simp add: upt_conv_Cons[OF vlt])
  show ?case
    apply (subst imbalance_imp.simps)
    apply (simp only: if_not_P[OF nvcv])
    apply (sep_auto heap: ih simp: foldeq vex vbl)
    done
qed

text \<open>A range that holds a proper subset of its block's entries has room for one more.\<close>

lemma ranges_room:
  assumes R: "csr_ranges vcount {..<vcount} Bl ((!) Hl) E" and x: "x < vcount"
    and ab: "csr_ranges.csr_abstract Bl ((!) Hl) E c x \<subset> A"
    and A: "finite A" "card A = Bl ! Suc x - Bl ! x"
  shows "Hl ! x < length E"
proof -
  interpret R: csr_ranges vcount "{..<vcount}" Bl "(!) Hl" E by (rule R)
  have "card (R.csr_abstract c x) < card A" by (rule psubset_card_mono[OF A(1) ab])
  hence "Hl ! x - Bl ! x < Bl ! Suc x - Bl ! x" using R.csr_card_abstract[OF x] A(2) by simp
  thus ?thesis using R.H_lo[OF x] R.B_bound[OF x] by linarith
qed

text \<open>Pass A refines the functional @{const passA}: the step at edge @{term e} reads its endpoints,
      flow and capacity, writes its tag and the excess, and appends a free edge to the two free
      ranges (@{const csr_append_imp}).  The flow, capacity and endpoint arrays agree with the
      functional lists on the real edges; the edge-state array may be longer.\<close>

lemma passA_imp_rule:
  fixes fl_arr cap_arr :: "'n array" and fst_arr snd_arr :: "nat array"
    and es_arr :: "edge_tag array" and exc_arr :: "'n array"
    and oe_arr oh_arr ie_arr ih_arr :: "nat array"
    and fla cla :: "'n list" and flla slla :: "nat list"
  assumes e_le: "e \<le> m"
    and fla_len: "m \<le> length fla" and fla_eq: "\<And>i. i < m \<Longrightarrow> fla ! i = fl ! i"
    and cla_len: "m \<le> length cla" and cap_eq: "\<And>i. i < m \<Longrightarrow> cla ! i = capacity_list ! i"
    and flla_len: "m \<le> length flla" and fst_eq: "\<And>i. i < m \<Longrightarrow> flla ! i = fst_list ! i"
    and slla_len: "m \<le> length slla" and snd_eq: "\<And>i. i < m \<Longrightarrow> slla ! i = snd_list ! i"
    and s_eq: "(est, exc, fo, fi) = fold (passA_step fl) [0..<e]
                 (replicate m InL, replicate (Suc vcount) 0, (out_lo, out.inp.E_spec), (in_lo, inc.inp.E_spec))"
  shows "<fl_arr \<mapsto>\<^sub>a fla * cap_arr \<mapsto>\<^sub>a cla * fst_arr \<mapsto>\<^sub>a flla * snd_arr \<mapsto>\<^sub>a slla *
          es_arr \<mapsto>\<^sub>a (est @ esr) * exc_arr \<mapsto>\<^sub>a exc *
          oe_arr \<mapsto>\<^sub>a snd fo * oh_arr \<mapsto>\<^sub>a fst fo * ie_arr \<mapsto>\<^sub>a snd fi * ih_arr \<mapsto>\<^sub>a fst fi>
         passA_imp fl_arr cap_arr fst_arr snd_arr es_arr exc_arr oe_arr oh_arr ie_arr ih_arr e m
        <\<lambda>_. fl_arr \<mapsto>\<^sub>a fla * cap_arr \<mapsto>\<^sub>a cla * fst_arr \<mapsto>\<^sub>a flla * snd_arr \<mapsto>\<^sub>a slla *
             es_arr \<mapsto>\<^sub>a (fst (passA fl) @ esr) * exc_arr \<mapsto>\<^sub>a fst (snd (passA fl)) *
             oe_arr \<mapsto>\<^sub>a snd (free_out fl) * oh_arr \<mapsto>\<^sub>a fst (free_out fl) *
             ie_arr \<mapsto>\<^sub>a snd (free_in fl) * ih_arr \<mapsto>\<^sub>a fst (free_in fl)>"
  using e_le s_eq
proof (induction "m - e" arbitrary: e est exc fo fi)
  case 0
  have em: "e = m" using "0.hyps" "0.prems"(1) by simp
  have s0: "(est, exc, fo, fi) = passA fl" using "0.prems"(2) em by (simp add: passA_def)
  have fo: "fo = free_out fl" and fi: "fi = free_in fl"
    using s0 by (cases "passA fl", simp add: free_out_def free_in_def)+
  show ?case unfolding em fo fi by (subst passA_imp.simps) (sep_auto simp: s0[symmetric])
next
  case (Suc d)
  define init :: "edge_tag list \<times> 'n list \<times> (nat list \<times> nat list) \<times> (nat list \<times> nat list)"
    where "init = (replicate m InL, replicate (Suc vcount) 0, (out_lo, out.inp.E_spec), (in_lo, inc.inp.E_spec))"
  have em: "e < m" using Suc.hyps(2) Suc.prems(1) by simp
  have seq: "(est, exc, fo, fi) = fold (passA_step fl) [0..<e] init" using Suc.prems(2) by (simp add: init_def)
  have sz: "sized (fold (passA_step fl) xs init)" for xs
  proof (induct xs rule: rev_induct)
    case Nil show ?case by (simp add: init_def sized_def length_out_lo length_in_lo length_out_E length_in_E)
  next
    case (snoc x xs) thus ?case by (simp add: passA_step_sized)
  qed
  have lens: "length est = m" "length exc = Suc vcount" "length (fst fo) = vcount" "length (fst fi) = vcount"
    using sz[of "[0..<e]"] seq[symmetric] by (simp_all add: sized_def)
  have fo_eq: "fo = fold (\<lambda>e p. if classify fl e = InTree then csr_append (fst_list ! e) e p else p) [0..<e]
                      (out_lo, out.inp.E_spec)"
    using arg_cong[OF seq, of "\<lambda>s. fst (snd (snd s))"] by (simp add: passA_fold_fo init_def)
  have fi_eq: "fi = fold (\<lambda>e p. if classify fl e = InTree then csr_append (snd_list ! e) e p else p) [0..<e]
                      (in_lo, inc.inp.E_spec)"
    using arg_cong[OF seq, of "\<lambda>s. snd (snd (snd s))"] by (simp add: passA_fold_fi init_def)
  note OR = out_ranges_fold[OF less_imp_le[OF em], of fl, folded fo_eq]
  note IR = in_ranges_fold[OF less_imp_le[OF em], of fl, folded fi_eq]
  have xvc: "fst_list ! e < vcount" and yvc: "snd_list ! e < vcount"
    using em by (simp_all add: fst_list_lt snd_list_lt)
  have room_o: "fst fo ! (fst_list ! e) < length (snd fo)"
  proof (rule ranges_room[OF conjunct1[OF OR] xvc])
    show "csr_ranges.csr_abstract out.inp.B_spec ((!) (fst fo)) (snd fo) undefined (fst_list ! e)
          \<subset> {e'. e' < m \<and> fst_list ! e' = fst_list ! e}"
      using OR xvc em by auto
    show "card {e'. e' < m \<and> fst_list ! e' = fst_list ! e} = out.inp.B_spec ! Suc (fst_list ! e) - out.inp.B_spec ! (fst_list ! e)"
      using out.graph.csr_card_abstract[OF xvc, of undefined] out_block[OF xvc, of undefined] by simp
  qed simp
  have room_i: "fst fi ! (snd_list ! e) < length (snd fi)"
  proof (rule ranges_room[OF conjunct1[OF IR] yvc])
    show "csr_ranges.csr_abstract inc.inp.B_spec ((!) (fst fi)) (snd fi) undefined (snd_list ! e)
          \<subset> {e'. e' < m \<and> snd_list ! e' = snd_list ! e}"
      using IR yvc em by auto
    show "card {e'. e' < m \<and> snd_list ! e' = snd_list ! e} = inc.inp.B_spec ! Suc (snd_list ! e) - inc.inp.B_spec ! (snd_list ! e)"
      using inc.graph.csr_card_abstract[OF yvc, of undefined] in_block[OF yvc, of undefined] by simp
  qed simp
  define s' where "s' = passA_step fl e (est, exc, fo, fi)"
  have dse: "d = m - Suc e" using Suc.hyps(2) em by simp
  have s'eq: "(fst s', fst (snd s'), fst (snd (snd s')), snd (snd (snd s'))) =
              fold (passA_step fl) [0..<Suc e]
                (replicate m InL, replicate (Suc vcount) 0, (out_lo, out.inp.E_spec), (in_lo, inc.inp.E_spec))"
    using Suc.prems(2) by (simp add: s'_def)
  note step = Suc.hyps(1)[OF dse Suc_leI[OF em] s'eq]
  have xe: "flla ! e = fst_list ! e" and ye: "slla ! e = snd_list ! e"
    and fe: "fla ! e = fl ! e" and ue: "cla ! e = capacity_list ! e"
    using em fst_eq snd_eq fla_eq cap_eq by auto
  have st: "(if fla ! e = 0 then InL else if cla ! e \<noteq> - 1 \<and> fla ! e = cla ! e then InU else InTree) = classify fl e"
    by (simp add: classify_def fe ue)
  have es': "(est @ esr)[e := classify fl e] = fst s' @ esr"
    using lens(1) em by (simp add: s'_def passA_step_fst list_update_append)
  have exc': "fst (snd s') = exc[slla ! e := exc ! (slla ! e) + fla ! e,
                flla ! e := exc[slla ! e := exc ! (slla ! e) + fla ! e] ! (flla ! e) - fla ! e]"
    by (simp add: s'_def passA_step_exc Let_def xe ye fe)
  have fo': "fst (snd (snd s')) = (if classify fl e = InTree then csr_append (flla ! e) e fo else fo)"
    by (simp add: s'_def passA_step_fo xe)
  have fi': "snd (snd (snd s')) = (if classify fl e = InTree then csr_append (slla ! e) e fi else fi)"
    by (simp add: s'_def passA_step_fi ye)
  have eb: "e < length flla" "e < length slla" "e < length fla" "e < length cla" "e < length est + length esr"
    using em flla_len slla_len fla_len cla_len lens(1) by auto
  have xb: "flla ! e < length exc" "slla ! e < length exc" "flla ! e < length (fst fo)" "slla ! e < length (fst fi)"
    using xvc yvc lens xe ye by auto
  have nme: "\<not> m \<le> e" using em by simp
  obtain Ho Eo Hi Ei where fo_p: "fo = (Ho, Eo)" and fi_p: "fi = (Hi, Ei)" by (cases fo, cases fi)
  have xb': "flla ! e < length Ho" "slla ! e < length Hi" using xb fo_p fi_p by simp_all
  show ?case
  proof (cases "classify fl e = InTree")
    case True
    note stepT = step[unfolded es'[symmetric] exc' fo' fi' if_P[OF True], unfolded fo_p fi_p True]
    have rb: "Ho ! (flla ! e) < length Eo" "Hi ! (slla ! e) < length Ei"
      using room_o room_i xe ye fo_p fi_p by simp_all
    show ?thesis
      unfolding fo_p fi_p
      apply (subst passA_imp.simps)
      apply (simp only: nme if_False Let_def)
      apply (sep_auto heap: csr_append_imp_rule stepT simp: eb xb xb' rb st True)
      done
  next
    case False
    note stepF = step[unfolded es'[symmetric] exc' fo' fi' if_not_P[OF False], unfolded fo_p fi_p fst_conv snd_conv]
    show ?thesis
      unfolding fo_p fi_p
      apply (subst passA_imp.simps)
      apply (simp only: nme if_False Let_def)
      apply (sep_auto heap: stepF simp: eb xb st False)
      done
  qed
qed

subsection \<open>Layer (d.5): the depth-first spanning-tree builder refines @{const build_dfs}\<close>

text \<open>The free ranges of the acyclified flow, as imperative collections over all vertex names: the
      block starts of the input CSRs, the range ends and the edges Pass A wrote, and a cursor array.\<close>

sublocale FO: csr_ranges_imp vcount "{..<vcount}" out.inp.B_spec "(!) (fst (free_out acyc_flow))"
    "snd (free_out acyc_flow)"
  by (rule csr_ranges_imp.intro[OF free_out(1)])

sublocale FI: csr_ranges_imp vcount "{..<vcount}" inc.inp.B_spec "(!) (fst (free_in acyc_flow))"
    "snd (free_in acyc_flow)"
  by (rule csr_ranges_imp.intro[OF free_in(1)])

text \<open>The DFS state relation: the imperative @{typ \<open>'n dfs_imp\<close>} record of array / reference handles
      against the functional @{typ \<open>'n dfs_state\<close>}.  The augmented edge arrays @{term di_fst} /
      @{term di_snd} (and @{term di_cap} / @{term di_flow} / @{term di_es}) are wider than the real
      block, so they are existential with their real prefix pinned --- @{term di_fst} /
      @{term di_snd} to @{term fst_list} / @{term snd_list}, @{term di_cap} to @{term capacity_list},
      and @{term di_flow} / @{term di_es} to the parameters @{term fl0} / @{term es0}.  The two
      iterators are the free-range collections @{term FO} / @{term FI} with the cursor functions of
      the state; the stack of vertices is the prefix of length @{term di_sp} of the stack array, top
      last.\<close>
definition dfs_rel :: "'n list \<Rightarrow> edge_tag list \<Rightarrow> 'n dfs_imp \<Rightarrow> 'n dfs_state \<Rightarrow> assn" where
  "dfs_rel fl0 es0 st s =
     (\<exists>\<^sub>A fsta snda capa flowa esa auxa stl sp.
        FO.csr_assn (ds_oc s) (di_ob st, di_oe st, di_oc st) * di_oh st \<mapsto>\<^sub>a fst (free_out acyc_flow) *
        FI.csr_assn (ds_ic s) (di_ib st, di_ie st, di_ic st) * di_ih st \<mapsto>\<^sub>a fst (free_in acyc_flow) *
        di_seen st \<mapsto>\<^sub>a ds_seen s *
        prnt_impl (di_tree st) \<mapsto>\<^sub>a ds_prnt s *
        thrd_impl (di_tree st) \<mapsto>\<^sub>a ds_thrd s *
        rvth_impl (di_tree st) \<mapsto>\<^sub>a ds_rvth s *
        lsuc_impl (di_tree st) \<mapsto>\<^sub>a ds_lsuc s *
        snum_impl (di_tree st) \<mapsto>\<^sub>a ds_snum s *
        aux_impl (di_tree st) \<mapsto>\<^sub>a auxa *
        di_par st \<mapsto>\<^sub>a ds_par s *
        di_dir st \<mapsto>\<^sub>a ds_dir s *
        di_pot st \<mapsto>\<^sub>a ds_pot s *
        di_fst st \<mapsto>\<^sub>a fsta * di_snd st \<mapsto>\<^sub>a snda * di_cap st \<mapsto>\<^sub>a capa *
        di_cost st \<mapsto>\<^sub>a cost_list * di_flow st \<mapsto>\<^sub>a flowa * di_es st \<mapsto>\<^sub>a esa *
        di_stk st \<mapsto>\<^sub>a stl * di_sp st \<mapsto>\<^sub>r sp *
        di_prev st \<mapsto>\<^sub>r ds_prev s * di_nxt st \<mapsto>\<^sub>r ds_nxt s *
        \<up>(ds_stk s = rev (take sp stl) \<and> sp \<le> length stl \<and> length stl = Suc vcount \<and>
          m \<le> length fsta \<and> m \<le> length snda \<and>
          (\<forall>e<m. fsta ! e = fst_list ! e) \<and> (\<forall>e<m. snda ! e = snd_list ! e) \<and>
          (\<forall>e<m. flowa ! e = fl0 ! e) \<and> (\<forall>e<m. capa ! e = capacity_list ! e) \<and>
          (\<forall>e<m. esa ! e = es0 ! e) \<and> length auxa = Suc vcount \<and>
          m + length (ds_afst s) \<le> length fsta \<and> m + length (ds_asnd s) \<le> length snda \<and>
          m + length (ds_acap s) \<le> length capa \<and> m + length (ds_aflw s) \<le> length flowa \<and>
          m + length (ds_aest s) \<le> length esa \<and>
          (\<forall>k<ds_nxt s. fsta ! (m+k) = ds_afst s ! k) \<and> (\<forall>k<ds_nxt s. snda ! (m+k) = ds_asnd s ! k) \<and>
          (\<forall>k<ds_nxt s. capa ! (m+k) = ds_acap s ! k) \<and> (\<forall>k<ds_nxt s. flowa ! (m+k) = ds_aflw s ! k) \<and>
          (\<forall>k<ds_nxt s. esa ! (m+k) = ds_aest s ! k)))"

text \<open>Introducing the relation from its parts.\<close>

lemma dfs_rel_intro:
  assumes "ds_stk s = rev (take sp stl) \<and> sp \<le> length stl \<and> length stl = Suc vcount \<and>
              m \<le> length fsta \<and> m \<le> length snda \<and>
              (\<forall>e<m. fsta ! e = fst_list ! e) \<and> (\<forall>e<m. snda ! e = snd_list ! e) \<and>
              (\<forall>e<m. flowa ! e = fl0 ! e) \<and> (\<forall>e<m. capa ! e = capacity_list ! e) \<and>
              (\<forall>e<m. esa ! e = es0 ! e) \<and> length auxa = Suc vcount \<and>
              m + length (ds_afst s) \<le> length fsta \<and> m + length (ds_asnd s) \<le> length snda \<and>
              m + length (ds_acap s) \<le> length capa \<and> m + length (ds_aflw s) \<le> length flowa \<and>
              m + length (ds_aest s) \<le> length esa \<and>
              (\<forall>k<ds_nxt s. fsta ! (m+k) = ds_afst s ! k) \<and> (\<forall>k<ds_nxt s. snda ! (m+k) = ds_asnd s ! k) \<and>
              (\<forall>k<ds_nxt s. capa ! (m+k) = ds_acap s ! k) \<and> (\<forall>k<ds_nxt s. flowa ! (m+k) = ds_aflw s ! k) \<and>
              (\<forall>k<ds_nxt s. esa ! (m+k) = ds_aest s ! k)"
  shows "FO.csr_assn (ds_oc s) (di_ob st, di_oe st, di_oc st) * di_oh st \<mapsto>\<^sub>a fst (free_out acyc_flow) *
        FI.csr_assn (ds_ic s) (di_ib st, di_ie st, di_ic st) * di_ih st \<mapsto>\<^sub>a fst (free_in acyc_flow) *
        di_seen st \<mapsto>\<^sub>a ds_seen s *
        prnt_impl (di_tree st) \<mapsto>\<^sub>a ds_prnt s *
        thrd_impl (di_tree st) \<mapsto>\<^sub>a ds_thrd s *
        rvth_impl (di_tree st) \<mapsto>\<^sub>a ds_rvth s *
        lsuc_impl (di_tree st) \<mapsto>\<^sub>a ds_lsuc s *
        snum_impl (di_tree st) \<mapsto>\<^sub>a ds_snum s *
        aux_impl (di_tree st) \<mapsto>\<^sub>a auxa *
        di_par st \<mapsto>\<^sub>a ds_par s *
        di_dir st \<mapsto>\<^sub>a ds_dir s *
        di_pot st \<mapsto>\<^sub>a ds_pot s *
        di_fst st \<mapsto>\<^sub>a fsta * di_snd st \<mapsto>\<^sub>a snda * di_cap st \<mapsto>\<^sub>a capa *
        di_cost st \<mapsto>\<^sub>a cost_list * di_flow st \<mapsto>\<^sub>a flowa * di_es st \<mapsto>\<^sub>a esa *
        di_stk st \<mapsto>\<^sub>a stl * di_sp st \<mapsto>\<^sub>r sp *
        di_prev st \<mapsto>\<^sub>r ds_prev s * di_nxt st \<mapsto>\<^sub>r ds_nxt s \<Longrightarrow>\<^sub>A dfs_rel fl0 es0 st s"
  unfolding dfs_rel_def using assms by sep_auto

text \<open>The stack is the reversed prefix of the stack array.\<close>

lemma stk_top:
  assumes "v # rest = rev (take sp stl)" "sp \<le> length stl"
  shows "sp = Suc (length rest)" "length rest < length stl" "stl ! length rest = v"
    "rev (take (sp - 1) stl) = rest"
proof -
  have l: "sp = Suc (length rest)" using arg_cong[OF assms(1), of length] assms(2) by simp
  have t: "take sp stl = rev rest @ [v]" using arg_cong[OF assms(1), of rev] by simp
  show "sp = Suc (length rest)" by (rule l)
  show "length rest < length stl" using l assms(2) by simp
  show "stl ! length rest = v"
    using arg_cong[OF t, of "\<lambda>xs. xs ! length rest"] l by (simp add: nth_append)
  show "rev (take (sp - 1) stl) = rest"
    using arg_cong[OF t, of "take (length rest)"] l by (simp add: min_def)
qed

lemma stk_push:
  assumes "sp < length stl"
  shows "rev ((list_update (take (Suc sp) stl) (sp) (w))) = w # rev (take sp stl)"
  using assms by (simp add: take_Suc_conv_app_nth list_update_append min_def)

text \<open>The two shared writers, on the cells they touch.\<close>

lemma tree_link_imp_rule:
  assumes "w < length se" "w < length pr" "w < length pa" "w < length di" "w < length po"
    "pv < length th" "w < length rv" "w < length sm"
  shows "<di_seen st \<mapsto>\<^sub>a se *
        prnt_impl (di_tree st) \<mapsto>\<^sub>a pr *
        di_par st \<mapsto>\<^sub>a pa *
        di_dir st \<mapsto>\<^sub>a di *
        di_pot st \<mapsto>\<^sub>a po *
        di_prev st \<mapsto>\<^sub>r pv *
        thrd_impl (di_tree st) \<mapsto>\<^sub>a th *
        rvth_impl (di_tree st) \<mapsto>\<^sub>a rv *
        snum_impl (di_tree st) \<mapsto>\<^sub>a sm>
         tree_link_imp st w p e d pw
         <\<lambda>_. di_seen st \<mapsto>\<^sub>a ((list_update se (w) (True))) *
        prnt_impl (di_tree st) \<mapsto>\<^sub>a ((list_update pr (w) (p))) *
        di_par st \<mapsto>\<^sub>a ((list_update pa (w) (e))) *
        di_dir st \<mapsto>\<^sub>a ((list_update di (w) (d))) *
        di_pot st \<mapsto>\<^sub>a ((list_update po (w) (pw))) *
        di_prev st \<mapsto>\<^sub>r w *
        thrd_impl (di_tree st) \<mapsto>\<^sub>a ((list_update th (pv) (w))) *
        rvth_impl (di_tree st) \<mapsto>\<^sub>a ((list_update rv (w) (pv))) *
        snum_impl (di_tree st) \<mapsto>\<^sub>a ((list_update sm (w) (1)))>"
  unfolding tree_link_imp_def using assms by sep_auto

lemma art_edge_imp_rule:
  assumes "i < length fs" "i < length sn" "i < length cp" "i < length fw" "i < length es"
  shows "<di_fst st \<mapsto>\<^sub>a fs *
        di_snd st \<mapsto>\<^sub>a sn *
        di_cap st \<mapsto>\<^sub>a cp *
        di_flow st \<mapsto>\<^sub>a fw *
        di_es st \<mapsto>\<^sub>a es>
         art_edge_imp st i x y u f tag
         <\<lambda>_. di_fst st \<mapsto>\<^sub>a ((list_update fs (i) (x))) *
        di_snd st \<mapsto>\<^sub>a ((list_update sn (i) (y))) *
        di_cap st \<mapsto>\<^sub>a ((list_update cp (i) (u))) *
        di_flow st \<mapsto>\<^sub>a ((list_update fw (i) (f))) *
        di_es st \<mapsto>\<^sub>a ((list_update es (i) (tag)))>"
  unfolding art_edge_imp_def using assms by sep_auto

text \<open>Reads of the fields of the folded relation.\<close>

lemma dfs_rel_sp:
  "<dfs_rel fl0 es0 st s> Ref.lookup (di_sp st) <\<lambda>r. dfs_rel fl0 es0 st s * \<up>(r = length (ds_stk s))>"
  unfolding dfs_rel_def by sep_auto

lemma dfs_rel_top:
  assumes "ds_stk s = v # rest"
  shows "<dfs_rel fl0 es0 st s> Array.nth (di_stk st) (length rest) <\<lambda>r. dfs_rel fl0 es0 st s * \<up>(r = v)>"
  unfolding dfs_rel_def by (sep_auto simp: assms stk_top(2,3))

lemma dfs_rel_snd:
  assumes "e < m"
  shows "<dfs_rel fl0 es0 st s> Array.nth (di_snd st) e <\<lambda>r. dfs_rel fl0 es0 st s * \<up>(r = snd_list ! e)>"
  unfolding dfs_rel_def by (sep_auto simp: assms)

lemma dfs_rel_fst:
  assumes "e < m"
  shows "<dfs_rel fl0 es0 st s> Array.nth (di_fst st) e <\<lambda>r. dfs_rel fl0 es0 st s * \<up>(r = fst_list ! e)>"
  unfolding dfs_rel_def by (sep_auto simp: assms)

lemma dfs_rel_seen:
  assumes "w < length (ds_seen s)"
  shows "<dfs_rel fl0 es0 st s> Array.nth (di_seen st) w <\<lambda>r. dfs_rel fl0 es0 st s * \<up>(r = ds_seen s ! w)>"
  unfolding dfs_rel_def by (sep_auto simp: assms)

text \<open>The stack top: an empty stack ends the traversal, otherwise the continuation runs on the top
      vertex.\<close>

lemma dfs_rel_top_rule:
  assumes stk: "ds_stk s = v # rest" and K: "<dfs_rel fl0 es0 st s> K v <Q>"
  shows "<dfs_rel fl0 es0 st s>
           do { sp \<leftarrow> Ref.lookup (di_sp st);
                if sp = 0 then return () else do { v \<leftarrow> Array.nth (di_stk st) (sp - 1); K v } }
         <Q>"
  by (sep_auto heap: dfs_rel_sp dfs_rel_top[OF stk] K simp: stk)

lemma build_dfs_a_imp_ret:
  assumes "ds_stk s = []"
  shows "<dfs_rel fl0 es0 st s> build_dfs_a_imp st <\<lambda>_. dfs_rel fl0 es0 st s>"
  by (subst build_dfs_a_imp.simps) (sep_auto heap: dfs_rel_sp simp: assms)

text \<open>One step of the iterator of a vertex over its free outgoing resp.\ ingoing range
      (@{thm [source] FO.csr_step_upto_imp_rule}), on the folded relation.\<close>

lemma dfs_rel_step_out:
  assumes vlt: "v < vcount"
    and has: "FO.csr_has (ds_oc s) v \<Longrightarrow>
       <dfs_rel fl0 es0 st (s\<lparr>ds_oc := FO.csr_move (ds_oc s) v\<rparr>)> f (FO.csr_current (ds_oc s) v) <Q>"
    and nhas: "\<not> FO.csr_has (ds_oc s) v \<Longrightarrow> <dfs_rel fl0 es0 st s> g <Q>"
  shows "<dfs_rel fl0 es0 st s> csr_step_upto_imp (di_ob st, di_oe st, di_oc st) (di_oh st) v f g <Q>"
proof -
  have L: "v < length (fst (free_out acyc_flow))" using vlt out_ranges_fold[OF order.refl, of acyc_flow]
    by (simp add: free_out_eq)
  have vK: "v \<in> {..<vcount}" using vlt by simp
  show ?thesis
    unfolding dfs_rel_def[of _ _ _ s]
    apply (intro ht_exEI ht_extract_pre_pure)
    subgoal for fsta snda capa flowa esa auxa stl sp
      apply (rule ht_cons_pre[OF _ FO.csr_step_upto_imp_rule[where c = "ds_oc s" and Hl = "fst (free_out acyc_flow)" and F = "FI.csr_assn (ds_ic s) (di_ib st, di_ie st, di_ic st) * di_ih st \<mapsto>\<^sub>a fst (free_in acyc_flow) *
        di_seen st \<mapsto>\<^sub>a ds_seen s * prnt_impl (di_tree st) \<mapsto>\<^sub>a ds_prnt s *
        thrd_impl (di_tree st) \<mapsto>\<^sub>a ds_thrd s * rvth_impl (di_tree st) \<mapsto>\<^sub>a ds_rvth s *
        lsuc_impl (di_tree st) \<mapsto>\<^sub>a ds_lsuc s * snum_impl (di_tree st) \<mapsto>\<^sub>a ds_snum s *
        aux_impl (di_tree st) \<mapsto>\<^sub>a auxa * di_par st \<mapsto>\<^sub>a ds_par s * di_dir st \<mapsto>\<^sub>a ds_dir s *
        di_pot st \<mapsto>\<^sub>a ds_pot s * di_fst st \<mapsto>\<^sub>a fsta * di_snd st \<mapsto>\<^sub>a snda * di_cap st \<mapsto>\<^sub>a capa *
        di_cost st \<mapsto>\<^sub>a cost_list * di_flow st \<mapsto>\<^sub>a flowa * di_es st \<mapsto>\<^sub>a esa *
        di_stk st \<mapsto>\<^sub>a stl * di_sp st \<mapsto>\<^sub>r sp * di_prev st \<mapsto>\<^sub>r ds_prev s * di_nxt st \<mapsto>\<^sub>r ds_nxt s", OF vK L refl]])
        apply (simp add: mult.assoc)
      apply (rule ht_cons_pre[OF _ has])
       apply (unfold dfs_rel_def, sep_auto)[1]
      apply assumption
     apply (rule ht_cons_pre[OF _ nhas])
      apply (unfold dfs_rel_def, sep_auto)[1]
     apply assumption
    done
    done
qed

lemma dfs_rel_step_in:
  assumes vlt: "v < vcount"
    and has: "FI.csr_has (ds_ic s) v \<Longrightarrow>
       <dfs_rel fl0 es0 st (s\<lparr>ds_ic := FI.csr_move (ds_ic s) v\<rparr>)> f (FI.csr_current (ds_ic s) v) <Q>"
    and nhas: "\<not> FI.csr_has (ds_ic s) v \<Longrightarrow> <dfs_rel fl0 es0 st s> g <Q>"
  shows "<dfs_rel fl0 es0 st s> csr_step_upto_imp (di_ib st, di_ie st, di_ic st) (di_ih st) v f g <Q>"
proof -
  have L: "v < length (fst (free_in acyc_flow))" using vlt in_ranges_fold[OF order.refl, of acyc_flow]
    by (simp add: free_in_eq)
  have vK: "v \<in> {..<vcount}" using vlt by simp
  show ?thesis
    unfolding dfs_rel_def[of _ _ _ s]
    apply (intro ht_exEI ht_extract_pre_pure)
    subgoal for fsta snda capa flowa esa auxa stl sp
      apply (rule ht_cons_pre[OF _ FI.csr_step_upto_imp_rule[where c = "ds_ic s" and Hl = "fst (free_in acyc_flow)" and F = "FO.csr_assn (ds_oc s) (di_ob st, di_oe st, di_oc st) * di_oh st \<mapsto>\<^sub>a fst (free_out acyc_flow) *
        di_seen st \<mapsto>\<^sub>a ds_seen s * prnt_impl (di_tree st) \<mapsto>\<^sub>a ds_prnt s *
        thrd_impl (di_tree st) \<mapsto>\<^sub>a ds_thrd s * rvth_impl (di_tree st) \<mapsto>\<^sub>a ds_rvth s *
        lsuc_impl (di_tree st) \<mapsto>\<^sub>a ds_lsuc s * snum_impl (di_tree st) \<mapsto>\<^sub>a ds_snum s *
        aux_impl (di_tree st) \<mapsto>\<^sub>a auxa * di_par st \<mapsto>\<^sub>a ds_par s * di_dir st \<mapsto>\<^sub>a ds_dir s *
        di_pot st \<mapsto>\<^sub>a ds_pot s * di_fst st \<mapsto>\<^sub>a fsta * di_snd st \<mapsto>\<^sub>a snda * di_cap st \<mapsto>\<^sub>a capa *
        di_cost st \<mapsto>\<^sub>a cost_list * di_flow st \<mapsto>\<^sub>a flowa * di_es st \<mapsto>\<^sub>a esa *
        di_stk st \<mapsto>\<^sub>a stl * di_sp st \<mapsto>\<^sub>r sp * di_prev st \<mapsto>\<^sub>r ds_prev s * di_nxt st \<mapsto>\<^sub>r ds_nxt s", OF vK L refl]])
        apply (simp add: ac_simps)
      apply (rule ht_cons_pre[OF _ has])
       apply (unfold dfs_rel_def, sep_auto)[1]
      apply assumption
     apply (rule ht_cons_pre[OF _ nhas])
      apply (unfold dfs_rel_def, sep_auto)[1]
     apply assumption
    done
    done
qed

text \<open>Discovering a fresh vertex @{term w} from @{term v} across the free real edge @{term e}: a
      straight run of array writes, the push and the reset of the two cursors of @{term w}.\<close>

lemma dfs_discover_imp_rule:
  assumes elt: "e < m" and wlt: "w < vcount" and sz: "dfs_sized s"
    and vlt: "v < Suc vcount" and pvlt: "ds_prev s < Suc vcount"
    and depth: "length (ds_stk s) < Suc vcount"
  shows "<dfs_rel fl0 es0 st s> dfs_discover_imp st v w e
         <\<lambda>_. dfs_rel fl0 es0 st (dfs_discover s v w e)>"
proof -
  have wK: "w \<in> {..<vcount}" and wl: "w < Suc vcount" using wlt by simp_all
  have eq: "dfs_discover s v w e =
     s\<lparr>ds_seen := (list_update (ds_seen s) (w) (True)), ds_prnt := (list_update (ds_prnt s) (w) (v)), ds_par := (list_update (ds_par s) (w) (e)),
        ds_dir := (list_update (ds_dir s) (w) ((fst_list ! e = w))),
        ds_pot := (list_update (ds_pot s) (w) (pval_plus (ds_pot s ! v)
                    (M_0, if v = fst_list ! e then cost_list ! e else - cost_list ! e))),
        ds_thrd := (list_update (ds_thrd s) (ds_prev s) (w)), ds_rvth := (list_update (ds_rvth s) (w) (ds_prev s)),
        ds_snum := (list_update (ds_snum s) (w) (1)), ds_prev := w, ds_stk := w # ds_stk s,
        ds_oc := FO.csr_reset (ds_oc s) w, ds_ic := FI.csr_reset (ds_ic s) w\<rparr>"
    by (simp add: dfs_discover_def dfs_push_def Let_def)
  note L = sz[unfolded dfs_sized_def]
  show ?thesis
    unfolding dfs_rel_def[of _ _ _ s]
    apply (intro ht_exEI ht_extract_pre_pure)
    subgoal premises PU for fsta snda capa flowa esa auxa stl sp
    proof -
      have stk: "ds_stk s = rev (take sp stl)" and spl: "sp \<le> length stl" and ls: "length stl = Suc vcount"
        and fe: "fsta ! e = fst_list ! e" and fl: "e < length fsta"
        using PU elt by auto
      have spv: "sp = length (ds_stk s)" using stk spl by simp
      have spb: "sp < length stl" using spv depth ls by simp
      have cl: "e < length cost_list" using elt by simp
      define pw where "pw = pval_plus (ds_pot s ! v) (M_0, if v = fst_list ! e then cost_list ! e else - cost_list ! e)"
      have small: "<FO.csr_assn (ds_oc s) (di_ob st, di_oe st, di_oc st) *
        FI.csr_assn (ds_ic s) (di_ib st, di_ie st, di_ic st) *
        di_seen st \<mapsto>\<^sub>a (ds_seen s) *
        prnt_impl (di_tree st) \<mapsto>\<^sub>a (ds_prnt s) *
        thrd_impl (di_tree st) \<mapsto>\<^sub>a (ds_thrd s) *
        rvth_impl (di_tree st) \<mapsto>\<^sub>a (ds_rvth s) *
        snum_impl (di_tree st) \<mapsto>\<^sub>a (ds_snum s) *
        di_par st \<mapsto>\<^sub>a (ds_par s) *
        di_dir st \<mapsto>\<^sub>a (ds_dir s) *
        di_pot st \<mapsto>\<^sub>a (ds_pot s) *
        di_fst st \<mapsto>\<^sub>a fsta *
        di_cost st \<mapsto>\<^sub>a cost_list *
        di_stk st \<mapsto>\<^sub>a stl *
        di_sp st \<mapsto>\<^sub>r sp *
        di_prev st \<mapsto>\<^sub>r (ds_prev s)>
        dfs_discover_imp st v w e
        <\<lambda>_. FO.csr_assn (FO.csr_reset (ds_oc s) w) (di_ob st, di_oe st, di_oc st) *
        FI.csr_assn (FI.csr_reset (ds_ic s) w) (di_ib st, di_ie st, di_ic st) *
        di_seen st \<mapsto>\<^sub>a ((list_update (ds_seen s) (w) (True))) *
        prnt_impl (di_tree st) \<mapsto>\<^sub>a ((list_update (ds_prnt s) (w) (v))) *
        thrd_impl (di_tree st) \<mapsto>\<^sub>a ((list_update (ds_thrd s) (ds_prev s) (w))) *
        rvth_impl (di_tree st) \<mapsto>\<^sub>a ((list_update (ds_rvth s) (w) (ds_prev s))) *
        snum_impl (di_tree st) \<mapsto>\<^sub>a ((list_update (ds_snum s) (w) (1))) *
        di_par st \<mapsto>\<^sub>a ((list_update (ds_par s) (w) (e))) *
        di_dir st \<mapsto>\<^sub>a ((list_update (ds_dir s) (w) ((fst_list ! e = w)))) *
        di_pot st \<mapsto>\<^sub>a ((list_update (ds_pot s) (w) (pw))) *
        di_fst st \<mapsto>\<^sub>a fsta *
        di_cost st \<mapsto>\<^sub>a cost_list *
        di_stk st \<mapsto>\<^sub>a ((list_update stl (sp) (w))) *
        di_sp st \<mapsto>\<^sub>r (Suc sp) *
        di_prev st \<mapsto>\<^sub>r w>"
        unfolding dfs_discover_imp_def pw_def
        using wl vlt pvlt L spb fl cl
        by (sep_auto heap: tree_link_imp_rule FO.csr_reset_imp_rule[OF wK] FI.csr_reset_imp_rule[OF wK]
                     simp: fe)
      show ?thesis
        apply (rule ht_cons_pre[OF _ ht_cons_post[OF ht_frame[OF small, where R = "di_oh st \<mapsto>\<^sub>a fst (free_out acyc_flow) *
        di_ih st \<mapsto>\<^sub>a fst (free_in acyc_flow) *
        lsuc_impl (di_tree st) \<mapsto>\<^sub>a (ds_lsuc s) *
        aux_impl (di_tree st) \<mapsto>\<^sub>a auxa *
        di_snd st \<mapsto>\<^sub>a snda *
        di_cap st \<mapsto>\<^sub>a capa *
        di_flow st \<mapsto>\<^sub>a flowa *
        di_es st \<mapsto>\<^sub>a esa *
        di_nxt st \<mapsto>\<^sub>r (ds_nxt s)"]]])
         apply (simp add: ac_simps)
        unfolding eq pw_def[symmetric]
        apply (rule ent_trans[OF _ ent_star_mono[OF dfs_rel_intro[where fsta = fsta and snda = snda and capa = capa
                 and flowa = flowa and esa = esa and auxa = auxa and stl = "(list_update stl (sp) (w))" and sp = "Suc sp"]
                 ent_true[of emp]]])
         apply (simp add: ac_simps)
        using PU spb by (simp add: stk_push stk)
    qed
    done
qed

text \<open>Finishing the top vertex @{term v}: two array writes and the pop.\<close>

lemma dfs_finish_imp_rule:
  assumes stk: "ds_stk s = v # rest" and sz: "dfs_sized s"
    and vlt: "v < Suc vcount" and plt: "ds_prnt s ! v < Suc vcount"
  shows "<dfs_rel fl0 es0 st s> dfs_finish_imp st v <\<lambda>_. dfs_rel fl0 es0 st (dfs_finish s v rest)>"
proof -
  note L = sz[unfolded dfs_sized_def]
  have eq: "dfs_finish s v rest =
     s\<lparr>ds_lsuc := (list_update (ds_lsuc s) (v) (ds_prev s)),
        ds_snum := (list_update (ds_snum s) (ds_prnt s ! v) (ds_snum s ! (ds_prnt s ! v) + ds_snum s ! v)),
        ds_stk := rest\<rparr>"
    by (simp add: dfs_finish_def Let_def)
  have small: "<prnt_impl (di_tree st) \<mapsto>\<^sub>a (ds_prnt s) *
        lsuc_impl (di_tree st) \<mapsto>\<^sub>a (ds_lsuc s) *
        snum_impl (di_tree st) \<mapsto>\<^sub>a (ds_snum s) *
        di_sp st \<mapsto>\<^sub>r sp *
        di_prev st \<mapsto>\<^sub>r (ds_prev s)> dfs_finish_imp st v <\<lambda>_. prnt_impl (di_tree st) \<mapsto>\<^sub>a (ds_prnt s) *
        lsuc_impl (di_tree st) \<mapsto>\<^sub>a ((list_update (ds_lsuc s) (v) (ds_prev s))) *
        snum_impl (di_tree st) \<mapsto>\<^sub>a ((list_update (ds_snum s) (ds_prnt s ! v) (ds_snum s ! (ds_prnt s ! v) + ds_snum s ! v))) *
        di_sp st \<mapsto>\<^sub>r (sp - 1) *
        di_prev st \<mapsto>\<^sub>r (ds_prev s)>" for sp
    unfolding dfs_finish_imp_def using vlt plt L by sep_auto
  show ?thesis
    unfolding dfs_rel_def[of _ _ _ s]
    apply (intro ht_exEI ht_extract_pre_pure)
    subgoal premises PU for fsta snda capa flowa esa auxa stl sp
    proof -
      have st: "v # rest = rev (take sp stl)" and spl: "sp \<le> length stl" using PU stk by auto
      show ?thesis
        apply (rule ht_cons_pre[OF _ ht_cons_post[OF ht_frame[OF small[of sp], where R = "FO.csr_assn (ds_oc s) (di_ob st, di_oe st, di_oc st) *
        di_oh st \<mapsto>\<^sub>a fst (free_out acyc_flow) *
        FI.csr_assn (ds_ic s) (di_ib st, di_ie st, di_ic st) *
        di_ih st \<mapsto>\<^sub>a fst (free_in acyc_flow) *
        di_seen st \<mapsto>\<^sub>a (ds_seen s) *
        thrd_impl (di_tree st) \<mapsto>\<^sub>a (ds_thrd s) *
        rvth_impl (di_tree st) \<mapsto>\<^sub>a (ds_rvth s) *
        aux_impl (di_tree st) \<mapsto>\<^sub>a auxa *
        di_par st \<mapsto>\<^sub>a (ds_par s) *
        di_dir st \<mapsto>\<^sub>a (ds_dir s) *
        di_pot st \<mapsto>\<^sub>a (ds_pot s) *
        di_fst st \<mapsto>\<^sub>a fsta *
        di_snd st \<mapsto>\<^sub>a snda *
        di_cap st \<mapsto>\<^sub>a capa *
        di_cost st \<mapsto>\<^sub>a cost_list *
        di_flow st \<mapsto>\<^sub>a flowa *
        di_es st \<mapsto>\<^sub>a esa *
        di_stk st \<mapsto>\<^sub>a stl *
        di_nxt st \<mapsto>\<^sub>r (ds_nxt s)"]]])
         apply (simp add: ac_simps)
        unfolding eq
        apply (rule ent_trans[OF _ ent_star_mono[OF dfs_rel_intro[where fsta = fsta and snda = snda and capa = capa
                 and flowa = flowa and esa = esa and auxa = auxa and stl = stl and sp = "sp - 1"]
                 ent_true[of emp]]])
         apply (simp add: ac_simps)
        using PU stk_top[OF st spl] by simp
    qed
    done
qed

text \<open>A distinct stack of vertex names is no deeper than the number of names.\<close>

lemma stk_depth:
  assumes "distinct xs" "set xs \<subseteq> {..<vcount}"
  shows "length xs \<le> vcount"
  using distinct_card[OF assms(1)] card_mono[OF _ assms(2)] by simp

text \<open>The traversal: induction along @{const build_dfs}, one case per call.\<close>

lemma build_dfs_a_imp_rule:
  assumes inv0: "dfs_inv acyc_flow s0"
  shows "<dfs_rel fl0 es0 st s0> build_dfs_a_imp st <\<lambda>_. dfs_rel fl0 es0 st (build_dfs acyc_flow s0)>"
proof -
  have gen: "fl = acyc_flow \<longrightarrow> dfs_inv fl s \<longrightarrow>
       <dfs_rel fl0 es0 st s> build_dfs_a_imp st <\<lambda>_. dfs_rel fl0 es0 st (build_dfs fl s)>"
    if dom: "build_dfs_dom (fl, s)" for fl s
  proof (induct rule: bd_induct[OF dom])
    case IH: (1 fl s)
    show ?case
    proof (intro impI)
      assume fl: "fl = acyc_flow" and inv: "dfs_inv fl s"
      note simps = bd_simps[OF IH(1), unfolded fl]
      note IH1 = IH(2)[unfolded fl] and IH2 = IH(3)[unfolded fl] and IH3 = IH(4)[unfolded fl]
      have inv: "dfs_inv acyc_flow s" using inv fl by simp
      have wf: "dfs_wf acyc_flow s" and sz: "dfs_sized s" and tsi: "tree_seen_inv s"
        and thi: "thread_inv s" and sni: "snum_inv s"
        using inv by (simp_all add: dfs_inv_def)
      have "<dfs_rel fl0 es0 st s> build_dfs_a_imp st <\<lambda>_. dfs_rel fl0 es0 st (build_dfs acyc_flow s)>"
      proof (cases "ds_stk s")
        case Nil
        have "build_dfs acyc_flow s = s" using simps(4) Nil by (simp add: bd_ret_conds_def)
        thus ?thesis using build_dfs_a_imp_ret[OF Nil] by simp
      next
        case (Cons v rest)
        have vK: "v \<in> dfs_seenK s" using wf Cons by (auto simp: dfs_wf_def)
        hence vlt: "v < vcount" by (simp add: dfs_seenK_def)
        have stK: "set (ds_stk s) \<subseteq> {..<vcount}" using wf dfs_seenK_sub by (auto simp: dfs_wf_def)
        have depth: "length (ds_stk s) \<le> vcount"
          using stk_depth[OF _ stK] sni by (simp add: snum_inv_def)
        have pvlt: "ds_prev s < Suc vcount" using thi by (simp add: thread_inv_def)
        have lens: "length (ds_seen s) = Suc vcount" "length (ds_prnt s) = Suc vcount"
          using sz by (simp_all add: dfs_sized_def)
        show ?thesis
          apply (subst build_dfs_a_imp.simps)
          apply (rule dfs_rel_top_rule[OF Cons])
          apply (rule dfs_rel_step_out[OF vlt])
          subgoal premises h
          proof -
            have c1: "bd_call1_conds acyc_flow s" using Cons h by (simp add: bd_call1_conds_def)
            note S = bd_out_step[OF wf Cons h]
            define e where "e = FO.csr_current (ds_oc s) v"
            define s1 where "s1 = s\<lparr>ds_oc := FO.csr_move (ds_oc s) v\<rparr>"
            have upd: "bd_upd1 acyc_flow s =
                (if ds_seen s ! (snd_list ! e) then s1 else dfs_discover s1 v (snd_list ! e) e)"
              by (simp add: bd_upd1_def Cons Let_def e_def s1_def)
            have T: "<dfs_rel fl0 es0 st (bd_upd1 acyc_flow s)> build_dfs_a_imp st
                     <\<lambda>_. dfs_rel fl0 es0 st (build_dfs acyc_flow s)>"
              using IH1[OF c1] bd_upd1_inv[OF inv c1] simps(1)[OF c1] by simp
            have Ts: "ds_seen s ! (snd_list ! e) \<Longrightarrow>
                <dfs_rel fl0 es0 st s1> build_dfs_a_imp st <\<lambda>_. dfs_rel fl0 es0 st (build_dfs acyc_flow s)>"
              using T upd by simp
            have Tu: "\<not> ds_seen s ! (snd_list ! e) \<Longrightarrow>
                <dfs_rel fl0 es0 st (dfs_discover s1 v (snd_list ! e) e)> build_dfs_a_imp st
                <\<lambda>_. dfs_rel fl0 es0 st (build_dfs acyc_flow s)>"
              using T upd by simp
            have elt: "e < m" and wlt: "snd_list ! e < vcount" using S(1,4) by (simp_all add: e_def)
            hence wl: "snd_list ! e < Suc vcount" by simp
            have sz1: "dfs_sized s1" using sz by (simp add: s1_def dfs_sized_def)
            have aux1: "v < Suc vcount" "ds_prev s1 < Suc vcount" "length (ds_stk s1) < Suc vcount"
              "length (ds_seen s1) = Suc vcount" "ds_seen s1 = ds_seen s"
              using vlt pvlt depth lens by (simp_all add: s1_def)
            show ?thesis
              unfolding e_def[symmetric] s1_def[symmetric]
              by (sep_auto heap: dfs_rel_snd[OF elt] dfs_rel_seen dfs_discover_imp_rule[OF elt wlt sz1 aux1(1-3)] Ts Tu
                           simp: aux1(5) lens(1) wl)
          qed
          apply (rule dfs_rel_step_in[OF vlt])
          subgoal premises h
          proof -
            have c2: "bd_call2_conds acyc_flow s" using Cons h by (simp add: bd_call2_conds_def)
            note S = bd_in_step[OF wf Cons h(2)]
            define e where "e = FI.csr_current (ds_ic s) v"
            define s1 where "s1 = s\<lparr>ds_ic := FI.csr_move (ds_ic s) v\<rparr>"
            have upd: "bd_upd2 acyc_flow s =
                (if ds_seen s ! (fst_list ! e) then s1 else dfs_discover s1 v (fst_list ! e) e)"
              by (simp add: bd_upd2_def Cons Let_def e_def s1_def)
            have T: "<dfs_rel fl0 es0 st (bd_upd2 acyc_flow s)> build_dfs_a_imp st
                     <\<lambda>_. dfs_rel fl0 es0 st (build_dfs acyc_flow s)>"
              using IH2[OF c2] bd_upd2_inv[OF inv c2] simps(2)[OF c2] by simp
            have Ts: "ds_seen s ! (fst_list ! e) \<Longrightarrow>
                <dfs_rel fl0 es0 st s1> build_dfs_a_imp st <\<lambda>_. dfs_rel fl0 es0 st (build_dfs acyc_flow s)>"
              using T upd by simp
            have Tu: "\<not> ds_seen s ! (fst_list ! e) \<Longrightarrow>
                <dfs_rel fl0 es0 st (dfs_discover s1 v (fst_list ! e) e)> build_dfs_a_imp st
                <\<lambda>_. dfs_rel fl0 es0 st (build_dfs acyc_flow s)>"
              using T upd by simp
            have elt: "e < m" and wlt: "fst_list ! e < vcount" using S(1,4) by (simp_all add: e_def)
            hence wl: "fst_list ! e < Suc vcount" by simp
            have sz1: "dfs_sized s1" using sz by (simp add: s1_def dfs_sized_def)
            have aux1: "v < Suc vcount" "ds_prev s1 < Suc vcount" "length (ds_stk s1) < Suc vcount"
              "length (ds_seen s1) = Suc vcount" "ds_seen s1 = ds_seen s"
              using vlt pvlt depth lens by (simp_all add: s1_def)
            show ?thesis
              unfolding e_def[symmetric] s1_def[symmetric]
              by (sep_auto heap: dfs_rel_fst[OF elt] dfs_rel_seen dfs_discover_imp_rule[OF elt wlt sz1 aux1(1-3)] Ts Tu
                           simp: aux1(5) lens(1) wl)
          qed
          subgoal premises h
          proof -
            have c3: "bd_call3_conds acyc_flow s" using Cons h by (simp add: bd_call3_conds_def)
            have upd: "bd_upd3 s = dfs_finish s v rest" by (simp add: bd_upd3_def Cons)
            have T: "<dfs_rel fl0 es0 st (dfs_finish s v rest)> build_dfs_a_imp st
                     <\<lambda>_. dfs_rel fl0 es0 st (build_dfs acyc_flow s)>"
              using IH3[OF c3] bd_upd3_inv[OF inv c3] simps(3)[OF c3] upd by simp
            have plt: "ds_prnt s ! v < Suc vcount"
              using tsi vK by (auto simp: tree_seen_inv_def dfs_seenK_def)
            show ?thesis
              using vlt by (sep_auto heap: dfs_finish_imp_rule[OF Cons sz _ plt] T)
          qed
          done
      qed
      thus "<dfs_rel fl0 es0 st s> build_dfs_a_imp st <\<lambda>_. dfs_rel fl0 es0 st (build_dfs fl s)>"
        using fl by simp
    qed
  qed
  have dom0: "build_dfs_dom (acyc_flow, s0)" using inv0 by (simp add: dfs_inv_def build_dfs_dom_wf)
  show ?thesis using gen[OF dom0] inv0 by simp
qed

subsection \<open>Layer (d.6): opening tree components and emitting artificial edges\<close>

text \<open>Opening a tree component, on the cells it touches: the artificial edge, the tree fields of
      @{term c}, the one-element stack and the two cursors of @{term c}; the continuation is the
      traversal.  The orientation @{term u} and the flow @{term a} of the artificial edge are named.\<close>

lemma open_tree_component_imp_cps:
  assumes cK: "c \<in> {..<vcount}" and x: "imbl ! c = x" and u: "(0 \<le> x) = u" and a: "\<bar>x\<bar> = a"
    and bnd: "c < length imbl" "m + nx < length fs" "m + nx < length sn" "m + nx < length cp"
      "m + nx < length fw" "m + nx < length es" "c < length se" "c < length pr" "c < length pa"
      "c < length di" "c < length po" "pv < length th" "c < length rv" "c < length sm" "0 < length stl"
    and K: "<FO.csr_assn (FO.csr_reset oc c) (di_ob st, di_oe st, di_oc st) *
        FI.csr_assn (FI.csr_reset ic c) (di_ib st, di_ie st, di_ic st) *
        imb_arr \<mapsto>\<^sub>a imbl *
        di_fst st \<mapsto>\<^sub>a ((list_update fs (m + nx) ((if u then c else vcount)))) *
        di_snd st \<mapsto>\<^sub>a ((list_update sn (m + nx) ((if u then vcount else c)))) *
        di_cap st \<mapsto>\<^sub>a ((list_update cp (m + nx) ((if u then a + 1 else a)))) *
        di_flow st \<mapsto>\<^sub>a ((list_update fw (m + nx) (a))) *
        di_es st \<mapsto>\<^sub>a ((list_update es (m + nx) (InTree))) *
        di_nxt st \<mapsto>\<^sub>r (Suc nx) * 
        di_seen st \<mapsto>\<^sub>a ((list_update se (c) (True))) *
        prnt_impl (di_tree st) \<mapsto>\<^sub>a ((list_update pr (c) (vcount))) *
        di_par st \<mapsto>\<^sub>a ((list_update pa (c) (m + nx))) *
        di_dir st \<mapsto>\<^sub>a ((list_update di (c) (u))) *
        di_pot st \<mapsto>\<^sub>a ((list_update po (c) ((if u then pval_negM else pval_M)))) *
        thrd_impl (di_tree st) \<mapsto>\<^sub>a ((list_update th (pv) (c))) *
        rvth_impl (di_tree st) \<mapsto>\<^sub>a ((list_update rv (c) (pv))) *
        snum_impl (di_tree st) \<mapsto>\<^sub>a ((list_update sm (c) (1))) *
        di_prev st \<mapsto>\<^sub>r c *
        di_stk st \<mapsto>\<^sub>a ((list_update stl (0) (c))) *
        di_sp st \<mapsto>\<^sub>r 1 *
        R>
        build_dfs_a_imp st <Q>"
  shows "<FO.csr_assn oc (di_ob st, di_oe st, di_oc st) *
        FI.csr_assn ic (di_ib st, di_ie st, di_ic st) *
        imb_arr \<mapsto>\<^sub>a imbl *
        di_fst st \<mapsto>\<^sub>a fs *
        di_snd st \<mapsto>\<^sub>a sn *
        di_cap st \<mapsto>\<^sub>a cp *
        di_flow st \<mapsto>\<^sub>a fw *
        di_es st \<mapsto>\<^sub>a es *
        di_nxt st \<mapsto>\<^sub>r nx *
        di_seen st \<mapsto>\<^sub>a se *
        prnt_impl (di_tree st) \<mapsto>\<^sub>a pr *
        di_par st \<mapsto>\<^sub>a pa *
        di_dir st \<mapsto>\<^sub>a di *
        di_pot st \<mapsto>\<^sub>a po *
        thrd_impl (di_tree st) \<mapsto>\<^sub>a th *
        rvth_impl (di_tree st) \<mapsto>\<^sub>a rv *
        snum_impl (di_tree st) \<mapsto>\<^sub>a sm *
        di_prev st \<mapsto>\<^sub>r pv *
        di_stk st \<mapsto>\<^sub>a stl *
        di_sp st \<mapsto>\<^sub>r sp *
        R>
        open_tree_component_imp st imb_arr m vcount c <Q>"
proof (cases u)
  case True
  show ?thesis unfolding open_tree_component_imp_def Let_def
    using bnd by (sep_auto heap: art_edge_imp_rule tree_link_imp_rule FO.csr_reset_imp_rule[OF cK]
                               FI.csr_reset_imp_rule[OF cK] K[unfolded Eq_TrueI[OF True] if_True One_nat_def]
                           simp: x u a True)
next
  case False
  show ?thesis unfolding open_tree_component_imp_def Let_def
    using bnd by (sep_auto heap: art_edge_imp_rule tree_link_imp_rule FO.csr_reset_imp_rule[OF cK]
                               FI.csr_reset_imp_rule[OF cK] K[unfolded Eq_FalseI[OF False] if_False One_nat_def]
                           simp: x u a False)
qed

lemma emit_U_edge_imp_small:
  assumes x: "imbl ! v = x" and u: "(0 \<le> x) = u" and a: "\<bar>x\<bar> = a"
    and bnd: "v < length imbl" "m + nx < length fs" "m + nx < length sn" "m + nx < length cp"
      "m + nx < length fw" "m + nx < length es"
  shows "<imb_arr \<mapsto>\<^sub>a imbl *
        di_nxt st \<mapsto>\<^sub>r nx *
        di_fst st \<mapsto>\<^sub>a fs *
        di_snd st \<mapsto>\<^sub>a sn *
        di_cap st \<mapsto>\<^sub>a cp *
        di_flow st \<mapsto>\<^sub>a fw *
        di_es st \<mapsto>\<^sub>a es>
         emit_U_edge_imp st imb_arr m vcount v
         <\<lambda>_. imb_arr \<mapsto>\<^sub>a imbl *
        di_nxt st \<mapsto>\<^sub>r (Suc nx) *
        di_fst st \<mapsto>\<^sub>a ((list_update fs (m + nx) ((if u then v else vcount)))) *
        di_snd st \<mapsto>\<^sub>a ((list_update sn (m + nx) ((if u then vcount else v)))) *
        di_cap st \<mapsto>\<^sub>a ((list_update cp (m + nx) (a))) *
        di_flow st \<mapsto>\<^sub>a ((list_update fw (m + nx) (a))) *
        di_es st \<mapsto>\<^sub>a ((list_update es (m + nx) (InU)))>"
  unfolding emit_U_edge_imp_def Let_def
  using bnd by (sep_auto heap: art_edge_imp_rule simp: x u a)

text \<open>Emitting a saturated @{term U} edge refines @{const emit_U_edge}.\<close>

lemma emit_U_edge_imp_rule:
  assumes vlt: "v < Suc vcount" and al: "art_len s" and room: "ds_nxt s < length vs_list"
  shows "<dfs_rel fl0 es0 st s * imb_arr \<mapsto>\<^sub>a imbalance> emit_U_edge_imp st imb_arr m vcount v
         <\<lambda>_. dfs_rel fl0 es0 st (emit_U_edge s v) * imb_arr \<mapsto>\<^sub>a imbalance>"
proof -
  have eq: "emit_U_edge s v =
     s\<lparr>ds_afst := (list_update (ds_afst s) (ds_nxt s) ((if 0 \<le> imbalance ! v then v else vcount))),
        ds_asnd := (list_update (ds_asnd s) (ds_nxt s) ((if 0 \<le> imbalance ! v then vcount else v))),
        ds_acap := (list_update (ds_acap s) (ds_nxt s) (\<bar>imbalance ! v\<bar>)),
        ds_aflw := (list_update (ds_aflw s) (ds_nxt s) (\<bar>imbalance ! v\<bar>)),
        ds_aest := (list_update (ds_aest s) (ds_nxt s) (InU)), ds_nxt := Suc (ds_nxt s)\<rparr>"
    by (simp add: emit_U_edge_def Let_def)
  have L: "length (ds_afst s) = length vs_list" "length (ds_asnd s) = length vs_list"
    "length (ds_acap s) = length vs_list" "length (ds_aflw s) = length vs_list"
    "length (ds_aest s) = length vs_list" using al by (simp_all add: art_len_def)
  show ?thesis
    unfolding dfs_rel_def[of _ _ _ s]
    apply (simp only: ex_assn_move_out)
    apply (intro ht_exEI)
    apply (subst mult.assoc, subst mult.commute[of "\<up>_"], subst mult.assoc[symmetric])
    apply (rule ht_extract_pre_pure)
    subgoal premises PU for fsta snda capa flowa esa auxa stl sp
    proof -
      have b: "m + ds_nxt s < length fsta" "m + ds_nxt s < length snda" "m + ds_nxt s < length capa"
        "m + ds_nxt s < length flowa" "m + ds_nxt s < length esa"
        using PU room L by auto
      have vl: "v < length imbalance" using vlt by simp
      note small = emit_U_edge_imp_small[where imbl = imbalance and x = "imbalance ! v"
          and u = "0 \<le> imbalance ! v" and a = "\<bar>imbalance ! v\<bar>" and fs = "fsta" and sn = "snda" and cp = "capa" and fw = "flowa" and es = "esa" and nx = "ds_nxt s", OF refl refl refl vl b]
      show ?thesis
        apply (rule ht_cons_pre[OF _ ht_cons_post[OF ht_frame[OF small, where R = "FO.csr_assn (ds_oc s) (di_ob st, di_oe st, di_oc st) *
        di_oh st \<mapsto>\<^sub>a fst (free_out acyc_flow) *
        FI.csr_assn (ds_ic s) (di_ib st, di_ie st, di_ic st) *
        di_ih st \<mapsto>\<^sub>a fst (free_in acyc_flow) *
        di_seen st \<mapsto>\<^sub>a (ds_seen s) *
        prnt_impl (di_tree st) \<mapsto>\<^sub>a (ds_prnt s) *
        thrd_impl (di_tree st) \<mapsto>\<^sub>a (ds_thrd s) *
        rvth_impl (di_tree st) \<mapsto>\<^sub>a (ds_rvth s) *
        lsuc_impl (di_tree st) \<mapsto>\<^sub>a (ds_lsuc s) *
        snum_impl (di_tree st) \<mapsto>\<^sub>a (ds_snum s) *
        aux_impl (di_tree st) \<mapsto>\<^sub>a auxa *
        di_par st \<mapsto>\<^sub>a (ds_par s) *
        di_dir st \<mapsto>\<^sub>a (ds_dir s) *
        di_pot st \<mapsto>\<^sub>a (ds_pot s) *
        di_cost st \<mapsto>\<^sub>a cost_list *
        di_stk st \<mapsto>\<^sub>a (stl) *
        di_sp st \<mapsto>\<^sub>r (sp) *
        di_prev st \<mapsto>\<^sub>r (ds_prev s)"]]])
         apply (simp add: ac_simps)
        unfolding eq
        apply (rule ent_trans[OF _ ent_star_mono[OF ent_star_mono[OF dfs_rel_intro[where fsta = "(list_update fsta (m + ds_nxt s) ((if 0 \<le> imbalance ! v then v else vcount)))"
                 and snda = "(list_update snda (m + ds_nxt s) ((if 0 \<le> imbalance ! v then vcount else v)))"
                 and capa = "(list_update capa (m + ds_nxt s) (\<bar>imbalance ! v\<bar>))" and flowa = "(list_update flowa (m + ds_nxt s) (\<bar>imbalance ! v\<bar>))"
                 and esa = "(list_update esa (m + ds_nxt s) (InU))" and auxa = auxa and stl = stl and sp = sp]
                 ent_refl[of "imb_arr \<mapsto>\<^sub>a imbalance"]] ent_true[of emp]]])
         apply (simp add: ac_simps)
        using PU room L by (auto simp: nth_list_update less_Suc_eq)
    qed
    done
qed

text \<open>Opening a tree component refines @{const open_tree_component}: the writes produce the seed state of
      @{thm [source] open_tree_component_seed}, from which the traversal runs.\<close>

lemma open_tree_component_imp_rule:
  assumes inv: "dfs_inv acyc_flow s" and cvc: "c < vcount" and unseen: "\<not> ds_seen s ! c"
    and cnz: "c \<noteq> 0" and stke: "ds_stk s = []" and al: "art_len s" and room: "ds_nxt s < length vs_list"
  shows "<dfs_rel fl0 es0 st s * imb_arr \<mapsto>\<^sub>a imbalance> open_tree_component_imp st imb_arr m vcount c
         <\<lambda>_. dfs_rel fl0 es0 st (open_tree_component acyc_flow s c) * imb_arr \<mapsto>\<^sub>a imbalance>"
proof -
  have wf: "dfs_wf acyc_flow s" and sz: "dfs_sized s" and thi: "thread_inv s"
    using inv by (simp_all add: dfs_inv_def)
  note L = sz[unfolded dfs_sized_def]
  have AL: "length (ds_afst s) = length vs_list" "length (ds_asnd s) = length vs_list"
    "length (ds_acap s) = length vs_list" "length (ds_aflw s) = length vs_list"
    "length (ds_aest s) = length vs_list" using al by (simp_all add: art_len_def)
  have pvl: "ds_prev s < Suc vcount" using thi by (simp add: thread_inv_def)
  have cK: "c \<in> {..<vcount}" using cvc by simp
  obtain sd where SD: "open_tree_component acyc_flow s c = build_dfs acyc_flow sd" "build_dfs_dom (acyc_flow, sd)"
    "(dfs_inv acyc_flow s \<and> \<not> ds_seen s ! c \<and> c \<noteq> 0 \<and> ds_stk s = []) \<longrightarrow> dfs_inv acyc_flow sd"
    "ds_stk sd = [c]" "ds_oc sd = ds_oc (dfs_push s c)" "ds_ic sd = ds_ic (dfs_push s c)"
    "ds_nxt sd = Suc (ds_nxt s)"
    "ds_seen sd = (list_update (ds_seen s) (c) (True))" "ds_prnt sd = (list_update (ds_prnt s) (c) (vcount))"
    "ds_par sd = (list_update (ds_par s) (c) (m + ds_nxt s))" "ds_dir sd = (list_update (ds_dir s) (c) (art_dir c))"
    "ds_pot sd = (list_update (ds_pot s) (c) ((if art_dir c then pval_negM else pval_M)))"
    "ds_thrd sd = (list_update (ds_thrd s) (ds_prev s) (c))" "ds_snum sd = (list_update (ds_snum s) (c) (1))"
    "ds_afst sd = (list_update (ds_afst s) (ds_nxt s) ((if art_dir c then c else vcount)))"
    "ds_asnd sd = (list_update (ds_asnd s) (ds_nxt s) ((if art_dir c then vcount else c)))"
    "ds_acap sd = (list_update (ds_acap s) (ds_nxt s) (art_tree_cap c))"
    "ds_aflw sd = (list_update (ds_aflw s) (ds_nxt s) (art_flow c))"
    "ds_aest sd = (list_update (ds_aest s) (ds_nxt s) (InTree))"
    "ds_rvth sd = (list_update (ds_rvth s) (c) (ds_prev s))" "ds_prev sd = c" "ds_lsuc sd = ds_lsuc s"
    by (rule open_tree_component_seed[OF wf sz cvc])
  have isd: "dfs_inv acyc_flow sd" using SD(3) inv unseen cnz stke by blast
  note B = ht_frame[OF build_dfs_a_imp_rule[OF isd], where R = "imb_arr \<mapsto>\<^sub>a imbalance", folded SD(1)]
  show ?thesis
    unfolding dfs_rel_def[of _ _ _ s]
    apply (simp only: ex_assn_move_out)
    apply (intro ht_exEI)
    apply (subst mult.assoc, subst mult.commute[of "\<up>_"], subst mult.assoc[symmetric])
    apply (rule ht_extract_pre_pure)
    subgoal premises PU for fsta snda capa flowa esa auxa stl sp
    proof -
      have b: "c < length imbalance" "m + ds_nxt s < length fsta" "m + ds_nxt s < length snda"
        "m + ds_nxt s < length capa" "m + ds_nxt s < length flowa" "m + ds_nxt s < length esa"
        "c < length (ds_seen s)" "c < length (ds_prnt s)" "c < length (ds_par s)" "c < length (ds_dir s)"
        "c < length (ds_pot s)" "ds_prev s < length (ds_thrd s)" "c < length (ds_rvth s)"
        "c < length (ds_snum s)" "0 < length stl"
        using PU room AL L cvc pvl by auto
      have K: "<FO.csr_assn (FO.csr_reset (ds_oc s) c) (di_ob st, di_oe st, di_oc st) *
        FI.csr_assn (FI.csr_reset (ds_ic s) c) (di_ib st, di_ie st, di_ic st) *
        imb_arr \<mapsto>\<^sub>a imbalance *
        di_fst st \<mapsto>\<^sub>a ((list_update fsta (m + ds_nxt s) ((if (0 \<le> imbalance ! c) then c else vcount)))) *
        di_snd st \<mapsto>\<^sub>a ((list_update snda (m + ds_nxt s) ((if (0 \<le> imbalance ! c) then vcount else c)))) *
        di_cap st \<mapsto>\<^sub>a ((list_update capa (m + ds_nxt s) ((if (0 \<le> imbalance ! c) then \<bar>imbalance ! c\<bar> + 1 else \<bar>imbalance ! c\<bar>)))) *
        di_flow st \<mapsto>\<^sub>a ((list_update flowa (m + ds_nxt s) (\<bar>imbalance ! c\<bar>))) *
        di_es st \<mapsto>\<^sub>a ((list_update esa (m + ds_nxt s) (InTree))) *
        di_nxt st \<mapsto>\<^sub>r (Suc (ds_nxt s)) *
        di_seen st \<mapsto>\<^sub>a ((list_update (ds_seen s) (c) (True))) *
        prnt_impl (di_tree st) \<mapsto>\<^sub>a ((list_update (ds_prnt s) (c) (vcount))) *
        di_par st \<mapsto>\<^sub>a ((list_update (ds_par s) (c) (m + ds_nxt s))) *
        di_dir st \<mapsto>\<^sub>a ((list_update (ds_dir s) (c) ((0 \<le> imbalance ! c)))) *
        di_pot st \<mapsto>\<^sub>a ((list_update (ds_pot s) (c) ((if (0 \<le> imbalance ! c) then pval_negM else pval_M)))) *
        thrd_impl (di_tree st) \<mapsto>\<^sub>a ((list_update (ds_thrd s) (ds_prev s) (c))) *
        rvth_impl (di_tree st) \<mapsto>\<^sub>a ((list_update (ds_rvth s) (c) (ds_prev s))) *
        snum_impl (di_tree st) \<mapsto>\<^sub>a ((list_update (ds_snum s) (c) (1))) *
        di_prev st \<mapsto>\<^sub>r c *
        di_stk st \<mapsto>\<^sub>a ((list_update stl (0) (c))) *
        di_sp st \<mapsto>\<^sub>r 1 *
        (di_oh st \<mapsto>\<^sub>a fst (free_out acyc_flow) *
        di_ih st \<mapsto>\<^sub>a fst (free_in acyc_flow) *
        lsuc_impl (di_tree st) \<mapsto>\<^sub>a (ds_lsuc s) *
        aux_impl (di_tree st) \<mapsto>\<^sub>a auxa *
        di_cost st \<mapsto>\<^sub>a cost_list)>
        build_dfs_a_imp st <\<lambda>_. dfs_rel fl0 es0 st (open_tree_component acyc_flow s c) * imb_arr \<mapsto>\<^sub>a imbalance>"
        apply (rule ht_cons_pre[OF _ B])
        apply (rule ent_trans[OF _ ent_star_mono[OF dfs_rel_intro[where fsta = "(list_update fsta (m + ds_nxt s) ((if (0 \<le> imbalance ! c) then c else vcount)))"
                 and snda = "(list_update snda (m + ds_nxt s) ((if (0 \<le> imbalance ! c) then vcount else c)))"
                 and capa = "(list_update capa (m + ds_nxt s) ((if (0 \<le> imbalance ! c) then \<bar>imbalance ! c\<bar> + 1 else \<bar>imbalance ! c\<bar>)))" and flowa = "(list_update flowa (m + ds_nxt s) (\<bar>imbalance ! c\<bar>))"
                 and esa = "(list_update esa (m + ds_nxt s) (InTree))" and auxa = auxa and stl = "(list_update stl (0) (c))" and sp = 1]
                 ent_refl]])
         apply (simp add: SD dfs_push_def art_dir_def ac_simps)
        using PU room AL b by (auto simp: SD art_dir_def art_flow_def art_tree_cap_def nth_list_update less_Suc_eq
                                     take_Suc_conv_app_nth)
      show ?thesis
        by (rule ht_cons_pre[OF _ open_tree_component_imp_cps[where oc = "ds_oc s" and ic = "ds_ic s" and imbl = "imbalance" and x = "imbalance ! c" and u = "0 \<le> imbalance ! c" and a = "\<bar>imbalance ! c\<bar>" and fs = "fsta" and sn = "snda" and cp = "capa" and fw = "flowa" and es = "esa" and nx = "ds_nxt s" and se = "ds_seen s" and pr = "ds_prnt s" and pa = "ds_par s" and di = "ds_dir s" and po = "ds_pot s" and th = "ds_thrd s" and rv = "ds_rvth s" and sm = "ds_snum s" and pv = "ds_prev s" and stl = "stl" and sp = "sp" and R = "di_oh st \<mapsto>\<^sub>a fst (free_out acyc_flow) *
        di_ih st \<mapsto>\<^sub>a fst (free_in acyc_flow) *
        lsuc_impl (di_tree st) \<mapsto>\<^sub>a (ds_lsuc s) *
        aux_impl (di_tree st) \<mapsto>\<^sub>a auxa *
        di_cost st \<mapsto>\<^sub>a cost_list", OF cK refl refl refl b K]])
           (simp add: ac_simps)
    qed
    done
qed

subsection \<open>Layer (d.7): the two vertex scans\<close>

text \<open>The scans never decrease the artificial-edge counter, so the final count bounds every
      intermediate one --- the room each emission needs.\<close>

lemma fold_nxt_mono:
  assumes step: "\<And>v t. v \<in> set vs_list \<Longrightarrow> dfs_inv acyc_flow t \<Longrightarrow> ds_stk t = [] \<Longrightarrow>
                  dfs_inv acyc_flow (g v t) \<and> ds_stk (g v t) = [] \<and> ds_nxt t \<le> ds_nxt (g v t)"
  shows "set xs \<subseteq> set vs_list \<Longrightarrow> dfs_inv acyc_flow s \<Longrightarrow> ds_stk s = [] \<Longrightarrow>
         ds_nxt s \<le> ds_nxt (fold g xs s)"
proof (induct xs arbitrary: s)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  have "dfs_inv acyc_flow (g x s) \<and> ds_stk (g x s) = [] \<and> ds_nxt s \<le> ds_nxt (g x s)"
    using step[of x s] Cons.prems by simp
  thus ?case using Cons.hyps[of "g x s"] Cons.prems(1) by fastforce
qed

lemma phase1_step_mono:
  "v \<in> set vs_list \<Longrightarrow> dfs_inv acyc_flow t \<Longrightarrow> ds_stk t = [] \<Longrightarrow>
   dfs_inv acyc_flow (phase1_step acyc_flow v t) \<and> ds_stk (phase1_step acyc_flow v t) = [] \<and>
   ds_nxt t \<le> ds_nxt (phase1_step acyc_flow v t)"
proof -
  assume v: "v \<in> set vs_list" and i: "dfs_inv acyc_flow t" and e: "ds_stk t = []"
  have "dfs_inv acyc_flow (phase1_step acyc_flow v t) \<and> ds_stk (phase1_step acyc_flow v t) = []"
    by (rule phase1_step_inv[OF v]) (simp add: i e)
  moreover have "ds_nxt t \<le> ds_nxt (phase1_step acyc_flow v t)"
    using phase1_step_nxt[OF i vs_less_vcount[OF v]] by auto
  ultimately show ?thesis by simp
qed

lemma phase2_step_mono:
  "v \<in> set vs_list \<Longrightarrow> dfs_inv acyc_flow t \<Longrightarrow> ds_stk t = [] \<Longrightarrow>
   dfs_inv acyc_flow (phase2_step acyc_flow v t) \<and> ds_stk (phase2_step acyc_flow v t) = [] \<and>
   ds_nxt t \<le> ds_nxt (phase2_step acyc_flow v t)"
proof -
  assume v: "v \<in> set vs_list" and i: "dfs_inv acyc_flow t" and e: "ds_stk t = []"
  have "dfs_inv acyc_flow (phase2_step acyc_flow v t) \<and> ds_stk (phase2_step acyc_flow v t) = []"
    by (rule phase2_step_inv[OF v]) (simp add: i e)
  moreover have "ds_nxt t \<le> ds_nxt (phase2_step acyc_flow v t)"
    using phase2_step_nxt2[OF i vs_less_vcount[OF v]] by auto
  ultimately show ?thesis by simp
qed

text \<open>The emptiness tests of the two blocks of a vertex, on the folded relation.\<close>

lemma dfs_rel_empty_out:
  "v < vcount \<Longrightarrow> <dfs_rel fl0 es0 st s> csr_empty_imp (di_ob st) v
   <\<lambda>r. dfs_rel fl0 es0 st s * \<up>(r = FO.csr_empty v)>"
  unfolding dfs_rel_def by (sep_auto heap: FO.csr_empty_imp_rule)

lemma dfs_rel_empty_in:
  "v < vcount \<Longrightarrow> <dfs_rel fl0 es0 st s> csr_empty_imp (di_ib st) v
   <\<lambda>r. dfs_rel fl0 es0 st s * \<up>(r = FI.csr_empty v)>"
  unfolding dfs_rel_def by (sep_auto heap: FI.csr_empty_imp_rule)

lemma phase1_step_imp_rule:
  assumes v: "v \<in> set vs_list" and inv: "dfs_inv acyc_flow s" and stke: "ds_stk s = []"
    and al: "art_len s" and room: "ds_nxt (phase1_step acyc_flow v s) \<le> length vs_list"
  shows "<dfs_rel fl0 es0 st s * imb_arr \<mapsto>\<^sub>a imbalance> phase1_step_imp st imb_arr m vcount v
         <\<lambda>_. dfs_rel fl0 es0 st (phase1_step acyc_flow v s) * imb_arr \<mapsto>\<^sub>a imbalance>"
proof -
  have vlt: "v < vcount" using v vs_less_vcount by blast
  have vnz: "v \<noteq> 0" using v zero_notin_vs_list by metis
  from vlt have vl: "v < Suc vcount" "v < length imbalance" by simp_all
  have ls: "v < length (ds_seen s)" using inv vlt by (simp add: dfs_inv_def dfs_sized_def)
  show ?thesis
  proof (cases "imbalance ! v = 0")
    case True
    thus ?thesis by (sep_auto simp: phase1_step_imp_def phase1_step_def vl)
  next
    case nz: False
    show ?thesis
    proof (cases "ds_seen s ! v")
      case True
      have r: "ds_nxt s < length vs_list"
        using room nz True emit_U_edge_nxt[of s v] by (simp add: phase1_step_def)
      show ?thesis
        by (sep_auto heap: dfs_rel_seen[OF ls] emit_U_edge_imp_rule[OF vl(1) al r]
                     simp: phase1_step_imp_def phase1_step_def nz True vl)
    next
      case False
      have r: "ds_nxt s < length vs_list"
        using room nz False open_tree_component_art(1)[OF inv vlt] by (simp add: phase1_step_def)
      show ?thesis
        by (sep_auto heap: dfs_rel_seen[OF ls] open_tree_component_imp_rule[OF inv vlt False vnz stke al r]
                     simp: phase1_step_imp_def phase1_step_def nz False vl)
    qed
  qed
qed

lemma phase1_imp_rule:
  assumes "Suc 0 \<le> v" "v \<le> Suc n" "dfs_inv acyc_flow s" "ds_stk s = []" "art_len s"
    "ds_nxt (fold (phase1_step acyc_flow) [v..<Suc n] s) \<le> length vs_list"
  shows "<dfs_rel fl0 es0 st s * imb_arr \<mapsto>\<^sub>a imbalance> phase1_imp st imb_arr m vcount v n
         <\<lambda>_. dfs_rel fl0 es0 st (fold (phase1_step acyc_flow) [v..<Suc n] s) * imb_arr \<mapsto>\<^sub>a imbalance>"
  using assms
proof (induction "Suc n - v" arbitrary: v s)
  case 0
  hence "n < v" by simp
  thus ?case by (subst phase1_imp.simps) sep_auto
next
  case (Suc d)
  have vn: "v \<le> n" and vs: "v \<in> set vs_list" using Suc.hyps(2) Suc.prems(1) by (auto simp: vs_list_def)
  have up: "[v..<Suc n] = v # [Suc v..<Suc n]" using vn by (simp add: upt_conv_Cons)
  note M = phase1_step_mono[OF vs Suc.prems(3,4)]
  have rest: "set [Suc v..<Suc n] \<subseteq> set vs_list" by (auto simp: vs_list_def)
  have M1: "dfs_inv acyc_flow (phase1_step acyc_flow v s)" "ds_stk (phase1_step acyc_flow v s) = []"
    using M by simp_all
  note P6 = Suc.prems(6)[unfolded up fold_Cons o_apply]
  have room1: "ds_nxt (phase1_step acyc_flow v s) \<le> length vs_list"
    by (rule order.trans[OF fold_nxt_mono[where g = "phase1_step acyc_flow", OF _ rest M1] P6])
       (rule phase1_step_mono; assumption)
  have al1: "art_len (phase1_step acyc_flow v s)" by (rule phase1_step_art_len[OF vs Suc.prems(3,5)])
  have IH: "<dfs_rel fl0 es0 st (phase1_step acyc_flow v s) * imb_arr \<mapsto>\<^sub>a imbalance> phase1_imp st imb_arr m vcount (Suc v) n
         <\<lambda>_. dfs_rel fl0 es0 st (fold (phase1_step acyc_flow) [v..<Suc n] s) * imb_arr \<mapsto>\<^sub>a imbalance>"
    unfolding up fold_Cons o_apply
    by (rule Suc.hyps(1)[OF _ _ _ M1 al1 P6]) (use Suc.hyps(2) vn in simp_all)
  show ?case
    using vn by (subst phase1_imp.simps) (sep_auto heap: phase1_step_imp_rule[OF vs Suc.prems(3,4,5) room1] IH)
qed

lemma phase2_step_imp_rule:
  assumes v: "v \<in> set vs_list" and inv: "dfs_inv acyc_flow s" and stke: "ds_stk s = []"
    and al: "art_len s" and room: "ds_nxt (phase2_step acyc_flow v s) \<le> length vs_list"
  shows "<dfs_rel fl0 es0 st s * imb_arr \<mapsto>\<^sub>a imbalance> phase2_step_imp st imb_arr m vcount v
         <\<lambda>_. dfs_rel fl0 es0 st (phase2_step acyc_flow v s) * imb_arr \<mapsto>\<^sub>a imbalance>"
proof -
  have vlt: "v < vcount" using v vs_less_vcount by blast
  have vnz: "v \<noteq> 0" using v zero_notin_vs_list by metis
  have ls: "v < length (ds_seen s)" using inv vlt by (simp add: dfs_inv_def dfs_sized_def)
  have lon: "is_lonely v \<longleftrightarrow> FO.csr_empty v \<and> FI.csr_empty v" by (simp add: is_lonely_def)
  show ?thesis
  proof (cases "ds_seen s ! v \<or> is_lonely v")
    case True
    thus ?thesis
      by (sep_auto heap: dfs_rel_seen[OF ls] dfs_rel_empty_out[OF vlt] dfs_rel_empty_in[OF vlt]
                   simp: phase2_step_imp_def phase2_step_def lon)
  next
    case False
    hence ns: "\<not> ds_seen s ! v" and nl: "\<not> (FO.csr_empty v \<and> FI.csr_empty v)" using lon by auto
    have r: "ds_nxt s < length vs_list"
      using room False open_tree_component_art(1)[OF inv vlt] by (simp add: phase2_step_def)
    show ?thesis
      using nl
      by (sep_auto heap: dfs_rel_seen[OF ls] dfs_rel_empty_out[OF vlt] dfs_rel_empty_in[OF vlt]
                         open_tree_component_imp_rule[OF inv vlt ns vnz stke al r]
                   simp: phase2_step_imp_def phase2_step_def ns lon)
  qed
qed

lemma phase2_imp_rule:
  assumes "Suc 0 \<le> v" "v \<le> Suc n" "dfs_inv acyc_flow s" "ds_stk s = []" "art_len s"
    "ds_nxt (fold (phase2_step acyc_flow) [v..<Suc n] s) \<le> length vs_list"
  shows "<dfs_rel fl0 es0 st s * imb_arr \<mapsto>\<^sub>a imbalance> phase2_imp st imb_arr m vcount v n
         <\<lambda>_. dfs_rel fl0 es0 st (fold (phase2_step acyc_flow) [v..<Suc n] s) * imb_arr \<mapsto>\<^sub>a imbalance>"
  using assms
proof (induction "Suc n - v" arbitrary: v s)
  case 0
  hence "n < v" by simp
  thus ?case by (subst phase2_imp.simps) sep_auto
next
  case (Suc d)
  have vn: "v \<le> n" and vs: "v \<in> set vs_list" using Suc.hyps(2) Suc.prems(1) by (auto simp: vs_list_def)
  have up: "[v..<Suc n] = v # [Suc v..<Suc n]" using vn by (simp add: upt_conv_Cons)
  note M = phase2_step_mono[OF vs Suc.prems(3,4)]
  have rest: "set [Suc v..<Suc n] \<subseteq> set vs_list" by (auto simp: vs_list_def)
  have M1: "dfs_inv acyc_flow (phase2_step acyc_flow v s)" "ds_stk (phase2_step acyc_flow v s) = []"
    using M by simp_all
  note P6 = Suc.prems(6)[unfolded up fold_Cons o_apply]
  have room1: "ds_nxt (phase2_step acyc_flow v s) \<le> length vs_list"
    by (rule order.trans[OF fold_nxt_mono[where g = "phase2_step acyc_flow", OF _ rest M1] P6])
       (rule phase2_step_mono; assumption)
  have al1: "art_len (phase2_step acyc_flow v s)" by (rule phase2_step_art_len[OF vs Suc.prems(3,5)])
  have IH: "<dfs_rel fl0 es0 st (phase2_step acyc_flow v s) * imb_arr \<mapsto>\<^sub>a imbalance> phase2_imp st imb_arr m vcount (Suc v) n
         <\<lambda>_. dfs_rel fl0 es0 st (fold (phase2_step acyc_flow) [v..<Suc n] s) * imb_arr \<mapsto>\<^sub>a imbalance>"
    unfolding up fold_Cons o_apply
    by (rule Suc.hyps(1)[OF _ _ _ M1 al1 P6]) (use Suc.hyps(2) vn in simp_all)
  show ?case
    using vn by (subst phase2_imp.simps) (sep_auto heap: phase2_step_imp_rule[OF vs Suc.prems(3,4,5) room1] IH)
qed

subsection \<open>Layer (d.8): assembling @{const build_tree_imp}\<close>

text \<open>Seeding the root: the four initial writes take the freshly allocated state to @{const dfs_init}.\<close>

lemma build_tree_seed_cps:
  assumes K: "<dfs_rel fl0 es0 st dfs_init * Fr> K <Q>"
  shows "<dfs_rel fl0 es0 st (dfs_init\<lparr>ds_snum := replicate (Suc vcount) 0, ds_prev := 0\<rparr>) * Fr>
         do { _ \<leftarrow> array_fun_upd_imp (snum_impl (di_tree st)) vcount 1;
              _ \<leftarrow> Ref.update (di_prev st) vcount;
              _ \<leftarrow> Ref.update (di_nxt st) 0;
              _ \<leftarrow> Ref.update (di_sp st) 0;
              K }
         <Q>"
proof -
  have "<dfs_rel fl0 es0 st (dfs_init\<lparr>ds_snum := replicate (Suc vcount) 0, ds_prev := 0\<rparr>)>
         do { _ \<leftarrow> array_fun_upd_imp (snum_impl (di_tree st)) vcount 1;
              _ \<leftarrow> Ref.update (di_prev st) vcount;
              _ \<leftarrow> Ref.update (di_nxt st) 0;
              Ref.update (di_sp st) 0 }
         <\<lambda>_. dfs_rel fl0 es0 st dfs_init>"
    unfolding dfs_rel_def by (sep_auto simp: dfs_init_def)
  from ht_bind[OF ht_frame[OF this, where R = Fr] K] show ?thesis
    by (simp only: bind_bind)
qed

text \<open>The root finalisation: its last successor is the last vertex emitted.\<close>

lemma dfs_rel_root_lsuc:
  assumes "length (ds_lsuc s) = Suc vcount"
  shows "<dfs_rel fl0 es0 st s> do { pv \<leftarrow> Ref.lookup (di_prev st); array_fun_upd_imp (lsuc_impl (di_tree st)) vcount pv }
         <\<lambda>_. dfs_rel fl0 es0 st (s\<lparr>ds_lsuc := (ds_lsuc s)[vcount := ds_prev s]\<rparr>)>"
  unfolding dfs_rel_def using assms by sep_auto

text \<open>The builder refines @{const build_tree}, from the freshly allocated arrays.\<close>

lemma build_tree_imp_rule:
  "<dfs_rel fl0 es0 st (dfs_init\<lparr>ds_snum := replicate (Suc vcount) 0, ds_prev := 0\<rparr>) * imb_arr \<mapsto>\<^sub>a imbalance>
     build_tree_imp st imb_arr m vcount n
   <\<lambda>_. dfs_rel fl0 es0 st (build_tree acyc_flow) * imb_arr \<mapsto>\<^sub>a imbalance>"
proof -
  have vs: "vs_list = [Suc 0..<Suc n]" by (simp add: vs_list_def)
  have i0: "dfs_inv acyc_flow dfs_init" "ds_stk dfs_init = []" "art_len dfs_init"
    by (simp_all only: dfs_init_inv dfs_init_art_len) (simp add: dfs_init_def)
  define s1 where "s1 = phase1 acyc_flow dfs_init"
  have p1: "dfs_inv acyc_flow s1 \<and> ds_stk s1 = []" unfolding s1_def by (rule phase1_inv) (simp add: i0)
  have a1: "art_len s1" unfolding s1_def by (rule phase1_art_len) (simp_all add: i0)
  have bt: "build_tree acyc_flow = (phase2 acyc_flow s1)\<lparr>ds_lsuc := (ds_lsuc (phase2 acyc_flow s1))[vcount := ds_prev (phase2 acyc_flow s1)]\<rparr>"
    by (simp add: build_tree_def s1_def Let_def)
  have n2: "ds_nxt (phase2 acyc_flow s1) \<le> length vs_list" using build_tree_nxt_le bt by simp
  have n1: "ds_nxt s1 \<le> length vs_list"
    using fold_nxt_mono[where g = "phase2_step acyc_flow", OF phase2_step_mono order.refl] p1 n2 by (fastforce simp: phase2_def)
  have R1: "<dfs_rel fl0 es0 st dfs_init * imb_arr \<mapsto>\<^sub>a imbalance> phase1_imp st imb_arr m vcount 1 n
            <\<lambda>_. dfs_rel fl0 es0 st s1 * imb_arr \<mapsto>\<^sub>a imbalance>"
    unfolding s1_def phase1_def One_nat_def
    by (rule phase1_imp_rule[where v = "Suc 0", folded vs]) (use i0 n1[unfolded s1_def phase1_def] in simp_all)
  have R2: "<dfs_rel fl0 es0 st s1 * imb_arr \<mapsto>\<^sub>a imbalance> phase2_imp st imb_arr m vcount 1 n
            <\<lambda>_. dfs_rel fl0 es0 st (phase2 acyc_flow s1) * imb_arr \<mapsto>\<^sub>a imbalance>"
    unfolding phase2_def One_nat_def
    by (rule phase2_imp_rule[where v = "Suc 0", folded vs]) (use p1 a1 n2[unfolded phase2_def] in simp_all)
  have ll: "length (ds_lsuc (phase2 acyc_flow s1)) = Suc vcount"
    using phase2_inv[OF p1] by (simp add: dfs_inv_def dfs_sized_def)
  show ?thesis
    unfolding build_tree_imp_def bt
    by (rule build_tree_seed_cps, rule ht_bind[OF R1], rule ht_bind[OF R2],
        rule ht_frame[OF dfs_rel_root_lsuc[OF ll]])
qed


subsection \<open>Layer (e): the concrete spanning-tree operations refine the arborescence ADT\<close>

text \<open>The three tree operations the network-simplex loop calls --- @{const ns_swap_edge_imp},
      @{const ns_get_path_pair_imp}, @{const ns_shift_pot_imp} --- are ported from the verified
      @{typ ndtree_impl} primitives of \<open>Rooted_Arborescense_Refinement\<close>.  Their imperative Hoare rules
      here match, one-for-one, the abstract @{locale arborescense_adt} axioms that
      @{locale network_simplex_impl_refine} assumes (with @{const ndtree_assn} for the tree assertion and
      the inherited @{const arb_invar} / @{const abstract_arb} / @{const get_path_pair_impl} /
      @{const swap_edge_impl} for the abstract side), so they discharge those axioms in the Layer (e)
      interpretation.\<close>

text \<open>A fill-pointer never overruns its array: if the prefix @{term \<open>take n zs\<close>} equals a list of
      length @{term n}, then @{term \<open>n \<le> length zs\<close>}.\<close>
lemma take_len_bound: "take n zs = ws \<Longrightarrow> length ws = n \<Longrightarrow> n \<le> length zs"
  by (metis length_take min.bounded_iff order_refl)

text \<open>Tree-edge swap: compute the join of the entering edge's endpoints (@{thm join_of_imp_correct}) and
      hand it to @{const update_tree_imp}.  The abstract swap-edge preconditions (a fundamental-circuit
      walk through the entering edge) are exactly those of @{thm swap_edge_axiom1}; we reuse its
      derivation to place @{term x} on @{term u}'s root-path below the join (@{text xfu}), off the root
      (@{text xnr}), with the join itself in the tree (@{text jnV}) --- the premises of
      @{thm update_tree_imp_rule}.\<close>
lemma ns_swap_edge_imp_rule:
  assumes inv: "arb_invar rt Vt S" and gp: "get_path_pair_impl S u v = (p1, p2)"
    and une: "u \<noteq> v" and wu: "walk_betw (abstract_arb S) u (p1 @ a # p3) rt"
    and dist: "distinct (p1 @ a # p3)" and em: "(x, y) \<in> set (edges_of_vwalk (p1 @ [a]))"
    and uV: "u \<in> Vt" and vV: "v \<in> Vt"
  shows "<ndtree_assn Vt S Ti> ns_swap_edge_imp Ti x u v
           <\<lambda>_. ndtree_assn Vt (swap_edge_impl S x u v) Ti>"
proof -
  have rinv: "rooted_arborescense_invar rt Vt (prnt S)" using inv unfolding arb_invar_def by simp
  have ps: "parent_spec (prnt S)" by (rule rooted_arborescense_invar_parent_spec[OF rinv])
  have wfu: "p1 @ a # p3 = follow (prnt S) u" by (rule unique_walk_to_root[OF inv uV wu dist])
  define j where "j = join_of (prnt S) u v"
  have fu_split: "follow (prnt S) u = p1 @ follow (prnt S) j"
    using get_path_pair_impl_correct(1)[OF inv uV vV gp] by (simp add: j_def)
  have p1ne: "p1 \<noteq> []"
  proof (rule ccontr)
    assume "\<not> p1 \<noteq> []" hence "p1 = []" by simp
    hence "edges_of_vwalk (p1 @ [a]) = []" by simp
    thus False using em by simp
  qed
  have ev_dec: "edges_of_vwalk (p1 @ [a]) = edges_of_vwalk p1 @ [(last p1, a)]"
    using edges_of_vwalk_append_3[OF p1ne, of "[a]"] p1ne by simp
  have xp1: "x \<in> set p1"
  proof -
    from em ev_dec have "(x, y) \<in> set (edges_of_vwalk p1) \<or> (x, y) = (last p1, a)" by auto
    thus ?thesis
    proof
      assume "(x, y) \<in> set (edges_of_vwalk p1)" thus ?thesis using v_in_edge_in_vwalk by fast
    next
      assume "(x, y) = (last p1, a)" thus ?thesis using p1ne last_in_set by auto
    qed
  qed
  have xfu: "x \<in> set (follow (prnt S) u)" using xp1 wfu by (metis Un_iff set_append)
  have fjne: "follow (prnt S) j \<noteq> []" by (rule follow_ne_ps[OF ps])
  have jinfj: "j \<in> set (follow (prnt S) j)" using fjne follow_hd_ps[OF ps, of j] by (metis hd_in_set)
  have jfu: "j \<in> set (follow (prnt S) u)" using fu_split jinfj by simp
  have jnV: "j \<in> Vt" using follow_subset_V[OF rinv uV] jfu by auto
  have du: "distinct (follow (prnt S) u)" by (rule follow_distinct_ps[OF ps])
  have disjp1fj: "set p1 \<inter> set (follow (prnt S) j) = {}"
    using du fu_split by (simp add: distinct_append)
  have rinfj: "rt \<in> set (follow (prnt S) j)"
    using follow_last_root[OF inv jnV] fjne by (metis last_in_set)
  have xnr: "x \<noteq> rt" using xp1 rinfj disjp1fj by auto
  have jnV': "join_of (prnt S) u v \<in> Vt" using jnV j_def by simp
  show ?thesis
    unfolding ns_swap_edge_imp_def swap_edge_impl_def
    apply (rule ht_bind[OF join_of_imp_correct[OF inv uV vV]])
    apply (sep_auto heap: update_tree_imp_rule[OF inv uV vV xfu jnV' xnr])
    done
qed

text \<open>Fundamental-circuit path search: the verified @{const get_path_pair_imp} with the two caller path
      arrays moved after the endpoints.  The two arrays hold a longest tree path (@{term \<open>card Vt - 1\<close>}
      entries), the fill pointers are @{term \<open>length p1\<close>} / @{term \<open>length p2\<close>}, and the array prefixes
      become the functional branch paths @{term \<open>get_path_pair_impl S u v\<close>}.  The two length bounds
      @{term \<open>length p_i \<le> length l_i\<close>} follow from @{thm take_len_bound}; the final existential is
      introduced explicitly (@{thm ent_ex_postI}) since @{method sep_auto}'s entailment solver loops on
      the framed @{term true}.\<close>
lemma ns_get_path_pair_imp_rule:
  assumes inv: "arb_invar rt Vt S" and une: "u \<noteq> v" and uV: "u \<in> Vt" and vV: "v \<in> Vt"
    and l1: "card Vt - 1 \<le> length xs1" and l2: "card Vt - 1 \<le> length xs2"
  shows "<ndtree_assn Vt S Ti * a1 \<mapsto>\<^sub>a xs1 * a2 \<mapsto>\<^sub>a xs2>
           ns_get_path_pair_imp Ti u v a1 a2
         <\<lambda>(ptr1, ptr2). \<exists>\<^sub>A l1' l2'. ndtree_assn Vt S Ti * a1 \<mapsto>\<^sub>a l1' * a2 \<mapsto>\<^sub>a l2' *
             \<up>(length l1' = length xs1 \<and> length l2' = length xs2 \<and>
               ptr1 \<le> length l1' \<and> ptr2 \<le> length l2' \<and>
               (take ptr1 l1', take ptr2 l2') = get_path_pair_impl S u v)>"
proof -
  obtain p1 p2 where pp: "get_path_pair_impl S u v = (p1, p2)"
    by (cases "get_path_pair_impl S u v") auto
  have len1: "card Vt \<le> Suc (length xs1)" using l1 by linarith
  have len2: "card Vt \<le> Suc (length xs2)" using l2 by linarith
  show ?thesis
    unfolding ns_get_path_pair_imp_def
    apply (sep_auto heap: get_path_pair_imp_rule[OF inv uV vV len1 len2 pp] simp: pp)
    subgoal premises prems for a b ys1 ys2
    proof -
      have b1: "length p1 \<le> length ys1"
        using prems(4) by (metis length_take min.bounded_iff order_refl)
      have b2: "length p2 \<le> length ys2"
        using prems(5) by (metis length_take min.bounded_iff order_refl)
      have cond: "length ys1 = length xs1 \<and> length ys2 = length xs2 \<and>
                  length p1 \<le> length ys1 \<and> length p2 \<le> length ys2 \<and>
                  take (length p1) ys1 = p1 \<and> take (length p2) ys2 = p2"
        using prems(2) prems(3) prems(4) prems(5) b1 b2 by blast
      have ent: "ndtree_assn Vt S Ti * a1 \<mapsto>\<^sub>a ys1 * a2 \<mapsto>\<^sub>a ys2 * true
                 \<Longrightarrow>\<^sub>A (\<exists>\<^sub>A l1' l2'. ndtree_assn Vt S Ti * a1 \<mapsto>\<^sub>a l1' * a2 \<mapsto>\<^sub>a l2' * true *
                     \<up>(length l1' = length xs1 \<and> length l2' = length xs2 \<and>
                       length p1 \<le> length l1' \<and> length p2 \<le> length l2' \<and>
                       take (length p1) l1' = p1 \<and> take (length p2) l2' = p2))"
        apply (rule ent_ex_postI[where x = ys1], rule ent_ex_postI[where x = ys2])
        apply (subst ent_pure_post_iff)
        apply (intro conjI)
         apply (rule ent_refl)
        using cond apply blast
        done
      show ?thesis by (rule entailsD[OF ent prems(1)])
    qed
    done
qed

text \<open>Functional bridge: the branch-free potential walk @{const shift_pot_impl} is a subtree fold over
      the thread block opposed to the root --- i.e. @{const iterate_root_opposed_impl} with the per-node
      read/shift/write step.  The block decomposition (@{thm block_props}) supplies the
      \<open>follow (thrd S) v = bl @ lsuc S v # rest\<close> split with \<open>lsuc S v \<notin> set bl\<close> that
      @{thm shift_pot_up_loop_subtree_fold} / @{thm shift_pot_down_loop_subtree_fold} need.\<close>
lemma shift_pot_impl_iterate:
  assumes inv: "arb_invar rt Vt S" and vV: "v \<in> Vt"
  shows "shift_pot_impl S v pl g up
       = iterate_root_opposed_impl S v
           (\<lambda>x acc. acc[x := if up then pval_plus (acc ! x) g else pval_minus (acc ! x) g]) pl"
proof -
  have pst: "parent_spec (thrd S)" using inv unfolding arb_invar_def by simp
  have bne: "block S v \<noteq> []" by (rule block_props(2)[OF inv vV])
  have blast': "last (block S v) = lsuc S v" by (rule block_props(3)[OF inv vV])
  have decomp: "follow (thrd S) v
                  = block S v @ (case thrd S (lsuc S v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S) w)"
    by (rule block_props(1)[OF inv vV])
  define bl where "bl = butlast (block S v)"
  have blk: "block S v = bl @ [lsuc S v]"
    unfolding bl_def using append_butlast_last_id[OF bne] blast' by simp
  define rest where "rest = (case thrd S (lsuc S v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S) w)"
  have L: "follow (thrd S) v = bl @ (lsuc S v) # rest" using decomp blk rest_def by simp
  have distf: "distinct (follow (thrd S) v)" by (rule follow_distinct_ps[OF pst])
  have notin: "lsuc S v \<notin> set bl" using distf L by (auto simp: distinct_append)
  show ?thesis
  proof (cases up)
    case True
    have "shift_pot_impl S v pl g up = shift_pot_up_loop S (lsuc S v) g v pl"
      by (simp add: shift_pot_impl_def True)
    also have "\<dots> = subtree_fold S (lsuc S v) v (\<lambda>x acc. acc[x := pval_plus (acc ! x) g]) pl"
      by (rule shift_pot_up_loop_subtree_fold[OF pst L notin])
    also have "\<dots> = iterate_root_opposed_impl S v
                     (\<lambda>x acc. acc[x := if up then pval_plus (acc ! x) g else pval_minus (acc ! x) g]) pl"
      by (simp add: iterate_root_opposed_impl_def True)
    finally show ?thesis .
  next
    case False
    have "shift_pot_impl S v pl g up = shift_pot_down_loop S (lsuc S v) g v pl"
      by (simp add: shift_pot_impl_def False)
    also have "\<dots> = subtree_fold S (lsuc S v) v (\<lambda>x acc. acc[x := pval_minus (acc ! x) g]) pl"
      by (rule shift_pot_down_loop_subtree_fold[OF pst L notin])
    also have "\<dots> = iterate_root_opposed_impl S v
                     (\<lambda>x acc. acc[x := if up then pval_plus (acc ! x) g else pval_minus (acc ! x) g]) pl"
      by (simp add: iterate_root_opposed_impl_def False)
    finally show ?thesis .
  qed
qed

text \<open>Potential shift: the subtree-fold refinement @{thm iterate_root_opposed_imp_rule} instantiated at
      the read/shift/write per-node step, with the array-length invariant @{term \<open>\<forall>w\<in>Vt. w < length acc\<close>}
      carried in the fold relation @{term R} (so every visited @{term \<open>x \<in> Vt\<close>} is in range).  The
      resulting functional value @{term \<open>iterate_root_opposed_impl S v f pl\<close>} is @{const shift_pot_impl}
      by @{thm shift_pot_impl_iterate}.\<close>
lemma ns_shift_pot_imp_rule:
  assumes inv: "arb_invar rt Vt S" and vV: "v \<in> Vt" and pinv: "\<forall>w\<in>Vt. w < length pl"
  shows "<ndtree_assn Vt S Ti * pa \<mapsto>\<^sub>a pl>
           ns_shift_pot_imp Ti v pa g up
         <\<lambda>_. ndtree_assn Vt S Ti * pa \<mapsto>\<^sub>a shift_pot_impl S v pl g up>"
proof -
  define f where "f = (\<lambda>x acc. acc[x := if up then pval_plus (acc ! x) g else pval_minus (acc ! x) g])"
  define R where "R = (\<lambda>(_::unit) acc. pa \<mapsto>\<^sub>a acc * \<up>(\<forall>w\<in>Vt. w < length acc))"
  have fi: "\<And>x a. x \<in> Vt \<Longrightarrow>
             <R () a>
               (\<lambda>x (_::unit). do { p \<leftarrow> Array.nth pa x;
                                   _ \<leftarrow> Array.upd x (if up then pval_plus p g else pval_minus p g) pa;
                                   return () }) x ()
             <\<lambda>_. R () (f x a)>"
  proof -
    fix x a assume xV: "x \<in> Vt"
    show "<R () a>
            (\<lambda>x (_::unit). do { p \<leftarrow> Array.nth pa x;
                                _ \<leftarrow> Array.upd x (if up then pval_plus p g else pval_minus p g) pa;
                                return () }) x ()
          <\<lambda>_. R () (f x a)>"
      unfolding R_def f_def by (sep_auto simp: xV)
  qed
  have main: "<ndtree_assn Vt S Ti * R () pl>
                ns_shift_pot_imp Ti v pa g up
              <\<lambda>_. ndtree_assn Vt S Ti * R () (iterate_root_opposed_impl S v f pl)>"
    unfolding ns_shift_pot_imp_def
    apply (rule iterate_root_opposed_imp_rule[where R = R and f = f and ai = "()"])
      apply (rule inv)
     apply (rule vV)
    apply (rule fi)
    apply assumption
    done
  have R_pl: "ndtree_assn Vt S Ti * pa \<mapsto>\<^sub>a pl \<Longrightarrow>\<^sub>A ndtree_assn Vt S Ti * R () pl"
    unfolding R_def using pinv by sep_auto
  have R_res: "\<And>u. ndtree_assn Vt S Ti * R () (iterate_root_opposed_impl S v f pl)
              \<Longrightarrow>\<^sub>A ndtree_assn Vt S Ti * pa \<mapsto>\<^sub>a shift_pot_impl S v pl g up"
    unfolding R_def shift_pot_impl_iterate[OF inv vV] f_def[symmetric] by sep_auto
  show ?thesis
    by (rule ht_cons_prec[OF R_pl R_res main])
qed

subsection \<open>Layer (e): the entering-edge selector refines @{const sel_select_impl}\<close>

text \<open>The cost part of a reduced-cost descriptor: a real cost cell @{term \<open>(M_0, cost_list ! e)\<close>} for a
      genuine edge (@{term \<open>e < m\<close>}), the big-M unit @{const pval_M} for an artificial one.  Reads the
      cost array only on the genuine branch, exactly where @{const cost_pval} does.\<close>
lemma cost_pval_imp_rule:
  assumes ce: "e < m \<Longrightarrow> e < length col \<and> col ! e = cost_list ! e"
  shows "<cost_arr \<mapsto>\<^sub>a col> cost_pval_imp m cost_arr e
           <\<lambda>r. cost_arr \<mapsto>\<^sub>a col * \<up>(r = cost_pval e)>"
  unfolding cost_pval_imp_def cost_pval_def
  using ce by (cases "e < m") sep_auto+

text \<open>One-arc pricing: @{const evaluate_imp} reads the two endpoints (@{term \<open>fst_all ! e\<close>} /
      @{term \<open>snd_all ! e\<close>}), the edge tag and --- off a self-loop --- the reduced cost, exactly the
      functional @{const evaluate}.  A self-loop is ineligible without pricing; otherwise the M-free sign
      test on the assembled descriptor gives eligibility, alongside the @{term \<open>InU\<close>} flag and the
      descriptor itself.\<close>
lemma evaluate_imp_rule:
  assumes fae: "e < length fstl" and sae: "e < length sndl"
    and cvce: "e < m \<Longrightarrow> e < length col \<and> col ! e = cost_list ! e"
    and esle: "e < length esl"
    and pa: "fst_all ! e < length \<pi>" and pd: "snd_all ! e < length \<pi>"
    and fok: "fstl ! e = fst_all ! e" and sok: "sndl ! e = snd_all ! e"
  shows "<fst_arr \<mapsto>\<^sub>a fstl * snd_arr \<mapsto>\<^sub>a sndl * cost_arr \<mapsto>\<^sub>a col * es_arr \<mapsto>\<^sub>a esl * pt \<mapsto>\<^sub>a \<pi>>
           evaluate_imp m fst_arr snd_arr cost_arr es_arr pt e
         <\<lambda>r. fst_arr \<mapsto>\<^sub>a fstl * snd_arr \<mapsto>\<^sub>a sndl * cost_arr \<mapsto>\<^sub>a col * es_arr \<mapsto>\<^sub>a esl * pt \<mapsto>\<^sub>a \<pi>
              * \<up>(r = evaluate esl \<pi> e)>"
  unfolding evaluate_imp_def evaluate_def Let_def
  using fae sae esle pa pd
  by (sep_auto simp: fok sok split: edge_tag.splits heap: cost_pval_imp_rule[OF cvce])

text \<open>Minor iteration: one pass over the live cache prefix @{term \<open>[i..<len]\<close>}, pricing each entry with
      @{const evaluate_imp}, keeping the eligible ones (advancing @{term i} and the running best) and
      deleting duds by swap-with-last.  Refines @{const scan_cache}: the imperative returns the final
      length / best while the cache array is left holding the functional result array.  Structural
      induction on the measure @{term \<open>len - i\<close>}, mirroring the fold-refinement style: one
      @{method sep_auto} with @{text \<open>split: if_splits\<close>} over the single functional unfolding \<open>scu\<close>,
      with both recursive calls discharged by the induction hypothesis.\<close>
lemma scan_cache_imp_rule:
  assumes "i \<le> len" and "len \<le> length a"
    and "\<And>e. e \<in> set (take len a) \<Longrightarrow>
        e < length fstl \<and> e < length sndl \<and> e < length esl \<and>
        (e < m \<longrightarrow> e < length col \<and> col ! e = cost_list ! e) \<and>
        fstl ! e = fst_all ! e \<and> sndl ! e = snd_all ! e \<and>
        fst_all ! e < length \<pi> \<and> snd_all ! e < length \<pi>"
  shows "<sarr \<mapsto>\<^sub>a a * es_arr \<mapsto>\<^sub>a esl * pt \<mapsto>\<^sub>a \<pi> * fst_arr \<mapsto>\<^sub>a fstl * snd_arr \<mapsto>\<^sub>a sndl * cost_arr \<mapsto>\<^sub>a col>
           scan_cache_imp m fst_arr snd_arr cost_arr es_arr pt sarr i len best
         <\<lambda>r. case scan_cache esl \<pi> i a len best of (a', rl, rb) \<Rightarrow>
                sarr \<mapsto>\<^sub>a a' * es_arr \<mapsto>\<^sub>a esl * pt \<mapsto>\<^sub>a \<pi> * fst_arr \<mapsto>\<^sub>a fstl
                * snd_arr \<mapsto>\<^sub>a sndl * cost_arr \<mapsto>\<^sub>a col * \<up>(r = (rl, rb))>"
  using assms
proof (induction "len - i" arbitrary: i len a best rule: less_induct)
  case less
  have mem_take: "\<And>j. j < len \<Longrightarrow> a ! j \<in> set (take len a)"
  proof -
    fix j assume j: "j < len"
    have "j < length (take len a)" using j less.prems(2) by simp
    hence "take len a ! j \<in> set (take len a)" by (rule nth_mem)
    thus "a ! j \<in> set (take len a)" using j by (simp add: nth_take)
  qed
  show ?case
  proof (cases "len \<le> i")
    case True
    show ?thesis
      by (subst scan_cache_imp.simps, subst scan_cache.simps) (sep_auto simp: True)
  next
    case False
    note lenF = False
    hence ilt: "i < len" by simp
    have iltl: "i < length a" using ilt less.prems(2) by simp
    have lenl: "len - 1 < length a" using ilt less.prems(2) by simp
    obtain elig u g where ev: "evaluate esl \<pi> (a ! i) = (elig, u, g)"
      by (cases "evaluate esl \<pi> (a ! i)") auto
    note eok = less.prems(3)[OF mem_take[OF ilt]]
    have eok1: "a ! i < length fstl" and eok2: "a ! i < length sndl"
      and eok3: "a ! i < length esl"
      and eok4: "a ! i < m \<Longrightarrow> a ! i < length col \<and> col ! (a ! i) = cost_list ! (a ! i)"
      and eokf: "fstl ! (a ! i) = fst_all ! (a ! i)" and eoks: "sndl ! (a ! i) = snd_all ! (a ! i)"
      and eok5: "fst_all ! (a ! i) < length \<pi>" and eok6: "snd_all ! (a ! i) < length \<pi>"
      using eok by auto
    note evr = evaluate_imp_rule[OF eok1 eok2 eok4 eok3 eok5 eok6 eokf eoks]
    have pref: "set (take (len - 1) a) \<subseteq> set (take len a)"
    proof -
      have "take (len - 1) a = take (len - 1) (take len a)" by (simp add: take_take)
      moreover have "set (take (len - 1) (take len a)) \<subseteq> set (take len a)" by (rule set_take_subset)
      ultimately show ?thesis by simp
    qed
    have sub: "set (take (len - 1) (a[i := a ! (len - 1)])) \<subseteq> set (take len a)"
    proof -
      have "set (take (len - 1) (a[i := a ! (len - 1)])) = set ((take (len - 1) a)[i := a ! (len - 1)])"
        by (simp add: take_update_swap)
      also have "\<dots> \<subseteq> insert (a ! (len - 1)) (set (take (len - 1) a))"
        by (rule set_update_subset_insert)
      also have "\<dots> \<subseteq> set (take len a)"
        using pref mem_take[of "len - 1"] ilt by auto
      finally show ?thesis .
    qed
    have m1: "len - Suc i < len - i" using ilt by simp
    have sle: "Suc i \<le> len" using ilt by simp
    \<comment> \<open>@{term best} is left schematic so the entering-edge tuple @{term g}, which @{method sep_auto}
        splits into a pair, still unifies through the induction hypothesis.\<close>
    note IH_elig = less.hyps[of len "Suc i" a, OF m1 sle less.prems(2) less.prems(3)]
    have m2: "len - 1 - i < len - i" using ilt by simp
    have ile: "i \<le> len - 1" using ilt by simp
    have lla2: "len - 1 \<le> length (a[i := a ! (len - 1)])" using less.prems(2) by simp
    have eok2': "\<And>e. e \<in> set (take (len - 1) (a[i := a ! (len - 1)])) \<Longrightarrow>
        e < length fstl \<and> e < length sndl \<and> e < length esl \<and>
        (e < m \<longrightarrow> e < length col \<and> col ! e = cost_list ! e) \<and>
        fstl ! e = fst_all ! e \<and> sndl ! e = snd_all ! e \<and>
        fst_all ! e < length \<pi> \<and> snd_all ! e < length \<pi>"
      using less.prems(3) sub by blast
    note IH_dud = less.hyps[of "len - 1" i "a[i := a ! (len - 1)]" best, OF m2 ile lla2 eok2']
    show ?thesis
      apply (subst scan_cache_imp.simps)
      apply (sep_auto simp: lenF ev iltl lenl lenl[unfolded One_nat_def] Let_def
                       split: if_splits heap: evr IH_elig IH_dud)
      done
  qed
qed


text \<open>Major iteration: the wrap-around block sweep from the bookmark @{term cur}, pricing each arc and
      pushing eligible ones at the length pointer, stopping on exhausted fuel, a full cache, or a
      completed block with the minimum met.  Refines @{const scan}; the cache array holds the functional
      result array.  Structural induction on the fuel; the arc-validity invariant @{term arc_ok} is
      constant (all arcs \<open>< mc\<close>) and @{term cur} stays in range by @{thm wrap_lt}.\<close>
lemma scan_imp_rule:
  assumes arc_ok: "\<And>e. e < mc \<Longrightarrow> e < length fstl \<and> e < length sndl \<and> e < length esl \<and>
        (e < m \<longrightarrow> e < length col \<and> col ! e = cost_list ! e) \<and> fstl ! e = fst_all ! e \<and> sndl ! e = snd_all ! e \<and> fst_all ! e < length \<pi> \<and> snd_all ! e < length \<pi>"
    and mcpos: "0 < mc"
  shows "cur < mc \<Longrightarrow> len \<le> max_candidates \<Longrightarrow> max_candidates \<le> length a \<Longrightarrow>
    <sarr \<mapsto>\<^sub>a a * es_arr \<mapsto>\<^sub>a esl * pt \<mapsto>\<^sub>a \<pi> * fst_arr \<mapsto>\<^sub>a fstl * snd_arr \<mapsto>\<^sub>a sndl * cost_arr \<mapsto>\<^sub>a col>
      scan_imp m fst_arr snd_arr cost_arr min_candidates max_candidates block_size mc es_arr pt sarr
               fuel bpos cur len best
    <\<lambda>r. case scan esl \<pi> mc fuel bpos cur a len best of (cur', a', len', rb) \<Rightarrow>
           sarr \<mapsto>\<^sub>a a' * es_arr \<mapsto>\<^sub>a esl * pt \<mapsto>\<^sub>a \<pi> * fst_arr \<mapsto>\<^sub>a fstl * snd_arr \<mapsto>\<^sub>a sndl * cost_arr \<mapsto>\<^sub>a col
           * \<up>(r = (cur', len', rb))>"
proof (induction fuel arbitrary: bpos cur len a best rule: less_induct)
  case (less fuel)
  note cur_mc = less.prems(1) and len_mc = less.prems(2) and lena = less.prems(3)
  show ?case
  proof (cases "fuel = 0 \<or> max_candidates \<le> len \<or> (bpos = 0 \<and> min_candidates \<le> len)")
    case True
    have imp_eq: "scan_imp m fst_arr snd_arr cost_arr min_candidates max_candidates block_size mc
                    es_arr pt sarr fuel bpos cur len best = Heap_Monad.return (cur, len, best)"
      using True by (subst scan_imp.simps) auto
    have fun_eq: "scan esl \<pi> mc fuel bpos cur a len best = (cur, a, len, best)"
      using True by (subst scan.simps) auto
    show ?thesis unfolding imp_eq fun_eq by sep_auto
  next
    case False
    hence g1: "fuel \<noteq> 0" and g2: "\<not> max_candidates \<le> len"
      and g3: "\<not> (bpos = 0 \<and> min_candidates \<le> len)" by auto
    have lla: "len < length a" using g2 len_mc lena by simp
    note aok = arc_ok[OF cur_mc]
    have aok1: "cur < length fstl" and aok2: "cur < length sndl" and aok3: "cur < length esl"
      and aok4: "cur < m \<Longrightarrow> cur < length col \<and> col ! cur = cost_list ! cur"
      and aokf: "fstl ! cur = fst_all ! cur" and aoks: "sndl ! cur = snd_all ! cur"
      and aok5: "fst_all ! cur < length \<pi>" and aok6: "snd_all ! cur < length \<pi>"
      using aok by auto
    note evr = evaluate_imp_rule[OF aok1 aok2 aok4 aok3 aok5 aok6 aokf aoks]
    obtain elig u g where ev: "evaluate esl \<pi> cur = (elig, u, g)"
      by (cases "evaluate esl \<pi> cur") auto
    have m1: "fuel - 1 < fuel" using g1 by simp
    have suclen_mc: "Suc len \<le> max_candidates" using g2 len_mc by simp
    have lena_upd: "max_candidates \<le> length (a[len := cur])" using lena by simp
    \<comment> \<open>Keep the wrap-around @{term cur1} and block-reset @{term bpos1} \<^emph>\<open>opaque\<close> (as defined
        constants), so the simplifier does not split their ifs and break the induction-hypothesis
        match; the ifs are folded into the program by \<open>cur1_def[symmetric]\<close> / \<open>bpos1_def[symmetric]\<close>.
        The IHs are unfolded past @{thm One_nat_def} so their \<open>fuel - 1\<close> matches the \<open>fuel - Suc 0\<close>
        the simplifier produces.  @{term best} stays schematic for the split entering-edge tuple.\<close>
    define cur1 where "cur1 = (if cur + 1 = mc then 0 else cur + 1)"
    define bpos1 where "bpos1 = (if bpos = 0 then block_size else bpos)"
    have cur1_mc: "cur1 < mc" unfolding cur1_def by (rule wrap_lt[OF mcpos cur_mc])
    note IH_elig = less.IH[OF m1 cur1_mc suclen_mc lena_upd]
    note IH_nelig = less.IH[OF m1 cur1_mc len_mc lena]
    have scu: "scan esl \<pi> mc fuel bpos cur a len best
                 = scan esl \<pi> mc (fuel - 1) (bpos1 - 1) cur1 (if elig then a[len := cur] else a)
                        (if elig then Suc len else len) (if elig then better best (cur, u, g) else best)"
      unfolding cur1_def bpos1_def by (subst scan.simps) (simp add: g1 g2 g3 ev Let_def)
    show ?thesis
      supply scan.simps[simp del]
      apply (subst scan_imp.simps)
      apply (simp only: if_not_P[OF g1] if_not_P[OF g2] if_not_P[OF g3]
                        cur1_def[symmetric] bpos1_def[symmetric])
      apply (sep_auto simp: ev lla lla[unfolded One_nat_def] Let_def scu
                       split: if_splits heap: evr IH_elig IH_nelig)
      apply (sep_auto simp: Let_def scu ev
                       heap: IH_elig[unfolded One_nat_def] IH_nelig[unfolded One_nat_def])+
      done
  qed
qed


subsection \<open>Layer (e): the entering-edge selector assembles the two scans\<close>

text \<open>The selector state relation: the fixed-capacity backing array, the block bookmark and the
      live-prefix pointer of the functional @{typ ns_sel} record are held by the array @{term sarr} and
      the two references @{term cref} / @{term lref}.\<close>
definition sel_assn_ns :: "ns_sel \<Rightarrow> ns_sel_imp \<Rightarrow> assn" where
  "sel_assn_ns sel s = (case s of (sarr, cref, lref) \<Rightarrow>
     sarr \<mapsto>\<^sub>a sel_arr sel * cref \<mapsto>\<^sub>r sel_cur sel * lref \<mapsto>\<^sub>r sel_len sel)"

text \<open>@{const ns_sel_select_imp} refines @{const sel_select_impl}: minor iteration over the cache
      (@{const scan_cache_imp}), and on failure a major block sweep (@{const scan_imp}), committing the
      pointers on a hit.  On @{term None} the cache has been rearranged (stale candidates pruned), so the
      store now represents \<^emph>\<open>some\<close> selector --- exactly the existential the weakened ADT axiom demands.\<close>
lemma ns_sel_select_imp_rule:
  assumes inv: "sel_invar_impl sel" and mcpos: "0 < marc"
    and arc_ok: "\<And>e. e < marc \<Longrightarrow> e < length fstl \<and> e < length sndl \<and> e < length esl \<and>
        (e < m \<longrightarrow> e < length col \<and> col ! e = cost_list ! e) \<and> fstl ! e = fst_all ! e \<and> sndl ! e = snd_all ! e \<and> fst_all ! e < length \<pi> \<and> snd_all ! e < length \<pi>"
  shows "<sel_assn_ns sel (sarr, cref, lref) * es_arr \<mapsto>\<^sub>a esl * pt \<mapsto>\<^sub>a \<pi>
          * fst_arr \<mapsto>\<^sub>a fstl * snd_arr \<mapsto>\<^sub>a sndl * cost_arr \<mapsto>\<^sub>a col>
           ns_sel_select_imp m marc block_size min_candidates max_candidates fst_arr snd_arr cost_arr
                             (sarr, cref, lref) pt es_arr
         <\<lambda>res. es_arr \<mapsto>\<^sub>a esl * pt \<mapsto>\<^sub>a \<pi> * fst_arr \<mapsto>\<^sub>a fstl * snd_arr \<mapsto>\<^sub>a sndl * cost_arr \<mapsto>\<^sub>a col
            * (case sel_select_impl sel \<pi> esl of
                 None \<Rightarrow> (\<exists>\<^sub>A ss. sel_assn_ns ss (sarr, cref, lref)) * \<up>(res = None)
               | Some (e, in_U, \<gamma>, sel') \<Rightarrow>
                   sel_assn_ns sel' (sarr, cref, lref) * \<up>(res = Some (e, in_U, \<gamma>)))>"
proof -
  from inv have larr: "length (sel_arr sel) = max_candidates"
    and lenmax: "sel_len sel \<le> max_candidates"
    and curlt: "0 < marc \<longrightarrow> sel_cur sel < marc"
    and rng: "set (take (sel_len sel) (sel_arr sel)) \<subseteq> {0..<marc}"
    by (auto simp: sel_invar_impl_def)
  have curm: "sel_cur sel < marc" using curlt mcpos by simp
  have lenl: "sel_len sel \<le> length (sel_arr sel)" using lenmax larr by simp
  \<comment> \<open>Each cached candidate is a genuine arc \<open>< marc\<close>, so the arc-validity invariant applies.\<close>
  have eok_cache: "\<And>e. e \<in> set (take (sel_len sel) (sel_arr sel)) \<Longrightarrow>
      e < length fstl \<and> e < length sndl \<and> e < length esl \<and>
      (e < m \<longrightarrow> e < length col \<and> col ! e = cost_list ! e) \<and> fstl ! e = fst_all ! e \<and> sndl ! e = snd_all ! e \<and> fst_all ! e < length \<pi> \<and> snd_all ! e < length \<pi>"
  proof -
    fix e assume "e \<in> set (take (sel_len sel) (sel_arr sel))"
    hence "e < marc" using rng by auto
    thus "e < length fstl \<and> e < length sndl \<and> e < length esl \<and>
      (e < m \<longrightarrow> e < length col \<and> col ! e = cost_list ! e) \<and> fstl ! e = fst_all ! e \<and> sndl ! e = snd_all ! e \<and> fst_all ! e < length \<pi> \<and> snd_all ! e < length \<pi>"
      by (rule arc_ok)
  qed
  note scr = scan_cache_imp_rule[OF le0 lenl eok_cache]
  obtain a1 len1 b1 where sc: "scan_cache esl \<pi> 0 (sel_arr sel) (sel_len sel) no_best = (a1, len1, b1)"
    by (cases "scan_cache esl \<pi> 0 (sel_arr sel) (sel_len sel) no_best") auto
  \<comment> \<open>@{const scan_cache} preserves the array length and shrinks the pointer, so the major sweep's
      preconditions (\<open>len1 \<le> max_candidates\<close>, \<open>max_candidates \<le> length a1\<close>) hold.\<close>
  have sc_spec: "length a1 = length (sel_arr sel) \<and> len1 \<le> sel_len sel"
    using scan_cache_spec[OF le0 lenl bok_no_best, of esl \<pi>] sc by simp
  have a1_max: "max_candidates \<le> length a1" using sc_spec larr by simp
  have len1_max: "len1 \<le> max_candidates" using sc_spec lenmax by simp
  note scim = scan_imp_rule[OF arc_ok mcpos curm len1_max a1_max]
  show ?thesis
    supply scan_cache.simps[simp del] scan.simps[simp del]
    unfolding ns_sel_select_imp_def sel_assn_ns_def sel_select_impl_def
    apply (sep_auto simp: sc split: prod.splits if_splits heap: scr scim)
    \<comment> \<open>The @{term None} / @{term None} case: the store now holds the pruned cache @{term aa}, which is
        the selector \<open>sel\<lparr>sel_arr := aa\<rparr>\<close> --- the existential witness.\<close>
    subgoal premises prems for x1 aa ab ac ad ae af ba x1a ag ah ai bb found1 a b found2
      apply (rule entailsD[OF _ prems(7)])
      apply (rule ent_ex_postI[where x = "sel\<lparr>sel_arr := aa\<rparr>"])
      apply sep_auto
      done
    done
qed


subsection \<open>Layer (e): the network-simplex loop refines the functional loop\<close>

text \<open>The five array-backed stores of the loop state --- flow, potentials, parent edge, parent direction,
      edge tags --- are plain \<open>\<mapsto>\<^sub>a\<close> points-to assertions (the functional value \<^emph>\<open>is\<close> the array
      contents; unlike the acyclifier there is no over-allocated remainder here, since the loop operates
      on the full augmented edge / vertex ranges).  The spanning tree uses @{const ndtree_assn}, the
      selector @{const sel_assn_ns}.\<close>
definition flow_assn_ns :: "'n list \<Rightarrow> 'n array \<Rightarrow> assn" where
  "flow_assn_ns fl fh = fh \<mapsto>\<^sub>a fl"
definition pot_assn_ns :: "(mtag \<times> 'n) list \<Rightarrow> (mtag \<times> 'n) array \<Rightarrow> assn" where
  "pot_assn_ns pl ph = ph \<mapsto>\<^sub>a pl"
definition parent_assn_ns :: "nat list \<Rightarrow> nat array \<Rightarrow> assn" where
  "parent_assn_ns pe ph = ph \<mapsto>\<^sub>a pe"
definition dir_assn_ns :: "bool list \<Rightarrow> bool array \<Rightarrow> assn" where
  "dir_assn_ns d dh = dh \<mapsto>\<^sub>a d"
definition es_assn_ns :: "edge_tag list \<Rightarrow> edge_tag array \<Rightarrow> assn" where
  "es_assn_ns el eh = eh \<mapsto>\<^sub>a el"

text \<open>Re-establish the functional network-simplex interpretation at the augmented graph (the \<open>NS\<close> of
      \<open>Network_Simplex_Initial_Basis_Selector\<close> is local to its own context and not inherited here); the
      thirty-odd structural / arborescence / potential-value axioms are discharged exactly as there.\<close>
interpretation NS: network_simplex
  where fst = "\<lambda> e. if e < m+Kart then fst_all ! e else Product_Type.fst (prod_decode (e - (m+Kart)))"
    and snd = "\<lambda> e. if e < m+Kart then snd_all ! e else Product_Type.snd (prod_decode (e - (m+Kart)))"
    and create_edge = "\<lambda> u v. (m+Kart) + prod_encode (u, v)"
    and \<E> = "{0..<m+Kart}"
    and \<u> = "\<lambda> e. if e < m+Kart then (if cap_all ! e = - 1 then \<infinity> else ereal (h (cap_all ! e))) else \<infinity>"
    and \<c> = "\<lambda> e. cost_all ! e"
    and r = vcount
    and shift_pot = shift_pot_impl
    and arborescense_invar = "arb_invar vcount Varb"
    and abstract_arborescense = abstract_arb
    and get_path_pair = get_path_pair_impl
    and swap_edge = swap_edge_impl
    and flow_invar = "\<lambda>xs. \<forall>k\<in>{0..<m+Kart}. k < length xs" and flow_upd = list_update and flow_lookup = nth
    and pot_invar = "\<lambda>xs. \<forall>v\<in>Varb. v < length xs" and pot_upd = list_update and pot_lookup = nth
    and parent_invar = "\<lambda>xs. \<forall>v\<in>Varb - {vcount}. v < length xs" and parent_upd = list_update and parent_lookup = nth
    and dir_invar = "\<lambda>xs. \<forall>v\<in>Varb - {vcount}. v < length xs" and dir_upd = list_update and dir_lookup = nth
    and es_invar = "\<lambda>xs. \<forall>k\<in>{0..<m+Kart}. k < length xs" and es_upd = list_update and es_lookup = nth
    and sel_invar = sel_invar_impl and sel_select = sel_select_impl
    and b = "\<lambda> v. h (b_lookup v)"
    and cap = "\<lambda> e. cap_all ! e"
    and pot_value_invar = "\<lambda> p. good_pot_val_c p \<and> pv_invar p"
    and pot_value_abstract = "pval_abstract bigM"
    and pot_value_plus = pval_plus
    and pot_value_minus = pval_minus
    and rcost_invar = rc_invar
    and rcost_abstract = "pval_abstract bigM"
    and fst_exec = "\<lambda> e. fst_all ! e"
    and snd_exec = "\<lambda> e. snd_all ! e"
  apply unfold_locales
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal using num_edges_gtr_0 by simp
  subgoal using cap_all_nonneg by (auto simp: zero_ereal_def)
  subgoal using r_in_V NSg_verts_Varb by simp
  subgoal by (rule graph_invar_abstract_arb)
  subgoal premises p using p NSg_verts_Varb by (metis general_axiom3)
  subgoal premises p using p NSg_verts_Varb by (metis Vs_abstract_arb)
  subgoal premises p by (rule get_path_pair_axiom1[OF p(1) p(2) p(3) p(4)[simplified NSg_verts_Varb] p(5)[simplified NSg_verts_Varb]])
  subgoal premises p by (rule get_path_pair_axiom2[OF p(1) p(2) p(3) p(4)[simplified NSg_verts_Varb] p(5)[simplified NSg_verts_Varb]])
  subgoal premises p by (rule swap_edge_axiom1[OF p(1) p(2) p(3) p(4) p(5) p(6) p(7)[simplified NSg_verts_Varb] p(8)[simplified NSg_verts_Varb]])
  subgoal premises p by (rule swap_edge_axiom2[OF p(1) p(2) p(3) p(4) p(5) p(6) p(7)[simplified NSg_verts_Varb] p(8)[simplified NSg_verts_Varb]])
  subgoal by (auto simp: NSg_verts_Varb nth_fun_list_update)
  subgoal by (auto simp: NSg_verts_Varb nth_fun_list_update)
  subgoal by (auto simp: NSg_verts_Varb nth_fun_list_update)
  subgoal by (auto simp: NSg_verts_Varb nth_fun_list_update)
  subgoal by (auto simp: NSg_verts_Varb nth_fun_list_update)
  subgoal by (auto simp: NSg_verts_Varb nth_fun_list_update)
  subgoal by (auto simp: NSg_verts_Varb nth_fun_list_update)
  subgoal by (auto simp: NSg_verts_Varb nth_fun_list_update)
  subgoal by (auto simp: NSg_verts_Varb nth_fun_list_update)
  subgoal by (auto simp: NSg_verts_Varb nth_fun_list_update)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal using cap_all_nonneg by auto
  subgoal premises p for sel \<pi> es e in_U \<gamma> sel'
  proof -
    have ok: "pot_ok \<pi>" using p(3)[simplified NSg_verts_Varb] p(4) by (simp add: pot_ok_def)
    show ?thesis using sel_select_impl_Some_final[OF p(1) ok p(6)] by (auto simp: rcabs_def marc_def)
  qed
  subgoal premises p for sel \<pi> es
  proof -
    have ok: "pot_ok \<pi>" using p(3)[simplified NSg_verts_Varb] p(4) by (simp add: pot_ok_def)
    show ?thesis using sel_select_impl_None_final[OF p(1) ok p(6)] by (auto simp: rcabs_def marc_def)
  qed
  subgoal premises p for p g
  proof -
    have pv: "pv_invar p" and gc: "good_pot_val_c p" using p(1) by auto
    have rc: "rc_invar g" using p(2) .
    have cert: "\<exists>A D. A \<subseteq> {0..<m+Kart} \<and> D \<subseteq> {0..<m+Kart} \<and> card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1 \<and> pval_abstract bigM p + pval_abstract bigM g = sum ((!) cost_all) A - sum ((!) cost_all) D"
    proof -
      from p(3) obtain A D where AD: "A \<subseteq> {0..<m+Kart}" "D \<subseteq> {0..<m+Kart}"
        "card {e \<in> A \<union> D. (if e < m+Kart then fst_all ! e else fst (prod_decode (e - (m+Kart)))) = vcount \<or> (if e < m+Kart then snd_all ! e else snd (prod_decode (e - (m+Kart)))) = vcount} \<le> 1"
        "pval_abstract bigM p + pval_abstract bigM g = sum ((!) cost_all) A - sum ((!) cost_all) D" by (elim exE conjE)
      have SE: "{e \<in> A \<union> D. (if e < m+Kart then fst_all ! e else fst (prod_decode (e - (m+Kart)))) = vcount \<or> (if e < m+Kart then snd_all ! e else snd (prod_decode (e - (m+Kart)))) = vcount} = {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount}"
        using AD(1,2) by auto
      have "card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1" using AD(3) SE by simp
      thus ?thesis using AD(1,2,4) by (intro exI[of _ A] exI[of _ D]) auto
    qed
    show ?thesis using pot_plus_faithful[OF pv rc cert] good_pot_val_c_plus[OF pv rc cert] by simp
  qed
  subgoal premises p for p g
  proof -
    have pv: "pv_invar p" and gc: "good_pot_val_c p" using p(1) by auto
    have rc: "rc_invar g" using p(2) .
    have cert: "\<exists>A D. A \<subseteq> {0..<m+Kart} \<and> D \<subseteq> {0..<m+Kart} \<and> card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1 \<and> pval_abstract bigM p - pval_abstract bigM g = sum ((!) cost_all) A - sum ((!) cost_all) D"
    proof -
      from p(3) obtain A D where AD: "A \<subseteq> {0..<m+Kart}" "D \<subseteq> {0..<m+Kart}"
        "card {e \<in> A \<union> D. (if e < m+Kart then fst_all ! e else fst (prod_decode (e - (m+Kart)))) = vcount \<or> (if e < m+Kart then snd_all ! e else snd (prod_decode (e - (m+Kart)))) = vcount} \<le> 1"
        "pval_abstract bigM p - pval_abstract bigM g = sum ((!) cost_all) A - sum ((!) cost_all) D" by (elim exE conjE)
      have SE: "{e \<in> A \<union> D. (if e < m+Kart then fst_all ! e else fst (prod_decode (e - (m+Kart)))) = vcount \<or> (if e < m+Kart then snd_all ! e else snd (prod_decode (e - (m+Kart)))) = vcount} = {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount}"
        using AD(1,2) by auto
      have "card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1" using AD(3) SE by simp
      thus ?thesis using AD(1,2,4) by (intro exI[of _ A] exI[of _ D]) auto
    qed
    show ?thesis using pot_minus_faithful[OF pv rc cert] good_pot_val_c_minus[OF pv rc cert] by simp
  qed
  subgoal premises p by (rule shift_pot_impl_spec[OF p(1) p(2)[simplified NSg_verts_Varb]])
  done

text \<open>Reading one array out of a larger separation-logic frame, without the frame-inference blow-up
      @{method sep_auto} suffers when several concrete @{term \<open>(\<mapsto>\<^sub>a)\<close>} conjuncts are present.\<close>
lemma arr_read_framed:
  fixes F :: assn
  assumes "i < length xs"
  shows "<a \<mapsto>\<^sub>a xs * F> Array.nth a i <\<lambda>r. a \<mapsto>\<^sub>a xs * F * \<up>(r = xs ! i)>"
  by (rule ht_cons_post[OF ht_frame[OF nth_rule]]) sep_auto

text \<open>The whole network-simplex loop, run on the materialised imperative state, refines the functional
      @{term \<open>NS.ns_loop\<close>}.  It instantiates @{locale network_simplex_impl_refine} at the concrete
      per-store operations (array reads / writes and the four proven tree / selector refinement rules),
      re-using the theory-level @{term NS} interpretation for the functional half; @{term ns_loop_prog}
      is definitionally \<open>nsR.ns_loop_imp\<close>.  The materialisation length bounds are hypotheses,
      discharged later by the tree builder.\<close>
lemma ns_loop_prog_rule:
  fixes fst_arr snd_arr :: "nat array" and cap_arr cost_arr :: "'n array"
    and s :: "(_, _, _, _, _, _, _) network_simplex_state"
    and si :: "(_, _, _, _, _, _, _, _) ns_impl_state"
  assumes lenf: "marc \<le> length fst_all" and lens: "marc \<le> length snd_all"
    and lenc: "marc \<le> length cap_all" and lenco: "m \<le> length cost_list"
    and lenfl: "marc \<le> length fstl" and lensl: "marc \<le> length sndl" and lencl: "marc \<le> length capl"
    and fstok: "\<And>e. e < marc \<Longrightarrow> fstl ! e = fst_all ! e" and sndok: "\<And>e. e < marc \<Longrightarrow> sndl ! e = snd_all ! e"
    and capok: "\<And>e. e < marc \<Longrightarrow> capl ! e = cap_all ! e"
    and inv: "NS.ns_invar s"
  shows
   "<(cap_arr \<mapsto>\<^sub>a capl * cost_arr \<mapsto>\<^sub>a cost_list * fst_arr \<mapsto>\<^sub>a fstl * snd_arr \<mapsto>\<^sub>a sndl) *
     flow_assn_ns   (network_simplex_state.current_flow s)  (ns_impl_state.iflow si)   *
     pot_assn_ns    (network_simplex_state.potentials s)    (ns_impl_state.ipot si)     *
     ndtree_assn Varb (network_simplex_state.spanning_tree s) (ns_impl_state.itree si)  *
     parent_assn_ns (network_simplex_state.parent_edge s)   (ns_impl_state.iparent si)  *
     dir_assn_ns    (network_simplex_state.edge_dir s)      (ns_impl_state.idir si)     *
     es_assn_ns     (network_simplex_state.edge_state s)    (ns_impl_state.iestate si)  *
     sel_assn_ns    (network_simplex_state.edge_sel s)      (ns_impl_state.isel si)     *
     (\<exists>\<^sub>A l1 l2. ns_impl_state.ipath1 si \<mapsto>\<^sub>a l1 * ns_impl_state.ipath2 si \<mapsto>\<^sub>a l2 *
        \<up>(card Varb - 1 \<le> length l1 \<and> card Varb - 1 \<le> length l2))>
      ns_loop_prog vcount m marc block_size min_candidates max_candidates
                   fst_arr snd_arr cost_arr cap_arr si
    <\<lambda>res. (cap_arr \<mapsto>\<^sub>a capl * cost_arr \<mapsto>\<^sub>a cost_list * fst_arr \<mapsto>\<^sub>a fstl * snd_arr \<mapsto>\<^sub>a sndl) *
     flow_assn_ns   (network_simplex_state.current_flow (NS.ns_loop s))  (ns_impl_state.iflow si)   *
     pot_assn_ns    (network_simplex_state.potentials (NS.ns_loop s))    (ns_impl_state.ipot si)     *
     ndtree_assn Varb (network_simplex_state.spanning_tree (NS.ns_loop s)) (ns_impl_state.itree si)  *
     parent_assn_ns (network_simplex_state.parent_edge (NS.ns_loop s))   (ns_impl_state.iparent si)  *
     dir_assn_ns    (network_simplex_state.edge_dir (NS.ns_loop s))      (ns_impl_state.idir si)     *
     es_assn_ns     (network_simplex_state.edge_state (NS.ns_loop s))    (ns_impl_state.iestate si)  *
     (\<exists>\<^sub>A ss. sel_assn_ns ss (ns_impl_state.isel si)) *
     (\<exists>\<^sub>A l1 l2. ns_impl_state.ipath1 si \<mapsto>\<^sub>a l1 * ns_impl_state.ipath2 si \<mapsto>\<^sub>a l2 *
        \<up>(card Varb - 1 \<le> length l1 \<and> card Varb - 1 \<le> length l2)) *
     \<up>(res = network_simplex_state.return (NS.ns_loop s))>"
proof -
  interpret nsR: network_simplex_impl_refine
      where fst = "\<lambda> e. if e < m+Kart then fst_all ! e else Product_Type.fst (prod_decode (e - (m+Kart)))"
        and snd = "\<lambda> e. if e < m+Kart then snd_all ! e else Product_Type.snd (prod_decode (e - (m+Kart)))"
        and create_edge = "\<lambda> u v. (m+Kart) + prod_encode (u, v)"
        and \<E> = "{0..<m+Kart}"
        and \<u> = "\<lambda> e. if e < m+Kart then (if cap_all ! e = - 1 then \<infinity> else ereal (h (cap_all ! e))) else \<infinity>"
        and \<c> = "\<lambda> e. cost_all ! e"
        and r = vcount
        and shift_pot = shift_pot_impl
        and arborescense_invar = "arb_invar vcount Varb"
        and abstract_arborescense = abstract_arb
        and get_path_pair = get_path_pair_impl
        and swap_edge = swap_edge_impl
        and flow_invar = "\<lambda>xs. \<forall>k\<in>{0..<m+Kart}. k < length xs" and flow_upd = list_update and flow_lookup = nth
        and pot_invar = "\<lambda>xs. \<forall>v\<in>Varb. v < length xs" and pot_upd = list_update and pot_lookup = nth
        and parent_invar = "\<lambda>xs. \<forall>v\<in>Varb - {vcount}. v < length xs" and parent_upd = list_update and parent_lookup = nth
        and dir_invar = "\<lambda>xs. \<forall>v\<in>Varb - {vcount}. v < length xs" and dir_upd = list_update and dir_lookup = nth
        and es_invar = "\<lambda>xs. \<forall>k\<in>{0..<m+Kart}. k < length xs" and es_upd = list_update and es_lookup = nth
        and sel_invar = sel_invar_impl and sel_select = sel_select_impl
        and b = "\<lambda> v. h (b_lookup v)"
        and cap = "\<lambda> e. cap_all ! e"
        and pot_value_invar = "\<lambda> p. good_pot_val_c p \<and> pv_invar p"
        and pot_value_abstract = "pval_abstract bigM"
        and pot_value_plus = pval_plus
        and pot_value_minus = pval_minus
        and rcost_invar = rc_invar
        and rcost_abstract = "pval_abstract bigM"
        and fst_exec = "\<lambda> e. fst_all ! e"
        and snd_exec = "\<lambda> e. snd_all ! e"
        and flow_lookup_imp = Array.nth and flow_upd_imp = array_fun_upd_imp
        and parent_lookup_imp = Array.nth and parent_upd_imp = array_fun_upd_imp
        and dir_lookup_imp = Array.nth and dir_upd_imp = array_fun_upd_imp
        and es_lookup_imp = Array.nth and es_upd_imp = array_fun_upd_imp
        and sel_select_imp = "ns_sel_select_imp m marc block_size min_candidates max_candidates fst_arr snd_arr cost_arr"
        and shift_pot_imp = ns_shift_pot_imp and get_path_pair_imp = ns_get_path_pair_imp and swap_edge_imp = ns_swap_edge_imp
        and cap_imp = "Array.nth cap_arr" and fst_exec_imp = "Array.nth fst_arr" and snd_exec_imp = "Array.nth snd_arr"
        and flow_assn = flow_assn_ns and pot_assn = pot_assn_ns and tree_assn = "ndtree_assn Varb"
        and parent_assn = parent_assn_ns and dir_assn = dir_assn_ns and es_assn = es_assn_ns and sel_assn = sel_assn_ns
        and rd = "cap_arr \<mapsto>\<^sub>a capl * cost_arr \<mapsto>\<^sub>a cost_list * fst_arr \<mapsto>\<^sub>a fstl * snd_arr \<mapsto>\<^sub>a sndl"
    apply intro_locales
    apply (all \<open>(rule fixed_univ_map_basic_imp.intro fixed_univ_map_imp_axioms.intro
                       network_simplex_impl_refine_axioms.intro)?\<close>)
    apply (unfold NSg_verts_Varb flow_assn_ns_def es_assn_ns_def parent_assn_ns_def dir_assn_ns_def pot_assn_ns_def)
    apply (sep_auto heap: ns_shift_pot_imp_rule ns_get_path_pair_imp_rule ns_swap_edge_imp_rule)
    defer 1
      apply (rule ns_get_path_pair_imp_rule; assumption)
     apply (rule ns_swap_edge_imp_rule; assumption)
    subgoal premises pr for e
      proof -
        have emc: "e < marc" using pr by (simp add: marc_def)
        have lt: "e < length capl" using emc lencl by simp
        have ce: "capl ! e = cap_all ! e" using capok[OF emc] .
        show ?thesis
          apply (rule ht_cons_pre[OF _ ht_cons_post[OF arr_read_framed[OF lt,
                   where a=cap_arr and F="cost_arr \<mapsto>\<^sub>a cost_list * fst_arr \<mapsto>\<^sub>a fstl * snd_arr \<mapsto>\<^sub>a sndl"]]])
          apply (sep_auto simp: ce)
          done
      qed
    subgoal premises pr for e
      proof -
        have emc: "e < marc" using pr by (simp add: marc_def)
        have lt: "e < length fstl" using emc lenfl by simp
        have fe: "fstl ! e = fst_all ! e" using fstok[OF emc] .
        show ?thesis
          apply (rule ht_cons_pre[OF _ ht_cons_post[OF arr_read_framed[OF lt,
                   where a=fst_arr and F="cap_arr \<mapsto>\<^sub>a capl * cost_arr \<mapsto>\<^sub>a cost_list * snd_arr \<mapsto>\<^sub>a sndl"]]])
          apply (sep_auto simp: fe)
          done
      qed
    subgoal premises pr for e
      proof -
        have emc: "e < marc" using pr by (simp add: marc_def)
        have lt: "e < length sndl" using emc lensl by simp
        have se: "sndl ! e = snd_all ! e" using sndok[OF emc] .
        show ?thesis
          apply (rule ht_cons_pre[OF _ ht_cons_post[OF arr_read_framed[OF lt,
                   where a=snd_arr and F="cap_arr \<mapsto>\<^sub>a capl * cost_arr \<mapsto>\<^sub>a cost_list * fst_arr \<mapsto>\<^sub>a fstl"]]])
          apply (sep_auto simp: se)
          done
      qed
    subgoal premises pr for Sel \<pi> Es a aa b poth esh ab ba
      proof -
        have mcpos: "0 < marc" using num_edges_gtr_0 by (simp add: marc_def)
        have arc_ok: "\<And>e'. e' < marc \<Longrightarrow> e' < length fstl \<and> e' < length sndl \<and> e' < length Es \<and>
            (e' < m \<longrightarrow> e' < length cost_list \<and> cost_list ! e' = cost_list ! e') \<and>
            fstl ! e' = fst_all ! e' \<and> sndl ! e' = snd_all ! e' \<and>
            fst_all ! e' < length \<pi> \<and> snd_all ! e' < length \<pi>"
        proof -
          fix e' assume e': "e' < marc"
          from e' lenfl lensl have a1: "e' < length fstl" "e' < length sndl" by auto
          from e' pr(3) have a2: "e' < length Es" by (auto simp: marc_def)
          from lenco have a3: "e' < m \<longrightarrow> e' < length cost_list" by auto
          from fstok[OF e'] sndok[OF e'] have af: "fstl ! e' = fst_all ! e'" "sndl ! e' = snd_all ! e'" by auto
          from endpt_in_Varb[OF e'] pr(2) have a4: "fst_all ! e' < length \<pi>" "snd_all ! e' < length \<pi>" by auto
          from a1 a2 a3 af a4 show "e' < length fstl \<and> e' < length sndl \<and> e' < length Es \<and>
              (e' < m \<longrightarrow> e' < length cost_list \<and> cost_list ! e' = cost_list ! e') \<and>
              fstl ! e' = fst_all ! e' \<and> sndl ! e' = snd_all ! e' \<and>
              fst_all ! e' < length \<pi> \<and> snd_all ! e' < length \<pi>" by blast
        qed
        have triple: "<sel_assn_ns Sel (a, aa, b) * poth \<mapsto>\<^sub>a \<pi> * esh \<mapsto>\<^sub>a Es * cap_arr \<mapsto>\<^sub>a capl *
                        cost_arr \<mapsto>\<^sub>a cost_list * fst_arr \<mapsto>\<^sub>a fstl * snd_arr \<mapsto>\<^sub>a sndl>
            ns_sel_select_imp m marc block_size min_candidates max_candidates fst_arr snd_arr cost_arr (a, aa, b) poth esh
          <\<lambda>res. poth \<mapsto>\<^sub>a \<pi> * esh \<mapsto>\<^sub>a Es * cap_arr \<mapsto>\<^sub>a capl * cost_arr \<mapsto>\<^sub>a cost_list *
                 fst_arr \<mapsto>\<^sub>a fstl * snd_arr \<mapsto>\<^sub>a sndl *
                 (case sel_select_impl Sel \<pi> Es of None \<Rightarrow> (\<exists>\<^sub>A ss. sel_assn_ns ss (a, aa, b)) * \<up>(res = None)
                   | Some (e, in_U, \<gamma>, sel') \<Rightarrow> sel_assn_ns sel' (a, aa, b) * \<up>(res = Some (e, in_U, \<gamma>)))>"
          by (sep_auto heap: ns_sel_select_imp_rule[OF pr(1) mcpos arc_ok])
        show ?thesis using hoare_triple_wlpD[OF triple pr(4)] by (simp only: ex_assn_move_out)
      qed
    done
  show ?thesis
    using nsR.ns_loop_imp_correct[OF inv]
    by (simp only: ns_loop_prog_def nsR.ns_rel_def nsR.ns_rel_weak_def NSg_verts_Varb)
qed

text \<open>The domain/range structural conditions of @{const Sarb} that the @{const ndtree_assn} tree bridge
      needs, extracted from @{thm arb_invar_Sarb}: every parent / thread / reverse-thread entry, and every
      last-successor, stays inside the vertex set @{term Varb}.  The @{term \<open>ran (prnt Sarb) \<subseteq> Varb\<close>} case
      goes through the parent-edge set's @{const dVs} (= @{term Varb} by @{thm dVs_Sprnt}); its membership
      is hand-written (@{method auto} / @{method blast} diverge on the shadowed-binder comprehension).\<close>
lemma Sarb_struct:
  shows Sarb_prnt_dom: "dom (prnt Sarb) \<subseteq> Varb" and Sarb_prnt_ran: "ran (prnt Sarb) \<subseteq> Varb"
    and Sarb_thrd_dom: "dom (thrd Sarb) \<subseteq> Varb" and Sarb_rvth_dom: "dom (rvth Sarb) \<subseteq> Varb"
    and Sarb_thrd_ran: "ran (thrd Sarb) \<subseteq> Varb" and Sarb_rvth_ran: "ran (rvth Sarb) \<subseteq> Varb"
    and Sarb_lsuc_in: "\<forall>v\<in>Varb. lsuc Sarb v \<in> Varb"
proof -
  note ai = arb_invar_Sarb[unfolded arb_invar_def]
  from ai have raiP: "rooted_arborescense_invar vcount Varb (prnt Sarb)"
    and dtE: "dom (thrd Sarb) = Varb - {lsuc Sarb vcount}"
    and drE: "dom (rvth Sarb) = Varb - {vcount}"
    and bijE: "\<forall>v v'. (thrd Sarb v = Some v') = (rvth Sarb v' = Some v)"
    and linE: "\<forall>v\<in>Varb. lsuc Sarb v \<in> Varb" by blast+
  from raiP have dpE: "dom (prnt Sarb) = Varb - {vcount}"
    and dvsE: "dVs {(y,x) |x y. Some x = prnt Sarb y} = Varb"
    by (auto simp: rooted_arborescense_invar_def)
  show "dom (prnt Sarb) \<subseteq> Varb" using dpE by auto
  show "ran (prnt Sarb) \<subseteq> Varb"
  proof (rule subsetI)
    fix z assume "z \<in> ran (prnt Sarb)"
    then obtain w where w: "prnt Sarb w = Some z" by (auto simp: ran_def)
    have mem: "(w, z) \<in> {(y,x) |x y. Some x = prnt Sarb y}"
      apply (rule CollectI) apply (rule exI[of _ z]) apply (rule exI[of _ w]) apply (simp add: w) done
    have "z \<in> snd ` {(y,x) |x y. Some x = prnt Sarb y}" using mem by (rule rev_image_eqI) simp
    hence "z \<in> dVs {(y,x) |x y. Some x = prnt Sarb y}" by (simp add: dVs_eq)
    thus "z \<in> Varb" using dvsE by simp
  qed
  show "dom (thrd Sarb) \<subseteq> Varb" using dtE by auto
  show "dom (rvth Sarb) \<subseteq> Varb" using drE by auto
  show "ran (thrd Sarb) \<subseteq> Varb" using bijE drE by (fastforce simp: ran_def dom_def)
  show "ran (rvth Sarb) \<subseteq> Varb" using bijE dtE by (fastforce simp: ran_def dom_def)
  show "\<forall>v\<in>Varb. lsuc Sarb v \<in> Varb" using linE .
qed

text \<open>Layer 1 of the network-simplex loop's padding-coupling lemma: the concrete entering-edge
      selector reads @{term edge_state} only at arc indices in @{term \<open>{0..<marc}\<close>}.  Hence
      @{const evaluate}, @{const scan_cache}, @{const scan} and @{const sel_select_impl} give the same
      result on two edge-state lists that agree on @{term \<open>{0..<marc}\<close>} --- the invariant a padded
      @{term \<open>state_all @ replicate (n - Kart) InL\<close>} needs so the loop is insensitive to the inert tail.\<close>

lemma evaluate_es_cong:
  "\<And>(es::edge_tag list) (es'::edge_tag list) (\<pi>::(mtag\<times>'n) list) e. es ! e = es' ! e \<Longrightarrow> evaluate es \<pi> e = evaluate es' \<pi> e"
proof -
  fix es es' :: "edge_tag list" and \<pi> :: "(mtag\<times>'n) list" and e
  assume eq: "es ! e = es' ! e"
  show "evaluate es \<pi> e = evaluate es' \<pi> e" unfolding evaluate_def eq ..
qed

lemma scan_cache_es_cong: "\<And>(es::edge_tag list) (es'::edge_tag list) (\<pi>::(mtag\<times>'n) list) i a len best.
     len \<le> length a \<Longrightarrow> (\<forall>j<len. a ! j < marc) \<Longrightarrow> (\<forall>k<marc. es ! k = es' ! k) \<Longrightarrow>
     scan_cache es \<pi> i a len best = scan_cache es' \<pi> i a len best"
proof -
  fix es es' :: "edge_tag list" and \<pi> :: "(mtag \<times> 'n) list" and i a len best
  show "len \<le> length a \<Longrightarrow> (\<forall>j<len. a ! j < marc) \<Longrightarrow> (\<forall>k<marc. es ! k = es' ! k) \<Longrightarrow>
        scan_cache es \<pi> i a len best = scan_cache es' \<pi> i a len best"
  proof (induction es \<pi> i a len best rule: scan_cache.induct)
    case (1 es \<pi> i a len best)
    note IHe = 1(1) and IHn = 1(2) and prA = 1(3) and prB = 1(4) and prC = 1(5)
    show ?case
    proof (cases "len \<le> i")
      case True
      thus ?thesis by (subst scan_cache.simps, subst (2) scan_cache.simps) simp
    next
      case False
      hence ilt: "i < len" by simp
      have emarc: "a ! i < marc" using prB ilt by blast
      have ev: "evaluate es \<pi> (a ! i) = evaluate es' \<pi> (a ! i)"
        by (rule evaluate_es_cong) (rule prC[rule_format, OF emarc])
      obtain elig u g where eveq: "evaluate es \<pi> (a ! i) = (elig, u, g)"
        by (cases "evaluate es \<pi> (a ! i)") auto
      show ?thesis
      proof (cases elig)
        case True
        have L: "scan_cache es \<pi> i a len best = scan_cache es \<pi> (Suc i) a len (better best (a ! i, u, g))"
          using False eveq True by (subst scan_cache.simps) (simp add: Let_def)
        have R: "scan_cache es' \<pi> i a len best = scan_cache es' \<pi> (Suc i) a len (better best (a ! i, u, g))"
          using False eveq ev True by (subst scan_cache.simps) (simp add: Let_def)
        show ?thesis using L R IHe[OF False refl eveq[symmetric] refl refl True prA prB prC] by simp
      next
        case False
        note nelig = this
        have L: "scan_cache es \<pi> i a len best = scan_cache es \<pi> i (a[i := a ! (len - 1)]) (len - 1) best"
          using \<open>\<not> len \<le> i\<close> eveq nelig by (subst scan_cache.simps) (simp add: Let_def)
        have R: "scan_cache es' \<pi> i a len best = scan_cache es' \<pi> i (a[i := a ! (len - 1)]) (len - 1) best"
          using \<open>\<not> len \<le> i\<close> eveq ev nelig by (subst scan_cache.simps) (simp add: Let_def)
        have p1: "len - 1 \<le> length (a[i := a ! (len - 1)])" using prA by simp
        have ial: "i < length a" using prA ilt by simp
        have lpos: "0 < len" using ilt by simp
        have l1m: "a ! (len - 1) < marc" using prB[rule_format, of "len - 1"] lpos by simp
        have p2: "\<forall>j<len - 1. a[i := a ! (len - 1)] ! j < marc"
        proof (intro allI impI)
          fix j assume j: "j < len - 1"
          show "a[i := a ! (len - 1)] ! j < marc"
          proof (cases "j = i")
            case True thus ?thesis using l1m ial by (simp add: nth_list_update)
          next
            case False
            have "a[i := a ! (len - 1)] ! j = a ! j" using False by (simp add: nth_list_update_neq)
            thus ?thesis using prB j by simp
          qed
        qed
        show ?thesis using L R IHn[OF \<open>\<not> len \<le> i\<close> refl eveq[symmetric] refl refl nelig p1 p2 prC] by simp
      qed
    qed
  qed
qed

lemma scan_es_cong: "\<And>(es::edge_tag list) (es'::edge_tag list) (\<pi>::(mtag\<times>'n) list) mc fuel bpos cur a len best.
     mc = marc \<Longrightarrow> 0 < marc \<Longrightarrow> cur < marc \<Longrightarrow> (\<forall>k<marc. es ! k = es' ! k) \<Longrightarrow>
     scan es \<pi> mc fuel bpos cur a len best = scan es' \<pi> mc fuel bpos cur a len best"
proof -
  fix es es' :: "edge_tag list" and \<pi> :: "(mtag \<times> 'n) list" and mc fuel bpos cur a len best
  show "mc = marc \<Longrightarrow> 0 < marc \<Longrightarrow> cur < marc \<Longrightarrow> (\<forall>k<marc. es ! k = es' ! k) \<Longrightarrow>
        scan es \<pi> mc fuel bpos cur a len best = scan es' \<pi> mc fuel bpos cur a len best"
  proof (induction fuel arbitrary: bpos cur a len best)
    case 0
    thus ?case by (subst scan.simps, subst (2) scan.simps) simp
  next
    case (Suc f)
    note prMc = Suc.prems(1) and prPos = Suc.prems(2) and prCur = Suc.prems(3) and prC = Suc.prems(4)
    show ?case
    proof (cases "max_candidates \<le> len")
      case True thus ?thesis by (subst scan.simps, subst (2) scan.simps) simp
    next
      case False note nmax = this
      show ?thesis
      proof (cases "bpos = 0 \<and> min_candidates \<le> len")
        case True thus ?thesis using nmax by (subst scan.simps, subst (2) scan.simps) simp
      next
        case False note nb = this
        have nmax': "(max_candidates \<le> len) = False" using nmax by simp
        have nb': "(bpos = 0 \<and> min_candidates \<le> len) = False" using nb by simp
        have ev: "evaluate es \<pi> cur = evaluate es' \<pi> cur"
          by (rule evaluate_es_cong) (rule prC[rule_format, OF prCur])
        obtain elig u g where eveq: "evaluate es \<pi> cur = (elig, u, g)" by (cases "evaluate es \<pi> cur") auto
        have eveq': "evaluate es' \<pi> cur = (elig, u, g)" using ev eveq by simp
        define bpos1 where "bpos1 = (if bpos = 0 then block_size else bpos)"
        define a1 where "a1 = (if elig then a[len := cur] else a)"
        define len1 where "len1 = (if elig then Suc len else len)"
        define best1 where "best1 = (if elig then better best (cur, u, g) else best)"
        define cur1 where "cur1 = (if cur + 1 = mc then 0 else cur + 1)"
        have L: "scan es \<pi> mc (Suc f) bpos cur a len best = scan es \<pi> mc f (bpos1 - 1) cur1 a1 len1 best1"
          supply scan.simps[simp del]
          by (subst scan.simps) (simp add: Let_def nmax' nb' eveq bpos1_def a1_def len1_def best1_def cur1_def)
        have R: "scan es' \<pi> mc (Suc f) bpos cur a len best = scan es' \<pi> mc f (bpos1 - 1) cur1 a1 len1 best1"
          supply scan.simps[simp del]
          by (subst scan.simps) (simp add: Let_def nmax' nb' eveq' bpos1_def a1_def len1_def best1_def cur1_def)
        have cur1m: "cur1 < marc" using prCur prMc prPos by (auto simp: cur1_def)
        have rec: "scan es \<pi> mc f (bpos1 - 1) cur1 a1 len1 best1 = scan es' \<pi> mc f (bpos1 - 1) cur1 a1 len1 best1"
          by (rule Suc.IH[OF prMc prPos cur1m prC])
        show ?thesis using L R rec by simp
      qed
    qed
  qed
qed

text \<open>The entering-edge selector as a whole reads @{term edge_state} only through @{const scan_cache}
      and @{const scan}, both confined to arcs below @{term marc} by @{const sel_invar_impl}, so its
      result is unchanged on edge-state lists agreeing on @{term \<open>{0..<marc}\<close>}.\<close>

lemma sel_select_impl_es_cong:
  assumes inv: "sel_invar_impl sel" and mpos: "0 < marc" and agr: "\<forall>k<marc. es ! k = es' ! k"
  shows "sel_select_impl sel \<pi> es = sel_select_impl sel \<pi> es'"
proof -
  have inv': "length (sel_arr sel) = max_candidates \<and> sel_len sel \<le> max_candidates \<and>
              (0 < marc \<longrightarrow> sel_cur sel < marc) \<and> set (take (sel_len sel) (sel_arr sel)) \<subseteq> {0..<marc}"
    using inv by (simp add: sel_invar_impl_def)
  have larr: "sel_len sel \<le> length (sel_arr sel)" using inv' by simp
  have cur: "sel_cur sel < marc" using inv' mpos by simp
  have rng: "set (take (sel_len sel) (sel_arr sel)) \<subseteq> {0..<marc}" using inv' by simp
  have idx: "\<forall>j<sel_len sel. sel_arr sel ! j < marc"
  proof (intro allI impI)
    fix j assume j: "j < sel_len sel"
    have "j < length (take (sel_len sel) (sel_arr sel))" using j larr by (simp add: min_def)
    hence "take (sel_len sel) (sel_arr sel) ! j \<in> set (take (sel_len sel) (sel_arr sel))" by (rule nth_mem)
    moreover have "take (sel_len sel) (sel_arr sel) ! j = sel_arr sel ! j" using j by simp
    ultimately show "sel_arr sel ! j < marc" using rng by auto
  qed
  have SC: "scan_cache es \<pi> 0 (sel_arr sel) (sel_len sel) no_best
            = scan_cache es' \<pi> 0 (sel_arr sel) (sel_len sel) no_best"
    by (rule scan_cache_es_cong[OF larr idx agr])
  obtain a1 len1 found1 e1 u1 g1
    where sc: "scan_cache es' \<pi> 0 (sel_arr sel) (sel_len sel) no_best = (a1, len1, found1, e1, u1, g1)"
    by (cases "scan_cache es' \<pi> 0 (sel_arr sel) (sel_len sel) no_best") auto
  have SE: "scan es \<pi> marc marc block_size (sel_cur sel) a1 len1 no_best
            = scan es' \<pi> marc marc block_size (sel_cur sel) a1 len1 no_best"
    by (rule scan_es_cong[OF refl mpos cur agr])
  show ?thesis
    unfolding sel_select_impl_def SC sc by (simp add: SE del: scan.simps)
qed

text \<open>Layer 2: the coupling relation @{term ns_couple} between two loop states that differ only in an
      inert tail of the flow / edge-state arrays (the indices at or above @{term marc}); all other fields are
      equal, flow and edge-state agree on @{term \<open>{0..<marc}\<close>}, and both satisfy @{const NS.ns_invar}.
      Under it the entering-edge selection agrees (@{thm sel_select_impl_es_cong}).\<close>

definition ns_couple where
  "ns_couple s s' \<longleftrightarrow>
     network_simplex_state.potentials s = network_simplex_state.potentials s' \<and>
     network_simplex_state.spanning_tree s = network_simplex_state.spanning_tree s' \<and>
     network_simplex_state.parent_edge s = network_simplex_state.parent_edge s' \<and>
     network_simplex_state.edge_dir s = network_simplex_state.edge_dir s' \<and>
     network_simplex_state.edge_sel s = network_simplex_state.edge_sel s' \<and>
     network_simplex_state.return s = network_simplex_state.return s' \<and>
     (\<forall>e<marc. network_simplex_state.current_flow s ! e = network_simplex_state.current_flow s' ! e) \<and>
     (\<forall>e<marc. network_simplex_state.edge_state s ! e = network_simplex_state.edge_state s' ! e) \<and>
     NS.ns_invar s \<and> NS.ns_invar s'"

lemma ns_select_cong:
  assumes cpl: "ns_couple s s'" and mpos: "0 < marc"
  shows "NS.ns_select s = NS.ns_select s'"
proof -
  have pot: "network_simplex_state.potentials s = network_simplex_state.potentials s'"
   and sel: "network_simplex_state.edge_sel s = network_simplex_state.edge_sel s'"
   and es: "\<forall>e<marc. network_simplex_state.edge_state s ! e = network_simplex_state.edge_state s' ! e"
   and inv: "NS.ns_invar s" using cpl by (auto simp: ns_couple_def)
  have si: "sel_invar_impl (network_simplex_state.edge_sel s)"
    using NS.ns_invar_implD(6)[OF NS.ns_invarD(1)[OF inv]] .
  have cong: "sel_select_impl (network_simplex_state.edge_sel s) (network_simplex_state.potentials s) (network_simplex_state.edge_state s)
            = sel_select_impl (network_simplex_state.edge_sel s) (network_simplex_state.potentials s) (network_simplex_state.edge_state s')"
    by (rule sel_select_impl_es_cong[OF si mpos es])
  have "NS.ns_select s = sel_select_impl (network_simplex_state.edge_sel s) (network_simplex_state.potentials s) (network_simplex_state.edge_state s')"
    unfolding NS.ns_select_def by (rule cong)
  also have "... = NS.ns_select s'" unfolding NS.ns_select_def by (simp add: pot sel)
  finally show ?thesis .
qed

text \<open>Layer 3 (part a): residual congruences. Under the coupling relation, the forward and backward
      residuals agree at any real arc, and the parent-edge residuals agree at any tree vertex.\<close>

lemma res_fwd_cong:
  assumes "ns_couple s s'" and "a < marc"
  shows "NS.res_fwd s a = NS.res_fwd s' a"
proof -
  have "network_simplex_state.current_flow s ! a = network_simplex_state.current_flow s' ! a"
    using assms by (auto simp: ns_couple_def)
  thus ?thesis by (simp add: NS.res_fwd_def Let_def)
qed

lemma res_bwd_cong:
  assumes "ns_couple s s'" and "a < marc"
  shows "NS.res_bwd s a = NS.res_bwd s' a"
proof -
  have "network_simplex_state.current_flow s ! a = network_simplex_state.current_flow s' ! a"
    using assms by (auto simp: ns_couple_def)
  thus ?thesis by (simp add: NS.res_bwd_def)
qed

lemma res_up_cong:
  assumes cpl: "ns_couple s s'" and pe: "NS.par_edge s v < marc"
  shows "NS.res_up s v = NS.res_up s' v"
proof -
  have peq: "NS.par_edge s v = NS.par_edge s' v" using cpl by (simp add: NS.par_edge_def ns_couple_def)
  have ueq: "NS.par_up s v = NS.par_up s' v" using cpl by (simp add: NS.par_up_def ns_couple_def)
  have F: "NS.res_fwd s (NS.par_edge s v) = NS.res_fwd s' (NS.par_edge s v)" using res_fwd_cong[OF cpl pe] .
  have B: "NS.res_bwd s (NS.par_edge s v) = NS.res_bwd s' (NS.par_edge s v)" using res_bwd_cong[OF cpl pe] .
  show ?thesis
  proof (cases "NS.par_up s v")
    case True thus ?thesis using ueq F peq by (simp add: NS.res_up_def)
  next
    case False thus ?thesis using ueq B peq by (simp add: NS.res_up_def)
  qed
qed

lemma res_down_cong:
  assumes cpl: "ns_couple s s'" and pe: "NS.par_edge s v < marc"
  shows "NS.res_down s v = NS.res_down s' v"
proof -
  have peq: "NS.par_edge s v = NS.par_edge s' v" using cpl by (simp add: NS.par_edge_def ns_couple_def)
  have ueq: "NS.par_up s v = NS.par_up s' v" using cpl by (simp add: NS.par_up_def ns_couple_def)
  have F: "NS.res_fwd s (NS.par_edge s v) = NS.res_fwd s' (NS.par_edge s v)" using res_fwd_cong[OF cpl pe] .
  have B: "NS.res_bwd s (NS.par_edge s v) = NS.res_bwd s' (NS.par_edge s v)" using res_bwd_cong[OF cpl pe] .
  show ?thesis
  proof (cases "NS.par_up s v")
    case True thus ?thesis using ueq B peq by (simp add: NS.res_down_def)
  next
    case False thus ?thesis using ueq F peq by (simp add: NS.res_down_def)
  qed
qed
text \<open>Layer 3 (part b): the two tree-path scans agree under the coupling, since every path vertex is a
      non-root tree vertex (@{thm NS.get_path_pair_verts}) whose parent edge is a real arc, so the
      per-vertex residuals coincide (@{thm res_up_cong} / @{thm res_down_cong}); the folds then agree
      by @{thm fold_cong}.\<close>

lemma scan_up_cong:
  assumes cpl: "ns_couple s s'" and pe: "\<forall>v\<in>set p. NS.par_edge s v < marc"
  shows "NS.scan_up s p = NS.scan_up s' p"
  unfolding NS.scan_up_def
proof (rule fold_cong[OF refl refl])
  fix x assume xp: "x \<in> set p"
  have "NS.res_up s x = NS.res_up s' x" using res_up_cong[OF cpl] pe xp by blast
  thus "(\<lambda>(m, best). let rr = NS.res_up s x in if rr = - 1 then (m, best) else if m = - 1 then (rr, x) else if rr \<le> m then (rr, x) else (m, best))
      = (\<lambda>(m, best). let rr = NS.res_up s' x in if rr = - 1 then (m, best) else if m = - 1 then (rr, x) else if rr \<le> m then (rr, x) else (m, best))"
    by simp
qed

lemma scan_down_cong:
  assumes cpl: "ns_couple s s'" and pe: "\<forall>v\<in>set p. NS.par_edge s v < marc"
  shows "NS.scan_down s p = NS.scan_down s' p"
  unfolding NS.scan_down_def
proof (rule fold_cong[OF refl refl])
  fix x assume xp: "x \<in> set p"
  have "NS.res_down s x = NS.res_down s' x" using res_down_cong[OF cpl] pe xp by blast
  thus "(\<lambda>(m, best). let rr = NS.res_down s x in if rr = - 1 then (m, best) else if m = - 1 then (rr, x) else if rr < m then (rr, x) else (m, best))
      = (\<lambda>(m, best). let rr = NS.res_down s' x in if rr = - 1 then (m, best) else if m = - 1 then (rr, x) else if rr < m then (rr, x) else (m, best))"
    by simp
qed
text \<open>Layer 3 (part b, cont.): the bottleneck agrees under the coupling --- it is a function of the two
      scans, the entering-edge residual, and the (equal) direction flags.\<close>

lemma bottleneck_cong:
  assumes cpl: "ns_couple s s'" and eE: "e < marc"
    and up1: "\<forall>v\<in>set p1. NS.par_edge s v < marc" and up2: "\<forall>v\<in>set p2. NS.par_edge s v < marc"
  shows "NS.bottleneck s e in_U p1 p2 = NS.bottleneck s' e in_U p1 p2"
proof -
  have suc: "NS.scan_up s (if in_U then p1 else p2) = NS.scan_up s' (if in_U then p1 else p2)"
    using scan_up_cong[OF cpl] up1 up2 by (cases in_U) auto
  have sdc: "NS.scan_down s (if in_U then p2 else p1) = NS.scan_down s' (if in_U then p2 else p1)"
    using scan_down_cong[OF cpl] up1 up2 by (cases in_U) auto
  have rfe: "NS.res_fwd s e = NS.res_fwd s' e" using res_fwd_cong[OF cpl eE] .
  have rbe: "NS.res_bwd s e = NS.res_bwd s' e" using res_bwd_cong[OF cpl eE] .
  have pu: "NS.par_up s = NS.par_up s'" using cpl by (simp add: NS.par_up_def ns_couple_def fun_eq_iff)
  show ?thesis
    unfolding NS.bottleneck_def Let_def suc sdc rfe rbe pu by simp
qed
text \<open>Layer 3 (part b, cont.): the augmented flow agrees on the real arcs. Reusing
      @{thm NS.augment_flow_lookup_char} on each side, the per-arc formula depends only on the input
      flow at that arc (equal on the real arcs) and the tree structure (parent edges / directions,
      which are equal), so the outputs coincide there.\<close>

lemma augment_flow_cong:
  assumes cpl: "ns_couple s s'" and eE: "e < marc" and d0: "0 \<le> \<delta>" and am: "a < marc"
    and up1: "\<forall>v\<in>set p1. NS.par_edge s v < marc" and up2: "\<forall>v\<in>set p2. NS.par_edge s v < marc"
  shows "NS.augment_flow s e in_U \<delta> p1 p2 ! a = NS.augment_flow s' e in_U \<delta> p1 p2 ! a"
proof -
  have inv: "NS.ns_invar s" and inv': "NS.ns_invar s'" using cpl by (auto simp: ns_couple_def)
  have fis: "\<forall>k\<in>{0..<m + Kart}. k < length (network_simplex_state.current_flow s)"
    using NS.ns_invar_implD(1)[OF NS.ns_invarD(1)[OF inv]] .
  have fis': "\<forall>k\<in>{0..<m + Kart}. k < length (network_simplex_state.current_flow s')"
    using NS.ns_invar_implD(1)[OF NS.ns_invarD(1)[OF inv']] .
  have eE': "e \<in> {0..<m+Kart}" using eE by (simp add: marc_def)
  have peq: "\<And>w. NS.par_edge s w = NS.par_edge s' w" using cpl by (simp add: NS.par_edge_def ns_couple_def)
  have pueq: "\<And>w. NS.par_up s w = NS.par_up s' w" using cpl by (simp add: NS.par_up_def ns_couple_def)
  have pu1: "\<forall>w\<in>set (if in_U then p1 else p2). NS.par_edge s w \<in> {0..<m+Kart}"
    using up1 up2 by (cases in_U) (auto simp: marc_def)
  have pu2: "\<forall>w\<in>set (if in_U then p2 else p1). NS.par_edge s w \<in> {0..<m+Kart}"
    using up1 up2 by (cases in_U) (auto simp: marc_def)
  have pu1': "\<forall>w\<in>set (if in_U then p1 else p2). NS.par_edge s' w \<in> {0..<m+Kart}" using pu1 peq by simp
  have pu2': "\<forall>w\<in>set (if in_U then p2 else p1). NS.par_edge s' w \<in> {0..<m+Kart}" using pu2 peq by simp
  have fa: "network_simplex_state.current_flow s ! a = network_simplex_state.current_flow s' ! a"
    using cpl am by (auto simp: ns_couple_def)
  show ?thesis
    using NS.augment_flow_lookup_char[OF fis d0 eE' pu1 pu2, of a]
          NS.augment_flow_lookup_char[OF fis' d0 eE' pu1' pu2', of a]
    apply (simp add: fa)
    apply (intro conjI impI arg_cong2[where f = "(+)"] arg_cong[where f = sum_list] map_cong[OF refl])
    apply (auto simp: peq pueq)
    done
qed
text \<open>Layer 4: under the coupling and a @{term Some} selection, the bottleneck agrees --- the entering
      edge is a real arc and both tree paths consist of non-root tree vertices, so @{thm bottleneck_cong}
      applies.\<close>

lemma couple_Some_bn:
  assumes cpl: "ns_couple s s'" and mpos: "0 < marc"
    and sel: "NS.ns_select s = Some (e, in_U, \<gamma>, sel')"
    and pp: "get_path_pair_impl (network_simplex_state.spanning_tree s) (fst_all ! e) (snd_all ! e) = (p1, p2)"
  shows "NS.bottleneck s e in_U p1 p2 = NS.bottleneck s' e in_U p1 p2"
proof -
  have inv: "NS.ns_invar s" using cpl by (simp add: ns_couple_def)
  have eE: "e \<in> {0..<m + Kart}" using NS.ns_select_SomeD(2)[OF inv sel] .
  have emarc: "e < marc" using eE by (simp add: marc_def)
  note ne = NS.entering_not_selfloop[OF inv sel]
  have emc: "e < m + Kart" using eE by simp
  have pp': "get_path_pair_impl (network_simplex_state.spanning_tree s)
               (if e < m + Kart then fst_all ! e else Product_Type.fst (prod_decode (e - (m + Kart))))
               (if e < m + Kart then snd_all ! e else Product_Type.snd (prod_decode (e - (m + Kart)))) = (p1, p2)"
    by (simp only: if_P[OF emc] pp)
  have tree: "NS.ns_invar_tree s" using NS.ns_invarD(7)[OF inv] .
  have up1E: "\<forall>v\<in>set p1. NS.par_edge s v \<in> {0..<m + Kart}"
  proof (rule ballI)
    fix v assume v: "v \<in> set p1"
    from subsetD[OF NS.get_path_pair_verts(1)[OF inv eE ne pp'] v]
    show "NS.par_edge s v \<in> {0..<m + Kart}" by (rule NS.ns_invar_tree_edgeD[OF tree])
  qed
  have up2E: "\<forall>v\<in>set p2. NS.par_edge s v \<in> {0..<m + Kart}"
  proof (rule ballI)
    fix v assume v: "v \<in> set p2"
    from subsetD[OF NS.get_path_pair_verts(2)[OF inv eE ne pp'] v]
    show "NS.par_edge s v \<in> {0..<m + Kart}" by (rule NS.ns_invar_tree_edgeD[OF tree])
  qed
  have up1: "\<forall>v\<in>set p1. NS.par_edge s v < marc" using up1E by (simp add: marc_def)
  have up2: "\<forall>v\<in>set p2. NS.par_edge s v < marc" using up2E by (simp add: marc_def)
  show ?thesis by (rule bottleneck_cong[OF cpl emarc up1 up2])
qed
text \<open>Layer 4: the four branch guards agree under the coupling (entering-edge selection agrees by
      @{thm ns_select_cong}; the paths by tree-equality; the bottleneck by @{thm couple_Some_bn}).\<close>

lemma ns_success_cond_cong:
  assumes cpl: "ns_couple s s'" and mpos: "0 < marc"
  shows "NS.ns_success_cond s = NS.ns_success_cond s'"
  unfolding NS.ns_success_cond_def ns_select_cong[OF cpl mpos] ..

lemma ns_unbounded_cond_cong:
  assumes cpl: "ns_couple s s'" and mpos: "0 < marc"
  shows "NS.ns_unbounded_cond s = NS.ns_unbounded_cond s'"
proof (cases "NS.ns_select s")
  case None thus ?thesis by (simp add: NS.ns_unbounded_cond_def ns_select_cong[OF cpl mpos])
next
  case (Some a)
  obtain e in_U \<gamma> sel' where a: "a = (e, in_U, \<gamma>, sel')" by (cases a) auto
  obtain p1 p2 where pp: "get_path_pair_impl (network_simplex_state.spanning_tree s) (fst_all ! e) (snd_all ! e) = (p1, p2)"
    by (cases "get_path_pair_impl (network_simplex_state.spanning_tree s) (fst_all ! e) (snd_all ! e)") auto
  have sel: "NS.ns_select s = Some (e, in_U, \<gamma>, sel')" using Some a by simp
  have sel': "NS.ns_select s' = Some (e, in_U, \<gamma>, sel')" using sel ns_select_cong[OF cpl mpos] by simp
  have bn: "NS.bottleneck s e in_U p1 p2 = NS.bottleneck s' e in_U p1 p2" using couple_Some_bn[OF cpl mpos sel pp] .
  have teq: "network_simplex_state.spanning_tree s = network_simplex_state.spanning_tree s'" using cpl by (simp add: ns_couple_def)
  show ?thesis unfolding NS.ns_unbounded_cond_def sel sel' by (simp add: pp bn teq[symmetric] Let_def)
qed

lemma ns_flip_cond_cong:
  assumes cpl: "ns_couple s s'" and mpos: "0 < marc"
  shows "NS.ns_flip_cond s = NS.ns_flip_cond s'"
proof (cases "NS.ns_select s")
  case None thus ?thesis by (simp add: NS.ns_flip_cond_def ns_select_cong[OF cpl mpos])
next
  case (Some a)
  obtain e in_U \<gamma> sel' where a: "a = (e, in_U, \<gamma>, sel')" by (cases a) auto
  obtain p1 p2 where pp: "get_path_pair_impl (network_simplex_state.spanning_tree s) (fst_all ! e) (snd_all ! e) = (p1, p2)"
    by (cases "get_path_pair_impl (network_simplex_state.spanning_tree s) (fst_all ! e) (snd_all ! e)") auto
  have sel: "NS.ns_select s = Some (e, in_U, \<gamma>, sel')" using Some a by simp
  have sel': "NS.ns_select s' = Some (e, in_U, \<gamma>, sel')" using sel ns_select_cong[OF cpl mpos] by simp
  have bn: "NS.bottleneck s e in_U p1 p2 = NS.bottleneck s' e in_U p1 p2" using couple_Some_bn[OF cpl mpos sel pp] .
  have teq: "network_simplex_state.spanning_tree s = network_simplex_state.spanning_tree s'" using cpl by (simp add: ns_couple_def)
  show ?thesis unfolding NS.ns_flip_cond_def sel sel' by (simp add: pp bn teq[symmetric] Let_def)
qed

lemma ns_pivot_cond_cong:
  assumes cpl: "ns_couple s s'" and mpos: "0 < marc"
  shows "NS.ns_pivot_cond s = NS.ns_pivot_cond s'"
proof (cases "NS.ns_select s")
  case None thus ?thesis by (simp add: NS.ns_pivot_cond_def ns_select_cong[OF cpl mpos])
next
  case (Some a)
  obtain e in_U \<gamma> sel' where a: "a = (e, in_U, \<gamma>, sel')" by (cases a) auto
  obtain p1 p2 where pp: "get_path_pair_impl (network_simplex_state.spanning_tree s) (fst_all ! e) (snd_all ! e) = (p1, p2)"
    by (cases "get_path_pair_impl (network_simplex_state.spanning_tree s) (fst_all ! e) (snd_all ! e)") auto
  have sel: "NS.ns_select s = Some (e, in_U, \<gamma>, sel')" using Some a by simp
  have sel': "NS.ns_select s' = Some (e, in_U, \<gamma>, sel')" using sel ns_select_cong[OF cpl mpos] by simp
  have bn: "NS.bottleneck s e in_U p1 p2 = NS.bottleneck s' e in_U p1 p2" using couple_Some_bn[OF cpl mpos sel pp] .
  have teq: "network_simplex_state.spanning_tree s = network_simplex_state.spanning_tree s'" using cpl by (simp add: ns_couple_def)
  show ?thesis unfolding NS.ns_pivot_cond_def sel sel' by (simp add: pp bn teq[symmetric] Let_def)
qed

text \<open>Re-parenting depends on the source state @{term s} only through @{term \<open>NS.par_edge s\<close>} and
      @{term \<open>NS.par_up s\<close>} (read along the spine); hence coupled states --- which share
      @{term parent_edge} and @{term edge_dir}, and therefore @{term par_edge}/@{term par_up} --- produce
      the identical re-parented arrays.\<close>
lemma reparent_walk_cong:
  assumes "\<And>w. NS.par_edge s w = NS.par_edge s' w" and "\<And>w. NS.par_up s w = NS.par_up s' w"
  shows "NS.reparent_walk s e v first pe pup ws pd = NS.reparent_walk s' e v first pe pup ws pd"
  using assms by (induction ws arbitrary: first pe pup pd) (auto simp: assms Let_def split: prod.splits if_splits)

lemma reparent_cong:
  assumes pe: "network_simplex_state.parent_edge s = network_simplex_state.parent_edge s'"
    and de: "network_simplex_state.edge_dir s = network_simplex_state.edge_dir s'"
  shows "NS.reparent s e P v = NS.reparent s' e P v"
proof -
  have peq: "\<And>w. NS.par_edge s w = NS.par_edge s' w" using pe by (simp add: NS.par_edge_def)
  have pueq: "\<And>w. NS.par_up s w = NS.par_up s' w" using de by (simp add: NS.par_up_def)
  show ?thesis unfolding NS.reparent_def pe de by (rule reparent_walk_cong[OF peq pueq])
qed

text \<open>Layer 4: the flip step preserves the coupling. On a flip, only @{term current_flow},
      @{term edge_state} and @{term edge_sel} change: the flow update agrees on @{term \<open>{0..<marc}\<close>}
      by @{thm augment_flow_cong} (using @{thm couple_Some_bn} to transfer the selection/bottleneck),
      the edge-state update by @{term list_update} pointwise, and both states stay invariant by
      @{thm NS.ns_flip_preservation}.\<close>
lemma ns_flip_upd_couple:
  assumes cpl: "ns_couple s s'" and mpos: "0 < marc" and cond: "NS.ns_flip_cond s"
  shows "ns_couple (NS.ns_flip_upd s) (NS.ns_flip_upd s')"
proof -
  have inv: "NS.ns_invar s" and inv': "NS.ns_invar s'" using cpl by (auto simp: ns_couple_def)
  have cond': "NS.ns_flip_cond s'" using ns_flip_cond_cong[OF cpl mpos] cond by simp
  from cond obtain e in_U \<gamma> sel' p1 p2 \<delta> v e0fwd up_side where
    sel: "NS.ns_select s = Some (e, in_U, \<gamma>, sel')" and
    ppx: "get_path_pair_impl (network_simplex_state.spanning_tree s) (fst_all ! e) (snd_all ! e) = (p1, p2)" and
    bn: "NS.bottleneck s e in_U p1 p2 = (\<delta>, True, v, e0fwd, up_side)" and dne: "\<delta> \<noteq> - 1"
    by (rule NS.ns_flip_condE)
  have sel': "NS.ns_select s' = Some (e, in_U, \<gamma>, sel')" using sel ns_select_cong[OF cpl mpos] by simp
  have teq: "network_simplex_state.spanning_tree s = network_simplex_state.spanning_tree s'" using cpl by (simp add: ns_couple_def)
  have bnc: "NS.bottleneck s e in_U p1 p2 = NS.bottleneck s' e in_U p1 p2" using couple_Some_bn[OF cpl mpos sel ppx] .
  have ppx': "get_path_pair_impl (network_simplex_state.spanning_tree s') (fst_all ! e) (snd_all ! e) = (p1, p2)" using ppx teq by simp
  have bn': "NS.bottleneck s' e in_U p1 p2 = (\<delta>, True, v, e0fwd, up_side)" using bnc bn by simp
  have flipeq: "NS.ns_flip_upd s = NS.ns_flip s e in_U \<gamma> sel' \<delta> p1 p2" by (simp add: NS.ns_flip_upd_def sel ppx bn)
  have flipeq': "NS.ns_flip_upd s' = NS.ns_flip s' e in_U \<gamma> sel' \<delta> p1 p2" by (simp add: NS.ns_flip_upd_def sel' ppx' bn')
  have eE: "e \<in> {0..<m + Kart}" using NS.ns_select_SomeD(2)[OF inv sel] .
  have emarc: "e < marc" using eE by (simp add: marc_def)
  have emc: "e < m + Kart" using eE by simp
  note ne = NS.entering_not_selfloop[OF inv sel]
  have ppf: "get_path_pair_impl (network_simplex_state.spanning_tree s)
               (if e < m + Kart then fst_all ! e else Product_Type.fst (prod_decode (e - (m + Kart))))
               (if e < m + Kart then snd_all ! e else Product_Type.snd (prod_decode (e - (m + Kart)))) = (p1, p2)"
    by (simp only: if_P[OF emc] ppx)
  have d0: "0 \<le> \<delta>" using NS.bottleneck_delta_bounds(1)[OF inv sel ppf bn dne] .
  have tree: "NS.ns_invar_tree s" using NS.ns_invarD(7)[OF inv] .
  have up1: "\<forall>v\<in>set p1. NS.par_edge s v < marc"
  proof (rule ballI)
    fix v assume v: "v \<in> set p1"
    from subsetD[OF NS.get_path_pair_verts(1)[OF inv eE ne ppf] v]
    have "NS.par_edge s v \<in> {0..<m + Kart}" by (rule NS.ns_invar_tree_edgeD[OF tree])
    thus "NS.par_edge s v < marc" by (simp add: marc_def)
  qed
  have up2: "\<forall>v\<in>set p2. NS.par_edge s v < marc"
  proof (rule ballI)
    fix v assume v: "v \<in> set p2"
    from subsetD[OF NS.get_path_pair_verts(2)[OF inv eE ne ppf] v]
    have "NS.par_edge s v \<in> {0..<m + Kart}" by (rule NS.ns_invar_tree_edgeD[OF tree])
    thus "NS.par_edge s v < marc" by (simp add: marc_def)
  qed
  have esl: "\<forall>k\<in>{0..<m + Kart}. k < length (network_simplex_state.edge_state s)"
    using NS.ns_invar_implD(5)[OF NS.ns_invarD(1)[OF inv]] .
  have esl': "\<forall>k\<in>{0..<m + Kart}. k < length (network_simplex_state.edge_state s')"
    using NS.ns_invar_implD(5)[OF NS.ns_invarD(1)[OF inv']] .
  have eles: "e < length (network_simplex_state.edge_state s)" using esl emc by simp
  have eles': "e < length (network_simplex_state.edge_state s')" using esl' emc by simp
  have esagree: "\<And>a. a < marc \<Longrightarrow> network_simplex_state.edge_state s ! a = network_simplex_state.edge_state s' ! a"
    using cpl by (simp add: ns_couple_def)
  have esupd: "\<And>a. a < marc \<Longrightarrow> (network_simplex_state.edge_state s)[e := (if in_U then InL else InU)] ! a = (network_simplex_state.edge_state s')[e := (if in_U then InL else InU)] ! a"
    by (auto simp: nth_list_update eles eles' esagree)
  have aug: "\<And>a. a < marc \<Longrightarrow> NS.augment_flow s e in_U \<delta> p1 p2 ! a = NS.augment_flow s' e in_U \<delta> p1 p2 ! a"
    by (rule augment_flow_cong[OF cpl emarc d0 _ up1 up2])
  have invf: "NS.ns_invar (NS.ns_flip s e in_U \<gamma> sel' \<delta> p1 p2)"
    using NS.ns_flip_preservation[OF inv cond] flipeq by simp
  have invf': "NS.ns_invar (NS.ns_flip s' e in_U \<gamma> sel' \<delta> p1 p2)"
    using NS.ns_flip_preservation[OF inv' cond'] flipeq' by simp
  show ?thesis
    unfolding flipeq flipeq' ns_couple_def
    apply (intro conjI)
    subgoal by (simp add: NS.ns_flip_def cpl[unfolded ns_couple_def])
    subgoal by (simp add: NS.ns_flip_def teq)
    subgoal by (simp add: NS.ns_flip_def cpl[unfolded ns_couple_def])
    subgoal by (simp add: NS.ns_flip_def cpl[unfolded ns_couple_def])
    subgoal by (simp add: NS.ns_flip_def)
    subgoal by (simp add: NS.ns_flip_def cpl[unfolded ns_couple_def])
    subgoal by (simp add: NS.ns_flip_def aug)
    subgoal by (simp add: NS.ns_flip_def esupd)
    subgoal by (rule invf)
    subgoal by (rule invf')
    done
qed

text \<open>Layer 4: the pivot step preserves the coupling. A full pivot rewrites seven fields; the
      potential/tree/parent/dir arrays are pure functions of the shared @{term spanning_tree},
      @{term potentials}, @{term parent_edge}, @{term edge_dir} (the last via @{thm reparent_cong}),
      hence are literally equal; the flow agrees on @{term \<open>{0..<marc}\<close>} by @{thm augment_flow_cong}
      and the two edge-state updates (at @{term e} and the leaving arc @{term \<open>NS.par_edge s v\<close>},
      both in @{term \<open>{0..<m+Kart}\<close>}) by @{term list_update} pointwise; both states stay invariant by
      @{thm NS.ns_pivot_preservation}.\<close>
lemma ns_pivot_upd_couple:
  assumes cpl: "ns_couple s s'" and mpos: "0 < marc" and cond: "NS.ns_pivot_cond s"
  shows "ns_couple (NS.ns_pivot_upd s) (NS.ns_pivot_upd s')"
proof -
  have inv: "NS.ns_invar s" and inv': "NS.ns_invar s'" using cpl by (auto simp: ns_couple_def)
  have cond': "NS.ns_pivot_cond s'" using ns_pivot_cond_cong[OF cpl mpos] cond by simp
  from cond obtain e in_U \<gamma> sel' p1 p2 \<delta> v e0fwd up_side where
    sel: "NS.ns_select s = Some (e, in_U, \<gamma>, sel')" and
    ppx: "get_path_pair_impl (network_simplex_state.spanning_tree s) (fst_all ! e) (snd_all ! e) = (p1, p2)" and
    bn: "NS.bottleneck s e in_U p1 p2 = (\<delta>, False, v, e0fwd, up_side)" and dne: "\<delta> \<noteq> - 1"
    by (rule NS.ns_pivot_condE)
  have poteq: "network_simplex_state.potentials s = network_simplex_state.potentials s'"
    using cpl by (simp add: ns_couple_def)
  have teq: "network_simplex_state.spanning_tree s = network_simplex_state.spanning_tree s'"
    using cpl by (simp add: ns_couple_def)
  have pareq: "network_simplex_state.parent_edge s = network_simplex_state.parent_edge s'"
    using cpl by (simp add: ns_couple_def)
  have direq: "network_simplex_state.edge_dir s = network_simplex_state.edge_dir s'"
    using cpl by (simp add: ns_couple_def)
  have reteq: "network_simplex_state.return s = network_simplex_state.return s'"
    using cpl by (simp add: ns_couple_def)
  have sel': "NS.ns_select s' = Some (e, in_U, \<gamma>, sel')" using sel ns_select_cong[OF cpl mpos] by simp
  have bnc: "NS.bottleneck s e in_U p1 p2 = NS.bottleneck s' e in_U p1 p2" using couple_Some_bn[OF cpl mpos sel ppx] .
  have ppx': "get_path_pair_impl (network_simplex_state.spanning_tree s') (fst_all ! e) (snd_all ! e) = (p1, p2)" using ppx teq by simp
  have bn': "NS.bottleneck s' e in_U p1 p2 = (\<delta>, False, v, e0fwd, up_side)" using bnc bn by simp
  have eE: "e \<in> {0..<m + Kart}" using NS.ns_select_SomeD(2)[OF inv sel] .
  have emarc: "e < marc" using eE by (simp add: marc_def)
  have emc: "e < m + Kart" using eE by simp
  note ne = NS.entering_not_selfloop[OF inv sel]
  have ppf: "get_path_pair_impl (network_simplex_state.spanning_tree s)
               (if e < m + Kart then fst_all ! e else Product_Type.fst (prod_decode (e - (m + Kart))))
               (if e < m + Kart then snd_all ! e else Product_Type.snd (prod_decode (e - (m + Kart)))) = (p1, p2)"
    by (simp only: if_P[OF emc] ppx)
  have tree: "NS.ns_invar_tree s" using NS.ns_invarD(7)[OF inv] .
  have vVr: "v \<in> NS.\<V> - {vcount}" using NS.bottleneck_pivot_facts(2)[OF inv sel ppf bn] .
  have d0: "0 \<le> \<delta>" using NS.bottleneck_pivot_facts(5)[OF inv sel ppf bn] .
  have e0E: "NS.par_edge s v \<in> {0..<m + Kart}" using NS.ns_invar_tree_edgeD[OF tree vVr] .
  have e0marc: "NS.par_edge s v < marc" using e0E by (simp add: marc_def)
  have e0eq: "NS.par_edge s v = NS.par_edge s' v" using pareq by (simp add: NS.par_edge_def)
  have up1: "\<forall>w\<in>set p1. NS.par_edge s w < marc"
  proof (rule ballI)
    fix w assume w: "w \<in> set p1"
    from subsetD[OF NS.get_path_pair_verts(1)[OF inv eE ne ppf] w]
    have "NS.par_edge s w \<in> {0..<m + Kart}" by (rule NS.ns_invar_tree_edgeD[OF tree])
    thus "NS.par_edge s w < marc" by (simp add: marc_def)
  qed
  have up2: "\<forall>w\<in>set p2. NS.par_edge s w < marc"
  proof (rule ballI)
    fix w assume w: "w \<in> set p2"
    from subsetD[OF NS.get_path_pair_verts(2)[OF inv eE ne ppf] w]
    have "NS.par_edge s w \<in> {0..<m + Kart}" by (rule NS.ns_invar_tree_edgeD[OF tree])
    thus "NS.par_edge s w < marc" by (simp add: marc_def)
  qed
  define P where "P = (if in_U = up_side then p1 else p2)"
  obtain parr darr where rp: "NS.reparent s e P v = (parr, darr)" by (cases "NS.reparent s e P v")
  have rp': "NS.reparent s' e P v = (parr, darr)" using rp reparent_cong[OF pareq direq] by simp
  have piveq: "NS.ns_pivot_upd s = NS.ns_pivot s e in_U \<gamma> sel' \<delta> v e0fwd up_side p1 p2"
    by (simp add: NS.ns_pivot_upd_def sel ppx bn)
  have piveq': "NS.ns_pivot_upd s' = NS.ns_pivot s' e in_U \<gamma> sel' \<delta> v e0fwd up_side p1 p2"
    by (simp add: NS.ns_pivot_upd_def sel' ppx' bn')
  let ?s2 = "NS.ns_pivot s e in_U \<gamma> sel' \<delta> v e0fwd up_side p1 p2"
  let ?t2 = "NS.ns_pivot s' e in_U \<gamma> sel' \<delta> v e0fwd up_side p1 p2"
  have aug: "\<And>a. a < marc \<Longrightarrow> NS.augment_flow s e in_U \<delta> p1 p2 ! a = NS.augment_flow s' e in_U \<delta> p1 p2 ! a"
    by (rule augment_flow_cong[OF cpl emarc d0 _ up1 up2])
  have esagree: "\<And>a. a < marc \<Longrightarrow> network_simplex_state.edge_state s ! a = network_simplex_state.edge_state s' ! a"
    using cpl by (simp add: ns_couple_def)
  have esl: "\<forall>k\<in>{0..<m + Kart}. k < length (network_simplex_state.edge_state s)"
    using NS.ns_invar_implD(5)[OF NS.ns_invarD(1)[OF inv]] .
  have esl': "\<forall>k\<in>{0..<m + Kart}. k < length (network_simplex_state.edge_state s')"
    using NS.ns_invar_implD(5)[OF NS.ns_invarD(1)[OF inv']] .
  have eles: "e < length (network_simplex_state.edge_state s)" using esl emc by simp
  have eles': "e < length (network_simplex_state.edge_state s')" using esl' emc by simp
  have e0les: "NS.par_edge s v < length (network_simplex_state.edge_state s)" using esl e0E by simp
  have e0les': "NS.par_edge s v < length (network_simplex_state.edge_state s')" using esl' e0E e0eq by simp
  have esupd2: "\<And>a. a < marc \<Longrightarrow>
      (network_simplex_state.edge_state s)[e := InTree, NS.par_edge s v := (if e0fwd then InU else InL)] ! a
    = (network_simplex_state.edge_state s')[e := InTree, NS.par_edge s' v := (if e0fwd then InU else InL)] ! a"
    by (auto simp: e0eq[symmetric] nth_list_update eles eles' e0les e0les' esagree)
  have invf: "NS.ns_invar ?s2" using NS.ns_pivot_preservation(1)[OF inv cond] piveq by simp
  have invf': "NS.ns_invar ?t2" using NS.ns_pivot_preservation(1)[OF inv' cond'] piveq' by simp
  show ?thesis
    unfolding piveq piveq' ns_couple_def
    apply (intro conjI)
    subgoal by (simp add: NS.ns_pivot_def Let_def rp rp' teq poteq flip: P_def split: prod.split)
    subgoal by (simp add: NS.ns_pivot_def Let_def rp rp' teq flip: P_def split: prod.split)
    subgoal by (simp add: NS.ns_pivot_def Let_def rp rp' flip: P_def split: prod.split)
    subgoal by (simp add: NS.ns_pivot_def Let_def rp rp' flip: P_def split: prod.split)
    subgoal by (simp add: NS.ns_pivot_def Let_def rp rp' flip: P_def split: prod.split)
    subgoal by (simp add: NS.ns_pivot_def Let_def rp rp' reteq flip: P_def split: prod.split)
    subgoal by (simp add: NS.ns_pivot_def Let_def rp rp' aug flip: P_def split: prod.split)
    subgoal by (simp add: NS.ns_pivot_def Let_def rp rp' esupd2 flip: P_def split: prod.split)
    subgoal by (rule invf)
    subgoal by (rule invf')
    done
qed

text \<open>@{term ns_invar} does not mention the @{term return} field, so it is invariant under the
      terminal flag writes (mirrors @{thm initial_basis_selector.ns_invar_ret}).  The
       must disable the self-referential @{thm NS.fst_exec_eq}/@{thm NS.snd_exec_eq}
      to avoid the known rewrite loop.\<close>
lemma ns_invar_ret: "NS.ns_invar (s\<lparr>network_simplex_state.return := r\<rparr>) = NS.ns_invar s"
  by (simp del: NS.fst_exec_eq NS.snd_exec_eq
           add: NS.ns_invar_def NS.ns_invar_impl_def NS.ns_invar_bflow_def NS.ns_invar_partition_def
                NS.ns_invar_flow_fits_def NS.ns_invar_pot_fits_def NS.ns_invar_strict_def
                NS.ns_invar_tree_def NS.ns_invar_selfloop_def NS.ns_L_of_def NS.ns_U_of_def
                NS.par_edge_def NS.par_up_def NS.par_vx_def)

text \<open>Layer 4: the two terminal branches (optimum / unbounded) only set the @{term return} flag, so
      they trivially preserve the coupling.\<close>
lemma ns_optimal_couple:
  assumes cpl: "ns_couple s s'"
  shows "ns_couple (NS.ns_optimal s) (NS.ns_optimal s')"
  using cpl by (simp add: ns_couple_def NS.ns_optimal_def ns_invar_ret)

lemma ns_unbounded_couple:
  assumes cpl: "ns_couple s s'"
  shows "ns_couple (NS.ns_unbounded_upd s) (NS.ns_unbounded_upd s')"
  using cpl by (simp add: ns_couple_def NS.ns_unbounded_upd_def ns_invar_ret)

text \<open>Layer 5: the whole loop preserves the coupling and transfers termination.  By the tailored
      loop induction, the two terminal branches close by the terminal couplings, and the flip/pivot
      branches thread the coupling through one step and apply the induction hypothesis, transferring
      the domain condition back through @{thm NS.ns_loop_dom_flip}/@{thm NS.ns_loop_dom_pivot}.\<close>
lemma ns_loop_couple:
  assumes dom: "NS.ns_loop_dom s" and mpos: "0 < marc"
  shows "ns_couple s s' \<Longrightarrow> NS.ns_loop_dom s' \<and> ns_couple (NS.ns_loop s) (NS.ns_loop s')"
proof (induction arbitrary: s' rule: NS.ns_loop_induct[OF dom])
  case (1 s)
  note IH = this
  show ?case
  proof (cases s rule: NS.ns_loop_cases)
    case 1
    have cond': "NS.ns_success_cond s'" using ns_success_cond_cong[OF IH(4) mpos] 1 by simp
    have doms': "NS.ns_loop_dom s'" by (rule NS.ns_loop_dom_success[OF cond'])
    show ?thesis using doms' ns_optimal_couple[OF IH(4)]
      by (simp add: NS.ns_loop_simps(1)[OF IH(1) 1] NS.ns_loop_simps(1)[OF doms' cond'])
  next
    case 2
    have cond': "NS.ns_unbounded_cond s'" using ns_unbounded_cond_cong[OF IH(4) mpos] 2 by simp
    have doms': "NS.ns_loop_dom s'" by (rule NS.ns_loop_dom_unbounded[OF cond'])
    show ?thesis using doms' ns_unbounded_couple[OF IH(4)]
      by (simp add: NS.ns_loop_simps(2)[OF IH(1) 2] NS.ns_loop_simps(2)[OF doms' cond'])
  next
    case 3
    have cond': "NS.ns_flip_cond s'" using ns_flip_cond_cong[OF IH(4) mpos] 3 by simp
    have cplf: "ns_couple (NS.ns_flip_upd s) (NS.ns_flip_upd s')"
      by (rule ns_flip_upd_couple[OF IH(4) mpos 3])
    have rec: "NS.ns_loop_dom (NS.ns_flip_upd s') \<and>
               ns_couple (NS.ns_loop (NS.ns_flip_upd s)) (NS.ns_loop (NS.ns_flip_upd s'))"
      by (rule IH(2)[OF 3 cplf])
    have doms': "NS.ns_loop_dom s'" by (rule NS.ns_loop_dom_flip[OF cond' conjunct1[OF rec]])
    show ?thesis using doms' conjunct2[OF rec]
      by (simp add: NS.ns_loop_simps(3)[OF IH(1) 3] NS.ns_loop_simps(3)[OF doms' cond'])
  next
    case 4
    have cond': "NS.ns_pivot_cond s'" using ns_pivot_cond_cong[OF IH(4) mpos] 4 by simp
    have cplf: "ns_couple (NS.ns_pivot_upd s) (NS.ns_pivot_upd s')"
      by (rule ns_pivot_upd_couple[OF IH(4) mpos 4])
    have rec: "NS.ns_loop_dom (NS.ns_pivot_upd s') \<and>
               ns_couple (NS.ns_loop (NS.ns_pivot_upd s)) (NS.ns_loop (NS.ns_pivot_upd s'))"
      by (rule IH(3)[OF 4 cplf])
    have doms': "NS.ns_loop_dom s'" by (rule NS.ns_loop_dom_pivot[OF cond' conjunct1[OF rec]])
    show ?thesis using doms' conjunct2[OF rec]
      by (simp add: NS.ns_loop_simps(4)[OF IH(1) 4] NS.ns_loop_simps(4)[OF doms' cond'])
  qed
qed

text \<open>Padding invariance: the loop invariant @{const NS.ns_invar} depends on the flow and edge-state
      stores only through their values at the real edge universe @{term \<open>{0..<m+Kart}\<close>} (and the length
      bound).  Hence extending / overwriting either store outside that range --- as the imperative solver
      does, allocating length @{term \<open>m+n\<close>} arrays and using only the first @{term \<open>m+Kart\<close>} cells ---
      preserves the invariant.  Each of the eight conjuncts is transported: the b-flow via
      @{thm NS.isbflow_cong}, the two partition sets via their set-builder shape over the edge range, the
      flow-fit on the L / U sets (both subsets of the edge range), strong feasibility on the tree parent edges
      (@{thm NS.ns_invar_tree_edgeD} places them in @{term \<E>}), and the self-loop fit which quantifies
      over @{term \<E>}.  The self-referential @{thm NS.fst_exec_eq}/@{thm NS.snd_exec_eq} must be disabled
      throughout to avoid the known rewrite loop.\<close>
lemma ns_invar_flow_es_cong:
  assumes inv: "NS.ns_invar s"
    and flen: "\<forall>k\<in>{0..<m+Kart}. k < length fl"
    and eslen: "\<forall>k\<in>{0..<m+Kart}. k < length es"
    and fag: "\<And>k. k < m+Kart \<Longrightarrow> fl ! k = current_flow s ! k"
    and eag: "\<And>k. k < m+Kart \<Longrightarrow> es ! k = network_simplex_state.edge_state s ! k"
  shows "NS.ns_invar (s\<lparr>current_flow := fl, network_simplex_state.edge_state := es\<rparr>)"
proof -
  define s2 where "s2 = (s\<lparr>current_flow := fl, network_simplex_state.edge_state := es\<rparr>)"
  have cf2: "current_flow s2 = fl" by (simp add: s2_def)
  have es2: "network_simplex_state.edge_state s2 = es"
    and pe2: "parent_edge s2 = parent_edge s" and ed2: "edge_dir s2 = edge_dir s"
    and pot2: "potentials s2 = potentials s"
    and tr2: "network_simplex_state.spanning_tree s2 = network_simplex_state.spanning_tree s"
    and sel2: "edge_sel s2 = edge_sel s" by (simp_all add: s2_def)
  have pared: "\<And>v. NS.par_edge s2 v = NS.par_edge s v"
    by (simp add: NS.par_edge_def pe2 del: NS.fst_exec_eq NS.snd_exec_eq)
  have parup: "\<And>v. NS.par_up s2 v = NS.par_up s v"
    by (simp add: NS.par_up_def ed2 del: NS.fst_exec_eq NS.snd_exec_eq)
  have parvx: "\<And>v. NS.par_vx s2 v = NS.par_vx s v"
    by (simp add: NS.par_vx_def pared parup del: NS.fst_exec_eq NS.snd_exec_eq)
  have flowE: "\<And>e. e \<in> {0..<m+Kart} \<Longrightarrow> NS.ns_flow_of s2 e = NS.ns_flow_of s e"
    using fag by (auto simp: cf2)
  have esE: "\<And>e. e \<in> {0..<m+Kart} \<Longrightarrow> network_simplex_state.edge_state s2 ! e = network_simplex_state.edge_state s ! e"
    using eag by (auto simp: es2)
  have LsubE: "NS.ns_L_of s \<subseteq> {0..<m+Kart}" unfolding NS.ns_L_of_def by blast
  have UsubE: "NS.ns_U_of s \<subseteq> {0..<m+Kart}" unfolding NS.ns_U_of_def by blast
  have Leq: "NS.ns_L_of s2 = NS.ns_L_of s"
    using esE by (auto simp: NS.ns_L_of_def simp del: NS.fst_exec_eq NS.snd_exec_eq)
  have Ueq: "NS.ns_U_of s2 = NS.ns_U_of s"
    using esE by (auto simp: NS.ns_U_of_def simp del: NS.fst_exec_eq NS.snd_exec_eq)
  have impl2: "NS.ns_invar_impl s2"
    unfolding NS.ns_invar_impl_def
    using flen eslen NS.ns_invar_implD(2,3,4,6,7)[OF NS.ns_invarD(1)[OF inv]]
    by (simp add: cf2 es2 pot2 pe2 ed2 sel2 tr2 del: NS.fst_exec_eq NS.snd_exec_eq)
  have bflow2: "NS.ns_invar_bflow s2"
    unfolding NS.ns_invar_bflow_def
    apply (rule NS.isbflow_cong[OF _ refl NS.ns_invarD(2)[OF inv, unfolded NS.ns_invar_bflow_def]])
    by (auto simp: cf2 fag)
  have part2: "NS.ns_invar_partition s2"
    using NS.ns_invarD(3)[OF inv]
    by (simp add: NS.ns_invar_partition_def pe2 Leq Ueq del: NS.fst_exec_eq NS.snd_exec_eq)
  have fits2: "NS.ns_invar_flow_fits s2"
    unfolding NS.ns_invar_flow_fits_def NS.flow_fits_spanning_tree_partition_def Leq Ueq
    apply (intro conjI ballI)
    subgoal for e using flowE[of e] LsubE NS.ns_invarD(4)[OF inv]
      by (force simp add: NS.ns_invar_flow_fits_def NS.flow_fits_spanning_tree_partition_def
                simp del: NS.fst_exec_eq NS.snd_exec_eq)
    subgoal for e using flowE[of e] UsubE NS.ns_invarD(4)[OF inv]
      by (force simp add: NS.ns_invar_flow_fits_def NS.flow_fits_spanning_tree_partition_def
                simp del: NS.fst_exec_eq NS.snd_exec_eq)
    done
  have pot_fits2: "NS.ns_invar_pot_fits s2"
    using NS.ns_invarD(5)[OF inv]
    by (simp add: NS.ns_invar_pot_fits_def pe2 pot2 del: NS.fst_exec_eq NS.snd_exec_eq)
  have strict2: "NS.ns_invar_strict s2"
    unfolding NS.ns_invar_strict_def pared parup cf2
    apply (intro ballI)
    subgoal premises p for v
    proof -
      have pE: "NS.par_edge s v \<in> {0..<m+Kart}" using NS.ns_invar_tree_edgeD[OF NS.ns_invarD(7)[OF inv] p] .
      have fl_eq: "fl ! NS.par_edge s v = current_flow s ! NS.par_edge s v" using fag pE by simp
      show ?thesis using NS.ns_invarD(6)[OF inv] p
        by (simp add: NS.ns_invar_strict_def fl_eq del: NS.fst_exec_eq NS.snd_exec_eq)
    qed
    done
  have tree2: "NS.ns_invar_tree s2"
    using NS.ns_invarD(7)[OF inv]
    by (simp only: NS.ns_invar_tree_def NS.par_edge_def NS.par_up_def NS.par_vx_def pe2 ed2 tr2) blast
  have self2: "NS.ns_invar_selfloop s2"
    using NS.ns_invarD(8)[OF inv] flowE
    by (auto simp: NS.ns_invar_selfloop_def simp del: NS.fst_exec_eq NS.snd_exec_eq)
  show ?thesis
    unfolding s2_def[symmetric] NS.ns_invar_def
    using impl2 bflow2 part2 fits2 pot_fits2 strict2 tree2 self2 by blast
qed

text \<open>The padded state couples with its base: overwriting the flow / edge-state stores outside the
      real edge range @{term \<open>{0..<m+Kart}\<close>} yields a state standing in the coupling relation
      @{const ns_couple} with the original.  Combined with @{thm ns_loop_couple} this transports the
      whole loop from the imperative padded state to the functional initial basis.\<close>
lemma ns_pad_couple:
  assumes inv0: "NS.ns_invar s0"
    and flen: "\<forall>k\<in>{0..<m+Kart}. k < length fl" and eslen: "\<forall>k\<in>{0..<m+Kart}. k < length es"
    and fag: "\<And>k. k < m+Kart \<Longrightarrow> fl ! k = current_flow s0 ! k"
    and eag: "\<And>k. k < m+Kart \<Longrightarrow> es ! k = network_simplex_state.edge_state s0 ! k"
  shows "ns_couple (s0\<lparr>current_flow := fl, network_simplex_state.edge_state := es\<rparr>) s0"
proof -
  have inv2: "NS.ns_invar (s0\<lparr>current_flow := fl, network_simplex_state.edge_state := es\<rparr>)"
    by (rule ns_invar_flow_es_cong[OF inv0 flen eslen fag eag])
  show ?thesis
    unfolding ns_couple_def
    using inv0 inv2 by (auto simp: marc_def fag eag simp del: NS.fst_exec_eq NS.snd_exec_eq)
qed

text \<open>The coupling relation is symmetric (every conjunct of @{const ns_couple} is).\<close>
lemma ns_couple_sym: "ns_couple s s' \<Longrightarrow> ns_couple s' s"
  unfolding ns_couple_def by (auto simp del: NS.fst_exec_eq NS.snd_exec_eq)

text \<open>The whole-loop padding transfer, packaged for the capstone: running @{const NS.ns_loop} from a
      padded state agrees with running it from the base state --- same termination, same terminal
      @{term return} verdict, and the two flows agree on the real edge range @{term \<open>{0..<marc}\<close>}.
      Instantiated later at @{term s0} = the functional initial basis.\<close>
lemma ns_loop_pad_transfer:
  assumes dom0: "NS.ns_loop_dom s0" and mpos: "0 < marc" and inv0: "NS.ns_invar s0"
    and flen: "\<forall>k\<in>{0..<m+Kart}. k < length fl" and eslen: "\<forall>k\<in>{0..<m+Kart}. k < length es"
    and fag: "\<And>k. k < m+Kart \<Longrightarrow> fl ! k = current_flow s0 ! k"
    and eag: "\<And>k. k < m+Kart \<Longrightarrow> es ! k = network_simplex_state.edge_state s0 ! k"
  shows "NS.ns_loop_dom (s0\<lparr>current_flow := fl, network_simplex_state.edge_state := es\<rparr>)
       \<and> network_simplex_state.return (NS.ns_loop (s0\<lparr>current_flow := fl, network_simplex_state.edge_state := es\<rparr>))
           = network_simplex_state.return (NS.ns_loop s0)
       \<and> (\<forall>e<marc. current_flow (NS.ns_loop (s0\<lparr>current_flow := fl, network_simplex_state.edge_state := es\<rparr>)) ! e
                   = current_flow (NS.ns_loop s0) ! e)"
proof -
  have cpl: "ns_couple s0 (s0\<lparr>current_flow := fl, network_simplex_state.edge_state := es\<rparr>)"
    by (rule ns_couple_sym[OF ns_pad_couple[OF inv0 flen eslen fag eag]])
  from ns_loop_couple[OF dom0 mpos, of "s0\<lparr>current_flow := fl, network_simplex_state.edge_state := es\<rparr>"] cpl
  have D: "NS.ns_loop_dom (s0\<lparr>current_flow := fl, network_simplex_state.edge_state := es\<rparr>)"
    and C: "ns_couple (NS.ns_loop s0) (NS.ns_loop (s0\<lparr>current_flow := fl, network_simplex_state.edge_state := es\<rparr>))"
    by blast+
  from C show ?thesis using D by (auto simp: ns_couple_def)
qed

text \<open>Functional core of the capstone.  When the acyclifier succeeds, the functional verdict
      @{const solve} is exactly the verdict read off @{term \<open>NS.ns_loop sp\<close>} for the padded initial
      basis @{term sp}: same @{term return}, same artificial-edge zero test on @{term \<open>[m..<m+Kart]\<close>},
      same optimal flow prefix @{term \<open>take m\<close>}.  The proof re-interprets @{locale network_simplex_init}
      at the concrete basis (discharged by the inherited \<open>NSinit_*\<close> obligations), turning
      @{const NS.ns_loop_impl} into @{const NS.ns_loop} via @{thm NS.ns_loop_dom_impl_same}, and pads
      through @{thm ns_loop_pad_transfer}; the @{term \<open>take m\<close>} branch uses the loop-invariant length
      bounds from @{thm ns_loop_invar}.\<close>
lemma solve_via_padded:
  assumes some: "acyc_flow_opt \<noteq> None" and mpos: "0 < marc"
    and flen: "\<forall>k\<in>{0..<m+Kart}. k < length fl" and eslen: "\<forall>k\<in>{0..<m+Kart}. k < length es"
    and fag: "\<And>k. k < m+Kart \<Longrightarrow> fl ! k = flow_all ! k"
    and eag: "\<And>k. k < m+Kart \<Longrightarrow> es ! k = state_all ! k"
  defines "sp \<equiv> (network_simplex_init_spec.init_state flow_all (ds_pot art_tree) (tree_st art_tree)
                   (ds_par art_tree) (ds_dir art_tree) state_all init_sel)
                 \<lparr>current_flow := fl, network_simplex_state.edge_state := es\<rparr>"
  shows "NS.ns_loop_dom sp \<and> NS.ns_invar sp
       \<and> solve = (if network_simplex_state.return (NS.ns_loop sp) = unbounded then Neg_inf_cycle
                  else if list_all (\<lambda>k. current_flow (NS.ns_loop sp) ! k = 0) [m..<m+Kart]
                       then Optimum (take m (current_flow (NS.ns_loop sp))) else Infeasible)"
proof -
  from some obtain f' where sf: "acyc_flow_opt = Some f'" by auto
  interpret NSinit: network_simplex_init
    where fst = "\<lambda> e. if e < m+Kart then fst_all ! e else Product_Type.fst (prod_decode (e - (m+Kart)))"
      and snd = "\<lambda> e. if e < m+Kart then snd_all ! e else Product_Type.snd (prod_decode (e - (m+Kart)))"
      and create_edge = "\<lambda> u v. (m+Kart) + prod_encode (u, v)"
      and \<E> = "{0..<m+Kart}"
      and \<u> = "\<lambda> e. if e < m+Kart then (if cap_all ! e = - 1 then \<infinity> else ereal (h (cap_all ! e))) else \<infinity>"
      and \<c> = "\<lambda> e. cost_all ! e"
      and r = vcount
      and shift_pot = shift_pot_impl
      and arborescense_invar = "arb_invar vcount Varb"
      and abstract_arborescense = abstract_arb
      and get_path_pair = get_path_pair_impl
      and swap_edge = swap_edge_impl
      and flow_invar = "\<lambda>xs. \<forall>k\<in>{0..<m+Kart}. k < length xs" and flow_upd = list_update and flow_lookup = nth
      and pot_invar = "\<lambda>xs. \<forall>v\<in>Varb. v < length xs" and pot_upd = list_update and pot_lookup = nth
      and parent_invar = "\<lambda>xs. \<forall>v\<in>Varb - {vcount}. v < length xs" and parent_upd = list_update and parent_lookup = nth
      and dir_invar = "\<lambda>xs. \<forall>v\<in>Varb - {vcount}. v < length xs" and dir_upd = list_update and dir_lookup = nth
      and es_invar = "\<lambda>xs. \<forall>k\<in>{0..<m+Kart}. k < length xs" and es_upd = list_update and es_lookup = nth
      and sel_invar = sel_invar_impl and sel_select = sel_select_impl
      and b = "\<lambda> v. h (b_lookup v)"
      and cap = "\<lambda> e. cap_all ! e"
      and pot_value_invar = "\<lambda> p. good_pot_val_c p \<and> pv_invar p"
      and pot_value_abstract = "pval_abstract bigM"
      and pot_value_plus = pval_plus
      and pot_value_minus = pval_minus
      and rcost_invar = rc_invar
      and rcost_abstract = "pval_abstract bigM"
      and fst_exec = "\<lambda> e. fst_all ! e"
      and snd_exec = "\<lambda> e. snd_all ! e"
      and init_flow = flow_all
      and init_pot = "ds_pot (build_tree acyc_flow)"
      and init_tree = Sarb
      and init_parent = "ds_par (build_tree acyc_flow)"
      and init_dir = "ds_dir (build_tree acyc_flow)"
      and init_edge_state = state_all
      and init_sel = init_sel
    apply unfold_locales
    apply (all \<open>(rule NSinit_tree_corr NSinit_strict NSinit_pot_fits NSinit_flow_fits_ns
                       arb_invar_Sarb NSinit_sel_invar
                       NSinit_flow_invar NSinit_es_invar_len NSinit_par_invar NSinit_dir_invar
                       pot_valid_build_tree NSinit_bflow_ne[OF some] NSinit_partition_aug[OF some]
                       NSinit_selfloop[OF some])?\<close>)
    done
  define I where "I = network_simplex_init_spec.init_state flow_all (ds_pot art_tree) (tree_st art_tree)
                        (ds_par art_tree) (ds_dir art_tree) state_all init_sel"
  have eqst: "I = NSinit.init_state"
    unfolding I_def by (simp add: NSinit.init_state_def network_simplex_init_spec.init_state_def Sarb_tree_st art_tree_def)
  have inv0: "NS.ns_invar I" unfolding eqst by (rule NSinit.init_state_invar)
  have dom0: "NS.ns_loop_dom I" unfolding eqst by (rule NSinit.network_simplex_correct(1))
  have cf0: "current_flow I = flow_all" and es0: "network_simplex_state.edge_state I = state_all"
    unfolding I_def by (simp_all add: network_simplex_init_spec.init_state_def)
  have fag': "\<And>k. k < m+Kart \<Longrightarrow> fl ! k = current_flow I ! k" using fag by (simp add: cf0)
  have eag': "\<And>k. k < m+Kart \<Longrightarrow> es ! k = network_simplex_state.edge_state I ! k" using eag by (simp add: es0)
  have sp_eq: "sp = I\<lparr>current_flow := fl, network_simplex_state.edge_state := es\<rparr>"
    unfolding sp_def I_def ..
  note T = ns_loop_pad_transfer[OF dom0 mpos inv0 flen eslen fag' eag']
  from T have Dsp: "NS.ns_loop_dom sp"
    and Rsp: "network_simplex_state.return (NS.ns_loop sp) = network_simplex_state.return (NS.ns_loop I)"
    and Fsp: "\<forall>e<marc. current_flow (NS.ns_loop sp) ! e = current_flow (NS.ns_loop I) ! e"
    unfolding sp_eq by auto
  have implsame: "NS.ns_loop_impl I = NS.ns_loop I" by (rule NS.ns_loop_dom_impl_same[OF dom0])
  have invI: "NS.ns_invar (NS.ns_loop I)" by (rule ns_loop_invar[OF dom0 inv0])
  have invsp0: "NS.ns_invar sp" unfolding sp_eq
    by (rule ns_invar_flow_es_cong[OF inv0 flen eslen fag' eag'])
  have invsp: "NS.ns_invar (NS.ns_loop sp)"
    using ns_loop_invar[OF Dsp[unfolded sp_eq] ns_invar_flow_es_cong[OF inv0 flen eslen fag' eag']]
    unfolding sp_eq by simp
  have fiI: "\<forall>k\<in>{0..<m+Kart}. k < length (current_flow (NS.ns_loop I))"
    using NS.ns_invar_implD(1)[OF NS.ns_invarD(1)[OF invI]] .
  have fisp: "\<forall>k\<in>{0..<m+Kart}. k < length (current_flow (NS.ns_loop sp))"
    using NS.ns_invar_implD(1)[OF NS.ns_invarD(1)[OF invsp]] .
  have lenI: "m \<le> length (current_flow (NS.ns_loop I))" using fiI mpos by (auto simp: marc_def)
  have lensp: "m \<le> length (current_flow (NS.ns_loop sp))" using fisp mpos by (auto simp: marc_def)
  have Fk: "\<And>k. k < m+Kart \<Longrightarrow> current_flow (NS.ns_loop_impl I) ! k = current_flow (NS.ns_loop sp) ! k"
    using Fsp implsame by (auto simp: marc_def)
  have r_eq: "network_simplex_state.return (NS.ns_loop_impl I) = network_simplex_state.return (NS.ns_loop sp)"
    using implsame Rsp by simp
  have la_eq: "list_all (\<lambda>k. current_flow (NS.ns_loop_impl I) ! k = 0) [m..<m+Kart]
             = list_all (\<lambda>k. current_flow (NS.ns_loop sp) ! k = 0) [m..<m+Kart]"
    using Fk by (auto simp: list_all_iff)
  have lenIimpl: "m \<le> length (current_flow (NS.ns_loop_impl I))" using lenI implsame by simp
  have tm_eq: "take m (current_flow (NS.ns_loop_impl I)) = take m (current_flow (NS.ns_loop sp))"
    by (rule nth_take_lemma[OF lenIimpl lensp]) (use Fk in auto)
  have solveE1: "solve = (if network_simplex_state.return (NS.ns_loop_impl I) = unbounded then Neg_inf_cycle
                  else if list_all (\<lambda>k. current_flow (NS.ns_loop_impl I) ! k = 0) [m..<m+Kart]
                       then Optimum (take m (current_flow (NS.ns_loop_impl I))) else Infeasible)"
    unfolding I_def by (simp add: solve_def sf)
  show ?thesis
    using Dsp invsp0 solveE1 r_eq la_eq tm_eq by simp
qed

subsection \<open>Layer (f): the CSR build and the edged vertices\<close>

text \<open>The shared builder fills the block starts and the edges of the two CSRs of the input.\<close>

lemma csr_build_out_rule:
  "<in_fst \<mapsto>\<^sub>a fst_list * in_snd \<mapsto>\<^sub>a snd_list * ob \<mapsto>\<^sub>a (0 # replicate vcount 0) * oe \<mapsto>\<^sub>a replicate m 0>
     csr_build_into_edges vcount (in_fst, in_snd) 0 ob oe
   <\<lambda>_. in_fst \<mapsto>\<^sub>a fst_list * in_snd \<mapsto>\<^sub>a snd_list * ob \<mapsto>\<^sub>a out.inp.B_spec * oe \<mapsto>\<^sub>a out.inp.E_spec>"
  using outI.csr_build_into_rule[of "replicate m 0", unfolded csr_build_into_edges_src] by simp

lemma csr_build_in_rule:
  "<in_fst \<mapsto>\<^sub>a fst_list * in_snd \<mapsto>\<^sub>a snd_list * ib \<mapsto>\<^sub>a (0 # replicate vcount 0) * ie \<mapsto>\<^sub>a replicate m 0>
     csr_build_into_edges_tgt vcount (in_fst, in_snd) 0 ib ie
   <\<lambda>_. in_fst \<mapsto>\<^sub>a fst_list * in_snd \<mapsto>\<^sub>a snd_list * ib \<mapsto>\<^sub>a inc.inp.B_spec * ie \<mapsto>\<^sub>a inc.inp.E_spec>"
  using incI.csr_build_into_rule[of "replicate m 0", unfolded csr_build_into_edges_tgt] by simp

text \<open>Copying the block starts into the cursor array makes the arrays a collection of the input
      edges (@{thm [source] outI.graph.csr_copy_imp_rule}, @{thm [source] outI.graph.csr_assn_intro});
      after the acyclifier, the same copy turns the cursor array of the released collection
      (@{thm [source] outI.graph.csr_assn_release}) into the empty ranges at the block starts that
      Pass A appends to.\<close>

lemma csr_copy_out_init:
  assumes "length l = vcount"
  shows "<ob \<mapsto>\<^sub>a out.inp.B_spec * oe \<mapsto>\<^sub>a out.inp.E_spec * oh \<mapsto>\<^sub>a l> csr_copy_imp vcount ob oh 0
         <\<lambda>_. outI.graph.csr_assn ((!) out.inp.B_spec) (ob, oe, oh)>"
proof -
  have T: "<ob \<mapsto>\<^sub>a out.inp.B_spec * oh \<mapsto>\<^sub>a l> csr_copy_imp vcount ob oh 0
     <\<lambda>_. ob \<mapsto>\<^sub>a out.inp.B_spec * oh \<mapsto>\<^sub>a take vcount out.inp.B_spec>"
    by (rule outI.graph.csr_copy_imp_rule) (simp_all add: assms)
  have I: "ob \<mapsto>\<^sub>a out.inp.B_spec * oh \<mapsto>\<^sub>a take vcount out.inp.B_spec * oe \<mapsto>\<^sub>a out.inp.E_spec \<Longrightarrow>\<^sub>A
           outI.graph.csr_assn ((!) out.inp.B_spec) (ob, oe, oh)"
    using outI.graph.csr_assn_intro[where l = "take vcount out.inp.B_spec" and c = "(!) out.inp.B_spec"
            and Ba = ob and Ea = oe and Ca = oh]
    by (simp add: ac_simps out.graph.B_length out.graph.K_less)
  show ?thesis
    by (rule ht_cons_pre[OF _ ht_cons_post[OF ht_frame[OF T, where R = "oe \<mapsto>\<^sub>a out.inp.E_spec"] ent_true_drop(2)[OF I]]])
       (simp add: ac_simps)
qed

lemma csr_copy_in_init:
  assumes "length l = vcount"
  shows "<ib \<mapsto>\<^sub>a inc.inp.B_spec * ie \<mapsto>\<^sub>a inc.inp.E_spec * ih \<mapsto>\<^sub>a l> csr_copy_imp vcount ib ih 0
         <\<lambda>_. incI.graph.csr_assn ((!) inc.inp.B_spec) (ib, ie, ih)>"
proof -
  have T: "<ib \<mapsto>\<^sub>a inc.inp.B_spec * ih \<mapsto>\<^sub>a l> csr_copy_imp vcount ib ih 0
     <\<lambda>_. ib \<mapsto>\<^sub>a inc.inp.B_spec * ih \<mapsto>\<^sub>a take vcount inc.inp.B_spec>"
    by (rule incI.graph.csr_copy_imp_rule) (simp_all add: assms)
  have I: "ib \<mapsto>\<^sub>a inc.inp.B_spec * ih \<mapsto>\<^sub>a take vcount inc.inp.B_spec * ie \<mapsto>\<^sub>a inc.inp.E_spec \<Longrightarrow>\<^sub>A
           incI.graph.csr_assn ((!) inc.inp.B_spec) (ib, ie, ih)"
    using incI.graph.csr_assn_intro[where l = "take vcount inc.inp.B_spec" and c = "(!) inc.inp.B_spec"
            and Ba = ib and Ea = ie and Ca = ih]
    by (simp add: ac_simps inc.graph.B_length inc.graph.K_less)
  show ?thesis
    by (rule ht_cons_pre[OF _ ht_cons_post[OF ht_frame[OF T, where R = "ie \<mapsto>\<^sub>a inc.inp.E_spec"] ent_true_drop(2)[OF I]]])
       (simp add: ac_simps)
qed

lemma csr_copy_out_ranges:
  "<outI.graph.csr_assn c (ob, oe, oh)> csr_copy_imp vcount ob oh 0
   <\<lambda>_. ob \<mapsto>\<^sub>a out.inp.B_spec * oe \<mapsto>\<^sub>a out.inp.E_spec * oh \<mapsto>\<^sub>a out_lo>"
proof -
  have lo: "take vcount out.inp.B_spec = out_lo"
    by (simp add: list_eq_iff_nth_eq length_out_lo out_lo_nth out.graph.B_length)
  have T: "<ob \<mapsto>\<^sub>a out.inp.B_spec * oh \<mapsto>\<^sub>a l> csr_copy_imp vcount ob oh 0
     <\<lambda>_. ob \<mapsto>\<^sub>a out.inp.B_spec * oh \<mapsto>\<^sub>a out_lo>"
    if "length l = vcount" for l
    using outI.graph.csr_copy_imp_rule[of 0 l ob oh] that by (simp add: lo)
  have E: "ob \<mapsto>\<^sub>a out.inp.B_spec * oh \<mapsto>\<^sub>a out_lo * oe \<mapsto>\<^sub>a out.inp.E_spec \<Longrightarrow>\<^sub>A
           ob \<mapsto>\<^sub>a out.inp.B_spec * oe \<mapsto>\<^sub>a out.inp.E_spec * oh \<mapsto>\<^sub>a out_lo * true"
    by (rule ent_true_drop(2)) (simp add: ac_simps)
  show ?thesis
    apply (rule ht_cons_pre[OF outI.graph.csr_assn_release])
    apply (simp only: ex_assn_move_out)
    apply (rule ht_exEI)
    apply (subst mult.assoc[symmetric])
    apply (rule ht_extract_pre_pure)
    subgoal premises p for l
      by (rule ht_cons_pre[OF _ ht_cons_post[OF ht_frame[OF T[OF p], where R = "oe \<mapsto>\<^sub>a out.inp.E_spec"] E]])
         (simp add: ac_simps)
    done
qed

lemma csr_copy_in_ranges:
  "<incI.graph.csr_assn c (ib, ie, ih)> csr_copy_imp vcount ib ih 0
   <\<lambda>_. ib \<mapsto>\<^sub>a inc.inp.B_spec * ie \<mapsto>\<^sub>a inc.inp.E_spec * ih \<mapsto>\<^sub>a in_lo>"
proof -
  have lo: "take vcount inc.inp.B_spec = in_lo"
    by (simp add: list_eq_iff_nth_eq length_in_lo in_lo_nth inc.graph.B_length)
  have T: "<ib \<mapsto>\<^sub>a inc.inp.B_spec * ih \<mapsto>\<^sub>a l> csr_copy_imp vcount ib ih 0
     <\<lambda>_. ib \<mapsto>\<^sub>a inc.inp.B_spec * ih \<mapsto>\<^sub>a in_lo>"
    if "length l = vcount" for l
    using incI.graph.csr_copy_imp_rule[of 0 l ib ih] that by (simp add: lo)
  have E: "ib \<mapsto>\<^sub>a inc.inp.B_spec * ih \<mapsto>\<^sub>a in_lo * ie \<mapsto>\<^sub>a inc.inp.E_spec \<Longrightarrow>\<^sub>A
           ib \<mapsto>\<^sub>a inc.inp.B_spec * ie \<mapsto>\<^sub>a inc.inp.E_spec * ih \<mapsto>\<^sub>a in_lo * true"
    by (rule ent_true_drop(2)) (simp add: ac_simps)
  show ?thesis
    apply (rule ht_cons_pre[OF incI.graph.csr_assn_release])
    apply (simp only: ex_assn_move_out)
    apply (rule ht_exEI)
    apply (subst mult.assoc[symmetric])
    apply (rule ht_extract_pre_pure)
    subgoal premises p for l
      by (rule ht_cons_pre[OF _ ht_cons_post[OF ht_frame[OF T[OF p], where R = "ie \<mapsto>\<^sub>a inc.inp.E_spec"] E]])
         (simp add: ac_simps)
    done
qed

text \<open>The non-lonely vertices of @{term \<open>[v..<Suc n]\<close>}, kept as a constant so that the loop refinements
      can carry it opaquely.\<close>

definition edged_lst :: "nat \<Rightarrow> nat list" where
  "edged_lst v = filter (\<lambda>w. \<not> is_lonely w) [v..<Suc n]"

lemma edged_lst_Cons: "v \<le> n \<Longrightarrow> edged_lst v = (if is_lonely v then [] else [v]) @ edged_lst (Suc v)"
  by (simp add: edged_lst_def upt_conv_Cons del: upt_Suc)

lemma edged_lst_empty: "n < v \<Longrightarrow> edged_lst v = []"
  by (simp add: edged_lst_def)

lemma edged_lst_vs: "edged_lst (Suc 0) = edged_vs_list"
  by (simp add: edged_lst_def edged_vs_list_def vs_list_def)

lemma count_edged_imp_rule:
  "v \<le> Suc n \<Longrightarrow>
   <outI.graph.csr_assn co (ob, oe, oh) * incI.graph.csr_assn ci (ib, ie, ih)>
     count_edged_imp ob ib v n acc
   <\<lambda>r. outI.graph.csr_assn co (ob, oe, oh) * incI.graph.csr_assn ci (ib, ie, ih) *
        \<up>(r = acc + length (edged_lst v))>"
proof (induction "Suc n - v" arbitrary: v acc)
  case 0
  then have vg: "n < v" by simp
  then show ?case by (subst count_edged_imp.simps) (sep_auto simp: edged_lst_empty[OF vg])
next
  case (Suc d)
  from Suc.hyps(2) Suc.prems have vn: "v \<le> n" by simp
  hence vc: "v < vcount" by (simp add: vcount_eq)
  have d': "d = Suc n - Suc v" using Suc.hyps(2) by simp
  note IH = Suc.hyps(1)[OF d']
  show ?case
    using vn vc
    by (subst count_edged_imp.simps)
       (sep_auto heap: outI.graph.csr_empty_imp_rule incI.graph.csr_empty_imp_rule IH
                 simp: edged_lst_Cons[OF vn] is_lonely_def)
qed

lemma fill_edged_imp_rule:
  "v \<le> Suc n \<Longrightarrow> j + length (edged_lst v) \<le> length vlst \<Longrightarrow>
   <va \<mapsto>\<^sub>a vlst * outI.graph.csr_assn co (ob, oe, oh) * incI.graph.csr_assn ci (ib, ie, ih)>
     fill_edged_imp va ob ib v n j
   <\<lambda>_. va \<mapsto>\<^sub>a (take j vlst @ edged_lst v @ drop (j + length (edged_lst v)) vlst) *
        outI.graph.csr_assn co (ob, oe, oh) * incI.graph.csr_assn ci (ib, ie, ih)>"
proof (induction "Suc n - v" arbitrary: v j vlst)
  case 0
  then have vg: "n < v" by simp
  then show ?case by (subst fill_edged_imp.simps) (sep_auto simp: edged_lst_empty[OF vg])
next
  case (Suc d)
  from Suc.hyps(2) Suc.prems(1) have vn: "v \<le> n" by simp
  hence vc: "v < vcount" by (simp add: vcount_eq)
  have d': "d = Suc n - Suc v" using Suc.hyps(2) by simp
  show ?case
    using vn vc Suc.prems(2)
    by (subst fill_edged_imp.simps)
       (sep_auto heap: outI.graph.csr_empty_imp_rule incI.graph.csr_empty_imp_rule Suc.hyps(1)[OF d']
                 simp: edged_lst_Cons[OF vn] is_lonely_def take_Suc_conv_app_nth list_update_append
                       drop_update_cancel)
qed

text \<open>Exit-bridge core: the six tree arrays produced by @{const build_tree} realise the abstract
      arborescence @{const Sarb} as an @{const ndtree_assn} over @{term Varb}.  The domain / range
      structure comes from @{thm Sarb_struct}; the per-vertex value correspondence from
      @{thm Sarb_sel} together with the @{const Sprnt} / @{const Sthrd} / @{const Srvth} definitions
      (the root's parent slot is @{term 0} by @{thm [source] build_tree_inv}); the length bounds from
      @{thm [source] build_tree_inv}.  The auxiliary array is unconstrained apart from its length.\<close>
lemma ndtree_assn_Sarb:
  assumes la: "Suc vcount \<le> length auxa"
  shows "prnt_impl Ti \<mapsto>\<^sub>a ds_prnt (build_tree acyc_flow) * thrd_impl Ti \<mapsto>\<^sub>a ds_thrd (build_tree acyc_flow) *
   rvth_impl Ti \<mapsto>\<^sub>a ds_rvth (build_tree acyc_flow) * lsuc_impl Ti \<mapsto>\<^sub>a ds_lsuc (build_tree acyc_flow) *
   snum_impl Ti \<mapsto>\<^sub>a ds_snum (build_tree acyc_flow) * aux_impl Ti \<mapsto>\<^sub>a auxa
   \<Longrightarrow>\<^sub>A ndtree_assn Varb Sarb Ti"
proof -
  have bt: "dfs_sized (build_tree acyc_flow)" "ds_prnt (build_tree acyc_flow) ! vcount = 0"
    using build_tree_inv[of acyc_flow] by (simp_all add: dfs_inv_def tree_seen_inv_def)
  note lens = bt(1)[unfolded dfs_sized_def]
  have vsub: "Varb \<subseteq> {0..<Suc vcount}" by (auto simp: Varb_def Vseen_def)
  have vaux: "Varb \<subseteq> {0..<length auxa}" using vsub la by auto
  have prnt_cond: "\<forall>v\<in>Varb. (\<forall>u. prnt Sarb v = Some u \<longrightarrow> ds_prnt (build_tree acyc_flow) ! v = u) \<and> (prnt Sarb v = None \<longrightarrow> ds_prnt (build_tree acyc_flow) ! v = 0)"
    by (auto simp: Sarb_sel Sprnt_def bt(2) Varb_def Vseen_def)
  have thrd_cond: "\<forall>v\<in>Varb. (\<forall>u. thrd Sarb v = Some u \<longrightarrow> ds_thrd (build_tree acyc_flow) ! v = u) \<and> (thrd Sarb v = None \<longrightarrow> ds_thrd (build_tree acyc_flow) ! v = 0)"
    by (auto simp: Sarb_sel Sthrd_def)
  have rvth_cond: "\<forall>v\<in>Varb. (\<forall>u. rvth Sarb v = Some u \<longrightarrow> ds_rvth (build_tree acyc_flow) ! v = u) \<and> (rvth Sarb v = None \<longrightarrow> ds_rvth (build_tree acyc_flow) ! v = 0)"
    by (auto simp: Sarb_sel Srvth_def)
  have ls_cond: "\<forall>v\<in>Varb. lsuc Sarb v = ds_lsuc (build_tree acyc_flow) ! v \<and> snum Sarb v = ds_snum (build_tree acyc_flow) ! v"
    by (simp add: Sarb_sel)
  have lsuc_in: "\<forall>v\<in>Varb. ds_lsuc (build_tree acyc_flow) ! v \<in> Varb" using Sarb_lsuc_in by (simp add: Sarb_sel)
  show ?thesis
    unfolding ndtree_assn_def
    apply (rule ent_ex_postI[where x="ds_prnt (build_tree acyc_flow)"])
    apply (rule ent_ex_postI[where x="ds_thrd (build_tree acyc_flow)"])
    apply (rule ent_ex_postI[where x="ds_rvth (build_tree acyc_flow)"])
    apply (rule ent_ex_postI[where x="ds_lsuc (build_tree acyc_flow)"])
    apply (rule ent_ex_postI[where x="ds_snum (build_tree acyc_flow)"])
    apply (rule ent_ex_postI[where x="auxa"])
    apply (sep_auto simp: zero_notin_Varb Sarb_struct vsub vaux lens prnt_cond thrd_cond rvth_cond ls_cond lsuc_in)
    done
qed


text \<open>The arborescence lives inside @{term \<open>{0..<Suc vcount}\<close>}, so the two path buffers the
      network-simplex loop demands (each of length at least @{term \<open>card Varb - 1\<close>}) are covered by the
      DFS stack arrays, whose length is @{term \<open>Suc vcount\<close>}.\<close>
lemma card_Varb_le: "card Varb \<le> Suc vcount"
proof -
  have "Varb \<subseteq> {0..<Suc vcount}" by (auto simp: Varb_def Vseen_def)
  from card_mono[OF _ this] show ?thesis by simp
qed


text \<open>The network-simplex phase of @{const solve_imp}, packaged as one Hoare triple over the raw arrays
      the tree builder leaves behind.  It bridges into @{thm [source] ns_loop_prog_rule} and reads the
      functional verdict off @{thm [source] solve_via_padded}: on exit the flow
      array holds a list whose @{term m}-prefix is the optimum whenever @{const solve} says so, and the
      returned flag decides the three verdicts.  The padded stores are related to the augmented
      @{const flow_all} / @{const state_all} on the real range @{term \<open>{0..<m+Kart}\<close>}, which is exactly
      what the tree builder's @{const dfs_rel} guarantees.\<close>
lemma ns_phase_core:
  assumes some: "acyc_flow_opt \<noteq> None" and mpos: "0 < marc"
    and lf: "marc \<le> length fsta" and ls: "marc \<le> length snda" and lc: "marc \<le> length capa"
    and af: "\<And>e. e < marc \<Longrightarrow> fsta ! e = fst_all ! e"
    and as: "\<And>e. e < marc \<Longrightarrow> snda ! e = snd_all ! e"
    and ac: "\<And>e. e < marc \<Longrightarrow> capa ! e = cap_all ! e"
    and flen: "\<forall>k\<in>{0..<m+Kart}. k < length flowa" and fag: "\<And>k. k < m+Kart \<Longrightarrow> flowa ! k = flow_all ! k"
    and eslen: "\<forall>k\<in>{0..<m+Kart}. k < length esa" and eag: "\<And>k. k < m+Kart \<Longrightarrow> esa ! k = state_all ! k"
    and laux: "Suc vcount \<le> length auxa"
    and lsv: "card Varb - 1 \<le> length svl" and lsoc: "card Varb - 1 \<le> length socl"
    and LF: "marc \<le> length fst_all" and LS: "marc \<le> length snd_all" and LC: "marc \<le> length cap_all"
  shows
  "<(cap_arr \<mapsto>\<^sub>a capa * cost_arr \<mapsto>\<^sub>a cost_list * fst_arr \<mapsto>\<^sub>a fsta * snd_arr \<mapsto>\<^sub>a snda) *
    (prnt_impl Ti \<mapsto>\<^sub>a ds_prnt (build_tree acyc_flow) * thrd_impl Ti \<mapsto>\<^sub>a ds_thrd (build_tree acyc_flow) *
     rvth_impl Ti \<mapsto>\<^sub>a ds_rvth (build_tree acyc_flow) * lsuc_impl Ti \<mapsto>\<^sub>a ds_lsuc (build_tree acyc_flow) *
     snum_impl Ti \<mapsto>\<^sub>a ds_snum (build_tree acyc_flow) * aux_impl Ti \<mapsto>\<^sub>a auxa *
     fa \<mapsto>\<^sub>a flowa * pa \<mapsto>\<^sub>a ds_pot (build_tree acyc_flow) *
     pare \<mapsto>\<^sub>a ds_par (build_tree acyc_flow) * dire \<mapsto>\<^sub>a ds_dir (build_tree acyc_flow) *
     esaa \<mapsto>\<^sub>a esa * sarr \<mapsto>\<^sub>a replicate max_candidates 0 * cref \<mapsto>\<^sub>r 0 * lref \<mapsto>\<^sub>r 0 *
     p1 \<mapsto>\<^sub>a svl * p2 \<mapsto>\<^sub>a socl)>
    ns_loop_prog vcount m marc block_size min_candidates max_candidates fst_arr snd_arr cost_arr cap_arr
      (ns_impl_state.make fa pa Ti pare dire esaa (sarr, cref, lref) p1 p2)
   <\<lambda>res. (\<exists>\<^sub>A fl'. fa \<mapsto>\<^sub>a fl' * cost_arr \<mapsto>\<^sub>a cost_list *
            \<up>(marc \<le> length fl' \<and>
              solve = (if res = Network_Simplex.unbounded then Neg_inf_cycle
                       else if list_all (\<lambda>k. fl' ! k = 0) [m..<marc]
                            then Optimum (take m fl') else Infeasible))) * true>"
proof -
  define sp where "sp = (network_simplex_init_spec.init_state flow_all (ds_pot art_tree) (tree_st art_tree)
                   (ds_par art_tree) (ds_dir art_tree) state_all init_sel)
                 \<lparr>current_flow := flowa, network_simplex_state.edge_state := esa\<rparr>"
  have LCO: "m \<le> length cost_list" by (simp add: length_cost_list_m)
  note T = solve_via_padded[OF some mpos flen eslen fag eag]
  have D: "NS.ns_loop_dom sp" and Inv: "NS.ns_invar sp"
    and SOLVE: "solve = (if network_simplex_state.return (NS.ns_loop sp) = unbounded then Neg_inf_cycle
                  else if list_all (\<lambda>k. current_flow (NS.ns_loop sp) ! k = 0) [m..<m+Kart]
                       then Optimum (take m (current_flow (NS.ns_loop sp))) else Infeasible)"
    using T unfolding sp_def by auto
  have invsp: "NS.ns_invar (NS.ns_loop sp)" by (rule ns_loop_invar[OF D Inv])
  have fisp: "\<forall>k\<in>{0..<m+Kart}. k < length (current_flow (NS.ns_loop sp))"
    using NS.ns_invar_implD(1)[OF NS.ns_invarD(1)[OF invsp]] .
  have lensp: "marc \<le> length (current_flow (NS.ns_loop sp))"
  proof -
    have "marc - 1 < length (current_flow (NS.ns_loop sp))" using fisp mpos by (auto simp: marc_def)
    thus ?thesis using mpos by simp
  qed
  note selred = sp_def network_simplex_init_spec.init_state_def art_tree_def
                Sarb_tree_st[symmetric, unfolded art_tree_def] ns_impl_state.make_def
                flow_assn_ns_def pot_assn_ns_def parent_assn_ns_def dir_assn_ns_def
                es_assn_ns_def sel_assn_ns_def init_sel_def
  show ?thesis
    apply (rule ht_cons_post_prec[OF ht_cons_pre[OF _
             ns_loop_prog_rule[where s = sp
               and si = "ns_impl_state.make fa pa Ti pare dire esaa (sarr, cref, lref) p1 p2",
               OF LF LS LC LCO lf ls lc af as ac Inv]]])
     apply (simp add: selred)
     apply (rule ent_ex_postI[where x=svl], rule ent_ex_postI[where x=socl])
     apply (rule ent_frame_fwdI[OF _ ndtree_assn_Sarb[OF laux],
         where F="cap_arr \<mapsto>\<^sub>a capa * cost_arr \<mapsto>\<^sub>a cost_list * fst_arr \<mapsto>\<^sub>a fsta * snd_arr \<mapsto>\<^sub>a snda *
                  fa \<mapsto>\<^sub>a flowa * pa \<mapsto>\<^sub>a ds_pot (build_tree acyc_flow) *
                  pare \<mapsto>\<^sub>a ds_par (build_tree acyc_flow) * dire \<mapsto>\<^sub>a ds_dir (build_tree acyc_flow) *
                  esaa \<mapsto>\<^sub>a esa * sarr \<mapsto>\<^sub>a replicate max_candidates 0 * cref \<mapsto>\<^sub>r 0 * lref \<mapsto>\<^sub>r 0 *
                  p1 \<mapsto>\<^sub>a svl * p2 \<mapsto>\<^sub>a socl"])
      apply sep_auto
     apply (sep_auto simp: lsv[unfolded One_nat_def] lsoc[unfolded One_nat_def])
    apply (rule ent_ex_preI)+
    apply (rule ent_ex_postI[of _ _ "current_flow (NS.ns_loop sp)"])
    apply (sep_auto simp: ns_impl_state.make_def flow_assn_ns_def lensp[unfolded marc_def] SOLVE marc_def)
    done
qed

text \<open>Agreement transfer, once for all four augmented arrays: a padded working array that matches the
      \<^emph>\<open>real\<close> input list below @{term m} and the builder's \<^emph>\<open>artificial tail\<close> above it agrees with the
      augmented list @{term \<open>xl @ take Kart xt\<close>} on the whole arc range @{term \<open>{0..<marc}\<close>}.  Applied
      with @{term xl}/@{term xt} instantiated to @{term fst_list}/@{term \<open>ds_afst art_tree\<close>} and the
      corresponding pairs for @{const snd_all}, @{const cap_all}, @{const flow_all}, @{const state_all}.\<close>
lemma agree_marc:
  assumes a1: "\<forall>e<m. xa ! e = xl ! e" and a2: "\<forall>k<Kart. xa ! (m+k) = xt ! k"
      and len: "length xl = m" and kt: "Kart \<le> length xt"
  shows "\<forall>e<marc. xa ! e = (xl @ take Kart xt) ! e"
proof (intro allI impI)
  fix e assume "e < marc"
  hence e: "e < m + Kart" by (simp add: marc_def)
  show "xa ! e = (xl @ take Kart xt) ! e"
  proof (cases "e < m")
    case True thus ?thesis using a1 len by (simp add: nth_append)
  next
    case False
    hence me: "e = m + (e - m)" by simp
    have kK: "e - m < Kart" using e False by simp
    have l1: "xa ! e = xt ! (e - m)" using a2 kK me by metis
    have l2: "(xl @ take Kart xt) ! e = take Kart xt ! (e - m)" using False len by (simp add: nth_append)
    have l3: "take Kart xt ! (e - m) = xt ! (e - m)" using kK kt by simp
    show ?thesis using l1 l2 l3 by simp
  qed
qed


text \<open>The network-simplex phase over the tree builder's own state relation.  Unfolding
      @{const dfs_rel} exposes the working lists and the pure conjunct block; @{thm agree_marc} turns the
      ``real prefix + artificial tail'' agreements into agreement with the augmented @{const fst_all} /
      @{const snd_all} / @{const cap_all} / @{const flow_all} / @{const state_all} on all of
      @{term \<open>{0..<marc}\<close>}; the DFS stack array and the acyclifier's second stack array serve as the
      loop's path buffers, and the stores the loop does not touch travel through as a frame.\<close>
lemma ns_phase_triple:
  assumes some: "acyc_flow_opt \<noteq> None" and mpos: "0 < marc" and lel: "length el = Suc vcount"
  shows
  "<sarr \<mapsto>\<^sub>a replicate max_candidates 0 * cref \<mapsto>\<^sub>r 0 * lref \<mapsto>\<^sub>r 0 * est \<mapsto>\<^sub>a el *
    dfs_rel acyc_flow (edge_state acyc_flow) st (build_tree acyc_flow)>
    ns_loop_prog vcount m marc block_size min_candidates max_candidates
      (di_fst st) (di_snd st) (di_cost st) (di_cap st)
      (ns_impl_state.make (di_flow st) (di_pot st) (di_tree st) (di_par st) (di_dir st) (di_es st)
                          (sarr, cref, lref) (di_stk st) est)
   <\<lambda>res. (\<exists>\<^sub>A fl'. di_flow st \<mapsto>\<^sub>a fl' * di_cost st \<mapsto>\<^sub>a cost_list *
            \<up>(marc \<le> length fl' \<and>
              solve = (if res = Network_Simplex.unbounded then Neg_inf_cycle
                       else if list_all (\<lambda>k. fl' ! k = 0) [m..<marc]
                            then Optimum (take m fl') else Infeasible))) * true>"
  unfolding dfs_rel_def
  apply (simp only: ex_assn_move_out)
  apply (rule ht_exEI)+
  apply (simp only: mult.assoc[symmetric])
  apply (rule ht_extract_pre_pure(1))
  subgoal premises P for fsta snda capa flowa esa auxa stl sp
  proof -
    have Kdef: "Kart = ds_nxt (build_tree acyc_flow)" by (simp add: Kart_def art_tree_def)
    have KA: "Kart \<le> length (ds_afst (build_tree acyc_flow))" using Kart_le len_afst_bt by simp
    have KB: "Kart \<le> length (ds_asnd (build_tree acyc_flow))" using Kart_le len_asnd_bt by simp
    have KC: "Kart \<le> length (ds_acap (build_tree acyc_flow))" using Kart_le len_acap_bt by simp
    have KD: "Kart \<le> length (ds_aflw (build_tree acyc_flow))" using Kart_le len_aflw_bt by simp
    have KE: "Kart \<le> length (ds_aest (build_tree acyc_flow))" using Kart_le len_aest_bt by simp
    have lf: "marc \<le> length fsta" using P KA by (simp add: marc_def)
    have ls: "marc \<le> length snda" using P KB by (simp add: marc_def)
    have lc: "marc \<le> length capa" using P KC by (simp add: marc_def)
    have af: "\<forall>e<marc. fsta ! e = fst_all ! e"
      using agree_marc[of fsta fst_list "ds_afst (build_tree acyc_flow)"] P Kdef KA
      by (simp add: fst_all_def art_tree_def length_fst_list_m)
    have as: "\<forall>e<marc. snda ! e = snd_all ! e"
      using agree_marc[of snda snd_list "ds_asnd (build_tree acyc_flow)"] P Kdef KB
      by (simp add: snd_all_def art_tree_def length_snd_list_m)
    have ac: "\<forall>e<marc. capa ! e = cap_all ! e"
      using agree_marc[of capa capacity_list "ds_acap (build_tree acyc_flow)"] P Kdef KC
      by (simp add: cap_all_def art_tree_def length_edges)
    have afl: "\<forall>e<marc. flowa ! e = flow_all ! e"
      using agree_marc[of flowa acyc_flow "ds_aflw (build_tree acyc_flow)"] P Kdef KD
      by (simp add: flow_all_def art_tree_def length_acyc_flow)
    have aes: "\<forall>e<marc. esa ! e = state_all ! e"
      using agree_marc[of esa "edge_state acyc_flow" "ds_aest (build_tree acyc_flow)"] P Kdef KE
      by (simp add: state_all_def art_tree_def length_edge_state)
    have flen: "\<forall>k\<in>{0..<m+Kart}. k < length flowa" using P KD by auto
    have eslen: "\<forall>k\<in>{0..<m+Kart}. k < length esa" using P KE by auto
    have laux: "Suc vcount \<le> length auxa" using P by simp
    have lsv: "card Varb - 1 \<le> length stl" using P card_Varb_le by simp
    have lsoc: "card Varb - 1 \<le> length el" using lel card_Varb_le by simp
    have LF: "marc \<le> length fst_all" by (simp add: marc_def)
    have LS: "marc \<le> length snd_all" by (simp add: marc_def)
    have LC: "marc \<le> length cap_all" by (simp add: marc_def)
    note CORE = ns_phase_core[OF some mpos lf ls lc af[rule_format] as[rule_format] ac[rule_format]
          flen afl[rule_format, unfolded marc_def] eslen aes[rule_format, unfolded marc_def]
          laux lsv lsoc LF LS LC]
    show ?thesis
      apply (rule ht_cons_post_prec[OF ht_cons_pre[OF _ ht_frame[OF CORE,
          where R="FO.csr_assn (ds_oc (build_tree acyc_flow)) (di_ob st, di_oe st, di_oc st) *
                   di_oh st \<mapsto>\<^sub>a fst (free_out acyc_flow) *
                   FI.csr_assn (ds_ic (build_tree acyc_flow)) (di_ib st, di_ie st, di_ic st) *
                   di_ih st \<mapsto>\<^sub>a fst (free_in acyc_flow) *
                   di_seen st \<mapsto>\<^sub>a ds_seen (build_tree acyc_flow) * di_sp st \<mapsto>\<^sub>r sp *
                   di_prev st \<mapsto>\<^sub>r ds_prev (build_tree acyc_flow) *
                   di_nxt st \<mapsto>\<^sub>r ds_nxt (build_tree acyc_flow)"]]])
      apply sep_auto
      done
  qed
  done

text \<open>The loop phase, reshaped for composition: the caller's flow array @{term in_flow} is threaded
      through untouched and the pure conjunct is moved \<^emph>\<open>last\<close>.\<close>
lemma ns_phase_triple':
  assumes some: "acyc_flow_opt \<noteq> None" and mpos: "0 < marc" and lel: "length el = Suc vcount"
  shows "<sarr \<mapsto>\<^sub>a replicate max_candidates 0 * cref \<mapsto>\<^sub>r 0 * lref \<mapsto>\<^sub>r 0 * est \<mapsto>\<^sub>a el *
          dfs_rel acyc_flow (edge_state acyc_flow) st (build_tree acyc_flow) * in_flow \<mapsto>\<^sub>a fs0>
         ns_loop_prog vcount m marc block_size min_candidates max_candidates (di_fst st) (di_snd st) (di_cost st) (di_cap st)
           (ns_impl_state.make (di_flow st) (di_pot st) (di_tree st) (di_par st) (di_dir st) (di_es st) (sarr, cref, lref) (di_stk st) est)
         <\<lambda>res. \<exists>\<^sub>A fl'. di_flow st \<mapsto>\<^sub>a fl' * di_cost st \<mapsto>\<^sub>a cost_list * in_flow \<mapsto>\<^sub>a fs0 * true *
           \<up>(marc \<le> length fl' \<and> solve = (if res = Network_Simplex.unbounded then Neg_inf_cycle
              else if list_all (\<lambda>k. fl' ! k = 0) [m..<marc] then Optimum (take m fl') else Infeasible))>"
  apply (rule ht_cons_post_prec[OF ht_frame[OF ns_phase_triple[OF some mpos lel], where R="in_flow \<mapsto>\<^sub>a fs0"]])
  apply sep_auto
  done

subsection \<open>Layer (g): assembling @{const solve_imp}\<close>

text \<open>The acyclifier phase of @{const solve_imp}, over the arrays the allocation and CSR phases leave
      behind.\<close>
lemma make_acyclic_solve_triple:
  "<fh \<mapsto>\<^sub>a (flow_list @ replicate n 0) * sh \<mapsto>\<^sub>a (Unseen # replicate vcount Unseen) *
    outI.graph.csr_assn ((!) out.inp.B_spec) Oi * incI.graph.csr_assn ((!) inc.inp.B_spec) Ii *
    vl \<mapsto>\<^sub>a edged_vs_list * pr \<mapsto>\<^sub>r 0 *
    cap_arr \<mapsto>\<^sub>a (capacity_list @ replicate n 0) * cost_arr \<mapsto>\<^sub>a cost_list *
    fst_arr \<mapsto>\<^sub>a (fst_list @ replicate n 0) * snd_arr \<mapsto>\<^sub>a (snd_list @ replicate n 0) *
    vst \<mapsto>\<^sub>a (0 # replicate vcount 0) * est \<mapsto>\<^sub>a (0 # replicate vcount 0) * dst \<mapsto>\<^sub>a (False # replicate vcount False)>
   make_acyclic_prog cap_arr cost_arr fst_arr snd_arr fh sh Oi Ii (vl, pr) vst est dst
   <\<lambda>r. \<exists>\<^sub>A f' c_o c_i. flow_assn_m f' fh *
        outI.graph.csr_assn c_o Oi * incI.graph.csr_assn c_i Ii *
        (cap_arr \<mapsto>\<^sub>a (capacity_list @ replicate n 0) * cost_arr \<mapsto>\<^sub>a cost_list *
         fst_arr \<mapsto>\<^sub>a (fst_list @ replicate n 0) * snd_arr \<mapsto>\<^sub>a (snd_list @ replicate n 0)) *
        (\<exists>\<^sub>A vl' el' dl'. vst \<mapsto>\<^sub>a vl' * est \<mapsto>\<^sub>a el' * dst \<mapsto>\<^sub>a dl' *
           \<up>(length vl' = Suc vcount \<and> length el' = Suc vcount \<and> length dl' = Suc vcount)) *
        true *
        \<up>((r \<longleftrightarrow> make_acyclic flow_list = None) \<and> (make_acyclic flow_list = None \<or> make_acyclic flow_list = Some f'))>"
proof -
  have lf: "length flow_list = m" by (simp add: length_flow length_edges)
  have cardn: "card original_network.\<V> \<le> Suc vcount"
  proof -
    have "card original_network.\<V> \<le> card (set vs_list)" using card_mono[OF finite_set V_sub_vs_list] .
    also have "\<dots> \<le> length vs_list" by (rule card_length)
    also have "\<dots> = n" by (rule length_vs_list)
    finally show ?thesis by (simp add: vcount_eq)
  qed
  have cardv: "card original_network.\<V> \<le> length (0 # replicate vcount (0::nat))" using cardn by simp
  have cardb: "card original_network.\<V> \<le> length (False # replicate vcount False)" using cardn by simp
  have cl_len: "m \<le> length (capacity_list @ replicate n 0)" by (simp add: length_edges)
  have cl_eq: "\<And>e. e < m \<Longrightarrow> (capacity_list @ replicate n 0) ! e = capacity_list ! e"
    by (simp add: nth_append length_edges)
  have co_len: "m \<le> length cost_list" by (simp add: length_cost_list_m)
  have co_eq: "\<And>e. e < m \<Longrightarrow> cost_list ! e = cost_list ! e" by simp
  have fla_len: "m \<le> length (fst_list @ replicate n 0)" by (simp add: length_fst_list_m)
  have fla_eq: "\<And>e. e < m \<Longrightarrow> (fst_list @ replicate n 0) ! e = fst_list ! e"
    by (simp add: nth_append length_fst_list_m)
  have sla_len: "m \<le> length (snd_list @ replicate n 0)" by (simp add: length_snd_list_m)
  have sla_eq: "\<And>e. e < m \<Longrightarrow> (snd_list @ replicate n 0) ! e = snd_list ! e"
    by (simp add: nth_append length_snd_list_m)
  have ent: "fh \<mapsto>\<^sub>a (flow_list @ replicate n 0) * sh \<mapsto>\<^sub>a (Unseen # replicate vcount Unseen) *
    outI.graph.csr_assn ((!) out.inp.B_spec) Oi * incI.graph.csr_assn ((!) inc.inp.B_spec) Ii *
    vl \<mapsto>\<^sub>a edged_vs_list * pr \<mapsto>\<^sub>r 0 *
    cap_arr \<mapsto>\<^sub>a (capacity_list @ replicate n 0) * cost_arr \<mapsto>\<^sub>a cost_list *
    fst_arr \<mapsto>\<^sub>a (fst_list @ replicate n 0) * snd_arr \<mapsto>\<^sub>a (snd_list @ replicate n 0) *
    vst \<mapsto>\<^sub>a (0 # replicate vcount 0) * est \<mapsto>\<^sub>a (0 # replicate vcount 0) * dst \<mapsto>\<^sub>a (False # replicate vcount False)
    \<Longrightarrow>\<^sub>A
    flow_assn_m flow_list fh * state_assn_v (replicate vcount Unseen) sh *
    outI.graph.csr_assn ((!) out.inp.B_spec) Oi * incI.graph.csr_assn ((!) inc.inp.B_spec) Ii *
    lc_assn \<lparr>lc_list = edged_vs_list, lc_pos = 0\<rparr> (vl, pr) *
    (cap_arr \<mapsto>\<^sub>a (capacity_list @ replicate n 0) * cost_arr \<mapsto>\<^sub>a cost_list *
     fst_arr \<mapsto>\<^sub>a (fst_list @ replicate n 0) * snd_arr \<mapsto>\<^sub>a (snd_list @ replicate n 0)) *
    vst \<mapsto>\<^sub>a (0 # replicate vcount 0) * est \<mapsto>\<^sub>a (0 # replicate vcount 0) * dst \<mapsto>\<^sub>a (False # replicate vcount False)"
    unfolding flow_assn_m_def state_assn_v_def lc_assn_def
    apply (simp only: ex_assn_move_out)
    apply (rule ent_ex_postI[where x = "[Unseen]"])
    apply (rule ent_ex_postI[where x = "replicate n 0"])
    apply (sep_auto simp: lf replicate_append_same)
    done
  show ?thesis
    apply (rule ht_cons_pre[OF ent])
    apply (rule ht_cons_post_prec[OF make_acyclic_prog_rule[OF cl_len cl_eq co_len co_eq fla_len fla_eq sla_len sla_eq lf
                af_cap_feasible_flow_list cardv cardv cardb]])
    apply (all \<open>(assumption)?\<close>)
    apply (intro ent_ex_preI)
    apply (rule ent_ex_postI)+
    apply (rule ent_star_mono ent_refl)+
    apply sep_auto
    done
qed

text \<open>Pass A, the imbalance transform and the clearing of the seen array, over the arrays the
      acyclifier leaves behind: afterwards every store holds the functional value the tree builder
      consumes.\<close>
lemma passA_phase_triple:
  fixes fl_arr cap_arr exc_arr ba :: "'n array" and fsta snda ob oe oh ib ie ih :: "nat array"
    and es_arr :: "edge_tag array" and dsta :: "bool array"
  assumes some: "acyc_flow_opt = Some f'" and mfla: "m \<le> length fla"
    and agfla: "\<forall>e<m. fla ! e = acyc_flow ! e" and ldl: "length dl = Suc vcount"
  shows "<fl_arr \<mapsto>\<^sub>a fla * cap_arr \<mapsto>\<^sub>a (capacity_list @ replicate n 0) * fsta \<mapsto>\<^sub>a (fst_list @ replicate n 0) *
          snda \<mapsto>\<^sub>a (snd_list @ replicate n 0) * es_arr \<mapsto>\<^sub>a replicate (m + n) InL * exc_arr \<mapsto>\<^sub>a (0 # replicate vcount 0) *
          outI.graph.csr_assn c_o (ob, oe, oh) * incI.graph.csr_assn c_i (ib, ie, ih) * ba \<mapsto>\<^sub>a b_arr * dsta \<mapsto>\<^sub>a dl>
         do { _ \<leftarrow> csr_copy_imp vcount ob oh 0; _ \<leftarrow> csr_copy_imp vcount ib ih 0;
              _ \<leftarrow> passA_imp fl_arr cap_arr fsta snda es_arr exc_arr oe oh ie ih 0 m;
              _ \<leftarrow> imbalance_imp exc_arr ba 0 vcount; arr_fill_imp dsta False 0 (Suc vcount) }
         <\<lambda>_. fl_arr \<mapsto>\<^sub>a fla * cap_arr \<mapsto>\<^sub>a (capacity_list @ replicate n 0) * fsta \<mapsto>\<^sub>a (fst_list @ replicate n 0) *
             snda \<mapsto>\<^sub>a (snd_list @ replicate n 0) * es_arr \<mapsto>\<^sub>a (edge_state acyc_flow @ replicate n InL) *
             exc_arr \<mapsto>\<^sub>a imbalance * ob \<mapsto>\<^sub>a out.inp.B_spec * oe \<mapsto>\<^sub>a snd (free_out acyc_flow) *
             oh \<mapsto>\<^sub>a fst (free_out acyc_flow) * ib \<mapsto>\<^sub>a inc.inp.B_spec * ie \<mapsto>\<^sub>a snd (free_in acyc_flow) *
             ih \<mapsto>\<^sub>a fst (free_in acyc_flow) * ba \<mapsto>\<^sub>a b_arr * dsta \<mapsto>\<^sub>a replicate (Suc vcount) False>"
proof -
  have rep_es: "replicate (m + n) InL = replicate m InL @ replicate n InL" by (simp add: replicate_add)
  have caplen: "m \<le> length (capacity_list @ replicate n 0)" by (simp add: length_edges)
  have capeq: "\<And>i. i < m \<Longrightarrow> (capacity_list @ replicate n 0) ! i = capacity_list ! i"
    by (simp add: nth_append length_edges)
  have fstlen: "m \<le> length (fst_list @ replicate n 0)" by (simp add: length_fst_list_m)
  have fsteq: "\<And>i. i < m \<Longrightarrow> (fst_list @ replicate n 0) ! i = fst_list ! i"
    by (simp add: nth_append length_fst_list_m)
  have sndlen: "m \<le> length (snd_list @ replicate n 0)" by (simp add: length_snd_list_m)
  have sndeq: "\<And>i. i < m \<Longrightarrow> (snd_list @ replicate n 0) ! i = snd_list ! i"
    by (simp add: nth_append length_snd_list_m)
  have s0: "(replicate m InL, 0 # replicate vcount 0, (out_lo, out.inp.E_spec), (in_lo, inc.inp.E_spec)) =
            fold (passA_step acyc_flow) [0..<0]
              (replicate m InL, replicate (Suc vcount) (0::'n), (out_lo, out.inp.E_spec), (in_lo, inc.inp.E_spec))"
    by simp
  note PA = passA_imp_rule[OF le0 mfla agfla[rule_format] caplen capeq fstlen fsteq sndlen sndeq s0,
              where esr = "replicate n InL", simplified]
  have E1: "fst (passA acyc_flow) = edge_state acyc_flow" by (simp add: edge_state_def split_beta)
  have E2: "fst (snd (passA acyc_flow)) = excess" by (rule passA_exc_acyc[OF some])
  have IMB: "<exc_arr \<mapsto>\<^sub>a excess * ba \<mapsto>\<^sub>a b_arr> imbalance_imp exc_arr ba 0 vcount
             <\<lambda>_. exc_arr \<mapsto>\<^sub>a imbalance * ba \<mapsto>\<^sub>a b_arr>"
    using imbalance_imp_rule[of 0 excess b_arr exc_arr ba]
    by (simp add: length_b_arr imbalance_def b_lookup_def)
  show ?thesis
    apply (simp only: rep_es)
    apply (sep_auto heap: csr_copy_out_ranges csr_copy_in_ranges PA IMB arr_fill_imp_rule
                    simp: ldl E1 E2)
    done
qed

text \<open>The stores the Pass-A phase leaves behind, with the freshly allocated tree arrays, the zeroed
      cursor arrays and the three fresh references, \<^emph>\<open>are\<close> the tree builder's state relation at the
      state that @{const build_tree_imp} seeds into @{const dfs_init}.\<close>
lemma dfs_rel_raw_intro:
  fixes prnt thrd rvth lsuc snum auxa par sv ob oe oh oc ib ie ih ic fsta snda :: "nat array"
    and dira dsta :: "bool array" and fl_arr cap_arr cost_arr :: "'n array"
    and es_arr :: "edge_tag array" and spr pvr nxr :: "nat ref"
  assumes mfla: "m + n \<le> length fla" and agfla: "\<forall>e<m. fla ! e = acyc_flow ! e"
    and laux: "length auxl = Suc vcount" and lsvl: "length svl = Suc vcount"
  shows "dsta \<mapsto>\<^sub>a replicate (Suc vcount) False * prnt \<mapsto>\<^sub>a (0 # replicate vcount 0) *
    thrd \<mapsto>\<^sub>a (0 # replicate vcount 0) * rvth \<mapsto>\<^sub>a (0 # replicate vcount 0) *
    lsuc \<mapsto>\<^sub>a (0 # replicate vcount 0) * snum \<mapsto>\<^sub>a (0 # replicate vcount 0) * auxa \<mapsto>\<^sub>a auxl *
    par \<mapsto>\<^sub>a (0 # replicate vcount 0) * dira \<mapsto>\<^sub>a (False # replicate vcount False) *
    pot \<mapsto>\<^sub>a (pval_zero # replicate vcount pval_zero) * fsta \<mapsto>\<^sub>a (fst_list @ replicate n 0) *
    snda \<mapsto>\<^sub>a (snd_list @ replicate n 0) * cap_arr \<mapsto>\<^sub>a (capacity_list @ replicate n 0) *
    cost_arr \<mapsto>\<^sub>a cost_list * fl_arr \<mapsto>\<^sub>a fla * es_arr \<mapsto>\<^sub>a (edge_state acyc_flow @ replicate n InL) *
    ob \<mapsto>\<^sub>a out.inp.B_spec * oe \<mapsto>\<^sub>a snd (free_out acyc_flow) * oh \<mapsto>\<^sub>a fst (free_out acyc_flow) *
    oc \<mapsto>\<^sub>a replicate vcount 0 *
    ib \<mapsto>\<^sub>a inc.inp.B_spec * ie \<mapsto>\<^sub>a snd (free_in acyc_flow) * ih \<mapsto>\<^sub>a fst (free_in acyc_flow) *
    ic \<mapsto>\<^sub>a replicate vcount 0 *
    sv \<mapsto>\<^sub>a svl * spr \<mapsto>\<^sub>r 0 * pvr \<mapsto>\<^sub>r 0 * nxr \<mapsto>\<^sub>r 0
    \<Longrightarrow>\<^sub>A dfs_rel acyc_flow (edge_state acyc_flow)
      \<lparr>di_seen = dsta, di_tree = \<lparr>prnt_impl = prnt, thrd_impl = thrd, rvth_impl = rvth, lsuc_impl = lsuc,
                                 snum_impl = snum, aux_impl = auxa\<rparr>,
       di_par = par, di_dir = dira, di_pot = pot, di_fst = fsta, di_snd = snda, di_cap = cap_arr,
       di_cost = cost_arr, di_flow = fl_arr, di_es = es_arr,
       di_ob = ob, di_oe = oe, di_oh = oh, di_oc = oc, di_ib = ib, di_ie = ie, di_ih = ih, di_ic = ic,
       di_stk = sv, di_sp = spr, di_prev = pvr, di_nxt = nxr\<rparr>
      (dfs_init\<lparr>ds_snum := replicate (Suc vcount) 0, ds_prev := 0\<rparr>)"
proof -
  have O: "ob \<mapsto>\<^sub>a out.inp.B_spec * oe \<mapsto>\<^sub>a snd (free_out acyc_flow) * oc \<mapsto>\<^sub>a replicate vcount 0 \<Longrightarrow>\<^sub>A
           FO.csr_assn (\<lambda>_. 0) (ob, oe, oc)"
    by (rule FO.csr_assn_intro) simp_all
  have I: "ib \<mapsto>\<^sub>a inc.inp.B_spec * ie \<mapsto>\<^sub>a snd (free_in acyc_flow) * ic \<mapsto>\<^sub>a replicate vcount 0 \<Longrightarrow>\<^sub>A
           FI.csr_assn (\<lambda>_. 0) (ib, ie, ic)"
    by (rule FI.csr_assn_intro) simp_all
  show ?thesis
  unfolding dfs_rel_def dfs_init_def
  apply (sep_frame_fwd rule: O)
  apply (sep_frame_fwd rule: I)
  apply (rule ent_ex_postI[of _ _ "fst_list @ replicate n 0"])
  apply (rule ent_ex_postI[of _ _ "snd_list @ replicate n 0"])
  apply (rule ent_ex_postI[of _ _ "capacity_list @ replicate n 0"])
  apply (rule ent_ex_postI[of _ _ "fla"])
  apply (rule ent_ex_postI[of _ _ "edge_state acyc_flow @ replicate n InL"])
  apply (rule ent_ex_postI[of _ _ "auxl"])
  apply (rule ent_ex_postI[of _ _ "svl"])
  apply (rule ent_ex_postI[of _ _ "0::nat"])
  apply (sep_auto simp: laux lsvl mfla agfla length_vs_list length_fst_list_m length_snd_list_m
                        length_edges nth_append)
  done
qed

text \<open>The acyclifier's flow assertion, weakened to exactly what the tree builder needs: a store of at
      least the augmented length whose real-edge prefix is @{const acyc_flow}.  Extracting \<^emph>\<open>this\<close> pure
      part (rather than @{const flow_assn_m}'s @{term \<open>length r = n\<close>}) keeps an equation on the locale
      parameter @{term n} out of the proof context.\<close>
lemma flow_assn_m_pad:
  assumes some: "acyc_flow_opt = Some f'"
  shows "flow_assn_m f' fh \<Longrightarrow>\<^sub>A (\<exists>\<^sub>A fla. fh \<mapsto>\<^sub>a fla * \<up>(m + n \<le> length fla \<and> (\<forall>e<m. fla ! e = acyc_flow ! e)))"
proof -
  have acy: "acyc_flow = f'" using some by (simp add: acyc_flow_def)
  show ?thesis
    unfolding flow_assn_m_def
    apply (rule ent_ex_preI)
    apply (rule ent_ex_postI[of _ _ "f' @ x" for x])
    apply (sep_auto simp: acy[symmetric] nth_append)
    done
qed

text \<open>Two rules restated with the state record's \<^emph>\<open>components\<close> as separate parameters plus defining
      equations.  In @{const solve_imp} the DFS state record is built from array / reference
      variables bound by the program itself, so a rule whose program mentions @{term \<open>di_nxt st\<close>} can
      never be unified against the program's @{term \<open>Ref.lookup nxt_ref\<close>}: higher-order unification
      would have to invert a record selector.  Taking the component as a parameter and discharging
      @{term \<open>di_nxt st = nx\<close>} afterwards sidesteps this.\<close>
lemma dfs_rel_rd_nxt:
  assumes "di_nxt st = nx"
  shows "<dfs_rel fl0 es0 st s> Ref.lookup nx <\<lambda>r. dfs_rel fl0 es0 st s * \<up>(r = ds_nxt s)>"
  using assms unfolding dfs_rel_def by sep_auto

lemma ns_phase_triple2:
  assumes some: "acyc_flow_opt \<noteq> None" and mpos: "0 < marc" and lel: "length el = Suc vcount"
    and e1: "di_fst st = a1" and e2: "di_snd st = a2" and e3: "di_cost st = a3" and e4: "di_cap st = a4"
    and e5: "di_flow st = a5" and e6: "di_pot st = a6" and e7: "di_tree st = a7" and e8: "di_par st = a8"
    and e9: "di_dir st = a9" and e10: "di_es st = a10" and e11: "di_stk st = a11"
  shows "<sarr \<mapsto>\<^sub>a replicate max_candidates 0 * cref \<mapsto>\<^sub>r 0 * lref \<mapsto>\<^sub>r 0 * est \<mapsto>\<^sub>a el *
          dfs_rel acyc_flow (edge_state acyc_flow) st (build_tree acyc_flow) * ofl \<mapsto>\<^sub>a fs0>
         ns_loop_prog vcount m marc block_size min_candidates max_candidates a1 a2 a3 a4
           (ns_impl_state.make a5 a6 a7 a8 a9 a10 (sarr, cref, lref) a11 est)
         <\<lambda>res. \<exists>\<^sub>A fl'. a5 \<mapsto>\<^sub>a fl' * a3 \<mapsto>\<^sub>a cost_list * ofl \<mapsto>\<^sub>a fs0 * true *
           \<up>(marc \<le> length fl' \<and> solve = (if res = Network_Simplex.unbounded then Neg_inf_cycle
              else if list_all (\<lambda>k. fl' ! k = 0) [m..<marc] then Optimum (take m fl') else Infeasible))>"
  using ns_phase_triple'[OF some mpos lel, where st = st and sarr = sarr and cref = cref and lref = lref]
  by (simp only: e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11)

lemma marc_eq: "marc = m + ds_nxt (build_tree acyc_flow)" by (simp add: marc_def Kart_def art_tree_def)
lemma marc_pos: "0 < marc" using num_edges_gtr_0 by (simp add: marc_def)

text \<open>The \<^emph>\<open>else\<close> branch of @{const solve_imp} --- Pass A, the imbalance transform, the tree builder,
      the network-simplex loop and the verdict tail --- as one Hoare triple over the arrays that the
      allocation and acyclifier phases leave behind.  The precondition keeps the acyclifier's
      @{const flow_assn_m} \<^emph>\<open>last\<close>, and the proof immediately weakens it with
      @{thm [source] flow_assn_m_pad}.  @{method sep_auto} always decomposes a goal down to its
      leftmost atomic command, so a block triple is spliced in by re-associating the binds (four
      @{method subst} of @{thm [source] bind_bind}, matching the five commands of
      @{thm [source] passA_phase_triple}) and applying @{thm [source] ht_bind} /
      @{thm [source] wlp_apply_ht} with an explicit frame.\<close>
lemma solve_tail_triple:
  fixes fl_arr cap_arr cost_arr exc_arr ba outfl :: "'n array"
    and fsta snda ob oe oh oc ib ie ih ic pra tha rva lsa sna aua paa sva esta :: "nat array"
    and dira dsta :: "bool array" and es_arr :: "edge_tag array"
  assumes some: "acyc_flow_opt = Some f'"
    and ldl: "length dl = Suc vcount" and lvl: "length vl0 = Suc vcount" and lel: "length el0 = Suc vcount"
    and lfs: "m \<le> length fs0"
  shows "<outI.graph.csr_assn c_o (ob, oe, oh) * incI.graph.csr_assn c_i (ib, ie, ih) *
          oc \<mapsto>\<^sub>a replicate vcount 0 * ic \<mapsto>\<^sub>a replicate vcount 0 *
          cap_arr \<mapsto>\<^sub>a (capacity_list @ replicate n 0) * cost_arr \<mapsto>\<^sub>a cost_list *
          fsta \<mapsto>\<^sub>a (fst_list @ replicate n 0) * snda \<mapsto>\<^sub>a (snd_list @ replicate n 0) *
          sva \<mapsto>\<^sub>a vl0 * esta \<mapsto>\<^sub>a el0 * dsta \<mapsto>\<^sub>a dl * exc_arr \<mapsto>\<^sub>a (0 # replicate vcount 0) *
          dira \<mapsto>\<^sub>a (False # replicate vcount False) * paa \<mapsto>\<^sub>a (0 # replicate vcount 0) *
          aua \<mapsto>\<^sub>a (0 # replicate vcount 0) * sna \<mapsto>\<^sub>a (0 # replicate vcount 0) *
          lsa \<mapsto>\<^sub>a (0 # replicate vcount 0) * rva \<mapsto>\<^sub>a (0 # replicate vcount 0) *
          tha \<mapsto>\<^sub>a (0 # replicate vcount 0) * pra \<mapsto>\<^sub>a (0 # replicate vcount 0) *
          poa \<mapsto>\<^sub>a (pval_zero # replicate vcount pval_zero) * es_arr \<mapsto>\<^sub>a replicate (m + n) InL *
          outfl \<mapsto>\<^sub>a fs0 * ba \<mapsto>\<^sub>a b_arr * flow_assn_m f' fl_arr>
     do { _ \<leftarrow> csr_copy_imp vcount ob oh 0; _ \<leftarrow> csr_copy_imp vcount ib ih 0;
          _ \<leftarrow> passA_imp fl_arr cap_arr fsta snda es_arr exc_arr oe oh ie ih 0 m;
          _ \<leftarrow> imbalance_imp exc_arr ba 0 vcount; _ \<leftarrow> arr_fill_imp dsta False 0 (Suc vcount);
          sp_ref \<leftarrow> ref 0; prev_ref \<leftarrow> ref 0; nxt_ref \<leftarrow> ref 0;
          _ \<leftarrow> build_tree_imp \<lparr>di_seen = dsta, di_tree = \<lparr>prnt_impl = pra, thrd_impl = tha, rvth_impl = rva, lsuc_impl = lsa, snum_impl = sna, aux_impl = aua\<rparr>, di_par = paa, di_dir = dira, di_pot = poa, di_fst = fsta, di_snd = snda, di_cap = cap_arr, di_cost = cost_arr, di_flow = fl_arr, di_es = es_arr, di_ob = ob, di_oe = oe, di_oh = oh, di_oc = oc, di_ib = ib, di_ie = ie, di_ih = ih, di_ic = ic, di_stk = sva, di_sp = sp_ref, di_prev = prev_ref, di_nxt = nxt_ref\<rparr> exc_arr m vcount n;
          Kart \<leftarrow> Ref.lookup nxt_ref;
          sel_arr \<leftarrow> Array.new max_candidates 0; scur \<leftarrow> ref 0; slen \<leftarrow> ref 0;
          res \<leftarrow> ns_loop_prog vcount m (m + Kart) block_size min_candidates max_candidates fsta snda cost_arr cap_arr
                   (ns_impl_state.make fl_arr poa \<lparr>prnt_impl = pra, thrd_impl = tha, rvth_impl = rva, lsuc_impl = lsa, snum_impl = sna, aux_impl = aua\<rparr> paa dira es_arr (sel_arr, scur, slen) sva esta);
          (if res = Network_Simplex.unbounded then return NegInfCycleF
           else do { allz \<leftarrow> scan_art_imp fl_arr m (m + Kart);
                     (if allz then do { _ \<leftarrow> arr_copy_imp fl_arr outfl 0 m; return OptimalF }
                      else return InfeasibleF) }) }
   <\<lambda>r. \<exists>\<^sub>A fs'. outfl \<mapsto>\<^sub>a fs' * cost_arr \<mapsto>\<^sub>a cost_list * ba \<mapsto>\<^sub>a b_arr *
        \<up>(r = status_of solve \<and> length fs' = length fs0 \<and> (\<forall>fs. solve = Optimum fs \<longrightarrow> take m fs' = fs)) * true>"
  apply (rule ht_cons_pre[OF ent_star_mono[OF ent_refl flow_assn_m_pad[OF some]]])
  apply (simp only: ex_assn_move_out)
  apply (rule ht_exEI)
  apply (simp only: mult.assoc[symmetric])
  apply (rule ht_extract_pre_pure(1))
  subgoal premises pre for fla
  proof -
    have mfla: "m \<le> length fla" using pre by simp
    have agfla: "\<forall>e<m. fla ! e = acyc_flow ! e" using pre by simp
    have mnfla: "m + n \<le> length fla" using pre by simp
    note PA = passA_phase_triple[OF some mfla agfla ldl, unfolded bind_bind[symmetric]]
    note DR = dfs_rel_raw_intro[OF mnfla agfla _ lvl, where auxl = "0 # replicate vcount 0", simplified]
    have sne: "acyc_flow_opt \<noteq> None" using some by simp
    show ?thesis
      apply (subst bind_bind[symmetric])
      apply (subst bind_bind[symmetric])
      apply (subst bind_bind[symmetric])
      apply (subst bind_bind[symmetric])
      apply (rule ht_bind[OF ht_cons_pre[OF _ ht_frame[OF PA, where R = "cost_arr \<mapsto>\<^sub>a cost_list * sva \<mapsto>\<^sub>a vl0 * esta \<mapsto>\<^sub>a el0 * oc \<mapsto>\<^sub>a replicate vcount 0 * ic \<mapsto>\<^sub>a replicate vcount 0 * dira \<mapsto>\<^sub>a (False # replicate vcount False) * paa \<mapsto>\<^sub>a (0 # replicate vcount 0) * aua \<mapsto>\<^sub>a (0 # replicate vcount 0) * sna \<mapsto>\<^sub>a (0 # replicate vcount 0) * lsa \<mapsto>\<^sub>a (0 # replicate vcount 0) * rva \<mapsto>\<^sub>a (0 # replicate vcount 0) * tha \<mapsto>\<^sub>a (0 # replicate vcount 0) * pra \<mapsto>\<^sub>a (0 # replicate vcount 0) * poa \<mapsto>\<^sub>a (pval_zero # replicate vcount pval_zero) * outfl \<mapsto>\<^sub>a fs0"]]])
       apply sep_auto
      apply (rule wlp_apply_ht[OF _ _ build_tree_imp_rule, where F = "esta \<mapsto>\<^sub>a el0 * ba \<mapsto>\<^sub>a b_arr * outfl \<mapsto>\<^sub>a fs0 * true"])
        apply assumption
       apply (rule ent_frame_fwdI[OF _ DR, where F = "exc_arr \<mapsto>\<^sub>a imbalance * esta \<mapsto>\<^sub>a el0 * ba \<mapsto>\<^sub>a b_arr * outfl \<mapsto>\<^sub>a fs0 * true"])
        prefer 2
        apply sep_auto
      apply (rule wlp_apply_ht[OF _ _ dfs_rel_rd_nxt, where F = "exc_arr \<mapsto>\<^sub>a imbalance * esta \<mapsto>\<^sub>a el0 * ba \<mapsto>\<^sub>a b_arr * outfl \<mapsto>\<^sub>a fs0 * true"])
         apply assumption
        apply sep_auto
      apply (rule wlp_apply_ht[OF _ _ ns_phase_triple2[OF sne marc_pos lel, unfolded marc_eq, where ofl = outfl], where F = "exc_arr \<mapsto>\<^sub>a imbalance * ba \<mapsto>\<^sub>a b_arr * true"])
        apply assumption
       apply sep_auto
       apply (sep_auto heap: scan_art_imp_rule arr_copy_imp_rule simp: lfs)
      done
  qed
  done

text \<open>\<^emph>\<open>Total correctness of the whole solver.\<close>  @{const solve_imp} --- allocation and padding of the
      input arrays, the two CSR builds, the edged-vertex materialisation, the acyclifier, Pass A, the
      spanning-tree build, the network-simplex loop and the verdict tail --- returns exactly
      @{term \<open>status_of solve\<close>}, and on @{const Optimum} the caller's flow array holds the optimal
      @{term b}-flow in its first @{term m} cells.  The acyclifier splits the proof in two: its
      @{const None} verdict is the infinite-cycle branch, closed outright, and its @{term \<open>Some f'\<close>}
      verdict is the whole rest of the solver, which is @{thm [source] solve_tail_triple}.\<close>
theorem solve_imp_correct:
  "<in_fst \<mapsto>\<^sub>a fst_list * in_snd \<mapsto>\<^sub>a snd_list * in_cap \<mapsto>\<^sub>a capacity_list *
    in_cost \<mapsto>\<^sub>a cost_list * in_flow \<mapsto>\<^sub>a flow_list * in_b \<mapsto>\<^sub>a b_arr>
     solve_imp n m block_size min_candidates max_candidates
               in_fst in_snd in_cap in_cost in_flow in_b
   <\<lambda>r. \<exists>\<^sub>A fs'. in_fst \<mapsto>\<^sub>a fst_list * in_snd \<mapsto>\<^sub>a snd_list * in_cap \<mapsto>\<^sub>a capacity_list *
                in_cost \<mapsto>\<^sub>a cost_list * in_flow \<mapsto>\<^sub>a fs' * in_b \<mapsto>\<^sub>a b_arr *
                \<up>(r = status_of solve \<and> length fs' = m \<and>
                  (\<forall>fs. solve = Optimum fs \<longrightarrow> take m fs' = fs)) * true>"
  unfolding solve_imp_def Let_def
  apply (simp only: vcount_eq[symmetric])
  apply (sep_auto heap: arr_copy_imp_rule
           simp: length_fst_list_m length_snd_list_m length_edges length_flow)
  apply (sep_auto heap: csr_build_out_rule csr_build_in_rule)
  apply (sep_auto heap: csr_copy_out_init csr_copy_in_init)
  apply (sep_auto heap: count_edged_imp_rule fill_edged_imp_rule simp: edged_lst_vs)
  apply (sep_auto heap: make_acyclic_solve_triple)
  subgoal by (sep_auto simp: acyc_flow_opt_def solve_none length_flow length_edges)
  apply (rule wlp_apply_ht[OF _ _ solve_tail_triple,
           where F = "in_fst \<mapsto>\<^sub>a fst_list * in_snd \<mapsto>\<^sub>a snd_list * in_cap \<mapsto>\<^sub>a capacity_list * true"])
   apply assumption
  apply sep_auto
  apply (simp_all add: acyc_flow_opt_def length_flow length_edges)
  apply (rule entailsD[rotated], assumption)
  apply sep_auto
  done

subsection \<open>The specification of @{const solve_imp}, free of the functional implementation\<close>

text \<open>@{thm [source] solve_imp_correct} still mentions the functional @{const solve}.  Composing it with
      @{thm [source] solve_correct} --- the three verdicts of the functional solver, stated against the
      input network @{term original_network} --- removes that reference: what remains is a statement
      relating the imperative program's \<^emph>\<open>returned flag and flow array\<close> directly to the
      minimum-cost-flow problem the input lists describe.

      The composition also has to eliminate the two \<^emph>\<open>derived\<close> balance constants, so that the balances
      in the specification are read off the caller's own @{term b_list}.  @{const b_arr} is the scatter
      of @{term b_list} into a @{term \<open>Suc vcount\<close>}-slot array at the vertex names @{term vs_list} ---
      which, the names being the dense range @{term \<open>[Suc 0..<Suc n]\<close>}, is just @{term b_list} framed by
      the null-sentinel slot and the artificial-root slot.\<close>
lemma b_arr_eq: "b_arr = 0 # b_list @ [0]"
proof -
  have lb: "length b_list = n" by (rule length_b)
  have lvs: "length vs_list = n" by (rule length_vs_list)
  have dz: "distinct (map fst (zip vs_list b_list))"
    using distinct_vs_list_code by (simp add: lvs lb)
  have lenA: "length b_arr = Suc (Suc n)" by (simp add: length_b_arr vcount_eq)
  have zl: "\<And>v x. (v, x) \<in> set (zip vs_list b_list) \<Longrightarrow> v \<in> {Suc 0..n}"
    by (auto simp: set_vs_list[symmetric] dest: set_zip_leftD)
  show ?thesis
  proof (rule nth_equalityI)
    show "length b_arr = length (0 # b_list @ [0])" using lenA lb by simp
  next
    fix i assume "i < length b_arr"
    hence iv: "i < Suc (Suc n)" using lenA by simp
    show "b_arr ! i = (0 # b_list @ [0]) ! i"
    proof (cases i)
      case 0
      have r0: "replicate (Suc vcount) (0::'n) ! 0 = 0" by (simp add: vcount_eq del: replicate_Suc)
      have "b_arr ! 0 = replicate (Suc vcount) (0::'n) ! 0"
        unfolding b_arr_def by (rule foldl_scatter_miss) (use zl in force)
      thus ?thesis using 0 r0 by simp
    next
      case (Suc j)
      show ?thesis
      proof (cases "j < n")
        case True
        note jl = True
        have n1: "zip vs_list b_list ! j = (vs_list ! j, b_list ! j)" using jl lvs lb by simp
        have n2: "j < length (zip vs_list b_list)" using jl lvs lb by simp
        have nvs: "vs_list ! j = Suc j" using jl by (simp add: vs_list_def del: upt_Suc)
        have mem: "(Suc j, b_list ! j) \<in> set (zip vs_list b_list)"
          using nth_mem[OF n2] n1 nvs by simp
        have lt: "Suc j < length (replicate (Suc vcount) (0::'n))" using jl by (simp add: vcount_eq)
        have "b_arr ! (Suc j) = b_list ! j"
          unfolding b_arr_def by (rule foldl_scatter_hit[OF dz mem lt])
        thus ?thesis using Suc jl lb by (simp add: nth_append)
      next
        case False
        hence jn: "j = n" using iv Suc by simp
        have r0: "replicate (Suc vcount) (0::'n) ! (Suc n) = 0"
          by (simp add: vcount_eq del: replicate_Suc)
        have "b_arr ! (Suc n) = replicate (Suc vcount) (0::'n) ! (Suc n)"
          unfolding b_arr_def by (rule foldl_scatter_miss) (use zl in force)
        hence z: "b_arr ! (Suc n) = 0" using r0 by simp
        thus ?thesis using Suc jn lb by (simp add: nth_append)
      qed
    qed
  qed
qed

text \<open>Hence, at every vertex of the input network --- the vertices are edge endpoints, so they lie in
      @{term \<open>{Suc 0..n}\<close>} --- the balance @{const b_lookup} reads is the entry of @{term \<open>0 # b_list\<close>}
      at that vertex \<^emph>\<open>name\<close>.  This is the functional mirror of what the code does: the caller passes
      the array @{term \<open>0 # b_list @ [0]\<close>} and the program indexes it by the vertex name, slot
      @{term \<open>0::nat\<close>} being the null sentinel and slot @{term \<open>Suc n\<close>} the artificial root.  (The
      input list @{term b_list} is itself indexed from @{term \<open>0::nat\<close>}, its entry @{term i} being the
      balance of vertex @{term \<open>Suc i\<close>} --- the convention @{thm [source] isolated_zero} already uses;
      prefixing the sentinel slot absorbs that shift.)  The balance function only ever occurs applied
      to vertices --- \<open>isbflow\<close> constrains it on @{term \<open>original_network.\<V>\<close>} alone --- so the two agree
      wherever it matters and may be exchanged inside \<open>isbflow\<close> and \<open>is_Opt\<close>.\<close>
lemma b_lookup_V:
  assumes "v \<in> original_network.\<V>" shows "b_lookup v = (0 # b_list) ! v"
proof -
  have "v \<in> set vs_list" using assms V_sub_vs_list by blast
  hence v: "v \<le> n" by (auto simp: set_vs_list)
  have lb: "length b_list = n" by (rule length_b)
  have key: "(0 # b_list @ [0]) ! v = (0 # b_list) ! v"
  proof (cases v)
    case 0 thus ?thesis by simp
  next
    case (Suc k)
    hence kn: "k < n" using v by simp
    thus ?thesis using Suc lb by (simp add: nth_append)
  qed
  show ?thesis by (simp add: b_lookup_def b_arr_eq key)
qed

lemma isbflow_cong_b:
  "original_network.isbflow f (\<lambda>v. h (b_lookup v))
   = original_network.isbflow f (\<lambda>v. h ((0 # b_list) ! v))"
  by (auto simp: original_network.isbflow_def b_lookup_V)

lemma is_Opt_cong_b:
  "original_network.is_Opt (\<lambda>v. h (b_lookup v)) f
   = original_network.is_Opt (\<lambda>v. h ((0 # b_list) ! v)) f"
  by (auto simp: original_network.is_Opt_def original_network.isbflow_def b_lookup_V)

text \<open>The pure part of the composition.\<close>
lemma solve_verdict_transfer:
  assumes r: "r = status_of solve" and len: "length fs' = m"
      and tk: "\<forall>fs. solve = Optimum fs \<longrightarrow> take m fs' = fs"
  shows "(case r of
            OptimalF \<Rightarrow> original_network.is_Opt (\<lambda>v. h ((0 # b_list) ! v)) (h \<circ> nth fs')
          | InfeasibleF \<Rightarrow> \<nexists>f. original_network.isbflow f (\<lambda>v. h ((0 # b_list) ! v))
          | NegInfCycleF \<Rightarrow> neg_infty_cycle)"
proof (cases solve)
  case (Optimum fs)
  have e: "fs' = fs" using tk Optimum len by (simp add: take_all)
  show ?thesis using r Optimum e solve_correct(1)[OF Optimum] is_Opt_cong_b by simp
next
  case Infeasible
  thus ?thesis using r solve_correct(2) isbflow_cong_b by simp
next
  case Neg_inf_cycle
  thus ?thesis using r solve_correct(3) by simp
qed

text \<open>Monotonicity of the pure assertion.  The final entailment must \<^emph>\<open>not\<close> be left to
      @{method sep_auto}: its @{method clarsimp} would orient the conjunct @{term \<open>length fs' = m\<close>} the
      wrong way and substitute the locale parameter @{term m} away, unfolding every locale
      abbreviation --- @{const solve} would become \<open>initial_basis_code_spec.solve capacity_list \<dots>
      (length fs') \<dots>\<close> --- and leaving an unprovable goal.  Splitting the entailment with
      @{thm [source] ent_star_mono} keeps the equation out of the simplifier's hands.\<close>
lemma ent_pure_mono: "(P \<Longrightarrow> Q) \<Longrightarrow> \<up>P \<Longrightarrow>\<^sub>A \<up>Q"
  by (cases P) (auto simp: entails_def)

text \<open>\<^emph>\<open>The specification of the imperative solver.\<close>  The caller supplies the six input arrays --- the
      balance array being @{term b_list} framed by the sentinel and root slots --- and gets back a flow
      array of exactly @{term m} entries: on @{const OptimalF} a minimum-cost @{term b}-flow of the
      input network, on @{const InfeasibleF} the information that no @{term b}-flow exists at all, and
      on @{const NegInfCycleF} that the network has a negative cycle of infinite capacity, so no
      minimum exists.  The five read-only input arrays come back unchanged.  Apart from
      @{const solve_imp} itself, nothing in this statement refers to the implementation: the balances
      are read directly off the caller's @{term b_list}.\<close>
corollary solve_imp_spec:
  "<in_fst \<mapsto>\<^sub>a fst_list * in_snd \<mapsto>\<^sub>a snd_list * in_cap \<mapsto>\<^sub>a capacity_list *
    in_cost \<mapsto>\<^sub>a cost_list * in_flow \<mapsto>\<^sub>a flow_list * in_b \<mapsto>\<^sub>a (0 # b_list @ [0])>
     solve_imp n m block_size min_candidates max_candidates
               in_fst in_snd in_cap in_cost in_flow in_b
   <\<lambda>r. \<exists>\<^sub>A fs'. in_fst \<mapsto>\<^sub>a fst_list * in_snd \<mapsto>\<^sub>a snd_list * in_cap \<mapsto>\<^sub>a capacity_list *
                in_cost \<mapsto>\<^sub>a cost_list * in_flow \<mapsto>\<^sub>a fs' * in_b \<mapsto>\<^sub>a (0 # b_list @ [0]) *
                \<up>(length fs' = m \<and>
                  (case r of
                     OptimalF \<Rightarrow> original_network.is_Opt (\<lambda>v. h ((0 # b_list) ! v)) (h \<circ> nth fs')
                   | InfeasibleF \<Rightarrow> \<nexists>f. original_network.isbflow f (\<lambda>v. h ((0 # b_list) ! v))
                   | NegInfCycleF \<Rightarrow> neg_infty_cycle)) * true>"
  apply (simp only: b_arr_eq[symmetric])
  apply (rule ht_cons_post_prec[OF solve_imp_correct])
  apply (rule ent_ex_preI)
  apply (rule ent_ex_postI)
  apply (rule ent_star_mono[OF ent_star_mono[OF ent_refl ent_pure_mono] ent_refl])
  apply (elim conjE)
  apply (rule conjI)
   apply assumption
  apply (rule solve_verdict_transfer; assumption)
  done

end


section \<open>A worked example: 10 vertices, 40 edges\<close>

text \<open>A random well-formed min-cost-flow instance meeting the locale conditions: vertices @{term \<open>1::nat\<close>}
      {\isasymdots} @{term \<open>10::nat\<close>} (name @{term \<open>0::nat\<close>} is the reserved null sentinel), 40 directed edges whose
      first ten form a Hamiltonian cycle so \<^emph>\<open>every vertex is incident to an edge\<close> (no lonely vertex)
      and the graph is connected; capacities / costs in \<open>[1, 50]\<close>; the initial flow is random but
      \<^emph>\<open>capacity-complying\<close> (\<open>0 \<le> f \<le> cap\<close>); and the balances (index @{term \<open>1::nat\<close>}{\isasymdots}@{term \<open>10::nat\<close>},
      with the sentinel and root slots @{term 0}) lie in \<open>[-50, 50]\<close> and \<^emph>\<open>sum to zero\<close> (flow
      conservation).  The selector is tuned with block size @{term \<open>10::nat\<close>}, min / max candidates
      @{term \<open>4::nat\<close>} / @{term \<open>16::nat\<close>}.  The optimum @{term b}-flow, if one exists, is written back
      into the first @{term \<open>40::nat\<close>} cells of the input flow array, which we freeze and return
      alongside the status flag.\<close>

definition solve_sample :: "(solve_status \<times> int list) Heap" where
  "solve_sample = do {
     in_fst  \<leftarrow> Array.of_list
       [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 10, 6, 7, 10, 8, 7, 10, 3, 1,
        9, 6, 8, 5, 8, 4, 4, 8, 1, 7, 7, 7, 7, 4, 4, 8, 4, 1, 9, 6 :: nat];
     in_snd  \<leftarrow> Array.of_list
       [2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 2, 10, 2, 8, 9, 4, 8, 8, 2,
        8, 7, 9, 4, 1, 9, 9, 7, 9, 2, 5, 1, 6, 10, 5, 9, 10, 5, 5, 5 :: nat];
     in_cap  \<leftarrow> Array.of_list
       [42, 24, 40, 5, 36, 29, 29, 32, 46, 24, 13, 50, 17, 13, 45, 4, 9, 39, 30, 18,
        28, 21, 50, 16, 10, 25, 48, 32, 26, 37, 24, 1, 33, 2, 34, 50, 33, 45, 48, 39 :: int];
     in_cost \<leftarrow> Array.of_list
       [47, 6, 33, 4, 13, 19, 37, 20, 39, 43, 22, 16, 24, 33, 32, 11, 28, 49, 2, 47,
        15, 22, 1, 25, 25, 28, 3, 6, 7, 47, 39, 40, 8, 41, 50, 42, 7, 20, 20, 10 :: int];
     in_flow \<leftarrow> Array.of_list
       [10, 8, 16, 5, 23, 15, 16, 16, 32, 4, 2, 8, 2, 10, 35, 2, 3, 37, 4, 9,
        0, 10, 31, 1, 2, 22, 12, 25, 6, 37, 8, 1, 32, 2, 21, 15, 29, 13, 31, 10 :: int];
     in_b    \<leftarrow> Array.of_list
       [0, 10, (- 6), (- 24), (- 16), 21, (- 14), 7, 8, 17, (- 3), 0 :: int];
     status \<leftarrow> solve_imp 10 40 10 4 16 in_fst in_snd in_cap in_cost in_flow in_b;
     f \<leftarrow> Array.freeze in_flow;
     return (status, f) }"

text \<open>The instance is kept as a sanity check on the shape of the interface; it is not run here, so
      loading this theory stays free of code compilation.  The solver that is actually generated is
      \<open>dimacs_solve_prog\<close> of \<open>DIMACS_Solver\<close>, whose exported SML sits next to it.\<close>

end
