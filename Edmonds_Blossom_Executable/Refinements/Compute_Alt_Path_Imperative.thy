theory Compute_Alt_Path_Imperative
  imports
    Alternating_Forest_Specs_Imp
    Blossom_Matching_Specs_Imp
    Blossom_Executable.Compute_Alt_Path
    Data_Structures.Bounded_Stack_Specs_Imp
    Data_Structures.Fixed_Univ_Set_Specs_Imp
    Imperative.Array_Folds
begin

provenance ai

section \<open>Imperative refinement of the alternating forest search\<close>

text \<open>The imperative program mirrors @{const Compute_Alt_Path.Compute_Alt_Path_impl}. The queue
  of even vertices whose neighbours remain to be scanned is an imperative bounded stack
  (@{locale bounded_stack_imp}): the functional search pushes and pops at the head of the queue.
  The list of unscanned edges, which all start at the vertex being scanned, is represented by that
  vertex, an array of its neighbours, and the position of the next neighbour to scan. The forest
  is an imperative alternating forest (@{locale alternating_forest_imp}), the matching an
  imperative matching (@{locale blossom_matching_imp}), and the roots are collected in an
  imperative set (@{locale fixed_univ_set_imp}). The neighbours of a vertex are read off the graph
  by an operation that returns them in an array. All operations are parameters; their Hoare
  triples, stated against the functional operations, are the assumptions of the refinement
  locale.\<close>

record \<^marker>\<open>provenance ai_human\<close> ('si, 'v, 'fi) Compute_Alt_Path_state_imp =
  i_queue :: 'si
  i_cur :: 'v
  i_nbs :: "'v array"
  i_pos :: nat
  i_len :: nat
  i_forest :: 'fi

locale \<^marker>\<open>provenance ai_human\<close> Compute_Alt_Path_Imperative_spec =
  fixes stack_empty_imp :: "'si Heap"
    and stack_push_imp :: "'si \<Rightarrow> 'v::heap \<Rightarrow> unit Heap"
    and stack_pop_imp :: "'si \<Rightarrow> unit Heap"
    and stack_top_imp :: "'si \<Rightarrow> 'v Heap"
    and stack_is_empty_imp :: "'si \<Rightarrow> bool Heap"
    and fset_empty_imp :: "'fseti Heap"
    and fset_insert_imp :: "'v \<Rightarrow> 'fseti \<Rightarrow> unit Heap"
    and empty_forest_imp :: "'fseti \<Rightarrow> 'fi Heap"
    and evens_isin_imp :: "'fi \<Rightarrow> 'v \<Rightarrow> bool Heap"
    and odds_isin_imp :: "'fi \<Rightarrow> 'v \<Rightarrow> bool Heap"
    and extend_forest_even_unclassified_imp :: "'fi \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and get_path_imp :: "'fi \<Rightarrow> 'v \<Rightarrow> 'pathi Heap"
    and lookup_partner_imp :: "'mi \<Rightarrow> 'v \<Rightarrow> 'v option Heap"
    and neighbours_imp :: "'gi \<Rightarrow> 'v \<Rightarrow> 'v array Heap"
begin

subsection \<open>The loop\<close>

partial_function \<^marker>\<open>provenance ai_human\<close> (heap) Compute_Alt_Path_imp ::
  "'gi \<Rightarrow> 'mi \<Rightarrow> ('si, 'v, 'fi) Compute_Alt_Path_state_imp \<Rightarrow>
   ('si, 'v, 'fi) Compute_Alt_Path_state_imp Heap" where
  "Compute_Alt_Path_imp Gi Mi s =
     (if i_pos s < i_len s then
            do { w \<leftarrow> Array.nth (i_nbs s) (i_pos s);
                 we \<leftarrow> evens_isin_imp (i_forest s) w;
                 if we then return s
                 else
                   do { wo \<leftarrow> odds_isin_imp (i_forest s) w;
                        if wo then Compute_Alt_Path_imp Gi Mi (s\<lparr>i_pos := Suc (i_pos s)\<rparr>)
                        else
                          do { mx \<leftarrow> lookup_partner_imp Mi w;
                               case mx of
                                 Some x \<Rightarrow>
                                   do { stack_push_imp (i_queue s) x;
                                        extend_forest_even_unclassified_imp (i_forest s) (i_cur s) w x;
                                        Compute_Alt_Path_imp Gi Mi (s\<lparr>i_pos := Suc (i_pos s)\<rparr>) }
                               | None \<Rightarrow> Compute_Alt_Path_imp Gi Mi (s\<lparr>i_pos := Suc (i_pos s)\<rparr>) } } }
          else
            do { e \<leftarrow> stack_is_empty_imp (i_queue s);
                 if e then return s
                 else
                   do { v \<leftarrow> stack_top_imp (i_queue s);
                        stack_pop_imp (i_queue s);
                        A \<leftarrow> neighbours_imp Gi v;
                        l \<leftarrow> Array.len A;
                        Compute_Alt_Path_imp Gi Mi
                          (s\<lparr>i_cur := v, i_nbs := A, i_pos := 0, i_len := l\<rparr>) } })"

subsection \<open>Initialisation and result\<close>

text \<open>A vertex is a root if it has a neighbour and is unmatched.\<close>

definition \<^marker>\<open>provenance ai_human\<close> "is_free_imp Gi Mi v =
  do { A \<leftarrow> neighbours_imp Gi v;
       l \<leftarrow> Array.len A;
       m \<leftarrow> lookup_partner_imp Mi v;
       return (l \<noteq> 0 \<and> m = None) }"

definition \<^marker>\<open>provenance ai_human\<close> "insert_if_free_imp Gi Mi v Ri =
  do { b \<leftarrow> is_free_imp Gi Mi v;
       if b then do { fset_insert_imp v Ri; return Ri } else return Ri }"

definition \<^marker>\<open>provenance ai_human\<close> "push_if_free_imp Gi Mi v Si =
  do { b \<leftarrow> is_free_imp Gi Mi v;
       if b then do { stack_push_imp Si v; return Si } else return Si }"

text \<open>The roots are inserted from the left and the queue is pushed from the right, so that they
  are the set and the list of the functional search.\<close>

definition \<^marker>\<open>provenance ai_human\<close> "initial_state_imp Gi Mi Vi =
  do { n \<leftarrow> Array.len Vi;
       Ri \<leftarrow> fset_empty_imp;
       Ri \<leftarrow> array_foldl Vi 0 n (insert_if_free_imp Gi Mi) Ri;
       Si \<leftarrow> stack_empty_imp;
       Si \<leftarrow> array_foldr Vi n (push_if_free_imp Gi Mi) Si;
       Fi \<leftarrow> empty_forest_imp Ri;
       A \<leftarrow> Array.of_list [];
       return \<lparr>i_queue = Si, i_cur = undefined, i_nbs = A, i_pos = 0, i_len = 0, i_forest = Fi\<rparr> }"

definition \<^marker>\<open>provenance ai_human\<close> "alternating_paths_imp s =
  (if i_pos s < i_len s then
     do { w \<leftarrow> Array.nth (i_nbs s) (i_pos s);
          P1 \<leftarrow> get_path_imp (i_forest s) (i_cur s);
          P2 \<leftarrow> get_path_imp (i_forest s) w;
          return (Some (P1, P2)) }
   else return None)"

definition \<^marker>\<open>provenance ai_human\<close> "Compute_Alt_Path_run_imp Gi Mi Vi =
  do { s \<leftarrow> initial_state_imp Gi Mi Vi;
       s' \<leftarrow> Compute_Alt_Path_imp Gi Mi s;
       alternating_paths_imp s' }"

end

section \<open>Correctness of the imperative search\<close>

locale \<^marker>\<open>provenance ai_human\<close> Compute_Alt_Path_Imperative =
  Compute_Alt_Path where lookup = lookup and mate_empty = mate_empty +
  Compute_Alt_Path_Imperative_spec where stack_push_imp = stack_push_imp
    and fset_insert_imp = fset_insert_imp and get_path_imp = get_path_imp
    and lookup_partner_imp = lookup_partner_imp and neighbours_imp = neighbours_imp +
  stk: bounded_stack_imp where stack_abstract = stack_abstract
    and stack_push_imp = stack_push_imp +
  fs: fixed_univ_set_imp where U = K and fixed_univ_set_invar = fset_invar
    and fixed_univ_set_abstract = fset_to_set and fixed_univ_set_empty = fset_empty
    and fixed_univ_set_insert = fset_insert and fixed_univ_set_delete = fset_delete
    and fixed_univ_set_isin = fset_isin and fixed_univ_set_assn = fset_assn
    and fixed_univ_set_empty_imp = fset_empty_imp and fixed_univ_set_insert_imp = fset_insert_imp +
  fr: alternating_forest_imp where evens = evens and odds = odds and roots = roots
    and get_path = get_path and abstract_forest = abstract_forest and forest_invar = forest_invar
    and vset_invar = fset_invar and vset_to_set = fset_to_set
    and extend_forest_even_unclassified = extend_forest_even_unclassified
    and empty_forest = empty_forest and forest_univ = K and vset_empty = fset_empty
    and vset_assn = fset_assn and get_path_imp = get_path_imp +
  mt: blossom_matching_imp where K = K and empty_matching = mate_empty
    and matching_invar = matching_invar_abs and lookup_partner = mate_lookup
    and get_partner = mate_partner and augment = mate_augment and matching_abstract = matching_abs
    and contract_path = mate_contract and expand_path_at_matched = mate_expand
    and add_alternatingly = mate_add_alternatingly and lookup_partner_imp = lookup_partner_imp
  for lookup :: "'adjmap \<Rightarrow> 'v::heap \<Rightarrow> 'vset option"
    and mate_empty :: 'mate
    and stack_push_imp :: "'si \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and stack_abstract :: "'s \<Rightarrow> 'v list"
    and fset_insert_imp :: "'v \<Rightarrow> 'fseti \<Rightarrow> unit Heap"
    and fset_assn
    and get_path_imp :: "'fi \<Rightarrow> 'v \<Rightarrow> 'pathi Heap"
    and lookup_partner_imp :: "'mi \<Rightarrow> 'v \<Rightarrow> 'v option Heap"
    and neighbours_imp :: "'gi \<Rightarrow> 'v \<Rightarrow> 'v array Heap" +
  fixes graph_assn :: "'adjmap \<Rightarrow> 'gi \<Rightarrow> assn"
  assumes neighbours_rule[sep_heap_rules]:
      "\<And>H Gi v. \<lbrakk>Graph.graph_inv H; v \<in> K\<rbrakk> \<Longrightarrow>
       <graph_assn H Gi> neighbours_imp Gi v
       <\<lambda>A. graph_assn H Gi * A \<mapsto>\<^sub>a neighbour_list H v>"
    and Compute_Alt_Path_axiom: Compute_Alt_Path_axiom
    and capacity: "2 * length vs \<le> cap"
begin

lemma graph_input_G': "graph_input G vs"
  and matching_invar_M': "matching_invar G M"
  using graph_input_G[OF Compute_Alt_Path_axiom] matching_invar_M[OF Compute_Alt_Path_axiom] .

lemma vs_in_univ: "set vs \<subseteq> K"
  by (rule graph_inputD(7)[OF graph_input_G'])

lemma graph_inv_G: "Graph.graph_inv G"
  by (rule graph_inputD(1)[OF graph_input_G'])

lemma matching_invar_abs_M: "matching_invar_abs (ugraph_abs G) M"
  using matching_invar_M' by (simp add: matching_invar_def)

lemma Vs_G_in_univ: "Vs (ugraph_abs G) \<subseteq> K"
  using Vs_G_subset_vs[OF Compute_Alt_Path_axiom] vs_in_univ by blast

lemma card_Vs_G: "card (Vs (ugraph_abs G)) \<le> length vs"
  using card_mono[OF List.finite_set Vs_G_subset_vs[OF Compute_Alt_Path_axiom]] card_length[of vs]
  by linarith

subsection \<open>The queue\<close>

definition "queue_assn xs Si =
  (\<exists>\<^sub>A S. stack_assn S Si * \<up>(stack_invar S \<and> stack_abstract S = xs))"

lemma queue_empty_rule:
  "<emp> stack_empty_imp <queue_assn []>"
  unfolding queue_assn_def
  by (sep_auto heap: stk.stack_empty_rule simp: stk.stack_empty)

lemma queue_push_rule:
  "length xs < cap \<Longrightarrow> <queue_assn xs Si> stack_push_imp Si x <\<lambda>_. queue_assn (x # xs) Si>"
  unfolding queue_assn_def
  by (sep_auto heap: stk.stack_push_rule simp: stk.stack_push)

lemma queue_pop_rule:
  "xs \<noteq> [] \<Longrightarrow> <queue_assn xs Si> stack_pop_imp Si <\<lambda>_. queue_assn (tl xs) Si>"
  unfolding queue_assn_def
  by (sep_auto heap: stk.stack_pop_rule simp: stk.stack_pop)

lemma queue_top_rule:
  "xs \<noteq> [] \<Longrightarrow> <queue_assn xs Si> stack_top_imp Si <\<lambda>r. queue_assn xs Si * \<up>(r = hd xs)>"
  unfolding queue_assn_def
  by (sep_auto heap: stk.stack_top_rule simp: stk.stack_top)

lemma queue_is_empty_rule:
  "<queue_assn xs Si> stack_is_empty_imp Si <\<lambda>r. queue_assn xs Si * \<up>(r \<longleftrightarrow> xs = [])>"
  unfolding queue_assn_def
  by (sep_auto heap: stk.stack_is_empty_rule simp: stk.stack_is_empty)

subsection \<open>The length of the queue\<close>

text \<open>The queue is a bounded stack, so pushing requires the queue to be shorter than the capacity.
  Every vertex pushed after the initialisation becomes even, and it is not a root. Hence the queue
  is never longer than the free vertices together with the even vertices that are not roots, which
  are fewer than the vertices of the graph.\<close>

definition "invar_queue_length state \<longleftrightarrow>
  length (queue state) \<le> length free_vertices + card (aevens state - aroots state)"

lemma invar_queue_length_initial: "invar_queue_length initial_state"
  by (simp add: invar_queue_length_def initial_state_def Forest.empty_forest(1,3))

lemma invar_queue_length_upd1:
  assumes "Compute_Alt_Path_call_1_conds state" "invar_forest state" "invar_unscanned state"
    "invar_queue_length state"
  shows "invar_queue_length (Compute_Alt_Path_upd1 state)"
proof-
  obtain v w rest x where c: "unscanned state = (v, w) # rest" "mate_lookup M w = Some x"
    "Forest.forest_extension_precond (search_forest state) (matching_abs M) v w x"
    by (rule call_1_facts[OF Compute_Alt_Path_axiom assms(1-3)])
  have inv: "forest_invar (matching_abs M) (search_forest state)"
    by (rule invar_forestD(1)[OF assms(2)])
  have x: "x \<notin> aevens state"
    using c(3) by (auto simp: Forest.forest_extension_precond_def)
  have "aroots state \<subseteq> aevens state"
    by (rule Forest.roots(2)[OF inv])
  hence "aevens (Compute_Alt_Path_upd1 state) - aroots (Compute_Alt_Path_upd1 state) =
      Set.insert x (aevens state - aroots state)"
    using x by (auto simp: upd1_fields[OF Compute_Alt_Path_axiom c(1,2)] Forest.forest_extend(3,5)[OF c(3)])
  moreover have "finite (aevens state - aroots state)"
    using Forest.finite_forest_basis(1)[OF inv] by blast
  ultimately show ?thesis
    using assms(4) x
    by (simp add: invar_queue_length_def upd1_fields[OF Compute_Alt_Path_axiom c(1,2)])
qed

lemma invar_queue_length_upd2:
  "invar_queue_length state \<Longrightarrow> invar_queue_length (Compute_Alt_Path_upd2 state)"
  by (simp add: invar_queue_length_def Compute_Alt_Path_upd2_def)

lemma invar_queue_length_upd3:
  "\<lbrakk>Compute_Alt_Path_call_3_conds state; invar_queue_length state\<rbrakk>
   \<Longrightarrow> invar_queue_length (Compute_Alt_Path_upd3 state)"
  by (auto simp: invar_queue_length_def Compute_Alt_Path_upd3_def
      Compute_Alt_Path_call_3_conds_def)

lemma queue_length_less_cap:
  assumes "Compute_Alt_Path_call_1_conds state" "invar_forest state" "invar_unscanned state"
    "invar_queue_length state"
  shows "length (queue state) < cap"
proof-
  obtain v w rest x where c: "unscanned state = (v, w) # rest" "mate_lookup M w = Some x"
    "{w, x} \<in> matching_abs M"
    "Forest.forest_extension_precond (search_forest state) (matching_abs M) v w x"
    by (rule call_1_facts[OF Compute_Alt_Path_axiom assms(1-3)])
  have x: "x \<notin> aevens state"
    using c(4) by (auto simp: Forest.forest_extension_precond_def)
  have "x \<in> Vs (ugraph_abs G)"
    using c(3) matching_invar_props(3)[OF matching_invar_M'] by (auto dest: edges_are_Vs_2)
  hence "Set.insert x (aevens state - aroots state) \<subseteq> Vs (ugraph_abs G)"
    using aevens_subset_Vs[OF assms(2)] by blast
  hence "card (Set.insert x (aevens state - aroots state)) \<le> card (Vs (ugraph_abs G))"
    by (rule card_mono[OF finite_Vs_G[OF Compute_Alt_Path_axiom]])
  moreover have "finite (aevens state - aroots state)"
    using Forest.finite_forest_basis(1)[OF invar_forestD(1)[OF assms(2)]] by blast
  ultimately have "card (aevens state - aroots state) < length vs"
    using x card_Vs_G by simp
  moreover have "length free_vertices \<le> length vs"
    by (simp add: free_vertices_def)
  ultimately show ?thesis
    using assms(4) capacity by (simp add: invar_queue_length_def)
qed

subsection \<open>The loop\<close>

text \<open>The invariants hold in every state that the search reaches from the initial state, except
  when there are no free vertices: then the search stops at once, with empty work lists.\<close>

definition "invars state \<longleftrightarrow>
  invar_forest state \<and> invar_unscanned state \<and> invar_queue state \<and> invar_scanned state \<and>
  invar_queue_length state"

definition "pre_assn s si nbs =
  queue_assn (queue s) (i_queue si) * i_nbs si \<mapsto>\<^sub>a nbs *
  forest_assn (search_forest s) (i_forest si) *
  \<up>(i_len si = length nbs \<and> unscanned s = map (Pair (i_cur si)) (drop (i_pos si) nbs) \<and>
    (invars s \<or> (unscanned s = [] \<and> queue s = [])))"

definition "state_assn s si = (\<exists>\<^sub>A nbs. pre_assn s si nbs)"

lemma unscanned_ConsD:
  assumes "unscanned s = map (Pair (i_cur si)) (drop (i_pos si) nbs)"
    "unscanned s = (v, w) # rest"
  shows "i_pos si < length nbs" "nbs ! i_pos si = w" "i_cur si = v"
    "rest = map (Pair (i_cur si)) (drop (Suc (i_pos si)) nbs)"
proof-
  show lt: "i_pos si < length nbs"
    using assms by (cases "i_pos si < length nbs") auto
  have "map (Pair (i_cur si)) (drop (i_pos si) nbs) =
      (i_cur si, nbs ! i_pos si) # map (Pair (i_cur si)) (drop (Suc (i_pos si)) nbs)"
    using lt by (simp add: Cons_nth_drop_Suc[symmetric])
  thus "nbs ! i_pos si = w" "i_cur si = v"
    "rest = map (Pair (i_cur si)) (drop (Suc (i_pos si)) nbs)"
    using assms by auto
qed

lemma unscanned_NilD:
  "\<lbrakk>unscanned s = map (Pair (i_cur si)) (drop (i_pos si) nbs); unscanned s = []\<rbrakk>
   \<Longrightarrow> \<not> i_pos si < length nbs"
  by auto

lemma \<^marker>\<open>provenance ai_human\<close> Compute_Alt_Path_imp_refine:
  "<graph_assn G Gi * matching_assn M Mi * pre_assn s si nbs> Compute_Alt_Path_imp Gi Mi si
   <\<lambda>si'. graph_assn G Gi * matching_assn M Mi * state_assn (Compute_Alt_Path_impl s) si'>"
proof \<^marker>\<open>provenance ai\<close> (induction arbitrary: s si nbs rule: Compute_Alt_Path_imp.fixp_induct)
  case 1
  then show ?case
    by auto
next
  case 2
  then show ?case
    by simp
next
  case (3 f s si nbs)
  show ?case
    unfolding pre_assn_def[of s si nbs] mult.assoc[symmetric]
  proof(rule ht_extract_pre_pure(1), goal_cases)
    case 1
    hence L: "i_len si = length nbs"
      and U: "unscanned s = map (Pair (i_cur si)) (drop (i_pos si) nbs)"
      and I: "invars s \<or> (unscanned s = [] \<and> queue s = [])"
      by blast+
    show ?case
    proof(cases "unscanned s")
      case (Cons e rest)
      obtain v w where e: "e = (v, w)"
        by (cases e)
      note Cons = Cons[unfolded e]
      note pos = unscanned_ConsD[OF U Cons]
      have lt: "i_pos si < i_len si"
        using pos(1) L by simp
      have invs: "invar_forest s" "invar_unscanned s" "invar_queue s" "invar_scanned s"
        "invar_queue_length s"
        using I Cons by (auto simp: invars_def)
      have inv: "forest_invar (matching_abs M) (search_forest s)"
        by (rule invar_forestD(1)[OF invs(1)])
      have edge: "{v, w} \<in> ugraph_abs G"
        using invs(2) Cons by (auto simp: invar_unscanned_def)
      hence vK: "v \<in> K" and wK: "w \<in> K"
        using Vs_G_in_univ by (auto dest: edges_are_Vs edges_are_Vs_2)
      text \<open>The program refers to @{term w} and @{term v} as the entry of the array of neighbours
        and as the vertex being scanned.\<close>
      note wv = pos(2,3)[symmetric]
      note EV = fr.evens_isin_rule[OF inv wK, of "i_forest si", unfolded wv]
      note OD = fr.odds_isin_rule[OF inv wK, of "i_forest si", unfolded wv]
      note LK = mt.lookup_partner_rule[OF matching_invar_abs_M wK, of Mi, unfolded wv]
      note isin = forest_isin[OF invs(1)]
      show ?thesis
      proof(cases "w \<in> aevens s")
        case True
        have F: "Compute_Alt_Path_impl s = s"
          by (subst Compute_Alt_Path_impl.simps) (simp add: Cons isin True)
        show ?thesis
          using lt pos(1) True[unfolded wv] L U I
          by (sep_auto heap: EV simp: F state_assn_def pre_assn_def)
      next
        case not_even: False
        show ?thesis
        proof(cases "w \<in> aodds s")
          case True
          define s' where "s' = s\<lparr>unscanned := rest\<rparr>"
          have call: "Compute_Alt_Path_call_2_conds s"
            using Cons not_even True by (simp add: Compute_Alt_Path_call_2_conds_def isin)
          have upd: "Compute_Alt_Path_upd2 s = s'"
            by (simp add: Compute_Alt_Path_upd2_def s'_def Cons)
          have invs': "invars s'"
            using invars_holds_2[OF Compute_Alt_Path_axiom call invs(1-4)]
              invar_queue_length_upd2[OF invs(5)]
            by (simp add: invars_def upd)
          have F: "Compute_Alt_Path_impl s = Compute_Alt_Path_impl s'"
            by (subst Compute_Alt_Path_impl.simps) (simp add: Cons isin not_even True s'_def)
          have IH: "<graph_assn G Gi * matching_assn M Mi * queue_assn (queue s) (i_queue si) *
                     i_nbs si \<mapsto>\<^sub>a nbs * forest_assn (search_forest s) (i_forest si)>
                      f Gi Mi (si\<lparr>i_pos := Suc (i_pos si)\<rparr>)
                    <\<lambda>si'. graph_assn G Gi * matching_assn M Mi *
                           state_assn (Compute_Alt_Path_impl s) si'>"
            using 3[of s' "si\<lparr>i_pos := Suc (i_pos si)\<rparr>" nbs] pos(4) L invs'
            unfolding F by (simp add: pre_assn_def s'_def mult.assoc)
          show ?thesis
            using lt pos(1) not_even[unfolded wv] True[unfolded wv]
            by (sep_auto heap: EV OD IH)
        next
          case not_odd: False
          show ?thesis
          proof(cases "mate_lookup M w")
            case None
            define s' where "s' = s\<lparr>unscanned := rest\<rparr>"
            have call: "Compute_Alt_Path_call_2_conds s"
              using Cons not_even None by (simp add: Compute_Alt_Path_call_2_conds_def isin)
            have upd: "Compute_Alt_Path_upd2 s = s'"
              by (simp add: Compute_Alt_Path_upd2_def s'_def Cons)
            have invs': "invars s'"
              using invars_holds_2[OF Compute_Alt_Path_axiom call invs(1-4)]
                invar_queue_length_upd2[OF invs(5)]
              by (simp add: invars_def upd)
            have F: "Compute_Alt_Path_impl s = Compute_Alt_Path_impl s'"
              by (subst Compute_Alt_Path_impl.simps)
                 (simp add: Cons isin not_even not_odd None s'_def)
            have IH: "<graph_assn G Gi * matching_assn M Mi * queue_assn (queue s) (i_queue si) *
                       i_nbs si \<mapsto>\<^sub>a nbs * forest_assn (search_forest s) (i_forest si)>
                        f Gi Mi (si\<lparr>i_pos := Suc (i_pos si)\<rparr>)
                      <\<lambda>si'. graph_assn G Gi * matching_assn M Mi *
                             state_assn (Compute_Alt_Path_impl s) si'>"
              using 3[of s' "si\<lparr>i_pos := Suc (i_pos si)\<rparr>" nbs] pos(4) L invs'
              unfolding F by (simp add: pre_assn_def s'_def mult.assoc)
            show ?thesis
              using lt pos(1) not_even[unfolded wv] not_odd[unfolded wv] None[unfolded wv]
              by (sep_auto heap: EV OD LK IH)
          next
            case (Some x)
            have call: "Compute_Alt_Path_call_1_conds s"
              using Cons not_even not_odd Some
              by (simp add: Compute_Alt_Path_call_1_conds_def isin)
            obtain v' w' rest' x' where c: "unscanned s = (v', w') # rest'"
              "mate_lookup M w' = Some x'" "{w', x'} \<in> matching_abs M"
              "Forest.forest_extension_precond (search_forest s) (matching_abs M) v' w' x'"
              by (rule call_1_facts[OF Compute_Alt_Path_axiom call invs(1,2)])
            have c': "v' = v" "w' = w" "x' = x" "rest' = rest"
              using c(1,2) Cons Some by simp_all
            note c = c[unfolded c']
            have xK: "x \<in> K"
              using c(3) matching_invar_props(3)[OF matching_invar_M'] Vs_G_in_univ
              by (auto dest: edges_are_Vs_2)
            define s' where "s' = Compute_Alt_Path_upd1 s"
            note upd = upd1_fields[OF Compute_Alt_Path_axiom Cons Some, folded s'_def]
            have invs': "invars s'"
              using invars_holds_1[OF Compute_Alt_Path_axiom call invs(1-4)]
                invar_queue_length_upd1[OF call invs(1,2,5)]
              by (simp add: invars_def s'_def)
            have room: "length (queue s) < cap"
              by (rule queue_length_less_cap[OF call invs(1,2,5)])
            have F: "Compute_Alt_Path_impl s = Compute_Alt_Path_impl s'"
              by (subst Compute_Alt_Path_impl.simps)
                 (simp add: Cons isin not_even not_odd Some s'_def Compute_Alt_Path_upd1_def)
            text \<open>The program names the partner returned by the lookup @{term x'}.\<close>
            have EXT: "<forest_assn (search_forest s) (i_forest si)>
                        extend_forest_even_unclassified_imp (i_forest si) v w x'
                      <\<lambda>_. forest_assn (extend_forest_even_unclassified (search_forest s) v w x)
                             (i_forest si)>" if "x' = x" for x'
              using fr.extend_forest_even_unclassified_rule[OF c(4)] vK wK xK that by simp
            have IH: "<graph_assn G Gi * matching_assn M Mi *
                       queue_assn (x' # queue s) (i_queue si) * i_nbs si \<mapsto>\<^sub>a nbs *
                       forest_assn (extend_forest_even_unclassified (search_forest s) v w x)
                         (i_forest si)>
                        f Gi Mi (si\<lparr>i_pos := Suc (i_pos si)\<rparr>)
                      <\<lambda>si'. graph_assn G Gi * matching_assn M Mi *
                             state_assn (Compute_Alt_Path_impl s) si'>" if "x' = x" for x'
              using 3[of s' "si\<lparr>i_pos := Suc (i_pos si)\<rparr>" nbs] pos(4) L invs' that
              unfolding F by (simp add: pre_assn_def upd mult.assoc)
            show ?thesis
              using lt pos(1) not_even[unfolded wv] not_odd[unfolded wv] Some[unfolded wv]
              by (sep_auto heap: EV OD LK queue_push_rule[OF room] EXT[unfolded wv] IH[unfolded wv])          qed
        qed
      qed
    next
      case Nil
      have ge: "\<not> i_pos si < i_len si"
        using unscanned_NilD[OF U Nil] L by simp
      show ?thesis
      proof(cases "queue s")
        case Nil': Nil
        have F: "Compute_Alt_Path_impl s = s"
          by (subst Compute_Alt_Path_impl.simps) (simp add: Nil Nil')
        show ?thesis
          using ge Nil Nil' L U I
          by (sep_auto heap: queue_is_empty_rule simp: F state_assn_def pre_assn_def)
      next
        case (Cons v q)
        have invs: "invar_forest s" "invar_unscanned s" "invar_queue s" "invar_scanned s"
          "invar_queue_length s"
          using I Cons by (auto simp: invars_def)
        have call: "Compute_Alt_Path_call_3_conds s"
          using Nil Cons by (simp add: Compute_Alt_Path_call_3_conds_def)
        have vK: "v \<in> K"
          using invs(3) Cons aevens_subset_Vs[OF invs(1)] Vs_G_in_univ
          by (auto simp: invar_queue_def)
        have hdtl: "hd (queue s) = v" "tl (queue s) = q" "queue s \<noteq> []"
          using Cons by simp_all
        define s' where "s' = s\<lparr>queue := q, unscanned := map (Pair v) (neighbour_list G v)\<rparr>"
        have upd: "Compute_Alt_Path_upd3 s = s'"
          by (simp add: Compute_Alt_Path_upd3_def s'_def Cons)
        have invs': "invars s'"
          using invars_holds_3[OF Compute_Alt_Path_axiom call invs(1-4)]
            invar_queue_length_upd3[OF call invs(5)]
          by (simp add: invars_def upd)
        have F: "Compute_Alt_Path_impl s = Compute_Alt_Path_impl s'"
          by (subst Compute_Alt_Path_impl.simps) (simp add: Nil Cons s'_def)
        note NB = neighbours_rule[OF graph_inv_G vK]
        have IH: "<graph_assn G Gi * matching_assn M Mi * queue_assn q (i_queue si) *
                   A \<mapsto>\<^sub>a neighbour_list G v * forest_assn (search_forest s) (i_forest si)>
                    f Gi Mi (si\<lparr>i_cur := v, i_nbs := A, i_pos := 0,
                                i_len := length (neighbour_list G v)\<rparr>)
                  <\<lambda>si'. graph_assn G Gi * matching_assn M Mi *
                         state_assn (Compute_Alt_Path_impl s) si'>" for A
          using 3[of s' "si\<lparr>i_cur := v, i_nbs := A, i_pos := 0,
                            i_len := length (neighbour_list G v)\<rparr>" "neighbour_list G v"] invs'
          unfolding F by (simp add: pre_assn_def s'_def mult.assoc)
        show ?thesis
          using ge hdtl
          by (sep_auto heap: queue_is_empty_rule queue_top_rule queue_pop_rule NB IH)
      qed
    qed
  qed
qed

lemma Compute_Alt_Path_imp_rule:
  "<graph_assn G Gi * matching_assn M Mi * state_assn s si> Compute_Alt_Path_imp Gi Mi si
   <\<lambda>si'. graph_assn G Gi * matching_assn M Mi * state_assn (Compute_Alt_Path_impl s) si'>"
  unfolding state_assn_def[of s si]
  by (sep_auto heap: Compute_Alt_Path_imp_refine)

subsection \<open>Initialisation\<close>

definition "is_free v \<longleftrightarrow> neighbour_list G v \<noteq> [] \<and> mate_lookup M v = None"

lemma free_vertices_is_free: "free_vertices = filter is_free vs"
  by (simp add: free_vertices_def is_free_def[abs_def])

lemma is_free_imp_rule:
  "v \<in> K \<Longrightarrow>
   <graph_assn G Gi * matching_assn M Mi> is_free_imp Gi Mi v
   <\<lambda>r. graph_assn G Gi * matching_assn M Mi * \<up>(r \<longleftrightarrow> is_free v)>"
  unfolding is_free_imp_def is_free_def
  by (sep_auto heap: neighbours_rule[OF graph_inv_G] mt.lookup_partner_rule[OF matching_invar_abs_M])

definition "insert_if_free S v = (if is_free v then fset_insert v S else S)"

definition "push_if_free v q = (if is_free v then v # q else q)"

lemma foldl_insert_if_free:
  "foldl insert_if_free S xs = foldl (\<lambda>S v. fset_insert v S) S (filter is_free xs)"
  by (induction xs arbitrary: S) (auto simp: insert_if_free_def)

lemma foldr_push_if_free: "foldr push_if_free xs q = filter is_free xs @ q"
  by (induction xs) (auto simp: push_if_free_def)

lemma insert_if_free_imp_rule:
  assumes "v \<in> K"
  shows "<(fset_assn S Si * \<up>(fset_invar S)) * (graph_assn G Gi * matching_assn M Mi)>
           insert_if_free_imp Gi Mi v Si
         <\<lambda>r. (fset_assn (insert_if_free S v) r * \<up>(fset_invar (insert_if_free S v))) *
              (graph_assn G Gi * matching_assn M Mi)>"
  using assms
  unfolding insert_if_free_imp_def insert_if_free_def
  by (sep_auto heap: is_free_imp_rule fs.fixed_univ_set_insert_rule
      simp: Fset.fixed_univ_set_insert)

lemma push_if_free_imp_rule:
  assumes "v \<in> K" "length q < cap"
  shows "<queue_assn q Si * (graph_assn G Gi * matching_assn M Mi)>
           push_if_free_imp Gi Mi v Si
         <\<lambda>r. queue_assn (push_if_free v q) r * (graph_assn G Gi * matching_assn M Mi)>"
  using assms
  unfolding push_if_free_imp_def push_if_free_def
  by (sep_auto heap: is_free_imp_rule queue_push_rule)

lemma roots_fold_rule:
  "<Vi \<mapsto>\<^sub>a vs * (fset_assn fset_empty Ri * \<up>(fset_invar fset_empty)) *
    (graph_assn G Gi * matching_assn M Mi)>
     array_foldl Vi 0 (length vs) (insert_if_free_imp Gi Mi) Ri
   <\<lambda>r. Vi \<mapsto>\<^sub>a vs * (fset_assn initial_roots r * \<up>(fset_invar initial_roots)) *
        (graph_assn G Gi * matching_assn M Mi)>"
proof-
  have "initial_roots = foldl insert_if_free fset_empty vs"
    by (simp add: initial_roots_def foldl_insert_if_free free_vertices_is_free)
  thus ?thesis
    using array_foldl_all_rule[where acc_assn = "\<lambda>S Si. fset_assn S Si * \<up>(fset_invar S)"
        and F = "graph_assn G Gi * matching_assn M Mi" and f = insert_if_free and xs = vs,
        OF insert_if_free_imp_rule] vs_in_univ
    by auto
qed

lemma queue_fold_rule:
  "<Vi \<mapsto>\<^sub>a vs * queue_assn [] Si * (graph_assn G Gi * matching_assn M Mi)>
     array_foldr Vi (length vs) (push_if_free_imp Gi Mi) Si
   <\<lambda>r. Vi \<mapsto>\<^sub>a vs * queue_assn free_vertices r * (graph_assn G Gi * matching_assn M Mi)>"
proof-
  have room: "length (foldr push_if_free (drop (Suc j) (take (length vs) vs)) []) < cap"
    if "j < length vs" for j
  proof-
    have "length (foldr push_if_free (drop (Suc j) (take (length vs) vs)) []) \<le> length vs - Suc j"
      using length_filter_le[of is_free "drop (Suc j) vs"]
      by (simp add: foldr_push_if_free)
    thus ?thesis
      using that capacity by linarith
  qed
  have step: "<queue_assn (foldr push_if_free (drop (Suc j) (take (length vs) vs)) []) Si *
                (graph_assn G Gi * matching_assn M Mi)>
                push_if_free_imp Gi Mi (vs ! j) Si
              <\<lambda>r. queue_assn (push_if_free (vs ! j)
                     (foldr push_if_free (drop (Suc j) (take (length vs) vs)) [])) r *
                   (graph_assn G Gi * matching_assn M Mi)>"
    if "j < length vs" for j Si
    using push_if_free_imp_rule[OF _ room[OF that]] vs_in_univ that
    by (simp add: subset_iff)
  show ?thesis
    using array_foldr_rule[where acc_assn = queue_assn and f = push_if_free and acc = "[]"
        and F = "graph_assn G Gi * matching_assn M Mi" and xs = vs and n = "length vs",
        OF le_refl step]
    by (simp add: foldr_push_if_free free_vertices_is_free)
qed

lemma initial_state_fields:
  "queue initial_state = free_vertices" "unscanned initial_state = []"
  "search_forest initial_state = empty_forest initial_roots"
  by (simp_all add: initial_state_def)

lemma initial_state_invars:
  "invars initial_state \<or> (unscanned initial_state = [] \<and> queue initial_state = [])"
proof(cases "free_vertices = []")
  case True
  thus ?thesis
    by (simp add: initial_state_fields)
next
  case False
  thus ?thesis
    using initial_state_props[OF Compute_Alt_Path_axiom False] invar_queue_length_initial
    by (simp add: invars_def)
qed

lemma initial_state_imp_rule:
  "<graph_assn G Gi * matching_assn M Mi * Vi \<mapsto>\<^sub>a vs> initial_state_imp Gi Mi Vi
   <\<lambda>si. graph_assn G Gi * matching_assn M Mi * Vi \<mapsto>\<^sub>a vs * state_assn initial_state si>"
proof-
  have roots: "fset_invar initial_roots" "fset_to_set initial_roots \<subseteq> K"
    using initial_roots_props[OF Compute_Alt_Path_axiom] Vs_G_in_univ by auto
  note EF = fr.empty_forest_rule[OF roots]
  show ?thesis
    unfolding initial_state_imp_def
    using initial_state_invars Fset.fixed_univ_set_empty(1)
    by (sep_auto heap: fs.fixed_univ_set_empty_rule roots_fold_rule queue_empty_rule
        queue_fold_rule EF simp: state_assn_def pre_assn_def initial_state_fields)
qed

subsection \<open>The result\<close>

text \<open>The two paths are heap objects; the result relates them to the functional paths.\<close>

definition \<^marker>\<open>provenance ai_human\<close> "paths_res_assn P r =
  (case P of
     None \<Rightarrow> \<up>(r = None)
   | Some (p1, p2) \<Rightarrow>
       (case r of None \<Rightarrow> false | Some (Pt1, Pt2) \<Rightarrow> path_assn p1 Pt1 * path_assn p2 Pt2))"

lemma alternating_paths_imp_pre_rule:
  assumes "unscanned s \<noteq> [] \<Longrightarrow>
    Compute_Alt_Path_ret_1_conds s \<and> invar_forest s \<and> invar_unscanned s"
  shows "<pre_assn s si nbs> alternating_paths_imp si
         <\<lambda>r. paths_res_assn (alternating_paths s) r * true>"
  unfolding pre_assn_def
proof(rule ht_extract_pre_pure(1), goal_cases)
  case 1
  hence L: "i_len si = length nbs"
    and U: "unscanned s = map (Pair (i_cur si)) (drop (i_pos si) nbs)"
    by blast+
  show ?case
  proof(cases "unscanned s")
    case Nil
    have "\<not> i_pos si < i_len si"
      using unscanned_NilD[OF U Nil] L by simp
    thus ?thesis
      by (sep_auto simp: alternating_paths_imp_def alternating_paths_def Nil paths_res_assn_def)
  next
    case (Cons e rest)
    obtain v w where e: "e = (v, w)"
      by (cases e)
    note Cons = Cons[unfolded e]
    note pos = unscanned_ConsD[OF U Cons]
    note wv = pos(2,3)[symmetric]
    have lt: "i_pos si < i_len si"
      using pos(1) L by simp
    have I: "Compute_Alt_Path_ret_1_conds s" "invar_forest s" "invar_unscanned s"
      using assms Cons by auto
    have inv: "forest_invar (matching_abs M) (search_forest s)"
      by (rule invar_forestD(1)[OF I(2)])
    have vE: "v \<in> aevens s"
      using I(3) Cons by (auto simp: invar_unscanned_def)
    have wE: "w \<in> aevens s"
      using I(1) Cons by (auto simp: Compute_Alt_Path_ret_1_conds_def forest_isin[OF I(2)])
    note GP1 = fr.get_path_rule[OF inv vE, of "i_forest si", unfolded wv]
    note GP2 = fr.get_path_rule[OF inv wE, of "i_forest si", unfolded wv]
    have res: "alternating_paths s =
        Some (get_path (search_forest s) (i_cur si), get_path (search_forest s) (nbs ! i_pos si))"
      by (simp add: alternating_paths_def Cons wv)
    show ?thesis
      using lt pos(1)
      by (sep_auto heap: GP1 GP2 simp: alternating_paths_imp_def res paths_res_assn_def)
  qed
qed

lemma alternating_paths_imp_rule:
  assumes "unscanned s \<noteq> [] \<Longrightarrow>
    Compute_Alt_Path_ret_1_conds s \<and> invar_forest s \<and> invar_unscanned s"
  shows "<state_assn s si> alternating_paths_imp si
         <\<lambda>r. paths_res_assn (alternating_paths s) r * true>"
  unfolding state_assn_def
  by (sep_auto heap: alternating_paths_imp_pre_rule[OF assms])

subsection \<open>Correctness\<close>

theorem \<^marker>\<open>provenance ai_human\<close> Compute_Alt_Path_run_imp_rule:
  "<graph_assn G Gi * matching_assn M Mi * Vi \<mapsto>\<^sub>a vs> Compute_Alt_Path_run_imp Gi Mi Vi
   <\<lambda>r. graph_assn G Gi * matching_assn M Mi * Vi \<mapsto>\<^sub>a vs *
        paths_res_assn Compute_Alt_Path_run_impl r * true>"
proof \<^marker>\<open>provenance ai\<close>-
  let ?FS = "Compute_Alt_Path_impl initial_state"
  have FS: "?FS = Compute_Alt_Path initial_state"
    by (rule Compute_Alt_Path_impl_to_Compute_Alt_Path[OF Compute_Alt_Path_axiom])
  have final: "Compute_Alt_Path_ret_1_conds ?FS \<and> invar_forest ?FS \<and> invar_unscanned ?FS"
    if "unscanned ?FS \<noteq> []"
  proof(cases "free_vertices = []")
    case True
    thus ?thesis
      using that by (simp add: FS Compute_Alt_Path_empty[OF Compute_Alt_Path_axiom]
          initial_state_fields)
  next
    case False
    have "Compute_Alt_Path_ret_1_conds ?FS"
      using ret_holds[OF initial_state_dom[OF Compute_Alt_Path_axiom]] that
      by (auto simp: FS Compute_Alt_Path_ret_2_conds_def)
    thus ?thesis
      using final_state_invars[OF Compute_Alt_Path_axiom False] by (simp add: FS)
  qed
  show ?thesis
    unfolding Compute_Alt_Path_run_imp_def Compute_Alt_Path_run_impl_def
    by (sep_auto heap: initial_state_imp_rule Compute_Alt_Path_imp_rule
        alternating_paths_imp_rule[OF final])
qed

text \<open>The paths found by the imperative search are those of the functional one, and hence satisfy
  @{thm [source] Compute_Alt_Path_run_impl_correct}.\<close>

theorem \<^marker>\<open>provenance ai_human\<close> Compute_Alt_Path_run_imp_correct:
  "<graph_assn G Gi * matching_assn M Mi * Vi \<mapsto>\<^sub>a vs> Compute_Alt_Path_run_imp Gi Mi Vi
   <\<lambda>r. \<exists>\<^sub>A P. graph_assn G Gi * matching_assn M Mi * Vi \<mapsto>\<^sub>a vs * paths_res_assn P r *
        \<up>(compute_alt_path_spec (ugraph_abs G) (matching_abs M) P \<and>
          ((\<exists>p. graph_augmenting_path (ugraph_abs G) (matching_abs M) p) \<longrightarrow> P \<noteq> None))>"
  using \<^marker>\<open>provenance ai\<close> Compute_Alt_Path_run_impl_correct[OF Compute_Alt_Path_axiom]
  by \<^marker>\<open>provenance ai\<close> (sep_auto heap: Compute_Alt_Path_run_imp_rule)
end

end
