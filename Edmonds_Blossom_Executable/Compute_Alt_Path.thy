theory Compute_Alt_Path
  imports Compute_Alt_Path_Invars
begin

provenance ai

section \<open>Functional alternating forest search\<close>

named_theorems call_cond_elims
named_theorems call_cond_intros
named_theorems ret_holds_intros
named_theorems invar_props_intros
named_theorems invar_props_elims
named_theorems invar_holds_intros
named_theorems termination_intros

context Compute_Alt_Path
begin

function \<^marker>\<open>provenance ai_human\<close> (domintros) Compute_Alt_Path ::
  "('v, 'forest) Compute_Alt_Path_state \<Rightarrow> ('v, 'forest) Compute_Alt_Path_state" where
  "Compute_Alt_Path state =
    (case unscanned state of
       (v, w) # rest \<Rightarrow>
         (if fset_isin (evens (search_forest state)) w then state
          else if fset_isin (odds (search_forest state)) w then
            Compute_Alt_Path (state \<lparr>unscanned := rest\<rparr>)
          else case mate_lookup M w of
             Some x \<Rightarrow> Compute_Alt_Path
               (state \<lparr>queue := x # queue state, unscanned := rest,
                 search_forest := extend_forest_even_unclassified (search_forest state) v w x\<rparr>)
           | None \<Rightarrow> Compute_Alt_Path (state \<lparr>unscanned := rest\<rparr>))
     | [] \<Rightarrow>
         (case queue state of
            v # q \<Rightarrow> Compute_Alt_Path
              (state \<lparr>queue := q, unscanned := map (Pair v) (neighbour_list G v)\<rparr>)
          | [] \<Rightarrow> state))"
  by pat_completeness auto

partial_function \<^marker>\<open>provenance ai_human\<close> (tailrec) Compute_Alt_Path_impl ::
  "('v, 'forest) Compute_Alt_Path_state \<Rightarrow> ('v, 'forest) Compute_Alt_Path_state" where
  "Compute_Alt_Path_impl state =
    (case unscanned state of
       (v, w) # rest \<Rightarrow>
         (if fset_isin (evens (search_forest state)) w then state
          else if fset_isin (odds (search_forest state)) w then
            Compute_Alt_Path_impl (state \<lparr>unscanned := rest\<rparr>)
          else case mate_lookup M w of
             Some x \<Rightarrow> Compute_Alt_Path_impl
               (state \<lparr>queue := x # queue state, unscanned := rest,
                 search_forest := extend_forest_even_unclassified (search_forest state) v w x\<rparr>)
           | None \<Rightarrow> Compute_Alt_Path_impl (state \<lparr>unscanned := rest\<rparr>))
     | [] \<Rightarrow>
         (case queue state of
            v # q \<Rightarrow> Compute_Alt_Path_impl
              (state \<lparr>queue := q, unscanned := map (Pair v) (neighbour_list G v)\<rparr>)
          | [] \<Rightarrow> state))"

lemma Compute_Alt_Path_impl_same:
  "Compute_Alt_Path_dom state \<Longrightarrow> Compute_Alt_Path_impl state = Compute_Alt_Path state"
proof(induction rule: Compute_Alt_Path.pinduct)
  case (1 state)
  show ?case
    using 1(2-)
    by (subst Compute_Alt_Path_impl.simps, subst Compute_Alt_Path.psimps[OF 1(1)])
       (auto split: list.splits option.splits if_splits)
qed

definition "free_vertices = filter (\<lambda>v. neighbour_list G v \<noteq> [] \<and> mate_lookup M v = None) vs"

definition "initial_roots = foldl (\<lambda>S v. fset_insert v S) fset_empty free_vertices"

definition "initial_state =
  \<lparr>queue = free_vertices, unscanned = [], search_forest = empty_forest initial_roots\<rparr>"

definition "alternating_paths state =
  (case unscanned state of
     (v, w) # _ \<Rightarrow> Some (get_path (search_forest state) v, get_path (search_forest state) w)
   | [] \<Rightarrow> None)"

definition "Compute_Alt_Path_run = alternating_paths (Compute_Alt_Path initial_state)"
definition "Compute_Alt_Path_run_impl = alternating_paths (Compute_Alt_Path_impl initial_state)"

lemmas [code] = Compute_Alt_Path_impl.simps free_vertices_def initial_roots_def
  initial_state_def alternating_paths_def Compute_Alt_Path_run_impl_def

definition "Compute_Alt_Path_call_1_conds state =
  (\<exists>v w rest x. unscanned state = (v, w) # rest \<and>
    \<not> fset_isin (evens (search_forest state)) w \<and>
    \<not> fset_isin (odds (search_forest state)) w \<and> mate_lookup M w = Some x)"

definition "Compute_Alt_Path_upd1 state =
  (let (v, w) = hd (unscanned state); x = the (mate_lookup M w) in
   state \<lparr>queue := x # queue state, unscanned := tl (unscanned state),
     search_forest := extend_forest_even_unclassified (search_forest state) v w x\<rparr>)"

definition "Compute_Alt_Path_call_2_conds state =
  (\<exists>v w rest. unscanned state = (v, w) # rest \<and>
    \<not> fset_isin (evens (search_forest state)) w \<and>
    (fset_isin (odds (search_forest state)) w \<or> mate_lookup M w = None))"

definition "Compute_Alt_Path_upd2 state = state \<lparr>unscanned := tl (unscanned state)\<rparr>"

definition "Compute_Alt_Path_call_3_conds state =
  (\<exists>v q. unscanned state = [] \<and> queue state = v # q)"

definition "Compute_Alt_Path_upd3 state =
  (case queue state of
     v # q \<Rightarrow> state \<lparr>queue := q, unscanned := map (Pair v) (neighbour_list G v)\<rparr>
   | [] \<Rightarrow> state)"

definition "Compute_Alt_Path_ret_1_conds state =
  (\<exists>v w rest. unscanned state = (v, w) # rest \<and> fset_isin (evens (search_forest state)) w)"
definition "Compute_Alt_Path_ret_2_conds state = (unscanned state = [] \<and> queue state = [])"

abbreviation "Compute_Alt_Path_ret1 state \<equiv> state"
abbreviation "Compute_Alt_Path_ret2 state \<equiv> state"

lemma Compute_Alt_Path_cases:
  assumes "Compute_Alt_Path_call_1_conds state \<Longrightarrow> P"
    "Compute_Alt_Path_call_2_conds state \<Longrightarrow> P"
    "Compute_Alt_Path_call_3_conds state \<Longrightarrow> P"
    "Compute_Alt_Path_ret_1_conds state \<Longrightarrow> P"
    "Compute_Alt_Path_ret_2_conds state \<Longrightarrow> P"
  shows P
proof(cases "unscanned state")
  case Nil
  then show ?thesis
    using assms(3,5) by (cases "queue state")
      (auto simp: Compute_Alt_Path_call_3_conds_def Compute_Alt_Path_ret_2_conds_def)
next
  case (Cons e rest)
  obtain v w where e: "e = (v, w)"
    by (cases e)
  show ?thesis
    using assms Cons e
    by (cases "fset_isin (evens (search_forest state)) w";
        cases "fset_isin (odds (search_forest state)) w"; cases "mate_lookup M w")
       (auto simp: Compute_Alt_Path_call_1_conds_def Compute_Alt_Path_call_2_conds_def
          Compute_Alt_Path_ret_1_conds_def)
qed

lemma Compute_Alt_Path_simps:
  assumes "Compute_Alt_Path_dom state"
  shows "Compute_Alt_Path_call_1_conds state \<Longrightarrow>
    Compute_Alt_Path state = Compute_Alt_Path (Compute_Alt_Path_upd1 state)"
    "Compute_Alt_Path_call_2_conds state \<Longrightarrow>
    Compute_Alt_Path state = Compute_Alt_Path (Compute_Alt_Path_upd2 state)"
    "Compute_Alt_Path_call_3_conds state \<Longrightarrow>
    Compute_Alt_Path state = Compute_Alt_Path (Compute_Alt_Path_upd3 state)"
    "Compute_Alt_Path_ret_1_conds state \<Longrightarrow> Compute_Alt_Path state = state"
    "Compute_Alt_Path_ret_2_conds state \<Longrightarrow> Compute_Alt_Path state = state"
  by (auto simp: Compute_Alt_Path.psimps[OF assms] Let_def
      Compute_Alt_Path_call_1_conds_def Compute_Alt_Path_upd1_def
      Compute_Alt_Path_call_2_conds_def Compute_Alt_Path_upd2_def
      Compute_Alt_Path_call_3_conds_def Compute_Alt_Path_upd3_def
      Compute_Alt_Path_ret_1_conds_def Compute_Alt_Path_ret_2_conds_def
      split: option.splits if_splits)

lemma Compute_Alt_Path_induct:
  assumes "Compute_Alt_Path_dom state"
    "\<And>state. \<lbrakk>Compute_Alt_Path_dom state;
      Compute_Alt_Path_call_1_conds state \<Longrightarrow> P (Compute_Alt_Path_upd1 state);
      Compute_Alt_Path_call_2_conds state \<Longrightarrow> P (Compute_Alt_Path_upd2 state);
      Compute_Alt_Path_call_3_conds state \<Longrightarrow> P (Compute_Alt_Path_upd3 state)\<rbrakk>
      \<Longrightarrow> P state"
  shows "P state"
  using assms(1)
proof(induction rule: Compute_Alt_Path.pinduct)
  case (1 state)
  show ?case
    by (rule assms(2)[OF 1(1)]; insert 1; fastforce simp: Compute_Alt_Path_call_1_conds_def Compute_Alt_Path_upd1_def
         Compute_Alt_Path_call_2_conds_def Compute_Alt_Path_upd2_def
         Compute_Alt_Path_call_3_conds_def Compute_Alt_Path_upd3_def Let_def
         split: option.splits if_splits)
qed

lemma Compute_Alt_Path_domintros:
  assumes "Compute_Alt_Path_call_1_conds state \<Longrightarrow> Compute_Alt_Path_dom (Compute_Alt_Path_upd1 state)"
    "Compute_Alt_Path_call_2_conds state \<Longrightarrow> Compute_Alt_Path_dom (Compute_Alt_Path_upd2 state)"
    "Compute_Alt_Path_call_3_conds state \<Longrightarrow> Compute_Alt_Path_dom (Compute_Alt_Path_upd3 state)"
  shows "Compute_Alt_Path_dom state"
  by (rule Compute_Alt_Path.domintros; insert assms; auto simp: Compute_Alt_Path_call_1_conds_def Compute_Alt_Path_upd1_def
       Compute_Alt_Path_call_2_conds_def Compute_Alt_Path_upd2_def
       Compute_Alt_Path_call_3_conds_def Compute_Alt_Path_upd3_def Let_def)

lemma ret_holds[ret_holds_intros]:
  assumes "Compute_Alt_Path_dom state"
  shows "Compute_Alt_Path_ret_1_conds (Compute_Alt_Path state) \<or>
         Compute_Alt_Path_ret_2_conds (Compute_Alt_Path state)"
proof(induction rule: Compute_Alt_Path_induct[OF assms])
  case IH: (1 state)
  show ?case
  proof(rule Compute_Alt_Path_cases[where state = state])
    assume c: "Compute_Alt_Path_call_1_conds state"
    show ?thesis
      using IH(2)[OF c]
      by (simp add: Compute_Alt_Path_simps(1)[OF IH(1) c])
  next
    assume c: "Compute_Alt_Path_call_2_conds state"
    show ?thesis
      using IH(3)[OF c]
      by (simp add: Compute_Alt_Path_simps(2)[OF IH(1) c])
  next
    assume c: "Compute_Alt_Path_call_3_conds state"
    show ?thesis
      using IH(4)[OF c]
      by (simp add: Compute_Alt_Path_simps(3)[OF IH(1) c])
  next
    assume c: "Compute_Alt_Path_ret_1_conds state"
    show ?thesis
      using c
      by (simp add: Compute_Alt_Path_simps(4)[OF IH(1) c])
  next
    assume c: "Compute_Alt_Path_ret_2_conds state"
    show ?thesis
      using c
      by (simp add: Compute_Alt_Path_simps(5)[OF IH(1) c])
  qed
qed

context
  assumes Compute_Alt_Path_axiom: Compute_Alt_Path_axiom
begin

lemma graph_input_G[simp]: "graph_input G vs"
  and matching_invar_M[simp]: "matching_invar G M"
  using Compute_Alt_Path_axiom
  by (simp_all add: Compute_Alt_Path_axiom_def)

interpretation abs_search: compute_alt_path
  where G = "ugraph_abs G" and M = "matching_abs M"
    and vset_invar = fset_invar and vset_to_set = fset_to_set
    and evens = evens and odds = odds and roots = roots
    and get_path = get_path and abstract_forest = abstract_forest
    and forest_invar = forest_invar
    and extend_forest_even_unclassified = extend_forest_even_unclassified
    and empty_forest = empty_forest and forest_univ = K and vset_empty = fset_empty
proof(rule compute_alt_path.intro)
  show "match (ugraph_abs G) (matching_abs M)"
    by unfold_locales
       (use ugraph_abs_graph_invar[OF graph_input_G]
         matching_invar_props[OF matching_invar_M] in auto)
  show "alternating_forest_ordinary_extension_spec fset_invar fset_to_set evens odds get_path
    abstract_forest forest_invar roots extend_forest_even_unclassified empty_forest K fset_empty"
    by (rule Forest.alternating_forest_ordinary_extension_spec_axioms)
qed

lemma finite_Vs_G[simp]: "finite (Vs (ugraph_abs G))"
  using ugraph_abs_graph_invar[OF graph_input_G] by simp

lemma Vs_G_subset_vs: "Vs (ugraph_abs G) \<subseteq> set vs"
  by (rule Vs_ugraph_abs_subset_vs[OF graph_input_G])

lemma mate_lookup_iff: "mate_lookup M u = Some v \<longleftrightarrow> {u, v} \<in> matching_abs M"
  using matching_invar_M by (simp add: matching_invar_def matching_abs_iff)

lemma Vs_matching_iff: "u \<in> Vs (matching_abs M) \<longleftrightarrow> mate_lookup M u \<noteq> None"
  by (rule Vs_matching_abs_iff[OF graph_input_G matching_invar_M])

lemma set_free_vertices:
  "set free_vertices = Vs (ugraph_abs G) - Vs (matching_abs M)"
  using Vs_G_subset_vs
  by (auto simp: free_vertices_def neighbour_list_nonempty_iff[OF graph_input_G]
      Vs_matching_iff)

lemma upd1_fields:
  assumes "unscanned state = (v, w) # rest" "mate_lookup M w = Some x"
  shows "search_forest (Compute_Alt_Path_upd1 state) =
      extend_forest_even_unclassified (search_forest state) v w x"
    "queue (Compute_Alt_Path_upd1 state) = x # queue state"
    "unscanned (Compute_Alt_Path_upd1 state) = rest"
  using assms by (simp_all add: Compute_Alt_Path_upd1_def Let_def)

lemma call_1_facts:
  assumes "Compute_Alt_Path_call_1_conds state" "invar_forest state" "invar_unscanned state"
  obtains v w rest x where
    "unscanned state = (v, w) # rest" "mate_lookup M w = Some x"
    "{v, w} \<in> ugraph_abs G" "{w, x} \<in> matching_abs M"
    "w \<notin> aevens state \<union> aodds state"
    "Forest.forest_extension_precond (search_forest state) (matching_abs M) v w x"
proof-
  obtain v w rest x where c: "unscanned state = (v, w) # rest"
    "\<not> fset_isin (evens (search_forest state)) w"
    "\<not> fset_isin (odds (search_forest state)) w" "mate_lookup M w = Some x"
    using assms(1) by (auto simp: Compute_Alt_Path_call_1_conds_def)
  have edge: "{v, w} \<in> ugraph_abs G" and v: "v \<in> aevens state"
    using assms(3) c(1) by (auto simp: invar_unscanned_def)
  have w: "w \<notin> aevens state \<union> aodds state"
    using c(2,3) by (simp add: forest_isin[OF assms(2)])
  have outside: "w \<notin> Vs (abs_examined state)"
    using w Forest.evens_and_odds(3)[OF invar_forestD(1)[OF assms(2)]] by blast
  have matching_edge: "{w, x} \<in> matching_abs M"
    using c(4) by (simp add: mate_lookup_iff)
  have "abs_search.if1 (search_forest state) v w x"
    using edge v outside matching_edge
    by (auto simp: abs_search.if1_def dest: edges_are_Vs_2)
  hence "Forest.forest_extension_precond (search_forest state) (matching_abs M) v w x"
    by (rule abs_search.if_1_forest_extension_precond[OF invar_forestD(1)[OF assms(2)]])
  thus ?thesis
    using that c(1,4) edge matching_edge w by blast
qed

lemma call_2_odd:
  assumes "Compute_Alt_Path_call_2_conds state" "invar_forest state" "invar_unscanned state"
  obtains v w rest where "unscanned state = (v, w) # rest" "w \<in> aodds state"
proof-
  obtain v w rest where c: "unscanned state = (v, w) # rest"
    "w \<notin> aevens state" "w \<in> aodds state \<or> mate_lookup M w = None"
    using assms(1) by (auto simp: Compute_Alt_Path_call_2_conds_def
      forest_isin[OF assms(2)])
  have "w \<in> Vs (ugraph_abs G)"
    using assms(3) c(1) by (auto simp: invar_unscanned_def dest: edges_are_Vs_2)
  hence "w \<in> aodds state"
    using c(2,3) invar_forestD(3)[OF assms(2)]
      Forest.roots(2)[OF invar_forestD(1)[OF assms(2)]]
    by (auto simp: Vs_matching_iff)
  thus ?thesis
    by (rule that[OF c(1)])
qed

subsection \<open>Preservation of the forest and work lists\<close>

lemma invars_holds_1[invar_holds_intros]:
  assumes "Compute_Alt_Path_call_1_conds state" "invar_forest state"
    "invar_unscanned state" "invar_queue state" "invar_scanned state"
  shows "invar_forest (Compute_Alt_Path_upd1 state)"
    "invar_unscanned (Compute_Alt_Path_upd1 state)"
    "invar_queue (Compute_Alt_Path_upd1 state)"
    "invar_scanned (Compute_Alt_Path_upd1 state)"
proof-
  obtain v w rest x where c: "unscanned state = (v, w) # rest"
    "mate_lookup M w = Some x" "{v, w} \<in> ugraph_abs G" "{w, x} \<in> matching_abs M"
    "w \<notin> aevens state \<union> aodds state"
    "Forest.forest_extension_precond (search_forest state) (matching_abs M) v w x"
    by (rule call_1_facts[OF assms(1-3)])
  note ext = Forest.forest_extend[OF c(6)]
  note upd = upd1_fields[OF c(1,2)]
  show "invar_forest (Compute_Alt_Path_upd1 state)"
    using assms(2) ext c(3,4) matching_invar_props(3)[OF matching_invar_M]
    by (auto simp: invar_forest_def upd)
  show "invar_unscanned (Compute_Alt_Path_upd1 state)"
    using assms(3) ext(3)
    by (auto simp: invar_unscanned_def upd c(1))
  show "invar_queue (Compute_Alt_Path_upd1 state)"
    using assms(4) ext(3)
    by (auto simp: invar_queue_def upd)
  show "invar_scanned (Compute_Alt_Path_upd1 state)"
    using assms(5) ext(3,4)
    by (auto simp: invar_scanned_def upd c(1))
qed

lemma invars_holds_2[invar_holds_intros]:
  assumes "Compute_Alt_Path_call_2_conds state" "invar_forest state"
    "invar_unscanned state" "invar_queue state" "invar_scanned state"
  shows "invar_forest (Compute_Alt_Path_upd2 state)"
    "invar_unscanned (Compute_Alt_Path_upd2 state)"
    "invar_queue (Compute_Alt_Path_upd2 state)"
    "invar_scanned (Compute_Alt_Path_upd2 state)"
proof-
  obtain v w rest where c: "unscanned state = (v, w) # rest" "w \<in> aodds state"
    by (rule call_2_odd[OF assms(1-3)])
  show "invar_forest (Compute_Alt_Path_upd2 state)"
    "invar_unscanned (Compute_Alt_Path_upd2 state)"
    "invar_queue (Compute_Alt_Path_upd2 state)"
    "invar_scanned (Compute_Alt_Path_upd2 state)"
    using assms(2-) c
    by (auto simp: Compute_Alt_Path_upd2_def invar_forest_def
        invar_unscanned_def invar_queue_def invar_scanned_def)
qed

lemma invars_holds_3[invar_holds_intros]:
  assumes "Compute_Alt_Path_call_3_conds state" "invar_forest state"
    "invar_unscanned state" "invar_queue state" "invar_scanned state"
  shows "invar_forest (Compute_Alt_Path_upd3 state)"
    "invar_unscanned (Compute_Alt_Path_upd3 state)"
    "invar_queue (Compute_Alt_Path_upd3 state)"
    "invar_scanned (Compute_Alt_Path_upd3 state)"
proof-
  obtain v q where c: "unscanned state = []" "queue state = v # q"
    using assms(1) by (auto simp: Compute_Alt_Path_call_3_conds_def)
  show "invar_forest (Compute_Alt_Path_upd3 state)"
    "invar_unscanned (Compute_Alt_Path_upd3 state)"
    "invar_queue (Compute_Alt_Path_upd3 state)"
    "invar_scanned (Compute_Alt_Path_upd3 state)"
    using assms(2-)
    by (auto simp: Compute_Alt_Path_upd3_def c invar_forest_def
        invar_unscanned_def invar_queue_def invar_scanned_def
        neighbour_list_ugraph_abs[OF graph_input_G])
qed

lemma invars_holds:
  assumes "Compute_Alt_Path_dom state" "invar_forest state"
    "invar_unscanned state" "invar_queue state" "invar_scanned state"
  shows "invar_forest (Compute_Alt_Path state) \<and>
    invar_unscanned (Compute_Alt_Path state) \<and>
    invar_queue (Compute_Alt_Path state) \<and> invar_scanned (Compute_Alt_Path state)"
  using assms(2-)
proof(induction rule: Compute_Alt_Path_induct[OF assms(1)])
  case IH: (1 state)
  show ?case
    apply (rule Compute_Alt_Path_cases[where state = state])
    using IH(2-)
    by (auto intro: invar_holds_intros simp: Compute_Alt_Path_simps[OF IH(1)])
qed

subsection \<open>Termination\<close>

definition "call_1_measure state = card (Vs (ugraph_abs G) - (aevens state \<union> aodds state))"
definition "call_2_measure state = length (unscanned state)"
definition "call_3_measure state = length (queue state)"
definition "Compute_Alt_Path_term_rel' =
  call_1_measure <*mlex*> call_3_measure <*mlex*> call_2_measure <*mlex*> {}"

lemma call_1_terminates:
  assumes "Compute_Alt_Path_call_1_conds state" "invar_forest state" "invar_unscanned state"
  shows "(Compute_Alt_Path_upd1 state, state) \<in> call_1_measure <*mlex*> r"
proof-
  obtain v w rest x where c: "unscanned state = (v, w) # rest"
    "mate_lookup M w = Some x" "{v, w} \<in> ugraph_abs G" "{w, x} \<in> matching_abs M"
    "w \<notin> aevens state \<union> aodds state"
    "Forest.forest_extension_precond (search_forest state) (matching_abs M) v w x"
    by (rule call_1_facts[OF assms])
  let ?U = "\<lambda>s. Vs (ugraph_abs G) - (aevens s \<union> aodds s)"
  have "w \<in> ?U state"
    using c(3,5) by (auto dest: edges_are_Vs_2)
  moreover have "?U (Compute_Alt_Path_upd1 state) \<subseteq> ?U state - {w}"
    by (auto simp: upd1_fields[OF c(1,2)] Forest.forest_extend(3,4)[OF c(6)])
  ultimately have "?U (Compute_Alt_Path_upd1 state) \<subset> ?U state"
    by blast
  hence "call_1_measure (Compute_Alt_Path_upd1 state) < call_1_measure state"
    by (simp add: call_1_measure_def psubset_card_mono)
  thus ?thesis
    by (rule mlex_less)
qed

lemma in_Compute_Alt_Path_term_rel':
  "\<lbrakk>Compute_Alt_Path_call_1_conds state; invar_forest state; invar_unscanned state\<rbrakk>
    \<Longrightarrow> (Compute_Alt_Path_upd1 state, state) \<in> Compute_Alt_Path_term_rel'"
  "Compute_Alt_Path_call_2_conds state
    \<Longrightarrow> (Compute_Alt_Path_upd2 state, state) \<in> Compute_Alt_Path_term_rel'"
  "Compute_Alt_Path_call_3_conds state
    \<Longrightarrow> (Compute_Alt_Path_upd3 state, state) \<in> Compute_Alt_Path_term_rel'"
  by (auto simp: Compute_Alt_Path_term_rel'_def mlex_iff
      Compute_Alt_Path_call_2_conds_def Compute_Alt_Path_call_3_conds_def
      Compute_Alt_Path_upd2_def Compute_Alt_Path_upd3_def
      call_1_measure_def call_2_measure_def call_3_measure_def
      dest: call_1_terminates[where r = "{}", unfolded mlex_iff])

lemma Compute_Alt_Path_terminates[termination_intros]:
  assumes "invar_forest state" "invar_unscanned state" "invar_queue state" "invar_scanned state"
  shows "Compute_Alt_Path_dom state"
proof-
  have wf: "wf Compute_Alt_Path_term_rel'"
    by (simp add: Compute_Alt_Path_term_rel'_def wf_mlex)
  show ?thesis
    using wf assms
  proof(induction rule: wf_induct_rule)
    case (less state)
    show ?case
      by (rule Compute_Alt_Path_domintros)
         (auto intro!: less.IH intro: in_Compute_Alt_Path_term_rel' invar_holds_intros
           less.prems)
  qed
qed

subsection \<open>Initialization and correctness\<close>

lemma foldl_fset_insert:
  assumes "set xs \<subseteq> K" "fset_invar S"
  shows "fset_invar (foldl (\<lambda>S v. fset_insert v S) S xs) \<and>
    fset_to_set (foldl (\<lambda>S v. fset_insert v S) S xs) = fset_to_set S \<union> set xs"
  using assms
  by (induction xs arbitrary: S) (auto simp: Fset.fixed_univ_set_insert)

lemma initial_roots_props:
  "fset_invar initial_roots"
  "fset_to_set initial_roots = Vs (ugraph_abs G) - Vs (matching_abs M)"
proof-
  have "set free_vertices \<subseteq> K"
    using graph_inputD(7)[OF graph_input_G] by (auto simp: free_vertices_def)
  from foldl_fset_insert[OF this Fset.fixed_univ_set_empty(1)]
  show "fset_invar initial_roots"
    "fset_to_set initial_roots = Vs (ugraph_abs G) - Vs (matching_abs M)"
    by (auto simp: initial_roots_def Fset.fixed_univ_set_empty(2) set_free_vertices)
qed

lemma initial_forest_invar:
  assumes "free_vertices \<noteq> []"
  shows "forest_invar (matching_abs M) (empty_forest initial_roots)"
  using assms initial_roots_props matching_invar_props(2)[OF matching_invar_M]
    matching_invar_props(5)[OF matching_invar_M graph_input_G]
    Vs_subset[OF matching_invar_props(3)[OF matching_invar_M]] set_free_vertices
  by (intro Forest.empty_forest(5)) auto

lemma initial_state_props[invar_holds_intros]:
  assumes "free_vertices \<noteq> []"
  shows "invar_forest initial_state" "invar_unscanned initial_state"
    "invar_queue initial_state" "invar_scanned initial_state"
  using initial_forest_invar[OF assms] initial_roots_props set_free_vertices
    Forest.roots_are_unmatched_evens[OF initial_forest_invar[OF assms]]
  by (auto simp: initial_state_def invar_forest_def invar_unscanned_def
      invar_queue_def invar_scanned_def Forest.empty_forest(1,4))

lemma Compute_Alt_Path_correct_ret_1:
  assumes "Compute_Alt_Path_ret_1_conds state" "invar_forest state" "invar_unscanned state"
  shows "compute_alt_path_spec (ugraph_abs G) (matching_abs M) (alternating_paths state)"
proof-
  obtain v w rest where "unscanned state = (v, w) # rest"
    "v \<in> aevens state" "w \<in> aevens state" "{v, w} \<in> ugraph_abs G"
    using assms by (auto simp: Compute_Alt_Path_ret_1_conds_def invar_unscanned_def
      forest_isin[OF assms(2)])
  thus ?thesis
    using invar_forestD(1,2)[OF assms(2)]
    by (auto simp: alternating_paths_def intro: abs_search.forest_paths_sound)
qed

lemma Compute_Alt_Path_correct_ret_2:
  assumes "Compute_Alt_Path_ret_2_conds state" "invar_forest state" "invar_scanned state"
  shows "\<not> graph_augmenting_path (ugraph_abs G) (matching_abs M) p"
proof-
  have closed: "\<And>v w. \<lbrakk>v \<in> aevens state; {v, w} \<in> ugraph_abs G\<rbrakk> \<Longrightarrow> w \<in> aodds state"
    using assms(1,3)
    by (auto simp: Compute_Alt_Path_ret_2_conds_def invar_scanned_def)
  have "\<not> abs_search.if1_cond (search_forest state)"
    using closed Forest.evens_and_odds_basis(4)[OF invar_forestD(1)[OF assms(2)]]
    by (auto simp: abs_search.if1_cond_def)
  moreover have "\<not> abs_search.if2_cond (search_forest state)"
    using closed Forest.evens_and_odds(4)[OF invar_forestD(1)[OF assms(2)]]
    by (auto simp: abs_search.if2_cond_def)
  moreover have "Vs (ugraph_abs G) - Vs (matching_abs M) \<subseteq> aevens state"
    using invar_forestD(3)[OF assms(2)] Forest.roots(2)[OF invar_forestD(1)[OF assms(2)]]
    by blast
  ultimately show ?thesis
    using invar_forestD(1)[OF assms(2)]
    by (auto dest: abs_search.termination_conditions_no_augpath)
qed

lemma initial_state_dom[termination_intros]: "Compute_Alt_Path_dom initial_state"
proof(cases "free_vertices = []")
  case True
  show ?thesis
    by (rule Compute_Alt_Path_domintros; insert True; auto simp: initial_state_def Compute_Alt_Path_call_1_conds_def
         Compute_Alt_Path_call_2_conds_def Compute_Alt_Path_call_3_conds_def)
next
  case False
  show ?thesis
    by (rule Compute_Alt_Path_terminates[OF initial_state_props[OF False]])
qed

lemma Compute_Alt_Path_impl_to_Compute_Alt_Path:
  "Compute_Alt_Path_impl initial_state = Compute_Alt_Path initial_state"
  by (rule Compute_Alt_Path_impl_same[OF initial_state_dom])

lemma Compute_Alt_Path_empty:
  assumes "free_vertices = []"
  shows "Compute_Alt_Path initial_state = initial_state"
  by (rule Compute_Alt_Path_simps(5)[OF initial_state_dom])
     (simp add: Compute_Alt_Path_ret_2_conds_def initial_state_def assms)

lemma no_augmenting_path_without_free_vertices:
  assumes "free_vertices = []"
  shows "\<not> graph_augmenting_path (ugraph_abs G) (matching_abs M) p"
proof
  assume "graph_augmenting_path (ugraph_abs G) (matching_abs M) p"
  hence "p \<noteq> []" "hd p \<notin> Vs (matching_abs M)" "path (ugraph_abs G) p"
    by (auto simp: matching_augmenting_path_def)
  moreover from this(1,3) have "hd p \<in> Vs (ugraph_abs G)"
    by (auto intro: mem_path_Vs)
  ultimately show False
    using assms set_free_vertices by auto
qed

lemma final_state_invars:
  assumes "free_vertices \<noteq> []"
  shows "invar_forest (Compute_Alt_Path initial_state)"
    "invar_unscanned (Compute_Alt_Path initial_state)"
    "invar_scanned (Compute_Alt_Path initial_state)"
  using invars_holds[OF initial_state_dom initial_state_props[OF assms]]
  by auto

lemma Compute_Alt_Path_correct_1:
  "compute_alt_path_spec (ugraph_abs G) (matching_abs M)
    (alternating_paths (Compute_Alt_Path initial_state))"
proof(cases "free_vertices = []")
  case True
  show ?thesis
    unfolding Compute_Alt_Path_empty[OF True]
    by (simp add: initial_state_def alternating_paths_def compute_alt_path_spec_def)
next
  case False
  show ?thesis
    using ret_holds[OF initial_state_dom] final_state_invars[OF False]
    by (auto intro: Compute_Alt_Path_correct_ret_1;
        auto simp: Compute_Alt_Path_ret_2_conds_def alternating_paths_def compute_alt_path_spec_def)
qed

lemma Compute_Alt_Path_correct_2:
  assumes "\<exists>p. graph_augmenting_path (ugraph_abs G) (matching_abs M) p"
  shows "alternating_paths (Compute_Alt_Path initial_state) \<noteq> None"
proof(cases "free_vertices = []")
  case True
  then show ?thesis
    using assms no_augmenting_path_without_free_vertices by blast
next
  case False
  show ?thesis
    using ret_holds[OF initial_state_dom] final_state_invars[OF False] assms
    by (auto dest: Compute_Alt_Path_correct_ret_2
        simp: Compute_Alt_Path_ret_1_conds_def alternating_paths_def)
qed

lemma Compute_Alt_Path_run_impl_correct:
  "compute_alt_path_spec (ugraph_abs G) (matching_abs M) Compute_Alt_Path_run_impl"
  "\<exists>p. graph_augmenting_path (ugraph_abs G) (matching_abs M) p \<Longrightarrow>
    Compute_Alt_Path_run_impl \<noteq> None"
  using Compute_Alt_Path_correct_1 Compute_Alt_Path_correct_2
  by (simp_all add: Compute_Alt_Path_run_impl_def Compute_Alt_Path_impl_to_Compute_Alt_Path)

end

end
end

