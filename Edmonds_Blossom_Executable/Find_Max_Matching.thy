theory Find_Max_Matching
  imports Graph_Matching_Specs
begin

provenance ai_human

section \<open>The top loop of Edmonds' blossom algorithm\<close>

text \<open>The top loop starts from the empty matching and augments the current matching along an
  augmenting path for as long as the search procedure finds one. When the search reports that no
  augmenting path exists, the matching has maximum cardinality by Berge's lemma. The search
  procedure is a parameter, specified by its soundness and its completeness.\<close>

subsection \<open>The program state\<close>

record 'mate Find_Max_Matching_state =
  current_matching :: 'mate

subsection \<open>Setup for automation\<close>

named_theorems call_cond_elims
named_theorems call_cond_intros
named_theorems ret_holds_intros
named_theorems invar_props_intros
named_theorems invar_props_elims
named_theorems invar_holds_intros
named_theorems state_rel_intros
named_theorems state_rel_holds_intros

subsection \<open>The loop\<close>

locale Find_Max_Matching = Graph_Matching_Specs where lookup = lookup and mate_empty = mate_empty
  for lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option" and mate_empty :: 'mate +
  fixes G :: 'adjmap and vs :: "'v list"
    and aug_path_search :: "'mate \<Rightarrow> 'v list option"
  assumes aug_path_search:
    "\<And>M p. \<lbrakk>graph_input G vs; matching_invar G M; aug_path_search M = Some p\<rbrakk>
       \<Longrightarrow> graph_augmenting_path (ugraph_abs G) (matching_abs M) p"
    "\<And>M. \<lbrakk>graph_input G vs; matching_invar G M;
           \<exists>p. graph_augmenting_path (ugraph_abs G) (matching_abs M) p\<rbrakk>
       \<Longrightarrow> aug_path_search M \<noteq> None"
begin

definition "Find_Max_Matching_axiom = graph_input G vs"

function \<^marker>\<open>provenance ai_human\<close> (domintros) Find_Max_Matching ::
  "'mate Find_Max_Matching_state \<Rightarrow> 'mate Find_Max_Matching_state" where
  "Find_Max_Matching state =
     (case aug_path_search (current_matching state) of
        Some p \<Rightarrow>
          Find_Max_Matching
            (state \<lparr>current_matching := mate_augment (current_matching state) p\<rparr>)
      | None \<Rightarrow> state)"
  by pat_completeness auto

partial_function \<^marker>\<open>provenance ai_human\<close> (tailrec) Find_Max_Matching_impl ::
  "'mate Find_Max_Matching_state \<Rightarrow> 'mate Find_Max_Matching_state" where
  "Find_Max_Matching_impl state =
     (case aug_path_search (current_matching state) of
        Some p \<Rightarrow>
          Find_Max_Matching_impl
            (state \<lparr>current_matching := mate_augment (current_matching state) p\<rparr>)
      | None \<Rightarrow> state)"

lemma Find_Max_Matching_impl_same:
  assumes "Find_Max_Matching_dom state"
  shows "Find_Max_Matching_impl state = Find_Max_Matching state"
proof(induction rule: Find_Max_Matching.pinduct[OF assms])
  case (1 state)
  show ?case
    by (subst Find_Max_Matching_impl.simps, subst Find_Max_Matching.psimps[OF 1(1)])
       (auto split: option.splits intro: 1(2))
qed

definition \<^marker>\<open>provenance ai_human\<close> "initial_state = \<lparr>current_matching = mate_empty\<rparr>"

definition \<^marker>\<open>provenance ai_human\<close> "Find_Max_Matching_run = Find_Max_Matching initial_state"

definition \<^marker>\<open>provenance ai_human\<close> "Find_Max_Matching_run_impl = Find_Max_Matching_impl initial_state"

lemmas [code] = Find_Max_Matching_impl.simps initial_state_def Find_Max_Matching_run_impl_def

definition "Find_Max_Matching_call_1_conds state =
  (\<exists>p. aug_path_search (current_matching state) = Some p)"

definition "Find_Max_Matching_upd1 state =
  state \<lparr>current_matching :=
           mate_augment (current_matching state)
             (the (aug_path_search (current_matching state)))\<rparr>"

definition "Find_Max_Matching_ret_1_conds state =
  (aug_path_search (current_matching state) = None)"

abbreviation "Find_Max_Matching_ret1 state \<equiv> state"

definition "invar_current_matching state = matching_invar G (current_matching state)"

definition "call_1_measure state =
  card (ugraph_abs G) - card (matching_abs (current_matching state))"

definition "Find_Max_Matching_term_rel' = call_1_measure <*mlex*> {}"

lemma Find_Max_Matching_call_1_conds[call_cond_elims]:
  "\<lbrakk>Find_Max_Matching_call_1_conds state;
   ((\<exists>p. aug_path_search (current_matching state) = Some p) \<Longrightarrow> P) \<rbrakk> \<Longrightarrow> P"
  by (auto simp: Find_Max_Matching_call_1_conds_def)

lemma Find_Max_Matching_call_1_condsI[call_cond_intros]:
  "aug_path_search (current_matching state) = Some p \<Longrightarrow>
   Find_Max_Matching_call_1_conds state"
  by (auto simp: Find_Max_Matching_call_1_conds_def)

lemma Find_Max_Matching_ret_1_conds[call_cond_elims]:
  "\<lbrakk>Find_Max_Matching_ret_1_conds state;
   (aug_path_search (current_matching state) = None \<Longrightarrow> P) \<rbrakk> \<Longrightarrow> P"
  by (auto simp: Find_Max_Matching_ret_1_conds_def)

lemma Find_Max_Matching_ret_1_condsI[call_cond_intros]:
  "aug_path_search (current_matching state) = None \<Longrightarrow>
   Find_Max_Matching_ret_1_conds state"
  by (auto simp: Find_Max_Matching_ret_1_conds_def)

lemma Find_Max_Matching_cases:
  assumes "Find_Max_Matching_call_1_conds state \<Longrightarrow> P"
          "Find_Max_Matching_ret_1_conds state \<Longrightarrow> P"
  shows "P"
  using assms
  by (cases "aug_path_search (current_matching state)")
     (auto simp: Find_Max_Matching_call_1_conds_def Find_Max_Matching_ret_1_conds_def)

lemma Find_Max_Matching_simps:
  assumes "Find_Max_Matching_dom state"
  shows "Find_Max_Matching_call_1_conds state \<Longrightarrow>
           Find_Max_Matching state = Find_Max_Matching (Find_Max_Matching_upd1 state)"
        "Find_Max_Matching_ret_1_conds state \<Longrightarrow>
           Find_Max_Matching state = Find_Max_Matching_ret1 state"
  by (auto simp: Find_Max_Matching.psimps[OF assms] Find_Max_Matching_upd1_def
                 Find_Max_Matching_call_1_conds_def Find_Max_Matching_ret_1_conds_def)

lemma Find_Max_Matching_induct:
  assumes "Find_Max_Matching_dom state"
  assumes "\<And>state. \<lbrakk>Find_Max_Matching_dom state;
                     Find_Max_Matching_call_1_conds state \<Longrightarrow>
                       P (Find_Max_Matching_upd1 state)\<rbrakk>
                    \<Longrightarrow> P state"
  shows "P state"
  apply(rule Find_Max_Matching.pinduct[OF assms(1)])
  apply(rule assms(2))
  by (auto simp: Find_Max_Matching_call_1_conds_def Find_Max_Matching_upd1_def)

lemma Find_Max_Matching_domintros:
  assumes "Find_Max_Matching_call_1_conds state \<Longrightarrow>
             Find_Max_Matching_dom (Find_Max_Matching_upd1 state)"
  shows "Find_Max_Matching_dom state"
  using assms
  by (auto intro: Find_Max_Matching.domintros
           simp: Find_Max_Matching_call_1_conds_def Find_Max_Matching_upd1_def)

end

subsection \<open>Locale for the proofs\<close>

locale Find_Max_Matching_thms = Find_Max_Matching +
  assumes Find_Max_Matching_axiom: Find_Max_Matching_axiom
begin

lemma graph_input_G[simp]: "graph_input G vs"
  using Find_Max_Matching_axiom
  by (simp add: Find_Max_Matching_axiom_def)

lemma ugraph_abs_G[simp]: "graph_invar (ugraph_abs G)"
  by (rule ugraph_abs_graph_invar[OF graph_input_G])

lemma finite_ugraph_abs_G[simp]: "finite (ugraph_abs G)"
  using ugraph_abs_G
  by (simp add: finite_Vs_then_finite)

lemmas aug_path_search_props = aug_path_search[OF graph_input_G]

subsection \<open>The invariant\<close>

lemma invar_current_matching_props[invar_props_elims]:
  "\<lbrakk>invar_current_matching state; (matching_invar G (current_matching state) \<Longrightarrow> P) \<rbrakk> \<Longrightarrow> P"
  by (auto simp: invar_current_matching_def)

lemma invar_current_matching_intro[invar_props_intros]:
  "matching_invar G (current_matching state) \<Longrightarrow> invar_current_matching state"
  by (auto simp: invar_current_matching_def)

lemma invar_current_matching_holds_1[invar_holds_intros]:
  "\<lbrakk>Find_Max_Matching_call_1_conds state; invar_current_matching state\<rbrakk>
   \<Longrightarrow> invar_current_matching (Find_Max_Matching_upd1 state)"
proof(elim call_cond_elims invar_props_elims exE)
  fix p
  assume inv: "matching_invar G (current_matching state)"
    and result: "aug_path_search (current_matching state) = Some p"
  show ?thesis
    using Mate.augment(1)[OF matching_invar_props(1)[OF inv] aug_path_search_props(1)[OF inv result]]
    by (auto intro!: invar_props_intros simp: Find_Max_Matching_upd1_def matching_invar_def result)
qed

lemma invar_current_matching_holds[invar_holds_intros]:
  assumes "Find_Max_Matching_dom state" "invar_current_matching state"
  shows "invar_current_matching (Find_Max_Matching state)"
  using assms(2)
proof(induction rule: Find_Max_Matching_induct[OF assms(1)])
  case IH: (1 state)
  show ?case
    apply(rule Find_Max_Matching_cases[where state = state])
    by (auto intro: IH(2-) invar_holds_intros simp: Find_Max_Matching_simps[OF IH(1)])
qed

subsection \<open>Termination\<close>

named_theorems termination_intros

lemma call_1_terminates[termination_intros]:
  assumes "Find_Max_Matching_call_1_conds state" "invar_current_matching state"
  shows "(Find_Max_Matching_upd1 state, state) \<in> call_1_measure <*mlex*> r"
proof-
  obtain p where p: "aug_path_search (current_matching state) = Some p"
    using assms(1)
    by (auto elim!: call_cond_elims)
  have inv0: "matching_invar G (current_matching state)"
    using assms(2)
    by (auto elim!: invar_props_elims)
  have inv: "matching_invar_abs (ugraph_abs G) (current_matching state)"
    using inv0
    by (simp add: matching_invar_def)
  have aug: "graph_augmenting_path (ugraph_abs G) (matching_abs (current_matching state)) p"
    by (rule aug_path_search_props(1)[OF inv0 p])
  have less: "card (matching_abs (current_matching state))
                < card (matching_abs (mate_augment (current_matching state) p))"
    using aug matching_invar_props(4)[OF inv0 graph_input_G]
    by (simp add: Mate.augment(2)[OF inv aug] new_matching_bigger)
  have "matching_abs (mate_augment (current_matching state) p) \<subseteq> ugraph_abs G"
    using Mate.matching(1)[OF Mate.augment(1)[OF inv aug]]
    by simp
  hence "card (matching_abs (mate_augment (current_matching state) p)) \<le> card (ugraph_abs G)"
    by (intro card_mono) simp_all
  hence "call_1_measure (Find_Max_Matching_upd1 state) < call_1_measure state"
    using less p
    by (simp add: call_1_measure_def Find_Max_Matching_upd1_def)
  thus ?thesis
    by (rule mlex_less)
qed

lemma wf_term_rel: "wf Find_Max_Matching_term_rel'"
  by (auto simp: wf_mlex Find_Max_Matching_term_rel'_def)

lemma in_Find_Max_Matching_term_rel'[termination_intros]:
  "\<lbrakk>Find_Max_Matching_call_1_conds state; invar_current_matching state\<rbrakk> \<Longrightarrow>
     (Find_Max_Matching_upd1 state, state) \<in> Find_Max_Matching_term_rel'"
  by (simp add: Find_Max_Matching_term_rel'_def termination_intros)

lemma Find_Max_Matching_terminates[termination_intros]:
  assumes "invar_current_matching state"
  shows "Find_Max_Matching_dom state"
  using wf_term_rel assms
proof(induction rule: wf_induct_rule)
  case (less x)
  show ?case
    by (rule Find_Max_Matching_domintros)
       (auto intro: invar_holds_intros less in_Find_Max_Matching_term_rel')
qed

subsection \<open>Correctness\<close>

lemma Find_Max_Matching_correct_ret_1:
  "\<lbrakk>invar_current_matching state; Find_Max_Matching_ret_1_conds state\<rbrakk>
   \<Longrightarrow> max_card_matching (ugraph_abs G) (matching_abs (current_matching state))"
proof(elim invar_props_elims call_cond_elims)
  assume inv: "matching_invar G (current_matching state)"
     and none: "aug_path_search (current_matching state) = None"
  hence "\<nexists>p. graph_augmenting_path (ugraph_abs G) (matching_abs (current_matching state)) p"
    using aug_path_search_props(2)
    by blast
  moreover have "matching (matching_abs (current_matching state))"
                "matching_abs (current_matching state) \<subseteq> ugraph_abs G"
                "finite (matching_abs (current_matching state))"
    using matching_invar_props(2,3)[OF inv] matching_invar_props(4)[OF inv graph_input_G]
    by simp_all
  ultimately show ?thesis
    using Berge[of "matching_abs (current_matching state)" "ugraph_abs G"] ugraph_abs_G
    by (auto simp: max_card_matching_def not_le)
qed

lemma ret1_holds[ret_holds_intros]:
  assumes "Find_Max_Matching_dom state"
  shows "Find_Max_Matching_ret_1_conds (Find_Max_Matching state)"
proof(induction rule: Find_Max_Matching_induct[OF assms])
  case IH: (1 state)
  show ?case
    apply(rule Find_Max_Matching_cases[where state = state])
    by (auto intro!: IH(2-) simp: Find_Max_Matching_simps[OF IH(1)])
qed

subsection \<open>The initial state\<close>

lemma initial_state_props[invar_holds_intros, termination_intros]:
  "invar_current_matching initial_state" "Find_Max_Matching_dom initial_state"
proof-
  show "invar_current_matching initial_state"
    using Mate.matching(2)[of "ugraph_abs G"]
      Vs_ugraph_abs_subset_vs[OF graph_input_G] graph_inputD(7)[OF graph_input_G]
    by (auto intro!: invar_props_intros simp: initial_state_def matching_invar_def)
  thus "Find_Max_Matching_dom initial_state"
    by (rule Find_Max_Matching_terminates)
qed

lemma Find_Max_Matching_impl_to_Find_Max_Matching:
  "Find_Max_Matching_impl initial_state = Find_Max_Matching initial_state"
  by (auto intro!: Find_Max_Matching_impl_same initial_state_props)

subsection \<open>Final correctness\<close>

lemma Find_Max_Matching_correct_1:
  "max_card_matching (ugraph_abs G)
     (matching_abs (current_matching (Find_Max_Matching initial_state)))"
  apply(intro Find_Max_Matching_correct_ret_1[where state = "Find_Max_Matching initial_state"])
  by(auto intro: invar_holds_intros ret_holds_intros)

lemma Find_Max_Matching_correct_2:
  "matching_invar G (current_matching (Find_Max_Matching initial_state))"
  using invar_current_matching_holds[OF initial_state_props(2,1)]
  by (auto elim!: invar_props_elims)

end

end

