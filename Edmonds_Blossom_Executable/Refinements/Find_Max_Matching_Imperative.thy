theory Find_Max_Matching_Imperative
  imports
    Find_Aug_Path_Imperative
    Blossom_Executable.Find_Max_Matching
begin

provenance ai

section \<open>Imperative refinement of the top loop\<close>

text \<open>The imperative program mirrors @{const Find_Max_Matching.Find_Max_Matching_impl}. The current
  matching is a heap object that is augmented in place, so the state of the loop is the handle of
  the matching. The graph and the vertex list are given to the search procedure as a heap object
  and an array. The search procedure, which returns an optional path as an optional array, is a
  parameter; its Hoare triple, stated against the functional search, is an assumption of the
  refinement locale.\<close>

locale \<^marker>\<open>provenance ai_human\<close> Find_Max_Matching_Imperative_spec =
  fixes aug_path_search_imp :: "'gi \<Rightarrow> 'mi::heap \<Rightarrow> 'v::heap array \<Rightarrow> 'v array option Heap"
    and empty_matching_imp :: "'mi Heap"
    and augment_imp :: "'mi \<Rightarrow> 'v array \<Rightarrow> unit Heap"
begin

partial_function \<^marker>\<open>provenance ai_human\<close> (heap) Find_Max_Matching_imp :: "'gi \<Rightarrow> 'v array \<Rightarrow> 'mi \<Rightarrow> 'mi Heap" where
  "Find_Max_Matching_imp Gi Vi Mi =
     do { r \<leftarrow> aug_path_search_imp Gi Mi Vi;
          case r of
            Some Pt \<Rightarrow> do { augment_imp Mi Pt; Find_Max_Matching_imp Gi Vi Mi }
          | None \<Rightarrow> return Mi }"

definition \<^marker>\<open>provenance ai_human\<close> "Find_Max_Matching_run_imp Gi Vi =
  do { Mi \<leftarrow> empty_matching_imp;
       Find_Max_Matching_imp Gi Vi Mi }"

end

section \<open>Correctness of the imperative top loop\<close>

locale \<^marker>\<open>provenance ai_human\<close> Find_Max_Matching_Imperative =
  Find_Max_Matching_thms where lookup = lookup and mate_empty = mate_empty +
  Find_Max_Matching_Imperative_spec where aug_path_search_imp = aug_path_search_imp
    and empty_matching_imp = empty_matching_imp and augment_imp = augment_imp +
  mt: blossom_matching_imp where K = K and empty_matching = mate_empty
    and matching_invar = matching_invar_abs and lookup_partner = mate_lookup
    and get_partner = mate_partner and augment = mate_augment and matching_abstract = matching_abs
    and contract_path = mate_contract and expand_path_at_matched = mate_expand
    and add_alternatingly = mate_add_alternatingly and empty_matching_imp = empty_matching_imp
    and augment_imp = augment_imp and path_assn = "\<lambda>p Pt. Pt \<mapsto>\<^sub>a p"
  for lookup :: "'adjmap \<Rightarrow> 'v::heap \<Rightarrow> 'vset option"
    and mate_empty :: 'mate
    and aug_path_search_imp :: "'gi \<Rightarrow> 'mi::heap \<Rightarrow> 'v array \<Rightarrow> 'v array option Heap"
    and empty_matching_imp :: "'mi Heap"
    and augment_imp :: "'mi \<Rightarrow> 'v array \<Rightarrow> unit Heap" +
  fixes graph_assn :: "'adjmap \<Rightarrow> 'gi \<Rightarrow> assn"
  assumes aug_path_search_imp_rule:
    "\<And>M Gi Mi Vi. matching_invar G M \<Longrightarrow>
     <graph_assn G Gi * matching_assn M Mi * Vi \<mapsto>\<^sub>a vs> aug_path_search_imp Gi Mi Vi
     <\<lambda>r. graph_assn G Gi * matching_assn M Mi * Vi \<mapsto>\<^sub>a vs *
          path_opt_assn (aug_path_search M) r * true>"
begin

lemma aug_path_in_univ:
  assumes "graph_augmenting_path (ugraph_abs G) (matching_abs N) p"
  shows "set p \<subseteq> K"
proof-
  have "2 \<le> length p"
    using assms by (simp add: matching_augmenting_path_def)
  hence "set p \<subseteq> Vs (ugraph_abs G)"
    using assms by (intro subset_path_Vs) auto
  thus ?thesis
    using Vs_ugraph_abs_subset_vs[OF graph_input_G] graph_inputD(7)[OF graph_input_G] by blast
qed

lemma \<^marker>\<open>provenance ai_human\<close> Find_Max_Matching_imp_refine:
  "<graph_assn G Gi * Vi \<mapsto>\<^sub>a vs * matching_assn (current_matching s) Mi *
    \<up>(invar_current_matching s)>
     Find_Max_Matching_imp Gi Vi Mi
   <\<lambda>Mi'. graph_assn G Gi * Vi \<mapsto>\<^sub>a vs *
          matching_assn (current_matching (Find_Max_Matching_impl s)) Mi' * true>"
proof \<^marker>\<open>provenance ai\<close> (induction arbitrary: s Mi rule: Find_Max_Matching_imp.fixp_induct)
  case 1
  then show ?case
    by auto
next
  case 2
  then show ?case
    by simp
next
  case (3 f s Mi)
  show ?case
  proof(rule ht_extract_pre_pure(1), goal_cases)
    case 1
    hence inv: "matching_invar G (current_matching s)"
      by (simp add: invar_current_matching_def)
    note AS = aug_path_search_imp_rule[OF inv]
    show ?case
    proof(cases "aug_path_search (current_matching s)")
      case None
      have F: "Find_Max_Matching_impl s = s"
        by (subst Find_Max_Matching_impl.simps) (simp add: None)
      show ?thesis
        by (sep_auto heap: AS simp: None F path_opt_assn_def)
    next
      case (Some p)
      have aug: "graph_augmenting_path (ugraph_abs G) (matching_abs (current_matching s)) p"
        by (rule aug_path_search_props(1)[OF inv Some])
      have call: "Find_Max_Matching_call_1_conds s"
        using Some by (simp add: Find_Max_Matching_call_1_conds_def)
      define s' where "s' = Find_Max_Matching_upd1 s"
      have s': "current_matching s' = mate_augment (current_matching s) p"
        by (simp add: s'_def Find_Max_Matching_upd1_def Some)
      have inv': "invar_current_matching s'"
        unfolding s'_def by (rule invar_current_matching_holds_1[OF call 1])
      have F: "Find_Max_Matching_impl s = Find_Max_Matching_impl s'"
        by (subst Find_Max_Matching_impl.simps) (simp add: Some s'_def Find_Max_Matching_upd1_def)
      have IH: "<graph_assn G Gi * Vi \<mapsto>\<^sub>a vs * matching_assn (mate_augment (current_matching s) p) Mi>
                  f Gi Vi Mi
                <\<lambda>Mi'. graph_assn G Gi * Vi \<mapsto>\<^sub>a vs *
                       matching_assn (current_matching (Find_Max_Matching_impl s)) Mi' * true>"
        using 3[of s' Mi] inv' unfolding F s' by simp
      note AU = mt.augment_rule[OF inv[unfolded matching_invar_def] aug aug_path_in_univ[OF aug]]
      show ?thesis
        by (sep_auto heap: AS AU IH simp: Some path_opt_assn_def split: option.splits)
    qed
  qed
qed

theorem \<^marker>\<open>provenance ai_human\<close> Find_Max_Matching_run_imp_rule:
  "<graph_assn G Gi * Vi \<mapsto>\<^sub>a vs> Find_Max_Matching_run_imp Gi Vi
   <\<lambda>Mi. graph_assn G Gi * Vi \<mapsto>\<^sub>a vs *
        matching_assn (current_matching Find_Max_Matching_run_impl) Mi * true>"
proof \<^marker>\<open>provenance ai\<close>-
  have "<graph_assn G Gi * Vi \<mapsto>\<^sub>a vs * matching_assn (current_matching initial_state) Mi *
         \<up>(invar_current_matching initial_state)>
          Find_Max_Matching_imp Gi Vi Mi
        <\<lambda>Mi'. graph_assn G Gi * Vi \<mapsto>\<^sub>a vs *
               matching_assn (current_matching Find_Max_Matching_run_impl) Mi' * true>" for Mi
    by (rule Find_Max_Matching_imp_refine[of _ _ initial_state,
          folded Find_Max_Matching_run_impl_def])
  hence "<graph_assn G Gi * Vi \<mapsto>\<^sub>a vs * matching_assn mate_empty Mi>
          Find_Max_Matching_imp Gi Vi Mi
        <\<lambda>Mi'. graph_assn G Gi * Vi \<mapsto>\<^sub>a vs *
               matching_assn (current_matching Find_Max_Matching_run_impl) Mi' * true>" for Mi
    using initial_state_props(1) by (simp add: initial_state_def)
  thus ?thesis
    unfolding Find_Max_Matching_run_imp_def
    by (sep_auto heap: mt.empty_matching_rule)
qed

theorem \<^marker>\<open>provenance ai_human\<close> Find_Max_Matching_run_imp_correct:
  "<graph_assn G Gi * Vi \<mapsto>\<^sub>a vs> Find_Max_Matching_run_imp Gi Vi
   <\<lambda>Mi. \<exists>\<^sub>A N. graph_assn G Gi * Vi \<mapsto>\<^sub>a vs * matching_assn N Mi *
        \<up>(max_card_matching (ugraph_abs G) (matching_abs N) \<and> matching_invar G N) * true>"
  using \<^marker>\<open>provenance ai\<close> Find_Max_Matching_correct_1 Find_Max_Matching_correct_2
  by \<^marker>\<open>provenance ai\<close> (sep_auto heap: Find_Max_Matching_run_imp_rule
      simp: Find_Max_Matching_run_impl_def Find_Max_Matching_impl_to_Find_Max_Matching)

end

end
