theory Edmonds_Blossom_Imperative
  imports
    Compute_Alt_Path_Imperative
    Find_Aug_Path_Subprocedures_Imperative
    Find_Max_Matching_Imperative
begin

provenance ai_human

section \<open>The imperative blossom algorithm\<close>

text \<open>The imperative layers are put together as the functional ones are: the alternating forest
  search (@{locale Compute_Alt_Path_Imperative}) is the search of the computation of a path or a
  blossom (@{locale Find_Aug_Path_Subprocedures_Imperative}), which is the search of the search by
  shrinking blossoms (@{locale Find_Aug_Path_Imperative}), which is the search of the top loop
  (@{locale Find_Max_Matching_Imperative}).

  The locale below fixes the functional data structures, the imperative ADTs (the queue of the
  forest search and the stack of contractions as bounded stacks, the sets of the forest search,
  the alternating forest and the matching, both with paths as arrays), the operations on graphs
  and the creation of a vertex with their Hoare triples, and the input. The functional and the
  imperative layers are composed by sublocales; the lower layers are instantiated for every graph,
  vertex list and matching they are called with.\<close>

locale Edmonds_Blossom_Imperative =
  Graph_Matching_Specs where lookup = lookup and mate_empty = mate_empty +
  fs: fixed_univ_set_imp K fset_invar fset_to_set fset_empty fset_insert fset_delete fset_isin
    fset_assn fset_empty_imp fset_insert_imp fset_delete_imp fset_isin_imp +
  fr: alternating_forest_imp where evens = evens and odds = odds and roots = roots
    and get_path = get_path and abstract_forest = abstract_forest and forest_invar = forest_invar
    and vset_invar = fset_invar and vset_to_set = fset_to_set
    and extend_forest_even_unclassified = extend_forest_even_unclassified
    and empty_forest = empty_forest and forest_univ = K and vset_empty = fset_empty
    and vset_assn = fset_assn and path_assn = "\<lambda>p Pt. Pt \<mapsto>\<^sub>a p" +
  mt: blossom_matching_imp where K = K and empty_matching = mate_empty
    and matching_invar = matching_invar_abs and lookup_partner = mate_lookup
    and get_partner = mate_partner and augment = mate_augment and matching_abstract = matching_abs
    and contract_path = mate_contract and expand_path_at_matched = mate_expand
    and add_alternatingly = mate_add_alternatingly and path_assn = "\<lambda>p Pt. Pt \<mapsto>\<^sub>a p"
    and matching_assn = matching_assn +
  q: bounded_stack_imp q_cap q_invar q_abstract q_empty q_push q_pop q_top q_is_empty
    q_assn q_empty_imp q_push_imp q_pop_imp q_top_imp q_is_empty_imp +
  cs: bounded_stack_imp cs_cap cs_invar cs_abstract cs_empty cs_push cs_pop cs_top cs_is_empty
    cs_assn cs_empty_imp cs_push_imp cs_pop_imp cs_top_imp cs_is_empty_imp
  for lookup :: "'adjmap \<Rightarrow> 'v::heap \<Rightarrow> 'vset option"
    and mate_empty :: 'mate
    and matching_assn :: "'mate \<Rightarrow> 'mi::heap \<Rightarrow> assn"
    and fset_invar :: "'fset \<Rightarrow> bool"
    and fset_to_set fset_empty fset_insert fset_delete fset_isin
    and fset_assn :: "'fset \<Rightarrow> 'fseti \<Rightarrow> assn"
    and fset_empty_imp fset_insert_imp fset_delete_imp fset_isin_imp
    and evens odds roots :: "'forest \<Rightarrow> 'fset"
    and get_path abstract_forest forest_invar extend_forest_even_unclassified empty_forest
    and q_cap q_invar
    and q_abstract :: "'q \<Rightarrow> 'v list"
    and q_empty q_push q_pop q_top q_is_empty
    and q_assn :: "'q \<Rightarrow> 'qi \<Rightarrow> assn"
    and q_empty_imp q_push_imp q_pop_imp q_top_imp q_is_empty_imp
    and cs_cap cs_invar
    and cs_abstract :: "'cs \<Rightarrow> ('gi::heap \<times> 'mi::heap \<times> 'v array \<times> 'v) list"
    and cs_empty cs_push cs_pop cs_top cs_is_empty
    and cs_assn :: "'cs \<Rightarrow> 'csi \<Rightarrow> assn"
    and cs_empty_imp cs_push_imp cs_pop_imp cs_top_imp cs_is_empty_imp +
  fixes graph_assn :: "'adjmap \<Rightarrow> 'gi \<Rightarrow> assn"
    and g_empty_imp :: "'gi Heap"
    and g_add_edge_imp :: "'gi \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'gi Heap"
    and neighbours_imp :: "'gi \<Rightarrow> 'v \<Rightarrow> 'v array Heap"
    and g_isin_imp :: "'gi \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool Heap"
    and create_vert :: "'v list \<Rightarrow> 'v"
    and create_vert_imp :: "'v array \<Rightarrow> 'v Heap"
    and G :: 'adjmap and vs :: "'v list"
  assumes g_empty_rule: "<emp> g_empty_imp <\<lambda>Hi. graph_assn empty Hi>"
    and g_add_edge_rule:
      "\<And>H Hi a b. <graph_assn H Hi> g_add_edge_imp Hi a b
                  <\<lambda>Hi'. graph_assn (Graph.add_edge H a b) Hi'>"
    and neighbours_rule:
      "\<And>H Gi v. \<lbrakk>Graph.graph_inv H; v \<in> K\<rbrakk> \<Longrightarrow>
       <graph_assn H Gi> neighbours_imp Gi v <\<lambda>A. graph_assn H Gi * A \<mapsto>\<^sub>a neighbour_list H v>"
    and g_isin_rule:
      "\<And>H Gi v w. \<lbrakk>Graph.graph_inv H; v \<in> K; w \<in> K\<rbrakk> \<Longrightarrow>
       <graph_assn H Gi> g_isin_imp Gi v w
       <\<lambda>r. graph_assn H Gi * \<up>(r = isin (Graph.neighbourhood H v) w)>"
    and create_vert: "\<And>ws. set ws \<subset> K \<Longrightarrow> create_vert ws \<notin> set ws"
    and create_vert_in_univ: "\<And>ws. set ws \<subset> K \<Longrightarrow> create_vert ws \<in> K"
    and create_vert_imp_rule:
      "\<And>ws Wi. set ws \<subset> K \<Longrightarrow>
       <Wi \<mapsto>\<^sub>a ws> create_vert_imp Wi <\<lambda>u. Wi \<mapsto>\<^sub>a ws * \<up>(u = create_vert ws)>"
    and graph_input: "graph_input G vs"
    and vs_strict: "set vs \<subset> K"
    and queue_capacity: "2 * length vs \<le> q_cap"
    and contractions_capacity: "length vs \<le> cs_cap"
begin

subsection \<open>The functional algorithm\<close>

text \<open>The functional layers, composed as in the executable instantiation.\<close>

sublocale cap: Compute_Alt_Path where G = H and vs = ws and M = N for H ws N
  by unfold_locales

sublocale fsub: Find_Aug_Path_subprocedures where compute_alt_path = cap.Compute_Alt_Path_run_impl
proof(unfold_locales, goal_cases)
  case (1 H ws N)
  thus ?case
    by (intro cap.Compute_Alt_Path_run_impl_correct(1)) (simp only: cap.Compute_Alt_Path_axiom_def; blast)
next
  case (2 H ws N)
  thus ?case
    by (intro cap.Compute_Alt_Path_run_impl_correct(2)) (simp only: cap.Compute_Alt_Path_axiom_def; blast)+
qed

sublocale fap: Find_Aug_Path where G = H and vs = ws and M = N
  and blos_search = fsub.compute_match_blossom and create_vert = create_vert for H ws N
  by unfold_locales
     ((rule fsub.compute_match_blossom; assumption) | (rule create_vert create_vert_in_univ; assumption))+

sublocale fmm: Find_Max_Matching where aug_path_search = "fap.Find_Aug_Path_run_impl G vs"
proof(unfold_locales, goal_cases)
  case (1 N p)
  thus ?case
    by (intro fap.Find_Aug_Path_run_impl_correct(1)) (simp only: fap.Find_Aug_Path_axiom_def; blast)+
next
  case (2 N)
  thus ?case
    by (intro fap.Find_Aug_Path_run_impl_correct(2)) (simp only: fap.Find_Aug_Path_axiom_def; blast)+
qed

sublocale fmm_thms: Find_Max_Matching_thms where aug_path_search = "fap.Find_Aug_Path_run_impl G vs"
  by unfold_locales (simp only: fmm.Find_Max_Matching_axiom_def; intro conjI graph_input vs_strict)

subsection \<open>The imperative algorithm\<close>

sublocale cap_imp: Compute_Alt_Path_Imperative_spec q_empty_imp q_push_imp q_pop_imp q_top_imp
  q_is_empty_imp fset_empty_imp fset_insert_imp empty_forest_imp evens_isin_imp odds_isin_imp
  extend_forest_even_unclassified_imp get_path_imp lookup_partner_imp neighbours_imp .

sublocale fsub_imp: Find_Aug_Path_Subprocedures_Imperative_spec cap_imp.Compute_Alt_Path_run_imp .

sublocale fap_imp: Find_Aug_Path_Imperative_spec fsub_imp.compute_match_blossom_imp create_vert_imp
  g_empty_imp g_add_edge_imp neighbours_imp g_isin_imp lookup_partner_imp copy_matching_imp
  contract_path_imp cs_empty_imp cs_push_imp cs_pop_imp cs_top_imp cs_is_empty_imp .

sublocale fmm_imp: Find_Max_Matching_Imperative_spec fap_imp.Find_Aug_Path_run_imp
  empty_matching_imp augment_imp .

text \<open>The imperative blossom algorithm, for the graph and the vertex list given as a heap object
  and an array.\<close>

definition "edmonds_blossom_imp Gi Vi = fmm_imp.Find_Max_Matching_run_imp Gi Vi"

subsection \<open>Correctness of the layers\<close>

text \<open>The alternating forest search, for a graph whose vertex list is at most as long as that of
  the input.\<close>

lemma compute_alt_path_imp_rule:
  assumes "graph_input H ws" "matching_invar H N" "length ws \<le> length vs"
  shows "<graph_assn H Gi * matching_assn N Mi * Wi \<mapsto>\<^sub>a ws> cap_imp.Compute_Alt_Path_run_imp Gi Mi Wi
         <\<lambda>r. graph_assn H Gi * matching_assn N Mi * Wi \<mapsto>\<^sub>a ws *
              alt_paths_assn (cap.Compute_Alt_Path_run_impl H ws N) r * true>"
proof-
  interpret I: Compute_Alt_Path_Imperative where G = H and vs = ws and M = N
    and cap = q_cap and stack_invar = q_invar and stack_abstract = q_abstract
    and stack_empty = q_empty and stack_push = q_push and stack_pop = q_pop and stack_top = q_top
    and stack_is_empty = q_is_empty and stack_assn = q_assn and stack_empty_imp = q_empty_imp
    and stack_push_imp = q_push_imp and stack_pop_imp = q_pop_imp and stack_top_imp = q_top_imp
    and stack_is_empty_imp = q_is_empty_imp
    and fixed_univ_set_delete_imp = fset_delete_imp and fixed_univ_set_isin_imp = fset_isin_imp
    and path_assn = "\<lambda>p Pt. Pt \<mapsto>\<^sub>a p"
  proof(unfold_locales, goal_cases)
    case (1 H' Gi' v)
    thus ?case
      by (rule neighbours_rule)
  next
    case 2
    show ?case
      using assms(1,2) by (simp only: cap.Compute_Alt_Path_axiom_def; blast)
  next
    case 3
    show ?case
      using assms(3) queue_capacity by linarith
  qed
  have eq: "I.paths_res_assn = alt_paths_assn"
    by (intro ext) (simp add: I.paths_res_assn_def alt_paths_assn_def)
  show ?thesis
    using I.Compute_Alt_Path_run_imp_rule unfolding eq .
qed

text \<open>The computation of a path or a blossom.\<close>

sublocale fsub_proofs: Find_Aug_Path_Subprocedures_Imperative
  where compute_alt_path = cap.Compute_Alt_Path_run_impl
    and compute_alt_path_imp = cap_imp.Compute_Alt_Path_run_imp and max_vertices = "length vs"
  by unfold_locales (rule compute_alt_path_imp_rule)

text \<open>The search by shrinking blossoms, for the input graph and every matching.\<close>

lemma find_aug_path_imp_rule:
  assumes "matching_invar G N"
  shows "<graph_assn G Gi * matching_assn N Mi * Vi \<mapsto>\<^sub>a vs> fap_imp.Find_Aug_Path_run_imp Gi Mi Vi
         <\<lambda>r. graph_assn G Gi * matching_assn N Mi * Vi \<mapsto>\<^sub>a vs *
              path_opt_assn (fap.Find_Aug_Path_run_impl G vs N) r * true>"
proof-
  interpret I: Find_Aug_Path_Imperative where G = G and vs = vs and M = N
    and blos_search = fsub.compute_match_blossom and create_vert = create_vert
    and blos_search_imp = fsub_imp.compute_match_blossom_imp
    and cap = cs_cap and stack_invar = cs_invar and stack_abstract = cs_abstract
    and stack_empty = cs_empty and stack_push = cs_push and stack_pop = cs_pop and stack_top = cs_top
    and stack_is_empty = cs_is_empty and stack_assn = cs_assn and stack_empty_imp = cs_empty_imp
    and stack_push_imp = cs_push_imp and stack_pop_imp = cs_pop_imp and stack_top_imp = cs_top_imp
    and stack_is_empty_imp = cs_is_empty_imp
    and max_vertices = "length vs"
  proof(unfold_locales, goal_cases)
    case (1 H ws N' Gi' Mi' Wi)
    thus ?case
      by (rule fsub_proofs.compute_match_blossom_imp_rule)
  next
    case (2 ws Wi)
    thus ?case
      by (rule create_vert_imp_rule)
  next
    case 3
    show ?case
      by (rule g_empty_rule)
  next
    case (4 H Hi a b)
    show ?case
      by (rule g_add_edge_rule)
  next
    case (5 H Gi' v)
    thus ?case
      by (rule neighbours_rule)
  next
    case (6 H Gi' v w)
    thus ?case
      by (rule g_isin_rule)
  next
    case 7
    show ?case
      by (simp only: fap.Find_Aug_Path_axiom_def; intro conjI graph_input assms vs_strict)
  next
    case 8
    show ?case
      by (rule order_refl)
  next
    case 9
    show ?case
      by (rule contractions_capacity)
  qed
  show ?thesis
    by (rule I.Find_Aug_Path_run_imp_rule)
qed

text \<open>The top loop.\<close>

sublocale fmm_proofs: Find_Max_Matching_Imperative
  where aug_path_search = "fap.Find_Aug_Path_run_impl G vs"
    and aug_path_search_imp = fap_imp.Find_Aug_Path_run_imp
  by unfold_locales (rule find_aug_path_imp_rule)

subsection \<open>Correctness of the imperative algorithm\<close>

text \<open>The imperative algorithm computes the matching of the functional algorithm.\<close>

theorem edmonds_blossom_imp_refine:
  "<graph_assn G Gi * Vi \<mapsto>\<^sub>a vs> edmonds_blossom_imp Gi Vi
   <\<lambda>Mi. graph_assn G Gi * Vi \<mapsto>\<^sub>a vs *
        matching_assn (current_matching fmm.Find_Max_Matching_run_impl) Mi * true>"
  unfolding edmonds_blossom_imp_def
  by (rule fmm_proofs.Find_Max_Matching_run_imp_rule)

text \<open>The imperative algorithm computes a maximum cardinality matching of the input graph.\<close>

theorem edmonds_blossom_imp_correct:
  "<graph_assn G Gi * Vi \<mapsto>\<^sub>a vs> edmonds_blossom_imp Gi Vi
   <\<lambda>Mi. \<exists>\<^sub>A N. graph_assn G Gi * Vi \<mapsto>\<^sub>a vs * matching_assn N Mi *
        \<up>(max_card_matching (ugraph_abs G) (matching_abs N) \<and> matching_invar G N) * true>"
  unfolding edmonds_blossom_imp_def
  by (rule fmm_proofs.Find_Max_Matching_run_imp_correct)

end

end
