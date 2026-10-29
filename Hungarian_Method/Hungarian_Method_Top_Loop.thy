(*
  Author: Thomas Ammer
*)

theory Hungarian_Method_Top_Loop
  imports
    Matching_LPs.Matching_LP
    Path_Search_Result
    Basic_Matching.Matching_Augmentation_Executable
begin

provenance human

section \<open>Top Loop for Hungarian Method\<close>

no_translations
  "_Collect p P"      <= "{p. P}"
  "_Collect p P"      <= "{p|xs. P}"

datatype result = success | failure | notyetterm

text \<open>A path search returns a result, a new matching (of the same size), a new potential and a
      new search context. The context is opaque to the top loop: it is only handed back to the
      next path search. A search may use it to remember where to continue.\<close>

record ('buddy, 'potential, 'ctx) hungarian_state = 
     buddies::'buddy
     potential::'potential
     search_ctx::'ctx
     result::result

subsection \<open>Locale for Implementation\<close>

locale hungarian_loop_spec =
fixes potential_abstract::"'potential \<Rightarrow> 'v \<Rightarrow> real"
   and init_potential::'potential
   and potential_invar::"'potential \<Rightarrow> bool"

   and empty_matching::'matching
   and matching_invar::"'matching \<Rightarrow> bool"
   and augment::"'matching \<Rightarrow> 'v list \<Rightarrow> 'matching"
   and matching_abstract::"'matching \<Rightarrow> 'v set set"

   and edge_costs::"'v set \<Rightarrow> real"

   and card_L card_R::nat
   and path_search::"'ctx \<Rightarrow> 'matching \<Rightarrow> 'potential \<Rightarrow> 
                      'v path_search_result \<times> 'matching \<times> 'potential \<times> 'ctx"
   and init_ctx::'ctx
   and G::"'v set set"
begin

function (domintros) hungarian_loop::
   "('matching, 'potential, 'ctx) hungarian_state \<Rightarrow> ('matching, 'potential, 'ctx) hungarian_state"
   where "hungarian_loop state =
     (case path_search (search_ctx state) (buddies state) (potential state) of
       (r, M', \<pi>', c') \<Rightarrow>
       (case r of
          Dual_Unbounded \<Rightarrow>
            state \<lparr>buddies:=M', potential := \<pi>', search_ctx := c', result:=failure\<rparr>
        | Lefts_Matched \<Rightarrow>
            state \<lparr>buddies:=M', potential := \<pi>', search_ctx := c', result:=success\<rparr>
        | Next_Iteration P \<Rightarrow>
            hungarian_loop (state \<lparr>buddies:=augment M' P, potential := \<pi>', search_ctx := c'\<rparr>)))"
  by pat_completeness auto

partial_function (tailrec) hungarian_loop_impl::
   "('matching, 'potential, 'ctx) hungarian_state \<Rightarrow> ('matching, 'potential, 'ctx) hungarian_state"
   where "hungarian_loop_impl state =
     (case path_search (search_ctx state) (buddies state) (potential state) of
       (r, M', \<pi>', c') \<Rightarrow>
       (case r of
          Dual_Unbounded \<Rightarrow>
            state \<lparr>buddies:=M', potential := \<pi>', search_ctx := c', result:=failure\<rparr>
        | Lefts_Matched \<Rightarrow>
            state \<lparr>buddies:=M', potential := \<pi>', search_ctx := c', result:=success\<rparr>
        | Next_Iteration P \<Rightarrow>
            hungarian_loop_impl (state \<lparr>buddies:=augment M' P, potential := \<pi>', search_ctx := c'\<rparr>)))"

definition "initial_state = \<lparr>buddies = empty_matching, potential = init_potential,
                             search_ctx = init_ctx, result = notyetterm\<rparr>"

definition "hungarian = 
  (if card_L \<noteq> card_R then None
   else
   let final_state = hungarian_loop_impl initial_state
   in (case result final_state 
        of failure \<Rightarrow> None
       | success \<Rightarrow> Some (buddies final_state)))"

lemmas [code] = hungarian_loop_impl.simps initial_state_def hungarian_def

lemma hungarian_loop_impl_same:
  assumes "hungarian_loop_dom state"
  shows   "hungarian_loop_impl state = hungarian_loop state"
  apply(induction rule: hungarian_loop.pinduct[OF assms])
  apply(subst hungarian_loop_impl.simps)
  apply(subst hungarian_loop.psimps)
  by(auto split: path_search_result.splits prod.splits)

definition "search_of state = path_search (search_ctx state) (buddies state) (potential state)"

definition  "hungarian_loop_upd state =
     (case search_of state of (r, M', \<pi>', c') \<Rightarrow>
        state \<lparr>buddies:=augment M' (the_path r), potential := \<pi>', search_ctx := c'\<rparr>)"

definition  "hungarian_loop_fail state =
     (case search_of state of (r, M', \<pi>', c') \<Rightarrow>
        state \<lparr>buddies:=M', potential := \<pi>', search_ctx := c', result:=failure\<rparr>)"

definition  "hungarian_loop_succ state =
     (case search_of state of (r, M', \<pi>', c') \<Rightarrow>
        state \<lparr>buddies:=M', potential := \<pi>', search_ctx := c', result:=success\<rparr>)"

definition  "hungarian_loop_fail_cond state = (fst (search_of state) = Dual_Unbounded)"

definition  "hungarian_loop_succ_cond state = (fst (search_of state) = Lefts_Matched)"

definition  "hungarian_loop_cont_cond state = (\<exists> p. fst (search_of state) = Next_Iteration p)"

lemma hungarian_loop_fail_condE:
  "\<lbrakk>hungarian_loop_fail_cond state;
    \<And> M' \<pi>' c'. search_of state = (Dual_Unbounded, M', \<pi>', c') \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by(cases "search_of state") (auto simp add: hungarian_loop_fail_cond_def)

lemma hungarian_loop_succ_condE:
  "\<lbrakk>hungarian_loop_succ_cond state;
    \<And> M' \<pi>' c'. search_of state = (Lefts_Matched, M', \<pi>', c') \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by(cases "search_of state") (auto simp add: hungarian_loop_succ_cond_def)

lemma hungarian_loop_cont_condE:
  "\<lbrakk>hungarian_loop_cont_cond state;
    \<And> p M' \<pi>' c'. search_of state = (Next_Iteration p, M', \<pi>', c') \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by(cases "search_of state") (auto simp add: hungarian_loop_cont_cond_def)

lemma hungarian_loop_cases:
  assumes "hungarian_loop_fail_cond state \<Longrightarrow> P"
          "hungarian_loop_succ_cond state \<Longrightarrow> P"
          "hungarian_loop_cont_cond state \<Longrightarrow> P"
    shows P
  using assms
  by(cases "fst (search_of state)")
    (auto simp add: hungarian_loop_fail_cond_def 
                    hungarian_loop_cont_cond_def
                    hungarian_loop_succ_cond_def)

lemma hungarian_loop_domintros:
  "hungarian_loop_fail_cond state \<Longrightarrow> hungarian_loop_dom state"
  "hungarian_loop_succ_cond state \<Longrightarrow> hungarian_loop_dom state"
  "\<lbrakk>hungarian_loop_cont_cond state; hungarian_loop_dom (hungarian_loop_upd state)\<rbrakk>
    \<Longrightarrow> hungarian_loop_dom state"
    apply(all \<open>rule hungarian_loop.domintros\<close>)
    apply(all \<open>cases "path_search (search_ctx state) (buddies state) (potential state)"\<close>)
    by(auto simp add: hungarian_loop_fail_cond_def 
                      hungarian_loop_cont_cond_def
                      hungarian_loop_succ_cond_def
                      hungarian_loop_upd_def search_of_def)

lemma hungarian_loop_simps:
 "hungarian_loop_fail_cond state \<Longrightarrow> hungarian_loop state = hungarian_loop_fail state"
 "hungarian_loop_succ_cond state \<Longrightarrow> hungarian_loop state = hungarian_loop_succ state"
 "\<lbrakk>hungarian_loop_cont_cond state; hungarian_loop_dom state\<rbrakk>
   \<Longrightarrow> hungarian_loop state = hungarian_loop (hungarian_loop_upd state)"
  by(auto simp add: hungarian_loop.psimps[OF hungarian_loop_domintros(1)] 
                    hungarian_loop.psimps[OF hungarian_loop_domintros(2)] 
                    hungarian_loop.psimps  hungarian_loop_upd_def
                    hungarian_loop_fail_def hungarian_loop_succ_def
            elim!: hungarian_loop_fail_condE hungarian_loop_succ_condE
                   hungarian_loop_cont_condE)
     (auto simp add: search_of_def)

lemma hungarian_loop_induct:
  assumes "hungarian_loop_dom state"
          "\<And> state. \<lbrakk>hungarian_loop_dom state;
                      hungarian_loop_cont_cond state \<Longrightarrow> P (hungarian_loop_upd state)\<rbrakk>
                     \<Longrightarrow> P state"
    shows "P state"
proof(induction rule: hungarian_loop.pinduct[OF assms(1)])
  case (1 state)
  note IH = this
  show ?case 
  proof(rule assms(2)[OF IH(1)], goal_cases)
    case 1
    then obtain p M' \<pi>' c' where "search_of state = (Next_Iteration p, M', \<pi>', c')"
      by(auto elim!: hungarian_loop_cont_condE)
    thus ?case 
      by(auto intro!: IH(2) simp add: hungarian_loop_upd_def search_of_def)
  qed
qed

definition "path_search_precond M \<pi> =
  (matching_invar M \<and> potential_invar \<pi> \<and> graph_matching G (matching_abstract M) \<and>
  matching_abstract M \<subseteq> tight_subgraph G edge_costs (potential_abstract \<pi>) \<and>
  feasible_min_perfect_dual G edge_costs (potential_abstract \<pi>))"

lemma path_search_precondI:
  "\<lbrakk>matching_invar M; potential_invar \<pi>;
    matching_abstract M \<subseteq> tight_subgraph G edge_costs (potential_abstract \<pi>);
    graph_matching G (matching_abstract M);
    feasible_min_perfect_dual G edge_costs (potential_abstract \<pi>)\<rbrakk>
   \<Longrightarrow> path_search_precond M \<pi>"
and path_search_precondE:
  "path_search_precond M \<pi> \<Longrightarrow>
   (\<lbrakk>matching_invar M; potential_invar \<pi>;
     matching_abstract M \<subseteq> tight_subgraph G edge_costs (potential_abstract \<pi>);
     graph_matching G (matching_abstract M);
     feasible_min_perfect_dual G edge_costs (potential_abstract \<pi>)\<rbrakk> \<Longrightarrow> P)
   \<Longrightarrow> P"
and path_search_precondD:
  "path_search_precond M \<pi> \<Longrightarrow> matching_invar M"
  "path_search_precond M \<pi> \<Longrightarrow> potential_invar \<pi>"
  "path_search_precond M \<pi> \<Longrightarrow> graph_matching G (matching_abstract M)"
  "path_search_precond M \<pi> \<Longrightarrow> 
     matching_abstract M \<subseteq> tight_subgraph G edge_costs (potential_abstract \<pi>)"
  "path_search_precond M \<pi> \<Longrightarrow> 
     feasible_min_perfect_dual G edge_costs (potential_abstract \<pi>)"
  by(auto simp add: path_search_precond_def)

definition "good_search_result M \<pi>' p =
        (potential_invar \<pi>' \<and> 
        matching_abstract M \<subseteq> tight_subgraph G edge_costs (potential_abstract \<pi>') \<and>
        feasible_min_perfect_dual G edge_costs (potential_abstract \<pi>') \<and> 
        set (edges_of_path p) \<subseteq> tight_subgraph G edge_costs (potential_abstract \<pi>') \<and>
        graph_augmenting_path G (matching_abstract M) p)"

lemma good_search_resultE:
  "good_search_result M \<pi>' p \<Longrightarrow>
   (\<lbrakk>potential_invar \<pi>'; 
     matching_abstract M \<subseteq> tight_subgraph G edge_costs (potential_abstract \<pi>');
     feasible_min_perfect_dual G edge_costs (potential_abstract \<pi>'); 
     set (edges_of_path p) \<subseteq> tight_subgraph G edge_costs (potential_abstract \<pi>');
     graph_augmenting_path G (matching_abstract M) p\<rbrakk> 
    \<Longrightarrow> P)
   \<Longrightarrow> P"
and good_search_resultI:
  "\<lbrakk>potential_invar \<pi>'; 
    matching_abstract M \<subseteq> tight_subgraph G edge_costs (potential_abstract \<pi>');
    feasible_min_perfect_dual G edge_costs (potential_abstract \<pi>'); 
    set (edges_of_path p) \<subseteq> tight_subgraph G edge_costs (potential_abstract \<pi>');
    graph_augmenting_path G (matching_abstract M) p\<rbrakk> 
   \<Longrightarrow> good_search_result M \<pi>' p"
and good_search_resultD:
  "good_search_result M \<pi>' p \<Longrightarrow> potential_invar \<pi>'"
  "good_search_result M \<pi>' p \<Longrightarrow> 
     matching_abstract M \<subseteq> tight_subgraph G edge_costs (potential_abstract \<pi>')"
  "good_search_result M \<pi>' p \<Longrightarrow> 
    feasible_min_perfect_dual G edge_costs (potential_abstract \<pi>')"
  "good_search_result M \<pi>' p \<Longrightarrow>
    set (edges_of_path p) \<subseteq> tight_subgraph G edge_costs (potential_abstract \<pi>')"
  "good_search_result M \<pi>' p \<Longrightarrow> graph_augmenting_path G (matching_abstract M) p"
  by(auto simp add: good_search_result_def)

text \<open>The contract of a path search. It returns a matching of the same size and a potential that
      satisfy the precondition again, together with a certificate for the result: unboundedness
      of the dual, all left vertices matched, or a tight augmenting path.\<close>

definition "good_search (L::'v set) R M res =
  (case res of (r, M', \<pi>') \<Rightarrow>
     path_search_precond M' \<pi>' \<and>
     card (matching_abstract M') = card (matching_abstract M) \<and>
     (case r of
        Dual_Unbounded \<Rightarrow>
          (\<forall> B. \<exists> \<pi>''. feasible_min_perfect_dual G edge_costs \<pi>'' \<and> sum \<pi>'' (L \<union> R) > B)
      | Lefts_Matched \<Rightarrow> L \<subseteq> Vs (matching_abstract M')
      | Next_Iteration p \<Rightarrow> good_search_result M' \<pi>' p))"

lemma good_searchD:
  assumes "good_search L R M (r, M', \<pi>')"
  shows "path_search_precond M' \<pi>'"
        "card (matching_abstract M') = card (matching_abstract M)"
        "r = Dual_Unbounded \<Longrightarrow> 
           \<forall> B. \<exists> \<pi>''. feasible_min_perfect_dual G edge_costs \<pi>'' \<and> sum \<pi>'' (L \<union> R) > B"
        "r = Lefts_Matched \<Longrightarrow> L \<subseteq> Vs (matching_abstract M')"
        "r = Next_Iteration p \<Longrightarrow> good_search_result M' \<pi>' p"
  using assms by(auto simp add: good_search_def)

lemma good_searchI:
  "\<lbrakk>path_search_precond M' \<pi>';
    card (matching_abstract M') = card (matching_abstract M);
    r = Dual_Unbounded \<Longrightarrow> 
       \<forall> B. \<exists> \<pi>''. feasible_min_perfect_dual G edge_costs \<pi>'' \<and> sum \<pi>'' (L \<union> R) > B;
    r = Lefts_Matched \<Longrightarrow> L \<subseteq> Vs (matching_abstract M');
    \<And> p. r = Next_Iteration p \<Longrightarrow> good_search_result M' \<pi>' p\<rbrakk>
   \<Longrightarrow> good_search L R M (r, M', \<pi>')"
  by(cases r) (auto simp add: good_search_def)

end

subsection \<open>Locale for Proofs\<close>

locale hungarian_loop = 
 hungarian_loop_spec where edge_costs = edge_costs
for edge_costs::"'v set \<Rightarrow> real" +
fixes L R ctx_invar
assumes G: 
   "bipartite G L R"
   "card_L = card L"
   "card_R = card R"
   "finite L"
   "finite R"
   "L \<union> R \<subseteq> Vs G" 
and potential:
 "potential_invar init_potential"
 "feasible_min_perfect_dual G edge_costs (potential_abstract init_potential)"
and matching:
  "\<And> M. matching_invar M \<Longrightarrow> graph_matching G (matching_abstract M)"
  "matching_invar empty_matching"
  "matching_abstract empty_matching = {}"
and augment:
  "\<And> M p. \<lbrakk>matching_invar M; graph_augmenting_path G (matching_abstract M) p\<rbrakk> \<Longrightarrow> 
         matching_invar (augment M p)"
  "\<And> M p. \<lbrakk>matching_invar M; graph_augmenting_path G (matching_abstract M) p\<rbrakk> \<Longrightarrow> 
         matching_abstract (augment M p) =  matching_abstract M \<oplus> set (edges_of_path p)"
and path_search:
  "\<And> c M \<pi> r M' \<pi>' c'. 
     \<lbrakk>path_search_precond M \<pi>; ctx_invar c; path_search c M \<pi> = (r, M', \<pi>', c')\<rbrakk>
     \<Longrightarrow> good_search L R M (r, M', \<pi>')"
  "\<And> c M \<pi> r M' \<pi>' c'. 
     \<lbrakk>path_search_precond M \<pi>; ctx_invar c; path_search c M \<pi> = (r, M', \<pi>', c')\<rbrakk>
     \<Longrightarrow> ctx_invar c'"
and init_ctx: "ctx_invar init_ctx"
begin

lemma graph_matching_finite: "graph_matching G M \<Longrightarrow> finite M" 
  using  finite_Vs_then_finite[of M] finite_parts_bipartite_graph_invar[OF G(4,5,1)]
      graph_invar_subset
  by auto

subsection \<open>Invariant Setup\<close>

definition "state_invar state = 
  (path_search_precond (buddies state) (potential state) \<and> ctx_invar (search_ctx state))"

lemma state_invarI:
  "\<lbrakk>path_search_precond (buddies state) (potential state); ctx_invar (search_ctx state)\<rbrakk>
   \<Longrightarrow> state_invar state"
and state_invarD:
  "state_invar state \<Longrightarrow> path_search_precond (buddies state) (potential state)"
  "state_invar state \<Longrightarrow> ctx_invar (search_ctx state)"
  by(auto simp add: state_invar_def)

lemma search_of_props:
  assumes "state_invar state" "search_of state = (r, M', \<pi>', c')"
  shows "good_search L R (buddies state) (r, M', \<pi>')" "ctx_invar c'"
  using path_search[OF state_invarD[OF assms(1)] assms(2)[unfolded search_of_def]] 
  by auto

subsection \<open>Invariant Preservation\<close>

lemma 
 assumes "hungarian_loop_cont_cond state"  "state_invar state"
 shows state_invar_pres_one_step:
    "state_invar (hungarian_loop_upd state)"
 and card_increase: "card (matching_abstract (buddies (hungarian_loop_upd state)))
                     > card (matching_abstract (buddies state))"
proof-
  obtain p M \<pi>' c' where search_is: "search_of state = (Next_Iteration p, M, \<pi>', c')"
    using assms(1) by(auto elim!: hungarian_loop_cont_condE)
  note search_props = search_of_props[OF assms(2) search_is]
  note precond = path_search_precondD[OF good_searchD(1)[OF search_props(1)]]
  note path_search_props_unfolded = 
         good_search_resultD[OF good_searchD(5)[OF search_props(1) refl]]
  define M' where "M' = augment M p"
  have state'_is: 
    "hungarian_loop_upd state = state \<lparr>buddies:=M', potential := \<pi>', search_ctx := c'\<rparr>"
    by(simp add: hungarian_loop_upd_def search_is M'_def)
  have matching_invar': "matching_invar M'" 
    by(auto intro!: augment(1) simp add: M'_def precond(1) path_search_props_unfolded(5))
  have M'_is: "matching_abstract M' = matching_abstract M \<oplus> set (edges_of_path p)"
    using precond(1) path_search_props_unfolded(5)
    by(auto simp add: augment(2) M'_def)
  hence new_matching_valid: "graph_matching G (matching_abstract M')"
    using precond(1,3) path_search_props_unfolded(5)
    by(auto intro!: graph_matching_finite dest: Berge_2')
  have M'_tight:
     "matching_abstract M' \<subseteq> tight_subgraph G edge_costs (potential_abstract \<pi>')" 
  proof(rule, goal_cases)
    case (1 e)
   hence  "e \<in> matching_abstract M \<or> e \<in> set (edges_of_path p)" "e \<in> G" 
     using precond(3) path_search_props_unfolded(5)
     by(auto simp add: in_symmetric_diff_iff M'_is intro: path_ball_edges )
   then show ?case 
     using path_search_props_unfolded(2,4)
     by auto
 qed
  show "state_invar (hungarian_loop_upd state)"
    using new_matching_valid M'_tight search_props(2)
    by(auto intro!: state_invarI path_search_precondI matching_invar' path_search_props_unfolded 
          simp add: state'_is)
  have "card (matching_abstract M') > card (matching_abstract M)"
    by(auto intro!: new_matching_bigger graph_matching_finite precond(3)
          simp add: M'_is path_search_props_unfolded(5,1))
  thus "card (matching_abstract (buddies (hungarian_loop_upd state)))
                     > card (matching_abstract (buddies state))"
    using good_searchD(2)[OF search_props(1)] by(simp add: state'_is)
qed

lemma fail_props:
  assumes "hungarian_loop_fail_cond state" "state_invar state"
  shows "state_invar (hungarian_loop_fail state)" 
        "result (hungarian_loop_fail state) = failure"
        "\<forall> B. \<exists> \<pi>. feasible_min_perfect_dual G edge_costs \<pi> \<and> sum \<pi> (L \<union> R) > B"
proof-
  obtain M' \<pi>' c' where search_is: "search_of state = (Dual_Unbounded, M', \<pi>', c')"
    using assms(1) by(auto elim!: hungarian_loop_fail_condE)
  note search_props = search_of_props[OF assms(2) search_is]
  show "state_invar (hungarian_loop_fail state)"
    using good_searchD(1)[OF search_props(1)] search_props(2)
    by(auto intro!: state_invarI simp add: hungarian_loop_fail_def search_is)
  show "result (hungarian_loop_fail state) = failure"
    by(simp add: hungarian_loop_fail_def search_is)
  show "\<forall> B. \<exists> \<pi>. feasible_min_perfect_dual G edge_costs \<pi> \<and> sum \<pi> (L \<union> R) > B"
    using good_searchD(3)[OF search_props(1) refl] .
qed

lemma succ_props:
  assumes "hungarian_loop_succ_cond state" "state_invar state"
  shows "state_invar (hungarian_loop_succ state)" 
        "result (hungarian_loop_succ state) = success"
        "L \<subseteq> Vs (matching_abstract (buddies (hungarian_loop_succ state)))"
proof-
  obtain M' \<pi>' c' where search_is: "search_of state = (Lefts_Matched, M', \<pi>', c')"
    using assms(1) by(auto elim!: hungarian_loop_succ_condE)
  note search_props = search_of_props[OF assms(2) search_is]
  show "state_invar (hungarian_loop_succ state)"
    using good_searchD(1)[OF search_props(1)] search_props(2)
    by(auto intro!: state_invarI simp add: hungarian_loop_succ_def search_is)
  show "result (hungarian_loop_succ state) = success"
    by(simp add: hungarian_loop_succ_def search_is)
  show "L \<subseteq> Vs (matching_abstract (buddies (hungarian_loop_succ state)))"
    using good_searchD(4)[OF search_props(1) refl] 
    by(simp add: hungarian_loop_succ_def search_is)
qed

subsection \<open>Termination\<close>

lemma hungarian_loop_termination_induction:
  assumes "state_invar state"
          "n = card G - card (matching_abstract (buddies state))"
    shows "hungarian_loop_dom state"
  using assms
proof(induction n arbitrary: state rule: less_induct)
  case (less n)
  show ?case 
  proof(cases state rule: hungarian_loop_cases)
    case 3
    note invar_later = state_invar_pres_one_step[OF 3 less(2)]
    hence card_later_less_G:
        "card (matching_abstract (buddies (hungarian_loop_upd state))) \<le> card G"
      using G(1,4,5)  finite_Vs_then_finite finite_parts_bipartite_graph_invar
      by(auto intro!: card_mono dest!: state_invarD(1) path_search_precondD(3))
    hence card_decrease:
         "card G - card (matching_abstract (buddies (hungarian_loop_upd state))) < n"
      using card_increase[OF 3 less(2)] less(3) by linarith
    show ?thesis 
      using 3 less(1) card_decrease invar_later
      by(auto intro: hungarian_loop_domintros(3))
  qed (simp_all add: hungarian_loop_domintros(1,2))
qed

lemmas hungarian_loop_termination = hungarian_loop_termination_induction[OF _ refl]

subsection \<open>Correctness\<close>

lemma hungarian_loop_result:
  assumes "hungarian_loop_dom state" "state_invar state"
  shows "state_invar (hungarian_loop state) \<and> result (hungarian_loop state) \<noteq> notyetterm \<and>
         (result (hungarian_loop state) = success \<longrightarrow>
            L \<subseteq> Vs (matching_abstract (buddies (hungarian_loop state)))) \<and>
         (result (hungarian_loop state) = failure \<longrightarrow>
            (\<forall> B. \<exists> \<pi>. feasible_min_perfect_dual G edge_costs \<pi> \<and> sum \<pi> (L \<union> R) > B))"
  using assms(2)
proof(induction rule: hungarian_loop_induct[OF assms(1)])
  case (1 state)
  note IH = this
  show ?case
  proof(cases state rule: hungarian_loop_cases)
    assume fc: "hungarian_loop_fail_cond state"
    show ?thesis 
      using fail_props[OF fc IH(3)] by(simp add: hungarian_loop_simps(1)[OF fc])
  next
    assume sc: "hungarian_loop_succ_cond state"
    show ?thesis 
      using succ_props[OF sc IH(3)] by(simp add: hungarian_loop_simps(2)[OF sc])
  next
    assume cc: "hungarian_loop_cont_cond state"
    show ?thesis 
      using IH(2)[OF cc] state_invar_pres_one_step[OF cc IH(3)]
      by(simp add: hungarian_loop_simps(3)[OF cc IH(1)])
  qed
qed

lemma min_perfect_if_lefts_matched:
  assumes "state_invar state" "card_L = card_R"
          "L \<subseteq> Vs (matching_abstract (buddies state))"
    shows "min_weight_perfect_matching G edge_costs (matching_abstract (buddies state))"
proof-
  note precond = path_search_precondD[OF state_invarD(1)[OF assms(1)]]
  have perfect: "perfect_matching G (matching_abstract (buddies state))"
    using assms(2,3) precond(3)
    by (auto intro: all_left_matched_perfect[OF G(1)] simp add: G(2,3,5))
  thus ?thesis
    using G(1,4,5) finite_parts_bipartite_graph_invar precond(4,5)
    by(auto intro!: min_weight_perfect_if_tight(1)[of _ _ "potential_abstract (potential state)"])
qed

lemma infeasible_if_sides_unequal_size:
  "card_L \<noteq> card_R \<Longrightarrow> \<nexists> M. perfect_matching G M"
  using G(6)
  by(intro no_perfect_matching_one_side_bigger)
    (auto intro!: G(1) simp add: G(2,3))

lemma no_perfect_if_unbounded:
  assumes "\<forall> B. \<exists> \<pi>. feasible_min_perfect_dual G edge_costs \<pi> \<and> sum \<pi> (L \<union> R) > B"
    shows "\<nexists> M. perfect_matching G M"
proof(rule notI, goal_cases)
  case 1
  then obtain M where M: "perfect_matching G M" 
    by auto
  define B where "B = sum edge_costs M"
  obtain \<pi> where pi: "feasible_min_perfect_dual G edge_costs \<pi>" "B < sum \<pi> (L \<union> R)"
    using assms by blast
  moreover hence "sum \<pi> (Vs G) \<le> sum edge_costs M"
    using M G(1,4,5) finite_parts_bipartite_graph_invar
    by(auto intro!: min_perfect_matching_weak_duality)
  moreover have "L \<union> R = Vs G"
    using G(1,6) bipartite_vs_subset by blast
  ultimately show False
    by(auto simp add: B_def)
qed

subsection \<open>The Initial State\<close>

lemma initial_state_invar: 
  "state_invar initial_state"
  by(auto intro!: state_invarI path_search_precondI
        simp add: initial_state_def matching potential init_ctx)

lemma initial_state_hungarian_dom:
  "hungarian_loop_dom initial_state"
  by (simp add: hungarian_loop_termination initial_state_invar)

lemma initial_state_loops_same:
  "hungarian_loop_impl initial_state = hungarian_loop initial_state"
  by (simp add: hungarian_loop_impl_same initial_state_hungarian_dom)

lemma loop_on_initial_state_result:
  "state_invar (hungarian_loop initial_state)"
  "result (hungarian_loop initial_state) \<noteq> notyetterm"
  "result (hungarian_loop initial_state) = success \<Longrightarrow>
     L \<subseteq> Vs (matching_abstract (buddies (hungarian_loop initial_state)))"
  "result (hungarian_loop initial_state) = failure \<Longrightarrow>
     \<forall> B. \<exists> \<pi>. feasible_min_perfect_dual G edge_costs \<pi> \<and> sum \<pi> (L \<union> R) > B"
  using hungarian_loop_result[OF initial_state_hungarian_dom initial_state_invar] by auto

subsection \<open>Final Correctness\<close>

lemma hungarian_cases:
  "hungarian = None \<Longrightarrow> 
     card_L \<noteq> card_R \<or> result (hungarian_loop initial_state) = failure"
  "hungarian = Some M \<Longrightarrow> 
     card_L = card_R \<and> result (hungarian_loop initial_state) = success \<and>
     M = buddies (hungarian_loop initial_state)"
  using loop_on_initial_state_result(2)
  by(auto simp add: hungarian_def Let_def initial_state_loops_same 
             split: if_split_asm result.split_asm)

theorem hungarian_correctness:
 "hungarian = None \<Longrightarrow> \<nexists> M. perfect_matching G M"
 "hungarian = Some M \<Longrightarrow> min_weight_perfect_matching G edge_costs (matching_abstract M)"
proof-
  show "hungarian = None \<Longrightarrow> \<nexists> M. perfect_matching G M"
    using hungarian_cases(1) loop_on_initial_state_result(4)
          infeasible_if_sides_unequal_size no_perfect_if_unbounded 
    by blast
  show "hungarian = Some M \<Longrightarrow> min_weight_perfect_matching G edge_costs (matching_abstract M)"
    using hungarian_cases(2) loop_on_initial_state_result(1,3)
    by(auto intro: min_perfect_if_lefts_matched)
qed

lemma hungarian_final_invar:
  "hungarian = Some M \<Longrightarrow> matching_invar M"
  using hungarian_cases(2) loop_on_initial_state_result(1)
  by(auto dest: state_invarD(1) path_search_precondD(1))

end

end