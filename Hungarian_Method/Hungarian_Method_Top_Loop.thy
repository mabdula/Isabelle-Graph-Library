theory Hungarian_Method_Top_Loop
  imports Matching_LPs.Matching_LP
          Path_Search_Result Basic_Matching.Matching_Augmentation_Executable
begin

section \<open>Top Loop for Hungarian Method\<close>

no_translations
  "_Collect p P"      <= "{p. P}"
  "_Collect p P"      <= "{p|xs. P}"

datatype result = success | failure | notyetterm

record ('buddy, 'potential) hungarian_state = 
     buddies::'buddy
     potential::'potential
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
   and path_search::"'matching \<Rightarrow> 'potential \<Rightarrow> ('v, 'potential) path_search_result"
   and G::"'v set set"
begin

function (domintros) hungarian_loop::
   "('matching, 'potential) hungarian_state \<Rightarrow> ('matching, 'potential) hungarian_state"
   where "hungarian_loop state =
     (let M = buddies state;
          \<pi> = potential state in
       case path_search M \<pi> of
         Dual_Unbounded \<Rightarrow> state \<lparr>result:=failure\<rparr>
       | Lefts_Matched \<Rightarrow> state \<lparr>result:=success\<rparr>
       | Next_Iteration P \<pi>' \<Rightarrow>
         let M' = augment M P
         in hungarian_loop (state \<lparr>buddies:=M', potential := \<pi>' \<rparr>))"
  by pat_completeness auto

partial_function (tailrec) hungarian_loop_impl::
   "('matching, 'potential) hungarian_state \<Rightarrow> ('matching, 'potential) hungarian_state"
   where "hungarian_loop_impl state =
     (let M = buddies state;
          \<pi> = potential state in
       case path_search M \<pi> of
         Dual_Unbounded \<Rightarrow> state \<lparr>result:=failure\<rparr>
       | Lefts_Matched \<Rightarrow> state \<lparr>result:=success\<rparr>
       | Next_Iteration P \<pi>' \<Rightarrow>
         let M' = augment M P
         in hungarian_loop_impl (state \<lparr>buddies:=M', potential := \<pi>' \<rparr>))"

definition "initial_state = \<lparr>buddies = empty_matching, potential = init_potential, result = notyetterm\<rparr>"

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
  by(auto simp add: Let_def split: path_search_result.splits)

definition  "hungarian_loop_upd state =
     (let M = buddies state;
          \<pi> = potential state;
          P = the_path (path_search M \<pi>);
          \<pi>' = the_pot (path_search M \<pi>); 
          M' = augment M P
       in state \<lparr>buddies:=M', potential := \<pi>' \<rparr>)"

definition  "hungarian_loop_fail state = (state \<lparr> result:=failure \<rparr>)"
definition  "hungarian_loop_succ state = (state \<lparr> result:=success \<rparr>)"

definition  "hungarian_loop_fail_cond state =
     (let M = buddies state;
          \<pi> = potential state in
       case path_search M \<pi> of
         Dual_Unbounded \<Rightarrow> True
       | Lefts_Matched \<Rightarrow> False
       | Next_Iteration P \<pi>' \<Rightarrow> False)"

lemma hungarian_loop_fail_condE:
  "\<lbrakk>hungarian_loop_fail_cond state;
    path_search (buddies state) (potential state) = Dual_Unbounded \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
and hungarian_loop_fail_condI:
  "path_search (buddies state) (potential state) = Dual_Unbounded
   \<Longrightarrow> hungarian_loop_fail_cond state"
  by(cases "path_search (buddies state) (potential state)")
    (auto simp add: hungarian_loop_fail_cond_def)

definition  "hungarian_loop_succ_cond state =
     (let M = buddies state;
          \<pi> = potential state in
       case path_search M \<pi> of
         Dual_Unbounded \<Rightarrow> False
       | Lefts_Matched \<Rightarrow> True
       | Next_Iteration P \<pi>' \<Rightarrow> False)"

lemma hungarian_loop_succ_condE:
  "\<lbrakk>hungarian_loop_succ_cond state;
    path_search (buddies state) (potential state) = Lefts_Matched \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
and hungarian_loop_succ_condI:
  "path_search (buddies state) (potential state) = Lefts_Matched
   \<Longrightarrow> hungarian_loop_succ_cond state"
  by(cases "path_search (buddies state) (potential state)")
    (auto simp add: hungarian_loop_succ_cond_def)

definition  "hungarian_loop_cont_cond state =
     (let M = buddies state;
          \<pi> = potential state in
       case path_search M \<pi> of
         Dual_Unbounded \<Rightarrow> False
       | Lefts_Matched \<Rightarrow> False
       | Next_Iteration P \<pi>' \<Rightarrow> True)"

lemma hungarian_loop_cont_condE:
  "\<lbrakk>hungarian_loop_cont_cond state;
   \<And> p \<pi>'. path_search (buddies state) (potential state) = Next_Iteration p \<pi>' \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
and  hungarian_loop_cont_condI:
   "path_search (buddies state) (potential state) = Next_Iteration p \<pi>' \<Longrightarrow> 
    hungarian_loop_cont_cond state"
  by(cases "path_search (buddies state) (potential state)")
    (auto simp add: hungarian_loop_cont_cond_def)

lemma hungarian_loop_cases:
  assumes "hungarian_loop_fail_cond state \<Longrightarrow> P"
          "hungarian_loop_succ_cond state \<Longrightarrow> P"
          "hungarian_loop_cont_cond state \<Longrightarrow> P"
    shows P
  using assms
  apply(cases "path_search (buddies state) (potential state)")
  by(auto simp add: hungarian_loop_fail_cond_def 
                    hungarian_loop_cont_cond_def
                    hungarian_loop_succ_cond_def)

lemma hungarian_loop_domintros:
  "hungarian_loop_fail_cond state \<Longrightarrow> hungarian_loop_dom state"
  "hungarian_loop_succ_cond state \<Longrightarrow> hungarian_loop_dom state"
  "\<lbrakk>hungarian_loop_cont_cond state; hungarian_loop_dom (hungarian_loop_upd state)\<rbrakk>
    \<Longrightarrow> hungarian_loop_dom state"
    apply(all \<open>rule hungarian_loop.domintros\<close>)
    apply(all \<open>cases "path_search (buddies state) (potential state)"\<close>)
    by(auto simp add: hungarian_loop_fail_cond_def 
                      hungarian_loop_cont_cond_def
                      hungarian_loop_succ_cond_def
                      hungarian_loop_upd_def)

lemma hungarian_loop_simps:
 "hungarian_loop_fail_cond state \<Longrightarrow> hungarian_loop state = hungarian_loop_fail state"
 "hungarian_loop_succ_cond state \<Longrightarrow> hungarian_loop state = hungarian_loop_succ state"
 "\<lbrakk>hungarian_loop_cont_cond state; hungarian_loop_dom state\<rbrakk>
   \<Longrightarrow> hungarian_loop state = hungarian_loop (hungarian_loop_upd state)"
  by(auto simp add: hungarian_loop.psimps[OF hungarian_loop_domintros(1)] 
                    hungarian_loop.psimps[OF hungarian_loop_domintros(2)] 
                    hungarian_loop.psimps  hungarian_loop_upd_def
                    hungarian_loop_fail_def hungarian_loop_succ_def
            elim: hungarian_loop_fail_condE hungarian_loop_succ_condE
                  hungarian_loop_cont_condE)

lemma fail_cond_after_fail_upd:
  "hungarian_loop_fail_cond state \<Longrightarrow> hungarian_loop_fail_cond (hungarian_loop_fail state)"
  by(auto elim!: hungarian_loop_fail_condE
         intro!: hungarian_loop_fail_condI
       simp add: hungarian_loop_fail_def)

lemma succ_cond_after_succ_upd:
  "hungarian_loop_succ_cond state \<Longrightarrow> hungarian_loop_succ_cond (hungarian_loop_succ state)"
  by(auto elim!: hungarian_loop_succ_condE
         intro!: hungarian_loop_succ_condI
       simp add: hungarian_loop_succ_def)

lemma succ_and_fail_impossible:
 "\<lbrakk>hungarian_loop_succ_cond state; hungarian_loop_fail_cond state\<rbrakk> \<Longrightarrow> False"
  by(auto elim!: hungarian_loop_succ_condE hungarian_loop_fail_condE)

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
  proof(cases state rule: hungarian_loop_cases, goal_cases)
    case 1
    then show ?case
     by(auto elim!:  hungarian_loop_fail_condE
            intro!: assms(2)[OF IH(1)]
          simp add: hungarian_loop_cont_cond_def)
  next
    case 2
    then show ?case 
     by(auto elim!:  hungarian_loop_succ_condE
            intro!: assms(2)[OF IH(1)] 
          simp add: hungarian_loop_cont_cond_def)
  next
    case 3
    show ?case 
      apply(rule assms(2)[OF IH(1)])
      using 3 
      by(auto intro!: IH(2)
               elim!: hungarian_loop_cont_condE
            simp add: hungarian_loop_upd_def Let_def 
               split: option.split prod.split path_search_result.splits)
  qed
qed

lemma flag_unchanged: "result (hungarian_loop_upd state) = result state"
  by(auto simp add: hungarian_loop_upd_def Let_def)

lemma flag_fail: "result (hungarian_loop_fail state) = failure"
  by(auto simp add: hungarian_loop_fail_def Let_def)

lemma flag_succ: "result (hungarian_loop_succ state) = success"
  by(auto simp add: hungarian_loop_succ_def Let_def)

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

end

subsection \<open>Locale for Proofs\<close>

locale hungarian_loop = 
 hungarian_loop_spec where edge_costs = edge_costs
for edge_costs::"'v set \<Rightarrow> real" +
fixes L R
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
  "\<And> M \<pi> B. \<lbrakk>path_search_precond M \<pi>; path_search M \<pi> = Dual_Unbounded\<rbrakk>
    \<Longrightarrow> \<exists> \<pi>'. feasible_min_perfect_dual G edge_costs \<pi>' \<and> sum \<pi>' (L \<union> R) > B"
   "\<And> M \<pi>. \<lbrakk>path_search_precond M \<pi>; path_search M \<pi> = Lefts_Matched\<rbrakk> 
    \<Longrightarrow> L \<subseteq> Vs (matching_abstract M)"
   "\<And> M \<pi> \<pi>' p. \<lbrakk>path_search_precond M \<pi>; path_search M \<pi> = Next_Iteration p \<pi>'\<rbrakk> 
    \<Longrightarrow> good_search_result M \<pi>' p" 
begin

lemma graph_matching_finite: "graph_matching G M \<Longrightarrow> finite M" 
  using  finite_Vs_then_finite[of M] finite_parts_bipartite_graph_invar[OF G(4,5,1)]
      graph_invar_subset
  by auto

subsection \<open>Invariant Setup\<close>

definition "state_invar state = 
  (matching_invar (buddies state) \<and> potential_invar (potential state) \<and>
   graph_matching G (matching_abstract (buddies state)) \<and>
  matching_abstract (buddies state) \<subseteq> 
        tight_subgraph G edge_costs (potential_abstract (potential state)) \<and>
  feasible_min_perfect_dual G edge_costs (potential_abstract (potential state)))"

lemma state_invarE:
  "state_invar state \<Longrightarrow> 
   (\<lbrakk>matching_invar (buddies state); potential_invar (potential state);
     graph_matching G (matching_abstract (buddies state));
     matching_abstract (buddies state) \<subseteq> 
          tight_subgraph G edge_costs (potential_abstract (potential state));
     feasible_min_perfect_dual G edge_costs (potential_abstract (potential state))\<rbrakk>
     \<Longrightarrow> P)
   \<Longrightarrow> P"
and state_invarI:
  "\<lbrakk>matching_invar (buddies state); potential_invar (potential state);
    graph_matching G (matching_abstract (buddies state));
    matching_abstract (buddies state) \<subseteq> 
          tight_subgraph G edge_costs (potential_abstract (potential state));
    feasible_min_perfect_dual G edge_costs (potential_abstract (potential state))\<rbrakk>
   \<Longrightarrow> state_invar state"
and state_invarD:
  "state_invar state \<Longrightarrow> matching_invar (buddies state)"
  "state_invar state \<Longrightarrow> potential_invar (potential state)"
  "state_invar state \<Longrightarrow> graph_matching G (matching_abstract (buddies state))"
  "state_invar state \<Longrightarrow> 
    matching_abstract (buddies state) \<subseteq> 
         tight_subgraph G edge_costs (potential_abstract (potential state))"
  "state_invar state \<Longrightarrow> 
    feasible_min_perfect_dual G edge_costs (potential_abstract (potential state))"
  by(auto simp add: state_invar_def)

subsection \<open>Invariant Preservation\<close>

lemma 
 assumes "hungarian_loop_cont_cond state"  "state_invar state"
 shows state_invar_pres_one_step:
    "state_invar (hungarian_loop_upd state)"
 and card_increase: "card (matching_abstract (buddies (hungarian_loop_upd state)))
                     > card (matching_abstract (buddies state))"
proof-
  define M where "M = buddies state"
  define \<pi> where "\<pi> = potential state"
  obtain p \<pi>' where path_search_result_is:  "path_search M \<pi> = Next_Iteration p \<pi>'"
    using assms(1)
    by(auto elim!: hungarian_loop_cont_condE simp add: M_def \<pi>_def)
  note state_invars = state_invarD[OF assms(2), folded M_def \<pi>_def]
  hence path_search_precond: "path_search_precond M \<pi>"
    by(auto intro!: path_search_precondI)
  note path_search_props = path_search(3)[OF path_search_precond path_search_result_is]
  note path_search_props_unfolded = 
         good_search_resultD[OF path_search_props]
  define M' where "M' = augment M p"
  have state'_is: "hungarian_loop_upd state = state \<lparr>buddies:=M', potential := \<pi>' \<rparr>"
    using path_search_result_is
    by(auto simp add: hungarian_loop_upd_def M'_def M_def \<pi>_def)
  have matching_invar': "matching_invar M'" 
    by(auto intro!: augment(1) simp add: M'_def state_invars(1) path_search_props_unfolded(5))
  have M'_is: "matching_abstract M' = matching_abstract M \<oplus> set (edges_of_path p)"
    using  state_invars(1) path_search_props_unfolded(5)
    by(auto simp add: augment(2) M'_def)
  hence new_matching_valid: "graph_matching G (matching_abstract M')"
    using  state_invars(1) path_search_props_unfolded(5) state_invars(3)
    by(auto intro!: graph_matching_finite dest: Berge_2')
  have M'_tight:
     "matching_abstract M' \<subseteq> tight_subgraph G edge_costs (potential_abstract \<pi>')" 
  proof(rule, goal_cases)
    case (1 e)
   hence  "e \<in> matching_abstract M \<or> e \<in> set (edges_of_path p)" "e \<in> G" 
     using state_invars(3) path_search_props_unfolded(5)
     by(auto simp add: in_symmetric_diff_iff M'_is intro: path_ball_edges )
   then show ?case 
     using path_search_props_unfolded(2,4)
     by auto
 qed
    show "state_invar (hungarian_loop_upd state)"
      using new_matching_valid  M'_tight
      by(auto intro!: state_invarI matching_invar' path_search_props_unfolded 
            simp add: state'_is)
    show  "card (matching_abstract (buddies (hungarian_loop_upd state)))
                     > card (matching_abstract (buddies state))"
      by(auto intro!: new_matching_bigger graph_matching_finite state_invars(3)
            simp add: state'_is M_def[symmetric] M'_is  path_search_props_unfolded(5,1))
  qed

lemma 
 assumes "state_invar state"
 shows state_invar_pres_fail: "state_invar (hungarian_loop_fail state)"
   and state_invar_pres_succ: "state_invar (hungarian_loop_succ state)"
  using assms
  by(auto intro!: state_invarI
           elim!: state_invarE
        simp add: hungarian_loop_fail_def hungarian_loop_succ_def)

lemma state_invar_pres:
  assumes "hungarian_loop_dom state"
          "state_invar state"
    shows "state_invar (hungarian_loop state)"
  using assms(2)
proof(induction rule: hungarian_loop_induct[OF assms(1)])
  case (1 state)
  then show ?case
    by(cases state rule: hungarian_loop_cases)
      (auto intro: state_invar_pres_fail state_invar_pres_succ 
                   state_invar_pres_one_step 
         simp add: hungarian_loop_simps)
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
      by(auto intro!: card_mono dest!: state_invarD(3))
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

lemma final_flag:
  assumes "hungarian_loop_dom state"
    shows "result (hungarian_loop state) \<noteq> notyetterm"
proof(induction rule: hungarian_loop_induct[OF assms(1)])
  case (1 state)
  then show ?case
    by(cases state rule: hungarian_loop_cases)
      (auto simp add: hungarian_loop_simps flag_fail flag_succ)
qed

lemma if_fail_flag_then_fail:
  assumes "hungarian_loop_dom state" "result (hungarian_loop state) = failure"
    shows "hungarian_loop_fail_cond (hungarian_loop state)"
  using assms(2)
proof(induction rule: hungarian_loop_induct[OF assms(1)])
  case (1 state)
  then show ?case
    by(cases state rule: hungarian_loop_cases)
      (auto simp add: hungarian_loop_simps  hungarian_loop_succ_def
               intro: fail_cond_after_fail_upd)
qed

lemma if_succ_flag_then_succ:
  assumes "hungarian_loop_dom state" "result (hungarian_loop state) = success"
    shows "hungarian_loop_succ_cond (hungarian_loop state)"
  using assms(2)
proof(induction rule: hungarian_loop_induct[OF assms(1)])
  case (1 state)
  then show ?case
    by(cases state rule: hungarian_loop_cases)
      (auto simp add: hungarian_loop_simps  hungarian_loop_fail_def
               intro: succ_cond_after_succ_upd)
qed

lemma min_perfect_if_algo_says_so:
  assumes "hungarian_loop_succ_cond state"
          "state_invar state" "card_L = card_R"
    shows "min_weight_perfect_matching G edge_costs (matching_abstract (buddies state))"
proof-
  have "L \<subseteq> Vs (matching_abstract (buddies state))" 
    using assms(1,2)
    by(intro path_search(2))
      (auto elim!: hungarian_loop_succ_condE state_invarE
            intro: path_search_precondI)
  hence perfect: "perfect_matching G (matching_abstract (buddies state))"
    using  assms(2,3) 
    by (auto intro: all_left_matched_perfect[OF G(1)] 
             elim!: state_invarE 
          simp add: G(2,3,5))
  thus ?thesis
    using G(1,4,5) finite_parts_bipartite_graph_invar state_invarD(4,5)[OF assms(2)]
    by(auto intro!: min_weight_perfect_if_tight(1)[of _ _ "potential_abstract (potential state)"])
qed

lemma infeasible_if_sides_unequal_size:
  "card_L \<noteq> card_R \<Longrightarrow> \<nexists> M. perfect_matching G M"
  using G(6)
  by(intro no_perfect_matching_one_side_bigger)
    (auto intro!: G(1) simp add: G(2,3))

lemma no_perfect_if_algo_says_so:
  assumes "hungarian_loop_fail_cond state"
          "state_invar state"
    shows "\<nexists> M. perfect_matching G M"
proof(rule notI, goal_cases)
  case 1
  then obtain M where M: "perfect_matching G M" 
    by auto
  define B where "B = sum edge_costs M"
  obtain \<pi> where pi: "feasible_min_perfect_dual G edge_costs \<pi>" "B < sum \<pi> (L \<union> R)"
    using assms(1,2)
    by(auto elim!: hungarian_loop_fail_condE state_invarE 
            dest!: path_search(1)[OF path_search_precondI])
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
  by(auto intro!: state_invarI 
        simp add: initial_state_def matching potential)

lemma initial_state_hungarian_dom:
  "hungarian_loop_dom initial_state"
  by (simp add: hungarian_loop_termination initial_state_invar)

lemma initial_state_loops_same:
  "hungarian_loop_impl initial_state = hungarian_loop initial_state"
  by (simp add: hungarian_loop_impl_same initial_state_hungarian_dom)

lemma loop_on_initial_state_invar:
  "state_invar (hungarian_loop initial_state)"
  by (simp add: initial_state_hungarian_dom initial_state_invar state_invar_pres)

subsection \<open>Final Correctness\<close>

theorem hungarian_correctness:
 "hungarian = None \<Longrightarrow> \<nexists> M. perfect_matching G M"
 "hungarian = Some M \<Longrightarrow> min_weight_perfect_matching G edge_costs (matching_abstract M)"
proof(goal_cases)
  case 1
  show ?case
  proof(cases "card_L = card_R")
    case True
    hence "result (hungarian_loop initial_state) = failure" 
      using 1 initial_state_hungarian_dom 
      by(auto simp add: Let_def result.split[of "\<lambda> x. x = None"]
                        initial_state_loops_same if_split[of "\<lambda> x. x = None"]
                        hungarian_loop_spec.hungarian_def
                 intro: result.exhaust[of "result (hungarian_loop initial_state)"]
                  dest: final_flag) 
    hence "hungarian_loop_fail_cond (hungarian_loop initial_state)" 
      using if_fail_flag_then_fail initial_state_hungarian_dom by blast
    then show ?thesis 
      using loop_on_initial_state_invar
      by(rule no_perfect_if_algo_says_so)
  next
    case False
    then show ?thesis 
      by(rule infeasible_if_sides_unequal_size)
  qed
next
  case 2
  hence "result (hungarian_loop initial_state) = success" 
      and same_cards:"card_L = card_R"
      and M_is: "M = buddies (hungarian_loop initial_state)"
      using 2 initial_state_hungarian_dom
      by(auto simp add: hungarian_def Let_def result.split[of "\<lambda> x. x = Some _"]
                        if_split[of "\<lambda> x. x = Some _"] initial_state_loops_same 
                 intro: result.exhaust[of "result (hungarian_loop initial_state)"]
                  dest: final_flag) 
    hence "hungarian_loop_succ_cond (hungarian_loop initial_state)" 
      using if_succ_flag_then_succ initial_state_hungarian_dom by blast
    thus ?case
      using loop_on_initial_state_invar same_cards
      by(auto intro!: min_perfect_if_algo_says_so simp add: M_is)
  qed

lemma hungarian_final_invar:
  "hungarian = Some M \<Longrightarrow> matching_invar M"
proof(goal_cases)
  case 1
  hence "result (hungarian_loop initial_state) = success" 
      and same_cards:"card_L = card_R"
      and M_is: "M = buddies (hungarian_loop initial_state)"
      using 1 initial_state_hungarian_dom
      by(auto simp add: hungarian_def Let_def result.split[of "\<lambda> x. x = Some _"]
                        if_split[of "\<lambda> x. x = Some _"] initial_state_loops_same 
                 intro: result.exhaust[of "result (hungarian_loop initial_state)"]
                  dest: final_flag) 
    hence "hungarian_loop_succ_cond (hungarian_loop initial_state)" 
      using if_succ_flag_then_succ initial_state_hungarian_dom by blast
    thus ?case
      using loop_on_initial_state_invar
      by(auto simp add: M_is elim!: state_invarE)
  qed

end
end