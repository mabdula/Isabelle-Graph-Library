section \<open>Using Orlins Algorithms to solve Flow Problems\<close>

subsection \<open>Flows in uncapacitated, simple Graphs\<close>

theory Usage_Pair_Graph
  imports Instantiation
begin

definition "\<E>_impl = [(1::nat, 2::nat), (1,3), (3,2), (2,4), (2,5),
(3,5), (4,6), (6,5), (2,6)] "
value "\<E>_impl"

definition "b_list =  [(1::nat,128::real), (2,0), (3,1), (4,-33), (5,-32), (6,-64)]"

definition "\<b>_impl = foldr (\<lambda> xy tree. update (prod.fst xy) (prod.snd xy) tree) b_list Leaf"
value "\<b>_impl"

definition "c_list = [( (1::nat, 2::nat), 1::real),
 ((1,3), 4), ((3,2), 2), ((2,4), 3), ((2,5), 1),
((3,5), 5), ((4,6), 2), ((6,5), 1), ((2,6), 9)]"

definition "\<c>_impl = foldr (\<lambda> xy tree. update (prod.fst xy) (prod.snd xy) tree) c_list Leaf"
value "\<c>_impl"


definition "final_state_pair = final_state id Pair \<E>_impl \<c>_impl \<b>_impl flow_lookup"
value final_state_pair

definition "final_flow_impl_pair = final_flow_impl id Pair \<E>_impl \<c>_impl \<b>_impl flow_lookup"
value final_flow_impl_pair

definition "final_forest = remove_all_empties(\<FF>_impl final_state_pair)"

value "inorder final_flow_impl_pair"
value "map (\<lambda> (x, y). (x, inorder y)) (inorder final_forest)"
value "inorder (conv_to_rdg_impl final_state_pair)"
value "inorder (not_blocked_impl final_state_pair)"


lemma no_cycle: "closed_w (id ` \<E> \<E>_impl) (map id C) \<Longrightarrow> (set C \<subseteq> \<E> \<E>_impl) \<Longrightarrow>
        foldr (\<lambda>e acc. acc + \<c> \<c>_impl flow_lookup e) C 0 < 0 \<Longrightarrow> False"
proof(goal_cases)
  case 1
  have C_in_E:"set C \<subseteq> set \<E>_impl"
    using 1 \<E>_impl_def 
    by (simp add: subset_eq to_set_def  selection_functions.\<E>_def)
  moreover have "List.filter (\<lambda> e. \<c>  \<c>_impl flow_lookup e > 0) \<E>_impl = \<E>_impl"
    unfolding selection_functions.\<c>_def flow_lookup_def \<c>_impl_def update_def \<E>_impl_def c_list_def
    by simp
  moreover hence "e \<in> set \<E>_impl \<Longrightarrow> \<c>  \<c>_impl flow_lookup e > 0" for e
    by (meson filter_id_conv)
  ultimately have "foldr (\<lambda>e acc. acc + \<c>  \<c>_impl flow_lookup e) C 0 \<ge> 0"
    by(induction C)
      (auto simp add: order_less_le)
  then show ?case 
    using 1 by simp
qed

lemma \<E>_impl_basic: "set_invar \<E>_impl"  "\<exists> e. e \<in> (to_set \<E>_impl)"
                  "finite (\<E> \<E>_impl)"
 proof(goal_cases)
  case 1
  then show ?case
    by(auto simp add: \<E>_impl_def set_invar_def)
next
  case 2
  then show ?case 
    by(auto simp add: \<E>_impl_def set_invar_def  to_set_def)
next
  case 3
  then show ?case  
    by(auto simp add: \<E>_impl_def set_invar_def selection_functions.\<E>_def to_set_def)
qed

lemma multigraph: "multigraph (prod.fst o id) (prod.snd o  id) id Pair (\<E> \<E>_impl)"
  apply(rule multigraph.intro)
  subgoal for e x y
    by(cases e) auto
  subgoal for x y
    by simp
   apply (simp add: \<E>_impl_basic(3))
  using selection_functions.\<E>_def \<E>_impl_basic(2) by blast


lemma Vs_is: "dVs (id ` to_set \<E>_impl) = {1,2,3,4,5,6}"
  unfolding to_set_def \<E>_impl_def by (auto simp add: dVs_def)

lemma Vs_is_bal_dom: "dVs (id` to_set \<E>_impl) = dom (bal_lookup \<b>_impl)" 
  apply(rule trans[of  _ "{1,2,3,4,5,6}"])
  subgoal
  unfolding to_set_def \<E>_impl_def by (auto simp add: dVs_def)
  subgoal
    unfolding dom_def bal_lookup_def \<b>_impl_def update_def b_list_def
    by auto
  done
                
lemma at_least_2_verts:" 1 < function_generation.N \<E>_impl to_list (prod.fst o id) (prod.snd o id)"
  apply(subst function_generation.N_def[OF selection_functions.function_generation_axioms])
  by(auto simp add: to_list_def \<E>_impl_def)

lemma no_cycle_cond: "no_cycle_cond id \<c>_impl \<E>_impl flow_lookup" 
  by (metis \<E>_def \<c>_def no_cycle no_cycle_cond_def)

lemma correctness_of_algo:"correctness_of_algo id \<E>_impl Pair \<b>_impl"
  using \<E>_impl_basic at_least_2_verts gt_zero multigraph  Vs_is_bal_dom  bal_invar_b[of b_list, simplified sym[OF  \<b>_impl_def]]
  by(auto intro!: correctness_of_algo.intro simp add:  bal_invar_b    \<E>_def)

corollary correctness_of_implementation:
 "return_impl final_state_pair = success \<Longrightarrow>  
        cost_flow_spec.is_Opt fst snd id \<u> (\<E> \<E>_impl) (\<c> \<c>_impl flow_lookup) (\<b> \<b>_impl) 
 (abstract_flow_map final_flow_impl_pair)"
 "return_impl final_state_pair = failure \<Longrightarrow> 
         \<nexists> f. flow_network_spec.isbflow  fst snd id (\<E> \<E>_impl) \<u> f (\<b> \<b>_impl)"
 "return_impl final_state_pair = notyetterm \<Longrightarrow>  
         False"
  using correctness_of_algo.correctness_of_implementation[OF correctness_of_algo no_cycle_cond]
  by(auto simp add: final_state_pair_def final_flow_impl_pair_def)

lemma opt_flow_found: "cost_flow_spec.is_Opt fst snd id \<u> (\<E> \<E>_impl) (\<c> \<c>_impl flow_lookup) (\<b> \<b>_impl)  (abstract_flow_map final_flow_impl_pair)"
  apply(rule correctness_of_implementation(1))
  by eval
end