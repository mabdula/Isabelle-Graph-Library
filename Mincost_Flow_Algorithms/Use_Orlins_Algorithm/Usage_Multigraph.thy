subsection \<open>Flows in Multigraphs without Capacities\<close>

theory Usage_Multigraph
  imports Instantiation
begin

datatype 'a edge_type = an_edge "('a \<times>'a)" | another_edge "('a \<times> 'a)"

definition "create_edge x y = an_edge (x,y)"
fun make_pair where
 "make_pair (an_edge e) = e"|
 "make_pair (another_edge e) = e"

  
  instantiation edge_type::(linorder) linorder
begin

fun less_eq_edge_type where
 "less_eq_edge_type (an_edge (x, y)) (another_edge (a, b)) = True" |
 "less_eq_edge_type (another_edge (x, y)) (an_edge (a, b)) = False" |
 "less_eq_edge_type (an_edge (x, y)) (an_edge (a, b)) = ((x, y) \<le> (a, b))"|
 "less_eq_edge_type (another_edge (x, y)) (another_edge (a, b)) = ((x, y) \<le> (a, b))"

fun less_edge_type where
 "less_edge_type (an_edge (x, y)) (another_edge (a, b)) = True" |
 "less_edge_type (another_edge (x, y)) (an_edge (a, b)) = False" |
 "less_edge_type (an_edge (x, y)) (an_edge (a, b)) = ((x, y) < (a, b))"|
 "less_edge_type (another_edge (x, y)) (another_edge (a, b)) = ((x, y) < (a, b))"
instance 
  apply(intro Orderings.linorder.intro_of_class  class.linorder.intro
              class.order_axioms.intro class.order.intro class.preorder.intro
              class.linorder_axioms.intro)
  subgoal for x y 
    apply(all \<open>cases x\<close>, all \<open>cases y\<close>) 
    apply force
    subgoal for a b
    by(all \<open>cases a\<close>, all \<open>cases b\<close>)
      (auto split: if_split simp add: less_le_not_le)
    subgoal for a b
    by(all \<open>cases a\<close>, all \<open>cases b\<close>)
      (auto split: if_split simp add: less_le_not_le)
  by force
  subgoal for x
    by(cases x) auto  
  subgoal for x y z
    apply(all \<open>cases x\<close>, all \<open>cases y\<close>, all \<open>cases z\<close>)
    apply(auto split: if_split simp add: less_le_not_le)
    using order.trans by metis+
  subgoal for x y 
    apply(all \<open>cases x\<close>, all \<open>cases y\<close>)
    apply(auto split: if_split simp add: less_le_not_le)
    apply presburger+
    by (metis order_antisym_conv)+
  subgoal for x y 
    by(all \<open>cases x\<close>, all \<open>cases y\<close>) 
     (force intro: le_cases3)+
  done
end


definition "\<E>_impl = map an_edge [(1::nat, 2::nat), (1,3), (3,2), (2,4), (2,5),
(3,5), (4,6), (6,5), (2,6)] @[another_edge (1,2)]"
value "\<E>_impl"

definition "b_list =  [(1::nat,128::real), (2,0), (3,1), (4,-33), (5,-32), (6,-64)]"

definition "\<b>_impl = foldr (\<lambda> xy tree. update (prod.fst xy) (prod.snd xy) tree) b_list Leaf"
value "\<b>_impl"

definition "c_list = [(an_edge (1::nat, 2::nat), 1::real),
 (an_edge(1,3), 4), (an_edge(3,2), 2), (an_edge(2,4), 3), (an_edge(2,5), 1),
(an_edge(3,5), 5), (an_edge(4,6), 2), (an_edge(6,5), 1), (an_edge(2,6), 9)]@[(another_edge (1,2), 0.0001)]"

definition "\<c>_impl = foldr (\<lambda> xy tree. update (prod.fst xy) (prod.snd xy) tree) c_list Leaf"
value "\<c>_impl"

term "initial_impl make_pair"

context
begin
definition "edges = [(0::nat, 1::nat), (0, 2), (2, 3), (2,4), (2,1), (1,5), (5,8), (8,7), (7,1),
                     (7,2), (7,4), (4,3), (3,4), (3,3), (9, 8), (8, 1), (4,5), (5,10)]"

definition "G = a_graph edges"

value edges
value G
value "dfs_initial_state (1::nat)"   
value "dfs_impl G 9 (dfs_initial_state 0)"
value "vset_diff (nbs edges (1::nat)) (nbs edges (2::nat))"
end

context begin
value "lookup G 1"
value "lookup G 12"
value "lookup' (Replace G) 12"
value "lookup' (Replace G) 1"
value "lookup' (edge_map_update' 1 (list_to_rbt [1::nat,2,3,4,5,6,7,8]) (Replace G)) 100"
value "remove_all_empties (edge_map_update' 1 (list_to_rbt [1::nat,2,3,4,5,6,7,8]) (Replace G))"
value "lookup (remove_all_empties (edge_map_update' 1 (list_to_rbt [1::nat,2,3,4,5,6,7,8]) (Replace G))) 100"
end


definition "final_state_multi = final_state make_pair create_edge \<E>_impl \<c>_impl \<b>_impl flow_lookup"
value final_state_multi

definition "final_flow_impl_multi =  final_flow_impl make_pair create_edge \<E>_impl \<c>_impl \<b>_impl flow_lookup"
value final_flow_impl_multi

definition "final_forest = remove_all_empties(\<FF>_impl final_state_multi)"

value "inorder final_flow_impl_multi"
value "map (\<lambda> (x, y). (x, inorder y)) (inorder final_forest)"
value "inorder (conv_to_rdg_impl final_state_multi)"
value "inorder (not_blocked_impl final_state_multi)"


lemma no_cycle: "closed_w (make_pair ` \<E> \<E>_impl) (map make_pair C) \<Longrightarrow> (set C \<subseteq> \<E> \<E>_impl) \<Longrightarrow>
        foldr (\<lambda>e acc. acc + \<c> \<c>_impl flow_lookup e) C 0 < 0 \<Longrightarrow> False"
proof(goal_cases)
  case 1
  have C_in_E:"set C \<subseteq> set \<E>_impl"
    using 1 \<E>_impl_def 
    by (simp add: subset_eq to_set_def  selection_functions.\<E>_def)
  moreover have "List.filter (\<lambda> e. \<c>  \<c>_impl flow_lookup e > 0) \<E>_impl = \<E>_impl"
    unfolding selection_functions.\<c>_def flow_lookup_def \<c>_impl_def update_def \<E>_impl_def c_list_def
    by simp
  moreover hence "e \<in> set \<E>_impl \<Longrightarrow> \<c> \<c>_impl flow_lookup e > 0" for e
    by (meson filter_id_conv)
  ultimately have "foldr (\<lambda>e acc. acc + \<c> \<c>_impl flow_lookup e) C 0 \<ge> 0"
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

lemma multigraph: "multigraph (prod.fst o make_pair) (prod.snd o  make_pair) make_pair create_edge (\<E> \<E>_impl)"
  apply(rule multigraph.intro)
  subgoal for e x y
    by(cases e) auto
  subgoal for x y
    by (simp add: create_edge_def)
   apply (simp add: \<E>_impl_basic(3))
  using selection_functions.\<E>_def \<E>_impl_basic(2) by blast


lemma Vs_is: "dVs (make_pair ` to_set \<E>_impl) = {1,2,3,4,5,6}"
  unfolding to_set_def \<E>_impl_def by (auto simp add: dVs_def)

lemma Vs_is_bal_dom: "dVs (make_pair ` to_set \<E>_impl) = dom (bal_lookup \<b>_impl)" 
  apply(rule trans[of  _ "{1,2,3,4,5,6}"])
  subgoal
  unfolding to_set_def \<E>_impl_def by (auto simp add: dVs_def)
  subgoal
    unfolding dom_def bal_lookup_def \<b>_impl_def update_def b_list_def
    by auto
  done
                
lemma at_least_2_verts:" 1 < function_generation.N \<E>_impl to_list (prod.fst o make_pair) (prod.snd o make_pair)"
  apply(subst function_generation.N_def[OF selection_functions.function_generation_axioms])
  by(auto simp add: to_list_def \<E>_impl_def)

lemma no_cycle_cond: "no_cycle_cond make_pair \<c>_impl \<E>_impl flow_lookup" 
  by (metis \<E>_def \<c>_def no_cycle no_cycle_cond_def)

lemma correctness_of_algo:"correctness_of_algo make_pair \<E>_impl create_edge \<b>_impl"
  using \<E>_impl_basic at_least_2_verts gt_zero multigraph
  by (auto intro!: correctness_of_algo.intro simp add: \<b>_impl_def bal_invar_b Vs_is_bal_dom  \<E>_def)
 
corollary correctness_of_implementation:
 "return_impl final_state_multi = success \<Longrightarrow>  
        cost_flow_network.is_Opt (fst o make_pair) (snd o make_pair) make_pair \<u> (\<c> \<c>_impl flow_lookup) (\<E> \<E>_impl) (\<b> \<b>_impl) 
 (abstract_flow_map final_flow_impl_multi)"
 "return_impl final_state_multi = failure \<Longrightarrow> 
         \<nexists> f. flow_network.isbflow  (fst o make_pair) (snd o make_pair) make_pair \<u>  (\<E> \<E>_impl) f (\<b> \<b>_impl)"
 "return_impl final_state_multi = notyetterm \<Longrightarrow>  
         False"
  using correctness_of_algo.correctness_of_implementation[OF correctness_of_algo no_cycle_cond]
  by(auto simp add: final_state_multi_def final_flow_impl_multi_def)

lemma opt_flow_found: "cost_flow_network.is_Opt (fst o make_pair) (snd o make_pair) make_pair \<u> (\<c> \<c>_impl flow_lookup) (\<E> \<E>_impl) (\<b> \<b>_impl)  (abstract_flow_map final_flow_impl_multi)"
  apply(rule correctness_of_implementation(1))
  by eval
end