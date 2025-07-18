subsection \<open>Flows in Multigraphs without Capacities\<close>

theory Usage_Multigraph
  imports Instantiation
begin

datatype 'a edge_type = an_edge "('a \<times>'a)" | another_edge "('a \<times> 'a)"

definition "create_edge x y = an_edge (x,y)"
fun fstt where
 "fstt (an_edge e) = fst e"|
 "fstt (another_edge e) = fst e"

fun sndd where
 "sndd (an_edge e) =snd e"|
 "sndd (another_edge e) = snd e" 
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
proof(intro Orderings.linorder.intro_of_class  class.linorder.intro
              class.order_axioms.intro class.order.intro class.preorder.intro
              class.linorder_axioms.intro, goal_cases)
  case (1 x y)
  then show ?case 
    apply(all \<open>cases x\<close>, all \<open>cases y\<close>) 
    apply force
    subgoal for a b
    by(all \<open>cases a\<close>, all \<open>cases b\<close>)
      (auto split: if_split simp add: less_le_not_le)
    subgoal for a b
    by(all \<open>cases a\<close>, all \<open>cases b\<close>)
      (auto split: if_split simp add: less_le_not_le)
    by force
next
  case (2 x)
  then show ?case by(cases x) auto 
next
  case (3 x y z)
  have a: "\<lbrakk> if ab \<le> aa \<and> \<not> aa \<le> ab then True else if ab = aa then b \<le> ba else False ;
       if aa \<le> ab \<and> \<not> ab \<le> aa then True else if aa = ab then ba \<le> bb else False ;
       x = an_edge (ab, b) ; y = an_edge (aa, ba) ; z = an_edge (ab, bb) \<rbrakk> \<Longrightarrow> b \<le> bb"
    for aa ab ba b bb
    using order.trans by metis
  have b: "\<lbrakk> if a \<le> aa \<and> \<not> aa \<le> a then True else if a = aa then b \<le> ba else False ;
       if aa \<le> ab \<and> \<not> ab \<le> aa then True else if aa = ab then ba \<le> bb else False ;
       x = an_edge (a, b) ;
       y = an_edge (aa, ba) ; z = an_edge (ab, bb) ; a \<noteq> ab \<rbrakk> \<Longrightarrow> a \<le> ab"
    for a aa ab b ba bb
    using order.trans by metis
  have c: "\<lbrakk> if ab \<le> aa \<and> \<not> aa \<le> ab then True else if ab = aa then b \<le> ba else False ;
       if aa \<le> ab \<and> \<not> ab \<le> aa then True else if aa = ab then ba \<le> bb else False ;
       x = another_edge (ab, b) ;
       y = another_edge (aa, ba) ; z = another_edge (ab, bb)\<rbrakk> \<Longrightarrow> b \<le> bb"
    for aa ab b ba bb
    using order.trans by metis
  have d: "\<lbrakk>if a \<le> aa \<and> \<not> aa \<le> a then True else if a = aa then b \<le> ba else False ;
       if aa \<le> ab \<and> \<not> ab \<le> aa then True else if aa = ab then ba \<le> bb else False ;
       x = another_edge (a, b) ;
       y = another_edge (aa, ba) ; z = another_edge (ab, bb) ; a \<noteq> ab \<rbrakk> \<Longrightarrow> a \<le> ab"
    for a aa ab b ba bb
    using order.trans by metis
  from 3 show ?case    
    by(all \<open>cases x\<close>, all \<open>cases y\<close>, all \<open>cases z\<close>)
      (auto split: if_split simp add: less_le_not_le intro: a b c d) 
next
  case (4 x y)
  have a: "\<lbrakk>if a \<le> aa \<and> \<not> aa \<le> a then True else if a = aa then b \<le> ba else False ;
       if aa \<le> a \<and> \<not> a \<le> aa then True else if aa = a then ba \<le> b else False ;
       x = an_edge (a, b) ; y = an_edge (aa, ba)\<rbrakk> \<Longrightarrow> a = aa"
    for a aa b ba bb
    by presburger
  have b: "\<lbrakk>if a \<le> aa \<and> \<not> aa \<le> a then True else if a = aa then b \<le> ba else False ;
       if aa \<le> a \<and> \<not> a \<le> aa then True else if aa = a then ba \<le> b else False ;
       x = an_edge (a, b) ;y = an_edge (aa, ba)\<rbrakk> \<Longrightarrow> b = ba"
    for a aa b ba
    by (metis order_antisym_conv)
  have c: "\<lbrakk>if a \<le> aa \<and> \<not> aa \<le> a then True else if a = aa then b \<le> ba else False ;
       if aa \<le> a \<and> \<not> a \<le> aa then True else if aa = a then ba \<le> b else False ;
       x = another_edge (a, b) ; y = another_edge (aa, ba) \<rbrakk> \<Longrightarrow> b = ba"
    for a aa b ba
    by (metis order_antisym_conv)
  have d: "\<lbrakk>if a \<le> aa \<and> \<not> aa \<le> a then True else if a = aa then b \<le> ba else False ;
       if aa \<le> a \<and> \<not> a \<le> aa then True else if aa = a then ba \<le> b else False ;
       x = another_edge (a, b) ; y = another_edge (aa, ba)\<rbrakk> \<Longrightarrow> a = aa"
    for a aa b ba
    by presburger
  from 4 show ?case 
    by(all \<open>cases x\<close>, all \<open>cases y\<close>)
      (auto split: if_split simp add: less_le_not_le intro: a b c d)
next
  case (5 x y)
  then show ?case 
    by(all \<open>cases x\<close>, all \<open>cases y\<close>) 
     (force intro: le_cases3)+
qed
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

definition "final_state_multi = final_state fstt sndd create_edge \<E>_impl \<c>_impl \<b>_impl flow_lookup"
value final_state_multi

definition "final_flow_impl_multi =  final_flow_impl fstt sndd create_edge \<E>_impl \<c>_impl \<b>_impl flow_lookup"
value final_flow_impl_multi

definition "final_forest = (\<FF> final_state_multi)"

value "inorder final_flow_impl_multi"
value "map (\<lambda> (x, y). (x, inorder y)) (inorder final_forest)"
value "inorder (conv_to_rdg final_state_multi)"
value "inorder (not_blocked final_state_multi)"

lemma no_cycle: "closed_w (make_pair fstt sndd ` \<E> \<E>_impl) (map (make_pair fstt sndd) C)
          \<Longrightarrow> (set C \<subseteq> \<E> \<E>_impl) \<Longrightarrow>
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

lemma multigraph: "multigraph fstt sndd create_edge (\<E> \<E>_impl)"
  using \<E>_impl_basic(2,3)
  by(auto intro!: multigraph.intro simp add: create_edge_def  selection_functions.\<E>_def)

lemma Vs_is: "dVs (make_pair fstt sndd ` to_set \<E>_impl) = {1,2,3,4,5,6}"
  unfolding to_set_def \<E>_impl_def 
  by (auto simp add: dVs_def make_pair_def multigraph_spec.make_pair_def)

lemma Vs_is_bal_dom: "dVs (make_pair fstt sndd` to_set \<E>_impl) = dom (bal_lookup \<b>_impl)" 
  apply(rule trans[OF Vs_is])
  by(auto simp add: dom_def bal_lookup_def \<b>_impl_def update_def b_list_def)
                
lemma at_least_2_verts:" 1 < function_generation.N \<E>_impl to_list fstt sndd"
  apply(subst function_generation.N_def[OF selection_functions.function_generation_axioms])
  by(auto simp add: to_list_def \<E>_impl_def)

lemma no_cycle_cond: "no_cycle_cond fstt sndd \<c>_impl \<E>_impl flow_lookup" 
  using no_cycle
  by(auto simp add: no_cycle_cond_def \<c>_def make_pair_def \<E>_def) 

lemma correctness_of_algo:"correctness_of_algo fstt sndd \<E>_impl create_edge \<b>_impl"
  using \<E>_impl_basic at_least_2_verts gt_zero multigraph Vs_is_bal_dom
  by (auto intro!: correctness_of_algo.intro 
         simp add: \<b>_impl_def bal_invar_b Vs_is_bal_dom  \<E>_def make_pair_def)

corollary correctness_of_implementation:
 "return final_state_multi = success \<Longrightarrow>  
        cost_flow_spec.is_Opt fstt sndd \<u> (\<E> \<E>_impl) (\<c> \<c>_impl flow_lookup) (\<b> \<b>_impl) 
 (abstract_flow_map final_flow_impl_multi)"
 "return final_state_multi = failure \<Longrightarrow> 
         \<nexists> f. flow_network_spec.isbflow  fstt sndd (\<E> \<E>_impl) \<u>  f (\<b> \<b>_impl)"
 "return final_state_multi = notyetterm \<Longrightarrow>  
         False"
  using correctness_of_algo.correctness_of_implementation[OF correctness_of_algo no_cycle_cond]
  by(auto simp add: final_state_multi_def final_flow_impl_multi_def)

lemma opt_flow_found: "cost_flow_spec.is_Opt fstt sndd \<u>  (\<E> \<E>_impl) (\<c> \<c>_impl flow_lookup) (\<b> \<b>_impl)  (abstract_flow_map final_flow_impl_multi)"
  apply(rule correctness_of_implementation(1))
  by eval
end