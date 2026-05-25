theory Bellman_Ford_Example
  imports Bellman_Ford  "HOL-Data_Structures.RBT_Map"
begin

instantiation prod::(linorder, linorder) linorder
begin

fun less_eq_prod where
 "less_eq_prod (x, y) (a, b) = (if x < a then True 
                                  else if x = a then y \<le> b
                                  else False)"
fun less_prod where
 "less_prod (x, y) (a, b) = (if x < a then True 
                                  else if x = a then y < b
                                  else False)"
instance 
proof(intro Orderings.linorder.intro_of_class  class.linorder.intro
              class.order_axioms.intro class.order.intro class.preorder.intro
              class.linorder_axioms.intro, goal_cases)
  case (1 x y)
  then show ?case 
    by(all \<open>cases x\<close>, all \<open>cases y\<close>)
      (auto split: if_split simp add: less_le_not_le)
next
  case (2 x)
  then show ?case 
    by(all \<open>cases x\<close>)
      (auto split: if_split simp add: less_le_not_le)
next
  case (3 x y z)
  have a: "if (ab::'a) \<le> aa \<and> \<not> aa \<le> ab then True else if ab = aa then (b::'b) \<le> ba else False \<Longrightarrow>
       if aa \<le> ab \<and> \<not> ab \<le> aa then True else if aa = ab then ba \<le> bb else False \<Longrightarrow> b \<le> bb"
    for ab b aa ba bb
    using order.trans by metis
  have b: "if a \<le> aa \<and> \<not> (aa::'a) \<le> a then True else if a = aa then (b::'b) \<le> ba else False \<Longrightarrow>
       if aa \<le> ab \<and> \<not> ab \<le> aa then True else if aa = ab then ba \<le> bb else False \<Longrightarrow> a \<noteq> ab \<Longrightarrow> a \<le> ab "
    for a aa ab ba b bb
    using order.trans by metis
  show ?case
    using 3
    by(all \<open>cases x\<close>, all \<open>cases y\<close>, all \<open>cases z\<close>)
      (auto split: if_split simp add: less_le_not_le intro: a b)
next
  case (4 x y)
  then show ?case 
    apply(all \<open>cases x\<close>, all \<open>cases y\<close>)
    by(simp_all split: if_splits add: less_le_not_le)
next
  case (5 x y)
  then show ?case 
    by(all \<open>cases x\<close>, all \<open>cases y\<close>)
      (auto split: if_split simp add: less_le_not_le)
qed
end

definition "connection_empty = empty"
definition "connection_update = update"
definition "connection_delete = RBT_Map.delete"
definition "connection_lookup = lookup"
definition "connection_invar = M.invar"

interpretation Map_connection: 
   Map connection_empty connection_update connection_delete connection_lookup connection_invar
  using RBT_Map.M.Map_axioms     
  by(auto simp add: connection_update_def connection_empty_def  connection_delete_def
                    connection_lookup_def connection_invar_def)

global_interpretation bellford: bellman_ford_spec where connection_update=connection_update
and connection_empty=connection_empty and connection_lookup=connection_lookup
and connection_delete=connection_delete and connection_invar=connection_invar 
and es= es and vs=vs and edge_costs=edge_costs
for nb f edge_costs es vs
defines search_rev_path_exec = bellford.search_rev_path_exec 
and bellman_ford_init_algo = bellford.bellman_ford_init
and  bellman_ford_algo = bellford.bellman_ford
and relax=bellford.relax        
and follow_map = bellford.follow_map
 using Map_connection.Map_axioms by(auto intro!: bellman_ford_spec.intro)

definition "edges = [(0::nat, 1::nat), (0, 2), (2, 3), (2,4), (2,1), (1,5), (5,8), (8,7), (7,1),
                     (7,2), (7,4), (4,3), (3,4), (3,3), (9, 8), (8, 1), (4,5), (5,10)]"

definition "vertices = remdups (map prod.fst edges @ map prod.snd edges)"

definition "c_list = [((0::nat, 1::nat), 1::real), ((0, 2), 0.5), ((2, 3), 5/8), ((2,4), 3), ((2,1), -1/3),
                      ((1,5), 4), ((5,8), 2), ((8,7), 0.1), ((7,1), 1.3),
                     ((7,2), 3), ((7,4), 3), ((4,3), 2), ((3,4), 1), ((3,3), 0), ((9, 8),2.5),
                      ((8, 1), 0), ((4,5), 2), ((5,10), 3)]"

definition "c_impl = foldr (\<lambda> xy tree. update (prod.fst xy) (prod.snd xy) tree) c_list Leaf"
value "c_impl"

definition "costs x y=  (case (connection_lookup c_impl (x, y)) of Some c => c | None => PInfty)"

value edges
value vertices

text \<open>Select a source\<close>
definition "init = bellman_ford_init_algo vertices 0"

text \<open>Execute the Bellman-Ford loop for $n - 1$ where $n$ is the number of vertices.\<close>
definition "final = bellman_ford_algo costs edges (length vertices - 1) init"
value "inorder final"

text \<open>Recover cheapest path from $0$ to $1$ etc.\<close>
value "(search_rev_path_exec 0 final 1)"

value "(search_rev_path_exec 0 final 10)"

value "(search_rev_path_exec 0 final 4)"

hide_const c_list c_impl edges vertices costs init final

end