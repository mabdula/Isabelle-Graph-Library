theory Hungarian_Example
  imports Hungarian_Method_Instantiation  Directed_Set_Graphs.Pair_Graph_RBT
          WBP_Matching_Exec
begin

section \<open>6 Matchings on Bipartite Example Graph\<close>

definition "edges_and_costs = [(0::nat, 1::nat, 1::real), (0,3, -10), 
(0,5, 2/3), (0,7, 1/87), (2,5, -12), (2,9, 100), (2,1, 2.5), (4,5, 2+1/7), 
(4,3, -1.3), (4,7, 2.4),
   (6,1, 1.8+1/9), (6,9, 200), (8, 9, 10000), (8,1, 6.2), (0, 9, -100),
 (2, 7, -100), (2,3,-40), (2,9,-100), (4,9, -100)]"

definition "edges = zip (map fst edges_and_costs) (map (fst o snd) edges_and_costs)"

definition "c_list = zip (zip (map fst edges_and_costs)  (map (fst o snd) edges_and_costs)) 
                   (map (snd o snd) edges_and_costs)"

definition "c_impl = foldr (\<lambda> xy tree.
              update (prod.swap (prod.fst xy)) (prod.snd xy)
              ( update (prod.fst xy) (prod.snd xy) tree))
              c_list Leaf"

definition "weights = (\<lambda> u v. abstract_real_map (lookup c_impl) (u, v))"

definition "bipartite_test = filter odd (map fst edges) @ filter even (map snd edges)"
value bipartite_test

definition "G = a_graph edges"

definition "left = foldr (\<lambda> x tree. RBT.insert x tree) (map fst edges_and_costs) Leaf"
definition "right = foldr (\<lambda> x tree. RBT.insert x tree) (map (fst o snd) edges_and_costs) Leaf"
thm hungarian_def

definition "final_min_perfect_matching 
    = compute_min_weight_perfect_matching left right weights (lookup G)"

value "final_min_perfect_matching"
value "if final_min_perfect_matching = None 
        then Nil else inorder (the final_min_perfect_matching)"

definition "final_max_perfect_matching 
    = compute_max_weight_perfect_matching left right weights (lookup G)"

value "final_max_perfect_matching"
value "if final_max_perfect_matching = None 
        then Nil else inorder (the final_max_perfect_matching)"

definition "final_min_matching 
    = compute_min_weight_matching left right weights (lookup G)"

value "final_min_matching"
value "inorder final_min_matching"

definition "final_max_matching 
    = compute_max_weight_matching left right weights (lookup G)"

value "final_max_matching"
value "inorder final_max_matching"

definition "final_min_max_matching 
    = compute_min_weight_max_card_matching left right weights (lookup G)"

value "final_min_max_matching"
value "inorder final_min_max_matching"

definition "final_max_max_matching 
    = compute_max_weight_max_card_matching left right weights (lookup G)"

value "final_max_max_matching"
value "inorder final_max_max_matching"
end