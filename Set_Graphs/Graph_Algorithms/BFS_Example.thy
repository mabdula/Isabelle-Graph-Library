theory BFS_Example
  imports BFS_Subprocedures "HOL-Data_Structures.RBT_Map" Set2_Join_RBT
begin

fun fold_rbt where
"fold_rbt f Leaf acc = acc"|
"fold_rbt f (B l x r) acc= f x (fold_rbt f l (fold_rbt f r acc))"|
"fold_rbt f (R l x r) acc= f x (fold_rbt f l (fold_rbt f r acc))"

lemma fold_rbt_is_foldr_of_preorder:"fold_rbt f T acc = foldr f (map fst (preorder T)) acc "
  by(induction f T acc arbitrary: rule: fold_rbt.induct) auto

definition "t_set \<equiv> Tree2.set_tree"
definition "neighb_inv \<equiv>  (\<lambda>t. (invc t \<and> invh t) \<and> Tree2.bst t)"
definition "neighb_empty = Leaf"

notation neighb_empty ("\<emptyset>\<^sub>N")

fun sel where
"sel Leaf = undefined" |
"sel (B l a r) = a"|
"sel (R l a r) = a"

lemma Set_satisified: "Set neighb_empty neighb_insert neighb_delete isin t_set neighb_inv"
  using  RBT.Set_axioms 
  by(auto simp add: neighb_empty_def neighb_delete_def neighb_insert_def t_set_def neighb_inv_def)

lemma Set_Choose_axioms: "Set_Choose_axioms neighb_empty isin sel"
  apply(rule Set_Choose_axioms.intro)
  unfolding neighb_empty_def 
  subgoal for s
    by(induction rule: sel.induct) auto
  done
 
lemma Set_Choose_satisfied:"Set_Choose neighb_empty neighb_insert neighb_delete isin neighb_inv t_set sel"
  using Set_satisified Set_Choose_axioms
  by(auto simp add: Set_Choose_def)

notation empty ("\<emptyset>\<^sub>G")

lemma Map_satisfied: "Map neighb_empty update RBT_Map.delete lookup M.invar"
  using RBT_Map.M.Map_axioms
  by(auto simp add: Map_def M.invar_def neighb_empty_def  RBT_Set.empty_def )

lemma Pair_Graph_Specs_satisfied: "Pair_Graph_Specs empty RBT_Map.delete lookup neighb_insert isin t_set sel
     update M.invar neighb_empty neighb_delete neighb_inv"
  using Set_Choose_satisfied Map_satisfied
  unfolding Pair_Graph_Specs_def
  by(auto simp add: Pair_Graph_Specs_def empty_def  neighb_empty_def)

lemma Set2_satisfied: "Set2 neighb_empty neighb_delete isin t_set neighb_inv neighb_insert neighb_union
     neighb_inter neighb_diff"
  using  Set2_Join_RBT.RBT.Set2_axioms 
  by(auto simp add: RBT_Set.empty_def neighb_empty_def neighb_delete_def t_set_def neighb_inv_def neighb_insert_def
                    neighb_union_def neighb_inter_def neighb_diff_def)

definition "fold_neighb = (fold_rbt)"
definition "fold_adj = (fold_rbt)"

lemma prderorder_set:"set (map fst (preorder N)) = Tree2.set_tree N"
  by(induction N rule: preorder.induct)auto

lemma preorder_witness:"set (map fst (preorder N)) = t_set N \<and> fold_rbt f N acc = foldr f (map fst (preorder N)) acc"
  unfolding fold_rbt_is_foldr_of_preorder prderorder_set t_set_def by auto

lemma rbt_fold_spec:"neighb_inv N \<Longrightarrow> \<exists>xs. set xs = t_set N \<and> fold_rbt f N acc = foldr f xs acc"
  using preorder_witness by metis

lemma BFS_subprocedures_axioms: "BFS_subprocedures_axioms t_set neighb_inv fold_neighb fold_adj"
 by(auto intro!: BFS_subprocedures_axioms.intro rbt_fold_spec
           simp add: fold_neighb_def fold_adj_def )

global_interpretation bfs_subprocedures: BFS_subprocedures
where insert = neighb_insert 
and sel = sel 
and neighb_empty = neighb_empty 
and diff = neighb_diff 
and lookup = lookup 
and empty = empty 
and delete=delete 
and isin = isin 
and t_set=t_set
and update=update 
and adj_inv = M.invar
and neighb_delete= neighb_delete
and neighb_inv = neighb_inv 
and union=neighb_union 
and inter=neighb_inter 
and fold_neighb = fold_neighb
and fold_adj=fold_adj
and G = G for G 
defines next_frontier = bfs_subprocedures.next_frontier
and expand_tree = bfs_subprocedures.expand_tree
by(auto intro!: BFS_subprocedures.intro 
           simp add: Pair_Graph_Specs_satisfied  Set2_satisfied BFS_subprocedures_axioms )

lemma BFS_axioms:"BFS_axioms isin t_set M.invar \<emptyset>\<^sub>N neighb_inv lookup G (expand_tree G) (next_frontier G)"
 by(fastforce intro!: BFS_axioms.intro 
       simp add: bfs_subprocedures.expand_tree  bfs_subprocedures.next_frontier)

global_interpretation bfs: BFS
where insert = neighb_insert 
and sel = sel 
and neighb_empty = neighb_empty 
and diff = neighb_diff 
and lookup = lookup 
and empty = empty 
and delete=delete 
and isin = isin 
and t_set=t_set
and update=update 
and adj_inv = M.invar
and neighb_delete= neighb_delete
and neighb_inv = neighb_inv 
and union=neighb_union 
and inter=neighb_inter 
and expand_tree = "expand_tree G"
and next_frontier = "next_frontier G"
and G = G and srcs = srcs for G srcs
defines bfs_initial_state = "bfs.initial_state"
and bfs_impl = bfs.BFS_impl
  by(auto intro!: BFS.intro simp add: Pair_Graph_Specs_satisfied Set2_satisfied BFS_axioms)

definition "edges = [(0::nat, 1::nat), (0, 2), (2, 3), (2,4), (2,1), (1,5), (5,8), (8,7), (7,1),
                     (7,2), (7,4), (4,3), (3,4), (3,3), (9, 8), (8, 1), (4,5), (5,10)]"

definition "vertices = remdups (map prod.fst edges @ map prod.snd edges)"

definition "nbs v = foldr (\<lambda> x tree. insert x tree) (remdups (map prod.snd (filter (\<lambda> e. prod.fst e = v) edges))) neighb_empty"

definition "G = foldr (\<lambda> x tree. update x (nbs x) tree) vertices  empty"

definition "src_list = [9::nat]"

definition "srcs =  foldr (\<lambda> x tree. insert x tree) src_list empty"

term bfs_initial_state
term bfs_impl

value edges
value vertices
value "neighb_diff (nbs 1) (nbs 2)"
value G
value "bfs_initial_state srcs"   
value "bfs_impl G (bfs_initial_state srcs)"
end