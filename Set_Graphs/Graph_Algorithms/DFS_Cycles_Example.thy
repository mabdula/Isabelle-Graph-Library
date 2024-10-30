theory DFS_Cycles_Example
  imports DFS_Cycles_Aux DFS_Cycles Set2_Join_RBT "HOL-Data_Structures.RBT_Map" 
begin

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

global_interpretation dfs_cycle_aux: DFS_Aux
  where empty = empty
and delete = delete
and insert = neighb_insert
and isin = isin
and t_set = t_set
and sel = sel
and update = update
and adj_inv = M.invar
and neighb_empty = neighb_empty
and neighb_delete = neighb_delete
and neighb_inv = neighb_inv
and union = neighb_union
and inter = neighb_inter
and diff = neighb_diff
and lookup = lookup
and s = s and G = G for s G
defines initial_state_aux = dfs_cycle_aux.initial_state
and dfs_aux = dfs_cycle_aux.DFS_Aux_impl
and neighbourhood = dfs_cycle_aux.neighbourhood'
  by(auto intro!: DFS_Aux.intro Pair_Graph_Specs_satisfied Set2_satisfied)

global_interpretation dfs_cycles: DFS_Cycles
  where empty = empty
and delete = delete
and insert = neighb_insert
and isin = isin
and t_set = t_set
and sel = sel
and update = update
and adj_inv = M.invar
and neighb_empty = neighb_empty
and neighb_delete = neighb_delete
and neighb_inv = neighb_inv
and union=neighb_union
and inter = neighb_inter
and diff = neighb_diff
and lookup = lookup
and dfs_aux = "\<lambda> s. dfs_aux G (initial_state_aux s)"
and cycle_aux = DFS_Aux_state.cycle
and seen_aux = DFS_Aux_state.seen
and V = V and G = G for V G
defines initial = dfs_cycles.initial_state
and find_cycles_by_dfs = dfs_cycles.DFS_Cycles_impl
  by(auto intro!: DFS_Cycles.intro Pair_Graph_Specs_satisfied Set2_satisfied)

definition "edges = [(0::nat, 1::nat), (0, 2), (2, 3), (2,4), (2,1), (1,5), (5,8), (8,7), (7,1),
                     (7,2), (7,4), (4,3), (3,4), (3,3), (9, 8), (8, 1), (4,5), (5,10)]"

definition "vertices = remdups (map prod.fst edges @ map prod.snd edges)"

definition "nbs v = foldr (\<lambda> x tree. insert x tree) (remdups (map prod.snd (filter (\<lambda> e. prod.fst e = v) edges))) neighb_empty"

definition "G = foldr (\<lambda> x tree. update x (nbs x) tree) vertices  empty"

definition "V = foldr (\<lambda> x tree. neighb_insert x  tree) vertices  neighb_empty"

value edges
value vertices
value "neighb_diff (nbs 1) (nbs 2)"
value G
value V

value "initial_state_aux (1::nat)"
value "dfs_aux G (initial_state_aux (9::nat))"

value "find_cycles_by_dfs V G initial"