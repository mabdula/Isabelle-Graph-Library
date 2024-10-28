theory BFS_Example
  imports BFS_2"HOL-Data_Structures.RBT_Map" Set2_Join_RBT
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
and G = F and t = "t::nat" and s = "s::nat"  for F t s
defines  dfs_initial_state = dfs.initial_state 
and neighbourhood=dfs.Graph.neighbourhood 
and dfs_impl = dfs.DFS_impl
  using Pair_Graph_Specs_satisfied Set2_satisfied 
  by(auto intro!: DFS.intro)