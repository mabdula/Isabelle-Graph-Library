theory Pair_Graph_RBT
imports Pair_Graph_Specs "HOL-Data_Structures.RBT_Set" "HOL-Data_Structures.RBT_Map"
       "Verified_SAT_Based_AI_Planning.Set2_Join_RBT"
begin

definition "neighb_inv \<equiv>  (\<lambda>t. (invc t \<and> invh t) \<and> Tree2.bst t)"

fun sel where
"sel Leaf = undefined" |
"sel (B l a r) = a"|
"sel (R l a r) = a"
             
interpretation set: Set Leaf insert_rbt delete_rbt isin Tree2.set_tree neighb_inv
  apply unfold_locales
  by (simp add: empty_def neighb_inv_def isin_set_tree RBT.set_isin RBT.set_tree_insert RBT.set_insert
                RBT.set_tree_insert RBT.set_tree_delete RBT.set_delete RBT.set_delete 
                RBT.invar_insert RBT.invar_insert RBT.invar_insert RBT.inv_delete RBT.invar_delete
                RBT.inv_delete)+

interpretation S_C: Set_Choose Leaf insert_rbt RBT.delete isin neighb_inv Tree2.set_tree sel
  apply unfold_locales
proof(goal_cases)
  case (1 s)
  then show ?case
    by(induction rule: sel.induct) (auto simp: empty_def)
qed

interpretation G: Pair_Graph_Specs RBT_Set.empty RBT_Map.delete lookup insert_rbt isin Tree2.set_tree sel
     update M.invar Leaf RBT.delete neighb_inv
  apply(rule Pair_Graph_Specs.intro)
  subgoal apply unfold_locales.
  apply unfold_locales .

fun fold_rbt where
"fold_rbt f Leaf acc = acc"|
"fold_rbt f (B l x r) acc= f x (fold_rbt f l (fold_rbt f r acc))"|
"fold_rbt f (R l x r) acc= f x (fold_rbt f l (fold_rbt f r acc))"

lemma fold_rbt_is_foldr_of_preorder:"fold_rbt f T acc = foldr f (map fst (preorder T)) acc "
  by(induction f T acc arbitrary: rule: fold_rbt.induct) auto

end