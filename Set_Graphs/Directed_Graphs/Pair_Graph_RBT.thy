theory Pair_Graph_RBT
imports Pair_Graph_Specs "HOL-Data_Structures.RBT_Set" "HOL-Data_Structures.RBT_Map"
       "Set2_Join_RBT" Tree_Filter
begin

lemma Map_axioms_as_needed: "Map \<langle>\<rangle> RBT_Map.update RBT_Map.delete lookup M.invar"
  using M.Map_axioms
  by(auto simp add: RBT_Set.empty_def)

abbreviation "vset_empty == RBT_Set.empty"
abbreviation "vset_union == union_rbt"
abbreviation "vset_insert == insert_rbt"
abbreviation "vset_diff == diff_rbt"
abbreviation "vset_delete == delete_rbt"
abbreviation "vset_inter == inter_rbt"
abbreviation "t_set == Tree2.set_tree"
definition "vset_inv =  (\<lambda>t. (invc t \<and> invh t) \<and> Tree2.bst t)"

definition "map_empty = (Leaf:: (('a \<times> ('a \<times> color) tree) \<times> color) tree)"
definition "edge_map_update = (update::('a::linorder)
   \<Rightarrow> ('a \<times> color) tree
      \<Rightarrow> (('a \<times> ('a \<times> color) tree) \<times> color) tree
         \<Rightarrow> (('a\<times> ('a \<times> color) tree) \<times> color) tree)"
definition "adj_inv = M.invar"


fun sel where
"sel Leaf = undefined" |
"sel (B l a r) = a"|
"sel (R l a r) = a"
             
interpretation set: Set Leaf insert_rbt delete_rbt isin Tree2.set_tree vset_inv
  apply unfold_locales
  by (simp add: empty_def vset_inv_def isin_set_tree RBT.set_isin RBT.set_tree_insert RBT.set_insert
                RBT.set_tree_insert RBT.set_tree_delete RBT.set_delete RBT.set_delete 
                RBT.invar_insert RBT.invar_insert RBT.invar_insert RBT.inv_delete RBT.invar_delete
                RBT.inv_delete)+

interpretation S_C: Set_Choose Leaf insert_rbt RBT.delete isin vset_inv Tree2.set_tree sel
  apply unfold_locales
proof(goal_cases)
  case (1 s)
  then show ?case
    by(induction rule: sel.induct) (auto simp: empty_def)
qed

interpretation G: Pair_Graph_Specs RBT_Set.empty RBT_Map.delete lookup insert_rbt isin Tree2.set_tree sel
     update M.invar Leaf RBT.delete vset_inv
  apply(rule Pair_Graph_Specs.intro)
  subgoal apply unfold_locales.
  apply unfold_locales .

fun fold_rbt where
"fold_rbt f Leaf acc = acc"|
"fold_rbt f (B l x r) acc= f x (fold_rbt f l (fold_rbt f r acc))"|
"fold_rbt f (R l x r) acc= f x (fold_rbt f l (fold_rbt f r acc))"

lemma fold_rbt_is_foldr_of_preorder:"fold_rbt f T acc = foldr f (map fst (preorder T)) acc "
  by(induction f T acc arbitrary: rule: fold_rbt.induct) auto

text \<open>We produce an adjacency map representing a graph from a list of edges.\<close>

definition "vertices edges = remdups (map prod.fst edges @ map prod.snd edges)"

definition "nbs edges v = foldr (\<lambda> x tree. insert x tree) (remdups (map prod.snd (filter (\<lambda> e. prod.fst e = v) edges))) Leaf"

definition "a_graph edges = foldr (\<lambda> x tree. update x (nbs edges x) tree) (vertices edges) empty"

definition "a_edge_set edges = foldr (\<lambda> x tree. insert x tree) edges empty"
end