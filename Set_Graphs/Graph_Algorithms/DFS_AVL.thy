theory DFS_AVL
  imports DFS Pair_Graph_AVL
begin

interpretation DFS_AVL: DFS
  where empty=AVL_Set_Code.empty and update=update and delete = AVL_Map.delete and
        lookup =lookup and adj_inv = M.invar  and neighb_empty = AVL_Set_Code.empty and 
        insert = AVL_Set_Code.insert and neighb_delete = AVL_Set_Code.delete and isin = isin and 
        t_set = "set o inorder" and neighb_inv = S.invar and sel = avl_sel
  apply unfold_locales
  sledgehammer

  apply(simp add: DFS_def)
  apply(intro conjI)
  subgoal using G.Pair_Graph_Specs_axioms .
  subgoal sorry 
  subgoal apply unfold_locales 
    subgoal apply(auto simp: G.graph_inv_def)

(* subgoal  apply unfold_locales
    apply(simp add: M.invar_def)
    by (metis avl_fold_works avl_map_dom_inorder)
  done*)
  done


end