theory Pair_Graph_AVL                                                  
  imports Pair_Graph_Specs "HOL-Data_Structures.AVL_Set" "HOL-Data_Structures.AVL_Map"
begin

fun avl_sel where
  "avl_sel Leaf = undefined"
| "avl_sel (Node _ (a,_) _) = a"

lemma avl_sel_works: "t \<noteq> empty \<Longrightarrow> avl_sel t \<in> (set o inorder) t"
  by (induction t) (auto simp: empty_def)

fun avl_fold_keys::"('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> (('a \<times> 'd) \<times> 'c) tree \<Rightarrow> 'b \<Rightarrow> 'b" where
  "avl_fold_keys f Leaf acc = acc"
| "avl_fold_keys f (Node l (a, h) r) acc = avl_fold_keys f r (f (fst a) (avl_fold_keys f l acc))"

lemma avl_fold_works: "avl_fold_keys f t acc = fold f (map fst (inorder t)) acc"
  by(induction t arbitrary: acc) auto

lemma dom_map_of_fst: "dom (map_of xs) = set (map fst xs)"
  by(induction xs) (fastforce simp: map_of_def dom_def image_def)+


lemma avl_map_dom_inorder: "sorted1 (inorder m) \<Longrightarrow> dom (lookup m) = set (map fst (inorder m))"
  using lookup_map_of
  by (metis dom_map_of_fst ext)

interpretation S_C: Set_Choose 
where empty = AVL_Set_Code.empty and insert = insert and delete = AVL_Set_Code.delete and
      isin = isin and t_set = "set o inorder" and invar = S.invar and sel = avl_sel
  apply(simp add: Set_Choose_def)
  apply(intro conjI)
  subgoal using S.Set_axioms[unfolded] by(auto simp add: S.set_def S.invar_def)
  subgoal apply unfold_locales subgoal for s by (cases s)  (auto dest!: avl_sel_works)
  done
  done

(*
interpretation G: Adj_Map_Specs
  where empty=AVL_Set_Code.empty and update=update and delete = AVL_Map.delete and
        lookup =lookup and adjmap_inv = M.invar  and vset_empty = AVL_Set_Code.empty and 
        vset_insert = insert and vset_delete = AVL_Set_Code.delete and isin = isin and 
        t_set = "set o inorder" and vset_inv = S.invar and sel = avl_sel 
  apply(simp add: Adj_Map_Specs_def)
  apply(intro conjI)
  subgoal using M.Map_axioms .
  subgoal using S_C.Set_Choose_axioms .
(* subgoal  apply unfold_locales
    apply(simp add: M.invar_def)
    by (metis avl_fold_works avl_map_dom_inorder)
  done*)
  done
*)

interpretation G: Pair_Graph_Specs
  where empty=AVL_Set_Code.empty and update=update and delete = AVL_Map.delete and
        lookup =lookup and adjmap_inv = M.invar  and vset_empty = AVL_Set_Code.empty and
        insert = AVL_Set_Code.insert and vset_delete = AVL_Set_Code.delete and isin = isin and
        t_set = "set o inorder" and vset_inv = S.invar and sel = avl_sel
  apply unfold_locales.

end