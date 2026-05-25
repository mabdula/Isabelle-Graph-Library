theory Tree_Filter
  imports "HOL-Data_Structures.Set2_Join"
begin
(*by Thomas*)
(*Filter as another join-based set operation on binary search trees*)
context Set2_Join
begin

fun filter where
"filter P Leaf = Leaf"|
"filter P (Node l (a, b) r) = 
 (let l' = filter P l;
      r' = filter P r
  in if P a 
     then join l' a r'
     else join2 l' r')"

lemma 
  assumes "inv T \<and> bst T"
  shows invar_filter: "inv (filter P T) \<and> bst (filter P T)" (is ?th1)
  and   set_filter: "set_tree (filter P T) = set_tree T \<inter> Collect P" (is ?th2)
proof-
  have "?th1 \<and> ?th2"
    using assms
  by(induction P T rule: filter.induct)
    (force intro!: inv_join inv_join2 bst_join bst_join2 dest!: inv_Node)+
  thus ?th1 ?th2
    by auto
qed

end
end