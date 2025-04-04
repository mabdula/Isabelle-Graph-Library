theory Kruskal_Greedy
  imports Matroids_Greedy.Best_In_Greedy Spanning_Trees Graph_Algorithms.DFS_Cycles_Aux
    Graph_Algorithms.DFS_Cycles Insertion_Sort_Desc Graphs_Matroids_Encoding
    "HOL-Data_Structures.Set2_Join_RBT" "HOL-Data_Structures.RBT_Map" "HOL-Library.Product_Lexorder"
begin


subsection \<open>Instantiations for Kruskal's algorithm\<close>

abbreviation "rbt_inv == ( \<lambda>t. (invc t \<and> invh t) \<and> Tree2.bst t)"

fun rbt_sel where
  "rbt_sel Leaf = undefined"
| "rbt_sel (Node _ (a,_) _) = a"

lemma rbt_sel_correct:
  "t \<noteq> empty \<Longrightarrow> rbt_sel t \<in> (set o inorder) t"
  by (induction t) (auto simp: empty_def)

interpretation Set_Choose_RBT: Set_Choose
  where empty = "\<langle>\<rangle>" and insert = insert_rbt and delete = delete_rbt and
    isin = isin and t_set = "Tree2.set_tree" and invar = "rbt_inv::(('v::linorder) rbt \<Rightarrow> bool)" and
    sel = rbt_sel
  apply(simp add: Set_Choose_def)
  apply(intro conjI)
  subgoal
    using RBT.Set_axioms[unfolded] by(auto simp add: S.set_def S.invar_def)
  subgoal apply unfold_locales subgoal for s by (cases s) (auto dest!: rbt_sel_correct)
  done
  done


interpretation Pair_Graph_U_RBT: Pair_Graph_U_Specs
  where empty = RBT_Set.empty and update = update and delete = RBT_Map.delete and
    lookup = lookup and adjmap_inv = "M.invar" and vset_empty = "\<langle>\<rangle>" and
    insert = insert_rbt and vset_delete = delete_rbt and vset_inv = "rbt_inv::(('v::linorder) rbt \<Rightarrow> bool)" and
    isin = isin and t_set = "Tree2.set_tree" and sel = rbt_sel
  apply(simp add: Pair_Graph_U_Specs_def Pair_Graph_Specs_def)
  using M.Map_axioms Set_Choose_RBT.Set_Choose_axioms by simp

interpretation DFS_Aux_Interp: DFS_Aux
  where empty = RBT_Set.empty and update = update and delete = RBT_Map.delete and
    lookup = lookup and adjmap_inv = "M.invar" and vset_empty = "\<langle>\<rangle>" and
    insert = insert_rbt and vset_delete = delete_rbt and vset_inv = "rbt_inv::(('v::linorder) rbt \<Rightarrow> bool)" and
    isin = isin and t_set = "Tree2.set_tree" and union = "RBT.union" and inter = "RBT.inter" and 
    diff = "RBT.diff" and sel = rbt_sel for G and s
  apply(simp add: DFS_Aux_def)
  using Pair_Graph_U_RBT.Pair_Graph_Specs_axioms RBT.Set2_axioms by auto

abbreviation "DFS_Aux' G s \<equiv> DFS_Aux_Interp.DFS_Aux G (DFS_Aux_Interp.initial_state s)"

interpretation DFS_Cycles_Interp: DFS_Cycles
  where empty = RBT_Set.empty and update = update and delete = RBT_Map.delete and
    lookup = lookup and adjmap_inv = "M.invar" and vset_empty = "\<langle>\<rangle>" and
    insert = insert_rbt and vset_delete = delete_rbt and vset_inv = "rbt_inv::(('v::linorder) rbt \<Rightarrow> bool)" and
    isin = isin and t_set = "Tree2.set_tree" and union = "RBT.union" and inter = "RBT.inter" and 
    diff = "RBT.diff" and sel = rbt_sel and seen_aux = "DFS_Aux_state.seen" and cycle_aux = "DFS_Aux_state.cycle" and
    dfs_aux = "DFS_Aux' G" for G and V
  apply(simp add: DFS_Cycles_def)
  using Pair_Graph_U_RBT.Pair_Graph_Specs_axioms RBT.Set2_axioms by auto

lemma DFS_Aux_correct_1_inst:
  assumes "DFS_Cycles.DFS_Cycles_axioms isin Tree2.set_tree M.invar \<langle>\<rangle> rbt_inv lookup G V"
    "s \<in> dVs (Pair_Graph_U_RBT.digraph_abs G)"
  shows "DFS_Aux_state.cycle (DFS_Aux' G s) \<Longrightarrow> \<exists>c. cycle' (Pair_Graph_U_RBT.digraph_abs G) c"
  using assms[simplified DFS_Cycles_Interp.DFS_Cycles_axioms_def[of "G" "V"]]
    DFS_Aux_Interp.DFS_Aux_correct_1[unfolded DFS_Aux_Interp.DFS_Aux_axioms_def]
  by blast

lemma DFS_Aux_correct_2_inst:
  assumes "DFS_Cycles.DFS_Cycles_axioms isin Tree2.set_tree M.invar \<langle>\<rangle> rbt_inv lookup G V"
    "s \<in> dVs (Pair_Graph_U_RBT.digraph_abs G)"
  shows "\<not>DFS_Aux_state.cycle (DFS_Aux' G s) \<Longrightarrow>
    \<nexists>c. cycle' (Pair_Graph_U_RBT.digraph_abs G \<downharpoonright> Tree2.set_tree (DFS_Aux_state.seen (DFS_Aux' G s))) c"
  using assms[simplified DFS_Cycles_Interp.DFS_Cycles_axioms_def[of "G" "V"]]
    DFS_Aux_Interp.DFS_Aux_correct_2[unfolded DFS_Aux_Interp.DFS_Aux_axioms_def]
  by blast

lemma DFS_Aux_correct_3_inst:
  assumes "DFS_Cycles.DFS_Cycles_axioms isin Tree2.set_tree M.invar \<langle>\<rangle> rbt_inv lookup G V"
    "s \<in> dVs (Pair_Graph_U_RBT.digraph_abs G)"
  shows "\<not>DFS_Aux_state.cycle (DFS_Aux' G s) \<Longrightarrow> v \<in> Tree2.set_tree (DFS_Aux_state.seen (DFS_Aux' G s)) \<Longrightarrow>
    w \<in> dVs (Pair_Graph_U_RBT.digraph_abs G) - Tree2.set_tree (DFS_Aux_state.seen (DFS_Aux' G s)) \<Longrightarrow>
    \<nexists>p. awalk (Pair_Graph_U_RBT.digraph_abs G) v p w"
  using assms[simplified DFS_Cycles_Interp.DFS_Cycles_axioms_def[of "G" "V"]]
    DFS_Aux_Interp.DFS_Aux_correct_3[unfolded DFS_Aux_Interp.DFS_Aux_axioms_def]
  by blast

lemma DFS_Aux_correct_4_inst:
  assumes "DFS_Cycles.DFS_Cycles_axioms isin Tree2.set_tree M.invar \<langle>\<rangle> rbt_inv lookup G V"
    "s \<in> dVs (Pair_Graph_U_RBT.digraph_abs G)"
  shows "rbt_inv (DFS_Aux_state.seen (DFS_Aux' G s))"
  using assms[simplified DFS_Cycles_Interp.DFS_Cycles_axioms_def[of "G" "V"]]
    DFS_Aux_Interp.DFS_Aux_correct_4[unfolded DFS_Aux_Interp.DFS_Aux_axioms_def]
  by blast

lemma DFS_Aux_correct_5_inst:
  assumes "DFS_Cycles.DFS_Cycles_axioms isin Tree2.set_tree M.invar \<langle>\<rangle> rbt_inv lookup G V"
    "s \<in> dVs (Pair_Graph_U_RBT.digraph_abs G)"
  shows "v \<in> Tree2.set_tree (DFS_Aux_state.seen (DFS_Aux' G s)) \<Longrightarrow>
    \<exists>p. awalk (Pair_Graph_U_RBT.digraph_abs G) s p v"
  using assms[simplified DFS_Cycles_Interp.DFS_Cycles_axioms_def[of "G" "V"]]
    DFS_Aux_Interp.DFS_Aux_correct_5[unfolded DFS_Aux_Interp.DFS_Aux_axioms_def]
  by blast

lemma DFS_Aux_correct_6_inst:
  assumes "DFS_Cycles.DFS_Cycles_axioms isin Tree2.set_tree M.invar \<langle>\<rangle> rbt_inv lookup G V"
    "s \<in> dVs (Pair_Graph_U_RBT.digraph_abs G)"
  shows "s \<in> Tree2.set_tree (DFS_Aux_state.seen (DFS_Aux' G s))"
  using assms[simplified DFS_Cycles_Interp.DFS_Cycles_axioms_def[of "G" "V"]]
    DFS_Aux_Interp.DFS_Aux_correct_6[unfolded DFS_Aux_Interp.DFS_Aux_axioms_def]
  by blast


lemma DFS_Cycles_imp_dfs_aux_axioms:
  assumes "DFS_Cycles.DFS_Cycles_axioms isin Tree2.set_tree M.invar \<langle>\<rangle> rbt_inv lookup G V"
  shows "DFS_Cycles.dfs_aux_axioms isin Tree2.set_tree \<langle>\<rangle> rbt_inv lookup G (DFS_Aux' G) DFS_Aux_state.seen DFS_Aux_state.cycle"
  unfolding DFS_Cycles_Interp.dfs_aux_axioms_def
  using DFS_Aux_correct_1_inst[OF assms] DFS_Aux_correct_2_inst[OF assms] DFS_Aux_correct_3_inst[OF assms]
    DFS_Aux_correct_4_inst[OF assms] DFS_Aux_correct_5_inst[OF assms] DFS_Aux_correct_6_inst[OF assms]
  by meson


thm DFS_Cycles_Interp.DFS_Cycles_correct_1

(* If Pair_Graph_U_invar holds + relationship between G and V, we have cycle iff cycle in ugraph_abs *)

abbreviation "DFS_Cycles' G V \<equiv> DFS_Cycles_Interp.DFS_Cycles V G DFS_Cycles_Interp.initial_state"

thm Pair_Graph_U_RBT.pair_graph_u_invar_def
thm DFS_Cycles.DFS_Cycles_axioms_def

lemma DFS_Cycles_correct_final:
  assumes "Pair_Graph_U_RBT.pair_graph_u_invar G" "rbt_inv V"
    "Tree2.set_tree (V::(('a::linorder) rbt)) = dVs (Pair_Graph_U_RBT.digraph_abs G)"
  shows "DFS_Cycles_state.cycle (DFS_Cycles' G V) = (\<exists>u c. decycle (Pair_Graph_U_RBT.ugraph_abs G) u c)"
proof-
  have "DFS_Cycles.DFS_Cycles_axioms isin Tree2.set_tree M.invar \<langle>\<rangle> rbt_inv lookup G V"
    unfolding DFS_Cycles_Interp.DFS_Cycles_axioms_def 
    using assms[simplified Pair_Graph_U_RBT.pair_graph_u_invar_def[of "G"]]
      Pair_Graph_U_RBT.digraph_abs_irreflexive[OF assms(1)]
      Pair_Graph_U_RBT.digraph_abs_symmetric[OF assms(1)] by fastforce

  from DFS_Cycles_Interp.DFS_Cycles_correct_1[OF this DFS_Cycles_imp_dfs_aux_axioms[OF this]]
    DFS_Cycles_Interp.DFS_Cycles_correct_2[OF this DFS_Cycles_imp_dfs_aux_axioms[OF this]]
    have "DFS_Cycles_state.cycle (DFS_Cycles' G V) = (\<exists>c. cycle' (Pair_Graph_U_RBT.digraph_abs G) c)"
    by blast
  with Pair_Graph_U_RBT.cycle_equivalence[OF assms(1)]
  show "DFS_Cycles_state.cycle (DFS_Cycles' G V) = (\<exists>u c. decycle (Pair_Graph_U_RBT.ugraph_abs G) u c)"
    by blast
qed


text \<open>Instantiations for Greedy\<close>

lemma tree_split_case:
  "(case t of Leaf \<Rightarrow> True | _ \<Rightarrow> False) = (t = Leaf)"
  by (fastforce split: tree.splits) 

fun rbt_subseteq :: "('a::linorder) rbt \<Rightarrow> 'a rbt \<Rightarrow> bool" where
  "rbt_subseteq t1 t2 = (case (RBT.diff t1 t2) of Leaf \<Rightarrow> True | _ \<Rightarrow> False)"

lemma rbt_subseteq_correct:
  "rbt_inv t1 \<Longrightarrow> rbt_inv t2 \<Longrightarrow> (rbt_subseteq t1 t2) = (Tree2.set_tree t1 \<subseteq> Tree2.set_tree t2)"
proof(unfold rbt_subseteq.simps tree.split[of "\<lambda> x. x= (_ \<subseteq> _)" True "\<lambda> _ _ _. False" "RBT.diff t1 t2" ],
      goal_cases)
  case 1
  have is_empty_iff:"RBT.diff t1 t2 = \<langle>\<rangle> \<longleftrightarrow> Tree2.set_tree t1 - Tree2.set_tree t2 = {}"
    using 1  Tree2.eq_set_tree_empty 
    by (subst RBT.set_tree_diff[of t1 t2, symmetric])fast+
  show ?case 
    using is_empty_iff by (subst Diff_eq_empty_iff[symmetric])fastforce
qed

lemma rbt_size_correct:
  "rbt_inv X \<Longrightarrow> size X = card (Tree2.set_tree X)"
  unfolding set_inorder[symmetric]
proof(induction X rule: inorder.induct)
  case 1
  then show ?case by simp
next
  case (2 l a uu r)
  have inter_empty:"set (Tree2.inorder l) \<inter> Set.insert a (set (Tree2.inorder r)) = {}"
    using 2(3) bst.simps(2)[simplified Tree2.set_inorder[symmetric]]
    by (metis Int_emptyI insert_iff not_less_iff_gr_or_eq)
  have rbt_inv_l: "rbt_inv l" 
    by (metis "2.prems" RBT.inv_Node bst.simps(2))
  have rbt_inv_r: "rbt_inv r" 
    by (metis "2.prems" RBT.inv_Node bst.simps(2))
  have a_not_down: "a \<notin> set (Tree2.inorder r)" 
    using 2(3) bst.simps(2)[simplified Tree2.set_inorder[symmetric]] by fast
  show ?case 
   using a_not_down inter_empty 
   by(auto  simp add: card_Un_disjoint card_insert_if  2(1)[OF rbt_inv_l] 2(2)[OF rbt_inv_r])
qed

interpretation Custom_Set_RBT: Custom_Set
  where empty = "\<langle>\<rangle>" and insert = insert_rbt and delete = delete_rbt and invar = "rbt_inv::(('e::linorder) rbt \<Rightarrow> bool)" and
    isin = isin and set = "Tree2.set_tree" and union = "RBT.union" and inter = "RBT.inter" and diff = "RBT.diff" and
    subseteq = rbt_subseteq and cardinality = size
  apply (subst Custom_Set_def)
  apply(intro conjI)
  subgoal
    using RBT.Set2_axioms by blast
  subgoal
    apply (subst Custom_Set_axioms_def)
    using rbt_subseteq_correct rbt_size_correct by blast
  done


definition "set_of_sets_isin f a = f a"

interpretation Matroid_Specs_Inst: Matroid_Specs
  where set_empty = "\<langle>\<rangle>" and set_insert = insert_rbt and set_delete = delete_rbt and set_inv = "rbt_inv::(('e::linorder) rbt \<Rightarrow> bool)" and
    set_isin = isin and to_set = "Tree2.set_tree" and union = "RBT.union" and inter = "RBT.inter" and diff = "RBT.diff" and
    subseteq = rbt_subseteq and cardinality = size and
    set_of_sets_isin = "set_of_sets_isin :: ('e rbt \<Rightarrow> bool) \<Rightarrow> 'e rbt \<Rightarrow> bool"
  apply (subst Matroid_Specs_def)
  apply (subst Indep_System_Specs_def)
  using Custom_Set_RBT.Custom_Set_axioms by blast

term "DFS_Cycles'"


fun rbt_set_fold :: "'a rbt \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'b" where
  "rbt_set_fold Leaf f acc = acc"
| "rbt_set_fold (Node l (a, _) r) f acc = rbt_set_fold r f (f a (rbt_set_fold l f acc))"

lemma rbt_set_fold_revinorder: "rbt_set_fold T f acc = foldr f (rev (inorder T)) acc"
 by(induction T f acc rule: rbt_set_fold.induct) auto

fun rbt_map_fold :: "('a \<times> 'd) rbt \<Rightarrow> ('a \<Rightarrow> 'd \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'b" where
  "rbt_map_fold Leaf f acc = acc"
| "rbt_map_fold (Node l ((a, d), _) r) f acc = rbt_map_fold r f (f a d (rbt_map_fold l f acc))"

lemma rbt_map_fold_revinorder: "rbt_map_fold T f acc = foldr (\<lambda> (x, y) acc. f x y acc) (rev (inorder T)) acc"
 by(induction T f acc rule: rbt_map_fold.induct) auto

global_interpretation Kruskal_Graphs_Matroids: Graphs_Matroids_Encoding
  where empty = RBT_Set.empty and update = update and delete = RBT_Map.delete and
    lookup = lookup and adjmap_inv = "M.invar" and vset_empty = "\<langle>\<rangle>" and
    insert = insert_rbt and vset_delete = delete_rbt and vset_inv = "rbt_inv::(('v::linorder) rbt \<Rightarrow> bool)" and
    isin = isin and t_set = "Tree2.set_tree" and sel = rbt_sel and

    set_empty = "\<langle>\<rangle>" and set_insert = insert_rbt and set_delete = delete_rbt and set_inv = "rbt_inv::(('e::linorder) rbt \<Rightarrow> bool)" and
    set_isin = isin and to_set = "Tree2.set_tree" and union = "RBT.union" and inter = "RBT.inter" and diff = "RBT.diff" and
    subseteq = rbt_subseteq and cardinality = size and 
    set_of_sets_isin = "set_of_sets_isin :: ('e rbt \<Rightarrow> bool) \<Rightarrow> 'e rbt \<Rightarrow> bool" and

    adjmap_fold = "rbt_map_fold" and vset_fold = "rbt_set_fold" and set_fold_adjmap = "rbt_set_fold" and
    set_fold_vset = "rbt_set_fold"
    for v1_of :: "('e::linorder) \<Rightarrow> ('v::linorder)" and v2_of :: "('e::linorder) \<Rightarrow> ('v::linorder)" and 
        edge_of :: "('v::linorder) \<Rightarrow> 'v \<Rightarrow> ('e::linorder)" and c :: "('v set) \<Rightarrow> rat" and c' :: "'e \<Rightarrow> rat"
      defines graph_to_edges = Kruskal_Graphs_Matroids.graph_to_edges
and edges_to_graph = Kruskal_Graphs_Matroids.edges_to_graph
and edges_to_vertices = Kruskal_Graphs_Matroids.edges_to_vertices
  apply (subst Graphs_Matroids_Encoding_def)
  using Pair_Graph_U_RBT.Pair_Graph_U_Specs_axioms Matroid_Specs_Inst.Matroid_Specs_axioms
  by blast

lemma map_of_dom_is:"set (map fst list) = {a. AList_Upd_Del.map_of list a \<noteq> None}"
proof(induction list)
  case Nil
  then show ?case by simp
next
  case (Cons a list)
  have "set (map fst (a # list)) = Set.insert (fst a) (set (map fst list))" by simp
  also have "... = Set.insert (fst a) {a. AList_Upd_Del.map_of list a \<noteq> None}" 
    using Cons by simp
  also have "... =  {aa. AList_Upd_Del.map_of (a # list) aa \<noteq> None}"
    by(cases a) auto
  finally show ?case by simp
qed

lemma map_of_rev: "distinct (map fst xs) \<Longrightarrow> map_of (rev xs) x = map_of xs x"
  by(induction xs)
    (auto simp add: map_of_append map_of_dom_is[simplified] split: option.split)

lemma  rbt_map_fold_correct: "M.invar G \<Longrightarrow>
       \<exists>xs. distinct xs \<and>
            set xs = dom (lookup G) \<and> rbt_map_fold G f S = foldr (\<lambda>x. f x (the (lookup G x))) xs S"
proof(subst rbt_map_fold_revinorder, rule exI[of _ "map fst (rev (inorder G))"], goal_cases)
  case 1
  have invar_inorder:"rbt G \<and> sorted1 (Tree2.inorder G)"
   using "1" M.invar_def by auto
  define list where "list = Tree2.inorder G"
  define list' where "list' = rev (inorder G)"
  have distinct_list:"distinct (map fst (Tree2.inorder G))" 
    using "1" M.invar_def strict_sorted_iff by blast
  moreover have "set (map fst (Tree2.inorder G)) = dom (lookup G)"
    using invar_inorder
    by(subst dom_def, subst M.inorder_lookup, unfold list_def[symmetric] map_of_dom_is) simp+
  moreover have "foldr (\<lambda>(x, y). f x y) (rev (Tree2.inorder G)) S =
    foldr (\<lambda>x. f x (the (lookup G x))) (map fst (rev (Tree2.inorder G))) S"
  proof-
    have "distinct (map fst list')" 
      by (metis distinct_list distinct_rev list'_def rev_map)
    hence same_fold:"foldr (\<lambda>(x, y). f x y) list' S =
    foldr (\<lambda>x. f x (the (AList_Upd_Del.map_of list' x))) (map fst list') S"
    proof(induction list')
      case Nil
      then show ?case by simp
    next
      case (Cons a list')
      show ?case 
      proof(cases a)
        case (Pair x y)
        have distinct_fsts: "distinct (x # map fst list')" 
          using Cons(2)[simplified Pair list.map(2) fst_conv] by fast
        have first_f_apply:"foldr (\<lambda>a. case a of (x, y) \<Rightarrow> f x y) (a # list') S = f x y (foldr (\<lambda>(x, y). f x y) list' S)"
          by(simp add: Pair)
        have map_of_same:"(foldr (\<lambda>xa. f xa (the (AList_Upd_Del.map_of ((x, y) # list') xa))) (map fst list') S)
              = (foldr (\<lambda>xa. f xa (the (AList_Upd_Del.map_of  list' xa))) (map fst list') S)"
          apply(rule foldr_cong[OF refl refl])
          subgoal for s t
            using distinct_fsts[simplified distinct.simps(2)] 
            by (subst map_of.simps, subst if_not_P)force+
          done
        have almost_result: "(foldr (\<lambda>(x, y). f x y) list' S) =
                   (foldr (\<lambda>xa. f xa (the (AList_Upd_Del.map_of ((x, y) # list') xa))) (map fst list') S)"
          using distinct_fsts[simplified distinct.simps(2)]
          by (subst map_of_same, subst Cons(1)[symmetric])force+
        show ?thesis
          apply(subst  first_f_apply)
          apply(subst Pair)+
          apply(subst  list.map(2))
          apply(subst foldr.simps)
          apply(subst o_apply)
          apply(subst map_of.simps)
          apply(subst if_P)
          apply simp
          apply(subst option.sel)
          apply(subst fst_conv)
          by(subst almost_result[symmetric] ) force
      qed
    qed
    show ?thesis
    using invar_inorder 
    by(simp add:  lookup_map_of map_of_rev[OF distinct_list, symmetric] list'_def[symmetric] same_fold)+  
  qed
 ultimately show ?case 
   by (metis distinct_rev rev_map set_rev)
qed

lemma bst_distinct_inorder:"bst T \<Longrightarrow> distinct (inorder T)"
  by(induction T rule: inorder.induct) fastforce+

lemma rbt_set_fold_correct: "rbt_inv S \<Longrightarrow> \<exists>xs. distinct xs \<and> set xs = Tree2.set_tree S \<and> rbt_set_fold S f G = foldr f xs G"
  apply(subst rbt_set_fold_revinorder)
  apply(rule exI[of _ "rev (Tree2.inorder S)"])
  using  bst_distinct_inorder[of S]
  by (unfold set_inorder[symmetric] set_rev distinct_rev ) fastforce

locale Transforms =
fixes v1_of::"('e::linorder \<Rightarrow> 'v::linorder)" and v2_of::"'e \<Rightarrow> 'v" 
and edge_of::"'v \<Rightarrow> 'v \<Rightarrow> 'e"
and input_G :: "('v * ('v rbt)) rbt" 
begin

abbreviation Kruskal_G_to_E :: "(('v::linorder) \<times> ('v rbt)) rbt \<Rightarrow> 'e rbt" where
  "Kruskal_G_to_E \<equiv> graph_to_edges edge_of"

definition Kruskal_E_to_G :: "('e::linorder) rbt \<Rightarrow> ('v \<times> ('v rbt)) rbt" where
  "Kruskal_E_to_G = edges_to_graph v1_of v2_of"

definition Kruskal_E_to_V :: "('e::linorder) rbt \<Rightarrow> ('v rbt)" where
  "Kruskal_E_to_V = edges_to_vertices v1_of v2_of"

definition carrier_graph_matroid :: "('e::linorder) rbt" where
  "carrier_graph_matroid = graph_to_edges edge_of input_G"

fun indep_graph_matroid :: "('e::linorder) rbt \<Rightarrow> bool" where
  "indep_graph_matroid E = 
    (let
      G = (Kruskal_E_to_G E);
      V = (Kruskal_E_to_V E)
    in
      (if rbt_subseteq E carrier_graph_matroid then \<not>DFS_Cycles_state.cycle (DFS_Cycles' G V)
      else False))"
end

global_interpretation transforms: Transforms
  where v1_of = v1_of and v2_of = v2_of and edge_of = edge_of and input_G = input_G
  for v1_of::"'e::linorder \<Rightarrow> 'a::linorder" and v2_of edge_of input_G
  defines Kruskal_G_to_E = transforms.Kruskal_G_to_E
   and Kruskal_E_to_G=transforms.Kruskal_E_to_G
   and Kruskal_E_to_V=transforms.Kruskal_E_to_V
   and carrier_graph_matroid=transforms.carrier_graph_matroid
   and indep_graph_matroid=transforms.indep_graph_matroid
  done



global_interpretation Kruskal_Greedy: Best_In_Greedy
  where set_empty = "\<langle>\<rangle>" and set_insert = insert_rbt and set_delete = delete_rbt 
     and set_inv = "rbt_inv::(('e::linorder) rbt \<Rightarrow> bool)" and
    set_isin = isin and to_set = "Tree2.set_tree" and union = "RBT.union" and inter = "RBT.inter" and diff = "RBT.diff" and
    subseteq = rbt_subseteq and cardinality = size and
    set_of_sets_isin = "set_of_sets_isin :: (('e::linorder) rbt \<Rightarrow> bool) \<Rightarrow> 'e rbt \<Rightarrow> bool" and 
    carrier = "carrier_graph_matroid edge_of input_G" 
and indep_set = "indep_graph_matroid v1_of v2_of edge_of input_G" and
    sort_desc = insort_key_desc
  for v1_of::"'e::linorder \<Rightarrow>'a::linorder" and v2_of edge_of input_G
  (* TODO should we instantiate remaining parameters here or just outside? \<Rightarrow> probably should instantiate carrier and indep_set
  here since they are specified in the locale, but cannot yet instantiate c and order *)
  apply (subst Best_In_Greedy_def)
  using Matroid_Specs_Inst.Matroid_Specs_axioms by blast

abbreviation "indep'  == Kruskal_Greedy.indep' (TYPE ('a::linorder))"

locale Kruskal_Proof_Matroid_Edges =
Transforms +
  assumes v1_never_v2:"\<And> e. v1_of (e::'e::linorder) \<noteq> v2_of e"
and v1_of_edge_of: "x \<noteq> y \<Longrightarrow> v1_of (edge_of x y) = x \<or> v1_of (edge_of x y) = y"
and v2_of_edge_of: "x \<noteq> y \<Longrightarrow> v2_of (edge_of x y) = x \<or> v2_of (edge_of x y) = y"
begin

interpretation Kruskal_Graphs_Matroids_Proofs: Graphs_Matroids_Encoding_Proofs
  where empty = RBT_Set.empty and update = update and delete = RBT_Map.delete and
    lookup = lookup and adjmap_inv = "M.invar" and vset_empty = "\<langle>\<rangle>" and
    insert = insert_rbt and vset_delete = delete_rbt and vset_inv = "rbt_inv::(('a::linorder) rbt \<Rightarrow> bool)" and
    isin = isin and t_set = "Tree2.set_tree" and sel = rbt_sel and

    set_empty = "\<langle>\<rangle>" and set_insert = insert_rbt and set_delete = delete_rbt and set_inv = "rbt_inv::(('e::linorder) rbt \<Rightarrow> bool)" and
    set_isin = isin and to_set = "Tree2.set_tree" and union = "RBT.union" and inter = "RBT.inter" and diff = "RBT.diff" and
    subseteq = rbt_subseteq and cardinality = size and 
    set_of_sets_isin = "set_of_sets_isin :: ('e rbt \<Rightarrow> bool) \<Rightarrow> 'e rbt \<Rightarrow> bool" and

    adjmap_fold = "rbt_map_fold" and vset_fold = "rbt_set_fold" and set_fold_adjmap = "rbt_set_fold" and
    set_fold_vset = "rbt_set_fold"
  for c :: "('a set) \<Rightarrow> rat" and c' :: "'e \<Rightarrow> rat"
 proof(rule Graphs_Matroids_Encoding_Proofs.intro, 
     rule Kruskal_Graphs_Matroids.Graphs_Matroids_Encoding_axioms, 
     rule Graphs_Matroids_Encoding_Proofs_axioms.intro, goal_cases)
  case (1 G S f)
  then show ?case by(auto intro:  rbt_map_fold_correct)
next
  case (2 G S f)
  show ?case 
  by(insert 2, rule rbt_set_fold_correct[of S f G]) fast
next
  case (3 V f S)
  show ?case by(insert 3, rule rbt_set_fold_correct) fast
next
  case 5
  then show ?case  by(auto intro: finite_set_tree simp add: Pair_Graph_Specs.finite_vsets_def[OF Pair_Graph_U_RBT.Pair_Graph_Specs_axioms])
next
  case (4 V f S)
  show ?case  by(insert 4, rule rbt_set_fold_correct) fast
next
  case (6 e)
  thus ?case 
    by (simp add: v1_never_v2)
next
  case (7 x y)
  thus ?case 
    using v1_of_edge_of by blast
next
  case (8 x y)
  thus ?case
    using v2_of_edge_of by presburger
qed

term Kruskal_Graphs_Matroids.graph_to_edges

definition "cost_nonnegative (c::(('v set) \<Rightarrow> rat)) = ( \<forall>e. c e \<ge> 0)"

term Kruskal_Graphs_Matroids.graph_to_edges
term Kruskal_Graphs_Matroids.edges_to_graph


context
    fixes c :: "('a set) \<Rightarrow> rat" and c' :: "'e \<Rightarrow> rat"
begin


lemma (* TODO instantiate assms directly using thms from encoding locale, maybe take the statement "further"*)
  indep_graph_matroid_expr_1:
  assumes "Pair_Graph_U_RBT.pair_graph_u_invar (Kruskal_E_to_G  (E::('e::linorder) rbt))" 
          "rbt_inv (Kruskal_E_to_V   E)"
    "Tree2.set_tree (Kruskal_E_to_V   E) =
            dVs (Pair_Graph_U_RBT.digraph_abs (Kruskal_E_to_G   E))"
  shows "indep_graph_matroid  E =
    (rbt_subseteq E (carrier_graph_matroid ) \<and>
 \<not>(\<exists>u c. decycle (Pair_Graph_U_RBT.ugraph_abs (Kruskal_E_to_G  E)) u c))"
  apply (subst indep_graph_matroid.simps)
  apply (subst Let_def)+
  apply (subst DFS_Cycles_correct_final[OF assms]) by presburger

lemma
  indep_graph_matroid_expr_2:
  assumes "rbt_inv (E::('e::linorder) rbt)"
  shows "indep_graph_matroid  E =
    (rbt_subseteq E (carrier_graph_matroid ) \<and> 
\<not>(\<exists>u c. decycle (Pair_Graph_U_RBT.ugraph_abs (Kruskal_E_to_G E)) u c))"
  using indep_graph_matroid_expr_1[of "E", unfolded Kruskal_E_to_G_def Kruskal_E_to_V_def]
    Kruskal_Graphs_Matroids_Proofs.edges_invar_imp_graph_invar[OF assms]
    Kruskal_Graphs_Matroids_Proofs.edges_invar_imp_vertices_props[OF assms]
  by(unfold Kruskal_E_to_G_def  edges_to_graph_def edges_to_vertices_def) blast
  

term Kruskal_Greedy.valid_solution 
term Kruskal_Greedy.nonnegative 
term Kruskal_Greedy.valid_order

thm Kruskal_Greedy.BestInGreedy_correct_1
thm Kruskal_Greedy.BestInGreedy_correct_3
thm Kruskal_Greedy.BestInGreedy_matroid_iff_opt



term Matroid_Specs_Inst.indep
term indep_graph_matroid

lemma carrier_graph_matroid_inv:
  assumes "Pair_Graph_U_RBT.pair_graph_u_invar input_G"
  shows "rbt_inv  (carrier_graph_matroid)"
  using Kruskal_Graphs_Matroids_Proofs.graph_invar_imp_edges_invar[OF assms] 
  by(unfold carrier_graph_matroid_def graph_to_edges_def)

lemma Kruskal_Greedy_indep':
  "Kruskal_Greedy.indep'  v1_of v2_of edge_of input_G (X::('e \<times> color) tree) =
 indep_graph_matroid X"
  using Matroid_Specs_Inst.indep_def set_of_sets_isin_def
  by (metis indep_graph_matroid_def)

lemma indep_graph_matroid_abs_equal:
  assumes "Pair_Graph_U_RBT.pair_graph_u_invar input_G" "rbt_inv X" "rbt_inv Y" "Tree2.set_tree X = Tree2.set_tree Y"
  shows "indep_graph_matroid  X
           = indep_graph_matroid  Y"
proof-
  have "rbt_subseteq X (carrier_graph_matroid) =
        rbt_subseteq Y (carrier_graph_matroid )"
    using rbt_subseteq_correct[OF \<open>rbt_inv X\<close> carrier_graph_matroid_inv[OF assms(1)]]
    rbt_subseteq_correct[OF \<open>rbt_inv Y\<close> carrier_graph_matroid_inv[OF assms(1)]] assms(4)
    by blast
  with Kruskal_Graphs_Matroids_Proofs.to_set_equal_imp_ugraph_abs_equal[OF assms(2-4)]
  show "indep_graph_matroid  X =
        indep_graph_matroid  Y"
    apply (subst indep_graph_matroid_expr_2[OF \<open>rbt_inv X\<close>])
    apply (subst indep_graph_matroid_expr_2[OF \<open>rbt_inv Y\<close>])
    unfolding Kruskal_E_to_G_def edges_to_graph_def using arg_cong2 .
qed
lemma Kruskal_BestInGreedy_axioms:
  assumes "Pair_Graph_U_RBT.pair_graph_u_invar input_G"
  shows "Best_In_Greedy.BestInGreedy_axioms rbt_inv Tree2.set_tree set_of_sets_isin 
  (carrier_graph_matroid) (indep_graph_matroid )"
  unfolding Kruskal_Greedy.BestInGreedy_axioms_def Matroid_Specs_Inst.invar_def
    Matroid_Specs_Inst.finite_sets_def
proof-
  from carrier_graph_matroid_def Kruskal_Graphs_Matroids_Proofs.graph_invar_imp_edges_invar[OF assms]
    have "rbt_inv  (carrier_graph_matroid )" 
      using assms carrier_graph_matroid_inv by blast
  with indep_graph_matroid_abs_equal[OF assms] Kruskal_Greedy_indep' finite_set_tree
  have "(rbt_inv  (carrier_graph_matroid ) \<and>
    (\<forall>X Y. rbt_inv X \<longrightarrow> rbt_inv Y \<longrightarrow> Tree2.set_tree X = Tree2.set_tree Y \<longrightarrow>
      indep'  v1_of v2_of edge_of input_G X =
      indep'  v1_of v2_of edge_of input_G Y)) \<and>
    (\<forall>X. finite (Tree2.set_tree X))" by blast
  thus ?thesis 
    by (metis (mono_tags, lifting) Best_In_Greedy.BestInGreedy_axioms_def Kruskal_Greedy.Best_In_Greedy_axioms Matroid_Specs_Inst.finite_sets_def Matroid_Specs_Inst.invar_def indep_graph_matroid_def)
qed


lemma Kruskal_sort_desc_axioms:
  "Best_In_Greedy.sort_desc_axioms Kruskal_Greedy.carrier_sorted"
  unfolding Kruskal_Greedy.sort_desc_axioms_def
  using set_insort_key_desc length_insort_key_desc sorted_desc_f_insort_key_desc insort_key_desc_stable
  by metis


context
  assumes pair_graph_u: "Pair_Graph_U_RBT.pair_graph_u_invar input_G"
begin

lemmas carrier_inv = carrier_graph_matroid_inv[OF pair_graph_u]

(*
interpretation input_G_graph_abs: graph_abs
  where G = "Pair_Graph_U_RBT.ugraph_abs input_G"
  using Pair_Graph_U_RBT.graph_abs_ugraph[OF pair_graph_u] by simp

interpretation (Pair_Graph_U_RBT.ugraph_abs (Kruskal_E_to_G carrier_graph_matroid))
*)
(*
lemma carrier_converted_back:
  "Kruskal_E_to_G carrier_graph_matroid = input_G"
  unfolding Kruskal_E_to_G_def carrier_graph_matroid_def 
  using Kruskal_Graphs_Matroids_Proofs.graph_to_edges_inverse[OF pair_graph_u] by simp
*)

lemma carrier_converted_graph_abs:
  "graph_abs (Pair_Graph_U_RBT.ugraph_abs 
(Kruskal_E_to_G  ( carrier_graph_matroid )))"
  using (*carrier_converted_back*) Pair_Graph_U_RBT.graph_abs_ugraph[OF pair_graph_u]
  sorry
(* Put this into interpretation or not? *)

lemma indep_graph_matroid_expr_3:
  assumes "rbt_inv (E::('e::linorder) rbt)"
  shows "indep_graph_matroid  E = 
    graph_abs.has_no_cycle (Pair_Graph_U_RBT.ugraph_abs 
(Kruskal_E_to_G  (carrier_graph_matroid)))
    (Pair_Graph_U_RBT.ugraph_abs (Kruskal_E_to_G  E))"
  unfolding graph_abs.has_no_cycle_def[OF carrier_converted_graph_abs]
  (* (rbt_subseteq E carrier_graph_matroid \<and> \<not>(\<exists>u c. decycle (Pair_Graph_U_RBT.ugraph_abs (Kruskal_E_to_G E)) u c)) *)
proof-
  from indep_graph_matroid_expr_2[OF assms]
  have "indep_graph_matroid  E =
    (rbt_subseteq E (carrier_graph_matroid ) \<and>
    (\<nexists>u c. decycle (Pair_Graph_U_RBT.ugraph_abs (Kruskal_E_to_G  E)) u c))" by blast
  also have "... = 
    (Pair_Graph_U_RBT.ugraph_abs (Kruskal_E_to_G  E) \<subseteq>
 Pair_Graph_U_RBT.ugraph_abs (Kruskal_E_to_G  (carrier_graph_matroid )) \<and>
    (\<nexists>u c. decycle (Pair_Graph_U_RBT.ugraph_abs (Kruskal_E_to_G  E)) u c))"
    unfolding Kruskal_E_to_G_def
    using Kruskal_Graphs_Matroids_Proofs.subset_iff_graph_to_edges_subset[OF assms carrier_inv]
    sorry
  finally show "indep_graph_matroid  E =
    (Pair_Graph_U_RBT.ugraph_abs (Kruskal_E_to_G  E) \<subseteq>
 Pair_Graph_U_RBT.ugraph_abs (Kruskal_E_to_G (carrier_graph_matroid )) \<and>
     (\<nexists>u c. decycle (Pair_Graph_U_RBT.ugraph_abs (Kruskal_E_to_G  E)) u c))" .
qed


(* TODO maybe generalise some parts of these theorems? *)
term indep'
lemma Kruskal_indep'_eq_has_no_cycle:
  assumes "rbt_inv (X::('e::linorder) rbt)"
  shows "indep' v1_of v2_of edge_of input_G X = graph_abs.has_no_cycle 
(Pair_Graph_U_RBT.ugraph_abs (Kruskal_E_to_G  (carrier_graph_matroid )))
    (Pair_Graph_U_RBT.ugraph_abs (Kruskal_E_to_G  X))"
  using Kruskal_Greedy_indep' indep_graph_matroid_expr_3[OF assms] by blast

lemma Kruskal_indep_subset_carrier:
  assumes "rbt_inv (X::('e::linorder) rbt)" "indep' v1_of v2_of edge_of input_G X"
  shows "rbt_subseteq X (carrier_graph_matroid )"
proof-
  from assms(2) Kruskal_Greedy_indep' indep_graph_matroid_expr_3[OF assms(1)]
  have "graph_abs.has_no_cycle (Pair_Graph_U_RBT.ugraph_abs 
(Kruskal_E_to_G (carrier_graph_matroid )))
    (Pair_Graph_U_RBT.ugraph_abs (Kruskal_E_to_G  X))" by blast
  then have "Pair_Graph_U_RBT.ugraph_abs (Kruskal_E_to_G  X) \<subseteq>
    Pair_Graph_U_RBT.ugraph_abs (Kruskal_E_to_G  (carrier_graph_matroid ))"
    using graph_abs.has_no_cycle_indep_subset_carrier[OF carrier_converted_graph_abs] by blast
  then have "Tree2.set_tree X \<subseteq> Tree2.set_tree ((carrier_graph_matroid ))"
    unfolding Kruskal_E_to_G_def
    using Kruskal_Graphs_Matroids_Proofs.edges_to_graph_subset_imp_subset[OF \<open>rbt_inv X\<close> carrier_inv]
    sorry
  with Custom_Set_RBT.set_subseteq[OF \<open>rbt_inv X\<close> carrier_inv]
    show "rbt_subseteq X (carrier_graph_matroid )" by blast
qed

lemma Kruskal_indep_ex:
  "(\<exists>X. rbt_inv (X::('e::linorder) rbt) \<and> indep' v1_of v2_of edge_of input_G X)"
proof-
  from graph_abs.has_no_cycle_indep_ex[OF carrier_converted_graph_abs]
  obtain G where "graph_abs.has_no_cycle (Pair_Graph_U_RBT.ugraph_abs 
(Kruskal_E_to_G  (carrier_graph_matroid ))) G"
    by blast
  from graph_abs.has_no_cycle_indep_subset_carrier[OF carrier_converted_graph_abs this]
    have "G \<subseteq> (Pair_Graph_U_RBT.ugraph_abs (Kruskal_E_to_G  (carrier_graph_matroid )))"
      sorry
  from graph_abs_mono[OF carrier_converted_graph_abs this]
    have "graph_abs G" by blast
    obtain G_impl where G_impl_invar: "Pair_Graph_U_RBT.pair_graph_u_invar G_impl" and
      G_impl_abs: "Pair_Graph_U_RBT.ugraph_abs G_impl = G"
      sorry

  (* If G satisfies ugraph_abs, there exists an impl graph satisfying pair_graph_u such that ugraph_abs (G_impl) = *)

  from Kruskal_Graphs_Matroids_Proofs.graph_invar_imp_edges_invar[OF \<open>Pair_Graph_U_RBT.pair_graph_u_invar G_impl\<close>]
    have "rbt_inv (Kruskal_Graphs_Matroids.graph_to_edges edge_of G_impl)" sorry


  from \<open>graph_abs.has_no_cycle (Pair_Graph_U_RBT.ugraph_abs (Kruskal_E_to_G (carrier_graph_matroid ))) G\<close> G_impl_abs
    have "graph_abs.has_no_cycle (Pair_Graph_U_RBT.ugraph_abs (Kruskal_E_to_G (carrier_graph_matroid )))
      (Pair_Graph_U_RBT.ugraph_abs (Kruskal_E_to_G (Kruskal_Graphs_Matroids.graph_to_edges edge_of G_impl)))"
    unfolding Kruskal_E_to_G_def sorry
   (* apply (subst Kruskal_Graphs_Matroids_Proofs.graph_to_edges_inverse[OF G_impl_invar])
    by (metis Kruskal_E_to_G_def carrier_converted_back)*)

  with Kruskal_Greedy_indep' indep_graph_matroid_expr_3[OF \<open>rbt_inv (Kruskal_Graphs_Matroids.graph_to_edges edge_of G_impl)\<close>]
    (* \<open>graph_abs.has_no_cycle (Pair_Graph_U_RBT.ugraph_abs (Kruskal_E_to_G carrier_graph_matroid)) G\<close>
    \<open>Pair_Graph_U_RBT.ugraph_abs G_impl = G\<close>
    Kruskal_Graphs_Matroids.graph_to_edges_inverse[OF G_impl_invar] *)
    have "Kruskal_Greedy.indep' v1_of v2_of edge_of input_G (Kruskal_Graphs_Matroids.graph_to_edges edge_of G_impl)" by blast
  with \<open>rbt_inv (Kruskal_Graphs_Matroids.graph_to_edges edge_of G_impl)\<close>
    show ?thesis by blast
qed


lemma Kruskal_indep_subset:
  assumes "rbt_inv X" "rbt_inv Y" "indep' v1_of v2_of edge_of input_G X" "rbt_subseteq Y X"
  shows "indep' v1_of v2_of edge_of input_G Y"
proof-
  from Kruskal_indep'_eq_has_no_cycle[OF assms(1)] assms(3)
  have no_cycle: "graph_abs.has_no_cycle
 (Pair_Graph_U_RBT.ugraph_abs (Kruskal_E_to_G (carrier_graph_matroid)))
      (Pair_Graph_U_RBT.ugraph_abs (Kruskal_E_to_G X))" by blast
  have X_subset_Y: "Pair_Graph_U_RBT.ugraph_abs (Kruskal_E_to_G Y) \<subseteq>
    Pair_Graph_U_RBT.ugraph_abs (Kruskal_E_to_G X)"
   (* using Kruskal_Graphs_Matroids_Proofs.subset_iff_graph_to_edges_subset[OF assms(2,1), of v1_of v2_of]
    assms(4) by(force simp add: Kruskal_E_to_G_def) *) sorry
  from graph_abs.has_no_cycle_indep_subset[OF carrier_converted_graph_abs no_cycle X_subset_Y]
  have "graph_abs.has_no_cycle (Pair_Graph_U_RBT.ugraph_abs
 (Kruskal_E_to_G  (carrier_graph_matroid)))
      (Pair_Graph_U_RBT.ugraph_abs (Kruskal_E_to_G Y))" by blast
  with Kruskal_indep'_eq_has_no_cycle[OF \<open>rbt_inv Y\<close>]
    show ?thesis by blast
qed

lemma Kruskal_augment:
  assumes "rbt_inv X" "rbt_inv Y" "indep' v1_of v2_of edge_of input_G X" 
"indep' v1_of v2_of edge_of input_G Y" "size X = Suc (size Y)"
shows "(\<exists>x. Pair_Graph_U_RBT.isin' x (RBT.diff X Y) \<and>
 indep' v1_of v2_of edge_of input_G (insert_rbt x Y))"
proof-
  from Kruskal_indep'_eq_has_no_cycle[OF assms(1)] assms(3)
  have no_cycle_X: "graph_abs.has_no_cycle (Pair_Graph_U_RBT.ugraph_abs
 (Kruskal_E_to_G  (carrier_graph_matroid )))
      (Pair_Graph_U_RBT.ugraph_abs (Kruskal_E_to_G X))" by blast
  from Kruskal_indep'_eq_has_no_cycle[OF assms(2)] assms(4)
  have no_cycle_Y: "graph_abs.has_no_cycle (Pair_Graph_U_RBT.ugraph_abs
 (Kruskal_E_to_G  (carrier_graph_matroid )))
      (Pair_Graph_U_RBT.ugraph_abs (Kruskal_E_to_G  Y))" by blast

  from Kruskal_Graphs_Matroids_Proofs.card_graph_to_edges[OF \<open>rbt_inv X\<close>]
     Kruskal_Graphs_Matroids_Proofs.card_graph_to_edges[OF \<open>rbt_inv Y\<close>] assms(5)

  have card_rel: "card (Pair_Graph_U_RBT.ugraph_abs (Kruskal_E_to_G  X)) 
= Suc (card (Pair_Graph_U_RBT.ugraph_abs (Kruskal_E_to_G  Y))) "
    unfolding Kruskal_E_to_G_def sorry

  from graph_abs.has_no_cycle_augment[OF carrier_converted_graph_abs no_cycle_X no_cycle_Y card_rel]
  obtain x where "x \<in> Pair_Graph_U_RBT.ugraph_abs (Kruskal_E_to_G X) 
- Pair_Graph_U_RBT.ugraph_abs (Kruskal_E_to_G  Y)"
      "graph_abs.has_no_cycle (Pair_Graph_U_RBT.ugraph_abs (Kruskal_E_to_G  
(carrier_graph_matroid )))
       (Set.insert x (Pair_Graph_U_RBT.ugraph_abs (Kruskal_E_to_G  Y)))" by blast
find_theorems Pair_Graph_U_RBT.ugraph_abs Kruskal_E_to_G
   (* TODO HERE !! *)
  show ?thesis
    apply(subst Kruskal_indep'_eq_has_no_cycle) sorry
qed


lemma Kruskal_indep_system_axioms:
  "Matroid_Specs_Inst.indep_system_axioms (carrier_graph_matroid ) 
(indep_graph_matroid)"
  apply (subst Matroid_Specs_Inst.indep_system_axioms_def)
  using Kruskal_indep_subset_carrier Kruskal_indep_ex Kruskal_indep_subset
  by (smt (verit) indep_graph_matroid_def)

lemma Kruskal_matroid_axioms:
  "Matroid_Specs_Inst.matroid_axioms (carrier_graph_matroid )
 (indep_graph_matroid )"
  apply (subst Matroid_Specs_Inst.matroid_axioms_def)
  using Kruskal_indep_system_axioms Kruskal_augment
  by (metis (no_types, lifting) indep_graph_matroid_def)

end


(* thm Kruskal_Greedy.BestInGreedy_correct_1[OF Kruskal_BestInGreedy_axioms] *)
(*thm Kruskal_Greedy.BestInGreedy_correct_1[OF Kruskal_BestInGreedy_axioms Kruskal_sort_desc_axioms Kruskal_indep_system_axioms]
*)
(* TODO NOW INSTANTIATE INDEP SYSTEM AXIOMS, CONNECT FINAL THEOREM 
\<Rightarrow> assumptions on c and order can be left as-is for now *)



(* !! TODO here assumption !! *)
(*
interpretation G_edges_abs: graph_abs
  where G = "Pair_Graph_U_RBT.ugraph_abs input_G"
  using Pair_Graph_U_RBT.graph_abs_ugraph[OF pair_graph_u] by simp
*)

term Kruskal_Greedy.initial_state 

(* TODO define Kruskal_MST, maybe should parametrise with graph and define outside of context? \<Rightarrow> or parametrise
with c and order? \<Longrightarrow> Don't need to put this function in context, only use use context when pair graph property
is actually necessary
\<Rightarrow> maybe parametrise with c and order? *)
(*
fun Kruskal_MST :: "(('v::linorder) * ('v rbt)) rbt" where
  "Kruskal_MST = Kruskal_E_to_G (best_in_greedy_state.result (Kruskal_Greedy.BestInGreedy (Kruskal_Greedy.initial_state c order)))"
*)
find_theorems "_::_ itself"

abbreviation "BestInGreedy == Kruskal_Greedy.BestInGreedy "

fun Kruskal_MST :: "('e::linorder list) \<Rightarrow> (('a::linorder) * ('a rbt)) rbt" where
  "Kruskal_MST order =
    Kruskal_E_to_G  (
best_in_greedy_state.result
 (Kruskal_Greedy.BestInGreedy (TYPE ('a)) v1_of v2_of edge_of input_G  
(Kruskal_Greedy.initial_state c' order)))"

context
  assumes pair_graph_u: "Pair_Graph_U_RBT.pair_graph_u_invar input_G"
begin

interpretation G_edges_abs: graph_abs
  where G = "Pair_Graph_U_RBT.ugraph_abs input_G"
  using Pair_Graph_U_RBT.graph_abs_ugraph[OF pair_graph_u] by simp

(* thm spanning_tree_def *)
thm G_edges_abs.is_spanning_forest_def
(*
thm Kruskal_Greedy.BestInGreedy_correct_3[OF Kruskal_BestInGreedy_axioms[OF pair_graph_u]
    Kruskal_sort_desc_axioms Kruskal_indep_system_axioms[OF pair_graph_u]]
*)
lemma Kruskal_Greedy_valid_inst:
  assumes "Kruskal_Greedy.nonnegative (TYPE ('a)) edge_of inut_G c'" 
"Kruskal_Greedy.valid_order (TYPE ('a)) edge_of input_G order"
shows "Kruskal_Greedy.valid_solution (TYPE ('a)) edge_of input_G v1_of v2_of
 (result (Kruskal_Greedy.BestInGreedy (TYPE ('a)) v1_of v2_of edge_of input_G
 (Kruskal_Greedy.initial_state c' order)))"
(*proof-
  from Kruskal_Greedy.BestInGreedy_correct_1[OF Kruskal_BestInGreedy_axioms[OF pair_graph_u]
    Kruskal_sort_desc_axioms Kruskal_indep_system_axioms[OF pair_graph_u], OF assms]
  show ?thesis by metis
qed*) sorry

lemma Kruskal_Greedy_opt_inst:
  assumes "Kruskal_Greedy.nonnegative (TYPE ('a)) edge_of input_G c'" 
"Kruskal_Greedy.valid_order (TYPE ('a)) edge_of input_G order"
 "Kruskal_Greedy.valid_solution (TYPE ('a)) edge_of input_G v1_of v2_of X"
  shows "sum c' (Tree2.set_tree X) \<le> sum c'
           (Tree2.set_tree (result (Kruskal_Greedy.BestInGreedy (TYPE ('a))
           v1_of v2_of edge_of input_G (Kruskal_Greedy.initial_state c' order))))"
proof-
 (* from Kruskal_Greedy.BestInGreedy_matroid_iff_opt[OF Kruskal_BestInGreedy_axioms[OF pair_graph_u]
    Kruskal_sort_desc_axioms Kruskal_indep_system_axioms[OF pair_graph_u]]
    Kruskal_matroid_axioms[OF pair_graph_u]
    assms Kruskal_Greedy.c_set_def*)
  have "Kruskal_Greedy.c_set c' (Tree2.set_tree X) \<le>
    Kruskal_Greedy.c_set c' (Tree2.set_tree (result
 (Kruskal_Greedy.BestInGreedy  (TYPE ('a))
           v1_of v2_of edge_of input_G (Kruskal_Greedy.initial_state c' order))))"
    sorry
  with Kruskal_Greedy.c_set_def show ?thesis by metis
qed



lemma nonneg_conv:
  "cost_nonnegative c \<Longrightarrow> Kruskal_Greedy.nonnegative (TYPE ('a)) edge_of input_G c'"
  sorry


lemma Kruskal_correct_final_1:
  assumes "cost_nonnegative c" "Kruskal_Greedy.valid_order (TYPE ('a)) 
edge_of input_G order" (* WRONG ASSUMPTIONS !! *)
  shows "G_edges_abs.is_spanning_forest (Pair_Graph_U_RBT.ugraph_abs (Kruskal_MST order))"
  sorry
 

thm Kruskal_matroid_axioms[OF pair_graph_u]
(*thm Kruskal_Greedy.BestInGreedy_matroid_iff_opt[OF Kruskal_BestInGreedy_axioms[OF pair_graph_u]
    Kruskal_sort_desc_axioms Kruskal_indep_system_axioms[OF pair_graph_u]]
*)
term "(Pair_Graph_U_RBT.ugraph_abs (Kruskal_MST order))"
lemma Kruskal_correct_final_2:
  assumes "cost_nonnegative c" "Kruskal_Greedy.valid_order (TYPE ('a)) edge_of input_G order" (* WRONG ASSUMPTIONS !! *)
    (* introduce new nonnegative predicate, maybe find some way to get order based on existing stuff or assume 
    function*)
    "Pair_Graph_U_RBT.pair_graph_u_invar G'"
    "Pair_Graph_U_RBT.ugraph_abs G' \<subseteq> Pair_Graph_U_RBT.ugraph_abs input_G"
    "G_edges_abs.is_spanning_forest (Pair_Graph_U_RBT.ugraph_abs G')"
  (* shows "sum c (Pair_Graph_U_RBT.ugraph_abs (Kruskal_MST c order)) \<le> sum c (Pair_Graph_U_RBT.ugraph_abs G')"  *)
  shows "sum c (Pair_Graph_U_RBT.ugraph_abs (Kruskal_MST order)) \<le>
 sum c (Pair_Graph_U_RBT.ugraph_abs G')"
proof-
  from \<open>G_edges_abs.is_spanning_forest (Pair_Graph_U_RBT.ugraph_abs G')\<close>
    have "graph_abs.has_no_cycle (Pair_Graph_U_RBT.ugraph_abs input_G) (Pair_Graph_U_RBT.ugraph_abs G')"
    unfolding G_edges_abs.is_spanning_forest_def by blast

  thm indep_graph_matroid_expr_3[OF pair_graph_u]

 (* thm Kruskal_Greedy.BestInGreedy_matroid_iff_opt[OF Kruskal_BestInGreedy_axioms Kruskal_sort_desc_axioms
      Kruskal_indep_system_axioms] pair_graph_u
*)
  have valid_soln: "Kruskal_Greedy.valid_solution (TYPE ('a)) edge_of input_G v1_of v2_of 
          (Kruskal_G_to_E G')" sorry
  from Kruskal_Greedy_opt_inst[OF nonneg_conv[OF assms(1)] assms(2) valid_soln]
  have "sum c' (Tree2.set_tree (Kruskal_G_to_E G'))
    \<le> sum c' (Tree2.set_tree (result (Kruskal_Greedy.BestInGreedy (TYPE ('a)) v1_of v2_of edge_of input_G 
(Kruskal_Greedy.initial_state c' order))))"
    by blast
  then have
      "sum c (Pair_Graph_U_RBT.ugraph_abs (Kruskal_E_to_G  (Kruskal_G_to_E G')))
    \<ge> sum c (Pair_Graph_U_RBT.ugraph_abs (Kruskal_E_to_G 
 (result (Kruskal_Greedy.BestInGreedy (TYPE ('a)) v1_of v2_of edge_of input_G (Kruskal_Greedy.initial_state c' order)))))"
   (*   using Kruskal_Graphs_Matroids_Proofs.costs_transformation[where E' ="(Kruskal_G_to_E G')" and
          E'' = "(result (Kruskal_Greedy.BestInGreedy (Kruskal_Greedy.initial_state c' order)))"]
    by blast*) sorry
  then
    show "sum c (Pair_Graph_U_RBT.ugraph_abs (Kruskal_MST order)) \<le> sum c (Pair_Graph_U_RBT.ugraph_abs G')"
    using Kruskal_Graphs_Matroids_Proofs.graph_to_edges_inverse[OF \<open>Pair_Graph_U_RBT.pair_graph_u_invar G'\<close>]
    using Kruskal_E_to_G_def sorry
qed
  


end

end
end
(* Example: Edge is implemented as pair of vertices where first element is always less than or equal
to second element *)
definition edge_of :: "('v::linorder) \<Rightarrow> 'v \<Rightarrow> ('v \<times> 'v)" where
  "edge_of u v = (if u \<le> v then (u, v) else (v, u))"

definition v1_of :: "('v \<times> 'v) \<Rightarrow> ('v::linorder)" where
  "v1_of e = fst e"

definition v2_of :: "('v \<times> 'v) \<Rightarrow> ('v::linorder)" where
  "v2_of e = snd e"
(*
definition "Kruskal_MST' input_G c' order = Kruskal_MST input_G v1_of v2_of edge_of c' order"
*)
(*
definition c where "c e = 0"

definition order where "order = []"

value "Kruskal_MST' (Leaf::((nat \<times> nat rbt) rbt)) c order"
*)


end