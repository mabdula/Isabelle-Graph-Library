theory Kruskal_Greedy2
  imports Matroids_Greedy.Best_In_Greedy Spanning_Trees Encoding
         Graph_Algorithms.DFS_Example Insertion_Sort_Desc "HOL-Library.Product_Lexorder"
begin

hide_const RBT_Set.insert
global_interpretation Pair_Graph_U_RBT: Pair_Graph_U_Specs
  where empty = empty and update = update and delete = delete and
    lookup = lookup and adjmap_inv = "M.invar" and vset_empty = "\<langle>\<rangle>" and
    insert = vset_insert and vset_delete = vset_delete and vset_inv = "vset_inv::(('v::linorder) rbt \<Rightarrow> bool)" and
    isin = isin and t_set = "Tree2.set_tree" and sel = sel
  defines add_edge =Pair_Graph_U_RBT.add_edge
    and  delete_edge =Pair_Graph_U_RBT.delete_edge
  by(simp add: Pair_Graph_U_Specs_def Pair_Graph_Specs_def M.Map_axioms S_C.Set_Choose_axioms)

find_theorems add_edge

text \<open>Instantiations for Greedy\<close>

lemma tree_split_case:
  "(case t of Leaf \<Rightarrow> True | _ \<Rightarrow> False) = (t = Leaf)"
  by (fastforce split: tree.splits) 

fun rbt_subseteq :: "('a::linorder) rbt \<Rightarrow> 'a rbt \<Rightarrow> bool" where
  "rbt_subseteq t1 t2 = (case (RBT.diff t1 t2) of Leaf \<Rightarrow> True | _ \<Rightarrow> False)"

lemma rbt_subseteq_correct:
  "vset_inv t1 \<Longrightarrow> vset_inv t2 \<Longrightarrow> (rbt_subseteq t1 t2) = (Tree2.set_tree t1 \<subseteq> Tree2.set_tree t2)"
proof(unfold rbt_subseteq.simps tree.split[of "\<lambda> x. x= (_ \<subseteq> _)" True "\<lambda> _ _ _. False" "RBT.diff t1 t2" ],
      goal_cases)
  case 1
  have is_empty_iff:"RBT.diff t1 t2 = \<langle>\<rangle> \<longleftrightarrow> Tree2.set_tree t1 - Tree2.set_tree t2 = {}"
    using 1  Tree2.eq_set_tree_empty  RBT.set_tree_diff[of t1 t2, symmetric]
    by (simp add: vset_inv_def)
  show ?case 
    using is_empty_iff by (subst Diff_eq_empty_iff[symmetric])fastforce
qed

lemma rbt_size_correct:
  "vset_inv X \<Longrightarrow> size X = card (Tree2.set_tree X)"
  unfolding set_inorder[symmetric]
proof(induction X rule: inorder.induct)
  case 1
  then show ?case by simp
next
  case (2 l a uu r)
  have inter_empty:"set (Tree2.inorder l) \<inter> Set.insert a (set (Tree2.inorder r)) = {}"
    using 2(3) bst.simps(2)[simplified Tree2.set_inorder[symmetric]]
    by (metis (no_types, lifting) Int_emptyI insert_iff not_less_iff_gr_or_eq vset_inv_def)
  have vset_inv_l: "vset_inv l" 
    by (metis "2.prems" RBT.inv_Node bst.simps(2) vset_inv_def)
  have vset_inv_r: "vset_inv r" 
    by (metis "2.prems" RBT.inv_Node bst.simps(2) vset_inv_def)
  have a_not_down: "a \<notin> set (Tree2.inorder r)" 
    using 2(3) bst.simps(2)[simplified Tree2.set_inorder[symmetric]] 
    by (metis not_less_iff_gr_or_eq vset_inv_def)
  show ?case 
   using a_not_down inter_empty 
   by(auto  simp add: card_Un_disjoint card_insert_if  2(1)[OF vset_inv_l] 2(2)[OF vset_inv_r])
qed

interpretation Custom_Set_RBT: Custom_Set
  where empty = "\<langle>\<rangle>" and insert = insert_rbt and delete = delete_rbt and invar = "vset_inv::(('e::linorder) rbt \<Rightarrow> bool)" and
    isin = isin and set = "Tree2.set_tree" and union = "RBT.union" and inter = "RBT.inter" and diff = "RBT.diff" and
    subseteq = rbt_subseteq and cardinality = size
  apply (subst Custom_Set_def)
  apply(intro conjI)
  subgoal
    using RBT.Set2_axioms
    by (metis RBT_Set.empty_def dfs.set_ops.Set2_axioms)
  subgoal
    apply (subst Custom_Set_axioms_def)
    using rbt_subseteq_correct rbt_size_correct by blast
  done


definition "set_of_sets_isin f a = f a"

lemma set_of_sets_isin_def': "set_of_sets_isin = id"
  using set_of_sets_isin_def by fastforce

interpretation Matroid_Specs_Inst: Matroid_Specs
  where set_empty = "\<langle>\<rangle>" and set_insert = insert_rbt and set_delete = delete_rbt and set_inv = "vset_inv::(('e::linorder) rbt \<Rightarrow> bool)" and
    set_isin = isin and to_set = "Tree2.set_tree" and union = "RBT.union" and inter = "RBT.inter" and diff = "RBT.diff" and
    subseteq = rbt_subseteq and cardinality = size and
    set_of_sets_isin = "set_of_sets_isin :: ('e rbt \<Rightarrow> bool) \<Rightarrow> 'e rbt \<Rightarrow> bool"
  apply (subst Matroid_Specs_def)
  apply (subst Indep_System_Specs_def)
  using Custom_Set_RBT.Custom_Set_axioms by blast

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

global_interpretation Kruskal_Graphs_Matroids: Encoding
  where empty = RBT_Set.empty and update = update and delete = RBT_Map.delete and
    lookup = lookup and adjmap_inv = "M.invar" and vset_empty = "\<langle>\<rangle>" and
    insert = insert_rbt and vset_delete = delete_rbt and vset_inv = "vset_inv::(('v::linorder) rbt \<Rightarrow> bool)" and
    isin = isin and t_set = "Tree2.set_tree" and sel = sel and

    set_empty = "\<langle>\<rangle>" and set_insert = insert_rbt and set_delete = delete_rbt and set_inv = "vset_inv::(('e::linorder) rbt \<Rightarrow> bool)" and
    set_isin = isin and to_set = "Tree2.set_tree" and union = "RBT.union" and inter = "RBT.inter" and diff = "RBT.diff" and
    adjmap_fold = "rbt_map_fold" and vset_fold = "rbt_set_fold" and set_fold_adjmap = "rbt_set_fold" and
    set_fold_vset = "rbt_set_fold"
    for v1_of :: "('e::linorder) \<Rightarrow> ('v::linorder)" and v2_of :: "('e::linorder) \<Rightarrow> ('v::linorder)" (*and 
        edge_of :: "('v::linorder) \<Rightarrow> 'v \<Rightarrow> ('e::linorder)"*) and c :: "('v set) \<Rightarrow> rat" and c' :: "'e \<Rightarrow> rat"
      defines (*graph_to_edges = Kruskal_Graphs_Matroids.graph_to_edges
and*) edges_to_graph = Kruskal_Graphs_Matroids.edges_to_graph
and edges_to_vertices = Kruskal_Graphs_Matroids.edges_to_vertices
  by (auto intro: Encoding.intro simp add: Custom_Set_RBT.Set2_axioms Pair_Graph_U_RBT.Pair_Graph_U_Specs_axioms)



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

lemma rbt_set_fold_correct: "vset_inv S \<Longrightarrow> \<exists>xs. distinct xs \<and> set xs = Tree2.set_tree S \<and> rbt_set_fold S f G = foldr f xs G"
  apply(subst rbt_set_fold_revinorder)
  apply(rule exI[of _ "rev (Tree2.inorder S)"])
  using  bst_distinct_inorder[of S]
  by(unfold set_inorder[symmetric] set_rev distinct_rev)(simp add: vset_inv_def )

locale Transforms =
fixes v1_of::"('e::linorder \<Rightarrow> 'v::linorder)" and v2_of::"'e \<Rightarrow> 'v" 
and input_G :: "'e rbt"
begin

definition Kruskal_E_to_G :: "('e::linorder) rbt \<Rightarrow> ('v \<times> ('v rbt)) rbt" where
  "Kruskal_E_to_G = edges_to_graph v1_of v2_of"

definition Kruskal_E_to_V :: "('e::linorder) rbt \<Rightarrow> ('v rbt)" where
  "Kruskal_E_to_V = edges_to_vertices v1_of v2_of"

definition indep_graph_matroid :: "('e::linorder) rbt \<Rightarrow> bool" where
  "indep_graph_matroid = (\<lambda> E. undirected_multigraph_spec.has_no_cycle_multi (\<lambda> e. {v1_of e, v2_of e})
                              (Tree2.set_tree input_G) (Tree2.set_tree E))"

definition "local_indep_oracle e X = 
((rbt_subseteq (vset_insert e X) input_G) \<and>
                   (lookup (Kruskal_E_to_G X) (v2_of e) \<noteq> None \<and> lookup (Kruskal_E_to_G X) (v1_of e) \<noteq> None\<longrightarrow>
                   return (dfs_impl (Kruskal_E_to_G X) (v2_of e) (dfs_initial_state (v1_of e))) 
                    = NotReachable))"

end

global_interpretation transforms: Transforms
  where v1_of = v1_of and v2_of = v2_of  and input_G = input_G
  for v1_of::"'e::linorder \<Rightarrow> 'a::linorder" and v2_of edge_of input_G
  defines Kruskal_E_to_G=transforms.Kruskal_E_to_G
   and Kruskal_E_to_V=transforms.Kruskal_E_to_V
   and indep_graph_matroid=transforms.indep_graph_matroid
   and local_indep_oracle= transforms.local_indep_oracle
  done

global_interpretation Kruskal_Greedy: Best_In_Greedy'
  where set_empty = "\<langle>\<rangle>" and set_insert = insert_rbt and set_delete = delete_rbt 
     and set_inv = "vset_inv::(('e::linorder) rbt \<Rightarrow> bool)" and
    set_isin = isin and to_set = "Tree2.set_tree" and union = "RBT.union" and inter = "RBT.inter" and diff = "RBT.diff" and
    subseteq = rbt_subseteq and cardinality = size and
    set_of_sets_isin = "set_of_sets_isin :: (('e::linorder) rbt \<Rightarrow> bool) \<Rightarrow> 'e rbt \<Rightarrow> bool" and 
    carrier = input_G and 
    indep_set = "indep_graph_matroid v1_of v2_of input_G" and
    sort_desc = insort_key_desc and 
    local_indep_oracle = "local_indep_oracle v1_of v2_of input_G"
    and wrapper_insert = insert_rbt
and wrapper_invar = "vset_inv::(('e::linorder) rbt \<Rightarrow> bool)"
and remove_wrapper = id
and wrapper_empty = Leaf
  for v1_of::"'e::linorder \<Rightarrow>'a::linorder" and v2_of input_G
  defines kruskal' = Kruskal_Greedy.BestInGreedy'
    and  kruskal = Kruskal_Greedy.BestInGreedy
    and   kruskal_init = Kruskal_Greedy.initial_state
    and   kruskal_init' = Kruskal_Greedy.initial_state'
    and indep' = "Kruskal_Greedy.indep'"
    and to_ordinary = Kruskal_Greedy.to_ordinary
  apply (subst Best_In_Greedy'_def, subst Best_In_Greedy_def)
 by(auto intro!: Best_In_Greedy'_axioms.intro 
simp add: Matroid_Specs_Inst.Matroid_Specs_axioms Pair_Graph_RBT.set.Set_axioms
 dfs.Graph.vset.set.invar_insert set.invar_empty)

locale Kruskal_Proof_Matroid_Edges =
Transforms where v1_of = "v1_of::'e::linorder \<Rightarrow> 'v::linorder" for v1_of+
assumes v1_never_v2:"\<And> e. v1_of e \<noteq> v2_of e"
begin

context 
  assumes  G_good: "vset_inv input_G"
begin
lemma Encoding_Proofs_axioms:
 " Encoding_Proofs_axioms t_set M.invar vset_inv lookup vset_inv t_set rbt_map_fold
     rbt_set_fold rbt_set_fold rbt_set_fold v1_of v2_of"(* edge_of"*)
proof(rule Encoding_Proofs_axioms.intro, goal_cases)
  case (1 G S f)
  then show ?case 
    by (simp add: rbt_map_fold_correct)
next
  case (2 G S f)
  then show ?case 
    by (simp add: rbt_set_fold_correct)
next
  case (3 V f S)
  then show ?case 
    by (simp add: rbt_set_fold_correct)
next
  case (4 V f S)
  then show ?case 
    by (simp add: rbt_set_fold_correct)
next
  case 5
  then show ?case 
    by (simp add: dfs.Graph.finite_vsetsI)
next
  case (6 e)
  then show ?case 
    by (simp add: v1_never_v2)
qed
(*
next
  case (7 x y)
  then show ?case
    by (simp add: v1_of_edge_of)
next
  case (8 x y)
  then show ?case
    by (simp add: v2_of_edge_of)
qed
*)
interpretation Kruskal_Graphs_Matroids_proofs: Encoding_Proofs
  where empty = RBT_Set.empty and update = update and delete = RBT_Map.delete and
    lookup = lookup and adjmap_inv = "M.invar" and vset_empty = "\<langle>\<rangle>" and
    insert = insert_rbt and vset_delete = delete_rbt and vset_inv = "vset_inv::(('v::linorder) rbt \<Rightarrow> bool)" and
    isin = isin and t_set = "Tree2.set_tree" and sel = sel and

    set_empty = "\<langle>\<rangle>" and set_insert = insert_rbt and set_delete = delete_rbt and set_inv = "vset_inv::(('e::linorder) rbt \<Rightarrow> bool)" and
    set_isin = isin and to_set = "Tree2.set_tree" and union = "RBT.union" and inter = "RBT.inter" and diff = "RBT.diff" and
    adjmap_fold = "rbt_map_fold" and vset_fold = "rbt_set_fold" and set_fold_adjmap = "rbt_set_fold" and
    set_fold_vset = "rbt_set_fold"
  for c :: "('v set) \<Rightarrow> rat" and c' :: "'e \<Rightarrow> rat"
  by(auto intro!: Encoding_Proofs.intro  Encoding_Proofs_axioms 
           simp add: Encoding_def 
            Pair_Graph_U_RBT.Pair_Graph_U_Specs_axioms Custom_Set_RBT.Set2_axioms)

lemma pair_graph_u_invar:
"vset_inv S \<Longrightarrow> Pair_Graph_U_RBT.pair_graph_u_invar (Kruskal_E_to_G S)"
  by (simp add: Kruskal_Graphs_Matroids_proofs.edges_invar_imp_graph_invar edges_to_graph_def local.Kruskal_E_to_G_def)

lemma same_dgraphabs:"dfs.Graph.digraph_abs = G.digraph_abs"
  by (simp add: RBT_Set.empty_def)

abbreviation "to_dbltn == (\<lambda>x. {v1_of x, v2_of x})"

lemma to_dbltn_sym: "{v2_of x, v1_of x} = to_dbltn x" by auto

interpretation undirected_multigraph: undirected_multigraph to_dbltn "Tree2.set_tree G"
  using v1_never_v2 by (auto intro!:  undirected_multigraph.intro)

lemma local_indep_oracle_correct:
  assumes "vset_inv S"
        "indep' v1_of v2_of input_G (id S)"
        "rbt_subseteq (id S) input_G"
        "e \<notin> t_set (id S)"
 shows "local_indep_oracle e S = indep' v1_of v2_of input_G (vset_insert e (id S))"
  apply(insert assms)
  unfolding indep'_def Matroid_Specs_Inst.indep_def Kruskal_Greedy2.indep_graph_matroid_def
            indep_graph_matroid_def set_of_sets_isin_def 
proof(goal_cases)
  case 1
  note case_assms = this
  have first_eq:"rbt_subseteq (vset_insert e S) input_G = (t_set (vset_insert e (id S)) \<subseteq> t_set input_G)" 
    using G_good assms(1) dfs.Graph.vset.set.invar_insert rbt_subseteq_correct by auto
  have second_eq:"(((lookup (local.Kruskal_E_to_G S) (v2_of e) \<noteq> None \<and> lookup (Kruskal_E_to_G S) (v1_of e) \<noteq> None) \<longrightarrow>
                 (return (dfs_impl (local.Kruskal_E_to_G S) (v2_of e) 
                 (dfs_initial_state (v1_of e))) = NotReachable))) =
                (\<nexists>u. Ex (undirected_multigraph_spec.decycle_multi (\<lambda>e. {v1_of e, v2_of e}) (t_set (vset_insert e (id S)))u))"
    if additional_assm: "insert e (t_set  S) \<subseteq> t_set input_G"
  proof-
    have digraph_abs_is:"G.digraph_abs (Kruskal_E_to_G S) =
     (\<lambda>e. (v1_of e, v2_of e)) ` t_set S \<union> (\<lambda>e. (v2_of e, v1_of e)) ` t_set S"
     by(auto intro!: Kruskal_Graphs_Matroids_proofs.digraph_abs_of_edges_of_to_graph_general
            simp add: assms(1) Kruskal_E_to_G_def edges_to_graph_def )
   have ugraph_abs_is: "Pair_Graph_U_RBT.ugraph_abs (Kruskal_E_to_G S) = to_dbltn ` (t_set  S)"
    by(auto intro!: Kruskal_Graphs_Matroids_proofs.dbltn_set_and_ugraph_abs[symmetric]
            simp add: assms(1) Kruskal_E_to_G_def edges_to_graph_def )
   have pair_graph_u_invar:"Pair_Graph_U_RBT.pair_graph_u_invar (edges_to_graph  v1_of  v2_of S)" 
     using assms(1) local.Kruskal_E_to_G_def pair_graph_u_invar by auto
   have double_ex_I: "rest x y \<Longrightarrow> \<exists>v1 v2.
       {x, y} = {v1, v2} \<and> rest v1 v2" for x y rest by auto
   have lookup_in_dVs:"lookup (local.Kruskal_E_to_G S) x = Some y\<Longrightarrow> 
          x \<in> dVs (dfs.Graph.digraph_abs (local.Kruskal_E_to_G S))" for x y
     using Kruskal_Graphs_Matroids_proofs.edges_invar_imp_graph_invar(2)[OF assms(1)]
            S_C.choose  
     by(unfold  dfs.Graph.digraph_abs_def DFS_Example.neighbourhood_def)
       (auto simp add: Kruskal_E_to_G_def edges_to_graph_def
                      neighbourhood_def[symmetric] dfs.Graph.neighbourhood_def dVs_def
               intro!: exI[of _ "{x, sel y}"]  double_ex_I)
   have "lookup (local.Kruskal_E_to_G S) (v1_of e) = Some y \<Longrightarrow>
         DFS.DFS_axioms isin t_set adj_inv vset_empty vset_inv lookup
          (local.Kruskal_E_to_G S) (v1_of e)" for y
     unfolding DFS.DFS_axioms_def[OF dfs.DFS_axioms]
     using   lookup_in_dVs pair_graph_u_invar
     by(unfold Pair_Graph_U_RBT.pair_graph_u_invar_def Kruskal_E_to_G_def adj_inv_def)
     simp
   hence DFS_thms: "lookup (local.Kruskal_E_to_G S) (v1_of e) \<noteq> None \<Longrightarrow>
        DFS_thms map_empty RBT_Map.delete vset_insert isin t_set sel update adj_inv vset_empty vset_delete vset_inv
     vset_union vset_inter vset_diff lookup (Kruskal_E_to_G S) (v1_of e)"
     by(auto intro!: DFS_thms.intro dfs.DFS_axioms DFS_thms_axioms.intro )
   have graph_abs_with_e: "graph_abs (to_dbltn ` insert e (t_set S))"
     using v1_never_v2 by (auto simp add: graph_abs_def dblton_graph_def Vs_def)
   have graph_abs_without_e: "graph_abs (to_dbltn `(t_set S))"
     using graph_abs_mono graph_abs_with_e by auto
   have graph_abs_vset_insert:"graph_abs (to_dbltn ` t_set (vset_insert e S))"
     using RBT.set_tree_insert[of S] case_assms(1) graph_abs_with_e 
     by(simp add:vset_inv_def)
   show ?thesis 
     unfolding dfs_impl_def dfs_initial_state_def
   proof(cases "lookup (local.Kruskal_E_to_G S) (v1_of e) \<noteq> None 
         \<and> lookup (local.Kruskal_E_to_G S) (v2_of e) \<noteq> None", goal_cases)
     case 1
     hence 1: "lookup (local.Kruskal_E_to_G S) (v1_of e) \<noteq> None" 
              "lookup (local.Kruskal_E_to_G S) (v2_of e) \<noteq> None" by auto
     note one = this
     show ?case
     proof(subst DFS_thms.DFS_to_DFS_impl[OF DFS_thms, symmetric, OF 1(1)], rule, all \<open>rule ccontr\<close>, goal_cases)
       case 1
       then obtain u C where uC_prop:"undirected_multigraph_spec.decycle_multi to_dbltn
                 (t_set (vset_insert e S)) u C" by auto
       moreover have  not_cycle_old:"\<not> undirected_multigraph_spec.decycle_multi to_dbltn
                 (t_set S) u C" 
         using case_assms(2) 
         by(simp add: id_def undirected_multigraph_spec.has_no_cycle_multi_def)
       ultimately have e_and_C:"e \<in> set C" "set C \<subseteq> (t_set (vset_insert e S))"
         unfolding undirected_multigraph_spec.decycle_multi_def     
        using epath_subset_other_set[of "insert {v1_of e, v2_of e} (to_dbltn ` t_set S)"
                                    u "map _ C" u , simplified list.set_map,OF _ image_mono] 
        by (auto simp add: Pair_Graph_RBT.set.set_insert[OF case_assms(1)])
      then obtain C1 C2 where C_split:"C = C1@[e]@C2"
        by (metis append_Cons append_self_conv2 split_list_last)
      obtain q where q_prop:"walk_betw (to_dbltn ` (insert e (t_set S))) u q u" "map to_dbltn C = edges_of_path q"
        using graph_abs.epath_imp_walk_betw[of _ u "map to_dbltn C" u, OF graph_abs_with_e] 
              uC_prop 
         by(auto simp add: undirected_multigraph_spec.decycle_multi_def  Pair_Graph_RBT.set.set_insert[OF case_assms(1)])
      
       hence e_in_p: "to_dbltn e \<in> set (edges_of_path q)"
        by (metis (mono_tags, lifting) \<open>e \<in> set C\<close> image_set rev_image_eqI)
      have lengthq: "length q \<ge> 2" 
        using \<open>to_dbltn e \<in> set (edges_of_path q)\<close> edges_of_path_nempty by fastforce
      have v1v2: "v1_of e \<noteq> v2_of e" 
        by (simp add: v1_never_v2)
    show ?case proof(cases "lookup (local.Kruskal_E_to_G S) (v2_of e)")
      case None
       thus ?thesis 
        by (simp add: one(2))
    next
      case (Some neighb)
      have "\<exists>q. walk_betw (to_dbltn ` t_set (vset_insert e S)) u q u \<and> map to_dbltn C = edges_of_path q"
        using graph_abs_vset_insert  uC_prop 
        by(auto intro:graph_abs.epath_imp_walk_betw simp add: undirected_multigraph.decycle_multi_def)
      have no_distinct_path:"\<nexists>p. distinct p \<and>
              vwalk_bet (dfs.Graph.digraph_abs (local.Kruskal_E_to_G S)) (v1_of e) p (v2_of e)"
        using DFS_thms.DFS_correct_1[OF DFS_thms] Some  one 1 by blast
      have no_other_e:"(to_dbltn e) \<notin> (to_dbltn ` t_set S)"
      proof(rule, rule ccontr, goal_cases)
        case 1
        then obtain d where d_prop:"to_dbltn d = to_dbltn e" "d \<in> t_set S" by auto
        hence "{(v1_of d, v2_of d), (v2_of d, v1_of d)} \<subseteq> (dfs.Graph.digraph_abs (local.Kruskal_E_to_G S))"
          by (simp add: RBT_Set.empty_def digraph_abs_is)
        moreover have "(v1_of e, v2_of e) = (v1_of d, v2_of d)\<or>(v1_of e, v2_of e) = (v2_of d, v1_of d)"
          using d_prop by(unfold doubleton_eq_iff) presburger
        ultimately have "vwalk_bet (dfs.Graph.digraph_abs (Kruskal_E_to_G S)) 
                         (v1_of e) [v1_of e, v2_of e] (v2_of e)" 
          by fastforce
        moreover have "distinct [v1_of e, v2_of e]"
          using v1v2 by auto
        ultimately show ?case 
          using   no_distinct_path by blast
      qed 
      moreover have dbltn_inj:"inj_on to_dbltn (t_set S) "
        using case_assms(2) undirected_multigraph.has_no_cycle_multi_to_dbltn_inj by simp
      ultimately have dbltn_inj_big:"inj_on to_dbltn (insert e (t_set S))" by auto
      moreover have C_subset:"set C \<subseteq> (insert e (t_set S))"
        using case_assms(1) dfs.Graph.vset.set.set_insert e_and_C(2) by auto
      ultimately have inj_C:"inj_on to_dbltn (set C)" 
        by (meson inj_on_subset)
      have distinct_edges_q:"distinct (edges_of_path q)"
        using q_prop(2) distinct_map[of to_dbltn C] uC_prop e_and_C inj_C
        by(auto simp add: undirected_multigraph.decycle_multi_def) 
      have e_vs_in_new_v_set:"{v1_of e, v2_of e} \<subseteq> Vs (to_dbltn ` insert e (t_set S))"
        by (simp add: vs_member)
      then obtain q1 q2 where q1_q2_prop: "q = q1@[v1_of e, v2_of e]@ q2 \<or> q = q1@[v2_of e, v1_of e]@ q2"
        using undirected_multigraph.edges_to_path_split_by_edge[of _ _ "v1_of e" "v2_of e"] e_in_p by fast
       obtain q' where  path_without_e:"walk_betw (to_dbltn `  (t_set S)) (v1_of e) q' (v2_of e)"
       proof(cases rule: disjE[OF q1_q2_prop], all "cases q1", all \<open>cases q2\<close>, goal_cases)
         case 1
         then show ?case 
           using q_prop(1) v1v2 walk_between_nonempty_pathD(3) walk_between_nonempty_pathD(4) by fastforce
       next
         case (2 a list)
         hence a1:"walk_betw (to_dbltn ` insert e (t_set S)) u (q1 @ [v1_of e]) (v1_of e)"
           using q_prop(1) by (intro walk_pref[of _ u q1 "v1_of e" "v2_of e # q2" u]) force
         moreover have a2:"walk_betw (to_dbltn ` insert e (t_set S)) (v2_of e) (v2_of e # q2) u"
           using q_prop(1) 2(2)  by(intro walk_suff[of _ u "q1@[v1_of e]" "v2_of e" q2 u]) force 
         ultimately have a3:"walk_betw (to_dbltn ` insert e (t_set S)) (v2_of e) ([v2_of e] @ q2) (v1_of e)"
           by (simp add: "2"(3) walk_betw_def)
         have a4:"set (edges_of_path ([v2_of e] @ q2)) \<subseteq> set (edges_of_path q)"
           using "2"(2) "2"(3) by auto
         moreover have a5:"to_dbltn e \<notin> set (edges_of_path ([v2_of e] @ q2))" 
           using "2"(2) "2"(3) distinct_edges_q by auto
         ultimately have a6:"set (edges_of_path ([v2_of e] @ q2)) \<subseteq> (to_dbltn `(t_set S))" 
           using a3 graph_abs.path_ball_edges' graph_abs_with_e walk_between_nonempty_pathD(1) by fastforce
         have "walk_betw (to_dbltn `(t_set S)) (v2_of e) ([v2_of e] @ q2) (v1_of e)"  
           using walk_betw_strengthen[OF a3 _ a6] 2(4) by simp
         hence "walk_betw (to_dbltn `(t_set S)) (v1_of e) (rev ([v2_of e] @ q2)) (v2_of e)" 
           by (meson walk_symmetric)
         thus ?case
           using 2(1) by simp         
       next
         case (3 a list)
         hence a1:"walk_betw (to_dbltn ` insert e (t_set S)) u (q1 @ [v1_of e]) (v1_of e)"
           using q_prop(1) by (intro walk_pref[of _ u q1 "v1_of e" "v2_of e # q2" u]) force
         moreover have a2:"walk_betw (to_dbltn ` insert e (t_set S)) (v2_of e) (v2_of e # q2) u"
           using q_prop(1) 3(2)  by(intro walk_suff[of _ u "q1@[v1_of e]" "v2_of e" q2 u]) force 
         ultimately have a3:"walk_betw (to_dbltn ` insert e (t_set S)) (v2_of e) (q1@ [v1_of e] ) (v1_of e)"
           by (simp add: "3"(4) walk_betw_def)
         have a4:"set (edges_of_path (q1@ [v1_of e])) \<subseteq> set (edges_of_path q)" 
           using 3(2-) edges_of_path_append_subset_2 by fastforce
         moreover have a5:"to_dbltn e \<notin> set (edges_of_path (q1@ [v1_of e]))" 
           using  distinct_edges_q by(unfold 3(2) edges_of_path_symmetric_split) simp
         ultimately have a6:"set (edges_of_path (q1@ [v1_of e])) \<subseteq> (to_dbltn `(t_set S))" 
           using a3 graph_abs.path_ball_edges' graph_abs_with_e walk_between_nonempty_pathD(1) by fastforce
         have "walk_betw (to_dbltn `(t_set S)) (v2_of e) (q1@ [v1_of e]) (v1_of e)"  
           using walk_betw_strengthen[OF a3 _ a6] 3(3) by simp
         hence "walk_betw (to_dbltn `(t_set S)) (v1_of e) (rev (q1@ [v1_of e])) (v2_of e)" 
           by (meson walk_symmetric)
         thus ?case
           using 3(1) by simp 
       next
         case (4 a list aa lista)
         hence a1:"walk_betw (to_dbltn ` insert e (t_set S)) u (q1 @ [v1_of e]) (v1_of e)"
           using q_prop(1) by (intro walk_pref[of _ u q1 "v1_of e" "v2_of e # q2" u]) force
         moreover have a2:"walk_betw (to_dbltn ` insert e (t_set S)) (v2_of e) (v2_of e # q2) u"
           using q_prop(1) 4(2)  by(intro walk_suff[of _ u "q1@[v1_of e]" "v2_of e" q2 u]) force     
         have a4:"set (edges_of_path (q1@ [v1_of e])) \<subseteq> set (edges_of_path q)" 
           using 4(2-) edges_of_path_append_subset_2 by fastforce
         moreover have a5:"to_dbltn e \<notin> set (edges_of_path (q1@ [v1_of e]))" 
           using  distinct_edges_q by(unfold 4(2) edges_of_path_symmetric_split) simp
         ultimately have a6:"set (edges_of_path (q1@ [v1_of e])) \<subseteq> (to_dbltn `(t_set S))" 
           using graph_abs.path_ball_edges' graph_abs_with_e walk_between_nonempty_pathD(1) by fastforce
         have a4:"set (edges_of_path ([v2_of e] @ q2)) \<subseteq> set (edges_of_path q)"
           using "4"(2) edges_of_path_append_subset by fastforce
         moreover have a5:"to_dbltn e \<notin> set (edges_of_path ([v2_of e] @ q2))" 
           using  "4"(4) distinct_edges_q by(unfold 4(2) edges_of_path_symmetric_split) simp 
         moreover have a3:"walk_betw (to_dbltn ` insert e (t_set S)) (v2_of e) ([v2_of e] @ q2) u"
           using a2 a1 by simp 
         ultimately have a7:"set (edges_of_path ([v2_of e] @ q2)) \<subseteq> (to_dbltn `(t_set S))"
           using  a1 a2 graph_abs.path_ball_edges' graph_abs_with_e walk_between_nonempty_pathD(1) by fast 
         have "walk_betw (to_dbltn `(t_set S)) u (q1@ [v1_of e]) (v1_of e)"  
           using walk_betw_strengthen 4(3) a1 a6 by fastforce
         moreover have "walk_betw (to_dbltn `(t_set S)) (v2_of e) ( [v2_of e]@q2)u"  
           using walk_betw_strengthen 4(3)  "4"(4) a3 a7 by fastforce
         ultimately have  "walk_betw (to_dbltn `(t_set S)) (v2_of e) ( ([v2_of e]@q2@(tl q1)@[v1_of e])) (v1_of e)" 
           using "4"(3) walk_transitive_2 by fastforce
         then show ?case 
           using 4(1)[of "rev ([v2_of e]@q2@(tl q1)@[v1_of e])"]
           by (meson walk_symmetric)
       next
         case 5
         then show ?case 
           using q_prop(1) v1v2 walk_between_nonempty_pathD(3) walk_between_nonempty_pathD(4) by fastforce
       next
         case (6 a list)
         hence a1:"walk_betw (to_dbltn ` insert e (t_set S)) u (q1 @ [v2_of e]) (v2_of e)"
           using q_prop(1) by (intro walk_pref[of _ u q1 "v2_of e" "v1_of e # q2" u]) force
         moreover have a2:"walk_betw (to_dbltn ` insert e (t_set S)) (v1_of e) (v1_of e # q2) u"
           using q_prop(1) 6(2)  by(intro walk_suff[of _ u "q1@[v2_of e]" "v1_of e" q2 u]) force 
         ultimately have a3:"walk_betw (to_dbltn ` insert e (t_set S)) (v1_of e) ([v1_of e] @ q2) (v2_of e)"
           by (simp add: "6"(3) walk_betw_def)
         have a4:"set (edges_of_path ([v1_of e] @ q2)) \<subseteq> set (edges_of_path q)"
           using "6"(2) "6"(3) by auto
         moreover have a5:"to_dbltn e \<notin> set (edges_of_path ([v1_of e] @ q2))" 
           using "6"(2) "6"(3) distinct_edges_q 
           by (simp add: insert_commute)
         ultimately have a6:"set (edges_of_path ([v1_of e] @ q2)) \<subseteq> (to_dbltn `(t_set S))" 
           using a3 graph_abs.path_ball_edges' graph_abs_with_e walk_between_nonempty_pathD(1) by fastforce
         have "walk_betw (to_dbltn `(t_set S)) (v1_of e) ([v1_of e] @ q2) (v2_of e)"  
           using walk_betw_strengthen[OF a3 _ a6] 6(4) by simp
         thus ?case
           using 6(1) by simp         
       next
         case (7 a list)
         hence a1:"walk_betw (to_dbltn ` insert e (t_set S)) u (q1 @ [v2_of e]) (v2_of e)"
           using q_prop(1) by (intro walk_pref[of _ u q1 "v2_of e" "v1_of e # q2" u]) force
         moreover have a2:"walk_betw (to_dbltn ` insert e (t_set S)) (v1_of e) (v1_of e # q2) u"
           using q_prop(1) 7(2)  by(intro walk_suff[of _ u "q1@[v2_of e]" "v1_of e" q2 u]) force 
         ultimately have a3:"walk_betw (to_dbltn ` insert e (t_set S)) (v1_of e) (q1@ [v2_of e] ) (v2_of e)"
           by (simp add: "7"(4) walk_betw_def)
         have a4:"set (edges_of_path (q1@ [v2_of e])) \<subseteq> set (edges_of_path q)" 
           using 7(2-) edges_of_path_append_subset_2 by fastforce
         moreover have a5:"to_dbltn e \<notin> set (edges_of_path (q1@ [v2_of e]))" 
           using  distinct_edges_q by(unfold 7(2) edges_of_path_symmetric_split to_dbltn_sym) auto
         ultimately have a6:"set (edges_of_path (q1@ [v2_of e])) \<subseteq> (to_dbltn `(t_set S))" 
           using a3 graph_abs.path_ball_edges' graph_abs_with_e walk_between_nonempty_pathD(1) by fastforce
         have "walk_betw (to_dbltn `(t_set S)) (v1_of e) (q1@ [v2_of e]) (v2_of e)"  
           using walk_betw_strengthen[OF a3 _ a6] 7(3) by simp
         thus ?case
           using 7(1) by simp 
       next
         case (8 a list aa lista)
         hence a1:"walk_betw (to_dbltn ` insert e (t_set S)) u (q1 @ [v2_of e]) (v2_of e)"
           using q_prop(1) by (intro walk_pref[of _ u q1 "v2_of e" "v1_of e # q2" u]) force
         moreover have a2:"walk_betw (to_dbltn ` insert e (t_set S)) (v1_of e) (v1_of e # q2) u"
           using q_prop(1) 8(2)  by(intro walk_suff[of _ u "q1@[v2_of e]" "v1_of e" q2 u]) force     
         have a4:"set (edges_of_path (q1@ [v2_of e])) \<subseteq> set (edges_of_path q)" 
           using 8(2-) edges_of_path_append_subset_2 by fastforce
         moreover have a5:"to_dbltn e \<notin> set (edges_of_path (q1@ [v2_of e]))" 
           using  distinct_edges_q by(unfold 8(2) edges_of_path_symmetric_split to_dbltn_sym) simp
         ultimately have a6:"set (edges_of_path (q1@ [v2_of e])) \<subseteq> (to_dbltn `(t_set S))" 
           using graph_abs.path_ball_edges' graph_abs_with_e walk_between_nonempty_pathD(1) by fastforce
         have a4:"set (edges_of_path ([v1_of e] @ q2)) \<subseteq> set (edges_of_path q)"
           using 8(2) edges_of_path_append_subset by fastforce
         moreover have a5:"to_dbltn e \<notin> set (edges_of_path ([v1_of e] @ q2))" 
           using 8(4) distinct_edges_q by(unfold 8(2) edges_of_path_symmetric_split to_dbltn_sym) simp 
         moreover have a3:"walk_betw (to_dbltn ` insert e (t_set S)) (v1_of e) ([v1_of e] @ q2) u"
           using a2 a1 by simp 
         ultimately have a7:"set (edges_of_path ([v1_of e] @ q2)) \<subseteq> (to_dbltn `(t_set S))"
           using  a1 a2 graph_abs.path_ball_edges' graph_abs_with_e walk_between_nonempty_pathD(1) by fast 
         have "walk_betw (to_dbltn `(t_set S)) u (q1@ [v2_of e]) (v2_of e)"  
           using walk_betw_strengthen 8(3) a1 a6 by fastforce
         moreover have "walk_betw (to_dbltn `(t_set S)) (v1_of e) ( [v1_of e]@q2)u"  
           using walk_betw_strengthen 8(3)  8(4) a3 a7 by fastforce
         ultimately have  "walk_betw (to_dbltn `(t_set S)) (v1_of e) ( ([v1_of e]@q2@(tl q1)@[v2_of e])) (v2_of e)" 
           using 8(3) walk_transitive_2 by fastforce
         then show ?case using 8(1) by auto
       qed
       have  dfs_vwalk:"vwalk_bet (dfs.Graph.digraph_abs (local.Kruskal_E_to_G S)) (v1_of e) q' (v2_of e)"
         apply(subst same_dgraphabs, subst Pair_Graph_U_RBT.ugraph_abs_digraph_abs[symmetric])
         using local.Kruskal_E_to_G_def pair_graph_u_invar apply simp
         using  graph_abs.walk_betw_iff_vwalk_bet[OF graph_abs_without_e]  path_without_e 
         by (simp  add: ugraph_abs_is )
       obtain q'' where "vwalk_bet (dfs.Graph.digraph_abs (local.Kruskal_E_to_G S)) (v1_of e) q'' (v2_of e)"
                             "distinct q''" 
         using  vwalk_bet_to_distinct_is_distinct_vwalk_bet[OF dfs_vwalk]
         by(auto simp add: distinct_vwalk_bet_def)
       thus False 
         using no_distinct_path by blast
     qed
   next
     case 2
     note two = this
     show ?case 
     proof(cases "lookup (local.Kruskal_E_to_G S) (v2_of e)")
       case None 
       hence "lookup (local.Kruskal_E_to_G S) (v1_of e) = None" 
         using two(2) by blast
       thus False 
         by (simp add: one)
     next
       case (Some neighbs)
       hence dfs_reachable:"return
         (dfs.DFS (local.Kruskal_E_to_G S) (v2_of e) (DFS.initial_state vset_insert vset_empty (v1_of e))) =
             Reachable" 
         using two(2) return.exhaust by auto
       then obtain p where p_vwalk:"vwalk_bet (dfs.Graph.digraph_abs (local.Kruskal_E_to_G S)) (v1_of e)
                                      p (v2_of e)"
         using DFS_thms.DFS_correct_2[OF DFS_thms[OF one(1)]] dfs_reachable by auto
       have walk_betw_around_e:"walk_betw (to_dbltn ` t_set S) (v1_of e) p (v2_of e)"
         apply(subst  ugraph_abs_is[symmetric], subst graph_abs.walk_betw_iff_vwalk_bet, simp add: graph_abs_without_e ugraph_abs_is)
         using  pair_graph_u_invar  p_vwalk 
         by(auto simp add: Pair_Graph_U_RBT.ugraph_abs_digraph_abs same_dgraphabs Kruskal_E_to_G_def)
       have "epath (to_dbltn ` t_set S) (v1_of e) (edges_of_path p) (v2_of e)" 
         by(auto intro!: graph_abs.walk_betw_imp_epath simp add: walk_betw_around_e graph_abs_without_e)
       moreover then obtain p' where p'_prop:"map to_dbltn p' = edges_of_path p" "set p' \<subseteq>  (t_set S)"
         using undirected_multigraph.edges_of_path_to_multigraph_path[OF epath_edges_subset]
         by blast 
       ultimately have epath_first_path:"epath (to_dbltn `  (t_set S)) (v1_of e) (map to_dbltn p') (v2_of e)"  
         by simp
       then obtain p'' where p''_prop:"epath (to_dbltn ` t_set S) (v1_of e) p'' (v2_of e)" 
                       "set p'' \<subseteq> set (map to_dbltn p')" "distinct p''"
         using  epath_distinct_epath by fast
       obtain p_mul where p_mul: "map to_dbltn p_mul = p''" "set p_mul \<subseteq> set p'"
         using p''_prop(2) map_eq_Cons_conv by(induction p'')  fastforce+
       hence epath_p_mul:"epath (to_dbltn ` t_set S) (v1_of e) (map to_dbltn p_mul) (v2_of e)"
         using p''_prop(1) by blast
       hence epath_first_path:"epath (to_dbltn ` (insert e (t_set S))) (v1_of e) (map to_dbltn p_mul) (v2_of e)"  
         by (auto intro: epath_subset image_mono subset_insertI)
       moreover have "epath (to_dbltn ` (insert e (t_set S))) (v2_of e) [to_dbltn e] (v1_of e)" 
         using v1_never_v2[of e] by(auto intro!: epath_single)
       ultimately have epath3:"epath (to_dbltn ` (insert e (t_set S))) (v1_of e) 
                              (map to_dbltn (p_mul@[e])) (v1_of e)" 
         by (auto intro: epath_append)
       moreover have "set (p_mul@[e]) \<subseteq> insert e (t_set S)" 
         using p'_prop(2) p_mul(2) by auto
       moreover have "2 \<le> length (p_mul@[e])" 
         using epath_non_empty[OF epath_p_mul, simplified length_map] 
         by (simp add: v1_never_v2)
       moreover have "distinct (p_mul@[e])" 
       proof-
         have "distinct p_mul"
           using p_mul(1)  p''_prop(3) by (auto simp add: distinct_map)
         moreover have "set p_mul \<subseteq> t_set S" 
           using p'_prop(2) p_mul(2) by order
         ultimately show ?thesis using assms(4) by auto
       qed
       ultimately have "undirected_multigraph.decycle_multi (t_set (vset_insert e (id S))) (v1_of e) (p_mul@[e])" 
          by (simp add: undirected_multigraph.decycle_multi_def  case_assms(1) dfs.Graph.vset.set.set_insert)
        thus ?thesis 
         using 2(1) by simp
     qed
   qed
 next
   case 2
   have "(\<nexists>u. Ex (undirected_multigraph.decycle_multi (t_set (vset_insert e (id S))) u))"
   proof(rule ccontr,goal_cases)
     case 1
     then obtain u C where uC:"undirected_multigraph.decycle_multi (insert e (t_set S)) u C"
       using case_assms(1) dfs.Graph.vset.set.set_insert by fastforce
     hence C_prop: "epath (to_dbltn ` insert e (t_set S)) u (map to_dbltn C) u"
                    "set C \<subseteq> insert e (t_set S)" " 2 \<le> length C" "distinct C"
       using uC[simplified undirected_multigraph.decycle_multi_def] by auto
     have e_in_C:"e \<in> set C"
     proof(rule ccontr, goal_cases)
       case 1
       hence "undirected_multigraph.decycle_multi (t_set S) u C"
         using uC epath_subset_other_set[of "(to_dbltn ` insert e (t_set S))" 
                    u "map to_dbltn C" u "to_dbltn ` (t_set S)"] 
         by (simp add: image_mono subset_insert undirected_multigraph.decycle_multi_def)
       then show ?case 
         using assms(2)  case_assms(2) by(force simp add: undirected_multigraph.has_no_cycle_multi_def)
     qed
     obtain C1 C2 where C1C2:"C = C1@[e]@C2"
       by (metis append_Cons append_Nil e_in_C in_set_conv_decomp_first)
     hence epath_extended:"epath  (to_dbltn ` insert e (t_set S)) u (map to_dbltn (C1@[e]@C2@C1@[e]@C2@C1@[e]@C2)) u"
       using epath_append C_prop(1)[simplified C1C2] by fastforce
     have middle_three_rewrite:"xs@[x,y,z]@ys = (xs@[x])@[y]@(z#ys)" for x y z xs ys by auto
     have e_path_very_verbose: "epath (to_dbltn ` insert e (t_set S)) u
 (butlast (map to_dbltn (C1 @ [e] @ C2 @ C1)) @
  [last (map to_dbltn (C1 @ [e] @ C2 @ C1)), to_dbltn e, hd (map to_dbltn (C2 @ C1 @ [e] @ C2))] @
  tl (map to_dbltn (C2 @ C1 @ [e] @ C2))) u"
       using epath_extended
       apply(rule back_subst[of "\<lambda> p. epath _ _ p _ "])
       apply(subst middle_three_rewrite) 
       apply(subst append_butlast_last_id, simp)
       apply(subst hd_Cons_tl,simp)
       by auto
     have "\<exists>x y. to_dbltn e = {x, y} \<and>
      x \<noteq> y \<and>
      epath (to_dbltn ` insert e (t_set S)) u
       (butlast (map to_dbltn (C1 @ [e] @ C2 @ C1)) @ [last (map to_dbltn (C1 @ [e] @ C2 @ C1))]) x \<and>
      epath (to_dbltn ` insert e (t_set S)) y
       ([hd (map to_dbltn (C2 @ C1 @ [e] @ C2))] @ tl (map to_dbltn (C2 @ C1 @ [e] @ C2))) u \<and>
      x \<in> last (map to_dbltn (C1 @ [e] @ C2 @ C1)) \<inter> to_dbltn e \<and>
      y \<in> to_dbltn e \<inter> hd (map to_dbltn (C2 @ C1 @ [e] @ C2))"
       using epath_find_splitter_advanced[OF e_path_very_verbose] by simp
     then obtain x y where xy_prop:"to_dbltn e = {x, y}"
      "x \<noteq> y"
      "epath (to_dbltn ` insert e (t_set S)) u (map to_dbltn (C1 @ [e] @ C2 @ C1)) x"
      "epath (to_dbltn ` insert e (t_set S)) y (map to_dbltn (C2 @ C1 @ [e] @ C2)) u"
      "x \<in> last (map to_dbltn (C1 @ [e] @ C2 @ C1)) \<inter> to_dbltn e"
      "y \<in> to_dbltn e \<inter> hd (map to_dbltn (C2 @ C1 @ [e] @ C2))" 
       by(subst (asm) append_butlast_last_id, simp) force
     have C1C2_empt:"C2@C1 \<noteq> []" 
       using C1C2 C_prop(3) by force
     define d1 where "d1 = last (C1 @ [e] @ C2 @ C1)"
     have d1_def': "d1 = last (C2@C1)"
       using C1C2_empt d1_def by auto
     define d2 where "d2 = hd  (C2 @ C1 @ [e] @ C2)"
     have d2_def': "d2 = hd (C2@C1)" 
       using C1C2_empt  by(auto simp add: d2_def hd_append)
     have xy_prop':"x \<in> to_dbltn d1 \<inter> to_dbltn e"
                   "y \<in> to_dbltn e \<inter> to_dbltn d2" 
       using xy_prop(5,6)
       by(all \<open>subst (asm) last_map, simp\<close>, all \<open>subst (asm) hd_map, simp\<close>)
          (auto simp add: d2_def d1_def)
     have last_in:"d1 \<in> set C"
       using C1C2   by(subst d1_def, intro set_rev_mp[OF last_in_set,of _  "set C"]) auto
     have hd_in:"d2 \<in> set C"
       using C1C2   by(subst d2_def, intro set_rev_mp[OF hd_in_set,of _  "set C"]) auto
     have  d1_prop:"d1 \<in> set C" "to_dbltn e \<inter> to_dbltn d1 \<noteq> {}" 
       using last_in xy_prop(1,5) by(all \<open>subst (asm) last_map, simp\<close>)(auto simp add: d1_def)
     have  d2_prop:"d2 \<in> set C" "to_dbltn e \<inter> to_dbltn d2 \<noteq> {}" 
       using hd_in xy_prop(1,6) by(all \<open>subst (asm) hd_map, simp\<close>)(auto simp add: d2_def)
     have "d1 \<in> insert e (t_set S)" 
       using C_prop(2) last_in by blast
     moreover  have d1_not_e:"d1 \<noteq> e"
     proof(rule ccontr, goal_cases)
       case 1
       hence "e \<in> set (C2@C1)"
         using C1C2_empt d1_def' last_in_set by blast
       hence "\<not> distinct C"
         using C1C2 by fastforce
       then show ?case
         by (simp add: C_prop(4))
     qed
     ultimately have d1_in_S:"d1 \<in>  (t_set S)" 
       by simp
     have  "d2 \<in> insert e (t_set S)" 
       using C_prop(2) hd_in by blast
     moreover have d2_not_e:"d2 \<noteq> e"
     proof(rule ccontr, goal_cases)
       case 1
       hence "e \<in> set (C2@C1)"
         using C1C2_empt d2_def' hd_in_set by blast
       hence "\<not> distinct C"
         using C1C2 by fastforce
       then show ?case
         by (simp add: C_prop(4))
     qed
     ultimately have d2_in_S: "d2 \<in> (t_set S)" by simp

     have dir_ds_in:"(v1_of d1, v2_of d1) \<in> G.digraph_abs (local.Kruskal_E_to_G S)"
          "(v2_of d1, v1_of d1) \<in> G.digraph_abs (local.Kruskal_E_to_G S)"
          "(v1_of d2, v2_of d2) \<in> G.digraph_abs (local.Kruskal_E_to_G S)"
          "(v2_of d2, v1_of d2) \<in> G.digraph_abs (local.Kruskal_E_to_G S)"
       by (simp add: d1_in_S d2_in_S digraph_abs_is)+
     have graph_inv:"G.graph_inv (local.Kruskal_E_to_G S)" 
       using local.Kruskal_E_to_G_def pair_graph_u_invar by force
     have "lookup (local.Kruskal_E_to_G S) (v1_of e) \<noteq> None" 
       using dir_ds_in  d1_prop(2) d2_prop(2) 2 d1_not_e d2_not_e  C1C2_empt  isin.simps(1)  xy_prop(1) xy_prop' 
       apply(cases "lookup (local.Kruskal_E_to_G S) (v1_of d1)")
       apply(all \<open>cases "lookup (local.Kruskal_E_to_G S) (v2_of d1)"\<close>)
       apply(all \<open>cases "lookup (local.Kruskal_E_to_G S) (v1_of d2)"\<close>)
       apply(all \<open>cases "lookup (local.Kruskal_E_to_G S) (v2_of d2)"\<close>)
       apply(simp add: doubleton_eq_iff  G.neighbourhood_def Pair_Graph_RBT.G.are_connected_abs[OF graph_inv, symmetric])+
       by metis
     moreover have "lookup (local.Kruskal_E_to_G S) (v2_of e) \<noteq> None"
       using dir_ds_in  d1_prop(2) d2_prop(2) 2 d1_not_e d2_not_e  C1C2_empt  isin.simps(1)  xy_prop(1) xy_prop' 
       apply(cases "lookup (local.Kruskal_E_to_G S) (v1_of d1)")
       apply(all \<open>cases "lookup (local.Kruskal_E_to_G S) (v2_of d1)"\<close>)
       apply(all \<open>cases "lookup (local.Kruskal_E_to_G S) (v1_of d2)"\<close>)
       apply(all \<open>cases "lookup (local.Kruskal_E_to_G S) (v2_of d2)"\<close>)
       apply(simp add: doubleton_eq_iff  G.neighbourhood_def Pair_Graph_RBT.G.are_connected_abs[OF graph_inv, symmetric])+
       by metis+
     ultimately show ?case
       using "2" by auto
   qed
   thus ?case 
     using "2" by blast
 qed
qed
  show ?case 
    using second_eq dfs.Graph.vset.set.set_insert[OF assms(1)]
    by (cases "rbt_subseteq (vset_insert e S) input_G ", 
       unfold local_indep_oracle_def undirected_multigraph_spec.has_no_cycle_multi_def first_eq ) 
       auto
qed

context fixes c::"'e \<Rightarrow> rat" and  order::"'e list"
  assumes non_negative_c:"\<And> e. e \<in> t_set input_G \<Longrightarrow> c e \<ge> 0"
and order_is_G: "t_set input_G = set order"
and order_length_is_G_card: "distinct order"
begin

lemma best_in_greedy_axioms:"Best_In_Greedy.BestInGreedy_axioms vset_inv t_set set_of_sets_isin input_G
     (Kruskal_Greedy2.indep_graph_matroid v1_of v2_of input_G)"
    by(auto simp add:  Matroid_Specs_Inst.invar_def local.indep_graph_matroid_def set_of_sets_isin_def
      Best_In_Greedy.BestInGreedy_axioms_def[OF Kruskal_Greedy2.Kruskal_Greedy.Best_In_Greedy_axioms] G_good Kruskal_Greedy2.indep_graph_matroid_def Matroid_Specs_Inst.indep_def
      Matroid_Specs_Inst.finite_setsI)

lemma sort_desc_axioms: "Best_In_Greedy.sort_desc_axioms Kruskal_Greedy.carrier_sorted"
  by (simp add: Kruskal_Greedy.sort_desc_axioms_def insort_key_desc_stable
 length_insort_key_desc set_insort_key_desc sorted_desc_f_insort_key_desc)

lemma indep_system_axioms:"Matroid_Specs_Inst.indep_system_axioms input_G
             (Kruskal_Greedy2.indep_graph_matroid v1_of v2_of input_G)"
  unfolding  Matroid_Specs_Inst.indep_system_axioms_def
proof(rule conjI[OF _ conjI], goal_cases)
  case 1
  then show ?case 
  by(simp add: rbt_subseteq_correct[OF _ G_good, symmetric]
           Matroid_Specs_Inst.indep_def Kruskal_Greedy2.indep_graph_matroid_def
             indep_graph_matroid_def undirected_multigraph.has_no_cycle_multi_def
             set_of_sets_isin_def) 
next
  case 2
  show ?case
    using undirected_multigraph.empty_has_no_cycle_multi_indep 
    by(auto intro!: exI[of _ Leaf] 
         simp add: Kruskal_Greedy.wrapper_axioms(5) Matroid_Specs_Inst.indep_def 
                   Kruskal_Greedy2.indep_graph_matroid_def indep_graph_matroid_def set_of_sets_isin_def
                    local.undirected_multigraph.empty_has_no_cycle_multi_indep)
next
  case 3
  show ?case
    unfolding Matroid_Specs_Inst.indep_def Kruskal_Greedy2.indep_graph_matroid_def indep_graph_matroid_def
              set_of_sets_isin_def
  proof(rule+, goal_cases)
    case (1 X Y)
    show ?case 
      using 1(1,2,4) Custom_Set_RBT.set_subseteq 
      by (auto intro:  undirected_multigraph.has_no_cycle_multi_indep_subset[OF 1(3)])
  qed
qed

lemma nonnegative:" Kruskal_Greedy.nonnegative input_G c"
  by(auto simp add: Kruskal_Greedy.nonnegative_def Pair_Graph_RBT.set.set_isin G_good  non_negative_c )

lemma size_G_length_order:"size input_G = length order"
  by(simp add:  G_good  Kruskal_Greedy2.rbt_size_correct distinct_card order_is_G order_length_is_G_card)

lemma valid_order: "Kruskal_Greedy.valid_order input_G order"
  by(simp add: Kruskal_Greedy.valid_order_def Pair_Graph_RBT.set.set_isin G_good  non_negative_c 
                  size_G_length_order order_is_G)

lemma kruskal_impl_corespondence: 
  "to_ordinary (kruskal' v1_of v2_of input_G (kruskal_init' c order)) =
  kruskal v1_of v2_of input_G (kruskal_init c order)"
proof(rule Kruskal_Greedy.BestInGreedy'_corresp, goal_cases)
  case (1 S x)
  then show ?case 
    by(unfold Kruskal_Greedy2.local_indep_oracle_def, intro local_indep_oracle_correct) auto
next
  case 2
  then show ?case 
    by (simp add: G_good)
next
  case 3
  then show ?case
    by (simp add: best_in_greedy_axioms) 
next
  case 4
  then show ?case 
    by (simp add: sort_desc_axioms)
next
  case 5
  then show ?case
    by (simp add: indep_system_axioms)
next
  case 6
  then show ?case
    by (simp add: nonnegative)
next
  case 7
  then show ?case
    by (simp add: valid_order)
qed

lemma indep_finite: "undirected_multigraph_spec.has_no_cycle_multi to_dbltn (t_set input_G) X \<Longrightarrow> finite X"
  using Spanning_Trees.undirected_multigraph.graph_indep_system_multi indep_system.indep_finite
 undirected_multigraph.undirected_multigraph_axioms by fast

lemma idnep_in_G:"undirected_multigraph_spec.has_no_cycle_multi to_dbltn (t_set input_G) X \<Longrightarrow>
           x \<in> X \<Longrightarrow> x \<in> t_set input_G"
  using local.undirected_multigraph.has_no_cycle_multi_indep_subset_carrier by auto

lemma indep_system_order:"indep_system (set order) (undirected_multigraph_spec.has_no_cycle_multi to_dbltn (set order))"
  using local.undirected_multigraph.graph_indep_system_multi[of input_G] order_is_G by auto

interpretation use_greedy_thms_kruskal:
Use_Greedy_Thms Leaf vset_insert vset_delete isin t_set vset_inv vset_union
                               vset_inter vset_diff rbt_subseteq  size set_of_sets_isin 
"undirected_multigraph_spec.has_no_cycle_multi (\<lambda> e. {v1_of e, v2_of e})(Tree2.set_tree input_G)"
input_G c order Kruskal_Greedy.carrier_sorted
  by(intro Use_Greedy_Thms.intro 
                      undirected_multigraph.graph_indep_system_multi indep_finite idnep_in_G)
    (auto intro!: Use_Greedy_Thms_axioms.intro
       simp add: Matroid_Specs_Inst.Matroid_Specs_axioms[simplified Matroid_Specs_def]
                       set_of_sets_isin_def' G_good non_negative_c order_is_G
                      indep_system_order indep_finite undirected_multigraph_spec.has_no_cycle_multi_def
                      order_length_is_G_card sort_desc_axioms)

lemma kruskal_returns_basis: "indep_system.basis (t_set input_G) 
(undirected_multigraph_spec.has_no_cycle_multi to_dbltn (t_set input_G))
 (t_set (result (kruskal v1_of v2_of input_G (kruskal_init c order))))"
  by(simp add:  kruskal_def Kruskal_Greedy2.indep_graph_matroid_def local.indep_graph_matroid_def 
                kruskal_init_def use_greedy_thms_kruskal.algo_gives_basis )

corollary kruskal_returns_spanning_forest: 
"undirected_multigraph_spec.is_spanning_forest_multi to_dbltn (t_set input_G)
 (t_set (result (kruskal v1_of v2_of input_G (kruskal_init c order))))"
  apply(subst undirected_multigraph.spanning_forest_iff_basis_multi)
  by(rule kruskal_returns_basis)

lemma rank_quotient_one: "indep_system.rank_quotient (t_set input_G)
    (undirected_multigraph_spec.has_no_cycle_multi to_dbltn (t_set input_G)) = 1"
  apply(subst Matroids_Theory.indep_system.matroid_iff_rq_eq_1[symmetric])
  by (auto simp add: use_greedy_thms_kruskal.indep_system 
                undirected_multigraph.graph_matroid_multi)

theorem kruskal_is_max:
"undirected_multigraph_spec.has_no_cycle_multi to_dbltn (t_set input_G) X \<Longrightarrow>
sum c X \<le> sum c (t_set (result (kruskal v1_of v2_of input_G (kruskal_init c order))))"
  unfolding kruskal_def kruskal_init_def Kruskal_Greedy2.indep_graph_matroid_def
            local.indep_graph_matroid_def
  apply(rule order.trans[rotated])
  apply(rule use_greedy_thms_kruskal.indep_predicate_greedy_correct[of X])
  by(simp add:  rank_quotient_one)+

definition "max_forest X =
 (undirected_multigraph_spec.is_spanning_forest_multi to_dbltn (t_set input_G) X
\<and> (\<forall> Y. undirected_multigraph_spec.is_spanning_forest_multi to_dbltn (t_set input_G) Y \<longrightarrow>
     sum c Y \<le> sum c X))"

corollary kruskal_computes_max_spanning_forest:
"max_forest(t_set (result (kruskal v1_of v2_of input_G (kruskal_init c order))))"
  using kruskal_is_max kruskal_returns_spanning_forest 
  by(auto simp add: max_forest_def undirected_multigraph.is_spanning_forest_multi_def)
end
end
end


definition "v1_of (e::(nat\<times>nat)) = min (fst e) (snd e)"
definition "v2_of e = (if fst e = snd e then fst e + 1 else  max (fst e) (snd e))"

interpretation kruskal_proof_maitroid_edges: Kruskal_Proof_Matroid_Edges v2_of G v1_of for G
proof(rule  Kruskal_Proof_Matroid_Edges.intro, unfold v1_of_def v2_of_def, goal_cases)
  case (1 e)
  then show ?case 
    by(cases "fst e = snd e") auto
qed


definition "edges = [(0::nat, 1::nat), (0, 2), (2, 3), (2,4), (2,1), (1,5), (5,8), (8,7), (7,1),
                     (7,2), (7,4), (4,3), (3,4), (3,3), (9, 8), (8, 1), (4,5), (5,10)]"

definition "G = foldr (\<lambda> x tree. vset_insert x  tree) edges empty"

definition "c_list = [((0::nat, 1::nat), 1::rat), ((0, 2), 0.5), ((2, 3), 5/8), ((2,4), 3), ((2,1), -1/3),
                      ((1,5), 4), ((5,8), 2), ((8,7), 0.1), ((7,1), 1.3),
                     ((7,2), 3), ((7,4), 3), ((4,3), 2), ((3,4), 1), ((3,3), 0), ((9, 8),2.5),
                      ((8, 1), 0), ((4,5), 2), ((5,10), 3)]"

definition "c_impl = foldr (\<lambda> xy tree. update (prod.fst xy) (prod.snd xy) tree) c_list Leaf"
value "c_impl"

definition "costs  e =  (case (lookup c_impl e) of Some c \<Rightarrow> c | None \<Rightarrow> 0)"

value "kruskal_init' costs edges"
value  "kruskal' v1_of v2_of G (kruskal_init' costs edges)"
value "inorder (result (kruskal' v1_of v2_of G (kruskal_init' costs edges)))"

thm kruskal_proof_maitroid_edges.kruskal_computes_max_spanning_forest
end