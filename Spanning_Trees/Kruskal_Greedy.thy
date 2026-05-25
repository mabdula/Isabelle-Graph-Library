theory Kruskal_Greedy
  imports Matroids_Greedy.Best_In_Greedy Spanning_Trees Encoding
    Graph_Algorithms_Dev.DFS_Example Insertion_Sort_Desc "HOL-Library.Product_Lexorder"
    Graph_Algorithms_Dev.RBT_Map_Extension
    Undirected_Set_Graphs.Directed_Undirected
begin

section \<open>Kruskal's Algorithm for Maximum Spanning Forest\<close>

text \<open>Since the set of spanning trees is a matroid,
we can use the Best-In-Greedy Algorithm to find a maximum weight solution.
This is also known as Kruskal's Algorithm.\<close>

(*TODO?
move lemmas on rbtsto RBT_Map_Extension?
*)

hide_const RBT_Set.insert
global_interpretation Pair_Graph_U_RBT: Pair_Graph_U_Specs
  where empty = empty and update = update and delete = delete and
    lookup = lookup and adjmap_inv = "M.invar" and vset_empty = "\<langle>\<rangle>" and
    insert = vset_insert and vset_delete = vset_delete and vset_inv = "vset_inv::(('v::linorder) rbt \<Rightarrow> bool)" and
    isin = isin and t_set = "Tree2.set_tree" and sel = sel
  defines add_edge =Pair_Graph_U_RBT.add_edge
    and  add_u_edge =Pair_Graph_U_RBT.add_u_edge
  by(simp add: Pair_Graph_U_Specs_def Pair_Graph_Specs_def M.Map_axioms S_C.Set_Choose_axioms)

text \<open>Instantiations for Greedy\<close>

lemma tree_split_case:
  "(case t of Leaf \<Rightarrow> True | _ \<Rightarrow> False) = (t = Leaf)"
  by (fastforce split: tree.splits) 

lemmas rbt_size_correct = rbt_size_correct[simplified
    vset_inv_def[simplified t_inv_def[symmetric], symmetric]]
lemmas rbt_nonempty_repr = rbt_nonempty_repr[simplified
    vset_inv_def[simplified t_inv_def[symmetric], symmetric]]
lemmas rbt_set_fold_correct = rbt_set_fold_correct[simplified
    vset_inv_def[simplified t_inv_def[symmetric], symmetric]]

global_interpretation Card_Set2_RBT: Card_Set2
  where empty = "\<langle>\<rangle>" and insert = insert_rbt and delete = delete_rbt and invar = "vset_inv::(('e::linorder) rbt \<Rightarrow> bool)" and
    isin = isin and set = "Tree2.set_tree" and union = "RBT.union" and inter = "RBT.inter" and diff = "RBT.diff" and
    cardinality = size
  defines subseteq = Card_Set2_RBT.subseteq
  apply (subst Card_Set2_def)
  apply(intro conjI)
  subgoal
    using RBT.Set2_axioms
    by (metis RBT_Set.empty_def dfs.set_ops.Set2_axioms)
  subgoal
    apply (subst Card_Set2_axioms_def)
    using rbt_nonempty_repr rbt_size_correct by blast
  done

interpretation Matroid_Specs_Inst: Matroid_Specs
  where set_empty = "\<langle>\<rangle>" and set_insert = insert_rbt and set_delete = delete_rbt and set_inv = "vset_inv::(('e::linorder) rbt \<Rightarrow> bool)" and
    set_isin = isin and to_set = "Tree2.set_tree" and union = "RBT.union" and inter = "RBT.inter" and diff = "RBT.diff" and
    cardinality = size 
  apply (subst Matroid_Specs_def)
  apply (subst Indep_System_Specs_def)
  using Card_Set2_RBT.Card_Set2_axioms by blast
                                                   
global_interpretation Kruskal_Graphs_Matroids: Encoding
  where empty = RBT_Set.empty and update = update and delete = RBT_Map.delete and
    lookup = lookup and adjmap_inv = "M.invar" and vset_empty = "\<langle>\<rangle>" and
    insert = insert_rbt and vset_delete = delete_rbt and vset_inv = "vset_inv::(('v::linorder) rbt \<Rightarrow> bool)" and
    isin = isin and t_set = "Tree2.set_tree" and sel = sel and
    set_empty = "\<langle>\<rangle>" and set_insert = insert_rbt and set_delete = delete_rbt and set_inv = "vset_inv::(('e::linorder) rbt \<Rightarrow> bool)" and
    set_isin = isin and to_set = "Tree2.set_tree" and union = "RBT.union" and inter = "RBT.inter" and diff = "RBT.diff" and
    adjmap_fold = "rbt_map_fold" and vset_fold = "rbt_set_fold" and set_fold_adjmap = "rbt_set_fold" and
    set_fold_vset = "rbt_set_fold"
  for v1_of :: "('e::linorder) \<Rightarrow> ('v::linorder)" and v2_of :: "('e::linorder) \<Rightarrow> ('v::linorder)" 
    and c :: "('v set) \<Rightarrow> rat" and c' :: "'e \<Rightarrow> rat"
  defines edges_to_graph = Kruskal_Graphs_Matroids.edges_to_graph
    and edges_to_vertices = Kruskal_Graphs_Matroids.edges_to_vertices
  by (auto intro: Encoding.intro simp add: Card_Set2_RBT.Set2_axioms Pair_Graph_U_RBT.Pair_Graph_U_Specs_axioms)

locale Oracle =
  fixes  input_G :: "('v::linorder \<times> 'v) rbt"
begin

definition Kruskal_E_to_G :: "('v \<times> 'v) rbt \<Rightarrow> ('v \<times> ('v rbt)) rbt" where
  "Kruskal_E_to_G = edges_to_graph fst snd"

definition Kruskal_E_to_V :: "('v \<times> 'v) rbt  \<Rightarrow> ('v rbt)" where
  "Kruskal_E_to_V = edges_to_vertices fst snd"

definition indep_graph_matroid :: "('v \<times> 'v) rbt  \<Rightarrow> bool" where
  "indep_graph_matroid = (\<lambda> E. graph_abs.has_no_cycle 
           ((\<lambda> e. {fst e, snd e}) ` (Tree2.set_tree input_G)) 
           ((\<lambda> e. {fst e, snd e}) ` (Tree2.set_tree E)) \<and> set_tree E \<subseteq> set_tree input_G)"

definition "local_indep_oracle e X = 
((Card_Set2_RBT.subseteq (vset_insert e X) input_G) \<and>
 (lookup (Kruskal_E_to_G X) (fst e) \<noteq> None \<and> lookup (Kruskal_E_to_G X) (snd e) \<noteq> None\<longrightarrow>
            return (dfs_impl (Kruskal_E_to_G X) (snd e) (dfs_initial_state (fst e))) 
                    = NotReachable))"

end

global_interpretation orcl: Oracle
  where  input_G = input_G
  for  input_G
  defines Kruskal_E_to_G=orcl.Kruskal_E_to_G
    and Kruskal_E_to_V=orcl.Kruskal_E_to_V
    and indep_graph_matroid=orcl.indep_graph_matroid
    and local_indep_oracle= orcl.local_indep_oracle
  done

global_interpretation Kruskal_Greedy: Best_In_Greedy'
  where set_empty = "\<langle>\<rangle>" and set_insert = insert_rbt and set_delete = delete_rbt 
    and set_inv = "vset_inv::(('v::linorder \<times> 'v) rbt \<Rightarrow> bool)" and
    set_isin = isin and to_set = "Tree2.set_tree" and union = "RBT.union" and inter = "RBT.inter" and diff = "RBT.diff" and
    cardinality = size and
    carrier = input_G and 
    indep_fn = "indep_graph_matroid  input_G" and
    sort_desc = insort_key_desc and 
    local_indep_oracle = "local_indep_oracle  input_G"
    and wrapper_insert = insert_rbt
    and wrapper_invar = "vset_inv::(('v \<times> 'v) rbt \<Rightarrow> bool)"
    and remove_wrapper = id
    and wrapper_empty = Leaf
  for  input_G
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
  Oracle +
  assumes v1_never_v2:"\<And> e d. e \<in> t_set input_G \<Longrightarrow> d \<in> t_set input_G \<Longrightarrow> prod.swap e \<noteq> d"
begin

lemma Encoding_Proofs_axioms:
  " Encoding_Proofs_axioms t_set M.invar vset_inv lookup vset_inv t_set rbt_map_fold
     rbt_set_fold rbt_set_fold rbt_set_fold"
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
qed

interpretation Kruskal_Graphs_Matroids_proofs: Encoding_Proofs
  where empty = RBT_Set.empty and update = update and delete = RBT_Map.delete and
    lookup = lookup and adjmap_inv = "M.invar" and vset_empty = "\<langle>\<rangle>" and
    insert = insert_rbt and vset_delete = delete_rbt 
    and vset_inv = "vset_inv::(('v::linorder) rbt \<Rightarrow> bool)" and
    isin = isin and t_set = "Tree2.set_tree" and sel = sel and
    set_empty = "\<langle>\<rangle>" and set_insert = insert_rbt and set_delete = delete_rbt 
    and set_inv = "vset_inv::(('v::linorder \<times> 'v) rbt \<Rightarrow> bool)" and
    set_isin = isin and to_set = "Tree2.set_tree" and union = "RBT.union" and inter = "RBT.inter" and diff = "RBT.diff" and
    adjmap_fold = "rbt_map_fold" and vset_fold = "rbt_set_fold" and set_fold_adjmap = "rbt_set_fold" and
    set_fold_vset = "rbt_set_fold"
    and v1_of = fst and v2_of = snd
  for c :: "(('v::linorder) set) \<Rightarrow> rat" and c' :: "('v \<times> 'v) \<Rightarrow> rat"
  by(auto intro!: Encoding_Proofs.intro  Encoding_Proofs_axioms 
      simp add: Encoding_def 
      Pair_Graph_U_RBT.Pair_Graph_U_Specs_axioms Card_Set2_RBT.Set2_axioms)

lemma G_arefl: "e \<in> t_set input_G \<Longrightarrow> fst e \<noteq> snd e"
  using v1_never_v2[of "(snd e, fst e)" "(fst e, snd e)"]  surjective_pairing[of e] by force

lemma pair_graph_u_invar:
  "vset_inv S \<Longrightarrow> t_set S  \<subseteq> t_set input_G \<Longrightarrow> Pair_Graph_U_RBT.pair_graph_u_invar (Kruskal_E_to_G S)"
  using Kruskal_Graphs_Matroids_proofs.edges_invar_imp_graph_invar[OF _  G_arefl]
  by(fastforce simp add: edges_to_graph_def local.Kruskal_E_to_G_def)

lemma same_dgraphabs:"dfs.Graph.digraph_abs = G.digraph_abs"
  by (simp add: RBT_Set.empty_def)

lemmas set_of_pair_def'[simp] =  set_of_pair_def[unfolded case_prod_beta]

lemma graph_abs_input_G:   
  assumes  G_good: "vset_inv input_G"
  shows "graph_abs (set_of_pair ` t_set input_G)"
  by (simp add: G_arefl G_good Kruskal_Graphs_Matroids_proofs.dbltn_set_and_ugraph_abs
      Kruskal_Graphs_Matroids_proofs.edges_invar_imp_graph_invar(1)
      Pair_Graph_U_RBT.graph_abs_ugraph)

lemma to_dbltn_inj: "S \<subseteq> t_set input_G \<Longrightarrow> inj_on set_of_pair S" 
proof(rule inj_onI, goal_cases)
  case (1 x y)
  then show ?case 
    using v1_never_v2[of x y]
    by(fastforce simp add: doubleton_eq_iff prod.swap_def prod_eqI)
qed

lemma local_indep_oracle_correct:
  assumes "vset_inv S" "indep'  input_G (id S)" 
          "Card_Set2_RBT.subseteq (id S) input_G"  "e \<notin> t_set (id S)"
  and   G_good: "vset_inv input_G"
  shows "local_indep_oracle e S = indep' input_G (vset_insert e (id S))"
  apply(insert assms)
  unfolding indep'_def Kruskal_Greedy.indep_graph_matroid_def
    indep_graph_matroid_def
proof(goal_cases)
  case 1
  note case_assms = this
  have S_in_input_G: "t_set S \<subseteq> t_set input_G"
    using Card_Set2_RBT.set_subseteq G_good case_assms(1,3) by auto
  have first_eq:"Card_Set2_RBT.subseteq (vset_insert e S) input_G
                 = (t_set (vset_insert e (id S)) \<subseteq> t_set input_G)" 
    using G_good assms(1) dfs.Graph.vset.set.invar_insert Card_Set2_RBT.set_subseteq 
    by(unfold id_def) blast
  have second_eq:"(((lookup (local.Kruskal_E_to_G S) (snd e) \<noteq> None 
                     \<and> lookup (Kruskal_E_to_G S) (fst e) \<noteq> None) \<longrightarrow>
                 (return (dfs_impl (local.Kruskal_E_to_G S) (snd e) 
                 (dfs_initial_state (fst e))) = NotReachable))) =
                (\<nexists>u. Ex (decycle (set_of_pair ` (t_set (vset_insert e (id S)))) u))"
    if additional_assm: "insert e (t_set  S) \<subseteq> t_set input_G"
  proof-
    have digraph_abs_is:"G.digraph_abs (Kruskal_E_to_G S) =
      t_set S \<union> prod.swap ` t_set S"
      using Kruskal_Graphs_Matroids_proofs.digraph_abs_of_edges_of_to_graph_general[OF assms(1)]
      by(auto simp add:  Kruskal_E_to_G_def edges_to_graph_def prod.swap_def)     
    have ugraph_abs_is: "Pair_Graph_U_RBT.ugraph_abs (Kruskal_E_to_G S) = set_of_pair ` (t_set  S)"
      by(auto intro!: Kruskal_Graphs_Matroids_proofs.dbltn_set_and_ugraph_abs[symmetric]
          simp add: assms(1) Kruskal_E_to_G_def edges_to_graph_def )
    have pair_graph_u_invar:"Pair_Graph_U_RBT.pair_graph_u_invar (edges_to_graph  fst snd S)" 
      using local.Kruskal_E_to_G_def pair_graph_u_invar[OF  assms(1) S_in_input_G] by simp
    have double_ex_I: "rest x y \<Longrightarrow> \<exists>v1 v2.
       {x, y} = {v1, v2} \<and> rest v1 v2" for x y rest by auto
    have lookup_in_dVs:"lookup (local.Kruskal_E_to_G S) x = Some y\<Longrightarrow> 
          x \<in> dVs (dfs.Graph.digraph_abs (local.Kruskal_E_to_G S))" for x y
      using Kruskal_Graphs_Matroids_proofs.edges_invar_imp_graph_invar(2)[OF assms(1)]
        S_C.choose  G_arefl S_in_input_G
      by(unfold  dfs.Graph.digraph_abs_def DFS_Example.neighbourhood_def)
        (force simp add: Kruskal_E_to_G_def edges_to_graph_def
          neighbourhood_def[symmetric] dfs.Graph.neighbourhood_def dVs_def
          intro!: exI[of _ "{x, sel y}"]  double_ex_I)
    have "lookup (local.Kruskal_E_to_G S) (fst e) = Some y \<Longrightarrow>
         DFS.DFS_axioms isin t_set adj_inv vset_empty vset_inv lookup
          (local.Kruskal_E_to_G S) (fst e)" for y
      unfolding DFS.DFS_axioms_def[OF dfs.DFS_axioms]
      using   lookup_in_dVs pair_graph_u_invar
      by(unfold Pair_Graph_U_RBT.pair_graph_u_invar_def Kruskal_E_to_G_def adj_inv_def)
        simp
    hence DFS_thms: "lookup (local.Kruskal_E_to_G S) (fst e) \<noteq> None \<Longrightarrow>
        DFS_thms map_empty RBT_Map.delete vset_insert isin t_set sel update adj_inv vset_empty vset_delete vset_inv
     vset_union vset_inter vset_diff lookup (Kruskal_E_to_G S) (fst e)"
      by(auto intro!: DFS_thms.intro dfs.DFS_axioms DFS_thms_axioms.intro )
    have graph_abs_with_e: "graph_abs (set_of_pair ` insert e (t_set S))"
      using that  G_arefl
      by(fastforce intro!: graph_abs.intro 
          exI[of "\<lambda> u. \<exists> v. {fst e, snd e} = {u, v} \<and> u \<noteq> v" "fst e"] 
          exI[of "\<lambda> v. {fst e, snd e} = {fst e, v} \<and> fst e \<noteq> v" "snd e"]
          simp add: dblton_graph_def Vs_def)
    have graph_abs_without_e: "graph_abs (set_of_pair `(t_set S))"
      using graph_abs_mono graph_abs_with_e by auto
    have graph_abs_vset_insert:"graph_abs (set_of_pair` t_set (vset_insert e S))"
      using RBT.set_tree_insert[of S] case_assms(1) graph_abs_with_e 
      by(simp add:vset_inv_def)
    show ?thesis 
      unfolding dfs_impl_def dfs_initial_state_def
    proof(cases "lookup (local.Kruskal_E_to_G S) (fst e) \<noteq> None 
         \<and> lookup (local.Kruskal_E_to_G S) (snd e) \<noteq> None", goal_cases)
      case 1
      hence 1: "lookup (local.Kruskal_E_to_G S) (fst e) \<noteq> None" 
        "lookup (local.Kruskal_E_to_G S) (snd e) \<noteq> None" by auto
      note one = this
      show ?case
      proof(subst DFS_thms.DFS_impl_to_DFS[OF DFS_thms, OF 1(1)],
          rule, all \<open>rule ccontr\<close>, goal_cases)
        case 1
        then obtain u C where uC_prop:"decycle 
                 (set_of_pair ` (t_set (vset_insert e S))) u C" by auto
        moreover have  not_cycle_old:"\<not> decycle (set_of_pair `(t_set S)) u C" 
          using case_assms(2)  graph_abs.has_no_cycle_def[OF graph_abs_input_G ] G_good
          by simp
        ultimately have e_and_C:"set_of_pair e \<in> set C" "set C \<subseteq> set_of_pair ` (t_set (vset_insert e S))"      
          using case_assms(1) dfs.Graph.vset.set.set_insert[of S]
            new_edge_in_decycle not_cycle_old uC_prop epath_edges_subset  
          by (fastforce simp add:  decycle_def )+
        then obtain C1 C2 where C_split:"C = C1@[set_of_pair e]@C2"
          by (metis append_Cons append_self_conv2 split_list_last)
        obtain urC where urC_props: "map set_of_pair urC = C" "set urC \<subseteq> t_set (vset_insert e S)"
          using  get_urlist_to_dbltn[OF e_and_C(2)] by blast
        obtain q where q_prop:"walk_betw (set_of_pair ` (insert e (t_set S))) u q u"
          "C = edges_of_path q"
          using epath_imp_walk_betw[of _ u "C" u]  uC_prop 
          by(auto simp add: decycle_def  Pair_Graph_RBT.set.set_insert[OF case_assms(1)])
        hence e_in_p: "set_of_pair e \<in> set (edges_of_path q)"
          using e_and_C(1) by blast
        have lengthq: "length q \<ge> 2" 
          using \<open>set_of_pair e \<in> set (edges_of_path q)\<close> edges_of_path_nempty by fastforce
        have v1v2: "fst e \<noteq> snd e" 
          using G_arefl that by auto
        show ?case proof(cases "lookup (local.Kruskal_E_to_G S) (snd e)")
          case None
          thus ?thesis 
            by (simp add: one(2))
        next
          case (Some neighb)
          have no_distinct_path:"\<nexists>p. distinct p \<and>
              vwalk_bet (dfs.Graph.digraph_abs (local.Kruskal_E_to_G S)) (fst e) p (snd e)"
            using DFS_thms.DFS_correct_1[OF DFS_thms] Some  one 1 by blast
          have no_other_e:"(set_of_pair e) \<notin> (set_of_pair ` t_set S)"
          proof(rule ccontr, goal_cases)
            case 1
            then obtain d where d_prop:"set_of_pair d = set_of_pair e" "d \<in> t_set S" by auto
            hence "{(fst d, snd d), (snd d, fst d)} \<subseteq> 
                  (dfs.Graph.digraph_abs (local.Kruskal_E_to_G S))"
              by (simp add: RBT_Set.empty_def digraph_abs_is)
            moreover have "(fst e, snd e) = (fst d, snd d)\<or>(fst e, snd e) = (snd d, fst d)"
              using d_prop by(unfold set_of_pair_def' doubleton_eq_iff) presburger
            ultimately have "vwalk_bet (dfs.Graph.digraph_abs (Kruskal_E_to_G S)) 
                         (fst e) [fst e, snd e] (snd e)" 
              by fastforce
            moreover have "distinct [fst e, snd e]"
              using v1v2 by auto
            ultimately show ?case 
              using   no_distinct_path by blast
          qed 
          moreover have dbltn_inj:"inj_on set_of_pair (t_set S) "
            using S_in_input_G by (auto intro!: to_dbltn_inj[simplified])
          ultimately have dbltn_inj_big:"inj_on set_of_pair (insert e (t_set S))" by auto
          moreover have C_subset:"set urC \<subseteq> (insert e (t_set S))"
            using case_assms(1) dfs.Graph.vset.set.set_insert urC_props(2) by auto
          ultimately have inj_C:"inj_on set_of_pair (set urC)" 
            by (meson inj_on_subset)
          have distinct_edges_q:"distinct (edges_of_path q)"
            using q_prop(2) distinct_map[of set_of_pair urC] uC_prop e_and_C inj_C
            by(auto simp add: decycle_def) 
          have e_vs_in_new_v_set:"set_of_pair e \<subseteq> Vs (set_of_pair ` insert e (t_set S))"
            by (simp add: vs_member)
          then obtain q1 q2 where q1_q2_prop: 
            "q = q1@[fst e, snd e]@ q2 \<or> q = q1@[snd e, fst e]@ q2"
            using e_and_C(1) q_prop(2) xy_in_edges_of_path_split[of "fst e" "snd e" q] by auto
          obtain q' where  path_without_e:"walk_betw (set_of_pair `  (t_set S)) (fst e) q' (snd e)"
          proof(cases rule: disjE[OF q1_q2_prop], all "cases q1", all \<open>cases q2\<close>, goal_cases)
            case 1
            then show ?case 
              using q_prop(1) v1v2 walk_between_nonempty_pathD(3) walk_between_nonempty_pathD(4) by fastforce
          next
            case (2 a list)
            hence a1:"walk_betw (set_of_pair ` insert e (t_set S)) u (q1 @ [fst e]) (fst e)"
              using q_prop(1) by (intro walk_pref[of _ u q1 "fst e" "snd e # q2" u]) force
            moreover have a2:"walk_betw (set_of_pair ` insert e (t_set S)) (snd e) (snd e # q2) u"
              using q_prop(1) 2(2)  by(intro walk_suff[of _ u "q1@[fst e]" "snd e" q2 u]) force 
            ultimately have a3:"walk_betw (set_of_pair ` insert e (t_set S)) (snd e) ([snd e] @ q2) (fst e)"
              by (simp add: "2"(3) walk_betw_def)
            have a4:"set (edges_of_path ([snd e] @ q2)) \<subseteq> set (edges_of_path q)"
              using "2"(2) "2"(3) by auto
            moreover have a5:"set_of_pair e \<notin> set (edges_of_path ([snd e] @ q2))" 
              using "2"(2) "2"(3) distinct_edges_q by auto
            ultimately have a6:"set (edges_of_path ([snd e] @ q2)) \<subseteq> (set_of_pair `(t_set S))" 
              using a3 graph_abs.path_ball_edges' graph_abs_with_e walk_between_nonempty_pathD(1)by fast
            have "walk_betw (set_of_pair `(t_set S)) (snd e) ([snd e] @ q2) (fst e)"  
              using walk_betw_strengthen[OF a3 _ a6] 2(4) by simp
            hence "walk_betw (set_of_pair `(t_set S)) (fst e) (rev ([snd e] @ q2)) (snd e)" 
              by (meson walk_symmetric)
            thus ?case
              using 2(1) by simp         
          next
            case (3 a list)
            hence a1:"walk_betw (set_of_pair ` insert e (t_set S)) u (q1 @ [fst e]) (fst e)"
              using q_prop(1) by (intro walk_pref[of _ u q1 "fst e" "snd e # q2" u]) force
            moreover have a2:"walk_betw (set_of_pair ` insert e (t_set S)) (snd e) (snd e # q2) u"
              using q_prop(1) 3(2)  by(intro walk_suff[of _ u "q1@[fst e]" "snd e" q2 u]) force 
            ultimately have a3:"walk_betw (set_of_pair ` insert e (t_set S)) (snd e) (q1@ [fst e] ) (fst e)"
              by (simp add: "3"(4) walk_betw_def)
            have a4:"set (edges_of_path (q1@ [fst e])) \<subseteq> set (edges_of_path q)" 
              using 3(2-) edges_of_path_append_subset_2 by fastforce
            moreover have a5:"set_of_pair e \<notin> set (edges_of_path (q1@ [fst e]))" 
              using  distinct_edges_q by(unfold 3(2) edges_of_path_symmetric_split) simp
            ultimately have a6:"set (edges_of_path (q1@ [fst e])) \<subseteq> (set_of_pair `(t_set S))" 
              using a3 graph_abs.path_ball_edges' graph_abs_with_e walk_between_nonempty_pathD(1)by fast
            have "walk_betw (set_of_pair `(t_set S)) (snd e) (q1@ [fst e]) (fst e)"  
              using walk_betw_strengthen[OF a3 _ a6] 3(3) by simp
            hence "walk_betw (set_of_pair `(t_set S)) (fst e) (rev (q1@ [fst e])) (snd e)" 
              by (meson walk_symmetric)
            thus ?case
              using 3(1) by simp 
          next
            case (4 a list aa lista)
            hence a1:"walk_betw (set_of_pair ` insert e (t_set S)) u (q1 @ [fst e]) (fst e)"
              using q_prop(1) by (intro walk_pref[of _ u q1 "fst e" "snd e # q2" u]) force
            moreover have a2:"walk_betw (set_of_pair ` insert e (t_set S)) (snd e) (snd e # q2) u"
              using q_prop(1) 4(2)  by(intro walk_suff[of _ u "q1@[fst e]" "snd e" q2 u]) force     
            have a4:"set (edges_of_path (q1@ [fst e])) \<subseteq> set (edges_of_path q)" 
              using 4(2-) edges_of_path_append_subset_2 by fastforce
            moreover have a5:"set_of_pair e \<notin> set (edges_of_path (q1@ [fst e]))" 
              using  distinct_edges_q by(unfold 4(2) edges_of_path_symmetric_split) simp
            ultimately have a6:"set (edges_of_path (q1@ [fst e])) \<subseteq> (set_of_pair `(t_set S))" 
              using graph_abs.path_ball_edges' graph_abs_with_e walk_between_nonempty_pathD(1) by fast
            have a4:"set (edges_of_path ([snd e] @ q2)) \<subseteq> set (edges_of_path q)"
              using "4"(2) edges_of_path_append_subset by fastforce
            moreover have a5:"set_of_pair e \<notin> set (edges_of_path ([snd e] @ q2))" 
              using  "4"(4) distinct_edges_q by(unfold 4(2) edges_of_path_symmetric_split) simp 
            moreover have a3:"walk_betw (set_of_pair ` insert e (t_set S)) (snd e) ([snd e] @ q2) u"
              using a2 a1 by simp 
            ultimately have a7:"set (edges_of_path ([snd e] @ q2)) \<subseteq> (set_of_pair `(t_set S))"
              using  a1 a2 graph_abs.path_ball_edges' graph_abs_with_e walk_between_nonempty_pathD(1) by fast 
            have "walk_betw (set_of_pair `(t_set S)) u (q1@ [fst e]) (fst e)"  
              using walk_betw_strengthen 4(3) a1 a6 by fastforce
            moreover have "walk_betw (set_of_pair `(t_set S)) (snd e) ( [snd e]@q2)u"  
              using walk_betw_strengthen[OF a3] 4(3)  "4"(4) a7 by fastforce
            ultimately have  "walk_betw (set_of_pair `(t_set S)) (snd e) ( ([snd e]@q2@(tl q1)@[fst e])) (fst e)" 
              using "4"(3) walk_transitive_2 by fastforce
            then show ?case 
              using 4(1)[of "rev ([snd e]@q2@(tl q1)@[fst e])"]
              by (meson walk_symmetric)
          next
            case 5
            then show ?case 
              using q_prop(1) v1v2 walk_between_nonempty_pathD(3) walk_between_nonempty_pathD(4) by fastforce
          next
            case (6 a list)
            hence a1:"walk_betw (set_of_pair ` insert e (t_set S)) u (q1 @ [snd e]) (snd e)"
              using q_prop(1) by (intro walk_pref[of _ u q1 "snd e" "fst e # q2" u]) force
            moreover have a2:"walk_betw (set_of_pair ` insert e (t_set S)) (fst e) (fst e # q2) u"
              using q_prop(1) 6(2)  by(intro walk_suff[of _ u "q1@[snd e]" "fst e" q2 u]) force 
            ultimately have a3:"walk_betw (set_of_pair ` insert e (t_set S)) (fst e) ([fst e] @ q2) (snd e)"
              by (simp add: "6"(3) walk_betw_def)
            have a4:"set (edges_of_path ([fst e] @ q2)) \<subseteq> set (edges_of_path q)"
              using "6"(2) "6"(3) by auto
            moreover have a5:"set_of_pair e \<notin> set (edges_of_path ([fst e] @ q2))" 
              using "6"(2) "6"(3) distinct_edges_q 
              by (simp add: insert_commute)
            ultimately have a6:"set (edges_of_path ([fst e] @ q2)) \<subseteq> (set_of_pair `(t_set S))" 
              using a3 graph_abs.path_ball_edges' graph_abs_with_e walk_between_nonempty_pathD(1) by fast
            have "walk_betw (set_of_pair `(t_set S)) (fst e) ([fst e] @ q2) (snd e)"  
              using walk_betw_strengthen[OF a3 _ a6] 6(4) by simp
            thus ?case
              using 6(1) by simp         
          next
            case (7 a list)
            hence a1:"walk_betw (set_of_pair ` insert e (t_set S)) u (q1 @ [snd e]) (snd e)"
              using q_prop(1) by (intro walk_pref[of _ u q1 "snd e" "fst e # q2" u]) force
            moreover have a2:"walk_betw (set_of_pair ` insert e (t_set S)) (fst e) (fst e # q2) u"
              using q_prop(1) 7(2)  by(intro walk_suff[of _ u "q1@[snd e]" "fst e" q2 u]) force 
            ultimately have a3:"walk_betw (set_of_pair ` insert e (t_set S)) (fst e) (q1@ [snd e] ) (snd e)"
              by (simp add: "7"(4) walk_betw_def)
            have a4:"set (edges_of_path (q1@ [snd e])) \<subseteq> set (edges_of_path q)" 
              using 7(2-) edges_of_path_append_subset_2 by fastforce
            moreover have a5:"set_of_pair e \<notin> set (edges_of_path (q1@ [snd e]))" 
              using  distinct_edges_q using 7(2) 
              by (simp add: "7"(4) edges_of_path_snoc_2 insert_commute)
            ultimately have a6:"set (edges_of_path (q1@ [snd e])) \<subseteq> (set_of_pair `(t_set S))" 
              using a3 graph_abs.path_ball_edges' graph_abs_with_e walk_between_nonempty_pathD(1) by fast
            have "walk_betw (set_of_pair `(t_set S)) (fst e) (q1@ [snd e]) (snd e)"  
              using walk_betw_strengthen[OF a3 _ a6] 7(3) by simp
            thus ?case
              using 7(1) by simp 
          next
            case (8 a list aa lista)
            hence a1:"walk_betw (set_of_pair ` insert e (t_set S)) u (q1 @ [snd e]) (snd e)"
              using q_prop(1) by (intro walk_pref[of _ u q1 "snd e" "fst e # q2" u]) force
            moreover have a2:"walk_betw (set_of_pair ` insert e (t_set S)) (fst e) (fst e # q2) u"
              using q_prop(1) 8(2)  by(intro walk_suff[of _ u "q1@[snd e]" "fst e" q2 u]) force     
            have a4:"set (edges_of_path (q1@ [snd e])) \<subseteq> set (edges_of_path q)" 
              using 8(2-) edges_of_path_append_subset_2 by fastforce
            moreover have a5:"set_of_pair e \<notin> set (edges_of_path (q1@ [snd e]))" 
              using  distinct_edges_q 8(2) edges_of_path_symmetric_split[of q1 "snd e" "fst e" q2]
              by (simp add: insert_commute)
            ultimately have a6:"set (edges_of_path (q1@ [snd e])) \<subseteq> (set_of_pair `(t_set S))" 
              using graph_abs.path_ball_edges' graph_abs_with_e walk_between_nonempty_pathD(1) by fast
            have a4:"set (edges_of_path ([fst e] @ q2)) \<subseteq> set (edges_of_path q)"
              using 8(2) edges_of_path_append_subset by fastforce
            moreover have a5:"set_of_pair e \<notin> set (edges_of_path ([fst e] @ q2))" 
              using 8(4) distinct_edges_q 8(2) edges_of_path_symmetric_split[of q1 "snd e" "fst e" q2] 
              by (simp add: insert_commute)
            moreover have a3:"walk_betw (set_of_pair ` insert e (t_set S)) (fst e) ([fst e] @ q2) u"
              using a2 a1 by simp 
            ultimately have a7:"set (edges_of_path ([fst e] @ q2)) \<subseteq> (set_of_pair `(t_set S))"
              using  a1 a2 graph_abs.path_ball_edges' graph_abs_with_e walk_between_nonempty_pathD(1) by fast 
            have "walk_betw (set_of_pair `(t_set S)) u (q1@ [snd e]) (snd e)"  
              using walk_betw_strengthen 8(3) a1 a6 by fastforce
            moreover have "walk_betw (set_of_pair `(t_set S)) (fst e) ( [fst e]@q2)u"  
              using walk_betw_strengthen[OF  a3] 8(3)  8(4) a7 by simp
            ultimately have  "walk_betw (set_of_pair `(t_set S)) (fst e) ( ([fst e]@q2@(tl q1)@[snd e])) (snd e)" 
              using 8(3) walk_transitive_2 by fastforce
            then show ?case using 8(1) by auto
          qed
          have  dfs_vwalk:"vwalk_bet (dfs.Graph.digraph_abs (local.Kruskal_E_to_G S)) (fst e) q' (snd e)"
            apply(subst same_dgraphabs, subst Pair_Graph_U_RBT.ugraph_abs_digraph_abs[symmetric])
            using local.Kruskal_E_to_G_def pair_graph_u_invar 
              graph_abs.walk_betw_iff_vwalk_bet[OF graph_abs_without_e]  path_without_e 
            by (simp  add: ugraph_abs_is )+
          obtain q'' where "vwalk_bet (dfs.Graph.digraph_abs (local.Kruskal_E_to_G S)) (fst e) q'' (snd e)"
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
        proof(cases "lookup (local.Kruskal_E_to_G S) (snd e)")
          case None 
          hence "lookup (local.Kruskal_E_to_G S) (fst e) = None" 
            using two(2) by blast
          thus False 
            by (simp add: one)
        next
          case (Some neighbs)
          hence dfs_reachable:"return
         (dfs.DFS (local.Kruskal_E_to_G S) (snd e) (DFS.initial_state vset_insert vset_empty (fst e))) =
             Reachable" 
            using two(2) return.exhaust by auto
          then obtain p where p_vwalk:"vwalk_bet (dfs.Graph.digraph_abs (local.Kruskal_E_to_G S)) (fst e)
                                      p (snd e)"
            using DFS_thms.DFS_correct_2[OF DFS_thms[OF one(1)]] dfs_reachable by auto
          have walk_betw_around_e:"walk_betw (set_of_pair ` t_set S) (fst e) p (snd e)"
            apply(subst  ugraph_abs_is[symmetric], subst graph_abs.walk_betw_iff_vwalk_bet,
                simp add: graph_abs_without_e ugraph_abs_is)
            using  pair_graph_u_invar  p_vwalk graph_abs_without_e
            by(auto simp add: Pair_Graph_U_RBT.ugraph_abs_digraph_abs same_dgraphabs Kruskal_E_to_G_def)
            have "epath (set_of_pair ` t_set S) (fst e) (edges_of_path p) (snd e)"
              using walk_betw_around_e graph_abs_without_e 
              by(auto elim:  graph_abs.dblton_E intro!: walk_betw_imp_epath)
          moreover then obtain p' where p'_prop:"map set_of_pair p' = edges_of_path p" "set p' \<subseteq>  (t_set S)"
            using epath_edges_subset get_urlist_to_dbltn by force
          ultimately have epath_first_path:"epath (set_of_pair `  (t_set S)) (fst e) (map set_of_pair p') (snd e)"  
            by simp
          then obtain p'' where p''_prop:"epath (set_of_pair ` t_set S) (fst e) p'' (snd e)" 
            "set p'' \<subseteq> set (map set_of_pair p')" "distinct p''"
            using  epath_distinct_epath by fast
          obtain p_mul where p_mul: "map set_of_pair p_mul = p''" "set p_mul \<subseteq> set p'"
            using get_urlist_to_dbltn p''_prop(2) by force
          hence epath_p_mul:"epath (set_of_pair ` t_set S) (fst e) (map set_of_pair p_mul) (snd e)"
            using p''_prop(1) by blast
          hence epath_first_path:"epath (set_of_pair ` (insert e (t_set S))) (fst e) (map set_of_pair p_mul) (snd e)"  
            by (auto intro: epath_subset image_mono subset_insertI)
          moreover have "epath (set_of_pair ` (insert e (t_set S))) (snd e) [set_of_pair e] (fst e)"      
            using  G_arefl[of e]  that by(auto intro!: epath_single) 
          ultimately have epath3:"epath (set_of_pair ` (insert e (t_set S))) (fst e) 
                              (map set_of_pair (p_mul@[e])) (fst e)" 
            by (auto intro: epath_append)
          moreover have "set (p_mul@[e]) \<subseteq> insert e (t_set S)" 
            using p'_prop(2) p_mul(2) by auto
          moreover have "2 < length (p_mul@[e])" 
          proof-
            have  "2 \<le> length (p_mul@[e])"
              using epath_non_empty[OF epath_p_mul, simplified length_map] G_arefl that by auto
            moreover have "2 = length (p_mul@[e]) \<Longrightarrow> False"
            proof(goal_cases)
              case 1
              then obtain d where p_mul_is:"p_mul= [d]"
                by(cases p_mul rule: vwalk_arcs.cases) auto
              have "snd d = snd e \<or> snd d = fst e"
                using epath3[simplified p_mul_is] by auto
              moreover have "fst d = snd e \<or> fst d = fst e"
                using epath3[simplified p_mul_is] by auto
              ultimately have "e = d \<or> e = prod.swap d \<or> e = prod.swap e \<or> d= prod.swap d" 
                using surjective_pairing[of e] surjective_pairing[of d] 
                by (fastforce simp add: prod.swap_def)
              thus False 
                using case_assms(4) p'_prop(2) p_mul(2)
                  p_mul_is that v1_never_v2[of e e] v1_never_v2[of d d] 
                  v1_never_v2[of d e] 
                by auto
            qed
            ultimately show ?thesis by fastforce
          qed
          moreover have " distinct (map (\<lambda>x. {fst x, snd x}) (p_mul @ [e]))"
          proof-
            have "distinct (p_mul@[e])"
            proof-
              have "distinct p_mul"
                using p_mul(1)  p''_prop(3) by (auto simp add: distinct_map)
              moreover have "set p_mul \<subseteq> t_set S" 
                using p'_prop(2) p_mul(2) by order
              ultimately show ?thesis using assms(4) by auto
            qed
            moreover have "inj_on set_of_pair (set (p_mul @ [e]))"
              using \<open>set (p_mul @ [e]) \<subseteq> insert e (t_set S)\<close> that to_dbltn_inj by blast
            ultimately show ?thesis
              by(simp add: distinct_map)
          qed
          ultimately have "decycle (set_of_pair ` (t_set (vset_insert e S))) (fst e) (map set_of_pair (p_mul@[e]))" 
            by(simp add: decycle_def dfs.Graph.vset.set.set_insert[OF case_assms(1)])
          thus ?thesis 
            using 2(1) by simp
        qed
      qed
    next
      case 2
      have "(\<nexists>u. Ex (decycle (set_of_pair ` (t_set (vset_insert e (id S)))) u))"
      proof(rule ccontr,goal_cases)
        case 1
        then obtain u C where uC:"decycle (set_of_pair ` (insert e (t_set S))) u C"
          using case_assms(1) dfs.Graph.vset.set.set_insert by fastforce
        hence C_prop: "epath (set_of_pair ` insert e (t_set S)) u ( C) u"
          " 2 \<le> length C" "distinct C"
          by(auto simp add: decycle_def) 
        obtain urC where urC: "set urC \<subseteq> insert e (t_set S)" "map set_of_pair urC = C"
          using  epath_edges_subset[OF C_prop(1)] get_urlist_to_dbltn by meson
        have e_in_C:"e \<in> set urC"
        proof(rule ccontr, goal_cases)
          case 1
          have "epath ((\<lambda>x. {fst x, snd x}) ` t_set S) u C u" 
            using "1" image_mono[OF urC(1), of set_of_pair]  urC(1,2) 
              image_mono[of "set urC" "t_set S"set_of_pair] image_set[of set_of_pair urC] 
            by (intro epath_subset_other_set[OF C_prop(1)])(auto simp add: list.set_map  subset_insert[OF 1, of "t_set S"])
          hence "decycle (set_of_pair ` (t_set S)) u C"
            using uC
            by (auto simp add: decycle_def)
          then show ?case 
            using case_assms(2)  graph_abs.has_no_cycle_def[OF graph_abs_input_G] G_good by simp
        qed
        obtain C1 C2 where C1C2:"urC = C1@[e]@C2"
          by (metis append_Cons append_Nil e_in_C in_set_conv_decomp_first)
        hence epath_extended:"epath  (set_of_pair ` insert e (t_set S)) u (map set_of_pair (C1@[e]@C2@C1@[e]@C2@C1@[e]@C2)) u"
          using epath_append C_prop(1)[simplified C1C2] urC by force
        have middle_three_rewrite:"xs@[x,y,z]@ys = (xs@[x])@[y]@(z#ys)" for x y z xs ys by auto
        have e_path_very_verbose: "epath (set_of_pair ` insert e (t_set S)) u
                    (butlast (map set_of_pair (C1 @ [e] @ C2 @ C1)) @
                    [last (map set_of_pair (C1 @ [e] @ C2 @ C1)), set_of_pair e, hd (map set_of_pair (C2 @ C1 @ [e] @ C2))] @
                    tl (map set_of_pair (C2 @ C1 @ [e] @ C2))) u"
          using epath_extended
          apply(rule back_subst[of "\<lambda> p. epath _ _ p _ "])
          apply(subst middle_three_rewrite) 
          apply(subst append_butlast_last_id, simp)
          apply(subst hd_Cons_tl,simp)
          by auto
       from epath_find_splitter_advanced[OF e_path_very_verbose] 
       obtain x y where xy_prop:"set_of_pair e = {x, y}"
          "x \<noteq> y"
          "epath (set_of_pair ` insert e (t_set S)) u (map set_of_pair (C1 @ [e] @ C2 @ C1)) x"
          "epath (set_of_pair ` insert e (t_set S)) y (map set_of_pair (C2 @ C1 @ [e] @ C2)) u"
          "x \<in> last (map set_of_pair (C1 @ [e] @ C2 @ C1)) \<inter> set_of_pair e"
          "y \<in> set_of_pair e \<inter> hd (map set_of_pair (C2 @ C1 @ [e] @ C2))" 
          by(subst (asm) append_butlast_last_id, simp) force
        have C1C2_empt:"C2@C1 \<noteq> []" 
          using C1C2 C_prop(2) urC(2) by auto
        define d1 where "d1 = last (C1 @ [e] @ C2 @ C1)"
        have d1_def': "d1 = last (C2@C1)"
          using C1C2_empt d1_def by auto
        define d2 where "d2 = hd  (C2 @ C1 @ [e] @ C2)"
        have d2_def': "d2 = hd (C2@C1)" 
          using C1C2_empt  by(auto simp add: d2_def hd_append)
        have xy_prop':"x \<in> set_of_pair d1 \<inter> set_of_pair e"
          "y \<in> set_of_pair e \<inter> set_of_pair d2" 
          using xy_prop(5,6)
          by(all \<open>subst (asm) last_map, simp\<close>, all \<open>subst (asm) hd_map, simp\<close>)
            (auto simp add: d2_def d1_def)
        have last_in:"d1 \<in> set urC"
          using C1C2   by(subst d1_def, intro set_rev_mp[OF last_in_set,of _  "set urC"]) auto
        have hd_in:"d2 \<in> set urC"
          using C1C2   by(subst d2_def, intro set_rev_mp[OF hd_in_set,of _  "set urC"]) auto
        have  d1_prop:"d1 \<in> set urC" "set_of_pair e \<inter> set_of_pair d1 \<noteq> {}" 
          using last_in xy_prop(1,5) by(all \<open>subst (asm) last_map, simp\<close>)(auto simp add: d1_def)
        have  d2_prop:"d2 \<in> set urC" "set_of_pair e \<inter> set_of_pair d2 \<noteq> {}" 
          using hd_in xy_prop(1,6) by(all \<open>subst (asm) hd_map, simp\<close>)(auto simp add: d2_def)
        have "d1 \<in> insert e (t_set S)" 
          using C_prop(3) last_in urC by blast
        moreover  have d1_not_e:"d1 \<noteq> e"
        proof(rule ccontr, goal_cases)
          case 1
          hence "e \<in> set (C2@C1)"
            using C1C2_empt d1_def' last_in_set by blast
          hence "\<not> distinct urC"
            using C1C2 by fastforce
          then show ?case 
            using C_prop(3) distinct_map urC(2) by auto
        qed
        ultimately have d1_in_S:"d1 \<in>  (t_set S)" 
          by simp
        have  "d2 \<in> insert e (t_set S)" 
          using C_prop(2) hd_in urC(1) by auto
        moreover have d2_not_e:"d2 \<noteq> e"
        proof(rule ccontr, goal_cases)
          case 1
          hence "e \<in> set (C2@C1)"
            using C1C2_empt d2_def' hd_in_set by blast
          hence "\<not> distinct C"
            using C1C2 urC by auto
          then show ?case
            by (simp add: C_prop(3))
        qed
        ultimately have d2_in_S: "d2 \<in> (t_set S)" by simp
        have dir_ds_in:"(fst d1, snd d1) \<in> G.digraph_abs (local.Kruskal_E_to_G S)"
          "(snd d1, fst d1) \<in> G.digraph_abs (local.Kruskal_E_to_G S)"
          "(fst d2, snd d2) \<in> G.digraph_abs (local.Kruskal_E_to_G S)"
          "(snd d2, fst d2) \<in> G.digraph_abs (local.Kruskal_E_to_G S)"
          by (simp add: d1_in_S d2_in_S digraph_abs_is)+
        have graph_inv:"G.graph_inv (local.Kruskal_E_to_G S)" 
          using local.Kruskal_E_to_G_def pair_graph_u_invar by force
        have fst_and_snd_same_none:
          "\<And> e. e \<in> Pair_Graph_U_RBT.digraph_abs (Kruskal_E_to_G S) \<Longrightarrow>
       (lookup (Kruskal_E_to_G S) (fst e) \<noteq> None) =
       (lookup (Kruskal_E_to_G S) (snd e) \<noteq> None)" 
          using  G_arefl
            Kruskal_Graphs_Matroids_proofs.edges_invar_imp_graph_invar(3)
            [simplified edges_to_graph_def[of fst snd, simplified atomize_eq, symmetric]]             
            S_in_input_G case_assms(1) by (unfold Kruskal_E_to_G_def) blast
        have "lookup (local.Kruskal_E_to_G S) (fst e) \<noteq> None" 
          using dir_ds_in  d1_prop(2) d2_prop(2) 2 d1_not_e d2_not_e  isin.simps(1)  xy_prop(1) xy_prop' 
          apply(cases "lookup (local.Kruskal_E_to_G S) (fst d1)")
          apply(all \<open>cases "lookup (local.Kruskal_E_to_G S) (snd d1)"\<close>)
          apply(all \<open>cases "lookup (local.Kruskal_E_to_G S) (fst d2)"\<close>)
          apply(all \<open>cases "lookup (local.Kruskal_E_to_G S) (snd d2)"\<close>)
          using fst_and_snd_same_none[of d1] fst_and_snd_same_none[of d2] 
          apply(all \<open>simp add: doubleton_eq_iff  G.neighbourhood_def
                Pair_Graph_RBT.G.are_connected_abs[OF graph_inv, symmetric]\<close>) 
          by metis
        moreover have "lookup (local.Kruskal_E_to_G S) (snd e) \<noteq> None"
          using dir_ds_in  d1_prop(2) d2_prop(2) 2 d1_not_e d2_not_e  C1C2_empt  isin.simps(1)  xy_prop(1) xy_prop' 
          apply(cases "lookup (local.Kruskal_E_to_G S) (fst d1)")
          apply(all \<open>cases "lookup (local.Kruskal_E_to_G S) (snd d1)"\<close>)
          apply(all \<open>cases "lookup (local.Kruskal_E_to_G S) (fst d2)"\<close>)
          apply(all \<open>cases "lookup (local.Kruskal_E_to_G S) (snd d2)"\<close>) 
          apply(all \<open>simp add: doubleton_eq_iff  G.neighbourhood_def 
                  Pair_Graph_RBT.G.are_connected_abs[OF graph_inv, symmetric]\<close>)+
          using fst_and_snd_same_none[of d1] fst_and_snd_same_none[of d2] 
          by metis+
        ultimately show ?case
          using "2" by auto
      qed
      thus ?case 
        using "2" by blast
    qed
  qed
  show ?case 
    using second_eq dfs.Graph.vset.set.set_insert[OF assms(1)] graph_abs.has_no_cycle_def[OF graph_abs_input_G]
    by (cases "Card_Set2_RBT.subseteq (vset_insert e S) input_G ",
        unfold local_indep_oracle_def  first_eq ) 
      (auto simp add: G_good)  
qed
end


locale Kruskal_Proof_Matroid_Edges' = 
Kruskal_Proof_Matroid_Edges where input_G = input_G
for input_G::"(('a::linorder \<times> 'a) \<times> color) tree"+
  fixes c::"('a \<times> 'a) \<Rightarrow> rat" and  order::"('a \<times> 'a ) list"
  assumes non_negative_c:"\<And> e. e \<in> t_set input_G \<Longrightarrow> c e \<ge> 0"
    and order_is_G: "t_set input_G = set order"
    and order_length_is_G_card: "distinct order"
    and G_good: "vset_inv input_G"
begin

lemma best_in_greedy_axioms:
  shows "Best_In_Greedy.BestInGreedy_axioms vset_inv t_set input_G
     (Kruskal_Greedy.indep_graph_matroid input_G)"
  by(auto simp add:  Matroid_Specs_Inst.invar_def local.indep_graph_matroid_def
      Best_In_Greedy.BestInGreedy_axioms_def[OF Kruskal_Greedy.Kruskal_Greedy.Best_In_Greedy_axioms] G_good Kruskal_Greedy.indep_graph_matroid_def
      Matroid_Specs_Inst.finite_setsI)

lemma sort_desc_axioms: "Best_In_Greedy.sort_desc_axioms Kruskal_Greedy.carrier_sorted"
  by (simp add: Kruskal_Greedy.sort_desc_axioms_def insort_key_desc_stable
      length_insort_key_desc set_insort_key_desc sorted_desc_f_insort_key_desc)

lemma indep_system_axioms: 
  shows "Matroid_Specs_Inst.indep_system_axioms input_G
             (Kruskal_Greedy.indep_graph_matroid input_G)"
  unfolding  Matroid_Specs_Inst.indep_system_axioms_def
proof(rule conjI[OF _ conjI], goal_cases)
  case 1
  then show ?case 
    by(simp add: Card_Set2_RBT.set_subseteq[OF _ G_good, symmetric]
        Kruskal_Greedy.indep_graph_matroid_def
        indep_graph_matroid_def) 
next
  case 2
  show ?case
    using graph_abs.has_no_cycle_indep_ex[OF graph_abs_input_G] graph_abs.has_no_cycle_indep_subset[OF graph_abs_input_G]
    by(auto intro!: exI[of _ Leaf] 
        simp add: Kruskal_Greedy.wrapper_axioms(5) 
        Kruskal_Greedy.indep_graph_matroid_def indep_graph_matroid_def G_good)
next
  case 3
  show ?case
    unfolding Kruskal_Greedy.indep_graph_matroid_def indep_graph_matroid_def
  proof((rule allI)+, (rule impI)+, goal_cases)
    case (1 X Y)
    have "graph_abs.has_no_cycle ((\<lambda>e. {fst e, snd e}) ` t_set input_G) ((\<lambda>e. {fst e, snd e}) ` t_set Y)"
      using 1(4,3) graph_abs.has_no_cycle_indep_subset[OF 
            graph_abs_input_G, of "(\<lambda>e. {fst e, snd e}) ` t_set X"]
      by(auto simp add: Card_Set2_RBT.set_subseteq [OF 1(2,1)] image_mono G_good)
    moreover have "t_set Y \<subseteq> t_set input_G"
      using "1"(1,2,3,4) Card_Set2_RBT.set_subseteq by blast
    ultimately show ?case by simp
  qed
qed

lemma nonnegative:
  shows " Kruskal_Greedy.nonnegative input_G c"
  by(auto simp add: Kruskal_Greedy.nonnegative_def Pair_Graph_RBT.set.set_isin G_good  non_negative_c )

lemma size_G_length_order:
  shows "size input_G = length order"
  by(simp add:  G_good  Kruskal_Greedy.rbt_size_correct distinct_card order_is_G order_length_is_G_card)

lemma valid_order: 
  shows "Kruskal_Greedy.valid_order input_G order"
  by(simp add: Kruskal_Greedy.valid_order_def Pair_Graph_RBT.set.set_isin G_good  non_negative_c 
      size_G_length_order order_is_G)

lemma kruskal_impl_corespondence:
  shows "to_ordinary (kruskal'  input_G (kruskal_init' c order)) =
  kruskal  input_G (kruskal_init c order)"
proof((subst kruskal_def, subst indep'_def[symmetric]), rule Kruskal_Greedy.BestInGreedy'_corresp, goal_cases)
  case (1 S x)
  then show ?case 
    by(unfold Kruskal_Greedy.local_indep_oracle_def, intro local_indep_oracle_correct)
      (auto simp add: subseteq_def G_good)
next
  case 2
  then show ?case 
    by (simp add: G_good)
next
  case 3
  then show ?case
    by (simp add: best_in_greedy_axioms indep'_def)
next
  case 4
  then show ?case 
    by (simp add: sort_desc_axioms)
next
  case 5
  then show ?case
    by (simp add: indep_system_axioms indep'_def)
next
  case 6
  then show ?case
    by (simp add: nonnegative)
next
  case 7
  then show ?case
    by (simp add: valid_order)
qed

lemma indep_finite: 
  "\<lbrakk>graph_abs.has_no_cycle (to_dbltn ` (t_set input_G)) (to_dbltn ` X);  X \<subseteq> t_set input_G \<rbrakk>
    \<Longrightarrow> finite X"
  using finite_subset graph_abs.has_no_cycle_def graph_abs_input_G 
  by fastforce

definition "has_no_cycle_in_graph E = 
(graph_abs.has_no_cycle (set_of_pair ` t_set input_G ) (set_of_pair ` E) \<and> E \<subseteq> t_set input_G)"

lemma indep_system_order:"indep_system (set order) has_no_cycle_in_graph"
  unfolding has_no_cycle_in_graph_def
proof(rule indep_system.intro, goal_cases)
  case 1
  then show ?case
    by simp
next
  case (2 X)
  then show ?case 
    using order_is_G by blast
next
  case 3
  then show ?case
    using graph_abs.has_no_cycle_indep_ex graph_abs.has_no_cycle_indep_subset graph_abs_input_G
      order_is_G by (force intro: exI[of _ "{}"] simp add: G_good)
next
  case (4 X Y)
  then show ?case 
    by(auto intro: graph_abs.has_no_cycle_indep_subset[OF graph_abs_input_G[OF G_good], simplified order_is_G set_of_pair_def']
        simp add: order_is_G )
qed

interpretation use_greedy_thms_kruskal:
  Use_Greedy_Thms Leaf vset_insert vset_delete isin t_set vset_inv vset_union
  vset_inter vset_diff  size  
  has_no_cycle_in_graph
  input_G c order Kruskal_Greedy.carrier_sorted
  by(intro Use_Greedy_Thms.intro graph_abs.has_no_cycle_indep_subset[OF graph_abs_input_G, simplified order_is_G] indep_finite)
    (auto intro!: Use_Greedy_Thms_axioms.intro
      simp add: Matroid_Specs_Inst.Matroid_Specs_axioms[simplified Matroid_Specs_def]
      G_good non_negative_c order_is_G
      indep_system_order indep_finite 
      order_length_is_G_card sort_desc_axioms has_no_cycle_in_graph_def)

lemma kruskal_returns_basis: "indep_system.basis (t_set input_G)  has_no_cycle_in_graph
 (t_set (result (kruskal input_G (kruskal_init c order))))"
  using order_is_G use_greedy_thms_kruskal.algo_gives_basis
  by(simp add:  kruskal_def Kruskal_Greedy.indep_graph_matroid_def local.indep_graph_matroid_def 
      kruskal_init_def has_no_cycle_in_graph_def)

corollary kruskal_returns_spanning_forest: 
  "graph_abs.is_spanning_forest (set_of_pair ` (t_set input_G)) 
   (set_of_pair ` (t_set (result (kruskal input_G (kruskal_init c order)))))"
proof(subst graph_abs.spanning_forest_iff_basis[OF graph_abs_input_G[OF G_good]],
    subst indep_system.basis_def, goal_cases)
  case 1
  then show ?case
    using graph_abs.graph_indep_system graph_abs_input_G by (auto simp add: G_good)
next
  case 2
  show ?case
  proof(rule, goal_cases)
    case 1
    then show ?case 
      using has_no_cycle_in_graph_def indep_system.basis_indep kruskal_returns_basis order_is_G
        use_greedy_thms_kruskal.indep_system by auto
  next
    case 2
    then show ?case 
    proof(rule, rule, goal_cases)
      case (1 e)
      then obtain edir where edir_props:"edir \<in> t_set input_G" "set_of_pair edir = e"
        "edir \<notin>  t_set (result (kruskal input_G (kruskal_init c order)))" by auto
      have "graph_abs.has_no_cycle ((\<lambda>e. {fst e, snd e}) ` t_set input_G)
      (set_of_pair` (Set.insert edir (t_set (result (kruskal input_G (kruskal_init c order))))))"
        using "1"(2) edir_props(2) by auto
      moreover have "(Set.insert edir (t_set (result (kruskal input_G (kruskal_init c order)))))
                     \<subseteq> t_set input_G"
        using edir_props(1) has_no_cycle_in_graph_def indep_system.basis_indep indep_system_order
          kruskal_returns_basis order_is_G by auto
      ultimately have "has_no_cycle_in_graph (Set.insert edir (t_set (result (kruskal input_G (kruskal_init c order)))))"
        by (simp add: has_no_cycle_in_graph_def order_is_G)
      moreover have "(Set.insert edir (t_set (result (kruskal input_G (kruskal_init c order))))) \<supset>
                      (t_set (result (kruskal input_G (kruskal_init c order))))"
        using edir_props(3) by blast
      thus ?case
        using calculation edir_props(1) indep_system.basis_def kruskal_returns_basis
          use_greedy_thms_kruskal.indep_system by auto
    qed
  qed
qed

lemma has_no_cycle_in_graph_defines_matroid: 
  "matroid (t_set input_G) has_no_cycle_in_graph"
proof(rule matroid.intro[OF  use_greedy_thms_kruskal.indep_system], rule matroid_axioms.intro, goal_cases)
  case (1 X Y)
  hence XY_in_G:"X \<subseteq> t_set input_G" "Y \<subseteq> t_set input_G" 
    using use_greedy_thms_kruskal.indep_in_input_G by auto
  then obtain e where e_prop:" e\<in> set_of_pair ` X - set_of_pair ` Y"
    "graph_abs.has_no_cycle ((\<lambda>x. {fst x, snd x}) ` t_set input_G)
                    (insert e ((\<lambda>x. {fst x, snd x}) ` ( Y)))"
    using  graph_abs.graph_matroid[OF graph_abs_input_G[OF G_good]] 1
    by(unfold has_no_cycle_in_graph_def matroid_def matroid_axioms_def set_of_pair_def'
        card_image[OF to_dbltn_inj, OF XY_in_G(1), symmetric]
        card_image[OF to_dbltn_inj, OF XY_in_G(2), symmetric]) blast
  then obtain ure where ure:"set_of_pair ure = e" "ure \<in> X - Y" by blast
  show ?case 
    using XY_in_G(1,2) e_prop(2) has_no_cycle_in_graph_def ure(1,2) by (auto intro: bexI[OF _ ure(2)])
qed


lemma rank_quotient_one: "indep_system.rank_quotient (t_set input_G)has_no_cycle_in_graph = 1"
  by(subst Matroids_Theory.indep_system.matroid_iff_rq_eq_1[symmetric])
    (auto simp add: use_greedy_thms_kruskal.indep_system 
      has_no_cycle_in_graph_defines_matroid )

theorem kruskal_is_max:
 "has_no_cycle_in_graph X \<Longrightarrow>
    sum c X \<le> sum c (t_set (result (kruskal  input_G (kruskal_init c order))))"
  unfolding kruskal_def kruskal_init_def Kruskal_Greedy.indep_graph_matroid_def indep_graph_matroid_def
  using use_greedy_thms_kruskal.indep_predicate_greedy_correct[of X]
  by(simp add:  rank_quotient_one  has_no_cycle_in_graph_def[simplified order_is_G[symmetric] set_of_pair_def', symmetric])+

definition "max_forest X =
 (graph_abs.is_spanning_forest (set_of_pair ` (t_set input_G)) (set_of_pair ` X) \<and> X \<subseteq> t_set input_G
\<and> (\<forall> Y. graph_abs.is_spanning_forest (set_of_pair ` (t_set input_G)) (set_of_pair ` Y) \<and> Y \<subseteq> t_set input_G \<longrightarrow>
     sum c Y \<le> sum c X))"

corollary kruskal_computes_max_spanning_forest:
  "max_forest (t_set (result (kruskal  input_G (kruskal_init c order))))"
  using kruskal_is_max kruskal_returns_spanning_forest   kruskal_returns_basis
        use_greedy_thms_kruskal.indep_system graph_abs.spanning_forest_alternative graph_abs_input_G
  by(force simp add: has_no_cycle_in_graph_def in_mono indep_system.basis_def G_good  max_forest_def)+

end

locale kruskal_correct =
  fixes G::"(('v::linorder \<times> 'v) \<times> color) tree"
  and c order
  assumes G_good:"\<And>e d. e \<in> t_set G \<Longrightarrow> d \<in> t_set G \<Longrightarrow> prod.swap e \<noteq> d"
                 "vset_inv G" "t_set G = set order" "distinct order"
and pos_c: "\<And>e. e \<in> t_set G \<Longrightarrow> (0::rat) \<le> c e"
begin

interpretation kruskal_proof_maitroid_edges: Kruskal_Proof_Matroid_Edges' G 
proof(rule  Kruskal_Proof_Matroid_Edges'.intro, 
all \<open>rule Kruskal_Proof_Matroid_Edges.intro | rule Kruskal_Proof_Matroid_Edges'_axioms.intro\<close>, goal_cases)
  case (1 e d)
  then show ?case 
    using G_good by simp
next
  case (2 e)
  then show ?case 
    by (simp add: pos_c)
next
  case 3
  then show ?case 
    by (simp add: G_good(3))
next
  case 4
  then show ?case
    by (simp add: G_good(4))
next
  case 5
  then show ?case
    by (simp add: G_good(2))
qed

lemmas kruskal_computes_max_spanning_forest = 
  kruskal_proof_maitroid_edges.kruskal_computes_max_spanning_forest
end

definition "edges = [(0::nat, 1::nat), (0, 2), (2, 3), (2,4), (2,1), (1,5), (5,8), (8,7), (7,1),
                     (7,2), (7,4), (4,3), (3,4), (3,3), (9, 8), (8, 1), (4,5), (5,10), (10,5), (10,1)]"

definition "G = foldr (\<lambda> x tree. vset_insert x  tree) edges empty"

definition "c_list = [((0::nat, 1::nat), 1::rat), ((0, 2), 0.5), ((2, 3), 5/8), ((2,4), 3), ((2,1), -1/3),
                      ((1,5), 4), ((5,8), 2), ((8,7), 0.1), ((7,1), 1.3),
                     ((7,2), 3), ((7,4), 3), ((4,3), 2), ((3,4), 1), ((3,3), 0), ((9, 8),2.5),
                      ((8, 1), 0), ((4,5), 2), ((5,10), 3), ((10,5), 30), ((10,1), 1000)]"

definition "c_impl = foldr (\<lambda> xy tree. update (prod.fst xy) (prod.snd xy) tree) c_list Leaf"
value "c_impl"

definition "costs  e =  (case (lookup c_impl e) of Some c \<Rightarrow> c | None \<Rightarrow> 0)"

value "kruskal_init' costs edges"
value  "kruskal' G (kruskal_init' costs edges)"
value "inorder (result (kruskal'  G (kruskal_init' costs edges)))"
end