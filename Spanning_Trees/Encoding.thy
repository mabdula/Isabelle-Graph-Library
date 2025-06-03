theory Encoding
  imports Undirected_Set_Graphs.Pair_Graph_U_Specs Matroids_Greedy.Indep_System_Matroids_Specs
begin

locale Encoding =
  pair_graph_u: Pair_Graph_U_Specs where lookup = lookup +
  set2: Set2 where insert = set_insert  and isin = set_isin 
  and delete = set_delete and invar = set_inv and empty = set_empty
  and set = to_set
for lookup :: "'adjmap \<Rightarrow> ('v::linorder) \<Rightarrow> 'vset option"
  and set_insert :: "('e::linorder) \<Rightarrow> 's \<Rightarrow> 's"  and set_empty and set_delete 
  and set_isin and set_inv and to_set
  and adjmap_fold :: "'adjmap \<Rightarrow> ('v \<Rightarrow> 'vset \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> 's \<Rightarrow> 's" and
  vset_fold :: "'vset \<Rightarrow> ('v \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> 's \<Rightarrow> 's" 
  and set_fold_adjmap :: "'s \<Rightarrow> ('e \<Rightarrow> 'adjmap \<Rightarrow> 'adjmap) \<Rightarrow> 'adjmap \<Rightarrow> 'adjmap" and
  set_fold_vset :: "'s \<Rightarrow> ('e \<Rightarrow> 'vset \<Rightarrow> 'vset) \<Rightarrow> 'vset \<Rightarrow> 'vset" +
fixes v1_of :: "'e \<Rightarrow> 'v" and v2_of :: "'e \<Rightarrow> 'v" 
  and c :: "('v set) \<Rightarrow> rat" and c' :: "'e \<Rightarrow> rat"
begin

fun edges_to_graph :: "'s \<Rightarrow> 'adjmap" where
  "edges_to_graph E =
    set_fold_adjmap E
    (\<lambda>e G. pair_graph_u.add_u_edge G (v1_of e) (v2_of e))
    empty"

fun edges_to_vertices :: "'s \<Rightarrow> 'vset" where
  "edges_to_vertices E = 
    set_fold_vset E
    (\<lambda>e N. if isin N (v1_of e)
           then (if isin N (v2_of e) then N else insert (v2_of e) N)
           else (if isin N (v2_of e) then insert (v1_of e) N else insert (v1_of e) (insert (v2_of e) N)))
    vset_empty"
end

locale Encoding_Proofs =
  Encoding +
  assumes adjmap_fold: "\<And> G S f. adjmap_inv G \<Longrightarrow> \<exists> xs. distinct xs \<and> set xs = dom (lookup G) \<and>
                                 adjmap_fold G f S = foldr (\<lambda> x acc. f x (the (lookup G x)) acc) xs S "
    and set_fold_adjmap: "\<And> G S f.  set_inv S \<Longrightarrow> \<exists> xs. distinct xs \<and> set xs = to_set S \<and>
                                 set_fold_adjmap S f G = foldr f xs G"
    and vset_fold: "\<And> V f S. vset_inv V \<Longrightarrow> \<exists> xs. distinct xs \<and> set xs = t_set V \<and>
                                    vset_fold V f S = foldr f xs S"
    and set_fold_vset: "\<And>V f S. set_inv S \<Longrightarrow> \<exists> xs. distinct xs \<and> set xs = to_set S \<and>
                                 set_fold_vset S f V = foldr f xs V"
begin

lemma pair_graph_u_invar_empty: "pair_graph_u.pair_graph_u_invar \<emptyset>\<^sub>G" 
proof-
  have " pair_graph_u.graph_inv \<emptyset>\<^sub>G"
    by (simp add: pair_graph_u.pair_graph_specs.adjmap.invar_empty pair_graph_u.pair_graph_specs.adjmap.map_empty pair_graph_u.graph_inv_def)
  moreover have "pair_graph_u.finite_graph \<emptyset>\<^sub>G"
    by (simp add: pair_graph_u.pair_graph_specs.adjmap.map_empty pair_graph_u.finite_graph_def)
  ultimately show ?thesis
    by (unfold pair_graph_u.pair_graph_u_invar_def )
       (simp add: pair_graph_u.pair_graph_specs.adjmap.map_empty pair_graph_u.neighbourhood_def 
        pair_graph_u.pair_graph_specs.vset.set.invar_empty pair_graph_u.pair_graph_specs.vset.set.set_empty 
        pair_graph_u.pair_graph_specs.vset.set.set_isin pair_graph_u.pair_graph_specs.finite_vsets_empty)
  qed

lemma P_of_ifE: "P (if b then x else y) \<Longrightarrow> (b \<Longrightarrow> P x \<Longrightarrow> Q) \<Longrightarrow> (\<not>b \<Longrightarrow> P y \<Longrightarrow> Q) \<Longrightarrow> Q"
  by(cases b) auto

lemma edges_invar_imp_graph_invar:
  assumes "set_inv E" "\<And> e. e \<in> to_set E \<Longrightarrow> v1_of e \<noteq> v2_of e"
  shows "pair_graph_u.pair_graph_u_invar (edges_to_graph E)" (is ?thesis1)
    and "\<forall> v y. lookup (edges_to_graph E) v = Some y \<longrightarrow> y \<noteq> vset_empty" (is ?thesis2)
    and "\<forall> e \<in> pair_graph_u.digraph_abs (edges_to_graph E).
 lookup (edges_to_graph E) (fst e) \<noteq> None \<longleftrightarrow>  lookup (edges_to_graph E) (snd e) \<noteq> None" (is ?thesis3)
proof-
  define f where "f = (\<lambda>e G.(pair_graph_u.add_u_edge G (v1_of e) (v2_of e)))"
  obtain xs where xs_prop:"distinct xs" "set xs = to_set E" "set_fold_adjmap E f \<emptyset>\<^sub>G = foldr f xs \<emptyset>\<^sub>G"
    using set_fold_adjmap[OF assms(1), of f empty]  by(auto simp add: f_def)
  have inv_after_list:"pair_graph_u.pair_graph_u_invar (foldr f xs \<emptyset>\<^sub>G)" 
    if asm: "\<And> e. e \<in> set xs \<Longrightarrow> v1_of e \<noteq> v2_of e" for xs
    using asm 
    by(induction xs)
      (auto simp add: pair_graph_u_invar_empty  f_def
            pair_graph_u.pair_graph_u_invar_add_edge_both(1)
             pair_graph_u.pair_graph_u_invar_add_u_edge(1) )   
  then show ?thesis1
    using assms(2) f_def[symmetric]  xs_prop(2,3) by auto
  show ?thesis2
    using assms(2)
    unfolding edges_to_graph.simps f_def[symmetric]  xs_prop(3) xs_prop(2)[symmetric]
    apply(induction xs)
    apply (simp add: pair_graph_u.pair_graph_specs.adjmap.map_empty)
    apply(subst foldr.simps, subst o_apply, subst f_def)
    apply(rule pair_graph_u.pair_graph_u_invar_add_u_edge(2))
    using inv_after_list
    by (auto intro:  pair_graph_u.pair_graph_u_invar_add_edge_both(2))
  show ?thesis3
    using assms(2)
    unfolding edges_to_graph.simps f_def[symmetric]  xs_prop(3) xs_prop(2)[symmetric]
  proof(induction xs)
    case Nil
    then show ?case 
      by (simp add: pair_graph_u.pair_graph_specs.adjmap.map_empty)
  next
    case (Cons a xs)
    show ?case 
      apply(subst (1) foldr.simps, subst o_apply, subst (1) f_def)
      apply(subst (1) foldr.simps, subst o_apply, subst (2) f_def)
      apply(subst (1) foldr.simps, subst o_apply, subst (3) f_def)
    proof( rule ballI, goal_cases)
      case (1 e)
      have a1: "pair_graph_u.graph_inv (foldr f xs \<emptyset>\<^sub>G)"
        using Cons(2) by (simp add: inv_after_list)
      have "(lookup (foldr f xs \<emptyset>\<^sub>G) x \<noteq> None) = (lookup (foldr f xs \<emptyset>\<^sub>G) y \<noteq> None)" 
        if assms1: "(x, y)\<in>[foldr f xs \<emptyset>\<^sub>G]\<^sub>g" for x y       
        using pair_graph_u.pair_graph_specs.are_connected_absI[OF assms1 a1]  pair_graph_u.graph_abs_symmetric[OF inv_after_list assms1]
          pair_graph_u.pair_graph_specs.vset.emptyD(3) pair_graph_u.pair_graph_specs.adjmap.map_empty pair_graph_u.graph_irreflexive[OF  pair_graph_u_invar_empty]
         Cons (2)
       by (cases "lookup (foldr f xs \<emptyset>\<^sub>G) x", all \<open>cases "lookup (foldr f xs \<emptyset>\<^sub>G) y"\<close>)
          (auto split: option.split simp add:  pair_graph_u.digraph_abs_def pair_graph_u.neighbourhood_def)
      hence ih_prem1: "\<forall>x\<in>[foldr f xs \<emptyset>\<^sub>G]\<^sub>g.
       (lookup (foldr f xs \<emptyset>\<^sub>G) (fst x) \<noteq> None) = (lookup (foldr f xs \<emptyset>\<^sub>G) (snd x) \<noteq> None)" 
        by auto
      show ?case
        using ih_prem1 Cons(2)
        by(intro bspec[OF pair_graph_u.pair_graph_u_invar_add_u_edge(3)
              [simplified pair_graph_u.none_symmetry_def], of _ _ _ "(fst e, snd e)", simplified fst_conv snd_conv]
            ) (auto simp add: inv_after_list "1")
    qed
  qed
qed 

lemma digraph_abs_of_edges_of_to_graph:
  assumes ys_prop: "set ys = to_set E" "set_fold_adjmap E g \<emptyset>\<^sub>G = foldr g ys \<emptyset>\<^sub>G" and
    g_def: "g = (\<lambda>e G. pair_graph_u.add_u_edge G (v1_of e) (v2_of e))" 
  shows  "[edges_to_graph E]\<^sub>g = (\<lambda> e. (v1_of e, v2_of e)) ` (to_set E) \<union> (\<lambda> e. (v2_of e, v1_of e)) ` (to_set E)"
proof-
  have graph_inv_fold_g:"pair_graph_u.graph_inv (foldr g ys \<emptyset>\<^sub>G)" for ys
   by(induction ys) 
     (auto intro: simp add: g_def pair_graph_u.pair_graph_specs.adjmap_inv_insert
        pair_graph_u.pair_graph_specs.graph_inv_empty pair_graph_u.add_u_edge_def)
  show ?thesis
    unfolding edges_to_graph.simps g_def[symmetric] ys_prop(2) ys_prop(1)[symmetric]
  proof(induction ys)
    case Nil
    then show ?case by(simp add: pair_graph_u.pair_graph_specs.digraph_abs_empty)
  next
    case (Cons a ys)   
    then show ?case 
      apply simp (*add_u_edge is unfolded to double add_edge because the theorems are simpler.*)
      apply(subst g_def, subst pair_graph_u.add_u_edge_def)
      apply(subst pair_graph_u.digraph_abs_insert[OF pair_graph_u_invar_empty])
      apply(rule pair_graph_u.adjmap_inv_insert[OF pair_graph_u_invar_empty])
      apply(rule graph_inv_fold_g)
      apply(subst pair_graph_u.digraph_abs_insert[OF pair_graph_u_invar_empty])
      by(auto intro!: graph_inv_fold_g) 
  qed
qed

lemma digraph_abs_of_edges_of_to_graph_general:
  assumes "set_inv E"
  shows "[edges_to_graph E]\<^sub>g = (\<lambda> e. (v1_of e, v2_of e)) ` (to_set E) \<union> (\<lambda> e. (v2_of e, v1_of e)) ` (to_set E)"
proof-
  have set_inv_G:"set_inv E"
    using assms  by blast
  define g where "g = (\<lambda>e G. pair_graph_u.add_u_edge G (v1_of e) (v2_of e))"
  obtain xs where xs_prop:"distinct xs" "set xs = to_set E" 
    "set_fold_adjmap E g empty = foldr g xs empty"
    using set_fold_adjmap[OF  set_inv_G, of g empty] by blast 
  show ?thesis
    by(rule digraph_abs_of_edges_of_to_graph[OF xs_prop(2,3) g_def])
qed 

find_theorems edges_to_graph

abbreviation "to_doubltn_set X \<equiv> (\<lambda>e. {v1_of e, v2_of e}) ` to_set X"

lemma dbltn_set_and_ugraph_abs:
  assumes "set_inv X"
  shows "to_doubltn_set X = pair_graph_u.ugraph_abs (edges_to_graph X)"
proof-
  define g where "g =  (\<lambda>e G. (pair_graph_u.add_u_edge G (v1_of e) (v2_of e)))" 
  obtain xs where xs_prop:" distinct xs" "set xs = to_set X" "set_fold_adjmap X g \<emptyset>\<^sub>G = foldr g xs \<emptyset>\<^sub>G"
    using set_fold_adjmap[OF assms(1), of g empty] by auto
  have X_vs_are:"[edges_to_graph X]\<^sub>g = (\<lambda>e. (v1_of e, v2_of e)) ` to_set X \<union> (\<lambda>e. (v2_of e, v1_of e)) ` to_set X"
    using  digraph_abs_of_edges_of_to_graph[OF xs_prop(2,3) g_def] by simp
  show ?thesis
    by(unfold pair_graph_u.ugraph_and_digraph_abs X_vs_are) auto
qed

end
end
