theory Compute_Path
  imports "Graph_Algorithms.BFS_Example" "Graph_Algorithms.DFS_Example"
          "Graph_Algorithms.RBT_Map_Extension"
begin  

lemma G_and_dfs_graph: "G.digraph_abs = dfs.Graph.digraph_abs"
                       "G.graph_inv = dfs.Graph.graph_inv"
                       (*"G.finite_graph = dfs.Graph.finite_graph"*)
  apply (auto simp add: RBT_Set.empty_def G.digraph_abs_def dfs.Graph.digraph_abs_def 
            DFS_Example.neighbourhood_def adj_inv_def)
  done

locale Compute_Path =
  fixes carrier::"('a::linorder) set"
    and s::"'a::linorder"
    and t::"'a"
    and G::"(('a \<times> ('a \<times> color) tree) \<times> color) tree"
    and S::"('a \<times> color) tree"
    and T::"('a \<times> color) tree"
begin

definition "one_source = fold_rbt (\<lambda> ss GG. add_edge GG s ss) S G"

definition "G' = fold_rbt (\<lambda> tt GG. add_edge GG tt t) T one_source"

term bfs_initial_state

abbreviation "srcs \<equiv> (if S = vset_empty then vset_empty else vset_insert s vset_empty)"

definition "bfs_tree = parents (bfs_impl G' (bfs_initial_state srcs))"

definition "dfs_final = dfs_impl bfs_tree (\<lambda> w. w =t) (dfs_initial_state s)"

definition "find_path = (if S = empty then None 
                         else if return dfs_final = Reachable 
                                 then Some (tl (butlast (rev (stack (dfs_final))))) 
                         else None)"

context 
  assumes s_and_t: "s \<notin> carrier"  "t \<notin> carrier"  "s \<noteq> t"
begin

context
  assumes graph_inv: "dfs.Graph.graph_inv G"
   and    finite_graph: "dfs.Graph.finite_graph G"
   and  finite_vs: "dfs.Graph.finite_vsets (TYPE ('a))"
   and vset_inv_S:"vset_inv S"
   and vset_inv_T:"vset_inv T"
   and S_in_carrier:"t_set S \<subseteq> carrier"
   and T_in_carrier:"t_set T \<subseteq> carrier"
   and verts_in_carrier: "dVs (dfs.Graph.digraph_abs G) \<subseteq> carrier"
begin

lemma G'_properties:
      "dfs.Graph.graph_inv G'" "dfs.Graph.finite_graph G'"
      "dfs.Graph.digraph_abs G' = dfs.Graph.digraph_abs G 
                 \<union> {(s, ss) | ss. ss \<in> t_set S} \<union> {(tt, t) | tt. tt \<in> t_set T}"
      "G.digraph_abs G' = dfs.Graph.digraph_abs G'"
proof-
  obtain xs where xs_prop: "set xs = t_set S" 
      "fold_rbt (\<lambda>ss GG. add_edge GG s ss) S G = foldr (\<lambda>ss GG. add_edge GG s ss) xs G"
    using rbt_fold_spec[OF vset_inv_S, of "(\<lambda>ss GG. add_edge GG s ss)" G] by auto
  have graph_inv_S_added:"dfs.Graph.graph_inv (foldr (\<lambda>ss GG. add_edge GG s ss) xs G)" for xs
    by(induction xs) (auto simp add: graph_inv)
  moreover have finite_graph_S_added:"dfs.Graph.finite_graph (foldr (\<lambda>ss GG. add_edge GG s ss) xs G)" for xs
    by(induction xs) (auto simp add: finite_graph dfs.Graph.finite_graph_add_edge graph_inv_S_added)
  ultimately have graph_inv_one_source:"dfs.Graph.graph_inv one_source"
        and finite_graph_one_source: "dfs.Graph.finite_graph one_source"
    by(simp add: one_source_def  xs_prop(2))+
  obtain ys where ys_prop: "set ys = t_set T" 
      "fold_rbt (\<lambda>tt GG. add_edge GG tt t) T one_source = foldr (\<lambda>tt GG. add_edge GG tt t) ys one_source"
    using rbt_fold_spec[OF vset_inv_T, of "(\<lambda>tt GG. add_edge GG tt t)" one_source] by auto
  have graph_inv_T_added:"dfs.Graph.graph_inv (foldr (\<lambda>tt GG. add_edge GG tt t) ys one_source)" for ys
    by(induction ys) (auto simp add: graph_inv_one_source)
  show "dfs.Graph.graph_inv G'"
    using graph_inv_T_added one_source_def ys_prop(2) by (force simp add: G'_def one_source_def )
  have finite_graph_T_added:"dfs.Graph.finite_graph (foldr (\<lambda>tt GG. add_edge GG tt t) ys one_source)" for ys
    by(induction ys) (auto simp add: finite_graph_one_source dfs.Graph.finite_graph_add_edge graph_inv_T_added)
  thus "dfs.Graph.finite_graph G'"
    by (simp add: G'_def ys_prop(2))
  have " dfs.Graph.digraph_abs  (fold_rbt (\<lambda>ss GG. add_edge GG s ss) S G) =
    dfs.Graph.digraph_abs G \<union> {(s, ss) | ss. ss \<in> t_set S}"
    unfolding xs_prop(1)[symmetric] xs_prop(2)
    by(induction xs) (auto simp add: dfs.Graph.digraph_abs_insert[OF graph_inv_S_added])
  moreover have "dfs.Graph.digraph_abs (fold_rbt (\<lambda>tt GG. add_edge GG tt t) T one_source) =
    dfs.Graph.digraph_abs one_source \<union> {(tt, t) |tt. tt \<in> t_set T}"
    unfolding ys_prop(1)[symmetric] ys_prop(2)
    by(induction ys) (auto simp add: dfs.Graph.digraph_abs_insert[OF graph_inv_T_added])
  ultimately show "dfs.Graph.digraph_abs G' =
    dfs.Graph.digraph_abs G \<union> {(s, ss) |ss. ss \<in> t_set S} \<union> {(tt, t) |tt. tt \<in> t_set T}"
    by(simp add: G'_def one_source_def)
  show "G.digraph_abs G' = dfs.Graph.digraph_abs G'" 
    by (simp add: RBT_Set.empty_def G.digraph_abs_def dfs.Graph.digraph_abs_def 
            DFS_Example.neighbourhood_def)
qed

lemma new_path_old_path:
"vwalk_bet_single_vertex (dfs.Graph.digraph_abs G') s p t \<Longrightarrow>
(length p \<ge> 3 \<and> (\<exists> s' t'. 
vwalk_bet_single_vertex (dfs.Graph.digraph_abs G) s' (tl (butlast p)) t'
\<and> s' \<in> t_set S \<and> t' \<in> t_set T))"
proof(goal_cases)
  case 1
  note one = this
  then have "1 \<le> length p"
    using not_less_eq_eq by (auto simp add: vwalk_bet_single_vertex_def vwalk_bet_def)
  moreover have "length p \<noteq> 2"
  proof(rule ccontr, subst (asm) not_not, goal_cases)
    case 1
    hence "(s,t) \<in> (dfs.Graph.digraph_abs G')" 
      using one
      by(auto intro: vwalk_arcs.cases[of p] simp add: vwalk_bet_single_vertex_def vwalk_bet_def )
    then show ?case 
      using S_in_carrier T_in_carrier s_and_t verts_in_carrier
      by(auto simp add: G'_properties(3))
  qed
  moreover have "length p \<noteq> 1"
  proof(rule ccontr, subst (asm) not_not, goal_cases)
    case 1
    hence "s = t" 
      using one
      by(auto intro: vwalk_arcs.cases[of p] simp add: vwalk_bet_single_vertex_def vwalk_bet_def )
    then show ?case 
      using  s_and_t by simp
  qed
  ultimately have length_p:"3 \<le> length p"
    by auto
  moreover have "hd p = s" 
    using "1" vwalk_bet_single_vertex_def by fastforce
  moreover have "last p = t" 
    using "1" vwalk_bet_single_vertex_def by fastforce
  ultimately obtain q where p_split:"p = [s]@q@[t]"
    by (metis append_butlast_last_id append_eq_Cons_conv hd_Cons_tl hd_Nil_eq_last last.simps s_and_t(3))
  have q_length: "length q > 0"
    using \<open>length p \<noteq> 2\<close> p_split by fastforce
  hence "vwalk_bet (dfs.Graph.digraph_abs G') s p t"
    using one s_and_t(3) vwalk_bet_single_vertex_def by fastforce
  hence "vwalk_bet (dfs.Graph.digraph_abs G') s ([s]@q) (last q)" 
    using p_split q_length vwalk_bet_prefix_is_vwalk_bet by fastforce
  hence vwalk_q_G':"vwalk_bet (dfs.Graph.digraph_abs G') (hd q) (q) (last q)"
    using q_length vwalk_bet_cons by fastforce
 moreover hence p_edges_in: "set (edges_of_vwalk q) \<subseteq> (dfs.Graph.digraph_abs G') " 
    by (simp add: vwalk_bet_edges_in_edges)
  moreover have "set (edges_of_vwalk q) \<inter> {(s, ss) |ss. ss \<in> t_set S} = {}"
  proof(rule ccontr, goal_cases)
    case 1
    hence "s \<in> set q" 
      using v_in_edge_in_vwalk(1) by fastforce
    then obtain q1 q2 where q_split: "q = q1 @[s]@q2" 
      by (metis append_Cons append_Nil in_set_conv_decomp_first)
    hence "(last ([s]@q1),s) \<in> dfs.Graph.digraph_abs G'" 
      using \<open>vwalk_bet (dfs.Graph.digraph_abs G') s p t\<close> 
           p_split vwalk_append_edge vwalk_bet_def vwalk_q_G' by fastforce
    hence "(last ([s]@q1),s) \<in> (dfs.Graph.digraph_abs G)" 
      using s_and_t S_in_carrier T_in_carrier by(auto simp add: G'_properties(3))
    hence "s \<in> dVs (dfs.Graph.digraph_abs G)"
      by blast
    then show ?case 
      using s_and_t(1) verts_in_carrier by auto
  qed
  moreover have "set (edges_of_vwalk q) \<inter> {(tt, t) |tt. tt \<in> t_set T} = {}"
  proof(rule ccontr, goal_cases)
    case 1
    hence "t \<in> set q" 
      using v_in_edge_in_vwalk(2) by fastforce
    then obtain q1 q2 where q_split: "q = q1 @[t]@q2" 
      by (metis append_Cons append_Nil in_set_conv_decomp_first)
    have "(last ([s]@q1@[t]),hd(q2@[t])) \<in> dfs.Graph.digraph_abs G'"
      using \<open>vwalk_bet (dfs.Graph.digraph_abs G') s p t\<close>  p_split vwalk_append_edge vwalk_bet_def vwalk_q_G' q_split 
      by (intro vwalk_append_edge)auto
    hence "(t,hd(q2@[t])) \<in> (dfs.Graph.digraph_abs G)" 
      using s_and_t S_in_carrier T_in_carrier by(auto simp add: G'_properties(3))
    hence "t \<in> dVs (dfs.Graph.digraph_abs G)"
      by blast
    then show ?case 
      using s_and_t(2) verts_in_carrier by auto
  qed
  ultimately have edges_of_q_in_G:"set (edges_of_vwalk q) \<subseteq> (dfs.Graph.digraph_abs G)"
    by (simp add: G'_properties(3) Int_Un_distrib le_iff_inf)
  moreover have "length q \<ge> 2 \<Longrightarrow>vwalk_bet (set (edges_of_vwalk q)) (hd q) q (last q)"
    by(auto intro: vwalk_bet_in_its_own_edges[OF vwalk_q_G'])
  ultimately have "length q \<ge> 2 \<Longrightarrow> vwalk_bet (dfs.Graph.digraph_abs G )(hd q) (q) (last q)"
    by (meson vwalk_bet_subset)
  moreover have "hd q \<in> t_set S"
  proof-
    have "(s,  hd (q @ [t])) \<in> dfs.Graph.digraph_abs G'"
      using \<open>vwalk_bet (dfs.Graph.digraph_abs G') s p t\<close> p_split 
      by (auto intro: vwalk_append_edge[of _ "[s]" "q@[t]", simplified])
    then show "hd q \<in> t_set S" 
      using s_and_t(1) S_in_carrier verts_in_carrier q_length T_in_carrier
      by(auto simp add: G'_properties(3))
  qed
  moreover have "last q \<in> t_set T"
  proof-
    have "(last ([s]@q), t) \<in> dfs.Graph.digraph_abs G'"
      using \<open>vwalk_bet (dfs.Graph.digraph_abs G') s p t\<close> p_split 
            vwalk_append_edge[of "dfs.Graph.digraph_abs G'" "[s]@q" "[t]"]
      by (simp add: vwalk_bet_nonempty_vwalk(1))
    then show "last q \<in> t_set T" 
      using s_and_t(2) S_in_carrier verts_in_carrier q_length T_in_carrier
      by(auto simp add: G'_properties(3))
  qed
  ultimately have "(vwalk_bet_single_vertex (dfs.Graph.digraph_abs G) (hd q) (tl (butlast p)) (last q) \<and>
        (hd q) \<in> t_set S \<and> (last q) \<in> t_set T)"
       using length_p p_split vwalk_q_G' neq_Nil_conv 
    by(auto simp add: vwalk_bet_single_vertex_def G'_properties(3) Suc_1[symmetric] Suc_le_length_iff
         , auto?)    
  then show ?case 
    using length_p by auto     
qed
  
lemma old_path_new_path:
  assumes "((\<exists> s' t'. vwalk_bet_single_vertex (dfs.Graph.digraph_abs G) s' p t'
             \<and> s' \<in> t_set S \<and> t' \<in> t_set T))"
  shows   "vwalk_bet_single_vertex (dfs.Graph.digraph_abs G') s ([s]@p@[t]) t"
proof-
  obtain s' t' where props:"vwalk_bet_single_vertex (dfs.Graph.digraph_abs G) s' p t'"
             "s' \<in> t_set S" "t' \<in> t_set T"
    using assms by auto
  hence "vwalk_bet_single_vertex (dfs.Graph.digraph_abs G') s' p t'" 
    unfolding G'_properties(3) 
    by(auto intro: vwalk_bet_single_vertex_subset simp add: G'_properties(3) )
  moreover have "(s,s') \<in> dfs.Graph.digraph_abs G'"
    using props(2,3) by(simp add: G'_properties(3))
  moreover have "(t', t) \<in> dfs.Graph.digraph_abs G'"
    using props(2,3) by(simp add: G'_properties(3))
  ultimately show ?thesis 
    by (fastforce intro: vwalk_bet_single_vertex_append vwalk_bet_single_vertex_single)
qed

lemma empty_set_iff:"(X \<noteq> vset_empty) = (t_set X \<noteq> {})"
  by (simp add: RBT_Set.empty_def)

lemma non_emptyE: "X \<noteq> {} \<Longrightarrow> (\<And> x. x \<in> X \<Longrightarrow> P) \<Longrightarrow>P"
  by auto

lemma bfs_axiom:" BFS.BFS_axiom isin t_set M.invar \<langle>\<rangle> vset_inv lookup srcs G'"
proof(cases "S \<noteq> vset_empty")
  case True
  show ?thesis 
  apply(insert True G'_properties(1,2) dVsI(1)[of s _ "{(s, ss) |ss. ss \<in> t_set S}"] finite_vs)
  apply(unfold bfs.BFS_axiom_def G_and_dfs_graph G'_properties(3))
    by(auto simp add: dfs.Graph.vset.set.set_insert[OF dfs.Graph.vset.set.invar_empty]
               dfs.Graph.vset.emptyD(1) split: if_split,
       rule non_emptyE[of "t_set S" _], 
       auto intro:  rev_finite_subset[OF  dfs.Graph.finite_vertices] 
         simp add: G'_properties(3) finite_vs dfs.Graph.vset.set.invar_empty  empty_set_iff
                   dfs.Graph.finite_vsets_def dfs.Graph.neighbourhood_abs[OF  graph_inv, symmetric])
next
  case False
  show ?thesis
    apply(simp, insert False G'_properties(1,2) dVsI(1)[of s _ "{(s, ss) |ss. ss \<in> t_set S}"] finite_vs)
    apply(unfold bfs.BFS_axiom_def G_and_dfs_graph G'_properties(3))
    using  infinite_super dfs.Graph.vset.set.set_empty  vset_inv_S
    by auto
qed
    
  
lemma bfs_dom: " bfs.BFS_dom G' (bfs_initial_state srcs)"
  using bfs.initial_state_props(4)[OF bfs_axiom] by blast

lemma bfs_impl_is: "bfs_impl G' (bfs_initial_state srcs) = 
                    bfs.BFS G' (bfs_initial_state srcs)"
  by(auto simp add: bfs.BFS_impl_same bfs.initial_state_props(4) bfs_axiom)

lemma bfs_invar_1: " bfs.invar_1 (bfs.BFS G' (bfs_initial_state srcs))"
  using bfs_axiom  by(auto intro: bfs.invar_1_holds bfs_axiom bfs_dom)

lemma bfs_invar_2: "bfs.invar_2 srcs G' 
      (bfs.BFS G' (bfs_initial_state srcs))"
 using bfs_axiom  by(auto intro!: bfs.invar_2_holds bfs_axiom bfs_dom)

lemma graph_inv_bfs_tree: "dfs.Graph.graph_inv bfs_tree"
  using bfs_invar_1 
  by(simp add:  adj_inv_def bfs.invar_1_def bfs_impl_is bfs_invar_1 bfs_tree_def)

lemma finite_graph_bfs_tree: "dfs.Graph.finite_graph bfs_tree"
  using bfs_invar_1 
  by(simp add:  adj_inv_def bfs.invar_1_def bfs_impl_is bfs_invar_1 bfs_tree_def)

interpretation dfs_lemmas: DFS_thms  where insert = vset_insert and
 sel = sel and  vset_empty = vset_empty and  diff = vset_diff and
 lookup = lookup and empty = map_empty and delete=delete and isin = isin and t_set=t_set
and update=update and adjmap_inv = adj_inv and vset_delete= vset_delete
and vset_inv = vset_inv and union=vset_union and inter=vset_inter and G= bfs_tree
and P_T = "\<lambda> w. w = t"
  by(auto intro!: DFS_thms.intro DFS_thms_axioms.intro 
           simp add: dfs.DFS_axioms DFS.DFS_axioms_def[OF  dfs.DFS_axioms] G'_properties finite_vs
                     graph_inv_bfs_tree finite_graph_bfs_tree)

lemma  find_path1: "find_path  = None \<longleftrightarrow> 
                             (\<nexists> p u v. vwalk_bet_single_vertex (dfs.Graph.digraph_abs G) u p v \<and>
                                       u \<in> t_set S \<and> v \<in> t_set T)"
proof-
  have find_path_means:"find_path  = None \<longleftrightarrow> (return dfs_final \<noteq> Reachable \<or> S = vset_empty)"
    by(simp add: find_path_def)
  show ?thesis
    unfolding find_path_def
proof(rule, goal_cases)
  case 1
  hence disjunction:"(return dfs_final \<noteq> Reachable \<and> S \<noteq> vset_empty) \<or> S = vset_empty"
    using find_path_means by auto
  show ?case 
  proof(cases rule: disjE[OF disjunction])
    case 1
    hence one: "return dfs_final \<noteq> Reachable" "S \<noteq> vset_empty" by simp+
    hence "return (DFS.DFS vset_insert sel vset_empty vset_diff lookup bfs_tree (\<lambda> w. w = t)
     (DFS.initial_state vset_insert vset_empty s)) \<noteq> Reachable"
      by (simp add: dfs_final_def dfs_impl_def dfs_initial_state_def dfs_lemmas.DFS_to_DFS_impl
              DFS_thms.DFS_to_DFS_impl[OF dfs_lemmas.DFS_thms_axioms] )
    hence "\<nexists>p. distinct p \<and> vwalk_bet (dfs.Graph.digraph_abs bfs_tree) s p t"
      using dfs_lemmas.DFS_correct_1 by(auto intro: return.exhaust)
    hence "\<nexists>p. vwalk_bet (dfs.Graph.digraph_abs bfs_tree) s p t"
      using   vwalk_bet_to_distinct_is_distinct_vwalk_bet by(fastforce simp add: distinct_vwalk_bet_def)
    hence no_parent_path:"\<nexists>p. vwalk_bet (G.digraph_abs bfs_tree) s p t"
      by (simp add: G_and_dfs_graph(1))
    have "\<nexists>p. vwalk_bet (G.digraph_abs G') s p t"
    proof(insert no_parent_path, unfold bfs_tree_def bfs_impl_def,
      subst (asm) BFS.BFS_impl_same[OF bfs.BFS_axioms bfs_dom],
      rule ccontr, rule exE, simp, thin_tac \<open>\<not> (\<nexists>p. vwalk_bet (G.digraph_abs G') s p t)\<close>, goal_cases)
      case (1 p)
      have "s \<in> t_set srcs"
        using one(2)
        by (auto simp add: dfs.Graph.vset.set.invar_empty)
      moreover have "t \<notin> t_set srcs"
        using one(2) s_and_t(3)
        by (auto simp add: dfs.Graph.vset.set.invar_empty dfs.Graph.vset.set.set_empty)
      ultimately obtain q s' where "vwalk_bet (G.digraph_abs (parents
              (bfs.BFS G' (bfs_initial_state srcs)))) s' q t" "s' \<in> t_set srcs"
       using bfs.BFS_graph_path_implies_parent_path[OF bfs_axiom _ 1(2)]
       by auto
     hence "vwalk_bet (G.digraph_abs (parents
              (bfs.BFS G' (bfs_initial_state srcs)))) s q t" 
       using s_and_t  one(2)
       by (auto simp add: dfs.Graph.vset.set.invar_empty dfs.Graph.vset.set.set_empty)
     then show ?case 
       using "1"(1) by force
   qed
   hence "\<nexists>p. vwalk_bet_single_vertex (G.digraph_abs G') s p t"
     using s_and_t(3) by(auto simp add: vwalk_bet_single_vertex_def)
   thus ?thesis 
     using old_path_new_path 
     by(auto simp add: G_and_dfs_graph(1))
 next
   case 2
   thus ?thesis
     by (simp add: dfs.Graph.vset.set.set_empty)
 qed 
next
  case 2
  note two = this
  show ?case
  proof(cases "S = vset_empty")
    case True
    then show ?thesis by simp
  next
    case False
    hence "\<nexists>p. vwalk_bet (G.digraph_abs G') s p t"
      using two new_path_old_path 
      by(fastforce simp add: vwalk_bet_single_vertex_def G_and_dfs_graph(1))
    hence "\<nexists>p. vwalk_bet (G.digraph_abs bfs_tree) s p t" 
      using  bfs_impl_is bfs_invar_2 bfs_tree_def 
      by(fastforce intro: vwalk_bet_subset simp add: bfs.invar_2_def)
    then show ?thesis 
      using  dfs_lemmas.DFS_correct_2 dfs_lemmas.DFS_to_DFS_impl s_and_t(3)
      by(auto simp add: dfs_final_def dfs_impl_def dfs_initial_state_def  G_and_dfs_graph(1))
  qed
 qed
qed

lemma  find_path2: 
  assumes"find_path = Some p"
  shows  "\<exists> u v. vwalk_bet_single_vertex (dfs.Graph.digraph_abs G) u p v \<and> u \<in> t_set S 
                   \<and> v \<in> t_set T \<and>
                  (\<nexists> p' u' v'. vwalk_bet_single_vertex (dfs.Graph.digraph_abs G) u' p' v' \<and> u' \<in> t_set S 
                   \<and> v' \<in> t_set T \<and> 
                          length p' < length p)"
proof-
  have dfs_result:"return dfs_final = Reachable" "p = (tl (butlast (rev (stack dfs_final))))"
    using assms[simplified find_path_def]
    by(all \<open>cases "S = vset_empty"\<close>, all \<open>cases "return dfs_final = Reachable"\<close>) auto
  hence "\<exists> p. vwalk_bet (dfs.Graph.digraph_abs bfs_tree) s p t" 
    using  dfs_lemmas.DFS_correct_2 dfs_lemmas.DFS_to_DFS_impl s_and_t(3)
    by(auto simp add: dfs_final_def dfs_impl_def dfs_initial_state_def)
  hence "vwalk_bet (dfs.Graph.digraph_abs bfs_tree) s (rev (stack dfs_final)) t"
    using dfs_lemmas.DFS_correct_2 dfs_lemmas.DFS_to_DFS_impl dfs_result(1) s_and_t(3)
    by(auto simp add:  dfs_final_def dfs_impl_def dfs_initial_state_def) 
  hence "vwalk_bet (G.digraph_abs bfs_tree) s (rev (stack dfs_final)) t"
    by (simp add: G_and_dfs_graph(1))
  hence big_vwalk:"vwalk_bet
   (G.digraph_abs
     (parents (BFS.BFS \<langle>\<rangle> vset_union (expand_tree G') (next_frontier G') (bfs_initial_state srcs))))
   s (rev (stack dfs_final)) t"
    using bfs.BFS_impl_same[OF bfs_dom] by(simp add: bfs_impl_def bfs_tree_def)
  hence "vwalk_bet (G.digraph_abs G') s (rev (stack dfs_final)) t"  
    using  bfs_invar_2 by(auto intro: vwalk_bet_subset simp add: bfs.invar_2_def)
  hence "vwalk_bet (dfs.Graph.digraph_abs G') s (rev (stack dfs_final)) t"
    by (simp add: G_and_dfs_graph(1))
  hence p_good_path:"vwalk_bet_single_vertex (dfs.Graph.digraph_abs G) (hd p) p (last p)" "(hd p) \<in> t_set S"
          "(last p) \<in> t_set T" 
    using dfs_result(2) new_path_old_path vwalk_bet_nonempty_vwalk(3,4) 
    by (fastforce simp add:  vwalk_bet_single_vertex_def)+
  moreover have " (\<nexists> p' u' v'. vwalk_bet_single_vertex (dfs.Graph.digraph_abs G) u' p' v' \<and> u' \<in> t_set S 
                   \<and> v' \<in> t_set T \<and> 
                          length p' < length p)"
  proof(rule ccontr, goal_cases)
    case 1
    then obtain p' u' v' where p'_prop: "vwalk_bet_single_vertex (dfs.Graph.digraph_abs G) u'  p' v'"
          "length p' < length p"  "u' \<in> t_set S" "v' \<in> t_set T"by auto
    hence "vwalk_bet_single_vertex (dfs.Graph.digraph_abs G') s ([s]@p'@[t]) t"
      using old_path_new_path p_good_path(2) p_good_path(3) by auto
    hence "vwalk_bet_single_vertex (G.digraph_abs G') s ([s]@p'@[t]) t"
      by (simp add: G_and_dfs_graph(1))
    hence valk_G'_p:"vwalk_bet (G.digraph_abs G') s ([s]@p'@[t]) t"
      by (simp add: vwalk_bet_single_vertex_def)
    have s_in_srcs:"s \<in> t_set srcs" 
      using dfs.Graph.vset.set.set_empty p_good_path(2) by auto
    hence t_no_in_srcs: "t \<notin> t_set srcs" 
      using dfs.Graph.vset.set.set_empty s_and_t(3) by auto
    have "length (rev (stack dfs_final)) \<le> length ([s]@p'@[t]) "
      using bfs.parent_path_cheaper[OF bfs_axiom s_in_srcs valk_G'_p t_no_in_srcs big_vwalk] by simp
    thus False 
      using dfs_result(2) p'_prop(2) by force
  qed
  ultimately show ?thesis by auto
qed

lemmas find_path = find_path1 find_path2

lemma  find_path2_weak: 
  assumes"find_path = Some p"
  shows  "\<exists> u v. vwalk_bet_single_vertex (dfs.Graph.digraph_abs G) u p v \<and> u \<in> t_set S 
                   \<and> v \<in> t_set T \<and>
                  (\<nexists> p'. vwalk_bet_single_vertex (dfs.Graph.digraph_abs G) u p' v \<and> length p' < length p)"
  using find_path2[OF assms] by fast

lemmas find_path_weak = find_path1 find_path2_weak
end
end

end

lemma fold_rbt_lookup:"M.invar N \<Longrightarrow>
       \<exists>xs. set xs = dom (lookup N) \<and>
            fold_rbt (\<lambda>(x, y). f x y) N acc = foldr (\<lambda>x. f x (the (lookup N x))) xs acc"
  by(intro  exI[of _ "(map (fst o fst) (preorder N))"])
    (auto simp add: fold_rbt_is_foldr_of_preorder dom_is_preorder rbt_fold_preorder_lookup M.invar_def rbt_red_def rbt_def)

global_interpretation pair_graph_specs_reverse: Pair_Graph_Specs_Reverse
where insert = insert_rbt 
and sel = sel 
and vset_empty = Leaf 
and lookup = lookup 
and empty = empty 
and delete=delete 
and isin = isin 
and t_set=Tree2.set_tree
and update=update 
and adjmap_inv = M.invar
and vset_delete= delete_rbt
and vset_inv = vset_inv 
and fold_vset = fold_vset
and fold_adjmap= "\<lambda> f. fold_adjmap (\<lambda> (x, y) acc. f x y acc)"
defines reverse_graph = pair_graph_specs_reverse.reverse_graph 
and     reverse_neighbourhood=pair_graph_specs_reverse.reverse_neighbourhood
and add_edge = pair_graph_specs_reverse.add_edge
  by(auto intro!: Pair_Graph_Specs_Reverse.intro Pair_Graph_Specs_Reverse_axioms.intro fold_rbt_lookup 
           simp add: G.Pair_Graph_Specs_axioms fold_vset_def  rbt_fold_spec fold_adjmap_def)

(*definition "edges = [(0::nat, 1::nat), (0, 2), (2, 3), (2,4), (2,1), (1,5), (5,8), (8,7), (7,1),
                     (7,2), (7,4), (4,3), (3,4), (3,3), (9, 8), (8, 1), (4,5), (5,10)]"

definition "G = a_graph edges"

value "reverse_graph G"*)

locale Compute_Path2 =
  fixes carrier::"('a::linorder) set"
    and G::"(('a \<times> ('a \<times> color) tree) \<times> color) tree"
    and S::"('a \<times> color) tree"
    and T::"('a \<times> color) tree"
begin

definition "bfs_visited = visited (bfs_impl G (bfs_initial_state S))"

definition "bfs_tree = parents (bfs_impl G (bfs_initial_state S))"

definition "dfs_final = dfs_impl (reverse_graph bfs_tree) (\<lambda> w. isin S w) 
                                 (dfs_initial_state (sel (inter_rbt (bfs_visited) T) ))"

definition "find_path = (if inter_rbt (bfs_visited) T = empty then None 
                         else if return dfs_final = Reachable 
                                 then Some (stack (dfs_final)) 
                         else None)"
(*
lemma "pair_graph_specs_reverse.graph_inv = dfs.Graph.graph_inv" 
*)
context
  assumes graph_inv: "dfs.Graph.graph_inv G"
   and    finite_graph: "dfs.Graph.finite_graph G"
   and  finite_vs: "dfs.Graph.finite_vsets (TYPE ('a))"
   and vset_inv_S:"vset_inv S"
   and vset_inv_T:"vset_inv T"
   and S_in_carrier:"t_set S \<subseteq> carrier"
   and T_in_carrier:"t_set T \<subseteq> carrier"
   and verts_in_carrier: "dVs (dfs.Graph.digraph_abs G) \<subseteq> carrier"
begin

lemma empty_set_iff:"(X \<noteq> vset_empty) = (t_set X \<noteq> {})"
  by (simp add: RBT_Set.empty_def)

lemma non_emptyE: "X \<noteq> {} \<Longrightarrow> (\<And> x. x \<in> X \<Longrightarrow> P) \<Longrightarrow>P"
  by auto

lemma bfs_axiom:" BFS.BFS_axiom isin t_set M.invar \<langle>\<rangle> vset_inv lookup S G"
  using Tree2.finite_set_tree[of "DFS_Example.neighbourhood G _"]
        dfs.Graph.neighbourhood_abs[OF graph_inv] 
  by(unfold bfs.BFS_axiom_def G_and_dfs_graph)(auto simp add:  graph_inv finite_graph vset_inv_S)
  
lemma bfs_dom: " bfs.BFS_dom G (bfs_initial_state S)"
  using bfs.initial_state_props(4)[OF bfs_axiom] by blast

lemma bfs_impl_is: "bfs_impl G (bfs_initial_state S) = 
                    bfs.BFS G (bfs_initial_state S)"
  by(auto simp add: bfs.BFS_impl_same bfs.initial_state_props(4) bfs_axiom)

lemma bfs_invar_1: " bfs.invar_1 (bfs.BFS G (bfs_initial_state S))"
  using bfs_axiom  by(auto intro: bfs.invar_1_holds bfs_axiom bfs_dom)

lemma bfs_invar_2: "bfs.invar_2 S G 
      (bfs.BFS G (bfs_initial_state S))"
  using bfs_axiom  by(auto intro!: bfs.invar_2_holds bfs_axiom bfs_dom)

lemma vset_inv_visited: "vset_inv bfs_visited"
  using bfs.invar_1_def bfs_impl_is bfs_invar_1 bfs_visited_def by auto

lemma graph_inv_bfs_tree: "dfs.Graph.graph_inv bfs_tree"
  using bfs_invar_1 
  by(simp add:  adj_inv_def bfs.invar_1_def bfs_impl_is bfs_invar_1 bfs_tree_def)

lemma graph_inv_bfs_tree2: "pair_graph_specs_reverse.graph_inv bfs_tree" 
  by (simp add: G_and_dfs_graph(2) graph_inv_bfs_tree)

lemma finite_graph_bfs_tree: "dfs.Graph.finite_graph bfs_tree"
  using bfs_invar_1 
  by(simp add:  adj_inv_def bfs.invar_1_def bfs_impl_is bfs_invar_1 bfs_tree_def)

lemma graph_inv_reverse: "dfs.Graph.graph_inv (reverse_graph bfs_tree)" 
  using  graph_inv_bfs_tree pair_graph_specs_reverse.reverse_graph_correct(1) 
  by(auto simp add: adj_inv_def)

lemma reverse_finite_graph: "pair_graph_specs_reverse.finite_graph (reverse_graph bfs_tree)"
  using  graph_inv_bfs_tree pair_graph_specs_reverse.reverse_graph_correct(2) 
  by(auto simp add: adj_inv_def)

interpretation dfs_lemmas: DFS_thms  where insert = vset_insert and
 sel = sel and  vset_empty = vset_empty and  diff = vset_diff and
 lookup = lookup and empty = map_empty and delete=delete and isin = isin and t_set=t_set
and update=update and adjmap_inv = adj_inv and vset_delete= vset_delete
and vset_inv = vset_inv and union=vset_union and inter=vset_inter and G= "reverse_graph bfs_tree"
and s = "sel (inter_rbt (bfs_visited) T)" and P_T ="(\<lambda> w. isin S w)"
  by(auto intro!: DFS_thms.intro DFS_thms_axioms.intro 
           simp add: dfs.DFS_axioms DFS.DFS_axioms_def[OF  dfs.DFS_axioms] finite_vs
                     graph_inv_reverse reverse_finite_graph)

lemma vwalk_reverse:"Vwalk.vwalk E p \<Longrightarrow> Vwalk.vwalk {(u, v) | u v. (v, u) \<in> E} (rev p)"
  by(induction  rule: Vwalk.vwalk.induct)
     (auto simp add: vwalk_snoc_edge dVs_def)

lemma vwalk_bet_reverse:"vwalk_bet E u p v \<Longrightarrow> vwalk_bet {(u, v) | u v. (v, u) \<in> E} v (rev p) u"
  using vwalk_reverse[of E p] hd_rev  last_rev by (auto simp add: vwalk_bet_def )

lemma pair_graph_reversal_identities: " {(y, x) |x y. (x, y) \<in> E} =  {(u, v) | u v. (v, u) \<in> E}"
                                      " {(y, x) |x y. (x, y) \<in> E} =  prod.swap ` E" 
                                      "{(u, v) | u v. (v, u) \<in> E} = prod.swap ` E"
  by auto

lemma vwalk_bet_reverse_iff:"vwalk_bet {(u, v) | u v. (v, u) \<in> E} v (rev p) u \<longleftrightarrow> vwalk_bet E u p v"
  using vwalk_reverse[of E p] vwalk_reverse[of " {(u, v) | u v. (v, u) \<in> E}" "rev p"]
        hd_rev  last_rev by (auto simp add: vwalk_bet_def )

abbreviation "trg == (sel (vset_inter bfs_visited T))"

lemma  find_path1: "find_path  = None \<longleftrightarrow> 
                             (\<nexists> p u v. vwalk_bet_single_vertex (dfs.Graph.digraph_abs G) u p v \<and>
                                       u \<in> t_set S \<and> v \<in> t_set T)"
proof-
  have find_path_means:"find_path  = None \<longleftrightarrow> (return dfs_final \<noteq> Reachable 
                 \<or> inter_rbt (bfs_visited) T = empty)"
    by(simp add: find_path_def)
  show ?thesis
    unfolding find_path_def
proof(rule, goal_cases)
  case 1
  hence not_reachable:"return dfs_final = NotReachable \<or> inter_rbt (bfs_visited) T = empty"
    using find_path_def find_path_means return.exhaust by auto
  show ?case
  proof(rule ccontr, goal_cases)
    case 1
    then obtain p s t where pst:"vwalk_bet_single_vertex (pair_graph_specs_reverse.digraph_abs G) s p t"
                       "s \<in> t_set S" "t \<in> t_set T"
      by(auto simp add: G_and_dfs_graph(1))
    have t_visited:"t \<in> t_set bfs_visited"
    proof(rule ccontr, goal_cases)
      case 1
      hence t_not_visited:"t \<notin> t_set (visited (bfs.BFS G (bfs_initial_state S)))"
        by (simp add: bfs_impl_is bfs_visited_def)
      then show ?case using 
         bfs.BFS_correct_1[OF bfs_axiom pst(2) t_not_visited] bfs.ret1_holds[OF bfs_axiom bfs_dom]
         bfs_invar_2 pst(1,2) set.set_empty 
        by(auto simp add: vwalk_bet_single_vertex_def  bfs.invar_2_def bfs.BFS_ret_1_conds_def)
    qed
     have t_in_inter:"t \<in> t_set bfs_visited \<inter> t_set T"
       by (simp add: pst(3) t_visited)
     have "vset_inter bfs_visited T \<noteq> vset_empty"
       using dfs.set_ops.set_inter[OF vset_inv_visited vset_inv_T] t_in_inter by auto
     hence a1:"(sel (inter_rbt (bfs_visited) T)) \<in> t_set bfs_visited \<inter> t_set T" 
       using dfs.Graph.vset.choose[of "inter_rbt (bfs_visited) T"] 
             dfs.set_ops.invar_inter[OF vset_inv_visited vset_inv_T] 
       by (simp add: bfs_subprocedures.set_ops.set_inter vset_inv_T vset_inv_visited)
     have  not_reachable:"return dfs_final = NotReachable" 
       using \<open>vset_inter bfs_visited T \<noteq> vset_empty\<close> not_reachable by auto
     have "dfs.Graph.not_isin' (sel (vset_inter bfs_visited T)) S"
       using  dfs_lemmas.DFS_to_DFS_impl not_reachable
       by(auto intro!: dfs_lemmas.DFS_correct_1_s_is_t simp add: dfs_final_def dfs_impl_def dfs_initial_state_def)
     hence a2:"(sel (inter_rbt (bfs_visited) T)) \<notin> t_set S"
       by (simp add: vset_inv_S)
     have "distance_set_single (pair_graph_specs_reverse.digraph_abs G) (t_set S) (sel (vset_inter bfs_visited T)) =
     distance_set_single (pair_graph_specs_reverse.digraph_abs (parents (bfs.BFS G (bfs_initial_state S))))
       (t_set S) (sel (vset_inter bfs_visited T))"
       using a1 a2 
       by (fastforce simp add: bfs_impl_is bfs_visited_def
           intro!: bfs.BFS_correct_2[OF bfs_axiom, of "(sel (inter_rbt (bfs_visited) T))"])
     moreover have "distance_set_single (pair_graph_specs_reverse.digraph_abs G) (t_set S)
                     (sel (vset_inter bfs_visited T)) <  \<infinity>" 
     proof-
       have "bfs.invar_current_reachable S G (bfs.BFS G (bfs_initial_state S))"
         using bfs.initial_state_props(1) bfs.initial_state_props(10) bfs.initial_state_props(2) 
             bfs.invar_current_reachable_holds bfs_axiom bfs_dom by blast
       thus ?thesis
         using a1 bfs_impl_is bfs_visited_def 
         by (auto simp add:  bfs.invar_current_reachable_def[OF bfs_axiom])
     qed
     ultimately  obtain s' p' where s'p':"vwalk_bet 
         (pair_graph_specs_reverse.digraph_abs (parents (bfs.BFS G (bfs_initial_state S))))
       s' p' (sel (vset_inter bfs_visited T))" "s' \<in> t_set S "
       using a2 dist_single_not_inf'[of 
            "(pair_graph_specs_reverse.digraph_abs (parents (bfs.BFS G (bfs_initial_state S))))"
                 "(t_set S)" "(sel (vset_inter bfs_visited T))"] 
       by(auto intro:  reachable_dist_2)
     then obtain p''  where p'':"vwalk_bet 
         (pair_graph_specs_reverse.digraph_abs (parents (bfs.BFS G (bfs_initial_state S))))
       s' p'' (sel (vset_inter bfs_visited T))" "distinct p''" 
       using  vwalk_bet_to_distinct_is_distinct_vwalk_bet
       by(fastforce simp add: distinct_vwalk_bet_def)
     have "\<exists> p t. distinct p \<and>
      vwalk_bet (pair_graph_specs_reverse.digraph_abs (reverse_graph bfs_tree)) (sel (vset_inter bfs_visited T)) p t \<and>
      dfs.Graph.isin' t S" 
       using pair_graph_specs_reverse.reverse_graph_correct(3)[OF graph_inv_bfs_tree2] vwalk_bet_reverse[OF p''(1)]
       by (auto intro!: exI[of _ "rev p''"] simp add: p'' bfs_impl_is bfs_tree_def pair_graph_reversal_identities(1) s'p'(2) vset_inv_S)
     thus False 
       using   dfs_lemmas.DFS_correct_1 not_reachable
       by (simp add:  G_and_dfs_graph dfs_final_def dfs_impl_def dfs_initial_state_def dfs_lemmas.DFS_to_DFS_impl)
   qed
 next
   case 2
   note two = this
   show ?case
   proof(rule ccontr, goal_cases)
     case 1
     hence one: "return dfs_final = Reachable" "vset_inter bfs_visited T \<noteq> vset_empty"
       using find_path_means  "1" by presburger+
  hence return_not_Reachable:"return (DFS.DFS vset_insert sel vset_empty vset_diff lookup (reverse_graph bfs_tree) (\<lambda> w. isin S w)
     (DFS.initial_state vset_insert vset_empty (sel (inter_rbt (bfs_visited) T)))) = Reachable"
    by(simp add: dfs_final_def dfs_impl_def dfs_initial_state_def dfs_lemmas.DFS_to_DFS_impl)
  obtain p s where  pt:
    "(vwalk_bet (dfs.Graph.digraph_abs (reverse_graph bfs_tree)) (sel (vset_inter bfs_visited T)) p s \<or>
     p = [sel (vset_inter bfs_visited T)] \<and> sel (vset_inter bfs_visited T) = s)" "dfs.Graph.isin' s S"
    using dfs_lemmas.DFS_correct_2[OF return_not_Reachable] by auto
   have sel_in_T:"sel (vset_inter bfs_visited T) \<in> t_set T"
      using  bfs_subprocedures.set_ops.invar_inter[OF vset_inv_visited vset_inv_T]
             bfs_subprocedures.set_ops.set_inter[OF vset_inv_visited vset_inv_T]
             dfs.Graph.vset.choose'[OF one(2)] by simp
  show False
  proof(rule disjE[OF pt(1)], goal_cases)
    case 1
    have "vwalk_bet (dfs.Graph.digraph_abs bfs_tree) s (rev p) (sel (vset_inter bfs_visited T))"
      using pair_graph_specs_reverse.reverse_graph_correct(3)[OF graph_inv_bfs_tree2] 
             "1"[simplified vwalk_bet_reverse_iff[of "dfs.Graph.digraph_abs _", symmetric]]
      by(simp add: reverse_graph_def G_and_dfs_graph(1))
    hence "vwalk_bet (pair_graph_specs_reverse.digraph_abs bfs_tree) s (rev p) (sel (vset_inter bfs_visited T))"  
      by (simp add: G_and_dfs_graph(1))
    hence "vwalk_bet (pair_graph_specs_reverse.digraph_abs G) s (rev p) (sel (vset_inter bfs_visited T))"  
      using bfs_invar_2
      by(auto intro:  vwalk_bet_subset simp add: bfs_impl_is  bfs_tree_def  bfs.invar_2_def)
    thus False 
      using two pt(2) sel_in_T
      by(auto simp add: G_and_dfs_graph(1) dfs.Graph.vset.set.set_isin[OF vset_inv_S] vwalk_bet_single_vertex_def)
  next
    case 2
    hence "vwalk_bet_single_vertex (dfs.Graph.digraph_abs G) (sel (vset_inter bfs_visited T))
                     p (sel (vset_inter bfs_visited T))"
      by (simp add: vwalk_bet_single_vertex_single)
    thus False
      using "2" pt(2) sel_in_T two vset_inv_S by auto
  qed
qed
qed
qed

lemma  find_path2: 
  assumes"find_path = Some p"
  shows  "\<exists> u v. vwalk_bet_single_vertex (dfs.Graph.digraph_abs G) u p v \<and> u \<in> t_set S 
                   \<and> v \<in> t_set T \<and>
                  (\<nexists> p'. vwalk_bet_single_vertex (dfs.Graph.digraph_abs G) u p' v \<and> length p' < length p)"
proof-
  have dfs_result:"return dfs_final = Reachable" "p = (stack dfs_final)"
    using assms[simplified find_path_def]
    by(all \<open>cases "vset_inter bfs_visited T = vset_empty"\<close>, all \<open>cases "return dfs_final = Reachable"\<close>) auto
  (*hence "\<exists> s p. 
      vwalk_bet (dfs.Graph.digraph_abs bfs_tree) (sel (vset_inter bfs_visited T)) p s" 
    using  dfs_lemmas.DFS_correct_2 dfs_lemmas.DFS_to_DFS_impl 
    by(auto simp add: dfs_final_def dfs_impl_def dfs_initial_state_def)*)
  have stack_is:"(stack
                 (dfs.DFS (reverse_graph bfs_tree) (\<lambda>w. dfs.Graph.isin' w S)
                   (DFS.initial_state vset_insert vset_empty (sel (vset_inter bfs_visited T))))) = p"
    by (simp add: dfs_final_def dfs_impl_def dfs_initial_state_def dfs_lemmas.DFS_to_DFS_impl dfs_result(2))
  then obtain s where  t_prop:"(vwalk_bet (dfs.Graph.digraph_abs (reverse_graph bfs_tree)) (sel (vset_inter bfs_visited T))
          (rev p) s \<or>
          p =[sel (vset_inter bfs_visited T)] \<and>  sel (vset_inter bfs_visited T) = s)"
          "dfs.Graph.isin' s S"
    using dfs_lemmas.DFS_correct_2 dfs_lemmas.DFS_to_DFS_impl dfs_result(1)
    by(auto simp add:  dfs_final_def dfs_impl_def dfs_initial_state_def) 
  have distinct_p:"distinct p" 
    using dfs_lemmas.initial_state_props(1) dfs_lemmas.initial_state_props(3)
          dfs_lemmas.initial_state_props(6) 
         dfs_lemmas.invar_seen_stack_holds dfs_lemmas.invar_seen_stack_props 
    by (auto simp add: dfs_result dfs_final_def  dfs_impl_def
            dfs_initial_state_def dfs_lemmas.DFS_to_DFS_impl[symmetric] )
  have sel_in_T:"sel (vset_inter bfs_visited T) \<in> t_set bfs_visited \<inter> t_set T" 
    using  S_C.choose' assms bfs_subprocedures.set_ops.invar_inter[OF  vset_inv_visited  vset_inv_T]
           bfs_subprocedures.set_ops.set_inter[OF  vset_inv_visited  vset_inv_T]
    by(auto simp add: find_path_def)
  have disjE': "A \<or> B \<Longrightarrow> (A \<Longrightarrow> \<not> B \<Longrightarrow> P ) \<Longrightarrow> (B \<Longrightarrow> P) \<Longrightarrow> P" for A B P by auto
  show ?thesis
  proof(rule disjE'[OF t_prop(1)], goal_cases)
    case 1
    hence vwalk_sp:"vwalk_bet (dfs.Graph.digraph_abs bfs_tree) s p (sel (vset_inter bfs_visited T))"
      using pair_graph_specs_reverse.reverse_graph_correct(3)[OF graph_inv_bfs_tree2] 
             "1"[simplified vwalk_bet_reverse_iff[of "dfs.Graph.digraph_abs _", symmetric]]
      by(simp add: reverse_graph_def G_and_dfs_graph(1))
    hence "vwalk_bet (dfs.Graph.digraph_abs G) s p (sel (vset_inter bfs_visited T))"
      using   bfs_invar_2 
      by (auto intro: vwalk_bet_subset simp add: G_and_dfs_graph(1) bfs_tree_def bfs.invar_2_def bfs_impl_is)
    moreover have s_in_S:"s \<in> t_set S"
      using t_prop(2) vset_inv_S by auto
    moreover have "(sel (vset_inter bfs_visited T)) \<in> t_set T"
      using sel_in_T by auto
    moreover have "(\<nexists>p'. vwalk_bet_single_vertex (dfs.Graph.digraph_abs G) s p' (sel (vset_inter bfs_visited T))
                     \<and> length p' < length p)"
    proof(cases "(sel (vset_inter bfs_visited T)) \<in> t_set S")
      case True   
      hence "p = [s] \<and> s = (sel (vset_inter bfs_visited T))" 
        using dfs_lemmas.DFS_correct_2_s_is_t(2) calculation(1) dfs.Graph.vset.set.set_isin[OF vset_inv_S]
        by(unfold  vwalk_bet_def stack_is) simp
      thus ?thesis 
        using "1"(2) by blast
    next
      case False
      show ?thesis
        proof(rule ccontr, goal_cases)
        case 1
        then obtain p' where p'_prop: "vwalk_bet_single_vertex (pair_graph_specs_reverse.digraph_abs G) s p'
                             (sel (vset_inter bfs_visited T))" "length p' < length p"
        by(auto simp add: G_and_dfs_graph(1))
        moreover hence vwalk_bet_p': "vwalk_bet (pair_graph_specs_reverse.digraph_abs G) s p'
                             (sel (vset_inter bfs_visited T))" 
        using False s_in_S vwalk_bet_single_vertex_def by fastforce
        moreover have "length p - 1 = distance_set_single (pair_graph_specs_reverse.digraph_abs G) (t_set S)
             (sel (vset_inter bfs_visited T))" 
        using  vwalk_sp  bfs.BFS_correct_3[OF bfs_axiom s_in_S]
        by(simp add: bfs_impl_is bfs_tree_def G_and_dfs_graph(1))
        moreover hence "length p = distance_set_single (pair_graph_specs_reverse.digraph_abs G) (t_set S)
             (sel (vset_inter bfs_visited T)) + 1" 
        using add_leE less_iff_succ_less_eq one_enat_def 
              ordered_cancel_comm_monoid_diff_class.diff_add p'_prop(2) plus_enat_simps(1)
        by metis
        ultimately show False 
        using False vwalk_sp bfs.parent_path_cheaper[OF bfs_axiom s_in_S] 
        by(fastforce simp add: bfs_impl_is bfs_tree_def  G_and_dfs_graph(1))      
      qed
    qed
    ultimately show ?thesis 
      by (auto simp add: vwalk_bet_single_vertex_def)
  next
    case 2
    show ?case
    using t_prop(2) vset_inv_S  "2" sel_in_T
    by (auto intro: exI[of _ s] simp add: "2" vwalk_bet_single_vertex_def)
qed
qed

lemmas find_path = find_path1 find_path2

lemmas find_path_weak = find_path1 find_path2
end
end

global_interpretation compute_path: Compute_Path
  where G = G and s=s and t = t and S = S and T = T and carrier =carrier
  for G s t S T carrier
  defines find_path = Compute_Path.find_path
      and dfs_final = Compute_Path.dfs_final
      and bfs_tree = Compute_Path.bfs_tree
      and srcs=Compute_Path.srcs
      and G' = Compute_Path.G'
      and one_source = Compute_Path.one_source
  done

lemmas find_path = Compute_Path.find_path
lemmas find_path_for_msec = Compute_Path.find_path_weak

end