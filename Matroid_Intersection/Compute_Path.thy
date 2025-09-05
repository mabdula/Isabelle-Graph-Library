theory Compute_Path
  imports "Graph_Algorithms_Dev.BFS_Example" "Graph_Algorithms_Dev.DFS_Example"
    "Graph_Algorithms_Dev.RBT_Map_Extension"
begin  

lemma G_and_dfs_graph: "G.digraph_abs = dfs.Graph.digraph_abs"
  "G.graph_inv = dfs.Graph.graph_inv"
  by(auto simp add: RBT_Set.empty_def G.digraph_abs_def dfs.Graph.digraph_abs_def 
      DFS_Example.neighbourhood_def adj_inv_def)

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

abbreviation "srcs \<equiv> ( vset_insert s vset_empty)"

definition "bfs_tree = parents (bfs_impl G' (bfs_initial_state srcs))"

definition "dfs_final = dfs_impl bfs_tree t (dfs_initial_state s)"

definition "find_path = (if S = empty then None 
                         else if return dfs_final = Reachable 
                                 then Some (tl (butlast (rev (stack (dfs_final))))) 
                         else None)"

lemma srcs_are: "t_set srcs = {s}"
  by (simp add: RBT_Set.empty_def)

context 
  assumes s_and_t: "s \<notin> carrier"  "t \<notin> carrier"  "s \<noteq> t"
begin

context
  assumes graph_inv: "dfs.Graph.graph_inv G"
    and    finite_graph: "dfs.Graph.finite_graph G"
    and  finite_vs: "dfs.Graph.finite_vsets G"
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
  "vwalk_bet (dfs.Graph.digraph_abs G') s p t \<Longrightarrow>
(length p \<ge> 3 \<and> (\<exists> s' t'. 
    (vwalk_bet (dfs.Graph.digraph_abs G) s' (tl (butlast p)) t' 
            \<or> ([s'] =  (tl (butlast p)) \<and> s' = t'))
      \<and> s' \<in> t_set S \<and> t' \<in> t_set T))"
proof(goal_cases)
  case 1
  note one = this
  then have "1 \<le> length p"
    using not_less_eq_eq by (auto simp add:  vwalk_bet_def)
  moreover have "length p \<noteq> 2"
  proof(rule ccontr, subst (asm) not_not, goal_cases)
    case 1
    hence "(s,t) \<in> (dfs.Graph.digraph_abs G')" 
      using one
      by(auto intro: vwalk_arcs.cases[of p] simp add:  vwalk_bet_def )
    then show ?case 
      using S_in_carrier T_in_carrier s_and_t verts_in_carrier
      by(auto simp add: G'_properties(3))
  qed
  moreover have "length p \<noteq> 1"
  proof(rule ccontr, subst (asm) not_not, goal_cases)
    case 1
    hence "s = t" 
      using one
      by(auto intro: vwalk_arcs.cases[of p] simp add: vwalk_bet_def )
    then show ?case 
      using  s_and_t by simp
  qed
  ultimately have length_p:"3 \<le> length p"
    by auto
  moreover have "hd p = s"  "last p = t" 
    using "1"  by fastforce+
  ultimately obtain q where p_split:"p = [s]@q@[t]"
    by (metis append_butlast_last_id append_eq_Cons_conv hd_Cons_tl hd_Nil_eq_last last.simps s_and_t(3))
  have q_length: "length q > 0"
    using \<open>length p \<noteq> 2\<close> p_split by fastforce
  hence "vwalk_bet (dfs.Graph.digraph_abs G') s p t"
    using one s_and_t(3) by fastforce
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
  ultimately have "((vwalk_bet (dfs.Graph.digraph_abs G) (hd q) (tl (butlast p)) (last q) \<or> 
                     ([hd q] = (tl (butlast p)) \<and> hd q = last q))\<and>
        (hd q) \<in> t_set S \<and> (last q) \<in> t_set T)"
    using length_p p_split vwalk_q_G' neq_Nil_conv 
    by(auto simp add:  G'_properties(3) Suc_1[symmetric] Suc_le_length_iff
        , auto?)
  then show ?case 
    using length_p by auto     
qed

lemma old_path_new_path:
  assumes "((\<exists> s' t'. (vwalk_bet (dfs.Graph.digraph_abs G) s' p t' \<or> ([s'] = p \<and> s' = t'))
             \<and> s' \<in> t_set S \<and> t' \<in> t_set T))"
  shows   "vwalk_bet (dfs.Graph.digraph_abs G') s ([s]@p@[t]) t"
proof-
  obtain s' t' where props:"vwalk_bet (dfs.Graph.digraph_abs G) s' p t' \<or> ([s'] = p \<and> s' = t')"
    "s' \<in> t_set S" "t' \<in> t_set T"
    using assms by auto
  hence "vwalk_bet (dfs.Graph.digraph_abs G') s' p t' \<or> ([s'] = p \<and> s' = t')" 
    unfolding G'_properties(3) 
    by(auto intro: vwalk_bet_subset simp add: G'_properties(3) )
  moreover have "(s,s') \<in> dfs.Graph.digraph_abs G'"
    using props(2,3) by(simp add: G'_properties(3))
  moreover have "(t', t) \<in> dfs.Graph.digraph_abs G'"
    using props(2,3) by(simp add: G'_properties(3))
  ultimately show ?thesis 
    by(auto simp add: Vwalk.vwalkI vwalk_append_single vwalk_bet_def)
qed

lemma empty_set_iff:"(X \<noteq> vset_empty) = (t_set X \<noteq> {})"
  by (simp add: RBT_Set.empty_def)

lemma non_emptyE: "X \<noteq> {} \<Longrightarrow> (\<And> x. x \<in> X \<Longrightarrow> P) \<Longrightarrow>P"
  by auto

lemma bfs_axiom:"S \<noteq> vset_empty \<Longrightarrow> BFS.BFS_axiom isin t_set M.invar \<langle>\<rangle> vset_inv lookup srcs G'"
(*proof(cases "S \<noteq> vset_empty")
  case True
  show ?thesis *)
    apply(insert (*True*) G'_properties(1,2) dVsI(1)[of s _ "{(s, ss) |ss. ss \<in> t_set S}"] finite_vs)
    apply(unfold bfs.BFS_axiom_def G_and_dfs_graph G'_properties(3))
    by(auto simp add: dfs.Graph.vset.set.set_insert[OF dfs.Graph.vset.set.invar_empty]
        dfs.Graph.vset.emptyD(1) split: if_split,
        rule non_emptyE[of "t_set S" _], 
        auto intro:  rev_finite_subset[OF  dfs.Graph.finite_vertices] 
        simp add: G'_properties(3) finite_vs dfs.Graph.vset.set.invar_empty  empty_set_iff
        dfs.Graph.finite_vsets_def dfs.Graph.neighbourhood_abs[OF  graph_inv, symmetric])
(*next
  case False
  show ?thesis
    apply(simp, insert False G'_properties(1,2) dVsI(1)[of s _ "{(s, ss) |ss. ss \<in> t_set S}"] finite_vs)
    apply(unfold bfs.BFS_axiom_def G_and_dfs_graph G'_properties(3))
    using  infinite_super dfs.Graph.vset.set.set_empty  vset_inv_S
   apply auto 
qed
*)

lemma bfs_dom: "S \<noteq> vset_empty \<Longrightarrow> bfs.BFS_dom G' (bfs_initial_state srcs)"
  using bfs.initial_state_props(4)[OF bfs_axiom] by blast

lemma bfs_impl_is: "S \<noteq> vset_empty\<Longrightarrow> bfs_impl G' (bfs_initial_state srcs) = 
                    bfs.BFS G' (bfs_initial_state srcs)"
  by(auto simp add: bfs.BFS_impl_same bfs.initial_state_props(4) bfs_axiom)

lemma bfs_invar_1: "S \<noteq> vset_empty\<Longrightarrow> bfs.invar_1 (bfs.BFS G' (bfs_initial_state srcs))"
  using bfs_axiom  by(auto intro: bfs.invar_1_holds bfs_axiom bfs_dom)

lemma bfs_invar_2: "S \<noteq> vset_empty \<Longrightarrow>bfs.invar_2 srcs G' 
      (bfs.BFS G' (bfs_initial_state srcs))"
  using bfs_axiom  by(auto intro!: bfs.invar_2_holds bfs_axiom bfs_dom)

lemma graph_inv_bfs_tree: "S \<noteq> vset_empty \<Longrightarrow> dfs.Graph.graph_inv bfs_tree"
  using bfs_invar_1 
  by(simp add:  adj_inv_def bfs.invar_1_def bfs_impl_is bfs_invar_1 bfs_tree_def)

lemma finite_graph_bfs_tree: assumes "S \<noteq> empty" 
  shows "dfs.Graph.finite_graph bfs_tree"
  using bfs_invar_1[OF assms]
 by(simp add: adj_inv_def bfs.invar_1_def bfs_impl_is[OF assms] bfs_invar_1[OF assms] bfs_tree_def
  G.graph_inv_def)

lemma S_not_empty_s_in_dVs_of_bfs_tree:
  assumes "S \<noteq> vset_empty"
     shows "s \<in> dVs (dfs.Graph.digraph_abs bfs_tree)"
      proof-
         obtain x where x_prop:"x \<in> t_set S"
           using assms vset_inv_S by blast
         hence "(s, x) \<in> G.digraph_abs G'"
           using G'_properties(3,4) by fastforce
         moreover have "x \<noteq> s" 
           using S_in_carrier s_and_t(1) x_prop by blast
         ultimately have "s \<in> dVs (G.digraph_abs (parents (bfs.BFS G' (bfs_initial_state srcs))))"
           using bfs.source_in_bfs_tree[OF bfs_axiom[OF assms], of s, simplified srcs_are] 
           by auto
         thus ?thesis
           by (simp add: assms G_and_dfs_graph(1) bfs_impl_is bfs_tree_def)
       qed

context 
  assumes  S_non_empt: "S \<noteq> vset_empty" 
begin

lemma  s_in_parents: "s \<in> dVs (dfs.Graph.digraph_abs bfs_tree)"
  using S_non_empt S_not_empty_s_in_dVs_of_bfs_tree by blast

interpretation dfs_lemmas: DFS_thms  where insert = vset_insert and
  sel = sel and  vset_empty = vset_empty and  diff = vset_diff and
  lookup = lookup and empty = map_empty and delete=delete and isin = isin and t_set=t_set
  and update=update and adjmap_inv = adj_inv and vset_delete= vset_delete
  and vset_inv = vset_inv and union=vset_union and inter=vset_inter and G= bfs_tree
  and t = t
 by(auto intro!: DFS_thms.intro DFS_thms_axioms.intro s_in_parents
      simp add: dfs.DFS_axioms DFS.DFS_axioms_def[OF  dfs.DFS_axioms] G'_properties finite_vs
      graph_inv_bfs_tree[OF S_non_empt] finite_graph_bfs_tree[OF S_non_empt]  dfs.Graph.finite_vsetsI)

lemmas dfs_lemmas_DFS_to_DFS_impl = dfs_lemmas.DFS_to_DFS_impl
lemmas dfs_lemmas_DFS_thms_axioms = dfs_lemmas.DFS_thms_axioms
lemmas dfs_lemmas_DFS_correct_1 = dfs_lemmas.DFS_correct_1
lemmas dfs_lemmas_DFS_correct_2 = dfs_lemmas.DFS_correct_2
end

lemma  find_path1: "find_path  = None \<longleftrightarrow> 
                             (\<nexists> p u v. (vwalk_bet (dfs.Graph.digraph_abs G) u p v \<or> (p = [u] \<and> u = v)) \<and>
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
      hence one: "return dfs_final \<noteq> Reachable" "S \<noteq> vset_empty" using 1 by simp+
      hence "return (DFS.DFS vset_insert sel vset_empty vset_diff lookup bfs_tree t
     (DFS.initial_state vset_insert vset_empty s)) \<noteq> Reachable" using one
        by (simp add: dfs_final_def dfs_impl_def dfs_initial_state_def 
                dfs_lemmas_DFS_to_DFS_impl[OF one(2) ]
            DFS_thms.DFS_to_DFS_impl[OF dfs_lemmas_DFS_thms_axioms] )

      hence "\<nexists>p. distinct p \<and> vwalk_bet (dfs.Graph.digraph_abs bfs_tree) s p t"
        using dfs_lemmas_DFS_correct_1[OF one(2) ] by(auto intro: return.exhaust)
      hence "\<nexists>p. vwalk_bet (dfs.Graph.digraph_abs bfs_tree) s p t"
        using   vwalk_bet_to_distinct_is_distinct_vwalk_bet by(fastforce simp add: distinct_vwalk_bet_def)
      hence no_parent_path:"\<nexists>p. vwalk_bet (G.digraph_abs bfs_tree) s p t"
        by (simp add: G_and_dfs_graph(1))
      have "\<nexists>p. vwalk_bet (G.digraph_abs G') s p t"
      proof(insert no_parent_path, unfold bfs_tree_def bfs_impl_def,
          subst (asm) BFS.BFS_impl_same[OF bfs.BFS_axioms bfs_dom[OF one(2)]],
          rule ccontr, goal_cases) 
        case 1
        then obtain p where "vwalk_bet (G.digraph_abs G') s p t" by auto
        note 1 = 1(1) this
        have "s \<in> t_set srcs"
          using one(2)
          by (auto simp add: dfs.Graph.vset.set.invar_empty)
        moreover have "t \<notin> t_set srcs"
          using one(2) s_and_t(3)
          by (auto simp add: dfs.Graph.vset.set.invar_empty dfs.Graph.vset.set.set_empty)
        ultimately obtain q s' where "vwalk_bet (G.digraph_abs (parents
              (bfs.BFS G' (bfs_initial_state srcs)))) s' q t" "s' \<in> t_set srcs"
          using bfs.BFS_graph_path_implies_parent_path[OF bfs_axiom _ 1(2), OF one(2)]
          by auto
        hence "vwalk_bet (G.digraph_abs (parents
              (bfs.BFS G' (bfs_initial_state srcs)))) s q t" 
          using s_and_t  one(2)
          by (auto simp add: dfs.Graph.vset.set.invar_empty dfs.Graph.vset.set.set_empty)
        then show ?case 
          using "1"(1) by force
      qed
      hence "\<nexists>p. vwalk_bet (G.digraph_abs G') s p t"
        using s_and_t(3) by(auto simp add:)
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
        by(fastforce simp add:  G_and_dfs_graph(1))
      hence no_p_in_tree:"\<nexists>p. vwalk_bet (G.digraph_abs bfs_tree) s p t" 
        using  bfs_impl_is bfs_invar_2 bfs_tree_def False
        by(fastforce intro: vwalk_bet_subset simp add: bfs.invar_2_def)
      moreover have "s \<in> dVs (dfs.Graph.digraph_abs bfs_tree)"
        using False S_not_empty_s_in_dVs_of_bfs_tree by blast
      ultimately show ?thesis 
        using  dfs_lemmas_DFS_correct_2[OF False] dfs_lemmas_DFS_to_DFS_impl[OF False] s_and_t(3)
        by(auto simp add: dfs_final_def dfs_impl_def dfs_initial_state_def  G_and_dfs_graph(1))
    qed
  qed
qed

lemma  find_path2: 
  assumes"find_path = Some p"
  shows  "\<exists> u v. (vwalk_bet (dfs.Graph.digraph_abs G) u p v \<or> (p = [u] \<and> u = v)) \<and> u \<in> t_set S 
                   \<and> v \<in> t_set T \<and>
                  (\<nexists> p' u' v'. (vwalk_bet (dfs.Graph.digraph_abs G) u' p' v' \<or> (p' = [u'] \<and> u' = v')) \<and> u' \<in> t_set S 
                   \<and> v' \<in> t_set T \<and> 
                          length p' < length p)"
proof-
    have dfs_result:"return dfs_final = Reachable" "p = (tl (butlast (rev (stack dfs_final))))"
           "S \<noteq> vset_empty"
    using assms[simplified find_path_def]
    by(all \<open>cases "S = vset_empty"\<close>, all \<open>cases "return dfs_final = Reachable"\<close>) auto
  hence "\<exists> p. vwalk_bet (dfs.Graph.digraph_abs bfs_tree) s p t" 
    using  dfs_lemmas_DFS_correct_2[OF dfs_result(3)] dfs_lemmas_DFS_to_DFS_impl s_and_t(3)
    by(auto simp add: dfs_final_def dfs_impl_def dfs_initial_state_def)
  hence "vwalk_bet (dfs.Graph.digraph_abs bfs_tree) s (rev (stack dfs_final)) t"
    using dfs_lemmas_DFS_correct_2[OF dfs_result(3)] 
          dfs_lemmas_DFS_to_DFS_impl[OF dfs_result(3)] dfs_result(1) s_and_t(3)
    by(auto simp add:  dfs_final_def dfs_impl_def dfs_initial_state_def) 
  hence "vwalk_bet (G.digraph_abs bfs_tree) s (rev (stack dfs_final)) t"
    by (simp add: G_and_dfs_graph(1))
  hence big_vwalk:"vwalk_bet
   (G.digraph_abs
     (parents (BFS.BFS \<langle>\<rangle> vset_union (expand_tree G') (next_frontier G') (bfs_initial_state srcs))))
   s (rev (stack dfs_final)) t"
    using bfs.BFS_impl_same[OF bfs_dom[OF  dfs_result(3)]] by(simp add: bfs_impl_def bfs_tree_def)
  hence "vwalk_bet (G.digraph_abs G') s (rev (stack dfs_final)) t"  
    using  bfs_invar_2[OF dfs_result(3)] by(auto intro: vwalk_bet_subset simp add: bfs.invar_2_def)
  hence "vwalk_bet (dfs.Graph.digraph_abs G') s (rev (stack dfs_final)) t"
    by (simp add: G_and_dfs_graph(1))
  hence p_good_path:"vwalk_bet (dfs.Graph.digraph_abs G) (hd p) p (last p) 
           \<or> (p = [hd p] \<and> hd p = last p)" "(hd p) \<in> t_set S"
    "(last p) \<in> t_set T" 
    using dfs_result(2) new_path_old_path[of "(rev (stack dfs_final))"] 
         vwalk_bet_nonempty_vwalk(3,4)[of "dfs.Graph.digraph_abs G"] 
   by( all \<open>cases p rule: vwalk_arcs.cases\<close>) fastforce+
  moreover have " (\<nexists> p' u' v'. (vwalk_bet (dfs.Graph.digraph_abs G) u' p' v' 
                                  \<or> (p' = [u'] \<and> u' = v'))
        \<and> u' \<in> t_set S \<and> v' \<in> t_set T \<and> length p' < length p)"
  proof(rule ccontr, goal_cases)
    case 1
    then obtain p' u' v' where p'_prop: "vwalk_bet(dfs.Graph.digraph_abs G) u'  p' v' \<or> (p' = [u'] \<and> u' = v')"
      "length p' < length p"  "u' \<in> t_set S" "v' \<in> t_set T"by auto
    hence "vwalk_bet (dfs.Graph.digraph_abs G') s ([s]@p'@[t]) t"
      using old_path_new_path p_good_path(2) p_good_path(3) by auto
    hence "vwalk_bet (G.digraph_abs G') s ([s]@p'@[t]) t"
      by (simp add: G_and_dfs_graph(1))
    hence valk_G'_p:"vwalk_bet (G.digraph_abs G') s ([s]@p'@[t]) t"
      by simp
    have s_in_srcs:"s \<in> t_set srcs"
      by (simp add: srcs_are)
    hence t_no_in_srcs: "t \<notin> t_set srcs" 
      using s_and_t(3) srcs_are by auto
    have "length (rev (stack dfs_final)) \<le> length ([s]@p'@[t]) "
      using bfs.parent_path_cheaper[OF bfs_axiom[OF dfs_result(3)] s_in_srcs valk_G'_p t_no_in_srcs big_vwalk ]
      by simp
    thus False 
      using dfs_result(2) p'_prop(2) by force
  qed
  ultimately show ?thesis by auto
qed

lemmas find_path = find_path1 find_path2

lemma  find_path2_weak: 
  assumes"find_path = Some p"
  shows  "\<exists> u v. (vwalk_bet (dfs.Graph.digraph_abs G) u p v \<or> (p = [u] \<and> u = v)) \<and> u \<in> t_set S 
                   \<and> v \<in> t_set T \<and>
                  (\<nexists> p'. (vwalk_bet (dfs.Graph.digraph_abs G) u p' v \<or> (p' = [u] \<and> u = v)) \<and> length p' < length p)"
  using find_path2[OF assms] 
  by metis

lemmas find_path_weak = find_path1 find_path2_weak
end
end

end
(*
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
*)
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