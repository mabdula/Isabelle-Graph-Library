theory Graphs_Matroids_Encoding
  imports Directed_Set_Graphs.Pair_Graph_U_Specs Matroids_Greedy.Indep_System_Matroids_Specs
begin


locale Graphs_Matroids_Encoding =
  pair_graph_u: Pair_Graph_U_Specs where lookup = lookup +
  matroid: Matroid_Specs where set_insert = set_insert and set_of_sets_isin = set_of_sets_isin
  for lookup :: "'adjmap \<Rightarrow> ('v::linorder) \<Rightarrow> 'vset option" and set_insert :: "('e::linorder) \<Rightarrow> 's \<Rightarrow> 's" and
    set_of_sets_isin :: "'t \<Rightarrow> 's \<Rightarrow> bool" and adjmap_fold :: "'adjmap \<Rightarrow> ('v \<Rightarrow> 'vset \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> 's \<Rightarrow> 's" and
    vset_fold :: "'vset \<Rightarrow> ('v \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> 's \<Rightarrow> 's" and set_fold_adjmap :: "'s \<Rightarrow> ('e \<Rightarrow> 'adjmap \<Rightarrow> 'adjmap) \<Rightarrow> 'adjmap \<Rightarrow> 'adjmap" and
    set_fold_vset :: "'s \<Rightarrow> ('e \<Rightarrow> 'vset \<Rightarrow> 'vset) \<Rightarrow> 'vset \<Rightarrow> 'vset" +
  fixes v1_of :: "'e \<Rightarrow> 'v" and v2_of :: "'e \<Rightarrow> 'v" and edge_of :: "'v \<Rightarrow> 'v \<Rightarrow> 'e" and c :: "('v set) \<Rightarrow> rat" and c' :: "'e \<Rightarrow> rat"
begin

(* TODO: Additional axioms/invariants necessary for proving properties *)

(* Iterate through graph itself, then through neighbourhood in nested fashion  *)
fun graph_to_edges :: "'adjmap \<Rightarrow> 's" where
  "graph_to_edges G =
    adjmap_fold G 
    (\<lambda>u N E. union E (vset_fold N 
        (\<lambda>v E. (let e = (edge_of u v)
                in (if \<not>(set_isin E e) then set_insert e E else E))) set_empty))
    set_empty"

(* Iterate through all edges, just use add_edge and v1_of, v2_of to build a graph, make
sure every edge is added symmetrically *)
fun edges_to_graph :: "'s \<Rightarrow> 'adjmap" where
  "edges_to_graph E =
    set_fold_adjmap E
    (\<lambda>e G. pair_graph_u.add_edge (pair_graph_u.add_edge G (v1_of e) (v2_of e)) (v2_of e) (v1_of e))
    empty"

fun edges_to_vertices :: "'s \<Rightarrow> 'vset" where
  "edges_to_vertices E = 
    set_fold_vset E
    (\<lambda>e N. if isin N (v1_of e)
           then (if isin N (v2_of e) then N else insert (v2_of e) N)
           else (if isin N (v2_of e) then insert (v1_of e) N else insert (v1_of e) (insert (v2_of e) N)))
    vset_empty"
end

locale Graphs_Matroids_Encoding_Proofs =
Graphs_Matroids_Encoding +
assumes adjmap_fold: "\<And> G S f. adjmap_inv G \<Longrightarrow> \<exists> xs. distinct xs \<and> set xs = dom (lookup G) \<and>
                                 adjmap_fold G f S = foldr (\<lambda> x acc. f x (the (lookup G x)) acc) xs S "
and set_fold_adjmap: "\<And> G S f.  set_inv S \<Longrightarrow> \<exists> xs. distinct xs \<and> set xs = to_set S \<and>
                                 set_fold_adjmap S f G = foldr f xs G"
and vset_fold: "\<And> V f S. vset_inv V \<Longrightarrow> \<exists> xs. distinct xs \<and> set xs = t_set V \<and>
                                    vset_fold V f S = foldr f xs S"
and set_fold_vset: "\<And>V f S. set_inv S \<Longrightarrow> \<exists> xs. distinct xs \<and> set xs = to_set S \<and>
                                 set_fold_vset S f V = foldr f xs V"
and finite_v_sets: "pair_graph_u.finite_vsets"
and v1_never_v2:"\<And> e. v1_of e \<noteq> v2_of e"
and v1_of_edge_of: "x \<noteq> y \<Longrightarrow> v1_of (edge_of x y) = x \<or> v1_of (edge_of x y) = y"
and v2_of_edge_of: "x \<noteq> y \<Longrightarrow> v2_of (edge_of x y) = x \<or> v2_of (edge_of x y) = y"
begin
(* Correctness properties *)

lemma x_not_y_edge_of: "x \<noteq> y \<Longrightarrow> v2_of (edge_of x y) = x \<Longrightarrow>  v1_of (edge_of x y) = y"
                       "x \<noteq> y \<Longrightarrow> v2_of (edge_of x y) = y \<Longrightarrow>  v1_of (edge_of x y) = x"
                       "x \<noteq> y \<Longrightarrow> v1_of (edge_of x y) = x \<Longrightarrow>  v2_of (edge_of x y) = y"
                       "x \<noteq> y \<Longrightarrow> v1_of (edge_of x y) = y \<Longrightarrow>  v2_of (edge_of x y) = x"
                       "x \<noteq> y \<Longrightarrow> v2_of (edge_of x y) = x \<longleftrightarrow>  v1_of (edge_of x y) = y"
  using v1_never_v2 v1_of_edge_of v2_of_edge_of by metis+

lemma pair_graph_u_invar_empty: "pair_graph_u.pair_graph_u_invar \<emptyset>\<^sub>G" 
proof-
  have " pair_graph_u.graph_inv \<emptyset>\<^sub>G"
    by (simp add: pair_graph_u.adjmap.invar_empty pair_graph_u.adjmap.map_empty pair_graph_u.graph_inv_def)
  moreover have "pair_graph_u.finite_graph \<emptyset>\<^sub>G"
    by (simp add: pair_graph_u.adjmap.map_empty pair_graph_u.finite_graph_def)
  ultimately show ?thesis
    using finite_v_sets 
    by (unfold pair_graph_u.pair_graph_u_invar_def )
       (simp add: pair_graph_u.adjmap.map_empty pair_graph_u.neighbourhood_def 
        pair_graph_u.vset.set.invar_empty pair_graph_u.vset.set.set_empty pair_graph_u.vset.set.set_isin)
qed

lemma  vset_fold_invar_pres_and_vs: assumes"vset_inv V" 
  shows "set_inv (vset_fold V
            (\<lambda>v E. let e = edge_of a v in if \<not> set_isin E e then set_insert e E else E) set_empty)" (is ?goal1)
     and   "to_set (vset_fold V
            (\<lambda>v E. let e = edge_of a v in if \<not> set_isin E e then set_insert e E else E) set_empty) =
         {edge_of a v | v. v \<in> t_set V}" (is ?goal2)
  proof-
    obtain xs where xs_prop: "distinct xs" "set xs = [V]\<^sub>s"
     "vset_fold V (\<lambda>v E. let e = edge_of a v in if \<not> set_isin E e then set_insert e E else E) set_empty =
     foldr (\<lambda>v E. let e = edge_of a v in if \<not> set_isin E e then set_insert e E else E) xs set_empty"
   using vset_fold[OF assms, of _ set_empty]
   by auto
  have set_inv_fold:"set_inv (foldr (\<lambda>v E. let e = edge_of a v in if \<not> set_isin E e then set_insert e E else E) xs set_empty)" for xs
   by(induction xs)
     (auto simp add: matroid.set.invar_empty Let_def split: if_split  intro: matroid.set.invar_insert)
  show ?goal1 
    by(auto intro: set_inv_fold simp add: xs_prop(3))
  show ?goal2
    unfolding xs_prop(3) xs_prop(2)[symmetric]
  proof(induction xs)
    case Nil
    then show ?case by (simp add: matroid.set.set_empty)
  next
    case (Cons a xs)
    show ?case 
      by(subst foldr.simps, subst o_apply, subst Let_def)
        (auto simp add: matroid.set.set_isin[OF set_inv_fold] set_inv_fold  Cons  matroid.set.set_insert)
  qed
qed

lemmas vset_fold_invar_pres = vset_fold_invar_pres_and_vs(1)

lemma P_of_ifE: "P (if b then x else y) \<Longrightarrow> (b \<Longrightarrow> P x \<Longrightarrow> Q) \<Longrightarrow> (\<not>b \<Longrightarrow> P y \<Longrightarrow> Q) \<Longrightarrow> Q"
  by(cases b) auto

lemma graph_invar_imp_edges_invar_and_abs:
  assumes "pair_graph_u.pair_graph_u_invar G" shows "set_inv (graph_to_edges G)"
"to_set (graph_to_edges G)  =
    (\<lambda> e. edge_of (fst e) (snd e))` [G]\<^sub>g"
     "(\<lambda>e. (v1_of e, v2_of e)) ` to_set (graph_to_edges G) \<union>
    (\<lambda>e. (v2_of e, v1_of e)) ` to_set (graph_to_edges G) = [G]\<^sub>g"
proof-
  define f where "f = (\<lambda>u N E. union E (vset_fold N 
        (\<lambda>v E. (let e = (edge_of u v)
                in (if \<not>(set_isin E e) then set_insert e E else E))) set_empty))"
  obtain xs where xs_prop:" distinct xs" "set xs = dom (lookup G)"
                                 "adjmap_fold G f set_empty = foldr (\<lambda> x acc. f x (the (lookup G x)) acc) xs set_empty" 
    using assms adjmap_fold[of G f set_empty]
    by(unfold graph_to_edges.simps pair_graph_u.pair_graph_u_invar_def pair_graph_u.graph_inv_def f_def)
      blast
  have vset_inv_a:"a \<in> dom (lookup G)  \<Longrightarrow> vset_inv (the (lookup G a))" for a
    using assms pair_graph_u.graph_inv_def pair_graph_u.invar_graph_inv by auto
  have set_inv_fold_f:"set xs \<subseteq> dom (lookup G) \<Longrightarrow>
             set_inv (foldr (\<lambda> x acc. f x (the (lookup G x)) acc) xs set_empty)" for xs
   unfolding f_def
    by(induction xs)
      (auto intro: matroid.set.invar_union vset_fold_invar_pres  vset_inv_a simp add: matroid.set.invar_empty)
  show "set_inv (graph_to_edges G)"
    using equalityD1[OF xs_prop(2)]  set_inv_fold_f
    by(auto simp add: graph_to_edges.simps xs_prop(3)[simplified f_def] f_def)
  have G_abs_is:"[G]\<^sub>g =  {(u, v) | u v.  v \<in>\<^sub>G the (lookup G u) \<and>  u \<in> set xs}"
  proof-
    have a1:"b \<in>\<^sub>G (if lookup G a = None then \<emptyset>\<^sub>N else the (lookup G a)) \<Longrightarrow> b \<in>\<^sub>G the (lookup G a)" for a b
      by(rule P_of_ifE[of _ "lookup G a = None" "\<emptyset>\<^sub>N" "the (lookup G a)"])
        (simp add: pair_graph_u.vset.emptyD(3) 
              pair_graph_u.vset.set.invar_empty pair_graph_u.vset.set.set_isin)+
    have a2:"b \<in>\<^sub>G (if lookup G a = None then \<emptyset>\<^sub>N else the (lookup G a)) \<Longrightarrow> \<exists>y. lookup G a = Some y" for a b
      by(rule P_of_ifE[of _ "lookup G a = None" "\<emptyset>\<^sub>N" "the (lookup G a)"])
      (simp add: pair_graph_u.vset.emptyD(3) pair_graph_u.vset.set.invar_empty
                      pair_graph_u.vset.set.set_isin)+
    show ?thesis
    using xs_prop(2)
    by(auto split: option.split simp add:  pair_graph_u.digraph_abs_def pair_graph_u.neighbourhood_def option.case_eq_if intro: a1 a2)
qed
  define f' where "f' = (\<lambda> x acc. f x (the (lookup G x)) acc)"
  define g where "g = (\<lambda>u E. union E (vset_fold (the (lookup G u)) 
              (\<lambda>v E.  set_insert (edge_of u v) E ) set_empty))"
  have  a_dom_set_inv:"a \<in> dom (lookup G) 
    \<Longrightarrow> set_inv (vset_fold (the (lookup G a)) (\<lambda>v. set_insert (edge_of a v)) set_empty)" for a
  proof(goal_cases)
    case 1
    have vset_inv_a:"vset_inv (the (lookup G a))"
      using 1 vset_inv_a by auto
    obtain ys where ys_prop: "set ys = [the (lookup G a)]\<^sub>s"
          "vset_fold (the (lookup G a)) (\<lambda>v. set_insert (edge_of a v)) set_empty = foldr (\<lambda>v. set_insert (edge_of a v)) ys set_empty"
      using vset_fold[OF vset_inv_a, of _ set_empty] by auto
    have aaa: "set_inv (foldr (\<lambda>v. set_insert (edge_of a v)) ys set_empty)"
      by(induction ys)
        (auto intro: matroid.set.invar_insert simp add: matroid.set.invar_empty)
    thus ?case
      using ys_prop by simp
  qed
  have set_inv_fold_g:"set xs \<subseteq> dom (lookup G) \<Longrightarrow> set_inv (foldr g xs set_empty)" for xs
  proof(induction xs)
    case Nil
    then show ?case by (simp add: matroid.set.invar_empty)
  next
    case (Cons a xs)
    show ?case 
      using Cons(2) a_dom_set_inv[of a]
      by(simp, subst g_def)(auto intro!: Cons(1) matroid.set.invar_union simp add: Cons(2))
  qed
  have set_inv_fold_h:"set_inv (foldr (\<lambda>v. set_insert (h v)) ys set_empty)"  for h ys
    using matroid.set.invar_empty 
    by (induction ys)(auto simp add: matroid.set.invar_insert)
   have to_set_fold_h:"to_set (foldr (\<lambda>v. set_insert (h v)) ys set_empty) = 
         {h v | v. v \<in> set ys}" for ys h
      using matroid.set.set_empty 
      by(induction ys)(auto intro: simp add: matroid.set.set_insert set_inv_fold_h)
  have a_in_dom_coarse:"a \<in> dom (lookup G)  \<Longrightarrow>
       to_set
        (vset_fold (the (lookup G a))
          (\<lambda>v E. let e = edge_of a v in if \<not> set_isin E e then set_insert e E else E) set_empty) =
       to_set (vset_fold (the (lookup G a)) (\<lambda>v. set_insert (edge_of a v)) set_empty)" for a
  proof(goal_cases)
    case 1
    have vset_inv_a:"vset_inv (the (lookup G a))"
      using 1 vset_inv_a by auto
    obtain ys where ys_prop: "set ys = [the (lookup G a)]\<^sub>s"
          "vset_fold (the (lookup G a)) (\<lambda>v. set_insert (edge_of a v)) set_empty = foldr (\<lambda>v. set_insert (edge_of a v)) ys set_empty"
      using vset_fold[OF vset_inv_a, of _ set_empty] by auto
      show ?case 
        by(simp add: ys_prop to_set_fold_h vset_fold_invar_pres_and_vs(2)[OF vset_inv_a])
    qed
  have with_easier_g:"set xs \<subseteq> dom (lookup G) \<Longrightarrow> to_set (foldr f' xs set_empty) = to_set (foldr g xs set_empty)" for xs
    apply(induction xs, simp_all, subst g_def,subst f'_def,subst f_def)
    using f'_def set_inv_fold_f vset_fold_invar_pres vset_inv_a  set_inv_fold_g 
    by(auto intro!: cong[of "Set.union _" "Set.union _"] a_in_dom_coarse simp add:  matroid.set.set_union a_dom_set_inv)
  note set_inv_fold_f' = set_inv_fold_f[simplified f_def, simplified f'_def[simplified f_def, symmetric]]
  show goal2:"to_set (graph_to_edges G)  =
    (\<lambda> e. edge_of (fst e) (snd e))` [G]\<^sub>g "
    using equalityD1[OF xs_prop(2)] xs_prop(1)
    unfolding graph_to_edges.simps  xs_prop(3)[simplified f_def] G_abs_is f'_def[simplified f_def, symmetric]
              with_easier_g[OF equalityD1[OF xs_prop(2)]]
  proof(induction xs)
    case Nil
    then show ?case by (simp add: matroid.set.set_empty)
  next
    case (Cons x xs)
    have to_set_foldr_f'_unfold:"to_set (foldr g (x # xs) set_empty) = (to_set (foldr g xs set_empty) \<union>
     {edge_of x v |v. v \<in> [the (lookup G x)]\<^sub>s})"  
      using Cons.prems(1) set_inv_fold_g  a_dom_set_inv  a_in_dom_coarse vset_fold_invar_pres_and_vs(2)
          vset_inv_a by (simp, subst g_def,subst matroid.set.set_union) auto
    have set_eqs:"(\<lambda>e. edge_of (fst e) (snd e)) ` {(u, v) |u v. v \<in>\<^sub>G the (lookup G u) \<and> u \<in> set xs} \<union>
    {edge_of x v |v. v \<in> [the (lookup G x)]\<^sub>s} =
    (\<lambda>x. edge_of (fst x) (snd x)) `
    ({(u, v). v \<in>\<^sub>G the (lookup G u) \<and> u \<in> set xs} \<union> {(x, v) |v. v \<in>\<^sub>G the (lookup G x)})"
    proof(rule, all \<open>rule\<close>, goal_cases)
      case (1 e)
      show ?case 
      proof(cases rule: UnE[OF 1])
        case 1
        then show ?thesis by auto
      next
        case 2
        note two = this
        then obtain v where v_prop:"e = edge_of x v" "v \<in> [the (lookup G x)]\<^sub>s" by blast
        moreover hence "v \<in>\<^sub>G the (lookup G x)"
          using Cons.prems(1) pair_graph_u.vset.set.set_isin vset_inv_a by auto
        ultimately show ?thesis 
          by force
      qed
    next
      case (2 e)
      then obtain u v where uv_prop:"e = edge_of u v" 
           "(u, v) \<in> {(u, v). v \<in>\<^sub>G the (lookup G u) \<and> u \<in> set xs} \<union> {(x, v) |v. v \<in>\<^sub>G the (lookup G x)}"
        by auto
      show ?case
      proof(cases rule: UnE[OF uv_prop(2)])
        case 1
        hence "e \<in> (\<lambda>e. edge_of (fst e) (snd e)) ` {(u, v) |u v. v \<in>\<^sub>G the (lookup G u) \<and> u \<in> set xs}"
          using uv_prop(1) by force
        then show ?thesis by simp
      next
        case 2
        hence "v \<in>\<^sub>G the (lookup G x)" and u_is_x:"u = x"by auto
        hence "v \<in> [the (lookup G x)]\<^sub>s" 
          using Cons.prems(1) pair_graph_u.vset.set.set_isin vset_inv_a by force
        then show ?thesis
          using uv_prop(1) u_is_x by auto
      qed
    qed
    have lookup_Set_is: "{(u, v). v \<in>\<^sub>G the (lookup G u) \<and> (u = x \<or> u \<in> set xs)} = 
          {(u, v). v \<in>\<^sub>G the (lookup G u) \<and> ( u \<in> set xs)} \<union>
              {(x, v) | v. v \<in>\<^sub>G the (lookup G x)}"
      by auto
    show ?case
      apply(subst  to_set_foldr_f'_unfold)+
      apply(simp add: image_Un)
      apply(subst Cons(1))
      using Cons(2,3) apply (simp, simp)
      by(subst lookup_Set_is, rule set_eqs)
  qed
  show   "(\<lambda>e. (v1_of e, v2_of e)) ` to_set (graph_to_edges G) \<union>
    (\<lambda>e. (v2_of e, v1_of e)) ` to_set (graph_to_edges G) = [G]\<^sub>g"
    unfolding  goal2
  proof(rule, all \<open>rule\<close>, goal_cases)
    case (1 e)
    show ?case 
    proof(cases rule: UnE[OF 1])
      case 1
      then obtain d where d_prop:"d \<in> (\<lambda>e. edge_of (fst e) (snd e)) ` [G]\<^sub>g" "e = (v1_of d, v2_of d)" by auto
      then obtain e' where e'_prop:"e' \<in> [G]\<^sub>g" "d = edge_of (fst e') (snd e')"
        by auto
      have e_no_loop:"fst e' \<noteq> snd e'" 
        using dVsI'(1) e'_prop(1) pair_graph_u.digraph_abs_irreflexive[OF assms] 
        by(cases e') auto
      have "e = e' \<or> e = prod.swap e'"
        using  v1_never_v2[of d] e_no_loop  e'_prop(1) e'_prop(2)
        by(cases rule: disjE[OF v1_of_edge_of[OF  e_no_loop]],
            all \<open>cases rule: disjE[OF v2_of_edge_of[OF  e_no_loop]]\<close>)
           (auto simp add: d_prop(2)  prod.swap_def)
      then show ?thesis 
        using e'_prop(1) pair_graph_u.graph_abs_symmetric[OF assms]
        by (metis d_prop(2) swap_simp swap_swap)
    next
      case 2
      then obtain d where d_prop:"d \<in> (\<lambda>e. edge_of (fst e) (snd e)) ` [G]\<^sub>g" "e = (v2_of d, v1_of d)" by auto
      then obtain e' where e'_prop:"e' \<in> [G]\<^sub>g" "d = edge_of (fst e') (snd e')"
        by auto
      have e_no_loop:"fst e' \<noteq> snd e'" 
        using dVsI'(1) e'_prop(1) pair_graph_u.digraph_abs_irreflexive[OF assms] 
        by(cases e') auto
      have "e = e' \<or> e = prod.swap e'"
        using  v1_never_v2[of d] e_no_loop  e'_prop(1) e'_prop(2)
        by(cases rule: disjE[OF v1_of_edge_of[OF  e_no_loop]],
            all \<open>cases rule: disjE[OF v2_of_edge_of[OF  e_no_loop]]\<close>)
           (auto simp add: d_prop(2)  prod.swap_def)
      then show ?thesis 
        using e'_prop(1) pair_graph_u.graph_abs_symmetric[OF assms]
        by (metis d_prop(2) swap_simp swap_swap)
    qed
  next
    case (2 e)
    have no_loop:"fst e \<noteq> snd e" 
      using   dVsI'(1) 2 pair_graph_u.digraph_abs_irreflexive[OF assms] 
      by(cases e) auto
    show ?case 
      using "2" image_iff  no_loop x_not_y_edge_of(5)
      by(cases rule: disjE[OF v1_of_edge_of[OF no_loop]],
            all \<open>cases rule: disjE[OF v2_of_edge_of[OF no_loop]]\<close>) 
      fastforce+
  qed
qed

lemmas graph_invar_imp_edges_invar = graph_invar_imp_edges_invar_and_abs(1)

lemma edges_invar_imp_graph_invar:
  assumes "set_inv E" shows "pair_graph_u.pair_graph_u_invar (edges_to_graph E)"
proof-
  define f where "f = (\<lambda>e G. pair_graph_u.add_edge (pair_graph_u.add_edge G (v1_of e) (v2_of e)) (v2_of e) (v1_of e))"
  obtain xs where xs_prop:"distinct xs" "set xs = to_set E" "set_fold_adjmap E f \<emptyset>\<^sub>G = foldr f xs \<emptyset>\<^sub>G"
    using set_fold_adjmap[OF assms(1), of f empty]  by(auto simp add: f_def)
  show ?thesis
    unfolding edges_to_graph.simps f_def[symmetric]  xs_prop(3) 
    by(induction xs)
      (auto intro: pair_graph_u.pair_graph_u_invar_add_edge simp add: pair_graph_u_invar_empty v1_never_v2  f_def)
qed

lemma digraph_abs_of_edges_of_to_graph:
  assumes ys_prop: "set ys = to_set E" "set_fold_adjmap E g \<emptyset>\<^sub>G = foldr g ys \<emptyset>\<^sub>G" and
                g_def: "g = (\<lambda>e G. pair_graph_u.add_edge (pair_graph_u.add_edge G (v1_of e) (v2_of e)) (v2_of e) (v1_of e))" 
     shows  "[edges_to_graph E]\<^sub>g = (\<lambda> e. (v1_of e, v2_of e)) ` (to_set E) \<union> (\<lambda> e. (v2_of e, v1_of e)) ` (to_set E)"
proof-
  have graph_inv_fold_g:"pair_graph_u.graph_inv (foldr g ys \<emptyset>\<^sub>G)" for ys
    by(induction ys) 
      (auto intro!: pair_graph_u.adjmap_inv_insert simp add:  g_def pair_graph_u.graph_inv_empty)
  show ?thesis
    unfolding edges_to_graph.simps g_def[symmetric] ys_prop(2) ys_prop(1)[symmetric]
  proof(induction ys)
    case Nil
    then show ?case by(simp add: pair_graph_u.digraph_abs_empty)
  next
    case (Cons a ys)   
    then show ?case 
    apply simp
    apply(subst g_def)
    apply(subst pair_graph_u.digraph_abs_insert)
    apply(rule pair_graph_u.adjmap_inv_insert)
    apply(rule graph_inv_fold_g)
    apply(subst pair_graph_u.digraph_abs_insert)
      by(auto intro!: graph_inv_fold_g) 
  qed
qed
(*
lemma digraph_abs_of_edges_of_to_graph:
  assumes ys_prop: "set ys = to_set E" "set_fold_adjmap E g \<emptyset>\<^sub>G = foldr g ys \<emptyset>\<^sub>G" and
                g_def: "g = (\<lambda>e G. pair_graph_u.add_edge (pair_graph_u.add_edge G (v1_of e) (v2_of e)) (v2_of e) (v1_of e))" 
     shows  "(\<lambda> e. edge_of (fst e) (snd e)) ` [edges_to_graph E]\<^sub>g =  (to_set E)"
proof-
  have graph_inv_fold_g:"pair_graph_u.graph_inv (foldr g ys \<emptyset>\<^sub>G)" for ys
    by(induction ys) 
      (auto intro!: pair_graph_u.adjmap_inv_insert simp add:  g_def pair_graph_u.graph_inv_empty)
  show ?thesis
    unfolding edges_to_graph.simps g_def[symmetric] ys_prop(2) ys_prop(1)[symmetric]
  proof(induction ys)
    case Nil
    then show ?case by(simp add: pair_graph_u.digraph_abs_empty)
  next
    case (Cons a ys)   
    then show ?case 
    apply simp
    apply(subst g_def)
    apply(subst pair_graph_u.digraph_abs_insert)
    apply(rule pair_graph_u.adjmap_inv_insert)
    apply(rule graph_inv_fold_g)
    apply(subst pair_graph_u.digraph_abs_insert)
       apply(auto intro!: graph_inv_fold_g) 
      find_theorems v1_of
  qed
qed
*)
lemma dVs_of_edges_of_to_graph:
  assumes ys_prop: "set ys = to_set E" "set_fold_adjmap E g \<emptyset>\<^sub>G = foldr g ys \<emptyset>\<^sub>G" and
                g_def: "g =  (\<lambda>e G. pair_graph_u.add_edge (pair_graph_u.add_edge G (v1_of e) (v2_of e)) (v2_of e) (v1_of e))" 
              shows  "dVs [edges_to_graph E]\<^sub>g = v1_of ` (to_set E) \<union> v2_of ` (to_set E)"
 by(unfold digraph_abs_of_edges_of_to_graph[OF assms] dVs_def) blast

lemma edges_invar_imp_vertices_props:
  assumes "set_inv E"
  shows "vset_inv (edges_to_vertices E)"
    "t_set (edges_to_vertices E) = dVs (pair_graph_u.digraph_abs (edges_to_graph E))"
proof-
  define f where "f = (\<lambda>e N. if isin N (v1_of e)
           then (if isin N (v2_of e) then N else insert (v2_of e) N)
           else (if isin N (v2_of e) then insert (v1_of e) N else insert (v1_of e) (insert (v2_of e) N)))"
  obtain xs where xs_prop:"distinct xs" "set xs = to_set E" "set_fold_vset E f \<emptyset>\<^sub>N = foldr f xs \<emptyset>\<^sub>N"
    using  set_fold_vset[OF assms, of f vset_empty] by(auto simp add: f_def)
  have vset_inv_fold_f:"vset_inv (foldr f xs \<emptyset>\<^sub>N)" for xs
   by(induction xs)
      (auto split: if_split intro: pair_graph_u.vset.set.invar_insert simp add: f_def pair_graph_u.vset.set.invar_empty)
  thus "vset_inv (edges_to_vertices E)"
    by(simp add:  f_def[symmetric]  xs_prop(3))
  define g where "g =  (\<lambda>e G. pair_graph_u.add_edge (pair_graph_u.add_edge G (v1_of e) (v2_of e)) (v2_of e) (v1_of e))"
  obtain ys where ys_prop:" distinct ys" "set ys = to_set E" "set_fold_adjmap E g \<emptyset>\<^sub>G = foldr g ys \<emptyset>\<^sub>G"
    using set_fold_adjmap[OF assms, of g empty] by auto
  have graph_inv_fold_g:"pair_graph_u.graph_inv (foldr g ys \<emptyset>\<^sub>G)" for ys
    by(induction ys) 
      (auto intro!: pair_graph_u.adjmap_inv_insert simp add:  g_def pair_graph_u.graph_inv_empty)
  have "[edges_to_vertices E]\<^sub>s = v1_of ` (to_set E) \<union> v2_of ` (to_set E)"
    unfolding edges_to_vertices.simps  f_def[symmetric]  xs_prop(3) xs_prop(2)[symmetric]
    by(induction xs)
      (simp add: pair_graph_u.vset.emptyD(1),  simp, subst f_def, auto simp add: pair_graph_u.vset.set.set_isin vset_inv_fold_f  pair_graph_u.vset.set.set_insert
                       pair_graph_u.vset.set.invar_insert )
  moreover have "dVs [edges_to_graph E]\<^sub>g = v1_of ` (to_set E) \<union> v2_of ` (to_set E)"
    using dVs_of_edges_of_to_graph[OF ys_prop(2,3) g_def] by simp
  ultimately show "[edges_to_vertices E]\<^sub>s = dVs [edges_to_graph E]\<^sub>g"
    by simp
qed

lemma to_set_equal_imp_ugraph_abs_equal:
  assumes "set_inv X" "set_inv Y" "to_set X = to_set Y"
  shows "pair_graph_u.ugraph_abs (edges_to_graph X) = pair_graph_u.ugraph_abs (edges_to_graph Y)"
proof-
  define g where "g =  (\<lambda>e G. pair_graph_u.add_edge (pair_graph_u.add_edge G (v1_of e) (v2_of e)) (v2_of e) (v1_of e))" 
  obtain xs where xs_prop:" distinct xs" "set xs = to_set X" "set_fold_adjmap X g \<emptyset>\<^sub>G = foldr g xs \<emptyset>\<^sub>G"
    using set_fold_adjmap[OF assms(1), of g empty] by auto
  have X_vs_are:"[edges_to_graph X]\<^sub>g = (\<lambda>e. (v1_of e, v2_of e)) ` to_set X \<union> (\<lambda>e. (v2_of e, v1_of e)) ` to_set X"
    using  digraph_abs_of_edges_of_to_graph[OF xs_prop(2,3) g_def] by simp
  obtain ys where ys_prop:" distinct ys" "set ys = to_set Y" "set_fold_adjmap Y g \<emptyset>\<^sub>G = foldr g ys \<emptyset>\<^sub>G"
    using set_fold_adjmap[OF assms(2), of g empty] by auto
  have Y_vs_are:"[edges_to_graph Y]\<^sub>g = (\<lambda>e. (v1_of e, v2_of e)) ` to_set Y \<union> (\<lambda>e. (v2_of e, v1_of e)) ` to_set Y"
    using  digraph_abs_of_edges_of_to_graph[OF ys_prop(2,3) g_def] by simp
  show ?thesis
    using X_vs_are Y_vs_are assms(3) 
    by(auto simp add: pair_graph_u.ugraph_and_digraph_abs)
qed

lemma graph_to_edges_inverse:
  assumes "pair_graph_u.pair_graph_u_invar G" 
  shows"pair_graph_u.digraph_abs (edges_to_graph (graph_to_edges G)) = pair_graph_u.digraph_abs G"
proof-
  have set_inv_G:"set_inv (graph_to_edges G)"
    using assms graph_invar_imp_edges_invar by blast
  define g where "g = (\<lambda>e G. pair_graph_u.add_edge (pair_graph_u.add_edge G (v1_of e) (v2_of e)) (v2_of e) (v1_of e))"
    obtain xs where xs_prop:"distinct xs" "set xs = to_set (graph_to_edges G)" 
       "set_fold_adjmap (graph_to_edges G) g empty = foldr g xs empty"
      using set_fold_adjmap[OF  set_inv_G, of g empty] by blast 
  show ?thesis
    using graph_invar_imp_edges_invar_and_abs(3)[OF assms] 
    by (subst digraph_abs_of_edges_of_to_graph[OF xs_prop(2,3)  g_def])
qed

abbreviation "to_doubltn_set X \<equiv> (\<lambda>e. {v1_of e, v2_of e}) ` to_set X"

lemma dbltn_set_and_ugraph_abs:
  assumes "set_inv X"
  shows "to_doubltn_set X = pair_graph_u.ugraph_abs (edges_to_graph X)"
proof-
   define g where "g =  (\<lambda>e G. pair_graph_u.add_edge (pair_graph_u.add_edge G (v1_of e) (v2_of e)) (v2_of e) (v1_of e))" 
  obtain xs where xs_prop:" distinct xs" "set xs = to_set X" "set_fold_adjmap X g \<emptyset>\<^sub>G = foldr g xs \<emptyset>\<^sub>G"
    using set_fold_adjmap[OF assms(1), of g empty] by auto
  have X_vs_are:"[edges_to_graph X]\<^sub>g = (\<lambda>e. (v1_of e, v2_of e)) ` to_set X \<union> (\<lambda>e. (v2_of e, v1_of e)) ` to_set X"
    using  digraph_abs_of_edges_of_to_graph[OF xs_prop(2,3) g_def] by simp
  show ?thesis
    by(unfold pair_graph_u.ugraph_and_digraph_abs X_vs_are) auto
qed

lemma edges_to_graph_subset_imp_subset:
  assumes "set_inv X" "set_inv Y" "pair_graph_u.ugraph_abs (edges_to_graph X) \<subseteq> pair_graph_u.ugraph_abs (edges_to_graph Y)"
  shows "to_doubltn_set X \<subseteq> to_doubltn_set Y"
  using assms(1) assms(2) assms(3) dbltn_set_and_ugraph_abs by presburger

lemma subset_imp_edges_to_graph_subset:
  assumes "set_inv X" "set_inv Y" "to_doubltn_set X \<subseteq> to_doubltn_set Y"
  shows "pair_graph_u.ugraph_abs (edges_to_graph X) \<subseteq> pair_graph_u.ugraph_abs (edges_to_graph Y)"
  using assms(1) assms(2) assms(3) dbltn_set_and_ugraph_abs by auto

lemma subset_iff_graph_to_edges_subset:
  assumes "set_inv X" "set_inv Y"
  shows "(to_doubltn_set X \<subseteq> to_doubltn_set Y) = (pair_graph_u.ugraph_abs (edges_to_graph X) \<subseteq> pair_graph_u.ugraph_abs (edges_to_graph Y))"
  using edges_to_graph_subset_imp_subset[OF assms] subset_imp_edges_to_graph_subset[OF assms]
    matroid.set.set_subseteq[OF assms] by blast

(*
lemma diff_graph_to_edges:
  assumes "set_inv X" "set_inv Y"
  shows "diff X Y = pair_graph_u.ugraph_abs (edges_to_graph X) - pair_graph_u.ugraph_abs (edges_to_graph Y)"
  sorry
*)

lemma card_graph_to_edges:
  assumes "set_inv X"
  shows "card (to_doubltn_set X) = card (pair_graph_u.ugraph_abs (edges_to_graph X))"
  by (simp add: assms dbltn_set_and_ugraph_abs)
(*
lemma costs_transformation:
  "sum c' (to_set E') \<le> sum c' (to_set E'') \<Longrightarrow>
   sum c (pair_graph_u.ugraph_abs (Kruskal_E_to_G E')) \<ge>
    sum c (pair_graph_u.ugraph_abs (Kruskal_E_to_G E''))"
      sorry
*)

end


end