theory BFS_Refinement
  imports Graph_Algorithms_Dev.BFS_3 BFS_Subprocedures Parent_Array Directed_Set_Graphs.Pair_Graph_Imperative
 "HOL-Imperative_HOL.Imperative_HOL" "HOL-Library.IArray" 
  Imperative.Array_Range_Iteration Data_Structures.Fixed_Univ_Set_Specs_Imp
  Data_Structures.Iterable_Set_Specs_Imp
begin

provenance ai


named_theorems bfs_heap_rules "Heap rules for breadth-first search"


record ('imp_dist, 'imp_vis, 'imp_cf, 'imp_par) BFS_state_imp =
     dists:: "'imp_dist" current:: "'imp_cf" visited:: "'imp_vis" current_dist::nat
     parent:: "'imp_par"

locale BFS_Imperative_spec = 
fixes imp_src_to_cf::"'imp_src \<Rightarrow> 'imp_cf Heap"
and set_srcs_visited::" 'imp_vis \<Rightarrow> 'imp_src \<Rightarrow> 'imp_vis Heap"
and next_frontier_current_parents_imp::
      "'imp_cf \<Rightarrow> 'imp_vis \<Rightarrow> 'imp_par \<Rightarrow> ('imp_cf \<times> 'imp_vis \<times> 'imp_par) Heap"
and imp_cf_is_empty::"'imp_cf \<Rightarrow> bool Heap"
and in_vis::"'ver::heap \<Rightarrow> 'imp_vis \<Rightarrow> bool Heap"
and set_all_dists_in_front_imp::"'imp_dist \<Rightarrow> 'imp_cf \<Rightarrow> nat \<Rightarrow> 'imp_dist Heap"
and parent_init_imp::"'imp_src \<Rightarrow> 'imp_par \<Rightarrow> unit Heap"
begin

partial_function \<^marker>\<open>provenance ai_human\<close> (heap) BFS_par_imp::
  "('imp_dist, 'imp_vis, 'imp_cf, 'imp_par) BFS_state_imp
     \<Rightarrow> ('imp_dist, 'imp_vis, 'imp_cf, 'imp_par) BFS_state_imp Heap"
  where 
 "BFS_par_imp state = 
   do { b \<leftarrow> imp_cf_is_empty (current state);
       if b then Heap_Monad.return state
       else do{ (current', visited', parent') \<leftarrow>
                  next_frontier_current_parents_imp (current state) (visited state) (parent state);
               let d = current_dist state;
               dist' \<leftarrow> set_all_dists_in_front_imp (dists state) current' (Suc d);
               BFS_par_imp (state \<lparr>dists:= dist', visited := visited', current := current',
                                 current_dist := Suc d, parent := parent'\<rparr>)}}"

definition "initial_state_imp empty_vis src_imp imp_some_dist imp_some_par =  
  do {v \<leftarrow> set_srcs_visited empty_vis src_imp;
      parent_init_imp src_imp imp_some_par;
      cf \<leftarrow> imp_src_to_cf src_imp;
      dists \<leftarrow> set_all_dists_in_front_imp  imp_some_dist cf 0;
      return \<lparr>dists = dists, current = cf, visited = v, current_dist = 0, parent = imp_some_par\<rparr>}"

definition "check_reachable empty_vis src_imp imp_some_dist imp_some_par t =
    do {init \<leftarrow> initial_state_imp empty_vis src_imp imp_some_dist imp_some_par;
        final \<leftarrow> BFS_par_imp init;
        in_vis t (visited final)}"

definition "visited_dists_parents_imp empty_vis src_imp imp_some_dist imp_some_par =
    do {init \<leftarrow> initial_state_imp empty_vis src_imp imp_some_dist imp_some_par;
        final \<leftarrow> BFS_par_imp init;
        return (visited final, dists final, parent final)}"

end

text \<open>The parent map is refined by @{term imp_par_assn}. It is initialised in place with the
      sources as roots (@{locale Parent_Map_Spec_init_imp}), and paths are read off by
      @{term get_path_imp} (@{locale Parent_Map_Spec_static_imp}).\<close>

locale BFS_Imperative = 
 BFS_3.BFS_distance_parents  where expand_tree = expand_tree and insert = insert and some_dist = some_dist
  and next_frontier_current_parents = next_frontier_current_parents +
 BFS_Imperative_spec where  imp_src_to_cf = imp_src_to_cf
  and in_vis = in_vis and set_all_dists_in_front_imp = set_all_dists_in_front_imp
  and next_frontier_current_parents_imp = next_frontier_current_parents_imp +
 par_static: Parent_Map_Spec_static_imp where U = U and to_dir_graph = parent_abstract
  and get_path = get_path and invar = parent_invar and roots = roots
  and parent_assn = imp_par_assn and get_path_imp = get_path_imp +
 par_init: Parent_Map_Spec_init_imp where U = U and to_dir_graph = parent_abstract
  and invar = parent_invar and roots = roots and vset_abstract = t_set and init = parent_init
  and vset_invar = vset_inv and parent_assn = imp_par_assn and vset_assn = imp_src_assn
  and init_imp = parent_init_imp
 for  imp_src_to_cf :: "'imp_src \<Rightarrow> 'imp_cf Heap"
  and expand_tree::"'adjmap \<Rightarrow> 'vset \<Rightarrow> 'vset \<Rightarrow> 'adjmap"
  and insert :: "'ver::heap \<Rightarrow> 'vset \<Rightarrow> 'vset" 
  and in_vis::"'ver \<Rightarrow> 'imp_vis \<Rightarrow> bool Heap"
  and some_dist::"'dist" and set_all_dists_in_front_imp::"'imp_dist \<Rightarrow> 'imp_cf \<Rightarrow> nat \<Rightarrow> 'imp_dist Heap"
  and next_frontier_current_parents :: "'vset \<Rightarrow> 'vset \<Rightarrow> 'par \<Rightarrow> 'vset \<times> 'vset \<times> 'par"
  and next_frontier_current_parents_imp ::
      "'imp_cf \<Rightarrow> 'imp_vis \<Rightarrow> 'imp_par \<Rightarrow> ('imp_cf \<times> 'imp_vis \<times> 'imp_par) Heap"
  and get_path_imp :: "'imp_par \<Rightarrow> 'ver array \<Rightarrow> nat \<Rightarrow> 'ver \<Rightarrow> nat Heap"
  and imp_src_assn::"'vset \<Rightarrow> 'imp_src \<Rightarrow> assn"
  and imp_par_assn::"'par \<Rightarrow> 'imp_par \<Rightarrow> assn" +
fixes  G_imp::"'imp_G"
 and graph_assn::"'adjmap \<Rightarrow> 'imp_G \<Rightarrow> assn"
 and imp_cf_assn::"'vset \<Rightarrow> 'imp_cf \<Rightarrow> assn"
 and imp_vis_assn::"'vset \<Rightarrow> 'imp_vis \<Rightarrow> assn"
 and imp_dist_assn::"'dist \<Rightarrow> 'imp_dist \<Rightarrow> assn"
assumes imp_sf_is_empty: "\<And> S Si. <imp_cf_assn S Si> imp_cf_is_empty Si 
                       <\<lambda> b. imp_cf_assn S Si * \<up>(b \<longleftrightarrow> S = \<emptyset>\<^sub>N)>"
 and imp_src_to_cf: "\<And> S Si. <imp_src_assn S Si> imp_src_to_cf Si 
                      <\<lambda> r. imp_cf_assn S r>"
 and set_srcs_visited: 
  "\<And> S Si. 
    <imp_src_assn S Si * imp_vis_assn vset_empty empty_vis> set_srcs_visited empty_vis Si 
           <\<lambda> r. imp_vis_assn S r * imp_src_assn S Si>"
 and next_frontier_current_parents_imp:  "\<And> cf imp_cf vis imp_vis par imp_par.
    \<lbrakk>vset_inv2 cf; vset_inv vis; t_set cf \<subseteq> t_set vis; t_set vis \<subseteq> dVs (Graph.digraph_abs G);
     parent_invar par; dVs (parent_abstract par) \<union> roots par = t_set vis\<rbrakk> \<Longrightarrow>
    <imp_cf_assn cf imp_cf * imp_vis_assn vis imp_vis * imp_par_assn par imp_par * graph_assn G G_imp>
    next_frontier_current_parents_imp imp_cf imp_vis imp_par
    <\<lambda> (r1, r2, r3). imp_cf_assn (fst (next_frontier_current_parents cf vis par)) r1 * 
                 imp_vis_assn (fst (snd (next_frontier_current_parents cf vis par))) r2 *
                 imp_par_assn (snd (snd (next_frontier_current_parents cf vis par))) r3 *
                 graph_assn G G_imp>"
and set_all_dists_in_front_imp:
    "\<And> d id. <imp_dist_assn d id * imp_cf_assn cf cfi> set_all_dists_in_front_imp id cfi n
            <\<lambda> r. imp_dist_assn (set_all_dists_in_set d cf n) r * imp_cf_assn cf cfi>"
and in_vis_rule: "\<And>vis visi s. s \<in> dVs (Graph.digraph_abs G) \<Longrightarrow>
     <imp_vis_assn vis visi> in_vis s visi <\<lambda> r. imp_vis_assn vis visi * \<up> (r \<longleftrightarrow> isin vis s)>"
begin

text \<open>The invariant of the rounds needed by the imperative round: the frontier is part of the
      visited set, and the vertices of the parent map are exactly the visited ones.\<close>

definition "round_inv cf vis par \<longleftrightarrow>
   vset_inv2 cf \<and> vset_inv vis \<and> t_set cf \<subseteq> t_set vis \<and> t_set vis \<subseteq> dVs (Graph.digraph_abs G) \<and>
   parent_invar par \<and> dVs (parent_abstract par) \<union> roots par = t_set vis"

lemma round_inv_step:
  assumes BFS_axiom "round_inv cf vis par"
          "next_frontier_current_parents cf vis par = (cf', vis', par')"
  shows "round_inv cf' vis' par'"
proof-
  have pre: "vset_inv2 cf" "vset_inv vis" "t_set cf \<subseteq> t_set vis"
       "t_set vis \<subseteq> dVs (Graph.digraph_abs G)" "parent_invar par"
       "dVs (parent_abstract par) \<union> roots par = t_set vis"
    using assms(2) by (auto simp: round_inv_def)
  note nf = next_frontier_current_parents[OF pre(1,2) graph_inv(1)[OF assms(1)] pre(3-6) assms(3)]
  note front = next_frontier[OF pre(1,2) graph_inv(1)[OF assms(1)] pre(3) nf(1) pre(4)]
  note vis = next_vis[OF pre(1,2) graph_inv(1)[OF assms(1)] pre(3) nf(1) pre(4)]
  obtain E where E: "parent_abstract par' = parent_abstract par \<union> E"
    "\<forall>x \<in> t_set cf'. \<exists>x' \<in> t_set cf. (x', x) \<in> Graph.digraph_abs G \<and> (x, x') \<in> E"
    "\<forall>x x'. (x, x') \<in> E \<longrightarrow>
      x \<in> t_set cf' \<and> x' \<in> t_set cf \<and> (x', x) \<in> Graph.digraph_abs G"
    using nf(3) by blast
  have "t_set cf' \<subseteq> dVs E"
    using E(2) by (blast intro: dVsI(1))
  moreover have "dVs E \<subseteq> t_set cf' \<union> t_set cf"
    using E(3) by (auto simp: dVs_def)
  ultimately have vertices: "t_set vis \<union> dVs E = t_set vis \<union> t_set cf'"
    using pre(3) by blast
  have "dVs (parent_abstract par') \<union> roots par' =
      (dVs (parent_abstract par) \<union> roots par) \<union> dVs E"
    unfolding E(1) nf(4) dVs_union_distr by (simp only: Un_ac)
  then have "dVs (parent_abstract par') \<union> roots par' = t_set vis'"
    by (simp only: pre(6) vertices vis(2))
  moreover have "t_set cf' \<subseteq> dVs (Graph.digraph_abs G)"
    using front(2) by (auto simp: Pair_Graph.neighbourhood_def dVs_def)
  ultimately show ?thesis
    using nf(2) front(1) vis(1,2) pre(4) by (auto simp: round_inv_def)
qed

lemma \<^marker>\<open>provenance ai_human\<close> next_frontier_current_parents_imp_round[bfs_heap_rules]:
  "round_inv cf vis par \<Longrightarrow>
    <imp_cf_assn cf imp_cf * imp_vis_assn vis imp_vis * imp_par_assn par imp_par * graph_assn G G_imp>
    next_frontier_current_parents_imp imp_cf imp_vis imp_par
    <\<lambda> (r1, r2, r3). imp_cf_assn (fst (next_frontier_current_parents cf vis par)) r1 * 
                 imp_vis_assn (fst (snd (next_frontier_current_parents cf vis par))) r2 *
                 imp_par_assn (snd (snd (next_frontier_current_parents cf vis par))) r3 *
                 graph_assn G G_imp>"
  unfolding round_inv_def by (elim conjE) (rule next_frontier_current_parents_imp)

definition "state_assn (s::('dist, 'vset, 'par) BFS_par_state)
    (imp_s::('imp_dist, 'imp_vis, 'imp_cf, 'imp_par) BFS_state_imp) = 
  (imp_vis_assn (BFS_dist_state.visited s) (BFS_state_imp.visited imp_s) *
   imp_cf_assn (BFS_dist_state.current s) (BFS_state_imp.current imp_s)*
   imp_dist_assn (BFS_dist_state.dists s) (BFS_state_imp.dists imp_s) *
   imp_par_assn (BFS_par_state.parent s) (BFS_state_imp.parent imp_s) *
    \<up> (BFS_dist_state.current_dist s = BFS_state_imp.current_dist imp_s \<and>
       round_inv (BFS_dist_state.current s) (BFS_dist_state.visited s) (BFS_par_state.parent s)))"

lemma \<^marker>\<open>provenance ai_human\<close> BFS_refine[bfs_heap_rules]:
  assumes BFS_axiom
  shows
  "<graph_assn G G_imp * state_assn s s_imp >
  BFS_par_imp s_imp 
  <\<lambda> s_imp'. graph_assn G G_imp * state_assn (BFS_par_impl s) s_imp'>"
proof(induction arbitrary: s s_imp rule: BFS_par_imp.fixp_induct, goal_cases)
  case 1
  then show ?case 
    by auto
next
  case (2 s s_imp)
  then show ?case 
    by simp
next
  case (3 f s s_imp)

  note IH = 3(1)[of 
     "\<lparr>BFS_dist_state.dists = dists, current = current, visited = visited,
       BFS_dist_state.current_dist = n, BFS_par_state.parent = par\<rparr>"
     "\<lparr>BFS_state_imp.dists = imp_dists, current = imp_current, visited = imp_visited,
       BFS_state_imp.current_dist = n, parent = imp_par\<rparr>"
     for imp_dists imp_current imp_visited imp_par dists current visited par n] 

  note IH[sep_heap_rules] = IH[unfolded state_assn_def, simplified, rule_format]

  show ?case
    apply(cases s, cases s_imp)
    subgoal for dists current visited current_dist par imp_dists imp_current imp_visited
                imp_current_dist imp_par
      (*<*)apply (rewrite in "<_> _ <\<hole>>" BFS_par_impl.simps)(*>*)
      using next_frontier_current_parents_imp_round IH  imp_sf_is_empty set_all_dists_in_front_imp
            round_inv_step[OF assms]
      apply(auto split!: if_split prod.split simp add: state_assn_def Let_def mod_pure_star_dist)
      by sep_auto
    done
qed

lemma \<^marker>\<open>provenance ai_human\<close> initial_refine[bfs_heap_rules]:
  assumes BFS_axiom
  shows
 "<imp_vis_assn vset_empty empty_vis* imp_src_assn srcs srcs_imp * imp_dist_assn some_dist imp_some_dist
   * imp_par_assn p imp_some_par>
  initial_state_imp empty_vis srcs_imp imp_some_dist imp_some_par
 <\<lambda> si. state_assn initial_par_state si>"
proof-
  have srcs: "vset_inv srcs" "t_set srcs \<subseteq> U"
    using vset_inv2[OF srcs_invar(2)[OF assms]] order.trans[OF srcs_in_G[OF assms] G_in_U] .
  note init_imp = par_init.init_rule[OF srcs]
  have ri: "round_inv srcs srcs (parent_init srcs)"
    using init[OF srcs] srcs_invar(2)[OF assms] srcs_in_G[OF assms] srcs(1)
    unfolding round_inv_def by simp
  show ?thesis
    apply(auto simp add: initial_par_state_def state_assn_def initial_state_imp_def)
    using imp_src_to_cf set_all_dists_in_front_imp set_srcs_visited init_imp ri
    by sep_auto
qed

lemma \<^marker>\<open>provenance ai_human\<close> BFS_program_behaviour[bfs_heap_rules]:
  "BFS_axiom \<Longrightarrow>
   <imp_vis_assn vset_empty empty_vis * imp_src_assn srcs srcs_imp * imp_dist_assn some_dist imp_some_dist
    * imp_par_assn p imp_some_par * graph_assn G G_imp>
   do { si \<leftarrow> initial_state_imp empty_vis srcs_imp imp_some_dist imp_some_par;
        BFS_par_imp si }
   < \<lambda> si'. state_assn (BFS_par_impl initial_par_state) si' * graph_assn G G_imp>"
  by (sep_auto heap: bfs_heap_rules simp: state_assn_def)

lemma \<^marker>\<open>provenance ai_human\<close> check_reachable_rule[bfs_heap_rules]:
  "\<lbrakk>BFS_axiom;
    t \<in> dVs (Graph.digraph_abs G)\<rbrakk> \<Longrightarrow>
   <imp_vis_assn vset_empty empty_vis * imp_src_assn srcs srcs_imp * imp_dist_assn some_dist imp_some_dist
   * imp_par_assn p imp_some_par * graph_assn G G_imp> 
   check_reachable empty_vis srcs_imp imp_some_dist imp_some_par t
  <\<lambda> b.  graph_assn G G_imp *
      \<up> (b \<longleftrightarrow> isin (BFS_dist_state.visited (BFS_par_impl initial_par_state)) t)>"
  unfolding check_reachable_def
  by (sep_auto heap: bfs_heap_rules in_vis_rule simp: state_assn_def)

lemma \<^marker>\<open>provenance ai_human\<close> visited_dists_parents_imp_rule[bfs_heap_rules]:
  "BFS_axiom \<Longrightarrow>
   <imp_vis_assn vset_empty empty_vis * imp_src_assn srcs srcs_imp * imp_dist_assn some_dist imp_some_dist
   * imp_par_assn p imp_some_par * graph_assn G G_imp> 
   visited_dists_parents_imp empty_vis srcs_imp imp_some_dist imp_some_par
  <\<lambda> (visi, di, pari). graph_assn G G_imp *
      imp_vis_assn (BFS_dist_state.visited (BFS_par_impl initial_par_state)) visi *
      imp_dist_assn (BFS_dist_state.dists (BFS_par_impl initial_par_state)) di *
      imp_par_assn (BFS_par_state.parent (BFS_par_impl initial_par_state)) pari>"
  unfolding visited_dists_parents_imp_def
  by (sep_auto heap: bfs_heap_rules simp: state_assn_def)

text \<open>The same, but the final frontier is kept as well, so that its arrays can be reused.\<close>

lemma \<^marker>\<open>provenance ai_human\<close> visited_dists_parents_imp_frontier_rule[bfs_heap_rules]:
  "BFS_axiom \<Longrightarrow>
   <imp_vis_assn vset_empty empty_vis * imp_src_assn srcs srcs_imp * imp_dist_assn some_dist imp_some_dist
   * imp_par_assn p imp_some_par * graph_assn G G_imp> 
   visited_dists_parents_imp empty_vis srcs_imp imp_some_dist imp_some_par
  <\<lambda> (visi, di, pari). graph_assn G G_imp *
      imp_vis_assn (BFS_dist_state.visited (BFS_par_impl initial_par_state)) visi *
      imp_dist_assn (BFS_dist_state.dists (BFS_par_impl initial_par_state)) di *
      imp_par_assn (BFS_par_state.parent (BFS_par_impl initial_par_state)) pari *
      (\<exists>\<^sub>A cf cfi. imp_cf_assn cf cfi)>"
  unfolding visited_dists_parents_imp_def
  by (sep_auto heap: bfs_heap_rules simp: state_assn_def)

text \<open>The main properties of @{thm [source] BFS_par_correct} carry over to the returned visited
      set, distances and parents.\<close>

theorem \<^marker>\<open>provenance ai_human\<close> visited_dists_parents_imp_correct[bfs_heap_rules]:
  assumes BFS_axiom
  shows
 "<imp_vis_assn vset_empty empty_vis * imp_src_assn srcs srcs_imp * imp_dist_assn some_dist imp_some_dist
   * imp_par_assn p imp_some_par * graph_assn G G_imp>
   visited_dists_parents_imp empty_vis srcs_imp imp_some_dist imp_some_par
  <\<lambda> (visi, di, pari). \<exists>\<^sub>A vis d par. graph_assn G G_imp * imp_vis_assn vis visi *
      imp_dist_assn d di * imp_par_assn par pari *
      \<up>((\<forall> x. x \<in> t_set vis \<longleftrightarrow> (\<exists>u \<in> t_set srcs. \<exists>q. vwalk_bet (Graph.digraph_abs G) u q x)) \<and>
         (\<forall> x \<in> t_set vis. dist_lookup d x = distance_set (Graph.digraph_abs G) (t_set srcs) x) \<and>
         (\<forall> x \<in> t_set vis - t_set srcs.
             (\<exists> u. (x, u) \<in> parent_abstract par) \<and>
             (\<forall> u. (x, u) \<in> parent_abstract par \<longrightarrow>
                u \<in> t_set vis \<and> (u, x) \<in> Graph.digraph_abs G \<and>
                distance_set (Graph.digraph_abs G) (t_set srcs) x =
                  distance_set (Graph.digraph_abs G) (t_set srcs) u + 1)) \<and>
         (\<forall> x \<in> t_set vis. \<exists>u \<in> t_set srcs.
             vwalk_bet (Graph.digraph_abs G) u (rev (get_path par x)) x \<and>
             length (get_path par x) - 1 = distance_set (Graph.digraph_abs G) (t_set srcs) x))>"
  by (rule ht_cons_post_prec[OF visited_dists_parents_imp_rule[OF assms]],
      simp only: split_paired_all prod.case,
      rule ent_ex_postI[where x = "BFS_dist_state.visited (BFS_par_impl initial_par_state)"],
      rule ent_ex_postI[where x = "BFS_dist_state.dists (BFS_par_impl initial_par_state)"],
      rule ent_ex_postI[where x = "BFS_par_state.parent (BFS_par_impl initial_par_state)"],
      use BFS_par_correct[OF assms refl] in sep_auto)

text \<open>Given the final parents and an array with room for at least as many vertices as the graph
      has after position @{term k}, @{term get_path_imp} writes the path from a visited vertex
      @{term v} back to a source into the array from position @{term k} on. Reversed, it is a
      shortest path from the sources.\<close>

theorem \<^marker>\<open>provenance ai_human\<close> get_path_imp_correct[bfs_heap_rules]:
  assumes BFS_axiom "final_state = BFS_par_impl initial_par_state"
          "v \<in> t_set (BFS_dist_state.visited final_state)"
          "k + card (dVs (Graph.digraph_abs G)) \<le> length r"
  shows "<imp_par_assn (BFS_par_state.parent final_state) pari * Ra \<mapsto>\<^sub>a r>
           get_path_imp pari Ra k v
         <\<lambda>k'. imp_par_assn (BFS_par_state.parent final_state) pari *
              Ra \<mapsto>\<^sub>a (take k r @ get_path (BFS_par_state.parent final_state) v @
                      drop (k + length (get_path (BFS_par_state.parent final_state) v)) r) *
              \<up>(k' = k + length (get_path (BFS_par_state.parent final_state) v) \<and>
                 (\<exists>u \<in> t_set srcs.
                    vwalk_bet (Graph.digraph_abs G) u (rev (get_path (BFS_par_state.parent final_state) v)) v \<and>
                    length (get_path (BFS_par_state.parent final_state) v) - 1 =
                      distance_set (Graph.digraph_abs G) (t_set srcs) v))>"
proof-
  have len: "k + length (get_path (BFS_par_state.parent final_state) v) \<le> length r"
    using get_path_length[OF assms(1-3)] assms(4) by linarith
  show ?thesis
    using BFS_par_correct(4)[OF assms(1-3)]
    by (sep_auto heap: par_static.get_path_rule[OF get_path_pre[OF assms(1-3)] len])
qed

text \<open>The same from position \<open>0\<close> on: the first @{term k} cells of the array hold the path, and
      reversed they are a shortest path from the sources.\<close>

corollary \<^marker>\<open>provenance ai_human\<close> get_path_imp_prefix_correct[bfs_heap_rules]:
  assumes BFS_axiom "final_state = BFS_par_impl initial_par_state"
          "v \<in> t_set (BFS_dist_state.visited final_state)"
          "card (dVs (Graph.digraph_abs G)) \<le> length r"
  shows "<imp_par_assn (BFS_par_state.parent final_state) pari * Ra \<mapsto>\<^sub>a r>
           get_path_imp pari Ra 0 v
         <\<lambda>k. imp_par_assn (BFS_par_state.parent final_state) pari *
              (\<exists>\<^sub>A ps. Ra \<mapsto>\<^sub>a ps * \<up>(length ps = length r \<and>
                 take k ps = get_path (BFS_par_state.parent final_state) v \<and>
                 (\<exists>u \<in> t_set srcs. vwalk_bet (Graph.digraph_abs G) u (rev (take k ps)) v \<and>
                    k - 1 = distance_set (Graph.digraph_abs G) (t_set srcs) v)))>"
proof-
  have len: "length (get_path (BFS_par_state.parent final_state) v) \<le> length r"
    using get_path_length[OF assms(1-3)] assms(4) by linarith
  show ?thesis
    using len
    by (sep_auto heap: get_path_imp_correct[OF assms(1-3), where k = 0, simplified, OF assms(4)])
qed

end
text \<open>The code locale of the subprocedures: it only fixes the operations of the visited set, the
      extension of the parent map and the fold over the neighbours of a vertex in the graph, and has
      no assumptions, so that it can be globally interpreted for code generation.\<close>

locale BFS_subprocedures_lists_code =
  fixes vis_isin_imp :: "'imp_vis \<Rightarrow> nat \<Rightarrow> bool Heap"
    and vis_insert_imp :: "nat \<Rightarrow> 'imp_vis \<Rightarrow> unit Heap"
    and par_extend_imp :: "'imp_par \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap"
    and nbs_fold_imp :: "'g \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat array \<times> nat \<Rightarrow> (nat array \<times> nat) Heap) \<Rightarrow>
          nat array \<times> nat \<Rightarrow> (nat array \<times> nat) Heap"
begin

text \<open>The visited set and the parent map are updated in place; their handles are not part of
      the accumulator, so no larger tuple is built per edge.\<close>

fun inner_loop where
"inner_loop Gi visi pari u (front, frontpt) =
   nbs_fold_imp Gi u
     (\<lambda> v (front, frontpt).
          do {b \<leftarrow> vis_isin_imp visi v;
              if \<not> b then do { front' \<leftarrow> Array.upd frontpt v front;
                               vis_insert_imp v visi;
                               par_extend_imp pari u v;
                               return (front', Suc frontpt)}
              else return (front, frontpt)})
      (front, frontpt)"

fun outer_loop where
  "outer_loop Gi visi pari (old_front, old_frontp) (front, frontpt) =
    iterate_range_strict old_front 0 old_frontp (inner_loop Gi visi pari) (front, frontpt)"

definition "imp_src_to_cf = (\<lambda> x. return x)"

fun imp_cf_is_empty where
 "imp_cf_is_empty (fronti, frontp, buffer_fronti) = 
          return (frontp = 0)"

fun set_srcs_visited where
  "set_srcs_visited (imp_vis::'imp_vis) (fronti, frontp, buffer_fronti) =
   do { iterate_range_strict fronti 0 frontp (\<lambda> v _. vis_insert_imp v imp_vis) ();
        return imp_vis }"

fun set_all_dists_in_front_imp where
 "set_all_dists_in_front_imp di (fronti, frontp, buffer_fronti) n = 
       iterate_range_strict fronti 0 frontp 
         (\<lambda> v di. Array.upd v n di) di"

fun next_frontier_current_parents_imp where
  "next_frontier_current_parents_imp Gi (fronti, frontp, buffer_fronti) imp_vis pari =
   do{
      (front', frontpt') \<leftarrow> outer_loop Gi imp_vis pari (fronti, frontp) (buffer_fronti, 0);
      return ((front', frontpt', fronti), imp_vis, pari)}"

end

text \<open>The proof locale: the visited set is a set over the universe @{term U} with membership test
      and insertion in place (@{locale fixed_univ_set_basic_imp}). The parent map over the universe
      @{term par_U} is extended in place (@{locale Parent_Map_Spec_extend_imp}). The graph @{term G}, a map from the
      vertices to their neighbour lists, is the indexed collection of the neighbourhoods; the fold
      over the neighbours of a vertex (@{locale indexed_set_fold_imp}) runs in the order of the
      neighbour list.\<close>

locale BFS_subprocedures_lists =
  BFS_subprocedures_lists_code where vis_isin_imp = vis_isin_imp and vis_insert_imp = vis_insert_imp
    and par_extend_imp = par_extend_imp and nbs_fold_imp = nbs_fold_imp +
  vis_imp: fixed_univ_set_basic_imp where U = U
    and fixed_univ_set_invar = vis_invar and fixed_univ_set_abstract = vis_abstract
    and fixed_univ_set_empty = vis_empty and fixed_univ_set_insert = vis_insert
    and fixed_univ_set_delete = vis_delete and fixed_univ_set_isin = vis_isin
    and fixed_univ_set_assn = vis_assn and fixed_univ_set_insert_imp = vis_insert_imp
    and fixed_univ_set_delete_imp = vis_delete_imp and fixed_univ_set_isin_imp = vis_isin_imp +
  par_imp: Parent_Map_Spec_extend_imp where U = par_U and to_dir_graph = par_abstract
    and extend = par_extend and invar = par_invar and roots = par_roots
    and parent_assn = par_assn and extend_imp = par_extend_imp +
  nbs_imp: indexed_set_fold_imp where idx_invar = nbs_invar
    and idx_abstract = "\<lambda>G u. set (case G u of None \<Rightarrow> [] | Some vs \<Rightarrow> vs)" and K = K
    and idx_fold = nbs_fold and idx_assn = graph_assn and idx_fold_imp = nbs_fold_imp
  for vis_isin_imp :: "'imp_vis \<Rightarrow> nat \<Rightarrow> bool Heap"
    and vis_insert_imp :: "nat \<Rightarrow> 'imp_vis \<Rightarrow> unit Heap"
    and par_extend_imp :: "'imp_par \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap"
    and nbs_fold_imp :: "'g \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat array \<times> nat \<Rightarrow> (nat array \<times> nat) Heap) \<Rightarrow>
          nat array \<times> nat \<Rightarrow> (nat array \<times> nat) Heap"
    and U :: "nat set"
    and vis_invar :: "'vis \<Rightarrow> bool"
    and vis_abstract vis_empty vis_insert vis_delete vis_isin vis_assn vis_delete_imp
    and par_U :: "nat set"
    and par_abstract :: "'par \<Rightarrow> (nat \<times> nat) set"
    and par_extend :: "'par \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'par"
    and par_invar :: "'par \<Rightarrow> bool"
    and par_roots :: "'par \<Rightarrow> nat set"
    and par_assn :: "'par \<Rightarrow> 'imp_par \<Rightarrow> assn"
    and nbs_invar :: "(nat \<Rightarrow> nat list option) \<Rightarrow> bool"
    and K :: "nat set"
    and nbs_fold :: "(nat \<Rightarrow> nat list option) \<Rightarrow> nat \<Rightarrow>
          (nat \<Rightarrow> nat list \<times> nat list \<times> 'par \<Rightarrow> nat list \<times> nat list \<times> 'par) \<Rightarrow>
          nat list \<times> nat list \<times> 'par \<Rightarrow> nat list \<times> nat list \<times> 'par"
    and graph_assn :: "(nat \<Rightarrow> nat list option) \<Rightarrow> 'g \<Rightarrow> assn" +
  assumes K_U: "K \<subseteq> U"
    and nbs_fold_order: "\<And>G u f acc. \<lbrakk>nbs_invar G; u \<in> K\<rbrakk> \<Longrightarrow>
          nbs_fold G u f acc = foldl (\<lambda>acc x. f x acc) acc (case G u of None \<Rightarrow> [] | Some vs \<Rightarrow> vs)"
begin

definition Vs where "Vs (G::nat \<Rightarrow> nat list option) = \<Union> {{u, v} | u v vs. G u = Some vs \<and> v \<in> set vs }"

text \<open>The visited set as a set of vertices of the graph.\<close>

definition "is_visited_set W S visi =
   (\<exists>\<^sub>A V. vis_assn V visi * \<up>(vis_invar V \<and> vis_abstract V = S \<and> S \<subseteq> W))"

lemma only_in_univ: "is_visited_set W S visi = is_visited_set W S visi * \<up>(S \<subseteq> W)"
  unfolding is_visited_set_def by (rule ent_iffI) sep_auto+

lemma \<^marker>\<open>provenance ai_human\<close> vis_memb_rule[bfs_heap_rules]:
  "W \<subseteq> U \<Longrightarrow>
   <is_visited_set W S visi * \<up>(a \<in> W)> vis_isin_imp visi a
   <\<lambda>r. is_visited_set W S visi * \<up>(r \<longleftrightarrow> a \<in> S)>"
  unfolding is_visited_set_def
  by (sep_auto heap: vis_imp.fixed_univ_set_isin_rule simp: vis_imp.fixed_univ_set_isin)

lemma \<^marker>\<open>provenance ai_human\<close> vis_ins_rule[bfs_heap_rules]:
  "W \<subseteq> U \<Longrightarrow>
   <is_visited_set W S visi * \<up>(a \<in> W)> vis_insert_imp a visi
   <\<lambda>_. is_visited_set W (Set.insert a S) visi>"
  unfolding is_visited_set_def
  by (sep_auto heap: vis_imp.fixed_univ_set_insert_rule simp: vis_imp.fixed_univ_set_insert)

lemma Vs_nbs:
  "x \<in> set (case G u of None \<Rightarrow> [] | Some vs \<Rightarrow> vs) \<Longrightarrow>
   x \<in> Vs G"
    by (cases "G u") (auto simp: Vs_def)

text \<open>The invariant of the parent map during a round: it is valid, and the vertices of its edges
      together with its roots are the visited vertices.\<close>

definition "par_vis_inv p V \<longleftrightarrow> par_invar p \<and> dVs (par_abstract p) \<union> par_roots p = V"

lemma par_extend_step:
  assumes "par_vis_inv p V" "u \<in> V" "y \<in> par_U" "y \<notin> V"
  shows "y \<in> par_U - dVs (par_abstract p) - par_roots p" "u \<in> dVs (par_abstract p) \<union> par_roots p"
        "par_vis_inv (par_extend p u y) (Set.insert y V)"
        "par_abstract (par_extend p u y) = Set.insert (y, u) (par_abstract p)"
        "par_roots (par_extend p u y) = par_roots p"
  using assms par_imp.extend[of p y u]
  by (auto simp: par_vis_inv_def dVs_eq)

text \<open>A round on one frontier vertex @{term u}: the newly visited vertices @{term D} get the
      parent @{term u}.\<close>

lemma inner_fold_par:
  assumes "foldl (\<lambda>x y. case x of (nf, vis, p) \<Rightarrow>
                if y \<notin> set vis then (y # nf, y # vis, par_extend p u y) else (nf, vis, p)) (nf, vis, p) ys
           = (nf', vis', p')" "set nf \<subseteq> set vis" "par_vis_inv p (set vis)" "u \<in> set vis"
          "set ys \<subseteq> par_U"
  shows "set nf' \<subseteq> set vis' \<and> par_vis_inv p' (set vis') \<and> par_roots p' = par_roots p \<and>
         (\<exists> D. set nf' = set nf \<union> D \<and> set vis' = set vis \<union> D \<and> D \<inter> set vis = {} \<and> D \<subseteq> set ys \<and>
               par_abstract p' = par_abstract p \<union> (\<lambda> y. (y, u)) ` D)"
  using assms
proof(induction ys arbitrary: nf vis p)
  case Nil
  then show ?case
    by (intro conjI exI[of _ "{}"]) auto
next
  case (Cons y ys)
  show ?case
  proof(cases "y \<in> set vis")
    case True
    have fold: "foldl (\<lambda>x y. case x of (nf, vis, p) \<Rightarrow>
                if y \<notin> set vis then (y # nf, y # vis, par_extend p u y) else (nf, vis, p)) (nf, vis, p) ys
           = (nf', vis', p')"
      using Cons.prems(1) True by simp
    have "set ys \<subseteq> par_U"
      using Cons.prems(5) by simp
    note IH = Cons.IH[OF fold Cons.prems(2-4) this]
    then obtain D where D: "set nf' = set nf \<union> D" "set vis' = set vis \<union> D" "D \<inter> set vis = {}"
      "D \<subseteq> set ys" "par_abstract p' = par_abstract p \<union> (\<lambda> y. (y, u)) ` D"
      by blast
    show ?thesis
      using IH D by (intro conjI exI[of _ D]) auto
  next
    case False
    note st = par_extend_step[OF Cons.prems(3,4) _ False]
    have y: "y \<in> par_U"
      using Cons.prems(5) by simp
    have fold: "foldl (\<lambda>x y. case x of (nf, vis, p) \<Rightarrow>
                if y \<notin> set vis then (y # nf, y # vis, par_extend p u y) else (nf, vis, p))
                (y # nf, y # vis, par_extend p u y) ys = (nf', vis', p')"
      using Cons.prems(1) False by simp
    have "set (y # nf) \<subseteq> set (y # vis)" "par_vis_inv (par_extend p u y) (set (y # vis))"
         "u \<in> set (y # vis)" "set ys \<subseteq> par_U"
      using Cons.prems(2,4,5) st(3)[OF y] by auto
    note IH = Cons.IH[OF fold this]
    then obtain D where D: "set nf' = set (y # nf) \<union> D" "set vis' = set (y # vis) \<union> D"
      "D \<inter> set (y # vis) = {}" "D \<subseteq> set ys"
      "par_abstract p' = par_abstract (par_extend p u y) \<union> (\<lambda> y. (y, u)) ` D"
      by (elim conjE exE) assumption
    show ?thesis
      using IH D st(4,5)[OF y] False by (intro conjI exI[of _ "Set.insert y D"]) auto
  qed
qed

text \<open>A round on the frontier vertices @{term us}: every newly visited vertex gets a frontier
      vertex as its parent, from which an edge leads to it.\<close>

lemma outer_fold_par:
  assumes "foldl (\<lambda>(nf, vis, p) u.
       foldl (\<lambda>x y. case x of (nf, vis, p) \<Rightarrow>
                if y \<notin> set vis then (y # nf, y # vis, par_extend p u y) else (nf, vis, p))
            (nf, vis, p) (N u)) (nf, vis, p) us = (nf', vis', p')"
          "set nf \<subseteq> set vis" "par_vis_inv p (set vis)" "set us \<subseteq> set vis"
          "\<forall> u \<in> set us. set (N u) \<subseteq> par_U"
  shows "set nf' \<subseteq> set vis' \<and> par_vis_inv p' (set vis') \<and> par_roots p' = par_roots p \<and>
         (\<exists> Ex. par_abstract p' = par_abstract p \<union> Ex \<and> set nf' = set nf \<union> fst ` Ex \<and>
                (\<forall> y u. (y, u) \<in> Ex \<longrightarrow> u \<in> set us \<and> y \<in> set (N u)))"
  using assms
proof(induction us arbitrary: nf vis p)
  case Nil
  then show ?case
    by (intro conjI exI[of _ "{}"]) auto
next
  case (Cons u us)
  obtain nf1 vis1 p1 where eq: "foldl (\<lambda>x y. case x of (nf, vis, p) \<Rightarrow>
                if y \<notin> set vis then (y # nf, y # vis, par_extend p u y) else (nf, vis, p)) (nf, vis, p) (N u)
         = (nf1, vis1, p1)"
    by (rule prod_cases3)
  have "u \<in> set vis" "set (N u) \<subseteq> par_U"
    using Cons.prems(4,5) by auto
  note one = inner_fold_par[OF eq Cons.prems(2,3) this]
  then obtain D where D: "set nf1 = set nf \<union> D" "set vis1 = set vis \<union> D" "D \<subseteq> set (N u)"
      "par_abstract p1 = par_abstract p \<union> (\<lambda> y. (y, u)) ` D"
    by blast
  have fold: "foldl (\<lambda>(nf, vis, p) u.
       foldl (\<lambda>x y. case x of (nf, vis, p) \<Rightarrow>
                if y \<notin> set vis then (y # nf, y # vis, par_extend p u y) else (nf, vis, p))
            (nf, vis, p) (N u)) (nf1, vis1, p1) us = (nf', vis', p')"
    using Cons.prems(1) unfolding foldl_Cons prod.case eq .
  have "set us \<subseteq> set vis1" "\<forall> u \<in> set us. set (N u) \<subseteq> par_U"
    using Cons.prems(4,5) D(2) by auto
  note two = Cons.IH[OF fold conjunct1[OF one] conjunct1[OF conjunct2[OF one]] this]
  then obtain Ex where Ex: "par_abstract p' = par_abstract p1 \<union> Ex" "set nf' = set nf1 \<union> fst ` Ex"
      "\<forall> y u. (y, u) \<in> Ex \<longrightarrow> u \<in> set us \<and> y \<in> set (N u)"
    by blast
  show ?case
    using one two D Ex
    by (intro conjI exI[of _ "(\<lambda> y. (y, u)) ` D \<union> Ex"]) (auto simp: image_Un image_image)
qed

text \<open>The arrays have the fixed lengths @{term L} and the fixed handles given by the caller, so
      that they can be reused for further searches on other graphs.\<close>

definition "front_assn L Fh G vis (front::nat list) fronti frontp = 
  (\<exists>\<^sub>A frontlist. fronti \<mapsto>\<^sub>a frontlist * \<up> (length frontlist > card (Vs G) \<and>
     frontp < length frontlist - card (Vs G) + card vis \<and> frontp \<le> length frontlist \<and>
        rev (take frontp (frontlist)) = front
     \<and> vis \<subseteq> (Vs G) \<and> set front \<subseteq> (Vs G) \<and> length frontlist = L \<and> fronti = Fh))"

lemma inner_loop_rule[bfs_heap_rules]:
  assumes "(front', vis', p') = 
          foldl (\<lambda>x y. case x of (nf, vis, p) \<Rightarrow>
                   if y \<notin> set vis then (y # nf, y # vis, par_extend p u y) else (nf, vis, p))
            (front, vis, p) (case G u of None \<Rightarrow> [] | Some ys \<Rightarrow> ys)"
          "finite (Vs G)" "nbs_invar G" "u \<in> K" "Vs G \<subseteq> K" "Vs G \<subseteq> par_U"
          "par_vis_inv p (set vis)" "u \<in> set vis"
  shows "<graph_assn G Gi
          * is_visited_set (Vs G) (set vis) visi * front_assn L Fh G (set vis) front fronti frontp
          * par_assn p pari>
  inner_loop Gi visi pari u (fronti, frontp)
 <\<lambda> (fronti', frontp'). 
   graph_assn G Gi
       * is_visited_set (Vs G) (set vis') visi * front_assn L Fh G (set vis') front' fronti' frontp'
       * par_assn p' pari>"
proof-
  have VU: "Vs G \<subseteq> U"
    using assms(5) K_U by (rule order.trans)
  define acc_assn where 
    "acc_assn = (\<lambda> (front, vis, p) (fronti, frontp). 
        is_visited_set (Vs G) (set vis) visi * front_assn L Fh G (set vis) front fronti frontp
        * par_assn p pari * \<up>(par_vis_inv p (set vis) \<and> u \<in> set vis))"
  define fi where "fi = (\<lambda> (v::nat) (front, frontpt). 
          do {b \<leftarrow> vis_isin_imp visi v;
              if \<not> b then do { front' \<leftarrow> Array.upd frontpt v front;
                               vis_insert_imp v visi;
                               par_extend_imp pari u v;
                               return (front', Suc frontpt)}
              else return (front, frontpt)})"
  define f where "f = (\<lambda>(y::nat) (nf, vis, p). if y \<notin> set vis then (y # nf, y # vis, par_extend p u y)
                                        else (nf, vis, p))"
  have fold: "nbs_fold G u f (front, vis, p) = (front', vis', p')"
    using assms(1) by (simp add: nbs_fold_order[OF assms(3,4)] f_def split_def)
  have step: "<acc_assn acc acci> fi x acci <\<lambda>r. acc_assn (f x acc) r>"
    if x: "x \<in> set (case G u of None \<Rightarrow> [] | Some ys \<Rightarrow> ys)" for acc acci x
  proof -
    obtain nf vs pp where acc: "acc = (nf, vs, pp)" by (cases acc)
    obtain fi' fp' where acci: "acci = (fi', fp')" by (cases acci)
    have xV: "x \<in> Vs G"
      using x by (rule Vs_nbs)
    show ?thesis
    proof (cases "par_vis_inv pp (set vs) \<and> u \<in> set vs")
      case False
      then show ?thesis
        unfolding acc acci acc_assn_def by sep_auto
    next
      case inv: True
    show ?thesis
    proof (cases "x \<in> set vs")
      case True
      then show ?thesis
        unfolding acc acci acc_assn_def fi_def f_def prod.case
        using xV inv by (sep_auto heap: vis_memb_rule[OF VU])
    next
      case False
      have xP: "x \<in> par_U"
        using xV assms(6) by blast
      note st = par_extend_step[OF conjunct1[OF inv] conjunct2[OF inv] xP False]
      note ext = par_imp.extend_rule[OF conjunct1[OF conjunct1[OF inv, unfolded par_vis_inv_def]] st(1,2)]
      have card: "card (set vs) < card (Vs G)" if "set vs \<subseteq> Vs G"
        using psubset_card_mono[OF assms(2)] that xV False by blast
      have push: "<front_assn L Fh G (set vs) nf fi' fp'> Array.upd fp' x fi'
                  <\<lambda>r. front_assn L Fh G (set (x # vs)) (x # nf) r (Suc fp')>"
        unfolding front_assn_def
        apply (intro ht_exEI ht_extract_pre_pure(1))
        subgoal premises fl for fl
        proof -
          have c: "card (set vs) < card (Vs G)"
            using fl by (blast intro: card)
          have lt: "Suc fp' < length fl"
            using fl c by (elim conjE) linarith
          show ?thesis
          proof (rule ht_cons_post_prec[OF upd_rule], goal_cases)
            case (1 r)
            show ?case
              using fl lt xV False
              by (intro ent_pure_preI(1) ent_ex_postI[where x = "list_update fl fp' x"])
                 (sep_auto simp: take_update_last card_insert_if)
          qed
        qed
        done
      show ?thesis
        unfolding acc acci acc_assn_def fi_def f_def prod.case
        using xV False inv st(3) by (sep_auto heap: vis_memb_rule[OF VU] vis_ins_rule[OF VU] push ext)
    qed
    qed
  qed
  have main: "<graph_assn G Gi * acc_assn (front, vis, p) (fronti, frontp)> nbs_fold_imp Gi u fi (fronti, frontp)
              <\<lambda>r. graph_assn G Gi * acc_assn (front', vis', p') r>"
    unfolding fold[symmetric]
    by (rule nbs_imp.idx_fold_rule[where acc_assn = acc_assn and f = f, OF assms(3,4)]) (fact step)
  show ?thesis
    unfolding inner_loop.simps fi_def[symmetric]
    by (rule ht_cons_post[OF ht_cons_pre[OF _ main]]) (sep_auto simp: acc_assn_def assms(7,8) split: prod.splits)+
qed

definition "old_front_assn L G (front::nat list) fronti frontp = 
  (\<exists>\<^sub>A frontlist. 
    fronti \<mapsto>\<^sub>a frontlist * \<up> ( frontp < length frontlist \<and> rev (take frontp (frontlist)) = front
    \<and> card (Vs G) < length frontlist \<and> length frontlist = L \<and> set front \<subseteq> Vs G))"

lemma outer_loop_rule[bfs_heap_rules]:
  assumes "(front', vis', p') = 
   foldl (\<lambda>(nf, vis, p) u. 
       foldl (\<lambda>x y. case x of (nf, vis, p) \<Rightarrow>
                if y \<notin> set vis then (y # nf, y # vis, par_extend p u y) else (nf, vis, p))
            (nf, vis, p) (case G u of None \<Rightarrow> [] | Some ys \<Rightarrow> ys)) 
   (front, vis, p) (rev old_front)"
          "finite (Vs G)" "nbs_invar G" "Vs G \<subseteq> K" "Vs G \<subseteq> par_U"
          "par_vis_inv p (set vis)" "set old_front \<subseteq> set vis" "set front \<subseteq> set vis"
  shows "<graph_assn G Gi
          * is_visited_set (Vs G) (set vis) visi * front_assn L Fh G (set vis) front fronti frontp
          * par_assn p pari * old_front_assn L G old_front old_fronti old_frontp>
  outer_loop Gi visi pari (old_fronti, old_frontp) (fronti, frontp)
 <\<lambda> (fronti', frontp'). 
   graph_assn G Gi
       * is_visited_set (Vs G) (set vis') visi * front_assn L Fh G (set vis') front' fronti' frontp'
       * par_assn p' pari * old_front_assn L G old_front old_fronti old_frontp>"
proof-
  define acc_assn where 
    "acc_assn = (\<lambda> (front, vis, p) (fronti, frontp). 
        is_visited_set (Vs G) (set vis) visi * front_assn L Fh G (set vis) front fronti frontp
        * par_assn p pari * \<up>(par_vis_inv p (set vis) \<and> set old_front \<subseteq> set vis \<and> set front \<subseteq> set vis))"
  define f where "f = (\<lambda>  (nf, vis, p) u.
      foldl (\<lambda>x y. case x of (nf, vis, p) \<Rightarrow>
               if y \<notin> set vis then (y # nf, y # vis, par_extend p u y) else (nf, vis, p))
            (nf, vis, p) (case G u of None \<Rightarrow> [] | Some ys \<Rightarrow> ys))"
  define R where "R ol \<longleftrightarrow> old_frontp < length ol \<and> rev (take old_frontp ol) = old_front
    \<and> card (Vs G) < length ol \<and> length ol = L \<and> set old_front \<subseteq> Vs G" for ol
  have main: "<graph_assn G Gi * acc_assn (front, vis, p) (fronti, frontp) * old_fronti \<mapsto>\<^sub>a ol>
     outer_loop Gi visi pari (old_fronti, old_frontp) (fronti, frontp)
     <\<lambda>r. graph_assn G Gi * acc_assn (front', vis', p') r * old_fronti \<mapsto>\<^sub>a ol>"
    if R: "R ol" for ol
  proof -
    have take: "nths ol {0..<old_frontp} = rev old_front"
      using R by (auto simp: R_def nths_intervall_strict_as_drop_and_take)
    have step: "<acc_assn acc acci * graph_assn G Gi> inner_loop Gi visi pari x acci
                <\<lambda>r. acc_assn (f acc x) r * graph_assn G Gi>"
      if x: "x \<in> set (nths ol {0..<old_frontp})" for acc acci x
    proof -
      obtain nf vs pp where acc: "acc = (nf, vs, pp)" by (cases acc)
      obtain fi' fp' where acci: "acci = (fi', fp')" by (cases acci)
      have xK: "x \<in> K"
        using x R assms(4) unfolding take by (auto simp: R_def)
      obtain a b c where abc: "foldl (\<lambda>x' y. case x' of (nf, vis, p) \<Rightarrow>
                if y \<notin> set vis then (y # nf, y # vis, par_extend p x y) else (nf, vis, p))
            (nf, vs, pp) (case G x of None \<Rightarrow> [] | Some ys \<Rightarrow> ys) = (a, b, c)"
        by (rule prod_cases3)
      have fx: "f (nf, vs, pp) x = (a, b, c)"
        unfolding f_def prod.case by (rule abc)
      have xo: "x \<in> set old_front"
        using x unfolding take by simp
      show ?thesis
      proof (cases "par_vis_inv pp (set vs) \<and> set old_front \<subseteq> set vs \<and> set nf \<subseteq> set vs")
        case False
        then show ?thesis
          unfolding acc acci acc_assn_def fx prod.case by sep_auto
      next
        case inv: True
        have xs: "x \<in> set vs"
          using inv xo by blast
        have NU: "set (case G x of None \<Rightarrow> [] | Some ys \<Rightarrow> ys) \<subseteq> par_U"
          using Vs_nbs assms(5) by blast
        note inner = inner_loop_rule[OF abc[symmetric] assms(2,3) xK assms(4,5) conjunct1[OF inv] xs]
        note fp = inner_fold_par[OF abc conjunct2[OF conjunct2[OF inv]] conjunct1[OF inv] xs NU]
        have post: "par_vis_inv c (set b) \<and> set old_front \<subseteq> set b \<and> set a \<subseteq> set b"
          using fp inv by blast
        show ?thesis
          unfolding acc acci acc_assn_def fx prod.case
          by (rule ht_cons_post[OF ht_cons_pre[OF _ inner]]) (sep_auto simp: post split: prod.splits)+
      qed
    qed
    have fold: "foldl f (front, vis, p) (nths ol {0..<old_frontp}) = (front', vis', p')"
      using assms(1) by (simp add: take f_def)
    show ?thesis
      unfolding outer_loop.simps
      using R iterate_range_strict_rule[of ol 0 old_frontp acc_assn "graph_assn G Gi"
                "inner_loop Gi visi pari" f old_fronti "(front, vis, p)" "(fronti, frontp)", OF step]
      unfolding fold by (sep_auto simp: R_def)
  qed
  show ?thesis
    unfolding old_front_assn_def
    by (sep_auto heap: main[unfolded acc_assn_def prod.case] simp: R_def acc_assn_def assms(6-8))
qed

text \<open>The frontier and the buffer are the two arrays @{term Fr} and @{term Bf} of length
      @{term L}, in either order, since they swap their roles in every round.\<close>

fun imp_cf_assn where 
   "imp_cf_assn L Fr Bf (G::nat \<Rightarrow> nat list option) front (fronti, frontp, buffer_fronti) =
      (\<exists>\<^sub>A frontlist buffer_frontlist. fronti \<mapsto>\<^sub>a frontlist *  buffer_fronti \<mapsto>\<^sub>a buffer_frontlist *
       \<up> (length frontlist > card (Vs G) \<and> frontp < length frontlist  \<and> 
          rev (take frontp (frontlist)) = front \<and> length buffer_frontlist > card (Vs G)
          \<and> set front \<subseteq> (Vs G) \<and> length frontlist = L \<and> length buffer_frontlist = L
          \<and> {fronti, buffer_fronti} = {Fr, Bf}))"

definition "imp_src_assn = imp_cf_assn"

lemma \<^marker>\<open>provenance ai_human\<close> imp_cf_is_empty_rule[bfs_heap_rules]:
  "<imp_cf_assn L Fr Bf G S Si> imp_cf_is_empty Si <\<lambda>b. imp_cf_assn L Fr Bf G S Si * \<up> (b = (S = []))>"
  by(cases Si) sep_auto

lemma foldl_insert[simp]:"foldl (\<lambda>S x. Set.insert x S) A xs = set xs \<union> A"
  by(induction xs arbitrary: A) auto

lemma \<^marker>\<open>provenance ai_human\<close> set_srcs_visited_rule[bfs_heap_rules]:
  assumes "Vs G \<subseteq> U"
  shows "<imp_src_assn L Fr Bf G S Si * is_visited_set (Vs G) {} empty_vis> 
          set_srcs_visited empty_vis Si
        <\<lambda>r. is_visited_set (Vs G) (set S) r * imp_src_assn L Fr Bf G S Si>"
proof (cases Si)
  case (fields fronti frontp buffer_fronti)
  have main: "<fronti \<mapsto>\<^sub>a fl * is_visited_set (Vs G) {} empty_vis>
     iterate_range_strict fronti 0 frontp (\<lambda>v _. vis_insert_imp v empty_vis) ()
     <\<lambda>_. fronti \<mapsto>\<^sub>a fl * is_visited_set (Vs G) (set S) empty_vis>"
    if fl: "frontp < length fl" "rev (take frontp fl) = S" "set S \<subseteq> Vs G" for fl
  proof -
    have nths: "nths fl {0..<frontp} = rev S"
      using fl by (auto simp: nths_intervall_strict_as_drop_and_take)
    have step: "<is_visited_set (Vs G) A empty_vis * emp> vis_insert_imp x empty_vis
                <\<lambda>_. is_visited_set (Vs G) (Set.insert x A) empty_vis * emp>"
      if x: "x \<in> set (nths fl {0..<frontp})" for A x
    proof -
      have "x \<in> Vs G"
        using x fl(3) unfolding nths by auto
      then show ?thesis
        by (sep_auto heap: vis_ins_rule[OF assms])
    qed
    note rule = iterate_range_strict_rule[of fl 0 frontp "\<lambda>A (_::unit). is_visited_set (Vs G) A empty_vis"
                  emp "\<lambda>v _. vis_insert_imp v empty_vis" "\<lambda>A x. Set.insert x A" fronti "{}" "()", OF step]
    show ?thesis
      by (rule ht_cons_prec[OF _ _ rule]) (sep_auto simp: fl(1) nths foldl_insert)+
  qed
  show ?thesis
    unfolding fields imp_src_assn_def imp_cf_assn.simps set_srcs_visited.simps
    by (sep_auto heap: main)
qed


abbreviation "imp_dist_assn_raw G dlist d di 
   \<equiv> (di \<mapsto>\<^sub>a dlist * 
          \<up>((\<forall> i \<in> dom G. i < length dlist \<and> d i = dlist ! i)))"

text \<open>The distances are kept in the array @{term Da} of length @{term L}.\<close>

definition "imp_dist_assn L Da G d di 
   = (\<exists>\<^sub>A dlist. di \<mapsto>\<^sub>a dlist * 
          \<up>((\<forall> i \<in> Vs G. i < length dlist \<and> d i = dlist ! i) \<and> di = Da \<and> length dlist = L))"


lemma foldl_fun_upd_same[simp]: "foldl (\<lambda>d x y. if x = y then n else d y) d xs =
       (\<lambda> x. if x \<in> set xs then n else d x)"
  by(induction xs arbitrary: d)  auto

lemma \<^marker>\<open>provenance ai_human\<close> set_all_dists_in_front_imp_rule[bfs_heap_rules]:
  "<imp_dist_assn L' Da G d di * imp_cf_assn L Fr Bf G cf cfi> set_all_dists_in_front_imp di cfi n
    <\<lambda>r. imp_dist_assn L' Da G (\<lambda>y. if y \<in> set cf then n else d y) r * imp_cf_assn L Fr Bf G cf cfi>"
  apply(cases cfi) 
  subgoal for fronti frontp buffer_fronti
    apply simp 
    apply(rule ht_ex_pre_and_post_I)+
    subgoal for frontlist buffer_frontlist
    apply(rule ht_cons_prec)
      defer defer
        apply(rule iterate_range_strict_rule[where list = frontlist
               and acc_assn = "imp_dist_assn L' Da G" and acc = d
               and F = "buffer_fronti \<mapsto>\<^sub>a buffer_frontlist *
          \<up> (card (Vs G) < length frontlist \<and> frontp < length frontlist \<and>
        rev (take frontp frontlist) = cf \<and> card (Vs G) < length buffer_frontlist \<and> set cf \<subseteq> Vs G
        \<and> length frontlist = L \<and> length buffer_frontlist = L \<and> {fronti, buffer_fronti} = {Fr, Bf})"
               and f = "\<lambda> d. \<lambda> x y. if x = y then n else d y"])
      by (sep_auto simp: imp_dist_assn_def nths_intervall_strict_as_drop_and_take 
         nths_intervall_strict_as_drop_and_take foldl_fun_upd_same)
    done
  done


lemma verts_rw:
   "\<Union> {{v1, v2} |v1 v2. (v1, v2) \<in> {(u, v). v \<in> set (case G u of None \<Rightarrow> [] | Some vset \<Rightarrow> vset)}} =
    \<Union> {uu. \<exists>u v vs. uu = {u, v} \<and> G u = Some vs \<and> v \<in> set vs}"
proof -
  have "v \<in> set (case G u of None \<Rightarrow> [] | Some vs \<Rightarrow> vs) \<longleftrightarrow>
    (\<exists>vs. G u = Some vs \<and> v \<in> set vs)" for u v
    by (cases "G u") auto
  then show ?thesis by simp
qed

sublocale BFS_subprocedures_3
  where empty = "\<lambda> x. None"
  and delete = "\<lambda> (x::nat) M. \<lambda> y. if y = x then None else M y"
  and insert = Cons
  and isin = "\<lambda> xs x. x \<in> set xs"
  and t_set = set
  and sel = hd
  and  update = "\<lambda> x z M. \<lambda> y. if y = x then Some z else M y"
  and adjmap_inv = "\<lambda> _. True"
  and vset_empty = Nil
  and vset_delete = "\<lambda> x xs. filter (\<lambda> y. x \<noteq> y) xs"
  and vset_inv = "\<lambda> _. True"
  and union = append
  and inter = "\<lambda> xs ys. filter (\<lambda> y. y \<in> set ys) xs"
  and diff = "\<lambda> xs ys. filter (\<lambda> y. y \<notin> set ys) xs"
  and fold_vset = "\<lambda>  f xs a. foldl (\<lambda>x y. f y x) a xs"
  and fold_adjmap = "\<lambda>  f xs a. foldl (\<lambda>x y. f y x) a xs"
  and lookup = "\<lambda> M x. M x"
  and fold2_vset = "\<lambda>  f xs a. foldl (\<lambda>x y. f y x) a xs"
  and fold2_vset' = "\<lambda>  f xs a. foldl (\<lambda>x y. f y x) a (rev xs)"
  and fast_insert = Cons
  and vset_inv2 = distinct
  apply unfold_locales
  apply (auto intro: exI[of _ "rev _"] simp add: foldl_conv_foldr) 
  done

text \<open>The frontier, visited set and parents as computed by the loops above: the old frontier is
      traversed from its first array entry, i.e.\ in reversed list order.\<close>

definition "next_frontier_current_parents G cf vis p =
   foldl (\<lambda> (nf, vis, p) u.
       foldl (\<lambda>x y. case x of (nf, vis, p) \<Rightarrow>
                if y \<notin> set vis then (y # nf, y # vis, par_extend p u y) else (nf, vis, p))
            (nf, vis, p) (case G u of None \<Rightarrow> [] | Some ys \<Rightarrow> ys))
     ([], vis, p) (rev cf)"

lemma inner_fold_proj:
  "(\<lambda>(a, b, c). (a, b)) (foldl (\<lambda>x y. case x of (nf, vis, p) \<Rightarrow>
                if y \<notin> set vis then (y # nf, y # vis, par_extend p u y) else (nf, vis, p)) (nf, vis, p) ys)
   = foldl (\<lambda>x y. case x of (nf, vis) \<Rightarrow> if y \<notin> set vis then (y # nf, y # vis) else (nf, vis)) (nf, vis) ys"
proof(induction ys arbitrary: nf vis p)
  case (Cons y ys)
  show ?case
    by (cases "y \<in> set vis")
       (simp_all only: foldl_Cons prod.case Cons.IH not_True_eq_False not_False_eq_True if_True if_False)
qed (simp only: foldl_Nil prod.case)

lemma outer_fold_proj:
  "(\<lambda>(a, b, c). (a, b)) (foldl (\<lambda>(nf, vis, p) u.
       foldl (\<lambda>x y. case x of (nf, vis, p) \<Rightarrow>
                if y \<notin> set vis then (y # nf, y # vis, par_extend p u y) else (nf, vis, p))
            (nf, vis, p) (N u)) (nf, vis, p) us)
   = foldl (\<lambda>(nf, vis) u. 
       foldl (\<lambda>x y. case x of (nf, vis) \<Rightarrow> if y \<notin> set vis then (y # nf, y # vis) else (nf, vis))
            (nf, vis) (N u)) (nf, vis) us"
proof(induction us arbitrary: nf vis p)
  case (Cons u us)
  obtain nf1 vis1 p1 where eq: "foldl (\<lambda>x y. case x of (nf, vis, p) \<Rightarrow>
                if y \<notin> set vis then (y # nf, y # vis, par_extend p u y) else (nf, vis, p)) (nf, vis, p) (N u)
         = (nf1, vis1, p1)"
    by (rule prod_cases3)
  have inner: "(nf1, vis1) = foldl (\<lambda>x y. case x of (nf, vis) \<Rightarrow>
                  if y \<notin> set vis then (y # nf, y # vis) else (nf, vis)) (nf, vis) (N u)"
    using inner_fold_proj[of u nf vis p "N u"] unfolding eq prod.case .
  show ?case
    unfolding foldl_Cons prod.case eq inner[symmetric]
    by (rule Cons)
qed (simp only: foldl_Nil prod.case)

lemma next_frontier_and_current_unfold:
  fixes G::"nat \<Rightarrow> nat list option"
  shows "next_frontier_and_current cf vis =
   foldl (\<lambda>(nf, vis) u. 
       foldl (\<lambda>x y. case x of (nf, vis) \<Rightarrow> if y \<notin> set vis then (y # nf, y # vis) else (nf, vis))
            (nf, vis) (case G u of None \<Rightarrow> [] | Some ys \<Rightarrow> ys)) 
   ([], vis) (rev cf)"
  unfolding next_frontier_and_current_def Graph.neighbourhood_def 
  apply(rule fun_cong[of "foldl _ _" "foldl _ _"])
  apply(rule fun_cong[of "foldl _" "foldl _"])
  apply(rule arg_cong[of _ _ foldl])
  by fast

lemma next_frontier_current_parents_proj:
  fixes G::"nat \<Rightarrow> nat list option"
  shows "(\<lambda>(a, b, c). (a, b)) (next_frontier_current_parents G cf vis p) = next_frontier_and_current cf vis"
  unfolding next_frontier_and_current_unfold next_frontier_current_parents_def
  by (rule outer_fold_proj)

text \<open>The parent map after a round: it is still valid, keeps its roots, and its new edges lead
      from the vertices of the new frontier to vertices of the old one by reversing graph edges.\<close>

lemma next_frontier_current_parents_par:
  assumes "next_frontier_current_parents G cf vis p = (cf', vis', p')"
          "par_vis_inv p (set vis)" "set cf \<subseteq> set vis" "Vs G \<subseteq> par_U"
  shows "par_vis_inv p' (set vis')" "par_roots p' = par_roots p"
        "\<exists> Ex. par_abstract p' = par_abstract p \<union> Ex \<and>
            (\<forall> x \<in> set cf'. \<exists> x' \<in> set cf.
                x \<in> set (case G x' of None \<Rightarrow> [] | Some ys \<Rightarrow> ys) \<and> (x, x') \<in> Ex) \<and>
            (\<forall> x x'. (x, x') \<in> Ex \<longrightarrow>
                x \<in> set cf' \<and> x' \<in> set cf \<and> x \<in> set (case G x' of None \<Rightarrow> [] | Some ys \<Rightarrow> ys))"
proof-
  have NU: "\<forall> u \<in> set (rev cf). set (case G u of None \<Rightarrow> [] | Some ys \<Rightarrow> ys) \<subseteq> par_U"
    using Vs_nbs assms(4) by blast
  have "set [] \<subseteq> set vis" "set (rev cf) \<subseteq> set vis"
    using assms(3) by auto
  note all = outer_fold_par[OF assms(1)[unfolded next_frontier_current_parents_def]
                              this(1) assms(2) this(2) NU]
  show "par_vis_inv p' (set vis')" "par_roots p' = par_roots p"
    using all by blast+
  obtain Ex where Ex: "par_abstract p' = par_abstract p \<union> Ex" "set cf' = set [] \<union> fst ` Ex"
    "\<forall> y u. (y, u) \<in> Ex \<longrightarrow> u \<in> set (rev cf) \<and> y \<in> set (case G u of None \<Rightarrow> [] | Some ys \<Rightarrow> ys)"
    using all by (elim conjE exE) assumption
  have cf': "set cf' = fst ` Ex"
    using Ex(2) by (simp only: list.set(1) Un_empty_left)
  note E3 = Ex(3)[unfolded set_rev]
  show "\<exists> Ex. par_abstract p' = par_abstract p \<union> Ex \<and>
            (\<forall> x \<in> set cf'. \<exists> x' \<in> set cf.
                x \<in> set (case G x' of None \<Rightarrow> [] | Some ys \<Rightarrow> ys) \<and> (x, x') \<in> Ex) \<and>
            (\<forall> x x'. (x, x') \<in> Ex \<longrightarrow>
                x \<in> set cf' \<and> x' \<in> set cf \<and> x \<in> set (case G x' of None \<Rightarrow> [] | Some ys \<Rightarrow> ys))"
    unfolding cf'
  proof(intro exI[of _ Ex] conjI ballI allI impI)
    show "par_abstract p' = par_abstract p \<union> Ex"
      by (rule Ex(1))
  next
    fix x
    assume "x \<in> fst ` Ex"
    then obtain e where e: "e \<in> Ex" "x = fst e"
      by (rule imageE)
    then have xe: "(x, snd e) \<in> Ex"
      by simp
    note E = E3[rule_format, OF xe]
    show "\<exists> x' \<in> set cf. x \<in> set (case G x' of None \<Rightarrow> [] | Some ys \<Rightarrow> ys) \<and> (x, x') \<in> Ex"
      by (rule bexI[where x = "snd e"], rule conjI[OF conjunct2[OF E] xe], rule conjunct1[OF E])
  next
    fix x x'
    assume xx: "(x, x') \<in> Ex"
    note E = E3[rule_format, OF xx]
    show "x \<in> fst ` Ex" "x' \<in> set cf" "x \<in> set (case G x' of None \<Rightarrow> [] | Some ys \<Rightarrow> ys)"
      by (rule rev_image_eqI[OF xx], simp, rule conjunct1[OF E], rule conjunct2[OF E])
  qed
qed

lemma \<^marker>\<open>provenance ai_human\<close> next_frontier_current_parents_imp_rule[bfs_heap_rules]:
  fixes G::"nat \<Rightarrow> nat list option"
  assumes "finite (Vs G)" "next_frontier_current_parents G cf vis p = (cf', vis', p')"
          "nbs_invar G" "Vs G \<subseteq> K" "Vs G \<subseteq> par_U" "par_vis_inv p (set vis)" "set cf \<subseteq> set vis"
  shows 
    "<imp_cf_assn L Fr Bf G cf imp_cf * is_visited_set (Vs G) (set vis) imp_vis * 
      par_assn p pari * graph_assn G Gi>
    next_frontier_current_parents_imp Gi imp_cf imp_vis pari
    <\<lambda>(r1, r2, r3).
        imp_cf_assn L Fr Bf G cf' r1 * is_visited_set (Vs G) (set vis') r2 * 
        par_assn p' r3 * graph_assn G Gi>"
proof (cases imp_cf)
  case (fields fronti frontp buffer_fronti)
  have nf: "(cf', vis', p') = 
   foldl (\<lambda>(nf, vis, p) u. 
       foldl (\<lambda>x y. case x of (nf, vis, p) \<Rightarrow>
                if y \<notin> set vis then (y # nf, y # vis, par_extend p u y) else (nf, vis, p))
            (nf, vis, p) (case G u of None \<Rightarrow> [] | Some ys \<Rightarrow> ys)) 
   ([], vis, p) (rev cf)"
    using assms(2) unfolding next_frontier_current_parents_def by (rule sym)
  have pre: "imp_cf_assn L Fr Bf G cf (fronti, frontp, buffer_fronti) * 
      is_visited_set (Vs G) (set vis) imp_vis * par_assn p pari * graph_assn G Gi \<Longrightarrow>\<^sub>A
     graph_assn G Gi * is_visited_set (Vs G) (set vis) imp_vis *
      front_assn L buffer_fronti G (set vis) [] buffer_fronti 0 * par_assn p pari * 
      old_front_assn L G cf fronti frontp * \<up>({fronti, buffer_fronti} = {Fr, Bf})"
    unfolding front_assn_def old_front_assn_def imp_cf_assn.simps
    apply(subst only_in_univ)
    by sep_auto
  have post: "graph_assn G Gi * is_visited_set (Vs G) (set vis') imp_vis *
      front_assn L buffer_fronti G (set vis') cf' fronti' frontp' * par_assn p' pari * 
      old_front_assn L G cf fronti frontp * \<up>({fronti, buffer_fronti} = {Fr, Bf})
     \<Longrightarrow>\<^sub>A imp_cf_assn L Fr Bf G cf' (fronti', frontp', fronti) * is_visited_set (Vs G) (set vis') imp_vis *
      par_assn p' pari * graph_assn G Gi" for fronti' frontp'
    unfolding front_assn_def old_front_assn_def imp_cf_assn.simps
    using card_mono[OF assms(1), of "set vis'"]
    by (sep_auto simp: insert_commute)
  have nil: "set [] \<subseteq> set vis"
    by (simp only: list.set(1) empty_subsetI)
  show ?thesis
    unfolding fields next_frontier_current_parents_imp.simps
  proof(rule ht_bind[OF ht_cons_prec[OF pre ent_refl ht_frame[OF outer_loop_rule[OF nf assms(1,3-7) nil]]]], 
        goal_cases)
    case (1 x)
    show ?case
    proof(cases x)
      case (Pair fronti' frontp')
      show ?thesis
        unfolding Pair prod.case
        by (rule ht_cons_prec[OF post _ ht_return_sp]) sep_auto
    qed
  qed
qed


lemma Vs_same:"dVs (Graph.digraph_abs G) =  Vs G"
  unfolding Vs_def Graph.digraph_abs_def Graph.neighbourhood_def dVs_def verts_rw[of G]
  by order

text \<open>Introduction of the assertions from arrays allocated by the caller: a frontier array
      whose first cells hold the sources, together with a buffer, and an array of distances.\<close>

lemma imp_src_assn_intro:
  "\<lbrakk>card (Vs G) < length fl;
    card (Vs G) < length bl;
    length ss < length fl;
    take (length ss) fl = ss;
    set ss \<subseteq> Vs G;
    length fl = L;
    length bl = L\<rbrakk> \<Longrightarrow>
   Fr \<mapsto>\<^sub>a fl * Bf \<mapsto>\<^sub>a bl \<Longrightarrow>\<^sub>A imp_src_assn L Fr Bf G (rev ss) (Fr, length ss, Bf)"
  unfolding imp_src_assn_def imp_cf_assn.simps
  by (intro ent_ex_postI[where x = fl] ent_ex_postI[where x = bl])
     (unfold ent_pure_post_iff, simp add: ent_refl)

lemma imp_dist_assn_intro:
  "\<lbrakk>\<forall>i \<in> Vs G. i < length dl \<and> d i = dl ! i; length dl = L\<rbrakk> \<Longrightarrow> 
   Da \<mapsto>\<^sub>a dl \<Longrightarrow>\<^sub>A imp_dist_assn L Da G d Da"
  unfolding imp_dist_assn_def
  by (intro ent_ex_postI[where x = dl]) (unfold ent_pure_post_iff, intro conjI allI impI ent_refl refl)

text \<open>Conversely, the distances can be read off the array.\<close>

lemma imp_dist_assn_char:
  "imp_dist_assn L Dh G d Da = 
   (\<exists>\<^sub>A dl. Da \<mapsto>\<^sub>a dl * \<up>((\<forall>i \<in> Vs G. i < length dl \<and> d i = dl ! i) \<and> Da = Dh \<and> length dl = L))"
  by (rule imp_dist_assn_def)

end

text \<open>The parent array is initialised from the prefix of the frontier array that holds the
      sources.\<close>

fun par_init_imp where
  "par_init_imp (fronti, frontp, buffer_fronti) Pa = parent_array_init_imp (fronti, frontp) Pa"

text \<open>The instance for a fixed graph @{term G} with the heap handle @{term Gi}. The vertices are
      below @{term N}; the frontier and the buffer are the arrays @{term Fr} and @{term Bf} of
      length @{term "Suc N"}, the distances are kept in the array @{term Da} of length @{term N},
      and the parents in a parent array of length @{term N} (@{locale parent_array}). The arrays
      are thus independent of the graph and can be reused for searches on further graphs with
      vertices below @{term N}. The parent array is refined by the assertion @{term par_assn},
      for which the operations of the parent array are correct, e.g.\ by
      @{const parent_array.pa_parent_assn} itself or by a variant fixing the array handle.\<close>

locale BFS_lists_instance = BFS_subprocedures_lists where nbs_fold_imp = nbs_fold_imp
    and par_U = "{..<N}" and par_abstract = parent_array.pa_graph
    and par_extend = parent_array.pa_extend and par_invar = "parent_array.pa_invar N"
    and par_roots = parent_array.pa_roots and par_assn = par_assn
    and par_extend_imp = parent_array_extend_imp +
  par_static: Parent_Map_Spec_static_imp where U = "{..<N}" and to_dir_graph = parent_array.pa_graph
    and get_path = "parent_array.pa_get_path N" and invar = "parent_array.pa_invar N"
    and roots = parent_array.pa_roots and parent_assn = par_assn
    and get_path_imp = parent_array_get_path_imp
  for nbs_fold_imp :: "'g \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat array \<times> nat \<Rightarrow> (nat array \<times> nat) Heap) \<Rightarrow>
          nat array \<times> nat \<Rightarrow> (nat array \<times> nat) Heap"
    and N :: nat
    and par_assn :: "(nat \<Rightarrow> nat option) \<Rightarrow> nat array \<Rightarrow> assn" +
  fixes G :: "nat \<Rightarrow> nat list option"
    and Gi :: 'g
    and srcs :: "nat list"
    and Fr Bf Da :: "nat array"
  assumes Vs_bound: "Vs G \<subseteq> {..<N}"
    and G_invar: "nbs_invar G"
    and Vs_K: "Vs G \<subseteq> K"
    and par_init_rule: "\<And> R k xs Ra \<pi> \<pi>i.
          \<lbrakk>set R \<subseteq> {..<N}; k < length xs; set (take k xs) = set R\<rbrakk> \<Longrightarrow>
          <Ra \<mapsto>\<^sub>a xs * par_assn \<pi> \<pi>i> parent_array_init_imp (Ra, k) \<pi>i
          <\<lambda>_. Ra \<mapsto>\<^sub>a xs * par_assn (parent_array.pa_init R) \<pi>i>"
begin

interpretation pa: parent_array N .

lemma finite_Vs: "finite (Vs G)"
  using Vs_bound by (rule finite_subset) (rule finite_lessThan)

lemma Vs_U: "Vs G \<subseteq> U"
  using Vs_K K_U by (rule order.trans)


sublocale imp_bfs: BFS_Imperative
where empty = "\<lambda> x. None"
  and delete = "\<lambda> x M. \<lambda> y. if y = x then None else M y"
  and insert = Cons

  and isin = "\<lambda> xs x. x \<in> set xs"
  and t_set = set
  and sel = hd
  and  update = "\<lambda> x z M. \<lambda> y. if y = x then Some z else M y"
  and adjmap_inv = "\<lambda> _. True"
  and vset_empty = Nil
  and vset_delete = "\<lambda> x xs. filter (\<lambda> y. x \<noteq> y) xs"
  and vset_inv = "\<lambda> _. True"
  and union = append
  and inter = "\<lambda> xs ys. filter (\<lambda> y. y \<in> set ys) xs"
  and diff = "\<lambda> xs ys. filter (\<lambda> y. y \<notin> set ys) xs"
  and lookup = "\<lambda> M x. M x"
  and vset_inv2 = distinct
  and G = G
  and srcs = srcs
  and next_frontier_and_current = next_frontier_and_current
and next_frontier_current_parents = "next_frontier_current_parents G"
and next_frontier_current_parents_imp = "next_frontier_current_parents_imp Gi"
and imp_cf_assn = "imp_cf_assn (Suc N) Fr Bf G"
and expand_tree = expand_tree
and graph_assn = "\<lambda> G Gi. graph_assn G Gi"
and imp_vis_assn = "\<lambda> xs. is_visited_set (Vs G) (set xs)"
and G_imp = Gi
and imp_cf_is_empty = imp_cf_is_empty
and imp_src_assn = "imp_src_assn (Suc N) Fr Bf G"
and imp_src_to_cf = imp_src_to_cf
and set_srcs_visited = set_srcs_visited
and in_vis = "\<lambda>v visi. vis_isin_imp visi v"
and dist_invar = "\<lambda> d S. S \<subseteq> (Vs G)"
and dist_lookup = "\<lambda> d x. d x"
and set_all_dists_in_set = "\<lambda> d S n. \<lambda> y. if y \<in> set S then n else d y"
and some_dist = id
and imp_dist_assn = "imp_dist_assn N Da G"
and set_all_dists_in_front_imp = set_all_dists_in_front_imp
and U = "{..<N}"
and parent_abstract = parent_array.pa_graph
and parent_invar = "parent_array.pa_invar N"
and get_path = "parent_array.pa_get_path N"
and roots = parent_array.pa_roots
and parent_init = parent_array.pa_init
and parent_init_imp = par_init_imp
and get_path_imp = parent_array_get_path_imp
and imp_par_assn = par_assn
proof(unfold_locales, goal_cases)
  case (1 BFS_tree frontier vis)
  then show ?case 
    by blast
next
  case (2 BFS_tree frontier vis)
  then show ?case 
    using expand_tree(2) by presburger
next
  case (3 BFS_tree frontier vis)
  then show ?case 
     using expand_tree(3) by presburger   
next
  case (4 frontier vis front' vis')
  then show ?case 
    using next_frontier_and_curent_correct by blast
next
  case (5 frontier vis front' vis')
  then show ?case
    using next_frontier_and_curent_correct(2)[OF _ _ 5(3,4,5,6)] by blast
next
  case (6 frontier vis front' vis')
  show ?case 
    by (rule TrueI)
next
  case (7 frontier vis front' vis')
  then show ?case 
    using next_frontier_and_curent_correct(4)[OF _ _ 7(3,4,5,6)] by blast
next
  case (8 S)
  show ?case 
    by (rule TrueI)
next
  case (9 dists front S n)
  thus ?case 
    unfolding Vs_same by simp
next
  case (10 dists front S n x)
  thus ?case 
    by presburger
next
  case (11 dists front S n x)
  thus ?case 
    unfolding Vs_same 
    apply(subst if_not_P)
    by force+
next
  case 12
  thus ?case 
    by simp
next
  case (13 frontier vis par front' vis' par')
  show ?case
    using next_frontier_current_parents_proj[of G frontier vis par] unfolding 13(8) prod.case
    by (rule sym)
next
  case (14 frontier vis par front' vis' par')
  have "par_vis_inv par (set vis)"
    unfolding par_vis_inv_def using 14(6,7) by (rule conjI)
  note nf = next_frontier_current_parents_par(1)[OF 14(8) this 14(4) Vs_bound]
  show ?case
    using nf unfolding par_vis_inv_def by (rule conjunct1)
next
  case (15 frontier vis par front' vis' par')
  have "par_vis_inv par (set vis)"
    unfolding par_vis_inv_def using 15(6,7) by (rule conjI)
  note nf = next_frontier_current_parents_par(3)[OF 15(8) this 15(4) Vs_bound]
  have e: "x \<in> set (case G x' of None \<Rightarrow> [] | Some ys \<Rightarrow> ys) \<longleftrightarrow> (x', x) \<in> Graph.digraph_abs G"
    for x x'
    unfolding Graph.digraph_abs_def Graph.neighbourhood_def by (simp only: mem_Collect_eq case_prod_conv)
  show ?case
    using nf unfolding e .
next
  case (16 frontier vis par front' vis' par')
  have "par_vis_inv par (set vis)"
    unfolding par_vis_inv_def using 16(6,7) by (rule conjI)
  then show ?case
    by (rule next_frontier_current_parents_par(2)[OF 16(8) _ 16(4) Vs_bound])
next
  case 17
  show ?case
    unfolding Vs_same by (rule Vs_bound)
next
  case (18 \<pi> \<pi>i R Ri)
  obtain fronti frontp buffer_fronti where Ri: "Ri = (fronti, frontp, buffer_fronti)"
    by (cases Ri)
  have r: "<fronti \<mapsto>\<^sub>a fl * par_assn \<pi> \<pi>i> parent_array_init_imp (fronti, frontp) \<pi>i
           <\<lambda>_. fronti \<mapsto>\<^sub>a fl * par_assn (pa.pa_init R) \<pi>i>"
    if "frontp < length fl" "rev (take frontp fl) = R" for fl
  proof-
    have "set (take frontp fl) = set R"
      using arg_cong[OF that(2), where f = set] by (simp only: set_rev)
    then show ?thesis
      by (rule par_init_rule[OF 18(2) that(1)])
  qed
  show ?case
    unfolding Ri par_init_imp.simps imp_src_assn_def imp_cf_assn.simps
    by (sep_auto heap: r)
next
  case (19 S Si)
  show ?case 
    by (rule imp_cf_is_empty_rule)
next
  case (20 S Si)
  show ?case 
    unfolding imp_src_assn_def imp_src_to_cf_def
    by (rule ht_cons_prec[OF ent_refl _ ht_return_sp]) sep_auto
next
  case (21 empty_vis S Si)
  show ?case 
    using set_srcs_visited_rule[OF Vs_U, of "Suc N" Fr Bf S Si empty_vis] unfolding list.set(1) .
next
  case (22 cf imp_cf vis imp_vis par imp_par)
  have pv: "par_vis_inv par (set vis)"
    unfolding par_vis_inv_def using 22(5,6) by (rule conjI)
  have "next_frontier_current_parents G cf vis par =
        (fst (next_frontier_current_parents G cf vis par),
         fst (snd (next_frontier_current_parents G cf vis par)),
         snd (snd (next_frontier_current_parents G cf vis par)))"
    by (simp only: prod.collapse)
  then show ?case
    by (rule next_frontier_current_parents_imp_rule[OF finite_Vs _ G_invar Vs_K Vs_bound pv 22(3)])
next
  case (23 cf cfi n d id)
  show ?case 
    by (rule set_all_dists_in_front_imp_rule)
next 
  case (24 vis visi s)
  have s: "s \<in> Vs G"
    using 24 unfolding Vs_same .
  show ?case 
    by (rule ht_cons_prec[OF _ ent_refl vis_memb_rule[OF Vs_U, of "set vis" visi s]]) (sep_auto simp: s)
qed

end

end
