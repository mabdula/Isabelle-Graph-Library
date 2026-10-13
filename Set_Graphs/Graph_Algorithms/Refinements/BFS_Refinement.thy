theory BFS_Refinement
  imports Graph_Algorithms_Dev.BFS_3 BFS_Subprocedures  Directed_Set_Graphs.Pair_Graph_Imperative
 "HOL-Imperative_HOL.Imperative_HOL" "HOL-Library.IArray" 
  Imperative.Array_Range_Iteration
begin

lemma triple_res_ht_ex_pre_and_post_I:"(\<And> x. <P x> c <\<lambda> (r1,r2,r3). Q x r1 r2 r3>) 
           \<Longrightarrow> <\<exists>\<^sub>A x. P x> c <\<lambda> (r1,r2,r3). \<exists>\<^sub>A x. Q x r1 r2 r3>"
  by sep_auto

lemma "<a \<mapsto>\<^sub>a xs * a' \<mapsto>\<^sub>a xs' * \<up> (i < length xs \<and> j < length xs')>
       do {Array.upd i x a; Array.upd j x' a'}
      <\<lambda> r. a \<mapsto>\<^sub>a xs[i:=x] * r \<mapsto>\<^sub>a xs'[j:=x'] * \<up> (i < length xs \<and> j < length xs')>"
  by sep_auto

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
and dist_lookup_imp::"'imp_dist \<Rightarrow> 'ver \<Rightarrow> nat Heap"
and parent_lookup_imp::"'imp_par \<Rightarrow> 'ver \<Rightarrow> 'ver Heap"
begin

partial_function (heap) BFS_par_imp::
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

text \<open>Path reconstruction on the final distances and parents: going back from @{term v} along the
      parents until a vertex of distance \<open>0\<close>, the vertices are written into the array
      @{term Ra} given by the caller, from position @{term k} on. The path thus ends up reversed in
      the array. The result is the position after the last vertex written. Mirrors
      @{const BFS_distance_parents.parent_path}.\<close>

partial_function (heap) path_rev_imp :: "'imp_dist \<Rightarrow> 'imp_par \<Rightarrow> 'ver array \<Rightarrow> 'ver \<Rightarrow> nat \<Rightarrow> nat Heap"
  where
  "path_rev_imp di pari Ra v k =
     do { Array.upd k v Ra;
          dv \<leftarrow> dist_lookup_imp di v;
          if dv = 0 then return (Suc k)
          else do { u \<leftarrow> parent_lookup_imp pari v;
                    path_rev_imp di pari Ra u (Suc k) } }"

definition "path_imp di pari Ra v = path_rev_imp di pari Ra v 0"
end

locale BFS_Imperative = 
 BFS_3.BFS_distance_parents  where expand_tree = expand_tree and insert = insert and some_dist = some_dist
  and next_frontier_current_parents = next_frontier_current_parents +
 BFS_Imperative_spec where  imp_src_to_cf = imp_src_to_cf
  and in_vis = in_vis and set_all_dists_in_front_imp = set_all_dists_in_front_imp
  and next_frontier_current_parents_imp = next_frontier_current_parents_imp
 for  imp_src_to_cf :: "'imp_src \<Rightarrow> 'imp_cf Heap"
  and expand_tree::"'adjmap \<Rightarrow> 'vset \<Rightarrow> 'vset \<Rightarrow> 'adjmap"
  and insert :: "'ver::heap \<Rightarrow> 'vset \<Rightarrow> 'vset" 
  and in_vis::"'ver \<Rightarrow> 'imp_vis \<Rightarrow> bool Heap"
  and some_dist::"'dist" and set_all_dists_in_front_imp::"'imp_dist \<Rightarrow> 'imp_cf \<Rightarrow> nat \<Rightarrow> 'imp_dist Heap"
  and next_frontier_current_parents :: "'vset \<Rightarrow> 'vset \<Rightarrow> 'par \<Rightarrow> 'vset \<times> 'vset \<times> 'par"
  and next_frontier_current_parents_imp ::
      "'imp_cf \<Rightarrow> 'imp_vis \<Rightarrow> 'imp_par \<Rightarrow> ('imp_cf \<times> 'imp_vis \<times> 'imp_par) Heap" +
fixes  G_imp::"'imp_G"
 and graph_assn::"'adjmap \<Rightarrow> 'imp_G \<Rightarrow> assn"
 and imp_src_assn::"'vset \<Rightarrow> 'imp_src \<Rightarrow> assn"
 and imp_cf_assn::"'vset \<Rightarrow> 'imp_cf \<Rightarrow> assn"
 and imp_vis_assn::"'vset \<Rightarrow> 'imp_vis \<Rightarrow> assn"
 and imp_dist_assn::"'dist \<Rightarrow> 'imp_dist \<Rightarrow> assn"
 and imp_par_assn::"'par \<Rightarrow> 'imp_par \<Rightarrow> assn"
assumes imp_sf_is_empty: "\<And> S Si. <imp_cf_assn S Si> imp_cf_is_empty Si 
                       <\<lambda> b. imp_cf_assn S Si * \<up>(b \<longleftrightarrow> S = \<emptyset>\<^sub>N)>"
 and imp_src_to_cf: "\<And> S Si. <imp_src_assn S Si> imp_src_to_cf Si 
                      <\<lambda> r. imp_cf_assn S r>"
 and set_srcs_visited: 
  "\<And> S Si. 
    <imp_src_assn S Si * imp_vis_assn vset_empty empty_vis> set_srcs_visited empty_vis Si 
           <\<lambda> r. imp_vis_assn S r * imp_src_assn S Si>"
 and next_frontier_current_parents_imp:  "\<And> cf imp_cf vis imp_vis par imp_par.
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
and dist_lookup_imp_rule: "\<And>d di x. x \<in> dVs (Graph.digraph_abs G) \<Longrightarrow>
     <imp_dist_assn d di> dist_lookup_imp di x <\<lambda> r. imp_dist_assn d di * \<up> (r = dist_lookup d x)>"
and parent_lookup_imp_rule: "\<And>p pari x. x \<in> dVs (Graph.digraph_abs G) \<Longrightarrow>
     <imp_par_assn p pari> parent_lookup_imp pari x
     <\<lambda> r. imp_par_assn p pari * \<up> (r = parent_lookup p x)>"
begin

definition "state_assn (s::('dist, 'vset, 'par) BFS_par_state)
    (imp_s::('imp_dist, 'imp_vis, 'imp_cf, 'imp_par) BFS_state_imp) = 
  (imp_vis_assn (BFS_dist_state.visited s) (BFS_state_imp.visited imp_s) *
   imp_cf_assn (BFS_dist_state.current s) (BFS_state_imp.current imp_s)*
   imp_dist_assn (BFS_dist_state.dists s) (BFS_state_imp.dists imp_s) *
   imp_par_assn (BFS_par_state.parent s) (BFS_state_imp.parent imp_s) *
    \<up> (BFS_dist_state.current_dist s = BFS_state_imp.current_dist imp_s))"

lemma BFS_refine:
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
      using next_frontier_current_parents_imp IH  imp_sf_is_empty set_all_dists_in_front_imp
      apply(auto split!: if_split prod.split simp add: state_assn_def Let_def mod_pure_star_dist)
      by sep_auto
    done
qed

lemma initial_refine:
 "<imp_vis_assn vset_empty empty_vis* imp_src_assn srcs srcs_imp * imp_dist_assn some_dist imp_some_dist
   * imp_par_assn some_parent imp_some_par>
  initial_state_imp empty_vis srcs_imp imp_some_dist imp_some_par
 <\<lambda> si. state_assn initial_par_state si>"
  apply(auto simp add: initial_par_state_def state_assn_def initial_state_imp_def)
  using imp_src_to_cf set_all_dists_in_front_imp set_srcs_visited 
  by sep_auto

lemma BFS_program_behaviour:
  "<imp_vis_assn vset_empty empty_vis * imp_src_assn srcs srcs_imp * imp_dist_assn some_dist imp_some_dist
    * imp_par_assn some_parent imp_some_par * graph_assn G G_imp>
   do { si \<leftarrow> initial_state_imp empty_vis srcs_imp imp_some_dist imp_some_par;
        BFS_par_imp si }
   < \<lambda> si'. state_assn (BFS_par_impl initial_par_state) si' * graph_assn G G_imp>"
  using initial_refine BFS_refine 
  by sep_auto

lemma check_reachable_rule:
  assumes "t \<in> dVs (Graph.digraph_abs G)"
  shows
 "<imp_vis_assn vset_empty empty_vis * imp_src_assn srcs srcs_imp * imp_dist_assn some_dist imp_some_dist
   * imp_par_assn some_parent imp_some_par * graph_assn G G_imp> 
   check_reachable empty_vis srcs_imp imp_some_dist imp_some_par t
  <\<lambda> b.  graph_assn G G_imp *
      \<up> (b \<longleftrightarrow> isin (BFS_dist_state.visited (BFS_par_impl initial_par_state)) t)>" 
  unfolding check_reachable_def
  using initial_refine BFS_refine in_vis_rule[OF assms]
  by (sep_auto simp: state_assn_def)

lemma visited_dists_parents_imp_rule:
 "<imp_vis_assn vset_empty empty_vis * imp_src_assn srcs srcs_imp * imp_dist_assn some_dist imp_some_dist
   * imp_par_assn some_parent imp_some_par * graph_assn G G_imp> 
   visited_dists_parents_imp empty_vis srcs_imp imp_some_dist imp_some_par
  <\<lambda> (visi, di, pari). graph_assn G G_imp *
      imp_vis_assn (BFS_dist_state.visited (BFS_par_impl initial_par_state)) visi *
      imp_dist_assn (BFS_dist_state.dists (BFS_par_impl initial_par_state)) di *
      imp_par_assn (BFS_par_state.parent (BFS_par_impl initial_par_state)) pari>" 
  unfolding visited_dists_parents_imp_def
  using initial_refine BFS_refine
  by (sep_auto simp: state_assn_def)

text \<open>The same, but the final frontier is kept as well, so that its arrays can be reused.\<close>

lemma visited_dists_parents_imp_frontier_rule:
 "<imp_vis_assn vset_empty empty_vis * imp_src_assn srcs srcs_imp * imp_dist_assn some_dist imp_some_dist
   * imp_par_assn some_parent imp_some_par * graph_assn G G_imp> 
   visited_dists_parents_imp empty_vis srcs_imp imp_some_dist imp_some_par
  <\<lambda> (visi, di, pari). graph_assn G G_imp *
      imp_vis_assn (BFS_dist_state.visited (BFS_par_impl initial_par_state)) visi *
      imp_dist_assn (BFS_dist_state.dists (BFS_par_impl initial_par_state)) di *
      imp_par_assn (BFS_par_state.parent (BFS_par_impl initial_par_state)) pari *
      (\<exists>\<^sub>A cf cfi. imp_cf_assn cf cfi)>" 
  unfolding visited_dists_parents_imp_def
  using initial_refine BFS_refine
  by (sep_auto simp: state_assn_def)

text \<open>The main properties of @{thm [source] BFS_par_correct} carry over to the returned visited
      set, distances and parents.\<close>

theorem visited_dists_parents_imp_correct:
  assumes BFS_axiom
  shows
 "<imp_vis_assn vset_empty empty_vis * imp_src_assn srcs srcs_imp * imp_dist_assn some_dist imp_some_dist
   * imp_par_assn some_parent imp_some_par * graph_assn G G_imp>
   visited_dists_parents_imp empty_vis srcs_imp imp_some_dist imp_some_par
  <\<lambda> (visi, di, pari). \<exists>\<^sub>A vis d p. graph_assn G G_imp * imp_vis_assn vis visi *
      imp_dist_assn d di * imp_par_assn p pari *
      \<up>((\<forall> x. x \<in> t_set vis \<longleftrightarrow> (\<exists>u \<in> t_set srcs. \<exists>q. vwalk_bet (Graph.digraph_abs G) u q x)) \<and>
         (\<forall> x \<in> t_set vis. dist_lookup d x = distance_set (Graph.digraph_abs G) (t_set srcs) x) \<and>
         (\<forall> x \<in> t_set vis - t_set srcs.
             parent_lookup p x \<in> t_set vis \<and> (parent_lookup p x, x) \<in> Graph.digraph_abs G \<and>
             distance_set (Graph.digraph_abs G) (t_set srcs) x =
               distance_set (Graph.digraph_abs G) (t_set srcs) (parent_lookup p x) + 1) \<and>
         (\<forall> x \<in> t_set vis. \<exists>u \<in> t_set srcs.
             vwalk_bet (Graph.digraph_abs G) u (parent_path d p x []) x \<and>
             length (parent_path d p x []) - 1 = distance_set (Graph.digraph_abs G) (t_set srcs) x))>"
  using BFS_par_correct[OF assms refl]
  by (sep_auto heap: visited_dists_parents_imp_rule)

text \<open>If the distances and parents refine those of the final state, @{const path_rev_imp} writes
      the reconstructed path to a visited vertex @{term v}, reversed, into the array from position
      @{term k} on.\<close>

lemma path_rev_imp_rule:
  assumes BFS_axiom "final_state = BFS_par_impl initial_par_state"
  shows "\<lbrakk>v \<in> t_set (BFS_dist_state.visited final_state);
          k + length (parent_path (BFS_dist_state.dists final_state) (BFS_par_state.parent final_state) v [])
            \<le> length r\<rbrakk> \<Longrightarrow>
   <imp_dist_assn (BFS_dist_state.dists final_state) di *
    imp_par_assn (BFS_par_state.parent final_state) pari * Ra \<mapsto>\<^sub>a r>
     path_rev_imp di pari Ra v k
   <\<lambda>k'. imp_dist_assn (BFS_dist_state.dists final_state) di *
        imp_par_assn (BFS_par_state.parent final_state) pari *
        Ra \<mapsto>\<^sub>a (take k r @
                 rev (parent_path (BFS_dist_state.dists final_state) (BFS_par_state.parent final_state) v []) @
                 drop (k + length (parent_path (BFS_dist_state.dists final_state)
                                     (BFS_par_state.parent final_state) v [])) r) *
        \<up>(k' = k + length (parent_path (BFS_dist_state.dists final_state)
                               (BFS_par_state.parent final_state) v []))>"
proof(induction "dist_lookup (BFS_dist_state.dists final_state) v" arbitrary: v k r rule: less_induct)
  case less
  have vG: "v \<in> dVs (Graph.digraph_abs G)"
    using parent_path_acc[OF assms less.prems(1), of "[]"] by (blast dest: vwalk_bet_endpoints(2))
  have k: "k < length r"
    using less.prems(2) parent_path_acc[OF assms less.prems(1), of "[]"] by simp
  show ?case
  proof(cases "dist_lookup (BFS_dist_state.dists final_state) v = 0")
    case True
    note rp = parent_path_step(1)[OF assms less.prems(1) True]
    show ?thesis
      unfolding rp
      by (subst path_rev_imp.simps)
         (sep_auto heap: dist_lookup_imp_rule[OF vG] simp: True k upd_conv_take_nth_drop)
  next
    case False
    let ?p = "parent_lookup (BFS_par_state.parent final_state) v"
    note step = parent_path_step(2)[OF assms less.prems(1) False]
    have p: "?p \<in> t_set (BFS_dist_state.visited final_state)"
            "dist_lookup (BFS_dist_state.dists final_state) ?p <
             dist_lookup (BFS_dist_state.dists final_state) v"
      using step by simp_all
    have rp: "parent_path (BFS_dist_state.dists final_state) (BFS_par_state.parent final_state) v [] =
              parent_path (BFS_dist_state.dists final_state) (BFS_par_state.parent final_state) ?p [] @ [v]"
      using step by simp
    have len: "Suc k + length (parent_path (BFS_dist_state.dists final_state)
                                 (BFS_par_state.parent final_state) ?p []) \<le> length (r[k := v])"
      using less.prems(2) rp by simp
    have tu: "list_update (take (Suc k) r) k v = take k r @ [v]"
      using k by (simp add: take_Suc_conv_app_nth list_update_append)
    have dv: "drop (Suc (k + length (parent_path (BFS_dist_state.dists final_state)
                                        (BFS_par_state.parent final_state) ?p []))) (r[k := v]) =
              drop (Suc (k + length (parent_path (BFS_dist_state.dists final_state)
                                        (BFS_par_state.parent final_state) ?p []))) r"
      by (rule drop_update_cancel) simp
    show ?thesis
      by (subst path_rev_imp.simps)
         (sep_auto heap: dist_lookup_imp_rule[OF vG] parent_lookup_imp_rule[OF vG]
                         less.hyps[OF p(2) p(1) len] simp: False k rp tu dv)
  qed
qed

text \<open>Given distances and parents that refine those of the final state and an array with at
      least as many cells as the graph has vertices, @{const path_imp} writes the path to a
      visited vertex @{term v}, reversed, into the first cells of the array and returns its length.
      It is the path @{const parent_path} reconstructs, hence a shortest path from the sources.\<close>

theorem path_imp_correct:
  assumes BFS_axiom "final_state = BFS_par_impl initial_par_state"
          "v \<in> t_set (BFS_dist_state.visited final_state)" "card (dVs (Graph.digraph_abs G)) \<le> length r"
  shows "<imp_dist_assn (BFS_dist_state.dists final_state) di *
          imp_par_assn (BFS_par_state.parent final_state) pari * Ra \<mapsto>\<^sub>a r>
           path_imp di pari Ra v
         <\<lambda>k. imp_dist_assn (BFS_dist_state.dists final_state) di *
              imp_par_assn (BFS_par_state.parent final_state) pari *
              (\<exists>\<^sub>A ps. Ra \<mapsto>\<^sub>a ps * \<up>(length ps = length r \<and>
                 rev (take k ps) =
                   parent_path (BFS_dist_state.dists final_state) (BFS_par_state.parent final_state) v [] \<and>
                 (\<exists>u \<in> t_set srcs. vwalk_bet (Graph.digraph_abs G) u (rev (take k ps)) v \<and>
                    k - 1 = distance_set (Graph.digraph_abs G) (t_set srcs) v)))>"
proof-
  have b: "length (parent_path (BFS_dist_state.dists final_state) (BFS_par_state.parent final_state) v [])
             \<le> length r"
    using parent_path_length[OF assms(1-3)] assms(4) by linarith
  show ?thesis
    unfolding path_imp_def
    using BFS_par_correct(4)[OF assms(1-3)] b
    by (sep_auto heap: path_rev_imp_rule[OF assms(1-3), where k = 0, simplified])
qed

end
locale imp_fixed_univ_set =
  fixes is_fixed_univ_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 's \<Rightarrow> assn"
  assumes only_in_univ: "is_fixed_univ_set U S Si = (is_fixed_univ_set U S Si * \<up> (S \<subseteq> U))"
(*
locale imp_set_empty = imp_set +
  constrains is_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 's \<Rightarrow> assn"
  fixes empty :: "'s Heap"
  and U::"'a set"
  assumes empty_rule[sep_heap_rules]: "<emp> empty <is_set {}>"
*)(*
locale imp_fixed_univ_set_is_empty = imp_fixed_univ_set +
  constrains is_fixed_univ_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 's \<Rightarrow> assn"
  fixes is_empty :: "'s \<Rightarrow> bool Heap"
  assumes is_empty_rule[sep_heap_rules]: 
    "<is_fixed_univ_set U s p> is_empty p <\<lambda>r. is_fixed_univ_set U s p * \<up>(r \<longleftrightarrow> s={})>"
*)
locale imp_fixed_univ_set_memb = imp_fixed_univ_set +
  constrains is_fixed_univ_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 's \<Rightarrow> assn"
  fixes memb :: "'a \<Rightarrow> 's \<Rightarrow> bool Heap"
  assumes memb_rule[sep_heap_rules]: 
    "<is_fixed_univ_set U s p * \<up> (a \<in> U)> memb a p <\<lambda>r. is_fixed_univ_set U s p * \<up>(r \<longleftrightarrow> a \<in> s)>"

locale imp_fixed_univ_set_ins = imp_fixed_univ_set +
  constrains is_fixed_univ_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 's \<Rightarrow> assn"
  fixes ins :: "'a \<Rightarrow> 's \<Rightarrow> 's Heap"
  assumes ins_rule[sep_heap_rules]: 
    "<is_fixed_univ_set U s p * \<up> (a \<in> U)> ins a p <is_fixed_univ_set U (Set.insert a s)>"

locale imp_fixed_univ_set_distinct_ins = imp_fixed_univ_set +
  constrains is_fixed_univ_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 's \<Rightarrow> assn"
  fixes distinct_ins :: "'a \<Rightarrow> 's \<Rightarrow> 's Heap"
  assumes distinct_ins_rule[sep_heap_rules]: 
    "<is_fixed_univ_set U s p * \<up> (a \<in> U \<and> a \<notin> s)> distinct_ins a p <is_fixed_univ_set U (Set.insert a s)>"

locale imp_fixed_univ_set_rest = imp_fixed_univ_set +
  constrains is_fixed_univ_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 's \<Rightarrow> assn"
  fixes reset :: "'s \<Rightarrow> 's Heap"
  assumes ins_rule[sep_heap_rules]: 
    "<is_fixed_univ_set U s p > reset p <is_fixed_univ_set U {}>"
  


text \<open>The code locale of the subprocedures: it only fixes the operations of the visited set and the
      iteration over the neighbours of a vertex in the graph, and has no assumptions, so that it can
      be globally interpreted for code generation.\<close>

locale BFS_subprocedures_lists_code =
  fixes visited_memb :: "nat \<Rightarrow> 'imp_vis \<Rightarrow> bool Heap"
    and distinct_ins :: "nat \<Rightarrow> 'imp_vis \<Rightarrow> 'imp_vis Heap"
    and iterate_neighbourhood :: "'g \<Rightarrow> nat \<Rightarrow>
          (nat \<Rightarrow> nat \<Rightarrow> nat array \<times> nat \<times> 'imp_vis \<Rightarrow> (nat array \<times> nat \<times> 'imp_vis) Heap) \<Rightarrow>
          nat array \<times> nat \<times> 'imp_vis \<Rightarrow> (nat array \<times> nat \<times> 'imp_vis) Heap"
begin

text \<open>The parent array is updated in place and its handle is not part of the accumulator,
      so no larger tuple is built per edge.\<close>

fun inner_loop where
"inner_loop Gi pari u (front, frontpt, vis) =
   iterate_neighbourhood Gi u 
     (\<lambda> u v (front, frontpt, vis) . 
          do {b \<leftarrow> visited_memb v vis;
              if \<not> b then do { front' \<leftarrow> Array.upd frontpt v front;
                               vis' \<leftarrow> distinct_ins v vis;
                               Array.upd v u pari;
                               return (front', Suc frontpt, vis')}
              else return (front, frontpt, vis)})
      (front, frontpt, vis)"

fun outer_loop where
  "outer_loop Gi pari (old_front, old_frontp) (front, frontpt, vis) = 
    do{iterate_range_strict old_front 0 old_frontp 
             (inner_loop Gi pari) (front, frontpt, vis)}"

definition "imp_src_to_cf = (\<lambda> x. return x)"

fun imp_cf_is_empty where
 "imp_cf_is_empty (fronti, frontp, buffer_fronti) = 
          return (frontp = 0)"

fun set_srcs_visited where
  "set_srcs_visited (imp_vis::'imp_vis) (fronti, frontp, buffer_fronti) =
   do { iterate_range_strict fronti 0 frontp 
             (\<lambda> v vis. do {b \<leftarrow> visited_memb v vis;
                           if \<not> b then distinct_ins v vis
                           else return vis})
             imp_vis}"

fun set_all_dists_in_front_imp where
 "set_all_dists_in_front_imp di (fronti, frontp, buffer_fronti) n = 
       iterate_range_strict fronti 0 frontp 
         (\<lambda> v di. Array.upd v n di) di"

fun next_frontier_current_parents_imp where
  "next_frontier_current_parents_imp Gi (fronti, frontp, buffer_fronti) imp_vis pari =
   do{
      (front', frontpt', vis') \<leftarrow> 
       outer_loop Gi pari (fronti, frontp) (buffer_fronti, 0, imp_vis);
      return ((front', frontpt', fronti), vis', pari)}"

end

text \<open>The proof locale adds the Hoare triples of the visited set and of the iteration over the
      neighbours: the latter folds a function over the neighbour list of the vertex.\<close>

locale BFS_subprocedures_lists =
  BFS_subprocedures_lists_code where visited_memb = visited_memb and distinct_ins = distinct_ins
    and iterate_neighbourhood = iterate_neighbourhood +
  imp_fixed_univ_set_memb where is_fixed_univ_set = is_visited_set
  and memb = visited_memb +
  imp_fixed_univ_set_distinct_ins where is_fixed_univ_set = is_visited_set
  and distinct_ins = distinct_ins
for is_visited_set and visited_memb::"nat \<Rightarrow> 'imp_vis \<Rightarrow> bool Heap"
  and distinct_ins :: "nat \<Rightarrow> 'imp_vis \<Rightarrow> 'imp_vis Heap"
  and iterate_neighbourhood :: "'g \<Rightarrow> nat \<Rightarrow>
          (nat \<Rightarrow> nat \<Rightarrow> nat array \<times> nat \<times> 'imp_vis \<Rightarrow> (nat array \<times> nat \<times> 'imp_vis) Heap) \<Rightarrow>
          nat array \<times> nat \<times> 'imp_vis \<Rightarrow> (nat array \<times> nat \<times> 'imp_vis) Heap" +
  fixes graph_assn :: "(nat \<Rightarrow> nat list option) \<Rightarrow> 'g \<Rightarrow> assn"
  assumes iterate_neighbourhood_rule:
    "(\<And> acc acci x vs. \<lbrakk>nhlists v = Some vs; x \<in> set vs\<rbrakk> \<Longrightarrow>
        <acc_assn acc acci * F> fi v x acci <\<lambda> r. acc_assn (f v acc x) r * F>) \<Longrightarrow>
     <graph_assn nhlists Gi *
      (acc_assn :: nat list \<times> nat list \<times> (nat \<Rightarrow> nat) \<Rightarrow> nat array \<times> nat \<times> 'imp_vis \<Rightarrow> assn) acc acci * F>
       iterate_neighbourhood Gi v fi acci
     <\<lambda> r. graph_assn nhlists Gi * F *
           acc_assn (foldl (f v) acc (case nhlists v of None \<Rightarrow> [] | Some vs \<Rightarrow> vs)) r>"
begin

definition "Vs (G::nat \<Rightarrow> nat list option) = \<Union> {{u, v} | u v vs. G u = Some vs \<and> v \<in> set vs }"


text \<open>The arrays have the fixed lengths @{term L} and the fixed handles given by the caller, so
      that they can be reused for further searches on other graphs.\<close>

definition "front_assn L Fh G vis (front::nat list) fronti frontp = 
  (\<exists>\<^sub>A frontlist. fronti \<mapsto>\<^sub>a frontlist * \<up> (length frontlist > card (Vs G) \<and>
     frontp < length frontlist - card (Vs G) + card vis \<and> frontp \<le> length frontlist \<and>
        rev (take frontp (frontlist)) = front
     \<and> vis \<subseteq> (Vs G) \<and> set front \<subseteq> (Vs G) \<and> length frontlist = L \<and> fronti = Fh))"

definition "imp_par_assn L Pa G p pari 
   = (\<exists>\<^sub>A plist. pari \<mapsto>\<^sub>a plist *
          \<up>((\<forall> i \<in> Vs G. i < length plist \<and> p i = plist ! i) \<and> pari = Pa \<and> length plist = L))"

lemma imp_par_upd_rule[sep_heap_rules]:
  "x \<in> Vs G \<Longrightarrow>
   <imp_par_assn L Pa G p pari> Array.upd x u pari 
   <\<lambda> r. imp_par_assn L Pa G (p(x := u)) pari * \<up> (r = pari)>"
  unfolding imp_par_assn_def
  by (sep_auto simp: nth_list_update)

lemma inner_loop_rule:
  assumes "(front', vis', p') = 
          foldl (\<lambda>x y. case x of (nf, vis, p) \<Rightarrow>
                   if y \<notin> set vis then (y # nf, y # vis, p(y := u)) else (nf, vis, p))
            (front, vis, p) (case G u of None \<Rightarrow> [] | Some ys \<Rightarrow> ys)"
          "finite (Vs G)"
  shows "<graph_assn G Gi
          * is_visited_set (Vs G) (set vis) visi * front_assn L Fh G (set vis) front fronti frontp
          * imp_par_assn L' Pa G p pari>
  inner_loop Gi pari u (fronti, frontp, visi)
 <\<lambda> (fronti', frontp', visi'). 
   graph_assn G Gi
       * is_visited_set (Vs G) (set vis') visi' * front_assn L Fh G (set vis') front' fronti' frontp'
       * imp_par_assn L' Pa G p' pari>"
proof-
  define acc_assn where 
    "acc_assn = (\<lambda> (front, vis, p) (fronti, frontp, visi). 
        is_visited_set (Vs G) (set vis) visi * front_assn L Fh G (set vis) front fronti frontp
        * imp_par_assn L' Pa G p pari)"
  define fi where "fi = (\<lambda> (u::nat) (v::nat) (front, frontpt, vis) . 
          do {b \<leftarrow> visited_memb v vis;
              if \<not> b then do { front' \<leftarrow> Array.upd frontpt v front;
                               vis' \<leftarrow> distinct_ins v vis;
                               Array.upd v u pari;
                               return (front', Suc frontpt, vis')}
              else return (front, frontpt, vis)})"
  define f where "f = (\<lambda>(nf, vis, p) y. if (y::nat) \<notin> set vis then (y # nf, y # vis, p(y := u))
                                        else (nf, vis, p))"
  have assms_1': "(front', vis', p') = 
          foldl f (front, vis, p) (case G u of None \<Rightarrow> [] | Some ys \<Rightarrow> ys)"
    using assms(1) by(auto simp add: f_def case_prod_unfold)
  show ?thesis
    unfolding inner_loop.simps fi_def[symmetric]
    apply(rule ht_cons_prec)
      defer
      defer
      apply(rule iterate_neighbourhood_rule[where F = emp and acc_assn = acc_assn, simplified,
          where fi = fi and nhlists = G
           and acc = "(front, vis, p)" and f = "\<lambda> x. f"])
    subgoal for acc acci x vs
    proof(cases acc, cases acci, goal_cases)
      case (1 front vis p fronti frontp visi)
      have x_in_Vs: "x \<in> (Vs G)" 
        using 1(1,2)
        by(auto simp add: Vs_def)
      show ?case 
        unfolding 1
        unfolding acc_assn_def front_assn_def
        unfolding acc_assn_def f_def fi_def 
        unfolding prod.case front_assn_def ex_assn_move_out(2)
      proof(cases "x \<notin> set vis", goal_cases)
        case 1
        show ?case
          apply(subst (2) if_P)
           using 1 apply force
           unfolding prod.case 
           using x_in_Vs 1 distinct_ins_rule[of "(Vs G)" "set vis" visi x] apply sep_auto
           subgoal for xa h ha r hb 
            apply(rule mod_exI[of _ "xa[frontp := x]"])
            apply (sep_auto simp: mod_pure_star_dist)
            apply(subst take_Suc_conv_app_nth)
            apply simp
            by (metis take_Suc_conv_app_nth take_update_last)
           subgoal
             using 1 by simp
           done
       next
         case 2
         thus ?case
           by sep_auto
       qed
     qed
     subgoal
       unfolding acc_assn_def prod.case 
       by sep_auto
     subgoal for x
       apply(clarsimp split!: option.split prod.split)
       subgoal for front frontpt vis
         unfolding acc_assn_def front_assn_def prod.case ex_assn_move_out(2)
         using assms(1)
         by sep_auto
       subgoal for vs front frontpt vis
         unfolding acc_assn_def front_assn_def prod.case
         apply(clarsimp split!: option.split prod.split)
         subgoal premises prems for a b c
         proof-
           have "(front', vis', p') = (a, b, c)"
             using prems by (simp add: assms_1')
           thus ?thesis
             by sep_auto
         qed
         done
       done
     done
 qed


definition "old_front_assn L G (front::nat list) fronti frontp = 
  (\<exists>\<^sub>A frontlist. 
    fronti \<mapsto>\<^sub>a frontlist * \<up> ( frontp < length frontlist \<and> rev (take frontp (frontlist)) = front
    \<and> card (Vs G) < length frontlist \<and> length frontlist = L))"

lemma outer_loop_rule:
  assumes "(front', vis', p') = 
   foldl (\<lambda>(nf, vis, p) u. 
       foldl (\<lambda>x y. case x of (nf, vis, p) \<Rightarrow>
                if y \<notin> set vis then (y # nf, y # vis, p(y := u)) else (nf, vis, p))
            (nf, vis, p) (case G u of None \<Rightarrow> [] | Some ys \<Rightarrow> ys)) 
   (front, vis, p) (rev old_front)"
          "finite (Vs G)"
  shows "<graph_assn G Gi
          * is_visited_set (Vs G) (set vis) visi * front_assn L Fh G (set vis) front fronti frontp
          * imp_par_assn L' Pa G p pari * old_front_assn L G old_front old_fronti old_frontp>
  outer_loop Gi pari (old_fronti, old_frontp) (fronti, frontp, visi)
 <\<lambda> (fronti', frontp', visi'). 
   graph_assn G Gi
       * is_visited_set (Vs G) (set vis') visi' * front_assn L Fh G (set vis') front' fronti' frontp'
       * imp_par_assn L' Pa G p' pari * old_front_assn L G old_front old_fronti old_frontp>"
proof-
  define acc_assn where 
    "acc_assn = (\<lambda> (front, vis, p) (fronti, frontp, visi). 
        is_visited_set (Vs G) (set vis) visi * front_assn L Fh G (set vis) front fronti frontp
        * imp_par_assn L' Pa G p pari)"
  define f where "f = (\<lambda>  (nf, vis, p) u.
      foldl (\<lambda>x y. case x of (nf, vis, p) \<Rightarrow>
               if y \<notin> set vis then (y # nf, y # vis, p(y := u)) else (nf, vis, p))
            (nf, vis, p) (case G u of None \<Rightarrow> [] | Some ys \<Rightarrow> ys))"
  show ?thesis
    unfolding outer_loop.simps 
    unfolding old_front_assn_def ex_assn_move_out(2)
    apply(rule triple_res_ht_ex_pre_and_post_I)
    subgoal for old_front_list
    apply(rule ht_cons_prec)
      defer
    defer
      apply(rule iterate_range_strict_rule[of old_front_list 0 old_frontp acc_assn 
          "graph_assn G Gi 
           * \<up> (old_frontp < length old_front_list \<and> rev (take old_frontp (old_front_list)) = old_front
                \<and> card (Vs G) < length old_front_list \<and> length old_front_list = L)" 
           "inner_loop Gi pari" f old_fronti "(front, vis, p)" "(fronti, frontp, visi)"
             ])
    subgoal for acc acci x
      apply(clarsimp simp add: acc_assn_def split: prod.split simp del: inner_loop.simps)
      subgoal for front vis p front' vis' p' fronit' frontp visi'
        apply(rule ht_cons_prec)
        defer defer
        apply(rule ht_frame[OF inner_loop_rule[where front' = front' and vis' = vis' and p' = p'
                 and front = front and vis = vis and p = p and G = G],
              where R = "\<up> (old_frontp < length old_front_list \<and> 
                rev (take old_frontp (old_front_list)) = old_front \<and>
                   card (Vs G) < length old_front_list \<and> length old_front_list = L)"])
        by(sep_auto simp: f_def assms(2))
      done
      using assms(1)
      by(sep_auto split: prod.split simp: old_front_assn_def acc_assn_def f_def nths_intervall_strict_as_drop_and_take)
  
      done
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

lemma imp_cf_is_empty_rule:
  "<imp_cf_assn L Fr Bf G S Si> imp_cf_is_empty Si <\<lambda>b. imp_cf_assn L Fr Bf G S Si * \<up> (b = (S = []))>"
  by(cases Si) sep_auto

lemma foldl_insert:"foldl (\<lambda>S x. if x \<in> S then S else Set.insert x S) A xs = set xs \<union> A"
  by(induction xs arbitrary: A) auto

lemma set_srcs_visited_rule:
      "<imp_src_assn L Fr Bf G S Si * is_visited_set (Vs G) {} empty_vis> 
          set_srcs_visited empty_vis Si
        <\<lambda>r. is_visited_set (Vs G) (set S) r * imp_src_assn L Fr Bf G S Si>"
  unfolding imp_src_assn_def
  apply(cases Si)
  subgoal for fronti frontp buffer_fronti
    apply simp
    apply(rule ht_ex_pre_and_post_I)+
    subgoal for frontlist buffer_frontlist
  apply(rule ht_cons_prec)
      defer defer
        apply(rule iterate_range_strict_rule[where acc_assn = "is_visited_set (Vs G)"
             and F = "buffer_fronti \<mapsto>\<^sub>a buffer_frontlist *
    \<up> (card (Vs G) < length frontlist \<and>
       frontp < length frontlist \<and> rev (take frontp frontlist) = S \<and> card (Vs G) < length buffer_frontlist \<and> set S \<subseteq> Vs G
       \<and> length frontlist = L \<and> length buffer_frontlist = L \<and> {fronti, buffer_fronti} = {Fr, Bf})"
         and f = "\<lambda> S x. if x \<notin> S then Set.insert x S else S" and list = frontlist and acc = Set.empty])
     by (sep_auto simp: foldl_insert nths_intervall_strict_as_drop_and_take)
   done
  done

abbreviation "imp_dist_assn_raw G dlist d di 
   \<equiv> (di \<mapsto>\<^sub>a dlist * 
          \<up>((\<forall> i \<in> dom G. i < length dlist \<and> d i = dlist ! i)))"

text \<open>The distances are kept in the array @{term Da} of length @{term L}.\<close>

definition "imp_dist_assn L Da G d di 
   = (\<exists>\<^sub>A dlist. di \<mapsto>\<^sub>a dlist * 
          \<up>((\<forall> i \<in> Vs G. i < length dlist \<and> d i = dlist ! i) \<and> di = Da \<and> length dlist = L))"


lemma foldl_fun_upd_same: "foldl (\<lambda>d x y. if x = y then n else d y) d xs =
       (\<lambda> x. if x \<in> set xs then n else d x)"
  by(induction xs arbitrary: d)  auto

lemma set_all_dists_in_front_imp_rule:
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
  by auto (metis insert_iff)+

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

definition "next_frontier_current_parents G cf vis (p::nat \<Rightarrow> nat) =
   foldl (\<lambda> (nf, vis, p) u.
       foldl (\<lambda>x y. case x of (nf, vis, p) \<Rightarrow>
                if y \<notin> set vis then (y # nf, y # vis, p(y := u)) else (nf, vis, p))
            (nf, vis, p) (case G u of None \<Rightarrow> [] | Some ys \<Rightarrow> ys))
     ([], vis, p) (rev cf)"

lemma inner_fold_proj:
  "(\<lambda>(a, b, c). (a, b)) (foldl (\<lambda>x y. case x of (nf, vis, p) \<Rightarrow>
                if y \<notin> set vis then (y # nf, y # vis, p(y := u)) else (nf, vis, p)) (nf, vis, p) ys)
   = foldl (\<lambda>x y. case x of (nf, vis) \<Rightarrow> if y \<notin> set vis then (y # nf, y # vis) else (nf, vis)) (nf, vis) ys"
  by (induction ys arbitrary: nf vis p) auto

lemma outer_fold_proj:
  "(\<lambda>(a, b, c). (a, b)) (foldl (\<lambda>(nf, vis, p) u.
       foldl (\<lambda>x y. case x of (nf, vis, p) \<Rightarrow>
                if y \<notin> set vis then (y # nf, y # vis, p(y := u)) else (nf, vis, p))
            (nf, vis, p) (N u)) (nf, vis, p) us)
   = foldl (\<lambda>(nf, vis) u. 
       foldl (\<lambda>x y. case x of (nf, vis) \<Rightarrow> if y \<notin> set vis then (y # nf, y # vis) else (nf, vis))
            (nf, vis) (N u)) (nf, vis) us"
proof(induction us arbitrary: nf vis p)
  case (Cons u us)
  obtain nf1 vis1 p1 where eq: "foldl (\<lambda>x y. case x of (nf, vis, p) \<Rightarrow>
                if y \<notin> set vis then (y # nf, y # vis, p(y := u)) else (nf, vis, p)) (nf, vis, p) (N u)
         = (nf1, vis1, p1)"
    by (rule prod_cases3)
  have inner: "(nf1, vis1) = foldl (\<lambda>x y. case x of (nf, vis) \<Rightarrow>
                  if y \<notin> set vis then (y # nf, y # vis) else (nf, vis)) (nf, vis) (N u)"
    using inner_fold_proj[of u nf vis p "N u"] unfolding eq prod.case .
  show ?case
    unfolding foldl_Cons prod.case eq inner[symmetric]
    by (rule Cons)
qed simp

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

lemma inner_fold_parents:
  assumes "foldl (\<lambda>x y. case x of (nf, vis, p) \<Rightarrow>
                if y \<notin> set vis then (y # nf, y # vis, p(y := u)) else (nf, vis, p)) (nf, vis, p) ys
           = (nf', vis', p')" "set nf \<subseteq> set vis"
  shows "set nf' \<subseteq> set vis' \<and> set vis \<subseteq> set vis' \<and> (\<forall>x \<in> set vis. p' x = p x) \<and>
         (\<forall>x \<in> set nf'. x \<in> set nf \<or> (p' x = u \<and> x \<in> set ys))"
  using assms
proof(induction ys arbitrary: nf vis p)
  case (Cons y ys)
  show ?case
  proof(cases "y \<in> set vis")
    case True
    then show ?thesis
      using Cons.IH[of nf vis p] Cons.prems by auto
  next
    case False
    have "foldl (\<lambda>x y. case x of (nf, vis, p) \<Rightarrow>
                if y \<notin> set vis then (y # nf, y # vis, p(y := u)) else (nf, vis, p))
            (y # nf, y # vis, p(y := u)) ys = (nf', vis', p')"
      using Cons.prems(1) unfolding foldl_Cons prod.case if_P[OF False] .
    moreover have "set (y # nf) \<subseteq> set (y # vis)"
      using Cons.prems(2) by auto
    ultimately have "set nf' \<subseteq> set vis' \<and> set (y # vis) \<subseteq> set vis' \<and>
       (\<forall>x \<in> set (y # vis). p' x = (p(y := u)) x) \<and>
       (\<forall>x \<in> set nf'. x \<in> set (y # nf) \<or> (p' x = u \<and> x \<in> set ys))"
      by (rule Cons.IH)
    then show ?thesis
      using False by auto
  qed
qed simp

lemma outer_fold_parents:
  assumes "foldl (\<lambda>(nf, vis, p) u.
       foldl (\<lambda>x y. case x of (nf, vis, p) \<Rightarrow>
                if y \<notin> set vis then (y # nf, y # vis, p(y := u)) else (nf, vis, p))
            (nf, vis, p) (N u)) (nf, vis, p) us = (nf', vis', p')" "set nf \<subseteq> set vis"
  shows "set nf' \<subseteq> set vis' \<and> set vis \<subseteq> set vis' \<and> (\<forall>x \<in> set vis. p' x = p x) \<and>
         (\<forall>x \<in> set nf'. x \<in> set nf \<or> (p' x \<in> set us \<and> x \<in> set (N (p' x))))"
  using assms
proof(induction us arbitrary: nf vis p)
  case (Cons u us)
  obtain nf1 vis1 p1 where eq: "foldl (\<lambda>x y. case x of (nf, vis, p) \<Rightarrow>
                if y \<notin> set vis then (y # nf, y # vis, p(y := u)) else (nf, vis, p)) (nf, vis, p) (N u)
         = (nf1, vis1, p1)"
    by (rule prod_cases3) 
  note one = inner_fold_parents[OF eq Cons.prems(2)]
  have "foldl (\<lambda>(nf, vis, p) u.
       foldl (\<lambda>x y. case x of (nf, vis, p) \<Rightarrow>
                if y \<notin> set vis then (y # nf, y # vis, p(y := u)) else (nf, vis, p))
            (nf, vis, p) (N u)) (nf1, vis1, p1) us = (nf', vis', p')"
    using Cons.prems(1) unfolding foldl_Cons prod.case eq .
  note two = Cons.IH[OF this conjunct1[OF one]]
  show ?case
  proof(intro conjI ballI)
    fix x
    assume x: "x \<in> set vis"
    then have "x \<in> set vis1"
      using one by blast
    then show "p' x = p x"
      using x one two by simp
  next
    fix x
    assume x: "x \<in> set nf'"
    show "x \<in> set nf \<or> (p' x \<in> set (u # us) \<and> x \<in> set (N (p' x)))"
    proof(cases "x \<in> set nf1")
      case True
      then have "x \<in> set vis1"
        using one by blast
      then have "p' x = p1 x"
        using two by simp
      then show ?thesis
        using True one by auto
    next
      case False
      then show ?thesis
        using x two by auto
    qed
  qed (use one two in blast)+
qed simp

lemma next_frontier_current_parents_parents:
  assumes "next_frontier_current_parents G cf vis p = (cf', vis', p')"
  shows "x \<in> set vis \<Longrightarrow> p' x = p x"
        "x \<in> set cf' \<Longrightarrow> p' x \<in> set cf \<and> x \<in> set (case G (p' x) of None \<Rightarrow> [] | Some ys \<Rightarrow> ys)"
proof-
  have "set [] \<subseteq> set vis"
    by simp
  note all = outer_fold_parents[OF assms[unfolded next_frontier_current_parents_def] this]
  show "x \<in> set vis \<Longrightarrow> p' x = p x"
    using all by blast
  show "p' x \<in> set cf \<and> x \<in> set (case G (p' x) of None \<Rightarrow> [] | Some ys \<Rightarrow> ys)" if x: "x \<in> set cf'"
    using bspec[OF conjunct2[OF conjunct2[OF conjunct2[OF all]]] x]
    unfolding list.set(1) set_rev empty_iff by blast
qed

lemma next_frontier_current_parents_imp_rule:
  fixes G::"nat \<Rightarrow> nat list option"
  assumes "finite (Vs G)" "next_frontier_current_parents G cf vis p = (cf', vis', p')"
  shows 
    "<imp_cf_assn L Fr Bf G cf imp_cf * is_visited_set (Vs G) (set vis) imp_vis * 
      imp_par_assn L' Pa G p pari * graph_assn G Gi>
    next_frontier_current_parents_imp Gi imp_cf imp_vis pari
    <\<lambda>(r1, r2, r3).
        imp_cf_assn L Fr Bf G cf' r1 * is_visited_set (Vs G) (set vis') r2 * 
        imp_par_assn L' Pa G p' r3 * graph_assn G Gi>"
proof (cases imp_cf)
  case (fields fronti frontp buffer_fronti)
  have nf: "(cf', vis', p') = 
   foldl (\<lambda>(nf, vis, p) u. 
       foldl (\<lambda>x y. case x of (nf, vis, p) \<Rightarrow>
                if y \<notin> set vis then (y # nf, y # vis, p(y := u)) else (nf, vis, p))
            (nf, vis, p) (case G u of None \<Rightarrow> [] | Some ys \<Rightarrow> ys)) 
   ([], vis, p) (rev cf)"
    using assms(2) unfolding next_frontier_current_parents_def by (rule sym)
  have pre: "imp_cf_assn L Fr Bf G cf (fronti, frontp, buffer_fronti) * 
      is_visited_set (Vs G) (set vis) imp_vis * imp_par_assn L' Pa G p pari * graph_assn G Gi \<Longrightarrow>\<^sub>A
     graph_assn G Gi * is_visited_set (Vs G) (set vis) imp_vis *
      front_assn L buffer_fronti G (set vis) [] buffer_fronti 0 * imp_par_assn L' Pa G p pari * 
      old_front_assn L G cf fronti frontp * \<up>({fronti, buffer_fronti} = {Fr, Bf})"
    unfolding front_assn_def old_front_assn_def imp_cf_assn.simps
    apply(subst only_in_univ)
    by sep_auto
  have post: "graph_assn G Gi * is_visited_set (Vs G) (set vis') visi' *
      front_assn L buffer_fronti G (set vis') cf' fronti' frontp' * imp_par_assn L' Pa G p' pari * 
      old_front_assn L G cf fronti frontp * \<up>({fronti, buffer_fronti} = {Fr, Bf})
     \<Longrightarrow>\<^sub>A imp_cf_assn L Fr Bf G cf' (fronti', frontp', fronti) * is_visited_set (Vs G) (set vis') visi' *
      imp_par_assn L' Pa G p' pari * graph_assn G Gi" for fronti' frontp' visi'
    unfolding front_assn_def old_front_assn_def imp_cf_assn.simps
    using card_mono[OF assms(1), of "set vis'"]
    by (sep_auto simp: insert_commute)
  show ?thesis
    unfolding fields next_frontier_current_parents_imp.simps
  proof(rule ht_bind[OF ht_cons_prec[OF pre ent_refl ht_frame[OF outer_loop_rule[OF nf assms(1)]]]], 
        goal_cases)
    case (1 x)
    show ?case
    proof(cases x)
      case (fields fronti' frontp' visi')
      show ?thesis
        unfolding fields prod.case
        by (rule ht_cons_prec[OF post _ ht_return_sp]) sep_auto
    qed
  qed
qed

lemma Vs_same:"dVs (Graph.digraph_abs G) =  Vs G"
  unfolding Vs_def Graph.digraph_abs_def Graph.neighbourhood_def dVs_def verts_rw[of G]
  by order

text \<open>Introduction of the assertions from arrays allocated by the caller: a frontier array
      whose first cells hold the sources, together with a buffer, and arrays of distances and of
      parents.\<close>

lemma imp_src_assn_intro:
  assumes "card (Vs G) < length fl" "card (Vs G) < length bl" "length ss < length fl"
          "take (length ss) fl = ss" "set ss \<subseteq> Vs G" "length fl = L" "length bl = L"
  shows "Fr \<mapsto>\<^sub>a fl * Bf \<mapsto>\<^sub>a bl \<Longrightarrow>\<^sub>A imp_src_assn L Fr Bf G (rev ss) (Fr, length ss, Bf)"
  unfolding imp_src_assn_def imp_cf_assn.simps
  by (intro ent_ex_postI[where x = fl] ent_ex_postI[where x = bl])
     (unfold ent_pure_post_iff, use assms in \<open>simp add: ent_refl\<close>)

lemma imp_dist_assn_intro:
  "\<lbrakk>\<forall>i \<in> Vs G. i < length dl \<and> d i = dl ! i; length dl = L\<rbrakk> \<Longrightarrow> 
   Da \<mapsto>\<^sub>a dl \<Longrightarrow>\<^sub>A imp_dist_assn L Da G d Da"
  unfolding imp_dist_assn_def
  by (intro ent_ex_postI[where x = dl]) (unfold ent_pure_post_iff, intro conjI allI impI ent_refl refl)

lemma imp_par_assn_intro:
  "\<lbrakk>\<forall>i \<in> Vs G. i < length pl \<and> p i = pl ! i; length pl = L\<rbrakk> \<Longrightarrow> 
   Pa \<mapsto>\<^sub>a pl \<Longrightarrow>\<^sub>A imp_par_assn L Pa G p Pa"
  unfolding imp_par_assn_def
  by (intro ent_ex_postI[where x = pl]) (unfold ent_pure_post_iff, intro conjI allI impI ent_refl refl)

text \<open>Conversely, the distances and the parents can be read off the arrays.\<close>

lemma imp_dist_assn_char:
  "imp_dist_assn L Dh G d Da = 
   (\<exists>\<^sub>A dl. Da \<mapsto>\<^sub>a dl * \<up>((\<forall>i \<in> Vs G. i < length dl \<and> d i = dl ! i) \<and> Da = Dh \<and> length dl = L))"
  by (rule imp_dist_assn_def)

lemma imp_par_assn_char:
  "imp_par_assn L Ph G p Pa = 
   (\<exists>\<^sub>A pl. Pa \<mapsto>\<^sub>a pl * \<up>((\<forall>i \<in> Vs G. i < length pl \<and> p i = pl ! i) \<and> Pa = Ph \<and> length pl = L))"
  by (rule imp_par_assn_def)

end

text \<open>The instance for a fixed graph @{term G} with the heap handle @{term Gi}. The vertices are
      below @{term N}; the frontier and the buffer are the arrays @{term Fr} and @{term Bf} of
      length @{term "Suc N"}, and the distances and the parents are kept in the arrays
      @{term Da} and @{term Pa} of length @{term N}. The arrays are thus independent of the graph
      and can be reused for searches on further graphs with vertices below @{term N}.\<close>

locale BFS_lists_instance = BFS_subprocedures_lists
  where is_visited_set = is_visited_set and visited_memb = visited_memb
    and distinct_ins = distinct_ins and iterate_neighbourhood = iterate_neighbourhood
  for is_visited_set and visited_memb :: "nat \<Rightarrow> 'imp_vis \<Rightarrow> bool Heap"
    and distinct_ins :: "nat \<Rightarrow> 'imp_vis \<Rightarrow> 'imp_vis Heap"
    and iterate_neighbourhood :: "'g \<Rightarrow> nat \<Rightarrow>
          (nat \<Rightarrow> nat \<Rightarrow> nat array \<times> nat \<times> 'imp_vis \<Rightarrow> (nat array \<times> nat \<times> 'imp_vis) Heap) \<Rightarrow>
          nat array \<times> nat \<times> 'imp_vis \<Rightarrow> (nat array \<times> nat \<times> 'imp_vis) Heap" +
  fixes G :: "nat \<Rightarrow> nat list option"
    and Gi :: 'g
    and srcs :: "nat list"
    and N :: nat
    and Fr Bf Da Pa :: "nat array"
  assumes Vs_bound: "Vs G \<subseteq> {..<N}"
begin

lemma finite_Vs: "finite (Vs G)"
  using Vs_bound by (rule finite_subset) (rule finite_lessThan)


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
and in_vis = visited_memb
and dist_invar = "\<lambda> d S. S \<subseteq> (Vs G)"
and dist_lookup = "\<lambda> d x. d x"
and set_all_dists_in_set = "\<lambda> d S n. \<lambda> y. if y \<in> set S then n else d y"
and some_dist = id
and imp_dist_assn = "imp_dist_assn N Da G"
and set_all_dists_in_front_imp = set_all_dists_in_front_imp
and parent_lookup = "\<lambda> p x. p x"
and parent_invar = "\<lambda> _. True"
and some_parent = id
and imp_par_assn = "imp_par_assn N Pa G"
and dist_lookup_imp = "\<lambda> di x. Array.nth di x"
and parent_lookup_imp = "\<lambda> pari x. Array.nth pari x"
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
    using next_frontier_current_parents_proj[of G frontier vis par] unfolding 13(7) prod.case
    by (rule sym)
next
  case (14 frontier vis par front' vis' par')
  show ?case
    by (rule TrueI)
next
  case (15 frontier vis par front' vis' par' x)
  show ?case
    using next_frontier_current_parents_parents(1)[OF 15(7,8)] .
next
  case (16 frontier vis par front' vis' par' x)
  show ?case
    using next_frontier_current_parents_parents(2)[OF 16(7,8)]
    unfolding Graph.digraph_abs_def Graph.neighbourhood_def
    by blast
next
  case 17
  show ?case
    by (rule TrueI)
next
  case (18 S Si)
  show ?case 
    by (rule imp_cf_is_empty_rule)
next
  case (19 S Si)
  show ?case 
    unfolding imp_src_assn_def imp_src_to_cf_def
    by (rule ht_cons_prec[OF ent_refl _ ht_return_sp]) sep_auto
next
  case (20 empty_vis S Si)
  show ?case 
    using set_srcs_visited_rule[of "Suc N" Fr Bf G S Si empty_vis] unfolding list.set(1) .
next
  case (21 cf imp_cf vis imp_vis par imp_par)
  have "next_frontier_current_parents G cf vis par =
        (fst (next_frontier_current_parents G cf vis par),
         fst (snd (next_frontier_current_parents G cf vis par)),
         snd (snd (next_frontier_current_parents G cf vis par)))"
    by (simp only: prod.collapse)
  then show ?case
    by (rule next_frontier_current_parents_imp_rule[OF finite_Vs])
next
  case (22 cf cfi n d id)
  show ?case 
    by (rule set_all_dists_in_front_imp_rule)
next 
  case (23 vis visi s)
  have s: "s \<in> Vs G"
    using 23 unfolding Vs_same .
  show ?case 
    by (rule ht_cons_prec[OF _ ent_refl memb_rule[of "Vs G" "set vis" visi s]]) (sep_auto simp: s)
next
  case (24 d di x)
  have x: "x \<in> Vs G"
    using 24 unfolding Vs_same .
  show ?case
    unfolding imp_dist_assn_def using x by sep_auto
next
  case (25 p pari x)
  have x: "x \<in> Vs G"
    using 25 unfolding Vs_same .
  show ?case
    unfolding imp_par_assn_def using x by sep_auto
qed

end

end