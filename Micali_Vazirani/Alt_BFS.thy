theory Alt_BFS
  imports Directed_Set_Graphs.Pair_Graph_Specs "HOL-Eisbach.Eisbach_Tools" Alt_Dist
          Data_Structures.Set2_Addons Data_Structures.More_Lists
begin

record ('graph, 'vset, 'dmap) BFS_state =
    parents:: "'graph" current:: "'vset" visited_even:: "'vset" visited_odd:: "'vset"
    distances:: "'dmap"

definition new_edges where
  "new_edges G frontier vis \<equiv> 
     {(u,v) | u v. u \<in> (frontier) \<and> 
                   v \<in> (Pair_Graph.neighbourhood G u) - vis}"

definition next_frontier where
  "next_frontier G frontier vis \<equiv> 
     {v | u v. u \<in> (frontier) \<and> 
               v \<in> (Pair_Graph.neighbourhood G u) - vis}"

locale BFS =
  dist_map: Map where empty = empty_dist and update = update_dist and delete = delete_dist and 
                      lookup = lookup_dist and invar = invar_dist +
  Graph: Pair_Graph_Specs
    where lookup = lookup_neighb +
  set_ops: Set2 vset_empty vset_delete _ t_set vset_inv insert 
  
for lookup_neighb :: "'adjmap \<Rightarrow> 'ver \<Rightarrow> 'vset option" and
    lookup_dist:: "'dmap \<Rightarrow> 'ver labelled_vtx \<Rightarrow> enat option" and
    empty_dist and update_dist and delete_dist and invar_dist +

fixes
  srcs::"'vset" and
  matching::"'adjmap" and
  unmatching::"'adjmap" and
  expand_tree::"'adjmap \<Rightarrow> 'adjmap \<Rightarrow> 'vset \<Rightarrow> 'vset \<Rightarrow> 'adjmap" and
  next_frontier_impl::"'adjmap \<Rightarrow> 'vset \<Rightarrow> 'vset \<Rightarrow> 'vset" and
  upd_dists::"parity \<Rightarrow> 'adjmap \<Rightarrow> 'dmap \<Rightarrow> 'vset \<Rightarrow> 'vset \<Rightarrow> 'dmap" and
  init_dists::"'dmap"

assumes
   expand_tree[simp,intro!]:
     "\<lbrakk>Graph.graph_inv BFS_tree; vset_inv frontier; vset_inv vis; Graph.graph_inv G\<rbrakk> \<Longrightarrow>
       Graph.graph_inv (expand_tree G BFS_tree frontier vis)"
     "\<lbrakk>Graph.graph_inv BFS_tree; vset_inv frontier; vset_inv vis; Graph.graph_inv G\<rbrakk> \<Longrightarrow>
        Graph.digraph_abs (expand_tree G BFS_tree frontier vis) =
         (Graph.digraph_abs BFS_tree) \<union>
         new_edges (Graph.digraph_abs G) (t_set frontier) (t_set vis)" and
   next_frontier[simp]:
    "\<lbrakk>vset_inv frontier; vset_inv vis; Graph.graph_inv G\<rbrakk> \<Longrightarrow>  vset_inv (next_frontier_impl G frontier vis)"
    "\<lbrakk>vset_inv frontier; vset_inv vis; Graph.graph_inv G\<rbrakk> \<Longrightarrow>
       t_set (next_frontier_impl G frontier vis) =
         next_frontier (Graph.digraph_abs G) (t_set frontier) (t_set vis)" and
   init_dists[simp,intro!]:
     "u \<in> t_set srcs \<Longrightarrow> lookup_dist init_dists (Vtx Even u) = Some 0"
     "invar_dist init_dists" and
   upd_dists[simp,intro!]:
     "\<lbrakk>invar_dist dist_map; vset_inv frontier; vset_inv vis; Graph.graph_inv G\<rbrakk> \<Longrightarrow>
       invar_dist (upd_dists parity G dist_map frontier vis)"
     "\<lbrakk>invar_dist dist_map; vset_inv frontier; vset_inv vis; Graph.graph_inv G;
       v \<in> next_frontier (Graph.digraph_abs G) (t_set frontier) (t_set vis)\<rbrakk> \<Longrightarrow>
        \<exists>u \<in> t_set frontier.
          v \<in> Pair_Graph.neighbourhood (Graph.digraph_abs G) u - t_set vis \<and>
          lookup_dist (upd_dists parity G dist_map frontier vis) (Vtx parity v) =
            Some (the (lookup_dist dist_map (Vtx (other_parity parity) u)) + 1)"
     "\<lbrakk>invar_dist dist_map; vset_inv frontier; vset_inv vis; Graph.graph_inv G;
       w \<notin> Vtx parity ` next_frontier (Graph.digraph_abs G) (t_set frontier) (t_set vis)\<rbrakk> \<Longrightarrow>
        lookup_dist (upd_dists parity G dist_map frontier vis) w = lookup_dist dist_map w"
begin

lemma init_dists_the[simp]:
  "u \<in> t_set srcs \<Longrightarrow> the (lookup_dist init_dists (Vtx Even u)) = 0"
  by simp

definition "BFS_axiom \<longleftrightarrow>
  Graph.graph_inv matching \<and> Graph.finite_graph matching \<and>
  Graph.graph_inv unmatching \<and> Graph.finite_graph unmatching \<and> 
  Graph.finite_vsets matching \<and> Graph.finite_vsets unmatching \<and>
  t_set srcs \<subseteq> dVs (Graph.digraph_abs unmatching) \<and>
  (\<forall>u. finite (Pair_Graph.neighbourhood (Graph.digraph_abs matching) u)) \<and>
  (\<forall>u. finite (Pair_Graph.neighbourhood (Graph.digraph_abs unmatching) u)) \<and>
  t_set srcs \<noteq> {} \<and> vset_inv srcs \<and>
  Graph.digraph_abs matching \<inter> Graph.digraph_abs unmatching = {}"

abbreviation "matching_neighbourhood' \<equiv> Graph.neighbourhood matching" 
abbreviation "unmatching_neighbourhood' \<equiv> Graph.neighbourhood unmatching" 
notation "matching_neighbourhood'" ("\<N>\<^sub>G _" 100)
notation "unmatching_neighbourhood'" ("\<N>\<^sub>G' _" 100)

function (domintros) BFS::"('adjmap, 'vset, 'dmap) BFS_state \<Rightarrow> ('adjmap, 'vset, 'dmap) BFS_state" where
  "BFS BFS_state =
     (
        if current BFS_state \<noteq> \<emptyset>\<^sub>N then
          let
            visited_even' = visited_even BFS_state \<union>\<^sub>G current BFS_state;
            parents' = expand_tree unmatching (parents BFS_state) (current BFS_state) (visited_odd BFS_state);
            current' = next_frontier_impl unmatching (current BFS_state) (visited_odd BFS_state);
            distances' = upd_dists Odd unmatching (distances BFS_state) (current BFS_state) (visited_odd BFS_state);
            visited_odd' = visited_odd BFS_state \<union>\<^sub>G current';
            parents'' = expand_tree matching parents' current' visited_even';
            current'' = next_frontier_impl matching current' visited_even';
            distances'' = upd_dists Even matching distances' current' visited_even'
          in
            BFS (BFS_state \<lparr>parents:= parents'', visited_even := visited_even',
                            visited_odd := visited_odd', current := current'',
                            distances:= distances''\<rparr>)
         else
          BFS_state)"
  by pat_completeness auto

definition "BFS_call_1_conds bfs_state = ( (current bfs_state) \<noteq> \<emptyset>\<^sub>N)"

partial_function (tailrec) BFS_impl::"('adjmap, 'vset, 'dmap) BFS_state \<Rightarrow> ('adjmap, 'vset, 'dmap) BFS_state" where
  "BFS_impl BFS_state =
     (
        if current BFS_state \<noteq> \<emptyset>\<^sub>N then
          let
            visited_even' = visited_even BFS_state \<union>\<^sub>G current BFS_state;
            parents' = expand_tree unmatching (parents BFS_state) (current BFS_state) (visited_odd BFS_state);
            current' = next_frontier_impl unmatching (current BFS_state) (visited_odd BFS_state);
            distances' = upd_dists Odd unmatching (distances BFS_state) (current BFS_state) (visited_odd BFS_state);
            visited_odd' = visited_odd BFS_state \<union>\<^sub>G current';
            parents'' = expand_tree matching parents' current' visited_even';
            current'' = next_frontier_impl matching current' visited_even';
            distances'' = upd_dists Even matching distances' current' visited_even'
          in
            BFS_impl (BFS_state \<lparr>parents:= parents'', visited_even := visited_even',
                            visited_odd := visited_odd', current := current'',
                            distances:= distances''\<rparr>)
         else
          BFS_state)"

lemma BFS_impl_same:
  assumes "BFS_dom state"
  shows "BFS_impl state = BFS state"
  by(induction rule: BFS.pinduct[OF assms])(auto simp add: BFS_impl.simps BFS.psimps)

definition "BFS_upd1 BFS_state =
(       let
          visited_even' = visited_even BFS_state \<union>\<^sub>G current BFS_state;
          parents' = expand_tree unmatching (parents BFS_state) (current BFS_state) (visited_odd BFS_state);
          current' = next_frontier_impl unmatching (current BFS_state) (visited_odd BFS_state);
          distances' = upd_dists Odd unmatching (distances BFS_state) (current BFS_state) (visited_odd BFS_state);
          visited_odd' = visited_odd BFS_state \<union>\<^sub>G current';
          parents'' = expand_tree matching parents' current' visited_even';
          current'' = next_frontier_impl matching current' visited_even';
          distances'' = upd_dists Even matching distances' current' visited_even'
        in
          BFS_state \<lparr>parents:= parents'', visited_even := visited_even',
                     visited_odd := visited_odd', current := current'',
                     distances:= distances''\<rparr>
)"
definition "BFS_ret_1_conds bfs_state = ((current bfs_state) = \<emptyset>\<^sub>N)"

abbreviation "BFS_ret1 bfs_state \<equiv> bfs_state"
 
definition "invar_well_formed bfs_state = (
              vset_inv (visited_even bfs_state) \<and> vset_inv (visited_odd bfs_state) \<and> vset_inv (current bfs_state) \<and>
              Graph.graph_inv (parents bfs_state) \<and> 
              finite (t_set (current bfs_state)) \<and> 
              finite (t_set (visited_even bfs_state)) \<and> finite (t_set (visited_odd bfs_state)) \<and>
              invar_dist (distances bfs_state))"

definition "G \<equiv> (Graph.digraph_abs unmatching) \<union> (Graph.digraph_abs matching) "

definition "invar_subsets bfs_state = (
  Graph.digraph_abs (parents bfs_state) \<subseteq> G \<and>
  t_set (visited_even bfs_state) \<subseteq> dVs G \<and>
  t_set (visited_odd bfs_state) \<subseteq> dVs G \<and>
  t_set (current bfs_state) \<subseteq> dVs G \<and> 
  dVs (Graph.digraph_abs (parents bfs_state)) \<subseteq> t_set (visited_even bfs_state) \<union> t_set (visited_odd bfs_state) \<union> t_set (current bfs_state) \<and>
  t_set srcs \<subseteq> t_set (visited_even bfs_state) \<union> t_set (visited_odd bfs_state) \<union> t_set (current bfs_state))"


(*
definition "invar_3_1 bfs_state = 
  (\<forall>v\<in>t_set (current bfs_state). \<forall>u. u \<in> t_set (current bfs_state) \<longleftrightarrow> 
      distance_set G (t_set srcs) v = distance_set G (t_set srcs) u)"

definition "invar_3_2 bfs_state = 
  (\<forall>v\<in>t_set (current bfs_state). \<forall>u \<in> t_set (visited bfs_state) \<union> t_set (current bfs_state).
     distance_set G (t_set srcs) u \<le>
       distance_set G (t_set srcs) v)"

definition "invar_3_3 bfs_state = 
  (\<forall>v\<in>t_set (visited bfs_state).
     neighbourhood G v \<subseteq> t_set (visited bfs_state) \<union> t_set (current bfs_state))"

definition "invar_dist_bounded bfs_state = 
  (\<forall>v\<in> t_set (visited bfs_state) \<union> t_set (current bfs_state).
     \<forall>u. distance_set (Graph.digraph_abs G) (t_set srcs) u \<le>
           distance_set (Graph.digraph_abs G) (t_set srcs) v
             \<longrightarrow> u \<in> t_set (visited bfs_state) \<union> t_set (current bfs_state))"

definition "invar_goes_through_current bfs_state =
         (\<forall>u\<in>t_set (visited bfs_state) \<union> t_set (current bfs_state). 
            \<forall>v. v \<notin> t_set (visited bfs_state) \<union> t_set (current bfs_state) \<longrightarrow>
              (\<forall>p. Vwalk.vwalk_bet (Graph.digraph_abs G) u p v \<longrightarrow> 
                     set p \<inter> t_set (current bfs_state) \<noteq> {}))"
*)

\<comment> \<open>A0: Abstract-predicate, P1/P2-swapped alt_distance_set (P1 = unmatched, P2 = matched).\<close>
definition "unmatched_edge = (\<lambda>e. e \<in> Graph.digraph_abs unmatching)"
definition "matched_edge   = (\<lambda>e. e \<in> Graph.digraph_abs matching)"

definition "alt_distance_set H parity v \<equiv>
  alt_dist.alt_distance_set unmatched_edge matched_edge parity H (t_set srcs) v"

abbreviation "alt_walk parity H u p v \<equiv>
  alt_dist.alt_vwalk_bet unmatched_edge matched_edge parity H u p v"

abbreviation "altd_G parity v \<equiv> alt_distance_set G parity v"
abbreviation "altd_T bfs_state parity v \<equiv>
  alt_distance_set (Graph.digraph_abs (parents bfs_state)) parity v"

definition "discovered bfs_state parity =
  (case parity of Even \<Rightarrow> t_set (visited_even bfs_state) \<union> t_set (current bfs_state)
                | Odd  \<Rightarrow> t_set (visited_odd bfs_state))"

\<comment> \<open>A1: Parity-conditional invar_distances_eq (the formal carrier of P2+P3).\<close>
definition "invar_distances_eq bfs_state =
  ((\<forall>v \<in> t_set (visited_odd bfs_state).
      altd_G Odd v = altd_T bfs_state Odd v) \<and>
   (\<forall>v \<in> t_set (visited_even bfs_state) \<union> t_set (current bfs_state) - t_set srcs.
      altd_G Even v = altd_T bfs_state Even v))"

\<comment> \<open>A2: Initial state (field order: parents, current, visited_even, visited_odd, distances).\<close>
definition "initial_state =
  \<lparr>parents = empty, current = srcs, visited_even = \<emptyset>\<^sub>N,
   visited_odd = \<emptyset>\<^sub>N, distances = init_dists\<rparr>"

lemmas [code] = BFS_impl.simps initial_state_def

(*
definition "invar_parents_shortest_paths bfs_state =
  (\<forall>u\<in>t_set srcs.
      \<forall> p v. Vwalk.vwalk_bet (Graph.digraph_abs (parents bfs_state)) u p v \<longrightarrow>
         length p - 1 = distance_set (Graph.digraph_abs G) (t_set srcs) v)"

definition "invar_distances_correct bfs_state =
(\<forall>v \<in> (t_set (visited bfs_state) \<union> t_set (current bfs_state)).
       distance_set (Graph.digraph_abs G) (t_set srcs) v =
         the (lookup_dist (distances bfs_state) v))"

definition "call_1_measure_1 BFS_state=
  card (dVs (Graph.digraph_abs G) - ((t_set (visited BFS_state)) \<union> t_set (current BFS_state)))"

definition "call_1_measure_2 BFS_state =
  card (t_set (current BFS_state))"

definition
  "BFS_term_rel' = call_1_measure_1 <*mlex*> call_1_measure_2 <*mlex*> {}"

definition "initial_state = \<lparr>parents =  empty, current = srcs, visited = \<emptyset>\<^sub>N, distances = init_dists\<rparr>"

lemmas[code] = initial_state_def
*)

context
  includes Graph.adjmap.automation and Graph.vset.set.automation and set_ops.automation2
  assumes BFS_axiom 
begin

lemma graph_inv[simp,intro]:
    "Graph.graph_inv matching"
    "Graph.finite_graph matching"
    "Graph.graph_inv unmatching"
    "Graph.finite_graph unmatching" 
    "Graph.finite_vsets matching"
    "Graph.finite_vsets unmatching"
    "Graph.graph_inv matching" 
    "Graph.graph_inv unmatching" 
    "Graph.finite_graph matching"
    "Graph.finite_graph unmatching"
    "Graph.finite_vsets matching"
    "Graph.finite_vsets unmatching" and
   srcs_in_G[simp,intro]: 
     "t_set srcs \<subseteq> dVs (Graph.digraph_abs unmatching)" and
   finite_vset:
     "finite (Pair_Graph.neighbourhood (Graph.digraph_abs matching) u)"
     "finite (Pair_Graph.neighbourhood (Graph.digraph_abs unmatching) u)" and
  srcs_invar[simp]:
     "t_set srcs \<noteq> {}" 
     "vset_inv srcs" and
  matching_unmatching_disjoint[simp]:
     "Graph.digraph_abs matching \<inter> Graph.digraph_abs unmatching = {}"
  using \<open>BFS_axiom\<close>
  by (auto simp: BFS_axiom_def)

named_theorems call_cond_elims
named_theorems call_cond_intros
named_theorems ret_holds_intros
named_theorems invar_props_intros
named_theorems invar_props_elims
named_theorems invar_holds_intros
named_theorems state_rel_intros
named_theorems state_rel_holds_intros


lemma DFS_call_1_conds[call_cond_elims]: 
  "BFS_call_1_conds bfs_state \<Longrightarrow> 
   \<lbrakk>(current bfs_state) \<noteq> \<emptyset>\<^sub>N \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by(auto simp: BFS_call_1_conds_def split: list.splits option.splits if_splits)


lemma BFS_ret_1_conds[call_cond_elims]:
  "BFS_ret_1_conds bfs_state \<Longrightarrow> 
   \<lbrakk>(current bfs_state) = \<emptyset>\<^sub>N \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by(auto simp: BFS_ret_1_conds_def split: list.splits option.splits if_splits)

lemma BFS_ret_1_condsI[call_cond_intros]:
  "\<lbrakk>(current bfs_state) = \<emptyset>\<^sub>N\<rbrakk> \<Longrightarrow> BFS_ret_1_conds bfs_state"
  by(auto simp: BFS_ret_1_conds_def split: list.splits option.splits if_splits)

lemma BFS_cases:
  assumes "BFS_call_1_conds bfs_state \<Longrightarrow> P"
      "BFS_ret_1_conds bfs_state \<Longrightarrow> P"
  shows "P"
proof-
  have "BFS_call_1_conds bfs_state \<or>
        BFS_ret_1_conds bfs_state"
    by (auto simp add: BFS_call_1_conds_def
                        BFS_ret_1_conds_def
           split: list.split_asm option.split_asm if_splits)
  then show ?thesis
    using assms
    by auto
qed

lemma BFS_simps:
  assumes "BFS_dom BFS_state" 
  shows"BFS_call_1_conds BFS_state \<Longrightarrow> BFS BFS_state = BFS (BFS_upd1 BFS_state)"
      "BFS_ret_1_conds BFS_state \<Longrightarrow> BFS BFS_state = BFS_ret1 BFS_state"
  by (auto simp add: BFS.psimps[OF assms]
                     BFS_call_1_conds_def BFS_upd1_def 
                     BFS_ret_1_conds_def Let_def
            split: list.splits option.splits if_splits)

lemma BFS_induct: 
  assumes "BFS_dom bfs_state"
  assumes "\<And>bfs_state. \<lbrakk>BFS_dom bfs_state;
                        (BFS_call_1_conds bfs_state \<Longrightarrow> P (BFS_upd1 bfs_state))\<rbrakk>
              \<Longrightarrow> P bfs_state"
  shows "P bfs_state"
  apply(rule BFS.pinduct)
  subgoal using assms(1) .
  apply(rule assms(2))
  by (auto simp add: BFS_call_1_conds_def BFS_upd1_def Let_def
           split: list.splits option.splits if_splits)

lemma BFS_domintros: 
  assumes "BFS_call_1_conds BFS_state \<Longrightarrow> BFS_dom (BFS_upd1 BFS_state)"
  shows "BFS_dom BFS_state"
proof(rule BFS.domintros, goal_cases)
  case (1)
  then show ?case
    using assms(1)[simplified BFS_call_1_conds_def BFS_upd1_def]
    by (force simp: Let_def split: list.splits option.splits if_splits)
qed

lemma invar_well_formed_props[invar_props_elims]: 
  "invar_well_formed bfs_state \<Longrightarrow> 
  (\<lbrakk>vset_inv (visited_even bfs_state) ; vset_inv (visited_odd bfs_state) ; vset_inv (current bfs_state) ;
    Graph.graph_inv (parents bfs_state); 
    finite (t_set (current bfs_state)); finite (t_set (visited_even bfs_state));
    finite (t_set (visited_odd bfs_state)); 
    invar_dist (distances bfs_state)\<rbrakk> \<Longrightarrow> P)
     \<Longrightarrow> P"
  by (auto simp: invar_well_formed_def)

lemma invar_well_formed_intro[invar_props_intros]:
  "\<lbrakk>vset_inv (visited_even bfs_state); vset_inv (visited_odd bfs_state); vset_inv (current bfs_state);
    Graph.graph_inv (parents bfs_state);
    finite (t_set (current bfs_state)); finite (t_set (visited_even bfs_state));
    finite (t_set (visited_odd bfs_state)); invar_dist (distances bfs_state)\<rbrakk> 
    \<Longrightarrow> invar_well_formed bfs_state"
  by (auto simp: invar_well_formed_def)

lemma finite_simp:
   "{(u,v). u \<in> front \<and> v \<in> (Pair_Graph.neighbourhood G u) \<and> v \<notin> vis} = 
       {(u,v). u \<in> front} \<inter> {(u,v). v \<in> (Pair_Graph.neighbourhood G u)} - {(u,v) . v \<in> vis}"
   "finite {(u, v)| v . v \<in> (s u)} = finite (s u)"
  using finite_image_iff[where f = snd and A = "{(u, v) |v. v \<in> s u}"]
  by (auto simp: inj_on_def image_def)
  
lemma invar_well_formed_holds_upd1[invar_holds_intros]:
  "\<lbrakk>BFS_call_1_conds bfs_state; invar_well_formed bfs_state\<rbrakk> \<Longrightarrow> invar_well_formed (BFS_upd1 bfs_state)"
  using finite_vset
  by(auto elim!: invar_well_formed_props call_cond_elims
          simp: Let_def BFS_upd1_def BFS_call_1_conds_def next_frontier_def 
          intro!: invar_props_intros)


lemma invar_well_formed_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BFS_ret_1_conds bfs_state; invar_well_formed bfs_state\<rbrakk> \<Longrightarrow> invar_well_formed (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_well_formed_holds[invar_holds_intros]:
   assumes "BFS_dom bfs_state" "invar_well_formed bfs_state"
   shows "invar_well_formed (BFS bfs_state)"
  using assms(2-)
proof(induction rule: BFS_induct[OF assms(1)])
  case IH: (1 bfs_state)
  show ?case
    apply(rule BFS_cases[where bfs_state = bfs_state])
    by (auto intro!: IH(2-) intro: invar_holds_intros  simp: BFS_simps[OF IH(1)])
qed

lemma invar_subsets_props[invar_props_elims]: 
  "invar_subsets bfs_state \<Longrightarrow>
  (\<lbrakk>Graph.digraph_abs (parents bfs_state) \<subseteq> G;
    t_set (visited_even bfs_state) \<subseteq> dVs G;
    t_set (visited_odd bfs_state) \<subseteq> dVs G;
    t_set (current bfs_state) \<subseteq> dVs G;
    dVs (Graph.digraph_abs (parents bfs_state)) \<subseteq>
      t_set (visited_even bfs_state) \<union> t_set (visited_odd bfs_state) \<union> t_set (current bfs_state);
    t_set srcs \<subseteq> t_set (visited_even bfs_state) \<union> t_set (visited_odd bfs_state) \<union> t_set (current bfs_state)\<rbrakk> \<Longrightarrow> P)
     \<Longrightarrow> P"
  by (auto simp: invar_subsets_def)

lemma invar_subsets_intro[invar_props_intros]:
  "\<lbrakk>Graph.digraph_abs (parents bfs_state) \<subseteq> G;
    t_set (visited_even bfs_state) \<subseteq> dVs G;
    t_set (visited_odd bfs_state) \<subseteq> dVs G;
    t_set (current bfs_state) \<subseteq> dVs G;
    dVs (Graph.digraph_abs (parents bfs_state)) \<subseteq>
      t_set (visited_even bfs_state) \<union> t_set (visited_odd bfs_state) \<union> t_set (current bfs_state);
    t_set srcs \<subseteq> t_set (visited_even bfs_state) \<union> t_set (visited_odd bfs_state) \<union> t_set (current bfs_state)\<rbrakk>
     \<Longrightarrow> invar_subsets bfs_state"
  by (auto simp: invar_subsets_def)

lemma dVs_new_edges_subset:
  "dVs (new_edges H frontier vis) \<subseteq> frontier \<union> next_frontier H frontier vis"
  by (auto simp: dVs_def new_edges_def next_frontier_def)

lemma invar_subsets_holds_upd1[invar_holds_intros]:
  assumes "BFS_call_1_conds bfs_state" "invar_well_formed bfs_state" "invar_subsets bfs_state"
  shows   "invar_subsets (BFS_upd1 bfs_state)"
proof-
  have wf[simp]:
    "vset_inv (visited_even bfs_state)" "vset_inv (visited_odd bfs_state)"
    "vset_inv (current bfs_state)" "Graph.graph_inv (parents bfs_state)"
    using assms(2)
    by (auto simp: invar_well_formed_def)

  have sub:
    "Graph.digraph_abs (parents bfs_state) \<subseteq> G"
    "t_set (visited_even bfs_state) \<subseteq> dVs G"
    "t_set (visited_odd bfs_state) \<subseteq> dVs G"
    "t_set (current bfs_state) \<subseteq> dVs G"
    "dVs (Graph.digraph_abs (parents bfs_state)) \<subseteq>
       t_set (visited_even bfs_state) \<union> t_set (visited_odd bfs_state) \<union> t_set (current bfs_state)"
    "t_set srcs \<subseteq> t_set (visited_even bfs_state) \<union> t_set (visited_odd bfs_state) \<union> t_set (current bfs_state)"
    using assms(3)
    by (auto simp: invar_subsets_def)

  define VE' where "VE' = visited_even bfs_state \<union>\<^sub>G current bfs_state"
  define P' where "P' = expand_tree unmatching (parents bfs_state) (current bfs_state) (visited_odd bfs_state)"
  define C' where "C' = next_frontier_impl unmatching (current bfs_state) (visited_odd bfs_state)"
  define VO' where "VO' = visited_odd bfs_state \<union>\<^sub>G C'"
  define P'' where "P'' = expand_tree matching P' C' VE'"
  define C'' where "C'' = next_frontier_impl matching C' VE'"

  have upd1: "BFS_upd1 bfs_state =
    bfs_state \<lparr>parents := P'', visited_even := VE', visited_odd := VO', current := C'',
               distances := upd_dists Even matching
                              (upd_dists Odd unmatching (distances bfs_state) (current bfs_state)
                                 (visited_odd bfs_state)) C' VE'\<rparr>"
    by (simp add: BFS_upd1_def Let_def VE'_def P'_def C'_def VO'_def P''_def C''_def)

  have inv_VE'[simp]: "vset_inv VE'"
    by (auto simp: VE'_def)
  have inv_P'[simp]: "Graph.graph_inv P'"
    by (auto simp: P'_def)
  have inv_C'[simp]: "vset_inv C'"
    by (auto simp: C'_def)
  have inv_VO'[simp]: "vset_inv VO'"
    by (auto simp: VO'_def)

  have abs_VE': "t_set VE' = t_set (visited_even bfs_state) \<union> t_set (current bfs_state)"
    by (auto simp: VE'_def)
  have abs_P': "Graph.digraph_abs P' =
                  Graph.digraph_abs (parents bfs_state) \<union>
                  new_edges (Graph.digraph_abs unmatching) (t_set (current bfs_state))
                    (t_set (visited_odd bfs_state))"
    by (auto simp: P'_def)
  have abs_C': "t_set C' = next_frontier (Graph.digraph_abs unmatching)
                             (t_set (current bfs_state)) (t_set (visited_odd bfs_state))"
    by (auto simp: C'_def)
  have abs_VO': "t_set VO' = t_set (visited_odd bfs_state) \<union> t_set C'"
    by (auto simp: VO'_def)
  have abs_P'': "Graph.digraph_abs P'' =
                   Graph.digraph_abs P' \<union>
                   new_edges (Graph.digraph_abs matching) (t_set C') (t_set VE')"
    by (auto simp: P''_def)
  have abs_C'': "t_set C'' = next_frontier (Graph.digraph_abs matching) (t_set C') (t_set VE')"
    by (auto simp: C''_def)

  have parents''_sub_G: "Graph.digraph_abs P'' \<subseteq> G"
    using sub(1)
    by (auto simp: abs_P'' abs_P' G_def new_edges_def)
  have VE'_sub_dVs: "t_set VE' \<subseteq> dVs G"
    using sub(2,4)
    by (auto simp: abs_VE')
  have C'_sub_dVs: "t_set C' \<subseteq> dVs G"
    by (auto simp: abs_C' next_frontier_def G_def)
  have VO'_sub_dVs: "t_set VO' \<subseteq> dVs G"
    using sub(3) C'_sub_dVs
    by (auto simp: abs_VO')
  have C''_sub_dVs: "t_set C'' \<subseteq> dVs G"
    by (auto simp: abs_C'' next_frontier_def G_def)

  have dVs_P': "dVs (Graph.digraph_abs P') \<subseteq> t_set VE' \<union> t_set VO'"
    using sub(5)
          dVs_new_edges_subset[of "Graph.digraph_abs unmatching" "t_set (current bfs_state)"
                                  "t_set (visited_odd bfs_state)"]
    by (auto simp: abs_P' abs_VE' abs_VO' abs_C')
  have dVs_P'': "dVs (Graph.digraph_abs P'') \<subseteq> t_set VE' \<union> t_set VO' \<union> t_set C''"
    using dVs_P'
          dVs_new_edges_subset[of "Graph.digraph_abs matching" "t_set C'" "t_set VE'"]
    by (auto simp: abs_P'' abs_VO' abs_C'')
  have srcs_sub: "t_set srcs \<subseteq> t_set VE' \<union> t_set VO'"
    using sub(6)
    by (auto simp: abs_VE' abs_VO')

  show ?thesis
    using parents''_sub_G VE'_sub_dVs VO'_sub_dVs C''_sub_dVs dVs_P'' srcs_sub
    by (auto simp: upd1 intro!: invar_subsets_intro)
qed

lemma invar_subsets_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BFS_ret_1_conds bfs_state; invar_subsets bfs_state\<rbrakk> \<Longrightarrow> invar_subsets (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_subsets_holds[invar_holds_intros]:
   assumes "BFS_dom bfs_state" "invar_well_formed bfs_state" "invar_subsets bfs_state"
   shows "invar_subsets (BFS bfs_state)"
  using assms(2-)
proof(induction rule: BFS_induct[OF assms(1)])
  case IH: (1 bfs_state)
  show ?case
    apply(rule BFS_cases[where bfs_state = bfs_state])
    by (auto intro!: IH(2-) intro: invar_holds_intros  simp: BFS_simps[OF IH(1)])
qed

\<comment> \<open>I-1a: invar_srcs_even -- srcs stay on the even side.\<close>

definition "invar_srcs_even bfs_state =
  (t_set srcs \<subseteq> t_set (visited_even bfs_state) \<union> t_set (current bfs_state))"

lemma invar_srcs_even_props[invar_props_elims]:
  "invar_srcs_even bfs_state \<Longrightarrow>
   (t_set srcs \<subseteq> t_set (visited_even bfs_state) \<union> t_set (current bfs_state) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_srcs_even_def)

lemma invar_srcs_even_intro[invar_props_intros]:
  "t_set srcs \<subseteq> t_set (visited_even bfs_state) \<union> t_set (current bfs_state)
     \<Longrightarrow> invar_srcs_even bfs_state"
  by (auto simp: invar_srcs_even_def)

lemma invar_srcs_even_holds_upd1[invar_holds_intros]:
  assumes "BFS_call_1_conds bfs_state" "invar_well_formed bfs_state" "invar_srcs_even bfs_state"
  shows "invar_srcs_even (BFS_upd1 bfs_state)"
proof-
  have wf[simp]: "vset_inv (visited_even bfs_state)" "vset_inv (visited_odd bfs_state)"
                 "vset_inv (current bfs_state)"
    using assms(2) by (auto simp: invar_well_formed_def)
  show ?thesis
    using assms(3)
    by (auto simp: invar_srcs_even_def BFS_upd1_def Let_def)
qed

lemma invar_srcs_even_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BFS_ret_1_conds bfs_state; invar_srcs_even bfs_state\<rbrakk> \<Longrightarrow> invar_srcs_even (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_srcs_even_holds[invar_holds_intros]:
  assumes "BFS_dom bfs_state" "invar_well_formed bfs_state" "invar_srcs_even bfs_state"
  shows "invar_srcs_even (BFS bfs_state)"
  using assms(2-)
proof(induction rule: BFS_induct[OF assms(1)])
  case IH: (1 bfs_state)
  show ?case
    apply(rule BFS_cases[where bfs_state = bfs_state])
    by (auto intro!: IH(2-) intro: invar_holds_intros  simp: BFS_simps[OF IH(1)])
qed


\<comment> \<open>I-1b: invar_current_unvisited -- the even frontier is fresh.
   NOTE: current \<inter> visited_odd = {} is FALSE (blossoms), so only the even disjointness holds.\<close>

definition "invar_current_unvisited bfs_state =
  (t_set (current bfs_state) \<inter> t_set (visited_even bfs_state) = {})"

lemma invar_current_unvisited_props[invar_props_elims]:
  "invar_current_unvisited bfs_state \<Longrightarrow>
   (t_set (current bfs_state) \<inter> t_set (visited_even bfs_state) = {} \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_current_unvisited_def)

lemma invar_current_unvisited_intro[invar_props_intros]:
  "t_set (current bfs_state) \<inter> t_set (visited_even bfs_state) = {}
     \<Longrightarrow> invar_current_unvisited bfs_state"
  by (auto simp: invar_current_unvisited_def)

lemma invar_current_unvisited_holds_upd1[invar_holds_intros]:
  assumes "BFS_call_1_conds bfs_state" "invar_well_formed bfs_state"
  shows "invar_current_unvisited (BFS_upd1 bfs_state)"
proof-
  have wf[simp]: "vset_inv (visited_even bfs_state)" "vset_inv (visited_odd bfs_state)"
                 "vset_inv (current bfs_state)"
    using assms(2) by (auto simp: invar_well_formed_def)
  show ?thesis
    by (auto simp: invar_current_unvisited_def BFS_upd1_def Let_def next_frontier_def)
qed

lemma invar_current_unvisited_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BFS_ret_1_conds bfs_state; invar_current_unvisited bfs_state\<rbrakk> \<Longrightarrow> invar_current_unvisited (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_current_unvisited_holds[invar_holds_intros]:
  assumes "BFS_dom bfs_state" "invar_well_formed bfs_state" "invar_current_unvisited bfs_state"
  shows "invar_current_unvisited (BFS bfs_state)"
  using assms(2-)
proof(induction rule: BFS_induct[OF assms(1)])
  case IH: (1 bfs_state)
  show ?case
    apply(rule BFS_cases[where bfs_state = bfs_state])
    by (auto intro!: IH(2-) intro: invar_holds_intros  simp: BFS_simps[OF IH(1)])
qed


\<comment> \<open>I-1c: invar_parents_edges -- edge typing; the formal carrier of P1.
   Every parents edge is either unmatched (even source, odd target) or
   matched (odd source, even-or-current target).
   NOTE: plain vwalk_bet paths in parents need NOT alternate -- blossom 2-cycles exist
   (D2 in the design decisions). No stronger statement than this edge-local form is true.\<close>

definition "invar_parents_edges bfs_state =
  (\<forall>u v. (u, v) \<in> Graph.digraph_abs (parents bfs_state) \<longrightarrow>
     ((u, v) \<in> Graph.digraph_abs unmatching \<and>
      u \<in> t_set (visited_even bfs_state) \<and> v \<in> t_set (visited_odd bfs_state)) \<or>
     ((u, v) \<in> Graph.digraph_abs matching \<and>
      u \<in> t_set (visited_odd bfs_state) \<and>
      v \<in> t_set (visited_even bfs_state) \<union> t_set (current bfs_state)))"

lemma invar_parents_edges_props[invar_props_elims]:
  "invar_parents_edges bfs_state \<Longrightarrow>
   (\<lbrakk>\<And>u v. (u, v) \<in> Graph.digraph_abs (parents bfs_state) \<Longrightarrow>
     ((u, v) \<in> Graph.digraph_abs unmatching \<and>
      u \<in> t_set (visited_even bfs_state) \<and> v \<in> t_set (visited_odd bfs_state)) \<or>
     ((u, v) \<in> Graph.digraph_abs matching \<and>
      u \<in> t_set (visited_odd bfs_state) \<and>
      v \<in> t_set (visited_even bfs_state) \<union> t_set (current bfs_state))\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_parents_edges_def)

lemma invar_parents_edges_intro[invar_props_intros]:
  "\<lbrakk>\<And>u v. (u, v) \<in> Graph.digraph_abs (parents bfs_state) \<Longrightarrow>
     ((u, v) \<in> Graph.digraph_abs unmatching \<and>
      u \<in> t_set (visited_even bfs_state) \<and> v \<in> t_set (visited_odd bfs_state)) \<or>
     ((u, v) \<in> Graph.digraph_abs matching \<and>
      u \<in> t_set (visited_odd bfs_state) \<and>
      v \<in> t_set (visited_even bfs_state) \<union> t_set (current bfs_state))\<rbrakk>
   \<Longrightarrow> invar_parents_edges bfs_state"
  by (auto simp: invar_parents_edges_def)

lemma invar_parents_edges_holds_upd1[invar_holds_intros]:
  assumes "BFS_call_1_conds bfs_state" "invar_well_formed bfs_state"
          "invar_parents_edges bfs_state"
  shows "invar_parents_edges (BFS_upd1 bfs_state)"
proof-
  have wf[simp]:
    "vset_inv (visited_even bfs_state)" "vset_inv (visited_odd bfs_state)"
    "vset_inv (current bfs_state)" "Graph.graph_inv (parents bfs_state)"
    using assms(2) by (auto simp: invar_well_formed_def)

  define VE' where "VE' = visited_even bfs_state \<union>\<^sub>G current bfs_state"
  define P' where "P' = expand_tree unmatching (parents bfs_state) (current bfs_state) (visited_odd bfs_state)"
  define C' where "C' = next_frontier_impl unmatching (current bfs_state) (visited_odd bfs_state)"
  define VO' where "VO' = visited_odd bfs_state \<union>\<^sub>G C'"
  define P'' where "P'' = expand_tree matching P' C' VE'"
  define C'' where "C'' = next_frontier_impl matching C' VE'"

  have upd1: "BFS_upd1 bfs_state =
    bfs_state \<lparr>parents := P'', visited_even := VE', visited_odd := VO', current := C'',
               distances := upd_dists Even matching
                              (upd_dists Odd unmatching (distances bfs_state) (current bfs_state)
                                 (visited_odd bfs_state)) C' VE'\<rparr>"
    by (simp add: BFS_upd1_def Let_def VE'_def P'_def C'_def VO'_def P''_def C''_def)

  have inv_VE'[simp]: "vset_inv VE'" by (auto simp: VE'_def)
  have inv_P'[simp]: "Graph.graph_inv P'" by (auto simp: P'_def)
  have inv_C'[simp]: "vset_inv C'" by (auto simp: C'_def)
  have inv_VO'[simp]: "vset_inv VO'" by (auto simp: VO'_def)

  have abs_VE': "t_set VE' = t_set (visited_even bfs_state) \<union> t_set (current bfs_state)"
    by (auto simp: VE'_def)
  have abs_C': "t_set C' = next_frontier (Graph.digraph_abs unmatching)
                             (t_set (current bfs_state)) (t_set (visited_odd bfs_state))"
    by (auto simp: C'_def)
  have abs_VO': "t_set VO' = t_set (visited_odd bfs_state) \<union> t_set C'"
    by (auto simp: VO'_def)
  have abs_C'': "t_set C'' = next_frontier (Graph.digraph_abs matching) (t_set C') (t_set VE')"
    by (auto simp: C''_def)
  have abs_P'': "Graph.digraph_abs P'' =
                   Graph.digraph_abs (parents bfs_state)
                   \<union> new_edges (Graph.digraph_abs unmatching) (t_set (current bfs_state))
                       (t_set (visited_odd bfs_state))
                   \<union> new_edges (Graph.digraph_abs matching) (t_set C') (t_set VE')"
    by (auto simp: P''_def P'_def)

  have new1: "\<And>u v. (u, v) \<in> new_edges (Graph.digraph_abs unmatching)
                       (t_set (current bfs_state)) (t_set (visited_odd bfs_state)) \<Longrightarrow>
                (u, v) \<in> Graph.digraph_abs unmatching \<and>
                u \<in> t_set (current bfs_state) \<and> v \<in> t_set C'"
    by (auto simp: new_edges_def next_frontier_def abs_C')
  have new2: "\<And>u v. (u, v) \<in> new_edges (Graph.digraph_abs matching)
                       (t_set C') (t_set VE') \<Longrightarrow>
                (u, v) \<in> Graph.digraph_abs matching \<and>
                u \<in> t_set C' \<and> v \<in> t_set C''"
    by (auto simp: new_edges_def next_frontier_def abs_C'')

  show ?thesis
    using assms(3) new1 new2
    by (intro invar_parents_edges_intro)
       (fastforce simp: upd1 abs_P'' abs_VE' abs_VO' invar_parents_edges_def)
qed

lemma invar_parents_edges_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BFS_ret_1_conds bfs_state; invar_parents_edges bfs_state\<rbrakk> \<Longrightarrow> invar_parents_edges (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_parents_edges_holds[invar_holds_intros]:
  assumes "BFS_dom bfs_state" "invar_well_formed bfs_state" "invar_parents_edges bfs_state"
  shows "invar_parents_edges (BFS bfs_state)"
  using assms(2-)
proof(induction rule: BFS_induct[OF assms(1)])
  case IH: (1 bfs_state)
  show ?case
    apply(rule BFS_cases[where bfs_state = bfs_state])
    by (auto intro!: IH(2-) intro: invar_holds_intros  simp: BFS_simps[OF IH(1)])
qed


\<comment> \<open>I-1d: P1 as a theorem (corollary of invar_subsets + invar_parents_edges).
   NOTE: plain vwalk_bet paths in parents need NOT alternate -- blossom 2-cycles
   mean non-alternating plain paths exist (D2). The only true P1-statement is for
   *alternating* walks, proved here. No stronger statement is provable.\<close>

lemma parents_alt_walk_in_G:
  assumes "invar_subsets bfs_state"
          "alt_walk parity (Graph.digraph_abs (parents bfs_state)) u p v"
  shows "alt_walk parity G u p v"
  using assms
  by (auto simp: invar_subsets_def intro: alt_dist.alt_vwalk_bet_subset)


\<comment> \<open>I-1e: invar_visited_closed -- half-step closure (analogue of BFS_2 invar_3_3).
   Unmatched clause: every even-visited vertex has its unmatched neighbourhood in visited_odd.
   Matched clause: every odd-visited vertex has its matched neighbourhood in visited_even \<union> current.
   NOTE: the matched clause's RHS includes current because the even frontier produced in
   the same iteration is not yet in visited_even at loop boundaries.\<close>

definition "invar_visited_closed bfs_state =
  ((\<forall>v \<in> t_set (visited_even bfs_state).
      Pair_Graph.neighbourhood (Graph.digraph_abs unmatching) v \<subseteq> t_set (visited_odd bfs_state)) \<and>
   (\<forall>v \<in> t_set (visited_odd bfs_state).
      Pair_Graph.neighbourhood (Graph.digraph_abs matching) v \<subseteq>
        t_set (visited_even bfs_state) \<union> t_set (current bfs_state)))"

lemma invar_visited_closed_props[invar_props_elims]:
  "invar_visited_closed bfs_state \<Longrightarrow>
   (\<lbrakk>\<And>v. v \<in> t_set (visited_even bfs_state) \<Longrightarrow>
        Pair_Graph.neighbourhood (Graph.digraph_abs unmatching) v \<subseteq> t_set (visited_odd bfs_state);
     \<And>v. v \<in> t_set (visited_odd bfs_state) \<Longrightarrow>
        Pair_Graph.neighbourhood (Graph.digraph_abs matching) v \<subseteq>
          t_set (visited_even bfs_state) \<union> t_set (current bfs_state)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_visited_closed_def)

lemma invar_visited_closed_intro[invar_props_intros]:
  "\<lbrakk>\<And>v. v \<in> t_set (visited_even bfs_state) \<Longrightarrow>
        Pair_Graph.neighbourhood (Graph.digraph_abs unmatching) v \<subseteq> t_set (visited_odd bfs_state);
    \<And>v. v \<in> t_set (visited_odd bfs_state) \<Longrightarrow>
        Pair_Graph.neighbourhood (Graph.digraph_abs matching) v \<subseteq>
          t_set (visited_even bfs_state) \<union> t_set (current bfs_state)\<rbrakk>
   \<Longrightarrow> invar_visited_closed bfs_state"
  by (auto simp: invar_visited_closed_def)

lemma invar_visited_closed_holds_upd1[invar_holds_intros]:
  assumes "BFS_call_1_conds bfs_state" "invar_well_formed bfs_state"
          "invar_visited_closed bfs_state"
  shows "invar_visited_closed (BFS_upd1 bfs_state)"
proof-
  have wf[simp]:
    "vset_inv (visited_even bfs_state)" "vset_inv (visited_odd bfs_state)"
    "vset_inv (current bfs_state)" "Graph.graph_inv (parents bfs_state)"
    using assms(2) by (auto simp: invar_well_formed_def)

  define VE' where "VE' = visited_even bfs_state \<union>\<^sub>G current bfs_state"
  define P' where "P' = expand_tree unmatching (parents bfs_state) (current bfs_state) (visited_odd bfs_state)"
  define C' where "C' = next_frontier_impl unmatching (current bfs_state) (visited_odd bfs_state)"
  define VO' where "VO' = visited_odd bfs_state \<union>\<^sub>G C'"
  define P'' where "P'' = expand_tree matching P' C' VE'"
  define C'' where "C'' = next_frontier_impl matching C' VE'"

  have upd1: "BFS_upd1 bfs_state =
    bfs_state \<lparr>parents := P'', visited_even := VE', visited_odd := VO', current := C'',
               distances := upd_dists Even matching
                              (upd_dists Odd unmatching (distances bfs_state) (current bfs_state)
                                 (visited_odd bfs_state)) C' VE'\<rparr>"
    by (simp add: BFS_upd1_def Let_def VE'_def P'_def C'_def VO'_def P''_def C''_def)

  have inv_VE'[simp]: "vset_inv VE'" by (auto simp: VE'_def)
  have inv_C'[simp]: "vset_inv C'" by (auto simp: C'_def)
  have inv_VO'[simp]: "vset_inv VO'" by (auto simp: VO'_def)

  have abs_VE': "t_set VE' = t_set (visited_even bfs_state) \<union> t_set (current bfs_state)"
    by (auto simp: VE'_def)
  have abs_C': "t_set C' = next_frontier (Graph.digraph_abs unmatching)
                             (t_set (current bfs_state)) (t_set (visited_odd bfs_state))"
    by (auto simp: C'_def)
  have abs_VO': "t_set VO' = t_set (visited_odd bfs_state) \<union> t_set C'"
    by (auto simp: VO'_def)
  have abs_C'': "t_set C'' = next_frontier (Graph.digraph_abs matching) (t_set C') (t_set VE')"
    by (auto simp: C''_def)

  have even_side: "Pair_Graph.neighbourhood (Graph.digraph_abs unmatching) v \<subseteq> t_set VO'"
    if "v \<in> t_set VE'" for v
  proof(cases "v \<in> t_set (visited_even bfs_state)")
    case True
    then show ?thesis
      using assms(3)
      by (auto simp: invar_visited_closed_def abs_VO')
  next
    case False
    hence "v \<in> t_set (current bfs_state)"
      using that by (auto simp: abs_VE')
    then show ?thesis
      by (auto simp: abs_VO' abs_C' next_frontier_def)
  qed

  have odd_side: "Pair_Graph.neighbourhood (Graph.digraph_abs matching) v \<subseteq> t_set VE' \<union> t_set C''"
    if "v \<in> t_set VO'" for v
  proof(cases "v \<in> t_set (visited_odd bfs_state)")
    case True
    then show ?thesis
      using assms(3)
      by (auto simp: invar_visited_closed_def abs_VE')
  next
    case False
    hence "v \<in> t_set C'"
      using that by (auto simp: abs_VO')
    then show ?thesis
      by (auto simp: abs_C'' next_frontier_def)
  qed

  show ?thesis
    using even_side odd_side
    by (auto simp: upd1 invar_visited_closed_def abs_VE' abs_VO')
qed

lemma invar_visited_closed_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BFS_ret_1_conds bfs_state; invar_visited_closed bfs_state\<rbrakk> \<Longrightarrow> invar_visited_closed (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_visited_closed_holds[invar_holds_intros]:
  assumes "BFS_dom bfs_state" "invar_well_formed bfs_state" "invar_visited_closed bfs_state"
  shows "invar_visited_closed (BFS bfs_state)"
  using assms(2-)
proof(induction rule: BFS_induct[OF assms(1)])
  case IH: (1 bfs_state)
  show ?case
    apply(rule BFS_cases[where bfs_state = bfs_state])
    by (auto intro!: IH(2-) intro: invar_holds_intros  simp: BFS_simps[OF IH(1)])
qed




\<comment> \<open>Batch 3 DEFINITIONS + props/intro (holds proofs come in a later session; ORDERING NOTE).\<close>

\<comment> \<open>analogue of invar_3_2; anchor: everything discovered is no deeper than current\<close>
definition "invar_level_bounded bfs_state =
  (\<forall>v \<in> t_set (current bfs_state). \<forall>parity. \<forall>u \<in> discovered bfs_state parity.
      altd_G parity u \<le> altd_G Even v)"

lemma invar_level_bounded_props[invar_props_elims]:
  "invar_level_bounded bfs_state \<Longrightarrow>
   (\<lbrakk>\<And>v parity u. v \<in> t_set (current bfs_state) \<Longrightarrow> u \<in> discovered bfs_state parity \<Longrightarrow>
        altd_G parity u \<le> altd_G Even v\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_level_bounded_def)

lemma invar_level_bounded_intro[invar_props_intros]:
  "\<lbrakk>\<And>v parity u. v \<in> t_set (current bfs_state) \<Longrightarrow> u \<in> discovered bfs_state parity \<Longrightarrow>
       altd_G parity u \<le> altd_G Even v\<rbrakk>
   \<Longrightarrow> invar_level_bounded bfs_state"
  by (auto simp: invar_level_bounded_def)

\<comment> \<open>analogue of invar_3_4 (invar_dist_bounded); downward closure across BOTH parities\<close>
definition "invar_discovered_downclosed bfs_state =
  (\<forall>parity parity' v u. v \<in> discovered bfs_state parity \<longrightarrow>
      altd_G parity' u \<le> altd_G parity v \<longrightarrow> u \<in> discovered bfs_state parity')"

lemma invar_discovered_downclosed_props[invar_props_elims]:
  "invar_discovered_downclosed bfs_state \<Longrightarrow>
   (\<lbrakk>\<And>parity parity' v u. v \<in> discovered bfs_state parity \<Longrightarrow>
        altd_G parity' u \<le> altd_G parity v \<Longrightarrow> u \<in> discovered bfs_state parity'\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_discovered_downclosed_def)

lemma invar_discovered_downclosed_intro[invar_props_intros]:
  "\<lbrakk>\<And>parity parity' v u. v \<in> discovered bfs_state parity \<Longrightarrow>
       altd_G parity' u \<le> altd_G parity v \<Longrightarrow> u \<in> discovered bfs_state parity'\<rbrakk>
   \<Longrightarrow> invar_discovered_downclosed bfs_state"
  by (auto simp: invar_discovered_downclosed_def)

\<comment> \<open>analogue of invar_3_1; current is exactly one even level\<close>
definition "invar_current_level bfs_state =
  (\<forall>v \<in> t_set (current bfs_state). \<forall>u.
      (u \<in> t_set (current bfs_state)) \<longleftrightarrow> (altd_G Even u = altd_G Even v))"

lemma invar_current_level_props[invar_props_elims]:
  "invar_current_level bfs_state \<Longrightarrow>
   (\<lbrakk>\<And>v u. v \<in> t_set (current bfs_state) \<Longrightarrow>
        (u \<in> t_set (current bfs_state)) \<longleftrightarrow> (altd_G Even u = altd_G Even v)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_current_level_def)

lemma invar_current_level_intro[invar_props_intros]:
  "\<lbrakk>\<And>v u. v \<in> t_set (current bfs_state) \<Longrightarrow>
       (u \<in> t_set (current bfs_state)) \<longleftrightarrow> (altd_G Even u = altd_G Even v)\<rbrakk>
   \<Longrightarrow> invar_current_level bfs_state"
  by (auto simp: invar_current_level_def)


\<comment> \<open>Batch 2: reachability + parity step lemmas.\<close>

\<comment> \<open>Helper: alt-distances have their parity.\<close>
lemma altd_G_parity:
  assumes "altd_G parity v = enat n"
  shows "of_parity parity n"
proof-
  from assms have notinf: "alt_dist.alt_distance_set unmatched_edge matched_edge parity G (t_set srcs) v \<noteq> \<infinity>"
    by (auto simp: alt_distance_set_def)
  from alt_dist_set_not_inf[OF notinf] obtain u where
    u_src: "u \<in> t_set srcs" and
    u_dist: "alt_dist.alt_distance unmatched_edge matched_edge parity G u v =
             alt_dist.alt_distance_set unmatched_edge matched_edge parity G (t_set srcs) v"
    by blast
  have u_lt: "alt_dist.alt_distance unmatched_edge matched_edge parity G u v < \<infinity>"
    using u_dist notinf by (simp add: less_le)
  from alt_shortest_path_exists_2[OF u_lt] obtain p where
    sp: "alt_dist.alt_shortest_path unmatched_edge matched_edge parity G u p v"
    by blast
  from sp have
    walk: "alt_dist.alt_vwalk_bet unmatched_edge matched_edge parity G u p v" and
    dist_p: "alt_dist.alt_distance unmatched_edge matched_edge parity G u v = enat (length p - 1)"
    by (auto elim!: alt_dist.alt_shortest_path_props)
  from walk have parity_len: "of_parity (other_parity parity) (length p)"
    by (auto elim!: alt_dist.alt_vwalk_betE)
  from walk have p_nonempty: "p \<noteq> []"
    by (auto simp: alt_dist.alt_vwalk_bet_def dest: Vwalk.vwalk_bet_nonempty)
  have n_eq: "n = length p - 1"
    using u_dist dist_p assms by (simp add: alt_distance_set_def)
  show ?thesis
    using parity_len n_eq p_nonempty
    by (cases parity; simp add: parity_simps even_diff_nat)
qed


\<comment> \<open>I-2a: invar_discovered_reachable -- parity-split reachability (analogue of BFS_2 invar_current_reachable).\<close>

definition "invar_discovered_reachable bfs_state =
  ((\<forall>v \<in> t_set (visited_even bfs_state) \<union> t_set (current bfs_state). altd_G Even v < \<infinity>) \<and>
   (\<forall>v \<in> t_set (visited_odd bfs_state). altd_G Odd v < \<infinity>))"

lemma invar_discovered_reachable_props[invar_props_elims]:
  "invar_discovered_reachable bfs_state \<Longrightarrow>
   (\<lbrakk>\<forall>v \<in> t_set (visited_even bfs_state) \<union> t_set (current bfs_state). altd_G Even v < \<infinity>;
     \<forall>v \<in> t_set (visited_odd bfs_state). altd_G Odd v < \<infinity>\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_discovered_reachable_def)

lemma invar_discovered_reachable_intro[invar_props_intros]:
  "\<lbrakk>\<forall>v \<in> t_set (visited_even bfs_state) \<union> t_set (current bfs_state). altd_G Even v < \<infinity>;
    \<forall>v \<in> t_set (visited_odd bfs_state). altd_G Odd v < \<infinity>\<rbrakk>
   \<Longrightarrow> invar_discovered_reachable bfs_state"
  by (auto simp: invar_discovered_reachable_def)

lemma invar_discovered_reachable_holds_upd1[invar_holds_intros]:
  assumes "BFS_call_1_conds bfs_state" "invar_well_formed bfs_state"
          "invar_discovered_reachable bfs_state"
  shows "invar_discovered_reachable (BFS_upd1 bfs_state)"
proof-
  have wf[simp]:
    "vset_inv (visited_even bfs_state)" "vset_inv (visited_odd bfs_state)"
    "vset_inv (current bfs_state)" "Graph.graph_inv (parents bfs_state)"
    using assms(2) by (auto simp: invar_well_formed_def)

  define VE' where "VE' = visited_even bfs_state \<union>\<^sub>G current bfs_state"
  define P' where "P' = expand_tree unmatching (parents bfs_state) (current bfs_state) (visited_odd bfs_state)"
  define C' where "C' = next_frontier_impl unmatching (current bfs_state) (visited_odd bfs_state)"
  define VO' where "VO' = visited_odd bfs_state \<union>\<^sub>G C'"
  define P'' where "P'' = expand_tree matching P' C' VE'"
  define C'' where "C'' = next_frontier_impl matching C' VE'"

  have upd1: "BFS_upd1 bfs_state =
    bfs_state \<lparr>parents := P'', visited_even := VE', visited_odd := VO', current := C'',
               distances := upd_dists Even matching
                              (upd_dists Odd unmatching (distances bfs_state) (current bfs_state)
                                 (visited_odd bfs_state)) C' VE'\<rparr>"
    by (simp add: BFS_upd1_def Let_def VE'_def P'_def C'_def VO'_def P''_def C''_def)

  have inv_VE'[simp]: "vset_inv VE'" by (auto simp: VE'_def)
  have inv_C'[simp]: "vset_inv C'" by (auto simp: C'_def)
  have inv_VO'[simp]: "vset_inv VO'" by (auto simp: VO'_def)

  have abs_VE': "t_set VE' = t_set (visited_even bfs_state) \<union> t_set (current bfs_state)"
    by (auto simp: VE'_def)
  have abs_C': "t_set C' = next_frontier (Graph.digraph_abs unmatching)
                             (t_set (current bfs_state)) (t_set (visited_odd bfs_state))"
    by (auto simp: C'_def)
  have abs_VO': "t_set VO' = t_set (visited_odd bfs_state) \<union> t_set C'"
    by (auto simp: VO'_def)
  have abs_C'': "t_set C'' = next_frontier (Graph.digraph_abs matching) (t_set C') (t_set VE')"
    by (auto simp: C''_def)

  have odd_new: "altd_G Odd v < \<infinity>" if "v \<in> t_set C'" for v
  proof-
    from that obtain u where u_curr: "u \<in> t_set (current bfs_state)"
      and u_neigh: "v \<in> Pair_Graph.neighbourhood (Graph.digraph_abs unmatching) u"
      by (auto simp: abs_C' next_frontier_def)
    have fin_u: "altd_G Even u < \<infinity>"
      using assms(3) u_curr by (auto simp: invar_discovered_reachable_def)
    have mem_G: "v \<in> Pair_Graph.neighbourhood G u"
      using u_neigh by (auto simp: G_def neighoubrhood_union)
    have unm: "unmatched_edge (u, v)"
      using u_neigh by (simp add: unmatched_edge_def Pair_Graph.neighbourhood_def)
    have le: "altd_G Odd v \<le> altd_G Even u + 1"
      unfolding alt_distance_set_def
      by (intro odd_alt_distance_set_neighbourhood) (fact mem_G, fact srcs_invar(1), fact unm)
    show ?thesis
    proof-
      have h: "altd_G Even u + 1 < \<infinity>" using fin_u by (simp add: plus_eq_infty_iff_enat enat_ord_simps)
      show ?thesis by (rule order_le_less_trans[OF le h])
    qed
  qed

  have even_new: "altd_G Even v < \<infinity>" if "v \<in> t_set C''" for v
  proof-
    from that obtain u where u_C': "u \<in> t_set C'"
      and u_neigh: "v \<in> Pair_Graph.neighbourhood (Graph.digraph_abs matching) u"
      by (auto simp: abs_C'' next_frontier_def)
    have fin_u: "altd_G Odd u < \<infinity>"
      using odd_new[OF u_C'] .
    have mem_G: "v \<in> Pair_Graph.neighbourhood G u"
      using u_neigh by (auto simp: G_def neighoubrhood_union)
    have mat: "matched_edge (u, v)"
      using u_neigh by (simp add: matched_edge_def Pair_Graph.neighbourhood_def)
    have le: "altd_G Even v \<le> altd_G Odd u + 1"
      unfolding alt_distance_set_def
      by (intro even_alt_distance_set_neighbourhood) (fact mem_G, fact srcs_invar(1), fact mat)
    show ?thesis
    proof-
      have h: "altd_G Odd u + 1 < \<infinity>" using fin_u by (simp add: plus_eq_infty_iff_enat enat_ord_simps)
      show ?thesis by (rule order_le_less_trans[OF le h])
    qed
  qed

  show ?thesis
    using assms(3) odd_new even_new
    by (auto simp: upd1 abs_VE' abs_VO' invar_discovered_reachable_def)
qed

lemma invar_discovered_reachable_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BFS_ret_1_conds bfs_state; invar_discovered_reachable bfs_state\<rbrakk> \<Longrightarrow>
     invar_discovered_reachable (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_discovered_reachable_holds[invar_holds_intros]:
  assumes "BFS_dom bfs_state" "invar_well_formed bfs_state"
          "invar_discovered_reachable bfs_state"
  shows "invar_discovered_reachable (BFS bfs_state)"
  using assms(2-)
proof(induction rule: BFS_induct[OF assms(1)])
  case IH: (1 bfs_state)
  show ?case
    apply(rule BFS_cases[where bfs_state = bfs_state])
    by (auto intro!: IH(2-) intro: invar_holds_intros  simp: BFS_simps[OF IH(1)])
qed


\<comment> \<open>I-2b: Parity step lemmas (analogue of BFS_2 dist_current_plus_1_new, split in two).\<close>

lemma alt_dist_odd_step:
  assumes "invar_level_bounded bfs_state" "invar_discovered_downclosed bfs_state"
          "invar_discovered_reachable bfs_state"
          "v' \<in> t_set (current bfs_state)"
          "v \<in> Pair_Graph.neighbourhood (Graph.digraph_abs unmatching) v'"
          "v \<notin> t_set (visited_odd bfs_state)"
  shows "altd_G Odd v = altd_G Even v' + 1"
proof-
  have fin: "altd_G Even v' < \<infinity>"
    using assms(3,4) by (auto simp: invar_discovered_reachable_def)
  have mem_G: "v \<in> Pair_Graph.neighbourhood G v'"
    using assms(5) by (auto simp: G_def neighoubrhood_union)
  have unm: "unmatched_edge (v', v)"
    using assms(5) by (simp add: unmatched_edge_def Pair_Graph.neighbourhood_def)
  have le: "altd_G Odd v \<le> altd_G Even v' + 1"
    unfolding alt_distance_set_def
    by (intro odd_alt_distance_set_neighbourhood) (fact mem_G, fact srcs_invar(1), fact unm)
  have "False" if lt: "altd_G Odd v < altd_G Even v' + 1"
  proof-
    have step1: "altd_G Odd v \<le> altd_G Even v'"
      using lt fin by (cases "altd_G Odd v"; cases "altd_G Even v'") (auto simp: eSuc_enat[symmetric] plus_1_eSuc ileI1)
    hence "v \<in> discovered bfs_state Odd"
      using assms(2,4) by (auto simp: invar_discovered_downclosed_def discovered_def split: parity.splits)
    thus False
      using assms(6) by (auto simp: discovered_def)
  qed
  thus ?thesis
    using le by force
qed

lemma alt_dist_even_step:
  assumes "invar_level_bounded bfs_state" "invar_discovered_downclosed bfs_state"
          "invar_discovered_reachable bfs_state"
          "w \<in> t_set (current bfs_state)" "altd_G Odd v' = altd_G Even w + 1"
          "v \<in> Pair_Graph.neighbourhood (Graph.digraph_abs matching) v'"
          "v \<notin> t_set (visited_even bfs_state) \<union> t_set (current bfs_state)"
  shows "altd_G Even v = altd_G Odd v' + 1"
proof-
  have finw: "altd_G Even w < \<infinity>"
    using assms(3,4) by (auto simp: invar_discovered_reachable_def)
  hence finv': "altd_G Odd v' < \<infinity>"
    using assms(5) by (simp add: plus_eq_infty_iff_enat)
  have mem_G: "v \<in> Pair_Graph.neighbourhood G v'"
    using assms(6) by (auto simp: G_def neighoubrhood_union)
  have mat: "matched_edge (v', v)"
    using assms(6) by (simp add: matched_edge_def Pair_Graph.neighbourhood_def)
  have le: "altd_G Even v \<le> altd_G Odd v' + 1"
    unfolding alt_distance_set_def
    by (intro even_alt_distance_set_neighbourhood) (fact mem_G, fact srcs_invar(1), fact mat)
  have "False" if lt': "altd_G Even v < altd_G Odd v' + 1"
  proof-
    have step1: "altd_G Even v \<le> altd_G Odd v'"
      using lt' finv' by (cases "altd_G Even v"; cases "altd_G Odd v'") (auto simp: ileI1 plus_1_eSuc)
    \<comment> \<open>Parity squeeze: Even value \<le> odd value forces \<le> odd value - 1 = Even w's value.\<close>
    obtain n where nm1: "altd_G Even v = enat n"
      using step1 finv'
      by (cases "altd_G Even v") (auto simp: order_le_less_trans)
    obtain m where nm2: "altd_G Even w = enat m"
      using finw by (cases "altd_G Even w") auto
    have even_n: "even n" using altd_G_parity[OF nm1] by (simp add: parity_simps)
    have even_m: "even m" using altd_G_parity[OF nm2] by (simp add: parity_simps)
    have v'_enat: "altd_G Odd v' = enat (m + 1)"
    proof-
      have "altd_G Odd v' = enat m + 1" using assms(5) nm2 by simp
      thus ?thesis by (auto simp only: enat_simps)
    qed
    have "n \<le> m + 1"
      using step1 nm1 v'_enat by (simp only: enat_simps)
    hence "n \<le> m" using even_n even_m by presburger
    hence "altd_G Even v \<le> altd_G Even w" using nm1 nm2 by (simp add: enat_simps)
    hence "v \<in> discovered bfs_state Even"
      using assms(2,4) by (auto simp: invar_discovered_downclosed_def discovered_def split: parity.splits)
    thus False using assms(7) by (auto simp: discovered_def)
  qed
  thus ?thesis using le by force
qed


\<comment> \<open>Batch 3a: Descent helpers.\<close>

\<comment> \<open>Helper 0: generalisation of odd_alt_distance_set_parent (no v \<notin> vs premise).
   The key insight: an Odd alt-walk has even length \<ge> 2, so the last two vertices
   [w, v] always exist; no u \<noteq> v assumption is needed.\<close>
lemma odd_alt_distance_set_parent':
  "\<lbrakk>alt_dist.alt_distance_set P1 P2 Odd G vs v < \<infinity>; vs \<noteq> {}\<rbrakk> \<Longrightarrow>
     \<exists>w. alt_dist.alt_distance_set P1 P2 Even G vs w + 1 = alt_dist.alt_distance_set P1 P2 Odd G vs v
         \<and> v \<in> Pair_Graph.neighbourhood G w \<and> P1 (w, v)"
proof(goal_cases)
  case 1
  hence notinf: "alt_dist.alt_distance_set P1 P2 Odd G vs v \<noteq> \<infinity>" by simp
  then obtain u where u_vs: "u \<in> vs"
    and u_eq: "alt_dist.alt_distance_set P1 P2 Odd G vs v = alt_dist.alt_distance P1 P2 Odd G u v"
    by (rule alt_distance_set_wit')
  have u_lt: "alt_dist.alt_distance P1 P2 Odd G u v < \<infinity>"
    using u_eq 1(1) by auto
  then obtain p where p: "alt_dist.alt_shortest_path P1 P2 Odd G u p v"
    by (erule alt_shortest_path_exists_2)
  have "even (length p)"
    using p by (auto dest!: alt_dist.alt_shortest_path_vwalk elim!: alt_dist.alt_vwalk_betE
                     simp: parity_simps)
  moreover have "p \<noteq> []"
    using p by (auto dest!: alt_dist.alt_shortest_path_vwalk
                     simp: alt_dist.alt_vwalk_bet_def dest: Vwalk.vwalk_bet_nonempty)
  ultimately have len_ge2: "length p \<ge> 2"
    by (cases "length p"; cases "length p - 1"; simp_all)
  moreover have "last p = v"
    using p by auto
  ultimately obtain p' w where pw: "p = p' @ [w, v]"
    by (auto simp: Suc_le_length_iff_2 eval_nat_numeral)
  obtain par where par_sp: "alt_dist.alt_shortest_path P1 P2 par G u (p' @ [w]) w"
    using p by (auto dest: alt_shortest_path_split_2 simp: pw parity_simps split: parity.splits)
  have par_Even: "par = Even"
  proof(rule ccontr, goal_cases)
    case 1
    hence "par = Odd" using parity.exhaust by auto
    hence "even (length (p' @ [w]))"
      using par_sp by (auto dest!: alt_dist.alt_shortest_path_vwalk elim!: alt_dist.alt_vwalk_betE
                             simp: parity_simps)
    moreover have "even (length p)"
      using p by (auto dest!: alt_dist.alt_shortest_path_vwalk elim!: alt_dist.alt_vwalk_betE
                       simp: parity_simps)
    hence "odd (length (p' @ [w]))" by (auto simp: pw)
    ultimately show ?case by auto
  qed
  have dist_eq: "alt_dist.alt_distance P1 P2 Odd G u v = alt_dist.alt_distance P1 P2 Even G u w + 1"
  proof-
    have eq1: "alt_dist.alt_distance P1 P2 Odd G u v = enat (length p' + 1)"
      using alt_dist.alt_shortest_path_dist[OF p] pw by simp
    have eq2: "alt_dist.alt_distance P1 P2 Even G u w = enat (length p')"
      using alt_dist.alt_shortest_path_dist[OF par_sp] par_Even by simp
    show ?thesis using eq1 eq2 by (simp add: eSuc_plus_1 eSuc_enat)
  qed
  have v_neigh: "v \<in> Pair_Graph.neighbourhood G w"
    using p pw vwalk_bet_suffix_is_vwalk_bet
    by (fastforce elim: alt_dist.alt_vwalk_betE simp: pw
                  dest!: alt_dist.alt_shortest_path_vwalk)
  have P1wv: "P1 (w, v)"
  proof-
    have bet: "alt_dist.alt_vwalk_bet P1 P2 Odd G u p v"
      using p by (rule alt_dist.alt_shortest_path_vwalk)
    have "P1 (last (edges_of_vwalk p))"
      using bet len_ge2 by (rule alternating_list_odd_last)
    moreover have "last (edges_of_vwalk p) = (w, v)"
    proof -
      have "last (edges_of_vwalk (p' @ [w, v])) = (w, v)"
      proof(induction p' rule: rev_induct)
        case Nil show ?case by simp
      next
        case (snoc x xs)
        show ?case using edges_of_vwalk_append_two_vertices[of "xs @ [x]" w v] by simp
      qed
      thus ?thesis using pw by simp
    qed
    ultimately show ?thesis by simp
  qed
  have set_eq: "alt_dist.alt_distance_set P1 P2 Even G vs w + 1 = alt_dist.alt_distance_set P1 P2 Odd G vs v"
  proof(rule antisym)
    have "alt_dist.alt_distance_set P1 P2 Even G vs w \<le> alt_dist.alt_distance P1 P2 Even G u w"
      using u_vs by (rule alt_dist.alt_dist_set_mem)
    hence "alt_dist.alt_distance_set P1 P2 Even G vs w + 1 \<le> alt_dist.alt_distance P1 P2 Even G u w + 1"
      by (simp add: add_right_mono)
    thus "alt_dist.alt_distance_set P1 P2 Even G vs w + 1 \<le> alt_dist.alt_distance_set P1 P2 Odd G vs v"
      by (simp add: dist_eq[symmetric] u_eq)
    show "alt_dist.alt_distance_set P1 P2 Odd G vs v \<le> alt_dist.alt_distance_set P1 P2 Even G vs w + 1"
      using v_neigh 1(2) P1wv by (intro odd_alt_distance_set_neighbourhood)
  qed
  thus ?thesis using v_neigh P1wv by blast
qed

\<comment> \<open>Helper 1: odd-level u is in visited_odd or the unmatched next_frontier.\<close>
lemma odd_level_in_frontier:
  assumes "invar_level_bounded bfs_state" "invar_discovered_downclosed bfs_state"
          "invar_discovered_reachable bfs_state" "invar_current_level bfs_state"
          "w \<in> t_set (current bfs_state)"
          "altd_G Odd u = altd_G Even w + 1"
  shows "u \<in> t_set (visited_odd bfs_state) \<or>
         u \<in> next_frontier (Graph.digraph_abs unmatching)
               (t_set (current bfs_state)) (t_set (visited_odd bfs_state))"
proof(cases "u \<in> t_set (visited_odd bfs_state)")
  case False
  have finw: "altd_G Even w < \<infinity>"
    using assms(3,5) by (auto simp: invar_discovered_reachable_def)
  hence finu: "altd_G Odd u < \<infinity>"
    using assms(6) by (simp add: plus_eq_infty_iff_enat)
  \<comment> \<open>odd parent: y with Even level = level of w, unmatched edge (y,u)\<close>
  obtain y where y_dist: "altd_G Even y + 1 = altd_G Odd u"
             and y_neigh: "u \<in> Pair_Graph.neighbourhood G y"
             and y_unm: "unmatched_edge (y, u)"
    using finu
    unfolding alt_distance_set_def
    by (fastforce dest!: odd_alt_distance_set_parent'[OF _ srcs_invar(1)]
                  simp: unmatched_edge_def Pair_Graph.neighbourhood_def)
  have y_level: "altd_G Even y = altd_G Even w"
  proof-
    have "1 + altd_G Even y = 1 + altd_G Even w"
      using y_dist assms(6) by (simp add: add_ac)
    thus ?thesis by (simp add: enat_add_left_cancel)
  qed
  hence "y \<in> t_set (current bfs_state)"
    using assms(4,5) by (auto simp: invar_current_level_def)
  thus ?thesis
    using y_neigh y_unm False
    by (auto simp: next_frontier_def unmatched_edge_def dest: neighbourhoodD)
qed simp

\<comment> \<open>Helper 2: even-level u at current+2 is in the matched next_frontier over
   the unmatched next_frontier.\<close>
lemma even_level_in_frontier:
  assumes "invar_level_bounded bfs_state" "invar_discovered_downclosed bfs_state"
          "invar_discovered_reachable bfs_state" "invar_current_level bfs_state"
          "w \<in> t_set (current bfs_state)"
          "altd_G Even u = altd_G Even w + 2"
  shows "u \<in> next_frontier (Graph.digraph_abs matching)
               (next_frontier (Graph.digraph_abs unmatching)
                  (t_set (current bfs_state)) (t_set (visited_odd bfs_state)))
               (t_set (visited_even bfs_state) \<union> t_set (current bfs_state))"
proof-
  have finw: "altd_G Even w < \<infinity>"
    using assms(3,5) by (auto simp: invar_discovered_reachable_def)
  hence finu: "altd_G Even u < \<infinity>"
    using assms(6) by (simp add: plus_eq_infty_iff_enat)
  \<comment> \<open>Step 1: u not yet even-discovered\<close>
  have u_not_even: "u \<notin> t_set (visited_even bfs_state) \<union> t_set (current bfs_state)"
  proof
    assume hin: "u \<in> t_set (visited_even bfs_state) \<union> t_set (current bfs_state)"
    hence "u \<in> discovered bfs_state Even"
      by (auto simp: discovered_def)
    hence "altd_G Even u \<le> altd_G Even w"
      using assms(1,5) by (auto simp: invar_level_bounded_def)
    thus False
      using assms(6) finw
      by (cases "altd_G Even w") (auto simp: one_enat_def)
  qed
  \<comment> \<open>Step 2: even parent x via even_alt_distance_set_parent'\<close>
  have pos_u: "0 < altd_G Even u"
    using assms(6) finw by (cases "altd_G Even w") (auto simp: one_enat_def)
  obtain x where x_dist: "altd_G Odd x + 1 = altd_G Even u"
             and x_neigh: "u \<in> Pair_Graph.neighbourhood G x"
             and x_mat: "matched_edge (x, u)"
    using pos_u finu
    unfolding alt_distance_set_def
    by (fastforce dest!: even_alt_distance_set_parent'[OF _ _ srcs_invar(1)]
                  simp: matched_edge_def Pair_Graph.neighbourhood_def)
  \<comment> \<open>The Odd distance of x: x_dist gives altd_G Odd x = altd_G Even u - 1 = altd_G Even w + 1\<close>
  have x_odd_level: "altd_G Odd x = altd_G Even w + 1"
  proof-
    from x_dist assms(6) have combined: "altd_G Odd x + 1 = altd_G Even w + 2" by simp
    show ?thesis
    proof (cases "altd_G Odd x"; cases "altd_G Even w")
      fix n m assume hn: "altd_G Odd x = enat n" and hm: "altd_G Even w = enat m"
      from combined hn hm have nm: "n + 1 = m + 2"
        by (simp only: hn hm plus_enat_simps enat_simps enat.inject)
      from nm have nm2: "n = m + 1" by arith
      with hn hm show ?thesis
        by (simp only: hn hm nm2 enat_simps)
    next
      fix n assume hn: "altd_G Odd x = enat n" and hw: "altd_G Even w = \<infinity>"
      from combined hn hw have False
        by (simp only: hn hw enat_simps)
      thus ?thesis ..
    next
      fix m assume hx: "altd_G Odd x = \<infinity>" and hm: "altd_G Even w = enat m"
      from combined hx hm have False
        by (simp only: hx hm enat_simps)
      thus ?thesis ..
    next
      assume "altd_G Odd x = \<infinity>" "altd_G Even w = \<infinity>"
      thus ?thesis by simp
    qed
  qed
  \<comment> \<open>Step 3: x is in the unmatched next_frontier (not in visited_odd)\<close>
  have x_not_odd: "x \<notin> t_set (visited_odd bfs_state)"
  proof
    assume "x \<in> t_set (visited_odd bfs_state)"
    hence "x \<in> discovered bfs_state Odd"
      by (auto simp: discovered_def)
    hence "altd_G Odd x \<le> altd_G Even w"
      using assms(1,5) by (auto simp: invar_level_bounded_def)
    thus False
      using x_odd_level finw
      by (cases "altd_G Even w") (auto simp: one_enat_def)
  qed
  have x_in_C': "x \<in> next_frontier (Graph.digraph_abs unmatching)
                      (t_set (current bfs_state)) (t_set (visited_odd bfs_state))"
    using odd_level_in_frontier[OF assms(1,2,3,4,5)] x_odd_level x_not_odd
    by auto
  \<comment> \<open>Step 4: assemble u into the matched next_frontier\<close>
  have x_neigh_unm: "u \<in> Pair_Graph.neighbourhood (Graph.digraph_abs matching) x"
    using x_mat x_neigh by (auto simp: matched_edge_def Pair_Graph.neighbourhood_def G_def)
  thus ?thesis
    using x_in_C' u_not_even
    by (auto simp: next_frontier_def dest: neighbourhoodD)
qed



\<comment> \<open>Batch 3b: invar_level_bounded preservation.\<close>

lemma invar_level_bounded_holds_upd1[invar_holds_intros]:
  assumes "BFS_call_1_conds bfs_state" "invar_well_formed bfs_state"
          "invar_subsets bfs_state"
          "invar_level_bounded bfs_state" "invar_discovered_downclosed bfs_state"
          "invar_current_level bfs_state"
          "invar_discovered_reachable bfs_state"
  shows "invar_level_bounded (BFS_upd1 bfs_state)"
proof-
  have wf[simp]:
    "vset_inv (visited_even bfs_state)" "vset_inv (visited_odd bfs_state)"
    "vset_inv (current bfs_state)" "Graph.graph_inv (parents bfs_state)"
    using assms(2) by (auto simp: invar_well_formed_def)

  define VE' where "VE' = visited_even bfs_state \<union>\<^sub>G current bfs_state"
  define P' where "P' = expand_tree unmatching (parents bfs_state) (current bfs_state) (visited_odd bfs_state)"
  define C' where "C' = next_frontier_impl unmatching (current bfs_state) (visited_odd bfs_state)"
  define VO' where "VO' = visited_odd bfs_state \<union>\<^sub>G C'"
  define P'' where "P'' = expand_tree matching P' C' VE'"
  define C'' where "C'' = next_frontier_impl matching C' VE'"

  have upd1: "BFS_upd1 bfs_state =
    bfs_state \<lparr>parents := P'', visited_even := VE', visited_odd := VO', current := C'',
               distances := upd_dists Even matching
                              (upd_dists Odd unmatching (distances bfs_state) (current bfs_state)
                                 (visited_odd bfs_state)) C' VE'\<rparr>"
    by (simp add: BFS_upd1_def Let_def VE'_def P'_def C'_def VO'_def P''_def C''_def)

  have inv_VE'[simp]: "vset_inv VE'" by (auto simp: VE'_def)
  have inv_C'[simp]: "vset_inv C'" by (auto simp: C'_def)
  have inv_VO'[simp]: "vset_inv VO'" by (auto simp: VO'_def)

  have abs_VE': "t_set VE' = t_set (visited_even bfs_state) \<union> t_set (current bfs_state)"
    by (auto simp: VE'_def)
  have abs_C': "t_set C' = next_frontier (Graph.digraph_abs unmatching)
                             (t_set (current bfs_state)) (t_set (visited_odd bfs_state))"
    by (auto simp: C'_def)
  have abs_VO': "t_set VO' = t_set (visited_odd bfs_state) \<union> t_set C'"
    by (auto simp: VO'_def)
  have abs_C'': "t_set C'' = next_frontier (Graph.digraph_abs matching) (t_set C') (t_set VE')"
    by (auto simp: C''_def)

  \<comment> \<open>Post-state component equalities from upd1.\<close>
  have curr_post_eq: "t_set (current (BFS_upd1 bfs_state)) = t_set C''" by (simp add: upd1)
  have disc_even_post: "discovered (BFS_upd1 bfs_state) Even = t_set VE' \<union> t_set C''"
    by (simp add: upd1 discovered_def split: parity.splits)
  have disc_odd_post: "discovered (BFS_upd1 bfs_state) Odd = t_set VO'"
    by (simp add: upd1 discovered_def split: parity.splits)

  \<comment> \<open>enat monotonicity helpers.\<close>
  have enat_le_add11: "(x::enat) \<le> x + 1 + 1" for x by simp
  have enat_plus1_le_plus11: "(x::enat) + 1 \<le> x + 1 + 1" for x by simp

  \<comment> \<open>Main goal: for every v in new current C'', every discovered u is bounded.\<close>
  show ?thesis
  proof(intro invar_level_bounded_intro)
    fix v parity u
    assume v_curr_post: "v \<in> t_set (current (BFS_upd1 bfs_state))"
    assume u_disc: "u \<in> discovered (BFS_upd1 bfs_state) parity"
    have v_C'': "v \<in> t_set C''" using v_curr_post curr_post_eq by simp
    \<comment> \<open>Decompose v \<in> C'' \<rightarrow> v' \<in> C' \<rightarrow> w \<in> current.\<close>
    obtain v' where v'_C': "v' \<in> t_set C'"
               and v_neigh: "v \<in> Pair_Graph.neighbourhood (Graph.digraph_abs matching) v'"
               and v_fresh_VE': "v \<notin> t_set VE'"
      using v_C'' by (auto simp: abs_C'' next_frontier_def)
    obtain w where w_curr: "w \<in> t_set (current bfs_state)"
              and v'_neigh: "v' \<in> Pair_Graph.neighbourhood (Graph.digraph_abs unmatching) w"
              and v'_fresh: "v' \<notin> t_set (visited_odd bfs_state)"
      using v'_C' by (auto simp: abs_C' next_frontier_def)
    have v_fresh_even: "v \<notin> t_set (visited_even bfs_state) \<union> t_set (current bfs_state)"
      using v_fresh_VE' by (simp add: abs_VE')
    \<comment> \<open>Two-step distances give altd_G Even v = altd_G Even w + 1 + 1.\<close>
    have stepO: "altd_G Odd v' = altd_G Even w + 1"
      using assms(4) assms(5) assms(7) w_curr v'_neigh v'_fresh
      by (rule alt_dist_odd_step)
    have stepE: "altd_G Even v = altd_G Odd v' + 1"
      using assms(4) assms(5) assms(7) w_curr stepO v_neigh v_fresh_even
      by (rule alt_dist_even_step)
    have v_level: "altd_G Even v = altd_G Even w + 1 + 1"
      by (simp add: stepE stepO)
    show "altd_G parity u \<le> altd_G Even v"
    proof(cases parity)
      case Even
      hence u_in: "u \<in> t_set VE' \<union> t_set C''"
        using u_disc disc_even_post by simp
      show ?thesis
      proof(cases "u \<in> t_set (visited_even bfs_state) \<union> t_set (current bfs_state)")
        case True
        \<comment> \<open>u pre-Even: IH + monotonicity.\<close>
        have ih: "altd_G Even u \<le> altd_G Even w"
          using assms(4) w_curr True
          by (auto simp: invar_level_bounded_def discovered_def)
        have "altd_G Even u \<le> altd_G Even w + 1 + 1"
          by (rule order_trans[OF ih enat_le_add11])
        with Even v_level show ?thesis by simp
      next
        case False
        \<comment> \<open>u \<in> C'' (new Even): same 2-step argument; current-level gives equality.\<close>
        hence u_C'': "u \<in> t_set C''" using u_in abs_VE' by auto
        obtain u' where u'_C': "u' \<in> t_set C'"
                   and u_neigh2: "u \<in> Pair_Graph.neighbourhood (Graph.digraph_abs matching) u'"
                   and u_fresh2: "u \<notin> t_set VE'"
          using u_C'' by (auto simp: abs_C'' next_frontier_def)
        obtain w_u where wu_curr: "w_u \<in> t_set (current bfs_state)"
                     and u'_neigh2: "u' \<in> Pair_Graph.neighbourhood (Graph.digraph_abs unmatching) w_u"
                     and u'_fresh2: "u' \<notin> t_set (visited_odd bfs_state)"
          using u'_C' by (auto simp: abs_C' next_frontier_def)
        have u_fresh_even: "u \<notin> t_set (visited_even bfs_state) \<union> t_set (current bfs_state)"
          using u_fresh2 by (simp add: abs_VE')
        have stepO2: "altd_G Odd u' = altd_G Even w_u + 1"
          using assms(4) assms(5) assms(7) wu_curr u'_neigh2 u'_fresh2
          by (rule alt_dist_odd_step)
        have stepE2: "altd_G Even u = altd_G Odd u' + 1"
          using assms(4) assms(5) assms(7) wu_curr stepO2 u_neigh2 u_fresh_even
          by (rule alt_dist_even_step)
        have u_level: "altd_G Even u = altd_G Even w_u + 1 + 1"
          by (simp add: stepE2 stepO2)
        have level_eq: "altd_G Even w_u = altd_G Even w"
          using assms(6) wu_curr w_curr by (auto simp: invar_current_level_def)
        with Even u_level v_level show ?thesis by simp
      qed
    next
      case Odd
      hence u_in: "u \<in> t_set VO'"
        using u_disc disc_odd_post by simp
      show ?thesis
      proof(cases "u \<in> t_set (visited_odd bfs_state)")
        case True
        \<comment> \<open>u pre-Odd: IH + monotonicity.\<close>
        have ih: "altd_G Odd u \<le> altd_G Even w"
          using assms(4) w_curr True
          by (auto simp: invar_level_bounded_def discovered_def)
        have "altd_G Odd u \<le> altd_G Even w + 1 + 1"
          by (rule order_trans[OF ih enat_le_add11])
        with Odd v_level show ?thesis by simp
      next
        case False
        \<comment> \<open>u \<in> C' (new Odd): alt_dist_odd_step + current-level gives altd_G Odd u = w+1 \<le> w+1+1.\<close>
        hence u_C': "u \<in> t_set C'" using u_in abs_VO' by auto
        obtain w_u where wu_curr2: "w_u \<in> t_set (current bfs_state)"
                     and u_neigh3: "u \<in> Pair_Graph.neighbourhood (Graph.digraph_abs unmatching) w_u"
                     and u_fresh3: "u \<notin> t_set (visited_odd bfs_state)"
          using u_C' by (auto simp: abs_C' next_frontier_def)
        have stepO3: "altd_G Odd u = altd_G Even w_u + 1"
          using assms(4) assms(5) assms(7) wu_curr2 u_neigh3 u_fresh3
          by (rule alt_dist_odd_step)
        have level_eq2: "altd_G Even w_u = altd_G Even w"
          using assms(6) wu_curr2 w_curr by (auto simp: invar_current_level_def)
        have u_dist: "altd_G Odd u = altd_G Even w + 1"
          using stepO3 level_eq2 by simp
        have "altd_G Odd u \<le> altd_G Even w + 1 + 1"
          by (rule order_trans[OF _ enat_plus1_le_plus11]) (simp add: u_dist)
        with Odd v_level show ?thesis by simp
      qed
    qed
  qed
qed

lemma invar_level_bounded_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BFS_ret_1_conds bfs_state; invar_level_bounded bfs_state\<rbrakk> \<Longrightarrow>
     invar_level_bounded (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)

\<comment> \<open>Batch 3c: invar_discovered_downclosed preservation.\<close>

lemma invar_discovered_downclosed_holds_upd1[invar_holds_intros]:
  assumes "BFS_call_1_conds bfs_state" "invar_well_formed bfs_state"
          "invar_subsets bfs_state"
          "invar_level_bounded bfs_state" "invar_discovered_downclosed bfs_state"
          "invar_current_level bfs_state"
          "invar_discovered_reachable bfs_state"
  shows "invar_discovered_downclosed (BFS_upd1 bfs_state)"
proof-
  have wf[simp]:
    "vset_inv (visited_even bfs_state)" "vset_inv (visited_odd bfs_state)"
    "vset_inv (current bfs_state)" "Graph.graph_inv (parents bfs_state)"
    using assms(2) by (auto simp: invar_well_formed_def)

  define VE' where "VE' = visited_even bfs_state \<union>\<^sub>G current bfs_state"
  define P' where "P' = expand_tree unmatching (parents bfs_state) (current bfs_state) (visited_odd bfs_state)"
  define C' where "C' = next_frontier_impl unmatching (current bfs_state) (visited_odd bfs_state)"
  define VO' where "VO' = visited_odd bfs_state \<union>\<^sub>G C'"
  define P'' where "P'' = expand_tree matching P' C' VE'"
  define C'' where "C'' = next_frontier_impl matching C' VE'"

  have upd1: "BFS_upd1 bfs_state =
    bfs_state \<lparr>parents := P'', visited_even := VE', visited_odd := VO', current := C'',
               distances := upd_dists Even matching
                              (upd_dists Odd unmatching (distances bfs_state) (current bfs_state)
                                 (visited_odd bfs_state)) C' VE'\<rparr>"
    by (simp add: BFS_upd1_def Let_def VE'_def P'_def C'_def VO'_def P''_def C''_def)

  have inv_VE'[simp]: "vset_inv VE'" by (auto simp: VE'_def)
  have inv_C'[simp]: "vset_inv C'" by (auto simp: C'_def)
  have inv_VO'[simp]: "vset_inv VO'" by (auto simp: VO'_def)

  have abs_VE': "t_set VE' = t_set (visited_even bfs_state) \<union> t_set (current bfs_state)"
    by (auto simp: VE'_def)
  have abs_C': "t_set C' = next_frontier (Graph.digraph_abs unmatching)
                             (t_set (current bfs_state)) (t_set (visited_odd bfs_state))"
    by (auto simp: C'_def)
  have abs_VO': "t_set VO' = t_set (visited_odd bfs_state) \<union> t_set C'"
    by (auto simp: VO'_def)
  have abs_C'': "t_set C'' = next_frontier (Graph.digraph_abs matching) (t_set C') (t_set VE')"
    by (auto simp: C''_def)

  \<comment> \<open>Post-state discovered sets.\<close>
  have disc_even_post: "discovered (BFS_upd1 bfs_state) Even = t_set VE' \<union> t_set C''"
    by (simp add: upd1 discovered_def split: parity.splits)
  have disc_odd_post: "discovered (BFS_upd1 bfs_state) Odd = t_set VO'"
    by (simp add: upd1 discovered_def split: parity.splits)

  \<comment> \<open>IH: pre-state downclosed.\<close>
  have IH: "\<And>p p' v u. v \<in> discovered bfs_state p \<Longrightarrow> altd_G p' u \<le> altd_G p v
             \<Longrightarrow> u \<in> discovered bfs_state p'"
    using assms(5) unfolding invar_discovered_downclosed_def by blast

  \<comment> \<open>Pre-state discovered \<subseteq> post-state discovered (monotonicity).\<close>
  have mono_even: "discovered bfs_state Even \<subseteq> discovered (BFS_upd1 bfs_state) Even"
  proof
    fix x assume "x \<in> discovered bfs_state Even"
    hence "x \<in> t_set (visited_even bfs_state) \<union> t_set (current bfs_state)"
      by (simp add: discovered_def)
    hence "x \<in> t_set VE'" by (simp add: abs_VE')
    thus "x \<in> discovered (BFS_upd1 bfs_state) Even" by (simp add: disc_even_post)
  qed
  have mono_odd: "discovered bfs_state Odd \<subseteq> discovered (BFS_upd1 bfs_state) Odd"
  proof
    fix x assume "x \<in> discovered bfs_state Odd"
    hence "x \<in> t_set (visited_odd bfs_state)" by (simp add: discovered_def)
    hence "x \<in> t_set VO'" by (simp add: abs_VO')
    thus "x \<in> discovered (BFS_upd1 bfs_state) Odd" by (simp add: disc_odd_post)
  qed
  have mono: "discovered bfs_state p \<subseteq> discovered (BFS_upd1 bfs_state) p" for p
    using mono_even mono_odd by (cases p) simp_all

  show ?thesis
  proof(intro invar_discovered_downclosed_intro)
    fix parity parity' v u
    assume v_post: "v \<in> discovered (BFS_upd1 bfs_state) parity"
    assume u_le: "altd_G parity' u \<le> altd_G parity v"
    show "u \<in> discovered (BFS_upd1 bfs_state) parity'"
    proof(cases parity)
      case Odd
      \<comment> \<open>v \<in> discovered' Odd = t_set VO' = visited_odd \<union> C'\<close>
      hence v_VO': "v \<in> t_set VO'" using v_post disc_odd_post by simp
      show ?thesis
      proof(cases "v \<in> t_set (visited_odd bfs_state)")
        case True
        \<comment> \<open>v pre-Odd: IH gives u \<in> pre-discovered parity' \<subseteq> post-state.\<close>
        have "v \<in> discovered bfs_state Odd" using True by (auto simp: discovered_def)
        then have "u \<in> discovered bfs_state parity'"
          using IH u_le Odd by blast 
        thus ?thesis using mono by blast
      next
        case False
        \<comment> \<open>v \<in> t_set C' (new Odd vertex).\<close>
        hence v_C': "v \<in> t_set C'" using v_VO' abs_VO' by auto
        \<comment> \<open>Decompose v \<in> C': obtain w \<in> current with altd_G Odd v = altd_G Even w + 1.\<close>
        obtain w where w_curr: "w \<in> t_set (current bfs_state)"
                   and v_neigh: "v \<in> Pair_Graph.neighbourhood (Graph.digraph_abs unmatching) w"
                   and v_fresh_odd: "v \<notin> t_set (visited_odd bfs_state)"
          using v_C' by (auto simp: abs_C' next_frontier_def)
        have stepO: "altd_G Odd v = altd_G Even w + 1"
          using assms(4) assms(5) assms(7) w_curr v_neigh v_fresh_odd
          by (rule alt_dist_odd_step)
        \<comment> \<open>finw for arithmetic.\<close>
        have finw: "altd_G Even w < \<infinity>"
          using assms(7) w_curr by (auto simp: invar_discovered_reachable_def)
        obtain m where hm: "altd_G Even w = enat m"
          using finw by (cases "altd_G Even w") auto
        have even_m: "even m" using altd_G_parity[OF hm] by (simp add: parity_simps)
        \<comment> \<open>stepO in nat: altd_G Odd v = enat (m + 1).\<close>
        have v_dist: "altd_G Odd v = enat (m + 1)"
          by (simp only: stepO hm enat_simps)
        \<comment> \<open>altd_G parity' u \<le> enat (m + 1), hence finite.\<close>
        have u_le_enat: "altd_G parity' u \<le> enat (m + 1)"
        proof-
          have h1: "altd_G parity' u \<le> altd_G Odd v" using u_le Odd by simp
          show ?thesis using h1 v_dist by simp
        qed
        obtain n where hn: "altd_G parity' u = enat n"
          using u_le_enat by (cases "altd_G parity' u") (auto simp only:)
          
        have n_le: "n \<le> m + 1"
        proof-
          have "enat n \<le> enat (m + 1)" using hn u_le_enat by simp
          thus ?thesis by (simp only: enat_simps)
        qed
        show ?thesis
        proof(cases "n \<le> m")
          case True
          \<comment> \<open>u level \<le> m = altd_G Even w: IH with w \<in> discovered bfs_state Even closes.\<close>
          have "altd_G parity' u \<le> altd_G Even w" using hn hm True by (simp only: enat_simps)
          have w_disc: "w \<in> discovered bfs_state Even"
            using w_curr by (auto simp: discovered_def)
          have "u \<in> discovered bfs_state parity'" using IH[OF w_disc] \<open>altd_G parity' u \<le> altd_G Even w\<close> by blast
          thus ?thesis using mono by blast
        next
          case False
          \<comment> \<open>n = m + 1; parity' must be Odd (m even \<Longrightarrow> m+1 odd).\<close>
          hence n_eq: "n = m + 1" using n_le by arith
          have odd_n: "odd n" using n_eq even_m by arith
          \<comment> \<open>parity' = Odd: if parity' = Even then altd_G Even u = enat n with even required.\<close>
          have parity'_Odd: "parity' = Odd"
          proof(cases parity')
            case Even
            have "even n" using altd_G_parity[OF hn[simplified Even]] by (simp add: parity_simps)
            thus ?thesis using odd_n by simp
          next
            case Odd thus ?thesis by simp
          qed
          \<comment> \<open>altd_G Odd u = altd_G Even w + 1; odd_level_in_frontier.\<close>
          have u_odd_dist: "altd_G Odd u = altd_G Even w + 1"
          proof-
            have h1: "altd_G Odd u = enat n" using hn parity'_Odd by simp
            have h2: "enat n = enat m + 1" using n_eq
              by (simp only: enat_simps)
            show ?thesis using h1 h2 hm by simp
          qed
          have "u \<in> t_set (visited_odd bfs_state) \<or> u \<in> next_frontier (Graph.digraph_abs unmatching)
                     (t_set (current bfs_state)) (t_set (visited_odd bfs_state))"
            using odd_level_in_frontier[OF assms(4,5,7,6) w_curr u_odd_dist] .
          hence "u \<in> t_set VO'"
            using abs_VO' abs_C' by auto
          thus ?thesis
            using parity'_Odd disc_odd_post by simp
        qed
      qed
    next
      case Even
      \<comment> \<open>v \<in> discovered' Even = t_set VE' \<union> t_set C''.\<close>
      hence v_even_post: "v \<in> t_set VE' \<union> t_set C''" using v_post disc_even_post by simp
      show ?thesis
      proof(cases "v \<in> t_set (visited_even bfs_state) \<union> t_set (current bfs_state)")
        case True
        \<comment> \<open>v pre-Even: IH closes.\<close>
        have "v \<in> discovered bfs_state Even" using True by (auto simp: discovered_def)
        then have "u \<in> discovered bfs_state parity'" using IH u_le Even by blast
        thus ?thesis using mono by blast
      next
        case False
        \<comment> \<open>v \<in> t_set C'' (new Even vertex): v \<notin> t_set VE'.\<close>
        have v_fresh_VE': "v \<notin> t_set VE'" using False abs_VE' by simp
        hence v_C'': "v \<in> t_set C''" using v_even_post by blast
        \<comment> \<open>Decompose v \<in> C'': obtain v' \<in> C', w \<in> current.\<close>
        obtain v' where v'_C': "v' \<in> t_set C'"
                   and v_neigh2: "v \<in> Pair_Graph.neighbourhood (Graph.digraph_abs matching) v'"
                   and v_fresh_VE'2: "v \<notin> t_set VE'"
          using v_C'' by (auto simp: abs_C'' next_frontier_def)
        obtain w where w_curr: "w \<in> t_set (current bfs_state)"
                   and v'_neigh2: "v' \<in> Pair_Graph.neighbourhood (Graph.digraph_abs unmatching) w"
                   and v'_fresh_odd2: "v' \<notin> t_set (visited_odd bfs_state)"
          using v'_C' by (auto simp: abs_C' next_frontier_def)
        have v_fresh_even2: "v \<notin> t_set (visited_even bfs_state) \<union> t_set (current bfs_state)"
          using v_fresh_VE' abs_VE' by simp
        \<comment> \<open>Two-step: altd_G Even v = altd_G Even w + 2.\<close>
        have stepO2: "altd_G Odd v' = altd_G Even w + 1"
          using assms(4) assms(5) assms(7) w_curr v'_neigh2 v'_fresh_odd2
          by (rule alt_dist_odd_step)
        have stepE2: "altd_G Even v = altd_G Odd v' + 1"
          using assms(4) assms(5) assms(7) w_curr stepO2 v_neigh2 v_fresh_even2
          by (rule alt_dist_even_step)
        have v_level: "altd_G Even v = altd_G Even w + 1 + 1"
          by (simp add: stepE2 stepO2)
        \<comment> \<open>finw for arithmetic.\<close>
        have finw2: "altd_G Even w < \<infinity>"
          using assms(7) w_curr by (auto simp: invar_discovered_reachable_def)
        obtain m where hm2: "altd_G Even w = enat m"
          using finw2 by (cases "altd_G Even w") auto
        have even_m2: "even m" using altd_G_parity[OF hm2] by (simp add: parity_simps)
        \<comment> \<open>v_level in enat form: altd_G Even v = enat (m + 2).\<close>
        have v_dist2: "altd_G Even v = enat (m + 2)"
        proof-
          have h1: "altd_G Even v = enat m + 1 + 1"
            by (simp add: v_level hm2 one_enat_def plus_enat_simps(1))
          have h2: "(m + 1 + 1 :: nat) = m + 2" by arith
          thus ?thesis by (simp only: h1 h2 enat_simps)
        qed
        \<comment> \<open>altd_G parity' u \<le> enat (m + 2), hence finite.\<close>
        have u_le_enat2: "altd_G parity' u \<le> enat (m + 2)"
        proof-
          have h1: "altd_G parity' u \<le> altd_G Even v" using u_le Even by simp
          show ?thesis using h1 v_dist2 by simp
        qed
        obtain n where hn2: "altd_G parity' u = enat n"
          using u_le_enat2 
          by (cases "altd_G parity' u") (auto simp only:)
        have n_le2: "n \<le> m + 2"
        proof-
          have "enat n \<le> enat (m + 2)" using hn2 u_le_enat2 by simp
          thus ?thesis by (simp only: enat_simps)
        qed
        show ?thesis
        proof(cases "n \<le> m")
          case True
          \<comment> \<open>u level \<le> m: IH with w \<in> discovered bfs_state Even closes.\<close>
          have "altd_G parity' u \<le> altd_G Even w" using hn2 hm2 True by (simp only: enat_simps)
          have w_disc2: "w \<in> discovered bfs_state Even"
            using w_curr by (auto simp: discovered_def)
          have "u \<in> discovered bfs_state parity'" using IH[OF w_disc2] \<open>altd_G parity' u \<le> altd_G Even w\<close> by blast
          thus ?thesis using mono by blast
        next
          case False
          \<comment> \<open>m < n \<le> m + 2: split on parity of n.\<close>
          hence n_gt_m: "m < n" by arith
          show ?thesis
          proof(cases "odd n")
            case True
            \<comment> \<open>n = m + 1 (since m < n \<le> m+2 and m even \<Longrightarrow> n = m+1).\<close>
            hence n_eq2: "n = m + 1" using n_le2 even_m2 n_gt_m by presburger
            \<comment> \<open>parity' = Odd.\<close>
            have parity'_Odd2: "parity' = Odd"
            proof(cases parity')
              case Even
              have "even n" using altd_G_parity[OF hn2[simplified Even]] by (simp add: parity_simps)
              thus ?thesis using True by simp
            next
              case Odd thus ?thesis by simp
            qed
            have u_odd_dist2: "altd_G Odd u = altd_G Even w + 1"
            proof-
              have h1: "altd_G Odd u = enat n" using hn2 parity'_Odd2 by simp
              have h2: "enat n = enat m + 1" using n_eq2 by (simp only: enat_simps)
              show ?thesis using h1 h2 hm2 by simp
            qed
            have "u \<in> t_set (visited_odd bfs_state) \<or> u \<in> next_frontier (Graph.digraph_abs unmatching)
                       (t_set (current bfs_state)) (t_set (visited_odd bfs_state))"
              using odd_level_in_frontier[OF assms(4,5,7,6) w_curr u_odd_dist2] .
            hence "u \<in> t_set VO'"
              using abs_VO' abs_C' by auto
            thus ?thesis
              using parity'_Odd2 disc_odd_post by simp
          next
            case False
            \<comment> \<open>n even; m < n \<le> m+2 and m even \<Longrightarrow> n = m+2.\<close>
            hence even_n2: "even n" by simp
            hence n_eq3: "n = m + 2" using n_le2 n_gt_m even_m2 by presburger
            \<comment> \<open>parity' = Even.\<close>
            have parity'_Even: "parity' = Even"
            proof(cases parity')
              case Odd
              have "odd n" using altd_G_parity[OF hn2[simplified Odd]] by (simp add: parity_simps)
              thus ?thesis using even_n2 by simp
            next
              case Even thus ?thesis by simp
            qed
            \<comment> \<open>altd_G Even u = altd_G Even w + 2; even_level_in_frontier.\<close>
            have u_even_dist: "altd_G Even u = altd_G Even w + 2"
            proof-
              have h1: "altd_G Even u = enat n" using hn2 parity'_Even by simp
              have h2: "enat n = enat m + 2" using n_eq3 by (simp only: enat_simps)
              show ?thesis by (simp only: h1 h2 hm2)
            qed
            have u_in_C'': "u \<in> next_frontier (Graph.digraph_abs matching)
                    (next_frontier (Graph.digraph_abs unmatching)
                       (t_set (current bfs_state)) (t_set (visited_odd bfs_state)))
                    (t_set (visited_even bfs_state) \<union> t_set (current bfs_state))"
              using even_level_in_frontier[OF assms(4,5,7,6) w_curr u_even_dist] .
            hence "u \<in> t_set C''"
              by (simp add: abs_C'' abs_C' abs_VE')
            thus ?thesis
              by (simp add: parity'_Even disc_even_post)
          qed
        qed
      qed
    qed
  qed
qed

lemma invar_discovered_downclosed_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BFS_ret_1_conds bfs_state; invar_discovered_downclosed bfs_state\<rbrakk> \<Longrightarrow>
     invar_discovered_downclosed (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)

\<comment> \<open>Batch 3d: invar_current_level preservation + all three whole-loop holds lemmas.\<close>

lemma invar_current_level_holds_upd1[invar_holds_intros]:
  assumes "BFS_call_1_conds bfs_state" "invar_well_formed bfs_state"
          "invar_subsets bfs_state"
          "invar_level_bounded bfs_state" "invar_discovered_downclosed bfs_state"
          "invar_current_level bfs_state"
          "invar_discovered_reachable bfs_state"
  shows "invar_current_level (BFS_upd1 bfs_state)"
proof-
  have wf[simp]:
    "vset_inv (visited_even bfs_state)" "vset_inv (visited_odd bfs_state)"
    "vset_inv (current bfs_state)" "Graph.graph_inv (parents bfs_state)"
    using assms(2) by (auto simp: invar_well_formed_def)

  define VE' where "VE' = visited_even bfs_state \<union>\<^sub>G current bfs_state"
  define P' where "P' = expand_tree unmatching (parents bfs_state) (current bfs_state) (visited_odd bfs_state)"
  define C' where "C' = next_frontier_impl unmatching (current bfs_state) (visited_odd bfs_state)"
  define VO' where "VO' = visited_odd bfs_state \<union>\<^sub>G C'"
  define P'' where "P'' = expand_tree matching P' C' VE'"
  define C'' where "C'' = next_frontier_impl matching C' VE'"

  have upd1: "BFS_upd1 bfs_state =
    bfs_state \<lparr>parents := P'', visited_even := VE', visited_odd := VO', current := C'',
               distances := upd_dists Even matching
                              (upd_dists Odd unmatching (distances bfs_state) (current bfs_state)
                                 (visited_odd bfs_state)) C' VE'\<rparr>"
    by (simp add: BFS_upd1_def Let_def VE'_def P'_def C'_def VO'_def P''_def C''_def)

  have inv_VE'[simp]: "vset_inv VE'" by (auto simp: VE'_def)
  have inv_C'[simp]: "vset_inv C'" by (auto simp: C'_def)
  have inv_VO'[simp]: "vset_inv VO'" by (auto simp: VO'_def)

  have abs_VE': "t_set VE' = t_set (visited_even bfs_state) \<union> t_set (current bfs_state)"
    by (auto simp: VE'_def)
  have abs_C': "t_set C' = next_frontier (Graph.digraph_abs unmatching)
                             (t_set (current bfs_state)) (t_set (visited_odd bfs_state))"
    by (auto simp: C'_def)
  have abs_VO': "t_set VO' = t_set (visited_odd bfs_state) \<union> t_set C'"
    by (auto simp: VO'_def)
  have abs_C'': "t_set C'' = next_frontier (Graph.digraph_abs matching) (t_set C') (t_set VE')"
    by (auto simp: C''_def)

  have curr_post_eq: "t_set (current (BFS_upd1 bfs_state)) = t_set C''" by (simp add: upd1)

  \<comment> \<open>Helper: every v \<in> t_set C'' satisfies altd_G Even v = altd_G Even w + 1 + 1 for some w \<in> current.\<close>
  have C''_level: "\<And>v. v \<in> t_set C'' \<Longrightarrow> \<exists>w \<in> t_set (current bfs_state). altd_G Even v = altd_G Even w + 1 + 1"
  proof-
    fix v assume v_C'': "v \<in> t_set C''"
    obtain v' where v'_C': "v' \<in> t_set C'"
               and v_neigh: "v \<in> Pair_Graph.neighbourhood (Graph.digraph_abs matching) v'"
               and v_fresh_VE': "v \<notin> t_set VE'"
      using v_C'' by (auto simp: abs_C'' next_frontier_def)
    obtain w where w_curr: "w \<in> t_set (current bfs_state)"
              and v'_neigh: "v' \<in> Pair_Graph.neighbourhood (Graph.digraph_abs unmatching) w"
              and v'_fresh: "v' \<notin> t_set (visited_odd bfs_state)"
      using v'_C' by (auto simp: abs_C' next_frontier_def)
    have v_fresh_even: "v \<notin> t_set (visited_even bfs_state) \<union> t_set (current bfs_state)"
      using v_fresh_VE' by (simp add: abs_VE')
    have stepO: "altd_G Odd v' = altd_G Even w + 1"
      using assms(4) assms(5) assms(7) w_curr v'_neigh v'_fresh by (rule alt_dist_odd_step)
    have stepE: "altd_G Even v = altd_G Odd v' + 1"
      using assms(4) assms(5) assms(7) w_curr stepO v_neigh v_fresh_even by (rule alt_dist_even_step)
    have v_level: "altd_G Even v = altd_G Even w + 1 + 1"
      by (simp add: stepE stepO)
    thus "\<exists>w \<in> t_set (current bfs_state). altd_G Even v = altd_G Even w + 1 + 1"
      using w_curr by blast
  qed

  show ?thesis
  proof(intro invar_current_level_intro)
    fix v u
    assume v_post: "v \<in> t_set (current (BFS_upd1 bfs_state))"
    have v_C'': "v \<in> t_set C''" using v_post curr_post_eq by simp
    obtain wv where wv_curr: "wv \<in> t_set (current bfs_state)"
                and v_lev: "altd_G Even v = altd_G Even wv + 1 + 1"
      using C''_level[OF v_C''] by blast
    show "(u \<in> t_set (current (BFS_upd1 bfs_state))) \<longleftrightarrow> (altd_G Even u = altd_G Even v)"
    proof
      \<comment> \<open>\<rightarrow> direction: u \<in> C'' \<Longrightarrow> altd_G Even u = altd_G Even v\<close>
      assume u_post: "u \<in> t_set (current (BFS_upd1 bfs_state))"
      have u_C'': "u \<in> t_set C''" using u_post curr_post_eq by simp
      obtain wu where wu_curr: "wu \<in> t_set (current bfs_state)"
                  and u_lev: "altd_G Even u = altd_G Even wu + 1 + 1"
        using C''_level[OF u_C''] by blast
      have level_eq: "altd_G Even wu = altd_G Even wv"
        using assms(6) wu_curr wv_curr by (auto simp: invar_current_level_def)
      show "altd_G Even u = altd_G Even v"
        using u_lev v_lev level_eq by simp
    next
      \<comment> \<open>\<leftarrow> direction: altd_G Even u = altd_G Even v \<Longrightarrow> u \<in> C''\<close>
      assume level_eq: "altd_G Even u = altd_G Even v"
      \<comment> \<open>altd_G Even u = altd_G Even wv + 1 + 1 = altd_G Even wv + 2.\<close>
      have u_level: "altd_G Even u = altd_G Even wv + 2"
      proof-
        have "altd_G Even u = altd_G Even wv + 1 + 1" using level_eq v_lev by simp
        thus ?thesis by simp
      qed
      \<comment> \<open>even_level_in_frontier gives u \<in> next_frontier matching C' (VE'), i.e., t_set C''.\<close>
      have u_in_C'': "u \<in> next_frontier (Graph.digraph_abs matching)
              (next_frontier (Graph.digraph_abs unmatching)
                 (t_set (current bfs_state)) (t_set (visited_odd bfs_state)))
              (t_set (visited_even bfs_state) \<union> t_set (current bfs_state))"
        using even_level_in_frontier[OF assms(4,5,7,6) wv_curr u_level] .
      hence "u \<in> t_set C''"
        by (simp add: abs_C'' abs_C' abs_VE')
      thus "u \<in> t_set (current (BFS_upd1 bfs_state))"
        using curr_post_eq by simp
    qed
  qed
qed

lemma invar_current_level_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BFS_ret_1_conds bfs_state; invar_current_level bfs_state\<rbrakk> \<Longrightarrow>
     invar_current_level (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)

\<comment> \<open>Whole-loop holds lemmas for the three level invariants (mutually dependent, so each assumes all three).\<close>

lemma invar_level_bounded_holds[invar_holds_intros]:
  assumes "BFS_dom bfs_state" "invar_well_formed bfs_state" "invar_subsets bfs_state"
          "invar_level_bounded bfs_state" "invar_discovered_downclosed bfs_state"
          "invar_current_level bfs_state" "invar_discovered_reachable bfs_state"
  shows "invar_level_bounded (BFS bfs_state)"
  using assms(2-)
proof(induction rule: BFS_induct[OF assms(1)])
  case IH: (1 bfs_state)
  show ?case
    by (rule BFS_cases[where bfs_state = bfs_state])
       (auto intro!: IH(2-) intro: invar_holds_intros simp: BFS_simps[OF IH(1)])
qed

lemma invar_discovered_downclosed_holds[invar_holds_intros]:
  assumes "BFS_dom bfs_state" "invar_well_formed bfs_state" "invar_subsets bfs_state"
          "invar_level_bounded bfs_state" "invar_discovered_downclosed bfs_state"
          "invar_current_level bfs_state" "invar_discovered_reachable bfs_state"
  shows "invar_discovered_downclosed (BFS bfs_state)"
  using assms(2-)
proof(induction rule: BFS_induct[OF assms(1)])
  case IH: (1 bfs_state)
  show ?case
    by (rule BFS_cases[where bfs_state = bfs_state])
       (auto intro!: IH(2-) intro: invar_holds_intros simp: BFS_simps[OF IH(1)])
qed

lemma invar_current_level_holds[invar_holds_intros]:
  assumes "BFS_dom bfs_state" "invar_well_formed bfs_state" "invar_subsets bfs_state"
          "invar_level_bounded bfs_state" "invar_discovered_downclosed bfs_state"
          "invar_current_level bfs_state" "invar_discovered_reachable bfs_state"
  shows "invar_current_level (BFS bfs_state)"
  using assms(2-)
proof(induction rule: BFS_induct[OF assms(1)])
  case IH: (1 bfs_state)
  show ?case
    by (rule BFS_cases[where bfs_state = bfs_state])
       (auto intro!: IH(2-) intro: invar_holds_intros simp: BFS_simps[OF IH(1)])
qed


lemma invar_distances_eq_holds_upd1[invar_holds_intros]:
  assumes "BFS_call_1_conds bfs_state" "invar_well_formed bfs_state" "invar_subsets bfs_state"
          "invar_level_bounded bfs_state" "invar_discovered_downclosed bfs_state"
          "invar_discovered_reachable bfs_state" "invar_current_level bfs_state"
          "invar_distances_eq bfs_state"
  shows "invar_distances_eq (BFS_upd1 bfs_state)"
proof-
  have wf[simp]:
    "vset_inv (visited_even bfs_state)" "vset_inv (visited_odd bfs_state)"
    "vset_inv (current bfs_state)" "Graph.graph_inv (parents bfs_state)"
    using assms(2) by (auto simp: invar_well_formed_def)

  define VE' where "VE' = visited_even bfs_state \<union>\<^sub>G current bfs_state"
  define P' where "P' = expand_tree unmatching (parents bfs_state) (current bfs_state) (visited_odd bfs_state)"
  define C' where "C' = next_frontier_impl unmatching (current bfs_state) (visited_odd bfs_state)"
  define VO' where "VO' = visited_odd bfs_state \<union>\<^sub>G C'"
  define P'' where "P'' = expand_tree matching P' C' VE'"
  define C'' where "C'' = next_frontier_impl matching C' VE'"

  have upd1: "BFS_upd1 bfs_state =
    bfs_state \<lparr>parents := P'', visited_even := VE', visited_odd := VO', current := C'',
               distances := upd_dists Even matching
                              (upd_dists Odd unmatching (distances bfs_state) (current bfs_state)
                                 (visited_odd bfs_state)) C' VE'\<rparr>"
    by (simp add: BFS_upd1_def Let_def VE'_def P'_def C'_def VO'_def P''_def C''_def)

  have inv_VE'[simp]: "vset_inv VE'" by (auto simp: VE'_def)
  have inv_P'[simp]: "Graph.graph_inv P'" by (auto simp: P'_def)
  have inv_C'[simp]: "vset_inv C'" by (auto simp: C'_def)
  have inv_VO'[simp]: "vset_inv VO'" by (auto simp: VO'_def)

  have abs_VE': "t_set VE' = t_set (visited_even bfs_state) \<union> t_set (current bfs_state)"
    by (auto simp: VE'_def)
  have abs_C': "t_set C' = next_frontier (Graph.digraph_abs unmatching)
                             (t_set (current bfs_state)) (t_set (visited_odd bfs_state))"
    by (auto simp: C'_def)
  have abs_VO': "t_set VO' = t_set (visited_odd bfs_state) \<union> t_set C'"
    by (auto simp: VO'_def)
  have abs_C'': "t_set C'' = next_frontier (Graph.digraph_abs matching) (t_set C') (t_set VE')"
    by (auto simp: C''_def)
  have abs_P'': "Graph.digraph_abs P'' =
                   Graph.digraph_abs (parents bfs_state)
                   \<union> new_edges (Graph.digraph_abs unmatching) (t_set (current bfs_state))
                       (t_set (visited_odd bfs_state))
                   \<union> new_edges (Graph.digraph_abs matching) (t_set C') (t_set VE')"
    by (auto simp: P''_def P'_def)

  have T'_sub_G: "Graph.digraph_abs P'' \<subseteq> G"
    using invar_subsets_holds_upd1[OF assms(1,2,3)]
    by (auto simp: upd1 invar_subsets_def)
  have T_sub_T': "Graph.digraph_abs (parents bfs_state) \<subseteq> Graph.digraph_abs P''"
    by (auto simp: abs_P'')

  have mono1: "alt_distance_set (Graph.digraph_abs P'') parity v \<le> altd_T bfs_state parity v"
    for parity v
    using T_sub_T'
    by (auto simp: alt_distance_set_def intro!: alt_distance_set_subset)
  have mono2: "altd_G parity v \<le> alt_distance_set (Graph.digraph_abs P'') parity v"
    for parity v
    using T'_sub_G
    by (auto simp: alt_distance_set_def intro!: alt_distance_set_subset)
  have sandwich: "alt_distance_set (Graph.digraph_abs P'') parity v = altd_G parity v"
    if "altd_G parity v = altd_T bfs_state parity v" for parity v
    using mono1[of parity v] mono2[of parity v] that by simp

  have odd_eq: "altd_G Odd v = alt_distance_set (Graph.digraph_abs P'') Odd v"
    if "v \<in> t_set VO'" for v
  proof(cases "v \<in> t_set (visited_odd bfs_state)")
    case True
    then show ?thesis
      using assms(8) by (intro sandwich[symmetric]) (auto simp: invar_distances_eq_def)
  next
    case fresh: False
    hence vC': "v \<in> t_set C'" using that by (auto simp: abs_VO')
    then obtain v' where v': "v' \<in> t_set (current bfs_state)"
      "v \<in> Pair_Graph.neighbourhood (Graph.digraph_abs unmatching) v'"
      by (auto simp: abs_C' next_frontier_def)
    have step: "altd_G Odd v = altd_G Even v' + 1"
      using assms(4,5,6) v' fresh by (intro alt_dist_odd_step)
    have edge_T': "(v', v) \<in> Graph.digraph_abs P''" "(v', v) \<in> Graph.digraph_abs unmatching"
      using v' fresh by (auto simp: abs_P'' new_edges_def)
    have v'_eq: "alt_distance_set (Graph.digraph_abs P'') Even v' = altd_G Even v'"
    proof(cases "v' \<in> t_set srcs")
      case True
      have v'_dVs_G: "v' \<in> dVs G"
        using v'(1) assms(3) by (auto simp: invar_subsets_def)
      have v'_dVs_T': "v' \<in> dVs (Graph.digraph_abs P'')"
        using edge_T'(1) by (auto intro: dVsI(1))
      have z1: "altd_G Even v' = 0"
        using True v'_dVs_G by (auto simp: alt_distance_set_def)
      have z2: "alt_distance_set (Graph.digraph_abs P'') Even v' = 0"
        using True v'_dVs_T' by (auto simp: alt_distance_set_def)
      show ?thesis by (simp add: z1 z2)
    next
      case False
      then show ?thesis
        using assms(8) v'(1)
        by (intro sandwich) (auto simp: invar_distances_eq_def)
    qed
    have srcs_ne: "t_set srcs \<noteq> {}" using srcs_invar(1) .
    have v_nb: "v \<in> Pair_Graph.neighbourhood (Graph.digraph_abs P'') v'"
      using edge_T'(1) by (rule neighbourhoodD)
    have unm: "unmatched_edge (v', v)"
      using edge_T'(2) by (simp add: unmatched_edge_def)
    have le1: "alt_distance_set (Graph.digraph_abs P'') Odd v
                 \<le> alt_distance_set (Graph.digraph_abs P'') Even v' + 1"
      unfolding alt_distance_set_def
      by (intro odd_alt_distance_set_neighbourhood) (fact v_nb, fact srcs_ne, fact unm)
    show ?thesis
      using le1 mono2[of Odd v] by (simp add: v'_eq step[symmetric] order_antisym)
  qed

  have even_eq: "altd_G Even v = alt_distance_set (Graph.digraph_abs P'') Even v"
    if "v \<in> t_set VE' \<union> t_set C''" "v \<notin> t_set srcs" for v
  proof(cases "v \<in> t_set (visited_even bfs_state) \<union> t_set (current bfs_state)")
    case True
    then show ?thesis
      using assms(8) that(2) by (intro sandwich[symmetric]) (auto simp: invar_distances_eq_def)
  next
    case fresh: False
    hence vC'': "v \<in> t_set C''" using that(1) by (auto simp: abs_VE')
    then obtain v' where v': "v' \<in> t_set C'"
      "v \<in> Pair_Graph.neighbourhood (Graph.digraph_abs matching) v'"
      by (auto simp: abs_C'' next_frontier_def)
    from v'(1) obtain w where w: "w \<in> t_set (current bfs_state)"
      "v' \<in> Pair_Graph.neighbourhood (Graph.digraph_abs unmatching) w" "v' \<notin> t_set (visited_odd bfs_state)"
      by (auto simp: abs_C' next_frontier_def)
    have stepO: "altd_G Odd v' = altd_G Even w + 1"
      using assms(4,5,6) w by (intro alt_dist_odd_step)
    have stepE: "altd_G Even v = altd_G Odd v' + 1"
      using assms(4,5,6) w(1) stepO v'(2) fresh by (intro alt_dist_even_step)
    have edge_T': "(v', v) \<in> Graph.digraph_abs P''" "(v', v) \<in> Graph.digraph_abs matching"
      using v' fresh by (auto simp: abs_P'' new_edges_def abs_VE')
    have v'_eq: "alt_distance_set (Graph.digraph_abs P'') Odd v' = altd_G Odd v'"
      using odd_eq[of v'] v'(1) by (auto simp: abs_VO')
    have srcs_ne: "t_set srcs \<noteq> {}" using srcs_invar(1) .
    have v_nb: "v \<in> Pair_Graph.neighbourhood (Graph.digraph_abs P'') v'"
      using edge_T'(1) by (rule neighbourhoodD)
    have mat: "matched_edge (v', v)"
      using edge_T'(2) by (simp add: matched_edge_def)
    have le1: "alt_distance_set (Graph.digraph_abs P'') Even v
                 \<le> alt_distance_set (Graph.digraph_abs P'') Odd v' + 1"
      unfolding alt_distance_set_def
      by (intro even_alt_distance_set_neighbourhood) (fact v_nb, fact srcs_ne, fact mat)
    show ?thesis
      using le1 mono2[of Even v] by (simp add: v'_eq stepE[symmetric] order_antisym)
  qed

  show ?thesis
    using odd_eq even_eq
    by (auto simp: upd1 invar_distances_eq_def abs_VE' abs_VO')
qed

lemma invar_distances_eq_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BFS_ret_1_conds bfs_state; invar_distances_eq bfs_state\<rbrakk> \<Longrightarrow>
     invar_distances_eq (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_distances_eq_holds[invar_holds_intros]:
  assumes "BFS_dom bfs_state" "invar_well_formed bfs_state" "invar_subsets bfs_state"
          "invar_level_bounded bfs_state" "invar_discovered_downclosed bfs_state"
          "invar_current_level bfs_state" "invar_discovered_reachable bfs_state"
          "invar_distances_eq bfs_state"
  shows "invar_distances_eq (BFS bfs_state)"
  using assms(2-)
proof(induction rule: BFS_induct[OF assms(1)])
  case IH: (1 bfs_state)
  show ?case
    by (rule BFS_cases[where bfs_state = bfs_state])
       (auto intro!: IH(2-) intro: invar_holds_intros simp: BFS_simps[OF IH(1)])
qed

lemma BFS_correct_dists_ret_1:
  assumes "invar_distances_eq bfs_state" "BFS_ret_1_conds bfs_state"
  shows "v \<in> t_set (visited_odd bfs_state) \<Longrightarrow> altd_G Odd v = altd_T bfs_state Odd v"
    and "\<lbrakk>v \<in> t_set (visited_even bfs_state); v \<notin> t_set srcs\<rbrakk>
           \<Longrightarrow> altd_G Even v = altd_T bfs_state Even v"
  using assms by (auto simp: invar_distances_eq_def)


\<comment> \<open>I-4b: invar_distances_correct -- the labelled distance map holds the true levels.\<close>
definition "invar_distances_correct bfs_state =
  ((\<forall>v \<in> t_set (visited_odd bfs_state).
      the (lookup_dist (distances bfs_state) (Vtx Odd v)) = altd_G Odd v) \<and>
   (\<forall>v \<in> t_set (visited_even bfs_state) \<union> t_set (current bfs_state).
      the (lookup_dist (distances bfs_state) (Vtx Even v)) = altd_G Even v))"

lemma invar_distances_correct_props[invar_props_elims]:
  "invar_distances_correct bfs_state \<Longrightarrow>
   (\<lbrakk>\<forall>v \<in> t_set (visited_odd bfs_state).
        the (lookup_dist (distances bfs_state) (Vtx Odd v)) = altd_G Odd v;
      \<forall>v \<in> t_set (visited_even bfs_state) \<union> t_set (current bfs_state).
        the (lookup_dist (distances bfs_state) (Vtx Even v)) = altd_G Even v\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_distances_correct_def)

lemma invar_distances_correct_intro[invar_props_intros]:
  "\<lbrakk>\<forall>v \<in> t_set (visited_odd bfs_state).
      the (lookup_dist (distances bfs_state) (Vtx Odd v)) = altd_G Odd v;
    \<forall>v \<in> t_set (visited_even bfs_state) \<union> t_set (current bfs_state).
      the (lookup_dist (distances bfs_state) (Vtx Even v)) = altd_G Even v\<rbrakk>
   \<Longrightarrow> invar_distances_correct bfs_state"
  by (auto simp: invar_distances_correct_def)

lemma invar_distances_correct_holds_upd1[invar_holds_intros]:
  assumes "BFS_call_1_conds bfs_state" "invar_well_formed bfs_state" "invar_subsets bfs_state"
          "invar_level_bounded bfs_state" "invar_discovered_downclosed bfs_state"
          "invar_current_level bfs_state" "invar_discovered_reachable bfs_state"
          "invar_distances_correct bfs_state"
  shows "invar_distances_correct (BFS_upd1 bfs_state)"
proof-
  have wf[simp]:
    "vset_inv (visited_even bfs_state)" "vset_inv (visited_odd bfs_state)"
    "vset_inv (current bfs_state)" "Graph.graph_inv (parents bfs_state)"
    "invar_dist (distances bfs_state)"
    using assms(2) by (auto simp: invar_well_formed_def)

  define VE' where "VE' = visited_even bfs_state \<union>\<^sub>G current bfs_state"
  define P' where "P' = expand_tree unmatching (parents bfs_state) (current bfs_state) (visited_odd bfs_state)"
  define C' where "C' = next_frontier_impl unmatching (current bfs_state) (visited_odd bfs_state)"
  define VO' where "VO' = visited_odd bfs_state \<union>\<^sub>G C'"
  define P'' where "P'' = expand_tree matching P' C' VE'"
  define C'' where "C'' = next_frontier_impl matching C' VE'"
  define DM' where "DM' = upd_dists Odd unmatching (distances bfs_state) (current bfs_state) (visited_odd bfs_state)"

  have upd1: "BFS_upd1 bfs_state =
    bfs_state \<lparr>parents := P'', visited_even := VE', visited_odd := VO', current := C'',
               distances := upd_dists Even matching DM' C' VE'\<rparr>"
    by (simp add: BFS_upd1_def Let_def VE'_def P'_def C'_def VO'_def P''_def C''_def DM'_def)

  have inv_VE'[simp]: "vset_inv VE'" by (auto simp: VE'_def)
  have inv_P'[simp]: "Graph.graph_inv P'" by (auto simp: P'_def)
  have inv_C'[simp]: "vset_inv C'" by (auto simp: C'_def)
  have inv_VO'[simp]: "vset_inv VO'" by (auto simp: VO'_def)
  have inv_DM'[simp]: "invar_dist DM'" by (auto simp: DM'_def)

  have abs_VE': "t_set VE' = t_set (visited_even bfs_state) \<union> t_set (current bfs_state)"
    by (auto simp: VE'_def)
  have abs_C': "t_set C' = next_frontier (Graph.digraph_abs unmatching)
                             (t_set (current bfs_state)) (t_set (visited_odd bfs_state))"
    by (auto simp: C'_def)
  have abs_VO': "t_set VO' = t_set (visited_odd bfs_state) \<union> t_set C'"
    by (auto simp: VO'_def)
  have abs_C'': "t_set C'' = next_frontier (Graph.digraph_abs matching) (t_set C') (t_set VE')"
    by (auto simp: C''_def)

  \<comment> \<open>Step A: fresh odd copies v \<in> t_set C' get the correct value via the inner (Odd) write.\<close>
  have fresh_odd: "the (lookup_dist (upd_dists Even matching DM' C' VE') (Vtx Odd v)) = altd_G Odd v"
    if vC': "v \<in> t_set C'" for v
  proof-
    have v_nf: "v \<in> next_frontier (Graph.digraph_abs unmatching)
                    (t_set (current bfs_state)) (t_set (visited_odd bfs_state))"
      using vC' by (simp add: abs_C')
    have ex: "\<exists>u \<in> t_set (current bfs_state).
        v \<in> Pair_Graph.neighbourhood (Graph.digraph_abs unmatching) u - t_set (visited_odd bfs_state) \<and>
        lookup_dist DM' (Vtx Odd v) =
          Some (the (lookup_dist (distances bfs_state) (Vtx (other_parity Odd) u)) + 1)"
      unfolding DM'_def by (intro upd_dists(2)) (auto simp: v_nf)
    then obtain u where u_cur: "u \<in> t_set (current bfs_state)"
      and u_nb: "v \<in> Pair_Graph.neighbourhood (Graph.digraph_abs unmatching) u"
      and v_not_vo: "v \<notin> t_set (visited_odd bfs_state)"
      and inner_val: "lookup_dist DM' (Vtx Odd v) =
                        Some (the (lookup_dist (distances bfs_state) (Vtx Even u)) + 1)"
      by (auto simp: parity_simps)
    have ih_u: "the (lookup_dist (distances bfs_state) (Vtx Even u)) = altd_G Even u"
      using assms(8) u_cur by (auto simp: invar_distances_correct_def)
    have step: "altd_G Odd v = altd_G Even u + 1"
      using assms(4,5,7) u_cur u_nb v_not_vo by (intro alt_dist_odd_step)
    have outer_miss: "Vtx Odd v \<notin> Vtx Even ` next_frontier (Graph.digraph_abs matching)
                                               (t_set C') (t_set VE')"
      by (auto simp: labelled_vtx.inject)
    have outer_notouch: "lookup_dist (upd_dists Even matching DM' C' VE') (Vtx Odd v) =
                           lookup_dist DM' (Vtx Odd v)"
      by (intro upd_dists(3)) (auto simp: abs_C'' outer_miss)
    show ?thesis
      using outer_notouch inner_val ih_u step by (auto simp only: enat_simps option.sel)
  qed

  have post_odd: "the (lookup_dist (upd_dists Even matching DM' C' VE') (Vtx Odd v)) = altd_G Odd v"
    if vVO': "v \<in> t_set VO'" for v
  proof(cases "v \<in> t_set (visited_odd bfs_state)")
    case True
    have v_not_nf_odd: "Vtx Odd v \<notin> Vtx Odd ` next_frontier (Graph.digraph_abs unmatching)
                                                (t_set (current bfs_state)) (t_set (visited_odd bfs_state))"
      by (auto simp: next_frontier_def True)
    have inner_notouch: "lookup_dist DM' (Vtx Odd v) = lookup_dist (distances bfs_state) (Vtx Odd v)"
      unfolding DM'_def
      by (intro upd_dists(3)) (auto simp: abs_C' v_not_nf_odd)
    have outer_miss: "Vtx Odd v \<notin> Vtx Even ` next_frontier (Graph.digraph_abs matching)
                                               (t_set C') (t_set VE')"
      by (auto simp: labelled_vtx.inject)
    have outer_notouch: "lookup_dist (upd_dists Even matching DM' C' VE') (Vtx Odd v) =
                           lookup_dist DM' (Vtx Odd v)"
      by (intro upd_dists(3)) (auto simp: abs_C'' outer_miss)
    have ih: "the (lookup_dist (distances bfs_state) (Vtx Odd v)) = altd_G Odd v"
      using assms(8) True by (auto simp: invar_distances_correct_def)
    show ?thesis using outer_notouch inner_notouch ih by simp
  next
    case False
    hence "v \<in> t_set C'" using vVO' by (auto simp: abs_VO')
    then show ?thesis using fresh_odd by simp
  qed

  have old_even: "the (lookup_dist (upd_dists Even matching DM' C' VE') (Vtx Even v)) = altd_G Even v"
    if vVE': "v \<in> t_set VE'" for v
  proof-
    have inner_miss: "Vtx Even v \<notin> Vtx Odd ` next_frontier (Graph.digraph_abs unmatching)
                                              (t_set (current bfs_state)) (t_set (visited_odd bfs_state))"
      by (auto simp: labelled_vtx.inject)
    have inner_notouch: "lookup_dist DM' (Vtx Even v) = lookup_dist (distances bfs_state) (Vtx Even v)"
      unfolding DM'_def
      by (intro upd_dists(3)) (auto simp: abs_C' inner_miss)
    have v_not_nf_even: "Vtx Even v \<notin> Vtx Even ` next_frontier (Graph.digraph_abs matching)
                                                  (t_set C') (t_set VE')"
      by (auto simp: next_frontier_def vVE')
    have outer_notouch: "lookup_dist (upd_dists Even matching DM' C' VE') (Vtx Even v) =
                           lookup_dist DM' (Vtx Even v)"
      by (intro upd_dists(3)) (auto simp: abs_C'' v_not_nf_even)
    have ih: "the (lookup_dist (distances bfs_state) (Vtx Even v)) = altd_G Even v"
      using assms(8) vVE' by (auto simp: invar_distances_correct_def abs_VE')
    show ?thesis using outer_notouch inner_notouch ih by simp
  qed

  have fresh_even: "the (lookup_dist (upd_dists Even matching DM' C' VE') (Vtx Even v)) = altd_G Even v"
    if vC'': "v \<in> t_set C''" for v
  proof-
    have v_nf: "v \<in> next_frontier (Graph.digraph_abs matching) (t_set C') (t_set VE')"
      using vC'' by (simp add: abs_C'')
    have ex_outer: "\<exists>u \<in> t_set C'.
        v \<in> Pair_Graph.neighbourhood (Graph.digraph_abs matching) u - t_set VE' \<and>
        lookup_dist (upd_dists Even matching DM' C' VE') (Vtx Even v) =
          Some (the (lookup_dist DM' (Vtx (other_parity Even) u)) + 1)"
      by (intro upd_dists(2)) (auto simp: v_nf)
    then obtain v' where v'_C': "v' \<in> t_set C'"
      and v'_nb: "v \<in> Pair_Graph.neighbourhood (Graph.digraph_abs matching) v'"
      and v_not_VE': "v \<notin> t_set VE'"
      and outer_val: "lookup_dist (upd_dists Even matching DM' C' VE') (Vtx Even v) =
                        Some (the (lookup_dist DM' (Vtx Odd v')) + 1)"
      by (auto simp: parity_simps)
    have v'_nf: "v' \<in> next_frontier (Graph.digraph_abs unmatching)
                     (t_set (current bfs_state)) (t_set (visited_odd bfs_state))"
      using v'_C' by (simp add: abs_C')
    have ex_inner: "\<exists>u \<in> t_set (current bfs_state).
        v' \<in> Pair_Graph.neighbourhood (Graph.digraph_abs unmatching) u - t_set (visited_odd bfs_state) \<and>
        lookup_dist DM' (Vtx Odd v') =
          Some (the (lookup_dist (distances bfs_state) (Vtx (other_parity Odd) u)) + 1)"
      unfolding DM'_def by (intro upd_dists(2)) (auto simp: v'_nf)
    then obtain w where w_cur: "w \<in> t_set (current bfs_state)"
      and w_nb: "v' \<in> Pair_Graph.neighbourhood (Graph.digraph_abs unmatching) w"
      and v'_not_vo: "v' \<notin> t_set (visited_odd bfs_state)"
      and inner_val: "lookup_dist DM' (Vtx Odd v') =
                        Some (the (lookup_dist (distances bfs_state) (Vtx Even w)) + 1)"
      by (auto simp: parity_simps)
    have v_not_ve: "v \<notin> t_set (visited_even bfs_state) \<union> t_set (current bfs_state)"
      using v_not_VE' by (auto simp: abs_VE')
    have stepO: "altd_G Odd v' = altd_G Even w + 1"
      using assms(4,5,7) w_cur w_nb v'_not_vo by (intro alt_dist_odd_step)
    have stepE: "altd_G Even v = altd_G Odd v' + 1"
      using assms(4,5,7) w_cur stepO v'_nb v_not_ve by (intro alt_dist_even_step)
    have ih_w: "the (lookup_dist (distances bfs_state) (Vtx Even w)) = altd_G Even w"
      using assms(8) w_cur by (auto simp: invar_distances_correct_def)
    show ?thesis
      using outer_val inner_val ih_w stepO stepE by (auto simp only: enat_simps option.sel)
  qed

  show ?thesis
    using post_odd old_even fresh_even
    by (intro invar_distances_correct_intro)
       (auto simp: upd1 abs_VO' abs_C'' abs_VE')
qed

lemma invar_distances_correct_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BFS_ret_1_conds bfs_state; invar_distances_correct bfs_state\<rbrakk> \<Longrightarrow>
     invar_distances_correct (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_distances_correct_holds[invar_holds_intros]:
  assumes "BFS_dom bfs_state" "invar_well_formed bfs_state" "invar_subsets bfs_state"
          "invar_level_bounded bfs_state" "invar_discovered_downclosed bfs_state"
          "invar_current_level bfs_state" "invar_discovered_reachable bfs_state"
          "invar_distances_correct bfs_state"
  shows "invar_distances_correct (BFS bfs_state)"
  using assms(2-)
proof(induction rule: BFS_induct[OF assms(1)])
  case IH: (1 bfs_state)
  show ?case
    by (rule BFS_cases[where bfs_state = bfs_state])
       (auto intro!: IH(2-) intro: invar_holds_intros simp: BFS_simps[OF IH(1)])
qed

lemma BFS_correct_distances_ret_1:
  assumes "invar_distances_correct bfs_state" "BFS_ret_1_conds bfs_state"
  shows "v \<in> t_set (visited_odd bfs_state) \<Longrightarrow>
           the (lookup_dist (distances bfs_state) (Vtx Odd v)) = altd_G Odd v"
    and "v \<in> t_set (visited_even bfs_state) \<Longrightarrow>
           the (lookup_dist (distances bfs_state) (Vtx Even v)) = altd_G Even v"
  using assms by (auto simp: invar_distances_correct_def)

\<comment> \<open>Domain coverage of the distance map: every discovered copy has an entry.\<close>
definition "invar_dists_defined bfs_state =
  ((\<forall>v \<in> t_set (visited_odd bfs_state).
      lookup_dist (distances bfs_state) (Vtx Odd v) \<noteq> None) \<and>
   (\<forall>v \<in> t_set (visited_even bfs_state) \<union> t_set (current bfs_state).
      lookup_dist (distances bfs_state) (Vtx Even v) \<noteq> None))"

lemma invar_dists_defined_props[invar_props_elims]:
  "invar_dists_defined bfs_state \<Longrightarrow>
   (\<lbrakk>\<forall>v \<in> t_set (visited_odd bfs_state).
       lookup_dist (distances bfs_state) (Vtx Odd v) \<noteq> None;
     \<forall>v \<in> t_set (visited_even bfs_state) \<union> t_set (current bfs_state).
       lookup_dist (distances bfs_state) (Vtx Even v) \<noteq> None\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_dists_defined_def)

lemma invar_dists_defined_intro[invar_props_intros]:
  "\<lbrakk>\<forall>v \<in> t_set (visited_odd bfs_state).
      lookup_dist (distances bfs_state) (Vtx Odd v) \<noteq> None;
    \<forall>v \<in> t_set (visited_even bfs_state) \<union> t_set (current bfs_state).
      lookup_dist (distances bfs_state) (Vtx Even v) \<noteq> None\<rbrakk>
   \<Longrightarrow> invar_dists_defined bfs_state"
  by (auto simp: invar_dists_defined_def)


lemma invar_dists_defined_holds_upd1[invar_holds_intros]:
  assumes "BFS_call_1_conds bfs_state" "invar_well_formed bfs_state"
          "invar_dists_defined bfs_state"
  shows "invar_dists_defined (BFS_upd1 bfs_state)"
proof-
  have wf[simp]:
    "vset_inv (visited_even bfs_state)" "vset_inv (visited_odd bfs_state)"
    "vset_inv (current bfs_state)" "Graph.graph_inv (parents bfs_state)"
    "invar_dist (distances bfs_state)"
    using assms(2) by (auto simp: invar_well_formed_def)

  define VE' where "VE' = visited_even bfs_state \<union>\<^sub>G current bfs_state"
  define P' where "P' = expand_tree unmatching (parents bfs_state) (current bfs_state) (visited_odd bfs_state)"
  define C' where "C' = next_frontier_impl unmatching (current bfs_state) (visited_odd bfs_state)"
  define VO' where "VO' = visited_odd bfs_state \<union>\<^sub>G C'"
  define P'' where "P'' = expand_tree matching P' C' VE'"
  define C'' where "C'' = next_frontier_impl matching C' VE'"
  define DM' where "DM' = upd_dists Odd unmatching (distances bfs_state) (current bfs_state) (visited_odd bfs_state)"

  have upd1: "BFS_upd1 bfs_state =
    bfs_state \<lparr>parents := P'', visited_even := VE', visited_odd := VO', current := C'',
               distances := upd_dists Even matching DM' C' VE'\<rparr>"
    by (simp add: BFS_upd1_def Let_def VE'_def P'_def C'_def VO'_def P''_def C''_def DM'_def)

  have inv_VE'[simp]: "vset_inv VE'" by (auto simp: VE'_def)
  have inv_C'[simp]: "vset_inv C'" by (auto simp: C'_def)
  have inv_VO'[simp]: "vset_inv VO'" by (auto simp: VO'_def)
  have inv_DM'[simp]: "invar_dist DM'" by (auto simp: DM'_def)

  have abs_VE': "t_set VE' = t_set (visited_even bfs_state) \<union> t_set (current bfs_state)"
    by (auto simp: VE'_def)
  have abs_C': "t_set C' = next_frontier (Graph.digraph_abs unmatching)
                             (t_set (current bfs_state)) (t_set (visited_odd bfs_state))"
    by (auto simp: C'_def)
  have abs_VO': "t_set VO' = t_set (visited_odd bfs_state) \<union> t_set C'"
    by (auto simp: VO'_def)
  have abs_C'': "t_set C'' = next_frontier (Graph.digraph_abs matching) (t_set C') (t_set VE')"
    by (auto simp: C''_def)

  have old_odd_def: "v \<in> t_set (visited_odd bfs_state) \<Longrightarrow> lookup_dist (distances bfs_state) (Vtx Odd v) \<noteq> None"
    for v using assms(3) by (auto simp: invar_dists_defined_def)
  have old_even_def: "v \<in> t_set (visited_even bfs_state) \<union> t_set (current bfs_state) \<Longrightarrow>
                        lookup_dist (distances bfs_state) (Vtx Even v) \<noteq> None"
    for v using assms(3) by (auto simp: invar_dists_defined_def)

  have post_odd_def: "lookup_dist (upd_dists Even matching DM' C' VE') (Vtx Odd v) \<noteq> None"
    if vVO': "v \<in> t_set VO'" for v
  proof(cases "v \<in> t_set (visited_odd bfs_state)")
    case True
    have v_not_nf_odd: "Vtx Odd v \<notin> Vtx Odd ` next_frontier (Graph.digraph_abs unmatching)
                                                (t_set (current bfs_state)) (t_set (visited_odd bfs_state))"
      by (auto simp: next_frontier_def True)
    have inner_notouch: "lookup_dist DM' (Vtx Odd v) = lookup_dist (distances bfs_state) (Vtx Odd v)"
      unfolding DM'_def
      by (intro upd_dists(3)) (auto simp: abs_C' v_not_nf_odd)
    have outer_miss: "Vtx Odd v \<notin> Vtx Even ` next_frontier (Graph.digraph_abs matching)
                                               (t_set C') (t_set VE')"
      by (auto simp: labelled_vtx.inject)
    have outer_notouch: "lookup_dist (upd_dists Even matching DM' C' VE') (Vtx Odd v) =
                           lookup_dist DM' (Vtx Odd v)"
      by (intro upd_dists(3)) (auto simp: abs_C'' outer_miss)
    show ?thesis using outer_notouch inner_notouch old_odd_def[OF True] by simp
  next
    case False
    have vC': "v \<in> t_set C'" using vVO' False by (auto simp: abs_VO')
    have v_nf: "v \<in> next_frontier (Graph.digraph_abs unmatching)
                    (t_set (current bfs_state)) (t_set (visited_odd bfs_state))"
      using vC' by (simp add: abs_C')
    have ex: "\<exists>u \<in> t_set (current bfs_state).
        v \<in> Pair_Graph.neighbourhood (Graph.digraph_abs unmatching) u - t_set (visited_odd bfs_state) \<and>
        lookup_dist DM' (Vtx Odd v) =
          Some (the (lookup_dist (distances bfs_state) (Vtx (other_parity Odd) u)) + 1)"
      unfolding DM'_def by (intro upd_dists(2)) (auto simp: v_nf)
    then obtain u where inner_val: "lookup_dist DM' (Vtx Odd v) =
                        Some (the (lookup_dist (distances bfs_state) (Vtx Even u)) + 1)"
      by (auto simp: parity_simps)
    have outer_miss: "Vtx Odd v \<notin> Vtx Even ` next_frontier (Graph.digraph_abs matching)
                                               (t_set C') (t_set VE')"
      by (auto simp: labelled_vtx.inject)
    have outer_notouch: "lookup_dist (upd_dists Even matching DM' C' VE') (Vtx Odd v) =
                           lookup_dist DM' (Vtx Odd v)"
      by (intro upd_dists(3)) (auto simp: abs_C'' outer_miss)
    show ?thesis using outer_notouch inner_val by simp
  qed

  have old_even_def': "lookup_dist (upd_dists Even matching DM' C' VE') (Vtx Even v) \<noteq> None"
    if vVE': "v \<in> t_set VE'" for v
  proof-
    have inner_miss: "Vtx Even v \<notin> Vtx Odd ` next_frontier (Graph.digraph_abs unmatching)
                                              (t_set (current bfs_state)) (t_set (visited_odd bfs_state))"
      by (auto simp: labelled_vtx.inject)
    have inner_notouch: "lookup_dist DM' (Vtx Even v) = lookup_dist (distances bfs_state) (Vtx Even v)"
      unfolding DM'_def
      by (intro upd_dists(3)) (auto simp: abs_C' inner_miss)
    have v_not_nf_even: "Vtx Even v \<notin> Vtx Even ` next_frontier (Graph.digraph_abs matching)
                                                  (t_set C') (t_set VE')"
      by (auto simp: next_frontier_def vVE')
    have outer_notouch: "lookup_dist (upd_dists Even matching DM' C' VE') (Vtx Even v) =
                           lookup_dist DM' (Vtx Even v)"
      by (intro upd_dists(3)) (auto simp: abs_C'' v_not_nf_even)
    show ?thesis using outer_notouch inner_notouch old_even_def[OF vVE'[unfolded abs_VE']] by simp
  qed

  have fresh_even_def: "lookup_dist (upd_dists Even matching DM' C' VE') (Vtx Even v) \<noteq> None"
    if vC'': "v \<in> t_set C''" for v
  proof-
    have v_nf: "v \<in> next_frontier (Graph.digraph_abs matching) (t_set C') (t_set VE')"
      using vC'' by (simp add: abs_C'')
    have ex_outer: "\<exists>u \<in> t_set C'.
        v \<in> Pair_Graph.neighbourhood (Graph.digraph_abs matching) u - t_set VE' \<and>
        lookup_dist (upd_dists Even matching DM' C' VE') (Vtx Even v) =
          Some (the (lookup_dist DM' (Vtx (other_parity Even) u)) + 1)"
      by (intro upd_dists(2)) (auto simp: v_nf)
    then obtain u where outer_val: "lookup_dist (upd_dists Even matching DM' C' VE') (Vtx Even v) =
                        Some (the (lookup_dist DM' (Vtx Odd u)) + 1)"
      by (auto simp: parity_simps)
    show ?thesis using outer_val by simp
  qed

  show ?thesis
    using post_odd_def old_even_def' fresh_even_def
    by (intro invar_dists_defined_intro)
       (auto simp: upd1 abs_VO' abs_C'' abs_VE')
qed

lemma invar_dists_defined_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BFS_ret_1_conds bfs_state; invar_dists_defined bfs_state\<rbrakk>
     \<Longrightarrow> invar_dists_defined (BFS_ret1 bfs_state)"
  by simp

lemma invar_dists_defined_holds[invar_holds_intros]:
  assumes "BFS_dom bfs_state" "invar_well_formed bfs_state"
          "invar_dists_defined bfs_state"
  shows "invar_dists_defined (BFS bfs_state)"
  using assms(2-)
proof(induction rule: BFS_induct[OF assms(1)])
  case IH: (1 bfs_state)
  show ?case
    by (rule BFS_cases[where bfs_state = bfs_state])
       (auto intro!: IH(2-) intro: invar_holds_intros simp: BFS_simps[OF IH(1)])
qed

lemma invar_dists_defined_initial[invar_holds_intros, simp]:
  "invar_dists_defined initial_state"
  by (auto simp: invar_dists_defined_def initial_state_def)

lemma invar_distances_correct_Some:
  assumes "invar_distances_correct bfs_state" "invar_dists_defined bfs_state"
  shows "v \<in> t_set (visited_odd bfs_state) \<Longrightarrow>
           lookup_dist (distances bfs_state) (Vtx Odd v) = Some (altd_G Odd v)"
    and "v \<in> t_set (visited_even bfs_state) \<union> t_set (current bfs_state) \<Longrightarrow>
           lookup_dist (distances bfs_state) (Vtx Even v) = Some (altd_G Even v)"
proof(goal_cases)
  case 1
  hence "lookup_dist (distances bfs_state) (Vtx Odd v) \<noteq> None"
        "the (lookup_dist (distances bfs_state) (Vtx Odd v)) = altd_G Odd v"
    using assms by (auto simp: invar_dists_defined_def invar_distances_correct_def)
  then show ?case
    by (cases "lookup_dist (distances bfs_state) (Vtx Odd v)") auto
next
  case 2
  hence "lookup_dist (distances bfs_state) (Vtx Even v) \<noteq> None"
        "the (lookup_dist (distances bfs_state) (Vtx Even v)) = altd_G Even v"
    using assms by (auto simp: invar_dists_defined_def invar_distances_correct_def)
  then show ?case
    by (cases "lookup_dist (distances bfs_state) (Vtx Even v)") auto
qed
\<comment> \<open>Batch 5: P4/P5 -- completeness of the visited sets at ret.
   ROUTE: ret-time induction over the closure invariant invar_visited_closed;
   this replaces BFS_2's invar_goes_through_current route (\<section>II.5).\<close>

lemma alt_walk_snocE:
  assumes "alt_walk parity H u p v" "1 < length p"
  obtains q w where
    "p = q @ [v]" "q \<noteq> []" "w = last q"
    "alt_walk (other_parity parity) H u q w" "(w, v) \<in> H"
    "case parity of Odd \<Rightarrow> unmatched_edge (w, v) | Even \<Rightarrow> matched_edge (w, v)"
proof -
  from assms(1) have walk: "vwalk_bet H u p v"
    and alt: "alt_list unmatched_edge matched_edge (edges_of_vwalk p)"
    and len_par: "of_parity (other_parity parity) (length p)"
    by (auto elim: alt_dist.alt_vwalk_betE)
  obtain q\<^sub>0 where p_eq: "p = q\<^sub>0 @ [v]"
    using last_of_vwalk_bet'[OF walk] by blast
  have q_ne: "q\<^sub>0 \<noteq> []" using p_eq assms(2) by auto
  have p_split: "edges_of_vwalk p = edges_of_vwalk q\<^sub>0 @ [(last q\<^sub>0, v)]"
    using q_ne p_eq by (simp add: edges_of_vwalk_append_3)
  have alt_pre: "alt_list unmatched_edge matched_edge (edges_of_vwalk q\<^sub>0)"
    using alt[unfolded p_split] by (auto dest: alt_list_append_1)
  have len_q: "of_parity parity (length q\<^sub>0)"
    using len_par p_eq by (cases parity; auto simp: parity_simps)
  have prefix_walk: "vwalk_bet H u q\<^sub>0 (last q\<^sub>0)"
    using q_ne walk[unfolded p_eq]
    by (intro vwalk_bet_prefix_is_vwalk_bet; simp)
  have q_walk: "alt_walk (other_parity parity) H u q\<^sub>0 (last q\<^sub>0)"
  proof (intro alt_dist.alt_vwalk_betI[OF prefix_walk alt_pre])
    show "of_parity (other_parity (other_parity parity)) (length q\<^sub>0)"
      using len_q by (cases parity; simp add: parity_simps)
  qed
  have edge_H: "(last q\<^sub>0, v) \<in> H"
    using vwalk_bet_edges_in_edges[OF walk] p_split by auto
  have elen: "length (edges_of_vwalk q\<^sub>0) + 1 = length q\<^sub>0"
    by (rule edges_of_vwalk_length'[OF q_ne])
  have typed_edge: "case parity of Odd \<Rightarrow> unmatched_edge (last q\<^sub>0, v)
                                 | Even \<Rightarrow> matched_edge (last q\<^sub>0, v)"
  proof (cases parity)
    case Odd
    hence ev: "even (length (edges_of_vwalk q\<^sub>0))"
    proof -
      have "odd (length q\<^sub>0)" using len_q Odd by (simp add: parity_simps)
      thus ?thesis using elen 
        by presburger
    qed
    have "alt_list unmatched_edge matched_edge [(last q\<^sub>0, v)]"
      using alt[unfolded p_split] ev by (rule alt_list_split_1)
    thus ?thesis using Odd by (auto simp: alt_list_step)
  next
    case Even
    hence od: "odd (length (edges_of_vwalk q\<^sub>0))"
    proof -
      have "even (length q\<^sub>0)" using len_q Even by (simp add: parity_simps)
      thus ?thesis using elen by presburger
    qed
    have "alt_list matched_edge unmatched_edge [(last q\<^sub>0, v)]"
      using alt[unfolded p_split] od by (rule alt_list_split_2)
    thus ?thesis using Even by (auto simp: alt_list_step)
  qed
  show ?thesis
    using p_eq q_ne q_walk edge_H typed_edge
    by (fastforce intro!: that[of q\<^sub>0 "last q\<^sub>0"])
qed

lemma alt_walk_confined:
  assumes "invar_visited_closed bfs_state" "invar_srcs_even bfs_state"
          "BFS_ret_1_conds bfs_state"
          "alt_walk parity G u p v" "u \<in> t_set srcs"
  shows "v \<in> (case parity of Even \<Rightarrow> t_set (visited_even bfs_state)
                            | Odd  \<Rightarrow> t_set (visited_odd  bfs_state))"
  using assms(4)
proof (induction "length p" arbitrary: p v parity rule: less_induct)
  case less
  show ?case
  proof (cases "1 < length p")
    case False
    \<comment> \<open>length p = 1: of_parity (other_parity parity) 1 forces parity = Even;
        then v = u \<in> srcs \<subseteq> visited_even (current = \<emptyset> at ret).\<close>
    have len_p_one: "length p = 1"
    proof -
      from less.prems have "p \<noteq> []"
        by (auto elim: alt_dist.alt_vwalk_betE simp: vwalk_bet_def)
      hence "length p \<ge> 1" 
        by (simp add: Suc_leI)
      thus ?thesis using False by presburger
    qed
    have parity_even: "parity = Even"
    proof -
      from less.prems have "of_parity (other_parity parity) (length p)"
        by (auto elim: alt_dist.alt_vwalk_betE)
      thus ?thesis using len_p_one by (cases parity; simp add: parity_simps)
    qed
    have vu: "v = u"
    proof -
      from less.prems have wb: "vwalk_bet G u p v"
        by (auto elim: alt_dist.alt_vwalk_betE)
      from wb have hu: "hd p = u" and lv: "last p = v"
        by (auto simp: vwalk_bet_def)
      from len_p_one have "hd p = last p"
        by (cases p; simp)
      thus ?thesis using hu lv by simp
    qed
    have "u \<in> t_set (visited_even bfs_state)"
      using assms(2,3,5)
      by (auto simp: invar_srcs_even_def BFS_ret_1_conds_def)
    thus ?thesis using parity_even vu by simp
  next
    case True
    from alt_walk_snocE[OF less.prems True] obtain q w where qw:
      "p = q @ [v]" "q \<noteq> []" "w = last q"
      "alt_walk (other_parity parity) G u q w" "(w, v) \<in> G"
      "case parity of Odd \<Rightarrow> unmatched_edge (w, v) | Even \<Rightarrow> matched_edge (w, v)"
      by blast
    have len_lt: "length q < length p" using qw(1) by auto
    have IH: "w \<in> (case other_parity parity of
                       Even \<Rightarrow> t_set (visited_even bfs_state)
                     | Odd  \<Rightarrow> t_set (visited_odd  bfs_state))"
      using less.hyps[OF len_lt] qw(4) by blast
    show ?thesis
    proof (cases parity)
      case Odd
      \<comment> \<open>other_parity Odd = Even; w \<in> visited_even; (w,v) unmatched \<Rightarrow> v \<in> visited_odd.\<close>
      have wve: "w \<in> t_set (visited_even bfs_state)"
        using IH Odd by (simp add: parity_simps)
      have uedge: "unmatched_edge (w, v)"
        using qw(6) Odd by simp
      have nb: "v \<in> Pair_Graph.neighbourhood (Graph.digraph_abs unmatching) w"
        using uedge qw(5) by (auto simp: unmatched_edge_def dest: neighbourhoodD)
      thus ?thesis
        using assms(1) wve Odd
        by (auto simp: invar_visited_closed_def)
    next
      case Even
      \<comment> \<open>other_parity Even = Odd; w \<in> visited_odd; (w,v) matched \<Rightarrow> v \<in> visited_even \<union> current = visited_even.\<close>
      have wvo: "w \<in> t_set (visited_odd bfs_state)"
        using IH Even by (simp add: parity_simps)
      have medge: "matched_edge (w, v)"
        using qw(6) Even by simp
      have nb: "v \<in> Pair_Graph.neighbourhood (Graph.digraph_abs matching) w"
        using medge qw(5) by (auto simp: matched_edge_def dest: neighbourhoodD)
      hence "v \<in> t_set (visited_even bfs_state) \<union> t_set (current bfs_state)"
        using assms(1) wvo by (auto simp: invar_visited_closed_def)
      thus ?thesis
        using assms(3) Even by (auto simp: BFS_ret_1_conds_def)
    qed
  qed
qed

lemma BFS_correct_no_odd_walk_ret_1:   \<comment> \<open>P4\<close>
  assumes "invar_visited_closed bfs_state" "invar_srcs_even bfs_state"
          "BFS_ret_1_conds bfs_state"
          "u \<in> t_set srcs" "v \<notin> t_set (visited_odd bfs_state)"
  shows "\<not>(\<exists>p. alt_walk Odd G u p v)"
  using alt_walk_confined[OF assms(1,2,3) _ assms(4)] assms(5) by fastforce

lemma BFS_correct_no_even_walk_ret_1:  \<comment> \<open>P5\<close>
  assumes "invar_visited_closed bfs_state" "invar_srcs_even bfs_state"
          "BFS_ret_1_conds bfs_state"
          "u \<in> t_set srcs" "v \<notin> t_set (visited_even bfs_state)"
  shows "\<not>(\<exists>p. alt_walk Even G u p v)"
  using alt_walk_confined[OF assms(1,2,3) _ assms(4)] assms(5) by fastforce

\<comment> \<open>Batch 7: ret1_holds, termination, initial_state_props, final assembly.\<close>

\<comment> \<open>ret1_holds: BFS terminates in a ret-1 state (boilerplate, mirror BFS_2 line 1261).\<close>
lemma ret1_holds[ret_holds_intros]:
  assumes "BFS_dom bfs_state"
  shows "BFS_ret_1_conds (BFS bfs_state)"
proof(induction rule: BFS_induct[OF assms(1)])
  case IH: (1 bfs_state)
  show ?case
    apply(rule BFS_cases[where bfs_state = bfs_state])
    by (auto intro: ret_holds_intros intro!: IH(2-)
             simp: BFS_simps[OF IH(1)])
qed

subsection \<open>Termination\<close>

named_theorems termination_intros

declare termination_intros[intro!]

\<comment> \<open>Single measure: card (dVs G - visited_even) strictly decreases each call (D6).\<close>
definition "call_1_measure BFS_state = card (dVs G - t_set (visited_even BFS_state))"
definition "BFS_term_rel' = call_1_measure <*mlex*> {}"

lemma finite_dVs_G: "finite (dVs G)"
proof -
  have "finite (dVs (Graph.digraph_abs unmatching))"
    by (intro Graph.finite_vertices; simp)
  moreover have "finite (dVs (Graph.digraph_abs matching))"
    by (intro Graph.finite_vertices; simp)
  ultimately show ?thesis
    by (simp add: G_def dVs_union_distr)
qed

lemma call_1_measure_decr:
  assumes "BFS_call_1_conds bfs_state" "invar_well_formed bfs_state" "invar_subsets bfs_state"
          "invar_current_unvisited bfs_state"
  shows "call_1_measure (BFS_upd1 bfs_state) < call_1_measure bfs_state"
proof -
  have wf[simp]: "vset_inv (visited_even bfs_state)" "vset_inv (visited_odd bfs_state)"
                 "vset_inv (current bfs_state)"
    using assms(2) by (auto simp: invar_well_formed_def)
  have cur_ne: "t_set (current bfs_state) \<noteq> {}"
    using assms(1) by (auto simp: BFS_call_1_conds_def)
  have cur_sub: "t_set (current bfs_state) \<subseteq> dVs G"
    using assms(3) by (auto simp: invar_subsets_def)
  have cur_disj: "t_set (current bfs_state) \<inter> t_set (visited_even bfs_state) = {}"
    using assms(4) by (auto simp: invar_current_unvisited_def)
  define VE' where "VE' = visited_even bfs_state \<union>\<^sub>G current bfs_state"
  have abs_VE': "t_set VE' = t_set (visited_even bfs_state) \<union> t_set (current bfs_state)"
    by (auto simp: VE'_def)
  have upd1_VE': "t_set (visited_even (BFS_upd1 bfs_state)) = t_set VE'"
    by (auto simp: BFS_upd1_def Let_def abs_VE')
  have psubset: "dVs G - t_set VE' \<subset> dVs G - t_set (visited_even bfs_state)"
    using cur_ne cur_sub cur_disj
    using abs_VE' by auto
  show ?thesis
    unfolding call_1_measure_def upd1_VE'
    using psubset finite_dVs_G
    by (simp add: psubset_card_mono)
qed

lemma wf_term_rel: "wf BFS_term_rel'"
  by (auto simp: wf_mlex BFS_term_rel'_def)

lemma in_BFS_term_rel'[termination_intros]:
  "\<lbrakk>BFS_call_1_conds bfs_state; invar_well_formed bfs_state; invar_subsets bfs_state;
    invar_current_unvisited bfs_state\<rbrakk> \<Longrightarrow>
    (BFS_upd1 bfs_state, bfs_state) \<in> BFS_term_rel'"
  by (simp add: BFS_term_rel'_def call_1_measure_decr mlex_less)

lemma BFS_terminates[termination_intros]:
  assumes "invar_well_formed bfs_state" "invar_subsets bfs_state"
          "invar_current_unvisited bfs_state"
  shows "BFS_dom bfs_state"
  using wf_term_rel assms
proof(induction rule: wf_induct_rule)
  case (less x)
  show ?case
    apply(rule BFS_domintros)
    by (auto intro: invar_holds_intros intro!: termination_intros less)
qed

subsection \<open>Initial state -- all invariants hold\<close>

lemma not_alt_walk_in_empty[simp]:
  "\<not> alt_walk parity {} u p v"
  by (auto simp only: alt_dist.alt_vwalk_bet_def not_vwalk_bet_empty)

lemma initial_state_props[invar_holds_intros, termination_intros, simp]:
  "invar_well_formed initial_state"
  "invar_subsets initial_state"
  "invar_srcs_even initial_state"
  "invar_current_unvisited initial_state"
  "invar_parents_edges initial_state"
  "invar_visited_closed initial_state"
  "invar_discovered_reachable initial_state"
  "invar_level_bounded initial_state"
  "invar_discovered_downclosed initial_state"
  "invar_current_level initial_state"
  "invar_distances_eq initial_state"
  "invar_distances_correct initial_state"
  "BFS_dom initial_state"
proof -
  \<comment> \<open>1. invar_well_formed\<close>
  show wf: "invar_well_formed initial_state"
    using srcs_in_G finite_subset
    by (auto simp: initial_state_def invar_well_formed_def
             intro: finite_subset[OF _ Graph.finite_vertices[where G = unmatching]])

  \<comment> \<open>2. invar_subsets\<close>
  show sub: "invar_subsets initial_state"
    apply (simp add: initial_state_def invar_subsets_def G_def)
    using srcs_in_G
    by blast
     
  \<comment> \<open>3. invar_srcs_even\<close>
  show "invar_srcs_even initial_state"
    by (auto simp: initial_state_def invar_srcs_even_def)

  \<comment> \<open>4. invar_current_unvisited\<close>
  show "invar_current_unvisited initial_state"
    by (auto simp: initial_state_def invar_current_unvisited_def)

  \<comment> \<open>5. invar_parents_edges: parents = empty, so digraph_abs empty = {}, premise set empty\<close>
  show "invar_parents_edges initial_state"
    by (auto simp: initial_state_def invar_parents_edges_def)

  \<comment> \<open>6. invar_visited_closed: visited sets empty\<close>
  show "invar_visited_closed initial_state"
    by (auto simp: initial_state_def invar_visited_closed_def)

  \<comment> \<open>7. invar_discovered_reachable: srcs have altd_G Even = 0 < \<infinity>\<close>
  show dr: "invar_discovered_reachable initial_state"
  proof -
    have "\<forall>v \<in> t_set srcs. altd_G Even v < \<infinity>"
    proof
      fix v assume v: "v \<in> t_set srcs"
      have vG: "v \<in> dVs G"
        using v srcs_in_G by (fastforce simp: G_def intro: dVs_subset)
      have "altd_G Even v = 0"
        using v vG by (auto simp: alt_distance_set_def)
      thus "altd_G Even v < \<infinity>" by (auto simp only: enat_simps)
    qed
    thus ?thesis
      by (auto simp: initial_state_def invar_discovered_reachable_def)
  qed

  \<comment> \<open>8. invar_level_bounded: current = srcs all have altd_G Even = 0; discovered Odd = {} (initial)\<close>
  show lb: "invar_level_bounded initial_state"
  proof -
    have "\<forall>v \<in> t_set srcs. \<forall>parity. \<forall>u \<in> discovered initial_state parity.
        altd_G parity u \<le> altd_G Even v"
    proof (intro ballI allI)
      fix v parity u
      assume v: "v \<in> t_set srcs" and u: "u \<in> discovered initial_state parity"
      have vG: "v \<in> dVs G"
        using v srcs_in_G by (fastforce simp: G_def intro: dVs_subset)
      have v0: "altd_G Even v = 0"
        using v vG by (auto simp: alt_distance_set_def)
      have u_srcs: "u \<in> t_set srcs"
        using u by (cases parity) (auto simp: initial_state_def discovered_def)
      have uG: "u \<in> dVs G"
        using u_srcs srcs_in_G by (fastforce simp: G_def intro: dVs_subset)
      have u0: "altd_G Even u = 0"
        using u_srcs uG by (auto simp: alt_distance_set_def)
      have up: "parity = Even"
      proof (rule ccontr)
        assume "parity \<noteq> Even"
        hence "parity = Odd" by (cases parity) auto
        have odd0: "altd_G Odd u = 0"
          using u \<open>parity = Odd\<close> by (simp add: initial_state_def discovered_def)
        obtain n where hn: "altd_G Odd u = enat n"
          by (cases "altd_G Odd u") (auto simp only: enat_simps odd0)
        hence "odd n" using altd_G_parity[of Odd u n] by (simp add: parity_simps)
        moreover have "n = 0"
          using hn odd0 by (auto simp only: enat_simps)
        ultimately show False by simp
      qed
      show "altd_G parity u \<le> altd_G Even v"
        using up u0 v0 by simp
    qed
    thus ?thesis
      by (auto simp: invar_level_bounded_def initial_state_def)
  qed

  \<comment> \<open>9. invar_discovered_downclosed\<close>
  show dc: "invar_discovered_downclosed initial_state"
  proof -
    have main: "\<forall>parity parity' v u. v \<in> discovered initial_state parity \<longrightarrow>
        altd_G parity' u \<le> altd_G parity v \<longrightarrow> u \<in> discovered initial_state parity'"
    proof (intro allI impI)
      fix parity parity' v u
      assume v: "v \<in> discovered initial_state parity"
         and le: "altd_G parity' u \<le> altd_G parity v"
      have v_srcs: "v \<in> t_set srcs"
        using v by (cases parity) (auto simp: initial_state_def discovered_def)
      have vG: "v \<in> dVs G"
        using v_srcs srcs_in_G by (fastforce simp: G_def intro: dVs_subset)
      have vp: "parity = Even"
      proof (rule ccontr)
        assume "parity \<noteq> Even"
        hence "parity = Odd" by (cases parity) auto
        have odd0: "altd_G Odd v = 0"
          using v \<open>parity = Odd\<close> by (simp add: initial_state_def discovered_def)
        obtain n where hn: "altd_G Odd v = enat n"
          by (cases "altd_G Odd v") (auto simp only: enat_simps odd0)
        hence "odd n" using altd_G_parity[of Odd v n] by (simp add: parity_simps)
        moreover have "n = 0" using hn odd0 by (auto simp only: enat_simps)
        ultimately show False by simp
      qed
      have v0: "altd_G Even v = 0"
        using v_srcs vG vp by (auto simp: alt_distance_set_def)
      have u0: "altd_G parity' u = 0"
        using le v0 vp by (simp add: v0)
      have up: "parity' = Even"
      proof (rule ccontr)
        assume "parity' \<noteq> Even"
        hence "parity' = Odd" by (cases parity') auto
        obtain n where hn: "altd_G Odd u = enat n"
          using u0 \<open>parity' = Odd\<close> by (cases "altd_G Odd u") (auto simp only: enat_simps)
        hence "odd n" using altd_G_parity[of Odd u n] by (simp add: parity_simps)
        moreover have "n = 0" using hn u0 \<open>parity' = Odd\<close> by (auto simp only: enat_simps)
        ultimately show False by simp
      qed
      have uG: "u \<in> dVs G"
      proof (rule ccontr)
        assume "u \<notin> dVs G"
        hence "altd_G parity' u = \<infinity>" by (simp add: alt_distance_set_def alt_dist.alt_dist_set_inf)
        thus False using u0 by (auto simp only: enat_simps)
      qed
      have u_srcs: "u \<in> t_set srcs"
        using u0 up uG by (auto simp: alt_distance_set_def)
      show "u \<in> discovered initial_state parity'"
        using u_srcs up by (auto simp: initial_state_def discovered_def)
    qed
    thus ?thesis
      by (auto simp: invar_discovered_downclosed_def main)
  qed

  \<comment> \<open>10. invar_current_level\<close>
  show "invar_current_level initial_state"
  proof -
    have main: "\<forall>v \<in> t_set srcs. \<forall>u. (u \<in> t_set srcs) = (altd_G Even u = altd_G Even v)"
    proof (intro ballI allI)
      fix v u
      assume v: "v \<in> t_set srcs"
      have vG: "v \<in> dVs G"
        using v srcs_in_G
        by (fastforce simp: G_def intro: dVs_subset)
      have v0: "altd_G Even v = 0"
        using v vG by (auto simp: alt_distance_set_def)
      show "(u \<in> t_set srcs) = (altd_G Even u = altd_G Even v)"
      proof
        assume u: "u \<in> t_set srcs"
        have uG: "u \<in> dVs G"
          using u srcs_in_G
          by (fastforce simp: G_def intro: dVs_subset)
        show "altd_G Even u = altd_G Even v"
          using u uG alt_distance_set_def v0
          by auto
      next
        assume eq: "altd_G Even u = altd_G Even v"
        hence u0: "altd_G Even u = 0" using v0 by simp
        have uG: "u \<in> dVs G"
        proof (rule ccontr)
          assume "u \<notin> dVs G"
          hence "altd_G Even u = \<infinity>" by (simp add: alt_distance_set_def alt_dist.alt_dist_set_inf)
          thus False using u0 by (auto simp only: enat_simps)
        qed
        show "u \<in> t_set srcs"
          using u0 uG by (auto simp: alt_distance_set_def)
      qed
    qed
    thus ?thesis
      by (auto simp: initial_state_def invar_current_level_def main)
  qed

  \<comment> \<open>11. invar_distances_eq: visited sets empty; current = srcs excluded from even clause\<close>
  show "invar_distances_eq initial_state"
    by (auto simp: initial_state_def invar_distances_eq_def)

  \<comment> \<open>12. invar_distances_correct: visited sets empty; even clause on srcs from init_dists axiom\<close>
  show dc2: "invar_distances_correct initial_state"
  proof -
    have even_clause: "\<forall>v \<in> t_set (visited_even initial_state) \<union> t_set (current initial_state).
            the (lookup_dist (distances initial_state) (Vtx Even v)) = altd_G Even v"
    proof
      fix v assume v: "v \<in> t_set (visited_even initial_state) \<union> t_set (current initial_state)"
      have v_srcs: "v \<in> t_set srcs"
        using v by (auto simp: initial_state_def)
      have vG: "v \<in> dVs G"
        using v_srcs srcs_in_G by (fastforce simp: G_def intro: dVs_subset)
      have v0: "altd_G Even v = 0"
        using v_srcs vG by (auto simp: alt_distance_set_def)
      have dist0: "the (lookup_dist (distances initial_state) (Vtx Even v)) = 0"
        using v_srcs by (auto simp: initial_state_def)
      show "the (lookup_dist (distances initial_state) (Vtx Even v)) = altd_G Even v"
        by (simp add: dist0 v0)
    qed
    thus ?thesis
      by (auto simp: initial_state_def invar_distances_correct_def)
  qed

  \<comment> \<open>13. BFS_dom from BFS_terminates\<close>
  show "BFS_dom initial_state"
    using wf sub
    by (auto intro!: termination_intros simp: initial_state_def invar_current_unvisited_def)
qed

\<comment> \<open>Batch 6: P6/P7 -- all DAG walks are shortest (tightness route).\<close>

definition "invar_parents_tight bfs_state =
  (\<forall>w v. (w, v) \<in> Graph.digraph_abs (parents bfs_state) \<longrightarrow>
     ((w, v) \<in> Graph.digraph_abs unmatching \<longrightarrow> altd_G Odd v = altd_G Even w + 1) \<and>
     ((w, v) \<in> Graph.digraph_abs matching \<longrightarrow> altd_G Even v = altd_G Odd w + 1))"

lemma invar_parents_tight_props[invar_props_elims]:
  "invar_parents_tight bfs_state \<Longrightarrow>
   (\<lbrakk>\<And>w v. \<lbrakk>(w, v) \<in> Graph.digraph_abs (parents bfs_state);
            (w, v) \<in> Graph.digraph_abs unmatching\<rbrakk> \<Longrightarrow> altd_G Odd v = altd_G Even w + 1;
     \<And>w v. \<lbrakk>(w, v) \<in> Graph.digraph_abs (parents bfs_state);
            (w, v) \<in> Graph.digraph_abs matching\<rbrakk> \<Longrightarrow> altd_G Even v = altd_G Odd w + 1\<rbrakk> \<Longrightarrow> P)
   \<Longrightarrow> P"
  by (auto simp: invar_parents_tight_def)

lemma invar_parents_tight_intro[invar_props_intros]:
  "\<lbrakk>\<And>w v. \<lbrakk>(w, v) \<in> Graph.digraph_abs (parents bfs_state);
           (w, v) \<in> Graph.digraph_abs unmatching\<rbrakk> \<Longrightarrow> altd_G Odd v = altd_G Even w + 1;
    \<And>w v. \<lbrakk>(w, v) \<in> Graph.digraph_abs (parents bfs_state);
           (w, v) \<in> Graph.digraph_abs matching\<rbrakk> \<Longrightarrow> altd_G Even v = altd_G Odd w + 1\<rbrakk>
   \<Longrightarrow> invar_parents_tight bfs_state"
  by (auto simp: invar_parents_tight_def)

lemma invar_parents_tight_holds_upd1[invar_holds_intros]:
  assumes "BFS_call_1_conds bfs_state" "invar_well_formed bfs_state"
          "invar_level_bounded bfs_state" "invar_discovered_downclosed bfs_state"
          "invar_discovered_reachable bfs_state"
          "invar_parents_tight bfs_state"
  shows "invar_parents_tight (BFS_upd1 bfs_state)"
proof-
  have wf[simp]:
    "vset_inv (visited_even bfs_state)" "vset_inv (visited_odd bfs_state)"
    "vset_inv (current bfs_state)" "Graph.graph_inv (parents bfs_state)"
    using assms(2) by (auto simp: invar_well_formed_def)

  define VE' where "VE' = visited_even bfs_state \<union>\<^sub>G current bfs_state"
  define P' where "P' = expand_tree unmatching (parents bfs_state) (current bfs_state) (visited_odd bfs_state)"
  define C' where "C' = next_frontier_impl unmatching (current bfs_state) (visited_odd bfs_state)"
  define VO' where "VO' = visited_odd bfs_state \<union>\<^sub>G C'"
  define P'' where "P'' = expand_tree matching P' C' VE'"
  define C'' where "C'' = next_frontier_impl matching C' VE'"

  have upd1: "BFS_upd1 bfs_state =
    bfs_state \<lparr>parents := P'', visited_even := VE', visited_odd := VO', current := C'',
               distances := upd_dists Even matching
                              (upd_dists Odd unmatching (distances bfs_state) (current bfs_state)
                                 (visited_odd bfs_state)) C' VE'\<rparr>"
    by (simp add: BFS_upd1_def Let_def VE'_def P'_def C'_def VO'_def P''_def C''_def)

  have inv_VE'[simp]: "vset_inv VE'" by (auto simp: VE'_def)
  have inv_P'[simp]: "Graph.graph_inv P'" by (auto simp: P'_def)
  have inv_C'[simp]: "vset_inv C'" by (auto simp: C'_def)

  have abs_VE': "t_set VE' = t_set (visited_even bfs_state) \<union> t_set (current bfs_state)"
    by (auto simp: VE'_def)
  have abs_C': "t_set C' = next_frontier (Graph.digraph_abs unmatching)
                             (t_set (current bfs_state)) (t_set (visited_odd bfs_state))"
    by (auto simp: C'_def)
  have abs_P'': "Graph.digraph_abs P'' =
                   Graph.digraph_abs (parents bfs_state)
                   \<union> new_edges (Graph.digraph_abs unmatching) (t_set (current bfs_state))
                       (t_set (visited_odd bfs_state))
                   \<union> new_edges (Graph.digraph_abs matching) (t_set C') (t_set VE')"
    by (auto simp: P''_def P'_def)

  have tight1: "altd_G Odd v = altd_G Even w + 1"
    if "(w, v) \<in> new_edges (Graph.digraph_abs unmatching)
                   (t_set (current bfs_state)) (t_set (visited_odd bfs_state))" for w v
  proof-
    have w_cur: "w \<in> t_set (current bfs_state)"
     and v_nb: "v \<in> Pair_Graph.neighbourhood (Graph.digraph_abs unmatching) w"
     and v_fresh: "v \<notin> t_set (visited_odd bfs_state)"
      using that by (auto simp: new_edges_def)
    show ?thesis
      by (intro alt_dist_odd_step)
         (fact assms(3), fact assms(4), fact assms(5), fact w_cur, fact v_nb, fact v_fresh)
  qed

  have tight2: "altd_G Even v = altd_G Odd w + 1"
    if "(w, v) \<in> new_edges (Graph.digraph_abs matching) (t_set C') (t_set VE')" for w v
  proof-
    have w_C': "w \<in> t_set C'"
     and v_nb: "v \<in> Pair_Graph.neighbourhood (Graph.digraph_abs matching) w"
     and v_fresh': "v \<notin> t_set VE'"
      using that by (auto simp: new_edges_def)
    from w_C' obtain w0 where w0: "w0 \<in> t_set (current bfs_state)"
      "w \<in> Pair_Graph.neighbourhood (Graph.digraph_abs unmatching) w0"
      "w \<notin> t_set (visited_odd bfs_state)"
      by (auto simp: abs_C' next_frontier_def)
    have stepO: "altd_G Odd w = altd_G Even w0 + 1"
      by (intro alt_dist_odd_step)
         (fact assms(3), fact assms(4), fact assms(5), fact w0(1), fact w0(2), fact w0(3))
    have v_fresh: "v \<notin> t_set (visited_even bfs_state) \<union> t_set (current bfs_state)"
      using v_fresh' by (simp add: abs_VE')
    show ?thesis
      by (intro alt_dist_even_step)
         (fact assms(3), fact assms(4), fact assms(5), fact w0(1), fact stepO,
          fact v_nb, fact v_fresh)
  qed

  have not_matched1: "(w, v) \<notin> Graph.digraph_abs matching"
    if "(w, v) \<in> new_edges (Graph.digraph_abs unmatching)
                   (t_set (current bfs_state)) (t_set (visited_odd bfs_state))" for w v
  proof-
    have "(w, v) \<in> Graph.digraph_abs unmatching"
      using that by (auto simp: new_edges_def Pair_Graph.neighbourhood_def)
    thus ?thesis using matching_unmatching_disjoint by blast
  qed
  have not_unmatched2: "(w, v) \<notin> Graph.digraph_abs unmatching"
    if "(w, v) \<in> new_edges (Graph.digraph_abs matching) (t_set C') (t_set VE')" for w v
  proof-
    have "(w, v) \<in> Graph.digraph_abs matching"
      using that by (auto simp: new_edges_def Pair_Graph.neighbourhood_def)
    thus ?thesis using matching_unmatching_disjoint by blast
  qed

  show ?thesis
  proof(intro invar_parents_tight_intro, goal_cases)
    case (1 w v)
    then show ?case
      using assms(6) tight1 not_unmatched2
      by (auto simp: upd1 abs_P'' invar_parents_tight_def)
  next
    case (2 w v)
    then show ?case
      using assms(6) tight2 not_matched1
      by (auto simp: upd1 abs_P'' invar_parents_tight_def)
  qed
qed

lemma invar_parents_tight_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BFS_ret_1_conds bfs_state; invar_parents_tight bfs_state\<rbrakk>
     \<Longrightarrow> invar_parents_tight (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_parents_tight_holds[invar_holds_intros]:
   assumes "BFS_dom bfs_state" "invar_well_formed bfs_state" "invar_subsets bfs_state"
           "invar_level_bounded bfs_state" "invar_discovered_downclosed bfs_state"
           "invar_current_level bfs_state" "invar_discovered_reachable bfs_state"
           "invar_parents_tight bfs_state"
   shows "invar_parents_tight (BFS bfs_state)"
  using assms(2-)
proof(induction rule: BFS_induct[OF assms(1)])
  case IH: (1 bfs_state)
  show ?case
    apply(rule BFS_cases[where bfs_state = bfs_state])
    by (auto intro!: IH(2-) intro: invar_holds_intros  simp: BFS_simps[OF IH(1)])
qed

lemma tight_walks_shortest:
  assumes "invar_parents_tight bfs_state" "u \<in> t_set srcs"
          "alt_walk parity (Graph.digraph_abs (parents bfs_state)) u p v"
  shows "enat (length p - 1) = altd_G parity v"
  using assms(3)
proof(induction "length p" arbitrary: p v parity rule: less_induct)
  case less
  show ?case
  proof(cases "1 < length p")
    case False
    have p_ne: "p \<noteq> []" and hd_p: "hd p = u" and last_p: "last p = v"
      using less.prems by (auto elim!: alt_dist.alt_vwalk_betE
                                 dest: hd_of_vwalk_bet' last_of_vwalk_bet)
    hence p_u: "p = [u]" and v_u: "v = u"
      using False by (cases p; auto)+
    have par: "parity = Even"
      using less.prems p_u
      by (cases parity) (auto simp: parity_simps elim!: alt_dist.alt_vwalk_betE)
    have u_dVs: "u \<in> dVs G"
      using srcs_in_G assms(2) by (fastforce simp: G_def dVs_union_distr)
    have "altd_G Even u = 0"
      using u_dVs assms(2)
      unfolding alt_distance_set_def
      by (simp add: distance_set_0)
    thus ?thesis
      using p_u v_u par by (auto simp: enat_simps)
  next
    case True
    from alt_walk_snocE[OF less.prems True] obtain q w where qw:
      "p = q @ [v]" "q \<noteq> []" "w = last q"
      "alt_walk (other_parity parity) (Graph.digraph_abs (parents bfs_state)) u q w"
      "(w, v) \<in> Graph.digraph_abs (parents bfs_state)"
      "case parity of Odd \<Rightarrow> unmatched_edge (w, v) | Even \<Rightarrow> matched_edge (w, v)"
      by blast
    have IH: "enat (length q - 1) = altd_G (other_parity parity) w"
      using less.hyps qw(1,4) by auto
    have len_p: "length p - 1 = length q" and len_q: "1 \<le> length q"
      using qw(1,2) by (auto simp: Suc_le_eq)
    show ?thesis
    proof(cases parity)
      case Odd
      hence e_unm: "(w, v) \<in> Graph.digraph_abs unmatching"
        using qw(6) by (auto simp: unmatched_edge_def)
      have tight: "altd_G Odd v = altd_G Even w + 1"
        using assms(1) qw(5) e_unm by (auto simp: invar_parents_tight_def)
      have IH': "enat (length q - 1) = altd_G Even w"
        using IH Odd by (simp add: parity_simps)
      have "enat (length q) = enat (length q - 1) + 1"
        using len_q by (auto simp only: enat_simps)
      also have "\<dots> = altd_G Even w + 1"
        using IH' by simp
      also have "\<dots> = altd_G Odd v"
        using tight by simp
      finally show ?thesis
        using Odd len_p by simp
    next
      case Even
      hence e_mat: "(w, v) \<in> Graph.digraph_abs matching"
        using qw(6) by (auto simp: matched_edge_def)
      have tight: "altd_G Even v = altd_G Odd w + 1"
        using assms(1) qw(5) e_mat by (auto simp: invar_parents_tight_def)
      have IH': "enat (length q - 1) = altd_G Odd w"
        using IH Even by (simp add: parity_simps)
      have "enat (length q) = enat (length q - 1) + 1"
        using len_q by (auto simp only: enat_simps)
      also have "\<dots> = altd_G Odd w + 1"
        using IH' by simp
      also have "\<dots> = altd_G Even v"
        using tight by simp
      finally show ?thesis
        using Even len_p by simp
    qed
  qed
qed

definition "invar_parents_shortest_alt bfs_state =
  (\<forall>u p v parity. u \<in> t_set srcs \<longrightarrow>
     alt_walk parity (Graph.digraph_abs (parents bfs_state)) u p v \<longrightarrow>
     enat (length p - 1) = altd_G parity v)"

lemma invar_parents_tight_shortest_alt:
  "invar_parents_tight bfs_state \<Longrightarrow> invar_parents_shortest_alt bfs_state"
  using tight_walks_shortest by (force simp: invar_parents_shortest_alt_def)

lemma invar_parents_tight_initial[invar_holds_intros, simp]:
  "invar_parents_tight initial_state"
  by (auto simp: invar_parents_tight_def initial_state_def invar_parents_edges_def)

subsection \<open>Final assembly: BFS correctness at BFS initial_state\<close>

lemma BFS_correct_subsets:
  "invar_subsets (BFS initial_state)"
  by (intro invar_subsets_holds initial_state_props)

lemma BFS_correct_reachable_ret_1:
  assumes "invar_discovered_reachable bfs_state"
  shows "v \<in> t_set (visited_odd bfs_state) \<Longrightarrow> altd_G Odd v < \<infinity>"
    and "v \<in> t_set (visited_even bfs_state) \<Longrightarrow> altd_G Even v < \<infinity>"
  using assms by (auto simp: invar_discovered_reachable_def)

lemma BFS_final_ret_conds: "BFS_ret_1_conds (BFS initial_state)"
  by (auto intro: ret_holds_intros termination_intros initial_state_props)

lemma BFS_final_current_empty: "t_set (current (BFS initial_state)) = {}"
  using BFS_final_ret_conds by (auto simp: BFS_ret_1_conds_def)

lemma BFS_correct_well_formed: "invar_well_formed (BFS initial_state)"
  by (intro invar_well_formed_holds initial_state_props)

subsection \<open>A single validity predicate for the output DAG\<close>

definition "valid_alt_BFS_DAG T dists VisE VisO =
  (\<comment> \<open>A: structural soundness\<close>
   Graph.digraph_abs T \<subseteq> G \<and>
   dVs (Graph.digraph_abs T) \<subseteq> t_set VisE \<union> t_set VisO \<and>
   (\<forall>u v. (u, v) \<in> Graph.digraph_abs T \<longrightarrow>
      ((u, v) \<in> Graph.digraph_abs unmatching \<and> u \<in> t_set VisE \<and> v \<in> t_set VisO) \<or>
      ((u, v) \<in> Graph.digraph_abs matching   \<and> u \<in> t_set VisO \<and> v \<in> t_set VisE)) \<and>
   \<comment> \<open>B: the visited sets are exactly the alt-reachable sets\<close>
   (\<forall>v \<in> t_set VisO. altd_G Odd v \<noteq> \<infinity>) \<and>
   (\<forall>v \<in> t_set VisE. altd_G Even v \<noteq> \<infinity>) \<and>
   (\<forall>u \<in> t_set srcs. \<forall>v p. alt_walk Odd  G u p v \<longrightarrow> v \<in> t_set VisO) \<and>
   (\<forall>u \<in> t_set srcs. \<forall>v p. alt_walk Even G u p v \<longrightarrow> v \<in> t_set VisE) \<and>
   \<comment> \<open>C1: the distance map holds the true levels (and is defined)\<close>
   (\<forall>v \<in> t_set VisO. lookup_dist dists (Vtx Odd v)  = Some (altd_G Odd v)) \<and>
   (\<forall>v \<in> t_set VisE. lookup_dist dists (Vtx Even v) = Some (altd_G Even v)) \<and>
   \<comment> \<open>C2: the DAG-induced levels agree (Even: away from srcs, cf. P2/P3)\<close>
   (\<forall>v \<in> t_set VisO. alt_distance_set (Graph.digraph_abs T) Odd v = altd_G Odd v) \<and>
   (\<forall>v \<in> t_set VisE. v \<notin> t_set srcs \<longrightarrow>
        alt_distance_set (Graph.digraph_abs T) Even v = altd_G Even v) \<and>
   \<comment> \<open>D: tightness -- every alternating DAG-walk from a source is shortest\<close>
   (\<forall>u \<in> t_set srcs. \<forall>p v parity.
        alt_walk parity (Graph.digraph_abs T) u p v \<longrightarrow>
        enat (length p - 1) = altd_G parity v))"

definition "valid_alt_BFS_DAG_impl T dists VisE VisO =
  (Graph.graph_inv T \<and> vset_inv VisE \<and> vset_inv VisO \<and> invar_dist dists \<and>
   finite (t_set VisE) \<and> finite (t_set VisO) \<and>
   valid_alt_BFS_DAG T dists VisE VisO)"

lemma valid_alt_BFS_DAG_props:
  assumes "valid_alt_BFS_DAG T dists VisE VisO"
  shows "Graph.digraph_abs T \<subseteq> G"
    and "dVs (Graph.digraph_abs T) \<subseteq> t_set VisE \<union> t_set VisO"
    and "\<And>u v. (u, v) \<in> Graph.digraph_abs T \<Longrightarrow>
           ((u, v) \<in> Graph.digraph_abs unmatching \<and> u \<in> t_set VisE \<and> v \<in> t_set VisO) \<or>
           ((u, v) \<in> Graph.digraph_abs matching   \<and> u \<in> t_set VisO \<and> v \<in> t_set VisE)"
    and "\<And>v. v \<in> t_set VisO \<Longrightarrow> altd_G Odd v \<noteq> \<infinity>"
    and "\<And>v. v \<in> t_set VisE \<Longrightarrow> altd_G Even v \<noteq> \<infinity>"
    and "\<And>u v p. u \<in> t_set srcs \<Longrightarrow> alt_walk Odd  G u p v \<Longrightarrow> v \<in> t_set VisO"
    and "\<And>u v p. u \<in> t_set srcs \<Longrightarrow> alt_walk Even G u p v \<Longrightarrow> v \<in> t_set VisE"
    and "\<And>v. v \<in> t_set VisO \<Longrightarrow> lookup_dist dists (Vtx Odd v)  = Some (altd_G Odd v)"
    and "\<And>v. v \<in> t_set VisE \<Longrightarrow> lookup_dist dists (Vtx Even v) = Some (altd_G Even v)"
    and "\<And>v. v \<in> t_set VisO \<Longrightarrow> alt_distance_set (Graph.digraph_abs T) Odd v = altd_G Odd v"
    and "\<And>v. v \<in> t_set VisE \<Longrightarrow> v \<notin> t_set srcs \<Longrightarrow>
           alt_distance_set (Graph.digraph_abs T) Even v = altd_G Even v"
    and "\<And>u p v parity. u \<in> t_set srcs \<Longrightarrow> alt_walk parity (Graph.digraph_abs T) u p v \<Longrightarrow>
           enat (length p - 1) = altd_G parity v"
  using assms by (fastforce simp: valid_alt_BFS_DAG_def)+

lemma valid_alt_BFS_DAG_intro:
  assumes "Graph.digraph_abs T \<subseteq> G"
      and "dVs (Graph.digraph_abs T) \<subseteq> t_set VisE \<union> t_set VisO"
      and "\<And>u v. (u, v) \<in> Graph.digraph_abs T \<Longrightarrow>
             ((u, v) \<in> Graph.digraph_abs unmatching \<and> u \<in> t_set VisE \<and> v \<in> t_set VisO) \<or>
             ((u, v) \<in> Graph.digraph_abs matching   \<and> u \<in> t_set VisO \<and> v \<in> t_set VisE)"
      and "\<And>v. v \<in> t_set VisO \<Longrightarrow> altd_G Odd v \<noteq> \<infinity>"
      and "\<And>v. v \<in> t_set VisE \<Longrightarrow> altd_G Even v \<noteq> \<infinity>"
      and "\<And>u v p. u \<in> t_set srcs \<Longrightarrow> alt_walk Odd  G u p v \<Longrightarrow> v \<in> t_set VisO"
      and "\<And>u v p. u \<in> t_set srcs \<Longrightarrow> alt_walk Even G u p v \<Longrightarrow> v \<in> t_set VisE"
      and "\<And>v. v \<in> t_set VisO \<Longrightarrow> lookup_dist dists (Vtx Odd v)  = Some (altd_G Odd v)"
      and "\<And>v. v \<in> t_set VisE \<Longrightarrow> lookup_dist dists (Vtx Even v) = Some (altd_G Even v)"
      and "\<And>v. v \<in> t_set VisO \<Longrightarrow> alt_distance_set (Graph.digraph_abs T) Odd v = altd_G Odd v"
      and "\<And>v. v \<in> t_set VisE \<Longrightarrow> v \<notin> t_set srcs \<Longrightarrow>
             alt_distance_set (Graph.digraph_abs T) Even v = altd_G Even v"
      and "\<And>u p v parity. u \<in> t_set srcs \<Longrightarrow> alt_walk parity (Graph.digraph_abs T) u p v \<Longrightarrow>
             enat (length p - 1) = altd_G parity v"
  shows "valid_alt_BFS_DAG T dists VisE VisO"
  unfolding valid_alt_BFS_DAG_def
  by (intro conjI ballI allI impI assms(1,2))
     (use assms(3-) in blast)+

lemma valid_alt_BFS_DAG_E:
  assumes "valid_alt_BFS_DAG T dists VisE VisO"
    and "\<lbrakk>Graph.digraph_abs T \<subseteq> G;
          dVs (Graph.digraph_abs T) \<subseteq> t_set VisE \<union> t_set VisO;
          \<And>u v. (u, v) \<in> Graph.digraph_abs T \<Longrightarrow>
            ((u, v) \<in> Graph.digraph_abs unmatching \<and> u \<in> t_set VisE \<and> v \<in> t_set VisO) \<or>
            ((u, v) \<in> Graph.digraph_abs matching   \<and> u \<in> t_set VisO \<and> v \<in> t_set VisE);
          \<And>v. v \<in> t_set VisO \<Longrightarrow> altd_G Odd v \<noteq> \<infinity>;
          \<And>v. v \<in> t_set VisE \<Longrightarrow> altd_G Even v \<noteq> \<infinity>;
          \<And>u v p. u \<in> t_set srcs \<Longrightarrow> alt_walk Odd  G u p v \<Longrightarrow> v \<in> t_set VisO;
          \<And>u v p. u \<in> t_set srcs \<Longrightarrow> alt_walk Even G u p v \<Longrightarrow> v \<in> t_set VisE;
          \<And>v. v \<in> t_set VisO \<Longrightarrow> lookup_dist dists (Vtx Odd v)  = Some (altd_G Odd v);
          \<And>v. v \<in> t_set VisE \<Longrightarrow> lookup_dist dists (Vtx Even v) = Some (altd_G Even v);
          \<And>v. v \<in> t_set VisO \<Longrightarrow>
            alt_distance_set (Graph.digraph_abs T) Odd v = altd_G Odd v;
          \<And>v. v \<in> t_set VisE \<Longrightarrow> v \<notin> t_set srcs \<Longrightarrow>
            alt_distance_set (Graph.digraph_abs T) Even v = altd_G Even v;
          \<And>u p v parity. u \<in> t_set srcs \<Longrightarrow>
            alt_walk parity (Graph.digraph_abs T) u p v \<Longrightarrow>
            enat (length p - 1) = altd_G parity v\<rbrakk> \<Longrightarrow> P"
  shows P
  by (rule assms(2)) (fact valid_alt_BFS_DAG_props[OF assms(1)])+

lemma valid_alt_BFS_DAG_impl_props:
  assumes "valid_alt_BFS_DAG_impl T dists VisE VisO"
  shows "Graph.graph_inv T" and "vset_inv VisE" and "vset_inv VisO"
    and "invar_dist dists"
    and "finite (t_set VisE)" and "finite (t_set VisO)"
    and "valid_alt_BFS_DAG T dists VisE VisO"
  using assms by (auto simp: valid_alt_BFS_DAG_impl_def)

lemma valid_alt_BFS_DAG_impl_intro:
  "\<lbrakk>Graph.graph_inv T; vset_inv VisE; vset_inv VisO; invar_dist dists;
    finite (t_set VisE); finite (t_set VisO);
    valid_alt_BFS_DAG T dists VisE VisO\<rbrakk>
   \<Longrightarrow> valid_alt_BFS_DAG_impl T dists VisE VisO"
  by (auto simp: valid_alt_BFS_DAG_impl_def)

lemma valid_alt_BFS_DAG_impl_E:
  assumes "valid_alt_BFS_DAG_impl T dists VisE VisO"
    and "\<lbrakk>Graph.graph_inv T; vset_inv VisE; vset_inv VisO; invar_dist dists;
          finite (t_set VisE); finite (t_set VisO);
          valid_alt_BFS_DAG T dists VisE VisO\<rbrakk> \<Longrightarrow> P"
  shows P
  by (rule assms(2)) (rule valid_alt_BFS_DAG_impl_props[OF assms(1)])+

lemmas valid_DAG_intros = valid_alt_BFS_DAG_intro valid_alt_BFS_DAG_impl_intro
lemmas valid_DAG_elims  = valid_alt_BFS_DAG_E valid_alt_BFS_DAG_impl_E
lemmas valid_DAG_dests  = valid_alt_BFS_DAG_props valid_alt_BFS_DAG_impl_props

theorem BFS_valid_DAG:
  "valid_alt_BFS_DAG (parents (BFS initial_state)) (distances (BFS initial_state))
                     (visited_even (BFS initial_state)) (visited_odd (BFS initial_state))"
proof -
  note RC = BFS_final_ret_conds and CE = BFS_final_current_empty
  have I_subs: "invar_subsets (BFS initial_state)"
    by (intro invar_subsets_holds initial_state_props)
  have I_pe: "invar_parents_edges (BFS initial_state)"
    by (intro invar_parents_edges_holds initial_state_props)
  have I_dr: "invar_discovered_reachable (BFS initial_state)"
    by (intro invar_discovered_reachable_holds initial_state_props)
  have I_vc: "invar_visited_closed (BFS initial_state)"
    by (intro invar_visited_closed_holds initial_state_props)
  have I_se: "invar_srcs_even (BFS initial_state)"
    by (intro invar_srcs_even_holds initial_state_props)
  have I_de: "invar_distances_eq (BFS initial_state)"
    by (intro invar_distances_eq_holds initial_state_props)
  have I_dc: "invar_distances_correct (BFS initial_state)"
    by (intro invar_distances_correct_holds initial_state_props)
  have I_pt: "invar_parents_tight (BFS initial_state)"
    by (intro invar_parents_tight_holds initial_state_props invar_parents_tight_initial)
  have I_dd: "invar_dists_defined (BFS initial_state)"
    by (intro invar_dists_defined_holds initial_state_props invar_dists_defined_initial)
  show ?thesis
  proof (intro valid_alt_BFS_DAG_intro, goal_cases)
    case 1 show ?case using I_subs by (auto simp: invar_subsets_def)
  next
    case 2 show ?case using I_subs CE by (auto simp: invar_subsets_def)
  next
    case (3 u v)
    show ?case
      using 3 I_pe CE by (fastforce simp: invar_parents_edges_def)
  next
    case (4 v) show ?case using 4 I_dr
      by (auto simp: invar_discovered_reachable_def)
  next
    case (5 v) show ?case using 5 I_dr
      by (auto simp: invar_discovered_reachable_def)
  next
    case (6 u v p)
    show ?case using 6 BFS_correct_no_odd_walk_ret_1[OF I_vc I_se RC] by blast
  next
    case (7 u v p)
    show ?case using 7 BFS_correct_no_even_walk_ret_1[OF I_vc I_se RC] by blast
  next
    case (8 v) show ?case using 8 invar_distances_correct_Some(1)[OF I_dc I_dd] by blast
  next
    case (9 v) show ?case using 9 invar_distances_correct_Some(2)[OF I_dc I_dd] by blast
  next
    case (10 v)
    show ?case using 10 BFS_correct_dists_ret_1(1)[OF I_de RC, symmetric] by blast
  next
    case (11 v)
    show ?case using 11 BFS_correct_dists_ret_1(2)[OF I_de RC, symmetric] by blast
  next
    case (12 u p v parity)
    have "invar_parents_shortest_alt (BFS initial_state)"
      using invar_parents_tight_shortest_alt[OF I_pt] .
    then show ?case using 12 by (auto simp: invar_parents_shortest_alt_def)
  qed
qed

theorem BFS_valid_DAG_impl:
  "valid_alt_BFS_DAG_impl (parents (BFS initial_state)) (distances (BFS initial_state))
                          (visited_even (BFS initial_state)) (visited_odd (BFS initial_state))"
  unfolding valid_alt_BFS_DAG_impl_def
  using BFS_correct_well_formed[unfolded invar_well_formed_def] BFS_valid_DAG
  by auto

subsection \<open>Corollaries: the classic exports, as projections of the predicate\<close>

lemma BFS_correct_parents_in_G:
  "Graph.digraph_abs (parents (BFS initial_state)) \<subseteq> G"
  by (rule valid_alt_BFS_DAG_props(1)[OF BFS_valid_DAG])

lemma BFS_correct_parents_edges_final:
  "(u, v) \<in> Graph.digraph_abs (parents (BFS initial_state)) \<Longrightarrow>
     ((u, v) \<in> Graph.digraph_abs unmatching \<and>
      u \<in> t_set (visited_even (BFS initial_state)) \<and>
      v \<in> t_set (visited_odd  (BFS initial_state))) \<or>
     ((u, v) \<in> Graph.digraph_abs matching \<and>
      u \<in> t_set (visited_odd  (BFS initial_state)) \<and>
      v \<in> t_set (visited_even (BFS initial_state)))"
  by (rule valid_alt_BFS_DAG_props(3)[OF BFS_valid_DAG])

lemma BFS_correct_odd_reachable:
  "v \<in> t_set (visited_odd (BFS initial_state)) \<Longrightarrow> altd_G Odd v < \<infinity>"
  using valid_alt_BFS_DAG_props(4)[OF BFS_valid_DAG] by (auto simp only: enat_simps)

lemma BFS_correct_even_reachable:
  "v \<in> t_set (visited_even (BFS initial_state)) \<Longrightarrow> altd_G Even v < \<infinity>"
  using valid_alt_BFS_DAG_props(5)[OF BFS_valid_DAG] by (auto simp only: enat_simps)

lemma BFS_correct_P4:
  "\<lbrakk>u \<in> t_set srcs; v \<notin> t_set (visited_odd (BFS initial_state))\<rbrakk> \<Longrightarrow>
   \<not>(\<exists>p. alt_walk Odd G u p v)"
  using valid_alt_BFS_DAG_props(6)[OF BFS_valid_DAG] by blast

lemma BFS_correct_P5:
  "\<lbrakk>u \<in> t_set srcs; v \<notin> t_set (visited_even (BFS initial_state))\<rbrakk> \<Longrightarrow>
   \<not>(\<exists>p. alt_walk Even G u p v)"
  using valid_alt_BFS_DAG_props(7)[OF BFS_valid_DAG] by blast

lemma BFS_correct_distances_Some:
  "v \<in> t_set (visited_odd (BFS initial_state)) \<Longrightarrow>
     lookup_dist (distances (BFS initial_state)) (Vtx Odd v) = Some (altd_G Odd v)"
  "v \<in> t_set (visited_even (BFS initial_state)) \<Longrightarrow>
     lookup_dist (distances (BFS initial_state)) (Vtx Even v) = Some (altd_G Even v)"
proof goal_cases
  case 1 then show ?case by (rule valid_alt_BFS_DAG_props(8)[OF BFS_valid_DAG])
next
  case 2 then show ?case by (rule valid_alt_BFS_DAG_props(9)[OF BFS_valid_DAG])
qed

lemma BFS_correct_distances_odd:
  "v \<in> t_set (visited_odd (BFS initial_state)) \<Longrightarrow>
   the (lookup_dist (distances (BFS initial_state)) (Vtx Odd v)) = altd_G Odd v"
  by (simp add: BFS_correct_distances_Some(1))

lemma BFS_correct_distances_even:
  "v \<in> t_set (visited_even (BFS initial_state)) \<Longrightarrow>
   the (lookup_dist (distances (BFS initial_state)) (Vtx Even v)) = altd_G Even v"
  by (simp add: BFS_correct_distances_Some(2))

lemma BFS_correct_odd_dist:
  "v \<in> t_set (visited_odd (BFS initial_state)) \<Longrightarrow>
   altd_G Odd v = altd_T (BFS initial_state) Odd v"
  by (rule valid_alt_BFS_DAG_props(10)[OF BFS_valid_DAG, symmetric])

lemma BFS_correct_even_dist:
  "\<lbrakk>v \<in> t_set (visited_even (BFS initial_state)); v \<notin> t_set srcs\<rbrakk> \<Longrightarrow>
   altd_G Even v = altd_T (BFS initial_state) Even v"
  by (rule valid_alt_BFS_DAG_props(11)[OF BFS_valid_DAG, symmetric])

lemma BFS_correct_parents_shortest:   \<comment> \<open>P6 (parity = Odd) and P7 (parity = Even)\<close>
  assumes "u \<in> t_set srcs"
          "alt_walk parity (Graph.digraph_abs (parents (BFS initial_state))) u p v"
  shows "enat (length p - 1) = altd_G parity v"
  by (rule valid_alt_BFS_DAG_props(12)[OF BFS_valid_DAG assms])

end text \<open>context\<close>

end text \<open>locale @{const BFS}\<close>
end
