theory Alt_BFS
  imports Directed_Set_Graphs.Pair_Graph_Specs "HOL-Eisbach.Eisbach_Tools" Alt_Dist
          Data_Structures.Set2_Addons Directed_Set_Graphs.More_Lists
begin

record ('graph, 'vset, 'dmap) BFS_state =
    parents:: "'graph" current:: "'vset" visited_even:: "'vset" visited_odd:: "'vset"
    distances:: "'dmap"

definition new_edges where
  "new_edges G frontier vis ≡ 
     {(u,v) | u v. u ∈ (frontier) ∧ 
                   v ∈ (Pair_Graph.neighbourhood G u) - vis}"

definition next_frontier where
  "next_frontier G frontier vis ≡ 
     {v | u v. u ∈ (frontier) ∧ 
               v ∈ (Pair_Graph.neighbourhood G u) - vis}"

locale BFS =
  dist_map: Map where empty = empty_dist and update = update_dist and delete = delete_dist and 
                      lookup = lookup_dist and invar = invar_dist +
  Graph: Pair_Graph_Specs
    where lookup = lookup_neighb +
  set_ops: Set2 vset_empty vset_delete _ t_set vset_inv insert 
  
for lookup_neighb :: "'adjmap ⇒ 'ver ⇒ 'vset option" and
    lookup_dist:: "'dmap ⇒ 'ver labelled_vtx ⇒ enat option" and
    empty_dist and update_dist and delete_dist and invar_dist +

fixes
  srcs::"'vset" and
  matching::"'adjmap" and
  matched_vtxs::"'vset" and
  unmatching::"'adjmap" and
  expand_tree::"'adjmap ⇒ 'adjmap ⇒ 'vset ⇒ 'vset ⇒ 'adjmap" and
  next_frontier_impl::"'adjmap ⇒ 'vset ⇒ 'vset ⇒ 'vset" and
  upd_dists::"parity ⇒ 'adjmap ⇒ 'dmap ⇒ 'vset ⇒ 'vset ⇒ 'dmap" and
  init_dists::"'dmap"

assumes
   expand_tree[simp,intro!]:
     "⟦Graph.graph_inv BFS_tree; vset_inv frontier; vset_inv vis; Graph.graph_inv G⟧ ⟹
       Graph.graph_inv (expand_tree G BFS_tree frontier vis)"
     "⟦Graph.graph_inv BFS_tree; vset_inv frontier; vset_inv vis; Graph.graph_inv G⟧ ⟹
        Graph.digraph_abs (expand_tree G BFS_tree frontier vis) =
         (Graph.digraph_abs BFS_tree) ∪
         new_edges (Graph.digraph_abs G) (t_set frontier) (t_set vis)" and
   next_frontier[simp]:
    "⟦vset_inv frontier; vset_inv vis; Graph.graph_inv G⟧ ⟹  vset_inv (next_frontier_impl G frontier vis)"
    "⟦vset_inv frontier; vset_inv vis; Graph.graph_inv G⟧ ⟹
       t_set (next_frontier_impl G frontier vis) =
         next_frontier (Graph.digraph_abs G) (t_set frontier) (t_set vis)" and
   init_dists[simp,intro!]:
     "u ∈ t_set srcs ⟹ the (lookup_dist init_dists (Vtx Even u)) = 0"
     "invar_dist init_dists" and
   upd_dists[simp,intro!]:
     "⟦invar_dist dist_map; vset_inv frontier; vset_inv vis; Graph.graph_inv G⟧ ⟹
       invar_dist (upd_dists parity G dist_map frontier vis)"
     "⟦invar_dist dist_map; vset_inv frontier; vset_inv vis; Graph.graph_inv G;
       u ∈ t_set frontier;
       v ∈ Pair_Graph.neighbourhood (Graph.digraph_abs G) u - t_set vis⟧ ⟹
        the (lookup_dist (upd_dists parity G dist_map frontier vis) (Vtx parity v)) =
          the (lookup_dist dist_map (Vtx (other_parity parity) u)) + 1"
     "⟦invar_dist dist_map; vset_inv frontier; vset_inv vis; Graph.graph_inv G;
       w ∉ Vtx parity ` next_frontier (Graph.digraph_abs G) (t_set frontier) (t_set vis)⟧ ⟹
        lookup_dist (upd_dists parity G dist_map frontier vis) w = lookup_dist dist_map w" and
   matching[simp]:
     "t_set matched_vtxs = dVs (Graph.digraph_abs matching)"
begin

definition "BFS_axiom ⟷
  Graph.graph_inv matching ∧ Graph.finite_graph matching ∧
  Graph.graph_inv unmatching ∧ Graph.finite_graph unmatching ∧ 
  Graph.finite_vsets matching ∧ Graph.finite_vsets unmatching ∧
  t_set srcs ⊆ dVs (Graph.digraph_abs unmatching) ∧
  (∀u. finite (Pair_Graph.neighbourhood (Graph.digraph_abs matching) u)) ∧
  (∀u. finite (Pair_Graph.neighbourhood (Graph.digraph_abs unmatching) u)) ∧
  t_set srcs ≠ {} ∧ vset_inv srcs ∧ vset_inv matched_vtxs"

abbreviation "matching_neighbourhood' ≡ Graph.neighbourhood matching" 
abbreviation "unmatching_neighbourhood' ≡ Graph.neighbourhood unmatching" 
notation "matching_neighbourhood'" ("𝒩⇩G _" 100)
notation "unmatching_neighbourhood'" ("𝒩⇩G' _" 100)

function (domintros) BFS::"('adjmap, 'vset, 'dmap) BFS_state ⇒ ('adjmap, 'vset, 'dmap) BFS_state" where
  "BFS BFS_state =
     (
        if current BFS_state ≠ ∅⇩N then
          let
            visited_even' = visited_even BFS_state ∪⇩G current BFS_state;
            parents' = expand_tree unmatching (parents BFS_state) (current BFS_state) (visited_odd BFS_state);
            current' = next_frontier_impl unmatching (current BFS_state) (visited_odd BFS_state);
            distances' = upd_dists Odd unmatching (distances BFS_state) (current BFS_state) (visited_odd BFS_state);
            visited_odd' = visited_odd BFS_state ∪⇩G current';
            parents'' = expand_tree matching parents' current' visited_even';
            current'' = next_frontier_impl matching current' visited_even';
            distances'' = upd_dists Even matching distances' current' visited_even'
          in
            BFS (BFS_state ⦇parents:= parents'', visited_even := visited_even',
                            visited_odd := visited_odd', current := current'',
                            distances:= distances''⦈)
         else
          BFS_state)"
  by pat_completeness auto

definition "BFS_call_1_conds bfs_state = ( (current bfs_state) ≠ ∅⇩N)"

definition "BFS_upd1 BFS_state =
(       let
          visited_even' = visited_even BFS_state ∪⇩G current BFS_state;
          parents' = expand_tree unmatching (parents BFS_state) (current BFS_state) (visited_odd BFS_state);
          current' = next_frontier_impl unmatching (current BFS_state) (visited_odd BFS_state);
          distances' = upd_dists Odd unmatching (distances BFS_state) (current BFS_state) (visited_odd BFS_state);
          visited_odd' = visited_odd BFS_state ∪⇩G current';
          parents'' = expand_tree matching parents' current' visited_even';
          current'' = next_frontier_impl matching current' visited_even';
          distances'' = upd_dists Even matching distances' current' visited_even'
        in
          BFS_state ⦇parents:= parents'', visited_even := visited_even',
                     visited_odd := visited_odd', current := current'',
                     distances:= distances''⦈
)"
definition "BFS_ret_1_conds bfs_state = ((current bfs_state) = ∅⇩N)"

abbreviation "BFS_ret1 bfs_state ≡ bfs_state"
 
definition "invar_well_formed bfs_state = (
              vset_inv (visited_even bfs_state) ∧ vset_inv (visited_odd bfs_state) ∧ vset_inv (current bfs_state) ∧
              Graph.graph_inv (parents bfs_state) ∧ 
              finite (t_set (current bfs_state)) ∧ 
              finite (t_set (visited_even bfs_state)) ∧ finite (t_set (visited_odd bfs_state)) ∧
              invar_dist (distances bfs_state))"

definition "G ≡ (Graph.digraph_abs unmatching) ∪ (Graph.digraph_abs matching) "

definition "invar_subsets bfs_state = (
  Graph.digraph_abs (parents bfs_state) ⊆ G ∧
  t_set (visited_even bfs_state) ⊆ dVs G ∧
  t_set (visited_odd bfs_state) ⊆ dVs G ∧
  t_set (current bfs_state) ⊆ dVs G ∧ 
  dVs (Graph.digraph_abs (parents bfs_state)) ⊆ t_set (visited_even bfs_state) ∪ t_set (visited_odd bfs_state) ∪ t_set (current bfs_state) ∧
  t_set srcs ⊆ t_set (visited_even bfs_state) ∪ t_set (visited_odd bfs_state) ∪ t_set (current bfs_state))"


(*
definition "invar_3_1 bfs_state = 
  (∀v∈t_set (current bfs_state). ∀u. u ∈ t_set (current bfs_state) ⟷ 
      distance_set G (t_set srcs) v = distance_set G (t_set srcs) u)"

definition "invar_3_2 bfs_state = 
  (∀v∈t_set (current bfs_state). ∀u ∈ t_set (visited bfs_state) ∪ t_set (current bfs_state).
     distance_set G (t_set srcs) u ≤
       distance_set G (t_set srcs) v)"

definition "invar_3_3 bfs_state = 
  (∀v∈t_set (visited bfs_state).
     neighbourhood G v ⊆ t_set (visited bfs_state) ∪ t_set (current bfs_state))"

definition "invar_dist_bounded bfs_state = 
  (∀v∈ t_set (visited bfs_state) ∪ t_set (current bfs_state).
     ∀u. distance_set (Graph.digraph_abs G) (t_set srcs) u ≤
           distance_set (Graph.digraph_abs G) (t_set srcs) v
             ⟶ u ∈ t_set (visited bfs_state) ∪ t_set (current bfs_state))"

definition "invar_goes_through_current bfs_state =
         (∀u∈t_set (visited bfs_state) ∪ t_set (current bfs_state). 
            ∀v. v ∉ t_set (visited bfs_state) ∪ t_set (current bfs_state) ⟶
              (∀p. Vwalk.vwalk_bet (Graph.digraph_abs G) u p v ⟶ 
                     set p ∩ t_set (current bfs_state) ≠ {}))"
*)

― ‹A0: Abstract-predicate, P1/P2-swapped alt_distance_set (P1 = unmatched, P2 = matched).›
definition "unmatched_edge = (λe. e ∈ Graph.digraph_abs unmatching)"
definition "matched_edge   = (λe. e ∈ Graph.digraph_abs matching)"

definition "alt_distance_set H parity v ≡
  alt_dist.alt_distance_set unmatched_edge matched_edge parity H (t_set srcs) v"

abbreviation "alt_walk parity H u p v ≡
  alt_dist.alt_vwalk_bet unmatched_edge matched_edge parity H u p v"

abbreviation "altd_G parity v ≡ alt_distance_set G parity v"
abbreviation "altd_T bfs_state parity v ≡
  alt_distance_set (Graph.digraph_abs (parents bfs_state)) parity v"

definition "discovered bfs_state parity =
  (case parity of Even ⇒ t_set (visited_even bfs_state) ∪ t_set (current bfs_state)
                | Odd  ⇒ t_set (visited_odd bfs_state))"

― ‹A1: Parity-conditional invar_distances_eq (the formal carrier of P2+P3).›
definition "invar_distances_eq bfs_state =
  ((∀v ∈ t_set (visited_odd bfs_state).
      altd_G Odd v = altd_T bfs_state Odd v) ∧
   (∀v ∈ t_set (visited_even bfs_state) ∪ t_set (current bfs_state) - t_set srcs.
      altd_G Even v = altd_T bfs_state Even v))"

― ‹A2: Initial state (field order: parents, current, visited_even, visited_odd, distances).›
definition "initial_state =
  ⦇parents = empty, current = srcs, visited_even = ∅⇩N,
   visited_odd = ∅⇩N, distances = init_dists⦈"

(*
definition "invar_parents_shortest_paths bfs_state =
  (∀u∈t_set srcs.
      ∀ p v. Vwalk.vwalk_bet (Graph.digraph_abs (parents bfs_state)) u p v ⟶
         length p - 1 = distance_set (Graph.digraph_abs G) (t_set srcs) v)"

definition "invar_distances_correct bfs_state =
(∀v ∈ (t_set (visited bfs_state) ∪ t_set (current bfs_state)).
       distance_set (Graph.digraph_abs G) (t_set srcs) v =
         the (lookup_dist (distances bfs_state) v))"

definition "call_1_measure_1 BFS_state=
  card (dVs (Graph.digraph_abs G) - ((t_set (visited BFS_state)) ∪ t_set (current BFS_state)))"

definition "call_1_measure_2 BFS_state =
  card (t_set (current BFS_state))"

definition
  "BFS_term_rel' = call_1_measure_1 <*mlex*> call_1_measure_2 <*mlex*> {}"

definition "initial_state = ⦇parents =  empty, current = srcs, visited = ∅⇩N, distances = init_dists⦈"

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
     "t_set srcs ⊆ dVs (Graph.digraph_abs unmatching)" and
   finite_vset:
     "finite (Pair_Graph.neighbourhood (Graph.digraph_abs matching) u)"
     "finite (Pair_Graph.neighbourhood (Graph.digraph_abs unmatching) u)" and
  srcs_invar[simp]:
     "t_set srcs ≠ {}" 
     "vset_inv srcs"
     "vset_inv matched_vtxs"
  using ‹BFS_axiom›
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
  "BFS_call_1_conds bfs_state ⟹ 
   ⟦(current bfs_state) ≠ ∅⇩N ⟹ P⟧
   ⟹ P"
  by(auto simp: BFS_call_1_conds_def split: list.splits option.splits if_splits)


lemma BFS_ret_1_conds[call_cond_elims]:
  "BFS_ret_1_conds bfs_state ⟹ 
   ⟦(current bfs_state) = ∅⇩N ⟹ P⟧
   ⟹ P"
  by(auto simp: BFS_ret_1_conds_def split: list.splits option.splits if_splits)

lemma BFS_ret_1_condsI[call_cond_intros]:
  "⟦(current bfs_state) = ∅⇩N⟧ ⟹ BFS_ret_1_conds bfs_state"
  by(auto simp: BFS_ret_1_conds_def split: list.splits option.splits if_splits)

lemma BFS_cases:
  assumes "BFS_call_1_conds bfs_state ⟹ P"
      "BFS_ret_1_conds bfs_state ⟹ P"
  shows "P"
proof-
  have "BFS_call_1_conds bfs_state ∨
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
  shows"BFS_call_1_conds BFS_state ⟹ BFS BFS_state = BFS (BFS_upd1 BFS_state)"
      "BFS_ret_1_conds BFS_state ⟹ BFS BFS_state = BFS_ret1 BFS_state"
  by (auto simp add: BFS.psimps[OF assms]
                     BFS_call_1_conds_def BFS_upd1_def 
                     BFS_ret_1_conds_def Let_def
            split: list.splits option.splits if_splits)

lemma BFS_induct: 
  assumes "BFS_dom bfs_state"
  assumes "⋀bfs_state. ⟦BFS_dom bfs_state;
                        (BFS_call_1_conds bfs_state ⟹ P (BFS_upd1 bfs_state))⟧
              ⟹ P bfs_state"
  shows "P bfs_state"
  apply(rule BFS.pinduct)
  subgoal using assms(1) .
  apply(rule assms(2))
  by (auto simp add: BFS_call_1_conds_def BFS_upd1_def Let_def
           split: list.splits option.splits if_splits)

lemma BFS_domintros: 
  assumes "BFS_call_1_conds BFS_state ⟹ BFS_dom (BFS_upd1 BFS_state)"
  shows "BFS_dom BFS_state"
proof(rule BFS.domintros, goal_cases)
  case (1)
  then show ?case
    using assms(1)[simplified BFS_call_1_conds_def BFS_upd1_def]
    by (force simp: Let_def split: list.splits option.splits if_splits)
qed

lemma invar_well_formed_props[invar_props_elims]: 
  "invar_well_formed bfs_state ⟹ 
  (⟦vset_inv (visited_even bfs_state) ; vset_inv (visited_odd bfs_state) ; vset_inv (current bfs_state) ;
    Graph.graph_inv (parents bfs_state); 
    finite (t_set (current bfs_state)); finite (t_set (visited_even bfs_state));
    finite (t_set (visited_odd bfs_state)); 
    invar_dist (distances bfs_state)⟧ ⟹ P)
     ⟹ P"
  by (auto simp: invar_well_formed_def)

lemma invar_well_formed_intro[invar_props_intros]:
  "⟦vset_inv (visited_even bfs_state); vset_inv (visited_odd bfs_state); vset_inv (current bfs_state);
    Graph.graph_inv (parents bfs_state);
    finite (t_set (current bfs_state)); finite (t_set (visited_even bfs_state));
    finite (t_set (visited_odd bfs_state)); invar_dist (distances bfs_state)⟧ 
    ⟹ invar_well_formed bfs_state"
  by (auto simp: invar_well_formed_def)

lemma finite_simp:
   "{(u,v). u ∈ front ∧ v ∈ (Pair_Graph.neighbourhood G u) ∧ v ∉ vis} = 
       {(u,v). u ∈ front} ∩ {(u,v). v ∈ (Pair_Graph.neighbourhood G u)} - {(u,v) . v ∈ vis}"
   "finite {(u, v)| v . v ∈ (s u)} = finite (s u)"
  using finite_image_iff[where f = snd and A = "{(u, v) |v. v ∈ s u}"]
  by (auto simp: inj_on_def image_def)
  
lemma invar_well_formed_holds_upd1[invar_holds_intros]:
  "⟦BFS_call_1_conds bfs_state; invar_well_formed bfs_state⟧ ⟹ invar_well_formed (BFS_upd1 bfs_state)"
  using finite_vset
  by(auto elim!: invar_well_formed_props call_cond_elims
          simp: Let_def BFS_upd1_def BFS_call_1_conds_def next_frontier_def 
          intro!: invar_props_intros)


lemma invar_well_formed_holds_ret_1[invar_holds_intros]:
  "⟦BFS_ret_1_conds bfs_state; invar_well_formed bfs_state⟧ ⟹ invar_well_formed (BFS_ret1 bfs_state)"
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
  "invar_subsets bfs_state ⟹
  (⟦Graph.digraph_abs (parents bfs_state) ⊆ G;
    t_set (visited_even bfs_state) ⊆ dVs G;
    t_set (visited_odd bfs_state) ⊆ dVs G;
    t_set (current bfs_state) ⊆ dVs G;
    dVs (Graph.digraph_abs (parents bfs_state)) ⊆
      t_set (visited_even bfs_state) ∪ t_set (visited_odd bfs_state) ∪ t_set (current bfs_state);
    t_set srcs ⊆ t_set (visited_even bfs_state) ∪ t_set (visited_odd bfs_state) ∪ t_set (current bfs_state)⟧ ⟹ P)
     ⟹ P"
  by (auto simp: invar_subsets_def)

lemma invar_subsets_intro[invar_props_intros]:
  "⟦Graph.digraph_abs (parents bfs_state) ⊆ G;
    t_set (visited_even bfs_state) ⊆ dVs G;
    t_set (visited_odd bfs_state) ⊆ dVs G;
    t_set (current bfs_state) ⊆ dVs G;
    dVs (Graph.digraph_abs (parents bfs_state)) ⊆
      t_set (visited_even bfs_state) ∪ t_set (visited_odd bfs_state) ∪ t_set (current bfs_state);
    t_set srcs ⊆ t_set (visited_even bfs_state) ∪ t_set (visited_odd bfs_state) ∪ t_set (current bfs_state)⟧
     ⟹ invar_subsets bfs_state"
  by (auto simp: invar_subsets_def)

lemma dVs_new_edges_subset:
  "dVs (new_edges H frontier vis) ⊆ frontier ∪ next_frontier H frontier vis"
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
    "Graph.digraph_abs (parents bfs_state) ⊆ G"
    "t_set (visited_even bfs_state) ⊆ dVs G"
    "t_set (visited_odd bfs_state) ⊆ dVs G"
    "t_set (current bfs_state) ⊆ dVs G"
    "dVs (Graph.digraph_abs (parents bfs_state)) ⊆
       t_set (visited_even bfs_state) ∪ t_set (visited_odd bfs_state) ∪ t_set (current bfs_state)"
    "t_set srcs ⊆ t_set (visited_even bfs_state) ∪ t_set (visited_odd bfs_state) ∪ t_set (current bfs_state)"
    using assms(3)
    by (auto simp: invar_subsets_def)

  define VE' where "VE' = visited_even bfs_state ∪⇩G current bfs_state"
  define P' where "P' = expand_tree unmatching (parents bfs_state) (current bfs_state) (visited_odd bfs_state)"
  define C' where "C' = next_frontier_impl unmatching (current bfs_state) (visited_odd bfs_state)"
  define VO' where "VO' = visited_odd bfs_state ∪⇩G C'"
  define P'' where "P'' = expand_tree matching P' C' VE'"
  define C'' where "C'' = next_frontier_impl matching C' VE'"

  have upd1: "BFS_upd1 bfs_state =
    bfs_state ⦇parents := P'', visited_even := VE', visited_odd := VO', current := C'',
               distances := upd_dists Even matching
                              (upd_dists Odd unmatching (distances bfs_state) (current bfs_state)
                                 (visited_odd bfs_state)) C' VE'⦈"
    by (simp add: BFS_upd1_def Let_def VE'_def P'_def C'_def VO'_def P''_def C''_def)

  have inv_VE'[simp]: "vset_inv VE'"
    by (auto simp: VE'_def)
  have inv_P'[simp]: "Graph.graph_inv P'"
    by (auto simp: P'_def)
  have inv_C'[simp]: "vset_inv C'"
    by (auto simp: C'_def)
  have inv_VO'[simp]: "vset_inv VO'"
    by (auto simp: VO'_def)

  have abs_VE': "t_set VE' = t_set (visited_even bfs_state) ∪ t_set (current bfs_state)"
    by (auto simp: VE'_def)
  have abs_P': "Graph.digraph_abs P' =
                  Graph.digraph_abs (parents bfs_state) ∪
                  new_edges (Graph.digraph_abs unmatching) (t_set (current bfs_state))
                    (t_set (visited_odd bfs_state))"
    by (auto simp: P'_def)
  have abs_C': "t_set C' = next_frontier (Graph.digraph_abs unmatching)
                             (t_set (current bfs_state)) (t_set (visited_odd bfs_state))"
    by (auto simp: C'_def)
  have abs_VO': "t_set VO' = t_set (visited_odd bfs_state) ∪ t_set C'"
    by (auto simp: VO'_def)
  have abs_P'': "Graph.digraph_abs P'' =
                   Graph.digraph_abs P' ∪
                   new_edges (Graph.digraph_abs matching) (t_set C') (t_set VE')"
    by (auto simp: P''_def)
  have abs_C'': "t_set C'' = next_frontier (Graph.digraph_abs matching) (t_set C') (t_set VE')"
    by (auto simp: C''_def)

  have parents''_sub_G: "Graph.digraph_abs P'' ⊆ G"
    using sub(1)
    by (auto simp: abs_P'' abs_P' G_def new_edges_def)
  have VE'_sub_dVs: "t_set VE' ⊆ dVs G"
    using sub(2,4)
    by (auto simp: abs_VE')
  have C'_sub_dVs: "t_set C' ⊆ dVs G"
    by (auto simp: abs_C' next_frontier_def G_def)
  have VO'_sub_dVs: "t_set VO' ⊆ dVs G"
    using sub(3) C'_sub_dVs
    by (auto simp: abs_VO')
  have C''_sub_dVs: "t_set C'' ⊆ dVs G"
    by (auto simp: abs_C'' next_frontier_def G_def)

  have dVs_P': "dVs (Graph.digraph_abs P') ⊆ t_set VE' ∪ t_set VO'"
    using sub(5)
          dVs_new_edges_subset[of "Graph.digraph_abs unmatching" "t_set (current bfs_state)"
                                  "t_set (visited_odd bfs_state)"]
    by (auto simp: abs_P' abs_VE' abs_VO' abs_C')
  have dVs_P'': "dVs (Graph.digraph_abs P'') ⊆ t_set VE' ∪ t_set VO' ∪ t_set C''"
    using dVs_P'
          dVs_new_edges_subset[of "Graph.digraph_abs matching" "t_set C'" "t_set VE'"]
    by (auto simp: abs_P'' abs_VO' abs_C'')
  have srcs_sub: "t_set srcs ⊆ t_set VE' ∪ t_set VO'"
    using sub(6)
    by (auto simp: abs_VE' abs_VO')

  show ?thesis
    using parents''_sub_G VE'_sub_dVs VO'_sub_dVs C''_sub_dVs dVs_P'' srcs_sub
    by (auto simp: upd1 intro!: invar_subsets_intro)
qed

lemma invar_subsets_holds_ret_1[invar_holds_intros]:
  "⟦BFS_ret_1_conds bfs_state; invar_subsets bfs_state⟧ ⟹ invar_subsets (BFS_ret1 bfs_state)"
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

― ‹I-1a: invar_srcs_even — srcs stay on the even side.›

definition "invar_srcs_even bfs_state =
  (t_set srcs ⊆ t_set (visited_even bfs_state) ∪ t_set (current bfs_state))"

lemma invar_srcs_even_props[invar_props_elims]:
  "invar_srcs_even bfs_state ⟹
   (t_set srcs ⊆ t_set (visited_even bfs_state) ∪ t_set (current bfs_state) ⟹ P) ⟹ P"
  by (auto simp: invar_srcs_even_def)

lemma invar_srcs_even_intro[invar_props_intros]:
  "t_set srcs ⊆ t_set (visited_even bfs_state) ∪ t_set (current bfs_state)
     ⟹ invar_srcs_even bfs_state"
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
  "⟦BFS_ret_1_conds bfs_state; invar_srcs_even bfs_state⟧ ⟹ invar_srcs_even (BFS_ret1 bfs_state)"
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


― ‹I-1b: invar_current_unvisited — the even frontier is fresh.
   NOTE: current ∩ visited_odd = {} is FALSE (blossoms), so only the even disjointness holds.›

definition "invar_current_unvisited bfs_state =
  (t_set (current bfs_state) ∩ t_set (visited_even bfs_state) = {})"

lemma invar_current_unvisited_props[invar_props_elims]:
  "invar_current_unvisited bfs_state ⟹
   (t_set (current bfs_state) ∩ t_set (visited_even bfs_state) = {} ⟹ P) ⟹ P"
  by (auto simp: invar_current_unvisited_def)

lemma invar_current_unvisited_intro[invar_props_intros]:
  "t_set (current bfs_state) ∩ t_set (visited_even bfs_state) = {}
     ⟹ invar_current_unvisited bfs_state"
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
  "⟦BFS_ret_1_conds bfs_state; invar_current_unvisited bfs_state⟧ ⟹ invar_current_unvisited (BFS_ret1 bfs_state)"
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


― ‹I-1c: invar_parents_edges — edge typing; the formal carrier of P1.
   Every parents edge is either unmatched (even source, odd target) or
   matched (odd source, even-or-current target).
   NOTE: plain vwalk_bet paths in parents need NOT alternate — blossom 2-cycles exist
   (D2 in the design decisions). No stronger statement than this edge-local form is true.›

definition "invar_parents_edges bfs_state =
  (∀u v. (u, v) ∈ Graph.digraph_abs (parents bfs_state) ⟶
     ((u, v) ∈ Graph.digraph_abs unmatching ∧
      u ∈ t_set (visited_even bfs_state) ∧ v ∈ t_set (visited_odd bfs_state)) ∨
     ((u, v) ∈ Graph.digraph_abs matching ∧
      u ∈ t_set (visited_odd bfs_state) ∧
      v ∈ t_set (visited_even bfs_state) ∪ t_set (current bfs_state)))"

lemma invar_parents_edges_props[invar_props_elims]:
  "invar_parents_edges bfs_state ⟹
   (⟦⋀u v. (u, v) ∈ Graph.digraph_abs (parents bfs_state) ⟹
     ((u, v) ∈ Graph.digraph_abs unmatching ∧
      u ∈ t_set (visited_even bfs_state) ∧ v ∈ t_set (visited_odd bfs_state)) ∨
     ((u, v) ∈ Graph.digraph_abs matching ∧
      u ∈ t_set (visited_odd bfs_state) ∧
      v ∈ t_set (visited_even bfs_state) ∪ t_set (current bfs_state))⟧ ⟹ P) ⟹ P"
  by (auto simp: invar_parents_edges_def)

lemma invar_parents_edges_intro[invar_props_intros]:
  "⟦⋀u v. (u, v) ∈ Graph.digraph_abs (parents bfs_state) ⟹
     ((u, v) ∈ Graph.digraph_abs unmatching ∧
      u ∈ t_set (visited_even bfs_state) ∧ v ∈ t_set (visited_odd bfs_state)) ∨
     ((u, v) ∈ Graph.digraph_abs matching ∧
      u ∈ t_set (visited_odd bfs_state) ∧
      v ∈ t_set (visited_even bfs_state) ∪ t_set (current bfs_state))⟧
   ⟹ invar_parents_edges bfs_state"
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

  define VE' where "VE' = visited_even bfs_state ∪⇩G current bfs_state"
  define P' where "P' = expand_tree unmatching (parents bfs_state) (current bfs_state) (visited_odd bfs_state)"
  define C' where "C' = next_frontier_impl unmatching (current bfs_state) (visited_odd bfs_state)"
  define VO' where "VO' = visited_odd bfs_state ∪⇩G C'"
  define P'' where "P'' = expand_tree matching P' C' VE'"
  define C'' where "C'' = next_frontier_impl matching C' VE'"

  have upd1: "BFS_upd1 bfs_state =
    bfs_state ⦇parents := P'', visited_even := VE', visited_odd := VO', current := C'',
               distances := upd_dists Even matching
                              (upd_dists Odd unmatching (distances bfs_state) (current bfs_state)
                                 (visited_odd bfs_state)) C' VE'⦈"
    by (simp add: BFS_upd1_def Let_def VE'_def P'_def C'_def VO'_def P''_def C''_def)

  have inv_VE'[simp]: "vset_inv VE'" by (auto simp: VE'_def)
  have inv_P'[simp]: "Graph.graph_inv P'" by (auto simp: P'_def)
  have inv_C'[simp]: "vset_inv C'" by (auto simp: C'_def)
  have inv_VO'[simp]: "vset_inv VO'" by (auto simp: VO'_def)

  have abs_VE': "t_set VE' = t_set (visited_even bfs_state) ∪ t_set (current bfs_state)"
    by (auto simp: VE'_def)
  have abs_C': "t_set C' = next_frontier (Graph.digraph_abs unmatching)
                             (t_set (current bfs_state)) (t_set (visited_odd bfs_state))"
    by (auto simp: C'_def)
  have abs_VO': "t_set VO' = t_set (visited_odd bfs_state) ∪ t_set C'"
    by (auto simp: VO'_def)
  have abs_C'': "t_set C'' = next_frontier (Graph.digraph_abs matching) (t_set C') (t_set VE')"
    by (auto simp: C''_def)
  have abs_P'': "Graph.digraph_abs P'' =
                   Graph.digraph_abs (parents bfs_state)
                   ∪ new_edges (Graph.digraph_abs unmatching) (t_set (current bfs_state))
                       (t_set (visited_odd bfs_state))
                   ∪ new_edges (Graph.digraph_abs matching) (t_set C') (t_set VE')"
    by (auto simp: P''_def P'_def)

  have new1: "⋀u v. (u, v) ∈ new_edges (Graph.digraph_abs unmatching)
                       (t_set (current bfs_state)) (t_set (visited_odd bfs_state)) ⟹
                (u, v) ∈ Graph.digraph_abs unmatching ∧
                u ∈ t_set (current bfs_state) ∧ v ∈ t_set C'"
    by (auto simp: new_edges_def next_frontier_def abs_C')
  have new2: "⋀u v. (u, v) ∈ new_edges (Graph.digraph_abs matching)
                       (t_set C') (t_set VE') ⟹
                (u, v) ∈ Graph.digraph_abs matching ∧
                u ∈ t_set C' ∧ v ∈ t_set C''"
    by (auto simp: new_edges_def next_frontier_def abs_C'')

  show ?thesis
    using assms(3) new1 new2
    by (intro invar_parents_edges_intro)
       (fastforce simp: upd1 abs_P'' abs_VE' abs_VO' invar_parents_edges_def)
qed

lemma invar_parents_edges_holds_ret_1[invar_holds_intros]:
  "⟦BFS_ret_1_conds bfs_state; invar_parents_edges bfs_state⟧ ⟹ invar_parents_edges (BFS_ret1 bfs_state)"
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


― ‹I-1d: P1 as a theorem (corollary of invar_subsets + invar_parents_edges).
   NOTE: plain vwalk_bet paths in parents need NOT alternate — blossom 2-cycles
   mean non-alternating plain paths exist (D2). The only true P1-statement is for
   *alternating* walks, proved here. No stronger statement is provable.›

lemma parents_alt_walk_in_G:
  assumes "invar_subsets bfs_state"
          "alt_walk parity (Graph.digraph_abs (parents bfs_state)) u p v"
  shows "alt_walk parity G u p v"
  using assms
  by (auto simp: invar_subsets_def intro: alt_dist.alt_vwalk_bet_subset)


― ‹I-1e: invar_visited_closed — half-step closure (analogue of BFS_2 invar_3_3).
   Unmatched clause: every even-visited vertex has its unmatched neighbourhood in visited_odd.
   Matched clause: every odd-visited vertex has its matched neighbourhood in visited_even ∪ current.
   NOTE: the matched clause's RHS includes current because the even frontier produced in
   the same iteration is not yet in visited_even at loop boundaries.›

definition "invar_visited_closed bfs_state =
  ((∀v ∈ t_set (visited_even bfs_state).
      Pair_Graph.neighbourhood (Graph.digraph_abs unmatching) v ⊆ t_set (visited_odd bfs_state)) ∧
   (∀v ∈ t_set (visited_odd bfs_state).
      Pair_Graph.neighbourhood (Graph.digraph_abs matching) v ⊆
        t_set (visited_even bfs_state) ∪ t_set (current bfs_state)))"

lemma invar_visited_closed_props[invar_props_elims]:
  "invar_visited_closed bfs_state ⟹
   (⟦⋀v. v ∈ t_set (visited_even bfs_state) ⟹
        Pair_Graph.neighbourhood (Graph.digraph_abs unmatching) v ⊆ t_set (visited_odd bfs_state);
     ⋀v. v ∈ t_set (visited_odd bfs_state) ⟹
        Pair_Graph.neighbourhood (Graph.digraph_abs matching) v ⊆
          t_set (visited_even bfs_state) ∪ t_set (current bfs_state)⟧ ⟹ P) ⟹ P"
  by (auto simp: invar_visited_closed_def)

lemma invar_visited_closed_intro[invar_props_intros]:
  "⟦⋀v. v ∈ t_set (visited_even bfs_state) ⟹
        Pair_Graph.neighbourhood (Graph.digraph_abs unmatching) v ⊆ t_set (visited_odd bfs_state);
    ⋀v. v ∈ t_set (visited_odd bfs_state) ⟹
        Pair_Graph.neighbourhood (Graph.digraph_abs matching) v ⊆
          t_set (visited_even bfs_state) ∪ t_set (current bfs_state)⟧
   ⟹ invar_visited_closed bfs_state"
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

  define VE' where "VE' = visited_even bfs_state ∪⇩G current bfs_state"
  define P' where "P' = expand_tree unmatching (parents bfs_state) (current bfs_state) (visited_odd bfs_state)"
  define C' where "C' = next_frontier_impl unmatching (current bfs_state) (visited_odd bfs_state)"
  define VO' where "VO' = visited_odd bfs_state ∪⇩G C'"
  define P'' where "P'' = expand_tree matching P' C' VE'"
  define C'' where "C'' = next_frontier_impl matching C' VE'"

  have upd1: "BFS_upd1 bfs_state =
    bfs_state ⦇parents := P'', visited_even := VE', visited_odd := VO', current := C'',
               distances := upd_dists Even matching
                              (upd_dists Odd unmatching (distances bfs_state) (current bfs_state)
                                 (visited_odd bfs_state)) C' VE'⦈"
    by (simp add: BFS_upd1_def Let_def VE'_def P'_def C'_def VO'_def P''_def C''_def)

  have inv_VE'[simp]: "vset_inv VE'" by (auto simp: VE'_def)
  have inv_C'[simp]: "vset_inv C'" by (auto simp: C'_def)
  have inv_VO'[simp]: "vset_inv VO'" by (auto simp: VO'_def)

  have abs_VE': "t_set VE' = t_set (visited_even bfs_state) ∪ t_set (current bfs_state)"
    by (auto simp: VE'_def)
  have abs_C': "t_set C' = next_frontier (Graph.digraph_abs unmatching)
                             (t_set (current bfs_state)) (t_set (visited_odd bfs_state))"
    by (auto simp: C'_def)
  have abs_VO': "t_set VO' = t_set (visited_odd bfs_state) ∪ t_set C'"
    by (auto simp: VO'_def)
  have abs_C'': "t_set C'' = next_frontier (Graph.digraph_abs matching) (t_set C') (t_set VE')"
    by (auto simp: C''_def)

  have even_side: "Pair_Graph.neighbourhood (Graph.digraph_abs unmatching) v ⊆ t_set VO'"
    if "v ∈ t_set VE'" for v
  proof(cases "v ∈ t_set (visited_even bfs_state)")
    case True
    then show ?thesis
      using assms(3)
      by (auto simp: invar_visited_closed_def abs_VO')
  next
    case False
    hence "v ∈ t_set (current bfs_state)"
      using that by (auto simp: abs_VE')
    then show ?thesis
      by (auto simp: abs_VO' abs_C' next_frontier_def)
  qed

  have odd_side: "Pair_Graph.neighbourhood (Graph.digraph_abs matching) v ⊆ t_set VE' ∪ t_set C''"
    if "v ∈ t_set VO'" for v
  proof(cases "v ∈ t_set (visited_odd bfs_state)")
    case True
    then show ?thesis
      using assms(3)
      by (auto simp: invar_visited_closed_def abs_VE')
  next
    case False
    hence "v ∈ t_set C'"
      using that by (auto simp: abs_VO')
    then show ?thesis
      by (auto simp: abs_C'' next_frontier_def)
  qed

  show ?thesis
    using even_side odd_side
    by (auto simp: upd1 invar_visited_closed_def abs_VE' abs_VO')
qed

lemma invar_visited_closed_holds_ret_1[invar_holds_intros]:
  "⟦BFS_ret_1_conds bfs_state; invar_visited_closed bfs_state⟧ ⟹ invar_visited_closed (BFS_ret1 bfs_state)"
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




― ‹Batch 3 DEFINITIONS + props/intro (holds proofs come in a later session; ORDERING NOTE).›

― ‹analogue of invar_3_2; anchor: everything discovered is no deeper than current›
definition "invar_level_bounded bfs_state =
  (∀v ∈ t_set (current bfs_state). ∀parity. ∀u ∈ discovered bfs_state parity.
      altd_G parity u ≤ altd_G Even v)"

lemma invar_level_bounded_props[invar_props_elims]:
  "invar_level_bounded bfs_state ⟹
   (⟦⋀v parity u. v ∈ t_set (current bfs_state) ⟹ u ∈ discovered bfs_state parity ⟹
        altd_G parity u ≤ altd_G Even v⟧ ⟹ P) ⟹ P"
  by (auto simp: invar_level_bounded_def)

lemma invar_level_bounded_intro[invar_props_intros]:
  "⟦⋀v parity u. v ∈ t_set (current bfs_state) ⟹ u ∈ discovered bfs_state parity ⟹
       altd_G parity u ≤ altd_G Even v⟧
   ⟹ invar_level_bounded bfs_state"
  by (auto simp: invar_level_bounded_def)

― ‹analogue of invar_3_4 (invar_dist_bounded); downward closure across BOTH parities›
definition "invar_discovered_downclosed bfs_state =
  (∀parity parity' v u. v ∈ discovered bfs_state parity ⟶
      altd_G parity' u ≤ altd_G parity v ⟶ u ∈ discovered bfs_state parity')"

lemma invar_discovered_downclosed_props[invar_props_elims]:
  "invar_discovered_downclosed bfs_state ⟹
   (⟦⋀parity parity' v u. v ∈ discovered bfs_state parity ⟹
        altd_G parity' u ≤ altd_G parity v ⟹ u ∈ discovered bfs_state parity'⟧ ⟹ P) ⟹ P"
  by (auto simp: invar_discovered_downclosed_def)

lemma invar_discovered_downclosed_intro[invar_props_intros]:
  "⟦⋀parity parity' v u. v ∈ discovered bfs_state parity ⟹
       altd_G parity' u ≤ altd_G parity v ⟹ u ∈ discovered bfs_state parity'⟧
   ⟹ invar_discovered_downclosed bfs_state"
  by (auto simp: invar_discovered_downclosed_def)

― ‹analogue of invar_3_1; current is exactly one even level›
definition "invar_current_level bfs_state =
  (∀v ∈ t_set (current bfs_state). ∀u.
      (u ∈ t_set (current bfs_state)) ⟷ (altd_G Even u = altd_G Even v))"

lemma invar_current_level_props[invar_props_elims]:
  "invar_current_level bfs_state ⟹
   (⟦⋀v u. v ∈ t_set (current bfs_state) ⟹
        (u ∈ t_set (current bfs_state)) ⟷ (altd_G Even u = altd_G Even v)⟧ ⟹ P) ⟹ P"
  by (auto simp: invar_current_level_def)

lemma invar_current_level_intro[invar_props_intros]:
  "⟦⋀v u. v ∈ t_set (current bfs_state) ⟹
       (u ∈ t_set (current bfs_state)) ⟷ (altd_G Even u = altd_G Even v)⟧
   ⟹ invar_current_level bfs_state"
  by (auto simp: invar_current_level_def)


― ‹Batch 2: reachability + parity step lemmas.›

― ‹Helper: alt-distances have their parity.›
lemma altd_G_parity:
  assumes "altd_G parity v = enat n"
  shows "of_parity parity n"
proof-
  from assms have notinf: "alt_dist.alt_distance_set unmatched_edge matched_edge parity G (t_set srcs) v ≠ ∞"
    by (auto simp: alt_distance_set_def)
  from alt_dist_set_not_inf[OF notinf] obtain u where
    u_src: "u ∈ t_set srcs" and
    u_dist: "alt_dist.alt_distance unmatched_edge matched_edge parity G u v =
             alt_dist.alt_distance_set unmatched_edge matched_edge parity G (t_set srcs) v"
    by blast
  have u_lt: "alt_dist.alt_distance unmatched_edge matched_edge parity G u v < ∞"
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
  from walk have p_nonempty: "p ≠ []"
    by (auto simp: alt_dist.alt_vwalk_bet_def dest: Vwalk.vwalk_bet_nonempty)
  have n_eq: "n = length p - 1"
    using u_dist dist_p assms by (simp add: alt_distance_set_def)
  show ?thesis
    using parity_len n_eq p_nonempty
    by (cases parity; simp add: parity_simps even_diff_nat)
qed


― ‹I-2a: invar_discovered_reachable -- parity-split reachability (analogue of BFS_2 invar_current_reachable).›

definition "invar_discovered_reachable bfs_state =
  ((∀v ∈ t_set (visited_even bfs_state) ∪ t_set (current bfs_state). altd_G Even v < ∞) ∧
   (∀v ∈ t_set (visited_odd bfs_state). altd_G Odd v < ∞))"

lemma invar_discovered_reachable_props[invar_props_elims]:
  "invar_discovered_reachable bfs_state ⟹
   (⟦∀v ∈ t_set (visited_even bfs_state) ∪ t_set (current bfs_state). altd_G Even v < ∞;
     ∀v ∈ t_set (visited_odd bfs_state). altd_G Odd v < ∞⟧ ⟹ P) ⟹ P"
  by (auto simp: invar_discovered_reachable_def)

lemma invar_discovered_reachable_intro[invar_props_intros]:
  "⟦∀v ∈ t_set (visited_even bfs_state) ∪ t_set (current bfs_state). altd_G Even v < ∞;
    ∀v ∈ t_set (visited_odd bfs_state). altd_G Odd v < ∞⟧
   ⟹ invar_discovered_reachable bfs_state"
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

  define VE' where "VE' = visited_even bfs_state ∪⇩G current bfs_state"
  define P' where "P' = expand_tree unmatching (parents bfs_state) (current bfs_state) (visited_odd bfs_state)"
  define C' where "C' = next_frontier_impl unmatching (current bfs_state) (visited_odd bfs_state)"
  define VO' where "VO' = visited_odd bfs_state ∪⇩G C'"
  define P'' where "P'' = expand_tree matching P' C' VE'"
  define C'' where "C'' = next_frontier_impl matching C' VE'"

  have upd1: "BFS_upd1 bfs_state =
    bfs_state ⦇parents := P'', visited_even := VE', visited_odd := VO', current := C'',
               distances := upd_dists Even matching
                              (upd_dists Odd unmatching (distances bfs_state) (current bfs_state)
                                 (visited_odd bfs_state)) C' VE'⦈"
    by (simp add: BFS_upd1_def Let_def VE'_def P'_def C'_def VO'_def P''_def C''_def)

  have inv_VE'[simp]: "vset_inv VE'" by (auto simp: VE'_def)
  have inv_C'[simp]: "vset_inv C'" by (auto simp: C'_def)
  have inv_VO'[simp]: "vset_inv VO'" by (auto simp: VO'_def)

  have abs_VE': "t_set VE' = t_set (visited_even bfs_state) ∪ t_set (current bfs_state)"
    by (auto simp: VE'_def)
  have abs_C': "t_set C' = next_frontier (Graph.digraph_abs unmatching)
                             (t_set (current bfs_state)) (t_set (visited_odd bfs_state))"
    by (auto simp: C'_def)
  have abs_VO': "t_set VO' = t_set (visited_odd bfs_state) ∪ t_set C'"
    by (auto simp: VO'_def)
  have abs_C'': "t_set C'' = next_frontier (Graph.digraph_abs matching) (t_set C') (t_set VE')"
    by (auto simp: C''_def)

  have odd_new: "altd_G Odd v < ∞" if "v ∈ t_set C'" for v
  proof-
    from that obtain u where u_curr: "u ∈ t_set (current bfs_state)"
      and u_neigh: "v ∈ Pair_Graph.neighbourhood (Graph.digraph_abs unmatching) u"
      by (auto simp: abs_C' next_frontier_def)
    have fin_u: "altd_G Even u < ∞"
      using assms(3) u_curr by (auto simp: invar_discovered_reachable_def)
    have mem_G: "v ∈ Pair_Graph.neighbourhood G u"
      using u_neigh by (auto simp: G_def neighoubrhood_union)
    have unm: "unmatched_edge (u, v)"
      using u_neigh by (simp add: unmatched_edge_def Pair_Graph.neighbourhood_def)
    have le: "altd_G Odd v ≤ altd_G Even u + 1"
      unfolding alt_distance_set_def
      by (intro odd_alt_distance_set_neighbourhood) (fact mem_G, fact srcs_invar(1), fact unm)
    show ?thesis
    proof-
      have h: "altd_G Even u + 1 < ∞" using fin_u by (simp add: plus_eq_infty_iff_enat enat_ord_simps)
      show ?thesis by (rule order_le_less_trans[OF le h])
    qed
  qed

  have even_new: "altd_G Even v < ∞" if "v ∈ t_set C''" for v
  proof-
    from that obtain u where u_C': "u ∈ t_set C'"
      and u_neigh: "v ∈ Pair_Graph.neighbourhood (Graph.digraph_abs matching) u"
      by (auto simp: abs_C'' next_frontier_def)
    have fin_u: "altd_G Odd u < ∞"
      using odd_new[OF u_C'] .
    have mem_G: "v ∈ Pair_Graph.neighbourhood G u"
      using u_neigh by (auto simp: G_def neighoubrhood_union)
    have mat: "matched_edge (u, v)"
      using u_neigh by (simp add: matched_edge_def Pair_Graph.neighbourhood_def)
    have le: "altd_G Even v ≤ altd_G Odd u + 1"
      unfolding alt_distance_set_def
      by (intro even_alt_distance_set_neighbourhood) (fact mem_G, fact srcs_invar(1), fact mat)
    show ?thesis
    proof-
      have h: "altd_G Odd u + 1 < ∞" using fin_u by (simp add: plus_eq_infty_iff_enat enat_ord_simps)
      show ?thesis by (rule order_le_less_trans[OF le h])
    qed
  qed

  show ?thesis
    using assms(3) odd_new even_new
    by (auto simp: upd1 abs_VE' abs_VO' invar_discovered_reachable_def)
qed

lemma invar_discovered_reachable_holds_ret_1[invar_holds_intros]:
  "⟦BFS_ret_1_conds bfs_state; invar_discovered_reachable bfs_state⟧ ⟹
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


― ‹I-2b: Parity step lemmas (analogue of BFS_2 dist_current_plus_1_new, split in two).›

lemma alt_dist_odd_step:
  assumes "invar_level_bounded bfs_state" "invar_discovered_downclosed bfs_state"
          "invar_discovered_reachable bfs_state"
          "v' ∈ t_set (current bfs_state)"
          "v ∈ Pair_Graph.neighbourhood (Graph.digraph_abs unmatching) v'"
          "v ∉ t_set (visited_odd bfs_state)"
  shows "altd_G Odd v = altd_G Even v' + 1"
proof-
  have fin: "altd_G Even v' < ∞"
    using assms(3,4) by (auto simp: invar_discovered_reachable_def)
  have mem_G: "v ∈ Pair_Graph.neighbourhood G v'"
    using assms(5) by (auto simp: G_def neighoubrhood_union)
  have unm: "unmatched_edge (v', v)"
    using assms(5) by (simp add: unmatched_edge_def Pair_Graph.neighbourhood_def)
  have le: "altd_G Odd v ≤ altd_G Even v' + 1"
    unfolding alt_distance_set_def
    by (intro odd_alt_distance_set_neighbourhood) (fact mem_G, fact srcs_invar(1), fact unm)
  have "False" if lt: "altd_G Odd v < altd_G Even v' + 1"
  proof-
    have step1: "altd_G Odd v ≤ altd_G Even v'"
      using lt fin by (cases "altd_G Odd v"; cases "altd_G Even v'") (auto simp: eSuc_enat[symmetric] plus_1_eSuc ileI1)
    hence "v ∈ discovered bfs_state Odd"
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
          "w ∈ t_set (current bfs_state)" "altd_G Odd v' = altd_G Even w + 1"
          "v ∈ Pair_Graph.neighbourhood (Graph.digraph_abs matching) v'"
          "v ∉ t_set (visited_even bfs_state) ∪ t_set (current bfs_state)"
  shows "altd_G Even v = altd_G Odd v' + 1"
proof-
  have finw: "altd_G Even w < ∞"
    using assms(3,4) by (auto simp: invar_discovered_reachable_def)
  hence finv': "altd_G Odd v' < ∞"
    using assms(5) by (simp add: plus_eq_infty_iff_enat)
  have mem_G: "v ∈ Pair_Graph.neighbourhood G v'"
    using assms(6) by (auto simp: G_def neighoubrhood_union)
  have mat: "matched_edge (v', v)"
    using assms(6) by (simp add: matched_edge_def Pair_Graph.neighbourhood_def)
  have le: "altd_G Even v ≤ altd_G Odd v' + 1"
    unfolding alt_distance_set_def
    by (intro even_alt_distance_set_neighbourhood) (fact mem_G, fact srcs_invar(1), fact mat)
  have "False" if lt': "altd_G Even v < altd_G Odd v' + 1"
  proof-
    have step1: "altd_G Even v ≤ altd_G Odd v'"
      using lt' finv' by (cases "altd_G Even v"; cases "altd_G Odd v'") (auto simp: ileI1 plus_1_eSuc)
    ― ‹Parity squeeze: Even value ≤ odd value forces ≤ odd value - 1 = Even w's value.›
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
    have "n ≤ m + 1"
      using step1 nm1 v'_enat by (simp only: enat_simps)
    hence "n ≤ m" using even_n even_m by presburger
    hence "altd_G Even v ≤ altd_G Even w" using nm1 nm2 by (simp add: enat_simps)
    hence "v ∈ discovered bfs_state Even"
      using assms(2,4) by (auto simp: invar_discovered_downclosed_def discovered_def split: parity.splits)
    thus False using assms(7) by (auto simp: discovered_def)
  qed
  thus ?thesis using le by force
qed


― ‹Batch 3a: Descent helpers.›

― ‹Helper 0: generalisation of odd_alt_distance_set_parent (no v ∉ vs premise).
   The key insight: an Odd alt-walk has even length ≥ 2, so the last two vertices
   [w, v] always exist; no u ≠ v assumption is needed.›
lemma odd_alt_distance_set_parent':
  "⟦alt_dist.alt_distance_set P1 P2 Odd G vs v < ∞; vs ≠ {}⟧ ⟹
     ∃w. alt_dist.alt_distance_set P1 P2 Even G vs w + 1 = alt_dist.alt_distance_set P1 P2 Odd G vs v
         ∧ v ∈ Pair_Graph.neighbourhood G w ∧ P1 (w, v)"
proof(goal_cases)
  case 1
  hence notinf: "alt_dist.alt_distance_set P1 P2 Odd G vs v ≠ ∞" by simp
  then obtain u where u_vs: "u ∈ vs"
    and u_eq: "alt_dist.alt_distance_set P1 P2 Odd G vs v = alt_dist.alt_distance P1 P2 Odd G u v"
    by (rule alt_distance_set_wit')
  have u_lt: "alt_dist.alt_distance P1 P2 Odd G u v < ∞"
    using u_eq 1(1) by auto
  then obtain p where p: "alt_dist.alt_shortest_path P1 P2 Odd G u p v"
    by (erule alt_shortest_path_exists_2)
  have "even (length p)"
    using p by (auto dest!: alt_dist.alt_shortest_path_vwalk elim!: alt_dist.alt_vwalk_betE
                     simp: parity_simps)
  moreover have "p ≠ []"
    using p by (auto dest!: alt_dist.alt_shortest_path_vwalk
                     simp: alt_dist.alt_vwalk_bet_def dest: Vwalk.vwalk_bet_nonempty)
  ultimately have len_ge2: "length p ≥ 2"
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
  have v_neigh: "v ∈ Pair_Graph.neighbourhood G w"
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
    have "alt_dist.alt_distance_set P1 P2 Even G vs w ≤ alt_dist.alt_distance P1 P2 Even G u w"
      using u_vs by (rule alt_dist.alt_dist_set_mem)
    hence "alt_dist.alt_distance_set P1 P2 Even G vs w + 1 ≤ alt_dist.alt_distance P1 P2 Even G u w + 1"
      by (simp add: add_right_mono)
    thus "alt_dist.alt_distance_set P1 P2 Even G vs w + 1 ≤ alt_dist.alt_distance_set P1 P2 Odd G vs v"
      by (simp add: dist_eq[symmetric] u_eq)
    show "alt_dist.alt_distance_set P1 P2 Odd G vs v ≤ alt_dist.alt_distance_set P1 P2 Even G vs w + 1"
      using v_neigh 1(2) P1wv by (intro odd_alt_distance_set_neighbourhood)
  qed
  thus ?thesis using v_neigh P1wv by blast
qed

― ‹Helper 1: odd-level u is in visited_odd or the unmatched next_frontier.›
lemma odd_level_in_frontier:
  assumes "invar_level_bounded bfs_state" "invar_discovered_downclosed bfs_state"
          "invar_discovered_reachable bfs_state" "invar_current_level bfs_state"
          "w ∈ t_set (current bfs_state)"
          "altd_G Odd u = altd_G Even w + 1"
  shows "u ∈ t_set (visited_odd bfs_state) ∨
         u ∈ next_frontier (Graph.digraph_abs unmatching)
               (t_set (current bfs_state)) (t_set (visited_odd bfs_state))"
proof(cases "u ∈ t_set (visited_odd bfs_state)")
  case False
  have finw: "altd_G Even w < ∞"
    using assms(3,5) by (auto simp: invar_discovered_reachable_def)
  hence finu: "altd_G Odd u < ∞"
    using assms(6) by (simp add: plus_eq_infty_iff_enat)
  ― ‹odd parent: y with Even level = level of w, unmatched edge (y,u)›
  obtain y where y_dist: "altd_G Even y + 1 = altd_G Odd u"
             and y_neigh: "u ∈ Pair_Graph.neighbourhood G y"
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
  hence "y ∈ t_set (current bfs_state)"
    using assms(4,5) by (auto simp: invar_current_level_def)
  thus ?thesis
    using y_neigh y_unm False
    by (auto simp: next_frontier_def unmatched_edge_def dest: neighbourhoodD)
qed simp

― ‹Helper 2: even-level u at current+2 is in the matched next_frontier over
   the unmatched next_frontier.›
lemma even_level_in_frontier:
  assumes "invar_level_bounded bfs_state" "invar_discovered_downclosed bfs_state"
          "invar_discovered_reachable bfs_state" "invar_current_level bfs_state"
          "w ∈ t_set (current bfs_state)"
          "altd_G Even u = altd_G Even w + 2"
  shows "u ∈ next_frontier (Graph.digraph_abs matching)
               (next_frontier (Graph.digraph_abs unmatching)
                  (t_set (current bfs_state)) (t_set (visited_odd bfs_state)))
               (t_set (visited_even bfs_state) ∪ t_set (current bfs_state))"
proof-
  have finw: "altd_G Even w < ∞"
    using assms(3,5) by (auto simp: invar_discovered_reachable_def)
  hence finu: "altd_G Even u < ∞"
    using assms(6) by (simp add: plus_eq_infty_iff_enat)
  ― ‹Step 1: u not yet even-discovered›
  have u_not_even: "u ∉ t_set (visited_even bfs_state) ∪ t_set (current bfs_state)"
  proof
    assume hin: "u ∈ t_set (visited_even bfs_state) ∪ t_set (current bfs_state)"
    hence "u ∈ discovered bfs_state Even"
      by (auto simp: discovered_def)
    hence "altd_G Even u ≤ altd_G Even w"
      using assms(1,5) by (auto simp: invar_level_bounded_def)
    thus False
      using assms(6) finw
      by (cases "altd_G Even w") (auto simp: one_enat_def)
  qed
  ― ‹Step 2: even parent x via even_alt_distance_set_parent'›
  have pos_u: "0 < altd_G Even u"
    using assms(6) finw by (cases "altd_G Even w") (auto simp: one_enat_def)
  obtain x where x_dist: "altd_G Odd x + 1 = altd_G Even u"
             and x_neigh: "u ∈ Pair_Graph.neighbourhood G x"
             and x_mat: "matched_edge (x, u)"
    using pos_u finu
    unfolding alt_distance_set_def
    by (fastforce dest!: even_alt_distance_set_parent'[OF _ _ srcs_invar(1)]
                  simp: matched_edge_def Pair_Graph.neighbourhood_def)
  ― ‹The Odd distance of x: x_dist gives altd_G Odd x = altd_G Even u - 1 = altd_G Even w + 1›
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
      fix n assume hn: "altd_G Odd x = enat n" and hw: "altd_G Even w = ∞"
      from combined hn hw have False
        by (simp only: hn hw enat_simps)
      thus ?thesis ..
    next
      fix m assume hx: "altd_G Odd x = ∞" and hm: "altd_G Even w = enat m"
      from combined hx hm have False
        by (simp only: hx hm enat_simps)
      thus ?thesis ..
    next
      assume "altd_G Odd x = ∞" "altd_G Even w = ∞"
      thus ?thesis by simp
    qed
  qed
  ― ‹Step 3: x is in the unmatched next_frontier (not in visited_odd)›
  have x_not_odd: "x ∉ t_set (visited_odd bfs_state)"
  proof
    assume "x ∈ t_set (visited_odd bfs_state)"
    hence "x ∈ discovered bfs_state Odd"
      by (auto simp: discovered_def)
    hence "altd_G Odd x ≤ altd_G Even w"
      using assms(1,5) by (auto simp: invar_level_bounded_def)
    thus False
      using x_odd_level finw
      by (cases "altd_G Even w") (auto simp: one_enat_def)
  qed
  have x_in_C': "x ∈ next_frontier (Graph.digraph_abs unmatching)
                      (t_set (current bfs_state)) (t_set (visited_odd bfs_state))"
    using odd_level_in_frontier[OF assms(1,2,3,4,5)] x_odd_level x_not_odd
    by auto
  ― ‹Step 4: assemble u into the matched next_frontier›
  have x_neigh_unm: "u ∈ Pair_Graph.neighbourhood (Graph.digraph_abs matching) x"
    using x_mat x_neigh by (auto simp: matched_edge_def Pair_Graph.neighbourhood_def G_def)
  thus ?thesis
    using x_in_C' u_not_even
    by (auto simp: next_frontier_def dest: neighbourhoodD)
qed



― ‹Batch 3b: invar_level_bounded preservation.›

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

  define VE' where "VE' = visited_even bfs_state ∪⇩G current bfs_state"
  define P' where "P' = expand_tree unmatching (parents bfs_state) (current bfs_state) (visited_odd bfs_state)"
  define C' where "C' = next_frontier_impl unmatching (current bfs_state) (visited_odd bfs_state)"
  define VO' where "VO' = visited_odd bfs_state ∪⇩G C'"
  define P'' where "P'' = expand_tree matching P' C' VE'"
  define C'' where "C'' = next_frontier_impl matching C' VE'"

  have upd1: "BFS_upd1 bfs_state =
    bfs_state ⦇parents := P'', visited_even := VE', visited_odd := VO', current := C'',
               distances := upd_dists Even matching
                              (upd_dists Odd unmatching (distances bfs_state) (current bfs_state)
                                 (visited_odd bfs_state)) C' VE'⦈"
    by (simp add: BFS_upd1_def Let_def VE'_def P'_def C'_def VO'_def P''_def C''_def)

  have inv_VE'[simp]: "vset_inv VE'" by (auto simp: VE'_def)
  have inv_C'[simp]: "vset_inv C'" by (auto simp: C'_def)
  have inv_VO'[simp]: "vset_inv VO'" by (auto simp: VO'_def)

  have abs_VE': "t_set VE' = t_set (visited_even bfs_state) ∪ t_set (current bfs_state)"
    by (auto simp: VE'_def)
  have abs_C': "t_set C' = next_frontier (Graph.digraph_abs unmatching)
                             (t_set (current bfs_state)) (t_set (visited_odd bfs_state))"
    by (auto simp: C'_def)
  have abs_VO': "t_set VO' = t_set (visited_odd bfs_state) ∪ t_set C'"
    by (auto simp: VO'_def)
  have abs_C'': "t_set C'' = next_frontier (Graph.digraph_abs matching) (t_set C') (t_set VE')"
    by (auto simp: C''_def)

  ― ‹Post-state component equalities from upd1.›
  have curr_post_eq: "t_set (current (BFS_upd1 bfs_state)) = t_set C''" by (simp add: upd1)
  have disc_even_post: "discovered (BFS_upd1 bfs_state) Even = t_set VE' ∪ t_set C''"
    by (simp add: upd1 discovered_def split: parity.splits)
  have disc_odd_post: "discovered (BFS_upd1 bfs_state) Odd = t_set VO'"
    by (simp add: upd1 discovered_def split: parity.splits)

  ― ‹enat monotonicity helpers.›
  have enat_le_add11: "(x::enat) ≤ x + 1 + 1" for x by simp
  have enat_plus1_le_plus11: "(x::enat) + 1 ≤ x + 1 + 1" for x by simp

  ― ‹Main goal: for every v in new current C'', every discovered u is bounded.›
  show ?thesis
  proof(intro invar_level_bounded_intro)
    fix v parity u
    assume v_curr_post: "v ∈ t_set (current (BFS_upd1 bfs_state))"
    assume u_disc: "u ∈ discovered (BFS_upd1 bfs_state) parity"
    have v_C'': "v ∈ t_set C''" using v_curr_post curr_post_eq by simp
    ― ‹Decompose v ∈ C'' → v' ∈ C' → w ∈ current.›
    obtain v' where v'_C': "v' ∈ t_set C'"
               and v_neigh: "v ∈ Pair_Graph.neighbourhood (Graph.digraph_abs matching) v'"
               and v_fresh_VE': "v ∉ t_set VE'"
      using v_C'' by (auto simp: abs_C'' next_frontier_def)
    obtain w where w_curr: "w ∈ t_set (current bfs_state)"
              and v'_neigh: "v' ∈ Pair_Graph.neighbourhood (Graph.digraph_abs unmatching) w"
              and v'_fresh: "v' ∉ t_set (visited_odd bfs_state)"
      using v'_C' by (auto simp: abs_C' next_frontier_def)
    have v_fresh_even: "v ∉ t_set (visited_even bfs_state) ∪ t_set (current bfs_state)"
      using v_fresh_VE' by (simp add: abs_VE')
    ― ‹Two-step distances give altd_G Even v = altd_G Even w + 1 + 1.›
    have stepO: "altd_G Odd v' = altd_G Even w + 1"
      using assms(4) assms(5) assms(7) w_curr v'_neigh v'_fresh
      by (rule alt_dist_odd_step)
    have stepE: "altd_G Even v = altd_G Odd v' + 1"
      using assms(4) assms(5) assms(7) w_curr stepO v_neigh v_fresh_even
      by (rule alt_dist_even_step)
    have v_level: "altd_G Even v = altd_G Even w + 1 + 1"
      by (simp add: stepE stepO)
    show "altd_G parity u ≤ altd_G Even v"
    proof(cases parity)
      case Even
      hence u_in: "u ∈ t_set VE' ∪ t_set C''"
        using u_disc disc_even_post by simp
      show ?thesis
      proof(cases "u ∈ t_set (visited_even bfs_state) ∪ t_set (current bfs_state)")
        case True
        ― ‹u pre-Even: IH + monotonicity.›
        have ih: "altd_G Even u ≤ altd_G Even w"
          using assms(4) w_curr True
          by (auto simp: invar_level_bounded_def discovered_def)
        have "altd_G Even u ≤ altd_G Even w + 1 + 1"
          by (rule order_trans[OF ih enat_le_add11])
        with Even v_level show ?thesis by simp
      next
        case False
        ― ‹u ∈ C'' (new Even): same 2-step argument; current-level gives equality.›
        hence u_C'': "u ∈ t_set C''" using u_in abs_VE' by auto
        obtain u' where u'_C': "u' ∈ t_set C'"
                   and u_neigh2: "u ∈ Pair_Graph.neighbourhood (Graph.digraph_abs matching) u'"
                   and u_fresh2: "u ∉ t_set VE'"
          using u_C'' by (auto simp: abs_C'' next_frontier_def)
        obtain w_u where wu_curr: "w_u ∈ t_set (current bfs_state)"
                     and u'_neigh2: "u' ∈ Pair_Graph.neighbourhood (Graph.digraph_abs unmatching) w_u"
                     and u'_fresh2: "u' ∉ t_set (visited_odd bfs_state)"
          using u'_C' by (auto simp: abs_C' next_frontier_def)
        have u_fresh_even: "u ∉ t_set (visited_even bfs_state) ∪ t_set (current bfs_state)"
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
      hence u_in: "u ∈ t_set VO'"
        using u_disc disc_odd_post by simp
      show ?thesis
      proof(cases "u ∈ t_set (visited_odd bfs_state)")
        case True
        ― ‹u pre-Odd: IH + monotonicity.›
        have ih: "altd_G Odd u ≤ altd_G Even w"
          using assms(4) w_curr True
          by (auto simp: invar_level_bounded_def discovered_def)
        have "altd_G Odd u ≤ altd_G Even w + 1 + 1"
          by (rule order_trans[OF ih enat_le_add11])
        with Odd v_level show ?thesis by simp
      next
        case False
        ― ‹u ∈ C' (new Odd): alt_dist_odd_step + current-level gives altd_G Odd u = w+1 ≤ w+1+1.›
        hence u_C': "u ∈ t_set C'" using u_in abs_VO' by auto
        obtain w_u where wu_curr2: "w_u ∈ t_set (current bfs_state)"
                     and u_neigh3: "u ∈ Pair_Graph.neighbourhood (Graph.digraph_abs unmatching) w_u"
                     and u_fresh3: "u ∉ t_set (visited_odd bfs_state)"
          using u_C' by (auto simp: abs_C' next_frontier_def)
        have stepO3: "altd_G Odd u = altd_G Even w_u + 1"
          using assms(4) assms(5) assms(7) wu_curr2 u_neigh3 u_fresh3
          by (rule alt_dist_odd_step)
        have level_eq2: "altd_G Even w_u = altd_G Even w"
          using assms(6) wu_curr2 w_curr by (auto simp: invar_current_level_def)
        have u_dist: "altd_G Odd u = altd_G Even w + 1"
          using stepO3 level_eq2 by simp
        have "altd_G Odd u ≤ altd_G Even w + 1 + 1"
          by (rule order_trans[OF _ enat_plus1_le_plus11]) (simp add: u_dist)
        with Odd v_level show ?thesis by simp
      qed
    qed
  qed
qed

lemma invar_level_bounded_holds_ret_1[invar_holds_intros]:
  "⟦BFS_ret_1_conds bfs_state; invar_level_bounded bfs_state⟧ ⟹
     invar_level_bounded (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)

― ‹Batch 3c: invar_discovered_downclosed preservation.›

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

  define VE' where "VE' = visited_even bfs_state ∪⇩G current bfs_state"
  define P' where "P' = expand_tree unmatching (parents bfs_state) (current bfs_state) (visited_odd bfs_state)"
  define C' where "C' = next_frontier_impl unmatching (current bfs_state) (visited_odd bfs_state)"
  define VO' where "VO' = visited_odd bfs_state ∪⇩G C'"
  define P'' where "P'' = expand_tree matching P' C' VE'"
  define C'' where "C'' = next_frontier_impl matching C' VE'"

  have upd1: "BFS_upd1 bfs_state =
    bfs_state ⦇parents := P'', visited_even := VE', visited_odd := VO', current := C'',
               distances := upd_dists Even matching
                              (upd_dists Odd unmatching (distances bfs_state) (current bfs_state)
                                 (visited_odd bfs_state)) C' VE'⦈"
    by (simp add: BFS_upd1_def Let_def VE'_def P'_def C'_def VO'_def P''_def C''_def)

  have inv_VE'[simp]: "vset_inv VE'" by (auto simp: VE'_def)
  have inv_C'[simp]: "vset_inv C'" by (auto simp: C'_def)
  have inv_VO'[simp]: "vset_inv VO'" by (auto simp: VO'_def)

  have abs_VE': "t_set VE' = t_set (visited_even bfs_state) ∪ t_set (current bfs_state)"
    by (auto simp: VE'_def)
  have abs_C': "t_set C' = next_frontier (Graph.digraph_abs unmatching)
                             (t_set (current bfs_state)) (t_set (visited_odd bfs_state))"
    by (auto simp: C'_def)
  have abs_VO': "t_set VO' = t_set (visited_odd bfs_state) ∪ t_set C'"
    by (auto simp: VO'_def)
  have abs_C'': "t_set C'' = next_frontier (Graph.digraph_abs matching) (t_set C') (t_set VE')"
    by (auto simp: C''_def)

  ― ‹Post-state discovered sets.›
  have disc_even_post: "discovered (BFS_upd1 bfs_state) Even = t_set VE' ∪ t_set C''"
    by (simp add: upd1 discovered_def split: parity.splits)
  have disc_odd_post: "discovered (BFS_upd1 bfs_state) Odd = t_set VO'"
    by (simp add: upd1 discovered_def split: parity.splits)

  ― ‹IH: pre-state downclosed.›
  have IH: "⋀p p' v u. v ∈ discovered bfs_state p ⟹ altd_G p' u ≤ altd_G p v
             ⟹ u ∈ discovered bfs_state p'"
    using assms(5) unfolding invar_discovered_downclosed_def by blast

  ― ‹Pre-state discovered ⊆ post-state discovered (monotonicity).›
  have mono_even: "discovered bfs_state Even ⊆ discovered (BFS_upd1 bfs_state) Even"
  proof
    fix x assume "x ∈ discovered bfs_state Even"
    hence "x ∈ t_set (visited_even bfs_state) ∪ t_set (current bfs_state)"
      by (simp add: discovered_def)
    hence "x ∈ t_set VE'" by (simp add: abs_VE')
    thus "x ∈ discovered (BFS_upd1 bfs_state) Even" by (simp add: disc_even_post)
  qed
  have mono_odd: "discovered bfs_state Odd ⊆ discovered (BFS_upd1 bfs_state) Odd"
  proof
    fix x assume "x ∈ discovered bfs_state Odd"
    hence "x ∈ t_set (visited_odd bfs_state)" by (simp add: discovered_def)
    hence "x ∈ t_set VO'" by (simp add: abs_VO')
    thus "x ∈ discovered (BFS_upd1 bfs_state) Odd" by (simp add: disc_odd_post)
  qed
  have mono: "discovered bfs_state p ⊆ discovered (BFS_upd1 bfs_state) p" for p
    using mono_even mono_odd by (cases p) simp_all

  show ?thesis
  proof(intro invar_discovered_downclosed_intro)
    fix parity parity' v u
    assume v_post: "v ∈ discovered (BFS_upd1 bfs_state) parity"
    assume u_le: "altd_G parity' u ≤ altd_G parity v"
    show "u ∈ discovered (BFS_upd1 bfs_state) parity'"
    proof(cases parity)
      case Odd
      ― ‹v ∈ discovered' Odd = t_set VO' = visited_odd ∪ C'›
      hence v_VO': "v ∈ t_set VO'" using v_post disc_odd_post by simp
      show ?thesis
      proof(cases "v ∈ t_set (visited_odd bfs_state)")
        case True
        ― ‹v pre-Odd: IH gives u ∈ pre-discovered parity' ⊆ post-state.›
        have "v ∈ discovered bfs_state Odd" using True by (auto simp: discovered_def)
        then have "u ∈ discovered bfs_state parity'"
          using IH u_le Odd by blast 
        thus ?thesis using mono by blast
      next
        case False
        ― ‹v ∈ t_set C' (new Odd vertex).›
        hence v_C': "v ∈ t_set C'" using v_VO' abs_VO' by auto
        ― ‹Decompose v ∈ C': obtain w ∈ current with altd_G Odd v = altd_G Even w + 1.›
        obtain w where w_curr: "w ∈ t_set (current bfs_state)"
                   and v_neigh: "v ∈ Pair_Graph.neighbourhood (Graph.digraph_abs unmatching) w"
                   and v_fresh_odd: "v ∉ t_set (visited_odd bfs_state)"
          using v_C' by (auto simp: abs_C' next_frontier_def)
        have stepO: "altd_G Odd v = altd_G Even w + 1"
          using assms(4) assms(5) assms(7) w_curr v_neigh v_fresh_odd
          by (rule alt_dist_odd_step)
        ― ‹finw for arithmetic.›
        have finw: "altd_G Even w < ∞"
          using assms(7) w_curr by (auto simp: invar_discovered_reachable_def)
        obtain m where hm: "altd_G Even w = enat m"
          using finw by (cases "altd_G Even w") auto
        have even_m: "even m" using altd_G_parity[OF hm] by (simp add: parity_simps)
        ― ‹stepO in nat: altd_G Odd v = enat (m + 1).›
        have v_dist: "altd_G Odd v = enat (m + 1)"
          by (simp only: stepO hm enat_simps)
        ― ‹altd_G parity' u ≤ enat (m + 1), hence finite.›
        have u_le_enat: "altd_G parity' u ≤ enat (m + 1)"
        proof-
          have h1: "altd_G parity' u ≤ altd_G Odd v" using u_le Odd by simp
          show ?thesis using h1 v_dist by simp
        qed
        obtain n where hn: "altd_G parity' u = enat n"
          using u_le_enat by (cases "altd_G parity' u") (auto simp only:)
          
        have n_le: "n ≤ m + 1"
        proof-
          have "enat n ≤ enat (m + 1)" using hn u_le_enat by simp
          thus ?thesis by (simp only: enat_simps)
        qed
        show ?thesis
        proof(cases "n ≤ m")
          case True
          ― ‹u level ≤ m = altd_G Even w: IH with w ∈ discovered bfs_state Even closes.›
          have "altd_G parity' u ≤ altd_G Even w" using hn hm True by (simp only: enat_simps)
          have w_disc: "w ∈ discovered bfs_state Even"
            using w_curr by (auto simp: discovered_def)
          have "u ∈ discovered bfs_state parity'" using IH[OF w_disc] ‹altd_G parity' u ≤ altd_G Even w› by blast
          thus ?thesis using mono by blast
        next
          case False
          ― ‹n = m + 1; parity' must be Odd (m even ⟹ m+1 odd).›
          hence n_eq: "n = m + 1" using n_le by arith
          have odd_n: "odd n" using n_eq even_m by arith
          ― ‹parity' = Odd: if parity' = Even then altd_G Even u = enat n with even required.›
          have parity'_Odd: "parity' = Odd"
          proof(cases parity')
            case Even
            have "even n" using altd_G_parity[OF hn[simplified Even]] by (simp add: parity_simps)
            thus ?thesis using odd_n by simp
          next
            case Odd thus ?thesis by simp
          qed
          ― ‹altd_G Odd u = altd_G Even w + 1; odd_level_in_frontier.›
          have u_odd_dist: "altd_G Odd u = altd_G Even w + 1"
          proof-
            have h1: "altd_G Odd u = enat n" using hn parity'_Odd by simp
            have h2: "enat n = enat m + 1" using n_eq
              by (simp only: enat_simps)
            show ?thesis using h1 h2 hm by simp
          qed
          have "u ∈ t_set (visited_odd bfs_state) ∨ u ∈ next_frontier (Graph.digraph_abs unmatching)
                     (t_set (current bfs_state)) (t_set (visited_odd bfs_state))"
            using odd_level_in_frontier[OF assms(4,5,7,6) w_curr u_odd_dist] .
          hence "u ∈ t_set VO'"
            using abs_VO' abs_C' by auto
          thus ?thesis
            using parity'_Odd disc_odd_post by simp
        qed
      qed
    next
      case Even
      ― ‹v ∈ discovered' Even = t_set VE' ∪ t_set C''.›
      hence v_even_post: "v ∈ t_set VE' ∪ t_set C''" using v_post disc_even_post by simp
      show ?thesis
      proof(cases "v ∈ t_set (visited_even bfs_state) ∪ t_set (current bfs_state)")
        case True
        ― ‹v pre-Even: IH closes.›
        have "v ∈ discovered bfs_state Even" using True by (auto simp: discovered_def)
        then have "u ∈ discovered bfs_state parity'" using IH u_le Even by blast
        thus ?thesis using mono by blast
      next
        case False
        ― ‹v ∈ t_set C'' (new Even vertex): v ∉ t_set VE'.›
        have v_fresh_VE': "v ∉ t_set VE'" using False abs_VE' by simp
        hence v_C'': "v ∈ t_set C''" using v_even_post by blast
        ― ‹Decompose v ∈ C'': obtain v' ∈ C', w ∈ current.›
        obtain v' where v'_C': "v' ∈ t_set C'"
                   and v_neigh2: "v ∈ Pair_Graph.neighbourhood (Graph.digraph_abs matching) v'"
                   and v_fresh_VE'2: "v ∉ t_set VE'"
          using v_C'' by (auto simp: abs_C'' next_frontier_def)
        obtain w where w_curr: "w ∈ t_set (current bfs_state)"
                   and v'_neigh2: "v' ∈ Pair_Graph.neighbourhood (Graph.digraph_abs unmatching) w"
                   and v'_fresh_odd2: "v' ∉ t_set (visited_odd bfs_state)"
          using v'_C' by (auto simp: abs_C' next_frontier_def)
        have v_fresh_even2: "v ∉ t_set (visited_even bfs_state) ∪ t_set (current bfs_state)"
          using v_fresh_VE' abs_VE' by simp
        ― ‹Two-step: altd_G Even v = altd_G Even w + 2.›
        have stepO2: "altd_G Odd v' = altd_G Even w + 1"
          using assms(4) assms(5) assms(7) w_curr v'_neigh2 v'_fresh_odd2
          by (rule alt_dist_odd_step)
        have stepE2: "altd_G Even v = altd_G Odd v' + 1"
          using assms(4) assms(5) assms(7) w_curr stepO2 v_neigh2 v_fresh_even2
          by (rule alt_dist_even_step)
        have v_level: "altd_G Even v = altd_G Even w + 1 + 1"
          by (simp add: stepE2 stepO2)
        ― ‹finw for arithmetic.›
        have finw2: "altd_G Even w < ∞"
          using assms(7) w_curr by (auto simp: invar_discovered_reachable_def)
        obtain m where hm2: "altd_G Even w = enat m"
          using finw2 by (cases "altd_G Even w") auto
        have even_m2: "even m" using altd_G_parity[OF hm2] by (simp add: parity_simps)
        ― ‹v_level in enat form: altd_G Even v = enat (m + 2).›
        have v_dist2: "altd_G Even v = enat (m + 2)"
        proof-
          have h1: "altd_G Even v = enat m + 1 + 1"
            by (simp add: v_level hm2 one_enat_def plus_enat_simps(1))
          have h2: "(m + 1 + 1 :: nat) = m + 2" by arith
          thus ?thesis by (simp only: h1 h2 enat_simps)
        qed
        ― ‹altd_G parity' u ≤ enat (m + 2), hence finite.›
        have u_le_enat2: "altd_G parity' u ≤ enat (m + 2)"
        proof-
          have h1: "altd_G parity' u ≤ altd_G Even v" using u_le Even by simp
          show ?thesis using h1 v_dist2 by simp
        qed
        obtain n where hn2: "altd_G parity' u = enat n"
          using u_le_enat2 
          by (cases "altd_G parity' u") (auto simp only:)
        have n_le2: "n ≤ m + 2"
        proof-
          have "enat n ≤ enat (m + 2)" using hn2 u_le_enat2 by simp
          thus ?thesis by (simp only: enat_simps)
        qed
        show ?thesis
        proof(cases "n ≤ m")
          case True
          ― ‹u level ≤ m: IH with w ∈ discovered bfs_state Even closes.›
          have "altd_G parity' u ≤ altd_G Even w" using hn2 hm2 True by (simp only: enat_simps)
          have w_disc2: "w ∈ discovered bfs_state Even"
            using w_curr by (auto simp: discovered_def)
          have "u ∈ discovered bfs_state parity'" using IH[OF w_disc2] ‹altd_G parity' u ≤ altd_G Even w› by blast
          thus ?thesis using mono by blast
        next
          case False
          ― ‹m < n ≤ m + 2: split on parity of n.›
          hence n_gt_m: "m < n" by arith
          show ?thesis
          proof(cases "odd n")
            case True
            ― ‹n = m + 1 (since m < n ≤ m+2 and m even ⟹ n = m+1).›
            hence n_eq2: "n = m + 1" using n_le2 even_m2 n_gt_m by presburger
            ― ‹parity' = Odd.›
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
            have "u ∈ t_set (visited_odd bfs_state) ∨ u ∈ next_frontier (Graph.digraph_abs unmatching)
                       (t_set (current bfs_state)) (t_set (visited_odd bfs_state))"
              using odd_level_in_frontier[OF assms(4,5,7,6) w_curr u_odd_dist2] .
            hence "u ∈ t_set VO'"
              using abs_VO' abs_C' by auto
            thus ?thesis
              using parity'_Odd2 disc_odd_post by simp
          next
            case False
            ― ‹n even; m < n ≤ m+2 and m even ⟹ n = m+2.›
            hence even_n2: "even n" by simp
            hence n_eq3: "n = m + 2" using n_le2 n_gt_m even_m2 by presburger
            ― ‹parity' = Even.›
            have parity'_Even: "parity' = Even"
            proof(cases parity')
              case Odd
              have "odd n" using altd_G_parity[OF hn2[simplified Odd]] by (simp add: parity_simps)
              thus ?thesis using even_n2 by simp
            next
              case Even thus ?thesis by simp
            qed
            ― ‹altd_G Even u = altd_G Even w + 2; even_level_in_frontier.›
            have u_even_dist: "altd_G Even u = altd_G Even w + 2"
            proof-
              have h1: "altd_G Even u = enat n" using hn2 parity'_Even by simp
              have h2: "enat n = enat m + 2" using n_eq3 by (simp only: enat_simps)
              show ?thesis by (simp only: h1 h2 hm2)
            qed
            have u_in_C'': "u ∈ next_frontier (Graph.digraph_abs matching)
                    (next_frontier (Graph.digraph_abs unmatching)
                       (t_set (current bfs_state)) (t_set (visited_odd bfs_state)))
                    (t_set (visited_even bfs_state) ∪ t_set (current bfs_state))"
              using even_level_in_frontier[OF assms(4,5,7,6) w_curr u_even_dist] .
            hence "u ∈ t_set C''"
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
  "⟦BFS_ret_1_conds bfs_state; invar_discovered_downclosed bfs_state⟧ ⟹
     invar_discovered_downclosed (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)

― ‹Batch 3d: invar_current_level preservation + all three whole-loop holds lemmas.›

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

  define VE' where "VE' = visited_even bfs_state ∪⇩G current bfs_state"
  define P' where "P' = expand_tree unmatching (parents bfs_state) (current bfs_state) (visited_odd bfs_state)"
  define C' where "C' = next_frontier_impl unmatching (current bfs_state) (visited_odd bfs_state)"
  define VO' where "VO' = visited_odd bfs_state ∪⇩G C'"
  define P'' where "P'' = expand_tree matching P' C' VE'"
  define C'' where "C'' = next_frontier_impl matching C' VE'"

  have upd1: "BFS_upd1 bfs_state =
    bfs_state ⦇parents := P'', visited_even := VE', visited_odd := VO', current := C'',
               distances := upd_dists Even matching
                              (upd_dists Odd unmatching (distances bfs_state) (current bfs_state)
                                 (visited_odd bfs_state)) C' VE'⦈"
    by (simp add: BFS_upd1_def Let_def VE'_def P'_def C'_def VO'_def P''_def C''_def)

  have inv_VE'[simp]: "vset_inv VE'" by (auto simp: VE'_def)
  have inv_C'[simp]: "vset_inv C'" by (auto simp: C'_def)
  have inv_VO'[simp]: "vset_inv VO'" by (auto simp: VO'_def)

  have abs_VE': "t_set VE' = t_set (visited_even bfs_state) ∪ t_set (current bfs_state)"
    by (auto simp: VE'_def)
  have abs_C': "t_set C' = next_frontier (Graph.digraph_abs unmatching)
                             (t_set (current bfs_state)) (t_set (visited_odd bfs_state))"
    by (auto simp: C'_def)
  have abs_VO': "t_set VO' = t_set (visited_odd bfs_state) ∪ t_set C'"
    by (auto simp: VO'_def)
  have abs_C'': "t_set C'' = next_frontier (Graph.digraph_abs matching) (t_set C') (t_set VE')"
    by (auto simp: C''_def)

  have curr_post_eq: "t_set (current (BFS_upd1 bfs_state)) = t_set C''" by (simp add: upd1)

  ― ‹Helper: every v ∈ t_set C'' satisfies altd_G Even v = altd_G Even w + 1 + 1 for some w ∈ current.›
  have C''_level: "⋀v. v ∈ t_set C'' ⟹ ∃w ∈ t_set (current bfs_state). altd_G Even v = altd_G Even w + 1 + 1"
  proof-
    fix v assume v_C'': "v ∈ t_set C''"
    obtain v' where v'_C': "v' ∈ t_set C'"
               and v_neigh: "v ∈ Pair_Graph.neighbourhood (Graph.digraph_abs matching) v'"
               and v_fresh_VE': "v ∉ t_set VE'"
      using v_C'' by (auto simp: abs_C'' next_frontier_def)
    obtain w where w_curr: "w ∈ t_set (current bfs_state)"
              and v'_neigh: "v' ∈ Pair_Graph.neighbourhood (Graph.digraph_abs unmatching) w"
              and v'_fresh: "v' ∉ t_set (visited_odd bfs_state)"
      using v'_C' by (auto simp: abs_C' next_frontier_def)
    have v_fresh_even: "v ∉ t_set (visited_even bfs_state) ∪ t_set (current bfs_state)"
      using v_fresh_VE' by (simp add: abs_VE')
    have stepO: "altd_G Odd v' = altd_G Even w + 1"
      using assms(4) assms(5) assms(7) w_curr v'_neigh v'_fresh by (rule alt_dist_odd_step)
    have stepE: "altd_G Even v = altd_G Odd v' + 1"
      using assms(4) assms(5) assms(7) w_curr stepO v_neigh v_fresh_even by (rule alt_dist_even_step)
    have v_level: "altd_G Even v = altd_G Even w + 1 + 1"
      by (simp add: stepE stepO)
    thus "∃w ∈ t_set (current bfs_state). altd_G Even v = altd_G Even w + 1 + 1"
      using w_curr by blast
  qed

  show ?thesis
  proof(intro invar_current_level_intro)
    fix v u
    assume v_post: "v ∈ t_set (current (BFS_upd1 bfs_state))"
    have v_C'': "v ∈ t_set C''" using v_post curr_post_eq by simp
    obtain wv where wv_curr: "wv ∈ t_set (current bfs_state)"
                and v_lev: "altd_G Even v = altd_G Even wv + 1 + 1"
      using C''_level[OF v_C''] by blast
    show "(u ∈ t_set (current (BFS_upd1 bfs_state))) ⟷ (altd_G Even u = altd_G Even v)"
    proof
      ― ‹→ direction: u ∈ C'' ⟹ altd_G Even u = altd_G Even v›
      assume u_post: "u ∈ t_set (current (BFS_upd1 bfs_state))"
      have u_C'': "u ∈ t_set C''" using u_post curr_post_eq by simp
      obtain wu where wu_curr: "wu ∈ t_set (current bfs_state)"
                  and u_lev: "altd_G Even u = altd_G Even wu + 1 + 1"
        using C''_level[OF u_C''] by blast
      have level_eq: "altd_G Even wu = altd_G Even wv"
        using assms(6) wu_curr wv_curr by (auto simp: invar_current_level_def)
      show "altd_G Even u = altd_G Even v"
        using u_lev v_lev level_eq by simp
    next
      ― ‹← direction: altd_G Even u = altd_G Even v ⟹ u ∈ C''›
      assume level_eq: "altd_G Even u = altd_G Even v"
      ― ‹altd_G Even u = altd_G Even wv + 1 + 1 = altd_G Even wv + 2.›
      have u_level: "altd_G Even u = altd_G Even wv + 2"
      proof-
        have "altd_G Even u = altd_G Even wv + 1 + 1" using level_eq v_lev by simp
        thus ?thesis by simp
      qed
      ― ‹even_level_in_frontier gives u ∈ next_frontier matching C' (VE'), i.e., t_set C''.›
      have u_in_C'': "u ∈ next_frontier (Graph.digraph_abs matching)
              (next_frontier (Graph.digraph_abs unmatching)
                 (t_set (current bfs_state)) (t_set (visited_odd bfs_state)))
              (t_set (visited_even bfs_state) ∪ t_set (current bfs_state))"
        using even_level_in_frontier[OF assms(4,5,7,6) wv_curr u_level] .
      hence "u ∈ t_set C''"
        by (simp add: abs_C'' abs_C' abs_VE')
      thus "u ∈ t_set (current (BFS_upd1 bfs_state))"
        using curr_post_eq by simp
    qed
  qed
qed

lemma invar_current_level_holds_ret_1[invar_holds_intros]:
  "⟦BFS_ret_1_conds bfs_state; invar_current_level bfs_state⟧ ⟹
     invar_current_level (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)

― ‹Whole-loop holds lemmas for the three level invariants (mutually dependent, so each assumes all three).›

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



end text ‹context›

end text ‹locale @{const BFS}›
end
