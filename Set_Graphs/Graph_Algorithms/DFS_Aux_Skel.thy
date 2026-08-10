theory DFS_Aux_Skel
  imports Directed_Cycle_DFS.DFS_DirCycle
begin

text ‹Undirected-graph cycle detection (skeleton instance) as an instance of the DFS skeleton. This is a self-contained
replacement for the ‹DFS_Aux› development: it reuses only the record ‹('ver,'vset) DFS_dircycle_state›
(skeleton spine plus a finished set and a cycle flag) from ‹DFS_DirCycle›, not its lemmas. Unlike the
directed instance, the back-edge test excludes the immediate stack parent (‹excl›), and the graph is
assumed symmetric and self-loop-free (undirected).›

subsection ‹Algorithm-independent helper lemmas on the DFS tree edge set›

lemma dfs_tree_aux1:
  assumes "l = v # l_tl" "w ∉ (set l ∪ F)"
    "∀(x, y) ∈ dG. (x ∈ F ⟶ y ∈ (set l ∪ F)) ∧ (y ∈ F ⟶ x ∈ (set l ∪ F))"
  shows
    "set (edges_of_vwalk (rev (w # l))) ∪ set (edges_of_vwalk (w # l)) ∪
    {(x, y). (x, y) ∈ dG ∧ x ∈ set (w # l) ∧ y ∈ F} ∪
    {(x, y). (x, y) ∈ dG ∧ x ∈ F ∧ y ∈ set (w # l)} ∪
    {(x, y). (x, y) ∈ dG ∧ x ∈ F ∧ y ∈ F} =
    {(v, w), (w, v)} ∪
    set (edges_of_vwalk (rev l)) ∪ set (edges_of_vwalk l) ∪
    {(x, y). (x, y) ∈ dG ∧ x ∈ set l ∧ y ∈ F} ∪
    {(x, y). (x, y) ∈ dG ∧ x ∈ F ∧ y ∈ set l} ∪
    {(x, y). (x, y) ∈ dG ∧ x ∈ F ∧ y ∈ F}"
proof-
  have 1: "set (edges_of_vwalk (w # l)) = {(w, v)} ∪ set (edges_of_vwalk l)"
    using assms(1) by simp

  have last_revl: "last (rev l) = v" using assms(1) by (simp add: last_rev)
  have revlne: "rev l ≠ []" using assms(1) by simp
  have "edges_of_vwalk (rev (w # l)) = (edges_of_vwalk (rev l)) @ [(v, w)]"
    using last_revl revlne by (simp add: edges_of_vwalk_append_3)
  then have 2: "set (edges_of_vwalk (rev (w # l))) = {(v, w)} ∪ set (edges_of_vwalk (rev l))" by simp

  from assms(2) assms(3)
    have 3: "{(x, y). (x, y) ∈ dG ∧ x ∈ set (w # l) ∧ y ∈ F} =
    {(x, y). (x, y) ∈ dG ∧ x ∈ set l ∧ y ∈ F}" by auto
  from assms(2) assms(3)
    have 4: "{(x, y). (x, y) ∈ dG ∧ x ∈ F ∧ y ∈ set (w # l)} =
    {(x, y). (x, y) ∈ dG ∧ x ∈ F ∧ y ∈ set l}" by auto

  from 1 2 3 4 show ?thesis by auto
qed

lemma dfs_tree_aux2_1:
  assumes "l = v # l_tl" "l_tl = []" "(∀(x, y) ∈ dG. x ≠ y)"
  shows
    "set (edges_of_vwalk (rev l_tl)) ∪ set (edges_of_vwalk l_tl) ∪
    {(x, y). (x, y) ∈ dG ∧ x ∈ set l_tl ∧ y ∈ (insert v F)} ∪
    {(x, y). (x, y) ∈ dG ∧ x ∈ (insert v F) ∧ y ∈ set l_tl} ∪
    {(x, y). (x, y) ∈ dG ∧ x ∈ (insert v F) ∧ y ∈ (insert v F)} =
    set (edges_of_vwalk (rev l)) ∪ set (edges_of_vwalk l) ∪
    {(x, y). (x, y) ∈ dG ∧ x ∈ set l ∧ y ∈ F} ∪
    {(x, y). (x, y) ∈ dG ∧ x ∈ F ∧ y ∈ set l} ∪
    {(x, y). (x, y) ∈ dG ∧ x ∈ F ∧ y ∈ F}"
proof-
  have 1: "set (edges_of_vwalk l_tl) = set (edges_of_vwalk l)"
    using assms(1) assms(2) by simp
  have 2: "set (edges_of_vwalk (rev l_tl)) = set (edges_of_vwalk (rev l))"
    using assms(1) assms(2) by simp

  have 3: "{(x, y). (x, y) ∈ dG ∧ x ∈ set l ∧ y ∈ F} =
    {(x, y). (x, y) ∈ dG ∧ x ∈ set l_tl ∧ y ∈ (insert v F)} ∪ {(x, y). (x, y) ∈ dG ∧ x = v ∧ y ∈ F}"
    using assms(1) assms(2) by simp

  have 4: "{(x, y). (x, y) ∈ dG ∧ x ∈ F ∧ y ∈ set l} =
    {(x, y). (x, y) ∈ dG ∧ x ∈ (insert v F) ∧ y ∈ set l_tl} ∪ {(x, y). (x, y) ∈ dG ∧ x ∈ F ∧ y = v}"
    using assms(1) assms(2) by simp

  have 5: "{(x, y). (x, y) ∈ dG ∧ x ∈ (insert v F) ∧ y ∈ (insert v F)} =
    {(x, y). (x, y) ∈ dG ∧ x ∈ F ∧ y ∈ F} ∪
    {(x, y). (x, y) ∈ dG ∧ x = v ∧ y ∈ F} ∪
    {(x, y). (x, y) ∈ dG ∧ x ∈ F ∧ y = v}" using assms(3) by auto

  from 1 2 3 4 5 show ?thesis by auto
qed

lemma dfs_tree_aux2_2:
  assumes "l = v # l_tl" "l_tl = u # l_tl_tl" "(∀(x, y) ∈ dG. x ≠ y)" "{(u, v), (v, u)} ⊆ dG"
    "set l_tl ∩ F = {}" "∀(x, y) ∈ dG. (x = v ⟶ y ≠ u ⟶ y ∈ F) ∧ (y = v ⟶ x ≠ u ⟶ x ∈ F)"
  shows
    "set (edges_of_vwalk (rev l_tl)) ∪ set (edges_of_vwalk l_tl) ∪
    {(x, y). (x, y) ∈ dG ∧ x ∈ set l_tl ∧ y ∈ (insert v F)} ∪
    {(x, y). (x, y) ∈ dG ∧ x ∈ (insert v F) ∧ y ∈ set l_tl} ∪
    {(x, y). (x, y) ∈ dG ∧ x ∈ (insert v F) ∧ y ∈ (insert v F)} =
    set (edges_of_vwalk (rev l)) ∪ set (edges_of_vwalk l) ∪
    {(x, y). (x, y) ∈ dG ∧ x ∈ set l ∧ y ∈ F} ∪
    {(x, y). (x, y) ∈ dG ∧ x ∈ F ∧ y ∈ set l} ∪
    {(x, y). (x, y) ∈ dG ∧ x ∈ F ∧ y ∈ F}"
proof-
  have 1: "set (edges_of_vwalk l) = {(v, u)} ∪ set (edges_of_vwalk l_tl)"
    using assms(1) assms(2) by simp

  have last_revlt: "last (rev l_tl) = u" using assms(2) by (simp add: last_rev)
  have revltne: "rev l_tl ≠ []" using assms(2) by simp
  have "edges_of_vwalk (rev l) = (edges_of_vwalk (rev l_tl)) @ [(u, v)]"
    using last_revlt revltne assms(1) by (simp add: edges_of_vwalk_append_3)
  then have 2: "set (edges_of_vwalk (rev l)) = {(u, v)} ∪ set (edges_of_vwalk (rev l_tl))" by simp

  have "{(x, y). (x, y) ∈ dG ∧ x ∈ set l_tl ∧ y = v} =
    {(u, v)} ∪ {(x, y). (x, y) ∈ dG ∧ x ∈ set l_tl_tl ∧ y = v}"
    using assms(2) assms(4) by auto
  then have "{(x, y). (x, y) ∈ dG ∧ x ∈ set l_tl ∧ y = v} = {(u, v)}"
    using assms(5) assms(6) by blast
  then have 3: "{(x, y). (x, y) ∈ dG ∧ x ∈ set l_tl ∧ y ∈ (insert v F)} =
    {(x, y). (x, y) ∈ dG ∧ x ∈ set l_tl ∧ y ∈ F} ∪ {(u, v)}" by auto
  have 4: "{(x, y). (x, y) ∈ dG ∧ x ∈ set l ∧ y ∈ F} =
    {(x, y). (x, y) ∈ dG ∧ x ∈ set l_tl ∧ y ∈ F} ∪ {(x, y). (x, y) ∈ dG ∧ x = v ∧ y ∈ F}"
    using assms(1) by auto

  have "{(x, y). (x, y) ∈ dG ∧ x = v ∧ y ∈ set l_tl} =
    {(v, u)} ∪ {(x, y). (x, y) ∈ dG ∧ x = v ∧ y ∈ set l_tl_tl}"
    using assms(2) assms(4) by auto
  then have "{(x, y). (x, y) ∈ dG ∧ x = v ∧ y ∈ set l_tl} = {(v, u)}"
    using assms(2) assms(5) assms(6) by auto
  then have 5: "{(x, y). (x, y) ∈ dG ∧ x ∈ (insert v F) ∧ y ∈ set l_tl} =
    {(x, y). (x, y) ∈ dG ∧ x ∈ F ∧ y ∈ set l_tl} ∪ {(v, u)}" by fast
  have 6: "{(x, y). (x, y) ∈ dG ∧ x ∈ F ∧ y ∈ set l} =
    {(x, y). (x, y) ∈ dG ∧ x ∈ F ∧ y ∈ set l_tl} ∪ {(x, y). (x, y) ∈ dG ∧ x ∈ F ∧ y = v}"
    using assms(1) by auto

  have 7: "{(x, y). (x, y) ∈ dG ∧ x ∈ (insert v F) ∧ y ∈ (insert v F)} =
    {(x, y). (x, y) ∈ dG ∧ x ∈ F ∧ y ∈ F} ∪
    {(x, y). (x, y) ∈ dG ∧ x = v ∧ y ∈ F} ∪
    {(x, y). (x, y) ∈ dG ∧ x ∈ F ∧ y = v}" using assms(3) by auto

  from 1 2 3 4 5 6 7 show ?thesis by auto
qed


subsection ‹The locale and the semantics via the skeleton callbacks›

locale DFS_Aux_Skel =
  Graph: Pair_Graph_Specs where lookup = lookup +
 set_ops: Set2 vset_empty vset_delete _ t_set vset_inv insert
for lookup :: "'adjmap ⇒ 'v ⇒ 'vset option" +
fixes G::"'adjmap" and s::"'v"
begin

abbreviation "neighbourhood' ≡ Graph.neighbourhood G"
notation "neighbourhood'" ("𝒩⇩G _" 100)

text ‹The back-edge test excludes the immediate stack parent ‹excl› (undirected DFS).›
definition "aux_found (dfs_state::('v,'vset) DFS_dircycle_state) =
   (case stack dfs_state of [] ⇒ False
    | (v # stack_tl) ⇒
       (((𝒩⇩G v) -⇩G (case stack_tl of [] ⇒ ∅⇩N | u # _ ⇒ insert u ∅⇩N))
          ∩⇩G (seen dfs_state -⇩G finished dfs_state)) ≠ ∅⇩N)"

definition "aux_on_found (dfs_state::('v,'vset) DFS_dircycle_state) = (dfs_state ⦇cycle := True⦈)"

definition "aux_on_empty (dfs_state::('v,'vset) DFS_dircycle_state) = dfs_state"

definition "aux_on_backtrack v (dfs_state::('v,'vset) DFS_dircycle_state) = (dfs_state ⦇finished := insert v (finished dfs_state)⦈)"

definition "initial_state =
  ⦇stack = [s], seen = insert s ∅⇩N, finished = ∅⇩N, cycle = False⦈"

text ‹We assume the graph is symmetric since we will run the algorithm on undirected graphs, and that
it has no self-loops.›
definition "DFS_Aux_axioms = (
  Graph.graph_inv G ∧ Graph.finite_graph G ∧ Graph.finite_vsets G ∧ s ∈ dVs (Graph.digraph_abs G) ∧
  (∀(x, y) ∈ (Graph.digraph_abs G). (y, x) ∈ Graph.digraph_abs G) ∧
  (∀x ∈ dVs (Graph.digraph_abs G). (x, x) ∉ Graph.digraph_abs G))"

sublocale aux: DFS_skel
  where lookup = lookup and G = G and s = s
    and found = aux_found and on_found = aux_on_found
    and on_empty = aux_on_empty and on_backtrack = aux_on_backtrack
  by unfold_locales

abbreviation "DFS_Aux_skel ≡ aux.DFS_skel"
abbreviation "DFS_Aux_skel_impl ≡ aux.DFS_skel_impl"

end

locale DFS_Aux_Skel_thms = DFS_Aux_Skel +
  assumes DFS_Aux_axioms: DFS_Aux_axioms
begin

lemma spine_preservation:
  "stack (aux_on_found st) = stack st" "seen (aux_on_found st) = seen st"
  "stack (aux_on_empty st) = stack st" "seen (aux_on_empty st) = seen st"
  "stack (aux_on_backtrack v st) = stack st" "seen (aux_on_backtrack v st) = seen st"
  by (auto simp: aux_on_found_def aux_on_empty_def aux_on_backtrack_def)

sublocale aux: DFS_skel_thms
  where lookup = lookup and G = G and s = s
    and found = aux_found and on_found = aux_on_found
    and on_empty = aux_on_empty and on_backtrack = aux_on_backtrack
  using DFS_Aux_axioms
  by (unfold_locales)
     (auto simp: aux.DFS_skel_axioms_def DFS_Aux_axioms_def
                 aux_on_found_def aux_on_empty_def aux_on_backtrack_def)

subsection ‹The DFS tree and the invariants›

definition "dfs_tree dfs_aux_state =
  set (edges_of_vwalk (rev (stack dfs_aux_state))) ∪ set (edges_of_vwalk (stack dfs_aux_state)) ∪
  {(x, y). (x, y) ∈ (Graph.digraph_abs G) ∧ x ∈ set (stack dfs_aux_state) ∧ y ∈ t_set (finished dfs_aux_state)} ∪
  {(x, y). (x, y) ∈ (Graph.digraph_abs G) ∧ x ∈ t_set (finished dfs_aux_state) ∧ y ∈ set (stack dfs_aux_state)} ∪
  {(x, y). (x, y) ∈ (Graph.digraph_abs G) ∧ x ∈ t_set (finished dfs_aux_state) ∧ y ∈ t_set (finished dfs_aux_state)}"

definition "invar_1 dfs_aux_state = (vset_inv (seen dfs_aux_state) ∧ vset_inv (finished dfs_aux_state))"

definition "invar_2 dfs_aux_state = (Vwalk.vwalk (Graph.digraph_abs G) (rev (stack dfs_aux_state)))"

definition "invar_s_in_stack dfs_aux_state =
  (stack (dfs_aux_state) ≠ [] ⟶ last (stack dfs_aux_state) = s)"

definition "invar_seen_stack_finished dfs_aux_state ⟷
    distinct (stack dfs_aux_state)
    ∧ set (stack dfs_aux_state) ⊆ t_set (seen dfs_aux_state)
    ∧ t_set (finished dfs_aux_state) ⊆ t_set (seen dfs_aux_state)
    ∧ t_set (finished dfs_aux_state) = t_set (seen dfs_aux_state) - set (stack dfs_aux_state)
    ∧ t_set (seen dfs_aux_state) ⊆ dVs (Graph.digraph_abs G)"

definition "invar_finished_vsets dfs_aux_state =
  (∀v ∈ t_set (finished (dfs_aux_state)). t_set (𝒩⇩G v) ⊆ t_set (seen (dfs_aux_state)))"

definition "invar_seen_reachable dfs_aux_state =
  (∀v ∈ t_set (seen dfs_aux_state). ∃p. awalk (Graph.digraph_abs G) s p v)"

definition "invar_visited_through_seen dfs_aux_state =
  (∀v ∈ t_set (seen dfs_aux_state). (∀w ∈ dVs (Graph.digraph_abs G) - t_set (seen dfs_aux_state).
     (∀p. Vwalk.vwalk_bet (Graph.digraph_abs G) v p w ∧ distinct p ⟶ (set p ∩ set (stack dfs_aux_state) ≠ {}))))"

definition "invar_dfs_tree_seen_1 dfs_aux_state =
  ((dfs_tree dfs_aux_state) = {} ⟶ t_set (seen dfs_aux_state) = {s})"

definition "invar_dfs_tree_seen_2 dfs_aux_state =
  ((dfs_tree dfs_aux_state) ≠ {} ⟶ dVs (dfs_tree dfs_aux_state) = t_set (seen dfs_aux_state))"

text ‹If the cycle attribute is false, there does not exist a cycle in dfs_tree.›
definition "invar_cycle_false dfs_aux_state =
   ( ¬cycle dfs_aux_state ⟶ (∄c. cycle' (dfs_tree dfs_aux_state) c))"

text ‹If the cycle attribute is true, there exists a cycle in the graph.›
definition "invar_cycle_true dfs_aux_state =
            ( cycle dfs_aux_state ⟶ (∃c. cycle' (Graph.digraph_abs G) c))"

definition "state_rel_1 dfs_aux_state_1 dfs_aux_state_2
              = ( t_set (seen dfs_aux_state_1) ⊆ t_set (seen dfs_aux_state_2))"

context
includes set_ops.automation2 and Graph.adjmap.automation and Graph.vset.set.automation
begin

lemma graph_inv[simp,intro]:
          "Graph.graph_inv G"
          "Graph.finite_graph G"
          "Graph.finite_vsets G"
  using DFS_Aux_axioms
  by (auto simp: DFS_Aux_axioms_def)

lemma s_in_G[simp,intro]: "s ∈ dVs (Graph.digraph_abs G)"
  using DFS_Aux_axioms
  by (auto simp: DFS_Aux_axioms_def)

lemma graph_symmetric[simp]:
  "(x, y) ∈ (Graph.digraph_abs G) ⟹ (y, x) ∈ (Graph.digraph_abs G)"
  using DFS_Aux_axioms
  by (auto simp: DFS_Aux_axioms_def)

lemma graph_no_self_loops1[simp]:
  "x ∈ dVs (Graph.digraph_abs G) ⟹ (x, x) ∉ Graph.digraph_abs G"
  using DFS_Aux_axioms
  by (auto simp: DFS_Aux_axioms_def)

lemma graph_no_self_loops2[simp]:
  "(x, y) ∈ (Graph.digraph_abs G) ⟹ x ≠ y"
  using graph_no_self_loops1 by blast

text ‹upd2 explicitly: pop the head and mark it finished.›
lemma upd2_unfold:
  "stack (aux.DFS_skel_upd2 st) = tl (stack st)"
  "seen (aux.DFS_skel_upd2 st) = seen st"
  "finished (aux.DFS_skel_upd2 st) = insert (hd (stack st)) (finished st)"
  "cycle (aux.DFS_skel_upd2 st) = cycle st"
  by (auto simp: aux.DFS_skel_upd2_def aux_on_backtrack_def)

lemma upd1_unfold:
  "stack (aux.DFS_skel_upd1 st) = sel ((𝒩⇩G (hd (stack st))) -⇩G seen st) # stack st"
  "seen (aux.DFS_skel_upd1 st) = insert (sel ((𝒩⇩G (hd (stack st))) -⇩G seen st)) (seen st)"
  "finished (aux.DFS_skel_upd1 st) = finished st"
  "cycle (aux.DFS_skel_upd1 st) = cycle st"
  by (auto simp: aux.DFS_skel_upd1_def Let_def)

text ‹The ‹found›-condition of the skeleton, exposed in the parent-excluding form.›
lemma found_unfold:
  "stack st = v # stack_tl ⟹
   aux_found st = (((𝒩⇩G v) -⇩G (case stack_tl of [] ⇒ ∅⇩N | u # _ ⇒ insert u ∅⇩N))
          ∩⇩G (seen st -⇩G finished st) ≠ ∅⇩N)"
  by (simp add: aux_found_def)

text ‹Exposing the parent-excluding back-edge facts hidden inside the skeleton conditions. The
skeleton's ‹found› already contains the ‹excl› test, so ‹¬found› is exactly the empty-intersection
fact from the original ‹call_1›/‹call_2› elims, and the skeleton ‹ret_2› (found) is the original
‹ret_1› (back-edge found).›
lemma call_1_excl:
  assumes "aux.DFS_skel_call_1_conds dfs_aux_state"
  shows "∃v stack_tl. stack dfs_aux_state = v # stack_tl"
    "((𝒩⇩G (hd (stack dfs_aux_state))) -⇩G (case (tl (stack dfs_aux_state)) of [] ⇒ ∅⇩N | u # _ ⇒ insert u ∅⇩N))
       ∩⇩G (seen dfs_aux_state -⇩G finished dfs_aux_state) = ∅⇩N"
    "((𝒩⇩G (hd (stack dfs_aux_state))) -⇩G (seen dfs_aux_state)) ≠ ∅⇩N"
proof -
  from assms obtain v stack_tl where stk: "stack dfs_aux_state = v # stack_tl"
    and nf: "¬ aux_found dfs_aux_state"
    and ns: "(𝒩⇩G (hd (stack dfs_aux_state))) -⇩G (seen dfs_aux_state) ≠ ∅⇩N"
    by (auto elim!: call_cond_elims)
  show "∃v stack_tl. stack dfs_aux_state = v # stack_tl" using stk by blast
  show "((𝒩⇩G (hd (stack dfs_aux_state))) -⇩G (seen dfs_aux_state)) ≠ ∅⇩N" using ns .
  from nf stk found_unfold[of dfs_aux_state v stack_tl]
    show "((𝒩⇩G (hd (stack dfs_aux_state))) -⇩G (case (tl (stack dfs_aux_state)) of [] ⇒ ∅⇩N | u # _ ⇒ insert u ∅⇩N))
       ∩⇩G (seen dfs_aux_state -⇩G finished dfs_aux_state) = ∅⇩N"
    by simp
qed

lemma call_2_excl:
  assumes "aux.DFS_skel_call_2_conds dfs_aux_state"
  shows "∃v stack_tl. stack dfs_aux_state = v # stack_tl"
    "((𝒩⇩G (hd (stack dfs_aux_state))) -⇩G (case (tl (stack dfs_aux_state)) of [] ⇒ ∅⇩N | u # _ ⇒ insert u ∅⇩N))
       ∩⇩G (seen dfs_aux_state -⇩G finished dfs_aux_state) = ∅⇩N"
    "((𝒩⇩G (hd (stack dfs_aux_state))) -⇩G (seen dfs_aux_state)) = ∅⇩N"
proof -
  from assms obtain v stack_tl where stk: "stack dfs_aux_state = v # stack_tl"
    and nf: "¬ aux_found dfs_aux_state"
    and ns: "(𝒩⇩G (hd (stack dfs_aux_state))) -⇩G (seen dfs_aux_state) = ∅⇩N"
    by (auto elim!: call_cond_elims)
  show "∃v stack_tl. stack dfs_aux_state = v # stack_tl" using stk by blast
  show "((𝒩⇩G (hd (stack dfs_aux_state))) -⇩G (seen dfs_aux_state)) = ∅⇩N" using ns .
  from nf stk found_unfold[of dfs_aux_state v stack_tl]
    show "((𝒩⇩G (hd (stack dfs_aux_state))) -⇩G (case (tl (stack dfs_aux_state)) of [] ⇒ ∅⇩N | u # _ ⇒ insert u ∅⇩N))
       ∩⇩G (seen dfs_aux_state -⇩G finished dfs_aux_state) = ∅⇩N"
    by simp
qed

text ‹The skeleton ‹ret_2› is the original ‹ret_1› (back edge found).›
lemma ret_2_found:
  assumes "aux.DFS_skel_ret_2_conds dfs_aux_state"
  shows "∃v stack_tl. stack dfs_aux_state = v # stack_tl"
    "((𝒩⇩G (hd (stack dfs_aux_state))) -⇩G (case (tl (stack dfs_aux_state)) of [] ⇒ ∅⇩N | u # _ ⇒ insert u ∅⇩N))
       ∩⇩G (seen dfs_aux_state -⇩G finished dfs_aux_state) ≠ ∅⇩N"
proof -
  from assms obtain v stack_tl where stk: "stack dfs_aux_state = v # stack_tl"
    and f: "aux_found dfs_aux_state"
    by (auto elim!: call_cond_elims)
  show "∃v stack_tl. stack dfs_aux_state = v # stack_tl" using stk by blast
  from f stk found_unfold[of dfs_aux_state v stack_tl]
    show "((𝒩⇩G (hd (stack dfs_aux_state))) -⇩G (case (tl (stack dfs_aux_state)) of [] ⇒ ∅⇩N | u # _ ⇒ insert u ∅⇩N))
       ∩⇩G (seen dfs_aux_state -⇩G finished dfs_aux_state) ≠ ∅⇩N"
    by simp
qed

subsection ‹invar_1: seen and finished are valid vsets›

lemma invar_1_props[invar_props_elims]:
  "invar_1 dfs_aux_state ⟹
     (⟦vset_inv (seen dfs_aux_state); vset_inv (finished dfs_aux_state)⟧ ⟹ P) ⟹ P"
  by (auto simp: invar_1_def)

lemma invar_1_intro[invar_props_intros]:
  "⟦vset_inv (seen dfs_aux_state); vset_inv (finished dfs_aux_state)⟧ ⟹ invar_1 dfs_aux_state"
  by (auto simp: invar_1_def)

lemma invar_1_holds_upd1[invar_holds_intros]:
  "⟦aux.DFS_skel_call_1_conds dfs_aux_state; invar_1 dfs_aux_state⟧ ⟹ invar_1 (aux.DFS_skel_upd1 dfs_aux_state)"
  by (auto simp: upd1_unfold elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_1_holds_upd2[invar_holds_intros]:
  "⟦aux.DFS_skel_call_2_conds dfs_aux_state; invar_1 dfs_aux_state⟧ ⟹ invar_1 (aux.DFS_skel_upd2 dfs_aux_state)"
  by (auto simp: upd2_unfold elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_1_holds_ret_1[invar_holds_intros]:
  "⟦aux.DFS_skel_ret_1_conds dfs_aux_state; invar_1 dfs_aux_state⟧ ⟹ invar_1 (aux.DFS_skel_ret1 dfs_aux_state)"
  by (auto simp: aux.DFS_skel_ret1_def aux_on_empty_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_1_holds_ret_2[invar_holds_intros]:
  "⟦aux.DFS_skel_ret_2_conds dfs_aux_state; invar_1 dfs_aux_state⟧ ⟹ invar_1 (aux.DFS_skel_ret2 dfs_aux_state)"
  by (auto simp: aux.DFS_skel_ret2_def aux_on_found_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_1_holds[invar_holds_intros]:
   assumes "aux.DFS_skel_dom dfs_aux_state" "invar_1 dfs_aux_state"
   shows "invar_1 (aux.DFS_skel dfs_aux_state)"
  using assms(2)
proof(induction rule: aux.DFS_skel_induct[OF assms(1)])
  case IH: (1 dfs_aux_state)
  show ?case
    apply(rule aux.DFS_skel_cases[where dfs_state = dfs_aux_state])
    by (auto intro!: IH(2-4) invar_holds_intros simp: aux.DFS_skel_simps[OF IH(1)])
qed

subsection ‹invar_2: the reversed stack is a walk›

lemma invar_2_props[invar_props_elims]:
  "invar_2 dfs_aux_state ⟹
     (⟦Vwalk.vwalk (Graph.digraph_abs G) (rev (stack dfs_aux_state))⟧ ⟹ P) ⟹ P"
  by (auto simp: invar_2_def)

lemma invar_2_intro[invar_props_intros]:
  "⟦Vwalk.vwalk (Graph.digraph_abs G) (rev (stack dfs_aux_state))⟧ ⟹ invar_2 dfs_aux_state"
  by (auto simp: invar_2_def)

lemma invar_2_holds_upd1[invar_holds_intros]:
  assumes "aux.DFS_skel_call_1_conds dfs_aux_state" "invar_1 dfs_aux_state" "invar_2 dfs_aux_state"
  shows "invar_2 (aux.DFS_skel_upd1 dfs_aux_state)"
    using assms graph_inv
    by (force simp: Let_def aux.DFS_skel_upd1_def elim!: call_cond_elims elim!: invar_props_elims
         intro!: Vwalk.vwalk_append2 invar_props_intros)

lemma invar_2_holds_upd2[invar_holds_intros]:
  "⟦aux.DFS_skel_call_2_conds dfs_aux_state; invar_2 dfs_aux_state⟧ ⟹ invar_2 (aux.DFS_skel_upd2 dfs_aux_state)"
  by (auto simp: upd2_unfold dest!: append_vwalk_pref elim!: invar_props_elims
           intro!: invar_props_intros elim: call_cond_elims)

lemma invar_2_holds_ret_1[invar_holds_intros]:
  "⟦aux.DFS_skel_ret_1_conds dfs_aux_state; invar_2 dfs_aux_state⟧ ⟹ invar_2 (aux.DFS_skel_ret1 dfs_aux_state)"
  by (auto simp: aux.DFS_skel_ret1_def aux_on_empty_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_2_holds_ret_2[invar_holds_intros]:
  "⟦aux.DFS_skel_ret_2_conds dfs_aux_state; invar_2 dfs_aux_state⟧ ⟹ invar_2 (aux.DFS_skel_ret2 dfs_aux_state)"
  by (auto simp: aux.DFS_skel_ret2_def aux_on_found_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_2_holds[invar_holds_intros]:
   assumes "aux.DFS_skel_dom dfs_aux_state" "invar_1 dfs_aux_state" "invar_2 dfs_aux_state"
   shows "invar_2 (aux.DFS_skel dfs_aux_state)"
  using assms(2-)
proof(induction rule: aux.DFS_skel_induct[OF assms(1)])
  case IH: (1 dfs_aux_state)
  show ?case
    apply(rule aux.DFS_skel_cases[where dfs_state = dfs_aux_state])
    by (auto intro!: IH(2-5) invar_holds_intros simp: aux.DFS_skel_simps[OF IH(1)])
qed

subsection ‹invar_s_in_stack: the deepest stack entry is s›

lemma invar_s_in_stack_props[invar_props_elims]:
  "invar_s_in_stack dfs_aux_state ⟹
     (⟦(stack (dfs_aux_state) ≠ [] ⟹ last (stack dfs_aux_state) = s)⟧ ⟹ P) ⟹ P"
  by (auto simp: invar_s_in_stack_def)

lemma invar_s_in_stack_intro[invar_props_intros]:
  "⟦(stack (dfs_aux_state) ≠ [] ⟹ last (stack dfs_aux_state) = s)⟧ ⟹ invar_s_in_stack dfs_aux_state"
  by (auto simp: invar_s_in_stack_def)

lemma invar_s_in_stack_holds_upd1[invar_holds_intros]:
  "⟦aux.DFS_skel_call_1_conds dfs_aux_state; invar_s_in_stack dfs_aux_state⟧ ⟹
  invar_s_in_stack (aux.DFS_skel_upd1 dfs_aux_state)"
  by (force simp: Let_def aux.DFS_skel_upd1_def dest!: append_vwalk_pref elim!: call_cond_elims
            elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_s_in_stack_holds_upd2[invar_holds_intros]:
  "⟦aux.DFS_skel_call_2_conds dfs_aux_state; invar_s_in_stack dfs_aux_state⟧ ⟹
  invar_s_in_stack (aux.DFS_skel_upd2 dfs_aux_state)"
  by (auto simp: upd2_unfold dest!: append_vwalk_pref elim!: invar_props_elims intro!: invar_props_intros elim: call_cond_elims)

lemma invar_s_in_stack_holds_ret_1[invar_holds_intros]:
  "⟦aux.DFS_skel_ret_1_conds dfs_aux_state; invar_s_in_stack dfs_aux_state⟧ ⟹
  invar_s_in_stack (aux.DFS_skel_ret1 dfs_aux_state)"
  by (auto simp: aux.DFS_skel_ret1_def aux_on_empty_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_s_in_stack_holds_ret_2[invar_holds_intros]:
  "⟦aux.DFS_skel_ret_2_conds dfs_aux_state; invar_s_in_stack dfs_aux_state⟧ ⟹
  invar_s_in_stack (aux.DFS_skel_ret2 dfs_aux_state)"
  by (auto simp: aux.DFS_skel_ret2_def aux_on_found_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_s_in_stack_holds[invar_holds_intros]:
   assumes "aux.DFS_skel_dom dfs_aux_state" "invar_1 dfs_aux_state" "invar_s_in_stack dfs_aux_state"
   shows "invar_s_in_stack (aux.DFS_skel dfs_aux_state)"
  using assms(2-)
proof(induction rule: aux.DFS_skel_induct[OF assms(1)])
  case IH: (1 dfs_aux_state)
  show ?case
    apply(rule aux.DFS_skel_cases[where dfs_state = dfs_aux_state])
    by (auto intro!: IH(2-5) invar_holds_intros simp: aux.DFS_skel_simps[OF IH(1)])
qed

subsection ‹invar_seen_stack_finished›

lemma invar_seen_stack_finished_props[invar_props_elims]:
  "invar_seen_stack_finished dfs_aux_state ⟹
     (⟦distinct (stack dfs_aux_state); set (stack dfs_aux_state) ⊆ t_set (seen dfs_aux_state);
      t_set (finished dfs_aux_state) ⊆ t_set (seen dfs_aux_state);
      t_set (finished dfs_aux_state) = t_set (seen dfs_aux_state) - set (stack dfs_aux_state);
      t_set (seen dfs_aux_state) ⊆ dVs (Graph.digraph_abs G)⟧ ⟹ P) ⟹ P"
  by (auto simp: invar_seen_stack_finished_def)

lemma invar_seen_stack_finished_intro[invar_props_intros]:
  "⟦distinct (stack dfs_aux_state); set (stack dfs_aux_state) ⊆ t_set (seen dfs_aux_state);
      t_set (finished dfs_aux_state) ⊆ t_set (seen dfs_aux_state);
      t_set (finished dfs_aux_state) = t_set (seen dfs_aux_state) - set (stack dfs_aux_state);
      t_set (seen dfs_aux_state) ⊆ dVs (Graph.digraph_abs G)⟧ ⟹ invar_seen_stack_finished dfs_aux_state"
  by (auto simp: invar_seen_stack_finished_def)

lemma invar_seen_stack_finished_holds_upd1[invar_holds_intros]:
  "⟦aux.DFS_skel_call_1_conds dfs_aux_state; invar_1 dfs_aux_state; invar_seen_stack_finished dfs_aux_state⟧ ⟹
    invar_seen_stack_finished (aux.DFS_skel_upd1 dfs_aux_state)"
proof (intro invar_props_intros, goal_cases)
  case 1
  let ?v = "hd (stack dfs_aux_state)"
  let ?w = "sel ((𝒩⇩G ?v) -⇩G (seen dfs_aux_state))"
  have "?w ∈ t_set (𝒩⇩G ?v) - t_set (seen dfs_aux_state)"
    using ‹invar_1 dfs_aux_state› ‹aux.DFS_skel_call_1_conds dfs_aux_state›
    by (auto elim!: invar_props_elims call_cond_elims)
  then have "?w ∉ set (stack dfs_aux_state)"
    using ‹invar_seen_stack_finished dfs_aux_state›
    by (auto elim!: invar_props_elims)
  moreover have "(stack (aux.DFS_skel_upd1 dfs_aux_state)) = ?w # stack dfs_aux_state"
    by (auto simp add: upd1_unfold)
  ultimately show ?case
    using ‹invar_seen_stack_finished dfs_aux_state›
    by (auto simp: upd1_unfold elim!: invar_props_elims)
next
  case 2
  then show ?case
    by (auto simp: upd1_unfold elim!: call_cond_elims elim!: invar_props_elims intro!: invar_props_intros)
next
  case 3
  then show ?case
    by (auto simp: upd1_unfold elim!: call_cond_elims elim!: invar_props_elims intro!: invar_props_intros)
next
  case 4
  let ?v = "hd (stack dfs_aux_state)"
  let ?w = "sel ((𝒩⇩G ?v) -⇩G (seen dfs_aux_state))"
  have "set (stack (aux.DFS_skel_upd1 dfs_aux_state)) = {?w} ∪ set (stack dfs_aux_state)"
    by (auto simp add: upd1_unfold)
  moreover have "t_set (seen (aux.DFS_skel_upd1 dfs_aux_state)) = {?w} ∪ t_set (seen dfs_aux_state)"
    using ‹invar_1 dfs_aux_state›
    by (auto simp add: upd1_unfold elim!: invar_props_elims)
  moreover have "?w ∈ t_set (𝒩⇩G ?v) - t_set (seen dfs_aux_state)"
    using ‹invar_1 dfs_aux_state› ‹aux.DFS_skel_call_1_conds dfs_aux_state›
    by (auto elim!: invar_props_elims call_cond_elims)
  ultimately show ?case
    using ‹invar_seen_stack_finished dfs_aux_state›
    by (auto simp add: upd1_unfold elim!: invar_props_elims)
next
  case 5
  let ?v = "hd (stack dfs_aux_state)"
  let ?w = "sel ((𝒩⇩G ?v) -⇩G (seen dfs_aux_state))"
  have "?w ∈ t_set (𝒩⇩G ?v) - t_set (seen dfs_aux_state)"
    using ‹invar_1 dfs_aux_state› ‹aux.DFS_skel_call_1_conds dfs_aux_state›
    by (auto elim!: invar_props_elims call_cond_elims)
  then have "?w ∈ dVs (Graph.digraph_abs G)"
    by blast
  moreover have "t_set (seen (aux.DFS_skel_upd1 dfs_aux_state)) = {?w} ∪ t_set (seen dfs_aux_state)"
    using ‹invar_1 dfs_aux_state›
    by (auto simp add: upd1_unfold elim!: invar_props_elims)
  ultimately show ?case
    using ‹invar_seen_stack_finished dfs_aux_state›
    by (auto simp add: upd1_unfold elim!: invar_props_elims)
qed

lemma invar_seen_stack_finished_holds_upd2[invar_holds_intros]:
  "⟦aux.DFS_skel_call_2_conds dfs_aux_state; invar_1 dfs_aux_state; invar_seen_stack_finished dfs_aux_state⟧ ⟹
    invar_seen_stack_finished (aux.DFS_skel_upd2 dfs_aux_state)"
  by (force simp: upd2_unfold elim!: call_cond_elims
            elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_seen_stack_finished_holds_ret_1[invar_holds_intros]:
  "⟦aux.DFS_skel_ret_1_conds dfs_aux_state; invar_seen_stack_finished dfs_aux_state⟧ ⟹
    invar_seen_stack_finished (aux.DFS_skel_ret1 dfs_aux_state)"
  by (force simp: aux.DFS_skel_ret1_def aux_on_empty_def elim!: call_cond_elims
            elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_seen_stack_finished_holds_ret_2[invar_holds_intros]:
  "⟦aux.DFS_skel_ret_2_conds dfs_aux_state; invar_seen_stack_finished dfs_aux_state⟧ ⟹
    invar_seen_stack_finished (aux.DFS_skel_ret2 dfs_aux_state)"
  by (force simp: aux.DFS_skel_ret2_def aux_on_found_def elim!: call_cond_elims
            elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_seen_stack_finished_holds[invar_holds_intros]:
   assumes "aux.DFS_skel_dom dfs_aux_state" "invar_1 dfs_aux_state" "invar_seen_stack_finished dfs_aux_state"
   shows "invar_seen_stack_finished (aux.DFS_skel dfs_aux_state)"
  using assms(2-)
proof(induction rule: aux.DFS_skel_induct[OF assms(1)])
  case IH: (1 dfs_aux_state)
  show ?case
    apply(rule aux.DFS_skel_cases[where dfs_state = dfs_aux_state])
    by (auto intro!: IH(2-5) invar_holds_intros simp: aux.DFS_skel_simps[OF IH(1)])
qed

subsection ‹invar_finished_vsets: finished vertices have all neighbours seen›

lemma invar_finished_vsets_props[invar_props_elims]:
  "invar_finished_vsets dfs_aux_state ⟹
     (⟦⋀v. v ∈ t_set (finished (dfs_aux_state)) ⟹ t_set (𝒩⇩G v) ⊆ t_set (seen (dfs_aux_state))⟧ ⟹ P) ⟹ P"
  by (auto simp: invar_finished_vsets_def)

lemma invar_finished_vsets_intro[invar_props_intros]:
  "⟦⋀v. v ∈ t_set (finished (dfs_aux_state)) ⟹ t_set (𝒩⇩G v) ⊆ t_set (seen (dfs_aux_state))⟧ ⟹
    invar_finished_vsets dfs_aux_state"
  by (auto simp: invar_finished_vsets_def)

lemma invar_finished_vsets_holds_upd1[invar_holds_intros]:
  "⟦aux.DFS_skel_call_1_conds dfs_aux_state; invar_1 dfs_aux_state; invar_finished_vsets dfs_aux_state⟧ ⟹
    invar_finished_vsets (aux.DFS_skel_upd1 dfs_aux_state)"
  by (force simp: upd1_unfold elim!: call_cond_elims
            elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_finished_vsets_holds_upd2[invar_holds_intros]:
  "⟦aux.DFS_skel_call_2_conds dfs_aux_state; invar_1 dfs_aux_state; invar_finished_vsets dfs_aux_state⟧ ⟹
    invar_finished_vsets (aux.DFS_skel_upd2 dfs_aux_state)"
proof (intro invar_props_intros, goal_cases)
  case (1 v)
  let ?v = "hd (stack dfs_aux_state)"
  have finexpr: "t_set (finished (aux.DFS_skel_upd2 dfs_aux_state)) = {?v} ∪ t_set (finished dfs_aux_state)"
    using ‹invar_1 dfs_aux_state›
    by (auto simp add: upd2_unfold elim!: invar_props_elims)
  have vnbrs: "t_set (𝒩⇩G ?v) ⊆ t_set (seen (dfs_aux_state))"
  proof -
    have empty: "((𝒩⇩G ?v) -⇩G (seen dfs_aux_state)) = ∅⇩N"
      using call_2_excl(3)[OF ‹aux.DFS_skel_call_2_conds dfs_aux_state›] by simp
    have "t_set (𝒩⇩G ?v) - t_set (seen dfs_aux_state) = t_set ((𝒩⇩G ?v) -⇩G (seen dfs_aux_state))"
      using ‹invar_1 dfs_aux_state› by (auto elim!: invar_props_elims)
    with empty show ?thesis by auto
  qed
  have seenexpr: "t_set (seen (aux.DFS_skel_upd2 dfs_aux_state)) = t_set (seen dfs_aux_state)"
    by (auto simp add: upd2_unfold)
  show ?case
    using ‹invar_finished_vsets dfs_aux_state› ‹v ∈ t_set (finished (aux.DFS_skel_upd2 dfs_aux_state))›
          finexpr vnbrs seenexpr
    by (force elim!: invar_props_elims)
qed

lemma invar_finished_vsets_holds_ret_1[invar_holds_intros]:
  "⟦aux.DFS_skel_ret_1_conds dfs_aux_state; invar_finished_vsets dfs_aux_state⟧ ⟹
    invar_finished_vsets (aux.DFS_skel_ret1 dfs_aux_state)"
  by (force simp: aux.DFS_skel_ret1_def aux_on_empty_def elim!: call_cond_elims
            elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_finished_vsets_holds_ret_2[invar_holds_intros]:
  "⟦aux.DFS_skel_ret_2_conds dfs_aux_state; invar_finished_vsets dfs_aux_state⟧ ⟹
    invar_finished_vsets (aux.DFS_skel_ret2 dfs_aux_state)"
  by (force simp: aux.DFS_skel_ret2_def aux_on_found_def elim!: call_cond_elims
            elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_finished_vsets_holds[invar_holds_intros]:
   assumes "aux.DFS_skel_dom dfs_aux_state" "invar_1 dfs_aux_state" "invar_finished_vsets dfs_aux_state"
   shows "invar_finished_vsets (aux.DFS_skel dfs_aux_state)"
  using assms(2-)
proof(induction rule: aux.DFS_skel_induct[OF assms(1)])
  case IH: (1 dfs_aux_state)
  show ?case
    apply(rule aux.DFS_skel_cases[where dfs_state = dfs_aux_state])
    by (auto intro!: IH(2-5) invar_holds_intros simp: aux.DFS_skel_simps[OF IH(1)])
qed

subsection ‹The DFS tree grows correctly: invar_dfs_tree_seen_1 and invar_dfs_tree_seen_2›

text ‹A shared fact used in the backtrack (upd2) tree-shape proofs: when the stack tail is nonempty,
the second stack entry is a genuine (symmetric) edge, and the current vertex's non-parent neighbours
are all finished. This is derived inside each case from that case's own premises.›

lemma invar_dfs_tree_seen_2_props[invar_props_elims]:
  "invar_dfs_tree_seen_2 dfs_aux_state ⟹
     (⟦(dfs_tree dfs_aux_state) ≠ {} ⟹ dVs (dfs_tree dfs_aux_state) = t_set (seen dfs_aux_state)⟧ ⟹ P) ⟹ P"
  by (auto simp: invar_dfs_tree_seen_2_def)

lemma invar_dfs_tree_seen_2_intro[invar_props_intros]:
  "⟦(dfs_tree dfs_aux_state) ≠ {} ⟹ dVs (dfs_tree dfs_aux_state) = t_set (seen dfs_aux_state)⟧ ⟹ invar_dfs_tree_seen_2 dfs_aux_state"
  by (auto simp: invar_dfs_tree_seen_2_def)

lemma invar_dfs_tree_seen_1_props[invar_props_elims]:
  "invar_dfs_tree_seen_1 dfs_aux_state ⟹
     (⟦(dfs_tree dfs_aux_state) = {} ⟹ t_set (seen dfs_aux_state) = {s}⟧ ⟹ P) ⟹ P"
  by (auto simp: invar_dfs_tree_seen_1_def)

lemma invar_dfs_tree_seen_1_intro[invar_props_intros]:
  "⟦(dfs_tree dfs_aux_state) = {} ⟹ t_set (seen dfs_aux_state) = {s}⟧ ⟹
    invar_dfs_tree_seen_1 dfs_aux_state"
  by (auto simp: invar_dfs_tree_seen_1_def)

lemma invar_dfs_tree_seen_1_holds_upd1[invar_holds_intros]:
  "⟦aux.DFS_skel_call_1_conds dfs_aux_state; invar_1 dfs_aux_state; invar_seen_stack_finished dfs_aux_state;
    invar_finished_vsets dfs_aux_state; invar_dfs_tree_seen_1 dfs_aux_state⟧ ⟹
    invar_dfs_tree_seen_1 (aux.DFS_skel_upd1 dfs_aux_state)"
proof (intro invar_props_intros, goal_cases)
  case 1
  let ?v = "hd (stack dfs_aux_state)"
  let ?w = "sel ((𝒩⇩G ?v) -⇩G (seen dfs_aux_state))"

  have stack_expr: "(stack dfs_aux_state) = hd (stack dfs_aux_state) # tl (stack dfs_aux_state)"
    using ‹aux.DFS_skel_call_1_conds dfs_aux_state›
    by (auto elim!: call_cond_elims)
  have w_not_in_seen: "?w ∉ set (stack dfs_aux_state) ∪ t_set (finished dfs_aux_state)"
    using ‹invar_1 dfs_aux_state› ‹invar_seen_stack_finished dfs_aux_state› ‹aux.DFS_skel_call_1_conds dfs_aux_state›
    by (force elim!: invar_props_elims call_cond_elims)
  have finished_vsets: "∀(x, y) ∈ (Graph.digraph_abs G).
    (x ∈ t_set (finished dfs_aux_state) ⟶ y ∈ set (stack dfs_aux_state) ∪ t_set (finished dfs_aux_state)) ∧
    (y ∈ t_set (finished dfs_aux_state) ⟶ x ∈ set (stack dfs_aux_state) ∪ t_set (finished dfs_aux_state))"
    using ‹invar_seen_stack_finished dfs_aux_state› ‹invar_finished_vsets dfs_aux_state›
    graph_symmetric Graph.digraph_abs_def
    by (fastforce elim!: invar_props_elims)
  from dfs_tree_aux1[OF stack_expr w_not_in_seen finished_vsets]
    have dfs_tree_expr:
    "dfs_tree (aux.DFS_skel_upd1 dfs_aux_state) =
    {(?v, ?w), (?w, ?v)} ∪ dfs_tree dfs_aux_state"
    unfolding dfs_tree_def by (auto simp add: upd1_unfold)
  with ‹dfs_tree (aux.DFS_skel_upd1 dfs_aux_state) = {}› show ?case by blast
qed

text ‹Common backtrack-tree computation ‹dfs_tree (upd2 st) = dfs_tree st›, used by the tree-seen
and cycle-false backtrack proofs. Re-derived from each caller's own premises.›
lemma dfs_tree_upd2_eq:
  assumes "aux.DFS_skel_call_2_conds dfs_aux_state" "invar_1 dfs_aux_state" "invar_2 dfs_aux_state"
    "invar_seen_stack_finished dfs_aux_state"
  shows "dfs_tree (aux.DFS_skel_upd2 dfs_aux_state) = dfs_tree dfs_aux_state"
proof (cases "tl (stack dfs_aux_state)")
  case Nil
  let ?v = "hd (stack dfs_aux_state)"
  have stack_expr: "stack dfs_aux_state = ?v # (tl (stack dfs_aux_state))"
    using ‹aux.DFS_skel_call_2_conds dfs_aux_state›
    by (force elim!: call_cond_elims)
  from graph_no_self_loops2 have noloop: "∀(x, y) ∈ (Graph.digraph_abs G). x ≠ y" by blast
  have stack_upd_expr: "stack (aux.DFS_skel_upd2 dfs_aux_state) = tl (stack dfs_aux_state)"
    by (auto simp add: upd2_unfold)
  have finished_upd_expr:
    "t_set (finished (aux.DFS_skel_upd2 dfs_aux_state)) = Set.insert (hd (stack dfs_aux_state)) (t_set (finished dfs_aux_state))"
    using ‹invar_1 dfs_aux_state›
    by (auto simp add: upd2_unfold elim!: invar_props_elims)
  show ?thesis
    unfolding dfs_tree_def stack_upd_expr finished_upd_expr
    using dfs_tree_aux2_1[of "stack dfs_aux_state" "?v" "tl (stack dfs_aux_state)"
      "Graph.digraph_abs G" "t_set (finished dfs_aux_state)", OF stack_expr Nil noloop]
    by blast
next
  case (Cons u l_tl_tl)
  let ?v = "hd (stack dfs_aux_state)"
  have stack_expr: "stack dfs_aux_state = ?v # (tl (stack dfs_aux_state))"
    using ‹aux.DFS_skel_call_2_conds dfs_aux_state›
    by (force elim!: call_cond_elims)
  from graph_no_self_loops2 have noloop: "∀(x, y) ∈ (Graph.digraph_abs G). x ≠ y" by blast

  have vw_rev: "Vwalk.vwalk (Graph.digraph_abs G) (rev (stack dfs_aux_state))"
    using ‹invar_2 dfs_aux_state› by (force elim!: invar_props_elims)
  have sym: "∀(x, y) ∈ (Graph.digraph_abs G). (y, x) ∈ (Graph.digraph_abs G)"
    using graph_symmetric by auto
  have vw_stack: "Vwalk.vwalk (Graph.digraph_abs G) (stack dfs_aux_state)"
    using vwalk_rev[OF sym vw_rev] by simp
  have stk_form: "stack dfs_aux_state = ?v # u # l_tl_tl"
    using stack_expr by (simp only: Cons)
  have vw_stack2: "Vwalk.vwalk (Graph.digraph_abs G) (?v # u # l_tl_tl)"
    by (subst stk_form[symmetric], rule vw_stack)
  have "(?v, u) ∈ (Graph.digraph_abs G)"
    by (rule Vwalk.vwalk_cons[OF vw_stack2])
  then have edges_in_G: "{(u, ?v), (?v, u)} ⊆ (Graph.digraph_abs G)" by auto

  have ssf: "set (stack dfs_aux_state) ⊆ t_set (seen dfs_aux_state)"
    "t_set (finished dfs_aux_state) ⊆ t_set (seen dfs_aux_state)"
    "t_set (finished dfs_aux_state) = t_set (seen dfs_aux_state) - set (stack dfs_aux_state)"
    using ‹invar_seen_stack_finished dfs_aux_state› stack_expr
    by (auto elim!: invar_props_elims)
  then have sets_disjoint: "set (tl (stack dfs_aux_state)) ∩ t_set (finished dfs_aux_state) = {}"
    using Vwalk.list_set_tl by fastforce

  have empty_inter: "((𝒩⇩G ?v) -⇩G (case (tl (stack dfs_aux_state)) of [] ⇒ ∅⇩N | u # _ ⇒ insert u ∅⇩N))
       ∩⇩G (seen dfs_aux_state -⇩G finished dfs_aux_state) = ∅⇩N"
    using call_2_excl(2)[OF ‹aux.DFS_skel_call_2_conds dfs_aux_state›] .
  have nbr_diff_u: "t_set ((𝒩⇩G ?v) -⇩G (insert u ∅⇩N)) = t_set (𝒩⇩G ?v) - {u}"
    using ‹invar_1 dfs_aux_state› by (auto elim!: invar_props_elims)
  have seen_diff_fin: "t_set (seen dfs_aux_state -⇩G finished dfs_aux_state) = t_set (seen dfs_aux_state) - t_set (finished dfs_aux_state)"
    using ‹invar_1 dfs_aux_state› by (auto elim!: invar_props_elims)
  have inter_empty: "t_set ((𝒩⇩G ?v) -⇩G (insert u ∅⇩N)) ∩ t_set (seen dfs_aux_state -⇩G finished dfs_aux_state) = {}"
    using empty_inter Cons ‹invar_1 dfs_aux_state›
    by (fastforce elim!: invar_props_elims)
  then have "(t_set (𝒩⇩G ?v) - {u}) ∩ (t_set (seen dfs_aux_state) - t_set (finished dfs_aux_state)) = {}"
    using nbr_diff_u seen_diff_fin by simp
  moreover have "(t_set (𝒩⇩G ?v) - t_set (seen dfs_aux_state)) = {}"
    using call_2_excl(3)[OF ‹aux.DFS_skel_call_2_conds dfs_aux_state›] ‹invar_1 dfs_aux_state›
    by (force elim!: invar_props_elims)
  ultimately have "(t_set (𝒩⇩G ?v) - {u}) ⊆ t_set (finished dfs_aux_state)" by blast
  with graph_symmetric
    have v_vsets: "∀(x, y) ∈ (Graph.digraph_abs G).
      (x = ?v ⟶ y ≠ u ⟶ y ∈ t_set (finished dfs_aux_state)) ∧
      (y = ?v ⟶ x ≠ u ⟶ x ∈ t_set (finished dfs_aux_state))"
    by blast

  have stack_upd_expr: "stack (aux.DFS_skel_upd2 dfs_aux_state) = tl (stack dfs_aux_state)"
    by (auto simp add: upd2_unfold)
  have finished_upd_expr:
    "t_set (finished (aux.DFS_skel_upd2 dfs_aux_state)) = Set.insert (hd (stack dfs_aux_state)) (t_set (finished dfs_aux_state))"
    using ‹invar_1 dfs_aux_state›
    by (auto simp add: upd2_unfold elim!: invar_props_elims)

  show ?thesis
    unfolding dfs_tree_def stack_upd_expr finished_upd_expr
    using dfs_tree_aux2_2[OF stack_expr Cons noloop edges_in_G sets_disjoint v_vsets]
    by auto
qed

lemma invar_dfs_tree_seen_1_holds_upd2[invar_holds_intros]:
  "⟦aux.DFS_skel_call_2_conds dfs_aux_state; invar_1 dfs_aux_state; invar_2 dfs_aux_state;
    invar_seen_stack_finished dfs_aux_state;
    invar_dfs_tree_seen_1 dfs_aux_state⟧ ⟹
    invar_dfs_tree_seen_1 (aux.DFS_skel_upd2 dfs_aux_state)"
proof (intro invar_props_intros, goal_cases)
  case 1
  have dfs_tree_expr: "dfs_tree (aux.DFS_skel_upd2 dfs_aux_state) = dfs_tree dfs_aux_state"
    using dfs_tree_upd2_eq[OF 1(1-4)] .
  have seen_expr: "t_set (seen (aux.DFS_skel_upd2 dfs_aux_state)) = t_set (seen (dfs_aux_state))"
    by (auto simp add: upd2_unfold)
  with dfs_tree_expr ‹dfs_tree (aux.DFS_skel_upd2 dfs_aux_state) = {}› show ?case
    using ‹invar_dfs_tree_seen_1 dfs_aux_state›
    by (force elim!: invar_props_elims)
qed

lemma invar_dfs_tree_seen_1_holds_ret_1[invar_holds_intros]:
  "⟦aux.DFS_skel_ret_1_conds dfs_aux_state; invar_dfs_tree_seen_1 dfs_aux_state⟧ ⟹
    invar_dfs_tree_seen_1 (aux.DFS_skel_ret1 dfs_aux_state)"
proof (intro invar_props_intros, goal_cases)
  case 1
  have "dfs_tree (aux.DFS_skel_ret1 dfs_aux_state) = dfs_tree dfs_aux_state"
    unfolding dfs_tree_def by (auto simp add: aux.DFS_skel_ret1_def aux_on_empty_def)
  with ‹dfs_tree (aux.DFS_skel_ret1 dfs_aux_state) = {}› ‹invar_dfs_tree_seen_1 dfs_aux_state›
    have "t_set (seen dfs_aux_state) = {s}"
    by (force elim!: invar_props_elims)
  then show ?case
    by (auto simp add: aux.DFS_skel_ret1_def aux_on_empty_def)
qed

lemma invar_dfs_tree_seen_1_holds_ret_2[invar_holds_intros]:
  "⟦aux.DFS_skel_ret_2_conds dfs_aux_state; invar_dfs_tree_seen_1 dfs_aux_state⟧ ⟹
    invar_dfs_tree_seen_1 (aux.DFS_skel_ret2 dfs_aux_state)"
proof (intro invar_props_intros, goal_cases)
  case 1
  have tree_eq: "dfs_tree (aux.DFS_skel_ret2 dfs_aux_state) = dfs_tree dfs_aux_state"
    unfolding dfs_tree_def by (auto simp add: aux.DFS_skel_ret2_def aux_on_found_def)
  with ‹dfs_tree (aux.DFS_skel_ret2 dfs_aux_state) = {}› ‹invar_dfs_tree_seen_1 dfs_aux_state›
    have "t_set (seen dfs_aux_state) = {s}"
    by (force elim!: invar_props_elims)
  then show ?case
    by (auto simp add: aux.DFS_skel_ret2_def aux_on_found_def)
qed

lemma invar_dfs_tree_seen_1_holds[invar_holds_intros]:
   assumes "aux.DFS_skel_dom dfs_aux_state" "invar_1 dfs_aux_state" "invar_2 dfs_aux_state"
     "invar_seen_stack_finished dfs_aux_state" "invar_finished_vsets dfs_aux_state"
     "invar_dfs_tree_seen_1 dfs_aux_state"
   shows "invar_dfs_tree_seen_1 (aux.DFS_skel dfs_aux_state)"
  using assms(2-)
proof(induction rule: aux.DFS_skel_induct[OF assms(1)])
  case IH: (1 dfs_aux_state)
  show ?case
    apply(rule aux.DFS_skel_cases[where dfs_state = dfs_aux_state])
    by (auto intro!: IH(2-8) invar_holds_intros simp: aux.DFS_skel_simps[OF IH(1)])
qed

lemma invar_dfs_tree_seen_2_holds_upd1[invar_holds_intros]:
  "⟦aux.DFS_skel_call_1_conds dfs_aux_state; invar_1 dfs_aux_state; invar_seen_stack_finished dfs_aux_state;
    invar_finished_vsets dfs_aux_state; invar_dfs_tree_seen_1 dfs_aux_state; invar_dfs_tree_seen_2 dfs_aux_state⟧ ⟹
    invar_dfs_tree_seen_2 (aux.DFS_skel_upd1 dfs_aux_state)"
proof (intro invar_props_intros, goal_cases)
  case 1
  let ?v = "hd (stack dfs_aux_state)"
  let ?w = "sel ((𝒩⇩G ?v) -⇩G (seen dfs_aux_state))"

  have stack_expr: "(stack dfs_aux_state) = hd (stack dfs_aux_state) # tl (stack dfs_aux_state)"
    using ‹aux.DFS_skel_call_1_conds dfs_aux_state› by (auto elim!: call_cond_elims)
  have w_not_in_seen: "?w ∉ set (stack dfs_aux_state) ∪ t_set (finished dfs_aux_state)"
    using ‹invar_1 dfs_aux_state› ‹invar_seen_stack_finished dfs_aux_state› ‹aux.DFS_skel_call_1_conds dfs_aux_state›
    by (force elim!: invar_props_elims call_cond_elims)
  have finished_vsets: "∀(x, y) ∈ (Graph.digraph_abs G).
    (x ∈ t_set (finished dfs_aux_state) ⟶ y ∈ set (stack dfs_aux_state) ∪ t_set (finished dfs_aux_state)) ∧
    (y ∈ t_set (finished dfs_aux_state) ⟶ x ∈ set (stack dfs_aux_state) ∪ t_set (finished dfs_aux_state))"
    using ‹invar_seen_stack_finished dfs_aux_state› ‹invar_finished_vsets dfs_aux_state›
    graph_symmetric Graph.digraph_abs_def
    by (fastforce elim!: invar_props_elims)
  from dfs_tree_aux1[OF stack_expr w_not_in_seen finished_vsets]
    have dfs_tree_expr:
    "dfs_tree (aux.DFS_skel_upd1 dfs_aux_state) =
    {(?v, ?w), (?w, ?v)} ∪ dfs_tree dfs_aux_state"
    unfolding dfs_tree_def by (auto simp add: upd1_unfold)

  have seen_expr: "t_set (seen (aux.DFS_skel_upd1 dfs_aux_state)) = t_set (seen (dfs_aux_state)) ∪ {?w}"
    using ‹invar_1 dfs_aux_state›
    by (auto simp add: upd1_unfold elim!: invar_props_elims)

  show ?case
  proof (cases "dfs_tree dfs_aux_state = {}")
    case True
    from True have "edges_of_vwalk (stack dfs_aux_state) = []"
      unfolding dfs_tree_def by blast
    then have stack_single: "(stack dfs_aux_state) = [?v]"
      using ‹aux.DFS_skel_call_1_conds dfs_aux_state› edges_of_vwalk.elims
      by (force elim!: call_cond_elims)
    from True dfs_tree_expr
      have tree_two: "dfs_tree (aux.DFS_skel_upd1 dfs_aux_state) = {(?v, ?w), (?w, ?v)}"
      by simp
    from True have "t_set (seen (dfs_aux_state)) = {s}"
      using ‹invar_dfs_tree_seen_1 dfs_aux_state› by (fastforce elim!: invar_props_elims)
    have s_eq_v: "s = ?v"
    proof -
      have "set (stack dfs_aux_state) ⊆ t_set (seen dfs_aux_state)"
        using ‹invar_seen_stack_finished dfs_aux_state› by (auto elim!: invar_props_elims)
      have hd_in: "hd (stack dfs_aux_state) ∈ t_set (seen dfs_aux_state)"
      proof -
        have "hd (stack dfs_aux_state) ∈ set (stack dfs_aux_state)"
          by (subst stack_single, simp)
        with ‹set (stack dfs_aux_state) ⊆ t_set (seen dfs_aux_state)› show ?thesis by auto
      qed
      with ‹t_set (seen (dfs_aux_state)) = {s}› show ?thesis by simp
    qed
    then have "t_set (seen (dfs_aux_state)) = {?v}"
      using ‹t_set (seen (dfs_aux_state)) = {s}› by simp
    with seen_expr
      have "t_set (seen (aux.DFS_skel_upd1 dfs_aux_state)) = {?v, ?w}" by auto
    with tree_two show ?thesis unfolding dVs_def by auto
  next
    case False
    have "?v ∈ dVs (dfs_tree dfs_aux_state)"
      using ‹invar_seen_stack_finished dfs_aux_state› False ‹invar_dfs_tree_seen_2 dfs_aux_state›
      ‹aux.DFS_skel_call_1_conds dfs_aux_state›
      by (force elim!: invar_props_elims call_cond_elims)
    have "?w ∉ dVs (dfs_tree dfs_aux_state)"
      using ‹invar_1 dfs_aux_state› ‹invar_dfs_tree_seen_2 dfs_aux_state› ‹aux.DFS_skel_call_1_conds dfs_aux_state›
      by (force elim!: invar_props_elims call_cond_elims)
    from ‹?v ∈ dVs (dfs_tree dfs_aux_state)› ‹?w ∉ dVs (dfs_tree dfs_aux_state)›
      have "dVs ({(?v, ?w), (?w, ?v)} ∪ dfs_tree dfs_aux_state) = dVs (dfs_tree dfs_aux_state) ∪ {?w}"
      unfolding dVs_def by blast
    with dfs_tree_expr
      have dVs_expr: "dVs (dfs_tree (aux.DFS_skel_upd1 dfs_aux_state)) = dVs (dfs_tree dfs_aux_state) ∪ {?w}"
      by simp
    from dVs_expr seen_expr False show ?thesis
      using ‹invar_dfs_tree_seen_2 dfs_aux_state›
      by (auto elim!: invar_props_elims)
  qed
qed

lemma invar_dfs_tree_seen_2_holds_upd2[invar_holds_intros]:
  "⟦aux.DFS_skel_call_2_conds dfs_aux_state; invar_1 dfs_aux_state; invar_2 dfs_aux_state;
    invar_seen_stack_finished dfs_aux_state; invar_dfs_tree_seen_2 dfs_aux_state⟧ ⟹
    invar_dfs_tree_seen_2 (aux.DFS_skel_upd2 dfs_aux_state)"
proof (intro invar_props_intros, goal_cases)
  case 1
  have dfs_tree_expr: "dfs_tree (aux.DFS_skel_upd2 dfs_aux_state) = dfs_tree dfs_aux_state"
    using dfs_tree_upd2_eq[OF 1(1-4)] .
  have seen_expr: "t_set (seen (aux.DFS_skel_upd2 dfs_aux_state)) = t_set (seen (dfs_aux_state))"
    by (auto simp add: upd2_unfold)
  from ‹dfs_tree (aux.DFS_skel_upd2 dfs_aux_state) ≠ {}› dfs_tree_expr seen_expr
    show ?case
    using ‹invar_dfs_tree_seen_2 dfs_aux_state›
    by (auto elim!: invar_props_elims)
qed

lemma invar_dfs_tree_seen_2_holds_ret_1[invar_holds_intros]:
  "⟦aux.DFS_skel_ret_1_conds dfs_aux_state; invar_dfs_tree_seen_2 dfs_aux_state⟧ ⟹
    invar_dfs_tree_seen_2 (aux.DFS_skel_ret1 dfs_aux_state)"
  unfolding invar_dfs_tree_seen_2_def aux.DFS_skel_ret1_def aux_on_empty_def dfs_tree_def by simp

lemma invar_dfs_tree_seen_2_holds_ret_2[invar_holds_intros]:
  "⟦aux.DFS_skel_ret_2_conds dfs_aux_state; invar_dfs_tree_seen_2 dfs_aux_state⟧ ⟹
    invar_dfs_tree_seen_2 (aux.DFS_skel_ret2 dfs_aux_state)"
  unfolding invar_dfs_tree_seen_2_def aux.DFS_skel_ret2_def aux_on_found_def dfs_tree_def by simp

lemma invar_dfs_tree_seen_2_holds[invar_holds_intros]:
   assumes "aux.DFS_skel_dom dfs_aux_state" "invar_1 dfs_aux_state" "invar_2 dfs_aux_state"
     "invar_seen_stack_finished dfs_aux_state" "invar_finished_vsets dfs_aux_state"
     "invar_dfs_tree_seen_1 dfs_aux_state" "invar_dfs_tree_seen_2 dfs_aux_state"
   shows "invar_dfs_tree_seen_2 (aux.DFS_skel dfs_aux_state)"
  using assms(2-)
proof(induction rule: aux.DFS_skel_induct[OF assms(1)])
  case IH: (1 dfs_aux_state)
  show ?case
    apply(rule aux.DFS_skel_cases[where dfs_state = dfs_aux_state])
    by (auto intro!: IH(2-9) invar_holds_intros simp: aux.DFS_skel_simps[OF IH(1)])
qed


subsection ‹Cycle-free invariant: invar_cycle_false›

lemma invar_cycle_false_props[invar_props_elims]:
  "invar_cycle_false dfs_aux_state ⟹
     (⟦(¬cycle dfs_aux_state) ⟹ (∄c. cycle' (dfs_tree dfs_aux_state) c)⟧ ⟹ P) ⟹ P"
  by (auto simp: invar_cycle_false_def)

lemma invar_cycle_false_intro[invar_props_intros]:
  "⟦(¬cycle dfs_aux_state) ⟹ (∄c. cycle' (dfs_tree dfs_aux_state) c)⟧ ⟹ invar_cycle_false dfs_aux_state"
  by (auto simp: invar_cycle_false_def)

lemma invar_cycle_false_holds_upd1[invar_holds_intros]:
  "⟦aux.DFS_skel_call_1_conds dfs_aux_state; invar_1 dfs_aux_state; invar_seen_stack_finished dfs_aux_state;
    invar_finished_vsets dfs_aux_state; invar_dfs_tree_seen_2 dfs_aux_state; invar_cycle_false dfs_aux_state⟧ ⟹
    invar_cycle_false (aux.DFS_skel_upd1 dfs_aux_state)"
proof (intro invar_props_intros, goal_cases)
  case 1
  let ?v = "hd (stack dfs_aux_state)"
  let ?w = "sel ((𝒩⇩G ?v) -⇩G (seen dfs_aux_state))"

  have vw_neq: "?v ≠ ?w"
    using ‹invar_1 dfs_aux_state› ‹invar_seen_stack_finished dfs_aux_state› ‹aux.DFS_skel_call_1_conds dfs_aux_state›
    by (force elim!: invar_props_elims call_cond_elims)
  have stack_expr: "stack dfs_aux_state = hd (stack dfs_aux_state) # tl (stack dfs_aux_state)"
    using ‹aux.DFS_skel_call_1_conds dfs_aux_state› by (auto elim!: call_cond_elims)
  have w_not_in_seen: "?w ∉ set (stack dfs_aux_state) ∪ t_set (finished dfs_aux_state)"
    using ‹invar_1 dfs_aux_state› ‹invar_seen_stack_finished dfs_aux_state› ‹aux.DFS_skel_call_1_conds dfs_aux_state›
    by (force elim!: invar_props_elims call_cond_elims)
  have finished_vsets: "∀(x, y) ∈ (Graph.digraph_abs G).
    (x ∈ t_set (finished dfs_aux_state) ⟶ y ∈ set (stack dfs_aux_state) ∪ t_set (finished dfs_aux_state)) ∧
    (y ∈ t_set (finished dfs_aux_state) ⟶ x ∈ set (stack dfs_aux_state) ∪ t_set (finished dfs_aux_state))"
    using ‹invar_seen_stack_finished dfs_aux_state› ‹invar_finished_vsets dfs_aux_state›
    graph_symmetric Graph.digraph_abs_def
    by (fastforce elim!: invar_props_elims)
  from dfs_tree_aux1[OF stack_expr w_not_in_seen finished_vsets]
    have dfs_tree_expr:
    "dfs_tree (aux.DFS_skel_upd1 dfs_aux_state) =
    {(?v, ?w), (?w, ?v)} ∪ dfs_tree dfs_aux_state"
    unfolding dfs_tree_def by (auto simp add: upd1_unfold)

  have cycle_eq: "cycle (aux.DFS_skel_upd1 dfs_aux_state) = cycle dfs_aux_state"
    by (auto simp add: upd1_unfold)
  with ‹¬cycle (aux.DFS_skel_upd1 dfs_aux_state)›
    have no_cyc: "¬cycle dfs_aux_state" by blast

  show ?case
  proof (rule ccontr, goal_cases)
    case 1
    then have "∃c. cycle' (dfs_tree (aux.DFS_skel_upd1 dfs_aux_state)) c" by blast
    then obtain c where cyc_upd: "cycle' (dfs_tree (aux.DFS_skel_upd1 dfs_aux_state)) c" by blast
    with cycle'_edges_subset have c_sub: "set c ⊆ (dfs_tree (aux.DFS_skel_upd1 dfs_aux_state))" by blast
    from cycle'_not_subset[OF cyc_upd]
      have "¬set c ⊆ (dfs_tree dfs_aux_state)"
      using ‹invar_cycle_false dfs_aux_state› no_cyc
      by (auto elim!: invar_props_elims)
    with dfs_tree_expr c_sub
      have "set c ∩ {(?v, ?w), (?w, ?v)} ≠ {}" by blast
    then consider (vw_in) "(?v, ?w) ∈ set c" | (wv_in) "(?w, ?v) ∈ set c" by blast
    then show ?case
    proof (cases)
      case vw_in
      from cycle'_adjmap_edge1[OF cyc_upd vw_neq vw_in]
        have "∃z. (?w, z) ∈ set c ∧ z ≠ ?v" by blast
      then obtain z where wz: "(?w, z) ∈ set c" and "z ≠ ?v" by blast
      with c_sub dfs_tree_expr
        have "(?w, z) ∈ dfs_tree dfs_aux_state" by auto
      then have "?w ∈ t_set (seen dfs_aux_state)"
        using ‹invar_dfs_tree_seen_2 dfs_aux_state›
        by (auto elim!: invar_props_elims)
      then show ?thesis
        using ‹aux.DFS_skel_call_1_conds dfs_aux_state› ‹invar_1 dfs_aux_state›
        by (auto elim!: invar_props_elims call_cond_elims)
    next
      case wv_in
      from cycle'_adjmap_edge2[OF cyc_upd vw_neq wv_in]
        have "∃z. (z, ?w) ∈ set c ∧ z ≠ ?v" by blast
      then obtain z where "(z, ?w) ∈ set c" and "z ≠ ?v" by blast
      with c_sub dfs_tree_expr
        have "(z, ?w) ∈ dfs_tree dfs_aux_state" by auto
      then have "?w ∈ t_set (seen dfs_aux_state)"
        using ‹invar_dfs_tree_seen_2 dfs_aux_state›
        by (auto elim!: invar_props_elims)
      then show ?thesis
        using ‹aux.DFS_skel_call_1_conds dfs_aux_state› ‹invar_1 dfs_aux_state›
        by (auto elim!: invar_props_elims call_cond_elims)
    qed
  qed
qed

lemma invar_cycle_false_holds_upd2[invar_holds_intros]:
  "⟦aux.DFS_skel_call_2_conds dfs_aux_state; invar_1 dfs_aux_state; invar_2 dfs_aux_state;
    invar_seen_stack_finished dfs_aux_state; invar_cycle_false dfs_aux_state⟧ ⟹
    invar_cycle_false (aux.DFS_skel_upd2 dfs_aux_state)"
proof (intro invar_props_intros, goal_cases)
  case 1
  have dfs_tree_eq: "dfs_tree (aux.DFS_skel_upd2 dfs_aux_state) = dfs_tree dfs_aux_state"
    using dfs_tree_upd2_eq[OF 1(1-4)] .
  have cycle_eq: "cycle (aux.DFS_skel_upd2 dfs_aux_state) = cycle dfs_aux_state"
    by (auto simp add: upd2_unfold)
  with ‹¬cycle (aux.DFS_skel_upd2 dfs_aux_state)›
    have "¬cycle dfs_aux_state" by simp
  with dfs_tree_eq ‹invar_cycle_false dfs_aux_state›
    show ?case by (force elim!: invar_props_elims)
qed

lemma invar_cycle_false_holds_ret_1[invar_holds_intros]:
  "⟦aux.DFS_skel_ret_1_conds dfs_aux_state; invar_cycle_false dfs_aux_state⟧ ⟹
    invar_cycle_false (aux.DFS_skel_ret1 dfs_aux_state)"
  unfolding invar_cycle_false_def aux.DFS_skel_ret1_def aux_on_empty_def dfs_tree_def by simp

lemma invar_cycle_false_holds_ret_2[invar_holds_intros]:
  "⟦aux.DFS_skel_ret_2_conds dfs_aux_state; invar_cycle_false dfs_aux_state⟧ ⟹
    invar_cycle_false (aux.DFS_skel_ret2 dfs_aux_state)"
proof (intro invar_props_intros, goal_cases)
  case 1
  have "cycle (aux.DFS_skel_ret2 dfs_aux_state) = True"
    by (simp add: aux.DFS_skel_ret2_def aux_on_found_def)
  with ‹¬cycle (aux.DFS_skel_ret2 dfs_aux_state)› show ?case by simp
qed

lemma invar_cycle_false_holds[invar_holds_intros]:
   assumes "aux.DFS_skel_dom dfs_aux_state" "invar_1 dfs_aux_state" "invar_2 dfs_aux_state"
     "invar_seen_stack_finished dfs_aux_state" "invar_finished_vsets dfs_aux_state"
     "invar_dfs_tree_seen_1 dfs_aux_state" "invar_dfs_tree_seen_2 dfs_aux_state"
     "invar_cycle_false dfs_aux_state"
   shows "invar_cycle_false (aux.DFS_skel dfs_aux_state)"
  using assms(2-)
proof(induction rule: aux.DFS_skel_induct[OF assms(1)])
  case IH: (1 dfs_aux_state)
  show ?case
    apply(rule aux.DFS_skel_cases[where dfs_state = dfs_aux_state])
    by (auto intro!: IH(2-10) invar_holds_intros simp: aux.DFS_skel_simps[OF IH(1)])
qed

subsection ‹Cycle-true invariant: invar_cycle_true›

lemma invar_cycle_true_props[invar_props_elims]:
  "invar_cycle_true dfs_aux_state ⟹
     (⟦(cycle dfs_aux_state) ⟹ (∃c. cycle' (Graph.digraph_abs G) c)⟧ ⟹ P) ⟹ P"
  by (auto simp: invar_cycle_true_def)

lemma invar_cycle_true_intro[invar_props_intros]:
  "⟦(cycle dfs_aux_state) ⟹ (∃c. cycle' (Graph.digraph_abs G) c)⟧ ⟹ invar_cycle_true dfs_aux_state"
  by (auto simp: invar_cycle_true_def)

lemma invar_cycle_true_holds_upd1[invar_holds_intros]:
  "⟦aux.DFS_skel_call_1_conds dfs_aux_state;
    invar_cycle_true dfs_aux_state⟧ ⟹ invar_cycle_true (aux.DFS_skel_upd1 dfs_aux_state)"
proof (intro invar_props_intros, goal_cases)
  case 1
  have "cycle (aux.DFS_skel_upd1 dfs_aux_state) = cycle dfs_aux_state"
    by (auto simp add: upd1_unfold)
  with 1 show ?case
    using ‹invar_cycle_true dfs_aux_state›
    by (auto elim!: invar_props_elims)
qed

lemma invar_cycle_true_holds_upd2[invar_holds_intros]:
  "⟦aux.DFS_skel_call_2_conds dfs_aux_state;
    invar_cycle_true dfs_aux_state⟧ ⟹ invar_cycle_true (aux.DFS_skel_upd2 dfs_aux_state)"
proof (intro invar_props_intros, goal_cases)
  case 1
  have "cycle (aux.DFS_skel_upd2 dfs_aux_state) = cycle dfs_aux_state"
    by (auto simp add: upd2_unfold)
  with 1 show ?case
    using ‹invar_cycle_true dfs_aux_state›
    by (auto elim!: invar_props_elims)
qed

lemma invar_cycle_true_holds_ret_1[invar_holds_intros]:
  "⟦aux.DFS_skel_ret_1_conds dfs_aux_state; invar_cycle_true dfs_aux_state⟧ ⟹
    invar_cycle_true (aux.DFS_skel_ret1 dfs_aux_state)"
  unfolding invar_cycle_true_def aux.DFS_skel_ret1_def aux_on_empty_def by simp

lemma invar_cycle_true_holds_ret_2[invar_holds_intros]:
  "⟦aux.DFS_skel_ret_2_conds dfs_aux_state; invar_1 dfs_aux_state; invar_2 dfs_aux_state;
    invar_seen_stack_finished dfs_aux_state; invar_cycle_true dfs_aux_state⟧ ⟹
    invar_cycle_true (aux.DFS_skel_ret2 dfs_aux_state)"
proof (intro invar_props_intros, goal_cases)
  case 1
  ― ‹cycle (ret2 state) = True, so we need ∃c. cycle' G c›
  have cycle_true: "cycle (aux.DFS_skel_ret2 dfs_aux_state) = True"
    by (simp add: aux.DFS_skel_ret2_def aux_on_found_def)
  ― ‹Back-edge facts from ret_2_found›
  from ret_2_found[OF ‹aux.DFS_skel_ret_2_conds dfs_aux_state›]
    obtain v stack_tl where stk: "stack dfs_aux_state = v # stack_tl" by blast
  from ret_2_found(2)[OF ‹aux.DFS_skel_ret_2_conds dfs_aux_state›] stk
    have back_edge:
      "((𝒩⇩G (hd (stack dfs_aux_state))) -⇩G
        (case (tl (stack dfs_aux_state)) of [] ⇒ ∅⇩N | u # _ ⇒ insert u ∅⇩N))
       ∩⇩G (seen dfs_aux_state -⇩G finished dfs_aux_state) ≠ ∅⇩N"
    by simp
  let ?v = "hd (stack dfs_aux_state)"
  show ?case
  proof (cases "tl (stack dfs_aux_state)")
    case Nil
    ― ‹Stack = [v]: The only neighbor in seen−finished would have to be v itself,
        but no self-loops, contradiction.›
    let ?x = "sel (((𝒩⇩G ?v) -⇩G ∅⇩N) ∩⇩G (seen dfs_aux_state -⇩G finished dfs_aux_state))"
    have ne: "((𝒩⇩G ?v) -⇩G ∅⇩N) ∩⇩G (seen dfs_aux_state -⇩G finished dfs_aux_state) ≠ ∅⇩N"
      using back_edge Nil by simp
    have "∃x. x ∈ t_set (((𝒩⇩G ?v) -⇩G ∅⇩N) ∩⇩G (seen dfs_aux_state -⇩G finished dfs_aux_state))"
      using ne ‹invar_1 dfs_aux_state›
      by (force elim!: invar_props_elims)
    then obtain x where
      "x ∈ t_set (((𝒩⇩G ?v) -⇩G ∅⇩N) ∩⇩G (seen dfs_aux_state -⇩G finished dfs_aux_state))"
      by blast
    then have "x ∈ t_set (𝒩⇩G ?v)" "x ∈ t_set (seen dfs_aux_state -⇩G finished dfs_aux_state)"
      using ‹invar_1 dfs_aux_state›
      by (auto elim!: invar_props_elims)
    from graph_no_self_loops1 ‹x ∈ t_set (𝒩⇩G ?v)›
      have "x ≠ ?v" by blast
    from ‹x ∈ t_set (seen dfs_aux_state -⇩G finished dfs_aux_state)›
      have "x ∈ set (stack dfs_aux_state)"
      using ‹invar_1 dfs_aux_state› ‹invar_seen_stack_finished dfs_aux_state›
      by (force elim!: invar_props_elims)
    from stk Nil have stack_eq: "stack dfs_aux_state = [?v]" by simp
    have "x ∈ set [?v]" using ‹x ∈ set (stack dfs_aux_state)› stack_eq by simp
    then have "x = ?v" by simp
    with ‹x ≠ ?v› show ?thesis by blast
  next
    case (Cons a list)
    let ?x = "sel (((𝒩⇩G ?v) -⇩G (insert a ∅⇩N)) ∩⇩G (seen dfs_aux_state -⇩G finished dfs_aux_state))"
    have ne2: "((𝒩⇩G ?v) -⇩G (insert a ∅⇩N)) ∩⇩G (seen dfs_aux_state -⇩G finished dfs_aux_state) ≠ ∅⇩N"
      using back_edge Cons by simp
    have "∃x. x ∈ t_set (((𝒩⇩G ?v) -⇩G (insert a ∅⇩N)) ∩⇩G (seen dfs_aux_state -⇩G finished dfs_aux_state))"
      using ne2 ‹invar_1 dfs_aux_state›
      by (force elim!: invar_props_elims)
    then obtain x where
      "x ∈ t_set (((𝒩⇩G ?v) -⇩G (insert a ∅⇩N)) ∩⇩G (seen dfs_aux_state -⇩G finished dfs_aux_state))"
      by blast
    then have
      "x ∈ t_set (𝒩⇩G ?v)" "x ∉ t_set (insert a ∅⇩N)" "x ∈ t_set (seen dfs_aux_state -⇩G finished dfs_aux_state)"
      using ‹invar_1 dfs_aux_state›
      by (auto elim!: invar_props_elims)

    from graph_no_self_loops1 ‹x ∈ t_set (𝒩⇩G ?v)›
      have xv_neq: "x ≠ ?v" by blast
    from ‹x ∉ t_set (insert a ∅⇩N)› have xa_neq: "x ≠ a" by simp
    from ‹x ∈ t_set (seen dfs_aux_state -⇩G finished dfs_aux_state)›
      have x_in_stack: "x ∈ set (stack dfs_aux_state)"
      using ‹invar_1 dfs_aux_state› ‹invar_seen_stack_finished dfs_aux_state›
      by (force elim!: invar_props_elims)

    have x_in_rev: "x ∈ set (rev (stack dfs_aux_state))" using x_in_stack by simp
    then obtain xs zs where xz: "rev (stack dfs_aux_state) = xs @ x # zs"
      using split_list by fastforce
    define p_x_v where "p_x_v = x # zs"
    have split: "rev (stack dfs_aux_state) = xs @ p_x_v"
      and p_ne: "p_x_v ≠ []"
      and p_hd: "hd p_x_v = x"
      by (simp_all add: p_x_v_def xz)

    have "Vwalk.vwalk (Graph.digraph_abs G) p_x_v"
      using append_vwalk_suff split ‹invar_2 dfs_aux_state›
      by (force elim!: invar_props_elims)
    moreover have last_p: "last p_x_v = ?v"
    proof -
      have "last (rev (stack dfs_aux_state)) = ?v" using stk by (simp add: last_rev)
      moreover have "last (rev (stack dfs_aux_state)) = last p_x_v"
        using split p_ne by (simp add: last_appendR)
      ultimately show ?thesis by simp
    qed
    ultimately have vwb: "Vwalk.vwalk_bet (Graph.digraph_abs G) x p_x_v ?v"
      using p_hd p_ne unfolding vwalk_bet_def by blast

    from vwalk_imp_awalk[OF vwb]
      have aw1: "awalk (Graph.digraph_abs G) x (edges_of_vwalk p_x_v) ?v"
      by blast
    have aw2: "awalk (Graph.digraph_abs G) ?v [(?v, x)] x"
      using ‹x ∈ t_set (𝒩⇩G ?v)›
      unfolding awalk_def dVs_def by auto
    have cycle_awalk: "awalk (Graph.digraph_abs G) x ((edges_of_vwalk p_x_v) @ [(?v, x)]) x"
      using awalk_appendI aw1 aw2 by simp

    from last_p
      have eov: "(edges_of_vwalk p_x_v) @ [(?v, x)] = edges_of_vwalk (p_x_v @ [x])"
      by (simp add: p_ne edges_of_vwalk_append_3)
    have averts: "awalk_verts x ((edges_of_vwalk p_x_v) @ [(?v, x)]) = p_x_v @ [x]"
    proof -
      have hdpx: "hd (p_x_v @ [x]) = x" using p_hd p_ne by (simp add: hd_append)
      have "awalk_verts x (edges_of_vwalk (p_x_v @ [x])) = p_x_v @ [x]"
        using awalk_vwalk_id[OF _ hdpx] by simp
      then show ?thesis using eov by simp
    qed
    with p_hd
      have tl_verts: "tl (awalk_verts x ((edges_of_vwalk p_x_v) @ [(?v, x)])) = tl p_x_v @ [x]"
      using p_ne by fastforce

    have "distinct (rev (stack dfs_aux_state))"
      using ‹invar_seen_stack_finished dfs_aux_state›
      by (force elim!: invar_props_elims)
    with split have distinct_p: "distinct p_x_v"
      by force
    have "distinct (tl p_x_v @ [x])"
    proof -
      obtain p' where pcons: "p_x_v = x # p'" using p_ne p_hd by (cases p_x_v) auto
      have "distinct (x # p')" using distinct_p pcons by simp
      then have "distinct p'" "x ∉ set p'" by auto
      then have "distinct (p' @ [x])" by simp
      then show ?thesis using pcons by simp
    qed
    with tl_verts
      have distinct_verts: "distinct (tl (awalk_verts x ((edges_of_vwalk p_x_v) @ [(?v, x)])))"
      by simp

    have "length p_x_v ≥ 2"
    proof -
      have "length p_x_v ≠ 0" using p_ne by simp
      moreover have "length p_x_v ≠ 1"
      proof
        assume "length p_x_v = 1"
        then obtain y where "p_x_v = [y]" by (cases p_x_v) auto
        then have "hd p_x_v = y" "last p_x_v = y" by simp_all
        with p_hd last_p xv_neq show False by simp
      qed
      ultimately show ?thesis by linarith
    qed

    have "∃ys. stack dfs_aux_state = [hd (stack dfs_aux_state), hd (tl (stack dfs_aux_state))] @ ys"
      using Cons stk
      by (force elim!: call_cond_elims)
    have rev_stk: "∃ys. rev (stack dfs_aux_state) = ys @ [a, ?v]"
    proof -
      from stk Cons have stack_form: "stack dfs_aux_state = ?v # a # list" by simp
      have "rev (stack dfs_aux_state) = rev list @ [a, ?v]"
        by (subst stack_form, simp)
      thus ?thesis by blast
    qed

    have "∃ys. p_x_v = ys @ [a, ?v]"
    proof -
      from rev_stk obtain ys_0 where rev_eq: "rev (stack dfs_aux_state) = ys_0 @ [a, ?v]"
        by blast
      from split rev_eq have xs_pxv: "xs @ p_x_v = ys_0 @ [a, ?v]" by simp
      have bltne: "butlast p_x_v ≠ []" using ‹length p_x_v ≥ 2›
        by (cases p_x_v) auto
      have blt_xs: "xs @ butlast p_x_v = ys_0 @ [a]"
      proof -
        have "butlast (xs @ p_x_v) = xs @ butlast p_x_v"
          using p_ne by (simp add: butlast_append)
        moreover have "butlast (ys_0 @ [a, ?v]) = ys_0 @ [a]"
          by (simp add: butlast_append)
        ultimately show ?thesis using xs_pxv by simp
      qed
      have last_blt: "last (butlast p_x_v) = a"
      proof -
        have "last (xs @ butlast p_x_v) = a" using blt_xs by simp
        then show ?thesis using bltne by (simp add: last_appendR)
      qed
      have blt_eq: "butlast p_x_v = butlast (butlast p_x_v) @ [a]"
      proof -
        have "butlast (butlast p_x_v) @ [last (butlast p_x_v)] = butlast p_x_v"
          using bltne by (simp add: append_butlast_last_cancel)
        then show ?thesis using last_blt by simp
      qed
      have "p_x_v = butlast (butlast p_x_v) @ [a, ?v]"
      proof -
        have pxv_blt_inner: "butlast p_x_v @ [last p_x_v] = p_x_v"
          using p_ne by (simp add: append_butlast_last_cancel)
        have pxv_blt: "butlast p_x_v @ [?v] = p_x_v"
          using pxv_blt_inner last_p by simp
        have "p_x_v = (butlast (butlast p_x_v) @ [a]) @ [?v]"
          using blt_eq pxv_blt by simp
        then show ?thesis by simp
      qed
      thus ?thesis by blast
    qed
    then obtain ys where "p_x_v = ys @ [a, ?v]" by blast
    with p_hd xa_neq
      have "ys ≠ []" by auto
    from ‹p_x_v = ys @ [a, ?v]› ‹ys ≠ []›
      have "length p_x_v ≥ 3"
      using Suc_le_eq by auto

    with edges_of_vwalk_length_geq_2[OF this]
      have length_greater_2: "length ((edges_of_vwalk p_x_v) @ [(?v, x)]) > 2"
      by auto

    from cycle_awalk distinct_verts length_greater_2
      show ?thesis unfolding cycle'_def Awalk_Defs.cycle_def by blast
  qed
qed

lemma invar_cycle_true_holds[invar_holds_intros]:
   assumes "aux.DFS_skel_dom dfs_aux_state" "invar_1 dfs_aux_state" "invar_2 dfs_aux_state"
     "invar_seen_stack_finished dfs_aux_state" "invar_cycle_true dfs_aux_state"
   shows "invar_cycle_true (aux.DFS_skel dfs_aux_state)"
  using assms(2-)
proof(induction rule: aux.DFS_skel_induct[OF assms(1)])
  case IH: (1 dfs_aux_state)
  show ?case
    apply(rule aux.DFS_skel_cases[where dfs_state = dfs_aux_state])
    by (auto intro!: IH(2-7) invar_holds_intros simp: aux.DFS_skel_simps[OF IH(1)])
qed

subsection ‹Seen-reachable invariant: invar_seen_reachable›

lemma invar_seen_reachable_props[invar_props_elims]:
  "invar_seen_reachable dfs_aux_state ⟹
     (⟦(⋀v. v ∈ t_set (seen dfs_aux_state) ⟹ (∃p. awalk (Graph.digraph_abs G) s p v))⟧ ⟹ P) ⟹ P"
  by (auto simp: invar_seen_reachable_def)

lemma invar_seen_reachable_intro[invar_props_intros]:
  "⟦(⋀v. v ∈ t_set (seen dfs_aux_state) ⟹ (∃p. awalk (Graph.digraph_abs G) s p v))⟧ ⟹
  invar_seen_reachable dfs_aux_state"
  by (auto simp: invar_seen_reachable_def)

lemma invar_seen_reachable_holds_upd1[invar_holds_intros]:
  "⟦aux.DFS_skel_call_1_conds dfs_aux_state; invar_1 dfs_aux_state; invar_2 dfs_aux_state;
  invar_s_in_stack dfs_aux_state; invar_seen_stack_finished dfs_aux_state;
  invar_seen_reachable dfs_aux_state⟧ ⟹ invar_seen_reachable (aux.DFS_skel_upd1 dfs_aux_state)"
proof (intro invar_props_intros, goal_cases)
  case (1 v)
  let ?v = "hd (stack dfs_aux_state)"
  let ?w = "sel ((𝒩⇩G ?v) -⇩G (seen dfs_aux_state))"

  have seen_expr: "t_set (seen (aux.DFS_skel_upd1 dfs_aux_state)) = t_set (seen (dfs_aux_state)) ∪ {?w}"
    using ‹invar_1 dfs_aux_state›
    by (auto simp add: upd1_unfold elim!: invar_props_elims)

  have "(?v, ?w) ∈ Graph.digraph_abs G"
    using ‹invar_1 dfs_aux_state› ‹aux.DFS_skel_call_1_conds dfs_aux_state›
    by (force elim!: invar_props_elims call_cond_elims)
  then have v_w_awalk:
    "awalk (Graph.digraph_abs G) ?v [(?v, ?w)] ?w"
    by (rule arc_implies_awalk, simp_all)

  have "?v ∈ t_set (seen dfs_aux_state)"
    using ‹invar_seen_stack_finished dfs_aux_state› ‹aux.DFS_skel_call_1_conds dfs_aux_state›
    by (fastforce elim: invar_props_elims call_cond_elims)
  then obtain p_v where p_v: "awalk (Graph.digraph_abs G) s p_v ?v"
    using ‹invar_seen_reachable dfs_aux_state›
    by (force elim: invar_props_elims)
  have w_reachable:
    "∃p_w. awalk (Graph.digraph_abs G) s p_w ?w"
  proof -
    have "awalk (Graph.digraph_abs G) s (p_v @ [(?v, ?w)]) ?w"
      using awalk_appendI[OF p_v v_w_awalk] .
    thus ?thesis by blast
  qed

  show ?case
    using seen_expr ‹invar_seen_reachable dfs_aux_state› w_reachable ‹v ∈ t_set (seen (aux.DFS_skel_upd1 dfs_aux_state))›
    by (force elim!: invar_props_elims)
qed

lemma invar_seen_reachable_holds_upd2[invar_holds_intros]:
  "⟦aux.DFS_skel_call_2_conds dfs_aux_state; invar_1 dfs_aux_state; invar_2 dfs_aux_state;
    invar_seen_stack_finished dfs_aux_state; invar_seen_reachable dfs_aux_state⟧ ⟹
    invar_seen_reachable (aux.DFS_skel_upd2 dfs_aux_state)"
proof (intro invar_props_intros, goal_cases)
  case (1 v)
  have seen_expr: "t_set (seen (aux.DFS_skel_upd2 dfs_aux_state)) = t_set (seen (dfs_aux_state))"
    by (auto simp add: upd2_unfold)
  from seen_expr ‹v ∈ t_set (seen (aux.DFS_skel_upd2 dfs_aux_state))›
    show ?case
    using ‹invar_seen_reachable dfs_aux_state›
    by (auto elim!: invar_props_elims)
qed

lemma invar_seen_reachable_holds_ret_1[invar_holds_intros]:
  "⟦aux.DFS_skel_ret_1_conds dfs_aux_state; invar_seen_reachable dfs_aux_state⟧ ⟹
  invar_seen_reachable (aux.DFS_skel_ret1 dfs_aux_state)"
  by (auto simp: aux.DFS_skel_ret1_def aux_on_empty_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_seen_reachable_holds_ret_2[invar_holds_intros]:
  "⟦aux.DFS_skel_ret_2_conds dfs_aux_state; invar_seen_reachable dfs_aux_state⟧ ⟹
  invar_seen_reachable (aux.DFS_skel_ret2 dfs_aux_state)"
  by (auto simp: aux.DFS_skel_ret2_def aux_on_found_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_seen_reachable_holds[invar_holds_intros]:
   assumes "aux.DFS_skel_dom dfs_aux_state" "invar_1 dfs_aux_state" "invar_2 dfs_aux_state"
     "invar_s_in_stack dfs_aux_state" "invar_seen_stack_finished dfs_aux_state"
     "invar_seen_reachable dfs_aux_state"
   shows "invar_seen_reachable (aux.DFS_skel dfs_aux_state)"
  using assms(2-)
proof(induction rule: aux.DFS_skel_induct[OF assms(1)])
  case IH: (1 dfs_aux_state)
  show ?case
    apply(rule aux.DFS_skel_cases[where dfs_state = dfs_aux_state])
    by (auto intro!: IH(2-8) invar_holds_intros simp: aux.DFS_skel_simps[OF IH(1)])
qed

subsection ‹Visited-through-seen invariant: invar_visited_through_seen›

lemma invar_visited_through_seen_props:
   "invar_visited_through_seen dfs_aux_state ⟹
     (⟦⋀v w p. ⟦v ∈ t_set (seen dfs_aux_state); w ∈ dVs (Graph.digraph_abs G) - t_set (seen dfs_aux_state);
        Vwalk.vwalk_bet (Graph.digraph_abs G) v p w; distinct p⟧ ⟹
        set p ∩ set (stack dfs_aux_state) ≠ {}⟧ ⟹ P) ⟹ P"
  using invar_visited_through_seen_def by blast

lemma invar_visited_through_seen_intro[invar_props_intros]:
  "⟦⋀v w p. ⟦v ∈ t_set (seen dfs_aux_state); w ∈ dVs (Graph.digraph_abs G) - t_set (seen dfs_aux_state);
              Vwalk.vwalk_bet (Graph.digraph_abs G) v p w; distinct p⟧ ⟹
              set p ∩ set (stack dfs_aux_state) ≠ {}⟧ ⟹ invar_visited_through_seen dfs_aux_state"
  by (auto simp: invar_visited_through_seen_def)

lemma invar_visited_through_seen_holds_upd1[invar_holds_intros]:
  "⟦aux.DFS_skel_call_1_conds dfs_aux_state; invar_1 dfs_aux_state; invar_seen_stack_finished dfs_aux_state;
    invar_visited_through_seen dfs_aux_state⟧
    ⟹ invar_visited_through_seen (aux.DFS_skel_upd1 dfs_aux_state)"
proof (intro invar_props_intros, goal_cases)
  case (1 v w p)
  let ?v = "hd (stack dfs_aux_state)"
  let ?w = "sel ((𝒩⇩G ?v) -⇩G (seen dfs_aux_state))"
  have seen_expr: "t_set (seen (aux.DFS_skel_upd1 dfs_aux_state)) = t_set (seen dfs_aux_state) ∪ {?w}"
    using ‹invar_1 dfs_aux_state›
    by (auto simp add: upd1_unfold elim!: invar_props_elims)
  have stack_expr: "stack (aux.DFS_skel_upd1 dfs_aux_state) = ?w # stack dfs_aux_state"
    by (simp add: upd1_unfold)
  from 1(5) seen_expr consider (a) "v = ?w" | (b) "v ∈ t_set (seen dfs_aux_state)"
    by fastforce
  then show ?case
  proof (cases)
    case a
    have "v ∈ set p"
      using hd_of_vwalk_bet''[OF 1(7)] a by simp
    with stack_expr a show ?thesis by auto
  next
    case b
    have w_old_unseen: "w ∈ dVs (Graph.digraph_abs G) - t_set (seen dfs_aux_state)"
      using 1(6) seen_expr by auto
    have "set p ∩ set (stack dfs_aux_state) ≠ {}"
      using ‹invar_visited_through_seen dfs_aux_state› b w_old_unseen 1(7) 1(8)
      unfolding invar_visited_through_seen_def by blast
    then show ?thesis
      by (auto simp add: upd1_unfold)
  qed
qed

lemma invar_visited_through_seen_holds_upd2[invar_holds_intros]:
  assumes call2: "aux.DFS_skel_call_2_conds dfs_aux_state"
      and inv1: "invar_1 dfs_aux_state"
      and inv_ssf: "invar_seen_stack_finished dfs_aux_state"
      and inv_vts: "invar_visited_through_seen dfs_aux_state"
  shows "invar_visited_through_seen (aux.DFS_skel_upd2 dfs_aux_state)"
proof (rule invar_props_intros)
  fix v w p
  assume v_in: "v ∈ t_set (seen (aux.DFS_skel_upd2 dfs_aux_state))"
     and w_out: "w ∈ dVs (Graph.digraph_abs G) - t_set (seen (aux.DFS_skel_upd2 dfs_aux_state))"
     and vwb: "Vwalk.vwalk_bet (Graph.digraph_abs G) v p w"
     and dist: "distinct p"
  have seen_eq: "t_set (seen (aux.DFS_skel_upd2 dfs_aux_state)) = t_set (seen dfs_aux_state)"
    by (simp add: upd2_unfold)
  obtain v' stack_tl where stack_hd: "stack dfs_aux_state = v' # stack_tl"
    using call_2_excl(1)[OF call2] by blast
  have stack_upd2: "stack (aux.DFS_skel_upd2 dfs_aux_state) = stack_tl"
    by (simp add: upd2_unfold stack_hd)
  have nbr_empty: "(𝒩⇩G v') -⇩G (seen dfs_aux_state) = ∅⇩N"
    using call_2_excl(3)[OF call2] stack_hd by simp
  have v_seen: "v ∈ t_set (seen dfs_aux_state)"
    using v_in seen_eq by blast
  have w_unseen: "w ∈ dVs (Graph.digraph_abs G) - t_set (seen dfs_aux_state)"
    using w_out seen_eq by blast
  have stk_sub: "set (stack dfs_aux_state) ⊆ t_set (seen dfs_aux_state)"
    using inv_ssf unfolding invar_seen_stack_finished_def by blast
  have v'_seen: "v' ∈ t_set (seen dfs_aux_state)"
    using stk_sub stack_hd by auto
  have vts_ih: "⋀v0 w0 p0.
    ⟦v0 ∈ t_set (seen dfs_aux_state);
     w0 ∈ dVs (Graph.digraph_abs G) - t_set (seen dfs_aux_state);
     Vwalk.vwalk_bet (Graph.digraph_abs G) v0 p0 w0; distinct p0⟧ ⟹
    set p0 ∩ set (stack dfs_aux_state) ≠ {}"
    using inv_vts unfolding invar_visited_through_seen_def by blast
  have ih_applied: "set p ∩ set (stack dfs_aux_state) ≠ {}"
    using vts_ih v_seen w_unseen vwb dist by blast
  then obtain u where u_p: "u ∈ set p" and u_stk: "u ∈ set (stack dfs_aux_state)"
    by auto
  show "set p ∩ set (stack (aux.DFS_skel_upd2 dfs_aux_state)) ≠ {}"
  proof (cases "u ∈ set stack_tl")
    case True
    thus ?thesis using u_p stack_upd2 by auto
  next
    case False
    hence u_eq: "u = v'"
      using u_stk stack_hd by auto
    then obtain p1 p2 where p_split: "p = p1 @ [v'] @ p2"
      using u_p by (auto simp: in_set_conv_decomp)
    have dist_p12: "distinct (p1 @ [v'] @ p2)"
      by (subst p_split[symmetric]; rule dist)
    show ?thesis
    proof (cases "p2 = []")
      case True
      have p_form: "p = p1 @ [v']" using p_split True by simp
      have wb: "Vwalk.vwalk_bet (Graph.digraph_abs G) v (p1 @ [v']) w"
        by (subst p_form[symmetric]; rule vwb)
      from vwalk_bet_snoc[OF wb] have "v' = w" by simp
      with w_unseen v'_seen show ?thesis by blast
    next
      case p2_nonempty: False
      have vwalk_vp12: "Vwalk.vwalk_bet (Graph.digraph_abs G) v (p1 @ v' # p2) w"
        using vwb by (simp add: p_split)
      have v'_p2_walk: "Vwalk.vwalk_bet (Graph.digraph_abs G) v' (v' # p2) w"
        using split_vwalk[OF vwalk_vp12] by simp
      have hd_p2_nbr: "hd p2 ∈ t_set (𝒩⇩G v')"
      proof -
        from p2_nonempty obtain a as where p2_eq: "p2 = a # as"
          using list.exhaust by auto
        have vwk: "Vwalk.vwalk (Graph.digraph_abs G) (v' # p2)"
          using v'_p2_walk by (simp only: vwalk_bet_def)
        from vwk p2_eq have "Vwalk.vwalk (Graph.digraph_abs G) (v' # a # as)"
          by (simp only: p2_eq)
        hence edge: "(v', a) ∈ Graph.digraph_abs G"
          by (rule vwalk_cons)
        with p2_eq show ?thesis
          by (auto simp: Graph.neighbourhood_abs)
      qed
      have hd_p2_seen: "hd p2 ∈ t_set (seen dfs_aux_state)"
      proof -
        have "t_set (𝒩⇩G v') - t_set (seen dfs_aux_state) =
              t_set ((𝒩⇩G v') -⇩G (seen dfs_aux_state))"
          using inv1 by (auto elim!: invar_1_props)
        with nbr_empty hd_p2_nbr show ?thesis by auto
      qed
      have hd_p2_walk: "Vwalk.vwalk_bet (Graph.digraph_abs G) (hd p2) p2 w"
        using v'_p2_walk p2_nonempty by (simp add: vwalk_bet_cons)
      have distinct_p2: "distinct p2" using dist_p12 by simp
      have p2_meets_stack: "set p2 ∩ set (stack dfs_aux_state) ≠ {}"
        using vts_ih hd_p2_seen w_unseen hd_p2_walk distinct_p2 by blast
      have v'_notin_p2: "v' ∉ set p2" using dist_p12 by simp
      from p2_meets_stack obtain x where x_p2: "x ∈ set p2" and x_stk: "x ∈ set (stack dfs_aux_state)"
        by auto
      have x_not_v': "x ≠ v'" using x_p2 v'_notin_p2 by blast
      have x_tl: "x ∈ set stack_tl" using x_stk stack_hd x_not_v' by auto
      have x_p: "x ∈ set p" using x_p2 p_split by auto
      have x_upd2: "x ∈ set (stack (aux.DFS_skel_upd2 dfs_aux_state))"
        using x_tl stack_upd2 by auto
      show ?thesis using x_p x_upd2 by auto
    qed
  qed
qed

lemma invar_visited_through_seen_holds_ret_1[invar_holds_intros]:
  "⟦aux.DFS_skel_ret_1_conds dfs_aux_state; invar_visited_through_seen dfs_aux_state⟧ ⟹
    invar_visited_through_seen (aux.DFS_skel_ret1 dfs_aux_state)"
  by (simp add: aux.DFS_skel_ret1_def aux_on_empty_def)

lemma invar_visited_through_seen_holds_ret_2[invar_holds_intros]:
  "⟦aux.DFS_skel_ret_2_conds dfs_aux_state; invar_visited_through_seen dfs_aux_state⟧ ⟹
    invar_visited_through_seen (aux.DFS_skel_ret2 dfs_aux_state)"
  by (simp add: aux.DFS_skel_ret2_def aux_on_found_def invar_visited_through_seen_def)

lemma invar_visited_through_seen_holds:
   assumes "aux.DFS_skel_dom dfs_aux_state" "invar_1 dfs_aux_state"
     "invar_seen_stack_finished dfs_aux_state" "invar_visited_through_seen dfs_aux_state"
   shows "invar_visited_through_seen (aux.DFS_skel dfs_aux_state)"
  using assms(2-)
proof(induction rule: aux.DFS_skel_induct[OF assms(1)])
  case IH: (1 dfs_aux_state)
  show ?case
    apply(rule aux.DFS_skel_cases[where dfs_state = dfs_aux_state])
    by (auto intro!: IH(2-6) invar_holds_intros simp: aux.DFS_skel_simps[OF IH(1)])
qed

subsection ‹State relation and monotonicity›

lemma state_rel_1_props[elim!]:
  "state_rel_1 dfs_aux_state_1 dfs_aux_state_2 ⟹
     (t_set (seen dfs_aux_state_1) ⊆ t_set (seen dfs_aux_state_2) ⟹ P) ⟹ P"
  by (auto simp: state_rel_1_def)

lemma state_rel_1_intro[state_rel_intros]:
  "⟦t_set (seen dfs_aux_state_1) ⊆ t_set (seen dfs_aux_state_2)⟧ ⟹
    state_rel_1 dfs_aux_state_1 dfs_aux_state_2"
  by (auto simp: state_rel_1_def)

lemma state_rel_1_trans:
  "⟦state_rel_1 dfs_aux_state_1 dfs_aux_state_2; state_rel_1 dfs_aux_state_2 dfs_aux_state_3⟧ ⟹
   state_rel_1 dfs_aux_state_1 dfs_aux_state_3"
  by (auto intro!: state_rel_intros)

lemma state_rel_1_holds_upd1[state_rel_holds_intros]:
  "⟦aux.DFS_skel_call_1_conds dfs_aux_state; invar_1 dfs_aux_state⟧ ⟹
    state_rel_1 dfs_aux_state (aux.DFS_skel_upd1 dfs_aux_state)"
  by (auto simp: upd1_unfold elim!: invar_props_elims intro!: state_rel_intros)

lemma state_rel_1_holds_upd2[state_rel_holds_intros]:
  "⟦aux.DFS_skel_call_2_conds dfs_aux_state; invar_1 dfs_aux_state⟧ ⟹
    state_rel_1 dfs_aux_state (aux.DFS_skel_upd2 dfs_aux_state)"
  by (auto simp: upd2_unfold elim!: invar_props_elims intro!: state_rel_intros)

lemma state_rel_1_holds_ret_1[state_rel_holds_intros]:
  "⟦aux.DFS_skel_ret_1_conds dfs_aux_state⟧ ⟹
    state_rel_1 dfs_aux_state (aux.DFS_skel_ret1 dfs_aux_state)"
  by (auto intro!: state_rel_intros simp: aux.DFS_skel_ret1_def aux_on_empty_def)

lemma state_rel_1_holds_ret_2[state_rel_holds_intros]:
  "⟦aux.DFS_skel_ret_2_conds dfs_aux_state⟧ ⟹
    state_rel_1 dfs_aux_state (aux.DFS_skel_ret2 dfs_aux_state)"
  by (auto intro!: state_rel_intros simp: aux.DFS_skel_ret2_def aux_on_found_def)

lemma state_rel_1_holds[state_rel_holds_intros]:
   assumes "aux.DFS_skel_dom dfs_aux_state" "invar_1 dfs_aux_state"
   shows "state_rel_1 dfs_aux_state (aux.DFS_skel dfs_aux_state)"
   using assms(2-)
proof(induction rule: aux.DFS_skel_induct[OF assms(1)])
  case IH: (1 dfs_aux_state)
  show ?case
    apply(rule aux.DFS_skel_cases[where dfs_state = dfs_aux_state])
    by (auto intro: state_rel_1_trans invar_holds_intros state_rel_holds_intros
             intro!: IH(2-) simp: aux.DFS_skel_simps[OF IH(1)])
qed

subsection ‹Return condition lemmas›

text ‹In the skeleton, ret_1_conds = stack empty (on_empty path) and ret_2_conds = found (on_found
path). This is the reverse of DFS_Cycles_Aux where ret_1 = found and ret_2 = empty.›

lemma DFS_Aux_ret_1[ret_holds_intros]:
  "aux.DFS_skel_ret_1_conds dfs_aux_state ⟹
    aux.DFS_skel_ret_1_conds (aux.DFS_skel_ret1 dfs_aux_state)"
  by (auto simp: aux.DFS_skel_ret1_def aux_on_empty_def aux_found_def
           elim!: call_cond_elims intro!: call_cond_intros)

text ‹When cycle becomes True (was False), the algorithm returned via on_found, so ret_2_conds holds.›
lemma ret1_holds[ret_holds_intros]:
   assumes "aux.DFS_skel_dom dfs_aux_state"
       and "cycle (aux.DFS_skel dfs_aux_state) = True"
       and "cycle dfs_aux_state = False"
   shows "aux.DFS_skel_ret_2_conds (aux.DFS_skel dfs_aux_state)"
   using assms(2-)
proof(induction rule: aux.DFS_skel_induct[OF assms(1)])
  case IH: (1 dfs_aux_state)
  show ?case
  proof (rule aux.DFS_skel_cases[where dfs_state = dfs_aux_state], goal_cases)
    case (1)
    ― ‹call_1_conds›
    have c1: "aux.DFS_skel_call_1_conds dfs_aux_state" by (rule 1)
    have cycle_upd1: "cycle (aux.DFS_skel_upd1 dfs_aux_state) = False"
      by (simp add: upd1_unfold IH(5))
    have dfs_eq: "aux.DFS_skel dfs_aux_state = aux.DFS_skel (aux.DFS_skel_upd1 dfs_aux_state)"
      by (simp add: aux.DFS_skel_simps[OF IH(1)] c1)
    have cycle_result: "cycle (aux.DFS_skel (aux.DFS_skel_upd1 dfs_aux_state)) = True"
      using IH(4) dfs_eq by simp
    from IH(2)[OF c1, OF cycle_result, OF cycle_upd1]
    show ?case by (simp add: dfs_eq)
  next
    case (2)
    ― ‹call_2_conds›
    have c2: "aux.DFS_skel_call_2_conds dfs_aux_state" by (rule 2)
    have cycle_upd2: "cycle (aux.DFS_skel_upd2 dfs_aux_state) = False"
      by (simp add: upd2_unfold IH(5))
    have dfs_eq: "aux.DFS_skel dfs_aux_state = aux.DFS_skel (aux.DFS_skel_upd2 dfs_aux_state)"
      by (simp add: aux.DFS_skel_simps[OF IH(1)] c2)
    have cycle_result: "cycle (aux.DFS_skel (aux.DFS_skel_upd2 dfs_aux_state)) = True"
      using IH(4) dfs_eq by simp
    from IH(3)[OF c2, OF cycle_result, OF cycle_upd2]
    show ?case by (simp add: dfs_eq)
  next
    case r1: (3)
    ― ‹ret_1_conds: cycle(DFS_skel) = cycle(on_empty) = cycle, contradicts IH(4)=True and IH(5)=False›
    have "cycle (aux.DFS_skel dfs_aux_state) = cycle dfs_aux_state"
      by (simp add: aux.DFS_skel_simps[OF IH(1)] r1 aux.DFS_skel_ret1_def aux_on_empty_def)
    with IH(4) IH(5) show ?case by simp
  next
    case r2: (4)
    ― ‹ret_2_conds: DFS_skel = on_found = aux_on_found which preserves stack/seen/finished›
    have eq: "aux.DFS_skel dfs_aux_state = aux_on_found dfs_aux_state"
      using r2 by (simp add: aux.DFS_skel_simps[OF IH(1)] aux.DFS_skel_ret2_def)
    have stk: "∃v stack_tl. stack dfs_aux_state = v # stack_tl"
      using r2 by (auto elim!: call_cond_elims)
    have fnd: "aux_found dfs_aux_state"
      using r2 by (auto elim!: call_cond_elims)
    have "aux.DFS_skel_ret_2_conds (aux_on_found dfs_aux_state)"
      using stk fnd
      by (auto simp: aux.DFS_skel_ret_2_conds_def aux_on_found_def aux_found_def
               split: list.splits)
    then show ?case using eq by simp
  qed
qed

lemma DFS_Aux_correct_1_ret_2:
  "⟦aux.DFS_skel_ret_2_conds dfs_aux_state; cycle dfs_aux_state;
    invar_cycle_true dfs_aux_state⟧ ⟹
    (∃c. cycle' (Graph.digraph_abs G) c)"
  by (auto elim!: invar_props_elims)

lemma DFS_Aux_correct_4_ret_2_aux:
  "⟦aux.DFS_skel_ret_2_conds dfs_aux_state; invar_1 dfs_aux_state⟧ ⟹
    vset_inv (seen dfs_aux_state)"
  by (auto elim!: invar_props_elims)

lemma DFS_Aux_ret_2[ret_holds_intros]:
  "aux.DFS_skel_ret_2_conds dfs_aux_state ⟹
    aux.DFS_skel_ret_2_conds (aux.DFS_skel_ret2 dfs_aux_state)"
  by (auto simp: aux.DFS_skel_ret2_def aux_on_found_def aux_found_def
           elim!: call_cond_elims intro!: call_cond_intros)

text ‹When cycle stays False, the algorithm returned via on_empty, so ret_1_conds (stack empty) holds.›
lemma ret2_holds[ret_holds_intros]:
   assumes "aux.DFS_skel_dom dfs_aux_state"
       and "cycle (aux.DFS_skel dfs_aux_state) = False"
   shows "aux.DFS_skel_ret_1_conds (aux.DFS_skel dfs_aux_state)"
   using assms(2-)
proof(induction rule: aux.DFS_skel_induct[OF assms(1)])
  case IH: (1 dfs_aux_state)
  show ?case
  proof (rule aux.DFS_skel_cases[where dfs_state = dfs_aux_state], goal_cases)
    case (1)
    ― ‹call_1_conds: apply recursive IH(2)›
    have c1: "aux.DFS_skel_call_1_conds dfs_aux_state" by (rule 1)
    have dfs_eq: "aux.DFS_skel dfs_aux_state = aux.DFS_skel (aux.DFS_skel_upd1 dfs_aux_state)"
      by (simp add: aux.DFS_skel_simps[OF IH(1)] c1)
    have cycle_result: "cycle (aux.DFS_skel (aux.DFS_skel_upd1 dfs_aux_state)) = False"
      using IH(4) dfs_eq by simp
    from IH(2)[OF c1] have "aux.DFS_skel_ret_1_conds (aux.DFS_skel (aux.DFS_skel_upd1 dfs_aux_state))"
      using cycle_result by blast
    with dfs_eq show ?case by simp
  next
    case (2)
    ― ‹call_2_conds: apply recursive IH(3)›
    have c2: "aux.DFS_skel_call_2_conds dfs_aux_state" by (rule 2)
    have dfs_eq: "aux.DFS_skel dfs_aux_state = aux.DFS_skel (aux.DFS_skel_upd2 dfs_aux_state)"
      by (simp add: aux.DFS_skel_simps[OF IH(1)] c2)
    have cycle_result: "cycle (aux.DFS_skel (aux.DFS_skel_upd2 dfs_aux_state)) = False"
      using IH(4) dfs_eq by simp
    from IH(3)[OF c2] have "aux.DFS_skel_ret_1_conds (aux.DFS_skel (aux.DFS_skel_upd2 dfs_aux_state))"
      using cycle_result by blast
    with dfs_eq show ?case by simp
  next
    case r3: (3)
    ― ‹ret_1_conds: DFS_skel = on_empty = aux_on_empty = id, so DFS_skel = dfs_aux_state›
    have eq: "aux.DFS_skel dfs_aux_state = dfs_aux_state"
      using r3 by (simp add: aux.DFS_skel_simps[OF IH(1)] aux.DFS_skel_ret1_def aux_on_empty_def)
    then show ?case using r3 by simp
  next
    case r4: (4)
    ― ‹ret_2_conds: DFS_skel = aux_on_found = dfs⦇cycle:=True⦈, contradicts IH(4): cycle=False›
    have eq: "aux.DFS_skel dfs_aux_state = aux_on_found dfs_aux_state"
      using r4 by (simp add: aux.DFS_skel_simps[OF IH(1)] aux.DFS_skel_ret2_def)
    have "cycle (aux.DFS_skel dfs_aux_state) = True"
      by (simp add: eq aux_on_found_def)
    with IH(4) show ?case by simp
  qed
qed

lemma DFS_Aux_correct_2_ret_1:
  "⟦aux.DFS_skel_ret_1_conds dfs_aux_state; ¬cycle dfs_aux_state;
    invar_seen_stack_finished dfs_aux_state; invar_cycle_false dfs_aux_state⟧ ⟹
    (∄c. cycle' ((Graph.digraph_abs G) ⇂ (t_set (seen dfs_aux_state))) c)"
proof-
  assume "aux.DFS_skel_ret_1_conds dfs_aux_state" "invar_seen_stack_finished dfs_aux_state"
    "¬cycle dfs_aux_state" "invar_cycle_false dfs_aux_state"
  then have "∄c. cycle' (dfs_tree dfs_aux_state) c"
    by (force elim!: invar_props_elims)
  have stack_empty: "stack dfs_aux_state = []"
    using ‹aux.DFS_skel_ret_1_conds dfs_aux_state›
    by (auto elim!: call_cond_elims)
  then have "dfs_tree dfs_aux_state =
    {(x, y). (x, y) ∈ (Graph.digraph_abs G) ∧
              x ∈ t_set (finished dfs_aux_state) ∧ y ∈ t_set (finished dfs_aux_state)}"
    unfolding dfs_tree_def by simp
  moreover have "t_set (seen dfs_aux_state) = t_set (finished dfs_aux_state)"
    using stack_empty ‹invar_seen_stack_finished dfs_aux_state›
    by (force elim!: invar_props_elims)
  ultimately have "dfs_tree dfs_aux_state = ((Graph.digraph_abs G) ⇂ (t_set (seen dfs_aux_state)))"
    unfolding induce_subgraph_def by blast
  with ‹∄c. cycle' (dfs_tree dfs_aux_state) c›
    show "(∄c. cycle' ((Graph.digraph_abs G) ⇂ (t_set (seen dfs_aux_state))) c)" by auto
qed

lemma DFS_Aux_correct_3_ret_1:
  "⟦aux.DFS_skel_ret_1_conds dfs_aux_state; invar_visited_through_seen dfs_aux_state;
    v ∈ t_set (seen dfs_aux_state);
    w ∈ dVs (Graph.digraph_abs G) - t_set (seen dfs_aux_state)⟧ ⟹
      (∄p. awalk (Graph.digraph_abs G) v p w)"
proof-
  assume "aux.DFS_skel_ret_1_conds dfs_aux_state" "invar_visited_through_seen dfs_aux_state"
    "v ∈ t_set (seen dfs_aux_state)" "w ∈ dVs (Graph.digraph_abs G) - t_set (seen dfs_aux_state)"
  have vts: "∀p. Vwalk.vwalk_bet (Graph.digraph_abs G) v p w ∧ distinct p ⟶
    (set p ∩ set (stack dfs_aux_state) ≠ {})"
    using ‹invar_visited_through_seen dfs_aux_state›
          ‹v ∈ t_set (seen dfs_aux_state)› ‹w ∈ dVs (Graph.digraph_abs G) - t_set (seen dfs_aux_state)›
    by (auto elim: invar_visited_through_seen_props)
  have stk: "stack dfs_aux_state = []"
    using ‹aux.DFS_skel_ret_1_conds dfs_aux_state›
    by (auto elim!: call_cond_elims)
  then have no_vwalks: "∄p. distinct p ∧ Vwalk.vwalk_bet (Graph.digraph_abs G) v p w"
    using vts by auto
  show "(∄p. awalk (Graph.digraph_abs G) v p w)"
  proof (rule ccontr, goal_cases)
    case 1
    then obtain p where "awalk (Graph.digraph_abs G) v p w" by blast
    from apath_awalk_to_apath[OF this]
      have "apath (Graph.digraph_abs G) v (awalk_to_apath (Graph.digraph_abs G) p) w" .
    with apath_def[of "(Graph.digraph_abs G)" "v"
                      "(awalk_to_apath (Graph.digraph_abs G) p)" "w"]
      have "awalk (Graph.digraph_abs G) v (awalk_to_apath (Graph.digraph_abs G) p) w"
        "distinct (awalk_verts v (awalk_to_apath (Graph.digraph_abs G) p))"
      by auto
    moreover have
      "vwalk_bet (Graph.digraph_abs G) v
        (awalk_verts v (awalk_to_apath (Graph.digraph_abs G) p)) w"
      using awalk_imp_vwalk[OF
        ‹awalk (Graph.digraph_abs G) v (awalk_to_apath (Graph.digraph_abs G) p) w›]
      by simp
    ultimately show ?case using no_vwalks by blast
  qed
qed

lemma DFS_Aux_correct_4_ret_1:
  "⟦aux.DFS_skel_ret_1_conds dfs_aux_state; invar_1 dfs_aux_state⟧ ⟹
    vset_inv (seen dfs_aux_state)"
  by (auto elim!: invar_props_elims)

lemma DFS_Aux_correct_5_ret:
  "⟦invar_seen_reachable dfs_aux_state; v ∈ t_set (seen dfs_aux_state)⟧ ⟹
    ∃p. awalk (Graph.digraph_abs G) s p v"
  by (auto elim!: invar_props_elims)

subsection ‹Termination and initial state›

lemma aux_initial_dom: "aux.DFS_skel_dom initial_state"
  by (intro aux.DFS_skel_terminates)
     (auto simp: initial_state_def intro!: invar_props_intros)

lemma initial_state_props:
  "invar_1 initial_state"
  "invar_2 initial_state"
  "invar_seen_stack_finished initial_state"
  "invar_visited_through_seen initial_state"
  "invar_s_in_stack initial_state"
  "invar_finished_vsets initial_state"
  "invar_dfs_tree_seen_1 initial_state"
  "invar_dfs_tree_seen_2 initial_state"
  "invar_cycle_false initial_state"
  "invar_cycle_true initial_state"
  "invar_seen_reachable initial_state"
  "aux.DFS_skel_dom initial_state"
proof-
  show "invar_1 initial_state"
    by (auto simp: initial_state_def intro!: invar_props_intros)
  show "invar_2 initial_state"
    by (auto simp: initial_state_def intro!: invar_props_intros)
  show "invar_seen_stack_finished initial_state"
    by (auto simp: initial_state_def intro!: invar_props_intros)
  show "invar_visited_through_seen initial_state"
    by (auto simp: initial_state_def hd_of_vwalk_bet''
             elim: vwalk_betE intro!: invar_props_intros)
  show "invar_s_in_stack initial_state"
    by (auto simp: initial_state_def intro!: invar_props_intros)
  show "invar_finished_vsets initial_state"
    by (auto simp: initial_state_def intro!: invar_props_intros)
  show "invar_dfs_tree_seen_1 initial_state"
    by (auto simp: initial_state_def dfs_tree_def intro!: invar_props_intros)
  show "invar_dfs_tree_seen_2 initial_state"
    by (auto simp: initial_state_def dfs_tree_def intro!: invar_props_intros)
  show "invar_cycle_false initial_state"
  proof (intro invar_props_intros, goal_cases)
    case 1
    have "dfs_tree initial_state = {}"
      by (auto simp: dfs_tree_def initial_state_def)
    then show ?case
      using awalk_def
      by (fastforce dest: cycle'_imp_awalk simp: dVs_empty)
  qed
  show "invar_cycle_true initial_state"
    by (auto simp: initial_state_def intro!: invar_props_intros)
  show "invar_seen_reachable initial_state"
  proof (intro invar_props_intros, goal_cases)
    case (1 v)
    then have "v = s"
      by (auto simp: initial_state_def)
    then show ?case
      unfolding awalk_def
      by (meson awalkE' awalk_Nil_iff s_in_G)
  qed
  show "aux.DFS_skel_dom initial_state"
    by (rule aux_initial_dom)
qed

subsection ‹Main correctness theorems›

lemma DFS_Aux_correct_1:
  assumes "cycle (aux.DFS_skel initial_state)"
  shows "(∃c. cycle' (Graph.digraph_abs G) c)"
  apply (intro DFS_Aux_correct_1_ret_2[where dfs_aux_state = "aux.DFS_skel initial_state"])
  subgoal
    using ret1_holds[OF initial_state_props(12)] assms initial_state_def by force
  subgoal
    using assms by blast
  subgoal
    by (auto intro!: invar_holds_intros initial_state_props)
  done

lemma DFS_Aux_correct_2:
  assumes "¬cycle (aux.DFS_skel initial_state)"
  shows "∄c. cycle' ((Graph.digraph_abs G) ⇂ (t_set (seen (aux.DFS_skel initial_state)))) c"
  apply (intro DFS_Aux_correct_2_ret_1[where dfs_aux_state = "aux.DFS_skel initial_state"])
  subgoal
    using ret2_holds[OF initial_state_props(12)] assms by force
  subgoal
    using assms by blast
  subgoal
    by (auto intro!: invar_holds_intros initial_state_props)
  subgoal
    by (auto intro!: invar_holds_intros initial_state_props)
  done

lemma DFS_Aux_correct_3:
  assumes "¬cycle (aux.DFS_skel initial_state)"
      and "v ∈ t_set (seen (aux.DFS_skel initial_state))"
      and "w ∈ dVs (Graph.digraph_abs G) - t_set (seen (aux.DFS_skel initial_state))"
  shows "(∄p. awalk (Graph.digraph_abs G) v p w)"
  apply (intro DFS_Aux_correct_3_ret_1[where dfs_aux_state = "aux.DFS_skel initial_state"])
  subgoal
    using ret2_holds[OF initial_state_props(12)] assms by force
  subgoal
    using invar_visited_through_seen_holds[OF initial_state_props(12) initial_state_props(1)
      initial_state_props(3) initial_state_props(4)]
    by blast
  subgoal
    using assms by blast
  subgoal
    using assms by blast
  done

lemma DFS_Aux_correct_4:
  "vset_inv (seen (aux.DFS_skel initial_state))"
  using invar_1_holds
  by (auto intro!: invar_holds_intros initial_state_props elim!: invar_props_elims)

lemma DFS_Aux_correct_5:
  assumes "v ∈ t_set (seen (aux.DFS_skel initial_state))"
  shows "∃p. awalk (Graph.digraph_abs G) s p v"
  apply (intro DFS_Aux_correct_5_ret[where dfs_aux_state = "aux.DFS_skel initial_state"])
  using assms by (auto intro!: invar_holds_intros initial_state_props elim!: invar_props_elims)

lemma DFS_Aux_correct_6:
  "s ∈ t_set (seen (aux.DFS_skel initial_state))"
proof-
  from state_rel_1_holds[where dfs_aux_state = "initial_state",
    OF initial_state_props(12) initial_state_props(1)]
  have "t_set (seen initial_state) ⊆ t_set (seen (aux.DFS_skel initial_state))"
    by auto
  then show "s ∈ t_set (seen (aux.DFS_skel initial_state))"
    unfolding initial_state_def by auto
qed


end

end

end



 