theory DFS_Reach_Skel_Refine_Example
  imports DFS_Reach_Skel_Refine DFS_Reach_Skel_Example
begin

text \<open>The refined reachability DFS at the red-black-tree instantiation, run side by side with
the plain one of \<^theory>\<open>Graph_Algorithms_Dev.DFS_Reach_Skel_Example\<close> on the same graph: same
verdicts --- it does the same thing --- computed off the state-carried pruned map instead of a
per-step set difference. Only the \<^emph>\<open>function layer\<close> is interpreted: the reasoning layer's
\<open>sel_cong\<close> is a genuine extra requirement on the vset ADT (a set-determined \<open>sel\<close>) which the
stock red-black-tree \<open>sel\<close> --- the root label --- does not satisfy. The run-level agreement
theorems live in \<^locale>\<open>DFS_Reach_Refine_thms\<close>; this theory is the executable demonstration.\<close>

global_interpretation rdfs: DFS_Reach_Refine where insert = vset_insert and
 sel = sel and vset_empty = vset_empty and diff = vset_diff and
 lookup = lookup and empty = map_empty and delete = delete and isin = isin and t_set = t_set
and update = update and adjmap_inv = adj_inv and vset_delete = vset_delete
and vset_inv = vset_inv and union = vset_union and inter = vset_inter and G = F and
t = t and s = s and R = R for F R t s
defines rdfs_initial_state = rdfs.rreach_initial_state and
rdfs_impl = rdfs.rr.DFS_skeleton_refine_impl and
rreach_found = rdfs.rreach_found and
rdfs_del_preds = rdfs.del_preds and
rdfs_del_in_edges = rdfs.del_in_edges
  using G.Pair_Graph_Specs_axioms RBT.Set2_axioms
  by(auto intro!: DFS_Reach_Refine.intro DFS_Reach.intro
          simp add: edge_map_update_def RBT_Set.empty_def adj_inv_def map_empty_def
                    vset_inv_def)

text \<open>The partial-function unfolding equation cannot serve as a code equation directly (its head
carries the instantiated callbacks as compound arguments), so we restate it once at the concrete
instance, with the callbacks inlined.\<close>
lemmas rdfs_impl_code[code] =
  rdfs.rr.DFS_skeleton_refine_impl.simps[folded rdfs_impl_def[folded rreach_found_def],
    unfolded rdfs.rreach_on_found_def rdfs.rreach_on_empty_def rdfs.rreach_on_backtrack_def
             rdfs.rreach_on_push_def, folded DFS_Reach_Skel_Example.neighbourhood_def]

text \<open>The graph of \<open>DFS_Reach_Skel_Example\<close>, and its reverse map --- the predecessors, built
once by swapping every edge --- for the in-edge deletion.\<close>
definition "edges = [(0::nat, 1::nat), (0, 2), (2, 3), (2,4), (2,1), (1,5), (5,8), (8,7), (7,1),
                     (7,2), (7,4), (4,3), (3,4), (3,3), (9, 8), (8, 1), (4,5), (5,10)]"
definition "G = a_graph edges"
definition "RG = a_graph (map prod.swap edges)"

value "rdfs_initial_state G RG (0::nat)"

text \<open>Same verdicts as the plain \<open>dfs_impl\<close>, side by side: 9 is not reachable from 0, 3 and 10
are, and from 9 one cannot reach 0.\<close>
value "(return (dfs_impl G 9 (dfs_initial_state 0)),
        return (rdfs_impl RG 9 (rdfs_initial_state G RG 0)))"
value "(return (dfs_impl G 3 (dfs_initial_state 0)),
        return (rdfs_impl RG 3 (rdfs_initial_state G RG 0)))"
value "(return (dfs_impl G 10 (dfs_initial_state 0)),
        return (rdfs_impl RG 10 (rdfs_initial_state G RG 0)))"
value "(return (dfs_impl G 0 (dfs_initial_state 9)),
        return (rdfs_impl RG 0 (rdfs_initial_state G RG 9)))"

hide_const edges G RG

end
