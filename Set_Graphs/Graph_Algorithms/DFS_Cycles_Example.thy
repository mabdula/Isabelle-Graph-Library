theory DFS_Cycles_Example
  imports DFS_Cycles Directed_Set_Graphs.Pair_Graph_RBT
begin

global_interpretation dfs_cycle_aux: DFS_Aux_Skel
  where empty = empty
and delete = delete
and insert = insert_rbt
and isin = isin
and t_set = Tree2.set_tree
and sel = sel
and update = update
and adjmap_inv = M.invar
and vset_empty = Leaf
and vset_delete = delete_rbt
and vset_inv = vset_inv
and union = union_rbt
and inter = inter_rbt
and diff = diff_rbt
and lookup = lookup
and s = s and G = G for s G
defines initial_state_aux = dfs_cycle_aux.initial_state
and dfs_aux = dfs_cycle_aux.aux.DFS_skeleton_impl
and dfs_aux_found = dfs_cycle_aux.aux_found
and neighbourhood = dfs_cycle_aux.neighbourhood'
  apply unfold_locales (*unfold_locales doesn't finish it due to different invariants used in
                         Set2_Join vs Set instantiations*) 
  by (simp add: vset_inv_def RBT.set_tree_union RBT.set_tree_inter RBT.set_tree_diff 
                RBT.bst_union RBT.inv_union RBT.bst_inter RBT.inv_inter RBT.bst_diff RBT.inv_diff)+

text \<open>The partial-function unfolding equation with the callbacks inlined, as a code equation.\<close>
lemmas dfs_aux_code[code] =
  dfs_cycle_aux.aux.DFS_skeleton_impl.simps[folded dfs_aux_def[folded dfs_aux_found_def],
    unfolded dfs_cycle_aux.aux_on_found_def dfs_cycle_aux.aux_on_empty_def
      dfs_cycle_aux.aux_on_backtrack_def]

text\<^marker>\<open>provenance ai\<close> \<open>The neighbourhood lookup the found test calls, as a code equation.\<close>
lemmas\<^marker>\<open>provenance ai\<close> neighbourhood_code[code] = G.neighbourhood_def[folded neighbourhood_def]

global_interpretation dfs_cycles: DFS_Cycles_Skel
  where empty = empty
and delete = delete
and insert = insert_rbt
and isin = isin
and t_set = Tree2.set_tree
and sel = sel
and update = update
and adjmap_inv = M.invar
and vset_empty = Leaf
and vset_delete = delete_rbt
and vset_inv = vset_inv
and union=union_rbt
and inter = inter_rbt
and diff = diff_rbt
and lookup = lookup
and dfs_aux = "\<lambda> s. dfs_aux G (initial_state_aux s)"
and V = V and G = G for V G
defines initial = dfs_cycles.initial_state
and find_cycles_by_dfs = dfs_cycles.DFS_Cycles_impl
  by unfold_locales

text\<^marker>\<open>provenance ai\<close> \<open>The correctness theorems of the sweep, for the executable instance on
  red-black trees.\<close>

lemma\<^marker>\<open>provenance ai\<close> find_cycles_by_dfs_correct:
  assumes "G.graph_inv G"
      and "G.finite_graph G"
      and "G.finite_vsets G"
      and "vset_inv V"
      and "t_set V = dVs (G.digraph_abs G)"
      and "\<And>x y. (x, y) \<in> G.digraph_abs G \<Longrightarrow> (y, x) \<in> G.digraph_abs G"
      and "\<And>x. x \<in> dVs (G.digraph_abs G) \<Longrightarrow> (x, x) \<notin> G.digraph_abs G"
  shows "DFS_Cycles_state.cycle (find_cycles_by_dfs V G initial) \<longleftrightarrow>
           (\<exists>c. cycle' (G.digraph_abs G) c)"
proof -
  have ax: "DFS_Cycles.DFS_Cycles_axioms isin t_set M.invar Leaf vset_inv lookup G V"
    using assms unfolding dfs_cycles.DFS_Cycles_axioms_def by blast
  have aux: "DFS_Cycles.dfs_aux_axioms isin t_set Leaf vset_inv lookup G
               (\<lambda>s. dfs_aux G (initial_state_aux s)) DFS_skeleton_state.seen DFS_dircycle_state.cycle"
    by (rule dfs_cycles.dfs_aux_axioms_skel_impl[OF ax]) (simp only: dfs_aux_def initial_state_aux_def)
  have impl: "find_cycles_by_dfs V G initial = dfs_cycles.DFS_Cycles V G initial"
    using dfs_cycles.DFS_Cycles_impl_same dfs_cycles.initial_state_props(6)[OF ax aux] by blast
  show ?thesis
    unfolding impl
    using dfs_cycles.DFS_Cycles_correct_1[OF ax aux] dfs_cycles.DFS_Cycles_correct_2[OF ax aux]
    by blast
qed

definition "edges = [(0::nat, 1::nat), (0, 2), (2, 3), (2,4), (2,1), (1,5), (5,8), (8,7), (7,1),
                     (7,2), (7,4), (4,3), (3,4), (3,3), (9, 8), (8, 1), (4,5), (5,10)]"

definition "G = a_graph edges"

definition "V = foldr (\<lambda> x tree. insert_rbt x  tree) (vertices edges) Leaf"

value edges
value "vertices edges"

value G
value V

value "initial_state_aux (1::nat)"
value "dfs_aux G (initial_state_aux (9::nat))"

value "find_cycles_by_dfs V G initial"

hide_const G V edges a_graph
end
