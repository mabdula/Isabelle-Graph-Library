theory IDFS_Example
  imports IDFS Directed_Set_Graphs.Pair_Graph_RBT
begin

text \<open>The incremental DFS (DFS\_avoid) at the red-black-tree backend, with its code
equations. Split out of DDFS\_Example.thy so that executable users of the incremental DFS
do not depend on DDFS.\<close>

section \<open>Generic DFS\_avoid interpretation (axioms-free skeleton pattern)\<close>

global_interpretation idfs: DFS_avoid
  where insert = vset_insert and sel = sel and vset_empty = vset_empty
    and diff = vset_diff and lookup = lookup and empty = map_empty
    and delete = RBT_Map.delete and isin = isin and t_set = t_set
    and update = update and adjmap_inv = adj_inv
    and vset_delete = vset_delete and vset_inv = vset_inv
    and union = vset_union and inter = vset_inter
    and G = G and stack0 = p0 and vis0 = V0 and avoid = A0
    and Pv = P and level = lev
  for G p0 V0 A0 P lev
  defines find_idfs = idfs.av.DFS_skel_impl
    and   av_found_rbt = idfs.av_found
    and   neighbourhood_idfs = idfs.Graph.neighbourhood
    and   avoid_impl_rbt = idfs.avoid_final_state_impl
    and   avoid_initial_rbt = idfs.avoid_initial_state
    and   vset_of_list_rbt = idfs.vset_of_list
  using G.Pair_Graph_Specs_axioms RBT.Set2_axioms
  by (auto intro!: DFS_avoid.intro
           simp: adj_inv_def map_empty_def vset_inv_def RBT_Set.empty_def)

lemmas find_idfs_code[code] =
  idfs.av.DFS_skel_impl.simps[folded find_idfs_def[folded av_found_rbt_def],
    unfolded idfs.av_on_found_def idfs.av_on_empty_def
             idfs.av_on_backtrack_def]
lemmas av_found_rbt_code[code] = idfs.av_found_def

text \<open>Routing lemmas for the IDFS/DFS\_avoid code-equation chain.

Note: The fold find\_idfs\_def[folded av\_found\_rbt\_def] transforms find\_idfs G A0 P into
idfs.av.DFS\_skel\_impl G A0 P (at the term level), allowing avoid\_impl\_rbt to be routed
through find\_idfs which already has code equations via find\_idfs\_code.\<close>

lemmas avoid_impl_rbt_code[code] =
  idfs.avoid_final_state_impl_def[folded find_idfs_def[folded av_found_rbt_def]]
lemmas avoid_initial_rbt_code[code] = idfs.avoid_initial_state_def
lemmas vset_of_list_rbt_code[code] = idfs.vset_of_list_def

end
