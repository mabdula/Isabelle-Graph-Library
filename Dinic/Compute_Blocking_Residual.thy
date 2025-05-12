theory Compute_Blocking_Residual
  imports DFS_Collect_Backtrack_Example Compute_Blocking_Simple "HOL-Library.Product_Lexorder"
begin

global_interpretation blocking_simple: blocking_simple where insert = vset_insert and
 sel = sel and  vset_empty = vset_empty and  diff = vset_diff and
 lookup = lookup and empty = map_empty and delete=delete and isin = isin and t_set=t_set
and update=update and adjmap_inv = adj_inv and vset_delete= vset_delete
and vset_inv = vset_inv and union=vset_union and inter=vset_inter 
and flow_lookup = lookup
and flow_empty = Leaf
and flow_update=update
and flow_delete=delete
and flow_invar=adj_inv
and G = G and
t = t and
s = s and
find_path = find_path and
u = u
for G s t find_path u
defines blocking_simple_loop=blocking_simple.compute_blocking_loop_impl
and     blocking_simple_initial=blocking_simple.initial_state
and add_flow_simple=blocking_simple.add_flow
and delete_edge=blocking_simple.delete_edge
  by(auto intro!: blocking_simple.intro
           simp add: dfs.Graph.Pair_Graph_Specs_axioms  dfs.set_ops.Set2_axioms
                      M.Map_axioms[simplified RBT_Set.empty_def adj_inv_def[symmetric]])

definition "find_path F s t = 
   (if neighbourhood F s = vset_empty then None
    else let final_state = dfs_del_dead_impl F t ( dfs_backtrack_initial_state s)
         in  (case return final_state of NotReachable \<Rightarrow> None |
                                         Reachable    \<Rightarrow> 
              Some (rev (stack final_state), backtrack final_state)))"

value "find_path G 0 10"
value "find_path G 0 6"

value "blocking_simple_initial G"
value "find_path G 0 10"
value "blocking_simple_loop 0 10 find_path (\<lambda> e. 4) (blocking_simple_initial G)"
value "inorder (flow (blocking_simple_loop 0 10 find_path (\<lambda> e. 4) (blocking_simple_initial G)))"

hide_const G edges

lemma find_path_correct:
assumes "dfs.Graph.graph_inv F" "dfs.Graph.finite_graph F" "dfs.Graph.finite_vsets F" "s \<noteq> t"
shows "\<exists>p. vwalk_bet (dfs.Graph.digraph_abs F) s p t \<Longrightarrow>
       \<exists>p del. vwalk_bet (dfs.Graph.digraph_abs F) s p t \<and> find_path F s t = Some (p, del)"
       (is "?asm1 \<Longrightarrow> ?thesis1")
      "find_path F s t = Some (p, dlt) \<Longrightarrow>
       acyc (dfs.Graph.digraph_abs F) \<Longrightarrow>
       vwalk_bet (dfs.Graph.digraph_abs F) s p t \<and>
       distinct p \<and>
       (\<forall>e\<in>set dlt. \<nexists>p. e \<in> set (edges_of_vwalk p) \<and> vwalk_bet (dfs.Graph.digraph_abs F) s p t)"
       (is "?asm2 \<Longrightarrow> ?asm3 \<Longrightarrow> ?thesis2")
proof(all \<open>cases "neighbourhood F s = vset_empty"\<close>)
 show  "?asm1 \<Longrightarrow> ?thesis1" if asy: "neighbourhood F s = vset_empty"
   using assms(4) dfs.Graph.vset.set.set_empty vwalk_then_edge[of "dfs.Graph.digraph_abs F" s _  t] 
   by(unfold dfs.Graph.are_connected_abs[OF assms(1), symmetric] asy) blast
  show  "?asm2 \<Longrightarrow> ?asm3 \<Longrightarrow> ?thesis2"  if asy: "neighbourhood F s = vset_empty"
    using asy by(simp add: find_path_def)
  assume s_neighb_non_empty:"neighbourhood F s \<noteq> vset_empty"
  have DFS_axioms: "DFS.DFS_axioms isin t_set adj_inv vset_empty vset_inv lookup F s"
    using RBT_Set.empty_def Tree2.eq_set_tree_empty assms(1,2,3)  s_neighb_non_empty
    by(auto intro:dfs.Graph.neighbourhood_absD simp add: dfs.DFS_axioms_def)
  have dfs_thms: "DFS_thms map_empty RBT_Map.delete vset_insert isin t_set sel update adj_inv vset_empty vset_delete vset_inv
     vset_union vset_inter vset_diff lookup F s"
    by(auto intro!: DFS_thms.intro DFS_thms_axioms.intro simp add: dfs.DFS_axioms DFS_axioms)
  have same_final_state: "dfs_del_dead_impl F t ( dfs_backtrack_initial_state s) =
                         dfs.DFS_collect_backtrack F t ( dfs_backtrack_initial_state s)"
    by(simp add: dfs_del_dead_impl_def dfs_backtrack_initial_state_def
                 DFS_thms.DFS_collect_backtrack_impl_same_on_initial[OF dfs_thms]) 
  have same_final_as_ordinary: "to_ordinary_DFS_state 
                    (dfs.DFS_collect_backtrack F t ( dfs_backtrack_initial_state s)) =
                    dfs.DFS F t ( dfs.initial_state s)"
    using DFS_thms.same_as_old_dfs_on_initial[OF dfs_thms]
    by(simp add: dfs_backtrack_initial_state_def)
  note DFS_correct_1 = DFS_thms.DFS_correct_1_weak[OF dfs_thms]
  note DFS_correct_2 = DFS_thms.DFS_correct_2[OF dfs_thms]
  show  "?asm1 \<Longrightarrow> ?thesis1"
  proof(goal_cases)
    case 1
    hence dfs_reachable:"DFS_state.return (dfs.DFS F t (dfs.initial_state s)) = Reachable"
      using DFS_correct_1 return.exhaust by blast
    define final_state where "final_state = dfs_del_dead_impl F t ( dfs_backtrack_initial_state s)"
    have dfs_backtrack_reachable: "return final_state =  Reachable"
      using  dfs_reachable same_final_as_ordinary[symmetric]  same_final_state
      by(auto simp add: final_state_def)
    show ?case 
    proof(rule exI[of _ "rev (stack final_state)"], rule exI[of _ "backtrack final_state"],
            rule conjI, goal_cases)
      case 2
      then show ?case
        using s_neighb_non_empty dfs_backtrack_reachable 
        by(auto simp add: find_path_def  final_state_def split: return.split)
    next
      case 1
      then show ?case 
        using  DFS_correct_2[OF dfs_reachable] same_final_as_ordinary[symmetric]
        by(simp add: final_state_def  same_final_state) 
    qed 
  qed
  show  "?asm2 \<Longrightarrow> ?asm3 \<Longrightarrow> ?thesis2"
  proof(goal_cases)
    case 1
     define final_state where "final_state = dfs_del_dead_impl F t ( dfs_backtrack_initial_state s)"
     have dfs_backtrack_result: "return final_state =  Reachable" "rev (stack final_state) = p" 
                                "backtrack final_state = dlt"
     apply(all \<open>rule case_split[of "DFS_Collect_Backtrack_Example.neighbourhood F s = vset_empty"]\<close>)
     apply(all \<open>rule return.exhaust[of "DFS_backtrack_state.return (dfs_del_dead_impl
                         F t (dfs_backtrack_initial_state s))"]\<close>)
     using "1"(1) 
     by(auto simp add: final_state_def find_path_def) 
   have "vwalk_bet (dfs.Graph.digraph_abs F) s p t"
     using DFS_correct_2[of t]  dfs_backtrack_result(1) dfs_backtrack_result(2)       
     by(auto simp add: final_state_def same_final_state same_final_as_ordinary[symmetric])
   moreover have "distinct p" 
     using DFS_thms.invar_seen_stack_holds[OF dfs_thms 
                                    DFS_thms.initial_state_props(6,1,3)[OF dfs_thms], of t]
     by(simp add: dfs.invar_seen_stack_def same_final_as_ordinary[symmetric]
                   dfs_backtrack_result(2)[symmetric] final_state_def same_final_state)
   moreover have "e\<in>set dlt \<Longrightarrow>
                  \<nexists>p. e \<in> set (edges_of_vwalk p) \<and> vwalk_bet (dfs.Graph.digraph_abs F) s p t" for e
     using  same_final_state  "1"(2) DFS_thms.dfs_backtrack_final(5)[OF dfs_thms, of t]       
     by(simp add: dfs.invar_dfs_backtrack_5_def acyc_def  dfs_backtrack_initial_state_def 
                  final_state_def  dfs_backtrack_result(2,3)[symmetric])     
   ultimately show ?case by auto
 qed
qed

interpretation blocking_simple_thms: blocking_simple_thms where insert = vset_insert and
 sel = sel and  vset_empty = vset_empty and  diff = vset_diff and
 lookup = lookup and empty = map_empty and delete=delete and isin = isin and t_set=t_set
and update=update and adjmap_inv = adj_inv and vset_delete= vset_delete
and vset_inv = vset_inv and union=vset_union and inter=vset_inter 
and flow_lookup = lookup
and flow_empty = Leaf
and flow_update=update
and flow_delete=delete
and flow_invar=adj_inv
and G = G and
t = t and
s = s and
find_path = find_path and
u = u
for G s t u
  apply(auto intro!: blocking_simple_thms.intro) 
  apply (simp add: blocking_simple.flow_map.Map_axioms blocking_simple.intro
      dfs.Graph.Pair_Graph_Specs_axioms dfs.set_ops.Set2_axioms)
  apply(rule blocking_simple_thms_axioms.intro)