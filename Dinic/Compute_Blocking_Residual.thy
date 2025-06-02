theory Compute_Blocking_Residual                 
  imports Graph_Algorithms_Dev.DFS_Collect_Backtrack_Example Compute_Blocking_Simple
          "HOL-Library.Product_Lexorder"
    Graph_Algorithms_Dev.BFS_Example Graph_Algorithms_Dev.RBT_Map_Extension
begin

lemma same_graph_consts: "G.graph_inv = dfs.Graph.graph_inv"
  "G.digraph_abs = dfs.Graph.digraph_abs"
  "BFS_Example.neighbourhood = dfs.Graph.neighbourhood"
  "DFS_Collect_Backtrack_Example.neighbourhood = 
                          dfs.Graph.neighbourhood"
  "G.graph_inv = dfs.Graph.graph_inv"
  by (auto simp add: adj_inv_def RBT_Set.empty_def
      BFS_Example.neighbourhood_def DFS_Collect_Backtrack_Example.neighbourhood_def)

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
   (if DFS_Collect_Backtrack_Example.neighbourhood F s = vset_empty then None
    else let final_state = dfs_del_dead_impl F t ( dfs_backtrack_initial_state s)
         in  (case return final_state of NotReachable \<Rightarrow> None |
                                         Reachable    \<Rightarrow> 
              Some (rev (stack final_state), backtrack final_state)))" for F

value "find_path G 0 10"
value "find_path G 0 6"

value "blocking_simple_initial G"
value "find_path G 0 10"
value "blocking_simple_loop 0 10 find_path (\<lambda> e. 4) (blocking_simple_initial G)"
value "inorder (flow (blocking_simple_loop 0 10 find_path (\<lambda> e. 4) (blocking_simple_initial G)))"

hide_const G edges

lemma find_path_correct:
  fixes F
  assumes "dfs.Graph.graph_inv F" "dfs.Graph.finite_graph F" "dfs.Graph.finite_vsets F" "s \<noteq> t"
  shows "\<exists>p. vwalk_bet (dfs.Graph.digraph_abs F) s p t \<Longrightarrow>
       \<exists>p del. vwalk_bet (dfs.Graph.digraph_abs F) s p t \<and> find_path F s t = Some (p, del)"
    (is "?asm1 \<Longrightarrow> ?thesis1")
    and "find_path F s t = Some (p, dlt) \<Longrightarrow>
       acyc (dfs.Graph.digraph_abs F) \<Longrightarrow>
       vwalk_bet (dfs.Graph.digraph_abs F) s p t \<and>
       distinct p \<and>
       (\<forall>e\<in>set dlt. \<nexists>p. e \<in> set (edges_of_vwalk p) \<and> vwalk_bet (dfs.Graph.digraph_abs F) s p t)"
    (is "?asm2 \<Longrightarrow> ?asm3 \<Longrightarrow> ?thesis2")

proof(all \<open>cases "DFS_Collect_Backtrack_Example.neighbourhood F s = vset_empty"\<close>)
  show  "?asm1 \<Longrightarrow> ?thesis1" if asy: "DFS_Collect_Backtrack_Example.neighbourhood F s = vset_empty"
    using assms(4) dfs.Graph.vset.set.set_empty vwalk_then_edge[of "dfs.Graph.digraph_abs F" s _  t] 
    by(unfold dfs.Graph.are_connected_abs[OF assms(1), symmetric] asy) blast
  show  "?asm2 \<Longrightarrow> ?asm3 \<Longrightarrow> ?thesis2"  if asy: "DFS_Collect_Backtrack_Example.neighbourhood F s = vset_empty"
    using asy by(simp add: find_path_def)
  assume s_neighb_non_empty:"DFS_Collect_Backtrack_Example.neighbourhood F s \<noteq> vset_empty"
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


locale blocking_level_residual_spec =
  flow_network_spec where fst = fst  +
  Map_realising: Map realising_edges_empty 
  "realising_edges_update::('v\<times> 'v) \<Rightarrow> ('e Redge) list \<Rightarrow> 'realising_type \<Rightarrow> 'realising_type"
  realising_edges_delete realising_edges_lookup realising_edges_invar +
  Map_residual_flow: Map residual_flow_empty
  "residual_flow_update::'e Redge \<Rightarrow> real \<Rightarrow> 'resflow_map \<Rightarrow> 'resflow_map"
  residual_flow_delete residual_flow_lookup residual_flow_invar

for fst::"'e \<Rightarrow> 'v::linorder" and realising_edges_empty realising_edges_update
  realising_edges_delete realising_edges_lookup realising_edges_invar
  residual_flow_delete residual_flow_lookup residual_flow_invar residual_flow_empty
  residual_flow_update  +
fixes s t ::'v
  and   es::"'e list"
  and   \<f>::"'e \<Rightarrow> real"
begin

definition "pos_es = filter (\<lambda> e. rcap \<f> e > 0) (map F es @ map B es)"
  (*Turn later into join/projection/collapsing functions.*)
definition "realising_edges_general list =
           (foldr (\<lambda> e found_edges. let ee = to_vertex_pair e in
                     (case realising_edges_lookup found_edges ee of 
                      None \<Rightarrow> realising_edges_update ee [e] found_edges
                     |Some ds \<Rightarrow> realising_edges_update ee (e#ds) found_edges))
            list realising_edges_empty)"

definition "realising_edges = realising_edges_general pos_es"

definition "E_simple = foldr (\<lambda> e acc. add_edge acc (prod.fst e) (prod.snd e))
                          (map to_vertex_pair pos_es) empty"
definition "u_simple e = sum_list (map (\<lambda> e. real_of_ereal (rcap \<f> e)) 
                       (case realising_edges_lookup realising_edges e of None \<Rightarrow> []| 
                        Some ees \<Rightarrow> ees))"

definition "level_simple = parents (bfs_impl E_simple (bfs_initial_state 
                          (vset_insert s Pair_Graph_RBT.vset_empty)))"

definition "blocking_flow_simple = 
      (if neighbourhood E_simple s = vset_empty 
       then None
       else let f = blocking_state.flow (blocking_simple_loop s t find_path u_simple 
                 (blocking_simple_initial level_simple))
            in if f = empty then None
            else Some f)"
  (*later, use a split function.*)
definition "residual_add_flow f e \<gamma> = 
residual_flow_update e ((abstract_real_map (residual_flow_lookup f) e) + \<gamma>) f"

(*later, use a split function.*)

definition "split_flow_single e fl acc= 
prod.fst (foldl (\<lambda> (resf, f) ee . 
       let \<gamma> = min (real_of_ereal (rcap \<f> ee)) f
       in (residual_add_flow resf ee \<gamma>, f -\<gamma>))
        (acc, fl) (the (realising_edges_lookup realising_edges e)))"

definition "find_blocking_flow =
    (case blocking_flow_simple 
     of None \<Rightarrow> None |
        Some flw \<Rightarrow>
     Some (
       rbt_map_fold flw (\<lambda> e fl acc. split_flow_single e fl acc) 
         residual_flow_empty
      ))"
  (*
definition "residual_blocking_flow =
    (case blocking_flow_simple 
     of None \<Rightarrow> None |
        Some flw \<Rightarrow>
     Some (
       foldr 
          (\<lambda> e acc. 
             prod.fst 
              (
               foldr 
                 (\<lambda> ee (resf, f). 
                  let \<gamma> = min (real_of_ereal (rcap \<f> ee)) (abstract_real_map (lookup f) e)
                  in (residual_add_flow resf ee \<gamma>, add_flow_simple f (-\<gamma>) e))
                 (the (realising_edges_lookup realising_edges e)) 
                 (acc, flw)
              )
          )
         (map to_vertex_pair pos_es)
         residual_flow_empty
      ))"*)
lemmas [code] =pos_es_def
  realising_edges_general_def
  realising_edges_def
  E_simple_def
  u_simple_def
  level_simple_def
  blocking_flow_simple_def
  residual_add_flow_def
  find_blocking_flow_def
  split_flow_single_def

end

locale blocking_level_residual= 
  blocking_level_residual_spec +
  flow_network+
  assumes es_props: "set es = \<E>" "distinct es"
  assumes s_neq_t: "s \<noteq> t"
  assumes finite_capacities: "\<And> e. e \<in> \<E> \<Longrightarrow> \<u> e < \<infinity>"
begin

lemma finite_rescaps: "e \<in> \<EE> \<Longrightarrow> rcap f e < \<infinity>"  "e \<in> \<EE> \<Longrightarrow> rcap f e > - \<infinity>"
  using finite_capacities 
  by(auto simp add:  \<EE>_def minus_ereal_def u_non_neg)

lemma finite_rescapsE: "e \<in> \<EE> \<Longrightarrow>(\<And> r. rcap f e  = ereal r \<Longrightarrow> P) \<Longrightarrow> P"
  using finite_rescaps[of e f] 
  by(cases "rcap f e" rule: real_of_ereal.cases) auto

lemma pos_es_props: "set pos_es = {e | e. e \<in> \<EE> \<and> rcap \<f> e > 0}"
  "distinct pos_es"
  by (auto intro!: distinct_filter inj_onI 
      simp add: pos_es_def \<EE>_def  distinct_map es_props)
    (*Use for projection*)
lemma realising_edges_invar_pres: "realising_edges_invar (realising_edges_general list)"
  unfolding realising_edges_general_def
  by(auto intro: foldr_invar 
      simp add: Map_realising.invar_empty Map_realising.invar_update realising_edges_general_def 
      split: option.split)
    (*Use for projection*)
lemma realising_edges_general_result_None_and_Some:
  assumes "(case realising_edges_lookup (realising_edges_general list) (u, v) 
            of Some ds \<Rightarrow> ds 
               | None \<Rightarrow> [])= ds"
  shows "set ds = {e | e. e \<in> set list \<and> to_vertex_pair e = (u, v)}"
  using assms
proof(induction list arbitrary: ds)
  case Nil
  then show ?case 
    by (auto simp add: realising_edges_general_def  Map_realising.map_empty 
        split: option.split)
next
  case (Cons a list ds)
  show ?case 
    using Map_realising.map_update[OF  realising_edges_invar_pres] Cons(1)[OF refl] 
    by (auto intro: realising_edges_invar_pres 
        simp add: Map_realising.map_update realising_edges_general_def Cons(2)[symmetric] 
        split: option.split)
qed
  (*Use for projection*)
lemma realising_edges_general_result_distinct:
  assumes "distinct list"
    "(case realising_edges_lookup (realising_edges_general list) (u, v) 
            of Some ds \<Rightarrow> ds 
               | None \<Rightarrow> [])= ds"
  shows "distinct ds"
  using assms
proof(induction list arbitrary: ds u v)
  case Nil
  then show ?case 
    by (auto simp add: realising_edges_general_def  Map_realising.map_empty 
        split: option.split)
next
  case (Cons e list ds u v)
  hence distlist: "distinct list" by auto
  show ?case 
    using  realising_edges_general_result_None_and_Some[OF Cons(3)]  Cons(1)[OF distlist refl, of u v]
    unfolding realising_edges_general_def Cons(3)[symmetric]
    apply(subst (asm) foldr_Cons, subst (asm) o_apply)
    apply(subst (asm) foldr_Cons, subst (asm) o_apply)
    apply(subst foldr_Cons, subst  o_apply)
    unfolding realising_edges_general_def[symmetric]
    using Cons(1)[OF distlist refl, of u v]  Cons.prems(1) 
      realising_edges_general_result_None_and_Some[OF refl, of list u v]
    by (auto simp add: realising_edges_general_def[symmetric] 
        Map_realising.map_update[OF  realising_edges_invar_pres , of "to_vertex_pair e" _ list] 
        split: option.split)
qed
  (*Use for projection*)
lemma realising_edges_general_result:
  assumes "realising_edges_lookup (realising_edges_general list) (u, v) = Some ds"
  shows "set ds = {e | e. e \<in> set list \<and> to_vertex_pair e = (u, v)}"
  using realising_edges_general_result_None_and_Some[of list u v ds] assms
  by simp
    (*Use for projection*)
lemma realising_edges_result:
  "realising_edges_lookup realising_edges d = Some ds \<Longrightarrow>
    set ds = {e |e. e \<in> set pos_es \<and> to_vertex_pair e = d}"
  "realising_edges_lookup realising_edges d= Some ds \<Longrightarrow>
    distinct ds"
  "realising_edges_lookup realising_edges d = None \<Longrightarrow>
    {e |e. e \<in> set pos_es \<and> to_vertex_pair e = d} = {}"
  using realising_edges_general_result_distinct[OF pos_es_props(2) refl, of "prod.fst d" "prod.snd d"] 
    realising_edges_general_result_None_and_Some[OF refl] 
  by(all \<open>cases d\<close>)(force simp add: realising_edges_def realising_edges_general_result)+
    (*Use for projection*)
lemma E_simple_props: "dfs.Graph.graph_inv E_simple" (is ?goal1)
  "dfs.Graph.finite_graph E_simple" (is ?goal2)
  "dfs.Graph.finite_vsets E_simple" (is ?goal3)
  "dfs.Graph.digraph_abs E_simple = to_vertex_pair ` (set pos_es)" (is ?goal4)
proof-
  define init where "init = (vset_empty:: (('b \<times> ('b \<times> color) tree) \<times> color) tree)"
  define list where "list = pos_es"
  have init_props: "dfs.Graph.graph_inv init" "dfs.Graph.finite_graph init" 
    "dfs.Graph.finite_vsets init"
    "dfs.Graph.digraph_abs init = to_vertex_pair ` (set [])"
    by (auto simp add: G.graph_inv_empty adj_inv_def init_def
        M.map_empty dfs.Graph.finite_graphI  empty_digraph_abs)

  have "?goal1 \<and> ?goal2 \<and> ?goal3 \<and> ?goal4"
    unfolding E_simple_def init_def[symmetric] list_def[symmetric]
    using init_props 
    by(induction list)(auto intro: dfs.Graph.finite_graph_add_edge)
  thus ?goal1 ?goal2 ?goal3 ?goal4 by auto
qed
lemma distinct_pairs_no_reaising_in_common:
  "e \<noteq> d \<Longrightarrow>
  {x. \<exists>uu. Some uu = realising_edges_lookup realising_edges e \<and> x \<in> set uu} \<inter>
  {x. \<exists>uu. Some uu = realising_edges_lookup realising_edges d \<and> x \<in> set uu} =
       {}"
  using realising_edges_result(1)
  by(cases "realising_edges_lookup realising_edges e",
      all \<open>cases "realising_edges_lookup realising_edges d"\<close>)
    auto

(*Use for projection*)
lemma u_simple_is:
  "u_simple ee = (\<Sum>e\<in>{e |e. e \<in> set pos_es \<and> to_vertex_pair e = ee}.
                          real_of_ereal \<uu>\<^bsub>\<f>\<^esub>e)"
  using realising_edges_result[of ee]
  by(auto intro!: comm_monoid_add_class.sum.neutral 
      split: option.split 
      simp add: u_simple_def,
      simp only: comm_monoid_add_class.sum.distinct_set_conv_list[symmetric])

lemma u_strictly_pos:
  "e \<in> dfs.Graph.digraph_abs E_simple \<Longrightarrow> u_simple e > 0"
  using finite_rescaps(1) zero_less_real_of_ereal 
  by  (cases e)
    (auto intro!: ordered_comm_monoid_add_class.sum_pos 
      intro: finite_rescapsE 
      simp add: u_simple_is pos_es_props(1) E_simple_props(4) finite_\<EE>)

lemma u_non_neg:
  "u_simple e \<ge> 0"
  by(cases e)
    (auto intro!: ordered_comm_monoid_add_class.sum_nonneg
      simp add: u_simple_is pos_es_props(1) E_simple_props(4) finite_\<EE> real_of_ereal_pos)

lemma bfs_axiom: "neighbourhood E_simple s \<noteq>vset_empty \<Longrightarrow>
                 BFS.BFS_axiom isin t_set M.invar \<langle>\<rangle> vset_inv lookup
                   (vset_insert s Pair_Graph_RBT.vset_empty) E_simple"
  unfolding BFS.BFS_axiom_def[OF bfs.BFS_axioms]
  using E_simple_props(1-3) 
  by (auto simp add: dfs.Graph.vset.set.set_insert[OF  dfs.Graph.vset.set.invar_empty]
      dfs.Graph.vset.set.set_empty dfs.Graph.vset.set.invar_empty
      Tree2.finite_set_tree[of "DFS_Collect_Backtrack_Example.neighbourhood 
                                                  E_simple _", 
        simplified dfs.Graph.neighbourhood_abs[OF  E_simple_props(1)]]
      same_graph_consts(1-3))

lemma e_leaving_s_in_level_graph:
  "e\<in>\<EE> \<Longrightarrow> 0 < \<uu>\<^bsub>\<f>\<^esub>e \<Longrightarrow> fstv e = s \<Longrightarrow> sndv e \<noteq> s \<Longrightarrow>
   to_vertex_pair e \<in> level_graph (to_vertex_pair ` {e |e. e \<in> \<EE> \<and> 0 < \<uu>\<^bsub>\<f>\<^esub>e}) {s} -
    {(u, v) |u v. distance (to_vertex_pair ` {e |e. e \<in> \<EE> \<and> 0 < \<uu>\<^bsub>\<f>\<^esub>e}) s u = \<infinity>}"
  apply(cases "to_vertex_pair e")
  by(subst distance_0I[OF refl, of "fstv e"] |
      auto intro!: in_level_graphI exI[of _e]  exI[of _ "0::nat"] 
      intro: distance_1I 
      simp add: enat_0  image_iff distance_set_single_source to_vertex_pair_fst_snd)+

lemma has_elem_not_emptyI:"x \<in> A \<Longrightarrow> A \<noteq> {}"
  by auto

lemma flow_network_axioms_for_simple_graph:
  "(\<exists> e\<in> \<EE>. rcap \<f> e > 0 \<and> fstv e = s \<and> sndv e \<noteq> s) \<Longrightarrow>
         flow_network prod.fst prod.snd id Pair (\<lambda>x. ereal (u_simple x))
     (level_graph (dfs.Graph.digraph_abs E_simple) {s} -
      {(u, v) |u v. distance (dfs.Graph.digraph_abs E_simple) s u = \<infinity>})"
  apply(rule flow_network.intro)
   apply(rule  multigraph.intro)
      apply (force simp add: id_def, force simp add: id_def)
    apply(rule finite_Diff)
    apply(rule finite_subset[OF level_graph_subset_graph])
    apply(simp add: E_simple_props(4))
  using has_elem_not_emptyI[OF  e_leaving_s_in_level_graph]
  by(auto intro: flow_network_axioms.intro has_elem_not_emptyI
      simp add: u_non_neg  E_simple_props(4) pos_es_props(1))

abbreviation "simple_level_graph_abstract ==  (level_graph (dfs.Graph.digraph_abs E_simple) {s}
     - {(u, v) | u v. distance  (dfs.Graph.digraph_abs E_simple) s u = \<infinity>})"
abbreviation "is_blocking_flow_simple == 
flow_network_spec.is_blocking_flow prod.fst prod.snd id simple_level_graph_abstract u_simple"

lemma blocking_flow_simple_correct:

"blocking_flow_simple = None \<Longrightarrow> \<nexists> p. vwalk_bet (dfs.Graph.digraph_abs E_simple) s p t" (is "?none \<Longrightarrow> ?nowalk")
"blocking_flow_simple = Some f \<Longrightarrow>\<exists> p. vwalk_bet (dfs.Graph.digraph_abs E_simple) s p t" (is "?some \<Longrightarrow> ?walk")
"blocking_flow_simple = Some f \<Longrightarrow> is_blocking_flow_simple s t (abstract_real_map (lookup f))" (is "?some \<Longrightarrow> ?blocking_flow")
"blocking_flow_simple = Some f \<Longrightarrow>\<exists>e\<in>\<EE>. 0 < \<uu>\<^bsub>\<f>\<^esub>e \<and> fstv e = s \<and> sndv e \<noteq> s" (is "?some \<Longrightarrow>?leaving_e")
"blocking_flow_simple = Some f \<Longrightarrow> dom (lookup f) \<subseteq> simple_level_graph_abstract"
"blocking_flow_simple = Some f \<Longrightarrow> adj_inv f"
proof(all \<open>cases "neighbourhood E_simple s = vset_empty"\<close>)
  show "?none \<Longrightarrow> neighbourhood E_simple s = vset_empty \<Longrightarrow> ?nowalk"
    by (auto simp add: G.source_of_path_neighb_non_empty RBT_Set.empty_def s_neq_t
        vwalk_bet_diff_verts_length_geq_2  dfs.Graph.neighbourhood_def
        DFS_Collect_Backtrack_Example.neighbourhood_def
        blocking_flow_simple_def same_graph_consts(3))
  show "?some \<Longrightarrow> neighbourhood E_simple s = vset_empty \<Longrightarrow> ?walk"
    "?some \<Longrightarrow> neighbourhood E_simple s = vset_empty \<Longrightarrow> ?blocking_flow"
    "?some \<Longrightarrow> BFS_Example.neighbourhood E_simple s = vset_empty \<Longrightarrow> \<exists>e\<in>\<EE>. 0 < \<uu>\<^bsub>\<f>\<^esub>e \<and> fstv e = s \<and> sndv e \<noteq> s"
    "?some \<Longrightarrow> BFS_Example.neighbourhood E_simple s = vset_empty \<Longrightarrow>
         dom (lookup f) \<subseteq> simple_level_graph_abstract"
    "?some \<Longrightarrow> BFS_Example.neighbourhood E_simple s = vset_empty \<Longrightarrow>
         adj_inv f"
    by (auto simp add:  blocking_flow_simple_def )   
  assume assm1: "neighbourhood E_simple s \<noteq> vset_empty"
  note bfs_axiom = bfs_axiom[OF assm1]
  have level_siple_is: "(bfs_impl E_simple (bfs_initial_state 
                          (vset_insert s Pair_Graph_RBT.vset_empty))) = 
                       (bfs.BFS E_simple (bfs_initial_state 
                          (vset_insert s Pair_Graph_RBT.vset_empty)))"
    by (simp add: bfs.BFS_impl_same bfs_axiom)
  have sources: "t_set (vset_insert s vset_empty) = {s}"
    "s \<in> t_set (vset_insert s vset_empty)"
    by (auto simp add: dfs.Graph.vset.set.invar_empty dfs.Graph.vset.set.set_empty)
  note BFS_correct_1 = bfs.BFS_correct_1[OF bfs_axiom sources(2)]
  note BFS_correct_2 = bfs.BFS_correct_2[OF bfs_axiom]
  note BFS_correct_3 = bfs.BFS_correct_3[OF bfs_axiom sources(2)]
  note BFS_correct_4 = bfs.BFS_correct_4[OF bfs_axiom]
  note BFS_level_graph = bfs.BFS_level_graph[OF bfs_axiom]
  note bfs_initial_state_props = bfs.initial_state_props[OF bfs_axiom]
  have bfs_invar_1: "bfs.invar_1 (bfs.BFS E_simple (bfs_initial_state 
                          (vset_insert s Pair_Graph_RBT.vset_empty)))"
    using bfs.invar_1_holds[OF bfs_axiom] bfs_initial_state_props(1,4) by blast
  have bfs_invar_2: "bfs.invar_2 (vset_insert s Pair_Graph_RBT.vset_empty) 
                          E_simple (bfs.BFS E_simple (bfs_initial_state 
                          (vset_insert s Pair_Graph_RBT.vset_empty)))"
    by (simp add: bfs.invar_2_holds bfs_axiom bfs_initial_state_props(1))

  define prnts where "prnts =  parents ((bfs.BFS E_simple (bfs_initial_state 
                          (vset_insert s Pair_Graph_RBT.vset_empty))))"
  have acyc_bfs_result:
    "acyc (dfs.Graph.digraph_abs prnts)"
    using reachable_level_graph_acyclic
    by(force simp add: prnts_def bfs.BFS_level_graph[OF bfs_axiom, simplified same_graph_consts] acyc_def reachable_level_graph_def)

  have blocking_simple_thms: "blocking_simple_thms map_empty RBT_Map.delete vset_insert isin t_set sel 
                   update adj_inv vset_empty vset_delete vset_inv vset_union vset_inter vset_diff
                   lookup lookup \<langle>\<rangle> update RBT_Map.delete adj_inv prnts s t u_simple find_path"
  proof(rule  blocking_simple_thms.intro[OF blocking_simple.blocking_simple_axioms],
      rule blocking_simple_thms_axioms.intro, goal_cases)
    case 1
    then show ?case 
      using bfs_invar_1[simplified bfs.invar_1_def]
      by (simp add: adj_inv_def prnts_def)
  next
    case 2
    then show ?case 
      using bfs_invar_1[simplified bfs.invar_1_def]
      by (simp add: adj_inv_def prnts_def)
  next
    case 3
    then show ?case 
      using Tree2.finite_set_tree by blast
  next
    case 4
    then show ?case 
      using acyc_bfs_result by auto
  next
    case (5 e)
    then show ?case 
      using BFS_correct_4 
      by(cases e)(auto intro!: u_strictly_pos simp add: RBT_Set.empty_def prnts_def subset_iff)
  next
    case (6 e)
    then show ?case
      by (simp add: u_non_neg)
  next
    case 7
    then show ?case 
      by (simp add: s_neq_t)
  next
    case (8 F s t)
    then show ?case
      using find_path_correct(1) by blast
  next
    case (9 F s t p del)
    then show ?case 
      using find_path_correct(2) by blast
  qed

  note blocking_simple_correctness=blocking_simple_thms.correctness[OF blocking_simple_thms]

  show none_no_walk:"?none \<Longrightarrow> ?nowalk"
  proof(goal_cases)
    case 1
    hence flow_empty:"blocking_state.flow 
           (blocking_simple_loop s t find_path u_simple 
                 (blocking_simple_initial level_simple)) = empty"
      using assm1
      by (auto simp add:  blocking_flow_simple_def )
    have no_parent_path:"\<nexists>p. vwalk_bet (dfs.Graph.digraph_abs prnts) s p t"
      using flow_empty  blocking_simple_correctness(4) level_siple_is 
      by(intro blocking_simple_correctness(1)) 
        (auto simp add: blocking_simple.termination_same RBT_Set.empty_def blocking_simple_initial_def 
          level_simple_def  prnts_def)    
    show ?case 
    proof(rule ccontr, goal_cases)
      case 1
      have "\<exists>q . vwalk_bet (G.digraph_abs prnts) s q t"
        using  bfs.BFS_graph_path_implies_parent_path[OF bfs_axiom] 1 s_neq_t sources(1,2)
        by(force simp add: RBT_Set.empty_def  prnts_def)
      thus ?case
        using no_parent_path
        by (simp add: RBT_Set.empty_def)
    qed
  qed
  assume assms2: "blocking_flow_simple = Some f" "BFS_Example.neighbourhood E_simple s \<noteq> vset_empty"
  have asm2': "BFS_Example.neighbourhood E_simple s \<noteq> \<langle>\<rangle>" 
    "BFS_Example.neighbourhood E_simple s \<noteq> vset_empty"
    using assm1 by auto
  have parent_path:"\<exists>p. vwalk_bet (dfs.Graph.digraph_abs prnts) s p t"   
    using assms2(1)  level_siple_is not_None_eq[of blocking_flow_simple] 
      Compute_Blocking_Residual.blocking_simple.termination_same[OF blocking_simple_correctness(4), symmetric]     
    by(intro blocking_simple_correctness(2)) 
      (auto simp add: if_not_P[OF asm2'(1)] prnts_def blocking_flow_simple_def
        blocking_simple_initial_def level_simple_def RBT_Set.empty_def) 
  show has_path:"\<exists>p. vwalk_bet (dfs.Graph.digraph_abs E_simple) s p t"
    using BFS_correct_4  parent_path 
    by(auto intro!:  vwalk_bet_subset simp add: RBT_Set.empty_def prnts_def)
  then obtain p where p_prop: "vwalk_bet (dfs.Graph.digraph_abs E_simple) s p t" "distinct p"
    using  vwalk_bet_to_distinct_is_distinct_vwalk_bet by(force simp add: distinct_vwalk_bet_def)

  have srcs_are_s:"t_set (vset_insert s vset_empty) = {s}"
    using sources(1) by blast

  show residual_leaving_s:"\<exists>e\<in>\<EE>. 0 < \<uu>\<^bsub>\<f>\<^esub>e \<and> fstv e = s \<and> sndv e \<noteq> s" 
  proof-
    obtain x where x_prop:"hd (edges_of_vwalk p) = (s, x)" "(s, x) \<in> dfs.Graph.digraph_abs E_simple "
      using  s_neq_t by(auto intro: vwalk_betE[OF p_prop(1)])
    then obtain e where e_prop:"0 < \<uu>\<^bsub>\<f>\<^esub>e" "(s, x) = to_vertex_pair e" "e\<in>\<EE>"
      by(auto simp add: E_simple_props(4) pos_es_props(1))
    moreover hence "fstv e = s"  
      using  fst_eqD[of s x] vs_to_vertex_pair_pres(1) by simp
    moreover have "sndv e \<noteq> s" 
    proof(rule ccontr, goal_cases)
      case 1
      hence "\<exists> xs. p = [s,s]@xs"
        using p_prop(1,2) fst_eqD[of s x] vs_to_vertex_pair_pres(1) e_prop(2) x_prop(1) s_neq_t
        by(cases p rule: edges_of_vwalk.cases, all \<open>cases e\<close>)
          (auto simp add: vwalk_bet_def vs_to_vertex_pair_pres split_pairs)
      thus False
        using p_prop(2) by force
    qed
    ultimately show ?thesis by auto
  qed
  note  flow_network_axioms_for_simple_graph = 
    flow_network_axioms_for_simple_graph[OF residual_leaving_s]
  note is_blocking_flow_def=flow_network_spec.is_blocking_flow_def[of
      prod.fst prod.snd id
      "(level_graph (dfs.Graph.digraph_abs E_simple) {s} -
    {(u, v) |u v. distance (dfs.Graph.digraph_abs E_simple) s u = \<infinity>})" "(\<lambda>x. ereal (u_simple x))"]
  note bfs_level_graph_def=BFS_level_graph[simplified same_graph_consts(2) srcs_are_s 
      distance_set_single_source, symmetric]
  have flow_non_empt: "blocking_state.flow (blocking_simple_loop s t find_path u_simple 
                 (blocking_simple_initial level_simple)) \<noteq> Leaf"
    using  assms2(1)
    by(auto simp add: blocking_flow_simple_def if_not_P[OF assm1] RBT_Set.empty_def[symmetric]) 
  note same_final_state =
    Compute_Blocking_Residual.blocking_simple.termination_same[OF blocking_simple_correctness(4)]
  note flow_non_empt'=flow_non_empt[simplified blocking_simple_loop_def parents_def[symmetric]]
  note same_final_state'= same_final_state[simplified parents_def[symmetric] blocking_simple_loop_def]

  show "is_blocking_flow_simple s t (abstract_real_map (lookup f))"
    using same_final_state blocking_simple_correctness(3) assms2(1)
      flow_non_empt is_blocking_flow_def[of s t]  not_None_eq option.inject
    by(unfold prnts_def level_siple_is level_simple_def  blocking_simple_initial_def
        blocking_flow_simple_def  bfs_level_graph_def if_not_P[OF assm1] Let_def,
        subst (asm) if_not_P)
      (auto simp add: if_not_P)
  show "dom (lookup f) \<subseteq> simple_level_graph_abstract"
    using same_final_state blocking_simple_correctness(5) assms2(1)
      flow_non_empt is_blocking_flow_def[of s t]  not_None_eq option.inject
    by(unfold prnts_def level_siple_is level_simple_def  blocking_simple_initial_def
        blocking_flow_simple_def  bfs_level_graph_def if_not_P[OF assm1] Let_def,
        subst (asm) if_not_P)
      (auto simp add: if_not_P)
  show "adj_inv f"
    using same_final_state blocking_simple_correctness(6) assms2(1)
      flow_non_empt is_blocking_flow_def[of s t]  not_None_eq option.inject
    by(unfold prnts_def level_siple_is level_simple_def  blocking_simple_initial_def
        blocking_flow_simple_def  if_not_P[OF assm1] Let_def,
        subst (asm) if_not_P)
      (auto simp add: if_not_P)
qed

lemma vwalk_simple_to_resreach:
  assumes "vwalk_bet (dfs.Graph.digraph_abs E_simple) s p t"
  shows "resreach \<f> s t"
proof-
  have awalk_found: "awalk (to_vertex_pair ` 
          {x. (x \<in> F ` \<E> \<or> x \<in> Redge.B ` \<E>) \<and> 0 < \<uu>\<^bsub>\<f>\<^esub>x}) s
     (edges_of_vwalk p) t"
    using vwalk_imp_awalk[OF assms]
    by (unfold E_simple_props(4) pos_es_def set_filter set_map set_append
        resreach_def  es_props(1) ) auto
  then obtain pp where pp:"set pp \<subseteq>
                {x. (x \<in> F ` \<E> \<or> x \<in> Redge.B ` \<E>) \<and> 0 < \<uu>\<^bsub>\<f>\<^esub>x}"
    "map to_vertex_pair pp = edges_of_vwalk p" 
    using list_in_image_map[of "edges_of_vwalk p"] 
    by(force simp add: awalk_def)
  have "awalk (to_vertex_pair ` \<EE>) s (map to_vertex_pair pp) t"
    using awalk_found
    by(auto intro: subset_mono_awalk simp add:  pp(2)[symmetric] \<EE>_def)
  moreover have "0 < Rcap \<f> (set pp)"
    using pp(1) 
    by(auto intro!: Rcap_strictI')
  moreover have " pp \<noteq> []" 
    using pp(2) awalk_found s_neq_t by fastforce
  moreover have "set pp \<subseteq> \<EE>"
    using pp(1) 
    by(auto simp add: \<EE>_def)
  ultimately show ?thesis
    by(auto intro!: exI[of _ pp] simp add: resreach_def)
qed

lemma resreach_to_vwalk_simple:
  assumes "resreach \<f> s t"
  shows "\<exists> p. vwalk_bet (dfs.Graph.digraph_abs E_simple) s p t"
proof-
  obtain p where p: "awalk (to_vertex_pair ` \<EE>) s (map to_vertex_pair p) t"
    "Rcap \<f> (set p) > 0" "p \<noteq> []" "set p \<subseteq> \<EE>"
    using assms by(auto simp add: resreach_def)
  show ?thesis
    using p(3)  p(4)
    by(force intro!: exI[of _ "awalk_verts s (map to_vertex_pair p)"]
        awalk_imp_vwalk subset_mono_awalk'[OF p(1)] imageI 
        rcap_extr_strict[OF _ p(2)]
        simp add: \<EE>_def E_simple_props(4) pos_es_def es_props(1))
qed

lemma residual_add_flow_correct:
  assumes "residual_flow_invar acc"
  shows   "residual_flow_invar (residual_add_flow acc e g)"
          "dom (residual_flow_lookup (residual_add_flow acc e g))
               = Set.insert e (dom (residual_flow_lookup acc))"
          "abstract_real_map (residual_flow_lookup (residual_add_flow acc e g)) =
           (\<lambda> d. if e = d then abstract_real_map (residual_flow_lookup acc) d + g 
                          else abstract_real_map (residual_flow_lookup acc) d)"
          "e \<noteq> d \<Longrightarrow> (residual_flow_lookup (residual_add_flow acc e g)) d =
                     residual_flow_lookup acc d"
  using assms
  by(auto intro!: ext 
        simp add: residual_add_flow_def abstract_real_map_def 
                  Map_residual_flow.map_update Map_residual_flow.invar_update 
           split: option.split if_split)

(*TODO MOVE*)
lemma ereal_of_real_of_ereal_leq: "x \<ge> 0 \<Longrightarrow> ereal (real_of_ereal x) \<le> x"
  by (simp add: ereal_real)

  (*To be solved by split lemmas/ to be outsourced*)

lemma split_flow_single_correct1:
  assumes "residual_flow_invar acc" " realising_edges_lookup realising_edges e = Some ds"
  shows  "residual_flow_invar (split_flow_single e fl acc)"
    "dom (residual_flow_lookup  (split_flow_single e fl acc)) \<subseteq>
          dom (residual_flow_lookup acc) \<union> set (the (realising_edges_lookup realising_edges e))"
    "\<And> d. d \<notin> set ds \<Longrightarrow>
         residual_flow_lookup 
               (split_flow_single e fl acc) d = residual_flow_lookup acc d"
proof-
  let ?iteration = " (\<lambda>(resf, f) ee.
             let \<gamma> = min (real_of_ereal \<uu>\<^bsub>\<f>\<^esub>ee) f in (residual_add_flow resf ee \<gamma>, f - \<gamma>))"
  have resflow_invar_fold:"residual_flow_invar acc \<Longrightarrow> residual_flow_invar
     (prod.fst (foldl ?iteration (acc, fl) ds))" for ds fl acc
    using assms(1)
    by(induction ds arbitrary: acc fl)
      (auto intro: residual_add_flow_correct(1) split: prod.split)
  thus "residual_flow_invar (split_flow_single e fl acc)"
    using assms(1)
    by(simp add: split_flow_single_def)
  have no_change_outside_es: 
       "residual_flow_invar acc \<Longrightarrow> e \<notin> set ds\<Longrightarrow> residual_flow_lookup
     (prod.fst (foldl ?iteration (acc, fl) ds)) e = 
       residual_flow_lookup acc e" for ds fl acc e
    using assms(1)  Map_residual_flow.map_update residual_add_flow_correct(1,4)
    by (induction ds arbitrary: acc fl)auto
  thus " d \<notin> set ds \<Longrightarrow>
         residual_flow_lookup 
               (split_flow_single e fl acc) d = residual_flow_lookup acc d" for d
    by (simp add: assms(1,2) split_flow_single_def)
  have "residual_flow_invar acc \<Longrightarrow> 
       dom (residual_flow_lookup (prod.fst (foldl ?iteration (acc, fl) ds ))) = 
        set ds \<union> dom (residual_flow_lookup acc)" for ds
  proof(induction ds arbitrary: acc fl)
    case (Cons a ds)
    show ?case  
      using residual_add_flow_correct(2) Cons(1)[simplified case_prod_beta Let_def]
     by (unfold set_simps(2) Un_insert_left 
                foldl_Cons case_prod_beta )
          (auto simp add:  Cons.prems residual_add_flow_correct(1))
  qed auto
  thus "dom (residual_flow_lookup (split_flow_single e fl acc))
    \<subseteq> dom (residual_flow_lookup acc) \<union> set (the (realising_edges_lookup realising_edges e))"  
    using assms(1) by(simp add:  split_flow_single_def)
qed

lemma split_flow_single_correct2:
  assumes "residual_flow_invar acc" " realising_edges_lookup realising_edges e = Some ds"
    "(\<And> d. d \<in> set ds\<Longrightarrow> abstract_real_map (residual_flow_lookup acc) d= 0)"
    "fl \<le> u_simple e" "fl \<ge> 0"
  shows  
    "sum (abstract_real_map (residual_flow_lookup  (split_flow_single e fl acc)))
           (set ds) = fl"
    "\<And> d. d \<in> set ds \<Longrightarrow>
         abstract_real_map (residual_flow_lookup 
               (split_flow_single e fl acc)) d \<le> rcap \<f> d"
    "\<And> d. d \<in> set ds \<Longrightarrow>
         abstract_real_map (residual_flow_lookup 
               (split_flow_single e fl acc)) d \<ge> 0"
proof-
  let ?iteration = " (\<lambda>(resf, f) ee.
             let \<gamma> = min (real_of_ereal \<uu>\<^bsub>\<f>\<^esub>ee) f in (residual_add_flow resf ee \<gamma>, f - \<gamma>))"
  have resflow_invar_fold:"residual_flow_invar acc \<Longrightarrow> residual_flow_invar
     (prod.fst (foldl ?iteration (acc, fl) ds))" for ds fl acc
    using assms(1)
    by(induction ds arbitrary: acc fl)
      (auto intro: residual_add_flow_correct(1) split: prod.split)
  have no_change_outside_es: 
       "residual_flow_invar acc \<Longrightarrow> e \<notin> set ds\<Longrightarrow> residual_flow_lookup
     (prod.fst (foldl ?iteration (acc, fl) ds)) e = 
       residual_flow_lookup acc e" for ds fl acc e
    using assms(1)  Map_residual_flow.map_update residual_add_flow_correct(1,4)
    by (induction ds arbitrary: acc fl)auto
  note  ds_positive = preorder_class.eq_refl[OF realising_edges_result(1)[OF assms(2),
                simplified pos_es_props(1)]]
  show "sum (abstract_real_map (residual_flow_lookup 
                (split_flow_single e fl acc))) (set ds) = fl"
    using assms(4)[simplified u_simple_def assms(2), simplified] assms(5)
          realising_edges_result(2)[OF assms(2)] ds_positive  assms(1,3)
    unfolding split_flow_single_def assms(2) option.sel
  proof(induction ds arbitrary: fl acc)
    case Nil
    then show ?case by simp
  next
    case (Cons a ds)
    hence distinctds: "distinct ds" by auto
    have sum_us_pos: "0 \<le> (\<Sum>e\<leftarrow>ds. real_of_ereal \<uu>\<^bsub>\<f>\<^esub>e)"
      using local.Cons(5) 
      by(auto intro!: ordered_comm_monoid_add_class.sum_nonneg  real_of_ereal_pos
            simp add: comm_monoid_add_class.sum.distinct_set_conv_list[OF distinctds, symmetric])
    have new_fl_less: "fl - min (real_of_ereal \<uu>\<^bsub>\<f>\<^esub>a) fl \<le> (\<Sum>e\<leftarrow>ds. real_of_ereal \<uu>\<^bsub>\<f>\<^esub>e)"
      using Cons(2) sum_us_pos by auto
    show ?case 
      using Cons(4,5,6)  Cons(1)[ OF new_fl_less _ distinctds, simplified Let_def]   
            residual_add_flow_correct
            abstract_real_map_cong[of "residual_flow_lookup _ " _ "residual_flow_lookup _",
                     OF no_change_outside_es[simplified Let_def , of _ a,
                           OF residual_add_flow_correct(1)[OF Cons(6)]]]
      by (subst set_simps(2), subst comm_monoid_add_class.sum.insert)
         (force simp add: Cons.prems(5,6) residual_add_flow_correct(3))+
  qed
  fix d
  assume asm: "d \<in> set ds"
  show "ereal (abstract_real_map (residual_flow_lookup (split_flow_single e fl acc)) d) \<le> \<uu>\<^bsub>\<f>\<^esub>d"
    using realising_edges_result(2)[OF assms(2)] ds_positive assms(1,3) asm
    unfolding split_flow_single_def assms(2) option.sel
  proof(induction ds arbitrary: acc fl)
    case Nil
    then show ?case by auto
    next
    case (Cons dd ds)
    show ?case
    proof(cases "dd = d")
      case True
      show ?thesis 
       using abstract_real_map_cong[of "residual_flow_lookup _ " _ "residual_flow_lookup _",
                     OF no_change_outside_es[simplified Let_def , of _ d ds,
                           OF residual_add_flow_correct(1)[OF Cons(4)]]]
          True  residual_add_flow_correct(3) Cons(2-6)
        by(auto intro!: linorder_class.min.coboundedI1 ereal_of_real_of_ereal_leq)
    next
      case False
      show ?thesis 
        using Cons.prems residual_add_flow_correct(1,3)  False
        by(auto intro!: Cons(1)[simplified Let_def])
    qed
  qed
  show "(abstract_real_map (residual_flow_lookup (split_flow_single e fl acc)) d) \<ge> 0"
    using realising_edges_result(2)[OF assms(2)] ds_positive assms(1,3,5) asm
    unfolding split_flow_single_def assms(2) option.sel
  proof(induction ds arbitrary: acc fl)
    case Nil
    then show ?case by auto
    next
    case (Cons dd ds)
    show ?case
    proof(cases "dd = d")
      case True
      have "0 \<le> real_of_ereal \<uu>\<^bsub>\<f>\<^esub>d"
        using Cons.prems(2) True real_of_ereal_pos by force 
      then show ?thesis 
        using  abstract_real_map_cong[of "residual_flow_lookup _ " _ "residual_flow_lookup _",
                     OF no_change_outside_es[simplified Let_def , of _ d ds,
                           OF residual_add_flow_correct(1)[OF Cons(4)]]]
               True residual_add_flow_correct(3) Cons(2-6)
        by auto
    next
      case False
      show ?thesis 
        using Cons.prems residual_add_flow_correct(1,3)  False
        by(auto intro!: Cons(1)[simplified Let_def])
    qed
  qed
qed

lemma find_blocking_flow_properties:
  assumes "find_blocking_flow = Some rsfl"
  shows   "residual_flow_invar rsfl"
    "dom (residual_flow_lookup rsfl) 
           \<subseteq> \<Union> {set (the (realising_edges_lookup realising_edges e)) 
               | e. e \<in> dom (lookup (the blocking_flow_simple) )}"
    "\<And> e. e \<in> dom (residual_flow_lookup rsfl) \<Longrightarrow>
            ereal (abstract_real_map (residual_flow_lookup rsfl) e) \<le> rcap \<f> e"
    "\<And> e. e \<in> dom (residual_flow_lookup rsfl) \<Longrightarrow>
            abstract_real_map (residual_flow_lookup rsfl) e \<ge> 0"
    "\<And> e. abstract_real_map (lookup (the blocking_flow_simple) ) e =
              sum (abstract_real_map (residual_flow_lookup rsfl))
                  (set (case (realising_edges_lookup realising_edges e) of Some ds \<Rightarrow> ds
                   | None  \<Rightarrow> []))" 
proof-
  have rsfl_is:"rsfl = rbt_map_fold  (the blocking_flow_simple) (\<lambda> e fl acc. split_flow_single e fl acc) 
         residual_flow_empty"
    using assms(1)
    by(cases blocking_flow_simple)(auto simp add: find_blocking_flow_def )
  obtain bfs where bfs_prop:"blocking_flow_simple = Some bfs" 
    using assms(1)
    by(cases blocking_flow_simple)(auto simp add: find_blocking_flow_def )
  obtain xs where iteration_order: "distinct xs"
     "set xs = dom (lookup bfs)"
     "rbt_map_fold bfs split_flow_single residual_flow_empty =
     foldr (\<lambda>x. split_flow_single x (the (lookup bfs x))) xs residual_flow_empty"
    using   rbt_map_fold_correct[OF blocking_flow_simple_correct(6)
             [OF bfs_prop , simplified  adj_inv_def], of split_flow_single residual_flow_empty]
    by auto

  note simple_flow_in_lg = blocking_flow_simple_correct(5)[OF bfs_prop]

  have in_xs_realising_no_none:"e \<in> set xs \<Longrightarrow>
           realising_edges_lookup realising_edges e \<noteq> None " for e
    using order.trans[OF simple_flow_in_lg 
              order.trans[OF _ level_graph_subset_graph[of 
             "(dfs.Graph.digraph_abs E_simple)" "{s}"]]]
         realising_edges_result(3)[of e]
    by(auto simp add: E_simple_props(4) pos_es_props(1) iteration_order(2))
  have resflow_invar:"residual_flow_invar
     (foldr (\<lambda>x. split_flow_single x (the (lookup bfs x))) xs residual_flow_empty)"
    if "\<And> e. e \<in> set xs \<Longrightarrow>
           realising_edges_lookup realising_edges e \<noteq> None" for xs
    using that
  proof(induction xs)
    case Nil
    then show ?case by(auto simp add: Map_residual_flow.invar_empty)
  next
    case (Cons a xs)
    show ?case 
      using Cons(2)[of a]
      by(auto intro!: split_flow_single_correct1(1)  Cons(1) Cons(2)[simplified]
            intro: prod.exhaust[of a]) 
  qed
  thus "residual_flow_invar rsfl"
    using bfs_prop in_xs_realising_no_none iteration_order(3) rsfl_is by auto

  have dom_in:"dom ( residual_flow_lookup
     (foldr (\<lambda>x. split_flow_single x (the (lookup bfs x))) xs residual_flow_empty))
     \<subseteq>  \<Union>  {set (the (realising_edges_lookup realising_edges e)) |e.
          e \<in> set xs}" 
    if in_xs_realising_no_none: 
       "\<And> e. e \<in> set xs \<Longrightarrow> realising_edges_lookup realising_edges e \<noteq> None" for xs
    using in_xs_realising_no_none
    unfolding iteration_order(2)[symmetric]
  proof(induction xs)
    case Nil
    then show ?case 
      by (simp add: Map_residual_flow.map_empty)
  next
    case (Cons a xs)
    obtain b where b_obtain:"realising_edges_lookup realising_edges a = Some b"
      using Cons(2)[of a] by auto
    show ?case 
    unfolding foldr_Cons o_apply
    using resflow_invar[OF Cons(2) ]  Cons(1)[OF Cons(2), simplified]
    by (intro order.trans[OF split_flow_single_correct1(2), OF _ b_obtain],
        all \<open>(subst  set_simps(2) image_Collect[symmetric])?\<close>)auto
qed
  show dom_subset_descr:"dom (residual_flow_lookup rsfl)
    \<subseteq> \<Union> {set (the (realising_edges_lookup realising_edges e)) |e.
          e \<in> dom (lookup (the blocking_flow_simple))}"
    using dom_in[OF in_xs_realising_no_none, of xs] 
    by(simp add: bfs_prop iteration_order(2,3) rsfl_is)
  have "e \<in> dom (residual_flow_lookup rsfl)
       \<Longrightarrow> ereal (abstract_real_map (residual_flow_lookup rsfl) e) \<le> rcap \<f> e
           \<and> (abstract_real_map (residual_flow_lookup rsfl) e) \<ge> 0"
    for e
    using in_xs_realising_no_none iteration_order(1)
          equalityD1[OF iteration_order(2)]
    unfolding rsfl_is bfs_prop option.sel
    unfolding  iteration_order(3)
  proof (induction xs)
    case Nil
    then show ?case 
      by (simp add: Map_residual_flow.map_empty)
  next
    case (Cons a xs)
    hence immediately_fom_IH_prems: 
    "e \<in> set xs \<Longrightarrow> realising_edges_lookup realising_edges e \<noteq> None" 
    "distinct xs" for e by auto
    obtain ds where ds_obtain: "realising_edges_lookup realising_edges a = Some ds"
      using Cons(3)[of a] by auto
    have d_in_ds_outside_of_old_dom:
             "d \<notin> \<Union> {set (the (realising_edges_lookup realising_edges e)) |e. e \<in> set xs}"
      if "d \<in> set ds" for d
    proof(rule ccontr, goal_cases)
      case 1
      then obtain e where e:"e \<in> set xs" "d \<in> set (the (realising_edges_lookup realising_edges e))"
        by auto
      then obtain ds' where ds': "realising_edges_lookup realising_edges e = Some ds'"
        using Cons.prems(2)[of e] by(cases "realising_edges_lookup realising_edges e") auto
      have "e = a"
        using realising_edges_result(1)[OF ds'] realising_edges_result(1)[OF ds_obtain]
              e(2) ds' that by auto
      thus False
        using Cons.prems(3) e(1) by auto
    qed
    have lookup_less_u_gtr_0_simple:"the (lookup bfs a) \<le> u_simple a" "0 \<le> the (lookup bfs a)"
    proof-
      have a_in_dom: "a \<in> dom (lookup bfs)"
        using Cons.prems(4) by auto
      show "the (lookup bfs a) \<le> u_simple a" "0 \<le> the (lookup bfs a)"
        apply(all \<open>rule flow_network_spec.is_blocking_flowE[OF 
                             blocking_flow_simple_correct(3)[OF  bfs_prop]]\<close>)
        using set_mp[OF simple_flow_in_lg  a_in_dom]
        by(auto elim!: flow_network_spec.is_s_t_flowE flow_network_spec.isuflowE 
             simp add: abstract_real_map_in_dom_the[OF a_in_dom, symmetric])
    qed    
    show ?case 
    proof(cases "e \<in> set ds")
      case True
      show ?thesis 
      using split_flow_single_correct2(2,3)[OF  _ ds_obtain]  lookup_less_u_gtr_0_simple True
          contra_subsetD[OF dom_in[OF immediately_fom_IH_prems(1), of xs]
                              d_in_ds_outside_of_old_dom] 
       by(force intro!: Cons(3) resflow_invar[of xs] abstract_real_map_outside_dom)+
  next
    case False
    note flow_no_change =  split_flow_single_correct1(3)[OF resflow_invar[OF immediately_fom_IH_prems(1)]
           ds_obtain False, of xs, simplified]
    note flow_no_change_abstract = abstract_real_map_cong[of "residual_flow_lookup _" e "residual_flow_lookup _", 
            OF  flow_no_change]
    show ?thesis
      using Cons.prems(1) flow_no_change  immediately_fom_IH_prems  Cons.prems(4) 
      by(auto intro!: conjunct1[OF Cons(1)] conjunct2[OF Cons(1)] simp add: flow_no_change_abstract)
    qed
  qed
  thus "ereal (abstract_real_map (residual_flow_lookup rsfl) e) \<le> \<uu>\<^bsub>\<f>\<^esub>e" 
       "0 \<le> abstract_real_map (residual_flow_lookup rsfl) e"
       if "e \<in> dom (residual_flow_lookup rsfl)" for e
    using that by auto
  have sum_split:"e \<in> set xs \<Longrightarrow> abstract_real_map (lookup (the blocking_flow_simple)) e =
         sum (abstract_real_map (residual_flow_lookup rsfl))
             (set (the (realising_edges_lookup realising_edges e)))" for e
   using in_xs_realising_no_none iteration_order(1)
          equalityD1[OF iteration_order(2)]
    unfolding rsfl_is bfs_prop option.sel  iteration_order(3)
  proof (induction xs)
    case Nil
    then show ?case 
      by (simp add: Map_residual_flow.map_empty)
  next
    case (Cons a xs)
    hence immediately_fom_IH_prems: 
    "e \<in> set xs \<Longrightarrow> realising_edges_lookup realising_edges e \<noteq> None" 
    "distinct xs" for e by auto
    obtain ds where ds_obtain: "realising_edges_lookup realising_edges a = Some ds"
      using Cons(3)[of a] by auto
    have d_in_ds_outside_of_old_dom:
             "d \<notin> \<Union> {set (the (realising_edges_lookup realising_edges e)) |e. e \<in> set xs}"
      if "d \<in> set ds" for d
    proof(rule ccontr, goal_cases)
      case 1
      then obtain e where e:"e \<in> set xs" "d \<in> set (the (realising_edges_lookup realising_edges e))"
        by auto
      then obtain ds' where ds': "realising_edges_lookup realising_edges e = Some ds'"
        using Cons.prems(2)[of e] by(cases "realising_edges_lookup realising_edges e") auto
      have "e = a"
        using realising_edges_result(1)[OF ds'] realising_edges_result(1)[OF ds_obtain]
              e(2) ds' that by auto
      thus False
        using Cons.prems(3) e(1) by auto
    qed
    have lookup_less_u_gtr_0_simple:"the (lookup bfs a) \<le> u_simple a" "0 \<le> the (lookup bfs a)"
    proof-
      have a_in_dom: "a \<in> dom (lookup bfs)"
        using Cons.prems(4) by auto
      show "the (lookup bfs a) \<le> u_simple a" "0 \<le> the (lookup bfs a)"
        apply(all \<open>rule flow_network_spec.is_blocking_flowE[OF 
                             blocking_flow_simple_correct(3)[OF  bfs_prop]]\<close>)
        using set_mp[OF simple_flow_in_lg  a_in_dom]
        by(auto elim!: flow_network_spec.is_s_t_flowE flow_network_spec.isuflowE 
             simp add: abstract_real_map_in_dom_the[OF a_in_dom, symmetric])
    qed  
    have the_lookup_abstract:"the (lookup bfs a) = abstract_real_map (lookup bfs) a"
      using Cons.prems(4) abstract_real_map_in_dom_the by force
    show ?case 
    proof(cases "e = a")
      case True
      have flow_zero_old: "d \<in> set (the (realising_edges_lookup realising_edges a)) \<Longrightarrow>
         abstract_real_map
          (residual_flow_lookup
            (foldr (\<lambda>x. split_flow_single x (the (lookup bfs x))) xs residual_flow_empty))
          d = 0" for d
        using d_in_ds_outside_of_old_dom[of d]
              dom_in[OF immediately_fom_IH_prems(1), of xs, simplified] 
        by(auto intro!: abstract_real_map_none simp add: ds_obtain) blast
      show ?thesis 
        using flow_zero_old lookup_less_u_gtr_0_simple
        by(auto intro!: split_flow_single_correct2(1)[symmetric]
         simp add: True immediately_fom_IH_prems(1) resflow_invar ds_obtain the_lookup_abstract)
  next
    case False
    show ?thesis
    proof(subst foldr_Cons, subst o_apply, rule trans[OF Cons(1)], goal_cases)
      case 1
      then show ?case 
        using Cons.prems(1) False by auto
    next
      case (2 e)
      then show ?case 
        using immediately_fom_IH_prems(1) by blast
    next
      case 3
      then show ?case 
        using immediately_fom_IH_prems(2) by auto
    next
      case 4
      then show ?case
        using Cons.prems(4) by auto
    next
      case 5
      show ?case 
      proof(rule sum_cong, goal_cases)
        case (1 d)
        hence d_not_in_ds:"d \<notin> set ds" 
          using  Cons.prems(1) False d_in_ds_outside_of_old_dom[of d] 
                 ds_obtain immediately_fom_IH_prems(1) realising_edges_result(1) 
          by auto
        note flow_no_change =  split_flow_single_correct1(3)[OF resflow_invar[OF immediately_fom_IH_prems(1)]
           ds_obtain d_not_in_ds, of xs, simplified]
        then show ?case 
          by (auto intro!: abstract_real_map_cong)
      qed
    qed
  qed
qed
  show "abstract_real_map (lookup (the blocking_flow_simple)) e =
         sum (abstract_real_map (residual_flow_lookup rsfl))
          (set (case realising_edges_lookup realising_edges e of None \<Rightarrow> [] | Some ds \<Rightarrow> ds))" for e
  proof(cases "e \<in> set xs")
    case True
    show ?thesis 
      by (simp add: sum_split True in_xs_realising_no_none option.case_eq_if)
  next
    case False
    hence "abstract_real_map (lookup (the blocking_flow_simple)) e = 0"
      by(auto intro!: abstract_real_map_outside_dom simp add: bfs_prop domI iteration_order(2))
    moreover have "realising_edges_lookup realising_edges e = Some ds \<Longrightarrow>
           sum (abstract_real_map (residual_flow_lookup rsfl)) (set ds) = 0" for ds
    proof(rule comm_monoid_add_class.sum.neutral
                        abstract_real_map_outside_dom, rule, 
         rule abstract_real_map_outside_dom, rule ccontr,
          goal_cases)
      case (1 e')
      then obtain ee where ee:
        "e' \<in> set (the (realising_edges_lookup realising_edges ee))" "ee \<in> dom (lookup bfs)" 
        "ee \<in> set xs"
        using dom_subset_descr by(force simp add: bfs_prop iteration_order(2)) 
      moreover have "ee = e" 
        using   in_xs_realising_no_none[of ee] 
                realising_edges_result(1)[of ee]  "1"(1,2) calculation(1) ee(3)
                realising_edges_result(1) by auto
      ultimately show False
        using False by blast
    qed
    ultimately show ?thesis 
      by(cases "realising_edges_lookup realising_edges e") simp+
  qed 
qed

    (*TODO MOVE*)
lemma sum_split_off: "A \<subseteq> B \<Longrightarrow> finite B \<Longrightarrow> (\<And> x. x \<in> B - A \<Longrightarrow> f x = 0) \<Longrightarrow> sum f A = sum f B" for f A B
  by (simp add: sum.mono_neutral_cong_right)

lemma if_non_empty_finite_finite: " (A \<noteq> {} \<Longrightarrow> finite A) \<Longrightarrow> finite A" by auto

lemma find_blocking_flow:
  "find_blocking_flow  = None
            \<longleftrightarrow> \<not> resreach \<f> s t" (is ?thesis1)
  "\<And> rf. find_blocking_flow = Some rf \<Longrightarrow> residual_flow_invar rf" 
  (is "\<And> rf. ?asm1 rf \<Longrightarrow> ?thesis2 rf")
  "\<And> rf. find_blocking_flow = Some rf \<Longrightarrow>
         residual_level_blocking_flow  \<f> s t
                (abstract_real_map (residual_flow_lookup rf))"
  (is "\<And> rf. ?asm1 rf \<Longrightarrow> ?thesis3 rf")
  "\<And> rf. find_blocking_flow = Some rf \<Longrightarrow>
          dom (residual_flow_lookup rf) 
          \<subseteq> residual_level_graph \<f> s"
  (is "\<And> rf. ?asm1 rf \<Longrightarrow> ?thesis4 rf")
proof-
  show ?thesis1
    using blocking_flow_simple_correct(1,2)  resreach_to_vwalk_simple  vwalk_simple_to_resreach
    by (auto split: option.split simp add: find_blocking_flow_def)
  fix rf
  assume asm: "find_blocking_flow = Some rf"
  then obtain rfs where asm':"blocking_flow_simple = Some rfs"
    by(auto simp add: find_blocking_flow_def 
        intro: option.exhaust[of blocking_flow_simple])
  show "residual_flow_invar rf"
    by (simp add: asm find_blocking_flow_properties(1))
  have dom_goal:"dom (residual_flow_lookup rf) \<subseteq> residual_level_graph \<f> s 
                - {e | e. multigraph_spec.multigraph_distance 
                  {e | e. e \<in> \<EE> \<and> rcap \<f> e > 0} to_vertex_pair s (fstv e) = \<infinity>}"
  proof(rule order.trans[OF find_blocking_flow_properties(2)[OF asm]],
      rule Union_least, goal_cases)
    case (1 X)
    then obtain e where X_props:"X = set (the (realising_edges_lookup realising_edges e))"
      "e \<in> dom (lookup (the blocking_flow_simple))" by auto
    hence e_in_lg: "e \<in> level_graph (dfs.Graph.digraph_abs E_simple) {s} -
   {(u, v) |u v. distance (dfs.Graph.digraph_abs E_simple) s u = \<infinity>}"
      using blocking_flow_simple_correct(5) asm' by auto
    then obtain ds where ds_prop: "realising_edges_lookup realising_edges e = Some ds"
      using realising_edges_result(3)[of e]
        level_graph_subset_graph[of "(dfs.Graph.digraph_abs E_simple)" "{s}"]
      by(fastforce simp add: E_simple_props(4) pos_es_props(1) )

    show ?case
      using e_in_lg 
      by(auto simp add: X_props(1) ds_prop  realising_edges_result(1)[OF ds_prop]  
          residual_level_graph_def multigraph_spec.multi_level_graph_def E_simple_props(4)
          pos_es_props(1)  multigraph_spec.multigraph_distance_set_def level_graph_def 
          to_vertex_pair_fst_snd multigraph_spec.multigraph_distance_def)
  qed
  thus "dom (residual_flow_lookup rf) \<subseteq> residual_level_graph \<f> s" by auto
  have valid_s_t_flow: "flow_network_spec.is_s_t_flow fstv sndv to_vertex_pair (residual_level_graph \<f> s) (rcap \<f>)
     (abstract_real_map (residual_flow_lookup rf)) s t"
  proof-
    have uflow:"flow_network_spec.isuflow (residual_level_graph \<f> s) (rcap \<f>)
     (abstract_real_map (residual_flow_lookup rf))"
    proof(rule flow_network_spec.isuflowI, goal_cases)
      case (1 e)
      then show ?case 
        apply(cases "e \<in> dom (residual_flow_lookup rf)")
        subgoal
          by(auto intro: find_blocking_flow_properties(3)[OF asm])
        using residual_level_graph_in_E_pos[of \<f> s]
        by(auto simp add: abstract_real_map_none less_eq_ereal_def zero_ereal_def domIff) 
    next
      case (2 e)
      then show ?case
        apply(cases "e \<in> dom (residual_flow_lookup rf)")
        subgoal
          by(auto intro: find_blocking_flow_properties(4)[OF asm])
        using residual_level_graph_in_E_pos[of \<f> s]
        by(auto simp add: abstract_real_map_none less_eq_ereal_def zero_ereal_def domIff) 
    qed
    have same_excess: "flow_network_spec.ex fstv sndv (residual_level_graph \<f> s)
          (abstract_real_map (residual_flow_lookup rf)) x = 
           flow_network_spec.ex prod.fst prod.snd
            (level_graph (dfs.Graph.digraph_abs E_simple) {s} -
            {(u, v) |u v. distance (dfs.Graph.digraph_abs E_simple) s u = \<infinity>})
            (abstract_real_map (lookup rfs)) x" for x
    proof-
      have helper_minus: "e \<in> multigraph_spec.delta_minus (residual_level_graph \<f> s) sndv x \<Longrightarrow>
    abstract_real_map (residual_flow_lookup rf) e \<noteq> 0 \<Longrightarrow>
       \<exists>ee\<in>multigraph_spec.delta_minus
         (level_graph (dfs.Graph.digraph_abs E_simple) {s} -
          {uu. \<exists>u. (\<exists>v. uu = (u, v)) \<and> distance (dfs.Graph.digraph_abs E_simple) s u = \<infinity>})
         prod.snd x.
       \<exists>uu. Some uu = realising_edges_lookup realising_edges ee \<and> e \<in> set uu" for e 
        using dom_goal realising_edges_result(1,3)[of "make_pair_residual e"]
        by(auto dest: option.exhaust[of "realising_edges_lookup realising_edges
                                       (make_pair_residual e)"]
              elim!: abstract_real_map_not_zeroE[of "residual_flow_lookup rf" ]
              intro!: exI[of _ "fstv e"]
              simp add: to_vertex_pair_fst_snd multigraph_spec.delta_minus_def residual_level_graph_def
              multigraph_spec.multi_level_graph_def multigraph_spec.multigraph_distance_set_def
              level_graph_def E_simple_props(4) pos_es_props(1)  distance_set_def 
              multigraph_spec.multigraph_distance_def)
      have helper_plus: "e \<in> multigraph_spec.delta_plus (residual_level_graph \<f> s) fstv x \<Longrightarrow>
         abstract_real_map (residual_flow_lookup rf) e \<noteq> 0 \<Longrightarrow>
         \<exists>x\<in>multigraph_spec.delta_plus
              (level_graph (dfs.Graph.digraph_abs E_simple) {s} -
               {uu. \<exists>u. (\<exists>v. uu = (u, v)) \<and> distance (dfs.Graph.digraph_abs E_simple) s u = \<infinity>})
              prod.fst x.
            \<exists>uu. Some uu = realising_edges_lookup realising_edges x \<and> e \<in> set uu" for e
        using dom_goal realising_edges_result(1,3)[of "make_pair_residual e"]
        by(auto dest: option.exhaust[of "realising_edges_lookup realising_edges
                                       (make_pair_residual e)"]
              elim!: abstract_real_map_not_zeroE[of "residual_flow_lookup rf" ]
              intro!: exI[of _ "sndv e"]
              simp add: to_vertex_pair_fst_snd multigraph_spec.delta_plus_def residual_level_graph_def
              multigraph_spec.multi_level_graph_def multigraph_spec.multigraph_distance_set_def
              level_graph_def E_simple_props(4) pos_es_props(1)  distance_set_def 
              multigraph_spec.multigraph_distance_def)

      have same_big_sum_minus: "sum (abstract_real_map (residual_flow_lookup rf))
          (multigraph_spec.delta_minus (residual_level_graph \<f> s) sndv x) =
          sum (abstract_real_map (residual_flow_lookup rf))
         (\<Union>x\<in>multigraph_spec.delta_minus
           (level_graph (dfs.Graph.digraph_abs E_simple) {s} -
            {(u, v) |u v. distance (dfs.Graph.digraph_abs E_simple) s u = \<infinity>})
           prod.snd x.
         {xa. \<exists>uu. Some uu = realising_edges_lookup realising_edges x \<and> xa \<in> set uu})"
        using realising_edges_result(1) realising_edges_result(3) helper_minus
        by(auto intro: sum.mono_neutral_cong_right[OF _ _ _ refl]
            simp add: multigraph_spec.delta_minus_def residual_level_graph_def
            multigraph_spec.multi_level_graph_def Collect_bex_eq[symmetric]
            multigraph_spec.multigraph_distance_set_def to_vertex_pair_fst_snd
            level_graph_def E_simple_props(4) pos_es_props(1)  distance_set_def 
            finite_\<EE> multigraph_spec.delta_minus_def[of "residual_level_graph \<f> s" sndv x]
            residual_level_graph_in_E[of \<f> s] rev_finite_subset[of \<EE> "residual_level_graph \<f> s"])
      have finite_if_list: "finite {x. \<exists>uu. Some uu = realising_edges_lookup realising_edges e \<and> x \<in> set uu}" for e
        by(cases "realising_edges_lookup realising_edges e") auto
      have same_big_sum_plus:
        "sum (abstract_real_map (residual_flow_lookup rf))
     (multigraph_spec.delta_plus (residual_level_graph \<f> s) fstv x) =
     sum (abstract_real_map (residual_flow_lookup rf))
     (\<Union>x\<in>multigraph_spec.delta_plus
           (level_graph (dfs.Graph.digraph_abs E_simple) {s} -
            {uu. \<exists>u. (\<exists>v. uu = (u, v)) \<and> distance (dfs.Graph.digraph_abs E_simple) s u = \<infinity>})
           prod.fst x.
         {xa. \<exists>uu. Some uu = realising_edges_lookup realising_edges x \<and> xa \<in> set uu})"
        using realising_edges_result(1) realising_edges_result(3) helper_plus
        by(auto intro: sum.mono_neutral_cong_right[OF _ _ _ refl]
            simp add: multigraph_spec.delta_plus_def residual_level_graph_def
            multigraph_spec.multi_level_graph_def Collect_bex_eq[symmetric]
            multigraph_spec.multigraph_distance_set_def to_vertex_pair_fst_snd
            level_graph_def E_simple_props(4) pos_es_props(1)  distance_set_def 
            finite_\<EE> multigraph_spec.delta_minus_def[of "residual_level_graph \<f> s" sndv x]
            residual_level_graph_in_E[of \<f> s] rev_finite_subset[of \<EE> "residual_level_graph \<f> s"])     
      show ?thesis
        using flow_network_axioms_for_simple_graph[OF blocking_flow_simple_correct(4), OF asm']
          multigraph.delta_minus_finite[of prod.fst prod.snd id Pair 
            "level_graph (dfs.Graph.digraph_abs E_simple) {s} - _"] 
          multigraph.delta_plus_finite[of prod.fst prod.snd id Pair 
            "level_graph (dfs.Graph.digraph_abs E_simple) {s} - _"] 
          finite_if_list same_big_sum_minus same_big_sum_plus
        by (auto simp add: find_blocking_flow_properties(5)[OF asm, simplified asm', simplified]
            disjoint_multiple_sum[OF _ distinct_pairs_no_reaising_in_common] 
            flow_network_def flow_network_spec.ex_def)
    qed
    have level_graph_simple_subset:
      "level_graph (dfs.Graph.digraph_abs E_simple) {s} -
              {uu.
               \<exists>u. (\<exists>v. uu = (u, v)) \<and> distance (dfs.Graph.digraph_abs E_simple) s u = \<infinity>} 
           \<subseteq> to_vertex_pair ` residual_level_graph \<f> s"
      by(auto simp add: level_graph_def distance_set_def E_simple_props(4) pos_es_props(1)
          residual_level_graph_def multigraph_spec.multi_level_graph_def
          multigraph_spec.multigraph_distance_set_def to_vertex_pair_fst_snd)
    show ?thesis
    proof(rule flow_network_spec.is_s_t_flowI, goal_cases)
      case 1
      then show ?case 
        using uflow by simp
    next
      case 2
      then show ?case 
        using same_excess blocking_flow_simple_correct(3)[OF asm']
        by(auto elim!: flow_network_spec.is_s_t_flowE 
            simp add: flow_network_spec.is_blocking_flow_def)
    next
      case 3
      then show ?case
        using  dVs_subset[OF level_graph_simple_subset]  blocking_flow_simple_correct(3)[OF asm']
        by(auto elim!: flow_network_spec.is_s_t_flowE 
            simp add: flow_network_spec.is_blocking_flow_def)
    next
      case 4
      then show ?case 
        using  dVs_subset[OF level_graph_simple_subset]  blocking_flow_simple_correct(3)[OF asm']
        by(auto elim!: flow_network_spec.is_s_t_flowE 
            simp add: flow_network_spec.is_blocking_flow_def)
    next
      case 5
      then show ?case 
        using   blocking_flow_simple_correct(3)[OF asm']
        by(auto elim!: flow_network_spec.is_s_t_flowE 
            simp add: flow_network_spec.is_blocking_flow_def)
    next
      case (6 x)
      then show ?case 
      proof(cases "x \<in> dVs (level_graph (dfs.Graph.digraph_abs E_simple) {s} -
                  {uu. \<exists>u. (\<exists>v. uu = (u, v)) \<and>
                       distance (dfs.Graph.digraph_abs E_simple) s u = \<infinity>})")
        case True
        then show ?thesis 
          using same_excess  6  blocking_flow_simple_correct(3)[OF asm']         
          by(auto elim!: flow_network_spec.is_s_t_flowE 
              simp add: flow_network_spec.is_blocking_flow_def)
      next
        case False
        have deltas_0:"e \<in> multigraph_spec.delta_minus (residual_level_graph \<f> s) sndv x \<Longrightarrow>
                   abstract_real_map (residual_flow_lookup rf) e = 0" 
          "e \<in> multigraph_spec.delta_plus (residual_level_graph \<f> s) fstv x \<Longrightarrow>
                   abstract_real_map (residual_flow_lookup rf) e = 0" for e
          using set_mp[OF dom_goal, of e] False
          by(auto intro!: abstract_real_map_none 
              simp add: multigraph_spec.delta_minus_def multigraph_spec.multigraph_distance_def 
              E_simple_props(4) pos_es_props(1) residual_level_graph_def multigraph_spec.multi_level_graph_def
              level_graph_def multigraph_spec.multigraph_distance_set_def distance_set_def
              dom_def to_vertex_pair_fst_snd multigraph_spec.delta_plus_def)
        then show ?thesis
          by(auto simp add: flow_network_spec.ex_def comm_monoid_add_class.sum.neutral)
      qed
    qed
  qed
  show "residual_level_blocking_flow \<f> s t (abstract_real_map (residual_flow_lookup rf))"
  proof(unfold residual_level_blocking_flow_def
      flow_network_spec.is_blocking_flow_def multigraph_spec.multigraph_path_def,
      rule ccontr, goal_cases)
    case 1
    then obtain p where p_prop:
      "awalk UNIV (fstv (hd p)) (map to_vertex_pair p) (sndv (last p))"
      "p \<noteq> []" "fstv (hd p) = s" "sndv (last p) = t" "set p \<subseteq> residual_level_graph \<f> s"
      "\<And> e. e\<in>set p \<Longrightarrow> abstract_real_map (residual_flow_lookup rf) e < \<uu>\<^bsub>\<f>\<^esub>e"
      using valid_s_t_flow by auto
    have "set (map to_vertex_pair p) \<subseteq> (level_graph (dfs.Graph.digraph_abs E_simple) {s} -
            {(u, v) |u v. distance (dfs.Graph.digraph_abs E_simple) s u = \<infinity>})"
    proof(rule, goal_cases)
      case (1 e)
      then obtain ee where ee: "ee \<in> set p" "to_vertex_pair ee = e" by auto
      then obtain p1 p2 where p1p2:"map to_vertex_pair p = p1@[e]@p2"
        using "1" single_in_append split_list_last by force
      have "distance (to_vertex_pair ` {uu \<in> \<EE>. 0 < \<uu>\<^bsub>\<f>\<^esub>uu}) s (prod.fst e) < \<infinity>"
      proof(cases p1)
        case Nil
        hence "s = prod.fst e"
          using p1p2 diff_is_res_circ p_prop(3) vs_to_vertex_pair_pres(1)
          by auto
        then show ?thesis 
          using ee p_prop(5)
          by(intro ord_class.ord_eq_less_trans[OF distance_0I, of _ _ _ \<infinity>])
            (auto intro!: dVsI'(1) 
              simp add: residual_level_graph_def multigraph_spec.multi_level_graph_def)
      next
        case (Cons a list)
        have awalk_help: "awalk UNIV s p1 (prod.fst e)"
          using awalk_fst_last p1p2 p_prop(1,3) by force
        hence vwalk_found: "vwalk_bet (to_vertex_pair ` {uu \<in> \<EE>. 0 < \<uu>\<^bsub>\<f>\<^esub>uu}) s 
                            (awalk_verts s p1) (prod.fst e)"
          using Cons 
          by(auto intro!: awalk_imp_vwalk  subset_mono_awalk'[of  UNIV]
              set_mp[OF image_mono[OF  order.trans[OF p_prop(5)
                    residual_level_graph_in_E_pos]], of _ to_vertex_pair, simplified]
              simp add: cong[OF refl p1p2, of set, simplified] )
        then show ?thesis 
          by(auto intro!: order.strict_trans1[of _  _ \<infinity>, OF vwalk_bet_dist, simplified])
      qed
      then show ?case 
        using set_mp[OF p_prop(5) ee(1)] 1 ee
        by(auto simp add: level_graph_def E_simple_props(4) pos_es_props(1) distance_set_def
            residual_level_graph_def multigraph_spec.multi_level_graph_def
            multigraph_spec.multigraph_distance_set_def image_iff
            split_pairs vs_to_vertex_pair_pres(1,2))
    qed
    moreover have pos_cap_old: "e\<in>set (map to_vertex_pair p) \<Longrightarrow>
         ereal (abstract_real_map (lookup rfs) e) < ereal (u_simple e)" for e
    proof(goal_cases)
      case 1
      then obtain ee where ee: "ee \<in> set p" "to_vertex_pair ee = e" by auto
      obtain ds where ds: "realising_edges_lookup realising_edges e = Some ds"
        "{ea |ea. ea \<in> set pos_es \<and> to_vertex_pair ea = e} \<noteq> {}"
        using realising_edges_result(3)[of e]  pos_es_props(1)
          set_mp[OF image_mono[OF order.trans[OF p_prop(5) residual_level_graph_in_E_pos]]
            1[simplified]]
        by auto
      have ee_unsaturated: "abstract_real_map (residual_flow_lookup rf) ee < real_of_ereal \<uu>\<^bsub>\<f>\<^esub>ee"
        using ee(1)   p_prop(5) residual_level_graph_in_E[of \<f> s]
        by(unfold less_ereal.simps(1)[symmetric], subst ereal_real'[simplified in_mono not_infty_ereal])
          (auto intro!: p_prop(6) intro: finite_rescapsE[of ee \<f>] )
      have capacity_respected: "d \<in> \<EE> \<Longrightarrow> 0 < \<uu>\<^bsub>\<f>\<^esub>d \<Longrightarrow> 
            abstract_real_map (residual_flow_lookup rf) d \<le> real_of_ereal (\<uu>\<^bsub>\<f>\<^esub>d)" for d
        by(unfold ereal_less_eq(3)[symmetric], 
            subst ereal_real'[simplified in_mono not_infty_ereal],
            all \<open>cases "residual_flow_lookup rf d"\<close>)
          (auto intro!: find_blocking_flow_properties(3)[OF asm]
            elim: finite_rescapsE
            simp add: abstract_real_map_none zero_ereal_def real_of_ereal_pos )
      have finites: "finite {ea |ea. ea \<in> set pos_es \<and> to_vertex_pair ea = e}" by simp
      show ?case 
        using ee p_prop(5) residual_level_graph_in_E_pos  ee_unsaturated finites
        by(auto intro!: ordered_cancel_comm_monoid_add_class.sum_strict_mono_strong[of _ ee] 
            capacity_respected 
            simp add: pos_es_props(1) find_blocking_flow_properties(5)[OF asm,
              simplified asm' option.sel]
            u_simple_is ds realising_edges_result(1)[OF ds(1)])
    qed
    moreover have "multigraph_spec.multigraph_path prod.fst prod.snd id (map to_vertex_pair p)"
      using awalk_fst_last  p_prop(1)
      by(force simp add: multigraph_spec.multigraph_path_def) 
    moreover have "prod.fst (hd (map to_vertex_pair p)) = s"
      using awalk_hd[OF p_prop(1)] p_prop(2,3)
      by(cases p) auto
    moreover have "prod.snd (last (map to_vertex_pair p)) = t"
      using awalk_last[OF p_prop(1)] p_prop(2,4)
      by(cases p) auto
    ultimately show False
      using  blocking_flow_simple_correct(3)[OF asm'] p_prop(2)
      by(unfold flow_network_spec.is_blocking_flow_def) blast
  qed
qed


end

end
