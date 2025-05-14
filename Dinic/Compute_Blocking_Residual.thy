theory Compute_Blocking_Residual
  imports DFS_Collect_Backtrack_Example Compute_Blocking_Simple "HOL-Library.Product_Lexorder"
    Graph_Algorithms_Dev.BFS_Example
begin
  (*TODO MOVE*)
lemma vwalk_bet_diff_verts_length_geq_2:"vwalk_bet E s  p t\<Longrightarrow> s \<noteq> t \<Longrightarrow> length p \<ge> 2"
  by(cases p rule: edges_of_vwalk.cases) (auto simp add: vwalk_bet_def)

lemma same_graph_consts: "G.graph_inv = dfs.Graph.graph_inv"
  "G.digraph_abs = dfs.Graph.digraph_abs"
  "BFS_Example.neighbourhood = dfs.Graph.neighbourhood"
  "DFS_Collect_Backtrack_Example.neighbourhood = 
                          dfs.Graph.neighbourhood"
  "G.graph_inv = dfs.Graph.graph_inv"
      apply (auto simp add: adj_inv_def RBT_Set.empty_def
      BFS_Example.neighbourhood_def DFS_Collect_Backtrack_Example.neighbourhood_def
      )



  done
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

definition "realising_edges_general list =
           (foldr (\<lambda> e found_edges. let ee = to_vertex_pair e in
                     (case realising_edges_lookup found_edges ee of 
                      None \<Rightarrow> realising_edges_update ee [e] found_edges
                     |Some ds \<Rightarrow> realising_edges_update ee (e#ds) found_edges))
            list realising_edges_empty)"

definition "realising_edges = realising_edges_general pos_es"

definition "E_simple = foldr (\<lambda> e acc. add_edge acc (prod.fst e) (prod.snd e))
                          (map to_vertex_pair pos_es) empty"

definition "level_simple = parents (bfs_impl E_simple (bfs_initial_state 
                          (vset_insert s Pair_Graph_RBT.vset_empty)))"

definition "u_simple e = sum_list (map (\<lambda> e. real_of_ereal (rcap \<f> e)) 
                       (case realising_edges_lookup realising_edges e of None \<Rightarrow> []| 
                        Some ees \<Rightarrow> ees))"

definition "blocking_flow_simple = 
      (if neighbourhood E_simple s = vset_empty 
       then None
       else let f = flow (blocking_simple_loop s t find_path u_simple 
                 (blocking_simple_initial level_simple))
            in if f = empty then None
            else Some f)"

definition "residual_add_flow f e \<gamma> = 
residual_flow_update e ((abstract_real_map (residual_flow_lookup f) e) + \<gamma>) f"

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
      ))"


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

lemma realising_edges_invar_pres: "realising_edges_invar (realising_edges_general list)"
  unfolding realising_edges_general_def
  by(auto intro: foldr_invar 
      simp add: Map_realising.invar_empty Map_realising.invar_update realising_edges_general_def 
      split: option.split)

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

lemma realising_edges_general_result:
  assumes "realising_edges_lookup (realising_edges_general list) (u, v) = Some ds"
  shows "set ds = {e | e. e \<in> set list \<and> to_vertex_pair e = (u, v)}"
  using realising_edges_general_result_None_and_Some[of list u v ds] assms
  by simp

lemma realising_edges_result:
  "realising_edges_lookup realising_edges (u, v) = Some ds \<Longrightarrow>
    set ds = {e |e. e \<in> set pos_es \<and> to_vertex_pair e = (u, v)}"
  "realising_edges_lookup realising_edges (u, v) = Some ds \<Longrightarrow>
    distinct ds"
  "realising_edges_lookup realising_edges (u, v) = None \<Longrightarrow>
    {e |e. e \<in> set pos_es \<and> to_vertex_pair e = (u, v)} = {}"
  using realising_edges_general_result_distinct[OF pos_es_props(2) refl, of u v] 
    realising_edges_general_result_None_and_Some[OF refl] 
  by(force simp add: realising_edges_def realising_edges_general_result)+

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

lemma u_simple_is:
  "u_simple (u, v) = (\<Sum>e\<in>{e |e. e \<in> set pos_es \<and> to_vertex_pair e = (u, v)}.
                          real_of_ereal \<uu>\<^bsub>\<f>\<^esub>e)"
  using realising_edges_result[of u v]
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
    (*
lemma level_siple_is: "(bfs_impl E_simple (bfs_initial_state 
                          (vset_insert s Pair_Graph_RBT.vset_empty))) = 
                       (bfs.BFS E_simple (bfs_initial_state 
                          (vset_insert s Pair_Graph_RBT.vset_empty)))"
*)
    (*
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
and G = E_simple and
t = t and
s = s and
find_path = find_path and
u = u
  apply(auto intro!: blocking_simple_thms.intro) 
  apply (simp add: blocking_simple.flow_map.Map_axioms blocking_simple.intro
      dfs.Graph.Pair_Graph_Specs_axioms dfs.set_ops.Set2_axioms)
  apply(auto intro!: blocking_simple_thms_axioms.intro simp add: E_simple_props)
  apply (simp add: E_simple_props(1))*)

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
abbreviation "is_blocking_flow_simple == flow_network.is_blocking_flow prod.fst prod.snd id u_simple 
     simple_level_graph_abstract"

lemma "blocking_flow_simple = None \<Longrightarrow> \<nexists> p. vwalk_bet (dfs.Graph.digraph_abs E_simple) s p t" (is "?none \<Longrightarrow> ?nowalk")
  "blocking_flow_simple = Some f \<Longrightarrow>\<exists> p. vwalk_bet (dfs.Graph.digraph_abs E_simple) s p t" (is "?some \<Longrightarrow> ?walk")
  "blocking_flow_simple = Some f \<Longrightarrow> is_blocking_flow_simple s t (abstract_real_map (lookup f))" (is "?some \<Longrightarrow> ?blocking_flow")
  "blocking_flow_simple = Some f \<Longrightarrow>\<exists>e\<in>\<EE>. 0 < \<uu>\<^bsub>\<f>\<^esub>e \<and> fstv e = s \<and> sndv e \<noteq> s" (is "?some \<Longrightarrow>?leaving_e")
proof(all \<open>cases "neighbourhood E_simple s = vset_empty"\<close>)
  show "?none \<Longrightarrow> neighbourhood E_simple s = vset_empty \<Longrightarrow> ?nowalk"
    by (auto simp add: G.source_of_path_neighb_non_empty RBT_Set.empty_def s_neq_t
        vwalk_bet_diff_verts_length_geq_2  dfs.Graph.neighbourhood_def
        DFS_Collect_Backtrack_Example.neighbourhood_def
        blocking_flow_simple_def same_graph_consts(3))
  show "?some \<Longrightarrow> neighbourhood E_simple s = vset_empty \<Longrightarrow> ?walk"
    by (auto simp add:  blocking_flow_simple_def )   
  show "?some \<Longrightarrow> neighbourhood E_simple s = vset_empty \<Longrightarrow> ?blocking_flow"
    by (auto simp add:  blocking_flow_simple_def )
  show "?some \<Longrightarrow> BFS_Example.neighbourhood E_simple s = vset_empty \<Longrightarrow> \<exists>e\<in>\<EE>. 0 < \<uu>\<^bsub>\<f>\<^esub>e \<and> fstv e = s \<and> sndv e \<noteq> s"
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
  note is_blocking_flow_def=flow_network.is_blocking_flow_def[OF  flow_network_axioms_for_simple_graph]
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
qed


end
end
