theory Compute_Blocking_Simple
  imports Directed_Set_Graphs.Pair_Graph_Specs
    Directed_Set_Graphs.Set2_Addons Directed_Set_Graphs.Set_Addons
    Blocking_Flow

begin
(*TODO MOVE*)
lemma vwalk_awalk_id:
  "cas u p v \<Longrightarrow> edges_of_vwalk (awalk_verts u p) = p"
proof(induction p arbitrary: u rule: edges_of_vwalk.induct)
  case 1
  then show ?case by simp
next
  case (2 e)
  then show ?case by (cases e) simp
next
  case (3 e d es)
  have ed_share_vert:"snd e = fst d" "cas (fst d) (d # es) v"
    using  "3.prems" 
    by(auto simp add: cas_simp[of "e#d#es", simplified]  cas_simp[of "d#es", simplified])
  show ?case 
    using ed_share_vert(1) 3(1)[OF ed_share_vert(2)]
    by (cases e, cases d) auto
qed
 
  (*important for edges_of_vwalk, MOVE *)
lemma rev_cases3: "(xs = Nil \<Longrightarrow> P) \<Longrightarrow> (\<And> x. xs = [x] \<Longrightarrow> P) \<Longrightarrow>
                   (\<And> ys y x. xs=ys@[y,x] \<Longrightarrow> P) \<Longrightarrow> P" 
  by (metis More_Lists.append_butlast_last_cancel append_Nil neq_Nil_conv_snoc)

definition "acyc G = (\<nexists> p u. vwalk_bet G u p u \<and> length p \<ge> 2)"

record  ('flow, 'map) blocking_state = flow::'flow graph::'map

locale blocking_simple =
  Graph: Pair_Graph_Specs
  where lookup = lookup +
    set_ops: Set2 vset_empty vset_delete _ t_set vset_inv insert +
    flow_map: Map flow_empty flow_update flow_delete flow_lookup flow_invar
  for lookup :: "'adjmap\<Rightarrow> 'v \<Rightarrow> 'vset option"
    and flow_lookup::"'flow_map \<Rightarrow> 'v \<times> 'v \<Rightarrow> real option"
    and flow_empty flow_update flow_delete flow_invar
    +
  fixes G::"'adjmap" and s::"'v" and t::"'v"
    and   u::"'v \<times> 'v \<Rightarrow> real"
    and   find_path::"'adjmap \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> (('v list) \<times> (('v \<times> 'v) list)) option"
begin

definition "add_flow f \<gamma> e = flow_update e ((abstract_real_map (flow_lookup f) e) + \<gamma>) f"

lemma add_flow: "flow_invar f \<Longrightarrow> flow_invar (add_flow f \<gamma> e)"
  "flow_invar f \<Longrightarrow> abstract_real_map (flow_lookup (add_flow f \<gamma> e)) =
                                  (\<lambda> d. (abstract_real_map (flow_lookup f)) d +
                                         (if d = e then \<gamma> else 0))"
  "flow_invar f \<Longrightarrow> dom (flow_lookup (add_flow f \<gamma> e))
                                   = Set.insert e (dom (flow_lookup f))"
  by(auto simp add:  abstract_real_map_def add_flow_def flow_map.invar_update flow_map.map_update)

function (domintros) compute_blocking_loop::"('flow_map, 'adjmap) blocking_state 
                            \<Rightarrow>('flow_map, 'adjmap) blocking_state" where
  "compute_blocking_loop state = 
(let current_flow = flow state; current_G = graph state in
  (case find_path current_G s t of 
      None \<Rightarrow> state
   |  Some (p, del) \<Rightarrow>
      let p_edges = edges_of_vwalk p;
          \<gamma> = (min_list (map (\<lambda> e. u e - abstract_real_map (flow_lookup current_flow) e) p_edges));
          zeroed_edges = filter (\<lambda> e. u e - abstract_real_map (flow_lookup current_flow) e = \<gamma>) 
                           p_edges;
          new_flow = foldl (\<lambda> wflow e. add_flow wflow \<gamma> e) current_flow p_edges;
          new_G    = foldl (\<lambda> wG e. Graph.delete_edge wG (fst e) (snd e)) 
                     current_G (zeroed_edges @ del)
      in compute_blocking_loop (state \<lparr> flow:=new_flow, graph := new_G \<rparr>)
 ))"
  by pat_completeness auto

definition
  "compute_blocking_loop_upd state =
  (let current_flow = flow state; current_G = graph state;
       p = fst (the (find_path current_G s t)); del = snd (the (find_path current_G s t));
       p_edges = edges_of_vwalk p;
       \<gamma> =  (min_list (map (\<lambda> e. u e - abstract_real_map (flow_lookup current_flow) e) p_edges));
       zeroed_edges = filter (\<lambda> e. u e - abstract_real_map (flow_lookup current_flow) e = \<gamma>) 
                           p_edges;
       new_flow = foldl (\<lambda> wflow e. add_flow wflow \<gamma> e) current_flow p_edges;
       new_G    = foldl (\<lambda> wG e. Graph.delete_edge wG (fst e) (snd e)) 
                     current_G (zeroed_edges @ del)
      in  (state \<lparr> flow:=new_flow, graph := new_G \<rparr>))"

partial_function (tailrec) compute_blocking_loop_impl::"('flow_map, 'adjmap) blocking_state 
                            \<Rightarrow>('flow_map, 'adjmap) blocking_state" where
  "compute_blocking_loop_impl state = 
(let current_flow = flow state; current_G = graph state in
  (case find_path current_G s t of 
      None \<Rightarrow> state
   |  Some (p, del) \<Rightarrow>
      let p_edges = edges_of_vwalk p;
          \<gamma> =  (min_list (map (\<lambda> e. u e - abstract_real_map (flow_lookup current_flow) e) p_edges));
          zeroed_edges = filter (\<lambda> e. u e - abstract_real_map (flow_lookup current_flow) e = \<gamma>) 
                           p_edges;
          new_flow = foldl (\<lambda> wflow e. add_flow wflow \<gamma> e) current_flow p_edges;
          new_G    = foldl (\<lambda> wG e. Graph.delete_edge wG (fst e) (snd e)) 
                     current_G (zeroed_edges @ del)
      in compute_blocking_loop_impl (state \<lparr> flow:=new_flow, graph := new_G \<rparr>)
 ))"

definition "initial_state = \<lparr> flow=flow_empty, graph=G\<rparr>"

abbreviation "delete_edge == Graph.delete_edge"

lemmas [code] = compute_blocking_loop_impl.simps initial_state_def add_flow_def 
                Graph.delete_edge_def

lemma compute_blocking_loop_induct: 
  assumes "compute_blocking_loop_dom state"
  assumes "\<And>state. \<lbrakk>compute_blocking_loop_dom state;
            find_path (graph state) s t \<noteq> None
            \<Longrightarrow> P (compute_blocking_loop_upd state)\<rbrakk> \<Longrightarrow> P state"
  shows "P state"
  apply(rule compute_blocking_loop.pinduct[OF assms(1)])
  apply(rule assms(2)[simplified compute_blocking_loop_upd_def])
  by (auto simp: Let_def split: list.splits option.splits if_splits)

lemma compute_blocking_loop_simps: 
  assumes "compute_blocking_loop_dom state"
  shows   "find_path (graph state) s t = None \<Longrightarrow> compute_blocking_loop state = state"
          "find_path (graph state) s t \<noteq> None \<Longrightarrow>
            compute_blocking_loop state =    compute_blocking_loop (compute_blocking_loop_upd state)"
  by(auto simp add: compute_blocking_loop.psimps[OF assms] Let_def compute_blocking_loop_upd_def)

lemma compute_blocking_loop_domintros: 
  shows   "find_path (graph state) s t = None \<Longrightarrow> compute_blocking_loop_dom state"
          "find_path (graph state) s t \<noteq> None \<Longrightarrow>
           compute_blocking_loop_dom (compute_blocking_loop_upd state) \<Longrightarrow>
           compute_blocking_loop_dom state"
  by(auto intro: compute_blocking_loop.domintros simp add: compute_blocking_loop_upd_def Let_def)

lemma termination_same:
  assumes "compute_blocking_loop_dom state"
  shows   "compute_blocking_loop_impl state = compute_blocking_loop state"
  apply(induction rule: compute_blocking_loop.pinduct[OF assms(1)])
  apply(subst compute_blocking_loop.psimps)
  apply simp
  apply(subst compute_blocking_loop_impl.simps)
  by(auto simp add: Let_def split: option.split)
end

locale blocking_simple_thms =
  blocking_simple +
  assumes
    graph_invars: "Graph.graph_inv G" "Graph.finite_graph G" "Graph.finite_vsets G" and
    acyc:        "acyc  (Graph.digraph_abs G)"                                      and
    positive_capacities: "\<And> e. e \<in> (Graph.digraph_abs G) \<Longrightarrow> u e > 0"   
    "\<And> e.  u e \<ge> 0"                                            and
    s_neq_t:      "s \<noteq> t"                             and
    find_path: "\<And> F s t. \<lbrakk>Graph.graph_inv F; Graph.finite_graph F; Graph.finite_vsets F;
                     \<exists> p. vwalk_bet (Graph.digraph_abs F) s p t; s \<noteq> t\<rbrakk> \<Longrightarrow>
                     \<exists> p del. vwalk_bet (Graph.digraph_abs F) s p t 
                                \<and> find_path F s t = Some (p, del)"
    "\<And> F s t p del. \<lbrakk>Graph.graph_inv F; Graph.finite_graph F; Graph.finite_vsets F;
                             find_path F s t = Some (p, del); s \<noteq> t; acyc (Graph.digraph_abs F)\<rbrakk> \<Longrightarrow>
                     vwalk_bet (Graph.digraph_abs F) s p t \<and> distinct p \<and>
                     (\<forall> e \<in> set del. 
                            \<nexists> p.  e \<in> set (edges_of_vwalk p) \<and> 
                              Vwalk.vwalk_bet (Graph.digraph_abs F) s p t)"
begin

definition "basic_invar state = (flow_invar (flow state) \<and>
                                 dom (flow_lookup (flow state)) \<subseteq> Graph.digraph_abs G \<and>
                                 Graph.graph_inv (graph state) \<and>
                                 Graph.finite_graph (graph state) \<and>
                                 Graph.finite_vsets (graph state) \<and>
                                 Graph.digraph_abs (graph state) \<subseteq> Graph.digraph_abs G)"

definition "invar_current_G_unsaturated state=
            (\<forall> e \<in> Graph.digraph_abs (graph state). 
                    u e - abstract_real_map (flow_lookup (flow state)) e > 0)"

definition "invar_positive_path state = 
            (\<forall> p. unsaturated_path_simple (Graph.digraph_abs G) u 
                         (abstract_real_map (flow_lookup (flow state))) s p t
             \<longrightarrow> vwalk_bet (Graph.digraph_abs (graph state)) s p t)"

lemma basic_invarI: "\<lbrakk> flow_invar (flow state);
 dom (flow_lookup (flow state)) \<subseteq> Graph.digraph_abs G ;
Graph.graph_inv (graph state); Graph.finite_graph (graph state) ;
 Graph.finite_vsets (graph state) ; Graph.digraph_abs (graph state) \<subseteq> Graph.digraph_abs G\<rbrakk>
\<Longrightarrow> basic_invar state"
  by(auto simp add: basic_invar_def)

lemma basic_invarE: " basic_invar state \<Longrightarrow> (\<lbrakk> flow_invar (flow state);
 dom (flow_lookup (flow state)) \<subseteq> Graph.digraph_abs G ;
Graph.graph_inv (graph state); Graph.finite_graph (graph state) ;
 Graph.finite_vsets (graph state) ; Graph.digraph_abs (graph state) \<subseteq> Graph.digraph_abs G\<rbrakk>
\<Longrightarrow>P) \<Longrightarrow> P"
  by(auto simp add: basic_invar_def)

lemma invar_current_G_unsaturatedI:
  "(\<And> e. e \<in> Graph.digraph_abs (graph state) \<Longrightarrow> 
                    u e - abstract_real_map (flow_lookup (flow state)) e > 0) 
\<Longrightarrow> invar_current_G_unsaturated state"
  by(auto simp add: invar_current_G_unsaturated_def)

lemma invar_current_G_unsaturatedE:
  "invar_current_G_unsaturated state\<Longrightarrow> 
((\<And> e. e \<in> Graph.digraph_abs (graph state) \<Longrightarrow> 
                   u e -  abstract_real_map (flow_lookup (flow state)) e > 0) \<Longrightarrow> P) \<Longrightarrow> P"
  by(auto simp add: invar_current_G_unsaturated_def)

lemma invar_positive_pathI:
  "(\<And> p. unsaturated_path_simple (Graph.digraph_abs G) u 
                         (abstract_real_map (flow_lookup (flow state))) s p t
             \<Longrightarrow> vwalk_bet (Graph.digraph_abs (graph state)) s p t) \<Longrightarrow>
invar_positive_path state"
  by(auto simp add: invar_positive_path_def)

lemma invar_positive_pathE:
  "invar_positive_path state \<Longrightarrow>
 ((\<And> p. unsaturated_path_simple (Graph.digraph_abs G) u 
                         (abstract_real_map (flow_lookup (flow state))) s p t
             \<Longrightarrow> vwalk_bet (Graph.digraph_abs (graph state)) s p t) \<Longrightarrow> P) \<Longrightarrow>P"
  by(auto simp add: invar_positive_path_def)

lemma initial_invars: "basic_invar initial_state"
                      "invar_current_G_unsaturated initial_state"
                      "invar_positive_path initial_state"
   by(auto intro!: basic_invarI invar_current_G_unsaturatedI invar_positive_pathI
                       positive_capacities(1)
         simp add: initial_state_def flow_map.invar_empty flow_map.map_empty  graph_invars
                          abstract_real_map_empty unsaturated_path_simple_def)
 
context  assumes  non_empty_G: "[G]\<^sub>g \<noteq> {}"
begin

interpretation flow_network: flow_network fst snd id Pair u "Graph.digraph_abs G"
  by(auto intro!:  flow_network.intro multigraph.intro flow_network_axioms.intro
      graph_invars positive_capacities simp add: non_empty_G )

lemma zero_flow_valid: "s \<in> dVs [G]\<^sub>g \<Longrightarrow> t \<in> dVs [G]\<^sub>g \<Longrightarrow> flow_network.is_s_t_flow (\<lambda> e. 0) s t"
  using s_neq_t positive_capacities
  by(auto simp add: flow_network.is_s_t_flow_def local.flow_network.isuflow_def
      local.flow_network.ex_def flow_network.delta_minus_def flow_network.delta_plus_def)

definition "invar_flow state =
           (flow_network.is_s_t_flow (abstract_real_map (flow_lookup (flow state))) s t)"

lemma invar_flowI: "s \<in> dVs [G]\<^sub>g \<Longrightarrow> t \<in> dVs [G]\<^sub>g \<Longrightarrow> (flow_network.is_s_t_flow (abstract_real_map (flow_lookup (flow state))) s t) \<Longrightarrow> invar_flow state"
  by(auto simp add: invar_flow_def)

lemma invar_flowE: "invar_flow state
\<Longrightarrow>(flow_network.is_s_t_flow (abstract_real_map (flow_lookup (flow state))) s t \<Longrightarrow> P) \<Longrightarrow> P"
  by(auto simp add: invar_flow_def)

lemma initial_flow_invar: "s \<in> dVs [G]\<^sub>g \<Longrightarrow> t \<in> dVs [G]\<^sub>g \<Longrightarrow> 
            invar_flow initial_state"
  by(auto intro!: invar_flowI  zero_flow_valid simp add: initial_state_def flow_map.map_empty
         abstract_real_map_empty )

lemma invars_preservation_upd:
  assumes "find_path (graph state) s t \<noteq> None" "basic_invar state"
    "invar_current_G_unsaturated state" " invar_flow state"
  shows   "basic_invar (compute_blocking_loop_upd state)" (is ?goal1)
    and     "invar_current_G_unsaturated (compute_blocking_loop_upd state)" 
    (is "?goal2")
    and     "invar_flow  (compute_blocking_loop_upd state) "
    (is " ?goal3")
    and     "invar_positive_path state 
          \<Longrightarrow> invar_positive_path (compute_blocking_loop_upd state)" 
    (is "?assm1 \<Longrightarrow> ?goal4")
    and     "dom (flow_lookup (flow  (compute_blocking_loop_upd state))) \<noteq> {}" (is ?goal5)
    and     "Graph.digraph_abs (graph  (compute_blocking_loop_upd state)) \<subset>    
           Graph.digraph_abs (graph state)"(is ?goal6)
proof-
  define current_flow where "current_flow = flow state"
  define current_G where  "current_G = graph state"
  define p where "p = fst (the (find_path current_G s t))"
  define del where "del = snd (the (find_path current_G s t))"
  define p_edges where "p_edges = edges_of_vwalk p"
  define \<gamma> where  "\<gamma> =  (min_list (map (\<lambda> e. u e - abstract_real_map (flow_lookup current_flow) e) p_edges))"
  define zeroed_edges where "zeroed_edges = filter (\<lambda> e. u e - abstract_real_map (flow_lookup current_flow) e = \<gamma>) 
                           p_edges"
  define new_flow where "new_flow = foldl (\<lambda> wflow e. add_flow wflow \<gamma> e) current_flow p_edges"
  define new_G  where "new_G   = foldl (\<lambda> wG e. Graph.delete_edge wG (fst e) (snd e)) 
                     current_G (zeroed_edges @ del)"
  have new_state_id: "compute_blocking_loop_upd state = state \<lparr> flow:=new_flow, graph := new_G \<rparr>"
    by(simp add: new_flow_def new_G_def zeroed_edges_def  \<gamma>_def
        p_edges_def del_def p_def current_G_def
        compute_blocking_loop_upd_def Let_def current_flow_def
        |subst current_flow_def)+ 
  have p_del_are: "find_path current_G s t = Some (p, del)"
    by (simp add: assms(1) current_G_def del_def p_def)

  have basic_invs: "flow_invar current_flow"
    "dom (flow_lookup current_flow) \<subseteq> [G]\<^sub>g"
    "Graph.graph_inv current_G"
    "Graph.finite_graph current_G"
    "Graph.finite_vsets current_G" "[current_G]\<^sub>g \<subseteq> [G]\<^sub>g"
    using assms(2) by(auto elim!: basic_invarE simp add: current_flow_def current_G_def)
  have acyc_current:"acyc [current_G]\<^sub>g " 
    using  acyc
    by(auto dest!:  vwalk_bet_subset[OF _ basic_invs(6)]  simp add: acyc_def)
  have p_props: "vwalk_bet [current_G]\<^sub>g s p t"
    "distinct p" "(\<forall>e\<in>set del. \<nexists>p. e \<in> set (edges_of_vwalk p) \<and> vwalk_bet [current_G]\<^sub>g s p t)"
    using find_path(2)[of current_G s t p del] assms s_neq_t acyc_current
    by(auto elim!: basic_invarE simp add: current_G_def p_def del_def)
  have s_t_in_G:  "s \<in> dVs [G]\<^sub>g" "t \<in> dVs [G]\<^sub>g"
    using  p_props(1)  
    by(auto intro!: vwalk_bet_endpoints[of _ s _ t] 
           intro!:  vwalk_bet_subset[OF _ basic_invs(6)])
  have p_non_empt: "p_edges \<noteq> []" 
    using p_props(1) s_neq_t
    by(cases p rule: list_cases3)(auto simp add: vwalk_bet_def  p_edges_def)
  have distinct_p_edges: "distinct p_edges"
    using distinct_edges_of_vwalk p_edges_def p_props(2) by auto
  have cap_respected: "\<And> e. e \<in> [G]\<^sub>g  \<Longrightarrow> 
                        abstract_real_map (flow_lookup current_flow) e \<le> u e"
    "\<And> e. e \<in> [G]\<^sub>g  \<Longrightarrow> 
                        abstract_real_map (flow_lookup current_flow) e \<ge> 0"
    using assms(4) 
    by(auto elim!: invar_flowE 
        simp add: flow_network.is_s_t_flow_def flow_network.isuflow_def current_flow_def)
  have zeroed_edges_are: "set zeroed_edges = { e | e. e \<in> set p_edges \<and>
                                   u e - abstract_real_map (flow_lookup current_flow) e = \<gamma>}"
    by(simp add: zeroed_edges_def)
  have p_edges_in_current_G: "set p_edges \<subseteq> [current_G]\<^sub>g" 
    by(auto intro!: vwalk_bet_edges_in_edges[OF vwalk_bet_subset[OF p_props(1)]]
        simp add: p_edges_def)
  hence p_edges_in_G: "set p_edges \<subseteq> [G]\<^sub>g" 
    using assms(2)
    by(auto  elim!: basic_invarE simp add:  current_G_def)
  have gamma: "\<And> e. e \<in> set p_edges \<Longrightarrow>
               \<gamma> \<le>  u e - abstract_real_map (flow_lookup current_flow) e"
    "\<exists> e  \<in> set p_edges. \<gamma> = u e - abstract_real_map (flow_lookup current_flow) e"
    using in_set_map[OF linorder_class.Min_in] p_non_empt 
    by(auto simp add: min_list_Min \<gamma>_def )
  have invar_new_flow: "flow_invar new_flow"
    using assms(2) 
    by(auto elim: basic_invarE  intro: foldl_invar add_flow(1) simp add: current_flow_def new_flow_def  )
  have dom_new_flow_is:
    "dom (flow_lookup new_flow) = dom (flow_lookup current_flow) \<union> set p_edges"
    using basic_invs(2,1)  p_edges_in_G add_flow(1,3)[of _ \<gamma> _]
    unfolding new_flow_def
    by(induction p_edges arbitrary: current_flow) auto
  hence dom_new_flow_in_G: "dom (flow_lookup new_flow) \<subseteq> [G]\<^sub>g"
    by (simp add: basic_invs(2) p_edges_in_G)
  have new_G_graph_inv: "Graph.graph_inv new_G"
    by (simp add: new_G_def Graph.adjmap_inv_delete basic_invs(3) foldl_invar)
  have new_G_finite_graph: "Graph.finite_graph new_G"
    unfolding new_G_def
    apply(rule conjunct1[OF foldl_invar[of "\<lambda> x. _ x \<and> _ x"]])
    apply(rule conjI[OF basic_invs(4,3)])
    by(auto intro: Graph.finite_graph_delete_edge)
  have new_G_finite_vsets: "Graph.finite_vsets new_G"
    unfolding new_G_def
    apply(rule conjunct1[OF foldl_invar[of "\<lambda> x. _ x \<and> _ x"]])
    apply(rule conjI[OF basic_invs(5,3)])
    by(auto intro: Graph.finite_vsets_delete_edge)
  have new_G_is:"[new_G]\<^sub>g = [current_G]\<^sub>g - set zeroed_edges -  set del"
    using basic_invs(3) Graph.adjmap_inv_delete
    apply(unfold new_G_def, induction zeroed_edges arbitrary: current_G)
    subgoal for current_G
      by (induction del arbitrary: current_G) auto
    by auto
  hence new_Graph_subset: "[new_G]\<^sub>g \<subseteq> [current_G]\<^sub>g" by auto
  show goal1: ?goal1
    using dom_new_flow_in_G new_Graph_subset basic_invs(6)
    by(auto intro!: basic_invarI simp add: new_state_id invar_new_flow new_G_graph_inv
        new_G_finite_graph new_G_finite_vsets)
  have new_flow_is:"abstract_real_map (flow_lookup new_flow) e = 
       (if e \<in> set p_edges then abstract_real_map (flow_lookup current_flow) e + \<gamma>
        else abstract_real_map (flow_lookup current_flow) e)" for e
    using basic_invs(1) distinct_p_edges add_flow(1,2) 
    unfolding new_flow_def
    by(induction p_edges arbitrary: current_flow) auto
  have e_in_G_flow_bound:"e \<in> [current_G]\<^sub>g \<Longrightarrow>
         0 < u e - abstract_real_map (flow_lookup current_flow) e" for e
    using assms(3) current_G_def current_flow_def invar_current_G_unsaturatedE by blast
  show ?goal2
    using e_in_G_flow_bound gamma(1)
    by(fastforce intro!: invar_current_G_unsaturatedI 
        simp add:  new_state_id new_flow_is new_G_is 
        zeroed_edges_are  current_G_def current_flow_def)
  have same_as_augmentation:
    "(abstract_real_map (flow_lookup new_flow)) =
     (local.flow_network.augment_edges 
          (abstract_real_map (flow_lookup current_flow)) \<gamma> (map F p_edges))"
    using basic_invs(1)
    unfolding new_flow_def 
      flow_network.augment_edges'_is_augment_edges[symmetric]
  proof(induction p_edges arbitrary: current_flow)
    case Nil
    then show ?case by simp
  next
    case (Cons a p_edges)
    have same_flow_one_step:"(abstract_real_map (flow_lookup (add_flow current_flow \<gamma> a))) = 
         flow_network.augment_edge (abstract_real_map (flow_lookup current_flow)) \<gamma>
          (F a)"
      by(auto simp add: add_flow(2)[OF Cons(2)])
    show ?case
      by(subst foldl.foldl_Cons, subst  Cons(1))
        (auto simp add:  same_flow_one_step intro: add_flow(1) Cons(2))
  qed
  have now_valid_flow: "flow_network.is_s_t_flow (abstract_real_map (flow_lookup current_flow)) s t"
    using assms(4) current_flow_def invar_flowE by blast
  have gamma_strict_pos:"0 < \<gamma>" 
    apply(rule bexE[OF  gamma(2)])
    using p_edges_in_current_G invar_current_G_unsaturatedE[OF assms(3)] 
    by(auto simp add: current_flow_def current_G_def)
  hence gamma_pos: "0 \<le> \<gamma>"  by simp
  have gamma_less_cap: "ereal \<gamma>
    \<le> flow_network.Rcap (abstract_real_map (flow_lookup current_flow))
        (F ` set p_edges)"
    using gamma(1) by (force simp add: flow_network.Rcap_def )
  have rcap_strict_pops:"flow_network.Rcap (abstract_real_map (flow_lookup current_flow))
        (F ` set p_edges) > 0"
    using dual_order.strict_trans1 ereal_less(2) gamma_less_cap gamma_strict_pos by blast
  have p_edges_in_E:"F ` set p_edges \<subseteq> flow_network.\<EE>"
    using local.flow_network.o_edge_res p_edges_in_G by fastforce
  have distinct_augpath: "distinct (map F p_edges)"
    by(auto simp add: distinct_map distinct_p_edges intro!: inj_onI)
  have s_hd_path: "flow_network.fstv (hd (map F p_edges)) = s"
    using p_props(1) s_neq_t 
    by (auto intro: list_cases3[of p] simp add: p_edges_def vwalk_bet_def)
  have t_tl_path: "flow_network.sndv (last (map F p_edges)) = t"
    using p_props(1) s_neq_t  
    by(cases p rule: rev_cases3)
      (auto intro:  simp add: p_edges_def vwalk_bet_def edges_of_vwalk_append_two_vertices)
  have augpath_p:"flow_network.augpath (abstract_real_map (flow_lookup current_flow))
     (map F p_edges)"
    using rcap_strict_pops vwalk_bet_subset[OF p_props(1), of UNIV, simplified]
      s_hd_path t_tl_path p_non_empt
    by(auto simp add: flow_network.augpath_def  flow_network.prepath_def o_def p_edges_def 
        intro!: vwalk_imp_awalk)
  show ?goal3
    using p_edges_in_E  s_t_in_G
    by(fastforce intro!:  invar_flowI flow_network.augment_along_s_t_path[OF now_valid_flow gamma_pos] 
        simp add:  gamma_less_cap  distinct_augpath s_hd_path t_tl_path augpath_p
        s_neq_t new_state_id same_as_augmentation)
  show "?assm1 \<Longrightarrow> ?goal4"
  proof(rule invar_positive_pathI, goal_cases)
    case (1 q)
    have unsaturated_in_G_with_f:
      "unsaturated_path_simple [G]\<^sub>g u (abstract_real_map (flow_lookup (flow state))) s q t"
      using 1(2)gamma_pos unsaturated_path_simple_mono
      by(fastforce simp add: new_state_id current_flow_def[symmetric] unsaturated_path_simple_def
                             new_flow_is )
    hence vwalk_current:"vwalk_bet [current_G]\<^sub>g s q t"
      using invar_positive_pathE[OF 1(1)] 
      by(auto simp add: current_G_def)
    have vwalk_q_edges:"vwalk_bet (set (edges_of_vwalk q)) s q t"
      using  s_neq_t vwalk_current
      by(intro vwalk_bet_in_its_own_edges[OF vwalk_current], cases q rule: list_cases3)
        (auto simp add: vwalk_bet_def)
    have not_in_zeroed:"e \<in> set zeroed_edges \<Longrightarrow> e \<in> set (edges_of_vwalk q) \<Longrightarrow> False" for e
      using 1(2)  
      by(auto elim!:  ballE[of _ _  e] 
          simp add: zeroed_edges_are new_state_id unsaturated_path_simple_def 
                     new_flow_is p_edges_def) 
    have not_in_del:"e \<in> set del \<Longrightarrow> e \<in> set (edges_of_vwalk q) \<Longrightarrow> False" for e
      using p_props vwalk_current by simp
    have vwalk_new:"vwalk_bet [new_G]\<^sub>g s q t" 
      using vwalk_bet_edges_in_edges[OF vwalk_current]
      by(auto intro: vwalk_bet_subset[OF vwalk_q_edges] not_in_zeroed not_in_del
          simp add: new_G_is)
    thus ?case 
      by(simp add: new_state_id)
  qed
  show ?goal5
    by(simp add: new_state_id dom_new_flow_is  p_non_empt)
  show ?goal6
  proof-
    obtain e where e_prop: "\<gamma> = u e - abstract_real_map (flow_lookup current_flow) e" "e\<in>set p_edges"
      using gamma(2) by blast
    have "e \<in> [current_G]\<^sub>g"  "e \<notin> [new_G]\<^sub>g" "e \<in> set zeroed_edges"
      using  e_prop(1,2) zeroed_edges_are p_edges_in_current_G 
      by (auto simp add: new_G_is)
    thus ?thesis
      using new_Graph_subset 
      by(auto simp add: new_state_id current_G_def)
  qed 
qed

lemma 
  assumes "compute_blocking_loop_dom state"
          "basic_invar state" "invar_current_G_unsaturated state" "invar_flow state"
    shows basic_invar_holds:  "basic_invar (compute_blocking_loop state)" (is ?thesis1)
    and   invar_current_G_unsaturated_holds: "invar_current_G_unsaturated (compute_blocking_loop state)" (is ?thesis2)
    and   invar_flow_holds:  "invar_flow (compute_blocking_loop state)" (is?thesis3)
proof-
  have "basic_invar (compute_blocking_loop state) \<and>
           invar_current_G_unsaturated (compute_blocking_loop state) \<and>
           invar_flow (compute_blocking_loop state)"
  using assms(2-)
proof(induction rule: compute_blocking_loop_induct[OF assms(1)])
  case (1 state)
  note IH = this
  show ?case 
    using invars_preservation_upd(1,2,3)[OF _ IH(3-)]  IH(2)
    by (cases "find_path (graph state) s t")
       (auto simp add: compute_blocking_loop_simps[OF IH(1)] IH(3-)Let_def 
                split: option.split)
qed
  thus ?thesis1 ?thesis2 ?thesis3
    by simp+
qed

lemma invar_positive_path_holds: 
  assumes "compute_blocking_loop_dom state"
          "basic_invar state" "invar_current_G_unsaturated state" "invar_flow state"
          "invar_positive_path state"
    shows "invar_positive_path (compute_blocking_loop state)"
  using assms(2-)
proof(induction rule: compute_blocking_loop_induct[OF assms(1)])
  case (1 state)
  note IH = this
  show ?case 
    by(cases "find_path (graph state) s t")
      (auto intro!:  IH(2) invars_preservation_upd(1,2,3)[OF _ IH(3-5)] 
                     invars_preservation_upd(4)[OF _ IH(3-)] 
         simp add: compute_blocking_loop_simps[OF IH(1)] IH(3-)Let_def 
            split: option.split)
qed

lemma final_path_search_unsuccessful:
  assumes "compute_blocking_loop_dom state"
  shows   "find_path (graph (compute_blocking_loop state)) s t = None"
proof(induction rule: compute_blocking_loop_induct[OF assms])
  case (1 state)
  then show ?case 
    using compute_blocking_loop_simps(1,2)[OF 1(1)]
    by(cases "find_path (graph (compute_blocking_loop (compute_blocking_loop_upd state))) s t")
       fastforce+
qed

lemma flow_dom_non_empty: 
  assumes "compute_blocking_loop_dom state"
          "basic_invar state" "invar_current_G_unsaturated state" "invar_flow state"
          "find_path (blocking_state.graph state) s t \<noteq> None"
    shows "dom (flow_lookup (flow (compute_blocking_loop state))) = {} \<Longrightarrow> False"
  using assms(2-)
proof(induction rule: compute_blocking_loop_induct[OF assms(1)])
  case (1 state)
  note IH = this
  show ?case 
    using "1.hyps" compute_blocking_loop_simps(2) IH(3-7)  compute_blocking_loop_domintros(1)
        compute_blocking_loop_simps(1,2) invars_preservation_upd(5)[OF _ IH(4-6)] 
    by (all \<open>cases "find_path (blocking_state.graph (compute_blocking_loop_upd state)) s t"\<close>)
       (auto intro:  IH(2) simp add: invars_preservation_upd)
qed

lemma computer_blocking_loop_terminates:
  assumes "basic_invar state" "invar_current_G_unsaturated state" "invar_flow state"
  shows   "compute_blocking_loop_dom state"
proof-
  define m where "m = card (Graph.digraph_abs (graph state))"
  show ?thesis
    using assms m_def
proof(induction m arbitrary: state rule: less_induct)
  case (less m)
  show ?case
  proof(cases "find_path (graph state) s t")
    case None
    then show ?thesis by(auto intro: compute_blocking_loop_domintros)
  next
    case (Some a)
    have card_less: "card [blocking_state.graph (compute_blocking_loop_upd state)]\<^sub>g
        < card [blocking_state.graph state]\<^sub>g" 
      by (intro psubset_card_mono)
         (force intro: basic_invarE[OF less.prems(1)] 
             simp add: Some invars_preservation_upd(6) less.prems(1,2,3))+
    show ?thesis 
      apply(rule compute_blocking_loop_domintros(2))
      using Some  card_less 
      by (auto intro!: less(1)[OF _ _ _ _ refl] Some invars_preservation_upd 
             simp add: less.prems(1,2,3) less(5))
  qed 
 qed
qed
end

lemma correctness:
        "flow (compute_blocking_loop initial_state) = flow_empty
         \<Longrightarrow> (\<nexists> p. vwalk_bet (Graph.digraph_abs G) s p t)"
        "flow  (compute_blocking_loop initial_state) \<noteq>flow_empty 
         \<Longrightarrow> \<exists> p. vwalk_bet (Graph.digraph_abs G) s p t"
        "flow  (compute_blocking_loop initial_state) \<noteq>flow_empty 
         \<Longrightarrow> flow_network_spec.is_blocking_flow fst snd id (Graph.digraph_abs G) u s t 
               (abstract_real_map (flow_lookup (flow (compute_blocking_loop initial_state))))"
        "compute_blocking_loop_dom initial_state"
        "flow  (compute_blocking_loop initial_state) \<noteq>flow_empty  \<Longrightarrow> dom (flow_lookup (flow (compute_blocking_loop initial_state))) \<subseteq> Graph.digraph_abs G"
        "flow  (compute_blocking_loop initial_state) \<noteq>flow_empty  \<Longrightarrow> flow_invar  (flow (compute_blocking_loop initial_state))"
proof-
  show "compute_blocking_loop_dom initial_state"
  proof(cases "find_path (blocking_state.graph initial_state) s t")
    case None
    then show ?thesis by(auto intro!: compute_blocking_loop_domintros(1))
  next
    case (Some a)
    then obtain p del where a_split:"a = (p, del)" by(cases a) auto
    hence p_prop:"vwalk_bet [G]\<^sub>g s (fst a) t" 
      using find_path(2)[of "graph initial_state", OF  _ _ _ Some[simplified a_split] s_neq_t]
         acyc graph_invars(1,2,3) 
      by(auto simp add: initial_state_def)
     hence G_props: "[G]\<^sub>g \<noteq> {}" "s \<in> dVs [G]\<^sub>g" "t \<in> dVs [G]\<^sub>g"
          by (simp add: s_neq_t vwalk_bet_hd_neq_last_implies_edges_nonempty)+    
        note invar_flow_intial = initial_flow_invar[OF G_props]
        thus ?thesis
    using computer_blocking_loop_terminates
                      [OF G_props(1) initial_invars(1,2) invar_flow_intial] by simp
  qed
  show "flow (compute_blocking_loop initial_state) = flow_empty 
      \<Longrightarrow> \<nexists>p. vwalk_bet [G]\<^sub>g s p t"
  proof(goal_cases)
    case 1
    note asm = this
    show ?case
      proof(rule ccontr, goal_cases)
        case 1
        then obtain p where p_prop:"vwalk_bet [G]\<^sub>g s p t" by auto
        hence G_props: "[G]\<^sub>g \<noteq> {}" "s \<in> dVs [G]\<^sub>g" "t \<in> dVs [G]\<^sub>g"
          by (simp add: s_neq_t vwalk_bet_hd_neq_last_implies_edges_nonempty)+    
        note invar_flow_intial = initial_flow_invar[OF G_props]
        note dom_of_initial=computer_blocking_loop_terminates
                      [OF G_props(1) initial_invars(1,2) invar_flow_intial]
        note final_basic_invar = basic_invar_holds
                      [OF G_props(1) dom_of_initial initial_invars(1,2) invar_flow_intial]
        have "dom (flow_lookup (flow (compute_blocking_loop initial_state))) \<noteq> {}" 
          using find_path(1)[OF graph_invars exI[of "\<lambda> p. vwalk_bet [G]\<^sub>g  s p t", OF p_prop] s_neq_t]
              by(auto intro!: flow_dom_non_empty[OF G_props(1) dom_of_initial  initial_invars(1,2)
                                   invar_flow_intial] 
                    simp add: initial_state_def)
      then show ?case
        by (simp add: asm flow_map.map_empty)
    qed
  qed
  assume assm: "flow (compute_blocking_loop initial_state) \<noteq> flow_empty"
  then obtain p del where p_del_prop:"find_path (graph initial_state) s t = Some (p, del)"
    using compute_blocking_loop_simps(1)[OF  compute_blocking_loop_domintros(1)]
    by(fastforce simp add: initial_state_def)
  hence p_vwalk:"vwalk_bet [G]\<^sub>g s p t" 
    using find_path(2)[OF graph_invars p_del_prop[simplified initial_state_def, simplified]
                           s_neq_t acyc] by simp
  thus "\<exists>p. vwalk_bet [G]\<^sub>g s p t" by auto
  have G_props: "[G]\<^sub>g \<noteq> {}" "s \<in> dVs [G]\<^sub>g" "t \<in> dVs [G]\<^sub>g"
    using p_vwalk
    by (simp add: s_neq_t vwalk_bet_hd_neq_last_implies_edges_nonempty)+  
  have flow_network: "flow_network fst snd id Pair (\<lambda>x. ereal (u x)) [G]\<^sub>g"
                     "multigraph fst snd id Pair [G]\<^sub>g"
    by(auto intro!:  flow_network.intro multigraph.intro flow_network_axioms.intro
      graph_invars positive_capacities simp add: G_props)

  note  initial_flow_invar =  initial_flow_invar[OF G_props]
  note initial_termination = computer_blocking_loop_terminates[OF G_props(1) 
               initial_invars(1,2) initial_flow_invar]
  note final_invar_flow = invar_flow_holds[OF G_props(1) initial_termination 
               initial_invars(1,2) initial_flow_invar]
  note final_basic_invar = basic_invar_holds[OF G_props(1) initial_termination 
               initial_invars(1,2) initial_flow_invar]
  note invar_flow_def = invar_flow_def[OF G_props(1)]
  note final_invar_positive_path= invar_positive_path_holds[OF G_props(1) initial_termination
                   initial_invars(1,2) initial_flow_invar initial_invars(3)]
  note final_no_path = final_path_search_unsuccessful[OF G_props(1) initial_termination]
  note multigraph_path_def = multigraph_spec.multigraph_path_def
  note is_blocking_flow_def = flow_network_spec.is_blocking_flow_def

  show "flow_network_spec.is_blocking_flow fst snd id [G]\<^sub>g (\<lambda>x. ereal (u x)) s t
     (abstract_real_map (flow_lookup (flow (compute_blocking_loop initial_state))))"
    unfolding is_blocking_flow_def
  proof(rule conjI, goal_cases)
    case 1
    then show ?case
      using final_invar_flow by(auto simp add: invar_flow_def)
  next
    case 2
    show ?case 
    proof(rule ccontr, goal_cases)
      case 1
      then obtain q where q_prop: 
          "multigraph_spec.multigraph_path fst snd id q" "q \<noteq> []"
          "fst (hd q) = s"  "snd (last q) = t" "set q \<subseteq> [G]\<^sub>g"
          "\<And> e. e\<in>set q \<Longrightarrow>
              ereal (abstract_real_map (flow_lookup (flow 
                       (compute_blocking_loop initial_state))) e)
              < ereal (u e)"
        by auto
      have "vwalk_bet [G]\<^sub>g s (awalk_verts s q) t"
        using q_prop(1,2,5)
        by(auto intro!: awalk_imp_vwalk intro: subset_mono_awalk' simp add: multigraph_path_def q_prop(3,4))
      moreover have "e\<in>set (edges_of_vwalk (awalk_verts s q)) \<Longrightarrow>
        abstract_real_map (flow_lookup (flow (compute_blocking_loop initial_state))) e < u e" for e
        using q_prop(6)[of e]  q_prop(1,2) 
        by(auto simp add: vwalk_awalk_id[of s q t] multigraph_path_def awalk_def q_prop(3,4))
      ultimately have "unsaturated_path_simple [G]\<^sub>g u
           (abstract_real_map (flow_lookup (flow (compute_blocking_loop initial_state))))
            s (awalk_verts s q) t"
        by(auto simp add: unsaturated_path_simple_def)
      hence "vwalk_bet [graph (compute_blocking_loop initial_state)]\<^sub>g s  (awalk_verts s q) t"
        using  final_invar_positive_path by(simp add: invar_positive_path_def)
      hence q_found_final: "\<exists> q. vwalk_bet [graph (compute_blocking_loop initial_state)]\<^sub>g s  q t"
        by auto
      have "find_path (graph (compute_blocking_loop initial_state)) s t \<noteq> None" 
        using find_path(1)[ OF  _ _ _ q_found_final s_neq_t] 
        by(auto intro: basic_invarE[OF final_basic_invar])
      then show ?case
        using final_no_path by auto
    qed
  qed
  show "dom (flow_lookup (flow (compute_blocking_loop initial_state))) \<subseteq> Graph.digraph_abs G"
    by (auto intro: basic_invarE[OF final_basic_invar])
  show "flow_invar  (flow (compute_blocking_loop initial_state))"
    using basic_invarE final_basic_invar by auto
qed

end
end
