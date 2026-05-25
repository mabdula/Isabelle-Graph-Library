section \<open>Orlin's Algorithm Executable\<close>

theory Instantiation
  imports Graph_Algorithms_Dev.RBT_Map_Extension
          Directed_Set_Graphs.Pair_Graph_RBT
          Graph_Algorithms_Dev.Bellman_Ford_Example
          Graph_Algorithms_Dev.DFS_Example
          Mincost_Flow_Algorithms.Orlins
begin

subsection \<open>Definitions\<close>

hide_const RBT_Set.empty Set.empty  not_blocked_update
notation vset_empty ("\<emptyset>\<^sub>N")

fun list_to_rbt :: "('a::linorder) list \<Rightarrow> 'a rbt" where
  "list_to_rbt [] = Leaf"
| "list_to_rbt (x#xs) = vset_insert x (list_to_rbt xs)"

value "vset_diff (list_to_rbt [1::nat, 2, 3, 4,6]) (list_to_rbt [0..20])"

text \<open>set of edges\<close>
definition "get_from_set = List.find"
fun are_all where "are_all P (Nil) = True"|
                  "are_all P (x#xs) = (P x \<and> are_all P xs)"
definition "set_invar = distinct"
definition "to_set = set"
definition "to_list = id"

notation map_empty ("\<emptyset>\<^sub>G")

definition "flow_empty = vset_empty"
definition "flow_update = update"
definition "flow_delete = RBT_Map.delete"
definition "flow_lookup = lookup"
definition "flow_invar = (\<lambda>t. M.invar t \<and>  rbt_red t)"

definition "bal_empty = vset_empty"
definition "bal_update = update"
definition "bal_delete = RBT_Map.delete"
definition "bal_lookup = lookup"
definition "bal_invar = (\<lambda>t. M.invar t \<and>  rbt_red t)"

definition "rep_comp_empty = vset_empty"
definition "rep_comp_update = update"
definition "rep_comp_delete = RBT_Map.delete"
definition "rep_comp_lookup = lookup"
definition "rep_comp_invar = (\<lambda>t. M.invar t \<and>  rbt_red t)"

definition "conv_empty = vset_empty"
definition "conv_update = update"
definition "conv_delete = RBT_Map.delete"
definition "conv_lookup = lookup"
definition "conv_invar = (\<lambda>t. M.invar t \<and>  rbt_red t)"

definition "not_blocked_empty = vset_empty"
definition "not_blocked_update = update"
definition "not_blocked_delete = RBT_Map.delete"
definition "not_blocked_lookup = lookup"
definition "not_blocked_invar = (\<lambda>t. M.invar t \<and>  rbt_red t)"

definition "rep_comp_upd_all = (update_all :: ('a \<Rightarrow> 'a \<times> nat \<Rightarrow> 'a \<times> nat)
   \<Rightarrow> (('a \<times> 'a \<times> nat) \<times> color) tree
      \<Rightarrow> (('a \<times> 'a \<times> nat) \<times> color) tree)"
definition "not_blocked_upd_all = (update_all :: ('edge \<Rightarrow> bool \<Rightarrow> bool)
   \<Rightarrow> (('edge \<times> bool) \<times> color) tree
      \<Rightarrow> (('edge \<times> bool) \<times> color) tree)"
definition "flow_update_all = (update_all :: ('edge \<Rightarrow> real \<Rightarrow> real)
   \<Rightarrow> (('edge \<times> real) \<times> color) tree
      \<Rightarrow> (('edge \<times> real) \<times> color) tree)"

lemma  rep_comp_upd_all: 
    "\<And> rep f. rep_comp_invar rep \<Longrightarrow> (\<And> x. x \<in> dom (rep_comp_lookup rep) 
                  \<Longrightarrow> rep_comp_lookup (rep_comp_upd_all f rep) x =
                      Some (f x (the (rep_comp_lookup rep x))))"
    "\<And> rep f g. rep_comp_invar rep \<Longrightarrow> (\<And> x. x \<in> dom (rep_comp_lookup rep)  \<Longrightarrow>
                     f x (the (rep_comp_lookup rep x)) = g x (the (rep_comp_lookup rep x))) \<Longrightarrow>
          rep_comp_upd_all f rep = rep_comp_upd_all g rep "
   "\<And> rep f. rep_comp_invar rep \<Longrightarrow> rep_comp_invar (rep_comp_upd_all f rep)"
   "\<And> rep f. rep_comp_invar rep \<Longrightarrow> dom (rep_comp_lookup (rep_comp_upd_all f rep))
                              = dom (rep_comp_lookup rep)"
 and not_blocked_upd_all: 
    "\<And> nblckd f. not_blocked_invar nblckd \<Longrightarrow> (\<And> x. x \<in> dom (not_blocked_lookup nblckd) 
                  \<Longrightarrow> not_blocked_lookup (not_blocked_upd_all f nblckd) x =
                      Some (f x (the (not_blocked_lookup nblckd x))))"
    "\<And> nblckd f g. not_blocked_invar nblckd \<Longrightarrow> (\<And> x. x \<in> dom (not_blocked_lookup nblckd)  \<Longrightarrow>
                     f x (the (not_blocked_lookup nblckd x)) = g x (the (not_blocked_lookup nblckd x))) \<Longrightarrow>
          not_blocked_upd_all f nblckd = not_blocked_upd_all g nblckd "
   "\<And> nblckd f. not_blocked_invar nblckd \<Longrightarrow> not_blocked_invar (not_blocked_upd_all f nblckd)"
   "\<And> nblckd f. not_blocked_invar nblckd \<Longrightarrow> dom (not_blocked_lookup (not_blocked_upd_all f nblckd))
                              = dom (not_blocked_lookup nblckd)"
 and flow_update_all: 
    "\<And> fl f. flow_invar fl \<Longrightarrow> (\<And> x. x \<in> dom (flow_lookup fl) 
                  \<Longrightarrow> flow_lookup (flow_update_all f fl) x =
                      Some (f x (the (flow_lookup fl x))))"
    "\<And> fl f g. flow_invar fl \<Longrightarrow> (\<And> x. x \<in> dom (flow_lookup fl)  \<Longrightarrow>
                     f x (the (flow_lookup fl x)) = g x (the (flow_lookup fl x))) \<Longrightarrow>
          flow_update_all f fl = flow_update_all g fl "
   "\<And> fl f. flow_invar fl \<Longrightarrow> flow_invar (flow_update_all f fl)"
   "\<And> fl f. flow_invar fl \<Longrightarrow> dom (flow_lookup (flow_update_all f fl))
                              = dom (flow_lookup fl)"
and get_max: "\<And> b f. bal_invar b \<Longrightarrow> dom (bal_lookup b) \<noteq> {}
 \<Longrightarrow> get_max f b = Max {f y (the (bal_lookup b y)) | y. y \<in> dom (bal_lookup b)}"
and to_list: "\<And> E. set_invar E \<Longrightarrow> to_set E = set (to_list E)"
             "\<And> E. set_invar E \<Longrightarrow> distinct (to_list E)"
  using update_all(3)
  by (auto simp add: rep_comp_lookup_def rep_comp_upd_all_def rep_comp_invar_def 
                     M.invar_def  update_all(1)  color_no_change rbt_red_def rbt_def 
                     not_blocked_invar_def not_blocked_lookup_def not_blocked_upd_all_def
                     flow_invar_def flow_lookup_def flow_update_all_def bal_invar_def
                     bal_update_def bal_lookup_def  to_list_def to_set_def set_invar_def
             intro!: update_all(2,3,4) get_max_correct)

interpretation adj: Map 
  where empty = vset_empty and update=edge_map_update and 
        delete=delete and lookup= lookup and invar=adj_inv
  using RBT_Map.M.Map_axioms
  by(auto simp add: Map_def rbt_red_def rbt_def M.invar_def  edge_map_update_def adj_inv_def RBT_Set.empty_def )

lemmas Map_satisfied = adj.Map_axioms

lemmas Set_satisified = dfs.Graph.vset.set.Set_axioms

lemma Set_Choose_axioms: "Set_Choose_axioms vset_empty isin sel"
  apply(rule Set_Choose_axioms.intro)
  unfolding RBT_Set.empty_def  
  subgoal for s
    by(induction rule: sel.induct) auto
  done

lemmas Set_Choose_satisfied = dfs.Graph.vset.Set_Choose_axioms

interpretation Pair_Graph_Specs_satisfied:
     Pair_Graph_Specs map_empty RBT_Map.delete lookup vset_insert isin t_set sel
     edge_map_update adj_inv vset_empty vset_delete vset_inv
  using Set_Choose_satisfied Map_satisfied
  by(auto simp add: Pair_Graph_Specs_def map_empty_def  RBT_Set.empty_def)

lemmas Pair_Graph_Specs_satisfied = Pair_Graph_Specs_satisfied.Pair_Graph_Specs_axioms

lemmas Set2_satisfied = dfs.set_ops.Set2_axioms

definition "realising_edges_empty = (vset_empty::((('a ::linorder\<times> 'a) \<times> ('edge list)) \<times> color) tree)"
definition "realising_edges_update = update"
definition "realising_edges_delete = RBT_Map.delete"
definition "realising_edges_lookup = lookup"
definition "realising_edges_invar = M.invar"

interpretation Map_realising_edges: 
 Map realising_edges_empty realising_edges_update realising_edges_delete 
     realising_edges_lookup realising_edges_invar
  using RBT_Map.M.Map_axioms     
  by(auto simp add: realising_edges_update_def realising_edges_empty_def  realising_edges_delete_def
                    realising_edges_lookup_def realising_edges_invar_def)

lemmas Map_realising_edges = Map_realising_edges.Map_axioms

lemmas Map_connection = Map_connection.Map_axioms

lemmas bellman_ford_spec = bellford.bellman_ford_spec_axioms

locale function_generation =

 Map_realising: Map realising_edges_empty "realising_edges_update::(('a)\<times> 'a) \<Rightarrow> 'edge list \<Rightarrow> 'realising_type \<Rightarrow> 'realising_type"
                    realising_edges_delete realising_edges_lookup realising_edges_invar +

 Map_bal: Map bal_empty "bal_update::'a \<Rightarrow> real \<Rightarrow> 'bal_impl \<Rightarrow> 'bal_impl" 
              bal_delete bal_lookup bal_invar +

 Map_flow: Map "flow_empty::'flow_impl" "flow_update::'edge \<Rightarrow> real \<Rightarrow> 'flow_impl \<Rightarrow> 'flow_impl"
                flow_delete flow_lookup flow_invar +

 Map_not_blocked: Map not_blocked_empty "not_blocked_update::'edge \<Rightarrow> bool \<Rightarrow> 'nb_impl \<Rightarrow> 'nb_impl" 
                      not_blocked_delete not_blocked_lookup not_blocked_invar +

 Map rep_comp_empty "rep_comp_update::'a \<Rightarrow> ('a \<times> nat) \<Rightarrow> 'rcomp_impl \<Rightarrow> 'rcomp_impl" rep_comp_delete 
     rep_comp_lookup rep_comp_invar 

for 

realising_edges_empty 
realising_edges_update 
realising_edges_delete 
realising_edges_lookup 
realising_edges_invar

bal_empty 
bal_update 
bal_delete 
bal_lookup 
bal_invar 

flow_empty 
flow_update 
flow_delete 
flow_lookup 
flow_invar

not_blocked_empty 
not_blocked_update 
not_blocked_delete 
not_blocked_lookup 
not_blocked_invar 

rep_comp_empty 
rep_comp_update 
rep_comp_delete 
rep_comp_lookup 
rep_comp_invar+

fixes \<E>_impl::'edge_set_impl 
and to_list:: "'edge_set_impl \<Rightarrow> 'edge list"
and fst::"'edge \<Rightarrow> ('a::linorder)" 
and snd::"'edge \<Rightarrow> 'a"
and create_edge::"'a \<Rightarrow> 'a \<Rightarrow> 'edge"
and \<c>_impl::'c_impl
and  \<b>_impl::'bal_impl
and to_set::"'edge_set_impl \<Rightarrow> 'edge set"
and c_lookup::"'c_impl \<Rightarrow> 'edge \<Rightarrow> real option"
begin

definition "make_pair e \<equiv> (fst e, snd e)"

definition "\<u> = (\<lambda> e::'edge. PInfty)"  
definition "\<c> e = (case (c_lookup \<c>_impl e)  of Some c \<Rightarrow> c | None \<Rightarrow> 0)"
definition \<E> where "\<E> = to_set \<E>_impl"
definition "N = length (remdups (map fst (to_list \<E>_impl) @ map snd  (to_list \<E>_impl)))"
definition "\<epsilon> = 1 / (max 3 (real N))"

definition "\<b> = (\<lambda> v. if bal_lookup \<b>_impl v \<noteq> None then the (bal_lookup \<b>_impl v) else 0)"
abbreviation "EEE \<equiv> flow_network_spec.\<EE> \<E>"
abbreviation "fstv == flow_network_spec.fstv fst snd"
abbreviation "sndv == flow_network_spec.sndv fst snd"

abbreviation "VV \<equiv> dVs (make_pair ` \<E>)"
                            
definition "es = remdups(map make_pair (to_list \<E>_impl)@(map prod.swap (map make_pair (to_list \<E>_impl))))"                             
definition "vs = remdups (map prod.fst es)"

definition "dfs F t = (dfs.DFS_impl F t)" for F
definition "dfs_initial s = (dfs.initial_state  s)"

definition "get_path u v E = rev (stack (dfs E v (dfs_initial u)))"

fun get_source_aux_aux where 
"get_source_aux_aux b \<gamma> [] = None"|
"get_source_aux_aux b \<gamma> (v#xs) =
 (if b v > (1 - \<epsilon>) * \<gamma> then Some v else 
           get_source_aux_aux b \<gamma> xs)"

definition "get_source_aux b \<gamma> xs =  (get_source_aux_aux  b \<gamma> xs)"

fun get_target_aux_aux where 
"get_target_aux_aux b \<gamma> [] = None"|
"get_target_aux_aux b \<gamma> (v#xs) =
 (if b v < - (1 - \<epsilon>) * \<gamma> then Some v else 
           get_target_aux_aux b \<gamma> xs)"

definition "get_target_aux b \<gamma> xs = (get_target_aux_aux b \<gamma> xs)"

definition "\<E>_list = to_list \<E>_impl"

definition "realising_edges_general list =
           (foldr (\<lambda> e found_edges. let ee = make_pair e in
                     (case realising_edges_lookup found_edges ee of 
                      None \<Rightarrow> realising_edges_update ee [e] found_edges
                     |Some ds \<Rightarrow> realising_edges_update ee (e#ds) found_edges))
            list realising_edges_empty)"
            
definition "realising_edges = realising_edges_general \<E>_list"
                       
definition "find_cheapest_forward f nb list e c=
        foldr (\<lambda> e (beste, bestc). if nb e \<and> ereal (f e) < \<u> e \<and>
                                       ereal (\<c> e) < bestc 
                                   then (e, ereal (\<c> e))
                                   else (beste, bestc)) list (e, c)"
                                 
                                 
definition "find_cheapest_backward f nb list e c=
        foldr (\<lambda> e (beste, bestc). if nb e \<and> ereal (f e) > 0 \<and>
                                      ereal (- \<c> e) < bestc 
                                   then (e, ereal (- \<c> e))
                                   else (beste, bestc)) list (e, c)"
                                   
                                   
definition "get_edge_and_costs_forward nb (f::'edge \<Rightarrow> real) = 
                          (\<lambda> u v. (let ingoing_edges = (case (realising_edges_lookup realising_edges (u, v)) of
                                     None \<Rightarrow> []|
                                     Some list \<Rightarrow> list);
                 outgoing_edges = (case (realising_edges_lookup realising_edges (v, u)) of
                                   None \<Rightarrow> [] |
                                   Some list \<Rightarrow> list);
                 (ef, cf) = find_cheapest_forward f nb ingoing_edges
                            (create_edge u v) PInfty; 
                 (eb, cb) = find_cheapest_backward f nb outgoing_edges
                            (create_edge v u) PInfty
                  in (if cf \<le> cb then (F ef, cf) else (B eb, cb))))"
                      
                      
definition "get_edge_and_costs_backward nb (f::'edge \<Rightarrow> real) = 
                          (\<lambda> v u. (let ingoing_edges = (case (realising_edges_lookup realising_edges (u, v)) of
                                     None \<Rightarrow> []|
                                     Some list \<Rightarrow> list);
                 outgoing_edges = (case (realising_edges_lookup realising_edges (v, u)) of
                                   None \<Rightarrow> [] |
                                   Some list \<Rightarrow> list);
                 (ef, cf) = find_cheapest_forward f nb ingoing_edges
                            (create_edge u v) PInfty; 
                 (eb, cb) = find_cheapest_backward f nb outgoing_edges
                            (create_edge v u) PInfty
                  in (if cf \<le> cb then (F ef, cf) else (B eb, cb))))"

definition "bellman_ford_forward nb (f::'edge \<Rightarrow> real) s =
         bellman_ford_algo (\<lambda> u v. prod.snd (get_edge_and_costs_forward nb f u v)) es (length vs - 1)
                                    (bellman_ford_init_algo vs s)"

definition "bellman_ford_backward nb (f::'edge \<Rightarrow> real) s =
         bellman_ford_algo (\<lambda> u v. prod.snd (get_edge_and_costs_backward nb f u v)) es (length vs - 1)
                                    (bellman_ford_init_algo vs s)"
                                    
fun get_target_for_source_aux_aux where
 "get_target_for_source_aux_aux connections b \<gamma>  []= None"|
"get_target_for_source_aux_aux connections b \<gamma> (v#xs) =
 (if b v <  - \<epsilon> * \<gamma> \<and> prod.snd (the (connection_lookup connections v)) < PInfty then Some v else 
           get_target_for_source_aux_aux connections b \<gamma> xs)"

definition "get_target_for_source_aux connections b \<gamma> xs = the(get_target_for_source_aux_aux connections b \<gamma> xs)" 

fun get_source_for_target_aux_aux where
 "get_source_for_target_aux_aux connections b \<gamma>  []= None"|
"get_source_for_target_aux_aux connections b \<gamma> (v#xs) =
 (if b v >   \<epsilon> * \<gamma> \<and> prod.snd (the (connection_lookup connections v)) < PInfty then Some v else 
           get_source_for_target_aux_aux connections b \<gamma> xs)"

definition "get_source_for_target_aux connections b \<gamma> xs =
            the (get_source_for_target_aux_aux connections b \<gamma> xs)"

definition "get_source state = get_source_aux_aux
 (\<lambda> v. abstract_real_map (bal_lookup (balance state)) v) (current_\<gamma> state) vs"
 
definition "get_target state = get_target_aux_aux
 (\<lambda> v. abstract_real_map (bal_lookup (balance state)) v) (current_\<gamma> state) vs"

definition "pair_to_realising_redge_forward state=
(\<lambda>e. prod.fst (get_edge_and_costs_forward 
    (abstract_bool_map (not_blocked_lookup (not_blocked state)))
    (abstract_real_map (flow_lookup (current_flow state))) (prod.fst e) (prod.snd e)))"

definition "get_source_target_path_a state s =
      (let bf = bellman_ford_forward (abstract_bool_map (not_blocked_lookup (not_blocked state)))
                                     (abstract_real_map (flow_lookup (current_flow state))) s
      in case (get_target_for_source_aux_aux bf 
                     (\<lambda> v. abstract_real_map (bal_lookup (balance state)) v)
                                           (current_\<gamma> state) vs) of 
            Some t \<Rightarrow> (let Pbf = itrev (search_rev_path_exec s bf t);
                             P = (map (pair_to_realising_redge_forward state)
                                      (edges_of_vwalk Pbf)) 
                       in Some (t, P))|
            None \<Rightarrow> None)"

definition "pair_to_realising_redge_backward state =
(\<lambda>e. prod.fst (get_edge_and_costs_backward 
                (abstract_bool_map (not_blocked_lookup (not_blocked state)))
                (abstract_real_map (flow_lookup (current_flow state))) (prod.snd e) (prod.fst e)))"

definition "get_source_target_path_b state t =
      (let bf = bellman_ford_backward (abstract_bool_map (not_blocked_lookup (not_blocked state)))
                                     (abstract_real_map (flow_lookup (current_flow state))) t
       in case ( get_source_for_target_aux_aux bf 
                       (\<lambda> v. abstract_real_map (bal_lookup (balance state)) v)
                                           (current_\<gamma> state) vs) of
          Some s \<Rightarrow> let Pbf = search_rev_path_exec t bf s;
                         P = (map (pair_to_realising_redge_backward state)
                                        (edges_of_vwalk Pbf)) 
                    in Some (s, P) |
          None \<Rightarrow> None)"

fun test_all_vertices_zero_balance_aux where
"test_all_vertices_zero_balance_aux b Nil = True"|
"test_all_vertices_zero_balance_aux b (x#xs) = (b x = 0 \<and> test_all_vertices_zero_balance_aux b xs)"

definition "test_all_vertices_zero_balance state_impl = 
            test_all_vertices_zero_balance_aux (\<lambda> x. abstract_real_map (bal_lookup (balance state_impl)) x) vs"

definition "ees = to_list \<E>_impl"
definition "init_flow = foldr (\<lambda> x fl. flow_update x  0 fl) ees flow_empty"
definition "init_bal = \<b>_impl"
definition "init_rep_card = foldr (\<lambda> x fl. rep_comp_update x  (x,1) fl) vs rep_comp_empty"
definition "init_not_blocked = foldr (\<lambda> x fl. not_blocked_update x False fl) ees not_blocked_empty"
end

lemmas Set_Choose = Set_Choose_satisfied

global_interpretation 
  Adj_Map_Specs2: Adj_Map_Specs2 lookup t_set sel edge_map_update adj_inv
                  vset_empty vset_delete vset_insert vset_inv isin 
  defines neighbourhood= Adj_Map_Specs2.neighbourhood
  using Set_Choose
  by(auto intro:  Adj_Map_Specs2.intro 
       simp add:  RBT_Set.empty_def  Adj_Map_Specs2_def Map'_def 
                  Pair_Graph_Specs_satisfied.adjmap.map_update 
                  Pair_Graph_Specs_satisfied.adjmap.invar_update)

lemmas Adj_Map_Specs2 = Adj_Map_Specs2.Adj_Map_Specs2_axioms

lemma invar_filter: "\<lbrakk> set_invar s1\<rbrakk> \<Longrightarrow> set_invar(filter P s1)"
  by (simp add: set_invar_def)

lemma set_get: 
 "\<lbrakk>set_invar s1; \<exists> x. x \<in> to_set s1 \<and> P x \<rbrakk> \<Longrightarrow> \<exists> y. get_from_set P s1 = Some y"
 "\<lbrakk> set_invar s1; get_from_set P s1 = Some x\<rbrakk> \<Longrightarrow> x \<in> to_set s1"
 "\<lbrakk> set_invar s1; get_from_set P s1 = Some x\<rbrakk> \<Longrightarrow> P x"
 "\<lbrakk> set_invar s1; \<And> x. x \<in> to_set s1 \<Longrightarrow> P x = Q x\<rbrakk> 
                     \<Longrightarrow> get_from_set P s1 = get_from_set Q s1" 
  using find_Some_iff[of P s1 x]  find_cong[OF refl, of s1 P Q] find_None_iff[of P s1]
  by (auto simp add: get_from_set_def set_invar_def to_set_def)

lemma are_all: "\<lbrakk>set_invar S\<rbrakk> \<Longrightarrow> are_all P S \<longleftrightarrow> (\<forall> x \<in> to_set S. P x)"
  unfolding to_set_def set_invar_def
  by(induction S) auto

interpretation Set_with_predicate: Set_with_predicate get_from_set filter are_all set_invar to_set
  using set_filter invar_filter  set_get(1,2)
  by (auto intro!: filter_cong Set_with_predicate.intro intro: set_get(3-) set_filter simp add: are_all to_set_def)
     fastforce+

lemmas Set_with_predicate = Set_with_predicate.Set_with_predicate_axioms

interpretation bal_map: Map
  where empty = bal_empty and update=bal_update and lookup= bal_lookup and 
        delete= bal_delete and invar = bal_invar
  using RBT_Map.M.Map_axioms
  by(auto simp add: bal_update_def bal_empty_def  bal_delete_def
                    bal_lookup_def bal_invar_def  M.invar_def Map_def rbt_red_def rbt_def)

lemmas Map_bal = bal_map.Map_axioms

interpretation Map_conv: Map conv_empty conv_update conv_delete conv_lookup conv_invar
  using RBT_Map.M.Map_axioms
  by(auto simp add: conv_update_def conv_empty_def  conv_delete_def
                    conv_lookup_def conv_invar_def  M.invar_def Map_def rbt_red_def rbt_def)

lemmas Map_conv = Map_conv.Map_axioms

interpretation flow_map: Map 
  where empty = flow_empty and update=flow_update and lookup= flow_lookup and 
        delete= flow_delete and invar = flow_invar
  using RBT_Map.M.Map_axioms
  by(auto simp add: flow_update_def flow_empty_def  flow_delete_def
                    flow_lookup_def flow_invar_def  M.invar_def Map_def rbt_red_def rbt_def)

lemmas Map_flow = flow_map.Map_axioms

interpretation Map_not_blocked: 
 Map not_blocked_empty not_blocked_update not_blocked_delete not_blocked_lookup not_blocked_invar
  using RBT_Map.M.Map_axioms
  by(auto simp add: not_blocked_update_def not_blocked_empty_def  not_blocked_delete_def
                    not_blocked_lookup_def not_blocked_invar_def  M.invar_def Map_def 
                    rbt_red_def rbt_def)

lemmas Map_not_blocked = Map_not_blocked.Map_axioms

interpretation Map_rep_comp: Map rep_comp_empty rep_comp_update rep_comp_delete rep_comp_lookup rep_comp_invar
  using RBT_Map.M.Map_axioms
  by(auto simp add: rep_comp_update_def rep_comp_empty_def  rep_comp_delete_def
                    rep_comp_lookup_def rep_comp_invar_def  M.invar_def Map_def rbt_red_def rbt_def)

lemmas Map_rep_comp = Map_rep_comp.Map_axioms

global_interpretation selection_functions: function_generation
  where realising_edges_empty= realising_edges_empty
    and realising_edges_update=realising_edges_update
    and realising_edges_delete=realising_edges_delete
    and realising_edges_lookup= realising_edges_lookup
    and realising_edges_invar= realising_edges_invar

    and bal_empty=bal_empty
    and bal_update=bal_update
    and bal_delete= bal_delete
    and bal_lookup=bal_lookup
    and bal_invar=bal_invar

    and flow_empty=flow_empty
    and flow_update=flow_update
    and flow_delete=flow_delete
    and flow_lookup=flow_lookup
    and flow_invar=flow_invar

    and not_blocked_empty=not_blocked_empty
    and not_blocked_update=not_blocked_update
    and not_blocked_delete=not_blocked_delete
    and not_blocked_lookup=not_blocked_lookup
    and not_blocked_invar= not_blocked_invar

    and rep_comp_empty = rep_comp_empty
    and rep_comp_update = rep_comp_update
    and rep_comp_delete = rep_comp_delete
    and rep_comp_lookup =  rep_comp_lookup
    and rep_comp_invar = rep_comp_invar

    and to_list=to_list
    and fst=fst
    and snd=snd
    and create_edge=create_edge
    and to_set = to_set
    and \<E>_impl = \<E>_impl
    and \<b>_impl = \<b>_impl
    and \<c>_impl = \<c>_impl
    and c_lookup = c_lookup
for fst snd create_edge \<E>_impl \<b>_impl \<c>_impl and 
    c_lookup::"'c_impl \<Rightarrow> 'edge::linorder \<Rightarrow> real option"
defines get_source_target_path_a= selection_functions.get_source_target_path_a
    and get_source_target_path_b =  selection_functions.get_source_target_path_b
    and get_source = selection_functions.get_source
    and get_target = selection_functions.get_target
    and test_all_vertices_zero_balance = selection_functions.test_all_vertices_zero_balance 
    and init_flow = selection_functions.init_flow 
    and init_bal = selection_functions.init_bal 
    and init_rep_card = selection_functions.init_rep_card 
    and init_not_blocked = selection_functions.init_not_blocked 
    and N = selection_functions.N
    and get_path = selection_functions.get_path 
    and get_target_for_source_aux_aux=selection_functions.get_target_for_source_aux_aux
    and get_source_for_target_aux_aux = selection_functions.get_source_for_target_aux_aux
    and get_edge_and_costs_backward = selection_functions.get_edge_and_costs_backward
    and get_edge_and_costs_forward = selection_functions.get_edge_and_costs_forward
    and bellman_ford_backward =selection_functions.bellman_ford_backward
    and bellman_ford_forward = selection_functions.bellman_ford_forward
    and pair_to_realising_redge_forward=selection_functions.pair_to_realising_redge_forward
    and pair_to_realising_redge_backward=selection_functions.pair_to_realising_redge_backward
    and get_target_aux_aux = selection_functions.get_target_aux_aux
    and get_source_aux_aux = selection_functions.get_source_aux_aux
    and ees =selection_functions.ees
    and vs = selection_functions.vs
    and find_cheapest_backward=selection_functions.find_cheapest_backward
    and find_cheapest_forward = selection_functions.find_cheapest_forward
    and realising_edges = selection_functions.realising_edges
    and \<epsilon> = selection_functions.\<epsilon>
    and es = selection_functions.es
    and realising_edges_general = selection_functions.realising_edges_general
    and \<E>_list = selection_functions.\<E>_list
    and \<u> = selection_functions.\<u>
    and \<c> = selection_functions.\<c>
    and \<E> = selection_functions.\<E>
    and \<b> = selection_functions.\<b>
  by(auto intro!: function_generation.intro 
        simp add: Map_realising_edges Map_bal Map_flow Map_not_blocked Map_rep_comp)

lemmas function_generation = selection_functions.function_generation_axioms

global_interpretation orlins_spec: orlins_spec 
  where edge_map_update =edge_map_update
    and vset_empty = "\<emptyset>\<^sub>N"
    and vset_delete = vset_delete 
    and vset_insert=vset_insert 
    and vset_inv = vset_inv
    and isin = isin 
    and get_from_set = get_from_set 
    and filter = filter 
    and are_all = are_all 
    and set_invar = set_invar 
    and to_set = to_set 
    and lookup = lookup
    and t_set = t_set 
    and sel=sel 
    and adjmap_inv = adj_inv
    and empty_forest=  map_empty
    and get_path = get_path 

    and flow_empty = flow_empty 
    and flow_update = flow_update 
    and flow_delete = flow_delete 
    and flow_lookup= flow_lookup 
    and flow_invar = flow_invar 

    and bal_empty = bal_empty 
    and bal_update=bal_update 
    and bal_delete = bal_delete 
    and bal_lookup =bal_lookup 
    and bal_invar=bal_invar 

    and rep_comp_empty=rep_comp_empty 
    and rep_comp_update =rep_comp_update 
    and rep_comp_delete=rep_comp_delete 
    and rep_comp_lookup=rep_comp_lookup 
    and rep_comp_invar=rep_comp_invar 

    and conv_empty =conv_empty 
    and conv_update = conv_update 
    and conv_delete = conv_delete 
    and conv_lookup=conv_lookup 
    and conv_invar = conv_invar

    and not_blocked_update=not_blocked_update 
    and not_blocked_empty=not_blocked_empty 
    and not_blocked_delete=not_blocked_delete 
    and not_blocked_lookup=not_blocked_lookup 
    and not_blocked_invar= not_blocked_invar 

    and rep_comp_upd_all = rep_comp_upd_all
    and not_blocked_upd_all =  not_blocked_upd_all 
    and flow_update_all = flow_update_all 
    and get_max = get_max 

    and get_source_target_path_a= 
    "get_source_target_path_a fst snd create_edge  \<E>_impl \<c>_impl c_lookup"
    and get_source_target_path_b =  
         "get_source_target_path_b fst snd create_edge \<E>_impl \<c>_impl c_lookup"
    and get_source =  "get_source fst snd \<E>_impl"
    and get_target = "get_target fst snd  \<E>_impl"
    and test_all_vertices_zero_balance = "test_all_vertices_zero_balance fst snd \<E>_impl"

    and init_flow = "init_flow  \<E>_impl"
    and init_bal = "init_bal  \<b>_impl" 
    and init_rep_card = "init_rep_card fst snd \<E>_impl"
    and init_not_blocked = "init_not_blocked \<E>_impl"

    and N = "N fst snd \<E>_impl"
    and snd = snd
    and fst = fst
    and create_edge = create_edge 
    and  \<c> = "\<c> \<c>_impl c_lookup"
    and  \<E> = "\<E>  \<E>_impl"
    and \<E>_impl = \<E>_impl
    and \<u> = \<u>
    and \<b> = "\<b> \<b>_impl"
    and \<epsilon> = \<epsilon>
  for fst snd create_edge \<E>_impl \<b>_impl \<c>_impl c_lookup \<epsilon>

defines initial = orlins_spec.initial 
    and orlins = orlins_spec.orlins 
    and send_flow = orlins_spec.send_flow
    and maintain_forest =orlins_spec.maintain_forest 
    and augment_edge = orlins_spec.augment_edge 
    and augment_edges = orlins_spec.augment_edges 
    and orlins_impl = orlins_spec.orlins_impl
    and send_flow_impl = orlins_spec.send_flow_impl 
    and maintain_forest_impl =orlins_spec.maintain_forest_impl 
    and augment_edge_impl = orlins_spec.augment_edge_impl
    and augment_edges_impl = orlins_spec.augment_edges_impl
    and to_redge_path = orlins_spec.to_redge_path 
    and add_direction = orlins_spec.add_direction
    and move_balance = orlins_spec.move_balance
    and move= orlins_spec.move 
    and insert_undirected_edge = orlins_spec.insert_undirected_edge
    and abstract_conv_map_i = orlins_spec.abstract_conv_map
    and abstract_not_blocked_map_i = orlins_spec.abstract_not_blocked_map 
    and abstract_rep_map = orlins_spec.abstract_rep_map 
    and abstract_comp_map = orlins_spec.abstract_comp_map 
    and abstract_flow_map_i = orlins_spec.abstract_flow_map 
    and abstract_bal_map_i = orlins_spec.abstract_bal_map
    and new_\<gamma>= orlins_spec.new_\<gamma>
    and make_pair = orlins_spec.make_pair
    and neighbourhood' = orlins_spec.neighbourhood'
  using  Map_bal Map_conv Map_flow Map_not_blocked Map_rep_comp 
  by(auto intro!: orlins_spec.intro algo_spec.intro maintain_forest_spec.intro rep_comp_upd_all
                  send_flow_spec.intro maintain_forest_spec.intro flow_update_all get_max not_blocked_upd_all
                  map_update_all.intro map_update_all_axioms.intro
        simp add: Set_with_predicate Adj_Map_Specs2)

lemmas [code] = orlins_spec.orlins_impl.simps[folded orlins_impl_def]

lemmas orlins_spec = orlins_spec.orlins_spec_axioms
lemmas send_flow_spec = orlins_spec.send_flow_spec_axioms
lemmas algo_spec = orlins_spec.algo_spec_axioms
lemmas maintain_forest_spec = orlins_spec.maintain_forest_spec_axioms

subsection \<open>Proofs\<close>

lemma set_filter: 
 "\<lbrakk> set_invar s1 \<rbrakk> \<Longrightarrow> to_set(filter P s1) = to_set s1 - {x. x \<in> to_set s1 \<and> \<not> P x}"
 "\<lbrakk> set_invar s1; \<And> x. x \<in> to_set s1 \<Longrightarrow> P x =  Q x \<rbrakk> \<Longrightarrow> filter P s1 = filter Q s1"
  using filter_cong[OF refl, of s1 P Q]
  by (auto simp add: set_invar_def to_set_def)

lemma flow_invar_Leaf: "flow_invar Leaf"
  by (metis RBT_Set.empty_def flow_empty_def flow_map.invar_empty)

lemma flow_invar_fold: 
 "\<lbrakk>flow_invar T; (\<And> T e. flow_invar T \<Longrightarrow> flow_invar (f e T))\<rbrakk>
    \<Longrightarrow> flow_invar ( foldr (\<lambda> e tree. f e tree) list T)"
  by(induction list) auto

lemma dom_fold:
"flow_invar T \<Longrightarrow>
 dom (flow_lookup (foldr (\<lambda> e tree. flow_update (f e) (g e) tree) AS T))
 = dom (flow_lookup T) \<union> f ` set AS"
  by(induction AS)
    (auto simp add: flow_map.map_update flow_invar_fold flow_map.invar_update)

lemma fold_lookup: 
 "\<lbrakk>flow_invar T; bij f\<rbrakk>
   \<Longrightarrow>   flow_lookup (foldr (\<lambda> e tree. flow_update (f e) (g e) tree) AS T) x
       = (if inv f x \<in> set AS then Some (g (inv f x)) else flow_lookup T x)"
  apply(induction AS)
  subgoal by auto
  apply(subst foldr_Cons, subst o_apply)
  apply(subst flow_map.map_update)
   apply(subst flow_invar_fold)
   apply simp
    apply(rule flow_map.invar_update)
    apply simp
    apply simp
  subgoal for a AS
    using bij_inv_eq_iff bij_betw_inv_into_left 
     by  (fastforce intro: flow_map.invar_update simp add: bij_betw_def)
   done

interpretation bal_map: Map where empty = bal_empty and update=bal_update and lookup= bal_lookup
                             and delete= bal_delete and invar = bal_invar
  using Map_bal by auto

lemma bal_invar_fold: 
  "bal_invar bs \<Longrightarrow> bal_invar (foldr (\<lambda>xy tree.  bal_update  (g xy) (f xy tree) tree) ES bs)" 
  by(induction ES)(auto simp add: bal_map.invar_update)

lemma bal_dom_fold: 
  "bal_invar bs \<Longrightarrow> 
    dom (bal_lookup (foldr (\<lambda>xy tree.  bal_update  (g xy) (f xy tree) tree) ES bs))
  = dom (bal_lookup bs) \<union> g ` (set ES)" 
  apply(induction ES)
  subgoal
    by auto
  by(simp add: dom_def, subst bal_map.map_update) (auto intro: bal_invar_fold)

interpretation rep_comp_map: 
 Map where empty = rep_comp_empty and update=rep_comp_update 
       and lookup= rep_comp_lookup and delete= rep_comp_delete and invar = rep_comp_invar
  using Map_rep_comp by auto

interpretation conv_map: 
  Map where empty = conv_empty and update=conv_update and lookup= conv_lookup
        and delete= conv_delete and invar = conv_invar
  using Map_conv by auto

interpretation not_blocked_map: 
  Map where empty = not_blocked_empty and update=not_blocked_update and lookup= not_blocked_lookup
        and delete= not_blocked_delete and invar = not_blocked_invar
  using Map_not_blocked by auto

lemma bal_invar_b:"bal_invar (foldr (\<lambda> xy tree. update (prod.fst xy) (prod.snd xy) tree) xs Leaf)"
  by(induction xs)
    (auto simp add: invc_upd(2) update_def invh_paint invh_upd(1)  color_paint_Black
                    bal_invar_def M.invar_def rbt_def rbt_red_def inorder_paint inorder_upd 
                    sorted_upd_list)

lemma dom_update_insert:"M.invar T \<Longrightarrow> dom (lookup (update x y T)) = Set.insert x (dom (lookup T))" 
  by(auto simp add: M.map_update[simplified update_def] update_def dom_def)

lemma M_invar_fold:"M.invar (foldr (\<lambda> xy tree. update (prod.fst xy) (prod.snd xy) tree) list Leaf)"
  by(induction list) (auto intro: M.invar_update M.invar_empty[simplified RBT_Set.empty_def]) 

lemma M_dom_fold: "dom (lookup (foldr (\<lambda> xy tree. update (prod.fst xy) (prod.snd xy) tree) list Leaf))
           = set (map prod.fst list)"
  by(induction list)(auto simp add: dom_update_insert[OF M_invar_fold])

hide_const RBT.B

locale function_generation_proof = 

function_generation where 
          to_set =" to_set:: 'edge_set_impl \<Rightarrow> 'edge set"
      and fst = "fst :: ('edge::linorder) \<Rightarrow> ('a::linorder)"
      and snd = "snd :: ('edge::linorder) \<Rightarrow> 'a"
      and not_blocked_update = "not_blocked_update ::'edge \<Rightarrow> bool \<Rightarrow> 'not_blocked_impl\<Rightarrow> 'not_blocked_impl"
      and flow_update =  "flow_update::'edge \<Rightarrow> real \<Rightarrow> 'f_impl \<Rightarrow> 'f_impl"
      and bal_update = "bal_update:: 'a \<Rightarrow> real \<Rightarrow> 'b_impl \<Rightarrow> 'b_impl" 
      and rep_comp_update="rep_comp_update:: 'a \<Rightarrow> 'a \<times> nat \<Rightarrow> 'r_comp_impl\<Rightarrow> 'r_comp_impl"+

Set_with_predicate  where 
          get_from_set="get_from_set::('edge \<Rightarrow> bool) \<Rightarrow>  'edge_set_impl \<Rightarrow> 'edge option"
      and to_set =to_set +

multigraph: multigraph fst snd create_edge \<E>+

Set_with_predicate: Set_with_predicate get_from_set filter are_all set_invar to_set +

rep_comp_maper: Map  rep_comp_empty "rep_comp_update::'a \<Rightarrow> ('a \<times> nat) \<Rightarrow> 'r_comp_impl \<Rightarrow> 'r_comp_impl"
                     rep_comp_delete rep_comp_lookup rep_comp_invar +

conv_map: Map  conv_empty "conv_update::'a \<times> 'a \<Rightarrow> 'edge Redge \<Rightarrow> 'conv_impl \<Rightarrow> 'conv_impl"
               conv_delete conv_lookup conv_invar +

not_blocked_map: Map not_blocked_empty "not_blocked_update::'edge \<Rightarrow> bool \<Rightarrow> 'not_blocked_impl\<Rightarrow> 'not_blocked_impl"
                     not_blocked_delete not_blocked_lookup not_blocked_invar +

rep_comp_iterator: Map_iterator rep_comp_invar rep_comp_lookup rep_comp_upd_all+

flow_iterator: Map_iterator flow_invar flow_lookup flow_update_all+

not_blocked_iterator: Map_iterator not_blocked_invar not_blocked_lookup not_blocked_upd_all
for get_from_set
    to_set 
    fst snd 
    rep_comp_update 
    conv_empty
    conv_delete 
    conv_lookup 
    conv_invar 
    conv_update 
    not_blocked_update 
    flow_update  
    bal_update 
    rep_comp_upd_all 
    flow_update_all 
    not_blocked_upd_all + 

fixes get_max::"('a \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> 'b_impl \<Rightarrow> real"
assumes  \<E>_impl_invar: "set_invar \<E>_impl"
and invar_b_impl: "bal_invar \<b>_impl"
and b_impl_dom: "dVs (make_pair ` to_set \<E>_impl) = dom (bal_lookup \<b>_impl)"
and N_gre_0: "N > 0"
and get_max: "\<And> b f. \<lbrakk>bal_invar b; dom (bal_lookup b) \<noteq> {}\<rbrakk>
              \<Longrightarrow> get_max f b = Max {f y (the (bal_lookup b y)) | y. y \<in> dom (bal_lookup b)}"
and to_list: "\<And> E. set_invar E \<Longrightarrow> to_set E = set (to_list E)"
             "\<And> E. set_invar E \<Longrightarrow> distinct (to_list E)"
begin

lemmas rep_comp_upd_all = rep_comp_iterator.update_all
lemmas flow_update_all = flow_iterator.update_all
lemmas not_blocked_upd_all = not_blocked_iterator.update_all

notation vset_empty ("\<emptyset>\<^sub>N")

lemma make_pairs_are:"multigraph.make_pair = make_pair"
                     "multigraph_spec.make_pair fst snd = make_pair"
  by(auto intro!: ext 
simp add: make_pair_def multigraph.make_pair_def multigraph_spec.make_pair_def)

lemmas create_edge = local.multigraph.create_edge[simplified  make_pairs_are(1)]

lemma vs_are: "dVs (make_pair ` \<E>) = set (map fst \<E>_list) \<union> set (map snd \<E>_list)"
  using multigraph.make_pair[OF refl refl] to_list \<E>_impl_invar
  by(auto simp add: \<E>_def \<E>_list_def dVs_def  make_pairs_are)

lemma \<E>_impl: "set_invar \<E>_impl"  "\<exists> e. e \<in> (to_set \<E>_impl)" "finite \<E>"
and  b_impl: "bal_invar \<b>_impl" "dVs (make_pair ` (to_set \<E>_impl)) = dom (bal_lookup \<b>_impl)"
and \<epsilon>_axiom: "0 < \<epsilon>" "\<epsilon> \<le> 1 / 2" "\<epsilon> \<le> 1/ (real (card (multigraph.\<V>)))" "\<epsilon> < 1/2"
 proof(goal_cases)
  case 1
  then show ?case 
    by (simp add: \<E>_impl_invar)
next
  case 2
  then show ?case 
    using local.\<E>_def local.multigraph.E_not_empty by auto
next
  case 3
  then show ?case
    by (simp add: local.multigraph.finite_E)
next
  case 4
  then show ?case 
    using invar_b_impl by auto
next
  case 5
  then show ?case 
    using b_impl_dom by auto
next
  case 6
  then show ?case 
    using \<E>_impl_invar local.\<E>_def local.multigraph.E_not_empty local.to_list(1) 
    by (auto simp add: \<epsilon>_def N_def ) 
next
  case 7
  then show ?case 
    by(auto simp add: \<epsilon>_def)
next
  case 8
  then show ?case 
    using vs_are N_gre_0
  by(auto simp add: \<epsilon>_def N_def to_set_def vs_are insert_commute \<E>_list_def
                  length_remdups_card_conv frac_le make_pairs_are)
next
  case 9
  then show ?case
    by(auto simp add: \<epsilon>_def)
qed

lemma N_def': "N =card VV"
  using \<E>_impl_invar  local.to_list(1)
 by(auto intro!: cong[of card, OF refl] 
         simp add:  N_def dVs_def \<E>_def to_set_def length_remdups_card_conv make_pair_def)

lemma \<E>_impl_basic: "set_invar \<E>_impl"  "\<exists> e. e \<in> (to_set \<E>_impl)" "finite \<E>"
  using \<E>_impl by auto

interpretation cost_flow_network: 
  cost_flow_network where \<E> = \<E> and \<c> = \<c> and \<u> = \<u>
                      and fst = fst and snd = snd and create_edge = create_edge
  using  \<E>_def multigraph.multigraph_axioms
  by(auto simp add: \<u>_def cost_flow_network_def flow_network_axioms_def flow_network_def)

lemmas cost_flow_network[simp] = cost_flow_network.cost_flow_network_axioms

abbreviation "\<cc> \<equiv> cost_flow_network.\<cc>"
abbreviation "to_edge == cost_flow_network.to_vertex_pair"
abbreviation "oedge == flow_network_spec.oedge"
abbreviation "rcap == cost_flow_network.rcap"

lemma make_pair_fst_snd: "make_pair e = (fst e, snd e)"
  using multigraph.make_pair' make_pairs_are by simp

lemma es_is_E:"set es = make_pair ` \<E> \<union> {(u, v) | u v.  (v, u) \<in> make_pair ` \<E>}"
  using to_list(1)[OF \<E>_impl_basic(1)] 
  by(auto simp add: es_def to_list_def \<E>_def  make_pair_fst_snd)

lemma vs_is_V: "set vs = VV"
proof-
  have 1:"x \<in> prod.fst ` (make_pair ` local.\<E> \<union> {(u, v). (v, u) \<in> make_pair ` local.\<E>}) \<Longrightarrow>
         x \<in> local.multigraph.\<V>" for x
  proof(goal_cases)
    case 1
  then obtain e where e_pr:"x = prod.fst e"
                "e \<in> make_pair ` \<E> \<union> {(u, v). (v, u) \<in> make_pair ` \<E>}" by auto
  hence aa:"e \<in> make_pair ` \<E> \<or> prod.swap e \<in> make_pair ` \<E>" by auto
  show ?case  
  proof-
    obtain pp  where
      f1: "\<forall>X1. pp X1 = (fst X1, snd X1)"
      by moura
    then have "e \<in> pp ` \<E> \<or> prod.swap e \<in> pp ` \<E>"
      using aa make_pair_fst_snd by auto
    then have "prod.fst e \<in> dVs (pp ` \<E>)" 
      by(auto intro: dVsI'(1) dVsI(2) simp add: prod.swap_def)
    then have "prod.fst e \<in> dVs ((\<lambda>e. (fst e, snd e)) ` \<E>)"
      using f1 by force
    thus "x \<in> local.multigraph.\<V>"
      by (auto simp add: e_pr(1) make_pair_fst_snd make_pairs_are)
  qed
qed
 have 2:"x \<in> local.multigraph.\<V> \<Longrightarrow>
         x \<in> prod.fst ` (make_pair ` local.\<E> \<union> {(u, v). (v, u) \<in> make_pair ` local.\<E>})" for x
  proof(goal_cases)
    case 1
    note 2 = this
  then obtain a b where "x \<in>{a,b}" "(a,b) \<in> make_pair ` \<E>" 
    by (metis in_dVsE(1) insert_iff make_pairs_are)
  then show ?case by force
qed
  show ?thesis
    by(fastforce intro: 1 2 simp add: vs_def  es_is_E  dVsI' make_pairs_are)
qed

lemma vs_and_es: "vs \<noteq> []" "set vs = dVs (set es)" "distinct vs" "distinct es"
  using \<E>_def  es_is_E  vs_def vs_is_V es_is_E \<E>_impl_basic
  by (auto simp add: vs_def es_def dVs_def )

definition "no_cycle_cond = (\<not> has_neg_cycle make_pair (function_generation.\<E> \<E>_impl to_set) \<c>)"

context
  assumes no_cycle_cond: no_cycle_cond
begin

lemma  conservative_weights: 
 "\<nexists> C. closed_w (make_pair ` \<E>) (map make_pair C) \<and> (set C \<subseteq> \<E>) \<and> foldr (\<lambda> e acc. acc + \<c> e) C 0 < 0"
  using no_cycle_cond 
  by(auto simp add: no_cycle_cond_def has_neg_cycle_def
          ab_semigroup_add_class.add.commute[of _ "\<c> _"])

thm algo_axioms_def

lemma algo_axioms: " algo_axioms snd \<u> \<c> \<E> set_invar to_set lookup adj_inv
                \<epsilon> \<E>_impl map_empty N fst"
  using  \<epsilon>_axiom  \<E>_impl(1)  no_cycle_cond
  by(auto intro!: algo_axioms.intro 
        simp add: \<u>_def \<E>_def N_def' Pair_Graph_Specs_satisfied.adjmap.map_empty
                  Pair_Graph_Specs_satisfied.adjmap.invar_empty make_pairs_are no_cycle_cond_def)
 
lemmas dfs_defs = dfs.initial_state_def

lemma same_digraph_abses:
 "Adj_Map_Specs2.digraph_abs = Pair_Graph_Specs_satisfied.digraph_abs"
and same_neighbourhoods: 
 "Adj_Map_Specs2.neighbourhood = Pair_Graph_Specs_satisfied.neighbourhood"
 by(auto intro!: ext 
       simp add: Adj_Map_Specs2.digraph_abs_def Pair_Graph_Specs_satisfied.digraph_abs_def
                Adj_Map_Specs2.neighbourhood_def Pair_Graph_Specs_satisfied.neighbourhood_def)

lemma maintain_forest_axioms_extended: 
  assumes "maintain_forest_spec.maintain_forest_get_path_cond \<emptyset>\<^sub>N vset_inv isin lookup
           t_set  adj_inv get_path u v (E::
                   (('a \<times> ('a \<times> color) tree) \<times> color) tree) p q"
  shows "vwalk_bet (Adj_Map_Specs2.digraph_abs  E) u p v"
        "distinct p"
proof(insert maintain_forest_spec.maintain_forest_get_path_cond_unfold_meta[OF
                     maintain_forest_spec assms], goal_cases)
  case 1
  note assms = this
  have graph_invar: "Pair_Graph_Specs_satisfied.graph_inv E"
  and finite_graph:"Pair_Graph_Specs_satisfied.finite_graph E"
  and finite_neighbs:"Pair_Graph_Specs_satisfied.finite_vsets E"
    using assms(4) by (auto elim!: Instantiation.Adj_Map_Specs2.good_graph_invarE)
  obtain e where e_prop:"e \<in> (Adj_Map_Specs2.digraph_abs  E)" "u = prod.fst e"
    using assms(1) assms(5) no_outgoing_last 
    by(unfold vwalk_bet_def Pair_Graph_Specs_satisfied.digraph_abs_def) fastforce
  hence neighb_u: "Adj_Map_Specs2.neighbourhood  E u \<noteq> vset_empty"
    using   assms(2)
             Pair_Graph_Specs_satisfied.are_connected_absI[OF _  graph_invar, 
             of "prod.fst e" "prod.snd e", simplified]  
    by(auto simp add: same_neighbourhoods same_digraph_abses)
  have q_non_empt: "q \<noteq> []"
    using assms(1) by auto
  obtain d where "d \<in> (Adj_Map_Specs2.digraph_abs  E)" "v = prod.snd d"
    using assms(1)  assms(5)  singleton_hd_last'[OF q_non_empt]
           vwalk_append_edge[of _ "butlast q" "[last q]",simplified append_butlast_last_id[OF q_non_empt]] 
    by(force simp add: vwalk_bet_def Adj_Map_Specs2.digraph_abs_def)
  have u_in_Vs:"u \<in> dVs (Adj_Map_Specs2.digraph_abs  E)" 
    using assms(1) assms(2)  by auto
  have dfs_axioms: "DFS.DFS_axioms isin t_set adj_inv \<emptyset>\<^sub>N vset_inv lookup 
                         E u"
    using finite_graph finite_neighbs graph_invar u_in_Vs
    by(simp only: dfs.DFS_axioms_def same_neighbourhoods same_digraph_abses)
  have dfs_thms: "DFS_thms map_empty delete vset_insert isin t_set sel update adj_inv vset_empty vset_delete
                   vset_inv vset_union vset_inter vset_diff lookup E u"
    by(auto intro!: DFS_thms.intro DFS_thms_axioms.intro simp add: dfs.DFS_axioms dfs_axioms)
  have dfs_dom:"DFS.DFS_dom vset_insert sel vset_empty vset_diff lookup 
    E v (dfs_initial u)"
    using DFS_thms.initial_state_props(6)[OF dfs_thms]
    by(simp add:  dfs_initial_def dfs_initial_state_def DFS_thms.initial_state_props(6) dfs_axioms)
  have rectified_map_subset:"dfs.Graph.digraph_abs E \<subseteq> 
                (Adj_Map_Specs2.digraph_abs E)"
    by (simp add: assms(2) same_neighbourhoods same_digraph_abses)
  have rectified_map_subset_rev:"Adj_Map_Specs2.digraph_abs  E 
                                 \<subseteq> dfs.Graph.digraph_abs E"
    by (simp add: assms(2) same_neighbourhoods same_digraph_abses)
  have reachable:"DFS_state.return (dfs E v (dfs_initial u)) = Reachable"
  proof(rule ccontr,rule DFS.return.exhaust[of "DFS_state.return (dfs E v (dfs_initial u))"],goal_cases)
    case 2
    hence "\<nexists>p. distinct p \<and> vwalk_bet (dfs.Graph.digraph_abs E) u p v"
      using  DFS_thms.DFS_correct_1[OF dfs_thms, of v]  DFS_thms.DFS_impl_to_DFS[OF dfs_thms, of v] 
      by (auto simp add:  dfs_def dfs_initial_def dfs_initial_state_def simp add: dfs_impl_def)
    moreover obtain q' where "vwalk_bet (Adj_Map_Specs2.digraph_abs  E ) u q' v" "distinct q'"
      using vwalk_bet_to_distinct_is_distinct_vwalk_bet[OF assms(1)]
      by(auto simp add: distinct_vwalk_bet_def )
    moreover hence "vwalk_bet (dfs.Graph.digraph_abs E) u q' v"
      by (meson rectified_map_subset_rev vwalk_bet_subset)
    ultimately show False by auto
  next
  qed simp
  have "vwalk_bet  (dfs.Graph.digraph_abs E)
            u (rev (stack (dfs E v (dfs_initial u)))) v"
    using reachable DFS_thms.DFS_impl_to_DFS[OF dfs_thms, of v]
    by(auto intro!: DFS_thms.DFS_correct_2[OF dfs_thms, of v]
         simp add: dfs_initial_def  dfs_def dfs_axioms dfs_impl_def dfs_initial_state_def) 
  thus "vwalk_bet (Adj_Map_Specs2.digraph_abs E ) u p v"
    using  rectified_map_subset vwalk_bet_subset assms(2)
    by (simp add:  local.get_path_def)
  show "distinct p" 
    using DFS_thms.DFS_correct_2(2)[OF dfs_thms]
    using  DFS_thms.initial_state_props(1,3)[OF dfs_thms]
           dfs_dom DFS_thms.DFS_impl_to_DFS[OF dfs_thms] reachable
    by(auto simp add:  assms(2) get_path_def same_neighbourhoods same_digraph_abses
                       dfs_def dfs_impl_def dfs_initial_def dfs_initial_state_def) 
qed

lemma flow_map_update_all: 
  "map_update_all flow_empty flow_update flow_delete flow_lookup flow_invar flow_update_all"
  using local.flow_update_all
  by(fastforce intro!: map_update_all.intro map_update_all_axioms.intro
           simp add: Map_flow.Map_axioms domIff )

lemma rep_comp_map_update_all: 
  "map_update_all rep_comp_empty rep_comp_update rep_comp_delete 
                  rep_comp_lookup rep_comp_invar rep_comp_upd_all"
  using local.rep_comp_upd_all
  by(fastforce intro!: map_update_all.intro map_update_all_axioms.intro
           simp add: Map_rep_comp.Map_axioms domIff Map_axioms)

lemma not_blocked_upd_all_locale:
  "map_update_all not_blocked_empty not_blocked_update not_blocked_delete
                  not_blocked_lookup not_blocked_invar not_blocked_upd_all"
  using local.not_blocked_upd_all
  by(fastforce intro!: map_update_all.intro map_update_all_axioms.intro
           simp add: Map_not_blocked.Map_axioms domIff )

interpretation algo: algo
  where \<E> = \<E> 
    and \<c> = \<c> 
    and \<u> = \<u> 
    and edge_map_update = edge_map_update 
    and vset_empty = vset_empty
    and vset_delete= vset_delete 
    and vset_insert = vset_insert
    and vset_inv = vset_inv 
    and isin = isin 
    and get_from_set=get_from_set
    and filter=filter 
    and are_all=are_all 
    and set_invar=set_invar
    and to_set=to_set 
    and lookup=lookup
    and t_set=t_set 
    and sel=sel 
    and adjmap_inv=adj_inv
    and \<epsilon> = \<epsilon> 
    and \<E>_impl=\<E>_impl 
    and empty_forest=map_empty
    and \<b> = \<b> and N = N
    and snd = snd 
    and fst = fst 
    and create_edge=create_edge

    and flow_empty = flow_empty 
    and flow_lookup = flow_lookup 
    and flow_update = flow_update
    and flow_delete=flow_delete 
    and flow_invar = flow_invar

    and bal_empty = bal_empty 
    and bal_lookup = bal_lookup 
    and bal_update = bal_update
    and bal_delete=bal_delete 
    and bal_invar = bal_invar

    and conv_empty = conv_empty 
    and conv_lookup = conv_lookup 
    and conv_update = conv_update
    and conv_delete=conv_delete 
    and conv_invar = conv_invar

    and rep_comp_empty = rep_comp_empty 
    and rep_comp_lookup = rep_comp_lookup 
    and rep_comp_update = rep_comp_update
    and rep_comp_delete=rep_comp_delete 
    and rep_comp_invar = rep_comp_invar

    and not_blocked_empty = not_blocked_empty 
    and not_blocked_lookup = not_blocked_lookup 
    and not_blocked_update = not_blocked_update
    and not_blocked_delete=not_blocked_delete 
    and not_blocked_invar = not_blocked_invar
  using cost_flow_network 
  by(auto intro!: algo.intro algo_spec.intro 
        simp add: Adj_Map_Specs2 algo_axioms algo_def Set_with_predicate_axioms flow_map_update_all
                  Map_bal.Map_axioms rep_comp_map_update_all  conv_map.Map_axioms not_blocked_upd_all_locale)

lemmas algo = algo.algo_axioms

lemma maintain_forest_axioms: 
 "maintain_forest_axioms \<emptyset>\<^sub>N vset_inv (isin:: ('a \<times> color) tree \<Rightarrow> 'a \<Rightarrow> bool) lookup t_set 
                         adj_inv local.get_path"
  by(auto intro!: maintain_forest_axioms.intro maintain_forest_axioms_extended)

interpretation maintain_forest: 
     Maintain_Forest.maintain_forest snd  create_edge \<u> \<E> \<c> edge_map_update vset_empty
     vset_delete vset_insert vset_inv isin filter are_all set_invar to_set lookup t_set sel
     adj_inv flow_empty flow_update flow_delete flow_lookup flow_invar bal_empty bal_update
     bal_delete bal_lookup bal_invar rep_comp_empty rep_comp_update rep_comp_delete rep_comp_lookup
     rep_comp_invar conv_empty conv_update conv_delete conv_lookup conv_invar not_blocked_update
     not_blocked_empty not_blocked_delete not_blocked_lookup not_blocked_invar rep_comp_upd_all
     flow_update_all not_blocked_upd_all \<b> get_max \<epsilon> N get_from_set map_empty \<E>_impl get_path fst
 by(auto intro!: maintain_forest.intro maintain_forest_axioms
        simp add: algo.algo_spec_axioms maintain_forest_spec_def algo)

lemma realising_edges_general_invar:
"realising_edges_invar (realising_edges_general list)"
  unfolding realising_edges_general_def
  by(induction list)
  (auto intro: Map_realising.invar_update split: option.split
       simp add: Map_realising.invar_empty realising_edges_empty_def 
                 realising_edges_invar_def realising_edges_update_def) 

lemma realising_edges_general_dom:
  "(u, v) \<in> set (map make_pair list)
  \<longleftrightarrow> realising_edges_lookup (realising_edges_general list) (u, v) \<noteq> None"
  unfolding realising_edges_general_def
proof(induction list)
  case Nil
  then show ?case 
    by(simp add: realising_edges_lookup_def realising_edges_empty_def Map_realising.map_empty)
next
  case (Cons e list)
  show ?case 
  proof(cases "make_pair e = (u, v)")
    case True
    show ?thesis 
      apply(subst foldr.foldr_Cons, subst o_apply)
      apply(subst realising_edges_general_def[ symmetric])+
      using True 
      by(auto intro: Map_realising.invar_update split: option.split
           simp add: Map_realising.map_update realising_edges_update_def realising_edges_lookup_def
                     realising_edges_general_invar[simplified realising_edges_invar_def])
  next
    case False
    hence in_list:"(u, v) \<in> set (map make_pair list)  
                   \<longleftrightarrow> (u, v) \<in> set (map make_pair (e#list))"
      using make_pair_fst_snd[of e] by auto
    note ih = Cons(1)[simplified in_list]
      show ?thesis
      unfolding Let_def 
      using realising_edges_general_invar False
      by(subst foldr.foldr_Cons, subst o_apply,subst ih[simplified Let_def])
        (auto split: option.split 
              simp add: realising_edges_update_def realising_edges_lookup_def
                        Map_realising.map_update realising_edges_invar_def
                         realising_edges_general_def[simplified Let_def, symmetric] )
  qed
qed

lemma realising_edges_dom:
    "((u, v) \<in> set (map make_pair \<E>_list)) =
    (realising_edges_lookup realising_edges (u, v) \<noteq> None)"
  using realising_edges_general_dom 
  by(fastforce simp add: realising_edges_def)

lemma not_both_realising_edges_none:
"(u, v) \<in> set es \<Longrightarrow> realising_edges_lookup realising_edges (u, v) \<noteq> None \<or>
                      realising_edges_lookup realising_edges (v, u) \<noteq> None"
  using realising_edges_dom make_pair_fst_snd
  by(auto simp add:  es_def \<E>_list_def)

lemma find_cheapest_forward_props:
   assumes "(beste, bestc) = find_cheapest_forward f nb list e c"
           "edges_and_costs = Set.insert (e, c)
               {(e, ereal (\<c> e)) | e. e \<in> set list \<and> nb e \<and> ereal (f e) < \<u> e}"
     shows "(beste, bestc) \<in> edges_and_costs \<and>
               (\<forall> (ee, cc) \<in> edges_and_costs. bestc \<le> cc)"
  using assms
  unfolding find_cheapest_forward_def
  by(induction list arbitrary: edges_and_costs beste bestc)
    (auto split: if_split prod.split , 
           insert ereal_le_less nless_le order_less_le_trans,  fastforce+)

lemma find_cheapest_backward_props:
   assumes "(beste, bestc) = find_cheapest_backward f nb list e c"
           "edges_and_costs = Set.insert (e, c) 
                 {(e, ereal (- \<c> e)) | e. e \<in> set list \<and> nb e \<and> ereal (f e) > 0}"
    shows "(beste, bestc) \<in> edges_and_costs \<and>
              (\<forall> (ee, cc) \<in> edges_and_costs. bestc \<le> cc)"
  using assms
  unfolding find_cheapest_backward_def
  by(induction list arbitrary: edges_and_costs beste bestc)
    (auto split: if_split prod.split,
     insert ereal_le_less less_le_not_le nless_le order_less_le_trans, fastforce+)

lemma get_edge_and_costs_forward_not_MInfty:
  "prod.snd( get_edge_and_costs_forward nb f u v) \<noteq>MInfty"
  unfolding get_edge_and_costs_forward_def
  using not_both_realising_edges_none[of u v] 
        imageI[OF conjunct1[OF 
             find_cheapest_forward_props[OF prod.collapse refl, 
                          of f nb _ "create_edge u v" PInfty]],
            of prod.snd , simplified image_def, simplified]
        imageI[OF conjunct1[OF 
              find_cheapest_backward_props[OF prod.collapse refl, 
                          of f nb _ "create_edge v u" PInfty]],
                 of prod.snd, simplified image_def, simplified]
  by(auto split: if_split prod.split option.split)
    (metis MInfty_neq_PInfty(1) MInfty_neq_ereal(1) snd_conv)+

lemma get_edge_and_costs_backward_not_MInfty:
  "prod.snd( get_edge_and_costs_backward nb f u v) \<noteq>MInfty"
  unfolding get_edge_and_costs_backward_def
  using not_both_realising_edges_none[of v u] 
  using imageI[OF conjunct1[OF 
             find_cheapest_forward_props[OF prod.collapse refl, 
                          of f nb _ "create_edge v u" PInfty]],
            of prod.snd, simplified image_def, simplified]
  using imageI[OF conjunct1[OF 
              find_cheapest_backward_props[OF prod.collapse refl, 
                          of f nb _ "create_edge u v" PInfty]],
                 of prod.snd, simplified image_def, simplified]
  by(auto split: if_split prod.split option.split)
    (metis MInfty_neq_PInfty(1) MInfty_neq_ereal(1) snd_conv)+

lemma realising_edges_general_result_None_and_Some:
  assumes "(case realising_edges_lookup (realising_edges_general list) (u, v) 
            of Some ds \<Rightarrow> ds 
               | None \<Rightarrow> [])= ds"
  shows "set ds = {e | e. e \<in> set list \<and> make_pair e = (u, v)}"
  using assms
  apply(induction list arbitrary: ds)
  apply(simp add: realising_edges_lookup_def realising_edges_general_def 
                   realising_edges_empty_def Map_realising.map_empty)
  subgoal for a list ds
    unfolding realising_edges_general_def
    apply(subst (asm) foldr.foldr_Cons, subst (asm) o_apply)
    unfolding realising_edges_general_def[symmetric]
    unfolding Let_def  realising_edges_lookup_def realising_edges_update_def
    apply(subst (asm) (9) option.split, subst (asm) Map_realising.map_update)
    using  realising_edges_general_invar 
    apply(force simp add: realising_edges_invar_def)
    apply(subst (asm) Map_realising.map_update)
    using realising_edges_general_invar 
    apply(force simp add: realising_edges_invar_def)
  by(cases "make_pair a = (u, v)") 
    (auto intro: option.exhaust[of "realising_edges_lookup (realising_edges_general list) (fst a, snd a)"]
             simp add: make_pair_fst_snd)
  done

lemma realising_edges_general_result:
  assumes "realising_edges_lookup (realising_edges_general list) (u, v) = Some ds"
  shows "set ds = {e | e. e \<in> set list \<and> make_pair e = (u, v)}"
  using realising_edges_general_result_None_and_Some[of list u v ds] assms
  by simp

lemma realising_edges_result:
    "realising_edges_lookup realising_edges (u, v) = Some ds \<Longrightarrow>
    set ds = {e |e. e \<in> set \<E>_list \<and> make_pair e = (u, v)}"
  by (simp add: realising_edges_def realising_edges_general_result)

lemma  get_edge_and_costs_forward_result_props:
  assumes "get_edge_and_costs_forward nb f u v = (e, c)" "c \<noteq>PInfty" "oedge e = d"
    shows "nb d\<and> rcap f e > 0 \<and> fstv e = u \<and> sndv e = v \<and>
                  d \<in> \<E> \<and> c = \<cc> e"
proof-
  define ingoing_edges where "ingoing_edges =
            (case realising_edges_lookup realising_edges
                  (u, v) of
            None \<Rightarrow> [] | Some list \<Rightarrow> list)"
  define outgoing_edges where "outgoing_edges =
            (case realising_edges_lookup realising_edges
                  (v, u) of
            None \<Rightarrow> [] | Some list \<Rightarrow> list)"
  define ef where "ef = prod.fst (find_cheapest_forward f nb ingoing_edges
             (create_edge u v) PInfty)"
  define cf where "cf = prod.snd (find_cheapest_forward f nb ingoing_edges
             (create_edge u v) PInfty)"
  define eb where "eb = prod.fst (find_cheapest_backward f nb outgoing_edges
             (create_edge v u) PInfty)"
  define cb where "cb = prod.snd (find_cheapest_backward f nb outgoing_edges
             (create_edge v u) PInfty)"
  have result_simp:"(e, c) = (if cf \<le> cb then (F ef, cf) else (B eb, cb))"
    by(auto split: option.split prod.split 
        simp add: get_edge_and_costs_forward_def sym[OF assms(1)] cf_def cb_def ingoing_edges_def outgoing_edges_def ef_def eb_def )
  show ?thesis
  proof(cases "cf \<le> cb")
    case True
    hence result_is:"F ef = e" "cf = c" "ef = d"
      using result_simp  assms(3) by auto
    define edges_and_costs where "edges_and_costs =
  Set.insert (create_edge u v, PInfty)
   {(e, ereal (\<c> e)) |e. e \<in> set ingoing_edges \<and> nb e \<and> ereal (f e) < \<u> e}"
    have ef_cf_prop:"(ef, cf) \<in> edges_and_costs"
      using find_cheapest_forward_props[of ef cf f nb ingoing_edges 
                            "create_edge u v" PInfty edges_and_costs] 
      by (auto simp add: cf_def edges_and_costs_def ef_def)
    hence ef_in_a_Set:"(ef, cf) \<in> 
 {(e, ereal (\<c> e)) |e. e \<in> set ingoing_edges \<and> nb e \<and> ereal (f e) < \<u> e}"
      using result_is(2) assms(2)
      by(auto simp add: edges_and_costs_def)
    hence ef_props: "ef \<in> set ingoing_edges" "nb ef" "ereal (f ef) < \<u> ef" by auto
    have realising_not_none: "realising_edges_lookup realising_edges (u, v) \<noteq> None"
      using  ef_props  
      by(auto split: option.split simp add: ingoing_edges_def) metis
    then obtain list where list_prop: "realising_edges_lookup realising_edges (u, v) = Some list"
      by auto
    have "set ingoing_edges = {e |e. e \<in> set \<E>_list \<and> make_pair e = (u, v)}"
      using realising_edges_result[OF list_prop] list_prop
      by(auto simp add: ingoing_edges_def)
    hence ef_inE:"ef \<in> \<E>" "make_pair ef = (u, v)" 
      using ef_props(1) 
      by(simp add: \<E>_def \<E>_impl_basic(1) \<E>_list_def to_list(1))+
    show ?thesis
      using  ef_inE(1) ef_inE(2)[simplified make_pair_fst_snd] ef_in_a_Set 
      by(auto simp add: ef_props  ereal_diff_gr0 result_is[symmetric])
  next
    case False
    hence result_is:"B eb = e" "cb = c" "eb = d"
      using result_simp  assms(3) by auto
    define edges_and_costs where "edges_and_costs =
  Set.insert (create_edge v u, PInfty)
   {(e, ereal (- \<c> e)) |e. e \<in> set outgoing_edges \<and> nb e \<and> ereal (f e) > 0}"
    have ef_cf_prop:"(eb, cb) \<in> edges_and_costs" 
      using find_cheapest_backward_props[of eb cb f nb outgoing_edges 
                            "create_edge v u" PInfty edges_and_costs] 
      by (auto simp add: cb_def edges_and_costs_def eb_def)
    hence ef_in_a_Set:"(eb, cb) \<in> 
 {(e, ereal (- \<c> e)) |e. e \<in> set outgoing_edges \<and> nb e \<and> ereal (f e) > 0}"
      using result_is(2) assms(2)
      by(auto simp add: edges_and_costs_def)
    hence ef_props: "eb \<in> set outgoing_edges" "nb eb" "ereal (f eb) > 0" by auto
    have realising_not_none: "realising_edges_lookup realising_edges (v, u) \<noteq> None"
      using  ef_props  
      by(auto split: option.split simp add: outgoing_edges_def) metis
    then obtain list where list_prop: "realising_edges_lookup realising_edges (v, u) = Some list"
      by auto
    have "set outgoing_edges = {e |e. e \<in> set \<E>_list \<and> make_pair e = (v, u)}"
      using realising_edges_result[OF list_prop] list_prop
      by(auto simp add: outgoing_edges_def)
    hence ef_inE:"eb \<in> \<E>" "make_pair eb = (v, u)" 
      using ef_props(1) 
      by(simp add: \<E>_def \<E>_impl_basic(1) \<E>_list_def to_list(1))+
    show ?thesis
      using  ef_inE(1) ef_inE(2)[simplified make_pair_fst_snd] ef_in_a_Set 
      by(auto simp add: ef_props  ereal_diff_gr0 result_is[symmetric])
  qed
qed

lemma  get_edge_and_costs_backward_result_props:
  assumes "get_edge_and_costs_backward nb f v u = (e, c)"  "c \<noteq>PInfty" "oedge e = d"
    shows "nb d \<and> cost_flow_network.rcap f e > 0 \<and> fstv e = u \<and> sndv e = v \<and> d \<in> \<E> \<and> c = \<cc> e"
proof-
  define ingoing_edges where "ingoing_edges =
            (case realising_edges_lookup realising_edges
                  (u, v) of
            None \<Rightarrow> [] | Some list \<Rightarrow> list)"
  define outgoing_edges where "outgoing_edges =
            (case realising_edges_lookup realising_edges
                  (v, u) of
            None \<Rightarrow> [] | Some list \<Rightarrow> list)"
  define ef where "ef = prod.fst (find_cheapest_forward f nb ingoing_edges
             (create_edge u v) PInfty)"
  define cf where "cf = prod.snd (find_cheapest_forward f nb ingoing_edges
             (create_edge u v) PInfty)"
  define eb where "eb = prod.fst (find_cheapest_backward f nb outgoing_edges
             (create_edge v u) PInfty)"
  define cb where "cb = prod.snd (find_cheapest_backward f nb outgoing_edges
             (create_edge v u) PInfty)"
  have result_simp:"(e, c) = (if cf \<le> cb then (F ef, cf) else (B eb, cb))"
    by(auto split: option.split prod.split 
        simp add: get_edge_and_costs_backward_def sym[OF assms(1)] cf_def cb_def ingoing_edges_def outgoing_edges_def ef_def eb_def )
  show ?thesis
  proof(cases "cf \<le> cb")
    case True
    hence result_is:"F ef = e" "cf = c" "ef = d"
      using result_simp  assms(3) by auto
    define edges_and_costs where "edges_and_costs =
        Set.insert (create_edge u v, PInfty)
            {(e, ereal (\<c> e)) |e. e \<in> set ingoing_edges \<and> nb e \<and> ereal (f e) < \<u> e}"
    have ef_cf_prop:"(ef, cf) \<in> edges_and_costs"
      using find_cheapest_forward_props[of ef cf f nb ingoing_edges 
                            "create_edge u v" PInfty edges_and_costs] 
      by (auto simp add: cf_def edges_and_costs_def ef_def)
    hence ef_in_a_Set:"(ef, cf) \<in> 
         {(e, ereal (\<c> e)) |e. e \<in> set ingoing_edges \<and> nb e \<and> ereal (f e) < \<u> e}"
      using result_is(2) assms(2)
      by(auto simp add: edges_and_costs_def)
    hence ef_props: "ef \<in> set ingoing_edges" "nb ef" "ereal (f ef) < \<u> ef" by auto
    have realising_not_none: "realising_edges_lookup realising_edges (u, v) \<noteq> None"
      using  ef_props  
      by(auto split: option.split simp add: ingoing_edges_def) metis
    then obtain list where list_prop: "realising_edges_lookup realising_edges (u, v) = Some list"
      by auto
    have "set ingoing_edges = {e |e. e \<in> set \<E>_list \<and> make_pair e = (u, v)}"
      using realising_edges_result[OF list_prop] list_prop
      by(auto simp add: ingoing_edges_def)
    hence ef_inE:"ef \<in> \<E>" "make_pair ef = (u, v)" 
      using ef_props(1) 
      by(simp add: \<E>_def \<E>_impl_basic(1) \<E>_list_def to_list(1))+
    show ?thesis
      using  ef_inE(1) ef_inE(2)[simplified make_pair_fst_snd] ef_in_a_Set 
      by(auto simp add: ef_props  ereal_diff_gr0 result_is[symmetric])
  next
    case False
    hence result_is:"B eb = e" "cb = c" "eb = d"
      using result_simp  assms(3) by auto
    define edges_and_costs where "edges_and_costs =
        Set.insert (create_edge v u, PInfty)
         {(e, ereal (- \<c> e)) |e. e \<in> set outgoing_edges \<and> nb e \<and> ereal (f e) > 0}"
    have ef_cf_prop:"(eb, cb) \<in> edges_and_costs" 
      using find_cheapest_backward_props[of eb cb f nb outgoing_edges 
                            "create_edge v u" PInfty edges_and_costs] 
      by (auto simp add: cb_def edges_and_costs_def eb_def)
    hence ef_in_a_Set:"(eb, cb) \<in> 
          {(e, ereal (- \<c> e)) |e. e \<in> set outgoing_edges \<and> nb e \<and> ereal (f e) > 0}"
      using result_is(2) assms(2)
      by(auto simp add: edges_and_costs_def)
    hence ef_props: "eb \<in> set outgoing_edges" "nb eb" "ereal (f eb) > 0" by auto
    have realising_not_none: "realising_edges_lookup realising_edges (v, u) \<noteq> None"
      using  ef_props  
      by(auto split: option.split simp add: outgoing_edges_def) metis
    then obtain list where list_prop: "realising_edges_lookup realising_edges (v, u) = Some list"
      by auto
    have "set outgoing_edges = {e |e. e \<in> set \<E>_list \<and> make_pair e = (v, u)}"
      using realising_edges_result[OF list_prop] list_prop
      by(auto simp add: outgoing_edges_def)
    hence ef_inE:"eb \<in> \<E>" "make_pair eb = (v, u)" 
      using ef_props(1) 
      by(simp add: \<E>_def \<E>_impl_basic(1) \<E>_list_def to_list(1))+
    show ?thesis
      using  ef_inE(1) ef_inE(2)[simplified make_pair_fst_snd] ef_in_a_Set 
      by(auto simp add: ef_props  ereal_diff_gr0 result_is[symmetric])
  qed
qed

lemmas EEE_def = flow_network_spec.\<EE>_def

lemma es_E_frac: "cost_flow_network.to_vertex_pair ` EEE = set es"
proof(goal_cases)
  case 1
  have help1: "\<lbrakk> (a, b) = prod.swap (make_pair d); prod.swap (make_pair d) \<notin> make_pair ` \<E>; d \<in> \<E>\<rbrakk> 
               \<Longrightarrow> (b, a) \<in> make_pair ` local.\<E>" for a b d
  using cost_flow_network.to_vertex_pair.simps 
  by (metis imageI swap_simp swap_swap)
  have help2: "\<lbrakk>(a, b) = make_pair x ; x \<in> local.\<E> \<rbrakk>\<Longrightarrow>
       make_pair x \<in> to_edge `
          ({F d |d. d \<in> local.\<E>} \<union> {B d |d. d \<in> local.\<E>})"
    for a b x
    using cost_flow_network.to_vertex_pair.simps make_pairs_are
    by(metis (mono_tags, lifting) UnI1 imageI mem_Collect_eq)
  have help3: "\<lbrakk> (b, a) = make_pair x ; x \<in> local.\<E>\<rbrakk> \<Longrightarrow>
       (a, b) \<in> to_edge `
          ({F d |d. d \<in> local.\<E>} \<union> {B d |d. d \<in> local.\<E>})"
    for a b x
    by (smt (verit, del_insts) cost_flow_network.\<EE>_def cost_flow_network.o_edge_res make_pairs_are
    flow_network_spec.oedge.simps(2) cost_flow_network.to_vertex_pair.simps(2) image_iff swap_simp)
    show ?case
     by(auto simp add: cost_flow_network.to_vertex_pair.simps es_is_E EEE_def
          cost_flow_network.\<EE>_def make_pairs_are Instantiation.make_pair_def
          intro: help1 help2 help3) 
qed

lemma to_edge_get_edge_and_costs_forward:
      "to_edge (prod.fst ((get_edge_and_costs_forward nb f u v))) = (u, v)"
  unfolding get_edge_and_costs_forward_def Let_def
proof(goal_cases)
  case 1   
  have help4: "\<lbrakk>realising_edges_lookup local.realising_edges (u, v) = None ;
       realising_edges_lookup local.realising_edges (v, u) = Some x2 ; \<not> x2a \<le> x2b ;
       local.find_cheapest_backward f nb x2 (create_edge v u) \<infinity> = (x1a, x2b) ;
       local.find_cheapest_forward f nb [] (create_edge u v) \<infinity> = (x1, x2a)\<rbrakk> \<Longrightarrow>
       prod.swap (make_pair x1a) = (u, v)"
    for x2 x1 x2a x1a x2b
    using realising_edges_dom[of v u] realising_edges_result[of v u x2]
           find_cheapest_backward_props[of x1a x2b f nb x2 "create_edge v u" PInfty, OF _ refl]
    by (fastforce simp add:) 
  have help5: "\<lbrakk>realising_edges_lookup local.realising_edges (u, v) = Some x2 ;
       realising_edges_lookup local.realising_edges (v, u) = None ;x2a \<le> x2b ;
       local.find_cheapest_backward f nb [] (create_edge v u) \<infinity> = (x1a, x2b) ;
       local.find_cheapest_forward f nb x2 (create_edge u v) \<infinity> = (x1, x2a) \<rbrakk>\<Longrightarrow>
       make_pair x1 = (u, v)"
    for x2 x1 x2a x1a x2b
    using realising_edges_dom[of u v]  realising_edges_result[of u v x2]
          find_cheapest_forward_props[of x1 x2a f nb x2 "create_edge u v" PInfty, OF _ refl]
    by (auto simp add: create_edge )
  have help6: "\<lbrakk>realising_edges_lookup local.realising_edges (u, v) = Some x2 ;
    realising_edges_lookup local.realising_edges (v, u) = Some x2a ; x2b \<le> x2c ;
    local.find_cheapest_backward f nb x2a (create_edge v u) \<infinity> = (x1a, x2c) ;
    local.find_cheapest_forward f nb x2 (create_edge u v) \<infinity> = (x1, x2b) \<rbrakk>\<Longrightarrow>
    make_pair x1 = (u, v)"
    for x2 x2a x1 x2b x1a x2c
    using realising_edges_result[of u v x2] realising_edges_result[of v u x2a]
          find_cheapest_forward_props[of x1 x2b f nb x2 "create_edge u v" PInfty, OF _ refl]
           find_cheapest_backward_props[of x1a  x2c f nb x2a "create_edge v u" PInfty, OF _ refl]
    by(auto simp add: create_edge)
  have help7: "\<lbrakk> realising_edges_lookup local.realising_edges (u, v) = Some x2 ;
    realising_edges_lookup local.realising_edges (v, u) = Some x2a ;\<not> x2b \<le> x2c ;
    local.find_cheapest_backward f nb x2a (create_edge v u) \<infinity> = (x1a, x2c) ;
    local.find_cheapest_forward f nb x2 (create_edge u v) \<infinity> = (x1, x2b) \<rbrakk> \<Longrightarrow>
    prod.swap (make_pair x1a) = (u, v)"
   for x2 x2a x1 x2b x1a x2c
    using realising_edges_result[of u v x2] realising_edges_result[of v u x2a]
          find_cheapest_forward_props[of x1 x2b f nb x2 "create_edge u v" PInfty, OF _ refl]
          find_cheapest_backward_props[of x1a  x2c f nb x2a "create_edge v u" PInfty, OF _ refl]
    by(auto simp add: create_edge)
  show ?case
    by(auto split: if_split prod.split option.split 
            simp add: create_edge make_pairs_are find_cheapest_backward_def find_cheapest_forward_def
                      Instantiation.make_pair_def
                 intro: help4 help5 help6 help7)
qed

lemma to_edge_get_edge_and_costs_backward:
      "to_edge (prod.fst ((get_edge_and_costs_backward nb f v u))) = (u, v)"
  unfolding get_edge_and_costs_backward_def Let_def
proof(goal_cases)
  case 1
  have help1: "\<lbrakk> realising_edges_lookup local.realising_edges (u, v) = None ;
    realising_edges_lookup local.realising_edges (v, u) = Some x2 ;\<not> x2a \<le> x2b ;
    local.find_cheapest_backward f nb x2 (create_edge v u) \<infinity> = (x1a, x2b) ;
    local.find_cheapest_forward f nb [] (create_edge u v) \<infinity> = (x1, x2a)\<rbrakk> \<Longrightarrow>
    prod.swap (make_pair x1a) = (u, v)"
    for x2 x1 x2a x1a x2b
    using realising_edges_dom[of v u]  realising_edges_result[of v u x2]
          find_cheapest_backward_props[of x1a x2b f nb x2 "create_edge v u" PInfty, OF _ refl]
    by (fastforce simp add:)
  have help2: "\<lbrakk> realising_edges_lookup local.realising_edges (u, v) = Some x2 ;
    realising_edges_lookup local.realising_edges (v, u) = None ; x2a \<le> x2b ;
    local.find_cheapest_backward f nb [] (create_edge v u) \<infinity> = (x1a, x2b) ;
    local.find_cheapest_forward f nb x2 (create_edge u v) \<infinity> = (x1, x2a)\<rbrakk> \<Longrightarrow>
    make_pair x1 = (u, v)"
    for x2 x1 x2a x1a x2b
    using realising_edges_dom[of u v]
    using realising_edges_result[of u v x2]
    using find_cheapest_forward_props[of x1 x2a f nb x2 "create_edge u v" PInfty, OF _ refl]
    by (auto simp add: create_edge )
  have help3: "\<lbrakk> realising_edges_lookup local.realising_edges (u, v) = Some x2 ;
    realising_edges_lookup local.realising_edges (v, u) = Some x2a ; x2b \<le> x2c ;
    local.find_cheapest_backward f nb x2a (create_edge v u) \<infinity> = (x1a, x2c) ;
    local.find_cheapest_forward f nb x2 (create_edge u v) \<infinity> = (x1, x2b) \<rbrakk> \<Longrightarrow>
    make_pair x1 = (u, v)"
    for x2 x2a x1 x2b x1a x2c
    using realising_edges_result[of u v x2] realising_edges_result[of v u x2a]
    using find_cheapest_forward_props[of x1 x2b f nb x2 "create_edge u v" PInfty, OF _ refl]
    using find_cheapest_backward_props[of x1a  x2c f nb x2a "create_edge v u" PInfty, OF _ refl]
    by(auto simp add: create_edge)
  have help4: "\<lbrakk> realising_edges_lookup local.realising_edges (u, v) = Some x2 ;
    realising_edges_lookup local.realising_edges (v, u) = Some x2a ; \<not> x2b \<le> x2c ;
    local.find_cheapest_backward f nb x2a (create_edge v u) \<infinity> = (x1a, x2c) ;
    local.find_cheapest_forward f nb x2 (create_edge u v) \<infinity> = (x1, x2b) \<rbrakk> \<Longrightarrow>
    prod.swap (make_pair x1a) = (u, v)"
    for x2 x2a x1 x2b x1a x2c
    using realising_edges_result[of u v x2] realising_edges_result[of v u x2a]
    using find_cheapest_forward_props[of x1 x2b f nb x2 "create_edge u v" PInfty, OF _ refl]
    using find_cheapest_backward_props[of x1a  x2c f nb x2a "create_edge v u" PInfty, OF _ refl]
    by(auto simp add: multigraph.create_edge)
  show ?case
    by(auto split: if_split prod.split option.split 
            simp add: create_edge make_pairs_are find_cheapest_forward_def
                      find_cheapest_backward_def Instantiation.make_pair_def
             intro: help1 help2 help3 help4)
qed

lemma costs_forward_less_PInfty_in_es: 
  "prod.snd (get_edge_and_costs_forward nb f u v) < PInfty \<Longrightarrow> (u, v) \<in> set es"
  using get_edge_and_costs_forward_result_props[OF prod.collapse[symmetric] _ refl, of nb f u v,
          simplified cost_flow_network.o_edge_res]
        es_E_frac to_edge_get_edge_and_costs_forward[of nb f u v] 
  by force

lemma costs_backward_less_PInfty_in_es: 
  "prod.snd (get_edge_and_costs_backward nb f u v) < PInfty \<Longrightarrow> (v, u) \<in> set es"
  using get_edge_and_costs_backward_result_props[OF prod.collapse[symmetric] _ refl, of nb f u v,
          simplified cost_flow_network.o_edge_res]
        es_E_frac to_edge_get_edge_and_costs_backward[of nb f u v] 
  by force

lemma bellman_ford:
  shows "bellman_ford  connection_empty connection_lookup connection_invar connection_delete
           es vs (\<lambda> u v. prod.snd (get_edge_and_costs_forward nb f u v)) connection_update"
proof-
  have MInfty:"MInfty < prod.snd (get_edge_and_costs_forward nb f u v)" for u v
    using get_edge_and_costs_forward_not_MInfty by auto
  show ?thesis
    using Map_connection MInfty  vs_and_es  costs_forward_less_PInfty_in_es
   by (auto simp add: bellman_ford_def bellman_ford_spec_def bellman_ford_axioms_def)
qed  

interpretation bf_fw: bellman_ford
  where connection_update=connection_update
     and connection_empty=connection_empty 
     and connection_lookup=connection_lookup
     and connection_delete=connection_delete 
     and connection_invar=connection_invar 
     and es= es 
     and vs=vs 
     and edge_costs="(\<lambda> u v. prod.snd (get_edge_and_costs_forward nb f u v))" 
   for nb f
  using bellman_ford by auto

lemma es_sym: "prod.swap e \<in> set es \<Longrightarrow> e \<in> set es"
  unfolding es_def to_list_def \<E>_def 
  by (cases e) (auto simp add:  make_pair_fst_snd)

lemma bellman_ford_backward: 
  shows "bellman_ford connection_empty connection_lookup connection_invar connection_delete
         es vs (\<lambda> u v. prod.snd (get_edge_and_costs_backward nb f u v)) connection_update"
proof-
  have MInfty:"MInfty < prod.snd (get_edge_and_costs_backward nb f u v)" for u v
    using get_edge_and_costs_backward_not_MInfty by auto
  show ?thesis
    using Map_connection MInfty  vs_and_es costs_backward_less_PInfty_in_es
    by (auto simp add: bellman_ford_def  es_sym bellman_ford_spec_def bellman_ford_axioms_def intro:  es_sym)
qed 

interpretation bf_bw: bellman_ford 
  where connection_update=connection_update
     and connection_empty=connection_empty 
     and connection_lookup=connection_lookup
     and connection_delete=connection_delete 
     and connection_invar=connection_invar 
     and es= es 
     and vs=vs 
     and edge_costs="  (\<lambda> u v. prod.snd (get_edge_and_costs_backward nb f u v))" 
     for nb f
  using bellman_ford_backward by auto
 
lemma get_source_aux:
 "(\<exists> x \<in> set xs. b x > (1 - \<epsilon>) * \<gamma> ) \<Longrightarrow> (get_source_aux b \<gamma> xs) \<noteq> None"
 "Some res = (get_source_aux b \<gamma> xs) \<Longrightarrow> b res > (1 - \<epsilon>) * \<gamma> \<and> res \<in> set xs "
 "\<not> (\<exists> x \<in> set xs. b x > (1 - \<epsilon>) * \<gamma> ) \<Longrightarrow> (get_source_aux b \<gamma> xs) = None"
  unfolding get_source_aux_def
  by(induction b \<gamma> xs rule: get_source_aux_aux.induct) force+

lemma get_target_aux:
 "(\<exists> x \<in> set xs. b x < - (1 - \<epsilon>) * \<gamma> ) \<Longrightarrow> (get_target_aux b \<gamma> xs)\<noteq> None"
 "Some res = (get_target_aux b \<gamma> xs) \<Longrightarrow> b res < - (1 - \<epsilon>) * \<gamma> \<and> res \<in> set xs "
 "\<not> (\<exists> x \<in> set xs. b x < - (1 - \<epsilon>) * \<gamma> ) \<Longrightarrow> (get_target_aux b \<gamma> xs) = None"
  unfolding get_target_aux_def
  by(induction b \<gamma> xs rule: get_target_aux_aux.induct) force+

abbreviation "underlying_invars (state)\<equiv> algo.underlying_invars  state"
abbreviation "invar_isOptflow (state)\<equiv> algo.invar_isOptflow state"
abbreviation "\<F> state \<equiv> algo.\<F>  (state)"
abbreviation "resreach \<equiv> cost_flow_network.resreach"
abbreviation "augpath \<equiv> cost_flow_network.augpath"
abbreviation "invar_gamma (state)== algo.invar_gamma state"
abbreviation "augcycle == cost_flow_network.augcycle"
abbreviation "prepath == cost_flow_network.prepath"

lemmas \<F>_def = algo.\<F>_def
lemmas \<F>_redges_def =  algo.\<F>_redges_def

lemmas prepath_def = cost_flow_network.prepath_def
lemmas augpath_def = cost_flow_network.augpath_def

lemma realising_edges_invar: "realising_edges_invar realising_edges" 
  by (simp add: realising_edges_def realising_edges_general_invar)

lemma both_realising_edges_none_iff_not_in_es:
"(u, v) \<in> set es \<longleftrightarrow> ( realising_edges_lookup realising_edges (u, v) \<noteq> None \<or>
                      realising_edges_lookup realising_edges (v, u) \<noteq> None)"
  using realising_edges_dom make_pair_fst_snd
  by(auto simp add:  es_def \<E>_list_def) blast

lemma get_edge_and_costs_forward_makes_cheaper:
  assumes "oedge e = d" "d \<in> \<E>" "nb d" "cost_flow_network.rcap f e > 0"
          "(C , c) = get_edge_and_costs_forward nb f (fstv e) (sndv e)"
    shows "c \<le> \<cc> e \<and> c \<noteq> MInfty"
  unfolding snd_conv[of C c, symmetric, simplified assms(5)]
  unfolding get_edge_and_costs_forward_def 
proof(cases "(fstv e, sndv e) \<notin> set es", goal_cases)
  case 1
  then show ?case 
    using cost_flow_network.o_edge_res cost_flow_network.to_vertex_pair_fst_snd assms(1) assms(2) es_E_frac 
    by(auto split: prod.split option.split simp add: find_cheapest_backward_def find_cheapest_forward_def)
next
  case 2
  note ines = this[simplified]
  define ingoing_edges where "ingoing_edges =
            (case realising_edges_lookup realising_edges
                  (fstv e, sndv e) of
            None \<Rightarrow> [] | Some list \<Rightarrow> list)"
  define outgoing_edges where "outgoing_edges =
            (case realising_edges_lookup realising_edges
                  (sndv e, fstv e) of
            None \<Rightarrow> [] | Some list \<Rightarrow> list)"
  define ef where "ef = prod.fst (find_cheapest_forward f nb ingoing_edges
             (create_edge (fstv e) (sndv e)) PInfty)"
  define cf where "cf = prod.snd (find_cheapest_forward f nb ingoing_edges
             (create_edge (fstv e) (sndv e)) PInfty)"
  define eb where "eb = prod.fst (find_cheapest_backward f nb outgoing_edges
             (create_edge (sndv e) (fstv e)) PInfty)"
  define cb where "cb = prod.snd (find_cheapest_backward f nb outgoing_edges
             (create_edge (sndv e) (fstv e)) PInfty)"
  have goalI: "prod.snd (if cf \<le> cb then (F ef, cf) else (B eb, cb))
                   \<le> ereal (\<cc> e) \<and>
                prod.snd (if cf \<le> cb then (F ef, cf) else (B eb, cb)) \<noteq> MInfty \<Longrightarrow> ?case"
    by(auto split: prod.split simp add: cf_def cb_def ef_def eb_def
                            ingoing_edges_def outgoing_edges_def)
  show ?case
  proof(cases e, all \<open>rule goalI\<close>, all \<open>simp only: cost_flow_network.\<cc>.simps\<close>, goal_cases)
    case (1 ee)
    define edges_and_costs where "edges_and_costs =
     Set.insert (create_edge (fst ee) (snd ee), PInfty)
       {(e, ereal (\<c> e)) |e. e \<in> set ingoing_edges \<and> nb e \<and> ereal (f e) < \<u> e}"
    have ef_cf_prop:"(ef, cf) \<in> edges_and_costs" "\<And> ee cc. (ee, cc)\<in>edges_and_costs \<Longrightarrow> cf \<le> cc"
      using find_cheapest_forward_props[of ef cf f nb ingoing_edges 
                            "create_edge (fst ee) (snd ee)" PInfty edges_and_costs]     
      by (auto simp add: "1" cf_def edges_and_costs_def ef_def)
    obtain list where listexists:"realising_edges_lookup realising_edges
                     (fstv e, sndv e) = Some list"
      using realising_edges_dom[of "fstv e" "sndv e"] assms(1,2) 1
      by (auto simp add:  es_def  \<E>_list_def make_pair_fst_snd  \<E>_def \<E>_impl(1) to_list(1))
    have ee_in_ingoing:"ee \<in> set ingoing_edges"
      unfolding ingoing_edges_def
      using realising_edges_dom[of "fstv e" "sndv e", simplified listexists, simplified]
               realising_edges_result[OF listexists] 
          "1" cost_flow_network.to_vertex_pair.simps cost_flow_network.to_vertex_pair_fst_snd \<E>_def 
          \<E>_impl(1) \<E>_list_def assms(1) assms(2) to_list(1) listexists
      by (fastforce simp add: ingoing_edges_def make_pairs_are)
    have "cf \<le> \<c> ee"
      using 1 assms(1-4) ee_in_ingoing 
      by (auto intro: ef_cf_prop(2)[of ee] simp add: algo.infinite_u edges_and_costs_def)
    moreover have "cf \<noteq>MInfty" 
      using ef_cf_prop(1) by(auto simp add: edges_and_costs_def) 
    ultimately show ?case
      using find_cheapest_backward_props[OF prod.collapse refl, of f nb outgoing_edges
                  "create_edge (sndv e) (fstv e)" PInfty]
      by auto (auto simp add: cb_def)
  next
    case (2 ee)
    define edges_and_costs where "edges_and_costs =
     Set.insert (create_edge (fst ee) (snd ee), PInfty)
      {(e, ereal (- \<c> e)) |e. e \<in> set outgoing_edges \<and> nb e \<and> 0 < ereal (f e)}"
    have ef_cf_prop:"(eb, cb) \<in> edges_and_costs" "\<And> ee cc. (ee, cc)\<in>edges_and_costs \<Longrightarrow> cb \<le> cc"
      using find_cheapest_backward_props[of eb cb f nb outgoing_edges 
                            "create_edge (fst ee) (snd ee)" PInfty edges_and_costs]     
      by(auto simp add: "2" cb_def edges_and_costs_def eb_def)
      
    obtain list where listexists:"realising_edges_lookup realising_edges
                     (sndv e, fstv e) = Some list"
      using realising_edges_dom[of "sndv e" "fstv e"] assms(1,2) 2
      by (auto simp add:  es_def  \<E>_list_def make_pair_fst_snd  \<E>_def \<E>_impl(1) to_list(1))
    have ee_in_ingoing:"ee \<in> set outgoing_edges"
      unfolding ingoing_edges_def
      using realising_edges_dom[of "sndv e" "fstv e", simplified listexists, simplified]
               realising_edges_result[OF listexists] 
          2 cost_flow_network.to_vertex_pair.simps cost_flow_network.to_vertex_pair_fst_snd \<E>_def 
          \<E>_impl(1) \<E>_list_def assms(1) assms(2) to_list(1) listexists
      by (fastforce simp add: outgoing_edges_def make_pairs_are)
    have "cb \<le> - \<c> ee"
      using 2 assms(1-4) ee_in_ingoing 
      by (auto intro: ef_cf_prop(2)[of ee] simp add: algo.infinite_u edges_and_costs_def)
   moreover have "cb \<noteq>MInfty" 
      using ef_cf_prop(1) by(auto simp add: edges_and_costs_def)
    ultimately show ?case
      using find_cheapest_forward_props[OF prod.collapse refl, of f nb ingoing_edges
                  "create_edge (fstv e) (sndv e)" PInfty]
      by auto (auto simp add: cf_def) 
  qed
qed

lemma get_edge_and_costs_backward_makes_cheaper:
  assumes "oedge e = d" "d \<in> \<E>" "nb d" "cost_flow_network.rcap f e > 0"
          "(C , c) = get_edge_and_costs_backward nb f (sndv e) (fstv e)"
    shows "c \<le> \<cc> e \<and> c \<noteq> MInfty"
  unfolding snd_conv[of C c, symmetric, simplified assms(5)]
  unfolding get_edge_and_costs_backward_def
proof(cases "(fstv e, sndv e) \<notin> set es", goal_cases)
  case 1
  then show ?case 
    using cost_flow_network.o_edge_res cost_flow_network.vs_to_vertex_pair_pres(1) 
          cost_flow_network.vs_to_vertex_pair_pres(2) assms(1) assms(2) es_E_frac by auto
next
  case 2
  note ines = this[simplified]
  define ingoing_edges where "ingoing_edges =
            (case realising_edges_lookup realising_edges
                  (fstv e, sndv e) of
            None \<Rightarrow> [] | Some list \<Rightarrow> list)"
  define outgoing_edges where "outgoing_edges =
            (case realising_edges_lookup realising_edges
                  (sndv e, fstv e) of
            None \<Rightarrow> [] | Some list \<Rightarrow> list)"
  define ef where "ef = prod.fst (find_cheapest_forward f nb ingoing_edges
             (create_edge (fstv e) (sndv e)) PInfty)"
  define cf where "cf = prod.snd (find_cheapest_forward f nb ingoing_edges
             (create_edge (fstv e) (sndv e)) PInfty)"
  define eb where "eb = prod.fst (find_cheapest_backward f nb outgoing_edges
             (create_edge (sndv e) (fstv e)) PInfty)"
  define cb where "cb = prod.snd (find_cheapest_backward f nb outgoing_edges
             (create_edge (sndv e) (fstv e)) PInfty)"
  have goalI: "prod.snd (if cf \<le> cb then (F ef, cf) else (B eb, cb))
                   \<le> ereal (\<cc> e) \<and> prod.snd (if cf \<le> cb then (F ef, cf) else (B eb, cb)) \<noteq> MInfty \<Longrightarrow> ?case"
    by(auto split: prod.split simp add: cf_def cb_def ef_def eb_def
                            ingoing_edges_def outgoing_edges_def)
  show ?case
  proof(cases e, all \<open>rule goalI\<close>, all \<open>simp only: cost_flow_network.\<cc>.simps\<close>, goal_cases)
    case (1 ee)
    define edges_and_costs where "edges_and_costs =
     Set.insert (create_edge (fst ee) (snd ee), PInfty)
       {(e, ereal (\<c> e)) |e. e \<in> set ingoing_edges \<and> nb e \<and> ereal (f e) < \<u> e}"
    have ef_cf_prop:"(ef, cf) \<in> edges_and_costs" "\<And> ee cc. (ee, cc)\<in>edges_and_costs \<Longrightarrow> cf \<le> cc"
      using find_cheapest_forward_props[of ef cf f nb ingoing_edges 
                            "create_edge (fst ee) (snd ee)" PInfty edges_and_costs]     
      by (auto simp add: "1" cf_def edges_and_costs_def ef_def)
    obtain list where listexists:"realising_edges_lookup realising_edges
                     (fstv e, sndv e) = Some list"
      using realising_edges_dom[of "fstv e" "sndv e"] assms(1,2) 1
      by (auto simp add:  es_def  \<E>_list_def make_pair_fst_snd  \<E>_def \<E>_impl(1) to_list(1))
    have ee_in_ingoing:"ee \<in> set ingoing_edges"
      unfolding ingoing_edges_def
      using realising_edges_dom[of "fstv e" "sndv e", simplified listexists, simplified]
               realising_edges_result[OF listexists] 
          "1" cost_flow_network.to_vertex_pair.simps cost_flow_network.to_vertex_pair_fst_snd \<E>_def 
          \<E>_impl(1) \<E>_list_def assms(1) assms(2) to_list(1) listexists
      by (fastforce simp add: ingoing_edges_def make_pairs_are)
    have "cf \<le> \<c> ee"
      using 1 assms(1-4) ee_in_ingoing 
      by (auto intro: ef_cf_prop(2)[of ee] simp add: algo.infinite_u edges_and_costs_def)
      moreover have "cf \<noteq>MInfty" 
      using ef_cf_prop(1) by(auto simp add: edges_and_costs_def) 
    ultimately show ?case
      using find_cheapest_backward_props[OF prod.collapse refl, of f nb outgoing_edges
                  "create_edge (sndv e) (fstv e)" PInfty]
      by auto (auto simp add: cb_def)
  next
    case (2 ee)
    define edges_and_costs where "edges_and_costs =
      Set.insert (create_edge (fst ee) (snd ee), PInfty)
       {(e, ereal (- \<c> e)) |e. e \<in> set outgoing_edges \<and> nb e \<and> 0 < ereal (f e)}"
    have ef_cf_prop:"(eb, cb) \<in> edges_and_costs" "\<And> ee cc. (ee, cc)\<in>edges_and_costs \<Longrightarrow> cb \<le> cc"
      using find_cheapest_backward_props[of eb cb f nb outgoing_edges 
                            "create_edge (fst ee) (snd ee)" PInfty edges_and_costs]     
      by(auto simp add: "2" cb_def edges_and_costs_def eb_def)
      
    obtain list where listexists:"realising_edges_lookup realising_edges
                     (sndv e, fstv e) = Some list"
      using realising_edges_dom[of "sndv e" "fstv e"] assms(1,2) 2
      by (auto simp add:  es_def  \<E>_list_def make_pair_fst_snd  \<E>_def \<E>_impl(1) to_list(1))
    have ee_in_ingoing:"ee \<in> set outgoing_edges"
      unfolding ingoing_edges_def
      using realising_edges_dom[of "sndv e" "fstv e", simplified listexists, simplified]
               realising_edges_result[OF listexists] 
          2 cost_flow_network.to_vertex_pair.simps cost_flow_network.to_vertex_pair_fst_snd \<E>_def 
          \<E>_impl(1) \<E>_list_def assms(1) assms(2) to_list(1) listexists
      by (fastforce simp add: outgoing_edges_def make_pairs_are)
    have "cb \<le> - \<c> ee"
      using 2 assms(1-4) ee_in_ingoing 
      by (auto intro: ef_cf_prop(2)[of ee] simp add: algo.infinite_u edges_and_costs_def)
   moreover have "cb \<noteq>MInfty" 
      using ef_cf_prop(1) by(auto simp add: edges_and_costs_def)
    ultimately show ?case
      using find_cheapest_forward_props[OF prod.collapse refl, of f nb ingoing_edges
                  "create_edge (fstv e) (sndv e)" PInfty]
      by auto (auto simp add: cf_def) 
  qed
qed

lemma less_PInfty_not_blocked:
 "prod.snd (get_edge_and_costs_forward nb f (fst e) (snd e)) \<noteq> PInfty
 \<Longrightarrow> nb (oedge (prod.fst (get_edge_and_costs_forward nb f (fst e) (snd e))))"
  using get_edge_and_costs_forward_result_props prod.exhaust_sel by blast

lemma less_PInfty_not_blocked_backward:
 "prod.snd (get_edge_and_costs_backward nb f (fst e) (snd e)) \<noteq> PInfty
 \<Longrightarrow> nb (oedge (prod.fst (get_edge_and_costs_backward nb f (fst e) (snd e))))"
  using get_edge_and_costs_backward_result_props prod.exhaust_sel by blast  

abbreviation "weight nb f \<equiv> bellman_ford.weight (\<lambda> u v. prod.snd (get_edge_and_costs_forward nb f u v))"

abbreviation "weight_backward nb f \<equiv> bellman_ford.weight (\<lambda> u v. prod.snd (get_edge_and_costs_backward nb f u v))"

lemma get_target_for_source_aux_aux:
 "(\<exists> x \<in> set xs. b x <  - \<epsilon> * \<gamma> \<and> prod.snd (the (connection_lookup connections x)) < PInfty) 
  \<longleftrightarrow>( (get_target_for_source_aux_aux connections b \<gamma> xs) \<noteq> None)"
 "( (get_target_for_source_aux_aux connections b \<gamma> xs) \<noteq> None)
  \<Longrightarrow> (let x = the (get_target_for_source_aux_aux connections b \<gamma> xs)
      in x \<in> set xs \<and> b x <  - \<epsilon> * \<gamma> \<and> prod.snd (the (connection_lookup connections x)) < PInfty)"
  by(all \<open>induction connections b \<gamma> xs rule: get_target_for_source_aux_aux.induct\<close>) auto

lemma get_target_for_source_aux:
 "\<lbrakk>(\<exists> x \<in> set xs. b x <  - \<epsilon> * \<gamma> \<and> prod.snd (the (connection_lookup connections x)) < PInfty); 
    res = (get_target_for_source_aux connections b \<gamma> xs) \<rbrakk>
  \<Longrightarrow> b res < - \<epsilon> * \<gamma> \<and> res \<in> set xs \<and> prod.snd (the (connection_lookup connections res)) < PInfty"
  by (subst (asm) get_target_for_source_aux_def,
       induction connections b \<gamma> xs rule: get_target_for_source_aux_aux.induct) force+

lemma get_source_for_target_aux_aux:
  "(\<exists> x \<in> set xs. b x >  \<epsilon> * \<gamma> \<and> prod.snd (the (connection_lookup connections x)) < PInfty) 
  \<longleftrightarrow>( (get_source_for_target_aux_aux connections b \<gamma> xs) \<noteq> None)"
  "( (get_source_for_target_aux_aux connections b \<gamma> xs) \<noteq> None)
  \<Longrightarrow> (let x = the (get_source_for_target_aux_aux connections b \<gamma> xs)
       in x \<in> set xs \<and> b x > \<epsilon> * \<gamma> \<and> prod.snd (the (connection_lookup connections x)) < PInfty)"
  by ( all \<open>induction connections b \<gamma> xs rule: get_source_for_target_aux_aux.induct\<close>) auto

lemma get_source_for_target_aux:
  "\<lbrakk>(\<exists> x \<in> set xs. b x >  \<epsilon> * \<gamma> \<and> prod.snd (the (connection_lookup connections x)) < PInfty); 
     res = (get_source_for_target_aux connections b \<gamma> xs)\<rbrakk> 
  \<Longrightarrow> b res > \<epsilon> * \<gamma> \<and> res \<in> set xs \<and> prod.snd (the (connection_lookup connections res)) < PInfty"
  by (subst (asm) get_source_for_target_aux_def, 
     induction connections b \<gamma> xs rule: get_source_for_target_aux_aux.induct) force+ 

interpretation send_flow_spec: send_flow_spec
  where \<E> = \<E> 
    and \<c> = \<c> 
    and \<u> = \<u> 
    and edge_map_update = edge_map_update 
    and vset_empty = vset_empty
    and vset_delete= vset_delete 
    and vset_insert = vset_insert
    and vset_inv = vset_inv 
    and isin = isin 
    and get_from_set=get_from_set
    and filter=filter 
    and are_all=are_all 
    and set_invar=set_invar
    and to_set=to_set 
    and lookup=lookup 
    and t_set=t_set 
    and sel=sel 
    and adjmap_inv=adj_inv
    and \<epsilon> = \<epsilon> 
    and \<E>_impl=\<E>_impl 
    and empty_forest=map_empty
    and \<b> = \<b> 
    and N = N
    and snd = snd 
    and fst = fst  
    and create_edge=create_edge

    and flow_empty = flow_empty 
    and flow_lookup = flow_lookup 
    and flow_update = flow_update
    and flow_delete=flow_delete 
    and flow_invar = flow_invar

    and bal_empty = bal_empty 
    and bal_lookup = bal_lookup 
    and bal_update = bal_update
    and bal_delete=bal_delete 
    and bal_invar = bal_invar

    and conv_empty = conv_empty 
    and conv_lookup = conv_lookup 
    and conv_update = conv_update
    and conv_delete=conv_delete 
    and conv_invar = conv_invar

    and rep_comp_empty = rep_comp_empty 
    and rep_comp_lookup = rep_comp_lookup 
    and rep_comp_update = rep_comp_update
    and rep_comp_delete=rep_comp_delete 
    and rep_comp_invar = rep_comp_invar

    and not_blocked_empty = not_blocked_empty 
    and not_blocked_lookup = not_blocked_lookup 
    and not_blocked_update = not_blocked_update
    and not_blocked_delete=not_blocked_delete 
    and not_blocked_invar = not_blocked_invar

    and get_source_target_path_a = get_source_target_path_a
    and get_source_target_path_b=get_source_target_path_b
    and get_source = get_source
    and get_target=get_target
    and test_all_vertices_zero_balance=test_all_vertices_zero_balance
  by(auto intro!: send_flow_spec.intro simp add: algo.algo_spec_axioms)

lemmas send_flow = send_flow_spec.send_flow_spec_axioms

abbreviation "send_flow_call1_cond state \<equiv> send_flow_spec.send_flow_call1_cond  state"
abbreviation "send_flow_fail1_cond  state \<equiv> send_flow_spec.send_flow_fail1_cond  state"
abbreviation "send_flow_call2_cond state \<equiv> send_flow_spec.send_flow_call2_cond  state"
abbreviation "send_flow_fail2_cond  state \<equiv> send_flow_spec.send_flow_fail2_cond  state"
abbreviation "get_target_cond  state \<equiv> send_flow_spec.get_target_cond  state"
abbreviation "get_source_cond  state \<equiv> send_flow_spec.get_source_cond  state"
abbreviation "vertex_selection_cond \<equiv> send_flow_spec.vertex_selection_cond"
abbreviation "abstract_bal_map \<equiv> algo.abstract_bal_map"
abbreviation "abstract_flow_map \<equiv> algo.abstract_flow_map"
abbreviation "abstract_conv_map \<equiv> algo.abstract_conv_map"
abbreviation "abstract_not_blocked_map \<equiv> algo.abstract_not_blocked_map"
abbreviation "a_balance state \<equiv> algo.a_balance state"
abbreviation "a_current_flow state \<equiv> algo.a_current_flow state"
abbreviation "a_not_blocked state \<equiv> algo.a_not_blocked state"
abbreviation "\<V> \<equiv> multigraph.\<V>"

lemmas send_flow_fail1_condE = send_flow_spec.send_flow_fail1_condE
lemmas send_flow_call1_condE = send_flow_spec.send_flow_call1_condE
lemmas send_flow_fail1_cond_def = send_flow_spec.send_flow_fail1_cond_def
lemmas send_flow_call1_cond_def= send_flow_spec.send_flow_call1_cond_def

lemmas send_flow_fail2_condE = send_flow_spec.send_flow_fail2_condE
lemmas send_flow_call2_condE = send_flow_spec.send_flow_call2_condE
lemmas send_flow_fail2_cond_def = send_flow_spec.send_flow_fail2_cond_def
lemmas send_flow_call2_cond_def= send_flow_spec.send_flow_call2_cond_def
lemmas get_source_condE = send_flow_spec.get_source_condE
lemmas get_target_condE = send_flow_spec.get_target_condE
lemmas vertex_selection_condE = send_flow_spec.vertex_selection_condE
lemmas invar_gamma_def = algo.invar_gamma_def
lemmas invar_isOptflow_def = algo.invar_isOptflow_def
lemmas is_Opt_def = cost_flow_network.is_Opt_def
lemmas from_underlying_invars' = algo.from_underlying_invars'

abbreviation "to_graph == Adj_Map_Specs2.to_graph"
abbreviation "digraph_abs == Adj_Map_Specs2.digraph_abs"

lemma get_source_axioms_red:
   "\<lbrakk>b = balance state; \<gamma> = current_\<gamma> state; Some s = get_source state\<rbrakk> 
       \<Longrightarrow> s \<in> \<V> \<and> abstract_bal_map b s > (1 - \<epsilon>) * \<gamma>"
   "\<lbrakk>b = balance state; \<gamma> = current_\<gamma> state; Some s = get_source state\<rbrakk> 
       \<Longrightarrow> \<not> (\<exists> s \<in> \<V>. abstract_bal_map b s > (1 - \<epsilon>) * \<gamma>) \<longleftrightarrow> ((get_source state) = None)"
  using get_source_aux(2)[of s "a_balance state" "current_\<gamma> state" vs] vs_is_V 
        get_source_aux(1,3)[of vs "current_\<gamma> state" "a_balance state"]
   by(fastforce elim: get_source_condE elim:  vertex_selection_condE
            simp add: get_source_def get_source_aux_def make_pairs_are)+

lemma get_source_axioms:
   "get_source_cond s state b \<gamma> \<Longrightarrow> s \<in> \<V> \<and> abstract_bal_map b s > (1 - \<epsilon>) * \<gamma>"
   "vertex_selection_cond state b  \<gamma>
         \<Longrightarrow> \<not> (\<exists> s \<in> \<V>. abstract_bal_map b s > (1 - \<epsilon>) * \<gamma>) \<longleftrightarrow> ((get_source state) = None)"
  using get_source_aux(2)[of s "a_balance state" "current_\<gamma> state" vs] vs_is_V 
        get_source_aux(1,3)[of vs "current_\<gamma> state" "a_balance state"]
   by(fastforce elim: get_source_condE elim:  vertex_selection_condE
            simp add: get_source_def get_source_aux_def make_pairs_are)+

lemma get_target_axioms:
  "get_target_cond t state b \<gamma> \<Longrightarrow> t \<in> \<V> \<and> abstract_bal_map b t < - (1 -\<epsilon>) * \<gamma>"
  "vertex_selection_cond state b  \<gamma>
             \<Longrightarrow> \<not> (\<exists> t \<in> \<V>. abstract_bal_map b t < -(1 - \<epsilon>) * \<gamma>) \<longleftrightarrow> ((get_target state) = None)"
  using get_target_aux(2)[of t "a_balance state" "current_\<gamma> state" vs] vs_is_V 
        get_target_aux(1,3)[of vs  "a_balance state" "current_\<gamma> state"]
   by(fastforce elim: get_target_condE elim:  vertex_selection_condE
            simp add: get_target_def get_target_aux_def make_pairs_are)+

lemma get_target_axioms_red:
  "\<lbrakk>b = balance state; \<gamma> = current_\<gamma> state;  Some t = get_target state\<rbrakk>
    \<Longrightarrow> t \<in> \<V> \<and> abstract_bal_map b t < - (1 -\<epsilon>) * \<gamma>"
  "\<lbrakk>b = balance state; \<gamma> = current_\<gamma> state\<rbrakk> 
    \<Longrightarrow>  \<not> (\<exists> t \<in> \<V>. abstract_bal_map b t < -(1 - \<epsilon>) * \<gamma>) \<longleftrightarrow> ((get_target state) = None)"
  using get_target_aux(2)[of t "a_balance state" "current_\<gamma> state" vs] vs_is_V 
        get_target_aux(1,3)[of vs  "a_balance state" "current_\<gamma> state"]
   by(fastforce elim: get_target_condE elim:  vertex_selection_condE
            simp add: get_target_def get_target_aux_def make_pairs_are)+

lemma path_flow_network_path_bf:
  assumes e_weight: "\<And> e. e \<in> set pp \<Longrightarrow> prod.snd (get_edge_and_costs_forward nb f (fstv e) (sndv e)) < PInfty"
     and is_a_walk: "awalk UNIV s (map to_edge pp) tt" 
     and s_is_fstv: "s = fstv (hd pp)"
     and bellman_ford:"bellman_ford connection_empty connection_lookup connection_invar 
                                    connection_delete es vs  (\<lambda> u v. prod.snd 
                                    (get_edge_and_costs_forward nb f u v)) connection_update"  
   shows "weight nb f (awalk_verts s (map cost_flow_network.to_vertex_pair pp)) < PInfty"
  using assms(1,2)[simplified assms(3)]
proof(subst assms(3), induction pp  rule: list_induct3)
  case 1
  then show ?case 
    using  bellman_ford.weight.simps[OF bellman_ford] by auto
next
  case (2 x)
  then show ?case
    using  bellman_ford.weight.simps[OF bellman_ford] apply auto[1]
    apply(induction x rule: cost_flow_network.to_vertex_pair.induct)
     apply(simp add: bellman_ford.weight.simps[OF bellman_ford] make_pair_fst_snd 
                    make_pairs_are Instantiation.make_pair_def)+
    done
next
  case (3 e d es)
  have same_ends:"sndv e = fstv d"
    using 3(3)
    by(induction e rule: cost_flow_network.to_vertex_pair.induct)
      (auto intro: cost_flow_network.to_vertex_pair.induct[OF , of _ d]  
        simp add:  bellman_ford.weight.simps[OF bellman_ford]
                           Awalk.awalk_simps make_pair_fst_snd  Instantiation.make_pair_def
                 cost_flow_network.vs_to_vertex_pair_pres(1) make_pairs_are)
  have "weight nb f
        (awalk_verts (fstv (hd ((e # d # es)))) (map cost_flow_network.to_vertex_pair (e # d # es))) =
        prod.snd (get_edge_and_costs_forward nb f (fstv e) (sndv e))
        + weight nb f (awalk_verts (fstv (hd (( d # es)))) (map cost_flow_network.to_vertex_pair (d # es)))"
    using same_ends
    by(induction e rule: cost_flow_network.to_vertex_pair.induct)
      (auto intro:  cost_flow_network.to_vertex_pair.induct[OF , of _ d]
           simp add:  bellman_ford.weight.simps[OF bellman_ford]
                  cost_flow_network.to_vertex_pair_fst_snd multigraph.make_pair)
    moreover have "prod.snd (get_edge_and_costs_forward nb f (fstv e) (sndv e)) < PInfty"
      using "3.prems"(1) by force
    moreover have "weight nb f (awalk_verts (fstv (hd (( d # es)))) (map cost_flow_network.to_vertex_pair (d # es))) < PInfty"
      using 3(2,3)
      by(intro  3(1), auto intro: cost_flow_network.to_vertex_pair.induct[OF , of _ e] 
                simp add: bellman_ford.weight.simps[OF bellman_ford] Awalk.awalk_simps(2)[of UNIV] 
                       cost_flow_network.vs_to_vertex_pair_pres(1))
    ultimately show ?case by simp
  qed

lemma path_bf_flow_network_path:
  assumes True
      and len: "length pp \<ge> 2"
     and "weight nb f pp < PInfty" "ppp = edges_of_vwalk pp"      
   shows "awalk UNIV  (hd pp) ppp (last pp) \<and>
            weight nb f pp = foldr (\<lambda> e acc. \<cc> e + acc)
                  (map (\<lambda> e. (prod.fst (get_edge_and_costs_forward nb f (prod.fst e) (prod.snd e)))) ppp) 0
              \<and> (\<forall> e \<in> set (map (\<lambda> e. (prod.fst (get_edge_and_costs_forward nb f (prod.fst e) (prod.snd e)))) ppp).
                  nb (oedge e) \<and> cost_flow_network.rcap  f e > 0)"
proof-
  have bellman_ford:"bellman_ford  connection_empty connection_lookup connection_invar connection_delete
     es vs (\<lambda> u v. prod.snd (get_edge_and_costs_forward nb f u v)) connection_update"
    by (simp add: bellman_ford)
  show ?thesis
  using assms(3-)
proof(induction pp arbitrary: ppp rule: list_induct3_len_geq_2)
  case 1
  then show ?case
    using len by simp
next
  case (2 x y)
  have "awalk UNIV (hd [x, y]) ppp (last [x, y])"
    using 2     unfolding get_edge_and_costs_forward_def Let_def
    by (auto simp add: arc_implies_awalk bellman_ford.weight.simps[OF bellman_ford] 
           split: if_split prod.split)
  moreover have "weight nb f [x, y] =
    ereal
     (foldr (\<lambda>e. (+) (\<cc> e)) (map (\<lambda>e. prod.fst (get_edge_and_costs_forward nb f (prod.fst e) (prod.snd e))) ppp) 0)"
    using 2  bellman_ford.weight.simps[OF bellman_ford]  
    by(auto simp add: arc_implies_awalk get_edge_and_costs_forward_result_props)
    moreover have "(\<forall>e\<in>set (map (\<lambda>e. prod.fst (get_edge_and_costs_forward nb f (prod.fst e) (prod.snd e))) ppp).
        nb (flow_network_spec.oedge e) \<and> 0 < cost_flow_network.rcap f e)"
      using 2  bellman_ford.weight.simps[OF bellman_ford] flow_network_spec.oedge.simps
                cost_flow_network.rcap.simps get_edge_and_costs_forward_result_props[OF sym[OF prod.collapse], of nb f x y]
      by(auto simp add: \<u>_def)
    ultimately show ?case by simp
next
  case (3 x y xs)
  thm 3(1)[OF _ refl]
  have "awalk UNIV (hd (x # y # xs)) ppp (last (x # y # xs))"
    using conjunct1[OF "3.IH"[OF _ refl]] "3.prems"(1) 
           bellman_ford.weight.simps(3)[OF bellman_ford ] edges_of_vwalk.simps(3)
    by (simp add:  "3.prems"(2)  Awalk.awalk_simps(2))
  moreover have " weight nb f (x # y # xs) =  prod.snd (get_edge_and_costs_forward nb f x y) +
                                       weight nb f (y # xs)"
    using bellman_ford bellman_ford.weight.simps(3) by fastforce
  moreover have "weight nb f (y # xs) =
ereal
 (foldr (\<lambda>e. (+) (\<cc> e))
   (map (\<lambda>e. prod.fst (get_edge_and_costs_forward nb f (prod.fst e) (prod.snd e))) (edges_of_vwalk (y # xs))) 0)"
    using "3.IH" "3.prems"(1) calculation(2) by fastforce
  moreover have "prod.snd (get_edge_and_costs_forward nb f x y) = 
                  \<cc> (prod.fst (get_edge_and_costs_forward nb f x y) )"
    using  "3.prems"(1) bellman_ford.weight.simps[OF bellman_ford]
    by (simp add: get_edge_and_costs_forward_result_props)
  moreover have "(\<forall>e\<in>set (map (\<lambda>e. prod.fst (get_edge_and_costs_forward nb f (prod.fst e) (prod.snd e))) (edges_of_vwalk (y # xs))).
    nb (flow_network_spec.oedge e) \<and> 0 < cost_flow_network.rcap f e)" 
    by (simp add: "3.IH" calculation(3))
  moreover have "nb (flow_network_spec.oedge (prod.fst (get_edge_and_costs_forward nb f x y)))"
    using  "3.prems"(1) bellman_ford.weight.simps[OF bellman_ford]
             get_edge_and_costs_forward_result_props[OF prod.collapse[symmetric], of nb f x y]
    by auto
  moreover have "0 < cost_flow_network.rcap f  (prod.fst (get_edge_and_costs_forward nb f x y))"
    using  "3.prems"(1) bellman_ford.weight.simps[OF bellman_ford]
           cost_flow_network.rcap.simps 
           get_edge_and_costs_forward_result_props[OF prod.collapse[symmetric], of nb f x y]
    by (auto simp add: \<u>_def)
  ultimately show ?case
    by (auto simp add: 3(3))   
qed
qed

lemma no_neg_cycle_in_bf: 
  assumes "invar_isOptflow state" "underlying_invars state"
  shows   "\<nexists>c. weight (a_not_blocked state) (a_current_flow state) c < 0 \<and> hd c = last c"
proof(rule nexistsI, goal_cases)
  case (1 c)
  have bellman_ford:"bellman_ford connection_empty connection_lookup connection_invar connection_delete
     es vs (\<lambda> u v. prod.snd (get_edge_and_costs_forward (a_not_blocked state) (a_current_flow state) u v)) connection_update"
    by (simp add: bellman_ford)
  have length_c: "length c \<ge> 2"
    using 1 bellman_ford.weight.simps[OF bellman_ford] 
    by(cases c rule: list_cases3) auto
  have weight_le_PInfty:"weight (a_not_blocked state) (a_current_flow state) c < PInfty" 
    using "1"(1) by fastforce
  have path_with_props:"awalk UNIV (hd c) (edges_of_vwalk c) (last c)"
       "weight (a_not_blocked state) (a_current_flow state) c =
       ereal (foldr (\<lambda>e. (+) (\<cc> e))
        (map (\<lambda>e. prod.fst (get_edge_and_costs_forward (a_not_blocked state) (a_current_flow state) (prod.fst e) (prod.snd e)))
                      (edges_of_vwalk c)) 0)"
      "(\<And> e. e\<in>set (map (\<lambda>e. prod.fst (get_edge_and_costs_forward (a_not_blocked state) (a_current_flow state) (prod.fst e)
                         (prod.snd e)))
           (edges_of_vwalk c)) \<Longrightarrow>
        a_not_blocked state (flow_network_spec.oedge e) \<and> 0 < cost_flow_network.rcap (a_current_flow state) e)"
    using path_bf_flow_network_path[OF _ length_c weight_le_PInfty refl] by auto
  define cc where "cc = (map (\<lambda>e. prod.fst (get_edge_and_costs_forward (a_not_blocked state) (a_current_flow state) (prod.fst e) (prod.snd e)))
                       (edges_of_vwalk c))"
  have "map (to_edge \<circ> (\<lambda>e. prod.fst (local.get_edge_and_costs_forward (a_not_blocked state)
                     (a_current_flow state) (prod.fst e) (prod.snd e)))) (edges_of_vwalk c) =
          edges_of_vwalk c"
    apply(subst (2) sym[OF List.list.map_id[of "edges_of_vwalk c"]])
    apply(rule map_ext)
    using cost_flow_network.to_vertex_pair.simps cost_flow_network.\<cc>.simps 
    by(auto intro:  map_ext simp add: to_edge_get_edge_and_costs_forward) 
  hence same_edges:"(map cost_flow_network.to_vertex_pair cc) = (edges_of_vwalk c)"
    by(auto simp add: cc_def )
  have c_non_empt:"cc \<noteq> []"
    using path_with_props(1)  "1"(1) awalk_fst_last bellman_ford.weight.simps[OF bellman_ford] 
           cost_flow_network.vs_to_vertex_pair_pres 
    by (auto intro:  edges_of_vwalk.elims [OF sym[OF same_edges]])
  moreover have awalk_f:" awalk UNIV (fstv (hd cc)) (map cost_flow_network.to_vertex_pair cc) (sndv (last cc))"
  proof-
    have helper: "\<lbrakk> c = v # v' # l; cc = z # zs; to_edge z = (v, v'); map to_edge zs = edges_of_vwalk (v' # l);
                    awalk UNIV v ((v, v') # edges_of_vwalk (v' # l)) (if l = [] then v' else last l);zs \<noteq> []\<rbrakk>
        \<Longrightarrow> awalk UNIV v ((v, v') # edges_of_vwalk (v' # l)) (prod.snd (to_edge (last zs)))"
      for v v' l z zs 
      by(metis awalk_fst_last last_ConsR last_map list.simps(3) list.simps(9))
      show ?thesis
    apply(rule edges_of_vwalk.elims [OF sym[OF same_edges]])
    using path_with_props(1) same_edges 
    using "1"(1) awalk_fst_last bellman_ford.weight.simps[OF bellman_ford] 
           cost_flow_network.vs_to_vertex_pair_pres apply auto[2]
    using calculation  path_with_props(1) same_edges 
    by(auto simp add: cost_flow_network.vs_to_vertex_pair_pres awalk_intros(1) intro: helper)
   qed
  ultimately have "cost_flow_network.prepath cc"
    using prepath_def by blast
  moreover have "0 < cost_flow_network.Rcap (a_current_flow state) (set cc)"
    using cc_def path_with_props(3)
    by(auto simp add: cost_flow_network.Rcap_def)
  ultimately have agpath:"augpath (a_current_flow state) cc"
    by(simp add: augpath_def)
  have cc_in_E: "set cc \<subseteq> EEE"
  proof(rule, rule ccontr, goal_cases)
    case (1 e)
    hence "to_edge e \<in> set (edges_of_vwalk c)"
      by (metis map_in_set same_edges)
    then obtain c1 c2 where c_split:"c1@[prod.fst (to_edge e)]@[prod.snd (to_edge e)]@c2 = c" 
      apply(induction e rule: cost_flow_network.to_vertex_pair.induct)
      subgoal for e
      using edges_in_vwalk_split[of "fst e" "snd e" c] cost_flow_network.to_vertex_pair.simps
            multigraph.make_pair by auto
      subgoal for e
      using edges_in_vwalk_split[of "snd e" "fst e" c] cost_flow_network.to_vertex_pair.simps
            multigraph.make_pair by auto
    done
  have le_infty:"prod.snd (get_edge_and_costs_forward (a_not_blocked state) (a_current_flow state) (prod.fst (to_edge e))
             (prod.snd (to_edge e))) < PInfty"
  proof(rule ccontr, goal_cases)
    case 1
    hence "prod.snd (get_edge_and_costs_forward (a_not_blocked state) (a_current_flow state) (prod.fst (cost_flow_network.to_vertex_pair e))
           (prod.snd (cost_flow_network.to_vertex_pair e)))
     = PInfty" by simp
    hence "weight (a_not_blocked state) (a_current_flow state) c = PInfty"
      using bellman_ford.edge_and_Costs_none_pinfty_weight[OF bellman_ford]
            c_split by auto
    thus False
      using weight_le_PInfty by force
  qed
  have one_not_blocked:"a_not_blocked state (oedge e)"
    using less_PInfty_not_blocked  "1"(1) cc_def path_with_props(3) by blast
  hence "oedge e \<in> \<E>"
    using assms(2) 
    unfolding algo.underlying_invars_def  algo.inv_unbl_iff_forest_active_def
                algo.inv_actives_in_E_def  algo.inv_forest_in_E_def
    by auto
  thus ?case
    using  1(2) cost_flow_network.o_edge_res by blast
qed
  obtain C where "augcycle (a_current_flow state) C"
    apply(rule cost_flow_network.augcycle_from_non_distinct_cycle[OF  agpath])
    using "1"(1) awalk_f c_non_empt awalk_fst_last[OF _ awalk_f]
          awalk_fst_last[OF _ path_with_props(1)] same_edges  cc_in_E  "1"(1) cc_def path_with_props(2)
    by auto
  then show ?case 
    using assms(1) invar_isOptflow_def cost_flow_network.min_cost_flow_no_augcycle by blast
qed
    

lemma get_target_for_source_ax:
" \<lbrakk>b = balance state; \<gamma> = current_\<gamma> state; f = current_flow state; Some s = get_source state;
   get_source_target_path_a state s = Some (t,P); invar_gamma state; invar_isOptflow state;
   underlying_invars state\<rbrakk>
  \<Longrightarrow> t \<in> VV \<and> (abstract_bal_map b) t < - \<epsilon> * \<gamma> \<and> resreach (abstract_flow_map f) s t \<and> s \<noteq> t"
proof( goal_cases)
  case 1
  note one = this
  have s_prop: "s \<in> \<V>" "(1 - local.\<epsilon>) * \<gamma> < abstract_bal_map b s"
 using get_source_axioms_red(1)[OF 1(1,2,4)] by auto
 define bf where  "bf = bellman_ford_forward (a_not_blocked state) (a_current_flow state) s"
  define tt_opt where "tt_opt = (get_target_for_source_aux_aux bf 
                     (\<lambda> v. abstract_real_map (bal_lookup (balance state)) v)
                                           (current_\<gamma> state) vs)"
  show ?thesis
  proof(cases tt_opt)
    case None
    hence "get_source_target_path_a state s = None"
      by(auto simp add: option_none_simp[of "get_target_for_source_aux_aux _ _ _ _"] 
                 algo.abstract_not_blocked_map_def option.case_eq_if 
                   tt_opt_def bf_def get_source_target_path_a_def)   
    hence False
      using 1 by simp
    thus ?thesis by simp
  next
    case (Some a)
  define tt where "tt = the tt_opt"
  define Pbf where "Pbf = itrev (search_rev_path_exec s bf tt)"
  define PP where "PP = map (\<lambda>e. prod.fst (get_edge_and_costs_forward (a_not_blocked state) (a_current_flow state)
                                  (prod.fst e) (prod.snd e)))
                   (edges_of_vwalk Pbf)"
  have tt_opt_tt:"tt_opt = Some tt"
    by (simp add: Some tt_def)
  have "Some (tt, PP) = Some (t, P)"
    using 1
    by(cases tt_opt)
      (auto simp add: option_none_simp[of "get_target_for_source_aux_aux _ _ _ _"] 
                 algo.abstract_not_blocked_map_def option.case_eq_if 
                   tt_opt_def bf_def get_source_target_path_a_def tt_def
                   PP_def Pbf_def pair_to_realising_redge_forward_def)
  hence tt_is_t: "tt = t" and PP_is_P: "PP = P" by auto 
  have t_props: "tt \<in> set local.vs"
     "a_balance state tt < - local.\<epsilon> * current_\<gamma> state"
     "prod.snd (the (connection_lookup bf tt)) < PInfty"
    using get_target_for_source_aux_aux(2)[of bf "a_balance state" "current_\<gamma> state" vs]
           Some
    by(auto simp add: tt_def tt_opt_def)
   have bellman_ford:"bellman_ford connection_empty connection_lookup connection_invar connection_delete
     es vs (\<lambda> u v. prod.snd (get_edge_and_costs_forward (a_not_blocked state) (a_current_flow state) u v)) connection_update"
      using bellman_ford by blast
   define connections where "connections = 
          (bellman_ford_forward (a_not_blocked state) (a_current_flow state) s)"
   have tt_dist_le_PInfty:"prod.snd (the (connection_lookup connections tt)) < PInfty"
     using bf_def connections_def t_props(3) by blast
  have t_prop:"a_balance state t < - \<epsilon> * current_\<gamma> state \<and>
         t \<in> set vs \<and> prod.snd (the (connection_lookup connections t)) < PInfty"
    using t_props by(auto simp add: tt_is_t connections_def  bf_def)
  have t_neq_s: "t \<noteq> s"
    using t_prop s_prop "1"(1) "1"(2) invar_gamma_def
    by (smt (verit, best) "1"(6) mult_minus_left mult_mono')
  have t_in_dom: "t \<in> dom (connection_lookup  connections)"
    using t_prop
    by (auto simp add: bellman_ford.bellman_ford_init_dom_is[OF bellman_ford]
                       bellman_ford.same_domain_bellman_ford[OF bellman_ford]
                       connections_def bellman_ford_forward_def
                       bellman_ford_init_algo_def bellman_ford_algo_def)
  hence pred_of_t_not_None: "prod.fst (the (connection_lookup connections t)) \<noteq> None"
    using t_neq_s t_prop bellman_ford.bellman_ford_pred_non_infty_pres[OF bellman_ford, of s "length vs -1"]
    by(auto simp add:  connections_def bellman_ford_forward_def 
         bellman_ford.invar_pred_non_infty_def[OF bellman_ford]
         bellman_ford_init_algo_def bellman_ford_algo_def)
  define Pbf where "Pbf = rev (bellman_ford_spec.search_rev_path connection_lookup s connections t)"
  have "weight (a_not_blocked state) 
          (a_current_flow state) Pbf = prod.snd (the (connection_lookup connections t))"
    unfolding Pbf_def
    using t_prop  t_neq_s  s_prop vs_is_V  pred_of_t_not_None 1(7,8)
    by(fastforce simp add: bellman_ford_forward_def connections_def
                bellman_ford_init_algo_def bellman_ford_algo_def make_pairs_are
                 intro!: bellman_ford.bellman_ford_search_rev_path_weight[OF 
                bellman_ford no_neg_cycle_in_bf, of connections s t]) +
  hence weight_le_PInfty: "weight (a_not_blocked state) (a_current_flow state) Pbf < PInfty"
    using t_prop by auto
  have Pbf_opt_path: "bellman_ford.opt_vs_path vs
 (\<lambda>u v. prod.snd (get_edge_and_costs_forward (a_not_blocked state) (a_current_flow state) u v)) s t
 (rev (bellman_ford_spec.search_rev_path connection_lookup s connections t))"
    using t_prop  t_neq_s  s_prop(1) vs_is_V  pred_of_t_not_None 1(7,8)
    by (auto simp add: bellman_ford_forward_def connections_def bellman_ford_init_algo_def
                       bellman_ford_algo_def make_pairs_are
                 intro!: bellman_ford.computation_of_optimum_path[OF bellman_ford no_neg_cycle_in_bf])
  hence length_Pbf:"2 \<le> length Pbf" 
    by(auto simp add: bellman_ford.opt_vs_path_def[OF bellman_ford]
      bellman_ford.vs_path_def[OF bellman_ford] Pbf_def)
  have "awalk UNIV (hd Pbf) (edges_of_vwalk Pbf) (last Pbf) \<and>
         weight (a_not_blocked state) (a_current_flow state) Pbf =
         ereal  (foldr (\<lambda>e. (+) (\<cc> e))
        (map (\<lambda>e. prod.fst (get_edge_and_costs_forward (a_not_blocked state) (a_current_flow state) (prod.fst e) (prod.snd e)))
                       (edges_of_vwalk Pbf)) 0) \<and>
         (\<forall>e\<in>set (map (\<lambda>e. prod.fst (get_edge_and_costs_forward (a_not_blocked state) (a_current_flow state) (prod.fst e)
                         (prod.snd e)))
           (edges_of_vwalk Pbf)).
    a_not_blocked state (flow_network_spec.oedge e) \<and> 0 < cost_flow_network.rcap (a_current_flow state) e)"
    by(intro path_bf_flow_network_path[OF _ length_Pbf weight_le_PInfty refl]) simp
  hence Pbf_props: "awalk UNIV (hd Pbf) (edges_of_vwalk Pbf) (last Pbf)"
                   " weight (a_not_blocked state) (a_current_flow state) Pbf =
         ereal  (foldr (\<lambda>e. (+) (\<cc> e))
        (map (\<lambda>e. prod.fst (get_edge_and_costs_forward (a_not_blocked state) (a_current_flow state) (prod.fst e) (prod.snd e)))
                   (edges_of_vwalk Pbf)) 0)"
                   "(\<And> e. e \<in> set (map (\<lambda>e. prod.fst (get_edge_and_costs_forward (a_not_blocked state) (a_current_flow state) (prod.fst e)
                         (prod.snd e)))
           (edges_of_vwalk Pbf)) \<Longrightarrow>
    a_not_blocked state (flow_network_spec.oedge e) \<and> 0 < cost_flow_network.rcap (a_current_flow state) e)"
    by auto
  define P where "P = (map (\<lambda>e. prod.fst (get_edge_and_costs_forward (a_not_blocked state) (a_current_flow state) (prod.fst e) (prod.snd e)))
                   (edges_of_vwalk Pbf))"
  have same_edges:"(map cost_flow_network.to_vertex_pair P) = (edges_of_vwalk Pbf)"
    apply(simp add: P_def , subst (2) sym[OF List.list.map_id[of "edges_of_vwalk Pbf"]])
    using get_edge_and_costs_forward_result_props[OF prod.collapse[symmetric] _ refl]
          to_edge_get_edge_and_costs_forward 
    by (fastforce intro!: map_ext)
  moreover have awalk_f:" awalk UNIV (fstv (hd P)) (map cost_flow_network.to_vertex_pair P) 
(sndv (last P))"
    apply(rule edges_of_vwalk.elims [OF sym[OF same_edges]])
    using Pbf_props(1) same_edges length_Pbf  "1"(1) awalk_fst_last bellman_ford.weight.simps[OF bellman_ford] 
           cost_flow_network.vs_to_vertex_pair_pres apply auto[2]
    using calculation  Pbf_props(1) same_edges 
    by(auto simp add: cost_flow_network.vs_to_vertex_pair_pres awalk_intros(1) 
                        arc_implies_awalk[OF UNIV_I refl]) 
      (metis awalk_fst_last last_ConsR last_map list.simps(3) list.simps(9))
  moreover have "P \<noteq> []"
    using  edges_of_vwalk.simps(3) length_Pbf same_edges
    by(cases Pbf rule: list_cases3) auto
  ultimately have "cost_flow_network.prepath P"
  by(auto simp add: cost_flow_network.prepath_def )
  moreover have "0 < cost_flow_network.Rcap (a_current_flow state) (set P)"
    using P_def Pbf_props(3)
    by(auto simp add: cost_flow_network.Rcap_def)
  ultimately have "augpath (a_current_flow state) P"
    by(auto simp add: cost_flow_network.augpath_def)
  moreover have "fstv (hd P) = s" 
    using awalk_f same_edges Pbf_opt_path  awalk_ends[OF Pbf_props(1)] t_neq_s
    by (force simp add: P_def bellman_ford.opt_vs_path_def[OF bellman_ford]
                        bellman_ford.vs_path_def[OF bellman_ford] Pbf_def)
  moreover have "sndv (last P) = t" 
    using awalk_f same_edges Pbf_opt_path  awalk_ends[OF Pbf_props(1)] t_neq_s
    by (force simp add: P_def bellman_ford.opt_vs_path_def[OF bellman_ford]
                        bellman_ford.vs_path_def[OF bellman_ford] Pbf_def)
  moreover have "set P \<subseteq> EEE"
  proof(rule, rule ccontr, goal_cases)
    case (1 e)
    hence "to_edge e \<in> set (edges_of_vwalk Pbf)"
      by (metis map_in_set same_edges)
    then obtain c1 c2 where c_split:"c1@[prod.fst (to_edge e)]@[prod.snd (to_edge e)]@c2 = Pbf" 
      apply(induction e rule: cost_flow_network.to_vertex_pair.induct)
      subgoal for e
        using edges_in_vwalk_split[of "fst e" "snd e" Pbf] multigraph.make_pair 
        by (auto simp add: Instantiation.make_pair_def)
      subgoal for e 
        using edges_in_vwalk_split[of "snd e" "fst e" Pbf] multigraph.make_pair 
        by (auto simp add: Instantiation.make_pair_def)
    done
  have le_infty:"prod.snd (get_edge_and_costs_forward (a_not_blocked state) (a_current_flow state) (prod.fst (cost_flow_network.to_vertex_pair e))
             (prod.snd (to_edge e))) < PInfty"
  proof(rule ccontr, goal_cases)
    case 1
    hence "prod.snd (get_edge_and_costs_forward (a_not_blocked state) (a_current_flow state) (prod.fst (cost_flow_network.to_vertex_pair e))
           (prod.snd (cost_flow_network.to_vertex_pair e)))
     = PInfty" by auto
    hence "weight (a_not_blocked state) (a_current_flow state) Pbf = PInfty"
      using bellman_ford.edge_and_Costs_none_pinfty_weight[OF bellman_ford]
            c_split by auto
    thus False
      using weight_le_PInfty by force
  qed
  have one_not_blocked:"a_not_blocked state (oedge e)"
    using less_PInfty_not_blocked  "1"(1) P_def Pbf_props(3) by blast
  hence "oedge e \<in> \<E>"
    using one(8)
    by(auto elim!: algo.underlying_invarsE algo.inv_unbl_iff_forest_activeE algo.inv_actives_in_EE algo.inv_forest_in_EE)
  thus ?case 
    using "1"(2) cost_flow_network.o_edge_res by blast
  qed
  ultimately have "resreach (abstract_flow_map f) s t"
    using cost_flow_network.augpath_imp_resreach 1(3) by fast  
  thus ?thesis 
    using "1"(1,2) t_prop vs_is_V  t_neq_s by blast
 qed
qed

lemma bf_weight_leq_res_costs:
assumes "set (map oedge qq) \<subseteq> set \<E>_list"
        " \<And> e. e \<in> set qq \<Longrightarrow> a_not_blocked state (flow_network_spec.oedge e)"
        "\<And> e. e \<in> set qq \<Longrightarrow> 0 < cost_flow_network.rcap (a_current_flow state) e"
        "unconstrained_awalk (map cost_flow_network.to_vertex_pair qq)"
   and  qq_len: "length qq \<ge> 1"
 shows "weight (a_not_blocked state) (a_current_flow state) 
                (awalk_verts s (map cost_flow_network.to_vertex_pair qq))
            \<le> foldr (\<lambda>x. (+) (\<cc> x)) qq 0" 
  using assms
proof(induction qq rule: list_induct2_len_geq_1)
  case 1
  then show ?case 
    using qq_len by blast
next
  case (2 e)
  then show ?case
      by(induction e rule: cost_flow_network.to_vertex_pair.induct) 
        (fastforce intro!: conjunct1[OF get_edge_and_costs_forward_makes_cheaper[OF 
                                  refl, of _ "a_not_blocked state" "a_current_flow state"]] 
                     intro: surjective_pairing prod.collapse
           simp add: \<E>_def \<E>_impl(1) \<E>_list_def to_list(1) make_pair_fst_snd make_pairs_are
                    Instantiation.make_pair_def
           simp del: cost_flow_network.\<cc>.simps)+
  next
    case (3 e d xs)
    have help1: 
      "\<lbrakk>(unconstrained_awalk ((fst ee, snd ee) # map to_edge xs) \<Longrightarrow>
        weight (a_not_blocked state) (a_current_flow state) (fst ee  # awalk_verts (snd ee) (map to_edge xs))
                   \<le> ereal (\<cc> (F ee) + foldr (\<lambda>x. (+) (\<cc> x)) xs 0)) ;
        (\<And>e. e = F dd \<or> e = F ee \<or> e \<in> set xs \<Longrightarrow>  a_not_blocked state (oedge e)) ;
        (\<And>e. e = F dd \<or> e = F ee \<or> e \<in> set xs \<Longrightarrow>  0 < rcap (a_current_flow state) e) ;
        unconstrained_awalk ((fst dd, snd dd) # (fst ee, snd ee) # map to_edge xs) ;
        dd \<in> set \<E>_list ; ee \<in> set \<E>_list ; oedge ` set xs \<subseteq> set \<E>_list\<rbrakk> \<Longrightarrow>
       prod.snd (get_edge_and_costs_forward (a_not_blocked state) (a_current_flow state) (fst dd) (fst ee)) +
       weight (a_not_blocked state) (a_current_flow state) (fst ee # awalk_verts (snd ee) (map to_edge xs))
       \<le> ereal (\<cc> (F dd) + (\<cc> (F ee) + foldr (\<lambda>x. (+) (\<cc> x)) xs 0))"for ee dd
    using  unconstrained_awalk_drop_hd[of "(fst dd, snd dd)"]  
    by(subst ereal_add_homo[of _ "_ + _ "])
      (fastforce intro!:  ordered_ab_semigroup_add_class.add_mono conjunct1[OF get_edge_and_costs_forward_makes_cheaper[OF 
                                  refl, of _ "a_not_blocked state" "a_current_flow state"]]
                      intro:       trans[OF prod.collapse] 
                               cong[OF refl unconstrained_awalk_snd_verts_eq[of "fst dd" "snd dd"
                                       "fst ee" "snd ee", symmetric]]
                       simp add: \<E>_def \<E>_impl(1) \<E>_list_def to_list(1))
   have help2: 
    "\<lbrakk> (unconstrained_awalk ((snd ee, fst ee) # map to_edge xs) \<Longrightarrow>
        weight (a_not_blocked state) (a_current_flow state) (snd ee #  awalk_verts (fst ee) (map to_edge xs))
        \<le> ereal (\<cc> (B ee) + foldr (\<lambda>x. (+) (\<cc> x)) xs 0)) ;
        (\<And>e. e = F dd \<or> e = B ee \<or> e \<in> set xs \<Longrightarrow>  a_not_blocked state (oedge e)) ;
        (\<And>e. e = F dd \<or> e = B ee \<or> e \<in> set xs \<Longrightarrow>0 < rcap (a_current_flow state) e) ;
        unconstrained_awalk ((fst dd, snd dd) # (snd ee, fst ee) # map to_edge xs) ;
        dd \<in> set \<E>_list ; ee \<in> set \<E>_list; oedge ` set xs \<subseteq> set \<E>_list \<rbrakk> \<Longrightarrow>
     prod.snd (get_edge_and_costs_forward (a_not_blocked state) (a_current_flow state) (fst dd) (snd ee)) +
     weight (a_not_blocked state) (a_current_flow state) (snd ee # awalk_verts (fst ee) (map to_edge xs))
     \<le> ereal (\<cc> (F dd) + (\<cc> (B ee) + foldr (\<lambda>x. (+) (\<cc> x)) xs 0))"for ee dd
    using  unconstrained_awalk_drop_hd[of "(fst dd, snd dd)"] 
    by(subst ereal_add_homo[of _ "_ + _ "])
         (fastforce intro!:  ordered_ab_semigroup_add_class.add_mono conjunct1[OF get_edge_and_costs_forward_makes_cheaper[OF 
                                  refl, of _ "a_not_blocked state" "a_current_flow state"]]
                      intro:       trans[OF prod.collapse] 
                               cong[OF refl unconstrained_awalk_snd_verts_eq[of "fst dd" "snd dd"
                                       "snd ee" "fst ee", symmetric]]
                       simp add: \<E>_def \<E>_impl(1) \<E>_list_def to_list(1))
    have help3: 
    "\<lbrakk>(unconstrained_awalk ((fst ee, snd ee) # map to_edge xs) \<Longrightarrow>
       weight (a_not_blocked state) (a_current_flow state) (fst ee # awalk_verts (snd ee) (map to_edge xs))
        \<le> ereal (\<cc> (F ee) + foldr (\<lambda>x. (+) (\<cc> x)) xs 0));
       (\<And>e. e = B dd \<or> e = F ee \<or> e \<in> set xs \<Longrightarrow> a_not_blocked state (oedge e));
       (\<And>e. e = B dd \<or> e = F ee \<or> e \<in> set xs \<Longrightarrow> 0 < rcap (a_current_flow state) e) ;
       unconstrained_awalk ((snd dd, fst dd) # (fst ee, snd ee) # map to_edge xs);
       dd \<in> set \<E>_list; ee \<in> set \<E>_list; oedge ` set xs \<subseteq> set \<E>_list\<rbrakk> \<Longrightarrow>
      prod.snd (get_edge_and_costs_forward (a_not_blocked state) (a_current_flow state) (snd dd) (fst ee)) +
      weight (a_not_blocked state) (a_current_flow state) (fst ee # awalk_verts (snd ee) (map to_edge xs))
      \<le> ereal (\<cc> (B dd) + (\<cc> (F ee) + foldr (\<lambda>x. (+) (\<cc> x)) xs 0))"
    for dd ee
       using unconstrained_awalk_drop_hd[of "(snd dd, fst dd)"] 
       by(subst ereal_add_homo[of _ "_ + _ "])
         (fastforce intro!:  ordered_ab_semigroup_add_class.add_mono conjunct1[OF get_edge_and_costs_forward_makes_cheaper[OF 
                                  refl, of _ "a_not_blocked state" "a_current_flow state"]]
                      intro:       trans[OF prod.collapse] 
                               cong[OF refl unconstrained_awalk_snd_verts_eq[of "snd dd" "fst dd"
                                       "fst ee" "snd ee", symmetric]]
                       simp add: \<E>_def \<E>_impl(1) \<E>_list_def to_list(1))
     have help4: 
       "\<lbrakk>(unconstrained_awalk ((snd ee, fst ee) # map to_edge xs) \<Longrightarrow>
           weight (a_not_blocked state) (a_current_flow state) (snd ee # awalk_verts (fst ee) (map to_edge xs))
           \<le> ereal (\<cc> (B ee) + foldr (\<lambda>x. (+) (\<cc> x)) xs 0));
          (\<And>e. e = B dd \<or> e = B ee \<or> e \<in> set xs \<Longrightarrow> a_not_blocked state (oedge e));
          (\<And>e. e = B dd \<or> e = B ee \<or> e \<in> set xs \<Longrightarrow> 0 < rcap (a_current_flow state) e);
           unconstrained_awalk ((snd dd, fst dd) # (snd ee, fst ee) # map to_edge xs);
           dd \<in> set \<E>_list ;  ee \<in> set \<E>_list ; oedge ` set xs \<subseteq> set \<E>_list \<rbrakk> \<Longrightarrow>
        prod.snd (local.get_edge_and_costs_forward (a_not_blocked state) (a_current_flow state) (snd dd) (snd ee)) +
        weight (a_not_blocked state) (a_current_flow state) (snd ee # awalk_verts (fst ee) (map to_edge xs))
         \<le> ereal (\<cc> (B dd) + (\<cc> (B ee) + foldr (\<lambda>x. (+) (\<cc> x)) xs 0))" for ee dd
       using  unconstrained_awalk_drop_hd[of "(snd dd, fst dd)"] 
       by(subst ereal_add_homo[of _ "_ + _ "])
         (fastforce intro!:  ordered_ab_semigroup_add_class.add_mono conjunct1[OF get_edge_and_costs_forward_makes_cheaper[OF 
                                  refl, of _ "a_not_blocked state" "a_current_flow state"]]
                      intro:       trans[OF prod.collapse] 
                               cong[OF refl unconstrained_awalk_snd_verts_eq[of "snd dd" "fst dd"
                                       "snd ee" "fst ee", symmetric]]
                       simp add: \<E>_def \<E>_impl(1) \<E>_list_def to_list(1))+
    show ?case
      using 3
      by(induction e rule: cost_flow_network.to_vertex_pair.induct, 
         all \<open>induction d rule: cost_flow_network.to_vertex_pair.induct\<close>) 
        (auto simp add: make_pair_fst_snd  make_pairs_are Instantiation.make_pair_def
             simp del: cost_flow_network.\<cc>.simps 
              intro: help1 help2 help3 help4)
  qed

abbreviation "get_source_target_path_a_cond \<equiv> send_flow_spec.get_source_target_path_a_cond"
lemmas get_source_target_path_a_cond_def = send_flow_spec.get_source_target_path_a_cond_def
lemmas get_source_target_path_a_condE = send_flow_spec.get_source_target_path_a_condE

lemma get_source_target_path_a_ax:
  assumes "get_source_target_path_a_cond  state s t P b \<gamma> f"
  shows   "cost_flow_network.is_min_path (abstract_flow_map f) s t P \<and>
           oedge ` set P \<subseteq> to_set (actives state) \<union> \<F> state \<and> 
           t \<in> \<V> \<and> abstract_bal_map b t < - \<epsilon> * \<gamma>"
proof-
  define bf where  "bf = bellman_ford_forward (a_not_blocked state) (a_current_flow state) s"
  define tt_opt where "tt_opt = (get_target_for_source_aux_aux bf 
                     (\<lambda> v. abstract_real_map (bal_lookup (balance state)) v)
                                           (current_\<gamma> state) vs)"
  show ?thesis
  proof(cases tt_opt)
    case None
    hence "get_source_target_path_a state s = None"
      by(auto simp add: option_none_simp[of "get_target_for_source_aux_aux _ _ _ _"] 
                 algo.abstract_not_blocked_map_def option.case_eq_if 
                   tt_opt_def bf_def get_source_target_path_a_def)     
    hence False
      using assms by (auto elim: get_source_target_path_a_condE)
    thus ?thesis by simp
  next
    case (Some a)
  define tt where "tt = the tt_opt"
  define Pbf where "Pbf = itrev (search_rev_path_exec s bf tt)"
  define PP where "PP = map (\<lambda>e. prod.fst (get_edge_and_costs_forward (a_not_blocked state) (a_current_flow state)
                                  (prod.fst e) (prod.snd e)))
                   (edges_of_vwalk Pbf)"
  have tt_opt_tt:"tt_opt = Some tt"
    by (simp add: Some tt_def)
  have "Some (tt, PP) = Some (t, P)"
    using assms
    by(cases tt_opt)
      (auto simp add: option_none_simp[of "get_target_for_source_aux_aux _ _ _ _"] 
                 algo.abstract_not_blocked_map_def option.case_eq_if 
                   tt_opt_def bf_def get_source_target_path_a_def tt_def
                  get_source_target_path_a_cond_def PP_def Pbf_def pair_to_realising_redge_forward_def)
  hence tt_is_t: "tt = t" and PP_is_P: "PP = P" by auto 
  have tt_props: "tt \<in> set local.vs"
     "a_balance state tt < - local.\<epsilon> * current_\<gamma> state"
     "prod.snd (the (connection_lookup bf tt)) < PInfty"
    using get_target_for_source_aux_aux(2)[of bf "a_balance state" "current_\<gamma> state" vs]
           Some
    by(auto simp add: tt_def tt_opt_def)
  have t_props:"t \<in> \<V>" "abstract_bal_map b t < - local.\<epsilon> * current_\<gamma> state"
       "resreach (abstract_flow_map f) s t" "s \<noteq> t" "current_\<gamma> state > 0"
    using get_target_for_source_ax[of b state, OF  _  refl, of f s t P]  assms 
    by(auto simp add: get_source_target_path_a_cond_def make_pairs_are elim: algo.invar_gammaE)
  hence bt_neg:"abstract_bal_map b t < 0"
    by (smt (verit, del_insts) local.algo.\<epsilon>_axiom(1) mult_neg_pos) 
  have s_props: "s \<in> \<V>" "(1 - local.\<epsilon>) * current_\<gamma> state < abstract_bal_map b s"
    using get_source_axioms_red(1)[of b state "current_\<gamma> state" s] assms
    by(auto simp add: get_source_target_path_a_cond_def)
  hence bs_pos: "abstract_bal_map b s > 0" 
    using t_props(5) \<epsilon>_axiom s_props(2) 
    by (auto simp add: algebra_simps)
       (smt (verit, best) mult_less_0_iff s_props(2))
  hence a_balance_s_not_zero:"a_balance state s \<noteq> 0"  
    using assms by(force simp add: get_source_target_path_a_cond_def)
  have knowledge: True
    "s \<in> VV" "t \<in> VV" "s \<noteq> t"
    "underlying_invars state"
    "(\<forall>e\<in>\<F> state. 0 < abstract_flow_map f e)"
    "resreach (abstract_flow_map f) s t"
    "b = balance state"
    "\<gamma> = current_\<gamma> state"
    "Some s = get_source state"
    "f = current_flow state"
    "invar_gamma state"
    "\<not> (\<forall>v\<in>VV. (abstract_bal_map  b) v = 0)"
    "\<exists>s\<in>VV. (1 - \<epsilon>) * \<gamma> < (abstract_bal_map  b) s"
    "\<exists>t\<in>VV. abstract_bal_map b t < - \<epsilon> * \<gamma> \<and> resreach (abstract_flow_map f) s t"
                  "t = tt"  "P = PP"
    using assms t_props t_props  a_balance_s_not_zero s_props
    by(auto simp add: get_source_target_path_a_cond_def tt_is_t PP_is_P vs_is_V make_pairs_are )
  hence 
    "(\<forall>e\<in>(abstract_conv_map (conv_to_rdg state)) ` (digraph_abs (\<FF> state)).
        0 < a_current_flow state (flow_network_spec.oedge e))"
    by (auto simp add: \<F>_def)
  have f_is: "abstract_flow_map f = a_current_flow state"
    and not_blocked_is: "abstract_not_blocked_map (not_blocked state) = a_not_blocked state"
    using assms by(auto simp add: get_source_target_path_a_cond_def)
  have t_prop: "abstract_bal_map b t < - \<epsilon> * \<gamma>" "resreach (abstract_flow_map f) s t"
    using knowledge t_props(2) by auto
  then obtain pp where pp_prop:"augpath (abstract_flow_map f) pp" "fstv (hd pp) = s" "sndv (last pp) = t" "set pp \<subseteq> EEE"
    using cost_flow_network.resreach_imp_augpath[OF , of "abstract_flow_map f" s t] by auto
  obtain ppd where ppd_props:"augpath (abstract_flow_map f) ppd" "fstv (hd ppd) = s" "sndv (last ppd) = t" "set ppd \<subseteq> set pp"
                        "distinct ppd"
    using pp_prop 
    by (auto intro:  cost_flow_network.there_is_s_t_path[OF  _ _ _ refl, of "abstract_flow_map f" pp s t])
  obtain Q where Q_min:"cost_flow_network.is_min_path (abstract_flow_map f) s t Q"
    apply(rule cost_flow_network.there_is_min_path[OF , of "abstract_flow_map f" s t ppd])
    using pp_prop ppd_props cost_flow_network.is_s_t_path_def 
    by auto
  hence Q_prop:"augpath (abstract_flow_map f) Q" "fstv (hd Q) = s" "sndv (last Q) = t"
        "set Q \<subseteq> EEE" "distinct Q"
    by(auto simp add: cost_flow_network.is_min_path_def 
              cost_flow_network.is_s_t_path_def)
  have no_augcycle: "\<nexists>C. augcycle (abstract_flow_map f) C" 
    using assms cost_flow_network.min_cost_flow_no_augcycle
    by(auto simp add: invar_isOptflow_def get_source_target_path_a_cond_def)
  obtain qq where  qq_prop:"augpath (abstract_flow_map f) qq"
     "fstv (hd qq) = s"
     "sndv (last qq) = t"
     "set qq
     \<subseteq> {e |e. e \<in> EEE \<and> flow_network_spec.oedge e \<in> to_set (actives state)} \<union>
        (abstract_conv_map (conv_to_rdg state))` (digraph_abs (\<FF> state))"
     "foldr (\<lambda>x. (+) (\<cc> x)) qq 0 \<le> foldr (\<lambda>x. (+) (\<cc> x)) Q 0" "qq \<noteq> []"
    using algo.simulate_inactives_costs[OF Q_prop(1-4) knowledge(5) refl
              f_is refl refl refl refl refl refl knowledge(4) _ no_augcycle ] 
           knowledge(6) 
    by (auto simp add: algo.\<F>_redges_def)
  have qq_len: "length qq \<ge> 1" 
    using qq_prop(2,3,6) knowledge(4)
    by(cases qq rule: list_cases3) auto
  hence e_in:"e \<in> set qq \<Longrightarrow>
            e \<in> {e |e. e \<in> EEE \<and> flow_network_spec.oedge e \<in> to_set (actives state)} 
                   \<union> (abstract_conv_map (conv_to_rdg state)) ` (digraph_abs (\<FF> state))" for e
      using qq_prop(4)  by auto
    hence e_es:"e \<in> set qq \<Longrightarrow> cost_flow_network.to_vertex_pair e \<in> set es" for e
      using es_E_frac algo.underlying_invars_subs  knowledge(5) by (fastforce simp add: algo.\<F>_redges_def)
    have e_es':"e \<in> set qq \<Longrightarrow> oedge e \<in> \<E>" for e
      using algo.from_underlying_invars'(2) cost_flow_network.o_edge_res e_in knowledge(5) by auto
    have e_in_pp_weight:"e \<in> set qq \<Longrightarrow> prod.snd (get_edge_and_costs_forward (a_not_blocked state) 
                                 (a_current_flow state) (fstv e) (sndv e)) < PInfty" for e
  proof(goal_cases)
    case 1
    note e_es[OF 1]
    moreover have oedge_where: "oedge e \<in> to_set (actives state) \<or> oedge e \<in> \<F> state"
      using e_in  1  by(auto simp add: \<F>_def)
    hence nb:"a_not_blocked state (oedge e)"
      using algo.from_underlying_invars'(20) knowledge(5) by auto
     have oedgeE:"oedge e \<in> \<E>"
      using oedge_where from_underlying_invars'(1,3)[OF knowledge(5)] by auto
    have "prod.snd (get_edge_and_costs_forward (a_not_blocked state) (a_current_flow state)
     (fstv e) (sndv e)) \<le> \<cc> e"
      using nb cost_flow_network.augpath_rcap_pos_strict'[OF qq_prop(1) 1] knowledge(11)
      by(auto intro!:  conjunct1[OF get_edge_and_costs_forward_makes_cheaper
               [OF refl oedgeE, of "a_not_blocked state" "a_current_flow state"]] prod.collapse)
    thus ?case by auto
  qed
  have bellman_ford:"bellman_ford connection_empty connection_lookup connection_invar connection_delete
     es vs (\<lambda> u v. prod.snd (get_edge_and_costs_forward (a_not_blocked state) (a_current_flow state) u v)) connection_update"
    by (simp add: bellman_ford knowledge(2) knowledge(3))
  have is_a_walk:"awalk UNIV s (map to_edge qq) tt" 
    using augpath_def knowledge(16) prepath_def qq_prop(1) qq_prop(2) qq_prop(3) by blast
  hence "vwalk_bet UNIV s (awalk_verts s (map cost_flow_network.to_vertex_pair qq)) tt"
    using  awalk_imp_vwalk by force
  moreover have weight_le_PInfty:"weight (a_not_blocked state) 
(a_current_flow state) (awalk_verts s (map cost_flow_network.to_vertex_pair qq)) < PInfty"
    using  path_flow_network_path_bf e_in_pp_weight is_a_walk bellman_ford qq_prop(2) by blast
  have no_neg_cycle_in_bf: "\<nexists>c. weight (a_not_blocked state) (a_current_flow state) c < 0 \<and> hd c = last c"
    using knowledge no_neg_cycle_in_bf assms
    by(auto elim!: get_source_target_path_a_condE)
  have long_enough: "2 \<le> length (awalk_verts s (map cost_flow_network.to_vertex_pair qq))"
    using knowledge(4) awalk_verts_non_Nil calculation knowledge(16)
          hd_of_vwalk_bet'[OF calculation] last_of_vwalk_bet[OF calculation] 
    by (cases "awalk_verts s (map cost_flow_network.to_vertex_pair qq)" rule: list_cases3) auto 
  have tt_dist_le_PInfty:"prod.snd (the (connection_lookup bf tt)) < PInfty"
    unfolding bf_def bellman_ford_forward_def bellman_ford_init_algo_def bellman_ford_algo_def
    using no_neg_cycle_in_bf  knowledge(4,16,2,3) vs_is_V weight_le_PInfty  is_a_walk long_enough 
    by (fastforce intro!:  bellman_ford.bellamn_ford_path_exists_result_le_PInfty[OF bellman_ford, of
            _ _ "(awalk_verts s (map cost_flow_network.to_vertex_pair qq))"])
   have t_dist_le_qq_weight:"prod.snd (the (connection_lookup bf t)) \<le>
                          weight (a_not_blocked state) 
                           (a_current_flow state) (awalk_verts s (map cost_flow_network.to_vertex_pair qq))"
    using   knowledge(4,16,2,3)   vs_is_V weight_le_PInfty  is_a_walk 
            bellman_ford.bellman_ford_computes_length_of_optpath[OF bellman_ford no_neg_cycle_in_bf, of s t]
            bellman_ford.opt_vs_path_def[OF bellman_ford, of s t]
            bellman_ford.vs_pathI[OF bellman_ford long_enough, of s t]
            bellman_ford.weight_le_PInfty_in_vs[OF bellman_ford long_enough, of]
            calculation
    by (auto simp add: vwalk_bet_def bf_def bellman_ford_forward_def bellman_ford_init_algo_def bellman_ford_algo_def)
  hence t_prop:"prod.snd (the (connection_lookup bf t)) < PInfty"
    using knowledge(16) tt_dist_le_PInfty by blast
  have t_in_dom: "t \<in> dom (connection_lookup  bf)"
    using knowledge(3) vs_is_V by (auto simp add: bellman_ford.bellman_ford_init_dom_is[OF bellman_ford]
                       bellman_ford.same_domain_bellman_ford[OF bellman_ford]
                       bf_def bellman_ford_forward_def bellman_ford_init_algo_def bellman_ford_algo_def)
  hence pred_of_t_not_None: "prod.fst (the (connection_lookup bf t)) \<noteq> None"
    using t_prop knowledge(4) bellman_ford.bellman_ford_pred_non_infty_pres[OF bellman_ford, of s "length vs -1"]
    by(auto simp add: bf_def bellman_ford_forward_def 
         bellman_ford.invar_pred_non_infty_def[OF bellman_ford]
          bellman_ford_init_algo_def bellman_ford_algo_def)
  have Pbf_def:"Pbf = rev (bellford.search_rev_path s bf t)" 
    unfolding Pbf_def
    using vs_is_V  pred_of_t_not_None t_props
    apply(subst sym[OF arg_cong[of _ _ rev, OF bellford.function_to_partial_function, simplified]])
    by(auto simp add: bellman_ford_forward_def bf_def bellman_ford_algo_def 
                          bellman_ford_init_algo_def tt_is_t make_pairs_are 
                 intro!:  bf_fw.search_rev_path_dom_bellman_ford[OF no_neg_cycle_in_bf] )
  have weight_Pbf_snd: "weight (a_not_blocked state) 
          (a_current_flow state) Pbf = prod.snd (the (connection_lookup bf t))"
    unfolding Pbf_def
    using t_prop   vs_is_V  pred_of_t_not_None knowledge(2,3,4)
    by(fastforce simp add: bellman_ford_forward_def bf_def bellman_ford_init_algo_def bellman_ford_algo_def
                 intro!: bellman_ford.bellman_ford_search_rev_path_weight[OF 
                bellman_ford no_neg_cycle_in_bf, of bf s t])+
  hence weight_le_PInfty: "weight (a_not_blocked state) (a_current_flow state) Pbf < PInfty"
    using t_prop by auto
  have Pbf_opt_path: "bellman_ford.opt_vs_path vs
 (\<lambda>u v. prod.snd (get_edge_and_costs_forward (a_not_blocked state) (a_current_flow state) u v)) s t
 (rev (bellford.search_rev_path s bf t))"
   using t_prop  vs_is_V  pred_of_t_not_None knowledge(2,3,4)
   by (auto simp add: bellman_ford_forward_def bf_def bellman_ford_init_algo_def bellman_ford_algo_def
                 intro!: bellman_ford.computation_of_optimum_path[OF bellman_ford no_neg_cycle_in_bf])
  hence length_Pbf:"2 \<le> length Pbf"
    using pred_of_t_not_None knowledge(3) vs_is_V 
    unfolding Pbf_def bf_def bellman_ford_forward_def
    by(fastforce simp add: bellman_ford.opt_vs_path_def[OF bellman_ford]
      bellman_ford.vs_path_def[OF bellman_ford] Pbf_def
      intro: bf_fw.search_rev_path_dom_bellman_ford[OF no_neg_cycle_in_bf])+
  have "awalk UNIV (hd Pbf) (edges_of_vwalk Pbf) (last Pbf) \<and>
         weight (a_not_blocked state) (a_current_flow state) Pbf =
         ereal  (foldr (\<lambda>e. (+) (\<cc> e))
        (map (\<lambda>e. prod.fst (get_edge_and_costs_forward (a_not_blocked state) (a_current_flow state) (prod.fst e) (prod.snd e)))
               (edges_of_vwalk Pbf)) 0) \<and>
         (\<forall>e\<in>set (map (\<lambda>e. prod.fst (get_edge_and_costs_forward (a_not_blocked state) (a_current_flow state) (prod.fst e)
                         (prod.snd e)))
           (edges_of_vwalk Pbf)).
    a_not_blocked state (flow_network_spec.oedge e) \<and> 0 < cost_flow_network.rcap (a_current_flow state) e)"
    by(intro path_bf_flow_network_path[OF _ length_Pbf weight_le_PInfty refl]) simp
  hence Pbf_props: "awalk UNIV (hd Pbf) (edges_of_vwalk Pbf) (last Pbf)"
                   " weight (a_not_blocked state) (a_current_flow state) Pbf =
         ereal  (foldr (\<lambda>e. (+) (\<cc> e))
        (map (\<lambda>e. prod.fst (get_edge_and_costs_forward (a_not_blocked state) (a_current_flow state) (prod.fst e) (prod.snd e)))
               (edges_of_vwalk Pbf)) 0)"
                   "(\<And> e. e \<in> set (map (\<lambda>e. prod.fst (get_edge_and_costs_forward (a_not_blocked state) (a_current_flow state) (prod.fst e)
                         (prod.snd e)))
           (edges_of_vwalk Pbf)) \<Longrightarrow>
    a_not_blocked state (flow_network_spec.oedge e) \<and> 0 < cost_flow_network.rcap (a_current_flow state) e)"
    by auto
  have "map (to_edge \<circ>
         (\<lambda>e. prod.fst (local.get_edge_and_costs_forward (a_not_blocked state) (a_current_flow state) (prod.fst e)
                     (prod.snd e)))) (edges_of_vwalk Pbf) =
    edges_of_vwalk Pbf"
    apply(subst (2) sym[OF List.list.map_id[of "edges_of_vwalk Pbf"]])
    apply(rule map_ext)
    using cost_flow_network.to_vertex_pair.simps cost_flow_network.\<cc>.simps 
    by(auto intro:  map_ext simp add: to_edge_get_edge_and_costs_forward)
  hence same_edges:"(map cost_flow_network.to_vertex_pair PP) = (edges_of_vwalk Pbf)"
    by(auto simp add: PP_def)
  moreover have awalk_f:" awalk UNIV (fstv (hd PP)) (map cost_flow_network.to_vertex_pair PP) 
                           (sndv (last PP))"
    apply(rule edges_of_vwalk.elims [OF sym[OF same_edges]])
    using Pbf_props(1) same_edges length_Pbf awalk_fst_last bellman_ford.weight.simps[OF bellman_ford] 
           cost_flow_network.vs_to_vertex_pair_pres apply auto[2]
    using calculation  Pbf_props(1) same_edges 
    by(auto simp add: cost_flow_network.vs_to_vertex_pair_pres awalk_intros(1) 
                        arc_implies_awalk[OF UNIV_I refl]) 
    (metis awalk_fst_last last_ConsR last_map list.simps(3) list.simps(9))
  moreover have "PP \<noteq> []"
    using  edges_of_vwalk.simps(3) length_Pbf same_edges
    by(cases Pbf rule: list_cases3) auto
  ultimately have "cost_flow_network.prepath PP"
  by(auto simp add:cost_flow_network.prepath_def )
  moreover have Rcap_P:"0 < cost_flow_network.Rcap (a_current_flow state) (set PP)"
    using PP_def Pbf_props(3)
    by(auto simp add: cost_flow_network.Rcap_def)
  ultimately have "augpath (a_current_flow state) PP"
    by(auto simp add: cost_flow_network.augpath_def)
  moreover have "fstv (hd PP) = s" 
    using awalk_f same_edges Pbf_opt_path  awalk_ends[OF Pbf_props(1)] knowledge(4)
    by (force simp add: PP_def bellman_ford.opt_vs_path_def[OF bellman_ford]
                        bellman_ford.vs_path_def[OF bellman_ford] Pbf_def)
  moreover have "sndv (last PP) = t" 
    using awalk_f same_edges Pbf_opt_path  awalk_ends[OF Pbf_props(1)]  knowledge(4)
    by (force simp add: PP_def bellman_ford.opt_vs_path_def[OF bellman_ford]
                        bellman_ford.vs_path_def[OF bellman_ford] Pbf_def)
  moreover have oedge_of_p_allowed:"oedge ` (set PP) \<subseteq> to_set (actives state) \<union> \<F> state"
  proof(rule, rule ccontr, goal_cases)
    case (1 e)
    have "a_not_blocked state e"
      using map_in_set same_edges "1"(1) PP_def Pbf_props(3) list.set_map by blast
    thus ?case 
      using "1"(2) algo.from_underlying_invars'(20) knowledge(5) by force
  qed
  have distinct_Pbf: "distinct Pbf"
    using no_neg_cycle_in_bf knowledge(2,3,4) vs_is_V pred_of_t_not_None 
    unfolding Pbf_def bf_def 
    by (fastforce intro!: bellman_ford.search_rev_path_distinct[OF bellman_ford]
          simp add: bellman_ford_forward_def bf_def bellman_ford_init_algo_def bellman_ford_algo_def)
  have distinctP:"distinct PP" 
    using distinct_edges_of_vwalk[OF distinct_Pbf, simplified sym[OF same_edges ]]
          distinct_map by auto
  have qq_in_E:"set (map cost_flow_network.to_vertex_pair qq) \<subseteq> set es"
    using e_es by auto
  have qq_in_E':"set (map flow_network_spec.oedge qq) \<subseteq> \<E>" 
    using e_es' by auto
  have not_blocked_qq: "\<And> e . e \<in> set qq \<Longrightarrow> a_not_blocked state (oedge e)" 
    using  algo.from_underlying_invars'(20) e_in knowledge(5) by (fastforce simp add: \<F>_def)
  have rcap_qq: "\<And> e . e \<in> set qq \<Longrightarrow> cost_flow_network.rcap (a_current_flow state) e > 0" 
    using  cost_flow_network.augpath_rcap_pos_strict'[OF  qq_prop(1) ] knowledge by simp
  have awalk': "unconstrained_awalk (map cost_flow_network.to_vertex_pair qq)"
    by (meson unconstrained_awalk_def awalkE' is_a_walk)
  have bf_weight_leq_res_costs:"weight (a_not_blocked state) (a_current_flow state) 
                (awalk_verts s (map cost_flow_network.to_vertex_pair qq))
                \<le> foldr (\<lambda>x. (+) (\<cc> x)) qq 0" 
    using qq_in_E not_blocked_qq rcap_qq awalk' qq_len  e_es'
    by(auto intro!: bf_weight_leq_res_costs simp add:  \<E>_def \<E>_impl(1) \<E>_list_def  to_list(1))
  have oedge_of_EE: "flow_network_spec.oedge ` EEE = \<E>" 
    by (meson  cost_flow_network.oedge_on_\<EE>)
  have " flow_network_spec.oedge ` set PP \<subseteq> \<E>"
    using from_underlying_invars'(1,3)[OF knowledge(5)] oedge_of_p_allowed by blast
  hence P_in_E: "set PP \<subseteq> EEE"
    by (meson image_subset_iff cost_flow_network.o_edge_res subsetI) 
  have "(foldr (\<lambda>e. (+) (\<cc> e)) PP 0) \<le> foldr (\<lambda>x. (+) (\<cc> x)) Q 0"
    using  weight_Pbf_snd t_dist_le_qq_weight Pbf_props(2)[simplified sym[OF PP_def]]
           qq_prop(5) bf_weight_leq_res_costs
    by (smt (verit, best) leD le_ereal_less)
  moreover have "(foldr (\<lambda>e. (+) (\<cc> e)) PP 0) = cost_flow_network.\<CC> PP"
    unfolding cost_flow_network.\<CC>_def 
    by(subst distinct_sum, simp add: distinctP, meson add.commute)
  moreover have "(foldr (\<lambda>e. (+) (\<cc> e)) Q 0) = cost_flow_network.\<CC> Q"
    unfolding cost_flow_network.\<CC>_def 
    by(subst distinct_sum, simp add: Q_prop(5), meson add.commute)
  ultimately have P_min: "cost_flow_network.is_min_path (abstract_flow_map f) s t PP"
    using Q_min P_in_E  knowledge(11)  distinctP
    by(auto simp add: cost_flow_network.is_min_path_def 
              cost_flow_network.is_s_t_path_def)
  show ?thesis
    using P_min distinctP Rcap_P oedge_of_p_allowed  PP_is_P knowledge(9)
          t_props(1,2) by fastforce
  qed
qed

lemma path_flow_network_path_bf_backward:
  assumes e_weight:"\<And> e. e \<in> set pp \<Longrightarrow> prod.snd (get_edge_and_costs_backward nb f (fstv e) (sndv e)) < PInfty"
     and is_a_walk:"awalk UNIV s (map to_edge pp) tt" 
     and s_is_fstv: "s = fstv (hd pp)"
     and bellman_ford:"bellman_ford connection_empty connection_lookup connection_invar 
                                    connection_delete es vs (\<lambda> u v. prod.snd 
                                    (get_edge_and_costs_backward nb f u v)) connection_update"  
   shows "weight_backward nb f (awalk_verts s (map cost_flow_network.to_vertex_pair pp)) < PInfty"
  using assms(1,2)[simplified assms(3)]
proof(subst assms(3), induction pp  rule: list_induct3)
  case 1
  then show ?case 
    using  bellman_ford.weight.simps[OF bellman_ford] by auto
next
  case (2 x)
  then show ?case
    using  bellman_ford.weight.simps[OF bellman_ford] apply auto[1]
    apply(induction x rule: cost_flow_network.to_vertex_pair.induct)
    apply(simp add: cost_flow_network.to_vertex_pair.simps make_pairs_are 
                     bellman_ford.weight.simps[OF bellman_ford] make_pair_fst_snd
                     Instantiation.make_pair_def)+
    done
next
  case (3 e d es)
    have same_ends:"sndv e = fstv d"
    using 3(3)
    by(induction e rule: cost_flow_network.to_vertex_pair.induct)
      (auto intro: cost_flow_network.to_vertex_pair.induct[OF , of _ d]  
        simp add: bellman_ford.weight.simps[OF bellman_ford]  Awalk.awalk_simps make_pair_fst_snd 
                 cost_flow_network.vs_to_vertex_pair_pres(1) make_pairs_are Instantiation.make_pair_def)
  have "weight_backward nb f
        (awalk_verts (fstv (hd ((e # d # es)))) (map cost_flow_network.to_vertex_pair (e # d # es))) =
        prod.snd (get_edge_and_costs_backward nb f (fstv e) (sndv e))
        + weight_backward nb f (awalk_verts (fstv (hd (( d # es)))) (map cost_flow_network.to_vertex_pair (d # es)))"
      using same_ends
    by(induction e rule: cost_flow_network.to_vertex_pair.induct)
      (auto intro:  cost_flow_network.to_vertex_pair.induct[OF , of _ d]
           simp add:  bellman_ford.weight.simps[OF bellman_ford]
                  cost_flow_network.to_vertex_pair_fst_snd multigraph.make_pair)
    moreover have "prod.snd (get_edge_and_costs_backward nb f (fstv e) (sndv e)) < PInfty"
      using "3.prems"(1) by force
    moreover have "weight_backward nb f (awalk_verts (fstv (hd (( d # es)))) (map cost_flow_network.to_vertex_pair (d # es))) < PInfty"
          using 3(2,3)
          by(intro  3(1), auto intro: cost_flow_network.to_vertex_pair.induct[OF , of _ e] 
                 simp add: bellman_ford.weight.simps[OF bellman_ford] Awalk.awalk_simps(2)[of UNIV] 
                       cost_flow_network.vs_to_vertex_pair_pres(1))
    ultimately show ?case by simp
  qed

lemma path_bf_flow_network_path_backward:
  assumes True
     and len: "length pp \<ge> 2"
     and "weight_backward nb f pp < PInfty"
         "ppp = edges_of_vwalk pp"      
   shows "awalk UNIV  (last pp) (map prod.swap (rev ppp)) (hd pp) \<and>
            weight_backward nb f pp = foldr (\<lambda> e acc. \<cc> e + acc)
                  (map (\<lambda> e. (prod.fst (get_edge_and_costs_backward nb f (prod.snd e) (prod.fst e)))) (map prod.swap (rev ppp))) 0
              \<and> (\<forall> e \<in> set (map (\<lambda> e. (prod.fst (get_edge_and_costs_backward nb f (prod.snd e)(prod.fst e)))) (map prod.swap (rev ppp))).
                  nb (oedge e) \<and> cost_flow_network.rcap f e > 0)"
proof-
  have bellman_ford:"bellman_ford connection_empty connection_lookup connection_invar connection_delete
     es vs (\<lambda> u v. prod.snd (get_edge_and_costs_backward nb f u v)) connection_update"
    by (simp add: bellman_ford_backward)
  show ?thesis
  using assms(3-)
proof(induction pp arbitrary: ppp rule: list_induct3_len_geq_2)
  case 1
  then show ?case
    using len by simp
next
  case (2 x y)
  have "awalk UNIV (last [x, y]) (map prod.swap (rev ppp)) (hd [x, y])"
    using 2     unfolding get_edge_and_costs_forward_def Let_def
    by (auto simp add: arc_implies_awalk bellman_ford.weight.simps[OF bellman_ford] 
           split: if_split prod.split)
  moreover have "weight_backward nb f [x, y] =
    ereal
     (foldr (\<lambda>e. (+) (\<cc> e)) (map (\<lambda>e. prod.fst (get_edge_and_costs_backward nb f (prod.snd e) (prod.fst e)))
     (map prod.swap (rev ppp))) 0)" 
    using "2.prems"(1)  
    by(auto simp add: es_sym[of "(y,x)"] bellman_ford.weight.simps[OF bellman_ford] 2(2) get_edge_and_costs_backward_result_props)
    moreover have "(\<forall>e\<in>set (map (\<lambda>e. prod.fst (get_edge_and_costs_backward nb f (prod.snd e) (prod.fst e))) (map prod.swap (rev ppp))).
        nb (flow_network_spec.oedge e) \<and> 0 < cost_flow_network.rcap f e)"
      using 2  get_edge_and_costs_backward_result_props[OF prod.collapse[symmetric] _ refl, of nb f x y]
      by auto
    ultimately show ?case by simp
next
  case (3 x y xs)
  thm 3(1)[OF _ refl]
  have "awalk UNIV (last (x # y # xs)) (map prod.swap (rev ppp)) (hd (x # y # xs))"
    using "3.IH" "3.prems"(1) "3.prems"(2) Awalk.awalk_simps(2) 
           bellman_ford.weight.simps(3)[OF bellman_ford ] edges_of_vwalk.simps(3)
    by (auto simp add: arc_implies_awalk)
    
  moreover have " weight_backward nb f (x # y # xs) =   prod.snd (get_edge_and_costs_backward nb f x y) +
                                       weight_backward nb f (y # xs)"
    using bellman_ford bellman_ford.weight.simps(3) by fastforce
  moreover have "weight_backward nb f (y # xs) =
ereal
 (foldr (\<lambda>e. (+) (\<cc> e))
   (map (\<lambda>e. prod.fst (get_edge_and_costs_backward nb f (prod.snd e) (prod.fst e))) 
                (map prod.swap (rev (edges_of_vwalk (y # xs))))) 0)"
    using "3.IH" "3.prems"(1) calculation(2) by fastforce
  moreover have "prod.snd (get_edge_and_costs_backward nb f x y) = 
                  \<cc> (prod.fst (get_edge_and_costs_backward nb f x y))"
      using 3  get_edge_and_costs_backward_result_props[OF prod.collapse[symmetric] _ refl, of nb f x y]
      by auto
  moreover have "(\<forall>e\<in>set (map (\<lambda>e. prod.fst (get_edge_and_costs_backward nb f (prod.snd e) (prod.fst e)))
                        (map prod.swap (rev (edges_of_vwalk (y # xs))))).
    nb (flow_network_spec.oedge e) \<and> 0 < cost_flow_network.rcap f e)" 
    by (simp add: "3.IH" calculation(3))
  moreover have "nb (flow_network_spec.oedge (prod.fst (get_edge_and_costs_backward nb f x y)))"
     using 3  get_edge_and_costs_backward_result_props[OF prod.collapse[symmetric] _ refl, of nb f x y]
      by auto
  moreover have "0 < cost_flow_network.rcap f  (prod.fst (get_edge_and_costs_backward nb f x y))"
     using 3  get_edge_and_costs_backward_result_props[OF prod.collapse[symmetric] _ refl, of nb f x y]
      by auto
  ultimately show ?case
    by (auto simp add: 3(3)  foldr_plus_add_right[where b = 0, simplified]) 
qed
qed

lemma edges_of_vwalk_rev_swap:"(map prod.swap (rev (edges_of_vwalk c))) = edges_of_vwalk (rev c)"
  apply(induction c rule: edges_of_vwalk.induct, simp, simp)
  subgoal for x y rest
    using edges_of_vwalk_append_2[of "[y,x]"] 
    by auto
  done

lemma no_neg_cycle_in_bf_backward: 
  assumes "invar_isOptflow state" "underlying_invars state"
  shows   "\<nexists>c. weight_backward (a_not_blocked state) (a_current_flow state) c < 0 \<and> hd c = last c"
proof(rule nexistsI, goal_cases)
  case (1 c)
  have bellman_ford:"bellman_ford  connection_empty connection_lookup 
                 connection_invar connection_delete
     es vs (\<lambda> u v. prod.snd (get_edge_and_costs_backward (a_not_blocked state) (a_current_flow state) u v)) connection_update"
    by (simp add: bellman_ford_backward)
  have length_c: "length c \<ge> 2"
    using 1 bellman_ford.weight.simps[OF bellman_ford] 
    by(cases c rule: list_cases3) auto
  have weight_le_PInfty:"weight_backward (a_not_blocked state) (a_current_flow state) c < PInfty" 
    using "1"(1) by fastforce
  have path_with_props:"awalk UNIV (last c) (map prod.swap (rev (edges_of_vwalk c))) (hd c)"
       " weight_backward (a_not_blocked state) (a_current_flow state) c =
  ereal
   (foldr (\<lambda>e. (+) (\<cc> e))
     (map (\<lambda>e. prod.fst (get_edge_and_costs_backward (a_not_blocked state) (a_current_flow state) (prod.snd e) (prod.fst e)))
       (map prod.swap (rev (edges_of_vwalk c))))
     0)"
      "(\<And> e. e\<in>set (map (\<lambda>e. prod.fst (get_edge_and_costs_backward (a_not_blocked state) (a_current_flow state) (prod.snd e) (prod.fst e)))
             (map prod.swap (rev (edges_of_vwalk c)))) \<Longrightarrow>
      a_not_blocked state (flow_network_spec.oedge e) \<and> 0 < cost_flow_network.rcap (a_current_flow state) e)"
    using path_bf_flow_network_path_backward[OF _ length_c weight_le_PInfty refl] by auto
  define cc where "cc = (map (\<lambda>e. prod.fst (get_edge_and_costs_backward (a_not_blocked state) (a_current_flow state) (prod.snd e) (prod.fst e)))
       (map prod.swap (rev (edges_of_vwalk c))))"
  have same_edges:"(map cost_flow_network.to_vertex_pair cc) = (map prod.swap (rev (edges_of_vwalk c)))"
    using to_edge_get_edge_and_costs_backward by (force simp add: cc_def)
  have c_non_empt:"cc \<noteq> []"
    using path_with_props(1)  "1"(1) awalk_fst_last bellman_ford.weight.simps[OF bellman_ford] 
           cost_flow_network.vs_to_vertex_pair_pres 
    by (auto intro:  edges_of_vwalk.elims[OF  sym[OF same_edges[simplified edges_of_vwalk_rev_swap]]])
  moreover have awalk_f:" awalk UNIV (fstv (hd cc)) (map cost_flow_network.to_vertex_pair cc) (sndv (last cc))"
    apply(rule edges_of_vwalk.elims [OF sym[OF same_edges[simplified edges_of_vwalk_rev_swap]]])
    using path_with_props(1) same_edges 
    using "1"(1) awalk_fst_last bellman_ford.weight.simps[OF bellman_ford] 
           apply auto[2]
    using calculation  path_with_props(1) same_edges 
    by (auto simp add: cost_flow_network.vs_to_vertex_pair_pres awalk_intros(1) 
                        arc_implies_awalk[OF UNIV_I refl]) 
       (metis awalk_fst_last last_ConsR last_map list.simps(3) list.simps(9))
  ultimately have "cost_flow_network.prepath cc"
    using prepath_def by blast
  moreover have "0 < cost_flow_network.Rcap (a_current_flow state) (set cc)"
    using cc_def path_with_props(3)
    by(auto simp add: cost_flow_network.Rcap_def)
  ultimately have agpath:"augpath (a_current_flow state) cc"
    by(simp add: augpath_def)
  have cc_in_E: "set cc \<subseteq> EEE"
  proof(rule, rule ccontr, goal_cases)
    case (1 e) 
    hence "to_edge e \<in> set (edges_of_vwalk (rev c))"
      by (metis map_in_set same_edges[simplified edges_of_vwalk_rev_swap])
    then obtain c1 c2 where c_split:"c1@[prod.fst (to_edge e)]@[prod.snd (to_edge e)]@c2 = rev c" 
      apply(induction e rule: cost_flow_network.to_vertex_pair.induct)
      subgoal for e
        using edges_in_vwalk_split[of "fst e" "snd e" "rev c"]  multigraph.make_pair' 
        by (auto simp add: Instantiation.make_pair_def)
      subgoal for e
        using edges_in_vwalk_split[of "snd e" "fst e" "rev c"]  multigraph.make_pair' 
        by (auto simp add: Instantiation.make_pair_def)
    done
  have c_split:"rev c2@[prod.snd (to_edge e)]@[prod.fst (to_edge e)]@ rev c1 = c" 
    apply(subst sym[OF rev_rev_ident[of c]])
    apply(subst sym[OF c_split]) 
    by simp
  have le_infty:"prod.snd (get_edge_and_costs_backward (a_not_blocked state) (a_current_flow state) (prod.snd (to_edge e))
             (prod.fst (to_edge e))) < PInfty"
  proof(rule ccontr, goal_cases)
    case 1
    hence "prod.snd (get_edge_and_costs_backward (a_not_blocked state) (a_current_flow state) (prod.snd (cost_flow_network.to_vertex_pair e))
           (prod.fst (cost_flow_network.to_vertex_pair e)))
     = PInfty" by simp
    hence "weight_backward (a_not_blocked state) (a_current_flow state) c = PInfty"
      using bellman_ford.edge_and_Costs_none_pinfty_weight[OF bellman_ford]
            c_split by auto
    thus False
      using weight_le_PInfty by force
  qed
  have one_not_blocked:"a_not_blocked state (oedge e)"
    using less_PInfty_not_blocked  "1"(1) cc_def path_with_props(3) by blast
  hence "oedge e \<in> \<E>"
    using assms(2) 
    by(auto elim!: algo.underlying_invarsE algo.inv_unbl_iff_forest_activeE algo.inv_actives_in_EE algo.inv_forest_in_EE)
  thus ?case
    using  1(2) cost_flow_network.o_edge_res by blast
qed
  obtain C where "augcycle (a_current_flow state) C"
    apply(rule cost_flow_network.augcycle_from_non_distinct_cycle[OF  agpath])
    using "1"(1) awalk_f c_non_empt awalk_fst_last[OF _ awalk_f]
          awalk_fst_last[OF _ path_with_props(1)]  cc_in_E  "1"(1) cc_def path_with_props(2)
    by (auto, metis list.map_comp same_edges)
  then show ?case 
    using assms(1) invar_isOptflow_def cost_flow_network.min_cost_flow_no_augcycle by blast
qed

lemma to_edge_of_get_edge_and_costs_backward:
 "cost_flow_network.to_vertex_pair (prod.fst (get_edge_and_costs_backward (not_blocked state)
         (current_flow state) a b)) = (b, a)"
  using to_edge_get_edge_and_costs_backward by force

lemma get_source_for_target_ax:
 "\<lbrakk>b = balance state; \<gamma> = current_\<gamma> state; f = current_flow state; Some t = get_target state;
   get_source_target_path_b state t = Some (s,P); invar_gamma state; invar_isOptflow state;
   underlying_invars state\<rbrakk>
   \<Longrightarrow> s \<in> VV \<and> (abstract_bal_map b) s > \<epsilon> * \<gamma> \<and> resreach (abstract_flow_map f) s t \<and> s \<noteq> t"
 proof( goal_cases)
  case 1
  note one = this
  have t_prop: "t \<in> \<V>" "- (1 - local.\<epsilon>) * \<gamma> > abstract_bal_map b t"
 using get_target_axioms_red(1)[OF 1(1,2,4)] by auto
 define bf where  "bf = bellman_ford_backward (a_not_blocked state) (a_current_flow state) t"
  define ss_opt where "ss_opt = (get_source_for_target_aux_aux bf 
                     (\<lambda> v. abstract_real_map (bal_lookup (balance state)) v)
                                           (current_\<gamma> state) vs)"
  show ?thesis
  proof(cases ss_opt)
    case None
    hence "get_source_target_path_b state t = None"
      by(auto simp add: option_none_simp[of "get_source_for_target_aux_aux _ _ _ _"] 
                 algo.abstract_not_blocked_map_def option.case_eq_if 
                   ss_opt_def bf_def get_source_target_path_b_def)   
    hence False
      using 1 by simp
    thus ?thesis by simp
  next
    case (Some a)
  define ss where "ss = the ss_opt"
  define Pbf where "Pbf = search_rev_path_exec t bf ss"
  define PP where "PP = map (\<lambda>e. prod.fst (get_edge_and_costs_backward (a_not_blocked state) (a_current_flow state)
                                  (prod.snd e) (prod.fst e)))
                   (edges_of_vwalk Pbf)"
  have ss_opt_ss:"ss_opt = Some ss"
    by (simp add: Some ss_def)
  have "Some (ss, PP) = Some (s, P)"
    using 1
    by(cases ss_opt)
      (auto simp add: option_none_simp[of "get_source_for_target_aux_aux _ _ _ _"] 
                 algo.abstract_not_blocked_map_def option.case_eq_if 
                   ss_opt_def bf_def get_source_target_path_b_def ss_def
                   PP_def Pbf_def pair_to_realising_redge_backward_def)
  hence ss_is_s: "ss = s" and PP_is_P: "PP = P" by auto 
  have s_props: "ss \<in> set local.vs"
     "a_balance state ss > local.\<epsilon> * current_\<gamma> state"
     "prod.snd (the (connection_lookup bf ss)) < PInfty"
    using get_source_for_target_aux_aux(2)[of bf "a_balance state" "current_\<gamma> state" vs]
           Some
    by(auto simp add: ss_def ss_opt_def)
   have bellman_ford:"bellman_ford connection_empty connection_lookup connection_invar connection_delete
     es vs (\<lambda> u v. prod.snd (get_edge_and_costs_backward (a_not_blocked state) (a_current_flow state) u v)) connection_update"
      using bellman_ford_backward by blast
   define connections where "connections = 
          (bellman_ford_backward (a_not_blocked state) (a_current_flow state) t)"
   have ss_dist_le_PInfty:"prod.snd (the (connection_lookup connections ss)) < PInfty"
     using bf_def connections_def s_props(3) by blast
  have s_prop:"a_balance state s > \<epsilon> * current_\<gamma> state \<and>
         s \<in> set vs \<and> prod.snd (the (connection_lookup connections s)) < PInfty"
    using s_props by(auto simp add: ss_is_s connections_def  bf_def)
  have s_neq_t: "s \<noteq> t"
    using t_prop s_prop "1"(1) "1"(2) invar_gamma_def
    by (smt (verit, best) "1"(6) mult_minus_left mult_mono')
  have s_in_dom: "s \<in> dom (connection_lookup  connections)"
    using s_prop
    by (auto simp add: bellman_ford.bellman_ford_init_dom_is[OF bellman_ford]
                       bellman_ford.same_domain_bellman_ford[OF bellman_ford]
                       connections_def bellman_ford_backward_def
                       bellman_ford_init_algo_def bellman_ford_algo_def)
  hence pred_of_s_not_None: "prod.fst (the (connection_lookup connections s)) \<noteq> None"
    using s_neq_t s_prop bellman_ford.bellman_ford_pred_non_infty_pres[OF bellman_ford, of t "length vs -1"]
    by(simp add:  connections_def bellman_ford_backward_def 
         bellman_ford.invar_pred_non_infty_def[OF bellman_ford]
         bellman_ford_init_algo_def bellman_ford_algo_def) 
  define Pbf where "Pbf =  rev (bellman_ford_spec.search_rev_path connection_lookup t connections s)"
  have no_neg_cycle_in_bf: "\<nexists>c. weight_backward (a_not_blocked state) (a_current_flow state) c < 0 \<and> hd c = last c"
    using "1"(7,8) no_neg_cycle_in_bf_backward by blast
  have "weight_backward (a_not_blocked state)  
          (a_current_flow state) Pbf = prod.snd (the (connection_lookup connections s))"
    unfolding Pbf_def
    using s_prop  s_neq_t  t_prop vs_is_V  pred_of_s_not_None 1(7,8)
    by(fastforce simp add: bellman_ford_backward_def connections_def
                bellman_ford_init_algo_def bellman_ford_algo_def make_pairs_are 
                 intro!: bellman_ford.bellman_ford_search_rev_path_weight[OF 
                bellman_ford no_neg_cycle_in_bf, of connections t s]) +
  hence weight_le_PInfty: "weight_backward (a_not_blocked state) (a_current_flow state) Pbf < PInfty"
    using s_prop by auto
  have Pbf_opt_path: "bellman_ford.opt_vs_path vs
       (\<lambda>u v. prod.snd (get_edge_and_costs_backward (a_not_blocked state) (a_current_flow state) u v)) t s
       (rev (bellford.search_rev_path t connections s))"
    using t_prop  s_neq_t  s_prop(1) vs_is_V  pred_of_s_not_None 
    by (auto simp add: bellman_ford_backward_def connections_def bellman_ford_algo_def 
                       bellman_ford_init_algo_def make_pairs_are 
                 intro!: bellman_ford.computation_of_optimum_path[OF bellman_ford no_neg_cycle_in_bf])
  hence length_Pbf:"2 \<le> length Pbf" 
    by(auto simp add: bellman_ford.opt_vs_path_def[OF bellman_ford]
      bellman_ford.vs_path_def[OF bellman_ford] Pbf_def)
  have Pbf_props: "awalk UNIV (last Pbf) (map prod.swap (rev (edges_of_vwalk Pbf))) (hd Pbf)"
                   "weight_backward (a_not_blocked state) (a_current_flow state) Pbf =
   ereal
   (foldr (\<lambda>e. (+) (\<cc> e))
     (map (\<lambda>e. prod.fst (get_edge_and_costs_backward (a_not_blocked state) (a_current_flow state) (prod.snd e) (prod.fst e)))
       (map prod.swap (rev (edges_of_vwalk Pbf))))
     0)"
    "(\<And> e. e  \<in>set (map (\<lambda>e. prod.fst (get_edge_and_costs_backward (a_not_blocked state) (a_current_flow state) (prod.snd e) (prod.fst e)))
             (map prod.swap (rev (edges_of_vwalk Pbf)))) \<Longrightarrow>
      a_not_blocked state (flow_network_spec.oedge e) \<and> 0 < cost_flow_network.rcap (a_current_flow state) e)"
    using path_bf_flow_network_path_backward[OF _ length_Pbf weight_le_PInfty refl] by auto
  define P where "P = (map (\<lambda>e. prod.fst (get_edge_and_costs_backward (a_not_blocked state) (a_current_flow state) (prod.snd e) (prod.fst e)))
             (map prod.swap (rev (edges_of_vwalk Pbf))))"
  have same_edges:"(map cost_flow_network.to_vertex_pair P) = (map prod.swap (rev (edges_of_vwalk Pbf)))"
     using to_edge_get_edge_and_costs_forward 
     by (auto simp add: get_edge_and_costs_forward_def P_def get_edge_and_costs_backward_def )
   moreover have awalk_f:
   "awalk UNIV (fstv (hd P)) (map cost_flow_network.to_vertex_pair P) (sndv (last P))"
    apply(rule edges_of_vwalk.elims [OF sym[OF same_edges[simplified edges_of_vwalk_rev_swap]]])
    using Pbf_props(1) same_edges length_Pbf  "1"(1) awalk_fst_last bellman_ford.weight.simps[OF bellman_ford] 
           cost_flow_network.vs_to_vertex_pair_pres apply auto[2]
    using calculation  Pbf_props(1) same_edges 
    by(auto simp add: cost_flow_network.vs_to_vertex_pair_pres awalk_intros(1) 
                        arc_implies_awalk[OF UNIV_I refl]) 
       (metis awalk_fst_last last_ConsR last_map list.simps(3) list.simps(9))
  moreover have "P \<noteq> []"
    using  edges_of_vwalk.simps(3) length_Pbf same_edges
    by(cases Pbf rule: list_cases3) auto
  ultimately have "cost_flow_network.prepath P"
  by(auto simp add:cost_flow_network.prepath_def )
  moreover have "0 < cost_flow_network.Rcap (a_current_flow state) (set P)"
    using P_def Pbf_props(3)
    by(auto simp add: cost_flow_network.Rcap_def)
  ultimately have "augpath (a_current_flow state) P"
    by(auto simp add: cost_flow_network.augpath_def)
  moreover have "fstv (hd P) = s" 
    using awalk_f same_edges Pbf_opt_path  awalk_ends[OF Pbf_props(1)] s_neq_t
          P_def bellman_ford.opt_vs_path_def[OF bellman_ford]
                        bellman_ford.vs_path_def[OF bellman_ford] Pbf_def
    by (metis (no_types, lifting))  
  moreover have "sndv (last P) = t" 
    using awalk_f same_edges Pbf_opt_path  awalk_ends[OF Pbf_props(1)] s_neq_t
    using P_def bellman_ford.opt_vs_path_def[OF bellman_ford]
                        bellman_ford.vs_path_def[OF bellman_ford] Pbf_def
    by (metis (no_types, lifting)) 
  moreover have "set P \<subseteq> EEE"
  proof(rule, rule ccontr, goal_cases)
    case (1 e)
    hence "to_edge e \<in> set ( (edges_of_vwalk ( (rev Pbf))))"
      by (metis map_in_set same_edges edges_of_vwalk_rev_swap)
    then obtain c1 c2 where c_split:"c1@[prod.fst (to_edge e)]@[prod.snd (to_edge e)]@c2 = rev Pbf" 
      apply(induction e rule: cost_flow_network.to_vertex_pair.induct)
      subgoal for e
        using edges_in_vwalk_split[of "fst e" "snd e" "rev Pbf"]  multigraph.make_pair' 
        by (auto simp add: Instantiation.make_pair_def)
      subgoal for e
        using edges_in_vwalk_split[of "snd e" "fst e" "rev Pbf"] multigraph.make_pair' 
        by (auto simp add: Instantiation.make_pair_def)
      done
  have c_split:"rev c2@[prod.snd (to_edge e)]@[prod.fst (to_edge e)]@ rev c1 = Pbf" 
    apply(subst sym[OF rev_rev_ident[of Pbf]])
    apply(subst sym[OF c_split]) 
    by simp
  have le_infty:"prod.snd (get_edge_and_costs_backward (a_not_blocked state) (a_current_flow state) (prod.snd (to_edge e))
             (prod.fst (to_edge e))) < PInfty"
  proof(rule ccontr, goal_cases)
    case 1
    hence "prod.snd (get_edge_and_costs_backward (a_not_blocked state) 
           (a_current_flow state) (prod.snd (cost_flow_network.to_vertex_pair e))
           (prod.fst (cost_flow_network.to_vertex_pair e)))
            = PInfty" by simp
    hence "weight_backward (a_not_blocked state) (a_current_flow state) Pbf = PInfty"
      using bellman_ford.edge_and_Costs_none_pinfty_weight[OF bellman_ford]
            c_split by auto
    thus False
      using weight_le_PInfty by force
  qed
  have one_not_blocked:"a_not_blocked state (oedge e)"
    using less_PInfty_not_blocked  "1"(1) P_def Pbf_props(3) by blast
  hence "oedge e \<in> \<E>"
    using one
    by(auto elim!: algo.underlying_invarsE algo.inv_unbl_iff_forest_activeE 
                   algo.inv_actives_in_EE algo.inv_forest_in_EE)
  thus ?case 
    using "1"(2)  cost_flow_network.o_edge_res by blast
  qed
  ultimately have "resreach (abstract_flow_map f) s t"
    using cost_flow_network.augpath_imp_resreach 1(3) by fast  
  thus ?thesis
    using one(1,2) s_neq_t s_prop vs_is_V by blast
 qed
qed

lemma bf_weight_backward_leq_res_costs:
 assumes "set (map flow_network_spec.oedge qq) \<subseteq> \<E>"
         "\<And> e. e \<in> set qq \<Longrightarrow> a_not_blocked state (flow_network_spec.oedge e)"
         "\<And> e. e \<in> set qq \<Longrightarrow> 0 < cost_flow_network.rcap (a_current_flow state) e"
         "unconstrained_awalk (map cost_flow_network.to_vertex_pair qq)"
    and  qq_len: "length qq \<ge> 1"
   shows "weight_backward (a_not_blocked state) (a_current_flow state) 
          (awalk_verts s (map prod.swap (rev (map cost_flow_network.to_vertex_pair qq))))
           \<le> foldr (\<lambda>x. (+) (\<cc> x)) qq 0" 
  using assms
proof(induction qq arbitrary: s rule: list_induct2_len_geq_1)
  case 1
  then show ?case 
    using qq_len by blast
next 
  case (2 e)
  show ?case
    using 2
    by(induction e rule: cost_flow_network.to_vertex_pair.induct) 
    (auto intro!: conjunct1[OF get_edge_and_costs_backward_makes_cheaper[OF 
                                  refl, of _ "a_not_blocked state" "a_current_flow state"]] 
                     intro: surjective_pairing prod.collapse
           simp add: \<E>_def \<E>_impl(1) \<E>_list_def to_list(1) make_pair_fst_snd make_pairs_are
                     Instantiation.make_pair_def
           simp del: cost_flow_network.\<cc>.simps)+
 next
   case (3 e d ds)
   have help1: 
  "weight_backward (a_not_blocked state) (a_current_flow state)
     (butlast (awalk_verts s (map (prod.swap \<circ> to_edge) (rev ds) @ [(snd ee, fst ee)])) @ [snd dd]) +
    prod.snd (local.get_edge_and_costs_backward (a_not_blocked state) (a_current_flow state) (snd dd) (fst dd))
    \<le> ereal (local.\<c> dd + (local.\<c> ee + foldr (\<lambda>x. (+) (\<cc> x)) ds 0))" 
  if assms:"(\<And>s. unconstrained_awalk ((fst ee, snd ee) # map to_edge ds) \<Longrightarrow>
          weight_backward (a_not_blocked state) (a_current_flow state)
           (awalk_verts s (map (prod.swap \<circ> to_edge) (rev ds) @ [(snd ee, fst ee)]))
          \<le> ereal (local.\<c> ee + foldr (\<lambda>x. (+) (\<cc> x)) ds 0))"
    "(\<And>e. e = F dd \<or> e = F ee \<or> e \<in> set ds \<Longrightarrow>
          a_not_blocked state (oedge e))"
    "(\<And>e. e = F dd \<or> e = F ee \<or> e \<in> set ds \<Longrightarrow>
          0 < rcap (a_current_flow state) e)"
    "unconstrained_awalk ((fst dd, snd dd) # (fst ee, snd ee) # map to_edge ds)"
    "dd \<in> local.\<E> " "ee \<in> local.\<E> " "oedge ` set ds \<subseteq> local.\<E>"
   for ee dd
     using assms unconstrained_awalk_snd_verts_eq  unconstrained_awalk_drop_hd[of "(fst _, snd _)" "(fst _, snd _)#map to_edge _"]
        by(subst ereal_add_homo[of _ "_ + _ "], subst add.commute) 
          (fastforce intro!: add_mono[OF conjunct1[OF get_edge_and_costs_backward_makes_cheaper[OF 
                                  refl, of _ "a_not_blocked state" "a_current_flow state", of "F _", simplified]]] prod.collapse simp add: awalk_verts_append_last')
      have help2: "weight_backward (a_not_blocked state) (a_current_flow state)
     (butlast (awalk_verts s (map (prod.swap \<circ> to_edge) (rev ds) @ [(fst ee, snd ee)])) @ [snd dd]) +
    prod.snd (local.get_edge_and_costs_backward (a_not_blocked state) (a_current_flow state) (snd dd) (fst dd))
    \<le> ereal (local.\<c> dd + (foldr (\<lambda>x. (+) (\<cc> x)) ds 0 - local.\<c> ee))"
        if assms: "(\<And>s. unconstrained_awalk ((snd ee, fst ee) # map to_edge ds) \<Longrightarrow>
          weight_backward (a_not_blocked state) (a_current_flow state)
           (awalk_verts s (map (prod.swap \<circ> to_edge) (rev ds) @ [(fst ee, snd ee)]))
          \<le> ereal (foldr (\<lambda>x. (+) (\<cc> x)) ds 0 - local.\<c> ee))"
         "(\<And>e. e = F dd \<or> e = B ee \<or> e \<in> set ds \<Longrightarrow> a_not_blocked state (oedge e))"
         "(\<And>e. e = F dd \<or> e = B ee \<or> e \<in> set ds \<Longrightarrow> 0 < rcap (a_current_flow state) e)"
         " unconstrained_awalk ((fst dd, snd dd) # (snd ee, fst ee) # map to_edge ds)"
         "dd \<in> local.\<E>" "ee \<in> local.\<E>"
         "oedge ` set ds \<subseteq> local.\<E>" for dd ee
        using assms
        using unconstrained_awalk_snd_verts_eq  unconstrained_awalk_drop_hd[of "(fst _, snd _)" "(snd _, fst _)#map to_edge _"]
        by(subst ereal_add_homo[of _ "_ _ _ "], subst add.commute)
          (fastforce intro!: add_mono[OF conjunct1[OF get_edge_and_costs_backward_makes_cheaper[OF 
                                  refl, of _ "a_not_blocked state" "a_current_flow state", of "F _", simplified]]] prod.collapse simp add: awalk_verts_append_last')
      have help3: "   weight_backward (a_not_blocked state) (a_current_flow state)
     (butlast (awalk_verts s (map (prod.swap \<circ> to_edge) (rev ds) @ [(snd ee, fst ee)])) @ [fst dd]) +
    prod.snd (local.get_edge_and_costs_backward (a_not_blocked state) (a_current_flow state) (fst dd) (snd dd))
    \<le> ereal (local.\<c> ee + foldr (\<lambda>x. (+) (\<cc> x)) ds 0 - local.\<c> dd)"
        if assms: "(\<And>s. unconstrained_awalk ((fst ee, snd ee) # map to_edge ds) \<Longrightarrow>
          weight_backward (a_not_blocked state) (a_current_flow state)
           (awalk_verts s (map (prod.swap \<circ> to_edge) (rev ds) @ [(snd ee, fst ee)]))
          \<le> ereal (local.\<c> ee + foldr (\<lambda>x. (+) (\<cc> x)) ds 0))"
          "(\<And>e. e = B dd \<or> e = F ee \<or> e \<in> set ds \<Longrightarrow>
          a_not_blocked state (oedge e))"
          "(\<And>e. e = B dd \<or> e = F ee \<or> e \<in> set ds \<Longrightarrow>
          0 < rcap (a_current_flow state) e)"
          "unconstrained_awalk ((snd dd, fst dd) # (fst ee, snd ee) # map to_edge ds)"
          "dd \<in> local.\<E>" "ee \<in> local.\<E> " "oedge ` set ds \<subseteq> local.\<E>" for ee dd
        apply(rule forw_subst[of _ "ereal ((- \<c> dd) + (\<c> ee + (foldr (\<lambda>x. (+) (\<cc> x)) ds 0 )))"], simp)
        using unconstrained_awalk_snd_verts_eq[of "snd _" "fst dd" "fst ee" "snd ee"]
        using unconstrained_awalk_drop_hd[of "(snd _, fst _)" "(fst _, snd _)#map to_edge _"] 
        using awalk_verts_append_last'[of _ _"snd _" "fst ee"] assms
        using unconstrained_awalk_drop_hd[of "(snd _, fst _)" "(fst _, snd _)#map to_edge _"] 
        by (subst ereal_add_homo[of "_" "(_ + _)"], subst add.commute)
           (fastforce intro: prod.collapse
                      intro!: add_mono[OF conjunct1[OF get_edge_and_costs_backward_makes_cheaper[OF 
                                  refl, of _ "a_not_blocked state" "a_current_flow state", of "B _", simplified]]])
      have help4: "  weight_backward (a_not_blocked state) (a_current_flow state)
           (butlast (awalk_verts s (map (prod.swap \<circ> to_edge) (rev ds) @ [(fst ee, snd ee)])) @ [fst dd]) +
          prod.snd (local.get_edge_and_costs_backward (a_not_blocked state) (a_current_flow state) (fst dd) (snd dd))
         \<le> ereal (foldr (\<lambda>x. (+) (\<cc> x)) ds 0 - local.\<c> ee - local.\<c> dd)" if assms:
         "(\<And>s. unconstrained_awalk ((snd ee, fst ee) # map to_edge ds) \<Longrightarrow>
          weight_backward (a_not_blocked state) (a_current_flow state)
           (awalk_verts s (map (prod.swap \<circ> to_edge) (rev ds) @ [(fst ee, snd ee)]))
          \<le> ereal (foldr (\<lambda>x. (+) (\<cc> x)) ds 0 - local.\<c> ee))"
         "(\<And>e. e = B dd \<or> e = B ee \<or> e \<in> set ds \<Longrightarrow> a_not_blocked state (oedge e)) "
         " (\<And>e. e = B dd \<or> e = B ee \<or> e \<in> set ds \<Longrightarrow> 0 < rcap (a_current_flow state) e)"
         "unconstrained_awalk ((snd dd, fst dd) # (snd ee, fst ee) # map to_edge ds)"
          "dd \<in> local.\<E> ""ee \<in> local.\<E> "  "oedge ` set ds \<subseteq> local.\<E> " for dd ee
        apply(rule forw_subst[of _ "ereal ((- \<c> dd) + (- \<c> ee + (foldr (\<lambda>x. (+) (\<cc> x)) ds 0 )))"], simp)
        using unconstrained_awalk_snd_verts_eq[of "snd dd" "fst dd" "snd ee" "fst ee"]
        using unconstrained_awalk_drop_hd[of "(snd dd, fst dd)" "(snd ee, fst ee)#map to_edge _"] 
        using awalk_verts_append_last'[of _ _"fst _" "snd ee"] assms
        using unconstrained_awalk_drop_hd[of "(snd _, fst _)" "(snd _, fst _)#map to_edge _"] 
        by (subst ereal_add_homo[of "_" "(_ + _)"], subst add.commute)
           (fastforce intro: prod.collapse
                      intro!: add_mono[OF conjunct1[OF get_edge_and_costs_backward_makes_cheaper[OF 
                                  refl, of _ "a_not_blocked state" "a_current_flow state", of "B _", simplified]]]) 
   show ?case
 using 3
  by(induction e rule: cost_flow_network.to_vertex_pair.induct, 
    all \<open>induction d rule: cost_flow_network.to_vertex_pair.induct\<close>) 
    (auto simp add: make_pair_fst_snd rev_map awalk_verts_append_last[of _ "_@[_]" "_ _" "_ _", simplified] 
                    sym[OF bellman_ford.costs_last[OF bellman_ford_backward]] make_pairs_are 
                    Instantiation.make_pair_def
             intro: help1 help2 help3 help4)
qed

lemma Forest_conv_erev: 
  assumes "cost_flow_network.consist forst conv" "symmetric_digraph forst"
          "\<And> e. e \<in> forst \<Longrightarrow> prod.fst e \<noteq> prod.snd e"
   shows  "e \<in> conv ` forst \<longleftrightarrow> cost_flow_network.erev e \<in> conv ` forst"
proof(rule cost_flow_network.consistE[OF assms(1)], rule symmetric_digraphE[OF assms(2)], rule, 
      all \<open>cases e\<close>, goal_cases)
  case (1 ee)
  hence a:"make_pair ee \<in> forst" by (fastforce simp add: make_pairs_are )
  hence b:"prod.swap (make_pair ee) \<in> forst"
    using 1 by (fastforce simp add: make_pairs_are )
  hence c:"conv (prod.swap (make_pair ee)) =  B ee"
    using 1(2)[of "fst ee" "snd ee" ee] assms(3)[of "make_pair ee"] a 1(1,4,5)
    by (metis (no_types, lifting) "1"(2) Redge.distinct(1) Redge.inject(1) imageE 
         make_pairs_are(1) prod.swap_def surjective_pairing)
  then show ?case 
    using "1"(5) b by force
next
  case (2 ee)
  hence a:"prod.swap (make_pair ee) \<in> forst" by (fastforce simp add: make_pairs_are )
  hence b:"make_pair ee \<in> forst"
    using 2 by (fastforce simp add: make_pairs_are )
  hence c:"conv (make_pair ee) =  F ee"
    using 2(2)[of "fst ee" "snd ee" ee] assms(3)[of "make_pair ee"] a 2(1,4,5)
  by (metis assms(1) cost_flow_network.fstv.simps(2) cost_flow_network.sndv.simps(2) image_iff
      local.algo.consist_fstv local.algo.consist_sndv make_pair_fst_snd surjective_pairing)
  then show ?case 
    using 2(5) b by force
next
  case (3 ee)
  hence c:"conv (prod.swap (make_pair ee)) =  B ee"
    using 3(2)[of "fst ee" "snd ee" ee] assms(3)[of "make_pair ee"] 
    by (metis assms(1) cost_flow_network.erev.simps(1) cost_flow_network.fstv.simps(2)
        cost_flow_network.sndv.simps(2) image_iff local.algo.consist_fstv local.algo.consist_sndv
        local.multigraph.make_pair''(1,2) make_pairs_are(1) prod.swap_def surjective_pairing)
  hence b:"prod.swap (make_pair ee) \<in> forst"
    using 3 by (fastforce simp add: make_pairs_are)
  hence a:"make_pair ee \<in> forst"using 3 by (fastforce simp add: make_pairs_are)
  moreover have "conv (make_pair ee) = F ee" 
    using "3"(2) multigraph.make_pair' assms(3) c calculation
    by (fastforce simp add: make_pairs_are)
  then show ?case
    using "3"(5) calculation by force
next
  case (4 ee)
hence c:"conv ((make_pair ee)) =  F ee"
  by (metis assms(1) cost_flow_network.erev.simps(2) cost_flow_network.fstv.simps(1)
      cost_flow_network.sndv.simps(1) image_iff local.algo.consist_fstv local.algo.consist_sndv
      make_pair_fst_snd surjective_pairing)
  hence b:"(make_pair ee) \<in> forst"
    using 4 by (fastforce simp add: make_pairs_are)
  hence a:"prod.swap (make_pair ee) \<in> forst"using 4 by (fastforce simp add: make_pairs_are)
  moreover have "conv (prod.swap (make_pair ee)) = B ee"
    using 4(2) multigraph.make_pair' assms(3) b c calculation
    by (fastforce simp add: make_pairs_are)
  then show ?case
    using 4(5) calculation by force
qed

abbreviation "get_source_target_path_b_cond \<equiv> send_flow_spec.get_source_target_path_b_cond "
lemmas get_source_target_path_b_cond_def = send_flow_spec.get_source_target_path_b_cond_def
lemmas get_source_target_path_b_condE = send_flow_spec.get_source_target_path_b_condE

lemma get_source_target_path_b_ax:
  assumes "get_source_target_path_b_cond  state s t P b \<gamma> f"
  shows  "cost_flow_network.is_min_path (abstract_flow_map f) s t P \<and>
          oedge ` set P \<subseteq> to_set (actives state) \<union> \<F> state \<and> 
          s \<in> \<V> \<and> abstract_bal_map b s > \<epsilon> * \<gamma>"
proof-
  define bf where  "bf = bellman_ford_backward (a_not_blocked state) (a_current_flow state) t"
  define ss_opt where "ss_opt = (get_source_for_target_aux_aux bf 
                     (\<lambda> v. abstract_real_map (bal_lookup (balance state)) v)
                                           (current_\<gamma> state) vs)"
  show ?thesis
  proof(cases ss_opt)
    case None
    hence "get_source_target_path_b state t = None"
      by(auto simp add: option_none_simp[of "get_source_for_target_aux_aux _ _ _ _"] 
                 algo.abstract_not_blocked_map_def option.case_eq_if 
                   ss_opt_def bf_def get_source_target_path_b_def)     
    hence False
      using assms by (auto elim: get_source_target_path_b_condE)
    thus ?thesis by simp
  next
    case (Some a)
  define ss where "ss = the ss_opt"
  define Pbf where "Pbf = search_rev_path_exec t bf ss"
  define PP where "PP = map (\<lambda>e. prod.fst (get_edge_and_costs_backward (a_not_blocked state) (a_current_flow state)
                                  (prod.snd e) (prod.fst e)))
                   (edges_of_vwalk Pbf)"
  have ss_opt_ss:"ss_opt = Some ss"
    by (simp add: Some ss_def)
  have "Some (ss, PP) = Some (s, P)"
    using assms
    by(cases ss_opt)
      (auto simp add: option_none_simp[of "get_source_for_target_aux_aux _ _ _ _"] 
                 algo.abstract_not_blocked_map_def option.case_eq_if 
                   ss_opt_def bf_def get_source_target_path_b_def ss_def
                  get_source_target_path_b_cond_def PP_def Pbf_def pair_to_realising_redge_backward_def)
  hence ss_is_s: "ss = s" and PP_is_P: "PP = P" by auto 
  have ss_props: "ss \<in> set local.vs"
     "a_balance state ss > local.\<epsilon> * current_\<gamma> state"
     "prod.snd (the (connection_lookup bf ss)) < PInfty"
    using get_source_for_target_aux_aux(2)[of bf "a_balance state" "current_\<gamma> state" vs]
           Some
    by(auto simp add: ss_def ss_opt_def)
  have s_props:"s \<in> \<V>" "abstract_bal_map b s > local.\<epsilon> * current_\<gamma> state"
       "resreach (abstract_flow_map f) s t" "s \<noteq> t" and gamma_0: "current_\<gamma> state > 0"
    using get_source_for_target_ax[of b state, OF  _  refl, of f t s P]  assms 
    by(auto simp add: get_source_target_path_b_cond_def make_pairs_are elim: algo.invar_gammaE)
  hence bs_neg:"abstract_bal_map b s > 0" 
    using dual_order.strict_trans2 local.algo.\<epsilon>_axiom(1) by fastforce
  have t_props: "t \<in> \<V>" "- (1 - local.\<epsilon>) * current_\<gamma> state > abstract_bal_map b t"
    using get_target_axioms_red(1)[of b state "current_\<gamma> state" t] assms
    by(auto simp add: get_source_target_path_b_cond_def)
  hence bt_pos: "abstract_bal_map b t < 0" 
    using gamma_0 \<epsilon>_axiom t_props(2) 
    by (auto simp add: algebra_simps)
       (smt (verit, best) mult_less_0_iff t_props(2))
  hence a_balance_s_not_zero:"a_balance state t \<noteq> 0"  
    using assms by(force simp add: get_source_target_path_b_cond_def)
  have knowledge: True
    "s \<in> VV" "t \<in> VV" "s \<noteq> t"
    "underlying_invars state"
    "(\<forall>e\<in>\<F> state. 0 < abstract_flow_map f e)"
    "resreach (abstract_flow_map f) s t"
    "b = balance state"
    "\<gamma> = current_\<gamma> state"
    "Some t = get_target state"
    "f = current_flow state"
    "invar_gamma state"
    "\<not> (\<forall>v\<in>VV. abstract_bal_map b v = 0)"
    "\<exists>t\<in>VV. -(1 - \<epsilon>) * \<gamma> > abstract_bal_map b t"
    "\<exists>s\<in>VV. abstract_bal_map b s > \<epsilon> * \<gamma> \<and> resreach (abstract_flow_map f) s t"
                  "s = ss"  "P = PP"
    using assms t_props t_props  a_balance_s_not_zero s_props
    by(auto simp add:  ss_is_s PP_is_P vs_is_V get_source_target_path_b_cond_def make_pairs_are) 
  hence 
    "(\<forall>e\<in> (abstract_conv_map (conv_to_rdg state)) ` (digraph_abs (\<FF> state)).
        0 < a_current_flow state (flow_network_spec.oedge e))"
    by (auto simp add: \<F>_def)
  have f_is: "abstract_flow_map f = a_current_flow state"
    and not_blocked_is: "abstract_not_blocked_map (not_blocked state) = a_not_blocked state"
    using assms by(auto simp add: get_source_target_path_b_cond_def)
  have s_prop: "abstract_bal_map b s > \<epsilon> * \<gamma>" "resreach (abstract_flow_map f) s t" 
    using get_source_for_target_ax[OF knowledge(8,9,11,10) _ knowledge(12)]
          knowledge(9) s_props(2,3)
    by auto
  then obtain pp where pp_prop:"augpath (abstract_flow_map f) pp" "fstv (hd pp) = s" "sndv (last pp) = t" "set pp \<subseteq> EEE"
    using cost_flow_network.resreach_imp_augpath[OF , of "abstract_flow_map f" s t] by auto
  obtain ppd where ppd_props:"augpath (abstract_flow_map f) ppd" "fstv (hd ppd) = s" "sndv (last ppd) = t" "set ppd \<subseteq> set pp"
                        "distinct ppd"
    using pp_prop 
    by (auto intro:  cost_flow_network.there_is_s_t_path[OF  _ _ _ refl, of "abstract_flow_map f" pp s t])
  obtain Q where Q_min:"cost_flow_network.is_min_path (abstract_flow_map f) s t Q"
    apply(rule cost_flow_network.there_is_min_path[OF , of "abstract_flow_map f" s t ppd])
    using pp_prop ppd_props cost_flow_network.is_s_t_path_def 
    by auto
  hence Q_prop:"augpath (abstract_flow_map f) Q" "fstv (hd Q) = s" "sndv (last Q) = t"
        "set Q \<subseteq> EEE" "distinct Q"
    by(auto simp add: cost_flow_network.is_min_path_def 
              cost_flow_network.is_s_t_path_def)
  have no_augcycle: "\<nexists>C. augcycle (abstract_flow_map f) C" 
    using assms  cost_flow_network.min_cost_flow_no_augcycle
    by(auto simp add: invar_isOptflow_def elim!: get_source_target_path_b_condE)
  obtain qq where  qq_prop:"augpath (abstract_flow_map f) qq"
     "fstv (hd qq) = s" 
     "sndv (last qq) = t"
     "set qq
     \<subseteq> {e |e. e \<in> EEE \<and> flow_network_spec.oedge e \<in> to_set (actives state)} \<union>
        (abstract_conv_map (conv_to_rdg state)) ` (digraph_abs (\<FF> state))"
     "foldr (\<lambda>x. (+) (\<cc> x)) qq 0 \<le> foldr (\<lambda>x. (+) (\<cc> x)) Q 0" "qq \<noteq> []"
    using algo.simulate_inactives_costs[OF Q_prop(1-4) knowledge(5) refl
              f_is refl refl refl refl refl refl knowledge(4) _ no_augcycle ] 
           knowledge(6) 
    by (auto simp add: algo.\<F>_redges_def)
  have qq_len: "length qq \<ge> 1" "qq \<noteq> []"
    using qq_prop(2,3,6) knowledge(4)
    by( all \<open>cases qq rule: list_cases3\<close>) auto
  have symmetric_digraph: "symmetric_digraph (Instantiation.Adj_Map_Specs2.digraph_abs (\<FF> state))"
    using algo.from_underlying_invars'(19) knowledge(5) by auto
  have forest_no_loop: "(\<And>e. e \<in> Instantiation.Adj_Map_Specs2.digraph_abs (\<FF> state) \<Longrightarrow>
          prod.fst e \<noteq> prod.snd e)" 
    using algo.from_underlying_invars'(14)[OF knowledge(5)]
    by(auto elim!: algo.validFE 
         simp add: dblton_graph_def Adj_Map_Specs2.to_graph_def UD_def) blast    
  have consist: "cost_flow_network.consist (digraph_abs (\<FF> state))
                      (abstract_conv_map (conv_to_rdg state))" 
    using from_underlying_invars'(6) knowledge(5) by auto
  hence e_in_pre:"e \<in> set qq \<Longrightarrow> e \<in> {e |e. e \<in> EEE \<and> flow_network_spec.oedge e \<in> to_set (actives state)} 
                   \<union> (abstract_conv_map (conv_to_rdg state)) ` (digraph_abs (\<FF> state))" for e
    using qq_prop(4)  by auto
  have e_in:"e \<in> set (map cost_flow_network.erev (rev qq)) \<Longrightarrow> e \<in> {e |e. e \<in> EEE \<and> flow_network_spec.oedge e \<in> to_set (actives state)} 
                   \<union> (abstract_conv_map (conv_to_rdg state)) ` (digraph_abs (\<FF> state))" for e
    using e_in_pre[of e] cost_flow_network.Residuals_project_erev_sym[of e] 
      Forest_conv_erev[OF consist symmetric_digraph forest_no_loop, simplified]
      cost_flow_network.erev_\<EE> cost_flow_network.oedge_and_reversed qq_prop(4)
    by auto
  hence e_es:"e \<in> set (map cost_flow_network.erev (rev qq)) \<Longrightarrow> oedge e \<in> \<E>" for e
    using algo.from_underlying_invars'(2) cost_flow_network.o_edge_res knowledge(5)
    by auto
  have e_in_pp_weight:"e \<in> set (map cost_flow_network.erev (rev qq)) \<Longrightarrow>
         prod.snd (get_edge_and_costs_backward (a_not_blocked state) (a_current_flow state) (fstv e)
               (sndv e))
         < PInfty" for e
  proof(goal_cases)
    case 1
    hence 11: "cost_flow_network.erev e \<in> set  qq"
      using in_set_map cost_flow_network.erve_erve_id[OF  ] set_rev by metis
    note e_es[OF 1]
    moreover have oedgeF:"oedge e \<in> to_set (actives state) \<or> oedge e \<in> \<F> state"
      using e_in  1 by (auto simp add: \<F>_def)
    hence oedgeE:"oedge e \<in> \<E>"
      using calculation by blast
    hence not_blocked:"a_not_blocked state (oedge e)"
      using oedgeF  from_underlying_invars'(20)[OF knowledge(5)] by auto
    moreover have flowpos:"\<exists> d. (cost_flow_network.erev e) = B d\<Longrightarrow> a_current_flow state (oedge (cost_flow_network.erev e)) > 0" 
      using cost_flow_network.augpath_rcap_pos_strict'[OF  qq_prop(1) 11] knowledge(11)
      by(induction rule: flow_network_spec.oedge.cases[OF  , of e]) auto  
    ultimately show ?case 
        using "11" cost_flow_network.augpath_rcap_pos_strict cost_flow_network.oedge_and_reversed cost_flow_network.vs_erev
                get_edge_and_costs_backward_makes_cheaper[OF refl _ _ _ prod.collapse, 
                       of "flow_network_spec.erev e" "a_not_blocked state" "a_current_flow state"] knowledge(11)  qq_prop(1) 
        by auto
  qed 
  have bellman_ford:"bellman_ford connection_empty connection_lookup connection_invar connection_delete
     es vs (\<lambda> u v. prod.snd (get_edge_and_costs_backward (a_not_blocked state) (a_current_flow state) u v)) connection_update "
    by (simp add: bellman_ford_backward knowledge(2) knowledge(3))
  have is_a_walk:"awalk UNIV t (map cost_flow_network.to_vertex_pair (map cost_flow_network.erev (rev qq))) ss" 
    using awalk_UNIV_rev[of ss "map to_edge qq" t, simplified rev_map, simplified]
    using  knowledge(16)  qq_prop(1) qq_prop(2) qq_prop(3) 
    by(auto simp add:  cost_flow_network.to_vertex_pair_erev_swap prepath_def  augpath_def )
  hence vwalk_bettt:"vwalk_bet UNIV t (awalk_verts t (map cost_flow_network.to_vertex_pair (map cost_flow_network.erev (rev qq)))) ss"
    using  awalk_imp_vwalk by force
  moreover have weight_le_PInfty:"weight_backward (a_not_blocked state) 
           (a_current_flow state) (awalk_verts t (map cost_flow_network.to_vertex_pair
               (map cost_flow_network.erev (rev qq)))) < PInfty"
    using e_in_pp_weight  is_a_walk bellman_ford_backward qq_prop(3) 
          cost_flow_network.rev_prepath_fst_to_lst[OF  qq_len(2)] 
    by (intro path_flow_network_path_bf_backward) auto
  have no_neg_cycle_in_bf: "\<nexists>c. weight_backward (a_not_blocked state) (a_current_flow state) c < 0 \<and> hd c = last c"
    using knowledge no_neg_cycle_in_bf_backward assms 
    by(auto elim: get_source_target_path_b_condE)
  have long_enough: "2 \<le> length (awalk_verts t (map cost_flow_network.to_vertex_pair (map cost_flow_network.erev (rev qq))))"
    using knowledge(4) awalk_verts_non_Nil calculation knowledge(16)
          hd_of_vwalk_bet'[OF calculation] last_of_vwalk_bet[OF calculation] 
    by (cases "(awalk_verts t (map cost_flow_network.to_vertex_pair (map cost_flow_network.erev (rev qq))))" rule: list_cases3) auto 
  have ss_dist_le_PInfty:"prod.snd (the (connection_lookup bf ss)) < PInfty"
    unfolding bf_def bellman_ford_backward_def bellman_ford_algo_def bellman_ford_init_algo_def
    using no_neg_cycle_in_bf knowledge(4,16,2,3)   vs_is_V weight_le_PInfty vwalk_bettt  long_enough 
    by (fastforce intro!: bellman_ford.bellamn_ford_path_exists_result_le_PInfty[OF bellman_ford_backward])
   have s_dist_le_qq_weight:"prod.snd (the (connection_lookup bf ss)) \<le>
         weight_backward (a_not_blocked state) (a_current_flow state) (awalk_verts t 
               (map cost_flow_network.to_vertex_pair (map cost_flow_network.erev (rev qq))))"
    using   knowledge(4,16,2,3)   vs_is_V weight_le_PInfty  is_a_walk 
            bellman_ford.bellman_ford_computes_length_of_optpath[OF bellman_ford no_neg_cycle_in_bf, of t s]
            bellman_ford.opt_vs_path_def[OF bellman_ford, of t s]
            bellman_ford.vs_pathI[OF bellman_ford long_enough, of t s]
            bellman_ford.weight_le_PInfty_in_vs[OF bellman_ford long_enough, of]
            calculation
    by (auto simp add: vwalk_bet_def bf_def bellman_ford_backward_def bellman_ford_algo_def bellman_ford_init_algo_def)
  hence s_prop:"prod.snd (the (connection_lookup bf s)) < PInfty"
    using knowledge(16) ss_dist_le_PInfty by blast
  have s_in_dom: "s \<in> dom (connection_lookup  bf)"
    using knowledge(2) vs_is_V by (auto simp add: bellman_ford.bellman_ford_init_dom_is[OF bellman_ford]
                       bellman_ford.same_domain_bellman_ford[OF bellman_ford]
                       bf_def bellman_ford_backward_def bellman_ford_algo_def bellman_ford_init_algo_def)
  hence pred_of_s_not_None: "prod.fst (the (connection_lookup bf s)) \<noteq> None"
    using s_prop knowledge(4) bellman_ford.bellman_ford_pred_non_infty_pres[OF bellman_ford, of t "length vs -1"]
    by(auto simp add: bf_def bellman_ford_backward_def  bellman_ford_algo_def bellman_ford_init_algo_def
         bellman_ford.invar_pred_non_infty_def[OF bellman_ford]) 
  have Pbf_def: "Pbf =  (bellford.search_rev_path  t bf s)" 
    unfolding Pbf_def bf_def bellman_ford_backward_def
    using vs_is_V  pred_of_s_not_None knowledge(2,3) ss_is_s
    apply(subst sym[OF arg_cong[of _ _ rev, OF bellford.function_to_partial_function, simplified]])
    subgoal
      unfolding bellman_ford_algo_def bellman_ford_init_algo_def
      apply(rule bf_bw.search_rev_path_dom_bellman_ford[OF no_neg_cycle_in_bf] )
      by(auto simp add: bellman_ford_backward_def bf_def
                        bellman_ford_algo_def bellman_ford_init_algo_def)
    by simp
  have weight_Pbf_snd: "weight_backward (a_not_blocked state) 
          (a_current_flow state) (rev Pbf) = prod.snd (the (connection_lookup bf s))"
    unfolding Pbf_def
    using s_prop   vs_is_V  pred_of_s_not_None knowledge(2,3,4)
    by(fastforce simp add: bellman_ford_backward_def bf_def bellman_ford_algo_def bellman_ford_init_algo_def
                 intro!: bellman_ford.bellman_ford_search_rev_path_weight[OF 
                bellman_ford no_neg_cycle_in_bf, of bf t s])+
  hence weight_le_PInfty: "weight_backward (a_not_blocked state) (a_current_flow state) (rev Pbf) < PInfty"
    using s_prop by auto
  have Pbf_opt_path: "bellman_ford.opt_vs_path vs
     (\<lambda>u v. prod.snd (get_edge_and_costs_backward (a_not_blocked state) (a_current_flow state) u v)) t s
     (rev (bellford.search_rev_path t bf s))"
   using s_prop  vs_is_V  pred_of_s_not_None knowledge(2,3,4)
   by (auto simp add: bellman_ford_backward_def bf_def bellman_ford_algo_def bellman_ford_init_algo_def
                 intro!: bellman_ford.computation_of_optimum_path[OF bellman_ford no_neg_cycle_in_bf])
    hence length_Pbf:"2 \<le> length Pbf"
    by(auto simp add: bellman_ford.opt_vs_path_def[OF bellman_ford]
      bellman_ford.vs_path_def[OF bellman_ford] Pbf_def)
  have Pbf_props: "awalk UNIV (hd Pbf) (edges_of_vwalk  Pbf)  (last Pbf)"
         "weight_backward (a_not_blocked state) (a_current_flow state) (rev Pbf) =
         ereal  (foldr (\<lambda>e. (+) (\<cc> e))
        (map (\<lambda>e. prod.fst (get_edge_and_costs_backward (a_not_blocked state) (a_current_flow state) (prod.snd e) (prod.fst e)))
               ( edges_of_vwalk  Pbf) ) 0)"
         "\<And> e. e\<in>set (map (\<lambda>e. prod.fst (get_edge_and_costs_backward (a_not_blocked state) (a_current_flow state) (prod.snd e)
                         (prod.fst e)))
           ( edges_of_vwalk  Pbf) ) \<Longrightarrow>
    a_not_blocked state (flow_network_spec.oedge e) \<and> 0 < cost_flow_network.rcap (a_current_flow state) e"
    using edges_of_vwalk_rev_swap[of "rev Pbf"]
          path_bf_flow_network_path_backward[OF _ length_Pbf[simplified sym[OF length_rev[of Pbf]]]
          weight_le_PInfty refl, simplified last_rev hd_rev]
      by auto 
  have same_edges:"(map cost_flow_network.to_vertex_pair PP) = (edges_of_vwalk Pbf)"
    unfolding PP_def 
    apply(subst (2) sym[OF List.list.map_id[of "edges_of_vwalk Pbf"]], subst map_map)
    using get_edge_and_costs_backward_result_props[OF prod.collapse[symmetric] _ refl]
          to_edge_get_edge_and_costs_backward 
    by (fastforce intro!: map_ext)
  moreover have awalk_f:" awalk UNIV (fstv (hd PP)) (map cost_flow_network.to_vertex_pair PP) 
                 (sndv (last PP))"   
    apply(rule edges_of_vwalk.elims [OF sym[OF same_edges]])
    using Pbf_props(1) same_edges length_Pbf awalk_fst_last bellman_ford.weight.simps[OF bellman_ford] 
           cost_flow_network.vs_to_vertex_pair_pres apply auto[2]
    using calculation  Pbf_props(1) same_edges 
    by (auto simp add: cost_flow_network.vs_to_vertex_pair_pres awalk_intros(1) 
                        arc_implies_awalk[OF UNIV_I refl]) 
       (metis awalk_fst_last last_ConsR last_map list.simps(3) list.simps(9))
  moreover have "PP \<noteq> []"
    using  edges_of_vwalk.simps(3) length_Pbf same_edges
    by(cases Pbf rule: list_cases3) auto
  ultimately have "cost_flow_network.prepath PP"
  by(auto simp add:cost_flow_network.prepath_def )
  moreover have Rcap_P:"0 < cost_flow_network.Rcap (a_current_flow state) (set PP)"
    using PP_def Pbf_props(3)
    by(auto simp add: cost_flow_network.Rcap_def)
  ultimately have "augpath (a_current_flow state) PP"
    by(auto simp add: cost_flow_network.augpath_def)
  moreover have "fstv (hd PP) = s" 
    using awalk_f same_edges Pbf_opt_path  awalk_ends[OF Pbf_props(1)] knowledge(4)
    by (force simp add: PP_def bellman_ford.opt_vs_path_def[OF bellman_ford]
                        bellman_ford.vs_path_def[OF bellman_ford] Pbf_def hd_rev last_rev)
  moreover have "sndv (last PP) = t" 
    using awalk_f same_edges Pbf_opt_path  awalk_ends[OF Pbf_props(1)]  knowledge(4)
    by (force simp add: PP_def bellman_ford.opt_vs_path_def[OF bellman_ford]
                        bellman_ford.vs_path_def[OF bellman_ford] Pbf_def hd_rev last_rev)
  moreover have oedge_of_p_allowed:"oedge ` (set PP) \<subseteq> to_set (actives state) \<union> \<F> state"
  proof(rule, rule ccontr, goal_cases)
    case (1 e)
    have "a_not_blocked state e"
      using map_in_set same_edges "1"(1) PP_def Pbf_props(3) list.set_map by blast
    thus ?case
      using  from_underlying_invars'(20)[of state, OF knowledge(5)] 1 by simp
  qed
  have distinct_Pbf: "distinct Pbf"
    using no_neg_cycle_in_bf knowledge(2,3,4) vs_is_V pred_of_s_not_None 
          bellman_ford.search_rev_path_distinct[OF bellman_ford]
    by (fastforce simp add: bellman_ford_backward_def bf_def Pbf_def bellman_ford_algo_def bellman_ford_init_algo_def)
  have distinctP:"distinct PP" 
    using distinct_edges_of_vwalk[OF distinct_Pbf, simplified sym[OF same_edges ]]
          distinct_map by auto
  have qq_in_E:"set (map flow_network_spec.oedge (map cost_flow_network.erev (rev qq))) \<subseteq> \<E>"
    using e_es by auto
  hence qq_rev_in_E:"set ( map flow_network_spec.oedge qq) \<subseteq> \<E>" 
    by(auto simp add: es_sym image_subset_iff cost_flow_network.oedge_and_reversed)
  have not_blocked_qq: "\<And> e . e \<in> set qq \<Longrightarrow> a_not_blocked state (oedge e)" 
    using  from_underlying_invars'(20)[OF knowledge(5)]  qq_prop(4) by(auto simp add: \<F>_def)
  have rcap_qq: "\<And> e . e \<in> set qq \<Longrightarrow> cost_flow_network.rcap (a_current_flow state) e > 0" 
    using  cost_flow_network.augpath_rcap_pos_strict'[OF  qq_prop(1) ] knowledge by simp
  have awalk': "unconstrained_awalk (map cost_flow_network.to_vertex_pair (map cost_flow_network.erev (rev qq)))"
               "unconstrained_awalk (map cost_flow_network.to_vertex_pair qq)"
    using unconstrained_awalk_def  is_a_walk qq_prop(1) cost_flow_network.augpath_def cost_flow_network.prepath_def
    by fastforce+
  have bf_weight_leq_res_costs:"weight_backward (a_not_blocked state) (a_current_flow state)
       (awalk_verts t (map cost_flow_network.to_vertex_pair (map cost_flow_network.erev (rev qq))))
      \<le> foldr (\<lambda>x. (+) (\<cc> x)) qq 0" 
    using qq_rev_in_E not_blocked_qq rcap_qq awalk' qq_len 
    by(fastforce intro!: bf_weight_backward_leq_res_costs[simplified
           cost_flow_network.rev_erev_swap , simplified rev_map, of qq _ t])   
  have oedge_of_EE: "flow_network_spec.oedge ` EEE = \<E>" 
    by (meson cost_flow_network.oedge_on_\<EE>)
  have " flow_network_spec.oedge ` set PP \<subseteq> \<E>"
    using from_underlying_invars'(1,3)[OF knowledge(5)] oedge_of_p_allowed by blast
  hence P_in_E: "set PP \<subseteq> EEE"
    by (meson image_subset_iff cost_flow_network.o_edge_res subsetI) 
  have "(foldr (\<lambda>e. (+) (\<cc> e)) PP 0) \<le> foldr (\<lambda>x. (+) (\<cc> x)) Q 0"
    using  weight_Pbf_snd s_dist_le_qq_weight Pbf_props(2)[simplified sym[OF PP_def]]
           qq_prop(5) bf_weight_leq_res_costs knowledge(16) 
    by (smt (verit, best) leD le_ereal_less)
  moreover have "(foldr (\<lambda>e. (+) (\<cc> e)) PP 0) = cost_flow_network.\<CC> PP"
    unfolding cost_flow_network.\<CC>_def 
    by(subst distinct_sum, simp add: distinctP, meson add.commute)
  moreover have "(foldr (\<lambda>e. (+) (\<cc> e)) Q 0) = cost_flow_network.\<CC> Q"
    unfolding cost_flow_network.\<CC>_def 
    by(subst distinct_sum, simp add: Q_prop(5), meson add.commute)
  ultimately have P_min: "cost_flow_network.is_min_path (abstract_flow_map f) s t PP"
    using Q_min P_in_E  knowledge(11)  distinctP
    by(auto simp add: cost_flow_network.is_min_path_def cost_flow_network.is_s_t_path_def)
  show ?thesis 
    using PP_is_P P_min knowledge(9) oedge_of_p_allowed s_props(1,2) by force
 qed
qed 

lemma get_source_aux_nexistence: "(\<not> (\<exists>s\<in> set xs. (1 - \<epsilon>) * \<gamma> < b s)) = (get_source_aux_aux b \<gamma> xs = None)"
  by(induction xs) auto

lemma get_target_aux_nexistence: "(\<not> (\<exists>s\<in> set xs. - (1 - \<epsilon>) * \<gamma> > b s)) = (get_target_aux_aux b \<gamma> xs = None)"
  by(induction xs) auto

lemma impl_a_None_aux:
" \<lbrakk>b = balance state; \<gamma> = current_\<gamma> state; f = current_flow state;
   underlying_invars state; (\<forall> e \<in> \<F> state . abstract_flow_map f e > 0);
   Some s = get_source state; invar_gamma state\<rbrakk>
    \<Longrightarrow> \<not> (\<exists> t \<in> VV. abstract_bal_map b t < - \<epsilon> * \<gamma> \<and> resreach (abstract_flow_map f) s t) 
      \<longleftrightarrow> get_source_target_path_a state s = None"
proof(goal_cases)
  case 1
  note knowledge = this
  define bf where "bf = bellman_ford_forward (a_not_blocked state) (a_current_flow state) s"
  define tt where " tt = get_target_for_source_aux_aux bf
                                (\<lambda>v. a_balance state v) (current_\<gamma> state)
                                   vs"
  have not_blocked_in_E: "a_not_blocked state e \<Longrightarrow> e \<in> \<E>" for e
    using knowledge(4)
    by(auto elim!: algo.underlying_invarsE algo.inv_unbl_iff_forest_activeE algo.inv_actives_in_EE algo.inv_forest_in_EE)
 have bellman_ford:"bellman_ford connection_empty connection_lookup connection_invar connection_delete
     es vs (\<lambda> u v. prod.snd (get_edge_and_costs_forward (a_not_blocked state) (a_current_flow state) u v)) connection_update"
    by (simp add: bellman_ford)
  have s_prop: "(1 - \<epsilon>) * \<gamma> < abstract_bal_map b s" "s \<in> VV"
    using knowledge(6,2,1)  vs_is_V get_source_aux(2)[of s "abstract_bal_map b" "current_\<gamma> state" vs]
    by(auto simp add: get_source_def get_source_aux_def) 
   hence bs0:"abstract_bal_map b s > 0"   
     using knowledge(7,2,1) \<epsilon>_axiom(2,4) algo.invar_gamma_def 
     by (smt (verit, ccfv_SIG) divide_less_eq_1_pos mult_nonneg_nonneg)
  have "\<not> (\<exists> t \<in> VV. abstract_bal_map b t < - \<epsilon> * \<gamma> \<and> resreach (abstract_flow_map f) s t) \<longleftrightarrow> 
            (tt = None)"
  proof(rule,  all \<open>rule ccontr\<close>, goal_cases)
    case (1 )
    then obtain t where "tt = Some t" by auto
    note 1 = this 1
    hence "(\<exists>x\<in>set vs.
    abstract_bal_map b x < - \<epsilon> * current_\<gamma> state \<and>
    prod.snd (the (connection_lookup bf x)) < PInfty)"
      using  get_target_for_source_aux_aux(1) knowledge(1)
      by(unfold tt_def) blast 
    then obtain x where x_prop:"x \<in> set vs" "abstract_bal_map b x < - \<epsilon> * current_\<gamma> state" "prod.snd (the (connection_lookup bf x)) < PInfty"
      by auto
    hence bx0:"abstract_bal_map b x < 0"
      using knowledge(7,2,1) \<epsilon>_axiom algo.invar_gamma_def
      by (smt (verit)  mult_minus_left mult_nonneg_nonneg)
    hence x_not_s:"x \<noteq> s"
      using bs0 by auto
    hence x_in_dom:"x\<in>dom (connection_lookup bf)" "prod.fst (the (connection_lookup bf x)) \<noteq> None"
      using x_prop bellman_ford.same_domain_bellman_ford[OF bellman_ford, of "length vs -1" s]
            bellman_ford.bellman_ford_init_dom_is[OF bellman_ford, of s] 
            bellman_ford.bellman_ford_pred_non_infty_pres[OF bellman_ford, of s "length vs - 1"]
      by(auto simp add: bf_def bellman_ford_forward_def bellman_ford.invar_pred_non_infty_def[OF bellman_ford]
                        bellman_ford_init_algo_def bellman_ford_algo_def)
    obtain p where p_prop:"weight (a_not_blocked state) (a_current_flow state) (p @ [x]) = 
                    prod.snd (the (connection_lookup bf x))"
           "last p = the (prod.fst (the (connection_lookup bf x)))"
           "hd p = s" "1 \<le> length p" "set (p @ [x]) \<subseteq> Set.insert s (set vs)"
      using  bellman_ford.bellman_ford_invar_pred_path_pres[OF bellman_ford, of s "length vs -1"]
             x_in_dom 
      by (auto simp add: bellman_ford.invar_pred_path_def[OF bellman_ford] bf_def 
                         bellman_ford_forward_def bellman_ford_init_algo_def bellman_ford_algo_def)
    hence pw_le_PInfty: "weight (a_not_blocked state) (a_current_flow state) (p @ [x]) < PInfty"
      using x_prop by auto
    define pp where "pp = (map (\<lambda>e. prod.fst (get_edge_and_costs_forward (a_not_blocked state) (a_current_flow state)
                  (prod.fst e) (prod.snd e)))
             (edges_of_vwalk (p @ [x])))"
    have transformed:" awalk UNIV (hd (p @ [x])) (edges_of_vwalk (p @ [x])) (last (p @ [x]))"
         "(\<And>e. e\<in>set pp \<Longrightarrow> a_not_blocked state (flow_network_spec.oedge e) \<and>
                                  0 < cost_flow_network.rcap (a_current_flow state) e)"
      using path_bf_flow_network_path[OF _ _ pw_le_PInfty refl] p_prop pp_def by auto
    have path_hd: "hd (p @ [x]) = fstv (hd pp)"
      by(subst  pp_def , subst hd_map, ((insert p_prop(4), cases p rule: list_cases3, auto)[1]),
            ((insert p_prop(4), cases p rule: list_cases3, auto)[1]),
            auto simp add: cost_flow_network.vs_to_vertex_pair_pres to_edge_get_edge_and_costs_forward)
    have path_last: "last (p @ [x]) = sndv (last pp)"
      apply(subst  pp_def , subst last_map)
      subgoal
        by ((insert p_prop(4), cases p rule: list_cases3, auto)[1])
      using  p_prop(4)  
      by (auto simp add: cost_flow_network.vs_to_vertex_pair_pres to_edge_get_edge_and_costs_forward sym[OF last_v_snd_last_e])
    have same_edges: "(edges_of_vwalk (p @ [x])) = map cost_flow_network.to_vertex_pair pp"
      using to_edge_get_edge_and_costs_forward by (auto simp add: o_def pp_def )
    have prepath:"prepath pp"
      using transformed(1) le_simps(3) p_prop(3) p_prop(4) path_hd path_last same_edges x_not_s 
      by (auto simp add: cost_flow_network.prepath_def)
    moreover have "0 < cost_flow_network.Rcap (abstract_flow_map f) (set pp)"
      using transformed(2) knowledge(3)
      by(auto intro: linorder_class.Min_gr_iff simp add: cost_flow_network.Rcap_def)
    ultimately have "augpath (abstract_flow_map f) pp"
      by(simp add: cost_flow_network.augpath_def)
    moreover have " e \<in> set pp \<Longrightarrow> e \<in> EEE" for e
      using transformed(2)[of e] not_blocked_in_E cost_flow_network.o_edge_res by blast
    ultimately have "resreach (abstract_flow_map f) s x"
      using cost_flow_network.augpath_imp_resreach path_hd p_prop(3,4) path_last
      by(cases p) auto
    thus False
      using 1 x_prop(1,2) knowledge(2) vs_is_V
      by simp
  next
    case 2
    then obtain t where "t\<in>local.multigraph.\<V>" 
               "abstract_bal_map b t < - local.\<epsilon> * \<gamma> " "resreach (abstract_flow_map f) s t"
      by (auto simp add: make_pairs_are)
    note 2 = this 2
    hence "abstract_bal_map b t < 0"
      using knowledge(7,2,1) \<epsilon>_axiom algo.invar_gamma_def
      by (smt (verit)  mult_minus_left mult_nonneg_nonneg)
    hence t_not_s:"t \<noteq> s"
      using bs0 by auto
    have f_is: "abstract_flow_map f = a_current_flow state"
      by (simp add: knowledge(3))
    obtain q where q_props:"augpath (abstract_flow_map f) q" "fstv (hd q) = s" 
                    "sndv (last q) = t" "set q \<subseteq> EEE"
      using  cost_flow_network.resreach_imp_augpath[OF  2(3)] by auto
    then obtain qq where qq_props:"augpath (abstract_flow_map f) qq"
       "fstv (hd qq) = s"
       "sndv (last qq) = t"
       "set qq \<subseteq> {e |e. e \<in> EEE \<and> flow_network_spec.oedge e \<in> to_set (actives state)}
            \<union> abstract_conv_map (conv_to_rdg state) ` (digraph_abs (\<FF> state))"
       "qq \<noteq> []"
      using algo.simulate_inactives[OF q_props(1-4) 1(4) refl f_is refl refl refl refl refl refl]
        t_not_s knowledge(5) by(auto simp add: \<F>_redges_def)
    have e_in_qq_not_blocked: "e \<in> set qq \<Longrightarrow> a_not_blocked state (flow_network_spec.oedge e)" for e   
      using qq_props(4) 
      by(induction e rule: flow_network_spec.oedge.induct)
        (fastforce simp add: spec[OF algo.from_underlying_invars'(20)[OF 1(4)]] flow_network_spec.oedge.simps(1) 
                   image_iff \<F>_def dest!: set_mp)+
    have e_in_qq_rcap: "e \<in> set qq \<Longrightarrow> 0 < cost_flow_network.rcap (abstract_flow_map f) e" for e
      using qq_props(1)  linorder_class.Min_gr_iff 
      by (auto simp add: augpath_def cost_flow_network.Rcap_def)
    obtain Q where Q_prop:"fstv (hd Q) = s" "sndv (last Q) = t" 
                   "distinct Q" "set Q \<subseteq> set qq" "augpath (abstract_flow_map f) Q"
      using cost_flow_network.there_is_s_t_path[OF , OF qq_props(1-3) refl] by auto
    have e_in_qq_E: "e \<in> set Q \<Longrightarrow> oedge e \<in> \<E>" for e 
      using Q_prop(4) e_in_qq_not_blocked not_blocked_in_E by blast
    have costsQ: "e \<in> set Q \<Longrightarrow>
         prod.snd (get_edge_and_costs_forward (a_not_blocked state) (abstract_flow_map f) (fstv e) (sndv e)) < PInfty" for e
     apply(rule order.strict_trans1)
       apply(rule conjunct1[OF get_edge_and_costs_forward_makes_cheaper[OF refl _ _ ,
                      of e "a_not_blocked state" "abstract_flow_map f"]])
      using  e_in_qq_E  e_in_qq_not_blocked  e_in_qq_rcap Q_prop(4) 
      by(auto intro: prod.collapse)
    have awalk:"awalk UNIV s (map cost_flow_network.to_vertex_pair Q) t"
      using Q_prop(1) Q_prop(2) Q_prop(5) cost_flow_network.augpath_def cost_flow_network.prepath_def by blast
    have "weight (a_not_blocked state) (abstract_flow_map f) (awalk_verts s (map cost_flow_network.to_vertex_pair Q)) < PInfty"
      using costsQ  awalk Q_prop(1) bellman_ford  knowledge(3) 
      by (intro path_flow_network_path_bf[of Q "a_not_blocked state" "abstract_flow_map f" s]) auto
    moreover have " (hd (awalk_verts s (map cost_flow_network.to_vertex_pair Q))) = s"
           using awalk by auto
    moreover have "last (awalk_verts s (map cost_flow_network.to_vertex_pair Q)) = t" 
        using awalk by force
      ultimately have " bellman_ford.OPT vs (\<lambda>u v. prod.snd (get_edge_and_costs_forward
                  (a_not_blocked state) (a_current_flow state) u v)) (length vs - 1) s t < PInfty" 
        using t_not_s 1(3)
        by(intro bellman_ford.weight_le_PInfty_OPTle_PInfty[OF bellman_ford _ _ refl,
                    of _ "tl (butlast (awalk_verts s (map cost_flow_network.to_vertex_pair Q)))"],
              cases "awalk_verts s (map cost_flow_network.to_vertex_pair Q)" rule: list_cases_both_sides) auto
    moreover have "prod.snd (the (connection_lookup bf t)) \<le> 
            bellman_ford.OPT vs (\<lambda>u v. prod.snd (get_edge_and_costs_forward 
             (a_not_blocked state) (a_current_flow state) u v)) (length vs - 1) s t"
      using bellman_ford.bellman_ford_shortest[OF bellman_ford, of s "length vs -1" t] vs_is_V
            knowledge(4) s_prop(2)
      by(auto simp add: bf_def bellman_ford_forward_def bellman_ford_init_algo_def
           bellman_ford_algo_def) 
    ultimately have "prod.snd (the (connection_lookup bf t)) < PInfty" by auto
    hence "t \<in> set vs" "abstract_bal_map b t < - \<epsilon> * current_\<gamma> state"
                    "prod.snd (the (connection_lookup bf t)) < PInfty"
      using "2" knowledge(2) vs_is_V by (auto simp add: make_pairs_are)
    hence "(tt \<noteq> None)"
      using get_target_for_source_aux_aux(1)[of vs "abstract_bal_map b"
                                            "current_\<gamma> state" bf] knowledge(1) tt_def 
      by blast
    thus False
      using 2 by simp
  qed
  thus ?thesis 
    by(simp add: tt_def bf_def local.get_source_target_path_a_def
                  algo.abstract_not_blocked_map_def option.case_eq_if)
qed

abbreviation "impl_a_None_cond \<equiv> send_flow_spec.impl_a_None_cond"
lemmas impl_a_None_cond_def = send_flow_spec.impl_a_None_cond_def
lemmas impl_a_None_condE= send_flow_spec.impl_a_None_condE

lemma  impl_a_None:
     "impl_a_None_cond state s b \<gamma> f \<Longrightarrow>
      (\<not> (\<exists>t\<in>VV. abstract_bal_map b t < - \<epsilon> * \<gamma> \<and> resreach (abstract_flow_map f) s t)) 
           = (get_source_target_path_a state s = None)"
  using impl_a_None_aux[OF refl refl refl] 
  by (auto elim!: impl_a_None_condE)

lemma impl_b_None_aux:
" \<lbrakk>b = balance state; \<gamma> = current_\<gamma> state; f = current_flow state;
   underlying_invars state; (\<forall> e \<in> \<F> state . abstract_flow_map f e > 0);
   Some t = get_target state; invar_gamma state\<rbrakk>
    \<Longrightarrow> \<not> (\<exists> s \<in> VV. abstract_bal_map b s > \<epsilon> * \<gamma> \<and> resreach (abstract_flow_map f) s t) 
        \<longleftrightarrow> get_source_target_path_b state t = None"
proof(goal_cases)
  case 1
  note knowledge = this
  define bf where "bf = bellman_ford_backward (a_not_blocked state) (a_current_flow state) t"
  define ss where "ss = get_source_for_target_aux_aux bf
                                (\<lambda>v. a_balance state v) (current_\<gamma> state)
                                   vs"
  have not_blocked_in_E: "a_not_blocked state e \<Longrightarrow> e \<in> \<E>" for e
    using knowledge(4)
    by(auto elim!: algo.underlying_invarsE algo.inv_unbl_iff_forest_activeE algo.inv_actives_in_EE algo.inv_forest_in_EE)
  have bellman_ford:"bellman_ford connection_empty connection_lookup connection_invar connection_delete
     es vs (\<lambda> u v. prod.snd (get_edge_and_costs_backward (a_not_blocked state) (a_current_flow state) u v)) connection_update"
    by (simp add: bellman_ford_backward)
  have t_prop: "- (1 - \<epsilon>) * \<gamma> > abstract_bal_map b t" "t \<in> VV" 
    using knowledge(6,2,1)  vs_is_V get_target_aux(2)[of t "abstract_bal_map b" "current_\<gamma> state" vs]
    by(auto simp add: get_target_def get_target_aux_def) 
  hence bt0:"abstract_bal_map b t < 0"   
      using knowledge(7,2,1) \<epsilon>_axiom algo.invar_gamma_def
      by (smt (verit) divide_less_eq_1_pos mult_minus_left mult_nonneg_nonneg)+
  have "\<not> (\<exists> s \<in> VV. abstract_bal_map b s > \<epsilon> * \<gamma> \<and> resreach (abstract_flow_map f) s t) \<longleftrightarrow> 
            (ss = None)"
  proof(rule,  all \<open>rule ccontr\<close>, goal_cases)
    case 1
    then obtain s where "ss = Some s" by auto
    note 1 = this 1
    hence "(\<exists>x\<in>set vs. abstract_bal_map b x > \<epsilon> * current_\<gamma> state \<and> 
           prod.snd (the (connection_lookup bf x)) < PInfty)"
      using  get_source_for_target_aux_aux(1) knowledge(1)
      by(unfold ss_def) blast 
    then obtain x where x_prop:"x \<in> set vs" "abstract_bal_map b x > \<epsilon> * current_\<gamma> state" "prod.snd (the (connection_lookup bf x)) < PInfty"
      by auto
    hence bx0:"abstract_bal_map b x > 0"
      using knowledge(7,2,1) \<epsilon>_axiom algo.invar_gamma_def 
      by (smt (verit)  mult_minus_left mult_nonneg_nonneg)
    hence x_not_s:"x \<noteq> t"
      using bt0 by auto
    hence x_in_dom:"x\<in>dom (connection_lookup bf)" 
                   "prod.fst (the (connection_lookup bf x)) \<noteq> None"
      using x_prop bellman_ford.same_domain_bellman_ford[OF bellman_ford, of "length vs -1" t]
            bellman_ford.bellman_ford_init_dom_is[OF bellman_ford, of t] 
            bellman_ford.bellman_ford_pred_non_infty_pres[OF bellman_ford, of t "length vs - 1"]
      by(auto simp add: bf_def bellman_ford_backward_def bellman_ford.invar_pred_non_infty_def[OF bellman_ford]
                        bellman_ford_init_algo_def bellman_ford_algo_def)
    obtain p where p_prop:"weight_backward (a_not_blocked state) (a_current_flow state) (p @ [x]) = 
                    prod.snd (the (connection_lookup bf x))"
           "last p = the (prod.fst (the (connection_lookup bf x)))"
           "hd p = t" "1 \<le> length p" "set (p @ [x]) \<subseteq> Set.insert t (set vs)"
      using  bellman_ford.bellman_ford_invar_pred_path_pres[OF bellman_ford, of t "length vs -1"]
             x_in_dom 
      by (auto simp add: bellman_ford.invar_pred_path_def[OF bellman_ford] bf_def bellman_ford_backward_def
                         bellman_ford_algo_def bellman_ford_init_algo_def)
    hence pw_le_PInfty: "weight_backward (a_not_blocked state) (a_current_flow state) (p @ [x]) < PInfty"
      using x_prop by auto
    define pp where "pp = (map (\<lambda>e. prod.fst (get_edge_and_costs_backward (a_not_blocked state) (a_current_flow state) (prod.snd e) (prod.fst e)))
               (map prod.swap (rev (edges_of_vwalk (p @ [x])))))"
    have transformed:" awalk UNIV (last (p @ [x])) (map prod.swap (rev (edges_of_vwalk (p @ [x])))) (hd (p @ [x]))"
         "(\<And>e. e\<in>set pp \<Longrightarrow> a_not_blocked state (flow_network_spec.oedge e) \<and>
                0 < cost_flow_network.rcap (a_current_flow state) e)"
      using path_bf_flow_network_path_backward[OF _ _ pw_le_PInfty refl] p_prop pp_def by auto
    have non_empt: "(rev (edges_of_vwalk (p @ [x]))) \<noteq> []"
      by(insert p_prop(4); cases p rule: list_cases3; auto)
    have path_hd: "last (p @ [x]) = fstv (hd pp)"
      using last_v_snd_last_e[of "p@[x]"] p_prop(4)
      by(auto simp add: pp_def last_map[OF non_empt]  hd_rev hd_map[OF non_empt] cost_flow_network.vs_to_vertex_pair_pres to_edge_get_edge_and_costs_backward)
    have path_last: "hd (p @ [x]) = sndv (last pp)"
     using hd_v_fst_hd_e[of "p@[x]"] p_prop(4)
      by(auto simp add: pp_def last_map[OF non_empt]  last_rev  cost_flow_network.vs_to_vertex_pair_pres to_edge_get_edge_and_costs_backward)
    have same_edges: "(map prod.swap (rev (edges_of_vwalk (p @ [x])))) = map cost_flow_network.to_vertex_pair pp"
      by(auto simp add: pp_def o_def to_edge_get_edge_and_costs_backward)
    have prepath:"prepath pp"
      using transformed(1) le_simps(3) p_prop(3) p_prop(4) path_hd path_last x_not_s  same_edges
      by(auto simp add: cost_flow_network.prepath_def) 
    moreover have "0 < cost_flow_network.Rcap (abstract_flow_map f) (set pp)"
      using transformed(2) knowledge(3)
      by(auto intro: linorder_class.Min_gr_iff simp add: cost_flow_network.Rcap_def)
    ultimately have "augpath  (abstract_flow_map f) pp"
      by(simp add: cost_flow_network.augpath_def)
    moreover have " e \<in> set pp \<Longrightarrow> e \<in> EEE" for e
      using transformed(2)[of e] not_blocked_in_E cost_flow_network.o_edge_res by blast
    ultimately have "resreach  (abstract_flow_map f) x t"
      using cost_flow_network.augpath_imp_resreach[OF , of " (abstract_flow_map f)" pp]
            path_hd p_prop(3,4) path_last
      by (metis One_nat_def hd_append2 last_snoc le_numeral_extra(4) list.size(3) not_less_eq_eq subsetI)
    thus False
      using 1 x_prop(1,2) knowledge(2) vs_is_V
      by simp
  next
    case 2
    then obtain s where "s\<in>multigraph.\<V> " "\<epsilon> * \<gamma> < abstract_bal_map b s"
                          "resreach (abstract_flow_map f) s t"
      by (auto simp add: make_pairs_are)
    note 2 = 2 this
    hence "abstract_bal_map b s > 0"
      using knowledge(7,2,1) \<epsilon>_axiom algo.invar_gamma_def 
      by (smt (verit)  mult_minus_left mult_nonneg_nonneg)
    hence t_not_s:"t \<noteq> s"
      using bt0 by auto
    have f_is: "abstract_flow_map f = a_current_flow state"
      by (simp add: knowledge(3))
    obtain q where q_props:"augpath (abstract_flow_map f) q" "fstv (hd q) = s" 
                    "sndv (last q) = t" "set q \<subseteq> EEE"
      using  cost_flow_network.resreach_imp_augpath[OF  2(5)] by auto
    then obtain qq where qq_props:"augpath (abstract_flow_map f) qq"
       "fstv (hd qq) = s"
       "sndv (last qq) = t"
       "set qq \<subseteq> {e |e. e \<in> EEE \<and> flow_network_spec.oedge e \<in> to_set (actives state)}
            \<union> abstract_conv_map (conv_to_rdg state) ` (digraph_abs (\<FF> state))"
       "qq \<noteq> []" 
  using algo.simulate_inactives[OF q_props(1-4) 1(4) refl f_is refl refl refl refl refl refl]
        t_not_s knowledge(5) by(auto simp add: \<F>_redges_def)
    have e_in_qq_not_blocked: "e \<in> set qq \<Longrightarrow> a_not_blocked state (flow_network_spec.oedge e)" for e   
      using qq_props(4) 
      by(induction e rule: flow_network_spec.oedge.induct)
        (fastforce simp add: spec[OF algo.from_underlying_invars'(20)[OF 1(4)]] flow_network_spec.oedge.simps(1) 
                   image_iff \<F>_def dest!: set_mp)+
    have e_in_qq_rcap: "e \<in> set qq \<Longrightarrow> 0 < cost_flow_network.rcap (abstract_flow_map f) e" for e
      using qq_props(1)  linorder_class.Min_gr_iff 
      by (auto simp add: augpath_def cost_flow_network.Rcap_def)
    obtain Q where Q_prop:"fstv (hd Q) = s" "sndv (last Q) = t" 
                   "distinct Q" "set Q \<subseteq> set qq" "augpath (abstract_flow_map f) Q"
      using cost_flow_network.there_is_s_t_path[OF , OF qq_props(1-3) refl] by auto
    define Q' where "Q'  = map cost_flow_network.erev (rev Q)"
    have Q'_prop: "fstv (hd Q') = t" "sndv (last Q') = s" 
                   "distinct Q'" 
      using Q_prop(1,2,3,5)  
      by(auto simp add:Q'_def cost_flow_network.augpath_def cost_flow_network.prepath_def
                       hd_map[of "rev Q"] hd_rev last_map[of "rev Q"] last_rev
                       cost_flow_network.vs_erev distinct_map cost_flow_network.inj_erev o_def)
    have e_in_qq_E: "e \<in> set Q \<Longrightarrow> oedge e \<in> \<E>" for e 
      using Q_prop(4) e_in_qq_not_blocked not_blocked_in_E by auto
    have costsQ: "e \<in> set Q \<Longrightarrow>
         prod.snd (get_edge_and_costs_backward (a_not_blocked state) (abstract_flow_map f) (sndv e) (fstv e)) < PInfty" for e
     apply(rule order.strict_trans1)
      apply(rule conjunct1[OF get_edge_and_costs_backward_makes_cheaper[OF refl _ _ , 
         of e "a_not_blocked state" "abstract_flow_map f"]])
     using  e_in_qq_E  e_in_qq_not_blocked  e_in_qq_rcap Q_prop(4) 
     by(auto intro: prod.collapse)
   have costsQ': "e \<in> set Q' \<Longrightarrow>
         prod.snd (get_edge_and_costs_backward (a_not_blocked state) (abstract_flow_map f)
                    (fstv e) (sndv e)) < PInfty" for e
   proof(goal_cases)
     case 1
     have helper: "\<lbrakk> (\<And>e. e \<in> set Q \<Longrightarrow>
                   prod.snd (get_edge_and_costs_backward (a_not_blocked state) (abstract_flow_map f) (cost_flow_network.sndv e)
                    (cost_flow_network.fstv e)) \<noteq> \<infinity>); x \<in> set Q ; e = cost_flow_network.erev x;
                   prod.snd (get_edge_and_costs_backward (a_not_blocked state) (abstract_flow_map f)
                    (fstv (cost_flow_network.erev x)) (sndv (cost_flow_network.erev x))) = \<infinity>\<rbrakk>
                  \<Longrightarrow> False" for x e
        by(induction e rule: cost_flow_network.erev.induct,
              all \<open>induction x rule: cost_flow_network.erev.induct\<close>) fastforce+
      from 1 show ?thesis
       using costsQ
       by(auto simp add:  Q'_def intro: helper)
    qed
    have awalk:"awalk UNIV t (map cost_flow_network.to_vertex_pair Q') s"
    proof-
      have helper: "\<lbrakk> s = fstv (hd Q);  Q \<noteq> []; 0 < cost_flow_network.Rcap (abstract_flow_map f) (set Q);
           t = sndv (last Q); awalk UNIV (fstv (hd Q)) (map to_edge Q) (sndv (last Q))\<rbrakk> \<Longrightarrow>
          awalk UNIV (cost_flow_network.sndv (last Q)) (map (prod.swap \<circ> to_edge) (rev Q))
           (cost_flow_network.fstv (hd Q))"
      by(subst sym[OF list.map_comp], subst sym[OF rev_map])
        (auto simp add:  intro: awalk_UNIV_rev) 
     show ?thesis
      using  Q_prop(1) Q_prop(2) Q_prop(5)
      by (auto simp add: cost_flow_network.to_vertex_pair_erev_swap cost_flow_network.augpath_def 
            cost_flow_network.prepath_def Q'_def intro: helper)
     qed
     have "weight_backward (a_not_blocked state) (abstract_flow_map f)
                 (awalk_verts t (map cost_flow_network.to_vertex_pair Q')) < PInfty"
      using costsQ'  awalk Q'_prop(1) bellman_ford  knowledge(3) 
      by (intro path_flow_network_path_bf_backward[of Q' "a_not_blocked state" "abstract_flow_map f" t]) auto
    moreover have " (hd (awalk_verts t (map cost_flow_network.to_vertex_pair Q'))) = t"
      using awalk by simp
    moreover have "last (awalk_verts t (map cost_flow_network.to_vertex_pair Q')) = s" 
        using awalk by simp
      ultimately have " bellman_ford.OPT vs (\<lambda>u v. prod.snd (get_edge_and_costs_backward 
                       (a_not_blocked state) (a_current_flow state) u v)) (length vs - 1) t s < PInfty" 
        using t_not_s 1(3)
        by(intro bellman_ford.weight_le_PInfty_OPTle_PInfty[OF bellman_ford _ _ refl,
                    of _ "tl (butlast (awalk_verts t (map cost_flow_network.to_vertex_pair Q')))"],
              cases "awalk_verts t (map cost_flow_network.to_vertex_pair Q')" rule: list_cases_both_sides) auto
    moreover have "prod.snd (the (connection_lookup bf s)) \<le> 
            bellman_ford.OPT vs (\<lambda>u v. prod.snd (get_edge_and_costs_backward
            (a_not_blocked state) (a_current_flow state) u v))
           (length vs - 1) t s"
      using bellman_ford.bellman_ford_shortest[OF bellman_ford, of t "length vs -1" s] vs_is_V
            knowledge(4) t_prop(2)
      by(auto simp add: bf_def bellman_ford_backward_def bellman_ford_algo_def
            bellman_ford_init_algo_def)
    ultimately have "prod.snd (the (connection_lookup bf s)) < PInfty" by auto
    hence "s \<in> set vs" "abstract_bal_map b s > \<epsilon> * current_\<gamma> state"
           "prod.snd (the (connection_lookup bf s)) < PInfty"
      using "2" knowledge(2) vs_is_V by (auto simp add: make_pairs_are)
    hence "(ss \<noteq> None)"
      using get_source_for_target_aux_aux(1)[of vs "current_\<gamma> state" "abstract_bal_map b"
                                             bf] knowledge(1) ss_def 
      by blast
    thus False
      using 2 by simp
  qed
  thus ?thesis 
    by(simp add: ss_def bf_def local.get_source_target_path_b_def
                  algo.abstract_not_blocked_map_def option.case_eq_if)
qed

abbreviation "impl_b_None_cond \<equiv> send_flow_spec.impl_b_None_cond"
lemmas impl_b_None_cond_def = send_flow_spec.impl_b_None_cond_def
lemmas impl_b_None_condE= send_flow_spec.impl_b_None_condE

lemma impl_b_None:
  "impl_b_None_cond state t b \<gamma> f\<Longrightarrow>
   (\<not> (\<exists>s\<in>VV. \<epsilon> * \<gamma> < abstract_bal_map b s \<and> resreach (abstract_flow_map f) s t)) =
     (get_source_target_path_b state t = None)"
  using  impl_b_None_aux[OF refl refl refl]
  by (auto elim!: impl_b_None_condE)

lemma test_all_vertices_zero_balance_aux:
  "test_all_vertices_zero_balance_aux b xs \<longleftrightarrow> (\<forall> x \<in> set xs. b x = 0)"
  by(induction b xs rule: test_all_vertices_zero_balance_aux.induct) auto

lemma test_all_vertices_zero_balance:
 "b = balance state 
   \<Longrightarrow> test_all_vertices_zero_balance state = (\<forall>v\<in>VV. abstract_bal_map b v = 0)"
  using vs_is_V 
  by(auto simp add: test_all_vertices_zero_balance_def test_all_vertices_zero_balance_aux)

lemma send_flow_axioms:
   "send_flow_axioms snd \<u> \<E> \<c> \<emptyset>\<^sub>N vset_inv isin set_invar
     to_set lookup t_set adj_inv flow_lookup flow_invar bal_lookup bal_invar rep_comp_lookup
     rep_comp_invar conv_lookup conv_invar not_blocked_lookup not_blocked_invar \<b> \<epsilon> fst
     get_source_target_path_a get_source_target_path_b get_source get_target
     test_all_vertices_zero_balance"
proof(rule send_flow_axioms.intro, goal_cases)
  case (1 state s t P b \<gamma> f)
  then show ?case 
    using get_source_target_path_a_ax by blast
next
  case (2 state s t P b \<gamma> f)
  then show ?case 
    using get_source_target_path_a_ax by blast
next
  case (3 state s t P b \<gamma> f)
  then show ?case 
    using get_source_target_path_a_ax by blast
next
  case (4 state s t P b \<gamma> f)
  then show ?case 
    using get_source_target_path_b_ax by blast
next
  case (5 state s t P b \<gamma> f)
  then show ?case 
    using get_source_target_path_b_ax by blast
next
  case (6 state s t P b \<gamma> f)
  then show ?case 
    using get_source_target_path_b_ax by blast
next
  case (7 s state b \<gamma>)
  then show ?case 
    using get_source_axioms by blast
next
  case (8 state b \<gamma>)
  then show ?case 
    using get_source_axioms by blast
next
  case (9 t state b \<gamma>)
  then show ?case
    using get_target_axioms by blast
next
  case (10 state b \<gamma>)
  then show ?case
    using get_target_axioms by blast
next
  case (11 state s b \<gamma> f)
  then show ?case 
    using impl_a_None by (auto simp add: make_pairs_are)
next
  case (12 state t b \<gamma> f)
  then show ?case 
    using impl_b_None by (auto simp add: make_pairs_are)
next
  case (13 state b)
  then show ?case
    using test_all_vertices_zero_balance by (auto simp add: make_pairs_are)
qed

interpretation send_flow: 
 send_flow snd create_edge \<u> \<E> \<c> edge_map_update "\<emptyset>\<^sub>N"
           vset_delete vset_insert vset_inv isin filter are_all set_invar to_set lookup t_set 
           sel adj_inv flow_update flow_delete flow_lookup flow_invar bal_update bal_delete 
           bal_lookup bal_invar rep_comp_update rep_comp_delete rep_comp_lookup rep_comp_invar 
           conv_update conv_delete conv_lookup conv_invar not_blocked_update not_blocked_delete 
           not_blocked_lookup  not_blocked_invar rep_comp_upd_all flow_update_all not_blocked_upd_all local.\<b> get_max local.\<epsilon>
           \<E>_impl "\<emptyset>\<^sub>G" N fst get_from_set flow_empty bal_empty rep_comp_empty conv_empty
           not_blocked_empty get_source_target_path_a get_source_target_path_b
           get_source local.get_target test_all_vertices_zero_balance
  by(auto intro!: send_flow.intro 
        simp add: send_flow algo send_flow_axioms)

interpretation rep_comp_map2:
 Map where empty = rep_comp_empty and update=rep_comp_update and lookup= rep_comp_lookup
       and delete= rep_comp_delete and invar = rep_comp_invar
  using Map_axioms by fastforce

lemma init_impl_variables:
      "\<And> xs. flow_invar (foldr (\<lambda> x fl. flow_update x (0::real) fl) xs flow_empty)"
      "\<And> ys. dom (flow_lookup (foldr (\<lambda> x fl. flow_update x  (0::real) fl) ys flow_empty)) = set ys"
      "\<And> vs. rep_comp_invar (foldr (\<lambda> x fl. rep_comp_update x  (x,1::nat) fl) vs (rep_comp_empty))"
      "\<And> vs. dom (rep_comp_lookup (foldr (\<lambda> x fl. rep_comp_update x  (x,1::nat) fl) vs rep_comp_empty)) = set vs"
      "\<And> vs. not_blocked_invar (foldr (\<lambda> x fl. not_blocked_update x False fl) vs ((((not_blocked_empty)))))"
      "\<And> vs. dom (not_blocked_lookup (foldr (\<lambda> x fl. not_blocked_update x False fl) vs ((((not_blocked_empty)))) ))
              = set vs"
      "\<And> vs. e \<in> dom (not_blocked_lookup (foldr (\<lambda> x fl. not_blocked_update x False fl) vs ((((not_blocked_empty)))))) 
             \<Longrightarrow> not_blocked_lookup (foldr (\<lambda> x fl. not_blocked_update x False fl) vs ((((not_blocked_empty))))) e = Some False"
  subgoal 1 for xs
  by(induction xs)
    (auto intro: Map_flow.invar_empty Map_flow.invar_update)
  subgoal 2 for ys
    using 1 by(induction ys)
     (auto simp add: Map_flow.map_update Map_flow.map_empty dom_def)
  subgoal 3 for vs
    by(induction vs)
      (auto intro: invar_empty invar_update)
  subgoal 4 for vs
    using 3 by(induction vs)
              (auto simp add: map_update map_empty dom_def)
  subgoal 5 for es 
    by(induction es)
      (auto intro: Map_not_blocked.invar_empty Map_not_blocked.invar_update)
  subgoal 6 for vs
    using 5 by(induction vs)
              (auto simp add: Map_not_blocked.map_update Map_not_blocked.map_empty dom_def)
  subgoal 7 for vs
    using 5 by(induction vs)
              (auto simp add: Map_not_blocked.map_update Map_not_blocked.map_empty dom_def)
done

lemma orlins_axioms:
    "orlins_axioms snd \<E> flow_lookup flow_invar bal_lookup bal_invar rep_comp_lookup
                   rep_comp_invar not_blocked_lookup not_blocked_invar \<b> get_max fst init_flow
                   init_bal init_rep_card init_not_blocked"
proof(rule orlins_axioms.intro, goal_cases)
  case 2
  then show ?case 
    by (simp add: init_impl_variables(1) local.init_flow_def)
next
  case 1
  then show ?case 
    using local.get_max by force
next
  case 4
  then show ?case
    using invar_b_impl local.init_bal_def by auto
next
  case 5
  then show ?case
    by (simp add: b_impl_dom local.\<E>_def local.init_bal_def make_pairs_are)
next
  case (6 x)
  then show ?case 
    by (simp add: b_impl_dom domIff local.\<E>_def local.\<b>_def local.init_bal_def make_pairs_are)
next
  case 7
  then show ?case 
    using init_impl_variables(3) local.init_rep_card_def by auto
next
  case 8
  then show ?case 
    using init_impl_variables(4) local.init_rep_card_def vs_is_V by(auto simp add: make_pairs_are)
next
  case 9
  then show ?case 
    by (simp add: init_impl_variables(5) local.init_not_blocked_def)
next
  case 10
  then show ?case
    using \<E>_impl_invar init_impl_variables(6) local.algo.\<E>_impl_meaning(1) local.ees_def local.init_not_blocked_def local.to_list(1) by force
next
  case (11 e)
  then show ?case
    by (simp add: init_impl_variables(7) local.init_not_blocked_def)
next
  case 3
  thus ?case
    by(simp add: local.\<E>_def  init_flow_def init_impl_variables(2) ees_def
                 \<E>_impl_invar local.to_list(1))
qed

interpretation orlins: 
  Orlins.orlins snd  create_edge \<u> \<E> \<c> edge_map_update vset_empty vset_delete vset_insert
     vset_inv isin filter are_all set_invar to_set lookup t_set sel adj_inv flow_empty
     flow_update flow_delete flow_lookup flow_invar bal_empty bal_update bal_delete bal_lookup
     bal_invar rep_comp_empty rep_comp_update rep_comp_delete rep_comp_lookup rep_comp_invar
     conv_empty conv_update conv_delete conv_lookup conv_invar not_blocked_update not_blocked_empty
     not_blocked_delete not_blocked_lookup not_blocked_invar rep_comp_upd_all flow_update_all
     not_blocked_upd_all \<b> get_max \<epsilon> N get_from_set map_empty \<E>_impl get_path fst
     get_source_target_path_a get_source_target_path_b get_source get_target
     test_all_vertices_zero_balance init_flow init_bal init_rep_card init_not_blocked
  by(auto intro!: orlins.intro
        simp add: maintain_forest.maintain_forest_axioms
                  send_flow.send_flow_axioms send_flow
                  maintain_forest.maintain_forest_spec_axioms orlins_spec_def
                  orlins_axioms)

definition "orlins_initial  = orlins.initial"
definition "maintain_forest_loop_impl =  maintain_forest.maintain_forest_impl "
definition "send_flow_loop_impl = send_flow_spec.send_flow_impl"
definition "orlins_loop_impl = orlins.orlins_impl"
definition "final_state = orlins_loop_impl (send_flow_loop_impl orlins_initial)"
definition "final_flow_impl = current_flow final_state"

corollary correctness_of_implementation:
 "return final_state = success \<Longrightarrow> cost_flow_network.is_Opt  \<b> (abstract_flow_map final_flow_impl)"
 "return final_state = infeasible \<Longrightarrow>  \<nexists> f. cost_flow_network.isbflow f \<b>"
 "return final_state = notyetterm \<Longrightarrow>  False"
  using  orlins.initial_state_orlins_dom_and_results[OF refl]
  by(auto simp add: final_state_def send_flow_loop_impl_def orlins_loop_impl_def
                    orlins_initial_def final_flow_impl_def)
(*
lemma final_flow_domain: "dom (flow_lookup final_flow_impl) = \<E>"
  
  using orlins_impl.final_flow_domain
  by(auto simp add: final_flow_impl_def final_state_def abstract_flow_map_def
 orlins_loop_impl_def initial_state_impl_def send_flow_loop_impl_def)
*)
end
end

definition "no_cycle_cond fst snd \<c>_impl \<E>_impl c_lookup =
            (\<not> has_neg_cycle (multigraph_spec.make_pair fst snd) 
                (function_generation.\<E> \<E>_impl to_set) (function_generation.\<c> \<c>_impl c_lookup))" 
  for fst snd

lemma no_cycle_condI:
"(\<And> D. \<lbrakk>closed_w ((multigraph_spec.make_pair fst snd) `   (function_generation.\<E> \<E>_impl to_set))
          (map (multigraph_spec.make_pair fst snd) D);
        foldr (\<lambda>e. (+) ( (function_generation.\<c> \<c>_impl c_lookup) e)) D 0 < 0 ;
        set D \<subseteq>   (function_generation.\<E> \<E>_impl to_set)\<rbrakk> \<Longrightarrow> False)
    \<Longrightarrow> no_cycle_cond fst snd \<c>_impl \<E>_impl c_lookup" for fst snd
  by(auto simp add: no_cycle_cond_def has_neg_cycle_def)

term \<open>multigraph_spec.make_pair fst snd\<close>
thm function_generation_proof_axioms_def

lemma function_generation_proof_axioms:
"\<lbrakk>set_invar \<E>_impl; bal_invar \<b>_impl;
  dVs (multigraph_spec.make_pair fst snd ` to_set \<E>_impl) = dom (bal_lookup \<b>_impl);
  0 < function_generation.N \<E>_impl to_list fst snd\<rbrakk>
   \<Longrightarrow> function_generation_proof_axioms bal_lookup bal_invar 
       \<E>_impl to_list \<b>_impl set_invar to_set  fst snd get_max" for fst snd
  by(intro function_generation_proof_axioms.intro)
    (auto simp add: to_list \<E>_def \<c>_def no_cycle_cond_def
      get_max multigraph_spec.make_pair_def selection_functions.make_pair_def)

interpretation rep_comp_iterator: Map_iterator rep_comp_invar rep_comp_lookup rep_comp_upd_all
  using Map_iterator_def rep_comp_upd_all by blast
lemmas rep_comp_iterator=rep_comp_iterator.Map_iterator_axioms

interpretation flow_iterator: Map_iterator flow_invar flow_lookup flow_update_all
  using Map_iterator_def flow_update_all  by blast
lemmas flow_iterator=flow_iterator.Map_iterator_axioms

interpretation not_blocked_iterator: 
  Map_iterator not_blocked_invar not_blocked_lookup not_blocked_upd_all
  using Map_iterator_def not_blocked_upd_all  by blast
lemmas not_blocked_iterator = not_blocked_iterator.Map_iterator_axioms

definition "final_state fst snd create_edge \<E>_impl \<c>_impl \<b>_impl c_lookup =
                    orlins_impl fst snd create_edge \<E>_impl \<c>_impl c_lookup
                    (send_flow_impl fst snd create_edge \<E>_impl \<c>_impl c_lookup
                            (initial fst snd \<E>_impl \<b>_impl))" for fst snd

definition "final_flow_impl fst snd create_edge \<E>_impl \<c>_impl \<b>_impl c_lookup=
                 (current_flow
                (final_state  fst snd create_edge \<E>_impl \<c>_impl \<b>_impl c_lookup))" for fst snd

definition "abstract_flow_map = algo_spec.abstract_flow_map flow_lookup"

locale correctness_of_algo =
  fixes fst snd::"('edge::linorder) \<Rightarrow> ('a::linorder)"
  and \<c>_impl:: 'c_impl
  and  \<E>_impl::"('edge::linorder) list" and create_edge 
  and \<b>_impl:: "(('a::linorder \<times> real) \<times> color) tree"
  and c_lookup::"'c_impl \<Rightarrow> 'edge \<Rightarrow> real option"

assumes \<E>_impl_basic: "set_invar \<E>_impl" " bal_invar (\<b>_impl)"
  and  Vs_is_bal_dom: "dVs (multigraph_spec.make_pair fst snd ` to_set \<E>_impl) = dom (bal_lookup \<b>_impl)"
  and at_least_2_verts: "0 < function_generation.N \<E>_impl to_list fst snd"
  and multigraph: "multigraph fst snd create_edge (function_generation.\<E> \<E>_impl to_set)"
begin

interpretation function_generation_proof:
 function_generation_proof realising_edges_empty realising_edges_update realising_edges_delete
     realising_edges_lookup realising_edges_invar bal_empty bal_delete bal_lookup bal_invar 
     flow_empty flow_delete flow_lookup flow_invar not_blocked_empty not_blocked_delete 
     not_blocked_lookup not_blocked_invar rep_comp_empty rep_comp_delete rep_comp_lookup 
     rep_comp_invar \<E>_impl to_list create_edge \<c>_impl \<b>_impl c_lookup filter are_all set_invar
     get_from_set to_set  fst snd rep_comp_update conv_empty conv_delete conv_lookup
     conv_invar conv_update not_blocked_update flow_update bal_update rep_comp_upd_all 
     flow_update_all not_blocked_upd_all get_max
  using  \<E>_impl_basic at_least_2_verts gt_zero multigraph
         rep_comp_iterator flow_iterator not_blocked_iterator  
  by(auto intro!:  function_generation_proof_axioms function_generation_proof.intro 
        simp add: flow_map.Map_axioms Map_not_blocked.Map_axioms Set_with_predicate \<E>_def Adj_Map_Specs2
                  Map_rep_comp Map_conv   bal_invar_b Vs_is_bal_dom 
                  Map_realising_edges function_generation.intro bal_map.Map_axioms) 

lemmas function_generation_proof = function_generation_proof.function_generation_proof_axioms
context   
  assumes no_cycle: "no_cycle_cond fst snd \<c>_impl \<E>_impl c_lookup"
begin

lemma no_cycle_cond:"function_generation_proof.no_cycle_cond "
  using no_cycle
  unfolding no_cycle_cond_def  function_generation_proof.no_cycle_cond_def
  function_generation_proof.multigraph.make_pair_def selection_functions.make_pair_def
  by simp

corollary correctness_of_implementation:
 "return (final_state fst snd create_edge \<E>_impl \<c>_impl \<b>_impl c_lookup) = success \<Longrightarrow>  
        cost_flow_spec.is_Opt fst snd  \<u> (\<E> \<E>_impl) (\<c> \<c>_impl c_lookup) (\<b> \<b>_impl) 
 (abstract_flow_map (final_flow_impl fst snd create_edge \<E>_impl \<c>_impl \<b>_impl c_lookup))"
 "return (final_state  fst snd create_edge \<E>_impl \<c>_impl \<b>_impl c_lookup) = infeasible \<Longrightarrow> 
         \<nexists> f. flow_network_spec.isbflow  fst snd (\<E> \<E>_impl) \<u>  f (\<b> \<b>_impl)"
 "return (final_state fst snd create_edge \<E>_impl \<c>_impl \<b>_impl c_lookup) = notyetterm \<Longrightarrow>  
         False"
  using  function_generation_proof.correctness_of_implementation[OF  no_cycle_cond] 
  by(auto simp add: final_state_def 
                function_generation_proof.final_state_def[OF  no_cycle_cond]
                function_generation_proof.orlins_loop_impl_def[OF  no_cycle_cond]
                orlins_impl_def send_flow_impl_def N_def get_source_target_path_a_def
                get_source_target_path_b_def get_source_def get_target_def get_path_def
                test_all_vertices_zero_balance_def 
                function_generation_proof.send_flow_loop_impl_def[OF  no_cycle_cond] initial_def 
                function_generation_proof.orlins_initial_def[OF  no_cycle_cond] init_flow_def
                init_bal_def init_rep_card_def init_not_blocked_def abstract_flow_map_def final_flow_impl_def
                function_generation_proof.final_flow_impl_def[OF  no_cycle_cond]
                \<E>_def \<b>_def \<c>_def \<u>_def)
(*
lemma final_flow_domain:
 "dom (flow_lookup (final_flow_impl  make_pair create_edge \<E>_impl \<c>_impl \<b>_impl c_lookup)) = \<E> \<E>_impl"
  using function_generation_proof.final_flow_domain[OF no_cycle_cond]
     by(auto simp add: final_state_def 
                function_generation_proof.final_state_def[OF no_cycle_cond]
                function_generation_proof.orlins_loop_impl_def[OF no_cycle_cond]
                orlins_impl_def send_flow_impl_def N_def get_source_target_path_a_impl_def
                get_source_target_path_b_impl_def get_source_impl_def get_target_impl_def get_path_def
                test_all_vertices_zero_balance_def 
                function_generation_proof.send_flow_loop_impl_def[OF no_cycle_cond] initial_impl_def 
                function_generation_proof.initial_state_impl_def[OF no_cycle_cond] init_flow_def
                init_bal_def init_rep_card_def init_not_blocked_def final_flow_impl_def
                function_generation_proof.final_flow_impl_def[OF no_cycle_cond] \<E>_def )
*)
end
end
datatype 'a cost_wrapper = cost_container 'a
end