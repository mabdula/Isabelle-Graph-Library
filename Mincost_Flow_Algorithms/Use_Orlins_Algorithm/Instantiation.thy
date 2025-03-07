section \<open>Instantiation of Abstract Datatypes\<close>

theory Instantiation
  imports RBT_Map_Extension
          Directed_Set_Graphs.Pair_Graph_RBT
          Graph_Algorithms.Bellman_Ford_Example
          Graph_Algorithms.DFS_Example
          Mincost_Flow_Algorithms.Orlins_Implementation
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

definition "rep_comp_update_all = (update_all :: ('a \<Rightarrow> 'a \<times> nat \<Rightarrow> 'a \<times> nat)
   \<Rightarrow> (('a \<times> 'a \<times> nat) \<times> color) tree
      \<Rightarrow> (('a \<times> 'a \<times> nat) \<times> color) tree)"
definition "not_blocked_update_all = (update_all :: ('edge_type \<Rightarrow> bool \<Rightarrow> bool)
   \<Rightarrow> (('edge_type \<times> bool) \<times> color) tree
      \<Rightarrow> (('edge_type \<times> bool) \<times> color) tree)"
definition "flow_update_all = (update_all :: ('edge_type \<Rightarrow> real \<Rightarrow> real)
   \<Rightarrow> (('edge_type \<times> real) \<times> color) tree
      \<Rightarrow> (('edge_type \<times> real) \<times> color) tree)"

lemma  rep_comp_update_all: 
    "\<And> rep f. rep_comp_invar rep \<Longrightarrow> (\<And> x. x \<in> dom (rep_comp_lookup rep) 
                  \<Longrightarrow> rep_comp_lookup (rep_comp_update_all f rep) x =
                      Some (f x (the (rep_comp_lookup rep x))))"
    "\<And> rep f g. rep_comp_invar rep \<Longrightarrow> (\<And> x. x \<in> dom (rep_comp_lookup rep)  \<Longrightarrow>
                     f x (the (rep_comp_lookup rep x)) = g x (the (rep_comp_lookup rep x))) \<Longrightarrow>
          rep_comp_update_all f rep = rep_comp_update_all g rep "
   "\<And> rep f. rep_comp_invar rep \<Longrightarrow> rep_comp_invar (rep_comp_update_all f rep)"
   "\<And> rep f. rep_comp_invar rep \<Longrightarrow> dom (rep_comp_lookup (rep_comp_update_all f rep))
                              = dom (rep_comp_lookup rep)"
 and not_blocked_update_all: 
    "\<And> nblckd f. not_blocked_invar nblckd \<Longrightarrow> (\<And> x. x \<in> dom (not_blocked_lookup nblckd) 
                  \<Longrightarrow> not_blocked_lookup (not_blocked_update_all f nblckd) x =
                      Some (f x (the (not_blocked_lookup nblckd x))))"
    "\<And> nblckd f g. not_blocked_invar nblckd \<Longrightarrow> (\<And> x. x \<in> dom (not_blocked_lookup nblckd)  \<Longrightarrow>
                     f x (the (not_blocked_lookup nblckd x)) = g x (the (not_blocked_lookup nblckd x))) \<Longrightarrow>
          not_blocked_update_all f nblckd = not_blocked_update_all g nblckd "
   "\<And> nblckd f. not_blocked_invar nblckd \<Longrightarrow> not_blocked_invar (not_blocked_update_all f nblckd)"
   "\<And> nblckd f. not_blocked_invar nblckd \<Longrightarrow> dom (not_blocked_lookup (not_blocked_update_all f nblckd))
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
  by (auto simp add: rep_comp_lookup_def rep_comp_update_all_def rep_comp_invar_def 
                     M.invar_def  update_all(1)  color_no_change rbt_red_def rbt_def 
                     not_blocked_invar_def not_blocked_lookup_def not_blocked_update_all_def
                     flow_invar_def flow_lookup_def flow_update_all_def bal_invar_def
                     bal_update_def bal_lookup_def  to_list_def to_set_def set_invar_def
             intro!: update_all(2,3,4) get_max_correct)


datatype  'd dd = Replace 'd | all_empty

locale Map_default =
adjmap: Map empty  "edge_map_update::'b \<Rightarrow> 'c \<Rightarrow> 'a \<Rightarrow> 'a" delete lookup adjmap_inv
for empty edge_map_update delete lookup adjmap_inv +
fixes default::'c
begin

notation "empty" ("\<emptyset>\<^sub>G" 100)

fun edge_map_update' where 
 "(edge_map_update' e  val (Replace m)) = 
(if val = default then 
(let red =  (delete e m) in (if red = empty then all_empty else Replace red)) else 
Replace (edge_map_update e val m))" |
 "(edge_map_update' e  val all_empty) 
= (if val = default then all_empty else Replace (edge_map_update e val empty))"

fun lookup' where 
 "(lookup' (Replace m) e) = 
  (let val = lookup m e in (if val = None then Some default else val))"|
 "lookup' all_empty e = Some default"

fun adjmap_inv' where 
"adjmap_inv' (Replace m) = (adjmap_inv m \<and> m \<noteq> empty \<and> 
(\<forall> x y. lookup m x = Some y  \<longrightarrow> y \<noteq> default) \<and> finite (dom (lookup m)))" |
"adjmap_inv' all_empty  = True"

lemma map': "adjmap_inv' m  \<Longrightarrow> lookup' (edge_map_update' a b m) = (lookup' m)(a \<mapsto> b)"
            "adjmap_inv' m \<Longrightarrow> adjmap_inv' (edge_map_update' a b m)"
proof(goal_cases)
  case 1
  have help1: "\<lbrakk> m = Replace mp; b = default;adjmap_inv mp;mp \<noteq> delete a mp;
           \<forall>x y. lookup mp x = Some y \<longrightarrow> y \<noteq> default;finite (dom (lookup mp));
          \<emptyset>\<^sub>G = delete a mp\<rbrakk> \<Longrightarrow> lookup' all_empty = (lookup' (Replace mp))(a \<mapsto> default)" 
    for mp
        using adjmap.map_delete[of mp a]  adjmap.map_empty fun_upd_other[of _ a "lookup mp" None]  
        by auto 
  from 1 show ?case 
        using adjmap.map_delete[of _ a]  adjmap.map_update 
        by (cases m)(auto  intro: help1 simp add: adjmap.invar_delete adjmap.map_delete  adjmap.invar_empty adjmap.map_empty adjmap.map_update )  
  next
    case 2
    have help1: "\<lbrakk> m = Replace mp ; b \<noteq> default ; adjmap_inv mp ; mp \<noteq> edge_map_update a b mp;
                  \<forall>x y. lookup mp x = Some y \<longrightarrow> y \<noteq> default ; finite (dom (lookup mp));
                 \<emptyset>\<^sub>G = edge_map_update a b mp\<rbrakk> \<Longrightarrow> False"
      for mp
      using adjmap.map_empty adjmap.map_update[of mp  a b] by auto
    have help2: "\<lbrakk>m = all_empty ; b \<noteq> default ; edge_map_update a b (\<emptyset>\<^sub>G) = \<emptyset>\<^sub>G\<rbrakk> \<Longrightarrow> False"
       using adjmap.map_empty adjmap.map_update[of empty  a b]  adjmap.invar_empty map_upd_nonempty[of "lookup empty" a b] 
         by auto
   from 2 show ?case
     by (cases m)
        (auto simp add:  adjmap.invar_delete adjmap.map_delete  adjmap.invar_empty
                                adjmap.map_empty adjmap.map_update adjmap.invar_update 
                intro: help1 case_split[of "b = default"] help2)
 qed

fun remove_all_empties where 
"remove_all_empties (Replace m) = m"|
"remove_all_empties all_empty = empty"

lemma
remove_almost_all_empties: 
   "\<And> adjmap. adjmap_inv' adjmap \<Longrightarrow> finite {x. lookup (remove_all_empties adjmap) x \<noteq> None}"
   "\<And> adjmap x vset. adjmap_inv' adjmap \<Longrightarrow> lookup' adjmap x = Some vset \<Longrightarrow> vset \<noteq> default \<Longrightarrow>
                               lookup (remove_all_empties adjmap) x = Some vset"
   "\<And> adjmap x. adjmap_inv' adjmap \<Longrightarrow> lookup' adjmap x = None \<Longrightarrow> lookup (remove_all_empties adjmap) x = None"
   "\<And> adjmap x. adjmap_inv' adjmap \<Longrightarrow> lookup' adjmap x = Some default
                 \<Longrightarrow> lookup (remove_all_empties adjmap) x = None"
   "\<And> adjmap. adjmap_inv' adjmap \<Longrightarrow> adjmap_inv (remove_all_empties adjmap)"
  subgoal for adjmap
    by (cases adjmap)(auto simp add: dom_def adjmap.map_empty)
  subgoal for adjmap x vset
    by(cases adjmap)(auto simp add: Let_def, metis option.inject)
  subgoal for adjmap x
    by(cases adjmap)(auto simp add: Let_def, presburger)
  subgoal for adjmap x
    using  adjmap.map_empty
    by(cases adjmap)(auto simp add: Let_def dom_def split: if_split, metis)
  subgoal for adjmap
     using adjmap.invar_empty
     by(cases adjmap) auto
   done
lemmas [code] = remove_all_empties.simps lookup'.simps
                edge_map_update'.simps
end

interpretation adj: Map where empty = vset_empty and update=edge_map_update
and delete=delete and lookup= lookup and invar=adj_inv
  using RBT_Map.M.Map_axioms
  by(auto simp add: Map_def rbt_red_def rbt_def M.invar_def  edge_map_update_def adj_inv_def RBT_Set.empty_def )

lemmas Map_satisfied = adj.Map_axioms

global_interpretation map': Map_default where 
empty=map_empty and edge_map_update=edge_map_update and delete=delete
and  lookup=lookup and adjmap_inv= adj_inv and default = vset_empty
defines lookup'= map'.lookup' and edge_map_update'=map'.edge_map_update'
and remove_all_empties=map'.remove_all_empties
and adjmap_inv'=map'.adjmap_inv'
  using Map_satisfied
  by (auto intro: Map_default.intro simp add: map_empty_def RBT_Set.empty_def)

definition "to_pair S = (SOME e. {prod.fst e, prod.snd e} = S)"

lemmas Set_satisified = dfs.Graph.vset.set.Set_axioms

lemma Set_Choose_axioms: "Set_Choose_axioms vset_empty isin sel"
  apply(rule Set_Choose_axioms.intro)
  unfolding RBT_Set.empty_def  
  subgoal for s
    by(induction rule: sel.induct) auto
  done

lemmas Set_Choose_satisfied = dfs.Graph.vset.Set_Choose_axioms

interpretation Pair_Graph_Specs_satisfied: Pair_Graph_Specs map_empty RBT_Map.delete lookup vset_insert isin t_set sel
     edge_map_update adj_inv vset_empty vset_delete vset_inv
  using Set_Choose_satisfied Map_satisfied
  unfolding Pair_Graph_Specs_def
  by(auto simp add: Pair_Graph_Specs_def map_empty_def  RBT_Set.empty_def)

lemmas Pair_Graph_Specs_satisfied = Pair_Graph_Specs_satisfied.Pair_Graph_Specs_axioms

lemmas Set2_satisfied = dfs.set_ops.Set2_axioms

definition "realising_edges_empty = (vset_empty::((('a ::linorder\<times> 'a) \<times> ('edge_type list)) \<times> color) tree)"
definition "realising_edges_update = update"
definition "realising_edges_delete = RBT_Map.delete"
definition "realising_edges_lookup = lookup"
definition "realising_edges_invar = M.invar"

interpretation Map_realising_edges: Map realising_edges_empty realising_edges_update realising_edges_delete realising_edges_lookup realising_edges_invar
  using RBT_Map.M.Map_axioms     
  by(auto simp add: realising_edges_update_def realising_edges_empty_def  realising_edges_delete_def
                    realising_edges_lookup_def realising_edges_invar_def)

lemmas Map_realising_edges = Map_realising_edges.Map_axioms

lemmas Map_connection = Map_connection.Map_axioms

lemmas bellman_ford_spec = bellford.bellman_ford_spec_axioms

locale function_generation =
Map_realising: Map realising_edges_empty "realising_edges_update::('a\<times> 'a) \<Rightarrow> 'edge_type list \<Rightarrow> 'realising_type \<Rightarrow> 'realising_type"
        realising_edges_delete realising_edges_lookup realising_edges_invar +
Map_bal: Map bal_empty "bal_update::'a \<Rightarrow> real \<Rightarrow> 'bal_impl \<Rightarrow> 'bal_impl" bal_delete bal_lookup bal_invar +
Map_flow: Map "flow_empty::'flow_impl" "flow_update::'edge_type \<Rightarrow> real \<Rightarrow> 'flow_impl \<Rightarrow> 'flow_impl" flow_delete 
flow_lookup flow_invar +
 Map_not_blocked: Map not_blocked_empty "not_blocked_update::'edge_type \<Rightarrow> bool \<Rightarrow> 'nb_impl \<Rightarrow> 'nb_impl" not_blocked_delete not_blocked_lookup 
not_blocked_invar +
Map rep_comp_empty "rep_comp_update::'a \<Rightarrow> ('a \<times> nat) \<Rightarrow> 'rcomp_impl \<Rightarrow> 'rcomp_impl" rep_comp_delete rep_comp_lookup rep_comp_invar 
for realising_edges_empty realising_edges_update realising_edges_delete realising_edges_lookup realising_edges_invar
 bal_empty bal_update bal_delete bal_lookup bal_invar flow_empty flow_update flow_delete flow_lookup flow_invar
not_blocked_empty not_blocked_update not_blocked_delete not_blocked_lookup 
not_blocked_invar rep_comp_empty rep_comp_update rep_comp_delete rep_comp_lookup rep_comp_invar+
fixes \<E>_impl::'edge_type_set_impl 
and to_list:: "'edge_type_set_impl \<Rightarrow> 'edge_type list"
and make_pair::"'edge_type \<Rightarrow> ('a::linorder) \<times> 'a" 
and fst::"'edge_type \<Rightarrow> 'a" 
and snd::"'edge_type \<Rightarrow> 'a"
and create_edge::"'a \<Rightarrow> 'a \<Rightarrow> 'edge_type"
and \<c>_impl::'c_impl
and  \<b>_impl::'bal_impl
and to_set::"'edge_type_set_impl \<Rightarrow> 'edge_type set"
and c_lookup::"'c_impl \<Rightarrow> 'edge_type \<Rightarrow> real option"
begin

definition "\<u> = (\<lambda> e::'edge_type. PInfty)"  
definition "\<c> e = (case (c_lookup \<c>_impl e)  of Some c \<Rightarrow> c | None \<Rightarrow> 0)"
definition \<E> where "\<E> = to_set \<E>_impl"
definition "N = length (remdups (map fst (to_list \<E>_impl) @ map snd  (to_list \<E>_impl)))"
definition "\<epsilon> = 1 / (max 3 (real N))"

definition "\<b> = (\<lambda> v. if bal_lookup \<b>_impl v \<noteq> None then the (bal_lookup \<b>_impl v) else 0)"
abbreviation "EEE \<equiv> flow_network.\<EE> \<E>"
abbreviation "fstv == flow_network_spec.fstv fst snd"
abbreviation "sndv == flow_network_spec.sndv fst snd"

abbreviation "VV \<equiv> dVs (make_pair ` \<E>)"

definition default_conv_to_rdg::"'a \<times> 'a \<Rightarrow> 'edge_type flow_network_spec.Redge"  where
"default_conv_to_rdg e = (case e of (u, v) \<Rightarrow> (let oedg = to_pair {u, v} in (
                                if oedg = (u, v) then flow_network_spec.F (create_edge u v)
                                else flow_network_spec.B (create_edge v u))))"
                                
definition "es = remdups(map make_pair (to_list \<E>_impl)@(map prod.swap (map make_pair (to_list \<E>_impl))))"
                                
                                
definition "vs = remdups (map prod.fst es)"

definition "dfs F t = (dfs.DFS_impl (remove_all_empties F) (\<lambda> w. w = t))" for F
definition "dfs_initial s = (dfs.initial_state  s)"

definition "get_path u v E = rev (stack (dfs E v (dfs_initial u)))"

fun get_source_aux_aux where 
"get_source_aux_aux b \<gamma> [] = None"|
"get_source_aux_aux b \<gamma> (v#xs) =
 (if b v > (1 - \<epsilon>) * \<gamma> then Some v else 
           get_source_aux_aux b \<gamma> xs)"

definition "get_source_aux b \<gamma> xs = the (get_source_aux_aux  b \<gamma> xs)"

fun get_target_aux_aux where 
"get_target_aux_aux b \<gamma> [] = None"|
"get_target_aux_aux b \<gamma> (v#xs) =
 (if b v < - (1 - \<epsilon>) * \<gamma> then Some v else 
           get_target_aux_aux b \<gamma> xs)"

definition "get_target_aux b \<gamma> xs = the (get_target_aux_aux b \<gamma> xs)"

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
                                   
                                   
definition "get_edge_and_costs_forward nb (f::'edge_type \<Rightarrow> real) = 
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
                  in (if cf \<le> cb then
                      (flow_network_spec.F ef, cf)
                      else (flow_network_spec.B eb, cb))))"
                      
                      
definition "get_edge_and_costs_backward nb (f::'edge_type \<Rightarrow> real) = 
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
                  in (if cf \<le> cb then
                      (flow_network_spec.F ef, cf)
                      else (flow_network_spec.B eb, cb))))"

definition "bellman_ford_forward nb (f::'edge_type \<Rightarrow> real) s =
         bellman_ford_algo (\<lambda> u v. prod.snd (get_edge_and_costs_forward nb f u v)) es (length vs - 1)
                                    (bellman_ford_init_algo vs s)"

definition "bellman_ford_backward nb (f::'edge_type \<Rightarrow> real) s =
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

fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"itrev [] ys = ys" |
"itrev (x #xs) ys = itrev xs (x #ys)"

definition "get_source_impl state = get_source_aux_aux
 (\<lambda> v. the (bal_lookup (balance_impl state) v)) (current_\<gamma>_impl state) vs"
 
definition "get_target_impl state = get_target_aux_aux
 (\<lambda> v. the (bal_lookup (balance_impl state) v)) (current_\<gamma>_impl state) vs"
  
abbreviation "TB opt \<equiv> (case opt of None \<Rightarrow> False
                                | Some x \<Rightarrow> x)"

definition "get_source_target_path_a_impl state s =
      (let bf = bellman_ford_forward (\<lambda> e. TB (not_blocked_lookup (not_blocked_impl state) e))
                                     (\<lambda> e. the (flow_lookup (current_flow_impl state) e)) s
      in
            case (get_target_for_source_aux_aux bf (\<lambda> v. the (bal_lookup (balance_impl state) v))
                                           (current_\<gamma>_impl state) vs) of 
            Some t \<Rightarrow> (let Pbf = search_rev_path_exec s bf t Nil;
                             P = (map (\<lambda>e. prod.fst (get_edge_and_costs_forward 
                                 (\<lambda> e. TB (not_blocked_lookup (not_blocked_impl state) e))
                                  (\<lambda> e. the (flow_lookup (current_flow_impl state) e)) (prod.fst e) (prod.snd e)))
                                      (edges_of_vwalk Pbf)) 
                       in Some (t, P))|
            None \<Rightarrow> None)"


definition "rev' xs = itrev xs Nil"

definition "get_source_target_path_b_impl state t =
      (let bf = bellman_ford_backward (\<lambda> e. TB (not_blocked_lookup (not_blocked_impl state) e))
                                     (\<lambda> e. the (flow_lookup (current_flow_impl state) e)) t
       in case ( get_source_for_target_aux_aux bf (\<lambda> v. the (bal_lookup (balance_impl state) v))
                                           (current_\<gamma>_impl state) vs) of
          Some s \<Rightarrow> let Pbf =rev' (search_rev_path_exec t bf s Nil);
                         P = (map (\<lambda>e. prod.fst (get_edge_and_costs_backward 
                                 (\<lambda> e. TB (not_blocked_lookup (not_blocked_impl state) e))
                                  (\<lambda> e. the (flow_lookup (current_flow_impl state) e)) (prod.snd e) (prod.fst e)))
                                        (edges_of_vwalk Pbf)) 
                    in Some (s, P) |
          None \<Rightarrow> None)"


fun test_all_vertices_zero_balance_aux where
"test_all_vertices_zero_balance_aux b Nil = True"|
"test_all_vertices_zero_balance_aux b (x#xs) = (b x = 0 \<and> test_all_vertices_zero_balance_aux b xs)"

definition "test_all_vertices_zero_balance state_impl = 
            test_all_vertices_zero_balance_aux (\<lambda> x. the (bal_lookup (balance_impl state_impl) x)) vs"

definition "ees = to_list \<E>_impl"
definition "init_flow = foldr (\<lambda> x fl. flow_update x  0 fl) ees flow_empty"
definition "init_bal = \<b>_impl"
definition "init_rep_card = foldr (\<lambda> x fl. rep_comp_update x  (x,1) fl) vs rep_comp_empty"
definition "init_not_blocked = foldr (\<lambda> x fl. not_blocked_update x False fl) ees not_blocked_empty"
end

lemmas Set_Choose = Set_Choose_satisfied

lemmas map' = map'.map'

interpretation Adj_Map_Specs2: Adj_Map_Specs2 lookup' t_set sel edge_map_update' adjmap_inv' vset_empty vset_delete vset_insert
     vset_inv isin 
  using Set_Choose map'
  by(auto intro:  Adj_Map_Specs2.intro simp add:  RBT_Set.empty_def  Adj_Map_Specs2_def Map'_def)

lemmas Adj_Map_Specs2 = Adj_Map_Specs2.Adj_Map_Specs2_axioms

lemma invar_filter: "\<lbrakk> set_invar s1\<rbrakk> \<Longrightarrow> set_invar(filter P s1)"
  by (simp add: set_invar_def)

lemma set_get:   "\<lbrakk> set_invar s1; \<exists> x. x \<in> to_set s1 \<and> P x \<rbrakk> \<Longrightarrow> \<exists> y. get_from_set P s1 = Some y"
                   "\<lbrakk> set_invar s1; get_from_set P s1 = Some x\<rbrakk> \<Longrightarrow> x \<in> to_set s1"
                   "\<lbrakk> set_invar s1; get_from_set P s1 = Some x\<rbrakk> \<Longrightarrow> P x"
                   "\<lbrakk> set_invar s1; \<And> x. x \<in> to_set s1 \<Longrightarrow> P x = Q x\<rbrakk> 
                     \<Longrightarrow> get_from_set P s1 = get_from_set Q s1" 
  using find_Some_iff[of P s1 x]  find_cong[OF refl, of s1 P Q] find_None_iff[of P s1]
  by (auto simp add: get_from_set_def set_invar_def to_set_def)

lemma are_all: "\<lbrakk> set_invar S\<rbrakk> \<Longrightarrow> are_all P S \<longleftrightarrow> (\<forall> x \<in> to_set S. P x)"
  unfolding to_set_def set_invar_def
  by(induction S) auto

interpretation Set3: Set3 get_from_set filter are_all set_invar to_set
  using set_filter invar_filter  set_get(1,2)
  by (auto intro!: filter_cong Set3.intro intro: set_get(3-) set_filter simp add: are_all to_set_def)
 fastforce+

lemmas Set3 = Set3.Set3_axioms

interpretation bal_map: Map where empty = bal_empty and update=bal_update and lookup= bal_lookup
and delete= bal_delete and invar = bal_invar
  using RBT_Map.M.Map_axioms
  by(auto simp add: bal_update_def bal_empty_def  bal_delete_def
                    bal_lookup_def bal_invar_def  M.invar_def Map_def rbt_red_def rbt_def)

lemmas Map_bal = bal_map.Map_axioms

interpretation Map_conv: Map conv_empty conv_update conv_delete conv_lookup conv_invar
  using RBT_Map.M.Map_axioms
  by(auto simp add: conv_update_def conv_empty_def  conv_delete_def
                    conv_lookup_def conv_invar_def  M.invar_def Map_def rbt_red_def rbt_def)

lemmas Map_conv = Map_conv.Map_axioms

interpretation flow_map: Map where empty = flow_empty and update=flow_update and lookup= flow_lookup
and delete= flow_delete and invar = flow_invar
  using RBT_Map.M.Map_axioms
  by(auto simp add: flow_update_def flow_empty_def  flow_delete_def
                    flow_lookup_def flow_invar_def  M.invar_def Map_def rbt_red_def rbt_def)

lemmas Map_flow = flow_map.Map_axioms

interpretation Map_not_blocked: 
 Map not_blocked_empty not_blocked_update not_blocked_delete not_blocked_lookup not_blocked_invar
  using RBT_Map.M.Map_axioms
  by(auto simp add: not_blocked_update_def not_blocked_empty_def  not_blocked_delete_def
                    not_blocked_lookup_def not_blocked_invar_def  M.invar_def Map_def rbt_red_def rbt_def)

lemmas Map_not_blocked = Map_not_blocked.Map_axioms

interpretation Map_rep_comp:Map rep_comp_empty rep_comp_update rep_comp_delete rep_comp_lookup rep_comp_invar
  using RBT_Map.M.Map_axioms
  by(auto simp add: rep_comp_update_def rep_comp_empty_def  rep_comp_delete_def
                    rep_comp_lookup_def rep_comp_invar_def  M.invar_def Map_def rbt_red_def rbt_def)

lemmas Map_rep_comp = Map_rep_comp.Map_axioms

global_interpretation selection_functions: function_generation
  where 
    realising_edges_empty= realising_edges_empty
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
and make_pair = make_pair
and fst=fst
and snd=snd
and create_edge=create_edge
and to_set = to_set
and \<E>_impl = \<E>_impl
and \<b>_impl = \<b>_impl
and \<c>_impl = \<c>_impl
and c_lookup = c_lookup
for fst snd create_edge make_pair \<E>_impl \<b>_impl \<c>_impl and c_lookup::"'c_impl \<Rightarrow> 'edge_type::linorder \<Rightarrow> real option"
defines get_source_target_path_a_impl= selection_functions.get_source_target_path_a_impl 
and get_source_target_path_b_impl =  selection_functions.get_source_target_path_b_impl 
and get_source_impl = selection_functions.get_source_impl 
and get_target_impl = selection_functions.get_target_impl 
and test_all_vertices_zero_balance = selection_functions.test_all_vertices_zero_balance 
and init_flow = selection_functions.init_flow 
and init_bal = selection_functions.init_bal 
and init_rep_card = selection_functions.init_rep_card 
and init_not_blocked = selection_functions.init_not_blocked 
and N = selection_functions.N
and default_conv_to_rdg=selection_functions.default_conv_to_rdg
and get_path = selection_functions.get_path 
and get_target_for_source_aux_aux=selection_functions.get_target_for_source_aux_aux
and get_source_for_target_aux_aux = selection_functions.get_source_for_target_aux_aux
and get_edge_and_costs_backward = selection_functions.get_edge_and_costs_backward
and get_edge_and_costs_forward = selection_functions.get_edge_and_costs_forward
and bellman_ford_backward =selection_functions.bellman_ford_backward
and bellman_ford_forward = selection_functions.bellman_ford_forward
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
  by(auto intro!: function_generation.intro simp add: Map_realising_edges Map_bal Map_flow Map_not_blocked Map_rep_comp)

lemmas function_generation = selection_functions.function_generation_axioms

global_interpretation orlins_impl_spec: orlins_impl_spec where
     edge_map_update =edge_map_update'
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
and lookup = lookup'
and t_set = t_set 
and sel=sel 
and adjmap_inv = adjmap_inv' 
and to_pair =to_pair  
and empty_forest= all_empty
and default_conv_to_rdg="default_conv_to_rdg create_edge"
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
and rep_comp_update_all = rep_comp_update_all
and not_blocked_update_all =  not_blocked_update_all 
and flow_update_all = flow_update_all 
and get_max = get_max 
and get_source_target_path_a_impl= 
    "get_source_target_path_a_impl (fst o make_pair) (snd o make_pair) 
                  create_edge make_pair \<E>_impl \<c>_impl c_lookup"
and get_source_target_path_b_impl =  
         "get_source_target_path_b_impl (fst o make_pair) (snd o make_pair) create_edge make_pair \<E>_impl \<c>_impl c_lookup"
and get_source_impl =  "get_source_impl (fst o make_pair) (snd o make_pair)  make_pair \<E>_impl"
and get_target_impl = "get_target_impl (fst o make_pair) (snd o make_pair)  make_pair \<E>_impl"
and test_all_vertices_zero_balance = "test_all_vertices_zero_balance make_pair \<E>_impl"
and init_flow = "init_flow \<E>_impl"
and init_bal = "init_bal \<b>_impl" 
and init_rep_card = "init_rep_card make_pair \<E>_impl"
and init_not_blocked = "init_not_blocked \<E>_impl"
and N = "N (fst o make_pair) (snd o make_pair) \<E>_impl"
and snd = "snd o make_pair" 
and fst = "fst o make_pair"
and create_edge = create_edge 
and make_pair = make_pair
and  \<c> = "\<c> \<c>_impl c_lookup"
and  \<E> = "\<E>  \<E>_impl"
and \<u> = \<u>
and \<b> = "\<b> \<b>_impl"
for  make_pair create_edge \<E>_impl \<b>_impl \<c>_impl c_lookup
defines initial_impl = orlins_impl_spec.initial_impl and
        orlins_impl = orlins_impl_spec.orlins_impl and
        loopB_impl = orlins_impl_spec.loopB_impl and
        loopA_impl =orlins_impl_spec.loopA_impl and
        augment_edges_impl = orlins_impl_spec.augment_edges_impl and
        to_redge_path_impl = orlins_impl_spec.to_redge_path_impl and
        augment_edge_impl=orlins_impl_spec.augment_edge_impl and
        add_direction = orlins_impl_spec.add_direction and
        move_balance = orlins_impl_spec.move_balance and
        move= orlins_impl_spec.move and
        insert_undirected_edge_impl = orlins_impl_spec.insert_undirected_edge_impl
  using  Map_bal Map_conv Map_flow Map_not_blocked
        Map_rep_comp
  by(auto intro!: orlins_impl_spec.intro algo_impl_spec.intro loopA_spec.intro rep_comp_update_all
                  loopB_impl_spec.intro loopA_impl_spec.intro flow_update_all get_max not_blocked_update_all
           intro: algo_impl_spec_axioms.intro
        simp add: Set3 Adj_Map_Specs2   algo_spec.intro)

lemmas orlins_impl_spec = orlins_impl_spec.orlins_impl_spec_axioms
lemmas loopB_impl_spec = orlins_impl_spec.loopB_impl_spec_axioms
lemmas algo_spec = orlins_impl_spec.algo_spec_axioms
lemmas loopA_impl_spec = orlins_impl_spec.loopA_impl_spec_axioms
lemmas algo_impl_spec = orlins_impl_spec.algo_impl_spec_axioms
lemmas loopA_spec = orlins_impl_spec.loopA_spec_axioms

subsection \<open>Proofs\<close>

lemma set_filter:   "\<lbrakk> set_invar s1 \<rbrakk> \<Longrightarrow> to_set(filter P s1) = to_set s1 - {x. x \<in> to_set s1 \<and> \<not> P x}"
                          "\<lbrakk> set_invar s1; \<And> x. x \<in> to_set s1 \<Longrightarrow> P x =  Q x \<rbrakk> 
                           \<Longrightarrow> filter P s1 = filter Q s1"
  using filter_cong[OF refl, of s1 P Q]
  by (auto simp add: set_invar_def to_set_def)

lemma flow_invar_Leaf: "flow_invar Leaf"
  by (metis RBT_Set.empty_def flow_empty_def flow_map.invar_empty)

lemma flow_invar_fold: "flow_invar T \<Longrightarrow>
        (\<And> T e. flow_invar T \<Longrightarrow> flow_invar (f e T)) \<Longrightarrow>
        flow_invar ( foldr (\<lambda> e tree. f e tree) list T)"
  by(induction list) auto

lemma dom_fold:"flow_invar T \<Longrightarrow>
         dom (flow_lookup (foldr (\<lambda> e tree. flow_update (f e) (g e) tree) AS T))
       = dom (flow_lookup T) \<union> f ` set AS"
  by(induction AS)
    (auto simp add: flow_map.map_update flow_invar_fold flow_map.invar_update)

lemma fold_lookup: "flow_invar T \<Longrightarrow>bij f \<Longrightarrow>
         flow_lookup (foldr (\<lambda> e tree. flow_update (f e) (g e) tree) AS T) x
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

lemma bal_invar_fold: "bal_invar bs \<Longrightarrow> 
bal_invar (foldr (\<lambda>xy tree.  bal_update  (g xy) (f xy tree) tree) ES bs)" 
  by(induction ES)(auto simp add: bal_map.invar_update)

lemma bal_dom_fold: "bal_invar bs \<Longrightarrow> 
dom (bal_lookup (foldr (\<lambda>xy tree.  bal_update  (g xy) (f xy tree) tree) ES bs))
= dom (bal_lookup bs) \<union> g ` (set ES)" 
  apply(induction ES)
  subgoal
    by auto
  by(simp add: dom_def, subst bal_map.map_update) (auto intro: bal_invar_fold)

interpretation rep_comp_map: Map where empty = rep_comp_empty and update=rep_comp_update and lookup= rep_comp_lookup
and delete= rep_comp_delete and invar = rep_comp_invar
  using Map_rep_comp by auto

interpretation conv_map: Map where empty = conv_empty and update=conv_update and lookup= conv_lookup
and delete= conv_delete and invar = conv_invar
  using Map_conv by auto

interpretation not_blocked_map: Map where empty = not_blocked_empty and update=not_blocked_update and lookup= not_blocked_lookup
and delete= not_blocked_delete and invar = not_blocked_invar
  using Map_not_blocked by auto

lemmas remove_almost_all_empties = map'.remove_almost_all_empties

lemma to_pair_axioms: "\<And> u v vs.  {u, v} = vs 
                                     \<Longrightarrow> to_pair vs = (u,v) \<or> to_pair vs = (v,u)"
proof(subst to_pair_def, goal_cases)
  case (1 u v vs)
  moreover define sel where "sel  = (SOME e. {prod.fst e, prod.snd e} = {u, v})"
  moreover have vs_is:"{prod.fst sel, prod.snd sel} = {u, v}"
    apply((subst sel_def)+, rule someI[of _ "(u, v)"])
    using 1 by (auto intro: someI[of _ "(u, v)"])
  ultimately show ?case
   by(auto simp add: to_pair_def sym[OF sel_def], metis doubleton_eq_iff prod.collapse)
qed

lemma bal_invar_b:"bal_invar (foldr (\<lambda> xy tree. update (prod.fst xy) (prod.snd xy) tree)
                     xs Leaf)"
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

lemma transform_to_sets_lookup_lookup':"adjmap_inv' E \<Longrightarrow>  (case lookup' E u of None \<Rightarrow> \<emptyset>\<^sub>N | Some vset \<Rightarrow> vset) =
       (case lookup (remove_all_empties E) u of None \<Rightarrow> \<emptyset>\<^sub>N | Some vset \<Rightarrow> vset)"
  by(cases E)
  (auto simp add:dfs.Graph.adjmap.map_empty  map'.adjmap.map_empty split: option.split)

hide_const RBT.B

locale function_generation_proof = 
function_generation where to_set =" to_set:: 'edge_type_set_impl \<Rightarrow> 'edge_type set"
      and make_pair = "make_pair :: 'edge_type \<Rightarrow> ('a::linorder) \<times> 'a"
      and not_blocked_update = "not_blocked_update ::'edge_type \<Rightarrow> bool \<Rightarrow> 'not_blocked_impl\<Rightarrow> 'not_blocked_impl"
      and flow_update =  "flow_update::'edge_type \<Rightarrow> real \<Rightarrow> 'f_impl \<Rightarrow> 'f_impl"
     and bal_update = "bal_update:: 'a \<Rightarrow> real \<Rightarrow> 'b_impl \<Rightarrow> 'b_impl" 
and  rep_comp_update="rep_comp_update:: 'a \<Rightarrow> 'a \<times> nat \<Rightarrow> 'r_comp_impl\<Rightarrow> 'r_comp_impl"+
Set3  where get_from_set="get_from_set::('edge_type \<Rightarrow> bool) \<Rightarrow>  'edge_type_set_impl \<Rightarrow> 'edge_type option"
         and to_set =to_set +

multigraph: multigraph fst snd make_pair create_edge \<E>+

Set3: Set3 get_from_set filter are_all set_invar to_set +

rep_comp_maper: Map  rep_comp_empty "rep_comp_update::'a \<Rightarrow> ('a \<times> nat) \<Rightarrow> 'r_comp_impl \<Rightarrow> 'r_comp_impl"
              rep_comp_delete rep_comp_lookup rep_comp_invar +
conv_map: Map  conv_empty "conv_update::'a \<times> 'a \<Rightarrow> 'edge_type flow_network_spec.Redge \<Rightarrow> 'conv_impl \<Rightarrow> 'conv_impl"
              conv_delete conv_lookup conv_invar +
not_blocked_map: Map  not_blocked_empty "not_blocked_update::'edge_type \<Rightarrow> bool \<Rightarrow> 'not_blocked_impl\<Rightarrow> 'not_blocked_impl"
              not_blocked_delete not_blocked_lookup not_blocked_invar +
rep_comp_iterator: Map_iterator rep_comp_invar rep_comp_lookup rep_comp_update_all+
flow_iterator: Map_iterator flow_invar flow_lookup flow_update_all+
not_blocked_iterator: Map_iterator not_blocked_invar not_blocked_lookup not_blocked_update_all
   for get_from_set  to_set  make_pair rep_comp_update conv_empty
conv_delete conv_lookup conv_invar conv_update not_blocked_update flow_update  bal_update 
 rep_comp_update_all flow_update_all not_blocked_update_all
          + 
fixes get_max::"('a \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> 'b_impl \<Rightarrow> real"
assumes  \<E>_impl_invar: "set_invar \<E>_impl"
and invar_b_impl: "bal_invar \<b>_impl"
and b_impl_dom: "dVs (make_pair ` to_set \<E>_impl) = dom (bal_lookup \<b>_impl)"
and N_gre_0: "N > 0"
and get_max: "\<And> b f. bal_invar b \<Longrightarrow> dom (bal_lookup b) \<noteq> {}
 \<Longrightarrow> get_max f b = Max {f y (the (bal_lookup b y)) | y. y \<in> dom (bal_lookup b)}"
and to_list: "\<And> E. set_invar E \<Longrightarrow> to_set E = set (to_list E)"
             "\<And> E. set_invar E \<Longrightarrow> distinct (to_list E)"
begin

lemmas rep_comp_update_all = rep_comp_iterator.update_all
lemmas flow_update_all = flow_iterator.update_all
lemmas not_blocked_update_all = not_blocked_iterator.update_all

notation vset_empty ("\<emptyset>\<^sub>N")

lemma vs_are: "dVs (make_pair ` \<E>) = set (map fst \<E>_list) \<union> set (map snd \<E>_list)"
  using multigraph.make_pair[OF refl refl] to_list \<E>_impl_invar
  by(auto simp add: \<E>_def \<E>_list_def dVs_def)

lemma \<E>_impl: "set_invar \<E>_impl"  "\<exists> e. e \<in> (to_set \<E>_impl)"
                  "finite \<E>"
and  b_impl: "bal_invar \<b>_impl" "dVs (make_pair ` (to_set \<E>_impl)) 
                  = dom (bal_lookup \<b>_impl)"
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
                  length_remdups_card_conv frac_le)
next
  case 9
  then show ?case
    by(auto simp add: \<epsilon>_def)
qed

lemma N_def': "N =card VV"
  using \<E>_impl_invar local.multigraph.make_pair' local.to_list(1)
 by(auto intro!: cong[of card, OF refl] 
         simp add:  N_def dVs_def \<E>_def to_set_def length_remdups_card_conv)

lemma \<E>_impl_basic: "set_invar \<E>_impl"  "\<exists> e. e \<in> (to_set \<E>_impl)"
                  "finite \<E>"
  using \<E>_impl by auto

interpretation cost_flow_network: cost_flow_network where \<E> = \<E> and \<c> = \<c> and \<u> = \<u>
and fst = fst and snd = snd and make_pair = make_pair and create_edge = create_edge
  using  \<E>_def multigraph.multigraph_axioms
  by(auto simp add: \<u>_def cost_flow_network_def flow_network_axioms_def flow_network_def)

lemmas cost_flow_network[simp] = cost_flow_network.cost_flow_network_axioms

abbreviation "\<cc> \<equiv> cost_flow_network.\<cc>"
abbreviation "F \<equiv> flow_network_spec.F"
abbreviation "B \<equiv> flow_network_spec.B"
abbreviation "to_edge == cost_flow_network.to_vertex_pair"
abbreviation "oedge == cost_flow_network.oedge"
abbreviation "rcap == cost_flow_network.rcap"

lemma default_conv_to_rdg: "cost_flow_network.consist default_conv_to_rdg"
  using to_pair_axioms[of , OF refl] flow_network_spec.Redge.simps(3,4) multigraph.create_edge
  by(auto split: prod.split simp add:  cost_flow_network.consist_def default_conv_to_rdg_def
     insert_commute) fastforce+

lemma make_pair_fst_snd: "make_pair e = (fst e, snd e)"
  using multigraph.make_pair' by simp

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
      by (auto simp add: e_pr(1) make_pair_fst_snd)
  qed
qed
 have 2:"x \<in> local.multigraph.\<V> \<Longrightarrow>
         x \<in> prod.fst ` (make_pair ` local.\<E> \<union> {(u, v). (v, u) \<in> make_pair ` local.\<E>})" for x
  proof(goal_cases)
    case 1
    note 2 = this
  then obtain a b where "x \<in>{a,b}" "(a,b) \<in> make_pair ` \<E>"
    by (meson in_dVsE(1) insertCI)
  then show ?case by force
qed
  show ?thesis
    by(auto intro: 1 2 simp add: vs_def  es_is_E)
qed

lemma vs_and_es: "vs \<noteq> []" "set vs = dVs (set es)" "distinct vs" "distinct es"
  using \<E>_def  es_is_E  vs_def vs_is_V es_is_E \<E>_impl_basic
  by (auto simp add: vs_def es_def dVs_def )

definition "no_cycle_cond =
        (\<forall> C. closed_w (make_pair ` function_generation.\<E> \<E>_impl to_set) (map make_pair C) \<longrightarrow>
         set C \<subseteq> function_generation.\<E> \<E>_impl to_set \<longrightarrow>
         foldr (\<lambda>e acc. acc + \<c> e) C 0 < 0 \<longrightarrow> False)"

context
  assumes no_cycle_cond: no_cycle_cond
begin
lemma  conservative_weights: "\<nexists> C. closed_w (make_pair ` \<E>) (map make_pair C) \<and> (set C \<subseteq> \<E>) \<and> foldr (\<lambda> e acc. acc + \<c> e) C 0 < 0"
  using no_cycle_cond no_cycle_cond_def by blast

lemma algo_axioms: " algo_axioms make_pair \<u> \<c> \<E> vset_empty set_invar to_set lookup' adjmap_inv' to_pair \<epsilon> \<E>_impl all_empty
     N default_conv_to_rdg"
  using to_pair_axioms \<epsilon>_axiom conservative_weights  \<E>_impl(1) default_conv_to_rdg 
  by(fastforce intro!: algo_axioms.intro simp add: \<u>_def \<E>_def N_def')+

lemmas dfs_defs = dfs.initial_state_def

lemma remove_all_empty_neighbourhood:
"adjmap_inv' (E::(('a \<times> ('a \<times> color) tree) \<times> color) tree dd) \<Longrightarrow>  (Adj_Map_Specs2.neighbourhood  E)

              =  (Pair_Graph_Specs.neighbourhood  lookup vset_empty (remove_all_empties E))"
  using transform_to_sets_lookup_lookup'[of E ]                  
 by(auto  simp add: Adj_Map_Specs2.digraph_abs_def Pair_Graph_Specs.digraph_abs_def
            Adj_Map_Specs2.neighbourhood_def Pair_Graph_Specs.neighbourhood_def[OF Pair_Graph_Specs_satisfied])
  
lemma remove_all_empty_digraph_abs:
"adjmap_inv' (E::(('a \<times> ('a \<times> color) tree) \<times> color) tree dd) \<Longrightarrow>  (Adj_Map_Specs2.digraph_abs E)
              =  (Pair_Graph_Specs.digraph_abs  lookup isin vset_empty (remove_all_empties E))"
  using transform_to_sets_lookup_lookup'[of E]
  by (auto simp add: Adj_Map_Specs2.digraph_abs_def Pair_Graph_Specs.digraph_abs_def[OF Pair_Graph_Specs_satisfied]
            Adj_Map_Specs2.neighbourhood_def Pair_Graph_Specs.neighbourhood_def[OF Pair_Graph_Specs_satisfied])

lemma loopA_axioms_extended: "vwalk_bet (Adj_Map_Specs2.digraph_abs  E) u q v \<Longrightarrow>
                       adjmap_inv' (E::(('a \<times> ('a \<times> color) tree) \<times> color) tree dd) \<Longrightarrow> p = get_path u v E \<Longrightarrow> 
                        u \<in> Vs ((Adj_Map_Specs2.to_graph ) E) \<Longrightarrow>
                        (\<And> x. lookup' E x \<noteq> None \<and> vset_inv (the (lookup' E x))) \<Longrightarrow> u \<noteq> v \<Longrightarrow>                      
                     vwalk_bet (Adj_Map_Specs2.digraph_abs  E) u p v"
"vwalk_bet (Adj_Map_Specs2.digraph_abs  E) u q v \<Longrightarrow> 
                       adjmap_inv' E \<Longrightarrow> p = get_path u v E \<Longrightarrow> 
                        u \<in> Vs ((Adj_Map_Specs2.to_graph ) E) \<Longrightarrow>
                        (\<And> x. lookup' E x \<noteq> None \<and> vset_inv (the (lookup' E x))) \<Longrightarrow> u \<noteq> v \<Longrightarrow>                      
                     distinct p"
proof(goal_cases)
  case 1
  note assms = this
  have graph_invar: "Pair_Graph_Specs_satisfied.graph_inv (remove_all_empties E)"
  proof(subst Pair_Graph_Specs_satisfied.graph_inv_def, rule conjI[rotated], rule, rule, rule, goal_cases)
    case (1 v vset)
    then show ?case 
      using assms(5)[of v] remove_almost_all_empties(2,4)[OF assms(2), of v]
      by(cases "lookup' E v = Some vset") auto
  qed (simp add: assms(2) remove_almost_all_empties(5))
  have finite_graph:"Pair_Graph_Specs_satisfied.finite_graph (remove_all_empties E)"
    using assms(2) remove_almost_all_empties(1)
    by blast
  have finite_neighbs:"Pair_Graph_Specs_satisfied.finite_vsets undefined"
    unfolding Pair_Graph_Specs_satisfied.finite_vsets_def 
    by (simp add: )
  obtain e where e_prop:"e \<in> (Adj_Map_Specs2.digraph_abs  E)" "u = prod.fst e"
    using assms(1) assms(6) no_outgoing_last 
    unfolding vwalk_bet_def Pair_Graph_Specs_satisfied.digraph_abs_def 
    by fastforce
  hence neighb_u: "Adj_Map_Specs2.neighbourhood  E u \<noteq> vset_empty"
    using  Set.set_specs(1)  assms(2)
 Pair_Graph_Specs_satisfied.are_connected_absI[OF _  graph_invar, of "prod.fst e" "prod.snd e", simplified]  
    by(auto simp add: neighbourhood_def   Pair_Graph_Specs_satisfied.digraph_abs_def 
                      remove_all_empty_digraph_abs [OF assms(2)]
                      remove_all_empty_neighbourhood[OF assms(2)] )
  have q_non_empt: "q \<noteq> []"
    using assms(1) by auto
  obtain d where "d \<in> (Adj_Map_Specs2.digraph_abs  E)" "v = prod.snd d"
    using assms(1)  assms(6)  singleton_hd_last'[OF q_non_empt]
           vwalk_append_edge[of _ "butlast q" "[last q]",simplified append_butlast_last_id[OF q_non_empt]] 
    by(force simp add: vwalk_bet_def Adj_Map_Specs2.digraph_abs_def)
  have u_in_Vs:"u \<in> dVs (Adj_Map_Specs2.digraph_abs  E)" 
    using assms(1) assms(2) remove_all_empty_digraph_abs by auto
  have dfs_axioms: "DFS.DFS_axioms isin t_set adj_inv \<emptyset>\<^sub>N vset_inv lookup 
                         (remove_all_empties E) u"
    using finite_graph finite_neighbs graph_invar u_in_Vs remove_all_empty_digraph_abs[OF assms(2)]
    by(simp only: dfs.DFS_axioms_def )
  have dfs_thms: "DFS_thms map_empty delete vset_insert isin t_set sel update adj_inv vset_empty vset_delete
                   vset_inv vset_union vset_inter vset_diff lookup (remove_all_empties E) u"
    by(auto intro!: DFS_thms.intro DFS_thms_axioms.intro simp add: dfs.DFS_axioms dfs_axioms)
  have dfs_dom:"DFS.DFS_dom vset_insert sel vset_empty vset_diff lookup 
     (remove_all_empties E) (\<lambda> w. w = v) (dfs_initial u)"
    using DFS_thms.initial_state_props(6)[OF dfs_thms]
    by(simp add:  dfs_initial_def dfs_initial_state_def DFS_thms.initial_state_props(6) dfs_axioms)
  have rectified_map_subset:"dfs.Graph.digraph_abs (remove_all_empties E) \<subseteq> 
                (Adj_Map_Specs2.digraph_abs E)"
    by (simp add: assms(2) remove_all_empty_digraph_abs)
  have rectified_map_subset_rev:"Adj_Map_Specs2.digraph_abs  E 
                                 \<subseteq> dfs.Graph.digraph_abs (remove_all_empties E)"
    by (simp add: assms(2) remove_all_empty_digraph_abs)
  have reachable:"DFS_state.return (dfs E v (dfs_initial u)) = Reachable"
  proof(rule ccontr,rule DFS.return.exhaust[of "DFS_state.return (dfs E v (dfs_initial u))"],goal_cases)
    case 2
    hence "\<nexists>p. distinct p \<and> vwalk_bet (dfs.Graph.digraph_abs (remove_all_empties E)) u p v"
      using  DFS_thms.DFS_correct_1[OF dfs_thms, of "\<lambda> w. w=v"]  
             DFS_thms.DFS_to_DFS_impl[OF dfs_thms, of  "\<lambda> w. w=v"] 
      by (auto simp add:  dfs_def dfs_initial_def dfs_initial_state_def simp add: dfs_impl_def)
    moreover obtain q' where "vwalk_bet (Adj_Map_Specs2.digraph_abs  E ) u q' v" "distinct q'"
      using vwalk_bet_to_distinct_is_distinct_vwalk_bet[OF assms(1)]
      by(auto simp add: distinct_vwalk_bet_def )
    moreover hence "vwalk_bet (dfs.Graph.digraph_abs (remove_all_empties E)) u q' v"
      by (meson rectified_map_subset_rev vwalk_bet_subset)
    ultimately show False by auto
  next
  qed simp
  have "vwalk_bet  (dfs.Graph.digraph_abs (remove_all_empties E))
            u (rev (stack (dfs E v (dfs_initial u)))) v \<or>
         (stack (dfs.DFS (remove_all_empties E) (\<lambda>w.  w = v) (DFS.initial_state vset_insert \<emptyset>\<^sub>N u)) = [u] \<and> u = v)"
    using reachable sym[OF DFS_thms.DFS_to_DFS_impl[OF dfs_thms, of "\<lambda> w. w = v"]] 
          DFS_thms.DFS_correct_2[OF dfs_thms, of  "\<lambda> w. w = v"]
    by(auto simp add: dfs_initial_def  dfs_def dfs_axioms dfs_impl_def dfs_initial_state_def) 
  thus "vwalk_bet (Adj_Map_Specs2.digraph_abs E ) u p v"
    using 1(6)
    unfolding assms(3) get_path_def
    by (meson rectified_map_subset vwalk_bet_subset)
  show "distinct p"
    using  DFS_thms.initial_state_props(1,3) DFS_thms.invar_seen_stack_holds
           dfs_dom DFS_thms.DFS_to_DFS_impl dfs.invar_seen_stack_def dfs_thms
    by(fastforce simp add:  assms(3) get_path_def dfs_def dfs_initial_def
                   dfs_initial_state_def  dfs_impl_def) 
qed

interpretation algo: algo where \<E> = \<E> and \<c> = \<c> 
and \<u> = \<u> and edge_map_update = edge_map_update' and vset_empty = vset_empty
and vset_delete= vset_delete and vset_insert = vset_insert
and vset_inv = vset_inv and isin = isin and get_from_set=get_from_set
and filter=filter and are_all=are_all and set_invar=set_invar
and to_set=to_set and lookup=lookup' and t_set=t_set and sel=sel and adjmap_inv=adjmap_inv'
and to_pair=to_pair and \<epsilon> = \<epsilon> and \<E>_impl=\<E>_impl and empty_forest=all_empty
and default_conv_to_rdg=default_conv_to_rdg and \<b> = \<b> and N = N
and snd = snd and fst = fst and make_pair = make_pair and create_edge=create_edge
  using cost_flow_network 
  by(auto intro!: algo.intro algo_spec.intro simp add: Adj_Map_Specs2 algo_axioms algo_def Set3_axioms)
lemmas algo = algo.algo_axioms

lemma algo_impl_spec: "algo_impl_spec edge_map_update' vset_empty vset_delete vset_insert vset_inv isin get_from_set filter are_all set_invar
     to_set lookup' t_set sel adjmap_inv' flow_empty flow_update flow_delete flow_lookup flow_invar bal_empty bal_update
     bal_delete bal_lookup bal_invar rep_comp_empty rep_comp_update rep_comp_delete rep_comp_lookup rep_comp_invar
     conv_empty conv_update conv_delete conv_lookup conv_invar not_blocked_update not_blocked_empty not_blocked_delete
     not_blocked_lookup not_blocked_invar rep_comp_update_all not_blocked_update_all flow_update_all get_max"
  using  Map_bal.Map_axioms Map_conv Map_flow.Map_axioms Map_not_blocked.Map_axioms
          algo_spec conv_map.Map_axioms  Map_axioms
  by(auto intro!: algo_impl_spec.intro algo_impl_spec_axioms.intro flow_update_all get_max not_blocked_update_all rep_comp_update_all 
         simp add: Adj_Map_Specs2 Set3_axioms algo_spec.intro)
 
lemma algo_impl:"algo_impl snd make_pair create_edge \<u> \<E> \<c> edge_map_update' vset_empty vset_delete vset_insert vset_inv isin
     get_from_set filter are_all set_invar to_set lookup' t_set sel adjmap_inv' to_pair \<epsilon> \<E>_impl all_empty N
     default_conv_to_rdg flow_empty flow_update flow_delete flow_lookup flow_invar bal_empty bal_update bal_delete
     bal_lookup bal_invar rep_comp_empty rep_comp_update rep_comp_delete rep_comp_lookup rep_comp_invar conv_update
     conv_delete conv_lookup conv_invar not_blocked_update not_blocked_empty not_blocked_delete not_blocked_lookup
     not_blocked_invar fst rep_comp_update_all not_blocked_update_all flow_update_all get_max conv_empty"
  using algo  Map_bal Map_conv Map_flow Map_not_blocked
        Map_rep_comp  Map_bal.Map_axioms Map_conv Map_flow.Map_axioms Map_not_blocked.Map_axioms
            conv_map.Map_axioms  Map_axioms Adj_Map_Specs2 Set3_axioms
  by(auto intro!: algo_impl.intro algo_impl_spec.intro algo_impl_spec_axioms.intro
 flow_update_all get_max not_blocked_update_all rep_comp_update_all algo_spec.intro) 

lemma realising_edges_general_invar:
"realising_edges_invar (realising_edges_general list)"
  unfolding realising_edges_general_def
  by(induction list)
  (auto intro: Map_realising.invar_update split: option.split
       simp add: Map_realising.invar_empty realising_edges_empty_def realising_edges_invar_def realising_edges_update_def) 

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
   "edges_and_costs = Set.insert (e, c) {(e, ereal (- \<c> e)) | e. e \<in> set list \<and> nb e \<and> ereal (f e) > 0}"
 shows "(beste, bestc) \<in> edges_and_costs \<and>
        (\<forall> (ee, cc) \<in> edges_and_costs. bestc \<le> cc)"
  using assms
  unfolding find_cheapest_backward_def
  by(induction list arbitrary: edges_and_costs beste bestc)
    (auto split: if_split prod.split,
     insert ereal_le_less less_le_not_le nless_le order_less_le_trans, fastforce+)

lemma get_edge_and_costs_forward_not_MInfty:
  shows "prod.snd( get_edge_and_costs_forward nb f u v) \<noteq>MInfty"
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
  shows "prod.snd( get_edge_and_costs_backward nb f u v) \<noteq>MInfty"
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


lemma 
  get_edge_and_costs_forward_result_props:
  assumes "get_edge_and_costs_forward nb f u v = (e, c)"
              "c \<noteq>PInfty" "oedge e = d"
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
  have result_simp:"(e, c) = (if cf \<le> cb then (flow_network_spec.F ef, cf) else (flow_network_spec.B eb, cb))"
    by(auto split: option.split prod.split 
        simp add: get_edge_and_costs_forward_def sym[OF assms(1)] cf_def cb_def ingoing_edges_def outgoing_edges_def ef_def eb_def )
  show ?thesis
  proof(cases "cf \<le> cb")
    case True
    hence result_is:"flow_network_spec.F ef = e" "cf = c" "ef = d"
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
    hence result_is:"flow_network_spec.B eb = e" "cb = c" "eb = d"
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

lemma 
  get_edge_and_costs_backward_result_props:
  assumes "get_edge_and_costs_backward nb f v u = (e, c)"
              "c \<noteq>PInfty" "oedge e = d"
    shows "nb d\<and> cost_flow_network.rcap f e > 0 \<and> fstv e = u \<and> sndv e = v \<and>
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
  have result_simp:"(e, c) = (if cf \<le> cb then (flow_network_spec.F ef, cf) else (flow_network_spec.B eb, cb))"
    by(auto split: option.split prod.split 
        simp add: get_edge_and_costs_backward_def sym[OF assms(1)] cf_def cb_def ingoing_edges_def outgoing_edges_def ef_def eb_def )
  show ?thesis
  proof(cases "cf \<le> cb")
    case True
    hence result_is:"flow_network_spec.F ef = e" "cf = c" "ef = d"
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
    hence result_is:"flow_network_spec.B eb = e" "cb = c" "eb = d"
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

lemmas EEE_def = flow_network.\<EE>_def

lemma es_E_frac: "cost_flow_network.to_vertex_pair ` EEE = set es"
proof(goal_cases)
  case 1
  have help1: "\<lbrakk> (a, b) = prod.swap (make_pair d); prod.swap (make_pair d) \<notin> make_pair ` \<E>; d \<in> \<E>\<rbrakk> 
               \<Longrightarrow> (b, a) \<in> make_pair ` local.\<E>" for a b d
  using cost_flow_network.to_vertex_pair.simps 
  by (metis imageI swap_simp swap_swap)
  have help2: "\<lbrakk>(a, b) = make_pair x ; x \<in> local.\<E> \<rbrakk>\<Longrightarrow>
       make_pair x \<in> to_edge `
          ({cost_flow_network.F d |d. d \<in> local.\<E>} \<union> {cost_flow_network.B d |d. d \<in> local.\<E>})"
    for a b x
    using cost_flow_network.to_vertex_pair.simps
    by(metis (mono_tags, lifting) UnI1 imageI mem_Collect_eq)
  have help3: "\<lbrakk> (b, a) = make_pair x ; x \<in> local.\<E>\<rbrakk> \<Longrightarrow>
       (a, b) \<in> to_edge `
          ({cost_flow_network.F d |d. d \<in> local.\<E>} \<union> {cost_flow_network.B d |d. d \<in> local.\<E>})"
    for a b x
  by (smt (verit, del_insts) cost_flow_network.\<EE>_def cost_flow_network.o_edge_res
    cost_flow_network.oedge_simps'(2) cost_flow_network.to_vertex_pair.simps(2) image_iff swap_simp)
    show ?case
    by(auto simp add: cost_flow_network.to_vertex_pair.simps es_is_E EEE_def cost_flow_network.\<EE>_def
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
    by (auto simp add: multigraph.create_edge )
  have help6: "\<lbrakk>realising_edges_lookup local.realising_edges (u, v) = Some x2 ;
    realising_edges_lookup local.realising_edges (v, u) = Some x2a ; x2b \<le> x2c ;
    local.find_cheapest_backward f nb x2a (create_edge v u) \<infinity> = (x1a, x2c) ;
    local.find_cheapest_forward f nb x2 (create_edge u v) \<infinity> = (x1, x2b) \<rbrakk>\<Longrightarrow>
    make_pair x1 = (u, v)"
    for x2 x2a x1 x2b x1a x2c
    using realising_edges_result[of u v x2] realising_edges_result[of v u x2a]
          find_cheapest_forward_props[of x1 x2b f nb x2 "create_edge u v" PInfty, OF _ refl]
           find_cheapest_backward_props[of x1a  x2c f nb x2a "create_edge v u" PInfty, OF _ refl]
    by(auto simp add: multigraph.create_edge)
  have help7: "\<lbrakk> realising_edges_lookup local.realising_edges (u, v) = Some x2 ;
    realising_edges_lookup local.realising_edges (v, u) = Some x2a ;\<not> x2b \<le> x2c ;
    local.find_cheapest_backward f nb x2a (create_edge v u) \<infinity> = (x1a, x2c) ;
    local.find_cheapest_forward f nb x2 (create_edge u v) \<infinity> = (x1, x2b) \<rbrakk> \<Longrightarrow>
    prod.swap (make_pair x1a) = (u, v)"
   for x2 x2a x1 x2b x1a x2c
    using realising_edges_result[of u v x2] realising_edges_result[of v u x2a]
          find_cheapest_forward_props[of x1 x2b f nb x2 "create_edge u v" PInfty, OF _ refl]
          find_cheapest_backward_props[of x1a  x2c f nb x2a "create_edge v u" PInfty, OF _ refl]
    by(auto simp add: multigraph.create_edge)
  show ?case
    by(auto split: if_split prod.split option.split 
            simp add: multigraph.create_edge  find_cheapest_backward_def find_cheapest_forward_def
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
    by (auto simp add: multigraph.create_edge )
  have help3: "\<lbrakk> realising_edges_lookup local.realising_edges (u, v) = Some x2 ;
    realising_edges_lookup local.realising_edges (v, u) = Some x2a ; x2b \<le> x2c ;
    local.find_cheapest_backward f nb x2a (create_edge v u) \<infinity> = (x1a, x2c) ;
    local.find_cheapest_forward f nb x2 (create_edge u v) \<infinity> = (x1, x2b) \<rbrakk> \<Longrightarrow>
    make_pair x1 = (u, v)"
    for x2 x2a x1 x2b x1a x2c
    using realising_edges_result[of u v x2] realising_edges_result[of v u x2a]
    using find_cheapest_forward_props[of x1 x2b f nb x2 "create_edge u v" PInfty, OF _ refl]
    using find_cheapest_backward_props[of x1a  x2c f nb x2a "create_edge v u" PInfty, OF _ refl]
    by(auto simp add: multigraph.create_edge)
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
            simp add: multigraph.create_edge find_cheapest_forward_def find_cheapest_backward_def
             intro: help1 help2 help3 help4)
qed

lemma costs_forward_less_PInfty_in_es: "prod.snd (get_edge_and_costs_forward nb f u v) < PInfty \<Longrightarrow> (u, v) \<in> set es"
  using get_edge_and_costs_forward_result_props[OF prod.collapse[symmetric] _ refl, of nb f u v,
          simplified cost_flow_network.o_edge_res]
        es_E_frac to_edge_get_edge_and_costs_forward[of nb f u v] 
  by force

lemma costs_backward_less_PInfty_in_es: "prod.snd (get_edge_and_costs_backward nb f u v) < PInfty \<Longrightarrow> (v, u) \<in> set es"
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

interpretation bf_fw: bellman_ford where connection_update=connection_update
and connection_empty=connection_empty and connection_lookup=connection_lookup
and connection_delete=connection_delete and connection_invar=connection_invar 
and es= es and vs=vs and edge_costs="(\<lambda> u v. prod.snd (get_edge_and_costs_forward nb f u v))" 
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

interpretation bf_bw: bellman_ford where connection_update=connection_update
and connection_empty=connection_empty and connection_lookup=connection_lookup
and connection_delete=connection_delete and connection_invar=connection_invar 
and es= es and vs=vs and edge_costs="  (\<lambda> u v. prod.snd (get_edge_and_costs_backward nb f u v))" 
for nb f
  using bellman_ford_backward by auto
 
lemma get_source_aux:"(\<exists> x \<in> set xs. b x > (1 - \<epsilon>) * \<gamma> ) 
\<Longrightarrow> res = (get_source_aux b \<gamma> xs) \<Longrightarrow> b res > (1 - \<epsilon>) * \<gamma> \<and> res \<in> set xs "
  unfolding get_source_aux_def
  by(induction b \<gamma> xs rule: get_source_aux_aux.induct) auto

lemma get_target_aux:"(\<exists> x \<in> set xs. b x < - (1 - \<epsilon>) * \<gamma> ) 
\<Longrightarrow> res = (get_target_aux b \<gamma> xs) \<Longrightarrow> b res < - (1 - \<epsilon>) * \<gamma> \<and> res \<in> set xs "
  unfolding get_target_aux_def
  by(induction b \<gamma> xs rule: get_target_aux_aux.induct) auto

abbreviation "aux_invar (state)\<equiv> algo.aux_invar  state"
abbreviation "invar_isOptflow (state)\<equiv> algo.invar_isOptflow state"
abbreviation "\<F> state \<equiv> algo.\<F>  (state)"
abbreviation "resreach \<equiv> cost_flow_network.resreach"
abbreviation "augpath \<equiv> cost_flow_network.augpath"
abbreviation "invar_gamma (state)== algo.invar_gamma state"
abbreviation "augcycle == cost_flow_network.augcycle"
abbreviation "prepath == cost_flow_network.prepath"

lemmas prepath_def = cost_flow_network.prepath_def
lemmas augpath_def = cost_flow_network.augpath_def

definition "get_source (state) = get_source_aux (balance state) (current_\<gamma> state) vs"
definition "get_target (state) = get_target_aux (balance state) (current_\<gamma> state) vs"

lemma realising_edges_invar: 
"realising_edges_invar realising_edges" 
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
      by (fastforce simp add: ingoing_edges_def)
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
      by (fastforce simp add: outgoing_edges_def)
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
      by (fastforce simp add: ingoing_edges_def)
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
      by (fastforce simp add: outgoing_edges_def)
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

lemma get_target_for_source_aux_aux:"(\<exists> x \<in> set xs. b x <  - \<epsilon> * \<gamma> \<and> prod.snd (the (connection_lookup connections x)) < PInfty) 
\<longleftrightarrow>( (get_target_for_source_aux_aux connections b \<gamma> xs) \<noteq> None)"
  by (induction connections b \<gamma> xs rule: get_target_for_source_aux_aux.induct) force+

lemma get_target_for_source_aux:"(\<exists> x \<in> set xs. b x <  - \<epsilon> * \<gamma> \<and> prod.snd (the (connection_lookup connections x)) < PInfty) 
\<Longrightarrow> res = (get_target_for_source_aux connections b \<gamma> xs) 
\<Longrightarrow> b res < - \<epsilon> * \<gamma> \<and> res \<in> set xs \<and> prod.snd (the (connection_lookup connections res)) < PInfty"
  by (subst (asm) get_target_for_source_aux_def,
       induction connections b \<gamma> xs rule: get_target_for_source_aux_aux.induct) force+
 
term bellman_ford_forward 
definition "get_target_for_source state s = (if s \<in> VV \<and>
             aux_invar state \<and> (\<forall> e \<in> \<F> state .  (current_flow state) e > 0)\<and> 
              s = get_source state \<and> invar_isOptflow state \<and> 
(\<exists> t \<in> VV . balance state t < - \<epsilon> * current_\<gamma> state \<and> resreach  (current_flow state) s t ) then 
let bf = bellman_ford_forward (not_blocked state) (current_flow state) s in
get_target_for_source_aux bf (balance state) (current_\<gamma> state) vs else
  (SOME t. t \<in> VV \<and> balance state t < - \<epsilon> * current_\<gamma> state \<and> resreach (current_flow state) s t))"


definition "get_source_target_path_a state s t= 
 (if invar_isOptflow state then
    (let bf = bellman_ford_forward (not_blocked state) (current_flow state) s; 
         t = get_target_for_source_aux bf (balance state) (current_\<gamma> state) vs;
         Pbf = search_rev_path_exec s bf t Nil;
         P = (map (\<lambda>e. prod.fst (get_edge_and_costs_forward (not_blocked state) (current_flow state) (prod.fst e) (prod.snd e)))
             (edges_of_vwalk Pbf)) in
          P) 
  else [])"

lemma get_source_for_target_aux_aux:"(\<exists> x \<in> set xs. b x >  \<epsilon> * \<gamma> \<and> prod.snd (the (connection_lookup connections x)) < PInfty) 
\<longleftrightarrow>( (get_source_for_target_aux_aux connections b \<gamma> xs) \<noteq> None)"
  by (induction connections b \<gamma> xs rule: get_source_for_target_aux_aux.induct) force+

lemma get_source_for_target_aux:
"(\<exists> x \<in> set xs. b x >  \<epsilon> * \<gamma> \<and> prod.snd (the (connection_lookup connections x)) < PInfty) 
\<Longrightarrow> res = (get_source_for_target_aux connections b \<gamma> xs) 
\<Longrightarrow> b res > \<epsilon> * \<gamma> \<and> res \<in> set xs \<and> prod.snd (the (connection_lookup connections res)) < PInfty"
  by (subst (asm) get_source_for_target_aux_def, 
     induction connections b \<gamma> xs rule: get_source_for_target_aux_aux.induct) force+ 

definition "get_source_for_target state t = (if t \<in> VV \<and>
             aux_invar state \<and> (\<forall> e \<in> \<F> state .  (current_flow state) e > 0)\<and> 
              t = get_target state \<and> invar_isOptflow state \<and> 
(\<exists> s \<in> VV . balance state s > \<epsilon> * current_\<gamma> state \<and> resreach  (current_flow state) s t ) then 
let bf = bellman_ford_backward (not_blocked state) (current_flow state) t in
get_source_for_target_aux bf (balance state) (current_\<gamma> state) vs else
  (SOME s. s \<in> VV \<and> balance state s > \<epsilon> * current_\<gamma> state \<and> resreach (current_flow state) s t))"

lemma itrev_rev_gen:"itrev xs ys = rev xs @ ys"
  by(induction xs ys arbitrary: rule: itrev.induct) auto

lemma rev_is_rev': "rev = rev'"
  by(auto simp add: itrev_rev_gen[of _ Nil, simplified] rev'_def)
 
definition "get_source_target_path_b state s t= 
 (if invar_isOptflow state then
    (let bf = bellman_ford_backward (not_blocked state) (current_flow state) t; 
         s = get_source_for_target_aux bf (balance state) (current_\<gamma> state) vs;
         Pbf = rev'(search_rev_path_exec t bf s Nil);
         P = (map (\<lambda> e. (prod.fst (get_edge_and_costs_backward (not_blocked state) (current_flow state) (prod.snd e) (prod.fst e)))) 
                     (edges_of_vwalk Pbf)) in
          P) 
  else [])"

interpretation loopB: 
 loopB snd make_pair create_edge \<u> \<c> \<E> vset_empty vset_delete vset_insert vset_inv isin get_from_set filter
    are_all set_invar to_set lookup' t_set sel adjmap_inv' \<b> to_pair \<epsilon> \<E>_impl all_empty N 
    default_conv_to_rdg get_source_target_path_b  get_source  get_target get_source_for_target  get_target_for_source
    fst get_source_target_path_a edge_map_update'
  using  algo 
  by(auto intro!: loopB.intro  loopB_spec.intro Adj_Map_Specs2 Set3_axioms algo_spec.intro)

lemmas loopB = loopB.loopB_axioms

abbreviation "loopB_call1_cond state \<equiv> loopB.loopB_call1_cond  state"

abbreviation "loopB_fail1_cond  state \<equiv> loopB.loopB_fail1_cond  state"

abbreviation "loopB_call2_cond state \<equiv> loopB.loopB_call2_cond  state"

abbreviation "loopB_fail2_cond  state \<equiv> loopB.loopB_fail2_cond  state"

lemmas loopB_fail1_condE = loopB.loopB_fail1_condE
lemmas loopB_call1_condE = loopB.loopB_call1_condE
lemmas loopB_fail1_cond_def = loopB.loopB_fail1_cond_def
lemmas loopB_call1_cond_def= loopB.loopB_call1_cond_def

lemmas loopB_fail2_condE = loopB.loopB_fail2_condE
lemmas loopB_call2_condE = loopB.loopB_call2_condE
lemmas loopB_fail2_cond_def = loopB.loopB_fail2_cond_def
lemmas loopB_call2_cond_def= loopB.loopB_call2_cond_def

lemmas invar_gamma_def = algo.invar_gamma_def
lemmas invar_isOptflow_def = algo.invar_isOptflow_def
lemmas is_Opt_def = cost_flow_network.is_Opt_def
lemmas from_aux_invar' = algo.from_aux_invar'

abbreviation "to_graph == Adj_Map_Specs2.to_graph"

lemma get_source_axioms:
   "\<lbrakk>b = balance state; \<gamma> = current_\<gamma> state;  s = get_source state;
                    loopB_call1_cond state \<or> loopB_fail1_cond state\<rbrakk> 
                    \<Longrightarrow> s \<in> VV \<and> b s > (1 - \<epsilon>) * \<gamma>"
    using get_source_aux[of vs \<gamma> b s] vs_is_V 
    by (auto elim!: loopB_call1_condE  loopB_fail1_condE simp add: get_source_def)

lemma get_target_axioms:
   "\<lbrakk>b = balance state ; \<gamma> = current_\<gamma> state; t = get_target state;
                     loopB_call2_cond state \<or> loopB_fail2_cond state\<rbrakk> 
                    \<Longrightarrow> t \<in> VV \<and> b t < - (1 -\<epsilon>) * \<gamma>"
    using get_target_aux[of vs b \<gamma> t] vs_is_V 
    by(auto elim!: loopB_call2_condE  loopB_fail2_condE simp add: get_target_def) auto  

lemma path_flow_network_path_bf:
  assumes e_weight:"\<And> e. e \<in> set pp \<Longrightarrow> prod.snd (get_edge_and_costs_forward nb f (fstv e) (sndv e)) < PInfty"
         and is_a_walk:"awalk UNIV s (map to_edge pp) tt" 
         and s_is_fstv: "s = fstv (hd pp)"
 and     bellman_ford:"bellman_ford  connection_empty connection_lookup connection_invar connection_delete
     es vs (\<lambda> u v. prod.snd (get_edge_and_costs_forward nb f u v)) connection_update"  
shows
"weight nb f (awalk_verts s (map cost_flow_network.to_vertex_pair pp)) < PInfty"
  using assms(1,2)[simplified assms(3)]
  apply(subst assms(3))
proof(induction pp  rule: list_induct3)
  case 1
  then show ?case 
    using  bellman_ford.weight.simps[OF bellman_ford] by auto
next
  case (2 x)
  then show ?case
    using  bellman_ford.weight.simps[OF bellman_ford] apply auto[1]
    apply(induction x rule: cost_flow_network.to_vertex_pair.induct)
    apply(simp add: bellman_ford.weight.simps[OF bellman_ford] make_pair_fst_snd)+
    done
next
  case (3 e d es)
  have same_ends:"sndv e = fstv d"
    using 3(3)
    by(induction e rule: cost_flow_network.to_vertex_pair.induct)
      (auto intro: cost_flow_network.to_vertex_pair.induct[OF , of _ d]  
        simp add:  bellman_ford.weight.simps[OF bellman_ford]
                           Awalk.awalk_simps make_pair_fst_snd 
                 cost_flow_network.vs_to_vertex_pair_pres(1))
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
and len:  "length pp \<ge> 2"
     and "weight nb f pp < PInfty"
         "ppp = edges_of_vwalk pp"      
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
        nb (flow_network.oedge e) \<and> 0 < cost_flow_network.rcap f e)"
      using 2  bellman_ford.weight.simps[OF bellman_ford] cost_flow_network.oedge_simps'
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
    nb (flow_network.oedge e) \<and> 0 < cost_flow_network.rcap f e)" 
    by (simp add: "3.IH" calculation(3))
  moreover have "nb (flow_network.oedge (prod.fst (get_edge_and_costs_forward nb f x y)))"
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
  assumes "invar_isOptflow state" "aux_invar state"
  shows   "\<nexists>c. weight (not_blocked state) (current_flow state) c < 0 \<and> hd c = last c"
proof(rule nexistsI, goal_cases)
  case (1 c)
  have bellman_ford:"bellman_ford connection_empty connection_lookup connection_invar connection_delete
     es vs (\<lambda> u v. prod.snd (get_edge_and_costs_forward (not_blocked state) (current_flow state) u v)) connection_update"
    by (simp add: bellman_ford)
  have length_c: "length c \<ge> 2"
    using 1 bellman_ford.weight.simps[OF bellman_ford] 
    by(cases c rule: list_cases3) auto
  have weight_le_PInfty:"weight (not_blocked state) (current_flow state) c < PInfty" 
    using "1"(1) by fastforce
  have path_with_props:"awalk UNIV (hd c) (edges_of_vwalk c) (last c)"
       "weight (not_blocked state) (current_flow state) c =
       ereal (foldr (\<lambda>e. (+) (\<cc> e))
        (map (\<lambda>e. prod.fst (get_edge_and_costs_forward (not_blocked state) (current_flow state) (prod.fst e) (prod.snd e)))
                      (edges_of_vwalk c)) 0)"
      "(\<And> e. e\<in>set (map (\<lambda>e. prod.fst (get_edge_and_costs_forward (not_blocked state) (current_flow state) (prod.fst e)
                         (prod.snd e)))
           (edges_of_vwalk c)) \<Longrightarrow>
        not_blocked state (flow_network.oedge e) \<and> 0 < cost_flow_network.rcap (current_flow state) e)"
    using path_bf_flow_network_path[OF _ length_c weight_le_PInfty refl] by auto
  define cc where "cc = (map (\<lambda>e. prod.fst (get_edge_and_costs_forward (not_blocked state) (current_flow state) (prod.fst e) (prod.snd e)))
                       (edges_of_vwalk c))"
  have "map (to_edge \<circ> (\<lambda>e. prod.fst (local.get_edge_and_costs_forward (not_blocked state)
                     (current_flow state) (prod.fst e) (prod.snd e)))) (edges_of_vwalk c) =
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
  moreover have "0 < cost_flow_network.Rcap (current_flow state) (set cc)"
    using cc_def path_with_props(3)
    by(auto simp add: cost_flow_network.Rcap_def)
  ultimately have agpath:"augpath (current_flow state) cc"
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
  have le_infty:"prod.snd (get_edge_and_costs_forward (not_blocked state) (current_flow state) (prod.fst (to_edge e))
             (prod.snd (to_edge e))) < PInfty"
  proof(rule ccontr, goal_cases)
    case 1
    hence "prod.snd (get_edge_and_costs_forward (not_blocked state) (current_flow state) (prod.fst (cost_flow_network.to_vertex_pair e))
           (prod.snd (cost_flow_network.to_vertex_pair e)))
     = PInfty" by simp
    hence "weight (not_blocked state) (current_flow state) c = PInfty"
      using bellman_ford.edge_and_Costs_none_pinfty_weight[OF bellman_ford]
            c_split by auto
    thus False
      using weight_le_PInfty by force
  qed
  have one_not_blocked:"not_blocked state (oedge e)"
    using less_PInfty_not_blocked  "1"(1) cc_def path_with_props(3) by blast
  hence "oedge e \<in> \<E>"
    using assms(2) 
    unfolding algo.aux_invar_def  algo.invar_aux22_def
                algo.invar_aux1_def  algo.invar_aux3_def
    by auto
  thus ?case
    using  1(2) cost_flow_network.o_edge_res by blast
qed
  obtain C where "augcycle (current_flow state) C"
    apply(rule cost_flow_network.augcycle_from_non_distinct_cycle[OF  agpath])
    using "1"(1) awalk_f c_non_empt awalk_fst_last[OF _ awalk_f]
          awalk_fst_last[OF _ path_with_props(1)] same_edges  cc_in_E  "1"(1) cc_def path_with_props(2)
    by auto
  then show ?case 
    using assms(1) invar_isOptflow_def cost_flow_network.min_cost_flow_no_augcycle by blast
qed
    

lemma get_target_for_source_ax:
" \<lbrakk>b = balance state; \<gamma> = current_\<gamma> state; f = current_flow state; s = get_source state;
                         t = get_target_for_source state s; loopB_call1_cond state; invar_gamma state\<rbrakk>
                        \<Longrightarrow> t \<in> VV \<and> b t < - \<epsilon> * \<gamma> \<and> resreach f s t"
  unfolding get_target_for_source_def
proof(rule if_E[where P= "\<lambda> x. t = x"], fast, goal_cases)
  case 1
  note assms = this
  have s_prop: "s \<in> VV" "(1 - \<epsilon>) * \<gamma> < b s"
  using get_source_axioms[OF 1(1) 1(2) 1(4)] "1"(6)[simplified sym[OF  get_target_for_source_def]] by auto
  from 1 have knowledge: "get_source state \<in> VV"
    "aux_invar state"
    "(\<forall>e\<in>to_rdgs to_pair (conv_to_rdg state) (Adj_Map_Specs2.to_graph  (\<FF>_imp state)).
        0 < current_flow state (flow_network.oedge e))"
    "invar_isOptflow state" 
    "(\<exists>t\<in>VV. balance state t < - (\<epsilon> * current_\<gamma> state) \<and> resreach (current_flow state) s t)"
    by force+
  then obtain tt where tt_pr: " balance state tt < - (\<epsilon> * current_\<gamma> state)" "resreach (current_flow state) s tt" "tt \<in> VV"
    by auto
  then obtain p where "augpath (current_flow state) p" "fstv (hd p) = s"
                      "sndv(last p) = tt" "set p \<subseteq> EEE"
    using cost_flow_network.resreach_imp_augpath by blast
  moreover have s_neq_tt:"s \<noteq> tt" 
    using \<epsilon>_axiom(1) s_prop  tt_pr(1) 1(7) "1"(1) "1"(2)
    unfolding invar_gamma_def 
    by (smt (verit, best) mult_minus_left mult_strict_right_mono)
  moreover have "\<nexists>C. augcycle(current_flow state) C"
    using cost_flow_network.is_opt_iff_no_augcycle knowledge(4)
    by (auto simp add: invar_isOptflow_def is_Opt_def )
  ultimately obtain pp where pp_prop:"augpath (current_flow state) pp"
     "fstv (hd pp) = s" "sndv (last pp) = tt"
     "set pp
     \<subseteq> {e |e. e \<in> EEE \<and> cost_flow_network.oedge e \<in> to_set (actives state)} \<union> to_rdgs to_pair (conv_to_rdg state) (\<FF> state)"
     "foldr (\<lambda>x. (+) (\<cc> x)) pp 0 \<le> foldr (\<lambda>x. (+) (\<cc> x)) p 0"
    using  algo.simulate_inactives_costs[ of "current_flow state" p, of s tt state, OF _ _ _ _ _  refl refl refl refl refl refl refl refl ]
           1(8) by auto
  have F_is: "\<FF> state = to_graph (\<FF>_imp state)" 
    using knowledge(2) from_aux_invar'(21) by auto
  hence e_in:"e \<in> set pp \<Longrightarrow> e \<in> {e |e. e \<in> EEE \<and> cost_flow_network.oedge e \<in> to_set (actives state)} 
                   \<union> to_rdgs to_pair (conv_to_rdg state) (\<FF> state)" for e
      using pp_prop(4)  by auto
    hence e_es:"e \<in> set pp \<Longrightarrow> cost_flow_network.to_vertex_pair e \<in> set es" for e
      using es_E_frac algo.aux_invar_subs knowledge(2) by fastforce
  have e_in_pp_weight:"e \<in> set pp \<Longrightarrow> prod.snd (get_edge_and_costs_forward (not_blocked state) (current_flow state) (fstv e) (sndv e)) < PInfty" for e
  proof(goal_cases)
    case 1
    note e_es[OF 1]
    moreover have oedge_where:"oedge e \<in> to_set (actives state) \<or> oedge e \<in> \<F> state"
      using e_in F_is 1 by auto
    hence nb:"not_blocked state (oedge e)"
      by (meson Un_iff from_aux_invar'(22) knowledge(2))
    have oedgeE:"oedge e \<in> \<E>"
      using oedge_where from_aux_invar'(1,3)[OF knowledge(2)] by auto
    have posflow:"\<exists> d. e = B d \<Longrightarrow> current_flow state (oedge e) > 0" 
      using cost_flow_network.augpath_rcap_pos_strict'[OF  pp_prop(1) 1]
      by(induction  rule: cost_flow_network.oedge.cases[OF  , of e])
         auto
    have "prod.snd (get_edge_and_costs_forward (not_blocked state) (current_flow state)
     (fstv e) (sndv e)) \<le> \<cc> e"
      using nb cost_flow_network.augpath_rcap_pos_strict'[OF pp_prop(1) 1] 
      by(auto intro:  conjunct1[OF get_edge_and_costs_forward_makes_cheaper
               [OF refl oedgeE, of "not_blocked state" "current_flow state"]] prod.collapse) 
    thus ?case by auto
  qed
  have bellman_ford:"bellman_ford connection_empty connection_lookup connection_invar connection_delete
     es vs (\<lambda> u v. prod.snd (get_edge_and_costs_forward (not_blocked state) (current_flow state) u v)) connection_update"
    by (simp add: bellman_ford knowledge(2) knowledge(3))
  have is_a_walk:"awalk UNIV s (map to_edge pp) tt"
    using pp_prop by (auto simp add:  augpath_def prepath_def)
  hence "vwalk_bet UNIV s (awalk_verts s (map cost_flow_network.to_vertex_pair pp)) tt"
    using  awalk_imp_vwalk by force
  moreover have weight_le_PInfty:"weight (not_blocked state) 
(current_flow state) (awalk_verts s (map cost_flow_network.to_vertex_pair pp)) < PInfty"
    using  path_flow_network_path_bf e_in_pp_weight is_a_walk bellman_ford pp_prop(2) by blast
  define connections where "connections = 
          (bellman_ford_forward (not_blocked state) (current_flow state) s)"
  have no_neg_cycle_in_bf: "\<nexists>c. weight (not_blocked state) (current_flow state) c < 0 \<and> hd c = last c"
    using knowledge(2) knowledge(4) no_neg_cycle_in_bf by blast
  have long_enough: "2 \<le> length (awalk_verts s (map cost_flow_network.to_vertex_pair pp))"
    using s_neq_tt awalk_verts_non_Nil calculation
          hd_of_vwalk_bet'[OF calculation] last_of_vwalk_bet[OF calculation] 
    by (cases "awalk_verts s (map cost_flow_network.to_vertex_pair pp)" rule: list_cases3) auto  
  have tt_dist_le_PInfty:"prod.snd (the (connection_lookup connections tt)) < PInfty"
    unfolding connections_def bellman_ford_forward_def bellman_ford_init_algo_def bellman_ford_algo_def
    using no_neg_cycle_in_bf  s_neq_tt  tt_pr(3) vs_is_V weight_le_PInfty  is_a_walk long_enough 
    by (fastforce intro!: bellman_ford.bellamn_ford_path_exists_result_le_PInfty[OF bellman_ford, of
            _ _ "(awalk_verts s (map cost_flow_network.to_vertex_pair pp))"] 
               simp add: s_prop(1) vs_is_V )   
  have t_prop:"balance state t < - \<epsilon> * current_\<gamma> state \<and>
         t \<in> set vs \<and> prod.snd (the (connection_lookup connections t)) < PInfty"
    using tt_dist_le_PInfty tt_pr(1) tt_pr(3) vs_is_V  "1"(9) assms(4)
    by(intro get_target_for_source_aux[of vs "balance state" "current_\<gamma> state" connections t]) 
      (auto simp add: connections_def)
  have t_neq_s: "t \<noteq> s"
    using t_prop s_prop "1"(1) "1"(2) "1"(7) invar_gamma_def
    by (smt (verit, best) mult_less_cancel_right_pos)
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
  have "weight (not_blocked state) 
          (current_flow state) Pbf = prod.snd (the (connection_lookup connections t))"
    unfolding Pbf_def
    using t_prop  t_neq_s  s_prop(1) vs_is_V  pred_of_t_not_None 
    by (fastforce simp add: bellman_ford_forward_def connections_def bellman_ford_init_algo_def bellman_ford_algo_def
                 intro!: bellman_ford.bellman_ford_search_rev_path_weight[OF 
                bellman_ford no_neg_cycle_in_bf, of connections s t]) 
  hence weight_le_PInfty: "weight (not_blocked state) (current_flow state) Pbf < PInfty"
    using t_prop by auto
  have Pbf_opt_path: "bellman_ford.opt_vs_path vs
 (\<lambda>u v. prod.snd (get_edge_and_costs_forward (not_blocked state) (current_flow state) u v)) s t
 (rev (bellman_ford_spec.search_rev_path connection_lookup s connections t))"
    using t_prop  t_neq_s  s_prop(1) vs_is_V  pred_of_t_not_None 
    by (auto simp add: bellman_ford_forward_def connections_def bellman_ford_init_algo_def bellman_ford_algo_def
                 intro!: bellman_ford.computation_of_optimum_path[OF bellman_ford no_neg_cycle_in_bf])
  hence length_Pbf:"2 \<le> length Pbf" 
    by(auto simp add: bellman_ford.opt_vs_path_def[OF bellman_ford]
      bellman_ford.vs_path_def[OF bellman_ford] Pbf_def)
  have "awalk UNIV (hd Pbf) (edges_of_vwalk Pbf) (last Pbf) \<and>
         weight (not_blocked state) (current_flow state) Pbf =
         ereal  (foldr (\<lambda>e. (+) (\<cc> e))
        (map (\<lambda>e. prod.fst (get_edge_and_costs_forward (not_blocked state) (current_flow state) (prod.fst e) (prod.snd e)))
                       (edges_of_vwalk Pbf)) 0) \<and>
         (\<forall>e\<in>set (map (\<lambda>e. prod.fst (get_edge_and_costs_forward (not_blocked state) (current_flow state) (prod.fst e)
                         (prod.snd e)))
           (edges_of_vwalk Pbf)).
    not_blocked state (flow_network.oedge e) \<and> 0 < cost_flow_network.rcap (current_flow state) e)"
    by(intro path_bf_flow_network_path[OF _ length_Pbf weight_le_PInfty refl]) simp
  hence Pbf_props: "awalk UNIV (hd Pbf) (edges_of_vwalk Pbf) (last Pbf)"
                   " weight (not_blocked state) (current_flow state) Pbf =
         ereal  (foldr (\<lambda>e. (+) (\<cc> e))
        (map (\<lambda>e. prod.fst (get_edge_and_costs_forward (not_blocked state) (current_flow state) (prod.fst e) (prod.snd e)))
                   (edges_of_vwalk Pbf)) 0)"
                   "(\<And> e. e \<in> set (map (\<lambda>e. prod.fst (get_edge_and_costs_forward (not_blocked state) (current_flow state) (prod.fst e)
                         (prod.snd e)))
           (edges_of_vwalk Pbf)) \<Longrightarrow>
    not_blocked state (flow_network.oedge e) \<and> 0 < cost_flow_network.rcap (current_flow state) e)"
    by auto
  define P where "P = (map (\<lambda>e. prod.fst (get_edge_and_costs_forward (not_blocked state) (current_flow state) (prod.fst e) (prod.snd e)))
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
  moreover have "0 < cost_flow_network.Rcap (current_flow state) (set P)"
    using P_def Pbf_props(3)
    by(auto simp add: cost_flow_network.Rcap_def)
  ultimately have "augpath (current_flow state) P"
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
        by auto
      subgoal for e 
        using edges_in_vwalk_split[of "snd e" "fst e" Pbf] multigraph.make_pair 
        by auto
    done
  have le_infty:"prod.snd (get_edge_and_costs_forward (not_blocked state) (current_flow state) (prod.fst (cost_flow_network.to_vertex_pair e))
             (prod.snd (to_edge e))) < PInfty"
  proof(rule ccontr, goal_cases)
    case 1
    hence "prod.snd (get_edge_and_costs_forward (not_blocked state) (current_flow state) (prod.fst (cost_flow_network.to_vertex_pair e))
           (prod.snd (cost_flow_network.to_vertex_pair e)))
     = PInfty" by auto
    hence "weight (not_blocked state) (current_flow state) Pbf = PInfty"
      using bellman_ford.edge_and_Costs_none_pinfty_weight[OF bellman_ford]
            c_split by auto
    thus False
      using weight_le_PInfty by force
  qed
  have one_not_blocked:"not_blocked state (oedge e)"
    using less_PInfty_not_blocked  "1"(1) P_def Pbf_props(3) by blast
  hence "oedge e \<in> \<E>"
    using knowledge(2)
    unfolding algo.aux_invar_def  algo.invar_aux22_def
                algo.invar_aux1_def algo.invar_aux3_def
    by auto
  thus ?case 
    using "1"(2) cost_flow_network.o_edge_res by blast
  qed
  ultimately have "resreach f s t"
    using cost_flow_network.augpath_imp_resreach 1(3) by fast  
  thus ?case 
    using assms(1) assms(2) t_prop vs_is_V by blast
next
  case 2
  have "\<exists> t.
        t \<in> VV \<and> balance state t < (- \<epsilon>) * current_\<gamma> state \<and> resreach (current_flow state) s t"
    using 2(6)
    unfolding 2(1-4) Let_def LoopB.loopB.loopB_call1_cond_def[OF loopB] 
    by metis
  moreover have "t = (SOME t. t \<in> VV \<and> balance state t < - \<epsilon> * current_\<gamma> state \<and>
             resreach (current_flow state) s t)"
    using "2"(4) "2"(9) by fastforce
  ultimately show ?case 
    using 2(1-4)
    by(auto intro!: someI_ex)
qed

lemma bf_weight_leq_res_costs:
assumes "set (map oedge qq) \<subseteq> set \<E>_list"
        " \<And> e. e \<in> set qq \<Longrightarrow> not_blocked state (flow_network.oedge e)"
        "\<And> e. e \<in> set qq \<Longrightarrow> 0 < cost_flow_network.rcap (current_flow state) e"
        "unconstrained_awalk (map cost_flow_network.to_vertex_pair qq)"
   and  qq_len: "length qq \<ge> 1"
shows "weight (not_blocked state) (current_flow state) (awalk_verts s (map cost_flow_network.to_vertex_pair qq))
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
                                  refl, of _ "not_blocked state" "current_flow state"]] 
                     intro: surjective_pairing prod.collapse
           simp add: \<E>_def \<E>_impl(1) \<E>_list_def to_list(1) make_pair_fst_snd
           simp del: cost_flow_network.\<cc>.simps)+
  next
    case (3 e d xs)
    have help1: 
      "\<lbrakk>(unconstrained_awalk ((fst ee, snd ee) # map to_edge xs) \<Longrightarrow>
        weight (not_blocked state) (current_flow state) (fst ee  # awalk_verts (snd ee) (map to_edge xs))
                   \<le> ereal (\<cc> (F ee) + foldr (\<lambda>x. (+) (\<cc> x)) xs 0)) ;
        (\<And>e. e = F dd \<or> e = F ee \<or> e \<in> set xs \<Longrightarrow>  not_blocked state (oedge e)) ;
        (\<And>e. e = F dd \<or> e = F ee \<or> e \<in> set xs \<Longrightarrow>  0 < rcap (current_flow state) e) ;
        unconstrained_awalk ((fst dd, snd dd) # (fst ee, snd ee) # map to_edge xs) ;
        dd \<in> set \<E>_list ; ee \<in> set \<E>_list ; oedge ` set xs \<subseteq> set \<E>_list\<rbrakk> \<Longrightarrow>
       prod.snd (get_edge_and_costs_forward (not_blocked state) (current_flow state) (fst dd) (fst ee)) +
       weight (not_blocked state) (current_flow state) (fst ee # awalk_verts (snd ee) (map to_edge xs))
       \<le> ereal (\<cc> (F dd) + (\<cc> (F ee) + foldr (\<lambda>x. (+) (\<cc> x)) xs 0))"for ee dd
    using  unconstrained_awalk_drop_hd[of "(fst dd, snd dd)"]  
    by(subst ereal_add_homo[of _ "_ + _ "])
      (fastforce intro!:  ordered_ab_semigroup_add_class.add_mono conjunct1[OF get_edge_and_costs_forward_makes_cheaper[OF 
                                  refl, of _ "not_blocked state" "current_flow state"]]
                      intro:       trans[OF prod.collapse] 
                               cong[OF refl unconstrained_awalk_snd_verts_eq[of "fst dd" "snd dd"
                                       "fst ee" "snd ee", symmetric]]
                       simp add: \<E>_def \<E>_impl(1) \<E>_list_def to_list(1))
   have help2: 
    "\<lbrakk> (unconstrained_awalk ((snd ee, fst ee) # map to_edge xs) \<Longrightarrow>
        weight (not_blocked state) (current_flow state) (snd ee #  awalk_verts (fst ee) (map to_edge xs))
        \<le> ereal (\<cc> (B ee) + foldr (\<lambda>x. (+) (\<cc> x)) xs 0)) ;
        (\<And>e. e = F dd \<or> e = B ee \<or> e \<in> set xs \<Longrightarrow>  not_blocked state (oedge e)) ;
        (\<And>e. e = F dd \<or> e = B ee \<or> e \<in> set xs \<Longrightarrow>0 < rcap (current_flow state) e) ;
        unconstrained_awalk ((fst dd, snd dd) # (snd ee, fst ee) # map to_edge xs) ;
        dd \<in> set \<E>_list ; ee \<in> set \<E>_list; oedge ` set xs \<subseteq> set \<E>_list \<rbrakk> \<Longrightarrow>
     prod.snd (get_edge_and_costs_forward (not_blocked state) (current_flow state) (fst dd) (snd ee)) +
     weight (not_blocked state) (current_flow state) (snd ee # awalk_verts (fst ee) (map to_edge xs))
     \<le> ereal (\<cc> (F dd) + (\<cc> (B ee) + foldr (\<lambda>x. (+) (\<cc> x)) xs 0))"for ee dd
    using  unconstrained_awalk_drop_hd[of "(fst dd, snd dd)"] 
    by(subst ereal_add_homo[of _ "_ + _ "])
         (fastforce intro!:  ordered_ab_semigroup_add_class.add_mono conjunct1[OF get_edge_and_costs_forward_makes_cheaper[OF 
                                  refl, of _ "not_blocked state" "current_flow state"]]
                      intro:       trans[OF prod.collapse] 
                               cong[OF refl unconstrained_awalk_snd_verts_eq[of "fst dd" "snd dd"
                                       "snd ee" "fst ee", symmetric]]
                       simp add: \<E>_def \<E>_impl(1) \<E>_list_def to_list(1))
    have help3: 
    "\<lbrakk>(unconstrained_awalk ((fst ee, snd ee) # map to_edge xs) \<Longrightarrow>
       weight (not_blocked state) (current_flow state) (fst ee # awalk_verts (snd ee) (map to_edge xs))
        \<le> ereal (\<cc> (F ee) + foldr (\<lambda>x. (+) (\<cc> x)) xs 0));
       (\<And>e. e = B dd \<or> e = F ee \<or> e \<in> set xs \<Longrightarrow> not_blocked state (oedge e));
       (\<And>e. e = B dd \<or> e = F ee \<or> e \<in> set xs \<Longrightarrow> 0 < rcap (current_flow state) e) ;
       unconstrained_awalk ((snd dd, fst dd) # (fst ee, snd ee) # map to_edge xs);
       dd \<in> set \<E>_list; ee \<in> set \<E>_list; oedge ` set xs \<subseteq> set \<E>_list\<rbrakk> \<Longrightarrow>
      prod.snd (get_edge_and_costs_forward (not_blocked state) (current_flow state) (snd dd) (fst ee)) +
      weight (not_blocked state) (current_flow state) (fst ee # awalk_verts (snd ee) (map to_edge xs))
      \<le> ereal (\<cc> (B dd) + (\<cc> (F ee) + foldr (\<lambda>x. (+) (\<cc> x)) xs 0))"
    for dd ee
       using unconstrained_awalk_drop_hd[of "(snd dd, fst dd)"] 
       by(subst ereal_add_homo[of _ "_ + _ "])
         (fastforce intro!:  ordered_ab_semigroup_add_class.add_mono conjunct1[OF get_edge_and_costs_forward_makes_cheaper[OF 
                                  refl, of _ "not_blocked state" "current_flow state"]]
                      intro:       trans[OF prod.collapse] 
                               cong[OF refl unconstrained_awalk_snd_verts_eq[of "snd dd" "fst dd"
                                       "fst ee" "snd ee", symmetric]]
                       simp add: \<E>_def \<E>_impl(1) \<E>_list_def to_list(1))
     have help4: 
       "\<lbrakk>(unconstrained_awalk ((snd ee, fst ee) # map to_edge xs) \<Longrightarrow>
           weight (not_blocked state) (current_flow state) (snd ee # awalk_verts (fst ee) (map to_edge xs))
           \<le> ereal (\<cc> (B ee) + foldr (\<lambda>x. (+) (\<cc> x)) xs 0));
          (\<And>e. e = B dd \<or> e = B ee \<or> e \<in> set xs \<Longrightarrow> not_blocked state (oedge e));
          (\<And>e. e = cost_flow_network.B dd \<or> e = cost_flow_network.B ee \<or> e \<in> set xs \<Longrightarrow> 0 < rcap (current_flow state) e);
           unconstrained_awalk ((snd dd, fst dd) # (snd ee, fst ee) # map to_edge xs);
           dd \<in> set \<E>_list ;  ee \<in> set \<E>_list ; oedge ` set xs \<subseteq> set \<E>_list \<rbrakk> \<Longrightarrow>
        prod.snd (local.get_edge_and_costs_forward (not_blocked state) (current_flow state) (snd dd) (snd ee)) +
        weight (not_blocked state) (current_flow state) (snd ee # awalk_verts (fst ee) (map to_edge xs))
         \<le> ereal (\<cc> (B dd) + (\<cc> (B ee) + foldr (\<lambda>x. (+) (\<cc> x)) xs 0))" for ee dd
       using  unconstrained_awalk_drop_hd[of "(snd dd, fst dd)"] 
       by(subst ereal_add_homo[of _ "_ + _ "])
         (fastforce intro!:  ordered_ab_semigroup_add_class.add_mono conjunct1[OF get_edge_and_costs_forward_makes_cheaper[OF 
                                  refl, of _ "not_blocked state" "current_flow state"]]
                      intro:       trans[OF prod.collapse] 
                               cong[OF refl unconstrained_awalk_snd_verts_eq[of "snd dd" "fst dd"
                                       "snd ee" "fst ee", symmetric]]
                       simp add: \<E>_def \<E>_impl(1) \<E>_list_def to_list(1))+
    show ?case
      using 3
      by(induction e rule: cost_flow_network.to_vertex_pair.induct, 
         all \<open>induction d rule: cost_flow_network.to_vertex_pair.induct\<close>) 
        (auto simp add: make_pair_fst_snd simp del: cost_flow_network.\<cc>.simps 
              intro: help1 help2 help3 help4)
  qed

abbreviation "get_source_target_path_a_cond \<equiv> loopB.get_source_target_path_a_cond"

lemma get_source_target_path_a_ax:
  assumes "get_source_target_path_a_cond  state s t P b \<gamma> f"
  shows "0 < cost_flow_network.Rcap f (set P) \<and>
        (invar_isOptflow state \<longrightarrow> cost_flow_network.is_min_path f s t P) \<and>
         cost_flow_network.oedge ` set P \<subseteq> to_set (actives state) \<union> \<F> state \<and>
         distinct P"
  apply(insert assms)
  unfolding  loopB.get_source_target_path_a_cond_def
             get_source_target_path_a_def loopB.loopB_call1_cond_def
proof(cases "invar_isOptflow state", goal_cases)
  case 1
  define bf where  "bf = bellman_ford_forward (not_blocked state) (current_flow state) s"
  define tt where "tt = get_target_for_source_aux bf (balance state) (current_\<gamma> state) vs"
  define Pbf where "Pbf = search_rev_path_exec s bf t Nil"
  define PP where "PP = map (\<lambda>e. prod.fst (get_edge_and_costs_forward (not_blocked state) (current_flow state)
                                  (prod.fst e) (prod.snd e)))
                   (edges_of_vwalk Pbf)"
  have knowledge: True
                  "s \<in> VV" "t \<in> VV" "s \<noteq> t"
    "aux_invar state"
    "(\<forall>e\<in>\<F> state. 0 < f e)"
    "resreach f s t"
    "b = balance state"
    "\<gamma> = current_\<gamma> state"
    "s = get_source state"
    "t = get_target_for_source state s"
    "f = current_flow state"
    "invar_gamma state"
    "\<not> (\<forall>v\<in>VV. b v = 0)"
    "\<exists>s\<in>VV. (1 - \<epsilon>) * \<gamma> < b s"
    "\<exists>t\<in>VV. b t < - \<epsilon> * \<gamma> \<and> resreach f s t"
                  "t = tt"  "P = PP"
    using 1 
    by(auto simp add: bf_def tt_def Pbf_def PP_def  split: if_split)
      (meson+, metis (no_types, lifting) mult_minus_left,
       insert "1"(1), unfold get_target_for_source_def, presburger+)
  hence 
    "(\<forall>e\<in>to_rdgs to_pair (conv_to_rdg state) (to_graph (\<FF>_imp state)).
        0 < current_flow state (flow_network.oedge e))"
    by auto
  have  loopB_call1_cond: " loopB_call1_cond state"
    using  1 unfolding loopB.loopB_call1_cond_def by presburger
  have t_prop: "b t < - \<epsilon> * \<gamma>" "resreach f s t" 
    using get_target_for_source_ax[OF knowledge (8,9,12,10,11) loopB_call1_cond knowledge(13)]
    by auto
  then obtain pp where pp_prop:"augpath f pp" "fstv (hd pp) = s" "sndv (last pp) = t" "set pp \<subseteq> EEE"
    using cost_flow_network.resreach_imp_augpath[OF , of f s t] by auto
  obtain ppd where ppd_props:"augpath f ppd" "fstv (hd ppd) = s" "sndv (last ppd) = t" "set ppd \<subseteq> set pp"
                        "distinct ppd"
    using pp_prop 
    by (auto intro:  cost_flow_network.there_is_s_t_path[OF  _ _ _ refl, of f pp s t])
  obtain Q where Q_min:"cost_flow_network.is_min_path  f s t Q"
    apply(rule cost_flow_network.there_is_min_path[OF , of f s t ppd])
    using pp_prop ppd_props cost_flow_network.is_s_t_path_def 
    by auto

  hence Q_prop:"augpath f Q" "fstv (hd Q) = s" "sndv (last Q) = t"
        "set Q \<subseteq> EEE" "distinct Q"
    by(auto simp add: cost_flow_network.is_min_path_def 
              cost_flow_network.is_s_t_path_def)
  have no_augcycle: "\<nexists>C. augcycle f C" 
    using  "1"(1) "1"(2)  cost_flow_network.min_cost_flow_no_augcycle
    by(auto simp add: invar_isOptflow_def)
  obtain qq where  qq_prop:"augpath f qq"
     "fstv (hd qq) = s"
     "sndv (last qq) = t"
     "set qq
     \<subseteq> {e |e. e \<in> EEE \<and> cost_flow_network.oedge e \<in> to_set (actives state)} \<union>
        to_rdgs to_pair (conv_to_rdg state) (\<FF> state)"
     "foldr (\<lambda>x. (+) (\<cc> x)) qq 0 \<le> foldr (\<lambda>x. (+) (\<cc> x)) Q 0" "qq \<noteq> []"
  using algo.simulate_inactives_costs[OF  Q_prop(1-4) knowledge(5)
          refl knowledge(12) refl refl refl refl refl refl knowledge(4,6) no_augcycle]
  by auto
  have qq_len: "length qq \<ge> 1" 
    using qq_prop(2,3,6) knowledge(4)
    by(cases qq rule: list_cases3) auto
  have F_is: "\<FF> state = to_graph (\<FF>_imp state)" 
    by (simp add: "1"(1) from_aux_invar'(21))
  hence e_in:"e \<in> set qq \<Longrightarrow> e \<in> {e |e. e \<in> EEE \<and> cost_flow_network.oedge e \<in> to_set (actives state)} 
                   \<union> to_rdgs to_pair (conv_to_rdg state) (\<FF> state)" for e
      using qq_prop(4)  by auto
    hence e_es:"e \<in> set qq \<Longrightarrow> cost_flow_network.to_vertex_pair e \<in> set es" for e
      using es_E_frac algo.aux_invar_subs  knowledge(5) by fastforce
    have e_es':"e \<in> set qq \<Longrightarrow> oedge e \<in> \<E>" for e
      using  algo.aux_invar_subs[OF  knowledge(5) refl refl refl refl refl refl refl]
              e_in cost_flow_network.o_edge_res by auto
    have e_in_pp_weight:"e \<in> set qq \<Longrightarrow> prod.snd (get_edge_and_costs_forward (not_blocked state) 
                                 (current_flow state) (fstv e) (sndv e)) < PInfty" for e
  proof(goal_cases)
    case 1
    note e_es[OF 1]
    moreover have oedge_where: "oedge e \<in> to_set (actives state) \<or> oedge e \<in> \<F> state"
      using e_in F_is 1 by auto
    hence nb:"not_blocked state (oedge e)"
      by (meson Un_iff from_aux_invar'(22) knowledge(5))
 have oedgeE:"oedge e \<in> \<E>"
      using oedge_where from_aux_invar'(1,3)[OF knowledge(5)] by auto
    have "prod.snd (get_edge_and_costs_forward (not_blocked state) (current_flow state)
     (fstv e) (sndv e)) \<le> \<cc> e"
      using nb cost_flow_network.augpath_rcap_pos_strict'[OF qq_prop(1) 1] knowledge(12)
      by(auto intro:  conjunct1[OF get_edge_and_costs_forward_makes_cheaper
               [OF refl oedgeE, of "not_blocked state" "current_flow state"]] prod.collapse) 
    thus ?case by auto
  qed
  have bellman_ford:"bellman_ford connection_empty connection_lookup connection_invar connection_delete
     es vs (\<lambda> u v. prod.snd (get_edge_and_costs_forward (not_blocked state) (current_flow state) u v)) connection_update"
    by (simp add: bellman_ford knowledge(2) knowledge(3))
  have is_a_walk:"awalk UNIV s (map to_edge qq) tt" 
    using augpath_def knowledge(17) prepath_def qq_prop(1) qq_prop(2) qq_prop(3) by blast
  hence "vwalk_bet UNIV s (awalk_verts s (map cost_flow_network.to_vertex_pair qq)) tt"
    using  awalk_imp_vwalk by force
  moreover have weight_le_PInfty:"weight (not_blocked state) 
(current_flow state) (awalk_verts s (map cost_flow_network.to_vertex_pair qq)) < PInfty"
    using  path_flow_network_path_bf e_in_pp_weight is_a_walk bellman_ford qq_prop(2) by blast
  have no_neg_cycle_in_bf: "\<nexists>c. weight (not_blocked state) (current_flow state) c < 0 \<and> hd c = last c"
    using knowledge no_neg_cycle_in_bf 1 by blast
  have long_enough: "2 \<le> length (awalk_verts s (map cost_flow_network.to_vertex_pair qq))"
    using knowledge(4) awalk_verts_non_Nil calculation knowledge(17)
          hd_of_vwalk_bet'[OF calculation] last_of_vwalk_bet[OF calculation] 
    by (cases "awalk_verts s (map cost_flow_network.to_vertex_pair qq)" rule: list_cases3) auto 
  have tt_dist_le_PInfty:"prod.snd (the (connection_lookup bf tt)) < PInfty"
    unfolding bf_def bellman_ford_forward_def bellman_ford_init_algo_def bellman_ford_algo_def
    using no_neg_cycle_in_bf  knowledge(4,17,2,3)   vs_is_V weight_le_PInfty  is_a_walk long_enough 
    by (fastforce intro!:  bellman_ford.bellamn_ford_path_exists_result_le_PInfty[OF bellman_ford, of
            _ _ "(awalk_verts s (map cost_flow_network.to_vertex_pair qq))"])
   have t_dist_le_qq_weight:"prod.snd (the (connection_lookup bf t)) \<le>
                          weight (not_blocked state) 
                           (current_flow state) (awalk_verts s (map cost_flow_network.to_vertex_pair qq))"
    using   knowledge(4,17,2,3)   vs_is_V weight_le_PInfty  is_a_walk 
            bellman_ford.bellman_ford_computes_length_of_optpath[OF bellman_ford no_neg_cycle_in_bf, of s t]
            bellman_ford.opt_vs_path_def[OF bellman_ford, of s t]
            bellman_ford.vsp_pathI[OF bellman_ford long_enough, of s t]
            bellman_ford.weight_le_PInfty_in_vs[OF bellman_ford long_enough, of]
            calculation
    by (auto simp add: vwalk_bet_def bf_def bellman_ford_forward_def bellman_ford_init_algo_def bellman_ford_algo_def)
  hence t_prop:"prod.snd (the (connection_lookup bf t)) < PInfty"
    using knowledge(17) tt_dist_le_PInfty by blast
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
    using vs_is_V  pred_of_t_not_None knowledge(3)
    apply(subst sym[OF arg_cong[of _ _ rev, OF bellford.function_to_partial_function, simplified]])
    by(fastforce simp add: bellman_ford_forward_def bf_def bellman_ford_algo_def bellman_ford_init_algo_def
                 intro!:  bf_fw.search_rev_path_dom_bellman_ford[OF no_neg_cycle_in_bf] )+
  have weight_Pbf_snd: "weight (not_blocked state) 
          (current_flow state) Pbf = prod.snd (the (connection_lookup bf t))"
    unfolding Pbf_def
    using t_prop   vs_is_V  pred_of_t_not_None knowledge(2,3,4)
    by(fastforce simp add: bellman_ford_forward_def bf_def bellman_ford_init_algo_def bellman_ford_algo_def
                 intro!: bellman_ford.bellman_ford_search_rev_path_weight[OF 
                bellman_ford no_neg_cycle_in_bf, of bf s t])+
  hence weight_le_PInfty: "weight (not_blocked state) (current_flow state) Pbf < PInfty"
    using t_prop by auto
  have Pbf_opt_path: "bellman_ford.opt_vs_path vs
 (\<lambda>u v. prod.snd (get_edge_and_costs_forward (not_blocked state) (current_flow state) u v)) s t
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
         weight (not_blocked state) (current_flow state) Pbf =
         ereal  (foldr (\<lambda>e. (+) (\<cc> e))
        (map (\<lambda>e. prod.fst (get_edge_and_costs_forward (not_blocked state) (current_flow state) (prod.fst e) (prod.snd e)))
               (edges_of_vwalk Pbf)) 0) \<and>
         (\<forall>e\<in>set (map (\<lambda>e. prod.fst (get_edge_and_costs_forward (not_blocked state) (current_flow state) (prod.fst e)
                         (prod.snd e)))
           (edges_of_vwalk Pbf)).
    not_blocked state (flow_network.oedge e) \<and> 0 < cost_flow_network.rcap (current_flow state) e)"
    by(intro path_bf_flow_network_path[OF _ length_Pbf weight_le_PInfty refl]) simp
  hence Pbf_props: "awalk UNIV (hd Pbf) (edges_of_vwalk Pbf) (last Pbf)"
                   " weight (not_blocked state) (current_flow state) Pbf =
         ereal  (foldr (\<lambda>e. (+) (\<cc> e))
        (map (\<lambda>e. prod.fst (get_edge_and_costs_forward (not_blocked state) (current_flow state) (prod.fst e) (prod.snd e)))
               (edges_of_vwalk Pbf)) 0)"
                   "(\<And> e. e \<in> set (map (\<lambda>e. prod.fst (get_edge_and_costs_forward (not_blocked state) (current_flow state) (prod.fst e)
                         (prod.snd e)))
           (edges_of_vwalk Pbf)) \<Longrightarrow>
    not_blocked state (flow_network.oedge e) \<and> 0 < cost_flow_network.rcap (current_flow state) e)"
    by auto
  have "map (to_edge \<circ>
         (\<lambda>e. prod.fst (local.get_edge_and_costs_forward (not_blocked state) (current_flow state) (prod.fst e)
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
    using Pbf_props(1) same_edges length_Pbf  "1"(1) awalk_fst_last bellman_ford.weight.simps[OF bellman_ford] 
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
  moreover have Rcap_P:"0 < cost_flow_network.Rcap (current_flow state) (set PP)"
    using PP_def Pbf_props(3)
    by(auto simp add: cost_flow_network.Rcap_def)
  ultimately have "augpath (current_flow state) PP"
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
    have "not_blocked state e"
      using map_in_set same_edges "1"(1) PP_def Pbf_props(3) list.set_map by blast
    thus ?case
      using  from_aux_invar'(22)[of state, OF knowledge(5)] 1 by simp
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
  have qq_in_E':"set (map cost_flow_network.oedge qq) \<subseteq> \<E>" 
    using e_es' by auto
  have not_blocked_qq: "\<And> e . e \<in> set qq \<Longrightarrow> not_blocked state (oedge e)" 
    using  F_is from_aux_invar'(22)[OF knowledge(5)]  qq_prop(4) by fastforce
  have rcap_qq: "\<And> e . e \<in> set qq \<Longrightarrow> cost_flow_network.rcap (current_flow state) e > 0" 
    using  cost_flow_network.augpath_rcap_pos_strict'[OF  qq_prop(1) ] knowledge by simp
  have awalk': "unconstrained_awalk (map cost_flow_network.to_vertex_pair qq)"
    by (meson unconstrained_awalk_def awalkE' is_a_walk)
  have 
bf_weight_leq_res_costs:"weight (not_blocked state) (current_flow state) (awalk_verts s (map cost_flow_network.to_vertex_pair qq))
 \<le> foldr (\<lambda>x. (+) (\<cc> x)) qq 0" 
    using qq_in_E not_blocked_qq rcap_qq awalk' qq_len  e_es'
    by(auto intro!: bf_weight_leq_res_costs simp add:  \<E>_def \<E>_impl(1) \<E>_list_def  to_list(1))
  have oedge_of_EE: "flow_network.oedge ` EEE = \<E>" 
    by (meson  cost_flow_network.oedge_on_\<EE>)
  have " cost_flow_network.oedge ` set PP \<subseteq> \<E>"
    using from_aux_invar'(1,3)[OF knowledge(5)] oedge_of_p_allowed by blast
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
  ultimately have P_min: "cost_flow_network.is_min_path f s t PP"
    using Q_min P_in_E  knowledge(12)  distinctP
    by(auto simp add: cost_flow_network.is_min_path_def 
              cost_flow_network.is_s_t_path_def)
  show ?case
    using P_min distinctP Rcap_P oedge_of_p_allowed knowledge(12,18) by simp
next
  case 2
  thus ?case
    by(auto simp add: cost_flow_network.Rcap_def)
qed 

lemma path_flow_network_path_bf_backward:
  assumes e_weight:"\<And> e. e \<in> set pp \<Longrightarrow> prod.snd (get_edge_and_costs_backward nb f (fstv e) (sndv e)) < PInfty"
         and is_a_walk:"awalk UNIV s (map to_edge pp) tt" 
         and s_is_fstv: "s = fstv (hd pp)"
 and     bellman_ford:"bellman_ford connection_empty connection_lookup connection_invar connection_delete
     es vs (\<lambda> u v. prod.snd (get_edge_and_costs_backward nb f u v)) connection_update"  
shows
"weight_backward nb f (awalk_verts s (map cost_flow_network.to_vertex_pair pp)) < PInfty"
  using assms(1,2)[simplified assms(3)]
  apply(subst assms(3))
proof(induction pp  rule: list_induct3)
  case 1
  then show ?case 
    using  bellman_ford.weight.simps[OF bellman_ford] by auto
next
  case (2 x)
  then show ?case
    using  bellman_ford.weight.simps[OF bellman_ford] apply auto[1]
    apply(induction x rule: cost_flow_network.to_vertex_pair.induct)
    apply(simp add: cost_flow_network.to_vertex_pair.simps 
                     bellman_ford.weight.simps[OF bellman_ford] make_pair_fst_snd)+
    done
next
  case (3 e d es)
    have same_ends:"sndv e = fstv d"
    using 3(3)
    by(induction e rule: cost_flow_network.to_vertex_pair.induct)
      (auto intro: cost_flow_network.to_vertex_pair.induct[OF , of _ d]  
        simp add: bellman_ford.weight.simps[OF bellman_ford]
                           Awalk.awalk_simps make_pair_fst_snd 
                 cost_flow_network.vs_to_vertex_pair_pres(1))
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
and len:  "length pp \<ge> 2"
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
        nb (flow_network.oedge e) \<and> 0 < cost_flow_network.rcap f e)"
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
    nb (flow_network.oedge e) \<and> 0 < cost_flow_network.rcap f e)" 
    by (simp add: "3.IH" calculation(3))
  moreover have "nb (flow_network.oedge (prod.fst (get_edge_and_costs_backward nb f x y)))"
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
  assumes "invar_isOptflow state" "aux_invar state"
  shows   "\<nexists>c. weight_backward (not_blocked state) (current_flow state) c < 0 \<and> hd c = last c"
proof(rule nexistsI, goal_cases)
  case (1 c)
  have bellman_ford:"bellman_ford  connection_empty connection_lookup 
                 connection_invar connection_delete
     es vs (\<lambda> u v. prod.snd (get_edge_and_costs_backward (not_blocked state) (current_flow state) u v)) connection_update"
    by (simp add: bellman_ford_backward)
  have length_c: "length c \<ge> 2"
    using 1 bellman_ford.weight.simps[OF bellman_ford] 
    by(cases c rule: list_cases3) auto
  have weight_le_PInfty:"weight_backward (not_blocked state) (current_flow state) c < PInfty" 
    using "1"(1) by fastforce
  have path_with_props:"awalk UNIV (last c) (map prod.swap (rev (edges_of_vwalk c))) (hd c)"
       " weight_backward (not_blocked state) (current_flow state) c =
  ereal
   (foldr (\<lambda>e. (+) (\<cc> e))
     (map (\<lambda>e. prod.fst (get_edge_and_costs_backward (not_blocked state) (current_flow state) (prod.snd e) (prod.fst e)))
       (map prod.swap (rev (edges_of_vwalk c))))
     0)"
      "(\<And> e. e\<in>set (map (\<lambda>e. prod.fst (get_edge_and_costs_backward (not_blocked state) (current_flow state) (prod.snd e) (prod.fst e)))
             (map prod.swap (rev (edges_of_vwalk c)))) \<Longrightarrow>
      not_blocked state (flow_network.oedge e) \<and> 0 < cost_flow_network.rcap (current_flow state) e)"
    using path_bf_flow_network_path_backward[OF _ length_c weight_le_PInfty refl] by auto
  define cc where "cc = (map (\<lambda>e. prod.fst (get_edge_and_costs_backward (not_blocked state) (current_flow state) (prod.snd e) (prod.fst e)))
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
  moreover have "0 < cost_flow_network.Rcap (current_flow state) (set cc)"
    using cc_def path_with_props(3)
    by(auto simp add: cost_flow_network.Rcap_def)
  ultimately have agpath:"augpath (current_flow state) cc"
    by(simp add: augpath_def)
  have cc_in_E: "set cc \<subseteq> EEE"
  proof(rule, rule ccontr, goal_cases)
    case (1 e)
    hence "to_edge e \<in> set (edges_of_vwalk (rev c))"
      by (metis map_in_set same_edges[simplified edges_of_vwalk_rev_swap])
    then obtain c1 c2 where c_split:"c1@[prod.fst (to_edge e)]@[prod.snd (to_edge e)]@c2 = rev c" 
      apply(induction e rule: cost_flow_network.to_vertex_pair.induct)
      subgoal for e
        using edges_in_vwalk_split[of "fst e" "snd e" "rev c"]  multigraph.make_pair' by auto
      subgoal for e
        using edges_in_vwalk_split[of "snd e" "fst e" "rev c"]  multigraph.make_pair' by auto
    done
  have c_split:"rev c2@[prod.snd (to_edge e)]@[prod.fst (to_edge e)]@ rev c1 = c" 
    apply(subst sym[OF rev_rev_ident[of c]])
    apply(subst sym[OF c_split]) 
    by simp
  have le_infty:"prod.snd (get_edge_and_costs_backward (not_blocked state) (current_flow state) (prod.snd (to_edge e))
             (prod.fst (to_edge e))) < PInfty"
  proof(rule ccontr, goal_cases)
    case 1
    hence "prod.snd (get_edge_and_costs_backward (not_blocked state) (current_flow state) (prod.snd (cost_flow_network.to_vertex_pair e))
           (prod.fst (cost_flow_network.to_vertex_pair e)))
     = PInfty" by simp
    hence "weight_backward (not_blocked state) (current_flow state) c = PInfty"
      using bellman_ford.edge_and_Costs_none_pinfty_weight[OF bellman_ford]
            c_split by auto
    thus False
      using weight_le_PInfty by force
  qed
  have one_not_blocked:"not_blocked state (oedge e)"
    using less_PInfty_not_blocked  "1"(1) cc_def path_with_props(3) by blast
  hence "oedge e \<in> \<E>"
    using assms(2) 
    unfolding algo.aux_invar_def  algo.invar_aux22_def
                algo.invar_aux1_def algo.invar_aux3_def
    by auto
  thus ?case
    using  1(2) cost_flow_network.o_edge_res by blast
qed
  obtain C where "augcycle (current_flow state) C"
    apply(rule cost_flow_network.augcycle_from_non_distinct_cycle[OF  agpath])
    using "1"(1) awalk_f c_non_empt awalk_fst_last[OF _ awalk_f]
          awalk_fst_last[OF _ path_with_props(1)]  cc_in_E  "1"(1) cc_def path_with_props(2)
    by (auto, metis list.map_comp same_edges)
  then show ?case 
    using assms(1) invar_isOptflow_def cost_flow_network.min_cost_flow_no_augcycle by blast
qed

lemma to_edge_of_get_edge_and_costs_backward:
"cost_flow_network.to_vertex_pair (prod.fst (get_edge_and_costs_backward (not_blocked state) (current_flow state) a b)) = (b, a)"
  using to_edge_get_edge_and_costs_backward by force

lemma get_source_for_target_ax:
" \<lbrakk>b = balance state; \<gamma> = current_\<gamma> state; f = current_flow state; t = get_target state;
                         s = get_source_for_target state t; loopB_call2_cond state; invar_gamma state\<rbrakk>
                        \<Longrightarrow> s \<in> VV \<and> b s > \<epsilon> * \<gamma> \<and> resreach f s t"
  unfolding get_source_for_target_def
proof(rule if_E[where P= "\<lambda> x. s = x"], fast, goal_cases)
  case 1
  note assms = this
  have call2_cond: "loopB_call2_cond state"
    using  "1"(6) unfolding sym[OF get_source_for_target_def] by simp
  have t_prop: "t \<in> VV" "- (1 - \<epsilon>) * \<gamma> > b t"
    using get_target_axioms[OF 1(1,2,4)] "1"(6) unfolding sym[OF get_source_for_target_def] 
    by auto
  from 1 have knowledge: "get_target state \<in> VV"
    "aux_invar state"
    "(\<forall>e\<in>to_rdgs to_pair (conv_to_rdg state) (to_graph (\<FF>_imp state)).
        0 < current_flow state (cost_flow_network.oedge e))"
    "invar_isOptflow state" 
    "(\<exists>s\<in>VV. balance state s > (\<epsilon> * current_\<gamma> state) \<and> resreach (current_flow state) s t)"
    using t_prop(1) by auto
  then obtain ss where ss_pr: " balance state ss > (\<epsilon> * current_\<gamma> state)" "resreach (current_flow state) ss t" "ss \<in> VV"
    by auto
  then obtain p where "augpath (current_flow state) p" "fstv (hd p) = ss"
                      "sndv(last p) = t" "set p \<subseteq> EEE"
    using cost_flow_network.resreach_imp_augpath by blast
  moreover have s_neq_tt:"ss \<noteq> t" 
    using \<epsilon>_axiom(1) t_prop  ss_pr(1) 1(7) "1"(1) "1"(2)
    unfolding invar_gamma_def 
    by (smt (verit, ccfv_SIG) mult_less_cancel_right_pos)
  moreover have "\<nexists>C. augcycle(current_flow state) C"
    using cost_flow_network.is_opt_iff_no_augcycle knowledge(4)
    by (auto simp add: invar_isOptflow_def is_Opt_def )
  ultimately obtain pp where pp_prop:"augpath (current_flow state) pp"
     "fstv (hd pp) = ss" "sndv (last pp) = t"
     "set pp
     \<subseteq> {e |e. e \<in> EEE \<and> cost_flow_network.oedge e \<in> to_set (actives state)} \<union> to_rdgs to_pair (conv_to_rdg state) (\<FF> state)"
     "foldr (\<lambda>x. (+) (\<cc> x)) pp 0 \<le> foldr (\<lambda>x. (+) (\<cc> x)) p 0"
    using  algo.simulate_inactives_costs[of "current_flow state" p, of ss t state,
                        OF _ _ _ _ _  refl refl refl refl refl refl refl refl]
           1(8) by blast
  have F_is: "\<FF> state = to_graph (\<FF>_imp state)" 
    using knowledge(2) from_aux_invar'(21) by auto
  hence e_in:"e \<in> set pp \<Longrightarrow> e \<in> {e |e. e \<in> EEE \<and> cost_flow_network.oedge e \<in> to_set (actives state)} 
                   \<union> to_rdgs to_pair (conv_to_rdg state) (\<FF> state)" for e
      using pp_prop(4)  by auto
    hence e_es:"e \<in> set pp \<Longrightarrow> cost_flow_network.to_vertex_pair e \<in> set es" for e
      using es_E_frac algo.aux_invar_subs knowledge(2) by fastforce
  have e_in_pp_weight:"e \<in> set pp \<Longrightarrow> prod.snd (get_edge_and_costs_backward (not_blocked state) (current_flow state) (sndv e) (fstv e)) < PInfty" for e
  proof(goal_cases)
    case 1
    note e_es[OF 1]     
    moreover have oedge_where:"oedge e \<in> to_set (actives state) \<or> oedge e \<in> \<F> state"
      using e_in F_is 1 by auto
    hence nb:"not_blocked state (oedge e)"
      by (meson Un_iff from_aux_invar'(22) knowledge(2))
    have oedgeE:"oedge e \<in> \<E>"
      using oedge_where from_aux_invar'(1,3)[OF knowledge(2)] by auto
    have posflow:"\<exists> d. e = B d \<Longrightarrow> current_flow state (oedge e) > 0" 
      using cost_flow_network.augpath_rcap_pos_strict'[OF  pp_prop(1) 1]
      by(induction  rule: cost_flow_network.oedge.cases[OF  , of e])
         auto
    have "prod.snd (get_edge_and_costs_backward (not_blocked state) (current_flow state)
     (sndv e) (fstv e)) \<le> \<cc> e"
      using nb cost_flow_network.augpath_rcap_pos_strict'[OF pp_prop(1) 1] 
      by(auto intro:  conjunct1[OF get_edge_and_costs_backward_makes_cheaper
               [OF refl oedgeE, of "not_blocked state" "current_flow state"]] prod.collapse) 
    thus ?case by auto
  qed
  have bellman_ford:"bellman_ford connection_empty connection_lookup connection_invar connection_delete
     es vs (\<lambda> u v. prod.snd (get_edge_and_costs_backward (not_blocked state) (current_flow state) u v)) connection_update"
    by (simp add: bellman_ford_backward knowledge(2) knowledge(3))
  have is_a_walk:"awalk UNIV ss (map to_edge pp) t"
    using pp_prop by (auto simp add:  augpath_def prepath_def)
  hence "vwalk_bet UNIV ss (awalk_verts ss (map cost_flow_network.to_vertex_pair pp)) t"
    using  awalk_imp_vwalk by force
  have is_a_walk':"awalk UNIV t (map to_edge (map cost_flow_network.erev (rev pp))) ss"
    using awalk_UNIV_rev[OF is_a_walk] cost_flow_network.rev_erev_swap[OF ,of pp]  rev_map[of cost_flow_network.erev pp] by simp 
  have lengthpp: "pp\<noteq> []" 
    using is_a_walk s_neq_tt by fastforce
  moreover have weight_le_PInfty:"weight_backward (not_blocked state) 
(current_flow state) (awalk_verts t (map cost_flow_network.to_vertex_pair (map cost_flow_network.erev (rev pp)))) < PInfty"
    apply(rule path_flow_network_path_bf_backward)
    subgoal for e 
      apply(induction  e rule: cost_flow_network.erev.induct)
      using   e_in_pp_weight 
      by (metis cost_flow_network.erve_erve_id cost_flow_network.vs_erev(1,2) in_set_map set_rev)+
    using is_a_walk'  bellman_ford pp_prop(3) cost_flow_network.rev_prepath_fst_to_lst[OF  lengthpp] by auto
  define connections where "connections = 
          (bellman_ford_backward (not_blocked state) (current_flow state) t)"
  have no_neg_cycle_in_bf: "\<nexists>c. weight_backward (not_blocked state) (current_flow state) c < 0 \<and> hd c = last c"
    using knowledge(2) knowledge(4) no_neg_cycle_in_bf_backward by blast
  have long_enough: "2 \<le> length (awalk_verts t (map cost_flow_network.to_vertex_pair (map cost_flow_network.erev (rev pp))))"
    by (simp add: awalk_verts_conv le_simps(3) lengthpp) 
  have ss_dist_le_PInfty:"prod.snd (the (connection_lookup connections ss)) < PInfty"
    unfolding connections_def bellman_ford_backward_def 
     bellman_ford_algo_def bellman_ford_init_algo_def
    using no_neg_cycle_in_bf  s_neq_tt  ss_pr(3) vs_is_V weight_le_PInfty  is_a_walk long_enough t_prop(1) 
          is_a_walk' 
    by (fastforce intro!: bellman_ford.bellamn_ford_path_exists_result_le_PInfty[OF bellman_ford, of
            _ _ "(awalk_verts t (map cost_flow_network.to_vertex_pair (map cost_flow_network.erev (rev pp))))"] )   
  have s_prop:"balance state s >  \<epsilon> * current_\<gamma> state \<and>
         s \<in> set vs \<and> prod.snd (the (connection_lookup connections s)) < PInfty"
    using ss_dist_le_PInfty ss_pr(1) ss_pr(3) vs_is_V  "1"(9) assms(4)
    by(intro get_source_for_target_aux[of vs "current_\<gamma> state"  "balance state"  connections s]) 
      (auto  simp add: connections_def )
  have t_neq_s: "t \<noteq> s"
    using t_prop s_prop "1"(1) "1"(2) "1"(7) invar_gamma_def
    by (smt (verit, del_insts) mult_less_cancel_right_pos)
  have t_in_dom: "s \<in> dom (connection_lookup  connections)"
    using s_prop
    by (auto simp add: bellman_ford.bellman_ford_init_dom_is[OF bellman_ford]
                       bellman_ford.same_domain_bellman_ford[OF bellman_ford]
                       connections_def bellman_ford_backward_def bellman_ford_algo_def bellman_ford_init_algo_def)
  hence pred_of_s_not_None: "prod.fst (the (connection_lookup connections s)) \<noteq> None"
    using t_neq_s s_prop bellman_ford.bellman_ford_pred_non_infty_pres[OF bellman_ford, of t "length vs -1"]
    by(auto simp add:  connections_def bellman_ford_forward_def 
         bellman_ford.invar_pred_non_infty_def[OF bellman_ford]
                        bellman_ford_backward_def bellman_ford_algo_def bellman_ford_init_algo_def)
  define Pbf where "Pbf = rev (bellford.search_rev_path  t connections s)"
  have "weight_backward (not_blocked state)  
          (current_flow state) Pbf = prod.snd (the (connection_lookup connections s))"
    unfolding Pbf_def 
    using t_prop  t_neq_s  s_prop(1) vs_is_V  pred_of_s_not_None 
    by (fastforce simp add: bellman_ford_backward_def connections_def bellman_ford_algo_def bellman_ford_init_algo_def
                 intro!: bellman_ford.bellman_ford_search_rev_path_weight[OF 
                bellman_ford no_neg_cycle_in_bf, of connections t s])
  hence weight_le_PInfty: "weight_backward (not_blocked state) (current_flow state) Pbf < PInfty"
    using s_prop by auto
  have Pbf_opt_path: "bellman_ford.opt_vs_path vs
 (\<lambda>u v. prod.snd (get_edge_and_costs_backward (not_blocked state) (current_flow state) u v)) t s
 (rev (bellford.search_rev_path t connections s))"
    using t_prop  t_neq_s  s_prop(1) vs_is_V  pred_of_s_not_None 
    by (auto simp add: bellman_ford_backward_def connections_def bellman_ford_algo_def bellman_ford_init_algo_def
                 intro!: bellman_ford.computation_of_optimum_path[OF bellman_ford no_neg_cycle_in_bf])
  hence length_Pbf:"2 \<le> length Pbf" 
    by(auto simp add: bellman_ford.opt_vs_path_def[OF bellman_ford]
      bellman_ford.vs_path_def[OF bellman_ford] Pbf_def)
  have "awalk UNIV (last Pbf) (map prod.swap (rev (edges_of_vwalk Pbf))) (hd Pbf) \<and>
  weight_backward (not_blocked state) (current_flow state) Pbf =
  ereal
   (foldr (\<lambda>e. (+) (\<cc> e))
     (map (\<lambda>e. prod.fst (get_edge_and_costs_backward (not_blocked state) (current_flow state) (prod.snd e) (prod.fst e)))
       (map prod.swap (rev (edges_of_vwalk Pbf))))
     0) \<and>
  (\<forall>e\<in>set (map (\<lambda>e. prod.fst (get_edge_and_costs_backward (not_blocked state) (current_flow state) (prod.snd e) (prod.fst e)))
             (map prod.swap (rev (edges_of_vwalk Pbf)))).
      not_blocked state (cost_flow_network.oedge e) \<and> 0 < cost_flow_network.rcap (current_flow state) e)"
   using path_bf_flow_network_path_backward[OF _ length_Pbf weight_le_PInfty refl] by simp
   hence Pbf_props: "awalk UNIV (last Pbf) (map prod.swap (rev (edges_of_vwalk Pbf))) (hd Pbf)"
                   "weight_backward (not_blocked state) (current_flow state) Pbf =
  ereal
   (foldr (\<lambda>e. (+) (\<cc> e))
     (map (\<lambda>e. prod.fst (get_edge_and_costs_backward (not_blocked state) (current_flow state) (prod.snd e) (prod.fst e)))
       (map prod.swap (rev (edges_of_vwalk Pbf))))
     0)"
         "(\<And> e. e  \<in>set (map (\<lambda>e. prod.fst (get_edge_and_costs_backward (not_blocked state) (current_flow state) (prod.snd e) (prod.fst e)))
             (map prod.swap (rev (edges_of_vwalk Pbf)))) \<Longrightarrow>
      not_blocked state (cost_flow_network.oedge e) \<and> 0 < cost_flow_network.rcap (current_flow state) e)"
    by auto
  define P where "P = (map (\<lambda>e. prod.fst (get_edge_and_costs_backward (not_blocked state) (current_flow state) (prod.snd e) (prod.fst e)))
             (map prod.swap (rev (edges_of_vwalk Pbf))))"
  have same_edges:"(map cost_flow_network.to_vertex_pair P) = (map prod.swap (rev (edges_of_vwalk Pbf)))"
    by (auto simp add: to_edge_of_get_edge_and_costs_backward P_def get_edge_and_costs_forward_def Let_def)
  moreover have awalk_f:" awalk UNIV (fstv (hd P)) (map cost_flow_network.to_vertex_pair P) 
(sndv (last P))"
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
  moreover have "0 < cost_flow_network.Rcap (current_flow state) (set P)"
    using P_def Pbf_props(3)
    by(auto simp add: cost_flow_network.Rcap_def)
  ultimately have "augpath (current_flow state) P"
    by(auto simp add: cost_flow_network.augpath_def)
  moreover have "fstv (hd P) = s" 
    using awalk_f same_edges Pbf_opt_path  awalk_ends[OF Pbf_props(1)] t_neq_s
          P_def bellman_ford.opt_vs_path_def[OF bellman_ford]
                        bellman_ford.vs_path_def[OF bellman_ford] Pbf_def
    by (metis (no_types, lifting))  
  moreover have "sndv (last P) = t" 
    using awalk_f same_edges Pbf_opt_path  awalk_ends[OF Pbf_props(1)] t_neq_s
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
        using edges_in_vwalk_split[of "fst e" "snd e" "rev Pbf"]  multigraph.make_pair' by auto
      subgoal for e
        using edges_in_vwalk_split[of "snd e" "fst e" "rev Pbf"] multigraph.make_pair' by auto
      done
  have c_split:"rev c2@[prod.snd (to_edge e)]@[prod.fst (to_edge e)]@ rev c1 = Pbf" 
    apply(subst sym[OF rev_rev_ident[of Pbf]])
    apply(subst sym[OF c_split]) 
    by simp
  have le_infty:"prod.snd (get_edge_and_costs_backward (not_blocked state) (current_flow state) (prod.snd (to_edge e))
             (prod.fst (to_edge e))) < PInfty"
  proof(rule ccontr, goal_cases)
    case 1
    hence "prod.snd (get_edge_and_costs_backward (not_blocked state) (current_flow state) (prod.snd (cost_flow_network.to_vertex_pair e))
           (prod.fst (cost_flow_network.to_vertex_pair e)))
     = PInfty" by simp
    hence "weight_backward (not_blocked state) (current_flow state) Pbf = PInfty"
      using bellman_ford.edge_and_Costs_none_pinfty_weight[OF bellman_ford]
            c_split by auto
    thus False
      using weight_le_PInfty by force
  qed
  have one_not_blocked:"not_blocked state (oedge e)"
    using less_PInfty_not_blocked  "1"(1) P_def Pbf_props(3) by blast
  hence "oedge e \<in> \<E>"
    using knowledge(2)
    unfolding algo.aux_invar_def  algo.invar_aux22_def
                algo.invar_aux1_def algo.invar_aux3_def
    by auto
  thus ?case 
    using "1"(2)  cost_flow_network.o_edge_res by blast
  qed
  ultimately have "resreach f s t"
    using cost_flow_network.augpath_imp_resreach 1(3) by fast  
  thus ?case 
    using assms(1) assms(2) s_prop vs_is_V by blast
next
  case 2
  have "\<exists> s.
        s \<in> VV \<and> balance state s > \<epsilon> * current_\<gamma> state \<and> resreach (current_flow state) s t"
    using 2(6)
    unfolding LoopB.loopB.loopB_call2_cond_def[OF loopB] 2(1-4) Let_def
    by metis
  moreover have "s = (SOME s. s \<in> VV \<and> balance state s > \<epsilon> * current_\<gamma> state \<and>
             resreach (current_flow state) s t)"
    using "2"(4) "2"(9) by fastforce
  ultimately show ?case 
    using 2(1-4)
    by(auto intro!: someI_ex)
qed

lemma bf_weight_backward_leq_res_costs:
assumes "set (map cost_flow_network.oedge qq) \<subseteq> \<E>"
    " \<And> e. e \<in> set qq \<Longrightarrow> not_blocked state (cost_flow_network.oedge e)"
    "\<And> e. e \<in> set qq \<Longrightarrow> 0 < cost_flow_network.rcap (current_flow state) e"
    "unconstrained_awalk (map cost_flow_network.to_vertex_pair qq)"
   and  qq_len: "length qq \<ge> 1"
 shows "weight_backward (not_blocked state) (current_flow state) 
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
                                  refl, of _ "not_blocked state" "current_flow state"]] 
                     intro: surjective_pairing prod.collapse
           simp add: \<E>_def \<E>_impl(1) \<E>_list_def to_list(1) make_pair_fst_snd
           simp del: cost_flow_network.\<cc>.simps)+
 next
   case (3 e d ds)
   have help1: 
  "weight_backward (not_blocked state) (current_flow state)
     (butlast (awalk_verts s (map (prod.swap \<circ> to_edge) (rev ds) @ [(snd ee, fst ee)])) @ [snd dd]) +
    prod.snd (local.get_edge_and_costs_backward (not_blocked state) (current_flow state) (snd dd) (fst dd))
    \<le> ereal (local.\<c> dd + (local.\<c> ee + foldr (\<lambda>x. (+) (\<cc> x)) ds 0))" 
  if assms:"(\<And>s. unconstrained_awalk ((fst ee, snd ee) # map to_edge ds) \<Longrightarrow>
          weight_backward (not_blocked state) (current_flow state)
           (awalk_verts s (map (prod.swap \<circ> to_edge) (rev ds) @ [(snd ee, fst ee)]))
          \<le> ereal (local.\<c> ee + foldr (\<lambda>x. (+) (\<cc> x)) ds 0))"
    "(\<And>e. e = cost_flow_network.F dd \<or> e = cost_flow_network.F ee \<or> e \<in> set ds \<Longrightarrow>
          not_blocked state (oedge e))"
    "(\<And>e. e = cost_flow_network.F dd \<or> e = cost_flow_network.F ee \<or> e \<in> set ds \<Longrightarrow>
          0 < rcap (current_flow state) e)"
    "unconstrained_awalk ((fst dd, snd dd) # (fst ee, snd ee) # map to_edge ds)"
    "dd \<in> local.\<E> " "ee \<in> local.\<E> " "oedge ` set ds \<subseteq> local.\<E>"
   for ee dd
     using assms unconstrained_awalk_snd_verts_eq  unconstrained_awalk_drop_hd[of "(fst _, snd _)" "(fst _, snd _)#map to_edge _"]
        by(subst ereal_add_homo[of _ "_ + _ "], subst add.commute) 
          (fastforce intro!: add_mono[OF conjunct1[OF get_edge_and_costs_backward_makes_cheaper[OF 
                                  refl, of _ "not_blocked state" "current_flow state", of "F _", simplified]]] prod.collapse simp add: awalk_verts_append_last')
      have help2: "weight_backward (not_blocked state) (current_flow state)
     (butlast (awalk_verts s (map (prod.swap \<circ> to_edge) (rev ds) @ [(fst ee, snd ee)])) @ [snd dd]) +
    prod.snd (local.get_edge_and_costs_backward (not_blocked state) (current_flow state) (snd dd) (fst dd))
    \<le> ereal (local.\<c> dd + (foldr (\<lambda>x. (+) (\<cc> x)) ds 0 - local.\<c> ee))"
        if assms: "(\<And>s. unconstrained_awalk ((snd ee, fst ee) # map to_edge ds) \<Longrightarrow>
          weight_backward (not_blocked state) (current_flow state)
           (awalk_verts s (map (prod.swap \<circ> to_edge) (rev ds) @ [(fst ee, snd ee)]))
          \<le> ereal (foldr (\<lambda>x. (+) (\<cc> x)) ds 0 - local.\<c> ee))"
         "(\<And>e. e = F dd \<or> e = B ee \<or> e \<in> set ds \<Longrightarrow> not_blocked state (oedge e))"
         "(\<And>e. e = F dd \<or> e = B ee \<or> e \<in> set ds \<Longrightarrow> 0 < rcap (current_flow state) e)"
         " unconstrained_awalk ((fst dd, snd dd) # (snd ee, fst ee) # map to_edge ds)"
         "dd \<in> local.\<E>" "ee \<in> local.\<E>"
         "oedge ` set ds \<subseteq> local.\<E>" for dd ee
        using assms
        using unconstrained_awalk_snd_verts_eq  unconstrained_awalk_drop_hd[of "(fst _, snd _)" "(snd _, fst _)#map to_edge _"]
        by(subst ereal_add_homo[of _ "_ _ _ "], subst add.commute)
          (fastforce intro!: add_mono[OF conjunct1[OF get_edge_and_costs_backward_makes_cheaper[OF 
                                  refl, of _ "not_blocked state" "current_flow state", of "F _", simplified]]] prod.collapse simp add: awalk_verts_append_last')
      have help3: "   weight_backward (not_blocked state) (current_flow state)
     (butlast (awalk_verts s (map (prod.swap \<circ> to_edge) (rev ds) @ [(snd ee, fst ee)])) @ [fst dd]) +
    prod.snd (local.get_edge_and_costs_backward (not_blocked state) (current_flow state) (fst dd) (snd dd))
    \<le> ereal (local.\<c> ee + foldr (\<lambda>x. (+) (\<cc> x)) ds 0 - local.\<c> dd)"
        if assms: "(\<And>s. unconstrained_awalk ((fst ee, snd ee) # map to_edge ds) \<Longrightarrow>
          weight_backward (not_blocked state) (current_flow state)
           (awalk_verts s (map (prod.swap \<circ> to_edge) (rev ds) @ [(snd ee, fst ee)]))
          \<le> ereal (local.\<c> ee + foldr (\<lambda>x. (+) (\<cc> x)) ds 0))"
          "(\<And>e. e = cost_flow_network.B dd \<or> e = cost_flow_network.F ee \<or> e \<in> set ds \<Longrightarrow>
          not_blocked state (oedge e))"
          "(\<And>e. e = cost_flow_network.B dd \<or> e = cost_flow_network.F ee \<or> e \<in> set ds \<Longrightarrow>
          0 < rcap (current_flow state) e)"
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
                                  refl, of _ "not_blocked state" "current_flow state", of "B _", simplified]]])
      have help4: "  weight_backward (not_blocked state) (current_flow state)
           (butlast (awalk_verts s (map (prod.swap \<circ> to_edge) (rev ds) @ [(fst ee, snd ee)])) @ [fst dd]) +
          prod.snd (local.get_edge_and_costs_backward (not_blocked state) (current_flow state) (fst dd) (snd dd))
         \<le> ereal (foldr (\<lambda>x. (+) (\<cc> x)) ds 0 - local.\<c> ee - local.\<c> dd)" if assms:
         "(\<And>s. unconstrained_awalk ((snd ee, fst ee) # map to_edge ds) \<Longrightarrow>
          weight_backward (not_blocked state) (current_flow state)
           (awalk_verts s (map (prod.swap \<circ> to_edge) (rev ds) @ [(fst ee, snd ee)]))
          \<le> ereal (foldr (\<lambda>x. (+) (\<cc> x)) ds 0 - local.\<c> ee))"
         "(\<And>e. e = B dd \<or> e = B ee \<or> e \<in> set ds \<Longrightarrow> not_blocked state (oedge e)) "
         " (\<And>e. e = B dd \<or> e = B ee \<or> e \<in> set ds \<Longrightarrow> 0 < rcap (current_flow state) e)"
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
                                  refl, of _ "not_blocked state" "current_flow state", of "B _", simplified]]]) 
   show ?case
 using 3
  by(induction e rule: cost_flow_network.to_vertex_pair.induct, 
    all \<open>induction d rule: cost_flow_network.to_vertex_pair.induct\<close>) 
    (auto simp add: make_pair_fst_snd rev_map awalk_verts_append_last[of _ "_@[_]" "_ _" "_ _", simplified] 
                    sym[OF bellman_ford.costs_last[OF bellman_ford_backward]]
             intro: help1 help2 help3 help4)
qed

lemma Forest_conv_erev_sym: 
  assumes"cost_flow_network.consist conv" 
shows " e \<in> to_rdgs to_pair conv forst \<longleftrightarrow>
                             cost_flow_network.erev e \<in> to_rdgs to_pair conv forst"
  apply(rule cost_flow_network.consistencyE[OF  assms])
  unfolding  to_rdgs_def  cost_flow_network.\<EE>_def
  apply(induction e rule: cost_flow_network.erev.induct)
  by(auto simp add: make_pair_fst_snd)
    (smt (verit, best) Int_Collect swap_simp to_pair_axioms)+

abbreviation "get_source_target_path_b_cond \<equiv> loopB.get_source_target_path_b_cond "

lemma get_source_target_path_b_ax:
  assumes "get_source_target_path_b_cond  state s t P b \<gamma> f"
  shows "0 < cost_flow_network.Rcap f (set P) \<and>
        (invar_isOptflow state \<longrightarrow> cost_flow_network.is_min_path f s t P) \<and>
         cost_flow_network.oedge ` set P \<subseteq> to_set (actives state) \<union> \<F> state \<and>
         distinct P"
  apply(insert assms)
  unfolding  loopB.get_source_target_path_b_cond_def
             get_source_target_path_b_def loopB.loopB_call2_cond_def
proof(cases "invar_isOptflow state", goal_cases)
  case 1
  have loopB_call2_cond: "loopB_call2_cond state"
    using 1 unfolding loopB.loopB_call2_cond_def Let_def by force
  define bf where  "bf = bellman_ford_backward (not_blocked state) (current_flow state) t"
  define ss where "ss = get_source_for_target_aux bf (balance state) (current_\<gamma> state) vs"
  define Pbf where "Pbf = rev'(search_rev_path_exec t bf s Nil)"
  define PP where "PP = map (\<lambda>e. prod.fst (get_edge_and_costs_backward (not_blocked state) (current_flow state)
                                  (prod.snd e) (prod.fst e))) (edges_of_vwalk Pbf)"
  have knowledge: True
                  "s \<in> VV" "t \<in> VV" "s \<noteq> t"
    "aux_invar state"
    "(\<forall>e\<in>\<F> state. 0 < f e)"
    "resreach f s t"
    "b = balance state"
    "\<gamma> = current_\<gamma> state"
    "t = get_target state"
    "s = get_source_for_target state t"
    "f = current_flow state"
    "invar_gamma state"
    "\<not> (\<forall>v\<in>VV. b v = 0)"
    "\<exists>t\<in>VV. -(1 - \<epsilon>) * \<gamma> > b t"
    "\<exists>s\<in>VV. b s > \<epsilon> * \<gamma> \<and> resreach f s t"
                  "s = ss"  "P = PP"
    using 1 
     by(auto intro: loopB.loopB_call2_condE[OF loopB_call2_cond] 
          simp add: bf_def ss_def Pbf_def PP_def split: if_split)
       (insert"1"(1) , unfold get_source_for_target_def, presburger+)  
  hence 
    "(\<forall>e\<in>to_rdgs to_pair (conv_to_rdg state) (to_graph  (\<FF>_imp state)).
        0 < current_flow state (cost_flow_network.oedge e))"
    by auto
  have s_prop: "b s > \<epsilon> * \<gamma>" "resreach f s t" 
    using get_source_for_target_ax[OF knowledge (8,9,12,10,11) loopB_call2_cond knowledge(13)]
    by auto
  then obtain pp where pp_prop:"augpath f pp" "fstv (hd pp) = s" "sndv (last pp) = t" "set pp \<subseteq> EEE"
    using cost_flow_network.resreach_imp_augpath[OF , of f s t] by auto
  obtain ppd where ppd_props:"augpath f ppd" "fstv (hd ppd) = s" "sndv (last ppd) = t" "set ppd \<subseteq> set pp"
                        "distinct ppd"
    using pp_prop 
    by (auto intro:  cost_flow_network.there_is_s_t_path[OF  _ _ _ refl, of f pp s t])
  obtain Q where Q_min:"cost_flow_network.is_min_path f s t Q"
    apply(rule cost_flow_network.there_is_min_path[OF , of f s t ppd])
    using pp_prop ppd_props cost_flow_network.is_s_t_path_def 
    by auto

  hence Q_prop:"augpath f Q" "fstv (hd Q) = s" "sndv (last Q) = t"
        "set Q \<subseteq> EEE" "distinct Q"
    by(auto simp add: cost_flow_network.is_min_path_def 
              cost_flow_network.is_s_t_path_def)
  have no_augcycle: "\<nexists>C. augcycle f C" 
    using  "1"(1) "1"(2)  cost_flow_network.min_cost_flow_no_augcycle
    by(auto simp add: invar_isOptflow_def)
  obtain qq where  qq_prop:"augpath f qq"
     "fstv (hd qq) = s"
     "sndv (last qq) = t"
     "set qq
     \<subseteq> {e |e. e \<in> EEE \<and> cost_flow_network.oedge e \<in> to_set (actives state)} \<union>
        to_rdgs to_pair (conv_to_rdg state) (\<FF> state)"
     "foldr (\<lambda>x. (+) (\<cc> x)) qq 0 \<le> foldr (\<lambda>x. (+) (\<cc> x)) Q 0" "qq \<noteq> []"
  using algo.simulate_inactives_costs[OF Q_prop(1-4) knowledge(5)
          refl knowledge(12) refl refl refl refl refl refl knowledge(4,6) no_augcycle]
  by auto
  have qq_len: "length qq \<ge> 1" "qq \<noteq> []"
    using qq_prop(2,3,6) knowledge(4)
    by( all \<open>cases qq rule: list_cases3\<close>) auto
  have F_is: "\<FF> state = to_graph (\<FF>_imp state)" 
    by (simp add: "1"(1) from_aux_invar'(21))
  have consist: "cost_flow_network.consist (conv_to_rdg state)" 
    using from_aux_invar'(6) knowledge(5) by auto
  hence "e \<in> set qq \<Longrightarrow> e \<in> {e |e. e \<in> EEE \<and> cost_flow_network.oedge e \<in> to_set (actives state)} 
                   \<union> to_rdgs to_pair (conv_to_rdg state) (\<FF> state)" for e
    using qq_prop(4)  by auto
 hence e_in:"e \<in> set (map cost_flow_network.erev (rev qq)) \<Longrightarrow> e \<in> {e |e. e \<in> EEE \<and> cost_flow_network.oedge e \<in> to_set (actives state)} 
                   \<union> to_rdgs to_pair (conv_to_rdg state) (\<FF> state)" for e
   using cost_flow_network.Residuals_project_erev_sym Forest_conv_erev_sym[OF consist] by (auto, blast, meson)
    hence e_es:"e \<in> set (map cost_flow_network.erev (rev qq)) \<Longrightarrow> oedge e \<in> \<E>" for e
      using algo.aux_invar_subs[OF   knowledge(5) refl refl refl refl refl refl refl] 
            cost_flow_network.o_edge_res by blast
  have e_in_pp_weight:"e \<in> set (map cost_flow_network.erev (rev qq)) \<Longrightarrow>
         prod.snd (get_edge_and_costs_backward (not_blocked state) (current_flow state) (fstv e)
               (sndv e))
         < PInfty" for e
  proof(goal_cases)
    case 1
    hence 11: "cost_flow_network.erev e \<in> set  qq"
      using in_set_map cost_flow_network.erve_erve_id[OF  ] set_rev by metis
    note e_es[OF 1]
    moreover have oedgeF:"oedge e \<in> to_set (actives state) \<or> oedge e \<in> \<F> state"
      using e_in F_is 1 by auto
    hence oedgeE:"oedge e \<in> \<E>"
      using calculation by blast
    hence not_blocked:"not_blocked state (oedge e)"
      using oedgeF  from_aux_invar'(22)[OF knowledge(5)] by auto
    moreover have flowpos:"\<exists> d. (cost_flow_network.erev e) = B d\<Longrightarrow> current_flow state (oedge (cost_flow_network.erev e)) > 0" 
      using cost_flow_network.augpath_rcap_pos_strict'[OF  qq_prop(1) 11] knowledge(12)
      by(induction rule: cost_flow_network.oedge.cases[OF  , of e])
      auto  
      ultimately show ?case 
        using "11" cost_flow_network.augpath_rcap_pos_strict cost_flow_network.oedge_and_reversed cost_flow_network.vs_erev
                get_edge_and_costs_backward_makes_cheaper[OF refl _ _ _ prod.collapse, 
                       of "flow_network.erev e" "not_blocked state" "current_flow state"] knowledge(12)  qq_prop(1) 
        by auto
  qed 
  have bellman_ford:"bellman_ford connection_empty connection_lookup connection_invar connection_delete
     es vs (\<lambda> u v. prod.snd (get_edge_and_costs_backward (not_blocked state) (current_flow state) u v)) connection_update "
    by (simp add: bellman_ford_backward knowledge(2) knowledge(3))
  have is_a_walk:"awalk UNIV t (map cost_flow_network.to_vertex_pair (map cost_flow_network.erev (rev qq))) ss" 
    using awalk_UNIV_rev[of ss "map to_edge qq" t, simplified rev_map, simplified]
    using  knowledge(17)  qq_prop(1) qq_prop(2) qq_prop(3) 
    by(auto simp add:  cost_flow_network.to_vertex_pair_erev_swap prepath_def  augpath_def )
  hence vwalk_bettt:"vwalk_bet UNIV t (awalk_verts t (map cost_flow_network.to_vertex_pair (map cost_flow_network.erev (rev qq)))) ss"
    using  awalk_imp_vwalk by force
  moreover have weight_le_PInfty:"weight_backward (not_blocked state) 
(current_flow state) (awalk_verts t (map cost_flow_network.to_vertex_pair (map cost_flow_network.erev (rev qq)))) < PInfty"
    using e_in_pp_weight  is_a_walk bellman_ford_backward qq_prop(3) 
          cost_flow_network.rev_prepath_fst_to_lst[OF  qq_len(2)] 
    by (intro path_flow_network_path_bf_backward) auto
  have no_neg_cycle_in_bf: "\<nexists>c. weight_backward (not_blocked state) (current_flow state) c < 0 \<and> hd c = last c"
    using knowledge no_neg_cycle_in_bf_backward 1 by blast
  have long_enough: "2 \<le> length (awalk_verts t (map cost_flow_network.to_vertex_pair (map cost_flow_network.erev (rev qq))))"
    using knowledge(4) awalk_verts_non_Nil calculation knowledge(17)
          hd_of_vwalk_bet'[OF calculation] last_of_vwalk_bet[OF calculation] 
    by (cases "(awalk_verts t (map cost_flow_network.to_vertex_pair (map cost_flow_network.erev (rev qq))))" rule: list_cases3) auto 
  have ss_dist_le_PInfty:"prod.snd (the (connection_lookup bf ss)) < PInfty"
    unfolding bf_def bellman_ford_backward_def bellman_ford_algo_def bellman_ford_init_algo_def
    using no_neg_cycle_in_bf knowledge(4,17,2,3)   vs_is_V weight_le_PInfty vwalk_bettt  long_enough 
    by (fastforce intro!: bellman_ford.bellamn_ford_path_exists_result_le_PInfty[OF bellman_ford_backward])
   have s_dist_le_qq_weight:"prod.snd (the (connection_lookup bf ss)) \<le>
                          weight_backward (not_blocked state) 
                           (current_flow state) (awalk_verts t (map cost_flow_network.to_vertex_pair (map cost_flow_network.erev (rev qq))))"
    using   knowledge(4,17,2,3)   vs_is_V weight_le_PInfty  is_a_walk 
            bellman_ford.bellman_ford_computes_length_of_optpath[OF bellman_ford no_neg_cycle_in_bf, of t s]
            bellman_ford.opt_vs_path_def[OF bellman_ford, of t s]
            bellman_ford.vsp_pathI[OF bellman_ford long_enough, of t s]
            bellman_ford.weight_le_PInfty_in_vs[OF bellman_ford long_enough, of]
            calculation
    by (auto simp add: vwalk_bet_def bf_def bellman_ford_backward_def bellman_ford_algo_def bellman_ford_init_algo_def)
  hence s_prop:"prod.snd (the (connection_lookup bf s)) < PInfty"
    using knowledge(17) ss_dist_le_PInfty by blast
  have s_in_dom: "s \<in> dom (connection_lookup  bf)"
    using knowledge(2) vs_is_V by (auto simp add: bellman_ford.bellman_ford_init_dom_is[OF bellman_ford]
                       bellman_ford.same_domain_bellman_ford[OF bellman_ford]
                       bf_def bellman_ford_backward_def bellman_ford_algo_def bellman_ford_init_algo_def)
  hence pred_of_s_not_None: "prod.fst (the (connection_lookup bf s)) \<noteq> None"
    using s_prop knowledge(4) bellman_ford.bellman_ford_pred_non_infty_pres[OF bellman_ford, of t "length vs -1"]
    by(auto simp add: bf_def bellman_ford_backward_def  bellman_ford_algo_def bellman_ford_init_algo_def
         bellman_ford.invar_pred_non_infty_def[OF bellman_ford]) 
  have Pbf_def: "Pbf = (bellford.search_rev_path  t bf s)"
    unfolding Pbf_def bf_def bellman_ford_backward_def
    using vs_is_V  pred_of_s_not_None knowledge(3,2)
    apply(subst sym[OF arg_cong[of _ _ rev, OF bellford.function_to_partial_function, simplified]])
    by(fastforce simp add: bellman_ford_backward_def bf_def sym[OF rev_is_rev'] bellman_ford_algo_def bellman_ford_init_algo_def
                 intro!:  bf_bw.search_rev_path_dom_bellman_ford[OF no_neg_cycle_in_bf] )+
  have weight_Pbf_snd: "weight_backward (not_blocked state) 
          (current_flow state) (rev Pbf) = prod.snd (the (connection_lookup bf s))"
    unfolding Pbf_def
    using s_prop   vs_is_V  pred_of_s_not_None knowledge(2,3,4)
    by(fastforce simp add: bellman_ford_backward_def bf_def bellman_ford_algo_def bellman_ford_init_algo_def
                 intro!: bellman_ford.bellman_ford_search_rev_path_weight[OF 
                bellman_ford no_neg_cycle_in_bf, of bf t s])+
  hence weight_le_PInfty: "weight_backward (not_blocked state) (current_flow state) (rev Pbf) < PInfty"
    using s_prop by auto
  have Pbf_opt_path: "bellman_ford.opt_vs_path vs
 (\<lambda>u v. prod.snd (get_edge_and_costs_backward (not_blocked state) (current_flow state) u v)) t s
 (rev (bellford.search_rev_path t bf s))"
   using s_prop  vs_is_V  pred_of_s_not_None knowledge(2,3,4)
   by (auto simp add: bellman_ford_backward_def bf_def bellman_ford_algo_def bellman_ford_init_algo_def
                 intro!: bellman_ford.computation_of_optimum_path[OF bellman_ford no_neg_cycle_in_bf])
    hence length_Pbf:"2 \<le> length Pbf"
    by(auto simp add: bellman_ford.opt_vs_path_def[OF bellman_ford]
      bellman_ford.vs_path_def[OF bellman_ford] Pbf_def)
  have "awalk UNIV (hd Pbf) (map prod.swap (rev (edges_of_vwalk (rev Pbf))))  (last Pbf) \<and>
         weight_backward (not_blocked state) (current_flow state) (rev Pbf) =
         ereal  (foldr (\<lambda>e. (+) (\<cc> e))
        (map (\<lambda>e. prod.fst (get_edge_and_costs_backward (not_blocked state) (current_flow state) (prod.snd e) (prod.fst e)))
               (map prod.swap (rev (edges_of_vwalk (rev Pbf)))) ) 0) \<and>
         (\<forall>e\<in>set (map (\<lambda>e. prod.fst (get_edge_and_costs_backward(not_blocked state) (current_flow state) (prod.snd e)
                         (prod.fst e)))
           (map prod.swap (rev (edges_of_vwalk (rev Pbf)))) ).
    not_blocked state (cost_flow_network.oedge e) \<and> 0 < cost_flow_network.rcap (current_flow state) e)"
    using path_bf_flow_network_path_backward[OF _ length_Pbf[simplified sym[OF length_rev[of Pbf]]]
                    weight_le_PInfty refl, simplified last_rev hd_rev] by simp
    hence Pbf_props: "awalk UNIV (hd Pbf) (edges_of_vwalk  Pbf)  (last Pbf)"
         "weight_backward (not_blocked state) (current_flow state) (rev Pbf) =
         ereal  (foldr (\<lambda>e. (+) (\<cc> e))
        (map (\<lambda>e. prod.fst (get_edge_and_costs_backward (not_blocked state) (current_flow state) (prod.snd e) (prod.fst e)))
               ( edges_of_vwalk  Pbf) ) 0)"
         "\<And> e. e\<in>set (map (\<lambda>e. prod.fst (get_edge_and_costs_backward(not_blocked state) (current_flow state) (prod.snd e)
                         (prod.fst e)))
           ( edges_of_vwalk  Pbf) ) \<Longrightarrow>
    not_blocked state (cost_flow_network.oedge e) \<and> 0 < cost_flow_network.rcap (current_flow state) e"
      using edges_of_vwalk_rev_swap[of "rev Pbf"] 
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
    using Pbf_props(1) same_edges length_Pbf  "1"(1) awalk_fst_last bellman_ford.weight.simps[OF bellman_ford] 
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
  moreover have Rcap_P:"0 < cost_flow_network.Rcap (current_flow state) (set PP)"
    using PP_def Pbf_props(3)
    by(auto simp add: cost_flow_network.Rcap_def)
  ultimately have "augpath (current_flow state) PP"
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
    have "not_blocked state e"
      using map_in_set same_edges "1"(1) PP_def Pbf_props(3) list.set_map by blast
    thus ?case
      using  from_aux_invar'(22)[of state, OF knowledge(5)] 1 by simp
  qed
  have distinct_Pbf: "distinct Pbf"
    using no_neg_cycle_in_bf knowledge(2,3,4) vs_is_V pred_of_s_not_None 
          bellman_ford.search_rev_path_distinct[OF bellman_ford]
    by (fastforce simp add: bellman_ford_backward_def bf_def Pbf_def bellman_ford_algo_def bellman_ford_init_algo_def)
  have distinctP:"distinct PP" 
    using distinct_edges_of_vwalk[OF distinct_Pbf, simplified sym[OF same_edges ]]
          distinct_map by auto
  have qq_in_E:"set (map cost_flow_network.oedge (map cost_flow_network.erev (rev qq))) \<subseteq> \<E>"
    using e_es by auto
  hence qq_rev_in_E:"set ( map cost_flow_network.oedge qq) \<subseteq> \<E>" 
    by(auto simp add: es_sym image_subset_iff cost_flow_network.oedge_and_reversed)
  have not_blocked_qq: "\<And> e . e \<in> set qq \<Longrightarrow> not_blocked state (oedge e)" 
    using  F_is from_aux_invar'(22)[OF knowledge(5)]  qq_prop(4) by fastforce
  have rcap_qq: "\<And> e . e \<in> set qq \<Longrightarrow> cost_flow_network.rcap (current_flow state) e > 0" 
    using  cost_flow_network.augpath_rcap_pos_strict'[OF  qq_prop(1) ] knowledge by simp
  have awalk': "unconstrained_awalk (map cost_flow_network.to_vertex_pair (map cost_flow_network.erev (rev qq)))"
               "unconstrained_awalk (map cost_flow_network.to_vertex_pair qq)"
    using unconstrained_awalk_def  is_a_walk qq_prop(1) cost_flow_network.augpath_def cost_flow_network.prepath_def
    by fastforce+
  have 
bf_weight_leq_res_costs:"weight_backward (not_blocked state) (current_flow state)
 (awalk_verts t (map cost_flow_network.to_vertex_pair (map cost_flow_network.erev (rev qq))))
 \<le> foldr (\<lambda>x. (+) (\<cc> x)) qq 0" 
    using qq_rev_in_E not_blocked_qq rcap_qq awalk'  qq_len 
    by(fastforce intro!: bf_weight_backward_leq_res_costs[simplified cost_flow_network.rev_erev_swap , simplified rev_map, of qq state t])   
  have oedge_of_EE: "flow_network.oedge ` EEE = \<E>" 
    by (meson cost_flow_network.oedge_on_\<EE>)
  have " cost_flow_network.oedge ` set PP \<subseteq> \<E>"
    using from_aux_invar'(1,3)[OF knowledge(5)] oedge_of_p_allowed by blast
  hence P_in_E: "set PP \<subseteq> EEE"
    by (meson image_subset_iff cost_flow_network.o_edge_res subsetI) 
  have "(foldr (\<lambda>e. (+) (\<cc> e)) PP 0) \<le> foldr (\<lambda>x. (+) (\<cc> x)) Q 0"
    using  weight_Pbf_snd s_dist_le_qq_weight Pbf_props(2)[simplified sym[OF PP_def]]
           qq_prop(5) bf_weight_leq_res_costs knowledge(17) 
    by (smt (verit, best) leD le_ereal_less)
  moreover have "(foldr (\<lambda>e. (+) (\<cc> e)) PP 0) = cost_flow_network.\<CC> PP"
    unfolding cost_flow_network.\<CC>_def 
    by(subst distinct_sum, simp add: distinctP, meson add.commute)
  moreover have "(foldr (\<lambda>e. (+) (\<cc> e)) Q 0) = cost_flow_network.\<CC> Q"
    unfolding cost_flow_network.\<CC>_def 
    by(subst distinct_sum, simp add: Q_prop(5), meson add.commute)
  ultimately have P_min: "cost_flow_network.is_min_path f s t PP"
    using Q_min P_in_E  knowledge(12)  distinctP
    by(auto simp add: cost_flow_network.is_min_path_def 
              cost_flow_network.is_s_t_path_def)
  show ?case
    using P_min distinctP Rcap_P oedge_of_p_allowed knowledge(12,18) by simp
next
  case 2
  thus ?case
    by(auto simp add: cost_flow_network.Rcap_def)
qed  

interpretation loopB_Reasoning: loopB_Reasoning snd make_pair create_edge \<u> \<c> \<E> vset_empty vset_delete
       vset_insert vset_inv isin get_from_set
     filter are_all set_invar to_set lookup' t_set sel adjmap_inv' \<b> to_pair \<epsilon> \<E>_impl all_empty N default_conv_to_rdg
     get_source_target_path_b get_source get_target get_source_for_target get_target_for_source fst
     get_source_target_path_a edge_map_update'
  using get_source_target_path_a_ax get_source_target_path_b_ax get_source_axioms get_target_axioms
        get_target_for_source_ax get_source_for_target_ax algo 
  by (auto simp add:  loopB_Reasoning_axioms_def  Adj_Map_Specs2 Set3_axioms
             intro!:  loopB.intro loopB_spec.intro loopB_Reasoning.intro  algo_spec.intro)

lemmas loopB_Reasoning= loopB_Reasoning.loopB_Reasoning_axioms

definition "norma e = (to_pair {prod.fst e, prod.snd e})"

lemma orlins_axioms: "orlins_axioms norma"
  by (simp add: orlins_axioms_def norma_def insert_commute to_pair_axioms)

lemma get_source_aux_aux_coincide:"(\<And> v. v \<in> set xs \<Longrightarrow> b v = b' v) \<Longrightarrow> get_source_aux_aux b g xs = get_source_aux_aux b' g xs"
  by(induction xs) auto

lemma get_target_aux_aux_coincide:"(\<And> v. v \<in> set xs \<Longrightarrow> b v = b' v) \<Longrightarrow> get_target_aux_aux b g xs 
= get_target_aux_aux b' g xs"
  by(induction xs) auto

lemma get_source_aux_nexistence: "(\<not> (\<exists>s\<in> set xs. (1 - \<epsilon>) * \<gamma> < b s)) = (get_source_aux_aux b \<gamma> xs = None)"
  by(induction xs) auto

lemma get_target_aux_nexistence: "(\<not> (\<exists>s\<in> set xs. - (1 - \<epsilon>) * \<gamma> > b s)) = (get_target_aux_aux b \<gamma> xs = None)"
  by(induction xs) auto

abbreviation "abstract  \<equiv> algo_impl.abstract isin  lookup' \<b> default_conv_to_rdg 
                                     flow_lookup  bal_lookup rep_comp_lookup  conv_lookup 
                                      not_blocked_lookup"

abbreviation "implementation_invar \<equiv> algo_impl.implementation_invar make_pair \<E> vset_inv isin set_invar
                                     lookup' adjmap_inv' flow_lookup flow_invar bal_lookup bal_invar
                                     rep_comp_lookup rep_comp_invar conv_lookup conv_invar
                                     not_blocked_lookup not_blocked_invar"

lemma get_source_impl_axioms:
"\<lbrakk>abstract state_impl = state; b = balance state; \<gamma> = current_\<gamma> state;
              \<exists> s \<in> VV. b s > (1 - \<epsilon>) * \<gamma>; implementation_invar state_impl\<rbrakk> \<Longrightarrow> get_source state = the (get_source_impl state_impl )"
"\<lbrakk>abstract state_impl = state; b = balance state; \<gamma> = current_\<gamma> state; implementation_invar state_impl\<rbrakk>
   \<Longrightarrow> \<not> (\<exists> s \<in> VV. b s > (1 - \<epsilon>) * \<gamma>) \<longleftrightarrow> ((get_source_impl state_impl) = None )"
proof(all \<open>goal_cases\<close>)
  assume assms: "abstract state_impl = state" "b = balance state"
                "\<gamma> = current_\<gamma> state " "implementation_invar state_impl"
  show goal1:"get_source state = the (get_source_impl state_impl)" 
    using assms(4) vs_is_V 
    by (auto intro!: arg_cong[of _ _ the] get_source_aux_aux_coincide 
           simp add: sym[OF assms(1)] get_source_impl_def get_source_def algo_impl.abstract_def[OF algo_impl] 
                      algo_impl.abstract_bal_map_def[OF algo_impl] get_source_aux_def 
                     algo_impl.implementation_invar_def[OF algo_impl] dom_def)
  show "(\<not> (\<exists>s\<in>VV. (1 - \<epsilon>) * \<gamma> < b s)) = (get_source_impl state_impl = None)" 
    using assms(4) vs_is_V 
    by (subst get_source_aux_nexistence[of vs, simplified vs_is_V] get_source_aux_aux_coincide |
        auto intro!: arg_cong[of _ _ the] 
           simp add: sym[OF assms(1)] assms(2,3) get_source_impl_def get_source_def 
                     algo_impl.abstract_def[OF algo_impl]
                     algo_impl.abstract_bal_map_def[OF algo_impl] 
                     algo_impl.implementation_invar_def[OF algo_impl] )+
qed

lemma get_target_impl_axioms:
"\<lbrakk>abstract state_impl = state; b = balance state; \<gamma> = current_\<gamma> state;
              \<exists> t \<in> VV. b t < - (1 - \<epsilon>) * \<gamma>; implementation_invar state_impl\<rbrakk> 
\<Longrightarrow> get_target state = the (get_target_impl state_impl )"
"\<lbrakk>abstract state_impl = state; b = balance state; \<gamma> = current_\<gamma> state; implementation_invar state_impl\<rbrakk>
   \<Longrightarrow> \<not> (\<exists> t \<in> VV. b t < - (1 - \<epsilon>) * \<gamma>) \<longleftrightarrow> ((get_target_impl state_impl) = None )"
proof(all \<open>goal_cases\<close>)
  assume assms: "abstract state_impl = state" "b = balance state"
                "\<gamma> = current_\<gamma> state " "implementation_invar state_impl"
  show goal1:"get_target state = the (get_target_impl state_impl)" 
    using assms(4) vs_is_V 
    by (auto intro!: arg_cong[of _ _ the] get_target_aux_aux_coincide 
           simp add: sym[OF assms(1)] get_target_impl_def get_target_def algo_impl.abstract_def[OF algo_impl] 
                     algo_impl.abstract_bal_map_def[OF algo_impl] get_target_aux_def 
                     algo_impl.implementation_invar_def[OF algo_impl] dom_def)
   
  show "(\<not> (\<exists>t\<in>VV. - (1 - \<epsilon>) * \<gamma> > b t)) = (get_target_impl state_impl = None)" 
    using assms(4) vs_is_V 
    by (subst get_target_aux_nexistence[of vs, simplified vs_is_V] get_target_aux_aux_coincide |
        auto intro!: arg_cong[of _ _ the]
           simp add: sym[OF assms(1)] assms(2,3) get_target_impl_def get_target_def 
                     algo_impl.abstract_def[OF algo_impl] 
                     algo_impl.abstract_bal_map_def[OF algo_impl] 
                     algo_impl.implementation_invar_def[OF algo_impl] )+
qed

lemmas get_source_target_path_a_condE = loopB.get_source_target_path_a_condE
lemmas get_source_target_path_b_condE = loopB.get_source_target_path_b_condE

lemma get_target_for_source_aux_aux_cong:
"(\<And> x. x \<in> set xs \<Longrightarrow> connection_lookup connections x = connection_lookup connections' x) \<Longrightarrow>
(\<And> x. x \<in> set xs \<Longrightarrow> b x = b' x) \<Longrightarrow>
g = g' \<Longrightarrow>
 get_target_for_source_aux_aux connections b g xs = get_target_for_source_aux_aux connections' b' g' xs"
  by(induction xs) auto

lemma get_source_for_target_aux_aux_cong:
"(\<And> x. x \<in> set xs \<Longrightarrow> connection_lookup connections x = connection_lookup connections' x) \<Longrightarrow>
(\<And> x. x \<in> set xs \<Longrightarrow> b x = b' x) \<Longrightarrow>
g = g' \<Longrightarrow>
 get_source_for_target_aux_aux connections b g xs = get_source_for_target_aux_aux connections' b' g' xs"
  by(induction xs) auto

lemma not_blocked_coincide:"nb = algo_impl.abstract_not_blocked_map not_blocked_lookup 
nb_impl\<Longrightarrow>
    TB (not_blocked_lookup nb_impl e) = nb e"
  by(auto simp add: algo_impl.abstract_def[OF algo_impl] algo_impl.abstract_not_blocked_map_def[OF algo_impl])

lemma flow_coincide:"e \<in> \<E> \<Longrightarrow> state = abstract state_impl 
\<Longrightarrow> implementation_invar state_impl \<Longrightarrow>
    (flow_lookup (current_flow_impl state_impl) e) =
     Some ((current_flow state) e)"
  by(auto simp add: algo_impl.abstract_def[OF algo_impl]
            algo_impl.implementation_invar_def[OF algo_impl] 
            algo_impl_spec.abstract_flow_map_def[OF algo_impl_spec]  dom_def)

lemma cheapest_forward_cong: " (\<And> e. e\<in> set ingoing_edges \<Longrightarrow> nb e = nb' e) \<Longrightarrow>
                               (\<And> e. e\<in> set ingoing_edges \<Longrightarrow> f e = f' e) \<Longrightarrow>
                                find_cheapest_forward f nb ingoing_edges e c
                              = find_cheapest_forward f' nb' ingoing_edges e c"
  unfolding find_cheapest_forward_def
  by(induction ingoing_edges) auto

lemma cheapest_backward_cong: " (\<And> e. e\<in> set ingoing_edges \<Longrightarrow> nb e = nb' e) \<Longrightarrow>
                               (\<And> e. e\<in> set ingoing_edges \<Longrightarrow> f e = f' e) \<Longrightarrow>
                                find_cheapest_backward f nb ingoing_edges e c
                              = find_cheapest_backward f' nb' ingoing_edges e c"
  unfolding find_cheapest_backward_def
  by(induction ingoing_edges) auto

lemma same_costs_forward: 
  assumes "(\<And> e. e \<in> \<E> \<Longrightarrow> nb e = nb' e)"
          "\<And> e. e \<in> \<E> \<Longrightarrow> f e = f' e"
        shows "get_edge_and_costs_forward nb f u v = get_edge_and_costs_forward nb' f' u v"
proof-
  define ingoing_edges where "ingoing_edges =
            (case realising_edges_lookup realising_edges
                  (u, v) of
            None \<Rightarrow> [] | Some list \<Rightarrow> list)"
  define outgoing_edges where "outgoing_edges =
            (case realising_edges_lookup realising_edges
                  (v, u) of
            None \<Rightarrow> [] | Some list \<Rightarrow> list)"
  have nb_agree: "e \<in> set ingoing_edges \<Longrightarrow> nb e = nb' e"  for e
    by (auto simp add: ingoing_edges_def \<E>_def \<E>_impl(1) \<E>_list_def assms(1) realising_edges_def realising_edges_general_result to_list(1))
  have f_agree: "e \<in> set ingoing_edges \<Longrightarrow> f e = f' e" for e
    by (auto simp add: ingoing_edges_def \<E>_def \<E>_impl(1) \<E>_list_def assms(2) realising_edges_def realising_edges_general_result to_list(1))
  have nb_agree': "e \<in> set outgoing_edges \<Longrightarrow> nb e = nb' e"  for e
    by (auto simp add: outgoing_edges_def \<E>_def \<E>_impl(1) \<E>_list_def assms(1) realising_edges_def realising_edges_general_result to_list(1))
  have f_agree': "e \<in> set outgoing_edges \<Longrightarrow> f e = f' e" for e
    by (auto simp add: outgoing_edges_def \<E>_def \<E>_impl(1) \<E>_list_def assms(2) realising_edges_def realising_edges_general_result to_list(1)) 
  have forward_cong:"find_cheapest_forward f nb ingoing_edges
             (create_edge u v) PInfty = find_cheapest_forward f' nb' ingoing_edges
             (create_edge u v) PInfty"
    using nb_agree f_agree
    by(auto intro: cheapest_forward_cong)
  moreover have backward_cong:"find_cheapest_backward f nb outgoing_edges
             (create_edge v u) PInfty = find_cheapest_backward f' nb' outgoing_edges
             (create_edge v u) PInfty"
    using nb_agree' f_agree'
    by(auto intro: cheapest_backward_cong)
  show ?thesis
    unfolding  get_edge_and_costs_forward_def Let_def
    using forward_cong ingoing_edges_def backward_cong outgoing_edges_def
    by simp
qed

lemma same_costs_backward: 
  assumes "(\<And> e. e \<in> \<E> \<Longrightarrow> nb e = nb' e)"
          "\<And> e. e \<in> \<E> \<Longrightarrow> f e = f' e"
        shows "get_edge_and_costs_backward nb f v u = get_edge_and_costs_backward nb' f' v u"
proof-
  define ingoing_edges where "ingoing_edges =
            (case realising_edges_lookup realising_edges
                  (u, v) of
            None \<Rightarrow> [] | Some list \<Rightarrow> list)"
  define outgoing_edges where "outgoing_edges =
            (case realising_edges_lookup realising_edges
                  (v, u) of
            None \<Rightarrow> [] | Some list \<Rightarrow> list)"
  have nb_agree: "e \<in> set ingoing_edges \<Longrightarrow> nb e = nb' e"  for e
    by (auto simp add: ingoing_edges_def \<E>_def \<E>_impl(1) \<E>_list_def assms(1) realising_edges_def realising_edges_general_result to_list(1))
  have f_agree: "e \<in> set ingoing_edges \<Longrightarrow> f e = f' e" for e
    by (auto simp add: ingoing_edges_def \<E>_def \<E>_impl(1) \<E>_list_def assms(2) realising_edges_def realising_edges_general_result to_list(1))
  have nb_agree': "e \<in> set outgoing_edges \<Longrightarrow> nb e = nb' e"  for e
    by (auto simp add: outgoing_edges_def \<E>_def \<E>_impl(1) \<E>_list_def assms(1) realising_edges_def realising_edges_general_result to_list(1))
  have f_agree': "e \<in> set outgoing_edges \<Longrightarrow> f e = f' e" for e
    by (auto simp add: outgoing_edges_def \<E>_def \<E>_impl(1) \<E>_list_def assms(2) realising_edges_def realising_edges_general_result to_list(1)) 
  have forward_cong:"find_cheapest_forward f nb ingoing_edges
             (create_edge u v) PInfty = find_cheapest_forward f' nb' ingoing_edges
             (create_edge u v) PInfty"
    using nb_agree f_agree
    by(auto intro: cheapest_forward_cong)
  moreover have backward_cong:"find_cheapest_backward f nb outgoing_edges
             (create_edge v u) PInfty = find_cheapest_backward f' nb' outgoing_edges
             (create_edge v u) PInfty"
    using nb_agree' f_agree'
    by(auto intro: cheapest_backward_cong)
  show ?thesis
    unfolding  get_edge_and_costs_backward_def Let_def
    using forward_cong ingoing_edges_def backward_cong outgoing_edges_def
    by simp
qed
  
lemma  abstract_impl_correspond_a:
  assumes "get_source_target_path_a_cond state s t P b \<gamma> f"
    "get_source_target_path_a_impl state_impl s = Some (t_impl, P_impl)" " invar_isOptflow state"
    "implementation_invar state_impl" "state = abstract state_impl"
    shows "P_impl= P \<and> t_impl = t"
proof(rule get_source_target_path_a_condE[OF assms(1)], goal_cases)
  case 1
  note knowledge= this

  define bf where "bf = bellman_ford_forward (not_blocked state) (current_flow state) s"
  define tt where "tt = get_target_for_source_aux bf (balance state) (current_\<gamma> state) vs"
  define Pbf where "Pbf = search_rev_path_exec s bf tt Nil"
  define PP where " PP = map (\<lambda>e. prod.fst (get_edge_and_costs_forward (not_blocked state) 
                               (current_flow state) (prod.fst e) (prod.snd e)))
                         (edges_of_vwalk Pbf)"
  have PP_is_P_tt_is_t:"PP = P"  "tt = t"
   using knowledge(1,2,5,6,10-12) assms(3)
   by(auto intro: loopB_call1_condE[OF "1"(13)] 
        simp add: PP_def Pbf_def tt_def bf_def  get_target_for_source_def 
                  get_source_target_path_a_def get_target_for_source_aux_def )
  define bf_impl where "bf_impl = bellman_ford_forward (\<lambda>e. TB (not_blocked_lookup (not_blocked_impl state_impl) e))
           (\<lambda>e. the (flow_lookup (current_flow_impl state_impl) e)) s"
  define tt_impl where " tt_impl = get_target_for_source_aux bf_impl 
                                          (\<lambda>v. the (bal_lookup (balance_impl state_impl) v)) 
                                               (current_\<gamma>_impl state_impl)
                                   vs"
  define Pbf_impl where  "Pbf_impl = search_rev_path_exec s bf_impl tt_impl Nil"
  define PP_impl where "PP_impl = map (\<lambda>e. prod.fst (get_edge_and_costs_forward 
                         (\<lambda>e. TB (not_blocked_lookup (not_blocked_impl state_impl) e))
                         (\<lambda>e. the (flow_lookup (current_flow_impl state_impl) e)) (prod.fst e) (prod.snd e)))
                         (edges_of_vwalk Pbf_impl)"
  have PP_is_P_tt_is_t_impl:"PP_impl = P_impl"  "tt_impl = t_impl"
    using assms(2)
    by (auto intro: option_caseE[of "\<lambda> x. x = Some (t_impl, P_impl)" ] 
             simp add: PP_impl_def Pbf_impl_def tt_impl_def bf_impl_def
                       get_source_target_path_a_impl_def get_target_for_source_aux_def)
  have bal_coincide: "v \<in> set vs \<Longrightarrow> bal_lookup (balance_impl state_impl) v = Some (b v)" for v
    using algo_impl.implementation_invar_partial_props(6)[OF algo_impl assms(4)]
          vs_is_V  algo_impl.abstractE'(2)[OF algo_impl, of \<b>]
    by(auto simp add: algo_impl.abstract_bal_map_def[OF algo_impl]  dom_def  assms(5)knowledge(8))
  have flow_coincide: "e \<in> \<E> \<Longrightarrow> the (flow_lookup (current_flow_impl state_impl) e) = f e" for e
    using algo_impl.implementation_invar_partial_props(4)[OF algo_impl assms(4)]
          vs_is_V  algo_impl.abstractE'(1)[OF algo_impl, of \<b>]
          algo_impl_spec.abstract_flow_map_def[OF algo_impl_spec]  dom_def  assms(5)knowledge(12)
    by auto
  have not_blocked_in_E: "not_blocked state e \<Longrightarrow> e \<in> \<E>" for e
    using algo_impl.implementation_invar_partial_props(13)[OF algo_impl assms(4)]
          vs_is_V  algo_impl.abstractE'(11)[OF algo_impl, of \<b>] 
    by( simp add: dom_def  assms(5) algo_impl.abstract_not_blocked_map_def[OF algo_impl] ,
             insert algo_impl.implementation_invar_partial_props(13)[OF algo_impl assms(4)], force)
  have not_blocked_coincide: "TB (not_blocked_lookup (not_blocked_impl state_impl) e)
                             = (not_blocked state e)" for e
    using algo_impl.implementation_invar_partial_props(13)[OF algo_impl assms(4)]
         algo_impl.abstractE'(11)[OF algo_impl, of \<b>]
     by(auto simp add: algo_impl.abstract_not_blocked_map_def[OF algo_impl]  dom_def  assms(5)knowledge(12))    
  have same_costs:"get_edge_and_costs_forward (\<lambda>e. TB (not_blocked_lookup (not_blocked_impl state_impl) e))
                   (\<lambda>e. the (flow_lookup (current_flow_impl state_impl) e))
        = get_edge_and_costs_forward (not_blocked state) (current_flow state)"
    using local.not_blocked_coincide knowledge(12) local.flow_coincide 
    by (auto intro!: ext intro: same_costs_forward)
  have same_bellman_ford:"bellman_ford_forward (\<lambda>e. TB (not_blocked_lookup (not_blocked_impl state_impl) e))
     (\<lambda>e. the (flow_lookup (current_flow_impl state_impl) e)) =
    bellman_ford_forward (not_blocked state) (current_flow state)"
    using same_costs  
    by (auto simp add: bellman_ford_forward_def bellman_ford_init_algo_def bellman_ford_algo_def)
  have ts_same: "tt_impl = tt"
    using same_bellman_ford bal_coincide     
    by(auto intro!: cong[of the, OF refl] get_target_for_source_aux_aux_cong 
         simp add:  assms(5) algo_impl.abstract_def[OF algo_impl] Let_def
                    algo_impl.abstract_bal_map_def[OF algo_impl] tt_impl_def tt_def bf_impl_def
                    bf_def get_target_for_source_aux_def)
  moreover have " PP_impl = PP"
    by(simp add: PP_impl_def PP_def Pbf_impl_def Pbf_def ts_same bf_impl_def bf_def same_bellman_ford
                 same_costs )   
  ultimately show ?case 
    using PP_is_P_tt_is_t PP_is_P_tt_is_t_impl 
    by simp
qed

lemma  abstract_impl_correspond_b:
  assumes "get_source_target_path_b_cond state s t P b \<gamma> f"
    "get_source_target_path_b_impl state_impl t = Some (s_impl, P_impl)" " invar_isOptflow state"
    "implementation_invar state_impl" "state = abstract state_impl"
    shows "P_impl= P \<and> s_impl = s"
proof(rule get_source_target_path_b_condE[OF assms(1)], goal_cases)
  case 1
  note knowledge= this

  define bf where "bf = bellman_ford_backward (not_blocked state) (current_flow state) t"
  define ss where "ss = get_source_for_target_aux bf (balance state) (current_\<gamma> state) vs"
  define Pbf where "Pbf = rev' (search_rev_path_exec t bf ss Nil)"
  define PP where " PP = map (\<lambda>e. prod.fst (get_edge_and_costs_backward (not_blocked state)
                                    (current_flow state) (prod.snd e) (prod.fst e)))
                         (edges_of_vwalk Pbf)"
  have PP_is_P_ss_is_s:"PP = P"  "ss = s"
   using knowledge(1,3,5,6,10-12) assms(3)
   by(auto intro: loopB_call2_condE[OF "1"(13)] 
        simp add: PP_def Pbf_def ss_def bf_def  get_source_for_target_def 
                  get_source_target_path_b_def get_source_for_target_aux_def )
  define bf_impl where "bf_impl = bellman_ford_backward (\<lambda>e. TB (not_blocked_lookup (not_blocked_impl state_impl) e))
           (\<lambda>e. the (flow_lookup (current_flow_impl state_impl) e)) t"
  define ss_impl where " ss_impl = get_source_for_target_aux bf_impl 
                                          (\<lambda>v. the (bal_lookup (balance_impl state_impl) v)) 
                                               (current_\<gamma>_impl state_impl)
                                   vs"
  define Pbf_impl where  "Pbf_impl = rev' (search_rev_path_exec t bf_impl ss_impl Nil)"
  define PP_impl where "PP_impl = map (\<lambda>e. prod.fst (get_edge_and_costs_backward
                           (\<lambda>e. TB (not_blocked_lookup (not_blocked_impl state_impl) e))
                         (\<lambda>e. the (flow_lookup (current_flow_impl state_impl) e)) (prod.snd e) (prod.fst e)))
                         (edges_of_vwalk Pbf_impl)"
  have PP_is_P_ss_is_s_impl:"PP_impl = P_impl"  "ss_impl = s_impl"
    using assms(2)
    by (auto intro: option_caseE[of "\<lambda> x. x = Some (s_impl, P_impl)" ] 
             simp add: PP_impl_def Pbf_impl_def ss_impl_def bf_impl_def
                       get_source_target_path_b_impl_def get_source_for_target_aux_def)
  have bal_coincide: "v \<in> set vs \<Longrightarrow> bal_lookup (balance_impl state_impl) v = Some (b v)" for v
    using algo_impl.implementation_invar_partial_props(6)[OF algo_impl assms(4)]
          vs_is_V  algo_impl.abstractE'(2)[OF algo_impl, of \<b>]
    by(auto simp add: algo_impl.abstract_bal_map_def[OF algo_impl]  dom_def  assms(5)knowledge(8))
  have flow_coincide: "e \<in> \<E> \<Longrightarrow> the (flow_lookup (current_flow_impl state_impl) e) = f e" for e
    using vs_is_V  algo_impl.abstractE'(1)[OF algo_impl, of \<b>]
    by(auto simp add: algo_impl_spec.abstract_flow_map_def[OF algo_impl_spec]  dom_def assms(5)knowledge(12)
                       algo_impl.implementation_invar_partial_props(4)[OF algo_impl assms(4)])
    have not_blocked_in_E: "not_blocked state e \<Longrightarrow> e \<in> \<E>" for e
    using algo_impl.implementation_invar_partial_props(13)[OF algo_impl assms(4)]
          vs_is_V  algo_impl.abstractE'(11)[OF algo_impl, of \<b>]
    by(auto simp add: algo_impl.abstract_not_blocked_map_def[OF algo_impl]  dom_def  assms(5))
  have not_blocked_coincide: "TB (not_blocked_lookup (not_blocked_impl state_impl) e)
                             = (not_blocked state e)" for e
    using algo_impl.implementation_invar_partial_props(13)[OF algo_impl assms(4)]
         algo_impl.abstractE'(11)[OF algo_impl, of \<b>]
     by(auto simp add: algo_impl.abstract_not_blocked_map_def[OF algo_impl]  dom_def  assms(5)knowledge(12))    
  have same_costs:"get_edge_and_costs_backward (\<lambda>e. TB (not_blocked_lookup (not_blocked_impl state_impl) e))
                   (\<lambda>e. the (flow_lookup (current_flow_impl state_impl) e))
        = get_edge_and_costs_backward (not_blocked state) (current_flow state)"
    using local.not_blocked_coincide knowledge(12) local.flow_coincide 
    by (auto intro!: ext intro: same_costs_backward)
  have same_bellman_ford:"bellman_ford_backward (\<lambda>e. TB (not_blocked_lookup (not_blocked_impl state_impl) e))
     (\<lambda>e. the (flow_lookup (current_flow_impl state_impl) e)) =
    bellman_ford_backward (not_blocked state) (current_flow state)"
    using same_costs  
    by (auto simp add: bellman_ford_backward_def bellman_ford_algo_def bellman_ford_init_algo_def)   
  have ss_same: "ss_impl = ss"
    using same_bellman_ford bal_coincide   
    by(auto intro!: cong[of the, OF refl] get_source_for_target_aux_aux_cong 
         simp add:  assms(5) algo_impl.abstract_def[OF algo_impl]
                    algo_impl.abstract_bal_map_def[OF algo_impl] ss_impl_def ss_def bf_impl_def
                    bf_def get_source_for_target_aux_def )
  moreover have " PP_impl = PP"
    by(simp add: PP_impl_def PP_def Pbf_impl_def Pbf_def ss_same bf_impl_def bf_def same_bellman_ford
                 same_costs )   
  ultimately show ?case 
    using PP_is_P_ss_is_s PP_is_P_ss_is_s_impl 
    by simp
qed

lemma impl_a_None_aux:
" \<lbrakk>b = balance state; \<gamma> = current_\<gamma> state; f = current_flow state;
            s \<in> VV; aux_invar state; (\<forall> e \<in> \<F> state . f e > 0);
            loopB_call1_cond state \<or> loopB_fail1_cond state; s = get_source state;
           state = abstract state_impl; implementation_invar state_impl;
           invar_gamma state\<rbrakk>
    \<Longrightarrow> \<not> (\<exists> t \<in> VV. b t < - \<epsilon> * \<gamma> \<and> resreach f s t) \<longleftrightarrow> get_source_target_path_a_impl state_impl s = None"
proof(goal_cases)
  case 1
  note knowledge = this
  define bf_impl where "bf_impl = bellman_ford_forward (\<lambda>e. TB (not_blocked_lookup (not_blocked_impl state_impl) e))
           (\<lambda>e. the (flow_lookup (current_flow_impl state_impl) e)) s"
  define tt_impl where " tt_impl = get_target_for_source_aux_aux bf_impl 
                                          (\<lambda>v. the (bal_lookup (balance_impl state_impl) v)) 
                                               (current_\<gamma>_impl state_impl)
                                   vs"
  define bf where "bf = bellman_ford_forward (not_blocked state) (current_flow state) s"
  have bal_coincide: "v \<in> set vs \<Longrightarrow> bal_lookup (balance_impl state_impl) v = Some (b v)" for v
    using algo_impl.implementation_invar_partial_props(6)[OF algo_impl knowledge(10)]
          vs_is_V  algo_impl.abstractE'(2)[OF algo_impl, of \<b>]
    by(auto simp add: algo_impl.abstract_bal_map_def[OF algo_impl]  dom_def knowledge(1,10,9))
  have flow_coincide: "e \<in> \<E> \<Longrightarrow> the (flow_lookup (current_flow_impl state_impl) e) = f e" for e
    using vs_is_V  algo_impl.abstractE'(1)[OF algo_impl, of \<b>]
    by(auto simp add: algo_impl_spec.abstract_flow_map_def[OF algo_impl_spec]  dom_def knowledge(3,10,9)
                      algo_impl.implementation_invar_partial_props(4)[OF algo_impl knowledge(10)])
  have not_blocked_in_E: "not_blocked state e \<Longrightarrow> e \<in> \<E>" for e
        using algo_impl.implementation_invar_partial_props(13)[OF algo_impl knowledge(10)]
          vs_is_V  algo_impl.abstractE'(11)[OF algo_impl, of \<b>] dom_def knowledge(10,9)
        by(force simp add: algo_impl.abstract_not_blocked_map_def[OF algo_impl] split: if_split
                    intro: option.exhaust[of "not_blocked_lookup (not_blocked_impl state_impl) e"])
    have not_blocked_coincide: "TB (not_blocked_lookup (not_blocked_impl state_impl) e)
                             = (not_blocked state e)" for e
    using algo_impl.implementation_invar_partial_props(13)[OF algo_impl knowledge(10)]
         algo_impl.abstractE'(11)[OF algo_impl, of \<b>]
     by(auto simp add: algo_impl.abstract_not_blocked_map_def[OF algo_impl]  dom_def  knowledge(10,9))    
  have same_costs:"get_edge_and_costs_forward (\<lambda>e. TB (not_blocked_lookup (not_blocked_impl state_impl) e))
                   (\<lambda>e. the (flow_lookup (current_flow_impl state_impl) e))
        = get_edge_and_costs_forward (not_blocked state) (current_flow state)"
    using local.not_blocked_coincide knowledge(3) local.flow_coincide 
    by (auto intro!: ext intro: same_costs_forward)
  have same_bellman_ford:"bf_impl = bf"
    using same_costs  
    by (auto simp add: bellman_ford_forward_def bf_def bf_impl_def bellman_ford_init_algo_def bellman_ford_algo_def)   
  have gamma_coincide: "current_\<gamma>_impl state_impl = current_\<gamma> state"
    using knowledge(9) 
    by(simp add: algo_impl.abstract_def[OF algo_impl])
  have bellman_ford:"bellman_ford connection_empty connection_lookup connection_invar connection_delete
     es vs (\<lambda> u v. prod.snd (get_edge_and_costs_forward (not_blocked state) (current_flow state) u v)) connection_update"
    by (simp add: bellman_ford)
  have s_prop: "(1 - \<epsilon>) * \<gamma> < b s" "s \<in> VV" 
     by(rule disjE[OF knowledge(7)], insert get_source_aux[of vs \<gamma> b, OF _  refl] vs_is_V;
     auto elim!: disjE[OF knowledge(7)] loopB_call1_condE loopB_fail1_condE 
        simp add:  get_source_def knowledge)+
   hence bs0:"b s > 0"   
     using knowledge(11,2,1) \<epsilon>_axiom(2,4) algo.invar_gamma_def 
     by (smt (verit, ccfv_SIG) divide_less_eq_1_pos mult_nonneg_nonneg)
  have "\<not> (\<exists> t \<in> VV. b t < - \<epsilon> * \<gamma> \<and> resreach f s t) \<longleftrightarrow> 
            (tt_impl = None)"
  proof(rule,  all \<open>rule ccontr\<close>, goal_cases)
    case (1 )
    then obtain t where "tt_impl = Some t" by auto
    note 1 = this 1
    hence "(\<exists>x\<in>set vs.
    the (bal_lookup (balance_impl state_impl) x) < - \<epsilon> * current_\<gamma>_impl state_impl \<and>
    prod.snd (the (connection_lookup bf_impl x)) < PInfty)"
      using  get_target_for_source_aux_aux[of vs " (\<lambda>v. the (bal_lookup (balance_impl state_impl) v))"
                                            "current_\<gamma>_impl state_impl" bf_impl, simplified sym[OF tt_impl_def]]
      by simp
    hence "(\<exists>x\<in>set vs. b x < - \<epsilon> * current_\<gamma> state \<and> prod.snd (the (connection_lookup bf x)) < PInfty)"
      by(simp add: bal_coincide gamma_coincide same_bellman_ford )
    then obtain x where x_prop:"x \<in> set vs" "b x < - \<epsilon> * current_\<gamma> state" "prod.snd (the (connection_lookup bf x)) < PInfty"
      by auto
    hence bx0:"b x < 0"
      using knowledge(11,2,1) \<epsilon>_axiom algo.invar_gamma_def
      by (smt (verit)  mult_minus_left mult_nonneg_nonneg)
    hence x_not_s:"x \<noteq> s"
      using bs0 by auto
    hence x_in_dom:"x\<in>dom (connection_lookup bf)" "prod.fst (the (connection_lookup bf x)) \<noteq> None"
      using x_prop bellman_ford.same_domain_bellman_ford[OF bellman_ford, of "length vs -1" s]
            bellman_ford.bellman_ford_init_dom_is[OF bellman_ford, of s] 
            bellman_ford.bellman_ford_pred_non_infty_pres[OF bellman_ford, of s "length vs - 1"]
      by(auto simp add: bf_def bellman_ford_forward_def bellman_ford.invar_pred_non_infty_def[OF bellman_ford]
                        bellman_ford_init_algo_def bellman_ford_algo_def)
    obtain p where p_prop:"weight (not_blocked state) (current_flow state) (p @ [x]) = 
                    prod.snd (the (connection_lookup bf x))"
           "last p = the (prod.fst (the (connection_lookup bf x)))"
           "hd p = s" "1 \<le> length p" "set (p @ [x]) \<subseteq> Set.insert s (set vs)"
      using  bellman_ford.bellman_ford_invar_pred_path_pres[OF bellman_ford, of s "length vs -1"]
             x_in_dom 
      by (auto simp add: bellman_ford.invar_pred_path_def[OF bellman_ford] bf_def 
                         bellman_ford_forward_def bellman_ford_init_algo_def bellman_ford_algo_def)
    hence pw_le_PInfty: "weight (not_blocked state) (current_flow state) (p @ [x]) < PInfty"
      using x_prop by auto
    define pp where "pp = (map (\<lambda>e. prod.fst (get_edge_and_costs_forward (not_blocked state) (current_flow state)
                  (prod.fst e) (prod.snd e)))
             (edges_of_vwalk (p @ [x])))"
    have transformed:" awalk UNIV (hd (p @ [x])) (edges_of_vwalk (p @ [x])) (last (p @ [x]))"
         "(\<And>e. e\<in>set pp \<Longrightarrow> not_blocked state (cost_flow_network.oedge e) \<and> 0 < cost_flow_network.rcap (current_flow state) e)"
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
    moreover have "0 < cost_flow_network.Rcap f (set pp)"
      using transformed(2) knowledge(3)
      by(auto intro: linorder_class.Min_gr_iff simp add: cost_flow_network.Rcap_def)
    ultimately have "augpath f pp"
      by(simp add: cost_flow_network.augpath_def)
    moreover have " e \<in> set pp \<Longrightarrow> e \<in> EEE" for e
      using transformed(2)[of e] not_blocked_in_E cost_flow_network.o_edge_res by blast
    ultimately have "resreach f s x"
      using cost_flow_network.augpath_imp_resreach[OF , of f pp] path_hd p_prop(3,4) path_last
      by(cases p) auto
    thus False
      using 1 x_prop(1,2) knowledge(2) vs_is_V
      by simp
  next
    case 2
    then obtain t where "t\<in>local.multigraph.\<V>"  "b t < - local.\<epsilon> * \<gamma> " "resreach f s t"
      by auto
    note 2 = this 2
    hence "b t < 0"
      using knowledge(11,2,1) \<epsilon>_axiom algo.invar_gamma_def
      by (smt (verit)  mult_minus_left mult_nonneg_nonneg)
    hence t_not_s:"t \<noteq> s"
      using bs0 by auto
    obtain q where q_props:"augpath f q" "fstv (hd q) = s" 
                    "sndv (last q) = t" "set q \<subseteq> EEE"
      using  cost_flow_network.resreach_imp_augpath[OF  2(3)] by auto
    then obtain qq where qq_props:"augpath f qq"
       "fstv (hd qq) = s"
       "sndv (last qq) = t"
       "set qq \<subseteq> {e |e. e \<in> EEE \<and> cost_flow_network.oedge e \<in> to_set (actives state)}
            \<union> to_rdgs to_pair (conv_to_rdg state) (\<FF> state)"
       "qq \<noteq> []"
    using algo.simulate_inactives[OF q_props(1-4) 1(5) refl 1(3) refl refl refl refl refl refl _  1(6)]
        t_not_s by auto
    have e_in_qq_not_blocked: "e \<in> set qq \<Longrightarrow> not_blocked state (cost_flow_network.oedge e)" for e   
      using qq_props(4) 
      by(induction e rule: cost_flow_network.oedge.induct)
        (force simp add: spec[OF from_aux_invar'(22)[OF 1(5)]] from_aux_invar'(21)[OF 1(5)])+
    have e_in_qq_rcap: "e \<in> set qq \<Longrightarrow> 0 < cost_flow_network.rcap f e" for e
      using qq_props(1)  linorder_class.Min_gr_iff 
      by (auto simp add: augpath_def cost_flow_network.Rcap_def)
    obtain Q where Q_prop:"fstv (hd Q) = s" "sndv (last Q) = t" 
                   "distinct Q" "set Q \<subseteq> set qq" "augpath f Q"
      using cost_flow_network.there_is_s_t_path[OF , OF qq_props(1-3) refl] by auto
    have e_in_qq_E: "e \<in> set Q \<Longrightarrow> oedge e \<in> \<E>" for e 
      using Q_prop(4) e_in_qq_not_blocked not_blocked_in_E by blast
    have costsQ: "e \<in> set Q \<Longrightarrow>
         prod.snd (get_edge_and_costs_forward (not_blocked state) f (fstv e) (sndv e)) < PInfty" for e
     apply(rule order.strict_trans1)
     apply(rule conjunct1[OF get_edge_and_costs_forward_makes_cheaper[OF refl _ _ , of e "not_blocked state" f]])
      using  e_in_qq_E  e_in_qq_not_blocked  e_in_qq_rcap Q_prop(4) 
      by(auto intro: prod.collapse)
    have awalk:"awalk UNIV s (map cost_flow_network.to_vertex_pair Q) t"
      using Q_prop(1) Q_prop(2) Q_prop(5) cost_flow_network.augpath_def cost_flow_network.prepath_def by blast
    have "weight (not_blocked state) f (awalk_verts s (map cost_flow_network.to_vertex_pair Q)) < PInfty"
      using costsQ  awalk Q_prop(1) bellman_ford  knowledge(3) 
      by (intro path_flow_network_path_bf[of Q "not_blocked state" f s]) auto
    moreover have " (hd (awalk_verts s (map cost_flow_network.to_vertex_pair Q))) = s"
           using awalk by auto
    moreover have "last (awalk_verts s (map cost_flow_network.to_vertex_pair Q)) = t" 
        using awalk by force
   ultimately have " bellman_ford.OPT vs (\<lambda>u v. prod.snd (get_edge_and_costs_forward (not_blocked state) (current_flow state) u v))
           (length vs - 1) s t < PInfty" 
        using t_not_s 1(3)
        by(intro bellman_ford.weight_le_PInfty_OPTle_PInfty[OF bellman_ford _ _ refl,
                    of _ "tl (butlast (awalk_verts s (map cost_flow_network.to_vertex_pair Q)))"],
              cases "awalk_verts s (map cost_flow_network.to_vertex_pair Q)" rule: list_cases_both_sides) auto
    moreover have "prod.snd (the (connection_lookup bf t)) \<le> 
            bellman_ford.OPT vs (\<lambda>u v. prod.snd (get_edge_and_costs_forward (not_blocked state) (current_flow state) u v))
           (length vs - 1) s t"
      using bellman_ford.bellman_ford_shortest[OF bellman_ford, of s "length vs -1" t] vs_is_V
            knowledge(4)
      by(auto simp add: bf_def bellman_ford_forward_def bellman_ford_init_algo_def bellman_ford_algo_def)
    ultimately have "prod.snd (the (connection_lookup bf t)) < PInfty" by auto
    hence "t \<in> set vs" "b t < - \<epsilon> * current_\<gamma> state" "prod.snd (the (connection_lookup bf t)) < PInfty"
      using "2" knowledge(2) vs_is_V by auto
    hence "(\<exists>x\<in>set vs.
    the (bal_lookup (balance_impl state_impl) x) < - \<epsilon> * current_\<gamma>_impl state_impl \<and>
    prod.snd (the (connection_lookup bf_impl x)) < PInfty)"
      by(auto simp add: bal_coincide gamma_coincide same_bellman_ford )
    hence "(tt_impl \<noteq> None)"
      using get_target_for_source_aux_aux[of vs " (\<lambda>v. the (bal_lookup (balance_impl state_impl) v))"
                                            "current_\<gamma>_impl state_impl" bf_impl, simplified sym[OF tt_impl_def]]
      by simp
    thus False
      using 2 by simp
  qed
  thus ?thesis 
    by(auto simp add: tt_impl_def bf_impl_def get_source_target_path_a_impl_def Let_def)
qed

lemma  impl_a_None:
       "b = balance state \<Longrightarrow>
       \<gamma> = current_\<gamma> state \<Longrightarrow>
       f = current_flow state \<Longrightarrow>
       abstract state_impl = state \<Longrightarrow>
       s \<in> VV \<Longrightarrow>
       aux_invar state \<Longrightarrow>
       (\<forall>e\<in>\<F> state. 0 < f e) \<Longrightarrow>
       loopB_call1_cond state \<or> loopB_fail1_cond state \<Longrightarrow>
       s = get_source state \<Longrightarrow>
       implementation_invar state_impl \<Longrightarrow>
       algo.invar_gamma state \<Longrightarrow>
       (\<not> (\<exists>t\<in>VV. b t < - \<epsilon> * \<gamma> \<and> resreach f s t)) = (get_source_target_path_a_impl state_impl s = None)"
  using impl_a_None_aux 
  by force

lemma impl_b_None_aux:
" \<lbrakk>b = balance state; \<gamma> = current_\<gamma> state; f = current_flow state;
            t \<in> VV; aux_invar state; (\<forall> e \<in> \<F> state . f e > 0);
            loopB_call2_cond state \<or> loopB_fail2_cond state; t = get_target state;
           state = abstract state_impl; implementation_invar state_impl;
           invar_gamma state\<rbrakk>
    \<Longrightarrow> \<not> (\<exists> s \<in> VV. b s > \<epsilon> * \<gamma> \<and> resreach f s t) \<longleftrightarrow> get_source_target_path_b_impl state_impl t = None"
proof(goal_cases)
  case 1
  note knowledge = this
  define bf_impl where "bf_impl = bellman_ford_backward (\<lambda>e. TB (not_blocked_lookup (not_blocked_impl state_impl) e))
           (\<lambda>e. the (flow_lookup (current_flow_impl state_impl) e)) t"
  define ss_impl where " ss_impl = get_source_for_target_aux_aux bf_impl 
                                          (\<lambda>v. the (bal_lookup (balance_impl state_impl) v)) 
                                               (current_\<gamma>_impl state_impl)
                                   vs"
  define bf where "bf = bellman_ford_backward (not_blocked state) (current_flow state) t"
  have bal_coincide: "v \<in> set vs \<Longrightarrow> bal_lookup (balance_impl state_impl) v = Some (b v)" for v
    using algo_impl.implementation_invar_partial_props(6)[OF algo_impl knowledge(10)]
          vs_is_V  algo_impl.abstractE'(2)[OF algo_impl, of \<b>]
    by(auto simp add: algo_impl.abstract_bal_map_def[OF algo_impl]  dom_def knowledge(1,10,9))
  have flow_coincide: "e \<in> \<E> \<Longrightarrow> the (flow_lookup (current_flow_impl state_impl) e) = f e" for e
    using vs_is_V  algo_impl.abstractE'(1)[OF algo_impl, of \<b>]
    by(auto simp add: algo_impl.implementation_invar_partial_props(4)[OF algo_impl knowledge(10)]
                      algo_impl_spec.abstract_flow_map_def[OF algo_impl_spec]  dom_def knowledge(3,10,9))
  have not_blocked_in_E: "not_blocked state e \<Longrightarrow> e \<in> \<E>" for e
    using vs_is_V  algo_impl.abstractE'(11)[OF algo_impl, of \<b>]
    by(auto intro: option.exhaust[of "not_blocked_lookup (not_blocked_impl state_impl) e"]
            simp add: algo_impl.abstract_not_blocked_map_def[OF algo_impl]  dom_def knowledge(10,9)
                      algo_impl.implementation_invar_partial_props(13)[OF algo_impl knowledge(10)])
  have not_blocked_coincide: "TB (not_blocked_lookup (not_blocked_impl state_impl) e)
                             = (not_blocked state e)" for e
    using algo_impl.implementation_invar_partial_props(13)[OF algo_impl knowledge(10)]
         algo_impl.abstractE'(11)[OF algo_impl, of \<b>]
     by(auto simp add: algo_impl.abstract_not_blocked_map_def[OF algo_impl]  dom_def  knowledge(10,9) )    
  have same_costs:"get_edge_and_costs_backward (\<lambda>e. TB (not_blocked_lookup (not_blocked_impl state_impl) e))
                   (\<lambda>e. the (flow_lookup (current_flow_impl state_impl) e))
        = get_edge_and_costs_backward (not_blocked state) (current_flow state)"
    using local.not_blocked_coincide knowledge(3) local.flow_coincide 
    by (auto intro!: ext intro: same_costs_backward)
  have same_bellman_ford:"bf_impl = bf"
    using same_costs  
    by (auto simp add: bellman_ford_backward_def bf_def bf_impl_def bellman_ford_algo_def bellman_ford_init_algo_def)   
  have gamma_coincide: "current_\<gamma>_impl state_impl = current_\<gamma> state"
    using knowledge(9) 
    by(simp add: algo_impl.abstract_def[OF algo_impl])
  have bellman_ford:"bellman_ford connection_empty connection_lookup connection_invar connection_delete
     es vs (\<lambda> u v. prod.snd (get_edge_and_costs_backward (not_blocked state) (current_flow state) u v)) connection_update"
    by (simp add: bellman_ford_backward)
  have t_prop: "- (1 - \<epsilon>) * \<gamma> > b t" "t \<in> VV" 
    by(rule disjE[OF knowledge(7)]) 
      (insert get_target_aux[of vs b \<gamma> , OF _  refl] vs_is_V knowledge;
         fastforce elim!: loopB_call2_condE loopB_fail2_condE 
        simp add:  get_target_def knowledge)+ 
   hence bt0:"b t < 0"   
     using knowledge(11,2,1) \<epsilon>_axiom(2,4) algo.invar_gamma_def
     by (smt (verit, del_insts) divide_less_eq_1_pos mult_minus_left mult_nonneg_nonneg)
  have "\<not> (\<exists> s \<in> VV. b s > \<epsilon> * \<gamma> \<and> resreach f s t) \<longleftrightarrow> 
            (ss_impl = None)"
  proof(rule,  all \<open>rule ccontr\<close>, goal_cases)
    case 1
    then obtain s where "ss_impl = Some s" by auto
    note 1 = this 1
    hence "(\<exists>x\<in>set vs.
    the (bal_lookup (balance_impl state_impl) x) > \<epsilon> * current_\<gamma>_impl state_impl \<and>
    prod.snd (the (connection_lookup bf_impl x)) < PInfty)"
      using  get_source_for_target_aux_aux[of vs "current_\<gamma>_impl state_impl" 
                                              " (\<lambda>v. the (bal_lookup (balance_impl state_impl) v))"
                                               bf_impl, simplified sym[OF ss_impl_def]]
      by simp
    hence "(\<exists>x\<in>set vs. b x > \<epsilon> * current_\<gamma> state \<and> prod.snd (the (connection_lookup bf x)) < PInfty)"
      by(simp add: bal_coincide gamma_coincide same_bellman_ford )
    then obtain x where x_prop:"x \<in> set vs" "b x > \<epsilon> * current_\<gamma> state" "prod.snd (the (connection_lookup bf x)) < PInfty"
      by auto
    hence bx0:"b x > 0"
      using knowledge(11,2,1) \<epsilon>_axiom algo.invar_gamma_def 
      by (smt (verit)  mult_minus_left mult_nonneg_nonneg)
    hence x_not_s:"x \<noteq> t"
      using bt0 by auto
    hence x_in_dom:"x\<in>dom (connection_lookup bf)" "prod.fst (the (connection_lookup bf x)) \<noteq> None"
      using x_prop bellman_ford.same_domain_bellman_ford[OF bellman_ford, of "length vs -1" t]
            bellman_ford.bellman_ford_init_dom_is[OF bellman_ford, of t] 
            bellman_ford.bellman_ford_pred_non_infty_pres[OF bellman_ford, of t "length vs - 1"]
      by(auto simp add: bf_def bellman_ford_backward_def bellman_ford.invar_pred_non_infty_def[OF bellman_ford]
                        bellman_ford_algo_def bellman_ford_init_algo_def)
    obtain p where p_prop:"weight_backward (not_blocked state) (current_flow state) (p @ [x]) = 
                    prod.snd (the (connection_lookup bf x))"
           "last p = the (prod.fst (the (connection_lookup bf x)))"
           "hd p = t" "1 \<le> length p" "set (p @ [x]) \<subseteq> Set.insert t (set vs)"
      using  bellman_ford.bellman_ford_invar_pred_path_pres[OF bellman_ford, of t "length vs -1"]
             x_in_dom 
      by (auto simp add: bellman_ford.invar_pred_path_def[OF bellman_ford] bf_def bellman_ford_backward_def
                         bellman_ford_algo_def bellman_ford_init_algo_def)
    hence pw_le_PInfty: "weight_backward (not_blocked state) (current_flow state) (p @ [x]) < PInfty"
      using x_prop by auto
    define pp where "pp = (map (\<lambda>e. prod.fst (get_edge_and_costs_backward (not_blocked state) (current_flow state) (prod.snd e) (prod.fst e)))
               (map prod.swap (rev (edges_of_vwalk (p @ [x])))))"
    have transformed:" awalk UNIV (last (p @ [x])) (map prod.swap (rev (edges_of_vwalk (p @ [x])))) (hd (p @ [x]))"
         "(\<And>e. e\<in>set pp \<Longrightarrow> not_blocked state (cost_flow_network.oedge e) \<and> 0 < cost_flow_network.rcap (current_flow state) e)"
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
    moreover have "0 < cost_flow_network.Rcap f (set pp)"
      using transformed(2) knowledge(3)
      by(auto intro: linorder_class.Min_gr_iff simp add: cost_flow_network.Rcap_def)
    ultimately have "augpath f pp"
      by(simp add: cost_flow_network.augpath_def)
    moreover have " e \<in> set pp \<Longrightarrow> e \<in> EEE" for e
      using transformed(2)[of e] not_blocked_in_E cost_flow_network.o_edge_res by blast
    ultimately have "resreach f x t"
      using cost_flow_network.augpath_imp_resreach[OF , of f pp] path_hd p_prop(3,4) path_last
      by (metis One_nat_def hd_append2 last_snoc le_numeral_extra(4) list.size(3) not_less_eq_eq subsetI)
    thus False
      using 1 x_prop(1,2) knowledge(2) vs_is_V
      by simp
  next
    case 2
    then obtain s where "s\<in>multigraph.\<V> " "\<epsilon> * \<gamma> < b s" "resreach f s t" by auto
    note 2 = 2 this
    hence "b s > 0"
      using knowledge(11,2,1) \<epsilon>_axiom algo.invar_gamma_def 
      by (smt (verit)  mult_minus_left mult_nonneg_nonneg)
    hence t_not_s:"t \<noteq> s"
      using bt0 by auto
    obtain q where q_props:"augpath f q" "fstv (hd q) = s" 
                    "sndv (last q) = t" "set q \<subseteq> EEE"
      using  cost_flow_network.resreach_imp_augpath[OF  2(5)] by auto
    then obtain qq where qq_props:"augpath f qq"
       "fstv (hd qq) = s"
       "sndv (last qq) = t"
       "set qq \<subseteq> {e |e. e \<in> EEE \<and> cost_flow_network.oedge e \<in> to_set (actives state)}
            \<union> to_rdgs to_pair (conv_to_rdg state) (\<FF> state)"
       "qq \<noteq> []"
    using algo.simulate_inactives[OF  q_props(1-4) 1(5) refl 1(3) refl refl refl refl refl refl _  1(6)]
        t_not_s by auto
    have e_in_qq_not_blocked: "e \<in> set qq \<Longrightarrow> not_blocked state (flow_network.oedge e)" for e   
      using qq_props(4) 
      by(induction e rule: cost_flow_network.oedge.induct)
        (force simp add: spec[OF from_aux_invar'(22)[OF 1(5)]] from_aux_invar'(21)[OF 1(5)])+
    have e_in_qq_rcap: "e \<in> set qq \<Longrightarrow> 0 < cost_flow_network.rcap f e" for e
      using qq_props(1)  linorder_class.Min_gr_iff 
      by (auto simp add: augpath_def cost_flow_network.Rcap_def)
    obtain Q where Q_prop:"fstv (hd Q) = s" "sndv (last Q) = t" 
                   "distinct Q" "set Q \<subseteq> set qq" "augpath f Q"
      using cost_flow_network.there_is_s_t_path[OF , OF qq_props(1-3) refl] by auto
    define Q' where "Q'  = map cost_flow_network.erev (rev Q)"
    have Q'_prop: "fstv (hd Q') = t" "sndv (last Q') = s" 
                   "distinct Q'" 
      using Q_prop(1,2,3,5)  unfolding Q'_def cost_flow_network.augpath_def cost_flow_network.prepath_def
       by(auto simp add: hd_map[of "rev Q"] hd_rev last_map[of "rev Q"] last_rev cost_flow_network.vs_erev distinct_map cost_flow_network.inj_erev o_def)
    have e_in_qq_E: "e \<in> set Q \<Longrightarrow> oedge e \<in> \<E>" for e 
      using Q_prop(4) e_in_qq_not_blocked not_blocked_in_E by auto
    have costsQ: "e \<in> set Q \<Longrightarrow>
         prod.snd (get_edge_and_costs_backward (not_blocked state) f (sndv e) (fstv e)) < PInfty" for e
     apply(rule order.strict_trans1)
     apply(rule conjunct1[OF get_edge_and_costs_backward_makes_cheaper[OF refl _ _ , of e "not_blocked state" f]])
     using  e_in_qq_E  e_in_qq_not_blocked  e_in_qq_rcap Q_prop(4) 
     by(auto intro: prod.collapse)
   have costsQ': "e \<in> set Q' \<Longrightarrow>
         prod.snd (get_edge_and_costs_backward (not_blocked state) f (fstv e) (sndv e)) < PInfty" for e
   proof(goal_cases)
     case 1
     have helper: "\<lbrakk> (\<And>e. e \<in> set Q \<Longrightarrow>
                   prod.snd (get_edge_and_costs_backward (not_blocked state) f (cost_flow_network.sndv e)
                    (cost_flow_network.fstv e)) \<noteq> \<infinity>); x \<in> set Q ; e = cost_flow_network.erev x;
                   prod.snd (get_edge_and_costs_backward (not_blocked state) f
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
      have helper: "\<lbrakk> s = fstv (hd Q);  Q \<noteq> []; 0 < cost_flow_network.Rcap f (set Q);
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
    have "weight_backward (not_blocked state) f (awalk_verts t (map cost_flow_network.to_vertex_pair Q')) < PInfty"
      using costsQ'  awalk Q'_prop(1) bellman_ford  knowledge(3) 
      by (intro path_flow_network_path_bf_backward[of Q' "not_blocked state" f t]) auto
    moreover have " (hd (awalk_verts t (map cost_flow_network.to_vertex_pair Q'))) = t"
      using awalk by simp
    moreover have "last (awalk_verts t (map cost_flow_network.to_vertex_pair Q')) = s" 
        using awalk by simp
   ultimately have " bellman_ford.OPT vs (\<lambda>u v. prod.snd (get_edge_and_costs_backward (not_blocked state) (current_flow state) u v))
           (length vs - 1) t s < PInfty" 
        using t_not_s 1(3)
        by(intro bellman_ford.weight_le_PInfty_OPTle_PInfty[OF bellman_ford _ _ refl,
                    of _ "tl (butlast (awalk_verts t (map cost_flow_network.to_vertex_pair Q')))"],
              cases "awalk_verts t (map cost_flow_network.to_vertex_pair Q')" rule: list_cases_both_sides) auto
    moreover have "prod.snd (the (connection_lookup bf s)) \<le> 
            bellman_ford.OPT vs (\<lambda>u v. prod.snd (get_edge_and_costs_backward(not_blocked state) (current_flow state) u v))
           (length vs - 1) t s"
      using bellman_ford.bellman_ford_shortest[OF bellman_ford, of t "length vs -1" s] vs_is_V
            knowledge(4)
      by(auto simp add: bf_def bellman_ford_backward_def bellman_ford_algo_def bellman_ford_init_algo_def)
    ultimately have "prod.snd (the (connection_lookup bf s)) < PInfty" by auto
    hence "s \<in> set vs" "b s > \<epsilon> * current_\<gamma> state" "prod.snd (the (connection_lookup bf s)) < PInfty"
      using "2" knowledge(2) vs_is_V by auto
    hence "(\<exists>x\<in>set vs.
    the (bal_lookup (balance_impl state_impl) x) > \<epsilon> * current_\<gamma>_impl state_impl \<and>
    prod.snd (the (connection_lookup bf_impl x)) < PInfty)"
      by(auto simp add: bal_coincide gamma_coincide same_bellman_ford )
    hence "(ss_impl \<noteq> None)"
      using get_source_for_target_aux_aux[of vs "current_\<gamma>_impl state_impl"
                "(\<lambda>v. the (bal_lookup (balance_impl state_impl) v))" bf_impl, simplified sym[OF ss_impl_def]]
      by simp
    thus False
      using 2 by simp
  qed
  thus ?thesis 
    by(auto simp add: ss_impl_def bf_impl_def get_source_target_path_b_impl_def)
qed

lemma impl_b_None:
" b = balance state \<Longrightarrow>
       \<gamma> = current_\<gamma> state \<Longrightarrow>
       f = current_flow state \<Longrightarrow>
       abstract state_impl = state \<Longrightarrow>
       t \<in> VV \<Longrightarrow>
       aux_invar state \<Longrightarrow>
       (\<forall>e\<in>\<F> state. 0 < f e) \<Longrightarrow>
       loopB_call2_cond state \<or> loopB_fail2_cond state \<Longrightarrow>
       t = get_target state \<Longrightarrow>
       implementation_invar state_impl \<Longrightarrow>
       algo.invar_gamma state \<Longrightarrow>
       (\<not> (\<exists>s\<in>VV. \<epsilon> * \<gamma> < b s \<and> resreach f s t)) = (get_source_target_path_b_impl state_impl t = None)"
  using  impl_b_None_aux
  by force

lemma test_all_vertices_zero_balance_aux:
"test_all_vertices_zero_balance_aux b xs \<longleftrightarrow> (\<forall> x \<in> set xs. b x = 0)"
  by(induction b xs rule: test_all_vertices_zero_balance_aux.induct) auto

lemma test_all_vertices_zero_balance:
       "abstract state_impl = state \<Longrightarrow>
       b = balance state \<Longrightarrow>
       implementation_invar state_impl \<Longrightarrow> test_all_vertices_zero_balance state_impl = (\<forall>v\<in>VV. b v = 0)"
  using vs_is_V 
  by(auto intro:    ball_cong
          simp add: algo_impl.implementation_invar_def[OF algo_impl] 
                    algo_impl.abstract_def[OF algo_impl] Let_def dom_def 
                    algo_impl.abstract_bal_map_def[OF algo_impl]
                    test_all_vertices_zero_balance_def test_all_vertices_zero_balance_aux)

lemma loopB_impl_axioms:
    "loopB_impl_axioms snd make_pair \<u> \<c> \<E> vset_inv isin set_invar to_set lookup' adjmap_inv' \<b> to_pair \<epsilon> default_conv_to_rdg
     get_source_target_path_b get_source get_target get_source_for_target get_target_for_source get_source_target_path_a
     flow_lookup flow_invar bal_lookup bal_invar rep_comp_lookup rep_comp_invar conv_lookup conv_invar not_blocked_lookup
     not_blocked_invar get_source_target_path_a_impl get_source_target_path_b_impl get_source_impl get_target_impl
     test_all_vertices_zero_balance fst"
  unfolding loopB_impl_axioms_def
  apply rule
  subgoal
    apply rule
    subgoal
       using abstract_impl_correspond_a  impl_a_None by auto fastforce+
    subgoal
      using abstract_impl_correspond_b impl_b_None by auto fastforce+
      done
    apply rule
    subgoal      
      using get_source_impl_axioms by auto
    apply rule
    subgoal      
      using get_target_impl_axioms by auto     
    apply rule
    subgoal      
      using get_target_impl_axioms by auto 
    using test_all_vertices_zero_balance by auto

interpretation rep_comp_map2: Map where empty = rep_comp_empty and update=rep_comp_update and lookup= rep_comp_lookup
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

lemma orlins_impl_axioms:
"orlins_impl_axioms make_pair \<E> \<b> flow_lookup flow_invar bal_lookup bal_invar rep_comp_lookup rep_comp_invar not_blocked_lookup
     not_blocked_invar init_flow init_bal init_rep_card init_not_blocked"
proof(rule orlins_impl_axioms.intro, goal_cases)
  case 1
  then show ?case 
    by (simp add: init_impl_variables(1) local.init_flow_def)
next
  case 2
  then show ?case 
    using \<E>_impl_invar init_impl_variables(2) local.algo.\<E>_impl_meaning(1) local.ees_def local.init_flow_def local.to_list(1) by auto
next
  case 3
  then show ?case
    using invar_b_impl local.init_bal_def by auto
next
  case 4
  then show ?case
    by (simp add: b_impl_dom local.\<E>_def local.init_bal_def)
next
  case (5 x)
  then show ?case 
    by (simp add: b_impl_dom domIff local.\<E>_def local.\<b>_def local.init_bal_def)
next
  case 6
  then show ?case 
    using init_impl_variables(3) local.init_rep_card_def by auto
next
  case 7
  then show ?case 
    using init_impl_variables(4) local.init_rep_card_def vs_is_V by presburger
next
  case 8
  then show ?case 
    by (simp add: init_impl_variables(5) local.init_not_blocked_def)
next
  case 9
  then show ?case
    using \<E>_impl_invar init_impl_variables(6) local.algo.\<E>_impl_meaning(1) local.ees_def local.init_not_blocked_def local.to_list(1) by force
next
  case (10 e)
  then show ?case
    by (simp add: init_impl_variables(7) local.init_not_blocked_def)
qed

interpretation orlins_impl: orlins_impl snd make_pair create_edge \<u> \<E> \<c> edge_map_update' vset_empty vset_delete vset_insert vset_inv isin
     filter are_all set_invar to_set lookup' t_set sel adjmap_inv' \<b> to_pair \<epsilon> N default_conv_to_rdg get_from_set all_empty
     \<E>_impl get_path flow_empty  flow_update flow_delete flow_lookup flow_invar bal_empty bal_update bal_delete bal_lookup
     bal_invar rep_comp_empty rep_comp_update rep_comp_delete rep_comp_lookup rep_comp_invar conv_empty conv_update
     conv_delete conv_lookup conv_invar not_blocked_update not_blocked_empty not_blocked_delete not_blocked_lookup
     not_blocked_invar rep_comp_update_all not_blocked_update_all flow_update_all get_max get_source_target_path_b
     get_source get_target get_source_for_target get_target_for_source get_source_target_path_a
     get_source_target_path_a_impl get_source_target_path_b_impl get_source_impl get_target_impl
     test_all_vertices_zero_balance norma init_flow init_bal init_rep_card init_not_blocked fst
  using  orlins_impl_axioms loopA_axioms_extended Adj_Map_Specs2 Set3  Set3_axioms
         algo loopB_Reasoning loopB_impl_axioms
         Map_bal.Map_axioms Map_conv Map_flow.Map_axioms Map_not_blocked.Map_axioms
         conv_map.Map_axioms  Map_axioms
  by(auto intro!: loopA.intro orlins_impl_spec.intro orlins_impl.intro  loopB_impl.intro
                  loopA_impl.intro loopB_impl_spec.intro loopA_impl_spec.intro loopA_spec.intro
                  algo_impl_spec.intro algo_impl.intro algo_spec.intro algo_impl_spec_axioms.intro  
                  flow_update_all get_max not_blocked_update_all rep_comp_update_all
        simp add: loopA_axioms_def orlins_def orlins_axioms_def norma_def insert_commute to_pair_axioms)

lemmas orlins_impl = orlins_impl.orlins_impl_axioms

definition "initial_state_impl  =
Orlins_Implementation.orlins_impl_spec.initial_impl snd filter all_empty \<E>_impl conv_empty rep_comp_update_all
 not_blocked_update_all flow_update_all get_max fst init_flow 
init_bal init_rep_card init_not_blocked"

definition "loopA_loop_impl = loopA_impl_spec.loopA_impl snd edge_map_update' vset_insert filter lookup'
N get_from_set get_path flow_update flow_lookup bal_update bal_lookup rep_comp_lookup conv_update
 conv_lookup rep_comp_update_all not_blocked_update_all fst"

definition "loopB_loop_impl = loopB_impl_spec.loopB_impl flow_update flow_lookup bal_update bal_lookup
 get_source_target_path_a_impl
 get_source_target_path_b_impl get_source_impl
 get_target_impl test_all_vertices_zero_balance "

definition "orlins_loop_impl =
 Orlins_Implementation.orlins_impl_spec.orlins_impl snd edge_map_update' vset_insert filter are_all lookup'
 N get_from_set get_path flow_update flow_lookup bal_update bal_lookup
 rep_comp_lookup conv_update conv_lookup rep_comp_update_all not_blocked_update_all get_max
get_source_target_path_a_impl get_source_target_path_b_impl get_source_impl
 get_target_impl test_all_vertices_zero_balance fst"

definition "final_state = orlins_loop_impl (loopB_loop_impl  (initial_state_impl))"
definition "final_flow_impl = current_flow_impl final_state"

definition "abstract_flow_map = algo_impl_spec.abstract_flow_map flow_lookup"

corollary correctness_of_implementation:
 "return_impl final_state = success \<Longrightarrow>   cost_flow_network.is_Opt  \<b> (abstract_flow_map final_flow_impl)"
 "return_impl final_state = failure \<Longrightarrow>  \<nexists> f. cost_flow_network.isbflow f \<b>"
 "return_impl final_state = notyetterm \<Longrightarrow>  False"
  using orlins_impl.orlins_impl_is_correct[OF  refl] 
  by(auto simp add: final_flow_impl_def final_state_def abstract_flow_map_def
 orlins_loop_impl_def initial_state_impl_def loopB_loop_impl_def)

lemma final_flow_domain: "dom (flow_lookup final_flow_impl) = \<E>"
  using orlins_impl.final_flow_domain
  by(auto simp add: final_flow_impl_def final_state_def abstract_flow_map_def
 orlins_loop_impl_def initial_state_impl_def loopB_loop_impl_def)

end
end


definition "no_cycle_cond make_pair \<c>_impl \<E>_impl c_lookup = (\<forall> C. closed_w (make_pair ` function_generation.\<E> \<E>_impl to_set) (map make_pair C) \<longrightarrow>
         set C \<subseteq> function_generation.\<E> \<E>_impl to_set \<longrightarrow>
         foldr (\<lambda>e acc. acc + function_generation.\<c> \<c>_impl c_lookup e) C 0 < 0 \<longrightarrow> False)"

lemma function_generation_proof_axioms:
" set_invar \<E>_impl \<Longrightarrow> bal_invar \<b>_impl\<Longrightarrow>
 dVs (make_pair ` to_set \<E>_impl) = dom (bal_lookup \<b>_impl) \<Longrightarrow>
0 < function_generation.N \<E>_impl to_list (fst \<circ> make_pair) (snd \<circ> make_pair) \<Longrightarrow>
 function_generation_proof_axioms bal_lookup bal_invar 
 \<E>_impl to_list (fst o make_pair) (snd o make_pair)  \<b>_impl set_invar to_set make_pair get_max"
  by (intro function_generation_proof_axioms.intro)(auto simp add: orlins_impl_spec.get_max to_list \<E>_def \<c>_def no_cycle_cond_def)

interpretation rep_comp_iterator: Map_iterator rep_comp_invar rep_comp_lookup rep_comp_update_all
  using Map_iterator_def rep_comp_update_all by blast
lemmas rep_comp_iterator=rep_comp_iterator.Map_iterator_axioms

interpretation flow_iterator: Map_iterator flow_invar flow_lookup flow_update_all
  using Map_iterator_def flow_update_all  by blast
lemmas flow_iterator=flow_iterator.Map_iterator_axioms

interpretation not_blocked_iterator: Map_iterator not_blocked_invar not_blocked_lookup not_blocked_update_all
  using Map_iterator_def not_blocked_update_all  by blast
lemmas not_blocked_iterator = not_blocked_iterator.Map_iterator_axioms

definition "final_state make_pair create_edge \<E>_impl \<c>_impl \<b>_impl c_lookup = orlins_impl  make_pair create_edge \<E>_impl \<c>_impl c_lookup
                    (loopB_impl  make_pair  create_edge \<E>_impl \<c>_impl c_lookup
                            (initial_impl  make_pair \<E>_impl \<b>_impl))"

definition "final_flow_impl  make_pair create_edge \<E>_impl \<c>_impl \<b>_impl c_lookup=
                 (current_flow_impl (final_state  make_pair create_edge \<E>_impl \<c>_impl \<b>_impl c_lookup))"

definition "abstract_flow_map = algo_impl_spec.abstract_flow_map flow_lookup"

locale correctness_of_algo =
  fixes make_pair
and \<c>_impl:: 'c_impl
and  \<E>_impl::"('edge_type::linorder) list" and create_edge 
and \<b>_impl:: "(('a::linorder \<times> real) \<times> color) tree"
and c_lookup::"'c_impl \<Rightarrow> 'edge_type \<Rightarrow> real option"
assumes \<E>_impl_basic: "set_invar \<E>_impl" " bal_invar (\<b>_impl)"
and  Vs_is_bal_dom: "dVs (make_pair ` to_set \<E>_impl) = dom (bal_lookup \<b>_impl)"
and at_least_2_verts: "0 < function_generation.N \<E>_impl to_list (fst \<circ> make_pair) (snd \<circ> make_pair)"
and multigraph: "multigraph (fst \<circ> make_pair) (snd \<circ> make_pair) make_pair create_edge (function_generation.\<E> \<E>_impl to_set)"
begin

interpretation function_generation_proof:
function_generation_proof realising_edges_empty realising_edges_update realising_edges_delete
     realising_edges_lookup realising_edges_invar bal_empty bal_delete bal_lookup bal_invar flow_empty flow_delete
     flow_lookup flow_invar not_blocked_empty not_blocked_delete not_blocked_lookup not_blocked_invar
     rep_comp_empty rep_comp_delete rep_comp_lookup rep_comp_invar \<E>_impl 
     to_list "(fst o make_pair)" "(snd o make_pair)" create_edge \<c>_impl \<b>_impl c_lookup
     filter are_all set_invar get_from_set to_set make_pair rep_comp_update conv_empty conv_delete conv_lookup
     conv_invar conv_update not_blocked_update flow_update bal_update rep_comp_update_all flow_update_all
     not_blocked_update_all get_max
  using  \<E>_impl_basic at_least_2_verts gt_zero multigraph
  using  rep_comp_iterator flow_iterator not_blocked_iterator  
  by(auto intro!:  function_generation_proof_axioms function_generation_proof.intro 
        simp add: flow_map.Map_axioms Map_not_blocked.Map_axioms Set3 \<E>_def Adj_Map_Specs2
                  Map_rep_comp Map_conv   bal_invar_b Vs_is_bal_dom  
                  Map_realising_edges function_generation.intro bal_map.Map_axioms ) 

lemmas function_generation_proof = function_generation_proof.function_generation_proof_axioms
context 
  assumes no_cycle: "no_cycle_cond make_pair \<c>_impl \<E>_impl c_lookup"
begin

lemma no_cycle: "closed_w (make_pair ` function_generation.\<E> \<E>_impl to_set) (map make_pair C) \<Longrightarrow>
          set C \<subseteq> function_generation.\<E> \<E>_impl to_set \<Longrightarrow>
          foldr (\<lambda>e acc. acc + function_generation.\<c> \<c>_impl c_lookup e) C 0 < 0 \<Longrightarrow> False"
  using no_cycle  by (auto simp add: no_cycle_cond_def)

lemma no_cycle_cond:"function_generation_proof.no_cycle_cond "
  unfolding function_generation_proof.no_cycle_cond_def
  using no_cycle by blast

corollary correctness_of_implementation:
 "return_impl (final_state  make_pair create_edge \<E>_impl \<c>_impl \<b>_impl c_lookup) = success \<Longrightarrow>  
        cost_flow_network.is_Opt (fst o make_pair) (snd o make_pair) make_pair \<u> (\<c> \<c>_impl c_lookup) (\<E> \<E>_impl) (\<b> \<b>_impl) 
 (abstract_flow_map (final_flow_impl  make_pair create_edge \<E>_impl \<c>_impl \<b>_impl c_lookup))"
 "return_impl (final_state  make_pair create_edge \<E>_impl \<c>_impl \<b>_impl c_lookup) = failure \<Longrightarrow> 
         \<nexists> f. flow_network.isbflow  (fst o make_pair) (snd o make_pair) make_pair \<u>  (\<E> \<E>_impl) f (\<b> \<b>_impl)"
 "return_impl (final_state  make_pair create_edge \<E>_impl \<c>_impl \<b>_impl c_lookup) = notyetterm \<Longrightarrow>  
         False"
    using  function_generation_proof.correctness_of_implementation[OF  no_cycle_cond] 
    by(auto simp add: final_state_def 
                function_generation_proof.final_state_def[OF  no_cycle_cond]
                function_generation_proof.orlins_loop_impl_def[OF  no_cycle_cond]
                orlins_impl_def loopB_impl_def N_def get_source_target_path_a_impl_def
                get_source_target_path_b_impl_def get_source_impl_def get_target_impl_def get_path_def
                test_all_vertices_zero_balance_def 
                function_generation_proof.loopB_loop_impl_def[OF  no_cycle_cond] initial_impl_def 
                function_generation_proof.initial_state_impl_def[OF  no_cycle_cond] init_flow_def
                init_bal_def init_rep_card_def init_not_blocked_def abstract_flow_map_def final_flow_impl_def
                function_generation_proof.final_flow_impl_def[OF  no_cycle_cond]
                function_generation_proof.abstract_flow_map_def[OF  no_cycle_cond] \<E>_def \<b>_def \<c>_def \<u>_def)

lemma final_flow_domain:
 "dom (flow_lookup (final_flow_impl  make_pair create_edge \<E>_impl \<c>_impl \<b>_impl c_lookup)) = \<E> \<E>_impl"
  using function_generation_proof.final_flow_domain[OF no_cycle_cond]
     by(auto simp add: final_state_def 
                function_generation_proof.final_state_def[OF  no_cycle_cond]
                function_generation_proof.orlins_loop_impl_def[OF  no_cycle_cond]
                orlins_impl_def loopB_impl_def N_def get_source_target_path_a_impl_def
                get_source_target_path_b_impl_def get_source_impl_def get_target_impl_def get_path_def
                test_all_vertices_zero_balance_def 
                function_generation_proof.loopB_loop_impl_def[OF  no_cycle_cond] initial_impl_def 
                function_generation_proof.initial_state_impl_def[OF  no_cycle_cond] init_flow_def
                init_bal_def init_rep_card_def init_not_blocked_def  final_flow_impl_def
                function_generation_proof.final_flow_impl_def[OF  no_cycle_cond] \<E>_def )

end
end
datatype 'a cost_wrapper = cost_container 'a
end