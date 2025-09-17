theory Dinic_Instantiation
  imports Dinic Compute_Blocking_Residual Graph_Algorithms_Dev.RBT_Map_Extension
begin

section \<open>Dinic's Algorithm Executable\<close>

text \<open>We use the other theories to get an executable implementation of Dinic's Algorithm.\<close>

instantiation   Redge:: (linorder) linorder
begin

fun less_eq_Redge where
 "less_eq_Redge (F (e::'a::linorder)) (Residual.B d) = (if e = d then True else e \<le> d)"|
 "less_eq_Redge (Residual.B e) (Residual.F d) = (if e = d then False else e\<le> d)"|
 "less_eq_Redge (F e) (Residual.F d) = (e \<le> d)"|
 "less_eq_Redge (Residual.B e) (Residual.B d) = (e \<le> d)"

fun less_Redge where
 "less_Redge (F (e::'a::linorder)) (Residual.B d) = (if e = d then True else e < d)"|
 "less_Redge (Residual.B e) (Residual.F d) = (if e = d then False else e < d)"|
 "less_Redge (F e) (Residual.F d) = (e < d)"|
 "less_Redge (Residual.B e) (Residual.B d) = (e < d)"

instance 
proof(standard, goal_cases)
  case (1 x y)
  then show ?case 
    by(cases x, all \<open>cases y\<close>) auto
  case (2 x)
  then show ?case
    by(cases x, all \<open>cases y\<close>) auto
next
  case (3 x y z)
 from 3 show ?case 
    by(cases x, all \<open>cases y\<close>, all \<open>cases z\<close>) 
       (auto elim!: if_elim)
next
  case (4 x y)
  then show ?case
    by(cases x, all \<open>cases y\<close>) 
      (auto elim: if_elim)
next
  case (5 x y)
  then show ?case 
    by(cases x, all \<open>cases y\<close>) 
      (auto elim: if_elim)
qed
end

global_interpretation dinic_subprocedures:
blocking_level_residual_spec where
fst = fst and
snd = snd and
realising_edges_empty = empty and
 realising_edges_update = update and
realising_edges_delete = delete and
realising_edges_lookup = lookup and
realising_edges_invar = M.invar and
residual_flow_delete = delete
and  residual_flow_lookup = lookup
and residual_flow_invar = M.invar
and residual_flow_empty = empty
and residual_flow_update = update
and \<E> = \<E>
and \<u> = \<u>
and create_edge = create_edge
and \<f> = \<f> 
and es = es
and s = s
and t = t
for fst snd  \<E>  \<u> create_edge \<f> es s t
defines pos_es =  dinic_subprocedures.pos_es
and reslising_edges_general= dinic_subprocedures.realising_edges_general
and realising_edges=dinic_subprocedures.realising_edges
and E_simple=dinic_subprocedures.E_simple
and u_simple=dinic_subprocedures.u_simple
and level_simple=dinic_subprocedures.level_simple
and blocking_flow_simple=dinic_subprocedures.blocking_flow_simple
and residual_add_flow=dinic_subprocedures.residual_add_flow
and residual_blocking_flow=dinic_subprocedures.find_blocking_flow
and split_flow_single=dinic_subprocedures.split_flow_single
  by(auto intro!: blocking_level_residual_spec.intro simp add: M.Map_axioms)

definition "find_blocking_flow flow_lookup fst snd es \<u> s t f
 = residual_blocking_flow fst snd \<u> (abstract_real_map (flow_lookup f))
 es s t"  for fst snd
term "\<lambda> T f init. fold_rbt (\<lambda> (e, fl) acc.  f acc e fl) T init"
term rbt_map_fold term fold_rbt
global_interpretation dinic_exec: dinic_spec
  where fst = fst
and snd = snd
and \<E> = \<E>
and \<u> = \<u>
and create_edge = create_edge
and s = s
and t = t
and flow_update = flow_update
and find_blocking_flow = 
     "find_blocking_flow flow_lookup fst snd es \<u> s t"
and flow_lookup=flow_lookup
and flow_empty = flow_empty
and flow_invar = flow_invar
and resflow_iterate = "\<lambda> T f init. rbt_map_fold T (\<lambda> e fl acc.  f acc e fl) init"
for fst snd  \<E>  \<u> create_edge es s t flow_update  flow_lookup
flow_empty flow_invar
defines dinic_intial = dinic_exec.dinic_initial
and dinic_loop= dinic_exec.dinic_impl
and dinic_step=dinic_exec.dinic_upd
and augment_impl=dinic_exec.augment_impl
and add_flow = dinic_exec.add_flow
  done

locale dinic_instantiation_correctness =
flow_network
  where fst = "fst::'e::linorder \<Rightarrow> 'v::linorder" for fst + 
fixes flow_lookup::"'flow_impl \<Rightarrow> 'e \<Rightarrow> real option"
and   flow_update::"'flow_impl \<Rightarrow> 'e \<Rightarrow> real \<Rightarrow> 'flow_impl"
and   flow_empty::"'flow_impl"
and   flow_invar::"'flow_impl \<Rightarrow> bool"
and   s t::'v
and   es::"'e list"
assumes es_props: "set es = \<E>" "distinct es"
assumes s_neq_t: "s \<noteq> t"
assumes finite_capacities: "\<And> e. e \<in> \<E> \<Longrightarrow> \<u> e < \<infinity>"
assumes flow_datastructure:
        "flow_invar flow_empty"
        "\<And> f. flow_invar f \<Longrightarrow> flow_invar (flow_update f e x)"
        "\<And> f. flow_invar f \<Longrightarrow> flow_lookup (flow_update f e x) = (flow_lookup f)(e:= Some x)"
        "\<And> e. flow_lookup flow_empty e = None"
begin

interpretation dinic_subprocedures_proofs:
blocking_level_residual where
fst = fst and
snd = snd and
realising_edges_empty = empty and
 realising_edges_update = update and
realising_edges_delete = delete and
realising_edges_lookup = lookup and
realising_edges_invar = M.invar and
residual_flow_delete = delete
and  residual_flow_lookup = lookup
and residual_flow_invar = M.invar
and residual_flow_empty = empty
and residual_flow_update = update
and \<E> = \<E>
and \<u> = \<u>
and create_edge = create_edge
and \<f> = \<f> 
and es = es
and s = s
and t = t
for  \<f> 
  using es_props s_neq_t finite_capacities flow_network_axioms
by(auto intro!: blocking_level_residual.intro blocking_level_residual_axioms.intro
      simp add: dinic_subprocedures.blocking_level_residual_spec_axioms)

interpretation dinic_proofs: dinic 
where fst = fst
and snd = snd
and \<E> = \<E>
and \<u> = \<u>
and create_edge = create_edge
and s = s
and t = t
and flow_update = flow_update
and find_blocking_flow = 
     "find_blocking_flow flow_lookup fst snd es \<u> s t"
and flow_lookup=flow_lookup
and flow_empty = flow_empty
and flow_invar = flow_invar
and resflow_iterate = "\<lambda> T f init. rbt_map_fold T (\<lambda> e fl acc.  f acc e fl) init"
and resflow_lookup = lookup
and resflow_invar = M.invar

proof(rule dinic.intro dinic_axioms.intro, goal_cases)
  case 1
  then show ?case by(simp add: flow_network_axioms)
next
  case 2
  show ?case 
  proof(rule dinic_axioms.intro, goal_cases)
    case (1 f)
    then show ?case 
  using dinic_subprocedures_proofs.find_blocking_flow
  by(auto simp add: find_blocking_flow_def residual_blocking_flow_def)
  next
    case (2 f rf)
    then show ?case 
      using dinic_subprocedures_proofs.find_blocking_flow
      by(auto simp add: find_blocking_flow_def residual_blocking_flow_def)
  next
    case (3 f rf)
    then show ?case 
      using dinic_subprocedures_proofs.find_blocking_flow
      by(auto simp add: find_blocking_flow_def residual_blocking_flow_def)
  next
    case (4 f rf)
    then show ?case 
      using dinic_subprocedures_proofs.find_blocking_flow
      by(auto simp add: find_blocking_flow_def residual_blocking_flow_def)
  next
    case (5 rf f init)
    show ?case 
      using rbt_map_fold_correct[OF 5, of "(\<lambda>e fl acc. f acc e fl)" init] by auto
  next
    case 6
    then show ?case 
      by (simp add: flow_datastructure)
  next
    case (7 e x f)
    then show ?case 
      by (simp add: flow_datastructure)
  next
    case (8 e x f)
    then show ?case 
      by (simp add: flow_datastructure)
  next
    case (9 e)
    then show ?case 
      by (simp add: flow_datastructure)
  qed
qed
end

(*definition "\<E>_impl = [(1::nat, 2::nat), (1,3), (3,2), (2,4), (2,5),
(3,5), (4,6), (6,5), (2,6)]"*)


definition "u_list = [( (1::nat, 2::nat), 25::ereal),
 ((1,3), 108), ((3,2), 10), ((2,4), 20), ((2,5), 11),
((3,5), 3), ((4,6), 45), ((6,5), 40), ((2,6), 2.5), ((1, 20), 2), ((20, 21), 3),
 ((21, 22), 4),  ((22, 23), 4.5),  ((23, 24), 8),  ((24, 25), 2.3),  ((25, 26), 10),  
((26, 27), 10),  ((22, 27), 1.5), 
((27, 28), 2), ((28, 29), 3.4), ((29, 30), 5), ((30, 6), 7)]"
definition "\<E>_impl = map fst u_list"

definition "\<u>_impl =
 foldr (\<lambda> xy tree. update (prod.fst xy) (prod.snd xy) tree) u_list Leaf"
value "\<u>_impl"

definition "dinic_initial_example = dinic_intial (empty::(((nat \<times> nat) \<times> real) \<times> color) tree)"
value "dinic_initial_example "

definition "dinic_loop_example =
 dinic_loop fst snd (abstract_real_map (lookup \<u>_impl)) \<E>_impl 1 6 
(\<lambda> T e fl. update e fl T) lookup "

definition "dinic_step_example =
 dinic_step fst snd (abstract_real_map (lookup \<u>_impl)) \<E>_impl 1 6 
(\<lambda> T e fl. update e fl T) lookup "

value "dinic_loop_example (dinic_initial_example)"
value "current_flow (dinic_loop_example (dinic_initial_example))"
value "inorder (current_flow (dinic_loop_example (dinic_initial_example)))"

value "inorder (current_flow (compow 1 dinic_step_example (dinic_initial_example)))"
value "inorder (current_flow (compow 2 dinic_step_example (dinic_initial_example)))"
value "inorder (current_flow (compow 3 dinic_step_example (dinic_initial_example)))"
value "inorder (current_flow (compow 4 dinic_step_example (dinic_initial_example)))"
end