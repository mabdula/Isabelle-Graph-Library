theory Ordered_Map_Heap (*TODO rename to Key_Value_Queue_Instantiation*)
  imports Complex_Main "Priority_Search_Trees.PST_RBT" Key_Value_Queue_Spec
begin

section \<open>Instantiation of Queue\<close>

(*See the following literature:
 Ralf Hinze: A Simple Implementation Technique for Priority Search Queues
 Lammich and Nipkow: Proof Pearl: Purely Functional, Simple and
        Efficient Priority Search Trees and Applications to Prim and Dijkstra (ITP 2019)
 Lammich and Nipkow: Priority_Search_Trees (AFP)*)

type_synonym 'a real_queue = "(('a \<times> real) \<times> tcolor \<times> 'a \<times> real) tree"
thm PST_RBT.PM.PrioMap_by_Ordered_axioms

definition "queue_empty = (empty::('a::linorder) real_queue)"
definition "queue_extract_min = 
(\<lambda> Q::('a::linorder) real_queue. 
  if Q = Leaf then (Q, None)
  else
  (let m = fst (pst_getmin Q)
  in (delete m Q, Some m)))"

definition "queue_decrease_key = 
(\<lambda> (Q::('a::linorder) real_queue) x k. update x k Q)"

definition "queue_insert = 
(\<lambda> (Q::('a::linorder) real_queue) x k. update x k Q)"

definition "queue_invar = 
(\<lambda> (Q::('a::linorder) real_queue). PST_RBT.PM.invar Q)"

definition "queue_abstract = 
(\<lambda> (Q::('a::linorder) real_queue). 
   {(x, k) | x k. lookup Q x = Some k})"

lemmas queue_defs = 
queue_empty_def 
queue_extract_min_def
queue_decrease_key_def
queue_insert_def
queue_invar_def
queue_abstract_def

interpretation key_value_queue_spec_satisfied:
   key_value_queue queue_empty queue_extract_min queue_decrease_key
                   queue_insert queue_invar queue_abstract
proof(rule key_value_queue.intro, goal_cases)
  case 1
  then show ?case 
    by(simp add: queue_defs PM.invar_empty)
next
  case 2
  then show ?case 
    by(simp add: queue_defs PST_RBT.empty_def)
next
  case (3 H)
  then show ?case 
    by(auto simp add: queue_defs Let_def PM.invar_delete)
next
  case (4 H x)
  then show ?case 
    by(cases "H = \<langle>\<rangle>")
      (auto intro: PM.map_getminE[OF surjective_pairing, of H] 
             dest: PM.map_is_empty[simplified rbt_is_empty_def]
         simp add: queue_defs Let_def)
next
  case (5 H)
  then show ?case
  by(cases "H = \<langle>\<rangle>")
    (auto simp add: queue_defs Let_def)
next
  case (6 H x k)
  then show ?case 
    by(cases "H = \<langle>\<rangle>")
      (auto simp add: queue_defs Let_def PM.map_delete[of H] 
                      if_split[of "\<lambda> x. x = Some _"])
next
  case (7 H x k)
  then show ?case 
    by(auto simp add: queue_defs PM.invar_update)
next
  case (8 H x k)
  then show ?case 
    by(auto simp add: queue_defs PM.map_specs(2)
                      if_split[of "\<lambda> x. x = Some _"])
next
  case (9 H x k k')
  then show ?case 
    by(auto simp add: queue_defs PM.invar_update)
next
  case (10 H x k k')
  then show ?case 
    by(auto simp add: queue_defs PM.map_update 
                      if_split[of "\<lambda> x. x = Some _"])
next
  case (11 H x k k')
  then show ?case 
    by(auto simp add: queue_defs)
qed

end