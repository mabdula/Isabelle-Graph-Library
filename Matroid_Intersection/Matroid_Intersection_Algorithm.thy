theory Matroid_Intersection_Algorithm
  imports Matroid_Intersection
begin

section \<open>Maximum Cardinality Matroid Intersection Algorithm\<close>

text \<open>This file contains a formalisation of the maximum cardinality matroid intersection algorithm
given by Korte&Vygen.\<close>

record 'sol intersec_state = sol::'sol

lemma sol_remove: "sol (state \<lparr> sol:= new_sol \<rparr>) = new_sol"
  by auto

locale unweighted_intersection_spec =
  graph: Pair_Graph_Specs where insert = "insert::'a \<Rightarrow> 'vset \<Rightarrow> 'vset"
  and lookup="lookup :: 'adjmap \<Rightarrow> 'a \<Rightarrow> 'vset option"
for insert lookup+ 
fixes set_insert::"'a \<Rightarrow> 'mset \<Rightarrow> 'mset"
  and set_delete::"'a \<Rightarrow> 'mset \<Rightarrow> 'mset"
  and to_set::"'mset \<Rightarrow> 'a set"
  and set_invar::"'mset \<Rightarrow> bool"
  and set_empty::"'mset"
  and weak_orcl1::"'a \<Rightarrow> 'mset \<Rightarrow> bool"
  and weak_orcl2::"'a \<Rightarrow> 'mset \<Rightarrow> bool"
  and inner_fold::"'mset \<Rightarrow> ('a \<Rightarrow> 'adjmap \<Rightarrow> 'adjmap) \<Rightarrow> 'adjmap \<Rightarrow> 'adjmap"
  and inner_fold_circuit::"'mset_red \<Rightarrow> ('a \<Rightarrow> 'adjmap \<Rightarrow> 'adjmap) \<Rightarrow> 'adjmap \<Rightarrow> 'adjmap"
  and outer_fold::"'mset_red \<Rightarrow> ('a \<Rightarrow> ('vset \<times> 'vset \<times> 'adjmap) \<Rightarrow> ('vset \<times> 'vset \<times> 'adjmap)) 
                           \<Rightarrow> ('vset \<times> 'vset \<times> 'adjmap) \<Rightarrow> ('vset \<times> 'vset \<times> 'adjmap)"
  and find_path::"'vset \<Rightarrow> 'vset \<Rightarrow> 'adjmap \<Rightarrow> 'a list option"
  and complement::"'mset \<Rightarrow> 'mset_red"
  and circuit1::"'a \<Rightarrow> 'mset \<Rightarrow>'mset_red"
  and circuit2::"'a \<Rightarrow> 'mset \<Rightarrow>'mset_red"
begin

definition "treat1 y X init_map = 
           inner_fold X (\<lambda> x current_map. if weak_orcl1 y (set_delete x X) 
                                         then graph.add_edge current_map x y 
                                         else current_map)
                       init_map"

definition "treat2 y X init_map = 
           inner_fold X (\<lambda> x current_map. if weak_orcl2 y (set_delete x X) 
                                         then graph.add_edge current_map y x 
                                         else current_map)
                       init_map"

definition "compute_graph X E_without_X =
           outer_fold E_without_X (\<lambda> y (SX, TX, current_map). (
            let (SX, TX, current_map) = (if weak_orcl1 y X then (insert y SX, TX, current_map)
                                         else (SX, TX, treat1 y X current_map));
                (SX, TX, current_map) = (if weak_orcl2 y X then (SX, insert y TX, current_map)
                                         else (SX, TX, treat2 y X current_map))
            in (SX, TX, current_map))) 
           (vset_empty, vset_empty, empty)"

fun augment where
  "augment X Nil = X"|
  "augment X [x] = set_insert x X"|
  "augment X (x#y#xs) = augment (set_insert x (set_delete y X)) xs"

function (domintros) matroid_intersection::"'mset intersec_state\<Rightarrow> 'mset intersec_state"  where
  "matroid_intersection state =
 (let X = sol state; (SX, TX, graph) = compute_graph X (complement X) in
     (case find_path SX TX graph of 
          None \<Rightarrow> state |
          Some p \<Rightarrow> matroid_intersection (state \<lparr> sol := augment X p\<rparr>) ))"
  by pat_completeness auto

definition "matroid_intersection_recurse_cond state =
(let X = sol state; (SX, TX, graph) = compute_graph X (complement X) in
     (case find_path SX TX graph of 
          None \<Rightarrow> False |
          Some p \<Rightarrow> True))"

lemma matroid_intersection_recurse_condE:
  "matroid_intersection_recurse_cond state \<Longrightarrow>
 (\<And> SX TX graph p X. X = sol state \<Longrightarrow> compute_graph X (complement X) = (SX, TX, graph) ==>
         find_path SX TX graph = Some p \<Longrightarrow> P) ==> P"
  by(force simp add: matroid_intersection_recurse_cond_def Let_def)

definition "matroid_intersection_recurse_upd state =
(let X = sol state; (SX, TX, graph) = compute_graph X (complement X) in
     state \<lparr> sol := augment X (the ( find_path SX TX graph )) \<rparr>)"

lemma P_of_matroid_intersection_recurseI:
  "matroid_intersection_recurse_cond state \<Longrightarrow> (\<And> SX TX graph p X. X = sol state \<Longrightarrow>
         compute_graph X (complement X) = (SX, TX, graph) ==>
         find_path SX TX graph = Some p \<Longrightarrow> P (state \<lparr> sol := augment X p\<rparr>)) 
==> P (matroid_intersection_recurse_upd state)"
  unfolding matroid_intersection_recurse_cond_def
    matroid_intersection_recurse_upd_def Let_def 
  apply(cases "compute_graph (sol state) (complement (sol state))", simp)
  subgoal for a b c
    by(cases "find_path a b c") auto
  done

definition "matroid_intersection_terminates_cond state =
(let X = sol state; (SX, TX, graph) = compute_graph X (complement X) in
     (case find_path SX TX graph of 
          None \<Rightarrow> True |
          Some p \<Rightarrow> False))"

lemma matroid_intersection_terminates_condE:
  "matroid_intersection_terminates_cond state \<Longrightarrow>
 (\<And> SX TX graph X. X = sol state \<Longrightarrow>  compute_graph X (complement X) = (SX, TX, graph) ==>
         find_path SX TX graph = None \<Longrightarrow> P) ==> P"
  by(force simp add: matroid_intersection_terminates_cond_def Let_def)

lemma matroid_intersection_cases:
  "(matroid_intersection_terminates_cond state \<Longrightarrow> P) \<Longrightarrow>
 (matroid_intersection_recurse_cond state \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding matroid_intersection_terminates_cond_def matroid_intersection_recurse_cond_def Let_def
  apply(cases "compute_graph (sol state) (complement (sol state))")
  subgoal for a b c
    by(cases "find_path a b c") auto
  done

lemma matroid_intersection_simps:
  assumes "matroid_intersection_dom state"
  shows "matroid_intersection_terminates_cond state \<Longrightarrow> matroid_intersection state = state"
    "matroid_intersection_recurse_cond state \<Longrightarrow>
           matroid_intersection state =
     matroid_intersection (matroid_intersection_recurse_upd state)"  
  by(auto intro:  P_of_matroid_intersection_recurseI matroid_intersection_terminates_condE 
      simp add: matroid_intersection.psimps[OF assms] 
      split: option.split prod.split)

lemma matroid_intersection_induct:
  assumes "matroid_intersection_dom state"
    "\<And> state. matroid_intersection_dom state  \<Longrightarrow>
                 (matroid_intersection_recurse_cond state
 \<Longrightarrow> P (matroid_intersection_recurse_upd state)) \<Longrightarrow> P state"
  shows   "P state"
  apply(rule matroid_intersection.pinduct[OF assms(1)])
  apply(rule assms(2)[simplified matroid_intersection_terminates_cond_def 
        matroid_intersection_recurse_cond_def matroid_intersection_recurse_upd_def])
  by(auto simp: Let_def split: list.splits option.splits if_splits)

partial_function (tailrec) matroid_intersection_impl::"'mset intersec_state \<Rightarrow> 'mset intersec_state" where
  "matroid_intersection_impl state =
 (let X = sol state; (SX, TX, graph) = compute_graph X (complement X) in
     (case find_path SX TX graph of 
          None \<Rightarrow> state |
          Some p \<Rightarrow> matroid_intersection_impl (state \<lparr> sol := augment X p \<rparr>)))"

lemma implementation_is_same:
  "matroid_intersection_dom state \<Longrightarrow> matroid_intersection_impl state = matroid_intersection state"
  apply(induction state rule: matroid_intersection.pinduct)
  apply(subst matroid_intersection_impl.simps)
  apply(subst matroid_intersection.psimps, simp)
  by(auto simp add: Let_def split: prod.split option.split)

definition "treat1_circuit y X init_map = 
           inner_fold_circuit X (\<lambda> x current_map.  graph.add_edge current_map x y )
                       init_map"

definition "treat2_circuit y X init_map = 
           inner_fold_circuit X (\<lambda> x current_map. graph.add_edge current_map y x)
                       init_map"

definition "compute_graph_circuit X E_without_X =
           outer_fold E_without_X (\<lambda> y (SX, TX, current_map). (
            let (SX, TX, current_map) = (if weak_orcl1 y X then (insert y SX, TX, current_map)
                                         else (SX, TX, treat1_circuit y (circuit1 y X) current_map));
                (SX, TX, current_map) = (if weak_orcl2 y X then (SX, insert y TX, current_map)
                                         else (SX, TX, treat2_circuit y (circuit2 y X) current_map))
            in (SX, TX, current_map))) 
           (vset_empty, vset_empty, empty)"

function (domintros) matroid_intersection_circuit::"'mset intersec_state \<Rightarrow> 'mset intersec_state"  where
  "matroid_intersection_circuit state =
 (let X = sol state; (SX, TX, graph) = compute_graph_circuit X (complement X) in
     (case find_path SX TX graph of 
          None \<Rightarrow> state |
          Some p \<Rightarrow> matroid_intersection_circuit (state \<lparr> sol := augment X p\<rparr>)))"
  by pat_completeness auto

definition "matroid_intersection_circuit_recurse_cond state =
(let X = sol state; (SX, TX, graph) = compute_graph_circuit X (complement X) in
     (case find_path SX TX graph of 
          None \<Rightarrow> False |
          Some p \<Rightarrow> True))"

lemma matroid_intersection_circuit_recurse_condE:
  "matroid_intersection_circuit_recurse_cond state \<Longrightarrow>
 (\<And> SX TX graph p X. X = sol state \<Longrightarrow>  compute_graph_circuit X (complement X) = (SX, TX, graph) ==>
         find_path SX TX graph = Some p \<Longrightarrow> P) ==> P"
  by(force simp add: matroid_intersection_circuit_recurse_cond_def Let_def)

definition "matroid_intersection_circuit_recurse_upd state =
(let X = sol state; (SX, TX, graph) = compute_graph_circuit X (complement X) in
     state \<lparr> sol := augment X(the ( find_path SX TX graph ))\<rparr>)"

lemma P_of_matroid_intersection_circuit_recurseI:
  "matroid_intersection_circuit_recurse_cond state \<Longrightarrow> (\<And> SX TX graph p X. 
        X = sol state \<Longrightarrow> compute_graph_circuit X (complement X) = (SX, TX, graph) ==>
         find_path SX TX graph = Some p \<Longrightarrow> P (state \<lparr> sol := augment X p\<rparr>))
              ==> P (matroid_intersection_circuit_recurse_upd state)"
  unfolding matroid_intersection_circuit_recurse_cond_def
    matroid_intersection_circuit_recurse_upd_def Let_def 
  apply(cases "compute_graph_circuit (sol state) (complement (sol state))", simp)
  subgoal for a b c
    by(cases "find_path a b c") auto
  done

definition "matroid_intersection_circuit_terminates_cond state =
(let X = sol state; (SX, TX, graph) = compute_graph_circuit X (complement X) in
     (case find_path SX TX graph of 
          None \<Rightarrow> True |
          Some p \<Rightarrow> False))"

lemma matroid_intersection_circuit_terminates_condE:
  "matroid_intersection_circuit_terminates_cond state \<Longrightarrow>
 (\<And> SX TX graph X. X = sol state \<Longrightarrow>
           compute_graph_circuit X (complement X) = (SX, TX, graph) ==>
         find_path SX TX graph = None \<Longrightarrow> P) ==> P"
  by(force simp add: matroid_intersection_circuit_terminates_cond_def Let_def)

lemma matroid_intersection_circuit_cases:
  "(matroid_intersection_circuit_terminates_cond state \<Longrightarrow> P) \<Longrightarrow>
 (matroid_intersection_circuit_recurse_cond state \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding matroid_intersection_circuit_terminates_cond_def 
    matroid_intersection_circuit_recurse_cond_def Let_def
  apply(cases "compute_graph_circuit (sol state) (complement (sol state))")
  subgoal for a b c
    by(cases "find_path a b c") auto
  done

lemma matroid_intersection_circuit_simps:
  assumes "matroid_intersection_circuit_dom state"
  shows "matroid_intersection_circuit_terminates_cond state
                 \<Longrightarrow> matroid_intersection_circuit state = state"
    "matroid_intersection_circuit_recurse_cond state \<Longrightarrow>
           matroid_intersection_circuit state = matroid_intersection_circuit
           (matroid_intersection_circuit_recurse_upd state)"  
  by(auto intro:  P_of_matroid_intersection_circuit_recurseI matroid_intersection_circuit_terminates_condE 
      simp add: matroid_intersection_circuit.psimps[OF assms] 
      split: option.split prod.split)

lemma matroid_intersection_circuit_induct:
  assumes "matroid_intersection_circuit_dom state"
    "\<And> state. matroid_intersection_circuit_dom state  \<Longrightarrow>
                 (matroid_intersection_circuit_recurse_cond state
               \<Longrightarrow> P (matroid_intersection_circuit_recurse_upd state)) \<Longrightarrow> P state"
  shows   "P state"
  apply(rule matroid_intersection_circuit.pinduct[OF assms(1)])
  apply(rule assms(2)[simplified matroid_intersection_circuit_terminates_cond_def 
        matroid_intersection_circuit_recurse_cond_def matroid_intersection_circuit_recurse_upd_def])
  by(auto simp: Let_def split: list.splits option.splits if_splits)

partial_function (tailrec) matroid_intersection_circuit_impl::"'mset intersec_state\<Rightarrow> 'mset intersec_state" where
  "matroid_intersection_circuit_impl state =
 (let X = sol state; (SX, TX, graph) = compute_graph_circuit X (complement X) in
     (case find_path SX TX graph of 
          None \<Rightarrow> state |
          Some p \<Rightarrow> matroid_intersection_circuit_impl (state \<lparr> sol := augment X p\<rparr>)))"

lemma implementation_circuit_is_same:
  "matroid_intersection_circuit_dom state
    \<Longrightarrow> matroid_intersection_circuit_impl state = matroid_intersection_circuit state"
  apply(induction state rule: matroid_intersection_circuit.pinduct)
  apply(subst matroid_intersection_circuit_impl.simps)
  apply(subst matroid_intersection_circuit.psimps, simp)
  by(auto simp add: Let_def split: prod.split option.split)

definition "initial_state = \<lparr> sol= set_empty \<rparr>"

lemmas [code] = matroid_intersection_impl.simps matroid_intersection_circuit_impl.simps
  treat1_def treat2_def treat1_circuit_def treat2_circuit_def
  compute_graph_def compute_graph_circuit_def augment.simps
  graph.add_edge_def initial_state_def
end

locale unweighted_intersection =
  unweighted_intersection_spec
  where insert = "insert::'a \<Rightarrow> 'vset \<Rightarrow> 'vset"
    and lookup="lookup :: 'adjmap \<Rightarrow> 'a \<Rightarrow> 'vset option"
    and set_insert = "set_insert::'a \<Rightarrow> 'mset \<Rightarrow> 'mset"
    and find_path = "find_path::'vset \<Rightarrow> 'vset \<Rightarrow> 'adjmap \<Rightarrow> 'a list option"
    and t_set = vset 
    and complement = "complement::'mset \<Rightarrow> 'mset_red"
    + double_matroid 
  where carrier = "carrier::'a set"
  for insert lookup set_insert find_path carrier vset complement+
  fixes to_set_red::"'mset_red \<Rightarrow> 'a set"
    and   set_invar_red::"'mset_red \<Rightarrow> bool"
  assumes set_insert: "\<And> S x. \<lbrakk>set_invar S; x \<in> carrier\<rbrakk> \<Longrightarrow> set_invar (set_insert x S)"
    "\<And> S x. \<lbrakk>set_invar S; x \<in> carrier\<rbrakk> \<Longrightarrow> to_set (set_insert x S) = Set.insert x (to_set S)"
  assumes set_delete: "\<And> S x. \<lbrakk>set_invar S; x \<in> carrier\<rbrakk> \<Longrightarrow> set_invar (set_delete x S)"
    "\<And> S x. \<lbrakk>set_invar S; x \<in> carrier\<rbrakk> \<Longrightarrow> to_set (set_delete x S) = (to_set S) - {x}"
  assumes set_empty: "set_invar set_empty" "to_set set_empty = {}"
  assumes weak_orcl1: 
    "\<And> X x. \<lbrakk>set_invar X; to_set X \<subseteq> carrier; x \<in> carrier; x \<notin> to_set X; indep1 (to_set X)\<rbrakk>
       \<Longrightarrow> weak_orcl1 x X \<longleftrightarrow> indep1 (Set.insert x (to_set X))"
  assumes weak_orcl2: 
    "\<And> X x. \<lbrakk>set_invar X; to_set X \<subseteq> carrier; x \<in> carrier; x \<notin> to_set X; indep2 (to_set X)\<rbrakk> 
       \<Longrightarrow> weak_orcl2 x X \<longleftrightarrow> indep2 (Set.insert x (to_set X))"
  assumes inner_fold: 
     "\<And> X f G. set_invar X \<Longrightarrow> \<exists> xs. set xs = to_set X \<and> inner_fold X f G = foldr f xs G"
  assumes inner_fold_circuit: 
     "\<And> X f G. set_invar_red X 
      \<Longrightarrow> \<exists> xs. set xs = to_set_red X \<and> inner_fold_circuit X f G = foldr f xs G"
  assumes outer_fold: 
     "\<And> X f trip. set_invar_red X \<Longrightarrow> \<exists> xs. set xs = to_set_red X
                                           \<and> outer_fold X f trip = foldr f xs trip"
  assumes find_path: 
    "\<And> G S T. \<lbrakk>graph.graph_inv G; graph.finite_graph G; graph.finite_vsets G; vset_inv S;
               vset_inv T; vset S \<subseteq> carrier; vset T \<subseteq> carrier; dVs (graph.digraph_abs G) \<subseteq> carrier\<rbrakk>
      \<Longrightarrow> find_path S T G = None \<longleftrightarrow> 
           (\<nexists> p u v. (vwalk_bet (graph.digraph_abs G) u p v \<or> (p = [u] \<and> u = v)) \<and>
                       u \<in> vset S \<and> v \<in> vset T)"
    "\<And> G S T p. \<lbrakk>graph.graph_inv G; graph.finite_graph G; graph.finite_vsets G; vset_inv S; 
                 vset_inv T; vset S \<subseteq> carrier; vset T \<subseteq> carrier;
                 dVs (graph.digraph_abs G) \<subseteq> carrier; find_path S T G = Some p\<rbrakk>
      \<Longrightarrow> \<exists> u v. (vwalk_bet (graph.digraph_abs G) u p v \<or> (p = [u] \<and> u = v))
                         \<and> u \<in> vset S \<and> v \<in> vset T \<and>
             (\<nexists> p'. (vwalk_bet (graph.digraph_abs G) u p' v \<or> (p' = [u] \<and> u = v))
                         \<and> length p' < length p)"
  assumes complement: "\<And> S. \<lbrakk>set_invar S; to_set S  \<subseteq> carrier\<rbrakk> \<Longrightarrow> set_invar_red (complement S)"
    "\<And> S. \<lbrakk>set_invar S; to_set S  \<subseteq> carrier\<rbrakk> \<Longrightarrow> to_set_red (complement S) = carrier - to_set S"
  assumes circuit1: 
    "\<And> X y. \<lbrakk>set_invar X; indep1 (to_set X); to_set X \<subseteq> carrier; y \<in> carrier;
             \<not> indep1 (Set.insert y (to_set X))\<rbrakk>
        \<Longrightarrow> to_set_red (circuit1 y X) = matroid1.the_circuit (Set.insert y (to_set X)) - {y}"
    "\<And> X y. \<lbrakk>set_invar X; indep1 (to_set X); to_set X \<subseteq> carrier; y \<in> carrier;
              \<not> indep1 (Set.insert y (to_set X))\<rbrakk>
        \<Longrightarrow> set_invar_red (circuit1 y X)"
  assumes circuit2: 
    "\<And> X y. \<lbrakk>set_invar X; indep2 (to_set X); to_set X \<subseteq> carrier; y \<in> carrier;
              \<not> indep2 (Set.insert y (to_set X))\<rbrakk>
        \<Longrightarrow> to_set_red (circuit2 y X) = matroid2.the_circuit (Set.insert y (to_set X)) - {y}"
    "\<And> X y. \<lbrakk>set_invar X; indep2 (to_set X); to_set X \<subseteq> carrier; y \<in> carrier;
              \<not> indep2 (Set.insert y (to_set X))\<rbrakk> 
        \<Longrightarrow> set_invar_red (circuit2 y X)"
begin

lemma treat1_correct:
  assumes "indep1 (to_set X)" "set_invar X" "y \<in> carrier - to_set X" "graph.graph_inv G"
  shows "graph.graph_inv (treat1 y X G)"
    "graph.digraph_abs (treat1 y X G) = graph.digraph_abs G \<union>
                       {(x, y) | x. x \<in> to_set X \<and> indep1 (to_set X - {x} \<union> {y})}"
    "graph.finite_graph G \<Longrightarrow> graph.finite_graph (treat1 y X G)"
    "graph.finite_vsets G \<Longrightarrow> graph.finite_vsets (treat1 y X G)"
proof-
  define f where "f = (\<lambda> x current_map. if weak_orcl1 y (set_delete x X) 
                                         then graph.add_edge current_map x y 
                                         else current_map)"
  obtain xs where xs_prop: "set xs = to_set X" True "inner_fold X f G = foldr f xs G"
    using inner_fold[OF assms(2), of f G] by auto
  have treat_is: "treat1 y X G = foldr f xs G"
    by(unfold xs_prop(3)[symmetric])(simp add: treat1_def f_def)
  have claim1:"graph.graph_inv (foldr f xs G)" for xs
    by(induction xs)(auto split: if_split simp add: f_def assms(4))
  thus "graph.graph_inv (treat1 y X G)"
    by (simp add: treat_is)
  have X_in_Carrier: "to_set X \<subseteq> carrier "
    by (simp add: assms(1) matroid1.indep_subset_carrier)
  have independence_is:"a \<in> to_set X \<Longrightarrow> 
          weak_orcl1 y (set_delete a X) = indep1 (Set.insert y (to_set X - {a}))" for a
    using X_in_Carrier  assms(1) matroid1.indep_in_subset set_delete(2)[OF  assms(2)] 
      matroid1.indep_in_carrier assms(3)
    by (subst weak_orcl1)
      (fastforce simp add: weak_orcl1 assms(3) assms(2) set_delete(1) subset_eq)+
  have "set xs \<subseteq> to_set X  \<Longrightarrow>graph.digraph_abs (foldr f xs G) = graph.digraph_abs G \<union>
                       {(x, y) | x. x \<in> set xs \<and> indep1 (to_set X - {x} \<union> {y})}"
    using xs_prop(2) 
    apply(induction xs, simp)
    apply(subst foldr_Cons, subst o_apply)
    apply(subst f_def)
    by(auto simp add: independence_is graph.digraph_abs_insert[OF claim1])
  thus "[treat1 y X G]\<^sub>g = [G]\<^sub>g \<union> {(x, y) |x. x \<in> to_set X \<and> indep1 (to_set X - {x} \<union> {y})}"
    by(simp add: treat_is xs_prop(1))
  have "set xs \<subseteq> to_set X \<Longrightarrow> graph.finite_graph G \<Longrightarrow> graph.finite_graph (foldr f xs G)"
    apply(induction xs, simp)
    apply(subst foldr_Cons, subst o_apply)
    apply(subst f_def)
    by(auto simp add: independence_is claim1 graph.finite_graph_add_edge)
  thus "graph.finite_graph G \<Longrightarrow> graph.finite_graph (treat1 y X G)" 
    by (simp add: treat_is xs_prop(1))
  have "set xs \<subseteq> to_set X \<Longrightarrow> graph.finite_vsets G \<Longrightarrow> graph.finite_vsets (foldr f xs G)"
    apply(induction xs, simp)
    apply(subst foldr_Cons, subst o_apply)
    apply(subst f_def)
    by(auto simp add: independence_is claim1 graph.finite_vsets_add_edge)
  thus "graph.finite_vsets G \<Longrightarrow> graph.finite_vsets (treat1 y X G)" 
    by (simp add: treat_is xs_prop(1))
qed

lemma treat2_correct:
  assumes "indep2 (to_set X)" "set_invar X" "y \<in> carrier - to_set X" "graph.graph_inv G"
  shows "graph.graph_inv (treat2 y X G)"
    "graph.digraph_abs (treat2 y X G) = graph.digraph_abs G \<union>
                       {(y, x) | x. x \<in> to_set X \<and> indep2 (to_set X - {x} \<union> {y})}"
    "graph.finite_graph G \<Longrightarrow> graph.finite_graph (treat2 y X G)"
    "graph.finite_vsets G \<Longrightarrow> graph.finite_vsets (treat2 y X G)"
proof-
  define f where "f = (\<lambda> x current_map. if weak_orcl2 y (set_delete x X) 
                                         then graph.add_edge current_map y x 
                                         else current_map)"
  obtain xs where xs_prop: "set xs = to_set X" True "inner_fold X f G = foldr f xs G"
    using inner_fold[OF assms(2), of f G] by auto
  have treat_is: "treat2 y X G = foldr f xs G"
    by(unfold xs_prop(3)[symmetric])(simp add: treat2_def f_def)
  have claim1:"graph.graph_inv (foldr f xs G)" for xs
    by(induction xs)(auto split: if_split simp add: f_def assms(4))
  thus "graph.graph_inv (treat2 y X G)"
    by (simp add: treat_is)
  have X_in_Carrier: "to_set X \<subseteq> carrier"
    by (simp add: assms(1) matroid2.indep_subset_carrier)
  have independence_is:"a \<in> to_set X \<Longrightarrow> 
          weak_orcl2 y (set_delete a X) = indep2 (Set.insert y (to_set X - {a}))" for a
    using X_in_Carrier  assms(1) matroid2.indep_in_subset set_delete(2)[OF  assms(2)] 
      matroid2.indep_in_carrier assms(3)
    by (subst weak_orcl2)
      (fastforce simp add: weak_orcl1 assms(3) assms(2) set_delete(1) subset_eq)+
  have "set xs \<subseteq> to_set X  \<Longrightarrow>graph.digraph_abs (foldr f xs G) = graph.digraph_abs G \<union>
                       {(y, x) | x. x \<in> set xs \<and> indep2 (to_set X - {x} \<union> {y})}"
    using xs_prop(2) 
    apply(induction xs, simp)
    apply(subst foldr_Cons, subst o_apply)
    apply(subst f_def)
    by(auto simp add: independence_is graph.digraph_abs_insert[OF claim1])
  thus "[treat2 y X G]\<^sub>g = [G]\<^sub>g \<union> {(y, x) |x. x \<in> to_set X \<and> indep2 (to_set X - {x} \<union> {y})}"
    by(simp add: treat_is xs_prop(1))
  have "set xs \<subseteq> to_set X \<Longrightarrow> graph.finite_graph G \<Longrightarrow> graph.finite_graph (foldr f xs G)"
    apply(induction xs, simp)
    apply(subst foldr_Cons, subst o_apply)
    apply(subst f_def)
    by(auto simp add: independence_is claim1 graph.finite_graph_add_edge)
  thus "graph.finite_graph G \<Longrightarrow> graph.finite_graph (treat2 y X G)" 
    by (simp add: treat_is xs_prop(1))
  have "set xs \<subseteq> to_set X \<Longrightarrow> graph.finite_vsets G \<Longrightarrow> graph.finite_vsets (foldr f xs G)"
    apply(induction xs, simp)
    apply(subst foldr_Cons, subst o_apply)
    apply(subst f_def)
    by(auto simp add: independence_is claim1 graph.finite_vsets_add_edge)
  thus "graph.finite_vsets G \<Longrightarrow> graph.finite_vsets (treat2 y X G)" 
    by (simp add: treat_is xs_prop(1))
qed

lemma compute_graph_correct:
  assumes "indep1 (to_set X)" "indep2 (to_set X)" "set_invar X " 
    "set_invar_red E_without_X" "to_set_red E_without_X \<subseteq> carrier  - to_set X"
    "compute_graph X E_without_X = (SX, TX, resulting_map)"
  shows   "vset_inv SX" "vset_inv TX" "graph.graph_inv resulting_map" 
          "graph.finite_graph resulting_map"
    "vset SX = {y | y. y \<in> to_set_red E_without_X \<and> indep1 (Set.insert y (to_set X))}"
    "vset TX = {y | y. y \<in> to_set_red E_without_X \<and> indep2 (Set.insert y (to_set X))}"
    and "graph.digraph_abs resulting_map = 
                {(x, y) |x y. y \<in> to_set_red E_without_X \<and> \<not> indep1 (Set.insert y (to_set X)) 
                                          \<and> x \<in> to_set X \<and> indep1 (to_set X - {x} \<union> {y})}
                \<union> {(y, x) |x y. y \<in> to_set_red E_without_X \<and> \<not> indep2 (Set.insert y (to_set X)) \<and> 
                                             x \<in> to_set X \<and> indep2 (to_set X - {x} \<union> {y})}"
    (is ?last_thesis)
    and "graph.finite_vsets resulting_map"
proof-
  define f where "f = (\<lambda> y (SX, TX, current_map). (
            let (SX, TX, current_map) = (if weak_orcl1 y X then (insert y SX, TX, current_map)
                                         else (SX, TX, treat1 y X current_map));
                (SX, TX, current_map) = (if weak_orcl2 y X then (SX, insert y TX, current_map)
                                         else (SX, TX, treat2 y X current_map))
            in (SX, TX, current_map)))"
  obtain xs where xs_prop: "set xs = to_set_red E_without_X" True
    "outer_fold E_without_X f (\<emptyset>\<^sub>N, \<emptyset>\<^sub>N, \<emptyset>\<^sub>G) = foldr f xs (\<emptyset>\<^sub>N, \<emptyset>\<^sub>N, \<emptyset>\<^sub>G)"
    using outer_fold[OF assms(4), of f "(vset_empty, vset_empty, empty)"] by auto
  have SX_is: "SX = fst (foldr f xs (\<emptyset>\<^sub>N, \<emptyset>\<^sub>N, \<emptyset>\<^sub>G))"
    using assms(6) xs_prop(3)[symmetric]
    by(auto simp add: f_def compute_graph_def)
  have TX_is: "TX = fst (snd (foldr f xs (\<emptyset>\<^sub>N, \<emptyset>\<^sub>N, \<emptyset>\<^sub>G)))"
    using assms(6) xs_prop(3)[symmetric]
    by(auto simp add: f_def compute_graph_def)
  have resulting_map_is: "resulting_map = snd (snd (foldr f xs (\<emptyset>\<^sub>N, \<emptyset>\<^sub>N, \<emptyset>\<^sub>G)))"
    using assms(6) xs_prop(3)[symmetric]
    by(auto simp add: f_def compute_graph_def)
  have vset_inv_SX:"vset_inv (fst (foldr f xs (\<emptyset>\<^sub>N, \<emptyset>\<^sub>N, \<emptyset>\<^sub>G)))" for xs
    by(induction xs)
      (auto split: prod.split intro: graph.vset.set.invar_insert simp add: f_def graph.vset.set.invar_empty)
  thus "vset_inv SX"
    using SX_is by fastforce
  have vset_inv_TX:"vset_inv (fst (snd (foldr f xs (\<emptyset>\<^sub>N, \<emptyset>\<^sub>N, \<emptyset>\<^sub>G))))" for xs
    by(induction xs)
      (auto split: prod.split intro: graph.vset.set.invar_insert simp add: f_def graph.vset.set.invar_empty)
  thus "vset_inv TX"
    using TX_is by fastforce 
  have graph_inv_resulting_map:
    "set xs \<subseteq> carrier - to_set X \<Longrightarrow> graph.graph_inv (snd (snd (foldr f xs (\<emptyset>\<^sub>N, \<emptyset>\<^sub>N, \<emptyset>\<^sub>G))))" for xs
    by(induction xs)
      (auto split: prod.split 
        intro!: treat1_correct(1)[OF assms(1,3)] treat2_correct(1)[OF assms(2,3)]
        simp add: f_def graph.graph_inv_empty)
  thus "graph.graph_inv resulting_map"
    by (simp add: assms(5) resulting_map_is xs_prop(1))
  have X_in_carrier:"to_set X \<subseteq> carrier"
    by (simp add: assms(1) matroid1.indep_subset_carrier)
  have "set xs \<subseteq> carrier - to_set X \<Longrightarrow> vset (fst (foldr f xs (\<emptyset>\<^sub>N, \<emptyset>\<^sub>N, \<emptyset>\<^sub>G))) = 
           {y |y. y \<in> set xs \<and> indep1 (Set.insert y (to_set X))}"
  proof(induction xs)
    case (Cons a xs)
    show ?case
    proof(subst foldr_Cons, subst o_apply, subst f_def, unfold Let_def,
        (split prod.split, rule, rule, rule)+, goal_cases)
      case (1 x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e)
      then show ?case 
        using Cons  vset_inv_SX[of xs]  graph.vset.set.set_insert
          weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
        by (cases "weak_orcl1 a X", all \<open>cases "weak_orcl2 a X"\<close>) auto
    qed
  qed(auto simp add: graph.vset.emptyD(3))
  thus "vset SX = {y |y. y \<in> to_set_red E_without_X \<and> indep1 (Set.insert y (to_set X))}"
    using SX_is assms(5) xs_prop(1) by presburger
  have "set xs \<subseteq> carrier -to_set X \<Longrightarrow> vset (fst (snd (foldr f xs (\<emptyset>\<^sub>N, \<emptyset>\<^sub>N, \<emptyset>\<^sub>G)))) = 
           {y |y. y \<in> set xs \<and> indep2 (Set.insert y (to_set X))}"
  proof(induction xs)
    case (Cons a xs)
    show ?case
    proof(subst foldr_Cons, subst o_apply, subst f_def, unfold Let_def,
        (split prod.split, rule, rule, rule)+, goal_cases)
      case (1 x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e)
      then show ?case 
        using Cons  vset_inv_TX[of xs]  graph.vset.set.set_insert
          weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
        by (cases "weak_orcl1 a X", all \<open>cases "weak_orcl2 a X"\<close>) auto
    qed
  qed(auto simp add: graph.vset.emptyD(3))
  thus "vset TX = {y |y. y \<in> to_set_red E_without_X \<and> indep2 (Set.insert y (to_set X))}"
    using TX_is assms(5) xs_prop(1) by presburger
  have "set xs \<subseteq> carrier - to_set X \<Longrightarrow> graph.digraph_abs (snd (snd (foldr f xs (\<emptyset>\<^sub>N, \<emptyset>\<^sub>N, \<emptyset>\<^sub>G)))) =  
           {(x, y) |x y.
     y \<in> set xs \<and>
     \<not> indep1 (Set.insert y (to_set X)) \<and> x \<in> to_set X \<and> indep1 (to_set X - {x} \<union> {y})} \<union>
    {(y, x) |x y.
     y \<in> set xs \<and> \<not> indep2 (Set.insert y (to_set X)) \<and> x \<in> to_set X \<and> indep2 (to_set X - {x} \<union> {y})}"
  proof(induction xs)
    case (Cons a xs)
    show ?case
    proof(subst foldr_Cons, subst o_apply, subst f_def, unfold Let_def,
        (split prod.split, rule, rule, rule)+, goal_cases)
      case (1 x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e)
      then show ?case 
      proof(cases "weak_orcl1 a X", all \<open>cases "weak_orcl2 a X"\<close>, goal_cases)
        case 1
        then show ?case 
          using Cons  weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)] 
            weak_orcl2[OF assms(3) X_in_carrier _  _ assms(2)]
          by auto
      next
        case 2
        then show ?case 
          using  graph_inv_resulting_map  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)] 
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)] 
          by (clarsimp, subst treat2_correct(2)[OF assms(2,3)])force+
      next
        case 3
        then show ?case 
          using  graph_inv_resulting_map  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)] 
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)] 
          by (clarsimp, subst treat1_correct(2)[OF assms(1,3)])force+
      next
        case 4
        then show ?case
          using Cons.prems
          apply(clarsimp, subst treat2_correct(2)[OF assms(2,3)], simp)
           apply(rule treat1_correct(1)[OF assms(1,3)])
          using graph_inv_resulting_map[of xs]  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)] 
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)] 
          by (subst treat1_correct(2)[OF assms(1,3)]|force)+
      qed
    qed
  qed (auto simp add:  graph.digraph_abs_empty)
  thus ?last_thesis
    using assms(5) resulting_map_is xs_prop(1) by presburger
  have "set xs  \<subseteq> carrier -to_set X \<Longrightarrow> graph.finite_graph (snd (snd (foldr f xs (\<emptyset>\<^sub>N, \<emptyset>\<^sub>N, \<emptyset>\<^sub>G))))"
  proof(induction xs)
    case (Cons a xs)
    show ?case
    proof(subst foldr_Cons, subst o_apply, subst f_def, unfold Let_def,
        (split prod.split, rule, rule, rule)+, goal_cases)
      case (1 x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e)
      then show ?case 
      proof(cases "weak_orcl1 a X", all \<open>cases "weak_orcl2 a X"\<close>, goal_cases)
        case 1
        then show ?case 
          using Cons  weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)] 
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
          by auto
      next
        case 2
        then show ?case 
          using  graph_inv_resulting_map  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)] 
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)] 
          by (clarsimp, subst treat2_correct(3)[OF assms(2,3)])force+
      next
        case 3
        then show ?case 
          using  graph_inv_resulting_map  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)] 
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)] 
          by (clarsimp, subst treat1_correct(3)[OF assms(1,3)])force+
      next
        case 4
        then show ?case
          using Cons.prems
          apply(clarsimp, subst treat2_correct(3)[OF assms(2,3)], simp)
            apply(rule treat1_correct(1)[OF assms(1,3)])
          using graph_inv_resulting_map[of xs]  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)] 
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)] 
          by (subst treat1_correct(3)[OF assms(1,3)]|force)+
      qed
    qed 
  qed (auto simp add: graph.adjmap.map_empty graph.finite_graph_def)
  thus "graph.finite_graph resulting_map"
    using  resulting_map_is xs_prop(1)  assms(5) by blast
  have "set xs  \<subseteq> carrier -to_set X \<Longrightarrow> graph.finite_vsets (snd (snd (foldr f xs (\<emptyset>\<^sub>N, \<emptyset>\<^sub>N, \<emptyset>\<^sub>G))))"
  proof(induction xs)
    case (Cons a xs)
    show ?case
    proof(subst foldr_Cons, subst o_apply, subst f_def, unfold Let_def,
        (split prod.split, rule, rule, rule)+, goal_cases)
      case (1 x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e)
      then show ?case 
      proof(cases "weak_orcl1 a X", all \<open>cases "weak_orcl2 a X"\<close>, goal_cases)
        case 1
        then show ?case 
          using Cons  weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)] 
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
          by auto
      next
        case 2
        then show ?case 
          using  graph_inv_resulting_map  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)] 
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)] 
          by (clarsimp, subst treat2_correct(4)[OF assms(2,3)])force+
      next
        case 3
        then show ?case 
          using  graph_inv_resulting_map  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)] 
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)] 
          by (clarsimp, subst treat1_correct(4)[OF assms(1,3)])force+
      next
        case 4
        then show ?case
          using Cons.prems
          apply(clarsimp, subst treat2_correct(4)[OF assms(2,3)], simp)
            apply(rule treat1_correct(1)[OF assms(1,3)])
          using graph_inv_resulting_map[of xs]  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)] 
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)] 
          by (subst treat1_correct(4)[OF assms(1,3)]|force)+
      qed
    qed 
  qed (auto simp add: graph.adjmap.map_empty graph.finite_graph_def)
  thus "graph.finite_vsets resulting_map"
    using assms(5) resulting_map_is xs_prop(1) by force
qed

lemma compute_graph_meaning:
  assumes "indep1 (to_set X)" "indep2 (to_set X)" "set_invar X" 
    "set_invar_red E_without_X" "to_set_red E_without_X = carrier - to_set X"
    "compute_graph X E_without_X = (SX, TX, resulting_map)"
  shows   "vset SX = S (to_set X)"
    "vset TX = T (to_set X)"
    "graph.digraph_abs resulting_map = A1 (to_set X) \<union> A2 (to_set X)"
  subgoal
    using compute_graph_correct(5)[OF assms(1-4) _ assms(6)] assms(5)
    by (simp add: S_def)
  subgoal
    using compute_graph_correct(6)[OF assms(1-4) _ assms(6)] assms(5)
    by (simp add: T_def)
  subgoal 
    using matroid2.indep_subset_carrier[OF assms(2)]
    by(subst compute_graph_correct(7)[OF assms(1-4) _ assms(6)])
      (auto simp add: matroid1.circuit_extensional[OF assms(1)] insert_Diff_if
        matroid2.circuit_extensional[OF assms(2)] A1_def A2_def assms(5))
  done

lemma effect_of_augmentation:
  assumes "set_invar X" "to_set X \<subseteq> carrier" "set p \<subseteq> carrier" "distinct p"
    "X' = ((to_set X \<union> {p ! i | i. i < length p \<and> even i}) -  {p ! i | i. i < length p \<and> odd i})"
  shows "set_invar (augment X p)" "to_set (augment X p) = X'"
proof-
  have "set p \<subseteq> carrier \<Longrightarrow> set_invar (augment X p)" for p
    using  assms(1,2) 
  proof(induction p arbitrary: X rule: induct_list012)
    case (sucsuc x y zs)
    note 3 = this
    show ?case 
      using 3(2-) 
      by(auto intro!: 3(1) intro: set_insert set_delete simp add: set_insert set_delete)
  qed (auto simp add: intro: set_insert set_delete)
  thus "set_invar (augment X p)"
    by (simp add: assms(3))
  show "to_set (augment X p) = X'"
    using assms
  proof(induction p arbitrary: X X' rule: induct_list012)
    case (sucsuc x y zs)
    have same_set:"Set.insert x (to_set X - {y}) \<union> {zs ! i |i. i < length zs \<and> even i} - {zs ! i |i. i < length zs \<and> odd i} =
    to_set X \<union> {(x # y # zs) ! i |i. i < length (x # y # zs) \<and> even i} -
    {(x # y # zs) ! i |i. i < length (x # y # zs) \<and> odd i}"
      using  "sucsuc.prems"(4)  
      by (auto simp add: nth_eq_iff_index_eq less_Suc_eq_0_disj gr0_conv_Suc)
        (metis dvd_0_right nth_Cons_0  nth_Cons_Suc even_Suc)+
    have help1: "to_set (set_insert x (set_delete y X)) \<subseteq> carrier" 
      using "sucsuc.prems"(1-3) local.set_insert(2) set_delete(1) set_delete(2) by auto
    show ?case 
      using sucsuc(2-) same_set set_insert set_delete
      by (auto simp add:  sucsuc(1)[OF  _ help1 _ _ refl])
  qed (auto simp add: set_insert)
qed

definition "indep_invar state = (indep1 (to_set (sol state)) \<and> (indep2 (to_set (sol state))))"

lemma indep_invar_recurse_improvement:
  assumes "matroid_intersection_recurse_cond state" "indep_invar state"
    "set_invar (sol state)" "to_set (sol state) \<subseteq> carrier"
  shows   "indep_invar (matroid_intersection_recurse_upd state)"
    "set_invar (sol (matroid_intersection_recurse_upd state))" 
    "to_set (sol (matroid_intersection_recurse_upd state)) \<subseteq> carrier"
    "card (to_set (sol (matroid_intersection_recurse_upd state))) = 
          card (to_set (sol state)) + 1"
    "S (to_set (sol state)) \<noteq> {}"
    "T (to_set (sol state)) \<noteq> {}"
    and   "\<exists>u v p. (vwalk_bet (A1 (to_set (sol state)) \<union> A2 (to_set (sol state))) u p v \<or> (p = [u] \<and> u = v)) \<and>
           u \<in> S (to_set (sol state)) \<and>
           v \<in> T (to_set (sol state))" (is ?last_thesis)
proof(all \<open>rule P_of_matroid_intersection_recurseI[OF assms(1)]\<close>)
  fix SX TX graph p X
  assume 1: "compute_graph X (complement X) = (SX, TX, graph)"
    "find_path SX TX graph = Some p" "X = sol state"
  have Xincarrier: "to_set X \<subseteq> carrier"
    by (simp add: "1"(3) assms(4))
  have indep1X: "indep1 (to_set X)"
    using assms(2) 1(3) indep_invar_def by auto
  have indep2X: "indep2 (to_set X)" 
    using assms(2) 1(3) indep_invar_def by auto
  have complementInvar: "set_invar_red (complement X)" 
    using complement(1)[OF _ Xincarrier] assms(3) 1(3) by simp
  hence complement_is: "to_set_red (complement X) = carrier - to_set X"
    using "1"(3) assms(3,4) complement(2) by force
  hence complementcarrier: "to_set_red (complement X) \<subseteq> carrier - to_set X"
    by simp
  note compute_graph_correct = compute_graph_correct[OF indep1X indep2X _
      complementInvar complementcarrier 1(1)]
  note compute_graph_meaning = compute_graph_meaning
              [OF indep1X indep2X _ complementInvar complement_is 1(1)]
  have SXincarrier: "vset SX \<subseteq> carrier" 
    using S_in_carrier compute_graph_meaning(1) indep1X indep2X
    by (simp add: "1"(3) assms(3))
  have TXincarrier: "vset TX \<subseteq> carrier" 
    using T_in_carrier compute_graph_meaning(2) indep1X indep2X assms(3) 1(3) by auto
  have graphverticesincarrier: "dVs [graph]\<^sub>g \<subseteq> carrier" 
    using compute_graph_meaning(3) dVs_A1A2_carrier indep1X indep2X assms(3) 1(3) by simp
  have finite_vsets: "graph.finite_vsets graph" 
    using compute_graph_correct(8)
    by (simp add: "1"(3) assms(3))
  obtain u v where p_prop: "vwalk_bet [graph]\<^sub>g u p v \<or> (p = [u] \<and> u = v)"
    "u \<in> vset SX"
    "v \<in> vset TX"
    "(\<nexists>p'.
          (vwalk_bet [graph]\<^sub>g u p' v \<or> (p' = [u] \<and> u = v)) \<and> length p' < length p)"
    using find_path(2)[OF compute_graph_correct(3,4) finite_vsets compute_graph_correct(1,2) 
        SXincarrier TXincarrier graphverticesincarrier 1(2)] assms(3) 1(3)  by auto
  hence p_prop_extended: "vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p v \<or> (p = [u] \<and> u = v)" 
    "(\<nexists>p'.
          (vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p' v\<or> (p' = [u] \<and> u = v)) \<and> length p' < length p)"
    using compute_graph_meaning(3) p_prop(4) assms(3) 1(3) by auto
  have pincarrier:"set p \<subseteq> carrier"
    using p_prop(1-3)
    using graphverticesincarrier in_mono vwalk_bet_in_vertices[of "[graph]\<^sub>g" u p v] SXincarrier 
    by (auto simp add: vwalk_bet_def)
  have p_not_empty:"p \<noteq> []" 
    using p_prop(1) by(auto simp add:  vwalk_bet_def) 
  have distinctp:"distinct p"
  proof(rule ccontr, goal_cases)
    case 1
    then obtain p1 x p2 p3 where p_decomp:"p = p1@[x]@p2@[x]@p3"
      using not_distinct_decomp by blast
    moreover hence "length p \<ge> 2" by auto
    moreover hence "vwalk_bet [graph]\<^sub>g u p v"
      using p_prop(1) by(auto simp add: vwalk_bet_def)
    ultimately have "vwalk_bet [graph]\<^sub>g u (p1@[x]@p3) v"
      by (meson indep1X indep2X vwalk_bet_cycle_delete)
    moreover have "length (p1@[x]@p3)< length p"
      using p_decomp by simp
    ultimately show ?case
      using p_prop(2) p_prop(3) p_prop(4) by blast
  qed
  have indep_after_aug:"indep1 (to_set (augment X p))"
    using augment_in_matroid1_single[OF indep1X indep2X, of u]
      augment_in_matroid1[OF indep1X indep2X, of u p v] p_prop_extended compute_graph_meaning p_prop
    by(subst effect_of_augmentation(2)[OF  _  Xincarrier pincarrier  distinctp refl])
      (auto intro: vwalk_arcs.cases[of p] simp add: assms(3) 1(3) p_not_empty vwalk_bet_def)  
  moreover have "indep2 (to_set (augment X p))"
    using augment_in_matroid2_single[OF indep1X indep2X, of u]
      augment_in_matroid2[OF indep1X indep2X, of u p v] p_prop_extended compute_graph_meaning p_prop
    by(subst effect_of_augmentation(2)[OF _  Xincarrier pincarrier  distinctp refl])
      (auto intro: vwalk_arcs.cases[of p] simp add: assms(3) 1(3) p_not_empty vwalk_bet_def)  
  ultimately show "indep_invar (state \<lparr> sol := (augment X p) \<rparr>)"
    by(simp add: indep_invar_def)
  show "set_invar (sol (state \<lparr> sol := (augment X p)\<rparr>))"
    using Xincarrier assms(3) distinctp effect_of_augmentation(1) 1(3) pincarrier by simp
  show "to_set (sol (state \<lparr> sol :=(augment X p) \<rparr>)) \<subseteq> carrier"
    by (simp add: indep_after_aug matroid1.indep_subset_carrier)
  show "card (to_set (sol (state \<lparr> sol := (augment X p)\<rparr>))) 
             = card (to_set (sol state)) + 1"
    using augment_in_both_matroids_single(3)[OF indep1X indep2X, of u] 
      augment_in_both_matroids(3)[OF indep1X indep2X _ _ _ _ refl, of u p v]
      p_prop_extended compute_graph_meaning p_prop
    by(subst sol_remove, subst effect_of_augmentation(2)[OF  _  Xincarrier pincarrier  distinctp refl])
      (auto intro: vwalk_arcs.cases[of p] simp add: 1(3) assms(3) p_not_empty vwalk_bet_def)
  show ?last_thesis 
    using compute_graph_meaning p_prop p_prop_extended(1) assms(3) 1(3) by auto
  thus "S (to_set (sol state)) \<noteq> {}" "T (to_set (sol state)) \<noteq> {}" by auto
qed

lemma indep_invar_max_found:
  assumes "matroid_intersection_terminates_cond state" "indep_invar state"
    "set_invar (sol state)" "to_set (sol state) \<subseteq> carrier"
  shows   "is_max (to_set (sol state))"
proof(rule matroid_intersection_terminates_condE[OF assms(1)])
  fix SX TX graph p X
  assume 1: "compute_graph X (complement X) = (SX, TX, graph)"
    "find_path SX TX graph = None" "X = sol state"
  have Xincarrier: "to_set X \<subseteq> carrier"
    by (simp add: assms(4) 1(3))
  have indep1X: "indep1 (to_set X)"
    using assms(2) indep_invar_def 1(3)  by auto
  have indep2X: "indep2 (to_set X)" 
    using assms(2) indep_invar_def 1(3) by auto
  have complementInvar: "set_invar_red (complement X)" 
    using complement(1)[OF _ Xincarrier] assms(3) 1(3) by simp
  hence complement_is: "to_set_red (complement X) = carrier - to_set X"
    using Xincarrier assms(3) 1(3) complement(2) by auto
  hence complementcarrier: "to_set_red (complement X) \<subseteq> carrier - to_set X"
    by simp
  note compute_graph_correct = compute_graph_correct[OF indep1X indep2X _ 
      complementInvar complementcarrier 1(1)]
  note compute_graph_meaning = compute_graph_meaning[OF indep1X indep2X _ complementInvar complement_is 1(1)]
  have SXincarrier: "vset SX \<subseteq> carrier" 
    using S_in_carrier compute_graph_meaning(1) indep1X indep2X 1(3) assms(3) by auto
  have TXincarrier: "vset TX \<subseteq> carrier" 
    using T_in_carrier compute_graph_meaning(2) indep1X indep2X 1(3) assms(3) by auto
  have graphverticesincarrier: "dVs [graph]\<^sub>g \<subseteq> carrier" 
    using compute_graph_meaning(3) dVs_A1A2_carrier indep1X indep2X 1(3) assms(3) by simp
  have finite_vsets: "graph.finite_vsets graph" 
    by (simp add: "1"(3) assms(3) compute_graph_correct(8))
  have no_path: "(\<nexists>p u v. (vwalk_bet [graph]\<^sub>g u p v \<or> (p = [u] \<and> u = v)) \<and> u \<in> vset SX \<and> v \<in> vset TX)"
    using find_path(1)[OF compute_graph_correct(3,4) finite_vsets compute_graph_correct(1,2) 
        SXincarrier TXincarrier graphverticesincarrier ] 1(2,3) assms(3) by auto
  hence "\<nexists>p x y. x \<in> S (to_set X) \<and> y \<in> T (to_set X) \<and> (vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) x p y \<or> x = y)"
    using compute_graph_meaning(1) compute_graph_meaning(2) compute_graph_meaning(3) assms(3) 1(3) 
    by (auto simp add:  vwalk_bet_def)
  thus  "is_max (to_set (sol state))"
    using if_no_augpath_then_maximum(1)[OF indep1X indep2X _ refl]
      indep1X indep2X 1(3) assms(3) by(auto simp add: is_max_def)
qed

lemma matroid_intersection_terminates_general:
  assumes  "indep_invar state" "set_invar (sol state)" "to_set (sol state) \<subseteq> carrier"
    "m = card carrier - card (to_set (sol state))"
  shows    "matroid_intersection_dom state"
  using assms
proof(induction m arbitrary: state)
  case 0
  hence X_is_carrier:"to_set (sol state) = carrier" 
    by (simp add: card_seteq matroid2.carrier_finite)
  show ?case 
  proof(cases state rule: matroid_intersection_cases)
    case 1
    show ?thesis 
      by(rule matroid_intersection_terminates_condE[OF 1])
        (auto intro: matroid_intersection.domintros)
  next
    case 2
    have "S (to_set (sol state)) \<noteq> {}" "T (to_set (sol state)) \<noteq> {}"
      using indep_invar_recurse_improvement(7)[OF 2 0(1,2,3)] by auto
    moreover have  "S (to_set (sol state)) = {}"
      by(simp add: X_is_carrier  S_def)
    ultimately show ?thesis by simp
  qed
next
  case (Suc m)
  show ?case  
  proof(cases state rule: matroid_intersection_cases)
    case 1
    show ?thesis 
      by(rule matroid_intersection_terminates_condE[OF 1])
        (auto intro: matroid_intersection.domintros)
  next
    case 2
    show ?thesis
    proof(rule matroid_intersection_recurse_condE[OF 2], goal_cases)
      case (1 SX TX graph p X)
      have helper:"indep1 (to_set (augment X p))" "indep2 (to_set (augment X p))" 
               "set_invar (augment X p)"  "to_set (augment X p) \<subseteq> carrier"
        using 1 2  indep_invar_recurse_improvement[OF 2 Suc.prems(1,2,3)] 
        by(auto simp add: matroid_intersection_recurse_upd_def indep_invar_def)
      have card_decrease: "m = card carrier - card (to_set (augment X p))"
        using 1 2 Suc.prems(4) indep_invar_recurse_improvement[OF 2 Suc.prems(1,2,3)] 
        by(auto simp add: matroid_intersection_recurse_upd_def)
      show ?case 
        apply(rule matroid_intersection.domintros)
        using helper 1 card_decrease
        by (auto intro!: Suc(1) simp add: indep_invar_def)
    qed
  qed
qed

lemma matroid_intersection_correctness_general:
  assumes "indep_invar state" "set_invar (sol state)" "to_set (sol state) \<subseteq> carrier"
  shows "is_max (to_set (sol (matroid_intersection state)))"
  using assms
proof(induction state rule: matroid_intersection_induct)
  case 1
  then show ?case 
    using matroid_intersection_terminates_general[OF assms refl] by simp
next
  case (2 state)
  note IH = this
  show ?case 
  proof(cases state rule: matroid_intersection_cases)
    case 1
    then show ?thesis 
      by (simp add: "2.hyps" "2.prems" indep_invar_max_found matroid_intersection_simps(1))
  next
    case 2
    show ?thesis 
      apply(subst matroid_intersection_simps(2)[OF IH(1) 2])+
      apply(rule IH(2)[OF 2])
      by(auto simp add: "2" IH(3-) indep_invar_recurse_improvement)
  qed
qed

lemma matroid_intersection_correctness:
  "indep_invar (matroid_intersection initial_state)"
  "is_max (to_set (sol (matroid_intersection initial_state)))"
  using matroid_intersection_correctness_general
  by(simp add: indep_invar_def initial_state_def is_max_def local.set_empty(1) local.set_empty(2))+

lemma matroid_intersection_termiantes: "matroid_intersection_dom initial_state"
  by(rule matroid_intersection_terminates_general)
    (auto simp add: indep_invar_def set_empty initial_state_def)

lemma matroid_intersection_total_correctness:
  "is_max (to_set (sol (matroid_intersection initial_state)))"
  "matroid_intersection_dom initial_state"
  using matroid_intersection_correctness matroid_intersection_termiantes by auto

lemma treat1_circuit_correct:
  assumes "set_invar_red X" "graph.graph_inv G"
  shows "graph.graph_inv (treat1_circuit y X G)"
    "graph.digraph_abs (treat1_circuit y X G) = graph.digraph_abs G \<union>
                       {(x, y) | x. x \<in> to_set_red X}"
    "graph.finite_graph G \<Longrightarrow> graph.finite_graph (treat1_circuit y X G)"
    "graph.finite_vsets G \<Longrightarrow> graph.finite_vsets (treat1_circuit y X G)"
proof-
  define f where "f = (\<lambda> x current_map.  graph.add_edge current_map x y)"
  obtain xs where xs_prop: "set xs = to_set_red X" True "inner_fold_circuit X f G = foldr f xs G"
    using inner_fold_circuit[OF assms(1), of f G] by auto
  have treat_is: "treat1_circuit y X G = foldr f xs G"
    by(unfold xs_prop(3)[symmetric])(simp add: treat1_circuit_def f_def)
  have claim1:"graph.graph_inv (foldr f xs G)" for xs
    by(induction xs)(auto split: if_split simp add: f_def assms(2))
  thus "graph.graph_inv (treat1_circuit y X G)"
    by (simp add: treat_is)
  have "set xs \<subseteq> to_set_red X  \<Longrightarrow>graph.digraph_abs (foldr f xs G) = graph.digraph_abs G \<union>
                       {(x, y) | x. x \<in> set xs }"
    using xs_prop(2) 
    apply(induction xs, simp)
    apply(subst foldr_Cons, subst o_apply)
    apply(subst f_def)
    by(auto simp add:  graph.digraph_abs_insert[OF claim1])
  thus "[treat1_circuit y X G]\<^sub>g = [G]\<^sub>g \<union> {(x, y) |x. x \<in> to_set_red X}"
    by(simp add: treat_is xs_prop(1))
  have "set xs \<subseteq> to_set_red X \<Longrightarrow> graph.finite_graph G \<Longrightarrow> graph.finite_graph (foldr f xs G)"
    apply(induction xs, simp)
    apply(subst foldr_Cons, subst o_apply)
    apply(subst f_def)
    by(auto simp add: claim1 graph.finite_graph_add_edge)
  thus "graph.finite_graph G \<Longrightarrow> graph.finite_graph (treat1_circuit y X G)" 
    by (simp add: treat_is xs_prop(1))
  have "set xs \<subseteq> to_set_red X \<Longrightarrow> graph.finite_vsets G \<Longrightarrow> graph.finite_vsets (foldr f xs G)"
    apply(induction xs, simp)
    apply(subst foldr_Cons, subst o_apply)
    apply(subst f_def)
    by(auto simp add: claim1 graph.finite_vsets_add_edge)
  thus "graph.finite_vsets G \<Longrightarrow> graph.finite_vsets (treat1_circuit y X G)" 
    by (simp add: treat_is xs_prop(1))
qed

lemma treat2_circuit_correct:
  assumes "set_invar_red X" "graph.graph_inv G"
  shows "graph.graph_inv (treat2_circuit y X G)"
    "graph.digraph_abs (treat2_circuit y X G) = graph.digraph_abs G \<union>
                       {(y, x) | x. x \<in> to_set_red X}"
    "graph.finite_graph G \<Longrightarrow> graph.finite_graph (treat2_circuit y X G)"
    "graph.finite_vsets G \<Longrightarrow> graph.finite_vsets (treat2_circuit y X G)"
proof-
  define f where "f = (\<lambda> x current_map.  graph.add_edge current_map y x)"
  obtain xs where xs_prop: "set xs = to_set_red X" True "inner_fold_circuit X f G = foldr f xs G"
    using inner_fold_circuit[OF assms(1), of f G] by auto
  have treat_is: "treat2_circuit y X G = foldr f xs G"
    by(unfold xs_prop(3)[symmetric])(simp add: treat2_circuit_def f_def)
  have claim1:"graph.graph_inv (foldr f xs G)" for xs
    by(induction xs)(auto split: if_split simp add: f_def assms(2))
  thus "graph.graph_inv (treat2_circuit y X G)"
    by (simp add: treat_is)
  have "set xs \<subseteq> to_set_red X  \<Longrightarrow>graph.digraph_abs (foldr f xs G) = graph.digraph_abs G \<union>
                       {(y, x) | x. x \<in> set xs }"
    using xs_prop(2) 
    apply(induction xs, simp)
    apply(subst foldr_Cons, subst o_apply)
    apply(subst f_def)
    by(auto simp add:  graph.digraph_abs_insert[OF claim1])
  thus "[treat2_circuit y X G]\<^sub>g = [G]\<^sub>g \<union> {(y, x) |x. x \<in> to_set_red X}"
    by(simp add: treat_is xs_prop(1))
  have "set xs \<subseteq> to_set_red X \<Longrightarrow> graph.finite_graph G \<Longrightarrow> graph.finite_graph (foldr f xs G)"
    apply(induction xs, simp)
    apply(subst foldr_Cons, subst o_apply)
    apply(subst f_def)
    by(auto simp add: claim1 graph.finite_graph_add_edge)
  thus "graph.finite_graph G \<Longrightarrow> graph.finite_graph (treat2_circuit y X G)" 
    by (simp add: treat_is xs_prop(1))
  have "set xs \<subseteq> to_set_red X \<Longrightarrow> graph.finite_vsets G \<Longrightarrow> graph.finite_vsets (foldr f xs G)"
    apply(induction xs, simp)
    apply(subst foldr_Cons, subst o_apply)
    apply(subst f_def)
    by(auto simp add: claim1 graph.finite_vsets_add_edge)
  thus "graph.finite_vsets G \<Longrightarrow> graph.finite_vsets (treat2_circuit y X G)" 
    by (simp add: treat_is xs_prop(1))
qed

lemma compute_graph_circuit_correct:
  assumes "indep1 (to_set X)" "indep2 (to_set X)" "set_invar X" 
    "set_invar_red E_without_X" "to_set_red E_without_X \<subseteq> carrier - to_set X"
    "compute_graph_circuit X E_without_X = (SX, TX, resulting_map)"
  shows   "vset_inv SX" "vset_inv TX" "graph.graph_inv resulting_map" "graph.finite_graph resulting_map"
    "vset SX = {y | y. y \<in> to_set_red E_without_X \<and> indep1 (Set.insert y (to_set X))}"
    "vset TX = {y | y. y \<in> to_set_red E_without_X \<and> indep2 (Set.insert y (to_set X))}"
    and "graph.digraph_abs resulting_map = 
                {(x, y) |x y. y \<in> to_set_red E_without_X 
                       \<and> x \<in> matroid1.the_circuit (Set.insert y (to_set X)) - {y}}
                \<union> {(y, x) |x y. y \<in> to_set_red E_without_X
                       \<and> x \<in> matroid2.the_circuit (Set.insert y (to_set X)) - {y}}"
    (is ?last_thesis)
  and "graph.finite_vsets resulting_map"
proof-
  define f where "f = (\<lambda> y (SX, TX, current_map). (
            let (SX, TX, current_map) = (if weak_orcl1 y X then (insert y SX, TX, current_map)
                                         else (SX, TX, treat1_circuit y (circuit1 y X) current_map));
                (SX, TX, current_map) = (if weak_orcl2 y X then (SX, insert y TX, current_map)
                                         else (SX, TX, treat2_circuit y (circuit2 y X) current_map))
            in (SX, TX, current_map)))"
  obtain xs where xs_prop: "set xs = to_set_red E_without_X" True
    "outer_fold E_without_X f (\<emptyset>\<^sub>N, \<emptyset>\<^sub>N, \<emptyset>\<^sub>G) = foldr f xs (\<emptyset>\<^sub>N, \<emptyset>\<^sub>N, \<emptyset>\<^sub>G)"
    using outer_fold[OF assms(4), of f "(vset_empty, vset_empty, empty)"] by auto
  have SX_is: "SX = fst (foldr f xs (\<emptyset>\<^sub>N, \<emptyset>\<^sub>N, \<emptyset>\<^sub>G))"
    using assms(6) xs_prop(3)[symmetric]
    by(auto simp add: f_def compute_graph_circuit_def)
  have TX_is: "TX = fst (snd (foldr f xs (\<emptyset>\<^sub>N, \<emptyset>\<^sub>N, \<emptyset>\<^sub>G)))"
    using assms(6) xs_prop(3)[symmetric]
    by(auto simp add: f_def compute_graph_circuit_def)
  have resulting_map_is: "resulting_map = snd (snd (foldr f xs (\<emptyset>\<^sub>N, \<emptyset>\<^sub>N, \<emptyset>\<^sub>G)))"
    using assms(6) xs_prop(3)[symmetric]
    by(auto simp add: f_def compute_graph_circuit_def)
  have vset_inv_SX:"vset_inv (fst (foldr f xs (\<emptyset>\<^sub>N, \<emptyset>\<^sub>N, \<emptyset>\<^sub>G)))" for xs
    by(induction xs)
      (auto split: prod.split intro: graph.vset.set.invar_insert simp add: f_def graph.vset.set.invar_empty)
  thus "vset_inv SX"
    using SX_is by fastforce
  have vset_inv_TX:"vset_inv (fst (snd (foldr f xs (\<emptyset>\<^sub>N, \<emptyset>\<^sub>N, \<emptyset>\<^sub>G))))" for xs
    by(induction xs)
      (auto split: prod.split intro: graph.vset.set.invar_insert simp add: f_def graph.vset.set.invar_empty)
  thus "vset_inv TX"
    using TX_is by fastforce 
  have graph_inv_resulting_map:
    "set xs \<subseteq> carrier - to_set X \<Longrightarrow> graph.graph_inv (snd (snd (foldr f xs (\<emptyset>\<^sub>N, \<emptyset>\<^sub>N, \<emptyset>\<^sub>G))))" for xs
    by(induction xs)
      (auto split: prod.split intro!: treat2_circuit_correct(1) treat1_circuit_correct(1)
        simp add: X_in_carrier assms(1) assms(2) assms(3) circuit2(2) weak_orcl2 circuit1(2) weak_orcl1
        f_def graph.graph_inv_empty)
  thus "graph.graph_inv resulting_map"
    by (simp add: assms(5) resulting_map_is xs_prop(1))
  have X_in_carrier:"to_set X \<subseteq> carrier"
    by (simp add: assms(1) matroid1.indep_subset_carrier)
  have "set xs \<subseteq> carrier - to_set X \<Longrightarrow> vset (fst (foldr f xs (\<emptyset>\<^sub>N, \<emptyset>\<^sub>N, \<emptyset>\<^sub>G))) = 
           {y |y. y \<in> set xs \<and> indep1 (Set.insert y (to_set X))}"
  proof(induction xs)
    case (Cons a xs)
    show ?case
    proof(subst foldr_Cons, subst o_apply, subst f_def, unfold Let_def,
        (split prod.split, rule, rule, rule)+, goal_cases)
      case (1 x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e)
      then show ?case 
        using Cons  vset_inv_SX[of xs]  graph.vset.set.set_insert
          weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
        by (cases "weak_orcl1 a X", all \<open>cases "weak_orcl2 a X"\<close>) auto
    qed
  qed(auto simp add: graph.vset.emptyD(3))
  thus "vset SX = {y |y. y \<in> to_set_red E_without_X \<and> indep1 (Set.insert y (to_set X))}"
    using SX_is assms(5) xs_prop(1) by presburger
  have "set xs \<subseteq> carrier - to_set X \<Longrightarrow> vset (fst (snd (foldr f xs (\<emptyset>\<^sub>N, \<emptyset>\<^sub>N, \<emptyset>\<^sub>G)))) = 
           {y |y. y \<in> set xs \<and> indep2 (Set.insert y (to_set X))}"
  proof(induction xs)
    case (Cons a xs)
    show ?case
    proof(subst foldr_Cons, subst o_apply, subst f_def, unfold Let_def,
        (split prod.split, rule, rule, rule)+, goal_cases)
      case (1 x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e)
      then show ?case 
        using Cons  vset_inv_TX[of xs]  graph.vset.set.set_insert
          weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
        by (cases "weak_orcl1 a X", all \<open>cases "weak_orcl2 a X"\<close>) auto
    qed
  qed(auto simp add: graph.vset.emptyD(3))
  thus "vset TX = {y |y. y \<in> to_set_red E_without_X \<and> indep2 (Set.insert y (to_set X))}"
    using TX_is assms(5) xs_prop(1) by presburger
  have "set xs \<subseteq> carrier -to_set X \<Longrightarrow> graph.digraph_abs (snd (snd (foldr f xs (\<emptyset>\<^sub>N, \<emptyset>\<^sub>N, \<emptyset>\<^sub>G)))) =  
           {(x, y) |x y.
     y \<in> set xs \<and> x \<in> matroid1.the_circuit (Set.insert y (to_set X)) - {y}} \<union>
    {(y, x) |x y.
     y \<in> set xs \<and> x \<in> matroid2.the_circuit (Set.insert y (to_set X)) - {y}}"
  proof(induction xs)
    case (Cons a xs)
    show ?case
    proof(subst foldr_Cons, subst o_apply, subst f_def, unfold Let_def,
        (split prod.split, rule, rule, rule)+, goal_cases)
      case (1 x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e)
      then show ?case 
      proof(cases "weak_orcl1 a X", all \<open>cases "weak_orcl2 a X"\<close>, goal_cases)
        case 1
        then show ?case 
          using Cons  weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)] 
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
            matroid1.independent_empty_circuit  matroid2.independent_empty_circuit
          by auto 
      next
        case 2
        then show ?case 
          using  graph_inv_resulting_map  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)] 
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)] 
            matroid1.independent_empty_circuit  matroid2.independent_empty_circuit
            X_in_carrier assms(2) assms(3) circuit2(2) assms(1) circuit2(1)
          apply (clarsimp,  subst treat2_circuit_correct(2))
            apply (force)
           apply (metis (no_types, lifting) snd_conv) 
          by(auto split: prod.split ) 
      next
        case 3
        then show ?case
          using  graph_inv_resulting_map  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)] 
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)] 
            matroid1.independent_empty_circuit  matroid2.independent_empty_circuit
            X_in_carrier assms(2) assms(3) circuit1(2) assms(1) circuit1(1)
          apply (clarsimp,  subst treat1_circuit_correct(2)) 
            apply (force)
           apply (metis (no_types, lifting) snd_conv) 
          by(auto split: prod.split ) 
      next
        case 4
        then show ?case
          using Cons.prems X_in_carrier assms(2) assms(3) circuit2(2) weak_orcl2
          apply(clarsimp, subst treat2_circuit_correct(2), simp)
           apply(rule treat1_circuit_correct(1)) 
          using assms(1) circuit1(2)  graph_inv_resulting_map[of xs]  
            Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]  
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]         
          by (subst treat1_circuit_correct(2)| force simp add: circuit1(1) circuit2(1) assms(1,2,3))+
      qed
    qed
  qed (auto simp add:  graph.digraph_abs_empty)
  thus ?last_thesis
    using assms(5) resulting_map_is xs_prop(1) by presburger
  have "set xs  \<subseteq> carrier -to_set X \<Longrightarrow> graph.finite_graph (snd (snd (foldr f xs (\<emptyset>\<^sub>N, \<emptyset>\<^sub>N, \<emptyset>\<^sub>G))))"
  proof(induction xs)
    case (Cons a xs)
    show ?case
    proof(subst foldr_Cons, subst o_apply, subst f_def, unfold Let_def,
        (split prod.split, rule, rule, rule)+, goal_cases)
      case (1 x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e)
      then show ?case 
      proof(cases "weak_orcl1 a X", all \<open>cases "weak_orcl2 a X"\<close>, goal_cases)
        case 1
        then show ?case 
          using Cons  weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)] 
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
          by auto
      next
        case 2
        then show ?case 
          using  graph_inv_resulting_map  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)] 
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)] 
            X_in_carrier assms(2) assms(3) circuit2(2)
          apply(clarsimp, subst treat2_circuit_correct(3)) 
             apply (force)
            apply (metis (no_types, lifting) snd_conv) 
          by(auto split: prod.split ) 
      next
        case 3
        then show ?case 
          using  graph_inv_resulting_map  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)] 
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)] 
            X_in_carrier assms(1) assms(3) circuit1(2)
          apply (clarsimp, subst treat1_circuit_correct(3))
             apply (force)
            apply (metis (no_types, lifting) snd_conv) 
          by(auto split: prod.split )
      next
        case 4
        then show ?case
          using Cons.prems
          apply(clarsimp, subst treat2_circuit_correct(3))
          using   X_in_carrier assms(1) assms(3) circuit1(2)   weak_orcl1[OF  assms(3) X_in_carrier _ _ assms(1)] 
            graph_inv_resulting_map Cons.IH 
          by (fastforce intro!: treat1_circuit_correct(1,3) circuit1(2) 
              simp add: X_in_carrier assms(2) assms(3) circuit2(2) weak_orcl2)+
      qed
    qed 
  qed (auto simp add: graph.adjmap.map_empty graph.finite_graph_def)
  thus "graph.finite_graph resulting_map"
    using  resulting_map_is xs_prop(1)  assms(5) by blast
  have "set xs  \<subseteq> carrier -to_set X \<Longrightarrow> graph.finite_vsets (snd (snd (foldr f xs (\<emptyset>\<^sub>N, \<emptyset>\<^sub>N, \<emptyset>\<^sub>G))))"
  proof(induction xs)
    case (Cons a xs)
    show ?case
    proof(subst foldr_Cons, subst o_apply, subst f_def, unfold Let_def,
        (split prod.split, rule, rule, rule)+, goal_cases)
      case (1 x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e)
      then show ?case 
      proof(cases "weak_orcl1 a X", all \<open>cases "weak_orcl2 a X"\<close>, goal_cases)
        case 1
        then show ?case 
          using Cons  weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)] 
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
          by auto
      next
        case 2
        then show ?case 
          using  graph_inv_resulting_map  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)] 
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)] 
            X_in_carrier assms(2) assms(3) circuit2(2)
          apply(clarsimp, subst treat2_circuit_correct(4)) 
             apply (force)
            apply (metis (no_types, lifting) snd_conv) 
          by(auto split: prod.split ) 
      next
        case 3
        then show ?case 
          using  graph_inv_resulting_map  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)] 
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)] 
            X_in_carrier assms(1) assms(3) circuit1(2)
          apply (clarsimp, subst treat1_circuit_correct(4))
             apply (force)
            apply (metis (no_types, lifting) snd_conv) 
          by(auto split: prod.split )
      next
        case 4
        then show ?case
          using Cons.prems
          apply(clarsimp, subst treat2_circuit_correct(4))
          using   X_in_carrier assms(1) assms(3) circuit1(2)   weak_orcl1[OF  assms(3) X_in_carrier _ _ assms(1)] 
            graph_inv_resulting_map Cons.IH 
          by (fastforce intro!: treat1_circuit_correct(1,4) circuit1(2) 
              simp add: X_in_carrier assms(2) assms(3) circuit2(2) weak_orcl2)+
      qed
    qed 
  qed (auto simp add: graph.adjmap.map_empty graph.finite_graph_def)
  thus "graph.finite_vsets resulting_map"
    using  resulting_map_is xs_prop(1)  assms(5) by blast
qed

lemma compute_graph_meaning_circuit:
  assumes "indep1 (to_set X)" "indep2 (to_set X)" "set_invar X" 
    "set_invar_red E_without_X" "to_set_red E_without_X = carrier - to_set X"
    "compute_graph_circuit X E_without_X = (SX, TX, resulting_map)"
  shows   "vset SX = S (to_set X)"
    "vset TX = T (to_set X)"
    "graph.digraph_abs resulting_map = A1 (to_set X) \<union> A2 (to_set X)"
  subgoal
    using compute_graph_circuit_correct(5)[OF assms(1-4) _ assms(6)] assms(5)
    by (simp add: S_def)
  subgoal
    using compute_graph_circuit_correct(6)[OF assms(1-4) _ assms(6)] assms(5)
    by (simp add: T_def)
  subgoal 
    using matroid2.indep_subset_carrier[OF assms(2)]
    by(subst compute_graph_circuit_correct(7)[OF assms(1-4) _ assms(6)])
      (auto simp add: matroid1.circuit_extensional[OF assms(1)] insert_Diff_if
        matroid2.circuit_extensional[OF assms(2)] A1_def A2_def assms(5))
  done

lemma indep_invar_recurse_circuit_improvement:
  assumes "matroid_intersection_circuit_recurse_cond state" "indep_invar state"
    "set_invar (sol state) " "to_set (sol state) \<subseteq> carrier"
  shows   "indep_invar (matroid_intersection_circuit_recurse_upd state)"
    "set_invar (sol (matroid_intersection_circuit_recurse_upd state))" 
    "to_set (sol (matroid_intersection_circuit_recurse_upd state)) \<subseteq> carrier"
    "card (to_set (sol (matroid_intersection_circuit_recurse_upd state))) = 
          card (to_set (sol state)) + 1"
    and   "\<exists>u v p. (vwalk_bet (A1 (to_set (sol state)) \<union> A2 (to_set (sol state))) u p v \<or> (p = [u] \<and> u = v) )\<and>
           u \<in> S (to_set (sol state)) \<and>
           v \<in> T (to_set (sol state))" (is ?last_thesis)
proof(all \<open>rule P_of_matroid_intersection_circuit_recurseI[OF assms(1)]\<close>)
  fix SX TX graph p X
  assume 1: "compute_graph_circuit X (complement X) = (SX, TX, graph)" 
    "find_path SX TX graph = Some p" "X = sol state"
  have Xincarrier: "to_set X \<subseteq> carrier"
    by (simp add: assms(4) 1(3))
  have indep1X: "indep1 (to_set X)"
    using assms(2) indep_invar_def 1(3) by auto
  have indep2X: "indep2 (to_set X)" 
    using assms(2) indep_invar_def 1(3) by auto
  have complementInvar: "set_invar_red (complement X)" 
    using complement(1)[OF _ Xincarrier] 1(3) assms(3) by simp
  hence complement_is: "to_set_red (complement X) = carrier - to_set X"
    using Xincarrier assms(3) complement(2) 1(3) by auto
  hence complementcarrier: "to_set_red (complement X) \<subseteq> carrier - to_set X"
    by simp
  have setinvarX: "set_invar X"
    using assms(3) 1(3) by auto 
  note compute_graph_correct = compute_graph_circuit_correct[OF indep1X indep2X 
       setinvarX complementInvar complementcarrier 1(1)] 
  have SXincarrier: "vset SX \<subseteq> carrier" 
    using complementcarrier compute_graph_correct(5) assms(3) 1(3) by blast
  have TXincarrier: "vset TX \<subseteq> carrier"
    using complementcarrier compute_graph_correct(6) 1(3) assms(3) by blast
  have graphverticesincarrier: "dVs [graph]\<^sub>g \<subseteq> carrier" 
    using compute_graph_correct dVs_A1A2_carrier indep1X indep2X 
    by (simp add: A1_def A2_def complement_is)
  have finite_vsets: "graph.finite_vsets graph"
    by (simp add: compute_graph_correct(8))
  obtain u v where p_prop: "vwalk_bet [graph]\<^sub>g u p v \<or> (p = [u] \<and> u = v)"
    "u \<in> vset SX"
    "v \<in> vset TX"
    "(\<nexists>p'.
          (vwalk_bet [graph]\<^sub>g u p' v \<or> (p' = [u] \<and> u = v)) \<and> length p' < length p)"
    using find_path(2)[OF compute_graph_correct(3,4) finite_vsets compute_graph_correct(1,2) 
        SXincarrier TXincarrier graphverticesincarrier 1(2)] assms(3) 1(3) by auto
  hence p_prop_extended: "vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p v \<or> (p = [u] \<and> u = v)" 
    "(\<nexists>p'.
          (vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p' v \<or> (p' = [u] \<and> u = v)) \<and> length p' < length p)"
    using compute_graph_correct p_prop(4) assms(3) 1(3) 
    by(unfold A1_def A2_def complement_is) auto
  have pincarrier:"set p \<subseteq> carrier"
    using p_prop(1-3) graphverticesincarrier in_mono vwalk_bet_in_vertices[of "[graph]\<^sub>g" u p v] SXincarrier 
    by auto
  have p_not_empty:"p \<noteq> []" 
    using p_prop(1) by(auto simp add: vwalk_bet_def) 
  have distinctp:"distinct p"
  proof(rule ccontr, goal_cases)
    case 1
    then obtain p1 x p2 p3 where p_decomp:"p = p1@[x]@p2@[x]@p3"
      using not_distinct_decomp by blast
    moreover hence "length p \<ge> 2" by auto
    moreover hence "vwalk_bet [graph]\<^sub>g u p v"
      using p_prop(1) by(auto simp add: vwalk_bet_def)
    ultimately have "vwalk_bet [graph]\<^sub>g u (p1@[x]@p3) v"
      by (meson indep1X indep2X vwalk_bet_cycle_delete)
    moreover have "length (p1@[x]@p3)< length p"
      using p_decomp by simp
    ultimately show ?case
      using p_prop(2) p_prop(3) p_prop(4) by blast
  qed
  have indep_after_aug:"indep1 (to_set (augment X p))"
    using p_prop_extended compute_graph_meaning_circuit p_prop
      p_not_empty  augment_in_matroid1_single[OF indep1X indep2X, of v] compute_graph_correct(5)
      augment_in_matroid1[OF indep1X indep2X, of u p v] 
    by ( subst effect_of_augmentation(2)[OF  setinvarX  Xincarrier pincarrier  distinctp refl])
      (auto intro: vwalk_arcs.cases[of p] simp add:  S_def complement_is compute_graph_correct(5)
        T_def  compute_graph_correct(6)  vwalk_bet_def )
  moreover have "indep2 (to_set (augment X p))"
    using p_prop_extended compute_graph_meaning_circuit p_prop
      p_not_empty  augment_in_matroid2_single[OF indep1X indep2X, of v] compute_graph_correct(5)
      augment_in_matroid2[OF indep1X indep2X, of u p v]
    by (subst effect_of_augmentation(2)[OF  setinvarX  Xincarrier pincarrier  distinctp refl])
      (auto intro: vwalk_arcs.cases[of p] simp add:  S_def complement_is compute_graph_correct(5)
        T_def  compute_graph_correct(6)  vwalk_bet_def)
  ultimately show "indep_invar (state\<lparr>sol := augment X p\<rparr>)"
    by(simp add: indep_invar_def)
  show "set_invar (sol (state\<lparr>sol := augment X p\<rparr>))"
    using 1(3)  Xincarrier distinctp effect_of_augmentation(1) pincarrier setinvarX by auto
  show "to_set (sol (state\<lparr>sol := augment X p\<rparr>)) \<subseteq> carrier"
    by (simp add: indep_after_aug matroid1.indep_subset_carrier)
  show "card (to_set (sol (state\<lparr>sol := augment X p\<rparr>))) = card (to_set (sol state)) + 1"
    apply(subst sol_remove, subst 1(3)[symmetric])
    using p_not_empty  p_prop_extended(1,2) 
          augment_in_both_matroids_single(3)[OF indep1X indep2X , of u] 
      setinvarX  complementInvar complement_is 
      compute_graph_meaning_circuit(1,2)[of X] indep1X indep2X p_prop(2) p_prop(3)   
      augment_in_both_matroids(3)[OF indep1X indep2X _ _ _ _ refl, of u p v]
      compute_graph_correct(5,6) p_prop 
    apply(subst effect_of_augmentation(2)[OF setinvarX Xincarrier pincarrier  distinctp refl])
    by(rule vwalk_arcs.cases[of p], auto simp add: T_def  S_def)
  show ?last_thesis 
    using compute_graph_meaning_circuit p_prop p_prop_extended(1)
      "1"(1,3) assms(3) complementInvar complement_is indep1X indep2X by auto
qed

lemma indep_invar_max_found_circuit:
  assumes "matroid_intersection_circuit_terminates_cond state" "indep_invar state"
    "set_invar (sol state)" "to_set (sol state) \<subseteq> carrier"
  shows   "is_max (to_set (sol state))"
proof(rule matroid_intersection_circuit_terminates_condE[OF assms(1)])
  fix SX TX graph p X
  assume 1: "compute_graph_circuit X (complement X) = (SX, TX, graph)"
    "find_path SX TX graph = None" "X = sol state"
  have Xincarrier: "to_set X \<subseteq> carrier"
    using 1(3) by (simp add: assms(4))
  have indep1X: "indep1 (to_set X)"
    using assms(2) indep_invar_def 1(3) by auto
  have indep2X: "indep2 (to_set X)" 
    using assms(2) indep_invar_def 1(3) by auto
  have setinvarX: "set_invar X" 
    using assms(3) 1(3) by simp
  have complementInvar: "set_invar_red (complement X)" 
    using complement(1)[OF setinvarX Xincarrier] by simp
  hence complement_is: "to_set_red (complement X) = carrier - to_set X"
    by (simp add: Xincarrier setinvarX complement(2))
  hence complementcarrier: "to_set_red (complement X) \<subseteq> carrier - to_set X"
    by simp
  note compute_graph_correct = compute_graph_circuit_correct[OF indep1X indep2X setinvarX 
      complementInvar complementcarrier 1(1)]
  note compute_graph_meaning = compute_graph_meaning_circuit[OF indep1X indep2X setinvarX complementInvar complement_is 1(1)]
  have SXincarrier: "vset SX \<subseteq> carrier" 
    using S_in_carrier compute_graph_meaning(1) indep1X indep2X by auto
  have TXincarrier: "vset TX \<subseteq> carrier" 
    using T_in_carrier compute_graph_meaning(2) indep1X indep2X by auto
  have graphverticesincarrier: "dVs [graph]\<^sub>g \<subseteq> carrier" 
    using compute_graph_meaning(3) dVs_A1A2_carrier indep1X indep2X by presburger
  have finite_vsets: "graph.finite_vsets graph "
    using compute_graph_correct(8) by blast
  have no_path: "(\<nexists>p u v. (vwalk_bet [graph]\<^sub>g u p v \<or> (p = [u] \<and> u = v)) \<and> u \<in> vset SX \<and> v \<in> vset TX)"
    using find_path(1)[OF compute_graph_correct(3,4) finite_vsets compute_graph_correct(1,2) 
        SXincarrier TXincarrier graphverticesincarrier ] 1(2) by auto
  hence "\<nexists>p x y. x \<in> S (to_set X) \<and> y \<in> T (to_set X) 
              \<and> (vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) x p y \<or> x = y)"
    using compute_graph_meaning(1) compute_graph_meaning(2) compute_graph_meaning(3) 
    by (auto simp add: vwalk_bet_def)
  thus  "is_max (to_set (sol state))"
    using if_no_augpath_then_maximum(1)[OF indep1X indep2X _ refl]
      indep1X indep2X by(auto simp add: is_max_def 1(3))
qed

lemma matroid_intersection_circuit_terminates_general:
  assumes  "indep_invar state" "set_invar (sol state)" "to_set (sol state) \<subseteq> carrier"
    "m = card carrier - card (to_set (sol state))"
  shows    "matroid_intersection_circuit_dom state"
  using assms
proof(induction m arbitrary: state)
  case 0
  hence X_is_carrier:"to_set (sol state) = carrier" 
    by (simp add: card_seteq matroid2.carrier_finite)
  show ?case 
  proof(cases state rule: matroid_intersection_circuit_cases)
    case 1
    show ?thesis 
      by(rule matroid_intersection_circuit_terminates_condE[OF 1])
        (auto intro: matroid_intersection_circuit.domintros)
  next
    case 2
    have "S (to_set (sol state)) \<noteq> {}" "T (to_set (sol state)) \<noteq> {}"
      using indep_invar_recurse_circuit_improvement(5)[OF 2 0(1,2,3)] by auto
    moreover have  "S (to_set (sol state)) = {}"
      by(simp add: X_is_carrier  S_def)
    ultimately show ?thesis by simp
  qed
next
  case (Suc m)
  show ?case  
  proof(cases state rule: matroid_intersection_circuit_cases)
    case 1
    show ?thesis 
      by(rule matroid_intersection_circuit_terminates_condE[OF 1])
        (auto intro: matroid_intersection_circuit.domintros)
  next
    case 2
    show ?thesis
    proof(rule matroid_intersection_circuit_recurse_condE[OF 2], goal_cases)
      case (1 SX TX graph p X)
      have helper:"indep1 (to_set (augment X p))" "indep2 (to_set (augment X p))"
                  "set_invar (augment X p)""to_set (augment X p) \<subseteq> carrier"
        using 1 2  indep_invar_recurse_circuit_improvement[OF 2 Suc.prems(1,2,3)] 
        by(auto simp add: matroid_intersection_circuit_recurse_upd_def indep_invar_def)
      have card_decrease: "m = card carrier - card (to_set (augment X p))"
        using 1 2 Suc.prems(4) indep_invar_recurse_circuit_improvement[OF 2 Suc.prems(1,2,3)] 
        by(auto simp add: matroid_intersection_circuit_recurse_upd_def)
      show ?case 
        apply(rule matroid_intersection_circuit.domintros)
        using helper 1 card_decrease
        by (auto intro!: Suc(1) simp add: indep_invar_def )
    qed
  qed
qed

lemma matroid_intersection_circuit_correctness_general:
  assumes "indep_invar state" "set_invar (sol state)" "to_set (sol state) \<subseteq> carrier"
  shows "is_max (to_set (sol (matroid_intersection_circuit state)))"
  using assms
proof(induction state rule: matroid_intersection_circuit_induct)
  case 1
  then show ?case 
    using matroid_intersection_circuit_terminates_general[OF assms refl] by simp
next
  case (2 state)
  note IH = this
  show ?case 
  proof(cases state rule: matroid_intersection_circuit_cases)
    case 1
    then show ?thesis 
      by (simp add: "2.hyps" "2.prems" indep_invar_max_found_circuit matroid_intersection_circuit_simps(1))
  next
    case 2
    show ?thesis 
      apply(subst matroid_intersection_circuit_simps(2)[OF IH(1) 2])+
      apply(rule IH(2)[OF 2])
      by(auto simp add: "2" IH(3-) indep_invar_recurse_circuit_improvement)
  qed
qed

lemma matroid_intersection_circuit_correctness:
  "indep_invar (matroid_intersection_circuit initial_state)"
  "is_max (to_set (sol (matroid_intersection_circuit initial_state)))"
  using matroid_intersection_circuit_correctness_general 
  by(simp add: indep_invar_def is_max_def local.set_empty(1) local.set_empty(2) initial_state_def)+

lemma matroid_intersection_circuit_termiantes: "matroid_intersection_circuit_dom initial_state"
  by(rule matroid_intersection_circuit_terminates_general)
    (auto simp add: indep_invar_def set_empty initial_state_def)

lemma same_results: "matroid_intersection_impl initial_state = matroid_intersection initial_state"
  "matroid_intersection_circuit_impl initial_state = matroid_intersection_circuit initial_state"
  by(simp add: implementation_is_same matroid_intersection_termiantes
      implementation_circuit_is_same matroid_intersection_circuit_termiantes)+

end
end