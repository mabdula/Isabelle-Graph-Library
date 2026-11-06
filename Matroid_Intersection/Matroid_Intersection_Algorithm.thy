(*
  Author: Thomas Ammer
*)

theory Matroid_Intersection_Algorithm
  imports Matroid_Intersection_Path_Loop
begin

provenance human

section \<open>Maximum Cardinality Matroid Intersection Algorithm\<close>

text \<open>This file contains a formalisation of the maximum cardinality matroid intersection algorithm
given by Korte and Vygen. The loop itself is the one of
@{theory Matroid_Intersection.Matroid_Intersection_Path_Loop}. Here it is instantiated twice:
the augmenting path is found by building the auxiliary graph explicitly, either by exchange
oracles or by circuit oracles, and running a path search on it.\<close>

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

text \<open>The two path searches: build the auxiliary graph, then search it.\<close>

definition "aux_path X = 
  (case compute_graph X (complement X) of (SX, TX, G) \<Rightarrow> find_path SX TX G)"

definition "aux_path_circuit X = 
  (case compute_graph_circuit X (complement X) of (SX, TX, G) \<Rightarrow> find_path SX TX G)"

sublocale standard: unweighted_intersection_path_loop_spec
  where augmenting_path = aux_path
  by unfold_locales

definition "augment = standard.augment"

definition "matroid_intersection \<equiv> standard.matroid_intersection"
definition "matroid_intersection_impl \<equiv> standard.matroid_intersection_impl"

lemmas matroid_intersection_impl_simps =
  standard.matroid_intersection_impl.simps[folded matroid_intersection_impl_def]

sublocale circuit: unweighted_intersection_path_loop_spec
  where augmenting_path = aux_path_circuit
  by unfold_locales

definition "matroid_intersection_circuit \<equiv> circuit.matroid_intersection"
definition "matroid_intersection_circuit_impl \<equiv> circuit.matroid_intersection_impl"

lemmas matroid_intersection_circuit_impl_simps =
  circuit.matroid_intersection_impl.simps[folded matroid_intersection_circuit_impl_def]

lemmas [code] = treat1_def treat2_def treat1_circuit_def treat2_circuit_def
  compute_graph_def compute_graph_circuit_def aux_path_def aux_path_circuit_def
  graph.add_edge_def matroid_intersection_circuit_impl_simps
  matroid_intersection_impl_simps
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

lemma compute_graph_aux_graph:
  assumes "set_invar X" "to_set X \<subseteq> carrier" "indep1 (to_set X)" "indep2 (to_set X)"
    "compute_graph X (complement X) = (SX, TX, G)"
  shows "graph.graph_inv G" "graph.finite_graph G" "graph.finite_vsets G"
    "vset_inv SX" "vset_inv TX" "vset SX \<subseteq> carrier" "vset TX \<subseteq> carrier"
    "dVs (graph.digraph_abs G) \<subseteq> carrier"
    "vset SX = S (to_set X)" "vset TX = T (to_set X)"
    "graph.digraph_abs G = A1 (to_set X) \<union> A2 (to_set X)"
proof-
  have complement_invar: "set_invar_red (complement X)"
    and complement_is: "to_set_red (complement X) = carrier - to_set X"
    using complement[OF assms(1,2)] by auto
  have complement_carrier: "to_set_red (complement X) \<subseteq> carrier - to_set X"
    using complement_is by simp
  note correct = compute_graph_correct[OF assms(3,4,1) complement_invar complement_carrier assms(5)]
  note meaning = compute_graph_meaning[OF assms(3,4,1) complement_invar complement_is assms(5)]
  show "graph.graph_inv G" "graph.finite_graph G" "graph.finite_vsets G" "vset_inv SX" "vset_inv TX"
    by(rule correct(3,4,8,1,2))+
  show "vset SX = S (to_set X)" "vset TX = T (to_set X)" 
    "graph.digraph_abs G = A1 (to_set X) \<union> A2 (to_set X)"
    by(rule meaning(1,2,3))+
  thus "vset SX \<subseteq> carrier" "vset TX \<subseteq> carrier" "dVs (graph.digraph_abs G) \<subseteq> carrier"
    using S_in_carrier[OF assms(3,4)] T_in_carrier[OF assms(3,4)] dVs_A1A2_carrier[OF assms(3,4)]
    by simp_all
qed

lemma compute_graph_circuit_aux_graph:
  assumes "set_invar X" "to_set X \<subseteq> carrier" "indep1 (to_set X)" "indep2 (to_set X)"
    "compute_graph_circuit X (complement X) = (SX, TX, G)"
  shows "graph.graph_inv G" "graph.finite_graph G" "graph.finite_vsets G"
    "vset_inv SX" "vset_inv TX" "vset SX \<subseteq> carrier" "vset TX \<subseteq> carrier"
    "dVs (graph.digraph_abs G) \<subseteq> carrier"
    "vset SX = S (to_set X)" "vset TX = T (to_set X)"
    "graph.digraph_abs G = A1 (to_set X) \<union> A2 (to_set X)"
proof-
  have complement_invar: "set_invar_red (complement X)"
    and complement_is: "to_set_red (complement X) = carrier - to_set X"
    using complement[OF assms(1,2)] by auto
  have complement_carrier: "to_set_red (complement X) \<subseteq> carrier - to_set X"
    using complement_is by simp
  note correct = compute_graph_circuit_correct[OF assms(3,4,1) complement_invar complement_carrier assms(5)]
  note meaning = compute_graph_meaning_circuit[OF assms(3,4,1) complement_invar complement_is assms(5)]
  show "graph.graph_inv G" "graph.finite_graph G" "graph.finite_vsets G" "vset_inv SX" "vset_inv TX"
    by(rule correct(3,4,8,1,2))+
  show "vset SX = S (to_set X)" "vset TX = T (to_set X)" 
    "graph.digraph_abs G = A1 (to_set X) \<union> A2 (to_set X)"
    by(rule meaning(1,2,3))+
  thus "vset SX \<subseteq> carrier" "vset TX \<subseteq> carrier" "dVs (graph.digraph_abs G) \<subseteq> carrier"
    using S_in_carrier[OF assms(3,4)] T_in_carrier[OF assms(3,4)] dVs_A1A2_carrier[OF assms(3,4)]
    by simp_all
qed

text \<open>Both path searches satisfy the specification of the path loop.\<close>

lemma aux_path_spec:
  assumes "set_invar X" "to_set X \<subseteq> carrier" "indep1 (to_set X)" "indep2 (to_set X)"
  shows "aux_path X = None \<longleftrightarrow> 
           (\<nexists> p u v. (vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p v \<or> (p = [u] \<and> u = v)) \<and>
                       u \<in> S (to_set X) \<and> v \<in> T (to_set X))"
    "aux_path X = Some p \<Longrightarrow> \<exists> u v. (vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p v \<or> (p = [u] \<and> u = v))
                  \<and> u \<in> S (to_set X) \<and> v \<in> T (to_set X) \<and>
             (\<nexists> p'. (vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p' v \<or> (p' = [u] \<and> u = v))
                         \<and> length p' < length p)"
proof-
  obtain SX TX G where fields: "compute_graph X (complement X) = (SX, TX, G)"
    by(rule prod_cases3)
  note props = compute_graph_aux_graph[OF assms fields]
  have path: "aux_path X = find_path SX TX G"
    by(simp add: aux_path_def fields)
  show "aux_path X = None \<longleftrightarrow> 
           (\<nexists> p u v. (vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p v \<or> (p = [u] \<and> u = v)) \<and>
                       u \<in> S (to_set X) \<and> v \<in> T (to_set X))"
    using find_path(1)[OF props(1-8)] by(simp only: path props(9-11))
  show "aux_path X = Some p \<Longrightarrow> \<exists> u v. (vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p v \<or> (p = [u] \<and> u = v))
                  \<and> u \<in> S (to_set X) \<and> v \<in> T (to_set X) \<and>
             (\<nexists> p'. (vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p' v \<or> (p' = [u] \<and> u = v))
                         \<and> length p' < length p)"
    using find_path(2)[OF props(1-8)] by(simp only: path props(9-11))
qed

lemma aux_path_circuit_spec:
  assumes "set_invar X" "to_set X \<subseteq> carrier" "indep1 (to_set X)" "indep2 (to_set X)"
  shows "aux_path_circuit X = None \<longleftrightarrow> 
           (\<nexists> p u v. (vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p v \<or> (p = [u] \<and> u = v)) \<and>
                       u \<in> S (to_set X) \<and> v \<in> T (to_set X))"
    "aux_path_circuit X = Some p \<Longrightarrow> \<exists> u v. (vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p v \<or> (p = [u] \<and> u = v))
                  \<and> u \<in> S (to_set X) \<and> v \<in> T (to_set X) \<and>
             (\<nexists> p'. (vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p' v \<or> (p' = [u] \<and> u = v))
                         \<and> length p' < length p)"
proof-
  obtain SX TX G where fields: "compute_graph_circuit X (complement X) = (SX, TX, G)"
    by(rule prod_cases3)
  note props = compute_graph_circuit_aux_graph[OF assms fields]
  have path: "aux_path_circuit X = find_path SX TX G"
    by(simp add: aux_path_circuit_def fields)
  show "aux_path_circuit X = None \<longleftrightarrow> 
           (\<nexists> p u v. (vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p v \<or> (p = [u] \<and> u = v)) \<and>
                       u \<in> S (to_set X) \<and> v \<in> T (to_set X))"
    using find_path(1)[OF props(1-8)] by(simp only: path props(9-11))
  show "aux_path_circuit X = Some p \<Longrightarrow> \<exists> u v. (vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p v \<or> (p = [u] \<and> u = v))
                  \<and> u \<in> S (to_set X) \<and> v \<in> T (to_set X) \<and>
             (\<nexists> p'. (vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p' v \<or> (p' = [u] \<and> u = v))
                         \<and> length p' < length p)"
    using find_path(2)[OF props(1-8)] by(simp only: path props(9-11))
qed

sublocale unweighted_intersection_path_loop
  where augmenting_path = aux_path
  by(unfold_locales) (fact set_insert set_delete set_empty aux_path_spec)+

sublocale circuit: unweighted_intersection_path_loop
  where augmenting_path = aux_path_circuit
  by(unfold_locales) (fact set_insert set_delete set_empty aux_path_circuit_spec)+

lemmas matroid_intersection_circuit_correctness = circuit.matroid_intersection_correctness
lemmas matroid_intersection_circuit_total_correctness = circuit.matroid_intersection_total_correctness
lemmas same_results = same_result circuit.same_result

lemmas effect_of_augmentation = effect_of_augmentation[folded augment_def]

end
end