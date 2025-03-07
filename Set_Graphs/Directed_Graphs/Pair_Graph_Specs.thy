theory Pair_Graph_Specs
  imports Awalk "Map_Addons" "Set_Addons"
 begin

section \<open>Locale for Executable Functions on Directed Graphs\<close>

text \<open>We develop a locale modelling an abstract data type (ADT) which abstractly models a graph as an
      adjacency map: i.e.\ every vertex is mapped to a \<open>set\<close> of adjacent vertices, and this latter
      set is again modelled using the ADT of sets provided in Isabelle/HOL's distribution.

      We then show that this ADT can be implemented using existing implementations of the \<open>set\<close> ADT.
\<close>

(*
record ('a, 's) Set_Rec = empty :: "'s" insert :: "'a \<Rightarrow> 's \<Rightarrow> 's" delete :: "'a \<Rightarrow> 's \<Rightarrow> 's"
                          isin :: "'s \<Rightarrow> 'a \<Rightarrow> bool" set :: "'s \<Rightarrow> 'a set" invar :: "'s \<Rightarrow> bool"

locale Set_Rec =
  fixes set_rec:: "('a,'s) Set_Rec"
  assumes "Set (empty set_rec) (insert set_rec) (delete set_rec) (isin set_rec)
               (set set_rec) (invar set_rec)"
    
record ('a,'s) Set_Choose_Rec = "('a,'s) Set_Rec" + sel :: "'s \<Rightarrow> 'a"



locale Set_Choose = Set_Rec set_rec
  for set_rec::"('a,'m) Set_Rec" + 

fixes sel ::"'m \<Rightarrow> 'a"
assumes choose: "s \<noteq> (empty set_rec) \<Longrightarrow> (isin set_rec) s (sel s)"
begin


locale Set_Map = Set
  where set = t_set for t_set +
fixes t_map ::"('a \<Rightarrow> 'a) \<Rightarrow> 'm \<Rightarrow> 'm"
assumes map: "bij_betw f (t_set s) t  \<Longrightarrow> t_set (t_map f s) = t"
*)

locale Set_Choose = set: Set 
  where set = t_set for t_set ("[_]\<^sub>s") +
fixes sel ::"'s \<Rightarrow> 'a"

assumes choose [simp]: "s \<noteq> empty \<Longrightarrow> isin s (sel s)"


begin
context
  includes set.automation
begin

(*
declare set_empty[simp] set_isin[simp] set_insert[simp] set_delete[simp]
        invar_empty[simp] invar_insert[simp] invar_delete[simp] choose[simp]
*)

subsection \<open>Abstraction lemmas\<close>

text \<open>These are lemmas for automation. Their purpose is to remove any mention of the locale set ADT
      constructs and replace it with Isabelle's native sets.\<close>

lemma choose'[simp, intro,dest]:
  "s \<noteq> empty \<Longrightarrow> invar s \<Longrightarrow> sel s \<in> t_set s"
  by(auto simp flip: set.set_isin)

lemma choose''[intro]:
  "invar s \<Longrightarrow> s \<noteq> empty \<Longrightarrow> t_set s \<subseteq> s' \<Longrightarrow> sel s \<in> s'"
  by(auto simp flip: set.set_isin)

lemma emptyD[dest]:
           "s = empty \<Longrightarrow> t_set s = {}"
           "s \<noteq> empty \<Longrightarrow> invar s \<Longrightarrow> t_set s \<noteq> {}"
           "empty = s \<Longrightarrow> t_set s = {}"
           "empty \<noteq> s \<Longrightarrow> invar s \<Longrightarrow> t_set s \<noteq> {}"
 using set.set_empty
 by auto
end
end
(*
locale Adjmap_Map_Specs = 
 adjmap: Map 
 where update = update and invar = adjmap_inv +


 vset: Set_Choose
 where empty = vset_empty and delete = vset_delete and insert = vset_insert and invar = vset_inv
      and isin = isin

 for update :: "'a \<Rightarrow> 'vset \<Rightarrow> 'adjmap \<Rightarrow> 'adjmap" and adjmap_inv :: "'adjmap \<Rightarrow> bool"  and

     vset_empty :: "'vset"  ("\<emptyset>\<^sub>N") and vset_delete :: "'a \<Rightarrow> 'vset \<Rightarrow> 'vset" and
     vset_insert and vset_inv and isin


  \<comment> \<open>Why do we need ann efficient neghbourhood test?\<close>


begin


end
*)

no_notation digraph ("digraph")


named_theorems Graph_Spec_Elims
named_theorems Graph_Spec_Intros
named_theorems Graph_Spec_Simps

locale Pair_Graph_Specs = 
 adjmap: Map 
 where update = update and invar = adjmap_inv +


 vset: Set_Choose
 where empty = vset_empty and delete = vset_delete and invar = vset_inv

 for update :: "'v \<Rightarrow> 'vset \<Rightarrow> 'adjmap \<Rightarrow> 'adjmap" and adjmap_inv :: "'adjmap \<Rightarrow> bool"  and

     vset_empty :: "'vset" and vset_delete :: "'v \<Rightarrow> 'vset \<Rightarrow> 'vset" and
     vset_inv
(*  Adjmap_Map_Specs where update = update
for update :: "'a \<Rightarrow> 'vset \<Rightarrow> 'adjmap \<Rightarrow> 'adjmap"*) 
begin

notation vset_empty ("\<emptyset>\<^sub>N")
notation empty ("\<emptyset>\<^sub>G")

abbreviation isin' (infixl "\<in>\<^sub>G" 50) where "isin' G v \<equiv> isin v G" 
abbreviation not_isin' (infixl "\<notin>\<^sub>G" 50) where "not_isin' G v \<equiv> \<not> isin' G v"

definition "set_of_map (m::'adjmap) = {(u,v). case (lookup m u) of Some vs \<Rightarrow> v \<in>\<^sub>G vs}"

definition "graph_inv G = (adjmap_inv G \<and> (\<forall>v vset. lookup G v = Some vset \<longrightarrow> vset_inv vset))"
definition "finite_graph G = (finite {v. (lookup G v) \<noteq> None})"
definition "finite_vsets = (\<forall>N. finite (t_set N))"

lemma graph_inv_empty: "graph_inv \<emptyset>\<^sub>G"
  by (simp add: adjmap.invar_empty adjmap.map_empty graph_inv_def)

definition neighbourhood::"'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset" where
  "(neighbourhood G v) = (case (lookup G v) of Some vset \<Rightarrow> vset | _ \<Rightarrow> vset_empty)"

notation "neighbourhood" ("\<N>\<^sub>G _ _" 100)

definition digraph_abs ("[_]\<^sub>g") where "digraph_abs G = {(u,v). v \<in>\<^sub>G (\<N>\<^sub>G G u)}" 

lemma digraph_abs_empty: "digraph_abs empty = {}" 
  by (simp add: adjmap.map_empty digraph_abs_def local.neighbourhood_def vset.set.invar_empty vset.set.set_empty vset.set.set_isin)

definition "add_edge G u v =
( 
  case (lookup G u) of Some vset \<Rightarrow> 
  let
    vset = the (lookup G u);
    vset' = insert v vset;
    digraph' = update u vset' G
  in
    digraph'
  | _ \<Rightarrow>
  let
    vset' = insert v vset_empty;
    digraph' = update u vset' G
  in
    digraph'
)"

definition "delete_edge G u v =
( 
  case (lookup G u) of Some vset \<Rightarrow> 
  let
    vset = the (lookup G u);
    vset' = vset_delete v vset;
    digraph' = update u vset' G
  in
    digraph'
  | _ \<Rightarrow> G 
)"

lemmas [code] = neighbourhood_def add_edge_def delete_edge_def

context \<comment>\<open>Locale properties\<close>
  includes vset.set.automation  adjmap.automation
  fixes G::'adjmap
begin

lemma graph_invE[elim]: 
  "graph_inv G \<Longrightarrow> (\<lbrakk>adjmap_inv G; (\<And>v vset. lookup G v = Some vset \<Longrightarrow> vset_inv vset)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: graph_inv_def)

lemma graph_invI[intro]: 
  "\<lbrakk>adjmap_inv G; (\<And>v vset. lookup G v = Some vset \<Longrightarrow> vset_inv vset)\<rbrakk> \<Longrightarrow> graph_inv G"
  by (auto simp: graph_inv_def)

lemma finite_graphE[elim]: 
  "finite_graph G \<Longrightarrow> (finite {v. (lookup G v) \<noteq> None} \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: finite_graph_def)

lemma finite_graphI[intro]: 
  "finite {v. (lookup G v) \<noteq> None}  \<Longrightarrow> finite_graph G"
  by (auto simp: finite_graph_def)

lemma finite_vsetsE[elim]: 
  "finite_vsets \<Longrightarrow> ((\<And>N. finite (t_set N)) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: finite_vsets_def)

lemma finite_vsetsI[intro]: 
  "(\<And>N. finite (t_set N)) \<Longrightarrow> finite_vsets"
  by (auto simp: finite_vsets_def)


lemma neighbourhood_invars'[simp,dest]:
   "graph_inv G \<Longrightarrow> vset_inv (\<N>\<^sub>G G v)"
  by (auto simp add: graph_inv_def neighbourhood_def split: option.splits)


lemma finite_graph[intro!]:
  assumes "graph_inv G" "finite_graph G" "finite_vsets"
  shows "finite (digraph_abs G)"
proof-

  have "digraph_abs G \<subseteq> {v. lookup G v \<noteq> None} \<times> (\<Union> (t_set ` {N | N v. lookup G v = Some N}))"
    using assms 
    by (fastforce simp: digraph_abs_def neighbourhood_def graph_inv_def split: option.splits)

  moreover have "finite {v. lookup G v \<noteq> None}"
    using assms
    by fastforce

  moreover have "finite (\<Union> (t_set ` {N | N v. lookup G v = Some N}))"
    using assms
    by (force elim!: finite_vsetsE finite_graphE
              intro!: finite_imageI 
                      rev_finite_subset
                        [where B = "(the o lookup G) ` {v. \<exists>y. lookup G v = Some y}"])
  ultimately show ?thesis
    by(fastforce intro!: finite_cartesian_product dest: finite_subset)+

qed

corollary finite_vertices[intro!]:
  assumes "graph_inv G" "finite_graph G" "finite_vsets"
  shows "finite (dVs (digraph_abs G))"
  using finite_graph[OF assms]
  by (simp add: finite_vertices_iff)

lemma finite_empty: "finite_graph empty"
  by (simp add: finite_graph_def)

subsection \<open>Abstraction lemmas\<close>

text \<open>These are lemmas for automation. Their purpose is to remove any mention of the neighbourhood
      concept implemented using the locale constructs and replace it with abstract terms
      on pair graphs.\<close>

lemma are_connected_abs[simp]: 
  "graph_inv G \<Longrightarrow> v \<in> t_set (\<N>\<^sub>G G u) \<longleftrightarrow> (u,v) \<in> digraph_abs G"
  by(auto simp: digraph_abs_def neighbourhood_def option.discI graph_inv_def
          split: option.split)

lemma are_connected_absD[dest]: 
  "\<lbrakk>v \<in> t_set (\<N>\<^sub>G G u); graph_inv G\<rbrakk> \<Longrightarrow> (u,v) \<in> digraph_abs G"
  by (auto simp: are_connected_abs)

lemma are_connected_absI[intro]: 
  "\<lbrakk>(u,v) \<in> digraph_abs G; graph_inv G\<rbrakk> \<Longrightarrow> v \<in> t_set (\<N>\<^sub>G G u)"
  by (auto simp: are_connected_abs)

lemma neighbourhood_absD[dest!]:
  "\<lbrakk>t_set (\<N>\<^sub>G G x) \<noteq> {}; graph_inv G\<rbrakk> \<Longrightarrow> x \<in> dVs (digraph_abs G)"
  by blast

lemma neighbourhood_abs[simp]:
  "graph_inv G \<Longrightarrow> t_set (\<N>\<^sub>G G u) = Pair_Graph.neighbourhood (digraph_abs G) u"
  by(auto simp: digraph_abs_def neighbourhood_def Pair_Graph.neighbourhood_def option.discI graph_inv_def
          split: option.split)

lemma adjmap_inv_insert[intro]: "graph_inv G \<Longrightarrow> graph_inv (add_edge G u v)"
  by (auto simp: add_edge_def graph_inv_def split: option.splits)

lemma digraph_abs_insert[simp]: "graph_inv G \<Longrightarrow> digraph_abs (add_edge G u v) = Set.insert (u,v) (digraph_abs G)"
  by (fastforce simp add: digraph_abs_def set_of_map_def neighbourhood_def add_edge_def split: option.splits if_splits)

lemma adjmap_inv_delete[intro]: "graph_inv G \<Longrightarrow> graph_inv (delete_edge G u v)"
  by (auto simp: delete_edge_def graph_inv_def split: option.splits)

lemma digraph_abs_delete[simp]:  "graph_inv G \<Longrightarrow> digraph_abs (delete_edge G u v) = (digraph_abs G) - {(u,v)}"
  by (fastforce simp add: digraph_abs_def set_of_map_def neighbourhood_def delete_edge_def split: option.splits if_splits)

lemma finite_graph_add_edge: assumes "graph_inv G" "finite_graph G" 
  shows "finite_graph (add_edge G u v)"
proof-
  have adjmap_inv: "adjmap_inv G" 
    using assms by auto
  have dom_is: "{va. lookup (add_edge G u v) va \<noteq> None} = Set.insert u {va. lookup G va \<noteq> None}" 
    by(auto split: option.split simp add: adjmap.map_update[OF adjmap_inv] add_edge_def)
  show ?thesis
    using assms(2)
    by(unfold finite_graph_def dom_is) auto
qed

end \<comment> \<open>Properties context\<close>  

end text \<open>@{const Pair_Graph_Specs}\<close>

locale Pair_Graph_Specs_Reverse =
pair_graph_specs: Pair_Graph_Specs where lookup=lookup 
for lookup :: "'adjmap \<Rightarrow> 'ver \<Rightarrow> 'vset option" +
fixes fold_vset::"('ver \<Rightarrow> 'adjmap \<Rightarrow> 'adjmap) \<Rightarrow> 'vset \<Rightarrow> 'adjmap \<Rightarrow> 'adjmap"
fixes fold_adjmap::"('ver \<Rightarrow> 'vset \<Rightarrow> 'adjmap \<Rightarrow> 'adjmap) \<Rightarrow> 'adjmap \<Rightarrow> 'adjmap \<Rightarrow> 'adjmap"
assumes fold_vset:"\<And> N f acc. vset_inv N \<Longrightarrow> \<exists> xs. set xs = t_set N \<and> fold_vset f N acc = foldr f xs acc"
assumes fold_adjmap:"\<And> N f acc. adjmap_inv N \<Longrightarrow> \<exists> xs. set xs = dom (lookup N) \<and>
                        fold_adjmap f N acc = foldr (\<lambda> x acc. f x (the (lookup N x)) acc) xs acc" 
begin

lemmas [code] = pair_graph_specs.add_edge_def

abbreviation "add_edge == pair_graph_specs.add_edge"

definition "reverse_neighbourhood x N G = (fold_vset (\<lambda> y acc. add_edge acc y x) N G)"

definition "reverse_graph G = (fold_adjmap reverse_neighbourhood G empty)"

abbreviation "graph_inv == pair_graph_specs.graph_inv"
abbreviation "finite_graph == pair_graph_specs.finite_graph"
abbreviation "digraph_abs == pair_graph_specs.digraph_abs"

lemma reverse_neighbourhood_correct:
  assumes "graph_inv Gacc" "vset_inv N"
  shows   "graph_inv (reverse_neighbourhood x N Gacc)"
          "finite_graph Gacc \<Longrightarrow> finite_graph (reverse_neighbourhood x N Gacc)"
          "digraph_abs (reverse_neighbourhood x N Gacc) = digraph_abs Gacc \<union> {(y, x) | y. y \<in>t_set N}"
proof-
  obtain xs where xs_prop: "set xs = [N]\<^sub>s" 
     "fold_vset (\<lambda>y acc. add_edge acc y x) N Gacc = foldr (\<lambda>y acc. add_edge acc y x) xs Gacc"
    using fold_vset[OF assms(2), of "\<lambda> y acc. add_edge acc y x" Gacc] by auto
  have graph_inv_fold:"graph_inv(foldr (\<lambda>y acc. add_edge acc y x) xs Gacc)" for xs
    by(induction xs)(auto simp add: assms(1))
  show "graph_inv (reverse_neighbourhood x N Gacc)"
    by(simp add: reverse_neighbourhood_def graph_inv_fold xs_prop(2))
  have finite_graph_fold:"finite_graph Gacc \<Longrightarrow> finite_graph (foldr (\<lambda>y acc. add_edge acc y x) xs Gacc)" for xs
   by(induction xs)(auto intro:pair_graph_specs.finite_graph_add_edge simp add: graph_inv_fold)
  show "finite_graph Gacc \<Longrightarrow> finite_graph (reverse_neighbourhood x N Gacc)"
    by(simp add: reverse_neighbourhood_def finite_graph_fold xs_prop(2))
  have "[foldr (\<lambda>y acc. add_edge acc y x) xs Gacc]\<^sub>g = [Gacc]\<^sub>g \<union> {(y, x) |y. y \<in> [N]\<^sub>s}"
    unfolding xs_prop(1)[symmetric]
    by(induction xs)(auto simp add: graph_inv_fold)
  thus "[reverse_neighbourhood x N Gacc]\<^sub>g = [Gacc]\<^sub>g \<union> {(y, x) |y. y \<in> [N]\<^sub>s}"
    using reverse_neighbourhood_def xs_prop(2) by presburger
qed

lemma reverse_graph_correct:
  assumes "graph_inv G" 
  shows   "graph_inv (reverse_graph G)"
          "finite_graph (reverse_graph G)"
          "digraph_abs (reverse_graph G) = {(y, x) | x y. (x, y) \<in> digraph_abs G}"
proof-
  have adj_map_inv_G: "adjmap_inv G"
    using assms by blast
  obtain xs where xs_prop: "set xs = dom (lookup G)"
     "fold_adjmap reverse_neighbourhood G \<emptyset>\<^sub>G = 
        foldr (\<lambda>x. reverse_neighbourhood x (the (lookup G x))) xs \<emptyset>\<^sub>G"
    using fold_adjmap[OF adj_map_inv_G, of reverse_neighbourhood empty] by auto
  have graph_inv_fold:"set xs  \<subseteq> dom (lookup G) \<Longrightarrow> graph_inv (foldr (\<lambda>x. reverse_neighbourhood x (the (lookup G x))) xs \<emptyset>\<^sub>G)" for xs
    by(induction xs)
      (auto intro!: reverse_neighbourhood_correct(1) intro: pair_graph_specs.graph_invE[OF assms]
                 simp add: pair_graph_specs.graph_inv_empty)
  show "graph_inv (reverse_graph G)"
    by(simp add: reverse_graph_def graph_inv_fold xs_prop)
  have finite_graph_fold:"set xs  \<subseteq> dom (lookup G) \<Longrightarrow> finite_graph 
                     (foldr (\<lambda>x. reverse_neighbourhood x (the (lookup G x))) xs \<emptyset>\<^sub>G)" for xs
    using assms 
    by(induction xs)
      (auto intro: pair_graph_specs.finite_graph_add_edge intro!: 
         reverse_neighbourhood_correct(2) simp add: graph_inv_fold pair_graph_specs.finite_empty)
  show "finite_graph (reverse_graph G)" 
    by(simp add: reverse_graph_def finite_graph_fold xs_prop)
  have "set xs  \<subseteq> dom (lookup G) \<Longrightarrow> 
  [(foldr (\<lambda>x. reverse_neighbourhood x (the (lookup G x))) xs \<emptyset>\<^sub>G)]\<^sub>g 
     = {(y, x) | x y. x \<in> set xs \<and> y \<in> t_set (the (lookup G x))}"
    using assms 
    by (induction xs)
       (force simp add: pair_graph_specs.digraph_abs_empty reverse_neighbourhood_correct(3) domIff graph_inv_fold)+
  moreover have "{(y, x) | x y. x \<in> set xs \<and> y \<in> t_set (the (lookup G x))}
                  = {(y, x) |x y. (x, y) \<in> [G]\<^sub>g}" 
    using  xs_prop(1) assms  pair_graph_specs.vset.set.set_isin  pair_graph_specs.vset.emptyD(1) pair_graph_specs.vset.set.invar_empty 
    by (auto simp add: pair_graph_specs.neighbourhood_def xs_prop(2) pair_graph_specs.digraph_abs_def )
       (auto | rule option.exhaust[of "lookup G x" "y \<in> [the (lookup G x)]\<^sub>s" for x y])+
  ultimately show "[reverse_graph G]\<^sub>g = {(y, x) |x y. (x, y) \<in> [G]\<^sub>g}" 
    using  xs_prop(1) by(auto simp add: reverse_graph_def xs_prop(2) pair_graph_specs.digraph_abs_def)
qed

end


end