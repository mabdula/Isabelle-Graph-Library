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
fixes sel ::"'m \<Rightarrow> 'a"

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
locale Adj_Map_Specs = 
 adj: Map 
 where update = update and invar = adj_inv +


 neighb: Set_Choose
 where empty = neighb_empty and delete = neighb_delete and insert = neighb_insert and invar = neighb_inv
      and isin = isin

 for update :: "'a \<Rightarrow> 'neighb \<Rightarrow> 'adj \<Rightarrow> 'adj" and adj_inv :: "'adj \<Rightarrow> bool"  and

     neighb_empty :: "'neighb"  ("\<emptyset>\<^sub>N") and neighb_delete :: "'a \<Rightarrow> 'neighb \<Rightarrow> 'neighb" and
     neighb_insert and neighb_inv and isin


  \<comment> \<open>Why do we need ann efficient neghbourhood test?\<close>


begin


end
*)

no_notation digraph ("digraph")


named_theorems Graph_Spec_Elims
named_theorems Graph_Spec_Intros
named_theorems Graph_Spec_Simps

locale  Pair_Graph_Specs = 
 adj: Map 
 where update = update and invar = adj_inv +


 neighb: Set_Choose
 where empty = neighb_empty and delete = neighb_delete and invar = neighb_inv

 for update :: "'v \<Rightarrow> 'neighb \<Rightarrow> 'adj \<Rightarrow> 'adj" and adj_inv :: "'adj \<Rightarrow> bool"  and

     neighb_empty :: "'neighb" and neighb_delete :: "'v \<Rightarrow> 'neighb \<Rightarrow> 'neighb" and
     neighb_inv
(*  Adj_Map_Specs where update = update
for update :: "'a \<Rightarrow> 'neighb \<Rightarrow> 'adj \<Rightarrow> 'adj"*) 
begin

notation neighb_empty ("\<emptyset>\<^sub>N")
notation empty ("\<emptyset>\<^sub>G")

abbreviation isin' (infixl "\<in>\<^sub>G" 50) where "isin' G v \<equiv> isin v G" 
abbreviation not_isin' (infixl "\<notin>\<^sub>G" 50) where "not_isin' G v \<equiv> \<not> isin' G v"

definition "set_of_map (m::'adj) \<equiv> {(u,v). case (lookup m u) of Some vs \<Rightarrow> v \<in>\<^sub>G vs}"

definition "graph_inv G \<equiv> (adj_inv G \<and> (\<forall>v neighb. lookup G v = Some neighb \<longrightarrow> neighb_inv neighb))"
definition "finite_graph G \<equiv> (finite {v. (lookup G v) \<noteq> None})"
definition "finite_neighbs \<equiv> (\<forall>N. finite (t_set N))"


definition neighbourhood::"'adj \<Rightarrow> 'v \<Rightarrow> 'neighb" where
  "neighbourhood G v \<equiv> (case (lookup G v) of Some neighb \<Rightarrow> neighb | _ \<Rightarrow> neighb_empty)"

notation "neighbourhood" ("\<N>\<^sub>G _ _" 100)

definition digraph_abs ("[_]\<^sub>g") where "digraph_abs G \<equiv> {(u,v). v \<in>\<^sub>G (\<N>\<^sub>G G u)}" 

definition "add_edge G u v \<equiv> 
( 
  case (lookup G u) of Some neighb \<Rightarrow> 
  let
    neighb = the (lookup G u);
    neighb' = insert v neighb;
    digraph' = update u neighb' G
  in
    digraph'
  | _ \<Rightarrow>
  let
    neighb' = insert v neighb_empty;
    digraph' = update u neighb' G
  in
    digraph'
 
)"

definition "delete_edge G u v \<equiv> 
( 
  case (lookup G u) of Some neighb \<Rightarrow> 
  let
    neighb = the (lookup G u);
    neighb' = neighb_delete v neighb;
    digraph' = update u neighb' G
  in
    digraph'
  | _ \<Rightarrow> G 
)"



context \<comment>\<open>Locale properties\<close>
  includes adj.automation neighb.set.automation
  fixes G::'adj
  (*assumes [simp]:"axioms G"*)
begin

lemma graph_invE[elim]: 
  "graph_inv G \<Longrightarrow> (\<lbrakk>adj_inv G; (\<And>v neighb. lookup G v = Some neighb \<Longrightarrow> neighb_inv neighb)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: graph_inv_def)

(*end*)

(*context \<comment>\<open>Locale properties\<close>
  includes automation
  fixes G::'adj
  (*assumes [simp]:"axioms G"*)
begin*)

lemma graph_invI[intro]: 
  "\<lbrakk>adj_inv G; (\<And>v neighb. lookup G v = Some neighb \<Longrightarrow> neighb_inv neighb)\<rbrakk> \<Longrightarrow> graph_inv G"
  by (auto simp: graph_inv_def)

lemma finite_graphE[elim]: 
  "finite_graph G \<Longrightarrow> (finite {v. (lookup G v) \<noteq> None} \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: finite_graph_def)

lemma finite_graphI[intro]: 
  "finite {v. (lookup G v) \<noteq> None}  \<Longrightarrow> finite_graph G"
  by (auto simp: finite_graph_def)

lemma finite_neighbsE[elim]: 
  "finite_neighbs \<Longrightarrow> ((\<And>N. finite (t_set N)) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: finite_neighbs_def)

lemma finite_neighbsI[intro]: 
  "(\<And>N. finite (t_set N)) \<Longrightarrow> finite_neighbs"
  by (auto simp: finite_neighbs_def)


lemma neighbourhood_invars'[simp,dest]:
   "graph_inv G \<Longrightarrow> neighb_inv (\<N>\<^sub>G G v)"
  by (auto simp add: graph_inv_def neighbourhood_def split: option.splits)


lemma finite_graph[intro!]:
  assumes "graph_inv G" "finite_graph G" "finite_neighbs"
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
    by (force elim!: finite_neighbsE finite_graphE
              intro!: finite_imageI 
                      rev_finite_subset
                        [where B = "(the o lookup G) ` {v. \<exists>y. lookup G v = Some y}"])
  ultimately show ?thesis
    by(fastforce intro!: finite_cartesian_product dest: finite_subset)+

qed

corollary finite_vertices[intro!]:
  assumes "graph_inv G" "finite_graph G" "finite_neighbs"
  shows "finite (dVs (digraph_abs G))"
  using finite_graph[OF assms]
  by (simp add: finite_vertices_iff)

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

lemma adj_inv_insert[intro]: "graph_inv G \<Longrightarrow> graph_inv (add_edge G u v)"
  by (auto simp: add_edge_def graph_inv_def split: option.splits)

lemma digraph_abs_insert[simp]: "graph_inv G \<Longrightarrow> digraph_abs (add_edge G u v) = Set.insert (u,v) (digraph_abs G)"
  by (fastforce simp add: digraph_abs_def set_of_map_def neighbourhood_def add_edge_def split: option.splits if_splits)

lemma adj_inv_delete[intro]: "graph_inv G \<Longrightarrow> graph_inv (delete_edge G u v)"
  by (auto simp: delete_edge_def graph_inv_def split: option.splits)

lemma digraph_abs_delete[simp]:  "graph_inv G \<Longrightarrow> digraph_abs (delete_edge G u v) = (digraph_abs G) - {(u,v)}"
  by (fastforce simp add: digraph_abs_def set_of_map_def neighbourhood_def delete_edge_def split: option.splits if_splits)


end \<comment> \<open>Properties context\<close>  

end text \<open>@{const Pair_Graph_Specs}\<close>




end