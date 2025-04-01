theory BFS_Subprocedures
  imports BFS_2 "HOL-Data_Structures.RBT_Map" Directed_Set_Graphs.Set_Addons 
begin

locale Pair_Graph_Sepcs_Set2 =
  Graph: Pair_Graph_Specs
    where lookup = lookup +
  set_ops: Set2 vset_empty vset_delete _ t_set vset_inv insert
for lookup :: "'adjmap \<Rightarrow> 'ver \<Rightarrow> 'vset option"
begin

definition "add_neighbs G u vs = (if vs = vset_empty then G else 
                                  (case (lookup G u) of None \<Rightarrow> update u vs G
                                  | Some vs' \<Rightarrow> update u (union vs' vs) G))"

lemmas [code] = add_neighbs_def

lemma add_neighbs_inv: assumes "Graph.graph_inv G" "vset_inv vs"
  shows  "Graph.graph_inv (add_neighbs G u vs)" 
         "Graph.finite_graph G \<Longrightarrow> Graph.finite_graph (add_neighbs G u vs)"
proof-
  note 1 = assms
  have b: "vset_inv vs \<Longrightarrow>
       \<forall>v vset. lookup G v = Some vset \<longrightarrow> vset_inv vset \<Longrightarrow>
       lookup G u = Some x2 \<Longrightarrow> (if v = u then Some (x2 \<union>\<^sub>G vs) else lookup G v) = Some vset 
        \<Longrightarrow> vset_inv vset " for v vset x2
    by(rule case_split[of "v = u"])( auto simp add: set_ops.invar_union)
  show  "Graph.graph_inv (add_neighbs G u vs)" 
    using 1
    by (auto split: if_split option.split 
             intro: Graph.adjmap.invar_update b
          simp add: Graph.adjmap.map_update Graph.graph_inv_def add_neighbs_def)
  show  "Graph.finite_graph G \<Longrightarrow> Graph.finite_graph (add_neighbs G u vs)"
    using 1
    by (auto split: if_split option.split 
             intro: Graph.adjmap.invar_update b
          simp add: Graph.adjmap.map_update Graph.graph_inv_def add_neighbs_def Graph.finite_graph_def
          finite_insert[of u "{v. \<exists>y. lookup G v = Some y}", symmetric]  insert_Collect)
qed

lemma add_neighbs_digraph_abs:
   "Graph.graph_inv G \<Longrightarrow> vset_inv vs \<Longrightarrow> Graph.digraph_abs (add_neighbs G u vs) =
    Graph.digraph_abs G \<union> {(u, v) | v. v  \<in> t_set vs}"
proof(goal_cases)
  case 1
  have a: "vset_inv vs \<Longrightarrow>
       \<forall>v vset. lookup G v = Some vset \<longrightarrow> vset_inv vset \<Longrightarrow>
       lookup G u = Some x2 \<Longrightarrow>
       b \<in> [case if a = u then Some (x2 \<union>\<^sub>G vs) else lookup G a of None \<Rightarrow> \<emptyset>\<^sub>N | Some vset \<Rightarrow> vset]\<^sub>s \<Longrightarrow>
       b \<notin> [vs]\<^sub>s \<Longrightarrow> lookup G a = Some x2a \<Longrightarrow> b \<in> [x2a]\<^sub>s" for a b x2 x2a
    by (auto intro: case_split[of "a = u"] simp add: set_ops.set_union)
  have b: "\<forall>v vset. lookup G v = Some vset \<longrightarrow> vset_inv vset \<Longrightarrow>
       lookup G u = Some x2 \<Longrightarrow>
       b \<in> [case if a = u then Some (x2 \<union>\<^sub>G vs) else lookup G a of None \<Rightarrow> \<emptyset>\<^sub>N | Some vset \<Rightarrow> vset]\<^sub>s \<Longrightarrow>
       b \<notin> [vs]\<^sub>s \<Longrightarrow> \<exists>y. lookup G a = Some y" for a b x2 x2a 
    using Graph.vset.emptyD(1) domIff by (fastforce intro: case_split[of "a = u"])
  have c: "b \<in> [case if a = u then Some vs else lookup G a of None \<Rightarrow> \<emptyset>\<^sub>N | Some vset \<Rightarrow> vset]\<^sub>s \<Longrightarrow>
       b \<notin> [vs]\<^sub>s \<Longrightarrow> lookup G a = Some x2 \<Longrightarrow> b \<in> [x2]\<^sub>s" for a b x2
     by (fastforce intro: case_split[of "a = u"])
  have d: "\<forall>v vset. lookup G v = Some vset \<longrightarrow> vset_inv vset \<Longrightarrow>
           b \<in> [case if a = u then Some vs else lookup G a of None \<Rightarrow> \<emptyset>\<^sub>N | Some vset \<Rightarrow> vset]\<^sub>s \<Longrightarrow>
           b \<notin> [vs]\<^sub>s \<Longrightarrow> \<exists>y. lookup G a = Some y" for a b 
    using Graph.vset.emptyD(3) domIff by (fastforce intro: case_split[of "a = u"])
  show ?case 
    using 1  Graph.vset.set.set_empty 
    by(auto split: if_split option.split 
            simp add:  add_neighbs_def Graph.digraph_abs_def 
                      Graph.neighbourhood_def Graph.adjmap.map_update Graph.graph_inv_def
                      Graph.vset.emptyD(3) Graph.vset.set.invar_empty
                      Graph.vset.set.set_isin set_ops.invar_union set_ops.set_union)
      (insert Graph.vset.emptyD(3), auto intro: a b c d)   
qed
end





locale BFS_subprocedures =
Pair_Graph_Sepcs_Set2 where lookup=lookup 
for lookup :: "'adjmap \<Rightarrow> 'ver \<Rightarrow> 'vset option" +
fixes G::"'adjmap" 
fixes fold_vset::"('ver \<Rightarrow> 'vset \<Rightarrow> 'vset) \<Rightarrow> 'vset \<Rightarrow> 'vset \<Rightarrow> 'vset"
fixes fold_adjmap::"('ver \<Rightarrow> 'adjmap \<Rightarrow> 'adjmap) \<Rightarrow> 'vset \<Rightarrow> 'adjmap \<Rightarrow> 'adjmap"
assumes fold_vset:"\<And> N f acc. vset_inv N \<Longrightarrow> \<exists> xs. set xs = t_set N \<and> fold_vset f N acc = foldr f xs acc"
assumes fold_adjmap:"\<And> N f acc. vset_inv N \<Longrightarrow> \<exists> xs. set xs = t_set N \<and>
                        fold_adjmap f N acc = foldr f xs acc" 

begin

abbreviation "neighbourhood' \<equiv> Graph.neighbourhood G" 
notation "neighbourhood'" ("\<N>\<^sub>G _" 100)

definition next_frontier::"'vset \<Rightarrow> 'vset \<Rightarrow> 'vset"  where
"next_frontier frontier vis= 
   fold_vset (\<lambda> u nf. nf \<union>\<^sub>G ((\<N>\<^sub>G u) -\<^sub>G vis)) frontier \<emptyset>\<^sub>N"
declare Graph.vset.set.set_empty[simp] Graph.vset.set.set_isin[simp] Graph.vset.set.set_insert[simp]
        Graph.vset.set.set_delete[simp] Graph.vset.set.invar_empty[simp] 
        Graph.vset.set.invar_insert[simp] Graph.vset.set.invar_delete[simp]
context
  includes Graph.vset.set.automation and set_ops.automation
begin

lemma next_frontier:
    "\<lbrakk>vset_inv frontier; vset_inv vis; Graph.graph_inv G\<rbrakk> \<Longrightarrow>  vset_inv (next_frontier frontier vis)"
    "\<lbrakk>vset_inv frontier; vset_inv vis; Graph.graph_inv G\<rbrakk> \<Longrightarrow>
       t_set (next_frontier frontier vis) =
         (\<Union> {Pair_Graph.neighbourhood (Graph.digraph_abs G) u | u . u \<in> t_set frontier}) - t_set vis"
proof-
  assume assms: "vset_inv frontier" "vset_inv vis" "Graph.graph_inv G"
  have goal1_gen:"vset_inv (foldr (\<lambda>u nf. nf \<union>\<^sub>G (\<N>\<^sub>G u -\<^sub>G vis)) xs \<emptyset>\<^sub>N)" for xs
   using assms 
    by (induction xs)(auto split: option.split)

  have "[(\<N>\<^sub>G a -\<^sub>G vis)]\<^sub>s \<subseteq> foldr (\<lambda>u nf. nf \<union> [(\<N>\<^sub>G u -\<^sub>G vis)]\<^sub>s) xs {}" if "a \<in> set xs" for xs a
    using that
    by (induction xs) (auto simp add: assms(2) assms(3) goal1_gen in_mono)
  hence "foldr (\<lambda>u nf. nf \<union> [(\<N>\<^sub>G u -\<^sub>G vis)]\<^sub>s) xs {} =
                   foldr (\<lambda>u nf. nf \<union> [(\<N>\<^sub>G u -\<^sub>G vis)]\<^sub>s) (remdups xs) {}" for xs
    by(induction xs) auto
  moreover have "foldr (\<lambda>u nf. nf \<union> [(\<N>\<^sub>G u -\<^sub>G vis)]\<^sub>s) xs {} = [(foldr (\<lambda>u nf. nf \<union>\<^sub>G (\<N>\<^sub>G u -\<^sub>G vis)) xs \<emptyset>\<^sub>N)]\<^sub>s"  for xs
    by (induction xs)
       (simp add: assms(2) assms(3) goal1_gen)+
  ultimately have "[(foldr (\<lambda>u nf. nf \<union>\<^sub>G (\<N>\<^sub>G u -\<^sub>G vis)) xs \<emptyset>\<^sub>N)]\<^sub>s =
                      [(foldr (\<lambda>u nf. nf \<union>\<^sub>G (\<N>\<^sub>G u -\<^sub>G vis)) (remdups xs) \<emptyset>\<^sub>N)]\<^sub>s" for xs
    by auto
  moreover obtain xs where xs_props:
       "set xs = [frontier]\<^sub>s"
       "[next_frontier frontier vis]\<^sub>s =
          [foldr (\<lambda>u nf. nf \<union>\<^sub>G (\<N>\<^sub>G u -\<^sub>G vis)) xs \<emptyset>\<^sub>N]\<^sub>s"
    using fold_vset[OF assms(1)]
    by(auto simp add: next_frontier_def) metis  
  ultimately obtain xs' where xs'_props: 
       "set xs' = [frontier]\<^sub>s"
       "[next_frontier frontier vis]\<^sub>s =
           [foldr (\<lambda>u nf. nf \<union>\<^sub>G (\<N>\<^sub>G u -\<^sub>G vis)) xs' \<emptyset>\<^sub>N]\<^sub>s"
       "distinct xs'"
    using distinct_remdups set_remdups
    by (metis )
  moreover have "[foldr (\<lambda>u nf. nf \<union>\<^sub>G (\<N>\<^sub>G u -\<^sub>G vis)) xs' \<emptyset>\<^sub>N]\<^sub>s =
                    \<Union> {neighbourhood [G]\<^sub>g u |u. u \<in> set xs'} - [vis]\<^sub>s"
    by(induction xs')
      (auto simp add: Graph.vset.emptyD(1) assms(2) assms(3) goal1_gen)+

  ultimately show "[next_frontier frontier vis]\<^sub>s = \<Union> {neighbourhood [G]\<^sub>g u |u. u \<in> [frontier]\<^sub>s} - [vis]\<^sub>s"
    by presburger

  have "vset_inv (foldr (\<lambda>u nf. nf \<union>\<^sub>G (\<N>\<^sub>G u -\<^sub>G vis)) xs \<emptyset>\<^sub>N)" for xs
   using assms 
    by (induction xs)(auto split: option.split intro!: Cons)

  thus "vset_inv (next_frontier frontier vis)"
    apply (subst next_frontier_def)
    using fold_vset[OF assms(1)]
    by metis
qed

definition expand_tree::"'adjmap \<Rightarrow> 'vset \<Rightarrow> 'vset \<Rightarrow> 'adjmap" where
"expand_tree BFS_tree frontier vis = 
   fold_adjmap 
     (\<lambda> u nf. add_neighbs nf u (diff (neighbourhood' u) vis)) frontier BFS_tree"

lemma expand_tree:
     "\<lbrakk>Graph.graph_inv BFS_tree; vset_inv frontier; vset_inv vis; Graph.graph_inv G\<rbrakk> \<Longrightarrow> 
       Graph.graph_inv (expand_tree BFS_tree frontier vis)"
     "\<lbrakk>Graph.graph_inv BFS_tree; vset_inv frontier; vset_inv vis; Graph.graph_inv G\<rbrakk> \<Longrightarrow>
        Graph.digraph_abs (expand_tree BFS_tree frontier vis) = 
         (Graph.digraph_abs BFS_tree) \<union> 
         {(u,v) | u v. u \<in> t_set (frontier) \<and> 
                       v \<in> (Pair_Graph.neighbourhood (Graph.digraph_abs G) u -
                       t_set vis)}"
     "\<lbrakk>Graph.graph_inv BFS_tree; vset_inv frontier; vset_inv vis; Graph.graph_inv G;
       Graph.finite_graph BFS_tree\<rbrakk> \<Longrightarrow> 
       Graph.finite_graph (expand_tree BFS_tree frontier vis)"
proof-
  assume assms: "Graph.graph_inv BFS_tree" "vset_inv frontier" "vset_inv vis" "Graph.graph_inv G"
  obtain xs where xs_prop:
    "set xs = [frontier]\<^sub>s" "expand_tree BFS_tree frontier vis = foldr (\<lambda> u nf. add_neighbs nf u (diff (neighbourhood' u) vis)) xs BFS_tree"
    using fold_adjmap[OF assms(2), of _ BFS_tree]
    by (auto simp add: expand_tree_def)
  have goal1_general:"Graph.graph_inv (foldr  (\<lambda> u nf. add_neighbs nf u (diff (neighbourhood' u) vis))
                          xs BFS_tree)" for xs
  proof(induction xs)
    case Nil
    then show ?case using assms(1) by simp
  next
    case (Cons a xs)
    show ?case
      by (auto intro: Cons(1) add_neighbs_inv  simp add: assms(3) assms(4))
  qed
  thus " Graph.graph_inv (expand_tree BFS_tree frontier vis)"
    by (simp add: xs_prop(2))
  have one_it_graph_abs:"Graph.graph_inv T \<Longrightarrow> 
                 [(\<lambda> u nf. add_neighbs nf u (diff (neighbourhood' u) vis)) u T]\<^sub>g 
               = [T]\<^sub>g \<union> {(u, v) |v. v \<in> neighbourhood [G]\<^sub>g u - [vis]\<^sub>s}" for u T
    by(auto simp add: assms(3) assms(4) add_neighbs_digraph_abs)

  have "[foldr (\<lambda> u nf. add_neighbs nf u (diff (neighbourhood' u) vis)) xs BFS_tree]\<^sub>g = [BFS_tree]\<^sub>g \<union> {(u, v) |u v. u \<in> [frontier]\<^sub>s \<and> v \<in> neighbourhood [G]\<^sub>g u - [vis]\<^sub>s}"
    using xs_prop(1) assms(2)
  proof(induction xs arbitrary: frontier)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    show ?case 
    proof(cases "a \<in> set xs")
      case True
      have heper: "[foldr (\<lambda> u nf. add_neighbs nf u (diff (neighbourhood' u) vis)) xs BFS_tree]\<^sub>g \<union> {(a, v) |v. v \<in> neighbourhood [G]\<^sub>g a - [vis]\<^sub>s} =
    [BFS_tree]\<^sub>g \<union> {(u, v). u \<in> [frontier]\<^sub>s \<and> v \<in> neighbourhood [G]\<^sub>g u \<and> v \<notin> [vis]\<^sub>s}"
      using Cons.prems(1) True 
      by (subst Cons(1)[of frontier])(auto simp add: Cons.prems(2))
     show ?thesis 
       using goal1_general heper 
       by (auto simp add: one_it_graph_abs)
   next
     case False
     have del_set:"[vset_delete a frontier]\<^sub>s = set xs"
       using Cons.prems(1) Cons.prems(2) False Graph.vset.set.set_delete by auto
     show ?thesis
       using Cons.prems(1) Cons.prems(2) False Graph.vset.set.set_delete 
     by(auto simp add: one_it_graph_abs goal1_general Cons(1)[of "vset_delete a frontier"] Cons.prems(2) Graph.vset.set.invar_delete del_set sym[OF Cons(2)])
 qed
qed
  thus "[expand_tree BFS_tree frontier vis]\<^sub>g =
    [BFS_tree]\<^sub>g \<union> {(u, v) |u v. u \<in> [frontier]\<^sub>s \<and> v \<in> neighbourhood [G]\<^sub>g u - [vis]\<^sub>s}"
    using xs_prop(2) by argo
  assume next_asm: "Graph.finite_graph BFS_tree"
  hence "Graph.finite_graph (foldr  (\<lambda> u nf. add_neighbs nf u (diff (neighbourhood' u) vis))
                          xs BFS_tree)"
    by(induction xs)
      (auto simp add: add_neighbs_inv(2) assms(3) assms(4) goal1_general)
 thus "Graph.finite_graph (expand_tree BFS_tree frontier vis)"
    using xs_prop(2) by argo
qed
end

lemmas [code] = expand_tree_def next_frontier_def

end
end