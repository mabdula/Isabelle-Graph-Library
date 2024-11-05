theory BFS_Subprocedures
  imports BFS_2 "HOL-Data_Structures.RBT_Map" Directed_Set_Graphs.Set_Addons 
begin

locale BFS_subprocedures =
  Graph: Pair_Graph_Specs
    where lookup = lookup +

  set_ops: Set2 vset_empty vset_delete _ t_set vset_inv insert
  
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
    apply(auto simp add: next_frontier_def)
    by metis
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
     (\<lambda> u nf. case (lookup G u) of None \<Rightarrow> nf
                     | Some vs \<Rightarrow> (case (lookup nf u) of None \<Rightarrow> update u (diff vs vis) nf
                              | Some vs' \<Rightarrow>update u (union vs' (diff vs vis)) nf)) frontier BFS_tree"

lemma expand_tree:
     "\<lbrakk>Graph.graph_inv BFS_tree; vset_inv frontier; vset_inv vis; Graph.graph_inv G\<rbrakk> \<Longrightarrow> 
       Graph.graph_inv (expand_tree BFS_tree frontier vis)"
     "\<lbrakk>Graph.graph_inv BFS_tree; vset_inv frontier; vset_inv vis; Graph.graph_inv G\<rbrakk> \<Longrightarrow>
        Graph.digraph_abs (expand_tree BFS_tree frontier vis) = 
         (Graph.digraph_abs BFS_tree) \<union> 
         {(u,v) | u v. u \<in> t_set (frontier) \<and> 
                       v \<in> (Pair_Graph.neighbourhood (Graph.digraph_abs G) u -
                       t_set vis)}"
proof-
  assume assms: "Graph.graph_inv BFS_tree" "vset_inv frontier" "vset_inv vis" "Graph.graph_inv G"
  define one_it where "one_it = (\<lambda>u nf.
          case lookup G u of None \<Rightarrow> nf
          | Some vs \<Rightarrow>
              case lookup nf u of None \<Rightarrow> update u (vs -\<^sub>G vis) nf
              | Some vs' \<Rightarrow> update u (vs' \<union>\<^sub>G (vs -\<^sub>G vis)) nf)"
  obtain xs where xs_prop:
    "set xs = [frontier]\<^sub>s" "expand_tree BFS_tree frontier vis = foldr one_it xs BFS_tree"
    using fold_adjmap[OF assms(2), of _ BFS_tree]
    by (auto simp add: expand_tree_def one_it_def)
  have goal1_general:"Graph.graph_inv (foldr one_it xs BFS_tree)" for xs
  proof(induction xs)
    case Nil
    then show ?case using assms(1) by simp
  next
    case (Cons a xs)
    have helper1: "\<And>v vset.
       lookup (foldr one_it xs BFS_tree) a = None \<Longrightarrow>
       lookup G a = Some x2 \<Longrightarrow>
       (if v = a then Some (x2 -\<^sub>G vis) else lookup (foldr one_it xs BFS_tree) v) = Some vset \<Longrightarrow>
       vset_inv vset" for x2 
      by (metis Graph.graph_invE assms(3) assms(4) local.Cons option.inject set_ops.invar_diff)
    have helper2: "lookup (foldr one_it xs BFS_tree) a = None \<Longrightarrow>
          lookup G a = Some x2 \<Longrightarrow> Graph.graph_inv (update a (x2 -\<^sub>G vis) (foldr one_it xs BFS_tree))"
      for x2
      by(auto simp add: Graph.graph_inv_def Cons[simplified  Graph.graph_inv_def]  Graph.adjmap.map_update intro!: Graph.adjmap.invar_update helper1)
    have helper3: "lookup (foldr one_it xs BFS_tree) a = Some x2a \<Longrightarrow>
       lookup G a = Some x2 \<Longrightarrow>
       lookup (update a (x2a \<union>\<^sub>G (x2 -\<^sub>G vis)) (foldr one_it xs BFS_tree)) v = Some vset \<Longrightarrow> vset_inv vset"
      for x2 x2a v vset
      apply(rule Graph.graph_invE[OF Cons] )
      apply(rule Graph.graph_invE[OF assms(4)] )
      apply(subst (asm)  Graph.adjmap.map_update) 
      by(simp, rule  case_split[of "v = a"], auto simp add:  assms(3) assms(4) Cons  set_ops.invar_diff set_ops.invar_union)
    have helper4:"lookup (foldr one_it xs BFS_tree) a = Some x2a \<Longrightarrow>
       lookup G a = Some x2 \<Longrightarrow> Graph.graph_inv (update a (x2a \<union>\<^sub>G (x2 -\<^sub>G vis)) (foldr one_it xs BFS_tree))"
      for x2 x2a
      using Graph.adjmap.invar_update local.Cons 
      by(auto intro: helper3 simp add:  Graph.graph_inv_def Cons[simplified  Graph.graph_inv_def])
    show ?case 
      using Cons 
      by(simp, subst one_it_def)(auto intro: helper2 helper4 split: option.split )
  qed
  thus " Graph.graph_inv (expand_tree BFS_tree frontier vis)"
    by (simp add: xs_prop(2))
  have one_it_graph_abs:"Graph.graph_inv T \<Longrightarrow> [one_it u T]\<^sub>g = [T]\<^sub>g \<union> {(u, v) |v. v \<in> neighbourhood [G]\<^sub>g u - [vis]\<^sub>s}" for u T
  proof(goal_cases)
    case 1
    note one=this
    show ?case
    proof(cases "lookup G u")
      case None
      then show ?thesis 
        using  Graph.vset.emptyD(1) 
        by(simp add: one_it_def Graph.neighbourhood_abs[OF assms(4), symmetric] Graph.neighbourhood_def) 
    next
      case (Some vs)
      note some=this
      hence vs_inv:"vset_inv vs" 
        using assms(4) by auto
      show ?thesis 
      proof(cases "lookup T u")
        case None
        have helper:"{(ua, v). v \<in>\<^sub>G (case lookup (update u (vs -\<^sub>G vis) T) ua of None \<Rightarrow> \<emptyset>\<^sub>N | Some vset \<Rightarrow> vset)} =
    {(u, v). v \<in>\<^sub>G (case lookup T u of None \<Rightarrow> \<emptyset>\<^sub>N | Some vset \<Rightarrow> vset)} \<union>
    {(u, v) |v. v \<in>\<^sub>G vs \<and> v \<notin> [vis]\<^sub>s}"
        proof(rule, all \<open>rule\<close>, goal_cases)
          case (1 e)
          then obtain x y where xy_prop: "e = (x,y)" 
              "y \<in>\<^sub>G (case lookup (update u (vs -\<^sub>G vis) T) x of None \<Rightarrow> \<emptyset>\<^sub>N | Some vset \<Rightarrow> vset)"
            by auto
          then show ?case
            using one 
            by (subst (asm) Graph.adjmap.map_update) (auto intro: case_split[of "u = x"]split: option.split simp add: Graph.vset.set.set_isin vs_inv assms(3) set_ops.invar_diff set_ops.set_diff)
        next
          case (2 e)
          show ?case 
          proof(cases rule: UnE[OF 2])
            case 1
            then obtain x y where "e = (x,y)" "y \<in>\<^sub>G (case lookup T x of None \<Rightarrow> \<emptyset>\<^sub>N | Some vset \<Rightarrow> vset)" by auto
            then show ?thesis 
              using one 
              by (subst Graph.adjmap.map_update)(auto simp add: Graph.vset.set.invar_empty Graph.vset.set.set_empty Graph.vset.set.set_isin None)
          next
            case 2
            then obtain y where "e = (u,y)" "y \<in>\<^sub>G vs \<and> y \<notin> [vis]\<^sub>s" by auto
            then show ?thesis
              using one 
              by (subst Graph.adjmap.map_update)(auto simp add: Graph.vset.set.set_isin assms(3) set_ops.invar_diff set_ops.set_diff vs_inv)
          qed
        qed 
        show ?thesis
          using helper 
          by(auto simp add: one_it_def None Graph.digraph_abs_def Graph.neighbourhood_def some neighbourhood_def split: option.split)
      next
        case (Some vs')
        have "{(ua, y).
     isin (case lookup (update u (vs' \<union>\<^sub>G (vs -\<^sub>G vis)) T) ua of None \<Rightarrow> \<emptyset>\<^sub>N | Some vset \<Rightarrow> vset) y} =
    {(u, y). isin (case lookup T u of None \<Rightarrow> \<emptyset>\<^sub>N | Some vset \<Rightarrow> vset) y} \<union>
    {(u, v) |v. v \<in>\<^sub>G vs \<and> v \<notin> [vis]\<^sub>s}"
        proof(rule, all\<open>rule\<close>, goal_cases)
          case (1 e)
           then obtain x y where "e= (x,y)" "y \<in>\<^sub>G (case lookup (update u (vs' \<union>\<^sub>G (vs -\<^sub>G vis)) T) x of None \<Rightarrow> \<emptyset>\<^sub>N | Some vset \<Rightarrow> vset)"
             by blast
           thus ?case
             apply(subst (asm) Graph.adjmap.map_update)
             using one apply fast
             using Graph.vset.set.set_isin Some assms(3) one set_ops.invar_diff 
             set_ops.invar_union set_ops.set_diff set_ops.set_union vs_inv  
             by(cases "u = x", all \<open>cases "lookup T x"\<close>) auto
         next
           case (2 e)
           show ?case
           proof(cases rule: UnE[OF 2])
             case 1
             then obtain x y where "e = (x,y)" "y \<in>\<^sub>G (case lookup T x of None \<Rightarrow> \<emptyset>\<^sub>N | Some vset \<Rightarrow> vset)"
               by auto
             moreover hence "lookup T x \<noteq> None" 
               using Graph.vset.set.invar_empty Graph.vset.set.set_empty Graph.vset.set.set_isin by fastforce
            ultimately show ?thesis 
              using Graph.vset.set.set_isin Some assms(3) 
                    one set_ops.invar_diff set_ops.invar_union set_ops.set_union vs_inv 
              by (subst  Graph.adjmap.map_update) auto
          next
            case 2
            thus ?thesis
              using Graph.vset.set.set_isin Some assms(3) one set_ops.invar_diff 
                    set_ops.invar_union set_ops.set_diff set_ops.set_union vs_inv 
              by (subst  Graph.adjmap.map_update)auto
          qed
        qed
        then show ?thesis
          by(simp add: one_it_def Some some Graph.digraph_abs_def Graph.neighbourhood_def neighbourhood_def)
      qed
    qed
  qed


  have "[foldr one_it xs BFS_tree]\<^sub>g = [BFS_tree]\<^sub>g \<union> {(u, v) |u v. u \<in> [frontier]\<^sub>s \<and> v \<in> neighbourhood [G]\<^sub>g u - [vis]\<^sub>s}"
    using xs_prop(1) assms(2)
  proof(induction xs arbitrary: frontier)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    show ?case 
    proof(cases "a \<in> set xs")
      case True
      have heper: "[foldr one_it xs BFS_tree]\<^sub>g \<union> {(a, v) |v. v \<in> neighbourhood [G]\<^sub>g a - [vis]\<^sub>s} =
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
qed
end

lemmas [code] = expand_tree_def next_frontier_def

end
end