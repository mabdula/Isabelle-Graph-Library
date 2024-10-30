theory BFS_Subprocedures
  imports BFS_2 "HOL-Data_Structures.RBT_Map" Set2_Join_RBT
begin

locale BFS_subprocedures =
  Graph: Pair_Graph_Specs
    where lookup = lookup +
  set_ops: Set2 neighb_empty neighb_delete _ t_set neighb_inv insert
  
for lookup :: "'adj \<Rightarrow> 'ver \<Rightarrow> 'neighb option" +

fixes G::"'adj" 
fixes fold_neighb::"('ver \<Rightarrow> 'neighb \<Rightarrow> 'neighb) \<Rightarrow> 'neighb \<Rightarrow> 'neighb \<Rightarrow> 'neighb"
fixes fold_adj::"('ver \<Rightarrow> 'adj \<Rightarrow> 'adj) \<Rightarrow> 'neighb \<Rightarrow> 'adj \<Rightarrow> 'adj"
assumes fold_neighb:"\<And> N f acc. neighb_inv N \<Longrightarrow> \<exists> xs. set xs = t_set N \<and>
                        fold_neighb f N acc = foldr f xs acc"
assumes fold_adj:"\<And> N f acc. neighb_inv N \<Longrightarrow> \<exists> xs. set xs = t_set N \<and>
                        fold_adj f N acc = foldr f xs acc"

begin

definition next_frontier::"'neighb \<Rightarrow> 'neighb \<Rightarrow> 'neighb"  where
"next_frontier frontier vis= fold_neighb (\<lambda> u nf. case (lookup G u) of None \<Rightarrow> nf
                                                  | Some vs \<Rightarrow> union nf (diff vs vis)) frontier neighb_empty"

lemma next_frontier:
    "\<lbrakk>neighb_inv frontier; neighb_inv vis; Graph.graph_inv G\<rbrakk> \<Longrightarrow>  neighb_inv (next_frontier frontier vis)"
    "\<lbrakk>neighb_inv frontier; neighb_inv vis; Graph.graph_inv G\<rbrakk> \<Longrightarrow>
       t_set (next_frontier frontier vis) =
         (\<Union> {Pair_Graph.neighbourhood (Graph.digraph_abs G) u | u . u \<in> t_set frontier}) - t_set vis"
proof-
  assume assms: "neighb_inv frontier" "neighb_inv vis" "Graph.graph_inv G"
  obtain xs where xs_prop:True
       "set xs = [frontier]\<^sub>s"
       "next_frontier frontier vis =
        foldr (\<lambda>u nf. case lookup G u of None \<Rightarrow> nf | Some vs \<Rightarrow> nf \<union>\<^sub>G (vs -\<^sub>G vis)) xs \<emptyset>\<^sub>N"
    using fold_neighb[OF assms(1)] by(fastforce simp add: next_frontier_def)
  have goal1_gen:"neighb_inv (foldr (\<lambda>u nf. case lookup G u of None \<Rightarrow> nf | Some vs \<Rightarrow> nf \<union>\<^sub>G (vs -\<^sub>G vis)) xs \<emptyset>\<^sub>N)" for xs
   using assms 
    by (induction xs)(auto split: option.split intro!: Graph.neighb.set.invar_empty set_ops.invar_union Cons set_ops.invar_diff)
  thus"neighb_inv (next_frontier frontier vis)"
   by(simp add: xs_prop(3)) 
  show "[next_frontier frontier vis]\<^sub>s = \<Union> {neighbourhood [G]\<^sub>g u |u. u \<in> [frontier]\<^sub>s} - [vis]\<^sub>s"
    unfolding xs_prop(3) 
    using xs_prop(1,2) assms(1) 
  proof(induction xs arbitrary: frontier)
    case Nil
    then show ?case by(auto intro!: Graph.neighb.set.set_empty)
  next
    case (Cons a xs)
    show ?case 
    proof(cases "a \<in> set xs")
      case True
      show ?thesis 
      proof(cases "lookup G a")
        case None
        then show ?thesis 
          using True Cons(2-) by (simp, intro Cons(1)) auto
      next
        case (Some vs)
        have vs_already_in:"[vs]\<^sub>s 
             \<subseteq>  \<Union> {neighbourhood [G]\<^sub>g u |u. u \<in> [frontier]\<^sub>s}"
          using  Cons.prems(2) True Some insert_absorb 
          by (fastforce simp add:  Graph.neighbourhood_abs[OF assms(3), symmetric] Graph.neighbourhood_def)   
        have helper: " \<Union> {neighbourhood [G]\<^sub>g u |u. u \<in> [frontier]\<^sub>s} - [vis]\<^sub>s \<union> [vs -\<^sub>G vis]\<^sub>s =
         \<Union> {neighbourhood [G]\<^sub>g u |u. u \<in> [frontier]\<^sub>s} - [vis]\<^sub>s"
          using assms  vs_already_in  Some
          by (subst set_ops.set_diff)(auto intro: set_ops.invar_diff)
        have hlper2: "[foldr (\<lambda>u nf. case lookup G u of None \<Rightarrow> nf | Some vs \<Rightarrow> nf \<union>\<^sub>G (vs -\<^sub>G vis)) xs \<emptyset>\<^sub>N]\<^sub>s \<union> [vs -\<^sub>G vis]\<^sub>s =
    \<Union> {neighbourhood [G]\<^sub>g u |u. u \<in> [frontier]\<^sub>s} - [vis]\<^sub>s"
          using True Cons(2-) helper by (subst Cons(1)) auto
        from Some show ?thesis
          using assms(2) assms(3)  hlper2 
          by (simp, subst set_ops.set_union)(auto intro: set_ops.invar_diff  goal1_gen)
      qed
    next
      case False
      thus ?thesis
    proof(cases "lookup G a")
      case None
      hence same_neighbs:"\<Union> {neighbourhood [G]\<^sub>g u |u. u \<in> [frontier]\<^sub>s} =
            \<Union> {neighbourhood [G]\<^sub>g u |u. u \<in> [neighb_delete a frontier]\<^sub>s}"
          using  Graph.neighb.set.set_delete[OF Cons(4)] Graph.neighb.set.set_empty  Graph.neighb.set.set_isin[OF  Graph.neighb.set.invar_empty]
                 neighbourhoodI 
          by(fastforce simp add: Graph.neighb.set.set_delete[OF Cons.prems(3)] Graph.digraph_abs_def Graph.neighbourhood_def)
     have "[foldr (\<lambda>u nf. case lookup G u of None \<Rightarrow> nf | Some vs \<Rightarrow> nf \<union>\<^sub>G (vs -\<^sub>G vis)) xs \<emptyset>\<^sub>N]\<^sub>s =
         \<Union> {neighbourhood [G]\<^sub>g u |u. u \<in> [neighb_delete a frontier]\<^sub>s} - [vis]\<^sub>s"
          using Cons(2-4)  Graph.neighb.set.set_delete 
          by (intro Cons(1))(auto simp add: Graph.neighb.set.invar_delete False)+
        thus ?thesis by (simp add: None same_neighbs)
    next
      case (Some vs)
      have same_neighbs:"\<Union> {neighbourhood [G]\<^sub>g u |u. u \<in> [frontier]\<^sub>s} =
            \<Union> {neighbourhood [G]\<^sub>g u |u. u \<in> [neighb_delete a frontier]\<^sub>s} \<union> [vs]\<^sub>s"
      proof(rule, all \<open>rule\<close>, goal_cases)
        case (1 x)
        then obtain u where u_prop:"x \<in> neighbourhood [G]\<^sub>g u" "u \<in> [frontier]\<^sub>s" by auto
        show ?case 
        proof(cases "u = a")
          case True
          hence "x \<in> [vs]\<^sub>s"
            using u_prop Some Graph.neighb.set.set_isin assms(3) 
            by(auto split: option.split simp add: neighbourhood_def Graph.digraph_abs_def Graph.neighbourhood_def)
          then show ?thesis  by simp
        next
          case False
          hence "u \<in> [neighb_delete a frontier]\<^sub>s"
            by (simp add: Cons.prems(3) Graph.neighb.set.set_delete u_prop(2))
          thus ?thesis 
            using u_prop(1) by auto
        qed
      next
        case (2 x)
        note 22 =this
        show ?case 
        proof(cases rule: UnE[OF 2])
          case 1
          then obtain u where "x \<in> neighbourhood [G]\<^sub>g u" "u \<in> [neighb_delete a frontier]\<^sub>s" by auto
          moreover hence "u \<in> [frontier]\<^sub>s"
            by (simp add: Cons.prems(3) Graph.neighb.set.set_delete)
          ultimately show ?thesis by auto
        next
          case 2
          hence "x \<in> neighbourhood [G]\<^sub>g a" 
            using  Graph.neighbourhood_abs[OF assms(3)] Graph.neighbourhood_def Some by fastforce
          moreover have "a  \<in> [frontier]\<^sub>s"
            using Cons.prems(2) by auto
          ultimately show ?thesis by auto
        qed
      qed
      have diff_sol: "[vs -\<^sub>G vis]\<^sub>s = [vs]\<^sub>s - [vis]\<^sub>s"
        using Some assms(2) 
        by(auto intro: Graph.graph_invE[OF assms(3)]  simp add: set_ops.set_diff)
      have IH_applied: "[foldr (\<lambda>u nf. case lookup G u of None \<Rightarrow> nf | Some vs \<Rightarrow> nf \<union>\<^sub>G (vs -\<^sub>G vis)) xs \<emptyset>\<^sub>N]\<^sub>s =
                   \<Union> {neighbourhood [G]\<^sub>g u |u. u \<in> [neighb_delete a frontier]\<^sub>s} - [vis]\<^sub>s"
        using Cons.prems(1)  Cons.prems(2)
        by(intro  Cons(1)[of "neighb_delete a frontier"])
          (auto simp add: False Cons.prems(3) Graph.neighb.set.invar_delete Graph.neighb.set.set_delete[OF  Cons.prems(3)] )
      show ?thesis 
        using Some assms(2) assms(3)  
        by (simp add: Some same_neighbs Un_Diff, subst set_ops.set_union)
           (auto intro: goal1_gen set_ops.invar_diff simp add: diff_sol IH_applied)
      qed
    qed
  qed
qed

definition expand_tree::"'adj \<Rightarrow> 'neighb \<Rightarrow> 'neighb \<Rightarrow> 'adj" where
"expand_tree BFS_tree frontier vis = 
fold_adj (\<lambda> u nf. case (lookup G u) of None \<Rightarrow> nf
                | Some vs \<Rightarrow> (case (lookup nf u) of None \<Rightarrow> update u (diff vs vis) nf
                              | Some vs' \<Rightarrow>update u (union vs' (diff vs vis)) nf)) frontier BFS_tree"

lemma expand_tree:
     "\<lbrakk>Graph.graph_inv BFS_tree; neighb_inv frontier; neighb_inv vis; Graph.graph_inv G\<rbrakk> \<Longrightarrow> 
       Graph.graph_inv (expand_tree BFS_tree frontier vis)"
     "\<lbrakk>Graph.graph_inv BFS_tree; neighb_inv frontier; neighb_inv vis; Graph.graph_inv G\<rbrakk> \<Longrightarrow>
        Graph.digraph_abs (expand_tree BFS_tree frontier vis) = 
         (Graph.digraph_abs BFS_tree) \<union> 
         {(u,v) | u v. u \<in> t_set (frontier) \<and> 
                       v \<in> (Pair_Graph.neighbourhood (Graph.digraph_abs G) u -
                       t_set vis)}"
proof-
  assume assms: "Graph.graph_inv BFS_tree" "neighb_inv frontier" "neighb_inv vis" "Graph.graph_inv G"
  define one_it where "one_it = (\<lambda>u nf.
          case lookup G u of None \<Rightarrow> nf
          | Some vs \<Rightarrow>
              case lookup nf u of None \<Rightarrow> update u (vs -\<^sub>G vis) nf
              | Some vs' \<Rightarrow> update u (vs' \<union>\<^sub>G (vs -\<^sub>G vis)) nf)"
  obtain xs where xs_prop:
    "set xs = [frontier]\<^sub>s" "expand_tree BFS_tree frontier vis = foldr one_it xs BFS_tree"
    using fold_adj[OF assms(2), of _ BFS_tree]
    by (auto simp add: expand_tree_def one_it_def)
  have goal1_general:"Graph.graph_inv (foldr one_it xs BFS_tree)" for xs
  proof(induction xs)
    case Nil
    then show ?case using assms(1) by simp
  next
    case (Cons a xs)
    have helper1: "\<And>v neighb.
       lookup (foldr one_it xs BFS_tree) a = None \<Longrightarrow>
       lookup G a = Some x2 \<Longrightarrow>
       (if v = a then Some (x2 -\<^sub>G vis) else lookup (foldr one_it xs BFS_tree) v) = Some neighb \<Longrightarrow>
       neighb_inv neighb" for x2 
      by (metis Graph.graph_invE assms(3) assms(4) local.Cons option.inject set_ops.invar_diff)
    have helper2: "lookup (foldr one_it xs BFS_tree) a = None \<Longrightarrow>
          lookup G a = Some x2 \<Longrightarrow> Graph.graph_inv (update a (x2 -\<^sub>G vis) (foldr one_it xs BFS_tree))"
      for x2
      by(auto simp add: Graph.graph_inv_def Cons[simplified  Graph.graph_inv_def]  Graph.adj.map_update intro!: Graph.adj.invar_update helper1)
    have helper3: "lookup (foldr one_it xs BFS_tree) a = Some x2a \<Longrightarrow>
       lookup G a = Some x2 \<Longrightarrow>
       lookup (update a (x2a \<union>\<^sub>G (x2 -\<^sub>G vis)) (foldr one_it xs BFS_tree)) v = Some neighb \<Longrightarrow> neighb_inv neighb"
      for x2 x2a v neighb
      apply(rule Graph.graph_invE[OF Cons] )
      apply(rule Graph.graph_invE[OF assms(4)] )
      apply(subst (asm)  Graph.adj.map_update) 
      by(simp, rule  case_split[of "v = a"], auto simp add:  assms(3) assms(4) Cons  set_ops.invar_diff set_ops.invar_union)
    have helper4:"lookup (foldr one_it xs BFS_tree) a = Some x2a \<Longrightarrow>
       lookup G a = Some x2 \<Longrightarrow> Graph.graph_inv (update a (x2a \<union>\<^sub>G (x2 -\<^sub>G vis)) (foldr one_it xs BFS_tree))"
      for x2 x2a
      using Graph.adj.invar_update local.Cons 
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
        using  Graph.neighb.emptyD(1) 
        by(simp add: one_it_def Graph.neighbourhood_abs[OF assms(4), symmetric] Graph.neighbourhood_def) 
    next
      case (Some vs)
      note some=this
      hence vs_inv:"neighb_inv vs" 
        using assms(4) by auto
      show ?thesis 
      proof(cases "lookup T u")
        case None
        have helper:"{(ua, v). v \<in>\<^sub>G (case lookup (update u (vs -\<^sub>G vis) T) ua of None \<Rightarrow> \<emptyset>\<^sub>N | Some neighb \<Rightarrow> neighb)} =
    {(u, v). v \<in>\<^sub>G (case lookup T u of None \<Rightarrow> \<emptyset>\<^sub>N | Some neighb \<Rightarrow> neighb)} \<union>
    {(u, v) |v. v \<in>\<^sub>G vs \<and> v \<notin> [vis]\<^sub>s}"
        proof(rule, all \<open>rule\<close>, goal_cases)
          case (1 e)
          then obtain x y where xy_prop: "e = (x,y)" 
              "y \<in>\<^sub>G (case lookup (update u (vs -\<^sub>G vis) T) x of None \<Rightarrow> \<emptyset>\<^sub>N | Some neighb \<Rightarrow> neighb)"
            by auto
          then show ?case
            using one 
            by (subst (asm) Graph.adj.map_update) (auto intro: case_split[of "u = x"]split: option.split simp add: Graph.neighb.set.set_isin vs_inv assms(3) set_ops.invar_diff set_ops.set_diff)
        next
          case (2 e)
          show ?case 
          proof(cases rule: UnE[OF 2])
            case 1
            then obtain x y where "e = (x,y)" "y \<in>\<^sub>G (case lookup T x of None \<Rightarrow> \<emptyset>\<^sub>N | Some neighb \<Rightarrow> neighb)" by auto
            then show ?thesis 
              using one 
              by (subst Graph.adj.map_update)(auto simp add: Graph.neighb.set.invar_empty Graph.neighb.set.set_empty Graph.neighb.set.set_isin None)
          next
            case 2
            then obtain y where "e = (u,y)" "y \<in>\<^sub>G vs \<and> y \<notin> [vis]\<^sub>s" by auto
            then show ?thesis
              using one 
              by (subst Graph.adj.map_update)(auto simp add: Graph.neighb.set.set_isin assms(3) set_ops.invar_diff set_ops.set_diff vs_inv)
          qed
        qed 
        show ?thesis
          using helper 
          by(auto simp add: one_it_def None Graph.digraph_abs_def Graph.neighbourhood_def some neighbourhood_def split: option.split)
      next
        case (Some vs')
        have "{(ua, y).
     isin (case lookup (update u (vs' \<union>\<^sub>G (vs -\<^sub>G vis)) T) ua of None \<Rightarrow> \<emptyset>\<^sub>N | Some neighb \<Rightarrow> neighb) y} =
    {(u, y). isin (case lookup T u of None \<Rightarrow> \<emptyset>\<^sub>N | Some neighb \<Rightarrow> neighb) y} \<union>
    {(u, v) |v. v \<in>\<^sub>G vs \<and> v \<notin> [vis]\<^sub>s}"
        proof(rule, all\<open>rule\<close>, goal_cases)
          case (1 e)
           then obtain x y where "e= (x,y)" "y \<in>\<^sub>G (case lookup (update u (vs' \<union>\<^sub>G (vs -\<^sub>G vis)) T) x of None \<Rightarrow> \<emptyset>\<^sub>N | Some neighb \<Rightarrow> neighb)"
             by blast
           thus ?case
             apply(subst (asm) Graph.adj.map_update)
             using one apply fast
             using Graph.neighb.set.set_isin Some assms(3) one set_ops.invar_diff 
             set_ops.invar_union set_ops.set_diff set_ops.set_union vs_inv  
             by(cases "u = x", all \<open>cases "lookup T x"\<close>) auto
         next
           case (2 e)
           show ?case
           proof(cases rule: UnE[OF 2])
             case 1
             then obtain x y where "e = (x,y)" "y \<in>\<^sub>G (case lookup T x of None \<Rightarrow> \<emptyset>\<^sub>N | Some neighb \<Rightarrow> neighb)"
               by auto
             moreover hence "lookup T x \<noteq> None" 
               using Graph.neighb.set.invar_empty Graph.neighb.set.set_empty Graph.neighb.set.set_isin by fastforce
            ultimately show ?thesis 
              using Graph.neighb.set.set_isin Some assms(3) 
                    one set_ops.invar_diff set_ops.invar_union set_ops.set_union vs_inv 
              by (subst  Graph.adj.map_update) auto
          next
            case 2
            thus ?thesis
              using Graph.neighb.set.set_isin Some assms(3) one set_ops.invar_diff 
                    set_ops.invar_union set_ops.set_diff set_ops.set_union vs_inv 
              by (subst  Graph.adj.map_update)auto
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
     have del_set:"[neighb_delete a frontier]\<^sub>s = set xs"
       using Cons.prems(1) Cons.prems(2) False Graph.neighb.set.set_delete by auto
     show ?thesis
       using Cons.prems(1) Cons.prems(2) False Graph.neighb.set.set_delete 
     by(auto simp add: one_it_graph_abs goal1_general Cons(1)[of "neighb_delete a frontier"] Cons.prems(2) Graph.neighb.set.invar_delete del_set sym[OF Cons(2)])
 qed
qed
  thus "[expand_tree BFS_tree frontier vis]\<^sub>g =
    [BFS_tree]\<^sub>g \<union> {(u, v) |u v. u \<in> [frontier]\<^sub>s \<and> v \<in> neighbourhood [G]\<^sub>g u - [vis]\<^sub>s}"
    using xs_prop(2) by argo
qed

lemmas [code] = expand_tree_def next_frontier_def

end
end