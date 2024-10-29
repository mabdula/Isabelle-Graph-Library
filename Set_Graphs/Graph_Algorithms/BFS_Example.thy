theory BFS_Example
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

fun fold_rbt where
"fold_rbt f Leaf acc = acc"|
"fold_rbt f (B l x r) acc= f x (fold_rbt f l (fold_rbt f r acc))"|
"fold_rbt f (R l x r) acc= f x (fold_rbt f l (fold_rbt f r acc))"

lemma fold_rbt_is_foldr_of_preorder:"fold_rbt f T acc = foldr f (map fst (preorder T)) acc "
  by(induction f T acc arbitrary: rule: fold_rbt.induct) auto

definition "t_set \<equiv> Tree2.set_tree"
definition "neighb_inv \<equiv>  (\<lambda>t. (invc t \<and> invh t) \<and> Tree2.bst t)"
definition "neighb_empty = Leaf"

notation neighb_empty ("\<emptyset>\<^sub>N")

fun sel where
"sel Leaf = undefined" |
"sel (B l a r) = a"|
"sel (R l a r) = a"

lemma Set_satisified: "Set neighb_empty neighb_insert neighb_delete isin t_set neighb_inv"
  using  RBT.Set_axioms 
  by(auto simp add: neighb_empty_def neighb_delete_def neighb_insert_def t_set_def neighb_inv_def)

lemma Set_Choose_axioms: "Set_Choose_axioms neighb_empty isin sel"
  apply(rule Set_Choose_axioms.intro)
  unfolding neighb_empty_def 
  subgoal for s
    by(induction rule: sel.induct) auto
  done
 
lemma Set_Choose_satisfied:"Set_Choose neighb_empty neighb_insert neighb_delete isin neighb_inv t_set sel"
  using Set_satisified Set_Choose_axioms
  by(auto simp add: Set_Choose_def)

notation empty ("\<emptyset>\<^sub>G")

lemma Map_satisfied: "Map neighb_empty update RBT_Map.delete lookup M.invar"
  using RBT_Map.M.Map_axioms
  by(auto simp add: Map_def M.invar_def neighb_empty_def  RBT_Set.empty_def )

lemma Pair_Graph_Specs_satisfied: "Pair_Graph_Specs empty RBT_Map.delete lookup neighb_insert isin t_set sel
     update M.invar neighb_empty neighb_delete neighb_inv"
  using Set_Choose_satisfied Map_satisfied
  unfolding Pair_Graph_Specs_def
  by(auto simp add: Pair_Graph_Specs_def empty_def  neighb_empty_def)

lemma Set2_satisfied: "Set2 neighb_empty neighb_delete isin t_set neighb_inv neighb_insert neighb_union
     neighb_inter neighb_diff"
  using  Set2_Join_RBT.RBT.Set2_axioms 
  by(auto simp add: RBT_Set.empty_def neighb_empty_def neighb_delete_def t_set_def neighb_inv_def neighb_insert_def
                    neighb_union_def neighb_inter_def neighb_diff_def)

definition "fold_neighb = (fold_rbt)"
definition "fold_adj = (fold_rbt)"

lemma prderorder_set:"set (map fst (preorder N)) = Tree2.set_tree N"
  by(induction N rule: preorder.induct)auto

lemma preorder_witness:"set (map fst (preorder N)) = t_set N \<and> fold_rbt f N acc = foldr f (map fst (preorder N)) acc"
  unfolding fold_rbt_is_foldr_of_preorder prderorder_set t_set_def by auto

lemma rbt_fold_spec:"neighb_inv N \<Longrightarrow> \<exists>xs. set xs = t_set N \<and> fold_rbt f N acc = foldr f xs acc"
  using preorder_witness by metis

lemma BFS_subprocedures_axioms: "BFS_subprocedures_axioms t_set neighb_inv fold_neighb fold_adj"
 by(auto intro!: BFS_subprocedures_axioms.intro rbt_fold_spec
           simp add: fold_neighb_def fold_adj_def )

global_interpretation bfs_subprocedures: BFS_subprocedures
where insert = neighb_insert 
and sel = sel 
and neighb_empty = neighb_empty 
and diff = neighb_diff 
and lookup = lookup 
and empty = empty 
and delete=delete 
and isin = isin 
and t_set=t_set
and update=update 
and adj_inv = M.invar
and neighb_delete= neighb_delete
and neighb_inv = neighb_inv 
and union=neighb_union 
and inter=neighb_inter 
and fold_neighb = fold_neighb
and fold_adj=fold_adj
and G = G for G 
defines next_frontier = bfs_subprocedures.next_frontier
and expand_tree = bfs_subprocedures.expand_tree
by(auto intro!: BFS_subprocedures.intro 
           simp add: Pair_Graph_Specs_satisfied  Set2_satisfied BFS_subprocedures_axioms )

lemma BFS_axioms:"BFS_axioms isin t_set M.invar \<emptyset>\<^sub>N neighb_inv lookup G (expand_tree G) (next_frontier G)"
 by(fastforce intro!: BFS_axioms.intro 
       simp add: bfs_subprocedures.expand_tree  bfs_subprocedures.next_frontier)

global_interpretation bfs: BFS
where insert = neighb_insert 
and sel = sel 
and neighb_empty = neighb_empty 
and diff = neighb_diff 
and lookup = lookup 
and empty = empty 
and delete=delete 
and isin = isin 
and t_set=t_set
and update=update 
and adj_inv = M.invar
and neighb_delete= neighb_delete
and neighb_inv = neighb_inv 
and union=neighb_union 
and inter=neighb_inter 
and expand_tree = "expand_tree G"
and next_frontier = "next_frontier G"
and G = G and srcs = srcs for G srcs
defines bfs_initial_state = "bfs.initial_state"
and bfs_impl = bfs.BFS_impl
  by(auto intro!: BFS.intro simp add: Pair_Graph_Specs_satisfied Set2_satisfied BFS_axioms)

definition "edges = [(0::nat, 1::nat), (0, 2), (2, 3), (2,4), (2,1), (1,5), (5,8), (8,7), (7,1),
                     (7,2), (7,4), (4,3), (3,4), (3,3), (9, 8), (8, 1), (4,5), (5,10)]"

definition "vertices = remdups (map prod.fst edges @ map prod.snd edges)"

definition "nbs v = foldr (\<lambda> x tree. insert x tree) (remdups (map prod.snd (filter (\<lambda> e. prod.fst e = v) edges))) neighb_empty"

definition "G = foldr (\<lambda> x tree. update x (nbs x) tree) vertices  empty"

definition "src_list = [9::nat]"

definition "srcs =  foldr (\<lambda> x tree. insert x tree) src_list empty"

term bfs_initial_state
term bfs_impl

value edges
value vertices
value "neighb_diff (nbs 1) (nbs 2)"
value G
value "bfs_initial_state srcs"   
value "bfs_impl G (bfs_initial_state srcs)"
end