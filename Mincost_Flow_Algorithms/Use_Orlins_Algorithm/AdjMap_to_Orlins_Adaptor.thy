theory AdjMap_to_Orlins_Adaptor
  imports  Directed_Set_Graphs.Pair_Graph_Specs 
           Data_Structures.Set2_Addons Data_Structures.Set_Addons
begin

locale adjmap_map_to_orlins =
cost_cost_map: Map cc_empty cc_update cc_delte  cc_lookup cc_invar+
cost_map: Map c_empty c_update  c_delte c_lookup c_invar+
Cmap: Map Cempty Cupdate Cdelte Clookup Cinvar +
Pair_Graph_Specs where empty = empty  and vset_empty = vset_empty
and isin = isin
for empty::"'adjmap_map" and vset_empty::"'vset" 
and isin::"'vset \<Rightarrow> 'a \<Rightarrow> bool"
and cc_empty and cc_update::"'a \<Rightarrow> 'cm \<Rightarrow> 'ccm \<Rightarrow> 'ccm" 
and cc_lookup cc_delte cc_invar and
c_empty and c_update::"'a \<Rightarrow> real \<Rightarrow> 'cm \<Rightarrow> 'cm"  
and c_lookup c_delte c_invar and
Map Cempty and Cupdate::"('a \<times> 'a) \<Rightarrow> real \<Rightarrow> 'C \<Rightarrow> 'C" 
and Clookup Cdelte Cinvar +
fixes fold_adjmap::"('a \<Rightarrow> 'vset option \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list) 
                     \<Rightarrow> 'adjmap_map \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list"
begin

function (domintros) to_list_gen where
"to_list_gen A acc = (if A = vset_empty then acc
                      else let x = sel A
                              in to_list_gen (vset_delete x A) (x#acc))"
  by pat_completeness auto

partial_function (tailrec) to_list_gen_exec where
"to_list_gen_exec A acc = (if A = vset_empty then acc
                      else let x = sel A
                              in to_list_gen_exec (vset_delete x A) (x#acc))"

definition "to_list A = to_list_gen_exec A Nil"

definition "add_edges = (\<lambda> x ys es. (case ys of None => es |
                                       Some ys \<Rightarrow> [(x, y). y \<leftarrow> to_list ys]@es))"

definition "collect_edges G = fold_adjmap add_edges G Nil"

lemma finite_A_terminating:"finite (t_set A) \<Longrightarrow>n = card (t_set A) \<Longrightarrow> vset_inv A \<Longrightarrow> to_list_gen_dom (A, acc)"
  by(induction n arbitrary: A acc)
    (auto intro: to_list_gen.domintros simp add: vset.set.invar_delete vset.set.set_delete)

lemma finite_fun_same_exec:
  assumes "finite (t_set A)" "vset_inv A"
  shows "to_list_gen_exec A acc = to_list_gen A acc"
 by(induction acc arbitrary: rule: to_list_gen.pinduct[OF finite_A_terminating[OF assms(1) refl assms(2)]])
   (auto simp add: to_list_gen.psimps to_list_gen_exec.simps) 

lemma to_list_gen_distinct:
  assumes  "finite (t_set A)" "vset_inv A"
  shows "vset_inv A \<Longrightarrow> t_set A \<inter> set acc = {} \<Longrightarrow> distinct acc \<Longrightarrow>
       distinct (to_list_gen A acc)"
    apply(induction acc arbitrary: rule: to_list_gen.pinduct[OF finite_A_terminating
                [OF assms(1) refl assms(2)]])
    using vset.set.invar_delete vset.set.set_delete 
    by (auto simp add: Let_def to_list_gen.psimps)

lemma to_list_gen_set:
  assumes  "finite (t_set A)" "vset_inv A"
  shows "vset_inv A \<Longrightarrow> t_set A \<inter> set acc = {}  \<Longrightarrow>
       set (to_list_gen A acc) = t_set A \<union> set acc"
    apply(induction acc arbitrary: rule: to_list_gen.pinduct[OF finite_A_terminating
                [OF assms(1) refl assms(2)]])
    using vset.set.invar_delete vset.set.set_delete 
    by (auto simp add: Let_def to_list_gen.psimps vset.set.set_empty) fastforce

lemma vsets1:"\<And>n. vset_inv n \<Longrightarrow> finite (t_set n) \<Longrightarrow> distinct (to_list n)"
  using to_list_gen_distinct[of _  Nil, simplified] finite_fun_same_exec[of _  Nil, simplified]
  by(auto simp add: to_list_def)

lemma vsets2:"\<And> n. vset_inv n \<Longrightarrow> finite (t_set n) \<Longrightarrow> set (to_list n) = t_set n"
  using to_list_gen_set[of _  Nil, simplified] finite_fun_same_exec[of _  Nil, simplified]
  by(auto simp add: to_list_def)

lemma length_filter_fist:"(length (filter ((=) xs) (xs # xss)) \<le> 1) = 
                          (length (filter ((=) xs) (xss)) = 0)"
"(length (xs # filter ((=) xs) ( xss)) \<le> 1) = 
                          (length (filter ((=) xs) (xss)) = 0)" 
  by auto

lemma length_filter_none: "(length (filter ((=) xs) (xss)) = 0) = 
                          (xs \<notin> set xss)" 
  by(induction xss) auto

lemma distinct_concat':
  "\<lbrakk> \<And> x . x \<noteq> Nil \<Longrightarrow> length (filter ((=) x) xs) \<le> 1;
     \<And> ys. ys \<in> set xs \<Longrightarrow> distinct ys;
     \<And> ys zs. \<lbrakk> ys \<in> set xs ; zs \<in> set xs ; ys \<noteq> zs \<rbrakk> \<Longrightarrow> set ys \<inter> set zs = {}
   \<rbrakk> \<Longrightarrow> distinct (concat xs)"
proof (induction xs)
  case (Cons xs xss)
  have "distinct xs"
    using Cons by simp
  moreover have "distinct (concat xss)"
        apply(rule Cons.IH)
       subgoal for ys
         using Cons(2)[of ys]
         by(auto intro: case_split[of  "xs = ys"])
       using Cons(3,4) by auto
  moreover have "set xs \<inter> set (concat xss) = {}"
       using Cons(4)[of xs _]  Cons(2)[of xs, simplified trans[OF length_filter_fist(1) length_filter_none]] 
       by force
   ultimately show ?case by simp
 qed simp

lemma P_of_ifI: "(P \<Longrightarrow> Q x ) \<Longrightarrow> (\<not> P \<Longrightarrow> Q y) \<Longrightarrow> Q (if P then x else y)"
  by auto

lemma image_cong: "A = B \<Longrightarrow> (\<And> x. x \<in> A \<Longrightarrow> x \<in> B \<Longrightarrow> f x = g x) \<Longrightarrow> f ` A = g ` B"
  by auto

context
assumes adjmap_fold:"\<And> m acc. adjmap_inv m \<Longrightarrow> finite (dom (lookup m)) \<Longrightarrow>
          \<exists> xs. distinct xs \<and> set xs = dom (lookup m) \<and>
                fold_adjmap f m acc = foldr (\<lambda> x acc. f x (lookup m x) acc) xs acc"
begin

lemma edges_right:
  assumes "adjmap_inv G"
              "\<And> x. lookup G x \<noteq> None \<Longrightarrow> vset_inv (the (lookup G x))"
              "finite (dom (lookup G))"
              "\<And> x. lookup G x \<noteq> None \<Longrightarrow> finite (t_set (the (lookup G x)))"
shows "distinct (collect_edges G)"
      "set (collect_edges G) = digraph_abs G"
proof-
  obtain xs where xs_prop: "distinct xs" "set xs = dom (lookup G)"
     "fold_adjmap add_edges G [] = foldr (\<lambda> x acc. add_edges x (lookup G x) acc) xs []"
    using adjmap_fold[OF assms(1,3)] by blast
  moreover have "foldr (\<lambda> x acc. add_edges x (lookup G x) acc) xs [] = 
        concat [[(x, y) . y \<leftarrow> to_list (the (lookup G x))] . x \<leftarrow> xs]"
    using assms(1) equalityD1[OF xs_prop(2)]
    by(induction xs) (auto simp add: add_edges_def)
  moreover have "distinct (concat [[(x, y) . y \<leftarrow> to_list (the (lookup G x))] . x \<leftarrow> xs])"
  proof(rule distinct_concat', goal_cases)
    case (1 ys)
    then show ?case 
      using xs_prop(1)
    proof(induction xs)
      case (Cons zs xs)
      show ?case  
      proof(cases "ys = map (Pair zs) (to_list (the (lookup G zs)))")
        case True
        have helper:"map (Pair zs) (to_list (the (lookup G zs)))
         \<in> (\<lambda>x. map (Pair x) (to_list (the (lookup G x)))) ` set xs \<Longrightarrow>
         map (Pair zs) (to_list (the (lookup G zs))) = map (Pair x) (to_list (the (lookup G x))) \<Longrightarrow>
         x \<in> set xs \<Longrightarrow> False" for x
        proof(goal_cases)     
          case (1 )
          hence "zs = x" 
            using Cons(2) True by (cases ys) auto
          thus ?case
            using 1(3)  Cons.prems(2) by auto
        qed
        show?thesis
          by(subst list.map(2), subst filter.simps(2), 
                subst if_P, simp add: True, simp only: True, 
                subst length_filter_fist(2)[of ], subst length_filter_none[of ])
            (auto intro: helper)
      next
        case False
        then show ?thesis
          apply(subst list.map(2), subst filter.simps(2),subst if_not_P)
          using  Cons(2,3)
          by (fastforce intro: Cons(1) simp add: False)+
      qed
    qed simp
  next
    case (2 ys)
    then obtain x where x_prop: "x \<in> set xs" " map (Pair x) (to_list (the (lookup G x))) = ys"
      by auto
    moreover hence "distinct (to_list (the (lookup G x)))"
      using xs_prop(2) by(auto intro: assms(2,4)[of x] vsets1) 
    ultimately show ?case
      by(auto simp add: distinct_map inj_on_def)
  qed(auto simp add: xs_prop(1)) 
  moreover have "set (concat [[(x, y) . y \<leftarrow> to_list (the (lookup G x))] . x \<leftarrow> xs]) 
                 = digraph_abs G"
  proof-
    have "set (concat [[(x, y) . y \<leftarrow> to_list (the (lookup G x))] . x \<leftarrow> xs]) =
         \<Union> { {(x, y) | y. y \<in> set(to_list (the (lookup G x)))}| x. x \<in> set xs}"
      by auto
    also have "... = \<Union> { {(x, y) | y. y \<in> t_set (the (lookup G x))}| x. x \<in> set xs}"
      using  xs_prop(2) vsets2  assms(2,4) by blast
    also have "... = {(x, y) | x y. y \<in> t_set (the (lookup G x)) \<and>  x \<in> set xs}" 
      by blast
    also have "... = {(x, y) | x y. y \<in> (case lookup G x of None \<Rightarrow> {}
                                             | Some xx \<Rightarrow> t_set xx )}" 
      by(auto simp add: option.split xs_prop(2) dom_def)
    also have "... = digraph_abs G"     
      unfolding digraph_abs_def neighbourhood_def 
      using vset.set.set_isin[OF vset.set.invar_empty, simplified vset.emptyD(3)[OF refl]] 
        option.simps(4) vset.set.set_isin[OF assms(2)] 
      by (fastforce intro: assms simp add: option.split)
    finally show ?thesis by simp
  qed
  ultimately show  "distinct (collect_edges G)" and "set (collect_edges G) = digraph_abs G"
    by(simp add: collect_edges_def)+
qed

definition "\<c>_impl C G = foldr (\<lambda> e acc. let ym = the (cc_lookup C (fst e));
                                           cost = the (c_lookup ym (snd e))
                                        in Cupdate e cost acc) (collect_edges G) Cempty"
lemma Cinavar_c_impl: "Cinvar (\<c>_impl C G)" (is ?thesis1)
      and dom_c_impl: "dom (Clookup (\<c>_impl C G))  = set (collect_edges G)" (is ?thesis2)
      and c_impl_lookup: "Clookup (\<c>_impl C G) e = 
                         (if e \<in> set (collect_edges G) 
                          then Some (the (c_lookup (the (cc_lookup C (fst e))) (snd e)))
                          else None)" (is ?thesis3)
proof-
  define es where "es = (collect_edges G)"
  have "Cinvar (\<c>_impl C G) \<and> dom (Clookup (\<c>_impl C G))  = set (collect_edges G)
        \<and> Clookup (\<c>_impl C G) e = 
                         (if e \<in> set (collect_edges G) 
                          then Some (the (c_lookup (the (cc_lookup C (fst e))) (snd e)))
                          else None)"
    unfolding \<c>_impl_def
    unfolding sym[OF es_def]
    apply(induction es)
    apply(auto intro:  Cmap.invar_update 
      simp add: Cmap.invar_empty Cmap.map_empty Cmap.map_update)+
    done
  thus ?thesis1 ?thesis2 ?thesis3 by auto
qed

lemma option_collapse_cong: "a = b \<Longrightarrow> b \<noteq> None \<Longrightarrow> Some (the a) = b"
  by auto

lemma assumes "adjmap_inv G"
              "\<And> x. lookup G x \<noteq> None \<Longrightarrow> vset_inv (the (lookup G x))"
              "finite (dom (lookup G))"
              "\<And> x. lookup G x \<noteq> None \<Longrightarrow> finite (t_set (the (lookup G x)))"
              "dom (cc_lookup C) = dom (lookup G)"
              "\<And> x. cc_lookup C x \<noteq> None \<Longrightarrow> 
                       dom (c_lookup (the (cc_lookup C x))) = t_set (the (lookup G x))"
         shows 
              "dom (Clookup (\<c>_impl C G)) = digraph_abs G" 
              "e \<in> digraph_abs G \<Longrightarrow> Clookup (\<c>_impl C G) e = c_lookup  (the (cc_lookup C (fst e))) (snd e)"    
proof-
  show thesis1:"dom (Clookup (\<c>_impl C G)) = digraph_abs G"
    by (simp add: assms(1-4) dom_c_impl edges_right(2))
  show "e \<in> digraph_abs G \<Longrightarrow> Clookup (\<c>_impl C G) e = c_lookup  (the (cc_lookup C (fst e))) (snd e)"
  proof(goal_cases)
    case 1
    hence luG:"lookup G (fst e) \<noteq> None" "snd e \<in> [the (lookup G (fst e))]\<^sub>s"
      using assms(2) 
      by (fastforce simp add: option.split[of "\<lambda> x. _ \<in>\<^sub>G x"]
           vset.emptyD vset.set.invar_empty vset.set.set_isin 
           digraph_abs_def neighbourhood_def)+
    have snd_e_dom:"(snd e) \<in> dom (c_lookup (the (cc_lookup C (fst e))))"
      using luG assms(5,6) by(fastforce simp add: luG)
    show ?case 
      using  thesis1 snd_e_dom 
      by (auto intro: option_collapse_cong simp add: "1" dom_c_impl  c_impl_lookup)
  qed
qed