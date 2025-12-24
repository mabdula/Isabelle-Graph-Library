section \<open>Bellman-Ford Algorithms with Abstract Datatypes\<close>
theory Bellman_Ford
  imports  "HOL-Library.Extended_Real" 
           Directed_Set_Graphs.Pair_Graph_Specs Directed_Set_Graphs.Awalk  "HOL-Eisbach.Eisbach"
begin 

subsection \<open>Auxiliary Lemmas\<close>

lemma single_diff_remove: "x \<notin> A \<Longrightarrow> A - {x} = A" by simp
lemma cases_distr: "f (case e of (x, y) \<Rightarrow> g x y) = f (g (fst e) (snd e))" for f g e
  by(auto split: prod.splits)
lemma single_in_append: "([a]@xs) = a#xs" by simp

lemma bulast_subset: "set (butlast xs) \<subseteq> set xs" 
  using in_set_butlastD by fastforce

lemma list_cases_both_sides: 
"(xs = [] \<Longrightarrow> P ) \<Longrightarrow> (\<And> x. xs =[x] \<Longrightarrow> P ) \<Longrightarrow> (\<And> x y ys. xs =[x]@ys@[y] \<Longrightarrow> P ) \<Longrightarrow> P "
  by (metis neq_Nil_conv snoc_eq_iff_butlast single_in_append)

lemma induct_list_length2: "length xs \<ge> 2 \<Longrightarrow> (\<And> x y. P [x,y]) 
\<Longrightarrow> (\<And> xs x y z. P (xs@[x,y]) \<Longrightarrow> P(xs@[x,y,z])) \<Longrightarrow> P xs"
proof(induction xs rule: rev_induct)
  case (snoc z xs)
  note IH = this
  show ?case 
  proof(cases xs)
    case (Cons b list)
    note cons = this
    show ?thesis 
    proof(cases list)
      case (Cons b llist)
      then obtain ys x y where axs_subst:"xs = ys@[x,y]"
        by (metis append_Cons append_butlast_last_cancel cons list.distinct(1) snoc_eq_iff_butlast)
      show ?thesis
        using axs_subst IH(3,4) snoc.IH 
        by (fastforce intro: IH(4))
    next
      case Nil
      then show ?thesis
        using cons snoc.prems(2) by fastforce
    qed
    next
      case Nil
      then show ?thesis 
        using snoc.prems(1) by force
    qed
  qed simp

lemma get_longest_common_tail:
assumes "length p \<ge> 1" "length q \<ge> 1" "last p = last q"
obtains ys p' q' where "p = p'@ys" "q =q'@ys" 
                        "\<And> ys' p'' q''. p=p''@ys' \<Longrightarrow> q = q''@ys' \<Longrightarrow> length ys' \<le> length ys"
proof(goal_cases)
  case 1
  have "{length ys |  ys. \<exists> p' q'. p = p'@ys \<and> q =q'@ys} \<noteq> {}"
    using assms by auto
  moreover have finiteset:"finite { length ys |  ys. \<exists> p' q'. p = p'@ys \<and> q =q'@ys}"
    by(fastforce intro: finite_subset[of _ "{length ys |ys. length ys \<le> (length p) }"] 
              simp add: finite_nat_set_iff_bounded_le) 
  ultimately have " Max {length ys |  ys. \<exists> p' q'. p = p'@ys \<and> q =q'@ys} \<in> {length ys |  ys. \<exists> p' q'. p = p'@ys \<and> q =q'@ys}"
    using linorder_class.Max_in by fast
  then obtain ys p' q' where ys_prop: "length ys = Max {length ys |  ys. \<exists> p' q'. p = p'@ys \<and> q =q'@ys}"
                       "p = p'@ys" "q =q'@ys" by fastforce
  show ?case
    using ys_prop(2) ys_prop(3) 
    by (auto intro!: 1[of p' ys q'] Max_ge[OF finiteset, simplified ys_prop(1)[symmetric]] )
qed

definition "backward_determ E = (\<forall> u v w. ((u, v) \<in> E \<and> (w, v) \<in> E) \<longrightarrow> u = w)"

definition "no_cycle E = (\<nexists> p v. closed_vwalk_bet E p v)"

lemma unique_path_backward_determ_acyclic:
  assumes "backward_determ E"  "vwalk_bet E u p v"  "vwalk_bet E u q v"  
          "no_cycle E" "length p \<ge> 2" "length q \<ge> 2"
  shows "p = q" 
proof(rule ccontr, goal_cases)
  case 1
  have same_lasts: " last p = last q"
    by(metis assms(2) assms(3) last_of_vwalk_bet)
  obtain ys p' q' where props:"p = p'@ys" "q = q'@ys"
                                "\<And>  ys' p' q'. p = p'@ys' \<Longrightarrow> q = q'@ys' \<Longrightarrow> length ys' \<le> length ys"
    using assms(5)  assms(6)  same_lasts
    by (auto intro: get_longest_common_tail[of p q])
  have same_end_points: "hd q = u" "hd p = u" "length p \<ge> 2"
                        "last q = v" "last p = v" "length q \<ge> 2"
    using assms by auto
  have ys_non_empt:"ys \<noteq> []" 
    using props(3)[of "butlast p" "[v]" "butlast q"] assms(2) assms(3) last_of_vwalk_bet' by fastforce
  have "p' \<noteq> q'" 
    using "1" props(1) props(2) by auto 
  hence p'_q'_cases:"(p' =[] \<Longrightarrow> q' \<noteq> [] \<Longrightarrow> P) \<Longrightarrow>
         (p' \<noteq>[] \<Longrightarrow> q' = [] \<Longrightarrow> P) \<Longrightarrow>
         (p' \<noteq> [] \<Longrightarrow> q' \<noteq> [] \<Longrightarrow> P) \<Longrightarrow> P" for P by auto
  show ?case
  proof(cases rule: p'_q'_cases)
    case 1
    hence "hd q' = u" "hd ys = u" 
      using assms(3) hd_of_vwalk_bet' props(1,2) 1 same_end_points by auto
    hence "vwalk_bet E u (q'@[u]) u"
      using assms(3) list.collapse props(2) ys_non_empt
      by (intro vwalk_bet_prefix_is_vwalk_bet[of "q'@[u]" E u "tl ys" v, simplified]) fastforce+
    moreover have "length (q'@[u]) \<ge> 2" 
      by (simp add: "1"(2) Suc_leI)
    ultimately show ?thesis 
      using assms(4) no_cycle_def by fastforce
  next
    case 2
    hence "hd p' = u" "hd ys = u" 
      using assms(3) hd_of_vwalk_bet' props(1,2) 1 same_end_points by auto
    hence "vwalk_bet E u (p'@[u]) u"
      using assms list.collapse props ys_non_empt
      by (intro vwalk_bet_prefix_is_vwalk_bet[of "p'@[u]" E u "tl ys" v, simplified]) fastforce+
    moreover have "length (p'@[u]) \<ge> 2" 
      by (simp add: 2 Suc_leI)
    ultimately show ?thesis
      using assms(4) no_cycle_def by fastforce
  next
    case 3
    hence "last p' \<noteq> last q'" 
      using  props(1) props(2) 
       props(3)[of "butlast p'" "last p' # ys" "butlast q'"] by auto
    moreover have "(last p', hd ys) \<in> E" 
      using "3"(1) assms(2) props(1) vwalk_append_edge[of E p' ys] vwalk_bet_props ys_non_empt
      by force
    moreover have "(last q', hd ys) \<in> E" 
      using "3"(2) assms(3) props(2) vwalk_append_edge[of E q' ys] vwalk_bet_props[of E u q v] ys_non_empt 
      by auto
    ultimately show ?thesis 
      using assms(1) by(auto simp add: backward_determ_def)
  qed
qed

lemma unique_path_backward_determ_distinct:
  assumes "backward_determ E"  "vwalk_bet E u p v" "no_cycle E"  "length p \<ge> 2"
  shows "distinct p"
proof(rule ccontr, goal_cases)
  case 1
  have u_not_v:"u \<noteq> v" 
    using assms(2) assms(3) assms(4) no_cycle_def by fastforce
  from 1 obtain x xs ys zs where p_prop:"p = xs@[x]@ys@[x]@zs"
    using not_distinct_decomp by blast
  moreover hence  "vwalk_bet E u (xs@[x]@zs) v"   
    using  assms(2) vwalk_bet_pref[of E u xs x "ys@[x]@zs" v] 
           vwalk_bet_suffix_is_vwalk_bet[of "[x]@zs" E u "xs@[x]@ys" v]
           vwalk_bet_transitive_2[of E u "xs@[x]" x "[x]@zs" v, simplified] 
    by simp
  moreover hence "length (xs@[x]@zs) \<ge> 2" 
    using u_not_v  not_less_eq_eq by (fastforce simp add: vwalk_bet_def) 
  ultimately show ?case 
    using unique_path_backward_determ_acyclic[OF assms(1,2) _ assms(3,4)] p_prop 
    by force
qed

lemma backward_determ_pres: "backward_determ E \<Longrightarrow> (u, v) \<in> E \<Longrightarrow> backward_determ (insert (w, v) (E - {(u, v)}))"
  by(auto simp add: backward_determ_def)

lemma backward_determ_pred: "backward_determ {(pred x, x) | x. x \<in> A}"
  unfolding backward_determ_def by simp

subsection \<open>Bellman Ford Algorithm\<close>

locale bellman_ford_spec = 
  fixes connection_update::"'a \<Rightarrow> 'a option \<times> ereal \<Rightarrow> 'con_impl \<Rightarrow> 'con_impl"
  and connection_empty and connection_lookup and connection_invar and connection_delete
assumes connection_map: "Map connection_empty
                             connection_update connection_delete connection_lookup connection_invar"
fixes es::"('a \<times> 'a) list" and vs::"'a list" and edge_costs::"'a \<Rightarrow> 'a \<Rightarrow> ereal"
begin

definition "bellman_ford_init s = connection_update s (None, 0) 
                                 (foldr (\<lambda> x done. connection_update x (None, PInfty) done) vs connection_empty)"

definition "relax connections  u v =
           (let csu = snd (the (connection_lookup connections u));
                csv = snd (the (connection_lookup connections v));
                cuv = edge_costs u v
             in (if csu + cuv < csv 
                 then connection_update v (Some u, csu + cuv) connections
                 else connections))"

fun bellman_ford::" nat \<Rightarrow> 'con_impl \<Rightarrow> 'con_impl" where
"bellman_ford 0 connections = connections" |
"bellman_ford (Suc n) connections = foldr (\<lambda> (x, y) done. relax done x y) es 
                                         (bellman_ford n connections)"

partial_function (tailrec) search_rev_path_exec where
"search_rev_path_exec s connections v acc=
(if s = v then v#acc
else (let u = the (fst (the (connection_lookup connections v)))
      in search_rev_path_exec s connections u (v#acc)))"

lemmas [code] = search_rev_path_exec.simps bellman_ford.simps relax_def bellman_ford_init_def


function (domintros) search_rev_path where
"search_rev_path s connections v =
(if s = v then [s]
else (let u = the (fst (the (connection_lookup connections v)))
      in v#search_rev_path s connections u))"
  by auto

lemma function_to_partial_function_general:
  assumes "search_rev_path_dom (s, connections, v)"
  shows "rev acc @ search_rev_path s connections v= rev (search_rev_path_exec s connections v acc)"
proof(induction arbitrary: acc  rule: search_rev_path.pinduct[OF assms])
  case (1 s connections v)
  note IH = this
  show ?case 
    apply(subst search_rev_path.psimps)
     apply (simp add: IH(1))
    apply(subst search_rev_path_exec.simps)
    apply(subst if_distrib[of rev])
    apply(subst (8) if_distrib)
    apply(rule if_cong)
      apply simp
     apply simp
    unfolding Let_def
    apply(subst sym[OF IH(2)[OF _ refl]])
     apply simp
    by auto
qed

lemma function_to_partial_function:
  assumes "search_rev_path_dom (s, connections, v)"
  shows "search_rev_path s connections v= rev (search_rev_path_exec s connections v Nil)"
  using function_to_partial_function_general[OF assms, of Nil] by auto

end

locale bellman_ford = bellman_ford_spec where connection_update =
 "connection_update::'a \<Rightarrow> 'a option \<times> ereal \<Rightarrow> 'con_impl \<Rightarrow> 'con_impl"
for connection_update +
assumes no_MInfty_costs: "\<And> u v. edge_costs u v > MInfty"
assumes edge_costs_outside_es:"\<And> u v. edge_costs u v < PInfty \<Longrightarrow> (u, v) \<in> set es"
assumes v_non_empt:"vs \<noteq> []" 
assumes vs_and_es: "set vs = dVs (set es)"
assumes distinct_vs: "distinct vs"
assumes distinct_es: "distinct es"
begin
lemma connection_axioms: "connection_lookup connection_empty = (\<lambda>_. None)"
"\<And> m a b. connection_invar m \<Longrightarrow> connection_lookup (connection_update a b m) = (connection_lookup m)(a \<mapsto> b)" 
"\<And> m a. connection_invar m \<Longrightarrow> connection_lookup (connection_delete a m) = (connection_lookup m)(a := None)"
 "connection_invar connection_empty "
 "\<And> m a b. connection_invar m \<Longrightarrow> connection_invar (connection_update a b m)"
 "(\<And>m a. connection_invar m \<Longrightarrow> connection_invar (connection_delete a m))"
    using connection_map[simplified Map_def] by auto

lemma bellman_ford_init_is: "connection_lookup (bellman_ford_init s) v =
                             (if v = s then Some (None, 0) else (if v \<in> set vs then  Some (None, PInfty)
                               else None))" (is ?th1)
                            "connection_invar (bellman_ford_init s)" (is ?th2)
proof-
  define intermed where "intermed = foldr (\<lambda> x done. connection_update x (None, PInfty) done) vs connection_empty"
  have "connection_lookup intermed v = (if v \<in> set vs then Some (None, PInfty) else None) \<and>
        connection_invar intermed"
    apply((subst intermed_def)+)
    using connection_axioms
    by (induction vs) auto
  hence intermed_is: "connection_lookup intermed v = (if v \<in> set vs then Some (None, PInfty) else None)"
    and invar_intermed: "connection_invar intermed"
    by auto
  show ?th1
    unfolding bellman_ford_init_def sym[OF intermed_def]
    using connection_axioms invar_intermed intermed_is 
    by auto
  show ?th2
    unfolding bellman_ford_init_def sym[OF intermed_def]
    using connection_axioms invar_intermed intermed_is 
    by auto
qed

fun weight where
"weight  [] = 0"|
"weight  [s] = 0"|
"weight (x#y#xs) = edge_costs x y + weight  (y#xs)"

lemma weight_le_PInfty_in_vs:"length P \<ge> 2 \<Longrightarrow> weight P < PInfty \<Longrightarrow> set P \<subseteq> set vs"
  apply(induction P rule: weight.induct, simp, simp)
  subgoal for x y xs
    using edge_costs_outside_es vs_and_es by (cases xs) auto
  done

lemma edge_and_Costs_none_pinfty_weight:
"edge_costs u v = PInfty \<Longrightarrow> xs = xs1@[u, v]@x2 ==> weight xs = PInfty"
  apply(induction xs1 arbitrary: xs)
   apply simp 
  subgoal for a x1
    by(cases x1) auto
  done

lemma real_path: "length xs \<ge> 2 \<Longrightarrow> weight xs < PInfty \<Longrightarrow> awalk (set es) (hd xs) (edges_of_vwalk xs) (last xs)"
proof(induction xs rule: weight.induct)
  case (3 x y xs)
  have a: "weight (y # xs) < PInfty \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> awalk (set es) y (edges_of_vwalk (y # xs)) (last (y # xs))"
    using 3(1)
    by (simp add: Suc_leI)
  have b: "edge_costs x y < PInfty" 
    using "3.prems"(2) by fastforce
  have c: " weight (y # xs) < PInfty" 
    using "3.prems"(2) by force
  show ?case
    apply(cases xs)
    subgoal using 3(2-)
      by (simp add: arc_implies_awalk edge_costs_outside_es)
    apply(subst edges_of_vwalk.simps, subst (3) sym[OF single_in_append])
    apply(rule awalk_appendI[of  _ _ _ y])
    using a b c
    by (auto simp add: arc_implies_awalk edge_costs_outside_es)
qed auto

lemma weight_not_MInfty:" weight xs > MInfty"
  using no_MInfty_costs by(induction xs rule: weight.induct) force+

definition "OPT  l s t = Min ({weight (s # xs @ [t]) | xs. length xs + 1 \<le> l \<and> set xs \<subseteq> set vs } \<union>
                             {if t = s then 0 else \<infinity>})"

definition "bellman_ford_one_step state = foldr (\<lambda> (x, y) done. relax done x y) es 
                                         state"

lemma bellman_ford_upd_one: "bellman_ford (Suc n) connections = 
                             bellman_ford_one_step (bellman_ford n connections)"
  by(simp add: bellman_ford_one_step_def)

lemma finite_of_V: "finite {f xs | xs. P xs \<and> length xs \<le> l \<and> set xs \<subseteq> set vs}"
proof-
  have "finite {xs. length xs \<le> l \<and> set xs \<subseteq> set vs}"
    by (metis (no_types, lifting) Collect_cong List.finite_set finite_lists_length_le)
  thus ?thesis by simp
qed

lemma finite_weight_set: "finite {weight  (s # xs @ [v]) |xs. length xs + 1 \<le> l \<and> set xs \<subseteq> set vs}"
  by(rule rev_finite_subset)
(auto intro!: finite_of_V[of "\<lambda> xs. weight  (s # xs @ [v])" "\<lambda> x. True" l, simplified])

lemma finite_lists_length_le1: "finite {xs. length xs \<le> i \<and> set xs \<subseteq> set vs}" for i
  using  finite_lists_length_le[ of _ i] 
  by (metis (no_types, lifting) Collect_cong List.finite_set)

lemma finite_lists_length_le2: "finite {xs. length xs + 1 \<le> i \<and> set xs \<subseteq> set vs }" for i
  by (auto intro: finite_subset[OF _ finite_lists_length_le1[of "i"]])

lemma OPT_not_MInfty: "OPT  l s t > MInfty"
  unfolding OPT_def
  using finite_weight_set[of  s t l]  weight_not_MInfty[of  ]
  by (intro iffD2[OF linorder_class.Min_gr_iff]) auto
(*Adapted from Lammich and Wimmer*)
lemma OPT_cases:
  obtains (path) xs where "OPT  l s v = weight (s # xs @ [v])" "length xs + 1 \<le> l" "set xs \<subseteq> set vs"
  | (sink) "s = v" "OPT  l s v = 0"
  | (unreachable) "s \<noteq> v" "OPT l s v = \<infinity>"
proof(goal_cases)
  case 1
  have finite_aux: "finite
   ({weight (s # xs @ [v]) |xs. length xs + 1 \<le> l \<and> set xs \<subseteq> set vs } \<union>
    {if s = v then 0 else \<infinity>})" 
    using finite_weight_set by force
  show ?thesis
  using 1 unfolding OPT_def 
  using Min_in[of "{weight  (s # xs @ [v]) |xs. length xs + 1 \<le> l \<and> set xs \<subseteq> set vs }
    \<union> {if s = v then 0 else \<infinity>}", OF finite_aux] 
  by(auto simp: finite_lists_length_le2 split: if_split_asm)
qed

lemma costs_last: "weight  (xs @ [u]) +
       edge_costs u v  = weight (xs @ [u, v]) "
  apply(induction xs, simp) 
  subgoal for a xs
    by(cases xs)  (auto simp add: add.commute add.left_commute)
  done
(*Adapted from Lammich and Wimmer*)
lemma Bellman_Equation:
  assumes "s \<in> set vs"
  shows "OPT  (Suc l) s v = min (OPT  l s v) (Min {OPT  l s u + edge_costs u v | u. u \<in> set vs})"
proof-
  have "OPT  l s u + edge_costs u v \<ge> OPT (Suc l) s v" if u_in_V: "u \<in> set vs" for u
    using OPT_cases[of  l s u]
  proof cases
    case (path xs)
    show ?thesis 
      using costs_last[of "s#xs" u v, simplified] finite_weight_set[of  s v "Suc l"]  path u_in_V 
      by (auto intro!: Min_le exI[where x = "xs@[u]"] simp: add.commute OPT_def)   
  next
    case sink
    have case_is:"edge_costs  u v  = weight (s#[]@[v])" 
      using sink by simp
    show ?thesis 
      apply(subst sink(2), subst OPT_def, rule Min_le)
      using finite_weight_set[of  s v "Suc l"]
      by (simp, subst case_is, subst add_0)  fastforce+
  qed auto
  hence "OPT (Suc l) s v \<le>  (Min {OPT  l s u +  edge_costs u v | u. u \<in> set vs})" 
    using  v_non_empt by (auto intro!: Min.boundedI)
  moreover have "OPT  (Suc l) s v \<le> OPT  l s v"
    using v_non_empt finite_weight_set[of  s v "Suc l"]
    by(auto intro!: Min_antimono simp add: OPT_def )
  ultimately have "OPT  (Suc l) s v \<le> min (OPT l s v) (Min {OPT l s u + edge_costs u v | u. u \<in> set vs})" by simp

  moreover have " OPT  (Suc l) s v \<ge>
    min (OPT  l s v)
     (Min {OPT l s u + edge_costs u v |u. u \<in> set vs})"
  proof(cases rule: OPT_cases[of "Suc l" s v])
    case (path xs)
    show ?thesis 
    proof(cases "length xs +1 \<le> l")
      case True
      have "(OPT l s v) \<le> weight (s # xs @ [v])"       
        using  finite_weight_set[of  s v l]  True path(3) 
        by (auto intro: Min_le simp add:  OPT_def)
      then show ?thesis 
        using path(1)
        by (simp add: min_le_iff_disj)
    next
      case False
      hence length_is: "length xs + 1 = Suc l" using path by simp
      have weight_split_last_egde:"weight  (s # xs @ [v]) = 
            weight (s # xs) + edge_costs (last (s#xs)) v "
        using costs_last[of  "butlast (s#xs)" "last (s#xs)" v]
        by (auto simp add: append_butlast_last_cancel)
      have bigger_than_opt:"weight  (s # xs) \<ge> OPT l s (last (s#xs))"
        unfolding OPT_def
        apply(rule Min_le)
        using finite_weight_set apply auto[1]
        apply(cases xs, simp, insert path(2,3))
        apply(subst last_ConsR, simp)+
        apply(subst  sym[OF append_butlast_last_id[of xs]], simp) 
        using subset_trans[OF bulast_subset[of xs], of "set vs"] by fastforce
      have "Min {OPT l s u + edge_costs u v  |u. u \<in> set vs} \<le> weight  (s # xs @ [v])" 
        apply(subst weight_split_last_egde)
        apply(rule order.trans[of _ "OPT l s (last (s # xs)) + edge_costs (last (s # xs)) v "])          
        using assms path(3)  bigger_than_opt  add_right_mono 
        by (force intro:  Min_le)+
      then show ?thesis using path 
        by (simp add: min_le_iff_disj)
    qed
  next
    case sink
    thus ?thesis using finite_weight_set[of s v l]
      by (auto intro: linorder_class.min.coboundedI1 Min_le simp add:  OPT_def)
  qed simp
  ultimately show ?thesis 
    by order
qed
 
lemma effect_of_relax:
  assumes "connection_invar connections"
  shows "snd (the (connection_lookup (relax connections  x v) v)) =
         min (snd (the (connection_lookup connections x)) + edge_costs x v)
             (snd (the (connection_lookup connections v)))"
       "z \<noteq> v \<Longrightarrow> snd (the (connection_lookup (relax connections  x v) z)) =
                  snd (the (connection_lookup connections z))"
       "z \<noteq> v \<Longrightarrow> fst (the (connection_lookup (relax connections  x v) z)) =
                  fst(the (connection_lookup connections z))"
       "z \<noteq> v \<Longrightarrow> connection_lookup (relax connections  x v) z =
                  connection_lookup connections z"
  using assms
  by (auto simp add: relax_def Let_def connection_axioms(2))

lemma connection_invar_relax_pres: "connection_invar connections \<Longrightarrow>
connection_invar (relax connections x y)"
  by (simp add:  relax_def Let_def connection_axioms(5))

lemma connection_inver_fold_pres: "connection_invar connections \<Longrightarrow>
 connection_invar (foldr (\<lambda>(x, y) done. relax done x y) ds connections)" 
  by(induction ds)(auto intro: connection_invar_relax_pres)

lemma finite_new_best_ways:"finite {OPT l s u + edge_costs u z |u. (u, z) \<in> set ds}" for z
      apply(rule finite_subset[rotated])
      apply(rule finite_imageI[of "set ds" "\<lambda> d. OPT l s (fst d) + edge_costs (fst d) z"], simp)
  by force

lemma vs_OPT_set_split:"{OPT l s u + edge_costs u v |u. u \<in> set vs} = 
        {OPT l s u + edge_costs u v |u. (u, v) \<in> set es} \<union>
        {OPT l s u + edge_costs u v |u. (u, v) \<notin> set es \<and> u \<in> set vs}"
    using vs_and_es  dVs_def by blast
lemma outside_es_inf:"\<And> w . w \<in>  {OPT l s u + edge_costs u v |u. (u, v) \<notin> set es \<and> u \<in> set vs} \<Longrightarrow> w = PInfty"
  using edge_costs_outside_es by auto

(*MOVE elsewhere?*)
lemma min_PInfty_cong: "x = PInfty \<Longrightarrow> y = z \<Longrightarrow> min z x = y"  by simp
lemma  add_inifinites: "finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow>finite B \<Longrightarrow> (\<And> x. x \<in> B \<Longrightarrow> x = PInfty) \<Longrightarrow> Min (A \<union> B) = Min A" for A B
  by (cases "B = {}")(auto simp add: linorder_class.Min_Un min_PInfty_cong)

lemma bellman_ford_step_shortest:
  assumes "connection_invar connections" and
       IH:"\<And> v. snd (the (connection_lookup connections v)) \<le> OPT  l s v" and
          "s \<in> set vs"
    shows "snd (the (connection_lookup (bellman_ford_one_step connections) v)) \<le> OPT (Suc l) s v"
proof-
have "snd (the (connection_lookup
               (foldr (\<lambda>(x, y) done. relax done  x y) es connections) v)) \<le> 
                Min (insert (OPT  l s v) {OPT l s u + edge_costs u v | u. (u, v) \<in> set es})" for v
proof(induction es arbitrary: v)
  case Nil
  then show ?case 
    using IH by auto
next
  case (Cons e es)
  show ?case 
  proof(subst foldr.simps(2), subst o_apply, 
        subst cases_distr[of id "\<lambda>x y done. relax done  x y" e, simplified], 
        cases "snd e = v", goal_cases)
    case 2
    then show ?case
      apply simp
      apply(subst effect_of_relax(2)[of " (foldr (\<lambda>(x, y) done. relax done x y) es connections)" v "snd e" "fst e"])
      apply(rule connection_inver_fold_pres[OF assms(1)])
      apply simp
      using Cons[of v] 
      by (smt (z3) Collect_cong snd_conv)
  next
    case 1 
    have Cons_applied: "(snd (the (connection_lookup (foldr (\<lambda>(x, y) done. relax done x y) es connections) v)))
                        \<le> Min (insert (OPT l s v) {OPT l s u + edge_costs u v |u. (u, v) \<in> set es})" 
      using Cons by fast
    have fst_e_dist_holds:"snd (the (connection_lookup (foldr (\<lambda>(x, y) done. relax done x y) es connections) (fst e)))
          \<le> OPT l s (fst e)"
      apply(rule order.trans)
      using finite_new_best_ways 
      by(auto intro!:  Cons[of "fst e"])
    have extract_e:"(insert (OPT l s v) {OPT l s u + edge_costs u v |u. (u, v) = e \<or> (u, v) \<in> set es}) =
         (insert (OPT l s (fst e) + edge_costs (fst e) v) 
         (insert (OPT l s v) {OPT l s u + edge_costs u v |u. (u, v) \<in> set es}))" 
      using sym[OF 1] 
      by (auto, metis fst_conv) 
    from 1 show ?case 
      apply simp
      apply(subst effect_of_relax(1)[of " (foldr (\<lambda>(x, y) done. relax done x y) es connections)" ])
      apply(rule connection_inver_fold_pres[OF assms(1)])
      apply(subst extract_e, subst linorder_class.Min_insert)
      using finite_new_best_ways fst_e_dist_holds  Cons_applied 
      by (fastforce intro!: linorder_class.min.mono simp add: add_right_mono )+
  qed
qed
  hence A:"snd (the (connection_lookup (bellman_ford_one_step connections) v)) \<le>
         Min (insert (OPT l s v) {OPT l s u + edge_costs u v |u. (u, v) \<in> set es})" 
    by(auto simp add: bellman_ford_one_step_def)
  moreover have  B:"Min (insert (OPT l s v) {OPT l s u + edge_costs u v |u. (u, v) \<in> set es})
                = min (OPT l s v) (Min {OPT l s u + edge_costs u v |u. u \<in> set vs})"
    apply(subst sym[OF linorder_class.Min_insert], simp )
    using v_non_empt 
    apply(simp, subst vs_OPT_set_split, subst sym[OF Un_insert_left], subst add_inifinites)
    using finite_new_best_ways outside_es_inf 
    by auto
  ultimately show ?thesis
    using Bellman_Equation[OF assms(3)] by simp
qed

lemma bellman_ford_step_connection_invar:
  assumes "connection_invar connections" 
  shows "connection_invar (bellman_ford_one_step connections)"
  by (simp add: assms bellman_ford_one_step_def connection_inver_fold_pres)

lemma bellman_ford_connection_invar:
  "connection_invar (bellman_ford l (bellman_ford_init s))"
  using  bellman_ford_init_is(2) bellman_ford_step_connection_invar bellman_ford_upd_one 
  by (induction l) auto

lemma bellman_ford_shortest:
  assumes "s \<in> set vs"
  shows "snd (the (connection_lookup (bellman_ford l (bellman_ford_init s) ) v)) \<le> OPT l s v"
  using assms
proof(induction "bellman_ford_init s" arbitrary: v rule: bellman_ford.induct)
  case (1)
  then show ?case 
     using bellman_ford_init_is(1) bellman_ford_init_is(2) 
     by (auto simp add: OPT_def) 
next
  case (2 l v)
  show ?case 
    apply(subst bellman_ford_upd_one)
    using 2 
    by (auto intro: bellman_ford_step_shortest bellman_ford_connection_invar)
qed

named_theorems invar_lemmas

definition "dom_invar s connections = (dom (connection_lookup connections) = insert s (set vs))"

lemma dom_invar_init[invar_lemmas]: "dom_invar s (bellman_ford_init s)"
  by(auto simp add: dom_invar_def dom_def bellman_ford_init_is(1)) 

lemma change_in_dom_no_change_dom[invar_lemmas]: "connection_invar connections \<Longrightarrow> v \<in> dom (connection_lookup connections) \<Longrightarrow>
                                   dom (connection_lookup (connection_update v val  connections))
                                   = dom (connection_lookup connections)"
  using connection_axioms(2) by (auto simp add: dom_def )

lemma relax_in_dom_no_change_dom[invar_lemmas]: "connection_invar connections \<Longrightarrow> v \<in> dom (connection_lookup connections) \<Longrightarrow>
                                   dom (connection_lookup (relax connections u v)) = dom (connection_lookup connections)"
  using change_in_dom_no_change_dom 
  by (auto simp add: relax_def Let_def)

lemma fold_in_dom_no_change_dom[invar_lemmas]: "connection_invar connections 
  \<Longrightarrow> set (map snd ds) \<subseteq> dom (connection_lookup  connections) \<Longrightarrow>
 dom (connection_lookup (foldr (\<lambda>(x, y) done. relax done x y) ds connections))
 = dom (connection_lookup  connections)" 
proof(induction ds)
  case (Cons a ds)
  show ?case 
    apply(simp, subst case_prod_beta, subst relax_in_dom_no_change_dom)
    using Cons
    by (auto intro: connection_invar_relax_pres connection_inver_fold_pres)
qed simp

lemma dom_invar_connection_realx[invar_lemmas]:"connection_invar connections \<Longrightarrow> dom_invar s connections \<Longrightarrow> u \<in> dom (connection_lookup connections) \<Longrightarrow> 
         v \<in> dom (connection_lookup connections) \<Longrightarrow> (dom_invar s (relax connections u v))"
  using  change_in_dom_no_change_dom
  by (auto simp add: relax_def Let_def dom_invar_def)

lemma relax_invar_dom_pres[invar_lemmas]:
  assumes "connection_invar connections" "dom_invar s connections"
           "set (map snd es) \<subseteq> dom (connection_lookup connections)"
           "set (map fst es) \<subseteq> dom (connection_lookup connections)"
  shows "dom_invar s (bellman_ford_one_step connections)"
   unfolding bellman_ford_one_step_def 
   using assms 
 proof(induction es arbitrary: connections)
   case (Cons a es)
   show ?case 
     apply(simp, subst case_prod_beta, subst dom_invar_connection_realx)
     using connection_inver_fold_pres[OF Cons(2)]
     using Cons (2,3, 4, 5)  fold_in_dom_no_change_dom
     by (auto intro: Cons(1)[simplified])
 qed simp

lemma one_step_same_dom[invar_lemmas]:
  assumes "connection_invar connections"
          "set (map snd es) \<subseteq> dom (connection_lookup connections)"
    shows "dom (connection_lookup (bellman_ford_one_step connections)) =
                dom (connection_lookup connections)"
  unfolding bellman_ford_one_step_def 
  using assms by(rule fold_in_dom_no_change_dom)

lemma  invar_after_Folds[invar_lemmas]:"connection_invar (foldr (\<lambda>x. connection_update x (f x)) ( us) connection_empty)"
    by(induction us) (auto simp add: connection_axioms(4) connection_axioms(5))

lemma vs_is_dom: "set vs = dom (connection_lookup (foldr (\<lambda>x. connection_update x (None, PInfty)) vs connection_empty))"
  proof(induction vs arbitrary: es)
   case (Cons a vs)
   show ?case 
    using invar_after_Folds  Cons
    by (auto simp add: dom_def  connection_axioms(2) )
qed (auto simp add: connection_axioms(1) dom_def)

lemma same_domain_bellman_ford[invar_lemmas]:
"dom (connection_lookup (bellman_ford l (bellman_ford_init s))) =
dom (connection_lookup (bellman_ford_init s))"
proof(induction l)
  case (Suc l)
 have "set (map snd es) \<subseteq> set vs" 
    by (smt (verit, best) dVsI'(2) image_iff image_set subset_code(1) vs_and_es)
  hence map_snd_subs:"set (map snd es) \<subseteq> dom (connection_lookup (bellman_ford_init s))"
    using invar_after_Folds vs_is_dom
    by (auto simp add:  connection_axioms(2) bellman_ford_init_def dom_def)
  show ?case 
    apply(subst bellman_ford_upd_one, subst one_step_same_dom)
    using Suc map_snd_subs 
    by (auto intro:  bellman_ford_connection_invar)
qed simp

lemma bellman_ford_init_dom_is[invar_lemmas]: "dom (connection_lookup (bellman_ford_init s)) = insert s (set vs)"
  using dom_invar_def dom_invar_init by auto

definition "invar_pred_non_infty s connections = 
           (\<forall> v \<in> dom (connection_lookup connections).
           (snd (the (connection_lookup connections v))) < PInfty
          \<longleftrightarrow> (v = s \<or> fst  (the (connection_lookup connections v)) \<noteq> None))"

lemma relax_invar_pred_non_infty_pres[invar_lemmas]:
  assumes "invar_pred_non_infty s connections" "connection_invar connections"
          "v \<in> dom (connection_lookup connections)"
          "u \<in> dom (connection_lookup connections)"
  shows "invar_pred_non_infty s (relax connections u v)"
  unfolding invar_pred_non_infty_def 
proof(subst relax_in_dom_no_change_dom[OF assms(2,3)], rule, goal_cases)
  case (1 w)
  show ?case 
  proof(cases "w = v")
    case True
    then show ?thesis 
      apply(simp, subst effect_of_relax(1))
      using assms(1,3,4)
      by (auto simp add: assms(2) connection_axioms(2) invar_pred_non_infty_def relax_def Let_def )
  next
    case False
    then show ?thesis 
      using subst effect_of_relax 1 assms
      by (auto simp add: invar_pred_non_infty_def )
  qed
qed

lemma foldr_invar_pred_non_infty_pres[invar_lemmas]: 
  assumes "invar_pred_non_infty s connections" "connection_invar connections"
          "set (map snd ds) \<subseteq> dom (connection_lookup connections)"
          "set (map fst ds) \<subseteq> dom (connection_lookup connections)"
  shows "invar_pred_non_infty s (foldr (\<lambda>(x, y) done. relax done x y) ds connections)"
  using assms
proof(induction ds)
  case (Cons a ds)
  show ?case 
    apply(subst subst foldr.simps(2), subst o_apply)
    apply(subst cases_distr[of id "\<lambda>x y done. relax done  x y" _, simplified])
    using Cons assms  connection_inver_fold_pres fold_in_dom_no_change_dom 
    by (intro relax_invar_pred_non_infty_pres) auto
qed simp

lemma one_step_invar_pred_non_infty_pres[invar_lemmas]:
  assumes "invar_pred_non_infty s connections" "connection_invar connections"
          "set vs \<subseteq> dom (connection_lookup connections)"
  shows "invar_pred_non_infty s (bellman_ford_one_step connections)"
  unfolding bellman_ford_one_step_def
  using assms vs_and_es 
  by (intro foldr_invar_pred_non_infty_pres) auto

lemma bellman_ford_init_invar_pred_non_infty[invar_lemmas]:
 "invar_pred_non_infty s (bellman_ford_init s)"
  by (auto simp add: invar_pred_non_infty_def bellman_ford_init_is(1) bellman_ford_init_dom_is)

lemma bellman_ford_pred_non_infty_pres[invar_lemmas]:
 "invar_pred_non_infty s (bellman_ford l (bellman_ford_init s))"
proof(induction l)
  case (Suc l)
  show ?case 
    using Suc bellman_ford_connection_invar bellman_ford_init_dom_is 
          same_domain_bellman_ford vs_and_es 
    by (fastforce intro!: foldr_invar_pred_non_infty_pres)
qed (simp add: bellman_ford_init_invar_pred_non_infty)

definition "invar_pred_in_dom s connections = 
           (\<forall> v \<in> dom (connection_lookup connections).
           (fst  (the (connection_lookup connections v)) \<noteq> None) 
               \<longrightarrow> the (fst  (the (connection_lookup connections v))) \<in> dom (connection_lookup connections))"

lemma relax_invar_pred_in_dom_pres[invar_lemmas]:
  assumes "invar_pred_in_dom s connections" "connection_invar connections"
          "v \<in> dom (connection_lookup connections)"
          "u \<in> dom (connection_lookup connections)"
  shows "invar_pred_in_dom s (relax connections u v)"
  unfolding invar_pred_in_dom_def 
proof(subst relax_in_dom_no_change_dom[OF assms(2,3)], rule, goal_cases)
  case (1 w)
  show ?case 
  proof(cases "w = v")
    case True
    then show ?thesis 
      using assms
      by (auto simp add: assms(2) connection_axioms(2) invar_pred_in_dom_def relax_def Let_def )
  next
    case False
    then show ?thesis 
      using relax_in_dom_no_change_dom  subst effect_of_relax 1 assms
      by (auto simp add: invar_pred_in_dom_def )
  qed
qed

lemma foldr_invar_pred_in_dom_pres[invar_lemmas]: 
  assumes "invar_pred_in_dom s connections" "connection_invar connections"
          "set (map snd ds) \<subseteq> dom (connection_lookup connections)"
          "set (map fst ds) \<subseteq> dom (connection_lookup connections)"
  shows "invar_pred_in_dom s (foldr (\<lambda>(x, y) done. relax done x y) ds connections)"
  using assms
proof(induction ds)
  case (Cons a ds)
  show ?case 
    apply(subst subst foldr.simps(2), subst o_apply)
    apply(subst cases_distr[of id "\<lambda>x y done. relax done  x y" _, simplified])
    using Cons assms  connection_inver_fold_pres fold_in_dom_no_change_dom 
    by (intro relax_invar_pred_in_dom_pres) auto
qed (auto simp add: assms(1))

lemma one_step_invar_pred_in_dom_pres[invar_lemmas]:
  assumes "invar_pred_in_dom s connections" "connection_invar connections"
          "set vs \<subseteq> dom (connection_lookup connections)"
  shows "invar_pred_in_dom s (bellman_ford_one_step connections)"
  unfolding bellman_ford_one_step_def
  using assms vs_and_es 
  by (intro foldr_invar_pred_in_dom_pres) auto

lemma bellman_ford_init_invar_pred_in_dom[invar_lemmas]:
" invar_pred_in_dom s (bellman_ford_init s)"
  by (auto simp add: invar_pred_in_dom_def bellman_ford_init_is(1) bellman_ford_init_dom_is)

lemma bellman_ford_pred_in_dom_pres[invar_lemmas]:
"invar_pred_in_dom s (bellman_ford l (bellman_ford_init s))"
proof(induction l)
  case (Suc l)
  show ?case 
    using Suc bellman_ford_connection_invar bellman_ford_init_dom_is 
          same_domain_bellman_ford vs_and_es 
    by (fastforce intro!: foldr_invar_pred_in_dom_pres)
qed (simp add: bellman_ford_init_invar_pred_in_dom)

definition "invar_s_pred_remains_zero s connections = 
(snd (the (connection_lookup connections s)) \<noteq> 0 \<longrightarrow> fst (the (connection_lookup connections s)) \<noteq> None)"

lemma relax_invar_s_pred_remains_zero_pres[invar_lemmas]:
  assumes "invar_s_pred_remains_zero s connections" "connection_invar connections"     
  shows "invar_s_pred_remains_zero s (relax connections u v)"
  using assms 
  by (auto simp add: connection_axioms(2) invar_s_pred_remains_zero_def relax_def Let_def )

lemma foldr_invar_s_pred_remains_zero_pres[invar_lemmas]: 
  assumes "invar_s_pred_remains_zero s connections" "connection_invar connections"
  shows "invar_s_pred_remains_zero s (foldr (\<lambda>(x, y) done. relax done x y) ds connections)"
  using assms
proof(induction ds)
  case (Cons a ds)
  show ?case 
    apply(subst subst foldr.simps(2), subst o_apply)
    apply(subst cases_distr[of id "\<lambda>x y done. relax done  x y" _, simplified])
    using Cons assms  connection_inver_fold_pres fold_in_dom_no_change_dom 
    by (intro relax_invar_s_pred_remains_zero_pres) auto
qed (auto simp add: assms(1))

lemma one_step_invar_s_pred_remains_zero_pres[invar_lemmas]:
  assumes "invar_s_pred_remains_zero s connections" "connection_invar connections"
          "set vs \<subseteq> dom (connection_lookup connections)"
  shows "invar_s_pred_remains_zero s (bellman_ford_one_step connections)"
  unfolding bellman_ford_one_step_def
  using assms vs_and_es 
  by (intro foldr_invar_s_pred_remains_zero_pres) auto

lemma bellman_ford_init_invar_s_pred_remains_zero[invar_lemmas]:
" invar_s_pred_remains_zero s (bellman_ford_init s)"
  by (auto simp add: invar_s_pred_remains_zero_def bellman_ford_init_is(1) bellman_ford_init_dom_is)

lemma bellman_ford_s_pred_remains_zero_pres[invar_lemmas]:
"invar_s_pred_remains_zero s (bellman_ford l (bellman_ford_init s))"
proof(induction l)
  case (Suc l)
  show ?case 
    using Suc bellman_ford_connection_invar bellman_ford_init_dom_is 
          same_domain_bellman_ford vs_and_es 
    by (fastforce intro!: foldr_invar_s_pred_remains_zero_pres)
qed (simp add: bellman_ford_init_invar_s_pred_remains_zero)

definition "invar_pred_path s connections = 
           (\<forall> v \<in> dom (connection_lookup connections).
           (fst  (the (connection_lookup connections v)) \<noteq> None) 
               \<longrightarrow> (\<exists> p. weight (p@[v])
                          = snd  (the (connection_lookup connections v))
                        \<and> last (p) =  the (fst  (the (connection_lookup connections v)))
                        \<and> hd p = s \<and> length p \<ge> 1 \<and> set (p@[v]) \<subseteq> insert s (set vs)))"

lemma relax_invar_pred_path_pres[invar_lemmas]:
  assumes "invar_pred_path s connections" "connection_invar connections"
          "v \<in> dom (connection_lookup connections)"
          "u \<in> dom (connection_lookup connections)"
          "invar_pred_non_infty s connections"
          "invar_s_pred_remains_zero s connections"
  shows "invar_pred_path s (relax connections u v)"
  unfolding invar_pred_path_def 
proof(subst relax_in_dom_no_change_dom[OF assms(2,3)], rule, goal_cases)
  case (1 w)
  show ?case 
  proof(cases "w = v")
    case True
    note w_is_v = this
    show ?thesis 
    proof((subst w_is_v)+, rule, cases "snd (the (connection_lookup connections u)) + edge_costs u v
                   < snd (the (connection_lookup connections v))", goal_cases)
      case 1
      hence " edge_costs u v < PInfty"
        by force
      hence v_in_vs:"v \<in> insert s (set vs)" 
        using edge_costs_outside_es in_dVsE(2)[of v "set es"]  vs_and_es by auto
      from 1(2) have length_w_is:"snd (the (connection_lookup (relax connections u v) v)) =
            snd (the (connection_lookup connections u)) + edge_costs u v"
        using  assms by (auto simp add: relax_def Let_def connection_axioms(2))
      from 1(2) have pred_is:"fst (the (connection_lookup (relax connections u v) v)) = Some u"
        using  assms by (auto simp add: relax_def Let_def connection_axioms(2))
      have "snd (the (connection_lookup connections u)) < PInfty" 
        using "1"(2) by force
      hence pred_or_is_s:"fst (the (connection_lookup connections u)) \<noteq> None \<or> u = s"
        using assms(5,4) by(auto simp add:invar_pred_non_infty_def)
      hence u_has_pred_implies_path:"fst (the (connection_lookup connections u)) \<noteq> None 
 \<Longrightarrow> \<exists>p. weight (p @ [u]) = snd (the (connection_lookup connections u)) \<and>
            last p = the (fst (the (connection_lookup connections u))) \<and> hd p = s \<and> 1 \<le> length p
            \<and> set (p@[u]) \<subseteq> insert s (set vs)"
        using assms(1,4) unfolding invar_pred_path_def by simp     
      show ?case
      proof(subst length_w_is, subst pred_is, cases "u = s", goal_cases)
        case 1
        show ?case 
        proof(cases " snd (the (connection_lookup connections u)) = 0")
          case True
          hence "weight ([u] @ [v]) = snd (the (connection_lookup connections u)) + edge_costs u v"
                "last [u] = the (Some u)" "hd [u] = s" "length [u] \<ge> 1" "set ([u]@[v]) \<subseteq> insert s(set vs)"
            using 1  v_in_vs by auto
          then show ?thesis by fast
        next
          case False
          hence "fst (the (connection_lookup connections u)) \<noteq> None" 
            using "1" assms(6) invar_s_pred_remains_zero_def by blast
          then obtain p where  p_prop:"weight (p @ [u]) = snd (the (connection_lookup connections u))"
            "last p = the (fst (the (connection_lookup connections u)))" "hd p = s" "length p \<ge> 1"
             "set (p@[u]) \<subseteq> insert s(set vs)"
            using u_has_pred_implies_path by blast
          moreover hence  aa:"weight (p @ [u]@[v]) = snd (the (connection_lookup connections u)) + edge_costs u v "
            using sym[OF costs_last] by simp
          show ?thesis
            apply(rule exI[of _ "p@[u]"])  
            using aa  p_prop(3,4,5) "1"  v_in_vs
            by(cases p) auto
        qed
      next
        case 2
           then obtain p where  p_prop: "weight (p @ [u]) = snd (the (connection_lookup connections u))"
            "last p = the (fst (the (connection_lookup connections u)))" "hd p = s" "length p \<ge> 1"
             "set (p@[u]) \<subseteq> insert s(set vs)"
             using pred_or_is_s u_has_pred_implies_path by blast
          moreover hence  aa:"weight (p @ [u]@[v]) = snd (the (connection_lookup connections u)) + edge_costs u v "
            using sym[OF costs_last] by simp
          show ?case
            apply(rule exI[of _ "p@[u]"])  
            using aa  p_prop(3,4,5) "1"  v_in_vs
            by(cases p) auto 
        qed
      next
        case 2
       from 2(2) have length_w_is:"snd (the (connection_lookup (relax connections u v) v)) =
            snd (the (connection_lookup connections v))"
        using  assms by (auto simp add: relax_def Let_def connection_axioms(2))
      from 2(2) have pred_is:"fst (the (connection_lookup (relax connections u v) v)) =
                             fst (the (connection_lookup  connections  v))"
        using  assms by (auto simp add: relax_def Let_def connection_axioms(2))
      obtain p where " weight (p @ [v]) = snd (the (connection_lookup connections v))"
                     " last p = the (fst (the (connection_lookup connections v)))" 
                     "hd p = s" "1 \<le> length p"  "set (p@[v]) \<subseteq> insert s(set vs)"
        using assms(1)  "2"(1) assms(3) pred_is 
        by (auto simp add:invar_pred_path_def)
      thus ?case
        using length_w_is pred_is by auto
    qed
  next
    case False
    show ?thesis
      using assms(2-) False  1 assms(1)[simplified invar_pred_path_def] 
      by (auto simp add: effect_of_relax(2,3))
  qed
qed
  
lemma foldr_invar_pred_path_pres[invar_lemmas]: 
  assumes "invar_pred_path s connections" "connection_invar connections"
          "set (map snd ds) \<subseteq> dom (connection_lookup connections)"
          "set (map fst ds) \<subseteq> dom (connection_lookup connections)"
          "invar_s_pred_remains_zero s connections"
          "invar_pred_non_infty s connections"
  shows "invar_pred_path s (foldr (\<lambda>(x, y) done. relax done x y) ds connections)"
  using assms
proof(induction ds)
  case (Cons a ds)
  show ?case 
    apply(subst subst foldr.simps(2), subst o_apply)
    apply(subst cases_distr[of id "\<lambda>x y done. relax done  x y" _, simplified])
    apply(rule relax_invar_pred_path_pres)
    apply(rule Cons(1))
    using connection_inver_fold_pres  fold_in_dom_no_change_dom  Cons(2-) assms 
          foldr_invar_pred_non_infty_pres  foldr_invar_s_pred_remains_zero_pres
    by auto
qed (auto simp add: assms(1))

lemma one_step_invar_pred_path_pres[invar_lemmas]:
  assumes "invar_pred_path s connections" "connection_invar connections"
          "set vs \<subseteq> dom (connection_lookup connections)"
          "invar_s_pred_remains_zero s connections"
          "invar_pred_non_infty s connections"
  shows "invar_pred_path s (bellman_ford_one_step connections)"
  unfolding bellman_ford_one_step_def
  using assms vs_and_es 
  by (intro foldr_invar_pred_path_pres) auto

lemma bellman_ford_init_invar_pred_path[invar_lemmas]:
" invar_pred_path s (bellman_ford_init s)"
  by (auto simp add: invar_pred_path_def bellman_ford_init_is(1) bellman_ford_init_dom_is)

lemma bellman_ford_invar_pred_path_pres[invar_lemmas]:
"invar_pred_path s (bellman_ford l (bellman_ford_init s))"
proof(induction l)
  case (Suc l)
  show ?case 
    using Suc bellman_ford_connection_invar bellman_ford_init_dom_is 
          same_domain_bellman_ford vs_and_es  bellman_ford_pred_non_infty_pres 
          bellman_ford_s_pred_remains_zero_pres bellman_ford_upd_one
          one_step_invar_pred_path_pres[of s ] 
    by fastforce
qed (simp add: bellman_ford_init_invar_pred_path)

definition "invar_pred_has_pred s connections = 
           (\<forall> v \<in> dom (connection_lookup connections). 
          (let pred =
           fst  (the (connection_lookup connections v))
           in (pred \<noteq> None  
               \<longrightarrow>  (fst  (the (connection_lookup connections (the pred))) \<noteq> None \<or> the pred = s))))"

lemma invar_pred_has_pred_init[invar_lemmas]:"invar_pred_has_pred s (bellman_ford_init s)"
  by(auto simp add: bellman_ford_init_is(1) invar_pred_has_pred_def dom_def)

lemma relax_invar_pred_has_pred_pres[invar_lemmas]:
  assumes "invar_pred_has_pred s connections" "connection_invar connections"
          "v \<in> dom (connection_lookup connections)"
          "u \<in> dom (connection_lookup connections)"
          "invar_pred_non_infty s connections"
  shows "invar_pred_has_pred s (relax connections u v)"
  unfolding invar_pred_has_pred_def Let_def
proof(subst relax_in_dom_no_change_dom[OF assms(2,3)], rule, rule, goal_cases)
  case (1 w)
  show ?case 
  proof(cases "w = v")
    case True
    note w_is_v = this
    show ?thesis 
    proof((subst w_is_v)+, cases "snd (the (connection_lookup connections u)) + edge_costs u v
                   < snd (the (connection_lookup connections v))", goal_cases)
      case 1
      from 1(1) have length_w_is:"snd (the (connection_lookup (relax connections u v) v)) =
            snd (the (connection_lookup connections u)) + edge_costs u v"
        using  assms by (auto simp add: relax_def Let_def connection_axioms(2))
      from 1(1) have pred_is:"fst (the (connection_lookup (relax connections u v) v)) = Some u"
        using  assms by (auto simp add: relax_def Let_def connection_axioms(2))
      have "snd (the (connection_lookup connections u)) < PInfty" 
        using "1"(1) by force
      hence pred_or_is_s:"fst (the (connection_lookup connections u)) \<noteq> None \<or> u = s"
        using assms(5,4) by(auto simp add:invar_pred_non_infty_def)
      thus ?case 
        using assms(2) effect_of_relax(4) option.distinct(1) pred_is
        by(cases "u = v") auto
      next
        case 2
        then show ?case
          using assms(1) 1 w_is_v 
          by (auto simp add: invar_pred_has_pred_def Let_def relax_def)
      qed
    next
      case False
      note false=this
      have connection_of_w:"connection_lookup (relax connections u v) w =
             connection_lookup connections w"
        by (simp add: False assms(2) effect_of_relax(4))
      hence pred_not_none:"fst (the (connection_lookup connections w)) \<noteq> None"
        using "1"(2) by force
      show ?thesis
      proof(cases "the (fst (the (connection_lookup connections w))) = v")
        case True
        then show ?thesis 
        using connection_of_w  assms 1 False
        by(force simp add:  effect_of_relax(4) relax_def connection_axioms(2) invar_pred_has_pred_def Let_def) 
      next
        case False
        then show ?thesis 
          using"1"(1) assms pred_not_none
          by(auto simp add: connection_of_w effect_of_relax(4) invar_pred_has_pred_def Let_def)
      qed
    qed
  qed
  
lemma foldr_invar_pred_has_pred_pres[invar_lemmas]: 
  assumes "invar_pred_has_pred s connections" "connection_invar connections"
          "set (map snd ds) \<subseteq> dom (connection_lookup connections)"
          "set (map fst ds) \<subseteq> dom (connection_lookup connections)"
          "invar_pred_non_infty s connections"
  shows "invar_pred_has_pred s (foldr (\<lambda>(x, y) done. relax done x y) ds connections)"
  using assms
proof(induction ds)
  case (Cons a ds)
  show ?case 
    apply(subst subst foldr.simps(2), subst o_apply)
    apply(subst cases_distr[of id "\<lambda>x y done. relax done  x y" _, simplified])
    apply(rule relax_invar_pred_has_pred_pres)
    apply(rule Cons(1))
    using connection_inver_fold_pres  fold_in_dom_no_change_dom  Cons(2-) assms 
          foldr_invar_pred_non_infty_pres  foldr_invar_s_pred_remains_zero_pres
    by auto
qed (auto simp add: assms(1))

lemma one_step_invar_pred_has_pred_pres[invar_lemmas]:
  assumes "invar_pred_has_pred s connections" "connection_invar connections"
          "set vs \<subseteq> dom (connection_lookup connections)"
          "invar_pred_non_infty s connections"
  shows "invar_pred_has_pred s (bellman_ford_one_step connections)"
  unfolding bellman_ford_one_step_def
  using assms vs_and_es 
  by (intro foldr_invar_pred_has_pred_pres) auto

lemma bellman_ford_init_invar_pred_has_pred[invar_lemmas]:
" invar_pred_has_pred s (bellman_ford_init s)"
  by (auto simp add: invar_pred_has_pred_def bellman_ford_init_is(1) bellman_ford_init_dom_is)

lemma bellman_ford_invar_pred_has_pred_pres[invar_lemmas]:
"invar_pred_has_pred s (bellman_ford l (bellman_ford_init s))"
proof(induction l)
  case (Suc l)
  show ?case 
    using Suc bellman_ford_connection_invar bellman_ford_init_dom_is 
          same_domain_bellman_ford vs_and_es  bellman_ford_pred_non_infty_pres 
          bellman_ford_s_pred_remains_zero_pres bellman_ford_upd_one
          one_step_invar_pred_has_pred_pres[of s ] 
    by fastforce
qed (simp add: bellman_ford_init_invar_pred_has_pred)

definition "invar_pred_mono connections = 
           (\<forall> v \<in> dom (connection_lookup connections). 
          (let pred =
           fst  (the (connection_lookup connections v))
           in (pred \<noteq> None  
               \<longrightarrow>  snd (the (connection_lookup connections v)) \<ge>
                    snd (the (connection_lookup connections  (the pred)))
                                             + edge_costs (the pred) v)))"

lemma invar_pred_pred_mono_init[invar_lemmas]:"invar_pred_mono (bellman_ford_init s)"
  by(auto simp add: bellman_ford_init_is(1) invar_pred_mono_def dom_def)

lemma relax_mono[invar_lemmas]:
"connection_invar connections \<Longrightarrow> w = v \<or> w \<in> (dom (connection_lookup connections)) \<Longrightarrow> 
snd (the (connection_lookup (relax connections u v) w)) \<le>
snd (the (connection_lookup connections w))"
  using connection_axioms(2)
  by (auto simp add: relax_def Let_def)

lemma relax_invar_pred_mono_pres[invar_lemmas]:
  assumes "invar_pred_mono connections" "connection_invar connections"
          "v \<in> dom (connection_lookup connections)"
          "u \<in> dom (connection_lookup connections)"
          "invar_pred_in_dom s connections"
  shows "invar_pred_mono (relax connections u v)"
  unfolding invar_pred_mono_def Let_def
proof(subst relax_in_dom_no_change_dom[OF assms(2,3)], rule, rule, goal_cases)
  case (1 w)
  show ?case 
  proof(cases "w = v")
    case True
    note w_is_v = this
    show ?thesis
    proof((subst w_is_v)+, cases "snd (the (connection_lookup connections u)) + edge_costs u v
                   < snd (the (connection_lookup connections v))", goal_cases)
      case 1
      from 1(1) have length_w_is:"snd (the (connection_lookup (relax connections u v) v)) =
            snd (the (connection_lookup connections u)) + edge_costs u v"
        using  assms by (auto simp add: relax_def Let_def connection_axioms(2))
      from 1(1) have pred_is:"fst (the (connection_lookup (relax connections u v) v)) = Some u"
        using  assms by (auto simp add: relax_def Let_def connection_axioms(2))
      thus ?case 
        using relax_mono 
        by (auto simp add: pred_is length_w_is add_right_mono assms(2) assms(4))
      next
        case 2
        thus  ?case 
          using 1 assms(1, 3)  w_is_v 
          by(force simp add: invar_pred_mono_def relax_def Let_def )
      qed
    next
      case False
      have in_dom:"(the (fst (the (connection_lookup connections w)))) \<in>
            dom (connection_lookup connections)"  
        using assms(5) 1 False assms(2) effect_of_relax(4)
        by (simp add: invar_pred_in_dom_def)
      have before: "snd (the (connection_lookup connections (the (fst (the (connection_lookup connections w)))))) +
       edge_costs (the (fst (the (connection_lookup connections w)))) w
       \<le> snd (the (connection_lookup connections w))" 
        using 1 False assms(1) assms(2) effect_of_relax(3) 
        by(force simp add: invar_pred_mono_def)
      show ?thesis
        using False  relax_mono in_dom assms(2) before 
        by (auto simp add: effect_of_relax(2,3) add.commute add_left_mono dual_order.trans)
    qed
  qed
  
lemma foldr_invar_pred_mono_pres[invar_lemmas]: 
  assumes "invar_pred_mono connections" "connection_invar connections"
          "set (map snd ds) \<subseteq> dom (connection_lookup connections)"
          "set (map fst ds) \<subseteq> dom (connection_lookup connections)"
          "invar_pred_in_dom s connections"
  shows "invar_pred_mono (foldr (\<lambda>(x, y) done. relax done x y) ds connections)"
  using assms
proof(induction ds)
  case (Cons a ds)
  show ?case 
    apply(subst subst foldr.simps(2), subst o_apply)
    apply(subst cases_distr[of id "\<lambda>x y done. relax done  x y" _, simplified])
    apply(rule relax_invar_pred_mono_pres)
    apply(rule Cons(1))
    using connection_inver_fold_pres  fold_in_dom_no_change_dom  Cons(2-) assms 
          foldr_invar_pred_non_infty_pres  foldr_invar_s_pred_remains_zero_pres
          foldr_invar_pred_in_dom_pres
    by auto
qed (auto simp add: assms(1))

lemma one_step_invar_pred_mono_pres[invar_lemmas]:
  assumes "invar_pred_mono connections" "connection_invar connections"
          "set vs \<subseteq> dom (connection_lookup connections)"
          "invar_pred_in_dom s connections"
  shows "invar_pred_mono (bellman_ford_one_step connections)"
  unfolding bellman_ford_one_step_def
  using assms vs_and_es 
  by (intro foldr_invar_pred_mono_pres) auto

lemma bellman_ford_invar_pred_mono_pres:
"invar_pred_mono (bellman_ford l (bellman_ford_init s))"
proof(induction l)
  case (Suc l)
  show ?case 
    using Suc bellman_ford_connection_invar 
          vs_and_es   bellman_ford_upd_one
          one_step_invar_pred_mono_pres[of _ s] invar_lemmas
    by (auto simp add: subsetI)
qed (simp add: invar_lemmas)

definition "pred_graph connections =
            {((the (fst (the (connection_lookup connections v)))), v) |
               v. v \<in> dom (connection_lookup connections) 
                  \<and> (fst (the (connection_lookup connections v))) \<noteq> None}"

definition "invar_pred_acyc connections = 
 (\<nexists> v p. vwalk_bet (pred_graph connections) v p v \<and> length p \<ge> 2)"

definition "vs_path s t xs = (length xs \<ge> 2 \<and> hd xs = s \<and> last xs = t \<and> set xs \<subseteq> set vs)"

lemma vsp_pathI: "length xs \<ge> 2 \<Longrightarrow> hd xs = s \<Longrightarrow> last xs = t \<Longrightarrow> set xs \<subseteq> set vs \<Longrightarrow> vs_path s t xs"
  by(auto simp add: vs_path_def)

definition "opt_vs_path s t xs = (vs_path s t xs \<and> (\<forall> ys. vs_path s t ys \<longrightarrow> weight ys \<ge> weight xs))"

lemma weight_sum_edge_costs:"distinct xs \<Longrightarrow> weight xs = 
sum (\<lambda> (u, v). edge_costs u v) (set (edges_of_vwalk xs))"
  apply(induction xs rule: weight.induct, simp, simp)
  apply(subst edges_of_vwalk.simps)
  apply(subst  List.set_simps(2))
  apply(subst comm_monoid_add_class.sum.insert_remove)
  apply simp
  apply(subst single_diff_remove)
  apply (meson distinct.simps(2) v_in_edge_in_vwalk(1))
  by(auto split: prod.splits simp add: algebra_simps)

lemma finite_sum_less_PInfty:"finite A \<Longrightarrow> (\<And> x. x \<in> A \<Longrightarrow> f x < PInfty) \<Longrightarrow> sum f A < PInfty "
  apply(induction A rule: finite_induct, simp)
  apply(subst comm_monoid_add_class.sum.insert_remove) 
  by auto

lemma weight_list_split:"weight (xs@[u, v]@ys) =weight (xs@[u]) + edge_costs u v + weight ([v]@ys)"
  apply(induction xs, simp)
  subgoal for a xs
    by(cases xs)
      (auto simp add: group_cancel.add1 ab_semigroup_add_class.add_ac(1))
  done

lemma weight_list_split':"weight (xs@[u]@ys) =weight (xs@[u])+  weight ([u]@ys)"
  apply(induction xs, simp)
  subgoal for a xs
    by(cases xs)
      (auto simp add: group_cancel.add1 ab_semigroup_add_class.add_ac(1))
  done

lemma  search_rev_path_exec_acc_assoc:
  assumes "search_rev_path_dom (s, connections, z)"
shows
    "rev acc @ rev (search_rev_path_exec s connections z bcc) =
    rev (search_rev_path_exec s connections z (bcc@acc))"
proof(induction arbitrary:  acc bcc rule: search_rev_path.pinduct[OF assms])
  case (1 s connections v)
  then show ?case 
    apply(subst search_rev_path_exec.simps)
    apply(subst (2) search_rev_path_exec.simps)
    by auto
qed

lemma weight_append_last: "weight (xs@[u,v]) = weight (xs@[u]) +edge_costs u v"
  apply(induction xs, simp)
  subgoal for a xs
    apply(cases xs)
    by(cases xs)(auto simp add: algebra_simps)
  done

lemma weight_pred_path:
  assumes  "length p \<ge> 2" "invar_pred_mono connections"
           "vwalk_bet (pred_graph (connections)) u p v" 
     shows "snd (the (connection_lookup connections v)) \<ge>
            snd (the (connection_lookup connections u)) + weight p"
  using assms(2-)
proof(induction arbitrary: v rule: induct_list_length2[OF assms(1)])
  case (1 x y)
  hence uv:"(u, v) = (x,y)" "(u, v) \<in> pred_graph connections" 
    using hd_of_vwalk_bet' last_of_vwalk_bet "1.prems"(2) vwalk_bet_nonempty_vwalk(3,4)
    by fastforce+
  hence "v\<in>dom (connection_lookup connections)" "(fst (the (connection_lookup connections v))) = Some u"
    by (auto simp add: pred_graph_def)
  hence "snd (the (connection_lookup connections u)) +  edge_costs u v
      \<le> snd (the (connection_lookup connections v))"
    using 1(1)[simplified invar_pred_mono_def Let_def] by auto
  then show ?case 
    using uv(1) by simp
next
  case (2 xs x y z v)
    hence uv:"v = z" "(y, v) \<in> pred_graph connections"
      using "2.prems"(2) last_of_vwalk_bet split_vwalk 
      by (simp add: vwalk_bet_def, fastforce)
  hence vy:"v\<in>dom (connection_lookup connections)" "(fst (the (connection_lookup connections v))) = Some y"
    by (auto simp add: pred_graph_def)
  hence "snd (the (connection_lookup connections y)) +  edge_costs y v
      \<le> snd (the (connection_lookup connections v))"
    using 2(2)[simplified invar_pred_mono_def Let_def] by auto
  have new_vwalk: " vwalk_bet (pred_graph connections) u (xs @ [x, y]) y"
    using 2(3) vwalk_bet_prefix_is_vwalk_bet[of "xs@[x,y]" _ u "[z]" v, simplified] uv(1) by blast 
  have "snd (the (connection_lookup connections u)) + weight (xs @ [x, y, z])
       = snd (the (connection_lookup connections u)) + weight (xs @ [x, y]) + edge_costs y z"
    using weight_append_last[of "xs@[x]" y z, simplified] 
    by(auto simp add: algebra_simps)
  also have "... \<le> snd (the (connection_lookup connections y))  + edge_costs y z"
    using 2(1)[OF 2(2) new_vwalk]
    by (simp add: add_right_mono)
  also have "... \<le> snd (the (connection_lookup connections z))"
    using uv(1) vy 2(2)[simplified invar_pred_mono_def Let_def] by auto
  finally show ?case 
    using uv(1) by simp
qed

lemma unused_edge_vwalk: "Vwalk.vwalk E p  \<Longrightarrow>e \<notin> set (edges_of_vwalk p) \<Longrightarrow> length p \<ge> 2 \<Longrightarrow> Vwalk.vwalk(E-{e}) p" 
  apply(induction rule: Vwalk.vwalk.induct[of E p], simp, simp) 
  subgoal for v v' vs
    by(cases vs) auto
  done

lemma unused_edge_vwalk_bet: "Vwalk.vwalk_bet E u p v  \<Longrightarrow>e \<notin> set (edges_of_vwalk p) 
\<Longrightarrow> length p \<ge> 2 \<Longrightarrow> Vwalk.vwalk_bet(E-{e}) u p v"
  by (metis unused_edge_vwalk vwalk_bet_def)

context 
  assumes nexistence_of_negative_cycles:"\<nexists> c. weight c < 0 \<and> hd c = last c"
begin

lemma pred_acyc_init:"invar_pred_acyc (bellman_ford_init s)"
  by(auto simp add: bellman_ford_init_is(1) invar_pred_acyc_def dom_def pred_graph_def not_vwalk_bet_empty)

lemma relax_invar_pred_acyc_pres:
  assumes "invar_pred_acyc connections" "connection_invar connections"
          "v \<in> dom (connection_lookup connections)"
          "u \<in> dom (connection_lookup connections)"
          "invar_pred_mono connections"
          "invar_pred_in_dom s connections"
  shows "invar_pred_acyc (relax connections u v)"
  unfolding invar_pred_acyc_def Let_def
proof(rule, goal_cases)
  case 1
  then obtain a p where a_p_prop:"vwalk_bet (pred_graph (relax connections u v)) a p a" "2 \<le> length p" 
    by auto 
  show False
  proof(cases "snd (the (connection_lookup connections u)) + edge_costs u v < snd (the (connection_lookup connections v))")
    case False
    hence "pred_graph (relax connections u v) = pred_graph connections"
      by(simp add: relax_def Let_def)
    hence "vwalk_bet (pred_graph connections) a p a" "2 \<le> length p" 
      using a_p_prop by auto
    then show ?thesis 
      using assms(1) by(auto simp add: invar_pred_acyc_def)
  next
    case True
    have u_no_v:"u \<noteq> v"
    proof(rule ccontr, goal_cases)
      case 1
      hence "edge_costs u u < 0" 
        using True  ereal_le_add_self linorder_not_less by auto
      hence "weight [u, u] < 0" by simp
      thus False 
        using nexistence_of_negative_cycles by fastforce
    qed
    have pred_graph_is:"(pred_graph (relax connections u v)) = 
           (pred_graph connections) - {(the (fst (the (connection_lookup connections v))), v)}
            \<union> {(u, v)}" apply rule defer
      unfolding relax_def Let_def pred_graph_def 
      using True  assms(2) connection_axioms(2) by (force, auto)
    hence walk_in_new:"vwalk_bet (pred_graph connections \<union> {(u, v)}) a p a"
      by(auto intro: vwalk_bet_subset[OF a_p_prop(1)])
    hence in_new_pred:"set (edges_of_vwalk p) \<subseteq> pred_graph connections \<union> {(u, v)}"
      by (simp add: vwalk_bet_edges_in_edges)
    have no_walk_in_old:"\<not> vwalk_bet (pred_graph connections) a p a"
      using a_p_prop(2) assms(1) invar_pred_acyc_def by force
    have u_v_in_p:"(u, v) \<in> set (edges_of_vwalk p)" 
    proof(rule ccontr, goal_cases)
      case 1
      hence "set (edges_of_vwalk p) \<subseteq>  pred_graph connections" 
        using in_new_pred  "1" by blast
      hence "vwalk_bet (pred_graph connections) a p a" 
        using a_p_prop(2)  vwalk_bet_not_vwalk_bet_elim_2[OF walk_in_new] by auto
      then show ?case 
        using no_walk_in_old by simp
    qed
    then obtain p1 p2 where p1p2_prop:"p = p1@[u, v]@ p2" 
      using edges_in_vwalk_split by fastforce
    moreover have "p1 = c#pp1 \<Longrightarrow> p2= b#pp2 \<Longrightarrow> vwalk_bet (pred_graph (relax connections u v)) v 
                      ([v]@((butlast p2)@p1)@[u]) u"
      for c b pp1 pp2
    proof(subst vwalk_bet_def, rule, goal_cases)
      case 1
      have " Vwalk.vwalk (pred_graph (relax connections u v)) (u # ([v] @ butlast p2) @ a # pp1 @ [u])"
        using 1 a_p_prop(1) p1p2_prop vwalk_bet_props 
        by (intro vwalk_rotate[of _ a pp1 u "[v] @ butlast p2"]) fastforce
      hence " Vwalk.vwalk (pred_graph (relax connections u v)) (u # [v] @ butlast p2 @p1 @ [u])"
        using "1"(1) a_p_prop(1) hd_of_vwalk_bet' p1p2_prop by fastforce
      thus ?case 
        by force
    qed simp
moreover have "p1 = [] \<Longrightarrow> p2= b#pp2 \<Longrightarrow> vwalk_bet (pred_graph (relax connections u v)) v ([v]@(butlast p2)@[u]) u"
  for b pp2
    proof(subst vwalk_bet_def, rule, goal_cases)
      case 1
      have "butlast p2 @ [u] = p2"
        using "1"(1) "1"(2) a_p_prop(1) p1p2_prop vwalk_bet_props by fastforce
      hence" Vwalk.vwalk (pred_graph (relax connections u v)) (v # butlast p2 @ u # [] @ [v])"
        using a_p_prop(1)[simplified 1 p1p2_prop, simplified]  1(2)  vwalk_bet_nonempty_vwalk(3) 
              vwalk_bet_nonempty_vwalk(4) 
        by (intro vwalk_rotate[of _ u Nil v "butlast p2"])fastforce
      thus ?case 
        using 1 
        by (metis append.assoc append_vwalk_pref single_in_append)
    qed simp
    moreover
  have "p1 =  b#pp1\<Longrightarrow> p2= [] \<Longrightarrow> vwalk_bet (pred_graph (relax connections u v)) v  ([v]@tl p1@[u]) u"
  for b pp1
    proof(subst vwalk_bet_def, rule, goal_cases)
      case 1
      have b_is:"b = v" 
        using "1"(1) "1"(2) a_p_prop(1) p1p2_prop vwalk_bet_props by fastforce
      have" Vwalk.vwalk (pred_graph (relax connections u v)) (u # [] @ b # pp1 @ [u])"
        using a_p_prop(1)[simplified 1 p1p2_prop, simplified] b_is
        by (intro vwalk_rotate[of _ b pp1 u Nil]) auto
      thus ?case 
        using 1 b_is 
        by simp
    qed simp
    moreover have "p1 =[] \<Longrightarrow> p2=[] \<Longrightarrow> vwalk_bet (pred_graph (relax connections u v)) v ([v]@[u]) u"
      using  vwalk_bet_props[OF a_p_prop(1)[simplified  p1p2_prop]] 
      by auto
    ultimately obtain q where  "vwalk_bet (pred_graph (relax connections u v)) v ([v]@q@[u]) u" 
      using append_Nil[of "[u]"] 
      by(cases p1)( cases p2, metis, simp, cases p2, fast+)
    then obtain r where  r_prop:"vwalk_bet (pred_graph (relax connections u v)) v r u" "distinct r"
      by (meson distinct_vwalk_bet_def vwalk_bet_to_distinct_is_distinct_vwalk_bet)
    hence lengthr: "length r \<ge> 2"
      using u_no_v   last_of_vwalk_bet' linorder_not_less vwalk_bet_props by fastforce
    have r_walk_in_new:"vwalk_bet (pred_graph connections \<union> {(u, v)}) v r u"
      using pred_graph_is by(auto intro: vwalk_bet_subset[OF r_prop(1)])
    moreover have "(u, v) \<notin> set (edges_of_vwalk r)" 
    proof(rule, goal_cases)
      case 1
      moreover have hdr:"hd r = v" 
        using r_prop(1) by fastforce
      ultimately have  "(u, v) \<in> set (edges_of_vwalk (tl r))"
        using list.sel(3) lengthr u_no_v
        by(cases r rule: vwalk_arcs.cases) auto
      hence "v \<in> set (tl r)"
        by (meson v_in_edge_in_vwalk(2))
      hence "\<not> distinct r"
        using hdr lengthr 
        by(cases r rule: vwalk_arcs.cases) auto
      thus False
        using r_prop by simp
    qed
    ultimately have r_walk_in_old_without_uv:"vwalk_bet (pred_graph connections - {(u, v)}) v r u"
      using  unused_edge_vwalk_bet[OF _ _ lengthr] by force
    hence r_walk_in_old:"vwalk_bet (pred_graph connections) v r u"
      by (meson Diff_subset vwalk_bet_subset)
    have "snd (the (connection_lookup connections v)) + weight r
          \<le> snd (the (connection_lookup connections u))" 
      using r_walk_in_old weight_pred_path[OF lengthr assms(5)] by simp
    hence "snd (the (connection_lookup connections u))
            > snd (the (connection_lookup connections u)) + edge_costs u v + weight r"
      using True 
      by (smt (verit, del_insts) MInfty_eq_minfinity add.commute weight_not_MInfty
          ereal_add_le_add_iff2 ereal_plus_eq_PInfty nless_le order.strict_trans2)
    hence weight_sum:"edge_costs u v + weight r < 0"
      by (metis ab_semigroup_add_class.add_ac(1) ereal_le_add_self leD leI)
    have lastr:"last r = u" 
      using r_prop(1) by fastforce
    have "edge_costs u v + weight r = weight (r@[v])"
      apply(subst (2) sym[OF  append_butlast_last_id])
      using lengthr apply force
      apply(subst lastr, simp)
      apply(subst weight_append_last[of "butlast r" u v])
      apply(subst (2) sym[OF lastr])
      apply(subst  append_butlast_last_id)
      using lengthr 
      by (force simp add: add.commute)+
    hence "weight (r@[v]) < 0" 
      using weight_sum by force
    thus False 
      using nexistence_of_negative_cycles r_prop(1) by fastforce
  qed
qed
  
lemma foldr_invar_pred_acyc_pres: 
  assumes "invar_pred_acyc  connections" "connection_invar connections"
          "set (map snd ds) \<subseteq> dom (connection_lookup connections)"
          "set (map fst ds) \<subseteq> dom (connection_lookup connections)"
          "invar_pred_mono  connections"
          "invar_pred_in_dom s connections"
  shows "invar_pred_acyc (foldr (\<lambda>(x, y) done. relax done x y) ds connections)"
  using assms
proof(induction ds)
  case (Cons a ds)
  show ?case 
    apply(subst subst foldr.simps(2), subst o_apply)
    apply(subst cases_distr[of id "\<lambda>x y done. relax done  x y" _, simplified]) 
    apply(rule relax_invar_pred_acyc_pres)
    apply(rule Cons(1))
    using connection_inver_fold_pres  fold_in_dom_no_change_dom  Cons(2-) assms 
          relax_invar_pred_acyc_pres invar_lemmas
    by auto
qed (auto simp add: assms(1))

lemma one_step_invar_pred_acyc_pres:
  assumes "invar_pred_acyc connections" "connection_invar connections"
          "set vs \<subseteq> dom (connection_lookup connections)"
          "invar_pred_mono connections"
          "invar_pred_in_dom s connections"
  shows "invar_pred_acyc (bellman_ford_one_step connections)"
  unfolding bellman_ford_one_step_def
  using assms vs_and_es 
  by (intro foldr_invar_pred_acyc_pres) auto

lemma bellman_ford_invar_pred_acyc_pres:
"invar_pred_acyc (bellman_ford l (bellman_ford_init s))"
proof(induction l)
  case (Suc l)
  show ?case 
    apply(subst  bellman_ford_upd_one)
    apply(rule one_step_invar_pred_acyc_pres[of _ s ])
    using Suc bellman_ford_connection_invar bellman_ford_init_dom_is 
          same_domain_bellman_ford vs_and_es
          one_step_invar_pred_in_dom_pres[of s] one_step_invar_pred_mono_pres[of _ s]
          bellman_ford_invar_pred_mono_pres[of _ s]
          bellman_ford_pred_in_dom_pres[of s] 
    by auto
qed (simp add: pred_acyc_init)

lemma no_cycle_is_cheaper:"weight (xs@[v]@ys@[v]@zs) \<ge> weight (xs@[v]@zs)" 
proof(cases ys)
  case Nil
  hence "weight (xs@[v]@ys@[v]@zs) = weight (xs@[v]) + edge_costs v v + weight ([v]@zs)" 
    using weight_list_split[of xs v v zs] by simp
  also have "weight (xs@[v]) + weight ([v]@zs) \<le> ..." 
  proof(rule ccontr, goal_cases)
    case 1
    hence "edge_costs v v < 0"
      by (meson add_right_mono ereal_le_add_self leI)
    hence "weight [v, v] < 0" by simp
    then show ?case 
      using nexistence_of_negative_cycles by fastforce
  qed
  moreover have "weight (xs@[v]) + weight ([v]@zs) = weight (xs@[v]@zs)" 
    apply(cases zs, simp)
    subgoal for a list
      using  weight_list_split[of xs v a list, simplified]
      by(auto simp add: algebra_simps)
    done
  ultimately show ?thesis by simp
next
  case (Cons a list)
  hence "weight (xs @ [v] @ ys @ [v] @ zs) =
        weight (xs @ [v]) +  weight ([v]@ys @ [v] @ zs)" 
    using weight_list_split[of xs v a "list@[v]@zs"] 
    by (simp add: add.commute add.left_commute)
  moreover have "weight (xs @ [v]) +  weight ([v]@ys @ [v] @ zs)
                 =  weight (xs @ [v]) +   weight ([v]@ys @ [v]) +  weight ([v] @ zs)"
    using weight_list_split'[of "[v]@ys" v zs]
    by (simp add: ab_semigroup_add_class.add_ac(1))
  moreover have "weight (xs @ [v]) +   weight ([v]@ys @ [v]) +  weight ([v] @ zs) \<ge>
                weight (xs @ [v]) + weight ([v] @ zs)"
  proof(rule ccontr, goal_cases)
    case 1
    hence "  weight ([v]@ys @ [v]) < 0"
      by (meson add_right_mono ereal_le_add_self leI)
    then show ?case 
      using nexistence_of_negative_cycles by auto
  qed
  moreover have "weight (xs @ [v]) + weight ([v] @ zs) =
                weight (xs @ [v] @ zs)"
    using weight_list_split' by presburger
  ultimately show ?thesis by simp
qed

lemma distinct_path_is_cheaper:
  "length xs \<ge> 2 \<Longrightarrow> hd xs \<noteq> last xs \<Longrightarrow>
\<exists> ys. weight xs \<ge> weight ys \<and> distinct ys \<and> set ys \<subseteq> set xs \<and> hd xs = hd ys \<and> last xs = last ys \<and> length ys \<ge> 2"
proof(induction "length xs" arbitrary:  xs rule: less_induct)
  case less
  show ?case 
  proof(cases "distinct xs")
    case True
    then show ?thesis 
      using less by auto
  next
    case False
    then obtain u p1 p2 p3 where path_is:"xs = p1@[u]@p2@[u]@p3"
      using not_distinct_decomp by blast
    have first_imprv:"weight (p1@[u]@p2@[u]@p3) \<ge> weight (p1@[u]@p3)"
      using no_cycle_is_cheaper by auto
    have not_both_empt:"p1 =[] \<Longrightarrow> p3 =[] \<Longrightarrow> False"
      using less.prems(2) path_is by force
    have uneq_ends:"hd (p1 @ [u] @ p3) \<noteq> last (p1 @ [u] @ p3)"
      using less.prems(2) path_is by (cases p1) auto
    have "\<exists>ys. weight ys \<le> weight (p1 @ [u] @ p3) \<and>
     distinct ys \<and> set ys \<subseteq> set (p1 @ [u] @ p3) \<and> hd (p1 @ [u] @ p3) = hd ys \<and> last (p1 @ [u] @ p3) = last ys
            \<and> length ys \<ge> 2"
      using not_both_empt  not_less_eq_eq path_is uneq_ends 
      by (intro less(1)[of "p1@[u]@p3"]) auto
    then obtain ys where ysprop:"weight ys \<le> weight (p1 @ [u] @ p3)" "distinct ys" "set ys \<subseteq> set (p1 @ [u] @ p3)"
     "hd (p1 @ [u] @ p3) = hd ys" "last (p1 @ [u] @ p3) = last ys" "length ys \<ge> 2"
      by auto
    hence  "weight ys \<le> weight xs" "distinct ys" "set ys \<subseteq> set xs"
     "hd xs = hd ys" "last xs = last ys" "length ys \<ge>2"
      using first_imprv dual_order.trans  ysprop path_is  hd_append[of "p1@[u]" "p2@[u]@p3", simplified] 
            hd_append[of "p1@[u]" p3, simplified] 
      by auto
    then show ?thesis by auto
  qed
qed

lemma vs_path_find_distinct_cheaper:
  assumes "vs_path s t P" "s \<noteq> t"
  obtains Q where "vs_path s t Q" "weight Q \<le> weight P" "distinct Q"
  using distinct_path_is_cheaper[of P] assms
  by(force simp add:vs_path_def)

lemma bellamn_ford_equality:
  assumes "s \<in> set vs" "s \<noteq> v" "v \<in> set vs"
  shows "snd (the (connection_lookup (bellman_ford (length vs - 1) (bellman_ford_init s)) v)) 
         = OPT (length vs - 1) s v"
proof(cases "OPT (length vs - 1) s v")
  case PInf
  hence all_below_pinfty:"\<And> xs. length ([s]@xs@[v]) \<le> length vs \<Longrightarrow> set xs \<subseteq> set vs \<Longrightarrow>  weight ([s]@xs@[v]) = PInfty"
  proof(goal_cases)
    case (1 xs)
    have "OPT (length vs - 1) s v \<le> weight ([s]@xs@[v]) "
      using finite_weight_set  1 
      by (auto intro!:  linorder_class.Min.coboundedI simp add:  OPT_def)
    then show ?case
      using PInf by force
  qed
  show ?thesis
  proof(rule ccontr, goal_cases)
    case 1
    hence less_Pinfty:"snd (the (connection_lookup (bellman_ford (length vs - 1) (bellman_ford_init s)) v)) < PInfty"
      using PInf by auto
    moreover have "v\<in>dom (connection_lookup (bellman_ford (length vs - 1) (bellman_ford_init s)))"
      by (simp add: assms(3) bellman_ford_init_dom_is same_domain_bellman_ford)
    moreover have " fst (the (connection_lookup (bellman_ford (length vs - 1) (bellman_ford_init s)) v)) \<noteq> None"
      using assms(2) bellman_ford_pred_non_infty_pres calculation(1) calculation(2) invar_pred_non_infty_def by auto
    ultimately obtain p where p_prop:"weight (p @ [v]) =
            snd (the (connection_lookup (bellman_ford (length vs - 1) (bellman_ford_init s)) v))"
            "last p = the (fst (the (connection_lookup (bellman_ford (length vs - 1) (bellman_ford_init s)) v)))"
            "hd p = s" "1 \<le> length p" "set (p@[v]) \<subseteq> insert s (set vs)"
        using bellman_ford_invar_pred_path_pres[of s "length vs -1"] 
    by(auto simp add:invar_pred_path_def)
  hence  12:"weight (p@[v]) =
       snd (the (connection_lookup (bellman_ford (length vs - 1) (bellman_ford_init s)) v))"
                 "hd (p@[v])= s" "last (p@[v]) = v" "length (p@[v]) \<ge> 2"
    using  hd_append2 not_less_eq_eq by auto
  then obtain P where  P_prop:"weight P \<le>
       snd (the (connection_lookup (bellman_ford (length vs - 1) (bellman_ford_init s)) v))"
                 "hd P = s" "last P = v" "distinct P" "set P \<subseteq> set (p@[v])"
    using assms(2) distinct_path_is_cheaper[of "p@[v]"] by auto
  moreover hence P_in_vs:"set P \<subseteq> set vs"
    using \<open>set (p @ [v]) \<subseteq> insert s (set vs)\<close> assms(1) by blast
  hence P_length:"length P \<le> length vs" 
    using sym[OF distinct_card[OF distinct_vs]]  sym[OF distinct_card[OF P_prop(4)]]
    by (auto simp add: card_mono)
  obtain pp where pp_is:"P = [s]@pp@[v]"  
    using  assms(2) calculation(2) calculation(3) hd_Nil_eq_last 
    by(cases P) 
     (auto, smt (verit, ccfv_SIG) append_butlast_last_id)
  have "length ([s]@pp@[v]) \<le> length vs"
    using P_length pp_is by blast
  moreover have "weight ([s]@pp@[v]) < PInfty" 
    using less_Pinfty calculation(1) pp_is by auto
  ultimately show False 
    using all_below_pinfty P_in_vs pp_is by auto
qed
next
  case MInf
  then show ?thesis 
    using  OPT_not_MInfty[of "length vs -1" s v] by simp
next
  case (real r)
  hence all_above_opt:"\<And> xs. length ([s]@xs@[v]) \<le> length vs \<Longrightarrow> set xs \<subseteq> set vs \<Longrightarrow>  weight ([s]@xs@[v]) \<ge>
                          OPT (length vs - 1) s v"
  proof(goal_cases)
    case (1 xs)
    have "OPT (length vs - 1) s v \<le> weight ([s]@xs@[v]) "
      using finite_weight_set  1 
      by (auto intro!:  linorder_class.Min.coboundedI simp add:  OPT_def)
    then show ?case by fast
  qed
    hence less_Pinfty:"snd (the (connection_lookup (bellman_ford (length vs - 1) (bellman_ford_init s)) v)) < PInfty"
      using  bellman_ford_shortest[OF assms(1), of "length vs - 1" v] real by fastforce
    moreover have "v\<in>dom (connection_lookup (bellman_ford (length vs - 1) (bellman_ford_init s)))"
      by (simp add: assms(3) bellman_ford_init_dom_is same_domain_bellman_ford)
    moreover have " fst (the (connection_lookup (bellman_ford (length vs - 1) (bellman_ford_init s)) v)) \<noteq> None"
      using assms(2) bellman_ford_pred_non_infty_pres calculation(1) calculation(2) invar_pred_non_infty_def by auto
    ultimately obtain p where p_prop:"weight (p @ [v]) =
            snd (the (connection_lookup (bellman_ford (length vs - 1) (bellman_ford_init s)) v))"
            "last p = the (fst (the (connection_lookup (bellman_ford (length vs - 1) (bellman_ford_init s)) v)))"
            "hd p = s" "1 \<le> length p" "set (p@[v]) \<subseteq> insert s (set vs)"
        using bellman_ford_invar_pred_path_pres[of s "length vs -1"] 
    by(auto simp add:invar_pred_path_def)
  hence  12:"weight (p@[v]) =
       snd (the (connection_lookup (bellman_ford (length vs - 1) (bellman_ford_init s)) v))"
                 "hd (p@[v])= s" "last (p@[v]) = v" "length (p@[v]) \<ge> 2"
    using  hd_append2 not_less_eq_eq by auto
  then obtain P where  P_prop:"weight P \<le>
       snd (the (connection_lookup (bellman_ford (length vs - 1) (bellman_ford_init s)) v))"
                 "hd P = s" "last P = v" "distinct P" "set P \<subseteq> set (p@[v])"
    using assms(2) distinct_path_is_cheaper[of "p@[v]"] by auto
  moreover hence P_in_vs:"set P \<subseteq> set vs"
    using \<open>set (p @ [v]) \<subseteq> insert s (set vs)\<close> assms(1) by blast
  hence P_length:"length P \<le> length vs" 
    using sym[OF distinct_card[OF distinct_vs]]  sym[OF distinct_card[OF P_prop(4)]]
    by (auto simp add: card_mono)
  obtain pp where pp_is:"P = [s]@pp@[v]"  
    using  assms(2) calculation(2) calculation(3) hd_Nil_eq_last 
    by(cases P) 
     (auto, smt (verit, ccfv_SIG) append_butlast_last_id)
  have "length ([s]@pp@[v]) \<le> length vs"
    using P_length pp_is by blast
  moreover have "weight ([s]@pp@[v]) \<ge> OPT (length vs - 1) s v" 
    using calculation(6) P_in_vs pp_is by (intro all_above_opt) auto
  ultimately show ?thesis
    using pp_is  bellman_ford_shortest[OF assms(1), of "length vs -1" v] by simp
qed

lemma better_opt_path_is_opt_path: "opt_vs_path s t P \<Longrightarrow> vs_path s t Q \<Longrightarrow> weight Q \<le> weight P 
                                     \<Longrightarrow> opt_vs_path s t Q"
  using opt_vs_path_def by force

lemma opt_path_same_weight: "opt_vs_path s t P  \<Longrightarrow> opt_vs_path s t Q \<Longrightarrow> weight P = weight Q"
  using opt_vs_path_def by force

lemma optpath_distinct:                            
  assumes "opt_vs_path s t P" "s \<noteq> t"
  obtains Q where "opt_vs_path s t Q" "distinct Q"
proof-
  have P_prop: "2 \<le> length P" "hd P = s" "last P = t" "set P \<subseteq> set vs" "s \<noteq> t"
   "\<And> ys. 2 \<le> length ys \<Longrightarrow> hd ys = s \<Longrightarrow> last ys = t \<Longrightarrow> set ys \<subseteq> set vs \<Longrightarrow> weight P \<le> weight ys"
    using assms by(auto simp add: opt_vs_path_def vs_path_def)
  then obtain ys where ys_prop:"weight ys \<le> weight P" "distinct ys" "set ys \<subseteq> set P" "hd P = hd ys" "last P = last ys" 
                       "length ys \<ge> 2"
    using distinct_path_is_cheaper[of P] by auto
  hence "vs_path s t ys"
    using P_prop(2) P_prop(3) P_prop(4) by (auto simp add: vs_path_def)
  moreover hence "opt_vs_path s t ys" 
    using assms(1) better_opt_path_is_opt_path ys_prop(1) by blast
  thus ?thesis 
    by (simp add: that ys_prop(2))
qed


lemma optpath_bellman_ford:                            
  assumes "opt_vs_path s t P" "s \<noteq> t"
  shows "weight P = OPT (length vs - 1) s t"
proof-
  obtain  Q where Q_prop:"opt_vs_path s t Q" "distinct Q"
    using assms(1) assms(2) optpath_distinct by blast
  hence lengthQ:"length Q \<le> length vs"
    using sym[OF distinct_card[of Q]] sym[OF distinct_card[of vs]] distinct_vs 
    by (auto simp add: card_mono opt_vs_path_def vs_path_def)
  then obtain xs where xs_prop:"Q =[s]@xs@[t]"
    using Q_prop 
    by(cases Q rule: list_cases_both_sides) (auto simp add: opt_vs_path_def vs_path_def )
  moreover have "length xs + 1 \<le> length vs - 1" "set xs \<subseteq> set vs" 
    using lengthQ xs_prop  Q_prop(1) opt_vs_path_def vs_path_def xs_prop by auto
  ultimately have OPT_less_Q:"OPT (length vs - 1) s t \<le> weight Q"
    using finite_weight_set
    by (auto intro: linorder_class.Min.coboundedI simp add: OPT_def)
  have "length ys + 1 \<le> length vs - 1  \<Longrightarrow> set ys \<subseteq> set vs \<Longrightarrow> weight P \<le> weight (s # ys @ [t])" for ys
  proof(goal_cases)
    case 1
    have "2 \<le> length (s # ys @ [t])" by simp
    moreover have "hd (s # ys @ [t]) = s" by simp
    moreover have "last (s # ys @ [t]) = t" by simp
    moreover have "set (s # ys @ [t]) \<subseteq> set vs" 
      using "1"(2) Q_prop(1) opt_vs_path_def vs_path_def xs_prop by auto
    ultimately have "vs_path s t (s # ys @ [t])" 
       by (auto simp add: opt_vs_path_def vs_path_def)
     then show ?case 
       using assms(1) by(auto simp add: opt_vs_path_def)
  qed
  hence "weight P \<le> OPT (length vs - 1) s t"
    using finite_weight_set  assms 
    by (auto intro: linorder_class.Min.boundedI simp add:  OPT_def)
  thus ?thesis
    using OPT_less_Q opt_path_same_weight[OF Q_prop(1) assms(1)] by simp
qed

lemma vs_path_append: "vs_path s u P \<Longrightarrow> vs_path u t Q \<Longrightarrow> vs_path s t (P@tl Q)"
  unfolding vs_path_def 
  by (smt (verit) Nat.le_diff_conv2 Suc_1 Un_subset_iff dual_order.trans hd_append2 last_appendR 
last_tl leD le_add1 length_append 
length_tl less_numeral_extra(1) list.collapse list.size(3) plus_1_eq_Suc set_append set_subset_Cons)


lemma OPT_path_exists:
  assumes "s \<noteq> t" "s \<in> set vs" "t\<in> set vs" "l > 0"
  obtains P where "vs_path s t P" "weight P = OPT l s t"
proof(goal_cases)
  case 1
  note rl = this
  have "OPT l s t \<in> ({weight (s # xs @ [t]) |xs. length xs + 1 \<le> l \<and> set xs \<subseteq> set vs} \<union> {if t = s then 0 else \<infinity>})"
    unfolding OPT_def 
    using finite_weight_set 
    by(intro linorder_class.Min_in) auto
  then obtain xs where xs_prop: "(weight (s # xs @ [t]) = OPT l s t \<and> length xs + 1 \<le> l \<and> set xs \<subseteq> set vs)
                        \<or>  OPT l s t  = PInfty" 
    using assms by force
  show ?case
  proof(rule disjE[OF xs_prop], goal_cases)
    case 1
    moreover have "vs_path s t (s # xs @ [t])"
      by (simp add: "1" assms(2) assms(3) vs_path_def)
    ultimately show ?case 
      by(auto intro: rl)
  next
    case 2
    have "length [] + 1 \<le> l" "set [] \<subseteq> set vs" "weight ([s,t]) = weight ([s]@[]@[t])" 
      using assms by auto
    hence "OPT l s t \<le> weight [s,t]"
      using finite_weight_set
      by(auto intro!: exI[of _ Nil] linorder_class.Min.coboundedI simp add: OPT_def )
    hence "weight [s,t] = PInfty"
      by (simp add: "2")
    moreover have "vs_path s t [s, t]" 
      by (simp add: assms(2) assms(3) vs_path_def)
    ultimately show ?case    
      by (auto intro: rl[of "[s,t]"] simp add: "2")
  qed
qed

lemma path_weight_in: assumes "vs_path s t Q'" "length Q' \<le> l + 1"
  shows "weight Q' \<in> {weight (s # xs @ [t]) |xs. length xs + 1 \<le> l \<and> set xs \<subseteq> set vs}"
proof-
  obtain xs where "Q' = ([s]@xs@[t])"
    using assms by(cases Q' rule: list_cases_both_sides) (auto simp add: vs_path_def)
  moreover hence "length xs + 1 \<le> l" "set xs \<subseteq> set vs" 
    using assms by(auto simp add: vs_path_def)
  ultimately show ?thesis by auto
qed
   
lemma optpath_exists:
  assumes "s \<noteq> t" "s \<in> set vs" "t\<in> set vs"
  obtains P where "opt_vs_path s t P"
proof(rule ccontr, goal_cases)
  case 1
  have length_vs: "length vs -1 > 0"
    using assms by(cases vs rule: remdups_adj.cases) auto
  obtain P where P_prop:"vs_path s t P" " weight P = OPT (length vs - 1) s t" 
    using assms length_vs by (auto intro: OPT_path_exists[of s t "length vs -1"])
  obtain Q where Q_prop:"vs_path s t Q" "weight Q < weight P"
    by (meson "1"(1) "1"(2) P_prop leI opt_vs_path_def)
  obtain Q' where Q'_prop: "vs_path s t Q'" "weight Q' \<le> weight Q" "distinct Q'"
    using assms  Q_prop(1) by (auto intro: vs_path_find_distinct_cheaper)
  have lengthQ':"length Q' \<le> length vs"
    using sym[OF distinct_card[OF Q'_prop(3)]] sym[OF distinct_card[OF distinct_vs]] Q'_prop(1) card_mono
    by(auto simp add: vs_path_def)
  have "weight Q' \<ge> OPT (length vs - 1) s t"
    using finite_weight_set  Q'_prop(1) lengthQ' path_weight_in  
    by (auto intro: linorder_class.Min.coboundedI simp add: OPT_def)
  thus False 
    using P_prop(2) Q'_prop(2) Q_prop(2) by simp
qed

theorem bellman_ford_computes_length_of_optpath:
  assumes "s \<noteq> t" "s \<in> set vs" "t\<in> set vs"
  obtains P where "opt_vs_path s t P" 
         "weight P = snd (the (connection_lookup (local.bellman_ford (length vs - 1) (bellman_ford_init s)) t))"
  using bellamn_ford_equality[OF assms(2,1,3)] optpath_bellman_ford[OF _ assms(1)] 
        optpath_exists[OF assms] 
  by auto


lemma s_reachbale_in_some_steps:
  assumes "v \<in> dom (connection_lookup connections)"
          "fst (the (connection_lookup connections v)) \<noteq> None"
          "n = card {u | u. \<exists> p. vwalk_bet (pred_graph connections) u p v }"
          "finite (dom (connection_lookup connections))"
          "invar_pred_acyc connections"
          "invar_pred_in_dom s connections"
          "invar_pred_has_pred s connections"
        shows" \<exists> i. compow i (\<lambda> w. the (fst (the (connection_lookup connections w)))) v = s"
  using assms(1-3)
proof(induction n arbitrary: v rule: less_induct)
  case (less n)
  define pred where "pred = the (fst (the (connection_lookup connections v)))"
  note IH = less[simplified sym[OF pred_def]]
  show ?case
  proof(cases "v = s")
    case False
    note false = this
    have pred_in_dom: "pred \<in> dom (connection_lookup connections)" 
      using  less.prems assms 
      by(auto simp add: local.pred_def invar_pred_in_dom_def)
    show ?thesis
    proof(cases "pred = s")
      case False
      have pred_of_pred_exists: "fst (the (connection_lookup connections pred)) \<noteq> None"
        using False assms(7)  less.prems(1) less.prems(2) 
        by(auto simp add: invar_pred_in_dom_def invar_pred_has_pred_def pred_def Let_def)
      have reachable_subs:"{u |u. \<exists>p. vwalk_bet (pred_graph connections) u p pred} \<subseteq>
            {u |u. \<exists>p. vwalk_bet (pred_graph connections) u p v}"
      proof(rule, goal_cases)
        case (1 x)
        then obtain p where "vwalk_bet (pred_graph connections) x p pred" by auto
        moreover have "vwalk_bet (pred_graph connections) pred ([pred, v]) v"
          using less.prems(1) less.prems(2) by(auto simp add: pred_def pred_graph_def)
        ultimately have "vwalk_bet (pred_graph connections) x (butlast p @[pred]@[v]) v"
          using vwalk_bet_transitive_2[ of _ x p  pred "[pred, v]" v] by simp       
        then show ?case by auto
      qed
      have v_in_pred_Vs:"v \<in> dVs (pred_graph connections)"
        using less.prems(1) less.prems(2)  by (auto simp add: pred_graph_def)
      have v_in_predgraph:"v \<in>  {u |u. \<exists>p. vwalk_bet (pred_graph connections) u p v}" 
          using vwalk_bet_reflexive[of v] v_in_pred_Vs by blast
      moreover have reachable_Smaller:"{u |u. \<exists>p. vwalk_bet (pred_graph connections) u p pred} \<subseteq>
            {u |u. \<exists>p. vwalk_bet (pred_graph connections) u p v} - {v}"
      proof(rule ccontr, goal_cases)
        case 1
        hence "v \<in> {u |u. \<exists>p. vwalk_bet (pred_graph connections) u p pred}" 
          using reachable_subs  v_in_predgraph by auto
        then obtain p where "vwalk_bet (pred_graph connections) v p pred" by auto
        moreover have "vwalk_bet (pred_graph connections) pred ([pred, v]) v"
          using less.prems(1) less.prems(2) by(auto simp add: pred_def pred_graph_def)
        ultimately have "vwalk_bet (pred_graph connections) v (butlast p @[pred]@[v]) v"
          using vwalk_bet_transitive_2[ of _ v p  pred "[pred, v]" v] by simp  
        then show ?case 
          using assms(5) invar_pred_acyc_def by force
      qed
      moreover have "finite {u |u. \<exists>p. vwalk_bet (pred_graph connections) u p v}"
      proof-
        have " {u |u. \<exists>p. vwalk_bet (pred_graph connections) u p v} \<subseteq> 
               dom (connection_lookup connections)"
        proof(rule, goal_cases)
          case (1 x)
          hence "x \<in> dVs (pred_graph connections)" by force
          moreover have "dVs (pred_graph connections) \<subseteq> dom (connection_lookup connections)"
          using assms(6,7)
          by(force simp add: pred_graph_def dom_def invar_pred_in_dom_def invar_pred_has_pred_def Let_def dVs_def)
        ultimately show ?case by auto
        qed
        thus ?thesis 
          by (simp add: assms(4) finite_subset)  
      qed
      ultimately have card_less:"card {u |u. \<exists>p. vwalk_bet (pred_graph connections) u p pred} <
                       card {u |u. \<exists>p. vwalk_bet (pred_graph connections) u p v}" 
        by(auto intro: psubset_card_mono)
    have " \<exists>i. ((\<lambda>w. the (fst (the (connection_lookup connections w)))) ^^ i) pred = s"
      apply(rule IH(1)[of _ pred , OF _ _ _ refl])
      using card_less less(4)  pred_in_dom  pred_of_pred_exists 
      by (auto intro: IH(1)[of _ pred , OF _ _ _ refl])
    then obtain i where "((\<lambda>w. the (fst (the (connection_lookup connections w)))) ^^ i) pred = s"
      by blast
    hence "((\<lambda>w. the (fst (the (connection_lookup connections w)))) ^^ Suc i) v = s"
      unfolding pred_def 
      by(subst funpow_Suc_right o_apply) auto
    then show ?thesis 
      by(auto intro: exI[of _"Suc i"])
  qed (auto intro: exI[of _ 1] simp add: pred_def)
 qed (auto intro: exI[of _ 0])
qed

lemma s_compow_reachble_term:"((\<lambda>w. the (fst (the (connection_lookup connections w)))) ^^ i) v = s
        \<Longrightarrow> search_rev_path_dom (s, connections,v)"
proof(induction i arbitrary: s connections v)
  case (Suc i)
  show ?case 
    using Suc(2)[simplified funpow_Suc_right o_apply]
    by (auto intro: search_rev_path.domintros Suc(1))
qed (auto intro: search_rev_path.domintros) 

lemma term_s_compow_reachable:
  assumes"search_rev_path_dom (s, connections,v)"
  shows "\<exists> i. ((\<lambda>w. the (fst (the (connection_lookup connections w)))) ^^ i) v = s"
proof(induction rule: search_rev_path.pinduct[OF assms])
  case (1 s connections v)
  note IH = this
  show ?case 
  proof(cases "s = v")
    case False
    obtain i where "((\<lambda>w. the (fst (the (connection_lookup connections w)))) ^^ i)
                     (the (fst (the (connection_lookup connections v)))) = s"
      using IH(2)[OF False refl] by auto
    hence "((\<lambda>w. the (fst (the (connection_lookup connections w)))) ^^ Suc i) v = s"
     by(subst funpow_Suc_right, subst o_apply)
    then show ?thesis by blast
  qed (auto intro: exI[of _ 0])
qed

lemma search_rev_path_is_in_pred_graph:
  assumes "search_rev_path_dom (s, connections, v)"
          "v \<in> dom (connection_lookup connections)"
          "s \<noteq> v"
          "invar_pred_in_dom s connections"
          "invar_pred_has_pred s connections"
          "fst (the (connection_lookup connections v)) \<noteq> None"
    shows "vwalk_bet (pred_graph connections) s (rev (search_rev_path s connections v)) v"
  using assms(2-)
proof(induction  rule: search_rev_path.pinduct[OF assms(1)])
  case (1 s connections v)
  note IH = this
  define pred where "pred = the (fst (the (connection_lookup connections v)))"
  have edge_in_pred_Graph: "(pred, v) \<in> pred_graph connections"
    using  IH(3,6,5,7) 
    by(auto simp add: pred_def invar_pred_in_dom_def invar_pred_has_pred_def Let_def pred_graph_def dom_def)
  show ?case 
  proof(cases "pred = s")
    case True
    have search_from_pred_is_s:"search_rev_path s connections pred = [s]"
      using True pred_def 
      by (subst search_rev_path.psimps, auto intro: search_rev_path.domintros)
    hence "search_rev_path s connections v = [v, s]"
      using IH(4)  search_from_pred_is_s 
      by(auto simp add: pred_def Let_def search_rev_path.psimps[OF IH(1)])
    then show ?thesis 
      using True edge_in_pred_Graph by auto
  next
    case False
    have "vwalk_bet (pred_graph connections) s (rev (search_rev_path s connections pred)) pred"
      using  False IH(3-)
      by(auto intro!: IH(2) simp add: invar_pred_has_pred_def pred_def Let_def invar_pred_in_dom_def)
    hence  "vwalk_bet (pred_graph connections) s (rev (search_rev_path s connections pred)@[v]) v"
      using edge_in_pred_Graph
      by (fastforce intro: vwalk_bet_transitive[where q="[pred, v]" , simplified])
    then show ?thesis 
      by (simp add: IH(4) pred_def search_rev_path.psimps[OF IH(1)])
  qed
qed

lemma pred_graph_subs_es:
  assumes "connections = bellman_ford (length vs - 1) (bellman_ford_init s)"
          "s \<in> set vs"
  shows "pred_graph connections \<subseteq> set es"
proof(rule, goal_cases)
  case (1 e)
  hence snd_e_in_dom:"snd e \<in> dom (connection_lookup connections)"
    using same_domain_bellman_ford bellman_ford_init_dom_is assms(2)
    by (auto simp add: pred_graph_def assms(1))
  hence "snd e \<in> set vs" 
    using same_domain_bellman_ford bellman_ford_init_dom_is assms(2)
    by (auto simp add: pred_graph_def assms(1))
  moreover hence fst_e_in_dom:"fst e \<in> dom (connection_lookup connections)" 
    using 1 bellman_ford_pred_in_dom_pres[of s "length vs - 1"]  
            bellman_ford_init_dom_is same_domain_bellman_ford 
    by (fastforce simp add: pred_graph_def  assms(1) invar_pred_non_infty_def invar_pred_in_dom_def)
  moreover hence "fst e \<in> set vs" 
    using   assms(2) 
            bellman_ford_init_dom_is[of s] same_domain_bellman_ford[of "length vs -1" s] assms(1)
    by auto
  moreover have fst_e_snd_e_Some:"fst (the (connection_lookup connections (snd e))) = Some (fst e)"
    using "1" by (auto simp add: pred_graph_def)
  moreover have fst_e_has_pred: "fst (the (connection_lookup connections (fst e))) \<noteq> None \<or>
                                 (fst e) = s"
    using bellman_ford_invar_pred_has_pred_pres[of s "length vs -1"] snd_e_in_dom fst_e_snd_e_Some
    by (auto  simp add: assms(1) invar_pred_has_pred_def Let_def)
  moreover obtain p where p_prop: "weight (p @ [snd e]) =
          snd (the (connection_lookup connections (snd e)))"
          "last p = (fst e)" "length p \<ge> 1"
    apply(rule ballE[OF bellman_ford_invar_pred_path_pres[of s "length vs - 1",
                   simplified invar_pred_path_def], of "fst e"])
    subgoal
      using fst_e_snd_e_Some fst_e_has_pred  bellman_ford_invar_pred_path_pres[of s "length vs -1"] 
            snd_e_in_dom 
      by(auto simp add:  assms(1) invar_pred_path_def) 
    using  fst_e_in_dom by(auto simp add: assms(1))
  moreover have "snd (the (connection_lookup connections (snd e))) < PInfty"
    using bellman_ford_pred_non_infty_pres[of s "length vs -1"] fst_e_snd_e_Some snd_e_in_dom
    by (auto simp add: assms(1) invar_pred_non_infty_def)
  moreover have "butlast p @ [fst e, snd e] = p @[snd e]" 
    using append_butlast_last_cancel[of p Nil]  p_prop(2) p_prop(3) by force
  ultimately have  "weight (butlast p @ [fst e])  + edge_costs (fst e) (snd e) < PInfty"
    using costs_last[of "butlast p" "fst e" "snd e"] 
    by presburger
  hence "edge_costs (fst e) (snd e) < PInfty"
    by simp
  then show ?case 
    using edge_costs_outside_es by force
qed

lemma s_reachable_in_some_steps:
  assumes "v \<in> set vs" 
          "fst (the (connection_lookup (local.bellman_ford l (bellman_ford_init s)) v)) \<noteq> None"
     shows" \<exists> i. compow i (\<lambda> w. the (fst (the (connection_lookup (bellman_ford l (bellman_ford_init s)) w)))) v = s"
  using  assms bellman_ford_init_dom_is same_domain_bellman_ford  bellman_ford_init_dom_is 
         bellman_ford_invar_pred_acyc_pres  bellman_ford_pred_in_dom_pres
         bellman_ford_invar_pred_has_pred_pres 
  by (auto intro!: s_reachbale_in_some_steps[OF _ _ refl])

theorem search_rev_path_dom_bellman_ford:
  assumes "v \<in> set vs" 
          "fst (the (connection_lookup (local.bellman_ford l (bellman_ford_init s)) v)) \<noteq> None"
    shows "search_rev_path_dom (s, (bellman_ford l (bellman_ford_init s)), v)"
  using assms(1) assms(2) s_compow_reachble_term s_reachable_in_some_steps by blast

lemma search_rev_path_is_pred_graph:
  assumes "connections = bellman_ford (length vs - 1) (bellman_ford_init s)"
          "v \<in> set vs" "v \<noteq> s" "s \<in> set vs"
          "fst (the (connection_lookup connections v)) \<noteq> None"
    shows "vwalk_bet (pred_graph connections) s (rev (search_rev_path s connections v)) v"
    using  search_rev_path_dom_bellman_ford bellman_ford_init_dom_is same_domain_bellman_ford
           assms bellman_ford_pred_in_dom_pres  bellman_ford_invar_pred_has_pred_pres 
    by (intro search_rev_path_is_in_pred_graph) auto

theorem search_rev_path_is_in_es:
  assumes "connections = bellman_ford (length vs - 1) (bellman_ford_init s)"
          "v \<in> set vs" "v \<noteq> s" "s \<in> set vs"
          "fst (the (connection_lookup connections v)) \<noteq> None"
    shows "vwalk_bet (set es) s (rev (search_rev_path s connections v)) v"
proof-
   have "(pred_graph connections) \<subseteq> set es"
    by (simp add: assms(1) assms(4) pred_graph_subs_es)
  thus ?thesis using search_rev_path_is_pred_graph[OF assms]
    by (meson vwalk_bet_subset)
qed

theorem search_rev_path_distinct:
  assumes "connections = bellman_ford (length vs - 1) (bellman_ford_init s)"
          "v \<in> set vs" "v \<noteq> s" "s \<in> set vs"
          "fst (the (connection_lookup connections v)) \<noteq> None"
        shows "distinct (rev (search_rev_path s connections v))"
proof-
  have "vwalk_bet (pred_graph connections) s (rev (search_rev_path s connections v)) v"
    using search_rev_path_is_pred_graph[OF assms]
    by simp
  moreover hence "length (rev (search_rev_path s connections v)) \<ge> 2"
    using assms(3) by(cases rule: remdups_adj.cases) (auto simp add: vwalk_bet_def)
  moreover have "no_cycle (pred_graph connections)"
    using bellman_ford_invar_pred_acyc_pres[of "length vs-1" s]
    by(fastforce simp add: assms(1) invar_pred_acyc_def no_cycle_def)
  moreover have "backward_determ (pred_graph connections)"
    by(auto simp add: backward_determ_def pred_graph_def)
  ultimately show "distinct (rev (search_rev_path s connections v))"
    by(fastforce intro: unique_path_backward_determ_distinct)
qed

lemma bellman_ford_s_costs_remain_zero:
  shows "snd (the (connection_lookup (bellman_ford (length vs - 1) (bellman_ford_init s)) s)) = 0"
proof(rule ccontr, goal_cases)
  case 1
  define spred where "spred = the (fst (the (connection_lookup (local.bellman_ford (length vs -1) (bellman_ford_init s)) s)))"
  have edge_in_pred_Graph: "(spred, s) \<in> pred_graph (bellman_ford (length vs -1) (bellman_ford_init s))"
    using "1"  bellman_ford_init_dom_is bellman_ford_s_pred_remains_zero_pres  same_domain_bellman_ford 
    by (auto simp add: invar_s_pred_remains_zero_def pred_graph_def spred_def)
  note top = 1
  hence "fst (the (connection_lookup (local.bellman_ford (length vs -1) (bellman_ford_init s)) s)) \<noteq> None"
    using bellman_ford_s_pred_remains_zero_pres
    by(auto simp add:  invar_s_pred_remains_zero_def)
  moreover have "spred \<in> dom (connection_lookup (bellman_ford (length vs -1) (bellman_ford_init s)))" 
    using bellman_ford_init_dom_is bellman_ford_pred_in_dom_pres[of s ]  same_domain_bellman_ford[of _ s]
          calculation(1)
    by(auto simp add: spred_def invar_pred_in_dom_def)
  moreover have s_not_pred:"s \<noteq> spred"
  proof(rule ccontr, goal_cases)
    case 1
    hence " vwalk_bet (pred_graph (local.bellman_ford (length vs - 1) (bellman_ford_init s))) s [s,s] s"
      using  edge_in_pred_Graph by auto
    then show ?case 
      using bellman_ford_invar_pred_acyc_pres[of "length vs -1" s]
      unfolding invar_pred_acyc_def by fastforce
  qed
  moreover have "search_rev_path_dom (s, local.bellman_ford (length vs - 1) (bellman_ford_init s), spred)"
    using bellman_ford_init_dom_is[of s]  bellman_ford_invar_pred_has_pred_pres[of s "length vs -1"] 
          calculation(1) calculation(2)
          s_not_pred same_domain_bellman_ford search_rev_path_dom_bellman_ford 
        by(auto simp add: spred_def  invar_pred_has_pred_def Let_def)
  ultimately have vwalk_s_spred:"vwalk_bet (pred_graph (local.bellman_ford (length vs - 1) (bellman_ford_init s))) s
   (rev (search_rev_path s (local.bellman_ford (length vs - 1) (bellman_ford_init s)) spred)) spred"
    using bellman_ford_pred_in_dom_pres[of s "length vs -1"]
          bellman_ford_init_dom_is bellman_ford_invar_pred_has_pred_pres[of s "length vs -1"]
          same_domain_bellman_ford search_rev_path_dom_bellman_ford[of s "length vs - 1" s]
    by(intro search_rev_path_is_in_pred_graph)(auto simp add: spred_def Let_def  invar_pred_has_pred_def )
  hence "vwalk_bet (pred_graph (local.bellman_ford (length vs - 1) (bellman_ford_init s))) s
   (rev (search_rev_path s (local.bellman_ford (length vs - 1) (bellman_ford_init s)) spred) @ [s]) s"
    using edge_in_pred_Graph 
    by(auto intro:  vwalk_bet_transitive[of _ s _ spred "[spred, s]" s, simplified])
  then show ?case 
      using bellman_ford_invar_pred_acyc_pres[of "length vs -1" s] vwalk_s_spred less_eq_Suc_le 
      by (fastforce simp add: invar_pred_acyc_def )
qed

theorem search_rev_path_bellman_ford_less_costs:
  assumes "connections = bellman_ford (length vs - 1) (bellman_ford_init s)"
          "v \<in> set vs" "v \<noteq> s" "s \<in> set vs"
          "fst (the (connection_lookup connections v)) \<noteq> None"
    shows "weight (rev (search_rev_path s connections v)) \<le> 
            snd (the (connection_lookup connections v))"
proof-
  have dommy: "search_rev_path_dom (s, connections, v)"
    using assms(1) assms(2) assms(5) search_rev_path_dom_bellman_ford by blast
  show ?thesis
    using assms
  proof(induction rule:  search_rev_path.pinduct[OF dommy])
    case (1 s connections v)
    note IH= this
    define pred where "pred = the (fst (the (connection_lookup connections v)))"
    have costs_mono: "snd (the (connection_lookup connections v)) \<ge>
                      snd (the (connection_lookup connections pred)) + edge_costs pred v"
      using IH(3) IH(4) IH(7) 
            same_domain_bellman_ford  bellman_ford_invar_pred_mono_pres[of "length vs -1" s] 
         by(auto simp add: pred_def invar_pred_mono_def  bellman_ford_init_dom_is )
  show ?case 
  proof(cases "pred = s")
    case True
    have search_from_pred_is_s:"search_rev_path s connections pred = [s]"
      using True pred_def 
      by (subst search_rev_path.psimps, auto intro: search_rev_path.domintros)
    hence "search_rev_path s connections v = [v, s]"
      using IH(1,5) search_from_pred_is_s 
      by(auto simp add: pred_def Let_def search_rev_path.psimps[OF IH(1)])
    moreover have "snd (the (connection_lookup connections pred)) = 0" 
      using IH(3) True bellman_ford_s_costs_remain_zero by blast
    then show ?thesis 
      using True calculation costs_mono by fastforce
  next
    case False
    have vwalk_s_pred:"vwalk_bet (pred_graph connections) s (rev (search_rev_path s connections pred)) pred"
      apply(rule search_rev_path_is_in_pred_graph[of s _ pred])
      apply(rule search_rev_path_dom_bellman_ford[of pred "length vs -1" s, simplified sym[OF IH(3)]])
      using False IH(3-) bellman_ford_init_dom_is[of s] same_domain_bellman_ford[of "length vs -1" s]
            bellman_ford_invar_pred_has_pred_pres[of s "length vs -1" ]
            bellman_ford_pred_in_dom_pres[of s "length vs -1" ]
      by(auto simp add: invar_pred_has_pred_def  vwalk_bet_def pred_def invar_pred_in_dom_def Let_def)
    hence non_empt_path:" (rev (search_rev_path s connections pred)) \<noteq> []"
      by fastforce
    have IHapplied: 
     "weight (rev (search_rev_path s connections pred))
    \<le> snd (the (connection_lookup connections pred))" 
     using  False IH(3-) bellman_ford_init_dom_is[of s ] same_domain_bellman_ford[of "length vs -1" s]
           bellman_ford_invar_pred_has_pred_pres[of s "length vs -1"]
           bellman_ford_pred_in_dom_pres [of s "length vs -1"]
     by(intro IH(2))(auto simp add: pred_def invar_pred_has_pred_def invar_pred_in_dom_def)
   have weight_one_step: "weight (rev (search_rev_path s connections pred)@[v]) =
   weight (rev (search_rev_path s connections pred)) +  edge_costs pred v"
   proof-
     have "weight (rev (search_rev_path s connections pred)@[v])
          = weight (butlast (rev (search_rev_path s connections pred))@[pred, v])"
       apply(rule  vwalk_bet_props[OF vwalk_s_pred])
       by(metis append_butlast_last_cancel)
     also have "... = weight (butlast (rev (search_rev_path s connections pred))@[pred]) +  edge_costs pred v"
       using  weight_append_last[of _ pred v, simplified] by simp
     also have "... = weight (rev (search_rev_path s connections pred)) +  edge_costs pred v"
       apply(rule  vwalk_bet_props[OF vwalk_s_pred])
       using append_butlast_last_id 
       by force
     finally show ?thesis
       by simp
   qed
    show ?thesis
      apply(subst search_rev_path.psimps)
      using IH(1) IH(5)
      using  IHapplied add_right_mono  weight_one_step 
      by (auto intro!: order.trans[OF _  costs_mono] simp add: pred_def)
  qed
qed
qed

theorem computation_of_optimum_path:
  assumes "connections = bellman_ford (length vs - 1) (bellman_ford_init s)"
          "v \<in> set vs" "v \<noteq> s" "s \<in> set vs"
          "fst (the (connection_lookup connections v)) \<noteq> None"
    shows "opt_vs_path s v (rev (search_rev_path s connections v))"
proof-
  obtain p where p_prop:"opt_vs_path s v p"
    using assms(3) optpath_exists[OF _ assms(4,2)] by auto
  moreover have "snd (the (connection_lookup connections v)) = weight p"
    using assms bellamn_ford_equality optpath_bellman_ford p_prop by simp
  moreover have "weight (rev (search_rev_path s connections v)) 
                 \<le> snd (the (connection_lookup connections v))"
    using assms search_rev_path_bellman_ford_less_costs by simp
  moreover have "vs_path s v (rev (search_rev_path s connections v))"
  proof(rule vsp_pathI, goal_cases)
    case 1
    then show ?case 
      apply(rule vwalk_bet_props[OF search_rev_path_is_pred_graph[OF assms]])
      using assms(3) 
      by(cases "rev (search_rev_path s connections v)" rule: remdups_adj.cases) auto
  next
    case 2
    then show ?case 
      apply(rule vwalk_bet_props[OF search_rev_path_is_pred_graph[OF assms]])
      using assms(3) 
      by(cases "rev (search_rev_path s connections v)" rule: remdups_adj.cases) auto
  next
    case 3
    then show ?case 
      apply(rule vwalk_bet_props[OF search_rev_path_is_pred_graph[OF assms]])
      using assms(3) 
      by(cases "rev (search_rev_path s connections v)" rule: remdups_adj.cases) auto
  next
    case 4
    then show ?case 
      by(auto intro: vwalk_bet_props[OF search_rev_path_is_in_es[OF assms]]
           simp add: subsetI vs_and_es vwalk_then_in_dVs)
  qed
  ultimately show ?thesis
    by(auto intro: better_opt_path_is_opt_path)
qed

lemma bellamn_ford_path_exists_result_le_PInfty:
  assumes "s \<in> set vs" "s \<noteq> v" "v \<in> set vs" "weight P < PInfty" "hd P = s" "last P = v" "length P \<ge> 2"
  shows      "snd (the (connection_lookup (bellman_ford (length vs - 1) (bellman_ford_init s)) v)) 
              < PInfty"
proof-
  obtain OP where OP_prop:"opt_vs_path s v OP" 
    using assms(1) assms(2) assms(3) optpath_exists by auto
  moreover have "weight OP = OPT (length vs - 1) s v"
    using  optpath_bellman_ford[OF OP_prop] assms by simp
  moreover have "snd (the (connection_lookup (local.bellman_ford (length vs - 1) (bellman_ford_init s)) v)) =
          OPT (length vs - 1) s v"
    using  bellamn_ford_equality[of s v] 
    by (simp add: assms(1) assms(2) assms(3))
  moreover have "vs_path s v P" 
    using assms  weight_le_PInfty_in_vs
    by (auto simp add: vs_path_def )
  moreover hence "weight P \<ge> weight OP"
    using OP_prop
    by(auto simp add:opt_vs_path_def)
  ultimately show ?thesis
    using assms(4) by order
qed
 
theorem bellman_ford_search_rev_path_weight:
  assumes "connections = bellman_ford (length vs - 1) (bellman_ford_init s)"
          "v \<in> set vs" "v \<noteq> s" "s \<in> set vs"
          "fst (the (connection_lookup connections v)) \<noteq> None"
        shows "weight (rev (search_rev_path s connections v)) =
               snd (the (connection_lookup connections v))"
  using assms(1) assms(2) assms(3) assms(4) assms(5) bellamn_ford_equality 
        computation_of_optimum_path optpath_bellman_ford by presburger

end

lemma weight_le_PInfty_OPTle_PInfty:
  assumes "weight (s#xs@[t]) < PInfty"  "s \<noteq> t" "l = length xs"
  shows "OPT (length vs -1) s t < PInfty"
using assms
proof(induction l arbitrary: s t xs rule: less_induct)
  case (less l)
  have in_vs:"set (s#xs@[t]) \<subseteq> set vs" 
    using  weight_le_PInfty_in_vs[OF _  less(2)]
    by simp
  show ?case 
  proof(cases "distinct (s#xs@[t])")
    case True
    hence "length (s#xs@[t]) \<le> length vs" 
      using   card_mono[OF _ in_vs ] distinct_card[OF distinct_vs] 
              distinct_card[OF True] by simp
    moreover hence "length xs + 1 \<le> length vs - 1"
      by simp
    moreover have " set xs \<subseteq> set vs"
      using in_vs by simp
    ultimately show ?thesis
      using less(2-) finite_weight_set 
      by (subst OPT_def, subst linorder_class.Min_less_iff) auto
  next
    case False
    then obtain as bs cs x where dist_split:"s # xs @ [t] = as@[x]@bs@[x]@cs"
      using not_distinct_decomp by blast
    moreover hence "weight (as@[x]@cs)  < PInfty" 
      using weight_list_split'[of as x "bs@[x]@cs"] weight_list_split'[of "[x]@bs" x cs]
            weight_list_split'[of "as" x cs] less(2) 
      by simp
    moreover obtain ys where ys:"s # ys @ [t] = as@[x]@cs"
      using dist_split less.prems(2) 
       by(cases cs, all \<open>cases bs\<close>,  all \<open>cases as\<close>)(auto simp add: snoc_eq_iff_butlast)
    moreover have "length (s # ys @ [t])< length  (s # xs @ [t])" 
      using ys dist_split  by simp
    moreover hence "length ys < length xs" by simp
    ultimately show ?thesis 
      using less by auto
  qed
qed
lemmas code_lemmas[code] = search_rev_path_exec.simps

find_theorems compow connection_lookup
end
end
