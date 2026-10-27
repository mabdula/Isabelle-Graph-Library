theory Alternating_Forest_Odd_Expansion
  imports Basic_Matching.Alternating_Forest_Executable
begin

lemma undir_delta_of_UD_is:
  "{{u, nu} |nu. {u, nu} \<in> UD G} = UD (\<delta>\<^sup>+ G u \<union> \<delta>\<^sup>- G u)"
  by(auto simp add: UD_def delta_plus_def delta_minus_def doubleton_eq_iff)

locale alternating_forest_odd_expansion_spec = 
alternating_forest_spec evens odds get_path abstract_forest forest_invar roots
    for evens::"'forest \<Rightarrow> 'vset"
    and odds::"'forest \<Rightarrow> 'vset"
    and get_path::"'forest \<Rightarrow> 'v \<Rightarrow> 'v list"
    and abstract_forest::"'forest \<Rightarrow> 'v set set"
    and forest_invar::"'v set set \<Rightarrow> 'forest \<Rightarrow> bool"
    and roots::"'forest \<Rightarrow> 'vset"
    and vset_empty::'vset +
  fixes the_other_neighb_of_odd:: "'forest \<Rightarrow> 'v \<Rightarrow> 'v"
    and expand_odd:: "'forest \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v list \<Rightarrow> 'forest"
  assumes the_other_neighb_of_odd:
     "\<And> \<M> F u. \<lbrakk>forest_invar \<M> F; u \<in> vset_to_set (odds F)\<rbrakk> \<Longrightarrow> 
        {the_other_neighb_of_odd F u} = {v | v. {u, v} \<in> abstract_forest F \<and> {u, v} \<notin> \<M>}"
     "\<And> \<M> F u v. \<lbrakk>forest_invar \<M> F; u \<in> vset_to_set (odds F); {u, v} \<in> \<M>; matching \<M>\<rbrakk> \<Longrightarrow> 
        {{u, nu} |nu. {u, nu} \<in> abstract_forest F} = {{u, the_other_neighb_of_odd F u}, {u, v}}"
   assumes expand_odd:
     "\<And> \<M> F u mu p. odd_expansion_precond \<M> F u mu p \<Longrightarrow>
       forest_invar (\<M> - {{u, mu}} \<union> {edges_of_path (p@[mu]) ! i| i. i < length p \<and> even i })
                    (expand_odd F u mu p)"
     "\<And> \<M> F u mu p. odd_expansion_precond \<M> F u mu p \<Longrightarrow> 
       abstract_forest (expand_odd F u mu p) = 
       abstract_forest F - {{u, nu} | nu. {u, nu} \<in> abstract_forest F}
            \<union> set (edges_of_path (the_other_neighb_of_odd F u #p@[mu]))"
     "\<And> \<M> F u mu p. odd_expansion_precond \<M> F u mu p \<Longrightarrow> 
       vset_to_set (odds (expand_odd F u mu p)) =
       vset_to_set (odds F) - {u} \<union> {p ! i | i. i < length p \<and> even i}"
     "\<And> \<M> F u mu p. odd_expansion_precond \<M> F u mu p \<Longrightarrow> 
       vset_to_set (evens (expand_odd F u mu p)) =
       vset_to_set (evens F) \<union> {p ! i | i. i < length p \<and> odd i}"
     "\<And> \<M> F u mu p. odd_expansion_precond \<M> F u mu p \<Longrightarrow> 
       roots (expand_odd F u mu p) = roots F"
     "\<And> \<M> F u mu p. odd_expansion_precond \<M> F u mu p \<Longrightarrow> 
         matching (\<M> - {{u, mu}} \<union> {edges_of_path (p@[mu]) ! i| i. i < length p \<and> even i })"
  
context 
  forest_manipulation_spec
begin

definition 
  "expand_odd (F::('vset, 'vset, 'vset, 'parent, 'origin) alt_forest) u cu p =
      (let prnts = parents F;
        rts = roots F;
        evs = evens F;
        ods = odds F;
        orngs = origins F;
        additional_odds = take_evens p;
        additional_evens = take_odds p;
        evs' = foldl (\<lambda> E x. vset_insert x E) evs additional_evens;
        ods' = foldl (\<lambda> E x. vset_insert x E) (vset_delete u ods) additional_odds;
        prnts' = foldl2 (\<lambda> par x y. parent_upd y x par) (parent_delete u prnts)
               (the (parent_lookup prnts u)#p@[cu]);
        uorg = the (origin_lookup orngs u);
        orngs' = foldl (\<lambda> org x. origin_upd x uorg org) (origin_delete u orngs) p
       in Forest rts evs' ods' prnts' orngs')"

definition "the_other_neighb_of_odd F u = the (parent_lookup (parents F) u)"

end

context 
  forest_manipulation
begin

lemma foldr2_parent_upd:
  assumes "parent_invar prnts" "length xs \<ge> 2" "distinct xs"
    "prnts' = foldr2 parent_upd xs prnts"
  shows "parent_invar prnts'" (is ?th1)
    and  "{(x, y) | x y. parent_lookup prnts' x = Some y} =
     {(x, y) | x y. parent_lookup prnts x = Some y} -
     {(x, y) | x y. parent_lookup prnts x = Some y \<and> x \<in> set (butlast xs)}
     \<union> set (edges_of_vwalk xs)" (is ?th2)
proof-
  have "?th1 \<and> ?th2"
    using assms(3,4)
  proof(induction arbitrary: prnts' rule: list_induct3_len_geq_2[OF assms(2)], goal_cases)
    case (1 x y prnts')
    then show ?case 
      using assms(1)
      by (auto intro!: parent_map.invar_update 
          simp add: parent_map.map_update if_split[of "\<lambda> x. x = Some _"])
  next
    case (2 x y xs prnts')
    note prnts'_def = 2(3)
    have distinct_here: "distinct (y # xs)"
      using 2(2) by auto
    note big_distinct = 2(2)
    note IH = conjunct1[OF 2(1)[OF distinct_here]] conjunct2[OF 2(1)[OF distinct_here]]
    define prnts'' where "prnts'' = (foldr2 parent_upd (y # xs) prnts)"
    note prnts'_def = 2(3)[simplified foldr2.simps o_apply prnts''_def[symmetric]]
    note IH' = IH[OF refl, simplified prnts''_def[symmetric]]
    show ?case 
    proof(rule, goal_cases)
      case 1
      then show ?case 
        using IH'(1)
        by(auto intro!: parent_map.invar_update 
            simp add: prnts'_def)
    next
      case 2
      have "{(x, y) |x y. parent_lookup prnts' x = Some y} = 
       {(x, y) |x y. parent_lookup prnts'' x = Some y} 
           - {(x, y) | y. parent_lookup prnts'' x = Some y} 
        \<union> {(x, y)}"
        using IH'(1)
        by(auto simp add: prnts'_def parent_map.map_update if_split[of "\<lambda> x. x = Some _"])
      thus ?case 
        using IH'(2) big_distinct bulast_subset[of xs]
        by (auto dest!: v_in_edge_in_vwalk'(1)[of x _ "y#xs"])
    qed
  qed
  thus ?th1 ?th2
    by auto
qed

lemma effect_of_expand_odd:
  assumes "vset_invar evs" "vset_invar ods" 
    "vset_invar rts" "parent_invar prnts" "origin_invar orngs"
    and new_forest_def: "new_forest = expand_odd (Forest rts evs ods prnts orngs) u cu p"
    and p_well_formed: "the (parent_lookup prnts u) \<notin> set p" "cu \<notin> set p" "distinct p"
    "cu \<noteq> the (parent_lookup prnts u)"
  shows "vset_invar (evens new_forest)" "vset_invar (odds new_forest)"
    "parent_invar (parents new_forest)" "origin_invar (origins new_forest)"
    and "roots new_forest = rts" (is ?th1)
    and "vset_to_set (odds new_forest) =
         vset_to_set ods -{u} \<union> {p ! i | i. i < length p \<and> even i}" (is ?th2)
    and "vset_to_set (evens new_forest) =
         vset_to_set evs \<union> {p ! i | i. i < length p \<and> odd i}" (is ?th3)
    and "{(x, y) | x y. parent_lookup (parents new_forest) x = Some y} =
         {(x, y) |x y. parent_lookup prnts x = Some y} -
         {(x, y) |x y.
           parent_lookup prnts x = Some y \<and> x \<in> (set p) \<union> {u, cu}} \<union>
         prod.swap ` (set (edges_of_vwalk (the (parent_lookup prnts u)#p@[cu])))" (is ?th4)
    and "origin_lookup (origins new_forest) =
         (\<lambda> x. if x \<in> set p then Some (the (origin_lookup orngs u))
               else if x = u then None
               else origin_lookup orngs x)" (is ?th5)
proof-
  define additional_odds where "additional_odds = take_evens p"
  define additional_evens where "additional_evens = take_odds p"
  define evs' where "evs' = foldl (\<lambda> E x. vset_insert x E) evs additional_evens"
  define ods' where " ods' = foldl (\<lambda> E x. vset_insert x E) (vset_delete u ods) additional_odds"
  define rev_addev where "rev_addev = rev additional_evens"
  have addevs_is: "rev additional_evens = rev_addev" "set additional_evens = set rev_addev"
    by(auto simp add: rev_addev_def)
  have "vset_invar evs' \<and> vset_to_set evs' = vset_to_set evs \<union> set additional_evens"
    unfolding evs'_def foldl_conv_foldr addevs_is
    using assms(1)
    by(induction rev_addev)(simp add: vset.invar_insert vset.set_insert)+
  thus "vset_invar (evens new_forest)" ?th3
    by (auto simp add: take_odds_set new_forest_def evs'_def additional_evens_def
        expand_odd_def Let_def)
  define rev_addod where "rev_addod = rev additional_odds"
  have addod_is: "rev additional_odds = rev_addod" "set additional_odds = set rev_addod"
    by(auto simp add: rev_addod_def)
  have "vset_invar ods' \<and> vset_to_set ods' = vset_to_set ods - {u} \<union> set additional_odds"
    unfolding ods'_def foldl_conv_foldr addod_is
    using assms(2)
    by(induction rev_addod)(simp add: vset.invar_insert vset.set_insert vset.invar_delete vset.set_delete)+
  thus "vset_invar (odds new_forest)" ?th2
    by (auto simp add: take_evens_set new_forest_def ods'_def additional_odds_def
        expand_odd_def Let_def)
  show ?th1 
    by(auto simp add: new_forest_def expand_odd_def)
  define prnts' where "prnts' = foldl2 (\<lambda> par x y. parent_upd y x par) (parent_delete u prnts)
               (the (parent_lookup prnts u)#p@[cu])"
  define upcu_rev where "upcu_rev = rev (the (parent_lookup prnts u)#p@[cu])"
  have upcu_rev_is: "rev (the (parent_lookup prnts u)#p@[cu]) = upcu_rev" "set (the (parent_lookup prnts u)#p@[cu]) = set upcu_rev"
    by(auto simp add: upcu_rev_def)
  have set_butlast_is:"set (butlast upcu_rev) = insert cu (set p)"
    by(auto simp add: upcu_rev_def)
  have invar_after_u_removal: "parent_invar (parent_delete u prnts)"
    by (simp add: assms(4) parent_map.invar_delete)
  have upcu_rev_length: "2 \<le> length upcu_rev"
    by(auto simp add: upcu_rev_def)
  have distinct_upcu_rev: "distinct upcu_rev"
    using p_well_formed by(auto simp add: upcu_rev_def)
  have parent_new_forest_are:"parents new_forest = prnts'"
    by(auto simp add: new_forest_def prnts'_def expand_odd_def)
  have edges_rev_is:"set (edges_of_vwalk upcu_rev) =
        prod.swap ` set (edges_of_vwalk (the (parent_lookup prnts u) # p @ [cu]))"
    unfolding upcu_rev_def edges_of_vwalk_rev 
    by simp
  show ?th4 "parent_invar (parents new_forest)"
    using assms(4) foldr2_parent_upd[OF invar_after_u_removal upcu_rev_length
        distinct_upcu_rev refl]
    unfolding parent_new_forest_are prnts'_def foldl2_conv_foldr2 upcu_rev_is
      set_butlast_is edges_rev_is
    by (auto simp add: parent_map.map_delete if_split[of "\<lambda> x. x = Some _"])
  define uorg where "uorg = the (origin_lookup orngs u)"
  define orngs' where 
    "orngs' = foldl (\<lambda> org x. origin_upd x uorg org) (origin_delete u orngs) p"
  define rev_p where "rev_p = rev p"
  have rev_p: "rev p = rev_p" "set p = set rev_p"
    by(auto simp add: rev_p_def)
  have "origin_invar orngs' \<and> 
         origin_lookup orngs'  = (\<lambda>x. if x \<in> set p then Some uorg
          else if x = u then None else origin_lookup orngs x)"
    using assms(5)
    unfolding orngs'_def foldl_conv_foldr rev_p
    by(induction rev_p)(auto simp add: origin origin_map.invar_delete origin_map.map_delete)
  thus "origin_invar (origins new_forest)" ?th5
    by(auto simp add: orngs'_def uorg_def new_forest_def expand_odd_def)
qed  

lemma the_other_neighb_of_odd_correct1:
  assumes "forest_invar \<M> (Forest rts evs ods prnts orngs)" 
    "u \<in> vset_to_set ods"
  shows "{the_other_neighb_of_odd (Forest rts evs ods prnts orngs) u} = 
         {v | v. {u, v} \<in> abstract_forest (Forest rts evs ods prnts orngs) \<and> {u, v} \<notin> \<M>}"
    (is ?th1)
    and "the_other_neighb_of_odd (Forest rts evs ods prnts orngs) u \<noteq> u" (is ?th2)
proof-
  note forest_invarD = forest_invarD[OF assms(1)]

  obtain v where v: "parent_lookup prnts u = Some v" "{u, v} \<notin> \<M>"
    using assms(2) forest_invarD(7)
    by(auto elim!: invar_odd_to_parent_non_matchingE)

  have uv: "{u, v} \<in> abstract_forest (Forest rts evs ods prnts orngs)"
    using v(1) by(auto simp add: abstract_forest_def)

  have other_edge:
    "\<lbrakk>{u, x} \<in> abstract_forest (Forest rts evs ods prnts orngs); {u, x} \<notin> \<M>\<rbrakk> \<Longrightarrow> x = v" for x
  proof(goal_cases)
    case 1
    hence "parent_lookup prnts u = Some x \<or> parent_lookup prnts x = Some u"
      by(auto simp add: abstract_forest_def doubleton_eq_iff)
    moreover have False if "parent_lookup prnts x = Some u"
    proof-
      have "{u, x} \<in> \<M>" 
        using "1"(1)  assms(2) that forest_invarD
        by(force elim!: invar_forest_even_and_oddE invar_even_to_parent_matchingE 
            simp add: insert_commute)
      thus False
        using 1(2) by auto
    qed
    moreover have "x = v" if "parent_lookup prnts u = Some x"
      using v(1) that by simp
    ultimately show ?thesis
      by auto
  qed

  show ?th1
    using v(2) other_edge
    by (auto simp add: v(1) uv the_other_neighb_of_odd_def)

  show ?th2
    using v(1) assms(1,2) uv forest_invarD(3)
    by(auto dest!: invar_forest_even_and_oddD simple_invariant_consequences(4) 
        simp add: the_other_neighb_of_odd_def)

qed

lemma the_other_neighb_of_odd_correct2:
  assumes "forest_invar \<M> (Forest rts evs ods prnts orngs)" 
    "u \<in> vset_to_set ods" "{u, v} \<in> \<M>" "matching \<M>"
  shows "{the_other_neighb_of_odd (Forest rts evs ods prnts orngs) u} = 
         {v' | v'. {u, v'} \<in> abstract_forest (Forest rts evs ods prnts orngs) \<and> v \<noteq> v'}"
  using assms(3,4) 
  by(auto simp add: the_other_neighb_of_odd_correct1[OF assms(1,2)] 
      dest: doubleton_in_matching(1))

lemma delta_of_odd:
  assumes "forest_invar \<M> (Forest rts evs ods prnts orngs)" 
    "u \<in> vset_to_set ods" "{u, v} \<in> \<M>" "matching \<M>"
  shows "{{u, nu} |nu. {u, nu} \<in> abstract_forest (Forest rts evs ods prnts orngs)} =
         {{u, the_other_neighb_of_odd (Forest rts evs ods prnts orngs) u}, {u, v}}"
proof-
  obtain mu' where mu': "parent_lookup prnts mu' = Some u" "{u, mu'} \<in> \<M>"
    "mu' \<in> vset_to_set evs"
    "\<And> y'. parent_lookup prnts y' = Some u \<Longrightarrow> mu' = y'"
  proof-
    show thesis
    proof(rule odds_unique_child[OF assms(1), simplified, OF assms(2)], goal_cases)
      case 1
      then show ?case 
        using assms(4) by auto
    next
      case (2 y)
      note 2 = 2[simplified]
      show ?case 
        by(auto intro!: that[OF 2])
    qed
  qed
  show ?thesis
  proof(rule, all \<open>rule\<close>, goal_cases)
    case (1 e)
    then show ?case 
    proof(cases "e \<in> \<M>", goal_cases)
      case 1
      then show ?thesis 
        using assms(3,4) doubleton_in_matching(1) by fastforce
    next
      case 2
      then obtain nu where "parent_lookup prnts u = Some nu 
                           \<or> parent_lookup prnts nu = Some u" "e = {u, nu}"
        by(fastforce simp add:  abstract_forest_def)
      then show ?thesis 
        using assms 2(2) mu'(2,4)
        by(auto simp add: the_other_neighb_of_odd_def 
            elim!: forest_invarE) 
    qed
  next
    case (2 e)
    moreover have "parent_lookup prnts u = 
          Some (the_other_neighb_of_odd (Forest rts evs ods prnts orngs) u)"
      using  assms(1,2) 
      by(auto elim!: forest_invarE invar_odd_to_parent_non_matchingE 
          simp add: the_other_neighb_of_odd_def)
    moreover have "parent_lookup prnts v = Some u"
      using assms(3,4) mu'(1,2) doubleton_in_matching(1)[of \<M> u mu' v] 
      by simp
    ultimately show ?case 
      by(auto simp add: abstract_forest_def)
  qed
qed

lemma expand_odd_correct:
  assumes "forest_invar \<M> (Forest rts evs ods prnts orngs)" 
    "matching \<M>"  "u \<in> vset_to_set ods" "{u, mu} \<in> \<M>" "odd (length p)" 
    "set p \<inter> 
     (Vs (abstract_forest (Forest rts evs ods prnts orngs)) \<union> vset_to_set rts \<union> Vs \<M>) 
     \<subseteq> {u}"
    "distinct p"
    and new_forest_def:
    "new_forest = expand_odd (Forest rts evs ods prnts orngs) u mu p"
    and M'_def: "\<M>' = (\<M> - {{u, mu}})
         \<union> {edges_of_path (p@[mu]) ! i| i. i < length p  \<and> even i }" 
  shows "forest_invar \<M>' new_forest" (is ?th1)
    and  "abstract_forest new_forest 
         = abstract_forest (Forest rts evs ods prnts orngs) -
           {{u, nu} | nu. {u, nu} \<in> abstract_forest (Forest rts evs ods prnts orngs)}
         \<union> set (edges_of_path (the_other_neighb_of_odd
                (Forest rts evs ods prnts orngs) u #p@[mu]))" (is ?th2)
    and "vset_to_set (odds new_forest) = vset_to_set ods - {u} \<union> {p ! i | i. i < length p \<and> even i}" 
    (is ?tha)
    and "vset_to_set (evens new_forest) = vset_to_set evs \<union> {p ! i | i. i < length p \<and> odd i}" 
    (is ?thb)
    and "roots new_forest = rts" (is ?th3)
    and "matching \<M>'" (is ?th4)
proof-

  note forest_invar_F = forest_invarD[OF assms(1)]
  note invar_basic_F = invar_basicD[OF forest_invar_F(1), simplified]
  note invar_basicD_here = 
    invar_basicD[OF forest_invar_F(1), simplified alt_forest.sel]
  note invar_matching_both_or_noneD_here = 
    invar_matching_both_or_noneD[OF forest_invar_F(2), simplified alt_forest.sel]
  note invar_forest_even_and_oddD_here = 
    invar_forest_even_and_oddD[OF forest_invar_F(3), simplified alt_forest.sel]
  note invar_parent_wfD_here = 
    invar_parent_wfD[OF forest_invar_F(4), simplified alt_forest.sel]
  note invar_even_to_parent_matchingD_here = 
    invar_even_to_parent_matchingD[OF forest_invar_F(5), simplified alt_forest.sel]
  note invar_rootsD_here = 
    invar_rootsD[OF forest_invar_F(6), simplified alt_forest.sel]
  note invar_odd_to_parent_non_matchingD_here = 
    invar_odd_to_parent_non_matchingD[OF forest_invar_F(7), simplified alt_forest.sel]
  note invar_odd_is_parentD_here = 
    invar_odd_is_parentD[OF forest_invar_F(8), simplified alt_forest.sel]

  obtain pu where pu: "parent_lookup prnts u = Some pu" "{u, pu}\<notin> \<M>"
    using assms(3) forest_invar_F(7)
    by(auto elim!: invar_odd_to_parent_non_matchingE)
  have pu_not_u: "pu \<noteq> u" 
    using assms(3) odds_unique_child[OF assms(1) _ assms(2), of u] pu 
    by force
  have u_pu_inF_verts: "u \<in> Vs (abstract_forest (Forest rts evs ods prnts orngs))"
    "pu \<in> Vs (abstract_forest (Forest rts evs ods prnts orngs))"
    using pu(1) by(auto simp add: abstract_forest_def)
  hence pu_not_in_p:"pu \<notin> set p" 
    using assms(6) pu_not_u by auto
  have mu_not_u: "mu \<noteq> u"
    using pu(1,2) assms(4,3) invar_basic_F(6)
      invar_even_to_parent_matchingD_here[of mu pu] invar_matching_both_or_noneD_here[of mu mu]
      invar_forest_even_and_oddD_here[of mu mu] insertCI[of mu "{mu}" mu]
    by auto
  obtain mu' where mu': "parent_lookup prnts mu' = Some u" "{u, mu'} \<in> \<M>"
    "mu' \<in> vset_to_set evs"
    "\<And> y'. parent_lookup prnts y' = Some u \<Longrightarrow> mu' = y'"
  proof-
    show thesis
    proof(rule odds_unique_child[OF assms(1) _ assms(2), of u], goal_cases)
      case 1
      then show ?case 
        using assms(3) by auto
    next
      case (2 y)
      note 2 = 2[simplified]
      show ?case 
        by(auto intro!: that[OF 2])
    qed
  qed
  have mu_is_mu': "mu' = mu" 
    using assms(2,4)  mu'(2) by(auto intro!: doubleton_in_matching(1))
  note mu_props = mu'[simplified mu_is_mu']
  have mu_in_F_verts: "mu \<in> Vs (abstract_forest (Forest rts evs ods prnts orngs))"
    using  mu_props(1) by(auto simp add: abstract_forest_def)
  have effect_pc1: "the (parent_lookup prnts u) \<notin> set p"
    using pu_not_in_p by(auto simp add: pu)
  have effect_pc2: "mu \<notin> set p"
    using assms(6) mu_in_F_verts mu_not_u by auto
  have effect_pc3: "mu \<noteq> the (parent_lookup prnts u)"
    using mu_props(2) pu(1,2) by fastforce
  note effect_of_expand_odd = 
    effect_of_expand_odd[OF invar_basicD_here(2,3,1,4,5) new_forest_def
      effect_pc1 effect_pc2 assms(7) effect_pc3]

  show ?tha ?thb ?th3 
    using effect_of_expand_odd by auto

  have no_ev_p:"vset_to_set evs \<inter> set p = {}" 
    using  assms(6) invar_basic_F(6) invar_even_to_parent_matchingD_here pu
    by auto
  have ods_p: "vset_to_set ods \<inter> set p \<subseteq> {u}" 
    using assms(6) invar_basic_F(6) by auto
  have p_neq_Nil: "p \<noteq> []" 
    using assms(5) by force
  have other_neighb_u_even:
    "the_other_neighb_of_odd (Forest rts evs ods prnts orngs) u \<in> vset_to_set evs"
    using assms(1,2) u_pu_inF_verts(2) 
      invar_basic_F(6) pu(1,2) invar_even_to_parent_matchingD_here[of u pu]
      odds_unique_child[of \<M> "Forest rts evs ods prnts orngs" pu]
    by (auto simp add: the_other_neighb_of_odd_def) 

  have sth_is_Dabstract_forest_old:
    "{(x, y) |x y. Some x = parent_lookup prnts y} = 
       Dabstract_forest (Forest rts evs ods prnts orngs)"
    by(auto simp add: Dabstract_forest_def)
  have sth_is_Dabstract_forest_new: 
    "Dabstract_forest new_forest = 
       {(x, y) . 
         (y, x) \<in> {(x, y) |x y. parent_lookup (parents new_forest) x = Some y}}"
    by(auto simp add: Dabstract_forest_def)
  have sth_is_Dabstract_forest_new: "Dabstract_forest new_forest = 
         {(y, x) |x y. parent_lookup prnts x = Some y} -
        {(y, x) |x y. parent_lookup prnts x = Some y \<and> x \<in> set p \<union> {u, mu}} \<union>
         set (edges_of_vwalk (the (parent_lookup prnts u) # p @ [mu]))"
    unfolding sth_is_Dabstract_forest_new effect_of_expand_odd(8)
    by (auto simp add: Dabstract_forest_def)

  have Dabstract_forest_new_forest_is:
    "Dabstract_forest new_forest =
    Dabstract_forest (Forest rts evs ods prnts orngs) -
    \<delta>\<^sup>+ Dabstract_forest (Forest rts evs ods prnts orngs) u -
    \<delta>\<^sup>- Dabstract_forest (Forest rts evs ods prnts orngs) u \<union>
    set (edges_of_vwalk
          (the_other_neighb_of_odd (Forest rts evs ods prnts orngs) u # p @ [mu]))"
    unfolding sth_is_Dabstract_forest_old[symmetric] sth_is_Dabstract_forest_new
  proof(rule arg_cong2[of _ _ _ _ Set.union], goal_cases)
    case 1
    then show ?case
      using  assms(6) invar_basic_F(14)
      by (auto simp add: delta_plus_def delta_minus_def mu_props(1,4))+
  qed (auto simp add: the_other_neighb_of_odd_def)

  show new_AF_is: ?th2 
    unfolding Dabstract_forest_UD[symmetric] Dabstract_forest_new_forest_is
      undir_delta_of_UD_is path_edges_set_of_pair_of_vwalk_edges UD_union_hom
  proof(rule arg_cong2[where f = Set.union], goal_cases)
    case 1
    then show ?case 
    proof(subst special_UD_hom_subtract, goal_cases)
      case (1 u v)
      then show ?case 
        using forest_invar_F(4)
        by(auto simp add: delta_plus_def invar_parent_Dabstract_forest_wf
            dest: wf_not_sym)
    next
      case 2
      then show ?case 
        using forest_invar_F(4)
        by(auto simp add: delta_plus_def delta_minus_def invar_parent_Dabstract_forest_wf
            dest: wf_not_sym)
    next
      case 3
      then show ?case
      proof(subst special_UD_hom_subtract, goal_cases)
        case (1 u v)
        then show ?case 
          using forest_invar_F(4)
          by(auto simp add: invar_parent_Dabstract_forest_wf dest: wf_not_sym)
      qed (auto simp add: delta_plus_def)
    qed
  qed (auto simp add: UD_is_image_set_of_pair)

  define up where "up = the_other_neighb_of_odd (Forest rts evs ods prnts orngs) u"

  have Vs_after: "Vs (abstract_forest new_forest) =
        Vs (abstract_forest (Forest rts evs ods prnts orngs)) - {u} \<union> set p"
    unfolding new_AF_is
  proof(rule, all \<open>rule\<close>, goal_cases)
    case (1 x)
    then show ?case 
    proof(elim vs_member_elim, goal_cases)
      case (1 e)
      note one = this
      show ?case 
        using one(2)
      proof(elim UnE, goal_cases)
        case 1
        then obtain y where y: "e = {x, y}"
          using one(1) by(auto simp add: abstract_forest_def)
        hence "x \<noteq> u"
          using one(1) 1 by auto
        moreover have "x \<in> Vs (abstract_forest (Forest rts evs ods prnts orngs))"
          using "1" one(1) by auto
        ultimately show ?case 
          by auto
      next
        case 2
        hence "x \<in> set p \<union>
                 {the_other_neighb_of_odd (Forest rts evs ods prnts orngs) u, mu}" 
          using one(1) 
          by(auto dest!: vs_member_intro[of x e] simp add:  Vs_of_edges_of_path)
        moreover have "the_other_neighb_of_odd (Forest rts evs ods prnts orngs) u
           \<in> Vs (abstract_forest (Forest rts evs ods prnts orngs))" 
          by (simp add: pu(1) the_other_neighb_of_odd_def u_pu_inF_verts(2))
        ultimately show ?case
          using mu_in_F_verts mu_not_u 
          by (auto simp add: pu(1) pu_not_u the_other_neighb_of_odd_def)
      qed
    qed
  next
    case (2 x)
    then show ?case 
    proof(elim UnE, goal_cases)
      case 1
      then obtain y where y:
        "parent_lookup prnts x = Some y \<or> parent_lookup prnts y = Some x" "x \<noteq> u"
        by(auto elim!: vs_member_elim simp add: abstract_forest_def)
      have ?case if  "y \<noteq> u"
        using that y 
        by(auto intro!: vs_member_intro[of x "{x, y}"] simp add: abstract_forest_def)
      moreover have ?case if "y = u"
      proof(cases rule: disjE[OF y(1)])
        case 1
        hence xmu:"x = mu" 
          by (simp add: mu_props(4) that)
        show ?thesis 
        proof(rule vs_member_intro[of x "{last (up#p), mu}"], goal_cases)
          case 2
          then show ?case 
            unfolding up_def  append_Cons[symmetric]
            by(intro UnI2, subst edges_of_path_snoc[symmetric]) auto
        qed (simp add: xmu)
      next
        case 2
        hence xup:"x = up" 
          by (simp add: that the_other_neighb_of_odd_def up_def)
        show ?thesis 
        proof(rule vs_member_intro[of x "{up, hd (p @ [mu])}"], goal_cases)
          case 2
          then show ?case 
            by(intro UnI2, cases "p @ [mu]") (auto simp add: up_def)
        qed (simp add: xup)
      qed
      ultimately show ?case 
        by auto
    next
      case 2
      then show ?case 
        by(auto simp add: vs_union Vs_of_edges_of_path)
    qed
  qed

  have Vs_of_M'_are:"Vs \<M>' = Vs \<M> - {u} \<union> set p"
    using mu_not_u assms(4,5)
    by (auto simp add: M'_def vs_union verts_of_even_edges[of "_ @[_]", simplified] 
        remove_matching_edges_Vs[OF assms(2)] Vs_of_edge)

  have dom_parent_lookup_after_is:
    "dom (parent_lookup (parents new_forest)) = dom (parent_lookup prnts) -
      {u} \<union> set (p @[mu])"
  proof(rule, all \<open>rule\<close>, goal_cases)
    case (1 x)
    then obtain y where "parent_lookup (parents new_forest) x = Some y"
      by blast
    hence disj:"parent_lookup prnts x = Some y \<and> x \<notin> set p \<union> {u, mu} \<or>
          (y, x) \<in> set (edges_of_vwalk (the (parent_lookup prnts u) # p @ [mu]))"
      using effect_of_expand_odd(8) by auto
    then show ?case 
      by (auto dest: v_in_edge_in_vwalk'(2))
  next
    case (2 x)
    then show ?case 
    proof(cases "x \<in> set (p @ [mu])")
      case True
      note true = this
      have  "\<exists> y.(y, x) \<in> set (edges_of_vwalk (the (parent_lookup prnts u) # p @ [mu]))"
      proof(cases "x = hd (p@[mu])")
        case True
        then show ?thesis 
          by(cases p) auto
      next
        case False
        then obtain p1 p2 where "p@[mu] = p1@[x]@p2" 
          using true
          by(auto simp add: in_set_conv_decomp)
        then obtain p1 p2 y where "p@[mu] = p1@[y, x]@p2"
          using False by(cases p1 rule: rev_cases) auto      
        then show ?thesis 
          using edges_of_vwalk_append[of "the (parent_lookup prnts u) # p1" "y # x # p2"]
          by(auto intro!: exI[of _ y])
      qed
      thus ?thesis
        using effect_of_expand_odd(8) by auto
    next
      case False
      then obtain y where y: "parent_lookup prnts x = Some y" "x \<noteq> u"
        using 2 by auto
      thus ?thesis
        using effect_of_expand_odd(8) False by auto
    qed
  qed

  have dom_parent_lookup_after:
    "dom (parent_lookup (parents new_forest)) \<subseteq> Vs (abstract_forest new_forest)"
    using invar_basic_F(14)
    unfolding dom_parent_lookup_after_is Vs_after
    by (auto simp add: mu_in_F_verts mu_not_u)

  have dom_parent_and_origin:"dom (parent_lookup (parents new_forest)) =
    dom (origin_lookup (origins new_forest)) - vset_to_set (roots new_forest)"
  proof-
    have helper: "x \<in> vset_to_set rts \<Longrightarrow> x \<in> set p \<Longrightarrow> False" for x
      using invar_basic_F(10) no_ev_p by auto
    show ?thesis
      using  invar_basic_F(13) mu_not_u mu_props(1)
      by(auto intro: helper 
          simp add: dom_parent_lookup_after_is effect_of_expand_odd(5,9) if_split[of "\<lambda> x. x = _"])+
  qed

  have origin_lookup_roots:
    "origin_lookup (origins new_forest) `
    (vset_to_set (roots new_forest) \<union> Vs (abstract_forest new_forest)) =
    Some ` vset_to_set (roots new_forest)"
  proof(rule, goal_cases)
    case 1
    then show ?case 
      using invar_basic_F(6,7,10) no_ev_p assms(6,3) invar_basicD_here(15)
        Un_iff[of u "vset_to_set evs" "vset_to_set ods"] 
        image_eqI[of "origin_lookup orngs u" "origin_lookup orngs" u
          "vset_to_set evs \<union> vset_to_set ods"] 
      by(auto simp add: Vs_after effect_of_expand_odd(9) effect_of_expand_odd(5) invar_rootsD_here(1))
  next
    case 2
    show ?case
    proof(rule , goal_cases)
      case (1 x)
      then obtain xx where xx: "xx \<in> vset_to_set (roots new_forest)" "x = Some xx"
        by auto
      hence xx_root: "xx \<in> vset_to_set rts"
        by (simp add: effect_of_expand_odd(5))
      hence "origin_lookup orngs xx = x"
        by (simp add: invar_rootsD_here(1) xx(2))
      hence "origin_lookup (origins new_forest) xx = x"
        using xx_root invar_basic_F(13) pu(1) invar_basic_F(10) no_ev_p
        by(auto simp add: effect_of_expand_odd(9) xx(2))
      then show ?case 
        using xx(1) by blast
    qed
  qed

  have invar_basic_after: "invar_basic \<M>' new_forest"
  proof(rule invar_basicI[OF _ effect_of_expand_odd(1,2,3,4)], goal_cases)
    case 1
    then show ?case
      by (simp add: effect_of_expand_odd(5) invar_basic_F(1))
  next
    case 2
    then show ?case 
      using  invar_basic_F(6,7,10)  assms(3,6)
      by(auto simp add: effect_of_expand_odd(6,7) Vs_after effect_of_expand_odd(5) in_set_conv_nth)
  next
    case 3
    then show ?case 
      using invar_basic_F(7) no_ev_p ods_p
      by(auto simp add: effect_of_expand_odd(6,7) assms(7) nth_eq_iff_index_eq)
  next
    case 4
    then show ?case 
      by(auto simp add: effect_of_expand_odd(7) invar_basic_F(8))
  next
    case 5
    then show ?case 
      by(auto simp add: effect_of_expand_odd(6) invar_basic_F(9))
  next
    case 6
    then show ?case 
      using invar_basic_F(10)  effect_of_expand_odd(5)
      by(auto simp add: effect_of_expand_odd(7))
  next
    case 7
    then show ?case 
      using invar_basic_F(10,11) no_ev_p
      by(auto simp add: Vs_of_M'_are effect_of_expand_odd(5))
  next
    case 8
    have ods_gtr_1:"card (vset_to_set ods) \<ge> 1" 
      using assms(3) invar_basic_F(9) less_eq_Suc_le by fastforce
    have rw0a: "card {p ! i |i. i < length p \<and> even i} =
               card {i |i. i < length p \<and> even i}" 
      unfolding setcompr_eq_image
      by(subst card_image)
        (auto simp add: inj_on_def assms(7) nth_eq_iff_index_eq)
    hence card_evens_gtr_1:"card {p ! i |i. i < length p \<and> even i} \<ge> 1"
      using assms(5)
      by(auto simp add: card_of_even_numbers_upto[simplified])
    have rw0b: "card {p ! i |i. i < length p \<and> odd i} =
               card {i |i. i < length p \<and> odd i}" 
      unfolding setcompr_eq_image
      by(subst card_image)
        (auto simp add: inj_on_def assms(7) nth_eq_iff_index_eq)
    have rw1: "card (vset_to_set ods - {u} \<union> {p ! i |i. i < length p \<and> even i}) =
         card (vset_to_set ods - {u}) + card {p ! i |i. i < length p \<and> even i}"
      using ods_p 
      by(auto intro!: card_Un_disjoint simp add: invar_basic_F(9))
    have rw2: "card (vset_to_set ods - {u}) = card (vset_to_set ods) - 1"
      using assms(3) by auto
    have rw4: "card (vset_to_set evs \<union> {p ! i |i. i < length p \<and> odd i}) = 
               card (vset_to_set evs) + card {p ! i |i. i < length p \<and> odd i}"
      using no_ev_p 
      by(auto intro!: card_Un_disjoint simp add: invar_basic_F(8))
    have rw5: "card {p ! i |i. i < length p \<and> odd i} = card {p ! i |i. i < length p \<and> even i} - 1"
      by(auto simp add: card_of_even_numbers_upto rw0b rw0a assms(5)
          card_of_even_numbers_upto[simplified] card_of_odd_numbers_upto[simplified])
    show ?case 
      using ods_gtr_1 card_evens_gtr_1 invar_basic_F(12)
      by(auto simp add: effect_of_expand_odd(5,6,7) rw1 rw2 rw4 rw5)
  next
    case 9
    then show ?case 
      using dom_parent_and_origin by simp
  next
    case 10
    then show ?case 
      using dom_parent_lookup_after by simp
  next
    case 11
    then show ?case 
      using origin_lookup_roots by simp
  next
    case 12
    then show ?case
      using  invar_basic_F(16)
      by(auto simp add: Vs_after Vs_of_M'_are effect_of_expand_odd(5))
  next
    case 13
    then show ?case 
      using invar_basic_F(17)
      by(auto simp add: new_AF_is)
  next
    case 14
    thus ?case
      using effect_pc1 assms(7) effect_pc2
      by(auto intro!: dblton_graph_diff dblton_graph_union distinc_p_dblton_edges
            simp add: new_AF_is invar_basic_F(18) effect_pc3 the_other_neighb_of_odd_def)
  qed

  have Vs_of_inserted_path:
    " Vs (set (edges_of_path
               (the_other_neighb_of_odd (Forest rts evs ods prnts orngs) u # p @ [mu])))
      = set (the_other_neighb_of_odd (Forest rts evs ods prnts orngs) u # p @ [mu])"
    by(auto simp add: Vs_of_edges_of_path)

  have invar_matching_both_or_none_after:
    "invar_matching_both_or_none \<M>' new_forest"
  proof(rule invar_matching_both_or_noneI, goal_cases)
    case (1 u' v')
    then show ?case
      unfolding M'_def
    proof(elim UnE, goal_cases)
      case 1
      hence uv: "{u', v'} \<in> \<M>" "{u', v'} \<noteq> {u, mu}"
        by auto
      hence all_neq: "u' \<noteq> u" "v' \<noteq> u" "u' \<noteq> mu" "v' \<noteq> mu"
        using matching_edges_not_eqD[OF assms(2)] assms(4) by auto
      note uv2 = invar_matching_both_or_noneD_here[OF uv(1)]
      then show ?case 
      proof(elim disjE, goal_cases)
        case 1
        then show ?case
          using uv all_neq
          unfolding Vs_after new_AF_is effect_of_expand_odd(5)
            delta_of_odd[OF assms(1,3,4,2)]
          by (auto simp add: doubleton_eq_iff)
      next
        case 2
        then show ?case 
          unfolding Vs_after new_AF_is effect_of_expand_odd(5)
            delta_of_odd[OF assms(1,3,4,2)] vs_union Vs_of_inserted_path
          using u_pu_inF_verts(1,2) all_neq(3,4) "2" assms(6) edges_are_Vs_2[of u' v' \<M>]
            edges_are_Vs_2[of v' u' \<M>] uv(1) 
          by (auto simp add: vs_member pu(1) the_other_neighb_of_odd_def insert_commute)
      qed
    next
      case 2
      then show ?case 
        unfolding Vs_after new_AF_is effect_of_expand_odd(5)
          delta_of_odd[OF assms(1,3,4,2)] vs_union Vs_of_inserted_path
        by(auto intro!: set_mp[OF edges_of_path_append_subset, of _ _ "[_]", simplified] 
            simp add: edges_of_path_length)
    qed
  qed

  have invar_forest_even_and_odd_after:
    "invar_forest_even_and_odd new_forest"
  proof(rule invar_forest_even_and_oddI, goal_cases)
    case (1 u' v')
    then show ?case 
      unfolding new_AF_is 
    proof(elim UnE, goal_cases)
      case 1
      have helper: "v' \<in> vset_to_set ods"
        if "{v', p ! i} \<in> abstract_forest (Forest rts evs ods prnts orngs)"
          " \<And> nu. {v', p ! i} = {nu, u} \<Longrightarrow>
             {nu, u} \<notin> abstract_forest (Forest rts evs ods prnts orngs)"
          "i < length p"  for i
        using edges_are_Vs_2[of u' v' "abstract_forest (Forest rts evs ods prnts orngs)"]
          that invar_forest_even_and_oddD_here[OF that(1)] invar_basic_F(6,7) ods_p 1
        by (auto  simp add: doubleton_eq_iff)
      from 1 show ?case 
        using no_ev_p invar_basic_F(6,7)
          edges_are_Vs_2[of u' v' "abstract_forest (Forest rts evs ods prnts orngs)"]
        by (auto intro: helper 
            simp add: effect_of_expand_odd(7,6) invar_forest_even_and_oddD_here insert_commute)+
    next
      case 2
      hence "{u', v'} = {the_other_neighb_of_odd (Forest rts evs ods prnts orngs) u,  hd p}
        \<or> {u', v'} \<in> set (edges_of_path (p@[mu]))"
        using  p_neq_Nil  by (cases p) (auto simp add: doubleton_eq_iff)

      hence disj:"{u', v'} = {the_other_neighb_of_odd (Forest rts evs ods prnts orngs) u,  hd p}
        \<or> {u', v'} \<in> set (edges_of_path p) 
        \<or> {u', v'} = {last p, mu}"
        using  p_neq_Nil 
        by (all \<open>cases p rule: rev_cases\<close>)(auto simp add: doubleton_eq_iff edges_of_path_snoc_2)
      have case1: "(u' \<in> vset_to_set (evens new_forest)) = (v' \<in> vset_to_set (odds new_forest))"
        "(u' \<in> vset_to_set (odds new_forest)) = (v' \<in> vset_to_set (evens new_forest))"
        if "u' = the_other_neighb_of_odd (Forest rts evs ods prnts orngs) u" "v' = hd p" for u' v'
      proof-
        have "u' \<in> vset_to_set (evens new_forest)" 
          using that(1) other_neighb_u_even
          by(auto simp add:  effect_of_expand_odd(7))
        moreover have "v' \<in> vset_to_set (odds new_forest)"
          using hd_conv_nth p_neq_Nil that(2) 
          by(auto simp add:  effect_of_expand_odd(6)) 
        ultimately show 
          "(u' \<in> vset_to_set (evens new_forest)) = (v' \<in> vset_to_set (odds new_forest))"
          "(u' \<in> vset_to_set (odds new_forest)) = (v' \<in> vset_to_set (evens new_forest))"
          using  invar_basic_after 
          by (auto elim!: invar_basicE)
      qed
      have case2_pred: "{u', v'} \<in> set (edges_of_path p) 
           \<Longrightarrow> \<exists> i. Suc i < length p \<and> {p !i, p!Suc i} = {u', v'}"
        using p_neq_Nil  Suc_less_eq[of _ "length p - Suc 0"]
        by(auto simp add: edges_of_path_index in_set_conv_nth[of "{u', v'}" "edges_of_path p"] 
            edges_of_path_length )
      have case2: "(u' \<in> vset_to_set (evens new_forest)) = (v' \<in> vset_to_set (odds new_forest))
          \<and> (u' \<in> vset_to_set (odds new_forest)) = (v' \<in> vset_to_set (evens new_forest))"
        if asm: "Suc i < length p" "p !i = u'" "p!Suc i = v'" for i u' v'
      proof(cases "even i")
        case True
        have "u' \<notin> vset_to_set (evens new_forest)"
          "v' \<in> vset_to_set (evens new_forest)"
          using no_ev_p asm True assms(7) nth_eq_iff_index_eq
          by(fastforce simp add: effect_of_expand_odd(7))+
        moreover have "v' \<notin> vset_to_set (odds new_forest)"
          "u' \<in> vset_to_set (odds new_forest)"
          using ods_p that(1,3,2) True assms(7) distinct_conv_nth even_Suc 
          by(auto simp add: effect_of_expand_odd(6), force?)
        ultimately show ?thesis
          by simp
      next
        case False
        have "u' \<in> vset_to_set (evens new_forest)"
          "v' \<notin> vset_to_set (evens new_forest)"
          using no_ev_p asm False assms(7) nth_eq_iff_index_eq that(2)
          by(fastforce simp add: effect_of_expand_odd(7))+
        moreover have "v' \<in> vset_to_set (odds new_forest)"
          "u' \<notin> vset_to_set (odds new_forest)"
          using ods_p that(1,3,2) False assms(7) distinct_conv_nth even_Suc 
          by(auto simp add: effect_of_expand_odd(6) nth_eq_iff_index_eq)
        ultimately show ?thesis
          by simp
      qed
      have case3: "(u' \<in> vset_to_set (evens new_forest)) = (v' \<in> vset_to_set (odds new_forest))"
        "(u' \<in> vset_to_set (odds new_forest)) = (v' \<in> vset_to_set (evens new_forest))"
        if "u' = last p" "v' = mu" "{u', v'} \<in> abstract_forest new_forest" for u' v'
      proof-
        have a: "u' \<notin> vset_to_set (evens new_forest)" 
          using that(1) p_neq_Nil assms(5) lessI[of "length p - Suc 0"] no_ev_p 
          by(force simp add: effect_of_expand_odd(7) assms(7) nth_eq_iff_index_eq 
              dest!: last_conv_nth)
        moreover have b: "v' \<notin> vset_to_set (odds new_forest)"
          using that(2) mu_props(3) invar_basic_F(7) effect_pc2
          by(auto simp add: effect_of_expand_odd(6)) 
        ultimately show "(u' \<in> vset_to_set (evens new_forest)) = (v' \<in> vset_to_set (odds new_forest))"
          by auto
        thus  "(u' \<in> vset_to_set (odds new_forest)) = (v' \<in> vset_to_set (evens new_forest))"
          using a b invar_basic_after mu'(3) mu_is_mu' that(2,3) 1
          by(auto elim!: invar_basicE) blast+
      qed
      show ?thesis
        using disj case1[of u' v'] case1[of v' u'] case2[of _ u' v']  case2[of _ v' u'] 
          case3[of u' v'] case3[of v' u'] 1 
        by (auto dest!: case2_pred simp add: doubleton_eq_iff insert_commute)
    qed
  qed

  have rw1:"set (edges_of_vwalk
          (the_other_neighb_of_odd (Forest rts evs ods prnts orngs) u # p @ [mu])) =
          {(the_other_neighb_of_odd (Forest rts evs ods prnts orngs) u, hd p)}
            \<union> {(last p, mu)} \<union> set (edges_of_vwalk p)"
    using p_neq_Nil  
    by(cases p rule: list_cases_hd_and_last)
      (auto simp add: doubleton_eq_iff edges_of_vwalk_append_two_vertices[of "_#_", simplified])

  have invar_parent_wf_after: "invar_parent_wf new_forest"
  proof(rule invar_parent_wfI, unfold parent_spec_def, goal_cases)
    case 1
    show ?case
    proof(rule wf_squeeze_in[of "{(x, y) |x y. Some x = parent_lookup prnts y}" u p], goal_cases)
      case 1
      then show ?case 
        using invar_basicD_here(17)
        by(simp add: finite_abstract_Dabstract_forest Dabstract_forest_def)
    next
      case 2
      then show ?case 
        using invar_parent_wfD_here parent_specD by blast
    next
      case 3
      then show ?case 
        by (simp add: dVsI(2) pu(1))
    next
      case 4
      then show ?case 
        by(simp add: assms(7))
    next
      case 5
      then show ?case 
        by (simp add: p_neq_Nil)
    next
      case 6
      then show ?case
        unfolding sth_is_Dabstract_forest_old dVs_Vs_Dabstract_abstract_forest
        using assms(6) by blast
    next
      case 7
      have rw_helper:
        "{(x, y) |x y. Some x = parent_lookup (parents new_forest) y} = 
           {(x, y) . Some x = parent_lookup (parents new_forest) y}"
        by auto
      show ?case 
        unfolding Dabstract_forest_new_forest_is[simplified  Dabstract_forest_def, simplified]
          rw_helper Un_assoc
      proof(rule arg_cong2[where f = Set.union], goal_cases)
        case 2
        show ?case 
          unfolding rw1 Un_assoc
          by(auto simp add: the_other_neighb_of_odd_def gamma_minus_def pu(1)
              gamma_plus_def mu_props(1,4))
      qed simp
    qed
  qed

  have invar_even_to_parent_matching_after:
    "invar_even_to_parent_matching \<M>' new_forest"
  proof(rule invar_even_to_parent_matchingI, goal_cases)
    case (1 u' v')
    note one = this
    hence "(v', u') \<in> Dabstract_forest new_forest"
      by(auto simp add: Dabstract_forest_def)
    hence "parent_lookup prnts u' = Some v' \<and> u' \<notin> set p \<union> {u, mu}
        \<or> u' = hd p \<and> v' = the (parent_lookup prnts u) 
        \<or> (v', u') \<in> set (edges_of_vwalk p) 
        \<or> u' = mu \<and> v' = last p" 
      by(auto simp add: sth_is_Dabstract_forest_new 
          rw1[simplified the_other_neighb_of_odd_def alt_forest.sel])
    then show ?case 
    proof(elim disjE, goal_cases)
      case 1
      then show ?case
        using one(1)
        by(auto intro: invar_even_to_parent_matchingD_here 
            simp add: M'_def effect_of_expand_odd(7))
    next
      case 2
      then show ?case 
        using one(1) no_ev_p p_neq_Nil  effect_pc3 assms(5,7)
          distinct_conv_nth[of p] neq_Nil_conv[of p] 
        by(fastforce simp add: M'_def effect_of_expand_odd(7) doubleton_eq_iff pu(1) pu_not_u)
    next
      case 3
      then obtain i where i:"(edges_of_vwalk p) ! i = (v', u')" "i < length (edges_of_vwalk p)"
        by(auto simp add: in_set_conv_nth)
      hence i_props:"p ! i = v'" "p ! Suc i = u'" "u' \<in> set p" "v' \<in> set p"
        by(auto simp add: edges_of_vwalk_index edges_of_vwalk_length)
      hence even_i: "even i"
        using one(1) no_ev_p assms(5,7) i(2) 
          nth_eq_iff_index_eq[of p _ "Suc i"] 
        by(force simp add: effect_of_expand_odd(7) edges_of_vwalk_length)
      have Suc_i_unique:"\<And> j. \<lbrakk> p ! j = u'; j < length p\<rbrakk> \<Longrightarrow> j = Suc i"
        using assms(5,7) i edges_of_vwalk_length[of p]
          i_props nth_eq_iff_index_eq[of p _ "Suc i"] odd_Suc_minus_one[of "length p"]
        by auto
      have i_unique: "\<And> j. \<lbrakk> p ! j = v'; j < length p\<rbrakk> \<Longrightarrow> j =  i"
        using assms(7) i_props(1,3,4) distinct_Ex1[of p "p ! i"] 
          distinct_Ex1[of p "p ! _"] distinct_Ex1[of p u'] Suc_i_unique
        by fastforce
      show ?case
        using one(1) no_ev_p i i_props  effect_pc2  Suc_i_unique 
        by(auto simp add: M'_def effect_of_expand_odd(7) doubleton_eq_iff)
          (force simp add: edges_of_path_index insert_commute nth_append_left)
    next
      case 4
      hence "{u', v'} \<in> {edges_of_path (p @ [mu]) ! i |i. i < length p \<and> even i}"
        using p_neq_Nil assms(5) nth_append_length[of "edges_of_path p" "{v', mu}" "[]"]  
        by(cases p rule: rev_cases)
          (auto intro: exI[of _ "length p - 1"] 
            simp add: edges_of_path_snoc_2 edges_of_path_length)
      then show ?case 
        using one(1) by(simp add: M'_def)
    qed
  qed

  have invar_odd_to_parent_non_matching_after:
    "invar_odd_to_parent_non_matching \<M>' new_forest"
  proof(rule invar_odd_to_parent_non_matchingI, goal_cases)
    case (1 u')
    then show ?case 
      unfolding effect_of_expand_odd(6)
    proof(rule UnE, goal_cases)
      case 1
      then obtain v' where v': " parent_lookup prnts u' = Some v'" "{u', v'} \<notin> \<M>" "u' \<noteq> u"
        using  forest_invar_F(7)
        by(auto elim!: invar_odd_to_parent_non_matchingE)
      moreover hence u'_nin_p:"u' \<notin> set p \<union> {u, mu}" 
        using "1" invar_even_to_parent_matchingD_here[of u'] mu_props(3) ods_p 
        by auto
      have "parent_lookup (parents new_forest) u' = Some v'"
        apply(rule Collect2D(2)[of u' v'])
        using v'(1) u'_nin_p 
        by (unfold effect_of_expand_odd(8)) auto
      moreover have "{u', v'} \<notin> \<M>'"
      proof-
        have "\<lbrakk>i < length p; {u', v'} = edges_of_path (p @ [mu]) ! i; even i\<rbrakk> \<Longrightarrow> False" for i
          using u'_nin_p insertI1[of u' "{v'}"] edges_of_path_index[of _ "p @ [mu]"]
            nth_mem[of _ p] nth_mem[of "Suc _" "p @ [mu]"] nth_append_left[of _ p "[mu]"]
          by auto
        thus ?thesis
          by(auto dest: edges_of_path_index[of _ "p @ [mu]", simplified] 
              simp add: M'_def v'(2) doubleton_eq_iff)
      qed
      ultimately show ?case 
        by simp
    next
      case 2
      then obtain i where i: "u' = p ! i" "i < length p" "even i"
        by auto
      show ?case 
      proof(cases "i = 0")
        case True
        have "parent_lookup (parents new_forest) u' = Some (the (parent_lookup prnts u))"
          apply(rule Collect2D(2)[of u' "the _"])
          unfolding effect_of_expand_odd(8)
          using  p_neq_Nil by (cases p)(auto simp add: True i(1))
        moreover have "{u', the (parent_lookup prnts u)} \<notin> \<M>'" 
        proof-
          have "\<lbrakk>{u', the (parent_lookup prnts u)} \<in> \<M>; u' \<noteq> u\<rbrakk> \<Longrightarrow> u' = mu"
            using assms(6) i(1,2) by(force dest!: edges_are_Vs) 
          moreover hence
            "\<lbrakk>{u', the (parent_lookup prnts u)} \<in> \<M>; the (parent_lookup prnts u) \<noteq> u\<rbrakk> 
                \<Longrightarrow> the (parent_lookup prnts u) = mu"
            using effect_pc2 i(1,2)  pu(1,2) by fastforce
          moreover hence "\<lbrakk>{u', the (parent_lookup prnts u)} \<in> \<M>; u \<noteq> u'\<rbrakk>
                          \<Longrightarrow> u = the (parent_lookup prnts u)" 
            using effect_pc3 by fastforce
          moreover have "\<lbrakk>{u', the (parent_lookup prnts u)} \<in> \<M>; mu \<noteq> u'\<rbrakk>
                          \<Longrightarrow> mu = the (parent_lookup prnts u)"
            using calculation(2) pu(1) pu_not_u by auto
          moreover have helper: False if
            "i < length p" "{u', the (parent_lookup prnts u)} = edges_of_path (p @ [mu]) ! i"
            "even i" for i
            using that effect_pc1 effect_pc3 Suc_lessI[of i "length p"] nth_mem[of "Suc i" p]
            by (fastforce simp add: edges_of_path_index doubleton_eq_iff nth_append_left)+
          ultimately show ?thesis
            by(auto  simp add: M'_def)
        qed
        ultimately show ?thesis
          by auto
      next
        case False
        hence u'_edge_in_p:"(p ! (i - 1), u') \<in> set (edges_of_vwalk p)"
          using edges_of_vwalk_index[of "i-1" p, symmetric] i(2) 
          by(auto intro!: nth_mem simp add: i(1) edges_of_vwalk_length)
        have "parent_lookup (parents new_forest) u' = Some (p! (i-1))"
          apply(rule Collect2D(2)[of u' "p! (i-1)"])
          using u'_edge_in_p
          unfolding effect_of_expand_odd(8) rw1[simplified the_other_neighb_of_odd_def alt_forest.sel]
          by simp
        moreover have "{u', p ! (i - 1)} \<notin> \<M>'"
        proof-
          have pi1_neq_u': "p ! (i - 1) \<noteq> u'"
            using distinct_no_self_loop_in_edges_of_vwalk assms(7) u'_edge_in_p
            by blast
          hence "{u', p ! (i - Suc 0)} \<notin> \<M>"
            using edges_are_Vs_2[of "p ! (i - Suc 0)" u' \<M>]
              edges_are_Vs_2[of u' "p ! (i - Suc 0)" \<M>]
              v_in_edge_in_vwalk(2)[OF u'_edge_in_p] assms(6)
              nth_mem[of "i -1" p, OF less_imp_diff_less, OF i(2)]
            by(auto simp add: insert_commute)
          moreover have False if
            "ia < length p" "{u', p ! (i - Suc 0)} = edges_of_path (p @ [mu]) ! ia" "even ia" for ia
          proof-
            have " p ! (i - Suc 0) \<in> set p"
              by (simp add: i(2) less_imp_diff_less)
            thus ?thesis
              using that assms(7) i(1,2,3) effect_pc2 
                distinct_indexD[OF assms(7), of "i - Suc 0" "Suc i"]
                distinct_indexD[OF assms(7) i(2), of ia]  distinct_indexD[of p i "Suc ia"]
                less_imp_diff_less[of i "length p" "Suc 0", OF i(2)]   
              by (cases "Suc ia = length p")
                (auto simp add: edges_of_path_index doubleton_eq_iff  nth_append_left)
          qed 
          ultimately show ?thesis
            by(auto simp add: M'_def)
        qed
        ultimately show ?thesis 
          by simp
      qed
    qed
  qed

  have invar_odd_is_parent_after:
    "invar_odd_is_parent new_forest"
  proof(rule invar_odd_is_parentI, goal_cases)
    case (1 u')
    then show ?case 
      unfolding effect_of_expand_odd(6)
    proof(elim UnE, goal_cases)
      case 1
      then obtain v' where v': " parent_lookup prnts v' = Some u'"  "u' \<noteq> u"
        using  forest_invar_F(8)
        by(auto elim!: invar_odd_is_parentE)
      hence "v' \<in> vset_to_set evs" 
        using 1 assms(1,2)  odds_unique_child[OF assms(1) _ assms(2), of u'] by auto
      moreover hence "v' \<notin> set p \<union> {u, mu}"
        using assms(3) invar_basic_F(7) mu'(1) mu_is_mu' no_ev_p v'(1,2) by fastforce
      thus ?case 
        by (intro  exI[of _ v'])
          (auto intro!: Collect2D(2)[of v' u' 
              "\<lambda> x y.  parent_lookup (parents new_forest) x = Some y",
              simplified effect_of_expand_odd(8)] 
            simp add: v')
    next
      case 2
      then obtain i where i: "u' = p ! i" "i < length p" "even i"
        by auto
      show ?case 
      proof(cases "i = length p -1")
        case True
        have "parent_lookup (parents new_forest) mu = Some u'"
          apply(rule Collect2D(2)[of mu u'])
          unfolding effect_of_expand_odd(8)
          using p_neq_Nil 
          by (cases p rule: rev_cases)
            (auto simp add: True i(1) edges_of_vwalk_append_two_vertices[of "_ # _", simplified])
        then show ?thesis 
          by auto
      next
        case False
        hence u'_edge_in_p:"(u', p ! Suc i) \<in> set (edges_of_vwalk p)"
          using edges_of_vwalk_index[of i p, symmetric] i(2) 
          by(auto intro!: nth_mem simp add: i(1) edges_of_vwalk_length)
        have "parent_lookup (parents new_forest) (p ! Suc i) = Some u'"
          apply(rule Collect2D(2)[of "p ! Suc i" u'])
          using u'_edge_in_p
          unfolding effect_of_expand_odd(8) rw1[simplified the_other_neighb_of_odd_def alt_forest.sel]
          by simp
        then show ?thesis 
          by auto
      qed
    qed
  qed

  interpret parent_old: parent "parent_lookup prnts"
    by (simp add: invar_parent_wfD_here parent.intro)
  note old_follow_last_Cons = parent_old.follow_last_Cons[folded follow_def]

  interpret parent_here: parent "parent_lookup (parents new_forest)"
    by(auto intro!: follow_dom_invar_parent_wf(1) invar_parent_wf_after)
  have follow_induct_here:
    "(\<And>v. (\<And>x2. parent_lookup (parents new_forest) v = Some x2 \<Longrightarrow> P x2) \<Longrightarrow> P v) \<Longrightarrow>
        P a" for P a
    using parent_spec_i.follow.pinduct parent_here.follow_dom by metis
  note follow_simps_here = parent_spec.follow.psimps[OF parent_here.follow_dom, folded follow_def]
  note follow_new_last_Cons=parent_here.follow_last_Cons[folded follow_def]
  note follow_cons_3_new = parent_here.follow_cons_3[folded follow_def]

  have new_org_root: "v \<in> vset_to_set rts \<Longrightarrow> origin_lookup (origins new_forest) v = Some v" for v
    using invar_basic_F(10) invar_even_to_parent_matchingD_here pu(1,2) no_ev_p
    by(auto simp add: effect_of_expand_odd(9) invar_rootsD_here(1))

  have orgn_lookup_mu: "origin_lookup orngs mu = Some (the (origin_lookup orngs u))"
    using forest_invar_F(6) mu_in_F_verts mu_props(1) u_pu_inF_verts(1) 
    by(auto elim!:  invar_rootsE simp add:  old_follow_last_Cons)
  have orgn_lookup_pu:
    "Some (the (origin_lookup orngs u)) = origin_lookup orngs (the (parent_lookup prnts u))"
    using invar_rootsD_here(2) mu_in_F_verts mu_props(1)  orgn_lookup_mu pu(1) u_pu_inF_verts(2) 
    by (auto simp add: old_follow_last_Cons)

  have big_induction:
    "origin_lookup (origins new_forest) v =
        Some (last (follow (parent_lookup (parents new_forest)) v)) \<and>
    ( \<forall>u\<in>set (follow (parent_lookup (parents new_forest)) v).
           origin_lookup (origins new_forest) v = origin_lookup (origins new_forest) u) \<and>
    set (edges_of_path (follow (parent_lookup (parents new_forest)) v)) \<subseteq> abstract_forest new_forest"
    if "v\<in>vset_to_set (roots new_forest) \<union> Vs (abstract_forest new_forest)" for v
    using that
  proof(induction v rule: follow_induct_here)
    case (1 v)
    have tirple_conjD: "A \<and> B \<and> C \<Longrightarrow> A" "A \<and> B \<and> C \<Longrightarrow> B" "A \<and> B \<and> C \<Longrightarrow> C"
      for A B C 
      by auto
    note IH = tirple_conjD[OF 1(1)]
    note Iprem= 1(2)
    show ?case 
    proof(cases "parent_lookup (parents new_forest) v")
      case None
      then show ?thesis 
        using Iprem dom_parent_and_origin origin_lookup_roots
          imageI[of v "vset_to_set rts \<union> Vs (abstract_forest new_forest)"
            "origin_lookup (origins new_forest)"]
        by(auto simp add: follow_simps_here effect_of_expand_odd(5) intro!: new_org_root)
    next
      case (Some v')
      note parent_lookup_v_is = this
      hence v_v'_in_Vs_AF:"{v, v'} \<in> abstract_forest new_forest" 
        "{v, v'} \<subseteq> Vs (abstract_forest new_forest)"
        by(auto simp add: abstract_forest_def)
      have edges_of_follow:
        "edges_of_path (v # follow (parent_lookup (parents new_forest)) v') =
           {v, v'}#edges_of_path (follow (parent_lookup (parents new_forest)) v')"
        using follow_cons_3_new[of v'] by auto
      show ?thesis 
      proof(cases "v \<in> insert mu (set p)")
        case True
        then show ?thesis 
        proof(elim insertE, goal_cases)
          case 1
          have "parent_lookup (parents new_forest) v = Some (last p)" 
            apply(rule Collect2D(2)[of v "last p"])
            unfolding effect_of_expand_odd(8)
            using p_neq_Nil 1
            by (cases p rule: rev_cases)
              (auto simp add: True  edges_of_vwalk_append_two_vertices[of "_ # _", simplified])
          hence v'_is_last_p: "v' = last p" 
            by (simp add: parent_lookup_v_is)
          have same_org:"origin_lookup (origins new_forest) v =
              origin_lookup (origins new_forest) v'"
            using "1" mu_not_u effect_pc2 p_neq_Nil v'_is_last_p 
            by(auto simp add: effect_of_expand_odd(9) orgn_lookup_mu)
          show ?case
            using v_v'_in_Vs_AF
            unfolding follow_new_last_Cons[OF parent_lookup_v_is]
            by (auto intro!: IH[OF Some]
                simp add: follow_simps_here[of v]  same_org edges_of_follow parent_lookup_v_is)
        next
          case 2
          then obtain i where i: "p ! i = v" "i < length p" 
            by (auto simp add: in_set_conv_nth)
          show ?case
          proof(cases i)
            case 0
            have "parent_lookup (parents new_forest) v = Some (the (parent_lookup prnts u))" 
              apply(rule Collect2D(2)[of v "the _"])
              unfolding effect_of_expand_odd(8)
              using p_neq_Nil 1 2 0 invar_basic_F(10) no_ev_p i
              by (cases p) (auto simp add: effect_of_expand_odd(5))
            hence v'_is: "v' = the (parent_lookup prnts u)"
              by (simp add: parent_lookup_v_is)
            have same_org:"origin_lookup (origins new_forest) v =
              origin_lookup (origins new_forest) v'"
              using 2
              by(auto simp add: effect_of_expand_odd(9) v'_is orgn_lookup_pu pu(1) pu_not_u)
            show ?thesis 
              using v_v'_in_Vs_AF
              unfolding follow_new_last_Cons[OF parent_lookup_v_is]
              by (auto intro!: IH[OF Some]
                  simp add: follow_simps_here[of v]  same_org edges_of_follow parent_lookup_v_is)
          next
            case (Suc nat)
            have v'_v'_in_p:"(p ! nat, v) \<in> set (edges_of_vwalk p)" 
              using assms(6)  Suc i(1,2) edges_of_vwalk_length[of p]
                in_set_conv_nth[of "edges_of_vwalk p ! nat" "edges_of_vwalk p"] 
                edges_of_vwalk_index[of nat p]
              by auto
            have "parent_lookup (parents new_forest) v = Some (p ! nat)" 
              apply(rule Collect2D(2)[of v "_ ! _"])
              unfolding effect_of_expand_odd(8)
              using v'_v'_in_p edges_of_vwalk_prepend_one edges_of_vwalk_append_one 
              by (fastforce intro!:  simp add: effect_of_expand_odd(5))
            hence v'_is: "v' = p ! nat"
              by (simp add: parent_lookup_v_is)
            have same_org:"origin_lookup (origins new_forest) v =
              origin_lookup (origins new_forest) v'"
              using Suc Suc_lessD i(2) nth_mem 2
              by(auto simp add: effect_of_expand_odd(9) v'_is)
            show ?thesis 
              using v_v'_in_Vs_AF
              unfolding follow_new_last_Cons[OF parent_lookup_v_is]
              by (auto intro!: IH[OF Some]
                  simp add: follow_simps_here[of v]  same_org edges_of_follow parent_lookup_v_is)
          qed
        qed
      next
        case False
        note false = this
        have v_v_in_rel: "(v, v') \<in> {(x, y) |x y. parent_lookup (parents new_forest) x = Some y}"
          using Some by auto
        have v'_not_in_p:"v' \<notin> set p" 
        proof(rule ccontr, goal_cases)
          case 1
          note one = this
          then obtain i where i:"i < length p" "p! i = v'"
            by (auto simp add: in_set_conv_nth)
          have "(parent_lookup prnts v = Some v' \<and> v \<noteq> u)
                \<or> (v', v) \<in>  set (edges_of_vwalk (the (parent_lookup prnts u) # p @ [mu]))"
            using False v_v_in_rel
            unfolding  effect_of_expand_odd(8)
            by auto
          moreover have "\<lbrakk>parent_lookup prnts v = Some v'; v \<noteq> u\<rbrakk> \<Longrightarrow> False"
          proof(cases "v \<in> vset_to_set evs", goal_cases)
            case 1
            moreover hence "{v, v'} \<in> abstract_forest (Forest rts evs ods prnts orngs)"
              by(auto simp add: abstract_forest_def)
            ultimately have "v' \<in> vset_to_set ods" 
              using invar_forest_even_and_oddD_here by simp
            then show ?thesis 
              using "1"(1)  false mu_props(4) ods_p one by auto
          next
            case 2
            hence "v \<in> vset_to_set ods" 
              using invar_basic_F(14,6) by auto
            thus ?case
              using 1 2 invar_forest_even_and_oddD_here no_ev_p 
              by (fastforce simp add: abstract_forest_def)
          qed
          ultimately show False
            using False v_in_edge_in_vwalk'(2)[of v' v "the (parent_lookup prnts u) # p @ [mu]"]
            by auto
        qed
        have v'_is_mu_if_v_is_u: "v = u \<Longrightarrow> v' = mu" 
          using False Vs_after v_v'_in_Vs_AF(2) by fastforce

        have same_org:"origin_lookup (origins new_forest) v = origin_lookup (origins new_forest) v'"
        proof-
          have same1:"origin_lookup (origins new_forest) v = origin_lookup orngs v"
            using False assms(7) Vs_after v_v'_in_Vs_AF(2) 
            by(auto simp add:  effect_of_expand_odd(9))
          moreover have same2:"origin_lookup (origins new_forest) v' = origin_lookup orngs v'"
            using v'_not_in_p  Vs_after v_v'_in_Vs_AF(2) 
            by (auto simp add:  effect_of_expand_odd(9))
          moreover have "origin_lookup orngs v' = origin_lookup orngs v"
          proof(cases "v = u")
            case True
            then show ?thesis 
              by (simp add: invar_rootsD_here(2) orgn_lookup_mu u_pu_inF_verts(1) v'_is_mu_if_v_is_u)
          next
            case False
            note FALSE = this
            have "parent_lookup prnts v = Some v'"
            proof-
              have "parent_lookup prnts v = Some v'
                \<or> (v', v) \<in>  set (edges_of_vwalk (the (parent_lookup prnts u) # p @ [mu]))"
                using v_v_in_rel Some false FALSE
                unfolding  effect_of_expand_odd(8) by auto
              thus ?thesis
                using false v_in_edge_in_vwalk'(2) by fastforce
            qed
            moreover hence "{v, v'}\<subseteq> Vs (abstract_forest (Forest rts evs ods prnts orngs))"
              by(auto simp add: abstract_forest_def)
            ultimately show ?thesis
              using old_follow_last_Cons[of v v'] 
              by (auto simp add: invar_rootsD_here(2))
          qed
          ultimately show ?thesis
            by simp
        qed
        show ?thesis
          using v_v'_in_Vs_AF
          unfolding follow_new_last_Cons[OF parent_lookup_v_is]
          by (auto intro!: IH[OF Some]
              simp add: follow_simps_here[of v]  same_org edges_of_follow parent_lookup_v_is)
      qed
    qed
  qed


  have invar_roots_after: "invar_roots new_forest"
  proof(rule invar_rootsI, goal_cases)
    case (1 r)
    then show ?case
      using assms(3) invar_basic_F(10,7) no_ev_p
      by(auto simp add: effect_of_expand_odd(5) effect_of_expand_odd(9) invar_rootsD_here(1))
  next
    case (2 v)
    then show ?case 
      using big_induction by auto
  next
    case (3 v u)
    then show ?case 
      using big_induction by force
  next
    case (4 v)
    then show ?case 
      using big_induction by simp
  qed

  show "forest_invar \<M>' new_forest"
    by(intro forest_invarI 
        invar_basic_after invar_matching_both_or_none_after invar_forest_even_and_odd_after 
        invar_parent_wf_after invar_even_to_parent_matching_after
        invar_roots_after invar_odd_to_parent_non_matching_after invar_odd_is_parent_after)

  have distinct_p_mu: "distinct (p@[mu])"
    by (simp add: assms(7) effect_pc2)

  show ?th4
    unfolding M'_def
  proof(rule matching_vertex_disj_union, goal_cases)
    case 1
    then show ?case 
      using assms(2) matching_delete by blast
  next
    case 2
    then show ?case 
      using effect_pc2
      by(auto intro!: even_edges_of_distinct_path_are_matching[of "p@[mu]", simplified]
          simp add: assms(7))
  next
    case 3
    then show ?case 
      using assms(2,6,7)  mu_props(2)
      by(auto simp add: verts_of_even_edges[of "p@[mu]", simplified] remove_matching_edge_Vs)
  qed
qed

interpretation odd_expansion_spec_satisfied:
 alternating_forest_odd_expansion_spec
 where vset_invar = vset_invar
 and vset_to_set = vset_to_set
 and evens = evens
 and odds = odds
 and get_path = get_path
 and abstract_forest = abstract_forest
 and forest_invar = forest_invar
 and roots = roots
 and the_other_neighb_of_odd = the_other_neighb_of_odd
 and expand_odd = expand_odd
proof(goal_cases)
  case 1
  interpret af_spec_here: 
    alternating_forest_spec evens odds get_path abstract_forest forest_invar roots
     vset_invar vset_to_set
    using satisfied
    by(auto simp add: alternating_forest_ordinary_extension_spec_def)
  note  odd_expansion_precondE = af_spec_here.odd_expansion_precondE

  show ?case
  proof(rule alternating_forest_odd_expansion_spec.intro, goal_cases)
    case 1
    then show ?case 
      using af_spec_here.alternating_forest_spec_axioms by auto
  next
    case 2
    then show ?case 
proof(rule alternating_forest_odd_expansion_spec_axioms.intro, goal_cases)
  case (1 \<M> F u)
  then show ?case 
    using the_other_neighb_of_odd_correct1[of \<M>] 
    by (cases F) auto
next
  case (2 \<M> F u v)
  then show ?case 
    using delta_of_odd[of \<M>] 
    by (cases F) auto
next
  case (3 \<M> F u mu p)
  then show ?case 
    using expand_odd_correct
    by (cases F) (force elim!: odd_expansion_precondE)
next
  case (4 \<M> F u mu p)
  then show ?case 
    using expand_odd_correct
    by (cases F) (force elim!: odd_expansion_precondE)
next
  case (5 \<M> F u mu p)
  then show ?case 
    using expand_odd_correct
    by (cases F) (force elim!: odd_expansion_precondE)
next
  case (6 \<M> F u mu p)
  then show ?case 
    using expand_odd_correct
    by (cases F) (force elim!: odd_expansion_precondE)
next
  case (7 \<M> F u mu p)
  then show ?case 
    using expand_odd_correct
    by (cases F) (force elim!: odd_expansion_precondE)
next
  case (8 \<M> F u mu p)
  then show ?case 
    using expand_odd_correct
    by (cases F) (force elim!: odd_expansion_precondE)
qed
qed
qed

lemmas odd_expansion_spec_satisfied = 
  odd_expansion_spec_satisfied.alternating_forest_odd_expansion_spec_axioms

end

thm forest_manipulation.odd_expansion_spec_satisfied

end