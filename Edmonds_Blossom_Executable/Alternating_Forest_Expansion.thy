theory Alternating_Forest_Expansion
  imports Alternating_Forest_Contraction
begin                  

(*Note: not necessary for the current executable blossom,
    but it will be useful for a cubic version of weighted blossom
    where path search and blossom expansion are interwoven.*)

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
    and K::"'v set" +
  fixes the_other_neighb_of_odd:: "'forest \<Rightarrow> 'v \<Rightarrow> 'v"
    and expand_odd:: "'forest \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v list \<Rightarrow> 'forest"
  assumes the_other_neighb_of_odd_basis:
     "\<And> \<M> F u. \<lbrakk>forest_invar \<M> F; u \<in> vset_to_set (odds F)\<rbrakk> \<Longrightarrow> 
        {the_other_neighb_of_odd F u} = {v | v. {u, v} \<in> abstract_forest F \<and> {u, v} \<notin> \<M>}"
  and expand_odd_basis:
     "\<And> \<M> F u mu p. \<lbrakk>odd_expansion_precond \<M> F u mu p; set p \<subseteq> K\<rbrakk> \<Longrightarrow>
       forest_invar (\<M> - {{u, mu}} \<union> {edges_of_path (p@[mu]) ! i| i. i < length p \<and> even i })
                    (expand_odd F u mu p)"
     "\<And> \<M> F u mu p. \<lbrakk>odd_expansion_precond \<M> F u mu p; set p \<subseteq> K\<rbrakk> \<Longrightarrow> 
       abstract_forest (expand_odd F u mu p) = 
       abstract_forest F - {{u, nu} | nu. {u, nu} \<in> abstract_forest F}
            \<union> set (edges_of_path (the_other_neighb_of_odd F u #p@[mu]))"
     "\<And> \<M> F u mu p. \<lbrakk>odd_expansion_precond \<M> F u mu p; set p \<subseteq> K\<rbrakk> \<Longrightarrow> 
       vset_to_set (evens (expand_odd F u mu p)) =
       vset_to_set (evens F) \<union> {p ! i | i. i < length p \<and> odd i}"
     "\<And> \<M> F u mu p. \<lbrakk>odd_expansion_precond \<M> F u mu p; set p \<subseteq> K\<rbrakk> \<Longrightarrow> 
       roots (expand_odd F u mu p) = roots F"
begin

lemma the_other_neighb_of_odd:
     "\<And> \<M> F u. \<lbrakk>forest_invar \<M> F; u \<in> vset_to_set (odds F)\<rbrakk> \<Longrightarrow> 
        {the_other_neighb_of_odd F u} = {v | v. {u, v} \<in> abstract_forest F \<and> {u, v} \<notin> \<M>}"
     "\<And> \<M> F u v. \<lbrakk>forest_invar \<M> F; u \<in> vset_to_set (odds F); {u, v} \<in> \<M>; matching \<M>\<rbrakk> \<Longrightarrow> 
        {{u, nu} |nu. {u, nu} \<in> abstract_forest F} = {{u, the_other_neighb_of_odd F u}, {u, v}}"
proof (goal_cases)
  case (1 M F u)
  then show ?case by (rule the_other_neighb_of_odd_basis)
next
  case (2 M F u v)
  have "{u, v} \<in> abstract_forest F"
    using evens_and_odds_basis(4)[OF 2(1)] 2(2) higher_forest_properties(2)[OF 2(1,3)]
    by blast
  moreover have "{u, w} \<in> abstract_forest F \<and> {u, w} \<notin> M \<longleftrightarrow>
      w = the_other_neighb_of_odd F u" for w
    using the_other_neighb_of_odd_basis[OF 2(1,2)]
    by blast
  ultimately have "{u, w} \<in> abstract_forest F \<longleftrightarrow>
      w = the_other_neighb_of_odd F u \<or> w = v" for w
    using 2(3) doubleton_in_matching(1)[OF 2(4), of u w v]
    by blast
  then show ?case
    by auto
qed

lemma expand_odd:
     "\<And> \<M> F u mu p. \<lbrakk>odd_expansion_precond \<M> F u mu p; set p \<subseteq> K\<rbrakk> \<Longrightarrow>
       forest_invar (\<M> - {{u, mu}} \<union> {edges_of_path (p@[mu]) ! i| i. i < length p \<and> even i })
                    (expand_odd F u mu p)"
     "\<And> \<M> F u mu p. \<lbrakk>odd_expansion_precond \<M> F u mu p; set p \<subseteq> K\<rbrakk> \<Longrightarrow> 
       abstract_forest (expand_odd F u mu p) = 
       abstract_forest F - {{u, nu} | nu. {u, nu} \<in> abstract_forest F}
            \<union> set (edges_of_path (the_other_neighb_of_odd F u #p@[mu]))"
     "\<And> \<M> F u mu p. \<lbrakk>odd_expansion_precond \<M> F u mu p; set p \<subseteq> K\<rbrakk> \<Longrightarrow> 
       vset_to_set (odds (expand_odd F u mu p)) =
       vset_to_set (odds F) - {u} \<union> {p ! i | i. i < length p \<and> even i}"
     "\<And> \<M> F u mu p. \<lbrakk>odd_expansion_precond \<M> F u mu p; set p \<subseteq> K\<rbrakk> \<Longrightarrow> 
       vset_to_set (evens (expand_odd F u mu p)) =
       vset_to_set (evens F) \<union> {p ! i | i. i < length p \<and> odd i}"
     "\<And> \<M> F u mu p. \<lbrakk>odd_expansion_precond \<M> F u mu p; set p \<subseteq> K\<rbrakk> \<Longrightarrow> 
       roots (expand_odd F u mu p) = roots F"
     "\<And> \<M> F u mu p. \<lbrakk>odd_expansion_precond \<M> F u mu p; set p \<subseteq> K\<rbrakk> \<Longrightarrow> 
         matching (\<M> - {{u, mu}} \<union> {edges_of_path (p@[mu]) ! i| i. i < length p \<and> even i })"
proof (goal_cases)
  case (1 M F u mu p)
  then show ?case by (rule expand_odd_basis(1))
next
  case (2 M F u mu p)
  then show ?case by (rule expand_odd_basis(2))
next
  case (3 M F u mu p)
  let ?E = "vset_to_set (evens F)"
  let ?O = "vset_to_set (odds F)"
  let ?A = "abstract_forest F"
  let ?D = "{{u, w} |w. {u, w} \<in> ?A}"
  let ?PE = "{p ! i |i. i < length p \<and> even i}"
  let ?PO = "{p ! i |i. i < length p \<and> odd i}"
  have inv: "forest_invar M F" and odd: "u \<in> ?O"
    and edge: "{u, mu} \<in> M" and match: "matching M"
    and fresh: "set p \<inter> (Vs ?A \<union> vset_to_set (roots F) \<union> Vs M) \<subseteq> {u}"
    and distinct: "distinct p"
    using 3(1) by (auto elim!: odd_expansion_precondE)
  have incident_even: "w \<in> ?E" if "{u, w} \<in> ?A" for w
    using higher_forest_properties(3)[OF inv edge_commute[OF that]] odd by simp
  have "u \<in> Vs ?A"
    using evens_and_odds_basis(4)[OF inv] odd
    by blast
  hence "{u, mu} \<in> ?A"
    using higher_forest_properties(2)[OF inv edge]
    by blast
  hence endpoints: "mu \<in> ?E" "the_other_neighb_of_odd F u \<in> ?E"
    using incident_even the_other_neighb_of_odd(1)[OF inv odd]
    by blast+
  have "Vs ?D \<subseteq> insert u ?E"
    using incident_even
    by (auto simp: Vs_def)
  moreover have "u \<notin> Vs (?A - ?D)"
    using dblton[OF inv]
    by (auto simp: Vs_def insert_commute elim!: dblton_graphE)
  moreover have "Vs ?A \<subseteq> Vs (?A - ?D) \<union> Vs ?D"
    by (auto simp: Vs_def)
  moreover have "Vs (?A - ?D) \<subseteq> Vs ?A"
    by (rule Vs_subset, rule Diff_subset)
  ultimately have deleted: "Vs (?A - ?D) - ?E = ?O - {u}"
    unfolding odds_eq_Vs_minus_evens[OF inv] by auto
  have no_even: "?E \<inter> set p = {}"
    using fresh odd evens_and_odds(3,4)[OF inv] by blast
  have old_odd: "(?O - {u}) \<inter> set p = {}"
    using fresh evens_and_odds_basis(4)[OF inv] by blast
  have partition: "set p = ?PE \<union> ?PO"
    by (auto simp: in_set_conv_nth) blast
  have disjoint: "?PE \<inter> ?PO = {}"
    using distinct by (auto simp: nth_eq_iff_index_eq)
  have path_vertices: "Vs (set (edges_of_path (the_other_neighb_of_odd F u # p @ [mu]))) =
      {the_other_neighb_of_odd F u, mu} \<union> set p"
    using Vs_of_edges_of_path[of "the_other_neighb_of_odd F u # p @ [mu]"] by simp
  have "(?O - {u}) - ?PO = ?O - {u}"
    using old_odd by auto
  moreover have "set p - ?E - ?PO = ?PE"
    using no_even disjoint by (auto simp: partition)
  moreover have diff_union: "X - (Y \<union> Z) = X - Y - Z" for X Y Z by blast
  ultimately show ?case
    unfolding odds_eq_Vs_minus_evens[OF expand_odd_basis(1)[OF 3]]
      expand_odd_basis(2,3)[OF 3] vs_union path_vertices
    by (simp add: diff_union Un_Diff endpoints deleted)
next
  case (4 M F u mu p)
  then show ?case by (rule expand_odd_basis(3))
next
  case (5 M F u mu p)
  then show ?case by (rule expand_odd_basis(4))
next
  case (6 M F u mu p)
  have inv: "forest_invar M F" and match: "matching M"
    and odd: "u \<in> vset_to_set (odds F)" and edge: "{u, mu} \<in> M"
    and fresh: "set p \<inter> (Vs (abstract_forest F) \<union> vset_to_set (roots F) \<union> Vs M) \<subseteq> {u}"
    and distinct: "distinct p"
    using 6(1)
    by (auto elim!: odd_expansion_precondE)
  have "u \<in> Vs (abstract_forest F)"
    using evens_and_odds_basis(4)[OF inv] odd
    by blast
  hence "{u, mu} \<in> abstract_forest F"
    using higher_forest_properties(2)[OF inv edge]
    by blast
  hence "mu \<noteq> u"
    using dblton[OF inv]
    by auto
  hence "mu \<notin> set p"
    using fresh edges_are_Vs_2[OF edge]
    by blast
  hence "matching {edges_of_path (p @ [mu]) ! i |i. i < length p \<and> even i}"
    using even_edges_of_distinct_path_are_matching[of "p @ [mu]"] distinct
    by simp
  moreover have "Vs (M - {{u, mu}}) \<inter>
      Vs {edges_of_path (p @ [mu]) ! i |i. i < length p \<and> even i} = {}"
    using fresh
    by (auto simp: remove_matching_edge_Vs[OF match edge]
        verts_of_even_edges[of "p @ [mu]", simplified])
  ultimately show ?case
    using matching_delete[OF match]
    by (auto intro: matching_vertex_disj_union)
qed

end

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
        prnts' = foldl2 (\<lambda> par x y. parent_put y x par) (parent_delete u prnts)
               (the (parent_lookup prnts u)#p@[cu]);
        uorg = the (origin_lookup orngs u);
        orngs' = foldl (\<lambda> org x. origin_put x uorg org) (origin_delete u orngs) p
       in Forest rts evs' ods' prnts' orngs')"

definition "the_other_neighb_of_odd F u = the (parent_lookup (parents F) u)"

end

context 
  forest_manipulation
begin

lemma foldr2_parent_upd:
  assumes "parent_invar prnts" "length xs \<ge> 2" "distinct xs"
    "prnts' = foldr2 parent_put xs prnts"
    and bounds: "set xs \<subseteq> K"
  shows "parent_invar prnts'" (is ?th1)
    and  "{(x, y) | x y. parent_lookup prnts' x = Some y} =
     {(x, y) | x y. parent_lookup prnts x = Some y} -
     {(x, y) | x y. parent_lookup prnts x = Some y \<and> x \<in> set (butlast xs)}
     \<union> set (edges_of_vwalk xs)" (is ?th2)
proof-
  have "?th1 \<and> ?th2"
    using assms(3,4) bounds
  proof(induction arbitrary: prnts' rule: list_induct3_len_geq_2[OF assms(2)], goal_cases)
    case (1 x y prnts')
    then show ?case 
      using assms(1) nil
      by (auto intro!: parent_map.fixed_univ_map_upd_invar
          simp: parent_lookup_def parent_map.fixed_univ_map_upd split: if_splits)
  next
    case (2 x y xs prnts')
    note prnts'_def = 2(3)
    have distinct_here: "distinct (y # xs)"
      using 2(2) by auto
    note big_distinct = 2(2)
    have tail_bound: "set (y # xs) \<subseteq> K" using 2(4) by auto
    note IH = conjunct1[OF 2(1)[OF distinct_here _ tail_bound]]
      conjunct2[OF 2(1)[OF distinct_here _ tail_bound]]
    define prnts'' where "prnts'' = (foldr2 parent_put (y # xs) prnts)"
    note prnts'_def = 2(3)[simplified foldr2.simps o_apply prnts''_def[symmetric]]
    note IH' = IH[OF refl, simplified prnts''_def[symmetric]]
    have bounds: "x \<in> K" "y \<noteq> nil" using 2(4) nil by auto
    show ?case 
    proof(rule, goal_cases)
      case 1
      then show ?case 
        using IH'(1) bounds
        by(auto intro!: parent_map.fixed_univ_map_upd_invar 
            simp add: prnts'_def)
    next
      case 2
      have "{(x, y) |x y. parent_lookup prnts' x = Some y} = 
       {(x, y) |x y. parent_lookup prnts'' x = Some y} 
           - {(x, y) | y. parent_lookup prnts'' x = Some y} 
        \<union> {(x, y)}"
        using IH'(1) bounds
        by(auto simp add: prnts'_def parent_put_lookup if_split[of "\<lambda> x. x = Some _"])
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
    and bounds: "set p \<subseteq> K" "u \<in> K" "cu \<in> K"
      "the (parent_lookup prnts u) \<in> K" "origin_lookup orngs u \<noteq> None"
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
  have insert_list:
    "vset_invar (foldl (\<lambda>S x. vset_insert x S) S xs) \<and>
      vset_to_set (foldl (\<lambda>S x. vset_insert x S) S xs) = vset_to_set S \<union> set xs"
    if "vset_invar S" "set xs \<subseteq> K" for S xs
    using that
    by (induction xs arbitrary: S) (auto simp: vset.fixed_univ_set_insert)
  have bounds_even: "set (take_odds p) \<subseteq> K"
    and bounds_odd: "set (take_evens p) \<subseteq> K"
    using bounds(1) by (auto simp: take_odds_set take_evens_set)
  show "vset_invar (evens new_forest)" ?th3
    using insert_list[OF assms(1) bounds_even]
    by (simp_all add: new_forest_def expand_odd_def Let_def take_odds_set)
  show "vset_invar (odds new_forest)" ?th2
    using insert_list[OF vset.fixed_univ_set_delete(1)[OF assms(2)] bounds_odd]
    by (simp_all add: new_forest_def expand_odd_def Let_def take_evens_set
        vset.fixed_univ_set_delete assms(2))
  show ?th1
    by (simp add: new_forest_def expand_odd_def)
  define prnts' where "prnts' = foldl2 (\<lambda> par x y. parent_put y x par) (parent_delete u prnts)
               (the (parent_lookup prnts u)#p@[cu])"
  define upcu_rev where "upcu_rev = rev (the (parent_lookup prnts u)#p@[cu])"
  have upcu_rev_is: "rev (the (parent_lookup prnts u)#p@[cu]) = upcu_rev" "set (the (parent_lookup prnts u)#p@[cu]) = set upcu_rev"
    by(auto simp add: upcu_rev_def)
  have set_butlast_is:"set (butlast upcu_rev) = insert cu (set p)"
    by(auto simp add: upcu_rev_def)
  have invar_after_u_removal: "parent_invar (parent_delete u prnts)"
    by (simp add: assms(4) bounds(2) parent_map.fixed_univ_map_upd_invar)
  have upcu_rev_length: "2 \<le> length upcu_rev"
    by(auto simp add: upcu_rev_def)
  have upcu_rev_bound: "set upcu_rev \<subseteq> K"
    using bounds(1,3,4) by (auto simp: upcu_rev_def)
  have distinct_upcu_rev: "distinct upcu_rev"
    using p_well_formed by(auto simp add: upcu_rev_def)
  have parent_new_forest_are:"parents new_forest = prnts'"
    by(auto simp add: new_forest_def prnts'_def expand_odd_def)
  have edges_rev_is:"set (edges_of_vwalk upcu_rev) =
        prod.swap ` set (edges_of_vwalk (the (parent_lookup prnts u) # p @ [cu]))"
    unfolding upcu_rev_def edges_of_vwalk_rev 
    by simp
  show ?th4 "parent_invar (parents new_forest)"
    using assms(4) bounds(2) foldr2_parent_upd[OF invar_after_u_removal upcu_rev_length
        distinct_upcu_rev refl upcu_rev_bound]
    unfolding parent_new_forest_are prnts'_def foldl2_conv_foldr2 upcu_rev_is
      set_butlast_is edges_rev_is
    by (auto simp add: parent_delete_lookup if_split[of "\<lambda> x. x = Some _"])
  have put_list:
    "origin_invar (foldl (\<lambda>Q x. origin_put x v Q) Q xs) \<and>
      origin_lookup (foldl (\<lambda>Q x. origin_put x v Q) Q xs) =
        (\<lambda>x. if x \<in> set xs then Some v else origin_lookup Q x)"
    if "origin_invar Q" "set xs \<subseteq> K" "v \<noteq> nil" for Q xs v
    using that
    by (induction xs arbitrary: Q)
      (auto simp: origin_map.fixed_univ_map_upd_invar origin_put_lookup fun_eq_iff)
  have origin_not_nil: "the (origin_lookup orngs u) \<noteq> nil"
    using bounds(5) by (cases "origin_lookup orngs u") (auto dest: origin_lookup_not_nil)
  show "origin_invar (origins new_forest)" ?th5
    using put_list[OF origin_map.fixed_univ_map_upd_invar[OF assms(5) bounds(2)]
      bounds(1) origin_not_nil, of nil]
    by (auto simp: new_forest_def expand_odd_def Let_def
        origin_delete_lookup[OF assms(5) bounds(2)] fun_eq_iff)
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
proof -
  obtain w where "parent_lookup prnts w = Some u" "{u, w} \<in> \<M>"
    using odds_child[OF assms(1) _ assms(4)] assms(2) by auto
  hence "parent_lookup prnts v = Some u"
    using doubleton_in_matching(1)[OF assms(4) _ assms(3)] by simp
  hence matched_edge: "{u, v} \<in> abstract_forest (Forest rts evs ods prnts orngs)"
    by (auto simp: abstract_forest_def insert_commute)
  have nonmatching:
    "{u, w} \<in> abstract_forest (Forest rts evs ods prnts orngs) \<and> {u, w} \<notin> \<M>
      \<longleftrightarrow> w = the_other_neighb_of_odd (Forest rts evs ods prnts orngs) u" for w
    using the_other_neighb_of_odd_correct1(1)[OF assms(1,2)] by blast
  have "{u, w} \<in> abstract_forest (Forest rts evs ods prnts orngs) \<longleftrightarrow>
      w = the_other_neighb_of_odd (Forest rts evs ods prnts orngs) u \<or> w = v" for w
    using nonmatching[of w] matched_edge assms(3)
      doubleton_in_matching(1)[OF assms(4), of u w v]
    by blast
  thus ?thesis by auto
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
    and bounds: "set p \<subseteq> K"
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
    using the_other_neighb_of_odd_correct1(2)[OF assms(1,3)]
    by (simp add: the_other_neighb_of_odd_def pu(1))
  have u_pu_inF_verts: "u \<in> Vs (abstract_forest (Forest rts evs ods prnts orngs))"
    "pu \<in> Vs (abstract_forest (Forest rts evs ods prnts orngs))"
    using pu(1) by (auto simp: abstract_forest_def)
  hence pu_not_in_p: "pu \<notin> set p"
    using assms(6) pu_not_u by blast
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
    by (rule doubleton_in_matching(1)[OF assms(2) mu'(2) assms(4)])
  note mu_props = mu'[simplified mu_is_mu']
  have mu_in_F_verts: "mu \<in> Vs (abstract_forest (Forest rts evs ods prnts orngs))"
    using mu_props(1) by (auto simp: abstract_forest_def)
  have effect_pc1: "the (parent_lookup prnts u) \<notin> set p"
    by (simp add: pu(1) pu_not_in_p)
  have effect_pc2: "mu \<notin> set p"
    using assms(6) mu_in_F_verts mu_not_u by blast
  have effect_pc3: "mu \<noteq> the (parent_lookup prnts u)"
    using mu_props(2) pu(1,2) by fastforce
  have expansion_bounds: "u \<in> K" "mu \<in> K"
    "the (parent_lookup prnts u) \<in> K" "origin_lookup orngs u \<noteq> None"
    using assms(3) invar_basic_F(3,15,18) u_pu_inF_verts pu(1)
      forest_vertices_in_universe[OF assms(1)] edges_are_Vs_2[OF assms(4)]
    by auto
  note effect_of_expand_odd = 
    effect_of_expand_odd[OF invar_basicD_here(2,3,1,4,5) new_forest_def
      effect_pc1 effect_pc2 assms(7) effect_pc3 bounds expansion_bounds]

  show ?tha ?thb ?th3 
    using effect_of_expand_odd by auto

  have no_ev_p:"vset_to_set evs \<inter> set p = {}" 
    using  assms(6) invar_basic_F(6) invar_even_to_parent_matchingD_here pu
    by auto
  have ods_p: "vset_to_set ods \<inter> set p \<subseteq> {u}" 
    using assms(6) invar_basic_F(6) by auto
  have p_neq_Nil: "p \<noteq> []"
    using assms(5) by (cases p) simp_all
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

  have Vs_after: "Vs (abstract_forest new_forest) =
        Vs (abstract_forest (Forest rts evs ods prnts orngs)) - {u} \<union> set p"
  proof -
    let ?F = "abstract_forest (Forest rts evs ods prnts orngs)"
    let ?D = "{{u, nu} |nu. {u, nu} \<in> ?F}"
    have "u \<notin> Vs (?F - ?D)"
      by (auto simp: Vs_def abstract_forest_def doubleton_eq_iff)
    moreover have "Vs ?F = Vs (?F - ?D) \<union> {u, pu, mu}"
      unfolding delta_of_odd[OF assms(1,3,4,2)] the_other_neighb_of_odd_def
      using pu(1) mu_props(1)
      by (auto simp: Vs_def abstract_forest_def)
    ultimately show ?thesis
      using pu_not_u mu_not_u
      by (auto simp: new_AF_is vs_union Vs_of_edges_of_path
          the_other_neighb_of_odd_def pu(1))
  qed

  have Vs_of_M'_are:"Vs \<M>' = Vs \<M> - {u} \<union> set p"
    using mu_not_u assms(4,5)
    by (auto simp add: M'_def vs_union verts_of_even_edges[of "_ @[_]", simplified] 
        remove_matching_edges_Vs[OF assms(2)] Vs_of_edge)

  have incoming:
    "(\<exists>y. (y, x) \<in> set (edges_of_vwalk (a # xs))) \<longleftrightarrow> x \<in> set xs"
    for a xs x
    by (induction xs arbitrary: a) auto
  have new_parent:
    "parent_lookup (parents new_forest) x = Some y \<longleftrightarrow>
      parent_lookup prnts x = Some y \<and> x \<notin> set p \<union> {u, mu} \<or>
      (y, x) \<in> set (edges_of_vwalk (the (parent_lookup prnts u) # p @ [mu]))" for x y
    using effect_of_expand_odd(8) by auto
  have dom_parent_lookup_after_is:
    "dom (parent_lookup (parents new_forest)) = dom (parent_lookup prnts) -
      {u} \<union> set (p @[mu])"
    by (auto simp: dom_def new_parent ex_disj_distrib incoming)

  have dom_parent_lookup_after:
    "dom (parent_lookup (parents new_forest)) \<subseteq> Vs (abstract_forest new_forest)"
    using invar_basic_F(14)
    unfolding dom_parent_lookup_after_is Vs_after
    by (auto simp add: mu_in_F_verts mu_not_u)

  have dom_parent_and_origin:"dom (parent_lookup (parents new_forest)) =
    dom (origin_lookup (origins new_forest)) - vset_to_set (roots new_forest)"
  proof-
    have helper: "\<lbrakk>x \<in> vset_to_set rts; x \<in> set p\<rbrakk> \<Longrightarrow> False" for x
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
    show ?case
      using invar_basic_F(18) bounds by (auto simp: Vs_of_M'_are)
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
        by (cases p rule: rev_cases)(auto simp add: doubleton_eq_iff edges_of_path_snoc_2)
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
      proof-
        have "(u' \<in> vset_to_set (evens new_forest) \<and> v' \<in> vset_to_set (odds new_forest)) \<or>
          (u' \<in> vset_to_set (odds new_forest) \<and> v' \<in> vset_to_set (evens new_forest))"
          using asm
          by (cases "even i") (auto simp: effect_of_expand_odd(6,7))
        thus ?thesis
          using invar_basicD(7)[OF invar_basic_after]
          by blast
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
        using v'(1) u'_nin_p by (simp add: new_parent)
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
          using p_neq_Nil by (cases p) (auto simp: new_parent True i(1))
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
          using u'_edge_in_p
          by (simp add: new_parent rw1[simplified the_other_neighb_of_odd_def alt_forest.sel])
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
          using p_neq_Nil
          by (cases p rule: rev_cases)
            (auto simp: new_parent True i(1) edges_of_vwalk_append_two_vertices[of "_ # _", simplified])
        then show ?thesis 
          by auto
      next
        case False
        hence u'_edge_in_p:"(u', p ! Suc i) \<in> set (edges_of_vwalk p)"
          using edges_of_vwalk_index[of i p, symmetric] i(2) 
          by(auto intro!: nth_mem simp add: i(1) edges_of_vwalk_length)
        have "parent_lookup (parents new_forest) (p ! Suc i) = Some u'"
          using u'_edge_in_p
          by (simp add: new_parent rw1[simplified the_other_neighb_of_odd_def alt_forest.sel])
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

  have path_origin:
    "origin_lookup (origins new_forest) v = Some (the (origin_lookup orngs u))"
    if "v \<in> set (the (parent_lookup prnts u) # p @ [mu])" for v
    using that pu_not_u mu_not_u effect_pc2 orgn_lookup_mu orgn_lookup_pu
    by (auto simp: effect_of_expand_odd(9) pu(1))

  have parent_same_origin:
    "origin_lookup (origins new_forest) v = origin_lookup (origins new_forest) w"
    if "parent_lookup (parents new_forest) v = Some w" for v w
  proof -
    have "parent_lookup prnts v = Some w \<and> v \<notin> set p \<union> {u, mu} \<or>
      (w, v) \<in> set (edges_of_vwalk (the (parent_lookup prnts u) # p @ [mu]))"
      using that effect_of_expand_odd(8) by auto
    then show ?thesis
    proof
      assume old: "parent_lookup prnts v = Some w \<and> v \<notin> set p \<union> {u, mu}"
      hence vertices: "v \<in> Vs (abstract_forest (Forest rts evs ods prnts orngs))"
        "w \<in> Vs (abstract_forest (Forest rts evs ods prnts orngs))"
        by (auto simp: abstract_forest_def)
      have "w \<notin> set p" "w \<noteq> u"
        using old vertices(2) assms(6) mu_props(4) by auto
      thus ?thesis
        using old invar_rootsD_here(2)[of v] invar_rootsD_here(2)[of w] vertices
        by (simp add: effect_of_expand_odd(9) old_follow_last_Cons)
    next
      assume edge: "(w, v) \<in> set (edges_of_vwalk (the (parent_lookup prnts u) # p @ [mu]))"
      have "w \<in> set (the (parent_lookup prnts u) # p @ [mu])"
        "v \<in> set (the (parent_lookup prnts u) # p @ [mu])"
        using Vwalk.v_in_edge_in_vwalk[OF edge] by auto
      thus ?thesis by (simp add: path_origin)
    qed
  qed

  have big_induction:
    "origin_lookup (origins new_forest) v =
        Some (last (follow (parent_lookup (parents new_forest)) v)) \<and>
     (\<forall>u\<in>set (follow (parent_lookup (parents new_forest)) v).
        origin_lookup (origins new_forest) v = origin_lookup (origins new_forest) u) \<and>
     set (edges_of_path (follow (parent_lookup (parents new_forest)) v)) \<subseteq> abstract_forest new_forest"
    if "v \<in> vset_to_set (roots new_forest) \<union> Vs (abstract_forest new_forest)" for v
    using that
  proof (induction v rule: follow_induct_here)
    case (1 v)
    show ?case
    proof (cases "parent_lookup (parents new_forest) v")
      case None
      then show ?thesis
        using 1(2) dom_parent_and_origin origin_lookup_roots
          imageI[of v "vset_to_set rts \<union> Vs (abstract_forest new_forest)"
            "origin_lookup (origins new_forest)"]
        by (auto simp: follow_simps_here effect_of_expand_odd(5) intro!: new_org_root)
    next
      case (Some w)
      hence edge: "{v, w} \<in> abstract_forest new_forest"
        by (auto simp: abstract_forest_def)
      hence "w \<in> vset_to_set (roots new_forest) \<union> Vs (abstract_forest new_forest)"
        by auto
      note IH = 1(1)[OF Some this]
      have "edges_of_path (v # follow (parent_lookup (parents new_forest)) w) =
        {v, w} # edges_of_path (follow (parent_lookup (parents new_forest)) w)"
        using follow_cons_3_new[of w] by auto
      thus ?thesis
        using IH edge parent_same_origin[OF Some]
        by (auto simp: follow_new_last_Cons[OF Some] follow_simps_here[of v] Some)
    qed
  qed

  have invar_roots_after: "invar_roots new_forest"
    using big_induction new_org_root
    by (intro invar_rootsI) (fastforce simp: effect_of_expand_odd(5))+

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
      using assms(2) by (rule matching_delete)
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
 and K = K
 and the_other_neighb_of_odd = the_other_neighb_of_odd
 and expand_odd = expand_odd
proof(goal_cases)
  case 1
  interpret af_spec_here:
    alternating_forest_spec evens odds get_path abstract_forest forest_invar roots
      vset_invar vset_to_set
    using satisified
    by (auto simp: alternating_forest_ordinary_extension_spec_def)
  show ?case
  proof (rule alternating_forest_odd_expansion_spec.intro[OF af_spec_here.alternating_forest_spec_axioms],
      rule alternating_forest_odd_expansion_spec_axioms.intro, goal_cases)
    case (1 \<M> F u)
    then show ?case
      using the_other_neighb_of_odd_correct1(1)[of \<M>]
      by (cases F) auto
  next
    case (2 \<M> F u mu p)
    then show ?case
      using expand_odd_correct(1)
      by (cases F) (force elim!: af_spec_here.odd_expansion_precondE)
  next
    case (3 \<M> F u mu p)
    then show ?case
      using expand_odd_correct(2)
      by (cases F) (force elim!: af_spec_here.odd_expansion_precondE)
  next
    case (4 \<M> F u mu p)
    then show ?case
      using expand_odd_correct(4)
      by (cases F) (force elim!: af_spec_here.odd_expansion_precondE)
  next
    case (5 \<M> F u mu p)
    then show ?case
      using expand_odd_correct(5)
      by (cases F) (force elim!: af_spec_here.odd_expansion_precondE)
  qed
qed

lemmas odd_expansion_spec_satisfied = 
  odd_expansion_spec_satisfied.alternating_forest_odd_expansion_spec_axioms

end

thm forest_manipulation.odd_expansion_spec_satisfied

end