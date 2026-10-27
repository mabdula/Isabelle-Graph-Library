theory Alternating_Forest_Contraction
  imports Basic_Matching.Alternating_Forest_Executable
    Graph_Quotient
begin

(*TODO MOVE*)

lemma exI2: "P x y \<Longrightarrow> \<exists> x y. P x y"
  by auto

locale alternating_forest_fork_contraction_spec = 
alternating_forest_spec evens odds get_path abstract_forest forest_invar roots
    for evens::"'forest \<Rightarrow> 'vset"
    and odds::"'forest \<Rightarrow> 'vset"
    and get_path::"'forest \<Rightarrow> 'v \<Rightarrow> 'v list"
    and abstract_forest::"'forest \<Rightarrow> 'v set set"
    and forest_invar::"'v set set \<Rightarrow> 'forest \<Rightarrow> bool"
    and roots::"'forest \<Rightarrow> 'vset"
    and vset_empty::'vset +
  fixes contract_fork::"'forest \<Rightarrow> 'v list \<Rightarrow> 'v list \<Rightarrow> 'v \<Rightarrow> 'forest" 
  assumes 
  contract_fork_spec:
   "\<And>\<M> F v v' B1 B2 u new_vert P contr.
     contract_fork_precond \<M> F v v' B1 B2 u new_vert P contr \<Longrightarrow>
     forest_invar (quot_graph contr \<M> - {{new_vert}})
                  (contract_fork F (B1@[u]) (B2@[u]) new_vert)"
   "\<And>\<M> F v v' B1 B2 u new_vert P contr.
     contract_fork_precond \<M> F v v' B1 B2 u new_vert P contr \<Longrightarrow>
     abstract_forest (contract_fork F (B1@[u]) (B2@[u]) new_vert) 
     = quot_graph contr (abstract_forest F) - {{new_vert}}"
   "\<And>\<M> F v v' B1 B2 u new_vert P contr.
     contract_fork_precond \<M> F v v' B1 B2 u new_vert P contr \<Longrightarrow>
     vset_to_set (odds (contract_fork F (B1@[u]) (B2@[u]) new_vert)) 
     = vset_to_set (odds F) - ({u} \<union> set B1 \<union> set B2)"
   "\<And>\<M> F v v' B1 B2 u new_vert P contr.
     contract_fork_precond \<M> F v v' B1 B2 u new_vert P contr \<Longrightarrow>
      vset_to_set (evens (contract_fork F (B1@[u]) (B2@[u]) new_vert)) 
    = vset_to_set (evens F) - ({u} \<union> set B1 \<union> set B2) \<union> {new_vert}"
   "\<And>\<M> F v v' B1 B2 u new_vert P contr.
     contract_fork_precond \<M> F v v' B1 B2 u new_vert P contr \<Longrightarrow>
     vset_to_set (roots (contract_fork F (B1@[u]) (B2@[u]) new_vert)) =
    (if u \<in> vset_to_set (roots F) then vset_to_set (roots F) - {u} \<union> {new_vert} 
     else vset_to_set (roots F))"
   "\<And>\<M> F v v' B1 B2 u new_vert P contr.
     contract_fork_precond \<M> F v v' B1 B2 u new_vert P contr \<Longrightarrow>
     matching (quot_graph contr \<M> - {{new_vert}})"

locale forest_contract_manipulation_spec=
  forest_manipulation_spec 
  where vset_insert = vset_insert
    and parent_empty = parent_empty
    and origin_empty = origin_empty
  for vset_insert::"'v \<Rightarrow> 'vset \<Rightarrow> 'vset"
    and parent_empty ::'parent
    and origin_empty::'origin + 
  fixes vset_iterate_parent :: "('parent \<Rightarrow> 'v \<Rightarrow> 'parent) \<Rightarrow> 'parent \<Rightarrow> 'vset \<Rightarrow> 'parent"
    and vset_union::"'vset \<Rightarrow> 'vset \<Rightarrow> 'vset"
begin

definition "vset_from_list xs = foldl (\<lambda> S x. vset_insert x S) vset_empty xs"

definition 
  "contract_path (F::('vset, 'vset, 'vset, 'parent, 'origin) alt_forest) p new_vert =
   (let prnts = parents F;
        rts = roots F;
        evs = evens F;
        ods = odds F;
        orngs = origins F;
        evs_in_p = take_evens p;
        ods_in_p = take_odds p;
        evs_in_p_set = vset_from_list evs_in_p;
        ods_new = foldl (\<lambda> S x. vset_delete x S) ods ods_in_p;
        evs_new' = foldl (\<lambda> S x. vset_delete x S) evs evs_in_p;
        prnts_wthout_p = foldl (\<lambda> x pmap. parent_delete pmap x) prnts p;
        prnts_new_connected = 
            vset_iterate_parent 
               (\<lambda> cprnts x. if vset_isin evs_in_p_set (the (parent_lookup cprnts x)) 
                            then parent_upd x new_vert cprnts
                            else cprnts)
                prnts_wthout_p ods_new;
        new_prnts = (case parent_lookup prnts (last p)
                     of None \<Rightarrow> prnts_new_connected 
                     | Some xpred \<Rightarrow> parent_upd new_vert xpred prnts_new_connected);
        orns_wthout_p = foldl (\<lambda> x omap. origin_delete omap x) orngs p;
        old_orgn = the (origin_lookup orngs (last p));
        new_orgns = (if old_orgn \<noteq> (last p)
                     then origin_upd new_vert old_orgn orns_wthout_p
                     else origin_upd new_vert new_vert (vset_iterate_origin 
                           (\<lambda> org x. if the (origin_lookup org x) = old_orgn
                                     then origin_upd x new_vert org
                                     else org) orns_wthout_p 
                          (vset_union ods_new evs_new')))
      in Forest (if vset_isin rts (last p) 
                 then vset_insert new_vert (vset_delete (last p) rts) 
                 else rts )

                 (vset_insert new_vert (foldl (\<lambda> S x. vset_delete x S) evs evs_in_p))

                 ods_new
                 
                 new_prnts 
 
                 new_orgns)"

definition 
  "contract_fork (F::('vset, 'vset, 'vset, 'parent, 'origin) alt_forest) B1 B2 new_vert =
   contract_path (contract_path F B1 (last B1)) B2  new_vert"

end

locale forest_contract_manipulation
  = forest_contract_manipulation_spec
  where vset_insert = vset_insert
    and parent_empty = parent_empty
    and origin_empty = origin_empty
    + forest_manipulation
  where vset_insert = vset_insert
    and parent_empty = parent_empty
    and origin_empty = origin_empty
  for vset_insert::"'v \<Rightarrow> 'vset \<Rightarrow> 'vset"
    and parent_empty ::'parent
    and origin_empty::'origin + 
  assumes vset_iterate_parent:
    "\<And> V f init. vset_invar V \<Longrightarrow> 
          \<exists> vs. vset_to_set V = set vs \<and> distinct vs \<and>
            vset_iterate_parent f init V = foldl f init vs"
    and vset_union:
    "\<And> S T. \<lbrakk>vset_invar S; vset_invar T\<rbrakk> \<Longrightarrow> vset_invar (vset_union S T)"
    "\<And> S T. \<lbrakk>vset_invar S; vset_invar T\<rbrakk> 
       \<Longrightarrow> vset_to_set (vset_union S T) = vset_to_set S \<union> vset_to_set T"
begin

lemma vset_from_list:
  "vset_invar (vset_from_list xs)"
  "vset_to_set (vset_from_list xs) = set xs"
proof-
  define xs' where "xs' = rev xs"
  have set_same: "set xs = set xs'"
    by(simp add: xs'_def)
  have  "vset_invar (vset_from_list xs) \<and>
        vset_to_set (vset_from_list xs) = set xs"
    unfolding vset_from_list_def foldl_conv_foldr xs'_def[symmetric] set_same
    by(induction xs')
      (auto simp add: vset.invar_empty vset.set_empty vset.invar_insert vset.set_insert)
  thus "vset_invar (vset_from_list xs)"
    "vset_to_set (vset_from_list xs) = set xs"
    by auto
qed
  
lemma effect_of_contract_path:
  assumes "vset_invar evs" "vset_invar ods" 
    "vset_invar rts" "parent_invar prnts" "origin_invar orngs"
    and new_forest_def:
    "new_forest = contract_path (Forest rts evs ods prnts orngs) p new_vert"
  shows   "vset_invar (roots new_forest)"
    "vset_invar (evens new_forest)"
    "vset_invar (odds new_forest)"
    "parent_invar (parents new_forest)"
    "origin_invar (origins new_forest)"
    and 
    "vset_to_set (roots new_forest) =
  (if (last p) \<in> vset_to_set rts then vset_to_set rts - {last p} \<union> {new_vert}
         else vset_to_set rts)" (is ?th1)
    and "vset_to_set (odds new_forest) =
     vset_to_set ods - {p ! i | i. i < length p \<and> odd i}" (is ?th2)
    and "vset_to_set (evens new_forest) =
     vset_to_set evs - {p ! i | i. i < length p \<and> even i} \<union> {new_vert}" (is ?th3)
    and "parent_lookup (parents new_forest) = 
    (\<lambda>x. if x = new_vert \<and> parent_lookup prnts (last p) \<noteq> None 
           then parent_lookup prnts (last p)
      else if (x \<in> set p \<longrightarrow>
               the None \<in> {p ! i |i. i < length p \<and> even i} \<and>
               x \<in> vset_to_set ods - {p ! i |i. i < length p \<and> odd i}) \<and>
              (x \<notin> set p \<longrightarrow>
               the (parent_lookup prnts x) \<in> {p ! i |i. i < length p \<and> even i} \<and>
               x \<in> vset_to_set ods - {p ! i |i. i < length p \<and> odd i})
           then Some new_vert else if x \<in> set p then None else parent_lookup prnts x)" (is ?th4)
    and "origin_lookup (origins new_forest) =
    (\<lambda> x. if x = new_vert \<and> the (origin_lookup orngs (last p)) \<noteq> last p 
                then Some (the (origin_lookup orngs (last p)))
          else if x \<in> set p \<and> the (origin_lookup orngs (last p)) \<noteq> last p then None
          else if the (origin_lookup orngs (last p)) \<noteq> last p then origin_lookup orngs x
          else if x = new_vert then Some new_vert
          else if x \<in> vset_to_set ods - {p ! i |i. i < length p \<and> odd i} \<union>
                            (vset_to_set evs - {p ! i |i. i < length p \<and> even i}) \<and>
                       the (if x \<in> set p then None else origin_lookup orngs x) =
                       the (origin_lookup orngs (last p))
               then Some new_vert
          else if x \<in> set p then None 
          else origin_lookup orngs x)" (is ?th5)
proof-
  define evs_in_p where "evs_in_p = take_evens p"
  define ods_in_p where "ods_in_p = take_odds p"
  define evs_in_p_set where "evs_in_p_set = vset_from_list evs_in_p"
  define ods_new where "ods_new = foldl (\<lambda> S x. vset_delete x S) ods ods_in_p"
  define evs_new' where "evs_new' = foldl (\<lambda> S x. vset_delete x S) evs evs_in_p"
  define prnts_wthout_p where 
    "prnts_wthout_p = foldl (\<lambda> x pmap. parent_delete pmap x) prnts p"
  define prnts_new_connected where "prnts_new_connected = 
            vset_iterate_parent 
               (\<lambda> cprnts x. if vset_isin evs_in_p_set (the (parent_lookup cprnts x)) 
                            then parent_upd x new_vert cprnts
                            else cprnts)
                prnts_wthout_p ods_new"
  define new_prnts where "new_prnts = (case parent_lookup prnts (last p)
                     of None \<Rightarrow> prnts_new_connected 
                     | Some xpred \<Rightarrow> parent_upd new_vert xpred prnts_new_connected)"
  define orns_wthout_p where  
    "orns_wthout_p = foldl (\<lambda> x omap. origin_delete omap x) orngs p"
  define old_orgn where "old_orgn = the (origin_lookup orngs (last p))"
  define new_orgns where "new_orgns = (if old_orgn \<noteq> (last p)
                     then origin_upd new_vert old_orgn orns_wthout_p
                     else origin_upd new_vert new_vert (vset_iterate_origin 
                           (\<lambda> org x. if the (origin_lookup org x) = old_orgn
                                     then origin_upd x new_vert org
                                     else org) orns_wthout_p 
                          (vset_union ods_new evs_new')))"
  define new_roots where "new_roots = (if vset_isin rts (last p) 
                 then vset_insert new_vert (vset_delete (last p) rts) 
                 else rts)"
  define evs_new where "evs_new = vset_insert new_vert (foldl (\<lambda> S x. vset_delete x S) evs evs_in_p)"

  have news: "roots new_forest = new_roots"
    "evens new_forest = evs_new"
    "odds new_forest = ods_new"
    "origins new_forest = new_orgns"
    "parents new_forest = new_prnts"
    by (auto simp add: new_roots_def evs_new_def evs_in_p_def ods_new_def ods_in_p_def
        new_orgns_def old_orgn_def orns_wthout_p_def evs_new'_def new_prnts_def
        prnts_new_connected_def new_forest_def contract_path_def Let_def
        evs_in_p_set_def prnts_wthout_p_def 
        split: option.split)

  have new_roots_props:
    "vset_invar new_roots"
    "vset_to_set new_roots = 
        (if (last p) \<in> vset_to_set rts then vset_to_set rts - {last p} \<union> {new_vert}
         else vset_to_set rts)"
    by(auto simp add: new_roots_def assms 
        intro!: vset.invar_insert vset.invar_delete 
        | subst (asm) vset.set_insert vset.set_delete vset.set_isin
        | subst vset.set_insert vset.set_delete)+
  define ods_in_p_rev where "ods_in_p_rev = rev ods_in_p"
  have ods_in_p_rev_same_set: "set ods_in_p = set ods_in_p_rev"
    by(auto simp add: ods_in_p_rev_def)
  have ods_new_props: 
    "vset_invar ods_new"
    "vset_to_set ods_new = vset_to_set ods - set ods_in_p"
    unfolding ods_new_def foldl_conv_foldr ods_in_p_rev_def[symmetric]
      ods_in_p_rev_same_set
    by(induction ods_in_p_rev)
      (auto intro!:  vset.invar_delete simp add: vset.set_delete assms)
  have set_ods_in_p_is: "set ods_in_p = {p ! i | i. i < length p \<and> odd i}"
    by (simp add: ods_in_p_def take_odds_set)
  define evs_in_p_rev where "evs_in_p_rev = rev evs_in_p"
  have evs_in_p_rev_same_set: "set evs_in_p = set evs_in_p_rev"
    by(auto simp add: evs_in_p_rev_def)
  have helper1:"vset_invar res" "vset_to_set res = vset_to_set evs - set evs_in_p"
    if "res = foldl (\<lambda>S x. vset_delete x S) evs evs_in_p" for res
    using that
    unfolding foldl_conv_foldr evs_in_p_rev_def[symmetric] evs_in_p_rev_same_set
    by(induction evs_in_p_rev arbitrary: res)
      (auto intro!:  vset.invar_delete simp add: vset.set_delete assms)
  hence evs_new_props: "vset_invar evs_new"
    "vset_to_set evs_new = vset_to_set evs - set evs_in_p \<union> {new_vert}"
    by(auto simp add: vset evs_new_def)
  have set_evs_in_p_is: "set evs_in_p = {p ! i | i. i < length p \<and> even i}"
    by (simp add: evs_in_p_def take_evens_set)
  define rev_p where "rev_p = rev p"
  have rev_same_set: "set p = set rev_p"
    by(auto simp add: rev_p_def)
  have prnts_wthout_p_props:
    "parent_invar prnts_wthout_p"
    "parent_lookup (prnts_wthout_p) = 
      (\<lambda> x. if x \<in> set p then None else parent_lookup prnts x)"
    unfolding prnts_wthout_p_def foldl_conv_foldr rev_p_def[symmetric] rev_same_set
    by(induction rev_p)
      (auto simp add: parent_map.map_delete parent_map.invar_delete assms)
  define f1 where "f1 = (\<lambda>cprnts x.
           if vset_isin evs_in_p_set (the (parent_lookup cprnts x))
           then parent_upd x new_vert cprnts else cprnts)"
  obtain vs1 where vs1: "vset_to_set ods_new = set vs1"  "distinct vs1"
    "vset_iterate_parent f1 prnts_wthout_p ods_new = foldl f1 prnts_wthout_p vs1"
    using vset_iterate_parent[OF ods_new_props(1), of f1 prnts_wthout_p] by auto
  define vs1_rev where "vs1_rev = rev vs1"
  have vs1_rev_set: "set vs1 = set vs1_rev"
    by(auto simp add: vs1_rev_def)
  have evs_in_p_set: "vset_invar evs_in_p_set"
    by (simp add: evs_in_p_set_def vset_from_list(1))
  have prnts_new_connected_props:
    "parent_invar prnts_new_connected"
    "parent_lookup prnts_new_connected =
       (\<lambda> x. if the (parent_lookup prnts_wthout_p x) \<in> vset_to_set evs_in_p_set
                \<and> x \<in> vset_to_set ods_new
        then Some new_vert else parent_lookup prnts_wthout_p x)"
    unfolding prnts_new_connected_def vs1(3)[simplified f1_def]
      foldl_conv_foldr vs1(1) vs1_rev_set vs1_rev_def[symmetric]
  proof(induction vs1_rev, goal_cases)
    case (4 a vs1_rev)
    note 1 = this
    show ?case
      apply(subst foldr.foldr_Cons, subst o_apply)
      apply(subst 1(2))
      apply(subst (4) if_distrib)
      apply(subst parent_map.map_update)
      subgoal
        using 1(1) by simp
      apply(subst 1(2))+
      by(auto simp add:  vset.set_isin[OF evs_in_p_set])
  qed (auto intro!: parent_map.invar_update simp add: prnts_wthout_p_props(1))
  have evs_in_p_set: "vset_to_set evs_in_p_set = set evs_in_p"
    by (simp add: evs_in_p_set_def vset_from_list(2))
  have new_prnts_props:
    "parent_invar new_prnts"
    "parent_lookup (new_prnts) = 
       (\<lambda> x. if x = new_vert \<and> parent_lookup prnts (last p) \<noteq> None 
           then parent_lookup prnts (last p) 
           else if (x \<in> set p \<longrightarrow> the None \<in> set evs_in_p \<and> x \<in> vset_to_set ods_new) \<and>
             (x \<notin> set p \<longrightarrow>
              the (parent_lookup prnts x) \<in> set evs_in_p \<and> x \<in> vset_to_set ods_new)
          then Some new_vert else if x \<in> set p then None else parent_lookup prnts x)"
    unfolding new_prnts_def option.case_distrib parent_map.map_update[OF prnts_new_connected_props(1)]
      prnts_new_connected_props(2) prnts_wthout_p_props(2) evs_in_p_set(1)
      if_distrib[of "\<lambda> x. the x \<in> _ \<and> _"] if_bool_eq_conj
    by(auto split: option.split intro!: parent_map.invar_update prnts_new_connected_props(1))
  have orns_wthout_p_props:
    "origin_invar orns_wthout_p"
    "origin_lookup orns_wthout_p = 
       (\<lambda> x. if x \<in> set p then None
             else origin_lookup orngs x)"
    unfolding orns_wthout_p_def foldl_conv_foldr rev_p_def[symmetric] rev_same_set
    by(induction rev_p)
      (auto simp add: assms origin_map.map_delete intro: origin_map.invar_delete)
  define f2 where "f2 = (\<lambda>org x.
                  if the (origin_lookup org x) = old_orgn then origin_upd x new_vert org
                  else org)"
  define intermed_orgn where 
    "intermed_orgn =(vset_iterate_origin f2
              orns_wthout_p (vset_union ods_new evs_new'))"
  have vset_uniony: "vset_invar (vset_union ods_new evs_new')"
    "vset_to_set (vset_union ods_new evs_new') = vset_to_set ods_new \<union> vset_to_set evs_new'"
    using evs_new'_def helper1(1)[OF refl] ods_new_props(1) 
    by(auto simp add: vset_union)
  obtain vs2 where vs2: "vset_to_set (vset_union ods_new evs_new') = set vs2"
    "distinct vs2"
    "vset_iterate_origin f2 orns_wthout_p (vset_union ods_new evs_new') =
     foldl f2 orns_wthout_p vs2"
    using vseta[OF vset_uniony(1)] by force
  define rev_vs2 where "rev_vs2 = rev vs2"
  have rev_vs2_set: "set vs2 = set rev_vs2"
    by(auto simp add: rev_vs2_def)
  have intermed_orgn_props:
    "origin_invar intermed_orgn"
    "origin_lookup intermed_orgn = 
       (\<lambda> x. if x \<in> vset_to_set ods_new \<union> vset_to_set evs_new' 
                \<and> the (origin_lookup orns_wthout_p x) = old_orgn
             then Some new_vert
             else origin_lookup orns_wthout_p x)"
    unfolding intermed_orgn_def vs2(3) vset_uniony(2)[symmetric] vs2(1)
      foldl_conv_foldr rev_vs2_set rev_vs2_def[symmetric]
    unfolding f2_def
  proof(induction rev_vs2, goal_cases)
    case (4 a vs2)
    show ?case 
      apply(subst foldr.foldr_Cons, subst o_apply)
      apply(subst if_distrib[of origin_lookup])
      apply(subst origin_map.map_update[OF 4(1)])
      apply(subst 4(2))+
      by(auto intro!: ext)
  qed (auto intro!: origin_map.invar_update simp add: orns_wthout_p_props(1))
  have invar_new_orgns: "origin_invar new_orgns"
    using intermed_orgn_props
    by(auto simp add: new_orgns_def intermed_orgn_def f2_def 
        intro!: origin_map.invar_update orns_wthout_p_props(1))

  show "vset_invar (roots new_forest)" ?th1
    unfolding news 
    using new_roots_props by simp+
  show "vset_invar (odds new_forest)" ?th2
    using ods_new_props set_ods_in_p_is
    unfolding news by simp+
  show "vset_invar (evens new_forest)" ?th3
    using evs_new_props set_evs_in_p_is
    unfolding news by simp+
  show "parent_invar (parents new_forest)" ?th4
    using new_prnts_props
    unfolding news set_evs_in_p_is ods_new_props(2) set_ods_in_p_is 
    by auto
  show "origin_invar (origins new_forest)"
    using invar_new_orgns
    by(auto simp add: news new_orgns_def)
  have vset_to_set_evs_new': "vset_to_set evs_new' = vset_to_set evs - {p ! i |i. i < length p \<and> even i}"
    using evs_new'_def helper1(2) set_evs_in_p_is by presburger
  show ?th5
    unfolding news new_orgns_def
    unfolding if_distrib[of origin_lookup]
  proof(subst origin_map.map_update, goal_cases)
    case 2
    show ?case
    using intermed_orgn_props[simplified intermed_orgn_def f2_def] orns_wthout_p_props(2)
    by(subst origin_map.map_update)
      (force simp add: ods_new_props(2) set_ods_in_p_is old_orgn_def vset_to_set_evs_new')+
  qed(simp add: orns_wthout_p_props(1))
qed

definition Dquot_graph where
  "Dquot_graph P G = {(P u, P v)| u v. (u,v) \<in> G}"

lemma Dquot_id:  "Dquot_graph id G = G"
  by(auto simp add: Dquot_graph_def)

lemma Dquot_quot_UD:"UD (Dquot_graph P G) = quot_graph P (UD G)"
  by(auto simp add: Dquot_graph_def quot_graph_def UD_def)

lemma Dquot_graph_alt_def:
  assumes contr_def: "contr = (\<lambda> v. if v \<in> set p then new_vert else v)"
    and new_vert_where: "new_vert \<notin> dVs G - set p"
  shows "Dquot_graph contr G - {(new_vert, new_vert)} =
    G - \<Union> {\<delta>\<^sup>+ G x |x. x \<in> set p} - \<Union> {\<delta>\<^sup>- G x |x. x \<in> set p} \<union>
    {(new_vert, y) |y. y \<in> \<Gamma>\<^sup>+ G set p} \<union>
    {(y, new_vert) |y. y \<in> \<Gamma>\<^sup>- G set p}"
proof(rule, all \<open>rule\<close>, goal_cases)
  case (1 e)
  then obtain u v where uv: "e = (u, v)"
    by(cases e) auto
  then obtain u' v' where  "u = contr u'" "v = contr v'" "(u', v') \<in> G"
       "u \<noteq> new_vert \<or> v \<noteq> new_vert"
    using 1 by(auto simp add: Dquot_graph_def)
  then show ?case 
    using new_vert_where
    by(auto simp add: contr_def Gamma_minus_def Gamma_plus_def
                      delta_plus_def delta_minus_def uv)
next
  case (2 e)
  then show ?case 
  proof(rule UnE, goal_cases)
    case 1
    then show ?case
    proof(rule UnE, goal_cases)
      case 1
      then obtain u v where uv: "e = (u, v)" "(u, v) \<in> G"
        by(cases e) auto
      have "e = (contr u, contr v)"
        if "u \<notin> set p" "v \<notin> set p"
        using that by(auto simp add: uv contr_def)
      moreover have False
        if "u \<in> set p" 
      proof-
        have "e \<in> \<delta>\<^sup>+ G u"
          using 1 by(auto simp add: uv delta_plus_def delta_minus_def) 
        hence "e\<in> \<Union> {\<delta>\<^sup>+ G x |x. x \<in> set p}" using that by auto
        thus False
          using 1 by simp
      qed
      moreover have False
        if "v \<in> set p"
      proof-
        have "e \<in> \<delta>\<^sup>- G v"
          using 1 by(auto simp add: uv delta_plus_def delta_minus_def) 
        hence "e\<in> \<Union> {\<delta>\<^sup>- G x |x. x \<in> set p}" using that by auto
        thus False
          using 1 by simp
      qed
      moreover have "e \<noteq> (new_vert, new_vert)"
        using "1" calculation(2) new_vert_where uv by blast
      ultimately show ?case
        using uv by(auto simp add: Dquot_graph_def)
    next
      case 2
      then show ?case 
      using new_vert_where
     by(auto simp add: Dquot_graph_def contr_def Gamma_plus_def)
    qed
  next
    case 2
    then show ?case 
  using new_vert_where
  by(auto simp add: Dquot_graph_def contr_def Gamma_minus_def)
 qed
qed

lemma contract_path_correct:
  assumes "forest_invar \<M> (Forest rts evs ods prnts orngs)" 
    "follow (parent_lookup prnts) v = p1@[u]@p2"
    "v \<in> vset_to_set evs"
    "u \<in> vset_to_set evs" "matching \<M>"
    "new_vert \<notin> Vs \<M> \<union> vset_to_set evs \<union> vset_to_set ods -  set (p1@[u])"
    "dblton_graph \<M>"
    and contr_def: "contr = (\<lambda> v. if v \<in> set (p1@[u]) then new_vert else v)"
    and new_forest_def:
    "new_forest = contract_path (Forest rts evs ods prnts orngs) (p1@[u]) new_vert"
  shows "forest_invar (quot_graph contr \<M> - {{new_vert}}) new_forest" (is ?th1)
    and  "abstract_forest new_forest 
         = quot_graph contr (abstract_forest (Forest rts evs ods prnts orngs)) - {{new_vert}}" (is ?th2)
    and "vset_to_set (odds new_forest) = vset_to_set ods - set (p1 @ [u])" 
    and "vset_to_set (evens new_forest) = vset_to_set evs - set (p1 @ [u]) \<union> {new_vert}"
    and "vset_to_set (roots new_forest) =
    (if u \<in> vset_to_set rts
     then vset_to_set rts - {u} \<union> {new_vert} else vset_to_set rts)" (is ?th3)
    and "matching (quot_graph contr \<M> - {{new_vert}})" (is ?th4)
    and "\<lbrakk>follow (parent_lookup prnts) v' = p1'@[u]@p2; set p1 \<inter> set p1' = {}\<rbrakk> \<Longrightarrow>
     follow (parent_lookup (parents new_forest)) 
     (if p1' = [] then new_vert else v') = p1'@[new_vert]@p2"
    (is "\<lbrakk>?asm1;?asm2\<rbrakk>\<Longrightarrow> ?th5")
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

  note effect_of_contract_path = 
    effect_of_contract_path[OF invar_basic_F(2,3,1,4,5) new_forest_def]

  note follow_alt_here = follow_alternating_paths(1,3)[OF assms(1), 
      simplified, OF assms(2)[symmetric] assms(3)]

  have evens_in_p_are: "{(p1 @ [u]) ! i |i. i < length (p1 @ [u]) \<and> even i} = 
        vset_to_set evs \<inter> set (p1@[u])"
  proof(rule, all \<open>rule\<close>, goal_cases)
    case (1 x)
    then obtain i where "x = (p1 @ [u]) ! i" "i < length (p1 @ [u])" "even i"
      by auto
    moreover hence "x \<in> vset_to_set evs" 
      using  alt_list_append_1 follow_alt_here(2)[simplified append.assoc[symmetric]]
             alternating_list_even_index[of _ _ "p1@[u]" i]
      by blast
    ultimately show ?case
      using in_set_conv_nth by fast
  next
    case (2 x)
    then obtain i where "x = (p1 @ [u]) ! i" "i < length (p1 @ [u])"
      using in_set_conv_nth[of x "p1 @ [u]"] Int_iff[of x "vset_to_set evs" "set (p1 @ [u])"]
      by auto
    moreover hence "even i" 
      using alt_list_append_1 follow_alt_here(2)[simplified append.assoc[symmetric]]
        alternating_list_odd_index[of _ _ "p1@[u]" i] "2"  invar_basic_F(7)
      by blast
    ultimately show ?case 
      by auto
  qed

  have odds_in_p_are: "{(p1 @ [u]) ! i |i. i < length (p1 @ [u]) \<and> odd i} = 
        vset_to_set ods \<inter> set (p1@[u])"
  proof(rule, all \<open>rule\<close>, goal_cases)
    case (1 x)
    then obtain i where "x = (p1 @ [u]) ! i" "i < length (p1 @ [u])" "odd i"
      by auto
    moreover hence "x \<in> vset_to_set ods" 
      using alt_list_append_1 follow_alt_here(2)[simplified append.assoc[symmetric]]
            alternating_list_odd_index[of _ _ "p1@[u]" i] 
      by blast
    ultimately show ?case
      using in_set_conv_nth by fast
  next
    case (2 x)
    then obtain i where "x = (p1 @ [u]) ! i" "i < length (p1 @ [u])"
      using in_set_conv_nth[of x "p1 @ [u]"]
            Int_iff[of x "vset_to_set ods" "set (p1 @ [u])"] by auto
    moreover hence "odd i" 
      using alt_list_append_1 follow_alt_here(2)[simplified append.assoc[symmetric]]
            alternating_list_even_index[of _ _ "p1@[u]" i] "2"  invar_basic_F(7)
      by blast
    ultimately show ?case 
      by auto
  qed

  have new_parents_are: "parent_lookup (parents new_forest) =
    (\<lambda>x. if x = new_vert \<and> parent_lookup prnts u \<noteq> None
          then parent_lookup prnts u
          else if (x \<notin> set (p1 @ [u]) \<and> the (parent_lookup prnts x)
                   \<in> set (p1 @ [u]) \<inter> vset_to_set evs \<and>
                   x \<in> vset_to_set ods - set (p1@[u]))
               then Some new_vert
          else if x \<in> set (p1 @ [u]) then None 
          else parent_lookup prnts x)"
    by(rule ext, unfold effect_of_contract_path(9) evens_in_p_are odds_in_p_are)
       auto
  have prnts_no_loop:"parent_lookup prnts u = Some u \<Longrightarrow> False" for u
    using forest_invar_F(4)
    by(auto intro!: wf_no_loop dest!: invar_parent_wfD parent_specD)
  have DAF_no_loop:"(u,u) \<in> Dabstract_forest (Forest rts evs ods prnts orngs) \<Longrightarrow> False" for u
    by(auto simp add: Dabstract_forest_def intro!: prnts_no_loop[OF sym])

  interpret parents_here: parent "(parent_lookup prnts)"
    using follow_dom_invar_parent_wf(1) forest_invar_F(4) by fastforce
  note follow_not_again_parent = parents_here.follow_not_again_parent[folded follow_def]
  note follow_subsequent_parent = parents_here.follow_subsequent_parent[folded follow_def]
  note follow_subsequent_parent_there = parents_here.follow_subsequent_parent_there[folded follow_def]
  note follow_valk_bet = parents_here.follow_valk_bet[folded follow_def, 
      simplified parents_here.parent_eq_follow_rel]
  note follow_simps = parents_here.follow_psimps[folded follow_def]
  note follow_hd = parents_here.follow_hd[folded follow_def]
  note follow_distinct = parents_here.follow_distinct[folded follow_def]
  note follow_append = parents_here.follow_append[folded follow_def]
  note follow_None = parents_here.follow_None[folded follow_def]
  note follow_distinct = parents_here.follow_distinct[folded follow_def]
  note follow_cons_3' = parents_here.follow_cons_3'[folded follow_def]
  note follow_cons_4 = parents_here.follow_cons_4[folded follow_def]
  note follow_cons_2 = parents_here.follow_cons_2[folded follow_def]

  have  parent_adj_pu_helper:
   "\<lbrakk>parent_lookup prnts x = Some y; x \<notin> vset_to_set ods \<or> y \<notin> vset_to_set evs;
     p1 = ys @ y # zs; x \<notin> set ys \<or> y = u\<rbrakk> \<Longrightarrow> False"
    for ys zs x y
  proof(goal_cases)
    case 1
    have y_not_u:"y \<noteq> u"
      using follow_distinct[of v] 1(3) assms(2) by auto
    have xy_af:"{x, y} \<in> abstract_forest (Forest rts evs ods prnts orngs)"
      using 1 abstract_forest_def by fastforce
    hence "x \<in> vset_to_set evs \<longleftrightarrow>  x \<notin> vset_to_set ods"
          "y \<in> vset_to_set evs \<longleftrightarrow> y \<notin> vset_to_set ods"
      using 1 invar_basic_F(14,6,7) by blast+
    hence even_x: "x \<in> vset_to_set evs"
      and odd_y: "y \<in> vset_to_set ods"
      using 1(2)  xy_af forest_invar_F(3)
      by(auto elim!: invar_forest_even_and_oddE)
    obtain y' ys' where  y'ys': "ys=ys'@[y']" 
      using assms(2,3) odd_y "1"(3) neq_Nil_conv_snoc[of "(y # _) @ [_]"]
            neq_Nil_conv_snoc[of zs] neq_Nil_conv_snoc[of ys]
            follow_hd[of v] invar_basic_F(7)
      by auto
    hence "parent_lookup prnts y' = Some y" 
      using 1
      by(auto intro!: follow_subsequent_parent[of v ys' y' y "zs@[u]@p2"] 
          simp add: assms(2))
    hence "y' = x" 
      using odds_unique_child'[OF assms(1) _ assms(5), of y]  odd_y 1 by simp
    show False
      using "1"(4) \<open>y' = x\<close> y'ys' y_not_u by auto
  qed

  have Dabstract_forest_new_in_Qquot: "Dabstract_forest new_forest \<subseteq>
    Dquot_graph contr (Dabstract_forest (Forest rts evs ods prnts orngs))"
    unfolding abstract_forest_def
  proof(rule, goal_cases)
    case (1 e)
    then obtain x y where xy: "e = (y, x)" "parent_lookup (parents new_forest) x = Some y"
      by(auto simp add: Dabstract_forest_def)
    show ?case
      using xy(2) unfolding xy(1) new_parents_are 
    proof(cases "x = new_vert \<and> parent_lookup prnts u \<noteq> None", goal_cases)
      case 1
      note 1 = 1[simplified if_P[OF 1(2)]]
      then show ?case 
        using in_set_conv_decomp[of y p1] assms(2) follow_not_again_parent[of v _ y _ u p2] 
        by(auto intro!: exI[of "\<lambda> y. (_ y \<longrightarrow> (_ y \<and> _ y)) \<and> (_ y \<longrightarrow> (_ y \<and> _ y))
                             \<and> (_ y \<longrightarrow> (_ y \<and> _ y))" y]
                 intro: exI[of _ u]
                  dest: prnts_no_loop 
              simp add: Dquot_graph_def contr_def Dabstract_forest_def)    
    next
      case 2
      note 2 = 2[simplified if_not_P[OF 2(2)]]
      then show ?case 
      proof(cases "x \<notin> set (p1 @ [u]) \<and>
        the (parent_lookup prnts x) \<in> set (p1 @ [u]) \<inter> vset_to_set evs \<and>
        x \<in> vset_to_set ods - set (p1 @ [u])", goal_cases)
        case 1
        note 1 = 1[simplified if_P[OF 1(3)]]
        hence "parent_lookup prnts x = Some (the (parent_lookup prnts x))"
          using  forest_invar_F(7) 
          by(auto elim!: invar_odd_to_parent_non_matchingE)
        then show ?case 
          using 1
          by(auto intro!: exI[of "\<lambda> ua. (_ ua \<longrightarrow> (\<exists> v. _ ua v)) \<and> _  ua \<and> _  ua " 
                            "(the (parent_lookup prnts x))"] 
                          exI[of "\<lambda> y. (_ y \<longrightarrow> (_ y \<and> _ y)) \<and> (_ y \<longrightarrow> (_ y \<and> _ y))
                             \<and> (_ y \<longrightarrow> (_ y \<and> _ y))" x] 
                simp add: Dquot_graph_def contr_def Dabstract_forest_def)
      next
        case 2
        note 2 = 2[simplified if_not_P[OF 2(3)]]
        then show ?case
        proof(cases "x \<in> set (p1 @ [u])", goal_cases)
          case 2
          note 2 = 2[simplified if_not_P[OF 2(4)]]
          have helper2:
           "\<lbrakk>parent_lookup prnts x = Some y; x \<notin> vset_to_set ods \<or> y \<notin> vset_to_set evs;
             p1 = ys @ y # zs; x \<notin> set ys \<or> y = u\<rbrakk> \<Longrightarrow> False" for ys zs 
            using parent_adj_pu_helper[of x y ys zs] by blast
          have x_not_oddD:"x \<notin> vset_to_set ods \<Longrightarrow> x \<in> vset_to_set evs"
            using "2"(1) invar_basic_F(14,6) by auto
          from 2 show ?case 
            using assms(4) invar_basic_F(6,7)
                  invar_even_to_parent_matchingD_here[of x y]
                  invar_forest_even_and_oddD_here[of x y]
                  invar_matching_both_or_noneD_here[of x y]  
            by(simp add: Dquot_graph_def contr_def Dabstract_forest_def, intro exI[of _ y])
              (auto dest: x_not_oddD invar_even_to_parent_matchingD_here[of x y] helper2
                  intro!: exI[of _ x] 
                simp add: in_set_conv_decomp[of y p1])
        qed simp
      qed
    qed
  qed

  have new_vert_loop_not_in_new: "(new_vert,new_vert) \<notin> Dabstract_forest new_forest"
  proof-
    note helpers_here = invar_basic_F(14) 
          invar_even_to_parent_matchingD_here[ of u "the (parent_lookup prnts u)"] 
          invar_forest_even_and_oddD_here[of u "the (parent_lookup prnts u)"]
          invar_matching_both_or_noneD_here[of u "the (parent_lookup prnts u)"]
          edges_are_Vs_2[of u "the (parent_lookup prnts u)"] 
          in_set_conv_decomp[of new_vert p1] 
          follow_not_again_parent [of v _ new_vert _ u p2] 
    show ?thesis
     using assms(6,2,4)  prnts_no_loop[of new_vert]
     by (auto simp add: new_parents_are Dabstract_forest_def, insert helpers_here, auto)
 qed

  have Qquot_in_Dabstract_forest_new: 
   "Dabstract_forest new_forest \<supseteq> 
    Dquot_graph contr (Dabstract_forest (Forest rts evs ods prnts orngs)) 
      - {(new_vert,new_vert)}"
  proof(rule, goal_cases)
    case (1 e)
    then obtain u' v' where uv: "e = (contr u', contr v')" 
      "Some u' = parent_lookup prnts v'"
      "contr u' \<noteq> new_vert \<or> contr v' \<noteq> new_vert"
      by (auto simp add: Dquot_graph_def Dabstract_forest_def)
    have u_neq_v: "u' \<noteq> v'"
      using uv(2) prnts_no_loop[of u'] by auto
    have u'v'_AF:"{u', v'} \<in> abstract_forest (Forest rts evs ods prnts orngs)"
      using uv(2) by(force simp add: abstract_forest_def )
    hence u'v'_evens_and_odds: "{u', v'} \<subseteq> vset_to_set evs \<union> vset_to_set ods"
      using uv(2) by (simp add: edges_are_Vs edges_are_Vs_2 invar_basic_F(6))
    have ?case
      if "u' \<in> set (p1 @ [u])" "v' \<in> set (p1 @ [u])"
      using uv that u_neq_v by(auto simp add: contr_def)
    moreover have ?case
      if asm: "u' \<notin> set (p1 @ [u])" "v' \<in> set (p1 @ [u])"    
    proof-
      note uv = uv[simplified contr_def if_not_P[OF asm(1)] if_P[OF asm(2)], simplified]
      have "v' = u" 
      proof(rule ccontr, goal_cases)
        case 1
        then obtain p1a p1b where "p1 = p1a@[v']@p1b"
          using asm(2) in_set_conv_decomp_first[of v' p1] 
          by auto
        then obtain p1a p1b where "p1@[u]@p2 = p1a@[v', u']@p1b@p2"
          using follow_subsequent_parent_there[of v p1a v' "p1b@[u]@p2" u']
          by(cases p1b)(auto simp add: assms(2) uv(2))
        then show ?case 
          using that(1) by auto
      qed
      thus ?thesis
        using uv 
        by(auto intro: exI[of _ u'] simp add: Dabstract_forest_def new_parents_are) 
    qed
    moreover have ?case
      if asm: "u' \<in> set (p1 @ [u])" "v' \<notin> set (p1 @ [u])"           
    proof-
      note uv = uv[simplified contr_def if_P[OF asm(1)] if_not_P[OF asm(2)], simplified]
      have u'v'_even_odd_eqiv: "u' \<in> vset_to_set evs \<longleftrightarrow> v' \<in> vset_to_set ods" 
        using uv(2) invar_forest_even_and_oddD[OF forest_invar_F(3), of u' v']
        by(force simp add: abstract_forest_def doubleton_eq_iff)
      obtain p1a p1b where p1a_p1b: "p1a@[u']@p1b = p1@[u]"
        using asm(1) split_list_last[of u' "p1 @ [u]"] by auto
      have u'_v'_parities: "u' \<in> vset_to_set evs \<and> v' \<in> vset_to_set ods"
      proof(rule ccontr, goal_cases)
        case 1
        hence u'_odd: "u' \<in> vset_to_set ods" and v'_even: "v' \<in> vset_to_set evs"
          using u'v'_even_odd_eqiv u'v'_evens_and_odds by auto
        hence "p1a \<noteq> []"
          using "1" assms(2,3) follow_hd[of v]  u'v'_even_odd_eqiv p1a_p1b
          by(cases p1) auto
        then obtain v'' p1a' where v'': "p1@[u] = p1a'@[v'',u']@p1b"
          using p1a_p1b
          by(auto dest!: append_butlast_last_cancel[of p1a "u' # [] @ p1b", symmetric])
        hence "parent_lookup prnts v'' = Some u'"
          using assms(2) follow_subsequent_parent[of v p1a' v'' u' "p1b @ p2"] 
          by auto
        hence "v'' = v'"
          using u'_odd assms(1,5) odds_unique_child' uv(2) by auto
        thus False 
          using that(2) v'' by auto
      qed
      show ?thesis
        using uv(1,3)  u'_v'_parities asm 
        by (auto simp add: uv(2)[symmetric] Dabstract_forest_def new_parents_are)
    qed
    moreover have ?case
      if asm: "u' \<notin> set (p1 @ [u])" "v' \<notin> set (p1 @ [u])"
    proof-
      note uv = uv[simplified contr_def if_not_P[OF asm(1)] if_not_P[OF asm(2)], simplified]
      hence no_new_vert: "u' \<noteq> new_vert" "v' \<noteq> new_vert"
        using assms(6) that(1,2) u'v'_evens_and_odds by auto
      show ?thesis
        using uv(1) uv(2)[symmetric] asm no_new_vert(2) 
        by (auto simp add: Dabstract_forest_def new_parents_are)
    qed
    ultimately show ?case 
      by fast
  qed
  have Qquot_in_Dabstract_forest_new:
    "Dquot_graph contr (Dabstract_forest (Forest rts evs ods prnts orngs)) -
       {(new_vert, new_vert)}
       = Dabstract_forest new_forest"
    using Dabstract_forest_new_in_Qquot Qquot_in_Dabstract_forest_new new_vert_loop_not_in_new
    by blast
  have AF_in_quot:"abstract_forest new_forest \<subseteq>
    quot_graph contr (abstract_forest (Forest rts evs ods prnts orngs))"
    using Dabstract_forest_new_in_Qquot UD_subseteq 
    by(auto simp add: Dabstract_forest_UD[symmetric] Dquot_quot_UD[symmetric])
  have new_vert_not_in_AF:"{new_vert} \<notin> abstract_forest new_forest"
    using new_vert_loop_not_in_new
    by(auto simp add: Dabstract_forest_def abstract_forest_def)
  have quot_in_AF: 
      "quot_graph contr (abstract_forest (Forest rts evs ods prnts orngs)) - {{new_vert}}
       \<subseteq> abstract_forest new_forest"
    using Qquot_in_Dabstract_forest_new
    unfolding Dabstract_forest_UD[symmetric] Dquot_quot_UD[symmetric]
    by(auto simp add: UD_def) 
  have quot_is_AF: 
      "quot_graph contr (abstract_forest (Forest rts evs ods prnts orngs)) - {{new_vert}}
       = abstract_forest new_forest"
    using AF_in_quot new_vert_not_in_AF quot_in_AF by blast
  have Vs_contracted:"Vs (abstract_forest new_forest) \<union> {new_vert}= 
        Vs (abstract_forest (Forest rts evs ods prnts orngs)) - set (p1@[u]) \<union> {new_vert}"
    unfolding quot_is_AF[symmetric]
    by(auto simp add: quot_graph_def Vs_def contr_def)
  have Vs_contracted':
     "Vs (abstract_forest new_forest) = 
      Vs (abstract_forest (Forest rts evs ods prnts orngs)) - set (p1@[u]) \<union> {new_vert} "
  if asm: "last (p1 @ [u]) \<notin> vset_to_set rts"
  proof(goal_cases)
    case 1
    obtain up where "parent_lookup prnts u = Some up"
      using asm[simplified] assms(4) invar_rootsD_here(2)[of u] invar_basic_F(13,6) 
      by blast
    hence "parent_lookup (parents new_forest) new_vert = Some up"
      by(simp add: new_parents_are)
    hence "new_vert \<in> Vs (abstract_forest new_forest)"
      by(auto simp add: abstract_forest_def)
    thus ?case
      by(unfold Vs_contracted[symmetric]) auto
  qed
  have p1_no_roots:"set p1 \<inter> vset_to_set rts = {}" 
  proof(rule ccontr, goal_cases)
    case 1
    then obtain x where x: "x \<in> set p1" "x \<in>  vset_to_set rts"
      by auto
    then obtain p1a p1b where "p1=p1a@[x]@p1b" 
      using split_list_first[of x p1] by auto
    then obtain y where "parent_lookup prnts x = Some y" 
      using assms(2) follow_subsequent_parent[of v p1a x _ _ ]
      by(cases p1b) auto
    then show ?case
      using x(2) invar_basic_F(13) by auto
  qed
  have u_roots_p2_Nil:"u \<in> vset_to_set rts \<longleftrightarrow> p2 = Nil"
    using invar_basic_F(13,6)[symmetric] follow_simps[of u] assms(2,4) 
          invar_rootsD_here(2)[of u] p1_no_roots follow_None[of u] follow_append
      by auto+
  have parents_ev_od: "x \<in> vset_to_set evs \<longleftrightarrow> y \<in> vset_to_set ods"
    "x \<in> vset_to_set ods \<longleftrightarrow> y \<in> vset_to_set evs"
    if "parent_lookup prnts x = Some y" for x y
    using invar_forest_even_and_oddD[OF forest_invar_F(3), of x y]
      invar_forest_even_and_oddD[OF forest_invar_F(3), of y x] that
    by(auto simp add: abstract_forest_def)
  have hd_p1: "hd (p1@[u]) = v"
    using hd_append[of p1 "[u]"] 
      parents_here.follow_hd[of v] assms(2) follow_def[of "parent_lookup prnts"]
    by auto
  have rev_alt_path_M: "rev_alt_path \<M> (p1 @ [u])"
    using follow_alt_here(1) edges_of_path_append_2[of "u # p2" p1] alt_list_append_1 
    by auto
  have M_quot: 
    "quot_graph contr \<M> - {{new_vert}} 
     = \<M> - ((if u \<in> vset_to_set rts then {} 
              else {{u, the (parent_lookup prnts u)}}) \<union> set (edges_of_path (p1@[u]))) \<union> 
                     (if u \<in> vset_to_set rts then {} 
                      else {{new_vert, the (parent_lookup prnts u)}})"
  proof(rule, all \<open>rule\<close>, goal_cases)
    case (1 e)
    then obtain x y where xy: "e = contr ` {x, y}" "{x, y} \<in> \<M>" "x \<noteq> y"
      using assms(7) by(force simp add: quot_graph_def) 
    hence  x_or_y_not_contracted:"x \<notin> set (p1@[u]) \<or> y \<notin> set (p1@[u])"
      using 1 by(auto simp add: contr_def)
    hence xy_not_in_edges:"{x, y} \<notin> set (edges_of_path (p1 @ [u]))"
      by (simp add: edge_not_in_edges_in_path)
    show ?case 
    proof(cases  "x \<notin> set (p1@[u]) \<and> y \<notin> set (p1@[u])")
      case True
      hence "e \<in> \<M>" "e = {x, y}"
        using  xy by (auto simp add: contr_def)
      then show ?thesis
        using  xy_not_in_edges True 
        by(auto simp add: doubleton_eq_iff)
    next
      case False
      then obtain x' y' where xy: "e = contr ` {x', y'}" "{x', y'} \<in> \<M>" "x' \<noteq> y'"
        "x' \<in> set (p1@[u])" "y' \<notin> set (p1@[u])" "{x, y} = {x', y'}"
        using xy(1,2) x_or_y_not_contracted doubleton_eq_iff[of x y y x] by fastforce
      have x'_is_u:"x' = u"
      proof(rule ccontr, goal_cases)
        case 1
        then obtain p1a p2a where p1ap2a:"p1 = p1a@[x']@p2a" 
          using xy(4) in_set_conv_decomp_last[of x' p1]
          by auto
        then obtain xp where xp: "parent_lookup prnts x' = Some xp"
          using assms(2) by(cases p2a) (auto simp add: follow_subsequent_parent)
        have x_not_odd:"x' \<in> vset_to_set ods \<Longrightarrow> False"
        proof(goal_cases)
          case 1
          then obtain xc p1aa where xc: " p1a = p1aa@[xc]" 
            using hd_p1 p1ap2a assms(3) invar_basic_F(7)
            by(cases p1a rule: rev_cases) auto
          hence xc_child_x:"parent_lookup prnts xc = Some x'" 
            using assms(2) p1ap2a 
            by (simp add: follow_def parents_here.follow_subsequent_parent)
          hence "xc \<in> vset_to_set evs"
            using assms(1,5) "1"
                  odds_unique_child[of \<M> "Forest rts evs ods prnts orngs"  x'] 
            by auto
          hence "{x', xc} \<in> \<M>" 
            using  xc_child_x 
              invar_even_to_parent_matchingD[OF forest_invar_F(5)] 
            by (auto simp add: edge_commute)
          hence "xc = y'" 
            using assms(5) doubleton_in_matching(1) xy(2) by fastforce
          then show ?case 
            using p1ap2a xc xy(5) by auto
        qed
        hence x'_even:"x' \<in> vset_to_set evs"
          using xp  invar_basic_F(14) invar_basic_F(6)[symmetric] by auto
        hence "xp \<in> vset_to_set ods" 
          by (simp add: parents_ev_od(1) xp)
        then obtain p2aa where "p2a = xp#p2aa"
          using p1ap2a xp assms(2,4) x_not_odd assms(4)follow_subsequent_parent parents_ev_od(2)
          by (cases p2a) auto
        have "{x', xp} \<in> \<M>"
          using x'_even forest_invar_F(5) invar_even_to_parent_matchingD xp
          by fastforce
        hence "xp = y'" 
          using assms(5) xy(2) by(auto intro!: doubleton_in_matching(1))
        thus False
          using \<open>p2a = xp # p2aa\<close> p1ap2a xy(5) by auto
      qed
      hence u_no_root:"u \<notin> vset_to_set rts" 
        using edges_are_Vs[of y' x' \<M>] invar_basic_F(11) xy(2)
        by blast
      have parent_x'_is:"parent_lookup prnts x' = Some y'"
      proof(cases "parent_lookup prnts x'")
        case None
        then show ?thesis 
          using u_no_root x'_is_u assms(4) domIff[of u "origin_lookup orngs"] invar_basic_F(13,15,6)
             imageI[of u "vset_to_set evs \<union> vset_to_set ods" "origin_lookup orngs"]
          by auto
      next
        case (Some a)
        hence "a \<in> vset_to_set ods" 
          using assms(4) parents_ev_od(1) x'_is_u by blast
        then show ?thesis 
          using assms(4,5) x'_is_u xy(2) Some invar_even_to_parent_matchingD_here[of u a]
          by (auto dest!: doubleton_in_matching(1)[of \<M> u y' a])
      qed
      have "e = {new_vert, the (parent_lookup prnts u)}" 
        using parent_x'_is  x'_is_u xy(3,5)
        by(auto simp add: xy(1) contr_def x'_is_u)
      thus ?thesis
        by (simp add: u_no_root)
    qed
  next
    case (2 e)
    show ?case 
    proof(rule UnE[OF 2], goal_cases)
      case 1
      note one = this
      then obtain x y where xy: "e = {x, y}" "x \<noteq> y"
        using assms(7) by auto
      have e_in_M: "e \<in> \<M>"
        using "1" by blast
      show ?case
      proof(rule matching_edge_rev_alt_path_cases[OF rev_alt_path_M e_in_M, simplified], goal_cases)
        case 1
        then show ?case
          by (simp add: assms(7))
      next
        case 2
        then show ?case
          by (simp add: assms(5))
      next
        case (3 u' v' i)
        hence "{u', v'} \<in> set (edges_of_path (p1@[u]))"
          using edges_of_path_length[of "p1 @ [u]"] 
                in_set_conv_nth[of "edges_of_path (p1 @ [u]) ! i" ]
          by auto
        then show ?case
          using "1" "3"(6) by force
      next
        case (4 u' v')
        hence "v' = the (parent_lookup prnts u)" 
          using assms(4,5)  e_in_M invar_basic_F(11,13,6)[symmetric] edges_are_Vs[of u v' \<M>]
                domIff[of u "origin_lookup orngs"] domIff[of u "parent_lookup prnts"]
                invar_basicD_here(15) invar_even_to_parent_matchingD_here[of u ]
          by (auto dest!: doubleton_in_matching(1)[of \<M> u "the (parent_lookup prnts u)" v'])
        then show ?case
          using one 4 invar_basic_F(11) edges_are_Vs[of u v' \<M>]
          by(cases "u \<in> vset_to_set rts")(auto simp add: quot_graph_def)
      next
        case 5
        then show ?case
          using xy(2) e_in_M
          by(auto intro!: bexI[of _ e] simp add: xy(1) quot_graph_def contr_def )
      qed
    next
      case 2
      hence  e_is: "e = {new_vert, the (parent_lookup prnts u)}" "u \<notin> vset_to_set rts"
        by(all \<open>cases "u \<in> vset_to_set rts"\<close>) auto
      moreover hence u_pu_M:"{u, the (parent_lookup prnts u)} \<in>\<M>" 
        using assms(4) invar_basic_F(13,6)[symmetric] domIff[of u "parent_lookup prnts"]
              invar_basicD_here(15) invar_even_to_parent_matchingD_here[of u]
              imageI[of u "vset_to_set evs \<union> vset_to_set ods" "origin_lookup orngs"]
        by auto
      moreover have "new_vert = the (parent_lookup prnts u) \<Longrightarrow> False"
      proof(goal_cases)
        case 1
        hence "new_vert \<in> Vs (abstract_forest (Forest rts evs ods prnts orngs))"
          using calculation(2) assms(4) invar_basic_F(13,15,6)[symmetric]
                imageI[of u "vset_to_set evs \<union> vset_to_set ods" "origin_lookup orngs"]
                domIff[of u "origin_lookup orngs"] domIff[of u "parent_lookup prnts"]
          by(auto intro!: edges_are_Vs[of _ u] exI2[of _ u new_vert]
                simp add: abstract_forest_def doubleton_eq_iff)
        hence "new_vert \<in> set (p1@[u])"
          using assms(6) "1" calculation(3) edges_are_Vs_2[of u new_vert \<M>]
          by auto
        moreover hence "new_vert = u \<Longrightarrow> False" "new_vert \<in> set p1 \<Longrightarrow> False"
          using "1" assms(2,7) u_pu_M e_is "1"  u_roots_p2_Nil follow_simps[of u] 
              follow_append[of v p1 u p2] option.exhaust_sel[of "parent_lookup prnts u"]
          by (force intro!: follow_not_again_parent[of v _ new_vert _ u p2]
                  simp add: in_set_conv_decomp)+
        ultimately show ?case 
          by auto
      qed
      moreover obtain pu where "parent_lookup prnts u = Some pu" 
        using e_is(2) u_roots_p2_Nil assms(2) follow_simps[of u]  follow_append[of v p1 u p2]
        by force
      ultimately show ?case
        using assms(7)
        by(auto intro!: bexI[of _  "{u, pu}"] follow_not_again_parent[of v _ pu _ u p2]
              simp add: assms(2) in_set_conv_decomp quot_graph_def contr_def)
    qed
  qed
  have distinct_path:"distinct (p1@[u]@p2)"
    using assms(2) follow_distinct[of v] by auto
  have alt_ev_od_p: "alt_list (\<lambda>x. x \<in> vset_to_set evs) (\<lambda>x. x \<in> vset_to_set ods) (p1 @ [u])"
    using alt_list_append_1[of _ _ "p1@[u]"] append.assoc follow_alt_here(2) by simp
  have odd_length_p:"odd (length (p1@[u]))" 
    using assms(4) invar_basic_F(7) alt_ev_od_p alt_list_or 
    by (intro last_odd_P1'[OF alt_ev_od_p]) fastforce+
  have org_lookup_last:"the (origin_lookup orngs u) = u \<longleftrightarrow>  u \<in> vset_to_set rts"
    using assms(4) invar_basic_F(15,6)[symmetric] invar_rootsD_here(1)[of u] 
          imageE[of "origin_lookup orngs u" Some "vset_to_set rts"]
    by force
  have lookup_u_not_none_roots: "parent_lookup prnts u = None \<longleftrightarrow> u \<in> vset_to_set rts"
    using assms(4) invar_basic_F(13,15,6)[symmetric] domIff[of u "origin_lookup orngs"] 
    by auto
  have Diff_Int_idem: "A - (A \<inter> B) = A - B" "A - (B \<inter> A) = A - B" for A B by auto
  have Union_of_same_diff: "(A - B) \<union> (C - B) = (A \<union> C) - B" for A B C by auto

  note origin_new_def = effect_of_contract_path(10)
    [simplified  evens_in_p_are odds_in_p_are Diff_Int_idem Union_of_same_diff
      set_eq_iff Diff_iff mem_Collect_eq last_snoc]

  have dom_samer: "dom (parent_lookup (parents new_forest)) =
    dom (origin_lookup (origins new_forest)) - vset_to_set (roots new_forest)"
  proof-
    show ?thesis
      unfolding new_parents_are effect_of_contract_path(10) dom_def
        evens_in_p_are odds_in_p_are Diff_Int_idem Union_of_same_diff
        set_eq_iff Diff_iff mem_Collect_eq
    proof(rule allI, goal_cases)
      case (1 x)
      have org_u_parent:"the (origin_lookup orngs (last (p1 @ [u]))) \<noteq> last (p1 @ [u]) \<longleftrightarrow>
           parent_lookup prnts u \<noteq> None"
        using lookup_u_not_none_roots org_lookup_last by auto
      show ?case 
        unfolding org_u_parent
      proof(cases "x = new_vert \<and> parent_lookup prnts u \<noteq> None", goal_cases)
        case 1
        hence u_no_root:"last (p1 @ [u]) \<notin> vset_to_set rts"
          using invar_basic_F(13) by auto
        moreover have "x \<notin> vset_to_set (roots new_forest)" 
          using u_no_root 1 assms(6) in_mono insert_Diff invar_basic_F(10) p1_no_roots
          by (auto simp add: effect_of_contract_path(6))
        ultimately show ?case
          using 1 by simp
      next
        case 2
        note two = this
        show ?case 
          unfolding if_not_P[OF 2]
        proof(cases "x \<notin> set (p1 @ [u]) \<and>
         the (parent_lookup prnts x) \<in> set (p1 @ [u]) \<inter> vset_to_set evs \<and>
         x \<in> vset_to_set ods \<and> x \<notin> set (p1 @ [u])", goal_cases)
          case 1
          note one = this
          hence one': "\<not> (x \<in> set (p1 @ [u]) \<and> parent_lookup prnts u \<noteq> None)"
            by simp
          show ?case 
            unfolding if_P[OF 1] if_not_P[OF one'] effect_of_contract_path(6)
          proof(cases "parent_lookup prnts u \<noteq> None", goal_cases)
            case 1
            have x_origin:"origin_lookup orngs x \<noteq> None"
              using one invar_basic_F(15,6) UnI2[of x "vset_to_set ods" "vset_to_set evs"]
              by auto
            show ?case 
              unfolding if_P[OF 1]
            proof(cases "last (p1 @ [u]) \<in> vset_to_set rts", goal_cases)
              case 1
              then show ?case 
                using x_origin assms(6) one invar_basic_F(10,7)
                by auto
            next
              case 2
              then show ?case
                using x_origin invar_basic_F(10,7) one by auto
            qed
          next
            case 2
            note TwO = this
            show ?case 
              unfolding if_not_P[OF 2]
            proof(cases "x = new_vert", goal_cases)
              case 1
              note OnE = this
              show ?case 
                unfolding if_P[OF 1]
              proof(cases "last (p1 @ [u]) \<in> vset_to_set rts", goal_cases)
                case 1
                then show ?case 
                  using assms(6) one OnE by force
              next
                case 2
                then show ?case 
                  using OnE assms(6) one by fastforce
              qed
            next
              case 2
              note tWo = this
              show ?case 
                unfolding if_not_P[OF 2]
              proof(cases "(x \<in> vset_to_set ods \<union> vset_to_set evs \<and> x \<notin> set (p1 @ [u])) \<and>
                           the (if x \<in> set (p1 @ [u]) then None else origin_lookup orngs x) =
                           the (origin_lookup orngs (last (p1 @ [u])))", goal_cases)
                case 1
                note oNe = this
                then show ?case 
                  unfolding if_P[OF 1]
                proof(cases "last (p1 @ [u]) \<in> vset_to_set rts", goal_cases)
                  case 1
                  then show ?case 
                    using tWo invar_basic_F(10,7) one by auto
                next
                  case 2
                  then show ?case
                    using tWo one invar_basic_F(10,7) by auto
                qed
              next
                case 2
                note tWo = this
                hence origin_x:"origin_lookup orngs x \<noteq> None" 
                  using Un_upper2[of "vset_to_set ods" "vset_to_set evs"] one 
                        invar_basic_F(15,6)
                        imageI[of x "vset_to_set evs \<union> vset_to_set ods" "origin_lookup orngs"]
                  by auto 
                have two': "x \<notin> set (p1 @ [u])"
                  using one by simp
                show ?case 
                  unfolding if_not_P[OF 2] if_not_P[OF two']
                proof(cases "last (p1 @ [u]) \<in> vset_to_set rts", goal_cases)
                  case 1
                  then show ?case 
                    using assms(6) origin_x one invar_basic_F(10,7) one by auto
                next
                  case 2
                  then show ?case 
                    using origin_x invar_basic_F(10,7) one by auto
                qed
              qed
            qed
          qed
        next
          case 2
          note two = this
          show ?case 
            unfolding if_not_P[OF 2]
          proof(cases "x \<in> set (p1 @ [u])", goal_cases)
            case 1
            then show ?case 
              by (auto simp add: effect_of_contract_path(6) lookup_u_not_none_roots)
          next
            case 2
            note Two = this
            hence Two': "\<not> (x \<in> set (p1 @ [u]) \<and> parent_lookup prnts u \<noteq> None)"
              by simp
            show ?case 
              unfolding if_not_P[OF 2]  if_not_P[OF Two']
            proof(cases "parent_lookup prnts u \<noteq> None", goal_cases)
              case 1
              note One = this
              show ?case 
                using One invar_basic_F(13)   
                by (auto simp add: effect_of_contract_path(6))
            next
              case 2
              note tWo = this
              then show ?case 
                unfolding if_not_P[OF 2]
              proof(cases "x = new_vert", goal_cases)
                case 1
                then show ?case 
                  using Two assms(6) invar_basic_F(14,6) 
                  by (auto simp add: effect_of_contract_path(6) lookup_u_not_none_roots)
              next
                case 2
                note TwO = this
                show ?case 
                  unfolding if_not_P[OF 2(2)]
                proof(cases "(x \<in> vset_to_set ods \<union> vset_to_set evs \<and> x \<notin> set (p1 @ [u])) \<and>
                            the (origin_lookup orngs x) = 
                            the (origin_lookup orngs (last (p1 @ [u])))", goal_cases)
                  case 1
                  note Onne = this
                  have "\<lbrakk>parent_lookup prnts x = Some y; x \<in> vset_to_set (roots new_forest)\<rbrakk>
                        \<Longrightarrow> False" for y
                    using TwO(2) invar_basic_F(13) 
                    by(cases "u\<in> vset_to_set rts") (auto simp add: effect_of_contract_path(6))
                  thus ?case 
                    using tWo org_u_parent Un_commute[of "vset_to_set evs" "vset_to_set ods"]
                      follow_simps[of x] invar_basic_F(6) Onne invar_rootsD_here(2)[of x]
                    by force
                next
                  case 2
                  show ?case 
                    using invar_basic_F(13) TwO(2) Two 2
                    by(cases "u \<in> vset_to_set rts") (auto simp add: effect_of_contract_path(6))
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed

  have Vs_evens_odds_roots_helper:
    " vset_to_set (evens new_forest) \<union> vset_to_set (odds new_forest) =
    vset_to_set (roots new_forest) \<union> Vs (abstract_forest new_forest)"
  proof(cases "last (p1 @ [u]) \<in> vset_to_set rts")
    case True
    have helper:"\<lbrakk>x \<in> set p1; x \<in> vset_to_set rts\<rbrakk> \<Longrightarrow> x = u" for x
      using p1_no_roots by auto
    from True show ?thesis
      using Vs_contracted invar_basic_F(6) 
      unfolding effect_of_contract_path(7,8)
                evens_in_p_are odds_in_p_are effect_of_contract_path(6) if_P[OF True]
      by (subst (2) Un_assoc)(auto intro!: arg_cong[of _ _ "insert _"] helper)
  next
    case False
    thus ?thesis
      unfolding effect_of_contract_path(7,8) evens_in_p_are odds_in_p_are effect_of_contract_path(6)
      using invar_basic_F(6) p1_no_roots 
      by (auto intro!: arg_cong[of _ _ "insert _"] simp add: Vs_contracted')
  qed

  have org_lookup_helper: 
    "origin_lookup (origins new_forest) `
    (vset_to_set (roots new_forest) \<union> Vs (abstract_forest new_forest)) =
    Some ` vset_to_set (roots new_forest)"
    unfolding Vs_evens_odds_roots_helper[symmetric]
    unfolding effect_of_contract_path(6,8,7,10)
    unfolding org_lookup_last evens_in_p_are odds_in_p_are Diff_Int_idem Union_of_same_diff
      set_eq_iff Diff_iff mem_Collect_eq last_snoc image_def
      Un_commute[of _ "{new_vert}"] Un_assoc[of "{new_vert}"]
  proof(rule allI, goal_cases)
    case (1 x)
    show ?case
    proof(cases "u \<in> vset_to_set rts", goal_cases)
      case 1
      hence h1: "the (origin_lookup orngs u) = u"
        using org_lookup_last by force
      have sg2: 
        "\<lbrakk>\<forall>x\<in>vset_to_set rts - {u}. origin_lookup orngs xa \<noteq> Some x;
          x = origin_lookup orngs xa; the (origin_lookup orngs xa) \<noteq> u\<rbrakk>
          \<Longrightarrow> xa \<in> vset_to_set evs \<Longrightarrow> False" for xa
        using invar_basic_F(15,6) imageI[of xa "vset_to_set evs \<union> vset_to_set ods" "origin_lookup orngs"]
              UnCI[of xa "vset_to_set ods" "vset_to_set evs"]
        by auto
      have sg3: 
        "\<lbrakk>\<forall>x\<in>vset_to_set rts - {u}. origin_lookup orngs xa \<noteq> Some x;
          x = origin_lookup orngs xa;  the (origin_lookup orngs xa) \<noteq> u;
          xa \<in> vset_to_set ods\<rbrakk> \<Longrightarrow> False" for xa
        using invar_basic_F(15,6)  imageI[of xa "vset_to_set evs \<union> vset_to_set ods" "origin_lookup orngs"]
              UnCI[of xa "vset_to_set ods" "vset_to_set evs"]
        by auto
      have sg4: 
        "\<lbrakk>\<forall>x\<in>vset_to_set evs \<union> vset_to_set ods - insert u (set p1).
         (x \<in> vset_to_set ods \<or> x \<in> vset_to_set evs) \<and> the (origin_lookup orngs x) = u \<or>
          x \<notin> vset_to_set ods \<and> x \<notin> vset_to_set evs \<and>
         (x = new_vert \<or> x \<noteq> new_vert \<and> Some xa \<noteq> origin_lookup orngs x) \<or>
          the (origin_lookup orngs x) \<noteq> u \<and>
         (x = new_vert \<or> x \<noteq> new_vert \<and> Some xa \<noteq> origin_lookup orngs x);
          x = Some xa; xa \<in> vset_to_set rts; xa \<noteq> new_vert\<rbrakk> \<Longrightarrow> xa = u" for xa
       using invar_basic_F(10) invar_rootsD_here(1) p1_no_roots 
       by(auto dest!: bspec)
      show ?case
        using h1 1
        by (auto intro: sg2 sg3 sg4 dest: sg2 sg3)
    next
      case 2
      hence h1: "the (origin_lookup orngs u) \<noteq> u"
        using org_lookup_last by force
      obtain ou where ou:"origin_lookup orngs u = Some ou"
        using assms(4) Un_iff[of u "vset_to_set evs" "vset_to_set ods"]
              invar_basic_F(15,6)
        by auto
      have sg1: "\<lbrakk>origin_lookup orngs u = Some ou; x = Some ou\<rbrakk> \<Longrightarrow> ou \<in> vset_to_set rts"
        using assms(4) Un_iff[of u "vset_to_set evs" "vset_to_set ods"] 
              invar_basic_F(15,6)
              imageI[of u "vset_to_set evs \<union> vset_to_set ods" "origin_lookup orngs"]
        by auto
      have sg2: "\<lbrakk>\<forall>x\<in>vset_to_set rts. origin_lookup orngs xa \<noteq> Some x;
                 xa \<in> vset_to_set evs\<rbrakk> \<Longrightarrow> xa = u" for xa
        using Un_iff[of xa "vset_to_set evs" "vset_to_set ods"] invar_basic_F(15,6)
             imageI[of xa "vset_to_set evs \<union> vset_to_set ods" "origin_lookup orngs"]
        by auto
      have sg3: "\<lbrakk>\<forall>x\<in>vset_to_set rts. origin_lookup orngs xa \<noteq> Some x; xa \<in> vset_to_set ods\<rbrakk>
                  \<Longrightarrow> xa = u" for xa
        using image_iff[of "origin_lookup orngs xa" "origin_lookup orngs"
                           "vset_to_set evs \<union> vset_to_set ods"] invar_basic_F(15,6)
        by auto
      have sg4: 
        "\<lbrakk>origin_lookup orngs u = Some ou; xa \<in> vset_to_set rts;
          \<forall>x\<in>vset_to_set evs \<union> vset_to_set ods - insert u (set p1).
             x = new_vert \<and> xa \<noteq> ou \<or> x \<noteq> new_vert \<and> Some xa \<noteq> origin_lookup orngs x\<rbrakk>
          \<Longrightarrow> xa = ou" for xa
        using assms(6) forest_invar_F(6) invar_basic_F(10) invar_rootsD_here p1_no_roots
        by(auto dest: bspec)
      show ?case 
        using ou 2 by (auto intro: sg1 sg2 sg3 sg4)
    qed  
  qed

  show new_evs_are: "vset_to_set (evens new_forest) = vset_to_set evs - set (p1@[u])\<union> {new_vert} "
    using effect_of_contract_path(8) evens_in_p_are by auto
  show new_ods_are: "vset_to_set (odds new_forest) = vset_to_set ods - set (p1@[u])"
    using effect_of_contract_path(7) odds_in_p_are by auto
  have invar_even_to_parent_matching_after: 
    "invar_even_to_parent_matching (quot_graph contr \<M> - {{new_vert}}) new_forest"
  proof(rule invar_even_to_parent_matchingI, goal_cases)
    case (1 u' v')
    then show ?case 
      unfolding new_evs_are
    proof(elim UnE, goal_cases)
      case 1
      hence not_P:"\<not> (u' = new_vert \<and> parent_lookup prnts u \<noteq> None)" 
        using assms(6) by blast
      from 1 show ?case 
        unfolding new_parents_are if_not_P[OF not_P]
      proof(subst (asm) if_not_P, goal_cases)
        case 1
        then show ?case 
using invar_basic_F(7) by auto
      next
        case 2
        then show ?case 
      proof(cases "u' \<in> set (p1 @ [u])", goal_cases)
        case 2
        note 2 = 2[simplified if_not_P[OF 2(3)]]
        moreover have e_in_M: "{u', v'} \<in> \<M>"
          using calculation(1,2) invar_even_to_parent_matchingD_here by auto
        moreover have "{u', v'} =  contr `{u', v'}"
        proof(rule matching_edge_rev_alt_path_cases[OF 
              rev_alt_path_M e_in_M assms(7) assms(5)], goal_cases)
          case (1 u'' v'' i)
          have "{u', v'} \<in> set (edges_of_path (p1 @ [u]))"
            using 1(3)
            by(auto intro!: nth_mem[of i "edges_of_path (p1 @ [u])"] 
                  simp add: 1(4)[symmetric] edges_of_path_length)
          then show ?case 
            using calculation(3) edge_not_in_edges_in_path by fastforce
        next
          case (2 u v)
          then show ?case 
            using assms(4) calculation(1,2) invar_basic_F(7) parents_ev_od(1)[of u' u]
            by (auto simp add: doubleton_eq_iff)
        qed (auto simp add: contr_def)
        moreover hence "{u', v'} \<noteq> {new_vert}"
          using calculation(1) prnts_no_loop by (auto simp add: contr_def)
        ultimately show ?case
          by (auto intro!: bexI[of _ "{u', v'}"] simp add: quot_graph_def )
      qed auto
    qed
    next
      case 2
      hence "u' = new_vert" by auto
      then show ?case
        using 2(1)
        unfolding new_parents_are
      proof(cases "parent_lookup prnts u = None", goal_cases)
        case 1
        hence cond_not: "\<not> (u' = new_vert \<and> parent_lookup prnts u \<noteq> None)" by auto
        from 1 show ?case 
          unfolding if_not_P[OF cond_not]
        proof(cases "u' \<notin> set (p1 @ [u]) \<and>
                     the (parent_lookup prnts u') \<in> set (p1 @ [u]) \<inter> vset_to_set evs \<and>
                     u' \<in> vset_to_set ods - set (p1 @ [u])", goal_cases)
          case 1
          note 1 = 1[simplified if_P[OF 1(4)]]
          then show ?case 
            using assms(6) by force
        next
          case 2
          note 2 = 2[simplified if_not_P[OF 2(4)]]
          hence u'_not_in_p:"u' \<notin> set (p1 @ [u])" by force
          note 2 = 2[simplified if_not_P[OF u'_not_in_p]] u'_not_in_p
          moreover hence "new_vert \<in> Vs (abstract_forest (Forest rts evs ods prnts orngs))"
            using invar_basic_F(14) by auto
          ultimately show ?case
            using assms(6) invar_basic_F(6) by auto
        qed
      next
        case 2
        note two = 2
        then show ?case 
        proof(subst (asm) if_P, goal_cases)
          case 2
          hence "v' \<in> vset_to_set ods"
            using assms(4) parents_ev_od(1) by force
          then show ?case 
            using 2(2) two(1) M_quot lookup_u_not_none_roots by simp
        qed simp
      qed
    qed
  qed

  have invar_odd_is_parent_after: "invar_odd_is_parent new_forest"
  proof(rule invar_odd_is_parentI, goal_cases)
    case (1 u')
    then obtain v' where v': "parent_lookup prnts v' = Some u'"
      using forest_invar_F(8)
      by(auto dest!: invar_odd_is_parentD simp add: new_ods_are)
    moreover hence "v' \<in> vset_to_set evs" 
      using "1" new_ods_are parents_ev_od(1) by auto
    ultimately show ?case
      using 1
      unfolding new_ods_are new_parents_are
    proof(cases "v' = u", goal_cases)
      case 1
      show ?case 
        using "1"(4) v' by auto
    next
      case 2
      note two = this
      hence u'v'_in_M:"{u', v'} \<in> \<M>"
        using forest_invar_F(5)
        by(auto dest!: invar_even_to_parent_matchingD simp add: insert_commute)    
      show ?case 
      proof(rule exI[of _ v'], rule matching_edge_rev_alt_path_cases[OF 
            rev_alt_path_M u'v'_in_M assms(7) assms(5)], goal_cases)
        case (1 u'' v'' i)
        then show ?case
          using two(3) edges_of_path_length[of "p1 @ [u]"]
            nth_mem[of i "edges_of_path (p1 @ [u])"]
            v_in_edge_in_path[of u' v' "p1 @ [u]"] 
          by auto
      next
        case (2 u'' v'')
        then show ?case 
          using two(3,4) by (auto simp add: doubleton_eq_iff)
      next
        case 3
        then show ?case 
          using assms(6) two(2) v' by auto
      qed
    qed
  qed

  have roots_unmatched_after: 
    "vset_to_set (roots new_forest) \<inter> Vs (quot_graph contr \<M> - {{new_vert}}) = {}"
    unfolding effect_of_contract_path(7,8) 
      evens_in_p_are odds_in_p_are effect_of_contract_path(6)
  proof(goal_cases)
    case 1
    have sg1: 
      "\<lbrakk>u \<in> vset_to_set rts; new_vert \<in> Vs (quot_graph contr \<M> - {{new_vert}})\<rbrakk> \<Longrightarrow> False"
      proof(goal_cases)
      case 1 
      note one = this
      then obtain e where e: "e \<in> \<M> - set (edges_of_path (p1 @ [u]))" "new_vert \<in> e" 
        "\<And> e'. \<lbrakk>e' \<in> \<M> - set (edges_of_path (p1 @ [u])); new_vert \<in> e'\<rbrakk> \<Longrightarrow> e = e'"
        using matching_unique_match[OF assms(5)]
        by(auto simp add: M_quot vs_member)
      show ?case 
      proof(cases rule: matching_edge_rev_alt_path_cases[OF rev_alt_path_M, of e])
        case 1
        then show ?case
          using e(1) by fastforce
      next
        case 2
        then show ?case
          by (simp add: assms(7))
      next
        case 3
        then show ?case 
          by (simp add: assms(5))
      next
        case (4 u'' v'' i)
        then show ?thesis 
          using e(1) nth_mem[of i "edges_of_path (p1 @ [u])"]
          by (auto simp add: edges_of_path_length)
      next
        case (5 u' v')
        hence "u' \<notin> vset_to_set rts" "v' \<notin> vset_to_set rts"
          using e(1) "5"(5) invar_basic_F(11) 
          by (auto dest: edges_are_Vs_2 edges_are_Vs)
        then show ?thesis
          using one(1)
          by (simp add: "5"(2))
      next
        case 6
        then show ?thesis
          using assms(6) e(1,2) by blast
      qed
    qed
    have sg2: 
     "\<lbrakk>u \<in> vset_to_set rts;x \<in> Vs (quot_graph contr \<M> - {{new_vert}});
       x \<in> vset_to_set rts\<rbrakk> \<Longrightarrow> x = u" for x
    using invar_basic_F(11) subsetD[OF Vs_subset[of "\<M> - _" \<M>, simplified]]
    by (auto simp add: M_quot)
  have sg3: "\<lbrakk>u \<notin> vset_to_set rts;x \<in> vset_to_set rts;
       x \<in> Vs (quot_graph contr \<M> - {{new_vert}})\<rbrakk> \<Longrightarrow> False" for x
    unfolding M_quot 
  proof((subst (asm) if_not_P, assumption)+, elim vs_member_elim, goal_cases)
    case (1 e)
    then show ?case 
    proof(elim UnE, goal_cases)
      case 1
      then show ?case
        using inf_sup_aci(1) insert_absorb invar_basic_F(11) by auto
    next
      case 2
      hence "{u, the (parent_lookup prnts u)} \<in> \<M>"
        by (simp add: assms(4) invar_even_to_parent_matchingD_here lookup_u_not_none_roots)
      then show ?case
        using assms(6) "2"(2,3,4) invar_basic_F(10,11) p1_no_roots
          vs_member_intro[of new_vert "{new_vert, the (parent_lookup prnts u)}" \<M>]
          vs_member_intro[of x "{u, the (parent_lookup prnts u)}" \<M>]
        by auto
    qed
  qed  
    show ?case
      by (auto intro: sg1 sg2 sg3)
  qed

  have unmatched_forest_Vs_are_roots:
    "Vs (abstract_forest new_forest) - Vs (quot_graph contr \<M> - {{new_vert}})
    \<subseteq> vset_to_set (roots new_forest)"
  proof(rule , rule ccontr, goal_cases)
    case (1 x)
    then obtain y where y: "parent_lookup (parents new_forest) x = Some y"
      using dom_samer org_lookup_helper
           imageI[of x "vset_to_set (roots new_forest) \<union> Vs (abstract_forest new_forest)"
          "origin_lookup (origins new_forest)"] 
      by(cases "parent_lookup (parents new_forest) x") auto
    then show ?case 
    proof(cases "x \<in> vset_to_set (evens new_forest)")
      case True
      then show ?thesis 
        using invar_even_to_parent_matching_after y 1(1)
        by(auto dest!: invar_even_to_parent_matchingD)
    next
      case False
      hence x_odd: "x \<in> vset_to_set (odds new_forest)"
        using "1"(1) Vs_evens_odds_roots_helper by auto
      then obtain y where y: "parent_lookup (parents new_forest) y = Some x"
        using invar_odd_is_parent_after
        by(auto dest!: invar_odd_is_parentD) 
      hence y_even:  "y \<in> vset_to_set (evens new_forest)"
        using assms(6)  new_ods_are parents_ev_od(1) x_odd 
        by(auto simp add: new_evs_are new_parents_are if_split[of "\<lambda> x. x = Some _"])
      hence "{x, y} \<in> quot_graph contr \<M> - {{new_vert}}"
        using invar_even_to_parent_matching_after y
        by(auto dest!: invar_even_to_parent_matchingD simp add: insert_commute)
      then show ?thesis
        using 1(1) by(auto dest: edges_are_Vs)
    qed
  qed

  have invar_basic_after: "invar_basic (quot_graph contr \<M> - {{new_vert}}) new_forest"
  proof(rule invar_basicI[OF effect_of_contract_path(1,2,3,4,5)], goal_cases)
    case 1
    then show ?case 
      using Vs_evens_odds_roots_helper by simp
  next
    case 2
    then show ?case 
      using assms(6) invar_basic_F(7)
      unfolding effect_of_contract_path(7,8) 
        evens_in_p_are odds_in_p_are effect_of_contract_path(6)
      by auto
  next
    case 3
    then show ?case 
      unfolding effect_of_contract_path(7,8) 
        evens_in_p_are odds_in_p_are effect_of_contract_path(6)
      using invar_basic_F(8) by auto
  next
    case 4
    then show ?case 
      unfolding effect_of_contract_path(7,8) 
        evens_in_p_are odds_in_p_are effect_of_contract_path(6)
      using invar_basic_F(9) by auto
  next
    case 5
    then show ?case 
      using invar_basic_F(10) p1_no_roots
      unfolding effect_of_contract_path(7,8) 
        evens_in_p_are odds_in_p_are effect_of_contract_path(6)
      by auto
  next
    case 6
    then show ?case
      using roots_unmatched_after by force
  next
    case 7
    have c1: "card (vset_to_set ods - vset_to_set ods \<inter> set (p1 @ [u])) = 
         card (vset_to_set ods) - card (vset_to_set ods \<inter> set (p1 @ [u]))"
      by (simp add: card_Diff_subset)
    have le1: "card (vset_to_set ods) \<ge> card (vset_to_set ods \<inter> set (p1 @ [u]))"
      by (simp add: card_mono invar_basic_F(9))
    have c3: "card (vset_to_set evs - vset_to_set evs \<inter> set (p1 @ [u]) \<union> {new_vert}) = 
             1 + card (vset_to_set evs) - card (vset_to_set evs \<inter> set (p1 @ [u]))" 
      using assms(6)
      by (subst card_Un_disjoint[of _ "{new_vert}"])
         (auto simp add: card_Diff_subset Suc_diff_le card_mono invar_basic_F(8))
    have le2: "card (vset_to_set evs) \<ge> card (vset_to_set evs \<inter> set (p1 @ [u]))"
      by (simp add: card_mono invar_basic_F(8))
    have c4: "card (vset_to_set evs \<inter> set (p1 @ [u])) = 1+ card (vset_to_set ods \<inter> set (p1 @ [u]))"
      unfolding evens_in_p_are[symmetric] odds_in_p_are[symmetric]
    proof(goal_cases)
      case 1
      have " card {(p1 @ [u]) ! i |i. i < length (p1 @ [u]) \<and> even i} = 
             card { i |i. i < length (p1 @ [u]) \<and> even i}"
       using distinct_path
       by(subst card_image[of "\<lambda> i. (p1 @ [u]) ! i", symmetric])
         (auto simp add: inj_on_def nth_eq_iff_index_eq intro!: arg_cong[of _ _ card])
      moreover have "card { i |i. i < length (p1 @ [u]) \<and> even i} =
                 card { i |i. i < length (p1 @ [u]) \<and> odd i} + 1"
        unfolding card_of_odd_numbers_upto card_of_even_numbers_upto
        using odd_length_p by auto
      moreover have " card {(p1 @ [u]) ! i |i. i < length (p1 @ [u]) \<and> odd i} = 
             card { i |i. i < length (p1 @ [u]) \<and> odd i}"
        using distinct_path
        by(subst card_image[of "\<lambda> i. (p1 @ [u]) ! i", symmetric])
          (auto simp add: inj_on_def nth_eq_iff_index_eq intro!: arg_cong[of _ _ card])
      ultimately show ?case by simp
    qed
    show ?case 
      unfolding effect_of_contract_path(7,8) 
        evens_in_p_are odds_in_p_are effect_of_contract_path(6)
        c1 c3 c4
    proof (cases "last (p1 @ [u]) \<in> vset_to_set rts", goal_cases)
      case 1
      have c2: "card (vset_to_set rts - {last (p1 @ [u])} \<union> {new_vert}) = 
           card (vset_to_set rts)"
      proof(subst card_Un_disjoint, goal_cases)
        case 1
        then show ?case 
          using infinite_super invar_basic_F(10,8) by auto
      next
        case 3
        then show ?case 
          using DiffI assms(6) invar_basic_F(10) p1_no_roots by auto
      next
        case 4
        then show ?case 
          using 1 infinite_super invar_basic_F(10,8)
          by(fastforce intro!: Suc_pred simp add: card_Diff_singleton )
      qed simp
      from 1 show ?case 
        using le1 le2 c2 invar_basic_F(12) by auto  
    next
      case 2
      then show ?case
        using le1 le2 invar_basic_F(12) by auto  
    qed
  next
    case 8
    show ?case
      by (simp add: dom_samer)
  next
    case 9
    then show ?case 
      by(auto simp add: abstract_forest_def)
  next
    case 10
    then show ?case
      using org_lookup_helper by blast
  next
    case 11
    then show ?case
      using unmatched_forest_Vs_are_roots by simp
  next
    case 12
    have " finite (Vs (abstract_forest (Forest rts evs ods prnts orngs)))"
      using invar_basic_F(6,8,9) finite_Un[of "vset_to_set evs" "vset_to_set ods"]
        finite_Un[of "vset_to_set rts"_]
      by auto
    then show ?case 
      using  Vs_contracted 
      by(auto intro!: finite_Vs_then_finite 
                      finite_subset[of "Vs (abstract_forest new_forest)"
                        "Vs (abstract_forest new_forest) \<union> {new_vert}",
                        simplified Vs_contracted])
  next
    case 13
    thus ?case
      by(auto intro!: dblton_graph_contract_into_one_vert[where S = "set (p1 @ [u])"]
            simp add: invar_basic_F(18) contr_def  quot_is_AF[symmetric])
  qed

  have invar_matching_both_or_none_after:
    "invar_matching_both_or_none (quot_graph contr \<M> - {{new_vert}}) new_forest"
  proof(rule invar_matching_both_or_noneI, goal_cases)
    case (1 u' v')
    then show ?case 
      unfolding M_quot
    proof(cases "u \<in> vset_to_set rts", goal_cases)
      case 1
      hence one: "{u', v'} \<in> \<M>" "{u', v'} \<notin> set (edges_of_path (p1 @ [u]))"
        by auto
      show ?case 
      proof(rule matching_edge_rev_alt_path_cases[OF 
            rev_alt_path_M one(1) assms(7) assms(5)], goal_cases)
        case (1 u'' v'' i)
        then show ?case
         using one(2) edges_of_path_length[of "p1 @ [u]"]
            nth_mem[of i "edges_of_path (p1 @ [u])"]
         by auto
      next
        case (2 u'' v'')
        then show ?case 
          using "1"(2) one(1) invar_basic_F(11)
          by(auto dest: edges_are_Vs)
      next
        case 3
        hence u'_v'_not_in_p:"u' \<notin> set (p1@[u])" "v' \<notin> set (p1@[u])"
          by auto
        hence eq1: "contr u' = u'" "contr v' = v'" 
          by(auto simp add: contr_def)
        moreover have e2: "contr u'' = u' \<Longrightarrow> u'' = u'" for u''
          using "3" assms(6) one(1) by(cases " u'' \<in> set (p1 @ [u])") (auto simp add: contr_def)
        moreover have eq3: "contr v'' = v' \<Longrightarrow> v'' = v'" for v''
            using "3" assms(6) one(1) by(cases " v'' \<in> set (p1 @ [u])") (auto simp add: contr_def)
        ultimately have "e = {u', v'}"
          if "e \<in> abstract_forest (Forest rts evs ods prnts orngs)"
            "contr ` e = {u', v'}" for e
          using that (2) 
          by auto (force intro: imageE[of u' contr e "u' \<in> e"] imageE[of v' contr e "v' \<in> e"])+
        hence AF_equiv:"{u', v'} \<in> abstract_forest new_forest \<longleftrightarrow> 
                 {u', v'} \<in> abstract_forest (Forest rts evs ods prnts orngs)"
          using "1"(1)[simplified M_quot[symmetric]]
          by (auto intro!: bexI[of _ "{u', v'}"] 
                 simp add: eq1 quot_graph_def quot_is_AF[symmetric])
        have disjoint_AF_equiv:
          "{u', v'} \<inter> (Vs (abstract_forest new_forest) \<union> vset_to_set (roots new_forest)) = {}
               \<longleftrightarrow> 
           {u', v'} \<inter> (Vs (abstract_forest (Forest rts evs ods prnts orngs)) 
                     \<union> vset_to_set rts) = {}"
          using invar_basic_F(6)  assms(4) u'_v'_not_in_p assms(6) one(1) 
          by (unfold Vs_evens_odds_roots_helper[simplified Un_commute[of 
                "vset_to_set (roots new_forest)"], symmetric])
             (auto simp add: new_evs_are new_ods_are )
        show ?case 
          using invar_matching_both_or_noneD_here[OF one(1)] 
          by(unfold AF_equiv disjoint_AF_equiv)
      qed
    next
      case 2
      then obtain up where up: "parent_lookup prnts u = Some up"
        using lookup_u_not_none_roots by blast
      then show ?case 
      proof(cases "{u', v'} = {new_vert, the (parent_lookup prnts u)}")
        case True
        have "{new_vert, the (parent_lookup prnts u)} = contr ` {u, the (parent_lookup prnts u)}"
         using "2"(2) lookup_u_not_none_roots prnts_no_loop up
                distinct_path  assms(2) up follow_subsequent_parent_there[of v p1 u p2 up]
         by(auto simp add: contr_def in_set_conv_decomp[of up] up)
        hence "{u', v'} \<in> abstract_forest new_forest"
          using True quot_is_AF[symmetric] 1 up 
          by(auto intro!:  bexI[of _ "{u, up}"] simp add: quot_graph_def abstract_forest_def)
        then show ?thesis by simp
      next
        case False
        hence two: "{u', v'} \<in> \<M>" "{u', v'} \<notin> set (edges_of_path (p1 @ [u]))"
          "u \<notin> vset_to_set rts"  
          using  M_quot 2 by auto
        show ?thesis
        proof(rule matching_edge_rev_alt_path_cases[OF 
              rev_alt_path_M two(1) assms(7) assms(5)], goal_cases)
          case (1 u'' v'' i)
          then show ?case
            using two(2) edges_of_path_length[of "p1 @ [u]"]
              nth_mem[of i "edges_of_path (p1 @ [u])"] 
            by auto
        next
          case (2 u'' v'')
          then show ?case 
            using 1 False assms(4) invar_even_to_parent_matchingD_here two(3) up 
            by (auto dest: doubleton_in_matching(1)[OF assms(5)] simp add: M_quot)
        next
          case 3
          hence u'_v'_not_in_p:"u' \<notin> set (p1@[u])" "v' \<notin> set (p1@[u])"
            by auto
          hence eq1: "contr u' = u'" "contr v' = v'" 
            by(auto simp add: contr_def)
          moreover have e2: "contr u'' = u' \<Longrightarrow> u'' = u'" for u''
            using "3" assms(6) two(1) 
            by(cases " u'' \<in> set (p1 @ [u])") (auto simp add: contr_def)
          moreover have eq3: "contr v'' = v' \<Longrightarrow> v'' = v'" for v''
            using "3" assms(6) two(1) 
            by(cases " v'' \<in> set (p1 @ [u])") (auto simp add: contr_def)
          ultimately have "e = {u', v'}"
            if "e \<in> abstract_forest (Forest rts evs ods prnts orngs)"
              "contr ` e = {u', v'}" for e
            using that (2) 
            by auto (force intro: imageE[of u' contr e "u' \<in> e"] imageE[of v' contr e "v' \<in> e"])+
          hence AF_equiv:"{u', v'} \<in> abstract_forest new_forest \<longleftrightarrow> 
                 {u', v'} \<in> abstract_forest (Forest rts evs ods prnts orngs)"
            using "1"(1)[simplified M_quot[symmetric]]
            by (auto intro!: bexI[of _ "{u', v'}"] 
                   simp add: eq1 quot_graph_def quot_is_AF[symmetric])   
          have disjoint_AF_equiv:
            "{u', v'} \<inter> (Vs (abstract_forest new_forest) \<union> vset_to_set (roots new_forest)) = {}
               \<longleftrightarrow> 
               {u', v'} \<inter> (Vs (abstract_forest (Forest rts evs ods prnts orngs)) 
                     \<union> vset_to_set rts) = {}"
            using invar_basic_F(6)  assms(4) u'_v'_not_in_p assms(6) two(1) 
            by (unfold Vs_evens_odds_roots_helper[simplified Un_commute[of 
                "vset_to_set (roots new_forest)"], symmetric])
               (auto simp add: new_evs_are new_ods_are )
          show ?case 
            using invar_matching_both_or_noneD_here[OF two(1)] 
            by(unfold AF_equiv disjoint_AF_equiv)
        qed
      qed
    qed
  qed

  have invar_forest_even_and_odd_after: "invar_forest_even_and_odd new_forest"
  proof(rule invar_forest_even_and_oddI, goal_cases)
    case (1 u' v')
    then obtain e where e: "e\<in>abstract_forest (Forest rts evs ods prnts orngs)"
      "{u', v'} = contr ` e" "contr ` e \<noteq> {new_vert}"
      by(unfold quot_is_AF[symmetric] quot_graph_def) blast
    moreover then obtain u'' v'' where u''_v'': "e = {u'', v''}" "u'' \<noteq> v''"
      using abstract_forest_dblton_graph assms(1) by force
    ultimately obtain u'' v'' where "u' = contr u''" "v' = contr v''"
      "u'' \<noteq> new_vert \<or> v'' \<noteq> new_vert" "{u'', v''} = e"
      by (auto simp add: doubleton_eq_iff)
    hence u''_v'':  "u' = contr u''" "v' = contr v''"
      "u'' \<noteq> new_vert \<or> v'' \<noteq> new_vert" 
      "{u'', v''} \<in> abstract_forest (Forest rts evs ods prnts orngs)"
      using u''_v'' e by auto
    moreover then have u''_v''_even_odd: "(u'' \<in> vset_to_set evs) = (v'' \<in> vset_to_set ods)"
      using forest_invar_F(3)
      by(auto dest!: invar_forest_even_and_oddD)
    have u''_v''_parent:"parent_lookup prnts u'' = Some v'' \<or> parent_lookup prnts v'' = Some u''"
      using u''_v''(4) by(auto simp add: abstract_forest_def doubleton_eq_iff)
    have alternative_case: "?case \<longleftrightarrow>
          (u' \<in> vset_to_set (odds new_forest)) = (v' \<in> vset_to_set (evens new_forest))"
      using "1"  Vs_evens_odds_roots_helper invar_basicD[OF invar_basic_after] edges_are_Vs_2[of v' u']
      by (auto dest: edges_are_Vs_2[of u' v']  simp add: insert_commute)
    have alternative_u''_v''_even_odd:
      "(v'' \<in> vset_to_set evs) = (u'' \<in> vset_to_set ods)"
      using parents_ev_od(1,2) u''_v''_parent by presburger
    have ?case if asm: "u'' \<notin> set (p1@[u])" "v'' \<notin> set (p1@[u])"
    proof-
      have "u' = u''" "v' = v''"
        using asm by(auto simp add: u''_v'' contr_def)
      thus ?case
        using  u''_v''_even_odd asm u''_v''(3) assms(6) invar_basic_F(6) u''_v''(4)
        by (auto simp add: new_evs_are new_ods_are dest: edges_are_Vs)
    qed
    moreover have ?case if asm: "u'' \<in> set (p1@[u])" "v'' \<notin> set (p1@[u])"
    proof-
      have "u' = new_vert" "v' = v''"
        using asm by(auto simp add: u''_v'' contr_def)
      moreover have 
         "\<lbrakk>v'' \<noteq> u; parent_lookup prnts u'' = Some v''; p1 = ys @ u'' # zs;
           v'' \<notin> set zs\<rbrakk> \<Longrightarrow> v'' \<in> vset_to_set ods" for ys zs
       using assms(2) follow_subsequent_parent_there[of v _ u'' "_@[u]@p2" v'']
             hd_append[of "[]" "u # p2"] hd_append[of zs "u # p2"]  by fastforce
     ultimately show ?case  
        using asm assms(4) u''_v''_even_odd  parent_adj_pu_helper[of v'' u'' ] u''_v''_parent
        by(auto simp add: in_set_conv_decomp[of u''] new_evs_are new_ods_are )+
    qed
    moreover have ?case if asm: "u'' \<notin> set (p1@[u])" "v'' \<in> set (p1@[u])"
      unfolding alternative_case
    proof(goal_cases)
      case 1
      have "v' = new_vert" "u' = u''"
        using asm by(auto simp add: u''_v'' contr_def)
      moreover hence "u' \<noteq> new_vert" 
        using e(2,3) by force
      moreover have 
        "\<lbrakk>u'' \<noteq> u;parent_lookup prnts v'' = Some u'';p1 = ys @ v'' # zs;
          u'' \<notin> set zs\<rbrakk> \<Longrightarrow> u'' \<in> vset_to_set ods" for ys zs
        using assms(2) follow_subsequent_parent_there[of v ys v'' "zs@[u]@p2" u'']
              hd_append[of zs "u # p2"] 
        by auto
      ultimately show ?case  
        using asm assms(4) alternative_u''_v''_even_odd parent_adj_pu_helper[of u'' v'' _ _ ] u''_v''_parent
        by(auto simp add: in_set_conv_decomp[of v''] new_evs_are new_ods_are)+
    qed
    moreover have False if asm: "u'' \<in> set (p1@[u])" "v'' \<in> set (p1@[u])"
    proof-
      have "v' = new_vert" "u' = new_vert"
        using asm by(auto simp add: u''_v'' contr_def)
      thus False
        using e(2,3) by auto
    qed
    ultimately show ?case
      by auto
  qed

  have parents_of_u_props: 
   "\<exists> pu ppu. parent_lookup prnts u = Some pu \<and> parent_lookup prnts pu = Some ppu
        \<and> pu \<notin> set (p1@[u]) \<and> ppu \<notin> set (p1@[u])"
    if "u \<notin> vset_to_set rts"
  proof-
    obtain pu where pu:"parent_lookup prnts u = Some pu"
      using \<open>u \<notin> vset_to_set rts\<close> lookup_u_not_none_roots by auto
    have "pu \<in> vset_to_set ods"
      using assms(4) parents_ev_od(1) pu by blast
    then obtain ppu where ppu: "parent_lookup prnts pu = Some ppu"
      using forest_invar_F(7)
      by (auto elim!: invar_odd_to_parent_non_matchingE)
    moreover have "pu \<notin> set (p1@[u])"
    proof(rule ccontr, unfold not_not, unfold in_set_conv_decomp, goal_cases)
      case 1
      then obtain ys zs where "p1 @ [u] = ys @ pu # zs" by auto
      thus False
        using  assms(2) pu
        by(cases zs rule: rev_cases)
          (auto intro: prnts_no_loop follow_not_again_parent[of v _ pu _ u p2])
    qed 
    moreover have "ppu \<notin> set (p1@[u])"
    proof(rule ccontr, unfold not_not, unfold in_set_conv_decomp, goal_cases)
      case 1
      then obtain ys zs where "p1 @ [u] = ys @ ppu # zs" by auto
      moreover obtain p2' where "p2 = pu#p2'"
        using assms(2) follow_subsequent_parent_there pu by blast
      ultimately show False
        using assms(2) ppu 
        by(auto intro!: follow_not_again_parent[of v ys ppu "zs" pu p2'])
    qed
    ultimately show ?thesis
      using pu by simp
  qed

  have invar_odd_to_parent_non_matching_after:
    "invar_odd_to_parent_non_matching (quot_graph contr \<M> - {{new_vert}}) new_forest"
  proof(rule invar_odd_to_parent_non_matchingI, goal_cases)
    case (1 u')
    note u'_odd = this
    then obtain v' where v': "parent_lookup (parents new_forest) u' = Some v'"
      using assms(6) invar_odd_to_parent_non_matchingE[OF forest_invar_F(7)]
      by(auto simp add: new_ods_are new_parents_are if_split[of "\<lambda> x. x = Some _"])
    moreover have "{u', v'} \<notin> quot_graph contr \<M> - {{new_vert}}"
    proof(rule ccontr, goal_cases)
      case 1
      hence u'_v'_in_quot:"{u', v'} \<in> quot_graph contr \<M> - {{new_vert}}" by auto
      then show ?case 
        unfolding M_quot
      proof(cases "u \<in> vset_to_set rts", goal_cases)
        case 1
        hence one: "{u', v'} \<in> \<M>" "{u', v'} \<notin> set (edges_of_path (p1 @ [u]))"
          "u \<in> vset_to_set rts"
          by auto
        show ?thesis 
        proof(rule matching_edge_rev_alt_path_cases[OF 
              rev_alt_path_M one(1) assms(7) assms(5)], goal_cases)
          case (1 u'' v'' i)
          hence "{u', v'} \<in> set (edges_of_path (p1@[u]))"
            using edges_of_path_length[of "p1 @ [u]"] nth_mem[of i "edges_of_path (p1 @ [u])"]
            by auto
          then show ?case 
            using one(2) by simp
        next
          case (2 u'' v'')
          then show ?case 
            using one(1,3) invar_basic_F(11) edges_are_Vs[of u v'' \<M>]
            by auto
        next
          case 3
          moreover have "\<not> (\<exists>y. parent_lookup prnts u = Some y)"
            by (simp add: lookup_u_not_none_roots one(3))
          ultimately have "parent_lookup prnts u' = Some v'"
            using v' assms(6) edges_are_Vs_2  one(1) 
            by(auto simp add: new_parents_are if_split[of "\<lambda> x. x = Some _"])
          then show ?case 
            using invar_odd_to_parent_non_matchingD_here new_ods_are one(1) u'_odd 
            by auto
        qed
      next
        case 2
        note 2 = 2[simplified if_not_P[OF 2(2)]]
        have v'_even: "v' \<in> vset_to_set (evens new_forest)" 
          using assms(6) effect_of_contract_path(8) evens_in_p_are 
                parents_ev_od(2) u'_odd v'
          by(auto simp add: new_ods_are new_parents_are if_split[of "\<lambda> x. x = Some _"])
        have u'_old_odd:"u' \<in> vset_to_set ods"
          using new_ods_are u'_odd by force
        have u_pu_in_M:"{u, the (parent_lookup prnts u)} \<in> \<M>"
          using "2"(2) assms(4) invar_even_to_parent_matchingD_here
            lookup_u_not_none_roots by auto
        show ?thesis 
        proof(cases "{u', v'} = {new_vert, the (parent_lookup prnts u)}")
          case True
          hence u'_v'_are: "u' = the (parent_lookup prnts u)" "v' = new_vert" 
            using assms(6) new_ods_are u'_odd True 
            by (fastforce simp add: doubleton_eq_iff)+
          moreover hence parent_u':
             "parent_lookup (parents new_forest) u' = parent_lookup prnts u'"
            using 1 new_ods_are u'_odd  parents_of_u_props[OF 2(2)] 
            by (force simp add:  new_parents_are)
          hence "{the (parent_lookup prnts u), u} \<in> \<M>"
            using "2"(2) assms(4) invar_even_to_parent_matchingD_here lookup_u_not_none_roots
            by(auto simp add: insert_commute)
          moreover have "the (parent_lookup prnts u) \<in> vset_to_set ods" 
            using u'_old_odd u'_v'_are(1) by auto
          ultimately show ?thesis
            using "2"(2) assms(6) parent_u' parents_ev_od(2) parents_of_u_props v' by fastforce
        next
          case False
          hence u'_v'_props:
            "{u', v'} \<in> \<M>" "{u', v'} \<noteq> {u, the (parent_lookup prnts u)}"
            "{u', v'} \<notin> set (edges_of_path (p1 @ [u]))"
            using "2"(1) by fastforce+
          show False
          proof(rule matching_edge_rev_alt_path_cases[OF 
                rev_alt_path_M u'_v'_props(1) assms(7) assms(5)], goal_cases)
            case (1 u'' v'' i)
            then show ?case
              using u'_v'_props(3) edges_of_path_length[of "p1 @ [u]"]
                nth_mem[of i "edges_of_path (p1 @ [u])"]
              by auto
          next
            case (2 u'' v'')
            hence "v'' = the (parent_lookup prnts u)" 
              using u_pu_in_M  doubleton_in_matching(1)[OF assms(5)] u'_v'_props(1)
              by auto
            then show ?case 
              using "2"(2,5) u'_v'_props(2) by force
          next
            case 3
            hence v'_even_old: "v' \<in> vset_to_set evs"
              using assms(6) edges_are_Vs_2 effect_of_contract_path(8) u'_v'_props(1) v'_even
              by fastforce
            moreover hence parent_u':
               "parent_lookup (parents new_forest) u' = parent_lookup prnts u'"
              using 3 assms(6) u'_odd v' 
                by (auto simp add: new_ods_are new_parents_are if_split[of "\<lambda> x. x = Some _"])
            then show ?case
              using forest_invar_F(7) invar_odd_to_parent_non_matchingD u'_old_odd u'_v'_props(1) v'
              by fastforce
          qed
        qed
      qed
    qed
    ultimately show ?case by fast
  qed

  have parent_rel_is_DAF:"{(x, y) |x y. Some x = parent_lookup (parents new_forest) y} = 
       Dabstract_forest new_forest"
    by(auto simp add: Dabstract_forest_def)

  have new_vert_not_Dabstract:
    "new_vert \<notin> dVs (Dabstract_forest (Forest rts evs ods prnts orngs)) - set (p1 @ [u])"
    using assms(6) invar_basic_F(6) 
    by(auto simp add: dVs_Vs_Dabstract_abstract_forest)

  have self_gamma_false:
    "u \<in> \<gamma>\<^sup>- Dabstract_forest (Forest rts evs ods prnts orngs) u \<Longrightarrow>False"
    "u \<in> \<gamma>\<^sup>+ Dabstract_forest (Forest rts evs ods prnts orngs) u \<Longrightarrow>False"for u
    by(auto intro!: DAF_no_loop[of u] simp add: gamma_minus_def gamma_plus_def)

  have invar_parent_wf_after:
    "invar_parent_wf new_forest"
  proof(rule invar_parent_wfI, rule parent_specI, goal_cases)
    case 1
    show ?case
    proof(cases "u = v")
      case True
      hence p1_empty: "p1 = []" 
        using distinct_path singletonI[of u] hd_p1
        by force
      show ?thesis 
      proof(cases "u = new_vert", goal_cases)
        case 1
        hence "contr = id"
          using  p1_empty
          by(auto intro!: ext simp add: contr_def)
        hence "Dabstract_forest new_forest = 
              Dabstract_forest (Forest rts evs ods prnts orngs)"
          unfolding Qquot_in_Dabstract_forest_new[symmetric]
          by (auto intro: DAF_no_loop simp add: Dquot_id)
        then show ?case 
          using forest_invar_F(4) invar_parent_Dabstract_forest_wf 
          by (unfold parent_rel_is_DAF) auto
      next
        case 2
        note u_not_new = this
        show ?case 
        proof(rule wf_vert_replace[of "Dabstract_forest 
                  (Forest rts evs ods prnts orngs)" new_vert _ u], goal_cases)
          case 1
          then show ?case
            using finite_abstract_Dabstract_forest invar_basic_F(17) by blast
        next
          case 2
          then show ?case 
            using forest_invar_F(4) invar_parent_Dabstract_forest_wf by blast
        next
          case 3
          then show ?case 
            using UnCI assms(6) insert_Diff invar_basic_F(6) p1_empty u_not_new 
            by (auto simp add: dVs_Vs_Dabstract_abstract_forest)
        next
          case 4
          then show ?case 
            unfolding parent_rel_is_DAF  Qquot_in_Dabstract_forest_new[symmetric]
              Dquot_graph_alt_def[OF contr_def new_vert_not_Dabstract] p1_empty
              append.append_Nil set_singleton_list Gamma_singleton
            by (auto intro: self_gamma_false)
        qed
      qed
    next
      case False
      hence "\<not> follow (parent_lookup prnts) v = [v]"
        using set_singleton_list[of v] in_set_conv_decomp[of u "p1 @ u # p2"] assms(2)
        by fastforce
      hence vwalk_bet_p:"vwalk_bet (Dabstract_forest (Forest rts evs ods prnts orngs)) (last ([u]@p2))
             (rev (p1@[u]@p2)) v"
        using follow_valk_bet[of v] 
        unfolding assms(2) Dabstract_forest_def alt_forest.sel(4)
        by(intro vwalk_bet_rev) auto
      show ?thesis 
      proof(rule wf_contract(1)[of "Dabstract_forest (Forest rts evs ods prnts orngs)"
            u "rev (p1@[u])" v new_vert], goal_cases)
        case 1
        then show ?case 
          using finite_abstract_Dabstract_forest invar_basic_F(17) by blast
      next
        case 2
        then show ?case 
          using forest_invar_F(4) invar_parent_Dabstract_forest_wf by fastforce
      next
        case 3
        then show ?case
          using vwalk_bet_p split_vwalk vwalk_bet3
          by (cases p2) fastforce+
      next
        case 4
        then show ?case
          using distinct_path by force
      next
        case 5
        then show ?case
          using new_vert_not_Dabstract by fastforce
      next
        case (6 x y z)
        then show ?case 
          by(auto simp add: Dabstract_forest_def dest!: sym[of "Some y"])
      next
        case 7
        then show ?case
          unfolding parent_rel_is_DAF  Qquot_in_Dabstract_forest_new[symmetric]
            Dquot_graph_alt_def[OF contr_def new_vert_not_Dabstract]
          by simp
      qed
    qed
  qed

  interpret parents_new: parent "(parent_lookup (parents new_forest))"
    by (simp add: follow_dom_invar_parent_wf(1) invar_parent_wf_after)
  have " parent_spec_i.follow_dom (parent_lookup (parents new_forest)) v" for v
    by (simp add: parents_new.follow_dom) 
  have follow_new_induct:
    " (\<And>v. (\<And>x2. parent_lookup (parents new_forest) v = Some x2 \<Longrightarrow> P x2) \<Longrightarrow> P v) \<Longrightarrow>
        P a" for P a
    using parent_spec_i.follow.pinduct parents_new.follow_dom by metis
  note follow_new_simps = parent_spec_i.follow.psimps[OF parents_new.follow_dom]
  note follow_new_last_Cons=parents_new.follow_last_Cons[folded follow_def]
  note new_follow_cong = follow_cong[folded follow_def]

  have lookup_self_implies_root:
    "origin_lookup (origins new_forest) r = Some r" 
    if "r \<in> vset_to_set (roots new_forest)" for r
  proof -
    have "r \<noteq> last (p1 @ [u]) \<or> r \<noteq> the (Some r) \<or> the (origin_lookup orngs (last (p1 @ [u]))) \<noteq> the (Some r) \<or> last (p1 @ [u]) = the (origin_lookup orngs (last (p1 @ [u])))"
      by argo
    thus ?thesis 
      using org_lookup_last that p1_no_roots assms(6) invar_basic_F(10)
      by(auto simp add: effect_of_contract_path(10,6) if_split[of "\<lambda> x. x = Some _"]
                        invar_rootsD_here(1))
  qed

  have parent_same_org_old:
    "origin_lookup orngs x = origin_lookup orngs y"
    if asm :"parent_lookup prnts x = Some y" for x y
  proof-
    obtain rest where "follow (parent_lookup prnts) x = x#y#rest"
      using asm follow_cons_3' follow_cons_4 by auto
    moreover have "x \<in> Vs (abstract_forest (Forest rts evs ods prnts orngs))" 
      using invar_basic_F(14) that by auto
    ultimately show ?thesis
      using forest_invar_F(6) by(auto elim!: invar_rootsE)
  qed

  have x_in_p1_org_is_u's_org: "x \<in> set (p1@[u]) \<Longrightarrow> origin_lookup orngs x = origin_lookup orngs u" for x
    using invar_basicD_here(6) UnI1[of v "vset_to_set evs" "vset_to_set ods"]
          invar_rootsD_here(3)[of v x] invar_rootsD_here(3)[of v u] assms(2,3) 
    by auto

  have parent_same_org_new:
    "origin_lookup (origins new_forest) x = origin_lookup (origins new_forest) y"
    if "parent_lookup (parents new_forest) x = Some y" for x y
    using that
    unfolding new_parents_are
  proof(cases "x = new_vert \<and> parent_lookup prnts u \<noteq> None", goal_cases)
    case 1
    note one = this
    hence org_if_cond:"x = new_vert \<and> the (origin_lookup orngs u) \<noteq> u"
      using lookup_u_not_none_roots org_lookup_last by presburger
    note parent_eq = 1(1)[simplified if_P[OF 1(2)]]
    have y_neq_x: "y \<noteq> x" 
      using parents_new.follow_cons_4 that by fastforce
    show ?case 
      unfolding origin_new_def if_P[OF org_if_cond]
    proof(subst if_not_P, goal_cases)
      case 1
      thus ?case
        using Dabstract_forest_def new_vert_loop_not_in_new org_if_cond that
        by fastforce
    next
      case 2
      show ?case
      proof(subst if_not_P, goal_cases)
        case 1
        thus ?case
          using one(1,2) org_lookup_last parents_of_u_props by auto
      next
        case 2
        show ?case
        proof(subst if_P, goal_cases)
          case 1
          show ?case
            using org_if_cond by simp
        next
          case 2
          thus ?case
            using parent_same_org_old[OF parent_eq] one(2) invar_basic_F(13)
                  domIff[of u "origin_lookup orngs"] domI[of "parent_lookup prnts" u]
            by auto
        qed
      qed
    qed
  next
    case 2
    then show ?case
      unfolding if_not_P[OF 2(2)]
    proof(cases "x \<notin> set (p1 @ [u]) \<and>
        the (parent_lookup prnts x) \<in> set (p1 @ [u]) \<inter> vset_to_set evs \<and>
        x \<in> vset_to_set ods - set (p1 @ [u])", goal_cases)
      case 1
      note onee = 1[simplified if_P[OF 1(3)]]
      have y_is_new_vert: "y = new_vert"
        using onee by auto
      have if_Cond:"\<not> (x = new_vert \<and> the (origin_lookup orngs u) \<noteq> u)"
         using lookup_u_not_none_roots onee(2) org_lookup_last by blast
      show ?case
        unfolding origin_new_def  if_not_P[OF if_Cond]
                  if_P[OF y_is_new_vert] eqTrueI[OF y_is_new_vert] simp_thms(22)
      proof(cases "the (origin_lookup orngs u) \<noteq> u", goal_cases)
        case 1
        note one' = this
        have "\<lbrakk>the (origin_lookup orngs u) \<noteq> u; x = u\<rbrakk> \<Longrightarrow> False"
             "\<lbrakk>the (origin_lookup orngs u) \<noteq> u; x \<in> set p1\<rbrakk> \<Longrightarrow> False"
          using onee(3) by auto
        moreover have 
          "\<lbrakk>the (origin_lookup orngs u) \<noteq> u; x \<noteq> u; x \<notin> set p1\<rbrakk>
               \<Longrightarrow> origin_lookup orngs x = Some (the (origin_lookup orngs u))"
        proof(goal_cases)
          case 1
          obtain y where "origin_lookup orngs u = Some y" 
            using one' invar_basic_F(13) domIff[of u "origin_lookup orngs"]
              domIff[of u "parent_lookup prnts"] org_lookup_last parents_of_u_props
            by auto
          moreover obtain px where "parent_lookup prnts x = Some px" " {x, px} \<notin> \<M>"
            using onee(3) forest_invar_F(7)
            by (auto elim!: invar_odd_to_parent_non_matchingE)
          ultimately show ?case
            using  onee(3) parent_same_org_old[of x px]  x_in_p1_org_is_u's_org[of px]
            by auto
        qed
        ultimately show ?case 
          using 1 by auto
      next
        case 2
        note two = this
        hence snd_if_cond_false: 
          "\<not> (y \<in> set (p1 @ [u]) \<and> the (origin_lookup orngs u) \<noteq> u)" by auto
        show ?case
          unfolding if_not_P[OF 2] if_not_P[OF snd_if_cond_false] if_True
        proof(subst if_not_P, goal_cases)
          case 1
          thus ?case
            using assms(6) onee(3) by fastforce
        next
          case 2
          show ?case
          proof(subst if_not_P, goal_cases)
            case 1
            thus ?case
              using assms(6) onee(3) by fastforce
          next
            case 2
            show ?case
            proof(subst (2) if_P, goal_cases)
              case 1
              obtain px where "parent_lookup prnts x = Some px" 
                using invar_basic_F(10,13,6,7) onee(3) domIff[of x "parent_lookup prnts"] 
                      invar_rootsD_here(2)[of x]
                by auto
              thus ?case
                using onee(3) x_in_p1_org_is_u's_org 
                by (fastforce dest: parent_same_org_old)
        qed simp
      qed
    qed
  qed
    next
      case 2
      note 2 = 2[simplified if_not_P[OF 2(3)]]
      hence x_not_in_p1u: "\<not> x \<in> set (p1 @ [u])"
        by force
      hence "parent_lookup prnts x = Some y"
        using 2(1) by auto
      note two = x_not_in_p1u this 2(2,3)
      have x_not_new_vert: "x \<noteq> new_vert"
        using two(3) dom_samer lookup_u_not_none_roots that
        by (auto simp add: effect_of_contract_path(6))
      have cond1_false: "\<not> (x = new_vert \<and> the (origin_lookup orngs u) \<noteq> u)"
        using two(3) org_lookup_last parents_of_u_props by force
      have cond2_false: "\<not> (x \<in> set (p1 @ [u]) \<and> the (origin_lookup orngs u) \<noteq> u)"
        using x_not_in_p1u by blast
      show ?case 
        unfolding origin_new_def if_not_P[OF cond1_false] if_not_P[OF cond2_false]
                  if_not_P[OF x_not_new_vert]
      proof(cases "the (origin_lookup orngs u) \<noteq> u", goal_cases)
        case 1
        obtain ou where ou:"origin_lookup orngs u = Some ou" 
          using assms(4) invar_basic_F(6) invar_rootsD_here(2) by auto
        have helper1: 
         "\<lbrakk>origin_lookup orngs u = Some ou; y = new_vert\<rbrakk> \<Longrightarrow> origin_lookup orngs x = Some ou"
          using new_vert_not_Dabstract assms(6) invar_basic_F(10,13,14)
            dVs_Vs_Dabstract_abstract_forest[of "Forest rts evs ods prnts orngs"]
             domIff[of x "origin_lookup orngs"] domIff[of x "parent_lookup prnts"] two(2)
            x_in_p1_org_is_u's_org[of new_vert] parent_same_org_old[of x new_vert]
          by auto
        have helper2:
         "\<lbrakk>u \<noteq> new_vert; y = u\<rbrakk> \<Longrightarrow> origin_lookup orngs x = None"
          using assms(4) parents_ev_od(2) two(2,4) x_not_in_p1u by auto
        have helper3: 
         "\<lbrakk>origin_lookup orngs u = Some ou; y \<noteq> new_vert; y \<in> set p1\<rbrakk>
           \<Longrightarrow> origin_lookup orngs x = None"
          using assms(4) parents_ev_od(2)[OF two(2)] two(2,4) x_not_in_p1u parent_same_org_old[OF two(2)] 
                parent_adj_pu_helper split_list_last
          by force+
        have helper4: 
         "\<lbrakk>origin_lookup orngs u = Some ou; y \<noteq> new_vert; y \<noteq> u; y \<notin> set p1\<rbrakk>
           \<Longrightarrow> origin_lookup orngs x = origin_lookup orngs y"
          using parent_same_org_old two(2) by blast
        from ou show ?case
          using 1 by (auto intro: helper2 helper3 helper4 helper1)
      next
        case 2
        note u_no_root = this
        hence if_snd_cond_false:"\<not> (y = new_vert \<and> the (origin_lookup orngs u) \<noteq> u)" by auto
        have if_snd_cond_false2:"\<not> (y \<in> set (p1 @ [u]) \<and> the (origin_lookup orngs u) \<noteq> u)"
          using 2 by auto
        show ?case
          unfolding if_not_P[OF 2] if_not_P[OF x_not_in_p1u]
            if_not_P[OF if_snd_cond_false] if_not_P[OF if_snd_cond_false2]
        proof(cases "y = new_vert", goal_cases)
          case 1
          show ?case 
            using invar_basic_F(14,6) two(2) x_not_in_p1u assms(6) 1
                  x_in_p1_org_is_u's_org[of new_vert] parents_ev_od(1,2)[of x new_vert]
                  parent_same_org_old[of x new_vert]
            by auto
        next
          case 2
          note y_neq_new_vert = this
          show ?case 
            unfolding if_not_P[OF 2]
          proof(cases "(x \<in> vset_to_set ods \<union> vset_to_set evs \<and> x \<notin> set (p1 @ [u])) \<and>
                      the (origin_lookup orngs x) = the (origin_lookup orngs u)", goal_cases)
            case 1
            note one = this
            show ?case
              unfolding if_P[OF 1]
            proof(subst (2) if_P, goal_cases)
              case 1
              thus ?case
                using one assms(4) invar_basic_F(7) parents_ev_od(1,2)[OF two(2)]
                  parent_same_org_old[OF two(2)] two(2,4)
                  parent_adj_pu_helper split_list_first by auto fastforce+
            qed simp
          next
            case 2
            note Two = this
            show ?case 
              unfolding if_not_P[OF 2]
            proof(subst (2) if_not_P, goal_cases)
              case 1
              thus ?case
                using "2" parent_same_org_old parents_ev_od(1,2) two(2) x_not_in_p1u by auto
            next
              case 2
              thus ?case
                using x_not_in_p1u Two invar_basic_F(14,6) two(2) parent_same_org_old[of x y]
                      x_in_p1_org_is_u's_org[of y] 
                by auto
          qed
        qed
      qed
    qed
  qed
qed

  have big_origin_conjunction_after:
    "origin_lookup (origins new_forest) v =
         Some (last (follow (parent_lookup (parents new_forest)) v)) \<and>
        (\<forall> u \<in> set (follow (parent_lookup (parents new_forest)) v).
           origin_lookup (origins new_forest) v = origin_lookup (origins new_forest) u) \<and>
       set (edges_of_path (follow (parent_lookup (parents new_forest)) v))
         \<subseteq> abstract_forest new_forest"
    if "v \<in> vset_to_set (roots new_forest) \<union> Vs (abstract_forest new_forest)" for v
    using that
  proof(induction v rule: follow_new_induct)
    case (1 vv)
    have tirple_conjD: "A \<and> B \<and> C \<Longrightarrow> A" "A \<and> B \<and> C \<Longrightarrow> B" "A \<and> B \<and> C \<Longrightarrow> C"
      for A B C 
      by auto
    note IH = tirple_conjD[OF 1(1)]
    note Iprem= 1(2)
    show ?case
    proof(cases "parent_lookup (parents new_forest) vv")
      case None
      hence vv_root: "vv \<in> vset_to_set (roots new_forest)" 
        using "1.prems" dom_samer
              domIff[of vv "origin_lookup (origins new_forest)"] org_lookup_helper
        by auto
      show ?thesis
        using None by (auto simp add: lookup_self_implies_root vv_root follow_new_simps[of vv])
    next
      case (Some pvv)
      have triple_conjI: "\<lbrakk>A;B;C\<rbrakk> \<Longrightarrow> A \<and> B \<and> C" for A B C
        by auto
      have vv_pvv_in_new_F: "{vv, pvv} \<in> abstract_forest new_forest"
        using Some
        by(auto simp add:abstract_forest_def)
      hence pvv_is_new_F_vert:
        "pvv \<in> vset_to_set (roots new_forest) \<union> Vs (abstract_forest new_forest)"
        by auto
      note IH = IH[OF Some pvv_is_new_F_vert]
      show ?thesis
      proof(rule triple_conjI, goal_cases)
        case 1
        then show ?case 
          using follow_new_last_Cons parent_same_org_new IH Some
          by auto
      next
        case 2
        then show ?case
          by (simp add: IH(2) Some follow_def parent_same_org_new parents_new.follow_cons_4)
      next
        case 3
        then show ?case 
          unfolding follow_new_simps[of vv, simplified Some option.case(2)] 
        proof(cases "parent_lookup (parents new_forest) pvv", goal_cases)
          case 1
          then show ?case
            by (simp add: vv_pvv_in_new_F follow_new_simps[of pvv])
        next
          case (2 ppvv)
          then show ?case 
            using IH(3)
            by(simp add:  vv_pvv_in_new_F follow_new_simps[of pvv])
        qed
      qed
    qed
  qed

  have invar_roots_after: "invar_roots new_forest"
    using big_origin_conjunction_after lookup_self_implies_root
    by(auto intro!: invar_rootsI)

  show ?th1
    by(auto intro!: forest_invarI invar_basic_after invar_matching_both_or_none_after
        invar_forest_even_and_odd_after invar_parent_wf_after 
        invar_even_to_parent_matching_after invar_roots_after
        invar_odd_to_parent_non_matching_after invar_odd_is_parent_after)

  show ?th2
    by (simp add: quot_is_AF)

  show ?th3 
    by (simp add: effect_of_contract_path(6))

  show ?th4
    unfolding M_quot
  proof(rule matchingI, goal_cases)
    case (1 e1 e2)
    then show ?case 
    proof(cases "u \<in> vset_to_set rts", goal_cases)
      case 1
      note 1 = 1[simplified if_P[OF 1(4)] Un_empty_right Un_empty_left]
      then show ?case 
        using assms(5) by(auto elim!: matchingE)
    next
      case 2
      note 2 = 2[simplified if_not_P[OF 2(4)]]
      have u_pu_in_M: "{u, the (parent_lookup prnts u)} \<in> \<M>"
        using "2"(4) assms(4) forest_invar_F(5) invar_even_to_parent_matchingD parents_of_u_props
        by fastforce
      have case1: "e1 \<inter> e2 = {}"
        if asm :"e1 \<in> \<M> - ({{u, the (parent_lookup prnts u)}} \<union> set (edges_of_path (p1 @ [u])))"
           "e2 = {new_vert, the (parent_lookup prnts u)}" for e1 e2
      proof-
        have e1_props: "e1 \<in> \<M>" "e1 \<noteq> {u, the (parent_lookup prnts u)}" 
                    "e1 \<notin> set (edges_of_path (p1 @ [u]))"
          using asm(1) by auto
        show ?thesis
        proof(rule matching_edge_rev_alt_path_cases[OF 
              rev_alt_path_M e1_props(1) assms(7) assms(5)], goal_cases)
          case (1 u'' v'' i)
          then show ?case
            using e1_props(3) edges_of_path_length[of "p1 @ [u]"]
              nth_mem[of i "edges_of_path (p1 @ [u])"]
            by auto
        next
          case (2 u v)
          hence "v = the (parent_lookup prnts u)"
            using assms(5) e1_props(1) last_snoc[of p1 u] u_pu_in_M
              doubleton_in_matching(1)[of \<M> u "the (parent_lookup prnts u)" v] by simp
          then show ?case
            using "2"(2,5) e1_props(2) by auto
        next
          case 3
          hence if_u_or_new_in_e1:
             "new_vert \<in> e1 \<Longrightarrow> e1 = {u, the (parent_lookup prnts u)}"
             "u \<in> e1 \<Longrightarrow> e1 = {u, the (parent_lookup prnts u)}"
            using assms(6)  e1_props(1) by auto
          have if_pu_in_e1: "the (parent_lookup prnts u) \<in> e1 
                 \<Longrightarrow> e1 = {u, the (parent_lookup prnts u)}" 
            using assms(5) e1_props(1) u_pu_in_M
              matching_unique_match[of \<M> "the (parent_lookup prnts u)" e1
                "{u, the (parent_lookup prnts u)}"] 
            by simp
          from 3 show ?case 
            by(auto simp add: asm(2) dest!: if_u_or_new_in_e1 if_pu_in_e1)
        qed
      qed
       have case2: False
          if "e1 = {new_vert, the (parent_lookup prnts u)}"
             "e2 = {new_vert, the (parent_lookup prnts u)}"
        using 2(3) that by simp
      have case3:"e1 \<inter> e2 = {}"
        if "e1 \<in> \<M> - ({{u, the (parent_lookup prnts u)}} \<union> set (edges_of_path (p1 @ [u])))"
           "e2 \<in> \<M> - ({{u, the (parent_lookup prnts u)}} \<union> set (edges_of_path (p1 @ [u])))"
        using that 1(3) by(intro matchingD[OF assms(5)]) auto
      show ?case
        apply(rule UnE[OF 2(1)], all \<open>rule UnE[OF 2(2)]\<close>)
        using  case1[of e1 e2] case1[of e2 e1] case2 case3
        by auto
    qed
  qed

  have new_parent_new_vert_None_pu_None:
      "parent_lookup (parents new_forest) new_vert = None \<Longrightarrow>
        parent_lookup prnts u = None"
    by(cases "parent_lookup prnts u")(auto simp add: new_parents_are)

  have parent_new_vert_is_pu:"parent_lookup (parents new_forest) new_vert = Some pu \<Longrightarrow>
       parent_lookup prnts u = Some pu" for pu
   using assms(6)  invar_basic_F(14,6) lookup_u_not_none_roots
   by(auto simp add: new_parents_are if_split[of "\<lambda> x. x = Some pu"])

  have assms6': "new_vert \<notin> vset_to_set evs \<union> vset_to_set ods - set (p1 @ [u])"
    using assms(6) by auto

  have edges_p_in_F:
    "set (edges_of_path (p1@[u]@p2)) \<subseteq> abstract_forest (Forest rts evs ods prnts orngs)"
    using assms(2,3)  invar_basic_F(6)
      forest_invar_F(6) UnI1[of v "vset_to_set evs" "vset_to_set ods"]
      invar_rootsD(4)[of "Forest rts evs ods prnts orngs" v]
    by auto
  hence p_inVs_of_F:"set (p1@[u]@p2) \<subseteq> vset_to_set evs \<union> vset_to_set ods"
    using assms(2,3) forest_invar_F(1,4,6)
      path_follow_verts_in_verts_F[of \<M> "Forest rts evs ods prnts orngs" v]
      invar_basicE[of \<M> "Forest rts evs ods prnts orngs"] invar_basic_F(6) 
    by auto

  have coincide_parents_in_p2:
    "v' \<in> set p2 \<Longrightarrow> 
     parent_lookup prnts v' = parent_lookup (parents new_forest) v'" for v'
    unfolding new_parents_are
  proof(subst if_not_P, goal_cases)
    case 1
    note one = this
    have "v' \<noteq> new_vert"
    proof(rule ccontr, goal_cases)
      case 1
      then obtain p1a p1b where "p1@[u] = p1a@[v']@p1b"
        using assms6' distinct_path one p_inVs_of_F by auto
      moreover obtain p2a p2b where "p2 = p2a@[v']@p2b" 
        using one single_in_append[of v'] split_list_first[of v' p2]
        by auto
      ultimately show ?case 
      using distinct_path by(cases p1b rule: rev_cases) auto
    qed
    then show ?case by simp
  next
    case 2
    then obtain p2a p2b where p2_split_middle:"p2 = p2a@[v']@p2b"
      by(auto simp add: in_set_conv_decomp)
    then show ?case
    proof(subst if_not_P, goal_cases)
      case 1
      note one = this
      have "\<lbrakk>v' \<in> vset_to_set ods; the (parent_lookup prnts v') \<in> set (p1@[u])\<rbrakk> \<Longrightarrow> False"
      proof(goal_cases)
        case 1
        then obtain pv' where pv': "parent_lookup prnts v' = Some pv'"
          using forest_invar_F(7) by(auto elim!: invar_odd_to_parent_non_matchingE) 
        then obtain p2b' where p2b': "p2b = pv'#p2b'" 
          using p2_split_middle assms(2) 
                follow_subsequent_parent_there[of v "(p1 @ [u]) @ p2a" v' p2b pv']
          by auto
        moreover have "pv' \<noteq> v'"
          using prnts_no_loop pv' by blast
        ultimately obtain p2bi p2bii where p2b'_split: "p2b' = p2bi@[pv']@p2bii"
          using "1"(2) distinct_path p2_split_middle pv' by force
        then show False
          using distinct_path p2_split_middle p2b' by auto
      qed
      then show ?case 
        by auto
    next
      case 2
      then show ?case 
        using distinct_path by auto
    qed
  qed
   
  have follow_new_vert:
   "follow (parent_lookup (parents new_forest)) new_vert = new_vert#p2"
  unfolding follow_new_simps[of new_vert]
  proof(cases "parent_lookup (parents new_forest) new_vert", goal_cases)
    case 1
    then show ?case 
      using lookup_u_not_none_roots u_roots_p2_Nil
      by (auto dest!: new_parent_new_vert_None_pu_None)
  next
    case (2 pu)
    hence "parent_lookup prnts u = Some pu"
      using parent_new_vert_is_pu by auto
    hence p2_is_follow:"p2 = follow (parent_lookup prnts) pu" 
      using assms(2) 
        follow_def[of "parent_lookup prnts"] parents_here.follow_append[of v "p1 @ [u]" pu]
        parents_here.follow_subsequent_parent_there[of v p1 u p2 pu] 
      by auto
    show ?case
      unfolding 2 option.case(2) p2_is_follow
    proof(rule arg_cong2[OF refl, of _ _ Cons],
          rule follow_cong[folded follow_def,
            OF parents_here.parent_axioms parents_here.follow_dom, symmetric], goal_cases)
      case 1
      then show ?case 
        by (simp add: coincide_parents_in_p2 p2_is_follow)
    next
      case 2
      then show ?case 
        by (simp add: parents_new.parent_axioms)
    qed
  qed

  have parent_in_p1u_new_parent_new_vert:
    "\<lbrakk>parent_lookup prnts v' = Some pv'; pv' \<in> set (p1@[u]); v' \<notin> set (p1@[u])\<rbrakk> \<Longrightarrow>
    parent_lookup (parents new_forest) v' = Some new_vert" for v' pv'
    unfolding new_parents_are
  proof(subst if_not_P, goal_cases)
    case 1
    hence "v' \<in> vset_to_set evs \<union> vset_to_set ods"
      using p_inVs_of_F parents_ev_od(1,2) by auto
    hence "v' \<noteq> new_vert"
      using "1"(3) assms6' by blast
    then show ?case
      by simp
  next
    case 2
    then show ?case 
    proof(subst if_P, goal_cases)
      case 1
      then show ?case 
        using parents_ev_od(2) assms(4) parent_adj_pu_helper split_list_last 
        by fastforce
    next
      case 2
      then show ?case 
        by simp
    qed
  qed

  have follow_u: "follow (parent_lookup prnts) u = u # p2"
    using assms(2) follow_append[of v p1 u p2] by auto

  have parent_not_in_p1u_new_parent_is_old:
    "\<lbrakk>parent_lookup prnts v' = Some pv'; pv' \<notin> set (p1@[u]); v' \<notin> set (p1@[u])\<rbrakk> \<Longrightarrow>
    parent_lookup (parents new_forest) v' = parent_lookup prnts v'" for v' pv'
    unfolding new_parents_are
  proof(subst if_not_P, goal_cases)
    case 1
    hence "v' \<in> vset_to_set evs \<union> vset_to_set ods" 
      using invar_basic_F(14,6) by auto
    hence "v' \<noteq> new_vert"
      using "1"(3) assms6' by blast
    then show ?case
      by simp
  next
    case 2
    then show ?case 
      by auto
  qed

  show "\<lbrakk>?asm1;?asm2\<rbrakk>\<Longrightarrow> ?th5"
  proof(induction p1' arbitrary: v')
    case Nil
    then show ?case 
     by(simp add: follow_new_vert)
  next
    case (Cons a p1')
    hence a_is_v': "a = v'"
      using follow_hd[of v'] 
      by auto
    moreover hence distinct_path:"distinct ((v' # p1') @ [u] @ p2)"
      using follow_distinct[of a] Cons.prems(1) by auto
    hence v'_not_in_p1u: "v' \<notin> set (p1 @ [u])" 
      using Cons.prems(2) calculation by auto
    note Cons = Cons
    then show ?case 
      unfolding a_is_v'
    proof(cases p1', goal_cases)
      case 1
      note IH = Cons(1)[of u, simplified if_P[OF 1(4)], simplified 1(4), simplified]
      from 1 have pv'_is: "parent_lookup prnts v' = Some u"
        using follow_cons_2(2) by simp
      then show ?case
        by(auto intro!: IH 
              simp add: follow_new_simps[of v'] follow_u
                        parent_in_p1u_new_parent_new_vert[OF pv'_is _ v'_not_in_p1u] 1(4)
                 split: option.split)     
    next
      case (2 pv' list)
      hence p1'_not_Nil:"p1' \<noteq> []" and p1_not_Nil: "v' # p1' \<noteq> []"
        by auto
      note Cons = 2(1-3)[simplified if_not_P[OF p1'_not_Nil] 2(4)] 2(4)
      have pv':"parent_lookup prnts v' = Some pv'"
           "follow (parent_lookup prnts) pv' = pv' # list @ u # p2"
        using calculation Cons
              parents_here.follow_cons_2[folded follow_def, of a pv' "list @ u # p2"]
        by auto
      have to_old_precond: "pv' \<notin> set (p1 @ [u])" "v' \<notin> set (p1 @ [u])"
        using distinct_path local.Cons(3,4) by auto
      note same_par = parent_not_in_p1u_new_parent_is_old[OF pv'(1) to_old_precond]
      show ?case
        using to_old_precond Cons(3)
        unfolding if_not_P[OF p1_not_Nil] 
        by(auto intro!: Cons(1)[simplified, of pv']
              simp add: Cons(4) follow_new_simps[of v'] same_par pv')
    qed
  qed
qed

theorem contract_fork_correct:
  assumes "forest_invar \<M> (Forest rts evs ods prnts orngs)" 
    "follow (parent_lookup prnts) v = p1@[u]@p2"
    "follow (parent_lookup prnts) v' = p1'@[u]@p2"
    "v \<in> vset_to_set evs"
    "v' \<in> vset_to_set evs"
    "set p1 \<inter> set p1' = {}"
    "matching \<M>"
    "new_vert \<notin> Vs \<M> \<union> vset_to_set evs \<union> vset_to_set ods - (set p1 \<union> set p1' \<union> {u})"
    "dblton_graph \<M>"
    and contr_def: "contr = (\<lambda> v. if v \<in> {u} \<union> set p1 \<union> set p1' then new_vert else v)"
    and new_forest_def:
    "new_forest = contract_fork (Forest rts evs ods prnts orngs) (p1@[u]) (p1'@[u]) new_vert"
  shows "forest_invar (quot_graph contr \<M> - {{new_vert}}) new_forest" (is ?th1)
    and  "abstract_forest new_forest 
         = quot_graph contr (abstract_forest (Forest rts evs ods prnts orngs))
             - {{new_vert}}" (is ?th2)
and "vset_to_set (odds new_forest) = vset_to_set ods - ({u} \<union> set p1 \<union> set p1')" (is ?th3)
and "vset_to_set (evens new_forest) = (vset_to_set evs - ({u} \<union> set p1 \<union> set p1')) \<union> {new_vert}" (is?th4)
and "vset_to_set (roots new_forest) =
    (if u \<in> vset_to_set rts
     then vset_to_set rts - {u} \<union> {new_vert} else vset_to_set rts)" (is ?th5)
and "matching (quot_graph contr \<M> - {{new_vert}})" (is ?th6)
proof-

  note forest_invarD = forest_invarD[OF assms(1)] 
  note invar_basicD = invar_basicD[OF forest_invarD(1)]

  interpret parents_here: parent "(parent_lookup prnts)"
    using follow_dom_invar_parent_wf(1) forest_invarD(4) by fastforce
  note follow_not_again_parent = parents_here.follow_not_again_parent[folded follow_def]
  note follow_subsequent_parent = parents_here.follow_subsequent_parent[folded follow_def]
  note follow_subsequent_parent_there = parents_here.follow_subsequent_parent_there[folded follow_def]
  note follow_valk_bet = parents_here.follow_valk_bet[folded follow_def, 
      simplified parents_here.parent_eq_follow_rel]
  note follow_simps = parents_here.follow_psimps[folded follow_def]
  note follow_hd = parents_here.follow_hd[folded follow_def]
  note follow_cons_2 =  parents_here.follow_cons_2[folded follow_def]
  note follow_append = parent.follow_append[folded follow_def, OF parents_here.parent_axioms]
  note follow_subsequent_parent=parents_here.follow_subsequent_parent[folded follow_def]
  have hd_p_is_v: "hd (p1 @ [u] @ p2) = v"
    using assms(2) follow_hd[of v] by simp
  have hd_p'_is_v': "hd (p1' @ [u] @ p2) = v'"
    using assms(3) follow_hd[of v'] by simp

  have u_even:"u \<in> vset_to_set evs"
  proof(rule ccontr, goal_cases)
    case 1
    hence u_odd: "u \<in> vset_to_set ods" 
      using assms(1,2,4) forest_invarD(1,4,6) invar_basicD(6)
           path_follow_verts_in_verts_F[OF forest_invarD(1,6,4), of v]
      by auto
    then obtain cu p1a where p1_split: "p1 = p1a@[cu]" 
      using 1 assms(4) hd_p_is_v by(cases "p1" rule: rev_cases) auto
    hence cu_u_in_F:"{cu, u} \<in> abstract_forest (Forest rts evs ods prnts orngs)" 
      using assms(2) follow_append follow_cons_2(2)[of cu u p2]
      by (fastforce simp add: abstract_forest_def)
    have pcu: "parent_lookup prnts cu = Some u"
      using p1_split assms(2) follow_subsequent_parent[of v p1a cu u p2]
      by auto
    hence cuu_M: "{cu, u} \<in> \<M>"
      using  cu_u_in_F  assms(1) forest_invarD(5) complex_invariant_consequences(2)
          invar_even_to_parent_matchingD  u_odd 
      by force
    obtain c'u p1'a where p1'_split: "p1' = p1'a@[c'u]" 
      using 1 assms(5) hd_p'_is_v' by(cases "p1'" rule: rev_cases) auto
    hence c'u_u_in_F:"{c'u, u} \<in> abstract_forest (Forest rts evs ods prnts orngs)" 
      using assms(3) follow_append follow_cons_2(2)[of c'u u p2]
      by (fastforce simp add: abstract_forest_def)
    have pc'u: "parent_lookup prnts c'u = Some u"
      using p1'_split assms(3) follow_subsequent_parent[of v' p1'a c'u u p2]
      by auto
    hence c'uu_M: "{c'u, u} \<in> \<M>"
      using  c'u_u_in_F  assms(1) forest_invarD(5) complex_invariant_consequences(2)
          invar_even_to_parent_matchingD u_odd 
      by force
    hence "c'u = cu" 
      using assms(7) cuu_M by(auto intro!: matching_partner_eqI)
    hence "c'u \<in> set p1 \<inter> set p1'"
      using p1'_split p1_split by simp
    then show ?case 
      using assms(6) by simp
  qed
  define contr1 where "contr1 = (\<lambda>v. if v \<in> set (p1 @ [u]) then u else v)"
  define intermedF where 
    "intermedF = contract_path (Forest rts evs ods prnts orngs) (p1 @ [u]) u"
  have u_not_there: "u \<notin> Vs \<M> \<union> vset_to_set evs \<union> vset_to_set ods - set (p1 @ [u])"
    by auto
  note after_first =
     contract_path_correct[OF assms(1,2,4) u_even assms(7) u_not_there assms(9) contr1_def intermedF_def]
  note p'_after = after_first(7)[OF assms(3,6)]
  have intermedF_split: "intermedF = Forest (roots intermedF) (evens intermedF)
          (odds intermedF) (parents intermedF) (origins intermedF)"
    by(cases intermedF) auto
  have invar_after_first: "forest_invar (quot_graph contr1 \<M> - {{u}}) 
           (Forest (roots intermedF) (evens intermedF)
          (odds intermedF) (parents intermedF) (origins intermedF))"
    using after_first(1)  intermedF_split by simp
  have final_precond1: "(if p1' = [] then u else v') \<in> vset_to_set (evens intermedF)"
    using after_first(4) hd_p'_is_v' hd_p_is_v assms(3,5,6) follow_append[of u _ u p2] 
    by(cases p1') auto
  have final_precond2: "u \<in> vset_to_set (evens intermedF)"
    by (simp add: after_first(4))
  have final_precond3: "new_vert \<notin> Vs (quot_graph contr1 \<M> - {{u}}) \<union> vset_to_set (evens intermedF) \<union>
       vset_to_set (odds intermedF) -
       set (p1' @ [u])"
    using assms(8)
    by (auto dest!: set_mp[OF Vs_subset[of 
                          "quot_graph contr1 \<M> - {{u}}" "quot_graph contr1 \<M>"],
                          simplified contr1_def, simplified]
          simp add: Vs_quot_graph_is_img contr1_def after_first(4,3))
  have final_precond4: "dblton_graph (quot_graph contr1 \<M> - {{u}})"
   using assms(8) 
   by(auto intro!: dblton_graph_contract_into_one_vert[OF assms(9) contr1_def])
  define contr2 where "contr2 = (\<lambda>v. if v \<in> set (p1' @ [u]) then new_vert else v)"
  have final_precond5: "new_forest = contract_path intermedF (p1' @ [u]) new_vert"
    by(simp add: new_forest_def contract_fork_def intermedF_def)
  have quot_graphId: 
    "quot_graph contr2 (quot_graph contr1 G - {{u}}) - {{new_vert}}
      = quot_graph contr G - {{new_vert}}" for G
    using assms(8)
    by(intro quot_graph_comp[OF contr1_def, of _ "set p1'"])
      (auto simp add: contr2_def contr_def)

  note final_props =  contract_path_correct(1-6)[OF invar_after_first p'_after
   final_precond1
            final_precond2 after_first(6)  final_precond3 final_precond4 contr2_def,
            simplified intermedF_split[symmetric], OF final_precond5, 
            simplified after_first(2,3,4,5)
             quot_graphId]
  show ?th1 ?th6 ?th2 ?th3 ?th4 ?th5
    using final_props assms(8) by auto
qed

interpretation fork_contraction_spec_satisfied:
 alternating_forest_fork_contraction_spec
 where vset_invar = vset_invar
 and vset_to_set = vset_to_set
 and evens = evens
 and odds = odds
 and get_path = get_path
 and abstract_forest = abstract_forest
 and forest_invar = forest_invar
 and roots = roots
 and contract_fork = contract_fork
proof(goal_cases)
  case 1
  interpret af_spec_here: 
    alternating_forest_spec evens odds get_path abstract_forest forest_invar roots
     vset_invar vset_to_set
    using satisfied
    by(auto simp add: alternating_forest_ordinary_extension_spec_def)
  note  contract_fork_precondE = af_spec_here.contract_fork_precondE
                                          
  show ?case
proof(rule alternating_forest_fork_contraction_spec.intro, goal_cases)
  case 1
  then show ?case 
    by (simp add: af_spec_here.alternating_forest_spec_axioms)
next
  case 2
  then show ?case
  proof(rule  alternating_forest_fork_contraction_spec_axioms.intro, goal_cases)
    case (1 \<M> F v v' B1 B2 u new_vert P contr)
    then show ?case
    proof(cases F, goal_cases)
      case (1 rts evs ods prnts orgns)
      hence Finvar: "forest_invar \<M> (Forest rts evs ods prnts orgns)"
        using 1 by(auto elim!: contract_fork_precondE)
      interpret parent_here: parent "parent_lookup prnts"
        using Finvar by(auto elim!: forest_invarE invar_parent_wfE intro!: parent.intro)
      note follow_same = parent_spec_i.follow_dom_impl_same[OF parent_here.follow_dom]
      show ?thesis 
        using 1(1) 
        by(auto elim!: contract_fork_precondE 
               intro!: contract_fork_correct[OF Finvar, of v B1 u P v'] 
             simp add: get_path_def follow_same 1(2))
    qed
  next
    case (2 \<M> F v v' B1 B2 u new_vert P contr)
    then show ?case
    proof(cases F, goal_cases)
      case (1 rts evs ods prnts orgns)
      hence Finvar: "forest_invar \<M> (Forest rts evs ods prnts orgns)"
        using 1 by(auto elim!: contract_fork_precondE)
      interpret parent_here: parent "parent_lookup prnts"
        using Finvar by(auto elim!: forest_invarE invar_parent_wfE intro!: parent.intro)
      note follow_same = parent_spec_i.follow_dom_impl_same[OF parent_here.follow_dom]
      show ?thesis 
        using 1(1) unfolding 1(2)
        by(elim contract_fork_precondE,
           intro contract_fork_correct[OF Finvar, of v B1 u P v'])
          (auto simp add: get_path_def follow_same 1(2))
    qed
  next
    case (3 \<M> F v v' B1 B2 u new_vert P contr)
    then show ?case
    proof(cases F, goal_cases)
      case (1 rts evs ods prnts orgns)
      hence Finvar: "forest_invar \<M> (Forest rts evs ods prnts orgns)"
        using 1 by(auto elim!: contract_fork_precondE)
      interpret parent_here: parent "parent_lookup prnts"
        using Finvar by(auto elim!: forest_invarE invar_parent_wfE intro!: parent.intro)
      note follow_same = parent_spec_i.follow_dom_impl_same[OF parent_here.follow_dom]
      show ?thesis 
        using 1(1) unfolding 1(2)
        by(elim contract_fork_precondE,
           subst contract_fork_correct[OF Finvar, of v B1 u P v'])
          (auto simp add: get_path_def follow_same 1(2))
    qed
  next
    case (4 \<M> F v v' B1 B2 u new_vert P contr)
    then show ?case 
    proof(cases F, goal_cases)
      case (1 rts evs ods prnts orgns)
      hence Finvar: "forest_invar \<M> (Forest rts evs ods prnts orgns)"
        using 1 by(auto elim!: contract_fork_precondE)
      interpret parent_here: parent "parent_lookup prnts"
        using Finvar by(auto elim!: forest_invarE invar_parent_wfE intro!: parent.intro)
      note follow_same = parent_spec_i.follow_dom_impl_same[OF parent_here.follow_dom]
      show ?thesis 
        using 1(1) unfolding 1(2)
        by(elim contract_fork_precondE,
           subst contract_fork_correct[OF Finvar, of v B1 u P v'])
          (auto simp add: get_path_def follow_same 1(2))
    qed
  next
    case (5 \<M> F v v' B1 B2 u new_vert P contr)
    then show ?case 
    proof(cases F, goal_cases)
      case (1 rts evs ods prnts orgns)
      hence Finvar: "forest_invar \<M> (Forest rts evs ods prnts orgns)"
        using 1 by(auto elim!: contract_fork_precondE)
      interpret parent_here: parent "parent_lookup prnts"
        using Finvar by(auto elim!: forest_invarE invar_parent_wfE intro!: parent.intro)
      note follow_same = parent_spec_i.follow_dom_impl_same[OF parent_here.follow_dom]
      show ?thesis 
        using 1(1) unfolding 1(2)
        by(elim contract_fork_precondE,
           subst contract_fork_correct[OF Finvar, of v B1 u P v'])
          (auto simp add: get_path_def follow_same 1(2))
    qed
  next
    case (6 \<M> F v v' B1 B2 u new_vert P contr)
    then show ?case
    proof(cases F, goal_cases)
      case (1 rts evs ods prnts orgns)
      hence Finvar: "forest_invar \<M> (Forest rts evs ods prnts orgns)"
        using 1 by(auto elim!: contract_fork_precondE)
      interpret parent_here: parent "parent_lookup prnts"
        using Finvar by(auto elim!: forest_invarE invar_parent_wfE intro!: parent.intro)
      note follow_same = parent_spec_i.follow_dom_impl_same[OF parent_here.follow_dom]
      show ?thesis 
        using 1(1) unfolding 1(2)
        by(elim contract_fork_precondE,
           intro contract_fork_correct[OF Finvar, of v B1 u P v'])
          (auto simp add: get_path_def follow_same 1(2))
    qed
  qed
 qed
qed

lemmas spec_satisfied =
  fork_contraction_spec_satisfied.alternating_forest_fork_contraction_spec_axioms

end
thm forest_contract_manipulation.spec_satisfied
end