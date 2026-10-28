theory Alternating_Forest_Contraction
  imports Basic_Matching.Alternating_Forest_Executable
    Graph_Quotient
begin
(*Note: not necessary for the current executable blossom, 
   but it will be useful for a cubic version
   where path search and contraction are interwoven.*)
provenance human

context alternating_forest_spec
begin

definition 
   "contract_fork_precond ℳ F v v' B1 B2 u new_vert P contr = 
    (forest_invar ℳ F ∧  matching ℳ ∧ dblton_graph ℳ ∧ 
     get_path F v = B1@[u]@P ∧ get_path F v' = B2@[u]@P ∧ set B1 ∩ set B2 ={} ∧
     v ∈ vset_to_set (evens F) ∧ v' ∈ vset_to_set (evens F) ∧ 
     new_vert ∉ Vs ℳ ∪ vset_to_set (evens F) ∪ vset_to_set (odds F) - (set B1 ∪ set B2 ∪ {u}) ∧
     contr = (λ v. if v ∈ {u} ∪ set B1 ∪ set B2 then new_vert else v))"

lemma contract_fork_precondI:
 "⟦forest_invar ℳ F; matching ℳ; dblton_graph ℳ; get_path F v = B1@[u]@P;
   get_path F v' = B2@[u]@P; set B1 ∩ set B2 = {}; v ∈ vset_to_set (evens F);
   v' ∈ vset_to_set (evens F); 
   new_vert ∉ Vs ℳ ∪ vset_to_set (evens F) ∪ vset_to_set (odds F) - (set B1 ∪ set B2 ∪ {u});
   contr = (λ v. if v ∈ {u} ∪ set B1 ∪ set B2 then new_vert else v)⟧
   ⟹ contract_fork_precond ℳ F v v' B1 B2 u new_vert P contr"
and contract_fork_precondE:
 "contract_fork_precond ℳ F v v' B1 B2 u new_vert P contr ⟹
 (⟦forest_invar ℳ F; matching ℳ; dblton_graph ℳ; get_path F v = B1@[u]@P;
   get_path F v' = B2@[u]@P; set B1 ∩ set B2 = {}; v ∈ vset_to_set (evens F);
   v' ∈ vset_to_set (evens F); 
   new_vert ∉ Vs ℳ ∪ vset_to_set (evens F) ∪ vset_to_set (odds F) - (set B1 ∪ set B2 ∪ {u});
   contr = (λ v. if v ∈ {u} ∪ set B1 ∪ set B2 then new_vert else v)⟧
   ⟹ Q)
  ⟹ Q"
  by(auto simp add: contract_fork_precond_def)

definition 
 "odd_expansion_precond ℳ F u mu p = 
  (forest_invar ℳ F ∧ matching ℳ ∧ u ∈ vset_to_set (odds F) ∧ {u, mu} ∈ ℳ ∧
  odd (length p) ∧ set p ∩ (Vs (abstract_forest F) ∪ vset_to_set (roots F) ∪ Vs ℳ) ⊆ {u} ∧ 
  distinct p)"

lemma odd_expansion_precondE:
  "⟦odd_expansion_precond ℳ F u mu p; 
    ⟦forest_invar ℳ F; matching ℳ; u ∈ vset_to_set (odds F); {u, mu} ∈ ℳ; odd (length p);
     set p ∩ (Vs (abstract_forest F) ∪ vset_to_set (roots F) ∪ Vs ℳ) ⊆ {u};  distinct p⟧ ⟹ P ⟧
   ⟹ P"
and odd_expansion_precondI:
  "⟦forest_invar ℳ F; matching ℳ; u ∈ vset_to_set (odds F); {u, mu} ∈ ℳ; odd (length p);
     set p ∩ (Vs (abstract_forest F) ∪ vset_to_set (roots F) ∪ Vs ℳ) ⊆ {u};  distinct p⟧ 
   ⟹ odd_expansion_precond ℳ F u mu p"
  by(auto simp add: odd_expansion_precond_def)


end

context forest_manipulation_spec
begin

abbreviation "parent_put k v P ≡ parent_upd P k v"
abbreviation "origin_put k v Q ≡ origin_upd Q k v"
abbreviation "parent_delete k P ≡ parent_upd P k nil"
abbreviation "origin_delete k Q ≡ origin_upd Q k nil"

end

context forest_manipulation
begin

lemma parent_put_lookup:
  "⟦parent_invar P; k ∈ K; v ≠ nil⟧ ⟹
    parent_lookup (parent_put k v P) = (parent_lookup P)(k ↦ v)"
  by (rule parent_lookup_upd)

lemma origin_put_lookup:
  "⟦origin_invar Q; k ∈ K; v ≠ nil⟧ ⟹
    origin_lookup (origin_put k v Q) = (origin_lookup Q)(k ↦ v)"
  by (rule origin_lookup_upd)

lemma parent_delete_lookup:
  "⟦parent_invar P; k ∈ K⟧ ⟹
    parent_lookup (parent_delete k P) = (parent_lookup P)(k := None)"
  by (auto simp: parent_lookup_def parent_map.fixed_univ_map_upd)

lemma origin_delete_lookup:
  "⟦origin_invar Q; k ∈ K⟧ ⟹
    origin_lookup (origin_delete k Q) = (origin_lookup Q)(k := None)"
  by (auto simp: origin_lookup_def origin_map.fixed_univ_map_upd)

lemma parent_lookup_not_nil:
  "parent_lookup P x = Some y ⟹ y ≠ nil"
  by (auto simp: parent_lookup_def split: if_splits)

lemma origin_lookup_not_nil:
  "origin_lookup Q x = Some y ⟹ y ≠ nil"
  by (auto simp: origin_lookup_def split: if_splits)


lemma parent_delete_list:
  assumes "parent_invar P" "set xs ⊆ K"
  shows "parent_invar (foldl (λA x. parent_delete x A) P xs)"
    "parent_lookup (foldl (λA x. parent_delete x A) P xs) =
      (λx. if x ∈ set xs then None else parent_lookup P x)"
  using assms
  by (induction xs arbitrary: P)
    (auto simp: parent_map.fixed_univ_map_upd_invar parent_delete_lookup fun_eq_iff)

lemma parent_redirect_list:
  fixes C
  assumes "parent_invar P" "set xs ⊆ K" "v ≠ nil"
  defines "step ≡ λA x. if C (parent_lookup A x) then parent_put x v A else A"
  shows "parent_invar (foldl step P xs)"
    "parent_lookup (foldl step P xs) =
      (λx. if x ∈ set xs ∧ C (parent_lookup P x) then Some v else parent_lookup P x)"
  using assms
  by (induction xs arbitrary: P)
    (auto simp: step_def parent_map.fixed_univ_map_upd_invar parent_put_lookup fun_eq_iff
      split: if_splits)

lemma origin_delete_list:
  assumes "origin_invar Q" "set xs ⊆ K"
  shows "origin_invar (foldl (λA x. origin_delete x A) Q xs)"
    "origin_lookup (foldl (λA x. origin_delete x A) Q xs) =
      (λx. if x ∈ set xs then None else origin_lookup Q x)"
  using assms
  by (induction xs arbitrary: Q)
    (auto simp: origin_map.fixed_univ_map_upd_invar origin_delete_lookup fun_eq_iff)

lemma origin_redirect_list:
  fixes C
  assumes "origin_invar Q" "set xs ⊆ K" "v ≠ nil"
  defines "step ≡ λA x. if C (origin_lookup A x) then origin_put x v A else A"
  shows "origin_invar (foldl step Q xs)"
    "origin_lookup (foldl step Q xs) =
      (λx. if x ∈ set xs ∧ C (origin_lookup Q x) then Some v else origin_lookup Q x)"
  using assms
  by (induction xs arbitrary: Q)
    (auto simp: step_def origin_map.fixed_univ_map_upd_invar origin_put_lookup fun_eq_iff
      split: if_splits)

lemma vset_delete_list:
  assumes "vset_invar S"
  shows "vset_invar (foldl (λA x. vset_delete x A) S xs)"
    "vset_to_set (foldl (λA x. vset_delete x A) S xs) = vset_to_set S - set xs"
  using assms
  by (induction xs arbitrary: S) (auto simp: vset.fixed_univ_set_delete)

lemma forest_vertices_in_universe:
  assumes "forest_invar M F"
  shows "verts F ⊆ K"
  using invar_basicD(1,2,3,6)[OF forest_invarD(1)[OF assms]]
    vset.fixed_univ_set_universe
  by blast


lemma forest_invar_odd_is_parent:
  "forest_invar M F ⟹ invar_odd_is_parent F"
  by (rule forest_invarD(8))

lemma odds_unique_child:
  assumes "forest_invar ℳ F" "x ∈ vset_to_set (odds F)" "matching ℳ"
  obtains y where "parent_lookup (parents F) y = Some x" "{x, y} ∈ ℳ"
    "y ∈ vset_to_set (evens F)"
    "⋀ y'. parent_lookup (parents F) y' = Some x ⟹ y = y'"
proof(goal_cases)
  case 1
  obtain y where y: "parent_lookup (parents F) y = Some x"
    using assms(2) forest_invar_odd_is_parent[OF assms(1)] invar_odd_is_parentD by blast
  hence xy_in_forest: "{x, y} ∈ abstract_forest F"
    by (auto simp: abstract_forest_def insert_commute)
  hence  y_even: "y ∈ vset_to_set (evens F)" 
    using invar_forest_even_and_oddD[of F y x] assms
    by (simp add: forest_invarD(3) insert_commute)
  hence yx_match: "{x, y} ∈ ℳ"  
    using y  assms(1)
    by(auto  elim!: forest_invarE simp add: insert_commute[of x y]
        dest!: invar_even_to_parent_matchingD)
  show ?thesis
  proof(rule 1[OF y yx_match y_even], goal_cases)
    case (1 y')
    hence xy'_in_forest: "{x, y'} ∈ abstract_forest F"
      by (auto simp: abstract_forest_def insert_commute)
    hence  y'_even: "y' ∈ vset_to_set (evens F)" 
      using invar_forest_even_and_oddD[of F y' x] assms
      by (simp add: forest_invarD(3) insert_commute)
    hence "{x, y'} ∈ ℳ" 
      using 1 y'_even assms(1)
      by(auto elim!: forest_invarE simp add: insert_commute[of x y']
          dest!: invar_even_to_parent_matchingD)
    then show ?case 
      using assms(3) doubleton_in_matching(1) yx_match by fastforce
  qed
qed

lemma odds_unique_child':
  assumes "forest_invar ℳ F" "x ∈ vset_to_set (odds F)" "matching ℳ"
    "parent_lookup (parents F) y = Some x" "parent_lookup (parents F) y' = Some x"
  shows "y = y'"
  using assms odds_unique_child[of ℳ F x] by auto

lemma odds_child:
  assumes "forest_invar ℳ F" "x ∈ vset_to_set (odds F)" "matching ℳ"
  obtains y where "parent_lookup (parents F) y = Some x" "{x, y} ∈ ℳ"
    "y ∈ vset_to_set (evens F)"
  using assms odds_unique_child[of ℳ F x] by metis


definition "Dabstract_forest F = {(x, y) | x y. Some x = parent_lookup (parents F) y}"

lemma Dabstract_forest_UD:
  "UD (Dabstract_forest F) = abstract_forest F"
  by(force simp add: Dabstract_forest_def abstract_forest_def UD_def)

lemma invar_parent_Dabstract_forest_wf:
  "invar_parent_wf F ⟷ wf (Dabstract_forest F)"
  by (auto simp add: invar_parent_wf_def Dabstract_forest_def parent_spec_def)

lemma finite_abstract_Dabstract_forest:
  "finite (abstract_forest F) ⟷ finite (Dabstract_forest F)"
  by(auto simp add: Dabstract_forest_UD[symmetric] simp add: finite_UD)

lemma dVs_Vs_Dabstract_abstract_forest:
  "dVs (Dabstract_forest F) = Vs (abstract_forest F)"
  using Vs_dVs_UD[of "Dabstract_forest F"] Dabstract_forest_UD[of F] by simp


lemma get_path_eq_follow:
  assumes "forest_invar M F"
  shows "get_path F v = follow (parent_lookup (parents F)) v"
proof -
  interpret parents_here: parent "parent_lookup (parents F)"
    by (rule follow_dom_invar_parent_wf(1)[OF forest_invarD(4)[OF assms]])
  show ?thesis
    using get_path_is_follow_impl[OF follow_dom_invar_parent_wf(2)[OF forest_invarD(4)[OF assms]]]
      parents_here.follow_impl_is_follow[folded follow_def follow_impl_def]
    by simp
qed

end


lemma exI2: "P x y ⟹ ∃ x y. P x y"
  by auto

locale alternating_forest_fork_contraction_spec = 
alternating_forest_spec evens odds get_path abstract_forest forest_invar roots
    for evens::"'forest ⇒ 'vset"
    and odds::"'forest ⇒ 'vset"
    and get_path::"'forest ⇒ 'v ⇒ 'v list"
    and abstract_forest::"'forest ⇒ 'v set set"
    and forest_invar::"'v set set ⇒ 'forest ⇒ bool"
    and roots::"'forest ⇒ 'vset"
    and K::"'v set" +
  fixes contract_fork::"'forest ⇒ 'v list ⇒ 'v list ⇒ 'v ⇒ 'forest" 
  assumes contract_fork_basis:
   "⋀ℳ F v v' B1 B2 u new_vert P contr.
     contract_fork_precond ℳ F v v' B1 B2 u new_vert P contr ⟹ new_vert ∈ K ⟹
     forest_invar (quot_graph contr ℳ - {{new_vert}})
                  (contract_fork F (B1@[u]) (B2@[u]) new_vert)"
   "⋀ℳ F v v' B1 B2 u new_vert P contr.
     contract_fork_precond ℳ F v v' B1 B2 u new_vert P contr ⟹ new_vert ∈ K ⟹
     abstract_forest (contract_fork F (B1@[u]) (B2@[u]) new_vert) 
     = quot_graph contr (abstract_forest F) - {{new_vert}}"
   "⋀ℳ F v v' B1 B2 u new_vert P contr.
     contract_fork_precond ℳ F v v' B1 B2 u new_vert P contr ⟹ new_vert ∈ K ⟹
      vset_to_set (evens (contract_fork F (B1@[u]) (B2@[u]) new_vert)) 
    = vset_to_set (evens F) - ({u} ∪ set B1 ∪ set B2) ∪ {new_vert}"
   "⋀ℳ F v v' B1 B2 u new_vert P contr.
     contract_fork_precond ℳ F v v' B1 B2 u new_vert P contr ⟹ new_vert ∈ K ⟹
     vset_to_set (roots (contract_fork F (B1@[u]) (B2@[u]) new_vert)) =
    (if u ∈ vset_to_set (roots F) then vset_to_set (roots F) - {u} ∪ {new_vert} 
     else vset_to_set (roots F))"
   "⋀ℳ F v v' B1 B2 u new_vert P contr.
     contract_fork_precond ℳ F v v' B1 B2 u new_vert P contr ⟹ new_vert ∈ K ⟹
     matching (quot_graph contr ℳ - {{new_vert}})"
begin

lemma contract_fork_spec:
   "⋀ℳ F v v' B1 B2 u new_vert P contr.
     contract_fork_precond ℳ F v v' B1 B2 u new_vert P contr ⟹ new_vert ∈ K ⟹
     forest_invar (quot_graph contr ℳ - {{new_vert}})
                  (contract_fork F (B1@[u]) (B2@[u]) new_vert)"
   "⋀ℳ F v v' B1 B2 u new_vert P contr.
     contract_fork_precond ℳ F v v' B1 B2 u new_vert P contr ⟹ new_vert ∈ K ⟹
     abstract_forest (contract_fork F (B1@[u]) (B2@[u]) new_vert) 
     = quot_graph contr (abstract_forest F) - {{new_vert}}"
   "⋀ℳ F v v' B1 B2 u new_vert P contr.
     contract_fork_precond ℳ F v v' B1 B2 u new_vert P contr ⟹ new_vert ∈ K ⟹
     vset_to_set (odds (contract_fork F (B1@[u]) (B2@[u]) new_vert)) 
     = vset_to_set (odds F) - ({u} ∪ set B1 ∪ set B2)"
   "⋀ℳ F v v' B1 B2 u new_vert P contr.
     contract_fork_precond ℳ F v v' B1 B2 u new_vert P contr ⟹ new_vert ∈ K ⟹
      vset_to_set (evens (contract_fork F (B1@[u]) (B2@[u]) new_vert)) 
    = vset_to_set (evens F) - ({u} ∪ set B1 ∪ set B2) ∪ {new_vert}"
   "⋀ℳ F v v' B1 B2 u new_vert P contr.
     contract_fork_precond ℳ F v v' B1 B2 u new_vert P contr ⟹ new_vert ∈ K ⟹
     vset_to_set (roots (contract_fork F (B1@[u]) (B2@[u]) new_vert)) =
    (if u ∈ vset_to_set (roots F) then vset_to_set (roots F) - {u} ∪ {new_vert} 
     else vset_to_set (roots F))"
   "⋀ℳ F v v' B1 B2 u new_vert P contr.
     contract_fork_precond ℳ F v v' B1 B2 u new_vert P contr ⟹ new_vert ∈ K ⟹
     matching (quot_graph contr ℳ - {{new_vert}})"
  subgoal by (rule contract_fork_basis(1))
  subgoal by (rule contract_fork_basis(2))
  subgoal premises prems for M F v v' B1 B2 u new_vert P contr
  proof -
    let ?C = "{u} ∪ set B1 ∪ set B2"
    have inv: "forest_invar M F"
      and fresh: "new_vert ∉ Vs M ∪ vset_to_set (evens F) ∪ vset_to_set (odds F) - ?C"
      and contr: "contr = (λx. if x ∈ ?C then new_vert else x)"
      using prems(1) by (auto elim!: contract_fork_precondE)
    have fresh_forest: "new_vert ∉ Vs (abstract_forest F) - ?C"
      using fresh evens_and_odds_basis(3)[OF inv] by blast
    have erase: "Vs (G - {{new_vert}}) - {new_vert} = Vs G - {new_vert}" for G
      by (auto simp: Vs_def)
    have outside: "Vs (quot_graph contr (abstract_forest F) - {{new_vert}}) - {new_vert} =
        Vs (abstract_forest F) - ?C"
      unfolding erase Vs_quot_graph_is_img contr
      using fresh_forest by auto
    show ?thesis
      unfolding odds_eq_Vs_minus_evens[OF contract_fork_basis(1)[OF prems]]
        contract_fork_basis(2,3)[OF prems]
      using outside odds_eq_Vs_minus_evens[OF inv] by auto
  qed
  subgoal by (rule contract_fork_basis(3))
  subgoal by (rule contract_fork_basis(4))
  subgoal by (rule contract_fork_basis(5))
  done

end

locale forest_contract_manipulation_spec=
  forest_manipulation_spec 
  where vset_insert = vset_insert
    and parent_empty = parent_empty
    and origin_empty = origin_empty
  for vset_insert::"'v ⇒ 'vset ⇒ 'vset"
    and parent_empty ::'parent
    and origin_empty::'origin + 
  fixes vset_iterate_parent :: "('parent ⇒ 'v ⇒ 'parent) ⇒ 'parent ⇒ 'vset ⇒ 'parent"
    and vset_union::"'vset ⇒ 'vset ⇒ 'vset"
begin

definition "vset_from_list xs = foldl (λ S x. vset_insert x S) vset_empty xs"

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
        ods_new = foldl (λ S x. vset_delete x S) ods ods_in_p;
        evs_new' = foldl (λ S x. vset_delete x S) evs evs_in_p;
        prnts_wthout_p = foldl (λ x pmap. parent_delete pmap x) prnts p;
        prnts_new_connected = 
            vset_iterate_parent 
               (λ cprnts x. if vset_isin evs_in_p_set (the (parent_lookup cprnts x)) 
                            then parent_put x new_vert cprnts
                            else cprnts)
                prnts_wthout_p ods_new;
        new_prnts = (case parent_lookup prnts (last p)
                     of None ⇒ prnts_new_connected 
                     | Some xpred ⇒ parent_put new_vert xpred prnts_new_connected);
        orns_wthout_p = foldl (λ x omap. origin_delete omap x) orngs p;
        old_orgn = the (origin_lookup orngs (last p));
        new_orgns = (if old_orgn ≠ (last p)
                     then origin_put new_vert old_orgn orns_wthout_p
                     else origin_put new_vert new_vert (vset_iterate 
                           (λ org x. if the (origin_lookup org x) = old_orgn
                                     then origin_put x new_vert org
                                     else org) orns_wthout_p 
                          (vset_union ods_new evs_new')))
      in Forest (if vset_isin rts (last p) 
                 then vset_insert new_vert (vset_delete (last p) rts) 
                 else rts )

                 (vset_insert new_vert (foldl (λ S x. vset_delete x S) evs evs_in_p))

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
  for vset_insert::"'v ⇒ 'vset ⇒ 'vset"
    and parent_empty ::'parent
    and origin_empty::'origin + 
  assumes vset_iterate_parent:
    "⋀ V f init. vset_invar V ⟹ 
          ∃ vs. vset_to_set V = set vs ∧ distinct vs ∧
            vset_iterate_parent f init V = foldl f init vs"
    and vset_union:
    "⋀ S T. ⟦vset_invar S; vset_invar T⟧ ⟹ vset_invar (vset_union S T)"
    "⋀ S T. ⟦vset_invar S; vset_invar T⟧ 
       ⟹ vset_to_set (vset_union S T) = vset_to_set S ∪ vset_to_set T"
begin

lemma vset_from_list:
  assumes "set xs ⊆ K"
  shows
  "vset_invar (vset_from_list xs)"
  "vset_to_set (vset_from_list xs) = set xs"
proof-
  define xs' where "xs' = rev xs"
  have set_same: "set xs = set xs'"
    by(simp add: xs'_def)
  have  "vset_invar (vset_from_list xs) ∧
        vset_to_set (vset_from_list xs) = set xs"
    unfolding vset_from_list_def foldl_conv_foldr xs'_def[symmetric] set_same
    using assms[unfolded set_same]
    by(induction xs')
      (auto simp add: vset.fixed_univ_set_empty(1) vset.fixed_univ_set_empty(2) vset.fixed_univ_set_insert(1) vset.fixed_univ_set_insert(2))
  thus "vset_invar (vset_from_list xs)"
    "vset_to_set (vset_from_list xs) = set xs"
    by auto
qed
  
lemma effect_of_contract_path:
  assumes "vset_invar evs" "vset_invar ods" 
    "vset_invar rts" "parent_invar prnts" "origin_invar orngs"
    and new_forest_def:
    "new_forest = contract_path (Forest rts evs ods prnts orngs) p new_vert"
  and bounds: "set p ⊆ K" "new_vert ∈ K"
    "origin_lookup orngs (last p) ≠ None"
  shows   "vset_invar (roots new_forest)"
    "vset_invar (evens new_forest)"
    "vset_invar (odds new_forest)"
    "parent_invar (parents new_forest)"
    "origin_invar (origins new_forest)"
    and 
    "vset_to_set (roots new_forest) =
  (if (last p) ∈ vset_to_set rts then vset_to_set rts - {last p} ∪ {new_vert}
         else vset_to_set rts)" (is ?th1)
    and "vset_to_set (odds new_forest) =
     vset_to_set ods - {p ! i | i. i < length p ∧ odd i}" (is ?th2)
    and "vset_to_set (evens new_forest) =
     vset_to_set evs - {p ! i | i. i < length p ∧ even i} ∪ {new_vert}" (is ?th3)
    and "parent_lookup (parents new_forest) = 
    (λx. if x = new_vert ∧ parent_lookup prnts (last p) ≠ None 
           then parent_lookup prnts (last p)
      else if (x ∈ set p ⟶
               the None ∈ {p ! i |i. i < length p ∧ even i} ∧
               x ∈ vset_to_set ods - {p ! i |i. i < length p ∧ odd i}) ∧
              (x ∉ set p ⟶
               the (parent_lookup prnts x) ∈ {p ! i |i. i < length p ∧ even i} ∧
               x ∈ vset_to_set ods - {p ! i |i. i < length p ∧ odd i})
           then Some new_vert else if x ∈ set p then None else parent_lookup prnts x)" (is ?th4)
    and "origin_lookup (origins new_forest) =
    (λ x. if x = new_vert ∧ the (origin_lookup orngs (last p)) ≠ last p 
                then Some (the (origin_lookup orngs (last p)))
          else if x ∈ set p ∧ the (origin_lookup orngs (last p)) ≠ last p then None
          else if the (origin_lookup orngs (last p)) ≠ last p then origin_lookup orngs x
          else if x = new_vert then Some new_vert
          else if x ∈ vset_to_set ods - {p ! i |i. i < length p ∧ odd i} ∪
                            (vset_to_set evs - {p ! i |i. i < length p ∧ even i}) ∧
                       the (if x ∈ set p then None else origin_lookup orngs x) =
                       the (origin_lookup orngs (last p))
               then Some new_vert
          else if x ∈ set p then None 
          else origin_lookup orngs x)" (is ?th5)
proof-
  define evs_in_p where "evs_in_p = take_evens p"
  define ods_in_p where "ods_in_p = take_odds p"
  define evs_in_p_set where "evs_in_p_set = vset_from_list evs_in_p"
  define ods_new where "ods_new = foldl (λ S x. vset_delete x S) ods ods_in_p"
  define evs_new' where "evs_new' = foldl (λ S x. vset_delete x S) evs evs_in_p"
  define prnts_wthout_p where 
    "prnts_wthout_p = foldl (λ x pmap. parent_delete pmap x) prnts p"
  define prnts_new_connected where "prnts_new_connected = 
            vset_iterate_parent 
               (λ cprnts x. if vset_isin evs_in_p_set (the (parent_lookup cprnts x)) 
                            then parent_put x new_vert cprnts
                            else cprnts)
                prnts_wthout_p ods_new"
  define new_prnts where "new_prnts = (case parent_lookup prnts (last p)
                     of None ⇒ prnts_new_connected 
                     | Some xpred ⇒ parent_put new_vert xpred prnts_new_connected)"
  define orns_wthout_p where  
    "orns_wthout_p = foldl (λ x omap. origin_delete omap x) orngs p"
  define old_orgn where "old_orgn = the (origin_lookup orngs (last p))"
  define new_orgns where "new_orgns = (if old_orgn ≠ (last p)
                     then origin_put new_vert old_orgn orns_wthout_p
                     else origin_put new_vert new_vert (vset_iterate 
                           (λ org x. if the (origin_lookup org x) = old_orgn
                                     then origin_put x new_vert org
                                     else org) orns_wthout_p 
                          (vset_union ods_new evs_new')))"
  define new_roots where "new_roots = (if vset_isin rts (last p) 
                 then vset_insert new_vert (vset_delete (last p) rts) 
                 else rts)"
  define evs_new where "evs_new = vset_insert new_vert (foldl (λ S x. vset_delete x S) evs evs_in_p)"

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


  have new_vert_not_nil: "new_vert ≠ nil"
    using bounds(2) nil by auto
  have evs_in_p_bound: "set evs_in_p ⊆ K"
    using bounds(1) by (auto simp: evs_in_p_def take_evens_set)
  have old_orgn_not_nil: "old_orgn ≠ nil"
    using bounds(3) origin_lookup_not_nil[of orngs "last p"]
    by (cases "origin_lookup orngs (last p)") (auto simp: old_orgn_def)
  have new_roots_props:
    "vset_invar new_roots"
    "vset_to_set new_roots =
      (if last p ∈ vset_to_set rts then vset_to_set rts - {last p} ∪ {new_vert}
       else vset_to_set rts)"
    using assms(3) bounds(2)
    by (auto simp: new_roots_def vset.fixed_univ_set_isin vset.fixed_univ_set_delete
        vset.fixed_univ_set_insert)
  have ods_new_props:
    "vset_invar ods_new"
    "vset_to_set ods_new = vset_to_set ods - set ods_in_p"
    using vset_delete_list[OF assms(2), of ods_in_p]
    by (simp_all only: ods_new_def)
  have evs_new'_props:
    "vset_invar evs_new'"
    "vset_to_set evs_new' = vset_to_set evs - set evs_in_p"
    using vset_delete_list[OF assms(1), of evs_in_p]
    by (simp_all only: evs_new'_def)
  have evs_new_props:
    "vset_invar evs_new"
    "vset_to_set evs_new = vset_to_set evs - set evs_in_p ∪ {new_vert}"
    using evs_new'_props bounds(2)
    by (auto simp: evs_new_def evs_new'_def[symmetric] vset.fixed_univ_set_insert)
  have evs_in_p_set_props:
    "vset_invar evs_in_p_set" "vset_to_set evs_in_p_set = set evs_in_p"
    using vset_from_list[OF evs_in_p_bound]
    by (simp_all only: evs_in_p_set_def)
  have prnts_wthout_p_props:
    "parent_invar prnts_wthout_p"
    "parent_lookup prnts_wthout_p = (λx. if x ∈ set p then None else parent_lookup prnts x)"
    using parent_delete_list[OF assms(4) bounds(1)]
    by (simp_all only: prnts_wthout_p_def)
  define f1 where "f1 = (λA x. if vset_isin evs_in_p_set (the (parent_lookup A x))
    then parent_put x new_vert A else A)"
  obtain vs1 where vs1: "vset_to_set ods_new = set vs1" "distinct vs1"
    "vset_iterate_parent f1 prnts_wthout_p ods_new = foldl f1 prnts_wthout_p vs1"
    using vset_iterate_parent[OF ods_new_props(1), of f1 prnts_wthout_p] by auto
  have vs1_bound: "set vs1 ⊆ K"
    using vset.fixed_univ_set_universe[OF ods_new_props(1)] vs1(1) by simp
  have prnts_new_connected_props:
    "parent_invar prnts_new_connected"
    "parent_lookup prnts_new_connected =
      (λx. if the (parent_lookup prnts_wthout_p x) ∈ set evs_in_p ∧ x ∈ vset_to_set ods_new
       then Some new_vert else parent_lookup prnts_wthout_p x)"
    using parent_redirect_list[OF prnts_wthout_p_props(1) vs1_bound new_vert_not_nil,
      where C="λq. vset_isin evs_in_p_set (the q)"]
    unfolding prnts_new_connected_def vs1(3)[unfolded f1_def]
    by (simp_all add: vset.fixed_univ_set_isin[OF evs_in_p_set_props(1)] evs_in_p_set_props(2) vs1(1) conj_commute)
  have new_prnts_props:
    "parent_invar new_prnts"
    "parent_lookup new_prnts =
      (λx. if x = new_vert ∧ parent_lookup prnts (last p) ≠ None
       then parent_lookup prnts (last p)
       else if (x ∈ set p ⟶ the None ∈ set evs_in_p ∧ x ∈ vset_to_set ods_new) ∧
         (x ∉ set p ⟶ the (parent_lookup prnts x) ∈ set evs_in_p ∧ x ∈ vset_to_set ods_new)
       then Some new_vert else if x ∈ set p then None else parent_lookup prnts x)"
    using parent_lookup_not_nil[of prnts "last p"] bounds(2)
    by (auto simp: new_prnts_def parent_put_lookup parent_map.fixed_univ_map_upd_invar
        prnts_new_connected_props prnts_wthout_p_props fun_eq_iff split: option.splits)
  have orns_wthout_p_props:
    "origin_invar orns_wthout_p"
    "origin_lookup orns_wthout_p = (λx. if x ∈ set p then None else origin_lookup orngs x)"
    using origin_delete_list[OF assms(5) bounds(1)]
    by (simp_all only: orns_wthout_p_def)
  define f2 where "f2 = (λA x. if the (origin_lookup A x) = old_orgn
    then origin_put x new_vert A else A)"
  define intermed_orgn where
    "intermed_orgn = vset_iterate f2 orns_wthout_p (vset_union ods_new evs_new')"
  have vset_uniony:
    "vset_invar (vset_union ods_new evs_new')"
    "vset_to_set (vset_union ods_new evs_new') = vset_to_set ods_new ∪ vset_to_set evs_new'"
    using vset_union[OF ods_new_props(1) evs_new'_props(1)] by auto
  obtain vs2 where vs2: "vset_to_set (vset_union ods_new evs_new') = set vs2" "distinct vs2"
    "vset_iterate f2 orns_wthout_p (vset_union ods_new evs_new') = foldl f2 orns_wthout_p vs2"
    using vseta[OF vset_uniony(1), of f2 orns_wthout_p] by auto
  have vs2_bound: "set vs2 ⊆ K"
    using vset.fixed_univ_set_universe[OF vset_uniony(1)] vs2(1) by simp
  have intermed_orgn_props:
    "origin_invar intermed_orgn"
    "origin_lookup intermed_orgn =
      (λx. if x ∈ vset_to_set ods_new ∪ vset_to_set evs_new' ∧
        the (origin_lookup orns_wthout_p x) = old_orgn
       then Some new_vert else origin_lookup orns_wthout_p x)"
    using origin_redirect_list[OF orns_wthout_p_props(1) vs2_bound new_vert_not_nil,
      where C="λq. the q = old_orgn"]
    unfolding intermed_orgn_def f2_def vs2(3)[unfolded f2_def]
    by (simp_all add: vs2(1)[symmetric] vset_uniony(2))
  have new_orgns_eq: "new_orgns =
      (if old_orgn ≠ last p then origin_put new_vert old_orgn orns_wthout_p
       else origin_put new_vert new_vert intermed_orgn)"
    by (simp only: new_orgns_def intermed_orgn_def f2_def)
  have new_orgns_props:
    "origin_invar new_orgns"
    "origin_lookup new_orgns =
      (if old_orgn ≠ last p then (origin_lookup orns_wthout_p)(new_vert ↦ old_orgn)
       else (origin_lookup intermed_orgn)(new_vert ↦ new_vert))"
    using bounds(2) new_vert_not_nil old_orgn_not_nil
    by (auto simp: new_orgns_eq origin_map.fixed_univ_map_upd_invar
        origin_put_lookup orns_wthout_p_props(1) intermed_orgn_props(1))
  show "vset_invar (roots new_forest)" "vset_invar (evens new_forest)"
    "vset_invar (odds new_forest)" "parent_invar (parents new_forest)"
    "origin_invar (origins new_forest)"
    using new_roots_props(1) evs_new_props(1) ods_new_props(1) new_prnts_props(1) new_orgns_props(1)
    by (simp_all only: news)
  show ?th1 ?th2 ?th3 ?th4
    by (simp_all only: news new_roots_props(2) ods_new_props(2) evs_new_props(2)
        new_prnts_props(2) ods_in_p_def evs_in_p_def take_odds_set take_evens_set)
  show ?th5
    by (auto simp: news new_orgns_props(2) intermed_orgn_props(2) orns_wthout_p_props(2)
        ods_new_props(2) evs_new'_props(2) old_orgn_def evs_in_p_def ods_in_p_def
        take_evens_set take_odds_set fun_eq_iff)
qed

definition Dquot_graph where
  "Dquot_graph P G = {(P u, P v)| u v. (u,v) ∈ G}"

lemma Dquot_id:  "Dquot_graph id G = G"
  by(auto simp add: Dquot_graph_def)

lemma Dquot_quot_UD:"UD (Dquot_graph P G) = quot_graph P (UD G)"
  by(auto simp add: Dquot_graph_def quot_graph_def UD_def)

lemma Dquot_graph_alt_def:
  assumes contr_def: "contr = (λ v. if v ∈ set p then new_vert else v)"
    and new_vert_where: "new_vert ∉ dVs G - set p"
  shows "Dquot_graph contr G - {(new_vert, new_vert)} =
    G - ⋃ {δ⇧+ G x |x. x ∈ set p} - ⋃ {δ⇧- G x |x. x ∈ set p} ∪
    {(new_vert, y) |y. y ∈ Γ⇧+ G set p} ∪
    {(y, new_vert) |y. y ∈ Γ⇧- G set p}"
proof(rule, all ‹rule›, goal_cases)
  case (1 e)
  then obtain u v where uv: "e = (u, v)"
    by(cases e) auto
  then obtain u' v' where  "u = contr u'" "v = contr v'" "(u', v') ∈ G"
       "u ≠ new_vert ∨ v ≠ new_vert"
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
      then obtain u v where uv: "e = (u, v)" "(u, v) ∈ G"
        by(cases e) auto
      have "e = (contr u, contr v)"
        if "u ∉ set p" "v ∉ set p"
        using that by(auto simp add: uv contr_def)
      moreover have False
        if "u ∈ set p" 
      proof-
        have "e ∈ δ⇧+ G u"
          using 1 by(auto simp add: uv delta_plus_def delta_minus_def) 
        hence "e∈ ⋃ {δ⇧+ G x |x. x ∈ set p}" using that by auto
        thus False
          using 1 by simp
      qed
      moreover have False
        if "v ∈ set p"
      proof-
        have "e ∈ δ⇧- G v"
          using 1 by(auto simp add: uv delta_plus_def delta_minus_def) 
        hence "e∈ ⋃ {δ⇧- G x |x. x ∈ set p}" using that by auto
        thus False
          using 1 by simp
      qed
      moreover have "e ≠ (new_vert, new_vert)"
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
  assumes "forest_invar ℳ (Forest rts evs ods prnts orngs)" 
    "follow (parent_lookup prnts) v = p1@[u]@p2"
    "v ∈ vset_to_set evs"
    "u ∈ vset_to_set evs" "matching ℳ"
    "new_vert ∉ Vs ℳ ∪ vset_to_set evs ∪ vset_to_set ods -  set (p1@[u])"
    "dblton_graph ℳ"
    and contr_def: "contr = (λ v. if v ∈ set (p1@[u]) then new_vert else v)"
    and new_forest_def:
    "new_forest = contract_path (Forest rts evs ods prnts orngs) (p1@[u]) new_vert"
  and new_vert_in_universe: "new_vert ∈ K"
  shows "forest_invar (quot_graph contr ℳ - {{new_vert}}) new_forest" (is ?th1)
    and  "abstract_forest new_forest 
         = quot_graph contr (abstract_forest (Forest rts evs ods prnts orngs)) - {{new_vert}}" (is ?th2)
    and "vset_to_set (odds new_forest) = vset_to_set ods - set (p1 @ [u])" 
    and "vset_to_set (evens new_forest) = vset_to_set evs - set (p1 @ [u]) ∪ {new_vert}"
    and "vset_to_set (roots new_forest) =
    (if u ∈ vset_to_set rts
     then vset_to_set rts - {u} ∪ {new_vert} else vset_to_set rts)" (is ?th3)
    and "matching (quot_graph contr ℳ - {{new_vert}})" (is ?th4)
    and "⟦follow (parent_lookup prnts) v' = p1'@[u]@p2; set p1 ∩ set p1' = {}⟧ ⟹
     follow (parent_lookup (parents new_forest)) 
     (if p1' = [] then new_vert else v') = p1'@[new_vert]@p2"
    (is "⟦?asm1;?asm2⟧⟹ ?th5")
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

  have path_in_universe: "set (p1 @ [u]) ⊆ K"
    using path_follow_verts_in_verts_F[OF forest_invar_F(1,6,4), of v]
      forest_vertices_in_universe[OF assms(1)] assms(2,3) invar_basic_F(6)
    by auto blast+
  have origin_defined: "origin_lookup orngs (last (p1 @ [u])) ≠ None"
    using invar_rootsD(2)[OF forest_invar_F(6), of u] assms(4) invar_basic_F(6)
    by (auto simp only: alt_forest.sel last_snoc)
  note effect_of_contract_path =
    effect_of_contract_path[OF invar_basic_F(2,3,1,4,5) new_forest_def
      path_in_universe new_vert_in_universe origin_defined]

  note follow_alt_here = follow_alternating_paths(1,3)[OF assms(1), 
      simplified, OF assms(2)[symmetric] assms(3)]

  have alternating_p:
    "alt_list (λx. x ∈ vset_to_set evs) (λx. x ∈ vset_to_set ods) (p1 @ [u])"
    using alt_list_append_1[OF follow_alt_here(2)[unfolded append.assoc[symmetric]]]
    by blast
  have path_parity:
    "(p1 @ [u]) ! i ∈ vset_to_set evs ⟷ even i"
    "(p1 @ [u]) ! i ∈ vset_to_set ods ⟷ odd i"
    if "i < length (p1 @ [u])" for i
    using alternating_list_even_index[OF alternating_p _ that]
      alternating_list_odd_index[OF alternating_p _ that] invar_basic_F(7)
    by auto
  have evens_in_p_are: "{(p1 @ [u]) ! i |i. i < length (p1 @ [u]) ∧ even i} =
        vset_to_set evs ∩ set (p1 @ [u])"
    using path_parity(1)
    by (auto simp only: mem_Collect_eq Int_iff in_set_conv_nth; blast)
  have odds_in_p_are: "{(p1 @ [u]) ! i |i. i < length (p1 @ [u]) ∧ odd i} =
        vset_to_set ods ∩ set (p1 @ [u])"
    using path_parity(2)
    by (auto simp only: mem_Collect_eq Int_iff in_set_conv_nth; blast)

  have new_parents_are: "parent_lookup (parents new_forest) =
    (λx. if x = new_vert ∧ parent_lookup prnts u ≠ None
          then parent_lookup prnts u
          else if (x ∉ set (p1 @ [u]) ∧ the (parent_lookup prnts x)
                   ∈ set (p1 @ [u]) ∩ vset_to_set evs ∧
                   x ∈ vset_to_set ods - set (p1@[u]))
               then Some new_vert
          else if x ∈ set (p1 @ [u]) then None 
          else parent_lookup prnts x)"
    by(rule ext, unfold effect_of_contract_path(9) evens_in_p_are odds_in_p_are)
       auto
  have prnts_no_loop:"parent_lookup prnts u = Some u ⟹ False" for u
    using forest_invar_F(4)
    by(auto intro!: wf_no_loop dest!: invar_parent_wfD parent_specD)
  have DAF_no_loop:"(u,u) ∈ Dabstract_forest (Forest rts evs ods prnts orngs) ⟹ False" for u
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
   "⟦parent_lookup prnts x = Some y; x ∉ vset_to_set ods ∨ y ∉ vset_to_set evs;
     p1 = ys @ y # zs; x ∉ set ys ∨ y = u⟧ ⟹ False"
    for ys zs x y
  proof(goal_cases)
    case 1
    have y_not_u:"y ≠ u"
      using follow_distinct[of v] 1(3) assms(2) by auto
    have xy_af:"{x, y} ∈ abstract_forest (Forest rts evs ods prnts orngs)"
      using 1 abstract_forest_def by fastforce
    hence "x ∈ vset_to_set evs ⟷  x ∉ vset_to_set ods"
          "y ∈ vset_to_set evs ⟷ y ∉ vset_to_set ods"
      using edges_are_Vs[OF xy_af] edges_are_Vs_2[OF xy_af] invar_basic_F(6,7)
      by blast+
    hence even_x: "x ∈ vset_to_set evs"
      and odd_y: "y ∈ vset_to_set ods"
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
      using "1"(4) ‹y' = x› y'ys' y_not_u by auto
  qed

  have Dabstract_forest_new_in_Qquot: "Dabstract_forest new_forest ⊆
    Dquot_graph contr (Dabstract_forest (Forest rts evs ods prnts orngs))"
    unfolding abstract_forest_def
  proof(rule, goal_cases)
    case (1 e)
    then obtain x y where xy: "e = (y, x)" "parent_lookup (parents new_forest) x = Some y"
      by(auto simp add: Dabstract_forest_def)
    show ?case
      using xy(2) unfolding xy(1) new_parents_are 
    proof(cases "x = new_vert ∧ parent_lookup prnts u ≠ None", goal_cases)
      case 1
      note 1 = 1[simplified if_P[OF 1(2)]]
      then show ?case 
        using in_set_conv_decomp[of y p1] assms(2) follow_not_again_parent[of v _ y _ u p2] 
        by(auto intro!: exI[of "λ y. (_ y ⟶ (_ y ∧ _ y)) ∧ (_ y ⟶ (_ y ∧ _ y))
                             ∧ (_ y ⟶ (_ y ∧ _ y))" y]
                 intro: exI[of _ u]
                  dest: prnts_no_loop 
              simp add: Dquot_graph_def contr_def Dabstract_forest_def)    
    next
      case 2
      note 2 = 2[simplified if_not_P[OF 2(2)]]
      then show ?case 
      proof(cases "x ∉ set (p1 @ [u]) ∧
        the (parent_lookup prnts x) ∈ set (p1 @ [u]) ∩ vset_to_set evs ∧
        x ∈ vset_to_set ods - set (p1 @ [u])", goal_cases)
        case 1
        note 1 = 1[simplified if_P[OF 1(3)]]
        hence "parent_lookup prnts x = Some (the (parent_lookup prnts x))"
          using  forest_invar_F(7) 
          by(auto elim!: invar_odd_to_parent_non_matchingE)
        then show ?case 
          using 1
          by(auto intro!: exI[of "λ ua. (_ ua ⟶ (∃ v. _ ua v)) ∧ _  ua ∧ _  ua " 
                            "(the (parent_lookup prnts x))"] 
                          exI[of "λ y. (_ y ⟶ (_ y ∧ _ y)) ∧ (_ y ⟶ (_ y ∧ _ y))
                             ∧ (_ y ⟶ (_ y ∧ _ y))" x] 
                simp add: Dquot_graph_def contr_def Dabstract_forest_def)
      next
        case 2
        note 2 = 2[simplified if_not_P[OF 2(3)]]
        then show ?case
        proof(cases "x ∈ set (p1 @ [u])", goal_cases)
          case 2
          note 2 = 2[simplified if_not_P[OF 2(4)]]
          have helper2:
           "⟦parent_lookup prnts x = Some y; x ∉ vset_to_set ods ∨ y ∉ vset_to_set evs;
             p1 = ys @ y # zs; x ∉ set ys ∨ y = u⟧ ⟹ False" for ys zs 
            using parent_adj_pu_helper[of x y ys zs] by blast
          have x_not_oddD:"x ∉ vset_to_set ods ⟹ x ∈ vset_to_set evs"
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

  have parent_u_not_new: "parent_lookup prnts u ≠ Some new_vert"
  proof
    assume parent_u: "parent_lookup prnts u = Some new_vert"
    have "{u,new_vert} ∈ ℳ"
      by (rule invar_even_to_parent_matchingD_here[OF assms(4) parent_u])
    then have "new_vert ∈ set (p1 @ [u])"
      using edges_are_Vs_2[of u new_vert ℳ] assms(6) by blast
    moreover have "new_vert ≠ u"
      using parent_u prnts_no_loop[of u] by auto
    ultimately obtain xs ys where p1: "p1 = xs @ [new_vert] @ ys"
      by (auto dest: split_list)
    show False
      using follow_not_again_parent[of v xs new_vert ys u p2] assms(2) parent_u
      by (simp add: p1)
  qed
  have new_vert_loop_not_in_new: "(new_vert,new_vert) ∉ Dabstract_forest new_forest"
  proof -
    show ?thesis
      using parent_u_not_new assms(6) prnts_no_loop[of new_vert]
      by (auto simp: new_parents_are Dabstract_forest_def)
  qed

  have Qquot_in_Dabstract_forest_new: 
   "Dabstract_forest new_forest ⊇ 
    Dquot_graph contr (Dabstract_forest (Forest rts evs ods prnts orngs)) 
      - {(new_vert,new_vert)}"
  proof(rule, goal_cases)
    case (1 e)
    then obtain u' v' where uv: "e = (contr u', contr v')" 
      "Some u' = parent_lookup prnts v'"
      "contr u' ≠ new_vert ∨ contr v' ≠ new_vert"
      by (auto simp add: Dquot_graph_def Dabstract_forest_def)
    have u_neq_v: "u' ≠ v'"
      using uv(2) prnts_no_loop[of u'] by auto
    have u'v'_AF:"{u', v'} ∈ abstract_forest (Forest rts evs ods prnts orngs)"
      unfolding abstract_forest_def
      apply (rule CollectI, rule exI[of _ v'], rule exI[of _ u'])
      using uv(2) by (simp add: insert_commute)
    hence u'v'_evens_and_odds: "{u', v'} ⊆ vset_to_set evs ∪ vset_to_set ods"
      using uv(2) by (simp add: edges_are_Vs edges_are_Vs_2 invar_basic_F(6))
    have ?case
      if "u' ∈ set (p1 @ [u])" "v' ∈ set (p1 @ [u])"
      using uv that u_neq_v by(auto simp add: contr_def)
    moreover have ?case
      if asm: "u' ∉ set (p1 @ [u])" "v' ∈ set (p1 @ [u])"    
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
      if asm: "u' ∈ set (p1 @ [u])" "v' ∉ set (p1 @ [u])"           
    proof-
      note uv = uv[simplified contr_def if_P[OF asm(1)] if_not_P[OF asm(2)], simplified]
      have u'v'_even_odd_eqiv: "u' ∈ vset_to_set evs ⟷ v' ∈ vset_to_set ods" 
        using uv(2) invar_forest_even_and_oddD[OF forest_invar_F(3), of u' v']
        by(force simp add: abstract_forest_def doubleton_eq_iff)
      obtain p1a p1b where p1a_p1b: "p1a@[u']@p1b = p1@[u]"
        using asm(1) split_list_last[of u' "p1 @ [u]"] by auto
      have u'_v'_parities: "u' ∈ vset_to_set evs ∧ v' ∈ vset_to_set ods"
      proof(rule ccontr, goal_cases)
        case 1
        hence u'_odd: "u' ∈ vset_to_set ods" and v'_even: "v' ∈ vset_to_set evs"
          using u'v'_even_odd_eqiv u'v'_evens_and_odds by auto
        hence "p1a ≠ []"
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
      if asm: "u' ∉ set (p1 @ [u])" "v' ∉ set (p1 @ [u])"
    proof-
      note uv = uv[simplified contr_def if_not_P[OF asm(1)] if_not_P[OF asm(2)], simplified]
      hence no_new_vert: "u' ≠ new_vert" "v' ≠ new_vert"
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
  have AF_in_quot:"abstract_forest new_forest ⊆
    quot_graph contr (abstract_forest (Forest rts evs ods prnts orngs))"
    using Dabstract_forest_new_in_Qquot UD_subseteq 
    by(auto simp add: Dabstract_forest_UD[symmetric] Dquot_quot_UD[symmetric])
  have new_vert_not_in_AF:"{new_vert} ∉ abstract_forest new_forest"
    using new_vert_loop_not_in_new
    by(auto simp add: Dabstract_forest_def abstract_forest_def)
  have quot_in_AF: 
      "quot_graph contr (abstract_forest (Forest rts evs ods prnts orngs)) - {{new_vert}}
       ⊆ abstract_forest new_forest"
    using Qquot_in_Dabstract_forest_new
    unfolding Dabstract_forest_UD[symmetric] Dquot_quot_UD[symmetric]
    by(auto simp add: UD_def) 
  have quot_is_AF: 
      "quot_graph contr (abstract_forest (Forest rts evs ods prnts orngs)) - {{new_vert}}
       = abstract_forest new_forest"
    using AF_in_quot new_vert_not_in_AF quot_in_AF by blast
  have Vs_contracted:"Vs (abstract_forest new_forest) ∪ {new_vert}= 
        Vs (abstract_forest (Forest rts evs ods prnts orngs)) - set (p1@[u]) ∪ {new_vert}"
    unfolding quot_is_AF[symmetric]
    by(auto simp add: quot_graph_def Vs_def contr_def)
  have Vs_contracted':
     "Vs (abstract_forest new_forest) = 
      Vs (abstract_forest (Forest rts evs ods prnts orngs)) - set (p1@[u]) ∪ {new_vert} "
  if asm: "last (p1 @ [u]) ∉ vset_to_set rts"
  proof(goal_cases)
    case 1
    obtain up where "parent_lookup prnts u = Some up"
      using asm[simplified] assms(4) invar_rootsD_here(2)[of u] invar_basic_F(13,6) 
      by blast
    hence "parent_lookup (parents new_forest) new_vert = Some up"
      by(simp add: new_parents_are)
    hence "new_vert ∈ Vs (abstract_forest new_forest)"
      by(auto simp add: abstract_forest_def)
    thus ?case
      by(unfold Vs_contracted[symmetric]) auto
  qed
  have p1_no_roots:"set p1 ∩ vset_to_set rts = {}" 
  proof(rule ccontr, goal_cases)
    case 1
    then obtain x where x: "x ∈ set p1" "x ∈  vset_to_set rts"
      by auto
    then obtain p1a p1b where "p1=p1a@[x]@p1b" 
      using split_list_first[of x p1] by auto
    then obtain y where "parent_lookup prnts x = Some y" 
      using assms(2) follow_subsequent_parent[of v p1a x _ _ ]
      by(cases p1b) auto
    then show ?case
      using x(2) invar_basic_F(13) by auto
  qed
  have u_roots_p2_Nil:"u ∈ vset_to_set rts ⟷ p2 = Nil"
    using invar_basic_F(13,6)[symmetric] follow_simps[of u] assms(2,4) 
          invar_rootsD_here(2)[of u] p1_no_roots follow_None[of u] follow_append
      by auto+
  have parents_ev_od: "x ∈ vset_to_set evs ⟷ y ∈ vset_to_set ods"
    "x ∈ vset_to_set ods ⟷ y ∈ vset_to_set evs"
    if "parent_lookup prnts x = Some y" for x y
    using invar_forest_even_and_oddD[OF forest_invar_F(3), of x y]
      invar_forest_even_and_oddD[OF forest_invar_F(3), of y x] that
    by(auto simp add: abstract_forest_def)
  have hd_p1: "hd (p1@[u]) = v"
    using hd_append[of p1 "[u]"] 
      parents_here.follow_hd[of v] assms(2) follow_def[of "parent_lookup prnts"]
    by auto
  have rev_alt_path_M: "rev_alt_path ℳ (p1 @ [u])"
    using follow_alt_here(1) edges_of_path_append_2[of "u # p2" p1] alt_list_append_1 
    by auto
  have M_quot: 
    "quot_graph contr ℳ - {{new_vert}} 
     = ℳ - ((if u ∈ vset_to_set rts then {} 
              else {{u, the (parent_lookup prnts u)}}) ∪ set (edges_of_path (p1@[u]))) ∪ 
                     (if u ∈ vset_to_set rts then {} 
                      else {{new_vert, the (parent_lookup prnts u)}})"
  proof(rule, all ‹rule›, goal_cases)
    case (1 e)
    then obtain x y where xy: "e = contr ` {x, y}" "{x, y} ∈ ℳ" "x ≠ y"
      using assms(7) by(force simp add: quot_graph_def) 
    hence  x_or_y_not_contracted:"x ∉ set (p1@[u]) ∨ y ∉ set (p1@[u])"
      using 1 by(auto simp add: contr_def)
    hence xy_not_in_edges:"{x, y} ∉ set (edges_of_path (p1 @ [u]))"
      by (simp add: edge_not_in_edges_in_path)
    show ?case 
    proof(cases  "x ∉ set (p1@[u]) ∧ y ∉ set (p1@[u])")
      case True
      hence "e ∈ ℳ" "e = {x, y}"
        using  xy by (auto simp add: contr_def)
      then show ?thesis
        using  xy_not_in_edges True 
        by(auto simp add: doubleton_eq_iff)
    next
      case False
      then obtain x' y' where xy: "e = contr ` {x', y'}" "{x', y'} ∈ ℳ" "x' ≠ y'"
        "x' ∈ set (p1@[u])" "y' ∉ set (p1@[u])" "{x, y} = {x', y'}"
        using xy(1,2) x_or_y_not_contracted doubleton_eq_iff[of x y y x] by fastforce
      have x'_is_u:"x' = u"
      proof(rule ccontr, goal_cases)
        case 1
        then obtain p1a p2a where p1ap2a:"p1 = p1a@[x']@p2a" 
          using xy(4) in_set_conv_decomp_last[of x' p1]
          by auto
        then obtain xp where xp: "parent_lookup prnts x' = Some xp"
          using assms(2) by(cases p2a) (auto simp add: follow_subsequent_parent)
        have x_not_odd:"x' ∈ vset_to_set ods ⟹ False"
        proof(goal_cases)
          case 1
          then obtain xc p1aa where xc: " p1a = p1aa@[xc]" 
            using hd_p1 p1ap2a assms(3) invar_basic_F(7)
            by(cases p1a rule: rev_cases) auto
          hence xc_child_x:"parent_lookup prnts xc = Some x'" 
            using assms(2) p1ap2a 
            by (simp add: follow_def parents_here.follow_subsequent_parent)
          hence "xc ∈ vset_to_set evs"
            using assms(1,5) "1"
                  odds_unique_child[of ℳ "Forest rts evs ods prnts orngs" x'] 
            by auto
          hence "{x', xc} ∈ ℳ" 
            using  xc_child_x 
              invar_even_to_parent_matchingD[OF forest_invar_F(5)] 
            by (auto simp add: edge_commute)
          hence "xc = y'" 
            using assms(5) doubleton_in_matching(1) xy(2) by fastforce
          then show ?case 
            using p1ap2a xc xy(5) by auto
        qed
        hence x'_even:"x' ∈ vset_to_set evs"
          using xp  invar_basic_F(14) invar_basic_F(6)[symmetric] by auto
        hence "xp ∈ vset_to_set ods" 
          by (simp add: parents_ev_od(1) xp)
        then obtain p2aa where "p2a = xp#p2aa"
          using p1ap2a xp assms(2,4) x_not_odd assms(4)follow_subsequent_parent parents_ev_od(2)
          by (cases p2a) auto
        have "{x', xp} ∈ ℳ"
          by (rule invar_even_to_parent_matchingD_here[OF x'_even xp])
        hence "xp = y'" 
          using assms(5) xy(2) by(auto intro!: doubleton_in_matching(1))
        thus False
          using ‹p2a = xp # p2aa› p1ap2a xy(5) by auto
      qed
      have u_no_root: "u ∉ vset_to_set rts"
        using edges_are_Vs[OF xy(2), unfolded x'_is_u] invar_basic_F(11)
        by auto
      have parent_x'_is:"parent_lookup prnts x' = Some y'"
      proof(cases "parent_lookup prnts x'")
        case None
        then show ?thesis 
          using u_no_root x'_is_u assms(4) domIff[of u "origin_lookup orngs"] invar_basic_F(13,15,6)
             imageI[of u "vset_to_set evs ∪ vset_to_set ods" "origin_lookup orngs"]
          by auto
      next
        case (Some a)
        hence "a ∈ vset_to_set ods" 
          using assms(4) parents_ev_od(1) x'_is_u by blast
        then show ?thesis 
          using assms(4,5) x'_is_u xy(2) Some invar_even_to_parent_matchingD_here[of u a]
          by (auto dest!: doubleton_in_matching(1)[of ℳ u y' a])
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
      then obtain x y where xy: "e = {x, y}" "x ≠ y"
        using assms(7) by auto
      have e_in_M: "e ∈ ℳ"
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
        hence "{u', v'} ∈ set (edges_of_path (p1@[u]))"
          using edges_of_path_length[of "p1 @ [u]"] 
                in_set_conv_nth[of "edges_of_path (p1 @ [u]) ! i" ]
          by auto
        with one show ?case
          by (auto simp: "3"(6) split: if_splits)
      next
        case (4 u' v')
        hence "v' = the (parent_lookup prnts u)" 
          using assms(4,5)  e_in_M invar_basic_F(11,13,6)[symmetric] edges_are_Vs[of u v' ℳ]
                domIff[of u "origin_lookup orngs"] domIff[of u "parent_lookup prnts"]
                invar_basicD_here(15) invar_even_to_parent_matchingD_here[of u ]
          by (auto dest!: doubleton_in_matching(1)[of ℳ u "the (parent_lookup prnts u)" v'])
        then show ?case
          using one 4 invar_basic_F(11) edges_are_Vs[of u v' ℳ]
          by(cases "u ∈ vset_to_set rts")(auto simp add: quot_graph_def)
      next
        case 5
        then show ?case
          using xy(2) e_in_M
          by(auto intro!: bexI[of _ e] simp add: xy(1) quot_graph_def contr_def )
      qed
    next
      case 2
      hence  e_is: "e = {new_vert, the (parent_lookup prnts u)}" "u ∉ vset_to_set rts"
        by(all ‹cases "u ∈ vset_to_set rts"›) auto
      moreover hence u_pu_M:"{u, the (parent_lookup prnts u)} ∈ℳ" 
        using assms(4) invar_basic_F(13,6)[symmetric] domIff[of u "parent_lookup prnts"]
              invar_basicD_here(15) invar_even_to_parent_matchingD_here[of u]
              imageI[of u "vset_to_set evs ∪ vset_to_set ods" "origin_lookup orngs"]
        by auto 
      moreover obtain pu where parent_u: "parent_lookup prnts u = Some pu"
      proof -
        have "∃r. origin_lookup orngs u = Some r"
          using origin_defined by simp
        hence "u ∈ dom (origin_lookup orngs)"
          by auto
        with invar_basic_F(13) e_is(2) show thesis
          by (auto intro: that)
      qed
      moreover have "new_vert ≠ pu"
        using parent_u_not_new parent_u by auto
      moreover have "pu ∉ set (p1 @ [u])"
        using follow_subsequent_parent_there[OF assms(2) parent_u] follow_distinct[of v]
        by (auto simp: assms(2))
      ultimately show ?case
        by (auto intro!: bexI[of _ "{u, pu}"] simp: quot_graph_def contr_def)
    qed
  qed
  have distinct_path:"distinct (p1@[u]@p2)"
    using follow_distinct[of v] by (simp only: assms(2))
  have alt_ev_od_p: "alt_list (λx. x ∈ vset_to_set evs) (λx. x ∈ vset_to_set ods) (p1 @ [u])"
    using alt_list_append_1[of _ _ "p1@[u]"] append.assoc follow_alt_here(2) by simp
  have odd_length_p:"odd (length (p1@[u]))" 
    using assms(4) invar_basic_F(7) alt_ev_od_p alt_list_or 
    by (intro last_odd_P1'[OF alt_ev_od_p]) fastforce+
  have org_lookup_last:"the (origin_lookup orngs u) = u ⟷  u ∈ vset_to_set rts"
  proof -
    have "origin_lookup orngs u ∈ Some ` vset_to_set rts"
      using imageI[OF UnI1[OF assms(4), of "vset_to_set ods"], of "origin_lookup orngs"]
      by (simp only: invar_basic_F(6,15))
    then obtain r where "origin_lookup orngs u = Some r" "r ∈ vset_to_set rts"
      by auto
    then show ?thesis
      using invar_rootsD_here(1)[of u] by auto
  qed
  have lookup_u_not_none_roots: "parent_lookup prnts u = None ⟷ u ∈ vset_to_set rts"
    using arg_cong[OF invar_basic_F(13), of "λA. u ∈ A"] origin_defined
    by (simp only: domIff Diff_iff last_snoc; blast)
  have Diff_Int_idem: "A - (A ∩ B) = A - B" "A - (B ∩ A) = A - B" for A B
    by blast+
  have Union_of_same_diff: "(A - B) ∪ (C - B) = (A ∪ C) - B" for A B C
    by blast

  note origin_new_def = effect_of_contract_path(10)
    [simplified  evens_in_p_are odds_in_p_are Diff_Int_idem Union_of_same_diff
      set_eq_iff Diff_iff mem_Collect_eq last_snoc]

  have dom_samer: "dom (parent_lookup (parents new_forest)) =
    dom (origin_lookup (origins new_forest)) - vset_to_set (roots new_forest)"
  proof(rule set_eqI)
    fix x
    have odd_parent: "x ∈ vset_to_set ods ⟹ parent_lookup prnts x ≠ None"
      using forest_invar_F(7)
      by (auto simp only: invar_odd_to_parent_non_matching_def alt_forest.sel)
    have seen_origin: "x ∈ vset_to_set evs ∪ vset_to_set ods ⟹ origin_lookup orngs x ≠ None"
      using invar_rootsD_here(2)[of x] invar_basic_F(6) by blast
    have fresh_parent: "x = new_vert ⟹ x ∉ set (p1 @ [u]) ⟹ parent_lookup prnts x = None"
      using assms(6) invar_basic_F(14,6)
      by (cases "parent_lookup prnts x") auto
    have parent_domain: "parent_lookup (parents new_forest) x ≠ None ⟷
        (if x = new_vert then parent_lookup prnts u ≠ None
         else x ∉ set (p1 @ [u]) ∧ parent_lookup prnts x ≠ None)"
      using odd_parent fresh_parent assms(6)
      by (cases "x = new_vert"; cases "x ∈ set (p1 @ [u])")
         (auto simp: new_parents_are)
    have origin_domain: "origin_lookup (origins new_forest) x ≠ None ⟷
        x = new_vert ∨ (x ∉ set (p1 @ [u]) ∧ origin_lookup orngs x ≠ None)"
      using seen_origin
      unfolding effect_of_contract_path(10) evens_in_p_are odds_in_p_are
      by (cases "x = new_vert"; cases "x ∈ set (p1 @ [u])";
          cases "the (origin_lookup orngs u) = u") auto
    have old_domains: "parent_lookup prnts x ≠ None ⟷
        origin_lookup orngs x ≠ None ∧ x ∉ vset_to_set rts"
      using arg_cong[OF invar_basic_F(13), of "λA. x ∈ A"]
      by (simp only: domIff Diff_iff)
    have lookup_dom: "a ∈ dom f ⟷ f a ≠ None" for a f
      by (rule domIff)
    show "x ∈ dom (parent_lookup (parents new_forest)) ⟷ x ∈ dom (origin_lookup (origins new_forest)) - vset_to_set (roots new_forest)"
      using assms(6) invar_basic_F(10) p1_no_roots
      unfolding Diff_iff lookup_dom parent_domain origin_domain old_domains effect_of_contract_path(6)
        lookup_u_not_none_roots
      by (cases "x = new_vert"; cases "u ∈ vset_to_set rts") auto
  qed

  have Vs_evens_odds_roots_helper:
    " vset_to_set (evens new_forest) ∪ vset_to_set (odds new_forest) =
    vset_to_set (roots new_forest) ∪ Vs (abstract_forest new_forest)"
  proof(cases "last (p1 @ [u]) ∈ vset_to_set rts")
    case True
    have helper:"⟦x ∈ set p1; x ∈ vset_to_set rts⟧ ⟹ x = u" for x
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

  have old_origin_in_roots:
    "origin_lookup orngs x ∈ Some ` vset_to_set rts"
    if "x ∈ vset_to_set evs ∪ vset_to_set ods" for x
    using imageI[OF that, of "origin_lookup orngs"]
    by (simp only: invar_basic_F(6,15))
  have origin_at_new: "origin_lookup (origins new_forest) new_vert =
    Some (if u ∈ vset_to_set rts then new_vert else the (origin_lookup orngs u))"
    by (simp add: effect_of_contract_path(10) org_lookup_last)
  have origin_outside:
    "origin_lookup (origins new_forest) x =
      (if u ∈ vset_to_set rts ∧ the (origin_lookup orngs x) = u
       then Some new_vert else origin_lookup orngs x)"
    if "x ∈ vset_to_set evs ∪ vset_to_set ods"
       "x ∉ set (p1 @ [u])" "x ≠ new_vert" for x
    using that org_lookup_last
    unfolding effect_of_contract_path(10) evens_in_p_are odds_in_p_are
    by (cases "u ∈ vset_to_set rts") auto
  have roots_new_seen:
    "vset_to_set (roots new_forest) ⊆
      vset_to_set (evens new_forest) ∪ vset_to_set (odds new_forest)"
    using invar_basic_F(10) p1_no_roots
    unfolding effect_of_contract_path(6-8) evens_in_p_are odds_in_p_are
    by auto
  have roots_new_origin: "origin_lookup (origins new_forest) r = Some r"
    if "r ∈ vset_to_set (roots new_forest)" for r
  proof (cases "r = new_vert")
    case True
    with that assms(6) invar_basic_F(10) p1_no_roots show ?thesis
      by (auto simp: effect_of_contract_path(6) origin_at_new)
  next
    case False
    with that have root: "r ∈ vset_to_set rts" and not_u: "r ≠ u"
      by (auto simp: effect_of_contract_path(6) split: if_splits)
    have seen: "r ∈ vset_to_set evs ∪ vset_to_set ods"
      using root invar_basic_F(10) by blast
    have outside: "r ∉ set (p1 @ [u])"
      using root not_u p1_no_roots by auto
    show ?thesis
      using not_u
      by (simp add: origin_outside[OF seen outside False] invar_rootsD_here(1)[OF root])
  qed
  have origins_new_in_roots:
    "origin_lookup (origins new_forest) x ∈ Some ` vset_to_set (roots new_forest)"
    if "x ∈ vset_to_set (evens new_forest) ∪ vset_to_set (odds new_forest)" for x
  proof (cases "x = new_vert")
    case True
    then show ?thesis
      using old_origin_in_roots[OF UnI1[OF assms(4)]]
      by (auto simp: origin_at_new effect_of_contract_path(6))
  next
    case False
    with that have seen: "x ∈ vset_to_set evs ∪ vset_to_set ods"
      and outside: "x ∉ set (p1 @ [u])"
      unfolding effect_of_contract_path(7,8) evens_in_p_are odds_in_p_are
      by auto
    show ?thesis
      using old_origin_in_roots[OF seen]
      by (auto simp: origin_outside[OF seen outside False] effect_of_contract_path(6))
  qed
  have org_lookup_helper:
    "origin_lookup (origins new_forest) `
      (vset_to_set (roots new_forest) ∪ Vs (abstract_forest new_forest)) =
      Some ` vset_to_set (roots new_forest)"
    unfolding Vs_evens_odds_roots_helper[symmetric]
  proof (rule equalityI)
    show "origin_lookup (origins new_forest) `
        (vset_to_set (evens new_forest) ∪ vset_to_set (odds new_forest)) ⊆
        Some ` vset_to_set (roots new_forest)"
      by (rule image_subsetI, rule origins_new_in_roots, assumption)
    show "Some ` vset_to_set (roots new_forest) ⊆
        origin_lookup (origins new_forest) `
        (vset_to_set (evens new_forest) ∪ vset_to_set (odds new_forest))"
    proof (rule image_subsetI)
      fix r
      assume root: "r ∈ vset_to_set (roots new_forest)"
      have "r ∈ vset_to_set (evens new_forest) ∪ vset_to_set (odds new_forest)"
        by (rule subsetD[OF roots_new_seen root])
      then have "origin_lookup (origins new_forest) r ∈
          origin_lookup (origins new_forest) `
          (vset_to_set (evens new_forest) ∪ vset_to_set (odds new_forest))"
        by (rule imageI)
      then show "Some r ∈ origin_lookup (origins new_forest) `
          (vset_to_set (evens new_forest) ∪ vset_to_set (odds new_forest))"
        by (simp only: roots_new_origin[OF root])
    qed
  qed

  show new_evs_are: "vset_to_set (evens new_forest) = vset_to_set evs - set (p1@[u])∪ {new_vert} "
    using effect_of_contract_path(8) evens_in_p_are by auto
  show new_ods_are: "vset_to_set (odds new_forest) = vset_to_set ods - set (p1@[u])"
    using effect_of_contract_path(7) odds_in_p_are by auto
  have invar_even_to_parent_matching_after: 
    "invar_even_to_parent_matching (quot_graph contr ℳ - {{new_vert}}) new_forest"
  proof(rule invar_even_to_parent_matchingI, goal_cases)
    case (1 u' v')
    then show ?case 
      unfolding new_evs_are
    proof(elim UnE, goal_cases)
      case 1
      hence not_P:"¬ (u' = new_vert ∧ parent_lookup prnts u ≠ None)" 
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
      proof(cases "u' ∈ set (p1 @ [u])", goal_cases)
        case 2
        note 2 = 2[simplified if_not_P[OF 2(3)]]
        moreover have e_in_M: "{u', v'} ∈ ℳ"
          using calculation(1,2) invar_even_to_parent_matchingD_here by auto
        moreover have "{u', v'} =  contr `{u', v'}"
        proof(rule matching_edge_rev_alt_path_cases[OF 
              rev_alt_path_M e_in_M assms(7) assms(5)], goal_cases)
          case (1 u'' v'' i)
          have "{u', v'} ∈ set (edges_of_path (p1 @ [u]))"
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
        moreover hence "{u', v'} ≠ {new_vert}"
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
        hence cond_not: "¬ (u' = new_vert ∧ parent_lookup prnts u ≠ None)" by auto
        from 1 show ?case 
          unfolding if_not_P[OF cond_not]
        proof(cases "u' ∉ set (p1 @ [u]) ∧
                     the (parent_lookup prnts u') ∈ set (p1 @ [u]) ∩ vset_to_set evs ∧
                     u' ∈ vset_to_set ods - set (p1 @ [u])", goal_cases)
          case 1
          note 1 = 1[simplified if_P[OF 1(4)]]
          then show ?case 
            using assms(6) by force
        next
          case 2
          note 2 = 2[simplified if_not_P[OF 2(4)]]
          hence u'_not_in_p:"u' ∉ set (p1 @ [u])" by force
          note 2 = 2[simplified if_not_P[OF u'_not_in_p]] u'_not_in_p
          moreover hence "new_vert ∈ Vs (abstract_forest (Forest rts evs ods prnts orngs))"
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
          hence "v' ∈ vset_to_set ods"
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
    moreover hence "v' ∈ vset_to_set evs" 
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
      hence u'v'_in_M:"{u', v'} ∈ ℳ"
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
    "vset_to_set (roots new_forest) ∩ Vs (quot_graph contr ℳ - {{new_vert}}) = {}"
    unfolding effect_of_contract_path(7,8) 
      evens_in_p_are odds_in_p_are effect_of_contract_path(6)
  proof(goal_cases)
    case 1
    have sg1: 
      "⟦u ∈ vset_to_set rts; new_vert ∈ Vs (quot_graph contr ℳ - {{new_vert}})⟧ ⟹ False"
      proof(goal_cases)
      case 1 
      note one = this
      then obtain e where e: "e ∈ ℳ - set (edges_of_path (p1 @ [u]))" "new_vert ∈ e" 
        "⋀ e'. ⟦e' ∈ ℳ - set (edges_of_path (p1 @ [u])); new_vert ∈ e'⟧ ⟹ e = e'"
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
        hence "u' ∉ vset_to_set rts" "v' ∉ vset_to_set rts"
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
     "⟦u ∈ vset_to_set rts;x ∈ Vs (quot_graph contr ℳ - {{new_vert}});
       x ∈ vset_to_set rts⟧ ⟹ x = u" for x
    using invar_basic_F(11) subsetD[OF Vs_subset[of "ℳ - _" ℳ, simplified]]
    by (auto simp add: M_quot)
  have sg3: "⟦u ∉ vset_to_set rts;x ∈ vset_to_set rts;
       x ∈ Vs (quot_graph contr ℳ - {{new_vert}})⟧ ⟹ False" for x
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
      hence "{u, the (parent_lookup prnts u)} ∈ ℳ"
        by (simp add: assms(4) invar_even_to_parent_matchingD_here lookup_u_not_none_roots)
      then show ?case
        using assms(6) "2"(2,3,4) invar_basic_F(10,11) p1_no_roots
          vs_member_intro[of new_vert "{new_vert, the (parent_lookup prnts u)}" ℳ]
          vs_member_intro[of x "{u, the (parent_lookup prnts u)}" ℳ]
        by auto
    qed
  qed  
    show ?case
      by (auto intro: sg1 sg2 sg3)
  qed

  have unmatched_forest_Vs_are_roots:
    "Vs (abstract_forest new_forest) - Vs (quot_graph contr ℳ - {{new_vert}})
    ⊆ vset_to_set (roots new_forest)"
  proof(rule , rule ccontr, goal_cases)
    case (1 x)
    then obtain y where y: "parent_lookup (parents new_forest) x = Some y"
      using dom_samer org_lookup_helper
           imageI[of x "vset_to_set (roots new_forest) ∪ Vs (abstract_forest new_forest)"
          "origin_lookup (origins new_forest)"] 
      by(cases "parent_lookup (parents new_forest) x") auto
    then show ?case 
    proof(cases "x ∈ vset_to_set (evens new_forest)")
      case True
      then show ?thesis 
        using invar_even_to_parent_matching_after y 1(1)
        by(auto dest!: invar_even_to_parent_matchingD)
    next
      case False
      hence x_odd: "x ∈ vset_to_set (odds new_forest)"
        using "1"(1) Vs_evens_odds_roots_helper by auto
      then obtain y where y: "parent_lookup (parents new_forest) y = Some x"
        using invar_odd_is_parent_after
        by(auto dest!: invar_odd_is_parentD) 
      hence y_even:  "y ∈ vset_to_set (evens new_forest)"
        using assms(6)  new_ods_are parents_ev_od(1) x_odd 
        by(auto simp add: new_evs_are new_parents_are if_split[of "λ x. x = Some _"])
      hence "{x, y} ∈ quot_graph contr ℳ - {{new_vert}}"
        using invar_even_to_parent_matching_after y
        by(auto dest!: invar_even_to_parent_matchingD simp add: insert_commute)
      then show ?thesis
        using 1(1) by(auto dest: edges_are_Vs)
    qed
  qed

  have invar_basic_after: "invar_basic (quot_graph contr ℳ - {{new_vert}}) new_forest"
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
    have c1: "card (vset_to_set ods - vset_to_set ods ∩ set (p1 @ [u])) = 
         card (vset_to_set ods) - card (vset_to_set ods ∩ set (p1 @ [u]))"
      by (simp add: card_Diff_subset)
    have le1: "card (vset_to_set ods) ≥ card (vset_to_set ods ∩ set (p1 @ [u]))"
      by (simp add: card_mono invar_basic_F(9))
    have c3: "card (vset_to_set evs - vset_to_set evs ∩ set (p1 @ [u]) ∪ {new_vert}) = 
             1 + card (vset_to_set evs) - card (vset_to_set evs ∩ set (p1 @ [u]))" 
      using assms(6)
      by (subst card_Un_disjoint[of _ "{new_vert}"])
         (auto simp add: card_Diff_subset Suc_diff_le card_mono invar_basic_F(8))
    have le2: "card (vset_to_set evs) ≥ card (vset_to_set evs ∩ set (p1 @ [u]))"
      by (simp add: card_mono invar_basic_F(8))
    have c4: "card (vset_to_set evs ∩ set (p1 @ [u])) = 1+ card (vset_to_set ods ∩ set (p1 @ [u]))"
      unfolding evens_in_p_are[symmetric] odds_in_p_are[symmetric]
    proof(goal_cases)
      case 1
      have " card {(p1 @ [u]) ! i |i. i < length (p1 @ [u]) ∧ even i} = 
             card { i |i. i < length (p1 @ [u]) ∧ even i}"
       using distinct_path
       by(subst card_image[of "λ i. (p1 @ [u]) ! i", symmetric])
         (auto simp add: inj_on_def nth_eq_iff_index_eq intro!: arg_cong[of _ _ card])
      moreover have "card { i |i. i < length (p1 @ [u]) ∧ even i} =
                 card { i |i. i < length (p1 @ [u]) ∧ odd i} + 1"
        unfolding card_of_odd_numbers_upto card_of_even_numbers_upto
        using odd_length_p by auto
      moreover have " card {(p1 @ [u]) ! i |i. i < length (p1 @ [u]) ∧ odd i} = 
             card { i |i. i < length (p1 @ [u]) ∧ odd i}"
        using distinct_path
        by(subst card_image[of "λ i. (p1 @ [u]) ! i", symmetric])
          (auto simp add: inj_on_def nth_eq_iff_index_eq intro!: arg_cong[of _ _ card])
      ultimately show ?case by simp
    qed
    show ?case 
      unfolding effect_of_contract_path(7,8) 
        evens_in_p_are odds_in_p_are effect_of_contract_path(6)
        c1 c3 c4
    proof (cases "last (p1 @ [u]) ∈ vset_to_set rts", goal_cases)
      case 1
      have c2: "card (vset_to_set rts - {last (p1 @ [u])} ∪ {new_vert}) = 
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
                        "Vs (abstract_forest new_forest) ∪ {new_vert}",
                        simplified Vs_contracted])
  next
    case 13
    show ?case
      using Vs_subset[of "quot_graph contr ℳ - {{new_vert}}" "quot_graph contr ℳ"]
        invar_basic_F(18) new_vert_in_universe
      by (auto simp: Vs_quot_graph_is_img contr_def)
  qed

  have invar_matching_both_or_none_after:
    "invar_matching_both_or_none (quot_graph contr ℳ - {{new_vert}}) new_forest"
  proof(rule invar_matching_both_or_noneI, goal_cases)
    case (1 u' v')
    then show ?case 
      unfolding M_quot
    proof(cases "u ∈ vset_to_set rts", goal_cases)
      case 1
      hence one: "{u', v'} ∈ ℳ" "{u', v'} ∉ set (edges_of_path (p1 @ [u]))"
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
        hence u'_v'_not_in_p:"u' ∉ set (p1@[u])" "v' ∉ set (p1@[u])"
          by auto
        hence eq1: "contr u' = u'" "contr v' = v'" 
          by(auto simp add: contr_def)
        moreover have e2: "contr u'' = u' ⟹ u'' = u'" for u''
          using "3" assms(6) one(1) by(cases " u'' ∈ set (p1 @ [u])") (auto simp add: contr_def)
        moreover have eq3: "contr v'' = v' ⟹ v'' = v'" for v''
            using "3" assms(6) one(1) by(cases " v'' ∈ set (p1 @ [u])") (auto simp add: contr_def)
        ultimately have "e = {u', v'}"
          if "e ∈ abstract_forest (Forest rts evs ods prnts orngs)"
            "contr ` e = {u', v'}" for e
          using that (2) 
          by auto (force intro: imageE[of u' contr e "u' ∈ e"] imageE[of v' contr e "v' ∈ e"])+
        hence AF_equiv:"{u', v'} ∈ abstract_forest new_forest ⟷ 
                 {u', v'} ∈ abstract_forest (Forest rts evs ods prnts orngs)"
          using "1"(1)[simplified M_quot[symmetric]]
          by (auto intro!: bexI[of _ "{u', v'}"] 
                 simp add: eq1 quot_graph_def quot_is_AF[symmetric])
        have disjoint_AF_equiv:
          "{u', v'} ∩ (Vs (abstract_forest new_forest) ∪ vset_to_set (roots new_forest)) = {}
               ⟷ 
           {u', v'} ∩ (Vs (abstract_forest (Forest rts evs ods prnts orngs)) 
                     ∪ vset_to_set rts) = {}"
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
        hence "{u', v'} ∈ abstract_forest new_forest"
          using True quot_is_AF[symmetric] 1 up 
          by(auto intro!:  bexI[of _ "{u, up}"] simp add: quot_graph_def abstract_forest_def)
        then show ?thesis by simp
      next
        case False
        hence two: "{u', v'} ∈ ℳ" "{u', v'} ∉ set (edges_of_path (p1 @ [u]))"
          "u ∉ vset_to_set rts"  
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
          hence u'_v'_not_in_p:"u' ∉ set (p1@[u])" "v' ∉ set (p1@[u])"
            by auto
          hence eq1: "contr u' = u'" "contr v' = v'" 
            by(auto simp add: contr_def)
          moreover have e2: "contr u'' = u' ⟹ u'' = u'" for u''
            using "3" assms(6) two(1) 
            by(cases " u'' ∈ set (p1 @ [u])") (auto simp add: contr_def)
          moreover have eq3: "contr v'' = v' ⟹ v'' = v'" for v''
            using "3" assms(6) two(1) 
            by(cases " v'' ∈ set (p1 @ [u])") (auto simp add: contr_def)
          ultimately have "e = {u', v'}"
            if "e ∈ abstract_forest (Forest rts evs ods prnts orngs)"
              "contr ` e = {u', v'}" for e
            using that (2) 
            by auto (force intro: imageE[of u' contr e "u' ∈ e"] imageE[of v' contr e "v' ∈ e"])+
          hence AF_equiv:"{u', v'} ∈ abstract_forest new_forest ⟷ 
                 {u', v'} ∈ abstract_forest (Forest rts evs ods prnts orngs)"
            using "1"(1)[simplified M_quot[symmetric]]
            by (auto intro!: bexI[of _ "{u', v'}"] 
                   simp add: eq1 quot_graph_def quot_is_AF[symmetric])   
          have disjoint_AF_equiv:
            "{u', v'} ∩ (Vs (abstract_forest new_forest) ∪ vset_to_set (roots new_forest)) = {}
               ⟷ 
               {u', v'} ∩ (Vs (abstract_forest (Forest rts evs ods prnts orngs)) 
                     ∪ vset_to_set rts) = {}"
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
    then obtain e where e: "e∈abstract_forest (Forest rts evs ods prnts orngs)"
      "{u', v'} = contr ` e" "contr ` e ≠ {new_vert}"
      by(unfold quot_is_AF[symmetric] quot_graph_def) blast
    moreover then obtain u'' v'' where u''_v'': "e = {u'', v''}" "u'' ≠ v''"
      using abstract_forest_dblton_graph assms(1) by force
    ultimately obtain u'' v'' where "u' = contr u''" "v' = contr v''"
      "u'' ≠ new_vert ∨ v'' ≠ new_vert" "{u'', v''} = e"
      by (auto simp add: doubleton_eq_iff)
    hence u''_v'':  "u' = contr u''" "v' = contr v''"
      "u'' ≠ new_vert ∨ v'' ≠ new_vert" 
      "{u'', v''} ∈ abstract_forest (Forest rts evs ods prnts orngs)"
      using u''_v'' e by auto
    moreover then have u''_v''_even_odd: "(u'' ∈ vset_to_set evs) = (v'' ∈ vset_to_set ods)"
      using forest_invar_F(3)
      by(auto dest!: invar_forest_even_and_oddD)
    have u''_v''_parent:"parent_lookup prnts u'' = Some v'' ∨ parent_lookup prnts v'' = Some u''"
      using u''_v''(4) by(auto simp add: abstract_forest_def doubleton_eq_iff)
    have alternative_case: "?case ⟷
          (u' ∈ vset_to_set (odds new_forest)) = (v' ∈ vset_to_set (evens new_forest))"
      using "1"  Vs_evens_odds_roots_helper invar_basicD[OF invar_basic_after] edges_are_Vs_2[of v' u']
      by (auto dest: edges_are_Vs_2[of u' v']  simp add: insert_commute)
    have alternative_u''_v''_even_odd:
      "(v'' ∈ vset_to_set evs) = (u'' ∈ vset_to_set ods)"
      using parents_ev_od(1,2) u''_v''_parent by presburger
    have ?case if asm: "u'' ∉ set (p1@[u])" "v'' ∉ set (p1@[u])"
    proof-
      have "u' = u''" "v' = v''"
        using asm by(auto simp add: u''_v'' contr_def)
      thus ?case
        using  u''_v''_even_odd asm u''_v''(3) assms(6) invar_basic_F(6) u''_v''(4)
        by (auto simp add: new_evs_are new_ods_are dest: edges_are_Vs)
    qed
    moreover have ?case if asm: "u'' ∈ set (p1@[u])" "v'' ∉ set (p1@[u])"
    proof-
      have "u' = new_vert" "v' = v''"
        using asm by(auto simp add: u''_v'' contr_def)
      moreover have 
         "⟦v'' ≠ u; parent_lookup prnts u'' = Some v''; p1 = ys @ u'' # zs;
           v'' ∉ set zs⟧ ⟹ v'' ∈ vset_to_set ods" for ys zs
       using assms(2) follow_subsequent_parent_there[of v _ u'' "_@[u]@p2" v'']
             hd_append[of "[]" "u # p2"] hd_append[of zs "u # p2"]  by fastforce
     ultimately show ?case  
        using asm assms(4) u''_v''_even_odd  parent_adj_pu_helper[of v'' u'' ] u''_v''_parent
        by(auto simp add: in_set_conv_decomp[of u''] new_evs_are new_ods_are )+
    qed
    moreover have ?case if asm: "u'' ∉ set (p1@[u])" "v'' ∈ set (p1@[u])"
      unfolding alternative_case
    proof(goal_cases)
      case 1
      have "v' = new_vert" "u' = u''"
        using asm by(auto simp add: u''_v'' contr_def)
      moreover hence "u' ≠ new_vert" 
        using e(2,3) by force
      moreover have 
        "⟦u'' ≠ u;parent_lookup prnts v'' = Some u'';p1 = ys @ v'' # zs;
          u'' ∉ set zs⟧ ⟹ u'' ∈ vset_to_set ods" for ys zs
        using assms(2) follow_subsequent_parent_there[of v ys v'' "zs@[u]@p2" u'']
              hd_append[of zs "u # p2"] 
        by auto
      ultimately show ?case  
        using asm assms(4) alternative_u''_v''_even_odd parent_adj_pu_helper[of u'' v'' _ _ ] u''_v''_parent
        by(auto simp add: in_set_conv_decomp[of v''] new_evs_are new_ods_are)+
    qed
    moreover have False if asm: "u'' ∈ set (p1@[u])" "v'' ∈ set (p1@[u])"
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
   "∃ pu ppu. parent_lookup prnts u = Some pu ∧ parent_lookup prnts pu = Some ppu
        ∧ pu ∉ set (p1@[u]) ∧ ppu ∉ set (p1@[u])"
    if "u ∉ vset_to_set rts"
  proof-
    obtain pu where pu:"parent_lookup prnts u = Some pu"
      using ‹u ∉ vset_to_set rts› lookup_u_not_none_roots by auto
    have "pu ∈ vset_to_set ods"
      using assms(4) parents_ev_od(1) pu by blast
    then obtain ppu where ppu: "parent_lookup prnts pu = Some ppu"
      using forest_invar_F(7)
      by (auto elim!: invar_odd_to_parent_non_matchingE)
    moreover have "pu ∉ set (p1@[u])"
    proof(rule ccontr, unfold not_not, unfold in_set_conv_decomp, goal_cases)
      case 1
      then obtain ys zs where "p1 @ [u] = ys @ pu # zs" by auto
      thus False
        using  assms(2) pu
        by(cases zs rule: rev_cases)
          (auto intro: prnts_no_loop follow_not_again_parent[of v _ pu _ u p2])
    qed 
    moreover have "ppu ∉ set (p1@[u])"
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
    "invar_odd_to_parent_non_matching (quot_graph contr ℳ - {{new_vert}}) new_forest"
  proof(rule invar_odd_to_parent_non_matchingI, goal_cases)
    case (1 u')
    note u'_odd = this
    then obtain v' where v': "parent_lookup (parents new_forest) u' = Some v'"
      using assms(6) invar_odd_to_parent_non_matchingE[OF forest_invar_F(7)]
      by(auto simp add: new_ods_are new_parents_are if_split[of "λ x. x = Some _"])
    moreover have "{u', v'} ∉ quot_graph contr ℳ - {{new_vert}}"
    proof(rule ccontr, goal_cases)
      case 1
      hence u'_v'_in_quot:"{u', v'} ∈ quot_graph contr ℳ - {{new_vert}}" by auto
      then show ?case 
        unfolding M_quot
      proof(cases "u ∈ vset_to_set rts", goal_cases)
        case 1
        hence one: "{u', v'} ∈ ℳ" "{u', v'} ∉ set (edges_of_path (p1 @ [u]))"
          "u ∈ vset_to_set rts"
          by auto
        show ?thesis 
        proof(rule matching_edge_rev_alt_path_cases[OF 
              rev_alt_path_M one(1) assms(7) assms(5)], goal_cases)
          case (1 u'' v'' i)
          hence "{u', v'} ∈ set (edges_of_path (p1@[u]))"
            using edges_of_path_length[of "p1 @ [u]"] nth_mem[of i "edges_of_path (p1 @ [u])"]
            by auto
          then show ?case 
            using one(2) by simp
        next
          case (2 u'' v'')
          then show ?case 
            using one(1,3) invar_basic_F(11) edges_are_Vs[of u v'' ℳ]
            by auto
        next
          case 3
          moreover have "¬ (∃y. parent_lookup prnts u = Some y)"
            by (simp add: lookup_u_not_none_roots one(3))
          ultimately have "parent_lookup prnts u' = Some v'"
            using v' assms(6) edges_are_Vs_2  one(1) 
            by(auto simp add: new_parents_are if_split[of "λ x. x = Some _"])
          then show ?case 
            using invar_odd_to_parent_non_matchingD_here new_ods_are one(1) u'_odd 
            by auto
        qed
      next
        case 2
        note 2 = 2[simplified if_not_P[OF 2(2)]]
        have v'_even: "v' ∈ vset_to_set (evens new_forest)" 
          using assms(6) effect_of_contract_path(8) evens_in_p_are 
                parents_ev_od(2) u'_odd v'
          by(auto simp add: new_ods_are new_parents_are if_split[of "λ x. x = Some _"])
        have u'_old_odd:"u' ∈ vset_to_set ods"
          using new_ods_are u'_odd by force
        have u_pu_in_M:"{u, the (parent_lookup prnts u)} ∈ ℳ"
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
          hence "{the (parent_lookup prnts u), u} ∈ ℳ"
            using "2"(2) assms(4) invar_even_to_parent_matchingD_here lookup_u_not_none_roots
            by(auto simp add: insert_commute)
          moreover have "the (parent_lookup prnts u) ∈ vset_to_set ods" 
            using u'_old_odd u'_v'_are(1) by auto
          ultimately show ?thesis
            using "2"(2) assms(6) parent_u' parents_ev_od(2) parents_of_u_props v' by fastforce
        next
          case False
          hence u'_v'_props:
            "{u', v'} ∈ ℳ" "{u', v'} ≠ {u, the (parent_lookup prnts u)}"
            "{u', v'} ∉ set (edges_of_path (p1 @ [u]))"
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
            hence v'_even_old: "v' ∈ vset_to_set evs"
              using assms(6) edges_are_Vs_2 effect_of_contract_path(8) u'_v'_props(1) v'_even
              by fastforce
            moreover hence parent_u':
               "parent_lookup (parents new_forest) u' = parent_lookup prnts u'"
              using 3 assms(6) u'_odd v' 
                by (auto simp add: new_ods_are new_parents_are if_split[of "λ x. x = Some _"])
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
    "new_vert ∉ dVs (Dabstract_forest (Forest rts evs ods prnts orngs)) - set (p1 @ [u])"
    using assms(6) invar_basic_F(6) 
    by(auto simp add: dVs_Vs_Dabstract_abstract_forest)

  have self_gamma_false:
    "u ∈ γ⇧- Dabstract_forest (Forest rts evs ods prnts orngs) u ⟹False"
    "u ∈ γ⇧+ Dabstract_forest (Forest rts evs ods prnts orngs) u ⟹False"for u
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
      hence "¬ follow (parent_lookup prnts) v = [v]"
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
    " (⋀v. (⋀x2. parent_lookup (parents new_forest) v = Some x2 ⟹ P x2) ⟹ P v) ⟹
        P a" for P a
    using parent_spec_i.follow.pinduct parents_new.follow_dom by metis
  note follow_new_simps = parent_spec_i.follow.psimps[OF parents_new.follow_dom]
  note follow_new_last_Cons=parents_new.follow_last_Cons[folded follow_def]
  note new_follow_cong = follow_cong[folded follow_def]

  have lookup_self_implies_root:
    "origin_lookup (origins new_forest) r = Some r" 
    if "r ∈ vset_to_set (roots new_forest)" for r
  proof -
    have "r ≠ last (p1 @ [u]) ∨ r ≠ the (Some r) ∨ the (origin_lookup orngs (last (p1 @ [u]))) ≠ the (Some r) ∨ last (p1 @ [u]) = the (origin_lookup orngs (last (p1 @ [u])))"
      by argo
    thus ?thesis 
      using org_lookup_last that p1_no_roots assms(6) invar_basic_F(10)
      by(auto simp add: effect_of_contract_path(10,6) if_split[of "λ x. x = Some _"]
                        invar_rootsD_here(1))
  qed

  have parent_same_org_old:
    "origin_lookup orngs x = origin_lookup orngs y"
    if asm :"parent_lookup prnts x = Some y" for x y
  proof-
    obtain rest where "follow (parent_lookup prnts) x = x#y#rest"
      using asm follow_cons_3' follow_cons_4 by auto
    moreover have "x ∈ Vs (abstract_forest (Forest rts evs ods prnts orngs))" 
      using invar_basic_F(14) that by auto
    ultimately show ?thesis
      using forest_invar_F(6) by(auto elim!: invar_rootsE)
  qed

  have x_in_p1_org_is_u's_org: "x ∈ set (p1@[u]) ⟹ origin_lookup orngs x = origin_lookup orngs u" for x
    using invar_basicD_here(6) UnI1[of v "vset_to_set evs" "vset_to_set ods"]
          invar_rootsD_here(3)[of v x] invar_rootsD_here(3)[of v u] assms(2,3) 
    by auto

  have parent_same_org_new:
    "origin_lookup (origins new_forest) x = origin_lookup (origins new_forest) y"
    if "parent_lookup (parents new_forest) x = Some y" for x y
  proof-
    note new_edge = that
    have edge_vertices: "a ∈ vset_to_set evs ∪ vset_to_set ods"
      "b ∈ vset_to_set evs ∪ vset_to_set ods"
      if "parent_lookup prnts a = Some b" for a b
      using that invar_basic_F(14,6) parents_ev_od[OF that] by auto
    have origin_u: "origin_lookup orngs u = Some (the (origin_lookup orngs u))"
      using origin_defined by auto
    have new_origin:
      "origin_lookup (origins new_forest) a =
        (if a = new_vert then
           (if u ∈ vset_to_set rts then Some new_vert else origin_lookup orngs u)
         else if a ∈ set (p1 @ [u]) then None
         else if u ∈ vset_to_set rts ∧ a ∈ vset_to_set evs ∪ vset_to_set ods ∧
             the (origin_lookup orngs a) = u then Some new_vert
         else origin_lookup orngs a)" for a
      using origin_u org_lookup_last
      unfolding effect_of_contract_path(10) evens_in_p_are odds_in_p_are
      by auto
    have outside_parent: "a ∈ vset_to_set ods ∧ b ∈ vset_to_set evs"
      if "parent_lookup prnts a = Some b" "a ∉ set (p1 @ [u])" "b ∈ set (p1 @ [u])" for a b
    proof(cases "b = u")
      case True
      then show ?thesis
        using parents_ev_od(2)[OF that(1)] assms(4) by auto
    next
      case False
      then obtain ys zs where split: "p1 = ys @ b # zs"
        using ‹b ∈ set (p1 @ [u])› by (auto simp: in_set_conv_decomp)
      show ?thesis
        using parent_adj_pu_helper[OF that(1) _ split] that(2)
        by (auto simp: split)
    qed
    show ?thesis
      using new_edge
      unfolding new_parents_are
    proof(cases "x = new_vert ∧ parent_lookup prnts u ≠ None")
      case True
      then have old_parent: "parent_lookup prnts u = Some y"
        using new_edge by (simp add: new_parents_are)
      have "y ∉ set (p1 @ [u])" "y ≠ new_vert" "u ∉ vset_to_set rts"
        using old_parent True parents_of_u_props lookup_u_not_none_roots
          edge_vertices[OF old_parent] assms(6) by auto
      then show ?thesis
        using True parent_same_org_old[OF old_parent]
        by (simp add: new_origin)
    next
      case False
      have not_root: "x ∉ vset_to_set (roots new_forest)"
        using arg_cong[OF dom_samer, of "λA. x ∈ A"] new_edge
        by (simp add: domIff)
      have not_new: "x ≠ new_vert"
        using False not_root
        by (auto simp: effect_of_contract_path(6) lookup_u_not_none_roots split: if_splits)
      have x_out: "x ∉ set (p1 @ [u])" "x ≠ new_vert"
        using False new_edge not_new by (auto simp: new_parents_are)
      obtain px where px: "parent_lookup prnts x = Some px"
        using False new_edge x_out forest_invar_F(7)
        by (auto simp: new_parents_are elim!: invar_odd_to_parent_non_matchingE split: if_splits)
      show ?thesis
      proof(cases "px ∈ set (p1 @ [u])")
        case True
        then have "y = new_vert"
          using outside_parent[OF px x_out(1)] x_out px new_edge
          by (auto simp: new_parents_are)
        then show ?thesis
          using x_out origin_u parent_same_org_old[OF px] x_in_p1_org_is_u's_org[OF True]
            edge_vertices[OF px] org_lookup_last
          by (auto simp: new_origin)
      next
        case False
        then have "y = px"
          using new_edge x_out by (simp add: new_parents_are px)
        moreover have "px ≠ new_vert"
          using False edge_vertices[OF px] assms(6) by auto
        ultimately show ?thesis
          using x_out False parent_same_org_old[OF px] edge_vertices[OF px]
          by (simp add: new_origin)
      qed
    qed
  qed

  have big_origin_conjunction_after:
    "origin_lookup (origins new_forest) v =
         Some (last (follow (parent_lookup (parents new_forest)) v)) ∧
        (∀ u ∈ set (follow (parent_lookup (parents new_forest)) v).
           origin_lookup (origins new_forest) v = origin_lookup (origins new_forest) u) ∧
       set (edges_of_path (follow (parent_lookup (parents new_forest)) v))
         ⊆ abstract_forest new_forest"
    if "v ∈ vset_to_set (roots new_forest) ∪ Vs (abstract_forest new_forest)" for v
    using that
  proof(induction v rule: follow_new_induct)
    case (1 vv)
    have tirple_conjD: "A ∧ B ∧ C ⟹ A" "A ∧ B ∧ C ⟹ B" "A ∧ B ∧ C ⟹ C"
      for A B C 
      by auto
    note IH = tirple_conjD[OF 1(1)]
    note Iprem= 1(2)
    show ?case
    proof(cases "parent_lookup (parents new_forest) vv")
      case None
      hence vv_root: "vv ∈ vset_to_set (roots new_forest)" 
        using "1.prems" dom_samer
              domIff[of vv "origin_lookup (origins new_forest)"] org_lookup_helper
        by auto
      show ?thesis
        using None by (auto simp add: lookup_self_implies_root vv_root follow_new_simps[of vv])
    next
      case (Some pvv)
      have triple_conjI: "⟦A;B;C⟧ ⟹ A ∧ B ∧ C" for A B C
        by auto
      have vv_pvv_in_new_F: "{vv, pvv} ∈ abstract_forest new_forest"
        using Some
        by(auto simp add:abstract_forest_def)
      hence pvv_is_new_F_vert:
        "pvv ∈ vset_to_set (roots new_forest) ∪ Vs (abstract_forest new_forest)"
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
    proof(cases "u ∈ vset_to_set rts", goal_cases)
      case 1
      note 1 = 1[simplified if_P[OF 1(4)] Un_empty_right Un_empty_left]
      then show ?case 
        using assms(5) by(auto elim!: matchingE)
    next
      case 2
      note 2 = 2[simplified if_not_P[OF 2(4)]]
      have u_pu_in_M: "{u, the (parent_lookup prnts u)} ∈ ℳ"
        using "2"(4) assms(4) forest_invar_F(5) invar_even_to_parent_matchingD parents_of_u_props
        by fastforce
      have case1: "e1 ∩ e2 = {}"
        if asm :"e1 ∈ ℳ - ({{u, the (parent_lookup prnts u)}} ∪ set (edges_of_path (p1 @ [u])))"
           "e2 = {new_vert, the (parent_lookup prnts u)}" for e1 e2
      proof-
        have e1_props: "e1 ∈ ℳ" "e1 ≠ {u, the (parent_lookup prnts u)}" 
                    "e1 ∉ set (edges_of_path (p1 @ [u]))"
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
              doubleton_in_matching(1)[of ℳ u "the (parent_lookup prnts u)" v] by simp
          then show ?case
            using "2"(2,5) e1_props(2) by auto
        next
          case 3
          hence if_u_or_new_in_e1:
             "new_vert ∈ e1 ⟹ e1 = {u, the (parent_lookup prnts u)}"
             "u ∈ e1 ⟹ e1 = {u, the (parent_lookup prnts u)}"
            using assms(6)  e1_props(1) by auto
          have if_pu_in_e1: "the (parent_lookup prnts u) ∈ e1 
                 ⟹ e1 = {u, the (parent_lookup prnts u)}" 
            using assms(5) e1_props(1) u_pu_in_M
              matching_unique_match[of ℳ "the (parent_lookup prnts u)" e1
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
      have case3:"e1 ∩ e2 = {}"
        if "e1 ∈ ℳ - ({{u, the (parent_lookup prnts u)}} ∪ set (edges_of_path (p1 @ [u])))"
           "e2 ∈ ℳ - ({{u, the (parent_lookup prnts u)}} ∪ set (edges_of_path (p1 @ [u])))"
        using that 1(3) by(intro matchingD[OF assms(5)]) auto
      show ?case
        apply(rule UnE[OF 2(1)], all ‹rule UnE[OF 2(2)]›)
        using  case1[of e1 e2] case1[of e2 e1] case2 case3
        by auto
    qed
  qed

  have new_parent_new_vert_None_pu_None:
      "parent_lookup (parents new_forest) new_vert = None ⟹
        parent_lookup prnts u = None"
    by(cases "parent_lookup prnts u")(auto simp add: new_parents_are)

  have parent_new_vert_is_pu:"parent_lookup (parents new_forest) new_vert = Some pu ⟹
       parent_lookup prnts u = Some pu" for pu
   using assms(6)  invar_basic_F(14,6) lookup_u_not_none_roots
   by(auto simp add: new_parents_are if_split[of "λ x. x = Some pu"])

  have assms6': "new_vert ∉ vset_to_set evs ∪ vset_to_set ods - set (p1 @ [u])"
    using assms(6) by auto

  have edges_p_in_F:
    "set (edges_of_path (p1@[u]@p2)) ⊆ abstract_forest (Forest rts evs ods prnts orngs)"
    using assms(2,3)  invar_basic_F(6)
      forest_invar_F(6) UnI1[of v "vset_to_set evs" "vset_to_set ods"]
      invar_rootsD(4)[of "Forest rts evs ods prnts orngs" v]
    by auto
  hence p_inVs_of_F:"set (p1@[u]@p2) ⊆ vset_to_set evs ∪ vset_to_set ods"
    using assms(2,3) forest_invar_F(1,4,6)
      path_follow_verts_in_verts_F[of ℳ "Forest rts evs ods prnts orngs" v]
      invar_basicE[of ℳ "Forest rts evs ods prnts orngs"] invar_basic_F(6) 
    by auto

  have coincide_parents_in_p2:
    "v' ∈ set p2 ⟹ 
     parent_lookup prnts v' = parent_lookup (parents new_forest) v'" for v'
    unfolding new_parents_are
  proof(subst if_not_P, goal_cases)
    case 1
    note one = this
    have "v' ≠ new_vert"
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
      have "⟦v' ∈ vset_to_set ods; the (parent_lookup prnts v') ∈ set (p1@[u])⟧ ⟹ False"
      proof(goal_cases)
        case 1
        then obtain pv' where pv': "parent_lookup prnts v' = Some pv'"
          using forest_invar_F(7) by(auto elim!: invar_odd_to_parent_non_matchingE) 
        then obtain p2b' where p2b': "p2b = pv'#p2b'" 
          using p2_split_middle assms(2) 
                follow_subsequent_parent_there[of v "(p1 @ [u]) @ p2a" v' p2b pv']
          by auto
        moreover have "pv' ≠ v'"
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
    "⟦parent_lookup prnts v' = Some pv'; pv' ∈ set (p1@[u]); v' ∉ set (p1@[u])⟧ ⟹
    parent_lookup (parents new_forest) v' = Some new_vert" for v' pv'
    unfolding new_parents_are
  proof(subst if_not_P, goal_cases)
    case 1
    hence "v' ∈ vset_to_set evs ∪ vset_to_set ods"
      using p_inVs_of_F parents_ev_od(1,2) by auto
    hence "v' ≠ new_vert"
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
    "⟦parent_lookup prnts v' = Some pv'; pv' ∉ set (p1@[u]); v' ∉ set (p1@[u])⟧ ⟹
    parent_lookup (parents new_forest) v' = parent_lookup prnts v'" for v' pv'
    unfolding new_parents_are
  proof(subst if_not_P, goal_cases)
    case 1
    hence "v' ∈ vset_to_set evs ∪ vset_to_set ods" 
      using invar_basic_F(14,6) by auto
    hence "v' ≠ new_vert"
      using "1"(3) assms6' by blast
    then show ?case
      by simp
  next
    case 2
    then show ?case 
      by auto
  qed

  show "⟦?asm1;?asm2⟧⟹ ?th5"
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
    hence v'_not_in_p1u: "v' ∉ set (p1 @ [u])" 
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
      hence p1'_not_Nil:"p1' ≠ []" and p1_not_Nil: "v' # p1' ≠ []"
        by auto
      note Cons = 2(1-3)[simplified if_not_P[OF p1'_not_Nil] 2(4)] 2(4)
      have pv':"parent_lookup prnts v' = Some pv'"
           "follow (parent_lookup prnts) pv' = pv' # list @ u # p2"
        using calculation Cons
              parents_here.follow_cons_2[folded follow_def, of a pv' "list @ u # p2"]
        by auto
      have to_old_precond: "pv' ∉ set (p1 @ [u])" "v' ∉ set (p1 @ [u])"
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
  assumes "forest_invar ℳ (Forest rts evs ods prnts orngs)" 
    "follow (parent_lookup prnts) v = p1@[u]@p2"
    "follow (parent_lookup prnts) v' = p1'@[u]@p2"
    "v ∈ vset_to_set evs"
    "v' ∈ vset_to_set evs"
    "set p1 ∩ set p1' = {}"
    "matching ℳ"
    "new_vert ∉ Vs ℳ ∪ vset_to_set evs ∪ vset_to_set ods - (set p1 ∪ set p1' ∪ {u})"
    "dblton_graph ℳ"
    and contr_def: "contr = (λ v. if v ∈ {u} ∪ set p1 ∪ set p1' then new_vert else v)"
    and new_forest_def:
    "new_forest = contract_fork (Forest rts evs ods prnts orngs) (p1@[u]) (p1'@[u]) new_vert"
  and new_vert_in_universe: "new_vert ∈ K"
  shows "forest_invar (quot_graph contr ℳ - {{new_vert}}) new_forest" (is ?th1)
    and  "abstract_forest new_forest 
         = quot_graph contr (abstract_forest (Forest rts evs ods prnts orngs))
             - {{new_vert}}" (is ?th2)
and "vset_to_set (odds new_forest) = vset_to_set ods - ({u} ∪ set p1 ∪ set p1')" (is ?th3)
and "vset_to_set (evens new_forest) = (vset_to_set evs - ({u} ∪ set p1 ∪ set p1')) ∪ {new_vert}" (is?th4)
and "vset_to_set (roots new_forest) =
    (if u ∈ vset_to_set rts
     then vset_to_set rts - {u} ∪ {new_vert} else vset_to_set rts)" (is ?th5)
and "matching (quot_graph contr ℳ - {{new_vert}})" (is ?th6)
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

  have u_even:"u ∈ vset_to_set evs"
  proof(rule ccontr, goal_cases)
    case 1
    hence u_odd: "u ∈ vset_to_set ods" 
      using assms(1,2,4) forest_invarD(1,4,6) invar_basicD(6)
           path_follow_verts_in_verts_F[OF forest_invarD(1,6,4), of v]
      by auto
    then obtain cu p1a where p1_split: "p1 = p1a@[cu]" 
      using 1 assms(4) hd_p_is_v by(cases "p1" rule: rev_cases) auto
    hence cu_u_in_F:"{cu, u} ∈ abstract_forest (Forest rts evs ods prnts orngs)" 
      using assms(2) follow_append follow_cons_2(2)[of cu u p2]
      by (fastforce simp add: abstract_forest_def)
    have pcu: "parent_lookup prnts cu = Some u"
      using p1_split assms(2) follow_subsequent_parent[of v p1a cu u p2]
      by auto
    hence cuu_M: "{cu, u} ∈ ℳ"
      using  cu_u_in_F  assms(1) forest_invarD(5) complex_invariant_consequences(2)
          invar_even_to_parent_matchingD  u_odd 
      by force
    obtain c'u p1'a where p1'_split: "p1' = p1'a@[c'u]" 
      using 1 assms(5) hd_p'_is_v' by(cases "p1'" rule: rev_cases) auto
    hence c'u_u_in_F:"{c'u, u} ∈ abstract_forest (Forest rts evs ods prnts orngs)" 
      using assms(3) follow_append follow_cons_2(2)[of c'u u p2]
      by (fastforce simp add: abstract_forest_def)
    have pc'u: "parent_lookup prnts c'u = Some u"
      using p1'_split assms(3) follow_subsequent_parent[of v' p1'a c'u u p2]
      by auto
    hence c'uu_M: "{c'u, u} ∈ ℳ"
      using  c'u_u_in_F  assms(1) forest_invarD(5) complex_invariant_consequences(2)
          invar_even_to_parent_matchingD u_odd 
      by force
    hence "c'u = cu" 
      using assms(7) cuu_M by(auto intro!: matching_partner_eqI)
    hence "c'u ∈ set p1 ∩ set p1'"
      using p1'_split p1_split by simp
    then show ?case 
      using assms(6) by simp
  qed
  define contr1 where "contr1 = (λv. if v ∈ set (p1 @ [u]) then u else v)"
  define intermedF where 
    "intermedF = contract_path (Forest rts evs ods prnts orngs) (p1 @ [u]) u"
  have u_not_there: "u ∉ Vs ℳ ∪ vset_to_set evs ∪ vset_to_set ods - set (p1 @ [u])"
    by auto
  have u_in_universe: "u ∈ K"
    using vset.fixed_univ_set_universe[OF invar_basicD(2)[simplified]] u_even by auto
  note after_first =
     contract_path_correct[OF assms(1,2,4) u_even assms(7) u_not_there assms(9) contr1_def intermedF_def u_in_universe]
  note p'_after = after_first(7)[OF assms(3,6)]
  have intermedF_split: "intermedF = Forest (roots intermedF) (evens intermedF)
          (odds intermedF) (parents intermedF) (origins intermedF)"
    by(cases intermedF) auto
  have invar_after_first: "forest_invar (quot_graph contr1 ℳ - {{u}}) 
           (Forest (roots intermedF) (evens intermedF)
          (odds intermedF) (parents intermedF) (origins intermedF))"
    using after_first(1)  intermedF_split by simp
  have final_precond1: "(if p1' = [] then u else v') ∈ vset_to_set (evens intermedF)"
    using after_first(4) hd_p'_is_v' hd_p_is_v assms(3,5,6) follow_append[of u _ u p2] 
    by(cases p1') auto
  have final_precond2: "u ∈ vset_to_set (evens intermedF)"
    by (simp add: after_first(4))
  have final_precond3: "new_vert ∉ Vs (quot_graph contr1 ℳ - {{u}}) ∪ vset_to_set (evens intermedF) ∪
       vset_to_set (odds intermedF) -
       set (p1' @ [u])"
    using assms(8)
    by (auto dest!: set_mp[OF Vs_subset[of 
                          "quot_graph contr1 ℳ - {{u}}" "quot_graph contr1 ℳ"],
                          simplified contr1_def, simplified]
          simp add: Vs_quot_graph_is_img contr1_def after_first(4,3))
  have final_precond4: "dblton_graph (quot_graph contr1 ℳ - {{u}})"
   using assms(8) 
   by(auto intro!: dblton_graph_contract_into_one_vert[OF assms(9) contr1_def])
  define contr2 where "contr2 = (λv. if v ∈ set (p1' @ [u]) then new_vert else v)"
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
            simplified intermedF_split[symmetric], OF final_precond5 new_vert_in_universe, 
            simplified after_first(2,3,4,5)
             quot_graphId]
  show ?th1 ?th6 ?th2 ?th3 ?th4 ?th5
    using final_props assms(8) by auto
qed

interpretation fork_contraction_spec_satisfied:
  alternating_forest_fork_contraction_spec
  where vset_invar = vset_invar and vset_to_set = vset_to_set
    and evens = evens and odds = odds and get_path = get_path
    and abstract_forest = abstract_forest and forest_invar = forest_invar
    and roots = roots and contract_fork = contract_fork and K = K
proof(goal_cases)
  case 1
  interpret af_spec_here:
    alternating_forest_spec evens odds get_path abstract_forest forest_invar roots
      vset_invar vset_to_set
    using satisified by (auto simp: alternating_forest_ordinary_extension_spec_def)
  have correct:
    "forest_invar (quot_graph contr M - {{new_vert}}) (contract_fork F (B1 @ [u]) (B2 @ [u]) new_vert) ∧
     abstract_forest (contract_fork F (B1 @ [u]) (B2 @ [u]) new_vert) =
      quot_graph contr (abstract_forest F) - {{new_vert}} ∧
     vset_to_set (odds (contract_fork F (B1 @ [u]) (B2 @ [u]) new_vert)) =
      vset_to_set (odds F) - ({u} ∪ set B1 ∪ set B2) ∧
     vset_to_set (evens (contract_fork F (B1 @ [u]) (B2 @ [u]) new_vert)) =
      vset_to_set (evens F) - ({u} ∪ set B1 ∪ set B2) ∪ {new_vert} ∧
     vset_to_set (roots (contract_fork F (B1 @ [u]) (B2 @ [u]) new_vert)) =
      (if u ∈ vset_to_set (roots F) then vset_to_set (roots F) - {u} ∪ {new_vert}
       else vset_to_set (roots F)) ∧
     matching (quot_graph contr M - {{new_vert}})"
    if "af_spec_here.contract_fork_precond M F v v' B1 B2 u new_vert P contr" "new_vert ∈ K"
    for M F v v' B1 B2 u new_vert P contr
  proof(cases F)
    case (Forest rts evs ods prnts orgns)
    have Finvar: "forest_invar M (Forest rts evs ods prnts orgns)"
      using that Forest by (auto elim!: af_spec_here.contract_fork_precondE)
    from that(1) show ?thesis
      unfolding Forest af_spec_here.contract_fork_precond_def
        get_path_eq_follow[OF Finvar] alt_forest.sel
    proof(elim conjE, goal_cases)
      case 1
      show ?case
        using contract_fork_correct[OF 1(1,4,5,7,8,6,2,9,3,10) refl that(2)]
        by auto
    qed
  qed
  show ?case
    by (intro alternating_forest_fork_contraction_spec.intro
        af_spec_here.alternating_forest_spec_axioms
        alternating_forest_fork_contraction_spec_axioms.intro; auto dest: correct)
qed

lemmas spec_satisfied =
  fork_contraction_spec_satisfied.alternating_forest_fork_contraction_spec_axioms

end
thm forest_contract_manipulation.spec_satisfied
end