theory Matching_Contraction_Expansion
  imports Graph_Quotient Basic_Matching.Matching_Augmentation_Executable
begin

locale blossom_matching_spec =
  fixes K::"'v set"
   and empty_matching::'matching
   and matching_invar::"'v set set \<Rightarrow> 'matching \<Rightarrow> bool"
   and lookup_partner::"'matching \<Rightarrow> 'v \<Rightarrow> 'v option"
   and get_partner::"'matching \<Rightarrow> 'v \<Rightarrow> 'v"
   and augment::"'matching \<Rightarrow> 'v list \<Rightarrow> 'matching"
   and matching_abstract::"'matching \<Rightarrow> 'v set set"
   and contract_path::"'matching \<Rightarrow> 'v list \<Rightarrow> 'v \<Rightarrow> 'matching"
   and expand_path_at_matched::"'matching \<Rightarrow> 'v list \<Rightarrow> 'v \<Rightarrow>'v \<Rightarrow> 'matching"
   and add_alternatingly::"'matching \<Rightarrow> 'v list \<Rightarrow> 'matching"
begin
definition "contract_path_precond G M p new_vert contr =
            (matching_invar G M \<and>
             alt_path (matching_abstract M) p \<and>  odd (length p) \<and>
            distinct p \<and> new_vert \<notin>  Vs (matching_abstract M) - set p \<and>
            contr = (\<lambda> x. if x \<in> set p then new_vert else x) \<and> set p \<subseteq> K \<and> new_vert \<in> K)"

lemma contract_path_precondE:
  "\<lbrakk>contract_path_precond G M p new_vert contr;
    \<lbrakk>matching_invar G M;
    alt_path (matching_abstract M) p;  odd (length p);
    distinct p; new_vert \<notin>  Vs (matching_abstract M) - set p;
    contr = (\<lambda> x. if x \<in> set p then new_vert else x); set p \<subseteq> K; new_vert \<in> K\<rbrakk> \<Longrightarrow> P\<rbrakk>
    \<Longrightarrow> P"
and contract_path_precondI:
  "\<lbrakk>matching_invar G M;
    alt_path (matching_abstract M) p;  odd (length p);
    distinct p; new_vert \<notin>  Vs (matching_abstract M) - set p;
    contr = (\<lambda> x. if x \<in> set p then new_vert else x); set p \<subseteq> K; new_vert \<in> K\<rbrakk>
    \<Longrightarrow> contract_path_precond G M p new_vert contr"
  by(auto simp add: contract_path_precond_def)

definition "expand_path_at_matched_precond G M old_vert mo new_vert p=
      (matching_invar G M \<and> {old_vert, mo} \<in> matching_abstract M \<and>
       new_vert \<notin> Vs (matching_abstract M) - {old_vert} \<and> new_vert \<notin> set p \<and>
       set p \<inter> Vs (matching_abstract M) = {} \<and> even (length p) \<and> distinct p \<and> set p \<subseteq> K \<and> new_vert \<in> K)"

lemma expand_path_at_matched_precondE:
  "\<lbrakk>expand_path_at_matched_precond G M old_vert mo new_vert p;
    \<lbrakk>matching_invar G M; {old_vert, mo} \<in> matching_abstract M;
     new_vert \<notin> Vs (matching_abstract M) - {old_vert}; new_vert \<notin> set p;
       set p \<inter> Vs (matching_abstract M) = {}; even (length p); distinct p; set p \<subseteq> K; new_vert \<in> K\<rbrakk> \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
and expand_path_at_matched_precondD:
  "\<lbrakk>matching_invar G M; {old_vert, mo} \<in> matching_abstract M;
     new_vert \<notin> Vs (matching_abstract M) - {old_vert}; new_vert \<notin> set p;
       set p \<inter> Vs (matching_abstract M) = {}; even (length p); distinct p; set p \<subseteq> K; new_vert \<in> K\<rbrakk>
   \<Longrightarrow> expand_path_at_matched_precond G M old_vert mo new_vert p"
  by(auto simp add: expand_path_at_matched_precond_def)

definition "add_alternatingly_precond G M p =
            (matching_invar G M \<and> set p \<inter> Vs (matching_abstract M) = {} \<and>
             even (length p) \<and> distinct p \<and> set p \<subseteq> K)"

lemma add_alternatingly_precondE:
   "\<lbrakk>add_alternatingly_precond G M p;
      \<lbrakk>matching_invar G M; set p \<inter> Vs (matching_abstract M) = {};
       even (length p); distinct p; set p \<subseteq> K\<rbrakk> \<Longrightarrow> P\<rbrakk>
     \<Longrightarrow> P"
and  add_alternatingly_precondI:
   "\<lbrakk>matching_invar G M; set p \<inter> Vs (matching_abstract M) = {};
       even (length p); distinct p; set p \<subseteq> K\<rbrakk>
    \<Longrightarrow> add_alternatingly_precond G M p"
  by(auto simp add: add_alternatingly_precond_def)
end

locale blossom_matching =
blossom_matching_spec +
assumes matching:
  "\<And> M G. matching_invar G M \<Longrightarrow> graph_matching G (matching_abstract M)"
  "\<And> G. Vs G \<subseteq> K \<Longrightarrow> matching_invar G empty_matching"
  "matching_abstract empty_matching = {}"
  "\<And> M G G'. \<lbrakk>matching_invar G M; G \<subseteq> G'; Vs G' \<subseteq> K\<rbrakk> \<Longrightarrow> matching_invar G' M"
  "\<And> M G x. \<lbrakk>matching_invar G M; x \<in> Vs (matching_abstract M)\<rbrakk>
         \<Longrightarrow>{x, get_partner M x} \<in> matching_abstract M"
and augment:
  "\<And> G M p. \<lbrakk>matching_invar G M; graph_augmenting_path G (matching_abstract M) p\<rbrakk> \<Longrightarrow>
         matching_invar G (augment M p)"
  "\<And> G M p. \<lbrakk>matching_invar G M; graph_augmenting_path G (matching_abstract M) p\<rbrakk> \<Longrightarrow>
         matching_abstract (augment M p) =  matching_abstract M \<oplus> set (edges_of_path p)"
and contract:
  "\<And> G M p new_vert contr.
   contract_path_precond G M p new_vert contr \<Longrightarrow>
   matching_invar (quot_graph contr G - {{new_vert}})
             (contract_path M p new_vert)"
 "\<And> G M p new_vert contr.
   contract_path_precond G M p new_vert contr \<Longrightarrow>
   matching_abstract (contract_path M p new_vert)
    = quot_graph contr (matching_abstract M) - {{new_vert}}"
and expand:
 "\<And> G M old_vert mo new_vert p.
    expand_path_at_matched_precond G M old_vert mo new_vert p \<Longrightarrow>
    matching_invar (G - {{old_vert, mo}} \<union> {{new_vert, mo}}
                    \<union> {edges_of_path p ! i| i. Suc i < length p \<and> even i})
                   (expand_path_at_matched M p old_vert new_vert)"
 "\<And> G M old_vert mo new_vert p.
    expand_path_at_matched_precond G M old_vert mo new_vert p \<Longrightarrow>
    matching_abstract (expand_path_at_matched M p old_vert new_vert) =
    matching_abstract M - {{old_vert, mo}} \<union> {{new_vert, mo}}
                    \<union> {edges_of_path p ! i| i. Suc i < length p \<and> even i}"
and add_alternatingly:
  "\<And> G M p. add_alternatingly_precond G M p \<Longrightarrow>
            matching_invar (G \<union> {edges_of_path p ! i| i. Suc i < length p \<and> even i})
            (add_alternatingly M p)"
 "\<And> G M p. add_alternatingly_precond G M p \<Longrightarrow>
            matching_abstract (add_alternatingly M p) =
            matching_abstract M \<union> {edges_of_path p ! i| i. Suc i < length p \<and> even i}"

and lookup_partner:
  "\<And>G M x y. matching_invar G M \<Longrightarrow>
   lookup_partner M x = Some y \<longleftrightarrow> {x, y} \<in> matching_abstract M"

context
  Matching_Augmentation_Specs
begin

definition
  "contract_path_at_matched M p new_vert =
    (let v = buddy_get M (hd p);
         cleared = foldl (\<lambda>M x. buddy_upd M x nil) M p
     in buddy_upd (buddy_upd cleared v new_vert) new_vert v)"

definition "contract_path M p new_vert =
  (if buddy_get M (hd p) = nil
   then foldl (\<lambda>M x. buddy_upd M x nil) M p
   else contract_path_at_matched M p new_vert)"

definition
  "expand_path_at_matched M p old_vert new_vert =
    (let v = buddy_get M old_vert;
         rematched = buddy_upd (buddy_upd (buddy_upd M old_vert nil) v new_vert) new_vert v
     in augment_impl rematched p)"

definition "contract_path_at_matched_precond G M p new_vert contr =
            (invar_matching G M \<and> hd p \<in> Vs (\<M> M) \<and> alt_path (\<M> M) p \<and> odd (length p) \<and>
            distinct p \<and> new_vert \<notin>  Vs (\<M> M) - set p \<and>
            contr = (\<lambda> x. if x \<in> set p then new_vert else x) \<and> set p \<subseteq> K \<and> new_vert \<in> K)"

definition "get_partner M x = buddy_get M x"

definition "add_alternatingly = augment_impl"

end

context
  matching_augmentation
begin

lemma get_partner_correct:
  assumes "invar_matching G M" "x \<in> Vs (\<M> M)"
  shows "{x, get_partner M x} \<in> \<M> M"
proof-
  have "buddy_lookup M x \<noteq> None"
    using assms(2) symmetric_buddiesD[OF invar_matchingD(2)[OF assms(1)]]
    by (auto simp: \<M>_def' Vs_def)
  then show ?thesis
    by (auto intro: buddy_get_in_\<M> simp: buddy_lookup_def get_partner_def split: if_splits)
qed

lemma clear_matching:
  assumes "buddy_invar M" "set p \<subseteq> K"
  shows "buddy_invar (foldl (\<lambda>M x. buddy_upd M x nil) M p)"
    "buddy_lookup (foldl (\<lambda>M x. buddy_upd M x nil) M p) =
       (\<lambda>x. if x \<in> set p then None else buddy_lookup M x)"
  using assms
  by (induction p arbitrary: M)
     (auto simp: buddy_map.fixed_univ_map_upd_invar buddy_lookup_upd_nil fun_eq_iff)

lemma contract_path_at_matched_effect:
  assumes "buddy_invar M" "buddy_lookup M (hd p) = Some v" "buddy_lookup M v = Some (hd p)"
    "distinct p" "v \<notin> set p" "new_vert \<in> set p \<or> (\<nexists>x. buddy_lookup M new_vert = Some x)"
    "set p \<subseteq> K" "new_vert \<in> K" "v \<in> K"
  shows "buddy_invar (contract_path_at_matched M p new_vert)"
    "\<M>_dir (contract_path_at_matched M p new_vert) =
       \<M>_dir M - {(x, y) |x y. x \<in> set p \<and> Some y = buddy_lookup M x}
         - {(v, hd p)} \<union> {(v, new_vert), (new_vert, v)}"
proof-
  have get: "buddy_get M (hd p) = v"
    using assms(2) by (auto simp: buddy_lookup_def split: if_splits)
  note cleared = clear_matching[OF assms(1,7)]
  show "buddy_invar (contract_path_at_matched M p new_vert)"
    using cleared(1) assms(8,9)
    by (simp add: contract_path_at_matched_def Let_def get buddy_map.fixed_univ_map_upd_invar)
  have look: "buddy_lookup (contract_path_at_matched M p new_vert) =
       (\<lambda>x. if x = new_vert then Some v else if x = v then Some new_vert
         else if x \<in> set p then None else buddy_lookup M x)"
    using cleared assms(8,9) in_K_not_nil
    by (auto simp: contract_path_at_matched_def Let_def get buddy_lookup_upd
                   buddy_map.fixed_univ_map_upd_invar fun_eq_iff)
  show "\<M>_dir (contract_path_at_matched M p new_vert) =
       \<M>_dir M - {(x, y) |x y. x \<in> set p \<and> Some y = buddy_lookup M x}
         - {(v, hd p)} \<union> {(v, new_vert), (new_vert, v)}"
    using assms(3,5,6)
    by (auto simp: \<M>_dir_def' look split: if_splits; metis option.inject)
qed

lemma contract_path_at_matched_correct:
  assumes "invar_matching G M" "hd p \<in> Vs (\<M> M)" "alt_path (\<M> M) p" "odd (length p)"
          "distinct p" "new_vert \<notin>  Vs (\<M> M) - set p"
  and universe: "set p \<subseteq> K" "new_vert \<in> K"
  and contr_def: "contr = (\<lambda> x. if x \<in> set p then new_vert else x)"
  shows   "invar_matching (quot_graph contr G - {{new_vert}})
             (contract_path_at_matched M p new_vert)" (is ?th1)
          "\<M> (contract_path_at_matched M p new_vert) = quot_graph contr (\<M> M) - {{new_vert}}" (is ?th2)
proof-
  note invar_matching_here = invar_matchingD[OF assms(1)]

  obtain v where v: "buddy_lookup M (hd p) = Some v" "buddy_lookup M v = Some (hd p)"
    using assms(2) invar_matching_here(2)
    by(auto elim!: symmetric_buddiesE simp add: \<M>_def' vs_member)

  hence hdp_v_in_M:"{hd p, v} \<in> \<M> M" and  hdp_v_in_M':"{v, hd p} \<in> \<M> M"
    by(auto simp add: \<M>_def')
  have dblton_M: "dblton_graph (\<M> M)"
    by (simp add: invar_matching_here(3) no_self_loop_buddy_dblton_graph)
  have matching_M:"matching (\<M> M)"
    by (simp add: invar_matching_here(4))
  have p_split_off_tl: "p = hd p # tl p"
    by (metis assms(4) even_zero list.exhaust_sel list.size(3))

  have rev_alt_path: "rev_alt_path (\<M> M) (tl p)"
    by (simp add: alt_path_tl_rev_alt_path assms(3))

  have v_neq_hd_p:"v \<noteq> hd p"
    using invar_matching_here(3) no_self_loop_buddyE v(2) by blast
  have even_tl: "even (length (tl p))"
    by (simp add: assms(4))
  note path_edge_cases = matching_edge_rev_alt_path_cases[OF rev_alt_path _ dblton_M matching_M]

  have v_in_set_p:"v \<notin> set p"
  proof(rule ccontr, goal_cases)
    case 1
    hence v_tl: "v \<in> set (tl p)" and "length p \<ge> 3"
      using v_neq_hd_p assms(4) by (cases p rule: list_cases4; auto)+
    hence tl_longer_1:"1 < length (tl p)" by auto
    obtain e where e: "e \<in> set (edges_of_path (tl p))" "v \<in> e" "e \<in> \<M> M"
      using in_rev_alt_path_part_of_matching[OF rev_alt_path v_tl even_tl tl_longer_1] by auto
    show ?case
    proof(cases rule: path_edge_cases[OF e(3)])
      case (1 u' v' i)
      hence "e = {hd p, v}"
        using e(2,3)  hdp_v_in_M  matching_unique_match[OF matching_M] by simp
      hence "hd p \<in> set (tl p)"
        using  e(1) edge_not_in_edges_in_path[of "hd p" "tl p"] by auto
      hence  "\<not> distinct p"
        by(cases p) auto
      then show ?thesis
        using assms(5) by simp
    next
      case (2 u v)
      then show ?thesis
        using even_tl by fastforce
    next
      case 3
      then show ?thesis
        using e(2) v_tl by auto
    qed
  qed

  have new_vert_in_p_or_not_buddy:"new_vert \<in> set p \<or> (\<nexists>x. buddy_lookup M new_vert = Some x)"
    using assms(6) by (auto simp add: \<M>_def')

  have v_in_K: "v \<in> K"
    using hdp_v_in_M invar_matching_here(4,6) by (auto simp: Vs_def)
  note contract_path_at_matched_effect =
       contract_path_at_matched_effect[OF invar_matching_here(1) v assms(5)
                                            v_in_set_p new_vert_in_p_or_not_buddy universe v_in_K]

  have lookup_and_p_heler1:
  "\<lbrakk>va \<in> set p; Some u = buddy_lookup M va; va \<noteq> v; u \<noteq> v\<rbrakk> \<Longrightarrow> u \<in> set p" for va u
  proof(goal_cases)
    case 1
    hence v_tl: "va \<in> set (tl p)"
      using v(1) by(cases p) auto
    hence tl_longer_1:"1 < length (tl p)"
      using even_tl by(cases p rule: list_cases4) auto
    from 1 have uva_in_M: "{u, va} \<in> \<M> M"
      by(force simp add: \<M>_def' doubleton_eq_iff)
    moreover obtain e where e: "e \<in> set (edges_of_path (tl p))" "va \<in> e" "e \<in> \<M> M"
      using in_rev_alt_path_part_of_matching[OF rev_alt_path v_tl even_tl tl_longer_1] by auto
    ultimately have "u \<in> set (tl p)"
      using matching_unique_match[OF matching_M, of va e "{u, va}", simplified]
      by(auto intro!: v_in_edge_in_path[of u va "tl p"])
    thus ?case
      by(cases p) auto
  qed

  have hd_p_in_p:"hd p \<in> set p"
    using p_split_off_tl by(cases p) auto

  have lookup_and_p_heler2:
  "\<lbrakk>u \<in> set p; Some u = buddy_lookup M va; va \<noteq> v; u \<noteq> v\<rbrakk> \<Longrightarrow> va \<in> set p" for va u
    using invar_matching_here(2) symmetric_buddiesD[of M u va] lookup_and_p_heler1[of u va] by auto

  have symm_buddies_after:
     "symmetric_buddies (contract_path_at_matched M p new_vert)"
      using invar_matching_here(2) v(2) v_in_set_p hd_p_in_p
      by(auto elim!: symmetric_digraphE
             intro!: symmetric_digraphI
           simp add: symmetric_digraph_iff_symmetric_buddies
                     contract_path_at_matched_effect(2)
              symmetric_buddiesD[OF invar_matching_here(2), simplified eq_commute[of _ "Some _"]]
               dest: lookup_and_p_heler1 lookup_and_p_heler2)

    have v_neq_new_vert: "v \<noteq> new_vert"
      using new_vert_in_p_or_not_buddy v(2) v_in_set_p by blast

    have no_self_loop_buddy_after: "no_self_loop_buddy (contract_path_at_matched M p new_vert)"
      using v_neq_new_vert invar_matching_here(3)
      by(auto intro!: no_self_loop_buddyI
            simp add: no_self_loop_buddy_and_\<M>_dir contract_path_at_matched_effect(2))

    have M_contract_is_UD:"\<M> (contract_path_at_matched M p new_vert) =
          \<M> M - {{x, y} |x y. x \<in> set p \<and> Some y = buddy_lookup M x} \<union>
        {{v, new_vert}}"
      unfolding \<M>_\<M>_dir_UD contract_path_at_matched_effect(2)
    proof ((rule subset_antisym; rule subsetI), goal_cases)
      case (1 e)
      then obtain u' v'  where
        "(u', v') \<in> \<M>_dir M - ({(x, y) |x y. x \<in> set p \<and> Some y = buddy_lookup M x} \<union> {(v, hd p)})
         \<union> {(v, new_vert), (new_vert, v)}"
           "e = {u', v'}"
        unfolding UD_def by blast
      then show ?case
      proof(elim UnE, goal_cases)
        case 1
        note one = this
        show ?case
        proof(rule UnI1, rule DiffI, goal_cases)
          case 1
          then show ?case
            using one by (simp add: in_UDI)
        next
          case 2
          show ?case
          proof(rule ccontr, goal_cases)
            case 1
            hence "(u', v') \<in> {(x, y) |x y. x \<in> set p \<and> Some y = buddy_lookup M x}"
              using v(2) v_in_set_p invar_matching_here(2) one(2)
              by (auto elim!: symmetric_buddiesE
                    simp add: one(1) doubleton_eq_iff
                              symmetric_buddiesD[OF invar_matching_here(2),
                                  simplified eq_commute[of _ "Some _"]]
                       intro: lookup_and_p_heler1
                        dest: lookup_and_p_heler1)
            then show ?case
              using one(2) by force
          qed
        qed
      qed auto
    next
      case (2 e)
      then show ?case
      proof(elim UnE, goal_cases)
        case 1
        moreover then obtain u' v' where "e = {u', v'}" "(u',v') \<in> \<M>_dir M"
          by (auto simp add: UD_def)
        ultimately show ?case
          using hd_p_in_p v(1)
          by(fastforce intro!: in_UDI[of u' v'])
    qed (auto simp add: UD_def)
  qed

  have x_buddies_helper:
      "{{x, y} |x y. x \<in> set p \<and> Some y = buddy_lookup M x} =
        insert {hd p, v} {edges_of_path p ! i | i. Suc i < length p \<and> odd i}"
  proof-
    have "{{x, y} |x y. x \<in> set p \<and> Some y = buddy_lookup M x} =
         insert {hd p, v} {e| e. e \<in> \<M> M  \<and> e \<inter> set (tl p) \<noteq> {}}"
       unfolding  \<M>_def'
    proof(subst p_split_off_tl, rule, goal_cases)
      case 1
      then show ?case
        using v invar_matching_here(2) by force
    next
      case 2
      then show ?case
      using invar_matching_here(2) v
      by(fastforce elim!: symmetric_buddiesE
                simp add: doubleton_eq_iff symmetric_buddiesD[OF invar_matching_here(2),
                          simplified eq_commute[of _ "Some _"]])
  qed
    moreover have "{e| e. e \<in> \<M> M  \<and> e \<inter> set (tl p) \<noteq> {}} =
               {edges_of_path (tl p) ! i | i. Suc i < length (tl p) \<and> even i}"
      using even_tl matched_verts_in_rev_alt_path_path_edges matching_M rev_alt_path by blast
    moreover have "... = {edges_of_path p ! i | i. Suc i < length p \<and> odd i}"
      using assms(4) less_Suc_eq_0_disj
      by(cases p rule: list_cases3)(auto intro:  exI[of _ "Suc _"])
    ultimately show ?thesis
      by simp
  qed

  have set_2diff_distr: "A - B - C = A - (B \<union> C)" for A B C by auto

  have set_minus_absorb: "A - B = A - (A \<inter> B)" for A B by auto

  have UD_helper:
   "UD ({(x, y) |x y. x \<in> set p \<and> Some y = buddy_lookup M x} \<union> {(v, hd p)}) =
     insert {hd p, v} {edges_of_path p ! i |i. Suc i < length p \<and> odd i}"
    using hd_p_in_p v(1)
    unfolding x_buddies_helper[symmetric]
    by(fastforce simp add: UD_def)
  have edges_of_p_split_off_v: "edges_of_path (v # p) = {v,hd p} # edges_of_path p"
    using hd_p_in_p by(cases p) auto
  have SD_here:
      "symmetric_digraph ({(x, y) |x y. x \<in> set p \<and> Some y = buddy_lookup M x} \<union> {(v, hd p)})"
   using lookup_and_p_heler1 v_in_set_p v
   by(auto elim!: symmetric_buddiesE
          intro!: symmetric_digraphI
        simp add: hd_p_in_p
                  symmetric_buddiesD[OF invar_matching_here(2), simplified eq_commute[of _ "Some _"]]
           dest:lookup_and_p_heler1)
  have Suc_i_less_p_is:"Suc i < length p \<longleftrightarrow> i < length (edges_of_path p)" for i p
    using assms(4) by(cases p) (auto simp add: edges_of_path_length)
  have rev_alt_v:"rev_alt_path (\<M> M) (v # p)"
    by(auto simp add: alt_list_step assms(3) edges_of_p_split_off_v hdp_v_in_M')

  show th2: ?th2
      unfolding \<M>_\<M>_dir_UD contract_path_at_matched_effect(2) UD_union_hom
                set_2diff_distr
      unfolding UD_diff_hom[OF SD_here]
      unfolding UD_helper \<M>_\<M>_dir_UD[symmetric] UD_of_swapped_pairs
      unfolding alt_path_matching_quot[OF matching_M hdp_v_in_M' assms(3,4)
                         dblton_M assms(5,6) contr_def]
    proof(rule arg_cong2[where f = Set.union], subst (2) set_minus_absorb,
          subst rev_alt_path_intersected_with_matching[OF matching_M rev_alt_v], goal_cases)
      case 1
      thus ?case
      unfolding edges_of_p_split_off_v Suc_i_less_p_is
      using nth_Cons_0[of "{v, hd p}" "edges_of_path p"]
            nth_Cons_Suc[of "{v, hd p}" "edges_of_path p"]
      by (fastforce simp add: less_Suc_eq_0_disj insert_commute)+
  qed auto

  have graph_matching_after:
    "graph_matching (quot_graph contr G - {{new_vert}}) (\<M> (contract_path_at_matched M p new_vert))"
    using invar_matching_here(4) assms(3,4,5,6)  dblton_M
    by(unfold th2, intro alt_path_contract_matching[OF _ hdp_v_in_M']) (auto simp add: contr_def)
  have finite_after: "finite (\<M> (contract_path_at_matched M p new_vert))"
    by (simp add: M_contract_is_UD invar_matching_here(5))

  have universe_after: "Vs (quot_graph contr G - {{new_vert}}) \<subseteq> K"
    using invar_matching_here(6) universe(2)
    by (auto simp: Vs_def quot_graph_def contr_def)
  show ?th1
   by(intro invar_matchingI symm_buddies_after contract_path_at_matched_effect(1)
            no_self_loop_buddy_after graph_matching_after finite_after universe_after)
qed

lemma expand_path_at_matched_effect:
  assumes "buddy_invar M" "distinct p" "even (length p)" "set p \<inter> dVs (\<M>_dir M) = {}"
    "buddy_lookup M old_vert = Some ovn" "ovn \<notin> set p" "new_vert \<notin> set p"
    "set p \<subseteq> K" "old_vert \<in> K" "new_vert \<in> K" "ovn \<in> K"
  shows "buddy_invar (expand_path_at_matched M p old_vert new_vert)"
    "\<M>_dir (expand_path_at_matched M p old_vert new_vert) =
       \<M>_dir M - {(x, y) |x y. x \<in> {old_vert, new_vert, ovn} \<and> buddy_lookup M x = Some y}
         \<union> {(new_vert, ovn), (ovn, new_vert)}
         - {(u, v) |u v. u \<in> set p \<and> buddy_lookup M u = Some v}
         \<union> \<Union>{{(u, v), (v, u)} |u v i. u = p ! i \<and> v = p ! (i + 1) \<and>
                                                   i + 1 < length p \<and> even i}"
proof-
  have get: "buddy_get M old_vert = ovn"
    using assms(5) by (auto simp: buddy_lookup_def split: if_splits)
  define rematched where
    "rematched = buddy_upd (buddy_upd (buddy_upd M old_vert nil) ovn new_vert) new_vert ovn"
  have inv: "buddy_invar rematched"
    using assms(1,9,10,11)
    by (simp add: rematched_def buddy_map.fixed_univ_map_upd_invar)
  have look: "buddy_lookup rematched =
      (buddy_lookup M)(old_vert := None, ovn \<mapsto> new_vert, new_vert \<mapsto> ovn)"
    using assms(1,9,10,11) in_K_not_nil
    by (simp add: rematched_def buddy_lookup_upd buddy_lookup_upd_nil
                  buddy_map.fixed_univ_map_upd_invar)
  have effect: "\<M>_dir rematched =
       \<M>_dir M - {(x, y) |x y. x \<in> {old_vert, new_vert, ovn} \<and> buddy_lookup M x = Some y}
         \<union> {(new_vert, ovn), (ovn, new_vert)}"
    by (auto simp: \<M>_dir_def' look split: if_splits; metis option.inject)
  have same: "buddy_lookup rematched u = buddy_lookup M u" if "u \<in> set p" for u
    using that assms(4,5,6,7)
    by (auto simp: look \<M>_dir_def' dVs_def)
  have expand: "expand_path_at_matched M p old_vert new_vert = augment_impl rematched p"
    by (simp add: expand_path_at_matched_def rematched_def Let_def get)
  show "buddy_invar (expand_path_at_matched M p old_vert new_vert)"
    unfolding expand by (rule augment_impl_effect(1)[OF inv assms(2,3,8)])
  show "\<M>_dir (expand_path_at_matched M p old_vert new_vert) =
       \<M>_dir M - {(x, y) |x y. x \<in> {old_vert, new_vert, ovn} \<and> buddy_lookup M x = Some y}
         \<union> {(new_vert, ovn), (ovn, new_vert)}
         - {(u, v) |u v. u \<in> set p \<and> buddy_lookup M u = Some v}
         \<union> \<Union>{{(u, v), (v, u)} |u v i. u = p ! i \<and> v = p ! (i + 1) \<and>
                                                   i + 1 < length p \<and> even i}"
    unfolding expand augment_impl_effect(2)[OF inv assms(2,3,8)] effect
    by (auto simp: same)
qed

lemma extend_graph:
 "\<lbrakk>invar_matching G M; G \<subseteq> G'; Vs G' \<subseteq> K\<rbrakk>
   \<Longrightarrow> invar_matching G' M"
  by(auto elim!: invar_matchingE intro!: invar_matchingI)

lemma expand_path_at_matched_correct:
  assumes "invar_matching G M" "{old_vert, mo} \<in> \<M> M" "new_vert \<notin> Vs (\<M> M) - {old_vert}"
          "new_vert \<notin> set p" "set p \<inter> Vs (\<M> M) = {}" "even (length p)" "distinct p"
 and universe: "set p \<subseteq> K" "new_vert \<in> K"
 and new_matching_def: "M' = \<M> M - {{old_vert, mo}} \<union> {{new_vert, mo}}
         \<union> {edges_of_path p ! i| i. Suc i < length p \<and> even i}"
shows "invar_matching (G - {{old_vert, mo}} \<union> {{new_vert, mo}}
                       \<union> {edges_of_path p ! i| i. Suc i < length p \<and> even i})
           (expand_path_at_matched M p old_vert new_vert)" (is ?th1)
      "\<M> (expand_path_at_matched M p old_vert new_vert) = M'" (is ?th2)
proof-

  note invar_matching_here = invar_matchingD[OF assms(1)]

  have effect_precond1: "set p \<inter> dVs (\<M>_dir M) = {}"
    using assms(5) by(auto elim!: in_dVsE(1) simp add: \<M>_def' \<M>_dir_def' Vs_def)
  have effect_precond2: "buddy_lookup M old_vert = Some mo"
    using assms(2)  invar_matching_here(2)
    by(auto simp add: \<M>_def' symmetric_buddiesD doubleton_eq_iff)
  have effect_precond3: "mo \<notin> set p" "new_vert \<notin> set p"
    using assms(2,3,4,5)
    invar_matching_here(2)
    by(auto dest: edges_are_Vs_2
        simp add: \<M>_def' symmetric_buddiesD doubleton_eq_iff vs_member edges_are_Vs_2) blast+
  have in_K: "old_vert \<in> K" "mo \<in> K"
    using assms(2) invar_matching_here(4,6) by (auto simp: Vs_def)
  note effect_here = expand_path_at_matched_effect[OF
          invar_matching_here(1) assms(7,6) effect_precond1 effect_precond2 effect_precond3 universe(1) in_K(1) universe(2) in_K(2)]

  have lookup1: "buddy_lookup M v = Some new_vert \<Longrightarrow> v = mo"
                "buddy_lookup M v = Some mo \<Longrightarrow> v = old_vert"for v
    using assms(2,3) effect_precond2 symmetric_buddiesD[OF invar_matching_here(2)] effect_precond2
    by(auto simp add: vs_member \<M>_def' doubleton_eq_iff)+


  show th2: ?th2
    unfolding \<M>_\<M>_dir_UD effect_here UD_union_hom new_matching_def
  proof(rule arg_cong2[where f = Set.union], goal_cases)
    case 1
    then show ?case
    proof(subst (2) Diff_triv, goal_cases)
      case 1
      then show ?case
        using effect_precond1
        by (auto simp add: effect_precond3)
    next
      case 2
      show ?case
        unfolding UD_union_hom
      proof(rule arg_cong2[where f = Set.union], goal_cases)
        case 1
        show ?case
        proof(subst UD_diff_hom, goal_cases)
          case 1
          then show ?case
            using invar_matching_here(2) effect_precond2  assms(3)
            by(auto intro!: symmetric_digraphI simp add: symmetric_buddiesD \<M>_def')
              (simp add: symmetric_buddiesD[of M old_vert, symmetric]
                symmetric_buddiesD[of M old_vert mo, symmetric])+
        next
          case 2
          then show ?case
            using assms(3) invar_matching_here(2)
            by (intro arg_cong2[where f = "(-)"])
               (auto intro!: exI[of "\<lambda> u. \<exists> v. _ v u", of _ old_vert]
                   simp add: UD_def \<M>_def' effect_precond2 symmetric_buddiesD lookup1 vs_member
                       dest: lookup1)
        qed
      next
        case 2
        then show ?case
          by (simp add: UD_of_swapped_pairs)
      qed
    qed
  next
    case 2
    then show ?case
      proof ((rule subset_antisym; rule subsetI), goal_cases)
        case (1 e)
        then obtain i where i: "i + 1 < length p" "even i"
          "e = {p ! i, p ! (i + 1)}"
          by (auto simp: UD_def insert_commute)
        then show ?case
          using edges_of_path_index[of i p]
          by (auto intro!: exI[of _ i])
      next
        case (2 e)
        then obtain i where i: "Suc i < length p" "even i" "e = edges_of_path p ! i"
          by auto
        have e_eq: "e = {p ! i, p ! (i + 1)}"
          using i edges_of_path_index[OF i(1)] by simp
        show ?case
          unfolding e_eq
        proof (rule in_UDI, rule UnionI[where X="{(p ! i, p ! (i + 1)), (p ! (i + 1), p ! i)}"])
          show "{(p ! i, p ! (i + 1)), (p ! (i + 1), p ! i)} \<in>
            {{(u, v), (v, u)} |u v j. u = p ! j \<and> v = p ! (j + 1) \<and>
                                      j + 1 < length p \<and> even j}"
            by (rule CollectI, rule_tac x="p ! i" in exI, rule_tac x="p ! (i + 1)" in exI,
                rule_tac x=i in exI) (simp add: i(1,2))
          show "(p ! i, p ! (i + 1)) \<in> {(p ! i, p ! (i + 1)), (p ! (i + 1), p ! i)}"
            by simp
        qed
      qed
  qed

  have symmetric_buddies_after:
      "symmetric_buddies (expand_path_at_matched M p old_vert new_vert)"
    unfolding symmetric_digraph_iff_symmetric_buddies effect_here(2)
  proof(rule symmetric_union_pres, goal_cases)
    case 1
    then show ?case
    proof(rule symmetric_diff_pres, goal_cases)
      case 1
      then show ?case
        using invar_matching_here(2) effect_precond2
              symmetric_buddiesD[of M mo old_vert, OF invar_matching_here(2)]
        by(auto elim!: symmetric_digraphE
               intro!: symmetric_digraphI
             simp add: symmetric_digraph_iff_symmetric_buddies
                       lookup1(1)
                       symmetric_buddiesD[OF invar_matching_here(2), of old_vert, symmetric]
                       symmetric_buddiesD[OF invar_matching_here(2), of old_vert mo, symmetric]
                       symmetric_buddiesD[of M _ new_vert, OF invar_matching_here(2)], auto?)
    next
      case 2
      have "(x, y) \<notin> \<M>_dir M" if "x \<in> set p" for x y
        using effect_precond1 that by (auto dest: Pair_Graph.dVsI(1))
      hence "{(u, v) |u v. u \<in> set p \<and> buddy_lookup M u = Some v} = {}"
        by (auto simp: \<M>_dir_def')
      then show ?case
        by (auto simp: symmetric_digraph_def)
    qed
  next
    case 2
    then show ?case
      by(auto intro!: symmetric_digraphI)
  qed

  have no_self_loop_buddy_after:
     "no_self_loop_buddy (expand_path_at_matched M p old_vert new_vert)"
    using effect_precond2 invar_matching_here(3) lookup1(1)
    by(auto elim!: no_self_loop_buddyE
         simp add: no_self_loop_buddy_and_\<M>_dir effect_here(2) assms(7) nth_eq_iff_index_eq
            intro: no_self_loop_buddyE[OF invar_matching_here(3)])

  have matching_after:
   "graph_matching (G - {{old_vert, mo}} \<union> {{new_vert, mo}}
                    \<union> {edges_of_path p ! i |i. Suc i < length p \<and> even i})
     (\<M> (expand_path_at_matched M p old_vert new_vert))"
  proof(rule, goal_cases)
    case 1
    then show ?case
      unfolding th2 new_matching_def
    proof(rule matching_vertex_disj_union, goal_cases)
      case 1
      have "{new_vert, mo} \<inter> Vs (\<M> M - {{old_vert, mo}}) = {}"
        using assms(3)
        by (simp add: remove_matching_edge_Vs[OF conjunct1[OF invar_matching_here(4)] assms(2)])
      then have "matching (insert {new_vert, mo} (\<M> M - {{old_vert, mo}}))"
        by (rule matching_insert)
           (rule matching_delete[OF conjunct1[OF invar_matching_here(4)]])
      then show ?case
        by simp
    next
      case 2
      then show ?case
        by(auto intro!: even_edges_of_distinct_path_are_matching simp add: assms(7))
    next
      case 3
      have i_smp:"i < length p - 1 \<longleftrightarrow> Suc i < length p" for i
        by (simp add: less_diff_conv)
      show ?case
        using   assms(5,6) effect_precond3
        by (auto elim!: vs_member_elim simp add: verts_of_even_edges[of p, simplified i_smp])
    qed
  next
    case 2
    then show ?case
      using invar_matching_here(4)
      by(auto simp add: th2 new_matching_def)
  qed

  have finite_after: "finite (\<M> (expand_path_at_matched M p old_vert new_vert))"
    by(auto intro!: finite_subset[of _ "set (edges_of_path p)"]
          simp add: th2 new_matching_def invar_matching_here(5) edges_of_path_length)

  show ?th1
  proof(rule invar_matchingI, goal_cases)
    case 1
    then show ?case
      by (simp add: effect_here(1))
  next
    case 2
    then show ?case
      using symmetric_buddies_after by simp
  next
    case 3
    then show ?case
      using no_self_loop_buddy_after by simp
  next
    case 4
    then show ?case
      using matching_after by simp
  next
    case 5
    then show ?case
      using finite_after by simp
  next
    case 6
    have pK: "p ! i \<in> K" if "i < length p" for i
      using universe(1) nth_mem[OF that] by auto
    show ?case
      using invar_matching_here(6) universe in_K
      by (auto simp: Vs_def edges_of_path_index pK dest: Suc_lessD)
  qed
qed

lemma add_alternatingly_correct:
  assumes "invar_matching G M"  "set p \<inter> Vs (\<M> M) = {}" "even (length p)" "distinct p"
 and universe: "set p \<subseteq> K"
 and new_matching_def: "M' = \<M> M
         \<union> {edges_of_path p ! i| i. Suc i < length p \<and> even i}"
shows "invar_matching (G \<union> {edges_of_path p ! i| i. Suc i < length p \<and> even i})
           (add_alternatingly M p)" (is ?th1)
      "\<M> (add_alternatingly M p) = M'" (is ?th2)
proof-

  note invar_matching_here = invar_matchingD[OF assms(1)]

  note augment_impl_effect_here = augment_impl_effect[OF invar_matching_here(1) assms(4,3) universe]

  have M_dir_with_p: "\<lbrakk>(u, v) \<in> \<M>_dir M; v \<in> set p \<or> u \<in> set p\<rbrakk> \<Longrightarrow> False" for u v
    using assms(2) by(auto simp add: \<M>_\<M>_dir_UD Vs_dVs_UD)


  show th2: ?th2
    unfolding \<M>_\<M>_dir_UD add_alternatingly_def
              augment_impl_effect_here(2) UD_union_hom new_matching_def
  proof(rule arg_cong2[where f = Set.union], goal_cases)
    case 1
    then show ?case
    proof(subst Diff_triv, goal_cases)
      case 1
      then show ?case
        by (auto dest: M_dir_with_p)
    next
    qed simp
  next
    case 2
    then show ?case
      using edges_of_path_index
      by(auto simp add: UD_def) blast
  qed

  have symmetric_buddies_after:
      "symmetric_buddies (add_alternatingly M p)"
    unfolding symmetric_digraph_iff_symmetric_buddies add_alternatingly_def
              augment_impl_effect_here(2)
  proof(rule symmetric_union_pres, goal_cases)
    case 1
    then show ?case
    proof(rule symmetric_diff_pres, goal_cases)
      case 1
      then show ?case
        using invar_matching_here(2) symmetric_digraph_iff_symmetric_buddies by blast
    next
      case 2
      then show ?case
        using assms(2) edges_are_Vs_2
        by(auto intro!: symmetric_digraphI simp add: \<M>_def')blast+
    qed
  next
    case 2
    then show ?case
      by(auto intro!: symmetric_digraphI)
  qed

  have no_self_loop_buddy_after:
     "no_self_loop_buddy (add_alternatingly M p)"
    using invar_matching_here(3)
    by(auto elim!: no_self_loop_buddyE
         simp add: no_self_loop_buddy_and_\<M>_dir  nth_eq_iff_index_eq
                   add_alternatingly_def augment_impl_effect_here(2) assms(4)
            intro: no_self_loop_buddyE[OF invar_matching_here(3)])

  have matching_after:
   "graph_matching (G \<union> {edges_of_path p ! i |i. Suc i < length p \<and> even i})
     (\<M> (add_alternatingly M p))"
  proof(rule, goal_cases)
    case 1
    then show ?case
      unfolding th2 new_matching_def
    proof(rule matching_vertex_disj_union, goal_cases)
      case 1
      then show ?case
      using assms(2,3) invar_matching_here(4)
      by(auto intro!: matchingI elim!: matchingE)
    next
      case 2
      then show ?case
        by(auto intro!: even_edges_of_distinct_path_are_matching simp add: assms(4))
    next
      case 3
      have i_smp:"i < length p - 1 \<longleftrightarrow> Suc i < length p" for i
        by (simp add: less_diff_conv)
      show ?case
        using  assms(2,3)
        by (auto elim!: vs_member_elim simp add: verts_of_even_edges[of p, simplified i_smp])
    qed
  next
    case 2
    then show ?case
      using invar_matching_here(4)
      by(auto simp add: th2 new_matching_def)
  qed

  have finite_after: "finite (\<M> (add_alternatingly M p))"
    by(auto intro!: finite_subset[of _ "set (edges_of_path p)"]
          simp add: th2 new_matching_def invar_matching_here(5) edges_of_path_length)

  show ?th1
  proof(rule invar_matchingI, goal_cases)
    case 1
    then show ?case
      by (simp add: add_alternatingly_def augment_impl_effect_here(1))
  next
    case 6
    have pK: "p ! i \<in> K" if "i < length p" for i
      using universe(1) nth_mem[OF that] by auto
    show ?case
      using invar_matching_here(6) universe
      by (auto simp: Vs_def edges_of_path_index pK dest: Suc_lessD)
  qed (simp add: finite_after matching_after
                  no_self_loop_buddy_after symmetric_buddies_after)+
qed


lemma contract_path_at_free_correct:
  assumes "invar_matching G M" "buddy_lookup M (hd p) = None"
    "alt_path (\<M> M) p" "odd (length p)" "set p \<subseteq> K" "new_vert \<in> K"
    "new_vert \<notin> Vs (\<M> M) - set p"
    "contr = (\<lambda>x. if x \<in> set p then new_vert else x)"
  defines "N \<equiv> foldl (\<lambda>M x. buddy_upd M x nil) M p"
  shows "invar_matching (quot_graph contr G - {{new_vert}}) N"
    "\<M> N = quot_graph contr (\<M> M) - {{new_vert}}"
proof-
  note inv = invar_matchingD[OF assms(1)]
  note cleared = clear_matching[OF inv(1) assms(5), folded N_def]
  have closed: "y \<in> set p" if xy: "buddy_lookup M x = Some y" and xp: "x \<in> set p" for x y
  proof-
    have xtl: "x \<in> set (tl p)"
      using xp xy assms(2) by (cases p) auto
    have even_tl: "even (length (tl p))"
      using assms(4) by simp
    have "length (tl p) > 0"
      using xtl by (cases "tl p") auto
    then have "1 < length (tl p)"
      using even_tl by presburger
    then obtain e where e: "e \<in> set (edges_of_path (tl p))" "x \<in> e" "e \<in> \<M> M"
      using in_rev_alt_path_part_of_matching[OF alt_path_tl_rev_alt_path[OF assms(3)] xtl even_tl]
      by blast
    have "{x, y} \<in> \<M> M"
      using xy by (auto simp: \<M>_def')
    then have "e = {x, y}"
      using inv(4) e(2,3) by (auto dest: matching_unique_match)
    then have "y \<in> set (tl p)"
      using e(1) by (auto dest: v_in_edge_in_path_gen)
    then show ?thesis
      by (cases p) auto
  qed
  have closed_iff: "x \<in> set p \<longleftrightarrow> y \<in> set p" if "buddy_lookup M x = Some y" for x y
    using closed[OF that] closed[of y x] symmetric_buddiesD[OF inv(2), of x y] that by blast
  have abs: "\<M> N = {e \<in> \<M> M. e \<inter> set p = {}}"
    using closed_iff by (auto simp: \<M>_def' cleared(2) split: if_splits)
  have unchanged: "contr ` e = e \<and> e \<noteq> {new_vert}"
    if "e \<in> \<M> M" "e \<inter> set p = {}" for e
    using that assms(7,8) by (auto simp: Vs_def)
  have collapsed: "contr ` e = {new_vert}"
    if edge_in: "e \<in> \<M> M" and hit: "e \<inter> set p \<noteq> {}" for e
  proof-
    from edge_in obtain x y where edge: "e = {x, y}" "buddy_lookup M x = Some y"
      by (auto simp: \<M>_def')
    have "x \<in> set p" "y \<in> set p"
      using edge hit closed_iff[OF edge(2)] by auto
    then show ?thesis
      by (simp add: edge(1) assms(8))
  qed
  have surviving: "contr ` e = e \<and> e \<inter> set p = {}"
    if "e \<in> \<M> M" "contr ` e \<noteq> {new_vert}" for e
    using that unchanged[OF that(1)] collapsed[OF that(1)] by blast
  have quotient: "quot_graph contr (\<M> M) - {{new_vert}} = \<M> N"
  proof (rule equalityI)
    show "quot_graph contr (\<M> M) - {{new_vert}} \<subseteq> \<M> N"
      using surviving by (fastforce simp: quot_graph_def abs)
    show "\<M> N \<subseteq> quot_graph contr (\<M> M) - {{new_vert}}"
      using unchanged by (fastforce simp: quot_graph_def abs)
  qed
  show "\<M> N = quot_graph contr (\<M> M) - {{new_vert}}"
    by (rule quotient[symmetric])
  show "invar_matching (quot_graph contr G - {{new_vert}}) N"
  proof (rule invar_matchingI)
    show "buddy_invar N" by (rule cleared(1))
    show "symmetric_buddies N"
      using inv(2) closed_iff by (auto simp: symmetric_buddies_def cleared(2) split: if_splits)
    show "no_self_loop_buddy N"
      using inv(3) by (auto simp: no_self_loop_buddy_def cleared(2) split: if_splits)
    have sub: "\<M> N \<subseteq> \<M> M"
      by (simp add: abs)
    have "matching (\<M> N)"
      using inv(4) sub by (auto simp: matching_def)
    moreover have "\<M> N \<subseteq> quot_graph contr G - {{new_vert}}"
      using graph_subset_quot_subset[OF conjunct2[OF inv(4)], of contr]
      by (simp only: quotient[symmetric]) blast
    ultimately show "graph_matching (quot_graph contr G - {{new_vert}}) (\<M> N)"
      by simp
    show "finite (\<M> N)"
      using inv(5) abs by simp
    have "Vs (quot_graph contr G) \<subseteq> K"
      using inv(6) assms(6,8) by (auto simp: Vs_quot_graph_is_img)
    then show "Vs (quot_graph contr G - {{new_vert}}) \<subseteq> K"
      using Vs_subset[of "quot_graph contr G - {{new_vert}}" "quot_graph contr G"] by blast
  qed
qed

lemma contract_path_correct:
  assumes "invar_matching G M" "alt_path (\<M> M) p" "odd (length p)" "distinct p"
    "new_vert \<notin> Vs (\<M> M) - set p" "set p \<subseteq> K" "new_vert \<in> K"
    "contr = (\<lambda>x. if x \<in> set p then new_vert else x)"
  shows "invar_matching (quot_graph contr G - {{new_vert}}) (contract_path M p new_vert)"
    "\<M> (contract_path M p new_vert) = quot_graph contr (\<M> M) - {{new_vert}}"
proof-
  have "invar_matching (quot_graph contr G - {{new_vert}}) (contract_path M p new_vert) \<and>
    \<M> (contract_path M p new_vert) = quot_graph contr (\<M> M) - {{new_vert}}"
  proof (cases "buddy_get M (hd p) = nil")
    case True
    then have "buddy_lookup M (hd p) = None"
      by (simp add: buddy_lookup_def)
    then show ?thesis
      using contract_path_at_free_correct[OF assms(1) _ assms(2,3,6,7,5,8)] True
      by (simp add: contract_path_def)
  next
    case False
    then have "hd p \<in> Vs (\<M> M)"
      using buddy_get_in_\<M>[of M "hd p"] by (auto simp: Vs_def)
    then show ?thesis
      using contract_path_at_matched_correct[OF assms(1) _ assms(2-)] False
      by (simp add: contract_path_def)
  qed
  then show "invar_matching (quot_graph contr G - {{new_vert}}) (contract_path M p new_vert)"
    "\<M> (contract_path M p new_vert) = quot_graph contr (\<M> M) - {{new_vert}}"
    by auto
qed


interpretation blossom_matching_spec_here:
  blossom_matching_spec
  where K = K and empty_matching = buddy_empty
  and matching_invar = invar_matching
  and augment =augment_impl
  and matching_abstract = \<M>
  and contract_path = contract_path
  and lookup_partner = buddy_lookup
  and expand_path_at_matched = expand_path_at_matched
  done

interpretation blossom_matching_here:
  blossom_matching
  where K = K and empty_matching = buddy_empty
  and matching_invar = invar_matching
  and augment =augment_impl
  and matching_abstract = \<M>
  and contract_path = contract_path
  and lookup_partner = buddy_lookup
  and expand_path_at_matched = expand_path_at_matched
  and get_partner = get_partner
  and add_alternatingly = add_alternatingly
proof(rule blossom_matching.intro, goal_cases)
  case (1 M G)
  then show ?case
    using invar_matchingD(4) by auto
next
  case (2 G)
  then show ?case
    by (simp add: empty_matching_props)
next
  case 3
  then show ?case
   by (simp add: empty_matching_props)
next
  case (4 M G G')
  thus ?case
    using extend_graph by blast
next
  case (5 M G x)
  thus ?case
    using get_partner_correct by blast
next
  case (6 G M p)
  then show ?case
    by (simp add: augmentation_correct(1))
next
  case (7 G M p)
  then show ?case
    by (simp add: augmentation_correct(2))
next
  case (8 G M p new_vert contr)
  then show ?case
    by(elim blossom_matching_spec_here.contract_path_precondE,
       intro contract_path_correct)
next
  case (9 G M p new_vert contr)
  then show ?case
  by(elim blossom_matching_spec_here.contract_path_precondE,
       intro contract_path_correct)
next
  case (10 G M old_vert mo new_vert p)
  thus ?case
    by(elim blossom_matching_spec_here.expand_path_at_matched_precondE,
       intro expand_path_at_matched_correct)
       auto
next
  case (11 G M old_vert mo new_vert p)
  thus ?case
    by(elim blossom_matching_spec_here.expand_path_at_matched_precondE,
       intro expand_path_at_matched_correct)
       auto
next
  case (12 G M p)
  thus ?case
    by(elim blossom_matching_spec_here.add_alternatingly_precondE,
       intro add_alternatingly_correct)
       auto
next
  case (13 G M p)
  thus ?case
    by(elim blossom_matching_spec_here.add_alternatingly_precondE,
       intro add_alternatingly_correct)
       auto
next
  case (14 G M x y)
  then show ?case
    by (auto simp: \<M>_def' doubleton_eq_iff
             dest: symmetric_buddiesD[OF invar_matchingD(2)])
qed

lemmas blossom_matching_spec_satisfied = blossom_matching_here.blossom_matching_axioms

end

thm matching_augmentation.blossom_matching_spec_satisfied
end