theory Blossom_Algo_Compute_Aug_Path
  imports Blossom_Algo_Contraction
begin

subsection \<open>Computing a Blossom or an Augmenting Path\<close>

definition compute_alt_path_spec where 
  "compute_alt_path_spec G M compute_alt_path =
   (
    (\<forall>p1 p2 pref1 x post1 pref2 post2. compute_alt_path = Some (p1, p2) \<longrightarrow>
        p1 = pref1 @ x # post1 \<and> p2 = pref2 @ x # post2 \<longrightarrow>
           post1 = post2) \<and>
    (\<forall>p1 p2. compute_alt_path = Some (p1, p2) \<longrightarrow>
         alt_path M (hd p1 # p2)) \<and>
    (\<forall>p1 p2. compute_alt_path = Some (p1, p2) \<longrightarrow>
         alt_path M (hd p2 # p1)) \<and>
    (\<forall>p1 p2. compute_alt_path = Some (p1, p2) \<longrightarrow> 
         last p1 \<notin> Vs M) \<and>
    (\<forall>p1 p2. compute_alt_path = Some (p1, p2) \<longrightarrow> 
         last p2 \<notin> Vs M) \<and>
   (\<forall>p1 p2. compute_alt_path = Some (p1, p2) \<longrightarrow>
         hd p1 \<noteq> hd p2) \<and>
   (\<forall>p1 p2. compute_alt_path = Some (p1, p2) \<longrightarrow>
         odd (length p1)) \<and>
   (\<forall>p1 p2. compute_alt_path = Some (p1, p2) \<longrightarrow>
         odd (length p2)) \<and>
   (\<forall>p1 p2. compute_alt_path = Some (p1, p2) \<longrightarrow>
         distinct p1) \<and>
   (\<forall>p1 p2. compute_alt_path = Some (p1, p2) \<longrightarrow>
        distinct p2) \<and>
   (\<forall>p1 p2. compute_alt_path = Some (p1, p2) \<longrightarrow> path G p1) \<and>
   (\<forall>p1 p2. compute_alt_path =  Some(p1, p2) \<longrightarrow> path G p2) \<and>
   (\<forall>p1 p2. compute_alt_path = Some (p1, p2) \<longrightarrow> {hd p1, hd p2} \<in> G))"

locale compute_match_blossom' = match G M + choose sel
   for sel::"'a set \<Rightarrow> 'a" and G M ::"'a set set" +

fixes compute_alt_path:: "(('a list \<times> 'a list) option)"

begin

abbreviation "compute_alt_path_spec' \<equiv> compute_alt_path_spec G M compute_alt_path"

lemma compute_alt_path_spec_works_2:
  assumes from_tree:
    "\<And>G M p1 p2 pref1 x post1 pref2 post2. compute_alt_path = Some (p1, p2) \<Longrightarrow>
        p1 = pref1 @ x # post1 \<and> p2 = pref2 @ x # post2 \<Longrightarrow>
           post1 = post2" and
    alt_paths:
    "\<And>G M p1 p2. compute_alt_path = Some (p1, p2) \<Longrightarrow>
         alt_path M (hd p1 # p2)"
    "\<And>G M p1 p2. compute_alt_path = Some (p1, p2) \<Longrightarrow>
         alt_path M (hd p2 # p1)"
    "\<And>G M p1 p2. compute_alt_path = Some (p1, p2) \<Longrightarrow> 
         last p1 \<notin> Vs M"
    "\<And>G M p1 p2. compute_alt_path = Some (p1, p2) \<Longrightarrow> 
         last p2 \<notin> Vs M" and
    hds_neq: 
    "\<And>G M p1 p2. compute_alt_path = Some (p1, p2) \<Longrightarrow>
         hd p1 \<noteq> hd p2" and
    even_lens:
    "\<And>G M p1 p2. compute_alt_path = Some (p1, p2) \<Longrightarrow>
         odd (length p1)"
    "\<And>G M p1 p2. compute_alt_path = Some (p1, p2) \<Longrightarrow>
         odd (length p2)" and
    distinct:
    "\<And>G M p1 p2. compute_alt_path = Some (p1, p2) \<Longrightarrow>
         distinct p1"
    "\<And>G M p1 p2. compute_alt_path = Some (p1, p2) \<Longrightarrow>
        distinct p2" and
    paths:
    "\<And>G M p1 p2. compute_alt_path = Some (p1, p2) \<Longrightarrow> path G p1"
    "\<And>G M p1 p2. Some(p1, p2) = compute_alt_path \<Longrightarrow> path G p2"
    "\<And>G M p1 p2. compute_alt_path = Some (p1, p2) \<Longrightarrow> {hd p1, hd p2} \<in> G"
  shows "compute_alt_path_spec'"
  using assms
  unfolding compute_alt_path_spec_def
  apply(intro conjI allI)
  by metis+

context 
assumes 
(*soundness of compute_alt_path*)
compute_alt_path_spec:
"compute_alt_path_spec'" and
(*completeness of compute_alt_path*)
compute_alt_path_complete:
"(((\<exists>p. path G p \<and> distinct p \<and> matching_augmenting_path M p)))
         \<Longrightarrow> (\<exists>blos_comp. compute_alt_path = Some blos_comp)"
begin

lemma shows 
  from_tree:
  "compute_alt_path = Some (p1, p2) \<Longrightarrow>
        p1 = pref1 @ x # post1 \<and> p2 = pref2 @ x # post2 \<Longrightarrow>
           post1 = post2" and
  alt_paths:
  "compute_alt_path = Some (p1, p2) \<Longrightarrow>
         alt_path M (hd p1 # p2)"
  "compute_alt_path = Some (p1, p2) \<Longrightarrow>
         alt_path M (hd p2 # p1)"
  "compute_alt_path = Some (p1, p2) \<Longrightarrow> 
         last p1 \<notin> Vs M"
  "compute_alt_path = Some (p1, p2) \<Longrightarrow> 
         last p2 \<notin> Vs M" and
  hds_neq: 
  "compute_alt_path = Some (p1, p2) \<Longrightarrow>
         hd p1 \<noteq> hd p2" and
  even_lens:
  "compute_alt_path = Some (p1, p2) \<Longrightarrow>
         odd (length p1)"
  "compute_alt_path = Some (p1, p2) \<Longrightarrow>
         odd (length p2)" and
  distinct:
  "compute_alt_path = Some (p1, p2) \<Longrightarrow>
         distinct p1"
  "compute_alt_path = Some (p1, p2) \<Longrightarrow>
        distinct p2" and
  paths:
  "compute_alt_path = Some (p1, p2) \<Longrightarrow> path G p1"
  "compute_alt_path = Some(p1, p2) \<Longrightarrow> path G p2"
  "compute_alt_path = Some (p1, p2) \<Longrightarrow> {hd p1, hd p2} \<in> G"
  using compute_alt_path_spec
  unfolding compute_alt_path_spec_def
  by metis+


lemmas compute_alt_path_spec' = from_tree alt_paths hds_neq even_lens distinct paths

lemma compute_alt_path_res_from_tree:
  assumes compute_alt_path_res: "Some (p1, p2) = compute_alt_path" and
    pfxs_are_pfxs: "(Some pfx1, Some pfx2) = longest_disj_pfx p1 p2"
  shows "\<exists>p. p1 = pfx1 @ p \<and> p2 = pfx2 @ p"
proof-
  obtain post1 post2 where "p1 = pfx1 @ post1" "p2 = pfx2 @ post2"
    using disj_pref_append1 disj_pref_append2 pfxs_are_pfxs
    by metis
  moreover have "pfx1 = (butlast pfx1) @ [last pfx1]"
    "pfx2 = (butlast pfx2) @ [last pfx2]"
    using first_pfx_nempty snd_pfx_nempty pfxs_are_pfxs by force+
  moreover have "last pfx1 = last pfx2"
    using pfx_common_end pfxs_are_pfxs by fastforce
  ultimately show ?thesis
    using compute_alt_path_res from_tree
    by (metis (no_types, lifting) append.assoc append_Cons)
qed

lemma compute_alt_path_res_neq_lasts:
  assumes compute_alt_path_res: "Some (p1, p2) = compute_alt_path" and
    lasts_neq: "last p1 \<noteq> last p2"
  shows "set p1 \<inter> set p2 = {}"
  using compute_alt_path_res from_tree lasts_neq
  by (metis Int_emptyI last_appendR list.simps(3) split_list)

end

end

lemma match_blossom_path_rev_stem:
  assumes 
    path: "path G (stem @ C)" and
    match_blossom: "match_blossom M stem C"
  shows "path G (C @ (rev stem))"
  apply(cases stem)
  subgoal using path by simp
  subgoal apply(rule path_append)
    subgoal using path_suff[OF path] .
    subgoal using rev_path_is_path[OF path_pref[OF path]] .
    subgoal by (smt match_blossom match_blossomD(3) edge_between_pref_suff hd_rev insert_commute
                    list.simps(3) odd_cycleD(3) odd_cycle_nempty path)
    done
  done


context compute_match_blossom'
begin

abbreviation "unmatched_edges \<equiv> {{v1,v2} | v1 v2. {v1, v2} \<in> G \<and> v1 \<notin> Vs M \<and> v2 \<notin> Vs M}"

definition "sel_unmatched = (let (v1,v2) = sel_pair (graph_abs.D unmatched_edges) in [v1, v2])"

definition compute_match_blossom where
  "compute_match_blossom = 
   (if (\<exists>e. e \<in> unmatched_edges) then
         let singleton_path = sel_unmatched in
           Some (Path singleton_path)
    else
     case compute_alt_path
       of Some (p1,p2) \<Rightarrow> 
         (if (set p1 \<inter> set p2 = {}) then
            Some (Path ((rev p1) @ p2))
          else
            (let (pfx1, pfx2) = longest_disj_pfx p1 p2 in
              (Some (Blossom (rev (drop (length (the pfx1)) p1)) (rev (the pfx1) @ (the pfx2))))))
       | _ \<Rightarrow> None)"

lemma unmatched_edges_subset_G: "unmatched_edges \<subseteq> G"
  by auto

lemma sel_unmatched_spec: "e \<in> unmatched_edges \<Longrightarrow> \<exists>v1 v2. (sel_unmatched) = [v1, v2] \<and> {v1,v2} \<in> unmatched_edges"
  using unmatched_edges_subset_G graph
  apply(auto simp: sel_unmatched_def split: prod.split)
  by (smt (z3) empty_iff finite_vertices_iff graph_abs.Vs_eq_dVs graph_abs.edge_iff_edge_1
               graph_abs.intro graph_invar_subset mem_Collect_eq sel_pair)

lemma sel_unmatched_spec': assumes "e \<in> unmatched_edges"
  obtains v1 v2 where "(sel_unmatched) = [v1, v2]" "{v1,v2} \<in> unmatched_edges"
  using assms sel_unmatched_spec
  by meson

end

(*We need another locale to interpret compute_match_blossom'. Unimplemented functions are added
  as locales. *)

locale compute_match_blossom'_use =
  g: graph_abs E +
  (*compute_match_blossom' G M compute_alt_path +*)
  choose sel +
  create_vert create_vert 
  for E::"'a set set " and sel create_vert:: "'a set \<Rightarrow> 'a" +
  fixes compute_alt_path::"'a set set \<Rightarrow> 'a set set \<Rightarrow> ('a list \<times> 'a list) option"
  assumes
   compute_alt_path_spec:
    "\<lbrakk>graph_invar G; matching M; M\<subseteq>G\<rbrakk> \<Longrightarrow> compute_alt_path_spec G M (compute_alt_path G M)" and
   compute_alt_path_complete:
    "\<lbrakk>graph_invar G; matching M; M\<subseteq>G\<rbrakk> \<Longrightarrow> (((\<exists>p. path G p \<and> distinct p \<and> matching_augmenting_path M p)))
         \<Longrightarrow> (\<exists>blos_comp. compute_alt_path G M = Some blos_comp)"

begin

interpretation find_aug_path_use_intrp: find_aug_path_use create_vert
                                        "\<lambda>G M. compute_match_blossom'.compute_match_blossom sel G M (compute_alt_path G M)"
proof(unfold_locales, goal_cases)
  case (1 G M)

  then interpret compute_match_blossom' sel G M "compute_alt_path G M"
    using compute_alt_path_spec compute_alt_path_complete
    apply unfold_locales
    by (auto simp: compute_alt_path_spec_def)

  have "\<exists>p1 p2. compute_alt_path G M = Some (p1, p2)"
    using compute_alt_path_complete 1
    by fastforce
  then show ?case
    by(auto simp: Let_def compute_match_blossom_def
               split: option.splits if_splits simp add: split_beta)
next
  case (2 G M p)
  then interpret compute_match_blossom' sel G M "compute_alt_path G M"
    using compute_alt_path_spec compute_alt_path_complete
    apply unfold_locales
    by (auto simp: compute_alt_path_spec_def)

  have "(\<exists>e. e \<in> unmatched_edges) \<or> (\<nexists>e. e \<in> unmatched_edges) \<and> (\<exists>p1 p2. compute_alt_path G M = Some (p1, p2) \<and> set p1 \<inter> set p2 = {})"
    using 2
    by(auto simp: Let_def compute_match_blossom_def
        split: option.splits if_splits simp add: split_beta)
  then consider (sing) "(\<exists>e. e \<in> unmatched_edges)" | 
                (aug_path) "(\<nexists>e. e \<in> unmatched_edges) \<and> 
                            (\<exists>p1 p2. compute_alt_path G M = Some (p1, p2) \<and>
                            set p1 \<inter> set p2 = {})"
    by force
  then show ?case
  proof cases
    case sing
    then have p_is_choice: "p = sel_unmatched"     
      using \<open>compute_match_blossom = Some (Path p)\<close>
      by(auto simp: compute_match_blossom_def)
    moreover obtain e where "e \<in> unmatched_edges"
      using sing
      by auto
    ultimately obtain va vb where vavb: "p = [va, vb]" "{va, vb} \<in> unmatched_edges"
      apply -
      apply(erule sel_unmatched_spec')
      by auto
    then show ?thesis            
      unfolding matching_augmenting_path_def
      using \<open>graph_invar G\<close>
      by (auto simp add: alt_list_step alt_list_empty Vs_def doubleton_eq_iff insert_commute)
  next
    case aug_path
    then obtain p1 p2 where p1p2: "(\<nexists>e. e \<in> unmatched_edges)" "compute_alt_path G M = Some (p1, p2)"
      "set p1 \<inter> set p2 = {}"
      by blast
    then have paths: "path G p1" "path G p2" "{hd p1, hd p2} \<in> G" 
      using paths compute_alt_path_spec compute_alt_path_complete 2
      by meson+
    then have "path G ((rev p1) @ p2)"
      by (simp add: construct_path)

    moreover have distincts: "distinct p1" "distinct p2" 
      using distinct p1p2 compute_alt_path_spec compute_alt_path_complete 2
      by meson+
    then have "distinct ((rev p1) @ p2)"
      using p1p2(3)
      by (simp add: construct_path)
    moreover have "compute_alt_path_spec'"
      using compute_alt_path_spec
      by (simp add: "2"(2) "2"(3) graph)
    hence distincts: "matching_augmenting_path M ((rev p1) @ p2)"
      apply(intro construct_aug_path'[OF p1p2(3)] iffD2[OF length_greater_0_conv[symmetric]] odd_pos
          compute_alt_path_spec'[OF _ _ p1p2(2)])
      by (simp add: p1p2(2))+
 
    moreover have "p =  ((rev p1) @ p2)"
      using p1p2(1,2) \<open>compute_match_blossom = Some (Path p)\<close>[simplified compute_match_blossom_def]
      by(auto split: option.splits if_splits simp add: split_beta)
    ultimately show ?thesis
      by auto
  qed
next
  case (3 G M stem C)
  then interpret compute_match_blossom' sel G M "compute_alt_path G M"
    using compute_alt_path_spec compute_alt_path_complete
    apply unfold_locales
    by (auto simp: compute_alt_path_spec_def)

  obtain p1 p2 where p1p2: "compute_alt_path G M = Some (p1, p2)" "set p1 \<inter> set p2 \<noteq> {}"
    using 3
    by(fastforce simp: Let_def compute_match_blossom_def
        split: option.splits if_splits simp add: split_beta)
  moreover have "compute_alt_path_spec'"
      using compute_alt_path_spec
      by (simp add: "3"(2) "3"(3) graph)
    ultimately have paths: "path G p1" "path G p2" "{hd p1, hd p2} \<in> G" 
    using paths
    by auto
  let ?pfx1 = "the (fst (longest_disj_pfx p1 p2))"
  let ?pfx2 = "the (snd (longest_disj_pfx p1 p2))"
  obtain pfx1 pfx2 where pfx12: "(Some pfx1, Some pfx2) = (longest_disj_pfx p1 p2)" (is ?pfx12)
    using \<open>set p1 \<inter> set p2 \<noteq> {}\<close>
    by (metis disj_pfx_is_complete first_pfx_then_snd_pfx option.exhaust prod.collapse)
  then have p1: "path G (rev (drop (length pfx1) p1) @ rev (pfx1) @ pfx2)" (is ?p1)
    apply(intro pfxs_path[where ?p2.0 = p2] paths)
    by auto
  obtain p1' p2' where "p1 = pfx1 @ p1'" "p2 = pfx2 @ p2'"
    using disj_pref_append1 disj_pref_append2 pfx12 by blast
  moreover have "pfx1 = (butlast pfx1) @ [last pfx1]" "pfx2 = (butlast pfx2) @ [last pfx2]"
    using first_pfx_nempty snd_pfx_nempty pfx12 by force+
  moreover have "last pfx1 = last pfx2"
    using pfx12 pfx_common_end by fastforce
  ultimately have "p1' = p2'"
    using compute_alt_path_res_from_tree[OF \<open>compute_alt_path_spec'\<close>] p1p2(1) pfx12
    by force

  have p2: "match_blossom M (rev (drop (length pfx1) p1)) (rev pfx1 @ pfx2)" if "matching M" (is ?p2)
    apply (intro  common_pfxs_form_match_blossom' [where ?p2.0 = p2 and ?p = p1'] pfx12)
    using that p1p2 compute_alt_path_spec'[where ?p2.0 = p2 and ?p1.0 = p1, OF \<open>compute_alt_path_spec'\<close>]
    using \<open>p1 = pfx1 @ p1'\<close> \<open>p2 = pfx2 @ p2'\<close> \<open>p1' = p2'\<close>
    by metis+

  have "stem = (rev (drop (length (pfx1)) p1))" "C = (rev (pfx1) @ (pfx2))"
    using \<open>compute_match_blossom = Some (Blossom stem C)\<close>[simplified compute_match_blossom_def] p1p2 pfx12
     apply(auto simp: Let_def split_beta split: option.splits if_splits)
    by (metis fstI sndI option.sel)+
  then have "path G (stem @ C) \<and> (matching M \<longrightarrow> match_blossom M stem C)"
    using p1 p2
    by auto
  then show ?case
    using \<open>matching M\<close>
    by auto
qed

lemmas find_max_matching_works = find_aug_path_use_intrp.find_max_matching_works 

end

end