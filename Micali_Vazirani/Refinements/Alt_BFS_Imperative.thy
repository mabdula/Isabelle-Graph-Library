theory Alt_BFS_Imperative
  imports Micali_Vazirani.Alt_BFS_Dist "HOL-Imperative_HOL.Imperative_HOL" Imperative.Array_Range_Iteration
begin

section \<open>Imperative Refinement of the Alternating BFS\<close>

text \<open>The imperative program mirrors the distance BFS of @{theory Micali_Vazirani.Alt_BFS_Dist}.
      Its operations are parameters; their Hoare triples, stated against the functional
      operations, are the assumptions of the refinement locale.\<close>

record ('imp_cf, 'imp_vis, 'imp_dist) Alt_BFS_state_imp =
  i_frontier :: 'imp_cf
  i_vis_even :: 'imp_vis
  i_vis_odd :: 'imp_vis
  i_dists :: 'imp_dist
  i_level :: nat

locale Alt_BFS_Imperative_spec =
  fixes imp_cf_is_empty :: "'imp_cf \<Rightarrow> bool Heap"
    and next_frontier_and_visited_imp :: "'imp_G \<Rightarrow> 'imp_cf \<Rightarrow> 'imp_vis \<Rightarrow> ('imp_cf \<times> 'imp_vis) Heap"
    and set_all_dists_imp :: "'imp_dist \<Rightarrow> parity \<Rightarrow> 'imp_cf \<Rightarrow> nat \<Rightarrow> 'imp_dist Heap"
    and imp_src_to_cf :: "'imp_src \<Rightarrow> 'imp_cf Heap"
    and set_srcs_visited :: "'imp_vis \<Rightarrow> 'imp_src \<Rightarrow> 'imp_vis Heap"
    and matching_imp unmatching_imp :: 'imp_G
begin

partial_function (heap) Alt_BFS_imp ::
  "('imp_cf, 'imp_vis, 'imp_dist) Alt_BFS_state_imp \<Rightarrow> ('imp_cf, 'imp_vis, 'imp_dist) Alt_BFS_state_imp Heap"
  where
  "Alt_BFS_imp s =
     do { b \<leftarrow> imp_cf_is_empty (i_frontier s);
          if b then return s
          else do { (F', VO') \<leftarrow> next_frontier_and_visited_imp unmatching_imp (i_frontier s) (i_vis_odd s);
                    D' \<leftarrow> set_all_dists_imp (i_dists s) Odd F' (Suc (i_level s));
                    (F'', VE') \<leftarrow> next_frontier_and_visited_imp matching_imp F' (i_vis_even s);
                    D'' \<leftarrow> set_all_dists_imp D' Even F'' (Suc (Suc (i_level s)));
                    Alt_BFS_imp (s\<lparr>i_frontier := F'', i_vis_even := VE', i_vis_odd := VO',
                                   i_dists := D'', i_level := Suc (Suc (i_level s))\<rparr>) } }"

definition "initial_state_imp empty_vis_even empty_vis_odd src_imp some_dist_imp =
  do { VE \<leftarrow> set_srcs_visited empty_vis_even src_imp;
       F \<leftarrow> imp_src_to_cf src_imp;
       D \<leftarrow> set_all_dists_imp some_dist_imp Even F 0;
       return \<lparr>i_frontier = F, i_vis_even = VE, i_vis_odd = empty_vis_odd, i_dists = D, i_level = 0\<rparr> }"

definition "Alt_BFS_run_imp empty_vis_even empty_vis_odd src_imp some_dist_imp =
  do { s \<leftarrow> initial_state_imp empty_vis_even empty_vis_odd src_imp some_dist_imp;
       Alt_BFS_imp s }"

end

locale Alt_BFS_Imperative =
  Alt_BFS_distance where lookup_neighb = lookup_neighb and lookup_dist = lookup_dist
    and next_frontier_and_visited = next_frontier_and_visited and set_all_dists = set_all_dists +
  Alt_BFS_Imperative_spec where next_frontier_and_visited_imp = next_frontier_and_visited_imp
    and set_all_dists_imp = set_all_dists_imp and imp_cf_is_empty = imp_cf_is_empty
    and imp_src_to_cf = imp_src_to_cf and set_srcs_visited = set_srcs_visited
  for lookup_neighb :: "'adjmap \<Rightarrow> 'ver \<Rightarrow> 'vset option"
  and lookup_dist :: "'dmap \<Rightarrow> 'ver labelled_vtx \<Rightarrow> enat option"
  and next_frontier_and_visited :: "'adjmap \<Rightarrow> 'vset \<Rightarrow> 'vset \<Rightarrow> 'vset \<times> 'vset"
  and set_all_dists :: "'dist \<Rightarrow> parity \<Rightarrow> 'vset \<Rightarrow> nat \<Rightarrow> 'dist"
  and next_frontier_and_visited_imp :: "'imp_G \<Rightarrow> 'imp_cf \<Rightarrow> 'imp_vis \<Rightarrow> ('imp_cf \<times> 'imp_vis) Heap"
  and set_all_dists_imp :: "'imp_dist \<Rightarrow> parity \<Rightarrow> 'imp_cf \<Rightarrow> nat \<Rightarrow> 'imp_dist Heap"
  and imp_cf_is_empty :: "'imp_cf \<Rightarrow> bool Heap"
  and imp_src_to_cf :: "'imp_src \<Rightarrow> 'imp_cf Heap"
  and set_srcs_visited :: "'imp_vis \<Rightarrow> 'imp_src \<Rightarrow> 'imp_vis Heap" +
  fixes graph_assn :: "'adjmap \<Rightarrow> 'imp_G \<Rightarrow> assn"
    and imp_src_assn :: "'vset \<Rightarrow> 'imp_src \<Rightarrow> assn"
    and imp_cf_assn :: "'vset \<Rightarrow> 'imp_cf \<Rightarrow> assn"
    and imp_vis_assn :: "'vset \<Rightarrow> 'imp_vis \<Rightarrow> assn"
    and imp_dist_assn :: "'dist \<Rightarrow> 'imp_dist \<Rightarrow> assn"
  assumes imp_cf_is_empty_rule:
      "\<And>S Si. <imp_cf_assn S Si> imp_cf_is_empty Si <\<lambda>b. imp_cf_assn S Si * \<up>(b \<longleftrightarrow> S = \<emptyset>\<^sub>N)>"
    and next_frontier_and_visited_imp_rule:
      "\<And>H Hi F Fi V Vi. \<lbrakk>vset_inv F; vset_inv V; Graph.graph_inv H; Graph.digraph_abs H \<subseteq> G;
          t_set F \<subseteq> dVs G; t_set V \<subseteq> dVs G\<rbrakk> \<Longrightarrow>
       <imp_cf_assn F Fi * imp_vis_assn V Vi * graph_assn H Hi>
         next_frontier_and_visited_imp Hi Fi Vi
       <\<lambda>(Fi', Vi'). imp_cf_assn (fst (next_frontier_and_visited H F V)) Fi' *
                     imp_vis_assn (snd (next_frontier_and_visited H F V)) Vi' * graph_assn H Hi>"
    and set_all_dists_imp_rule:
      "\<And>d di p F Fi n. \<lbrakk>vset_inv F; t_set F \<subseteq> dVs G\<rbrakk> \<Longrightarrow>
       <imp_dist_assn d di * imp_cf_assn F Fi> set_all_dists_imp di p Fi n
       <\<lambda>r. imp_dist_assn (set_all_dists d p F n) r * imp_cf_assn F Fi>"
    and imp_src_to_cf_rule:
      "\<And>S Si. <imp_src_assn S Si> imp_src_to_cf Si <\<lambda>r. imp_cf_assn S r>"
    and set_srcs_visited_rule:
      "\<And>S Si Vi. <imp_src_assn S Si * imp_vis_assn \<emptyset>\<^sub>N Vi> set_srcs_visited Vi Si
                 <\<lambda>r. imp_vis_assn S r * imp_src_assn S Si>"
begin

definition "dist_state_invar t =
  (vset_inv (d_frontier t) \<and> vset_inv (d_vis_even t) \<and> vset_inv (d_vis_odd t) \<and>
   t_set (d_frontier t) \<subseteq> dVs G \<and> t_set (d_vis_even t) \<subseteq> dVs G \<and> t_set (d_vis_odd t) \<subseteq> dVs G)"

definition "state_assn t ti =
  imp_cf_assn (d_frontier t) (i_frontier ti) * imp_vis_assn (d_vis_even t) (i_vis_even ti) *
  imp_vis_assn (d_vis_odd t) (i_vis_odd ti) * imp_dist_assn (d_dists t) (i_dists ti) *
  \<up>(d_level t = i_level ti \<and> dist_state_invar t)"

lemma dist_state_invar_upd:
  assumes "Graph.graph_inv matching" "Graph.graph_inv unmatching" "dist_state_invar t"
  obtains F' VO' F'' VE' where
    "next_frontier_and_visited unmatching (d_frontier t) (d_vis_odd t) = (F', VO')"
    "next_frontier_and_visited matching F' (d_vis_even t) = (F'', VE')"
    "vset_inv F'" "t_set F' \<subseteq> dVs G"
    "Alt_BFS_dist_upd t = t\<lparr>d_frontier := F'', d_vis_even := VE', d_vis_odd := VO',
        d_dists := set_all_dists (set_all_dists (d_dists t) Odd F' (Suc (d_level t)))
                     Even F'' (Suc (Suc (d_level t))),
        d_level := Suc (Suc (d_level t))\<rparr>"
    "dist_state_invar (Alt_BFS_dist_upd t)"
proof-
  obtain F' VO' where nf1: "next_frontier_and_visited unmatching (d_frontier t) (d_vis_odd t) = (F', VO')"
    by (cases "next_frontier_and_visited unmatching (d_frontier t) (d_vis_odd t)") auto
  obtain F'' VE' where nf2: "next_frontier_and_visited matching F' (d_vis_even t) = (F'', VE')"
    by (cases "next_frontier_and_visited matching F' (d_vis_even t)") auto
  have I: "vset_inv (d_frontier t)" "vset_inv (d_vis_even t)" "vset_inv (d_vis_odd t)"
          "t_set (d_frontier t) \<subseteq> dVs G" "t_set (d_vis_even t) \<subseteq> dVs G" "t_set (d_vis_odd t) \<subseteq> dVs G"
    using assms(3) by (simp_all add: dist_state_invar_def)
  note N1 = next_frontier_and_visited[OF I(1,3) assms(2) unmatching_matching_in_G(1) I(4,6) nf1]
  have F'_G: "t_set F' \<subseteq> dVs G"
    unfolding N1(2) by (rule subset_trans[OF next_frontier_dVs dVs_subset[OF unmatching_matching_in_G(1)]])
  note N2 = next_frontier_and_visited[OF N1(1) I(2) assms(1) unmatching_matching_in_G(2) F'_G I(5) nf2]
  have F''_G: "t_set F'' \<subseteq> dVs G"
    unfolding N2(2) by (rule subset_trans[OF next_frontier_dVs dVs_subset[OF unmatching_matching_in_G(2)]])
  have upd: "Alt_BFS_dist_upd t = t\<lparr>d_frontier := F'', d_vis_even := VE', d_vis_odd := VO',
        d_dists := set_all_dists (set_all_dists (d_dists t) Odd F' (Suc (d_level t)))
                     Even F'' (Suc (Suc (d_level t))),
        d_level := Suc (Suc (d_level t))\<rparr>"
    by (simp add: Alt_BFS_dist_upd_def nf1 nf2)
  have "dist_state_invar (Alt_BFS_dist_upd t)"
    using N1 N2 I F'_G F''_G by (auto simp: upd dist_state_invar_def)
  thus thesis
    using that[OF nf1 nf2 N1(1) F'_G upd] by blast
qed

lemma dist_state_invar_initial:
  "\<lbrakk>vset_inv srcs; t_set srcs \<subseteq> dVs G\<rbrakk> \<Longrightarrow> dist_state_invar initial_dist_state"
  by (simp add: dist_state_invar_def initial_dist_state_def Graph.vset.set.invar_empty
                Graph.vset.set.set_empty)

lemma Alt_BFS_refine:
  assumes "Graph.graph_inv matching" "Graph.graph_inv unmatching"
  shows "<graph_assn matching matching_imp * graph_assn unmatching unmatching_imp * state_assn t ti>
           Alt_BFS_imp ti
         <\<lambda>ti'. graph_assn matching matching_imp * graph_assn unmatching unmatching_imp *
                state_assn (Alt_BFS_dist_impl t) ti'>"
proof(induction arbitrary: t ti rule: Alt_BFS_imp.fixp_induct)
  case 1
  then show ?case
    by auto
next
  case 2
  then show ?case
    by simp
next
  case (3 f t ti)
  note IH = 3[of _ "\<lparr>i_frontier = Fi, i_vis_even = VEi, i_vis_odd = VOi, i_dists = Di, i_level = n\<rparr>"
              for Fi VEi VOi Di n]
  show ?case
  proof(cases ti, cases "d_frontier t = \<emptyset>\<^sub>N")
    case (fields Fi VEi VOi Di n)
    case True
    show ?thesis
      unfolding fields
      apply (subst Alt_BFS_dist_impl_simps(2)[OF True])
      by (sep_auto heap: imp_cf_is_empty_rule simp: state_assn_def True)
  next
    case (fields Fi VEi VOi Di n)
    case False
    show ?thesis
    proof(rule hoare_triple_preI, goal_cases)
      case (1 h)
      hence inv: "dist_state_invar t" and lvl: "d_level t = n"
        by (simp_all add: state_assn_def fields mult.assoc[symmetric] mod_pure_star_dist)      obtain F' VO' F'' VE' where
          nf1: "next_frontier_and_visited unmatching (d_frontier t) (d_vis_odd t) = (F', VO')" and
          nf2: "next_frontier_and_visited matching F' (d_vis_even t) = (F'', VE')" and
          F': "vset_inv F'" "t_set F' \<subseteq> dVs G" and
          upd: "Alt_BFS_dist_upd t = t\<lparr>d_frontier := F'', d_vis_even := VE', d_vis_odd := VO',
                  d_dists := set_all_dists (set_all_dists (d_dists t) Odd F' (Suc (d_level t)))
                               Even F'' (Suc (Suc (d_level t))),
                  d_level := Suc (Suc (d_level t))\<rparr>" and
          inv': "dist_state_invar (Alt_BFS_dist_upd t)"
        by (rule dist_state_invar_upd[OF assms inv])
      have I: "vset_inv (d_frontier t)" "vset_inv (d_vis_even t)" "vset_inv (d_vis_odd t)"
              "t_set (d_frontier t) \<subseteq> dVs G" "t_set (d_vis_even t) \<subseteq> dVs G" "t_set (d_vis_odd t) \<subseteq> dVs G"
        using inv by (simp_all add: dist_state_invar_def)
      have F'': "vset_inv F''" "t_set F'' \<subseteq> dVs G"
        using inv' by (simp_all add: dist_state_invar_def upd)
      have r1: "<imp_cf_assn (d_frontier t) Fi * imp_vis_assn (d_vis_odd t) VOi *
                 graph_assn unmatching unmatching_imp>
                  next_frontier_and_visited_imp unmatching_imp Fi VOi
                <\<lambda>(a, b). imp_cf_assn F' a * imp_vis_assn VO' b * graph_assn unmatching unmatching_imp>"
        using next_frontier_and_visited_imp_rule[OF I(1,3) assms(2) unmatching_matching_in_G(1) I(4,6)]
        by (simp add: nf1)
      have r3: "<imp_cf_assn F' Fi' * imp_vis_assn (d_vis_even t) VEi * graph_assn matching matching_imp>
                  next_frontier_and_visited_imp matching_imp Fi' VEi
                <\<lambda>(a, b). imp_cf_assn F'' a * imp_vis_assn VE' b * graph_assn matching matching_imp>"
        for Fi'
        using next_frontier_and_visited_imp_rule[OF F'(1) I(2) assms(1) unmatching_matching_in_G(2) F'(2) I(5)]
        by (simp add: nf2)
      note r2 = set_all_dists_imp_rule[OF F'] and r4 = set_all_dists_imp_rule[OF F'']
      have IH': "<graph_assn matching matching_imp * graph_assn unmatching unmatching_imp *
                  (imp_cf_assn F'' Fi'' * imp_vis_assn VE' VEi' * imp_vis_assn VO' VOi' *
                   imp_dist_assn (set_all_dists (set_all_dists (d_dists t) Odd F' (Suc n)) Even F''
                                    (Suc (Suc n))) Di')>
                   f \<lparr>i_frontier = Fi'', i_vis_even = VEi', i_vis_odd = VOi', i_dists = Di',
                      i_level = Suc (Suc n)\<rparr>
                 <\<lambda>ti'. graph_assn matching matching_imp * graph_assn unmatching unmatching_imp *
                       state_assn (Alt_BFS_dist_impl t) ti'>"
        for Fi'' VEi' VOi' Di'
        using IH(1)[of "Alt_BFS_dist_upd t" Fi'' VEi' VOi' Di' "Suc (Suc n)"] inv'
        unfolding Alt_BFS_dist_impl_simps(1)[OF False, symmetric]
        by (simp add: state_assn_def upd lvl)
      show ?case
        unfolding fields state_assn_def[of t]
        by (sep_auto heap: imp_cf_is_empty_rule r1 r2 r3 r4 IH' simp: False lvl)    qed
  qed
qed

lemma initial_refine:
  assumes "vset_inv srcs" "t_set srcs \<subseteq> dVs G"
  shows "<imp_vis_assn \<emptyset>\<^sub>N VEi * imp_vis_assn \<emptyset>\<^sub>N VOi * imp_src_assn srcs Si * imp_dist_assn some_dist Di>
           initial_state_imp VEi VOi Si Di
         <\<lambda>ti. state_assn initial_dist_state ti>"
  unfolding initial_state_imp_def
  by (sep_auto heap: set_srcs_visited_rule imp_src_to_cf_rule set_all_dists_imp_rule[OF assms]
                simp: state_assn_def initial_dist_state_def dist_state_invar_initial[OF assms, unfolded initial_dist_state_def])

text \<open>The imperative alternating BFS refines the distance BFS, whose result is characterised by
      @{thm [source] Alt_BFS_dist_correct}.\<close>

theorem Alt_BFS_run_imp_rule:
  assumes BFS_axiom
  shows "<graph_assn matching matching_imp * graph_assn unmatching unmatching_imp *
          imp_vis_assn \<emptyset>\<^sub>N VEi * imp_vis_assn \<emptyset>\<^sub>N VOi * imp_src_assn srcs Si * imp_dist_assn some_dist Di>
           Alt_BFS_run_imp VEi VOi Si Di
         <\<lambda>ti. graph_assn matching matching_imp * graph_assn unmatching unmatching_imp *
               state_assn (Alt_BFS_dist_impl initial_dist_state) ti>"
  unfolding Alt_BFS_run_imp_def
  using graph_inv[OF assms]
  by (sep_auto heap: initial_refine[OF srcs_props[OF assms]] Alt_BFS_refine)

theorem Alt_BFS_run_imp_correct:
  assumes BFS_axiom
  shows "<graph_assn matching matching_imp * graph_assn unmatching unmatching_imp *
          imp_vis_assn \<emptyset>\<^sub>N VEi * imp_vis_assn \<emptyset>\<^sub>N VOi * imp_src_assn srcs Si * imp_dist_assn some_dist Di>
           Alt_BFS_run_imp VEi VOi Si Di
         <\<lambda>ti. \<exists>\<^sub>A F VE VO D. graph_assn matching matching_imp * graph_assn unmatching unmatching_imp *
               imp_cf_assn F (i_frontier ti) * imp_vis_assn VE (i_vis_even ti) *
               imp_vis_assn VO (i_vis_odd ti) * imp_dist_assn D (i_dists ti) *
               \<up>(vset_inv VE \<and> vset_inv VO \<and>
                 t_set VE = t_set (visited_even (BFS initial_state)) \<and>
                 t_set VO = t_set (visited_odd (BFS initial_state)) \<and>
                 (\<forall>v \<in> t_set VE. enat (dist_lookup D (Vtx Even v)) = altd_G Even v) \<and>
                 (\<forall>v \<in> t_set VO. enat (dist_lookup D (Vtx Odd v)) = altd_G Odd v) \<and>
                 Graph.digraph_abs (parents (BFS initial_state)) =
                   dist_dag (t_set VE) (t_set VO) (dist_lookup D))>"
  using Alt_BFS_dist_correct[OF assms]
  by (sep_auto heap: Alt_BFS_run_imp_rule[OF assms] simp: state_assn_def)

end

end
