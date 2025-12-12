theory Blossom_Algo_Main_Loop
  imports "Berge_Lemma.Berge" Misc
begin

subsection\<open>The main loop of a maximum matching algorithm that is based on Berge's lemma\<close>

locale find_max_match = graph_abs G for G +
  fixes aug_path_search::"'a set set \<Rightarrow> 'a set set \<Rightarrow> ('a list) option" 
  assumes
    aug_path_search_complete: 
    "\<lbrakk>matching M; M \<subseteq> G; finite M; (\<exists>p. graph_augmenting_path G M p)\<rbrakk>
     \<Longrightarrow> (\<exists>p. aug_path_search G M = Some p)" and
    aug_path_search_sound:
    "\<lbrakk>matching M; M \<subseteq> G; finite M; aug_path_search G M = Some p\<rbrakk>
     \<Longrightarrow> graph_augmenting_path G M p"
begin

text\<open>A measure function to prove termination\<close>

definition find_max_matching_meas where
  "find_max_matching_meas M = (card (G - M))"

lemma finite_G:
  shows "finite G"
  using finite_UnionD graph
  unfolding Vs_def
  by auto

lemma find_max_matching_meas_decreases:
  assumes "M \<subseteq> G" "M' \<subseteq> G" "card M < card M'"
  shows "find_max_matching_meas M' < find_max_matching_meas M"
  unfolding find_max_matching_meas_def
  using finite_G graph assms
proof(induction G arbitrary: M M')
  case empty
  then show ?case by auto
next
  case (insert x F)
  then show ?case
    by (metis card_Diff_subset card_mono diff_less_mono2 finite.insertI infinite_super leD psubsetI psubset_card_mono)
qed


text\<open>The main algorithm: parameterised by @{term aug_path_search}, which is a function that should be 
     able to return an augmenting path if one exists. It returns an @{term alt_list} optional path.\<close>

(* TODO if \<rightarrow> case *)
function (domintros) find_max_matching where
  "find_max_matching M = 
     (if (\<exists>p. aug_path_search G M = Some p) then
        (find_max_matching (M \<oplus> (set (edges_of_path (the (aug_path_search G M))))))
      else M)"
  by pat_completeness auto

lemma find_max_matching_dom:
  assumes "matching M"" M \<subseteq> G"" finite M"
  shows "find_max_matching_dom M"
proof-

  have base: "find_max_matching_dom M" if "\<forall>p. aug_path_search G M \<noteq> Some p" for M
    using that
    by (metis find_max_matching.domintros)

  have step: "\<And>M. find_max_matching_dom (M \<oplus> (set (edges_of_path (the (aug_path_search G M)))))
                   \<Longrightarrow> find_max_matching_dom M"
    by (rule find_max_matching.domintros) simp

  from assms show ?thesis
  proof(induction "find_max_matching_meas M" arbitrary: M rule: nat_less_induct)
    case 1
    show ?case
    proof(cases "\<exists>p. matching_augmenting_path M p \<and> path G p \<and> distinct p")
      case True
      then obtain p where p: "aug_path_search G M = Some p"
        using aug_path_search_complete 1(2-4)
        by blast
      then have aug_path: "path G p" "distinct p" "matching_augmenting_path M p"
        using aug_path_search_sound 1(2-4)
        by blast+
      have "matching (M \<oplus> set (edges_of_path p))"
        "M \<oplus> set (edges_of_path p) \<subseteq> G"
        "card M < card (M \<oplus> set (edges_of_path p))"
        using Berge_2[OF aug_path(3) 1(3) aug_path(1,2) 1(4,2)]
        by simp+
      moreover have "finite (M \<oplus> set (edges_of_path p))"
        by (simp add: finite_symm_diff 1)
      moreover have "find_max_matching_meas (M \<oplus> set (edges_of_path p)) < find_max_matching_meas M"
        apply(rule find_max_matching_meas_decreases)
        subgoal using 1(3) .
        subgoal using \<open>M \<oplus> set (edges_of_path p) \<subseteq> G\<close> .
        subgoal using \<open>card M < card (M \<oplus> set (edges_of_path p))\<close> .
        done
      ultimately have "find_max_matching_dom (M \<oplus> set (edges_of_path (the (aug_path_search G M))))"
        using True p 1 by auto
      then show ?thesis
        using local.step by blast
    next
      case False
      then have "aug_path_search G M = None"
        using aug_path_search_sound 1(2-4)
        by (meson not_Some_eq)
      then show ?thesis
        using base
        by auto
    qed
  qed
qed

lemma find_max_matching_is_matching:
  assumes matching: "matching M"" M \<subseteq> G"" finite M"
  shows "matching (find_max_matching M)" (is ?g1)
proof-
  have "find_max_matching_dom M"
    using assms
    by (simp add: find_max_matching_dom)
  then show ?g1
    using assms
  proof (induction rule: find_max_matching.pinduct)
    case one_M_whatevs: (1 M)
    show ?case
    proof(cases "\<exists>p. aug_path_search G M = Some p")
      case True
      then obtain p where p: "aug_path_search G M = Some p"
        by auto
      then have aug_path: "path G p" "distinct p" "matching_augmenting_path M p"
        using aug_path_search_sound one_M_whatevs(3-5)
        by blast+
      have "matching (M \<oplus> set (edges_of_path p))"
        "M \<oplus> set (edges_of_path p) \<subseteq> G"
        using Berge_2[OF aug_path(3) one_M_whatevs(4) aug_path(1,2) one_M_whatevs(5) one_M_whatevs(3)]
        by simp+
      moreover have "finite (M \<oplus> set (edges_of_path p))"
        by (simp add: finite_symm_diff one_M_whatevs.prems(3))
      ultimately have "matching (find_max_matching (M \<oplus> set (edges_of_path (the (aug_path_search G M)))))"
        apply(intro one_M_whatevs)
        using True p by auto
      then show ?thesis
        using \<open>find_max_matching_dom M\<close> True
        by(simp add: find_max_matching.psimps)
    next
      case False
      then have "(find_max_matching M) = M"
        by (simp add: find_max_matching.psimps one_M_whatevs.hyps)
      then show ?thesis
        using one_M_whatevs(3)
        by simp
    qed
  qed
qed

lemma find_max_matching_is_finite:
  assumes matching: "matching M"" M \<subseteq> G"" finite M"
  shows "finite (find_max_matching M)"
proof-
  have "find_max_matching_dom M"
    using assms
    by (simp add: find_max_matching_dom)
  then show ?thesis
    using assms
  proof (induction rule: find_max_matching.pinduct)
    case one_M_whatevs: (1 M)
    show ?case
    proof(cases "\<exists>p. aug_path_search G M = Some p")
      case True
      then obtain p where p: "aug_path_search G M = Some p"
        by auto
      then have aug_path: "path G p" "distinct p" "matching_augmenting_path M p"
        using aug_path_search_sound one_M_whatevs(3-5)
        by blast+
      have "matching (M \<oplus> set (edges_of_path p))"
        "M \<oplus> set (edges_of_path p) \<subseteq> G"
        using Berge_2[OF aug_path(3) one_M_whatevs(4) aug_path(1,2) one_M_whatevs(5) one_M_whatevs(3)]
        by simp+
      moreover have "finite (M \<oplus> set (edges_of_path p))"
        by (simp add: finite_symm_diff one_M_whatevs.prems(3))
      ultimately have "finite (find_max_matching (M \<oplus> set (edges_of_path (the (aug_path_search G M)))))"
        apply(intro one_M_whatevs)
        using True p by auto
      then show ?thesis
        using \<open>find_max_matching_dom M\<close> True
        by(simp add: find_max_matching.psimps)
    next
      case False
      then have "(find_max_matching M) = M"
        by (simp add: find_max_matching.psimps one_M_whatevs.hyps)
      then show ?thesis
        using one_M_whatevs
        by simp
    qed
  qed
qed

lemma find_max_matching_is_subset:
  assumes matching: "matching M"" M \<subseteq> G"" finite M"
  shows "find_max_matching M \<subseteq> G"
proof-
  have "find_max_matching_dom M"
    using assms
    by (simp add: find_max_matching_dom)
  then show ?thesis
    using assms
  proof (induction rule: find_max_matching.pinduct)
    case one_M_whatevs: (1 M)
    show ?case
    proof(cases "\<exists>p. aug_path_search G M = Some p")
      case True
      then obtain p where p: "aug_path_search G M = Some p"
        by auto
      then have aug_path: "path G p" "distinct p" "matching_augmenting_path M p"
        using aug_path_search_sound one_M_whatevs(3-5)
        by blast+
      have "matching (M \<oplus> set (edges_of_path p))"
        "M \<oplus> set (edges_of_path p) \<subseteq> G"
        using Berge_2[OF aug_path(3) one_M_whatevs(4) aug_path(1,2) one_M_whatevs(5) one_M_whatevs(3)]
        by simp+
      moreover have "finite (M \<oplus> set (edges_of_path p))"
        by (simp add: finite_symm_diff one_M_whatevs.prems(3))
      ultimately have "find_max_matching (M \<oplus> set (edges_of_path (the (aug_path_search G M)))) \<subseteq> G"
        apply(intro one_M_whatevs)
        using True p by auto
      then show ?thesis
        using \<open>find_max_matching_dom M\<close> True
        by(simp add: find_max_matching.psimps)
    next
      case False
      then have "(find_max_matching M) = M"
        by (simp add: find_max_matching.psimps one_M_whatevs.hyps)
      then show ?thesis
        using one_M_whatevs
        by simp
    qed
  qed
qed

lemma find_max_matching_is_max:
  assumes matching_1: "matching M"" M \<subseteq> G"" finite M" and
    matching_2: "matching M'"" M' \<subseteq> G"" finite M'"
  shows "card M \<le> card (find_max_matching M')"
  using assms
proof-
  have "find_max_matching_dom M'"
    using assms
    by (simp add: find_max_matching_dom)
  then show ?thesis
    using assms
  proof (induction rule: find_max_matching.pinduct)
    case (1 M')
    show ?case
    proof(cases "\<exists>p. aug_path_search G M' = Some p")
      case True
      then obtain p where p: "aug_path_search G M' = Some p"
        by auto
      then have aug_path: "path G p" "distinct p" "matching_augmenting_path M' p"
        using aug_path_search_sound 1(6-8)
        by blast+
      have "matching (M' \<oplus> set (edges_of_path p))"
        "M' \<oplus> set (edges_of_path p) \<subseteq> G"
        using Berge_2[OF aug_path(3) 1(7) aug_path(1,2) 1(8,6)]
        by simp+
      moreover have "finite (M' \<oplus> set (edges_of_path p))"
        by (simp add: finite_symm_diff 1)
      ultimately have "card M \<le> card (find_max_matching (M' \<oplus> set (edges_of_path (the (aug_path_search G M')))))"
        apply(intro 1)
        using True p by auto
      then show ?thesis
        using 1(1) True
        by (simp add: find_max_matching.psimps)
    next
      case False
      then have "\<nexists>p. matching_augmenting_path M' p \<and> path G p \<and> distinct p"
        using aug_path_search_complete 1(6-8)
        by blast
      then have "\<forall>M \<subseteq> G. matching M \<longrightarrow> card M \<le> card M'"
        using Berge[OF 1(8,6,7)] graph
        by (auto simp add: leI)
      moreover have "find_max_matching_dom M'"
        using "1.hyps" by auto
      ultimately show ?thesis
        apply (simp add: find_max_matching.psimps)
        using 1(3-5) False
        using False by blast
    qed
  qed
qed

text\<open>The algorithm terminates given an empty matching.\<close>

lemma matching_empty:
  shows "matching {}"" {} \<subseteq> G"" finite {}"
  unfolding matching_def
  by auto

text\<open>The algorithm computes a maximum matching, given a function that computes an augmenting path.\<close>

lemma find_max_matching_works:
  shows "(find_max_matching {}) \<subseteq> G"
    "matching (find_max_matching {})"
    "finite (find_max_matching {})"
    "\<forall>M. matching M \<and> M \<subseteq> G \<and> finite M \<longrightarrow> card M \<le> card (find_max_matching {})"
  subgoal using find_max_matching_is_subset matching_empty by fastforce
  subgoal using find_max_matching_is_matching matching_empty by fastforce
  subgoal using find_max_matching_is_finite matching_empty by fastforce
  subgoal using find_max_matching_is_max matching_empty by fastforce
  done

end

end